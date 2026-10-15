-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5199
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:04:17.497615+00:00
-- url     : https://prove2.me/submissions/80ab3951-e76a-4bb8-af7d-7e51c4ebc28a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 934892086 ≤ n < 935071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 934893336 1250 934892086 934892099
    0x10803071202030304050a06110403060e0601090c0e090105040c020309120709050117060708060a05031f0e0d090b21090f0c060a020a02011115040807030e030613150e0304060504 78
    0x1c1514226007954410014070001540006000d0034054019000107618481c081c01c09569105035440a0505130400584480d40c41001c01c0d0030b41241e200445c104000404090182d4690005400041c0d1002d01c0c04010010f034201034000c40c241c00c145106480c0b030300d140140000c80c6aa4807001c100b80700d50200f40d00b445000c8952007040e0250004a003803802034070142100701c0d0346103402441ca5080100000c00308115403907040c0c0841c042c18004094886190b481032401e80f00762907070410035820741d05040c2110200100070501c5044184a03680d995034180c2003034043c148030b510851800710304201d00c4483c1d00d5403031aa894040e0040c00d013940a0110000911240c9281464003004544100010080e1000c0b071500011140d8080c2d9080c20a004041d0850b2041810090308145491a81e500c140030001000781490017403c01500c251200440902602c0500d65581c000700e80c070441d0002c90b0801d0b400402c1080c8500c1d078817120300c3d03d4049502c0c010740940f14110b804c154032050105030041011f0148 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 934894586 1250 934893336 934893353
    0x40f0f140f1603061e0f0e060a0b030d081b0a08040b0604060e070f050f03010605071e05030307110309100e0a09050919080f0304080310080f0604080c070e01080307 72
    0x40d244614002c12100508900e0410405518030004014540e640c89004403140402c00c12003941c1c3c1e000e04c04000045040b24210080c041c0c090704044e40c0d004040008002c51560302c242040407402400824003005400b400361380503840a4070300c0017120036009401403804400001085000444d540b0000d203030070503140100144c080a45a10310450412600b4000c0b0038900c62240d501000da03280030141002800b6081c1c61901c102d00b05132030305070700000000c9a1950403200400f0b04a2059070819008088c000803080c98a00c04c00d001440d075007041001ca90150b100309110b440d90703107942003983d140590040020345030451140c600c4000c9040110b000c1070138904103c4010013400c3c41d80c014040f929100303c205444002e40000741100711402004075050099001c1a00d81c0d04e1103003841d00d5941d080a0800801321340007101c1d00f00805140000c00309061030045561502d4850300d40c0145510b8980c0c0c1e46400d402d812108400400e40301d0554001181801e03540c004d4001c0c03013510302840d55001141032503442c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 934895836 1250 934894586 934894603
    0xa060611030c1c090512010c09050303040f0306020703050405060c0d0305090c030703350d0f0c02030d0b0301020c030d0203090c1807080a020d052805060105040e040f0f14 75
    0x51904284800303412000041035070b1441d030008401443d0743c402901e41c242c86608180c0c0140e03800109403125504038000551002130f4680c202e031500ca007002d580c0e0003003550300e100703034001d00c41e07210095002080000d40f9500a0a0703030380c3c4241440d505140c0c039070000c20602e40200d060700f80386a001007070055403240c0511525404c61000c8015200010829011984e12100c0d844014500e01c2c0341c07031107559100c40358030810ba070884040024654070003814041c013810fa040b1030150a18546041d0242c0c0f5440c20f54414541c2c0030300d440d0040c60401040e15130071002041440c94054041d5000c01407030041601c244024410809120001030b201c1c103012203124a84001111507e00613250341d83c007030300502d111a540703640c45201450301050541d03a06154002030300a0442c80d40c2681d060806114414074030140511a0f1f81a003051804013168038035064090b0784040e40c1007800305030104014051403182520080e0302a000c0c2407513221001c040d03a207980070094515400d40741c116050083d00654181844907a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 934897086 1250 934895836 934895867
    0x80a050901020c18070315080a150f0c02060702070b071e170a0f0e090108071e15081e010e06040207053d14060f030f0706020706020f030301030c060c021302030a0606 73
    0x141f00d0500980130350b1031000d000068050b60603d01891030b4601d082d0080c0c910725002442c1480280409100659100d80695021015000c0d030000456113803d00c4040c0c401441d044000501c4030707040c858900356034074641d41c0c00782c40c0b100300301c141c4010004045000380149961603480c008011543c88005103060300c0000351740d01c141d000702e004005542000070030a05407032242c103a5040c02c0c02d0151010301c21100d1a4017140b0b860944047d40002d441d08290030902c10f00d00010100109021510000400942405903001c07400220000c103255003810781c00fa0070000c0c454404ca54948007848040d42074003400044600407200d51207246c20b42c500007020a080000d903007000072320031403901000c0380070b55040080605008514891940c161581c04000e0040a29061030039200340035140c9030000d4a07040240540c01c00742c40f5010001030b41d01c00000807a412070340c01c070141803001410b000080710208444d80701641c0c000318441d50703c0c5207420709200940c015501c0c00000150035140100c0034158612296035070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 934898336 1250 934897086 934897121
    0x30c0604121b11010f0c0515010501270e0907080f03040914090601030b1e1602011d061603060e090102180d031e050d090f021804080a050901020c180703 67
    0xc500141c04040c012401070800d01741a2500065000b08448a0399a0780000d401d9110341507031602404513210486060341e20a90320444174102c40720600740101e80b00e0001081142d0011010029100907010154100400b601070350f0350241c0e520041440c1c1903040890a07402d81000600700300f031008a114800d03044a08030b0040c1c1e00e901d8004281611602e0510001d040d8050340d50000b501c0c1e070180c81811100141000001c41941000c200003000051980c0f042d0340075610f082036a11140b0242204d02030001d04610080c960f80da07500c880c40c0d501004005014042c143c0302c1030007094032900341240da8412450a400140c603075503078401500083c2811000c0d5400742400401200220f544104030072100001210041d81062840e0320886503441809607400c010f0345030134059002c021450800c8010320340222012401001c000c0d410803900041030390001d000030303030820240742d240c0c0c040d00c094405854140113a819901e4107002144490f40307000040e407402c10020003044482070700b5100f04107040d051007000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 934899586 1250 934898336 934898387
    0x10e0108010c020d110c3102031302040209040f1b0215060a0311010e09100e0a1418010612060207030305100b0a030f0b0a0905070206070c03020c12030c060412 70
    0xa520f907444940c0798005c00c02c402c25284000350041003c0c11144001801c00070180041d20b501c00d01c0c0c43c00702400f0854074504051400030b58481c41c02900d0141c4c4002e126070503443e9450b030070070009500104086400644981102c51240036911402c0c1c04449800300801c860351190300028140400c054901da4030017040818804680c60300310145040e294003d4407440705624810058512101c223100d0700b80c1c0320035030384204003442d460021030b04100d5551006944244d1200604002034070070450005e41600c000e180003d075408503c011801c400e107000000021015211500004168240b84007614400d0300001c07a00105a031500c10710782d215924412403040c150400a00011b94812160745000301500d58008060110f0303244d0000c002000c1c02409440e00b41d540b4000280942011144c2d1009801900c001030300850082099004880d41a405801e00c900c40908100a2001440c00b01c9100e10083c000c01100d0b40b02000b000b40618000d0380f180c01080c40401005000c0041c00103050680c5816400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 934900836 1250 934899586 934899611
    0x2601031a010e180307060c02030c010c080f04260f030f01050f130f020c01090f02041104030c2102040911040509030901140901021207060603030f05040b070f1b0e010e010801 76
    0x1000c94102600c2103140031202c90042c800f602d50b014080700030340076a14101c00c0d068010340010007041d4000b1030600a001c03080441f4010b850a0100712800c040c000d01c98030010740010101640198203080c086c401c071284d04040d400646840c0c10a002141409c0740c00818050b281c0e0420020b28014001100c503114240201404604000b02085400c21095207a005590b04507a0580680d1070b5109c840008103c1442c03103043c188515452030400768011403810244400c803594110803079003603d030040e120500e100e18080c3c021a80e000c0d20b100c0b0300c106c000c50700c828100694450051240c041e00400a40e07040c1002e110422080b200c1c041c08a400590082042c072103d84d821058001c580010042c150340c88100c0400141c0c01c4c400e1200740c101c5140c40026004042040c9580a5000c0d2030103035036074a45402409030160b50318441c501402e00f48010521030440021003d802040440d407151904140a520502c00010b47c510990841c4925404920042c010ba00c2e4030003409004084000090052254410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 934902086 1250 934900836 934900859
    0xb07020f010309110d1a010b0301150e0a3308190216020d20040c210b0603090c0301180206071202190c150c050316032601031a01 57
    0x81900d05140c0c0f01c144a0050099511180c140420080d100d440482e200b403400248200c181c0c1c00310014854400700100d00218031300103907810b03284914007194a41225213130660312008a4148180d12103140600401c041400e040c000807081018800110012a0712242c160201a21f8040204008012080000803404d1100000510200101c016514444001c085201c4c04280c0d0001c1c1d0002c80094844040151500701e1100d1020164a1003c090220034104001d940345450f0985c0040c3d00241c4501c0b08080000255000f1514103030001002c00240b008118240c01c2241d0414a80e08114584611814203003e00f03001e40401003200b0019003c4c40c1d0000c0e101307021740e140260181e1600d11103240418000c00070300390310b010850943e412144062034000040203a500030710b24240b80c03035580c201e40a4080c07a201d0b8003041c0c0c00009141003400c2030a0a80380e1203903c6905070104004000042c0d80c4201d00d0142000103810b07035294002543c1541020901051202c2040c40c00c0d4484d240104140441c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 934903336 1250 934902086 934902109
    0xe010c0c05011b171207020c0109091d2e140a0902010c0f05010b010e0f010c14010b13050402030c0d0c23130b0310090c0e07031103010e100b0702 64
    0x9091a914030300324683c91044480c40403100918481c00c0303050380001804a00040e0865580e0f501c511989035076001402c98403008203103045804600302c0300007840010000c1d0400d0b00c10030b1000c000ca4022640d08000d56140c81002c202d488038006107141a588900346042c0603c3c540e034441304043c0701e440482210811b2410b002400200300075540c6002c801160310a0080b42c9100340c01c0800411016074900b000360003403060302c031002d020170750140c4142c003281080030610500c1981616410400741154030707040d01e03015010407402c0c519543d507003e01040f565420808641201c2c240700c000740c2807a20f441414900a000c1f50240d10036800d5540f018009050582038000381c0709940740e481c0d4940c005010802002918402150740007641c1c8540d10108810740e80b040c803101d04204e04407071200f010540484102d030780e2110007400302d02c3e40001c1800300b880030b401c40315008142460b0014501003180b030300b83d80a810030b0700100c05c400f0b0500240082c01c1e031740321946000341054641180c501081035002810804a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 934904586 1250 934903336 934903339
    0x50d020d240911091215040308010f0906080d080405070f0b120f090a081c0e0f0601060813060b0d080403080a02010b040c17040f080a17100608070c06200702010e010c0c05 75
    0x104180d05d21900800d2003d40340c00001c0440074032081c24240b4001c1e158200074081c0c0c0060480c1480b00045a140601514044171740a002800b40c1c0000c142d000c070340d0840020400d59140c49441000036440040d004440018201032410a0300d86013428024407140202914414041c00c0c0300c014840700c04070218012040d150700040e496138a240b802c503178042d0f59240001210a5514007007080e00480305c04100345030480d000000303454040e03032140410f0f101c124044e900c0b42250340d0b00301c0c05080000c3c0b0307503848a86003c0000344003d010705899640da812940c045e4104542c3d00710702241c1034600340d409029844240004950034001840c58076001449101c3e80c2c5d0a041c008803003080030400340031081c00171060540d0450172090ba03481410300050240c044007ca01c003071400c0000000f60030030402e400450140e5000fa501d214090300e90542c215005641c042094407003a0303684e01c10b85d2403100c1030741d0041180504c0c00310840c1c40703a50a000141422001c0540c10b810320a112a000001038840900b0a007500c90 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 934905836 1250 934904586 934904599
    0x91614031902031905070b0a0306092316030b060a11060c03070f050d021b0f0c092412070603051501020d02070512120408030d0b06130501050d020d24091109 69
    0x215044c8145440b00c5a1300c41d0a41d07c0000443e0581594180c0110050300c1c500a814440c801016a652503da0720035580300c4207180100c2c2c00b24142c1244490303a40303c1c5000c41d10300030800074900b00001303615a000f04400b401044034451003400710318050180c1da81c010346c0b61101608615018002820900310440b0b0103003004000aa102c0e40030300c1d0796050300d060139034903c80e03448003a86d03202d4031681d80c03898810324080740e2154180c8000d541c581460310b207101e6a900e40b900c4004107000b01000c0210602c9044ca03079480b5420400c540e20404003044604000d161650700800d0034140709603800361501d030703078801c5504542026903c2003074181c00140c40c6040310b00c2511842c04c10200780340c0390350030103400200641090304006800265a000040600801840c01d20208104032200082001074440c10490f00c2c1410f03000081081958000c2002d40001c80724204058901b2442d43c103c101210031214401902c1d60721000e05041c0f0a90b03e0004030b0240c410400e0401a21410b5141c14840d03000d81d8108034070402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 934907086 1250 934905836 934905883
    0x3303080702010806010306030503030f180304030507120501060302151806090d2d0809031902031005060d0204090302010e0f011503150e03040e04031119080309161403190203 76
    0xd111fa0f1200004680000680f922401c2030490050000310682e0032038040f501c4052102c20b0242d01104440444c0d0b841300040044070b140404a4054030020710303054805550700c003c0000562a09075850120f1269004600d584d40d4040c00880c02c40100001090300400701401038642e1034813119410001c090300720203104019010360301c11801280c41030030384030481a0f00505000800a0320000317089044811010340d00301241c10100f401d080514500040d6044e40a0000300d1106c2c24150311091b00000301130704044244000e6004117007034855405080b80180c0d540c618071105041d05120072000d2104c0f800081c0013900300316a500002580c0b0b400050180350710442c101103044240c0e03003c40c0414038130000303176500d4a0380c495010f00f00100454040e804900454940c442030800481c1c811446c45000c20744a40c50584d54a0705611508024001801c5201e0944491204220714003610010014511032006090910b0249810b1245890105c0326008030074051000580e00498440c810b0403403d0140085030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 934908336 1250 934907086 934907089
    0x302040509100e070303110604170d0b0402133201050a03141e0903070506070c02010c0203010501031104060503060906161806020d1103030609190e013303080702010806 74
    0x50b80307855004006241565000d041031000c01c030030084074081e4603070000301c000440340340e620340d50100c078018071041000440000441300b80b0041c0141c0e6803c0f142c009013407101003010504a03848040101c4900b10240401c100304a0705020300320183c80c01e0507100504005201000d100e08544480e030b81e05009000c501e43e8011031007a40b0110143c00a41044007050034203a4896229400590020106c0350100c030010301022400800c8035045580100148010340d101c4c00120b40059202404a04200c0742e04134a0300503950074003410307001e14020034683d40784400d6242000b0803621154046400703134000074100004504040b4515501c50080c503140c40c070070009050101d508059111121580394034480001c5400c50340000c0c0070b4a02c3c100c6460780105038508200c02c9582c1d00003107903860703844075800340000d01106900c2c0070441c02c0214607002203101c002e041400c60070769001c1c10718408000c0340050b0b22240810285281e241c10301103180c00081c1182152100c142901c210724010b41801444400316195 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 934909586 1250 934908336 934908343
    0x6030606062c04020715020702010207210b0606160507090c0f1d040b030f060105010201150e06100207090c03090c15080c090f09090109021009050d061e050903040f0605130302040509 80
    0x59079203c20396242c3c0b241446d07558002904410303c2070b1f005200c2d2074400700b50170281401c01448507034425000741c1704c4d017940d9694003d4800010003c5030801c0d42070200d50f00d9890807074003582c1a01d10502c0500601410100b00100316200142607504000c20700481e0094203401ca45100c0354070600443e40d00400c003c2402050141952505107500343c401c107400d004019030b000c560ae0b030688109078000d010322032180c440380078500c4440c000c1000600c00140810850702d8029202029044980150b403880c07580e40d010302088456503129503022a4407001400200f21741807100c600902904400c0c001400d0400302d00610102b0014400c021480001407100d0b1295034401018441c020300a00c22134491600b502c8840c064001c0c040104d000300d60030126010f08501900301d400c19100040e01d0503403c0c1520342c450390044c10038526084c41881c69180107a01c000384034011548105240d50003140e5840c030f828881c12455082c1d07804502000010b001100401e103110042504407a011100425281c4075006c82604 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 934910836 1250 934909586 934909597
    0x4090f060503071e05091b0c0c04060f060806040212060d050102090a0617180303070c020609030d0f1202030c03190e1b0a090203190e070b0d06030606062c0402 70
    0x902d407080510000d10310b801d62940728004022035409580c070b296a80d0a0164036441034403500d170b05114094014068501c143d0103000c03645107400c00c0741e0707000e6520705c0450125546900402d115201d102c1c000d01420780c0203200300d074110320150340451802042d0034481c0d031003050140440f07200f00414044201846400d405407500131030700a04903034880ba074600c0c0141240d1034507900e0751030260350540019014100b81d180300604003d0034003d9031035999505002c4960303500820041380c1c400c02c140300285ca41c1d181002114100395094030360010380c820a010140940723140f0011030008078010010040d00e00c08035000d40c3d4120001544099000c05078843c1c00c009040d400304040c282c0d20a08119080e0140d07000d2454a5070003003035681c103400c2901c3c2c0324950241e08c011201c125111030750068800100400e0341c01181030124401c00c0d55a00340c3c9800038400c4960004400c1002d29440300c40610500409104000c0149410308114040380348030752020039181c1c1c500c036004020450440403080c1c9600c036a011900b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 934912086 1250 934910836 934910839
    0x70f02060f0a03020d0c030b151c0203010b09030606030f0a03050906070b0f041b0807050d060b0d060b010201051e2e08030d0e0a0c0b450105040b04090f0605 69
    0x2e84038120410014000c0d0402c11000640a040c1364001e0038003070091003100304503500030380000251403034881c030740c2481c0e44541a050491a9802d0004060f01c22074400b850213014140851581d07402c8801c00c161a003603020344082c0c8203802c003900d1507068540c00540540c8140d4103080003a00c8200d07400010700107004201010305001310510800181c8c400d58549584124030402c808044c41c07004024081e1b491400c0c0c0941c09150703010050510031440c10034000c10500d0b2117480041202030224011600b40c4900c000c080b2400c50702c460100000e903030203001d025408400040700c4ad109951407006007245002c040c00c41c00c940d643d0003441850ba5078240c1050f10201450092200c1c0351960345007800e540391f00c403010245000b03281c0a1900315240d0045000b004035500240851032060410301a1038a9600c80707244010741c08420b160b8245003c84c1c00b40d1514035942e8403a001352884500d49603181c00042c4a99245040242c108403e11040d0000002e46040d54001500011141c4405413400000c0220b504000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 934913336 1250 934912086 934912117
    0x518070c060914241005010503060d0804030c0317030c09090910050106180807050a03140f0604080315041b1206080f2b20030d1d0c06030c070f0206 65
    0x40f00f82c0000f8240c1c000b00079002c41d40d08020f41000d00c10074020000d803101302002030400340070070803913106034007441c0c002030003e1020b2050030180d07951403c0350b489944221600701000b241041480f86c1d01d828400207500607070781c030352031460b02000e104114032402c4000c603c100d540a000c155004400c001019403e040b2030700400003543c55800250103900300e00c00d420b911080f8040302003451400070840c81d0440d0009890000400c1c203563f60b5521061b00c0c00314112040c0300f40c207161590b0550030442c02d0701940c000e0f42c0c016a00d0501c1c940c590110501400600d001c2d501705224100c00d0354003401142e080070b600713141049105c1d101c0c111070300140000f81d01403103542c40303510420100e030b250110320700900c00c040c1c0c00e100072080840e5480c03640d4460720b0251040032400030015164480341c40c0c4110b1050080581c266894040c6c1c41446004941c03042421000400800b1521019201c3c10080f2845000c4201d41580c01c40c5401ea02e031660501c1901e00c01481c284149180c1411516902d042c0c664605200710305 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 934914586 1250 934913336 934913363
    0xd1d06180a032001030905060c1e030115030f0c120b040209030106150e1516230f0105060a12060c1412040501061406220b040803130518070c0609 64
    0x3850f940501030201c1e624034841c00d0b010240c590b00034494070710703245c4e8030070b0180c002036440e00f001803043d0b0001101c0c881c0d5440c04440304200c80c640103000318081c0180c5c2d40d0103c4210071106000f02118030010501c0c00c401d1810440c0c2081e10f42028650741034012039000815074440c9a404500680655800e103070300366082040200d0712402070040801811410390345c0403d02400c1c0800c100c043d1485000f86802c91200300002248003098160888001b805061107a0b01e4410100b08079828140f5204407503201c0e08844444e078a008401c2c080c81382c1090f812516031400038108415540e01003c8820010305040e601c0200013903c40c001c1e04088800c0e008505003a0719401c0340c50540d40c80020403602190554030700310010400852103181056400e0000d00b10074103202d00d2508034981d148129032000d1407107201c20000251415194004c01c09403004902940d11845d1106511880748000c3e00aa8840d2400280c20207440c010210b1465202d4524980300010721110b0500900030500c280010f021003c60021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 934915836 1250 934914586 934914593
    0x409050f010906090b0f06010c06090c030b01030503090111011e0e010f050f010f060f05030a0c110601060c051204051f05040302060f03070f030e030a210c020c030d1d06180a03 77
    0x54416034002c0d517100c815030303841100801940380e0464209011621415003240852100e520014101740301d41811140c42d900e0b40c0f524520b1358000d070300c00c580316400081d901002d9640413030342c901c56060303000c024009544011442a240c03032907001c052a400c3d95a40000740b00c00c03425040f0800101c20480d00b0481400c001c4440d09800200b4081c4a04402030b40500260441c403c2004405d1060503030350b171a02316201c0804d05400761481c4125181000910343c40020503110a000c040d0083c0300f0f07a02c5036407512640d858001d0400348503c0082d40b600e04107200c00c1000740c56030341096040c0c1c0f00366440702e00303540d0f8440c009403801d000d10380002e90040f00c00304504000701e03120b100450050050340c550f2081207040602c100e00351a16078000d40e03420b400038009403002601400c982d161801c501c00a6400c03031110365000808880e0740c8550a0016030003c4000c0206003070500c072401401445190003802c40542d4541980200b06003860240038070700020710f210114543c4482e1400c2d243c001070109091907940e04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 934917086 1250 934915836 934915841
    0x1031709042a111212040609020a0e10170c040c18090b0a0e0618060a05060f070303060e07140a12020c0a06050105220b0d020303040807061701060e0409050f010906 72
    0x401407004504440720307404003d1000550a820400c1d0f501c415864403040701101407400c0c0016104031101030319079040000594403c00d01d44094081c80469440740e01c2c000400c3c2400c494241e0280a0a4600c5001b03030078a140003148402260f81c0c1501c004c41c07000c2450324200c8201d8811044c40c0d841138159400415480c03c540c016681d1102c04882003003007143c5540d441003021400340c0300b15074040c900c8a0b40740f04227280203250540c07040004140d60b12890351007021030308035401000c254003c1d610024541041503094030a1070060700700d0000c1ca0402d882c00c83c0d00074010001c071441c040c03407008000c00c0350401c0b20722680142070746151048048d07494601c00c40d034075035442a444000310703120b604000c0080307103501301008003126440d44130300003544c0505000c40000040c1481c10000b604125408900d070050b0f24200000c00080030030324014010b2a281500003007140090f031551182459000c0700400205500540400c0e40ca90200c1d000664a03100780f6089280c40100c682a0445500342000c420138482e290703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 934918336 1250 934917086 934917161
    0x5190c05090112021503060f0409171201150302040305190f2906041a040f0b061c050f0c09011d040c02100e1c0f030605031b180103170904 61
    0x83d00c8031328070800b171241e0000d90390104031503a640254442494404c1c80c5440d0f04140741e900c0c054810a510303041c41d00b080b04200d90001c0302c01032030210b095004100141a54000302601580c5140031400c0904650310341d5183c5500b14208109100c2c0d100101060000004c541c0c0d03021584072050354240310350a40d40c8a1044070b0358204590340400000000c0a43c14a030258501f00802050f500d40325107801410000206501111504602d41e00d0300c01a90f5506e4920040c4161000182640345840c4c00041100584200034254119818400c00380681d20b0390340005e4036500d00090078040c20b0030b035a564504484100408256903c40d0410100c0e2007926008108041c114044800074800c2050034040f555507103200c0000c03114000311006141007101e100300311250100c0e0b411b16021807c1e940c0d0304000780ca001781c00003409070ba410101c40400218640440c040562040c40043d80c80c0035032660b15951002d40b10010070120f141c1e000988241950394a41c001c1509804803202c0b85e2060303120114071401050f10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 934919586 1250 934918336 934918339
    0xb0c1617160803030115020c03100b030d020a0f02090a0f1a040c050c1b0d06020d05010e13020315150a12020f0105040f05010c0201090506030403270305190c0509011202 74
    0x45807526155041c068a8010584801100962569281034808541c82d444400b43c401140500d40e5840380344d0f03030103216540702c1040090f00410a10038101c2010b0412452220308025540a054040b0001d400c03414452a8543c0480b0107015070340c0c460080707001909418003110300d014603103100559104084070643c90001d40699082040741c8202c8402d89031032041e076003501800d81c4514201561000c200420790380b81c850141c02c843e11190242e0310394041e6004032084944036500c81c0c0040c049035003010381169000b5495100440700c58156001320b46c88858050750b00b11103652882c0020811903004c40980c00c00507000e0170080341142d075085110400691880d08a1080100300f1000c03607598440e5099500380c4a80e04100c507800ca00e080011350303010704814400c03414081c0307003480061141e882c000030714800c0c3d000e612040340000800c0d104d600c0c250030b40034000001000e21441030000c5000000d4642d40051560120f446840c07071401c000d881c0d221181e0000d03910035071110010034540d0381d030400203a06520 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 934920836 1250 934919586 934919593
    0x1b02010e0d1a01230310050717040c08010c05282006040c1502030d090f0f030519030606020703020d060e12040602010c02060103031d0d0503041e0506040303090b0c1617 74
    0x461613225030a0901c40c0c580c5a4503900208213004440015840140c0010003410055000050060407503681c01049070300f81c4004040d2641080502e5003170184013001396003868254900802c101030326401c03601c84403da040e00d524510031044110f00400c400804c0010255842807103481380003405a0324801102e040720918188000020307003403500040000c005405070095420a040c0790600304c0100900803040e96030b072280e0301d43c00e00070841010280c101103019a80f0782d9501c1c18418151103040549410000030189003a508220b400e6000c41c0b51000d9070342c1111400740d102c0603400e1031406404801c00018050040e40848600084403500500c00c9450540003803010610260041c2d88400003440054042480b101030758952070740040d00e041c18079a00805401907401c0c1921001e24540058100e02c0e140d0000300b0f840004100c002c0340c844000c12040301c80b14513007411964014240141da1194908842c80407400700030815090006040504032000c6c0003150b1035a1f855486200408030400c4980ca00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 934922086 1250 934920836 934920869
    0x4051804020f060a021507030c0206060a0302030322050a080c0a0e06222301050a080f1905071e090506031605011d0a0e0906071b02010e0d1a01 63
    0x1801002584a50740041c910540300300b0400900c0034a50000c0301c000300b18010f4040708410300610780405401807905607400900c04910480180c58860040e0038244102c000c503504100595001040b95100214900c15902e068a0910b0500411505070881c030351003141c425021036005000119503140e840102d4503c0c4155584010004e680d000603554144c0100c6081d0140810540c4415404c000c4070b0740791400030b40310070216800e042c024041c509100c6028202030042200740753841d45041d0060040319010300f06800c04440002d036200c01e5908042c3c95040e11610304e00134000140314040040070700100a607207440c108000b071f0007010400e0048050291514010502038100001c90250031030072442280019800d04005542c080c148172194a028420343c0d800002c15221811140d004010000720500e450501080c51401c018005006000304007940301e2414280d04541428504160282002c2c8a403980c96004503c00d000e9001c406000740c03880f20800c0700d61001881050b8102c0702000c80c0d81c18641c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 934923336 1250 934922086 934922119
    0x1091401053c180103030f02010e070e0c040302090901020c010c3f110c0d2313030b0c0315010f120e01090c12051b06030414150c0405 59
    0x7049060302d103944984000b68582c00d0219103600c07001c0e1036502e6251030b0241031002c800141400010f402c1070b1001c03500c580e00400406130825007003c020480390000f4001140d6040d5000e64481d01441034842da03071940c401040003440c1c800111009150094120700e001e280c000892402f0f940181160034180d031812244030440ca225110b602c40407070b444407210408131506009919090800305003589802e481050000b42100513126003092482d655075a83c2e1a0900d200001d4200010b20140d0424060a01d03803000e0902d2882044c1c450030855012920348401d43c45847e07582c04a4607800050071450000103021500039813102540c8a89610404000c203150f01600440d800000354941c100441c8807080d04250351352160708150b101c0b50b010400010380603419110340c112060950b000541000c920807401c3d0a0103c240100503102d01041c2c111000090310002140c032500c401003025000e007145210b00222110144200e000d070304004030620041e4100300d00780310b030700d82d0051041a12030b03006c800010610307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 934924586 1250 934923336 934923349
    0x40e0d05071b1805090f0d02010b04050a111603110a0f14210d11040303170c03131101050706060312180f06030b06120f01050915030a03030b040b03060109140105 71
    0x36030340c40d1808241c1d0b4400c8803e802003d0400900010440d00400311618100c80d81082002d003031050aa00100c4e6181c0c40400340002c98034081c09501403581000600c810070034604084480041151030440002c24213401d044400260710740a45a81d4003c40024400344203900000ca100d40f4010140641c3c0e40058401c0c00b42d071092050900580c6500c0c991184412800840181c0b03a034444c2e044001c1400041070090400b1503005400460104030025928045285104040c65005420760001c52442c00c0011040c0f021159040004104210456110100c0d92003001a1f030340e860340c000e00a011094582c5012500058031401150002c1d004650408010f0040081002190043c070912180c541c28201c00b14080c040304250582c001e24204040d810020000030a50300c603146400d00d41b20594145801c01000d0040038101050301403503000c054034141d4005c038080b00b10641c542400511400d804010070060145454001d44c140120000002c6040d03054000b5000c0607407c44a1605580c1c80c0c02c2006507 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 934925836 1250 934924586 934924589
    0x50a0215120a0b0303040302030f0303010f080a0305030606030a0b09040f030e030106240507080a02011a0f012010060305060f06030105090d030e010b09010306020a090501140f09040e0d05071b 84
    0x4101441c0c007003240740c0e80542c80321050340307005015285400c2c0c90750003180c6403180c03d1010140a50000004000c0401410b480d03502902d0502c0c0544400320b840d440043c102c1c080542128440c0c6000804200d0044450b03103d080d0301c8001510a0607285018203100295072008a001d40100d0030103808030801e481c06105820984d484001800801103201c1405100d4044c040d0441d01401020400c44c00851403a901801400d51a0360020401c4031900c4e0b044c0c000040d0b541c144a00540403d9803c0c40715030703007003134548188131141c504113441c1c803000c485041d00d407200c0e840f0408007a6103048070200600c138000c0f0301180b0a0151980e05425611188141030803180115410209078101000008220b4800c3d044000040e928070004a4044442e400141d40d400d400ea10407942c42d940020220403498001c8d420000904c82400c02114001a034000344a6911490300405c03c6180002102e00c6035583e1070b8021048403800c20700301d4006a82c821743c0503205500c607180560300650202c00301e01482c5420314000c070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 934927086 1250 934925836 934925857
    0x90606170a030518060c0a1e0305040b0c10060803070c05150a14090a121a01050f01030b041806020c0601090615121b02031b010b100f0912050a0215 65
    0x880281d42d071022100d5810107104c00500122403c03000800d540c134032014051b070315401005001d002e1440e1800c003a10350a4030b0485103103900304201035804650000162021500e1100f0130555030006104c116042c0f500708801011220320b40301000c11400300c00000351510318400e200c0d56401d251200b007007128103400c009880702104030410001c15018840c120418015032844921070903c21001d002030540711031034111034100303500e081d8080107024401380000201040d031690010301d0350500b07020602e9800d560075114145600c2d91162403a94907070340d018002e0b401e8100c00c1c44210194514011019501c044d000207070324400c0e8400072403c5011071240508489070748195500c03641c03584105540700c2d9460106d40c12041e070307500340c40c50004914000c00768000300c46034051659080008138244040c04041140c0115a2400c1244140c44d01d84c4e040e400d0020000341412034010000740021107940350ba603041040c800d064401c4400c10000002000700d1014070866070014034000c006580e100034000c0d8007611 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 934928336 1250 934927086 934927093
    0xc02040f052e140a171c030209030c12030c01140702010b01110606130608010c0c020a210b040c170a031e0e19080d080603070b0c1c091809060617 64
    0x4000758203e003851205003050180c0000c083c955a2078a06100081211000800d500240c0c0c46105228407009001e60b0904c460500314184200c40c00440d90320002c00320319038000c041030a002909407500b08103960030780d0181c01c02400905401e16100401c0a000e680e02c0001d5828204012281d6004a01e220300411703020000304019078500d410004909a50418502c03112341da00700121b5850402c0c05100610000e40d210350740840424410703c16044029807009990151403142c900c605500d165031454141d8101c8207144050312141030081e008510740e800708100001e249110f0a100401054408450b07020f0b44544007504174400440c182000d0182000c8000b504203e51080280b400f00562880b0b583c00c8074480c3c04050300d8190040c1b400fa80f0410701e1000c03540394400c118152030200403003c0070b407546002c0f1030708140180c050320303070307100d4040d0048500200c1e03040d180c0d11781e2031056404200a0901142c040b035486e84c981c00c060002d08803c2c0b0140d500d64101680440c02500c50710034a8a400400d2006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 934929586 1250 934928336 934928339
    0x5010305091902010309121815050405060f040527010905060a0b130b0a031e0b03030f07170301060c06290d060f0218031b180402010c02040f052e 64
    0x101040b09141a4101d06050380d401c0810045880c210320300c0c3c00b10f000d94036140008064912101ca4002040c4c0c042c4580400741003540720b505a001007601c00716801510032036142c036002c4c142d54155000e25000341c3d810401451b17200303a012241d250304406145291441c085a0f9032501480002d071042141e03000c1d08090211000c201c079a04203001020f2180d0740c00c14443c030f0f040c1c41e40c0402440b40e00524185000a460b07441040c1d07a00d02928010440d181082c208200c040b4230017002c2600ca0280c20307a00b40021101154020901c41205411320761205006c081655030f6131904809800d0020810058030b03402e14000200800c244c01c4041c240403900c4034004000346d140e40508101a8610f03074001140c00c0c036141d00702c0f600c15030340c136001401c0e2500721042c50860810310007081c18503109290081001d26252b8103c518015254584d01203940c100d10304444036142d403a40010b0b100e0b0b2003c0b00c4020b400c01d18010700c03104888080d6120740d0203244503030144048910303944100300015003103a84580740c0c480306000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 934930836 1250 934929586 934929613
    0xe10050307171005090c011d090a0908130b03070801080105042a09110901020609031204110d0b0a0614060405061b012c2802040b061309060f0501030509 67
    0x14001e4004180d0011103c038444041d10f4403040c0c410958a407410340e0300131107030071007150380024403080e0b80c0301e440c00259003402c2c04400040564101503d950f8510350364510000500c1170590440380000349a44503c0070b156691041c0365020b42c001c840d0390000840400011030980741c180500d0b401282c0040413201c885006000e10055402108441c4d402c000400400280400315400b5101001003841241c0d5100c5242030006030030404010401c82c1150400c00c100e8819070b580e00c501c1c58002e6000144c03002c2d90208040811041e041c5840e0241c01285e181e0b0800c0081c0b00c503a0018001c1d9504141c6148040300e1880510101b402503005031075002d601403102000c200303c81174500100c14503100c00802d40d041f4080305104441000901c4022540000030324590820081109800004070402600046c020110720800040c3d11990005d220740d440c2c80c2c29040c26a2064203540c440380581540703010701da5544040074000c02d1284140c842903092907000080c00c1d0700901c0340310701c264034000c060205441401c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 934932086 1250 934930836 934930859
    0xf03060907110f0618061003080c011e020309010b0108010501121505090f100b030c0720090a140606030907030f030c08120f090a170714060406060e10050307 69
    0x8107150104542d50344801d48001c2c003086018800711141004d448903042044040901c140010544d41075039000a040c000141008860042180c1e00801c0d60754803403841c1109a1701500342181030000401068602c040e0401041d4000c5008001d03e10080060708040001511000000d210b55408651000c4450600c40626003207258250800580c265599803101d0014a1441081e141c40b0046103840e03042210301384401c1e120901078580c1042d00f41c15880d03c03c3c041942d80c0320f1840c00402d111700e103060601580c0082c581003202d1030701c010081c0c6554130b09500c8100c000c0070f0b1000146c80080707408020996604000c001c89000340c0f241c002a000c0141140c175a000d030f1082c034103012030400c44101c10440214181070090305c01303152400c101c1038082c00e087c618000388202c09000b031300d180d420a81002000840685084100c160007880d0280c66030b01d0b50400c4c080088018860340381030701840782080200411a803100c000d42e28510090f9109440d1000110505a6580592601036000000c240045440780 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 934933336 1250 934932086 934932091
    0xf15070e03120a0e0a0e010f0501050d14071e0503011212021203040506010e010806070c11010e04110702190b070206091c030e011209051009030c0c0303020c040609020f030609 77
    0x1a08403010380d0310414150000c0c1e0710030a5032400043d00921111040e00d440c900440061001c26007000706d6504288010704034040901c10281403100c000741c010f47d00601a000300410f403006038214403061a0400c0b02a050750224942458046070b4201d18846c02c0c5c0c004d109a17416184041010354035000c95581e1221613038400000207066105180c1252442035402000310703c114820b1015200710352500c00000007040c410f070050383c00c2da04810100031920340d0040c10908a81c0d08900400040c0c00c5c8440107807120b04080b00c807144c02c00c1c20000400c0c2000d90440c010200d2904c00d442040146034420444003c44290b80514160100208004009450614007030001c5503001441440740741c0b08100c84c006200c501c4c90086020511400380010340e980c000c500009440188030080c4500d80c2286d0b100b940300c8900507080c900b290340d154a8801410300c40ca00345803140741e1041d20400c1c2d403038480c10702958a40c5190401c9200700c2c1004801b1496900500030303504030120031f0a07250700350f031144001c005528200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 934934586 1250 934933336 934933339
    0x1d01050f030a020303030a02180409030e01030f150b0421051b03010b06120f011e0608040503070f050303092109101205010f030b1e070507051006090e0f15070e 70
    0x1076002e07000141c0d609100450145c00705150050341c48059580c0506030720b600800e454882e9140c4041600030036001030420040000910f070002d088121410030030005c088054528055410720940812008003a100800c142e4500c2c2254404102c68a164860222441c0784010501d07000464600014420102d003c442000c0003000400c50200c1180400c001340c1000400403424034200c014000201d101820240c0901914502e0114821b001a40007207041c49034450101003286140009003405018800d5840c8140d0003600842e03450242e0610981c0c980080d02d11b804940640504841a80d90706080c41d04440c1c04154030500701049081000301940211b1840000d105040381d42c5100c40120388111406005c5000e41d100095046040c51418000010b05901d0503031040c0c540c2c81600a070071039030310758030251520741582c3e140c400340303402801d05e0082d002d5000000d0070190081002c1540340c20161900d40041b0841e101f0312800d0789040c1d42c13441d250001c0c203031865081003c02c20725446074052951440b030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 934935836 1250 934934586 934934593
    0x20a060c03020705060f0a120b060f0c070314010617060108060403030b120d0906020c040203061e15070b01560c03070201091d07080703090f1b1d01050f03 68
    0x252000800e845520841154051080c001007000d010f68019520580d491010f000070011b6801003408a2b003a84a1042c0c3d8040c400300210f0103504c03c2600b00021005140e003d40c101c07010b4940a010740c0e0180c1245c2c01244107030705d0308084040c541c140c0010700c01d04850080c00142200d403140d480540c0103280ca907929580041c400705c01189866410420007907040c00c3c942d07030848101d00c1d18a0007802c00b1f5011100718410790040040c011107a8580c001118201c0c0b080c940d180403030030341b1f00018400700c0c0010030b86505c00e0300102d404d501303002d81022058100c4d80884050720002c0328a940790000303c2420740402c0011951030200e4440449240001ca405940c1800341c00d42c144040e0203d0010783d00800000001c5900c00243e00046582c00075406005288040594040448014100c8038020001700340000b0000c003180003031403942c440d0b0021444a074105811810784030b1641487d4115544000d00d90214554040c0002601080f07030184080e11004140c0500300c80c2d081130100040044a034030070071391521 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 934937086 1250 934935836 934935839
    0xc0328141305061b07060e03070b04062c150c04090608030d0b060a080718030b0c0901021b3102030c030a0b150412060f0e0d1803020a060c030207 64
    0x3030204154019650142081207090070380c501945440320080ca00c0469024041e891050180c0c540c040d1004180c0c48000842c0c01440d00c00000d00e18040c4100c0507149400c50300c2072005025290b4411184400503541110fa100001e003004c40130400b07a0300b5500002d40c0f080d00c0503074010040d2105503400464020b6240e14296850020009841d003941101607280c01c001101e0b500651180318550851406442483c2072440062000c2c0920740c0051011050003000b0720302c600c540e651200c1c100c000d0340d132104800c0c802c0d040c014201d0040341c0120710158054404c160f80380311000310900070b5a44174103004103c81c00c20000209850868201d056040000c5240b014403115880c580d8005140301e0112900708036141e1400410742400d85040070b14050154040300810350f0300c0c0c2c4449003151b0543d00900403680c000c07034082c03030614010845560b0101a161034591003080706e400105150007224500d070b0f00d059070782c0008002204425600d10000798024040328003041014024042090194040d005072104903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 934938336 1250 934937086 934937111
    0x513020d09021e09162f100506010e04090c1205010b030304080114010b03091e0f0f061503060118180f030905010f03020c07050121061701050c0328 65
    0x4000d0b41c0c91030140d0032801001c009050855443d54170421110b01c21404102c1c400024003c2482c042000410310369264080030540010104c600119008000300c509500c99031440500600d0142e81490014080b0202240241303810301911030b01a800103900d8540c2807030243d6982c4c60a040304c1c03044030340d55201c50740790040d80e0b001d1000d0300080401c40c0c000b140b03a09001281c0849520160001940c0d030740c0600500101140000310b05401d01c8140e0f150088010022444070b00e40142101c003001d00b1f00c02d0a81219102e01c0c0171900500810340707190740b2380100001104054442c4001d018401c40e4103a0091190b032160321540000004a100610746080e10141e9101c4081c0c0402d0b90005402141c0079079010080c8c2e5901c1523200b50890268902103003030840c044506a19a8800e02c03c00d4100058100034003e142058441e40c520782c507607003100b00411541c03070880c17654034055014402c090b5481c2c140000c0001d021403003120700c181d03000445115408010440c8822114a5034200301c0d40d0b03541c500598040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 934939586 1250 934938336 934938349
    0xa0213021c020423090f01120809190503060603031e0306120a11010815030a1704081e12040b1e1c0207060606020c0a0e0a1b1107060305010513020d0902 67
    0x54284603014280c900c0d02e41030165042c3c0701c0341041d02c0c0a8000d840800c0b910a4003601b015040d0707210f10035540f0007031150303007001c9072079015161086500c1a11183d401d002c0388810382d00181201c0c029025141a9079401c402c05489001c0c010b0240e83d4408007030b41400040805c0c600856104800074403d540e0101c440f500c091030500000c000b181c2100f8a44408189581c0103601c0650001e9514000c0741c001140d0781c003180e08c40750003100c003c24850541103810800c03c50b0205442c058511442241e0b51200003910110001800c0b184401303d5000d01d40350340c6d264040b0a01101d042d01d411b00c134428605134011281640459460f005c004004000340401d50004801c0140300a0001c1014000741e1140c2c110b0400e401104c95981c4183d003503510030300e0a00030b1134403032524040894071103450350612a501c038540c1c000507256114020f108808032190701300c4045e4000c80d44200da00d00400884480c1500c610003601141c0082c014540e000e0b440040000049403180c000b421040d20b1148041401c03801e50340441c58 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 934940836 1250 934939586 934939589
    0xc010606020609060f0c0405060c100e0a1112072702070c03030e0901080d030b28030c0e1311042c0d09030b06010e12030d09140a0213021c0204 63
    0x40c0c02c00000c3c4a0b225108019190304500c0703410030b002403800c0400c5801240e00c580c0c031400f0300400f8003259003104801c1c01d01407020703a01144007092040c0c880051030a0744030b10500d18111740c5560032590120140c10501042103081441c0700052000354100801200140c0c1503040c10140c0c94916034545400381d41c24005400d400f0321810042500710f0841c90b0281c8840746070840103000d4031700c2e0801044201400038124071a40082d08000554154079004200641145e06842e020440c5002440340301103a82482034080b00c2c061103d52000540711030000500d500107a4102001d14030341101800070480d11602ca180300d10300107000052000380c440c040b4440b10301c8080e90741540300301c11642c80c0f48000f0902207400f8107090341c5885217500c0d0650761018002800a0542c078100080029014042d4a888021241d0f000b52041169202c6500c06211000b50902c00800c5808080c80b01118070180000907900c81819402440d50f00c62005040901c3c00070342014107801c9076111804180d07103900c95584018070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 934942086 1250 934940836 934940849
    0x1270c0207090c0f020d0503070c0507080606040b03160527241215100f09020306030d0807201009030302090a14220605120604030215070c030e03030c0106 68
    0x1945103800c2c511021220f26a040205000340c61401c1600180d01098003510808207041c005c1c0c494a881004550044c9085401801c0303114654010506020005a2501c5560116828840302d03448000780350300c07a040d8040f080300d0605441400e02461600c1005950200c104081c8400d0000007140303020b100c0c0c0740c01d850200a04d9080d4106070721814a4000c0c0d4411104143c030040101002d400d40703195203144d0b1403001182c008442001c07070f10980e0803103c0600200f161100e494003c40d1500040802035000b52030092191140c841090340f014003c9030b446200b0040c54442c00e441c40700c112412070800c0040f07450302c0b03d40d0094000503066005a40700d89240c075802a900181c42d00041414852000c40c250090b14003503140070300d40344c000d9441d03021700101f179100100c2c480c801001c80b0040d00301510454100560080005069001c1800d0001f045371007140250b08450901d1441180b40ca040d901c2944d091001904031003854001c07038050445101d00c4040542203c0c0b401c03802c4180d245c01c40380aa0000c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 934943336 1250 934942086 934942093
    0xb09101407052124270c040305072d03020f0d03020708062e050619091d0f160f03090f081204030207080c0609041e0f0b01020708060f01270c02 63
    0x12400d0302e88551054619107064421080030380c0d0b09542c02c5c680c07000c52214802611101e0340000d404c03610f10001e8030b0040d94081c048411aa88400305080304c85498540c41a803a5805800090100041010070040300e4024003083c1920303403000148989080241c4056056126552000410483c20010b85106000032a41c400e62000c8801c4c1074951080b41d6140008003c142e184248000d42d0b03840100c1d1040016540000701c41058280213a41031801980503441c111105002c0d1150a44001c040601c9404c4002c04220180d640204105000803050807107400184401e1030341d82d800b802a482421040d0103051180c4284c10a40c0c0c0340e111903404ac0d501800b0110452040c00b04142e010400403004d40040c10181a00d0302051011403264044c1503d858030840d1619480100304034020311301d985500b1013a209010611104020201401d40b140c00c550061240303c0d070006184c64003045a03030140c16403002c448050303480c1c0b0004049100382000841c90500c034404100c0b000382d08520071000311000300e8026 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 934944586 1250 934943336 934943371
    0xf1f0c110a03110c06130b030405100e07140415050402030a06030803010b180d03140a031811030d0e011d12060f041205030601021c05160b091014070521 67
    0x18113041040e070031245400b98000b40b051032048101e1001c5032055a01c0740c00301a40365a03a9042032880e200e181d940d1510914544078000106100c0451040e09030340144103400113110280e010300045030302d103450501014400007800e0150386850303001540c100c1403030b46021540d140c403600d50403095407081e807045180070300c0014410b0300800804600c0140704030441d89c8148111149c0c8020342510b010340d8481820700c400260614600d80258030590b04c114507007410440c120302e0b524100048079000301485110f485284c41509031180b24819502c024003042e0f440b00005900051581c181003c007401159000244070f070380c0c4410410800ca00c61059014100c10b051a050504050b0b251400002400b01003010410402820381d030002200c49c11200701d46000c14a6008a1030100c1d41ca0180c00d501941d0101c1c168624010311120341105401400c502c0160f415000f24011a18200c031400c1c22283b00002c9a01300083c00d640c01030b40905070994101860511032000c031030b0306070303507010049441c0315200650750350 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 934945836 1250 934944586 934944617
    0x816030e13021b0319031e0e0c09011a0a120216210804030503060603070201060810060e010b13031b090906050114030d200c0619020f1f0c110a03 64
    0x300300f14070000d01000c0c61820300e5902c07040c103442040b89190010b050b2548244c0558200500200002030031220003000f4a11414000d0390f10762000c0440d00d803241c0000f030004944540b07014000b07291012100d660a140812007e825104801c0f034030708602c0300aa01b8041c000b224480d05194600140c4103003940003c40b4003c2003004910941c2c0300c404003c214001c010080080d40060072030303030440d00031290140c43e6614644102c0c0035000b50340110080e8094900c50f400300c440c050f0480e005980f40880b2009481c0e032205240d000d180640704200c4081100c2da04104081070303110058900c0da6112101c0e015030383d80c55140f48000c0e01c02e884001c036541950b910042207000c242c100b110701030705012070182c1041001c8040c0104074036827240b42d5040d10014440800c583d0401002500100e002c050301c40ca8854a02d000700002c50b0030101010001740c000c4c100400442c0401040910303940199000004108110b40942001803c030b4810f10002e0000354031a520190400304800b01d0b410340f2903a921880c1140000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 934947086 1250 934945836 934945867
    0x20c0303091b09071d0301090b060a0911090904150507050a0306290a0201090203060f06031c020303040605060a030530040b03060d0f080a08010e0606070816030e1302 73
    0x2440500004440403500740b542c0d0b501103d00342c11520038500f59a56000200c003800100300c07043c010300d515610b00310a8038100704e10b10825520a00c81103441e01c1105941c0c2c450030b0103a07000301d8064610100c0070806441d00b481d0800456400a01628000604a0200c0d81400403660700f079906030042038001c5115010039906d1b014000203410864075040c4400312000030310300c0100881940d103154000106aaa51141c0f00354042c0d8101c6400038125800e50409281d0843c501100780c2c0c80d14000e018411400c004640800452116031625500851840e80c8540746c10008003002380142d07070700291025000020680c10001c210b210208008845685ca084107100340117410440c0000740114001c7c0400c003d200e20b00000c0c1ea5004006841440c001245868943d041040ca14002401c408000c61700059803941b260307219060310201014402c00c4c1c3c80300020000c40e030290140040c07a820007004030101003d40c2d510f0180d00203102c1d023003d071001da600c040003c943c00480c003801031000c0e5020640113299117045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 934948336 1250 934947086 934947103
    0xa1e0c1401081305030f0a080a05060604230a180c020f01051302060705150f07030c360b0a1110090201081f0801050a0506040c08160e1201020c030309 66
    0x440d0003040030018040068212080106407a4810119002c039005100c1d00780121108403a50181c6582d44154620010304a510292a140d005038500b00008642c1c0c2420402c80342036a000100407148000d80408414406005660068109203c11000a01da8040140410080000340e4011581c0d01d83d80340e000b41381440e00109000940e041c0010701c0a00801e442031060100c0c0c05079540c581d105047d052262400445890300c2646c0c800c4103040061540980030341d03600800c040d42e010300c46021050000c40301407106501e80b6a0f0110708003901c1d11481c0a211240c6004200b04a0517480030703503181c0e180d00003a00103082180100d0480004140301440034411400d408515042c00c01002c20b0710380008040240c01860502c140b030043d0300079603441c415510079074000c202b160000d0010745400c4182001510b41560303a24011b500707041034151050300803001d0701d2144402940344420f11119440031661448000062a0810086e02000d00b54060030f000414414040b10001e50352030920114151034010f0f05e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 934949586 1250 934948336 934948349
    0x9010b1c140f0a062603090d050c0102060907300204050702070518090a11060f04082a0d0204020a0c0804030606080d1107060e01120f060317040e180a1e0c 68
    0x10458140318461780c074101c401d1181c5404a04900142c00c400d107081c039510404800700e901c03800e40460703041040800240d10304100c0d02a0b095030640d80703450030f00079aa80803a004444452a41c080b0390041c0c0040020340205c24864504480107507082500801c0448006588440c010703040400c041c407035401d0061544034581803100300c40859240082c040798454480001c0106403164081183e00f1a0b50382c0d10a90303100580601106956503603a41285950380004282081e40c42809a90940c411040b1001c008202002901d141d84a07080380c0d0810000758840d03a104018000306039040300218203050040c2001d18498203000907014108003101c0d0ad0710070001c11300e404020904c10b1405020384d0200d07101c0100c0703400e82004810010903000589a00e503030007c224803120701c0c009800400458a4200404403401007060a40c4090800d0f0503e8880c800c0e4010f603603006100c03401069462910303412200c51040200165402d8001c66900d03800010703030824814111a10140600040c031081c0e100d17003c0140300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 934950836 1250 934949586 934949591
    0x3081809010b091c02240d0f05041e061503140c03010207080403060b0a0b070302030a1404061b06020c0601030c0612060e0c030414030d0c03140609010b1c140f0a 71
    0xd010000c4c01404003156101c20a400b94211001151181307000d1800c6a0186480c0c00301c0a54030990360001904031210b0040c1040c01e06d52440481441403080c14065130b003068002e0380340c103902c00c1c0c040644010030320114ac0180c1c0e14001201c8220440544002440c400c00071100c80821a065261400442d0080746100380d01c10042c01d40050807184c2201c1c1141d42c0818040703143c544240000d11044916480700280020004440d01010340c0400108140354007902c90a0350a403801c3e16050450040d070055401188071500000300c1102c0381141d40003160302c9400d01615280109049905011f802e80c422519016411414045550840c155100c00c0d0414581000060f1404418114407000503054105001c00040490309110341c2c0740541d0100310001013100d90b1092210500e4004000c040410f1001920b003022080d41038441098807070040c0300003441100d01e6424800142c42d10384c0449a00d0f06c1602d481000700303100e6136042c0151000e07500520084480b0b854184900340000400420b040501071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 934952086 1250 934950836 934950847
    0x5120105091e0a0209030a110424230d1212200304080904090b0702100204030803010605090307120b041e0308191d070510020708031903020403081809010b 68
    0x6007020b0b09800e95881000003601a1a00c1100500910400803110341500507540280140110b00551030f17029103054608000c002d0481d03c6000700e50b90800105060b024844030100a070302d03031828a131214000810000c0c5240b218440004104019030700046070785c2c0303d17800803002007203400100400140000aa00b485050400004036800b40d0f18155401d100007004030100b030510845006072144404040c004022002d85400c10b503031318560448100c030051261b900341d0881d114642c020b4604480e070100110f401c590a0140c2591180c00010340c141c0c05220b560380008400c43c6000308080c030140580e6090300030742030908011403402c84041000410001c1d04002000281c0d00005c1541e0001c2010714980c80d40f044000480080c2c44400341c609101d10f041d100180260300701140b48011100d00703c4016158141a00085c0d84501d0148a2407945401c148070070b800030a5034a075081d0510040f441c0c0145070603203c0e544d01400b81c0000f5401d403e150514403155a2030300701901ca05000d084401c1c006030408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 934953336 1250 934952086 934952101
    0x1906050105031302101713060b0f010207030b22030e0f010c0b060f01090f03050304090506010905100e041512050708010527190f03030c09030f240c0512010509 70
    0xf0300c82e80a00034040c614182100e20002d10510102407405108443d0400c24200741c8103142a00e10103039000d07112945002030703000042c40e02c0e07039140c06469010303009003800da4034603210a10f000c10000c00c5d505002d4000030000b14024402d1740d0003131442e0300c2500c61190191489041c40500ca0703d015616050089400744480450a204c0d240c1b54401c00c21590f1003010685540125082e15882d413090f01e000c8050440801002070101c0a08180e8503001820803256596100441d03d101041c890650007080c2c205401c0e10681c41504062195140a040484c0a40d86000079028001041d48a4100010300350002410404180110001030461000a0005007011f038245181021002851b8008a1014000e0451032805210320302c044000140c40605171005420081040703000c00f1030440001e45412512800704d80101c44e1541925041162038031480c4640e40e80c1c05960225903004000b04030000240d104208441c000d048820350184c2d54551501c190a60b0f000c464241a0081c9201e10541400c20501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 934954586 1250 934953336 934953361
    0x92c0a120807020c0d0f081c0c0e090a020906040320030d11060a0c0f0c1401020c0c130911040f0b030d090501030e060115030213091a10081b090103060e190605010503 73
    0x21540011f215640c41d8158075a50f4015614840303940201424902501c916680020100b6213a5900b528410240da41d8115090100d2084049050380014280310030300c04100d0000501e090104406640a120103841000a186c6250342a0351b0340068050a00716401600c01d0000b1078122082e00028401c030050614050484440c0e80c4400f0100a80e010400c01405400c0d9031000c06c82d45620b0086699403020104a0f4030342120703034656401012000100250102d86104240c480740d00403c00d1160406042c00300405015404a0f26001a44946459200b03035014080a500142103449041038280f80400150580d003031000049540c2d04800e004200e080ea46000c8146540e01600d40142d8800e240390480c101141580c0001c40c1c41440c003410010480340c0710455048401c400c0b28140381c444203103441107800b0003085038a0100114011007164900c0000030161059440506000c10300c503844411081062134101c0300700680c0d01d050140d55580310100c8c41041c01400c020f2810a1641c0740c0888031116 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 934955836 1250 934954586 934954613
    0x9120605070905330d1401050a050d0506040b070c080c070602010e1605150408030a0906121109040b120d0c230d050c160b0a09092c0a120807020c0d 65
    0x4d0306001d40402450380c403455011601c0400d60b10304100044450101d040c0d8030002c1c00d02a5601800c2c000b034001c10716251204030040550b9221000740b01aa40ba50341d9040100000741074070092000f88442140042d44c010040c095103a8070100409080740340500003425039415807404492034105d504d00031148101c87c0401d50230707100d003a02e100740c1111480c00000543c0c80f0355071200180c0d000104801041d6980002180200e8131139a841d11070881c0003140c02021a81c95880150180500300900400703410103802c550003c41d002000c48503078160600045050001c146040c0740040c20b024119000c001140076902d108a2020b6070019404288544a81da113000b03074003071942445004030f00b2014a400411400c1c03000d158004095a01985c0c1e1613440c20107070820303000c02e80400c00800300030034400f4541c4604071258201003c1d0008240c8110011992074000c00e00c182940d00881081502141c0581c0604111110b0340d47e4005991a100d100241800140322030a0b01c107002a55000000c01d094011041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 934957086 1250 934955836 934955899
    0x612020103050c0d0212150a14040c0e130609050c04050f0d0c121211060603030901050a0e10090503060c120c03090f07080609070b160b060109120605070905 69
    0x20b1541c403003c18010b0309005201e50020854000107000c2d450400030355803035010740742070142c03220140c001008000c2800880d0013100b50807011807000e1902da140c40c1e00034410b8190306040110814050700c1c003040030741c0c1441c50211501c0c1d071242001c01001c421445401d5204100d50503880c1000e080400181d00c85d01061070307040c03240383c00c4013150051144892070034004200302c1c801d401c40c00c056894244840030b13040c0c00742c1e4003198103a810040c072280082100f80c4102801005117107004088001504c4da41c100460410401091007500300710751722201032841c230751051070f02c60055040c91702c1c04052508100400c40701c0d50100511003c45401050481030381c200d04085951a241c1c0d907102400303803508030140d50130383c2030f40325501001502d02408104640102d8050040e141f0603a100c2c0d40303107400c0d445848440704040035007007016030119104440c1160030407014035007104000d50710f5224042120110006441e8940c5c1e0760140b00840c0d030006900c000514081c1e4a607101a060000071203805032031000c443c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 934958336 1250 934957086 934957091
    0x1020901091d041119120b07021507080714180a0f0602030a03020f092707020a0206030c0304061509020c150c07260c07140603100b0c0a080f0c0706030612020103 71
    0x26442c0e41d82c2c104510400c5240d551001c0c40d1703581d4518210b400380072040c00343e03152481e490115985a101044526094040b1a0100c00e1502d90030811901440020040d47c104004008044400c0d00d8207402005c00c0c6030611484004580c0900400ca452034969004d800c8039101544100003d5030088140c4003051014200140c96814902c3e0021a80c803940e441c1503844402c003d102420f280d00042410740c0342e101c20016030100e80d10244266500c448022001c1e610250600028550342d041e00700440d07026100b0702e004107411960000f11f506510058000000325600882d50912150080249070900c40340030b009000181000210840c1c284142c0c00058100038030208002e00350352080c511f006001c03020002c143c1d95900e0001742c8503180e24040c0611510042c2c03031402ca407150315190090783e00816045240041442c980341d11044190f1010140c409580108148000451003000140218000101e44540d40b901c0d50041a81401d178940c00c02c40900d49004807e10204001ca554030314520b81c2800d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 934959586 1250 934958336 934958363
    0xc02010207090204060302070312020f04031b0e070908060f0f060d170f0408120708031314070906150c080409111621020a02010807080c130801020901091d04 69
    0x100e0900407180c01c640390450000a0000d40c2036815030003414641d000f581d6202040803015060001d03482401610504841c2c01c0c4018404105103080724206c0f40355103001030305895591f049030f090f510001c0310180b0114803000c0c010812100184441a480040700081ca00c6501d440c480222810b07401a01322400340e450960340c0c108010030a0040c4000c2c201200c1d45d5600c41c1452904021203a00a010b00c607801e000d03c5203801e100700d04030400e03500034541c03203115a030135961200c0913000d07041e28088041e103150f8410002d6980003002880340c08050050030001283d16400c00304040e01c1801401103403402c1103034000706ea101180c41c00007910241d60380079034041590980ca80c2c02e00b19a02544405503284880302d8800d0041100715840b2071001125090b00e4031b0340f000c00c80800c1e170711112003010103800714101c600002c090510a4045c55884030990195609080c080701d0702c101840803540000195030740c002030610403584c124bc26900100303240540f07102c0a070040c440d501d40000028000504800c04460b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 934960836 1250 934959586 934959589
    0x40c06051606141b030606070807021309060902041a010207091d01050a06030317040c09181e1e24020f1c0c051224032a040203070f0c02 60
    0x210301d0505500248148502900310400c0800d100b800e07a4103002c9000101ca01c182c0b5200c054040c0e07441034400500050401d410b03070301d440d1400c0d030004108982c000b0818580d0290340c900781c40f03090045405010002502c030041c1c0706020841c0e42c9504150390b030350720b0850028242da0b80010940e0070343e14464000701c1d00c0c0700c000b14443c4140c614590340c012554200001c109034001d031941b143c02224046c1c0d44283e011380030b2604020000340c040c0c9001d809641c0c0141305020765200e13500425059401c207035214102401c5038071145407100140240000c0b0210760070020701484881e05200310704500604000701c2e00c40322661880116140724684171001d00d00140b031504442010740c10b0754040f2580071030183da2401514094041e07143c002642038102450b0800707072041740d441041a0ba2440c0403855445006444714101c0b250312040708401c2504004504890500b00c0e01d0a01880d02290072907c008480d4505040b4880c9071034003049040d90080d88144100070007942c3c0807480740201410340c100000000000d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 934962086 1250 934960836 934960867
    0x605210c12060a0f1803111f0b09010f050d29010608011e05060a081b0f0903011d070e1003020303120f060f06040b0904060f0f0815040c0605 62
    0x9180c00c0d03000251016181c1c04035030108001d4400c00c210b039070401078009101c0750501101c070301803c02c0311646268400b6500082c050482c40541700c112004403044c0781c1940c2d15079203c1038058003800204a03240c00f504001801d000c44001d0140815581013007506092001042040340c21342ea015007011808841d60b004440c001940440b071501074bc007c0c2070780d0340c0c4030b000c080d01c4001c003803062942c2a400900c1408250341c509100c0c1040e11401403044e481c0000b0704408031405a00a0300304595101c500c160b004940311100001e060441c40007010b00d440f200f0110400d400c6034103c00742000f00d00c10303107400315140a0b008a1710809036000c05108a40c103407101500004000c0441c2c10094061000091000c03024001000300c0c1c1c07203620075070b03846541a92030006000b0303016160a00540c000304140400e103c800c04050140202c1075010b000004d103540d4a0f00071100c0c00040703038071079603103a07902440502c0121001e1200c8070f11000307184000110340c1030680d500008138007a40309240400c400070403615154100e00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 934963336 1250 934962086 934962103
    0x4060e270a02070c0803030f1012080306040903182408010302060409110c03160b010b120106030b220b03010b0901030b0411060d0905010c09080703080d020c03040509010603020d0f060521 82
    0x11085944a240c208100818103009071800040e001c4165000105680d0401d40340400070307400352f0100d003141c8481c82071001902d0404c004034140a20f002080d01d0f2103080034200401010b40d6a101005030b00315059214500700149000c50810140200610250712100101c070105d6604810000d9014045981d1b05070300e0141d1100b81c0c9a070b01002410803500340080c00d01031407460241d1000c2c48181d1303039480c44160600c00c41001e4152034561a004200a034007035072103990318070405411303003a160100c41d411480c80c40001c440c00c4803541d61130407640440e0500740f28415501000703507601e20055040d925080c45452009200600800550641c2c0aa6489134026603007000111042400f0100c5075103030241c00b82c1400103040b4001000b100700054114000281c99085a4000b01c40034940b58003082c6d10350183d0310020344c1ca40305110400000035651502c2c2a402d00030031190b0f80050715603c04481100a4a90254001c84c40b50b0500d00305100c0c581e0b071420a10798070009008410084255020720301d0800240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 934964586 1250 934963336 934963349
    0xd0509060d022b0f021804150503030c07081c0c060207050712151b0c06090804081225150504022d1306030f0b090a0804060e270a02070c 60
    0x524600300300702e0350803d0305041669a00800d100715840c0c411000224000d100c100c0322000000061503005040c80ea00030307100a001c1d072146460503511003010900e1680034100d40b24650380242003c121151083c0f001c814034152401440304603140700030004103407400c000d0002e48000d600103072110400ca0100210f8004040e9100c0284c40310f0841d040a010f070840104030078448030b00349020200e41c40701d60450310141c10444d032544014a04c07030f80c4810005040c014412a0200f40070080071501c5c050421100c403a07880400c81103a6500410380c0d0541d401d02e00321803081e10301c05d82c40c1450400907222201a6610580111001800d5500c07070000030001c022066085098000c2c42518400880061040c0301e41e1a90079985604040503c0401d00d040740c0d101e100243c541040100044005a00c10203000e07006883d15049a8124106840d0200789900c42e41c80003000c01c0c03003041a030350303141001c0c403200501c96010140d607000041420102040200001c1800c04050303030004055082046451118015200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 934965836 1250 934964586 934964617
    0x271e0c03250905090f100b16021c0201021b031c031503050c2e0e0112020a020c1008041203050703060b04030c061e0905091e13140d0509060d02 63
    0x840072800341003900507020b2540281c000e100012030482d0314a444c4ca014010400500402515180c0c10030542c3e04a4180c1541d00200101910090b9507004407441c0c241c2c100300007110410b211840064500925030714600c40002c40800195125600425903c401c80000d400500b00101c140001314000d020350b08244481c0d00000f5004000d00c440000d421081c030030107541c114122070b420420102605500c141000d0959103170b2040c044050308c24845070710000010b0600310071041038140d0326010798000c92000b10050b0b00c14400084c86107840c0c0450a0f85074480c0c14407200c0340c1401c1d00c0b100c03840d40f03110302d8240515481d1004102c1e418481d03808000103010100304181c070f80c1e45928219255540c01d2140e1310000c0d03889072a00c2c2c0d40340354410000008001980310340030b1316440d08040c0700d404440100880419540301c00010700030b102500903207214804503031007245827201c0c5103071126844c4500da6500d41e0560200c52140640c1d500a822a0558030301141c07419201c1003c0c001e807401038805c840344800001d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 934967086 1250 934965836 934965901
    0x2060d060305031c061a07080703020312130b0a020a050d240902090f0415151418010216210203010e1f0b03060f0a0911271e0c03 57
    0x120045540300303102c408030301c0170301503a40d8984100c0003c0d0514100341144030020002000016403e1008200b40d80c400d0055a04001101581450740b1104903481988004001050410001a00c501581c401c42c4818114180300e60240020102d0041d0714035165100c0e9166412505440c000090346940051450903100c00c130b4603050b1000184d00503907000e9000344410811010070746000d00032010030441921031610b0903460100403181d0591000400802c0c44808a604a01d040c20b00b401000c1d04150750044401c1c51000c1000285001c0c41940600ea80d040946130034416240c4601c1c1426101154040342c0b4001556030001a004250b501400820744c800e031920308840c030820825480c01c5000d0881c0401041903130307200341a1102c10440d401c2d51061028000643c80c5c200d20b51181c0e02c0b050045070142541840807000c80c429078044219100c00440c40002c10702d5040f0f039100f803c1c0c1e1100c0c40600c0c200815000c00455a588907014080703400e04034012002031a01e0182c40210325200c1c1402e202c850144 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 934968336 1250 934967086 934967107
    0x90a0b0702010f150503061f090c0914010c11060a020c030a030f0909020c2e140a0609090b012d060503041505060a170118230f030702060d06030503 65
    0x801c9982d096100f090f0800207400700421040001c1d00440340090041e00c000d50740d84100c1c2c80c5900445442c2c00811441410201d5030680510440d50f0003242c50725031414040c06c120b5041440380095000c10b0401442547d403000040c02c143c4495541482a0f8910791103a01c1d08600b039007400c8400400540512a4070442e03014141d010500181502c51500e0307452034603444151200603403051115600065104521007040790f101c00564040c11f072001c25410581d840d91385101026901000344010040e040003043c0200c458592080308001c040320b0b2010001c0b05e00507a41c41170303503140c1407084020144158984c00c0b01c01d42c2d034581c00d1061b190300400f2502856250f071009455a0000da8007982c42d165180038903450700b003c0d4420350340a10001410041036514181e40042c200100c1c42c14007160f07549540d100012600c05044200803c0e210300e117164428940d41c6651701140c00b540b031a0300000e50040d2030f8442d01d0310002c400c403000940c055840c2e80e0b588159082050150051b40c0c0018010710000031401e640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 934969586 1250 934968336 934968341
    0x120207212d09061407020f0d020d03120c11060619031e06320703020f0d0e0f0105100605090a030c091a0f01090605030a0b0d05100f02030709030803090a0b070201 71
    0x40c5026a1a002e4403076444500440340740c048507048a40014080204002500c0c0c20420000c41a0005042d001d10102c01d0340810050203c0078001c802041c8400c000100600240c0038500c802c07201e81c60310100c2d0703c425685265036098040e0400e4000c404483d81c0400701401e6a100901a542020100c9802c0c0c10441d04584051302c0d840d02650000c1c500040f411040c06107111800f06600001030292105e40281404004104060001ca0501d5801c111120034a82440d0103001120740444000031741800514055051014210a01100d03914000c200901d00c050100403106442d5107285c05521407072503102148004500741c101410045064400080704103003500800381c412a500d038100c11001582081c8080c03506072401c628007080b40c550f001e0040c184108061035002c8400540481d002035120081400d2405810042e10950000341c10001a142c140c050203100c122101c0c811869403522500040c22074442e8000240301940010100d8542401080508070072504004456100d0a09042c007030300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 934970836 1250 934969586 934969667
    0x503060a210615031b03020f062206110c030102040605160503040503070e0105011e080112020f0910050109150f12290f030304050904060203040f05030403030302030712020721 77
    0x581e14948440300c0c5411140c15100011240e003c3c048e0040e03d40700d03404102441d045021948100c001c0e40c25200502501000b904000341115140c50034038070903910416041c14002804280603a00420003082125400004c41d0300d80c503182e061510503040180b0b00700b42188074070740c45503a06118005021034032075020b0361a94100c076826249c003500310360b103035041a0903038000500318804180e4500c010484604142d40244406200a21450b0010700700070000b5034010081c5e500700b810401c18913007031005580180031800034140721514003074041d24096005109026421401c2c081044c0d034400d0060300c0420350000c0c40c0700075400001140743c40c1c2c0e11042510182c04803004a01c00d21020390404810304011017110103179540542143c00a0355030740c48000203544080d0048800c00409180c03080440d0050010b40061442a500542c0d40c0c10900c000a224205103111102c801d032041005200081d80310381c808018003070301d407500e00c001c110304182659115505913401007110404e40100400e178411200c080d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 934972086 1250 934970836 934970843
    0x620030403020328090e1b070b0a0b12120f0d0f0b0a06050703140f130e0402011812150213081c030c080a18151b0503060a21061503 58
    0x1404010713189582d03001140200e204000300c0c02d1749100344004460000c1c03582d400b0300e03040c0c250600c0d82d0343c400c03c030344a41d408804c003a241c404040042c040320228a0082111401e001ca40e400010000c3c1a000c98032050462010300840c50000342184c03a0201003004d684000c146040100088000005504007803e001e800e140e204c0c00c10f544d00820000d004500381da0095070543d807515840341a0aa1680342d0398041800070760b80da00144070060321480401401400340848880ca04902c0c1464400074040900010007000b00a40341c800521503011661004083e06401c907020340383e804007110400c8001d206130111b801840240c001b01042c1f0910009a0f00002d20401005c040e80103103ca1084044a05899015002412610120301080c129421585050700c07001215642e402c8655201c500301c540100120038040c0d102c20720b09040c00187c0c0d42500312990503007000d928510305840000d5000115026600201c40580c11440c00c414420200c003110a40c010000c0140f0305018056248684441c030046 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 934973336 1250 934972086 934972117
    0x4201503011d010801150b0309011122050d031d12011b020f0105070905190b0304060e0606100e0103150b0304051e0c1e0d170405041a06040306200304030203 69
    0x3a1307001c0d0500c146500b51142c018122200c6081501d00c049950000d0884602036403503074040d0059000c81c03801014018520304140e80d84c048940750f89070034141c07660f021901c100406051480030941100c130b00d0012044407400301035010340f09400258169080c100e403400340d628100c5441511031030300b0f4903421800942d4003203d022803190b00700a03090780e408446080c0040d0407a841049103091401c003104c50005400405480c0e1500c540c82400c8a0704100c03800e84850b074403101100a81c00091242640141095481d603803040c03040040541a24520741e00c030303410555216495400500c00d0f500c5036000d000001c046947c4c0381458104103655010300000c0240c180b11840071012007e100003800c00c01d5810103400ca0340c500c0d09204024400900140c030260f006221001e01d48000360711a011411800008400305031110b0905003804102c07401640306841c1c51035525484802a600e941c00e85080341e522080110310242e00c401300c03c0d0a81c0044c901d003402076001000307000070103030040058040180d07040c901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 934974586 1250 934973336 934973339
    0xc020c2107171002072a090203090715030e0c060306130908070203011407021f11161e02090c0c0a080304080703031103040f03120b150705070e04201503011d01 70
    0x1800032031150701c45c018100031618104007038100700e01c61102c4407041e00310108030005545140d00000e80e03000b00c81e0029590401d82080c04442c200d442001c0030414140750030082c01181410443ea01c46c00e41020303d200d0f030300100020301159074001d9140100401001c06011884140c44c2030170482e04002030891081d400c1040240740d5101c20990b440c0b240030030744c0c02411200e1050707015603d4a020030146045032a00d0340d40000804000c13a00400d114000c02200c0e0010190600304503c003160800d2101e03a4280d605141390000d070785c4494940c1c1c1c1124844034440d60711400b6111030340c9810760103e4000c000038000b008000620081501400314903000740ca0038440052580b00300c0115100482d001064192030140000c042441041c680a81c080181d034006201011040020820748184511803800c000c0041c0d200200314003440100010200407000c10818102a0344480c0300e0b00d00d841e5102000b01540071090307050784e00c4081e184108003071030407510390780c0d61549050703000403034050010203250290100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 934975836 1250 934974586 934974613
    0xc03030715110309070603020a090504061418011a090a09090b0405010b030102162604090f0b09160503130b10051212160201090e01081501090c020c210717 68
    0xf142e101384003010103071180504000b0260025008043c0c12030411041410105030b40d119407046502906161920907218180401000748600d0001d5006071074680c0280100084e0388680c094480164a440401c2d4803079030103c01040d120000d03a4003c4401a0034800000180184e519100340501c0c01040280240c45000c0d092509074402c1c000f0241c4814401002280840d005107007000b8015078074204102d004004001c00741d03d6420035040304180c1603451a8001c0c260044c0d00c030b01207292400761243c140c0c0303281c594991110f0080d040d03c0c840078020004001414002c582e01104605980050082a54105800d6011b85100315021365400359500e41c07180b0b105258001600d41d03444c00120000307032600d007107c91001c2105055200807414052456004100000081b0215000c3d2900000800c00904a19402101c6480680c4442030700d074075104405202c683d0102e00d4905802007a103d1502c00011205001d0f24101006143c405d0f5000386c1744041403220850991300301030107c0d00101e6050720000507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 934977086 1250 934975836 934975871
    0xc08010f08030316140d05040b070e04060b092e020a06180b0a1e0f0504020f0a0b03010b03062101140106031e05061503070c05070e040818030c03030715 67
    0xd45034100b1010318120a03c0085c803400408100c1040307a00b0003404e00d906413041c4420740c1e03c152411940d54581c5010070560b240e02c590100c101403000c44080c0702803460a00491030314805c08040301d008150441e5420258200d0400d0184107640d41035805511048203000203407188480003045400c0d9091071618285000b0036205041040d8100f80300245580310310441c2c4005000410342207100010b070040c0c40c001030595101e500300207490701d24082000c1c5014810441d051440007003040c40341c11065410f0005403c01819603040d40e02c100e1b480303940c0e80c0743c80002403a807a10b00281d800800b003807881d03840c041b42c0041d00702c644840c0962101c4210390b40c803064260180c90308200307038030120701c2c102920ba44111180d41020790440c4000c0c00e1001341004042e07040584c0e41c41214480d001c00c4502c0b4240302040020000c103002046605500f0b012401d0a030313502021442a00c0982180c2030f80d16101504c15036040c070a40303d4080004080360350311082464035101e0410724030000d181c114a4070030005454079220 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 934978336 1250 934977086 934977091
    0x601051306150e12031c0608030f120a1404060c090e1509040609020d0503070c05030115170c060a0306050a05040e0a0b15060a050409050a0c1e02100c08010f080303 72
    0x799810403091411400495850000c683c099502403100a03107012454800d00080c01d0a240341e401d040c0c02d00c0164070105c0281c0b202d48e03000ba41d0991041140c0100c50a12000340c6101c3c14480f03ca0303410b151522048540600130307200403d1070500860341400100b01c1d0720360009072000c00307544403561216a0b8007501c59106c9401c444d60701854000760544111441c0101c101a44644140350000b4a024150041f81c0140d4148408490980c000600c140c12700c660340502d58001c0004500a20404070b100400000310549486040403481e4003040403018840300340402c16101c28080e004035112090020000c018102911600d40284140800412107080030b00034182c8101880c801000b01d42c80540d0ba01d40b02e0309000b070000c490209000041500c40d41c94200501c60080250344080d00c0301c1c146840348040384c0c005880c1850070f5142038542c0050700c0c1c22501a070901203c00440441da195200002e0703082480d4054000c24807480e0408401d81103800a00e0581603940100f02d40100e19281c3d80c0444d941d120030b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 934979586 1250 934978336 934978349
    0x50f21070e1008010b0703120203070c170414040b01170411041a032509180c14090a0f0f02073203030105040507030212040b07030e0c01121d0a050601051306 69
    0x4180040c4440080f17a40100001031003860255001740d003d220b04022a0000d65240001403480407191040c042c5102900c2c032001d1480c1e82c1d0500d030900c1c240b800c070703280081141d100d4080c0b034403004400e07407585c0286e00c0082480c880b8014440a468240ba080541e080351013210f6200c3c80ca003a244082c0b189804000d04203050001d4021712142207452030f4032078480314007891306601a10100c0c021540c0702480c02000070388149054000034401541c0f800010030364039508980c0c043d00b800a0700c5240781c1e890f02d01064203d070000d103000a00041c00e420181c068045080016912800010144c4c100480401200c070b1265001d00c21590136000e00c620300003024201d00104069a00a00042c00503181681c804ca17003048203410010f1500030400314200315010200d6060f6142060503040100054140c0136041c0429580c2001e012244240c0e00083c2c0395580340103229042d41d03175070400074001c1600d00c1c455072503404002d41102e05000183c504641d4800c024050b681c080c0d400d00c814000c00e142d0328007500056800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 934980836 1250 934979586 934979597
    0x40c030b090a0c020a231606021516080411061305120105071d1f0203030901150605041e080f1f06050a12060615030e160e0601050f21070e10 62
    0x90740c40e20036444e20404946c0d20200c2d20400803e130f40c6402008079403000c0c0d00c1040e004000d203140a00107404e050b400c000442180d605c1d401000540d200c940c28084410503d402d00840c2c98039a4200112966071496009070098400135040c00380c41c01101e00d00e03044440480c0c003030b5614510010b076682618401d41d42600401c0c0712243e2500700101c01204040110009031040e42c480003010b0208014140803480710001d83c00000511003070813400e01880380c0d140e041c4c08440200c13924080c1b0013041e070f20071741c0706d4051100482c01401c1c040f0500020b8404c001c1056a0880d00604481c07030f09035841c6c2a444000707104045d09030407114000c0c5084e01840003251310060554801034a4140e25407600d5032100b4007200d070680d48032004154070000071160b00c17622680743e400090003210401c04514140d80780c00b002402d900449004c014400b16001c90950100d001c2ca403041d204c100d16103204100b8007a1414805001c20101e042640012001c25500c1c0326500c2c951310949100102020b002040000c84102c200051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 934982086 1250 934980836 934980853
    0x15031b1202090711030d020d1b020d12060b0c070e15090708182a090c0a030e0a14030a1e020a03110a0b01332c040c030b090a0c02 57
    0x107800ea2110380e1000f410300704101d25030480880c80e07007507a001d25014860315a01091111105885201e16070b95000896280050000308143c069034480310451030170100044d2501095800300e031900107600601020500e103880d000e10b40da00544a002601540700031140300303400294140120000c03d08200006030003240c0540303c000c000c40301e00750001c08010b581c2012014000c540842000180908a1584200025480703a60078680340146482c0d0114800c3d824076007071007900c5a103a4102c80c0300e5103450a002801c1210401c0490629045d0b12016098100d240c04a24420340084000e00a540c103541c0c58002511100c0c42080d138503c3c1809900c00140d00501e08100001d010350318403078200042000300c0300c0340b0210b03a4030b4001160090304100607984004074460a0301c60380141c441410100b01c0c04481231511402802019000c8000b481d86420700100d40021140705992a03d07807070000c0150050044420124004d00036080d0546414058603d00300040c2c031300724580c8183c4003066010b80c05081903c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 934983336 1250 934982086 934982089
    0xf08120f0a0513170105040b18060609061207080c090106050403080d1104050303040314010e010b01020607260f070e0a050a0320030a1b080a0c050105071515031b1202 73
    0x1034114480120400f640d00001040720010010114110680300d000468545002d14005840e40400381c10710004000100b81c0001341c0c0f2021403c15480807066405004c2a0740d40c0c170008aa428426034240034a004003007022407240c0c0b01041d0104211015140b03030344266030724101160144902d10010b010490180a10342d0000540c1d081600c00d042d182603c4c80c00c1c50b44500002e4203650040c1d00485100c0c06542007490505d00c280070344040b0702040381c003c01c0301100c030304000b03921054018414020060384a07207082e0100446441e00c40c3d01c0040c1e4515411600c4d0681d421858150213580e207030042092082d40494900e864510311050301c4010742880310140c03030342e5507040000301d43d001180001141d207840e4040c241c40802414010354022074500400d00ea1840c041184c44084d03401c07007002c80d084052100c1c003186c482d0454100b250000e10b8469614009800d00c00d5504842c0d141d440209414846100d5680c145002d20303005803030059103005081c00d11200c008007d40180d225041c100c4842c1100071015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 934984586 1250 934983336 934983347
    0x40804030b07030b360108070e041403030f073209031005070206010e0f07080112030201020712120e030c0c06070212060c04090e060712050907030206040f08120f0a 72
    0x104a41800b090700403103c0b000407600400b050b5914528482000280300d0526144100381c07170300c981100314070019410031440a4a404550003501c034903184000c003007001c20031110841c00460b40c800e07040c0c4e130712410061080300c4441d8096600200148140f0f202c0032002d1411442002c105a07040710f000352401d40c10441200b0341d08120707880c0c1d03072600917250b25103103010a50249500c0340d180340c0c0c094007856042001305008603002610702c50b000c1071103c01f08010940c104800f581910600103014601c035083e864102d019100b0404001c0c0040160100017200540101c2e002030350743e601072001e002c681a1709040681d00e0007071036141c20144d80451601030842c206400280780e440e0001d0946500541400d00d0549014000d489140050303200007820091000c151094051203d010b0000d03043d182130141c001090303401c46c015080c80080d0399101042440034200901c2c00110b074050f01d055102e6540d650711215000f4503203d01c41550044019414810310248200c58106400c241c185040c00c220706401ca84 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 934985836 1250 934984586 934984591
    0x1a1e0111030f03041202010c021209040510170604030e030f0a08070302070b030c0706380a092d090206040e220f1a06010c0807061b080901050f040804030b 68
    0x3560300041003880c0d9003420460045200f94000d00c6000b80000c10b403003000742103407014080c100131500444501015811104100c403800346e4202c030081003603101e44c3c0c00c0c09204c5038154401040c0b003003c103140789210080441d406c1d10480c00f036160381c4d100580749000d0607154000745201104035000001c040e0b00007500000039010043c028411130717000b2074032032800715010380c01036400340c038801b6000c202c1c0d80c00c0007020700920720240304038804880d02050100402140e80606600342ca00440c4006a01e001c03038031154401d40042c25608024042403103400d404015130081d0700012501c0a041c0c104140901c0510300410a12550241c03445140c9882c0041894450b0406031440b90101c00d146c1c02074042e401c070a44282a058001c0244d07018407242032403d40c8541030205070302c6202c40001420455280c0e0042c40001c0140d40090b2207640d50342d000d140c804000c158a040c0c81004081000440300c819500c00c2c24180316100240080182c4d0701c0e44c605d1207403025070880f0001c01c1103000304400e00c0081d643c2c0708100c2c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 934987086 1250 934985836 934985867
    0x6090607060f0e06040b1b0d05060d06051311040903080112030504050301110c0615010e0f04021e040f0906031101050c0a0b01031202120c15040201051209011a1e01 72
    0x2012800704610324141d9156043c05515944458140700600c050101455041080c2e0000c0070b104111001d42c4845034002c202d1010440340d034807400a00aa29408110a591580640204018504011400c0808140d1241515000030828001c10300f1304161054805040d095152010b17160f1900440d000e900251200480c2000b006010000d03040c1c8090090880a45034007440c2506c43c0b0040e0080e0346000e41c000d20081c004000c1c4505119a660051110480741c0419036113081c3c1c100a203804140030348203024081120403244482c0010508582c001307401581e42214030175031000d0307585400c042501c0d0107000c0038001c1c3c40d03800119482d56010340c1c002d00c040c619140a8640d00c11a50300e0340380912500340d0060300d03145001d8203050a015418450b110310018005180d60816480c100070030742d01c84509240c0c0b10340340400b00c04942568041e100b43d4090b00351900301c5440034544200f03072502800c81e030402600401c0c1c00380c2d113582140c5404075020341007200c0310307280c2c12021b600d41c8011101c4030042c3c1c8620 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 934988336 1250 934987086 934987091
    0xc07170a1b0806130b0606030709031b0308040e07030c0503010f0902071509060c1b0b040f080c1605030721120e03030d0605030f0312180309040617060a02090609060706 74
    0x342c1940900c5110f1262261054400b4940c3c03071350412244001e0010065840380004100b0000401d4014558200340c90b080a00c5801640b00c465220003548215013000d000100c0c04900010089504868644075491540d021b01010380311a10a0b91940428010b83c4102490340d2001d010843c0640d01034980180508000c4564610310992041201c02ea25001ea9500d0380750101803500640145030480d080711080060ba402d010a0b1b1600201c11a01070b100034881d14084801100307100184c3c0945100111400c05d460070381d4a031806012020106114040c024081c8100000d8904105107032840027a81d0010211682003050340c400304030802da19110814413120350f8410459840400140020040c0c50000281780c070b00301000c151400303c052503844000c0d8003c10805d90100d551902040d00b01070b10302081d440700c00101405905500900c00b1641e003040c600400001c0c82e0030325241204200e04420162881520b481c440d00d800ea03c00c0f0700703030103401c9241008005010300303085c0300401c111406200300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 934989586 1250 934988336 934988339
    0x60f07091a03040c24050f1e070303060b0a0e10020109061e0e06090c12010b180411010905010e1003020909090f0f0a0b0708060f03070801020c07170a1b 67
    0x200c8510070120718141c40700c50004010041084060413156024101d044080c2c01401805405545015044070601c402c210001c41d02c2e001074500b12050b41c03041000742c8aa440a00c0003180d44200c190440d402c01d80009003009000140c00040e40110f8080c1c0165076501080075445a0078804075000c599102000c665a40c0040c0300421400d105519404154030704074208140520a1031080d500201c01c3c0420301d401030b03002e0005090300041d40c002c0c110010b032004401c501284e11a140107021600025030000180c420b200560a2004507003441184140c850001200381c500045491304501d00a00c1d0108032101c4003624039140c09210f10f8020321045c940946401d0002010540d50401a106041540c0c404200100400c03001c0c403000000c8030003040104810b515503142d104030f07500e010341660144102800410f1003915503940b9500e004801500300c600300b030358803030a042c001e61010a01c2ca810340680303c4041802907800785c00c0140d09920900602c0002481e84841e0b000b0b01e00c0150500307410001d140c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 934990836 1250 934989586 934989599
    0x60903150a020d0f0615080619080c0103061d0105061b0a050a02011b03080f0a0b030a1a0117030d0f0b030708010606230a0f02010b0604080f07080609060f0709 70
    0xc000d115955103070000d030f16030042c6003036042035801c2109000c200a09292060004200013507540ca0300c2c034040c3c0352400f03081d01c810010503d080c00c07100070b00341048009100440c517004002210109118280d03401c200c050303611152510034010090103148100002d0004100d189402d4005d001310341000c0545166500301d1980c030138940410114101e849400c1084113501b13643c1c01c18035186106a417607420145200300d40e40c2c020140c120052140c10680001c2d0089003021800d584101207a03070002c0c0c100e0702c0c081241d0901d0b03421684820280c0400010780c10020540b2401025141000840c15000714104040722440300301410307480110102d482d41c2c0309240207003554100107000041c460f450000030520706219000b0442046103420760345030004800301c140030248a44c02c0300d824661a14050300e1162101108170301610741c61100b154040f07404907000c98000320210b000c0303044403c400101d80c0c9890b40c0720300454440310204c91702403a6400c20000105403040b201180350380300f072407403502c01850b030784549 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 934992086 1250 934990836 934990873
    0x80316050d1e050a060b040330030f0605040c020a1e0c031506050f0105040312020c041e0506031605010f051614010f140a020a050c0a050a05160f0302060903 69
    0x185041a00381c0240002e030241d0041e104158000c065004140b00c55400e107aa0450b8510951000074001e43d00704500d020b0101300206141080c892010030070005001100000b0f0250050041000c0040d01d401e000084c140b070a0302c00c05400c2c1c0d140e500501030b0001035840f45404e9000c000c0e10b001410303000b000300100044004000c0406148921a4000b01d1215049410704884a0b5000f840c041e141041182040fa070304403007500c04a070b038800780c903810b0741012030422820040c91034803036a04142401c9001c0440818074280004014070140200020360f941ca08042e910801d201010180070b10184050207207510500c10640500c00c242442807800010342031030f000990a1010565486112007581840440c080c0502c111140f4000c10600c1090150380307050662030805402c007004541e0004c1c6180d17051b4000d0040c1d443d44501041500c10441003800d2264a5041c28442118035008444420b041d410181c10f054043e643d00c4c10346061902d08650034440305506c00020075605105034070540b02d0150014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 934993336 1250 934992086 934992101
    0x21e19090903080108061b2802011b02011104151709060103021503071403090f0a26030f01060c060905010e1f140a050a24140409080316050d 62
    0x2504005540102810300410b00c3c41c06800020554014500f07001e500802c1d91000340071000c16840762540c03116a52040b48501e408003606a08002c035140049603013580642c441c080361848824a040c00c0c0c80842c1d01203080345c20b054030b01101000709000c207104c940c869020b01004009075081c5141c0076014105030200070300044800c4070550b80454014070850a049401c0c0c0420b0081c00034050070740c241040c000c0c1a4101c90300c00e00c00e032100c0200001d1680300042050080b000b0340306060320303c00020350400e01080516050001020215101d54054644031141200c0c881c480407041008141d0800104076500c5021450a4500036202c6501401182082c03054564100d0240000d100d40c800ca12040484001e26009108416241065090441482940c555840500e84c8d030002465542c0044400040ca80a07400c01c5203040f2400e241140f81140c6003041c015120720011035a444482c95007040306842000b040240088018400304680c2103000d602100511094103010f802c01c41c7d4100b540080350400d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 934994586 1250 934993336 934993349
    0x403020a1e121a100f0b0301031419110301020702210705011e21020a0503010609080d05070807140d03020d110403110d170d020307110604021e19 64
    0x8240c0704070300290803240c140307004003012146450020350540b07070490141d11540780d0f82c4440640000107541449842681d9003d00910b281140e812038586030040090781007404121002d10b51601141e040000000d41f000f680040030350b030461054102c0c1d41e02c145081491107031301d8043d1340a11a00d80180e071a404131100440c81c9a010b1525481c40d441c80d1032606510742d21103414400064040300c2d4100c4914903143c1c80107c06c0c02d02a0a0468a044001300740d4105000b070010207202007a4039482c03940c010000c6040314495500d2144035911000006d40300c0342041001004148208400d0340010004070141c900c1c00e0050310944a03105000082da404c0105103506080000d0f80000c92501d400131a00c1031046029042c0080c50801e0700303654070034100520079100d162140700100460410000f244442c2e000e20003502d00c05548a041203002000a07400598613100450284034003404200400103e00c0d2107150000c007900b05003840c650010502055411b181c40d0440c21100170110f440c4400300044000302507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 934995836 1250 934994586 934994609
    0x20d0f0209040c081b0702030c03010c0504030c0b12010608060f0d03030509010614240c19034a0306131b15030f020903011a1201111c020403020a 64
    0xc1c0d4070700300b004a80e1008551014010303603600f80144803040c3c000b5210b01040741e0801550303c0b981400060310f00400209a07030307031540c00c0681003a540f9500a01800c00c581c0b04946290325036413203015004046c060401a620789414030001000301c18480c6000e242c0000010f403281c24039401c200041140710001038000c1c0d000c6625002482074890003482140001c00c080f100703030002001c421000504050303495640c01c8514a4002004280c1164801280c0d03119082c1c2080b582040107014107050286c1c420002980403940c3c210309502c03280c3d4044060040031a5641c155030384100790383e46c24104002180d8030850482d000741c6003580c0c952420403105009940840281c0c040d00a589060034854050f00310846040b000380004000c000a00c400c030441d00c44c086c0c00c0101d0390030600400d0200901a40c0c0b041341d0f05600b840000380341651090340403000b018054404d11504048440c40074281c500304500a807040717004022901d84040b0650b01c078040458203d40151078141d40e500098004545134010b151002c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 934997086 1250 934995836 934995847
    0x20c1912051606020d050702090601020129030d1103090d03050c01021b010b010207061403070c1e0213060602121b0f060a060905041101034a161206020d0f02 69
    0xb04030228050050502d44010314040c0c040100c000d120740141d0380020300810310880030440c1c981c001e400c4500d00001585502411800300050000d100700c0d1500100d00074081d100401e400c0510441034030703612035001c8000310700d01310490341031212402c0503103c00e5080040501907180074940078001041905c240c000c1e80030f400c06002000500f15080802030f141503601001e0100044d03a003000074a00350500303103034070380d6103036075070f400c01903c2c1c1448800e070090038001089480601d44416411240c03006000742d0305001c0c0603802c0b0f1f01180445809024040250f8482051410a03016100c014001c9004407845c0580c1c542d1400503aa250510ba0940303004550020020080621018880c002c018504000c080c040780c101516046a080301c20a0103604050300c400443e10b0b001c4017503801d850118100504c0369071030704c003c065100e800d60724000002044090110f10710340002d00010b100001c80409440341c1d0300f2520b009198070300501c9a540488405409001c240c005107002d110721009040c48820140c0e9a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 934998336 1250 934997086 934997113
    0x20a0b0a061e12080f07080a0c0317040503030a090305120109090b09161809120f090503011505060a11010606020303010e0106031a040b0303120c040306060b0a020c191205 75
    0x46000076948400e10066204000381da95904004810310780111104c2c0c0d942c03004c41805040fa202d800d00181905e08000762004403241c2c401840c1020038001c0d650384c880c0301890207844a1001e400c2d50040c1070b41c2c0c4103102081c5060000e07484000b4280c400e081003482c05038001d500c072072440d509074044c081c2c0503550503c3d4802e03c40502404c59003c425500600307000300d255828090041c0c41e50143c0e0701035105103581401c0c1656242e126810482d0031200503007a2104411009103402046102c01c1d0001da01c2c003400180c0c03410140960750000308418080300c84a400c3c602400a550800032120f400c025002e01a0305030b0100c28401c0901401c0103074051030396517041c5080c410704c480d41a1301032000c140c85d102c01c0741c1d840d4031405448800c00c0030403180415040fa000000a24501074020001076040c145800d02048075200401002160320482d0280300380d80c2c0c0c0311245085401036841e1880075810001c0003441500c1c0900900808105001c10b242030107443d20106d500340e103503d10b81202c4681c08100355600b078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 934999586 1250 934998336 934998359
    0x91305010305070b1c110d0516030b06070503070807020f090109090b060603090a481a0a0c0501020d29041109010c050f01110d0b030d140307020a0b0a06 67
    0x1400888404d58505044d02c43e440242c21704c512881c1c0c08039565100e0300744602504100300c4200381482d174000d1000f4101820310310100c0190008900100f49031250025503810803106031441241c006000c0e41c10103469440f60490380c0d100f00802c90780214400e5032661039960303044180c1c0c080c0c000000001149031480c0790210620b500a45120f228485c00d00401c00c40f040d00084010400c0d074005144031400981c11602d103400c205000c071210000c040c0480c500d0941806c1c100c91640d2218191540100c1c507a540071031461312030072400045404404201288402c5e00905040d10014802c800040c50013051148074070407114111070407403045011500541903040141605030030801c0844041080502c5010704160350b10420441358140702804d51501c0038401e080c01010200c1280708020300014030007482400d031941c09911680320301c0b480c16450b1001414002070101300400715880721403130407810051082c11900010700300001c51080c441c9500006205c1c100c828002c0c183d510b40072131000c0c10701414484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 935000836 1250 934999586 934999589
    0x2306010309110f01170108010e16150807090801060308031f0803160c03120807021c0503010b071b0b21041104050912070b0f010b03240609130501030507 67
    0x10181000018004a00b5501c030b0302c00d000320110b07181e0003214262001600d655000344000e2120315107620001030303001410740115032684e9044d42500d0b07076240f84105410481e103540c000d80c006610b0440282555a006e10550340d0020900c0c00e0658925686401c1e050950741c980d08201c40020000c002e00810440c042d00b5a8000d00311220f400511703a041015040e503078006c54403424102c452045509040c40f10640000c000303560402a641c000b0703200c0c01005480214203480c0e000040c442c140044d0380a0100100a4441d0062540c54038916480c00503071102c50303042142c2c296201c50440d818125031444e0062802c0c0104004409243ca42c06054501209401c83c6000c4410208880d0304003c0020841c840004c030b9144e048030b0008460310390300305551900011808002242c00c000840c6820b00100f212520b20514039000c0c103013204c0c1e880d01d4040007e40001c0d07400400400f01c5c038108001090345620007408250000c3d054500b41001000090542d60083c40c1241d801030395000107005206041c400b420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 935002086 1250 935000836 935000839
    0x80703050d0813051f090c0b0a08091504030f032c19050304030206031807081506010c0b07030f0f0f020909060411180103020409050a050f090d05070b0c0903012306 72
    0x8401680d80d100d0645034203c150706080a041821790400300b05140350311040e01c071508a803071400b4031526038035001143c1e4090351f903607004a44154005017a008002505121081d000c005032003540e113455a040c0d490810322006c01c01495281c00c0780c0031000c44461101a0480c0e6402d03150702d020840c14000c40e040629682a584c40228150b2051001c100008110b900f01ca60550b001c5589a850700034074600244192041c00f440d0140c41c10000c1c0803500010004403503052006101d840303445580040d51030041c0000000c0c501d2001c1000503400c98002c0d803024203401054040441c800848031080e90403a48500c8145080b140d000c02c041007241807a8034015800301040c0e0782003081c520700940c0c445c2a070041a641c052404010300c0f0201d008d900c40e4040e507004002c8240c05100c60300f00610510050101220303060111401c60000a286000016080540c48400d8598502d03101e0b1070b440307003401580000c2c07101c00c08100c100300401c0c198809110726003094012014141080307640041c2c0441d00030001d0102c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 935003336 1250 935002086 935002111
    0x20307050906090604090c050a030e0c1f200703060f020301080307080703050f0d021803071809030207030506091c02030702130f0b0409060509070e040c0504090804080703050d08 78
    0x108065400008461489000b11038035519400d00e400001c585104540154108500f03080e0a030254903000b00c0500840390407a1404c3c003410010300c484903030342c82083d081184d0055030191140c14090701140340131044800c503d03101d00e0100c4004105113035840c42100e41c00c0c0950241c0300c20018004184203410000c00d1000c4154a10352504203034540d01d003d6203070302411844c000030f504010940030300e0031901c3d200f40b40700d01c40d51500400d142142c0250010301f03e40107903003665014103605150101e0050b0039540344035900314440501d1902c21000380760840c002c0b02580f08041d008800708204001d042c0c8603002007002410b604a40c0b108040c03c0d400a82da45d042907600c240040c50060791024406070394034040300c10001c0c840b0628141040039000441c24680c03c90714010051040c0f00554002c14882c03019541107540d00d641c1c174507103298440c0088501070036908075500b09020902e02904580011406110305509194541882c10300f4072113658070455003544220780381d000d429003043c503003071344002c100054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 935004586 1250 935003336 935003341
    0x30322050703020f12070e1506031605030a140a0509070608091c03181203060b040303080a020d020730050705060f22110f090603030703030b0d020d23010203 69
    0x1001c0c0d440c55680802441a01c50032110486074503800c0c40000159038070401c50382080ea41d013400760b02c400402e41d15058481c04c1241218542c0c104842102d010b100c80300c000d00f5503d602040c08135240d400290540f060540c451200312240d41200e6665030103090f00000c0060f083c142220f0301840c04400c2d901c0b42d000e001c104000c002c1c1114001c608103241c0d90f04904980f0b81404080000c030000c210294241488401d2006584103108414100e0801c9401c0c9850401c16a5103c04043d100b0340138920000300058a01400140c2100d41a00a040a104405809420489156281d0650880040580700e03c0e10412010030300101c250b0200d51101d400d2402e2075450025543c50b01030701c0d148010300810304c020441002c502c2c01e10a542046c00300c0d0700141048060b22040e450b02c509014045842c0324820381121514209916140c007102c3d000e040010002d624010703003560305402034000503e055078000303840071803000540c540e09011111107126900500380c5103040d41c1d001201e0368601c0000350b010382c8103108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 935005836 1250 935004586 935004593
    0x519030c030605040606050a080c19080712020402070c1d1b0304080a0903120c0c050603070c030f09050a0b03010905160909110423120102070308011a0d0509030322 72
    0xc8081500d03003014020a0555490503c036002d8543c690105070480195800040c11100c0895120500d600071141352500803035001241131145414098070360b403500107140820200550551455400b40302410160404400c1e8031481c161046580c45640380258a51104c5154850400800e40c4000c03110385007126a00700c2c8540d42241c0c000104002c0c40840000f1301840810b0052080c00000c5501030055807149070080c034010f06544410100704d410dc2e0301c041300410140380038001d991050703c107540c0310460005261030881e1100040d860f2401803005005020600c2c0c2c0781c410003035002d8820040100d9407549802081c108450004104810807042d90104030b000d04d603c102900c04440202c00c3c0860450500400041c95100703035402200240403030b044060102d40e5040242d005280d040f1043c02e21032256040150a0744642e800060003e118a001408988203c403c55554111401c09090a0007207074050f04044030016240241a644080100228920351030500f0000607043e20340d030281280d40d5607 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 935007086 1250 935005836 935005853
    0xc02101d2e090b1801020d11032704061e082817040f0303090b120a1116060e0f03040b0f16050a1103120f16020414160818031209010b0a060504051903 66
    0xb45420003201d10714030f89100902142000200880080041120cd40e90300c204100c45400310090442c0ba182030000061030792004100a0303503044e000c052080e20a515122902804400d840b800c5606c803550f1516840c0e2402410080d0000c1c000e140c1c1c85000b00d60840c14040d1140246070300c1200e20341c4d030820410382072192040d2515000303050b07101c011403031082020380c14402d4010103818004425091015500740400c03500074036034910340c1f44180e40702c40d160b64405e0381e141e1003a4080d02c641c001c01000721180544e00d07070300182034541481c50006021091642d402d8202a060380301600d00c0700b030300c2c104064076144c280b01f0f2224a01d0203a070b14078a0030440c20f9002d55540036a00d68045410020903886081d915141c000220469281c5010f41c600c3c0340c01105040102c0700d1403143d0f40040c12100020320710340b40340b42c801058600700b04c00641c01d003c4401c04450080c1401409035426540304c41d02036005803241c0029002520607500c5039500c8a0030310041c0b24aa009801590b882d001c40c2e01400c101182445 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 935008336 1250 935007086 935007097
    0xb19110f09040e1c0806090601111b010903080412060b0406050f0d02030c1221070b01290a032a050f03070c02101d2e090b1801020d1103 60
    0x1503402140a80d0740710303001c03030030444040041400d00101600c040311060307100c3c203098406c81c8100ea0030f64803034803003400450b0744590110b484a030503840100750201e200d16443c14210301080c1454000a010f0716644d50006a4000d42d200840403440d40403031204000300c90040312030702e00702503804100042c03400340040c0381d480015200300c5c0185054403050301591001d01c00104208000b038001c211541707070410050f40d50740440103000c08401c0403105960103840e404c0300311502d06802010304a560303400c0c003140c12080b022026200b444820807440d01321030301201c2d0f4040c00f035401300d0341c400244003039a03119072006404150917081c800c14203620042e03119a4221094880c403982e82d030407117a100d40e039401c0306613401960a1000f941c42a208948100490350184407203804d66098011803400011403400d109034000b4102282040210880c0c0c0314400301d40d0384045181c0d0550b94038110540340c2da261111040c90748802964102c2c2610310050641d00d50301044100802e881c41d24024a0140602500300c0c3c030b03070082 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 935009586 1250 935008336 935008339
    0xd0201110901030c2703020310060303120c02150907060f090e011502030d020429090d030e030c04020408010e0c011106132103090b060a05090f0c04030b19110f09 71
    0x3d07000111003192141544441c0194000c041d0015522105e20807200c284a910080744203110740354031262040368a0048104503585a207070707691003c0610240c8400350046c80e4142c000c500c02d801c040b103084244182071034040c000c40070140c00d010307051217002000111070480041c02d03c40444c0040007440c125900c0c0504407400b02080d85051812104201c0c1144111445807400b24008240410040070840d421512000e481182c4070021441d210406054000c6004050f8040d040302c01d5203000c28010800c0320045d076402016201080d001034001000c80e0860b40124038aa95206403501c900c590030424103110203424200b2000c00f40001d91202d507621001000b2562104492003940c0c204617a2405c100b206002204081005009500c0000c0c006d00c4101c00698114003a24003081d0542080e80041c0140c400203003001d40c03141d448002084a900002e0644200e4440821000010504210f4041e0003242c254401c40280c840700e149882c01e8600c14a90345071100300800044030880e41c3c56040301c1d4050340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 935010836 1250 935009586 935009591
    0x2a0809011b200c0d120905010f0f14040f03061e020304021f090b0f0307090614121005040e0a120201151419060309031206050319050a20030d020111090103 68
    0x56030030701c0604200c003031032a00ba00100a00c020000704030100c10f61505e09406070750346954899440004403000d4a48015042c00324000500440c1100e128407882c418000c030941e00c1500c1c182c1d550f800c51090404036401511030540d01e2250416414404004d101000342405056045003856000501c405103c003454001840180322000e80d03150290300c10300020b01c00301829070b88034440044c18a0f02c40d801190b0b120001554000c01158480c02031200c2901401e0212030103080242c1402c03c180c840d14040d002a1509a001ca0001043ea50350700503844c0d00b001c1040609010304880c80c20f05071014203580124150b904022500e01262008405081141c0011184003420900000071550104003c01c0b20b49650304000380109003560150442103a1512079511902218240802d4004446641c015a030b4540c00c64117446d500c1c02803c000c0100c0c1c0c00c0c00342059500004032661081c078058640104521080d110041030801807400380603c42c2502443d000030300000c2000c400310704061054003000c906040e07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 935012086 1250 935010836 935010887
    0x1323010c0201152d031b0e090a0b0a0b03120406030204150305090a020114070204060f080c0103021312051f06212415030506090106170a062a0809011b 66
    0x113920380c002c400840d00000204460324104030740000a84190003120411070a04d0042004017a0000715450410b03008605d070f0686803140010b4002804040b440786525109901200503625407020060004000944005a98500d08508070b9000001022040103141c6803500b00a0900c80200345002c0590f42442c004082100307a11032141103019101000c0d402603d80000072400c0441450f00206469046d030882c1c240607143c00044082c2c2c82000c440b1510300d820400204102c0c10030303030102d0104500c164191100d0072070304034480404004544d8880c05254482100300014003c101c4800d0041e020321380c0001488a40d80c69081c20f00c0360f402c50440b1a88950604e0612a01490744040380480403c00302d00007555a0341000b030f5071003006030381800c0d8a501c1c042d40025842a40341c0c20311585402d070300180c240355000341c80361001808a2144d4103002001f46188001c44078802a02883c0c0d106251942c1205080024000e0b0854402c1502c5010000720a0b144090082d04650429103900b201256040c902 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 935013336 1250 935012086 935012159
    0x30906020d0c080f122a2701020c060f18010504141e04020c010501081c20120c100b0a050f090c0f0a0503090c0103141323010c020115 59
    0x40c80740d100804080d6421170140801075000c161045101400e03654840c4020a421108480c6032088022103048800520740348080900c6180000c0d80d03031041401947c140c109540e0204900b54042d03d0030405000002031583d900301c00040034080f40050038070308181403604000704000300322158507640741b2802102001447d103401070940e03080d410b00068425516201e0b80c0c0307021130283c2400c0c080c860250148401a0350200ca841400151419070b66031a05c000d10740d047d6a400b4081280040031816015403504801240441d200800500c40528021b00001e80e18030024011214101c0130540300e904042c0c0104070b65a10030038184a440c8003151742c0c19582d11800501980d610070b260310700d80500004200d400344075820102852140740114181c981200640d00110100c036032a81c0c172000c8110340c0700c000c512441005212011001d2103000744007100d006c148017500710315050140d130f0b002a80d1205501070a10f542805002200c410401082d6241c0342000000c94120000c60010a045000c412001c040c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 935014586 1250 935013336 935013367
    0x6060c1502090f120309041a0a0510050c010204060c0b0702010519180204060308040e01080303010e01120f0c08070f170c0d1a040303050406060b0304050c090601090506030a0603030906020d0c08 85
    0x101d03001804488118045461340b602c13a00012049072182c0e251040414608815100b0410044002003103103e500e8102070402c01119403601ea540200720081c02030186443c824070040c03028141e182c564200880c01d0703203480d00c050301c002881841164180800c0c4070481c2408400104902d6007c6800309070081100c44540e840b100d07040010f580541841e000200384644100100160345520300065403d030303245c032041540c0344021311654010381181d070010011000d40544801d905031191541e148018540d40741c15100400980280541c0e410284003004242401f02e54600100b00c00300010040c0000308d4074140d00c0e81008a14240280b00580143c2c040040b10001c0304115000558102c0260406050080040c5011a403c0714654501000429044a1802581d108a0b4054000d003180041d800038403d4200010300040c0c1403000c800804640c0365603041c0603501c10301207904002461855810014091a103550060065400100c0c480d054164445100000e0582116480d03580345460200c0c1d420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 935015836 1250 935014586 935014609
    0xd080604050c090a03060c11031312080d231608010b13031704050307170c010c021c050f190804030303051e0106030c0f0810030f0203191506060c150209 67
    0x113208400c0100032003003243d00e03480301c00c0008503565415445464295103954078800d45038003001d0b00d107440c0301c00c000c0500c2c45060340602a104110f01e90038000c0b0101000c09440559100f0404403002000207040310350840410303a40328000b401690f500f81c0c071030b21000e8811901805021240000000c5c40100c1d010b01000c00f00095621208a6403840010301c0b1420050300280500341c801d000c2c00000140a00301c6481882244400c40080d003403803004440151200f01c10508220b8002403d01d00041910003a89100f44119001e500507010201c4c1c50324038a0708000b4440000b120105c800d61800001c40c807000240c80a90b503060400103405d807121010f20031131401d040c03080c034040024000003290907580354200300766006152322010b981404526040d100603104075488032200740360746400c101041e10140e4060b0030500140c140c940c100c4a03011070001800035500140c1e02091040540c542e450240d116410003818146440d4a00406c1c6982d00780303d4810403094050036030307000b04150101d035544008505 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 935017086 1250 935015836 935015839
    0x81222030809150717010b1c0f0e0d090611010e03070807030903050a0f3e041b050301080d02030c1f0b100f18051c0807140c040b030d080604050c09 65
    0x40f0310710b805000100b80c0d100710704000408040c243c00001ea00e6031504c050b110050b0b004855452403401c101c90b41d100a082c40c0420101c15616256840c600c03200a000086456903959610358100c0e0503d0300140000c0310842440c0d03820382c540403504900301c13004070545000e00da00104840d940c41403814122600c2c1c10a40001c1d00728040d605042c0c040240c61400c0400b90380c4a01e01841941070252045d010000e41c00280021004d43c4c0404848404520030380410748034002880040e440301c01d0394001500000d00030070080860000001805100400c02903900c41100c0751000310316000c40f0418840e19441341c0c40d4100545045004544a01800c1da003014104900c05081e12100291009005080508224201001c0f49034400c0700b1103440801d503843c4054a10180170481c08903400315120a1010312507400b030700c11400501000000030301c012125200095000000c094281a0a081004444e40403002d2840f95004d0a200500250044542540036208540009855036000b01003003440c0305001c10b0342d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 935018336 1250 935017086 935017123
    0x50102030a0c0e0108091203100e0c0d18030e09330f010f02060402150c06041a0c071e02040e0d030203040b0105090408121909081222030809 62
    0x70411104640c02400c6146495850000c0c00300040015101d0f07800a886100581c0c021110413002140000000c1d6003180000e1001d5a6241e0380346017403055040161404070384a00000b1b0750f070360b800185001d80400c3c00b590b42c20700440c0c69225030b4003810302c0c2207071054180540d003040c001401846000610540c0c08050034100154941454007021025170803610f0603204141c00070300c1b40210351240e0320590006640d038004140320740390f42d02001200c80c00d150000f0400f40b010803091802c5001401000d010301e21803401c0c480c1c000c3e12031403040001c1200a1540c4506041841610040b80d00d510075544d0f504001040300211004a002080c050855205102040e1082c00e0881700c540354141c0c01584200c1c05a4101c0b20613988030070810030501025200984154000d0010026005211007010b1304034901202c84e104805c1000030040075900c042006482c000e00c04101a020700b030078069965440740c41a0302c5513403000c4e00c60f00c032214040a0841d01500300046500080c0c0048010000040001c143d02d140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 935019586 1250 935018336 935018341
    0x605040f020310240e0a030203070f080f0303190b040f11040e130807082d03010e1b04171009050708190206091203130305060702010c021b1c05010203 66
    0x20602952007542e000288802440001424820701c01003441c04613500300504500941491044505508100351036a0040d22150000016a01003082d0802080c0c81c0f80d0f407445003854090440d09044200c9644105c2d50030400070403500e81c01c13a00c1c90860130490030500040d1a082600800d00400c2c03400c010864403451322600600e9503d054024204841c510a20303202c1030f59580340303002012503050310000c3c00c50105005540010300030704003030590184c9809140050410001c460700060700342520801e140403000005002e0981d10a1000d58405c421000c071746006002441c01084511551280c040d012a00c8464610b0281e420300a9580d85002c42c04103121545590404980340c8202d03208442984c81040c000d0081c01076159a141c4049030020300c15403c0c00120010b03c005081d0078002e0310070f01e010400c40040c041202401c13120103540074200808151601e400064212100b0780d40c220b06660061042e00d00e0440700c01c0b850200c040c400da5000030700c8006640e000010001d0781030014001d5002108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 935020836 1250 935019586 935019611
    0x150207240c05040510050c030f0d0f1a0907080c13030c090c1704110d050105100602010b120a060b01090f03050c010305060f0904060c020c0a0801050f0901020a080712060504 76
    0x11050341604128410040e24410740415501c5104610420790031010f2000070780c00445c002c0000e030815043e10f4050b40c1c544507812003500941c1e408492514a02c540d15000000c2140c0c2900c42c05928941540c8860140d02072038000071424403008007007000300401803001441c075070040e1080e11030034168000a9420700b503ca192141c41c00659014844a0615000f90700c1c1c10f0700d100c0d4100c85000c510000e0701b040d003510b43e40c07030308454030f0807039030b000c64000e420803042100050302403050a02c42d0aa034914010420b081460080c01d580018044a2242c0e4482d08143c000c010003140d90241d151b0301c07060011f03102d64140c00503507221f90355600072a000145070600006010000c51a2101c0c640c1c01d90782008165580000c0120842503c04110b8201c4004030004001405580c0910000d41a40c0101c444a10b580c0700000c1d8122a607820810869444a05000500c211441c000d41c005500400039030512130401001049050010810300c20010111080c20b1450756591055018100192040c00b07401031003071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 935022086 1250 935020836 935020883
    0xa14090c130602150c13060f180e0a0c02010608030906030429010602010e03040b0913060b13032105070b040c09060902041511070b1b03040837150207 66
    0x43c1c4074140942c0800020716000c20384004c6491200398002c40106c018180f2104440e013450071807600e018072458200010441c880b550301040100030422221040d85460700c050400c0d0b60782d03042d0040c203580c1407034414031145d140802075808482041d5040703074681d80c4604145d0fa14810340303100602194503010303c03826030040d03041c4594181c031829002444920090344140d50340340308511545ca414082408100c03207518080d08041109203409801280b015111001c852041e070003c0301c5070b000d4030100340d810420041e5141171581c800580040d920342d5800b020310081c209100d255801000e004119000500b00b02400b20301da8050000c1d50400c008040c3c403845920000e5002c1e009000501034030b8007424001c1c6209841c180c45501184020f05001c500d481a605c00a0704500c0d52000b25001c1d0301801e114449080020304004c000d140000c12805024a020b120f105e854414403c084040158284003a40010b442100407103030f0003001e0101140c1844c0f0010000c1c051081c0c018175446108450307244940011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 935023336 1250 935022086 935022103
    0x4080a02091302010c03030e030d06060905040b0312031b071b050411030601020a060515062106150f0d020d090f0201020d020a0c0509070203070209090a110a14090c130602 75
    0x1d6945007038585482500507000c00c80254003e00184002c1401400240320b5000880c00d05140400c890801c036035500c0310819585150403481c002602100208100c1c039147c060700d1101fa00580c054903850600f54481205803000600c6011240c070040c40304603542907104221424550068158440440000c07224091039140b48070705446181000c455000c1d0195400031039000b808160018000e10640395107460103000c00900c1002d00710441020300c062611200d005002d05080344000d111400b40b280d0f5076940414000d481c0500070112990b00c001700255a008440b05800340343e801c99200c40b2a0b902c640c0191094442d01c800c0c0b0390504801c40c0c208a4286e0754403d01781c0c801d8081c2e800c0107a4208040340d03598142600640f580c22107290410503400c2040801d078008041c4d106491410507150041280110140c1c7c1303001150388007048180038051062160020310004880c000b9034170786401e088588000c0d0140e003040c41007800402040c80c517001d80c0b04444c1c02c40c081d8203c030720011b81e4900c000303512031064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 935024586 1250 935023336 935023339
    0x209010c1a01081b01050702040e0106120305032a04060c060603020d0f05280308090a050609070e060d0c14040e0d0e0913052d011a040e0f060a0b0f0604080a02 70
    0x13007011a1000d0446619120707900c04c0c040e5170341d17420842070340c0030030000c0c0c5280b00a071a4107540c0d86201203820038800c20004d494500984980340d881c10011520f039a02400031000e090210304990005600c0b03800c0340100c80840c5d281c1d00d0412102e16031403c219000306003681c0001d610042c2404030000304440c4040f081700c414058401d546400600150700040117210300101032440b02005110f0000a00411500b500006072408a80d81c0c030388140c0c0d4240c60304409484803082680042d1042007034540c8001d0300c0e90700150a444000c450a0a41d03202c2d000c46003140070381c0300001072400c20305040f0384696005c00260310a00048681100318805e014161030b0131084001d0082d036900300061000400c1d41d5011940380e90002c01803400c0c0049001560b00c42ca444400b0380e00c0380040c10380c1058203000900901c444d20070404960500d5460107410001114000c01c100801074120550582c0c3c0c4d00c2c000310f18641d010756080b0020401d440204d00040c0c10359002c071501d50303202501040204140d100000c10304402d520 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 935025836 1250 935024586 935024593
    0x30303061e060721030b01120c0203070503030a0605150f0315010e03120c0d110a0b0619081c0c11060a090302030703051e390919051501050d0209010c1a0108 69
    0x10340d404c0072401c0d190303c1c2d0382031808180244415010703090160311000340c28806105481c10f101c041d549590442d44290f412840c119250340080c820340ca0100d41c0040500d00004105141014150030340b140c07804020003072410240d81c88401d0300aa401510207803804a002410b58107a0b100300d148802168100405407040c922034640010b18a074018045a000340c08004014020440e8075981c1d02010b10b8004c004035004011019802215103640c1c882d100035002c50005451080e8014200f000c00180032204007003001000d64820010031610324108040003802e840b0599107425807d4185c9200d0440da000940511070710030300100740040030900c180c200c1030480201c802c007410803080c1035444040e00300301e100d0303200301e58400b10080124a8003d501840c1003007403111040103100000e40e50140494004c0480e2a5240101c1d601c80182c2c41542d40c003040304000071460803003440008000d40144840074510550000b030803103442e0f000d9020121200e9003c0c01c1c50b80301d8101c44a0800005000f0300c1004030510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 935027086 1250 935025836 935025893
    0x40606030308090a02130506061201030b0415050f070c05031c0f060f1a03070e1305182805072105070b090906010503130b090313090605030303061e0607 67
    0xd03004101c0484c003a8004016001400c0c4003da1500101009003605c5d5010800b041070090400c1c05003c454001c60103840e11541e5860a0f0038024050b45a8000110b170043c03618042106007140f000c10940c024500d031424003080707042480c1280c80c510560904406e05510786000001c54030240d00f0603610707a41404d00c03e1106542e08d882640031803101c1e004000112400b220301c2607006a2070406507900c100d00e46001d030303034040082000c141c00070081d0082c61501c5494800b040807407045079401d905d900080c00300400000c0030300d045a00b2080c1c0e200403001c54840e11000e1b8a01406402c022000282c15241c61401448018103a400c05450780407000719200d0040d1100040c0f003549130b20130f6690000001c0c140c60303000c0d038841004503015031008003650b5002001001308408618042005031191032040001d540d10710a800300880310000650020f12005d0070900c0a0000c1c0d02d0110580340c115009503241c05c544440010714803580f855060189402c00320103d00ea0013402814410a1401040400305000f501c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 935028336 1250 935027086 935027101
    0x7240b280b0f190207033c0206030a0902121b0a060908060a2d021b010501050a030f0507120b061005090915030a0506182b0e18040606030308 62
    0x5000301c0740141220300d414404150844030701c44183c24009071610640f1034054032907a48602c0d1a1a4001c402c18014404900c04140c1d845032640a80301032800907081100807403540003a00c0b51100400d520740703154a606000e02151524203901c0170f170101c0c803c00d4926002c1c001030703a440040141d900700b6121302024140010014040e191903419601100060a010b0342c45480c0b8101410380c080c04a910640c2040c00300c2c00b4424902a21a03402d920710b134001d030340d41c80b0a040340302c410140080494240d902d02401006956101d040250403245d11a001521701602c5041080c100501684170b030061080340000714040000d00e10b1110320800341180c0c045040b42c00c40c1d0049429026201c0c0382ea4000f0a207001007500c500c42020b00d48420207004040340c0f405080e81d46c41604140003501d0710640e19080e41040071a4100a01000306400c2e29203428020120352608800528001c0c8140310003442f000001003802c0d0b854907000319210048807078041845050038501017004203018401680041c8c0e071240440da40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 935029586 1250 935028336 935028359
    0x308070c0b0703090311010c080619080a1101031107060c030f05010303170a2c0d05090a0e060d02090103050a231e1510061407240b28 59
    0x30300c1d0806414907155070303160025401007440510580074402c1110b500704414509009040000c5400d98a03c0d50908100e01404443c0070500065000306000740c01c10300c02e0560001d61182c0d0141c0100b011012400b0310f00040c0d00402800002d9020040001428014400580c002d5880b80f041648c081200d658003d14420445a080c0030050000d0201c0034900c91802e2071003c0c00360408100c004c000303051070f6841242c2d0180101c02254807810b10404100804d4000c0170311640352604654242940380c04c2c600c0d0006240c030680c6004000380308d9410004101a5103c03000c00382c00d0279501a0940c02c0958481c10a275a40d03221501003110903142044941c82090141d0800e03445040386c1078010271220480c50f45409440354804030440d541d00c15203080c254444501c00a86008806050400e1022401c155009214402a032503002c45514200100400585901d110032070780b1904a24400c1c1041403001d0880180410583d0b41e80c0c85603480000011000080c402c0d41465807900110304c40c40c540ea0081c4481 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 935030836 1250 935029586 935029607
    0xb0a090206160312060807030209060a030c050907030e3702011b111c021002120306011b02040606270506070b061f0f0905060c0c0103020f040f080604030807 69
    0x10407007001d104081040807482560328926109003000715525001c1d2580000300e5009902c82c00d1603500c03d020400650502e055040c0d00040f090358001c0303441c1d007141c903403195507c03d42c4542c0f030081c16401c00194403039102e60f04c203102d1800c0c4d8070103495001c1c81504d40b04203414121100136418101c0004801d8901026040c040c24069040e1a00440da00000391030301c00381030404d1019203100c60360345040641da545003284204070829120b48880b5850540c014400c11015030744000043d5440005088081400da0060741d51100003403800e0400d0b03904e103040300c41d406071500e20000d401a007080700104289400514409280c1580c2c0c0303004c1c41503d4812000d005000145c41400c1e00000e00f08080070100d03107180c82d0164485006024003409408112207200c80300d0300c40c5446800503901455a00e1000e6000c030100c001000103ca040342020080484140c5408081d88164141503000035410031405514040d02c0c0200b2041460785006c0350b4824490303882d07800855003100003804c01c0300003c52842c0510f146c43e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 935032086 1250 935030836 935030839
    0x80f010501030e060406050a02121e1003030c1104061509140105090d020f031c050702090604060803031f0801020423030d12150528080606060a1206210b0a0902 70
    0x4045d0300e42d510b50100410b0060004462241c08000394003003000c01541ca42e015120707010118036800c49001403241e40400181030703c0410014003004102099100459006450300041c004070901200f40001e0000e1405d54800610301c0500004070000b1030b00030301ea89040780ca107042d1030000199880e0046425229041c041da520640001c00c101c058204100500e42e40d6002404a442901285101052001c0b01803140d0000400c001950030031414401480364000740e06071400d020007800c00030b0080d103a0100903e201c0c002c80e2110b11080e0b400c1040c0486400419030f0702c0085581d03e80f582c0400d00405503010f43c0c2d03203449040d45405001400d00240c6401803003a1951682c0194407060a51005481074040c031844441d400300c00071445a4404c1c03882d609074800c284207200c582140c4034040120882070350080b0780c0f0b50020300c100318140d1903e0041780e10745840c92070545429407680d103960006040c290003000000440000b800500c040c098504e4800901504170b101941e51841c6544040d41c0c01280020f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 935033336 1250 935032086 935032093
    0xc090f0402240d0203060402070b040507031a0f1306090b09030918060102030702121510090f060308090d0f080a030c022a060d1e06150201022a1c080f010501030e 71
    0x40302c6805499020315007205001f4805842d195060715004c031924010346003070300c4d070b038020305010820403485215101303124211700b42103a56850100c01c2034146100003000c9140601c11303549a0000c005040e408100c8480d4880b900c5110740c10300000e4190740c1e4000362501c0703000d04090400c0703c101040041c138480c820b100590045203440010303406d102240044500040e0244900505426180f903052b85091049a0840d80c0603c0383d482c0c8800740094500000c40150450301e020307824004103000400301d03000804c05840f41120030a862501c101c210b070321810701070301400c8082582d02000d941a00819400803241c1c3c2103903149400c0c402c00102d0460042624009040b40009003001d03401d000300980040400d400d800101c4040080302c40300030281000814800710b07544c1100b44a01c81c03e0240c4100b01d00c9140c4021800d1455400790040b081007401c090303007d0120f4045400c501c541c1c0402ca160b20090320003900c03008a86030b4107809402c061069072806544040740e400451a94482d100e04018900010f004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 935034586 1250 935033336 935033347
    0xa080d0e04021e070c0f090f0614011205060307050d08070507080f0a15020d050403020c04060b0414040e0a021005040906060c030225080a050703060506011b080c0c090f040224 77
    0x584490b54007018084861172402c40c000a2a00b2480c0074520040c8510400825450951045542180c1e000c1e0050120700c50107084500403071342e01c21010803002c3e00304200002c1d543c5906001078980501c560116510078050210401041103510160501502c114211031280d42c9070341c03065440740c030200080d408940c0021102004075407002d000401504040c440146020007046103241521422070703050300564040c5000140c2400e1510400c0010301e0010306103424507051034114850079014030341c52481240c80d542c0c21940320100f400004402c80e40101750302994901008050410f400074425458100d140c62000180f160184c6502e10400b80c1c99806840d05448a2030b0b00294068a815000c695100340500403c08840400040489d00e0098004200540c07651520005a4100034a16810004002c0071100d0103405410b6100090764442c0245844d06c2204110b18a00b0510b01038469200f0319034014000030240000c040ca01850003914003250350103520400014903800d0040b800380e421310404c503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 935035836 1250 935034586 935034637
    0x8030a02030c0729090c01021f020405030102031f050f010507030c050c060408010213052b170f0405042a0c14030d0e0d02070605030c0a0309020a080d0e0402 69
    0x45601008601d07845040441c44d4403100020600307070003001c100c0c10746480b000c501c2da4200c51069500c903400100503c10803102d00300007074a510000c95808109003119070340368142301c4260103071400f034074014000715103d1a01c071142140915071074404020000b070411012405040c0038004004075035044c2c403030a02d047d299540031964803600300402c2d10540100c0b2024602503035004001e20050804400158548021182580b0104141d0380282d00c1010491038880418034085501e00004101c12041d012518803828014540c4220a031481c40c040d41c0040c460f020b4201c1c5802401c01c0c0c034402e4030100110000050144c036440b89031031513030030300e0046d14090600c414442e900418110348a51301c0d9200c1c003a01d43c286d1a107190840c0c21149941c54446800780c02040007082603080c03205180c4000c1590324500307039000c1c02910000e400c030f2042d44030010b403403241c1c94041c0d000411001d6000e4106500b4940e05c03030820303849420b20f0107000009012100d0b03500103442c150003a11340d889404600c458180350840c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 935037086 1250 935035836 935035841
    0x1716110105041a04080d090302010e19050705060c1603030f11012d110708070b0c030c070b0c0403050d0e1003060806011502010b030d0c0201120603150504021c0f02190308030a 77
    0x40c421201c2c001c00700003800d242c0c001801f86105007440b94001180d01c04070707103e10360706100c100024964518460368554000c100c0000f4a4000c07101d05aa200c1d9840d031189807001c2c2049652005d40e4002c400c00c40002007010780c40201705e4501080c0d82d90701c440245440c110030f4240d07006c020b000001b115110244243e01040c22032a038210082c019030018080000b0112360003c0c1c0c010b8002a61161000308204050001581c48a940000c203c0c0000380b0f0f501c0c0c24201c3d601507008020000c4c24402c2d01000041c11903400e4030888004d140c03c042101c4c402070f031094004103549000c08180b401070a0700c0411500580c00781c0508002c1c0c40c101400b42019a08141c103c00204804074151004c56481e031180030803548040c0036991013086641e40d1031502500030b0001500702280d2440c101082d9113004c400b000030490301c4a01c0c00807180000e00100e125210740c0005041c051540ca861011018040c1b038188c200503640042d100094802d4138034980a5010928460088146100c0500700080030000102024405e9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 935038336 1250 935037086 935037091
    0x412080d050f0f1506211b120705130e0a02070c06020607020c0f03030909010b1305030a020f1c0206030a06060e06090f010c0c030c0e0f060a03030e101716110105041a 73
    0x5170603d401c5c20b4000140000c0c1101d01ca10f441c444888904c14030800300400400c0c0490320f41081602447d004ca50101442c9080e07000701075404000000ca00d1091201e620711502c0020a4040d4058616051480404000b5441040300b00d03240609481c0010f41c2d0750000c10b0440c0309210075000f03803c0070442840bd01540303820098189030305000402c008201030b5601c5c81c1d600d001e0000c140303850381c03251054920951241059000315100b6441520403000507540c00d2810802c4040030b9614400362104000070340800594030310000c1d0700038404010070900c141e1950120b003c503446592481e048000e203000b03101c5a40b00b40100c858001128403d1075803a0350084e41d207803c10034815100180c403139a680d01c1c0d55000203c180c000c0c000070414103092109841440b200180c01200072240c16005901c0c41da0b0141001d0000034205000303e1000e060b40301d1782c1e402240324076842240c03102c1308899454447c9598900c2c2c0f440605280c04a00d501d418170101c440c051080905c07aaa21404c800541c00c82200380c0120070400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 935039586 1250 935038336 935038339
    0xf05091c0306180204080d3209030109030e0f0d15270803060f01030b101b15091209060203041406040909060501050f04020702030601090e030412080d050f0f15 70
    0x41e01c2e00011020404a4031202c201c0e140880140c4039820000da4074181030704540e82d84108541b140030481c0c07075080d0300c280240d4a0a0803001e5088907001e248041801d0054420340c07903242d403030540640145504020000301000c800c44a800705c0c10603000c10446c03541e151400140403c403034001035028012180e4090010758020394103c012124070003204611807401c0c0c1030111003074000402846243c1c10002e8841c50303402000d080c01e2010f028210f010074104130003c074402e800c024030080011801003045441018558105c00316035001c680c18403141001d48020b4000300c0d0010810300f6164140d030b100f89246030030b549555000d980742a1812074120b80344d520070070005610100030440000c0c40c400364450101d01511032040410558034120411031007a14048116018600401c41240180c1d00860700740d0649208000004d0000620030b8030034a9400380f07800030383c0f07900540c0c1810010321110304050040412510390034001a5290740e208501c60100b501d220f00b4003000a00071886541d8030300700491481a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 935040836 1250 935039586 935039591
    0x1f0c0f1403060f2d1c021302090a080609060903091e03120a02010b03330406271502091005070f0c0b09180f04080309010603060f0e010f05091c03 64
    0x41e41c0c3c00100342030040100038920700401c4200382c0c07001c01009100b0401d004211440b8801c00ca00301e04000944200e41c0d0020700c00c3d21444402942c140301031b0305a40750810054403a0000380c0d01c40188641ea2181510140b10034450b4600180480b24000104e801182018000950030408128404100a80d034070035642d141c0980e005102c0c404030540060010011305a0000c45c0805417a018103060032060104040c01c60030400440a0449148000840a004080c0e000010b03603183e00f801d4008012488bc41c440315400002c01c03003c00c12102d0000388030356001c1c00a032406e02c3c40b04240c0800b03e1080540081c0c02c42e980d404a99543c6000740301501c44035005840385a10b03d620f40d901d50180b400a42c000d644001c1003c154003085050841001c1800d007110184404c5504152a01070f000000003800108002d00c00000035204400039080704008542c824818044803844034080800780c0102c02c00c0449a603c0c000d40082c0342c44a50081c14054034003c006405a2281504880c558001d144401e109254 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 935042086 1250 935040836 935040859
    0x30601140d080705120d0506030706020601060f200c0a1403100207140d03061701061802031b0a08060f0306070f0f021908210c09060a030603051f0c0f140306 69
    0x4c0c8144524990441070780c620669400c04040d6800841d00301811003406a80038810070300000c0c0d000107080303041d01c0b81810030054207014260202d43d40a00b81c04500456490300c003030401018000240526120412140d00c199980c44030887c000b0440000d19a03503040d0b201107510011608554001c01c1d03d0341c028509411480f034510a02d5142056605010000aa5580c001c100310f442c6600c2c0750301c20b01c4440000340b040501d0302d400d0414940841020365405540000400e201d030306c1301070352001d020143c510065101d80e0031210140045104841c0d00d40a17810407006124145004200e0034481e92003074491444c05086a04216040c40300c0514210540c494281144840e4515040700c030445403060422a45c1e40307040c0141c0032021240484001c0040003080d0034002004040c1050300d0140750107442c00c503158400c0d42c0d8218060442a0b2000d0100c2c02504484051200c1810303100c401c003d0114000e20000f480c0010880701014040c02000000340c400b184040d9207403c050083d50000ba0060020aa00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 935043336 1250 935042086 935042093
    0x9030310030f03121d06160e150c0f0d03061d0a05190204030c090e03041a0c1f091101020f1209030307061e05090d080103030c05120d0218030601140d0807 68
    0x1651003901e510281140c1c03115002c3c065004210080e4452900540343e294002c0700480038283d08020322142d4410000000318900c4456a8810f5401e0b442c040020bd5102c52104c03c8c0f5140c98000d42c844800011342000404208490703028110340e81e0f284102d21401300f503a10f100000c8000d11300900364030703050580c41c1c181c80b103200c90030f00142014500544d03448000c80d181c201c00d0805c640c41c14035004810f4200f4403007040321200c0e0381854100501c10b202266074940c2645281ca007403c40490710300380d0076640c1c0880104000c1036a448003600b203104100304400c03c0c03440300c016695110300c40c540040c0c5070b03c110b8508800760080340203400f04c0c1c0c00c082c048900b815081c1da500020359103450300000c0070f103204c1824600221401d00549800030f21100103007008840c81c0d103000302100014003014080c088100308410811100700681090b4450351607079161180038203840d90b400303507006240b050307102810909031185500c1c000c40c585049861540c1540e01188600c1d0500c4034150548900345c0b2014400c2c001000031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 935044586 1250 935043336 935043341
    0xb04080a02120a030c030501120c0e090c091003030e01031103061c080c060708011403070504050c0c011406130e0a0624030305041508040b060108090c18010e09030310030f0312 77
    0x200d0544d00d01250a14802c94010210740c0e05901c80d0041d100850220701c0403980010303404064a10b01c4600a885580d1240d4541c9042010801503811004420402171056a04111881074030702c01c4c2d07a40d00342c003e4035000450549100346416080d1040410104105160801c14500400c074144070483d501195070b141c1c2665074121a1500846410030410041215400301d5403a02500180c8009242214000b020070703030f2151359018450242e80da400202d0307000314220094414182d0140b0081c01680000e444143c4240ca007910306901408911540742d401d10724034003c40107503000c0c54005255070782c2140c4500c405052032240880c03440700c45908440c0100a0000404040c6003c0d1719407541c0c0e02d24103004888503495100814007048109002e0100242c0d2003610035400600901c1e010201d5200c211880d418080281c0740103a004003002d404210200850850314102d40e40c072a5019100d80d50000074686030312084401c410120405241403000134240030010804502902d800c100354030544812004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 935045836 1250 935044586 935044597
    0x114030f060411210d03090c170c0906040e12070c0b0301060306081005090c040b0301020418090b09060103030215091203180c060406090b0309190b0906130b04080a0212 74
    0x3440300c0c5800000b6000c0c00c180b0940c444c6880c410845020034001c4010060b11400300601160826481d00000800e000c000031440700a03141076801d070408440072400c00c1d075071607001d80c07176403800b031503815001030b0721403400e440303080340d84941c0e078014192400c03a42090442c142d002e640c003181e4221110601080c0c1c10b1004018601078031443d14005421810101014540008000e0204c4031034142010045480700c085200303e000c14041c1d4003c0b40740b21118001901900542e00509501d11401c06031248040058200f02a10b40c051180791105845501009403282d509010260243e403121a40071490680300d10515480b8120030144c0b18080072203071030040168030544044004494003480041ca1010501c4440c21040003140d2003460b09180080c060f000440d07600c0f5800d0203039008000140385407428050034880809801204055240c075103000c803e0071100b0b4510f01c02c5445070200042803c1e0044215641d401e410025038112c0d035560380c0d03075100740d54000c841e00130850052800e4038940400b042d000d0034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 935047086 1250 935045836 935045843
    0x30c070b032404181a0a02030717070905090703020d060914160c05011127210a05070b190c0206030432071e03080f07020315100e06010807080114030f0604 68
    0xc01c5c0103101c220086501d4010b42402c00340352040060000c1d4175000185c124814000030200d00f540e964071542603806810700d0b400250000d0340b103010800c0180d41540244003800403c4070400000d5120f07225141260005c4d40482c4400c44660003007032960a040c001034103c03128a01e41000d20280030340d00c917403e4a0903d810741c0806900400c50b0502040401e10701030017072030410b640300056907c0c48005256403490140c11511410b11210b4859580000d01085420542180456008603505e0880c0b05095015040f018400d1035010502c402c61442000c02d264015001010582162550744070403d2421f8441c40c0f004c01c2030004090307000c1003602070fa860112582c046000d41451482c10b22692510001544e09204440d0359000c00d00c0001c2000d8143d902c0b40c1001c001c1d098a0310441d00c04689001d403020341e89212100020204958081c103402094151248000b1840301525681d00641c1c035190f00f5990780010503075100050002040086d8407144a2000030111503c180c100554242414030646099 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 935048336 1250 935047086 935047103
    0x92808030c0c1c110c090105011b0618020307120c060503250e01030507090803040909110607050106080c040902130c090b12010e06011107031704051002030c070b03240418 75
    0x59620f40d800c10210b521200313021002d4518680790b400042da140105010f500e05001d42505995202d12200301101e4919074425020010000040070440d03440c8103108089120340f082a0006c140b0124000020070720940c0005022005424624140e0f0703941c000400590520040d50491403a084001031204030001d081c0d207410a81c4054000018141d8070024030340414001c144074108030030240041118101c5a84400000d044526031520895441080441d5540110082469010700c0010f500c540308950034181214141c800b00001c0c8030aaa050850183d8095480c00b8400480d41e46030704002e5040d001440c0507010b064917501201010f80000f1050000c405140c070040c00b050500528103071700301a00b420448040443d64006560301c02403400002d00e400b020000728584680140c0584000e48001000d2400d24660340340029540e4000b06220402072103030700760000d003295440341182e000780403000702e078400641c1400820111807100900c1542040e55408130101e031105a05200206610400c0c96 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 935049586 1250 935048336 935048383
    0xd080a270905040c1406070f060f05100e0a05010e0606091306120b010e090a1e050d080a0f0e0c10020a060203010f081e030d05040510050f092808030c0c 67
    0x540c002480794208400146041045a40d0f90f511b0100385c8408941c0140004035160706860400c01615940380313072289581c10b2009001f00c02074081d00d210300b91910440b440207603503a50820380098172420720410310050192400b18155003009002000c01c8800076028070442c6041d09003500480d1005d5008420500c8815400400c1003c80990540140b98159501c1007605007094405d4841d011000000c10080104200d500c1d032100080000800079000302c1138405260030b404001c0c124050444012a406142004141041c50980315051006040100504203d00c0c550b00780000c0106490a4800f03503c1404c0f282c40009440d400194003038403035448046845883c0c4001149170070043c0c6071070343c54180004841d02a840000090b1a0181c7c0300f2a40031550ba01ca40c00c105050a8601407007040403818641041108490140c20382d004400480840e0343c00d00d80605000101c0d16040c2d042141c90050f50380304c2d03010406000186030004801c6015619080c010a0130344e2819045018211075003448a10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 935050836 1250 935049586 935049593
    0xb03120304050303010b0915032701150501050c01060905041a010609061704020f04021b0c03030405010504180e0a0f0b0609010b120702010e1005060f0d080a27090504 73
    0x84180400a845246030450515946198030703800140101c40c002403010501800c0769903032481d4500500c0c481414a51b0302d041880c90110401080d04920105580c1002201c03640c0c40305200d01300c803c0c08802e400840351170400d401114250302024944240e0340d242c0c240803035504210310039940510b00c500c0f801d03240d0481d0201c688000402c168460414000c5c01001009015003040e10b19000c2b41d9521403000c13240d6554400034910040d2040c00c1da40180c40415110b0800c110030340392454880c1c1403021240d51140301c20426a0b6441140500c43c0012418081084154281130000c030000450400226200200310101881c10125402c29501408144410824859075600b40340c0c00c00015940c4020700d41c1000b6100106228045800042c0034407900000c4450b8402e521668985840c44290b0300300c800304090320400340005490b240c1c841c1120b102000e0003441c007030000c00b141a40c4199035606208080c4801e41e0348484810b40405007000c0c0d220111030010410b42e402c0007a05689400044c203051034107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 935052086 1250 935050836 935050843
    0x309010c02271006094a090105010b04061b060e1c030b01020703030c0809010905090a0b1215041b0b0d0c1803021e040f02030a0207021003050f06060307050705060a0b03 74
    0x10302c8103013800882e80083c008202c640603060b0140c003441e00b05e5035454100c4110f0080e80718809446a202034400806d03442100c00300c921040c01010103400901060340c895800741c02c00d01c0390f4400e0201148108250750480512158001c00d02c0d800b59400040320100030254608002035042040b80c81540600c0300d00d000c0350940300e001c6400400703200410030541160b4002c0c1c65100e151074050324860b40400c0200079a0300c245020b00242401500f040c055041004594010300104958248941005600294054400104121580e0020360150219140d580704d402c4c0d0100c94860b010303c109000040451407048550092015200da0a40003500384e6104800400615080000091250a07104108090303600c16510354030b07420f41027800d000e5070b01003540058001c24000658071451400401000b0928a256000e800c0b82802500c40c000d803201c85460403800c94108644008032405480041584c2d4100b5a0141d54811410704202e803402c00e458543c44c1c9800700494026443c80c4d207030501d41d8020309090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 935053336 1250 935052086 935052089
    0x12030702130605090a11190f020c1503061002030409020c03030103120c050d080a0e010f06090c080c07080708090619020d050f04090203040503040509130c0b0901020309010c022710 79
    0x1907400300182820000050700d01080580030010044c1c03260602240800468222107085c50700f500206840c000302c403030140070103402ca5400c00150003220140310540c20725031621100e602c40e5401e01455542c2c0ea0042054200c0c1c0c200356102148020b000c0860405038a20080c030060500100954481d0700d035140800244182d0080401080f040c00b460500048001601d05081d8066042842c0706664401d401e03030003011000e420b8000b45d030808491f104401f015512010548a040e041444000c003030320760a40e110031050343c010a0404040243c0004140e000001c0d00700e052042d03040301e20305003040c00003403142d400c000380307401001e100f03400d200c101103804002e9455041c015080046c140703040c1c450a04090b00079072081d0b45466070004005410000c091040301c0c05040002d0515455041000e2a011500382e101d0003282c649001c8040800d61008100540b501020140d004600d0808a01c2c01110000000107080342c01c004510788800e1444000414240c0828200f46000030038604509881c0c4100301c107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 935054586 1250 935053336 935053369
    0xc030b0f060a080d03050603012c060c040b0406050304030c060f0c1116060c050a2405010501050909061315080c011409150c120a080901140f0a0b030c12030702 70
    0x21000c0000d03003c045480ba8080e0726508000032995039000110780902010401c040340b641c069130003142032404004000704c110b1623410442d401d41c0c1d40c1c2044084c07240300d640100441d03060140001c01c40c8910130001540d20911a10300075600e10b0881d91a00305880301c04c03e00d40c00740d80e20b43d0310b040e00d2a5800b6000c0280307041e030380c030080c40702180188210700036042d14000d1000b00b02290300d03510184101005440e00c0d9551201d070300c1d000d11030101d0742401c24800800c81c4003201c501b0100000340b69071007502a01c400c0b0038003c00c240c109071205001c008100d07113140c0f04044015140c5c441214200181c90074040240171003c050003c4d400444001031107184401c0c00240039840c140036008094550b005416001d80c1c1c94000c1c142d840584002840c68114407415241003504001043c40300142d1001c0024000e2008000a00c8030300d611101e00c105030300b0b00319080b050001d07078a000954503207025042032005400c0581540c212051400219050001c0031004244542c00001d0481c1103007000d060003080d0101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 935055836 1250 935054586 935054599
    0x3090316231f0c030209060a0305061906140a0c020d060e1002160f051603030e010806030d1e09080f030703140a050403030507021c030f0305010f0e0402100c0c030b0f06 74
    0x500c0028640902d00b00c210716002e00d40e49800c1145224041e80c116156900001c0c0203030317151802040b0050251508070b0303540340a011000104480c00070340d1007100c1c05a0b42213407601c0c1d00301d000c54107020340f064004036144010411680400c0c4090303182c0088c0e4202c902c0c05044081400c2c500300a11a20f0b00c0ba00082155010b0300c104011014444500c107c80c095550042041c2003848540c2015403425040340054804030384400c5000040540002b4072807503429003a01d41d000d01e42c3d2801d04040d00c1d0441c05600901151407800503100e11161850f850ba00d0720400c1c280030815548500400b032401281200c1d00c9040d900c0080e1007018150807032000a2000c1d091a03415290442012000b41a07020b41d20006042c01408a0060b0441d0b0303c103400003072414280c0c40d00500c49c000504006040052690114020a181100200c1c0303030449a00c441c000d8410841d2940c4454655a00313011800301800131240c20090a8908880020450000140214007400c6403844a00b81072030b480c424428007816851240302c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 935057086 1250 935055836 935055853
    0xf021c061107170c070b030f01050a090207080702010324270c090909030509180f07080105030d081f08030a02070501090f061209020310090302010f0911060309031623 73
    0x840c02c15070b03034242c0810f11258a4032240441981450010a900541c4080c2004800c0000e582d40b0780482038100d820440349940d046940f00600c4042307100b482005848d03100d0400c2040d01650083d0850b00c8a81c0340c540004c00b04c0000300995880c400d80c20303040000d5807280c419000d142c0c841148201c02c808130100c0d00420980c250030320040c201400070304c070b0900a591280816002e06000d03400f40c0d0107021001c5c1c90505000c032100030810740980c00700d4600454003072034400700c4c90041c8240310060580350b018004080080c902581664a00c500403c0d40c0f510310f1034860301e0303000801d42090000050000f0300045803030b6604282c019080095a8201c281004034481040100c1204080603100b264040e0402d0a401c040120507040038181049000c2d4240c400c1000481b034800c203e5100001c003e000340d00800008150301140003d43e040e51101070040b415190f500031591500000954210320400100c3e4541100c07a505c10781c0940101d8411340e4043d144040507000c038072441da5130350130140300c05c0058032151 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 935058336 1250 935057086 935057093
    0x3060e0c19060f0f12021902060703050108061305011509331703070c0b030105040f02040b0f16120c0b0702012009040e1603020f18070503040f021c061107 68
    0x5090300380010420461603883d440301e40c01780c2c031007a0303150003000c1e0155903806d15881c03410211102000b0382e000504c81d000000310410b11034030605040e505200003910032510380b000c0c80e9410307a214003c140d601d95030328505100400c0aa90b20f1030010f1100760380105451119041e406501005a00c00e00240c1548d0a0022403280061821209a44043e0317640e502e080d40c2130501600d9070040b6400244003080d60000440d0252040c40514101c2384200e40034001c0452100c0688180d002c0c1e8800c038064140c007480003100c2a20800c01400000c2e48007904c419150750582c84030110140c90f10304050201d20501c00c4202480345035085180d000800c0d0000388188551550307450359030f040c40c01115070000d0011900c03c0190b51190864000d50342d0b0303003084544a994a54278400840f8891208a2040f14100410405420180104a01c0c40e105558210305551204c8080c1c2d0150300081007110b10000d807404080040e980d0111958800055002c0404004203e03d01413007103a42652034102034640c01e01484001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 935059586 1250 935058336 935058347
    0xb060108071e1805010e03100504081c06051809060403210e060117010506090a09060204050a031506080f0c121608031e120105091003060e0c1906 64
    0x41400c0c030303205060355a9540100c036140c404030042d20b03900d15065045005603070700034510442005150342d20700c0b0081d592801036484400d0130b0360168054201e03580c40b4000c5070890b444181c0c40b0717002c0d80c40e0529060205102c100003030110503c2420a654a14081c4154140301c13510000044011104d8582c40c14000c55195440a008000a0820903141010a0035060912103e00300c0240c840c8140481d00c002011f254450070240203e0006410701c1044107481401402510300440b00542180019103070404c02502070300e821345080c1c45564081000003040e031a109910002140100b4001c5080c1c40c8e144052010b90718140e02c144125030184c0141c002c0f2050108810300141b0040740c5100c0c0d4000d40b0559030703003044a803407030702c0410005660300043c81000210062490780c580c0310301095018045a200c0d1458000d400c810403010588038014409030802e18170280c2c100c0080c8205840e21956a80c8080949489082c1c6584035041140440d4050405014005520719040d1110a80e03d0500c1d200816 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 935060836 1250 935059586 935059591
    0x90216110904151a0307080714030109080a050f1c02040303080f10050f01020a06062c0112030309020409020d03030f0f0e0a0615081914030c120307030b0a0305150f040b 74
    0x110b56079414a02c4040c03850b0b2001d6610404d80038040c1c840d066030b01e058158480c202d0384114000e00e149600144041c2c501881969041903119003d1401c0c11191902121107070407030001046c424030304001d6002d8151a1141840c8123011415025a41300d04601e00145034400c0680140c00c1010a00c091011400c81440c200055804c20788801c0500808800100c0ca040084240944071510744200421174007a540380b04000c151a0b02c0340d01d07010545003401850840c3d803d124801030382d000019a070f00064070075000510094001800861140b407143c00090014006802c01c402003580d40d100000c0e0003805020300c241d501e1120b10300b04042d5a0504890b034031902d01ea40020038280d070b1440060219101e804184018281e00400c8803542c6045981409040d040f1800545130303076641e0701000d224400b00100710b8001c00d80c06409801e5291a402d041c4006030006891041819250740d0b02004540302c103101c0300002d40c003032001855100c00d000c00600030100080c0010030700c100745400f00b1001c02c084a0f00c1a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 935062086 1250 935060836 935060873
    0x1021504080904020403080c01061703040f03020f060c152d040f060e030c0627030901030c0504081f0501140d0b040303090210050a0801320406090216110904 69
    0x20342e10107a6000142c001d00c100e400c0200b4000d0045801c01607885c05500040541e17058140480c940c4005519043d501d005500c1401a4000d4502050005007030100c90052044005450a820910312118950034200911059500c1c0d144440c108410611315000300711041483d0700010400c014008040400f011300180003a201c088059401d00400c0f5556000301d00b112110002d17242c49056400d02551218401d0312040c0c000c00c05410007040d0203e14105d0407005231800401140f42c4a6100010740c003408865080c0400d01800b4440014000014800d6800619142001d9044460518280411643c1c1a049101701c41c2001c141c400a985510201055042d0070146070a01d41e138861404a001c3d19032008000d400400c203140c03c801454000029045000303c5403a00c6005a803203d20b074041d80000b4600503040c44610051504840c0b4030f402230b4a0070101d000e08045010364803800c88100ba41c0c004134006005a04040c181030030311000c091042e0412034110703082c0d031a600f41515500d001500302503240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 935063336 1250 935062086 935062103
    0x30f0203131d070809210c030a091403280201030f0c0c0605010e0601020309130b03030409022104030f0e040b060c070f09020901120b01120608010c0e031c08130f061a01021504 77
    0xa444440803502074a080f03440d007c0499550300c103824402083c2c0002803041c00e040300c1440307900c0889450040380410004104641e92100c050b01c000c03041800341c0383c1c45001ea05141d600c180f400e92084150044889000003a12281003454a5190507003c403407050380f040d4921110a014845940e90201c111003680c0c904075083c000c484070018250000780501c1c123500394903201c0098000b610700c0f0541c01804040c2c101c4250034588200c0542451011700b0125070040000e21852010b00301076000e01a09840d07900c024200044d5001c0c0c102c04950941c0c05402c0c00c000309d0740140390800231100c0c080d412401400348a08207505081d25100040c040b1403440801410f210f032141300e0b10419921501d1ba2000c0102d10b2807003804070940d07d000b92402810420800400100ca00001490908000908201c030030701c42201940d40705d5144808a48151303010f005800001600c489140104500d00380c245a030700d01076540001c9044081032000382100321861164103540280c02a03c20f0203041c501c54a81c01a002010f0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 935064586 1250 935063336 935063383
    0x1a060721110708010504140d080a021608182103070807031205041104050a06050f10270603050f060d0b09070504020f0408010c0912030f0203131d070809 67
    0x10790303070300341000c019030741920400000080410701500250300450040d1000d07040c02040c501c10340c1e11901030400d01e00114032001c020403c005501e81c010031291681c903103c40041c15165565a01603444048140c1e140d9042135503020302442c0104209101e1907600111040c4505110303245074803030041c2200689002e1011582d2428580100c15690003007510210400107881c0500d0709100100c460350b2440d011303c4c40c0100060070820248500b0007612002840c00c48046182010800c12a4401d050030f0204882c00c0c92407140304015880044040210b8210116590f00304031004044981c0100a0101c00f00003000744142074031407640c0703e146541c001c0080c654941c0c1c0d485400b417034030009520098002d480001d840a852010703002500c19100740320024400b5541c420800c4440341c500340505003a40784881c488500181c040c580c8500f5405c81c90060f40d0a00400394401c10085415a00030082c1010b90791400058520540480c0d07802000b605200c202410075101196540001c02950940e4400071140f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 935065836 1250 935064586 935064653
    0x120806061603080711060105030a080f040b1201170106050d032313031b03080a0c050a08070609300c030905030d0e1009122909011a0607 60
    0x121240c80541c80c0c2680d407624a5860000d006242c00ca50704000902001c1e070003140b900d40416a00d0490328004c004140b0a50a80c0740d0f00850350182d030000c6044842003100081100750329000c0d10540c40c9200501d40301d50726011303185259030500300080742d259141600c244025070f00d2103445103406400d031a200c47c0303010480c110440c0103c9002012654030401107120b4941019102810f02628841d001c10800f84402c0c5184682078910360100902140d0b0520180308001c0c811828400914002c0c000c80e20000c009480e0381c03060390f200007001c6d070700c00d40c40b2440301007406011aaa0598a15480190000b10544010f007450644407034000e401001300d4900040141441415038002800b4010b045c2d4100030903100c405040c8003030074014980030b4400d150751130001174083e0001c0c0c4110303804005e00104d01c100540c0c030f51070410400000c840542203640c0001d41d1140c040c1070064455220a00006052202a070002c4581003240f006103103d0748040080e0000200002501490501c24400e001e505841101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 935067086 1250 935065836 935065849
    0x30d03090618060c020f0c030715090e130b0c070b011a091f0305010f030302030a03020a050d0f090201030b19090203040317100f1508071d04020c011d0703120806 71
    0x400704011070305102c0003001401034551002c402424550200c46043c84a848056264410305054a81c5a008002d04003c580645d202c0c14507030100c24680301c00c0083d1202d005040004080d0761a07881c045401025900f040074901b9510781104501003414100062980c40d1506070405020740070703102c035440c0460b12200c48914207a41070f1400c010b01c001d8030b6200d001c8039803015001d20443d500000e0304002c00041c46000000300503003580e070164051840c2200072542034010354000070809040200402c8ac00c0c0f840d410a201f01d4100d04101d0307502182e24070341400010b060300c100355543e6103d1042904041c1041d0700d4414006c04903503007007a01584aa5943c03c0540d1220b07a000c400c00341c00240c14003084040c4c001c80800c0700c01d8415100400b80740d10385030144c080300040c2c8441824049240400883c256a01030313054840c05018250013071150511020100d020b0303800c041a1491603030744070b142100d121000c0120716501e050040c4010400c65207551135020441041031720038014080701c070001c40d1440d101c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 935068336 1250 935067086 935067101
    0x50f010b180307090609020d0b010801121b0308120a0c030606050417070b1201031509110d020d0510020a0801170a03050703180b04080613032f010c030203012102030d030906 76
    0x12420085c0c5503403211190003035400b041300343c0200703803900040c00c01940c002c00d05141611541403005414041541c0c4014503038690b0f4640100c1c2e80b204400020000b80c02d000101907200306654a800c82d0f060807003000f0290f51110400105250801c2d40c2800280d50000648049038040f0743c181000034161007a040c01c00b2050741045100c001c00180210401240c82c4401d8100c0b48601da412182c0b0342c5509060040781e40a507802080e03820304a05000403071501c0324100c0302c02400241800c1c0d0b0340003260717911803500d056505801209500030949128050700810214010004000815402d0307070507a08a80d240c0c104108006c040c0600030480c001814450050a4620f400c038609418840352250f4040d140354026110348941340c400c0c1400602142c185081c1a5900381e4180c9401203c00c422001c40c91404440720400340c8407905510300054030200074022500c01007550344005a4075410800c0c02040c0540f01014030880031083c074007540040e20000b0311301d001e1401c0380c40c000440c00444d10340b1a015003842c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 935069586 1250 935068336 935068349
    0xb220807080d0f090f030204050402121f150315050c0f0f03160329010c080711090603160504110922150605090f060714070801050f010b180307 63
    0x2000c0e40418070703000c0001c00b040415000c0e00c0c0d000003254803100840701c0c0f220501074201c41c03030f0882da003c10042c01c280c0c0200780c22510060100d200ca445140d0440d24141c80302200051510001c0c4030944509041d2007088490301c103042d2084161400c40c0ca580c0d414444840910102c1d59403240040c0c0d00046103002c1d100002d02e5407500c265988410f0ba0152001c1e002550180a6401410303190303020300b80a440351080c40071010000f05003030240818440c00324070020341154180521100d90708002040040280a03003840780948841200125040c841c000200034400350007503001c541c4074850902003200302c008451040358086050740040307060041e0350180c00315050700801002c0c50060030310305840d101c40700c4040c2a8420880041c3c080302d20707004008244503540c0450406c200000c00c50904602c01d140142000d000c4901c0c0007019a42c400b10481c0c01d5103401801d03080b0080500c01da40082c01000e0700402c00c019109500c3d410034134550200d100b00c03400c0e458401211281c0000c4d1352824050381008124 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 935070836 1250 935069586 935069593
    0x160f0b09010504120e0d0b040302070b041706070e030303150a0e01032006090a03020d0c0317030708070806010906080a0e0102030108010603051e210c1b0f03070b2208 73
    0x1086030405018010680b0102e62140d02015040d11130341c0f1540c3e9420703202800030a00c80e644983c030f44401d0182040a001a000c502400e032010a0f0202d8040c01071004000c011841e19a48040310b01d81400d04002501c1201080141401381e980360750300005883d0001112200c4440d00340b41031000840c0d103812035020415240707207140000305010300e5a8105000f020032148441004440900304015441048000d5a11031051041800035043ca007000340744040c45a0170300b000554880d161070b01e140b02031b0319001040c40307400020025660380c001e2215070040b84600380103600741440c20021380300d010140142c4c01041145000200e100300140c020401480a40000319941e50f11928035601901c0340340410343c1c1030f204d0040030140080c00b0701e60344807a01700143c01610340d46608441d01140004541d5071035560328002d20035415000010700200346644034584840c42c081d030740036051150020b52014103601c40c3d0080e030310402c41941c0c600202c5040359122101c00113001c110030101e07181143c158002c104a0320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 935071942 1106 935070836 935070841
    0x605040b0903070b1909090e03040320040f06060f0206090c0907020a061415061216020a210917030904110405041401091b05160f0b 58
    0x890040586105075600c00e1404490340240c610303441c41200c0880004c2905e60400380c6c06008140f4828148401408007880b0750b00d9008910000c1d101d00c0f002d05940c10b4003c2c40c85004400580c00900810202c0582c401c41c00c0200001e005990200b115551710500305800010264402e08120005080070300c1580180411004068880825845800082c800017640c0e4000c00c0400f50308901c0b842000e1604c40301041d4000d81007012240605c20801041c048201c0c01c040c03050303102c7c0c000c4881d40d030b25261070102245001008100075000d42d1817032288074200d4064004001400031070b540c2c0c0000550f12078400d10f0840741443c12041556001b0040d440341814550416440c215081e48502c1c1070039600c801140a8a00c0c20314501c146400c04001400070b01d0313442c41544d8505004000a00f814400260f02a09910500c01110b4114402c2d00c00841040b21004c210081076074405910342150 = true := by decide +kernel

theorem cover : BRFrame.Cov 934892086 935071942 := by
  have h0 := BRFrame.cov_init 934892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 934892086 ≤ n) (h2 : n < 935071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
