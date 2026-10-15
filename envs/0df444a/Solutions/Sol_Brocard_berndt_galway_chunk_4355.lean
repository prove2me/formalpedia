-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4355
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:21:14.072977+00:00
-- url     : https://prove2.me/submissions/a1d52ad3-9fce-4ae9-9932-2b90eece2672

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 783093525 ≤ n < 783273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 783094775 1250 783093525 783093533
    0xa29091e150301090f0305120a0c0c0602070f0c180b010e0d02060c03070b0f0a0b030d120c021f0501050906100207120201030204080618010c09081b12060709061407 72
    0x8000585000c1d40d001e00d025010480780c80a41141c070f551034200e80c82c8808604140b8000f002c0364004010381c0c22200020b40030582803e1140030350b6250020595030844804415141e0344001e60010320112441c0c410380040c8800244400d404000900a05c20039070f15808841600c082541c2d148802c580c1005010032428103981d4070941d00801880e0161131140c2c44100c018402403540c41101c0000d000b4011000c104110101c0e00c81c02c262107080c0c01601840a500b40400b45980d0701c0c1d02406850100d400d011403042480d480d90b019462345a01481140c50f80f0580041d00f1528603142a24100501d4452005100a0a01420340d9402a006445107420f0b5481c0150003900e4102c240654403070400680075200a6a02c60340689004d0b09606081d2003030384c240542070a1416041c0401d48e2000d50034071604025050007402c1c4d18080399000000b50040001c0f2045080003602c0c41c0b0341465000340b0040e50070340e81c00b104000c141d00c40c03699515403820090402c03c019041c5039196003040400301080102800013 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 783096025 1250 783094775 783094831
    0x1404051605090a0f020f0f0d06050f06070b0c040504021b15070f080603120c011509020f090d0203032503090506030103080405120f010509030a0e0a1401080a2909 71
    0x480e12000c4001002240084c0c58006071044104150711140013040c01c0c10003000c2c0c0b100402400095040400c04a6a100103000b25004200c440c0e543c840c0b01404002d002c11041241503503c807040c148010710307040e1141d0000b0220723000b000d103203d40408202504c0222000811008203040380b950525540c2d441c00660017840f00b60408150010400f00300f0114480382c404024000e41d40c2059110786444055a03442d01d0b0080019400e00c01c0320b06c081c1c042c000750000036031084500ba07440402400f49009013442c18001c400c4507030302080780c0603c001c010783d082d0951161020740c003004442a5964001c0428100241700d51641d13000540f10b040704000400c00a0003034030840d0300b15031040d00d03003c441c40c00301c681480c2000450f016114981d424501045188480440200300040d0a9211550706094800a0000b000c544e4040d01402c0841c8000300b6820b0b600400d0b01c542e01144554000c610140481d01e500304908902c1c04a4a020000e988101c1d078500d0841520f03076022020099050080c44c43c42940484 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 783097275 1250 783096025 783096031
    0xb0408030901120605030607111b2b08120906070f05070605130b0c090a120c0e18010e0c1318140102070506130611120721140405160509 60
    0x144400030f2041e10240700c10307410107401084020243c50851801c0030010b040780c181c6001c01d0810b405210001400c41651083c90001c48502811005a0100190b40d0450020b0800303664440c04c0540368010000948010007070800240b0303054200b286d410282c13011740c64448043d105601340080b03103008140703c66024044e070f041e90b80c0100c004502c0780c9460030a80f150300c40c500d10203000706007402d080040041040000309147c01050354142d8240d5a140c19003642c002c210300f0b00410030316907a0300400269906010041c0c110000e0f00c003c2c800034a200c07418500b1181400c58000d02508403403405082c1c0c1c903100343e0540c41e0400c080710502050b110b1190907110819039903001040744c1c45100903814901c400354159518194044110354031400c017021400c00d4201a118112130a80c1030001c0301c000d54440c07506580450407a8005074100d0f484000d41940c400307000100070000310501c550880c0c0306e60004d0180c0031420a00c1880399110303050074241642000311000003130705a0720740018104903580b83c2c0307100c50b94 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 783098525 1250 783097275 783097277
    0x9030a0e10030e0604030903030e0a05150c03042601050601090311010c030e040623010311030117010906050c0310080c0a030b060604080d0f020d0219030e0102070503010c0314010b0408030901 84
    0x70001c20103038203400600a800c8910010b104d43d4040104240d0000305000a0340d000741c0741c0100c070505583c100551000c1c1401800c3c4c1000c0d00d00380d6410040c0d00c440c09040d20481580640703091544849032001c40d0404c00700c0e007511507103c89081d80d902010030306c03030603400050070711744050b03814115203442c107140c04405003c0c1d0400c03079981040018148900c1c1c654100b11002402031200700c0c3d071111002003074407800f1081c0542004c110804000c660107031150f00702d120004214917056a107000d075118558800e42c00c4140865482c0e00d00301c00000e09078400d0f00e1145400582554480c01d01c0818140c011460b0340050005138030882103036806960b08042c0d4012258000d01030203841d40c6280100e95240142c0d401142e0b00d11851110900558100c50038505030201c2e40c0c2241c0c006005880201e98810900460b2100d202d1020b0f208404248907540d100c52000040c0101e400256444c00030908640c40c0da8503480010355600b440038000700501604c203004006800c0481e0525080c4018141c692003441d04c554 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 783099775 1250 783098525 783098539
    0xd050a03080a20130b210a020c0601030f08160c092d18020901030317070206070918020c1501061101050603060705130f0b2104050715110304180509030a0e 68
    0x80c11502c2148000c0300640b40038540f19440700304040c008171b0000d2418800d01d41c6200c802000410850f0719100b5610100030003002030241e82d01c1c5403110030701059a800103855440b41007107660000415002407049092142c0c04001d801480d00c0c0c0c048084442c0310007610420050094500c2841c040c030081008040d4140600091000e02038100d414508108500203401c00d180400020a06070070106021131032000800d22a43c03981c1c0c140c0201c0e290b640c00c84046001c602409814804031a9803021070031032100d0500c0052501500340741441c0f0b4410b152602d001c000c90740b00c0041c00307070943c00302002000300c2480300248400d080c40c100081d101c1e10020240d40800801050b40d440d0071542d00c113041c0042c40300c140004085922a604480759a00035901030441403204403040e00050900728099128642180c05002c01a052140c03007004000e10201000070000484481012070409000400041880d1180c81e040b00c1401403e00060350030080180f1102d800c2400507a400680000c0c0710344258404681e08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 783101025 1250 783099775 783099787
    0x20901030b04090515010b0c030a080403110a050d021c0e06070f0c0306050609011202090610180b03100603050124021203010e0603011b050706020c010b0d050a03080a20 74
    0x100d00030701d407003040540d1290600c018030040c0000491524a28400c490b81070402c0e84e202e035580711541c0308401002449500402010030040d00c10081186c005101c2d01e040103405070090b80f05850664410020340b0a9002001c40e020240d8041010b2842500707045103202982c03890603006030030600c1e03164034640118800030740041008561641c90a800b03a01c01200c188440c0c680c2031110091008481840c044c1e0324031400400c200190000c0f40955541c000e00100a03503840710f060211094035008801d040c4040300c02a42d82c0f0440c03e441440250180034580d0340c507450200341200d520400c03a8408801e051070440144180da03400340d000d1107000d00002410348800c4c10000b0482c41c00450400c0c80340c5035a004800440c044815080460190908071300138003040c0b61074448010801c80300c00c1c070b690104004020000c001400d0b50041c12800d2540400081e0002380d8102050104c64071b40070440d0316420403402035040640129141d45c0003005540e08200d0b4400c0c1b04c07102586001d6894141901110100305 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 783102275 1250 783101025 783101027
    0x100e0712020f10020303010e06031504260f0d05063304090c03020301173904050103050c01020d0305011d092104140118051c21110d0f03020901 63
    0x20091a004003d8404000c9071140349000303441380c0007030003140b115003400c0001c070308180f030300140801e00030301480360046654803955601400c112045882c410703048000074a00402032808000b0308428106141d109640d00b1440d40c40c4d404444d00100114495070203201e00a6444148181800e204051500c80a14001c1c0720240c2801c0b5019a1b400707600c88a0400e920240502d5158029504030349004540c80b0b120003510b1022511040038450303c114403500c00311005001c80204091880c800482c40440c1740170901c00c2d0101d0f040d20002d0700140e684d64041c05a106595070304029000c040d00304e620b820446035040660405281481c46140c0b440b41c1e5005c07000ca01004010300000403041801140405405886078440c0c11640052140341566401c46082000a5002d5803504400001d1100d00c048003605181c00c02550740c0511030442490307403051900c000011440c00d4240e0008911480c200c0076050f180070f0050501554180445580c0c110003403801c103058110304a090b0001d0f0b1030401603213400711000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 783103525 1250 783102275 783102289
    0x301111204021c05030d0606090b0a2a0c081b06160b040c0806040b0f0901060803030a1a0603010909060f0608101a0a0609180522030314040b0603100e071202 69
    0x18000c1c01e11701002500f0f01032a503459104c030f01140c9440d100d01d44081da507100030021030300407850000c021038000400d0580c0003041d15845103101d5000703a65200c4102071501c810382d0b840260381286030294403082e00aa4405408007070500c0c0d0403000c9604c1c07031401d0f00f0074515000500600303c0041109202070f0228007045503030004240607140b034900722001032809003803a034030040c801c1c1d03695104088000080b50350a081070060340140c59000c00194903584516180d00000c0c210300c2c3c0007403000d001c030318081112541e0344402140201071070100420300d0001c90604000300c0314030002c02e0224915042d400c00520102040070141e003160724500190000d0b1000680031a80d40c146805a40000b030440c01081c1650000c2190040c2c8039440400040c042d1b14403c0b00d0100c0710b094038840f0b2108020a003000c3c60021656407003000512070b180115070b1b80505042c80310700401c1524100c0381040c0b5282000520b0808010110014440d12402d100c080700a5480c0c3c1d07290340b40c0f40200e619402e600a0b10100b9511001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 783104775 1250 783103525 783103579
    0xc030305070912051c0216050f040608010606210915050618010b120f040c0e090f0706031d07050105040b0d0b030f012f12151002030306030111120402 66
    0x82c40c10210f400c503103019034440c040b0b0001c1c41301d19a01c4458902c00f4902c000340b484801d2000704565008182040108804c66000140031030380b0548940001c160003400303024040003031010f40c5590140b040e1460341d2340f2222401400004e0624500303503c18000c174140464144c080f19240d0400544d9840e42c0000c0348040c40481031182100401c00300015080e001c60004206410200e400702400b91240141464400340c1a5009070210001c0c2c0c00500010308a8520305421500400c1121010070084180609040307040d800307103010955600e240121000c0c00d0400c00207214108003c0d115890419001034018042e5014685404c0404910a034040b031865114000601000b004c031032207c260080094003a045143c1e411842b01c04420300001c2425203a4142c40b041c00a043c0140d050819020019141e0bc10050a89a1211110100c400641c6900141c002140c070301c1d82c082c598070f151000c02e05081d1032141904040f001405c024502d4045001c2c0b50050b002681101d0000c5013040c0c156107808100d204c0b0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 783106025 1250 783104775 783104789
    0xb2a0d170712020d0b090709060306091b08060315040f0b1f09270c05180712052d090618030f07030903150605031014061225140f010c0303050709 64
    0x1401f441040c1c3c0d04409404c0c03c580450b5402d01545899002d21800d036011280500e10740c99044d01d140c24194007603056190b200b038000d07045440c0c2c40c00c0d06455443c0450292010751703002100b201c021003070003000c4d0081a480300d03030a861001c00b00f404e038540d00c00083c014400d18004941d119411000103800e202008501c0080582c41113040a481c00d09071000c0c0d680c0c1c450144a0920704407003001a0030b0407807210388a074065460b04001c0d0b106d0359056101601000f0100c40d28000c441c0700003ca005000d526442c074002e6072402d00070320741c903000c036642d403410346c018182d644620401042c800c0c074800000300711142c40074289401c83e2101d0003403400f640c4ca550303176400007040003c030051100780c018110350080b011510218100c9003c003980410000847e03900b82e0502c03003526100070004605003448604203c0b00800d0304100c0780455003032210011611241c0d00301d03613540b8008550810070004000d40728086004110740c0c2500300f50681c0006068040c080307100074145625180000c00c0315004082ca07800074020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 783107275 1250 783106025 783106039
    0x10c0b160306080d020c0301061a0f0304081e1b010605030a23010618060504050112021c0506070e010e060301050a031218060519030e06010b2a0d170712020d0b 70
    0xb013a0040d40b03035100e1400c003900962811300005008030f20003449440c124501441a46010030048005502d03600003002076500c8441040000310341403824000c2441c08100b003080c180c0ba215802c1c2d050711000001d900107461603040400520103681c4c00704501a444c0c0e03001c00780700d66000319022180550a000a0034507260352801a000524101405960f01402c0320b84000700440c0e0f4881041008480080c0544c01c00d011660040d02c0042c2051400e07403a000004901c184810030a0740c2d01c46140900481d00c84001420101039004c035135801c40b41c6164140402c030784150440d1306003004141c000c8210702c0702410b101c030804800a046400b03031071103034801410385100001107601d950018110754000200e0003441d0f210800900c107160310911070b00503001c0300c900103000c0030f901c0c041104146070040e01c00348134128800300c0001c0c2110f00c02007240700c3c420b00d010f01510121426100180c2654900495950040f00c50390030007034800d0340f18520190a616070040181c4441501c41440020300031543e1403900300075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 783108525 1250 783107275 783107293
    0x10605150c0a06060f08060a020c0a060b120d031a03011e05060111101a120d050c010204090e010608010c08100e0414101d01020a080112031b0609060b010c0b16030608 73
    0x40745c08110030079075410804881b981d0f2142e4240038124030445000c07a1058000c41081000141180c000d10fa80c07810040150003e42c41c3e81400c1c1341089a866800c1c404240e0380c81c54100401300300c00d410030803c0d108400800048070b9511800f01c40b51054121460b035150361f040011f81d541e005038442d00d00070340c00000310b0301040007803440c0b18020200c110b40025404001c1d612414546014020080d10301a0070001d001504102182038526800540310003100395024000415240c15503c0303a00388485c080400429070b1450401c00d1421220070040707074010404200204061094040f41420460383e10300c1200303e6a90707443c2032041d040c2071191031300c0315980910500b0796524074007074114000e0864824140210005241502401c03446607810403c0031031051001080224164503032002000e000e030401c00d03d0910070903c0d0b10300c10342c0e030302d001142d12559a1038010244050351091801404081c00c2c491500d16882d111004c498900500440000d09404032014400d442a0030110013001c42c0411034031070035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 783109775 1250 783108525 783108539
    0x6060f03090609011811010810080d171f030f02130207052109100302031f0b030901060920030601020a15060302010e04060308031803130b0403020111010605150c0a0606 74
    0x69040e91101d001d0340c00c00c450b04885c1c08407504884a20340e07024206003400300d0103400541d0003480040400034500040ca000145c03040d024001d02003915150340d0307070288481d140800800e000300060310418400030701c0d03410708103107200c0f900e00c1c0707800d4036003080204140d09880c0c40015100a0726012000c0040c0c004241c5008024002503880714082c0c00903400305100704440d1408180b8003034040d0f403c0d030040c881000310444901941c001c540001801000060100100030b07242e52482c10766203d5204030100004121041c202031003100c0c00f80100c13050a001004040d40c0c0002c490400402283ca100000808540181e00821010107480e9004008000340311340783c45e8032001030050b4072040c2c0c04202e010b00c10300d02c0f62406104800c10f981e44644003a0940d1103112203000c8082d03051400e0961440204580424500c02109031402001828400c9984504600c00100340700c80302c20301a21541c0c11b01200388400ea40c0c8901d0414180311500c0c80316214040c8034001803421030403c0000e0320040ca0248085624 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 783111025 1250 783109775 783109783
    0xc0f061e050c1312062c0c0916031a10180b03090a020f06090424060507081b03040807080304060e01110a021509041a0907170f07030212090c0a080f07030b06060f0309 73
    0x1050000140d1f4a410350700300c00d02402000444440d4604c0c211941e60900785400b036440b0040204d11840319504030000d00c0040f6500c444152401808902e007815421403e8190641d01400390004810702e90941c1052400c980c0d40d2030340100024490584e24044507815100c600c107807070201800070000e100346081680000020111071b41401344d01890788202003406401981102c50480d8450503480c0b400181404140c00304070500011482c90204100000b003c000801a46015101f603e0207196150301c2c100740030709021040c0d0501414040094010f560348140414041d0701c00d9016241e48080820071250756040b0f01c101c00ca01a0b019140401d9158105032803151b2442c0a14155051005a00d41110070703916489040040039600c0c0b103d00004102109185070a6081003641c10054240090305181e8003034408225103030b651582c07141c5840440d0780360602c0480010050400904000301401e08034a803120403c1c00003510500d074480201c2c0158035920101e401628a1010840d1203003490840380b43c40d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 783112275 1250 783111025 783111101
    0x1260a0f031202040605180f060c070e1b0a0e01110a03090509070c0f1502070b090a0b070503100905130206120109050c090f010c0f061e050c131206 65
    0x78001d140800c2c820840740c42290f06035000da032991030512076034100461100d90103101e03564001020a615113403079100d12001d003002c02031510260849905100d1860a15040205004950800038207640d54031010081180c404c0600c03460190b2064882c1001650f10908028500b8110301c00c1d00030139010300d60300410700c0060701d00864880f6080e40303440900301e0b41c05417803510181000a00c401520300040704c0c000a980c10f40103080c009820014152103698103503801311803d68141c0c0040c0c0380c0301700f0040800c0c0e649a01560342d0a1a13821403c001c054048554078a016020500350344d103001c0b56001f01c1003c107039410380c0d50040c032080d61815000146a4545401c0c41000c0c140307400d000100c0c960010080540b81d00003c06802c00286000c0700004640c13440482406a6500140ea0000e02c080740d424041c145214031045140440c0413520298042184c40062411b20008414020f13242d8810601201d241221501100a001c05501e410a030000b0304586403649462500d02c680c40416044000d02401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 783113525 1250 783112275 783112277
    0x180603070915021f02091005070f1b060206060d05030414060d0f1b02011b1d030a0602031605120f0711070e1905040c0b0c070f0308031501020d0801260a0f03 69
    0x100340d01204c01000300b80d026062107141c1c00002a40c140850905c41c030098245540203411890b060b0348030740c4a0940e0782c0b00502c0e10403400c9135000300c1407210075010840d42da0040005d40c0c8502d0107803d1500d841e03440f40114000c040c501c2c28403460825807903031280203844a5240c88001088401440b104850041c071401417149806d0500002c20381c0800d00610030303045014520100c1c0344a06e02a0001121080100c04aa03d00503140f40d10005032501c081241171909489030a00580e80c0c10240f2808040208815070b000c04c010f01000800c401116031034050380c0013000c420b510401a207849105440a0220100301201c0f88144000060301c4445500302a0080c4200c02d2002c41c1a402640301800b0760704100c801802006200004000c200c62100080c85918041d005881c4a180c8401142681107d207070b2050380c6091002c0180003000d0711a00071101c40c01d409000a10100198034406004420f0504c03464101c141c1c0f0101d605440e03408aa0342120002010b019156011071610f005882c117983e04100354 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 783114775 1250 783113525 783113563
    0x50a0c02060d09170c1606080a0f0e0109030206064009050d02070609090212130204060801020c25030b0a0b0303040905090307033e0a05150f0a0218060307091502 71
    0x100061b000411300e882030303400c1569050303d20307a2504000340c06040718102030150140d8610384e4240000c000c0c42000ca1162007079000d05000e0600200300300700e104460000e440600c00f1091003414513030f180c50915442a03402802180d51a0075100100c00600309048090002e00411003d1808140d0202d068000d49038140c8943c4401070302e58a05604a01491800301221021a0081122030071101c0500c185c40d0320040010481540301d00d18242a41c120078050605940001c094111411440c0b0f5070740044244210904440e80c55526512400c2c030000e4140a1107aa032203030ba8003075a0302e00340100c1e0040d102d891410300050078581001d07540ca034003038076090340010000c5480000d440e40b4002d60080c0d0303090958000010764640f085022900700401030001c42446100b030900d000480034410803848526440303140d105413504102c9102441c00003041440514030400079102c8241d00e003c0000300c04401030303078070b1922030380c0d100d42c10b0790702000d1074104c2000c18543d1304020070701d29400920406489180032501d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 783116025 1250 783114775 783114793
    0x80307031404030903140f16060e040b01081f090c09180b0f060a0c051b03070f0308030106030b041401032004050f010b0c070b0a02010b0a06050a0c02060d09170c 71
    0x103041c03070942510700800084049a00b00042082204403440540300401920301001103203945514200c1c41e215258408407000e1010000d080e0001e14812881400303841c148a01c82c0d20000081c8212801000141000315500c180d0115030381c1c5241a13009040d200404115000021002500d03100c0907100b0200c501e07030f000e40d2000041215014503020b001e0090070340786003003540300108140c0c3c1d00500d00640030010702c00d02140220340d0070031001e6085c2580030640f8080840440626043c062203800401014202480810003c0d8904040360704550191900207080b00410b80024094035040814a034441000c0001106020b85c1002170702031140c1c89072801400c0c180d50030601c010b4907011a003e29550754104010400004c404005040c9900c032101039580f1242c440c903110006c0c0e0010015000107130364440e44114141007000644000c1d0090707041617030408071203007001030408400c414001d0103004082404404140144c0000b102594811295440030310104006a516004011065401c0c8100b01c45 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 783117275 1250 783116025 783116051
    0x605040c0b09030c011d0306040c08120301060f031a130c030501140321041508040204060f081906020405040f20070b2d0f15060a1209020d0f08030703 66
    0x11102d0111000c0c01800e00e41e0603500054a80d40a00f4002c52050104514540001d80d0103201141c800c51040024503105800c0000f51440c01c0c5036120310703015180c0100300600105401c0390011007a0715003481c001c1900e87c0a01034607511101c900c00c4040e00b01c0034810b00c00c40d180302e0035080010b03074200c1940c04221680c3e803049511680309840c8002c41d0160010102101da003e106080c01841d0402200550b18080e81c03074100c1108921044401c0d000941d10b0340038002140741c280109001001c88054408204d07042c00a500d4a41642c00c0d4000301c00c0000d10268810800303507406442c020b0400400800c8040c80d400c00001c0900b907020040b40c040700d40035101c0a031020f01c0c801a2082d01e90841c80703d0702183d030380c500d8030305841c00000481040c0c0400000740701010001d072542d10384500c2000c4c40500041c2805c111254506414011052103500240300080c0b1241c0c0c0405106100440002c0c0410049103500105150f01901d41c00900b66202481c00e80d400c2c8110b2000640c003490081e41e08010b03000f5a0f0300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 783118525 1250 783117275 783117277
    0x30201020307030e01150302010503040f051c030b01030603020a0b030403090b13050a050405010303020312130b130b060a06081906090207061407020a170d0e0f010e0c1504150207030f0605040c0b 85
    0x141b005c649101d2007060000d940301d5005140e001e4840c0b200101d041c0c801e62601440d00329180705ca020a0703441c40c034101d241c9541c503010b4010260000e080501c032403401c590000740045454094410301c42030102c0000d043c58414007910300141900882690b84500ca007a0280004a080c043c40e409a1284134001a050070700c2e11400b412079030194080c50920740851519410002c010300f40040c02520f002c4181c01240004146900501e071034015045100a145030001d11108020702d007920900c88d50307004228007900b0070300c100d51003501d080c0001040c070034059040c401440582c020703011a80c404540c1e8030410241c0e6102d022402c1d0a11001c040f59960401c003203946908204004015010309110424000c0701c100180426080140022450554103180709151908480c01000035a445804405c450401400481800310055032000000b01880d08c1088a0380f14a11508000c01c5405456880072407091003144007440d403114492140440c54240311b80a000c06480903600c10300800400586040361030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 783119775 1250 783118525 783118541
    0x90a17071a04060c0c03120807030f1505040e030c01090b062103040b091804030305160507110907020109080f0a091202030d0c020303090a0f08010b0f06250f030201020307030e01 78
    0x440892401d41005400c4400c044804c00c105c0301a00d00c4080403001441c010000d41c02c0ea1025030f1150654600404010161074042c000480e62a10700360094008640a10120341940c200f6500402e00b50114408145035201f074429900c403651801c0340c02c204210403096046d01070b40b0109c13a240c501c0d007c20045c1c0780841c440958810090340c4100020030245280340050700c8003080003010710210440da402c400c100024210303030450010b0b41e15810001030a01d081400c5522003914a0180e0922550317030f5078501469a81120302d8800c00c0228001100c49100350080f144140d8443d00442c2c9510030700340c4202090f0045c1c01007034041a4030150225106030320b0101c1d030307840640040050090f00699401a1004400a40140c0c5c00d40000c100207403060b15119808401454007451101c0150302e41002e4500310344480100d203104000c0c0010980e5182c2d100c50a4500c0c0f6084116042e80001c80d506406042c42e907202c0b401007403189144581d0b1b06058042d40514031403181c60b14184040d800e030710b1010703013220b02030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 783121025 1250 783119775 783119819
    0x6080c0109060f1b1401090312060b0a1407050706050a09080d090306090606050a080c04060909020d0b070e0d0b06091f1401091d1e160c020105090a1707 67
    0x54041c503c0041c8a1081c2c40c0d8004009414540400b05075150307010403055015100301c0903912031140d4810141d00440b0b0121120184030108800750a00800c00386500c1100500020040c80100c0c4072040743c116002c82e006a0303880b40481c6c40c0e5940d54407018100fa004501c444010030119132001821190108200720340c3d07581c5954403074140e82907a681c04002c200c8240241c40e2255035000100c0d0704e803141c8400304040c008000003030440c2d40c3e4070010441524540e800c0450711505080e01c0500603250900b8410710366a0181d155011503441c404129510349001c2503255000c1c00c400c0c40d0030140542c0e224081d01810701a00c40315800d07603400c40352000220f40300000c2c001d400a00d0300d00700b05600702982d204c000503005250840c207256440c45904030740f510070114085100916004e202940303804848518a440184204501603d403a4181c07080c5443c0203e420811b000c0c60280002c1160312030740885a070034500130b04195050341c907145c40720042694144000624444d08902080c1080b11910481c40d003880 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 783122275 1250 783121025 783121037
    0x12111e0f090711060c030108012003062704030e130207031d010e0d08030108070e010305070b1c050f010503010b01020f030706090f0f2d080d0911030d0306080c010906 73
    0xe40c1081c44210301005111604025180f0041414110180565030042080e10601504d03541403a44150071641c0d015100f0180c5000003c01d00005e6292405a03170b0b120104581c1441e0840c1454002e920111b41400e0804034800e0302400c0104254010405ccd840c201000d4035a0b858941a002041b4100d108074000a40840c2c1a140d00128940d040e02250048100600d01026185080c0e0f0110306e090314003120456003440080014080c826007009a40c00800448a0425080d45141c43c0d07a9101c2d00a4020041c84210026164400c0d10001e00440a0340c282e250040042d80742c0f422a10000070000e010300c500c65402c21241c07002c20b41c800100018505900c10180d440c0034103981d107100c020119440111400b0140000c40380109205000f0200e2050003003041c1030440100205990840c146000001006074450b2050700101e20080300f07483c03854028601c0001d4128150404850b210701a162a660520441c44100d442603410f400071002c496600e4100c4034030801c244015202007034903005803000241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 783123525 1250 783122275 783122299
    0xd050403021b031902041e0b041a01080a050c130303020309011e14031003120207080d090308031801060504021815090f09130804030b0411041e0c0912111e 68
    0x10390340c131002c0c5105100400000348010710b00a0440245180ca80501c603003540c13000002c00501f4a40610702207802c8441c00c0510701c82c0f103000043c0190703e0242600b40c1c0c80d80c0c1c800014100014800172200d00e0000c00001c102c5803544c9103030081d582d42c05000101c1c0001c101c0041010b60750032403204540340412030303210341d50341861140450380e80b50001010a12460078010000010ac0da004030f1000303c00e512a805400d01508219503140ba21015140200420100403000c002140750001503039000080c045554801c0c02d1611001e901406d1a50000ba610520010780303010070041815428110b13600a82e410013008180c0f94ad501850f0040020881d0030080b140c3e00c2d01003501e411003541c0c0e4414040c2c0011440d40700f2580f00ca2265802581086441092910030721041c03184240e020211108104c070140101084610310b68005100040e00800c07998440b100601030b24014840d90014280c403001c0240804114100b002d0059520500280140d036040000f61481da658940c4003001c11002e004045441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 783124775 1250 783123525 783123553
    0x92502190c051e0f13140c04030b1602030702040b040b031c030b0103060302130c121523010c23031c1b020c240d06150c0203070e040204110d050403021b03 68
    0xf5259052130062140d0b03500c01340c04100c601b044080e00604a5030382e103545450451a1541140f0400f0b0300d0307003024907d03211036907907010b5002040342c5100d40d042d6004a124040780000c1030103880c00d036511680c18021b00f01852912440c822174a01c0e0161a81e9042c80303490b94100c01541103481600019400040b09a81604058026004600800107078a400c49481801c036515408880c0c0c9803902c0c402900340e00c81c0402025103031829524158116840340c071001004070740082c14510800ca130080c440441c2e8140304908500f101a0000100003200640340e5a11000c2003c469000102c0b07860f07602e4a1030121310f001c0400421400000040841e001882c802c0010000c100b519800090704015184040c540380c6400380b005e0010b0150208024004252281044103000c20513852000d0a410010ba8408520141e54002008030440d0304042021142d5203c90011802074400d0030600c4445020006108800640030f501041c80303640203500303440c003650782c8411002c4a440002c000d154142e000d00804482e003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 783126025 1250 783124775 783124789
    0x2a0906060e0628030e1204270f1a1e03070e0a06030212061603150e041502040305060405160e010603020a0e040615030b092502190c051e0f 61
    0x8440b9255400701c40031201d403aa00d14500410120000003a12801d6405003424100401404521202c2c24207060600b4505603029024208c2c1c111014000d003140608418a482e521111741241c020800780300b42c46440c4c841d640242400c41c003880c080c4050340d2800443d04001910042030b84001009004041d00e0100c1913514048094402d5030205d50390781000005a070f5183c3c00303010b007030402405001a441c010f03112a0358a410075000c9000e0504143e60417194500342c0008130b041c0c8a1541c40d54100b42c0320f50911050341c9000b40091b034007141c800a400300600c903000414920a5109104903520b04403080c1501c0103640c0c0e144980044030359004014030686010307401a1140000a1800d0500450070000240580308a50700900300101840001c0d2200b0344c0c1401140c444480c16240b4501034100441c4a0114121200c40d0030001e651480f07040c42410310901a00c0305000c04605d108060b0350342414040c880c007084e4490903109039596004c0c0708960007500001d03101c40300c00500c0d18130f05039614018000c80b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 783127275 1250 783126025 783126037
    0x170601050607120f020c0a060c03030509061b1c0213230109120503130308040f050316060c08070c03030e092d0a14010f060212161b032a0906060e06 65
    0x5600030305142071055215503100f02c0042c401541c0f81c1270981701da402c01504036800600714441a410001c100700314003500200c0c90180c40041e58149559500c1d10210200b10b5280c50101c0042c1400002c03504001da20100441050f540c00600080c0d1603100400d520a00e16858000c040c041542e40204001340d000d01c401036001a070003002620320b40300117081c40d00d160760070a8104a840c0310f00801c0030301c12940c111403140054407050300100415005012680d008104902c40d500800c811000008200200c0c1c000fa2500c2d00d80c0300d4050b1040e04c0d01c03454081c0c001500c158200e40600010400182c0c1221614912b114002c819840b160410f41c2c0001002c01c4014000c058580745922210001c03d20307a03c40c007030036009000c485070341c841d4607041030700082c204444001d080100c04014030050051810f05140010340719440140c02c00d201c407201ca580022040c0036031019140000b00d2001118280400e4080d40800000042103400c5075114100385c411900b05005500004040d0b0210724028107080d00141b107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 783128525 1250 783127275 783127277
    0x8040609300c08030d052224200a021002070b0f2d01030c120b07030207020a0504180201030b03030f0f071b061101060e070509010522170601050607120f 67
    0x8078a0f00c0e0b8840a04d581c0c001300010071845d42d6001000a203a010700010301d1890301d11581491008540d449104100728503039681194810701c603008101d2100c240d8004221040200c040d0014000411200c0350550807025128025010704003080c1d641041074421100d2542d44003100030819110006d0494000d01c00822004640c186582512002c10001017585046502a20080e0f110b40c1980748c2190a12030560140211003141004a03000401c02000158881051300d030050f1031f040b8900000320035182651119401c54906071440380c403070405a50b9040598006e0701e051185800c0003081c10303030300d10500c1e8810304560b0080c8a0268503200d004002c00c0758901909601c0084413410740f2102540c9160f52120b000305040b900c01090b011020300911004210504010001e8501420b028000340700303410340755042200004100320815200f044a82c3c01000003400390740100e48070a00d00790a1203605c0380c65403540c450344c400014035140040031a080305a11007134142d00c807001342105a40c824032103070001c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 783129775 1250 783128525 783128543
    0x30010204061d1318020a090b010f0f022a03430f081c0906300507050d0e160b031e0901052202010212030c040b03040804060930 56
    0x201240f41c1a000344d01807980d0700c851200038005207104001130300c403a503405446002d050505e01070540e03130004642403c0040d541840c0c40007e00040d402c034240303c0c1d1140c8004600000c03614000d400c21505c80401c036002002d03003c69880103000c440034180400d105001e000107503004c0d40e03403094400c14041f41c00b0b41c0d0b2440c084501200d94417217400e41503840a98200c15215031012100c0c5203045089110741d00c9441c0760341000d4200500704003004040341102000301d11407502d044003080c144100e10443c5091051106004c00003030402c1c0c140141594000c2071389401c0103003171060340c070100f42e404209104502c00c1c5034860104d1900d400400c58141d00010480311101c800c882408050358030300742d02039200c4d0001030000140f6181072012121080483c01410755800f005200e8000141d0300010301101002c0a181c5003600c039550b644e91488244556044560350041c0482440100003448000d001134803040d07290030100d40e88410003c880c103c1111819090550000d9103800d0403d1410311070000d0901414002e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 783131025 1250 783129775 783129799
    0x70f0b37020a09030804120506011712030c0d021303030f02030a08130302160f240f18050a0e042a060311040302100e0f0102071202090901060530010204061d 69
    0x110a9401031350018042144031f94807401088010700a003805000001c95203400000d100040503500e0b036200552044d9444000045500000c0079130a4942d11200a081035507034040750600401d07480c020b1f201c11400300c0c030a601090100d80c00170099448180e52507460071403a0b65002038485402c0c044403800d4041d4003d5050211250020200c408003900403003084a5a00b898100100c402c04038880d000a4610f40c400c02a10306258843c0180d041c0d0803203454156103080903441d00c080103809a51026030300c41c642030000910080f03038080c81803145014044e0041c44180720701d09884d4082041d924240408014501441168042e9010000c1c51464603451401c00340c0320f50103d5401d80300308100e4030104208071002011440d00d02500124440c1c28409001d25920b0591240c0f14211400c500922511408000900c00c210075881032006200060031510b400b11810040f80204000000881c06014584e9051000c69014021941104c42c00c0d0b481e0300510307040d810750740112092049a44e07408140345142d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 783132275 1250 783131025 783131033
    0x201050603370b01060216032a08010e010902040e1b010c08040e070305090c0f31020f0a080901060806060105071104060311010f140d02030c070f0b37020a0903 70
    0x122052041c458100300d03505504017100a45005803c0c80820220b1540e21818400290040c00744030304080805c410070540d420190550213040d04d0360300400e000d0761130602d01c0003240205410801c48a03000341c1d820040c2103110800f4949443c0c40c400c0c03102c800381c12a145207030194881e00c413115030680240c03281d40c1000d80f44d100c0b003101070805445007400a920b920a0008144081c0061341d2150340440e80407100048210100f407034100c008951036000c0b681d546c0300c031164042400c445981121400710031961448101d180d40c005400200d540400104100300069951105100311416280d8407001030035a5030b2482d0045a082d84060002c49064940e130ba25500662a0fa02a00e8040e51044580308070182807100010b1500a440c003031542085100452640020f462800300c51a98290250240e138a035103c05000225200788200201004074440c001c4080c000d1048420340502c14400115003c184075514500d0710a200c1c0402d1030301d480c081d4071008005000703030b401401c501ea214140130f29002d42c0d80d11 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 783133525 1250 783132275 783132373
    0xa110a0b130b07111203060a03061103010608180a08030406090b1923011202270a320709120f0b011e03060b06370201050603 55
    0x30006030288111200204220400050581c441c030031346800f580d0440301d40ca1803a540c04d440d034600a044180040810907613241c00d1400740245410190a1003140345544900001d41d2091296000041451b0080342c09040800c070411680e5500360010308242c01c8a4a6040c0d440d403010380100d0300c00b41e60b01c01582c0022100414584140010b400d21002e030039940b0341a809541c01d02c0c50002e2000301d00703200e00f01c00c59004541c050544180031259846c400c0c5901c003090415071564a01c50520307444602064110180c1c0322494460560101c040c050750550040c00d240b06a20940d100d0025056200001d099085410400754054110300e801418141d0781c2d040000350b0710750484140d5050f128241d80d2001d0012654030103004140e500d0803940032004e40c5040305681031003800001c000c50303218888000a80e680d0403e550a070801d11000c207507041e001617411114182940121928203c1c901c202100320750043c410711b0300c94840500545160000c0c00701310512149a0001194220500202100c0c0281404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 783134775 1250 783133525 783133531
    0x8090d150c020c0603160e040905070e041109070504035703020904020904030e03010203010603020a08090a031209050a17040302090f070504060e0310090b150f060a110a0b 75
    0x44000a07104001d21402824041c400422501401c410000e200000b0010344034441c0202103442c1900e0401c4035000068090b14515a0190840c41406400f0840c2011700700c0d04d5014030320400c01e42100c8625641440f0810340304a6040e40469402d00040000c1014072102034400c1421184034500c4a404208207203030700c90012aa00c1051080340d009032034031011100c56510003e541507903035440a103903a000803105200140000e02600a1102107000c25000d02441e240b14100100295225a111a001002034010a507903a000805901c0031a074541d0001c540c3c038103820f806903a040e46d510782c0c40c0320070390123003503040300c200c520b031003005040c4002c0750441c14076080316004044800e59451943c010404805005048441c1074655001071200b000d8000f0210340484081d070030507079499503070540041d0030a400d401c0300c00d013200e0400c01403104100c04891030a110320044100b0807860070343c0c030781402490707150040e60a8000c0c1080116080c417034060550044004c42d103400705c030150500d50b0f464140d00d440036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 783136025 1250 783134775 783134813
    0x2a0c0603050a0e01050903042d030308060a061e2001110d0501080f0c1903020603090708100902010e040b030106170f0705040b060d2c071806080a08090d 67
    0x800501038400494003641e003800c211070f0001d0250b4102a02c5103a100d10591044a10405144070798561420032016405041c0b44950100c003801641c07424003800f2204100e890038070403400070402080c20350194090181001040c21545168402c1c0c4009131405000414940c44c042e040110381514071000740519402d5100b4860701c0c48e111110407440da0242e4a0681222101c1c0c0c10005d05100b14220015081e181114200c0d0000c502400482c940c0012082540010390800d20001c1000403540000550004440e000d1048411107840c5210708003c5a0304000001d000441d10590365280d841e190b04001030302e8000900009489a83e03200d0240910108000c0d55811742180c1e00324850101705110b441c004040c20348041c00b500703620800182c21889a41003c0d000c15507607920442072603801c2000e03d441c00517032084001c6104402d5007805e40e075074005e1140c08040e2520380c00e086501107090143c6001c03124548010070650503280d50740f014607041b022102e50080c034000d85820106041c450401806160 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 783137275 1250 783136025 783136031
    0x20d050f0d031a0d0203030f130902041401021023090f0d0f0206060913060e10051003050105100501140a0c0c0306020c060a0e0d0e030c030d030b12010501062a0c0603 73
    0xc41407880c03c0215000360248a410744006000158901004490603078200d80359045d075900380800511408066078020b0b03008144007141c0492240d00710f200d0400c081009800b12618150385040843c00d0380c012107a8515540d4408081070680d40d80484030740d4104044006a03003031045258049071410905019141c00507485074140003106405110161700b0080a403442c100514100c9540d000300c1140141c0144407d44d034502d0384503a5141030000d1070420180d82e109005a00b4400003521300342130507020554880d4a0b08010070301241600c82c40b00e00710f90042e11038a624110260a5082d1604421944801d029104a5020020303c5032016500914840c86006858003803c001c403900c1e00e0350040c030500c056413528210103103025001420240b008881c2c584038051001040100f0709004024481503098412100001c090607050307003001e10f00c00c0c81610700f43c0c4018040041ea07800e9800a1143d000440c2510050400301b0031911002007410300c04060600510303c440d0340f0070780602ca042d8005000269 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 783138525 1250 783137275 783137291
    0x6090209100509090601150c1e0b06100819020703020a08120f06040902010e0f01051c02040501111b10051209100e0307080405040c09050303070f0204050c04080604020d050f0d03 78
    0x2801d4140b03144c0000306003004080941c1000700c0e0700c4001d031a085542c028080c1c2e0030b003031104001c0b8074800315038005070550740e044000c0c050f85440000001c055400ca44141c954034013004103140300340c5044c3e101c0d50000c01035515203082c40408100035030103803005408500512820102203000e030300040100400398510b07000c040c6081c81e0504114000904050300c210b09189180780940c5c0c1c00140c044052800b112510800c4400c0c00c0140e519105d00324502c0b21038800c50312003185005007603018204440080c0c9449403e64014040261607030025400940d00002946c529050342c2007171078000098449034144030786800801c40d00031654141c1140c0101c295402580318910141d140d01850b644e44601030021402c1100782e603140e88460146019035401282d07103802006a45103d800710b50001e0070080e040c1c81d40c407026414540c008501c40b403010b0f030045003048046900b2170505800c840896920318081c1c0b104e502e440c2d0800c00089504041a0b030303240300d02c3c507542000483c14425540e0401321518002000d42d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 783139775 1250 783138525 783138529
    0x6040b070306060c050c04050c040f090603020307090606140a03062301030c0e210a060623060315010c020301090c12140105090601180608010f02070201080a060b0412060902091005 79
    0x42c00c0e50007100400101c040c49000103400081c080c0080b0f81c088074081110382c0d0300d43c21005a03008503840145156049000050006015806182924020307000d41d2000303901c0e200c0755015038440f845140001914409082c40403103940001e00b801c40b04600d00894125615002032040d075a030034051000684d00701c032503031101d981c15108146c4074074140d083c80c0010381d2051001840d60781c4007a210043c908040a82c228500c5801e0206143c07565006c0000c210a43d1580d40c0c1503004c3c4040448840c0f120302094140e0381e207280c01400d8900c034944c40019401c0f4038101000461340102100e01c103c2c0c166403554031490000305031030303050030180120200912071030b03120f41064080a02d4407905070480fa4507010601c41c081c0070100d4003a064580c810052500d000944c03030b4440007040140c0c080b14840d407a006441400507091f400800391a03000b41c0c3d41110ba919900348600840b1320305e210382294120100410800390302e0408900d010940124000101e6112940105005600440d0b110540c090035002c01d001074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 783141025 1250 783139775 783139781
    0xc0807081902120f16020306131703010f14062107091d0a0e0f0115052b0b0601030605030709020705011103010f0b0702060c030a0905011d1c0507050306040b0703 71
    0x84001c0d1000b000345038024210300740c0921a5154603d8612400100340a245c000709000c0380007968054102c0d94149062006081c55000310001104c05c1d90300441c151074035414404c2038a041c0c841ca1880b410742d03e4a400740b040741402441142d079801030300511521640120640760b40c03040048400890361075180000005001c0c2107280c00000c0750002c030044611400d1007a00e0502c3c0d100c0e94103200060f104070290b403480d14264416610086540c2841180d022990311200ea0314101d079030589990055000d520358000c09030781c0d0b03611854042d40b4044800004200c9040708280c2140042c10000740f100d0720344003c20304041b503541024401036000220001088800d02c00d9100d80ca140d40e120a00750350408603500f00400c07140c40350841e0f0540201c0c0c07243c1950355510489580c0c1000c0c0d001c80e50f81c5c035003980010b08600c0251042d54040b03620103218820b8001c0c00d406c400d42e0540b00511b0000b02080c184408e15162151000c00e42e401c0c03007a02e80105154600b0422180551300807800d001051800d07000007419 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 783142275 1250 783141025 783141067
    0x150b070f0605011d011e0515090108061f0e01050f0c061b030f160e130b030c0306010602070e10090203040309090b06120f1e10030317060a060f0c080708 67
    0x2011306190003103441c440d002c41c1c100d415100306111481942c0720700d50340c00c0c025a5098000c01e030b011208055a8079500c035428001c0c03509200071703200c21000d543e0301e03400c00807220202900c41d2610300e404075204851520520480c1a034171014107165080c907070010355010751600840515215a4000018032917902e0710f09064054080300304026038958a08004400301241c40a0219601082a00d14103403809000c2c210307080404c2c10281024080c0110a00c200300602581c070344086c041c0c0600e1031114464240440e10340c1c140c6260b0340041c060703d071506003086071040004020a24800081074045104511800158011400f9a89025400c0c1c1020b03c2807048514014900d403042e4010850990003017503411225501500144e00c82c0c2255541e000c07504402d100c20100380c0880130300041085041c280c0c1d80c034a00c0c1500d000340c1c0e80c4800c6480c120000260120300b81d802c154414a100d0f0100115442224030703a240b00c03254034042c0f0704042c080c0e8804403d82c01c617120840c1c1c08070b000700d003180c1c0c010b0002001c400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 783143525 1250 783142275 783142289
    0x30f13080a080906030a0f050a022a1908070507141504050a121a012301020712020603040804030c080109021e01120b06131e080a0c0603150b070f060501 67
    0x205a444035540d0b0a82440b50000711800f440c00803000680c40e865940c89043c1e402d81824090100c0c0c500034205100a41c0060000e00c89603a50004100b0410327a1407441464102c2c0306402451900f542e1140b40c0c0d01422100c100311030000e010403001000070380a00050b030050040044580c0c40d40c400b0340801825002da141548440b4405020801843c1d4800b03204d803080762030740301400d400c1030300380d041008107030090117803003807407103101000008504108030a61500014600000201d0080200049846035803d11440c521000c0d02c0701d03003101500c1e0001c01150010700c125800c40c94103070b0325030b00c000300600158440c10707040e5901d92144065050000c420390359691100f19402c1e8504040c00040c01d080034685080b408180d40d016590180c0e1203800072998420101c810140c0803d0b0355a446000480507140d00c0c030f0710308012050000c2d91a030300007150940c00c0e61100703000c0c44903805c1c0442103004114000092240000c640070002304c0040d04001012001d006134441101c1c1205810200b040e40d1040e80034034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 783144775 1250 783143525 783143533
    0x1103040b01060503100803070c0e0a02041404021b0a0c06120501081906061d06040e010b01020a0308070c0b04080c060f060d020114212208030601120905030f1308 71
    0x21001840000d1440d05440403410295140d48034000e84048081d4136070016811480005204804c3c0141c0c1c1200c0c2d0216490440000010342d44c81d10541d040c1c2c00355100e29050180b1410182c03449285c01d4001e0410340008107007074482c00740000e41071407410b0306010003139406003009001440802c0c5e1080002c00c0002650000b402554903040c1403030341e500e4201540d4400011400c084400304a00703a005080103044814141c0240616034f000c0d500c0300101030701e030140b04516020032240c4006040c09035a0210405030080d200035907003510280c6083e10014040d504110750000e440c00001d4041203814052030040210741d44544050f4112450700e08050040c0d06c0404031002005226a40c00390344840803982807a125510340c40d03800109420303024940784440c0b2503541d2000c400042071103181c014818042e108030100c440481c100c044035035120b901703009492000108000b40480d406000a40c0b442a140c910000c1d0103003003a250b45040d1380004403442c01d00407000500180030005180c0b20800381c03194201030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 783146025 1250 783144775 783144781
    0x25110312030403030504020f04050705040906080a05030702011206092a0915230406030b100f021e0a0606060f0207170307020d1a01080d17060d11131404061103 70
    0x1500e09000090005040503100d000040464550b0a080f4100880c050010301c01e90a2885004e0020740141c0100506a407a1410004825000050082c0705540040c0554035008803038004403005007074800f08500e201e449240002c1c440c15580704400032503680e13181080b0016840e030050075284003400060400c0009500091120348482c803a455808001c50034125181e0560b01c811981d00760b04000340c0c3c9402000414001081a0141c00591881c80b0858016000b00c40c40e0000303641003404030a481d00142d01c02103000d440c4080841001803940111306c00ca502075422640c490055034926000f180001750186d48144909804110710780150982041020303981c200e070b84805540e4004c512010740f003184030039100b900b441090b0204920040003001c0e494070941e140c1c0c1d48241c2e00c4a043c140d00001464281900d0a42621890714900a10004100d03295041c069102c0c440325084204d0415840701f0034800b04402515103100e9554031541c40740c48161107240900302401120301031400303c11841010410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 783147275 1250 783146025 783146053
    0x20c0601050907030e0a050d0906020a030f050912010c0f09050621040f0f1202120a0509041d03220b030705030406092301090c0b181302251103 63
    0x8a141518416102181c0b0307961019003c80107000d403803400c02d0460284a210b41d00b07002d000301c0c030381c0c90000c8144c949550403a92103504030307580e4141e0301010340000c528022540c1d070240b144008001c4410000d104100c2d0b04220221036084030103009500380425050682c42c1e41d05a00803003220010305c412a02903080c9686c540e1522841144800715007130500d0104006001c02c40c01d04011041160005c80d507042840003407034602e5141070000788541c0940701e105607440445120104803517140245550389804e080303400c0305100140c080d2603080c40380c1140e400c1551001910810140401980c0264219a1002c901000f011704012a13045a90042c50410400003403607000300c201d039080350b806000000c6e00d850a060045d0200c01448681078070701e52014490041603070540040a078140101c20401c0041e55908404960344250f500d001010160300c09000d04604d44020002c1080d84850b13800751401a64102202d101d1745c80e9080f0042d4849618003800a00c018030f41c10340c1c4403c030f00364002c100c18010501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 783148525 1250 783147275 783147283
    0x10e0706020c09040f12020d0e0406140607170a0906030b040203011d090a0f060b0405090606010806060d111306080c0702130b040e0f0609160f06200f0a0b0703020c 72
    0xc883c0151501000301e0200a410b400000c0525048002d541042c00401c40c000c3d2500901005113001456400d0603405a203420f10034a070480700030849040c118020301c0140f10240e00500d10581e50703500880e0444040c9140c410041c0340171030b0f155548550700d81c200440502100d00d070848141c040c5106100500809001440c3c103000280704030f004085075030780e44c41d6041ca03080c0f0640d4010100c020141304d003020030080307411156442c80c00f22740c2407200781e80311035825945882c01c407104c0b400281554081082424484000c103101d0464890214070355050b404582003650204040c0013a5807072103002004515845030300d258001901002252070100b075900060640394a08c40c404900d00d0744c400c018011692160311000c02240080c0640780300d14080c2003015107461342211009181d01a410302c0b203034219031101c1d0400030b98140500386909070341440303c1107441c0810700145490800000d10031400954080000d19071000481c0002c007041d400b24a0b040c10382e5040a4000c2003410f00500240c5040c6901203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 783149775 1250 783148525 783148543
    0x1b1d1f1803200a03050102040e100803070f060f020d14010303080c030c2b0f09050d050408030f090118080a030207090b130b03010b0418020f010c030f0e0604090e0609010e070602 78
    0x2d495405101e03003180005841d907515600c014080e40c1300040c00603410300d03514090361003a92013078043e400d2680da030b42a0075164418804002c100c40e4110300d60b00005005580a888181c0c68044c0050804e8550301d800300840c1d140c00d407840881e07201c44c0010010164080f40c010382c0314401c40d40050542c00c00114100d09130290f154030110038140809603080c40e980c0140d40d080c4001c8017441c00c1c009802545030320401070510783c1d015030b5140030b02c5148264450113902160111388071200150700d000c80403141c2003455000700441e90304120030656010301c440b100000603405001d410014043c00e1600e440d01a1030f0088562006017001d06080c030080240c1c1d19021035100c1150503000220300051190006401040e0b0700980d60303802071038003290550280007456400c29191007592150a60302824005584d07015900b40c0c0180024041d515118100748180c10780c60700a00042d00301810300362510421f800381e449500c80342440750b01c40410895034034803d002e60307000300102d00c1c0601031890030010000d48441c408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 783151025 1250 783149775 783149813
    0x1b0318010201180b13060c08060f0f03030a030f0f051f08010c05071203140c0d0f0b150f04030f030809010b120303070f0504050a271b1d1f1803 63
    0xa2000a103403802d82c202c1710084294048410070103402e1160000c0c0421106517002809000101c18060f0301d410600041d000308800200158100510f140c0700f02e0185c41c484454010302526100e6400b402d280d1402140e02070b1183c0c1901c40407003851410710402009017940040c11680c140600041e0607600b000460740c9042d0841541042807402d0308040d0043c044010381244003001140821400c0b40410000c0c20038011002c409021045c01c003400300382036662040441ba400084490f01180d03079070500b4000c144a07404100c41c1e90601b40c2d40c0d11803240300440160705401043c000000c01a00d90740c01c3c0314400c4210300072141000c4646020020955a010003040d08046c00f07031590004040394015000da5001b420001c02c1700150700c0c1c940b9403806040f803007a014a18150548015039081d040c980c0113940390318071701a200c8014030402e030a0031241210a8580d10042c0c0402102495840c0c5a140314082c002d080500601100c1c495401c004284059a009000c0f0b0240c440605100044040b80246032a0440e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 783152275 1250 783151025 783151043
    0x302010c1103070b04080106060801150c02031903120e03030f150103060807030c081203041a13150b01080c0a17040812090705040c0903020f04111b031801020118 71
    0x85241865042000c409407550500c1441c0000615520a0000348243c400300e0f40240b080729900c004c1036403074040c02c2c010038041503103001d01001054840c4411541c600d0008085840200d050490031400c107061000950003c0c00c5145000d13001c2c0824091170400d044000004c52640c50620301640407160b002e0501000350070000d4040c680ca030320a410020180401e042542e9407d80d583c0b42c5074120000611816826000b9151010b100a0215095034070030340c1c02c003417a903d44960305556000008002030441000104080d2914049444215070301a1146007040005000300050005400054001cdc0f02c00c2c3c3c400c00401401f9911a0f1124171003005001080000341c80e92640e1400d101ca0380210403204881c1003005040240700400058001c013107031382c2034808200f91450700c1c10440700000640000307500304071141582821402c0c1035000c2c180e00180000390a003001c01660540c036502c06581c0c1c1403582e6500220b104c8840c1c40300203501196106090000f000758032001160b210050080d104041c00c0411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 783153525 1250 783152275 783152297
    0x406061d130605180a140601021c02011b030c110712020d060e0f0717060c040e101e030302071d041e1b1805040507050d0201050405040207081b0604020a030201 70
    0x6070b4206501074140204500350103c91000550f9110104071190b00c112070500007440c0c486924608100d001e284180d0190400c04003124050020304048d032201000c42d0340e030340e20307040781e0000f007500c4141e105041360b401184840c1440f0b00140304c2000c0032039901041d00405800c02c200107801d8400c0c1100c590649040780c051107241001002480b007100e085d80c2500801404e240c8072000814076105403460b00d4041400301003007101c0350b9550702c0e0072201410005000c0106110100d14510956403100e0070022084c01c0390b8482e0a4445a1204010140d25041403203c0a02c20990107101d042c015011700000c50f5032a8880400200d81c2e05070142014000c81d0740d070f180032100c410741801c00700001034018140c40407842d00014240e01d81c1a81e8411a01d2400c0d05000c285403100b0503000300c60295800a0082c4141c034181800c1002142c4800000c0781848000c12000606403218000f034031080340600e0802c1e89450385146041c1d400301c10f0310411843c40d007000040000503540c41500f1010740c1d4081c41c0005402d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 783154775 1250 783153525 783153559
    0x2a0b18040e0106030f0b070207081504051608060a0b271b040f1d100509060a0905090303090c1002100c03020d020304060516020f0705060a180b04050406061d 69
    0x254070300c0450825400c0c1180070080c0501d96a04410040c8585201c0340c1555401c00704070380f81c40240c024041103401491030740141c0826408000c0d0001c1c0a41c086c0c0303002c2d208500da108900049035001000344e030020000c2104103c814422001da240042c2c3d0a2200400c100e120041c1e00b480ca49040d101405c40e0b01e01161300803854510040070450540007541d9125150741e185080040c1c1132042413054000ca00381e003a110f1641400b610300501004684103c414184401c00014500013800315402c07038046e1a0024a0184c1740c00782d24000da80307540180d80e0b2070a01d18031490800c509140d0480c083d05000c03184100d01c03540020601103440045000103601e0340720320801c901038411a07030350380c000d140040300780018400b1035401140219821004da00c204000e03200103a07120045003510030100d4105000810150400400406c0c11400c20b02d000060290010410581e140c515080b9003c00741c0c0200301803041c0d0a06102d104081d000a06001c080b0f2a1407101c1018031824015038240109105401d81c4d60380c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 783156025 1250 783154775 783154781
    0x6020a0c170f070f0905100b180f060a080901180b0103080306130f05061806060409020702030c1801031401090c09180606080a020906090c160c050901032a0b1804 71
    0x1120007040c0c5070100c4c2d0f00c0c2841c60100e100ca0042110003403825000c59098054049803000700c41000c10740340d050040d10044041c0c00610005860b4200c0c160b070111294a54a8070f006101080040e211594070f41018455142182c404205103100845061242004120510805170440c0c0d84a03000039500e644003008642c140c1540d54045107042e051464840e103243e01500003501c903082c266210089811949007441c01085c0c00e41d840c80d0000000c110034403da1005030000e100d0a03001900721a19001c50b000491715140122240a00300b4030f00100501c1006000c02d100105400d01c0c00c002d210114132a2550100306c0c4003440342803c1d40ea590341840354040032500e002101a82c00003030070800c00350f0b1600725030b840d10400c1c4c0040384140c00940001c0c003d4606100c5103805481124000c0f03080210442d1000c901c140c2c2c00b9415220b4450706440050750b40c0e074428000c0e001c0c51080f00018140c010000100b4401c120030502e08a0290225000340944140b03a07080d2121203d45c0700c00c100c0c0e13803003038103000c5002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 783157275 1250 783156025 783156043
    0x1d030a200c030a0c0603050601021c0c080714070f0b030f150f03011407021006030f031b05060412030b0d02032503060204090e070807150c110607110a06020a0c17 71
    0x1d0f01074402d02100b842603031020303507040307503515101408140d81e80c8004a031244030341c03074440401600710a61180003920501140071000d2146058520300360700313034030384030b41ca0454200440c8066109000c03d100c0300102401c000c00410f4510440360840c01c01084e0000703000402010102c01c14022201d15065503240700426072101d50140080240c0801582c401c0c10480e82101c0c4000944039413024404442c0755446a00d0403a03400c81008070490605a4048420b0b401205061161840710428200802c0d021b00c007090080340702c0c070054a03600c3c0412034094195580c1a810900c200f100e0340d17400c1c2c0540c801055940c04180d81100c1e04111000020203400000d501c4e0300040c0a4910204000c00c0b2103103668800d000c2044201c080714040c030303070f16131031035548200078082c0d2040071903038800d0103112600034074001110f00d20420f2030f1004c2614a50200d031054005900980303180c22035011018103030901c1d450841c080c2c400e52010301801d40054039104a400c3d602d10034421000c00322101903440d800d0034480310b29 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 783158525 1250 783157275 783157279
    0x4060509360103030e01090302010c140a05100203010326030f06031c020a1e030f03020f12040b270312060a03170c010c051c0f0b0a06031d030a200c 65
    0x10928100009826440c07400340400c13804a40420880b424941c020040c50f030071290b0580d214000410940d8888071004010303210010144030b0603250000003881881490301b45080150700603125803560408841c0704400a0006107511942e071011080480001c1c01c0300d5101d82007501e205140d03101c401c0401c2c0b800b0850507120000d07081a40311517141c5c81d400705445598074001c03840d421300112041d170b81036800c041c0e41d400140810104e020440074031f40203030060844484e00201c89820000700094804281d0030031201190744003008020004042c0c1004103d004607a01c5525005110780d402d40000e50708e00c81e900b1624601407450f40003900960f5400e1840c0041d660007420002800164600070f001504807a4054819500341140529114441c0095900d05041340300400907561111890600a2124400ea41c0245031102031004181c0c80d0200b01c00002c20481d94001a5409403031100c00303011601c0d6900c0e4010780c1003084400c001c0c0d80d0080303203410700da5150f4202b40521185170450610340441e01451079 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 783159775 1250 783158525 783158599
    0x102070b1b0c040b01020613030c02101101051b0a140408100507020d0509091303021c0e0301140f150a090e0a0b1326041a0702030d0504060509 63
    0x1041ca0480700045418460002141c900c0c600e0340c01004180e885000d03c0c5401a404000007440700a148203e900000303000c0e040c485212641038000c40d40c600c617465488000f0070781704100d82c40b00650134814582d01c00d202110210207400c445000d401d040c07045092440801101c00d071910220b020000440340100221000c90380145015440d600180004950340405030140c000c914102c540118102c8032260300c010001d192030350701c0071001d02100002c0700080d800c6104485a001c5062001030051032403001d0f41c2c495440802840040600b074410000b00344440c4102c030000c1c04000801071980a80180800c5100030601180c4030100700208440e85c010a59141070940c1e41144000204030004807074011849511903583d030ba0356504810021582c0100175148440d00000110000c505a490480c1207200c01c5260a03500c000000250100b446010590700300041c804085140c00c1141c00d047c00d14500300281411728094015095000720b60724a4000e030486c030380c0c8400403241203d002142140550b4a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 783161025 1250 783159775 783159787
    0x908010905060621120a0c061401150906020c060307020a05032209090206030414070504150e010603060503060109111c021c1b0c11030d020a0b010f06090b090102070b 73
    0x1140da510702c160b92044c02140c01101007075080c2821038068444414030300c001c00560b9500d102143c0c842d132009070030a0410181c0c080c40c00000300a13000700c6800034650000d158042d4144040711280c2e1019060010510030301d800c0800c0110303004900081505001c450043d165034460701d0aa04010b0620b070010300d030b4000044c690302030300c00100904c3d4000384400c50040905444d02c40701821a44000b20203903001c0400d00004001490204004200801c44419108107a41d600d000c9015281d80503040100202300301c50034030150580300c1c1010300500480c9014040140340102003601c5d41018003805500d1919452940c0681c10904115201c841c81d03005124070301c00d0141c2d5010000c2d08024422007410302c0b06075840c0100391203030259400f50030b00300c030350400100400300d000d4400c01c03036600c01103134015080d80c0c0c00907969400780003030b00042010360080c02403200309103827492007000c050300502c16401142c14240212603001e4001c0c000e4030203400400d035840c210300006070b00d482103560111203d42000582 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 783162275 1250 783161025 783161033
    0xc090106050a020c0105090a030803040c03060c02010204090b0a03021008090a080f0304120216050120030307180e070e0907111006051311032d2401080613050709080109 74
    0x4000111443d030030341c3d618030300700001140e42d48900c601d201d03072140d001c4d04144045030420700110b800512400c4504855540c0c1d80c0d454094604080d80701001d030350f0100d4108500c07030700c900400084603c00ca80b07000041d07046900180c4d40ca940100204100800800021401c0000b0400c116080e07070800030540c3ca4426420214030103034000c0710104c81034140034101e8040e550002136180003615100c003030181168140b20044420848065002c0680380c0040e40c00481c00718188000c40c0510441e41d51000c1d1240f02c090694004401c0354031443d0aa030807281000341140c0d02068403010000304659071502c1b0349821004607040440601141d0550040da41c240321011141e9002100b1608180c410302c3c10040605802d400315000105040926082000011505511030f03240c0c1001c40d82e03042c1c501c0c04a1100d040095001001100c0c80c8008031402e4034064440709109a00c006200d00c240b034481c00f18500700d00071500102510300c0580c1441d4072100400c1032203000e26a0740024048103802000b00d0210346c14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 783163525 1250 783162275 783162277
    0x1d120702060c100c0908161a070218070e030307080306010c020a0e16080c0f0d02070303110a030e28060e0f030a031d0c0a060804020303090406090c080c1305120c09010605 75
    0x8038280421862000040d1b0f84602103108201031229240c42400300d07240c03c000c040082c900c40608810004100710000040c0c2d24010300c4107402500001d60202c81c6404240a08030204251b0070a1191b03000340802400109450200e0794002401e1910500210081c400b01e02e1b1030303c880e002046074100c44030420076401c91203000005007a201d80e440241c19140c14010012500c02d8400300b41c05c5110400ca60703481c2c41c9903a0020001d0745e109180c0010070390403403401d070b80d002d8000310b0910001075128485a0f41d070001c10400003215807400f0f940040c104007840f008022440304032400911164035140148041c200038000d006062001a00b580d03aa2a400080180205441098040b000203803081e04c4a00510001d800400814081c0c10b10031305a040c21801c1d034811400500481c2e042c441000b4030000c0340c8450043c0c1004181b107100200c2d01601400020704403900080c82224140b80611480c2c2d810720b0000421030032100306131101c0c81c0d9490006207841c01c240d40040141c1e007100030100001002c40d8008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 783164775 1250 783163525 783163541
    0xe130e0105041a2208040f0b0d0b0105040e130501060510020d0206010f0312110106210b09060c031503030705010c051e0307120e030d0f020d1d120702060c10 69
    0x1605400c0740002c00c854031294009452203400020f0592a1344141d0024800391450640500301241c00c055490302c0c1c2071056005d540004150301c8004c10001400402e900034550034100900b4080c0c00d160400098080d42d00c1c0062840304142d200741558014040294030100150a000c0c04c010801040c0c41d0000e9561280c01d0094001403040800001f55584024a460296940708a58040c8005054012107001d54103500303c03019556039a9001803407090b03403003000401c44484284042c1e00c80c002d0a01840443c4001c1c0001030399042a01003110304e00c050380880780e22070a400c1980c1440708078400424030318010b48500a01030b41c603100c02c9144c000e40082c060402c60521503001130020028055200349804203840034408246500001c0c2c00c3c55250340c20204000e50310a084a04022026446c441074400b00b03020f03008102d0740040c000540c1d0489000f02000302841c2601d40d10b8042ca4035200681e62803502c8038000d803d0300d000c110801107507a20012140402c864104480e05528240803500c000c1c0108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 783166025 1250 783164775 783164783
    0x2d020a090230040b06010513030f02040c08070e01050c070b03011e05030a150203071704031106090a020d02040f110408030c0106050d030210090227060a0807150e130e010504 76
    0x2c02c1c0c1c010381c41c8036036030107072240c81d0540314061a081d2a559140d1502d10307005008541800414050420203180196208000314010b103040c0c10826040e00602c0200d40c03080034240d080108040c2040501904500781600055081c80c110703541e40c070f174804041c0c00c28a1640294845000000002400c040d01c04101102d141d001d01d88a809195681e0030107691f404040c000600816200c41008012006a4040c0d98404021300b042c004000b500c00301003184a000b00c500f01c001c55910340c81c10310100710400c00a40e111000f039000304180c64940c0c0014004440008000f07104903107585a050190b40701d03810109030018080e98542d141c5844418850300d0303811a005002256107480c07800256460407600e40401030307401d034020304403500041c42c40c1000360031103c5069800503962400092100740341c91401c0181107903a4040040703405d00800f006403155141d0b008880e142d1000a0910204075924517108031001203042407500210b00340080340e034001d41180c07405d1005140c0782000400c0d01042d0407480c801c03449 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 783167275 1250 783166025 783166057
    0x181f0615020304150804110a08100b0103110f0f2817070c0b1b0d09060b030304030305120a110a090905100e06010c0503220302010206132d020a0902 65
    0x120380d801c82c0d580c082c61003048001c038401110622890302a801150b005800360003541d255040c0000030880381c80c0d0903401114581c2c84000d03030b601d200440388183c080c86075092034184100840081070082da401280c031011076110700010311200c58040001110104501010385d10304220130040d001c070b05620700c0e800e108042000008280c0b03420305044401c81c46085541c0b51810240259181c3c10b408000060032800c0c0007004140c8030250240d0000901007a50782c82c600450344900300e243c40416070f42c020511a000b41c2c81440309000007078005090f81c0390b850400c2c000701c102d03556105024000e40500841540d0140000032240075141c0c0c0400814142ca8100c21b042c0009c0e240d204040d02c2c4045e01d0320622503030001080110300c40390302c0303101100f03941401181164141824509041c4159484030400320308800c0c2e0780020821941c0510001e907004040d4038140502c0310003a00d45622005070445840013011040244100300c61802680102c7c0c1a00a0810b0481ea0344854080b8002d500c20f407100c1081c642 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 783168525 1250 783167275 783167309
    0x6090901020903070b0c10140a15120602131a030103060605031c031e0218010212281214060a08120414011106070306091112181f06 58
    0x1014000c40b030104102800a194017490011400b1050f008a003503460180034030252003020f240140100013002d00e80b18808d02c52402c2400140c0c0c1110180034400d029140400c02c03c2146c6040d0082000020307411404c0565a14055080200c00102d1a000840101000c010303ca0309103080e000914149c80c0309420402166403100101a9110f100c070850300071360014404851030042c801d800c00c1181003081c8a000c0c0c0400f2450352124240e030003002c060b00e054414030318024099a4104442550454808907007498140c05c02e0100c5954460018561410000481d007404a01e02c60031b0307080203020700110108140e01c051204100c405c5025104075118002d12000480c0b0b04001044020030b0400d01401e280c0303010300d003840c0c0b01000740d0103012641c140315941c182218023035001d0040c05d100d1545650006020350070200f0f41011142ea00340402e0b01c0c000180300400710b000a040025410980c1c0340d45080c610000300a03640e20702900b04000860201c0c4203015000c07003040b2074116030142c601e0811100600b00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 783169775 1250 783168525 783168541
    0x50c0601091a0d03021006060c0203060c13230d0f03140f0a0e0604031e05071d18010f0c0306180c05030601050c011107030503060f0409022b06140609 66
    0x80060b02c403000340342c94022200340c0614080b03030311148039480b07801668440c040d054409400c071162a0f001c680420101c01813a01180340900403154010050341510741007d110080c4405515594090260580c200340383c1c2030b1300704c3c0501c0c04103001410010078692040000d0302e0141c011030740051085001c6030320741c2203a020500c000030940b100d00e007102070724600b80000e40c041210084484407116030000d40800000c000320715100c0013050600f925100b440f001d94238034a00a8940b581980c132645861201c0c402d00001c501c00c1c26855500015040c10070b02100c040b1a80d21401031480c00d41803002145860f401e4a500e54054001c10103c071444a814200280040c0c480f100742e5142d42d640000050040000801542c0994040d18405114000020f1906451089032041d51b010030010b501264010040048628069100b4800544150703024410303168154089420700d131900700240315001c82c0140c0040490074401c200d010054210906010103d1500700c4a95010001d4807101d00a020b9440025148 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 783171025 1250 783169775 783169781
    0x1a1c02190201060e06040b01030902030f0703050601060201050903040e0901021303060b040b030f07170a050a03030605090a1a011d09010e01050906060309071806260c100c06050402150406050c060109 87
    0x1c0e180760b90948416505c01c0100401054030301c00740c0381495982e5141101584040010400d605003c0d0002e00b141030030345c1440b80c903140c4141e001070216810607040291126000c0103a40c01c6464003070201c8041d03101c0720140c40c06409010601c07070310314000850000601045803c03c5030364190a686c01c0040051160a040e143c40c2805220308044e404035808001c1419800c0420a0001c08007056444600840d034130f07242851005c240a500191b241c40b028025854103600d42c3c0c0c1c01040700e64041040150058585000100d80d0341241d040c002d0030410703900d807540a6100b401d0318141c028100d245c550b840b04000c1c09000028022140140028000281603003080d4003224000c540d41d00080c6406481c0480304e0458000003401c0b50801a2201c03000035181c550803600002040d0200b4140c505500143d041603d060b051202c0c4521a15001c00c2c2214881c0d001550b14403010381004021805943d58008102c0b14460b40251050324080090b000905583c8071000d0040c10502c60203413811640ea9010210030b07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 783172275 1250 783171025 783171029
    0x1e0c030b1c030203072009150102250503010c080907090e071203140301060815091009020d020c03030103050303190203070e060c010e061f0f0806011a1c0219020106 72
    0x1035500711070720701d103003400050307606480391048a14206803951480e034608103440301240c13050141c0c158800e103407400a071902e50007039036070342003182003003602d00000d6441d040b001c4600300a40380506000201c2841004041c0075200141c000d206c0400712410080894030100d540301054002e1000118544a550190744452403000004011450404065101c20702c84000c046003440040c900c004442e000010246009003c1a02d0300c1000d4648030081c0014102524405031046c42c0800802c002c0b400051004030076900d00410042c0c4528040706000300a00c181034440e20b0307900c0040300000801a002004500c2204074140281c024a01d140444080e4081079030f040d404500d9500c03450a490408001908000f000c060022860b004001030b8a07003001d40070749010440d10301200d81c1c80c1082c404191140020154080d000c075269141a400310f40b508010f000f0741c42e0341c6c00c0c1070308003c08000100040e0f0b0b00940300019449507a40c0503d21400081d8841c40041c1c071031800f150140307005a0f00620a280c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 783173525 1250 783172275 783172279
    0x80303060102211c0e060f37020d2c030a03050c1204051c080112030c0f150603021323090a08160308060d0305120403090503011e0c030b 60
    0x1e0307442c840c4a044110855403422503065014480141440f5000340d074100150783d80d01000940d002c0c041d1200d400c00314010420401400000248220740310502070140e203040c41101d8035032001d00c10b140b00510980003030b0070342d0202500214500983c1142c5030311401483da0020180361301c40520000302c119078022f410541030650000d101e01c08100b40a904a5640319058036142407a28424142c00440c00c0c0b01078501707958913440344050401d20700510304001002301890420b081e0940c9000300924955422500c01020400e840004004215071154102c60701c9a0001c0020007880034059100d004001a1100380d11441d240944803030400041d20566411000941554200881e1500b0b0400f454a0140c07008480d4454681480b01250111000e0300503c1104010b041025420341401098818042c2a480c81000700d400803000081c0c004048030320240c512030520f51981c2d0381e0b00302601c2106042d0701154055007060801d5410005a0703214216038100d51500b00300c80c41105208404603001543e060f9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 783174775 1250 783173525 783173533
    0x52403070b071b030203190b0105010921022b1a04050c120f0a0c09050c120a2c1e0f0c010e060403020d03090806090d1403090c1018080303060102 64
    0x200403d0003000c03807400036488a2150740074141c0c0c0740d0120349040301d070110070460184000707246401c10a60046143c0108800d1030301d941c005040c101d2060441682500c829680700b03041c0348110842d12400400c906410001d914011b020002c2400e01c1c0380c0c03c05060046441070007079081381d400c2511404005010b01e8000d401051320351808424411524150080e00d540f0340310f1041a000258010080400014480e0310b5110a00f450802a07500f41c41d0080c10b83c000c128401c1c441c28406200201c60b141e03000622600c007142d03a50002c41744005d218412540007104098484031310b4114400010761070304a448800c40d40807101c02c1024403d40710030030014100d8040e0400f100070100d961007a06c141c025900c00820903032900d680c076400030709c0030000020704a0100701070910821207030105224070740d4030000d00c802810048045250042c02d51001c115902e09100c004404a2420403080000a96000010380562003008400c0c40150602080c02281c8420308103507640170410803404000d4901402040e0014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 783176025 1250 783174775 783174787
    0xf0b130b07031e111804020f0702100e0607120813020a150327020102120c070b0d021201030506180c0303040909140d0e040e0105070c060506010909052403070b 70
    0x114050040340403820724034403c2029010f28007501d441000e00c0e0500d81c00301c450356412100f01074240143d180d801c840c8141d10522403182c0c002d031030100700c0b0050390303040704d40c1707820044200000c2c0c1c1c40500d00c980458202c000814990204480100c4e445c19045050701c4031001c690341e800c1000c1501c0c129000c0250404c0d100603080002114501c09070001d00602d09002c00c4d0304000101c2c03a480b20803021000483d00c500c01e5181c07000d42d40c05000700340b824a9100f2041c0d14080301e0140c0399540b001540b081803003a0000103507080074100030340d054030310040d40441400c0c01540c3d81d082166403540e080c3c80c0300d004540706c1450340b14817a10008164000d020050040c608041c504201080140110002910f00008004441640704003e00c040e2440c8101070300e840304a00000e2083c44200c500c03641c40507850340c0c90981171003d4160814901c910039507000d4404a80f550721f07800104c544403016800200710a08050500000c610450402c0980d0760445044c010101c0485c070815030f1310006445075180380e078020001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 783177275 1250 783176025 783176027
    0x10911270402090303120103140d0e10120e0105010f091806020307021e060406060608071b0302190b04021905010c060b041b181401021015030606030f0b130b07 70
    0x10600c46610018001401d00c444140440d0540c2d104203502d5085c04100c00051041100c11740e01071403a1075030701001305447c1007050070190a58902c100001d100300080c8011342801403044800316407020f105a0284840c000400f45240a01028018000d8000b95a2000308004030b076441980c98815007180d035806d080100303450b2036009501c06071400007180204a8520040300240607062442419030005180903d4030303050400440340c080d042041088614824083c68a6103c48011100d001106150103c210545400ea01d82032400001111466840104106100c0c4141d03072a03200fa40203454a050b0b407000802c0c215013004c19401400d0114030141c03102000320b01294058040c51501500005e00c1c6803085200c3d0707000c203141e09030000c00900c102802d02e20101202503c0f0740103040c0d00200c1d000344403010002030346405101041101180e900c0c80390312804201a200e01d8000d6404c501f04100715a00c2c1d04142c0d0441400c1c00c4181c03039410000001c02c61304500c18095002c19a0420180b1034181c4038000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 783178525 1250 783177275 783177337
    0xe030c012a1d040501030b07031a0a05011b140d09090e0a03080c0708030f040203190203060a0c021c1115010e160509100914150d32010911 61
    0xb0072a6030032041c20a00071465103039485000c0c06580203000900461030b00d29001001d90344169070310035a4032041460a181a101c201140003600c0090812026143c0e842c0544c51625100c080301918800e0b0001d1202c417000808215040201107a60f01d40c40300c00c0d03c4641d514250781040c2800c0842d9441f440e4040040392280c0c440702e42044094402c10715000c0b00e62070b441e1840d002525030342c60b0049000144000c41c0b0701003100848800e07601c008040d11180750703000a510380c6801400c5807409601d5601e0603102a10a1001000007440041c0e50742c9408525080200040464028059281318440100045003000e0300c2c13a80c12150007405a000980d501c041d900026400301b41d0500c00c1c0719060004181c1540e80305100e41c030345646075590300e101d1850030381101500b0301c060800a00070a40b18124001e0003181d10100c032580154484042408120580032540c00348400c00e810290001c00345421450100c90002141291049041800740341c180c048541e48a204000e440b1035000189441050b141c00d185d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 783179775 1250 783178525 783178547
    0x8030c0706030e030c0105040303020405011101051b0f1605070305070b25020f4212100f06020a0302010b0f1804240204210203060a1e0e030c012a 64
    0x5503805c2c0032800d50200d00f550030560341200400c0d0003060038001541c2c03001e02500c0d03410000700280028184400940654a100450310445040000d01c40748810401000c907000c1012407142c00e50001040d04142d52600e2003804120340f940034003000000e0301d010070420707144804054014074188803081c0180304041c03010303084200d8011503004038002055840c10820f8002441a8100e48154080704800b1b00100076031005000c41801031410b041c0c455001c40047da40c1107846008010203944030014041141501031303004031201c11800201160a56020442e1028103200b90000c1c011034501c842040700308484004d0306508810422048180d9a218101040d0400d0080100800c401c3c0406076002c442915080c80d04200da8001030200203542041101007200b00000c2c11f0f46102030005c1e8000b075190040a04540001a25027070405d581441030203940c080c08820420400a14100c00403242e160b402c00684000c26500e41707aa40362001e000c0c00b03a49403401d508100141c4a02001000c1514000c3e50f40c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 783181025 1250 783179775 783179801
    0xd14250608061807031a0405011a0c011b0c03020105071b02061c02030903070b130b0f0417131409040b070513090c03240305060c4008030c070603 64
    0xf0000300346440400714402d40245041d65020038804020502c021010002030080c070b00030b902d440c00402030100c29010310300d2003078011300015682d00d00210f42c40d409030081c3c10403118191046503155241c00d80080e10072011500c0b90b00280600e81d40c00030241da48010002000c01d040e11040146c20040c5000b600401c0c0300e8181d07114aa000c85801c41c1c0050407070700102d4540044c2e62001070440c061004142003164424080100c2c025100300302d5560549100014005041002040001c9000c104208003448400142804459140d90010388150380c1036401e44504e00d03000b030000c1544a042e007400c020451055810805245880c0c0303890303208a82c0c0b9030100081d0624041c0c805408520142180901c81082c01180d4001c50000100407050703146414450100040010350f54007000000c6010405076405024035580c0364403841c41800c03490f02d1080001902140200803401c41441c01c0c4c10100764001d0071500c80e60400f211b5216082c580c2e4a100e002010001680640e40400505109401841229500d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 783182275 1250 783181025 783181039
    0x30c030f1e01031b08030301080309010c02010504091e06060206070f111501120308130c0e07050405180f0c0c0a0611070b0702010b0102011104050117060105090d1425060806 76
    0x10490038000d41e00380c00450b44694000c43d08030040942d000c251014068880c050741c03841d45000c0f2026500d21811810324180301d02021070000396801001590010071502506101c40d1200132a07141210042c0440560340500d81180800c0700c42c400543c5a20403000b5442c3c2525003030801c0804d65a104490325065010310030080582010455031003200d0003400d40c1c0850f0700840c1c050346405412101d000f0040b09130a4134800500d400310b80e014800c1c00440d000740380e2188103071b01c508508450038030540c0c0000341c00a613282c0035401108219403c10b48281b40c03c0c1b1028030641c40d80035501031030340f0502e8101d00b4a03900540ca02c0012440643c00000b440d80440a4589410b80c240c1d02c1107150b0904545140250355038900c4854039580a00035840c03242c04004aa614142c14000040e2646002d850031001c41c08a00300010032a034001e60440d10441d00041924600042c14500ba4040181c40c040104050141c0f0b10b41c03c10514058100d11041c40c00100b0404080d0300701841100d010b00018803140e88000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 783183525 1250 783182275 783182311
    0x5100507050d0e132a030b0d0308090111040b12010602010c12020904060509040b2d190e12040503070b19110c0a14030d08071209031e02070614030c030f 67
    0x2c0588034050a480ca03020030511300100c4031482480504500c5100c17800c0c1030501192202542d21018001c0b9520b5040c1800803083d21400744250040042d0010030031030450014001c16809080c50140c01d440100050701e25261b070302e505040742a602400c00980204040d442004034014194002e0301070312602420006c1d9059a80c000103800e41415141510120300311024044100d00500c118016030300e90440e40c00b6a001d00842d83c003600c80e070090442140c45000358401c1c86003900b5400401c040705802d01140c10301d140e041d48039040b0b503100348120ba02c00d100d84040002d5021840d400c1e240c030300780c4800356a011545924016180103508264880a9000d080e041c031841e65a01c07104540540980070840482e26459000d240c60403400341100d1003800612420000c600b6802800b1709844c2c51014800b04040d2002c2c40c041d40d80842c0c1050b0b80e4a690b20019400421030b50000c0d41d0402c1b036180d0ba03150710755548142441c01091100b52450150000100f002402e0081404a030a400c9030640c900b8190841c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 783184775 1250 783183525 783183559
    0xf0d0c0f0203100633081f1511060402060d0c051b01060f08060907140102030702040912090b04030807030e0d1b061206140f060c0d0905100507050d0e 66
    0x19025a292400a66541c0001d1224401d5491074440001c00c40c14202403105030b145035001e0484805805101b00070b10200081c004902001800b1060036800440443c80c0d51140c044598105001c0c2d070802c0007a02c004200889070030f00260b020b00843d00030304140d04d0f05401040e88000790a1200324002881010008100c0b10790001140000500740701000103105070800340060307000f04c1c0c2940100d44503404401408a00100804c20030211900c041004804003003080050341540075800c00654403d01d405299014041085e0500000314091f50714101e81d40e850700401c407407038050f600003d810b224041c0a0f5500090280842130700b030040081c80d2060488060392800031501c0e4118100b090003141c410200301403a00b000309111005800001840302908250000c540030482254481c0700784040d5550039101c0d1144001c4070700e40c824400954904004903d405800303500d0501c2902e015070428139803100402d10960a0301c0406501c03201400c000941054101c80f00d401c0100d0f0076078020104541c1d610b0794 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 783186025 1250 783184775 783184783
    0x2f130b03120a0e0a03031e0e0618031216080d0f0906092d020103020d0905191106070c05220213030c080f0606090703091e140f0d0c0f0203 61
    0x20036400300d00300b0358410040c080104441400071803a4040d90030321400b800000d4215044a5080300e032825025050404548210703a400b115040180d0130060000c4d8003400362800032245581854250304417120800105401ca003188078090203103028580c0201410005507030400100003000204bc400b040403076140c400c0004964900c007003140e040da070704c84122003000203140920790300384c140c2110030f204d044120b40c92501030140c4071002410517500045c3c0206030344140e0310070860203400c4400c88203201e414914400100d80401c40c1034400383e5444903120400d203020011103c0c0107a020241c00c00c10ba00d0a01070190300240d9000304400410954640290482e5900c054041da10482d401240b00318510705161036510700a400484440c1c00400100c0c10345040043d84542000c4180c07080780165549001c200c00608208500900038a910082610f100c541c1c0081e00941c00e00810300042100ca01081181d9100c0f030031480c1d6407854100040951184d070056041254142c0030b01c0e0b042d02c0340b16040d40042d00f4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 783187275 1250 783186025 783186043
    0x40305032419080115050a0501030b03190b090f0a030c0b091e1b041103010b131505040504050f1510030e06190c020607020a0206030a140406092f130b03 67
    0x341a0b400c030411141d50b003409200c0e242c03072002e0030400000f0708001c08104079207203178010a410301d030311035005010b02e8504101c018a40344881d403000c607904c000c525081c04450800d5620048510620b2100d01c8030103000303c6da07510700c140d15456100042c0c040f6954900c4105008240700f80c00c0c0038080344512460300070810700c2d0a0481090190803e03242c00741c131002800241c8489a07014626108810500c071001d4000c40b030541c0c900d00217840d1195019841e08284001c642c00c1711152812185e0003031365503a00a0003520070765100316020f02c010303504c3c4a02c405444004440c0c0961f0410340c40444501410001302c94400101a4500403c1c1c0d42807c4506130714040040e6075403440c01c0d1100c03084460194203841038011141a0307201500d01d500388032000a585103400750000c0d00c68a00000031074100806544000594a0144e940c00c1c101d02e0701d030030080d005000d28002507035100c20a0034541060301c5141c0382d2642d01c0802034030505403650070307038207220f4003d08a0007502c241680d12400a401c40d50b08002c9820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 783188525 1250 783187275 783187309
    0x60603172b0e1903020615012c030706180e09060a09030201152306030907060806190602100b090720030d0608030403200112150902040902041d0403050324 68
    0xb1920018130f0001e03d018030080c420941d007909900500c1c0142c2e032180d00815010008101e20304051081d61a07400484c00b03030b50703070380d0303851301c502d010004030180c1100c040c010117140218420810350b80c0b80692024040b0445030a909900800300007002e42d613099100200c5613020348000600e01c031550302c0601200344181c000f21070304103180300c0d1382d15050301a04003803130103c209a07055803c40c142840c02c19912961805070304180f01d00c100008035561200d03001c965200190201c1c2c01d00b071300c0e69960003070740310400300344040351045c02e22455842606041902a01800302d81c2c5e41e9111401c081098013414503206010410316020401410300030414a01840c00640300350806103a60b14910b280c03001c0c2c1c04d0000522070140e81b2940080d502c1513038109903020300e45a0400c50210365040cbca0b041da078003c00f403d504488030580c4041004034180019901a20036944410100f940c030000b42d840c0c4a41c040e10440b00103001074000c10009211004411249001942c09004481405000310005a4201380460300344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 783189775 1250 783188525 783188563
    0xe01020903010f09030c0b0c0f0706050a0f0c0e040c0c050a050d11011a090403020109050f06070f050309030f0c0319050310090e0607110c030a060603172b0e 69
    0x40324a180c28403031481d4a00e00c1c0e02003081001d030315030f03406030410b50300c50005046404141d0003d2041c89100c1c08541e00b00341660a07541e51f03040e25203014002400b0640c4c001540a2030260400d000030000d100358911071063b0b45540c9035480400003041301420b0020308280804c80c0d01140040056001c01c4a085031a00c01c00c0074110a0140f10703001480c081c0352918071221a81002e5280c42e80100c4140c2d0030301035800035910a89159280c0c1400d9000d440342580040051041c500001c440110100300c06010707000c01d0380c44420203005c10130102c0c2ca80c001a14030810540040140050405048c8000c05001d1100310940313003080074400c1c0b00b42a50b2070405040001c22000800c100903218419089001f8200d6110200010700f292880c10b9900c0d08000c28410038041d6040403005200d03810407114040c0c8000030111007042c1002c2c500140584a5403208840f19190f1703c103ca110311650b6001d03540c651b880400d0b074001c1040703001c00401c001d210301c2d082040d800d41e8a10310500704d000c0134006440c860369459114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 783191025 1250 783189775 783189787
    0x12020c210d0b0105071a15030a0501050402011e05030c180a0b04050112020a020a11030f0f16080106060c08070f080708071a060d020103050612061801182d060e0102 72
    0x30000b91001c0450309410400c08100ca040021401078400104442040c000c50941e030782d4400d1004100c0241400c0c603403501c0390b0700790441081015040944114402c2c1c1c1c1e24200c0d401c0114a080c41c1406200b8002d0124209000150b46018020060240078000100005181072410302150b05904290482c04d41c0090000c0c061009581144200504079040c0200718600602e0310310003900c03211882070040c1070712051000c1011136941003080e90201c10080d01a181056440306895542c0c81c890103206030ba000c04400002141c1d00c040c82410101d440a48407064071010b90758580381c0603440f84000b250321040c215080b5010070144c03070142509501c40c0780707015a10a02c60804844003d00c0d5201c00288002a008101c50368070f03039031003101100d0341c20308021602d910341380c00103038200442180a0301c95105c0c030790410009c4c0c2d200344042107580350100004c120a4408004013000f52445c241c014103ca05107525a110081519842a1160080740e118140c00c11540e034950060760341042c900c1d0301580d004984c3c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 783192275 1250 783191025 783191047
    0xc16021f0807090b090906010c030905030712050c04052712030a0b2107090f020d090b060901241d040e0304051801030f02040e120c0604200112020c21 66
    0xc4000d49080ca81c101d0a0445c000c00044210b58010400350400034004002801c140c081ca50a10103440024145d8422544401701541d01a00c1d504c0256468415051549c40c0c030f09092003214003906004149034036540290801d10380b01e45000c60405e80f203101d2011500400f0505401550051070001c0d400708241d40305030100429425010582006080010120f14075114002400c100b101c007242000310b120b0ce02c8000e082e0080c0545801c0c5c40c862400d14080d0b804100c549607485100764401c884141080e602e0324003880100c1030b810f85000c510034410348803031a001d0141d540c04181c200801800700b20f01106c18003103425210300400907400b552000c0b50900bc07074030b03203c46400e400708001d1603c004158515141c10390344482084010f800f0720b60307074560b1101030342062014540c00680c85510030f03560205240000c0ea2080f00715410303540301d4a405c2d10942510340003044021807090580d01c2e203042504610034403000b03620403000744449224004c00311030410140e80618100342990041e2544440503801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 783193525 1250 783192275 783192287
    0xa0c0c0303172d060a0e04050c12030c1b0f030f070f15081902040b070b01030c0501030218010e030c18010f0501050c190c0e090a050d0302030c16021f0807 68
    0x70030001104110703d00115410b0035030000700400114405004240e480b40c07000b03c1ca03042e1054100c41610040f0750200018040006800395201c101914002e06140d003052003a600c9000e1507a0020040d00505002c00c1030010400030900503000c02016180d1706100100080e00c0c0c94600c1c150200306420500080100c03110222040b0000e110803a43c403002500d600b0310044c4000030003001c08882c5003c83c032320f5020501d8241e0685d4040c0500313040141d502c2940381004212000c003484201c03100c0c000f1340000b01c0c8551181c001e0341d4085208103500c0252004a030b005545c0c501002803065050f02c1108859001a40c0340364500c4204d00100c10303100803950604800e281000300540180d13042c80310401412041150025420700c0c0a00700b50b10705132558146140120b034102d181d45c806245004542c0a001082e1000b180700303048580300d042181c0310340300001410b500740d00007290708150018061105810b40c954591845400b075100400392443c0c0c80c4181c01038000d00306800f52032000594030380c003040b000d15003005e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 783194775 1250 783193525 783193531
    0x3060c020f16060c051c02072c040b06030a1718042c030f0d1a0d020f060f0708030a060602070f0510050d0b0a0305210313080a0c0c030317 61
    0xc0140062190070300650030042c1c1684a0711080000280c14001801410304c01c1c070507005842100311a4207280d46030300a40d111550300681c404808100c0d4505000f03c0a111203180c0c07030b0701980300b88900c2ea031551107000c0c4402004200c50b40601504103c6000980c1d95a03015004a02039000152115428001210003a51142c1c030315010340d16120000040b04401103000b046c24256405c850340401200f1801421401010701a40300f90380b02088914109910f41c00c9000c00089280d9080180c1040c401041841850580c01035009038410f400075003e824010010300300d900540b502140307400340e03556901810340e00444007070258680c2daa20a00c94a0741c10b014506c0244281e040c5941c52600748000904c3c4c8454401c10030043c03100004903c040c491654104280d002401090b42e15541e0350703410800c0e240c20340d03280c0301c0c03c1c441c0c854401090350b82880001d4a0081c03002d0411284030040c965280103442d0300075540c0d0020712000c1d6450b03a0001d400355404c500034610070369a10310007004e9401c00641e034800103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 783196025 1250 783194775 783194803
    0x120b030309130507020a0b070507020112180213020f0d020405040b060a2c09040507082a04020c070509010902040305070626060a0f09020322030c260403060c02 70
    0x810160140b661000c40940c290742c1c001100060fa902c42c0309041e03150a40040c4001c1c112404082000502c0341c0010103045010b00070389580d0303079050604034028115200040301c640c40c01e81002e076940250900c171400500840c030700c01005140c580806041c0031280c01041c41c00300c01d2500020140b20500f45802540940d40080e03842d0380c1411a040344c0586840c04070080d00d4069a40c0b1020030004a20820201d0460000a400c2c07901c80e04040c20003984403070707607030280c00d00c1c501c034030081603020f5606201c84109410040601e40b07001180903003000080c0d80310841001d1684249800403e00d82da43d84400c1e8000c041074030006a40310700d076241040c203089071644010240020000710b0b5985154805480d0020301c41d40c20803403401d945400000780840703210f03004541c44000110003c07440120981c021802840034054034500b45241586191551400c1d01e030060000700740e5407200d070014450b44905130301ea0402c00250342200d81899112505d50b04aa4030540d00e140d1221910b110080d0140b1240d1a07403003803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 783197275 1250 783196025 783196027
    0x609060320010203043b270703080d1401080f120909060607020114161709100f030e0a0309050405071706060c030706020712082401050702030102070210120b0303 71
    0x10900041c0d1240a64401c0c401c00300c400150009844030307040c0e0b0215075030b50560726002d080120b50900380301848003103414091007047e4510414100100380300e0343ea2640015070043c0f10050444d5075415142c1c00c11040f6170752084e140d907201c540b50600c40740018040d244038030052154000d0341d200c0d60314140e08041c0450310100304001259541d2100802d80e507221009484580d510110b80c801221041510f641c20807070b41201154042041180c4580c01d10756a00440c8046091085109510700300d1150000c2d01d0390105016100450743c900403440e1740c0886082e410005100c8010454641c02c0455102d022000035440140c00d00c058600b9200d01c0d03821403414035004222100d8403404842907080604500d104150100d00c160004000301b08075140c55a01c02000d5441d16410b190202e0040d940209140104041500068020b0110714076410070800100740b62001754080401034405501c02d4034142e030195002c01c002d0016032030b4036016802e2050a651001c05603a01103620200312400581c641d0b00c2900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 783198525 1250 783197275 783197333
    0x1e0507050c0d1b03030b1206040305090429010318050d0512092a0f150702091b03040b060a23010306060f14091804030203030103050d030b0d140f0106090603 69
    0x841c0821505803243c4c181800607610300180d0001c0c1020361400b00340c0e83c0f1441a02c013000205039001c8007401d500c080c1581c00748902807100c400050001c0400d40e603250b05214410580380b46604c290414054a408407080310360003411070716141d090115080c90000400e20005840302400c2c1070070768056108030804041c00b201e05020400c900744064158425001400510840b106655201103018174108000c09401050100032040c0c0c6164004003002c3e0f110b080b5107000940001700b200e4a0002d0314002d82541d5146a840c0c1d80c030726041c0c010281440e6004030300d40c40c02140a469a44255803141c0b07005103440d402807034034400101603c6907600103c080184070b007551031005401c04041d0f1041d034604d00c40203454095440c08120040a143c0511000307429600900080c0340d0048000d42c10f0b0390048041c0c8005c01407249050f010380d0003110074a9005034801d007206020483c0c0b00f040441d0a2034003402e031000810648a490300390740f09504407040d169590602041040707802c4070895040c08030141a1002e250b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 783199775 1250 783198525 783198557
    0x92101020702010914011e11010c11070e0f16090b030a050603010e07080d05032a040312030212010e0414060711060109090b0f070215010308120a0509101e0507050c0d 73
    0x350f51003414001c2c016075100c1d140c90240503008c0341c1040700311075008000e224184400100000917454417200b150140c0f904c0490081400b100c481d109036181418140961201c20444803598100d54100301001000e440100310955000001c5018401c0102c0201d030f1420300904050071a00010741800655101c2030040003a00300108008100e0849810850340300d035203c04169042c0b0011030340201d03804c0d480d80c0c54a0020b0f03034214043e0054074050b050181d822203082130182c00700e2244400c8200400c503ca001002152000100164003a00c80c90041c0c48410402c0801440c0000580307641d004034010107400e0b0f400c1001000040e00408a05800340003254054031411000c0710007401444903a401400000c1a40380200100802c02e00d041205004641e900d0820b440950020407103041c44030700950200f00d9051040c01150b0181c0c5101000c0d02d4a0701000f0b802d00010120454100d02d2480903010006440020340b081e1440380751036840e420f9651403140c01007410480744451102c103105041e01410000e17 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 783201025 1250 783199775 783199787
    0xc0a180609060f0816050114130807030c0f0e070c0f020f040e010b03011a102a030e0f060a020c060a0309060e010b04140f01062105150a0b07050a0809210102070201091401 75
    0x801e162085080d27a460115180c42482c1031181c220001d9882440000030400c050040c0c1c030000c40b041580400c60741038840d000c40780c25401c291041d20002c0c180032407840100d2403200015001130300c01442c040010081c0004501660300c1103050fa80301e03075524910088a404c080c083e20b100c1c41200c1d109414800d04500003d03d8414041780014108070400880700c603403207541d0713007a8090256a4542e0f0300300c0d8a0a440e0003041c3c01a89680c40e40154209601402541014030036200c06103682e801a0014011420a00c505030b00007410309810192268424070200340948141c004042d074540010545206100a20069070b84003101140705a00c100304003e59020b07069980d81c1521800d10b444102c805031201c20145450402144107035951501c410301a00d9809600b44092084080d202048501d94406100760309008500d0041c140f504031401c09000a40c9140080000400c024101d000302816140030b02840640180300d105280c5d40019001c0c155070b00100c007140204031114818460b614080d000030b01e8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 783202275 1250 783201025 783201047
    0x22e0f080a11040923090607090f150f1206080f01060f03120503091204060e1203190e131103180601030206040902090406090513140c0a180609060f08160501 69
    0x90b612038121640c10b2009000350701c000d2031743e80001d04508040580700e440300b8080d28654041042807800007951030003d001441218011010002070f02c500a40c10303a03d08540302c00301c200300400b2030070007520501da41c0316000182064200500625614040550845c0c0c0701e60040040f218040340c0070000200d015641b03411002c0249070071516602d645480900e4038840d8614500d404c90080b07004100907134840030f084041c076011210720a2107100752941039203910500510309201c41c03008000402d014000c1903001e207245400703440381c10162052100380301140c6072211840110403000042c082840310b82c00b50446d0041598000e494194510b50001d80039120b02e2103044040c2d1b0700402c2d000a030b9a5a94801d80040c001c10a00744050f2516281c0e5004030740e0191811940f9420b065601128040c00007034108101c44003070250071242e402d00c1d81505049041101c80f01e080381d00c81401183c60300d2103000311001056071107500c403182814510b481d4244001020802c0a22407290810012a07074010b2801c12 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 783203525 1250 783202275 783202289
    0xb091f0e0c040905090f12130b04180c08091903200319020f03091c05010c050307030e03121f08070f051201140705090a121406090613022e0f080a1104 66
    0x10355981ea11162254000e1554480740c0142700100d40000c904000200c0c1d000b01030380d402010848000d4910b003e864044090b50030340880c1c0c1c00794a9041240c040000c90054460007420414126003140b01c50403a80880380c001e1a4654001190f4000c150100d80c02140f452801c4c0c0c000345c031408840d843c1656485c012030080701c0c814440100c400d00e004090000388031545400100a110440c02c5220240041d4015102003001070701e01401c0e03110b403481c044182c0e9210051200040600c0d15520480d4006002d45000103501e25299400020103040402c50403001703294082142d84039510b04000c1003103a0300b0310004050180d05211104804058010045034060054100551241c42007030100c1d0366484035810844400c40503461540c213000c152410090490151011100c0d81d9a0f400c0c0c1082d1140b03803d8801003c11550403010324014603068507220941c48510000c6500c0d245501c52828605020780b0032807000c510b0004c000c15029900c600380f85c1c0d22610b545802d001e2540700d05c032a40118425071181c0a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 783204775 1250 783203525 783203527
    0x204060f051e13080a050c09010609080a0206030a020c0d111c1e0e0301020c0c09012c090a0f1505010b041a13080307081c0b091f0e0c040905090f12 65
    0xf014190103c00040d0140c00d050085070131400d00703440d2680d0b40d814001e00f02032140700b1a0000050303c91207001400c05441c802c0002d01440201c6909012890704041c00d819010f580078030100c1510f035410041e100b007501c015528411918032508495003000880044a03044070041410703e080f0f1508052443d00c03091501c540142d188400a00c00c07183c888000340300303681c0340d400012044400b00b80001e58a214000448803134950342d0740c032800320010300103400381c00d9440c04d440a040000041e40b50801d651100052040e1a101c500e1a41c03906e40c900d5030500c0455038607140c2c44140305041c01c03c1c440d803402740444c8000140740c6801c145000030041c603135480340d0001d0f40000400c500040e0319107920100070240141142d03165030031880c0030107440d0800c070422240700c2031312220081150800d01030b06080480140c80082c00380c8072076039101a403224031000502110038207800080d09000103d44544189140c0e034819880f1428082d5210a4400c00f0304a0195640003a9144210f440c0204444140b052130040e02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 783206025 1250 783204775 783204787
    0x8150607120c17090f0a030f0f0602040504110c06060d0308011802070b01060201200702011409040e1b030c030105011d0405150a060321080c03100302090405010204060f051e 76
    0x12150780300c2d042001021510002c006250034000000541183c1800b1986515007848217001d024050303070240b10182001e8454418403011803005018104170601841c8054605500c0e200820144c030100d442080340c403480020160005036080c8101a0440d82c01c031440b1401a80030703100203107d104103005607001c86007143c402222180580e4103d40103030b41e00c01030000c415a507902d006402403010511181c810310904003200c01d1406035200b1038841540c16102c00c15080b4962030b00385410380047c14925006a5542c40000303003014100400c20390b181d16407405140268110040c181040340b06010346000e030381010014801007120708803c174907458041c0004006e0b0340c1c4604040b80b42c00c10540010541910a2003401401707400b0342c10980c20340e80548000c036202c60303005404070300c0300e030625001d20b00207030151000c151050110700045070048e2030f4607a115030141d01c0380c00103881c000b021b650445841e035001404100c0e00d60014138072802003115050241c100013042d8020058210090000c1214132000584 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 783207275 1250 783206025 783206027
    0x2100c0b011a091e030706020703031d010306030218070e0d031e020c0a0b0304170a0806150913060503120304150c020a0b090a0c05030f0723060c0d0815060712 70
    0xd4450303001005000742c40681d2440852034107078113180c040d14000c0c05080d20101c0c071140001075078421254940e8443d442550150301000c58544014121410140c07608800400f42c1c0d00d941c6c0101c1a009400b01d1070815040078040900007001040845004020200701c0e2004a90843c100c003540001c0c0103420030541100440032800c0c2248540c059a03c02078402c40894807158060243d03100354031a660000e51101a0541d502d000d0041c2d9100e0300000d03031141c0000c0c50b123041c8550710351214180b01e54841c0c14400700303000144290010343e50b214210b40c0e403000104500c6c0380c1009a081c4070b50320204d6440c5941826190125200e594203001030100d9214544003c0041c82000311002250700030300b0030911810310342c601c56210142210107580781c0d0004c01d804500d910b8082004212603902c40d00800c80d140c909a0b903800c175818980504558002c03040541c02035900c58a0003001c2129100000c0c0440040340c25000d8a410800b41040981c06041c20114519403985401c4a08154000070650780701190900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 783208525 1250 783207275 783207277
    0x70c03060606090e0c04051f032a02070e09251208030405011505060a0c05100908120a05070806210d02030a0e010c0c0b0901090803041202100c0b011a 66
    0x88010412450140c0006141d6030041d030035402e07036201d028010090707100d2a6400e0038078003e41c02003990202c056001c80585000043c00c80050030001e040c080380b4800740d035901c02662540c1264042030302407520400d1000036414801d081c05032240f00c000c603429046c03503e2010303541d00185580c044182c0c4415010000a0080741e5010700030070301034800660f03005032864001d0b016082a94216181c1d824801905040c031740c001c0c4000705882c0003400c180c1c1407000c501d2080f28880c8000406a407603001c1c0c01c1c00d10004040d81d00800311580d01403440140e43c1d003240b16410309610001000c0280c11450071052104455218a10940204003200d5009480700300c2d24241804103407901510440c3d00ca003101407803400340c001c4003a0007402040d0300c0e09102c840804005640103041c103440140040040e03030040c081c03c50100e0140640c0d80b0185040780f00503841b145041d01e10f038401d400c0342e02c1000880c0e41d03240031032420440c200003411035842d2070703d920009580c4150030880e040c010100c0d02c5500400d05500000030708 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 783209775 1250 783208525 783208529
    0x1030e0318061c0c030b090702120a0c05070308040e010602120a1d0d1a0c16020405090a0209070302070b13150c0203130f1410081501020a020d14012a0302070c 70
    0x2d0114049500d940143c2c10003040009003503408a420008040c289141c03001c0d416100c0c4805030064034480c2000008020154801030301031080c008502d0f0200c001c51010011340010714454072000c0d640342d00300154142c200c00143d01010855208810a600100d040400c3d101d10031542d0410a640522003110041781c0e0001c2903185420200d00b044010500c811404410308405440280520948503022900d10328400e41d000101012590302020006041560010358040d00342d00503507101d01036943c002080702109840d1440003d4000ca000d0041c0001c1681c3d5640044043d03540340e1200b4144e0b9600492404110458124295519182d50209000740201c0b69208040d03040b680c1299101c00484220a00c580500c8402405085411600c0d0410310110b1340ca4060030b45541d0010341c0c8440024002c2d13a510344030507046002d45128603006072280d0994243c81c902c41c08a03040c0726583c1101c42800c49244600182d01020b50814205a00b03240c61740301c403888981c515002d40e4502443c01c1810f603800080e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 783211025 1250 783209775 783209797
    0x1e150703060306050c0912030f1c0f02030103120206010509011203120b03190c0803090a03151425020c060415020f0a080901180518040501091b080c01030e031806 71
    0x80343c100f10124501e18010641260f04940b0740180056444c440c5580e030003200e1844051113400c01040c125641e0ac48a1451081d20039070b0049100c07144032414005a03002a84112040b00185014ad103c080d01448464007620707050701c00e20380c95854600130148503011500090140107001002c241901403079000741d00343d940c01030202c1d604140c2c202ca07a0090f80e10011001d860714002000d010400789004001c40722018002805083d081e400d54a42203d1505d2584041d05031551340c0380d6641007007442d40e0b00c5510038140b01541d0401c80312002d6114080d2501100e1035011074000101003002552403000343e90588ee14140c07a06d0300107c4101c8180c0c6064083c102c01070b424410003803120104000140200011402aa18100c0d0b00f408406002d001458a00815900c403000001100c0c4038041080821340c058003031000420744890035181c3c20411550742da140a2003149400c002c2c04040010014050706500a180070000a1b05039560f8513124010340304d014042d1100c24403052402d580341d000b5591000c0349 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 783212275 1250 783211025 783211031
    0x20105130b0903010c0201140a0e0712150501060c0f260d090507050a08122b20120105090c0c0d080621190314040305010902031e150703060306 63
    0x300c120418081e08002e64451082d8209000703401610b10601071690351052a4103007800c9525140f01e408090a89940003004500c03605000051801d5880c4089030f043d0700888010110095a2202d0b5055540c140c010320b0910020038a120002101c1c0d5000c4a16603820101580d18954030307110341003900321100004008884081109c018950080d172014010501c95411124019940c0c41031000b90340b0309118608843d00500b034181c02c0950010010710355841140541c00c1d00011070700050b004011411404055107907102500c2c12011140140702d084410049141070402400070b0b0441509801400740d54050705034034005c240a20100c0c02580d00c0f280c004400d070f46510300b2000300107001e0841211054892404aa0001003c0000e51103070100f1285580151082c00b2004200300342940340118200c04020324844029416a511805800918491000072681c40f20600403d0325140c0301000b2042c01200900143e1030b0000c0008a0204151a000710008070f070740c410b00241c00401d160380c4050300c0d84d82 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 783213525 1250 783212275 783212279
    0x5010305010b1812121b07060c060f060e0108100e0c0a03020607060b210106140d24020408010e120903150a0b040c2a08030a0902150a08040311031305040902010513 72
    0x201a0780941060110f4001b01269590000e00c055611400b600c00c42d400b2660282500307020801a8000205001003000d0104000e6070750b004501c481182640155141d41100c48890b804121600036001900c0b480310051141e006c0d01c00000d01c4e0b0101900c0000c1c030658001650004011040e00400401400140805101e0140b95a1650044120981c0600652a009011881c040040f00c5480c281070003404541d26441d0310f58034440128421101081c1e8031030300e02180c065440c44c0c0d00042026204000c00460311008443c030052a0548104040541e07401c107114650558400165091252141c603808d08941d89607040110000e1250752092a040340c1041c110b400c03c0c40d00900101c1503217111192416581250070490300501b1180840280001e40c1080410903490460300010500b90000300640e4680c12043c00c0c2000b0707940407020b10300c042450343c000c1209068009885040c019000320203546001d400c04207a003d40e500314020703544550354954800082d64810350036039444d02481408100750035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 783214775 1250 783213525 783213553
    0xf060f0a030c0b130602153d0f050f0f010c0807080403081b19120e190501080903070f061503060c091502150411010c080f03090705010305010b1812 65
    0x1c4e000c0c601103011080895400100c0c64800180010b000e040d9421424060b00d071002d4200004016803080240d28500b4040d02d21100c0440318000e00b078100607580c0b491414907200c100d21a0180f180e01440c86450488c1c00d000380c0351210310700c00c2040f5800b4030700b80d00d46002502d05100c1c0d0303016032075001e018040081000700411a24500074290365095180b0109200c600c101e0013a03903003c2c44800003c00c141c08590250008510b111003054840746410301d21103040e1030b00042101581e103000203150b25641080100135a50300035a501d0341008001000c0c514180303258813400312422a03658001c01860f030313810250030081007054000b8042c640c800010301a46114070f80003003e000c0c4134040e15a082031520881c90f541400010042c01611101e000000590746a0b100e00c20030040340306080e0b06101580e0712030070010340880020507200c2c548110031074490400ca21000d2070001039401c4107040c1850000117025540843c0266213000841442000b0b800c103640011810074509011100660300c2100144100c0d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 783216025 1250 783214775 783214777
    0x408030714120f0d05071b05070e150120031605030a201b1207121401060e01050d05010e01050c070629100504030b0711010c02060f060f0a030c0b 64
    0x8480307010112012075a510380410014032440c605681040d004021030b0440c4c071901d4002c60750100e102d051145041078040124a02515000000c41c0d182c1c122010502401002005050b0803050a0b540301d581d55500500107003000d03030009124820200d902410110401040007203510040695040d0400c110311803802c1d40d03580d000801c2c2c034004a02c14140d08400c1e1100c0705858601901c02500600100e4829100301003601d00103001c2540207030703045004040c0c00004000c13030001040d11048411013845c440c201405c00c1e01405108525a07414030104100c03403101e0990060540c0c1080342e1206102000b45040750060459021608480d42054100002d08114201070042940110b01c2030195140a9510100c09a00c006550b9451508000074030b42c80e040c40c002c83c6000300c103a4104a45025240d45500041503c1151801c001844504141105110038024005000d60307a000030055030514001c24400160002c1c640340c020040114050041d5985544500c01103811140134014140c51b90054031203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 783217275 1250 783216025 783216053
    0x809012703080604050903090121060b0a080f0f010e070e1e03071e0b0304170d0504060f0905070506030604110408060106020106050604030c09020f27010e0307120f050304080307 78
    0xc0750b92030000584504042c0103030703441502140c02071440d203064007005460000078413480381d0340d2082c2e8441f10340d003402840c1700f444003a0006403891903c0c0c1005a02c000c1007a000242003401300070382c841c01e0005c000036148484d0705403982551000400d40e03403400d049400800303021009a1250240314580b081007103d80e2104884071054064410403615110350544554020035036500c0c060300d0642c20004680700d1009582c10500c603540e1662000b14070560306485401185d120740c24243d4420500042120131f00c2140120b1411101c14880007001d074445584a680e2446402c6c000c44002000548541c2d0b0355000000c207419102d0b1044e22151140d070215503074175090040002562800b03a020a40c2d01d0b020080e2812240e2202e1041011420018030700060340003805501a40761051004520022148035607600500c01d41c102d106010a41800051a4540c59054a800798100d0780003031012001762101c030320f06503810142075500e4088501d41903181d4416588000c002e40000714031002000842e40301021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 783218525 1250 783217275 783217277
    0xc0613110d0f080a1e05070507150201090c0b09091518040809031b030712120f351503030a0305190504051f050f01060c0f1e050f01090f02010809012703 67
    0x1664a58540948031b61043d40c0e8054283d51050004200c05d0485204080d010300035440049845989075890250901407500941d0780c1e05800b054070100350a221480c40d80c0145007815500401c0d081c840440c40e2011084000c1100014007000103041c09070310782c2140d00101d005412552144051601800c414181418442c828040e0300c20005d102d6850300f00030200950811940f18480300034110503100340544454180c01c1c042c1c906000114401c014400b07140d810b51941e18240030400c0c0050110407008010006040d041c104400401d083d2400000c1ea1000012070800013015200e46030440c1925401c0c401c042e1041e0305207010481000404140d4900c80000010000d00041104500c54185c80044400d400d000c100e00b0010031910f48950707480700c003103400358281150f40e15080d1030341401040902040708411768801e829008000c000c0000303c2034950004000c0060b00501c0d9669005a110420040e040000e014041540090294010001072a44900c507081e88400d5603132014842c0c076400d500394 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 783219775 1250 783218525 783218567
    0x30c020a0b07020306060f0a050d030e0301110c0f0a0308070c031b03020a031b030e0906040f1b020f01060302090c0c100e1c18030b1009020706020c0613110d0f080a 72
    0x4440c7d040403c1c128802c036030024445c51595050030305008a014002d0419020064003c4420034191402c2c8220100070220b4011540e40701c0710f1200140c504400b038540c140c00380c1d01031852071000c00d5100c2c003900d40044181c03500301e00402c11424101c07100e040078030040c1d0104180502030b204058002032901001c9100b0b4032091401002118000e80030030f9204005400706d00240042c80640c0f038020281640000e00400015103070744c411a80c44120341004c0303070403510540a0164140155010840031075490700c800001d01000341140c0c085000c0d480d001e0424524081c001c510152501c109201c41c401040c1c640004106000f400c2e000e0030742c2e94029041e190841040c1203005080507101e0500540036090034034203549024030315980c8241d00f8030000d0001514011183c00407803100301d14001429800d00070794015071195900c04400f410904050310200301e4603c1c825400300002c0c1e40405c540302d034641c02c44144c5011081810b144074103080b020002000b050700003d000f00119003141c1202c4854500e99640 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 783221025 1250 783219775 783219781
    0xf0b0a0806041703040c03020d080d0e0606120718020703230405010305060a051807021603140105010602030a0923220501080c0f1e09071d0108060d0b04030c020a0b07020306 76
    0x50f0340e451100781c8020703000030907025050002d81002d64004406034030078200e180c6400c1100003140125400000c1c964800e4020800384183d520703141c516a01c00140a0014080340d91901400101d030400c40303286800915004100001410301400c100074400e089814100620180c1e11210325055006014503400310789014040341003411300a1288041d10406411028042040511810000070091a0000714407450382100c83c600c294589140065205400f00409944051072480c29a01d05800c4141158018030004404070f0784813102204480c1d03a8076251490050b810400c6910408540d080b41d0090384002583c9090602d01c000e00c01d0600f4801d10400c00341e601e44a00700d4551004020b9154000341c0c41441420700e141980c0048088141c00c4440d0300d00341c6010000c030311a200708a8180c800310340d8888a096200007a403580d046001c00900c0d004041d0728009000440b651035141c4098240f02c0802c00180825025896a03000f40e0703001092606000c1e0340e41003854131503000d810124003900901c404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 783222275 1250 783221025 783221063
    0xe0c0717030f0a0b010507080304060e0d09061103161e06140402010f031e020f0d05070201090c0602060c0301180e0619060803030438040b010905090f0706030f0b0a080604 75
    0x154040c809016991b0324035140c10f5440301c91a940010700281c400b88e0342c0344509841d10404100c6411180c101d40c446080c000d1170551301400c607600b840c55041d00b0b40c0080000c81c0c001840141d0341714005601c4000e403c0040344480750f0300d11440c42450010603a6162045840703da100c03084405106034403d0343c441584400009044050f907525032440e6009006d00c15010a00305902c0e0068807007244440c200c0d5081110100f841010740f8410789806c00540d5490b5900001e0140c445424400f07003d1a00040246040c01c1a401820340301c144070300030341d4008402c01c44031200360a4124045d00d030f89942c1201e186051000074001c07174540107110820464074100340020840340210550b40f0994121100c03000310030241100784100d200c221603507504084200c802460242d483c0803d54091801401c0a0a1540c14440180110352016002c040c0b2588140364411f0010400100c400640300c0d03900d03002c01d901440143d00300180ca01910020b601951608c00858405400a845840b56028010b00c04000c07402c6a5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 783223525 1250 783222275 783222281
    0x207060b0f060a0e04110d0f0906150605033d26070b070317010909331a06040e090606040e0d0e03150a0209180606040e0c0717030f0a 59
    0x70000f0007046007224032104030320380f69104202c82c501c0140c44901d40350030500100c0c2210350000c8180d824035650803484061200034072400c0c1424002d140e120250034107001c0054441d0000807d40241100411070400341480c3d1401001410f5042c01104281005034000d0b0b007010980c00d01506a46e00080e64a0007aa892201d14410702d000c0c90390050310440e42003855003202e81d84113050507410310005001e5103017203006000d4858020484541e0004914655103007500c144181d8420741e000010390582c2110b0403447c41a03d4581156404500042402d0301d4070101c03600300b40d18809942e01800100300011080c0310851858807070340d0702c3c2d000c3eaa490f9941c030081200300d0b840091038220b02d074080c00c80b290307559000341c00c1492058001802c0f42c41030007003d0f450210f0030004541e06c10a564012441c0007180c100042003103002b101904d1304100798608003000c05e43c02e0146100e45c01035034cc24400031031140c000b040b00b00c1d41c01d02c1d0003501041490498490138203140d0301c1952604c0c0340441010000750801c11381c1c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 783224775 1250 783223525 783223537
    0x204091b0906140c0109080316171501030b181e0604110405121c091d0105011b03050403050a0b01170607080a0509100f061d06030a240207060b0f06 65
    0x61600d070410700e2a00701c0502c07580c0121604104c20342d80c540020f40400c0a4401031485041c40810b0320000c44c3e0507080041003143c001c28400400c2c00040d052201c05288402d4503080c0200c00c0c41c0001e82d00ba0f0040c00214503850b851040e40400c03801400380210740d280d004510307866294035240540540c840c1010321048580490707440605403410310044c800e0786400d41c07104440f44451030890f42203c030110074146c100220064490081180c88008001c0d10006500c014450500745000400c60340c5000c0c0064541409007412000c0e802041d100d4104041c01641924041d40e0403000326914068540341c5103801c00c0f000e004144845100741042200725000103095407158a070703030b80c600940e80c481d000000050b01c030292036800d25016507a0140c1607540b2521034105500e40c901000b180f054a001e140d400d000d04000101718030420303040100311881c0c40000d0340c020b41c90b900121a03a54022210310609820580114280c8580e00001d568018400305802c9404940b5040740d40080301700c01d80042101e144214 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 783226025 1250 783224775 783224777
    0x605210907050111160608060907031802040e01060b0d060816080c010c020f03191104020903070b0a0e0d060509011d060a20040303180501090602030304110a0302040204091b0906 78
    0xc50020b0180354443c0d1480840209603a04a44551040c4000c0c03c6151040d5040000042e520300204422072400400050f003100680c2401c0000f000390600f410310050b03010101034010b41c1c44540910b1a501c0952000c0b0080407021049a1505a5031070340c280a081c1d031f4840d1811510824540902c08021020442e0413103000000a000c580d104c0c00040d2000c140703192080e80d2042503074000c20300c0f03500d084c044074a00000105000341c4182103458410888420000a54003ea10500030f00c50103840c005440c1044d1541001420b48072a003203c0b0840d0310110900b02990401d00b808051000c000660300490300507980e08000740481c0101da00c50000d90f0040048030f808540c081c1c00803810714000355105030f2041ca01c81c041850042c1100c03c5c01c0800364043e50048001480c8200442300070460740c11140d01a003002d2030b002c4490740ca0290000c1d9280000381001c0c6c4481c3e0f00000032061543c500220380700070340c1c0c060000e544980c1e595514000a180c001345041003c80098184000c40d4410003162041d00c0303007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 783227275 1250 783226025 783226033
    0x91501050a0909060f020301351009150603050a0b0603061003020904021f0c050c0a03051218040c03020406030f090203030a110c0a0906031403040b0a050f1306052109 73
    0xe0001c07403002800c3c030003000307076a026980c0403030440c058800d000550207020034125060014000d48501c030042c5901405243d420000c00c05142403400006c01c2c00d82208000640116004100f4107008022024001007118000c0c540741000082090204080e84828095901c02c100c0b6610101419202c24044071060020303151410103000500d0456603843c1c01c0f034005880c00c070a441c0030b1072071061000c81d840b4000c1d01180e142d02c019400c0100403c500d542c130f08070030b44260034030074030316500c8940c0c03640240b01d0110114004944103060b18010171540c401410014810310911064002c098020b41c402d015420002e800d003800780700e0000c464000d8588042c0e0150055142c0b0f42c140341c00f02c8040c081508400d416000700342c4008080d0355010303084030162410f01800a038451851804440c01c0381c034250b0500854005010030410020804117488004945007001e55440358844541c2941c0d109040b0040c0308660804804120f40340d1080140100c06400408080084601c4030700b525100022605e11525501c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 783228525 1250 783227275 783227279
    0x20a030302161713080a1502071b0b0a1707020c1201090b0c1902190f0309080a03031d0f0303011401030e0d020a11060c0c01081f0905091501050a 64
    0x322a034014000200d031a982003803003165a58a40790214070710b198030748810070042001d060884400380c1400040040400400c01d200d055519003e285032200c2d0040803865001c69228107101c0741c114a142200080b2000c40e002c1e9896000032103854018001c040002a01c101c01011900042c1c03c8550050450350010f2034040040300810a00390074414000341039540b1002d08074005540c0405c0a8000d0394818112600c13a500807520140c0010044200c03821507105000703d06060401e140f8800c1c07615000120520a0030250034240c80a030f1056101c01c400b803145210000c18558540d220700410114009034000700303040700410903691030f8160a01c0c01290010401009501c0034504101815031040c140800e40c031a28400c00ea041c0301d40040c0b13550240e0000c2c001c0301e0812000011400700380c00d04942c014100211801030075a03d50004043c94184060000030840364505400c0c0c0b407081109040943e51107076114000040a8401a0340c4404075204420300a0410480c02440300d068035406424001014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 783229775 1250 783228525 783228527
    0xc06120f0a0c05120a11160213060605040e0604090f1407050f06040e0a0b0a0e0702012304021002010b03010c0f08090f0c100509150702010e0a061b0c050d050f10020901020a03 77
    0x801c0140117403036615590075414029581c42c074050495110310a81960310f00045005002036619070b0091441041d107086800c0c08045d41103400c0d50241c0c0d040b131070b91410550710b010224004140c4c1c00000740000807000c000c1c1040104040b4581251030b40d000540301050750320303014081002450107619034403890600003030000c51200c5403460760040701c203c0d02241c10014540480d0042c0700c41e4100d07a140510100400010a809010b040c0c464481c5e9a41c0c0350f181c5096000d01c072401000600000c0c07194517000e0444002d18801d4000d0810910024000c121010b0401c00260030040d07442200b20200b40f16400103030f806007002c81c0c2c50303100040380c0d4045d0041e91400d1040007030711b0001c0c55072401031040910285c421601c50480c0c200c03c1400c284d00d129503030513483c0005081e01800104440c810481d143e02440f0035580084000b00442c2c11100c00c002e40e80c1c0d81e1030480030030201a000075410865141019051000012381d0b0b5042200752029141c1002001801d44243e220b00c402042c05a400120000700003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 783231025 1250 783229775 783229807
    0xc0f01030207110a060302031828050114090105010f0803070b0714070807051608010c090e0a0216080702280b03070c050f0706020c06160803090c06120f0a0c05 70
    0xc02d03c5031580020100c03102001410340c4505070061700000c0d5003c0304206800800c400300301d1120a000c40180242014103100d88070b48150b024400920641c3d0040d10010800c00f508078102c1042c5c000000301d1a4944181c2e168000c000900c581a03910910510010384110302100712500706402c40c0b0400d4140c1c0e611801a604184664402c07440d51408228200100c0d9405000c0c02460740716602030701340c028070080004907554442e08060306592501c841c1403500d80d0454640811a00c40e4408003040e641c0340816400280a40092840c0a107404070158080008003070003002420301c02c49d181050920408900c120400b0021403c9d20005c03c131079000c1c45035207041c40145a1211592030700c1c5403100d01550744c0d242800d103440640315260f80840414007c0c0c0ba014400c04006010a45039103003444905034484c54401e40c2c4160260030010008003203038a0f0b035400d011345603a101d80545400d6032510181100303d540501124400c1070451860041082d008403401401b081e52400e81c0d410341010304506d0b058000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 783232275 1250 783231025 783231037
    0x16051e040905070b1306020c0108090a1211010906062d0311130e0d020601170c150408030705100b091b030619080a060f05010501080408070c0f090603140c0f010302 72
    0x1071485443c00001d03028500000410040e03c5982180752450714003c000b0b407415521807101c40c14841c21608001403c90002558564990004001d00c0001000d440a0324006a520080e406035420070080c002402003e4000a0490300300b4650388008405442141a0902c9591500c0d4102480028108003095420b1041840c0f000300501d1501a550070010074011511003010507041908090200d03403605406128403401000030301c0c507030305074a00142d020f10f446001d411841c40c803416403079203000f02d44001c0702d00340c074041c00d01d01045903035a030a207082040d6a800c45102c0b100c0200e0400040010504207080010702416444c0c4c10030a20b01c004c451404066000204204e80004414901c05014000c0091103401070846c03070301800c052030042c203000c400e580400c201e51544a052400400c06664010f0f903040d80030350815036aa032210807505d0080c0c9502601c3d80314512045070000049440c0085a1042003168814a203002e24551400ca280392a2000350a2170384c0e0013213880c85c5011b102d50194004240d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 783233525 1250 783232275 783232283
    0x1a0705040b071b030c0509130c17030f03040c0e070c030c0609060f090b01150905150304080705030301080c041a030d080a0b0d080c0105010f08030904020d06120516051e0409 76
    0x1a0f071400c0c00c0322900000ca154829600d40c284000100030b20304100480580204400306104000c00c0716031220f0030001914411103540c1022401c5101c040039040c400c1d00e0b040c4000c0c000d840da403414581800289142c0500801c44c01d560391401107080035005060701c60000386d040d00c0e400101080d50729018010070580b482910003a840e01078100ca4120644140061a44203d80a480a50408509040e18020007001c8030a00620000903c501e07130300c10461000c0640760300300b501c0c0d0340d07502d0b8a44442d0078060401d00400600c0088001b01c0e10034404a07000003141d0090b541004140c1c2e81c516102a208007010040d40c040c1c020040c14264a8410b8405940c41125500301041e01c2c0e841c240801c1c01504001c20903610050003040d0440070000038015a4014050a5440551281070580b125140d20a20b102d2921036980042e01000504140c3c0010000344034170310840c4045402810b00c1c54a40070002f00c1040d404250b0040820a454814880c0004045030043c48080000900c103110041400303c2c4103030307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 783234775 1250 783233525 783233543
    0x5070501050a1e03060510090305060c0c06010b031e011706060108192a0512010506040f09181703070809011509020913021c0c021f05060f19031a0705040b07 69
    0x106c3c003525521103039440041079a98910703003d8038506000d414040c010385100b01d0380380e04000c7c2410200c00000e070b00e0705407002c4840c40365a82d100c0c0b42148032041c18030380410241000d400d0000410b120a81a240a05840310041e503038580d40306001121b207214210380e52214012110301c460152020342d0700c561300d041030b000300100402940411820400c046c0720086c10009000080864000004984040c01000155241418182084030300c900c0344109014040c12645d40f0304003018045260400c00d50281c0d08503160b000b01504400c0a204580d004a8401000c0356201021848520381481011020411004445030550400b021400a03512a070b00841d4804102405181c601100d84000d2603030007001881c4000ba00c03596060b250582c0e04d0042800d041d900710400c8480014a01d001d22107000391101c80005060791440002101da8200821064019200d6208100310a031101c0c03140d000d0740c1c090142c001d0702003002c00e4a04c07030103e0110b030200700091060104220000010015051440c8030754025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 783236025 1250 783234775 783234779
    0x3060d0b18010f060501120e190807060c0806010e0d03021b0102030c030315180403020a020d0f2a09090206070201260c0a0806040b150309031c0905070501050a1e0306 73
    0x16609641c0d80302d8003401d04130ba4521003080590307085140d40c1d403c40030a02d400d00c00400c04500c41501e800049108282000c0003050715020071910900b1120540da120504010751145c00c10b0081071040e00700c5549022a102c55030014051804003101641243c4c07650050002400c0ac282903080311007483c0f08035041d444184520303626101e0a0010314860a501c000d0504010460380401903c803011045107070a640c040030502012960100308203441d5030301076821000c415154649810703145a000006466040c4009030b40100d02c506412420301c01002e400d80c00c0070b04d42c850414804039180b189009610920812901c001540034180803400140d003010841540404134030000880b81c0115201d681c81c000001e4040300d03280d00100090f0b000f030070a59040104421500c00b0600340380500c41c910781410f5010001940044017002101c2076001801c6a200285c09410141c0f8003038a40034030200d1320341c0522040841e040d482101a68110322659403210720110444c0c070038215000c1c02e424607004045d2140701c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 783237275 1250 783236025 783236071
    0x405010504020c07170a0b091b0109080714060409140f090706090e0a1b09060207060327060f1d01050f04020603150d0f14010615020a02190f08031c0203060d0b 70
    0x546205402442c06070181c0004071040c41568502720002a040c840e0301c40d41806444000201c130400d441e5121a8101541c07003800000d142c2d4040d9600c800001410300030b040e4805600308000340d000d030741c6d4a9840082c5484d0183c0113511100d4a0003814001000101c082000300c030224101500049008400600e42050b0a0294000620501d030040807460501c0100905a81040582c0042c07e1515080118610b100d04c201450000050b4048014055201c45800c0c01016800300340498160001000366030b010300100c0312950504000c015040d4a004001a421078035a55114800e540c010903079840e5070b49203013031000724162000700d183d00030440683d9200000c2c00d03400302e03a00789400390b85041814501084200d094444540107124010700f140c00c280c01d95500090420745955040320b0415115044012004e0b89100e65441701c040b108001000040080012000b003045031b03030303202205941e0700008458500380c3c842a660103400c60034101d4244041a01d0406240d04100076450760070307040c4203000d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 783238525 1250 783237275 783237293
    0x180b0d020306041202160e04032003040f09062102150c060a0e3a020f12190207120204020a1b050c0a290309030d020a020307020405010504020c07170a 66
    0x50071035200040c1c1813000c032566010419002101c4181881c00d984a0402009080408001d00000c003400409034004001085922010103c3e40d008070407607440715514129a01c490000d885144091454160b001c210303100b80141d2803907aa024007102343e4110900c0d60078040c0010840d03c6100d240c9030309005240d56200d00303201203030144280b50070128000c10b4401d8800d01b0000c2d400ca066070150080f00071a07108403851290001d00102101c2c00802a01c1d8809003a414000d803004c20500c1c60013807003070030910160b84070040c0040c81204146a0001e0f03454071403d0b80d03928140d01881013409505001c4a00510f01900200f007100d00903d002d250300c0d115080740310303600103204904840ca80c003d41c08860060915288030b10003407219010407641004400d548001c0720507480004440c0540000002d00091000c10450300c900818010441d034a40c0000c8009450b5003110300224401c1d0705103000028140b810f4020b40780d01c20b81c0c540140c4040d92400100ba20035951882321009035005a031420004070359802 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 783239775 1250 783238525 783238531
    0x121b0510140f09070b130504140a0c02122203020d03080a2007080c0a050307121202040302010e010c02040617062a030f07090302041b0e0109180b0d020306 68
    0xa8008510a0244650740d100c0c0c010041003001c54001120401c00940d4000502e00222010303944040c0d0356000c010019503001c0115040160891f0074002076071000607902110520038000700340108014800401c00701e031a501140500302425005106030009038515090000c0901c000e101d100244503560360102d04108045034003a0003040d10401000000c10b081d008003d12400e09005101d0003c1070524030040a026000000c0c003014400b00380c3e1642c1000c204990501d0a400c14100c07138550036146000030b0384103070381e000c001d000456450b410601104607000b903505603541611200184009040111800201d03480f059074481d80398803000861840580f603010a6110400141c500740c6420840380002084100c0705202500c03008605000007807500c0d050305d0b048410041d10400b15241c0d010f0403610074400f83c102a510503d0410069070f08112003a489844800342d0b1184200d01d009070380103640b0b4080701c1c42084040f1401511901400d60160300212120f1070080410b000380d6016000300380f40135011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 783241025 1250 783239775 783239803
    0x6090e0109050d050f04091a0d0f030e15090d0c05040c050403050c1009030210031b0e010e01090f14030307140c090a180305181008061903121b05 64
    0x964016418020b040c0114101d031030107400c0042c50262821a244503a205500c00c401480b592150405a411050524540d8500004002107141d540300e0902e05000f54800b0703422404070b0701c5a0141402d50800c1d03031102c0501419002e4040c1801c0300041803003c12403020000702c41c100c03070000c40800e0300d683d031784980c0100c0300c2540d031110748846c20341c0341442ca49113284149500c51041c8410546d0342d554060920810f595050f00c0707140c544441c0301015005084010000f0700808a0900c1041d1070641c45010b19107c40000d0b43d681e20103120200055901000a002d40440311040c820705004004001d8003d80b240440682140d240c1704aa450f1080340541d600f00b030030301d02d800c18141c481441c90440f00b0b4a0300104000b10402c10000d03541240d6502403001c00e402170031722034045400c079100c8820a20003240036034050007050000c0e61f0407034010400102140c60030320031810494110405c405403a018409d6940c0a0307101200408200002d641280c2c138502c1e8215103458a440a000080d41440b50303040284032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 783242275 1250 783241025 783241031
    0x90e04080702100f1d13020c03040806070314072627100c020f0307060906020412060603030207061803020f1908061b190305150607030c05013801020106090e01 70
    0x165290062860510903210b42c60721860305010170342540c030050808031030b02552000591b07aa15441c4494110300071603022242c0b50041e035080007105505034101004500a60f82440866900c03031800740d40310b450920010300f0848281340c0102040300400841600080e2070348448021483e404d0302802c0c000e07002d00b0200c025412000d04501b2888950080041060302030000d440c00500d0540041c0e0380340110700014003815254260041805041c0e811a00074000e841071099410b200c6c1e04203540508401d100c210018441e0b02c10025607a0310a01a240180711820309292010307265800300207007002c400c004142d2240141d00382641c6020b6210b00c2c0b000500019018209070320300b44402c14803100040982d00c1c01c000041100302c2000303d080030855504403981c00c00140b10f0301c51000310100c1040e40c1d48442c3e04a040002c2c0030081c5a003040301e03441c00510520092107140d075040240499013150201400b240c45001008580c80144d4072520750b0700f24010320002a08680d1501e400d020b0b10855a084c60321655 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 783243525 1250 783242275 783242297
    0xe070e04020f070813060c020d030c0303060527010e100504020319151403030f25140a0605010b160b0405030708030109090b06040c0806010c110907021609050106090e0408070210 78
    0x45e1a0900c0248164104500078890540110b00d400b06503900050401c000c00d4900020540240d10510141c8009000140c142c0702c024504003c0300d0003419103d002c03c5002d00000344041003003030942e1280400441d02c181c03441c50f00c13060201940014150280002a4003038106480c2d20038400e01050200f0b62507021400e602e1705031020119440d810050740613400c20020704000740141401c50b0340d200c3c0b880088c1c80c41c1c0d42c0d034203180c0b002800344400002c0042030074000d002040c0c68000f03880075009002d50800c02407a6641e20819449101d450400c070f242c03d0a5a116402056a44e441e00340d100e401042542c0c5800a41e9403204c4055009070004c40d802642c4280340801d1003c5060b83d42c0d0701540175103080281c03480c464005492000d005202904003d00c6a10700010010008940140c2000242c80b111542c28148406901c4440d1008100091054814005104004d50050078100d41031034890188481c20032180e00d10861006009560540b0204a00001a1100d0300c8062900c0700c1c0e940c420306100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 783244775 1250 783243525 783243547
    0x9030303070c1412070b13050f0609010605120a0305070c091b0f02030306031506220605090705070b040303050703110d0504050f070317210a0f11040e070e04020f0708 73
    0x114509075503440c40e4442c200020010041404036642c0507000385103215150340705003442226001f00e1000a00501448207041d8014000190003030140607154000e10103c1d45407814030002e1401400800450ba10002065001c04d006500800140e1f003d050b142c40c0c0302d030322680d14a0a50307049009030280c1d5400d0355045012140c0c4004104866111807002e1032071400c007007000903074980c6081544407600c00c203080810080d40d105403004034545004487d401110b1501228000140030511a4a02841d01040020314881c4500121040541c2c840e100b00503070b07216924100c00404000b0310902c1416500c451120b250b9680c032001d4212940035140219441c58640391050415035107a01804d4284d100d8041440080c080301c4200444810326070b145a101c00c0380c04104242c0e9007103035101060340b41b41001071262100c001d41285000f102d8698060110b004120322480052150348034014130304e40d5801c0401c0f0342030310541c0d11900d014001003000d400c01a801d408030b8202d40c0960340446921000060040b00c0c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 783246025 1250 783244775 783244793
    0x106020304090605151b010b030f0304031b05030a030e19080a02150f0a0507050a0b040b04050c03030a050414130f140c04080d0f030f05040c0e160905041109030303070c 74
    0x1800c000c4e585c2900171445410b804403603004441d0840500e250f0094a2150304400358014000d1314001002c441c0c8040d10003081d9900c84d8000d0100b0303500e41c0d0141c8000403042216008034000c030f0390f020f00288400440b0391001c0301c81111604080358802c0000401d46001c119446045014007d403001600803401d040c410070a03500500d41c1105240d19042c0310380e00d1408014000d031500340f41742d4180150760711000c4c45c0c968144441a080107140c01d504074140010f001c0300d40002841284100d00301d40b03500e03001c1c0c030405690380a00f0000e14000f03002040300744030200b880f00042c2d20040b0090b00b0003100c0910b0210400c01d60310380708141c3c854207a6a604041c08184180103650300500d8104080303140c40c0c1400380c030a494100c1111680e043c001c903500f5070460f0500c07980c450702e1011580c001c10041c500703241c80c000c2840c06035403060304800210400851058660303805420f401c00240c0d100d4000d41c03450101404041c041c203200d40d00b40702d1018841201070b80c900b440118404d0312603030b4600c902c08080d890b024801d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 783247275 1250 783246025 783246029
    0xb07030203010e13030909020f070b04060b03100b060412030e030a08030a0f06030b0402100507150219020c180901060801110403050706080c07020405040f02041404030809010c09030206070606050901060203040906 93
    0xc000c4c40d90b203940400d030400c0700319051701c4100d14051303541d61724000009140c3c891000010901c0c41d9500401c014004280d0040c03404040480580e5003400280c050700080d00d184402d034583c040010801003044480201d1056421380c03090030030b141c01a0318440024201008840e0581c0c42d080000708000211980e44259802150000c504101c11800e644540081010017000203000b00241255600e180303003c0c40a482c50182e2218410107844651600c0ca8040d4010340c07004820940c90740013000000380007040442c00c400018080d070b4410f44440c10503118052f0050820300c8255039424010411040a00a54268400380785069599504d1881c0c10381ca0202250f003c0130070064400140036202c5144000c903200d030744d0115000304403a10f950400c50702d10005071078020360062920f50400040650511580c0c822406a200e22003503544495140d03007038a00c000b03200b40018212500500040c94580040c021044c0074401c001542502c0c1c0380441e23642035081e0000c40146e400860208038600907800341c400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 783248525 1250 783247275 783247291
    0x60e09070608011721130308040f090b06030f150a0602060115260705120a1e020c25170718020901050a0e0328110d050c0105030703090b07030203010e 66
    0xf980703503101a21707110103000b8040700d080c101d81002e01d11261181c4043d142c00080c100007280e282650392038490301070740c0300e0b1280008814001d80009001201803042400309800940080d2642d603c02401d00c582c03000050040401215802d444580e035283c21f82140013511040e001000e0a50520400103802402014248100440b856181039410501c01c00e501d1801020075020a00b078032642c07801d8410f4014000707580004000003007040240c4020b9001541c401c03880c2c1c2442030385900300b0488042a48213920b80d40d040b030b51004644880e0715a00260346080150300c032115450036038403881c169400600c11444910550f018407020300000d50244034582c030340840c001d030851610040100181550103401c4100c4107003c0e50401c8680c854800f40660520302c400340d403041ca4a103420202e524802190154151200d800740441016141410b60b8210b0080b5084401081d083c1041401100c6e240c0c001014481010344588007a000504c00050b028003950842c3c8015072a5814006070790f4102500500741c00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 783249775 1250 783248525 783248549
    0x1e01150911070f050328031808180a08060a02030105101803020907020f0627010e070b09150d09060b0d03080103060c110a1118010f1206060e0907060801 67
    0x61420128008a5000640c07024541540000d00e040a40c2103000b84001040e010780c0b42c180b0816268640904043e8071b00841c2c80070000000c1c88459481003000b00d0600814000040000d03000c0c3c26003203000408402c0c2c6c0105020012500d82d00c0031402c00005a500e0518183c000c00103011500d4180b4000d80c0300540c070300d055085480d011100060000e060321000e4003800145021902c0c0070f10078401c1c20b04600920003146c0f03a40c00e00c4022101d4103100c41d100356680da45003d4405202d0072042c042d81603222041320081034400c1c00d084902c03c4a51010206961000703020b82c42607202e80811700680421030420400041d08299824a4025190390201c8544a2580d00e0030b0100003e1b00704503441e0660b5003008000801c09100f010a65a044101c7c0004400748580380701202001504100100304050a032180d81c07203000a03034054a1355110030300500c0c5901000c508103211802d00081d5403810a07000d500d010500a0303541050030205003098030009525000501d040c0411074011141e540180b903040000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 783251025 1250 783249775 783249791
    0xb030402090618130f021215061e040b0604030209011e0e0601051b0c031f0c020106050616061b0e0a050906060f03100503030c071a030103021305091e011509 69
    0x20103e6008100c0e10851400150704000c0c4020b61150308103241d8040d00b40246003c000941d15924400c07041c905a134044140000f84680c20308114000048045128880b030700e0092008000180c900f07508143c3c0c001070280400000359403000d00403402420003051010100100710f82c183d03010307000d9412050610741d5100070b101031668407404542f240031349020508020f02030501030300d081841078000b05501d48112484000c0049190722910f403e5210020104030080c0300007001c1c2e007070b542e0b14070030b140e4442e4091050b44421101c81c00007060481c820000010543c0c06550034041c1502c2c0c84c0e05d800001068007080f0801410016207080c064081210982075900d80100000c45a210b1050840c04406d4080041a186071000409902802004007520f03202d421150700a5900e100600c0340c02c405e0710142011a001e414084210780c16a50042e0168001d1940a01c0c6100902009000000d41e40b10b8000070511400c1c6903100d00702c899450600102d12a4400070620b40100415000001c3c007510385409 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 783252275 1250 783251025 783251059
    0x1060206220b0604060b0c01020d05060a0302181f0e1801290a03061107030215010609090905030d1a030c03031824030705030103020108010b121503010f060b0304020906 74
    0x608401c0340d00180c1e480d6195507007008038003e440141c3c0011004c20010444032030346541134020302012114000d00b0030082d5a61010402508068400a500301c041e0800000c0022420201558400d800200e03034040b10442801c49035000c45668000c0e60622560414050b909020001c0c80e264048180000e000101420203090010002c070000350203080b001c0c48058005454804800008580051041141c2246aa448001c0c1d03031080c60120010f0003072074070854140110102c0941a55201d64032100301724102209500144180081592079200600c0400405080f42c06a10300301840e5900004030f003d9040c09042c54800c0e1429050f01c07035001803166800c803038000700c4040c070740b65000c0b5000d00220b62844940a440840902c49010342d003000010440304a41020085040343d00c00c0e42c2e545102da81e01d079144411405030311a415045c5001030085500c81e900c4041a001400004000192001c00045d4041c00c4460383e50208420040c00700c00c010644c42c020301e600307501010544085100442d640c2e1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 783253525 1250 783252275 783252331
    0x16080703110d1a220501051e010f03020112090b1305060907082119050c060f040f03030b0316030f150501061e200604022103091c0c0e01060206 63
    0x81c01d8081071038240001e0522402d900c688482004c14040064504000e0510724040c010480d0340d00d01d05900901e03141c04020b03000100c40d04070380316010702030344142c159801121002d8084494046036611100448040b580c00c0600e50b0082c01c00030a03448070006203141c41402c00303030010491800340e000400204000c86000c113401d240740015070003c004101c01c4146641c1a8007030010301040c000b485040c01c10400d40c00a00404403c0b07025822142c0d40c2c1c1d03805000c00400c65046038020103c0c201c3c200b44600090094000040b030034030007800e032035018610303101d00000000994800d5a031100c1003480f260130b215490468a4030000c10704001c1c00b1940c1007001c040c04056103401380001081c0e82010508550344a92414110030062030b860070801c0d13004002d80e070340e0b420040c1d40513032080c0340140d5542846800e29a12803281400d03100070318148584030041156544044140c1003084104e00c0d4101700048054407480c000d07101030b6540303107020350404000a03c1c10000030804100e20110b10895103803115944 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 783254775 1250 783253525 783253553
    0x204050a030201200f070303020c1e090411040203071815020a260a030221040b060d0302070302030312041e0c03110d060f2304022116080703110d 64
    0xc20302d14014488180003807080c00c030f80703000c601140c042c4007105c1081d020086003100450b4025401c071880e03040c0d1001002600c08505050001d441e0050f4000c0d211414082a030560003406501820200c040000204090f41e0007190440001840200d1800c41c01e500c0c0802000a00068411a0303a12041101d020350380b01815040641110035127100d44541c980311501074180c80404049243d06c51004400250107900100500403100c040c01e2180050a504080c001d03200359041920000551580b005000b45030143c02801c2d000c40c000d410010026880800c0200a03450040c0f000d040a450035003840044800c2c11045070744e115450b040c861001c0348000400340c042c2c1e60040400340100d4601c100060301042001c400030310050900c18010b40c580315681c0b100072840c00c10301042090891050041c411014200c5009602442580402c10703000c4060240d101071700308142c11035014081842c103207010440385510820b4543d1040300c00f03108101d41004a408030403c15146c0090101ca1a82c800000140b42 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 783256025 1250 783254775 783254777
    0x1505061b01060b03060103050c0313061a04060308030103170406021b041410060e03120d020904020f070f170a080411031623030307050d05030408090901090b10030204050a030201 78
    0x4520311000440c0c030041000320900000080103560350f190028125904111400c6020900d4400042d00882e03000c01280d01c00c001ca1a2421040c80f13403075403640700414080c81e48402685e000c0e03000c1500c5481d01c4c4030741d0b0f0146014214081d2030398550324180c55960f4010125030b8500c2018401040f5003500002c0700f800d91000810355140d80e00419001c14000d00b01d129100c5144c2d44001c0510070300c01450b49090342a140c2a6031400b10000c114000d169a40c00e07404540da010300c000708800d0782440d200364064100848004c1025280030402da002456540281034250342492000344441c01300600e4403110900c0e800c0c0c0c803400d2414150625400350944000800240105001004d0703078110340d5080c860b4a5416611ba8468031016803500b4101e10108004402c0010342002c080b111a0503107000025600450b600c00c0040031019001c0d10112020b03000034004949402c02441402c28542e03404020b107000c2d00c0000c0000406640ba002004940d030a0f0404881c10b241c4104007d10454480200001c2500e0702 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 783257275 1250 783256025 783256027
    0x5101e020d0207020a1202010314070c060906060503071805133f050c010e060f1f0306090b06010e04060b03130807060221010602012a020f0f070501030609150506 71
    0x95104507002034410040c00950041c0d80603008200c000e410020701516038001e980030418200150240707140690241c0c4c8840106898050260000700309402408400e4070603400400c207181d4a00100780703083c43c40d0f008080500d070906414490755001f0312805031b004455034042c1111168540b608104c20141c1040ba40d50300e0300690000008507546a001521044803124151125101880040140d0852a01e025003542400c5d98030100c003800180c4580114908150b03204151030340621981c400580c40c004a461215032200040400c801d03201d1a800c07140180030841e4030346801400140b607a40701c0702c0c15a104501e045020300c2500c80007400d41303034013411400c80f1061710140e6040000b168083d442008002500000b4000300440400030742107103007901603161010990f220002030b400d0724540c8600c00110207000403032007048404166013401e41540b80c0196900c28a010040f1420201c465080a030180c0c00404100680d507494840d90b4010b006010b020008801d0a00e515107604140748030706442800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 783258525 1250 783257275 783257287
    0xa05040b030313091a06040b1206150316080601020a050c10030209060c030d05070c0b07141908010f12030203090603100b0c060a050604141b041502060405101e02 71
    0x2800c0040712000343d420740250343e1813940d0340c40c00c030090004d80519660072442503170040c0303040c10050700303442c141e49449070700341d0900d0490b148126034900014042d40e803000c900c08401da05941c003070000794010948503040c0d140340c1c580350101801002c0054019811503015010000214034007041c074002144040b00c2d06c0d80803421510f8110064024035000d95485100000d0815000b0000401041c0400070b690042c8000d581e03411054610001c40480030340440d0000c2c3c006095148180c6280c01442c042c140b07094100f219841e04182c0302c055540c1c2c0c1d0350115000300b0040c00750303000f11101c1500909008820841e010b00d02d070f0f0003d440307014001d01070340a0307079010000c1045411141ca601c805040c171a2001134503042d044055035038039a07054480030455071410020800d42d08182c055120000c0c9002d04c00609034030343d50010b0010000881040d400c1050034840031071084460244024018125402454181081d0804608101500101c41141031402000d00840680c0e4180d10349078000c10900140c60354 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 783259775 1250 783258525 783258529
    0x30c0507050a060e0406140931030e04060803031905060f03010c02280b0126072607240e0a03030c29010902090a08010e030a120b0a05040b 61
    0x35809401050703210904400c0071800340c1d0b104504204105044034180049030365603051650310030103039141e2030300000780000207071b103201d06941903140d00300ca0340451030100501003801ca9840c01140d40c0481c0040d5554200201925240c003501c0081c10340350b4007a5140d410a04032096469003401c190f2448607890704e00003601980c0e001c4a681351802d019000380000d1031015030003916060101c1000036803034400c03004040e01c1d510114905080b203500c10300070742c3d103a420a00001100e90031502103030034000803800c104141c0c50007030194000410100d000b00400c50700c0d00c0d0855400921107064403031517601219042140f07100401c1103214110b6108078002034030001e03000c200c604417003402925400030656a80081003507400011940001d00a5100c00c001c607030750b001a9103404100301c81c1840398186d0b08005001d0700303500f5402040505001883c2c840d000b582d4401035425204c0c0a118440c258201054500e650341d0043c1000d030742c00c00307a10010030203c2e031341c58005404543c49006a0380100d540b003084071030715 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 783261025 1250 783259775 783259783
    0x16050112090f0b01030303151401200313080c1206160e0d0f05100b040902090411060408120a0e06040e13030c05150702010c05090a03080702040920030105070f02030304030c05 77
    0x80c0d9000343c1015210340e101c0c24098040c010402c5a220400f40c004030002da240201c0c080c200c500f25050755085802e20b148020b496a844922001d0b00c0c2c1800200410321a041044044400408140002e0402942c10703004100101f4615564601c032a0400001c000f207910185c02e2a411400d20303802c00207100d180980c04901d05c0c1440740b400a103801d500210070380911000003210103070340c04581e0301402034000703040a000a852a014000390001c00d01000700d00010f00c1e4401d9104005406402141881d5640d4800d5180210390601807070100800686d0f0f40e901a4008001810200300b40c1e82c881c1f80500c6c0400308036007035400038100603c44a038000020100362003042c1d00d50340c550304001107510040c4003040b0400c0020060714490095880e00643d143c10f54041c00030382d200c10200609601c240c51075904d03081c6c2140d01100c4103d030700a540c0c4108000203100800398800e4100c082e1800001001d22006143c21244091302650034410741c1c070074003003080b6030000031203610550500d00210641c15500d410380c64 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 783262275 1250 783261025 783261053
    0x230705090d0f02090c070f0314090a090603020f04020903030711031608010b0111010c020c040b1512011d160f03060305070b0c060a0c14160804090b031605011209 71
    0x300404840428080c80509001d4100382c42c0211030000840d2160000c0705918860510b005100001c1c0740151000b0034050758003156a02994040a03251501000001c1c00a492540190000d01e6560b1400e00941c105000154007200096508518003820880066078902500200800c030440f0030150171425101804603205c1300905403210700040d43c64140c01806050143c801a000070340c101c80c020302500c01402040f03800315a98024007507558001042c000600081c0360480d410a2220042400b030350812030040080d0030b030010280b0210350501003148545400c0242046c040c0580350240046084510130f452642e8510342811214905540c90a0b00030340700c0c50340702400c0e6001e1041c000856080280085c2a050081400d44805d0342d02d6200341000c8406c01108900003850303401782c61503c03001081c02090140e0700d0150705042c0c510280d41e030807026402070b0080e080703054494040d035950381010010044440707010600101e000c0d0612000a01000460700070341440c1da240d82a50090005070700340302003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 783263525 1250 783262275 783262279
    0x16060b04060308090102060f071d01090b0309150c0f0a0806130603241b0e06130602010207030f021f11070c1409010503060f010302090c04120507050901080123070509 73
    0x10a60b4900300810203400c01d60806016000d0000010843c000d01940d0707501c03460b0076071039031803115903654045034251888044c00e50502c04481c0d404699189100040c51007007031001c000382016058070b4860220070f0780260030701c1c00042060111482650360001070300e152007400c1c680b001203907070f400c800a980d0768801c042000e040c0b8545017010050108100951410046994a810004408600c54000c44071404599100a03400317070702e507241d110711031100480d07450001403410341407044110095480406d282c0c44400580c0d4002911010513402c03142c1d441d0303042d40d50300203000c0141d0b00054400962000d050305900301c03079a500d03026145503200c0007035450a94100d40150890b0f0b8036440c1c06103d03000588a5584124070341c00c000662440d001401d144921880040700702e02e80d28581c02d101d1844170103011640001c00910022034005024032400108502800040003032501d03180c00e220407d81c0680092903540d040c0210180c000320405a030000c81d091020301c0e00210350714100101d407d40140a0215 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 783264775 1250 783263525 783263531
    0x3080d06150201090501230c0a1e0f0f080411040507030227040f0501061b260d050c03070e2106070504030507050a030308070f020f16080708060402030316060b04 71
    0x101d0039415807081143d0b40c800d0008110381241c4040001c0688a81c8018070401a1800005a094040382e80036101842040c10441d10308400c031200e048440c68015030b04070002d40791000103050b4a502000760f410b080e019040068030740c1450340b294495954030226040c0aa9200d201088405120358111842d40440840c0c500411074601810400e951207407911511442c1003413009441040e192149034100e0300e103611202d2212131610100c7c0c81628901c035050340d0031140d10144440b117800d10b46444440c010f084004541c2c030500b90a04004961010f0404401c0b11010b10821488035003046071544451030848807001c000c02c0c809100d035201c500f04a011143c600420302801500c03900600a001038a00c01c0050300d050a444800707002c80a5481d1102400043c4d41d6008501254004c1180a05149491041d681c05400f40c0804c645442c00030001c4c0360901c18003801c208004802031080b10082e01144000d800c01c1d050640001e0341e40d004154114594941d440c503030780200001d6903c00c60710000087d0040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 783266025 1250 783264775 783264809
    0xd05090a05100b030105061e090c190801030203010c08011a07060204030c091b0302070503070b0901090b011e0807080703080c1c0e0405060d17090312031609080a0c03080d06 76
    0x1001c0940900fa024074080c1d07003080701181861a000c03020b1400694481c020943d100424020001c442c0030190203165110002c1102a0300e82d4003800c043c1c0402c8049407540e58165141d032040c1821240c10700c40130410402c0b010010b001030210980c481002c0d80075440e90076240c01040c100f2000a110b5940003c00300d940d0060000f640c200d1981103a003054505403125541c010300307003c00350107034440c0d940001c080d41c100b00203510009544540303058200075038100009041459507600b4840601c00e8005003400700c900441440090319843d1498090281c9002600d210743c1380c0b01a09554203c4d9001c01000c2e0340000c140c20070311040c1000040d0f04112140c0d01c425a1200c0075002030b201e840341c54501d80c080e5041c070f4002040d81c00c1401120302500c1d4002004049040c00c44180041900881d505982c140500c0030b200c00503101c0d100286006221120b9900b2480c1c1141c8000f42c070b030019940c014000f03074120b040d0300d07800300b01d0300d11240080320b030800c40a50b586e0880408610040140e5000b00301050a02950 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 783267275 1250 783266025 783266053
    0x601051207120e0f0604120503040503090103180506130c0f050303190201140112210e0d030e150301180b1509180406020a0e0a180b0d170307030b150d05090a05 70
    0x140b0342c0194080c00402ea060400311400308c940b44021500584a944104100102ca51003544101c0c80c031011000e0406000384156501d5050203410b58001d000104282900424007044944d410020b00c070f00480c03002d0701032401003c20344078001c034a85d0300e106100785482440c1d00c90007900031400c0c80c0c083e070b200c0c40f0b110340c1c607800f03d10072440d03401c00113845102a001e01c501c43c040c40300d01440c1821409413203801464101c5400c110100c00810f504804102554544104c41c1d2500b04960a001c80c0113140c40e41c0341e605003081550811703024900102c84500f00461010075860b81c0821180b02c010000040355a07500d403802044210f01c2d20005e01040014800c10130042c4640c983c050032402d060b40e0746400d8101045000c00c030440880b4000c111488006e2051780d00d000306142d010000c0c140c1c0c05403405c07202d07070100d8a510f050001480d014080420b000010021950340c544983d041056088448010139008c01c2d0380341c07116020340c4041d20308059440c4c021a034000c004000b40a281944601113403040a9087c81e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 783268525 1250 783267275 783267283
    0x1005040219140307140c0a140307050f0c0f0d14031b0c01020105010501210b031c1218062d020a18083d050f0601051207120e0f 56
    0x40c24000080851281180d0a0009001c49003c0c040541c5c825030b8020341d08410340d082d6448040404a248120854200000d16071050451600ca500700a15103a181c503041032414800c0400b114804c5400c202c0511090340d40d036180c18580da4bc020303aa00d28500002d45001e52440c4600458202144000700e00b25030040c10245505031020004000d980340c4454600c0160300f070700d01c2800b41074041005640b03041184c0c0009100d40c10842c10741c04010a94010b050017003814510b520a24207003c140d04540c00d06201d4210b81d52611043c503040c010007030b0082000034032100b50301800c4010540354541030520072504942d1200c001010000c408034107038095902e058002944030210440102300791145600d9030f180340c0045030040319958009024494031104480518000826810403802c480b03000f0140782040b0b44641501d8284a9040081c040c10090b801075000b00c4000c1c605410072800300b00444e81040840c006540007495401c244040030701d207401e00000703807020700d080c62079601c2804415201d4040010b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 783269775 1250 783268525 783268567
    0x307200112061e0801200f1312060606090e0103110f030610050310110702040b031606020105010e0a0204150e01140708040e010608041a060303090604030605060a060509010f0810050402 81
    0x3c1c0000030702036440080c50b083e50019003a0300300b890155210600d02a0134a40140001c080d025102c620b0a0308003840f4180b5950b0302e4010504989071003454500300a064801e840c05401d450600210701e900d40b18103070054100502004196a9008000c909a61038200681985203c01010f8440700e19050113800c8200c440c0d48680d521170303c290030340905065442d10910255504003000c83c0d00d0440305400b8440a07005d1150182d4152250761000010344421218400240000ba4000b0416524141d001615210050f0000c00c0c014410882000381080e0400703100e00003d41d40c01c1c4026040003480050701d400498414880000500152820421100400070700a075450541000c2c4583d8a502c021900e501c03080b6401029290301e030032100d64440c0c0c624000c03603104100a00312803900c80c102c40412141c2d00140d0084031880d840f00180482e603d4a000054098555850483d0404109c440000c00d010b040018050a00400d080441e0100d0001d030f0912001e00320203001555183c01d0004d0700c0f14a59420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 783271025 1250 783269775 783269819
    0x60d0f05091006082508011b021005010f0603091a01060f171012060603080d0b0906030607051905070c1e0e06060d24030605150102030720011206 64
    0x180a070b441901d6418441c220550391801c000345841c0c601d503000d04003418900120400c0c0b210001200080c00d0b9824021024401304900d8254a2000d8401c07000c0d00c0c00740c0610813641410708120040c40001d081d071050804035550307480c2c041101611814048410414500048064640d0074004038403103400c1000002416415a41e06000360000100111981ca05907080c00c00956410010003031000c0141d40400010301607000094096625500c00580e544011504990103403a10050941340c07500e03003000c0d58030500586c05081c4c2d51924941c024030314440e240780f113200c05d201d45c0d81164516201c0c00030385462503030100c02d01000390b8681615010b00701c0604080b0400c20034041c0f0210f840504a01481c4c040c0d000078000d0b906100701e4040f010040c1048070849404548100c004e00b24070307081840804001c60003840001401d040c03154080501c0c8216250f4a410741d030040280100203201c1002d00105601c114880790700305d00b81000100c91030002440f485080c41e0810b980401e44206244080e8030803004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 783272275 1250 783271025 783271033
    0x801080706140912240a0c03090201080601110705060f03040b0705160803070c06141803070c12051203011e060e010e01230706090b1005100c02060d0f0509 68
    0x41c40320201c900c0c2801562240042e4828483ca580d103050a00c3d040c1d07144150142a0307982c550844030003000060906140c1c0745003c070100c0500040364528130070315030603000c1ea20382484044541d0700040e020900203032659040250203000707800024001c1c04282c001e0000108039a550300000f2802c060742c1d4106845c1075620100a402203007080780a013084a94580302c0900019141100740ca591001c0d40004081805100750140c0e00c80000301180b15080180141ca0410707009820540160400c2240100001217198800c00c00040818601d8039450308807040f15135502c0306403906241c40b50404501c08003038070b030032840400003242080342031184103001c0b007440d101c0d10036090307485600303c60341000500100e0110322401542c807a554807a01e40030300c40f65003445e850b091203045166840101d6100090030303507603166120007407003c0210320041a80c01000d41d500c074510403030500d4006440c00c055002c0803410f200c0040d83e50b2046484620a5802c0010200000c003c81d0100c001c064001c1d29048a919500307003d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 783273381 1106 783272275 783272279
    0x30c0501020d0f0f0501050901050d02152a06070216060825020a030311120601051806131403070e0a0b1c050309190e04030c020d0f0308010807 63
    0x194141c0004e0301c0003210301c0d40c508460040e00703c0c6125044036001000780d0f83c2d900b040340f42029011200092415001c2011200038407401c2245c4284980d40450040c0444022000d4012901d4200c1682c185580d0088200e84030981e144880c0400c0e800c4082c01d00009204881059010403c5243c022018185410b042000074000340100d006034040c0143c48209a414020540c011417045081030600d541120341500c920001000141000320200381d41d00d8a81d03060303c04041122001e0070040d0786040c01030041100c40403c0c084c0b01118210070b000e00c507442c14009a030b00100d58460360011440c0c0c5541c50510f014000c01d4101c00c3d80b108075000d1401140c001c00100140381413084006640d03c003520018000a01806401c038500c01140d0841003000f107070064812075002d80e25182460202c40940300140c0301c0e00405102600c0394118a440314209900900b005059980100840d40c04036 = true := by decide +kernel

theorem cover : BRFrame.Cov 783093525 783273381 := by
  have h0 := BRFrame.cov_init 783093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 783093525 ≤ n) (h2 : n < 783273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
