-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4424
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:34:27.342986+00:00
-- url     : https://prove2.me/submissions/48f8b2b9-de18-4893-b726-dd43df922e41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 795503597 ≤ n < 795683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 795504847 1250 795503597 795503633
    0x14100309050118060f0b0301020a0509040504110603010b0d051302010e0105130e13021c02090f0c27131109011202040306090f050601080d08042405241813 68
    0x3c020700046103441006014000c00010283d0f2030000318610905040c002c40324a00038540d1454501154541004010710000c0c1c03040c0c0740c085882c0645005a200c21005601800121b030340c41307807241d0b481c200300010350320000e00070803100400c101100010b0360018400c0390f804c40c3c00d0030225101e000b030078220035144141d540410100b41e140d405204211141c0f1104503411070003078428084408000113107500008490000079005840e00c3c000030001f901200107280c0100007100c1041c5448150703500c030500203406211084440c01c1c203070844a00ea150889c50461490101c07101030080801c1074440350b0305805400702d02410300540800b0444c03005aa581228091a80840c04200444c07407410207495203022403030708a4840c402c4800104240c000059001d1140480381d40716851640e03503680380d49011107016410380250040e004103140e003400d00c0c010340d80b140883c2c4801113601e9a038001800e40681840b1580760040a05154a48510303601008807907024004001422068074540391900741c0c101d0180c050303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 795506097 1250 795504847 795504881
    0x1150c0c0605090114034309060909051e100e1303030605330415080703110405011e0e09040b04020307061b26040f0e01141003090501 59
    0x104600b038001d006001e41c00000e0f40d5500c542144c0108000540c80207642100301c6809852007009a0343c5003a0006d04506d000404040e15002ca299030400d480b41c80d0b143d0800461010300c0c060002aa03c00c4918000b4600700b0420f00c1386040330f005d01c0800140820018108040540018440c1075440c081840280200d0040401d1440d064a00030f0a00d48034100440c00a41409800a064908802200d00c81214000b801407425220703455020741d400494030080e00008144070000c1c02440444a8005003003541d2903603910761410480041c220f481f110b003e01f54030402440203100c0c9036070110300068241d030351117010700c80004888816a1403000140050364094410001c0001700541540c110780218400c0c0c0444003402e880348020307150481c954800c9500c3c501c680750500007140e0303080e0007003500b107086140c200c000c070120154241403680960070008601c10340050802030b00c882910301c640102494500b0b15580c080e06400a00c1f0f40010200c084101500c6859120502c00c0a51114142c940c51441c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 795507347 1250 795506097 795506099
    0x2030f0a09140f0f01050709050307061209150504140715080604090b010609060f081519030605010909380703110409060503010c08040c120f05030304050313081501150c0c 75
    0x200303d90300c1308242c0c5070f08655400c280103d00d1150042069030305407003005010308540c1c1e003845c004441c08001c042c0f11103070480e110b0016001042d949005080e004074400c1c004101407500d8102110810050303c40414254803140b41048048004091020140458904040e00b42c4030100003c01901d04241e01405100c00a800042d115800c164000205c03402d5443e005507100040c00150395115085404400d61061032206403040e10700b42d0701c0300009501c2c0502c021a102e0b01c0b41c45200031036100b608081740c2c0d16a1000340300103000001170769004c0d4a140039040d1030b48110f140040344210b28803d00c0140d404200c880801c0720103000e60001d50b064402d07480e0b02a150365444088401a002920070640294070744090843e440b07200792440380c030507900034441001541c903181342500556440d20302074442403000c0100400103070080c0011030085014074011919481c100d01400c000010315800b14003903612850300160840840c20005044070340300b800490303007080e1000040d150403030801d00081c41000110300c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 795508597 1250 795507347 795507373
    0x60323010b0d1e2a05040b0d0e1614040207110d0201051207170a0c090303050904020c0303011d01080f0c060306040b13060f09060b180f06040b07021302030f0a0914 72
    0x1004000b80f00c51350010110010842607201880f003404220341001034400c0200b40030080d42c1030020542d45000410000e000701031800100c0c10201e14202d40c0076a18600c5a0800c584100d4003c03068410b00d00300c0d41145030411640d00d0301d008a01200c4d542d8020380b0b903000540203580c01071081c1c80001c264544210110f151004009060740882c9005203020059000450500c0f441407180c4130b419250707621103d000c02d0440e2000e8070700c0c1c1c02c01501680e00c2602044481d41056040c40030354003d264440550480040c3c82101200500c0305030070640d1198001d6840c6148220b0010303041c0c840c800c098401070b941352500004280034103a9031521a0b00038400b0400722908001503800242141c21000c0c51144407900c070700d000029100075109a80c981c1c5d0091003104203901c0901c00301038864500074184070a403120301c030108120342c015504c090283d2001213030f40002e5040c1a00f2400c0d0f540d002c0c4904605e5481c04040761001d01c0c1c0054801c518282d0380d5000c0608000b06424422100c2e98460121507550845403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 795509847 1250 795508597 795508601
    0x40521060703140a4a0f01060603020f0d200703110601061d2206031208010e070c060e07080102030c0714030702030715050910030501060323010b0d1e 66
    0xd0f0401200781c1000d8000f81003500e6030b1080c12075000e030100d9a00400540208000d01100d000d40c000c0001c0c81141100c00504050b1249402010760740d100a0000b5000000300f0030708580143d0712540500d030042101d046080d101d201110f100f25000200051031900c0524136414140c110b40250154501c00119034040c0754000c52490030a00700541142d00c96a201e0070100c44a030f500e290040542d84159032168602d01c1c00300310620300c1d040d2041c00c0000c03540703a8046030800e840080d8019540101070a402c0407609034003800103405008c21080c074915a08101900030040100076101519036951141c452404c4181440301e100141114402551603013080c1c1c0754405994005803044030040c04a8a2140781d11901006407821203800801a04c4002c0c1b50810b4404503040070107849080001c20001c2003003503036031a600102940d0340c1c0c1c2d40004035581080701c080c00b200c49030b100800c221240d10b620035200210640c4d000307054440c0400c45a44420b00141d4030340151140550450700003160340e41603040d00d03110fa = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 795511097 1250 795509847 795509861
    0x3040e2212030b06070b01140316150c02030c0d0b01090f1803030b01110f071706060a0306020913090515071103030103060504020a1205010608120906040521060703 72
    0x8040400500d60303400040c200c00c0030280350003825842105090948680a94410030103020701805051034000140c0c0c4500005900740c001c400c0313807075200c1d0048680d400c0400905055444195a03d0140f40c14800c00c41d51503005460345404100e01020035004646041c400407022507000307440f035101034001c1e190041c882d1609028140c141e82c500500305481c0040d501402c41d013a5152039203000c09051a0310304402800c1e40040036814400c4050300c0601c015400c00c1515461900c80026080380b50900058442221817690314081c55481340b814003010303a81c0c84005400303c9034441001aa154009004508106592061080092300c0c08400c2018040042103040400c403103512245520307613500e401034481000c040c00700b210a038400c0c070040c17000030000d034803080c2c020740010252940c0300e80c0c4890807072902403007941c00c0f20903944130001003150507420003d100902c80003981890601c824400440e81c2801030340b048600c00d121411400310241c1c0000804241e920f44181516018946140090050030031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 795512347 1250 795511097 795511111
    0x1052b0507112808120f16021b060c0102071e02010806010f050d1a0d03030e0d080c04170703061112090c0105270a0608010e06010c170304050c0a3c06080c0c03040e 72
    0x700001104c040d07823000c291000380099262060800c555440280070941d0030805698115650070400700000c20340a94a05c2e0103444c60202000044406100061103e003001d0007160501481c3c86041c202e180e0002d0648440310806100083c4550030b2800d01e0000c4825142002c4e00002c049101c2410316906410048010400c1002c0394050074500b0412908404200c0313014603c104240030034404405200200b4000700d03428022106070680340e494080032101e80e500081954900050103084007424064600e50051f6140e02030070ac8ca80c003000000c4d08c01c1c032601d680718409a40a0744d0380c0b0b12180f5481400d0901700400380ca440c6035030352601c05c0541640c03c00c0c01180f4448204000103001584903000c00c42c101075010744201600c83c40e040c00c0050341d400c0504212000e01a07042d0030506910b501d640100200801d8401e800c0600c40c4160a01502c141000c45072074500d0645032500000c5140019101211390504d060011551a0400408580640c114815681c00006000100b40143c1280f65001c0e001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 795513597 1250 795512347 795512371
    0x406111206010f0c211403010f15030603020a17010c08043503041209080303040302030f03040320061008010504050615010216090b0108090307020306040201052b0507112808120f 78
    0x860b0501e2901c0c0024827600c00d4060040b50207000388044400090128000c80c1804a5940d880703a0009602aa280d0007042140700700c0201303803034503001c240100107019080d41043c00f41400d042c0c4503030b900692102c0201111540d02800c10100f0780038422180f0481450800d5551203003441d103810030f2900c0400c040b180c0001e085000c0421a454003100320707406554507800850ac4c084030b41300480000d800c010310070740522140480200b220250300e28505440303688003010f1702943c6009411418200703076a80110f4010b0780b40404000c0002c200058881c0c0002c0442d000103011242c0c43c0c0104e2400000b01480d0020010781c030400141076245410182403200240c07184602640c0780c08000399280035011001c0e50640c4a20081000f65025900900b00392402032425904c1c08180c83e00a1803448602da075040d006a900c03801c20210a03841301004101ca500e403c05000591482e501902c4000041c01c44140c1000241c0803480800c9039200c100c420104088d03d969820340740c0251403034a4114200c1e0003200e220 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 795514847 1250 795513597 795513617
    0x111611030106052e09090e0703021002160308030903090d031d060f0319020d0606020a05070b04030503070b1f03050a03110d0203180301061d0406111206010f0c21 71
    0x2140512016000801c04d0981c0b104001d0450140c90031030388804a010140300c004072011030065480d0040e40800c00e0400002c1800c00d02c0c41c8140401c001140813024210740104c05689100c14031742d46038504883d00401d01540340d072100d03040c0d282540300d60a44a54001c00300d002500815401c04680300310810980f407002e1110803c030083c00074a1103002040e41141d542000040e03400c4484064071240844108401802c3c1000c4400040c11200c183d001400968014043c003003c106041250030068054665460b0502d881d40e0384031942d070700480d180201404109000140803121100715a8030f803d81c101c030080c0c4059034a040103526042541070503000114200c42c1c1c004180000503903400e01c0040c0d68001c505e0300034107600d519900b00c00a05455815500c1d40c00001e00001d0101c00718101d0040034564048509003440c000e000c4410ba162180210f800902083c6d1290380ca485009034496400e003010841c00e40d0042080b1200c035400b14008000502030804601550f44c0444a40c06030701c1251030b507003469 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 795516097 1250 795514847 795514849
    0x72601050117010e010504030c1b150c051b030c011b0219050102010c02060708070c1a07020c01120b0904020105030703140c0c12040f120305040e070305060418020d020411161103010605 81
    0x10343e10446001d4040749d208103c220001c0e01602080c5816401d00300588241070b241c3d03401d41485500701c00c82e040012041c03c42071081c007005100004102c03000c0c5100340140c07400300700420744546241c10b6250502180300b01c02c3c0300805071841c11a817040c0d40209061840541c0c000302d00c1e12648180a614019842c100fa0401c4c3c2c1400056100d0242807181ca40050720343c0c810104650340540c218044412601c0f01d03081860fa540300c000b42a0050368641c002d4000c0400c1311000401c03070306545861030506410a40030414548504032026085502032070220342d00c1d5900034040c2d000d403010300030340540c52144504202150711900050021171507000140c408418048030800c0c10760180d40100b202c20b000c1d041d8108003e42d10220028a100e20a0910f9820705588540046102d203003255030401194951003006000d26003881849004c140b038585401c60342c40300340c0105001e4044d2000007070045603604444042105084240c0780d0146191042c0c90104c4154036041c041448402ca12502039821b01c4408241 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 795517347 1250 795516097 795516101
    0x81b011b0309020114030a180b0604230f331c0203102a020601060e10121e022b020301050d0303020901050702120309010917072601050117010e01 64
    0x2c00781d01650365800d010303004d80585090343d2000d0014010503550303214564a80070341c40400429140100000f240e50b02d0550107100c19074002494001005920b09802500c501241500640108501559003010380e42e8002d07034540b240341c0b07900c0f0700c14030f4244030a00c0180807442003010000100035144409000711010f584070740f42d0480b1000a61640080783d50340301a0350240e10078240740f13a069071080381c1c0c1c1800250b03c4ea4000c000b0161a00141c20003401400300d0354003c4060441c03100127851441628002000052544402d545910000c40c0c607110030303d124007106540da22403140070b0b490856903815110b00314070107204a00408014010040c00d1204107002c2071080c0ea04a900250203621542c2656034220000e52011000c10f0600400744034141c0540c4916018012800d02540107540d2040d11000140ca80e0b6050360014004003510101e4844403100411030f02c00306e03504445810340032650184420480500c04d5102e240790741c0303050000a40b1000002e420004440c00900030040c00c80c0040600d42 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 795518597 1250 795517347 795517361
    0x14030118060b0a0c1106070204050103050a05010e1501030b07090f09020c241b0c0709020702030c04150b2802071a0414010e120d020f0d03091707081b011b03 69
    0x22812800c2e544011400303603c110705c10644018820307480e280403a80003a0458100f07030000d4503141d000740c00d401c00300304091048085011401005150359040541140d00c00241404000e1100710f540300401c0d003117402541070401401c17004903070034542e50320351504070020340202c03100c3d480601c240741c0d03141800340320004001005c0e01c1c0c031014010311b83c0e5000c0c0c400000140198070192407142c100078510043c00300340001c20107400e4528025a41342c1880c010145402c5112040c548110328120000d8064452000800c0c105c0d455100219201d2880c1140600e568815415003682d0010043d119000143e01007510401d58031800c000b0070030380690340c145e050380b0301860281c94600071000200b48203542c080c0c1248000000010180300408400e02c403a01e061108555a110142c0c1c0b02a04e0501d0301c54040c41004103000003440e08100c0040181c45000703d01601c00800404510001940c000780041303a41101d02c00c14041c46c0c9428040c02d5940027a000345001c0f2610102166000410041284a409101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 795519847 1250 795518597 795518617
    0x90509061003020f0f041d01090209090412050c06040b160206040c18090503070507090b03030c03030a051e01080c01171621090605090d030905031914030118060b 71
    0x750540d6610682c000d6006100403142014240110034515006000410142c21800e419201e81c8840010b606422081078001c0020f140c01408505840c1e196004042e0707005030401c901d0018020184404d41e800d20500d01c018150340110700810051000ca40f01f01030103403d51b08045481401c00c0e00040340c0310541654018500920714008101d000c038420311100b2801c1100c500014001059555240b443d800300000311640d802240c1d00b0020294a4801e4003c03d10f8107030003851501c0400c0c072078507841e407000a08124072103035a440803a41c1d081424084001c2c921520032903c5081d42c442c40f016585078009004140007078004000380c0021040550a03900031114800ba0a0506100d0f800c02d07100c00c440e041c0a03240032020f450b00e0060408250107003480c01c6c2e0080300700060034285203045c1d6007402855111041410b05010d040030000b400042142c9070640e525070f03000301101c01c85030300701d40200c286540c0b400303000e4010001080024809420b4030100854800401900e555003080d4041e50052683d40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 795521097 1250 795519847 795519859
    0x13203709030609021309110f060f040504020d060b0703020f06090d090506030415060b3001030f140106091d070b091e0a0b0901080c1227060406020a09050906 69
    0x1040010302c03580120300504d01c014100021012480c4100c4c085648400c402d8840c841d06a0340c202040c1810600e0f071a40c0942560b031145810140c1c60b0b014001d22507403050500465001401c254014100d81c031840280c691102040c1c4d48940504009541c2c4203003c1040c0114041c4402141c1002d40004040c4800b005544455582910303000420013613800080c0284c40c540c4c10520315503254100c510803600030b40301e54680b05454081d90701c003518041c5104000c16085010803903050381140c80300c03c2c02a04603a4800049034090f81107103412062618400e0903000d456003822804603050080e03800400e07d501d005210f5903158050070340780683d079100d01d00c19480300d00800c0080c0c0509003000141c5002032214880d07400c1031200010301041c0100915400301c0d003113000104030142d4540c0c0c0009950741042c0d0200895051500c8030340407007003c01c1c0142c60749414802c1a00c09035020500c00c00e8603d10300a0b05c03c2075602c0780c038090401a0107035000100d030300c0001e00c4c0c071500420145003100200e070003604050700c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 795522347 1250 795521097 795521099
    0x29281b020d02030f0a05070602240114010507060504240203130803101e030b0c0c100b0111010c1706041815150b04061b0213203709 58
    0xd10900c0300a0040c10b9070140101c040303941d000b14040109401e820f1140d0001c00c81c503840c040009091022120506000300001b9035440c00180d00065220f0640380d10a01001906188034010b9419100c6d01c94028140c90030801000103008540c4800055140c0300f1450b01c0305d070002c2003980b10803840200c0d80f440036110841c9810300481d01a2018542c4000440c080da44000e8807031042c244000e1160f80c2180d19901d08810500030001c211114030b0b006038404c01000e044c0340300c44c0f101d5900c070803244405080450707039102031201c04e03881043c1251443c038118000f040041c10310b000c020000d910420400d9501c1a003203003c11031034102407142c0a0440c040030f00c402c0440b0915528540300070070507000d454400b0b1b190605200a0102c111101000707200c401b080d5551940750040141c4400100030a80d100c1c000408040000b58844c550010a402465280007030210301c00b01510780085242c0403540052000440e40c4880c0c080000000401300000d1003c1131031412250704600100c1e40c901443d04001100000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 795523597 1250 795522347 795522349
    0x4110405030a3503060f0306010602061b07080408031908060d03030e0109080f0705070909150e0709020a11100c0c0807111e120a0c29281b02 62
    0x68032125004403503110f203100180400b801c803c80c103940c99007140000611100b4a001d0503a09009034003600501161b42c5400700282d16018010007401360342001040441720400c1310802c4612865000700615100c50301c0700382d002c3c1d482d04a01260704010302105200e662003401110141c1c824080100f8020750b546941d54110003400410405026964031040a900080c40c45000b4010b580e95240c48180c4a45050800b1803801d4400c0e030004082918158800005c04c3c005000840240d0041d02c02007200b44000c0d500c1c61801d00c0c0350340015a414800708240e01e000d603005034046501d0342404125070b09001c640009008684c50130220b1804a40c034000344100140070940682100340c0101c00c10078020060030b010901801200c0800d607064162000b00144a282244410089040d500b00418a04540b07694004030405d4078084d04130701c0514141450302040000e85216134810010780c1582e2a000500c580301d60b0005444141150310052a14404116103e0070340a841d0842d584070240300414960 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 795524847 1250 795523597 795523613
    0x7020613050618010e010212190c0905041e1d07060306050915010c080d021c09030f110f0a150605090705070f060609020c0a0201020c01030b010e040509031b0c04110405030a 76
    0x6003c03404a9500c0d44d4407031200c00400e2010301062040040b00004170324101c152100c03c20842c0b0400d2411914048451600704d9018100c0300940d00240d86c00540c148020001e8120021030045032800103082284506105500301c440c00c1c0b032882d44200b1030300c18039111042507064580501403642c000210710300048070045112844030345c040043c10300b80445d00541d200d0240f48c0d80501c0c1c0da003d103203400054040046c25115100b2441c500e4130103041103070044541d00103201102d140e522804001c143d42c4100046442401800102400c1200701e6a4903082464000391300550300c100714452518280f00000c2178289441070324420913856403110720309500c80d61548800707035203040240c5000d031760b403400400c5101044c4010b018501481c0c00504035032001c1d2000a142c401010755460415080c81c2003180701c0d9801016034150b03254110f802181c41e40d550b8014a255024414420707243c030099641390780007903101003802c58003110151801c2c04810b1b45444180801d00c501e208072a0035901c05054800410015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 795526097 1250 795524847 795524881
    0x13050a0803062d1f020a110406230a051008010b0705150103051b24031302060a050a0f0c0c090b010908011d06060a0b040605030910090b070206130506 66
    0x1400c540c0c0b03901c480100071400c0103014101d64070448041110340c802e40303001c01004000702101215500c400001c800029100c0c402140014920002e400a07155681e59941000001d060207800c1503000410840070507203c101c041a07030ad4000c20b05681c002c10541050000344400c00d426460300c0186074602011169140d0005000f070300e03c0c0c00788280c2d0100e09220251114002d6006d200240075000060309006c079003940301048607109400c8100501c0f200140c8004900c80c580014102c29103964607042c0c118042039107031000a60008001a112490541100180030789000d6680c4150b480210b000c1c1c2a61101070000000e01265030301c240820003904503401c56a0201d6040c541000ca00e075840c043d203400d5508010565262550540404003090810420075138090f10032204015000e107842c00c03040b014410ba016000801c800000060504002007214444090078441e040254114505007078400c4141501d070040180565404070f54940c0001c5019040103400c01d0161005842d80150500146a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 795527347 1250 795526097 795526099
    0x10311060f0c0a080304150509100c02032118010501052d09010f0812070807031103042309060904051b01020709020301140102011b05270d05070303030513050a080306 73
    0x4010000d5424020f1180054240c41064003680f40d00b0285482030302d0f00a04d050310713030102d86400c040202d6060001058880c4400c42e03d13000032085400f0700d0032802c0d48201c150580f024000d82c130f5541c207400c407441e03641489203007410303075101c007125001a0380303800d9600078840d107503005291485401b1010060285681c010f1b40d40e080e00c940f1003010707074080348550b002644600512090740c907007084614024420114403a8000c1d8480e8a4501280c0d1120060300032404003408101031085294014042001103401402100c0c0e1070a4a512620110003456000c2c103031001d018020a0300401c0403030800c044418051a8001301902c00c1d88550309134010912901c28600f070462181c1500002e45141c030788000d50203015101c0040a481281d07100190a50344a1f40d1104c404c4801c450401c0380c4154032100303486044048201c04525842150f168003440e0500d454500c0e03202100460078000c21400060b441d003141d2207a1130034405035580e000c018866003150b000c0a030139a0098440c460005462400550340010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 795528597 1250 795527347 795527377
    0x20c090c07021e040c030903140f0c0a050a03090609060e04111c0504060c170a0f0207120806010810081f0906061e0812040504050406090b10031a01031106 68
    0x540d40009043e9881080100c4840d1100d084004803424580111100b40c550350405005051440d82c00070034901d00e0001c41185c040011801c0403c2c01c40d044115590032800c401180c14201c1075080060329501410340860216910260001710580a11007140407185a03403100704120001405100c09440b0340c40d00000c0e1103008001c4400041e60902c260740180e415600009041d19107840d05604a8041124040078440065180e0308441c0e42d188220750700001980001c40c5181340210428080d020700e003002005e403003940900d20803e03944071940510075102640c5140264903002c1104151404500803c11039070450390100c802c103c00601441021600d40c0d2001484941c00d46503a400c03540c007a044140c144542081e8401d02c4021052410301501c40d0002070903c01d1010002c492151189100d01400f0355101d100080501c036031940034020315a04803901e003109152411540b01542c0310740c0800c44020a1900e25412251003500007a4142e030341c01840d0015003403180007049401d0b0850f50301d07500c10070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 795529847 1250 795528597 795528607
    0x4050f071e0b28030e1207021530040308060a0f0902131205061e06031b0f0307090501050114070c060305060a090c0c1502190e011206080a0203120a020c090c 69
    0x10710f07201826000720034643ea00184404074000c100d81014a0310141c03c208502c140188005a52a407028034080141c0c650b250740d4070900842c2300340b0705034101c010088901080d40d00704055480d5a0031240c1c442c034420341d51020315a1702d110400c0260655801860210004c0103800c1c080706440c3d5000f0041d6400411004480980d100c05181c0000040c40f0100e40c607401c41c00500140510303208445c6084c040f10303e00450185080703000700340e40310101503100303074040c11000c0c0c1507010340c8802d0a10109201c000e400c2e5080c440c0c4a88921015003028410280050072449441d4207620342c58080d2a2510f51033200c0d102c0151070308404502409010b4401540500701c41d200103170042c440c0c422140203441381e45580c038400302e80e0308102202801000280c4107241c0100400b55091002421220541c02142420102002c400004a8015482c1040c8414031440c1045c04100900c0010f101c15000d4400c43c00c96400c41d10110220007540a45000c0c0030160b0700c10307603080800f0320f051a4059806040b61054500b00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 795531097 1250 795529847 795529897
    0x90604080a1215090c080f0c07030e0904030206060a0506120c130b04090b04050a0e0c0114090a060915140d05060d0611180621090a0b04050f071e0b 65
    0x202d00283c604000007594500030481190203019800030100c8606102c6c030b241c5001d500c0c0f42c00110b0003d000c401c05c1071001658608040c0a111685030b0340300d01500e1034180c1e01e0b05140c040e6072480c090301d01e544a5501c1c44000a101d00d040c03002c8450811002c0803101190329070501c00b05898000c64140c0d42d8418808002007840504c10004e00000e180854011601114120030300080b45c10244c80c4400031810b007414003a2030500081c628840c03076020f00e00340f00303041c8007188000d000380281e4404c3c691140d540c1000103511503100d2a0442031b154002031303d090707421283d48141e41040042da09480c00c1c0e0428002d02011640981c006644007a010740765003441c040c13035980e050450303600b10b003059201240403440c801094070b03108950703d00000036550710385030100d9080750016000d103541c01c850b090010140001d000c2d040c01d011031062140c0c800b5800c0140d0603e8600607440e003440d441c415400d4464024001044035134000c5400c1ca82030140c0e00b03011024144622904203601031403c5104104000e84a2088 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 795532347 1250 795531097 795531101
    0x1b0c020603091908190903120c0204090b0903091c02010915050d090c0e13020a090908090d060b1005070c12050a14010c030c0905090105240703030510080105090604080a12 75
    0x15910482886558002c999035200d42456216280000c00c000c0309418000180b03244c507955003203892270500744920801480054080c0003800c0c8000c00c03c6813000240701100071300201501000784200e880800c83c04031041112200080000003a0014038a0b203010812032041c41030880c2251903c0c0352091a2021894104054642c0070030b0894104100784000c1201108107802160420b545a0918a03d400c00740c002070000781d107034000e40070381590b0f0f40421020803600d00202c40451401610191103011030f403c20100910b6240a014002d43c48201c1044001d48110102c45040394044a82180b250030015400001c0d43c0941c0107d0341c0d40b140681c40c1002c10040001440032040100000c02c0d010400c1c417004056500031b5400c0400e20503814400d11166459103409415540c064800303401c14813146201c5040c03034001c42c9500d17058940008a10040c141e2640001d403088051020308c0d414a944c88003c1400c0700c1040383d4005c3c013a0402400b05001806c020300030200c0b0703204c52808844c002541001402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 795533597 1250 795532347 795532393
    0x21303080c100912030e1501090b030304080a150b0607050a08070821060f01020d1209030e0a140117010501020604030309060e0f0a0204060b030f0a090204060b0d050a1b0c02060309 79
    0xe0020f5450041e540c0d1305526014206910301a40040e0406490388081c084410074180500070000d52a040d103800c42c0d0700c0400541d030007040464121034842c10780d0b06000045601d9281c00c2030599050043e026581d01303101d012100342c170754000014203042e90307a502c070032000e0b0b0000c1c90101c1c0d04480800008000062814042c030602c010400d1404450801c03108001d03c45444501e11810354004203905015140c000c8865103400440c1d01c00450441c0f0189811140200743d140c54640c051840c200c04030311285403810700d42d480402038031200040200c0e488401d011003424469140168031610008000900c2a0440402c4074030414001c04c400422117410703401c11215200d01c01031540010300031420b5281600481c0000c2c001c507a082ea2450401486035040e0b02c00060080e0740030b9403620705950071502c0b01e40c41107006002149503d62034105003401c0c0b102510003514046090b03030038403146203140312801d07919440d00302e0103442e050103001140c0c3c240729464100408103074440c044c0c02c00c001180c41074100700c05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 795534847 1250 795533597 795533603
    0x1080102030f07020609070e04020a0b070818040605061c09020901081b0a082d010f0f1505030c1507050105280e0a031d12010c020d03021303080c1009 66
    0xd6100d16202c2d5014208460041800086500c4402484124800030910200b9500380610071145a034450001c540c002d001c9074402d034100c0e100019150300780f01c000d001510603a0841c881c0c070405403d14804202c00d0b00c00c0c038001ca40e8040c004100b1380a0725207440701c14112405845802142031440e540010320104001d902040d0980c110790800440769007000c40400c6120800c98120b0342207428240801d40d140c4162000c0240100d03043e100d86445a100b40d030b1491b4070301012009002d4001c0425040c00500380071a090500141041c502c2050702c421003c00c00c05807034000e80242422444a020006002c1c002459240100b50403c00680820000e004180c880c1c404103004440d880301c580701c001c280400750140d00645515100510345643c90100361102901d405141c80d03550301e0360a6281c1901070b10051511941f0440481001520800641203910309030519020780c0ca034542c18202c190180d20401c3c654020034440901c0c1480002c0200707018080741081e00c411070703121114000d50b01c012248141415 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 795536097 1250 795534847 795534851
    0x130e0601030e01061e06080f13050a060c09060e030331091104030b0117030405040b04020c06070801030c140f1306050d0303141302030c010f0212043002031b010207050603010801 78
    0x20720440403403503c0700030b210343d11f00703c6aa0700d80583d41ca00c913524080c0181e0410101c21003114107004080101048150b000f203c01c110417902c8602c05403c000da0307840f8a1b40801c94440c8101031074a004402c0e15070342004081c00319101542c4200d40e5612203001c0f418042c494619035800f2819070510720a6016080e1a00e54580e40c1d03900b941040141058160f20660050243d02c08659100310080f00f1b81d8101d8400740c401240305111400058080e000740b1006061a108207010444034035408920f0904890250400c0020b07076490310310310444486000c100715006441e40f5580340c141e0811820521440710042c0001502c280c03600f000400100b55404158006030b1504031304983e10040584041c0c102c403030b1203148814062160b02190b201c810200380103040c4580200194240c40c024003000c0640700140e0034542d662f507103c1040700c00307030007541100407803130000c480c02d090b200407034030120001c841d40080052040c41115058040b00c01040d18005045016503c4001500e8407440080c40c01b9080c40000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 795537347 1250 795536097 795536129
    0x90c090501050d170304020a0504020a0c02040c1e110f0313031505130f020415060c260712091503020705010e070608061005070b0c0301030c0b130e0601030e0106 71
    0x5840586906030030071841001c40082d0103002800c40340c10900003000704007100d610b90780c0705d00000b8108241c0e580700c1504540002003030803030325030703c1065589850f208507001c0107212040d0000701c8030841c0e40c0d43e00e0f2101d0401e0102d440c10081c052110714131036010210031107642c0303008900d03d41c0c119040f400525102d0600550207004107c1e071482e01d01e1301c42c10707600401c005500d81b550f142917010662100150200b840362a0f65002e640380c54001849c1c0c07100e0920b9250400c1e503510002014090140700685019001c0d042849038100350b00300800c034444a0326005810318110303032100b05034145000001814071003200000a0b44000031411b2800c00310042d140180c585c05603003049801c4d610a10566803164005050a00c00103400008051b0486000d44c0c04400c3d404442e07030103480c244900b9030090501071120003002110f064180007541a20700c54603a00d01c0b05a42c07224030760114020010319403000300522200380100402d0030a120740c480014034001c00c801407550207890840e40c141d00204421221442e03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 795538597 1250 795537347 795537359
    0x10e0708070605070302031903090209092109152101030308100632070b1305070803030f04060b0f180a0b0d02011d0d0b09030309100203061305060112090c 68
    0x41241d005041e1814001d1502d44c0d03a503402500ea2244000c810008086034000101c40c074400e900840700700d0380c05031a80440382042120190380b100c07a90000e4812510004040103480255016070702100c7c005003000340c000200c40b0000d1016004090010204001001844a11440194042e00071806501e901c092418210720640f00e600c50794010b1014820411003840003202c002040340700c3e401c1803032101034100c508085004036500c1241d00c0501841c150f00c0a0100c661142e1b0320501c1e016110b03038110b6030f40ca031b907520240f5100d010031034080c0c1c0058992030000e0042021074100d4074004900400f503801803030b2040c00158000c00c801c8200207484044804002810301c492140000c07020084a00c2d00750380842d503000800d080059a40d4440d5211550740c0d00200d43c03103952401c111140d00860f80e00c420318014216503601c1d0005c84108003030703100b5441d90350000081842200e02406028112180c0951419091800350030040c10707a504102c04001050302090b803034400c94010520400304407144515200e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 795539847 1250 795538597 795538603
    0x2604060e180105281e09230103061e11091002011b051e07051501060e0a090216050303070507020a0527090c13020d0513081812010e0708 60
    0x40400c1000d103811401408980d03195403201003020003003003c0804070500c05558210000d150350040178035400f105007035031201c000c65415a09590313040c60100702050b9070304e404246014100d11030841154030000144082036554101d60350200f50591409540b40007101c0d000c2c2220701240400010082c0420046c05901e800340d0281c030101c0c0140f0080c03241404220b402403440064401c914284440026900d2100841d280c081c08404005101207403260300c42c0c140b0030340701d0b003618018140c01700380c0d1400403403003e005001c00c841d50203010301940e5800b07080c035080300001d6005d03d180c02c211404030a402c50000304100029403080c205c1c0d50759151583c09920501030500b8041d04014807900107144248400480500c910300c814455800c24405516881c108500b8030350a162a1900400c00e11440c1c036521910340c0080c001403000c1c080401c025500d4042d0300ba46d5080c0c007034004080240801602c10524084035a080e91400020312911205070011045401c40c0d030300c2481c2410940290400f001202024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 795541097 1250 795539847 795539869
    0x9170d051506030a0b0a0e070e0918060a0903120618060e06060a05160b070c150902010e06030901230601030606021209150409050708060a0602070f032604060e 70
    0x300d00403a600785600001801d28000100004003d41d42c8141d2528540d40e891a44401009021040440703420b006c103000f13000c900d00c80d103050701070350819002c117011009109001860303810b1840038010310b45030f400d043c41c086c005d03180081e810419a40c02c0c0c11030444140c82480b00910074050302050b60201c80d05c0381c8050b01d80c20345c46004544e84c400c040001d19110b060031105121030300d00d007140d641c040401c05000c000303801034000350805900b4020012102e4004600300d084900034804c4001c20041104050103a0702d04140090002c4e01c114005c405e2400d1480140d9048141c4800100f000310180000342ea00407112020984840c01d0a024001c0d556090700c201ca002d82071920103050744520807801049148684100b0a000e1210b560201e41074103500d01c1030f01d014007210300051203541002c0c0e4009060007000c0e02c10a00c1080310800025243c0d00010b64401112500c400c6c66201e5403075500d0f2039145041c4d20815130248403041d09500c4070f1010060041002d065103482d0075001203898010300c400d81c030f05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 795542347 1250 795541097 795541111
    0x1e1101110406092c040317010e0717041110020109060c0521060a09050c07030f0906090b0c01110a09030308060d02150304050f07090c1115011809170d05 67
    0x400c0005120a40e400405003094460f4041d0203c071082a00d0101100003411005280c13946500c030080c0030401d036204601e0300040f050142405000c0e6201e201410105409641510205003d0100301d1422030b0040e14890f4814010200003c0d945002404101580d9400a0010040c0d45d039100180402c2034500c203101d8042498503040741414190202c3c2d4101e00700c00c010501500e912400000d5442d601d0710b2021001e0209800e083c003050030419403628054102e00e00490110b80640648a0f20f14402c814400480300c40da96850025854056001c04c80d6000180d03609065403104414510160f03004001c16180c0100d0f510540c49030f00d0750900800d003260150413980308102920360703180540d8a07200044080865070407010740d82d4a0b0340c50a03a14048200c1c82442c0307079004000c40000d104d00154401613146405846014000c40c07507861060721401c682807580a6201000010b1000000200500c200300e80a900c0c00a900401a21408100b44006030400440c900011b8803603011005c0340101500452 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 795543597 1250 795542347 795542381
    0x9130318050319060905033412050706060302060f040602060a0e03120c2a100b0303030a0b06070606150e100c151409010b09060102070303020c0609011e1101 69
    0x1080c400025141c00309043c1c2401c00040c0c201e01107051213002d42c0001401ca0f17004003125a40d220150803003186503000b500317207425008a010080310100d08125082555a4448035840160111010568680c0c0010f60240d50b515a105004801031311040003d14821403c440780507180c610b0b03c0c0c0000d08d400d500601000e81607040c01035200340d10400109a4400d643c0303200b40d0250603500c40f44801491f00900c05114100403503140303280b0305040349000540141d03c0c0c030010ba4502c40c0a2098110030340301568001303a050340c001c1000902e048603d034441d440d2140001d22082c070300812038840d4026160a07400030360b856003100103501d46c2c141d04451071807805034054920484011560318060034045045102030301c0c4c8082020708840c844da007940300d01032020364425000801c1c203002007030300c0c020404803442c41e00850401010510640c0001140800c50354140c1c014201e90000b0b0b000e000541c0c016400c02e9041c00361441d8054007520b152403000c0741c0b485440e6034900b49075007000051402d542400a103c64250 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 795544847 1250 795543597 795543599
    0x80711030f0c010c1406100303020c0f0f100e0333060603041101050d0e0a0b0a1e02070218010e10090c120216060501060f0905040b0a050909070509130318 68
    0x20303101245419078400300342440c038112801c030700317210700d90403055161043c00c1c0c0103a008121501035401902000d49000742c1c200c981c21140703441440000072982c1615613002c0455220511a864010f401d013400b0659490714041c2d241c00d50b03010034580710003040c10007410141e10072207825a61070f031303000e036034a80e401c0113003041032414140e020410502c40900007602019003032240707a9241e401903003100e005400d02c1004010350080059266110707800c140d03007101c0145040022031029010341c011860b0341000769800710314451490005c0c0c002980981d000b26042000c2c0400c80d10a43c000c4011035008000c080028542864503056650b500c20b503607040b125041d49008480510298064960030b10304001c05401a1f80301c0c11140e40c0500c2d0314194100400c000d0420001244d250751100303440c0c003401e94a8491a082c0c545480402080c2c4404024117a048086084100f01c1440c0140c00c2c290406860b0040d43c1e0100e440d44042410004122000780741c00140c4820041010303400f00d03501084140040260040d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 795546097 1250 795544847 795544873
    0x121a1501050a0e04090210030204140a050f011206050402120108060f040c060c020111061f0f06120c03020702030a230102090a120c15091508040210081801060308071103 74
    0x150140b400560200a003214100c0300e40c0c2c139181e00020b8001d80040504018150242004000e94014029101c450110156060450400302003200968000a00032198990000c0044070303404030001300410180c4c0c85040c0010340d43c43d02e20040070700d42902080c0306555810000304a28201d40580b24160b81c01c40d0070204000300711503100d043c0540d01c0500d03105245801c28001246c0700590a2034040c20380c06004103102c42180c0480e0480e640c01c2007603801e4120f480c0e4805403910007010600c5031b031002c1004214244c0d0440d0580d030011886c5081c03820300608200458010034039203502d06404403000c411800c00d009844a185142a4189040c1402985400300301e1001c0b4040b1403262045e03003e10b22001e0240d104010000300c246000e00a41c005c650840200d0301c000401207580c2d44905481100104111590684204480382c4101d401616804800000302012181c0040050030001a460701080c0050030345030a000b003000550103400c4458a4000070305044041c81c00c100e040728881c1d88212120981 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 795547347 1250 795546097 795546107
    0x406090c350303040b42030a02011e0228020901080f1b060d0c0305102738100527030304081212090601060c1502040e190e0c0609040213121a1501 64
    0x2040c100bc1e1050080c3e0092203007079140c00d4a50701c0760040f502c3d101d000c03da4420740070707440a250140200d460703500b1a641c94002d40d40711490511095000d8000810500340703889080c0d00342c011600e001d403a003450031005405841c221400300b41c050300020340341e074103108140d071441641d5005042079245082004800d080006a00300800c1c540c40d40e0291100744401c440301e01102c0803a0380081748641d0007821001c0780500d8141c60004400c0a200e454600c00d0741e000ca0703100324103540e4404200030004460704600c00ca217441c0d403218041d0240e410302c410803020500c8901440340c005030700e89400501c2d03103d05040203070500e110300082c0b0078256907001c3c100400220354083c0b03006003100e82020840b1005500f07102c03190080c1c17007076400003090040440d05114001000c01e08400310029551000c2002c00d0881310401e03211500c03050016445001400350540503e410390040c81c1001404062001e0280c0d126080702203010700c12030940d60040715540c420494a0040409907200c1002803401e00f100c25200c2c00a0b01e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 795548597 1250 795547347 795547367
    0x20a0f03091a0f01061713140a0c08070603111201182a020c0301150b0a050d0c0507050f0606030706080406090c350303040b42030a0201 60
    0x8205511031448409104210807071488202051100801e01c1c6403083c8a03c0d00308400b03105140010350391200c40c0404040d46840341c3c0c000d084941c1d0360084111180c0f21520240585448102140200c0c080c20001400f011030351001004203902500d01245400e101600b128410b598243c4034046c00c0102c048881c0b0215180c1c0c1c191f80056066901c0c80e40402e0700311300141240b80c0820461201c00d007641c3d03c10410304603040c0320703003075140e084505040120042c0760998510b500e84141900311507000b0b0110040d05400b82c2807820075441c050741440c0720594840305460702221500b010500006000003441001d114034a44403003054000e202a0030310101080d66000c2d81d100703980030819920003140801401e03410240a160b04003224110058490380c0c1c0035000a1400300520906d0a038105440c600d6254240c0c441c0c501e0820f5024604556850700c0c1c401001c4401051510304107145020300264801e0000039010036802c50b10920f8040e9062529200b42038000ea445600c0381d805078180c0001030b0384c0003060300303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 795549847 1250 795548597 795548627
    0xa0b07060c091e0311010e030601030602090301090515011a040303051e0d0903030606091d04020613080607050c01050a020903030d0b0a12030c0512040b0d0218060c0a05070801020a 79
    0x1000c01000c0002c50b900785598112441444040564440ea0b02401d000c10040d2401070100e54591400c060056540b40c0e101d90002c2d406800c0100100085802e44d406080b10040140001c5101d0340f843c3e941a09202c1540b4030090300a8026005100e017841c206134031140c032003c4151039440d050035034601600500900d4401c0388070f81d0300340d0005281603180d07000782c409000181000707001541203071071701a02400c5c9500071040011844440014010000c850a00e4559a07000201d0b40f00e46458091100c03e501089000400c20031106000409440400206101d00c1d40c60b0346158890441880c1d2a0a45101414107a82c4500520010142d0350b0084104c40048035504070006219800c4004200703100c070399070310000082600b014840c061541040384030b03074ac0300d2042d01520540b0340d0440708440c182c01280559105082c0600100005103e19402444c16040c40009504082000c8000901c03561116604035007580024514008100c2c1c20480c5a006c3c0c4103100003903041c01e003003070300040052000c0c030452 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 795551097 1250 795549847 795549851
    0x31609050c040306060611011b0c0201083c1021061d1e030703050406050d0f0603140c010305010308030a1505090c0406081608131505070e030c0a0b0706 67
    0x455100200c9500b00c400542d0b0000f000c0c860a691204054000c00b50000450b400d5401c1407011b0421808030380300070340c020405450312403040711550011a40d03160011310380300449030408408070700b0305000d2440000c440351941120904050301c0e42d042a000f44042c0218040b101c4501d014031040040c400c04400d04000b203105a0320650303c1e82040400340c81201705050345800c0005480d64000e1000c07540c031032201d02210015142030850458240c0d244220080a40001d40521090103218030410050001d40d10422001c2800b14109849008941282d8022585414081c1a4000c2c0050500c044841071409007801c000070741c134648400e91240710041581c0c0035203030b88003021540d0f03c15100342c000c007070040981200d100d441d186810182923441402110081144c0000003030071140340502c2c200001c41d240e82c600b40749032100214000c0709603091604540c00c61525000c0349055403644121445001c0c60341c4e802c90400c031701c0030505007080c1454000314064080f2042c1030203410035100c211681716a1010740 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 795552347 1250 795551097 795551101
    0x9060a05070c0f0b150a0308030a09030c0512180906090601030e01020c06010b1201170d0c06020d1e060506040e160c05070305010603061d0d030e12071b0503160905 72
    0x1c02c0325581e80c0703840010100b401020194081c000100304217440768250f602410100c00d481030400406003a24480245044810070005101003101d4003c501528400e00342801d95483c00ea803640e0070103255a40000410201184200c0a4044118500b01c1100140c0c0c00403400e08280780480c0100c0b100510b000c0c14142c4440404840c044d095040341c903080d286000703a0350203507110768030b1540d03507806521900d614514840c008a130360a80c2c49040126517407400300805d07500501d11802c0c7c0321045d000b031003541c1e515401e00c8036140309070460051211161803c0c1e040c100d64940c41e646841218101d4010b2400348809010501c14002c0451100350440040003075000041120142103400c0300b01c8910040150180040c000200401500a18103480c03003004140507103220004101015071030440014101e520407507641e401d40780654090031035940510103903450680200d10040055101d1070040b5407801c048140320081c1200c403441c040c0941000c90207018851a00c03100d5000507a5103015003407406a81d400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 795553597 1250 795552347 795552361
    0x606041812141317060901020909010e070207090e0303060315060a031103010e2512170a14031009050a0606140a121e0c0c020603160e0a0806061809060a05 68
    0x20603520201e02c03090f400000310b40c840824009000b02c3e43c05000091003400041540b110040c02075031091075001e001c0c0c041c240c0c642801c5406e0100702610080550003445404600315a00340100c07208085190015560707030030b0400030706107045014251b4540e6469240280003460743d409601c04205c2e900039030140038210142d0000781c01090821405155481914089030700100b69680034900d0034200710004000c181d5845884027888003004e001000780b000800c54048216014000d00044d1800e481c4c2007100c4241e50203800903980c000d03034880860180b41c170400c02182150b4042c2641c094980d90048c846240341c00d602801801c1083c02440d07a8802c00305290343c52600c5040f480d099101e403410705111038110009511800364212614074070540c181140e43d080b450046084601450b400751415245507250380b844ca100c41e0115410208011040c40e0259150740c498a01d1000f820f8150003034901820000e0400084040c003000301c20841404c4000c10052440101e0200d41c0040000303404100755880e0300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 795554847 1250 795553597 795553637
    0x50703090e0a0902121209010813020a030c180209150f0c0a0605011a0c0c040e0a0b04050708010e0a110d0201030b04020c060103050d031a12070509090606041812 71
    0x9000072030a02490310402c48a9031180d00201003042c002c0e43c0c0072204d4600b030040b00d034803000c0c0400b00f50300780401003021000d254441c00d00030b0740c072100c80d0a07180c2e2841c0096000403443c04580e803082d1200680c00c2c50a00c001e0b00d074540303c3c802030b014940045180144000101d680360203c00030480e9a1240400e11005680e0f03140d0840350844010b100381c4000d24400d145c1030000342800c1c024910480f5501d04103640d4904101d0031a65000030030401000128070716810440640001d4104200302d000d0700c8454000100a144424015889100035106450400f8007250031900c1d5481200c4880c0d021001d10030200f815501c0f0400010410354803841c0312500c0703000580103803080003c0c21307802074070000308684801320204646059034421415207210841c201d00407019252915218116001ca0541c5842c20b49031281450940200ca501075448080d5070f072000810507102120305071035542040d0108180c0e45030910031440413141400c07810b80b00f8200b903100c01c000a815150070b4410b00c1103414450218002e80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 795556097 1250 795554847 795554849
    0x201111005251b1a0a0c09050d0218150d200a0308030f04051204140108060303030c0412021807080a051b0307030e071502010906060f0e040206030c0f030114100f0f05070309 76
    0xb80030140c130b480c01c03e109140000c008000c0d01a000803102a004a0113280c240d0502080c2c1d500106802900c3d2481700f90b045a03000082c094014003840c400056105468a900359806240a0100b4480d250244040c1d200041040c1c03014520070301b040764007840018421410780f5000380954803502000c0d5130701e191051400c17035031810401888030b000c1400a000c00039014030590504082e032303841030507444010074950359000658101c116500305020a0103900c80010598a0403030005002c001d030040d4085d550020341c41c0030366590b80000d5103402004607400541c000d254002080a603c0a00e003030305c0c170382214098000034100c0d4041645500b62804e26610800210380905000c407000c40c142d0040000107402420041c03000c0b0741007400d00c100000d00c0c4003100010303000c6900b00002c0c680035658560030040c142e403009105030780303441d01881200d598600b814080c2d40600303401c01c00051424001400c10001d03000c0d007001c100c2009010040b840761550700c00a50b4801e0a40d034100603480d5409458227960120751 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 795557347 1250 795556097 795556133
    0xa08040320042a09150e03010f050c090a060c170306210303091018020105090117010306141305150601050c0f0102040609060512130201111005251b 65
    0x5140500b85007080c03d6155a16125140c00303408004030010600f81c41c400c0740e62081e10703400200c0702488203003213001c0d400305450b00c1c100400000300792164056400c101c410030b0b10100300044d0003140c031410324181101c00c40060a003d0910603030003074040c1d851240170f50402c03101c2c590219000c400301d5a82e441d029415000601c0c0b2034072120808108001032540c9030000c0b03528000c144035502004031410700038400c001e94162000c058800c6a1955001580d155200c2819503041103a4841c05801840c50000c00d02e001e5441601c01088186030b400810a4481025203d4449404810f00007000038200040700b030082c90700c504402801d640c1c4c00300180c50900440300715114a01405c140554084d0041d40280150761080d2070300c5500a440b11012620350280156410001700807001160f400b9000300080040e5a20500d020342c1c0088050301c00d40c1c00c0c1040c00740030301c80d460748907014011541c080000c0c042202500b0003545e00e04036240000103161168150f820313032828503a43c6031001880915038481c805504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 795558597 1250 795557347 795557351
    0x7080904022b0b0a05030a080c030f0d0608010f0b0607060509070b0714070b07020a140a0f030605090d08091504062315060f03010e0624070c05030a0804032004 70
    0x940d441840e0b107000b9088a421800d82c90440540028980812050306503600a0000c6c008402d5075078501185074026807020129100901c80b412074004000c0040c04c000f810a00089041850301d02300b1401d40702c1f026003411000b814840b0841f580c2d2103000964000b03d4109402103215119001c0040c00c0c4400c0d6001004441400103600050050080641c540041a00203c03040070790b45445071280c0e8000c0400080d0700070303110b44080045800c09a001c00c01048018802e0400b1751761420000d210040560086807081d40362001c11a203204144a12449000b584c02c1c86451442c002452a440e4203280c0d4400340440325110100b000d21801d0350240c50f0b2000c1d000e102c400f42c982c080328000140e480c1102c40c24018100ca440c5030025080c100c003590100801d604019086034200780d40c2c03501d9820001c00a030703081f1102540c0d444424120900c2c42c0070f820b500240aa07903c846500385034a0556444e0481d0340a68440c0e2840c5000510313010403501106e030007450403400c28440040740f1030004881c1c166640d10034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 795559847 1250 795558597 795558637
    0x60307030b090a0603082709010f1805060307060f050d02160b0a0903050304060908090d081921090f0501020a050a030b0d031e030906052a0c030708090402 68
    0x69003551284030600021544200303140d540b5000304064520030b0000070b0441c1c5003071001c00400000d29029101180d1808002403100301c5803404566465001d0b40b1021901c20050010000c02d81e40d60601e400d031004180741800549850700109607141e007148155010043c0503070305018001d100d141540ea1009030317490706541c0c400070790300011080e03d0760701401c0e07401c42507560210300b1b010a5485007041440d0305480303071421540c0340d03107450b0f0041c800750009035000340c1c00704501034440d5166046001500d00c0703800143c0c2c5410b0072403c289150f60907001100300380841d504108454003440c081122145d03220060203d0411900d142965401101c090003d00035070020940b400340c40e4000014180741e01880c2d400304142e004000400c9600c4682d4030015000c60703104039102d8a02d00e004d00c00c85031072103440d090101b2200c44607601c2170700b15201203070080c0043c21510100c0410316502c400d01e2403402c580c0041d907824141215443c030b8a03403040c01c00c010400714000500320400c0c1c589406461410701c0a402d540300740 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 795561097 1250 795559847 795559861
    0xf0103080309210703030b030a0c0e070e041b0206090f0318190308040504050a09022202160b040507090c051603030b0a0e06150c03040909020316150f1e1d0603 70
    0x3e41c00c003180480c00700c0e0910328104018107000524031784441c1c101c0015814a45007120300380c410800500700070100b180b01d81044401b070b200c0380502540d10140340301c04d002035007420704001e0038410041c080104541000d040360608241c00819500340b00128140100707441d60300c000250511109000c05400708802034400418003104802500413a40185d50502a13640e8500d100e03012603a051a00030b51290035500c02204203454000e11210755000c094006140842c09644200d030310200b00000c8408011400400c010440305102e013000501c550b004c00c0c4004c0f8412800a0720901070512a8656940b11004240915220743c02c5034802c803c0c00f9101007c800d890340c40740e001000c01202c00c039008142403031070b240d41d05404c00200c0e45080e49030001b841c201420140540054210000305903070502c105600d2070b00340c007102c50403480105900c2d01c0c50034002c624510301030083d07540149400140b10f03c1010761509606c4802c0c0d40800300707100b860040c2000d8402c3c40e001c00d11660290711580c0181c408400c0101e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 795562347 1250 795561097 795561163
    0x615030b0907031a01120605040203010f060b0d06080606010507030f090e0a0506040e0c0a051e060a080105010807030203040f0305030402061b030a0219020f061c1103070806090f0103080309 83
    0xb0f0302c0c002c0002c4500c0400c1c4440000c000803082c45501007105042000d1408108240e1190f60402d10082c004900c00604164040503560650000840850001b44070f0b02c40c040d95100c1c0100900404e00503090601d0408006040350080d0030b005001c1c0724480f00603000300b41c4140416005014840100c034524200409464000e01d0101d0350f2600a03440c10413102d0100e18001090100340000900e03450301c41e410034050041d14401640015003440350104a0141c2c0d58801c40030306200076143d40e40d00e1283d89804001010501c0161080041c18410800d00c0003180100c40070000e002e40505005540352600d00c003141c0c5901c20a402c4400000324801c80c0880110040002c0030440180d6080710b91100505085214000a4900081d40140300d81010042c0b410101c0140200c07201103921060f5030390f01d00310a50150350f1120290070b80c1c0c500020420120541140c45d85801c0a4103540d035802c2e5140420322000e00b540c041c0805001c403440800010042d0100704000f510a104860314225000c485200c0c582c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 795563597 1250 795562347 795562349
    0x12020102040f0e04020a061b1a060a06080c03010b1602060d0615140909040f02280e0c0d09020609220507030509071503062d090204060c0615030b0907 66
    0x1000c030903000102003c80c102824010381e00100107140640c0b40c0702c02030f2810580c0113014140c48408031040c07070103c0c02442c04a000b00b100e520054800345848010060107103443d8001e5418045c0940c14084030070b00b0101681d05452440e02540d580f8180c0701020500034403800c100035072081c0c0003e1206841c08264200c1c008803041d40020350190b0b808510160340308003411944111040301440420250300d401c4003110341250140441100740503c81d0082030304c5c0c030178103a151410442d21054101d0310f07040c0444180002d100d260301f00752607418540e45112180c81082d0001000310348030051142507503117180444076000d000411605100081810b08590701a006026484c10b80ca02000660302c02d01a000e41485170009001408003a401e0101081c40d0100383e010940402d5513030000480e0359441d02041c5800c0071032926801034075290b8001c61003c002804e030000d00450303006000402c1a150410710408a042e400f450100782800080b5103d00f00c080d1640c8040c000d2102001401805000495228 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 795564847 1250 795563597 795563609
    0x304030c080d09050c0f0f19050409080406080a020a080601030b12070611100510031401140a0b2403012601090f0c06031109010c03020c0a03110a050406030f08070c031202010204 78
    0x50704005a04104800d071128950038503001f50a00c8842d812900d00211034201c1c040300c0308542e414154444010500b1528401d50840f5050f400107004c1c08140e80141046520a25440c0150f282c4078070020010300c0b5040280059051545030190741459940f032a0003d202c1709400011902500c2e92041300422640060403a00080d008a01144503008950301a092140b01010321482c252851591040b000c0181e001c0900115540d5000d0b415100e0402014640220421500428130f007000c18100a282881d002500d031092801d48040c1d00654460410789044500c115481d06c4010104012140e0f03040c24170f1240324070340d4038003001c51042100340c038500304ad001c0c01089030000254440b80140c04684c9410480404220140002360071984105640c4003594428415501c000c8001404a8403401061300b00b101c0602050720020070f07034140a600d1200420080780d0a01c089483c40d160140120074140020b44034807000a11801408600050344c07008540c0051788406038444540024000e4010740511 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 795566097 1250 795564847 795564853
    0x105070314010503060403111219090b0310050603090c0d0c1e06140a0c050604050607020111090913030504050604090506030715020d080a0b0a030317180a03050304030c080d0905 78
    0x203016000707544924161a4083c0051925850710740742070701d400801e2418602103101e10b03401e090001d090328000d01854440c0d2006400e0445070f043d0050001c0280c0e8101405140040c000c1048101011451070122181035030116079036213801c843e0f9410302e0402401c16400202c10075507001040382882c905411a4548a000403039510340f04d5040102020302d1103150006a501c0c620048c5801c0000c00421504510b410700450b002c10503600da070f04040c0d0440e81a07800382c200c00100414240c080c017483c81c84924041d11580740a8600c00000c1c061b2401600e007440780c00102c0104400c0500880c1160007400f0000d054545803540c604850020f00411a012400382c0207081c00040c2080105800039445016500580310600107610308941d8004001d100c1040c8d1901c07a018412241c40d5007041401460081e0f031005441064850301c0c44040901514508680c1c0b18900030602000c4081044c294043d40344c9001d43d031300c0d11035040481d00448580406003001d500081c2c130017512045070f845540b84510800603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 795567347 1250 795566097 795566111
    0x3030503011a040e0403050d091203050a0c020705030706200f06040c050a05010c3509040b0306070203090d1b06110f0d120e030708070609020117040c0314011d01050703 74
    0x1003211207010f20b01c5460080400301c40410b00190084003d00a9400f110350001a03060046c0c581424540c0712800480100b5512020700242208034010b54510344541d0004180e213900d044080390740e07032100344961400c014080801305828410144092555282c60089889800d03000400d26258401590f00315442046074038005014100400c0c0340088070707016128110a07806036154120950b13040c543c03200c4c04480760300c6030045010690702d50007156881110050f8641c100b400900044a94510010b07103e5070080d801c100300e0f1a800800c8841039407003599030071482901407400c0d440001c44407070b111800c1e5556040100d54141c1c0300301002085451390045841c0324000700c0c0d0154445400080810004801100f511212001900070209511984044914141980e1200741c00c9400c502030071100b079602c0d008000c0c150340c0d004442c3c00e0407400d1040da20a00d0704042d80d644804464a100060034100030200076010002c003940306444049075408002500070070940c04a000f010200c826401091403d04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 795568597 1250 795567347 795567389
    0xf1b1005060a080f071802120703020a03060f03081602030f0a080a0906210e03040306050f060f06030705070b060406120f0c080c0a0b0904021b010902180c030604110904060303050301 80
    0x2a100d08a00148029090050625500c2944401c1a903003000211387c08201c9050650390300c1e140e162059142d568010780f180303801070008007a580a42c0c0502500750b16210140041180c81084038803000210440e05403900d0b0620100c2d0a1100000c82403405004200c955814403100500801800801d6940e02c4c2c003180d110f040a0300c0721070802c10f01095140703c0400781d140341e0205603c5186490000d00890741031940c0c82d070303c10080e04c40895030081c081c11035000b031100c01d0901c0c01c0c154007007003400c0380e0701381c1103140038580200b0074012110b02030300c24032190340820541d489540c080005807111030300c0010f0880303150a04d090f00f0380100004031451510103a00060032030003c0381d400200382005050741081c81c036240ba108180c1d00000c003043e5000c3d900300080e40001c0c02c04061000703004d12400000c036890391a0700410001403800e035820340205844000308180017941c08212036000504607070019030101121410b0200b4001e00304859003003481c4c1100030040c10382010240d4101d1349280340c40070104020407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 795569847 1250 795568597 795568603
    0x2113080703121812020f010210110705070906030f1118040305032a090607081605100b0301050f180c030d090306050c070201090308160c0b120a09080f1b1005060a08 72
    0x3104184c421070229090b0001490007404000080ca030500c122418124100c0e1408c00310307807401141c500c0c4440b001810604014050100500030002c104040050b5480c50311072041c500c4503914020203109800020012607903c41040e41c03000c0701290342500e210b240625001c0d01d2580280c0700340f81d20744403151002503405c050564500d4101ba8400000c0c6c05c241c0324000f481207e4000e139100b1908490b05000da0f10340c502d25107950b80c40d41030144008242103001140410304641c203039510180030364104010030400404130610030303030000d10b94119075a800c010b2740e855a05050300b0114550f170600030140b11303c100c254030078501c03826280a400104419224517102a0345172140c0f680090202d4501081000800e4066010b0280a103582000f4101c99900b507035901c0c0031851a0304840610325022480720403426440074800e81c081c0251a0811008001d5100d254250060440345048100c0c005000212400b41e001031010300380c003401c11155007818a16040300a0038045070f5441c0900303c1a04d0000c0c00750800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 795571097 1250 795569847 795569849
    0x2190807170118020702010309300809060612190b0a060824060d0507230102030306030a0b060d080309060414030f04091104030b180d0221130807031218 67
    0x40c1200340058202c40c103d20000c0c3d00085410b905041c0d40c3e0345480302080402e030100303401c42c0145110f03140d003480c111032511280c8202c50b0541304000d078031010442d460100103040c0340c11410440d1011048410000c1f11884c01c906495604030b04407074a03042c4010054206103450140404540034061f05450340c491a5440f188040d10300c0488140d0020000220fa250540741d0b000390015080600500082c1c43d264942101a0310524551641040d034450b0b0b01410205d8050191092011310b14505065000a9940b4000b5001400b519105000308049aa44003410354803141d010724296202e1406e024041e444a0b0100da0a69007000300c110001c044c07002c0442100c1980d41d103d8080d5040908006214008000c030010320341800d00200004000701c0c0d82480e030f191213201c840f0f02d048185400c1a000a0401c000c0c00e444c901994000514030402825401e40860880c0480301c0c03490700c80000302c1c0f0060080181354426500d0380100d0300084280030403540c2c510f002c03c02e1501c0d9003421070081102e0141e880c4403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 795572347 1250 795571097 795571109
    0x90201020a0b09070518090105130b06120f0f010209040e0d05041215020f07020a2414130807080c06030f04030c0501110d060f120b011503021908071701 67
    0x1041d180c00c80054100704035140c0180c40101181e0f0801e403181c0c041903019200c1c58110f6001e1103810100101c5a01c24005d440e884102100c0180d8040c5403a62003150070003000c1c0c050b5120b07e054224840b40c3e42c00401c0701d10412a1040202d5920100c40d01c000c0d8000c2d0720800025014600304440307120f80000016194400c0600b5036a4945010310301061580c1d46207128a0454036081419401310700420380340081d01305c400790110034965580240c070401003107120361350109255414076a11601110f054030134400180c445810240100044880d40c2080c03880350046450350780c000d007900841d107000c00190050548607100d04035414050000d0410089000c100d03541800124043c0004000a01c03030390305411098890790004c21902c03580103103103482d500040e6407528219601c000c200040c0080e80e20000c000d00c011301d406100408070b0b4507207100f10300050080800c10f511030f104100d41c00e48264101c5903041d0443d21808905101010000c05d100000c0d101c010000e0305441c0c6030b80301c203441204403604840c2c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 795573597 1250 795572347 795572353
    0xc0e0910081c030204090207110f010c110d060603021215251b0209040809030c01050924040803030109021c1503260c060105040c020d090b0f040b0a0f030f09020102 72
    0x10610880c4089002d02c04205410542c09020000f00c541c0f85001616846100d903c1254080802e00c043c098807102c5004441d041182280c48040031500000101031040d0041e40d800d500d81d001410301034042c0c00981c2c80250030860070524185c4010010403034400d040700c2481c20141607200c05003000c842c005042c20540e00c1c0d034180302d11000510700801042083c2141100c141605002c40d4000503414401120150f5602c40c00040324119450203001e0148041c2e404d003055418804088003140541c0200349030151343c107880880d5400c28840e40c00a660003403414100f00c03039407503071144483c1010b0b4214a58420030b800300400b040030b00e21414003031131410050369495110101c0c03454990002a1a000c0b4043e00070140d0303d00f00034043c002c00001070a100f001d1070014880e07945014140300c101c0b04582c10300b008540140042d0008680d0006842040300e441d250b480391903100c182c80882c1da0780308591000c01d80301ca00150311204c440d0002d14203c2c20b40c4480d24200f0840c05070b0100c0b401074440f0200000d005030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 795574847 1250 795573597 795573613
    0x1021305030708060a2c0705030c18040f0c0b031009050610050a200d0305090d05071a09010f05042009090c0409080403050a0c031b061e0c060c0e091008 67
    0x60010384c8002c960008600702000070700c01b012034010100c490b4400145403a08005014082401c0401c211550307004280c40044025840381101d69080b84080c000070110305041c0078400900c440818000090b141030780459940c0e0410002c2907042d170081c0e201d41c000d481e0070310000907039a181c04408020459801d455a0740b800c01500400c9071102604251101600c0241c82c5072101803504200c800000000c6403000103a500700742a40910380950071003101e0402508110310300018004080c020550307654104050319940318a0300207805803003400d5104d80d0403880c03d001c000600a4082060794004914082158614070b401c081c0021041d045034000e00340d0344003045100321801c00e42c4c0315501550040e440c542c101600d0b42e44a50030b05004040a4908000310103040c81880081490200705d42415011140c00750300c0c10401800c0ca400c80500c18025507400c1003071000140c002d0700702045580c0d204d403007080700f54880c0c3e0014101042c0c850480d03018100c0e1310b000540d081030081030141034505a02c0200905 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 795576097 1250 795574847 795574861
    0xf0921030a0c170c1e030403050a0807210c0e03060f150f0909030c24061302190225300c060207140303120a022a0102130503070806 58
    0x9810301101080802180c5810b500e4444504541540283e03600440c507642d514440c1e0040c0b03900340c0d0112400c42440f17410418040060b0304003044076406441420089545e0359091015612a03003c0030412560f0a885240038240d00b08079445800354000688036201d08000b00014140d880704200c8111440c00c401c00041071a0b6080c0081c1c2c034550240080403141c0c00000350010803400c102c00c0d15005016440421300c141c0150f800e204800308012000b42d80395619000020145220070043d1807280100348059181c01c0001ca107404446100c5401c03905500203d1060034002d584040c2c0c0c49811550003101180000d042079082c46681c00c0301c0030030460f009403000306074084041409034002592481c4050f60110006015801054020812600542041c0385404002020320104018851081e00104109031030000030b83c1c84d081c1c1002e41200c005071242003240a0610014801c0d000310014111104040c1150308150000d081404000480704c003056500d2050582d11409402200c2e401c0c0c100800280c0c1c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 795577347 1250 795576097 795576101
    0x60810090f0f090803160c03080a0b0103061e03150902032a100201150b030403020d030c0e06160c0b0708040e1906060c0b100b0714030f030f0921030a 66
    0x408001d0100014044000300c0b24404a074244101118400c1e404020401c076020382e204040703101181c034201000300c007505580003007120300001e01c42405c8558508801003207034440d500c80c1025108840c0400180d150300004002050344e5032208494203d056070b130561940425006d03192840713a01034010f0080340c1840c10480c41e001c002c40c80402a0348418009420f41d5078441070000054102900000381131504800c8010a07910135410001101c030082080c40002036000400f01500e06461400291800c2c5108049540c410509403041e80f00c4408240c2e445103100d01003c03209a5032042007185072050381c2d90180fa006000d1303020003918000080c001000074540001c1095030042140e0744104000c080c0200d41e030112805900100300003458282c802080080040d030b42c03a00103100070012030100d440c0484032001880355003402400498140404810603d040003900c1e1240914043e0b543c5918180f03200c00300c604030072240710b400c0d4495401c1c142c180011005020780c1d80404125100c2c0b45569400d05000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 795578597 1250 795577347 795577361
    0x6090509130c03240b0604030b10180b09090705030a0b040f020303040e0103060b01090e01060c060914030306100302251103010507030b010314220312060609030c06081009 75
    0x540c01d803036008440000303040030520000303548a444109403032a03081200e101342c003011140c10480d4030f182c04084c08107940c8000999040b26071184084000d0380e90600002080c040c2c5510160800e129030000a03c645030035040f540a031041580d10300226a200042c5d103648000728454039400d42c1103200c41202241000301070ba43d0090040301c0c0004040c002d580824516402588036144528040d4014404c0101d13074000c006008401f460100b03079540c10403601801014040c896901030102041c5074004100003a081513140c4c0c2d40203001c0400f103c14006a4a80b00d0b0700480d405c0e07205200310b602942c0818020710950302084003c001d60898280d81115600082009103030a6824900b000c00403440b6650900405114483c26a07000c1445041640050195807580f0103c0c60706520030340403c000c14156a50048044004d44020198807003113050555030014090405d41815041020101d05c00c0c0e0814810700c126403007440c1444041d80c0e9000c080ba12444155840213100d849144104030804980e00049 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 795579847 1250 795578597 795578611
    0x2103151f0f0e060a0e030a0f05061e06210c040203011415070507090507030e0102180a231c1205032d0a0905030f040e06030c04060b31030803040605060103020406090509 74
    0x21f80250203580b140342120481c1c580444803640803000708151900c0056142403841c0c50035005084030308008001845050010f80313606031940c5298038001d50780c042040f0000003405d0240046540b0b50310392550103064660350039010702405d40401c40000d41440c010841e600160007201030200380e1b0400c01e120000d880d01038011801c0645610052040c03010070700c020800c00316012101c034040030f8032000340040d040403640400b8100f1190f042400c05c9005094004516403404c4481507002d0003080c4500740480c0d584a4050101000816180c880c650031500450040528010300340c1c5076140c4492401480c1c0705062070700c0c41207041320042081c0710019000003440511402c142c13420507210b440b0200c11a009940081c00030340c4c58009000481c00c042c44500941c01098030248000307803d00b070740f00509200315109481760540880e00020700080001c04058a541808004026a643c074140a01950030554060315114980004500ba0358020f108442c01c4543c01e440703489a1714542406c100103000010144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 795581097 1250 795579847 795579853
    0x306070f082406030a020d0606030e120f0c0a050718091709040608060c1e1201120c0506040e1f050109090f020c01090516082103151f0f0e060a0e03 65
    0x10810f649000c09544550703102540141c4455885414000f9505507500903001d15207818044000303080045048180d081101c00e14564a402d000d0075844c06210340c1440081c1c81c0205e100c04010090f0105503c01102c55000c08440c04807201c41140040b540c40a000401c00000c0302c500204000488001c1c0840ca13000420005200d42d4034a100b43c00c03d202160858025640026021098160746210246210910a10a0a003100c0319001d45242c00103001c1c20408580c1c00d1004c00800040406e0807010b400050602c0762101d58814400f4020344007540c21401071205803400316044144c00c8952011900141e407076000c624070704105c601c01007915420207002c0940030441200f951009003e003840451195008002d01c0a00055030100e2020076004010140c01107500306464418141508000b000301d810303003e80da03446132204c100b030304141c500c00301da0030078101c422056100c0e003c01d60300340342854aa11811201800720004031400e6003a50009588904140550320f840380c030809030034046607806421 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 795582347 1250 795581097 795581161
    0xa0e1614090901031415090304140a0b0a0518031f0216140d180b0901120b0d0309080705010e1c03200616050703051603090902180306070f08 62
    0x4210b092100341c00503a0700805a80c05050300c810304110b015001e01045031200d0325030508020740d94403480fa9101d46410740c0c91090045400c0e90322801b40600510300004034641d1100f4450020f0001e07040b071100a400042d00002c2d65410741404641e003441c154188503002007601060f14050000d41118489072070100c150281c1e40009443ea034040a40048280002c1010055145004000010251a08581e50b14126081106d02500804e03907101c040f0900381404101c0c4400c242c3c0000f0b190314131040b40e0150440005006241c0c0084980e002c0c0e0321508142c030a80f40e00d034001515244400001daa0700702c51612016141e01036000e1101f00158424038210b00ae548601e801c00a0030300d10034490240a4015006202c00c80e0031b8801c80c6c40071504c40c3d08001e41080800d4134054694040d029400c850300b40710001c1102014456182503010f0985404210344032030302c0c0380e448000443d0b4005858024410040032502c032a010355025011200c0c135642d034005c2030fa140c500d00200a90a541c68821804042d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 795583597 1250 795582347 795582349
    0x7020121060906180b180c070b0f06130b060715020f03010e0f090106030c06030e07051504080f060615070503120406050402031903051909080109110a0e161409 70
    0x9403500030030400d030010910b507060610030810002c0144003c264a481c140080c03541c2c0d286c50445500002910120750426911000f40302c14134441c0c04801003500d54600c080100c51102c02403194003c41e001d984495941101e840306208a41482042d264080303018403402c40010242c4003a82c5040724420009420b01500702c0e4940031681003a00604200c01c00d200c100301c005112400c4030340e07102d00050001c1c00598510744603400c07418800d004130010580c984004955200301084044001c0101901c0b9140302e89542d002150b1580090044000a0207a0f07810101200b00010380240101d0b4020030031981c0307428030307000c1590703503413003003504503454081806080e0003441c0d00c21103944034900030302000c6094130f0039104260400c0f022003580d091583e030722007031701c00800d0740401680d150742c24081814001120791174041d10891802e5100c10f0440d030034403890504000b045c11080c002e5240c1542e0806050303031248a02030041c40100c950f80400da4540342c843c00c1e03003807140007c030307250068030324a252402210704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 795584847 1250 795583597 795583601
    0x3010b1c020706050414070f0b0d02130e180f0706030c1803030c0605072136030f090303050d0209180a0e0730030509030d090e011202030307020121 65
    0x40b040e59025914400c00051140810680c00340d1881d0201420210b401d001c64501c01082078040d09680300004500345001941e43d50441f90034549511a0000a0ba83c40f044030003810811105400188038500e0f60720300001000030f2807400a00071034003801145041140440c01407030059620804c0003041400e0720158048103580001560003a6a482c120001500b0048240c2d140580798004024007041d00008140340340351041c01c01e0300700403000704a103015000f1000100003c030001d200454034550046c801d640c0318145040c01035119403618503125490b582c003a0340711a50313840081c0214400700302c403181d241400d9000b400e45080040c0b48076a0f125120801c1d121940086512b44207665030383c550b603585440d041080724020001102041c545c070700074888001d10ba6249000c5840564400d00c0144109800390060380d50385403002e011640101640c02c4c0003044140544036241c0e02664200021840025655898108a402900035807504006078011103500d0050584590b90b40981c961700c1c12a20443c2c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 795586097 1250 795584847 795584857
    0xf0b0309030708120907060906080403080907050406081e0c1305100b0309030a0305060f01091404060e0f0708010609060c080309070305100618271103011b1101050c03010b1c02 77
    0x820f0700145c43c241c180a0701d01314040e00300d2030a10640c40300800949500010603603109a01d403510007070365101e0745100f61401c81d49410856001d404d02c00c011808800c0060110184d1003c0c000b0613082c01484e0002c00c2c0c03548141e00804d034101d09503081145007039079183c02050b000a00102c062a00c9a60703041da102058205a800c040c040e00300003250b00c0000d504d03010720f6030003020498291320441c07546000a400160288a0320075410010050340515960396403040008001004a05081d407411114000101d003044a0a00108000070004120701d0312032200341c01911043d40700c01c4440070984c0c0381d5041d29000203200f903c0500c1140000f00004800340314a040401c06c00c103001c50b182c1e040c5000b40c912042d000b442c9800252410000b6404600c601d0324003142d8800d44400e209085040303090008001c0100c0d115981c0540c01c0c02c0100c4d0103120b941106204d0100182d880105100e006106c460903650161070105100c9001e100510400d10300300000d00d21500c8a078541190003101d000c1107404d83c6c101d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 795587347 1250 795586097 795586117
    0x160305071a011d0f0106140903030a1701060e0603070c140d08100806060f0d031403040f11400e030405030105060604032004240317040f0b0309030708 66
    0x40700042103c103282865070006071200031210505071a11503400c000b07045051003598104506c408070a00b00c0c001c084101c4010146c003400b92682d41c05034a1000d04400a8000080301680c06180005985442110b0400940d04010006440d548520301d0803135006c900c0c0e41040e5242c072003d4050010014003003245055034809a203481c0d0561400381119408a54680d2040c00241c114004022165403035604d21400100c0848a04010241c030341003c0312560b1303e0100310101d0903400400e000610010b0104003503110300c0b510f510001c01c00300109100c0c0f42c10340c0c0400c000b80308101040e02c03220342c0d8030980340748030f85030025601190210421856205456038645403005c9a0400035040c07095040a010f035545c004410340e846481d1900d0760307540f2000f2002466500440900114003082607941d00e4004404d803501c83c0c00c0d1586001d108001079041c80700c191100304d0b4051005030104030040300c03560548045501d4220038001c024a0710154210aa0004015050901080203945d002a1107078005e0703c00c1d19a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 795588597 1250 795587347 795587393
    0x60309020a080d0f1e0503240a1403070b040b0306040504060b04090f120504050325120302031903051603050406110304120e06040e01090b1813060612030516030507 72
    0x108440000d04200e03ca90f80c0700c12000445c03141440c155400104480e0007901d081e80c005c0d6030041403400c52440750350a40c101c540c8082c8611001602198203c0c0300101200201c0642d541140e540e40c1c18001c3d4030951040c2d40e1188800c1c40002d07000d1406030b00c244d901500a40c030110311b10095a00040848072894811030385111802c00020074044c840601000000090070060301d01030920000035170b1a48070390410181a54980c0c101b20706c08480c10191801401440c0351804051200d28010303450b90440c0304004c2c4003800003003d0003441c904c24021240103c1403c0c00901d081c2040c800210040d20340144192000394550b0003ea0600c4202402548164059a50b000064644c0b0030300602c201d8039180030502c20300080c4400c1c42400c8100500504403400f03806c0000314940d5010115100c9242c108101048550a00c00c00c58a8120b0080154166119140401845454021540e0341c1e000f11400600050420300444584c00c103001045c000d03250007420000d0030403242e5a2030306102e034022001005900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 795589847 1250 795588597 795588617
    0x5120c0301060b07060e0d0804021e1003021206011806030e03040f0b04030312020906040e04051e010f060501170606031f0b0a1205090604080f0c03130311100207060309020a080d 78
    0x4846c1c41a18001d5030002e010b44000380c100980104804006003000e4400d04880130828034055105072100319080c0098251105107501d1800900207400140750401c06141e10000114158451240810085e03440b0740b4088020f030411034110010804280f2a1006100411020420b525107450060013800c503000b00030381c2c0781e0840c5030040030007031030a0030036200500600001d17815036100001d0300c0c103580c1ca540d041c860715503031070070f045107041031102d190001c81c1914501c4507507007401900f004141400c0200d00b842021b58450045030512102c1001c1e070010400000820850300d0100000c40d0010001201100b00200005090b10b01c050344d076119000c1d000d40040c00c1c1100903004000540002c3c0c20740810040c51910191550f22401c008100038080c0da00011514280c051460580c1d44482244040381d495218414043c0100d5455010544070011040c120001d140742580381e0111065880d0302500c1403510300102503002d0801503c04a0380900e0170351020030803800802144504036881e13030705d00b0025 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 795591097 1250 795589847 795589853
    0x303032301151803330515091810150b040605040305010b0a08030a0e061603020a0c08060c12060d021c0b090c0d020d05100c0906020105010608070905120c0301060b07 73
    0x240f0322110007820490701c0c103042080840c030b083c1c0c944966001c8440c5035034000580c4a0350455040e20601e80801301300d1400c418030000d2840ca01c0003100f4100140c8d031f0101903860301c0100d000803074020000c2180c25403081d4050105012a60407040c00c4c00c045d1105950416100d10380e00c1076a40080d00a040045e02c041010014480e090041d404181d0701512900751250078001e190f5242e20523800418140003900c81486016100c1400312100010b90401a501050703042c83c0c000d440f5005c994098030702024403003000c02d82c0400403a07814007030b600e00a5401c0c0781c9541c140440350b901600400d80c3e40c3c03007540780590001507210001c21002c41c10740200081e840d0546c1e40b4202c1501800031300f0a4000d40d0113400030800c0e40d00c8181d8960f4840f50100e82c03455005003d440c183c0d1030070601d180c030440c849041004004001350031032000416600c0e1500240500d03a00c800c0100c2703400c48201d81d40000642450020881e0f400d010440c111240c07103001c02d0350746514622020a0a60305284d000d40642c450010b602424 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 795592347 1250 795591097 795591107
    0x7050106120c0509090c281a03070813230f070b041a04050406090501051f141b1c020f1209041e05090d08090a0c030303230115 56
    0xa41404101c01c00075440d9600c2e80301c1a220240102405001400081018100700b08685004110001c01d0040095000e07031311203000328245003c401042c0d00d05900030544d0b80d541c1c0e03480c0755a030782403c0031541150b40305d035000c58000354090045c018844c401000040840c8805030780d61008110001c8503010b000d91308190620b4021041e522a032a60800541840b681256900720340072240c40c8840034041c1544152081010322450b403001d9070103498030100140544294000504a541c129404d902085160070786501c00101d0f07640d440c001581e40264800c4149490300034003600c0050320135044142d407007800c1440c03901108291269500050101031484260f0402c8030440c1e46d600c407400341150b0100d820742d080342800b80c024550300ca2912014200c1031070803e9400d540e420b04840710300744035a080c2114400c1c2c03503075890b0030102d000480304000260740324030000b800c800c940e900c402108811481d58508400600e140050201090f441c1c8460300ca041000b5070481d8081c25800d8a0815071681045003e41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 795593597 1250 795592347 795592349
    0x110109030c11191703210405060f01030b0606030c19030b0901080703170708070f15110a17060a1a0d0615050a0302090118060302180906063c07050106 66
    0x2204040fa1031002283c210802c010208844c103400c200c08155040b030b6142c0c0c0c1540604071240039004c40340541c40940c46400648540210300542c1500c0742030b2610a40c0180500017400050f0449590302e0110380142402c02c002e5620050b03818610382882200404140010000a01c1e400002c0c3ca892011a05151155016004022500082207180c1c5590b4440044054807035110240031001308284d0203000059003164000359204900303002d0070f0861701e00242024001041c04046030f18001540042d5148a001c40c0d259507003980b20014160406811040c251000404440d001140140006850b21005403c2081102041d0300d01d502e03170780c20101030400c41d05994015580341040c4510841041e8000342151604510742c5400b683c3c58041702d00580e0084500003000e072503641c6a810002d4955451342c003401700c8290142c10252080300c1c20003002a000d00a43d1250f0f40804d04002800712441d444c4424513100340001c10940c0c1442040340c0012810211500141c1452000102d040400c0001e01c5154 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 795594847 1250 795593597 795593599
    0x4050622080615010c020f090903130906030308040f0606030203060c12130c03030f030204180c021c020303180c03071d0f07020705370503121809040201110109030c11 73
    0x204180c5071407802d0b003082c0b103002c0303c150b8144800302c130070032055440d40d00401c1c018400c090704010040c10b201d65800d03071302d03480700708054807503040840701246d192402d021f800122601699004141c0d00d5580310b155a085440100300c4415a403010000700584003800f00314400d4404400e0141c0318985808103844054008140d502c21000c1313511807500084191285034162600351800191119000c01d00b40c009125a0304135407035148070981e202e0f00c4800c072500407072030b160560307402e036124080f5240762502c4c400d500c00340e0340f409600148005000d071484082c145030364510703400444001f80e818002081c1003044c2500b00b1f481c03043c049a050f01c02c00404030b00054119000012000c541e14010900035140d1190f801003a115181e2040300c2038407070100303820398445644400c1103003620346a0740c0000304583d00ca80c80380302d02030b01a0a4501d65204000001d99003005440a540c03801c3c00d5499041011181d0014402c0b0305201508107951484038091164402851113a00c802c0310121a604100d610b55100080701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 795596097 1250 795594847 795594853
    0x1107050a1427013605091504061a04050403080114031603080a080f0f040206030402120d120c050a0e1507051203040606090c0e040c090b1303060509070506160303020405062208 77
    0x1504a44800d41110070f11102c613040010f22a16440740303c1e82441c180300380030016014141c0c188070500c00d55a00010940c0f261242c1d0184c1410808184425542d00310303005008a80a14010050450441c0d4540f070401c100805407040c2c55102074910603442c0f41c0c4d4000f61612030340410341c108200d4000c01c000750460450701490243d03140031226031200b041d000300001c0c003888010010404544480c1d040c903071662804002c0e640404030343c030001003042140045819070242003943e49210725004504591071100242e50305c059580d09030301800440480b40b24a5410300303408119010124400f440a0984501e01710507040d964101804c161054400c6900980100b40c90f04006103043c9411010414903200b054501248038108001d003560207444031382c0103a00b400000100000c03484082c41d007580541c0e2068104009607111180d040b0340d00c4030b66004460308554204203d0b500c0c2c98100d911580d210b8800c2c54003500c2c15890300c002c00c0e032907000724800a5410050b10a6a43c1c3d02010b110214090300d440001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 795597347 1250 795596097 795596159
    0x5010309081603182409081e0f1501060221040905040f02060f070605090a030c0212030c0a06060602010c080606040504110702060a020d1107050a142701 67
    0x222080e901c40c0728061103451045a002000709406031000d1100c40001340c1d41c0c90b0340583d03245a004280d503585141c0b0815052058000e07107030305004840c100c0a45607202c00070601070441204006150403010205481441004030b0032480d500c3c2040f2400d4860039400c031340802945010030103441c040005441e586042c41d2040b010403040da201c01030360101d40921101140513280c0c1c0c28100303010f98081801075000b840000700b090000d8501c000401803141b05150070005c0343c0d0b40a8031180c0300d8003103101c000c000070500310b0a036000d49402440400c1c03292070407094070b140501940c1c50600d001440c5a040b00d0a0f07880b458204820383e0284140b541500d07041c00c1000d1a407030700c40e00185c900d106601559219a03598060b000c100c0140c5070946041c03581c090540381d0313601038160020750303202000500c003000034088244041c011080070806608940029100d42c80d40da007000c584003585000c1121198009412519030082c03000341065071262054801d0000c05517504045004680c1248050005800d440c00d902c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 795598597 1250 795597347 795597353
    0x8010908030606030402010509041a2803020f0102030d1404030f050316210906020c010506030f061314060a0c020705010f05040e07090302060d0e06070e01020d030b060f04030c05090105010309 84
    0x401c40b80e1101c8200c400303503501d640b24401618036001d00c2d10129000382c90000900c0b0000c1c0c8820aa4151360000ca03041151084050720041102a6800c0065502038100e0410001400c0404a0849400e014015681080c0c0c5d0b40019600302c417501040340c942401c100040c80700740364020396188040c1c4603600d886465443c18105650000700c824410381d0400840f8100702d01040307080b4100500303d8020413018040b00c0b0850030700c00043d40048056420740d51030f1a0100c2c100f4a4001081d10f40d404240c009016656540e049104004410880c20b54002c80a001401203028003801100d119460041d400104080c6071031000385800703020307000581071001e4484088000c035080415981150010ba2640c5142c1e515040219a000d52541c00250000301c081180703102408141c024a0810003000200d070700d542d41d40c50089600c04c108141d40c50140e00030005d40050700d072181e003140c649014042c4c40c05150080d5150a5806984594800c3d07030704840391501400185441a070f95401480241703028041c08016407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 795599847 1250 795598597 795598613
    0x3040209060d0b0411120f061006020a03021216060203070216061b060f0e01020a200a110d030c050d030914030c150a0f15081504210c020402071209080109 68
    0x140c0090804032800c255500c070f41c1d4844681d0202c4001d079005031200300400d4403100d030fa240d034127960000240e40d811102041071480010340102013505507005044070170300c3c001031055a0b4469100691010b0450b4584070109001d4001036000700c3c031680c01007860140907003d80b20001040c0e0401d004002e844580d2044421100071044045174111b200002c04016650f0700b10020603025070340502650002c10107010741030f0803802d06035082003017030406603288258000c020340f02e2661000c014640f46036032489034024200301c080714520612904201c810f082c0c05446aa1800001020910000b529010303810100904680f83d421080c451400542c28110700382149500c58200c080c40f540d072885030500003501034210750807101d20154200810408006108800207113480300b800fa40c012442001000c09040440100d00c1d441181c001814181d004095075911000d440e02a062504101e040700c1e103440507983c2d0788001c040c410300c01c2400c1d40c841c495480c00030f480d00800d6400710400d079241400c4038000c03540d15 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 795601097 1250 795599847 795599851
    0x10c0f03020a02010e12071b060c140c03011104051c0b04290103060c0813030e0112110c100c020d0206310507060318152d0203040209060d0b 62
    0x90309000da01c40c90803010480c010407010100e0501c600c241c4003074864111158000301992401600101540c08000296484031a010b01c55400059005040040441d04d506058081030115a054600807080c00300068292108401d03180441100014200a1494115941c414a03055160fa10034118619101c100900a000f040903101c0051000198203128003403a41aa0001884040560950712402c00600403c0c1c1903414401007041c410104001c5007401d81b02c180b266915580e01048508460300440e80d007100703030724103c6480c2d455800d02c08509400d840a043c03c940401c00070900d810151b068002526100e08000080d50000c079082c0341c40341d1740031445950044c440d13480e01504100119030700d109007180c140710103242116486000100100403680804481c40742d907050202d440d80d802c105130b45904034940100200d43c40d404c11503850320303e50050018005681442c0044444a0040d507030750480e05441c0d14143c0d43d00004003c2140741040e03040740c00c8141500c0c0200c40740380c990b40300300081b000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 795602347 1250 795601097 795601127
    0x305240f1507020306040302060403020d090305030a030906201e03070507080c03040510111612150f020f04030605100e060103051306021308060109020f030c0c070f06120b03010c 78
    0x10194140c1401d080303020880e01d0203a4081c00300d0381c903440c0c2410020340307444085d03078100c0c0140515004030004511400c080d0007603030f41142c040d40c0b4096000c0030940017840d00c2d410481f54140c036040880c544800700090510002c51107441c080c0e9030310850b104100c9030300c0d40035841c1100420500038040c0195010094644856000c02e0540d6192480f900051647c00341d43d2080d60b000ba1300300c0070f503050b4030740c0061035082c5100118116a6a0000048400c41d4400d10b1700030b42c06941c001860000c04118100d40c000700039000c0ca40001458101400001e042ea03019500910150500090070010050716115aaa000014400906040341000c0540c07145480140c4010704141d2944041040b848280012444895001d40119035408142c000c8407402c1c9074a1180307003400e010700300001414006c0340c000c84180303062000345589140d59080382c0b00c003a41c1001403001103a20804401055081c81c0f20b0703a0700080c01c6251900040e0507203100c4448142c035030f000043c034042d034148100e0bd201c643e0407211601c7d641c50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 795603597 1250 795602347 795602359
    0x806061203090616110102010902060a20031207080702061b0706290a0e0c09011808010e0c1201231308031602010c08010807031209030b070305240f 65
    0x100d030051500e90b02454801a038000800201814040d41c20940440b10a205a4171542d860301448010380c00c03a030070401d0180d0441002c10500d8a0f003445400301c0140300ea0720140c0317445510094030059156412403540060160001c109001c1c0003500064890761152181c0f008244510700f6403e042e0145009807207420010300003240500401c11560844480000c00c682480e0161220300111a0400d40b030000310303402000c4181c0b02080d01c01c0003624061044483e400301620345884000110f809941c0c8001c10705040c1d444545c0441c15107001c1c022000c107009440002c0080303120500820110304045600039000344c5c540201a1195459860001c20b121104c1c0e141715400c1d692101060889a4901c5000301000400420820610660016442e9400c1194020028103510320001d0b41d80324028001d02141d6405210f0401c0060303140a410340040e220f92414a959541e250349005d617014096480700f010a131282c04004800382c400090900d800064070485040210700c0c1c0104503041c58aa82d01d0380506 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 795604847 1250 795603597 795603619
    0x1508060123030708210f370504260a08030106020c06030405150703180c092f0c1e0a03080c13051507050f0a060608010603031202070507081209090a06080606 69
    0x110340006d4505101098181e1995140c0c6a650f03080e1004911354183c1b1813110404d0310741140c803000c511200110105031109440d05003880f0195140d00c0e100203e481004c04880d14812803114180b1100032001e11981086880e54140080030b07003440c44e11700703a071400350f6802c1c810880454000290380c0030208040ca0501419152035000300e0160004182440c00c00d0000c00c0a2400c00000dc5112400c646204a00b00507500352454040c100c00302416956605004036000101c0002c071250041c80d000981c002210880507401040000718000321102d07045940040c0401d40a064003c54507680c05110b03802e2851601401c0c4040a0414185000d541d018080082680000000c2d01003242d80307081d0020b046540d02c01244c01003c0d036458110108130341503418640006801c4905007d0301042c7c0b80d064941a81040314030343c211000b508030100507906449040c2c0e00084c0e00c034040c46240100b940120a640c1c0d40d4081205000b0319074800b62580d20b80504d03080042088501c045685a0040400c4a21000349 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 795606097 1250 795604847 795604903
    0x10e131d0609030a02010e07030206040e1f1202031c1b0317100510050a0c02100c060510170a0c12030507051c12020c07091508060123030708 62
    0xc08010601541544680401d2000400b00000030701583e00e020b81c000c0c000960071025003525000d051000039000003043c0814002c4002e5141c009234008603a052040314054003020309058a40c01e64080d46032080c1caa182081503040c02d0100041c002c64001036044e414039000d20042844d5214001841c05401d5000c40744209481054080f0519501d20030403e03031410180301c2c4402c0c02c3c645100d8284a0040390105140e002d0082d400e581111815848121087c03001d17800384201102d40354200030408c1181c1c6c016000041081c0301c2d4900a55564808505544c20015050b1401d84031040300c4200358012000c28001548000c40d070010f850080c141024544894501500c0354019010002e1050151030108a0740d402541c105204c000c1c12170b990a101c200300300140c1c408170310400c0661082c032340005a0510000380d45820140c058180b480b2403e41c40c99403200c6950810400b030700311010000d0303a81c0041803030308004202c01011401c110090310245261004141e6a10083c40b055010010307003e09034940 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 795607347 1250 795606097 795606131
    0x60c0314370f021207020f1f090218040201180807031403131202030d09030b070c05120f07021302031006080411090f06040e0102181228050c010e13 65
    0x100881001803010750081c0c0c245030044e40220312264044c410f0340b0002014a440000c103d01c4508105001c0c4c000c88450f4140e102a51146842c03000489884048010042c0c42c1c1d410a581008201d20380c80c1d1032424140b00042141d0100c09000b0b080800e841014030502034003082c1c4001f141ea020340042c0f52602c070890341904500030089007030303405000c0403c0003d841203240c90980325648201e00343c0342d1410b248482035409420740c0c00040c02e555404000100d0036170051456140c003601600c116002403e034120349500c96403000c2c020a007003504c0840c0c010110300340b5111010008400c1c200950442c60301030050f01c8070030180c0c0308842c1008a56800300e0207001034060882014007020703040c1d000b60710304641c25528107442514407502803850009104688034040c030a50760032550300c00c840f5002003085400c0016041845000c920780703015070884800c0695a0082d1441034511741c51502c03011080d941002401c0500c071b000241c4c180f0007074083ca01248c1d516101014002c0343e600030300180d860a02c42007420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 795608597 1250 795607347 795607441
    0x21081023040b1504080d0905060f180f030d0f08010b09010203030f0406060801020310030b090a112e08090d050403020108040822030b06030c0a030c0303111207060c0314 74
    0x210703d04002030100380c3e03220208585246281c55114429490368030700c107010407845001c1c0d04031855401032042c91919941200f00c8003969800510802100c048400060300300840600c4410129031070b01120b00c0c045821013280ca00418480301018205000a4000703512440001d0103281e021030752100107801c10641c1d074844400f5185600c001c6460b0b117404c0e1801c01d0190b4443c08243d442c0c07070b21440000d0f28520001040750950f94003134101a40c00713400074280040b05120141c48040100c0e201d038000d41105003600d030031501d048580e0b511002030070520039030f0381401c4131500b141c41048000c01060000d43d812103c51504140d005020301c0e55001074011034204001800e1031003010f0340311008004144424041c40900802048064a503041c01c4001000f10f4080d041c070005040d4041d2200400100f40155002c00c0c078900342405440c0d950700144190085580aa00e040303c83c95a40ea00701600252b0501c149001049180c030000380707505168952461007900072410007420342d010704403400f0440941d81019 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 795609847 1250 795608597 795608629
    0x50913060320061305090601031d0d0e0901031109130807121404060c060b01091e060315060c0609030905180915071b21081023040b 58
    0x14540c40703141c019010600d070b1950030b402540086050415241078400c980c4c0350800d0940e0102d90b1454a0188020807100800b80d0341070607640e91651103540003815440d84131081c0d08005d0541070321100005400b0030001080140642c80110040c0f0005203511884960060100c80703c402581c0d520000c9a07003080044001025101c02140780010070040c060341145102d0281c4903014032700e100d04800b80d110b0103a44100c44c0000c40c40d1003c180400c0741a030002020010600d00840b81d1919840020600618540c4181500d4511901002659814070030314840b94a01c2c20007003562071a01d1001050b01130b0004018041c140d035100e40300209030040d0500c500a003405040f1414160716001c0c0310001100c101c5603401c503030094070640c4207640702d8010140d20031129611440e18400c2c4407020700b1803082c07802c9000c0ba0894140000030303030068020402d6103014100f5035500748180c540b094080c41d00c8070035640030f20080c83c04110781089424401a4032036140c5c005036000500030318564006600710521100507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 795611097 1250 795609847 795609851
    0x80f04030506090705120a031407060e1e07050939070c0801090b071b050102030f041101090b1b0c0603010321080f0a020a020a0b0906010f0807080706050913 69
    0x41000100c0d0b00e91042d03403420141c1c0c203020f5440c820300242522030000c180031500880c807030303400107802500c125010040440d05a8180b091715501c00301250349100101d01507911075001c44800002c0c0034241d148140000c009032202606e0103011401d22080548181c0103090403182d6850748049020900103c40850b2045060031840e052505220f42e0040200b61007225140a0103b001c3c4014080c2160742540140b402d80240c0c1e07056000c6035100c00c1180c0d24081d19081310300c2200415000d0002d07500518104140c040f00e03040516000751031042c560507a506204170707500e00300100384000065454580950402c00000e00c18103405608120203441590f510006c084004001e000449009241d400000448407001402c00350059400e08030444403901d0b01c00c1104001002e1441580150485c18024011155441542c3c0c1d035107807448004650390405a0300032801044800e4a00c1c0c400e10003050b00d04080c0c81d4007414019100e884520900944041c40000a0506180d440b00c0c00644810000c203941 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 795612347 1250 795611097 795611099
    0x40f050601021501030809100c0b0901141e0c0a0207030f142a060715020307031a01030c0e040902030c060703032301050f1315080303010504050a0c0912080f04 70
    0x100912054603100e0040c8504650501e02c5104140060b050b80c3c0c000140c81d09000300202040440c5460500c142c0800809240040009551111107030241628200102d00710302c80400d014180703400101a5070303840740354401d921460303860008496044110841c0b101e69901c80403205914000f2543c1c0300402c800b8500501005015010303a15a615480303000540c1c400c100c0300d00c0c2caa50001401c4c0080b464011280f0340c2d41382d003441c0000042c0140c5200f00ba01000c0711004c1c03c480c0742242c0003100ca107404a511120042403085030688584160942400c042007401020840188549100440b903030107242e603100010b095580c200b08649825000401066032000c541c80c0040141c2841030b614100c0041c010721510200c0140c003035083c160f80300504030920f11003501c020440c0b41044a025100459640c0200081c50308241c0240070203040514000c5649514200a010881d00c5c010282072140d071800c00301e20745072580050760f00e080300e9070f2288107030300a9014144080544110107039080c0200c00014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 795613597 1250 795612347 795612371
    0x101b021c08030a05070e1f090b03091b1e04020306300714090610090b0f0403020108010b030606070f030215131b0f06050f0c0f07081015060e010c0204 66
    0x25482008600c0040c062a2105170b0241c8032010307440c0361030b64031444481d20072075600300d0f010301a2000d0752540740940c84e16a03a00d810140035070041c0c50702d888070b801545c0002e101c2c1ca20340c0d1040341e005109490740a81c0c420301d0361503043c0000080041d580700741d80000c045503090307444800307240010420603483c5c6080204480303004559103a101e08001303103000b880c00000c1c40065060030411071540c0030b013510000e66030300710803c02c02c910303c2178281c014809030550114900c402800648042001d1700c50040e40c0b02d00310b0001416440050f40020003810f010400c01040d80c88140580d245158001620f65803200300b880c007070707041070040c07101d1708600f00945041042544440012400703003401540e00910107903a849040721807110038040e18100902c11101002914480c01c01000b0040407080480e080c00c00d1148410305040f500420400264040c54092181c807a06020a15401d034640008103c02c4440701d0528079413580034802c0b6014016110540c221690141c03503560345d000e40c010f00400417421000303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 795614847 1250 795613597 795613613
    0x20d0c090512060105010815062206180803041e150527030c092206141311100c08160b071b060c02031204080c0c101b021c 54
    0x121885110714951003040001140201d100f606071201a5119042a625410498100100d601d842c42d000001080740c40700720b20541804070342a500c41480c40000c01d01c1c0020041c50840e03141020300c080740303885408000805002007121700300c4510035030448a0705030369201602d05100030f6100e03002690041181587d060b40c042e00410f0662000090224001e0354000603c00c8294500c942d913170507911250490b10301d0f00c4d00320607941d40000424880302e0b541004d11980c02241304540021100e0b19241c41030b0710242644817020b564040c92040c00540d16504c20744880303094141c03450456014450903a01c08610310701c95000000542c1e00032107400d80d9013a99910203184001c410406407880c8000c0e00216441612542001440a8181c1c020000c400d04603200d00c0002d0004031503040952104101e01c580d007081c2c5c07200880c0b20301e0190b4101c584420030702e881c1c6406c0820b0201d505201c2d01340810030749980c5401079500156021040c0c4200720a4009102107410106850b03e401d203240d20410719101081404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 795616097 1250 795614847 795614849
    0x40522150f031209060f03270803041e080301060315050907051309020a09030b061216080105092b020a060f0c170606070201260a0e0c240d020d0c09 65
    0x1a43c10031000c0007003c801101c12407407902800300010134031004407140c603100303410180d100003465000008800c0001004110b03190f4002e02103807455004001c006c01e1004d81030701c1e03454680010700c1803468542d00e9920400c09110500a80c42403640e07800315601500d00c0d0000e00d402030311002d49980c0070b908141d14082c20b00d420100b039201d095003030110301040b8200c603070094422125403500c50818060843d900d070982e8a20080c80b403a0801400340352200c1c3d103041041020300c54035507c02c18203002404c02083e0350a50720020035001c942d80c40105a18151018101d00e01406611000e002c0d01043c0f80f6041203003080440c142c0603118509141d000da0500e00140d0080c011810961941d404069405810140c50003088038629803041c024000c160240d401035462a54160200a809030080081100310f001c2e0002907071101e48481d03817503902d60484074081001e0808a00101e0707011417141070359108994101e1001e681208000d4000c9034110790854035070162084540c4000d014404200340e0300c2c00906142079 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 795617347 1250 795616097 795616103
    0xf06070201122c1006060504120f0507091409010203160e03012c0c03160b0702061204050105010306140f01051005040b041e05062d0d0f0603020114040522150f03 71
    0x691034001395944000c1c0f190b542100d8283d140d103400c1a2038980c1d40040ea00701110309172112184400380c1000248140554800ba00542c18002613400b1006600340d04044000c0080a16178410001d100c181e13040095107805c0040c0c1c1d403610345054400c880120b40506085205500e4030702207141c260500306100121009020300320710032182c8105651007016641c003044441001e4a441a41043c80390071540401450360a00191000d0300d0309680320300504d02e88008642c00d031441d03551400144100022401307402950310004000442c03a0410b0082032503a21010700ca803501c0752204e44d4400591501071801d4a00504641c0f0340c49481c3c0780e58034402c2c1a0a916040c1e0055a055034003004196450100d007582d409082e004140c1035124055030900e5800c020380d84c18091105424003840901c4c1da060300900e500c08a07402804565140781d44005000410b242e04c5401c0d866805000500058032800810082d492888041c0220010120700450080c030110701d850144094007800498500d00d005140e5040301d01c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 795618597 1250 795617347 795617353
    0x21090f040f021908160c021005090a03050115141809010608010e101b12020c0a020a090e0d08010b0a05030a090c060c12030c050307120f0e1b0f06070201122c 69
    0x1440940406002480800420111b40700391808005400c0c4480400181c1c0005d060440c600111600081c202c0c0d84641d004454a0f915140d070303820213469090352200180f22028a40f40b41d902d104000450704240c0740130040303241d074120b0001002080b094102c1c0b001815004003c100ca001c03503a040507207030024074078502d04490800d0701064080c101c2018000c01c80070340e5620030070035803900440744020b58868500302040784a840094809a41c9041c242002000c1e803407000108024180c00d41418521f007120701605120909004001004541d0121455101149462a44caaa400080b00000c2101c00700140c4404c00c64080807079455081200301328618000c210114802011542c11019603900049040000c1c20520104803003500070102205542142940490001c1b0225061011200b00742c0c1c0410561b40100c900c2181c040088060154041b01500d8000381c40c03200401254442c45070321802810000741040c108048132480d4003ca100c00c201e20b41c4444405a1140003e25902050130400c071580 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 795619847 1250 795618597 795618601
    0x2a05090d061a0f0f1f090b1317010e070612023009010e0d03050612010e010b040b010302130e040314031515031501080a02070b0c0301030521090f040f021908 69
    0x803a1003401e408070700400905c10800300b52582071205600110409681c14000390180c00324601c05c50f900035040c03020321001c2101c0f01a2420b00d4200c105a801210f0400991512540120b00c44003c50042d06450050130500446101201c0800007032041c007480d1114440e40503507801b041c4441e8505000c11102c5001c003006d998440300401d608035411030b420341441f40d02a07184c1d00b140c9030007500110390040e0020b000810404980080e242950001c102c6880c43d659581016002403600d48503810072130f803082c40c0842c100303001d2a2903004050900e01503004000141c100040405204141600100200c0710407180c59041500e43e428140c05c0500b50548294881009a001c4220060580384564100103070b0094080e2041d005645400300039103c410420b800300605801304221301d41c1c55000301485165141e5961440c100700f070900d0800303120340f044000c040865801d400484003d5070b0f0701400407a040201c6041d80000a0001c00d8080d81100e0f4250020038840110004034503491980402c13525030003425 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 795621097 1250 795619847 795619849
    0x90109020a02100617062212030b0405070c0b1e0406020318100c030f05060d0f05010b060703081005010f080a0209040f0c02030d0f0c020709020d020c010504152a05090d061a0f 77
    0x10708000b8131076107183d4503412a100119207001c2c9520400403250400203070f014ac4a00100c0d096a20442c0d00b60042002c40d1031000030450304035001c0750301100c1d00860000c1c1c141810f29010b60080c0250010300111307000320203c0c521220340b103880d81a00801c08110740e0707c21500da007400044e00c0513644550209160024251120840e401814072400c401030a92010a40303079603540410690400e4240c134150340c1e8403240d0b402c60301c1e00c82c01400000e000b6204d040720380c9040b4032140250130f600d4002604010110502c1e4450036000f20f070f8150010841c0700c002da2180344901c0403e00400b0b40300c850b24401401c0403c000c4401d50040028100080018003d014024500c000d24040e584034090502c0141d1010004100400310359003d00f120092100700076140c689480e80d82070a651090f64283c480340c0300d0000341d00701384405101e403a201d5a04030411640405107208550346410001110710180100003e90b101ca50340c8e200c2e61031802c0c1d40d12030300401600319100180c48002441510182c0100d8000f60311242c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 795622347 1250 795621097 795621121
    0x110f060a110f030913020307031401080708010e0f210706060303030c0e03070b0a0c02010c050f01020c0d030e07060c050a05060a0506030c060f070f15050c27090109020a0210061706 79
    0x20640280a017441060302d0783c0f9902c002d60004240d2010150f40e40180213a403403002c03440314000c000d40002081d03480c2c101440c940c00c4074901c0442030010340c081417010f59085404900c15515801c00652501c90401d088005030151042c1030006142c030345820004420542c00d540402c40d004c0e81981e0745601c1540d0801070645d0364086024071560244d081c880403400d503220380a046001481031505c5003203206542e48051601c5040700d042da0540e500401d51342d0400908202080300018946010300091444080107600c0da5001c0c00740c041001106043d5070700703100040000301d4000d82d0000850f5098034202c19030200620041d2603051090180c03900c25281c3c2d01d018410f036800308281c0030105181500035581c103101000c2418007181c40f1840c003018458000000e101d000d2086c9801c001c0c2e240d9960802c28a0f0859804400039000000300e420050a00ba44881d14401e0542e900b4842c01a686d56022105a04d00002a42e1016034a8140300c0c1c00304540800040d554000740c0340b130b412660503498003811410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 795623597 1250 795622347 795622357
    0x11062226130e1b0c010608010f020901030c05040e041e12030617152d0a02040f0905041a150301150302030d0f0c1509020907030b130e0a110f060a110f03 67
    0x94200b4440c3c64403080104000038810129100d00008465540d80c001d5800e44e16492807a8403001e5000c18542d1465815000700c00c040249031508a10f40360410400d0780c201040600040d1040603403510f180e8055803600e0180589503040707400b05000c80b91403c0c0040c09403d030341c000c42410354840c001302d0481c1d480004920f42080c040c43d0303021600d80d59103541c5450f100c02d101404540b8400040701d48420304640d45045000d1804514050b0b0f03103034107100b12103403490300325807210300e145150108000106200404044140e41c0e405806c3c2d00c00e407a0501c55440c1d00303840c2c0c10701c5c5601d1751900c200c19038003074019901042180d10030380590392487c0d070301c2c441501c1071021400d14001248040c80c084001940800c3c0c02030010413403600014040340c3c107130045004184101c0b00c00010039540d0014100c546802210800341c40c1f501e4200740304403114168030585030702c00711000403d2070703580e50b0400d02c056031103d25101d4091400781c030540d01c50981620080c98400b2030104040f80c0e00801e01d030080098404003c80e2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 795624847 1250 795623597 795623611
    0x210020906070641010f0f090f1b02010e120a081303090803040b09120a080a0c02041404051e01060e01150e0306150111062226130e 58
    0x82d003406482d0329940b024002d0018100a29500e80e071031480501c102e8060300700000c013101c42101104501d618805008081030308058076001c44000300704144c59602c0c0494003651a84900401c6400102a10754064800b811404011800c1140302010080c0d0550100d000c1d49004030840c1c01805074072001031f003180f040702140c030009044500018000c150b90b81c0e940a0443c400e2811920055450111320308640058200c1a080071000030340360841d20700140d6030b1555910320809411002582d9031945054854044a9414002003060303070801c0d55030356840003d070f051124031b02e070346a46024902152034a22141001c15164910811041d9948051241c10b0a884c4101122403007a400c01965604c14040c241080301085800f00032903802c5e131020300c02240203440b448000040c5061840003d803c4c80c2803411110075a602140400500306842401d408400b802000801d000c0f441908080d01104d140c01c50122000c4603124101e204016204002c060050120030b09040302038130b4812001901c02c040e1110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 795626097 1250 795624847 795624859
    0x608271614030c0d050a0602070503250c05100207140103060801020d06090608030307211b0f091a030a0c05070f0f02101b200d05030309060a0917030903070c0e0702100209 75
    0x1b10300080d0075940100300580c0105d00301ea05142d000004072030321800e10101d61442d0060750201c98108851140500041d0800300c1e41c061990030030000007551480386208808000c00100800c4030300d40d000b940b044000d1328a4030020f5640341c2c640e008040c013415180c492402c00e00d240c070380005420f0f40048290b0b40180406e603528030000008410400341d940100e0000c1c810301d0b030b44000c001080585001003c0100700583c85024842107401d50260607c4c01b00d51020209a208403040a2801e01034011244e001146900c0010400371703a910448450040660081c41c00d500200c10b81d0a0000d100c11107440544200d40c00902c011a482040342c607c1c00201c141c4209041065480b80041c01c0c2104581c46091601c907105030400581c0000750342c6184842090b20305800000503c21070b51014000720350300440b01b813818885d080d001d03075807003504020740b1004403246140400440c0e0307082e9080c81110021904080780c000303280d49426160f030280c1001e450820145c4162a4032000781603890003a42c01150b001005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 795627347 1250 795626097 795626113
    0x3030a031e140601030b030106081e030708031003110d0b0a0207112214040302030714120d0c020c0103050c1e190215010608271614030c0d05 62
    0x580107092980c19440401060820303a1610280038402c01e52280718a002c107032a5801c0c050300160866000154143c003a905005040c01100400030307020142540e0b00800c01c400462501420b429030048500c01420940700109000c2c07500780f80582e240c20390780070700060207013081d00c0350401c8500310741c1c039030001d00740038400000604803255680609010b0740101b01140008403458006552400703213800108041c84a5500b8142081341407081040f03441c801960414241010745001c3d66070300421134010141e01c4c03041000064030800b0710030714030191001e40b04181c8035224001c55601902e81d004000005101d25001010198440d0003858042c44400ba101c80c5821044101c801d042010081880b030190001c200118200c54008039182e0b40c0113035079001d48005201400411824017060340f105007000311880501c20820b100d081c82c1c55001400d0800c0500c0401103a00c4035003009801b2404034901600514002880d030140f9040c1d02607000200c052705c034151610000c1050080310444081c20903400995 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 795628597 1250 795627347 795627367
    0xf091416180f060303050d0f020711191706180d090612020708030a050a11040303080f1e090d081012020f2b02090105041107111c0602130902090303 65
    0x2a0744108050301000402c0c52050b0681d160156042c590040340000c000281701e1002421510132010065110642586041c200d03803140c021902645a0517440750140d0154210b0300e42c8814182d400410b0414508400d0182440107591103050403260443d03c031000710030f182103410020810b11034550098581c081c1403401e0081c100c4100007403440700a880303035081010401044014011350301c02c2141c241c020442c1d20300120140182c4440c0105008000d500340400d100098014207001c2e4080c0840024140e542c3e00e0180d44403100c03410001c030f5242d403130904060000508000c200c01d00500d4013512103141503140d00c1101861200e49101d81040d01c00c0762140e840c01481c000401e14041180284046111312890328841c003d803141d1406520101c4d2061400380443c10720261702401084200e400300650f80d02d48280300058031442400403c60814001c02c505c00750760352115170011078104900310f410807000d45000002940000e00070100010100e10010b01140c0718006c942688001801950410145038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 795629847 1250 795628597 795628619
    0x909030d1b0f0e040213140a06030b0306010b1c050a0f060608130206030c040b0412060e032b1d010f0b0604120b0703060302030a030e0f01080405030f07050307060f091416 75
    0x3034069900603001c01c00c888048006d02c0c60340d00030b04030300045c2d085810784a80810072940722a9201d80f060500b84a0140e416660106546045859806555070754035000d10140c508000400403171801d252406050207540c255a0340290112500340c14100282500daa01c2502c0c1180101d4220301da6181140280005091100156401c58a200319035802c2540760000800b281d00260400c0c0201c000180e0000c00b44045402104130305401440030350700d050140403511000440d00301e02502e100e0b40032020081c804210303610031a1542440701294008419044240340a000b23000f5141c2a01c50030078500b1069464600304490407039001c015901c03444115541e0b107540c00400109401c05265407070030000050388040c070015035200d22983c0c6210107890008100071144905960340b504002d42d80f02000005400001294103213261030300d11031348a400d1403070310900c1c42c0308260004140c2c0e070610021042404640e04000791032441088090042d01e000c0c490a903480800c0b01d030084540012680c00c00c4190011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 795631097 1250 795629847 795629867
    0xf020a170f0c270d05240613020a050d110903010c0809300409050106030c0c03140c07030212070806010b07030e09070905060a360e150909030d1b0f 65
    0x84140c0b6101400c0f40002442c0d1041c400000e4907990001a4100401d28401d6500c0120100c00c0034490410b00300100850b049071850043c0d0420a0313030000307580c14000c2c00703401600d0340c1c80c450000512515500950302002170304071009180c004e43c20551904126401408058422940030b0010000f81014034003200349003840c03400751340c61061840300ea08071219440e80204050138070580041003a500d050002011038060011407010010881a81c1c4002980302c01414450140b024035261520f800b221161b05082c01ca9100940c4188441c0300c1848072040814010201c0343e8090584140ea0fa8070402c1510510400c40001c000803141c9841420070314054070348030b400c03038690701d00000b003151a400030400ca07511104200f004543d44d120300c410752140c4441030100d4141c541180d05000300200c0d08030140c014071030288800003400340d400103190965074034590315504801010346880c3e0800030307152610b90344002e006c51855400e10b150360142460032140360420040f16500d0f0341c1229103004084921483c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 795632347 1250 795631097 795631147
    0x306090608120708091f0206091005011409040c05192115050a270c0f0f140f060406090f0f23040b1f020f2409010f020a170f0c 56
    0x101b045c154064007400c181c0480c007810340041550b03003040750707a240c0381282020200d82107506041c011301015181e810003003134840040d989040c2d1910b0b20319140c2100f0f038860304040e8100e840d050a0200002207810303000d0846030040071049109030400086e0140000c2c01c0c0c070142040e42d00252440c9000c2990b4032582e4400d028200c0010201c3d0360b00c10f0012600694803600b210110600290014802c003201d4800c01400c0707942000c51454500385100003100018403420305075a078808c5407000c258850040c860690000145007907600c64540c40081c001801900030036910a641d100702180c0010709079100401d48180c035120905810250025502e040d11015500713801035121844040981c4400c1c038600d40c00801a420300c0110507103070200034a032101100d0691210f60105610440507107100d12000f070050300aa04c40d04141c0d45003210503025102c2c1c00703001c00e1910300c0021080300c425841003c40c0044d0000005070040c0382c6481b071414224807002e0f10b4140049804000c0300305117000318140c070300301840c0e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 795633597 1250 795632347 795632359
    0x21170c16030c05010c05040504051503121e0304211404030609110a030c15030b0d0209040c080307030e0f060a0f200f030901020c03150105061b030a030609060812070809 74
    0x4043d0784080c29100490091000b28038080b8080c00b00c4c0ca040d00462b075020323610f034031200304103c2c031000020741d10802200d4207900050009080408a0040e27050030304d80c080045011036407800c0610703140413829400c0c0c0c848070940081c0c0141220f62407051082510801c40050703a80e050034110f4071820020260b548089480210002e413503031040d21825480d0008502901d507140c85645031800301188000400700030020507203084994100d69071440c00e07201a007601515070405940c0d80c0d2412200000f00c80c0c000310200d210100c1c2030340415901444401c982c450070345040700c0080611051014030301a241c484004140c69020003d101403058161140700800108074104201454a1250404500e28a21040c039040003031440c4e00c650301040700348400c240c04e80c0200000c03d03115482d5407011606018980c4034a10000ba0a0b891500f055500c80403d00d81006032942c40c60b07200b00c058010002485004c01060411000041492020561203d00700c13031a0111894075046503030f0000164450360400d6030100d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 795634847 1250 795633597 795633617
    0xd12090608152e0c15180b0601090b0705010903020c090f2a040803040807050609060a030b01050904140601080a0c0f1103040317040e010e0103030504091821170c1603 73
    0x84500c49940503c01140c0c0c6484400b40c0280c14503481d07520f05000600600c609001290003034442002c4a844080d4001404441319100d82d001240c1400082e4040c05010034080b4040f401d05c0b10650100e501c0e01c0c8240c003207031000d01c548024401071003c120345190b000b1080c03600265628204101c132940c84a1050010a0b00c42806280f0600c150019000000c081c1e10201d010301c40d500d4100500009454100c0b113a81c2004023100028481e842501d0341102050340720410101982d020b042580ca0310ae00040050040d41c845e4070062402c00c00880c1c0d000d000508001c00314900603103611401034002c030b441d6980804030165079030584100001040d00d11052000b00000404161803000e420194007405180c50358139884c00c00302c51040141a009401140ea0752401000080e80040c1101e040b2248803002154a0309030b800740d0202c44040b000c020300302207840e041086052590f1808080e200351541c8035001d110403842252040708100321203000c10349c481040a08c42840341e103103004004510a103840c1d5110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 795636097 1250 795634847 795634909
    0x6040816050c13141b0405281d1303050d15050d0803010e0115020d12021204060e1501080a140a05250611150c090d1209060815 56
    0x100398404807070a03107a940c402042c0c4110600150007034022100c00322180c8a444170829a442034400e62086500c10000c102001003007148201507420740080b032041200002c0d6550310f510300c1015200c2c85100202c030a590000341100e0003442504445034055444d24140012118070a008007142140c10880d9007070804000385560b01e5908801d515407003501d1460b1203514101010350340c0001a0084030f06c21031810144c0c03001e107600041da10f004c81040e02d019110800001c6549000303205000c0c0801c0001410001c00080c4101d0f604217641d064000c4c0203e44900301d42c0600c041b61000c0070301485019810400314078012072f26464031406003d0300d140a481130202c0c00d5035228a0310882c200200095440c0d04150b00460440000100081446081002d000012291581d44448a9101e4015100402008a02e03140c0940301560080030300034020728003049242c00c101c4004000220020300041b214040030070550310404066006403030032180301c00b902220608212140d8001c920010703400b02024000141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 795637347 1250 795636097 795636109
    0x30e0402120a0b0d051603141f110c16060801090213031211071710050403080f0705190315050307030203070b1c05010b0d060819080d020c06101706040816050c 70
    0x45050a1900d801342e0038a14030b04034000d8011400c20081d1a00100c2c4140a580c4251a645910402e402000540070581c3d0ac0034554034000c980b80786441e0302c45c0e1945030014011000c1080c0a031200b544500c1d184d80e80e50301d1464140e12951040c8982d03c850038004100040b072889600521031140c0c181000301c00f603502092890000c16500150000c003a10148a0000c4002d01c00e0b0810b182e441c039020b00c41c80c034258030050510240902101c1c103003007105001404c424800c41c140c2d0705070380b0188192564000a650010007070309820241031841542c81c0000034151600143c540300b02d07503000e00504925031404c8002800707030708100c0c50324034944086141c03104102154440d440c0030f041d019602580750415546083c044514036005540a5445041e281380d14070101a01290b2141d8010302295407070a801603590043c0c0640701c0c210b5414030510f020300c00c0d44114611a00180d40c8580c0040c2c0c42220482d030442d47d00e00081c6c0d000707407810341d007001006894400d203038800ea801400b0f00e0446200c42c1c00d44001c540c3c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 795638597 1250 795637347 795637363
    0x11150c0a080a0f05091f0c200f0303070e0406211205070204050f04050c09041113060905070f140702060304080d0b1807111203130309090c0309030e0402120a0b0d05 72
    0x940742c05c29102c00360503040f9401c42d40c0006c0b00b50707501000103c0d82100090007805112011000c0d1103415800402007413010002040c0d8101c0c8482503e4880c1880c900c00703824001d00b030000c02d00c140d00303052000c80c809840039998491000010541c80790303501a0b845030b6a04d21160000c803003c000d01000301c040035880b0750044c0d43c01100b200090007403030710b05401c08074180b058840c842c5220b000c9000c1440080b41513000c0079106144120303490700346041a40b100c070000b0403250b480010300504020400c125150010354440480e941601e036000850301c8029081014400c044000303500c1101400413401055900300648005050b500000803018480000a01c44c1e84c5044103102c1d50300da0000810402c5588580b81c056100711510003800c210040254012981c0001000282c104c1e02c00801c21090600c43d061046c02400d013041d0800070b10004100044c0039148556082e40800c05004c100da1560030184200e030300c507000d0210300000c140c40b4441960060401c0783d410a90148800c64441c000c81c9060017602 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 795639847 1250 795638597 795638611
    0x601020f120a0305060405240d140d020c18150a030f0f03031803020c0d061d070509071b0303111905030f0106140706051b040611150c0a080a0f05 64
    0x1900c42c511440010103444c0020a641c4c010703400c2c030303048c01090300c20380340040c0411903010459082c000084021851203880003001501c611241c20b60f45200c6500410019007d200e0b903429684a5540c2900340503c0034258110390f5406907482000640d0107209520068084000500503801c80355a5150a00b80f1068143d0658034000d184c8400703820160184a02c15591740c50100c0030034640c1864034003a403101300402101d4000d46143c1c10354400c000302e40d4003006c3d80e6451441e07805132080a00c2002c50b550280e6014280c020032820001c0f03580c0900441c550214640c40c1c24004d8100101960f00b100a00852086203808281c1401420349104c11645650b40a0415694281d10b9152044000701040d00c1a4813000901000c50340001040d00c207002280d02040d00082c0109207511103800f1080d08501d841c1024000032004039000c241e0580c0403040f00e2010344d21108a40303004000000d043c16229007600c0402c2c202500b009035141203401404c0c0941e006070980000200407040c41d20b00410794104032001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 795641097 1250 795639847 795639883
    0x311061c0c090501020d0c02040b0a0b03040b0a0e0705100f120608010b03011508060117160312020607080f2719030206150604180b0301110915210601020f 68
    0x4038010710351010500c0300a0200348020090624500e00c00317080071407001c5010b40580e8483c49004507a444882c2c1d000d00401051840c01d40c0e91515040034102200295403160a481c10086e0941920710001220400e071603004001d1540764050010a59020410314402814005c80c1e245566010600e0311400c0300800504001090784a00c2004250855100001c14181003005c80d00600509800113400342c1541d4414201e548400da5440b07015103045e0300f000d803504880088640c084200540b00d82c00d0745003851070b6000c96100d61540401560340c0e42c01151000c200c0e460307100000d40d6030a03c2e071150b10381024407100400482c81d142035945040810309940304030060700d030b072020908041d81008841e1340600d0702d80d0110180d03100c42001a00a105511801108103441c2003040780300b1007103a00c50b0b070400748001c0080240b56a10134940351290810802c0c54420411078050040321200b03030040764501046c483d11444410741112420201510103021707641184036201990161200400100129004006d68 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 795642347 1250 795641097 795641111
    0x609010314240a18020306120607020706140306090f06011224080d0206060409080405091003021905010203190309080a021006050d0f0b04020310060b0d0606180311061c 74
    0x12001e4504280c2071a03c0c001c02d81e9040c2044068464084400c820003803990160340c80d1111400206803041010441040d4046e41003800300d95a00000c03080300b100c3c09501c9030300c4100600d8000d00c0c2d40b03002c102d640b150000c10210019186140d42e58169038040300505220400d03146201c42d040440b03003c05c04860b2182c2000c8071150700c17105050310f802c0050506500030700c0403c0800d10b00a442d0030002d4811406592100b2140080207120810303a4040c01020303201d0242d51030b003484140d180a64921040e8010354041405003c044c640c12203c0007503a5060b0011441e09046a08031020401c0031450b00042503665081e602c000b40d00880141410409540105114000c8011120864000c0d40c81188070317540612030480011841d40603078a056402160810040d40d80b8000f0034101101440c90098891910740042507114094000c0e020307142208034204403681d2079410568a40066089100f8a200906000c100294100c0c9014001703200241107941440310309410313007500104003003840020a403101a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 795643597 1250 795642347 795642391
    0x60602010b2e120f0f0c12060501051b01020f1c061e0302040203070e0901150212090901180f0c0503040201020c0a15110a080403050303040b0f090601050609010314 72
    0x8141d40e803009010380107010408920b6280407050340303110303200e03002c0c00b6440030240300c1101e00f0b41c0400c64041c41c030b03002401001108800342c00100205032850011468243c90300840309940d11810040d00e4060b10b440385800d14035401c0c0b18400a0501d404a02503400704000300c41035104030041e104e600d141e540c1d034400561000c08800147c49481c1c000208080c1c80194245030b1201180c415800c5035010740d80142d803501c030850100d4400c0c00c60072030a0f4009644800018204072641e80c6070822801c164266460b40d0744c4c10500d4222481089901540708c455000107004298403042c0628503181119000a00000007210703540130f0306c10040040e00403c0c0044200700c20355030180000d9020300411569007400038100800c1c2c2c22240004655030082010304070003040555400c00600c01074680000d441e0303482d1941c0f4903119590364801c980c2281c0d101c020101080004104640480c0644420303000303410a0303800d150a1100507009045450b0401d615171105050b180c220701005801a00d5102c0f0b00542444081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 795644847 1250 795643597 795643609
    0x7020a0803070302070b07020102251d1303030b060c1203060a060507210e150403061b1209020a170a031116051c02211603110d060f060602010b 63
    0x584204919042002082c0c000781c1d01144e0700066410104806484110a00040740762a8927088200d0003030100101d150300c150034000403070084a400b42903105440c500311303e00d4940105c080d51903054401254080c180003034040d801900d10741001408071070a002d20892030a140c158009240341c2424000011302c402c070300300f091802e0b028181c0c50405030f14002013550744c02e07071103458409000f441d610040d00041d0700c0761051801d0008450010720040d40f2210390100031190798060310040750118030f8400e01007900000340105059030301c01c2c1d4552201c0e901a200f29100504107504d0104d80c80101c000e00030698040e40001c503904100310300c00408082c0b05519015001004902d440c540c05d80c022130300108680c006290103000d84205480c41d40390440a103290700850203640704001e51004820180e0142100348540311079a0f400c00c00120380b40099141e960107104142c07804040d20f40d000c00314202c680303400d00000018881c3e104003400221552004442130440d0500c1c1c101d900181d45070b10216400d45444 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 795646097 1250 795644847 795644849
    0x21060a1a010806100e03071d2202060304121404080d09060e060403020f030c04090302030a080f1306022d07051605030c2407030e1002070303080604090c080106030807020a 75
    0xe0800554909103800010395520703072030704128200900c4111640e1742d524280255001000d4417580c1d031086000c042d00651030814101c03442d05070140141502c00e10f0744035482c0ca0034500342d000342c91946541c95076100c1c0c0e901c0030000d40052040c0900a84c0b007403150b9241c1001130004200300c1c001340400c0c00f1601d0000b00009040d0784484100001045070501603a50b280480d421294110340504420030020003107800d12600307110b000d03480f07807400c6030380700c141741d00400200380d14411565800b140341d40d9650020030107801650080041503c5210070400142583d005100403007500070b404107268001c0840000000d5030340301e04640404003042440401c0020000101407884102c461407016040002107030751100903441032441503010342207510031810741d039850202c03108218858541d101c4440c100a041000d6000f03681d40603048a5101c2d0ba02c0610100d40d02d030035030364165140b03503494076000200400740c0044581510380f400600c03030000d03400c4000d01c46e02d0000c40c4a440303200c5d1603500718010001101b441d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 795647347 1250 795646097 795646099
    0xa03030f170601050d0e0c040f051f030308041415010303090602210f16080d05040b07110d141c060918030c03143a06060c0221060a1a 59
    0x301c0050104581c0c105003a41c02120058000003800c0b810790090710b20b0035100e122140d030058503044001e560910141c201e9485640480c541811000c511171900640e2203403440040c0004500b980480c00141414041064000c0721b40e04a900312064a05100071241003030b030044001c946103002c204031440c0c0502c19001100d2034846aa0b0f02c820000344500114400c9003800c1241c40c40015540c3d2294842000c003921568000f08101c0d100d921404100300180419201a00e040c0c103441c0019904500c14001e200820344d0490161800703400301c41e800c0da002d84688100c40c492940c2405134020810b55401d500051000280020400030302d44540b1904076007000d4001d0840ca68429608004290080c5042c142c5a5051414600d103d060007200d00c03403801100c42e101602c07034070100203508010703208a070544103040d1030a010b41c2c0c0303400034254a0300320b42142c82031401181c000c045c801c0c0985804554015854041c008000c40880e180001c14241141102d1003041903a17158951643d50204031f5a5644c0010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 795648597 1250 795647347 795647387
    0x90c0f030513031209060e0a054c060b0c01020316080618090c0d15050127020711040903020a14010c08010b0702012d12140c07060b0a03030f 62
    0x2041c0c4005000c1c90a01554906440d25400c1070420040564802454442c0340800d4509a07207081c5401ca883e2859002a0380d2540c2c070034042c5040840003903500e03084181031a04956001840c6001e0501c80124140b2809044bd644680000c0d140401200400f02c0d01940c200042c0e40707180042d08100003114542d1028200801d00c0304200c03403a100c00107423900c055100c5902e515959120b50102c2e260140f11007005402040700289c40080000503400c08415510020b41800281c4c1c95101801140d02c4204201c0d006048444025644030b03810b44c010418140180502554101c011012800b600c0050000300c005a00c04001d06050201072900c07901d6201c1100c0c001d000880307a400c4c0040a82c2c0f41801284541500050a581103a001d00c0007214603a80814002e0084003044950403044079881140700c01080300800501d11000145c440c6000384c0342018000801c0c2d03103e0900080c0903810201040301c059580300301c00080360343c0300d030340394001107110b41d50b0141c6200b0310000061504040200181c000e403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 795649847 1250 795648597 795648631
    0xf0f0e01080304060c030503090a0807080307020d0e010f0e030a0b100e0106050703230705011b031107020303121f180c0809060606030c040f090b210d08040c090c0f0305 74
    0x40d0380560051017158061400c2520b940ba81c01c8001d041107440d120081c2910000240d50042109001c044c42c0702d0143c503000d98604040b580010764444c14a141c446000800b0901d001d5410b500840d50003030001c00150880383c06a100307a485d4503600780217503501c007140e451300c01d4200008007000c3c0800e400742545261032400e14080da540a81000426000044007040b1820044c80b40320301c0d64107441100380c124000340a04a01042010400c001030281d220010341810440c1c21303440c082e401118001ca0340500154600515901802103841000d4405889101c003011900454648410300c02c018040182c6544405203070103581c0000c032440d0085c0001809000c00c10800313031880119440c2d2b40308000360782c0035940756a880002443c611990b0071004881032521400710720b02209a12011441030140c8081100045d07060010b01140f40e01c408a042c0380c1c2c01300104541051240e01301c20f401c01e10861200c1c0650382c40315020001d03180341516041c00100311003401d00b891030b0b0500909411480d02100340e9411 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 795651097 1250 795649847 795649859
    0x1406070804030206030a09020d03030606020111072a170105070f1106061e04020c010b18010e070c03050409060b070b2a2107020616030513060e070f0f0e01080304 71
    0x5402603200180c4201c04c0880021000e1030590008078640b1341c01068204800340518001d4001d180ca0300503c80198608800c2610004400b82100e00b40b9400131002c0c00403270000601d074031040344000c1181a8162803e840040c0d070010f8240c4400000c032000002044a14104500810301c00690b200401040300020702c035404a107000c6003aa401c242d0548940d80e002d442c1e031420069039800c0503c201e401610004045a84800661015081036802c5490b0260400c1100c0d403103041041c01c0c080c1c4a1a440224049100907010b103880500d054800d083c54ad08041d41c5428400440700a940284c0701e0740c0d80050340d4130800c0b03040065141e210321041e184019207030b17580102903c40c60703c40d50705c00076401000407900130580e408103000600200455407440c81d40707402c800081d21890295284d1401030b0b100c04020200342d01902030244550380c072481d00761244c0300c80d40ba880c024010500c2c0e000c88034010401c011484822000c1600c001c0c01030b06910300348446c9030000040c58981c050744500c034660800e000502603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 795652347 1250 795651097 795651113
    0x6041e0206090d0f0206031e090a0201020628150e0702120f0d020d060602240f13080c0f0d020c030601080304050d050f100b09091c20030d06140607 65
    0x4010800d40b4000c066403030354030303081301e4481c184c01c40a035100da004002c20251000041e848014400280c1c2041510703101c0881d626555005000024051317044100090b2514040d00381514842e00103603030480520301100c411504489410f100802c89100c4804280415005008480e4000c406480203040c2071242140303000e0070340030700510001c20110024032001880304d144c040d11100400b07800100311540c2e075402c02030350303c01340345103003003440e4400c60003100aa03900400348921601c42416078651950f161012880000308502e4110b80d010310a1106180c0c003401081030b48080100c40300100303075124171114003a141070425503482e8803941c0100c0043c801c0d12804001d0b0341c2220415900010741c40750300e1808600f444981c0407908081e02c100c40e091003a102e41a00b006561420a88000c0141d895420000780ca6500d19203100701d0711004200700e0700070a48504600722441d00004440814804000030490840e030000e1400c0d0004c1d52140342c00d00070304003204c04d240d568100454800e40307080361035a68024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 795653597 1250 795652347 795652357
    0x9010203012c0f090c04140121050718090614040507080708030904020d06081005100b0c0604240606050c10021608070507030c06050c01050c030c0715140906041e0206 73
    0xd0f1500c95107000c1035030f08508000c00a00060001c2c024040407201113850510b604091240700c03900d003221030804c240d806500800d0b2488036001006003084a041208000308001e807180303005000b5a07100d181c000818420f102e05034a8412000d8042201d080070705105152411507000501c00d600105030401c48541c0002c2161484081a030300561600c076149a400010842a070196102c2d001e01524104030000d282d100030b200321031310090490700d15181e041482d010700481c184440158018008580441c40e020300310b2034000081138800c1820052a4042c10a0350000e1340003001217400031500020810081c4401c085614090310210300b03182510b112009024450000038080480005000e001e208041c0612000f840d040303103034a848035a40d2000108a540f10444c800880d500e0700c0045862206180c0c00c03240240854241d160030b004141e19908189000314102a001070f0307032400301c105080d9968488920444a001c003512243c0381074204103082c290044290403640101300703190801a60359406032a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 795654847 1250 795653597 795653611
    0xc050c0a0b040f050706080a0614010c0b0a0603060c09032a0e07050d1a0f030a02010f030e0a0c12031206031e080c121305090f04080a051209010203012c 67
    0x25203503202c0e400e2003507081c0161140648540503000f030204405410004c100d00a41100c042080040d41d505608245681c02018403400a80d84611010204154140135070700700d000003000041d40d540c2e0f42e84180445148041000105400b0801003081c07052411f002014046001a041e010351143c40d22894041100d0003860100720000000c16001886503003640c014409210080010b050b0004020510049031070700c4a1180045a07041c031207a090104510304155410f859494040c90341c0c41d401d401070100d9031984130700c40c0b15044100300411841c140040c010b02c810604a81e40b0807031824001c00720300d40042091415803d00b2010000114182280c07003114013220200300c1441340e245442c401520070740c8513000c03c902c641022850a02e603514010b000c90448134008401c2582e542c1c0500c0b0124408680303030700003112080b00103008111201c008200e41081850038624107500c0b651900c040e06801e4030050542e031340c0130006000341c3c5801e510910341c81c6601e20042d0003400001c0300c2c0ea0b0120304001c0480c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 795656097 1250 795654847 795654863
    0x71e0b03040c1a0c0105010807030c060c1203020d0e0613061b080708041e0b0106080109060b0301140f0901180c09051e0420030411060301050a0e150a080a03030c050c0a 74
    0x50703003c882509040c4e5a4007001a0024001542d45014042c0d44100030b010032b07200c4034844900050001c3c0903803400e601c69507000b08071007000d0301c000c94190700a400c04280024242c0c3c48000d1482d654a003445260b00c83d0305215603003c205092401d0220840c2d00c12010741c00600460700e00109030030703080668103a000d003240c40c1c842c10340d54451901906800603501582051409111303428100184402c0d1541601c010b40d440700c00d26031342c5098800c03d5403494490310b5203540040006120001440c01c0b9030304105006800c440c1c02010041c0070401c80032003644045100d0481c015505400c040c0f6009074165400c1d14600f04403c0c0b0f0510002a044100a581d00f482e0309003a0300703550901c1c1c1c4854000e1510001d201c441441c902d12207014000745944101e508a441000820100c07d0320710342136068a05a0354043e2800031140d040031040031074440f025000c1ca400b0703c0501104c41c29507071504039481c042d000e490060203400086103000742c05c0d00e48c0780e00143c3c1480014840069500c8000800064081c0c1094003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 795657347 1250 795656097 795656129
    0x15031514012003031b0328020f1b0f071d090703052d1207081308030a0504180605011b03050d050c0a080c0c0303040b18071e0b03040c 59
    0x598101c1c0e41805420070700c090400101e6000b41001c4003440c070943c0449440f181a603030a02801405200c01c6402130f01ca01b10f9110411250300c004040010381070103296005142400f04c20907074200b13802c90794003080c0007424010b01100034038080c0600b1101014090043c0380e040c4c10310b942c1c4403020f01c02d1071009095000c1100003500040040002600941c0c021080d207030480e6015000180d41c03240040400841d56601001d108428030010344020f0103090761480c4c0c2d04080d075039075842da0203170320102603038403114030100010650400034801402d949040c0d80b241c2e41c2e154900007401d4861031001406100a91401c00d0420003640c22003003400c07211a0b1441d2201550074a45404c0d03c0d00e0064118070055946408d04024604194a004010612450302c440d00d9a80d81d620b46826544207030500200c154006201140004080744206d6070000300b004140540d480d0204031040c58903006610682e803040c2202c914810340c0148598480250030840303222031840c40c090b21380c10314280c0c151041281ea2869000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 795658597 1250 795657347 795657349
    0x903090405010303020d200d0c02030a0b010602060a0c180510120501171221040c08030a030f0501050a051c060b060f0711040c0e300715031514 63
    0x4219a2105001030042101c0d50b100e08000f50748019800d031402c0400e01060b003a000090300040300030542016800100344150301d0807011124070425400c102c1c0c05d88a8080d01c0c0c40000c80e40072280d4040d01c000d0f0b0051001d46003015101d401d580c44940f401d002d2090340b01143c0610640d9420004c01d8401c1600d401c24068170a62084841006501101100c917251030008982940d0050070070300010b1100c01182c006e5041d91205001e14400d0703803c01c501d82c5011008800040a40c559030b00d52150150701c0f1401e02598454019040d40e100300b010f800003d86d00c80308000403140030310826014200c00e4626520541c10140440d607000c01d160350000b1040d14003d0680d01300805900107525520014141d2a1900c440e0032620700c0d2500050011520144404c06100503801e052103840742c030f030426554000e5900554010b1080501d14004215000d00c4503400207117940440348042c5060103070752001452040d01d44011302c070b03240d0920b0049000f05818240c040b580d40d00c1103010300090710310301041c03d152054050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 795659847 1250 795658597 795658603
    0x6031b011b1b090f0605150d0f0b04020304050d020f0106080d031109030d0f020d030c121a0303180f06030c041a04151101150302060307110f030c070302010f0c1a09 72
    0x104001000c00e8a42000c220a241138125246003190158248045a180c004001c440c1d03400f10301c0400400800e1000006444964219211608044100055901085001c2001d82e41b0494041d18a5448003c51200d02d550402883c01281200e00003041a00e017032186254440c2e1312503001d4020140c507046080610f8414808540308058001c1c110341d0809900103002e13140b08190417800001d405482c0526200a009020300304c40c1009540d1040c8031446032210101c0149080704611501016244020b2400e071030400082c00800b420002c861207890300202000016400381e0202c0d401850140140300d0040305c00000c1d1400e5a00750550100c040d00d4a01511400c0c1c0141c0e400000c0340c0c2c0601506100742e0381c11800c0e0352480007100703000784480074403000b019204c030700213200c000c3d0440d8041000820b103070b101703884148203c3d0040055540c40c11113100c0d103c1c5960024800c6100a8010310000c008560b001320070020f40c81694186410320803201e88031008a9465a500b414040c40304c0800079410700014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 795661097 1250 795659847 795659873
    0x1602090f010308041e080d0801080607051315170f09011a10030b031507030501090605030d020c13060e0a0203090c1801051512180601140a0b090109030b01080606031b011b 75
    0xa01d089034044e2481f8000102552020b20803501113000e58004a1225442030040b1541c41c040900ca220b00a0f2500300380c061640800403403a81002803c1129a103406401090140101c000619140c05070130441400c50844000d40740300850b2001c0070b0700d015019150181d0320211340b100d600b400160105860080381c1001c4141c0c8920f28030720255010442410342650005040e6992240200401c41c0c440d010716a42e4001c1d05410b0025274098066000c0d549880003a040080310b80e43d0011031a2981c3e21502c0d1a1108140c1d0b400f441d59070080100071500d1410010ba42510004a84070061b4003000d500c0602d020606019081c040c000d4101e504c1256802003007240c5140404142480b158036003010802c01c51190b1340e003d40303050300851000150031081002c0d42d42c141c000043c40e85071410302d085070b1420b080e800b0b20a21030600c07136030f440000007042440b03840034002d085050240c05103140a4081509000062000d1040540407406584459a20840303610072201c00281c0b4a00002060400c96044403038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 795662347 1250 795661097 795661109
    0x3020c1e090a1803020105090114010b09190506070c03050105060a05091b07080a0807030501060f02150603010b040c0c1716030e041d0c0315011d0c0c031602090f010308041e 76
    0x8003044603c1050782c1544003e04c00c80c502c8000700044c090401c0140d444400070b04c902800c03582c0601c116040f41c0380801c50384c400d0303030800e0400f8001c4540d00d80106519400946040c1da50200020003001800310a02400d503102e4230446190b440305090100050b00c80602401e80d034950f00e2400700c0041c2d0244800104c6200c00e8120700340e55111120400010200030b0102c03051000641002d000240450040e001a9030002207a0050b04018035200143c0d288964020b103215415904d07400d13803400b80e489500c150b200f2811580d94441201215040042c000f800300c6402000d214410042e40c2d144a1031074209031400c50781840d080b101c040f40f03800044e020785014482c030301d070000001000c2404010001400c00c08114250180d84003c40d005218000304642480f98148e0036841141c0218188444012503501c024200c02590805046d158580d18503040940c82c410381d03026104003001540b500220181c0d02001000d40b0802c9503045503035500603402244200070501034a09c6410000c8402c8014140c05450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 795663597 1250 795662347 795662381
    0x10605060301030b1602010b1011070512031b06060105040905061305091b01080903030f040f0b0408091c051f020f0d02070b090a03020a020d29010303020c1e090a 71
    0x18403818001041138054038810804440c0000e8039000700d00600030311100d81c500400420f107901c041e00c0251007003002c82a098040d40101500455030740d07104860701c4224110200296120300c0d42016a4070910300021860059502c0842000400c0c0e038498110b40076905490400324a0751034280c089107502001158801100e41004104102c072040055862a0f520309560b50304110501140107540140081d2520700c4185c04c2080052240c140c4e008130990041d04c5000003141400c0c0704d031640c4c14008001e86040300da46000007205100f5282c02040414020203e103408c20740c61020741d0310159280125681380e100d4800703448005040d100c1941c1a40d814054510490f665030802603502c8000f54014002110000303030f4800461000c40f400503d98900f140d140c0c00505056aa41e02001803c0a600c081103401381c0d219092000d0452a02d43e6050200852031b03225072865040d880c005e424100b26022250103692028006100ca90500000141118084d1010000c84e181c400300d54000d800c01a200e8031800e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 795664847 1250 795663597 795663599
    0x1062102030703150504090206121b0a110705120d0e030c0307030f02090708060d03080c0f0409050414160519090e071e0506030a05090109050d120f020327010605060301 74
    0x3070b01601300140700c205000c03946558585550402048031015070019420082c10321564108014010903130350010303072012003031449001c80d02d0003401c01d610260072030700010b9005164000001d0100240d2020b00012a080708031820180220b40c0d4502081981000b0408407031380d21140d584051040b50030300d08015041c0e428032503d908000d901c2c40303d101022801409004002884140320b95001401100000c0012510300038546040302c115002601303425400201f0064501c480c0c060f0b030010300060140840c00f05840c80d207420f040080e00001d0803403080702d401942803145514580109801584c504440d000000b12713400071161203161340780d00540b945901e40715401e900c0110008011048072540513460f0080309602113400021841c0d840f80b26040041400032031507440302500311950000402e0000552022181c6486141c034488a90034004100d441110707207c19102030017640c000340f01031041580745080980d4403005074804403136030302050491100c0720124010290050002000c00030011a144c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 795666097 1250 795664847 795664861
    0x711040b10110f0304080a0314040e0406050405190c060c050f030a05220e07080a0b180a0b040b0307030206031e152805060f040f03050303070f020f060106210203 71
    0x942e069040495142c41000000c50300c9800000460b004e4a801001400c00c03401c10f96025944a292a103110162503001d1001290002429520902c264010400840c1504203801d00f00e050092244182002000707812058010402044103082150020b180103510a01c4500745142840300195a041d0540000503c1354a107688c841c0c09013414031000d01300c0e00003d02105a215070f80c06081d105410310b010405002811050280c411903034030440b0f1500210711000c10760009203912059508007102501100c0a11843c011a0720581c0320040d000d96041051602c20310000e41e0b2603010784002481400d000000030580700581c000c11900c6540000b05001a09003000e10294280c0081c0e04d5034094806098a841041d030ba44c14110103c242c11080b1001c3e080c103010034480b0300d40c06107843c00c01584c002c200004d18050711095110080d4050405107480c0c0c10900f0005010600c01104d01c2c08645c0104060001c191002c6480c0b81100d10a0801032441601e106050910441400c0b00e00000740c8003204120744 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 795667347 1250 795666097 795666107
    0xb010e092a070b0f010e0403030b04020d020c01060603200906030a090f030e0126061908030f0306040608010c0516051018020a0b04060c02120a02031204030c05060f0711040b10 77
    0x1d451103006581c50f1603aa015088506010910888901d9032010b00401c000c00d002e0703400303050b100d07001810152030034a00c00305c040142e0384030201494050b951080300300002c2d94103125205944000858413403194045080780728440c01511016407203a007000002c154403400c103600c001c0c40107034810700d00c40c009941800c001d03100c0b05400031340e580403d80c240a09884140605051280199503408007001e0f03454140900c1802c158402c0301e00c10100c008100865041d00c00c2002d0400845814181075032460200103010036034005034040708044e030411046483c0103401409581c400e8519581d600d1a45543e41811841d01850712a82c441c860b00c2c142801e1070505c0050702c4071804a009440440031903035035000d1000c00d80308900c1000c0000700503414040051411198a0300c81048100840f100000c0c20780003e8202500004c000724540707000079080040244a42c10340c8010321084a4140c20240301c000340809510074940007c122060708600140c3c0e0384d60310f9009a81c0700001034901d22a50f5040500500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 795668597 1250 795667347 795667357
    0x10204063615080c07200f03010f020d0b030a1101050d0204150c02090f070206060609030f1504140309030601050405061f0e01023307110a12120b010e092a 68
    0x40025280000156200c01e1202210707020345e40f00744620080c14030841b060000550b041c01003a8404211001c09010307075024000d0b000082d103002001603861100b00c581b08202c4800d40c8d20341d40a40c002502d004007166003c01084540c0380c082c2481a034981c4009002030091140d0342212001042901007403d40580c400080000d1600c2600d100000381c07984601141140300c12525100164030280014405042c103c0c0035101020020702110031500060281c1403d0000d20445200c84c212810300f0041440002e00011802c03681c420003840c601003048010a880e81014090540502c1e2280042121601e400d20075064039492012140e07186030301a6401481962040c41c170368018403c100044d081800c0c02850f080807450300404802601c1a44c40100b5450300008141e04203204806040c1002400c0034811403295a00c0352001c2c2e000e074481120090705103501550a19034507440c0210142440c0d8111200d51410340d41103c61a45070b90314810030006a135110358950b50348048942564040e901c0b17217000745c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 795669847 1250 795668597 795668639
    0x2040801270f02150c030c06150a0f06030c09120c06180b04030b04061404030c050706090503060a0911030312011505070302100209010c0803190606020102040636 71
    0x901d00c5040100d000c01d80c0080c0c03002070704010362030058500515081072882841045843c0160038054445c1001d41590804004511250085002c01030103400c911544050140c0031501c54844600300044003540c10b090f8000c41041c55030340c030700c4002000d000c4c5e00c001000b45214500e031100a4000e15103100000038600c18803001c1440f03220054180141104804162000c1e005024146072031078840c400d606401510690b9040c1eaa42d41c9096070302c10380c0c451640f040b40291144120201c00d8682640b910040d503006800f00140408103004555000c030b440d940000401401040000d401e06000c00311910203411158503100c0015100100e003032403581e803412181c00c0021203480190350384054510348640000180141c11000c1e030304d50710400d5940035145440d010314140c80703003c0c00d23641c881c00694403d0b00c0300440b00440e9001c00750302c000700b4000e40c009000948000e504041c034012029060124440c01c00320000b0501c0510925a01c441138406006c0440d0800c1d901e0b042c2d039440000d965100300d52013071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 795671097 1250 795669847 795669881
    0x60806190b1201050a0528080d02070e0606040317090411030115030e0a050a1e0206040311091303142b0b10030c090e0c12040b0a0c090e0f130602040801 67
    0x34131403404143c810200d52002d4401040c0042444510510145203800030408110000c00032400c810100903500d00c0a21540050080e1410030b03540c2c43c21004010009489008108414000282c008207603d00c89550440801d440c0c2d81080005170283c401d0307040c104a440710210000901900d014150b1100f0300781603d04000c080518181c190320790701c2c0040301034260361110741c0e9400010300d40b43d90140c074240c0b025118100022254001140c980c41503000341ca41c2082c8030701e94a582d160541c1c0c0340303801042090b18900e158140c0c0c1e402a120a41002080c0b4950102291201d03450f40c0b081e21124011052070800000c2554100c00030b00140b1400c039115006600308602c0d030003007d01074810389610345031a464010300b4071301c0d01c0c11800e107481e0000c0000c0d0b000d103000c0c004545c0c580200c0084c10701452241440d56854a08038102c103084a60041c00d240400400200400c204040c0294070350b0054101c402c1c0e116a80c3d24450741c1e174140d8454107401000e480c07001070001781308441076100a214003080514 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 795672347 1250 795671097 795671099
    0xe03100b120102071218180903080c0a02060c161b0911040f1a09220b1005030411012106060e042706061e08010b030d09060806190b1201 60
    0x646801c0703009010b801421741070006042101107000f403505000030100d4803040d000f11611032880c540031552071400c0c402c9943e241c20703110041540005030154000710b2380d1622030a01044681c02035503040c010748198003a140c00900030404400002d00045c04c3e40e080700040c00104003198a0b459041c02d43e11940078440d04d40561100c00b0100c8c0000c450442c1d0a40070591040c0d81441452480740810541d000c41c00141040380c0c118940740c00510310103160801940d01c2208000001c1c06041d540d070794010500c110101c001c501c5480d608a0b0969410075040b110401c600400103005903402d10541d90529855524200101c281604a820a80c140c5947e56141103007040075200303110a03501c1d0329041c0740c41a98400f4201c4210003561070000c9120b401900040b41d1582e0751000708040781840e0b01074240b65001d82105211041090180c0d01d00301d1010b40082280002104c00240243e0050041408000c8844081500c680c0c07046450701c0d55905941e00720a519070b903150001c0c0d03035600c00708201008488080c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 795673597 1250 795672347 795672379
    0x30f05010e4c0c0f0906210608120706150e010e071e030212090313050d0302070e2508090715021e070602060109090203070b0a0e03100b 60
    0x1d2840d00010b20180e070307240c0140d8448400586004046400b550340050407010400044242c8410b058200d00c0700d000090a18801c1c0c030040001464400d00e6042c0105610200b04069002d8004620a2401a410268000741c501301c100504034681c4048102c0c8544844018051030072030041420350312456040007582d0001c0115417519905100d007145034a03450004110300a002080e0540c000b501c0c0c5015101c0b823142441c48a002d0304d1801124000a80c0469a4182150704001c540c1e0401340410056007072403d03000c802a642c1d4114022140aa0000b000000415000f0094080980b183c10218027075460502e80070065003900620b0108000001c0c0902c0403902e024148140c01554400041d0407072500b030251000c1c00d401202a0b1a0840c46940010300c1100041f103200b410000d645c10181008030b01d041c80091500314103070070102d545807404e0701240040e43d00165180841d014003600c3c0342c07030b140400303001d66410780c07024001d42e051301804c1d421884860082c0d01484001d041194414201d03541a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 795674847 1250 795673597 795673603
    0x20d082502030c1320091003060b031303090b030a0218041416020f0709022802150a060e0405010f1a0a0504150807080115051008060424030f05010e 65
    0x340d01035090f03000351250f0840760401040070b000d0100c0310f05001c941e01540c00501160120b1194450034444808948080d242ca408000c00c2c40e020440d20b400d010342c0d82031038112500f07480060035040a0b0450180003004050042c860a001440250442c5883c0e04d45200040065031041500c00e4848414844860251500e845000301000440f40b2401e090365825004e8180340080c901c1500541c8581d2900c58141541040618040e0500a102603100d250b603000c000f98002100c050031071058260011906000c5d40011400c115052001c0c0c54802c9072a4801e248000303042a400000034000030004004c00c1c001c05402c2203048240141c0100021170700504a58044480d11506d2030780440c0888041280b4078082d04500c1d00c40b81c48611100c840c82da13482d203031881c00005600c144100c1c0d4540c0503541032030040008503001000203032981c100c440c50505008180e008000c1c49070340701c1c590710142c00d0002d41c0040421100040f0341382174a1081034581c00c201c4005c0c002e02d941220b1960a0076041402c900e404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 795676097 1250 795674847 795674917
    0x70f09060b16030809030f0f18010918022208010902030c0f0d0204020702040209030a03082e03143301050d110907120903092c061903020d08 62
    0x15114021042210b03907402c44041c6406004001941b00602200c0783e80b00c8503100519052072149030381585c800000a510a0040c2a01203031814030000d60390030400301e050501303c50039100c001e50005030b649130583c500b00345180c800c0103410189044103c0c0400e440f00154400c60145008504442c1c02030180300410140755170f075003070b510303000115154000018102600608040f0784005c001500780702c241c3c00400d20308800e084054000544000a1140c1188012002ca10320f4000b905e50b04041c0c074003141164000e00c4688001081ba0003450b10001d84590240815585100c0d204a4000c02c0c840702401c070340009020050400c0000d02400c00010705180035503020070415448400d134001d1041d03803800c1204084000305154240b00c0c0003100702c102c444441c4110302400f44240c54085040b030403c4c0e9600c483c0660706081c101e080d8070450b01e290941e4840004c00d64445000c0314088a454000421150b40350f0242e0b2000303402002c12002082000741c01005070a9410304071110004910038021090840064 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 795677347 1250 795676097 795676117
    0x9040f030c063b0727020708070213050402090412020109300201050402130b18010e180a021305090c090906011e12080f0f160b070509010215060d05070f09060b 70
    0xb00c502044000d80f042c0050b40e00c2c3e55440b0410085004641d5a2404d80e80f01c3c2c602110209230014500c411441c0107040e40b2131404641ea41000325140c5640852001000a8000351052030903608a02600740300f5040b04400c00c0e0301c090039422008840c40601c010122103c1c146500d84080491800090301c140f01301e0f4030481d0001c000d2403804003001c030040010040c0800303ea800801c6d5018000300102000381c00743c000d04500c41c00481d14a8400201c0d40300c0050039010007015007003d08400003590b9103e104400342e441d101c200094503282c1201381d40c5041d442418503900706100c1010003140721400300340c040c100c8118501d4050250b14090320300c02d54803614011009641e0061050f440407900300005001c80d020f101400c5803a005804299104c160010243c4101d074001e00302104040003590901c542d0030010904080342484261030010351141c0c039000d010003203500d0190000340350740d980184036410903421001750b4030902d446d051031440160700c07030045000c0e00b0700303040000901c101c03103104170303000240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 795678597 1250 795677347 795677353
    0x1030903020a020d05011b0c03140f031b22031202060402060406030b0105091206150a0f0b0d230f090a12051e032a03010509040f030c063b 61
    0x82c3e50070080004c3e08a8019101507681d1890103011002040003600000800c0c0c41e16141a40c0c2882d00404448040f540d00c04d03c010244802101c1c021003030b003900d4100304629842c0d1006a03c140d00c4400e240682e00380c002d14404c1c0c010038000030f00e10704040310041d40c0c020034243c1850082240160307039071601075a00071b400070802c120803c40340c3c0c840e034070613610200c051402c07070300c0d1403410300010302102450414525903405c05006c2c00381c2070404c0356407000d5800040e0750601c1e1036807400044103001c010034032449981090002e03034800103d209510241c071200e0070324030083d403c60240b80c03048038140044800040c4441e0520105010300700015003c402950700c200500d08000000f00c0444040e00301c0d20750a150501544516a012040308000c0c0d8441c041181d0b0010184c4c44c00e5103043d0464010840c0004480c8040005000c6a100c004200782e001d90032030000f03d07000d030f0146400c1b1103550388440d01500e41460113940c409841d885ca41d02c0680f90341d00c0c0d000d242882940500c500443c020004400140e68 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 795679847 1250 795678597 795678613
    0x609010b061c06030f060507080f0c04050402090103020f0403060630061e240f140f18090703031103030f0106110102040f12140a050c04021614010504060b0103090302 73
    0xe020002d14491009a407075010540c11341d40d80d1007030605035420f40101c45158442c020881025400350318140d000100c1c00c80000781d4140001c9140081c403c070300815000e6a0006900009a40240c040b03844c1c03031502c2c0c400b0603541c680d00d0400c6030003418203000e9141e50882800c409c841000202c0b1049002c0607440207403440807807507075450784020403130898490480180040841002c6a0512408407418400100029640345507040350f07100d4555508542e42d40300048000344501480c0b0810404110070544070b064942000000040282d980041c0c030800100d42d11040081c1e00b0000304aa204480c402c0d02d031001007800c503400d000d8403800101c41048200010000401c04944110407a0090034440c100040c5026283c02d00103841d881d0712b800c80403503544442061801c07c40ca05500311070320094400501020085d540e60b003602c45403002d080c40e208980100300c0d040c085902d0401000181e81c00010303c1140200008050301a010480302a50301a240c8203022201c0c0d4002c0c05202ca0550380b42e40981305d04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 795681097 1250 795679847 795679867
    0xd020708150619080a031218051e0309060f1908092d0709270b070f0e100206070905120c01081509040305040f080c0f0d0213020301170609010b06 64
    0x903a01810307100078500880800120a1320900c85100118080d69420b100e40c4039032100d05040c0c1d00210400d00320080c1d504d203840d0100782d0104480400200880e0050304c1d0301d403100d0f00b03a03181d0f000300f0410f65401f6000140088c0101c0307007080100720405a81002d500d038681144d1040e80c609100b00c41440c650b4120032040b036030400c0141e9144105080002200b0160340c81c80030641c1c50103074079421141910b0799980c44102203100321902603070304400b5600b40e884c071188182e03900301c0d0005029101c03a0a0008000c007082d8040c1c040e804e407000c20400902901c1246400351002551007105642c04c8001c42d880c3c1d00d003c162070030107048040314074040e50010700365584010011206060010010342e800100e07014890400d9446101c06030082d40299903070340e212403d085400340c141c90203a00c44242d40c0d01c02e10301ca0101e615262920005004112202c03008030f580b60011881201560500045440c400800452910140404d105030115840d044a50503aa2403510a0896038021411540030100f8007900d025 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 795682347 1250 795681097 795681109
    0xc04020a092c0108030403140309101b061506030c360f030c03031803050615060c0d1e0503100302060325172427090d0207081506 57
    0x10600300a820034001c19240c1042c11040030030b07002080c4030341000504100340b090099900210804401c0038510b0010b4031000500c0848504426209201e454004009419006001241007603000001845040b840c0507802102180078016070001c40d00e0055254216442010420100c003000000a504541001c0095070390140580710b0850f0814110400b0403000020304080008510506110f400c0c5800c41c50302030100c1d280303060081b2a441980500b04089000042e009400403008900d1801540e80c030802b042940c49501d218642c18428000403990075580042800240340c4903103c0100400030841d400c44091000355090303040301540e28030031f001500d0080700840c0c100000081da06622501c0c00030540004c0e1701d1403183d002041818448800121807a80c0e0319a100d150b01000500e6031060112449602450200150158030700003080b44401b61a04c043c2031aa46881c55900d0192909a548036548c0300f240001c4801401820000288410001110440070200414604a43c4d507009c1c1030000f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 795683453 1106 795682347 795682379
    0x19030203120c0307260711101706040c020a15061d1e04030302095802010212120a0b03071419260c04020a09 48
    0x91610100031500e90300d0780910286152540c0a030401015103010710840307034241740000d004042c4184160041c1e0700100403941c1c204000182c03c41200c2100000107000305200d4075002155403443c1541100c00340b00c4103841280e088070b03140c1d25800b400820680070b600c0400da4500040c04040080110111207440307a0480b40340c2414a43c0c6109845120080103647e0040c03100082410188241c04803800810300030036824101d0340b4076201c0195080c400000c00e503560b81406403144680e40c44504000d018142e566035220441000341207401092003500c04034118080c1414800c802d10416000e00840018241c10b10050314080c4200e0b0b0894203800f200e1403195108110400c100514550110511081a40c1e060082410340c003500c540c03890560010101c0028100d0800c3c0449600880106591042000c4a80d520250020311080344240702100e000541e06107401d0000041100d0107030 = true := by decide +kernel

theorem cover : BRFrame.Cov 795503597 795683453 := by
  have h0 := BRFrame.cov_init 795503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 795503597 ≤ n) (h2 : n < 795683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
