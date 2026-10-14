-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2312
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:20:03.136814+00:00
-- url     : https://prove2.me/submissions/18acb8ec-c465-4652-a38b-87be8b01f147

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 415647482 ≤ n < 415827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 415648732 1250 415647482 415647493
    0x20307120305072d0f0b090304030203120c031c0b0102070603021c05130f140606030d09050d060e1204030c05040204080604030507050c031605030d030c0e0d0302280b0703060602 78
    0xc2003030321402413015000196000003030b51200303e2841c00c003001d041c02901c1e11070030300e00c000080203800d0001c1da0300542c1843c029802c05145500113691032424a016802003500810050740d001000c0045d07500140604014886d0380440903046401801c006140e1390052080080c0003070100d00074400c4490b481340404001640c1202c481c80080a004060320402b4900c02e50b00c00c0d4004100d0341c0d0141c5150901c9940c1c83ca64031849494270b40c1c80c1c16009498103110340c001c3e12165078002d40040419044030403d569480010050781130a800802c440010190315006401341c01001c800900001d0060f41e210783c1c0c105400380d03103840500c0304a000c0c60150803865400300b00498042030086000d007250302d110b102141c016054050119040220001c1403001240c2403c0301070003c2d2030148801000b001091034100030b135002086000b0032842c02c1402660045044150b070105040c400d1203c010703014404002c094118548055114500d0713a0300c0e0081e120f812450000c6002507202c4e0049504981a5900428 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 415649982 1250 415648732 415648747
    0x61f03170309101b0e010e3102130603110705060106180902071104021b01020d02030117010c021b0103020d02130807060206073504050d08090106030b16020f1009020307120305 77
    0xe4504c8051607207207051047c14481c0e600d4682c2e07039131440c8583c04080c0b04102c455000c065480c4c415801e120007030501c0c0c1c070300600c203012115100d0405607080740c0240c81c0200703411200d442044414811301302c1c080d009029140c00420340c5900040c050005e50b80e50b8183c0c1c9042c030f6544094204a009951004051440710007040792140b5040c3c000c3d00f4520345c1d41c0c0071440c2a4102040312802ca0303000b001c0072205141c0100c0100110f502caa14010b02d400b0707800c0001d20136030812140003034486a122003c0b40c422180740c6480d00a0303034400d40c162850600d00c0c402c11941d84802401070100040c203807285c82003600c1103590115030300348080b501c18001c0c1c0712600c560444100030840e09200301c40b16132802c007170042e0b030b58450200d060903ca16280928080c1003d00340401a0000003880341000030806440760381069020000502810b44150380004c81100101d001c0c3d1290000f28103000b0361820b0410303031f44111072032890b40741c4890717005104040c402c50031504902d503181c0403001c400201b500301801040d014080c0c0d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 415651232 1250 415649982 415649987
    0x90c17161e0e0a06050c1c1e03270f060515040606030b03164a0f0108071202010503090304091e29010c05010b1011150405061f03170309101b 62
    0x1c1000e880b15040c1100045e107064143c40c001524180344200103070300d841c0e000c0d041d090a0380c0c00307001c20805032b01490b40d004059100c811403808600300081080b40e4482c001110048884111740c1d500304010700034002559039840040c00341400040c11446400742c00042c006440340d01c0040c00484800f1655030783c5022158019100b1030740c4001c3c1e4100e003003c91550b12150303204007190182100c1414640c81045050540c4001c958210582200003e988658801d0000340c3c000d20f17440442541c2480c040340c1da030340d5441500d400c5001e56030007404014240101c071700c1000346c3c0d0100c030200c0e4043e80804000103a0107181e818440860b2034034440e000c00b0b6068827100103500c103604d461802da0158002142c9061480c01041ca0f03030303c107180d10b08001020400c100300824402c0c840e88028010036000c2d41c1d80c41c2041e07140d90744c52340340c0030b0110200709120590404c50350204250520046400800c0805c005a000400044c0d551046440201c3c034050301015440c100858455003c411611008508081d281500b06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 415652482 1250 415651232 415651273
    0xc0c1515010f120603060203070e0d05031909054c0e0303071208070e040603021003050603120f070c080d0e1e040501030c090c17161e0e0a06050c 64
    0x1030000f0021660905030109002d07000b030400070752041c040160340c0c0c0b03012000200b9510041800b50300c50041c001031800405c000105035204101c081da01d107802c002c0d8404081e100400242d20180c2c000180c0e03030600080e034041420551800f00c0c0002c0d01e00c541440403040341e4000001c0100742950b400c0398154072181520403d081c0111440150440f45010240c1e12452110f2030340b900d070400003441203c1004481540318007040d07480e207000d860603c00e160a55001a448061542c8040c0800d662a000078510b03035001c214825030002d1903c001582c1e903240c5500342841d07501c242c1e010303500c54101210001c5c2200000825048900c0b890352603030703541b1580300d08010488189032072060302d80354001d040c40003a43e0345200d0365000307500c10440d9410803407801802c44141c0d40581c000c03600b8841c650302c85810b091008038400b540440007984441440031612410764458407583c0d54803884001801002c28010381040401d283c40104450f01c44e441542c82400710340b60b105504224203503800480c0a8110705c43c02040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 415653732 1250 415652482 415652507
    0x6090408180409060212010303090f0b090d0602090d0317010506030108061302040e2e0213090e1014090105010801051605090315040302060a06060206070c0b0714030c0c151501 77
    0x450303d08030070b07140c0038283e801c01c1c241000e00d410341d0001041010b0300504008001c7c80005002002d0382d00e051852440e80c080d503c802c9000f00040c0c508003003081420340c100c9544140061100c0302c484883d013070042111500161595441c140d83c1c0000c59185082c80689049620a80007040f141d43d81d2508040f4602d4203603401c90b00726840310000d6205d510b0030b008503052a03c800b000d100c414407104a090f0100912684944d2061380b042049100c0002209101c0d01901d02c050008900b07410f102c155180b03040b4035110140551071419603141c181a80510f095806905400028001662030f18007441c00c0b12410394124100030840c007580e411841c050009011000c1c0010240d986529840c03208040c101000c440480050b04000d04000f1b24618501c03580c00070f01503500c01044c4a03d002040500030154400d0060300b110120000103900310301c624506080d01075480c052680364100340b1032000b520f400504100d409406402c0f000141c01c01e100310705a21036039070346010800030225100155a41d1b0400703103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 415654982 1250 415653732 415653739
    0x60c0903020901140414070e270112061518200c0a03120501053007060f03060b12040605040201020a1a01030c0815070e030a0203011506080609040818 66
    0x2000001507961501118003c0007080c0d14503034841028001c20084848090b040066245401e00f4401401c1e80408a01c0d06001c0a4440c0000f8a040b1107a40300800048210410040100c00000c00d040d41c4000c85920101d100d0502406010560001550310b80b00340d0160b200b40034942d0040000c03018464000210450390044511008010f2aa058000c0c1d030108200b0011580424a4102050751009805425621600041080d07505010014900a0301d041e4141c90300c1c0e942c82400c82103111240005524100c45104444065030f90710005000d0001c1c82d0b210720302091030701000162620004046921b00c100402e01c020741c6644594407035000f803802078020ba0451050a440e0b00c0040d981139000102c1740140079039115590301d9494880b0300000550403c00e1150030040c0c840800141c50141c0c46d400954130b0030b00300100c143d8000464a00401440c0c0a5855070070f110b44096142c1c04070300e44205481e015521099907070b49000502c0090315041c1c80040c0300c4501000b40d840c0d040c0e03120608078000d1a004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 415656232 1250 415654982 415654997
    0xf020321270a0b0606130308070602190804031e090918150f0f060b18040b130213060c081c0908040806240a05010c080f0a0203030a05130807060c 64
    0x1d010050381c00c0221015030115911030319100c0280402c0c0c01403103921003001c9031103c0c03a01c11000481992410b183c4401803d4800c00f00d01c040402ca0300e5010b9031182da07a030982030030107050b010000400c0f500e0161801d0307022403000c000041c0c0c8044400d07550200e48800382c03038000700981381500310b600400d4184c40759030820258101601c00603152601002040580a4002c01d918507a03242110440d2049022204100d1030000c04024603200d440580342d500f010000c043c03840001c05400b0401030b2100c13098195000d03101c6c40d5009103403a6141e001d850b142c1c02d00b4621010841c0c80321015503290701c904ca806400410305000c02e0419840c1341070700110810b01000003145110040d968101c1a030003581003000f81d034000e54108030810140440e041c00d8400b14100c1d003084500c9000101e2180d0703446010702da04000142440c03a003848800012102400c820200c00c95903803e5a04000352240c000b41c5810307560384d007800b0100d140034007418aa84e0341c4c241c11200300c52a000c919075071040100b50701296141402086d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 415657482 1250 415656232 415656271
    0x1c0201151e080f060a110403020a05010c1529040504020d0f03020c03120a08060f060d0b0301060b16140a05030f0913060605040f170309090712020304120f020321 71
    0x18080880034a03d18001410b09081002c990000c0d00c0c0c0d0803003040c0c40241d01b03020030405a900e500c08402250400e080600c42038040c0d0501d050071860542c2080310060510701c04454000f90382450008900c001880c071180100540c04210981d00140c0d4003951012842001e40c02250080b51150f91700c0307100740101c80b00650004086420140000320f041c00c030b14400700318125056001540140d1116040310042c580c0130700d0b28002401d41c09507001c642c25859841c2104241900d0962007080580350030100c05807129024207010320300002000c1d08941e10901c849001041840c00280d10700004ea1244c091820038043c182d5100298000c8581e2a03030282c011454240302a14a200705c0010b000030fa501ca6a807181400302c0c0014600c0316521141218001d49058640503c0100940d075111400f140c600007603845051007100c2d4840c60302c01c00350a9500c0041031204110b134242e400c004d041c505807110390200764801c906a8490045c100b04441e900402c03044d039422080002e032820b07402144020645481c1d043c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 415658732 1250 415657482 415657499
    0xc1207120b100812091807091502030405090a0e01110307020a1226070e010f020319030b15030601030605040c080711121201050f060403080706091e051c0201151e 71
    0xa04d240100f481040005039800e6900309a07050701d4054809010b2000e86050410000340040514802d65240342c42c00b030180003d0300c4c82070084500403c2d004040c0142c500b0030001243c01000d02410900196103001e59100e103000d140010f070391054050381c0180c00d0400503174542c40380315400f6580800410400840003403c4500c1030001c0120303074008506000349071406150240186c92800400750511102d14206104140d0000c2200d04030f540e0924041c00313036400701e18181d0181c110803028980c01358244489440d0345000d03401a41c17081d8400da0f018070506640d20706001c12618a0059280040c0c036000c00502c081c1d0107100300e90a8004841c003144c5480b10041c64648113500320407403000e40c0009104c010025850f0100302d102500808840c1a45424135541d00c0704510b1103900c4000300040d48a882080520200180b01aa861103038068991000c0052034255180e1a8400010309110001541d500c20588148140840d02280d95042c4810300e040002d04032200c412440300400301e95144d000401c61a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 415659982 1250 415658732 415658743
    0x20d0507060504052a010e0319150b0301290405070507060e120a02030d0605182202130606030c1706060705030706060801050610141b030d0e0c1207120b1008 69
    0x805182030b4805c007043c003d00040c001a1700e4021240b2a03800103040440820790b6a0860340d22541c0b10103013020461010041d00081c0c400206220384c154a44400344644c2d82d15100c4100790580c0507120000030701c0411040104a9100b510610b000603c2031114000052a561001810b07500c0c00049a013044c0c84e00e03080c0700c0705520880b4a580141c002042c1c1407101d103020b01900d005440111000050080c40070700005d1151001081c50020f0210f000b2a0400c0d0130703071080c0070107450382c002e13022f07130344408500c402c183c082c002030300c20780f40001c0c50801044c82c0e00b881390106450b04000c0c1ca44005080c0c4400b410442c05800c407000580e50b5000400002d00010a64810403005164010011459140100030020454400d440440c140840300d034402c2881655801110b200034034107008001103110242c941d51640c0076002c031250200b4504800c0c90001c1000060200c036001c012122400d40c181c842000719200c0340e940c4280c41c040309500a20364006014003556640c0403546406032516150354a542a2074032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 415661232 1250 415659982 415660033
    0x20a0f111e0f0402030906070c0c1505070b060f03100e070b0c060601020123040f03050702040f0f0501060302040b04090504080f03160201050c070218040501200c070501020d050706050405 82
    0x20010007410006030070020151442c0e1001103800314210f140080f1801e88070300b8014101020011100c20100401001d0800360000e001c140203506542c1021500203001680900000c0d261022294000b9183c0d00d00312209581030312000d4044c0142120845040028085111081c01107025144001c140e4810740005071980e42103000c01442c883c00c107440003a00311482c030070240044410b00810360701e101c4201640c0340e411540c44412200c3d25032090804039601e000c2c0310002584107003040320100060105401a541c100c00c136038802c000a99030340300e00390101d20840c415000c0024007800300f0002151720703501151b40240242040340c03400d40c0d07000f42c11040707034801c841c0d150700d080c00c200c04204202d50910416a12521980c41c06250219913000160300140c050429400d40f01d82d10000b6041150070340004ca008041c40c04030380c00000190000504940100c020b44c04980708601001074150b100090000980000c0d49400e450310340d80d80c65400c09058014026640e522440382944e20b580080580c01e02003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 415662482 1250 415661232 415661269
    0x3151c17161a0703050105180a0b04090503030912031003060f020405040c0810090203010509010b0702120f250b1903110a05030604150e0604020711100e09010b030106020a0f11 77
    0x509a031030305024a00d0b202030580c8041610700001401241c0f517041c5044d081c00c0140b003070900c0ca95111814035002c0c00321000d203190441d06126800c1d04010f40000514040d003407503c00c0c0c505046d408031501d040c42c04125a1018159103100301000422465808001020401400580340030f0f102d5002c9415248824640d00000d54128204024a0840e071800c0c40500081c00d010b61031940f604002400000040c0505007441000041e65411503645001c0b07071000d0305065040c0c48024420084058541c2042c1c10440e10410700c4803200c25100c030318480c0c44d2080e119258031640c00c1000c080c503600c0f0740c2c181010041c000d045d580c001034008107070700e48050005009030340c1d00c0075500e02d020000d00065403030100300b464003010006024084444414001503014000743d80050b03c4c3c0b4218281000c1c48081301d1006600a11300d4511800034603406203903901ea401d41507494000d80c0c0da850301104c01c0c40c4804d1243e0302c0183c00940400d40000c2c4000d0120661500401c0c20025022950700025018072865002980 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 415663732 1250 415662482 415662503
    0x10c021801030c030b090c030a020103050603150a0b010f1b030804240f0e0c0a0510090306020f030906070801120b25112104050f041103010b03151c1716 67
    0x1001703003084200b0360060b01300029091074000c03500442c0da981028940241415200c500140080d1810080710001d2041c400b561a19810946070850003440341c1560035000648002c01202841c0c0580443d8083c800303540000c2e16105450303101182d8450019100301e400c054000700081100d040300d0700d1103000801961000501250081e603000803074880f208800c0e40c0341c0041c1408404ca55a0103906811217000b590350101c400c450340002c0700d81440507000200340300d00c00705680002620380005544181203003021100f80e41c4130504151010402480303600e1420000324080b030006030400410300c0e0070a071980700140325080c0101c8610380101c0300f0203c8100062a0450840d0560002c00186640d114601d4400c017400d6004200707003030184128040d441c0561418604690b20361910340c007205821aa03d1403140d01ca58403944080035590003920406405017107801d5400c1c00b03290051042d101d0500640c01100048100d64440110441c1c40c035034203111034010b0250029040a80941c01ca03c0c1d40308011407039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 415664982 1250 415663732 415663739
    0xf031b011407020a030e01050f0c06060901050913030e010e09010602150c130501031505030a0503070c090b1f09050307060c02090109180311030405030d030605031b0f010c021801030c 80
    0xe0840d40074602400c20111507400348030000c0d0700814032003052038040c5445c0301d1032014040141d0390342c443c400640c201d140d00004ca07030090f03080110f680c0780070740c204a07500581d07a641c6070200301c81810203a03490341b2a170015804d0072000a0180d980c1c02d1f49010103050905020114000040c10140f00741e1101d00560000c0314841d07070041c98452000d0b401440741040314141031a5503505d0121403400d00500b030615a40d650070b003182074440320000740200402003c48080d0700842c6001030b1203030042d100403550210041c80c082880b45050081c0c0104c090701802c400c14101c2d1a0f10b02c4001303528075002c2ca03c103200b014000070849460500048014200315100e4101c1001140706200100302d05078440e802840c41c20614901c03114500c40f500e1083c0e43c0500c1c002c44800c0c1214006811846183c0c0182d615200308c011880c551605500810102e440890644030039038115a0201c42d400b1500c00143e03440f1800060706c440700d40c0662040124980090f20703000048010400002941100381c106461031840081c042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 415666232 1250 415664982 415665037
    0x1104090218120d0e0a0b030a0b10140a05030a0905060f090c0906150703110d09060f0e0102060c131a22060206060607060b0402130513020f030a0903020f03 68
    0xd506500c03040e1942c2e08545490300da442d869100900e034900c204800c4401c03103850344e03070f80924a1014102c1100b55a6407801c0040c0d88100030555100c1a038090030080321501c08543c0100e0300c1c00415160135000900d000741c4c16004960b6a0310045c40d02c40215521405540400e500300002480340003000c0301400d940c244040403502d011401c07038003940f10b441d05208202940d210844000d84e450b028100086d2507030b03018034068071641c2c005078030180c0900c41e6207441a901c903031108081c001ca070a192546e03132000d091044200c2d0803000d50081c960143e401070011624039074450000b08811607141200521050301c545400400c10030130101d00401c1c400200341080e102000400004081e000b2170011a80280384c80c00180d02c4803001019241f06040129021040c0f1805800c902c0c0740000041c03045640e032120b4844290340d101c8a0080b01c1c024254100354810a045ca8400c4500c000c2817803200d9811591080100d402030f01550100b101140605110030303102c51401c00240c40003d0070700900140e40052070044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 415667482 1250 415666232 415666267
    0x160e06040e0a030c0b062e020a0b04030801030c06031a01110102040506120a0b0a081203070201090609032327060903030403080403050c0a0627030c09140c03070e1311040902 76
    0x41d07201f91452100c08800004051505160110802c200851448509416400d03c180424003a0040724680c04100c1010703400700845040c0c0784030352820802e01d51145d6007101200c051101c810b40442c20024941c480d580101d82c54440710800c0400503103400d4844020800741d13000b526800c1542e0f5641030034454410000c1c0101c603541c07401900d00b481e15515004040e51758034805100c41e652088008042010746100390008014160002000d219142d51841e00600e012843e400981c0b40c131003c0d0f1041003511160000b00e58031012490400c08101440b04200b540207281280d005a10080c2080018140e403028070203071005502030291243c8840c070703505101d17043c03555000c64288540348003582030002507080003039410850703090000d080a0543d0fa9000caa01d140c00740c4c2020740076040c020400925a071035034000c2c04481c4030003500c0340b500b501c0748103070000350f03000035105040400c0c00c00e80d20207024200410f040c00943c00c05840406d0f50218020f125800d40c1c0250400900c041e00064100b0031412104107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 415668732 1250 415667482 415667491
    0x307080a0302030418270b0a090506150303070506010e06120c030d050d0e010e0f2812050f0a03021201051905040f0b03010f09020f0102160e06040e0a030c0b 69
    0x142031844400d68000392248503d00070703021454000400460f00f00c0640d0f11404418401a12480000d502d281942c00e02202130714046482082110015000c0c009901403802002d40c0900184411b03200c40005121180480d80e215815201c03c2c4510408034604000a50081850b4001c0701840e00345801404840081190b110249520010130310045890000d0951500d032200c2c609583c6032503100304000060180640c81c2c500a600300041030708903600208030358051003005800c41d500382d50501c80c520120185042050080e8400a00384000700e1040010303c1c140381018175050b460421142c1c12418150081c03405000040c0d03010512076410403902d17002501500080b20841654040c2c000e015a10903030340e01405010326220b1031a00c0000039107402c0901c43c024018028000301c2c904210800042c40300c680268440c0d00541003501441d400860040f640c88024010b4550640c100b1001590000c8007425094201d0b58403514503100360700504c081c0228903c01d544e1049402d09070b00740743c84518400352 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 415669982 1250 415668732 415668749
    0x4060902010e101b0609060516120603020102030d020903030c06091515030307060902060c1e01050a0902030a1e0f08030a050c34080304081c05040b0a15050406090204050307 76
    0x210303466541c2e6040084055113244407004d071480f40b6028a00f01e40070380780145c001002542440280a640740041c0c8110b4480309681c1e030b03011420008201e01c0800e079003040c03001a000d6001040030101c01401a00142040540901242c2c40c00310760b10102894082c0c121568145a00084810840700780803489043c1c0043c50710856402112113100000d0305c82c4680c41004000035606d030600c030119103a50b42560340052010f000e40b02942c0c035118021003d40b00c3c800014845528050001e40008140c0c840c20100d80e8004c0e000705a000181e5030340303000f50081c0d0103104003000418022000051243d003036005c0381c248503200d6a626030401051400958401511ba80705407a420722110050102c403000c072100501c617103e41e40c0207040d05917000b1202c01040c804042c040340310010400050198000050840d90455600301e04203e00d02e00d51941122001d440044c03400e901c41010801844260f00002140464034800b42e00c5280c1e684009801c40d0915481200d00035004541001280350038060000200380c0c03038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 415671232 1250 415669982 415669999
    0x11040212070509010c0b010f090e0f12160204021b01140108033103061401060f09171c080106020111031303270303020a0b1f03030e06090904060902010e 67
    0x90340e000502030001d041004211011030940341c540e02c19030144410302d8002d60340c03c1665842d640440001d0700c41c0e000e29010b42c5c0c100744100c81945400261680607400c040701400c155442091000c4d180da0180141032103007000e0701083c2c00540c0e07c0e44020820079403003948421000b41c483c036a56003511081c1c51814010403608004011a01c0b01104031100785e000702000c2d90b18030b105090710082501118070301420030300f28103801104002c1c46a110542c2048030005a06039680d80d084d04032806103861170981d000840c0420700304400b20242025040c5418030405850f9200d0b014240110b0f000d2100d0400b900081001d00108038054080c03203a164904640010b942c918505075a00340390180e0b008200408102c86c1e02d10040619101e40c08011718000312104940400d03549040017940c4507100b003030a84d8500101c0010800b01d008803140071801d08000c0f000b8001807451a2010344580132201040743c0c001804201c0305026035111041244601d02c00d10000980340c1d540e000052100c440700c0030990040c0c404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 415672482 1250 415671232 415671247
    0xb270102030403170705040f0e0103052e020f0712081f0302010c12090e010801020301031a0603100905010b121e01020f0d05061804061a06040506160606050a03050a110402 75
    0x138440c4044650040d00d00d9180b0346650000311500d116a90106180f8920b00001040301410401542d0407207001c4c208a8640f540807a010300b0786c10055601e091102010103d03d04400c103000d8014080803180391824909100c0e00362030317198424044088900000e5500342c100030048842d0144d400c1d03220440c1400d18101429940040e149051003000503200d00042c01d400d1a5491060320004050100d01104060310f594545030705010350000e02040b901e240d4200c445100c0804c0d10341c0d05521a640090041030701c505400c1d9148010010501d003501c0c04d5403a04135040c1540c9507100907010003403c40d001040001c406650180b050612803030414401c0c2d0040100b4204906c07202c003500e102c01d070040000146501c500c1c002540915803030321b425904013003400030002405090350140348203101c5802080004004081004102e102d140034086e4000418000741806041c80c1d59038200442c850000051a00d44440000704120007560003160300740e2009502004025401032004001c030700039102076091249 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 415673732 1250 415672482 415672487
    0x210020f09010c0804030c06020a11010c11060706110a0f0806240a11060a0603020915090a0e07120f02130207020f120c040e06090708060c03070c0c030b270102030403 73
    0x1805400904110710a000d000074811000105c400466200f801642d05d2680c8410194685041c4a0b00303030f0b02104508a5021154010345001783c2607a40114a803940242c00c608112143d08800307400c0c0c90b0701c0da47e03080c2c0d400b100c0c80090041009900d6600c82c450b90402d2890002e01d04074004150301e0103410440d04140c4100c101c201c900d040c00855482040e1103038170404085503003298417002400c0a220b005c00344080b802103070340401d040e00d000340c800030a00d80e030b0346192041c20b2510060b11a00100e0620024003128065030103083c0801d81710701070340c40b041e50390424904980440070058404a0402403c80f00b145424607122400390f610000940c00c1c900c0c15000500c1c07100c421504140601440038000d640326038240300f10350300d8050080013001128074280c243e55950404132a070b00e04e0361103050b1010640c2040001e255105503042001c943c9036590340e000c221611914903804030b50074014074001000103007044070114841c402140361003074120741c50246055100a05000c0200366403040041c0000700760f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 415674982 1250 415673732 415673737
    0x309040606021209010c0201210b090606030906041101020c0604180b1009050415031a07020d0c05030717090d08030702060c0a080f071b0303020c010b03030a0804030f0201061a0a0210020f 82
    0x80d424201b00c0000d5500d0300050380c2d03200101c80c020381c100303964004445690f450b5034030020384284251441c0c02a176566000b8271145103c117071848030540d0f00a90010380041c040b111050ba140506205a4400d440c801c00422150381103078001e6824294120320590007901e45218100381314008441280c4a500361940c041c1c8086601d0054501441c2c940074050b018200801581d40110340c02044580100640001d00c80d580c58241d50400050003882a529500340c0b03d6002c0d95450707500300e005035141042c103684000c00741074000d86090f006401409140d4241d40d40d65a4810f102e0300942d001c40c0d4a1508450080c24000002d08034203000105102c9641c00070303444000d16078441c07400303881d403852030312405e001b80d824295203140510007130702c44045201019455005003800180c480c0091283c105c80d603003090f071240116008000054110030005010a104505120240c00c140c0000181c140d118400e0f054545641700003014181c40014a48800b1136041080040361110040c003181800400100030030f451 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 415676232 1250 415674982 415674997
    0xf010c08012c011212020c0105040b0714060c0307090b070b190b0a0b121b0901210609090b06010908121b2d07050d02090403020c040e03090406060212 66
    0x4001c01104400c603034040c070075021031108200004541d07503944d03003c1808400c018450071503008001c0803a4200440c00052640340501c030584841c2d0034076007401c00103c81600440c1e002c1e1103400c5140e0000c150b01c0003c1c0616070040304030800056503450700c000064501c0384180d0044414503810420480481d00701510260003040540d01604d41200240b0b00401505000441540c05203c1003400503142813404010314801002c001e41501035070303030b10310040b4141040203a06c514649040218031440d612071648214403907070204288800740405501070048a4907900700c0442550303541c4080c814443d103142061790001003440d041760124245503000c0d03299a40080188010034000c10b80a116a0007045500107c00f00300302141c80341202c0d1341961104101c80540c840c0a03020401c07070340c0c8103220041500010f403200078000c005241a940c0c01d00207804802003042e0b045016454480c01aa0b580b40030326507188078142c0055850b00c440b6000c00003280d00c3e030b034440e20541d88a02c0c4a00c0c1c4049040b030513a01d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 415677482 1250 415676232 415676249
    0x120d080c0702120d0302030702010c02010225051f05180a12080c0d0912031b05030114040f090b071b0c03020609040207050304090207060614031009140a050c030f010c0801 75
    0x3207240380c0c804903404501418101546000344124150401d0785940518841c01d0254001d2040c500070b92416406c1b88507451002c2001254a807000003013801c80c0086801c0d091041d0200c0d140240403003603801c44800e0f45038241c0d444c2a11071061100c202440140c203040c451103240502130004070359a41c8848001900b20350014000d00c0300009000000b0f4006580c10007541c2403040c01100c400d450b10828a02031001c101d07010074640107010400b900c15803803030010380300039032201851642880d4040d500e040100c809154000c0d101c03641e40108040d203005440341a4800c0c00d0100c15070410080182c02e90b95481d200031a880c2052071074101050b0907400440032690185e540d180c1c0c0f030445e0310104001e0304c00e150002d0021301c4001800240c031003c40d030040c004503018440403c807107034603000e1040001c03001d154003680c1a07104003045902d46e900c51b032011000718489e801c1003100b2501c1540346420406642419a5141c01c044a16400d80c24140007401c2c007011510000c200e100c506c0f0030301604145040c05550705 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 415678732 1250 415677482 415677487
    0xa091d06090402030c0d030309020a0806090307080d0213150e041b030513080a081b18100207030501050a060623040e15150301051e0307050f0315040b0105120d080c 72
    0x10f40d1010710880f80d06640103840040110392505000d0b001c1c1c0389000089000300c0901c800010ba0010101e8401d0080c0c807114061072400d01c0f183ca400b850303a00101507e1600c0d40e801c000d107400300d001503009980104400c041204a07448881c40252120520300a5507019a0418124001e1092584444400c003030060034005140d4489500010600c4001540201606000540742c000c468105501a20801c0648410300d5144080995035115024002001072280600000541c1a180403402d038242d801c07051049559042e0f4980381d490943e6001d540984000341d030b402e000d01000754052504010b8000d1104402c8004620700d030034811510032803103212021140440840c1801c0c030519609010140d004046606880c40c5042102440e8400e2146a100e060084040c0400ca24588040c1c03c403100003c0140c20070610f07003020b0142d5000c80490301070b4140541c140c0680482001152217000328001d400c0c8a515605080034030150300c4000070016282d034030207040325581070744c0440900d51014000c001d240c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 415679982 1250 415678732 415678741
    0x2c060a11192127050303040201081509041b050d0503180d060f05191406060c0703170702011b050604060207080d02030a1a010e0102030f0a0e1003020a091d0609 70
    0x15401d040c5200d0ba01140d00c24018030400341040b0760070012004000745582d0001c019074003001d43d0142c0510030014038035002400050003541c002c81c900c0794000b0a24050300c00c1c0300056030004002c40822201108c0e807440e0070008003160350b01c115090b0042d200c1680e014400c92100d4a41d65560b0154404034a040202c20b5600c0d14a43c50f5448420076032075000d00c051022030341e50310001703000e010101d81c1e5020300c0c01d03440f034042e081c0829402441103a0006e8004e40001f40c9a00703040c40f105a000313960018040c81414000000940615007a200e60510791604545450503440010080c04541160401c000c00381d401030004114082007007600190302c92001030746c41d803442c6071608aa005495080fa8610720100c200311410342150800385000407502815861000c0318401507500ca060800c10b180141e2050020de010034201000520f5030804034140159841d00000c0010084d680340d00d10b290000750040b43d40b00c1016044008940a00701d550248966112400000b03054454018031031032040c0801c47c0810b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 415681232 1250 415679982 415679987
    0xe0604090f030e09130b0a0b061c0605030f0f190302281505070c0206030604090f150c03020a0e1018170601080c01050f07062c060a1119 60
    0x225649510514641c4540c02605000c1c2101514110440c0640d0f007210005042c04c45419040d9499076124100005949440c0c208200500c8161051034100a00300001c1c0b0181e41900d45480402c802d448000c25240d00340018141090413080354210103921009843c88102c038081580d036900c120244001040310308a05080780303400280a899039510486032041902c9030440f00c1c444411074003407440131440c0401125205c0440b40700f207441100086508007003600501c1c14070019078001d500200f01003802c8046448491441056440494507151034880175400e00415001c0d80304d20b18004e050842c10030902c40b030050140c4c40b9001c02035119460300145041028001c943c01a0038010f51262050a40c1d281e007880f010314000b03190205503a2090b0f13400001c41900000d01044c451070103030348240c10002c0f0390f8581c150f035800003e02214020b80307401c9440c584900465000320030020701000c039002e2081c554103443c1000d001034507448011342803418080c2034901d9079003221840340603498000700310034502508 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 415682482 1250 415681232 415681241
    0x30f0f09030605010608090c0a030201050d110903010c0f1404030c050105070203100e0708100e0d03020328090218060f090a0609060311040507021f0218060c0d030b060c06010e0604 79
    0x202403c0ca441d00204409911034006881003800b00201c81d083c1c10b00078104001c61416100c001c0c0022420030200011803030b030380c004603200052201c00c24104142c00000a0950f03000d02034050000b0380120a101d04030307a002d050203400707604110341790b45131a003561039004030200c06d8010a81031140002e20f10b0f0464078100608060070100e80300812603400c4082c1ba098444906200703900b550b00c03c1c09015051010b00348912101c1e04014801401c050078000001c2e406500018941d4401020b465a4020503a8202204803a4280181c0c800a07191030244104015a40f002d01c0500b41689a40300300421501d492031a805508000c80d610b1519544548050001d0403103a0850082e49042c100c000040200800f20f010480708201d9041c4a00e6643d05022aa034102982e119041d01c032002c3c2d40000c601520740d0013460f04440d4401c0c286100003058000c105944d00261040642e9072041500c1500103a2602c20a050339404841d060319101e02c28554079550701040c0108514055410701182d041e9503280d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 415683732 1250 415682482 415682489
    0x8370e0f0d0f020a05060c031e0c03030f010f0b0309340b120901051015030902040c0513090b0105090105160c0602100609110a1107030c12060e0a030f0f09 68
    0x1100030100d141e1400e0181d81c40d94070b00890007914051004121843d0200a595658544400440c1020214030300e03030881c50701e0140c806080c541c0401c8030702c8440100340300562142c83c00c0b040710010740d45001010446580e175588038040d0b5038020310034030000031800310320f95007045040d84810380d0744664072028020907801e1182c06140341c0e861420001e00406c21030003421141d42546070030015540e80e50b00150982c0d1003160302064014402009200c00004502c140c602c0c3c010a181c0080d10080300d5010a0494200006140c045280801c174031603011300f271942020141002c044280044211080060181c0c0200c0c0390341070601c01c0104082884101c0e15401107049a045130000b56490369611003c1d455036a00c950b0031178001c1c144040440c115002e40103e1100c168800700c100d26100d182c6c4021590301c02041c51002c024082c040c0300002180300d0807000c030050b140e1862500d02ca00010726124040f202c5268030710045402080407640880d4006240c64007001c0c560815012407040420210fa5040c010f41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 415684982 1250 415683732 415683739
    0x50a06081009020c0109050c0a05100c14070f0801230a021606090b040201090f060c0818090a020c0c03120433020a020f0d0c0b0a030e0a08370e0f 64
    0x2507003070761307441c05410603110140a0401e4508000d084410700054402501810350064907421844084901c41c1c1c007801e21827800b8601c15104c942c410002c207070a082c3c0f01d80c000116440d0b40700e41403000c03000a02c00c0d10b41825480207044419000d00250803145a0000d02c0404010350110700c1642e1000072405811030158080740c2001444128030b0500900c000644040c1d001a40f2031801081e40c0070b071030000c40f00703032502ca40355514400b8040d0f80d000f0465114200c0302806803100d21a00f042c0d0f40f100141c4034020940300c0b030003603101e50201401628007140031041e140b00f54000701c041f402c441c008008980507109a02d91403003c0f9422031195104d4140050781c1540e1103924008495105540842c0440d2000d100700c0f100d6110f088898100510340c01362040190514288810400081c2d105000418144070107080c003003280e9054101c05810030480503000d4a6110b0001010500d0148030340651403480d035170b03103030404844081e00b48029013001400581c605012815100e0305507582e8040400e042103e004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 415686232 1250 415684982 415684987
    0x23240a020c120406090f030302030306040b130e07180204180e0708030307081506040308030609070233010e10090504060b0607050c0a0602010b0d0605041b0e100f050a0608100902 78
    0x84102d202d2907009103d00c00000d00400004202c00d04c2034802d18085903016801542107460349010480280400a030b056030100039214072010903080c80c0144481c1c1c280e24009840f109207849840090b115401c080300100f144101700038010108459501d41804151207030005d040341e2202c20030f510700101070300020418417000c01002a5240e00a400500c6541d03040d8501c0b0792840680240889130195000003400d070102030000070000c1c201041c02e16030060080c41120b008501c1041a106090180002e5081030f4031407a40080144001e0589640103101100c201a203524010345c20460903011405a0305140382c82c4c002080500c2100d030030200036000e00034111955070b401460800ea503040221880c1c1d001e0710030001c1c0015450700605c54404203160140482c100001c46599450060070300820440702840c034140c100b442518040e0418010349182480ea007494101908940544e000e2544004040200110144903a48442008204582d002d0030044041c0c1c61b4030922841e0000c8541201c070207544003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 415687482 1250 415686232 415686253
    0x6051023210d12150e012c0f13020901120221070b0703050903060109020d0510050f060a02011803020c120a0302120a030f09030819060f0510050f030423240a020c 71
    0x245d1050324101c0340c40341000703841001e8191181602240900c0402580241d042c001080d035800c2008040c0c1c05904a2240d20b01c0351f0721703640014030003c0c017030b007044e40c8451105108008508080003e810000c21900f003000c6061300036008141d81e415580035403405004042400e600b054014410f544001400805540c045d45c0c44241c44030003034000006035684142448041070344482d400100c00c1c140c1da0050015204000c1405c01d00030303d5403015118804540da50a02d41c80c05030595010a0b1881e84280c0c040d003100d031211002c00012910785100030700550800c0400c0070000ba00015a00140341d4234541d0340d5260a41250254001c0440f0380707481051720f080100070f02c10941d12640040c441d0300221711020781c8600c07000c00402113031954000d681a100300a0b5051050b461305080a01c0268005d10b021442d04144110188490300306850449145000001919005600007800d40a1804140c01042102c2c0d00d40c0c00d26600c81c18240b0021001c0d00240003098034440d00c0d40440c0ca80d00040011942030152 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 415688732 1250 415687482 415687499
    0xf060103080a080c1c022b050a150e070f0c080c07060206100609050405060f12010c0f0503070503060d05070f0303110607030605010c06051023210d1215 67
    0x10005040014551000076400401303450a680e04000c004c580a0b2218803c20a814020341c42011822801c0c080c0703281c9111401202e0005180c022940803000c5424104010103105468600400b081c5848200a061081015112030240e2201c42c030301d0201d8070b5401044064500740c41030b85000d0401c3c500000c220b0b00201c1c0003d15030080f00c8007527080310640d031380d000c01c0c18680700c01c103008000c00036800b00c1f800c016510700b41d00642e0300828000c151030040e0600100050b000050b500c5c0b4254140d44880c5401510368024403160310030a62420024954a46280e000340307540f000621b910311804070300b040141400310410202000e030024000240000c1c0c2c4a007405403ca12070b030702141d40ca034400c4000140c20700b03109025550032141306844090703d195903a521030014180040201c506c04051140000c0c142550111014a0049012414041e00007001c01d022950603c0c0981d200c06124a150010401ca00004c80d405640018681490001640100c1034064030880c11040300e00c07030501c4004111440e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 415689982 1250 415688732 415688737
    0x18060a02030712111f060509100317030c0409150b030c0d1a01230910050a02010c08040c090e0f0601240314071b020d260f0304020f030f06010308 64
    0xe00a41c0f48203012852014200c0311100301105440d42038008055030b0440c1a00000d24403081c812100e0041509501c5402081282c0011a0400030a4040c1c1d0010000c0c0001c007103551482d4101c008565165140c050030100c4907200f280f14070b5400710364a9182c0c0c8038000544e04410302510310901d01651303d003001d841882d49a0800c0b01c0c0d81041c149004504c2c803100304c9000c01d51819000684a554001816011600c0f0381c5044000c1007408c4042041a501e40d80d441c03081d0b070710b02d002690f00e510b900d81c810070900a08544c228a00d400c103000000c5c090001080b000001001201c00301a004240b00402d01511400c00d021031003001c84910910380082503e19240c044a1400c450b4200c0c110440407215004405484100900c00380758055000402d50840c4200070440320b449030051000c01310b43d215404540c1c0d00b40144e4040e2074031191458000c40b14035000044404610f180d000a5003004111032a0a42c10311015000920418041603049030780d45052100910680c4c804c0c007601ca0669607428020003d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 415691232 1250 415689982 415689997
    0xc03120a020c070501110604110a03050d0c11030a0f0b06010c02060f0403111009030b25020105010e0a060609050f1807120b010c110d0201120204080313060c0302060c18060a0203 78
    0xf80100364003c10359500c141440749030003070b800740100035589440d1502c400480c100e03240030380c210345038120220124000304600b441f141000c0d500d03010007003410300f02220820f0045045c43d1107904180614008980345404000b86243c2101c0d01c50706644070f4000503a0341c0005880025009100464500316180c1084068030480e4010b031010758070150003208011440044052110100d00d44582c01d01c003196038030400c1ca61250950701310b00c3c0303294070b10581e54143e80a403a2401006070744400060007441d064101940c0c01c50030b410420300059003030410280c0108818018180a03c6151a103034899544417492401c184a11041c01c021174108008010700d00c54000340c47c01d048a08014040707030340394480c02c13085144640181c410b65126016000300240640c100c1000c0e810002116400a81194248024001442c11200840e40c80f4040d0900c40d4075403031241d00050038441c08040c0f17039010a0b0040f03089980060030f80052540c900301e050300d80008103100402240c000c440441d01101d01c0740c00000410a8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 415692482 1250 415691232 415691257
    0x1d061002251e031a040b0103060b040209040504060203060102010b3c280e060913020316120213060609060503040816032a080a0c050309030a0804170705010807050c03120a02 76
    0x81e9504214550300c44d00152802094014924010004204154009040410300030005498906071000040039a802078030140c0b950b07603001051146a60b024491004100c1003a1040c1d12842074805066034012141e54038142845101d10107110640081c0c0e01c0c014040300300a01081c65003003c0c0000e202c08a080c03542c4071350301c01404400410190841065580300f410010810388031a61601000f030696152008101c2c5c02d0300c940080300c00741009100720030003c1c00c00d524403403d60002900401c10b410a01885071a6810f140400c2401025804a504030998125003007443c0d0b21746451030075096070701c83c044c07001c1c0c60b0707807118192501011750010090400c07060400c1c10001c814041400240e0403156008000c1c05607400b008150202e60162040c0c002403030040742600e04140c0c00c403001c03d0404210240803a02e4540000707051001c982e806c40b4004803404210000c102c01070406001801c2c1c0706004d013058051000101d001e03441034500708102c5488080035030766401030341040004400650030074040d07000d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 415693732 1250 415692482 415692503
    0xd110f0408100b0328140c04060605120a091707060203010e07050a0c02040c0905060f0c010c050a17040222060602070915050f0303040e011d061002251e03 68
    0x10010b00d03500a500b610480180a0004020704d040c804040003070301c080c002000031342403010700d01052040c0d10b010014072125024040c60010082003100301c2d801a0825000e00100344411120050f9241c4610307400003040100090003055070500603141d007203901c030314040540001000c0003003280369000345048901c0c166419501d40c4a400041c2d84074052868208005450350842c80d0242ca01034110365015031940c109424299120400704034076900400d07150450400004100760840000d2040a0500003145412401d1140c03803413000306406138000c0c070070b101003c101021a05642e510180c01e800f500125512101070005241081e010b0106440781c0340150080210001d2812418054a44103a042c1100e11420314104400c20085002d032120040c0c2500c800e20011406110382c0381c43d0341c0600144548200014103400d0329610b000ea005062a000310715841001c0c02903038000030002c040c10b0030036001811502960002440840b16648034000040d10410010001c0001d1141d007800c0d00c0c09203d401c02e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 415694982 1250 415693732 415693753
    0x2100207060215131b0906030f150207080714030f0301030501050f0a230910020a0914040b010e1233091c200102030f1602070612020d110f0408 63
    0x4110440c202d92515150844e100b94100054101010300b2140c0000c2d0803a43d080c589a1400c04101d4010350400c491355544124103005100c003008010190a10350702044d0700d040201d03541d400351401003050080500156152101070f084060095504451981c2c0c401d603129a540d041c00c2e4042e0800751611032441620201003945100036000d074205440c07030344040044428040e8070709100313500014060f111074012260061034a50182c001080b03c00e980303580b030441050500f0001a100c0e0042e00c0007030301c00c900c0c000003074200341d03080409104a16422140346c030f551203400400c54100840303400b401c00c0c1810f501c3c3e207040081454a084a0300c82c808a54035000542c5c500c0d014554440b110340c2d00000d210449500c800321207114007403038903d03400328291504041030003070703401350aa82060302c1c0203a100b5a031804004000c0074850184400011078070041094520f8104040c088100d1030102404040e000591100c800c100e0750003020140304002c40050744d030050b0040c590266001406091014083c41e074851 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 415696232 1250 415694982 415695013
    0x3230406031b020712030c0b070e09010801021e030a09050109080a020c010206010f17030f03010f45020f0c0c04050609010f050409030e06070c15031107020d0f021002070602 76
    0x80c1c0d02c0348a00d800a003207041c01d18040c41d0750150b001d0400c504010a900c54400020601d800b1107002e4403240e00d1b5a2015078a05080000c6640145c1000907940e01c180080d4952240411842c0343e1241c2154100d680c036216038001a025050680002e0702c1c0b9030800c02c1c410104140b080091500514a034281e80c007007882d0000481e100c410a1052202d0500450310038010503010701c0c5101c80314080401207900e40554031b00110b249404c00d030721070012400114010444503030b05008041c0365088010518106020007a803052094001010920006a480342d84062120742c03075048410510300c0003561030315107000100e4642d64840560400f030250742000007040c41424421012130607503c07645e24404035941401c00f80002003c000e00160100001000d03441d1441d180e5400070318202e4020030b400500a414000b042000740b4041811604261078944140f032402c180e10f090f05c0015504484001c0c42c0718450070716810070504010061f5010440303070340700255250005550012204640c003920340300ca02d00c4080c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 415697482 1250 415696232 415696271
    0x507142b020a1107171209011b0302010b030705040e10090510060b041802030403020d030e0309280f050105071103070b030f0a0b092202041103090a0b0c0403050a0f0323040603 77
    0x8a9198000304203246408403200140121f00e506140000c4030380c040404507403601502e0141640941d64600b05c10509050505c0f05001030a020785042c402903501d0302c50f0aa4031040c401034112040ea403614008100315081c4240324094400100500c004d43d150321052866a206209490f00c00075260020058070855009403841160141c02404602401c02801d402600c80c810130103c80340010840203203d0b658803c5004615100d00103103e6111841d46032071000108183c012031010354415100b048a40c1c0d2003011a0b0304217902607000c01c4510605400701e403401c1259041094030f282e0100401c4020350f9031500152040c1448482404001408418030a40c400b0965420401000018461030010400224522030074406800000c1e07640322004414a55001070b198182e2903001180142c0506c005900d4a54000c82d0042c0083d141c1403851303031515501d0703e01c60002000701219102c907500341402081c0481d10f01041c05c060400e8011080c069950341e03031090040b440804e1908914400100c5401c00c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 415698732 1250 415697482 415697519
    0x1006140306011703091903050d050c011d07061b060c020105060310110405010e1c08031e0606040614040e090715080f0613060504090501050601030507142b020a1107 72
    0x144d4641132810741400380e010120745038007103500114000000003e000f000304110000090740d070143c442405034605429612403102c0d00c00c11396008803640000090124000d000c64495007848402000e600320b0340340311040140405080c10b407410742041b40317064041d04014451b150407000d55014154088110044480503c1d0541c0c4142c4248007d0001e94001e50072a040d0744402045044c03d1022001240c000f070558100807504444084184407264403103041004242d500c0440810452900c03c1c080f4100b03005502c2007000308000e00c400b0100c00b00a1108039009440400c400d08000d00d410100c03583c0d90503151141c120078010700c5010000041c131a001803070160440e010143c486860f50020098015952000d25414903034a04000460341e60718442c00750302c14440c0c0c001081d580b50520014044400090286052004e0328000300400c02d401c1044403407040441900d00200280240480c26041241c1c0d491290307948005621500d07141c001c602c1080412070b1104540f48c03140c5031101070081480480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 415699982 1250 415698732 415698779
    0x706021606030c05160501090b15031f06030b0106090302090f060108070e01110106120c0f03051c0e060a0324050a0b03091005010f0305010b101b05100614030601 71
    0x9030502101c0e20a8100079084901850440d080000c041c4000007142d4242e0000c0b41c290b955402c7c00404c01c12500010355000d4040003044175100d00130303c0480d0702d0710030903010554a0480080c0c0b07641c81d101c5a5004401941d040b8111442c19038490b030740600503084901040c0d100d132010400080aa84285000911861044c0d61705480c503181c000e01940c03000c40048609041c08691015401c000809100300d500800200810080401e01802c0120000080d40c0040c0c55101c4100014000314000140403400241c9541e00544d008500300000c1301c401840600c2c0d00c2c0d1009001070341d50002c9515402402d00048000080c0c0142a038070b003c02038001e01d1a104140d0002030340c0a0802c10000030170040e41d4041e00b401d0035030703810810ba40d090b1400c82d01c0c241c00010b8038203a601c2060040c003600348140400c2c803100707840d56400d41e05544c001805161099588580e000f0316103481104012061001c2e41e2020014117050000c16114080284011200e65400340248200e2000161400c01c15880784071040040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 415701232 1250 415699982 415700023
    0x9050f0112110312030703020a0912020102070b03151309020f0f0102100c02010f0c020304150804030815040212090102031806010308030c0a090f0b070308010626060f21070602 77
    0x656803442c400c807501003a40c2e458012054a24a448009001180b140d401d95500581c0c4a800c0361019040700c00d203400c02040c10721340c50304080050b41c00080f40c02c01d4032031003018151650b030303040c00a10a500c43c032945c841e0001c03000740410300e044140b500840584c070300c22501d4100da1050402440207480e5002400c1c0e0040c1e10200c0f0285481c0b00c503506c0400b01c80440d100210b504c0000c03810480644200264510044c1d00014040011903a180804414600700b0300d41000075045c9514000c012140c05031207428800034091815103d5030381c03541240e07a514895000440310b031902d0a103040c004e400031540d1f02d000752500c00d01d104042002080701d50503250720080650541e11411502c500b15005540c580040c004800c03804550094040c10a4008008607800c05680345010300e8000e01c00041a0311200030700007103d0b03500d03440d0310940500703050301542610303494020350381c07a400241da8501c1c1205d0560045801c07818030b0002c582280d40c0c8000c9000c41c50448000b6940d50350202ea594074410f540c0309500f00342 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 415702482 1250 415701232 415701269
    0x31606050f15040e07030507080d030c090806060f0a18051b0903060a0b0406030b0907030c060e1003050a060911070b0609091b030a0611090f1207031112150109050f01 73
    0x4e500840c00080d511003161a425126500c062500c020380e08032020a074050311100350110b0f0f00d070150144a110501c0d1030340c401f529017100c0d55a1814003502ca1442280250100c2c155501c84000460061504428010610401402c406d0051005131408000c0341d1246081403c0c982068080703868100340600100031a41c0c3d07402503440100822290580d000d13480e03000010114401e1081d49000f289580040d101300c40c1f071840e118110b80020341c040c00520880440c1000d4650740c3e0b201c0040030444070706001c41e2903511018110010881d6403c102c240038501100550f00c042c0c45005002c0e8203214122426403516060200400074130101d80300d6a10754400b030840c1014240080802e40340f110080e040f1400340704643d44d01410350302c01045181e01c4260200b0800c00d05d01d8500035090704207801380c8442c042d88c1590007510b611100300c0d00014000383c8100042d4111602c03a05030042e101c2c0c03566400da07600d08c00c42074034500140e83d0030b1003540c00d890308103c00b15000c03a1010304080e0499140701c110001e020031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 415703732 1250 415702482 415702489
    0x10510030b100e04081206010c020d0609210309110604050913210e01030b0d1203020f07060204090203040c0905091906150311010f08160818031606050f15 68
    0x24034240218104800c00a00b1001d4283c08034020780c8124a45c94444010b00c140002c8400000c01031410803814609a030007580ba140704070b50942d85c20404c0410325850074201501d000051204525441c080e450b182d1000b07650650000303c07202c1c403130100e00000b640720004001e401e000328007807540d01619120124540711200701030403c0c3d0600c202002da641c807002c3c0b00544002c0e111600000080748240602c80300560f458800d00b82d00302411500c0320134445d80ba80700c2d04105102c0480300028154009800099400c2401c00c1e501300950014055545039242e0810b0000303500165400c9a05000700100814001814003550b031203646030070018413a265020310f11a2030004041c000b0394890b503070f0f10400040e285c42550b41c840994050103e100d40908801d0004040c00c81c402c00c1c91303042200500034400031002c5c80c0c82c1d4040ca01607074034140070991160440301c0643c0c400d41418690341e200014112544510f04102d2003942401404200040e55070820303020000c59045860210450b140001041c1ca442d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 415704982 1250 415703732 415703753
    0x3120c0706030b131d0a06060e0c0313030e0a0b030a0903021513080d020403080d0605011202181011030304050607030b0109060210050a0204180911040b1f0c1208160201051003 77
    0xc01107488080410150100d170303030403c6400380054a0184c1c485805100095414050a41081406c1034035899441c000c3c8164a5145810100074100000810318501580c0c0303003911040905840f00d0030640c0c83c18803c0220000b0000c04c00c0c1240940204103a19000031101e00c0c185200300c0c14800ba00301c5c40c1005540743c8001c1d9110060b440015a4284000700119042d2800780c159196070741c0c000100c3c50f04100014082c440782e06020740003a401008413549586c07128000100c00e080640b00710801d04040c1c50b0070ba400440341c2421002c41d20000c010042800310005086021740404c2d201001401c009800440341900e15008203c0968441d042c445c3c0d00742c200c0d074030070755000300785610050420f070710385280c042102e0f0104078045866803211080c00600c1144190400401c100b150304000c100040f40100720f1041e0701004140400f1100d180401c1c040d4090076a8207421070f4400700c0c14400c45016840901046000da440910703420306048100c0c4864014407038103000742c40e900010001546190327209003103607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 415706232 1250 415704982 415705001
    0x150806071112030403050a080c0f0909060a030203010207030203030a0c02060c1228020903060c0909010e09160f03050c1009091805070905071707141803120c0706030b13 74
    0x10b01c20b03460b11844514141d0040c6000d1446596159644e9450b00c00003003908101900c07c0352290010040c442d859101181164038100e41910140c2e01c555400002074988070349640003035010350000880c1810160f0210007107204418022040002a403c284226522102194080f18034481001005141d03818450341c1e40d030010411241d0060f0410042e0825101520318000c0704d40f0580205410791701d4079003804030343e900c030b4628041d0500306003000c2c001a00401041c4034115018540c3c00c0894070740c1c00700b402081e11281c4e01444144405548580341e507a40c1c10240b1042c2c900780900044841d0a180c10070110000c19420703650000103070300f003841180091504d88411994160030a0f0000c00248060258600900d400c070b00004040c40e003a000034148012803004940c1d02024402040701482c1c00c10308030b40344025094001c0303407100419018042450884049146e041c45554102407078808898010603a20843c0740035240030580e01d0a041e400d039510441c007281d00100801203101c10004030792000c1202d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 415707482 1250 415706232 415706267
    0x7030c020d4407020609040509032206141201031709030708030901030506011e0311042103030c0507050a120201020f22050109030f03080c0405060c0a0615080607 71
    0x21008080c00180801c148954040707101c00d01d4001c40c00d00c480700b00c1295203504000710149192100784d83c006040c921650407168460b40d075034008940c41420410554148805800e03035050360555520084003103040d40d12511000030300545640034800711403000e544101c01100a0b02c86164216500d441120190031034181211005011021007030f03508001800052198201643c0d0b50064040010300f9120003c0c111410b00c8038039603a0720444440004040441401e034980000d4481902c001011144520707401482090062000c0303182803c0c2c0c030125000842d10a48040003145101c4105691030f0088001c05412900014295001b146000703480254040725031000625000e008460314003603400c042810501d03c040d506420482c5500004120090705090815194040c0b41d540c5441414060450040c1002417140100d44c401c090142a107000c1d00c80200080d4644000d500010b6480c0707a80c4209441c1682070450000c0c9126180c1d18407015141c0b0f68010700b40f281e980303910585582d00c4038212180c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 415708732 1250 415707482 415707503
    0x1090b0f1201021c0509010515031b01090302040c18060e060405011101230714070804090f0e07120c09112203050d0503061206090c0d02040902060d14010b07030c020d 73
    0x1c038180b11005031345040700e4454000070942820410705007150710040540007450124889842d02d07660001c2d180202101c0c1c2108a941c6000d643c0040380c082c00a5070000b50814108034914103600d400c0081700d50141c4101200180c0542d075204102c0303000c0208090150442030803c0180240e510403040b00000103d0000003042050f039807000c0d0039020322400c813203402a50a100500110303d82c0b2060450403515215141400e00070369881d0110584540e20841056507601e02c00e4590602c0c840d0403078807070361304e00c002660841903991494441080c3c40f8141220000864032000c030700510240305041503040d50b600c080b4101003038003400300c4922240030410000712950721400000560108544003104c61182e4030b0503224103103001032207102d420ba20254070380b507003000c0100319503423a0000700020800c0341100c0d0254400c020f800404d004100f584000b039004080043c460f000b0440b00c3c0c211405415050b500314007680e9917021419924082c0540c000e00081040d05000c1c09490140f54200c0b1060141386c0301e80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 415709982 1250 415708732 415708747
    0x3081e0402061602011b1b0b0c1e0f060906012d030308060607050703081206040c082215020415050a0c030c020609040203150f010e010c06021b0601030f020901090b0f120102 76
    0x240d101a0301a00705d03516045010203a00300707886c1f18030910083c1a00c00c8602c3c20300c100c0b03446641c1ca400c81601030120307000044110003111142042501143d403488406d9514900f070403400c182d1907842c01d0040310200c5540000100031504085040e5812421500c00d03504290b003035640440d040840504101d50121061006601051702848080b00031071140071069519902a1008995100b0003490326104500d0942c6c0d03a00904d4006070351030b0740082620355070a40307110303a0201e80c01c00480703040000d405121011034003038044099500400035100c42c0c6c0820004000c08147c00c5500f0322815189400107000c810140c070003c0e00461800c11011301c02811a41045914404079080742c04c100c0b1500400414200d080103e8200031a800982c180c0070310f419000b003045a00041c142e618441c0e40201100d90020300928494540c1010641400440040c2c4156584d2824042d03495410304200340c1c45800304d0400015035141510604030340f440d025100700341c0807034510300b00b041c02410f041c11f01e05a075408110303c030f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 415711232 1250 415709982 415710017
    0x170a03050f0c0327040b040905030d09050f1e0c10051804020702040515040e06090304060c02030c09040302210418021315030603210c02120a02060703081e040206160201 74
    0x603185102c803904044071310b90b140100300568419140340ca000c1d91400785003c001c01c030301200303c582030103001401050050381c40c500f0713625007080c100f0302e0841401000d040102ca802c3d80b081c031510384644c4c01e0459144107103040030811030038960700d414404144100b007400f4040143e8401c1d89c0700c2c0740c03000b440142060065000301e804d0340d03c111fa504a400d0f0020f450b425030b034a040d2281001002c039250040105180c440318140e0359202c0d40c0114014410000f00080c1195010000701c0f00c000c030f01070001341c050304161074040e540709a03500294080e02d01701c000c050040e9111900780c4044941c0380c681c0481207000315041074000d601c4a5080b60300e00c855008081a2402c01e007658121071807950781c0c001002b41c078609200d810784145d0030030f1001d41c4401c1e5000da1200d9a108400800c1c0540403100b940c0710703101d20604a031174038001140007500244081005002c0c142c20116a42c82007000f00741e1401908004070001201c440c0883c1c0095221006015030101c164201040c846100d106040200d94101d12009a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 415712482 1250 415711232 415711267
    0x1204290304081207090e01091e090b06033702030a05011d0f01050c030103140f0d0c11030a020306040b190608030414010c080301090f0222170a03050f0c03 68
    0x20b071250340000450100070a44115900e52101103460310803021400c00035610040c20061040181030341e15480995482c80380a20303038010328072a9030020031001c00c691920300c4500d2011220350303200f405210050021031600c286020700b50a260b40c402c01c0301d0b4a904184280c404620742059800d845407203000340c00102d0910a40d07103030b11410243e160381d461180c0307402440c0480034151000f66905010074842d00046840940c0d055030360000d04030f10070804440702c45180520041030201d0070310481c1400441070345c01c02c0020400c58040c40544400b40800c005042d6075071500390001b174040c1d01002c006030100c0c004014540d0800000c046400542c01c0d039021b141c0a640440d000742e43c150301300080410000400090042c1d00c1c480070309040048000b07940307070144103000510031840c1c041d40b1501c500d40322521a50403629403480b80309005405401001840314074400c580510941c603000440030188201c0009200128190316a42d00f41c6048101003281c8401e4000c40e0400d07003944421b00c403560202d00300070b01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 415713732 1250 415712482 415712491
    0x9130b0319050c0d0c170114040c09050f04050606040905190506010807140d14070b040b1c052202031e2506090504150905010b04060801050312042903 66
    0x401d440840380c1c905201d424400c8480e48580300d9002001c1103400500080100c000b00d4901641c1c61400300c0c80301c6007240c090301c590300c8552044180441000b00300203003501100141d5030341d001d0400441da2403904c103c2611406640107030095100100040303171443c103038100c0a4468454000d4489401c21644a03084083c407010301140c2540043d030040c00780110800905005203030940c40b41860000c0300e00400c242d003241002c090962403000d1a0481800070800c9407000400d103001c03920381c0e15031391001c030100340c0d82240c2c0f6401c4441000e8880c164007100c482c00341a0181c21404800c2c141750f044000303800001410008120f030903001e4041040307003c0e01e80f21a00c1080d5284035001e009119908119910350810009681591802c600000c2c44135603403000c3e20b21b050f50415100060006820320412501c031299500c00031455042c14008201600c6110140c0211000b684815130305980702d03410507481e25003014014600050500c000c205d01c18075900e40220a6500701072600000f5500d000091190744101e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 415714982 1250 415713732 415713763
    0x309050d090306050901060e040f17040b030103020f030d021207060b06030a02130608040c0510020c12010605040e061306021303060c030c110c090a0b03010b1f020106061409130b03 79
    0x70700c1081484214010540c0c8104180001c204180c141600c444c01104007a101528541030019200100301030641c0305400d083c21489603e03211955510315250f03c0d4000d010403400b40d03580240c1c01185081c0041c10107002c0d901074000d01502041341c000b0b07803500d4000c170704181c840d10f0304d44040200d1074072244019030060076000e40242e610400745088600c0c0d42003a40c09a01040320020030003011408102041c0143c89044a04042582c08200203d240109041005500010303900c04070b0310901c41541b00d10112902503400740030201d2100502078560000326600b80c0b4085150900d00001100c56005007a070015017083c0100c0c494890701e4010858031000003400c0070903540d241940110342c000d41d02c00c003a03141d546c0045c030104c1070040100b007618801a04110440791210014045541d003900034034444480541154401e5821368038407140390642e41c1034100594609000483d606110300d0000d482994070000c940c3c41d01082d0410b2200000700703c800c0c52030307050703480d107a0503000d82d401e01c00118202e000d02c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 415716232 1250 415714982 415714997
    0x3120d09030305090f060105092d090601090614060d200c1b0325080307060f0e01020a211409030306041b090e0408040308030708100b18040c0309050d 66
    0x510300a000c86201910201c03951784401c104411004000070501e043d03034000e4482000d103817258600d401c1c1e00b80c0c01d00c00d20380012002c1512804607022151025114a0300d010803180c032a43d9819541c401c851190094000c841d0100780301c6c07551414200b004101544002e0000540c094803c0780860070b80480400c040d015007000070f682290b002c6c040041426810784a00000d410f8054200040d90360b000034040d0042844030f20b13503005204440c038540840100482c078240c3e661074190389000170040603c2141e8a8a4520708400c0711038070f0340b0501c01d070b801c283c940da00c90300b10f049071072241d00d400c4032000c0f8140d020240c1c551090050032509401312030300a1482c04001e40e142d041500821040d84c641c050700081c0218038000b40d03034603aa07201411034101c0e110091481d0560301c841c01d04014903c1a6007014000d86800010f20030a660700c068090311403100c1c005401d040d142c898400c10224400c0d014003a10b074018101c40c00c0e146207030960045081d0303111030400040e4520b81d0754445042c01d40d0403000402140b02d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 415717482 1250 415716232 415716251
    0x90f120c080d0c0c081203340e010201060807060905060c03040810020703030e1f020a0c0204090c030512040302060a030c1101240501030e070b1b10410603120d 70
    0x3c0c4801c000c0c0040201800d40035a14424005040c00018907080340858036003450500c061011182e4407942d88d1500300c2103900701840801a029115051119005600c1e114000450b06008281c9600b170324016500e200410f8601030400601d80c0280005c80e80c2c6000400000900c0b60040040c1045070300c00c00b10240c2c40c1d00032400c01404492107920502890380000e0021802214202c1c074210038440050310050315984951070032100411000e0000350811706c1d0060b9030f070900c1001d205c1d21003164400c2d400c45440d101180155215170045200080d080704041c419104150300036004104a130301180350080c44400b1810341c0303d0a540c03860750603160580e4118020164490b5030000000500b000303013403d2000b185955505076540c50743e4441c441c1c5111000c280e80c2d00c0d8040c212801d002601166044402520101d480b00000741030f01400c004041d000314a1712199200590b0640c0e810302e0460083c0b119810011900d840000001400c56030f05000d013210b414401043c02d40500516581e010000900000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 415718732 1250 415717482 415717493
    0x5071d311b140a082205060f090d02030705030f3007030e01060506090409020102010b130509060112350c03090f0a1802070c0302040504030c05010c090f120c080d0c 72
    0x140d00800402c402e4200001d24401d60092002d07500030404400c01c040200100c0103042812100c010700420300c1c01180280031500c03511000140c040d1407800c1c1920081090004140d07502d1141100060541d0424400c0200034050176010308101176403081d0000d080d00c01c0ca25020282040c00e010340c01605410400d02c0300e0294144100b0500c0b8010000801401d8140340010320240104c0c0d00882c030913601d80030180c1c03c40e4402c0d00303c03801c01d10b4050904000c00c05c007101840b01602d01218031507030394400d0000006155100c508100c0c20503400100c80d80075501007403a03990b029090802090030381a40b00d0044202c044004005000c2152080c4c0070710b4581c0c98400400c15242c0c440b1040c20712075200c214003071294402598004c0c2c0f5000c0c80c0303040107a45580d00d00c1d0000411200e9800a54003d180c80c040105050f0030080c00864a40321b00001c02c00312000d80300a481c000c0181c020400d207002d241406000d4074141074a10200603002d244044d0407a07907501d000500d01070603411103500203460b41c1030f030004001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 415719982 1250 415718732 415718747
    0x715030e0d0305100306021c090804150e090105040e070803030c040501021b0901060f1e1d0409230a0503030a06060f0c0b0705031f080105071d311b 65
    0x2040b49000e024a042410380c4a6603101c103404050071540e40042e200d001c103004100c140c056500d800d0b5090241d00381c80e0170070360641d4000c1c1c0700d203030700e4146000b0020084d180b08800c5c001914000900d1000181d0815007800b000784219082003459200d0341c800459402c83c100043c2d84140d100203071081d40c0b5403c0400090400d07110040c02c2c900c0c421541c09800c42580d4031028103055900d54074211030141c14417001100ea4043c90000400c3c505900f810101070203510402210794a1100c0d011229181098024441140c421042c0906103d48602016045014000d070038824041094104c41c0d240b110703a03c4d01c5007580c0c801c4c1e4202101d130750f803003000b00300d02600041c65030000841c41c1031249071034403d0385030710f410240f00030040010800004005007007603181080540105a515604032052501c9407030354ad00818081d1004400702d4050a081107281d00c9000c03d00d0440301024024511880020000c542c18800c003d864682e502841c80c0840c00180c0913102d600180c96002c4030140b0020300c000006844c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 415721232 1250 415719982 415720003
    0x31819140f09060d0f0f08070309091d0a08130506030c0c1908090d03050c1c08131718090901091b060f11031b0102041401020703050706030b030715030e 67
    0x4902c500204480d941e11a220b00d070606800ca5075100d1011300c945441c044080c00c03244020581d0101090540034168426000410350705250070401c451b4500c24822007401000800d0f104055000448075400243c00002600710420042d40e03c2c034400b03441d10001003d680007100c2d10140c1410111311009000070401030307850f0905404c07408644141040c1c84201041c42040140ea02641500e0281810144220110341188042c08243e03403002810f080800d131140341c040103020015403400f01140f1041c007111181c89103213a11100c0075100384039416338103030107400500f4082d244420062004140e84c580c0f14280784500407500000690150b603141c038100e0128404001204400d040b0404c2c002e0a40080c4110320381c8101c0c0c1004c01070b0402e07a030801031441c8240c2c07154182000391000008400d19054000c0c10a50b22031800b00c0c603514040c0c2004903507800851201401c19400301104000440c001d501403003003440b01a081d200b1194461100d2030341d50007042c1801d4002603481d00718144080e014040181c56 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 415722482 1250 415721232 415721239
    0x309020a0b030601050708031312080a0b03161e12050d02060f06060708071403041203121a0d03020a0b0c030411041a0f041b0903020a08030c031819140f 67
    0x118200f03000020014005c041e07004100e40c0c400400714464144054820036000d6001c00c02040c028020300d8001c104440540384042c204d424450498000e2601240d00d0756a124402c2d80340e50260300d03100007001c6032280088080000341118001181c80e141c051079604d80140120300521003446200002450301d01e000701098401000403060092a036101c5045a00254000d003200d40c64401c44d00b024808000c21400c0c071006440f0010700014038406081d6440580c2e8001d0301c91401c40c01540001c0d0041c2e910040441c091034440326584519894442c407440025070084c4101c0c0c10071505035a58911082040c3c40e6403900c0039000c010002048840100a01142c0c01035a00344040110030114284d4414441049442040d502c98181c806860795407288280c81243c555124004c00303003601c0640000c0640c003003070340a5920344002151040d40041280d04000e0400011032522081d0f0841e40d0000b4000440d00368001d40044502508004000c507145c041c0245604047c00c2c0180c44080200071031080041d00d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 415723732 1250 415722482 415722487
    0xe0106180306050c09040e070501031811040504080d0203071e020c0a0b0d1e02041502060f06190b0d060f090603030206130206090a030b0a050a090f030c061107030309020a0b 76
    0x248a41651494400c8941c454000f0500340c0b140a200d40301d9005480030242c116280c04604a040d1200041100c201c0b94203880402c041040065900d465801c1c00720081c00c5030840c24007402c41400d255010750f50090007113601c24101050b800f240400e99100765050b2000584004060b0303400e0001443d940c1140c0690b000914240c825600410080b4405104200c2e11030b80c0460744035144502d5410682c4003400324043c0145180060400c84000c1d0020b0180c2510406d0034841408541e000095190040c80e20850692195440004212903030140d0f0640321121400100700103058038001026020f541210701001c40c00e542001d200d04901903075580300c06003582c10b010003040440d80205c1c0c070715009100c003441c2000c200d51900124609102e4022169040084002e0000c14442c0c8031800c64000e03a100301060119031142c5001c442a503103045c2002d0041780c9904250f800003070080b40e94140c0f0741e100c0d030004214800c103007a144841c1d40042000703402113900d646000d8218940440e041e0042c003400700c0d14070f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 415724982 1250 415723732 415723757
    0x304080a0f030201050f33030708030705070e060603040f1a0f06090a020f0406080c2506060915060c052e060807080d0f11070314150606030601030b0a1508010e0106 72
    0x12002c0f00440c81041c0d141f03803031800d2407030305501d00e021000044c40140c1201e1800e40c8d10f10f0000c0e5a42e1080e6416a598040d04201040152a00310140d002d07000040c4014159100c1d600c42c0d0b0000a41000206e50645040c10400c280030f49003951144259820040302700c03246441424006554402000d402d1194410840d1045880490042c1c9041d9001450881c0c107030758401c81030207a00c0c070804800100300c0022444a240303d8440803540c1c0b6105120306014000c01d0b648290702000d40300d41c09902c1c40310505d940414050b1030310031400d00101c107006108450150101c200c080ea003842c51282c0d05002000c3d52444075104d1385441c06180024002140103001d650316007142d164030f0340f4011411004100c1d5944000da030262154000c0683c3c1c64005007655025550b07407402c0c10010381d10f0200d2082600580d6240103640f844c2c41c00b0309200e2a80904a10b03d160345000044000b00078041e41c40b640800300c0070b004141c80701d12605012250380300d511181c10f81c1d4100200a4400c010591050007080241c15914 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 415726232 1250 415724982 415725001
    0x9060a0504051c091706071d010c02060f1c020c0111040e2d0c040302040b01030203060127030605130c050306090304090f0608030a0f0311042301020304080a0f030201050f 75
    0x1500d1000b40f80c000728902007407003040310418155070001c08602c40c1d16200b00014040480c000b03005003600d03183c805030341c1d0310f032401204800980050240031a205e5031010000d8240300c001454032606440312a4603128905601d22a00307204503c818001542c0480c86000e0000300f480303908800308000480030708051400440f144004001403c00c80c00e05181d10710301b5042c0171054004084030003140c00300401752501120703556113904944000c1c2d11071400c10388520b5003940a84200d9020b4070341a0b5901640c80000658014407141c4241452403400580ca400400701703589200b03e074060b010300c968101580b8070300d0800f0b03401c9a81c25004035119400c010203000768000000100c1e02210140071010035441100d00d240e01c018861940302c030003130b070000190001d0000d92280343c41b0804406614204040c6681a01564860140780034204050f600d03070025180e034401d040015005a141441100c0ca09600c1d0401d807410210b000c1012034401f582c9601032802c260f0203004442d80705103401000c185505d045c0128 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 415727482 1250 415726232 415726243
    0x1e050a0b090105040c020a021003050402090c0a080609040507080a26090303040635180705030d120906110304050c0301050c1b01093504080a140c1809060a050405 71
    0x1010710555030781302000003d900034001f1000e180c1d00105142035400f240d400c09405042d040340c040703200307025550018445280e1001503804030038055882882598421041c40122000a001076a1034442c400d000141a2000c0104028061260881c11080c13031030140700c8403000b03282008000c0d4801d8148210001d540f000000d032011100c1a282c10b151614206080d00c641060342d071101d00301d968218040750382c180f0f500d44405000300106101030740d1514030192065155603060113210780c190084e02c000888584100003c80441e01e21070781c0050034015540d00d8100311480726000d41c8a00102001304030500800f4003c4c1ca03003408044c0c000b40701c03e2a00c2503000703025201d0328200000c0004005003605c60150251700001c80c20f90722455448070407600b0340e1b1201d4080071040680215022884404617204444005e580031100101300070082400107a0b1555604411903210720050300c55261480300c0c541d01c07901f1000302142c081300c0001040c2862000d8500b0103000030011b0f83c406007071005120000340e00240 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 415728732 1250 415727482 415727489
    0xa1202010c08040803070602040311011d01140c01020a031e050f13230c0a1409010b0f0c1f0605040b0f040b010e121e0a050703170d1e050a0b0901 64
    0xc0100414070640380014250046420400a6100c081075174402c0100c254014029603010b40a0040014030000c0119890011856440501446403240505950003500d410a0344111422040c0c2001e2803032488030300320303006802044002a150741c00551158001e25a0001086c2c40040a01c40c82c038007069500c09040014111b001c200240195000c14000f0030903c500d40d007082040101910701088202a680705a0700071824030528550f40001658810003901400d42c0c0c4d03000d0000c3e0a070380e103042200d5026070000a100d4840d44070801a4800c854814040d07901101c8052004045070740c0d03101c20400494076030350411802640b074600c40c40d07400c0c1d44042142c040c201e412a80800c50b9102280121005800010100d800c54800d2800903c0c5503c0881c0c0320703001c0f01c00301451040d5000f80c280200d9840c1c60944018125800c0340c002070002c02c1c0300c2e550358402034201c050017524211940c0058022102c0c40711a01000c1c10103510900f22045c0103010345a007207588904140110210400000c4021a0610 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 415729982 1250 415728732 415728737
    0xb060909060f190e01061e080a0807061b0c030201140112170c0109080903010f05010b12040c050d120215090d12180b0f0f040f14070b03090114060a120201 68
    0x82c03030200c41203e018022030f4a00d007081c4000c0d00a054042c0c041e100354002c007050007107102e2040c101c468001c2c89840032946a640202014007258558507041da0000200f516100c0d10b50744040c40e10420f00c0e4120480381300036600c64002d80c1c035506009084446d00c06404168400c00801002640741c68011a546150050420110381e100c0001c506802d00c98020106c0d21035007000023900501132028080d181d0064190000d000011500c00314004642e824090b000c106241402185c60f403a072003810441e80984101c240003216a1150005000c042d01c402d01101d200c0012541c8002c0c4582c1484201c0c210001e8062140d40f07410310140c2107883d0444000d5600802482c0f09a0185490075600060300803902c1c0c0290803001007081c1001c00c1e40480484007500c90100c1c00b00401e802a031008089441180c00441c0865441d105544094252440c0134a8104500c5000e8003c42c0c2e0030b00400043d801508803030000101030300716600b402c040c80d034020000ca00c03500e030f0340d14200510104001407030001503091 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 415731232 1250 415729982 415730011
    0x1c0905101209140309010e0609060327120913060612021c0504050a0203150403140702031509030d0c0504181d07081b19030201050d0f0203040f0b06090906 68
    0x85035030000800781040050b02e4400702d040303c031241e11808001054591004c0c1c0e0340c1400d90040c2d405000b0f040c40386414558126a0800c0021403a480c0c1740b584021241e00b03d0400c14481c48410b04091901000e0340c0001e0000300e000803170f425a440d040c08960803101810100780016850300700003403d02c82002071441481c0e900010444103041b21100c900607408540081044181002e0034160b54462104400b03e00a11036035603480c0f00540800102c1d480359a152391848503c0700080d24050040c1c00c541c9003280c1511a5110100110b241c1c174076000c0c8212600002540c0340c60700c000e038480c107840100c503024003404010041440001d82d410100810f000501c00040759072081d00300358070007590010300381206a019656000c00d9201d00450442038280e401154200c10885240400c003c2c03122092480241004d0300070200010750181002e04807c440d070a1001407030b4049280040d0a0703a10840e812900c004c0f15591000821010068940d000101038442e0000341c03910200890740c603400a40f001510306400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 415732482 1250 415731232 415731257
    0x80a05070501030b1809030417030f0a0c02011209060b090a1a0427050102120609061008090304230307060c020307092d020c12090d0201030522051c090510 68
    0x6000121512485c40035007517400d0b00e000754086480786c125006290606038402d00c2c3c408400000015070360b0b0490b81d88071a5240c11403560042e551030441c3c0030120b05011036aa14031804070001e03c29250350760b008480c04030f05501404104040d40c40c0c001d0401c000140f03400700000e44034904000640c40e1000585001650182d40300c1d0400988a0a007080a01c01140c1071b02c200070040190083d0091151803181200e607506c602d400c200500b20b084a1080d00007042c042d00300d03580c62040007490f420002c0c0e0425a0710740b9464440030400e807201c54000785400303490754040c009281401c1188100070280fa180003920311605900094a440c11489003e6509858864180200410030005240f0550680c0062200204004180080c1d000203010740c030a401178101e84c1241c0720180301140c100110080280064003e82c0d0300540c010000502079410b2590484c4410b030144640e040c2d182da00c2802a0000c24680c3c0700c4c15621003039101108044020040100010070007921114001d440070303156410701007501c3c4d20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 415733732 1250 415732482 415732489
    0x60917010e0303070513090908070b041b15090e06090f04150207061d0c0919020409020706062d0603050c0d05040b07120e0607030c020f100203060a080a05070501030b 73
    0x8079506030480d03400000180100306801c800144a00c000c1c0580341600581d580003e4400ca40b00c940019180d0704080010f01e00086420340c040741d010384201c851450364a9003900c8019180504e3304174040c0c21000f2844800751581183d0070000814a06501c3d400710301e440d2000c104082c80143c81e020f4002e6000001c501000103039920025111015801103444200070b0411300d020304841240c2070114540782c0d072007860000010403041e600040242040d5159214403400c00c1c454481c2c10b0208030500d40c203102c0856954010f0008020720781c002c44002c1240c50400d20b001401c2c040350000300101020142c00c484241c4d5009040d035045231050b040014103940d5000128410344541106006890b00e04020442088100030745a80180303900e03611a000c42010400c94402c4950b209034240b02a8001000160300350301c00e41005c0718030b03030b0b052060319040d00d08411010301e80150040c50068098000c010840c080c1403001c000f070000c28560300204040491915890384484c003900407a4109511003420140030384 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 415734982 1250 415733732 415733741
    0x7020a08030d060f05180c031b030c03040c08030304030c0308041e0b01080c04020a05120705091201061406073c08030405300c010f051302100906091701 67
    0x980041039954403109508070b01d0041849001e641c034090741001c0d01180c1030070b000000104200740c1d0b0041c1021525000c12801058000510040700035000708074840585140101035402103400421280d2203040c10b250500410300c3c1e60b08030b160f09500500402000c2680020704c003031019090708000755161198148442081c1c486540700d0364070901c02008404000405a04e9070480d80044140c03a5102c0081003008140d00c25007018400040f800e01010f8016812160880d4101d901d504020786052020400b10f0062700706010300030b040c1d9541d014100601e5510a5401c40b064104581c018034003804d170341c0e0748900c0c156105294841c00c0d5050b1283c9480450b50407004111021000200c040582a803600007a2544200c40480c0c070b600031886a1000a02c1001c1d02074803880051021003103c644035680c01005404c62880c014966488410002060301a4803e25000d1304c08000d0302d0b2603510712401482151514625504200002c6050410080e6440032520040e50540c00380318110450304a211030161 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 415736232 1250 415734982 415734989
    0x60c080f0a031d0a06050601020d140c03091c140d08042303310b0a260411030c1f0c0f0c09060f080d050301031e0b27010510060507020a 60
    0x103007a900d03542d20f1103810005400e008240f158500703000341e503900c0004a85841c1014000e40219a4403129000c100f8001005001e00402180442f070a0000440002c0c121022003401d0580090301c83c40350394140103080300101c041e821000014a682041c1c580001c00405004201401390b0004e42e5000e1700100c8142052202c0c414408102c981320288000c00444d040c14020510380e5500c20781c01402400c0e42410801e204554002e4092410310354591410307a50f040d040503c400501c441d200d8482850300c84d2010060055004419021407050341c80705044c41c0032140855984140402e141c6ea0000490301b00b00020000082e282030018410146800e4440442c5e02000901004003d880402c65400c1588800111507040064600701c0e6560300fa0b41c7c2e141d44500d4560030000310204014000714060038503c400f15080021036424208140c3c9035035202d12000d440d20014074030201001d000788a40c02d1051403801e00070340002c100d1414141030045503030b0030303610a2606009020407103d040d55640190031009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 415737482 1250 415736232 415736261
    0x90103091a0117060c09090702072310030b0f1203071502090a0b160305031503063409120305040e071809020702010509011d04060303020610060c080f0a03 68
    0x152480803080044070424050010380e88001c00c0c021120b80380008035a030094450b84089450f00ca4a5010b205107010002c000c2c0042d40b05181c40051a82c466070144080c0c510000301742e20007103051b6000c0042c1942040703203a80415046c54407040c010368807220740e45880081218070781012880302c0784481c02e5004141c4080d00320b80300d00790101140000da8004103040d2204484103003100380c551003c1c100c94000d0f843e20303a11001da01c0204100007401074000719002010400c1c1854107440041c002450032800300da08095890034140002c0b80d0401c0b03001c002000e18940950750f01107041080d0024148602c0b8072510803203503250354001050500643c2150041d001c0307801707180e05521341000041d03c0d1001c081210140c030a48031900280762440c61080d50262641655414500700041004413a400ca4000ea41d01013412030b0621072169540c1da1051000441c4290080c042d0f84c549200e845040c02e07c560b00603c207000c0c9200c211000604110122140010540801030300c640c82c2c200308500410041400420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 415738732 1250 415737482 415737503
    0x905010b37050d0b040209070c03050f0c01110a020109061109030d080a0902030114090f1b06180307060207062d140702030105040311011b02060a0207020d0221070909120509010309 79
    0x203200301c4c24141c0b8483d900940714008a5110712000711400203003000c025001400511081d070805100c0d00045c5a4202c6d17900020541c0c80e8050b008000e5540025407000241c0c1d518001e050410070306000b410642c1250f40300070f50400c807600c1c004c83d4584440120305002c0003c0c0b0740c001410445180d100410640d00035000f0400070722211460001c02070166080c942a205000f605c1900007400109156040b400d0b205140300e40307400a0500c02c490b007012180100104003c031203488a51020400705004224981c0100881450004042c103221982400a21001d01081d0031880d40400c0703034485000d03403942c1e14107070091000c1c80c9005551801580c000941c13550904090006169201402c2d00a00000e50001c02602691110860100c0441c6143c90302680041c00010845000d65001e02055800038058030898101c1e035002500c41d940310078600d1304d01c44a4816040800000300711020180c85104c10800c4248000e03210810b140c0d090340d07030401c20043c002484ca00d49034801c5d0490442264007046800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 415739982 1250 415738732 415738759
    0xc050a0b01031a130f020f010e040e0d0f0e030601061b051c03050a0207020f12150c0307200303220807122a151409010905010b3705 58
    0x12111200d201c040903418241c01c00700e6036084001d100c1140480d030041141c88100119400d001051f00c80106443c14402c444000401c0c549450007003100c0c8505610103040303220f030740348005051b84105070820010040c1c91000b4008a03200003540c070703056403014101904c08164071180d69843c401c96200080450107686151819103400701039034003c40416403030500450b66070410f69002c03801041800303540203103210000c0050b402c000c011141a22083c2e01a900c502c070701c500c41d03015030180031740e541122000d001003000340c1140d1040f0004c000c07402ea6846c1884d0181c2c0c20b4480c41d6a4000a400c0c030044058030304181900186100d00850000d9100120644030b01141c204000d00040491300107020618031244000004d060b560618035000600d10a03502800c01c40c0c58449142888450505800c0e40e100b07065003110817440310303ca1068920000100f500c50047c81d0041c2503c006400c000c1c0280c0c54151510b107111030690601e4822015101d0f05090a500e08215820340340c00f981c030154204200142c4030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 415741232 1250 415739982 415739993
    0x912040b2d04050418150f020f0a09050f0a0308030114030a1401021c0c020706140c070305062a0403021e040c030209090f060f100c05030d050103060f0603080a0c050a0b0103 76
    0x4004440080b10b04000702d4103d00c410305030b41503045c03100130900310b0400100204c0b08090ba21030721010740d02550050810308006541d2a540c5e10280c40c00e404a111090300700035070b2270601c4006c0b20f4203078207496100e882c1c0d1441c2e46600c8140410302030304001d111015186401601c080040385486600500301d0200342001c000118000d42c0904101003203c07585071940784800440b0702911101da1074a5001340301080c54400111500c810540b1080701c01c3e10100989140700b60100a418091030140d4080c000d14100280000c440c0f0030a605110500e01c051040901e18880c050244e50840760140e0300216042400e6a21021214000e40340f50341c01890309410068207035142d80500064030055502c01445c4d05c3d08041c10003201d6044031080e82c400001f40c8500340504041c007581814440e91b0a1540f2405441c8d580c0d942180c009814a00e070891740d500c01042031000718050790818820580f01080300c0f5056485441c00d03845440004c0c0244116019241c0c1006010060240070a402c140402e0b000d5840e490b04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 415742482 1250 415741232 415741237
    0xa1a0301060f0c0807030e03190c140f0405070801080d0206090a03050d020c0708030310230f150409050403120c0f03020a02100f0b0a061403010e0c161203050912040b2d 74
    0x1f524083d21441c10b1204062801145d00d030911030300119900302062812004003500301c2141e880642101c100090b244ca1921540280c2d4040d440780d8940124941c1031001540c40c12510f00d24410465119005000c030342180072035145a5942c00d494a15903582030000103502901c0b0342030404a06215a0744001444030b00440654000c01c0c40c2a0041400b03640d6001801c410400e00710411540144084c2c00540380c5880c62562500d1a4007410340801056518070307401c00c41d001603008000480d118401c10041581c0402c0c440a0141010800c20005102a40c018181d1456910a5061650008507203c40a008100191601c04454400d01c09500b10321030b250090200d03070144070b0090b080e084010803028003074182c60b0031107600d0400e400c0c00e580c03070721007818640ea40207481c001d4452800c0006200014540c10454500360003054107115005a8800040407604020590301c410341151003200342c035209540440d0216007080081a882e48104c1e010741c221b0105000d51381081a0200c01c0b500101c0100c50003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 415743732 1250 415742482 415742507
    0x501030507050102070f09021806040b0a0e041107020d03030e0a11040c080622090b1e010504051e090c1207030308010f120206180901140a1a0301060f0c080703 70
    0x6076005540d0754401a071340c0351002e029481c0d204d51140d4080c82940e183c2e602405103400980710300610544000c010840c40d03800394000c00358445001030074084040d0083c07031850f00210b00352820010f0045100e0361043d980203103c802485200c01d11a400c080c94441c0d0098600c44000d1000c2c0caa48080516010044440051000340202e041c03c15800300b440c02041400e214150103008010080180b80b0040d00f14442204000c00c000d80d1044517601003483c51800d103101d12220f010400c0788410381401c0007c0704005074003a6116504203010170013070510000414041d22010081b104007a142c942000381803042d40007181e900080b40b8003d4258580340040c0d040100c030301a0302c0b0884640d80b5480c102051983d075002c0c2e1201c608a01c40508010700b0f2042c018815030301c410030302e1013034001404006001c0da0001ea00c00c0c40c031880180c2116032186000d03100380c0f009001d4050b1b01450100050f80ba081c03e07000510610042c060141042404140151103c01050354030903002a42c0b410756140c0600078024401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 415744982 1250 415743732 415743743
    0x10609020c06090a05300a031d1b0f0406180c0914030303010605210a1b1b110a0b0309010204060f05072a03050a0503030402040b091506091210050103 66
    0x404201440702c042031070030413660010058000ca00c407041b452041803200c9509442c06180c240004515420040042c00f09070711655000f00300306004201403a01c114810300c105045400a4801c00e50318040350342228103843c01541c1c008101c0d2060800a00203240c25481881e40d445400c0c5480300072591584441d4001419884100c0e8454482e140b010002d40e41c8040c05805601c1040180021401040a0803000c041484461191214042d047c004a001582c0c0000c00a4039003203660021005910a180346002074038010074000d5921480300300b21010362802820161010b1808001a1240d01c100d402521503600a1982d9003044a03907207000398454401e03100011422903d0020482c0f040d001c50342d00680003004120309048400d41400c1059a00701068000f1000e40030000000e4004d02a400081d400f0740060750326445d081c010320003a0b51101801a00c10b001c0e0310100b0003151810701c5000c05160094601ca516007914102180c0003003800c811080140c4158050981000015001507068a2081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 415746232 1250 415744982 415744993
    0x80304121a0906010b0906160b07020f160909111903060b09160e1c0303021e031e0406020f04080d120b1e0607060c05040e07092d030203010609020c 65
    0x50701c4003590031030035108501d07681c000c100104907040c0020301815000c000141031500d80f0129641030310084c42819000c42d03c000c200400c004003a0707018440f10303901000c03100140948001030b4a001d50219841d01074640d07034031b554290003000c0c081c0100c1007008014003e0030551031250300405403030058005200481d4400d040a808105074180f15501e84e004810312451604200440e04043d2001910b001ea030980100a2800030f88081051603525178410303010f81c40040c0da842c9019545c911400704c40340c11034100d880800c00e00250b00851440758411692560080140391158a0044043c2c4034200d0310003045400410080b4400310b000c10064000401529884004001c40641f502a41c07081030036154803400c80c403140c0c00311202c0d80040c2c034100d02c401852140b1748102e0b541c1781c804640c0345c08240c2e800100080f5090106456000003036801840500b400d0381c0d02c901d401c02c2d00c1c50070606410b01c60000141803114101000200e0880d601466004000384100ca49445000b0009d420412020109104a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 415747482 1250 415746232 415746263
    0x3050607020a06271e0816030e190e0a32060301050103170c0309031b011805030303280c031b09031a04080d090302061806191508030412 60
    0x40010701d82410003090b041c1410340076803110203103c0044040c45095543c05d94102000a144030002c0c81801c40c00682001c10f2410340c10020440c00c140c0005034084c04a148000c0c0046642005540458035005101c3c802507440091220140010340b24165218102e4100800074040e140301e4440090300f0103200003040d9443d00209401c0e01c07028400503005000c2212403441010348600180948a0244110380c43c01c851200441e14194a2050038242c1005180460b80c581d030344030344600240c120583c00030203e141450002901c074400504900021080084640010024005104031003110030201300481d0240c14405405460304403200009111207541c0c000300b1500990004059a0300444440c100010340300090411020190041d54003100c2800380000c8061a4014880f8980c0b09501804090501550014035000380c21003a0070540c0110f000c110041c02c115114901c2040b04603c00720b08490000700403904c51030160460b801a0100107408105050003202d4154031911481840c0b42c0c4c40c1c1d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 415748732 1250 415747482 415747511
    0xf0501030f0227060919030605070503040302030a0c021819060f06050f0309031308030c2b031a03010c110d210f0f1a151806031003050607020a06 64
    0x2015070381c2214944802040c0f0501001c9282d40e0300140c00a07000074a8828400c0c000744000305060084017144e60303920406d00070000c05014180e003241c140d003091401c506150303501a40300e0164411900800c4640b000d01400d5580d240d001c0301d103280101d0f101181c2d90034550b00903012022001d0800d04040d06140300011140c6000075884202c9a25544131800c2000481000c540c0c0e900140600c40140300034005c8c8954900d417000b4100007400d90700001c641d90b80c2400700a5040c400340040300384451910a107009840106030200f0750411010346800200a1036019100b4451130f210410300c1d425600e840800d48150390001248840c0450860440d09814060901200c41c24010066811b89080e6000c0d03038902c0729865000100c00d0060490081142e1402d6103850302242c281030315440103030500200301e8120b400c002c22111030208400840c00e180c0181418008444601001d4082c0a4400007000828001c08c0c040f005014640c000d00f40c03052030502c42030083da02c0c4a044020b07140c00749400d840200081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 415749982 1250 415748732 415748737
    0xf060609150c1b0f1306051c14010204050901090e01140717150d1203060b120610080c090d0201020f01020406090f3f021503180102070f0b1f0f0501030f02 68
    0xe0700820440c003030114a020711085c820350040180b440340d11404c0c081a03959030030700d80c031110300e050000c603214011950a011051800c0b42d0039010699204110a025a880c0c0d8040341e415540700b40d2003c99810038452415005000c2e1000ca466202d1000050020302c5500c0003080d1b1040416515850441d04e40310f400b081c2e850860b80265074000c43ca400301500081804106647c140a00d081c0041e615568010018031540324001d00b0000940c45810464689014888070f007040a481c07a10203468904058420554401c0b0b40710341c0d102d1000c8050100031a0b04c00c00504054051220082d51181e0f587d40000d08004018098908484820800440c0580c1c540040006048030380d54201c400c0d46011600d120010700d8065505002064030001c000075850300211514000c3c061200555280b41104110051240d4480d4141c2c007640100400404100c0600400c012030b0707000b40d070916040d11070713141002c17402100802032010056540d4001444805203454442181c2d4280c038103220200000c00903108a2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 415751232 1250 415749982 415750033
    0x610021b0108070912030f0305070206190b06130e07030605010c03080a0510030605070801060807030903050f030703090b090601180b10141c0504050f01060503060f060609150c 77
    0x80103a1640d51158072a026894000c0d07160309144600039103400c03450041c810640b0040d0080303051002c0583c001c80c0d00d03101d2180d12410fa4030182c00d65007003904c0c2c10103103540c0e54071a018a682d04c4076003c10301036a884080355101d17480003a010ba800341d038406170083c00c00c07170407548207001c20324140c000250f550080f6254810982c0c5690360040a07036460900300014400900040c46d1000d1030744001c0300160350351061b28020bc0c2541c0f200b0382d1035890041d000704a500c008155200701410300c0b09003c0000d03040403e440e42c0f0f01d10664400d850780d98100c0d00300c0007460110341c0a0715105225090040c460030206529050700c2c2071082c0b1112000505203210300b6a102162400d0302f120806d42d2503811a449920710041c281c6c0e002c9401864540784041d00301c26607049040e11146c0503510814030080041c00c00800354568040d9000744010f07403420b00040e4440800900c001d1810040c08001039040d500e942c11100d8500e4020f000310741c15080002c0800b0039403c5055a4001403043d1107174103805849042c11062175 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 415752482 1250 415751232 415751263
    0xf0614040212160504030602070501020c0d050a02030a1430071e052116020f010603030e01051c0501090204050f041505060c01060e09030c06010e010b0403060e0313090203061002 78
    0x2615003e103d10840040403d5040402c1020320000c00001c22074001400c409000301c0000da1148400c840140c00c091802c0f520405002d01000031060130354020003580c036407a4850808060790b91400e036101006126445240c41b00310443c0081e41840032182c6040860344003040c03800c0a280c0e40e0b190342a1582d6800411202c49010401c0300090307821311500042c00302010103238500000e00c00038a400c0d081c42c80250b444a4000304084107003004503034100103201602103910002d20600e0300d19100a455000380010050405c040000d82d590000358101c040c80028841c544100190b69440da240790003504680a003074800e4203540615040c6160070300916803140207480d80c1511881ca41020880d41c0d40c04104018030071354a501d000590440c020580e01c2c41040b030200a55036038100c4107031047c200304058010552007440c000041c410902044291401c1ea94045000900c403505221101e20b0350090707480c0c980708859994004201e55a150300070791702821090319002c0d00400048416a00d0302c0c4564001580b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 415753732 1250 415752482 415752517
    0x10b0403020d030e0405040c05011409090403140708040f06110c0112020a1b050c01031d1b0a03050303070f020106080c03150402060c030406081e01030519150f06140402 74
    0x361802008262580e8480c0c18141342d51030180b00440e00b42c9208403410380d400c200c000e031b04120741c2d41c000d00040403004041250502d01520000040c280030b802500203410880380d0a54403a85841c1c201c1190002034003c2c0455807075030794071030845e211140c00380161800038664180c90b06851100188043c0030710350503140c030032180c1c01c010006802500140c841c01c0801440c151740b4110380c04800d216010380e6000700080c181c618640c4001600b5507081d0410421950713845000840429000b154600b203503010081f11403001c5805d84006031004c02c40e900301500e6400004107115080c2d81058101c0e210300021740080c40a02e030b5540046407503080041d07019030590400c6040d02414068900460350080c0300614060070325807107600103899a04650840d01c0452150300a2006840d550005d2401a4607606040d003c6503042d691140d85031500c4001d0102c0130980c507c1d40f5010001641ca00d88803d0098940c100025980110b00502070030300751150412203c04e494030b00b42a41414001c5840e0501407045220 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 415754982 1250 415753732 415753739
    0x408060f07031e0608060708010b0a0c031e0f080106020f031812071e080304051503090114070e1815060d0204080105010b0403120c02011d040e07061e08010b04 70
    0x82503100800e000c0406a45050031614010800100b030500302c00d02c00c0009116051001c50307850200042e1042003401000001001840c90210440d40503510314908111041e2061506550304940b01414071000224854881e8003554007119a8a1441c460b69600c0801d980e5264240d03165079403240d805403207410030810905842c04086080d0800d40b0f01500155002c103201c441d440c141151900f04003e0440b5902e050213131900660212405403c29402540c0fa240c234040024884c2d0660814007801382c0c1c804070000d02e681a007903100084181c100b000c0454140b42410f0700404400300b6202e8988501c00004407840d0030302c12401250310524165001410540341842000b4494001c0003045007440c0e0200400729841034280905070007009011f40541d19141589042c014425211409404000f80912090f001d0f0b0780c8021100b030903035101c2e000103031088440702c0401c0251040e003956088030f10607401d000401c80c3d40f040350306003050200c2c0450080c1e603007403001c0bc44203103c00b803040b44648001031100b070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 415756232 1250 415754982 415755001
    0x15040b0f07061a03062a04080304050102060a0b0906010f180303030c0f1706010513030615061403061318020405090c0102160b070b18010507020706090602160b0c07050607081e040806 80
    0xa800850200e51b080d203002e41c00c0c0395905640c40343d0011a0f05400121b01084256010483c41d50000c4840300103005044980020640b100c8006206504000c1104c0c4070480081c051a2000072030310110000c02e80b400c0c0c581c00d015020780041d5100d000003a50000c0c401c40014420001c1d0103100b43c2c045204420b034ac0307a100c011521a04082600301d45400a40d20000000d1628840c601c4c4e102006d44070f9250980c079040001d48400c182e007004406141080003042240d60f50008103005e03604503104002040401001c1c0420740102c5154003d401510740000c1c09080da80000d44040c40d10026801c88034010004040b100c0c0e144014030039043c440c402480850b00207a55541481d0f4000018007503400914807286c2c046003998001d44907403000da04812028050180e1011060000d0040c2d4001811f43c040e4217002201200f21600c200c0030380c0c034408131b16101485810b000100c0205001440e03551130b00168244015540d01c134420703082c000c075181c030090100c1030303122030583d41216403040113001181e0384d09040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 415757482 1250 415756232 415756261
    0xe04060803041a0c03030f1603050c0d0e07092d0e060a0203040819050a091a1803030c03030403080f150f040b030106050303040609030c0911070215040b0f07061a0306 73
    0x40308442c6400340701c0c130030160398200701840c45010030011289060800d46648a400d0240c2901041014104010404000e030a201110b0210000850028005002100081c141a0550000004242006039003002064900d0505243c407143d100309020160010125500312070503200c1c8501281c00c8940060b1111800b980a103900078014800c852810284001c0c0d403003a881d1040f000c80100b2008070784211202c0d0b1180c40c2e8000303406119032100c164a400d081c940194000c1c10700300c0746114416109000c0c83e84051081e103200314a6482200e03280c0c10300d032034043d00c91503044a00e544c0003049413001a0403140b020301c182c0038440000d80503582140000003400050641042060381540d2149400601900c0402c0240001c202c5582c0d400c0d80d09045281000d0700c0102903200d21006414038041007082550b030011034154941c11200301800d0640c0c0310741c038501c41c0034035444502c03031420115000304c0312448000140382042c420307001004900d0030700c068410814144440701c2d4040e0300c20f50001d02003c0803510b6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 415758732 1250 415757482 415757519
    0xa030c080702060d0e060a141f0e0c0405130b0a03080313050703030201050601021b0a050405100b0c011a0306040b0105100e0409080406031506080a051306090c03030e0406080304 78
    0x16451401225402143c03081e0f02c41c41481d2440b0780e03038603030421260900381304145e088020014184a80b00140e844460084c50241241d10200c1712070403d41c0040709041010401444401c41101c1c29284c000e0b0004c050360042d12429018040c030740d40c01d0820181c41c1c030503040000c80040100c8001c605686076040d094000500a90a128030b140008000c6141040100011886940041090314018000a0406150128040800550414010580d03980c3c402241c1a14415500099503590380d000c09400d0400c59481440a244c002440c1005218190030405002505406902914200c482415130341c4204403005040d41281000502c414500300c00c40d4000541e080c500552540034140000e011104808400c4581c402d00180030400d654041c01816440c9a070145240c41d024509140a80740820003091818115540c0000661240741d0445030030b07182d0742001c0c04206600c65880d107048984c105000660210b441400b90068070f1803c0d0141c4010780d103000016606103840c286101c0030820a802 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 415759982 1250 415758732 415758743
    0x1170601050d0302030f03220f0606140a090504020301091a10230f06040f1701051006020a0627060c080f09100e0c2e020a2109080102270d050a030c 65
    0x164440d00d80b040620901058089d441c544407018140c904102110b00caa88140c110445610007088103070303640307400c1c0710859460200100c0c803590b40d4400a401000c000707000801040c00020741200c1c0510b111303801d86c0300341102c200880130b0540b9651000700342c818080c42002d4a1482c0300d0400400d0914290323000b44c26502604460405848804038030035214284c00401c0803610440902241031000d000b200d803c05a08080040282d003000c030000d482d810110009407605031241003003100c8041c0c022541c4058200800812144080362034468042d0030780548160004001f440403c103245980c0101e18040c40000b07004010034500303244036502410030184807d501b8000c2e2400d1007180d4443d00803209804403c0c000594140b407820501c0700105009540000c1154860040c0c9000a880d44402c000091030310070120701400c1403a2000c861251994002110030b50002c00c20182e102d800c4500c0310020005286014250300500c01408000749001c40042e229a10a00841010a004201924650f400358 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 415761232 1250 415759982 415760011
    0x4030521121315060b131205060402010507080f03071e0e030706140c03070c030c0806011202041a15210c0a030507110d0e04050c070f02060903100501170601050d0302030f03 76
    0x1007150012100030b079000807500070300003544201b02e00080e40c2c06000b500c9908104118071081e92500b039503070f0710005c000a051000020751507040c80041e60503107035000c21441d51a0340e00d00d09000000d088841ea0555170102c070248251100344980202c0030507844c00340c007400801c0c4d500d28018040758003002016410112100c1080100f03603c0d00140b00a00e159401071140f02e003018a149001d0342d05903107580c05070388132b500518010302c0540703a000d103540740da503070100d80200300c0c00c221041c00c000358a10f0061140c0c0c854419100200d003403032450b0140400b440d010242106480c400c0c07000748115030085035295603d040800c80301c8001400303035000c1c0303410080514100f9101041c1c1c0c41014901005032183c4804107040507406000d81c0780a014541c0c0c070283c035140003410520565a49103500c119910000c0c0300f4080880c4c041042c0c0c07010403d40c241c9a201e03900901181d40d44808072100c0040c0d841140c4218001d281c00420703a07042c010300d0387c004588c2c1035005519200303817201854401d8101418414000e40342 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 415762482 1250 415761232 415761263
    0x903020d1404090509030721090b13050402071511070807020d0f050a14060106090501020a020919020d02070c0501020d0503130f120305060406140102031606060902040305211213 78
    0x140d204d02c40c0306025100082d603550107513050129217a0346c0c4181200030381c3e03007070b152044002d0791000301403080300c60910009850b0503090701d62421041d0b96401654000d4070200c0c0250030303c081049200714104448804006015203491800c1ca24402c01d200130b4803510041002c8801800c0c2140210034140c0210605c590404941e80c40f607041803000c103016520401c2c0e21030901c20200303041c480ea138010803840c1011102c00e450000040d4403a169418064822004040055582181070820400c0c05894003001c640e14a284018a4025003000c003040d00c2d007203402c40c070200b280d500024a030100740d45e81d500d581d415951100340701c1a1001e2007007011a0510012a03130300c40014006907075450328212a0310007090500d0031205200413120b02e54058031415030403003152142641c02008443e080700000410002205640c00e00d500a0080d9501c042502440014004140040854201d40c0c0c0ba560518449441505040e080c0d010302071300080a0f9801e0841012440c1488002c10303801041d4407406910524240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 415763732 1250 415762482 415762499
    0xc060405221803080109061805041109090703110d0201090302221401140a0b0417030c07030f02010f030e060a09050c04050a0515011403060103050c12010f03020a0503010903020d1404 80
    0x261280b141c42c440c007041c1c0036002c00d50410407031400761088400422441e460084454031000f000c59642c819507584170041010300c554030034102514000500a00000c0c24503d01456580d9014402a502d03401504031021461911a03010321312290142c0d520300b9001e045400300000541007501c894400154007e01c644210381c130380210142c940045525544542c9040f14607601d044044002a201d8440e0883c10f0190100840c06d440550346101c02e05223020130302c80c803030f649180f00702c002101e540d01c0f030704800000700140d40102d0300c0f0041c800e0741c404d224400c1a4030b040d82a01d5001c8030500164120a00103241210540d01908080d8010700407284103408440c0410100d0340140c9070f0001244e150300401c03580e50700841e0000c520290a18180b940c0012600c009400da000c044c0504d0304060316440801c1c1042031a00580b00200e1008000210300c1d651181d03400303d5003040c0e12040b805841000d000080515044c410b4101c215015009000c040c400010100da0a0050390308030040c254090101044c14007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 415764982 1250 415763732 415763741
    0x1110106080d05250317060609030a1b1d0403140309030405060a052101060f051c0b0a0e0c030a06061103120c0421060f1b0c2910080c06040522 63
    0x500070344030072001c808803981d4819110700041087d07000700e0702040010b465446c00505101c8060f00529201d103204512000304803100360551002c81024081301031811000e02800841d80218440d0700c8010394894510a032075824042201e070707a0300c15041800308225508000380140442899458410b19101d01c1c1034291004101c000c200d0034031f480380702006200c1103410110491613041130782001400e0650040340010142e14038007541d203030541c03500391520345034444694920183c16010750145452603c800f010760140c10468003412018141140010300d18020003600c01100b507018041d5103041030901c1d484403a80000b5102d24500c40c420070002a9010742c1011809020710f1034144c119451415081400649195509600d07400f0b1900001d043c480c0d2024800c41e40b01e500c2d90616444e1072680313082c40914114070f1003141000e04003988003ca811421504041e01c201010903144110b43c2c0c0f40c10b00c540d60382c00007444080c0c00140802040c011440c01030f6a24821400321700c01811003540a0001a0644 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 415766232 1250 415764982 415765057
    0x70b030106020a031805060d0e0a05010c11060609040305030103030f020f0d091802182704030e091303090605070618121205060d0f0f0f0c0501110106080d05 69
    0x181c01000c0c0312004c059001112a070103982901c00c40d107103a0f061900003078403849600e0501500f95035403d000026440140441400c060b0050003c100e1090302030030181280e000341d1000c0ca458010080011010f1034244201800355405589650446e800c1da039065640c89500401e400561161500c1d1400d40c2104100400a11140f651600002460030000e14102e9102003040d0400c0c9005018a402c6510751152140e08103000f00c5000c0740c0d9071603c03481080d14155a84040c00307011a8142000300745500281c0311001c40c142038402060580d540110840f0301d910b24100200003030003928041018510031005444024090000055003404804100041c40c126450441d84410821015005507030040480c03c11010504801d226904d0801b0004050b10300810000300743c0381040c540c81083c0520310b0746900050398000124281001030381060804c10007a8843c03c1d0004020b4881041101c0040c004c0c0d0007201e4141c03009141c40f181d01103040d5050b4100341014a110310040c2c0442c00d4030300212141d030104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 415767482 1250 415766232 415766237
    0x7030e0a0c060201150602060c07030c171305090906060a09051503030301080c09130f0b0c0903030a020c130b010e060901022a0f01080106020a02011404081b030d02010c20070b030106 80
    0x70003c05d60340068642c1c03075a510a45c00c3d1740200d0200108071758101e04558190344e2500c2e109000c0002468a04180e41d5420855420000302041c410065076200800c981940e10440d2508500d607101c8004660b00d0000700c940680028848008114801241d0446174200c11022030351100c2c44030407804a40340d504240e0003003500b9400f20240005900f0842c000c2a00840e0500380d0341c2e0414019111820140401203000381070281060000b0348140e080c3c0241d400e0000001c055070b1743c0d5001080002c1d562100034200b58400e2a0800b10440340c0d011901c43c13000001c8040e10740c80c104145120800c51240c000d80801070650292804031480341e01c2c403103200b1420000c9105100101c188440520980d1400280c05905200401740180081500068079003030483d0b0928019080e45842c1107030303034407038011580a519240f00e410706030b0104480c2c40b828001c1580c4240d0440e40180101c420483c01d90300000003010208903a07080c100c5408039403214455000222004550b4520780c0e51690f1980390f03200340d101800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 415768732 1250 415767482 415767491
    0x10e030d020a0c0e0408041502030405040e0604120e130209120601030c0f0b180f1206090102040603110a051b0307021509030d031b03020d0b0303030106033207030e0a0c060201 77
    0x30080d12494000207403180741180103851405c0c0e614a58a445503000e00b0045503820040586924420400c03074014001c0a402402039200c100c0c0314030313501c1038141c50440d141c20911a024240a204452010343c43c5401070010b6118040100844021750005064035044009140c890b101d62404000b240d000b9132180e07000101c1d50340740400c1c1c0d102e100f1036900004100c54007001141602001d00c415011400802c503080f080355a412000140b65000d1030340c01d20070318000d41007000358900b01035001d4000c1b01c2458500380720b5071940f010001d9040c41907052600c0030500920040154401d202401c890420801c0b0460b45460801e80000d2041c100c0003481000001c00060b0107003590405001c1850480201e042c00c0c270150110f40c044180380003481d5001d4040513801f04408002d000c0d0381d04400c083c41c1015050742d03a6542c45010003005000c01e9442040a610a44040f6681e41c490021800010700407541c0444161103c10f000c8002d000d0b08203618106210300e0303d01c400800c11402c236000003480075800004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 415769982 1250 415768732 415768753
    0x5090112120215061c060f0203060a0801060e16120207050604150b100807121805070509010617040c03080a02101b020c0d0507120f0203070b1c0b010e030d02 69
    0x3900a1010380014045402020031154143c000700030a40e00a14122100300c1012070751030b4a448a9a088500601450f0a00d5121302004519034001d50180b0002e46840300300544500406080e108544a400701c440340309000074054030300d0440c410060260526081b0560100c91800340b050781c04c0004207450307540111050004001e5405400d400002c8003a0b000d200025801e07000802c60800c666500d0284915440080e8150348a416405108101c03002e0800c0003007081c0c500c0304012484d811303080324030b4420058085083c0ca402641c15048075141d6035825000c948224110240e183d024104031502e07a00c1400200000349114050a194403069009000e06021038a014054641d4650790a81401c01c0d0b502e031030718456010819100408056030240c40710102490000d143c022942e015008001101002204102051200b801d03800d00881c1291002034903980f42d0020385c4240003060350359035401110400c08884581100d468400141003450120070f070036002c01c1c14590641c02c41c80040c1c10440488 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 415771232 1250 415769982 415769993
    0x1f050d062c0406020903030406020a0c051f0c021302040b03041a0105030d08100905010e041415070c050a02040f0e01060801020406050f03090708030415080702010504200a05090112 79
    0x600200307003021150601c0c1e4150034025200c128095a01c0c1249200600000c0500140e0340448202c20f42c05000c45e5601c0e030365440300940360f055a1380107c0341c1052081002599190400040040050760b81c1c0c200d5821402540075210222035860407600810588001000d10324288050001404ca1414040e40c0b40381900c0c0082c1c003201680c0c0100f040c00d0740c102c010b01a58900041d050384012003410302180a894104010f074070f14501e41d20150911b81000700208420002e802c0f0140118031440c1c4054a605c41c0d6202203803100c11074500440d0340c3c0340100010b100b03e40b1804c650010300d40554180d406c051030a0300880c0a65102060000c03000b030301d445400750620000d200340002081c54400840c28181042030082280c4121031450000302c10102c0441c940d0441848424001c5c8140d500301c0e50342d1130745c40350f501c80c403088030502020202d4940720001e08003500600030707148510341c4550425801401c54a81c0350082500126151b00104044004111901e548100c103010381580f000d00c071169200351819 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 415772482 1250 415771232 415771241
    0x20a030b04200904021308031912050f070503040f05060907081603080d150e011203110610051921212a120e040501140607111f050d 58
    0xb0a140c0700d07080541030703940c031140506941c0510701c00c540141c0e403011408082484421660020b8816003c0062a0302125040c003103410041d0b011621123603481004200303080111002125070280201c034510010b0303010f80c40341c0025503005120b07800c02c038220301294980c1840c01d0800c0301e12b044158803644050100980800102030042d61110039225941e055980311003441c01750309205021680c0f00e0b9615101e0290321310352f100140174160b28684056030b481c001c0c0d80c4820020002600412100681c155035188007268451040180d0401140343d00e10300802c1c08542901655040166040018082020032980005014036055004803516680442c20041030110000208080c1204000f176020510ba40090000108112003204114660b1002c03a160122000d5002c00800c640c003540100034650b6003240080d80301c0c100076241000140c0c0c0340e0086520a050131460300e540058244407401c0003031049038a5000c0c5100c050a41c0300e052a070314004041c22020707030700c40c4804100c010910a0314001240716 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 415773732 1250 415772482 415772501
    0x180918100b130c05041509050d0503090f0405010b120619030b010312020304050a0308090103180303021201080f120c07080a0312050f0105011205060f12100501080d0915020709020a030b04 82
    0x20b04100e50004a40083d03c944114807440c003000003121042107646005407240c0c3c0040c140540300381120001807801c141c0300c1c0d0200107200c0c406c1d44d10101e01780030b9080502c104c0e416110145035891400b402c0b0681d110300021700908c00c5034000e0035805c00f25401c04030003542c48006d6100b0a00c4000a504500c0c9c034242481409009130308540c0103001c10011a0361304880d4000b02e90300f000380d00307070b4400e40c0b17000480151908020030300204440900210426070f0650003003101d12400d000c0f010081e600d03810060b8403180100212042e50344940e540300f0540c94044001d20b0040002002c503600942c5d240e44150a0103000071081e40429440341c00500c00034564000c642e44800c400f00b4100c4036605107070001e13201201101c0d01d4168a07903208001152070f29003402103034002900401c0040054240306805590752140700e9a101550b0a02d8000500304070006101c2640064584031900c41c03608141a41c01c500304a2003100045200761180040ea0084510040c03010084507500843d50071180010301095610742c90 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 415774982 1250 415773732 415773769
    0x1e0503060c120609040303060801110702011214180106030c06030504050601090c0818032209150b041403070b0706090b070509030d140c0304120303060506180918100b 73
    0x400b048480341d442c08516400f54003183d0507034140d1143d0a0403001429680c001906a61914034062903403004600900a210b2007682c80c02500c41e9412441801d84181100403429081c881002c500b02ca0f1032126061250351442c40005200c0b6030341e80326104121240d41c80000825691402e1005000c82807001c1ca014102e00c020510003500105d4000300015002006806d043d5201c0c2d24000c088082801100c040c182c1d19013044102c3c030b000003444c070541d40741b070302c01d070310009203003c3c2844845000c010280040300c0e000d890341d03402c0c2450b150100302007400c441c00d0154940100351021604800800180c1101406100c002031110981e15111140502c050700396400e2140034424030703d0a0381d0001d44024452000d14101150b034417202d00e01202402804c0b014880c900021a000c540100301da419101140c1c041c2d9003d200a595440073f0140364840c5e80c185240110f540e401d1764150342000144140c020002c0c8411004880c03140308503a041044000b90449002d4507004c0e03481540c40c0c907210407d60034100c803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 415776232 1250 415774982 415774987
    0x90114040b031f150c030c1a0601260c0706150b0310050108010b2a030a0c05122104020303090d0503070201080106020d1b05161d0903040605030a0f061e0503060c 71
    0x5020341d84031090b03001c5401e0811020b403003075108141c4a0b440007d141d561140d910108410f00c003021306d10321507049403c2800180001c60528003400112411800c04882c56007040c040e13180c82c104040d00c0d50000005850098072038021010100302d812120000b820f40301603842d121f00300041c01124640880e40041c2c108030b24507005100d100401c404a5240050800ca07111900c000c40038108000203c60420085500012466680c65900418000107181c884d10507104034444412000b41c0e03034000e1955110440c1241c4002e2215192404002a0001c0c001000c803414103203034400148900082c940300315240d800200c0d5440031560402001e07030151040b40040c1110350217010f0000c04c00c00c041d07890300d003d549000b1288024441c00744001588840e0b48600c0c0d4001548880e00c405103211039680e0f042074020044005003a2050200a58060303e0300c66580700d14544032000e400024000000110000030303998140084c4e44044820648a81c0c602c1d0240341440d1450f2408041c103241000f44a00001c8204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 415777482 1250 415776232 415776239
    0xa060e01030c09200a0c050c120712050f16140d11060d090b25051c020f131401022107061d06010603150b071502090114040b031f 57
    0x1034442400070fa42031000b0019850385554000078010660b00c034140742d03001d00022038540007a4809600421607000700c1c01c4a100412000500211159400707402109810001d0244207002003a0140e6403a00e0280e0111401004442041818018070480c00c40800c03403500300030040c0c02000081c1c1038131000100ca40c45500ac0c82d58448041840c0555030940c8030320000207203081d07403c2e071078bd000c0326841d50040e42c114038510746000c1e0340d2201c2101d03241c982c41c0c0201d044008222180308000700c41d010007451003030f078403181800700628003e50482e59915412200a000304900302001035071120040440f203080b00c48111000001a083c86a00c0c2200d4403510908a08400c2c0c0c184444102c43c516940001e0001b00c9644440b644200e160a290304002507010350310001403001e5240d0804140b041c0c0d490510b1140c10395511540445215249000300202404107508070f09030095405840710201c1810301e241c0400700c0e039000c00280e40c40358000300410000032080c0088800c4c1c0c40e00341c7d564440250000c03d8018107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 415778732 1250 415777482 415777493
    0x106031a010f0f020106120606080f190b07030603020319060b040c1e0e0a12050d03090b071d0414010f1401020a060203040206090907020607020f030a1b06090b0f0a060e0103 76
    0xba0001d004040c850103240c1d910b18a8800d50021000380094605540090510f1038000040e185910a146991191041001e001c1202050f100802844902c0905956a0303d0343c6190044030014203641c1495590500040035882c1440720054000b020141e0100000072454030f18100c6104d2860b540c001c0e460280c0c45100c003900704c07041c0c1c80d00c1551880b109140e078071480307030446031302c211007001d260170030044800002d02800c041031100c3c51310720800544040043c0301c24120220717400048041d14072440d60300401d403054010456544c190a0304a5118041c650354004507083da0041100c8410054480004000407080d0428500c080c003045030041c0800d03217000000039034400d00c029001e0325071980000032504640c1c3d060120b0706810005404d050b828900104082d44812003125450054010b041d200724011501104444040007541c50f80411142d201844450312903440104591440d520410031000c10b20380340f099840b603090400f040050380303000e02800058031455030100075010078280042c0000382c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 415779982 1250 415778732 415778747
    0xe01020d0c061508031e0a0c0209060d0506090c0321030103240f1b080c04260102040f0513051504090305090a0f061407110d02030f0d02060106031a01 66
    0x500c074502404501c401d42407800c0107003000d01d5100c0428000c030000003121100400035044010003860400c07240d8038050008040744c490030401800080d00341d4000c070b005240410009400040240080102800503554103150100589038240c0545c400700590b00289801c2041410451084215001140d90001d03480384501040c00010544280d154203040301c4141c0500f04031905030500c406204200308004a0801401e078102e207210b40503003800c440384145014080c10f0740541d210307510f020729140c540702c415015a20b00c40d100f0038550b201d14480007d24403017400540040e00c800055010940d02d4901001011900300b90800311580c00c0404100104603444071101c00c81c40213607000b0803019080d14044a2900c20181035940c40051100f022400c0d2214000440540344a0745400d00c0d812403444130610b55024007003000703100ca807256500500301d092112410140d10320150032604103020b586025414a40341e07010540040c2c2c0074600401c06198035014426a2400d0103e00c0d0300540d030744134002000c0d82d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 415781232 1250 415779982 415780003
    0x309050f1531020603040521180402030720010b0604140117040804060c020d12020f0c0f090c070218090609122107050f0406030518010605060403060f0207020a1d070e0102 75
    0xc507004030024080c02401c3c846030222030061000044141c0791084503003020b2704144500c0811110320700c0000d01504017403080303d005050036110204403641c1c54580171001c4443c0481404d080d5200c0424030015290700c0f026101030600d10a000010000c4800010200c00c0c01060900280b1108014000440d075000100d4007611802c0c5060b140581403170010070a038000344400208441d603800310340c07140c0503408545c400904408405455044000d00204500000102e004c00c3d8004811400314022010950041c0340301c52020b0020700c0d02810301c05603401064001c403404401a00310804005490070144010415160340c00c49150900080d038070b0f500d0090f00e61241e03050b4503810001c081800f40340602c0075038035050b00c2c2981d140d0352a03494210080103400c098035003249499a00c5501000442d041c010741080d500042e20940c141482e548526002d001d50350400c003540f50b402c1080c0380c0583c44100400c2e0182c000d50644003030750f1060444403122014002c10003020004c4c0c821000d0707502da90209407040340c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 415782482 1250 415781232 415781239
    0x905011b02280f020907030905010b01020d2703020616030e090c1821070e0610050f0a030e100603031706030c10032a08250309050f153102 61
    0x841c550f15000030740761040d010107035100301503508000850354035070009083d844c45031000b4069800b421005aaa03001a2000341c4007042001c0050b4140c0f00410841c0d5a203419034007003417040c0696035000b0508a610203a10205070078501c40134a000d00d0380040030990090070585100080d4a0201d2b581310042c05207030341c840c0650200c0c007503080540d0303521071402281c0880c900c0f82c1e03101e400e501c07032000d07a45240511980c910040e00c00d001404600d002c003419603050134240c445c240b602d811000704202d44c0d4800e000300c90a00d07585003403d00800c50200706500310780d5a086000640c6a08504010304040d00d004c0005540c440044c040206940f404900c40181d180b0584a42499681c800380540c090003100400d202240950800703d120b0f0803414800c4c030b020300107030344803128941c40f41060740d5003542032020341d0056054500910301006100703034040c10710180078105442d0251004400c050810b061407011040144402060108600030358102c0106d90f080d4181c000c0401c0f00d0309540915400340446e005c0e21 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 415783732 1250 415782482 415782553
    0x915030c081b0d0f0b1e031005060d0b06030a060203090d031a0307050f0d050f060f060105130b031b0307020601030501060f0e0109020f0909090f01060510021005070207090905011b02 80
    0xc0c0513651308000c0142500808003170404141032180c2882c0d0600303150340c074407074440c0e405c2c58070003044940300d03c40c0038050242004500c81204d40303600c0c0084c038020b010310380c00d44900030720100440c0c07051015500920085010340030110170803c0003030a8510b41602c81004a50041c400c00135560f00040810458106949000c00c0c940c01c40e0001d240c008040001070528000e0108156070a1000700d2294801c80d003404c6280c5942e140d05004503803d0007421110107442c1c01e90101482408100c0002e0340d44a1031103440c00202c99040014a220341d0070545110001d80c1c0108018010000f01703003e4071014104108051440740d181c03440d0340c0040c0d10180304101400d81d000550407003000030b840450f042001d010340048607509008040e42d55030211030014038480c0d441e2a80100c5c0501e4007487c541050003090740144880460700308042d0042c000074040c8815882014400114100f4901030403a045000b200001600d039a01040e10700700e41c44c0d0140742c0045410540800b084010040071070580c04d25004100c15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 415784982 1250 415783732 415783751
    0xc0c0a062d0203010504050c0702150906070804090b03070e240301021306120f1806181407030b0915180a0f060f0b040908030703020a0915030c081b0d 66
    0xa00c600c00e00040e038401c20384111040d0544266001941251303011b0fa0b0070402ca42d18801d800d150f50150550003540081d00c966419131b004444409040c01480003061755260440b165a5001c0c0e903403040e808070203510307200c0604000f5071505002a0300142200030320b0106a18041c21070000c8800e8148912030594081d07445149980c0b025415103125401c1c12000d52049512514054409802c20070140c041c10b0402218400140d218024080204040e015007140b9000356910500900910015003400109100b1198042106441401c0586d140c03400079212860840c206902c6c0e0060080c8000310b00c2d40f10104081c4c0b6202e0000307035030340d100e00303401041184501da046502d030038927002c8030001c2c1c84007610315071203410302101d50700c80c00a00310945800c001c0ca0700d000050000f5100002c002400228050000a5890b8020b8008044035216807801c84000c5403a03200706c910030400109120300113642c1ea00780107074076500414203d4101c0390700d105a0030b030b600c5612400c0f0054415098221005915001481c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 415786232 1250 415784982 415785011
    0x9010921050d060305070515040e061c06050106051917060d03051b060118051509130b15040636110a21020a05040504020702010924080c0c0a06 63
    0x76107020007040d1043c0501940c030300745166200054018548541b00b10384c100300880500004460444140c00301c4000320307a60710401c02c80b060450040c0b9460035440c441c3c0c0c031000904688200d81c068a555102c0035185c0000c0c4401183c02e0980c29a03000030b202d020402001110300c031195007a07100508032030498a069043ca400c40c1c950145090343c607101e101540e800201000041840ca0585100b125100240100c00c0008001c0d81c07000d4480c65840e0014541a101d6810069000c5a2001141c10000e102903110381e10100012030490f05020348080311400400346151500a54005084024000c01e903082c01c0d40040d0210a404500718501d822030b08030703000c0c800e80960030004070001c5805070140c5486200c0b001400c0384d00041146420303061500300d1100c1901c0c4601c00d60300103060640d102403d0600309030074000258070050b803d0341485a090000580780395506001d42c10881a00038850340700140190140440201810500c0400000d10100c02030704400200184020b40107c800f040c0d038003462154 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 415787482 1250 415786232 415786237
    0x21b030a170c03070f030f080403050904050411060703020a02040605041103010924081507140f090d0804061d030105011a0703030b0901060203071b140910050a0e010801050901092105 80
    0x10032540d8000419007a00b03110105e600c09416074000e440e80b4030a500790010071a6000320458005021820600c84095281002d5102030f910a208000716023940ea4245c1c0050615040b40c08210010b80c80b0142503411400d0a0041500620701603405002d0901494003628103070005010751000956207256894041400c0385e04000010703184a0000c200c070381c48804403038585d1035102c00400c4110080c0042084540f140c5c1e2940746c104000301e0010b00f86010041c034440694400e254856120440b02c1c0d80d41c01159441c4014001488103071070702c04110003003010740c02008414899591190340b4100040140103010f1200310104041891002c1c0c0d580b2551a0070380041c0b40108689070089000400441d0840d0000002c1030228020001c0e000200c01c42816200318041501074020754513140c0d01d1454160900b0302d1043d41000c41c240003281040d48038008104443d01990020b40b141c452a4010061003e083c030031180c010030040024001708585440b1454040d140100c151b510240c4840b41c020200d204005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 415788732 1250 415787482 415787497
    0x507080d0c050306032a0105070203030d050a020306011407030f0e180f0618220311010e0a02040b061201051e030a0b07031506120b0a1d0106021b030a17 67
    0x40060303118411005040f5041112264028400c102650060880506245c51440c800042900c4031812030001180e0b04d40002c0d000302c0e0184014040c02c50819a6405001d1180744174031b41c0103880780352400004041000c444030b80c03130075100c0800c211404258400e074810420b031860704020031460010804202443c0702405048070741c10404084c05242022040c5081c021001101c0f040c3c01581806541865084251041074110711092240e010b0320060041c5944c0c100d00a0612009403103140050500b5103104010003102d6811000010b0110326140c8103c101d000801d94a060a200c1c004942000703001041c01080d1080000260140c0a148408041c4010006c00b9007070704d9603140305d4a4403185841d01a15600d001c00d050080034080c02c0b0342c003130b920800c980280e5906a03036141d1061b4600000d10345022146d070401a03818010460711280e0b580034400f100440c240f002c0c690301d0508005d080c001c602c400c040d07000b0082064200b10b0340e000910101025000714040202814584442d4003e1142c410b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 415789982 1250 415788732 415788757
    0x2160b160512011e0914040308100b031602010207020a0e1e07021f0e01020d060f0b0f0d0c0c140f07170c0906030a21090e0f0703201308010b030309030d050708 70
    0x4003410b00d41000082001c1c0100d10275250f410a0751a2000c1340c4d80944401d01036808101070900020f86000d101c10082e00340012180001403138584290003049006e109508070340104d03c5440b0038000c0d0115022040103200c9151a2a00c04a09015500941301d80c508001a901890509001e188050155122141c02004440215520744682c01110702400745803145120b15801c1072400159a01440221910322244e000d003185031003406036500000b0a94464800100844810f861001071024400c0200220341034004201d0680c000003618038111141d081019034052940340b98411b2000000d5804030008201c980600039525540483d245c1005620042d0001010700a00b005050b080e9014102604803907480c03e18407512a112100c0e6540700303a0b425950b0301041c00010b0169817007a07100b51844030802c0c0104e45280d1803a10300400740d41040320346016104000c00200650103003442180c140f13a1007a00031b1800c01100fa00026101d500c4001c011041c000006407003010000c0030b030b045845481040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 415791232 1250 415789982 415789991
    0x3030c21020109060b0406030c0b160c030303090b091204050402070501021c02040305160b090d03020a060f021306020715080702100c0513060507050703021302160b160512011e09 78
    0x100c400074043c140d4560b0940b5501c1c5012600126401c050156009403504481d140c0304080c03404090300f82c158096070710340340d12503250082100020805c0c103ca400850096402050100c4181403401c842040078001842d81e5002d20182d80a4180240c281c0c3c040b140c084900607240e02d42130070058068842c0041d40070425100042d0343c4c002103036a901a10a59014104480b000400781c01c110718100f90a000b245105003043c00500c07414074242e8884442c441c42807056811003c65a95684150b4030104543c110b46600401e84040c1c4100d00d01c16903005162610003400142d1814201d03440c0d218aa940c10410020004001001907008100f00d41502c405480d0801020f1445e02d00103019801403030031401c01d01d152084c0010654070803010780710042c0e04600540b2950b0b186608010303c6428070f001010b0865028010151003111012001c410302e4098560940c0ba40380c101c0d18a8042e1100e4114036090100601002c3c00400c50040c515054620750b0351240b030329100040c200425403645a011718803143c100b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 415792482 1250 415791232 415791293
    0x906030b120f15180705040f090203010c0c14010209061204020a0803040305011b0518040902030c0d080c120a0c120903060905010e070801061815080604080415050301030b0103030c 79
    0xc0d00c00c41c0d901c80d03d0b0860f105601c0703200e05031008080410000c911907200040a114501d0580e04c456507186d20300714006078501441d030104e030944003c080d0702000325003000c400d070083c049101828001284644000c502d420f1300c14002800384d0280100f000b003c540c40e00001000c5440d0038200002802a01048a8440e81d42e46003003030180c50300c0515000141e441c440bc0400c0309020b2425200040c158142a410000003402444000c003001745059916104d400803160043d2115026050b110703002c2d42e4050f0340e0384000704001d4a018442c4000f204d0400c0c003040b050147c0d907400038140408a500c84506026520b121030112441c0034142c001600041c41e081040c4204201544510400070592044d2070710a5503d82e2010b080722498410952483e15401c1e01801c800090750140c85444803180000c04140d40301e400407807a0000403101291301e01e000050a103c1300c0448504445c00c8411403400b14030310742c115030b00d0704080a03041c0300c020144100010f802080040100f5a240c01d0a8143c070120044c0d10b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 415793732 1250 415792482 415792513
    0x1d01110a020120030a0c091a09040b150909100306020f0306090f010b0d2a020304180506030c100c05060a150f0f06050304050313030302070f05040203070906030b12 72
    0x3503690000550b00e020040007496450882e040c40407803007449607038107550303c840c00500a0149504804100581704078040741c1103905c034131222503150820782c009480718102c4041c00100c801c04030010384260301c24400c00341c0e81c803440c80491720140000e40d00c03401280c60b801c0c20010b060466410050846002042e4221103910000c0518407a40003107a07407090700c0d11640380440b0151400c1c020011018401c1140e8800e40e00340d174010710000840c1040d80103055507079012184a46c04070051200050f04002400c0003400341c41204102c4020001008004509092002a40e1031112091070360040200122103031540780035040700f180307054000065400070f142401c0301000034000740d41c40342a400042ca2020461144202c1100e09a03120100b1b01114a41400d0701607031940c20081040790700740b10070400001c2482c070041c626070003075210790010502a41001052a000740b19a0000c5010740c1c8103008100c10a0343c084221000c80b51941400546a0308800105103002060050f4049520501c0c0c0d5100702c0d030740d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 415794982 1250 415793732 415793737
    0x6030f20070c0f03061a0418030e0d0b13030f0906020a030f120e070602060106021504020f0f1306090605150d050a060b0705070e0c0a1e03140a050702011407121d0111 73
    0x2581c10803034040c0740002010030040b640f1004550fa51754603503444010001cac0c0951100d40da40c1c03200408d100d48000a50751642540d00c2c08603060075040c0c201011174000c060b00f140305040001e80c5401c0c41c1c031030036080c000000d588201c042409030405c00244281014280216480c0c441160140740a0041d4416102110760711199032240710014820718000013040351002c81d1000020a42320b0383c115103505c454081001e08030310301c0b481c40e9001c2c02410310220280c0c1c40589000c88071142c50800303e91949030454080403911103030300c0385d030052580d05000c0041400b02c00c01c5500303000b11400000b03665120807042c14010310281d003140100030f0000441400703121001070172108441030314440b103c0c907560f0b0101011481c0038904150001c5a1f035010070042200741010282e030b554201d890001800001c1c5150b407071000c4419200442e07460394410911000b10341c2070246c44400c41c0704030010f00c01410000001400303d0803941c4961402a6580f5105a61030590f0700c2c4221208003800080c405d2005a4054020030b071b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 415796232 1250 415794982 415795001
    0x90405070e010f02010b01090308070809091608060f0a0608101a090406050d080403020603090111070b060f180c0d090507060f0908060606070f02040219020706030f20070c0f0306 78
    0xfaa108080034101c0f84140104d880c00300c07044c0e4641300d065140d81e85040083d0404003007143c080d81c0c113000c0e510160700e42c1d592441c0710f1b003001c95a1b100713080202c0d0713000f90000e0000b424060290000e003141d44000e8803141450307800c03a151440d103401c06540e076145c955402d10240d000683c010300c60803a0081d103491010007420485004682c1007100716515003c0103501c450b0410010104d00040c08100007601e418400303154018843c000105420840c0003104500b540b015900315a404005414400d941c00c01d00d031079003c03d40e4140c8200c40701600403203129180f480700505007030000000003103003071840d8142d07000030038a150f004e0202d842c81a19090003401800440345001d000950031100001d0308640000c3d103a0203210040c12003460007005484000c00b00103003220698005800700310340121200518050300300d5111320342c040c26500b0304022000741a1018a10100462424000401c1c0920240c5076280d010310076580c40c250350790b201c524094080e06840e900c1650f215100c81381c00024000190804500d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 415797482 1250 415796232 415796237
    0xe0f0c07330b0d0c031e1707120201020a0206060910050a0e01090c1d19051305060907020a0b01150c0b0a0e0c060426010e0f03070b06240f090405070e01 67
    0x4030700018801030303090f4072501400c0d030503800d2010400f0581c02141c0c28440c40224071030039580180742e00c40b002c402c0200d422910700309100185030002d00110300301e001c1070074609100a502d0080230b01c00095980d8000b500030b504c03544495000c51b00080404a2540051030f000d42100c0d101a50f542086d4201c2509203e100c080c80d00302800e480082d4420300d401c03a1001021500084400102028410100230310780c58440c10050003503004c506517494401c100d032151001d6070080f8041c40c00b0b1042c0072004001912010541d0b22101003c800600c0380d0142c1c07415100b0240b0b230344c415041c4522044a40034507000025060041c0401030007007800e425005203040ea031801c01100d81021031102840110321032441904244500d803901100c0c00e445694085540405200003ca0420381b00c900903414500d00818010050b40002070010030005081c1003164060f4085611040a41541e00605006070b04081484590440020103030042c0100c01c06a400a107400f4004008501d041d22010744295440000d8501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 415798732 1250 415797482 415797491
    0x60301240e18060406020c07090e010504150e0a02060c031303050f060c18040b011103040f051c020303070213090f08041d0105011b080c03030408130e0f0c0733 70
    0x452032411940d803105600b0440c0200348030f0f030b2907440ea08029080800e40880302c0c0209440001d43c40c0140c0945521000d6030400090345041a1505580450409100a04003800d044120790300038408612408030320380580750140d40e20085c5030407906600c9440180010000c5946001c8103005d00018909400d0900d10b04441085d1240d0500c078400b409810300305400030010040c81c42460505410504403101c042c100750290640d0b005c0d04500b16046a00942c003880807604041201e840c021440911034002d02070740349104500d6401081e00ea00c42c0d0640a0b000751070a50f40c1402c40308850b40414a15a040451046850310700d1400143c0e0f81d10510954128000103640c181c859aa030050440c12900161900610070741680d10790401c0028562081d070b09803c041c85481401401440294880c1e441054683d03598010030901d0031801050350840482c401125080001c04128484c1280c2c0101083c442652105d0346490300c010707440810008000804403503800c0040130828030728541141c00b84490b080c407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 415799982 1250 415798732 415798741
    0x506010f050f0d1d0d050c101b08040c1508070e060a09060e060705120408070b03090309040902040b06070515160206041203020906040807081b09060405060301240e 72
    0x158140202401c40180c00300400c0034207200c1c1a540c1c03004c8606180348280354210200840081d007480301690420000c03510005598080c43c0041c00850118113401204000101c4c03000b03400100d0b1440401e60720700740304004001c00c06000c4015001c8006103200e6203604110503041c1c100900c1c810058406002264025110425518100c070a5661013062130b5580c10925280c580c044034400d00c03000304035420040401807000814010b200c105910301e40e0014280c0d440c2e103020111454034040340d0000e0542c43d01481881142500442141c00803802141c000c94402442e000060013000c040301d45a900c210001442010005c0101c1c0d11441c84618500000b600e0f07848444112440c84900da05100682101b400100080c17845142c0d0345500c48203150040c102803040f00480c0c1d01c0d51280c1c21959840e48503040030001d60304100069481c2860184204a11031b6005012546032000504143d203d2501c80c0001411510254441050307150417286240d43c803150448c3c00f00510145001c1e001c0c050340c8850004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 415801232 1250 415799982 415799987
    0x120311070605390a03080f0c0301080709150f0603050a110406021002031e04030206011e050609062d0904050a0209010503060d0f050303010b0a02010c1107090f06030609060506010f 79
    0xa541e24600950800c03c5412140720400c044120300d143c00c0349014682004100e0410100f0400d0074080c030944416149007051031b442d1000110040c0b4a40101c00d0400c01405544000303c0e1640071502060400314000c00c0c250307840e08140360180c00a5220010700030300003c225a254119074001e03550382d0f01c10801101c800304054010302c102d00a01c400360780010400d444240072980115400101c0881030080c4110140b0811818501603a040c4e0041c2d00c4100140001d03624000703d02802130a043c03540c003403107240c05c01140d810300074600348510a0501003a00380d13070140101003901040080e4010b551ba00d9004c010721900540110000a000d80d150000041006910340b0803180410016120141141c0da003800700010702446881c222074011a078001840003400c1000518003074059824085c0e254182c01d00000e00f1a11240000400c1045072010031600e50000b081c08415268900d0000c10350020446030000903224540c801800a85062030740d1003801240c0c2d004a00844090740c40d20400064203804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 415802482 1250 415801232 415801237
    0x1506070c1716060e011809021b0610050609120601060f11030304021309020a0f0b03250906180b16020f030d091401210504121112030907120311070605 66
    0x400c18001c482c0070003803055501510100404034414504251126038100500000c0075280d8001540c4680110f0030210b51441b420382100c09001650007000c5603d00040015400320041c0706040c0241c000041d0300796603841e900071049202008800320f82c850350303403490000c0042c214901c184000074100700d900d000286010080300c0c00795800401d00501c684401410800500c1e00600880e03121701c140c0310002d000c806180d2484020142440202e071246010485a4481c08a2a035000c40d1180c0da02c99888030360740c000b44040c083d2007491400f48425800c041d031403c080000e50700500c0360b42e400443c4032881c65281030700c0884403a10958030460041d1030b45c018540e89404c0c0f60680c00114204e80c07824021a0540b001c0070210f800c0501d030010300d42d03074500c20501d0618405c48041c640301d80c495042000340300c1d103107140820015a51030140040c4950703032075440d140c1480c1590313440c3c15800000800d9901400300409c501900200c3e04600d155405490090306000140500c56024012402c0c0083d2040c0103205 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 415803732 1250 415802482 415802503
    0x4030f05040609150917010501060801050a0302130905030c0106030822231c03120e06070509060705010b0603010e0f010801090f151d0d0201060e090a0b1506070c17 72
    0x42c0e02c3c0310340d41810403050301c420042c0455800c01203002070000e0007201e6900000d039626030480002640d541003030070041c81810305030807442c001c282c00081000142c895105c00d140c00e00400702c00040181d80f9107041c40c118400c000c0711034201d6017844000f0080c44000c500800604070190400070007848007115100504405125100045e18005090300c0943d942804000301c00d00d00401961185c02c0c44001402541741c01c18003900011800c00c140354140f0220712038584a038031168000c00d03161400d8100140b4510800d0b44041c05610049084003c0010075001020000720043c03007142c61750303150011001120400c981d80001c0d404004c0000620350030610a00300c2c0142c015102404103540394861201d40300724800404141c80c6e450749850501c0c2800c595440f118030b8880041c00c0c5a100e082002070a5420035000500e81542e014107003c41c59100052850340d083c1c2c00b60400050390794407110345861650090102d130f0041e600145580400c803400003c84241d6044501c0c2c100c241c054041c520395500d18043c0e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 415804982 1250 415803732 415803737
    0x1a0901080d050a121506180302060a180e010603050702190203030403020411090d1110020303151507080f04061b0b24030106030f0314130b0d0b120604030f050406 71
    0x203040780c000e00c1100245030300070443c144001e500440300700c45821100b04500c105118440d80205101d21584000300c040ca480c1d46000d240e80480c1581c0019800d03201d000781c01d0b010301201c00b0380b054501c0707648802c040c010040011990324540e50750300301602901c002c48010006010f070100545030442c0707204170741c041d260700680207508203402e41d400d1200070300305840c1d1400c10340c05c18441c002c090360315840c3c1d07544200d1041050300030801580007800030300b0300d41c0b841d0482950005d204100300c0d101a11140e071784c084421260b0860451551070018890b20820300007501e0781e480050f40e400f0109a5030010b0046508641d545140120896005100150a44801080c4145c0007020520030a88000c0d0003c11511034503e5006051002c0f0020342142c219074000c4070f05c92409a003c40030705801c00010651b113101900414580203188400ea4444512801003102902d0086400600107481d6400401d00c46c4d03004c1d00e5500b940d51400385190b0b4030b0200300d508030b002620030244251802d110308240c5048500320f4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 415806232 1250 415804982 415804993
    0x40509010b271c030e0102100b130b0616080301150903030c0204050943052b0206030901050901060605180f0315040c0f080a0206030c1602040f1a090108 67
    0x10400c0b0802c1400d805003103030340602034003800c1541020001c42c83e0306092007a03d5082000300f0b0480003a0400d07562040c01a1891703d460005442038403090a2060000f40c0c100d000940e401103840010400c0c041c0030701d00041c8103d8001e00c00100000c550003036050385ca201203085404241c1782130480b81984030740802030000d240c494022006003425040303690010410000c0d40e00b00400350405854040d1025407054151300c1e12032803070b40142501e0300113030509502c26107000001420100072405511012549000304680710072070b80400100808030703007032044d4001c3c04103540e81801e054050203060103039140c81c410b5181000010710180114211844444d800701a0843c5028240800c00c00c03510340c04405415001d9a0302c8503100f8207062074210b202d81d04c44d003002c50382c66040056075190521980c005070150390011000501590321401944d51081044d80120356401d00d0359036422450302e00e900c0003508541410046800c64005c0d81004001c010042031000da19849282005a0514284117850440c3c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 415807482 1250 415806232 415806277
    0xf0c0a03090909240609021917090d20010c0c12090f05100c050303180f07080a0803060102010213060e04270303020f070f0309050f0103090c140411030408040509010b 73
    0x284030921213201c1c1008400511180d480e200d0b0401c0e0f0303000c0403182c60000380e541c507202e2003190485d030a0f00c9404810303049120185403036041d484d5500c2051440707105201a140c0070034030f40d003402c91846c6400204080240700d40040404058103d000041003241c114011000a6449a110725440812036941e030804485462404040c0100382c1a07c17000d407400c1018a02004010640820066014441c4d5035816040c030248424268100140721043c00003070780005d403042003880f50010301040f14603040f1408076521344038440183e00901c101c070351543c1030000c0c0080000720190003100c003048440c8140c40030700242e84452a90460032016146600403010230952100c00b0a1084d4081c110210710f060000e440c1c0030068903002e007155004841100003612b0030ba01800181050310f0041c42402c030070708043c02488440d40d1210068030844c007602d000048a04415039055547e6004807a0400e0f01c0765109580c1e0400b4201080b0b00c0e80140981409540000c000150744400d078411220000e008a4001c51620749 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 415808732 1250 415807482 415807523
    0xf0206010b180301091b150806040b010318050f06070e0d080702041805030901020714090a091104060f08190b0c07110913110f150f0f0c0a03090909 65
    0x69961612100c000c00b0b51500c0d1901c007449016442c81c0161041e5520180c626407a00360142543c101d4000d0700c5c0da208a915035690010011030304083c0072140481c41000920040700240b920345018081700504c00b0400c8184030007c250070400321500700c01e43d4010794402d0740641300400e28044041d080f20f404100c0030081100c210180c13402502c028404101092028aa00301d204010141a1400d8200140003180c0e50780401c0803500403c4600504032003014840300040c1d8082005200720601920703003ca44e003c1004400a0402000004000b00b04042c0c45004030005618680604c21840c401d00b1034490307111180f0500c20071081c0d88410b41c40000c1e5981181c1c4800c43d04002012620565a8520000d0035540c911810748160280350311240311a00740c1c1024403056000b0306969010f44501122107140f0307210300c140d40030303030543d041d2030545e40d4003000755105864802c500c001d442400c0d000c0f4420823030031070100b008406a402035903020b65803522580200201c41c400c2c10010028560300350300c4000d604 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 415809982 1250 415808732 415808737
    0x90e10110a14090603010b0c190312020304020102010b04050a060617060904032a03080406140f16020a050d08041208010807120204091202030310081605092505070b070f0206010b 78
    0x2900b07040d8a60802c0e400c1804503030a5002a08005481c1001080c01115a02d0400501c200500c1d10101d8008027401510301418580280c410101c48540002c0081c0075a4000d4010084c0c44201820803c03503498985100d600400403030040900040004d0f03070090b0b80034140d840042c02800c0080844055031910384d0280c41c40d14060b01d1022400d040c140b050780a41d0b41c0e40b40c0315107070280291200101c61500b454408103c4d80310381c040300c551050080c144140c1c1d4a01203005540420440d808000a80322841c1c10f91400b129250b00400f83d110303c500e1929031030751005c0c150380540d203e8000d055102518110685001009003c6d000c0654014001040450511503903451100d00117400010100c178542c035040482c40c0c042007020096400002413101c1c048440440303800801c1c20001030310b91408040c4401d4003101c80761186600c541d00002c0411039144840d004a0f0094000c0d0100c213880c8114910302614a40021100741c41724220540091a028020400c600800c60302e5800f4040742da00b0490002c6658 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 415811232 1250 415809982 415810007
    0x6040b01020a0f2102030a0c0215040f080a0507050d1104091103060a05071805090a0b0105040b0706090204051e0403230a030b12010b060a030b0303090901090e10110a 73
    0x103101d010091004030361001d40c4248403501130307142c0b81c0c03030076620b0051006519148034002c0110b520030406d074000294000340100e071582c3d04030360b07480b042184020802c9460046401c46e000040d8800d00000c0e044800180b050b541610603802e68414980d10410000c600c00c43c3d4501a003030102c0c02c0c1c603204451400d1390001c0801446902001540440100071074a020002c40d061406995130710180011260000c80c00c032003018491040c100d119003000049444000c010701142002c03500c844000d1441d80c0250f00350703000f50603413507071441d2200c6160801c07001501410801740c1c02186000c0c040740c001e0903100080c40080240b512012565151a030f8100d9034401c40d85544904100340720036005001d00c50ba4010184c40f8029039000c42d020b00104200000f0001d1211004c2d4035070f1404981481603155001984d0326200942000106c41c0c0c0d13180003080c21341c031171400c0c036a50040000c800400e40040c1a07014039541c070159001c41e0040d030110305544044034180300e03c5100c17841c2c051040d1a50740340702d15100c4824 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 415812482 1250 415811232 415811237
    0x9010209011e02071703030601021b0a03030311070f0305070614240102010e010e0d080108070305060105061b072304060b0319060302040603031e0e01050a050f0c2a04050f06040b01 79
    0x1811390b908607598151805c10301c5070741c4035040002030203000d60341007020010401d2907a07011007180030000002840e14480d440700a05141c0c40e070001182c55101d42d02aa03c4190b04024030040c04071040c0f5005100c0d034002001120380d246007110080d08110f51a01e6640301d140b01155844501103003030400307010b903034482d40240e04664950021240c920341c2030040c1080507100c0e030002c11019080000c0078244d00016002403041d58052681000072502c00a900d90460360306641407590703510f80441c0c0c1c0401f108560901c02d00f07441016800600382c40c1503149800366004d03414034080d10180780c9007008140c171054414440301080c180082800c00c17100030744a0025043d42c88000414544c3d036030100307055034103541c810303030104510300c61248400075080c1014145a9031031600785c041400684c000307003090140a201100f0000c0100b44070909100341e0089690401c94070007110034a5040c04840d00402c0301100c2c41c0340c004400c0021484031030405004450250050f940f503241e040d48c5400a2100428940010030304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 415813732 1250 415812482 415812493
    0xe04050c0406030b010521030403020f011407080d05220b220c03140a0308010b0901030204081b0307050102030403030c02040e1603060902030105100b0703082a1209010209011e02 78
    0x306a603951251070001d44c072805110b0015032501c0100300514203141900c07050980d6501405610181c0401260140c80d0704480707041841502c000100e070f66840340303030703121104941c005044014890704502400c26000400401e000a40d40d00140c03080c58050900403200042907181507030000345410b01071680c442d2030040880e024030842d0307809402079802ca070002c0d47d046040010920501810364084000804074000900e0010070a650041140f5014440d08040700030111b000788132030384242c049034001c0c040c290444440b803080c19041c241004032014440d00c288101038002540b5400401690101c81d019195003480300780030707020305c0081c152007502450140039041c2055028500c00840c031001d50301a20340020750a04600c1850b0071110302030110300001c0f80448042080b841444119280b01d541031a0851443e214640260003414038010705407404d0101d80b00120b0100210030290034039072182d03415048240c0f50000ca90b0b08130300c0340241107070000e0f44144441d0021803092030403c803030000b540304840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 415814982 1250 415813732 415813753
    0x1805060109111935010e010501050309060c09010e0402031501080615090d020619020a0c1208161406070e0307140a1a1903060816060816090510030501150809070e0405 73
    0xe02440c000c142a0844c030340d601c00140503403e03000180a0260078203007800d600e0740c104190346607902c034002441204502030000d004862a441844a04c200c0c400c083d10948d101d08181400c0074800014000c558001000d072000a4420300d03102040d1580c881402030301d145040801c009104005a90380c0b411b83c2c001400f040190140c10540000001802660b0702030041c0e22440d203812102582d00781d1102c00403581401002e40400c208a0486080c180c50848803090100300c4d00c2c1000b9001c10101e020101401030130708100215401c40340f41e0303014100840648641d90303200c10149000c000f0b111030b81c80e000001c4100911503583c90083c400c07004504108101c1c00c18075641403400001c840c0a080c500060780350381080102d02c6003048074401c0c043e40769070442d080ca0b04006004094940091000b100005050794101483d40140b030130310003400e400741c10400a4079142001034081c00d803c1c414400710380400300b42025031510031804203015010100c0600001c41c40c240c91605c00c1180a042560240500507161 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 415816232 1250 415814982 415815047
    0xb06030a03050a0c0c18020903060109020f040b03070c05010504060b1201091e0503041a0711010c02090a051503010207080309060f07050f1804050403030f060503070b040e040618050601091119 84
    0x140340598840101688d20f14408091508010040e40549205070051002d60069400a025030b019a84c030410b003d91a0303030f9200012601c02da071600c00502694a490b0a02090242c150440300301c07000159840d400001d507800c205802c880c030448001c0d107101407074645944290b071807a0043c448a8021411641003580b1307130542d080b4034448920514084000090203004000c210541542c6852090801807a50000c58002c111030354070003010740e401a5070768400114225114076680c0001c00c40a40219140c28491402d03c0241c1d100355005003440c4580c20029028203031500701b4620a138129611b160a242e4142002d6660390012162244e80100c20813410040d40c40d1407003180d1055001e56400f0488844a0300390303104445071508428002c0d08058410b000705860b1800f00c80444a0300d2a41c42c00580c0c85041076002010850003081a010049000000340100001d266050718003d10b02008880d010300c4030702c2114807a00135101c14801c401c8500741e8007240a511140044c4170584104446c0e8810300040c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 415817482 1250 415816232 415816259
    0x3040e150909010504030210020f0313020301020c07181524050405180621070b07020402090612010305060609071202090a1809050f060108030f0a05040e10030b06030a03050a0c0c 78
    0x2c90300700c0e9581d50800c82859030400401c454403207019811440d2100c20b41c400d8085110003800c04001e042a112400110b490035811541d0303c403001026140135a84440140500c40a00e02100c200c4508040035010b1148003000041c088030054800ca09a481112400c2c11480c5458150282402818000040e40d61212000425503030b069007003031186860020100210300c807204043d01d240381202c5510420b40c11000440c2c03070580e42d002d9051030700c035122440007130040e100e030082d40ca8100c4404500c0303400f1110010703c918166031086e401e070385095460105000440700222072040009001c40310001c45645d099000304201640900107154060300e9000a14510341a8042d254205550b80511000d1100522004040031074420103440d05502d800400d075035030301802c030700700000400010340300b40018054000c032002412460502e520310b2030010500e4450400c90300c8181c1e500c80030080003c01503e00415914445545921640e0500c680c452040b03d58a80c84181100c0003080e10701c2c04950300c04038004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 415818732 1250 415817482 415817491
    0x307020d14030a0e1806210304030c0f031205210c091806100306050307030210021609060e0702062415072001020604200402070f03030b030d1103040e1509 68
    0x8440030100701160a000c404089103903040314881d82c417024000b1903940c20504034100103285a02d0800003c20403101400d504c240e0b4801451104071850024103505000c08103800c4a00030240c00109801c0400305072001c2c424840e440c0300003034122410f9140e600303502c07403a2904a400080d01505114007080482c140b002c1025100842500901c20000c2c280360039074030078940c000f042c58148045458103021996940940c040244201c882d84030f4000454820840d170241c103012646400c01071039a688940c00204141e010701d42c00c84034010001108140006000d90140501101141e980c807440b000e0303409011419218954031000d0400001d4280d00010041e02130325004003107500c19000f070314034081c0a5840da11001415500450300304400304840700b483e046243d40851000c061038842000040091041c400003c0c42601d84103140428140e041e40400f502071400d4040b14002a0160010751f520b1364409098030241d4020001844031030b1103214100e8201000c80015171010061100081c00c4445c100c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 415819982 1250 415818732 415818737
    0xb0a1b0f020f0d1104020309010b0d35180604090c050c06010603050c220f03051609020f0a0c110d1b090c0806120703020604082a030307020d14030a 65
    0xc29110640c038080041d049000801c076610b404a000030f070707191030824000341c1401c0c1c4210b50100005002207000e4018200c1020700404a4004c10180d00e800780310081e01000302c5d010f51074540c28180c10004501c43c0d005000c03500341d408908102c085669408001000b000498108a050100284402041c050795407000b0040c0c07502a100c842c0c1d40007080c07038520140d21000c205410001400212541750045039543c02d000d008006810100d40800c540445103076015158211b0203072800424000c000c81d02c034440600040300000203942d10030f41c0e00103038002e00c1000030784810200000103403a0301132041510828880c2038004c640c00d80d8200021480004c0349011b45803d040601c100c0c00320315203c0c0c40b100280c060b5a408005650944500801030b00c001000c2600072001502104441c110400c0700c007000319802007035556a42d46505041c1d0300e4000450841c1c48040c030301a013035a0240c8078001c40d80e00800d00035004501b4032510341c00700581d00810b2682030760b00034030100e21600d0160041c0020203000300c540c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 415821232 1250 415819982 415820003
    0xb0406021e0601120b04290601020c04050f0c180d0c080607030504150e150420060c0a06021c0608030901090509130b0c0d0f0c08010f08070b0a1b 64
    0xc041503aa00c50401e1408641d50b0030240040c884248494070500c9580c2c2c102440386820796803803800e8020b0000140c0300c408030b0a15041c07264810111158038900c06e88003039081e2906240c900c028071081ea40162152015030880da0002040000c40d000070f00381100d241d6030301c0d9480000c6040822841d04c0c10031001c2d0391800c02c18206000d588800c001250f0001038502d410005840c013522009041035a01140c5980c1544880c111807415004000400e0490100500d4509a05003032600a031103011900380c010b0300c0007600c19495410316003c1c1c180d6032032400c4a8081c0c9140902c81d540d0700700a51020390b51030010686502480085991781c80b841d0040c02d5800b00940c0c0d41ea0003080017404107259603024502c00c0303990f4820041c0380040304a1410344598081071080d01600c81c5414200300e8050015864911031402c2014001406c95800120342c92195407a9408030f6600d482908101030403c0c0625111580480c20070400700007c2d070010720140f2114039080e105000468a0000034015002c019518074110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 415822482 1250 415821232 415821253
    0x1c0515090724110f03030112030302040305010203180c27071b0b040b0a020a0f03090c0b0d0501030c0501020a1211030d0f0203180118020d020f04020f0c0d081510090b040602 76
    0x4402d540188001000611a0071300341c0120955a101c14003441455018041c0c1d410201802601528007a503802002551a8603150100882d00b0841e03d42c4040903100c0d40c21090034900f03002908808c41c1c8101076141301d14081110340d030303020400003810500401c40b54020199042c240c82a11414452144040d40c00504041c10030105000000e0100c1c03038290300c1041902d01464200300f40c1d15482c000340c2030201d0f11300a1420442c01c001c01d650300004d19140e002911a0020540740d1049058903c2015407902894803603004a82d22a070646000705001200c040b0002003a0060852802581044045034940031600c050641641d040c02c0030044007640100c184040070034012120040c008500c00204410800c042300740700118851900640540d005032401c0042d922461001c2d130308a03801800075540d450b004098010b0550002d0040074440c010301f031a0b484110f10492516019102c03550b40d031000c0000340c038100a521000b20564000380143e040d00082c8100c20710b009800144450f80140c1740d044503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 415823732 1250 415822482 415822487
    0x1009051e220b03070e06010f110105010b070b15010813080403060f09020916020706030c2003040303080a1b03020c01022208300c030705070f051c0515090724 69
    0xb100200c501c240c1010b041444410010f00755a903020313030700b440e00c0460803008400c29182008102d00c11201c1d13500b05000450b85071204401800b41c0c52203a90801c0c8140d07200701ea040e0b010741440341800e0000c0c46103400b00c4c00301e02e207600e00c01d076100303000d89449131402d6030781d070707034407001c44a000f112240b085840f0542c40d403c0d4684284266845110400700540c51b9074141002511400e26001e00024180c3d1000300710390b240c1c41413170f0048050502040400c400e4000080582c0e49410074401100020401c038005254000240030341d090f0085494403034480300450320801e9001e0341050f104400291350034405100d00324072001000002c102400c1d015200d950406210600701598080e24855081910944154103d040b0400001da0368200641c680c0320420001140d09502c12440054100d116940001c0303244450100d098040300c80483d11400300b03801204413002c15030b1000401410343d41016010380d00d0101400c0f01550b1082400003902c0002c0d0711184031003c4403100c011200a40c0d000114692100394 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 415824982 1250 415823732 415823741
    0x301140a0b1c0509030c430e01050111100b0105071a0402010e03010b0603013003030212070c03050d0c090504110919080a120302120c0a09051009051e22 67
    0x10b005015506d4521081041c0740e5940c21101011448651143d4820717a6581180804803a0342820210040440100001001d803520a01683c01641d402d40000507540d800340c6812000400e032000030b40084804c0304a134400070a03000010a06001c410410070740020100341c44290800500b808405941c00d06000041400c1418030340326000341e1400e00041003c0c0e41e084180c038116411050181d051918903ea444104404000c010303031a020300c110168105905500a842c480b10744400340070190f9030f014000c403640e00c008140580400d40420001d105400725811462075014941020408e490340d40f004241281c03c0c943c6070180c141c0000c203010850f407034140316020b42e034a0a190700c0d40100707003002d0007140c80340c582c80d000038070780846107420b01102802601030715120601c88002a20300c1c80c01904901c4540d2041152000007140c0c4040440d003850104040940c50b0550b07541e01203441c5c00c01c4180000c45030880c0003400514010546940203130340e0401c8841c174003a00301040c100049045000c01080d02c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 415826232 1250 415824982 415824991
    0x103150c02030a09030209090a020616031b0209040b0604110d0603050c0f0f060a0c0b1302030f1b1201112101090204030201020c011b050601080d0906140301140a0b1c05 74
    0x1504104400d00c803ea5000040f0b1081d0307501103a450400c1d46840f15814034141001900a401040105c0c03180d07100303114076500da0415802610740030050041d40d000c04101c07822804009501c0040c02000c80c000c142005081384d8058405403002581c4414540141425005414000340f02074403514203004021050108400007a4151110703001e0715131130740015070802400d54045004950101c0c4644041d8420b10040000a0304280b00810b903041400c40140d5a0821200c02e0b4024807505155241c1c400f80040c010300c0440141482c800052034103010050045e1498020b840a503485024000102e00c034440200303980b81e0310450f03121070031041301840d000941050340035245440c41800204007503600030445150a070400d10300000c0c020720040415005205410b0068824491280049001180020003020a2006071101048242c0c1c03071004840e884601c000c030400e5503005100402440c0c0081c128190300580042c49482129141d03400011183c000658040e065680f1801102c07004040c2d10030103030130 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 415827338 1106 415826232 415826237
    0x9041e051606050c070320030f0c09060105040b03060d06110310080f0a260c060907150f080609100f0902070606051020150103150c 58
    0x12014a02101d440c180c800303410204055000d40103443c09642c0280c010103501c0d0851340c403074040c0c881c0c01c91440c0070803040540c80c6400c1e640034013604e851039034032030010409107080f1000c0003d5840d02401090601400f00000d104801d503000440b80d1110082c0c2d05484241c4103072a2400c01030420781000c2150a02c08014404200c40300c0032254100c0301d414044030a20450304241d0b580341c1d800d0f04002010118410040480e0603204c806031803841e813483c0f032040c5c10526070107075440c180041240d26110359000310505101c100282d9000300351801051034000840c14100344050300c0c030030b0060290341c850301c0c1c0440060080d00c0081c10b0382d000f40034a018010b41e0181e807048610080d400181c001c031003490034050089030078103107005d0340d0304d81c1c50959841c20502090303070b070b028070004050110f03200050140702c08000c0102110031085000318480e014440c1307580f1204103000d00716201c05407080304 = true := by decide +kernel

theorem cover : BRFrame.Cov 415647482 415827338 := by
  have h0 := BRFrame.cov_init 415647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 415647482 ≤ n) (h2 : n < 415827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
