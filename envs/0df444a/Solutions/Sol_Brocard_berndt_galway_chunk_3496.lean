-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3496
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:49:30.734981+00:00
-- url     : https://prove2.me/submissions/77bfef4f-3b61-4d2f-a31c-8095a47f7be2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 628597122 ≤ n < 628776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 628598372 1250 628597122 628597133
    0x62304110304020f0918030c0708060108010c0f0c230109050c040e2802060c1e01060509061c21080c070203060c030403020f01050109060303030b01080c03180705040606080708070206040b04 83
    0x100680546a8070402812001030350346e061001d41005414980104481407520700c916140c00c1c01a8014002e60b458440c00003400c07036224400a4000c10316060007205558030b49090b041c0b03030104e80256144040c030300c14030001004040d08407080050140d4121103021585208120403a0803501c6921043d0307000d40ea4140c0c8440241111301c409007a0203520046070800350b00801c240340d0188900e011103030480c00585004a03d000c508600c500306501c000c01c0520300b8a004078060b444040c02c110f00c503801850303140022644540500c552035500020001070300d20780b000c07600c130b0128008403d0000704d210000040e04400e0550161480d154008005180f252114400f00b000c680c0007400039004c50040f14402c03041e0b80b0302400b84074001c01c003080d000911030345107041c000c0468080f1508141085a40303018041d220141c9401d0303e410400103480c0401070b00041d22a60310f80102d03584440c0c0c0141c24030780001002030300140f01501c10382094982510550b6850012070720b41031700b107800404030300b034000c0810040355 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 628599622 1250 628598372 628598389
    0x9012306091801030c0e040f23070602010b0a1a09010c0812010f03120503090c010e040906060b031012080a0503130501150f090b0901050f04062304110304020f 70
    0x10406080c00d454a5000360108001c041c1000e54000b19101c000010020066040048001424100c07046141818071b50344000f50088942d0019100031044003c100028002c0c0051420145001c01110015a0303070b40400303400b030072112800904c01d2103600000502c448420b488005a00540400c4c1464000100c005503042174040700c054440c1041030200c000240a04c4401a029000303003003015006c60700d1443e10113001c04070411000d0400c1428400d0140c45034002480e808003210900700810314400c80c0d004100140b0b005c440c05052941003140000c0d4002c0940700460152004142e902e10064444c04091211a030404000b400b0107020482e0005517031040000c0c41c5c1100054214944220594440c2800d54646145201c007039510000e0802840c422100c4150081c0404001401300c40d1900000442c040b105205442c0609a41222401f0556456109501900d001152103000c0e9840040140d03030080301002c180d00542c0780a0b4406200500c21045d01d11465006180051416000c4148515003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 628600872 1250 628599622 628599689
    0x10e1309060b012d0c14011a01030b210c130f11040302180c090a03081804062d031e1514180109051e011a060f0307050c071409060901 59
    0x2117049841c000040022205008450f40e103400070606159498240c482118581074003410305140c10f035a12440e4803104030750000949050300d0400d500340254003060402010347c0f5588e5100030000d104143d000040e130f001c5060f55070486401c0000740c5030f50081c1c5103a84031305c0c00044d45c00320006e521030303c042c5c0290800d01da220360b1a28506082c500c020b0041052003000e60422655201c0c007140404024010f20464510801c044806100b0f0302e2030a06481c0200e50545490145000790100b40640f0301c100310301d00b000842c1d101103441c2850b80c590340e4071000e22010100c102c529075681c04c0501c55440082c0110444098034840a00c15034440380f559070352414545803180b86554885c100840440c0c0c091202459046c9407003009000c140b02629140e00f1107219140082151a0408620711241c4411081c1d8241c01d080200d50743d52622076071826951401483e820701c200d403082c21000b00c0d000b0b0f910800720800c02806d0340d420011303071521010842400800d0084911050241c040000300185428110444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 628602122 1250 628600872 628600877
    0xc131a0c07050d2d020310090501051e070c0204090c0e27120703020f0f0c1311030109180c06020a12081501050f210f060901080604020906010e1309060b012d 69
    0x30203115170201e828612500c804079820743d40e0305a2241840401c0c003581da03104440415100070000a0904d49011603000341285007004103001340310702103407520750003900421740105d042100b0954403021407840c548121140d0102c211803805100d118828500009088041c8002521544c01450000132580c0c00a8100b98114410600c0103403000009001c2c02d058500c140001c1d0542482c01400d11101041088022000616108581c1c1c0d91801c0742054a0540d4088035001c54100c40b52440d581e00311900880150400304a00d500003030381c135000241d0568942c41103260300284c440400040d101c1080803102c401d40c00d250610304000301d40c03044004003c0341000711400c03410000d45250042c80071981d010300c8101c1c028a0380c14890b100340650719250b4410411a250790144d8104902241c0b69940640000e00031042c44021884070b0380114459030300900e0107040c26800c2c0540d2080310b00a01650001601c01c1d0340381c500080c1071540301c0c09030101d0720030800000390b840045010307108840140780c004038400c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 628603372 1250 628602122 628602203
    0x150909050c0d020d050603070f060c08070303020f030c0a3903180807030215070c030611040e090c09061002030f03092817070b0c131a0c07050d 63
    0x40080b42c4007030092844290b0b800181841d0520505282000d240c210340d0011200380020000c9640c0318080038041341c0d101080b40e449440c5450180e010780038481c4540e08010001c0100318803142000f014041a07109561038078403203600d07200903800f00c1032604c00d200c600040001004241b00c001e01d07604e09815100c0d140c1310514405003886100c0350002600300740c603d40c102c1c07581007096107014061200000032400c0414a48a00d540c0c501903845910300c80100000e440342020b0705113801c51001e0380c00414491408011516151b10016161821040740034420801c18001c90040d06013000b07940340000399500118988040341842c0940313078000514030501403103203624a011020480050840604400e401034600c00098900500640080116240d8000062110074042000300220390340001d65002010390792080025240c00c1c03044680c1124403902c0030000d99517000300342c08000f40440d0020009031207100b9180c000b00240440300d142c0c060001301d114202c40710841040358940950940c00d080044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 628604622 1250 628603372 628603387
    0xa17070c1110140c160e1501180f0905011806050f0d050a170a090b0903061b0c1e010b01080f0c091f2a1a06041103010b13150909050c 59
    0xd4544c8001d8240ca2a50040407940b1040c85035108403070050311440303158186501e01410014004070842c052a81080b0380440407071402a400326148024100300d02c00312241c142c81d8488040502020b1080030300c0782924214901142d00c4911428040d2500103040d05030b40308151040008580101006035081e020381703600703603000500d001d4401500750300064005032141d4007801c000d800211158080152035004104148075a540420f52542c4140000c6100d00c0c400e4140300c02000f02e018001d07006500744664040c001c41a065030820202e0b20380c2a10007400850500d0004668100040d141c4211082002c0d010500940c43c41d00038080e400030251240c84c0001c131310501d100040000d8403a10300420440035240c403004071010910310380400b091001c903698038a1036076070090600c2c008140302413184200000c1246a91503070005942d04040068541c1c995031a00d540c402c10b9805030f02c1c003012400001000288001e45103c0c0645950080d032100d19003a0301e026031000207428003c0030038108000800924 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 628605872 1250 628604622 628604657
    0x209010303121e0504020f100c0b18060a090203100b0603040b1e07030e07090905060609070207090606030b030106060305071403070905090903071709101d03030a17070c1110 76
    0x941040c0e000c0e00000c5100d040c503005221f226100c0c2c0d03001501500d060b044502c1d103150410b05042e44148d01c503008103066139910041070180341c041c0040c040a4082c6205100070401590021000b0500880c152007490720861400402c94001107505504a8400c0c800a000700300f40a000720741c0880103000030703034500440b000380da00c40280440b00c2d41c02083d65080074100c410300130825800507144000080100781d07030039162541c0e908001041603108041903400201c070f043c424403141008145018092043d15250000680603104c3c028410b40258600f120005500e403181c002c06028030803503181c0c6c103030f0f04000c002d450b0342ca5030009056000b4005061030014007034564000c503910a0004001035501c5aa6a00d0001130300c0c16041c0c220056140d042c04240010f07a22008210050102c034100300c40c001c2e0910545404105a64181542c980008180e44480d00d820480d550703480c11030b00088600544d580081503d00554143c80070b820883c01c50103826160074030b084220790740d0140e400d003000b035050440d891 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 628607122 1250 628605872 628605911
    0xc030d0f05091504061706150d0902040b0a06050a080f10060c24020702041a01120e011d010509060702030414040b030c15040815040f0b1902040303091a07020901030312 74
    0x1060001d41c16150424501c18241b02c900c0d0170100854481d03c044100c0b03440340c011402408100141d0030f07a1140c101c011540c0715071050030b490501400d12a519565054050011b4000015013804a4056070025100442102d0024480c1d10b41c000c200349410305254040390310780361100f002c0307803001c41025142804405080400514005a90025a461500d4814002a40c6200300c5070034191601401540385aa0401c80c240001c11481000180f04280b25002501400c01c010f003c00341b010580b01e9018001106400043c4a500d485085801031344445404981d64401d6204041441440e00700450381c80c9080d40110030100002000c40f409401488000344d0140358030045024426000101000148414480703981c55401c03a441510052402d0340b10341110084ac802c0060580d80c0001c0082c08500050643d200c0b0f0041c10342c41152160785901c0c002c0e00100345070140350628183d0f021805100c0c80704c101180c80316030707002d42010816442e40c0d82c01d580711078900c01140b101030b40300c100828000c150f5594 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 628608372 1250 628607122 628607129
    0x9071407061109150a2c090a1a0108160315080d021006081501030212071205030408072c070e062209140c0a1404080604050c030d0f05091504 62
    0x10b0050b501e28a540410100f4180e040144503104000e000710f0f4422074121805448580d20b00b0700030305404004112456540c402d01c05e480e540501c0d00d0040c0070740701c1400d40c0321010f60390f00300702500c4032300d050035006444070034003107d1000b40100007202c0e030300c103052194100d12020a0b0b0051401c41464075a0b00390ba04210644014400507400062428412803031070003100f0040a070300020b040700151800f015000f41005001c0030b4081d5800700d10400880100300140d5000702007034030b800c0c00e10003028a044d5480b544a441040d4080c4076045001c10035248103003100c000c3d000070303440950400c14202c84200f45104014171440a000340b0383c81450181d241d100c0180b04071807141586d0604081e51307020041c1d5500c1c583e04007100c880e10f00800306010640c06412145c000f01d20182954682c020394001312800a0b040740007155440c00498001745001c0000341da1405140702d1420b6130120955001455591000540c450002420407414442158000c10040140c02030103000c410340d683e41100b4400b07240d03105a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 628609622 1250 628608372 628608401
    0x106031226090f01060f0f0501030b0d1a01080c011704120212030117122a10020d0609200a0e0102120a0e09090a05100b0105070506101703090907140706 67
    0xf129102c5407000380f2810025241c1003a8002080d42440f210300301c4800309024203414140d43d82100c0085a0340c0300f030807022980c2c0c0080640c804000030012090840c0342845a01c40764890701924120179030103003020800240410402c58080c0d81c49448003015a4a4105a001580140f03500d80c1080700455006501801400b1058110a145032003454500340082c0302080e0840001d00c65200098020380104903807110074039680781181c07400f040300c5062842001029041700c2c40020340c585100c41a41100c2c08403402d45000f08129001401e150020594000625000c80020481952840e000304c050044801041c8102d403003130104681b10744035031303406607507154041524907003007142c54034020800a9100e42510080e01030005565515030b6542030303003c61074904d5526140345200f40e07403082060391440c40c0c001049038020b050200d24415030f00a64000d41c10148000c4c2c02603007811000200300d501140020b420485580e45401040741d032000d6098074900d45520030003400010548a002d003410011000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 628610872 1250 628609622 628609633
    0x90e0705032d0a0c0f020109050601050907120207110a060302090f13021b0a020907020a03080415020f0d0e06060f090103141e070e0105010f0203030610050d09080318010603122609 79
    0x80e40500071104005c0e001c0110780c10312100c4000140042101811120240c40c603803450345440e002078400450014010002510204141052144002c01d414003280150340a030001c075100e91084081c1d100d8200e2140c1c00524240f103c04250603d14603410b2910300f400d00060502c00070074403040305994801d003004041e600440c03403181940340c00c491070780d0030620600003060302e60b80340c1e40d02a0013500d0040000d40b44840804025022040603011115140c03000d0f20511341da0881c80a903100107242c8541004031504c14800007441174142056640c4101e64001c20300b000680c40d558420340d2002494202112502503010956048400191010300204110006d066060f00b0403064484944050303000320b04000c3c0c20391150302619004070849401c0101a0f64a00e1a02030208003514240b04604594070380515003030010b018402c181002d10b00505a40e902c2003202110256100e00340c07041800040c0110110010400c2480c1c060b400f178150b9014942800c403e40440307001042c80d0024111208100f94024 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 628612122 1250 628610872 628610891
    0x4020f010306180204090c050306130e07030f080721050d0504060230070309120c030e15220305030a080711120a0e030a050c060f0c0105070306030201090e0705032d0a 73
    0x3070055140e802031f07a262071030940c5407440015518690340c4902402082c4e031100c400c032006406009000107103400500c1d19110500900e410282c43e44001c100390750441100940c0d5403120f40c030500a00701c86080796525810200e1558801000784006041281c03410303801c0040404078148c00b210540d5203640c0324021009040341288100000703100034429010540b404045030000303070100c107401c900c3c2e00c0203147003105120841e403030190f4504e00407021090380b103c045944039550480107030042c403009600c1e0100b40c03c000c43d0024a151003509600004080740c0051045002c0c46209032805580700e08140b9010444103002c580d59800e01c860000031000e50900040d1004850790805030f5164051016801010900344a89807643c031940001401c9110f080c000800394103030b02e010400d445039402280300802090a15120241c01410148402c80c08107641c018001100520046030034801d070b039292a118519612076a14003441d11030160030b914042514020200940c000c08641440741c0002079001405060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 628613372 1250 628612122 628612139
    0x15030b090a05040b0415090f060f0b0315180304120506012d05010f03021b0f19080406030504140d080f0121020d0f120e0a0f080604020f010306180204 66
    0x300288001071450804060000040c000c041c0e036070b445030700040c503c3c404d00d0318103031079a0241c1101100a050805007140c82c1c0e0038800b181c2d0102041550102c0100328010b4035405042e1242102c400715048005100e0018660010070300825a5070322602c001d8918040d01c85c3c19031100401c0c4d60000390341590107240140f0041488800e001c505c081c640c1140402c1c0360f42d240042c00459868000c090411510044581c0301d140280c040c0c651009100360710440c5910301c40407803517032200c0b82c40b0515960701c1100d030b071082000c540884a0703034040d030450901d900c1e041c00c10f28140c0181a000d08110b8420020812201c3d0600e424490001008060350300c1e030b85035061444901e400c001040e0084820345160045800e03800ac4801081002c41360b06680c92803100015080034400f03282880b001a00202c025810b0031031541e0b210494018504040340d4511800784c4981601c60482c03810300a8151580c4884049809071400c4490103a5100051402080040d120003400906d1080c0111880c00c054000c103044c8003010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 628614622 1250 628613372 628613389
    0x804080109032d120623090f041e0215030c03373b0f030909040209131205040501121a010810080304030b0901200d0c0915030b 56
    0x2d003080d9414000451050f84007012200b04000500c40e01d40d50801d0700990310380107800100754440e94035445011221494000208034049140309070410702c005682c01061103606401540c105441c810700c0404031030500d0306121100c10599210340008000f000842800380110b20035100c1001c030548030b0a0008030030707a1402102e02c083c2503600a95000010342140c8940001c00e0103e079850110b81c000c00034801a0340340e64480b80038401038561040d200a003d074100b0780054400b03040c404480150000800403a103034014610740c1980500341101150261130040c0700c9540046841812485aa80e0f6640d910a010310400d424000302d4004030b020019507030402c0c08906804800a801d1080207034500c1044d011040c1c90ba0f40e82c6c18840381c1400b04201070203891200f130141a4080440b079440d40c80f8104002904012a1340c00619130a0290f035900c040c6160321a0042000d00c400301509042c82c00c0240303005000700465610401161ba400051002d0415080041043c2180c0b400280c1a4507035003440440c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 628615872 1250 628614622 628614647
    0x706090807030f180302011409010909020403080301061202070209010e0702100606270305030d05090a0501060902030f0105302401080d050c0319111e0601060c11040209010309080408010903 83
    0x840f45003000541d8200c16400d003102c8c3c804087d20f60f030b88506001a600d1a05641046c0780305d40c8045000f108004141004505990103a221249100e03034103824001a07204401c0c000750840803600040004240042d01c40f074004600380140e400070301c002c0807000300f240d0740c40c0d1000b4002090707000920900320184c0c50b41c2441f01d4203080402d0001d81151901c076034911071a44413502144e91600010040c2c2c8050100b40c0c1810b9005001f480020354450202c4084c0d0030584505a0224990b0000280d074580448887c0c0761207901951124030200702c01c141c0240c0a0003c03100d005c10f00507000c500c4080c0c801060340580807003a10021208550501100ba85040c000140300390910030104610000020000260346030255011820304100d120400c0c00c58101404002c48056407055103040310504241c400b2800c076520021088640d240c0c0e87d450b00b15a0b04004034009440c0c6001040c3c0c807071580c02d10360003e00154034181004070b0b0f0107089030b440d0b1136554019030014486035546c00c4040c08142d031008046010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 628617122 1250 628615872 628615907
    0xc16060b060c06060a0b0f160c0e0106090510050702030a0611090d03031a0d0302060103170d0c02010e15070504050603090a0804030b19050f07050d2c0105010e01060c02060706090807030f 82
    0xb0900b13070340d410b03000500c80c1440308d030580d00f0b480d41c1d0101040210200c40001d88a50032105045581d2480003501580c1d040c01741d903100d118030980d500742062141e8180c0710320a40040042052007800c0c1c0328a4001c00420800e000811420442040e840d02c03a109089080d038842d65000888140c0c20402001d1f141004402600c161881e601c10342c0404d90011b4290305594001500d901c02d1951000400030704e00ca5a01e50240385820010803065a903019480a01480c00310740c29201261103012414440e0304080310710101003407043c04103204a080c2076028541c409040d0701110722008040d10b503100c0603003042d4012580001a4010000407210b40740003c030701114001010301403030608142d601c0200d0030084c0594100a030100c0c01095100558229610014a00315512051030b047d014404002c0001106c2300b09660030040001030801c143d0310018101c1e0718540d5a02d950101590030032415622a103810340301c46894526190105150200411909100b0740310384031010001c050240c00d9040b2454410074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 628618372 1250 628617122 628617127
    0x90f010b0405060a171005090f0106020d03111b0c120f030406030b040b04051521030409020a210209040c020303060d1101031517150c16060b060c06060a0b 68
    0x256a8081a10705680301200c209495941e2504221040840003842848403240c28080c40348419a000305001035400640c1e00122580c0e0b606e1902000c2d0f0001c2c03103540016130002215004076482940708a607003511544801703103000c424a40c110324220604c14000d0440d084141c04004038501542d00030803400420000c0c080d04042008895100d0240717100c1c180506448080c40c05040e905c65002c800070003c0100200039a05159014841060410300c0090013580e58046400340c100d0821035002d0380b480c580005514180c1082840300181d0000c031040024845182204099296461000d09162021040058031104d1910802c810f07502c4000600d02990010024460a5118880d4080425400c000312803103a0004000481c02402c22101e20003010b407043c5c4001c0354411200404005500014003160540c0d075012a044610750304c2030b1418040007504109001910f0b4207031a040c900c2034003440c8005041c0742d81c840451802c4c0d20020306140702c0d070015002c00c9074500d04001c140e0b0251101c1210b050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 628619622 1250 628618372 628618379
    0x181c242306010f1b12030b01050903190206120a0b03011103070f0c050705100215060f181e09031201060305011802090a1715010b072a080f030702090f01 67
    0x1000d1500240c991070402000a002da40100e014402103201107080030b112601413540d60500540c0c0700185841100005d050603810089980b040058130145c45005000c0e0088100380e403500080071001a908076000702003804092008010f001c219807250b480743e28045a0312514204041c02c54828042c2568800300500c184403000d41e0203001c0c1000961a824a612098000d0610354901007440d84100d600400725403518807801d40c04600041c510300358072480e8045469490400200495803007465400140004c010b0040036000041c1503088005041d03845c1080700120012499140201d501c010b050b4000200712103607180c01034840d0300501880c507003040a035051400315851049280c0d01860700c0b540220320320346c0c80d694642800c80144581c0c2c03030046100007405c4107030352a00f03041550344003074040c0d0381d00000300c02513480c0860301c4103940401151400162880c2421b420340e1306440c2543d611600c0d0501142c0440e04201c509012400f05000310b484800910401c402060000c1c44451070302480030040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 628620872 1250 628619622 628619681
    0x31513051c050a110f0f1e060405210c0a03050403050d080115110c040603060e07091109060d091502040807050f0a050402090315040f11010302181c24 66
    0xd4610310401d26005950031005801d00303145c4032000041c5000740c014603500700101d00c4005001d620b100c003410704400c08400700010941c1c80d48401c69020b000d540146c0c812010001d00c20201c0714256802c4603000e41000c0f982001503190403101c403411000b00300001400e0003031240810040b10104403a21b491041517040900001a4481e00048803080c0120543d000d90340610a000b5981180302c00741041004680c0c1c1c0c00c04101420107458090250702409c078010520560030300a42070340e110111160342c03401c003c4106200d09544080c074603041003a134855007540010408440ba0010b460b000d2405602c40303081031000f030b007804641d610040c03162454921007445c0b44c5070414600103d6104603401602d4140100109041071000e141340301035403d5060170003040040792600d003090a4081c000f40110101640019030032440f0b8956240c1750003100d035880010300d04d00007211030004640c0e000d00981000380341d1346605403005603041c40d180f60000101001b44a400c6803040202241000d45c5144038a401074581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 628622122 1250 628620872 628620877
    0x1b0c260604021806030703140a060606090308070b0a0207052401080705010c060c2a11040b0d12030e030a0e09070801050607121e0c0b0f01080d0509031513051c05 71
    0xf804443c149000c0051007540d401d0100d07030000c541007125001004030880340c40d503d8011240048600354942880803d0700e43c405e69100090365486800d0780c2c0750070040c0c0c5490b51010360003001d803480c194081280100141c814090201c034081c50403000842040b5480b80440582416000b104107980b0420040145a0b889414590f80c103410920000c0d071344010300d41c101d410140111031048665a5601100c1c0b101c0a071040314202030340203849002c41c440b211010002541d001c22016544002c00b0100030000c203034210705070440161541400039100d07160850050454203d416004041140c0890a040c0741c1000040c41c3e034000418944842d0300e6040400003002805034070b601528048083c01115109401402075811807031860110741c0d1140d0f40c10707500174600c4200c40e6045620a1130200860744c0b140444003014140d402e50809060b101c041c040303044074186c100418490303061003612180007903507091180c0355000b80c006500c04804c0315480d080c114941246820f000d03510f442d0740d40190f201184d10006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 628623372 1250 628622122 628622149
    0x30308190b032505030f03030a110406050711130c050c01050919230312010303030c030b010e150702060721390212060a0605040b0a03031b0c26060402 66
    0x8490207655500003500f042c69040035805104449074005980c0c00003025501c540c01c5039000740002e020160113054140035620030310020403030911100c00000c0208255041404018001090405210859406460884010780040303040082c9244204000b0301500f607101010100501e1008440d00c2c016101f01000c2001411094070a846241017a20110803001e007907176400c0440c0d8980845003095003019000b1310003100130a103012103004110f0300034054140c10070320503165441c240044101f0302110b204140085804601c00b0802000141d641d40c0241c424036000c0c400100038025004600e80d1810991b00440042c4030490b525015981d260544900307140560a19442c0b410f00c407030025038181c01c1c960300e0080d406061683c2d03070a107404002501503c104411042840350a9643c401e020440d804004603039040001c10809101080c0600020a240f1a4001c20064246d0381600c8981c0e20340005d421454402002005106105d005101e203106410700a40c0901000c0c18181d000a03c500718088 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 628624622 1250 628623372 628623403
    0x71109060d060c0216151e020712060b01030b090c070602091309030c020405100b03010e060a0f08060402031029061605070e07080103030f050c01060f030308190b03 72
    0x1000036826889041c1802541036101c2e20a01c419a0b024070b0194548989108800c00300e20060000142091058a030040521075a00c426001e60484000700801c0c6050140340000e5110f9400001110080280b9481c405030181d80d001401d03452a100050a41e40314200303840c41100c0c450140101502c2c144103d500d0541e00c003c0050365400d5210100d0b1115218a0030300001c03528241d84041455040600c84654034422101000b0a80d40c0d90001c03264030105000e4074140e54000d0005002e01180920301c940c110100170111043d05599071611a42c0398001c1c1c20ad02c42d950000ea0500085050401c04901400ca1002d02841400b0034000c1404404060f060340804000d0504044070550b156042241d412142c6101d00c2103100f101404e125560742a02c3c411501100d21810004801c14418440203060740d905540c0c04041000359030b0203c803503420075100c86031b195588400005a04000c2a0440b008620a80313036440c3d1490b00d10381c40d440c840f0340042d2020070709080601c0c0160541c2c0100b0000d1a20a105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 628625872 1250 628624622 628624639
    0x1050315011e05030a05070305191d120403030306050108010b0f0711090907030224071b120c05012303060d0c0305030d0504150c020c060a02030d061403010e030711 72
    0x2040100c80e21901450308a82032007006100000c900e0740320f401903100b180e452030284201e840f805011402c813101261440c0a402c84040315440c1c90545402060b00c600107504e11003040c401c400211800c161008042115402c0001400c20400d174050003550010402400c100e00598908000c1150521500c00e1250315200002140c0303041103e208000801c071b20000d0111195480c14140c40c983d1443e050105034410004040058008030000380210a10340300400d03414102402561421180c04108000c181914280304020070400c498510a8160300d0044001c1d2a810346003500240510000105071890701c159414010b808030f00300b00440303030400c20950342010740305142e00b000248104e0f070303401c000e107180800a00d400c0e0010280d00280d004901a1090b01e001210a03a2010129004c40c0c180d480036811410442a0313610b41038010300840070300d500550b4a02100b024552040301c6094001011f510100360b0040c4050400b40310754280840c29800440c50301005460f20000f00c002943c01905c158002c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 628627122 1250 628625872 628625911
    0x6140703110601030501061d06061204020d080703030f1b09170f0106090506210601050915041835180a0e010612050114010315080f0a1b05010503 64
    0x28100518101a114142c81c00ca58580c903005018100603c00d4103181072021a2110001d041c1880c5a409003200601c000d01c0d016885071840003241e0020b1040c0d80c040c07041c86500740410b413000001c224003803180d5000189040c81180c0c140440b5a080403c00031450600e41e040b03a40c80e00280458181c0d40000114140511118011850511003420480305542840000520102d45800c081d0007a0011140941181945843c1d400340140180881038a588500010041420f148074078542119403440324950600700712004c034059400c0382001640c5801d0f10512305061000f80003509203001040c4441910756030340b41e902d04202d5410a040c0c06240440040c3c9462444403d450b014520b074000341506507459a103400c201500d0101b40700d5140400d44602c401a001405403149070b05a031703016800025010b007204d0045006001160407400740892040010903201010070100c14000c0c2c02a0041c4018050351a1401c1d2000c10941d08442e010002401488141e80001c1625440820a001c89059620 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 628628372 1250 628627122 628627127
    0x20a0f031a090a151e051b090a172b090b161707141f02040f0b090109053304060c26040603050402030d0216210c09051e0106140703 58
    0x240b01e2105005c08010b000c80540004813a0030041c801d80001c9440f0750307903030300c101c40260852180c496001d6102400190901213194130400407803070052190100c848c0349418040d030307841c5041c07000b0403000904581320130201c4c0c860340a07202d800641810b59400d410842c0194051480e040c000d400105050000300b4440020615001a81e443d00e4103e00440d44403440d420000f501d402443d80003805030300781a4544218103c0078003c940854182d0b0b203101000526044000800d070700101c2081d0b040000700d040010f4030f030b682e405004a21010231540b0455010702d8410040c504501d90100d941c0c0400144000c001d0f45403c6025a01d1094001392949007100c5005000c191b00f41c0000c41e015a000d0340030502143c1c650345684034501c614402d40440b00c001c010b103082030766100d4800310840549182600c050044155401750405400704c0044402d02c610000ea4614010b04143c0c3c0003050300c40d0b40c0d07008011501805e00f8107034204941d08007442c4115418041c00038821110b043d4103030301c40394000805108052 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 628629622 1250 628628372 628628381
    0x100e01080610050c251e0b0d0b040608030406120b090703050402010c081801090806240d0204050901150510090608060a1d07030f110910020a020a0f031a090a15 70
    0x20388801c245c032006010004900120b05010070504c1024502280128210b9032821210111519117520070072080e00d4121406080e5014036000d10540f500c035035100c1200e0702c0b02e0041002a1509e040959100d6040c442c0007032064500403007038400301742070010703148164407210400703a00f005e8145004100d41e580d0b80011b03100e002d01510002c298680004201454641081d55001000004d0340d0300c0715100c1d65964001d98540c0700303545a0100603961004c1c2c1d000010354042c2c400c0106000750003a0410503440e00010215241100e402c9550394450303c40461032401d0403200300140008488200482c140001c00911002060203031001f406400c90204d0700e59910040f0400081c00700195610500700c82c900714501020042e1a10742c00700f8200390b20103007014000c0c010708010391168140e4604100c441c201700000640c00b020716400f0f40c01146150300140c0c40b61600381025145c80f1401c203008501e145030100c03010121000102210001000348aa06a004102914895003044201104440703808880c1c0062 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 628630872 1250 628629622 628629637
    0x9080403060b180c0a170610081909050f120a02060703051e04080c371529010f090302040b0a0e01060c060f05060604230a03030e100e0108061005 64
    0x41040b03410042c40c1030680000740003164041c1c0d2142d00f400954942441c06c29800d845141c1e1110085661005440c828020641c0c0300c41200d10302c07103040d89004011011036201020958503600541d120280380c90040001900e030101c214030240c034101a0340f00c000d444660103080002019202c03800b0403041014001410482003410401c121075003458a01040c1c19031040c000f0120f10b00a485402e1041c0d115941840702d52508513501001e40c0300003c010040001031407a04455a203500d1044200c40003061043d00c0e441d4000e480c4000d0000942a8405c3d108080c071084141000501040c1103883c0313522000304412698162404150f2500f808001698a8050f8000d9003141d000d000002130466800b6114803081790155408010080340da4a01c50103030b03003080350700c1500400104000c00243d13089002500c900b411407410717804e00802010000b80702c620300f0782c410b800151110321756140c946400520444052254102084803a04480000c1e011a00050a1510411340da1121016080c001c0c4100c6045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 628632122 1250 628630872 628630909
    0x6041506150807120506030d050d020c030a0206040506010e010f09020a02190606090f0902090f18011e06060305070c141f091106030103030813062a1209080403060b 72
    0x40d03401d509001001c10004071241000100c1c001c80d81164000c3d5882154065a405000360045070300d4400244c9190303000b0144900000e50812402c485140c0a001400c0c1195140c4c0c00f91801d41050b0414601d00001a081650400c10010042040010341c00c0d4004c2111801107015850300c1d14040140c4c180092072600503900b240100f00b100070000c055100005030760001c6d108009140030502d007107084403141e1100942100072180404e0f40c144480d00c0741580400015403500ea450b40e01c04001c5c0c2580e00070405058420f0680150244400d024015040a494207140402491a04501c0104000000c00018024240d65030034694400000d01250343d001e44000c440310748002918103880002d000d010303c1507441c003080301c20704000342c64000122030480380c050391600301e141c4408800c0c000409024100f02c40550341c4481d210174144504129034801514001324a545520011009d0254180c44a403040e1043c680500240052100c0c0187d0b0b003601c0d0041000912003e03240c002c0340c602000c9200a105 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 628633372 1250 628632122 628632149
    0x5010b1e150921010e12071709060403050d080f07021906150e0115110703030e04060e09010c0e010e10030207080f070f03020c030309150c07170f01060803030906041506 74
    0xf1052000014860068000d0000b08400a00c840301161156901049011107000c20840540421811032a0303a1a41c003461032501e1500c2180030000741300342c1c8036600496007500020352035039400ea080307100c01d035100c1444511030711185462040252030b180c43e0000550900c007044031b41014400694000001d5030030034840560290b40341c01c12100c20644c24841e19038018142142064018401c0d038420203080390413001441e400f811a42c05031028007004031019085035540200082944460880c0fa020f80300301d6000244a03e07540c40001d140700c0b1803918072810f00140e55200341041c0c4a01d44801440351f4585401601e4100c0e07450401070a02c80c4800320000d0220100e600030900246090801c4000c3c4690221290100410107041e241d003c0d0009441d408101d0060041c083c861140040443c07420309801d0350392545d1035000442d012100c80c55400084c0d40011500c2a62072001d216070000b40940e48020360075480c2084040e555801e0050009020b521440031100c407041080e0016409000075031002903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 628634622 1250 628633372 628633399
    0x190b09090c0a090603080a12090c0603020a18031101050d020409140906070f14091306090209040c03020f3406090c0504090302420405010b1e1509 64
    0x1030399000c219401c1ca10810307084030b0000c0e000c40184216030803290300c048924180042e444080e00e18007401c0c0e2007000d00a848900b8113002400101045d00607100c503450051b2a0041618028148030080c50718001441c5482010300124041e07401c4d40c2039a010900e00660340d8840402c0840c007a0003664070a0f921039040c1014110f102c44481c180c0c1e44a2100032007211880e036141c103c1261003103c0c024220700441c0c844500c00640d0400c10b8003c0c82c3da07402c054001c0c140c600718800310303000300e0340700341d0003248001c5d80441c40c1480f41ca02801107a10313010640c43c00f075080c240c2032140001c0131700c42c02c2c00283d1030b2402c40c2081c3d40c3c520081c1c0104080440c024405c8021a0b00e80d040c0000940304c0010121007801d409180814503250621440e04519050303401050300420448040a0405031300c1104207203038040d482c540f407100300901001c000c0000b86c031075116a50304007031a009003034031010300340e46109840c0020300b103048081e4044916850f09007156406d500d41502c00629500744900f90800340c00110030003420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 628635872 1250 628634622 628634641
    0x51f2603041403010e06040b0118091b090606020f251d090610060f03050c0c1e070902030f0a020d0605130516080c0427140a11030f190b09 61
    0x40b501d40720a800038004064100c0f40d25840302c01c21140101200c417921b0040c00905840d00030442c1e120796191000490b5449038585001004800c3c0703010201004031081400b20480e140901c100800c0a4002020392414106819442d00c50711130203900c074040e9034012115100a01c40c0f411009110700341418010100561002d144100700300c03030702910340c03061401240c900c0407292902812560103646100389280000011005014058114000100207000030502c0e20b50034081031908505400340b00031014542744040e414820164840d02c0d65038810b00030001b21101d444c410f00c0c3d2080a041c40161349009080c1035800424030307500b2540e0020608070056483c03407020360009004440d5450700c3ca109410089040310421021500c0076074001c01032208112580c515140f40c81c60762050140300208030340002c0c01c40211150040b94441c0550014180040049144140408492410201c23850341ca01880340b42501352001d03106845040703c01c010b40d40030300d001c0d80c4400052140240010389030b0400d001031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 628637122 1250 628635872 628635899
    0x160b0f0711090903070c0e040b01060f0306090509030d060906051f020f0106270e1009020111060a0c090605030709031202031b030306040b031b01030e210d051f260304 73
    0xc60341c06e444038401052010f8400c07006880347d40c1c08031035148940c3c20042c04403100312801d458001407607101d08020a1803286805843c2c49082100d0040d515240c1540542007510055407007203035101d140200500441c0c541c19100e00c500310484400c000002c03040d08089181040080b075148043d460f10304040f4140140000028801c01e00300201240003c103080d18008940705e80c65800c1480e03100b1400f1004425964100d01002d500505001c10790132940b0f0001410180b04803804118182d56540031701034144c010300408040e010518049040d172500520107024050580000b52415014060381c00c04180300700b003124294400e00c00c0020000a10042c02a601c0c5c0040e1181c612a03420429072816600380007a80588060308601e400e49103540003801580200543c00c0c0c103200740c1c0684090b1103801d022001000076000c04044074503941c1d056148008045640160001c40030700304807125950300080001800b81038039241d56110320001000071243d007a070803201303c2452083c0400f00d00040d0100e1007042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 628638372 1250 628637122 628637137
    0xf110d020105061216171005090a0b16090303140d0207050a03111b120f0609060f06090402102d1115010b0a0c030c06050f04020102160b0f0711090903 66
    0x95001070302ca0385001594469200c0c0ca010b00e1088101402000364a00d0940924407009400050b203820b00940400c18007038440c100d49c5015503a000009420030400200c240c258010010719051284203112000100780c02c0e400d00c000350420092020507040c100380340040760144206480e086568900ea441e0244d1641c281c1c490907000b184052200d1407540102141c0b684504110394406890b0304000002c1140d0042481406561441204039802002d2001c0100e94002d08400c0001c0c0700380d280c1140e00307002d1410014400f6000d401e890003071000580b20035103881c00000442c01c0c41c81d1807144118124010f40c104050704a030500080e1099850346070400400c005000c00c50054400c0c203c1d41203038814040c2020702c241c800300ca02c00c01c69000d0540c441c42d0021641446850a0750000c40c0a4a820003611000c0c0d5071074650442c1c6106020441d80c040010060850b042005500e0300c51406130b00715800d0140c00c110741d102c9940081d0340030030840444a80b484a0b17100615034401030504084651341c0750003031071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 628639622 1250 628638372 628638379
    0xd0c11060a150b0f120709150c0201120209030a05070b070c09090f080a050f0304060b18040b060411090301060611070f0b0301050409020d02040e0d03180506070f110d02010506 77
    0x41142a84240211500c40200b0141c078016030785032552903000d5a02198502c610030400380501c004821030034001d28001c20040c0e03184103442d070501d0941d078440b1000c3c0c031591042c000039118640040c0d0700b105a506c14800202c13001622054400b0109041000d8080d00401c01e000301d881c0031508000c0100500511401201c0255809840700e191008952030354002030111004103400c10001040c4030000c0c101c102043c81e22a04103644141e0090458200707a6040390002e0711071545000c0c9041503048030600090041404544d403d141c1c683c0d445070000070b0f10141c0580d072a021030000091141d811200800c1c0083c000300301e055550b420060013100d07210a1b40100d0b014003c8000b61420706a5400e2003a130f81070018040c0b540e40b806041100500341004200d0b040644200014096a55031055101100c03282c00507125542c1020401401c84205c00301e01d83e160320a6807144004113900080442d401904c07400c0903c410b4040440540b03076280c8041c0c90300418400c011002e0512607043d00428092217056 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 628640872 1250 628639622 628639633
    0xb0708090c0d0c030813180b010f0806150d060308070c030c060203270d021804030f1106130f051903020709020f18060f0703080402130204080a0b0604020d0c11 70
    0x12080005004482c64082c1000003282030070720200d01007100411403240c00c1e035011419a0f40e81c41c0d0060701d00c844541406120303070761050a80050358101c03010804000152030600b10364038204000501402010303910780034100000c15034054004256100101035900710a0311901c460203840d05131405500c5000445038942040800201c09000109903004020889400b500c10304540100002207200c1c025440d40c406100c044135805070701c81d412040c0c0d2100058401c0c15a41c0b40506002d13010740d0510305280c0800078000104e00c0c1132600402c1d1030380c11620510072044902e80505140c3d12401c00018041e08a02032242280020080e501051085da48280c094443d00c60703455000f03200324040c01070350301035011041121851844034640014041c68009010740c0c10b041a581207807030150040041140482c4480c0c00341301c00e6250024155918138000c400a40c90a400c00c59995280d452454004180d0b681d0540800d200da40d03280c05845c1c00048010007000030004c80c1900805002c00d001000c182070281 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 628642122 1250 628640872 628640893
    0xc0d0201050708040f32062211041413030e0102010c050a18030506070f020c0f1008100509070305010905060109060806010f030f0e0706020708010203041208040f0b070809 75
    0x601a09109450603180e1541c80c1d82d8503200c2034882d0b480c040301145d41d44544200c800c0301c0108140c8450307941c0c00d01e0071040401860b00310000d142c81f40150a01803003142c01c0304c0700082c0321900d0408501e0264480300140b4910315507001700b005854510680c082c80c4281400304614240c800102ea000140a5030715450b44a00080043e4201d8030480181d000142c001c1126260b01401103030200c0c07852584d07540c4980095501e40720700d0708081c2c082e0342030400100d106c90003011a56040000c040100000c90300341400c1c1003031200040045206c4245c00081c003400000041e0f80326501c540b0803008050140c0302a41601e0700050060081109021b251012864500810101d512481c101e0307041c2d84c80d58403004000d407640b10040d205400c040501c10101900c8064036902816940500d690048000004011103030130281d000e4104a41d6800200d001c0c0e01c1881000080395821060841100442c18024001c0d1110b003400703603802d4407010018201440c050240b024260b800f403412441400e080d000e403400e2081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 628643372 1250 628642122 628642127
    0x60408070c0e0c040306020705030c01050907170616270f06030c03050f01091802040f0501030302300a03180510060b040302090a0203070c050a1103010f110307140c10020c0d 76
    0x300342d85083d540d1030300740402e100007034841d401070407003d00400440e130820010300901030945104407196101508060402c00408a0784200f4001d00c04654018184602c0e00980714040005507a43c0707081001603200303404403400c0e8580d0031888080c0b054014405400d0300c41c014031010321070900c1103400192a10481d02601486031003128000c000303401c050049a4070f03007444c400103400d0800407001c441c6c03091005030005a680c3d115000000750000c034042915032440c00c004e070038800740940c0300d494031800f804968039002038201d101c500d0314038455090b034442c968030b10214010807801508102c00121040c030306090150000e81209004040c030f6060103a00e031100c040308014040ea00c4025048101309010880d41021900a95880388491808510240707440c0c80e5285051802038040e10340065405840910b03040a0155640700060035a05000c0002040c41000c2c40e071000501c010100b01d1a00b0300074280014900c00c4600340c2007440c0c00c0b42c403100c4051080d40e001351302c1002403040b1881901a024821030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 628644622 1250 628643372 628643399
    0xc012304021f02010f0609050411030c13050c1b161a0406030207060b0d0b011a07121110051906080a1e050f07240c050c1302040503060408070c 63
    0x354050400c441542511682c040c10b000741e000c00c4000d41d522416250640c14a0748207010052100742400300d1907041504100c48107142030748101d80290000307241c108603a2540f152240103c100b0b500700040c5a40c0e60000c1c41880c0c000c01c60b012881501050980320700d00d030005820b0062401c1010580ba440d69203014501108817801d41c0210300708000d000400c00e00e4020390280440074024180440c60864010028043c810340c0c1001701c601040345030040c001a00125240031110301080d9220303140c10311b1511040002102c403416542040603440c1d00001010080c4046c9258000660080c40141040e0a20544054614005028140c60407600082c0c04d00c00003100780c5603d0300040d0112880d1180181c561600040c184195000d00c00c0042400044904100d01001080308a40008070f9180c14030030070017494956440041003148214151003c41c0002c81c0d6525001ca08a0742d61041443e44060480130f401550b022903418014002003000303000d0030600401d00310348208038007481ca98030381d040c144065 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 628645872 1250 628644622 628644631
    0x3020c032b0c050d020312180a0204020c2b0e030a2a0b0d1a030a0308060108062706010f090f0b0d09080a0905190b1804110c0123 57
    0x341c0084031000300048a442803400703100a52400021104003501c0b101d00e02810b80d8403c10040c0d0002030740002d0a2515840c294221401003081c01d404401d420044e559072200c030745d001e03120780e90001e4106040d90f010010b00c0580f0300c00c0d4880ca01e04a600c0c00304040c0803039100d040800821020038a20f4620f250200e040b054042d072100000748240d40d0402c05003000345620600468000b03100f040840c0000d14100036012941c0c041002180081e40a078001c200d81c82146101c60103030740800c00300c03000640c002c138032103600c25820f06e4041c01c1e5544a60014041c0322091646034141d0076000c21140f2a524072602070b5205160a03211442a0000d91000b102c040c0c01602c210007503401401c60a0003890050740040441c6d01401401040b11000c6446032a2160700c0080c030080404c024000800079401d0010389070045441710249100001d1a0000d82c81051103012800641e0044100b10310f6520342d41c0b0781c0030100040070700406540301c56802d08503d0003000d0035031086400780b84003061180103020080100384117 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 628647122 1250 628645872 628645903
    0x509070b0c0613050c090405010605010905010c0809101e0509030f15010e0703090b01090b0a060e1003020d060305060717011e0603020310230114030105150c150403030903020c03 78
    0x5907943c0844200b04141e0002c421181070090b216003512030780c3c03403011550040c1e008600002d07055191000243c4a840e2a03031005040c0724480240c0c4021130301e034009481c06280296070b415040d900b4404115811000350004100b401d80b603911081e001e41d80080a041d03034050680031280c000030149152591500c0610464411030343d0000188105440305c4e50540e00943d0310b09002c98110942c2d990300c0d6074034200343c0120213000c0d690034140d0460320b00307400740b02c0040c409400c00643d02005071011a200d450109803500906800240d510b40c60302250344900d0066400c0350135076405d81008907006002d05254484014000721280001c60034055440030503102d0010b9101c40410f0525081d02a8003940000301071401e5040098000502000100100000b4001c2219200c154640700341c000b5104c81440000074800c201c0c18001404a0f0300d8140c0c0b486032441d50303826611713140c40e144000c9901d809440c001036031900d4808024071040503055000420880d20a40940341001c0d00303401856603d00421101045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 628648372 1250 628647122 628647133
    0x5040e181f0f020301061e090b1b0a06020304030221030c120a1506090f0e01080303060411041a12091f05060103090b011511030c0703080a09030212010509070b0c 71
    0x201159000d030a1110020101c010410000ca0b01501c0101d8209a0100000c5946000d4030051719003882400c42d4031b180503041005e0003900340b0f486240c0d07c2c0614002c096441c41b414001c1f48400c0030401540362102da001a080d547c83c40c1a2070001d448411915101402c001100e00c4804645d0354441900d120b00400340d00c2a0030800101268a40c080020340042c1c0c010344d941529200070f41403903c09102802441e00c44c100e01d5498400c00c88004005688447c208c0140d81005020001e0003004aa8000d03004440c0402c50460184168480e0b200b284e11441c28403142a003c00703450384c01203020346041038545c61071605503a2084041d9480307240f05900030003640982154494045802e50000c5e1300280185400074a111741995600e070440800c1c2c024000c9403402d002c80511056000c0300a030303030b801c41c401c000e5400c2030b400b44032842d0707112030300d0100400d0b01c04042072215001c0d2103030b440b0310011a0001c0c042d01c607000e900d090150017008144e03902100e501502001241402c01d000850b0060b0307110000610 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 628649622 1250 628648372 628648393
    0xf06020a05060402010c1415071107050901030b090f100f0c0801030317091c02060a0e0706091205010b04020d0b040e01020a210914060939040e010c05040e18 69
    0x40e0000041441141c012140c416685003801e010408423910380318600c4840c40701e09041102030050300200c0340c4400346030b0103880e05001e00d8036103808180c11294480c1013040306071030340c014160522200407028052441480c091201d91070f9207800603002d43d0fa03001010030030000e2100742254400d80901024001c0380811045500c1c402e0341c044880c1e0b011980009443c50000680c01808403000444060801a07010005000544469118030700010300380c00c004100461a0120141c0404003e01c00c482e0000215655441880340039004125841c1005104665407041c4000a500410500741000d00803454021000220f850501c02c81e42200c02c1a21036000c0d80560b180c07021003104032010f0180d0751548403820340c80040e5414031500c900c0c0031040f0181420b40b40c0303981c4040c9070181c865024200c130707240d00a284410032940d900c1081d20001500003500400b00301c03804100904056003103d1507961818038820141c0d039000b405041640c0d003a514400d865100d1038144110701c0040b8040f01d90980105a014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 628650872 1250 628649622 628649627
    0x120f051602010903240e06091c0c1b06021e0c130b03070b091003060506190c02030604030305011503090507142407020411210712060308040f06020a0506040201 70
    0x1603420341d105240102d54262203a440b0428141509100c0105940c1a10101e02429150040407030070155400100101c2ca8414412640e03100d5002c204d0400c4120f00240004143c0328080481c6255040000111040d18184156108074101d200b520018000c0055403511804490142c0588a01c100b0090403840c0c0c1c0c490810100c000d461640300043c5682d000b0368100313070314140b15450041c002c6003075242d101e24160f0180454910344d102424201490302c2e100b80071350f80c3d940041e41c0c0001c80388030101e0006000240103581c00b914000c07010b580b5205503000c010130140c0c190232850688103207200ca51094500960705a042e980c1e45480108280c00003141131140c0c030117001080700c0118000b808132000c2c0011102e082240c1a80c5c0070040503030200082e40c00b0550400c1d0107100c04281501e0489807805040008c080d41c1c4c0540400d1040c1000d00410124041610460f9074140340d00c0d890f0743c10025240d40b807804483c140c1c40343c42a9041010341607000506540041805600c02c0c0e0060003030401c0c1d0383c459004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 628652122 1250 628650872 628650907
    0x903082706061207180207050c15040308070c090e0d090807120f11100e010305060a14150c121803060610032a050904050c0903120c010209061303120f05 67
    0x1000860700c59204c0c0044c007540080e00c85860428042001a692505403c24509010a040426001d070400f800801c4210b80d4040c00c0300d00b00ca81221b0020f0715040c0c5d51411103400c1035540d016001441c10f001101407120340c085451203014038a074980803034a0360b40300300294a07001d003840344c240141d68021100300030505d003500c404001c606c00d4807103590383d0101300006000c5114000100001440440e0380d00455600341c8035444d000b03c403c0301c01a0170076140c8007101302e50132200852580984100001d0040031140e000941b480314000310240c0f030a000b44603034003d0068206800f60211107811180741001401c000c100d10f13010300070140640050028018044e405404404d40c0f10418031507017070901078001c0010040700f5844d00390360303612641d680c100010401a520040c1c00824880400c0180b0007090703800003480c0c1503445890101685400303038014001d009010301181ca5030070042c0013030510b0000b40700b540303a01c0999100b20245008000e03005021240c3c8001035001002045c0d0801c000900781e00750b00b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 628653372 1250 628652122 628652149
    0x4020f09030613051b09070e130c030f15120209091609050108060a050c09150706050f01180e0a2406030302010e0c0d05060606090a0801090308270606 66
    0x818a03204019012030716000d41140d4100f4108020f1400c2c0003001014840070789101050f54264140c200c010380020b107800c4016003a802404207010762a0010f8031054400c81050041d104100542c48400e18082d002e4810303100071640d0580b8000035205404600d00a043c25600034010003152441264280300054201030036400300c40c030441d180030307c4000b0b071549504040c08980c03c01043d00d51508010a141142c040c020800c100c0c02c003401c000c0079174000b20075201c0c0408121071030b40c58074403a40200e8045205008024107800e081c102044405681c81c04c840b4120340354000314090404a0301d090070206e861540100495422415000f004212082058269200254100e85c0c10b9840b02c14440f040700c4482e0300460260351210b00102c2c80401c140603140100c8419120040c03011007543d40c03d912624010500343c81050081a41c42064450f58002d4029204120081201100904024117400c1d000c80d0051601c0490702c0e014000301c0d0f01c1c46d03112846410b13258018011901c0d144c0c100403010600d205e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 628654622 1250 628653372 628653397
    0xa0f14010c15020301180f1e020a0302040f0902070308090318092509030506070c0503030f090c0a120203060106050c060a09080c03040e010315051b0f13090c090918020402 75
    0x1c0e0359441182c0f006500030564400d128000030300c065078440c155030001d80e0500003a464868680390000048060b86500c8260010041c1c5c0e80104040641c001c0c000d42d041034070b0700f40c035201e00400c00b038101e47e004000d0b45020ba152040c1c203a44044404da0381e8421150444c84048989441a000341048224075412030b0302c440101c441c000315599215061400b2801240001e40386c99010014004103011039600620786181400b448001da4440d01d07641d20010b42585120445a000506940402c1c0620b046114000b0510b841c040e5646100e8082400d40030740981c800d0003210000a0950b000783e084800d414400c070040c180550b2201c03100c0c00201000390040c2c4582c01c0402c008000340030240700a10140c13030650242019541541050714032040a000421180c5140c031003440152507000c04030070078070126180f08941e24030410b0807100442c01035a198000c0c1c43c088041c0801e940107150030070b0b91019000c1c1e517448440c3e40d540c6125401d030b509610003403182c10100f0344400058200390700100b68030346011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 628655872 1250 628654622 628654643
    0x615021f021c0e21031905060d0b060d050d05030f010f03020a0b03040303111902190822050d0605180c0a141210020403120309030e13090c060e0a0f14010c 68
    0x150010781451440300b1359120341e02c500204000303180c14103900740700c0700000d80a010801c40c50030074045280340c28251405001c4085241c00a06180c2e0fa800c64025115408815104100c0c51b404010f08035400640f0340390b01c8800b12800101d60054000385140480c0d400900c2d480380d29140490300c018907030000e0b000742c041648030110049441070f2900103110000c40340e03400c040c0070405076100030705042c0420241c05002d0304083c1c064000c0380e01c14081d02c6d01009810310b80381702d02034601102545c00201d5030100350080200d084400510055501c42485a002036080001120000c40400c5c4c8840c00c405609510214102e001d01a4842d02e1049a50995001d411304580c081503850551030311151446d110041c9800040500c01c203d00980c50492300c501c6810144110768256601401c0098005103890050301d104580c0c03030707452600b900907903601500300901604094403148014003800e03a00d14040c0c003809003a040007410a0407400d84d071003100c000170040c4500001807401121003105e500d00543d0110707200c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 628657122 1250 628655872 628655893
    0x90915050f1902130311030c010810050f031f0203010f12120e060f120103030e0d0b0601080a0f0c020d0906050720010e13020307030b0618130615021f021c0e 69
    0x2c0540390003850080c1b58203494040c1e1801014500000c00400d036042040c19414443d8007515484941d040e075600701c0f0000d20038160300c0c000ca403500d4ac0031000c1c109034006850b0029008070f4150300642c1078412000a0260f002d0b2140d01e801e500c044030040041101110074403038190140300c2d150182e04550002d19162910300d00403010000c6030484c2c240340284194030001001019040074114112400a0354960740400e441d460f00307243c5140c014242410712254200064562820341d02c03440000d040b00004018003001000e0095440790b20b001c04902080300050302144860280301610b0f5140d0303000d0f09820054003803080421003a000070010030705000c00304508034001e9841709c00404007601c20407401616844e00c10701c02400d540b034402500b0701647d002c014811607425a0030548101c140c2c03c1e1407040054800c540c400e40100707001d074850204520317a200c00c1c0c04500c1d03000c01e00316000c0e12003401440c1d6800c040402c640c12031007640c41050000044074a40c9140c005030340c110845801012007500e200166 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 628658372 1250 628657122 628657147
    0x50306010c14240907030f081804020d020711010302030c070f05120c0d020106240e0d0b070c020f370803040f08011a030607110f07090915050f1902 65
    0x14003280c0107032246842d40c02d11480c60f861114207511080740d0b0b004003c40c62035925080541e030b0b42c2847c0902121000078041048895000655200d10b030003030070855503403010800d000020b400c030840458109040480f100c0766036120b4020f403409030803d414183d26082da2075540201415040d281100d880c01203c00c0544244000c4029144102d21000501200c0e030bc070b180000e0840300a5000380c10070340c20701164286001a5130440f81081141410280e00c24851403000a01c0e201441f02c00900003c210010400c00950001110080c00d10980310180140c00360410080d12124000c601002080c0000341250744c2c3c44243c500c041680350070402e02060b952076040c03130381c1194425000b800310006064030400c0014030910620fa6000102c0f0011522200c05400113500c03000084c101000704842d6a038441c078180320903c0354034480040c0c2380c119a9000d555924070805450a0324040e00c0c01100240c03800f00c0c1d1002809094030407a21080582100d682d90f01d1031640d01c0f088100d12804065091005403245034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 628659622 1250 628658372 628658383
    0x603030917010f0f020a0207240e03030c0a0606050a05150307030b010c0501020304030c0b0105040203090705060c01150f05090f09070315090b04030206090723100c05030f0316030606050306010c14 86
    0x120b04010140c3d841c0d61b038510182c034003034050740300004a41c1d40880b04003c520081070880300c4c4443c1450b18803034510711040028030b54054024000d245001d554103040800685a02241c00c845d01a50406112950b0700200b1800110b541703c46091407504000040c1010720035401b0f00c881d00b005040416590000361110303402c9030411901100403540010004041c880300241160062204560541c41d51400c2c0800545580342c030311459001c4c803800b080c61880044207402c0001c43c2009120a4250a0782d1038102c19000351092140c603004000a01c0401d03901401c601c09a0300c44c200400051026074a55a01c2d00401e40038080300c1d02c20241d640608000040c400d2904600443c025030080c01d42e81440200e143c10700805503c0840380b83d0083c00340041116a01c15046c5c1d0000c0300f110090144030001e1400e0f04c0315152100024000d0000055540b45006044003650007003260022030110f03801d15600036011291140950b0010071400e10000711990301c074032822502107100da00c45051028034480369502c0d08 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 628660872 1250 628659622 628659641
    0x3040c0b130302030c0d020d02150d1a0f01110a150f0608060708090c18040f06050c0a02100c08010e10030213020c0105060d0314030408160f11040603030917010f 71
    0x1109040c400c00a40c40d0030810800d000804440e00c6c401e6072085c0e03001032454100081d009015076024244210355176400820348010780c00c07a01d01880072815511001aa000724171446034401d614034100c0c4d034a154851482c44220400c210000e0500d0358641c1c880f20501c4280109003011152039000c8000d42801030300440006190b42c0d0000c005505001e0409495070400810191440c5e00a0701c440e01d150f50340c0c0702c070110102c0b05880621802d49440c200344840001955002d000307142000203200103140104010b100210050b401d45803a4441c40d21180300307549920081200041805c401030114403450701e007a5401c880201200200e65560b0303804240c40c1326202c09824041079010800603d102400c0c01455840041156001800e200540e0301900110321407400e0a91010084002400c12401c4c2c41110842807a01c0240281d4900e06e1800c1409015540012201a00a200d0381510740c10709015040c04d499054503a11b04041c200301841025165258002040d90340310601d640c0d105290f8810711401c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 628662122 1250 628660872 628660897
    0x81b16180b030c0607050312010f0503150f061314040c060e09011505070c0e090601030c06020312070e0f0613080f07031e030903120903050601060311070803040c0b 72
    0x4a10304040e5100d2150460340049140c0e04090221840341e4010600c00d403045822036a15031154800d0405914600441508402802c0444000b00e01900000340140440c8c0d0220304032901480c0324000344106ca442595000042440100494807074904480b113082007260301200014011200580c1d1298024162000e0b18140800d002c2400280c0cde0081ca440e0b144003055843d4000707545804149010310710f9070948a0108038008c00c000c401c100a0400c1c0e200105488048500d00d402c00d044015201d034030070303c4111011031119500080301d60010094a012000603420704115599070b0704191140d202c010300c000c0d40300d05e8100110019659420140150552031441c0743c4040b814085250302c3e1086211100000360f100703110803c0040c0100301031303044114112450340000c410924003600c000c0500d40004000304a18079440f001180e00c40402e00450380240b04a03180c0d03036aa4803041d421142081789206c0701102c01c110302004103404100030350f04240305042d10003403565600031a951030b03080061800034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 628663372 1250 628662122 628662163
    0x402011b0605011a040303050f0f1614060610020d0f0504080106060e13140c0904140c03040b070306062309030313060f2c030f100903031a06030103081b 67
    0x1070340203c1031885142c8072002c0b40c0e003072400b0700717544005d0308c4e501444044203000e0000007030907031800e24840292102c00c5031484404582e07502c0d504e424692464900c229200500c9020f00040071344c070b0640c000c100000940e07009032000d00c481d444200d6004004084500501204000c001601ea10900c207502c000c040a94815801c80c14943c00c0060450061034600110f41c1840d640b01020052072110541110529064964661040300414060143c1d21000f003803c885101c204150600c04e00c0c021031182d0303c43d008a07000342d500c1c0720069003240d016000d0b00001565401c0002c0344a80001c52204141a4a034600c0381130a80420000c1d14540c00600203501c01202a4010410550000e140e074441d800d003801d00540c0c403840312460601310303540903000191025030501c4070308194030240400c9580c0d03c203200543c5c102c1100c01c078111001c1c0c58140d03002c400191038840d19001e80c0c0e48001402408100042101c0d1640e4a07580752007501e5008110f1414140c000d480012560060400840c03450050601400a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 628664622 1250 628663372 628663379
    0x40203090f0d0c050c0604150f090513091a040b060409030504030506010f03170f0f1b15090706050309060705071a0708180c0a05300c040b01020f150402011b060501 72
    0xa003009040c5c84442d02882d01400244250f000c0c24000102c002c0032450074200019150400312001c4034075502072604419407162131204613004d50030015015020b0540e200b1030744e03922a0b8031401050111000760200410002060452502c0c2c0c06c4208170501a1030300b9403c0c03175165180c40f42002c0302a440a0000808207000f00108100c0104c003072102100f008200341000b074401f901e000681f04080d000d4450480005100b4502c2e0842d0504100082001c800c40350803554005907894a180280c0b4110028464818001486d43c4900c0c2120303c203540b00c2021305050388071260b068686030846401240c6850f00c0591080460007200140352181e0b81c207036101060b41c100f032849414000d00c88414007009400009840355140c803070001c00c0080724016a40507400104c480d4040e1404180d446180d0380a50f075501a0300e10451000070464409030b0111802c0010810800043ea91004000d03c148160340103540034505401c442c06885078070900606003005410310002d02c0c8000880c180d1011500641c2e00c20050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 628665872 1250 628664622 628664633
    0xb0a02010b1c0f021201020c06011a0406050f0d09080a180608091914100f05062d040f02190207050604270b03030c060f070305040c05040203090f0d0c 66
    0x160460711042d1022107541d005411005500719500c24054500d04510203403504545950b41124400301e5041c00840d05e07406402c5107280c07500300a2149541e9504490307020402512030b4000c0b203080b5011030300c8461902c3d200b0300f6048103075000074170500c510559551070500840d24050042c46201c506130b69110102a44030340c241d03050415608084200715560042058103100000e50510591a1340281c0d6030b40c51141c40c0c00b15010004100d02156070085642020800d80341e80c1142d40300c081d8000c428000359076950107104401468103d294071164a407010340380c5910844252032200840940003140110115144800343e07070280540a01c4c81e4890120707011003950600c10080a408d045605d285401c0c9404954104070000b0400006480321403c00c40c05a803002d50311000c0c41501c06000c0c1d0b601c4020502000c2d40702c003001c65103446015044400594190300c688261032249601ca820074011500303040034007001707400c01090308129101300c203030600b40400c08100b9100d2401c150382d1780c100d084c2000d1801 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 628667122 1250 628665872 628665881
    0x3030810080601230f030d050a0305150f010c1104020f1207091a0a200304030309060306050109090506030c09010801020904060e04080a080408120106020d0f0c02010c0b0604090203070b0a0201 84
    0x103103080d00140d0061180d40c680e614a4104409807204c03440c0030000000000e81e407400c10340645d03681440740f503001071540c2d03801102514040c280c98904006980e0f0703108001c001ca225080c0001e41c810766540340071074071b580122483e290207801042c0340349003541d010010500b00d034085040c1d118103a60105001501420080c0200e83c01001460315840c1540b40140e201e6011a00c2441d00404141c00700f400421207100b903000180c00003614030011074075030141c1c000944030350041c00168001b0745000070111300c0303601a000e0a41242c0060f560003248501d441d1a031002080003501e165818041c0104000d480c1c5d45d09980180a05040f01c00180d55010400400c000c40b034040d40150801900d400421001ca03201c401a100c8031a52414120800c0d40d5514017850740e4070695200e103d8450020f80042196640024121f00104c02526642d013603072541001500c44502c0c0090081c0055005490940000e244448054000030090070104403100583e00103818165181c102d59141c0101145145040d42d09004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 628668372 1250 628667122 628667129
    0x5120301030c0b070b040201080603030906030c090a06020f0a031206050d110420090d170a11060f280608010207050102030a060b03130f022704020a0b0f041403070f03030810 76
    0x1021864280b13507648803544024020b00190612182d00700150f1140c03800d208441d80c129000700b42ea50342e0f280c1904424501c4d0042880d50303029402c80c40000c51014000a0041c0c41a12450000c0c504078a80355021654805c070000200c0d078980d140c4000007000d8903802c41c1d5603006442140d011041101541c1880304407135012501114160400245081150420089504205040c0c8091705451a03e0a050700d028403020000381003040b0000d001c19007107600c0002450301d2035139003090360300d180c6a44d2400c40749520103482250520302070312440264501c0800c07800c4047c400080002c50020350300c0b04102d08a0b0005007064449035000400c0043c007904501c1480040c104001580d411401c0000606000c03042501b40203001510001d144001d40d50340c00d034850b1f9262034400c03500903550040018800602da00352400c0b030061380f42c00c20210708400900243c6120b5514011024241864a40e0007040040c103082c8640d014000c010300400d60307200002008c00a940a84c843c10000c2c200024850030380d410701d50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 628669622 1250 628668372 628668389
    0x14060f0702010b010c1b0b040e0a0c0201110d05041b08070f050d03230d0612121e180b0c06370b040e0d0906030b01030b0f090702070305120301030c 65
    0xc03d00744160b07007103021030703404030b0b000400c40400e545018075008642ca629041498080004240058010381000c004c900c14401010184284011020162b090b1011180404120813050020315030b0844260301180c0e201d400344801c110305280304102d56091408542106025801c4464140099429000b0318002802c06855050580e00c075520004c117a40d11200b21140c0c0c0e61035034120070842c02d400f0016604901c2c0500b208100965503500030a850203011641210300e0300c100000403206900848400448200d06902e42000c649111021643c0195099020311150064a0003007800c0c456540940060a1114010503590621030a07001001d480c040305198507640c0d01c24002d06e0400e0382c2c18030280040c4580004182070380b9403030000d0f014010004041a4504c60010160401980459850308440c4aa00c082180c01d01c000011002d44001d441e031640c001d014041001b00b42d003050140340e503126900b803040d02c100c05e03265640c080c2031003511640d00b0070303003030001c0014418040d070000352000602240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 628670872 1250 628669622 628669631
    0x1170c0d0210230408010b0103060603230c120c040305010b121510090903031a0a030b04121b0c080d030507080a05190c02030d11030402031c0c14060f070201 69
    0x55002620490044103080c0400050061004940d04450103c6841260000b080da4a8648954009009140d42034030341d4002800e00b80001000340c002e03c1100105d03c1d5510700038040c02c20124802c4405480588515408441000150180180445a00d00500302c0441080c1d0f128914200f15007920000d02e0103d229414100d5940d03158100001c515007101d0760980100c031a03988810030054070260540c8100080b609201143e010036601da849010f03024900628000e0320b40064040c00101c000c3c83c000180b120450001160128007103210044050045107030400c1a5034401c0ba030301000c1c001c01002140c401e5080c01d000d002c3c0010074800200e0000041c541040343e45440480100079040141c46a000c069462000c500340c00001040300b9032400002006001026143c0e10003580c0e03600111100e0034492500001c000090071001c100d9000d6034009005200501c016402c03014900300c0c2c0d40e5180b081c882e104c0d0307040b0001340c0c1068a11145020640c054150303843c01d8500e4075280b840040c400c2c011a490b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 628672122 1250 628670872 628670899
    0xa180207050f010e1009030c0b0708100b03090307030813061b02390a0503030a020d0207050d0c0506030a180b040210020a0c14220204051c0506190b040501170c 70
    0xb4800d10041010400810b46c14440e0030306a480d4038404070058101070203d0100403403d6007054105001c0c60303006001c1548581d0710110104140070540f003c411a410070403c0101180c803421102e0340003646030600350f1040c2d40780d54650b801c07140448804000c0d40c11074055421066014859194280d03000d003080d0600440040d04003454040d001c081c7c41c00ca528440003100d19840d40c800503005010301030704480c0d50f800d030792501035601d141640c8054018800c13080040768500f00842c4038146190b21100b4040b0b00d5041104010041d00300400040100d0354542000d817500103489403000105025036a01c03003040c28640140090300c4044003076001950b002242860018840caa900303803c403480f40e82d2803010b05a4000028002040c02200300c00c180162500c00119821551700030001c440007200d2260f422a0841c0c0504c0c20388040b240c0141c0180c002400040b4407034950031250310b1502001c0f5002910080d41400039045800a800c90b00c4101031309600c501400904218140604800b01d48170030700e1008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 628673372 1250 628672122 628672151
    0x415020f060705130902030a09050d081006020703051b1507030c030f08041106031803072a03050c01080a020f0c0604142b02010b1c0b0705040509150a180207050f01 72
    0xc5a110f034845c03056000002840540913980080343e5070b45e11030305942c211109160020b1003d0301c260351412200c03241420010f202800007600c0303006c485c0d01c880580f0000c42c0252625145101005035607400031500498a01d1288820340103242d410310a403916103030385581d07060003003d05240d4040b00090000e100184001300f60303a00d00102c10028101c0d0742c00c7c2d4075038a4465101c46041e00e00c40c0340000d8800460510300b0060840380b217254040c030b1808603d182044900c0015198000d522000d403913600040f480c030340d90394464540307580d000c80740c114007618060300409040590b90240142d100e194100c01d00303002c00c0040712520808a24400c000400200310404100b0a01690700340c2420701a440183c04004107900039088a200c07040010324082c0e082151a101e0789c0440c0580c881160400c54400016a0b4039008074295019247d02814901d19903803000d00f8218141501ea40701940900c00c902e00186541a612001d185440b5108000d6290030951403e90b20b0000741c0302e01c0c410b050741011880d080d07800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 628674622 1250 628673372 628673407
    0x3080f07020a0f03210218031609050606130b0d06080706050d181205030106020c04020712080405070905010603061e031101210603061407030516030e01020415020f060705 75
    0x280c000c0c050303c0441c1c0c600c0c41c00345d600c030100e1180a034900aa5007503d2680c0407099025144e4420a408000440003c0108050300c030482400300508203403402e0414002200300380c0c84207522010107010b26251020f01303013010f003c1c0c08650740400c003010400940c19a48000600882004243c1c1c1b80040c60f03194204240036015005031603283e0080c51b0744200b40e00e49003010658020260b40c1051490b50020007420000b0420340c402d0048002520840b40686440d041c9403085502c0140c20028190000840700001c448040019105807080e101d0701c80049401111303407141900a00c03030f81e10b00261607850000c1205c40001e14800040d6231491a40040000c41d042e6440c02c4e16083c000d18100b4020510680d0210202c1d00c1081d0040c8241d1401c20040f003008941d60202c0ea1580c00c8070000700ca01c1d6200c2c5003c4050700d2049402c80300c2c01c44562544c10782c0c2402508040401c2190900150a0585560140c813840010203d0f12005178010102c0e01c1401c5814000141c100f4818034055140080c43c0703401ea217059 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 628675872 1250 628674622 628674643
    0x1150f05310605070b2404090302030c25050105130504020c031303030509040b040b10050903152a03070507020618030a2003030a0c02131b090303080f0702 68
    0x1c19010300300c1080c60307031035414084000400021200c0d81c40d4881d0801031140e04820300440381c001c10103000c81c900b40100f40d68a80300b01e001d031022003140134072207060001900c3d15060480c01d5100138030502030b05d07401c2480300c00d000403d1484483c2c0c00f18580303091002c0c0019158003160522500700211b03800b05004010080980308142e90169503010210301302032542c480c0819016080f0543d140200416510600404160350308480500c11361500c2801c01c411108285442079010414a60061044c0c0c0100060840080d00a041d910850151614608242c80c1140c02425400228143c07240120641c0489954618401080c60661603c0d0f00d000d000352040c0c0c20040c0c440c0344003154909583d43da903e40c0b4040700501074140e0301d00f440346282c1002d401295054034000117825282c17458030381c2070002c10303515699100c1d13a408030740c0d020503004e12200081603451481c54580b01d006888545007007141240080c0c600c0d0b40d46000451030340c00c00600045000e066060b40d60b10080a002c9290350008640405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 628677122 1250 628675872 628675897
    0x10c0b04020904030216030308100504020f0702450a02070f0308060a03080c0c03010e0115091503020a0e0a150b090909010f0e031308010506010512070309050307080301150f05 77
    0x31600c1e103003020703442e046da03000d02d4a8011b145420040b003050307070241496018030038510000c402079499604020507801901408181400b05022900141c075003c0d00c01003000e05680d0030101102070b840d241c5d600b8100e14240e064042c840f9001203494607503191512550054103101f085040403d2541e4444032060f40f03840250401000c0b9010070b190341c1c0c48804200003075602210085da06e00320700d0310711038a40094000041c880d5103440401080901e040c00b910313100d50203204425000c50704015482000300900d2065280c00c18201c02e011006868009181d00a0010180c5503502c614107441e07150140d4140e11000e02441c409804104030200e00a800c0d81c41000301159440260303501c10071401d0040038260301400c0050300742031094100c0d070404401822040c0600b00401d00071781d241c010179801e80344141c94150015800700b10758408001010302145e044150b40c41c002c0784450880d181c2628503000f15031300340d130701120000c0100112680f006000c0c0700c0995900b08034446111440c0b005e0800d014080c4140c12 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 628678372 1250 628677122 628677139
    0x30705040b300109030f020c0901030c181b0c17090d08030a0f150f0602062202121204180b030a0b0a09080d0906060807030503070201050901050f2205010c0b0402 71
    0x980001c41c400030450b59103600070014400a030030000e2201051400c01409802400302c2601d06007040701000e07040c2d0344c1050110104034540006d205a0340b140303004016106555682c50400001e030022850841e9642d41c0c1c98403040e038294240402200c810f0b0000b112606d80400c01c01c80c681c1c0350302d0460840d954008005546030358400c02080e010b00030545c1e00c03044242c035280c042c05070800b0703415600781981d80c1406200340c1c00e5242c11007aa078a10050305c07100d01252241d441803403c4c85840040700c0e04203102414020120207810500343c40d052110070fa030052a8004a0f042c0402580304844a00501c910b01d401e0040b82040004641c54040c0c110380580401002000194a41d1154000c40310303095010104a9841896005071030040400c07000c02c48078a41411340010390524002041010f694110000d10b1404416900544003a07020514503414030405206c03000500790f0701e00107080009079110104d000907c00c185814000c5c0c501e030b0080707810f00c03200c414403c0115115440c080d81c8998195401c49 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 628679622 1250 628678372 628678429
    0x26120d05070504120b3705060109030b0112051f0507020c01140706151a0309011409030307122c060c030c16210f03060b03040f0816150902030705040b 66
    0x454005001003000d40b0500d0340c6c0250a0108080d0100c0f506030907056504018540700e0400440f2003001ca031002914041a84006100b01a0341040700f0040707600c50002c5a02800c0822507002410004d80c585041841da54010454603075010301c250000d0305802d20703159070003942210100489004282000d01000da598111944012903130b50840040c02c001c00151290b120041c040c003071951b00c1102c4200e4107508000c0c0f0140114490580517014540402c042d41c15540c4d03131042103a07001c0b28840c1181420344c484050b1044038028091800c2207241d86404010030605241d801032400d100500501c0b02030204108100a012401043d00d00e00e00328000c1024595840c0c1c00c1c00c40260001840c080705650b541360381861450b410440c540c150030f4942d1004e01c000c550f40e6050003d0360000b1240600f15040c0450b0f405d00042000300200100c00c0c501e034480c1603500242e11041091710826045118650f501d034561010b603c2c08000c0f0400030613003190244122401c130008200101240302e00e100d043d00342c5c82c0002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 628680872 1250 628679622 628679641
    0x503060a09050c04030c0f0515030a0b041d0d0905130209040605090109060e0903160201260a02210105280308030901050402011202030601080126120d05070504120b 72
    0x4001400c215405210506000500403d103030b2141c4801ca60b00c40000310001040d40640e10800c04035807008005603200301d42030244500e50750009090b0300c0807030740e1a250700b80c895440340f14441000360303080f00031009034507880d00302f03450186030b00000428001912401c0105560342030040030380c5031040c1030240c0c6452891010401520340c0e5001150300400250001c1108011980100d04503440e0110800407a1914408540c072071103169a07684003021740861480c0954003892035070360384003494501c040c1081c42a00c1d50003a02c02044c1d03210300c078054002a42030401864496660380c0400103441200c41549014001018180503590302c10710b219079124414035100c4420012001035801c10341c80c580c0c0340380c00890a07000f40402c0320206e0100740c1c15011034941441078401e40f44500c406841c2d01c99240d0078880311301a51041c54540c0000000c040c0c0300c1d03860082c400c0c0302108049540010311a25420003c4516040d954010f000308104203080c00f00704200d0700e9a401414640b40c20507484c211507214903c58 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 628682122 1250 628680872 628680889
    0x141513020c060a0e190c0b0304020f040216032c040905150930070b09030c030c0609011404050706050c0309120606010824061804050f0f0a0c0f050306 66
    0x114103071400b0702402c01c154001c440d0000005141a0004d8880c80c0f44540c42001e120b444050010700500e10b1500c052096200040003190440d000401c40c00c0c000c1c01c4500018181d82c01900b02d14803145040b03140c1000c240d008481490344603495040c10b9822200004c0e9020f0031452504141d104076100d4540400340300303090101e01001260400382c0e1500c0d18000d41d58a40d1410912005048000e0120664428285d180c0100b0407241504103010303c0c004081d2500c40c10503001a044415501082126a145000800080040280c0c29010740014a440c0f520b035400c492800030b11140e90016981040009207001c150401034501509020303488840050507140345014154146800c00342d244240c0d02c81400025220f4400c0704e09903600c1c102540d6901d580342c034072b2072506100805414410120051380c5000300203414024028a0702c42d044107800c20001d0242d400559901c0307940340c10b000501c00451044100c0c5540903059030803d210003600c41e50002d001240c8024946d003004000b102207000c80d51584030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 628683372 1250 628682122 628682137
    0x14070f060c0503040b0903040b0d0c090b1602150f190201060806011d07020a11130b090c0415140403120507020d120f030b0303030a09020a031509030314151302 70
    0x30030810041e1041d00904964025501030f10809207100c0081c450020000c00c590665a400505030309100c1003029901c09891420162418000e0341140401c4201042010740090b000480030440b504c28140103101c0c040b80d0b072060076100c2c61000c11a41d04254a214221003020050554880360403000400490041c8016000385034140a10000000e6030042e181402e5050f02072800009000e44030500161303580d03c0701800062424500000c2c80f0401e24040000d90840100108003003486c421280020700b102000310303490340f40641c001c2403d2060809011700380700c1c41406070401c1c50340903001c03810040b06c500a610006004400400e0400c445610a009403803005501402e00e1280d1a43c0b407600d42c2000e00346038414000a110a0040f84103248680100503072144040c0245241d40c55024407140508001c00040c0d80000182d01c0000002e0440800704a20528024000070101c03445d140003020b85183e564145003241454080c403215810710096520307081401c0701c00d0034040c884504603c0c060b025160 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 628684622 1250 628683372 628683383
    0x606040512190f030f020f1c022506090806010303090e0c0c030a1101151d15060a0207180509060609180307141c080a020913020403051b0301060614070f 67
    0xc81020080c106164540c924401e171140e001c6203024000c02c07a0341c3c412002c9070900e0769006000c0e51000c5101418018a842c41e00e1042d02c03030314504050703d400007a40c101494506140b41c880c0400803070b0350000d403081c09421440081c029a515584000b81004c105d4003404850381191008030345001c0d05030b0101e03241449d541c3e040c0ea031909030040000d44030303202403400c500e40e80d420188006003907220b100c0548140c8a040c1c20170008030118000c0601000c20007003a0240b24180350078003494542d1028054200f18410b58010700c51242444144e003151010205c0c84901207003014144403039130001040c21603104809485104e256a00d900c000d551003104c2c03041c10b0b001d81c00000380000c00e10480c4000200664440800c40c0c0c490710800302d4604c4000106241d01d07001806003004182c234200c480c1c008100988c00145100b4280840301d010800300d03881940308035815480940d0007446036403891410001c900307085000f00290b41c034290000c0d003078842080b407484180400081100c10440c982c3c0d031681110350001e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 628685872 1250 628684622 628684663
    0x4061112010311040e01182d080316020a0f0206030702011e090b1536070809011a0105030a0b0d06020c0a0b0907080a020d050f12030114010201050606040512 69
    0x82c205410f80c007110707102142c012800c040c0113004940e4140103d840000200c10108143e51031390711090000522202464908868000010004014041c20400361401000841d80d030307007003a0102168121107440e603035065406c031840f19004601918807a11000d501901c54036541e40e81c02500702c2c0141107500c0d00c043e8803255070403600c1105100758000030410740b24514405068840052038801e0540302c03400603502c041510244181c0200403900311620000c1d04107071404940350090000a44030b4112001800070b0880c00820010740000d00410813000b40c202e87c5618090754a10000340148802441c1c80800790300c1e402e00d0007403501c1d6501c18416540e0400401c40d161841e401c800c2d40c4403401140c00349d4690064902142140c2d5020030164215003506c0014a50000d0681c0fe008140061290559090003007462602101c0300c244070003141500103085543d0350350b04000c803007980e100e00e021503a07045a14081c108803084e02c607081110b05460b030131900f035035550b102500250300c3c10550b660b8000b55850341 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 628687122 1250 628685872 628685879
    0xc27040e030c07090203010311060f0d02270609010c080a050408071217031303140702040509010c0807020304030503120603010636050f0f07030b030703110907090501080406111201 79
    0x8009419a10b1503034090340c92440d0f69440400c142e000c280000b503c6140184418421480c06a004000b4030300b03034055240c10100a41440b500b00e03040b140c104414104503807610f05461450000580003413008a400b141446480c800007007801d00680c030000c2905d81c0c00508003e202c0d0007031090303a0041c5102c2040300c82d41c3d51200c030f960081609210301141e940c83c051160020b0034043e00152845980410700000d1803102c2520219040c00d1031500c42c0040001c2003081401684550240d584034011000c00420307807519a120040019200909400454109020a0000400c0401180c1ca15000f044a103402030300c5040000340188517076404a2012105070300c8011103902c0d031480c0c0240c2082c42d18180c0298020481c6100251242111640b00d0b501d0420300140103020030070b200b1070308a000341c64006000896440464503000700c40d002681c00c201d2a44440c1c20341e107001d0740350980c401c41501d0204c81c058603010002c1e02215005e00000c24035070300c898504410b10382038801e803001010008500815540d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 628688372 1250 628687122 628687151
    0x100c1b06020c010b010503070c061a060409020306010e0102031903051b030f0709120309050433180c020c060c01020c0d030c02010e0c030601171504111002060c2704 72
    0x7204a0b00655424038080c4030966009100b070fa44521015240c07011044001d50713485c001400e00440e40c01c22500f01c0d000844c020349609000d80301402c500c42005a0303e0401d140050074201e03034484202e0440d4801c02c030b243c80640701c0c00000c1c0c0c0c0e500d0721410042103035110800c0c0803003541da440421200f2144080100038050344400c501070b0081c800c2e520748148440c0c0340c0340d0440c24044505809030104203010000c04c0f0909056004000440c9103060114510b40300384014804e210300100c003103d0948034203030107000401c070030443d807200e40c2d1a10100700025111080b0194440b0401884580310700c401152007190b4080c290111401c0e001a0b40c2500c2e418203004002900074046059000d00661030801c4503031450000240c0061b0304034000740100700980c81c0003201d40f049109158042c0c03680c080e4101d81e09a50f07401d06000c070300a6201c2d5882c441c202003120144841e0200217903e1404550200302030081003200d400440704441202c001703145c00d0141c4680790150466144022940080c030340500c4210411 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 628689622 1250 628688372 628688377
    0x5041101090803030c04170102070212070906050405040c03020d0f0602041d0a1e0f0f020c010906051e04020f0607050607090911130510090803181f02100c1b0602 71
    0x1a0980310300381c0540d15421182c0e903d02045072100c001c0b010403c001d00400c00f000b940d04030341c14501d40001d80341120682c0480d0ba25040169501c59070380c044081844803c040e170050b040a840107450402c4076151139158201c000d102c40c07001078003038a07a200662041c0803440880f5020139401c000190368a0b070b0b441010760340355aa0203407103143c038007403070404180010554001c20310300b211440000c034441c00d540128800201190a0861503041d901c0620440c0e01403280040e106075002c40000040b80c020b1800d242054031030083c54003190264407820f40265950581c0d0041e00705405032080c031a606c0181c00490498425100080c0041c4640d00401413500c2c1d1045a5809550001c03500b88040e074030b50003a181140c0034030400c0060742641d4072414411030a2454030b845207061640b4080e03040d80c4e41c130014281590b014030030703180c0c4c15140e52004030040c1c14100340340d8030040d00484000808207a034550094481180c501e140080c582c945c44402a141e00c10341903202c1c0d0b002403200308022000d1915000c0c0c0250b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 628690872 1250 628689622 628689653
    0x8090d03171305071a090f19080f0d0513060c060213142e12020403060615030b090c0d020912030406021b0a030b13051005100314010b0a140607060504 66
    0x51003541001706603000f8a661442500f003a0251a60a0000c103000f080310701000001820b4001002d64082130410900103100402010f00c4030140c10384070746a541d41c0341022940210310061160810150f99003004851007601201c4e034901c0e08042002e120f14180010744a001d0019108990140e0085806600f010800604c10030880b035983c0c0b19080c40803c500c803046c0d20100b00100045941700030703180c180500803003030383c5e900ca43c00c1c014070b015282d0b5500d40c21030302281c015000c4d054001c0640b03020280c1521444000c444112001d01c1503160a10b9448410b00c90701111918058004c210300c0a941c640c80003590000b0520030941e070311140c46040c02036a4160300090604444c4c0007891302c040d14207001c00c02006480d00700002c00c002c0d039a101940c2e0344201c2e1b0302604a071a48281d401800d21a5a00d1003120300980082d89064861895402c10100f2103100307400c203481503450302c0c115402d56074401c45400c0449642c08541500a0301c0c58000130f0642c01410f80c0940721038217040401c001c016440d100b20654 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 628692122 1250 628690872 628690883
    0x9010e0103050c180d05100603030f030615260106081b0c150c0d0c050307080a0b090118140112020306070f1b020a0b0703181208090d031713 62
    0x8440400045007900d2041e101e050340d101041200e800e000f40e0001c0f41c00c110079006003002905503215580d10b40307031904842101071990b0382d69500740101544010003032403e01c803c3c0780a015035824184032041290040c0000014403040120036208c0e454005034008445400300c0c400a510342e5541805040c2841c05c031000304031200c14054214855a00d54180c400701d010b800020013000c94800403114401e50090412080c148041c4580d640000090291000b080780503652607490342849003001c0d0200070003800034400b15080542c40401c0da180d07a410203044542c003658800e90f42d8007840c0d1001c010a0070104207148038800000210300b44085002d0300c04554400c3d4100c0da29503450881c00c07500407c44001113400a40030900c8030702003a007404480b40004c2e0004007107024890313071451103104a41c05504110040340004d50402e500914041581008000d000c0c02102c9024542da1a0380701442007402c0305228101210012003030501c070b80c0065804500c0d940c4401d80f141041e10441407142c494000403140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 628693372 1250 628692122 628692137
    0x30a060f06051207050d060608070803190e0108131b141003050403050a1805060d0e06010e010807030303020c100e071707030308040602070311030d0f060e100e070201021306050901 79
    0xb89400e00f5454245000d01c3c2c44050940c2a0910003003001e85841090b042c1c07010f030340700e2001007251682840410018100500110ba1b580062011032604040e032014101c14809000c044d43cbc42640c020751801d5101c00e084440100c2c5602c5441c0019008000d0030881c40d040c414a100480c182c00303c0c14090000a100b00ca00c04075401005900310150355080301d0060000f80144813180d403480c041d03101054502c05488542e1070f510349400c0030802c0b90b00702c3c0040d40c0350b107910f54030100c400400c1401094090710401854071000d6042c002819651160352000a04041e0f00049660741003c061014555100044809215103034038580741c280e80709031a00036510b40c02203d04888281704000980d401c202c903411703140c1e42c0c41580c07180c441500940000800303030b081c030a41d80446040e84000348001d125160907814001038181c502c403030707103411180755821500c25840c160b0180400c04201980450461310f0500b03039161155103580d4200c1c0a8080d01c1c560140c1700c40c00010214800d504003020f402c03094020b03640c030310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 628694622 1250 628693372 628693379
    0x1507150614090a050c090603220605040605092a0105070b1501120203151c020d1b210605040c0308040b04180c1d04020708040b030703180b06010804030c02030a060f06 73
    0x10f04544065624800e03510040086408038180000035550240c4c035000e0008141e541181d44840b440103c0d0f10440f03480344ea03441000b0401c5406d21407150001848c02c01883c084010180981d03034846844009400d1940100d42ca5500384e200e0011910300d258001c89402072428841c181421808103c00d0a1340802c1040c600c84507500c0051090b03911419401c980a848607107034400f4424001601d540b41c8080350310103032100700036883da4030260041510842001105803408903c1e44a05807094002c0e00c0342000821309680441500040000c441303800c00742c001aa07440d14580071034a42400d07440144500c0c0c01003000156000290b02038402c4900320942c0841f00c00419260ba0110b0740760740340250110f4542c0d21007040d80c200d91030f014020034202a00052030b044141c0c94074a11508207a22a503180c070000400c102c1801e0b8940900044a0f140c10101784c100c142d0f030340d02c0c07950941740102181d0421204000203424035104203906050b00d034006d001e41e002c640003410310307401500c03844000c0c4203180c2c2400d0000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 628695872 1250 628694622 628694641
    0x6061821031d12030918040c12151404020a050103060f05190f030605090d0903021c0809130902040f0209130c090b0d14010f05060a030e07080304080f0c060306150715061409 76
    0x1501c0780743d00028103120030b41403449e4542114030810041c0c4400003018a08406001035110714051129910307010405440c0501c1005681c4c00541c110758105401c00c8000c1141d42d401212203810b8560440740341d8041c920756400992a840184d101914156030600e0000a01c01c41760b00980c0100740542c15200c0c00380b5500000e84440c4411f120003134001184a00c0030460f40d110240c0800c00b04e01c01d82c0c9141c40c10540c1c10015507034080318407003402207560b01c6844804610b000c0c4505040c205400b1815230030311b803180d40080d0000030a0305a000a40340c40d0001e00720800d20403510341c0c000d40f03410304082d500c0301c0c081d00c3d03142e0050611001540c03e40e050070380042108100703804904222403008010514115000e42e045002d4090b00007550a54405c000300407d07060000d1000e44090f04410307006207500c0124060701d0f86064880c0c083c0c00d0003003000300140080340e10784108500d00040e0303081085558603070614060a1040a03002039030b240624025001c07400152030a00c8902526045a01054644550491 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 628697122 1250 628695872 628695919
    0x40501030b070804020a091a01032004120609050a080d0509011e020c1e30070f02010c0f060203100e06100c031206061821031d120309 59
    0x500031060801c00654034078411818158854805004000c006595030312100589210500c0c034403000038a03101c0701c034540d42d241c420701030f900c1d040b84200d025403142440c0420aa2140380a07620340c2807103901d04281401003903000340403c184c0c01012510440024204003601c0d820883c0c80c541400d0a01d8042040310105000c1c401c03006040b420010f6205c3d103079068000080d070119002c0903040c040c15103502c0f50004903000b2803416203a803402500140544d80750040a82c1030700310880000c06407250000168442d40c8041d00c1c030700755028505040300b03480e50006032070707110420b20014521440c0151081c1080340c19005107010b840c0c4005401c10703c584500000f44e40c00c0c801c03511540c00010743e0480304013051181d030081e80202c0c0241402e860030250116004189c85540d040000410344038469844500c4410004030020902e10101b06821424100d20240400d1032940180130090b0482d190003540c8032032032204107890f4008100184258000940715143d03004044514810004505080c3c0550030f112032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 628698372 1250 628697122 628697129
    0x30301031514012309040b0f011203080402061e0315090108010b010c02090604110304050d09050d12140d020a17010f081504170309011505060c0d030905030d020301060503010f05040501 81
    0x8200d052a0300740120341181d5003111301d9000283c2c003504402d900326280d070400c090266000b000402001d140610104a60620607840209460300307030f455401c042075102c203605800c185d04881040e5183c80418484028403019241c011150100000740302c0192800014030108c1c076420303111160035030780c1c0c0c802c200e0888820340c003540c0c04038612000030001072600750505540305030001e00c0000c81e80d00c50b0a901c0003c0c0c0007150119030540c0f03c80c04400642d60010101c40003010210f501c00708c0101c5650b00e84c04241c030104822300a0240301e014100007460340500f92851001c00110464a071900c8600043c0102c8044c41d25811440710380d03001050040d9200c2d4108142d59900000f007124021170302003074041e180002c009607207000003a501051b800000400450007038105d0380000c20003240c14038140c06100000d501c8580329a00070060001c7e07000011915002d6010300742400100005036040190440c0b04501030510602c1c800030000c01c0980d0401d002d107040c0c40410082c10015903d03001444204c440c28007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 628699622 1250 628698372 628698401
    0x310060b03040624180f140a1416180b0f0d0e01200703050918040302010b040b1c020a0b0705010213170c0405060402160302070810061406070f0c080303010315 70
    0x4040c4221000c2205c00c2c8110620f15070009501420254900110303641c040321416111041401d04c11701e800103008840540403071202d14090780c00c00031840391490340940329174428041d035510103c0b480703421059040c004100b050355156449506d084991308990100300c801003a60f00d40080d0b0300b68000140708110141c20842840310018883c09484a96a00b2022044041200c10032013080d1540752440d44e1011902d80031160503547c2072a2a0180c00d56000d40d40030b034004c83ca4260038154503a2041c2c00003010500d0218072400881c4140003042c0224100e41140410310310000d8442c080110541c020401500d0720542045582e1300c426144c548105900051841c60340110440300701843c0551199800110042c801450289803020590101401c0d10080d80981c00075002000340e48000d01c4a840031080b00f00c01000380c1d900b007034180c0b075481c0c2401d0403d50103400c0c049540310402c2120584400555000000f401103260785041d0144e596009010842d168000c5480000c4102400e009070a014000517 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 628700872 1250 628699622 628699691
    0x4060b13021b1204061419050d0b1017070c050f0d030b0102150f18010f0f110405150901030b0306090732090601030b06070303050609010b04050303070b060310060b030406 75
    0xb4001c1b00e11440243c61303a4000d400410072015a940000040c9442c030200b43c58039515907540340807600032140101003c900a03807090843d400c80d40e078010044c00700f8042004404915031242c0740101c9800c2c0f00f4810041440c810a0020b0328844000219006e02d09102c1d9424800c04224000490b1507081e041c0150704544552004a0307425006155140d90252807940303458841c1095003049402c1d9880c05890441042e0380311035203010116207018096001440b81205468107140002080141c3c804424901501d0f44c04a17110445038400e811100e48a54010100d80040c00e001e2180381d242d4590b0300c686400741141200402c00d0388a400414144014220f900c6a41e103080c600c10f002c1c440b0401804241090369a815642c415960400900b449a000f503800107818500724040c00500f072030680042841940511040000f03940001c1242c081c1903000c3c40003030540c1c4030f210101c0e10300094119100d44050500901140301120100a5840f66000d082c00307000c00c104244d0b10084107840c115424402a106 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 628702122 1250 628700872 628700879
    0x32403110901290322060203040c06031a0910050904050706030501150804020108090a020a090b0a05061806180307060507060f1a01050f04081b0a090c02031204060b13021b1204 77
    0x6280130303540c0700f28000d4000001145043d042d19805454034821101c2c56400310900c4140101d1400c02005402c82d07040421002044490b04443d40c0450001e2038440c80b00e620002d11250400c6e070444005080107004580799081c14a040381e00c0b0784103400394400082c540000011440c00030b54165184801d40d842c0c85d0b2789500c641c0c004489210300100480c0e464460841c100340141c590017801001800c605600103000700400081011200c2c00c0c0e03100c144140c40c24000c1c8000d0240c1000d8444402000b02d0308243d030707030500304181403080c0c902c5254a42c2c50700070701200161032500312009160b0184194410003203c0880415002201d816002000c1041918003800910354010030017494021104031156043c103642c0c01d0b400d031070b00d0202c2803040903220340240c80c400306042c10407071080902018001441143c011080003907403405024001d82d07400300381c2408102801031950025000080180c00c4203003c0c449800194069800074107500c9900503040070b0100c142c9404100d02814040030743e0520b20700b515 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 628703372 1250 628702122 628702199
    0xf0903020a1203020c33192001020d020409111206041e0e1501060c0b0601051308241302060304020f0414040c0501080a020f0a032403110901 62
    0x74550440c01c0d0b03c11034420352116645c0780d0748071b080c560810741c94200700e10440780c12000d0b013183c4400703503140904144506451036622100c41c10b00a40c8525041282400304640c00f03618411a0580b0840da510001d0590070340021900200156121210107029800b070b18a000c2d04903108007100740f0740300b19103040030a01500d05a003080c00009107046070010b140300e0802404c001c64665002c4120705503c1344200d10410700e18a000507004081500342481107030350b41d840304115a4001001507040117000213803417191400080020015022001c201c402101d44e00101c0140301c0403844440b100c0d8811400020300c8420f03100084450b081d4003404581c10368541d6800e00c85500d001d60707a40d9078032503201d44010703140302e0f007050b03605104600405184420b54602800509030b08005002088494010058a2900d49030f0303038100d5501c0c490030325000480d140d05001b86030850b0200307140034100c0b0b8500900001405801c04036600c0c85201194600350a907607400c8400d1030f841c090303024408820034101d0301028451 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 628704622 1250 628703372 628703399
    0x50114060a121e06170a03020601060324080102030906162f06040b01031712070c060e010e030903070b120705070516030b0403081b0319110d06060f0903020a 69
    0x30305100c000304100c1c1100300341070081050102c804454a44d200c00c100705c8020503a43c07910601c0c01110240004804a860094513024140a00000d050f107610184020140050660003241c0150084100c1d0a843e40c40c194040c6d442550350803000d110320385c01705900c1103594079501d14540c612f4558500b0805003985004e004442890029040784583d40141076008007404507900c44c1d8403c1280403030640c11450001b4080003983c0304000412170900c40d8690245100ba4a035410001e203042040340400383c0d2521002628544405030705d82c1d401d020340c1204503a400809400c201008600780ca01058a480b5504054014203403d650a600e0350404582090700800003800303841e010f20143c80c0500d07480129009900b005920844404640c1e004220a0542c800c0c100d0340c00081121411082140464102500e400b018102d10b8401d040d40b401d2030344d0b980d070650000150060b1f44404540366104211550001c2c0b2103481203001140c1d108032428205d9120b0815142030360b600800005009041000c50176044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 628705872 1250 628704622 628704647
    0x20d0305220e0a11040803210a1e05060d0606090b0a09141b0705070609060908060f010b0901180803030a150e1501030f0f0f0e0106080606060a02160f09050114060a 72
    0x3c407010040400d01e00801c1c8010504801e204070707d09014a041d012410010600925081a203441c0c400c561013040c0003241c5c141c542c284002e10104bc151a1000090034202e21124010001454540b000030807150680228000c000d080b82e0540440f6511405001980c00c00000c074900c522a0400207100403586d0741220410310461b00c1141e0500c91070707a40e040d2030908550407a4020038207810b010428070340d21041c540080d00c0d1074806404141484540350040070010f002c2ca1015134008544940241d00c01c02d440c8203131301402601040d0807660b642a0503100ea20603034540050701c1c01d01441c800586d4041130b014007255100c08540341207665010441400e00405503003203040540300c0b5240300071907080c2d0080b14010844314400041c2c0c2c80d0380c0700030300c02203c1c0e80c07181103d0300d40d04001e02004401c2012071030a6000600f41d4446944010082041b41080540802490700e6043c401c404540d8020142120303082c0e40faa150100300fa40d032100340c90700b12592004109075001d5400c00500c0791040c070950040100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 628707122 1250 628705872 628705901
    0x50f0603030a080f040c0806010608061309030507260703030902040507050a0918021c1508161205012018030714010c050c0901090e150403080c0313020d0305220e0a 72
    0x9060f01c60941d08c2c1030180a074451000142030409000961600c091407030b9400010443c00c100e092aaa60090050300403401c01410080e482004183c2c0c1d41c0022901e00703110180035100d0707662640503240190080103078940070303400303a0300e04800030f480e2600403011500c4c001041d03140c40c074046180041200341803210742c0f102107a842e0240042010002180b13400b2000c0400d180000c41c0d01440f1000c01c03a5001c000d5030102c1c4041d803000c20300d8200080c0c072801c10350655038407070030650706040b00d0306000b405810110010200003060020b04418020702c0e1002e801c111103407140200e48908481c0801d1b580c1d50403400340074800310080303a281d03015601520920048038460001c1d9240c28410000007101c680c000d074018001d00fa03c6d510800350210b000d0009100d61420b50034030000030700303140d14028088940207102184101000000c100502140d21b40c0e1310544c0d900400c21001c6420f01d1030003c210350030031500c0c5150308030045031a811405040001a00740d6040895411182c1d82d55001c40b4017610340040100c04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 628708372 1250 628707122 628707143
    0x40e130503070b22111002032203020a0b120703020a1e1115090a1e080715050c09030a1203090507090c080c0c0d030902010918050f0603030a080f04 65
    0x544103001800003640501e11802003442c00044414500e000d13018502580010b24961a00007140b514520401d24025039650f0b190410b0700720180d03d584034070f0b818440d0300303980319a41c1100000384807100c1c0c0640b40b01303075a400121a41d4181c070000a0150310403184408a04400040c4002e00c07940c06483c5c40055807501c0d09840b0200000e82c042940413043c01000030380345204510101000b08450b1600480705a440740252070f02d5003003a5107401001400800211807103142140c0c00114908402c002c9810100803a0b44440070710304500c0b00030385070f0355a203040f600340310029903040604820360b41c400c42d015010b4105141c543d0f0b120f10044800020034428103944606d8440482c3c4100800340107408040000a454401c3d42409032054800900128410001b0408440b0160001c02d040700d40c916030741001b01d155840d91005031408142c9400540c209601c1000c2d040c4102c006030031007401401c404810490a844103000e0540340c0c4180404107001c039007400d000c12816050151f000c1d83c054000c1c0308900c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 628709622 1250 628708372 628708411
    0x4031e02090403020d0f02210309150106030b0307050108150d382d0c0906070302030a0f0311090d0203010b030d020a051603020d120905190801180503040e 68
    0x101038070010380e819030041c0d001c440494203580c3c2021300c52030070346618002032025078801c4215104a00502042e12120480803010030366002c0b0812581035a0303240c5038008142c40d078403035000400406800d210380b4442d218001c1d000915500807100c26001e8195281240324003182c54050042074400c0b0b0300100c510f005c40781d21841d4204400310207607a00403240d20444940c2020200120264040034040e00501c0045280040303911002c0e844e81c0007a040b07050b041010701e549070120344650f4040c0a03802500150006608020184e02000504000c0c45986500d03010701c130200303801c0341110003070030554060440820883d0040c0c64a1800d6100b407a00c0100003044ca60102c0012a003071a50010044015a011340850300400c0b400b0b2020030074a03102e0844003803c1d1490f5400040709440c11000181904641c0c2c0c0414296a11031060301c405488007502100741c44004003a22180482e4034862006c00354030b0034a00c0c1082850f1074140e142d020b60044003c500301801e003000030f15940c00150040c1a01e441180b10b04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 628710872 1250 628709622 628709629
    0x7050603091b031c120b040908090102061819061113030b071d040e0115081f11090f061309020403020108091606031505030f0c100f0504031e02 63
    0x11481200c1d07800140c1004860150300c0c82052002d1010103200781c01c10030700c68070441c41d16034030240104810f10700071402c8414003620074010119040c500382c100e801d245100b400d21007054001c009d40f02c001e908981c640e43c4e41c04c1d10714107100541421581c0c950000d2076a98040c0e0481e1082040e400e018080c0000d5480000c5146407031580022220a5014002a010070921009003051980720615041407000031110080d44103403842c0c1d006000b807013940e403240311940140c0c09520882e9036000d46002c0c0c2100f0783c2c0384c112056440c0c825060b24841d032081190102c3c00e4000c94041e4070020070841c0f01c2d503401c044041c42001038904010710750681151040c0801c41c66840d070b08203440300415503001c0041e9140e0450000400075640141180c000e640016429864a5407080c802c908641c40d616000401d03100d507003417030b059610340c0d640055450f10030101c0e002440007010803d90620302d400c80f210040b40c51054015200e03440300950420110381c0c01c1c802000071503260441c4d4140e44012141082e9100e100b613001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 628712122 1250 628710872 628710877
    0xd020a171c0506010908060c03130c0b07110a120515041a0c0405010905040207080904111c060e010602060105090a0e01110f070606140a14060d05090a050c0a06140a02070506 76
    0x1c80c04680c0c9600074401d01d035030840005400303000b00002030f02e01880c11045c20a4184400381c051030303200041c21300c11400d10403403000d0700010f8084510015034814190070221200300d95549010302c6164440000502000c5149030440403941c03103800f50007500c64400c0030b06d8044000400c00d85604a0740f201c40e80d913020483d0080c500ca4940356407169103480c10400010003221164104a00552042017008003160ba22070984d038000c201100c01203200da005048100d0107000358840c0341811006c0c048100c80c0401280c2001c001c2d5000108004002c1e03030b8800c0126a030320b0080c401c01d500040001c0110b01c46161340d401035800c280800c3d0021a4100035041d41100550050304254010f0710017140181c01c003c4076001707010040c40c07810344071a0201c0207100065a054064801c81000702e001607400411a103490707040e1000c8407600300041140c0d15150400ca62290f4050108907010b00813894450320307a1401c04902016284503641340d40c815183d11201300202c1d4003100030082548503409001500b84e0f02da000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 628713372 1250 628712122 628712167
    0xc0304080a080a0201152105070308030112260f0a1b030305011e0305030412050a0c0321140a1413060f0f09080a0f0f0614180d020a17 59
    0x4a80c0d42c000034180217007128034212001000141c10142003040c0c040c201090541134403110440e40d514241c07450f1062030b003c0b05910080941901100000f0b098260b0360020a5150103503601c2c4107a0045812040c00c40703116201041c002e61403d04c03c03000000c40280c050100300740a170400c100d1303c0004071000381d03a000c1c030100c04400280e160070051103080240d0f84440c2d0350078040300602e0780150850b0368a64482c041da01a41140c4d8070402c00b000d06200040044040c1503802c20ba0641e0341725100c2c103000004040150b406011320300c0c05204148c000e44110b0889109208100095007012030501d0201d44900c1d040381560b01c0d10406105d4000c42d200761403402c6004081d03580b02e100c010001108003814042381c0142810038094a440204141c040c04914111035a9000f078007010118050f00e40350131007800c039481c0a0072562070301503400d030b5025603528a280a148020007050b014035280d0034940d501d001402c3d04000507080001c2c8000060508006c20109040c0009124203180d400c0300b40c0c0024000200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 628714622 1250 628713372 628713383
    0x2120f0a0311010c08010303030507212007170702130c120606051606050a02160c050a0b1615021903060515071a0405100204030807020a05060a090b0c0304080a 70
    0xd51030805401c80c22540709103030544024080d02d100b01c4809409208144030150170f15403100700141c1000e1203440100c1180003c40c0940120a21400c0908004c01c9501c09122006800c2d40c0a41c40d0018a00142c640700f560003a20088840050700046146800031041242c01004100c07040c003480643d80140e0f900b00181355500540c904441d40c0941c1602d0301a4840024400204048480c841c1e007071010044641d004880861243c4440310440c00901c20311050544800d0950310170070400484012800450388229442c1c0440c0e502c6900e03070401c43c4580185c030f02009800f40d500c0720015181c841c0500c031001d40d0003001810808826007003591000400055000241c2e1108188664039010550000032640203001a00700007203a5241c6600c5501e0100c5807200d000d440c0c00180402408204641906036807000170744d1110340d203180201503a080894202d20400ca10303100401c250404100b522030882e540e2351044081c134580030b50b400d42940400301e2210240020040030403116010411034082ea440345 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 628715872 1250 628714622 628714633
    0x1c12020a05030615250212030703080901110325020c0402040b040f0806090a1e0219060305160f0e010e04050c270a0510030e01111809060d06020702120f 67
    0x400800000c0b52480160b01d0010000f40180240400382055a070700c2c40003c0c620b0031841040d14000100601f1180c41729900302e10000070200c04140d07100741028000c080010007070141100e801d040182c80c1c0001c40303150200d028040c540400c4034003020900c00c2242154011344042003003000101d03050b0391054001d880d41d500e00042c200400314441409170014a00980030700207030b0421100b219110070300d04901400c80001001060868003903500701000301580280924081da907400c6000c810340400d0710a01c808a4500b030b000468038450030810040107641507494400b805c03aa1401a904240d9040d9018100940442ca00c1c159844034452103009091f181e000b141c60305910302e0703500c501c0c00002c06581115100644400025141c0c48140c0c4180d9200700c03506904600454001c0b0000d19603c09200415800c214900010801c010002d00d0701b03801492071003a000104405120001000741c80050f0171407101e0340d000000c07a1940d4060b0800510041025903283c001100c158600018102301d038070940c004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 628717122 1250 628715872 628715881
    0x3020d081b0d0f240f290901021507021c0c050d14040f08010203060a170c220504060506090702210d0603020303070501020d1808030a0b030118030203030a0c08091c12020a0503 77
    0x21000c20001d0854a40951b801ca10711910001e401300540745014800e2001b040f1030580f0f80c007d0102019a1344001202c00c0185090301e0020340e140b400c00c0b03141480c40728000e96240240d1181402500c01c540003801041c19a03021031044604d42c0002e0b071400301041c0280408908511144140401041303007800160322400d01404000b00c484442d40700000d04500036031016000c210126a4041c00e400842d019110305801d140d2500701d28400603405258146041c0400c0104001540054029001034414500c80ea50b9440300380e98420002e228904e0fa1715205424501205503100140301410000b000401d181c0d0b507a030302080c81e5800201007291030b6500440d40078880840c911810030000d00e03c0764501403168154580030701f648409400c1d01c011135110304d10b8007210345094001d441c0c4800c000450010480c018200251a90000d40e904d20081c1d0402c03250715120361042d20000d02400f650009050628000c24042c0f68451030341c904901882012114480d0002ea2880500352040d066100c2036901d141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 628718372 1250 628717122 628717139
    0x8060f150d0c020a05070605070507031e0c0905190e030909010608010608070509012a0510090302010506030c01023412030f020601080d03180f03020d081b0d0f24 71
    0x40d0590000b15445101c0702808031701c3c0081e6640c04c40c1d0650500316946c121038202541441d10542014201d0003001e20b91001501c0c400320700c903403550b0180d040720660720341320034601060b01c0007503481030b003510034907640344030f03c03040651000c02005800b8088034a0705420f0000300d10081403d80c01040450791305c00c010000b4035040032896600070f00381d24105180c2600100043d041001101000c00340500c3c08810000070480c408040d41c040d40c115048990611440243c00003070b00e0003501c2100103509000c0404c0c84d600b00020710301d22402050f0050410800c1c1101c280c0304400d210100d81c1c91100d83c0c111007034544031070141c21030060400d4120000902da294200500b29190031004101103500240041001081c046035480c00010245000708407110030346c0806000c00c07124540902403010528000c8109900007420790f000340c0154448002c0c90352150040300182114400c2d50340e03440c5007004505e0441107a54404201c0c01c15050002501c2410700954131008000c2003a42c0701d0980103043c09004186 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 628719622 1250 628718372 628718381
    0x908060907080d0509030a080a020c210106050a0e04020405060d0c060903030f08100b0c0c030105130303050606031306020d06080f071802090105161103030d050406050c160308060f150d 81
    0x281c00d00345217103000550408641d890301e03040c4001e040c3c0207012620030061442440100101140200407280c00d5039802c10101009000d000744009940c42c0074000030380c6e03040a4241000719022281d2a00311550f40350203010250000800daa58002d40340500d2400103440480c95030090300e4180d40e082025801d51801070085000042c6443c1404501420030614203945507072a020b40e99200405508d61003006400c42c64040c83d0b00c001030340741d400d000811102000940480705000c0c000e035014449070302d464061005e81e210a452040d011881c500c5440041500c580003400810b80000d0001056903075102124207140701200031141981020b0b81c02c0065000400d80603c403049175000451510b107800c2c0010b01548510054506600007034403000e8144609c02c0059078008001806503640c500e03400110a0040400300c90884640d407500d008a40d0740030300300c0141e41e40d81400d00345130500c05c10107480c00d03036a0400043c001c1e6409440c0c090215015241c60040b0360000d072a0301010b41d241c88401c09039400340c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 628720872 1250 628719622 628719643
    0xf011a03150705160c08010b04020f0a210207030305090c040c0f050a1701080c01080603190b061807091505070f0b090a0c091e0b01050f1c0203150f0a0e16090806090708 74
    0xb4ac1c014420001a21406000c8a102602e181445490a6074408240044a0410650300c0381144042440b0b0149501504091305c614084c900b61003d840130b0740200012145602e40d0540000c800308922141c0c140107000034001001c0074100504c00d60090790121010440981140b00950040c01c545202c6580110f0102d1300b0000407006011503d8031034510704110044050007a01c04e0a0900c0410310940b0b0b40d030b1a400b1441e6501036402c006141c01617025018070314910481d1242c1c4140081600c00030302c1a01a03075900b03580309060040b6210240c5804010301e01c041c1c00c0e00d8a5014a040a4001030145034130000140305d0b1900118079040ea21b18241240720f581c02d55046210b0230886000f11a03030703018049498210303805a2480e02c84982c4846101d0310040b210140301d440b8400001e00810200500c80f0389185130048481c2c0411a4030402030012141076440b8100a030965440400c407d0713a96820100c130400c1c100c1c85c201110319aa0051545015426602c0400c1c03a0010b02d0140008201408404500e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 628722122 1250 628720872 628720879
    0x503120c15060603061c140f060906190905010b03010911010e0f030307120224010509010602030a020a06020c01090b010e01090b03060408070303020a110d020f011a03150705160c08010b 81
    0x140c03074000040f584503c0b0042460f4440c4020400c440d1014500440c1105a117401c814407401149480c401541d40314644020050b0502c207d07030018030701c0d070f00c00284584102800e20255202c0034010810b40040c01f200c0751304417071554985480482d203441c00d215840c1060f00030848030016050020024120780303034000c8014010055112132508540b070010449018a50280140d491410646002c07401c21a12024091410308507100c49210001d0708825641030b0342d4100c645c40600e91340c0d600160317642c1c8070381c041c1c070b602503003059a0700404207241da8060503564031000c0010032007175119962260320036000d070810010ba29400c001407000301d00318401c040102200350000e24040c20552100451400f5a0380010304040d000910014514821450416550345007130880d407511542010282d2101c4075010400031961030404d480c501d01081d1104c0480440340a0007502d0301c1c0300e20703c03041e02914a0007070403031050003c1040340310000300014402280b13903805082d2038004d07a03042c42d0805081d2251009420320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 628723372 1250 628722122 628722163
    0x216050a0807030f0206040803031911030f04030e0111010c05070c08070302061615060b1902010506062d030106020706020f01090209060409061e0b040501080f0d14040503120c 77
    0x14141c00000c1032010b90f900074007a000c1840c91403000503981e201e90b410015041c04007005200c3e401450000c043c119103001c00b07040c4240110070107c3e01c180e0000b107552040b82803451001c1340c0802d020b1450f0000d219018500714844c3c40e00010818251201c1ca480c8100181d0300049980c00e0083c1070700100701405459001c1c140003455900019240d004041c0d803090050810403140f4100718000300000084540c26100f40200340d5034500052140d0045070b025070360200404d00e005c0e1003d02c18850540305002c010805070030301403040c91150810301d001c8000e4241810b00680c580c2e440324101c018500812940c0d000306180c9051560003030800c801e03608010320a80c101501e440040e07645030110740c0e0041e41650005a140d074141081005061910f410307101e80415480c10f4150b1403125005005030240030f40d003d22181e684d038402590364503019124184d040c1c000c0104280420b119882030b0303c10104107081d582c201a10780b00081c1c02c01455a000c8400f2880c00510101c1c0e10358244201d15012004441815 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 628724622 1250 628723372 628723379
    0x6040f05210d050c010b09010905010303030e1216050f0a0f0c08071202060f120406022a030306010e150a0504030b0105010c050c010e03150f01060905030a150b01050c0a030216050a 79
    0x340e8485003030310880b0a000f000316803140d18150950084129000040c0760000c203503074504c2d81030020882800140d001900f0030303401c1c2e0080d800005003001c0d2980c5101d486480e180c45000e100031002000102160203008101c0006081c503020440860814000c0000d42c040e01a9440d04990707040311a1300c184e415400182d0208100b40c4881e46da00340a5406544603640c803005541020710301c0c41a621070703500551945007400b082c0040342e405000c50000b0030345500000c0b8844180d141360302d0b0f0b080c0d4006d03c0d0750707004100144e01d0354498180d81c5912000a48100980c0031208110783e60f0703400c4444d0185c005031001c2001c005120380040600c0c0140b8082c00d2014801441c1d8a40319100c2c2c0705035241c54103025007160261b05139142009a580c2d1920151980c06540c1001303136400c08a00800c0c8104c00000b200304001086074a00800e070441c2865204524118400300e21110001804411032a503061260521403020b80040038050307168034a22960242691107030030001c400100d01240c00050044198441c1030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 628725872 1250 628724622 628724689
    0x2d090d060b0913170d0609050a06060e0a050a0909170f12060a0b1e0c070803040806100b070605040f0b330d06050c160b041515060c060b06040f05 64
    0x58004e6150704426518240410003102602c550780c46000041e20b010708000300422681d1042c0151905603841840c54000d003400c11058000c1c2d809030941c0046d0ba03810410040c8602d40c0b00f600d44a200b03070031426400d8000000501907422010460610801c00680848103468031080b4a521807404c031041201c3c40c0c2040b2400b007040c045c181c0c1d80b05400c031281c0310144c07030021203500b075900d071034006004c8413400d43e01e0343d24071920b98205e813140107154480d01000c9400700200482c00c800303071400c0d00036050400c3e23a540c80c1c1c600a014040d0090f9684040320071b640002c07820303060f00588140c00c09483d20f000284244101070074510031800c074411a01c030301c00e4a03c400b0350321648a504d0a40e04004045019140d4030881125480f42101c070721400000c910003c810080002800d51240d40188003040141503150208000d841400d1420031102b60100e106002540c040c0442d0b070895401040c001400315000408503106030703c29004004003c40086007001945042c2c1c0012101250403030b1098008aa0682d80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 628727122 1250 628725872 628725893
    0x12090504051608130b0c04080105010b0f031b040b1201050315240f03030c061f050a0320130506030d031e05251d062d090d060b0913 58
    0x80380100900d020225048139007038419481003a41111001c1c0450038100d100011a41c000e10030001c0950814000066505440c0141c50b0107454081c007261a5513240340005100004210341034052070b6040c04041001004030b80078228889405100700034550401e000c0514041e2121212140a44044100207000c06405100c40081c6650911125a040d00c0400240d948601720b220343d42500c00882d4644401ca4000351483c0500405d101641c1e10b40d480180103450388840e8000c1c55084100c0760000c200140c1c40440304090f070010b4568002406460000007803e00703c002c1e011075207150302d840c03d01190340380a01036a19110761500301040081610321168054000c0c001722440c05a81d50301c001440744030402d03c1440034114002240000c4044450b0162075045d9142c6103c600c0c40000c40e6004260502c9011105405217840c1c50100030000c807800346408001510303e14141c0b41061100e00d085480d0080f9211609101d05da0108100c1d40810600440800003800000c4c0521603d080d0000710740030044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 628728372 1250 628727122 628727161
    0x606030e160521010e0a0c080a030f05031b0703090810020a090510030e0a03030204030314210c0412050a0203012f09031c020c12030a0f1215031209050405 68
    0x1140440c8219a00103059a40600303e61000107500b400303010f50710140003068044640d480340804040e4144c55454042d594406a44024013203034042171750594071030082c405190f000200362840c010030150702c5001c82e1181c11252084000c40c3c11607100f40100e000a100060030780e19850300450424230303402ea008101e2059480340c1d41c001e1110340000c500d41c3e4825000000160f03d050211039200806140003002036002d4801a40014004095a0f0400500200b160408803451116051500030550268a00803011700300c1809801c04001c009000a41c01c880d81c12803d015501404421340180145400d44100c2c10f0419182c0d034089950b2000001d8241c000b049056400c0070594071520f118000c6850440c0c90103101c90b48031202101c0c00740d0305900248030f0001d0340041d2841d500e070708000800b1583d24080d8240400110740c0032664242040e11608148040242561001c16a40c5081c5111550901c041c0c000380c48145501007055101c2d500041e0701002031000f40e804202c2407802e0140310b44415210103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 628729622 1250 628728372 628728379
    0x180e07020a1103010e0601120c06050708030c16020a080d0212030402061b010209041e0e060402030309012a051e1504030c030c02100206090c1921080301090606030e1605 74
    0xb10304010352401d501107000004c109040740c2440d42c40321030000000c840201c00300c44c000e0100002080c243c0c428001e84280f2907015240701d04645400354a61300304d40003200106c0f10201c450f0075080140c2d0316000483d0080c00010094051180b11403802411b000c04031080b030f08043d204000340001600d0301c2c01102d250a030011802c0802c2d030a1440d0042c06849800e1a0315840390800c811074401100404000141c034003001400c024200c0a03103100381d00d900049a0107507040d0400d210425055009800540c000c0c080028940c0900960b00f40500000d414500c05480c907511070075181800c042c1100e5032802240c035820081c407401603070204080f00520001c2c401010014902d12003000c244c000c05c0c14040042d401011910101080c0750300940c0c81c2000ca170010b40d50b10605c084140142007007000b024240e0640c1c16a03500032030905400c84c4003925981083c003907001c90600503c0215403000082c42c007031320801d100402c2107880c013000202510791262041d14241c0000d100006079900e665a0304080f61030aa = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 628730872 1250 628729622 628729643
    0x803030103080a110d0201141303090509070c082206211a030a0b061302040b0f070f02120f150114040906060b0408331f0f06180e07020a 60
    0x414100c640c110f13a1307011090503229a1100324001754041d0011900d070320080c1c800d103038641e8a4452281654100f9a800340c0400c1c00c0c1201444a42800150140e120380581410324030140360350345865507640004050403c0007000b40f0340c100c0c119050f030b428100038103d51600c000f528210001c00d40d00d0407601440744030380347d641d11104058100502c902000354440101a2005c624103820114400c41045800500c107810b1142c101d00c5040031842910113a80900d0040c0381031148800140c295640300c001c05440000000d9500e00040e030700c2c011030503070904108000e860805207100c0d105103008000d0001c0c190340b0300c0701001400849840c200e5914010002c075008241c00442e81401c034001c02c8140c02511f0002400a0003203540b450003d20702c015203144a91003810400e4580c2607000c60340e99010003e100c140c62a000c42e8800100e04050b04601c0031205041700007954400e002540070466500000101d80404c2103000d10307030440480c940042440705108461132800d50402134030341c0e180000007400901c0c407 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 628732122 1250 628730872 628730887
    0x615030603071809050f160506070606091104030606120209040b061504061d06070b01120c0504020403060b040c02011a1011101b050a020a06020f0706140601030e0106080303010308 79
    0x20032440d402080034224102d20800700c00f642d030025000d101c0c4255414401c50640400a485c00500640b2210030040c0054105040408120182d403040c0020f9400c25143c010208010800e84604990602c4e0340001990b41c80c9540b410100f600c29507800820080800c074044400f43e299240f8699100d540320243c0c0a490f40d40f8400504500044918070f103000001050110b80c0c55002201c401d01010308242503940c1c50000b004001491182c140300400c00d02c4584010860301c0304003000e035030321544906005410207441b20049012030f0440d078416954079448040815060400f0f11a001141c005880203201c001140000040d814401e1807016000f0141340791118109481103812000400e14901603a039030310b00594070314000d000140110b40a4291052441240d54012402c86103032400e2074018000498450311004029040411010f0203c030040001c60002034461041003400400443c2c00c96a07818014001001c4500c0c0150548d1030341c2c9400010320061500005890450b035100c2c03221540d5108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 628733372 1250 628732122 628732129
    0x31062301050d09032d11030c0a030311071703010504061410050d09020603161103040806190209060a090f1707090b010903020d030e01031a010818011b120e0606150306 73
    0x50722405c040c8000410320b03490004e0902021202c0082d1956035030104000f16107407509490344115034a0b02c0c0207511881d076660010740a07402c0f8030124103000803d1420140c250b11524282c05405d007146000410002c011b008501d068401c10b4003a0160b54244000c0145000208408c0314004c680d81003403141c04581506a20701541084c41d0650f40540b02907141d04140940d5800b00034400071800204001014802031200b0000584089600400050070f0075152103484202a0001c00707595001c16400b04816401911040300030720021159a0380c01c480b09140072000d0207010cc081d0085180a4601103046144620000d88102907404482c40000c15484ac2c0005a4031214990710094000721281c400f501456084030901c2d04245007a01c050000d1005c0341080b0398425050340c94280031544d43e6001c03c1e10305820200721041410000d00000341c0d00190442c0705070350201640c100d8000382d00e4840c0e03100522005c0c002d0040b404404802088a800c000b0009126466681c80381c515503500030001030f0017a80e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 628734622 1250 628733372 628733387
    0x1805150f1c0602040e01060513141311030610030606050421020d0f0b160c14010e010e0f120f0a050c0106260d0206040b0631062301050d0903 62
    0xc0034203058060320410702c0c2600c084d4125100302d00c0c09044074070000800ca07008000301c5001c1281441605030b41828008c40441651402d0307801078100b90143c7d10fa020061302e03841074243c12083c103a45d10340c407443c02c001000321207040148090201410018100800c50b0007030141ca0545d014068880607082c4590341440d0100c0d84000041e61000c215130740351003030001c280c0d5030584443c06403010072041c3d40d8803015480c49a081035200c00c005295540c1c098041440c01400c0000e04003040004140201c400b106182590782d046400c40e015080544107a1040e9000c10286c58200300a400841c20001e060740707103021030301a1040c40c1c42441000104101c3d500002e50040e005003104c0c100484245507500b202c5c0303440608481d20b624081c851540c05000060000915034070450744129019446c0d507442c81032150b6071041c1c41c3c00d03c0848102c0001c075035145040015180381144ea8810011b0b06903d040e514038024a90003100381c00b0348810700112100d030390344a4100e4980c008440008905502c141c0740480d002e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 628735872 1250 628734622 628734649
    0x30d0e030d0509030a0f1103120c060a02030402062106030705010c0c090b0a08150a0e150415020c0106030f02010216180902010e040f0618020c1b190902041805150f 72
    0xd5410b21b03041c0100f04010038140c65101e000e03001c0f5000b4404000a0242c244a000c41030750082d4000c81c0001c80000b00c0f50000c41c5d00c907201030000c43c2046403010424034401e000054006502c00202c1c100a05420200012401003a091900090f18070700c9464000080c0c2c1d4901855030155210180c2c003040c0d8036911428002400403d0403260f02e4001d003144d160b5189400d42d407001c0641c2c1441c05030441c4100015607a00d20140c00f071044541c54031250b039000300385180306d101c00410a409000c40c9584210a1003010f0056019440c4d814143c2002d00c002811706551240501042800302e0081c402951104100e080e051683e110001d9402d156000690300041c59400040e0301c5800c000d4640141541604a4400c076494083c0500c00b88080b1300f032100a9004440000d02d003a4445007035101413a903500441a80803030043d1480b069610740d0b02000340000c1c03103500b00800c040d400041c00c00a0403044202c911411902c50810010307420110403444554143c0205c880c42241c3c0b1820310b1307a09584203817a51008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 628737122 1250 628735872 628735883
    0x209011406130609050a240f03150e04060b1c11211f060810020f0c06091c08010b040e1005090910060b071a040f050102030a0902030d0e030d0509030a 66
    0x2c032a03480304000d1542c01c007402480d00640c00392000180d48800c020074106885a00707440f00290246852044443c1c0c403281280f139040548659a090b0540c43e0340c20004050b10001c204030b2a14a001e0500304169404000d20b64098421440b1940c07001c001014182c100550050407100303a040c01600141d80202000c2042100b200c48961801c480c000024940c1c400c1da00442c0401000040d00d481507040341c1c4070348a2002d80790405000c4041501d0742c0e40c014410b5000b181070690601840c00c2c015854a14106d40300c40701503000d0341000c035889503c00c204801c10030140c0b03405a00b41d03040200025041c05580701d1004c0d58040d420115003040e616103030490180c03501a01a00c402e1500c44410b981d501040e402200e1034518004c00450800340107800c664001d81c00c02c0e426000d840458000f04505000103000740c64244140c0d464030001031081c0021802003038059808103a008280c01058181203601d0b540c403040c441e15941c0700d41ca98030042030200c01a001170a1403501d44191201003400c01c000c2c07141c000d00703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 628738372 1250 628737122 628737157
    0x7020111240105010210060b03010605090301060e09160f0515030c0c01050702030a26010b070f0b070c20181e0a060905070f02151003021e01110a0209011406 69
    0x21501d42801049040700c40903802c49104003a250b8481d41220f01c20701620581d100100010302142d4019001000b6684001d400003480c507503104080810000c0540c0c440c007141c2c00c0b0540e103d40e42181c00c0c01500c05030503101a085140c0b0320701130016109100c0305564008101020001411400e0507030203031344030046000700074069031030400002900e81e80b110484401148090b038000b96600f100750b0700440c0451802032541400e07402c0c9030f042c20140d0806c42c811180c40e80d49004144c0007500e8500303500d0245210303441d0032081c84101c0c07a000340103a040c0707052203aa08010011a890f5941c82070841e1644030004c0c0c101e81c0340fa4403580f04001c03c9994800c08039095200010034000098004e52001c01150354418040005849a000403503884140c02c0181005070302c00d090b00c8115040e4240300c15000100e441c01c94001a03a07aa01251284010180c00100c1c030603c0800b9241558100711084e00403117690b0007900740804a540082d43c8001306005440404402804180064032241e045400785400890710a2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 628739622 1250 628738372 628738423
    0x9150e130c0305010e0a0b070221030a1b0207050a12021c020f1c050c01020604150507050909070f020c0303042303250f0503060f041209030602191701080307020111 72
    0x591b40c078808042100c000c0c81e040b0008042034030110301e03009a100f44070603080303550960620424031500081e0030300072903a5544d0084450a035030909085110741c1c0c1c41d0007908141e8640070030011070801d190b2140c1d040c0402541c043d4010703940c1140d624485446c4103103a40c4010740380d0021032190200c40c0030796a0882000c1801420400c0800c3c21072000a03c10000c903401400c420004a8032580c0a4074010b00292010300c15240c40355294002035401802490018240300c0c1e4403000400002082c3e9540010880c484c000c80c8105506004407106e022043c1c008529081c54002010424000e0b40fa808024540d6000c007400c2554040c0541000e0f4074031010ac007a40c00344505c22141c0044101e00c2090201461070200040504000c190240f2408401203400368503912030715056801761580ca40c1c0000c10100140c0400020082c0c409442e05045003080c00700e8901c418040a00409140030020050094640040102803c004201c0c0c0302c181c2d080c40c2085030206840c51a0749803003040d0301c400e0038041a40e100d05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 628740872 1250 628739622 628739651
    0x905072709060605090901050411040320180a0f0c02030901050a02070b0711130504020d0201030209011b0506071b11100c060f020316050a0215060d0f0c09150e130c030501 75
    0xd00c05c200c1c00702e5110f04103903a10010001251039028a41000841c2840100046180c034015680803100c0000305101e04d02d000c000190100131007484e4902c408410606101d9075034060710a840c0c3d180c2c03101c1020801d0b003680c254041c4d035030b000340d00301d450402100042c0c107441e0300e04c03d000701d800034002101c903e0b448480c0d91a2203940c0200301404507004a282e0b00080f40410481d0040d180144c0e0090300da4a06454190011070282d0301144c1a941032090354146a00313266441211081c0d040d0081000e05401d0078001c400408010752142026250044405060046001030703031400c2c0c040d0021500a800c01c00b50f40c00030303511080c007400301404592410308113441d0400903800075071061070054401c00d104d4031307090001d8a40d40201c00030000113038480c090f1403030400702c880d0301640c0000004151068404a07030307071203000180c51040c0880d008030503584200241030460144400c402c28100020704254181014102190070040ca030071307161692004200223104a480d1038102443e0080000d001105450a00c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 628742122 1250 628740872 628740877
    0x3021b0604030e09041713210b090703051005040606050607050313050d03200f19110f060d200406050304152904020d0212010f0905072709060605 64
    0x1a40440e030001466070a81c80c14040c03545c400c0342e2041001194880800c0140b13165006400583c1c0000c8410b10041036600802082132051022088040704414851030100840c0c40701401103a01b0380d014050910000301d0110b04150980c0213903a0010b84c80d0b603582001f402a01440e40140d810140000381071003071040100040c908032100100003041c2c156204140004965102c002400084003515101c01084001408a03400c250140803900406012003644d400d01c5038241a01c1c016201c001c0c0100108070152102d210208000c4030600004413010021400602c20b031f0791a102082e980d82000d0a14481103100b44252042c0060040c2d21342d5161200907000ea8015941524002004001d1407c040c005025022031740849080310144c51030342c1468994000701c103415150340240c0031310042c284901c4134800f420240d585126a00400d52424088054070f2549030041c001c1b003410481007202c216085106d01d100d20740300c4654541002405028125240e40c146c020120300340c00c01c1d80000d14203501002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 628743372 1250 628742122 628742131
    0x6110309070b04050f1908010f06090501170a1b0b03040303050103050114070906050f0d09060c09090e07051e09090706090609030c0b1c050412030b03030703080c0a03021b06 76
    0x80301c41e165110090080203000f5803140c1a03000c0e16a1100000c1070518030314110301900000d2203101c4840e11007002d50300303603072030b0f0314420220075030b80c00042200341c1c032500817240101802c0820b01190044060f0607921280c0c0800080c2003000792008048000140c10f1246004203410b8030040d0316030400b450002c000c0c0c2002c2c0700076140b942c20b00c01d042c00801c201d841201d000d100f00707444010810380f6254050390b05400c2001c5520a4020a0205685102c07081c06618030301403042000050f0001e00003405091780c1078680094081c00c2c40c1c848503401f0b400c80090b400042c0ea0088440a0402c03e581c287d00c1601500c8040301500401d41a05000701154001015419282d141d120881001d844800450380019148000340208005920801003400c0380b10040248503500ca83c0c0403198001d84901109403501594102e0b070f88901110768981c50380d458441c40400a05c1200030310716004564800810403000942103403c0c5030f00c00684016070034040d03030484d0740d074945403002803a641c0422841075480da0405c59 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 628744622 1250 628743372 628743391
    0x50d12112e06080c0127080304031a09070b0301141309060c030605030a05210403020d0b16170a0b2b0b010b0a050f1309020f0703120209030a02040504020d061103 71
    0xc030b01150781400031845550050060b036640a060392140149005010241010a440050b20700d012032007003c1400200003071402040e510860b65030301014420b101c800104014031030307040000148041e5842e401124112a04640d803203088015510000d009421004c1440080b50301c0e2600020801070b0a403c40404225540c50400a0a030354105154613080e400c03000130503a8120784054030400d52241c85400d25000300342c80c1e00d81029100e03404100210003d060070b5580190460811024881c604d41c07100ca441550b2034078080f58506440030180d2101c024002185e541d07118941481e903034a820f500320030041d40e00486000b042c440301c0300b00e2402c0f85005000b65141c580348400496008a01d0048552000c41c1c0c0c4c0c0c4551400000340a0041c00c1c2c0c00848003204d0100200800003007203441800070b4080c83ca440e400031941c035a02031801825844002e0800325065006202159655801103040303080590140c90104281c3d982c1d06c00108020040e0000514061900d11080e00710001000614030418005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 628745872 1250 628744622 628744631
    0x20115120b0903031519051005070b0601030204030f140a0b24090c03061516080c01050a090b010b09060408060a1e06080d0507050331050d12112e 64
    0x80e044941c80b0b00c000c41c0c01d01540031131400e07007264909003c1d80b0400100c600368071ba0880e00380c80b00002420302c21900c45d43d03030015101183c5c3c10280092400c2c00e41d00b260003400c003140752900e5603650302e0b51300020007009002507184035850022643e0500c0302280050780b0241e050450300d001c0385800702842e0200d640d0080e001c006488019141490b05286004001d042441c4e401d550300c1000b0031800c0c1c05d62054002d184e503400c0c01044000000010084003042c81440b40c240c07100c810711806030849000a10010350300382405445c501240820010a040d50503010711940c0d60706461011404900c101e80c81120a842805c08102000e52940d00c144c12040d816008603017a0708440000c5401c7d50401c1c0602d400c0c6811030307084402603d0054009120b40c2d445035040d0781c05c140d00808504c8014020134401d60400000042035620768401c60a01409424100d5202241b401c994403031802c8010308501e8007040c02030045c810030042900704950301003110700c50b00d0140c0c0e4a03042d9080c0764040b001461990f060074140b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 628747122 1250 628745872 628745881
    0x103020d020d06091b180e0c04092f090a06050d0e070801060509010b0c030f0a031806090309090c0504090216021f1407050c0f010905040e0a050706092301020115120b 73
    0x19500040c06c41c0b03001c0c3d41c01c00045081864580d502d4001420b42c03140e148040100260070110790240c140307000350b520b0300d1080300c040040c410800809201107030b400f240d03410010030b4144c7d942d001c01e00040c0e0303601d8507207d030700c4008091024005045074030b02e600031440360441c0040c407034105400046c25600241c0f0201c146076a59107682c101e80c016501e40a0081c1c0040c4000c0381c000403031030060300c849149440c1c04036203150203124070182c021052800780c40b01030b110088a000d00d60003001d503000501c401d034000c02c100c000e0260003c015000700d001e00c525603074000481038001c25144200241d41074005103c04090f100701442105414201c1e16000d022039004582c058141c1e0056040e500c0703041d0000090445a0210700070056044544210310703051110000c408586500c8038440c04d24909803e1009044800c41d904005143c42c041b944154104403a0b200284a202c601c0c1103001c5114403001010760000002c0f800507405030a050404070443c03034940c04009443c0c0da030044d2001e82c69000e4034810107140c0303c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 628748372 1250 628747122 628747127
    0xf010501150f050a080c070b010b030a06141e0a080f061006020c0f09070309060c09030201021218060d0212070507060c0f05180301090602120f07030b09060103020d020d06091b 77
    0x5041009030100f00148160344031980038803002540b181e0009240b034902a00359440c140f5012081e04107200812000c0304202e80d100b8144030b004040d1641c52500b03407150402c00c0000c0c00c200d0004221f8840401c069076120101e40324416400b024180790340c01da03503800341c044e0502d80c2c0d5000201ca900c0f02134098014002513250020074507900064000c0e00240c0044000014400200e001401603810956541aa900844c610384140104001d0f031380d650208031403460000914104402580e6205441e003040f8551440700a80012100c00345e0949007240c603845407412600003400f440041403072603010582044039495000f001040228031540c000c00c1285884201210800b0043c60484086403040111500c8100000c81c4c0d070072101002000031030a1109030380c48100b80d0304190718000c00c020242d0180500320980c82681548440d00e86000c004200300000020301e00140a40001d052640c0090542003024031501182d5600c0103c2005020341a551509913006041071603a00c44003010000c1001c035007a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 628749622 1250 628748372 628748387
    0x30c021c02010206162d03060902181c0507060f080c030906010e1003021503011d1506030c0403061a04060911030c0f070b010e0402132306120f01050115 67
    0xe40681c000c01071980c411001000c500759020042c0184050070b00b8000e442c01000b41403107084006c1c40c80844403078060000c09402d58660381c01c91041540140b06d00801441d0040620a4a10342221620888030b24080c04840c000c0320302001600c1801046000304000707800c44801c200e0840d859481000340ea445510b240324501007503c4c9080c00fa00b041d8010000d1100b80301505400c840c80d02c0114000b25901d9000882245c1482c141c40e03d40c0d6401b10040111300c1802d4101305c2c03929500462240c55140440350a42074444a0301d02c2c5200d44070100103c0c0c040d50304001520041c59000c50101301660018803071490340e800c110306981c450b80c20a0004943e2a96078004c0360900075070445e4480c00c5442e460039039029a0030141c1007401c04c0e030b02400038001140010700124000c0008914070051801c0c2401404650103030001c1c0e80020f00d0910240402424503c01150003400844107076402c140c5800c070000325050280c1c0b0400c009486207402c0801d0f02081940014100d5004100c00788450401140075190071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 628750872 1250 628749622 628749679
    0x160501050d051531050f040609030e030f070f08010c020a03140d0c0206160905100e032517012d14090c01021b092e1202010806010918020c01020412030c02 68
    0x31b614101080c001882c0740c0003050340b98843e0800314004150132002c246890140b14000340c4a9228003400c0011501224100c4041c0000d200280080002a40007954800303907281c0c01130070000305c20f84020750818200c1c152020908291014440075107100f030300968828042d02d0b00c01065148150840d921802581010212800031300715440c8520030300010303a40c0c10a101c03016609400303264a0032100740508104045461110480809010f0400622100e007040005040401b07a2600390711884284405c2104d40281d6101a001c401102d10412800e0140c5220003165951608810074000300c1080491042800c3c44280c1c21158000c03414103400c103103503030f109003c117800c4000400490300c2e000310360704d04d0794a00381d081380ba00d48825031201400044100b0382d4014078104a400312482e04560740001c03404d8000500b46001e10b0200d041c40c8000c610b580054030003940715940050403000c081000e4064030010041e070b81803844042100d080161444240305d404a00c5001c290044e11441480400601d444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 628752122 1250 628750872 628750891
    0x512121311100e06030a0e07060f05040510020f060708071814060304050f0601030302150702010c020601051c1a011401050a021002030703090206030711160501050d05153105 76
    0x340d07a4603802d114000301800100010400000c01c0106a529160001e500441c1c452000180c80c117810b240480c01d01400b0f800c05002c0107040351041c1501680030080d00c1c20394001b2200c100540690302e01c02da02d4544000f52200c10350140408000d055500070200038480c0749c0a49640850030100301c4144c99010081c00b4013011050782920420313032410424003942e80303d44a06c0032605403490310b210991402009034403c40041e4000c00c08540e882043d00c0034983c10400500090040e50344112000e5200d110500425000d0301d020144078404051340c0303a048403502e400121a40404540401280c40c1310001d02521031036a02c416840101548120110368040c9129406440100341400d80704010758000350166040507120406100542d840800030360141e2455241e2006450401d0500e904114295810100b02038846200304031340c0c2d8118048540c0d01c031488500003036070b0307035050702044120340c3c20081141c101c640000c0d0034845400c826060b03030303c8825035005c0c03448d070104640b0040b00b0740c1c4044485248 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 628753372 1250 628752122 628752143
    0x20109020d06090606050a03060b0f010503010302100804061e0207050f0a0f08090604030213020d051008070e10080f030c250306021e21060609010906120905121213 72
    0x200b000c81e803103104081c3c03051501040d12952800080c010030000d81096500c1ca81e070350040407062400741c3c1450b480c1d200030300344241190700d503400190000c40000303100b42c1888200c0c7c00260402c180d5030301a200034120071004d00f6407441c180a10600075000450221024031824104658640300002c902c10500c0d0b000e0a00e04200c0340a0f503840780ca40e0000300c07003560024000d000c0880113070b036144402800b60395a00c2c001601e0b500e013420800c041d03074000340441102e0101a10284070b511000700700032050b07510041541405403544c141c8140300380c17080d50001d0002d0181050a00050201000505100341014110341010b04c03845801c452060b655110f03112004160b040400019201c0e4024105c40d4100b000041041d41400ca45c02046034000f5803143c008003000b860202c0442046500d55800c50030548501c1e0801d031440d8006044602d8a01400b010701c031100390340c109000f0040e00560489513001d0240d44290b0041311505029030001c180c043c040c5580440010301703850080940e090300b10f400650104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 628754622 1250 628753372 628753399
    0x9090c091b0a0c0807210318020109051002030c060117071a04090b04020705060f06030f07030f1b0803130f171015051c0b1b0301060e010e03100506090702010902 71
    0x241c2110f0440d1080b150103000340200030106000c420f28105141d0200d41c0700010446018008040715004400b800440300040c600d040940da00c80c8540040d581c055a004c1004124094140e2850103048108082445882d0010450265940c88520210032510460703090903210f03d042e400542104050550814080c002080f10a2481c2c000b1b100c00e60018000501c0c10b0a261a428141001110060300c03401c81c803030a20015081c20451605905c50318800785c200241955201c1280b600c2c00f00000c1d1041409a0b10701110001c0300c3c100c140180b404030102d07640d5280c4a00c1140c1411309920a0380c94044004000154800303000d008840c070344c900361010340401c070a9945c1c494000d0008011418050600f14000b00e15078551030b50301482e03680c0c4044502081ca007989848040060700410040043c2c40c4801c003c1410f201e61070503241036034610700b020420000c3d0100101d80c403403070000381c1550502c240746c800c3d052000168003441c0551001d4407540c0ba01c2d51401000d0703099032041a0001e40085070440d510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 628755872 1250 628754622 628754627
    0x1b020d020c060d06030615030c0614090d08040e0708060f04050108190606170705130b011d0114030411030c030c0d06180501060b0309070509100504021809090c091b0a 73
    0x40016030044030f400507050791240c03500c504440d0214411301c1502000d03030b0248240104000202c00610035854407008111204c40043c1d900e00914504078001c480c20900c2404110400003518058a251035030200b440c540703101e000309100740a44a9a0082090668800e96802c003405402d0695501c0402054000382080340243c10300b014110503600c031a42d80c2d10115100800080c03000c082100304009148003400d00b410480c52500d0543c1c05541289004003c8110340d8004415102c1d42110807068020000c41100607551242030000843c04030340d0001c10001049070038007248120450503411103003424092014149d0700e0700d000403103560140c034070241c0c0303800145680c200703004064888028030700e80d0304039544c0c1609403043d0b9001030005850110404c208000208040d000800c401c43d0307007088a00340845440d9804034140112801140c001522034a5401196840041c9400240049070703e4a007642003151950501c00b000e03442000e000300030070100b0410595090400d660a006503241c580010801d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 628757122 1250 628755872 628755877
    0x940030806030109020306070905011205061c241d070819020102010902060703021f02030106050f030601210b01030c05120a0914010e01062402060c0d0209040e011b020d020c06 77
    0x22103502d592900314010042c1c9061158078003a000f10344a28800604020016103c0000c83e02080b052900d42810041c282c1d032502d1400d010050070700c00c40807485080b400d10b00f8240700c45803e4100705583c401c00714809089a940413403203c231f07602020301400003050110540c9503941c03031080c0006540003080ca80c4c00700106044d08900107105000001d03d28506501042c0a41c001c0c00301640540c01507503050a00604495480e0300400306c5a030214034540c10968050028011218440c0e91480007200290080c0d001d421400000e880d420828034070320075080d07000740180080100080c00207043c0040e0a0600f805034040d9801850844c084103401c0e0f1795036410000500402c03c1c00e80d080c91640441048040080c810020016401c20010800b913082c00c0d50b5011445860f40c0c140c61100c1b40b0708040300c106a002c2240f44d0031903c0d081e61256511071140f8a1000307805502085540680341c480c00244a038015403040c2e151440102c0250001c404001007a6111206c075204078000da082035003000400d1a2a100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 628758372 1250 628757122 628757131
    0x1d0612071205030306040b030d0212030c090d11040e0a0804140f100c0c0b03010608190e0316020a0f0e010e04052a240a03180209400308 60
    0x1221031080d600c45101560601411003035400d03400000a002203804c20b801481900c4405030000c05039102c003000c00035510704404110300c2040402202140381c4100007000c80329407003c010004000c06540742040a0f0a5091810640c03084d8500500b03081014000b10700700b0503050304480c0351418145492040212804a50030303565100d9000c0710a95980d0742d591000c00c2c48000f2a5039a04820b500d02d03d4907051502480d004890744020502c0100710241e44a5902d40c1c0c008440800905000b01d44001a005070582000040e014000440c00e04d109039801c00c183d48446000300d03524414640d0700c0d1903159080345240138083e000e660120051042c101c4503040a03404c070f807042046a00030180700014070b2980902e41d000c0c20f264984443d400d21b8502d030020416180400503004d92082c10845d00c0a90701c030b4468035600c141803645400c2c055004024030b02422040b0b903006045580d89203002e0500740a19100c88401042001c2c50702c059800766400400050600e105885081d0030240440d1016280030710004c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 628759622 1250 628758372 628758409
    0x9011d0c0114040b030c121e0a1d0f0f0c09090d0f02030d0204030c081b06031518010b0310090b0609010507140a05030a0e0102061b03060a0b040b030a061d06 69
    0xa0075003513080154800c080030060b13681c4540012401c440d001d032015110000c15210817461340300b1008582c80780c5030400181c46c000201401510710544940300145240ba04600a4008400140c500452011140010700f030036500341e00c000b01c0410081c850207030f9620b1800d43c00382d0060400203008400d030100d0242940100d03400c00100b040c00b0b00c103990040c0c204413400304c50860208010b05040103e0802038480c81000d4041c184818045903607400018805540658511225031454840005d120360f0807403000c000303210b10b40c1c650800c80d80780c1d4020b03aa0344882d440c0e00f10b40041d814015100b10084031100806003450140c0380c4004642c0ca4010708004c1d1230406400f68510340e40d81c0204800c01c8007521410180d6100e40039200090f000c00034411025065400100402c02c55510710500010030040d46103032075849440b40004130b440183d607904100f40348480028085041130079080990702c03401486400f80116a00c03140f03050202c07141b5891204807120008049501c0345045042259201c9021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 628760872 1250 628759622 628759627
    0x111070803040515070915050a270509040c030c0b04082a061201030b15030604020411070209040b010f27050402010e060a0914090903030c0304020d0209070809011d0c0114 75
    0x80f13003107031800c10040e120fa4002c01ea0020b02048043da05017000407944503281000c900b480500040907000d0004c110b2550700201021030402d81540e851940c0c24040c090242030400070340703414501107055001c180011740b01c80c042540001000746444c01114207440a101c040d00e8910082e8602c1d5110f2000320314814080100358010200c1512003901500c00070102181d01c0301b06500d1401c0c0794034540000303400880c100c00c07203e04416039500d00041050f0840c1c0c1c160f5000502044140c1e03400d00034055103070000d5005030301c0e5061009000d000d4074002d05030390103048480d645c1030b40c032840041c0ea4103052284541000101c0d100160b40c01450b44000c2d0700030f0060403ca10408220000602564414240c070000b08920080900c003c5000f200d01c4080300e20152410f01c09410440c0d00d25070f5900000f4013244100308c000001400b1503c500c00c074500045d03400303441c510341402c0090020b071101c00210307000e0a40c3d42c40c00e1207920040610000c2c4001c80c0c0c0c20315014080c000504d100444451003070011001580c42e04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 628762122 1250 628760872 628760893
    0x20109030b07053106120902060301120c05010305041a040512040f180b2407060606090306050f01140d14030a050703020d05090a050108090f01290301110708030405 72
    0x81da03200751081401e80d85a541d9040725100c0068000310050070111501d0070152a07541c0408400c11003c159901d40c1029021040441070240290815075002900500d011000140b4141d036103040320f08403881401c40f801d646848034011000c032507044070003603e40c400c00e801102c0c4c001e000e28100b1703400a000304141c4800c4210b000b4990801d034481e50007440f004021120801102010000f20101d2a203604018450130a04000241181d942e01005203203080c01c2c5d400d40c20712100358004460503260b1048090100b80e5841034090b00c41010707444140d07009410040000e4040010306a40d50682e0460705045103101e10010030b20055000c85802142e18540036001008900001c001400d0310070550755505039a030025290003420f141540e0114001c0c40070903c0000031959446000e0401c0c2c84c0c2c2840d0041080e522507042c50f24107420240c00800d01d528100c0401d040180078800c9004409140c181e98100d10f42200a1608980ca004014481d5403003d218141c006071500c0c00440d0000d000700c0450b807540c0324 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 628763372 1250 628762122 628762133
    0x24040f050d0203300a24030303060e070c051c0c0602030907030c0f06080105041109040f050f010b0a0503040803040c0e010609090f020f2d0706090501050a06031e02010903 75
    0x1e20791103180940d001190000a8a00e26010316000c86130885100801340e10340d249040c0c0000014101500c0c0d5915004000b01c80100d003140c4288421a54103800700450340ca0401400074000c074002e9004c9018600c0c001031400e401102d0310200c0ca98000c009107180f121070820072038243c0105181c401000000381c8610007289142c00614041c44884d406040151314506e0224208500c5500007100c1008101003003013901d070002c494504460050700d01064500003108905980d01c9410703001c81d80989800c00c510801589503024500c107001c004050704540c1d03240c4e8411080c80c092801d03008002a001c20000f00000c001102540d0010311900d49810150703240c201c44a1888002d8202ca400681c60140c1040310000354054510140c0d02e410b0214904040b2070a50030381441040740e026036a0920324905140c840340c61a040400c01444082c0302c4d00d400d90380c076000307000d00100c54065801e5820103000c103135020740d507110390f40490b40d000d400c14031916017114030301105d03800160041c0d040c0040c07042d00001180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 628764622 1250 628763372 628763383
    0x201020d110d0c020d0207030b070e0a0611010e0c03070b0d0e070303110c100c030509030f01020408011a0901060801060c050f010f0b011b02010f110304090603030f09060224040f05 79
    0x21420181c0a48419502c4102c208407910300e001c09046601100120a417241c0126042d0f00344e07a0841d058102d55920502d003036403c0041000d9958001079050000a004dd0b4007007031868140c14000002d001c0705500c0504244d5030710a4070320031541a0405c0034200702c0340c2a224000c0c20010002c803404103001c0349401009003001100d6200741c0205050301a011000c00d030500011907001412600c0305039000000d00000d022800503030009060100014102c40659000c10003045804a41d500070356036140c0752866540030300711016011518116003c005802480d000c2d845506950180c3c1d100d481ea40e1905100f1200302c1181d441c1580c00d070080e1412002c03080401e0042c00d44035541040003042851034000010090020740e80704d01201d01c203000c10000141c0c0d00400c1481e0307081051500c104840e032a99282400d510503030340218040c920f016800020580c2003c4a09140c0c0e0640d1034241034550399400c1a600c0d84c01e183c005482001c058000d41940810b040c00c0c168200780601c8074103160b80c4080d5100c0d407500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 628765872 1250 628764622 628764641
    0x1020f0d080907090203090a0221010903090810020f090d0312020301150806060c0d110304080601121a0c160f0222050112051005041e0c140901080309010c030201020d 73
    0x4000c1402c200c065001084164010090007208510714030f0146a01034561421070342c001c1c07095903406490b11080c1071525050000348540c0c0001c0001c0410791501600000c16445034140074040c1c461800b08c02e813101c0c800d5176a00819204c4d0940b80080710410450a200320356412001d00c02c0140c41c08140012510145000c0c0820300b1b01c0001100a400740a031060000400e06071050070300b0000341403000000306840d2140903860510101c200301c40740e112402c0d03019580129072644079a02c00080c0403810000c2c00341006006111b1f036071020007240f00c80d15a03200121248016403800308042d40e80020a0450700300f82c540201080006101c16a00180c0c241c103051010343c0140000f05841c1503424003074800c0c94014408018181a104001e035aa10307180d854403069207254664400025050124880031842d0070b04501330551580f0f400c602e0950558a15406910059642900b80c0c40441c01c080390154183c03030861006504110308000111002c6842400480840d5000d20205130300d40d50a00482214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 628767122 1250 628765872 628765877
    0x160e0912040902090901120317040809182401080117010609050114120d021203100305010e030703170c0d020d0f0515041109010e0d030504080a1203050f0610050901020f0d 75
    0x84d0f80e4804100546800103030402e2910141d41d05174800041e80114088d034a968242860b44150703030396424040b2250007194120f035009000d10307a8441c180c441940400784500c1e80260010880280c4a2010300e10003031404400c0e010485240c01400240f01c5040d5035038800c0c0c40200040b48540e110100074040e40c0c03080c1d000f54100803000b00b00502078a0a038000f9862520280d0040440048046000750b07110202103861002d4000000498031a02045903e00d024503003140081c0240c4141c1000d250307490340302403c190009145400c0911100314442840313030244101217078013130419011000c114000e6100c903d00d1003840e956100541002031050013014442e00c480c1c0369492603030302503000b0300c800d9035094458800b001501b00701045a5a80040c1c180b40865000c4e81d40111041b2580b405450620031500456190310511002608200b0340fa900c00c141c0b000c0d25a4244103c1c3c9843e1040036001405546895000c1c444070244401d4920a0000e001d650105204407000c002d2084000340c180601a11950300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 628768372 1250 628767122 628767127
    0x20a05060c040506070b1305190302150f0112030e04020c03070c08160303030203090a20040e0c060a1b080f0712030203151002120c070e07180e070507021206070809160e0912040902 79
    0x601d4bc05008151804040341030903d281e150602d00302007469014000c070f2450f05064012803003810311414082a04403c081c10456860081d0312007940d40e600500006c0317408502004000c149401c000c160001c07000003040020109a04542c0c054010350001841c49050f4441c042195001c0342c60021000800384401d9811000409204240803d4500004140c10329902101d03844509032500c1e401c41d0b09074401403402c00745141c04401c00c03000d806140003010305030a20101c0c030315020031003000c0204100762060015002c1c841c0489801d905074001165005000c142542c101a03982c1040d894440b00503800d441070301c10110364031151841eaa0480800780b90180d00c60b0405100c0414880341c01e9400120505119042c00194141c0b805100c1c4e0034000c81c1c82c50b041420100710154000c005950106500814450130000f2142c0040c0d0368180032910180020200000725490703040c01f003a0f80d8921070400320355207071307a0381840c030701d01c0d42244043c040708810b110f0710b0808030084c20084040c6c0083c0ca1402c01c0581d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 628769622 1250 628768372 628768423
    0xd080c090916021b010c15140106051c0903120906020910020c0a050922170c0a11011b0204020705070b03090601090501060f09030318090c020a05060c040506070b1305 73
    0x900d000520307056810b0f04c0b80c800b11011001c1ea0403d0410b003203168801000d5920408492010b00503040640c168078140c0000030020503111b4000c1c0c00350141155030700d0010009210041040151910b80d04041c004c550340c5808080301103034a4106a151038003410000d441e2150707800100d44215034a94a54006800c10b0a1680071443c01c1542400108000c488155003030801e00303041c010a014401c1440e00215031541c000d0100300c8c404040c080c20900d0015025202d071001c01960b46c8405104004580d4440c042000d9882d40d07004143c0c0041314100b64825000440c4e42d6401d01000394080303102a610f40c850880d00191007422400118810291100501b13080d51500314004140d5038103030000010b102032010140510742d42300504d401140d0301490151042d141e83d040c0e440499189801c05455507003411000c580c11900003401002c0288207500700d41155565207080c2d0b000740a50b00841e548034104001d0170010901c40306202c1c1d0441401c0d04080100032aa56640e440c280803015105035051403400e03100e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 628770872 1250 628769622 628769627
    0x304080309132705010f060b040815070806100905090403030603050f0601142b0506151e01050c100509010b010e10090623030406060e1006020d080c090916 68
    0x7402415001c01080c84952100014a50107031070003c896400001803129040600500350080c3e00b980c007101d00100726560700c0707a1403035042d0341c804d014800d07091040866100c121440c202c200c3d4424002036891442c252140b900f007001041101141e54100a5404800f040907074560803058012842078500144840c551f00e485400c00380c680c4d42c101d8668201a004000030400000c45005202084910000c100c000c04507841c030613501401030712034080c50000d6403010800001003480c019520340c3e040600d0603c1441c01c204080181088103800260380e090020103a50050000c4c20071500c000f400d50b0740701002c8072050300440340101c40703140d860389d1250390b28989940c0000005100701029540202070603140f00c000b8003840214131814042003030301d03501a0a041e40201840ca00400150a110380d20b0070075003004000f42409000d038a07040c0084601180c46045000e03240011140c85801804c0f008002c01c50683c0c070200c00a06180c800300d010000c400c000d64410b0a03075032041e0860044400c8004802100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 628772122 1250 628770872 628770889
    0x6020705060c1005060a080a06050405100e121b1c080105090c120901020412030c051504050703140109061b08060402041208070203010e01020301030b370b01110304080309 75
    0x40d004610070001c0d228600008034124880d02e0103c10041038585a003000b2880b540002e43c0205400d029518001c07040180c41e030045070186000700c00700c4410400318141102102d01006166016907c90685070003012408409042022100380b00303115080c0070034111703505098030100c04203a0f0b003a0719000c481d26242c001c040d142c09401d064400407041e240001480010388203020602e04c01c420035000081800c07109404540180040d452001e00381c0c00140340c040e2040020900c1218180114845200380c0d42401041a1155400c03074001c1c0162481c507105c905408038001000d510395500d6032280c00c04240140110420102d0150035a1541032031440c0041000c0400342085105030300420040060686141080b1480d0b50040781d034650f03d000c07070300c002070061110021b40141940040000402c1c09082013042d84214662809a680703502180020142d5400525041c00000ca00b8511002038001c0b41e403204000000604040e004004000300342442c541040c1e000e9143c0c8d80c4000351102c0b0700c1c1024202c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 628773372 1250 628772122 628772129
    0x13170a061a090c071a07090b070501090804090e070905061c030903020a12110301050705091e0d08090a06080c191106090624031209210607140903071403071d01060207 73
    0x40c0301c0392402c02c0a001048124944115423982e00003191b03823000d100703082d40003040345640f0415050340c440e40ca41160003e40306864540343d0301c0c05022400180790f032860041c244100c600904180394010107000c0e51100080585043e004c00c04035410100c0142c1300c40302100054000d480b4066050307174540c41d090350b4a15800d280c06029034104001d000c1f4450b0000f058030a080c0c0c00321030284000c2e59140d8401000c24a1014141c0d0105622503844180714005004049120040d505508a00c0d260b102c291020351003951906244078080090f1004140145520204941c00b45040e211210390b1420300303880d00f81e080c0c0715030195030090f07400d102da6080001181060780b910415800c518445400c0029100d440f9043c02e0f003c2c2880026940d401940c0701c031109023585441900c1e2003050038109007200e541e0744048070040049115000140c03c5e83d540030041c1c1e094410003c1c01402200c2c18040ca40e0981c648440e0b803290507125603000400c1c110303ca40a0f0f1054628400e152000d10f40c540500249083c4c020360 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 628774622 1250 628773372 628773413
    0x1030602070c05010c02030c010302030a0f05150301050121020f0d0204090b0601230315030c031218010306030f0228060c0506010911030a020903070f030813170a061a090c07 76
    0x212040187c41c0405c841964070001d09005849961340b04185011740fa002c25170384039443c5414104604c0d098055100d000d80503094001700041d0380c8030420242c5940e16052120f0800f2919408040140340c2100d40c40302d042d1340901512000c0b20a580444c003030b251018401c41c0c15580c080304011907540c0c0901480114103000e111440c40070030301e4814516610000c0e00d01007400003003a0115415490401480c1c0d0303800d0300941160b01e0001c0189000c2c2258000c0842041c0a410604c0c090b00c403580300f409100300b56500880f88002000240e401c02ca09103241041030403484a0341404440c0170030708101c80ba001080070740c03100800102c040c0361190402005805c250300781440c0440c896030161840703080d00d1744200c82c4140183d071054100000307440d20946620081c00f0041072000030080000c41006400342c01c04000000f6005a194040440c1c001807250361000a0b0b80806000004101950030040d01503603019800010403042c0b5011801d003480c2120030b1525540000b0320141000103c01030325180e9a0301a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 628775872 1250 628774622 628774637
    0xa0c230306060f01030b0409120f08060402030705040920180906030604051504050309040204030c060201050a0c02190201030204030206071101120203040308010608040515151203030903220e01030602070c0501 91
    0x11000a082100340e80c54141099030354942c1411b191551b502240c20103030400c90440021031004002410001484a40e2000503800c0e004605142000e0003900e000f2560794480d01c0c18507090144403c01002c00381f00404840154050031032407619500020b00c0411903004140300c0c190401d01c10300c003210b540940a0340c0079611010401021031000b14013600c540121481c0050280c0341c604029246000c0d000e892a0f0261002030004100250108120121181500207001035039440500004841c0c0c010000405604840c0c0020401c0c23251141d05101c0c00d1050500500f850381f2034001c50440d40101760100c40349000a5121445903812000c00016400810b00940c41d6113055a00140802410300c901818081c451010608004e02440000c8078446202c00b00c1e411490b00490b8900f0b100b4076600c17402c0c01103140b8011000004004022640b258a010004601e04100340b100e240c100e03101c0781004005885406008503072900500c11040c02940100d00c0982c0b212218140072200d0b904603171099040c409034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 628776978 1106 628775872 628775881
    0x11040803031e070806030a03030b04020f071203110403120e041b02060f0601050c0c131805071404060e0a0504061b02070f08120313050a0c230306 64
    0x14200030141602e420b82c3c240e0321804183c07141601500b000c40100007190080c1c01c1051242c0e006840141b600c0301e1106040388035048010203da400010030144c40e038559250049580541c20080120f18240c91661025032040c0180290018000341c010080700719030303a513030250200703401c194200b1812500c2800020745500c400c81e1500081c0340c0c40b2012034245d52203081a2078004004e68010811000350004000081c5131504c107240342d0b540c83d4445103594074034820030810f10511450003486001d0130580352000d66051179036424090352415004001c8261892103080d08030101440000b401d8a4a042c88000780002c403508100600403002807821765940000e1280460305074030803001d4200d4640712110f8441203201000305c8004018070204140411099803200c6c814072440031294442000d0b5100803c0b0703101ca9202018103000c029500070030020300054480000c10840150a4a00e803 = true := by decide +kernel

theorem cover : BRFrame.Cov 628597122 628776978 := by
  have h0 := BRFrame.cov_init 628597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 628597122 ≤ n) (h2 : n < 628776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
