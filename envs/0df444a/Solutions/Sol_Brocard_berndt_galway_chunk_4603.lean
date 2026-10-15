-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4603
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:08:55.800411+00:00
-- url     : https://prove2.me/submissions/c7f284ef-86cc-46ec-86dd-c9f401b00c16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 827697841 ≤ n < 827877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 827699091 1250 827697841 827697859
    0x50f030a09150f050301050103090f05060a020a1704080a0f0e0603010f170601030215090f060c010501050a0f1d2a0d0f233c0a0e0c0915 60
    0x96198089040c400b03840b918840d840035140402800c46541055002c0078000902c10720062016622982001c10014016061204c2c0d0898503103400e42001015941405044d500182c1c07030103125080081103d012201d40300d0902c6603e015203c2d45414498888054108800c204019503034500502c800302c008100902081c0c0c4075a110b101084d0840054002c481c2c02003d83e0034041e0380008000b544a040e60b0380a465807480301407498a504003900401e500c564800300c02c8000c8400da407100d00241c10042c00881c0082a51f501d41000d1049040ba26003091803036011582d01030049040071050300c0906001134000440560f44d0810b894014210140103500e4034030401483c0308074100a00143c0000c81c822901003101e400b00308194001c94240c83e800c01d120158204510408244210301c0e50f41c131040a0900908a100640d40c10f0b107a46070641c80b102034004004441c8203c141c85010065005c1558041001254a43c21910f40e580e0800c203241480303170004d1400602d04e00c10850400b2030620016142c048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 827700341 1250 827699091 827699107
    0x1201030f14010e0303070908061611011121060607050a0b15090a090b0c18060901020c0a0b0705060a1a0915030d03050a0b0a050a031106040302120a0510020a09060804050f03 76
    0xe102d82c4241c48003800500046e0010850070347c0400c849000300001010250030715070b4a0000c0e1204bc1e59003205032403656840944030392040c5228028546940300e684c2209508a4101e25103400e07030405840d06002c0c010911103000010000658101003940058048040e0ba0f110140a00e003d001d240d4415007008030764043c4402e42c0c00ca90402c5051030300c0350022410554a00401e200381d8068200202d045100e11400a4501d08003c4014288002c040c41034a292602100100c1c121000d0f513403165400740720004540d810300406000d403036040001c150040c001c4172602c00c03203404103580844542b0311681d4450041009801c880c656011550809020340d00c00c080402ca0107002070100319102081c00f030802031507100038580141054150748000308296411411901c0e0100c4039504000b015410450810000c000760b610b040c150750701880e601005088941e00e41c50328034249000724200700340585c0103000444e10a9005001030003035405a243c0007219039107070b04005190450080b030b030038070501000480207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 827701591 1250 827700341 827700343
    0x3070518090105250c0804050a0303021c18030b2a04032901030b090f0111210f0c09040b06040e060a291b2508031201030f14010e 57
    0x2a01c2811507070000c00c240d54844807080120072502080510329202c202401c458180a0b090000455010f5001c039820309454401064008820342c20903405030344045103003c0790781702000c007105040ea02841d0580709039000c2400e10660807846d0000401c0e0b00f5001000403041c8030500031600000b000044103000078100450040006d9015010030b690040081481d0701801c00540498410400e0510360041c0c560701c0d64846480c42caa0250018035503015134141109800d009000360755003840035150b8250741d0402001620b8810403041c4101d083c8407100c5c0e007081540c0484400c1907a000c0f480b10f034141e0307640c10414009401410a40748281e0b0002021601107107181201c102148103140c162610119207841e81180742e00d401c8170000c2020701c00c0c00c44070281800c1c0b440e03c01401811040300f0501c00714540700034010b8140500503281130408d0003108031044001d075102411600034607640003d54500809011525409130701400041c0c12106c207050904200a150a00c004074905000001c11002138442c441c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 827702841 1250 827701591 827701639
    0x60405040b03150c040f08030903031b0a0f0507060f0e0a090c0201020904021b060f04050316020109120b0f011220010e09040809040f02040501300f0504060c0c0c14030705 75
    0x22046e40c011140000c80c03840400011211800302c01001103080851503001e40d401c61000c0c9401101034041c01d144400014194440c60b808130348030700050700009041a9004081040e041c00d90310400c031400300f1140c1107840c0d28080c0c8090310350700000840c0c18041e540781070340a031045000c895002840007900d105804400041d41c6004410744065494903216142c802030202002d541c007510503002003044000000c8510f0b140450548103040c03080d1042d9586044c0d40901d20744074070940304401e00b1001c1080040803030707403c51b02501e20310220a9110410751524000724800c0164408060000a00410a68043c203460610428010315200603417515242100c02900040c0069000d070707050460307424442e1114000d650650b08103035074404013184450106462200e10007010000c00100c0c0614803440c00e400e0082e000d25503601200400e050800f80b034030408440b4a04813310400611541c64400107419003242001c5408050b802e007148940040081d040c00a1540143d0740030520f41074a042e049645019 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 827704091 1250 827702841 827702849
    0x2090405011208040905130b0a0203090115082104120f0b010b0403080306040b04320903030f070c08131203080901050601050405120a0210170702010b060405040b03150c04 75
    0x6204690342e500594140616500c001440070b0720600050140001c1c0d6440541d102c2548000d40c890030071151107442c0810829a0890007003034001003042400e03482400b44241c2e91050304181e944091a10300c3d203036203800c01c28018034000b0006502030340c884148079061f40c02030b10ba0b00c410b0490081d030301e10300012200502c1404403046024900002500e42002c000ea804407a00003000e20b103190343e904200002480081c051561007643c480a803c07090106418403880c28040012031410148920428800e01c14018101c11895108008018800300d403015080c0e04000d0504041000d8001d41c9802880f0703002d12824040052058100001c40001c0070040d80b6945010303898103201d0b034580c0100d1500f1389200300d4010340407440821041000d424800d04241900c1c2d0740c40250f80c001e0f8400c0e4009507104aa01ca203081c001004040300418445c42e4102c6103410a40600080204800c008082503003030060380f00787e500c1995261400720340d5441c18406400200c400020100c1b2510745840340e0141504a401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 827705341 1250 827704091 827704099
    0x60a0809150c0a0507050a0b09030c19080703030905030708070510060504020a0c150f0e0601060f020f060f040f06180507050f03190c0312033206010c14030403060209 73
    0x8000000700c8aa80c010500a0394090021850104400d005454035030000404407100d1143c00c084101117002d0024490082c980940656601d240440402d45860545016500040c0d4021b40320400903001108844d500e40d81400c010401d404541401400c40c01051405404148009112402c200000c03400d800001400c4c0c0e400c0088644502c1484128001c440c0a0408513084c0c000c40c00100f010010500c00c64420322001190106103c5810b900ba501c2d011681003007640003000501031b041d049408401c01c2c0c0b400d403008080710071509002940c0d540f80548120101c0b0440d002080170300440c2d1305074609141c0c00c1a0309110300c80f000b10344c0750101d400c04041940e044c0a01400898030380f6203510300c40100c8000074010071001010002143c5d40762072021007101d046000b0040040051381c80154001078101c60f490010700c201541d41d0b0031601c0c4182002d01d4220500c3e004d00c51010b107513a00780e2a5001070082c81c1200c0e083c08203103000481c3c01100380c60199030f0b00c00820000100302d16034004100c0000152 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 827706591 1250 827705341 827705353
    0x30307060b100806030a0605250306261209031c0216080607090e0c22090b0411121806011517010509061203070f030c1a07050f0d0b060a0809 62
    0x250b011100303400103032862645a0081503040d0085002908000d0300002c80c004041c1d0b40000b03502e050299038900d100c54034003007511740c1010007a0941003240c11002c104140100502010310076000e5842c1c1c0c0c4072800c0c2a110407170101d0301c910251000c100710a081091403500a40203481c490003e0b55a040a02940b501407460100201c0d40500c04103c05004400341e441e0110880c0c1030400c141015040200140d0724050248030044102d0118254002d4884842040000300f500702002c80080d01e120100140c0514107024221b01455010004c5a01c0e81e40d0311040886261120840d039117002c0740c002d840c034543e80b10ba2030020481c1309610311414014030203a201c440c046204032004242680091040f158030415020003d043c0d41010814462680d242038140da1500040f50341e40050320044d40d46c2900054041d0342d0010030030001e1650b45800c09448100c2044601d803a1030000c04502ca041034440d000c0c40c006ca484401d11030705130001c0c0341c2c82e040140010340701d030503110303000307204a000300c0302080288954 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 827707841 1250 827706591 827706619
    0x5030408040b0706141305031801020c150a020609030414060a110a0302280c05100917061005010c0b0a023610140901211803031b05030f0901060302030307060b 70
    0x104161b9411594400083d501f17240f040045007a2480c803a40029042d03014140c0b00f6107044d03030b440344d40d59003103001105995202c1070440ca00910f003043c001d0803001941e00401092102045100204d0302801044807507954912031880103c1d0007441850b01c4080a2048a040300105a004519070b1081c4451401c9524128401c0386141400403800901410b1100d03480400d0107d070070300880c08000315150b07003080f8020f0380e6980e003400c0d21000c0b01e040f585450f8000c036045c0500050b0224100005103424030300300c00a40800d03206da28000340d0143c400c284913680001d241d04030169544c20302c0268059000340c20810f101900c032584c083c0d10030070f510a01c84c010990b403c0c140f03540900c00103815681d00551023400c1060620040d551b5810b035001c0201800340c000041c00e038501050007101d10352018040345081004c2103280140c2a00c2c14201751105885480c5c8201d914190301006407503000000700d020a0302c503150490190b00508154101070f405000c0050044140078603a040307440702d00000c0c1c690902c80350314 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 827709091 1250 827707841 827707861
    0x7061e0b0a0b0702010201090804080a020a09050f13020a090c170906010e181005150907030b010f051b0d0507110901030f1104062c0a02070309050105030408040b070614 74
    0x29802850368449072004090140042d0b180151078107a2041c0000201c443d0311b034031800d403070741c00541c0504802d92043c064441142801d00c000001082c0004082c006410440400c101001009042d00014901c0300d11000941d5039040b00d440080aa4481c00c20842440b16001031401c1481c444004010441c0b1020134900140020340c641280c0e2070100c14181da45a50b2031040e81c285940d00100074a20070600c080d03143c5034042c0702d070a00609100b8228501514400c00740000305a0003004181490316014840340035903000f00302d00b402d85203140307021a1759000c1200c00c00c00000302c80300703114014030940508024071034203d402071195070700038458480d468031500d00300002c541c0b090100400490440403094009014200606200b400042001c61182d480b8045140c0c0b0404031215001440d1821080c8501d002c0009030264101c4168542503242c4a8a918040e2074841c2030701c5030038100b00e4000005020700800744156005480e007403a2a60303a800d41030500d4400b81502412288040010078003064400e40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 827710341 1250 827709091 827709101
    0xc0b130f0e060108070e04020d020903060928031206091e060b0a08090c102001090f0215040803030709030b0f1302041e0e03031e0112121407061e 64
    0x4500c21581c4400e41d50b100044a0002c405050384051007544505150545e5450010b840c4010300c0d00b00042c0c0341d03150282010301d0700c40050306003500c5070400500c040464903142c101d00c03d040c0c4000a00d628076812440c00302c611303240a00700d400d4140c2c40c1903004940070840b50000c2d0404d1080c0041b162949140341c814504462280c4070381e00301841c0030400307544464000c0289070743c0507003c5000e49001c0d507400c401168030902d1524000d800200203c0c0d00c01c603c003240c101d202e03580103400741c000c0003186140d83e61a102c00507081c034064852142198484070300e00c00d01c42220060a00d01d000c1d40c1d100e00f061103001e07060b240c29002c1203e4030296500061041294242800c2c441d40076045030340c843e40010303001e0000500c0c2c1480307d9603c10304450711200310115507001d08058032508000851b6680752800c8188000d4001e1000c40040c42d1100e070041107641301c4516103000313098124141d8109410b24000030313114a6034841d011056444082010014482a0b620103a1f449454901940058510b03e40480c2221 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 827711591 1250 827710341 827710349
    0x10806010f0b0c031207050c0609150a15030803040c0f030b07081803030402041d01020a0e041802061903092109171203040c030b10091107020a031e0c0b130f 69
    0xc0d1061244812200e940845e103900a1160304120f071402104440407820078108030b03007901c4c0542c02010f021495400130605030b984420000d01c100494139041044036a00c012500c809809400b01002040520004110440091810050f9580d0380780e9645040c01d0180011503215000c560100005101d294846006181149079440a50318550b580da081100620007110f180082244010122241d40c0c8244000c02c1c1a1030180c0781d200702410400100000d68941c951542020180c1c03003101030041e290030f000c0d510780781c10042d8001c0c01000c1002c0220001c10041d0740203860b03520114032004605c1015081112038400301d5840d40942a2108803000800300301c0c095410301540301400001c1c00d1040b46001d15049485840c034050203650f2603c60307800c401420344005851180f0584100715814040c81683c01c911258110796051140035000075412103c6848050048074141e403102d041110f0703100b4100c10041e802420704100b561109070070851074120302800d44403001148004100c1d4900c0070744284c01c031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 827712841 1250 827711591 827711593
    0x72a0e0f01062a2004060801060509060915030d0f1106010b041214010603050f100c0806040209040b1809011802030607030c050c0102042705091c02030c06010806010f0b0c 75
    0xa40c09116040791a01d180091907190344603c426204000b4102e0101009038454810a007845400c19804000441d15640d002c1d00130b5a1426004001613202c8600c00c3c2d078440c02c11921440c2e296034040c2e80f005890414003506501d401842030720301c1c54a03001011000c114010380e4900414002c43c4030f00c030340e0340c40c0c1c2030040c81e1002c40c0c180000c018014014820b02c22061180303490864112030032245030309550440c0c200301e440d0b800803a100b82090604000d042c021080301c0f00188007290101c00041c10082001d002e186c016a00000c0c4100c10f601c0716040181d0440014000020300c50198180110b80101034030504110350a01a5000e500012251a040704540090140003d030b12244000e81c000c01d44480d049051250602c40c01c20301140030b2001d0401401c2010f140d041c02e80410003041004500003106120aa16000600005c0040040c14101144481d9141407184101201c241d14600400f509241548259000840c607840045800c034102c079046031044a040d80c4031400b0703200364050300311a491030f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 827714091 1250 827712841 827712857
    0x60b040509060115030b030609100e19111c0309030203061308030a0203090a0b0a02070b070504060f0e060f16021002030306010f030504030e18091b01050f072a0e0f0106 74
    0x4c1003000c031020302060788190600141301c80c140c2002c203091004c100e50004903508541150a5000c41600500c0103041605025101c1d8500001440550420054001e8824000080d61070450b03211204410913104c2c00001c1c1000c02c644901c0c0003001c80e40b15000c228024012200480c40c201103014400544135400760456040d590f070003020740000d41000741465500c0c46000e0008e804684c802c820580206c2d90408096a61081800d0007150418043c02801c1040000c00041000c280c1c048151100d14805144c03608480c4140b0340029604e009500154800120015003044129141254091950302c00d9440f200c04a0a80e0f805a849010827240780340032648100c1b034290a04d21903440303158468420305140c080030405001145800201452405000300c107074060244060041195000d01a005c1131501d46080f05000020007500401400d00103010021071206e0402c414400c194840c0912400b14800c480b00c6445d02700010702d45441030f0507010040c0000f00f40c078102d05141c0d40d8103071144d81d195120b03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 827715341 1250 827714091 827714099
    0x41d2d042a0603020711060729010308040302010309051501080312010801050126010906020d052e0902130503030705031c0e120c0321150409050c0f06040306090c03060b0405090601 79
    0x1020790305c0114100d0b4103403410b14040c0c551340d0350072000d021080d00500c150300401c9016010781d01c002000b5800d6800e00c0c80848010000260040b04032000d41c1c0e4286004103c0d590280b4050f03240020a0012414018050b400859460000005002e120140c801c14810750f07640c40d072102d801c80c1c00c00c3c042c12605013600da06040031003120003d030003401e00c416000001c000416840c0e1100b240c00c000442d0f600ca645500500c45031400c0560035040da401042a4100c8041c14650140c1c900c5183c5d200e2040e5554000c20441e00940419440400800c8041e003074aa8a041d6032620a480344e0059541c03281101140c65171035500c00c450b204e1524001c0c0f036038004000c84020491f0400c0c01b900980b0842c01d4034441002000e45560659000400240b50340050035154142854030061071410030f01498012841c00c0925004030320001003a0b04803220948100c201a0307189801700d9114442c58001600e100d060101d42c0302084024407862040302e01840c020044d44d4094000c10040c0e50040c1d480200541c41540140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 827716591 1250 827715341 827715347
    0xd05090307170f010c0e09010602060610031d0a060509011b05040306090c1706061f02060610090f14011206030f1b0f0f0e0606041d2d042a06 62
    0x803030810500803c551149000a90050070746141c140c13064001043d0b00e110440da41065001c040c003600513030000c1c0582d450404081003c01c2d60141c100702c00c058660041b55500e0340b0700029140d200380c09900b540c94400c038604009015080907901032105600c3d14912500c01420450f00714000756059454620742440d580701c5c038001d046100002c0c0c60100c0c001c0030002e20b1808072a80c00012035200030140c4514980042000b0709a0f0310100608040d4101120f80b407251070b80424410750100b401c80c1d0a000180d542e000449540285030030403404810301c01c40100c1e1020421088401e000710998403c00340340d020329a0708050b61000d200040403d04101240d0002841440380305141c90408120310070302c540e03503424011f000202c5610416a81c03012a5090102585c074180e034070742c032500544409203414074005c1030441d10818064030700c2c0c1c000828008110581c07c10b8007003480d601c10040c18060303244800084011209030a03a0b0803658041d00074110901116507070036003903100c801b010038148031515001080e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 827717841 1250 827716591 827716619
    0xc06090105061503150d05100b0a060504091d0f1605060a0906030f0e011b020c190302011d03062d07021011190c031d03071406070c0e07020d05090307 66
    0xf0105030304a050920046445078842041001c7c016401407103c0d0040400000881c0d10241210b402040d0340c140c00e002042c1c225046804542c244a0000740c00444071036141c0307039038004620038204c41c09507510b040e03147d041c0025100c0201d0b10345c00c4080c043c0d81d5203100300003062191100d0a404203444070410031425000c0e501411202800150226036030303400c80205802c44040709100c00301000071590b10701015074108005803010400761003042400c00c03184400f07107940111b8403009041124820544200808002080c0d40308100074044680d07030708014080090700215003011076120f24541040e050030886d5100e4003401800d054002d80074000d045948a00078000080c80e072010010104000e094600d15151604900b25a940d600301280701c003490000e0a094080310290080041a070510b0f03403541e400300e071302c0d070440d02070b40c074a801076410440109001e401040c10142101c5101c100000c0c048004081e05d0307225180e15401d4075071a102c50641500c440c00b030a003007550154403a00702401540e07510b4081c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 827719091 1250 827717841 827717851
    0x60e071413022b02180901050a140607061404171602010f110307050d02010509030c061317280306030f02090a0603140106090f05040803070804170c030c06090105061503 74
    0xd07080542040c1440f8507651690070792a1070350741c0c0002d010307000880440c0118203640080310907841c294541000584017208501414500b000007901646044c2c2d2020101c403a82c1e40c0c80b260510207129a1101c0e018082004c8405032000c420b481488214804204201d88940c12000200c0300106080e40045aa402e1090104028004203540140003820104098405030340706400800c919508407000038203681c000350a03031040b5402400b04502452003c10030a0340020469403000d4001c1d100d00b00204c901d04050116511210b00040b0360f0031030383c04103c1d9440e900200c60a116840c01000704202c6c21180d56120140c8901c1111503400018030309411020707040110340da000704070b598480c0c40303600703038100742e02601c4505030f540c0d032401c209410f9140294801e0f2101c1d01c03010001443d15480f541e9580c48001d00d031710100280800010f082004902d04d4045170384c04072064949500c203046040f030b6a58010713004809540308440c00612000c405008032403084a000e030030242000e018006021198001401c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 827720341 1250 827719091 827719117
    0x150f170910150302150403030c1212061712030603070308030c1201061110060b180102120f1201050d0c0e1e07080f0f07140f07020d060e07141302 64
    0x4140058400035014059905400c8641071580302d10f10710401c20f00c540d42c40d00100f5003090500041012130742103010b03410115008283c000c4045035114044812040c1c95108080c50382c5050404900c5851414400549800c150101c800110410540e148240012200c665051380a080203000040c4107c000d180c120a419615a0400c0d892903600040084260402c0e00007a41050140103902410080710311404503605080002c0d41c2030003586900341c8101069044001520900013035164400c01c9850400104000c0709a10fa51160b40c1c1001940d11400282e0300e2014a0800030445241c5203102c00d1145600ca020f007080c7c246051140201604020401c80031030341810741c400c44c00d03024010054400c280c10380e1028401c0c500b6080750203510300e001d0901c0f0032002040c000c005609800c4180210152819540141c82d81c08092004410344200c240080d0040b208020716000c20100350007650021a802003a80c0285468401600c89010480b980c540d10020004000728a840700364002c110014200b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 827721591 1250 827720341 827720353
    0x90304060309050a410d1d0d0b0114040b060313020a1703040e0c0a0c021507140304050a05010804110609040204080a11120c0a15020106050910150f1709 67
    0xd01d400c4805417002c903460140d07000640381c031400034610710650101c5068091881841c65000301c8082d80d9042d1900001007401a088400341c960907640600004031103006200f444810400c1c9410f000e030500070b11603541b40c20201e00c0580c8540c640f50080c0b0301c002202034000b504540e00c0e101d00f9000e0300c0d46180d041e600400514408500044c40035030060118607003030006d503680c80c03900c040c584d0a90001042040315100a0018a0302203030320180d032660094048a03104190440085942d4840c451400300030100409810175034201c01c4048040c000310b0b00202d0b0304201c0942d43d00d0045d16583c004070380c01003012020203002c510030302c2d010b00540220800031300300500f481c2d1182d84480c601407420034266420941b2074006500c41c43c24500c10070400c000710000d404600c0d0143e000c00c58000300c600586891564503486510030070300c01d40c09030000305001000030050b41820404030314201810302403403103080311000380443d465025070071141000042c1c0e601e8480500105042c0b01d040c40000c1d141100c14002da07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 827722841 1250 827721591 827721593
    0x7050307151803030204030b0a1a1002160303090f050306010b030c030c0909012d08030706051e01150f031406010c020a03061e0e0604050a02060a03060e04030c030f0206090304060309050a 82
    0xa641c80b815002d1113914016521400c600f000085540010010542d403410a502035503151050219990112020b40d0000585400031100b82e0400c3c00d2290b00b0300d607801a004000040c9030340170f03204c10221091006155a516121410706880b0781e401d02600400c0b01d41040440d880c021003400560f03003e41004e009138241600a00010282d03170f0b003a805049031500050b1640d00c1808075100001001a21030749511019241c24826a107034020000050051540c410004420300070409a00e100702840b451404250768440b04e0440302041100030344000141c0100441030118024030070415002c40709041c0404e242d43d044c0044610011074a8101d030841420000040004c01c82d010b00404910b80b8203d04c14000c203000b03510411201e0300e030449042d03a440002440b010800110f036601440e07406650f600e0b0b40710078411068000d090154080c849031f02c0c43d041000185548803a821038140c1c481d0340c4592a85012001c01c82c2e4600c000d495510450700200000c10440303000360300542c401840355041d01c24a14503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 827724091 1250 827722841 827722871
    0x105031303052206020c0316121a0f010e07050304020d12210218030a02090114060705060703140f04030806240d0b1516020f06091002070504110705030715 68
    0x1181032060143c20291014408250180034245020780190001c011040483e003150015480b0303486258501c0011400300028089000d15844074901c42c403190301c040d414480c0103c28049070901c00c01c00c4000d811008a00800d128008980c02150020301c404d0404100e91101900003080d000f05009201040e500301e1182d41c050640001c86031042c0f10300603286c0c03c85415500c18003d510a025109400903504170006075100400070b4152550702c00300c103440702c411310f01103007451058034800b51061113004100214941c0c99000b0005200215140310300d02c2d16070f1003a8a008045c1640c0003000b003a030081c0010700d50308100340c5020003018030b600f100640000a0030101829408400b42c1254a034903110440d1442c284803106190942042040c04c1c5040e0191800149148000320000e02c2918141c80c0c9500302da442209880301c10310020b05000b004010040065034036045403052a02440c104010050710211a400303440c1c2941e0014040e40c13910480b42e030760711110244000003a603c0c0e540c03501d5031180103c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 827725341 1250 827724091 827724127
    0xa030209030f060709080102040f0b0c0c150414091905090120042d170c04020d0f0b01080601120e07030f260301180b1503090c090a0209010503130305 66
    0x440103041c881c20f018200410122003500802c065a004100400014441074036203c0bc941014440a0700ca140d044007544c280034005030f14030340c460004000399201c8900c1d1300007401121004820403c0c00c0c0030384814001d2000d401c48445c01c1c4038503d104000c5003a480c941100c0d0344410340360700001e00e01c55440c0d002e018854540c0d004031602500800d05210031940d4009035030200c1e5094120708580e6a07140c071420176421442c0220810701030503400640140b032040190302c013060001002551141c0018000d07038000d0492840c0322081d2420000c03001c4055000d85d203030a0180c141a5903105840300e80d80e0903080030f40312410040605105a44002002c503440d149100091071080d0013800b55488442c1c0700c6201402551807405904004000411096100110036504100e00e0240482c070181c5020000d200c0c2030000340d183c0141c1d4000401c0041c0380b4800306509506800494034a0260b4480c0b59805080740640e000301400300d401000460041980141c103205903070f00c81c0c03600038a0500c0384203114070010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 827726591 1250 827725341 827725363
    0xf0204090c23030f010203090a081e0f0d0b0f0f0103110d020c01050702060702010501080a02010f030e0d091503110919080321070203030709140f0a0b0a080705031b0a03020903 77
    0x100c0302242d055140c1405890000c0d1003c50095045042c0080380c4d40d250240d603040208003607000030702ea6620081001e50f40b12481c00c0201407907110100c9504010003680f0200400039540d240000040d511310f4042c0882d11710200103840500c50908010055000305104944c99400c1ca038140624039a007003284c0003c0000481c11000840c980c10001c001a03d4060003803c03d806590500005100340c40000501c00d11183d02440c000100c010b00c100150001d010302ca140b01da43e40034940c18081015007000486040718901050310003410410b61044044843d0b1b141401207503d0100300d42c3d030035407a00240004140289194100401c2d1382d4038030702c0b4919800b5190382044031400454040f0085008038400d64808840e001551540c500071400804442490080030340415030400201921b403039000c8040101100982501c0704140c589098101d550024215075002660401c00102c2c15480742007034034012140c1866259441409011095035a044040b11108040d400e220703d10207a03400b00040c07807080b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 827727841 1250 827726591 827726639
    0x20c0307050c01081006080406090c26060702030f0d0b04020c070603090605010504062706120303060e06120a080c2b0305010b09011d0607050111120106020a0f0204090c 74
    0x2c6000d001420140c0010a042c0300501011000c1080641060100354810743c04100040c4a00c0c43d440d00c4e44001000760000b040301042c1c40410b162618042190380d1103910500101c558a03504c01c80203d075a4802d104041143d5181840b80e003064080c550024401100001d00c003504100c03a10001619062460313010b500001c0d16844410103100952048030301502c01550140650350500c0d80280111407007400100c0c40c024191039503544011144c3c0003002801420a441c2045100c505008000c0c000300c2c00741d007924420020110786186482c20603041444030b060b0180415403030588890382c1c01d41181164210750f0103045225040b05400301b441a50f1122000401140c02c803400c03100504a4405801246c4580002c1200d1200382c0c3e00420702062410352380c850144a00a00d101054130b5014030403000340250700f090110703021501c143c5c02402d0b1010341800d1120560b0703030301d600072603852800700c401030400140044150003508268000b0003130b03d07008640880c00140c0d6444004054039100e0044004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 827729091 1250 827727841 827727853
    0x31b0c030e1305131b0509010e10230a0e0114060c121902010c03050118090201110111030f10060f2708010501060e09090309040902031005070c0c0501031a060904020c030705 76
    0x811840d40916075211741c1c11915840340c20306100214142800601030055520341c2240042c2400c003c504420016020b400c04807503030020640060180700a052078000d1080c0045580030561356100039000e41241c0f41d80a124800c403010a0500200360301c40086038201c0d0040b141a44017941c0114018010140c2040881d010b04400d00d40081c00c4910060303003002050f0030a80100034803a807461320011803d40001000442080300d200603aa03082c04030042110710b5080c91840301010041d80051440740c0030801c0b802c0c2c9160b4450b50607005040d503038004c81b408120300c80324103418688922100300c1040740b40341e0962901c0200a01c0310090b90f045a10020441c2e44600060089551001992107440d1007030311854040d05001d41010b40300e01a100103540100d54440c005010b56804201c0d0b00000c1440f00010085824800c500034407002c0c1401081d40d10f50000d0000082c554407038401c1188981d00044030b61260b03c81c507420400c160744270700b085c00e60181d006d1040d00726200c1c4c14001015814420307002000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 827730341 1250 827729091 827729093
    0x7150804060501061e0311161103010b010c03020330040b10050a030f080f0f03090129090a0b031c0206010801180c0905060103020d02030412031b0c030e130513 70
    0x1c2501c6058100e80200410a9040041344052185a0a500c2800c0c240414503140b483d40b0850640078030b100c10802525500c0b00c1400340402680c0a007251001600280800c445500054881c00d15661006005910030000700300c40018180c0080c107250f5504460500c400ca03102c4c02c5c0401d60805440c1500d035020078074144640e40e10103a075848000c00007072702d0b00911a0301d59181c40310303a010381c0c0300c0c094800440060045d000d036a014040b642040044100a902c900b0003c0c4482d00030a502d1890101c000050405a00704204003002481c1800009000d02c26958a40801c80f02414403407060542520859882c0c0c1052103e41d544140c3e034907500e9000301401e614161406083d19440c031186041e020001180718003082d020322070142610085000414107460700c10040b0300074030881866843c41c5101105101c01c2100250001d8040119640d050200d5040e0514010042c00c080ca040c8002c0b452920601001900501400b44811401014028035031002070313100068400881d4003090290b51044144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 827731591 1250 827730341 827730353
    0x1206091a030c0102011e0f06050a080f12090a0b0c010e06090a0201022104030308101a090f0109080d0e0f04021602091807050402180330030411060c07150804 69
    0x20000001d02c02880341c00000d06c1042c401901c0c050001101c1c0c0d80b500c1e404009158070f80c01007002004042c0c501c03641b9681d1498607d4030f030043c0e0f43c0a40c80600448102200120380f40003a80d00c0f2180c010301c803c1c1d0092921040400941c028150651075540b00c1e2120140500144030310b034031410241003d400e8652040c03000a0400c501c00360701e804903400301500382421020090603641640d81c103050018480e1210b19040c002402c4540c403010312501c1c0480e07080860141000034204d24502175800700d408001200042d20421442d004180d503a920003403170702c840a845071003d0341c902100074081203860324601000c60142d0340580b241540001a1415403411801c140b40350300d91010040c0b03001e80d099518081c0e9180c072080544901c91144c2c0c0c000c2584100484021400805121300504980340f107030b2592042c0d6036480c0200d40c0700d50105280ca01451032402400c003201e01c03d992001542a5040550302003041c0c83d009002400c40030710508902045200d0b005941b010803034107a440b0f058a510340352030300f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 827732841 1250 827731591 827731603
    0xf060e06030111070f020d050f03040602030a1205250e0411030912030702032a030c060f09030406020604120e0303030f04021e010f0e01111e07080a0f031206091a03 72
    0x3034050040100a400042170100c10700303460b0158100c81c00080c400940c00c103103282000c02c0d0000c958034000010002081034000004000c4e9031740c0703902c950792410403c0c10183c0480b00215000c00d1072240034940422a1f610301c01c1c42d2141d081140c100b41c42c0c07407110310001c40d080f0f540c2440c0350a0501f10000901c5005c01c0100100701d5110090b0030342d0b921b18604100001e44901945170705040d68140c220f41e080a42c061f403c103600001c1108011281ca640b40c1c411503545d6900255900300062440d18040348040002004507010f481e52500185081e889a50b940510198801034650030414100c800620664050000318012221120b180310141414010403d0407441085a00105118407071000c1141e60801185c094070030450410b50302004030303c001a900100d501404400c14010755062001c00064601c8011481e0742c588100d4103004d032211103a9580e01a1b014004c0c200c0340240603001e00180c8140f0b030112004a00120110304190b03109500000d9424481080240340c0c401c59a05800d41010094 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 827734091 1250 827732841 827732861
    0x6050301090f0809030106090e06160f090b16050f0615060310140d021002072402031c02120a0204051306051c06061703070c06110d120f060e060301 65
    0x8104076111551000460300480d04018249103003c140683c581e40c00f035106000038001070b10240031104035600308507111401201d8ad5410b802d44030b80005010b41c072a03003600c0d10044e201d885402a242c280310f811a401d8004070000c0840d851141564400214140f01403040000c0c801d0080c0450705225562035105456490701300c2c0244814802c1007043d80712480b0000c204c0d0a802031003001c0500c1c0c00d010403d000010800603401541032400e0600b0b107607000501e20f00700d40c030507120150184500c00043d00c1c203001c4c5403000b10043e0300500040075000011500b00031920b084040c018a408800c1c240c02150f42c10440e0b9654415602260401841c101b00045e06e510b240f0603401003041e64144000109003d020002c942c1d054401080d000e000c010441d4007005c0070780b0310320036190014035004001c0369480d407003d142203415085501d000a4898000c42440e50114590000380800c4185941e01311020150a17a03000300543d1a15003005104d1414031540340580302d686d44800240c681070301814290380200307107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 827735341 1250 827734091 827734093
    0x30e1b06070f02040b09180f0f0703030e0d0606030309170114010e130f06050403110d0c1506031218050f0f0d0602090306070503060a12021011100903090504060503 72
    0x18809040ea640500716031107940d1044400700458540d0021400800101c0401da400841a0003808400081e99800c1c54251640d0000c80340035442c0f40004030f8580b00e40c8200e8610650180700f040c00028003c6080c66940003025004205410039500e8140c2540c02d9540154041100d400040c081d590711001c00d000076100401c02800041c04028020301006814419003d9100c41034011641407001c2e548a074440342c0e040800000a0342050910b03000500c001c2d1011004a1106100c249010202045000e80340c07a05403a1400560042d4603032500e0690065800311105903100c80200004003074696242d00c5541d03650b52107030654650750b000d40b140c04080d000203200b6880c0900c203004640d1451040320034a1426501c01e03000c100c0d2490190043d01544140b1541800b03024100407445500001562007011308030b03254000e059859a82150300012400b020350030940c00c0544500403405028649201d5409074103c400d0300401c0310b0004200c42a0140450005007550002c011034501802240041c20f0220 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 827736591 1250 827735341 827735383
    0x1c08090c010c1220010c08010e01060c120c11040e0a0309050405010f090f0e0609030d0605040b1f0c060e070305061005090721020301180e0f030a0c0f02030d030e 71
    0x1441e07000f040500a500e05040080301105151604028104107080080020091148400c4000040c000800034010521601c1c0c0c0b40d400090f82501c19500080c48a80000c408032420058160446040070242c00590301d0315201d25007103049840e42d02c5041c043c980c1030340c083c0c0414001403500401600003548a0b130300c00c03418640103100303991281940d60301302c030104d4000058881d0210301200141c000e41c41104410301408003040707501007020005042c0008103141c1000281d44803c20030007200c210f100c11540009002149078840e8207000341c95486411641410302c1c0c001504c0d92044107440007001c440c0c810313070054a0108100101000216000383c42480300200c1c0c103003071001048066074010034120410040d62501d54407130346980e501005551080006540c0d0f503855500e139043c884420540103a04602e491482c4028001c0821808040740442c1f014514150b00d0300b1f0202c0e054100860181c0714000c1102c408801650700b088141055806d680b03000c5101080b449080d801e101e003003100d15844200351 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 827737841 1250 827736591 827736593
    0xa05090c030c01031d010501030b0105090c0406080a0b0f0a0306021e180f180c0406200a020f3d1d1009171510120b0402031c08090c010c 60
    0x401ca2005002013071a00043c5840301040f102e0244a2080d00b00c8425464900040300380320302180018140c038001d840040c07041d1030321001d00c10148224031840c40001c643c940840c2c0e40071003580003445840323801000000d4000e084d500051f40b0709000d40c07040307a1540e0f001440d020300401c405055400341540149131410020380e803001500f480d40c0c80b2101845209078205086042c0c0c1c88480c141c00c80000030301d03110018a800f05060007154420700440c00400c00b07615070b1080f1807801c5801120401d0012020304084401070342032090400c40d0721034555105020f0a204460100303007030a02001d003101d0807440040008100504040010724035601d1042240160b0f6101110441c00e011039084101904d00140540c55620210b070344000c0ca8002116509001030304c43d21800b00002c0424056218104030329541d103d0111040072104544165203d000d15100b0300c0700440d9142082a5001d4000740c02c0d240b981c6d0360a0210050341d00324004920100300558207024040070200b02d6114046001e0809803c0c400e03203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 827739091 1250 827737841 827737843
    0x10812182106010e010b0705033109060305100207080d0e190f0b090105040215030a0207021002031e0301080a2a17010c020604020607021c150903020f0d0f110313030b0a05090c03 78
    0x100420b02003400c0c00403084030800c56140c861000c4501c1002b600c5601c0341e80300c05445002e0241ca00c0160307903511511004031a0042c4900c21030b41c0d0340e607002c0c1000340341c4411410548094034210054004a0003401d5080740d41e420001d801050a900c01c0300000001c071104c0c981010000009440130110b40e1405013000700513150007000450b0046c0494040d030f225030341c0902d070501034400d07188025001505840c1c9254070580000207046141c01159640c00b81d4a103000c2200f106000c01d1090340c84c1c0d9844040345801082500b80c402906034802d405544401c02401c00d9034038460748650108030307100c540c2051551046400e1060300c000760032501c050b0110342010340005045010b0000041d106032100400444122400f201c0403941c0342d030040003111411400b0b010311008000b1442e041d000f40c0100d014010301c006d030101c1ca409010400e41c648081c03130075540741c00300c0d52200340c030000502c588001c0003480d00b02d10183c0103050003184502c1089100f0302e80944806d0035220068569041ca038000710340310801d9a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 827740341 1250 827739091 827739097
    0x90204051f080c1315080f0a0c2007080319020d020c06030f1e0406020c0d0e060403080a051303150b010c0b0613090f0812010812182106010e010b070503 67
    0x5490001c468858101c5078071400399031030661141034060101c100d800c0038039800c40c00e154840d0360404000c52060751201d030b404049c2d525010380741c07000400380e00d00b100010741c10b1001030b09040081000ca852180d200d0b4003c80c519845113201e801e0713508a422920300a0380c1d0403c908000100148094103a0340401c0c000300d0a0303400b020344a01d81001c0c01030b0018084402500c2d0b049410502e070b4088c078200b0304181c1071040c029403010100040c207004444a1205041c0603081c081030f2018003030019403500e465a210400150091078049007004420000300070303400d440c0c0b20300300050360080d62400f40055101c1c0e000c6084448114500741407241225034000400c50000b4142d60000040d100228074035540c1d4054001804500002843c0d040006c810000b400070ba440a032005024000404d196071340c89084c9140d4400341d160519902c210f0400550f82144840c114044c6c1c1c00d0005804007054406030b14113108980c00100d814111036203c000104441c20031400b1090050202c482c600c0d143c01460b483e815100c0c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 827741591 1250 827740341 827740351
    0x721050406050414062101030314041406030a0b090106020601082419110d0509010f06080d050703090e090609060604060501020a0803040c0b211e062107090204051f08 73
    0xb540d10060f9810f070317890780c0049a0070031b004038403030000081100914040d45c0c6000e002c290300184a0103d940c80326015802200e09584c0f4a4515001340396022003041010380c03001b0b1400f41070079182e906614050f241c540c5c00383e000e80900c2e005088075605140c4401e1034160f40c80750510400310680c0421841a0340c0c3c901458000502e01440902502c00031120000b920744000d1500c200b031070000b95458001c00350f0340b000317000d014000700038000c02c0501d010380c4040e80c8542c050308125410290820710b82601600080074268402e003040c03079030b96940f01000140c10304100c803502010b4007c0740420110000520801d80e01c110700701c50130400780e801d020000f551150060802022002d00201050a120540510100a0000c41241981d07104619082c103405004c80354001e01c4044030002185000207000b01741c40100407420140103059407600e0400c681c1c1528003078100580e00010301c60200d4071800344000c00c05042c03644005030b0f60303c0c604010f011044480c1c0304203d0800c40020420000181d2152030a6049 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 827742841 1250 827741591 827741609
    0x90606010c0f061d100e0d02071e180507020d030e2a040f020c150c09100c020d031d03060c040303050a050c0a0c05040f09020315071407210504060504 66
    0x440c020f032070200020541203108900040b41420740060350440003441d01001c0c00389200030f010f410000d911440c1c1e10100d041d112005a081244284082c4036800a4640700d5000c0042e00309106a8a0701c2d29442c0390005403101440c6929013040105070754041003400145100b520341040204100c40107161210503d041e0100c801202d501280904144080c44a84a02004008108040c03101d07002d88000e41c085942d0940307a0141c0c59400101070526490f90384a11130701b101140c60000207504001d128100700c07003490280144200c0c54800358541d42e00c0c2c0d4400d1840f90b00c0300300305400098003552500e10305c039055a110f0352101e0b04100d00b090741b44042c2d8044070f50500b012030f10340c003c10005039030b103014010603180300380b00d80c8456005004820b019107003100e10030f4400300002280e401f582420b442d0903202c0070303405034004003409400752056114964400610718010030301140c8107042811550010301e0581e07402200e0b0301d070402d0900500c003502101c10324600303003507161500d882005001400749210b40100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 827744091 1250 827742841 827742863
    0x509031e0c01020c162d03060b060d09030e190302010c060b0f0909030307120209010f0c1e0803040501050703050609010e0c0f190915090905040f02190905090606010c 73
    0x1800d07100f501912904845441516946288040c103000450020710800c004103c2046001d030146007040707681c0389800404d004425145040da00c03844003030150503074950b4006404110000d0000c00c3c2d0f00c44e071100c092007951080152120102044004039210992000300d2322205801c200503a007000940380520b6000a000c500c440014000032620800d0880c4113411058807020000d5241b13001c4001e606c0741c00d50391070315a210605108044102c2c0900400240440c8119085541d00c0340034001c40964540f1601e040740006503040d000e0307000c4402c06401252141400300c14002001400e0150aa1100051800700045d2a01c0310004d40002010b1040b4100d04075040040b90202040c0e130225030101c1c3d05650450750350301c80c4111f01d83c2a18482d0042c180050700604000c600195401c1c0c0d6050340161990760320300300c1c50802c24018010f1002034012a002000c00800c10b00584032100c1c104030b044004111040180d141c001c101c4290351004207000810380040303042041e03aa0300007640f044015001640048 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 827745341 1250 827744091 827744107
    0xd060b130612030210060f0b0304060609020d02070303110a0c12020a0812040302160302090a1e0606090e0c07170c030909010f08100908040605031902030a0f0509031e 73
    0x18000c102020305540c1681016004100352401480d1142c20034440c0d03007220300301c00851068000311149400713001118008198200500b0030390f14003441c4c20074015400003614903950381861080368410000992a5900480e01109058062192400c5009008002850039905060041034104d006130000c21210040a00349d428a00c00c000d1003138150340c0002020355a07c4003400c2151000411107007100140b0810b6030500581c9004100c090840340e01400c07422040c0c0ba041b40c075201603c084040100125076401d14000600f40c28041c030001003001d625800c100e54101200c4005807800202646501e00f820850400002c02c40d01c02e80c58480400d65040340ca40e14404000c034214410201d425070300c1010400080303542541007440008450300c0c201100c0a0010b003003090803e665400c100079200110510003004840c2c09400116840002e90040d401c498603e09060f0003240c0040c1d60301514251f4600c61289aa40e880c860150031010b40700080d420b29214680010390001c0402800300083c0011904003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 827746591 1250 827745341 827745349
    0x902130e010b09040f09050a0209071110060e090609030d0b0604091e060512070e040c0308130503060606041401030b01050c010905011a1c080c0a1208150105090d060b 73
    0x190141440309080e42003965100380668090708400d0b41a4483c0d03280612000c6200308901c00c81d40c80036408000790820254035020409418030081c4500188841c3c80407503203050380c0c1840794170419207503882d00042441c1132002c01c490911b4028001c1200358800c1d0b0600550740d80000984442000114021503124020b502103907050299620040c0b03100d081501c50f000200b881810342000180305041002480e0b9500700304007507410f02c1c6155042d0780d0072040342400303541280d02c0b00301d9009000781700c007020b45a82d039a41e10040d0340c000801c0c0c1c1000b1640801c00d004915040c0b00d102d82100040356010308280c28562000f00300001c21540d603060503a900d907411580d900500640d443d04010f10002c0060103140c2c101503002e4400e882c400100000144441d60075840c11170403d1601070080c160003106a20550b6401c03206030b01005604607140300e4601580001200a0740d0000300390200d50366500c440c203201120070030200040803c0740c180305060109101c10344424540c0c01c8040e03000400400e6481180001c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 827747841 1250 827746591 827746627
    0x110c062e08100e15040f110a032f06040b090409050a0c080c030c061c09060e0c030606180403081b0a0306080f01060b03061306050303070501141305030405130b03251e0902 75
    0x2c1d0707030030074808e80e8000103001050328134901450b2020341064251300c0070140000c40030141c0c40025407050060200344100b500400145c0b0601d0409803000501075407507211103141c40139001c401c03141900c2c440c0b4203200c0003074180174100450074180c006110202505000800a0003030181d81d60404168504861014001703401013500d03d0b41128081209040600e034050300c0382540100507020f440b500d00880e10b02c0c2045081c62a0074548002c02011940b22994100c0304150081c2c40140c81000000d24020401024001000207041c1910f00040443c6040c58039410002401c042d08501d0345010800c02281007140c040701e5111104941240046408071203044c02894550407481d01440081858410888150300510040f00003044034000c0b0354651504207410000300300014400d030000d100c1040641401820a060607241890201d240107503800441e1800700782041081e250040c018000c80a4408052960042e00d540c017501403410083c3c10610250140611501225540c0001d03441c8000b05101e001c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 827749091 1250 827747841 827747873
    0x108070503040f120206090c0f0607170409050c03060f0105031005040b0102030d1d190c0605070f081603030e03070b0f0c210406110c062e08100e15040f 67
    0x42e009003807013480000e40e00e4504550307030741062044420302c489501c0d0562265080c0b0310018211490302c061a1340f80b000c1d0209410141c20701c00024000801d034013541e40202c82c410410140625101d1512500b0011011054070601e8144030081041c1700f038943c040190301081d00c2058501048900a99004030315500c02c1e803a615610720314261099031b10240c4645c0c04411016508204c2e0850000581c150810a1034a4001042f8805500e130403c0094082d1028004035030150388500190385090310341c50300c5644038150030107988010340c44102c01c0580500c03507012800801c50041d07080c405c640d0786c0c505140303001410b0003525450b46000600d01c2084042103034180ca01040750b820a5015260013050000000d48040322006d04058460342007003080c809071803926405200500c1262a4010502056414041c0c54800500e20071000902c0500a010040003040088000d22290000810300c1c41101e00750707280c080058203e001d035500140c50983e43e40d42c00c19001006d00c420301006240202c02c070700141c10307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 827750341 1250 827749091 827749103
    0x200a05040c0914180f0c0904020c060a0c1e11010b1810120c0902130533040f060f050408062d1b0702060d11070c0b090108070503040f 59
    0x805010704035804910003045510b401c804240200780c050400c842800e40e500581050900b140000b01c1c110100d44445030083e29020140d49080072140104003603078013011080105502c03203028000801c220780b040c2441d00c103c610f0000d004031a5201002c18881d51311010500704050b515888900f031000794041c51209000900c201e2680d4041d564051060004445030980c2605144000075036145840e0280100f66200d00d209c0640313418607003d070f0000e400c0108000003200910901042985a403190403c0010b448810340d0242c040d40c010807004408000c070811900d41003804100990b100c080007901c141c2c3c40c68200000582641c1808a4007070140b68860800341c0710f80130900c00184003864280f4112010342c03100e0140b1800606914495040c2640e0081840320a0300c42c0c0141d11207480042c1c071085100500d43c03480c2c0f40c56242c088050b18040c0001000202c000078400d410402c1801e2100006c01a00d00c1c45414044103e001a240850050910742840300000c00078081101200c10320240d00d074000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 827751591 1250 827750341 827750351
    0x170304180903120b090604090f02040c0305150d080301150525030806010e03070315020705062d070c02010c080d091109180304120302010e030307020d020c010804200a0504 75
    0x4620030107000980700540100740b440d20072884040403070007007404912010f003045000c2e0300c0342030510006041141c400d440d180514041000169201d005148601a4030b5501050b141030500c440e040445400d21100d1082d008003a4281c0092240e9007a00d04540154003903010301101c02d03030306603468421882c1074960018051644803d118a0440345400715001e03641c2d002071a6540c41c01590703000740c03442940d545940a000c081002a407081248984100c03c0800542407503260355a05240400640f40c007035005000c6040149001d10b109020102229400220300b51400c1602c0050141e1070210001390400c40d84860309070500561600700c540203030741040c2c100025561401c02050a4441201c07c502c20303811003020503801440b20080c0206020f01034003862400c0e10f007584149070016126411829035484188103070a122080c800341d80b04801c00e4019100b410603841c402404d292410342001d040c04031403070611001c0741201c4448203c0030340b850b214403147c80006c400101c0c0305c1d01c9035105070340c071034101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 827752841 1250 827751591 827751629
    0x31202030706061403031c112109060f0a050723030601080114130e070f061808031812100f02120603010209060f0307030e030703030c0810080304170304 67
    0x8010714106009281c10401e80e6124542d010b0160310340707100c581e031680c418042a050383c082c0c41d201a00000f0700000018030301c00a6808908a0b03009192641c09854541c0300c1006194640a51350740c0c4009110040c2c0020325100010329184078002c0c05221146e69150009203515000340800c5202c1d40d113038004070310301d00391802d04281e59500483d042400280c110f00000b07a0000e06004080941100600c2070884041020b6014024000700300b1101030b0784607449000807660741102d00d60014044075951000481c0400c0e4138501450520b07031091001c0c0d031003040300d41101d1080c42c1901c50404801c440c8000c5031800c442c03901303107841001018008018600f0400619105203940149840d0711083c00780c1c5241e5440b80205800c0b0b00800942c40d800000400c846060b001d0304400070355001400303060000310360542e25412441c503000954114003107599595003100307a0742c00000d182d501940c141c100380c1419040441e0a80c49015030711070301307244012500b5407082114007801560050f180b20810b40010000d5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 827754091 1250 827752841 827752843
    0xd020307021606080c090a0302040c2d0e010f1e11010c020f0303183306120d1d04110403120503010b1914070c150c1505060604031202 59
    0x2059504202501c1541a546845006444118103c5180e80c07200003180e41c40c01c140201e541d2010017610703484058120003000513a241d00c22002000700703035035800e1203810180119080864200101c510b10000c05d408000765254030406086405c0400c0c0f900f48295a00030000b6114801c0d980c16510b00c49008000b000180c0d5400900d189800ca00c400081c081c0050001060b61124081005854160010000a00d0390a15102034000240000080341c42210030408040c0b070540c140f940400341003002030710651070104e09041c0701e600400200e0f150701108014980031642c55880364482e005001c0b000c0c0d00d07a13111000120300304c01d0203100a8000c0c000c0304620266143e16512a010880f4007071020306910b24070303c1c42032082da41a035002025080c941038203031280046448a40c0c3d0030780c0c1040030b07281a440c0ea4403440009041414801d0f54407403105400d1010300060b00c2503108030713201004002c0d2a010041b540303841c054a000201031000003481d80340c12007c100503101d41c4d00060904000c200c5800c40c44c580c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 827755341 1250 827754091 827754097
    0x70e1f0206070f0c15240305010b1f0203120406061205030702130e030304030e041b05031504202107020312130f1e1704081e060708070c080d02 63
    0x10368940b40c12001c014000d4424621140005d0b051207607000701c1ca170b2058072581c4900480410101080d155082c9060422a0103034660000c8904d81d46810300d12805052074008114034015809140210440b40100299a070040b480e160581c4d0070f140380801d003031100a0784140d0140000c00850a10902e06042090307a0380c3c00540d00704d016214584070380d0058450761140c11084154400070710b2441e252a10100d401e00c0281c842294415170b1180c8110b00c0e10003403442c124403810107072903582e03c2e841c0170b15082401c00c4529850900460415900b0a07007082c034142e070302c0c0b0701810f07403c0c031140c9405551403d03581d55904c291141c065004082c051004c0560008050200c02100c50380c828031503030b26007801080e02150b101e0001c12030301c0796011200001b0441d00c46c152420141d80118610021503441d603840445028168402074100028248410700c82442128006280c2e00e0507a010807450118141c4c0c0c03280001c10000820040c03070007080800e440352009c040f102d074108800788d031196484581c90000754 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 827756591 1250 827755341 827755351
    0xb0612030a0504140f03061801020c031303111813050a0804030b040b182d0d200303100504020304080c030309030d0614030d0e04020c42070e1f0206 65
    0x52001c411140754034001a51640c0303c1c8001d03002c0d0140f51502d04200015523801d41b03144500d55001e0280056808040000c4d20f400d00703000e1806a6a1407a5041001200102c44021809503a070f04505442c00030314800601e811441c24801c02c40744203080e08056091034070101c0f004141820004000080c0250880d0305030182e805040c4186a94456036010400700c015603e5800c200e400c00031405a004070310304150022015104050072626482e140c0c0a42440c0301105200c0100e90322241c079402030a40c0c00704003840315074900010741c41c606200c0b1b42111084d011b886224407a503000800135041144050503500940c00400c103c80c2c03a8182828100d407603810422010340b14a00c0d10702c0005001b04810380034010800d015028281d0320321407200485101c03c6189551341c00179000c11a558015104100d40900f6070455081480c2c0d09420142140d1611254a008070100080c00a03c0403c500340184440d00400c603403c09803154500034001c42c0c141002c6a0403043d00900500c008048641c001c1200c500c24 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 827757841 1250 827756591 827756609
    0x6050307140a0807030c0b1303021807030509030a05070f02060403020307030c150c0b06041508030408071403012a020109080d2003070207051903050102130801060911070b0612030a0504 81
    0x40740c4440d00e56680300130600c0041c005035400c074410000c5840311001001c6521442170580c0031139480c5d40224003600441e10b2401d2a0300c2d1064100310382168148565071700002404050362030400c0c4207000034040c1c0640940a030403820000035181c2159540c07000c0383c00440d03014040c0e0340750b29981d0a2a0401078420320481d5405d00d036214021400c94407604031941410ba12413002041070300e617141800010031496498208001107440041000c540070400313040248150720044c18440c1c200b00c04000e0034900c0d1071515000781c0c1403034855480300340c4064104e05c90f81d8400c0803d40000d03100100c12809000e640c000034044a40005001c91125403542200d01c03403540742c00e140c01c10301a000703e03c03030900c0c44111880340050300880707810b01a030f26289081240e9101c516045580807038503521820b0032617102d054501041c241d66007040040705800c0c01803000070b02d030b0700070200045a1408000c030064400d500c0c0c002c2c1148440300c00503046d03540c4c0c90341e881c0b10710249400307e0f9204e840408002e040c41e07125004610300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 827759091 1250 827757841 827757859
    0x9030c0c0f010807030203040606030204020f1b0a050c09151c1202070b0d021e0313020a060203040305070306020318070b0406021614040504051504050703110108040302070e07030605030714 83
    0x250600c41c2880340003060694078000f1503a9040011402508003400c11070f000d0b500c451000004d0b0392180080d0582000c5808881d50741c070840381181010048007400303400103821280d4241c01080e80859008040d100940b0044059918801142c040444407100207034010b046c500144058400e440d0030103a114415070380c0c4100d4001d001c4050342d03690968410f2a00100f4100042c0ea41d004081c0c001d06100c4400c80264000c4a1488180c014103400c00c4541c00794070501200c8034003d610342591644010f04081c000f5520349401c2d5201d441e15481c440c04060010b90700040410740120111f141c400c9011500c20640342e00f107488060480c100e45c060b104c3d00e401440340e48001c41040c0b2208100400f01c420982c4405500702221040c0409444010070585042c010086440300400c150014284190321031400340c480b15003076160001541c5207046800e41080026401c1000291b00042c400f01919080b04ea030001035590030204401030031440c0c005580600506400080b00c411245c03100001a0044a100907 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 827760341 1250 827759091 827759113
    0x102030705060f181603120e030303040b1005090c030406092a08010c14120a020f03130c1203020d031e0f0614060906180a050a0e04020108060a050d1e060509030c 71
    0x3a03101c0c41110002d5105d51840c10800000b007060758219203000e00390070031030348005c03443e00001c0c1142c104403800d42d01c00e10344034200705004000482c1440500701c1100d4800140c24020160401d03400010b0000380180c1d0740d514001d0901130040c082030191244c0e0050b01d07a4403082c4031455020b10100e44541e644541c2080440030b0102e01070700c03140f40c1100c2e84501d01c50400b440700e1401c010b581400741c0451019503080024607044014200158801e0b000c0000702000c030811841c1c2220a0015507019581c0700a042038008000780d4046400003d0142611b00030800760b65000109800da20901602c040040c5010405244800103403c018100e40021410b80c000c48040b00c01e0189900c151190325522280810002e040c2d41403100e9a1040b10700e000d44400012521400858403801c030a80000c0c0c1c0140700603041004542c2d000381503591281090751800d900e6440c0c14080b51104031050300092440d2101d02e0f140e1054191a411040740c00d420010034880d40c202101030544a038014012400d40d0302841c1e902c94 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 827761591 1250 827760341 827760343
    0x330305011505030a11040305160b12041202120a020c0a0f0605030c1305100302090f041a01050a0c120804020a171e0a020a03060b01031413110102030705060f18 70
    0x28121081c0c0c41030002900c1d2858802c4030550310042101c03100d00d5640700c81d49106241140500003540c40b0751300401040c072034105c449501629613404240c5076441000380440c50a41c46102d40d80140e41b000200c81d40b1000306c1030030381c10080b04400e040741d200300200d44503c0c80e030360002d40507101ca4401d64440400544440c0d920303101c264103000c2c00000c6a030420100c2d04541c05000202080f04144005003000e81c1c1390341c005110454140c1c10751000a40100d55415540b601140e03010060404407000c129080e0401070a41094070b640b420503061240124103c02040c0c065070f810213129920071000340c2034602d00352019000d20010303641613002c0c000400340400c4182d81040e60100d6640614000e10412603249020b01c5082c1807859905803e0103810034050042c2c13100304207a000f55100f69404520945520001421205032400d2079034058000820b00068601000c2405105600308901080c416041030050346903104510b0000d0880c0f180004111200c0f40b450034903401903c4400310061040752046c019 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 827762841 1250 827761591 827761601
    0x14011e1505030618190c06080c0717031512010e010c0203160605060f030d031a220b0607020a0b0a0f0512070e12100603021311120c043303 61
    0x50b0103a00401c003007030a070359001d8000903100001c00101c800d180c4004808000101020a04907803103648a001401039540007488194003551b0340c0c000d00c2c00e0007070648514518030841002c04000c4400000801e040300301041045042010182512812401d02d4407114001e00e594003113000300d5460015500b095078808402c44240c00304440302c0481140340307510307044003c000c00342c04590300c103921124051094505115900d0500d03015100007030200000726401e40c041c0c6181800c10b201b0b400707004040545030301800758519803c1085000260002c07680d07022910612583c1c802941c00922507000180c1d44200000034000ca20302e41e0307a161150004010162000d0040112246c107080001c0300103400103204500403102c9200007401d507072003a43c03842016801d251002d14200e6003103071a603405000750304040e15800003050019500b0800c0e8046c008103451a805210302804145050030040760700443c542007514040c00300c21000788402d01c100380c5c5002452502d450f1180c041c034003003200303c10f1b803901078811 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 827764091 1250 827762841 827762849
    0xc0a151104121103071503020a02550803040314030f06010e220605031e0d081e070e130b011202070201030e0a14070e0114040914011e15 60
    0x40900e007002e0703580c90300c10b0511034a14050b054840c2141c005458a42030121400741c201c1d50f1001640d503046041d000703082403003500c80015101e00c0654040b09800762039041702e004104039240c60701002c66060303001e0441c82c80300710302501200700e68004505000c180720085011f944070b40c59540c9030740343d0040d03c94101c1c00112401a560304024002a0182d40034050030720504c04c00403d420a400000031400350f403a0085214201200e955000501c15800c0030080c0d03010240d03101407014400214030105903943caa040346031200b0440203501080d000925020f0360b65107030310b12051203040b42c604043c0060045440001c024401c091800b00b4103c003c0072846003219901c01a96800c801c2060151140040c0d40103030030407410541c9d20001104001814021030810902c64400100303c0c4020105407460442c00e40c04c071803508081c08004011a0300d07031000807100a41d0554020603000824103020403900601c80760614a5420009400d8907110703803c0c2c1201c2ca410384441c08000007402086900b1303c2100d0307401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 827765341 1250 827764091 827764109
    0xe010e0708011a07151805010b0406090e100b1201021c05010909020a03080313050304150f080f010e060a0305100519140606030a18030c12210507050c0a151104 70
    0x1282c080840c01c01501d040d44424200350108214100c10306c0b6110600e1a01403d80d0b05941d9401c4025491801d405104010010f2160602c01d00402844098803044c02d0b01c401282540e450f105026942c507004001460100508021034895a0750f05806110428081c03044000074607080020900c0c8400b40704800c903154026088460241c11030f039810301d41d944003420b200340d400144900300d4000340c82000240050f14040c9440c64400c01100c201805c5070b4800e9500341c05000107907040226140d0305a149a0444041d1001c0c00055190038010400010381a0070203070560003120959070244c0c085800031405801c451103101e000c545000c0c0100221841460040903990307440c4040781c0c4610f800800703560010a481000500303c005455082400100d07460200c0c003081840306074100b840100341c1d00340d00282182c00c00d1200d402c1c038682054504640100c507089036980d24400320304110700c01e03801c0c0e4410440c000100c404144950900710709002d0700907801c0c59014104003203c0035000d0050165021540425 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 827766591 1250 827765341 827765347
    0xe0d09062a03080a150605070605060105040e0705031504050708040b01150f03050a1b2006070905011d09090304051e0609240a090509071d060901090e010e0708011a 72
    0x780e0103e41c1c00001804c400f13050394a481840c0d503a180364600540080150b511403a84d907141c076180c10403e95400038121414400240420000015000c2c01640c2c4400d192901607581e035290440c1d5159400c2da03240042d0840d2030002080300c981c0c4c20050340d501031400750801d5407072680d80e400c60390f0440a10051034000141400303c48110b440c029080980c02414417400400e0002c6000303060f41e1001c903450f840000188a48429598903030528803c55404000c1e4000b40009180001303020b0301c0700c2510320884e410400c08020855028402d0010340341011001440107034a820960305642e640e420502072288a6a403088500d0b6503810b684000300d5404c50054109802d0a00d50410003400040c1c501040095820701c100c446e446407094801000e07440748035100c1800b0b050912050145c0c2200c0100203c003401000807002c0800780090584c983c10100071142650f44d401840c0040b242d071a405e5021801d5020300e0f000201d441a2031845940c4102619030f15060309a0f61103095180c2c9082c1801c032108600303810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 827767841 1250 827766591 827766593
    0x3130e0c040513180c240e1e060f030117070509040f0f0213020d0b0a0f060c05100e0604140c090114030c04020d090203240718080f0a0303050108010b0604090f0e0d09062a 75
    0x46002c0c4080e02320081c00120b40052401040d0b041d40240c01d4a49031140000050100f030400c228aa10313124005401011030a00380030115412400181c00a0800e0003603100c040100094440d036404c1035680500180c1ca140241c4120b003000c2d40100e50001d0311242410403000890901d82d01143c1161490030705844543e19000c0b00340d070301e901d940d074055590b80142c0e000c0040e40c03880c43c0100c03120840d6090040c1920301c0c3c6401c00000018401070004110f0700142c800c451a9910048210b0555084103440c0d0340f4044000c002a241202d100300b00c0d0740003030001c50740409080d0303954004a82c6d50f000741c09960b82c2c01042312604452020700d018800306010f044012404d2144204040c0701e02c3c1080003403c55005444060035403401041e907044008642c0324202000c20103030b142c06180e006285101c0240070b42c0b5240c0c00094442d004c1c60241c0000550b03a0301d9035540d0807025030401c100c82c100c1041500c035891b20040c0010440c0e54140209004a880400c070012042614000602801a0b6103080a022005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 827769091 1250 827767841 827767849
    0x1020706051e0a1e0e09010504051905060418030c06060504020403030c171b160f080a110307050907050d0c02070b0d0c0e100203130e0c040513180c240e 67
    0x400c40c0800304002c0c0200480c00707184441c058102010002ea1288511105c1c0308007040314001c81604402d010b0381c2450148008000fa00146852110503001c01041958074000810000c180c40f0186522040764015204281030300040c2140025000c1c910a100312034452061001760301c80d40c84028002030315400c403030b4040b03805a4a02203c4241c06186585403090003504ca610006000f108883c058101035900d8003002a41c18404004002e0f4005001030549820140d42c0c46000311080580920035900300020b056800b4030042d07002c3c1500804003200c0c4d0800c0030000344140c019000c203802052500740c3c0c0480c404d00010304142102c1c10604003501d031548480202015014554150301030103a80705035481550307155130008a000300268011515014003445078403078200300c0d40c41440002d58000c10302a000200404440c1507030410764041a03480e42203c1541d00604200d00b680c204420803001010401262801c1101119410041c50115100e0001c040712000017490034580801ea28500c40b03411418 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 827770341 1250 827769091 827769097
    0x40e010e03160309051e03010b030106061b0303200301060f0207080c120a02123004050919020a120b09191e0906020a0212270f1e01020706051e 63
    0x12092134103029456551300482c0074110401c00d1710004084054407810303542030134841d502d02440c04400030300483c0c2c5445800350640140180c218500c107001c1c01907005241c06a04911084e01c003c070b00c00325588451050003c01038200780a4840051020b900d004002c80c40001d0700402c0d21b9291018103c0d100100c410030100d03081d40c00c00c50600380200758564001d039507078103039012001006201030510000c8050900d9040d21031070907840950082d40f5003038018000c82d14161002e69000382d9682c1440c2e00d4a000815986c00c0d041c40920005000043c9410b15660014408040c074007503420034041d50b6110010051390923411520001e0820003d80c071401d4000f4687c000a4665400344903030020a48010b021106032000700c0c0080e90450f0300019090a000c0c0e0400c618850f442c21031880c5403c082499020540c100d210200700c202e00300d41200d44400641c5c8a4055a40d441c10003003450300b103900140c0c15400340403100045140540210704001800a0003401203641c7e540d071084c070490412001030291901a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 827771591 1250 827770341 827770343
    0x70b0f1803190c2d0b0a090b16090f03051c030501060813060b060a1e03020702031509072103020705060c03090418170d0b0f1324090b040e010e0316 65
    0x5080c0301c0c4111031340c042440c6a10f510002c44e00344030108000c241400000014007401034011580381003054808070f81c200702e40940002400c1940700d4401e112901c200d60501c02030b0090b41440038014000010003100080846400f20755402040001041c45419001c95009201d0380c008a0b20070000a2001d07022b030380c005000d031403150b0030000d841210907000c200c40d41c012203248c5010034444070440600425030700c03402d104440146025440d0004580c0401d446007014004841c4a503a9000414400303942480040080c02907204000c100d0b51510f000c0e0404107081803c10f4000d0f0185050200d2607083c210100c9071180804001949012140720501000b8041c2207101019811800005400241c0b280b06203c001c9203a0700c072064030307200511468012141c02d2040c45100d0740e030010903184252a00d112074000010703043d0001800c501800d010380c0111000d03145e0141d65070b05d51701c0080380080c00340e030010f90f100c901a50300300b118a5994406908132403480b68580301940c030600105821800c00d000c0d4204407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 827772841 1250 827771591 827771603
    0x703081005040519050f01140d051c021006090614210109030e01080a0510050d06020d0c03021c0606170402011106070206011a0306062217060402010e010c0b04060b06070b0f1803190c 80
    0x60f01002412991440902f004005821418071104030303401a0090001402d02140d04100c407618001403a2115088074460780d020301d0050040c0381c01d2545006a8400c22a20f4030002c0c41600c03040e140041201a105100c170f408180150045100e9020306e06c251486509e01d200126880c03401c00c1c0400680c40e040400450716240c080040303c0d0961014041c00d41e00303044c5a1400f50720781922205221442107034158149445151000400420791301c140c1c010f03a49203030311210148039100c50004031440c03042818959142d100300350900604c1d43d800940e25040b500020b1450308a642131a0a0004d40e03c001d480301ca03070010040c0b00101c8100748400403181d01c00004030083c881544d4692001c0100c000c148441422500544108415541c224035820300e00c090034a4a00241e02840d0356468006502401c0901840d56818407801280c8840c8212804d03c1d411203d50969403038011010f40440000329600800c01022b03481c0541c0350100001542c0e101000054854510420403101315210204004181c42c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 827774091 1250 827772841 827772853
    0x309350a0c181b050f0a27080c030a02011d0f0d05101107120c02210a0c0b07030f080606090a030b061002120703081005040519050f01140d05 62
    0xd03881d00685801020089214107548801d10110300407200200c09002240641c0d21261004070b901c4412102d08003a0000101e4591020180c111044503086c039510502c000a1341c10001707514181800d00c0c0071903400b001100d40c80c6044005040d1a40d030303181c80003801b054504440f104601c91060380001c1c8288058444080001e50b0b40001e00018000d0300180d030690001c1c081003007800360b1400340d200c48007102560746c0d01d002c4869541c00c64070500c1007441c17000c0103160300d0381208643d40d001070001c4481a0b2100c04944030100039070320b910303002c29240c00c84000c02401c2000a0b0802040300350341030140c250700e55103840c0b02010f80070341d018a07005041990000003001428116614030540502071406411403840c1840d04000740185c038510700e40c01c0c03420b41d40006211700300721086408840c0c1495040ca00142182c581e0035811140d0002500001c0e4041c0c1000c080041c04403a5a286c00c462071683e4100b813105442d00351910361451404e001d003080e20080728000300002d0500400711401c0c0d910401c11940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 827775341 1250 827774091 827774093
    0x8131e060e012d0b030d180f0f0605070312020f041d0c0322081606050601210c02031b010912030b030a0201080903191d09090303070c1a090102070309350a 68
    0x4201058010714070701107040d40043c18142d0701c8940e118400707007502380544c00c481800c003421145181464070a503410481d0004165041502c145568420007416410030341d100c030b0300031050042541050144841c3c140c103c1b010803880b680321541c01030003040e80341c441c5d83c40d68580a651000f0041c080d001c800044144106010006e90008010003c0f0385210391941840200d602d03158065074805080b450400850360116801e1388a15039a1551a111500d00011003603544042a81180203180c200803d0700c80c1d4400d4841c003500103400647c1810300c90903100c1c1d00710003c15030039011101c3c0c00d0032058165004140440040d40940b40e41c0741c104d482c12007200e0800c0504080d0300301e4110070700c40d0030000030180560040070440380081c0e00c10b05a01100c0b580c00318035200b038541d541d902000344007104101c51b519410081c0080590b016034410032002103410b09151808545020b540b0006044002904d0300c0c10000c0c2482440d202003074922030382c06480381003141803416007405e0114080c160f04240548e5850300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 827776591 1250 827775341 827775343
    0x60705070b03011d0603060609090a020a030b0103030e0316030b07140c010605030f010b1e0f0d0302011b0e030309011809090624080d08131e060e012d0b03 68
    0x440140289091150b4035030500c54156040f18200c6201c0500c0103404083c02002d58001c07803c1c0364403a1045d5030b04415a510108824031b403107240d0102a410a45910003c800d1011162485059034001e4542c44080540c4400b410307520107480e00007400c403940404040c000219107840c0103811940f1440c00c00d42c0c0506450a80e4000d0b80a4043c0c2042607540c0c800420440c1000c0c015100a150340c0c2e0000c120074030b50000816141c600e4a0030444500302034000c0100c40f03586141743d1036400c000c06402c0911050440c50040d00034041d4000c40c07aa20079a440a04101d58810b04c403440495074080c01131420034500c11f005442040c403001d01c60320b58081000c00403410030030600c129050207001d0340340801e50114001001d000030314050b072034004210032082d003480154800a0481c81d61209441e0203d40d95a40010008040154050013450110582284140c80213001d034031929507030103500c00b0408907801c000454201d501d01d10310303c0c4c000458244448102c41d080c5081d0b07800b904c40c01001042e0409440002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 827777841 1250 827776591 827776603
    0x9012f0307030f020301060216060203030c07080d091b0603110f0a050c1f06030c0b0c0304060c060b060d05040203240c0a02011b0201060627090908070507030804171f0209060705 78
    0xfa10040e070042801034818a015014400103081d2b03070000d14036508255903480e550f03104085014100c080002250360611619a01900b031203600005a201c12031981240301e5504103d070710071200002d08003035100716000300140440e0403e07488040000c0c1380a0303071450291040d0b0400e00d4150013a015443d450524090703001200c01c465900c502d400103002e81540761803250781c15641c100c01c940200600900d041c110000040310207a40040c10241040e40e418900319014005c2e044100b80c00030340100320305040003840c1d00017a000742d20803419200e50070049016807410030141c100f10503061101c0c80103d402c400e5003500910b140e481c50320020440101500d9074450309030341c0c85403940050b0341d00c80301040541c1d0f0194586a80700e405802d00b00041d44280150341c2d09403c140604540c843c0c0e10400754013009060021550941d40c41000d031381032280c7d20700f04030303c880d00300344541030303c0c180c07c7e06040a00d910040344184026151031440d1001501141c2842e0094010304105a0080720800c00200414010807035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 827779091 1250 827777841 827777849
    0x18012706020f19020d020f2803140109051e030d050408030a05010b07050607050f0c0604111215011701060b042d0b09130f020d0509012f0307030f020301 67
    0x10152503070b04000301c51800c04108000760300822100c1c85540140c2c3e800c0021103405404071984200d44a40800103401c890400d80a82909121b20101030030061000c10850100e0f0702801213403e52508801c1d100b400d82e00040e03402003079900f004c80300080b00019560400042000e14044a0904030710140000072914140c0c2c0c281c1c1e880d03e02004100c41e0003036078043d1a0251622040d1030741821141e0351540d5035106c1c0a80b0748018400007040030a20071101c036082d1003a40d811541156403c0c1441e007001009401c0b460501c60080c0500f80c09020204d40010300e006401c4031542c0c4404103030f8601652740d100d810500c0800d071550354a810300010b800d56000060005450340182070148019008010130130b00403040c1042c100d64041132000c112400301d003070554102d02e00c16500815041321103c1d095004050b0022010341d8248042400110031856510a51041022400030003108040c5081c3c03c600b4016514032405400003002c1c4d51280000800103943c0103819406d001c52511030f148403000603a042604 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 827780341 1250 827779091 827779093
    0x6060f0f19090906021e040e0c031f0b1c0b0a05060c01110a0906081b0a080711010e01150801060e06060706140c122410050d0606080f0c1801270602 65
    0x1c41001010702d60384268407000d012a001031a0915010b94030400c040c0041c262790084101100103105641288400c00d4450040d00c03d18202d191904403d203200d400c403803518845d111140e04004042c194a10a0001151004000301c001d2440c00381088116401801141e60079500c440d40d58060701a81c1c0c001d003190580703544030885900d040000c0240311309801045d000c003000c416980346c3c0c0110325000454803806070350318008602d0f40e01d0b004141d42401840450300b00940c038209001e4180c00341984405d1404c1c6101460340110381c1e032402c0b0b040c248c032068010002da0010b4440443c0795031030140010702d1107034400c07600490285076403128900d00c2038081710003441c1550001501a0344504000c0b01d560300c032040647e8054010180216210503080309250180143d02980000d160355000f80150342c922604202d0501c003141d00c0d80c0d00100b5601050300c509440a020101081c00998078030152030401d60b1402c01c001198104000440385070582d00500d40403840014500c104128004080e203000d0004d5030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 827781591 1250 827780341 827780347
    0x160803090f0607061b230304060b06070b1f3c0b04080714010f0f0e03070803190f110c0411040e18070602071a0703050c030a090806060f0f1909090602 66
    0xf60040c604181d15a006e02c0f6954468040c19250405481d00a0b070015400500382c8096008034003284941031000e42600086c4040103d4410207500650704401460f201c009866a911051a4008060701c81c4d04c02998105c05010741041082c1040c1c18a030000e0040b007054265034140003201907029410200540d040014107001004e01c03d00600c01110007803030409148040410001c4c48400d400c4400f10411201c0007102070315907002c0200c4009800c02109807643c6030842804542c54403c60a00800458032210080c0b1406028607100002d0740d1492003d04005880d10040000801d50300040150540e010720000c265021036400d418070601c1429244030702d04114680f003a03d021029444181158880030040c03040142e40704507030b010700e03546c02c0000d0f450300040d103801d540c503001d6041a18068403010a4014006510400d0602180c0d104001e440c0e50740c9464080c0000c0700c800581541c0c01819500980c2c00d2418010480c2e0301d46401022958441070300c8400000a40b09845000e9130312179004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 827782841 1250 827781591 827781641
    0xb030c1e09010b070f24020a0c020f010207210602041a07140c030312041103150103030809151303170112020f030703030e0d060615050705160803090f060706 69
    0x21081901400840d000c4508000c1380e961481c80c06440240d0041200c01d041c0340d200502c41c000c4044030450500c90400395207a40003440b009010aa00e0742c01a8400c0c400c94069400b2540045031040a840400428480b00c0400b0041c0060a10f00400212211542000001025144410040c00000304030100c10360f04c80b89410540c0e88440982c85840003604074041c02c06017070b41c0000459034101c8010140458582c1c8604003100d41c07055201e1401c1e014054043d11418070302c520007031141a41e101b51521030685d1511664203035107800e41e64013400218600004510710b0408040340300c180358840e103080140b0030085c2c0e15110702c0c2042a48900d80c201c041c21602e0085140c4154040c5404405400410500d461603c0c000c18803208020b210303024141c0d46940704140320054024201a000e044007080141001c054018895403042806880602400700500d600740794103560b107030840704d8035070096043c035101004200303103504800c00701544000108490350000300c250044201d000511000003114440c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 827784091 1250 827782841 827782849
    0xc1503060f04110301050f011416120f020703030503042301020301091805060a0510030c03120e030a02011215080a11030f07030f060209010309140a120f0c060b030c1e 73
    0x1004540030702c124200208481c08000e0070080d00d04698040b07400f02d082000102c01a070304000d0300c00480104060015658025011070051400d5180c802c0040c282e5203d071109040b550112000c1082006070880030b01080440d2050014607006070151217035120110b0507687c0d0800c80f15880c400d4510b641d40200040242c8030580c030501000080c20040f000180100380c2da41e9841d6140180001d111a5640c4c01091192407108055000303154030000031340e00c0c5502ca090200c000b212807555400059543d2006503136500b404581c026081e40e043e100d04403455008500038014020983e00c991554040032400a0481c03810840344c0300d214002c01604c0c40e40341411080c50b09000703914213280000e62050004000103810708202c001c03641d81110006855030178540049002c0c110311000035045c0d004084041818920202c5d0843c1043d214841c030084100440780c0076504104544002c0c400300312404818408602ca80e041150601d0009058441750380036a0005809890990b1403800405860500c440c1c841c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 827785341 1250 827784091 827784109
    0x1401050d020307020f2e18080a18050604180c0318030509030d0302030906040f03300b01020c0f0f0d05030403140705040b1509040b040609151d180c150306 68
    0x210040c1c11808844a40c0c6d059804a216140003526155036a2103610003103000f105c031880300e079601064155503000d080c00010403032440022000080e50110800240d2450940100d5080310000d41c12070b04403844c6a4883e00050070921140320500d81c480500d03940c28041140882001d91184e112a911004c1d59001d00d4a42010f4a104205043c810014003c091800240095105911003d14104202d580c07901700c400340034094141415105494205045016071610100c1c0030728074110401500b0605401207943d20f01000c80c140e0801e1880303491071041d00340380d00c0c0040d00c50700142c10340320407142d1359540524590040c1c0c0305841154410345581d50710b1206000352001050f04032402d1020441200c00230f5060b005844e0080f800380800144008607440c0d40c3c12401070035400174010002107a071006480d01502c0e1000582c580400301000c045442c2140800030b1456000c8441b444203a560b880b0b0304c50300c0c7c8020111ba0301c506480345100300040c03940c4814507007268032070203519941c17207040c0719082c440854 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 827786591 1250 827785341 827785363
    0x30c0804120b22150219030e16030b130501060b0c03490f0c0306152d141c0c0e0d080d0e030d09032006011401050d020307020f 56
    0xf000001c28007594415070500c025105030403d0320409034500c3c2c0c0900d64000e114031460003c002148540c0c003074181d5050340c005050f2120000968952040f6801801540070607400001d0071001e0380004a040c021840361010411b40c410340002410503140c10124149421241e41d001c147d40c400114104800425045590410803900c0c0d40c484410034010054180a40e6a8031074498104050b2003201150305a0400e1003080305040c0104040e000052000f000740045d40600120541d40d0322000300983c0c86004195810243d441800840701c145045d40c502c901d4608850070108106284041991848100200a501d82c2c01c595044c83c00003801031070041c3e07025032280d0300900418410000907910381c4c0346854002c0c0d41c041182c50340c412601c90075400a2031440140c020700c0c4000714140e03581c1c04443d485045500c0c000d4070783d41803c0b07501341c900c084054180c1c50031648a400c074100401400580841d0407520403c141402800d0540480303035042280c20894680340144c1c44040c0384034902000307000c589221 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 827787841 1250 827786591 827786611
    0xe03030f1005032107081b0601090630030224040c0504061401080405071a1216090b03090a06050901020307110d0e12070b03011d0112120804030c0804120b 68
    0xc141c0d202500c40300c0c06000b400681301e000001440e00304100f00042110001c80c0048150b0407501c1c03444082076501d0009010340540940b034010007040078994860003206c1429070512442285011030030002a865100c40200c00394418505150f4102001c0d01c10302d110410341e0342c0801d04915050a18804001c01c0d5486240502c2c1351240900070348540320b02034440603801307007015002629107180040c40c0c00e0300c0da8420b4514004010246c1402211132004108809042c500040d0301c1d02e880090001c60101404040d001c509840400c1203182e4030781c0051035000c1a45000e50369840b0050311040141c1d50100c41907981a54004200048282c0004041ea443e10840c4010405201110300103442090f1801a40e885400510a4480202420010031000e442034442e51610795a42d502c44802074070043c9051032141240f000041180c4003025000780d0106c0d00a21741c1806400c040c4402c0d503410f40058400d0303041120702d6a0720008240c3c0e01e0004d0005110342e030828502011581840700160802421100300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 827789091 1250 827787841 827787853
    0x81f0c0305150f0a0e0a091a060901030f0812040819020c09181c0906082818050d210509121b07061d0303070c060e040e03030f100503 59
    0x80719050294207090210686002c40010f0300c076070010b0721651550b80080441c1d42200c007013200c00380319030300b010044600c84c0000316901c0c1d01c040703450035440008441c002e030841030f0100104041500d40015101c92030050f110103150170b81c40b12608150740c03000c550550711200009501c5580d40d4801ca11a00c42074050300c00ba0030302c80162400a6010031015106000d41421803403032014170003090007401c6d0818404c040c0c01080c070400c01000703407501c14184070700c202040b17252001a0558a01c801da41c00c3c0300e0401204003608401c10b814940041c00c029090500c203100000d42c503000228200210124551241c840b400500d4100080100b140008142c00e12240e081c40148204510f000541c1c8907450f841c4813819898800c10303c0501c05020302e1001c5c2410600c25513800144064003c01d81d01041c0340205031550f49a909441410360300e10030a180101010b04088080007218400c4403425942003000308040b54005140003610719580050307462140000300d82d802d1240d00806101140010301c2d017900030f015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 827790341 1250 827789091 827789101
    0x8010608180604060e010f0f0615080705070303020d090f0311010c18030f1a010b0304020a0605090d062408011a010306050112091703070507110a051c0c081f0c0305 72
    0x186a14010380001c1c480b17511003600c192a04000e42144200401141040201c00718003550300b80607040d030f032003030000401600707880d640941c1c840c40d0700c1031081c00b0740d480e402c0c0f401d4403595086009602655100c82070640d20040c8030002450b1404802030b05019666083c50300851074905421501d0041c2d098041c041105220f03003606002d0503510007220303005960f0461589103803c05070600080384c44010324601c48400040742c808014005140114000e80d182040180c4030041503a040c81440392103644184030751002000a81e44ea00080c20300402d0942c0003003940a8000008101d036035940100b0300381e9440700e00500070426070181d1034181240c2440e080c0245d919043c0040c1500d203040b4480c401c0b00ba100c00781942171201a40c6640c2c2d040744000c4c0700d640d4901d01204005c1caa0703009100101ca4513015070120b860359103031480c00d8105a5000901c0c41c0c88900c5c04840c4001860040b030411201e070144160700154071982071014040d0200c000c0510960b84101c506c001d07088030041c0074901c081c1894507007842 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 827791591 1250 827790341 827790343
    0x1060e010e090c0f070812060126060d05010e03090316030804030b090a0503070809010206100b0a050c0f010504031707020d02030412151b03060503070513050c04150801060818 77
    0x407040003540c1c01c000359156003012410b6841680d01c00c00246200203180c004100d180f00c02031900742c0381c5829050a41d00e03094011540c000028607604408102404018502021071100c9070b00240f00800c0c14520f110301d540d806003541c9050803035234140c4e0408651080b49050511503103200d24103441ca000400c0f030860359092814000c500014200c0d815a00c00104082c1c0c0c20002100c9503504041103944401ea00d207406160742c1c0c040c2000038014020500400d520320800d028100544030304d84c3d00313941031801c2800200c455402c007170700a42031841100c4041080460a10809003d1030181d034613080301c00e0704400f00080480e40035004e0011035110008490f030060780807040e1801e484c010540d4a00800c07160801e051070b41d6540c162450380c1494880310f40c54400402c0b1424645a80545007440708980d00c0f4205034031807000d4443c45030000f180f60381c640c034090015070044d58048000c64165090540318000c4170711441184400b4000329510304014040c041d0000d64a1341c0c41842103c0115000e00d28000d01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 827792841 1250 827791591 827791607
    0xa0b090c030a0b012307210207050f0301061706010602061e040b040f0213050a0c0e030601090b06040e01120201030f0e1c021c0c021302070206071e0804030602070203010501060e01 79
    0x1c0d1a001d03503160304501c0301d40c1c810b800c0c2d0031a500d07a0402c14119140a01c1342c802c16031b4046041101c0c3ea840c0d90f1580d074104018013100381d00a80c0703250050b000c1d042c50042407100300344024070500e601d55030f940b80114060802040d1811203a8404004001750341c14810060702c0d100317003e4a00303086822480c00c550361760701d00c0e42610380c0d0103035000d0810706058450340307802280108600c8000307500c2080460300e09000e0840e540218480c58a13260705014100c0c0c03000c1c00fa6100340d003514403d0b800d50002d10062000c1007590704414066031010b05030610b8039030b98200080300b8407420b8000e12400c0401d8064441550b905024041401c821140c1c2044106c82039560340c1d40d06c0713500031002c95501e00307a2002481440e000340143d6410a007501404010b84001e07000080003024000400c07403041e480314501034282c050b1842034602440c1d020700081c0c0b4288031602c42c5554891340507041040001c050351464002014840034100841c0309100150b00c4580500c1007500b50b4030142c00480070440c414070051380c0f41c0e90000341 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 827794091 1250 827792841 827792851
    0xa060302090415110309030304020a051f05031003240606050306130f140108341e09090825050309040c0c02120f12090a090f180b0a0b090c03 62
    0x192060b081e0f030543c5010003030f10340c00400107a441c201008001c05550040300540c0b103117108442000703500c1e0f2254200254080c2d510b021082d00071140a418001074016002190000c00d0000001c1c0c01c5550703555161ba10241d4900e02002a02c0748a6108544160502412014020b581489400c40c502280410400540039008031b08080e1184000010b807100b50703020038101c003503c0440c000c1541e1905180c6d9624407001c880c407040c50400102480340001c000707440e055030102c001048424a460281c036903840200701e1070081d51603842d004000588000314400e03540d4851043c505076032900034410740700359403448100000f40100c04c0d4100c00743c00598080111220101c003124001541000040c045401441c4210025001607000d44031125140f000a000780300c08142d0700440c0d00c0b8540101e0030080c01e004040a03140c210a4102040c0001401508000d03034042010038000303160407100405800d41456032134180d6903008040140319100e40d0318003801002c0e02d4192180003031070800901d200c0d030710310000700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 827795341 1250 827794091 827794103
    0x82a0f0103020304060b151b190b1801060303031506170a021c050408090f031501030321020a0804060b0103060308043302010b01170c0904050c1b10050a0603020904 72
    0x10006040221030351000720300c030300c0140c805203e00411602091301ea83c09914403101d24841c2408c1c0c0004100000762810b6410300b081080411046c0e070360f65003544940c1c042d00d000c0c0f40e20080d040410400409202c1c1d500218001c0c3c0d40482e10900b0741000c140c968441b5003001c000c200c500d465001100b403144c20801c0e00140348810040c0c1e14800d10403490340b921026040002d400c0e04000900042c0000794000d499140c104540d48201c3c5100078040640c0c40c685014894052050100100b020a001350703502c24002031401e07281c00030004001d01c50f6040764006544d66020448600600060103240c0c4030702c0463709001e0038108000360031500c4140c86030099200d85000081300c65810161880305002c000402590502c0740342c00e14000d100064040e08841c6103040c001003c01d801107000c2e520380d199240c0941103a842c0c49141c84889400d000c0030300001041d040c5000800c010750b0314044010488007180700d124038090620085c050740450103441000d044000b2450804505101681e10f440c089500158451 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 827796591 1250 827795341 827795347
    0xf0909061810060b030f0124080c090405240301061a0705240103060f020a0804120201060e09070f142808060705220602030a110a0c082a0f010302 64
    0x70794035103031400908081190b40c1c01d120340081d0b80d60000000d035001d100c0c04007142503107a899150440759109010311001c0d000c5860060288400d02030282560081004161036181c440c0d100f0114059a4090380c128291200b80001b400b9480211841c406d0031a404030300900c1014a000f40d9002803107a072007180c00e41e11a00150030000c20204101c02d40da160000401d0031054102026400e84100c800d203c151071007800c0006240c0740d200c49108580059916440d41030068440741c960051341183d64000c00c0c255940d0340404219003042e80b0016225145803c000e00782d150a140896008694075480200b60340708102e40c401e0a50340c0c40070504008180005030616044840c0c00d1009029407a501c091064040d02c020711103d43e50100003010703945080110120303052050503400010f540b2502c52103005070001d000303055a10780300701c683c80502400030044822503040e580310200e04103e039900c0b8607036680c80000d154a1442c400ea80c0c0070b21038101c165031110150082000300f0295032503035408a0400d5800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 827797841 1250 827796591 827796631
    0x7020415050108091b0f0f121615020730060b1009080a08030910020d052205070512010e0102041e150f08040c08060405010c1b110f0d1208060f090906 66
    0x4480c0311f20342c0000040440040d0f5a03045411031b105c02340e901d031800310a0481038011401c00064030010341d9054060340140301c22803405000d0f01071940c4054610301480d00440581024508a203031400f030060007810002151107409080000030342c501d0303a014080c4003054504000d80c84000c50015540303178209200e25601e503a030000c110300303186c000e00e4a10702e0070b48085100c41c2407413078036401284201e01902483c00d04400c081501e00306400701100080c0b481d0300000d400d0240d410f1800d41c1143c034403001c0001048003101c1c2c10889080e44c10503001214215080401d040c0140300c400e042c50010311200a07200c030008120b10005000e00080e18120042c4403a08000c6410003c41001d140020103642c020b0310258100752400701c1c0a4165064403000103241e6020716518540c411885140d04c03030380440b03c0c2c403940070780006100000507211401988038480180060104e0b140c000401c4060103140d5a040701c0349468020000d1200b0310701c0c001da014090806c2084000703240003c0e4a50001d4481b083c6415030204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 827799091 1250 827797841 827797849
    0x507260a0b0a08010603020102060105041103070e060d060909210906110c1c0b010e060d06090f02210f0102040b030f250504030b0a1109010f0507020415050108091b0f 73
    0x10740e1650720341107100b001c00091080b03410350041c42940d100b6801d450361a60382d013040106607000011040d203008000c10115a01502500000308181400b900700c81c18986100402c00403624035a21510a880d195650041000304055400d00c40c0645590b4007161503450010040060250780210401d120800e034144c550010100100000d512000705000801400c101244d82c041c040c10008640c1c1c030290700004554030101c40000d0f486420060324a000704007a03915420040c1c00610801c1d91001ca2b009007160160322040340e185100c1800c11411001810f00200302882c00744540c1c0d150000da48180400e00005030b074036080300c1d0407034200d0b414840152290740346103140580201000680c500c0114040b41c200360840d0242045a02840520700c0070b07070300c00000c4025580007912440390030101b04044c0c5101c0d8000e03880c010121550345019810300240d0741c04201151a1203040b000711001000e0208103039039105000950000024001d40711020045000c000804407155000344508001e044920240e11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 827800341 1250 827799091 827799101
    0xa060506030114010f0936020301080d02150403021902030313080607202e020d0603120512010315091a040507173705010c030507260a 59
    0x9004000a80d00d5a4611096a0f40030f924443d0b01d01141410b108a9a038601502281c81214504c281c141b96003101880c0b01d032100da404010104540600d0400d848181d81c05101a5010b481c00c1d6004001c0c02170418000392400002419110b090007503041080700081e130104113000c122031141da440084080c1c1e0f200203804d50240d480700e01c0d0300e81c1c1c0350800001c14400c00a465401500b0a4454444040b4000c3d104014000941c5450140e0b82c070201c00d0791030700d5010b01070815144240c100000d9261100c0780d0940140d03400004000b040e25180c2e9000d1045c01101c1c041c1203400311440c00d00c245090100141030064000512002d00f1250906950f082c00ca00c05401c2a04820f50051090014004854200040040658080e0791611800c0d002050700440007042d80503000084008018481c92060710700b000840c2c4172030f4084642107002c0d00380e90060000d24040c40b450300c81e0780085401c0c03900c0f00009044400041c0084100030b24207016a404002c03a03021203614080d003100001e07555440300c82c03e1000e84 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 827801591 1250 827800341 827800349
    0x50415510806060d0c1e0512010525051606060323071508150a0f0b130f060519020a120c050d0e01120207080714060118050c2a010e0d0207050d0b0408030a06 69
    0x440c554441442240c0640c80305224144bd00d0310480388001c2c1220b2103400d05c17020075003040420020000110b0301d142e14486158010b01c600d0001c169141c49a80750120280c03160745540c7d040f450300b0428040144140110701c06804858018117402c03101ea48002d0040c14003230181c1000c14642d928031546a01c480d8a100090007403880c001c40465907460f4020130580c84180d030b52214043c2c018010504400044c0900d080310110b5a94605107070740c1f4580d0f0b00c19040c0c200320b000258450055601b0004542e00b181c140c00940c10b0b20f030901005503505050b42000700d40324812041000c07400109000743c2c0c0003450048980e840200c01600c1c0d000030701e44240c00784200036000e40002c1c401c07140380d10701c0c00c0700040c0315060380c051001005004035580e0b5a04141c90082d95826002c2401380148035404007444004c000c060801c1c0c5802254000031500342d421150b80c0004000790381c00c0b20141c0354249404000000c0100710956800380e40c0074854071060030140e00a4002404000d001010030000300d095040314002d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 827802841 1250 827801591 827801599
    0x3180d1a0a0f061206060807060207030b0a0b0a03150c0e1c0804080604060b0307060203090a0306050a0209181501090515030702100f050415510806060d0c1e05 70
    0x4562984d00030f50314880d81d51030855016040040205090344c1c04203400f02103a100d034004002e80c07070030750b0b03590140120020082021107954044d8008c0c155180d038071701c030b0055000b04070703030880c40c00e0400002044c0c0c1e02003d45c000511030752500400450710b5020b00d41d40240111200302021148500c6c040500e072080c2e034005003003486140240b1081c002180d001101d0040101d049803041030f03403018140e849000e89000e2580c00690001c0800210b0041d4111550052031210300520b09951040042e450700e040f0011f101b4002c943c1010400341c402400b94000c0840401d0800400ca24501800180300c4141311040403000c140210115500c0c40c02045507a68004402106100c0121801c039080028002210181e520103039113101e6294159080c0308802e0b0f186800d40407000c08115003000203d00c0c010f0000400022141c0f41c09600e0405190f0080b9245c07003540744002481c01d031404992500c0d00d234020388030300d10605039940c1328000507881c1c6003031a007194048010340401c2c8000c0001700c00140e441e80e202d2600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 827804091 1250 827802841 827802851
    0x10b011e0e0d050d0923061c090f230c040c1b03020307060c030203090c090403092705091204060c082b0c03021303030c061d03180d1a0a0f 61
    0x7040343c08125400340c801565070300101c46950b00740b40c40f040d200454a900d070350380c107185401c0310381d04000700103140d101050a00460824001e040d03a608aa03041e58040e620034500011020412443c0164541d2080402d00c101100d92541d0001a495441e4a1191440b4907075901003030420b1405800705000c80e4166444641540600d03080180d101d60000008503291481d00110202c003500030b2007501d0184030400010f00a451190061086111020b0010f4062041240740020b100c40302c01c0b03460b00d106010601500e008006900c0315019518050315044540e007010a0540c8000d0b25281660111030061811807003506150900701403910501c141c8802c0c102c100e5100364494178807a048440040c206000c00c1120081d1007a0450403030107a06820039010040c60307010004640320b003507004215070181034002080701c0c5591180f030300125400e2003200c4581010031014445010304004016a42d816034a20b48420116075030404902d80c0b014040000382e02000c04580107540c96440506d20080701c0c541040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 827805341 1250 827804091 827804093
    0x370305030f070c080d05040303030e150108010204170102030606090607061e09050607090e28090b0105030d08010509281505280504050c1204120908010b011e0e0d 71
    0x8010703807010b041650038110514001515400c00500d900c5202055540c02e8142410b41e9000c402508209110065038070500c03101c003c584010806160090816600042e503a516000100704911084000c0c1c180c1c40e441801006110303154030040369000d610440383c1d603503034507050300d84580207014030500ca01c10055645512207044043d5400205468014011104a80d0384c0031001ca0b10340900340141c2440301a92000300d8004003a2505040c880e0041616a09003201d10202203400c072504100c095035a03030b200c00e004000d542414041010b010300b8a10b0302000ca90b0400b0301058540c4000342503c141110b07420380115825182007910710a44054010500185811441c00d5622800b83e000303d62094a142034200d5000c145880c82d2440040484100f0088034641010040100001860f01c0c841030010812140300000350102079100c2da00c00d68408200b110412802010040759800104d600d86c50408810170076070f0002d481c401c101318411008080c0c2c0116100446000090410072a00815204d190038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 827806591 1250 827805341 827805367
    0x1706060d06111908010302120105060d060c02210a080603030f1c09230706020f06130201090e07050a2a0f020f0307060206010503011107030f121b0f020c37030503 71
    0x1741224000c40f0080003140b450f6100c01e00701c07181901d000d0b03070100880c0003000003e40c0e40e400c140c0b040e50f4a8010b4408000c14008040784049406e600c51441e0a4000744408001c2d40080203941c0080c0c0070f50085041042260711002603100320491001424001d1103001148030b080c0d0040d01600ea40b0480c0c0340a03145481070460208041900021350038054503001050203480020f00f0800d08240320018803280d00c80c100741e6001c47e504502c0c164100141c24901040c05140c2200301c0d80556021380c1c1e8a65603151181004150302c000e003a10045014191130580b6458402011040080b60031900301c3d60212030601c001030200030a29007042e0140202d100000d8851b0b0003042540c101c0381c041d0300074000300400010141c4948a0502d004010070320702095a080b451160b0408100b141e100302c40000c01c200160003070192844000c41250008040c0360b140d10305594140100c103114403089d03500721010500422110454090070810302e00c2e0b08580076524222940800e8003000031034000c419240d940c0003604d010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 827807841 1250 827806591 827806607
    0x603060c03142e030515040606120f0b1810240e0112030e090f0702152202010215010e04021f0507080d0209030609071706060d061119 59
    0x1401203441e0208441c240d00609000600c111200203110f079083c0c01c04240241120350075214041e411881003004070002d1410001094910800e914202051070300340ba02009442e07244e00f022031245a0076088000142c804060300b00c045621074105580380d0313150040203600c0910040c00c100d0364410700c8410002000151b216910708500b9603800e411142324841801040071140c804c603504001502d0040101e42440c12038526694401e00e409076040a0b88000070340401d40640c2c00240405506041c8074002c1d0301040210b0203006461448c0445140240704c808050022681c400312604030301070781c0c0085a02c01d0150b030f44031006c07083c8207001a58482c0d0a840b07032410103d0f02203000302030068186030025050006a4212842699010324154a550702c503415600400d10841d06290240007142c807540e01071101d40d00c01c00122000300b00c03003481c2072a4102c2d0380c0414074103421107412500c10301619486602024030b0843c0c11078004645001d461034044441d110b0540d1702c6003842260030200d08070a42c08030003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 827809091 1250 827807841 827807861
    0x2030712121401094127010b0901120f110d0f140105060d150207080702040c08090118170a020304030803010e0420100c020616030e040501140307120510060306 70
    0x1080c2d034043c0c84031203003490b40d01890070102c592140c02844040310105c0003c550380302e15103000388104100b4020390200c01c1d8601640c0c0344040d944441c40b085140c10841c0545004191004840d946181a43c481d0002c3d0030484034050035001340c000601c4403030380328628203071507550b8001071034444031000b418055000004224100029400c16000c95101c1c40c3c03540e01d095a058200d6842c240c0c440343c1d90300040095000c04c1c0c00311000d500601c003820241c0e03114800d08030812200e0b11001710070f160404000b400c482d4000d4155880c218040290000f00d00d22021050803151003241d816034900c1c240300142d185020310390008041c035600000110380007191250b07141c081e0380710310749889280a50401c00030402d00a00951500614401031050110780308402c4816028005801320b03240005c046842c2101c1003241b003059012440218100d111410988078090050591b00d4a0000b005d2a010010307444406612a10000200100c00501804010f000b03034807901d100e40c142000f901e0340e86d00e4074401801710201 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 827810341 1250 827809091 827809121
    0xf0608032808040b0a052a0d06061112092e0e03060f070c0606050616020f0301110403080a1116080d020f0304050607030e0312040806070203071212140109 68
    0x1e6500d1500d40110300050160303074000d0104520b03640ea4030140300100070080c0040d856200c0d010703040e21406025820602c00c0c100c585c280e40c0e9540305c48031245050310200e038000001c01940d1803440c1c5081c0c40100b220029038080c07000b1241d41c3c1c20080001102c42c60141c021403210048180801b68207010800b078900c105200f92103010b0482a050201600c6220071100241c9940010340002c0203544154220f960841c401c0c200064156100e5021902c80e402007a1052030520700d07040941d080d40342c21001201c0d509011402407212203581c80c1c00d5004c502807440004c04190707004c40c0d242401d80c040d48054890019000c111100e6940c88628170074841103510500703000b40210780e1603000c2184013080c1d89251210302c0c001589014500818400319600c030308820f60800c111000861002d5800344102c006284118490076166400c0c6004942000342c043c02070307020740d4810412040010413414100e09031010b582840e8900e40552040000a8050010000d117161605000480d00403000d600a13102084038803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 827811591 1250 827810341 827810407
    0xf0411090a0f080d050a021005040201020f061612110a18030f0b04060e030a0c0b06121b0f0d03080f041401020a0c0b1302010c14150a060612060e06040f060803 70
    0x3e401510241b00f625038800040e00462106500c0441d16000241c001d84107104607845401800f451070309002064820300c00707070b001d0354400c8020b1a910118100c0b4400d190382041084965a0766100c0441c468840c0c00300a0000c2c06e01c8244c8030402d9880300c0401941c0000003031150f102e0900d441d05031500b0848044071345074613140c10200d0390440001910b84c002255191014103500c65111640b07085401060b0981c85030400004464249040c08103d0008001209a02001d9000400c06c45005001080540100c2d00d601000d030120b03600c803290607040000041135100d01e44031800c1000885800c543c44030f90070340c00003401000c203da00468202d541d500882c074084580d00c4d400d030568603040c40e1700d0010340081d01718074151006c580c07520040044030000d04120740a00340040900e542d1000100c8070710364070568911b82082920782204c0c03012079841b103504080100c5820300c00403004403800940302e00d004c0c1d0307582c19181d081c146083c0d1100780174110780d400b101d0b01c507801c0043c401c0c1c0c290b610340f940d4804c07800381d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 827812841 1250 827811591 827811613
    0x30301051009080c3601081005190902040b0d150b03070609030303020c0c0d030c050f03040f061b0818030106050f0105030c131a070b13020f0411090a0f08 68
    0x7101c0d100180c4549a01070200b45428108106105d1482c1c001c3e40c92019105105400d641603004100ba41c44255088400305903151020325802c0402c0103c03841d0310f950401080100505440207903155900c1c00c070200042c004100d0020400401000c40140d400c42c0710b07030300c54030700344413034801c1030b11480710000302c2813001d1405281410703207800d0b803441480042180401c0502c002802a006420b100e075806003110000340403031000919641c54120300344d000c5088a8104014494240401d251000c550b000071854585042214440c24225120b00ca04006e242c0070b800c241180044c0520072101c0c1c200c0700c001e480d45500700c0800c1c1c0701c141e903c0001c1e21031340c03800f40005010b0410000b41d80d10018140c5030141540d03142c84e612045c503808003502106000d00d114000c209403c10540b006a0041040240c0c2c1d00c0715003915224080c220f016003180a0b441095141c000181d88000d0003007000b0406607004242480700c5a00c0346d00d98081c822425612a0040001244c1d00004401c05803c80d239608084410a80039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 827814091 1250 827812841 827812847
    0x40b010306150518090a020a08090601230d0b07030e010612020a051909062c060330071a0f0705070f0c0305010903030c0e03070b0d050907170303010510 67
    0x480e02c01d00c400c4110180d00034100301d02030000b400a00b00c90a290041c4ea000b120005040038404036004580e1590100f00c0a211035400018947d0060769507000b040554181604403034049100c81e040541d41541e00312030750850321140c514406240e44403803402c0e841e08028801030007604030f41c0062002c035840e00c0c0001441400420084030340316005840c08500c242454144802c004108800300760300c4032500c50005d20f491141c42102c0c0100119400315081c207d4402e2482c0030319448054040c90070002400f48681540c3c08500c900c20b20001d10501e042c400f17404140c2c0c090a03a000318504000390000f0442205015006240b00000360321060381e4a03131940d4004201c072810740285d41c1d42e000200305210070740c001034031304007a100480e00407564000d0540d62aa162070954a6a010460020740c480c1e6900103016009029100c01c80b200701d0140904a0030061541c0c01c501401072102900c54865021500d009814817a04005c0d1100d01c1076805c030f810f114400507550b5802031150a001d0034549001c0248288 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 827815341 1250 827814091 827814101
    0x60618030809040b19080a0215040b030604050414070e0f0906310f080903010b0109080a020f0d0b0408040303110102040302010f0305090705060319050c030c09010f051215040b0103 79
    0x10307014080710704204001c07007403100500c680e100454101c1c1071000605200c109095140d030041c40c035034008012a40d1644103015071f800600542c840b03091424442404010345490a59901c507805a0300060f05542c2c0b0f0030511540c011400f0445580d0003104c0c000305408800f0720045100380781d0003071444003d40b40c4c2c09405650b07000031034280c0480c80d2600184a8007650361842e1712480c0c40d00396218181c100d040d440c1d01c10100550790045855000c0004e81c2400c0342800e0048280d401000d00b0000301d0708c1c0c40c200e03840b41c460b00c0d4010020301c201d115041911069481c64130340311840c1c0d0851005055454140340c05461070707209000c15800b0035484101d84526090500031281601da041e5030341d400349a0400710135030240502a1944503036001c1d09201059940b111000340d07104d15502900082240d40d10803c50089400c068503000d120301042003089501c0200c803040303c004510a180680e00c440d43c652080341c0c41e002d90115002009080d001740b00c1d120407031025444000e1800ca4003045800d0340c0d00d0054044070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 827816591 1250 827815341 827815343
    0x40f022b02150306330d05060f0a030308060f040906020406050309190f060e0f0f1b1905190806040b040b0c19030209040b063f0105060a03020f0c0106061803 69
    0x100c20410507170300090300c1c2001c549000300204601d0061501d04c03d182420b800c20100300c0078040d85c502c1040b10340d1501c144003075000a000d032448600141180c80c0100407040081402c1c1c040d1030110038041c11511241c0c00508841e82003042103484584814001b445a4010389250300d8038442c0c1e400c6c0365080c200002c1030500c400d0f8425065809655181c0e90030000d00b00c08022600c00b4000c5c004c00c1102e0700c5081c00819500c1502d84040d080d4111107c2c01c261a404a0154070b6000b070303845d0b843e41f4561541d0440c900c025a84100e4204102c4005041c0071405114181c0180503903005010600c810014100b6000e40140d128100360a1155111481c103c460b0064100b20000c0398110001071000390700070341c01086002d80190000c1205040100031811590006e2841c1c2c00d6503a0054030114800c1c980f100b4160b40c01c540b040c003003031400441c44002d407426106002d500e116031000a2403410060013070313045541420250304010b40f80c07018628100d0003056280f04080c007052400c061100c0294000100005030303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 827817841 1250 827816591 827816599
    0x35010308031e010e1306060e2a0901020309060d0b2706060313140106080a0503070b0106020a05030706240308070606090e07060305090f16060909090803040f022b02150306 75
    0x903a45001519040310502c4000742d0340d0650347c100100ba0403500071907091007a80140d6080b1040510110622041401c081e180c4d46880301c10701000445a0340407040b9001c40408540e042e48071540340443c100282500030045030b0200140801d80742c0e0307d07403250340a000000c24800390784260361544103001161104a403e101c04403420008a400a4000c18549151801110001480b56203a000381482e119541205442c0b0368808606c2c2070410040889040c050f003451b1010380340c018650f960b115a41d0003409001801d081d1601069820948a282c4244001000022804100d543c81c2018441940521001e07500d090402d040821009500e0085e0182c3d000200001d11360607103800821802000b02600b0030722240111409180604800c06c003040c40c50b40c3c03a0048041003442c02c6405440080b8650104152500f4802ea90300464503c00540b40d0190304941f101c413200c03001d4030000d8120710304015030102c02e4069680b81500d03180e145026a90b000c1c804d0715280c86803000c0000715010340c0000c80e802940 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 827819091 1250 827817841 827817869
    0x6091e0f060819201e0a270308040303140c0304090207060b01030c051e0906030f06010f0f200a050f0102030907060512010b0901050f0309240735010308031e01 70
    0x71344035142c4014004100d1214a010b03c0a5190480c0542d540c4202106070000343c0c10700c1001c501184000070f00510082e01c104103020b02c0c0c599903c140d4a0b01641c030016060000f0240030000340d1b0340e540b04a581180c490011b407540c96459100038002901f1011007950401c0c641004000594081d01c1100d000e200c1d15185d150800261506044501c0081580d119149406000e00282c60700d51102440c005c0d42c10700355015540c0b812100041c403030405d03240f80b130f410040121240c0082c6600041d80388400004c010364488050a071140c514600f8003201d400070401d119900c0e0480c14110194040c5000780040001d9447c515990b4801b00c6190123242484e04000303d100c0d004201c1700300c21500078415071406040050901005d2a244060341e002200c84081079006600d01c584450540403818020341c010703c1a250701400c184000900c8150880480310380301e6040b10383c100c106803221640303504224003c1101e503050343e1245030200303094006540c0020405407610f4112001000a4105410f888046d014510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 827820341 1250 827819091 827819141
    0xf080a0b0f0f06161a090703080d02130512061f03110f0f0603010306050402040f0c0c0303050c04052808150c0f090a1511010606091e0f060819 63
    0x30400c012080420752041e02000000d02410b21a80d042404038003a00303040c9041100c0180340c805e43c50008044501da0f070401001070000030f02c200c0640300c0803020300380b00585980c500780849503610225004940c1c0404492000550414005030141c810240a040341da400c01021208182180c00e81c0002403c5440c010f000084604112415070741030781001303058580f4580d2034004151154401c1e0410343e070142d1a94108820740c1010b0040110004045c20b00304000c50a14000138449900d20600400305078460300440c403c58403001c02d40380503007402001c00c101407007260882d140011030740107a00d400b90074490000685007030110326402000b640281441040d035441c2440e1203e42d21038403007030a0780c060502160b0307015110550b48802034413890100c1d00d140809907402034805c4004203401d40281c0c3c10300c0020301c0441c0c2d004000500b101c03005900ca1401002d620005110070700141c11070764072621180400100c660340020194041c0c42005840080740070103110300b20a5844000204089546c070b251494 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 827821591 1250 827820341 827820349
    0x180603030f0c0c0d140606030601180c030b1504060905060316050a050403050d08040302011505030d031a03010f0c09170706052d13090b031b010912030f080a0b0f 71
    0x710100445000ba60b0709a142c0d2000910f41104400c0300303444902c0428505170444004000e111f400c1403041f001016158900380b1081030a015500007828141d031558442c0d60380034003d400060b00000010301501241d501c204d01c10b1140d070420301c11607000807043d4000090f54104402201d0060140d100c0303070819411340b00000d441d954851a02c0500300101000000045607080c4002004110740e56240222820103044c002d00b0759000203000007000e600c0f40020803159800017003100c001010b9040c0402c5109990a801003096599000300390035500f044000041c541c4958010750740001980c54840c0d1040d12070240741c20b60781c1039050703003c11a40304040500c0118040c0000e05801c4031441c03818161040c0b0304c4040f03081c40d40001a03100030030401050b401c05030b826295040028008a0b00d04101d040c0c1241c0c0029030f80d1781040c442450410b1140c400d4a000d034480c190700b8000d0320b16481b1030514034409185c0200100786c0070a111000803515408a480c45074a402004501c8100030050141c1c0c0f29060108 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 827822841 1250 827821591 827821597
    0x501091b0e13050916030f2307050103051f0902030612060c031b070812090601060e060d0b010c02060a090e15211f05040501060501090602070e15060f0702180603030f 73
    0x40e030701070310602e50a83d107210708143c9240051442501800c45144007454a481c0392254100d2403a082880d4101a11000c20f00044149c1151300034a40403406840341e03110107803411804801c0c0d494032031040380081004903880c0c005502412040d240943c020007002d400c191903500586004110200420211b10642406031640b800b41096800705880c2484641c0c03040d2259000700104560f1000d4141007001218050164600403ca07030b0410001400d40440064074602c10380154100c101d6544d22202050303482088042607441d405003807030f951042c0310381c0064101c10961081d03410644010b000034030f2200d58001c0c0620700700f178068209040c001a40d100400641c4182503c111030303208280c1c0500c9101c00c800300b008191030041d40f000609040901b41582520f006401c0b8031306110241c2000c000f000c0d40019030000322442c1c1e4501d40d8042d02e6010b990044d5020050301a40c1c041000b140c00c0080301090700003012402c1c0708681240d044c2621010b10020868115122503040c1c01c14007600c0c111825030402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 827824091 1250 827822841 827822851
    0xe01050706020f16030e04241a0f040308070b0601050f07020402030714130f0b211803031005120109020603150604030f0803070908060c0304060e0a05010501091b0e1305 74
    0x3078181403504d241030100e880d981044090740080d50152016000b07003018424000703041e0a000c0b4514907440c00880c080780500e207030701c61102e80e0400411300c00344d03211501c0240c0b20b003101d81e8445141e0b901e59034240b500700e0382c1000e90281d9070b0b50442c0d00800c20640c080e008640800c40c0170701000381015000c7e000c1100030f410040c0344d142400f4003038821041c440750751002000b8900c000080206210309207130000201c0300e01d035000740a0b00c1130b04105510741040c601a540103150601994000b06603149000e0740301449106151142030702c400b2043c00a11030145900d1000c1c0c03401a95865200100b8040e01400d07102e034400041d40000081000c110b0000c8800389800c071030180608054070300741d5241d5412404c0b00d0300b404207450700007020007031080c4194860003600003007059400405850410100c0c455145c400a8401001960340d1003035040ca02000384142e898a54120f4001c215969440c0900400303070100d0504011481504201e868038076026442c4403800b400054020040d96500400712401843d0141c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 827825341 1250 827824091 827824117
    0x709050403050d050a0e0c03030f0d0e0a0507030b0a0b0103200a0306050310090605160e0105090a03080307120b01030c05030a0504170d020a0206071e210612050d0e0105070602 77
    0x21003c1c0c03142490051902980003c600040d541d01c40804142c206031259a0741e0740b113500708110f03d80c01d603194002a80e201e0740400c1030000d2081c0c070208105140069a00004045000701e4030000103100c803507a400c03441401c44d44000d00034605800011400c03110322081c1c2100310108550582c41c1303001ca00000e8072051409090001750b5603154030001c1d00e002e188000c100f4040e520b401840f02082418050300340c0010000821100105c64004003800034111403103224100903000c06c402d003d0741e542c043c0c10001950002105540ca041048005100d004040c3d0f141c4c0e0b1050a213040e0f0b4425501c40d01c2100aa1b001560b1240c3c210748600220034058040a44151140072029981c1c001001c5c1a00040101c0b940f00303180146d032080000000380c2003601c0200207409100154200c4100640620b0143c122194149404451001c2d00d1180c0201c401c400c1000c008820310700700d80811400b0960b01205c4501c0d01980450381c1e045041382c805c441c000360010000f03000035418000c0c000040c03010b401a04210361040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 827826591 1250 827825341 827825347
    0x60608070c0b152d2b0503090a080c010e061813020409020f0a0e0d110105030907090e033c070302010b0316050405090604050c100e031507120509070905040305 70
    0x1540313083e5070059658a60582d1480122070b0210001d080c0c0b421101a0784104199000040507032070039914485150a034079000740c0342c0081000501c110344610600400c5002560380300e54511395100700b02006207001c11a503170858a80c0b841c0030020765982e5406a0f00200701802201e0601c0a0004584580d4595927024400400c9a20080c0094071000c030a00d410142c0b070b07140d102002006542e00038550f41c050740c5501940d50104800c00259124801d00b805c04540e41d40324444400d1038030500c0d031700001e6040d16201001c10144000f10040240250f5020710403141d070a2104c0101020090604025614800c0352100e078401a40b44050300e030369406030000140010459000c00d040c02200d036603080d4107101000c000d0015240c05c1c030602d03411411500c010702c00303490190b81c4c1e02c0c1d88454100034184681e607241580001d5501c2402d10013108200542542c20030403840d502c10040c6041a646003000c5041c90f4881c000303000c0548159131180480300000d080c01c07442c00b00103000805c1c0183c0f00f501085010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 827827841 1250 827826591 827826631
    0xf0501050603010e03300717010b09010c11120d0f030f05131205130b0915071703060604052701080a0c030b0a0f0203090c01020c06070305180d200301060608070c0b 72
    0x840d040d1845540341d911000e01e81e082c52246c0fa000034405800c66040340c801400074bc03003d80d9002202d9080c1543c0400b00c14140361041740060f07640c40726190b4003c01e910603001c22030b03003039641b0100c2100d2100c983e86060001e0b0703505851a030150717074085981030401c812260145010600801003203452032201c0c1000c500e40282d8081c000300501c0345402c0203441400c0005e5544641c1401c0415090003803041c94141c1c246900d9a0b21410132211070758207290300b480c0100203e103542c0c0c0d40b94200c4005040082010100014071007c4a14020300c2190500c04030030000c000080008011a032511f01036400aaa0350038030b03056a681001e0300e80082c1c1100741080d652209035202c01d0007440154060588180213104008a043c00246800500b8051600604041c012440026000030503603440c80800c40c0c0c400030700c01007440864200781d69584058102900d509034051506445040b042406d1410f034003d1000944801c000e07a00d0b60019248c0100140d40c004d00080460038100049422029490005502e4045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 827829091 1250 827827841 827827927
    0x20d060e031803160b09100e032e0501050109060309030302210402190501022d071e080106140613030b07050a1d030712030207030f0f0501050603010e03 67
    0x101040254040b10207860480091a0400c0074140c94039500c0206400107040c40508202802840900e90003281d1035a99003001d580110324100b850300c40a8211104140140d054040c69014448070044245202103881184002405844d0586206840e401011481c10a04800620540c1402d0701050740c244404101800c030906050030f05030207450381c0c4207035080500402c000d1009007040130f00c10300782c0c80c00c040000da600031481c4809200c42d2003c5100300b41020300d000f403e444210460160500400030045040303102114040c44220321000705008154960816070308941c00d030301414005004c5103c80c05901e150000c001d0160314101d05198442d540d40e0381d1105070781c42c425188000402c1020861031500750b4440a20101c0c0754006071101c21042150000c40d4031400d9a0245e07201e041c11031200741c000c0c14001c108400003158005400c00e0582c410382032081c0c0380d503203160080707885500b00340c0421242e1405002d44100d00e02c015001d14a801007100840c0c0f403d001070700b040203803031028440d40094588 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 827830341 1250 827829091 827829097
    0x209030703060c0e031621060e0f10060815090a0b1602010c090b070b1e0a021c0c0e04050a06030b04050a050c060c100b040612060f15030f020d060e03 66
    0x301c141c10105600b980004054116944c2c0001c090203644104410f0003c2daa011880070101c0e0000501c078484001c0c0d8032601c0d00a1650804050700e03441c14890715500c5440005001c0303040c030300070f04107417074030f4105070390195040da84540f04e851a6a406200a40c840c1c0c8961450b081c0c200e00c8a10459626844a42c1c82c41d80d660001c849616114000000907640940c085c0181164039080f842d15112003410060b105085024034080544124800400103d0f421b03880c4480840b00d0080345440d6506242c490b08103800b9510a8480c20041861030345071203c065035901429480301803907200d20b01c40184807814880106001004c0312101511810000080b034401400349000e14082c0d406401080d845081041c41e040040c28000c0c0500d40070440c6541c03d40d00840c3c0d40c02c4e080da501c0c801040b4109400001000b501181d000b070f882c4010410341c0c0c1005c000c1c2e264030911484085c45070610001681d42c1c00c90b40460083d101c00b41101e20004c1004006181c02d640c40300100e0300c1400000b444a86d04000f0520f150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 827831591 1250 827830341 827830343
    0x20c150408060a090303050a0b09010b09060403050a0f051b100e011e0309110108070c0312090b0c0304030e040e030d020705071a130e1e1b0a020c0109080c01051c0209030703 76
    0x40d52902402e045c964140955a400a80300d502070008848080200c1e103441414403503900200408510f00300c5503640d0504840045801504031142000d15083c25446101c0110044403107205004040002c0340d01102c43c41e40351400101510b40c503104d92034094420415250080341000301c00e2048035103140841d6107000c3d0f02001c954000519414914050010a500c220014140000309003000021640203064064095052500c2c071503050383c0e500440054009000c004008281000800403001c00d628003440c071030380c00b0740c0d03904070b00d50320101c24003045901001c07100500c0d410030030040440700c4060300100040ca210344e00720340001c1e81d10400e41541d01820407220380f13030050000d01a9606208100181301070845040310490500305090306040d00141a030b819501a940e200c009050a400b88100c40c030300401101d64166100d50140000351903000d4241c25034041541031002240e02100051040710008040e15100d1500c020159180f20300c080a60780c400d602c80d02040840d6487d00c0c107110702c500031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 827832841 1250 827831591 827831611
    0x705100f05010e1512064008160b0114030c0a030203060105100e12030a0f020102040e060405040323031008070806041b030611090f0d0506071110060f0e0c030403020c15040806 77
    0x16107804c864204802c0e40e0254001f070490a84110191880701ea01204044540c041c0c2040c1d640c01214030030461600c400200548158100f100001d10450100c1090f014414201c09581d2411f80702d0b41046510200c5003c00b0b501503102200520150509204c010407625080c20114032503200f090002d0b0f030024011130041c0382500003140904006810a06c02e1884824600003942082d040c01601511144c004251601c13aa032134002190030325008070390560b000104030400f145003508262040c416540140cad03200030b500f009030000044401c03000c030758041500d803900e004d85100c0d19a6200c41201d007a0311103204002000248000000841600c180f2202a6188100d90340320302e035070390030840020040780c0c4c00c6010703051b0042c0e61030001300301141e003070b41c0b00c201401d0a10080c2103132841035240c10350351100224450715001c008240d080307a01071008101d5a941e805808183e682e00c001c80810b0005840c0140503911080722808545000c4804100500e0b20f0740c0c1450030a03a23900d442914121051b600c200031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 827834091 1250 827832841 827832871
    0x509071101060b1209070e06130f0c170105010329031e07080c010e03100f24140f0d11060f04030b34030906090203030705100f05010e151206 62
    0x18000c4c003040c40e60b4800112005000e130945002000407481e0030050040d03210700407406480c0b03002c0411394048040c902020108000c4101031041c0941703191054a061088216540c00014a9604c02c3c003903044407403c0b0252551032207400143c0340d44040106e003800c5505002d0084103410321648940c21030b510303c179031030000c3c101640340000b51030800e15000d00d41d074100082202c900e030958030001004035000018620029083c00c1c91030141000380030880310076182c0380b1071858801c1c1d1f5031030810000c403da0f0380c0c4040603141040c14a04011040608400840d0001c28041010010880030301043c0306001003c1c0c101441d0010100c1100380681c425042224060b8004040c00018210802868903103800503196001c8807901e020407041c10074040340043c0415450b501040b04009554103e03c10701580a011640c50310300600e0415100ca60240a40203103031b280c0004d42c45060580e019281c1255916140ca4245c1c0d00c1345c201800c031410064510a42002c00c030000100c0d80350041113402d210f0b1401e0854001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 827835341 1250 827834091 827834107
    0x11030c0d231215100e270903120a2708070b0a061e0501090b0903120a09061205100e09010905070608100f211a010303090614130509071101060b 63
    0x42078520180710754020760580700650005604054480c4401d401207903000403248900301c1c6902080281c1e40d00c1c0e80c2c0c4109010a00c00c007258000054031806275080d45200c03555584041c01400c403100307519003041c01250768500c03c0040721032054102c0007a0098954515020054a071581c07515020354481c0d042e590f0700d1380101f00b1a1007030920402040041c5c414140c0d120301c2e09000801c1e4031058000c205500d407000603d00410fa9040021000116071909030395200c0c901c804010b051001c0fa40325207000b0603505400c04240414034031130700f40300740482c19000c84401e040c82c2c40d20003444001044401959a260b00450210b601007040c08000c054681d03c41c40e4500d8910707443e2809007203541c040700c01c00c2d078500001d024184025044a804110003030002d5201b1144c3e09180c1c810088036903e07908500180000030007890341c440545c00a07240d0307981354844000300320340b20294144519603807a040c081d01c014043c00585880c86605403c8103152424074002d10040c4080d60031541c1c079a00680040000152043c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 827836591 1250 827835341 827835361
    0xf070e0f010e060f062d0d180c2102090423010c0207140105041203020d09050f0f10180803070b07050c1f02040905010803030711030c0d2312 62
    0xd002d40420800002e45052000219641c040d440041901c0b0343c0000c905000d000c414580d690703501020504550700e0f140820450500740d0790041840000759400c09241c1220181104080090f0742d80c05800d12440e02d26061004034006041a40380ba5001700808a8030301590b600300c0818000c0380140650f07100c1544c0410140c0d5000d912400c8110b099050052186032035401142040468401c103682656040201004031064403464200080b140350240c80101495400242c102c0c0c11146500d80103411512807041200c20540f14101a6102692800000031410303c0c21080100d03424504004005c01c1d00c0b0000e180c4031042e40e41104c4120f51008c03c0c0741003405030700d004040d00010181402c52900030251129529003114241070a03071058465076852620300a541250000c10300d071134040100796190340030796449500945800001501602d25800e070324002004070703214003240e0710003070042920000082d0f482d5800b602d0500d01c40c0340d504040c590fa45d0a5500100f5115542c2942903009140c480740302 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 827837841 1250 827836591 827836621
    0x91b183c0907060e1c230606030c060f09121905010f050108150c0d05130b07112503120804021e06180409140c0a1403030d0e0f070e 58
    0x1a0300e0550104100f084059003000c000e4131007020946134011055429000904800e581c410002c018071a902c5411003e60844a00041b150310280300340c3d0020f49a4108040d030311a81e5081c0c0c164001001c20551030680704a50040440510281c072030112201100761041c2004050040040400c03040000c0204100c3c084c8190541031000010400465052445241c0e40d5010b1341c403641c131460040804101a06a88015140b0500f4094000e01461806825405801c4000407040364442c0005010401d45809104100110102c00c0c000f81858041c8401d5444542c19030621340d0480c0440e640c001c0003086001c00d0340d0030404000e850300542030500e803052040711038540c010012001c44d071030516403655640c07008840c2c075183d00054030000d04c4080b10000c0e00a195100009040d18108020050b406e01f000c5140010110704490a0084507074070002500f420034115900341d8540c204101602c04028607501c072a002e06003180c111104410700100c002e2515409410049245581000b0082041c1c40340c854 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 827839091 1250 827837841 827837851
    0x61e02130302060a0512090307030e37030f0516050a030803060d1110021c02010209150c010204080607020105061c05060604090204110d0203091b183c 66
    0x118a000c80d11820144622040c1c0002845800e000078980c10a51240094811802e6500305c07103070480c00d11400f425034039030012030102e005c50b00031401d0810307614200140c00300c1046003107a04200b1251b15009145184481c2d400c0703840d010f0055001201086070820404805e0740701d040204069001c01131a0b066219031680b109104014105040c400200c103101030301c0d0096429a000088100c03240750440d4041001f400079600400d2900c501066198000350a06610000c41d140007641204e06130120f00740e115528065400c228140c1e403d010301c8441c04001c10710540310340b0005050a44845545050040c15600385005039110401d001c0d403840c1141c021410038080456602c0c5070032840d40c2da983c98202c0100f140f4800c42c1e41e418007205646854002c01e10701d0314a501c0b032664070411407201c00c0003900151040c10151040c80103085600500d030303c581c8000b0f04000c14030480c0c003009029900c034400004200380c00306200300b030030f500d50b92245080c060f0324500c1c5407100d40d164090f030301c5501039043c1000b04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 827840341 1250 827839091 827839151
    0x2030915070210020c070b0d02123603090303030f09121201060c051623370503071203021516030908041e0810020405031506010c020a0306 61
    0x50019803500090054083c080b40540581c030764100503c1e071401d210303565102141ca803400003078502510b01c6030340c018540c241205840d5000340c2ca0308900507058020305c581e07030500700307000780c4605140500304c0410300d15a480040481e440c1207110b4021904680080e034403007103581c02c80b034140700d864403084c0001a45005900001c030300f40014103005921040c0c040c4207000910442610302e02c14844144060704030150603151034032449a803207001e480e085015800c020a80900c0511010700d52030a00300350b2031111540a2049450000c4039495803082c0100503100303411000b103502c0080c854030284a940c0003860180c403a8600709040b402c000e810403054150054501c040441004114000301020307113450b04851800061584c120301e40825640300c1c03074220306005240e400c1420010300d84000130b03000740e40012003500d540090501d2244140e0007280665070707140e009a00c0345000c3c44882c0320840d51054052406000080654010a903600c440340c00986405445504d18156044984682485005844 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 827841591 1250 827840341 827840383
    0x30212030a020a0b0603030d090b220f170c0d050304030e03060708010e060102210c01060f080a0209060a090f0b1c020a0302040e010626060601050a0503060909071503020309 76
    0x884025110f0810060050889508801140e00c80d00c0c100103407100102ca00408110440c2c0c603003460a0090030495002d0100707004c098000c084201c20300c8144ca91950b00200e5601007640130351f17516102d031140341c03010700700c40e0000c0c4205e9414040801c01d00a0071989915030b030b0b071350f402c00e420000c20750109118918041e41c040c105000d051640030702c3c003e0458003003001e141e03d01e8a030750700101c1c2812130254030a5007442e2043d03e0440d030582d140c80203084804160008110039a5122840000400b991107581025040b211901015050171004950300c002c008201c003001e00d1701c1d05044422183c88429907402a56110710b80d140301e0034070941c600b080c0c1c01201d000305640244d5070300141d0003e40c2c40c040240980e448030141035503581c0c2504071001820034150398003a402e008103e01119400c1c20a02103059200d1100481c00d503501540859090b05080e59940e490b42c0d4601040c0842c8000240074455180b14901e4009504104040340c24404501c580e00540c0c5c0b03090000ca021316090f103501d601589000340b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 827842841 1250 827841591 827841607
    0x110703030915170a050402030c032401080106032102011d160503030c0304060c110d050a0302010f06051021060605040504050f0606070f0515040f05250b09030a080d02030103021203 79
    0xf080300c07507911038450000451140c1e554030100341042e1000141d281c25118003c040e500b0800551b203003000700101d00000e050305a070303501c0e11a42a68207034400a02402e21281d15400c124800118a6040b1421400082103807400790003103d6450700749800d104146d800640900c809600296000d40c0185030880c025402d00c1078151141e9240d00c40c0c0c0c89104140408075507038100300320402009a0302c484d40245911503c0e01c40381049034940c1090001107006520741810070411600714071900080da071000c3d0002c1c041809002e4140e4505000c1000080b442140c00000401c41c80e0740c3c041e501c080c10f444c0d600e00d902c0d030740780009001c10b50300080c0c50b09000c0182d080403c101904c521051319049504139060030000100f82c1081410001e690303003100c07074000d016000c20050016226004580d207120340d045540a101050310070940d043c00d88003950200d00c0280707007080b0071050000500742684006054520a028943d90b00b0680e60084200c192059000301c0108290f1900d80b5074030710a0b4801c103010314501601 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 827844091 1250 827842841 827842877
    0x1b010905100216050303010602010915090c03030e01050d0c03021801030e0a08090a082b0219120207180905010c210c05090d031124010e07110703030915 67
    0x2507525000c0c035580401c841c108843c08a002c0c106803a00102540d94950715444001d020b4421a80255188002d180d01c00c41d149082e84540c4400642282d0801d0220f800c0d03650403540c441d0031807602d03410800c0510000080304c010b4400d4135050700c49901e00507a01c54280b02220708840448045a050500e44100482540c20114066054607444038400e581d0352023240004240b14001d0300019114440c02c00054240e0040c1032050000c41a050740076040480d080fa0100d0744ca80088800645040441c0c4034140001c10520148071850030b00d00582e54110789502c100d000503240e50f41d480386215200d0f4038a905100b001c1c840c040b64070410785400864485204d01001001580d120021000d503070790080c40c00701903c2142650203001c4000c051800808042c1002440135890180309a00c2c0c4c014001c14003140c3c02c100c00303401855602c868490203540c4c42c19052a89c400d000400e02814020500b40b00d20703482005110b03000c00b070740c86600d80081c803a0500001441341402c3c10341010070306c000d07048003c2c01116 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 827845341 1250 827844091 827844103
    0xd140c1203131203030e06040b010608130f03032a0804120206010e07300506090a020307271707080c0a0f2304061d060303030723120a021b010905 64
    0x3c06405040c0070085600d01107000f040b55100d0603070580115024003041000d10380401d4100ca010782c3d01e059094070b800c00480c16441c5803c3d8004c182030501e00010000038041d0b0400441120704031466940d441c0420301003111502000401c2c400500080704001c101724013105040c458004030b03c002c1020350b060441076000400082c21f18014090703401030010135803031400c10750450b000c507090b02d1011014a00c10703d540585404d40b6024401c0c0c00e03500008901018610070350f03100b41070070394820089812210021210b9060001000d1955902c0c03440481c3c108200c070000185038800c0300c010900d0618005003241070800000f07003140300b0030100e8801c00460078154204000c0d208400d00821420320f07043c8a6040c1040c0090b80507030045e0804000040c1710652907a00c00180d1800c200008175076840004041d181d210449002021032000d0b611614200412720343d6024010343c95482030b280050f0101640c0310544c08581100e51160006040c80080348045580f04100c1080402800b240d020303a500d16441304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 827846591 1250 827845341 827845349
    0x917040f0519030b18100c0804060c140d1508030721091202100302090901090213120209152b0606240503070c021c11061e090d140c120313 61
    0x140c02c0085c2e2108402c1c081c4401c0300309080307035001042a009036203000b0308146c004403400d640c0d1380d02c0d000b80720091500030101c0b00c1d5941c6103800b060303261a10820700c0c54014610800c0400031100b800c540452400c40400042c19124013641d0351004428855859010030344c81000d044040080b031800401c0001540c8000030f118035412201e450000c11071000031030007805a103041543c072580c1c0d07900000c2d181c42c6075401030016405418084680903110000d542440c2d40065000b50420880000a591400d105c0d2100790b21641c0108142d4a0107201c0203109400580003039440401401c003910481086100e200d40d10052200820244003002044180300942080450b4036052240000c00104c00c148a4400c00100c00c1c0d00030309031040945c40d030440b40c00001ca80382c0100c1e4074007120048040c0c1450544142c801e802114140030402d05c0c2c4026048000340c0000d00321981001c0c0c0b085151740014421081c24940d500c03090300074a10700101000708002ea21070714905c110250030800443e000781e10b001440310140d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 827847841 1250 827846591 827846611
    0xe0a02030f031206120d1409180403120b0102100c05070f0c230603070c06061214071e0b090102030904050a0c0206010608151207080a0b0f06030d05030a0917040f0519030b 75
    0x10000c0d0f00b6044040c3d11a401c0700580c00704908080c0c1d086c03003240f18003c9002b6800307a51124481c00b181003a0381c0856400030003103800340e409040704281d05e07141c9400061550b00705140680c24040d403a5540415034220340c03401c55103261700710014804202d1b11000000d070f640040380a001ca1450342000f18100e8032001d4a2035041081c0c0c288503506000158202c1e10003041442c50102140360a805c0080c41c8120900801095004540b0f001491441c0e01403015801d40204a52030507103440e05031000302c40c2d48440c1100381903010522a50b001542c85216030b5100b003496820215214050810080c10801c0c160404410b000d4418180030620119244603101440c0641c1c89043c42d03140082c2941c40c0a202e503106082c984034284101082290101c4818010b1011950031101c0391142e004042c0c13201c82074410351001139814400140d440e80e0326008003100038041d00080f050280d44003209106503001c6d403c480484107003160104803d080c407190410351191203070061101282184d40e48a4041c074054820118 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 827849091 1250 827847841 827847857
    0x1090e04080c1501121a07091806050310020c010b0a03031b060e0a030f0206070f140f130e06010e040209090606341109090d030e0a02030f031206120d 66
    0x440410807605000c0502040f80c0203203583e45601190318804880c6046801802610b5406045500305c69185d004800302d465849165051031b4107060400c1501c0c4501d80b4007502c502c000102500c0600140116000110002d656544a5903a8a00f5524140c1090f4040c1c42100c20400100ba4826112240748460745a40604994642409005001310b000e280701c103405085052803c168001d01d2046407104940c00350b070320070358603001c042d1041c1d54180310381e2011a603440300001103071030008000e14000401d6192103080854201640340d06c402da0750407050300046810280034956130015118038549004840540ca00303a501c80104100079006800140074a01c0131540c480c00d6007800100f400d00c850510b03200100218160320710700344400c8040c000e40d115141c40c441003100e400c00c49107107886492484003c02942d030300300360101c004040401c0b080c1e04600600021400603503051007940d107410301d004021501c07030300c010031018180303440038054901c18100700d80350328010640031444103445d50345802c114070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 827850341 1250 827849091 827849107
    0x110306091f260d142512020a06050901091115040302060d090308060402070302031b030c0d0305160207180f0f0e0a1a010f0b07172701090e0408 63
    0x340c902081d04030748181001e80c5000210b0005a0490701501c080364070480320302c1d050740c031410340d44a00b50110094001008204a503c2a42c40c1c0841c088842d4119201419241a9413942c0301c8421a004018006030131421102c818021107001e2076410041d000020800c1c804140e1301c4c1341014911441440c001d10404000301580c51840094600550b0080c09080e610b0110341c0c2c1d40002454034030700440c0400c42842c04604942010300c02c0d6506564560000c52404015600116140002158102c1584810025000c45070400d22480c24038444a407408201c9040240c81211b070361540d038140004550080e0000c003d9000c90282c803010407400803400040c9050619110303400b038181c0c1c42d25128003908000c01042814030004241985134042c1401c0345c52072070980c07203440f0741031000c3c0700c0e000300d840f20760305c0c14010011100c0007030200c41c0c070811440d03605a50021185103560000c0600300c65891403070108041d448c19001001c50b01079000d1030103641c01c0e0704042003294405800f0b84081d05a500100e2900d17 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 827851591 1250 827850341 827850391
    0xf020c010327030908010e010203011d06041d070e011a040b031008151e06060315010c0209040308010326120415150f0b0f031810110a0311030609 64
    0x8030000040765101c0318480302c0c0342400303028040340303100c1c01d105980780c00311192604c2c1041c401e070303410784880c203c8202410203000c00c2c09450280150003254407a545041e046202008048586094082c078009072681c1c5103481d00550007950164820005420b140c075800c40002030903000c40301a11441c010380b03904c80d1100c140454040009410003c410b2049421510a40e200d00c185a80305035241c3c0f08620510364250310402c008007058074140d40000c4107001040c8040c2c0800c00d03103400c1c48818035050f40c0c9054181c0006034468019101540481c040600500c01c0c0840502000461101e400101c0f0b5107200d100700a100611550001032850342c1d0640c0860100300b05e06000a404801e080000d220b032403040d001000582c412445980704000490307038000751480d9944280d41c0904aa0b1045600715981c101c1c2c1c000d404540c841c0408068040c140b800006904a03200e401c2002008009490721401020000342c00c5403d07011452410550600c200070290780da042c5002c1d4409105c8440c00540406d0348a80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 827852841 1250 827851591 827851631
    0xa08070c0510060f060e0a0e07180f05030106050d0b04020405041103150f0601020708150403030e0d0e090c04030f2a0602030702191503020c0c130207120f020c0103 72
    0x41150041c10104203000341c543c0c20140944451480f0503900c0f5030303200e00c03d44d041d0740c1c1d00d5142900409100020065540030041c1340d40e100c106824031103890300342220203440c0d004c041d4101c00e400045013202402241402d03c00c0340040d00060b203141c0a0210b80b9210740c03849000041c0000d100d01c3d11400040c0400540c8002d00724803280245c21640341c0d40001100f1441401c1c2142c44041d50110280000c4c095071001070f1207000c0718040806021044002d0490300750900005009a040c50344a074101c08410b1820020f000000a1550f02c0c0046490210100500050007a100721003000b820303c070500c082100c52460807240c40d03204410841c1d03840788503880304c5001000c4140c00a005401440010030a40100040024a10031121000c807060110008640951300b4004c1c08140780f000e00c20070203894080c5e4003c022013a051001c07a0040059040041d0212150081004035181c01180c900100064040e00c1c20020310503007008480f81c0e007200030003951ba09080c5851410161140d0350320f080c0300801c0491b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 827854091 1250 827852841 827852843
    0xc0f031303021203090a060b0a0b0f0f0412080d23070c0f020a12020906270c0708030114190509070e130e03041521090206121504140c0a08070c 63
    0xd83d0f92645000c4a48503240e18200c241901c20301d041c500340c64114a08603110700262203020b55032600b8a5003043c500c2c00160810010308115600c02c1101040401d0101c900c4a94203204022503907803200405010403d455a0b01105030250071445900c034000c020700940c0da40d01400c14070b044801e1415608007251a50102403000e0341104000c0b00210318000700120000c221342c000d50304140c043d04d42c0010300a55002d610850700c2d240789030a42e02c0403c594130341080c2e0380060344800b82c2410b128a43d1103110881d07000f0381c4103088002c2840c1880d01e0034108000c02c0f54016100211451005103010082400c40400420100c10059140450055a034915103052a4200030880420041160100407542c90784a0700441c0500600c41000c034200030300c40d18500845a10080d410300d008a0810300e80e802900300c101c400ca80c014418400001f040d10034012084c42490510000d05600c5000001d000886081d1154034228261a6080049000c45a000c44141d9041407519980d42d80d02c4c00000c5441e4207034040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 827855341 1250 827854091 827854123
    0x702030d1104060e1e010c080415031d010902090105060f0f0f040e1003120e04090b0703062309010314030c0f010b100c0f150209030304030c0e0c0f03130302 69
    0x1a0784401c00d0400d0040c00c1a40d246031105882c1c0c01c3c651041001c1018000c0d200340c0a140140007191155119000b0420114441c4410505040c1c5818015000c243c0d408030b003e00181d51040d0200d08030b6141d0702019a4100b4480c0204106141c0d600898403801050249074040c48000800a004a080e1000c4640c203a403241805a16140002e0501000798001e01c104101d130442d4001140000b5950b10300c83c001c480e401580310721882005403007501d4020004180740d40c410b598511140204a00c2c0804500c5102103940c0000c0a50802104100e81409508540302c083c10703140404140381c603210f0080d41520781000540840104c4100c00c149035100c0c12198001500511011400c2854150080910003404032401c030003c035106402126402038421011300100078420944000c502944035150640014800141c1340001c3c81300403034034607070041e4030480300c40704000c1040101c1d40a40c030308650020441c0e500c562404070480030828060002400503a01698040b00480816000300540c034844a4220 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 827856591 1250 827855341 827855351
    0x70611030a230f030126070e0a090602180108090102190309300e040519150320010315050102250e0106170f07020d051e160314070f02090702030d 64
    0x120f00d40b1580003072080c004402101480815101c3c0d0496130000100100c40050103190719204000e10354078000307400d0a4203140c0d0f56071000d022a1041c0000c0c26046456400c4200d0f01848030001010107030002c081c60401c4e44180414004200e10502d40c0011201c2890701040654075070078003600c00745201c42c01a92600c6072000e540140100f180300da5035041990b84800301180884028002604c0003114503000f00900d94960101c80159039118049070600c00c280c0503885a2240d0316034408204c4010000c0211032102e15840340ba40e0305002d542580d414a411a540b02c1d454440040d544105212110f008450146210200c070316522030050001c4c00542d07018401941d683c5406410b41c505900060750061000d40003d0341c83d94001c00e1a070180d040350b0700400030b00303042440031070700c039001309205640380c40a114120051100170300c040e100c15060104241000c001614003e00380c00441c42c107000c1070750405c2c400380f0007282605807003007090342d01611219599a01e882d004c07811445002c80b511403151801d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 827857841 1250 827856591 827856607
    0x905090606010f0c03050426010905030d0f020720190e06100309020919200a020f0a050a02040213091b1103042102150309010905070611030a23 63
    0x140103005038000c0e203d100e10181d91010803642c501d4028000703808a18108000c0100a0240301c5448100a00f864400b40102410780450309451000d1000e035016840801d040048010713900c1000c40c400120a011480d0010554604120040084091188183e0740240d4121500ca100c901e00981041c80185001191202c2c0d4001d81580281d4103540100503000400c0c0881c0d02a11820360384940081000c0c1d04c90350389001c88010b0741d109205d681203050319200791441c509100700310440c20b01a100503454498a55090013854860381040d04000c1f40e01c86801c8801245010404508590701a100969240c1d1030040030034144405a0027500b48501e41502c02550603510500100141c040d580c4640d804021840e00c982e0341e01850060101e00c40100d00c03011300f034009500e01d040001d480a080010901c0d0700380c5204d01190011180354800340d4403400074070304205040c070404002d840d80303007041c80d440104140000e40c0d81c00359401c180b091003100e14528042403d40b8041c02a0740c01d06c011203076994111 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 827859091 1250 827857841 827857843
    0x6070e0f0607110d0f15091a0a0b06070b1e0c04030f050c09040f050f2d3c03120f070309050601090e070503010515010c0809061809071409040c0207090509 68
    0x403521046d0790340b58004c1580d01d4034450500865503034a40208280204c041c480007000d404000140010844a580e140c1501c0f0030744a100203094894020115445246803100b26501d1030480462001609007440d400c20000018510a8405a81c0c220002075240c0c203d5290692801040b00c540b1076011012400700802c106540c40401c070020b115106599004c000e541000360b41d080f0300b001c2250002d40c0318840039120700d120007030602420108000c9440c080703507005444407040500d100f00400c03e000980c0039035a09009650f045250b840c0c5030700841ca040203209007545403107406000f00c2e00301c00e440710100b07a40c3c0344039410048410f50008141d07070342940c1d00c041b030a0003040784000a41c075600407000c0004640c034042c45260302c41d8a84c048980c501902c007900446151146c00350440f400070040c00a00c1c020740b1410040c0009022004d11189501109000c012040c1c02c0180301070100076111000511001401080c0e4034000780030b0300c0201e000141603500340c0c06c0008079005041405d1900080260b0300030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 827860341 1250 827859091 827859113
    0x5070b04080c011e180306050708071403010f0306020c0c041113050a1802071a130b0108030304150b150f030f130c0e060105160f0506070e0f0607110d 66
    0x1c1201d04a400ba1a08103005581050b0b000210300306203100320303a036020a14040c101c0d256a480130101c06200041e12507039040d0803103c05a40c5000001d102c003040085090700300c0101c001e04040d03520250f08542c9032408003001c64846007c001d0440d500421201480c0c00c04005d5499810070061040c40740c072600d01c0e01850703d0340109290484001c21a00c00141609090714490191070f00d004141070000c0040080c1c001035444030000303c07141042045036982c000d00441140e400350f446041d441c14071481606018400d407406801401d400d820800c01e200006088481444c0c84140e03512001c1130130251000042e000e0005030b10311141246000526049094603d8025882007440d01a00107d0f900e5074003000c83c505106020091007070071218400d01007000c4100070f0f1030b40000c0514180e890310004a44001a4000c1d080049942d03002d1800080100702082c8101a402082441c00030b02014007880051011001c1c00c06050261100050800500a84060400040401070449080017819262400344d40f8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 827861591 1250 827860341 827860349
    0x60c01020c0c04180c031205210601021e0d110f1f060b040e1302220510060e133b0705010305041101110f060c1206040b031c03060305070b04 62
    0x82d00d40b40e1010850818184c4850080c0d40000781d6103061421965450503041c862203900c81403101c28001d0070790000b05e401c0d0701050107140400310202e90800100180c81c10130010804a1181040c034566040141e00080d503040c80d00181c64404003050700400200e0400038560018001405051500c151038100e03031200da44510b482c42010050720303a0f10710f2600c010303015a0041804003802c6102280ca0b918914560000c12030008221000a50030800b040e501401d005480322070054594040010000d4404910300040c440380c280798511684010000350b84005510f00c00480503501c1116030200120385503c0e40a0b45104141503010080004403e0030381d46904d00515118400c1140101d0594400d01985019030ba0020764220810310100055a8160044c9445c400c14440ca011903004904100a42800780e83d80081403559009640079480c81c610b0001c00c12030040782400d99481d02501c0c00a0740780303e1035900071b004441d62600c0000c118060f240340d51000d030180c491207001103211800c80c3d004108807 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 827862841 1250 827861591 827861599
    0x20403050c0607050a0b04060f020a030e060906012405130324060617042a15020f03040603020f0715051005010e130c02030d0e0c1206090c0f060c01020c0c 68
    0x1c105001002070b148103620006200b500040031400000d603c02d908150070038480d26010550031280240344040341c1181551a000a031a80840200c020007401003e170004c0c8000043c1816606004450800105002c001441c403803804203446078252107582507031741c0c0c90002c907501c0303045599908181034010540011030605c0c4206200d00b805654a80c481d060850301c264844e110790800150840e800054014025207100c13003020b400d40140c41c01d401d0b200319011502e44080ca0f50398242600e05070071940d281060340965000a24112500c6400000d58048031000e2802507619180c00c02225075034010070b0070040c20201c50458040f440c82e00c940029124030007040c65050115600c000464074a092100b4568004144421274400d8400641101401c60003600480b440c2151450725002126151140c0e00c5158000810707141041c504aa03085100541d56002004117051032005c041c1c0b01e8000300803051103040d2403184805030392a50015610107507901c0c07008546070f02e81c406c00c5607200e85031010f4951003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 827864091 1250 827862841 827862853
    0x306040b04150e18060408070311010f0509060a020a05070f0314030406020421240b1e03010f11040e0603120c160b1c050406060504061203030b01031b0c0606150302040305 75
    0x2040b00003207038103004c2210640003003400b5201c548401c6440e0f4007042e029010800c06143c0703103042150074011800d20580c01c174000175003031801c0c82075141440e001070711345658180100258074509502105a6401e56008031400c949088280703000e4542241c03191070500f00610110801040c041c10b60b0103041111001180807422198844c0e00c2d50071070181d610001c020703000025801b12841c01008890200c99444680010300d45010000155800e09200700000900b007800135a60060a083c01280c0d80711603000014804e83e00e01d0b40e01034100d03004c1d0f07000c2c8881c405016400078207261380c100000001c541450841d26658020030800719180d9441401030764030700100c41400501c0e607401714111443d280d041003a020701d052400403054003428020b00241c40454031010b011449550b0380c40b4600040030070b000c0070818602c2318900034080e10300196610781030616043c644003c42000701c4d40114507800390b1800c0701c0c4007681481c5c101c0c02040c0315040390010845813100030180d59050703401001503900440c03c0b00c003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 827865341 1250 827864091 827864101
    0xd050105040b19050f01030f1406010f0911070b040209090304030f0308180f031c0618150f031709120a0b0118110d020a051b160905070e01050306040b04150e 69
    0x903a0000d440005d180740c0000d0042010640440304002007a214044c1405904a00413440d850101d082c0c100264040e2042400c12086210340b1941218014240043d400d04060b902c520407610f6000b400130b405000d12781d000580500040c02160b02a680c40740070100c00480c1820010454902140c000d00718640f8026098960b240c0003d0075002a80c0744401140340c142303408001d11003800081d180c1d160990310340d00d001c190303024000340511441084820000d00c41c0d074987c1e007030301d0303803d2031313a07000140081c1122002e1021400c44040c81408801d481206c550301c5074250080303240c2c550315000303034036850050700c4108040000310b1248604a03660001c440d46020010350803102100c41c1818441843c071003c0012088001c020b4016203025006070400d14241945902c14294204c2400000c5405801c041400d100101651040d0006003200701020041490b00711406040e410784140744606000b4040700040e4030384d441d9084000100c0014009104241c000100403403462141e0140c0312074011102c0c0058 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 827866591 1250 827865341 827865391
    0x10603090b2223070b0703140315060f0708160c0515030a110715062909091f0806090f0d0206010e0405070306020a021b01030218010e0d050105040b 65
    0x189000065414500204a082e6600c0c00708204440c11503604601d0f14032105640c1da01404100020b00c1ca02640d01e660782d407603240092482100a1914500348428024030441030350700282c0e180fa00c88151041c2d43c2d2075540c80d81400c814000d01c0740046c01c51600141a1100107002d0703841001d054801d90b1115035a940b10020071800b0040c948031000e5200c401d02c001861088142c20090140b84801001c80c6441050307110004a40c030400351811217162246003c000110405013401e01c0e03210100128000d400240d110b0b6034280c894410807900c034121650119011410000c1501c002841c101d41700302c42550f9030213206440300e40844084003a4010078581c3ea440e903070049681580b040481c3d01922450f800c12180818040d000b50003a5110701c540000880045e050703200070f000613411900140081c501c0d00701705020f008020244e042c109070041c0511450b9609483c018a02c4007001d003429410158090085245005c0241c4003805540c00c00080c0001e019400044900500c11605502c4040030315032140c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 827867841 1250 827866591 827866621
    0x1815040b1e0912070608060904031d01030e241806011503140f010326030601050c0f0105040f1406010e01090e03070b0106090503071703071b030605010603090b 70
    0x1050140001c00044a03403074032105001180007240107096060000c2c100200c1c04100000d4a000542c1d84003039420301c5410381100805034812030844440e200e03031034180c1c2c005120f007070702c8400350f0180100c07422101c0050b0f0181e00040305561182044a1034003501005d07485030350b500c0e00002d01c104c0700d01001044411000d04070310600000f1980040a55034a01044600410582c0383c0440415a07120a200303e0300410000450150179892080704d515411400d000ea1007100300c09141818290081000d0f1a20350300d001030b06c0c1e001c3c60909005031a9801061440e0412552000100d007079440e0104100401688120704641c203030280c1614400d0854103041d15689900c02e02503142c510f10000010401d40a154220500b416000d0301070b40c0c01c2c820075940d00d09a80c5403e0700644041512100c0620050600300f0001c8003d25051032020b2001c2c0704015255103074403d0b100d01404940f00c44103200c80c06000021503000071640f00000700243c0d0707911203005008011089003103408640d40c1000c1440c4030180341d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 827869091 1250 827867841 827867849
    0x70f11070b040e0c04170303040201090806060f1c02030105190b19210f050c01030e0a110f0a03050304080105074d030714010b010f081605040b181504 66
    0x2070300e000e0030103240544414000741192040798040101086601603240d03003a06c05060b1708011600e0341005d100261070191135400465803640184104076940d5200d01c207845a010003510800c18120300c0c0d48450541d0401d158020350590b00388000c0c0040c1c190364035041050744c072001c841004095148002c03c161301500440048201400d03410070b00644008000f00e8900d4a6244102114042c0d55174402c0c10070144900c06807600e0b00305070101d0782c40303580500403042c1e0b02b02032201400340d0010f40d03079403040c0c00003011258601440e251a00b240540d00e0342c500007000b4642140446e40c41d259600e00e05406004211a07040018040c404601c04185c0400c48001c000c103201256030800c0f03812952285150741180184c403031141d0080c100300316106800d100501100d4080c0c980b009000c0002d24030302d825100140c0e04241003148444110360b03000e030b110070500c1d0010100c0c90600594802b0610803241c2c4e0040b500900400240003626070080c0360380d1441200400030503154001800c10080e44101c5500562103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 827870341 1250 827869091 827869109
    0x6110303040303051f120308152101020c011503030e0306040b070e0d12091409220f0c33021b01020a0f060e0f0a0f0326070f1107 57
    0x128000a000340c04c0140d0140340c86020400c4520100d031508891590303640202c02c400c41001040d030625a0100c801030748503200d04591141c0d04001c0c8042420407440c070b10360703000249840800b0340c128003080d0102c030601e03940e000c004e202000c00811140302820162008602040c0c201c58a0416820f001c11560312440c0c01c14207450340c665500000b0b0720004048200c060748001205580c03000251012101070300c100075981e8810f1b03107508204603c04190ba804000034802e04030702003000448401d030a001d541181034012001602480c501d4146c0c3c508081c0c800041140c654124046a060702c42d04442c001040825070701f1000c2c0d2403281c421000e0a801c00c40340001a04446d1340701d00c425401c0d03100c4001414040c81228121091600c640d445910155021640240ca030039190611500c104062400840380c040980325085540d17407441c841c1c80b65803500800340129201c80c0c020560000c0c00b06140591010b144113014540090006c1c582c021641c100c0c0c01091051040344a5090005001e00a40310120 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 827871591 1250 827870341 827870347
    0x90501050a240311070605090c1c080f0a11030c0102190c0c1e081504030f05030106051804110a0e1207080a020d1103031b071a16020102010b1c0606061103 68
    0xa00704801400c1002c42c4d224005204120740700028080b88900d0f442421214050300c020715030b01d41040110758217010b0005155030f00d0840c200205692201301e030355505503001d025980303d041080c155001c81c0082c811852a000206a00b112080190024410402d040c0302d4a80c20103100c100580384401d048001408a8429100c2403000708034802d1400e6940101e014203401984e9980492460120b0000d4441410941c040a10041540044000080650608129040d0360510b01d0040c010301840b480e000c0c0c0d070b41c0b00c015031116640341c503404107070048038906940d40d4070401202c000c1c0800c0e481e502101c0c000c611036042e070301084101052250985445201401090056400b00310b82d21901c0c00e004d072030002d81001c00908590342007008040c0380da4801c0c07800304038101c01c00040c2d0500308a85d00c0500788032103405c990030b0300c00c45041c203c0340c1c0780b1690000c01103082d81e01e00040b401440702c1c0782d05039084240c882001e0744142200e100b000c0d041b407260605002003a26820301301c0e681c071b541c808007101c030f68800c3c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 827872841 1250 827871591 827871659
    0x10b150703120f0e0f0c180f0c070f08221217220e010608010f0306020a02010b031204080f030f0a0c050a12080a05090c030c1009050604090501050a 65
    0x442140b8981c40070082c002c0350f00725400c1c0f12601140c2d03d400f0005000d071320408540300c0c010170a10420201040888414901c1803040c0b1000c81c1d010340080c000a003c140040002d1100850304040d520900c0d0040101203000d00103203010340c8554030051503695004612024040c02c4403040d10210161400781c40c4040d0307005806ea0701c51002c11501c800b0000f18101c14061418846203c1140044045072001d4005049107003c00b084d00c030460603045081004040401800f40301042e041880132254014070050b5140c100d440100e0050a010f00c09941c5402005020601629294040c01c00c0d00c1c16403040d500c200c1411084156603119180b054100d410050002d80d42c018010301050751201d00980c01e4075824461580c1c1c0410042c800b9000001203142d000031700025401c21f2140940c0720700c0d80b01c003e00d000c0e459400040d0f0303a441c0e13891080744110300c8501140301451040109030024074014203640d03160b0b511000e141380070340424010700d0301502c1c0c200000601401804c04100c0400010420392404000b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 827874091 1250 827872841 827872847
    0x2c100501081812070606350c03060f0a0f1e0b03010219050309120307030213060c150c0201020f19080c0f041e03020d0302010c0801050111070b0310030f0303020903010b150703 77
    0x107000c00303a1740940c0e03400e00002c3d81040803811054100d43e07003020381002005500e1740743e40d801c0e84020400362548145c0180209840000340036070807100c00180f010329955580312450252900c565105540e60928505080080c154140c89024400000c0d081c0401c0d408041814202e008588024401a460107c1142283d005030011900b1503425801c0d03032511520024440540e40c015681c4e000007070340c0050340829031100080d42030003600c0300d0718211016108540351401c001100000b14200b082e0380b020054180c40c000d5040f101901900ca450540362840704001c3c906581c444842c0002242540b8001003440c1d01d00021221558495000d4605042c2404445070047e0010b1b00000c00500c4001e6002c409a9075006068030058800d0340046090380c03c194006141d100d060f8080d60610042041c031544e041c1002c10404140d442140b0003d03100c1c0d07191b81c0001d11141150b80058581d02d40320903203105048d450340080c54010000d0300244100c40000b420300c4000401e030850140074040900000c00001d01c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 827875341 1250 827874091 827874097
    0x20f030105091807080a200108061012090f12050301120f0512040e190c1d030106031415010501050f04060c1502030a0f11090a2c100501081812 63
    0x203c0041403030025021001e503440d11405030005540c0b9803180c0440070030000320350b800c01031041180c003880004180b4a0b00180403080701030461032155180d4144a140944148848809540800300601c200030039420014200303800c100c0706a904050241c41490365501034400c490403144501040e50380300707150783c444403200203000100300d406004420f1014010301d103600141002d0306107581e10200600304201150190385034050400480c604040081c018150494501510329410b0040c0410b9440b01e400002d00500b0700742c0000b4000250800715201400000944011202020700150329030b23605c6000660700340c0101c540358004c0d40303000c000a1001500c10235000080034802d419004150b10013507041c07003da810031603030000d88a07a0340622008600450080c41d01800c1d4181c010343c500251074020911100321400f03a9200015036203d08402141000805128060880042c41d524100542c0718070380c0080a204083c00a8569400301c1c1c02100241400403150021000826a02c094648400d6082e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 827876591 1250 827875341 827875351
    0x1213030f110709290108070e040902030a1211190f0210051e0901020d0905090f040c03050102030a020414060307200115170d18050121020711030d03020f03010509 71
    0x200581e200001c083d081c1e07000c1d0304490880e00c0485142c2000d03400c40c0d540083c1e440d540c01c07810040d0440074801259003003000c950290701d0613100880c04441e180042460325904200003440c0300e883c0078200003029070140780c5038089003000c402d8a0680c4039000c0045181c13104200c01400380a40c8400e080d00525209103000f00c0007900d400d0590805403c072105c51030399035180074030360300040000400410302e40c2d042c4901d04400c1d5540c1410300a0350b00301030128030382100c020308004015910402043c00e10030b0700c044040086030700000a559038941081140040d406c24420304401da801400500c030149400400d80b88581584d540d40206000b00d0104004a50503e00140c0501d5680384030304401070780503070034003005840224600200307201c2c80e1001918042182602070100071600d5a5145440c20001d00d880456100b40380441c00c0c0217602010701a10b0b03076000060b80e001c510004101b001c100c60030307c20100c0283c04506a03210240300100c282c0503403141002e10f04141c0c0d810801885240750102c610f503040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 827877697 1106 827876591 827876593
    0x2040605250209040c0f15020a02130e1e0c04020715050a11041206050f06010215150607030239040b0d020301020d021213030f11 57
    0x3034081d0800ca00450000100c2589000c03a15039500c68029400400ca10064103080c50300c80180c0c0c0320b51142d007500101e03c010010f40481e8104021114074a03a4014280c139402a9081104904031003200002d400d80c0e9100122085000b001035210990403000e02c00c00070f11980845a10b0036100c3c0100f00d00c201c0c0100542800100d0030b0302281c00d680310922000c54035844003002070000d4460030000c06c03030f41000450b000820b40386010540d008540650f0313003042145c903004054155607004984140c00341c0d2003440c1031492000040701c6690321001e60007000c80c4402c0e2400001c1c0a55001d2081500160301c800020000e1000c0d050810350b000c0010440c000311043c02c1c001c4044640c2c4030100403882155911740010203921002500d003601d0303a00600031540d40b20005c3d42c18000f90010341c1c418110036145000110007101c4805200d03480394143d240c2c40880d82d1200307001c84010081d11142801 = true := by decide +kernel

theorem cover : BRFrame.Cov 827697841 827877697 := by
  have h0 := BRFrame.cov_init 827697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 827697841 ≤ n) (h2 : n < 827877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
