-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4695
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:26:27.513429+00:00
-- url     : https://prove2.me/submissions/cabb7393-753a-4964-874b-f08d8b19ef5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 844244604 ≤ n < 844424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 844245854 1250 844244604 844244623
    0x70b0c07110d060506031204080d0509040f060b0c07060e010e090603150703020a1206051c060204050a030c15021b0d030e1027030512160606030303051504020408030a11 74
    0x42102d401402d040c1071000103050103442e468481c0c00f40c0090038585005800c201d40441d029080a0300c41d01c9410079050b01d950700560501034210313444200d4840c3c0180070344030304005000020001519042440002c518200c2c90b90400b00912102100d20070b41c0c0d07a00a214040001c50448000950b81c1d22880440d0521210001e90042d903400301050106082d05a0060144409240c1d01c4800c0c0382000200f4005888070f4ac86005e4100f181d401103125426520398041245502460000d4030340340d902d0000c01c584180d10360040c0c502d42440e040c00c1c044001c4004009010411601c000c02a080381c11008192044003004028404d40c2d00904039000c160269418a0802d02c0c002c0440c12043e1170741d50050202c1000b0300f400c0510030399054040c6151401c0e0007500d0103498000c002003c441115200050b1b0950092482c0409004c00a078004e001880034020303c409103210780d03008103580c1000c0310050400b04440250704d118030300500050084a031b000013541e940a0880c44c007030006d1400748030202d00700380602 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 844247104 1250 844245854 844245859
    0x207050d11041b030f05060607110a03050a05061e06130c030f020f0c0f0a0503030f04060e0f07090c0207031104020a031401030f150e061519091b05070b0c0711 70
    0x180e44458149400b075802819010545051013104170450349a0200c8a0480b0082d030b0040041c481d130008101201d491031800700c0c0c080c00c110318541d181d0300c0302031070221a43d500300d600d43d02a0040000200c5221003103004001d50722100059820f0100000b8100c0c00c004a507604039594941100c0c403418440e4010303171642c1444000455643c1c11401741304405501202510074603100312000720501800001340c84507010341001c0550300b0340c1c0300c1080c007504403180504240c0f0680c1d150b040e140520307007040c040b9298580060008201d003504d02007504080d85c003a052160195041000c040005c03e40c02c0c220044c04081c100d600513075076078241405030000d22460099103641d0b00e6100000c010000003800e00340c8902d0158900d00700c1d100c0300914003030a490310a044078506822550100340d22807420404010300400003040b14080c4003400c840d103850401c159000b40201500c2d2003007805c2c2c46164120080038200b9030300d0410316091382ca459080840c000031b820a203880708001491000e1004151840d002010700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 844248354 1250 844247104 844247111
    0x80a020f0435060a02030c19050a1701060c06050903040b0a02030d06140a0e0403110d0201151e0303180807031220070b0f0906070b071205070207050d1104 68
    0x190840ea0b401c20403082c0b501140011100c54000d480c010550040d0394001c60080104059503d03a0300c10300280d00301904512840c8424000c042103003044421819802000f5903400d502d070b082d0aa4001d25004040c1d011084884581c801070203020390000364407100135000040480d064494241d103074610310403a481802070303007400300302c0e40700540c0d001c8003c001c0c1d81c181d0780e404e000c0d0035205d000041115444038040390b40900c405100308821480d084015074014080c1c14100611b07180201d8860a0504011202005035566404550101b84c00c00054000d41901418820140301c00e28000703100309940d01014040c00300340300b503401c6c1210340050f40c1d001601c10041038460140c1d03a8640440d0004101d00042c0201c1e00c00200319034140615001914501040340c0104800b520f40840c0f04101d600020a00e20381a00c1000f0407a0183c940c540149400b61180712908030a1401050050408541240201c41036060006021290f64005015000c2d00c004a071505076000f81d51a10300f80d601401c2070b910350007a04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 844249604 1250 844248354 844248359
    0x16050f13030516031a06060304020d03030b09190c030b0310022a0d030605012111070b010810061d0a180f030f030c09030308010e100305070f031205030403020a0201080a020f04 77
    0x400683c084100c0344101c8514407212510007070303890a00012203490750440c0040c0005130152800d8181140c0071406410b0000321842c54201181c3d007000126520b010f000c61101f007a0042503031a200c0c0c01080d41040c0b404000d005841c200003034949000825a000658002c9042d81541c0c41045008581e080b64030824841080704c211050303124816041c0940201e440c241c0001080d50050301000010204800c0c0b00f5042509200c018000300080c0f01c5001482c00107008002c00105070340d0702580a401344000034122042000b00b0b0106844042e0414202c2c541c41501190040d00305400403030b0400c88140c0701040391600300c18a0620121801c40207442c515064459000703040d0172000040020f0b00c2580c0a102254141409440c041d85a1000030300040900d00108000c40c0507180351a00704ca4031035030000040d9a0703519003510b0407103541c02080c0408442c500800411170109420f03503403403115040580c250324150320040e440b1a06c1c8003000c0c3c180000c103030010b0a00013440c1c0c1100c412034640321803039403550f4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 844250854 1250 844249604 844249633
    0x30703150b0408060109200d1a1206070c03020c04020403030c0203060105030312281b1106060109090b0607020303130e060103060518071e0f020c04020f0f0c010204050303040909020916050f130305 86
    0x502c0358158030320b4240081d00f0309e2441c02d0805a071001000200010301141c1c0395804200c524108007613043c0c00718051030010150f9581c55000500c0190f01a40d600b009a0040340101418000182c0c4424070a44c001c000070b00b00c1007508040c941d80070f6260411454642d011010307180321060018284a6040d15040c001c03903840d0302030041c00017401d000384d44130300c007402004500c5d6668540981e6080d0200d03e009070100b00c81c1c1c2c0345070442c0130f000034003404081c10001103a01007847c41d00800b220011216162030288a011383c00d1032030175030141c1d0918051140d1842c0c200420040c0c07a03100c1c81b101810801d4400140c91500541d09010345907181c41c01d80000c5100100c0051030303c1c00070f0700c0040042c0038030030000c006445d1034029660300002c8101300300d241441001300ea1955a2040c0d0383c2c4800c9540902000881da41d0a001420041c1050342c00407401641510402c02c542d0f4006081d940e90314858046100d4642d8400265907070b1012000003256154500301580b501c1000c554001401e5101d036141c2e00760b089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 844252104 1250 844250854 844250861
    0x100f15050d09060905160605030a1515030c020f1c0e031e030310090b09070c0c09050f151c08030a020903030c0c0301141b071502030703150b0408060109200d 69
    0x840c001da00b95003401e80c081001440031b1a40d0302c01d440c0003d1051011681100c040c1e40104454000b20703140d808800d40e14032074900362960751816103011950320359520301070329018040c004200ca8003c020b070190b191701903c1d0f010300d002c035404028104030303034018107805c162170420500031070340800d15211240394440340010359030350320485032202160040840041c03582c03030301d019440c000000140041210b41d03030307070388200c4401d00c80742d206982c000c44440001401e881207116490041c88000da03945a5464a05117a914908104c101c2c2800361030740030a0f0288801032014000141588500015601d88810810303e0180c040c0b04a15581800001000100c16400142c2c509016506030024000e20050040603445040100c0d50703035000880013840c0340f141c1c2c440d11006284140c45040d4202d00d091800203540100d0300116245804203954003001e84020030544020002011208855442c2c18202003040391601c170103100c0c0e1282e464031131003e0300010651014544002c0b4a0b03041c4241c40301c50140244014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 844253354 1250 844252104 844252121
    0x80909101a0a08010e090c0618041d0604120210180c060804081803160603090506060a080712080904050705030411150910030b100c0308100f15050d0906 67
    0x3468805020807400001d20007541c100c4009a1030f100d215a00c2c0c8811220010360003450880980910f81d0100380560300c60f00504104280058013580880d0b851081c80300303c0d50704001103034030711080c184040d0a9034000100b0310741c0309601203419046503c0030803050f850018400c001c01601410152103050100c0c106000380240d40c015400c08039140d07510340301612000c40560b0f018290b817004110504881c1c0d08c084010000c000058200c8020b481441d5480c0a000c0464108100080e03ca0040348140f0404020703030b075004102191601d103410320b01042079684007003520079025013104d4001346405100a1001761403403e0741c080c1043c40709181c408802411507008540c1240d00c1a1604510f01490030100340f011045003940039000d25140a44041140650b407e00090041544880f0344c001c6607142c142c2681c1d0400c45589030003005469a26029240c400000c10740c002c0108141001c0104800069100c1c003120100210b0b0107030590a414101c40c1803241401d944202401d002a40c3c042094580c080c014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 844254604 1250 844253354 844253369
    0xf0905060309100501090b0102031909030b0a020a031416030c0c0c08070e0106140d021605010f0c2c10020a0b010b04060f02010527071703070201030501120c06080408090910 76
    0x1940e0300c2c0c1511104440004403211300592040c86202f269203001d041d01e0b907514549007448498580d580d942c0c11381c000303405c656016010f40c02044000c002c41e054000d12001401c461400f030b4651404101b00d21100322043c410f003040546440740900710724002c200041149820aa1601b40c4e41d41302c2c00426525225403080a000d0900034000043c0c07213106042c07402a103400d21040910381280c8840e408041d4008107824100c50100c420140b0001d4824843e2810b540b1095002280420ac01500a400d0030b0100d02c10308605607a080303142040c9441206514101d0ba002c4410b60307a0500c50460480c9890849000203000c40401000440c01d440c03118090f0003210a1603032080342424604508034207882040e1102d01c810203c030b1801010110f56018100c05010302581103070003c598444407401c11038082c00c40920f0036080054030100b503503814058140508084c50310390520f8201980c43c00e640c00010300c1002c0c1040400d40c08101000301420031119450001004082a814986804410541d403172003200b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 844255854 1250 844254604 844254611
    0x1302042d0629070803060a1203080402090709030b040803220b04231b060d06030305210405100b04150b280906030b0607050312010e13020d030f090506030910 69
    0x4015100102d000040702031142d0031802c02d203a40e40c4690564002600312a13110146078408120803030b159515842c010701940e180b00050825006200c2140d01c0540400c0401c00f5080d07062010850a228261300145c0c4a100965a40c2c1cad0f1b140e1910303c91217650042d00e00400351908050610100303c00d054096805820030006101819903806001410b60044070015000344420b5001c48200f0701c1c00030000c0b0005029140b070a80b031007410000b203503035640003140230800114018914001c0b0b00c1038104444020340c07040210307080580b100d5980c0d020b000e201a0f200c40e00c1e5203410b041034583c2c4e0440c503840800c00d003501c4166520380841a00640196170303642556100c0003030141101d801d000500c0da45883e43e48070a200e0038104181200680034400c00b5a030442420401c207400140204010b01c0c01d20441102807a0b60b504014004410000142101020443d4181500003603030715161501481c503410b082c540104100c07400c0c2a00c00410b10790086602290100405c03080c50008a04407820b810f4800e004c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 844257104 1250 844255854 844255889
    0x507080d030213030308101503020d0e0d08040f03140315010e012f03040e07090314012003092a210c0919020304060f0608061302042d06 60
    0x101d080380180410160183c07400c0740100f0109004518998210110741da011040765100c442000700d85c6007840300400003c3c0d002840c090192040d11441c03c0340000c44002d05044d10b00741000a10039680900080c0a001c28030001204140c021a02501c5910105d19466160b150001e80350302c611000007150b074040b2748142c400d091158071511002105800b00c903001f01180801940e171034504a0304d03400707450b0103102c200000b103032000300242214400c80c1c6c1c96950725419400c518000035440085190780069a0410904044450903412202d0500c103198840350340700e9585c00305480c0390811600e00c4000e805a04410305940c3e41c0d81b220780a60440c01a00c20340e203004600290002400b11002448115400182c00b400741490241e40f800c0d085090f0a00401d00c034005000d802c805c9a0060b60300b02c5500d03543e040e0990071400b42d4040c0000510072007001d0407032850320708118252015100c40080c4203965400744115044561031009036261040903003029001c1d01c495019004041c0ea004031000d103840c00c00d01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 844258354 1250 844257104 844257107
    0x160e070810060e030c03010f05070f09060e0d0c1d04030905030705090f0907150207080d1407030c060e030f070c05030304080d030e0c061c0501140a060c1703040507080d 74
    0x10306000300751006068401e14505041203c002e007440300d500381d15001e002c0000c030715980d003401a030030100c003103890002e0300d42044400a0455015400c209081c00000700007041190f4120240c0208100b0684200d09081154034010f030703417200d0540200740c4c001c6503604030002508003c805284611311a46800c04200e849508165649003076106043d0301a0182001038001491320f0740b440e4000354540100c90b9800d403118640346c0401c4020708401b0040c5c1c000842000440410800c5400303140072410031104170084201ea030f04403840f0301d40c3e0140500c41d045040384204503466104000e4071010f50143d0b41c40d0009201c0009079540038840039599840724090104291801004550846140d08020311541c55006815006081540070744142030052400702c00c0319844103401030040ea81c2582d00e640101000305090421a101030300303c60380b43e41d24171040700300e01c0e00c41281c0842030b40c544d800d18114942040c60030074072002c054240411410404014031003001000108802034615180980d002881c20a40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 844259604 1250 844258354 844258367
    0x1020c100218061309060e0403081608010506031812180a141201060e0106030b0405130b07031d0f07180522023c01080606030103080318160e07 63
    0x41ca00c000319120b1900d503080d45403100c014101c0340b400420b52803000e0350726442e403c01c5404a50200c28a05400010001090b0344041d00a61107003200000c4c43d014030310554028488003050203101d0140350008081a00005042c500c201e0185150040f60498540d01648207000d403c15641d2010050102445034a14540140088207a031b202e03100d0885071501d64010400841000c1213004095541d80002180c00d5080807502030107000d05440c0407805075259002d0108842004000000c03034101c0c90813402c00542d400a14503040b0301c00c1e00e408503000f0000c405510f4800c5d4038020040862203075200c82d401c5408081740000c1150807014600045410003c88281a158100c5403100c2c440c103401424800000620b020013240c2c2d00150045003420f441c840d8105a240540200320405000700d441c0c101088142c409500306028286010495401c0404c04550140070600000b040c0c0c90000c0001200000d07400280ca5140280341c0445401105c45010203044000e58080c0781c021030b10784000505120f00404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 844260854 1250 844259604 844259617
    0x80c0601062106032d060203070f1b0b070806030f070810110c101d1006080c0f06190c02061605010c090518071b0602031006020c0a03060905190501020c1002 69
    0x2d030411364001704e00c06482011484000140d80465581c0c0ea084003141107807029600c200034640340c0300c440c0303041c1c0e00000d401300310b00c90307188845203c000410320000740c1a84100b1303801c003000d030030542402d40392200040d040040c0c904213414648a5060001001c440c0020743c1401d4010000e42001640b2100d040c481030f911884081480550001e400d03540244800d81c803004400101d00d02110b018110355510364200301a01d0105043c01d501d5210a01186000b8040c0c524131010440d961100d4032040c0c00480c2c50340c001d000038800110044401007443d2801826200b201c258010100c41c1d54074a01c1071440c1e4a10480d55013a0b80b03e601e40b200928500d07021351124000da0f00000c7c900400e842c3e40d0520030183c101c0040240c1f00300103070b403242000000701c03505120f41114442c120158580c03038000320034544c5403c2d5030300c038a0440d404520b00c051a620b403d820401030b80e400050105810340765050a40c81d005501c0b1180c0c4203101c1ea40160024000107501600103041483d0a444898005031181400c0e40075a9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 844262104 1250 844260854 844260863
    0xa150c020d08040501020415031d0102041520010c020a210c0f0c051020060606091318030509043c06030804031101080c0f070f080c060106210603 64
    0x801c1d038809590148481c15405481307080054581500c03036131107150141c2032010703000c00300e130b154565611201d0030301424020a901c520021400c0516000320010f84200003c5850240203075150101c207110b11640380903c40c01d024600038001c500003480d00035620704012506880000840c136123034150081007824040e0741c400030742d502c80340c580300c5440d4a41c1c40c1c41551000c135605030604000040c2600d51010200003003981d91110400410704004805811442c280f42c0382c0c0700d40080080006503540c1d5410303a46408000c3c5c40401001084284040050030700c4c050b034104804105540c0b10825034804c0091081180540b03040c041f0311314100c0055106441868480b0000c103080421844804401c02c642c900e0403004400459201c3ea40d494400c1250300980050381c054284006404072540c001c1803041d0045090f920640c0780201850028a0074020f90b48020054800d030703a0600d040c0400982a2441c41c501103080e580e080d40d441c200503000110a90104a20391140001036011100d58407484003103c1c0c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 844263354 1250 844262104 844262113
    0x1090b0901020118030908010e01060f060302070c0803130504060e040b0a0e0c0d080307140c0a030e060912010c090501030b061801170103030905090a0e0a12030e0f0a150c02 76
    0x4001a5412681104204504640d81c0e401c3e00b500c0c20b40030b180309040090281d1164001103051052a50030344149a0702840036030305004080041001050a0310304031034092500503106c1c4098544803800009a41c01070315103100102e81c001c2c03114900c058401c03c84500311001c1010550b00c400e000b200300c0003150090002c0c60494001480d6070081d401034010381e818002910744442500000403010302923101c003610b256101008018841d90841211421001c20300d2010341880c009088031550b8101c407001c018108400c52011020716241c4070140d40b1540c1d030044c48903411841d40708601d4001c24507560601c00144080e500060194000e2041e20b04007c0d0241c5003074582010b9949040a0b4424008140d0400140018403000034607079045460203984660350b00141207140c4800c10046030005003031200c3c110310344009451140c0b00090007141700b540c4011040028000d09105a0007003010b0350b6545c41d00d009080c10103104010216214110521980f2000e8180550300c0c101402c6410090960001d07900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 844264604 1250 844263354 844263359
    0x30a060e04082a010e01091a0108031b030d05090a03030f02270a0e0702070e0919300e03210a12090807060b0f0910060e01180e040b090a020109 63
    0x20185441d000f90105403240c0e4121400c607066460841d000c40c0e9032089541d54034440e250030403600d46d01450007140c00e40100c07009075040812282c0c5134441c00d1083d20300101d1080590500820901c1500d444501d036180030025481c250307100030f4440010a508a002918003155100752036201d00c01c2e0780b2034100c0c00f0402007859184040340b1041c21041d80b20140c0c0704c5031804000500201c04a00c00e44113811aa000d441e00503e0003003451080e0030090a2214103402c070280d131403112058003007040640c0d90840072485a40c2d40360a6044400c84d00031143c00015002c455038188125000340052000f2502503003102c55013107581d0b10180400c610402107102e00d4004100c400c200c0e0388124540d42d0154a02e00c00000c0180c040d644001040e40040c0c41241c003540c48051403e100c0c038004011047d103480503600c4c1d07429072520b0700c1200703030124441c0a44014000500580d4805074402c503018281c422003045822040c0362180011841c03160115022140b8044403000194965000b0a200303603416410703190180060f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 844265854 1250 844264604 844264627
    0x8010b030c07050a080412050d030203130b0618010b0c0f060105060702010c02190e0a060b120624040b03090106061818020903060f0103020306220f170d02030a060e0408 74
    0x10b224600a0340c0fa407261845541c042640a03000303000800010b1520003041038145040c2c1c1c1440c9003406201c003494410700401c10403010100740404c2d81c940c42040744180c2e90315603000036140d55242e1a50903022840300004640c501b05840280080c1d840d210803201c018044000036660b6540c24080c83d50042c00a020b82070055019159281c5e0003403008140780c41b0481c00130800d4008250702c0d400304c000c002c98102808401c001724072174600900603031041e052410401c10b20088504901600c480d001da8103000c00300852300001c07450482101c0a910b6450398590b07072043d001040d45c01c2626140704c15441c2c1000010b5840c010358140c032425242c0319030010081e1800000c0d0500b4400c1e0900c03d0107140d000c0106107510f40c2c0c10710040b84100740c2c41d58a04015411801031502c0e00b440281100c8400c2c070080f4260f101c20901c204c0d0392020561045581e9052110707071402a1005500c4041000415408601699001c1d03170398015510680d140202045015603e45200703a6042d010760300a008010b081042d00c0307082 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 844267104 1250 844265854 844265857
    0x62307020c0f210102090d080403021801380708031f050904030f02010204051201020a030506040509101109182215020c0718020703120b03060105120a05121908010b030c 74
    0x201032a0f400142860000c50203d91000f1150b001222400030004051085103440a54090740b810100c1c69034005604140d070142c401c0e68580841260000c007510380500212104070442c41e96a00120460748451044c5000304854000740e074000c0124442c503100c80344d8080b20840402c100d50000f8081052521346032070980d92054904200d130210f5400b000089583d40398911042417454440d070005a6400c88600e006003181c0b030140415100303a081409000e8500320020b060390500e0f0200c07000180105007130b00d056038181304601d886500710300c4000100040c409082001ca00c10440168200d40c8030100720207503001608900c0b00100300d0b0351082074045100c8440d40c00781c020b20010320b0890395142e45402c0d001c0c0d035040c001c102c60010341c3c0d00011150704040e8456142c620700c0c04c00000c02d101810300000065120081401000d00500c01703070744150030440b010080b0001d00398211040d43c5031030400e81401d49140d840421413001c0c84007110170140f800c1c0d1243c50218101c40c00c100a1b282142c6a115049255 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 844268354 1250 844267104 844267159
    0x60603070e240304240501050f150702090108030a02060f1608060d061b030b0109120602250302010912050901020622050303090a0201030b060309030f0304062307020c0f 74
    0x2c02090b90800142010524019030155006405c00c0241c2c41e902c00300000c900540c2c040e00c94045061000401198036250351400c8051411942c0020103820101e4a07001d0740100b150181d80704020a000007907a81008c0000c00d00b81c5495400c0c0c2c2d80980d108003004803224025114280d2981142034014822845010696085403005100810100d07140d140d001c10b40d4620351414501210f000c24031000d468151003401781443c1e080c02c003220350b645004160150950300b501702800f15030700010146041d402c042d03600c50726100c0000308010b02c2546400c00900071b02050904903000009098005031645c021070985a040c2c80503802092903a8071024035090110030703203000c0c3d00c104a4800d15103000500a03c044d41c415036000008100b001c03076500004090300c1c0d41991144c0102410800d04c03180e0040402103800102c8000c01d15a500e0721913140101c018206001020041eaa000c5a190064a5282d60f01802a01a070342180c111400480c00c000c0303000b182d803440d80c0e07015000029445412001c41281200b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 844269604 1250 844268354 844268389
    0x311010b1c0c0503071404111603020115080d36060504030c0905040f12140c06061c21170703020a09050f03030d090602040306060305030406020f0102040e1825030b060603070e 77
    0x2042c0c9da100081c05100121801180582d44805051684002c00383c1d404000785801d8000700103285000001800c6021403003001084c0e850000c04203100e5034103002c3d00348951a100310b0715000c0143c0d0360304c000300039800a0100300c0301c448a040c40081e2012880c015180299040101018600c43c940e4401040b0710080c1c2d030f00d60610030300348042462601c201d4050f094220484000d4002490b00e201002224040c800303400e07041090303006140022441220507440054400611000100e400c407000b0384114400501e068a260b076228204801b143c0d240d00035029648040d110b00504503107840c10400d501880c650321541503070052081c0c8080901030380007421482d0180100500d03044e182d84407170081c0c41851b00151040e61000078108031241d8100714070340700394840000841c00c0500700101580e83e01d0001d0040d0b801102914076200010109004d0520401c02420300a1400041c403200d0990005152005690007090302002840c0d9081507412244a58041e68508916119074003c028074008400d00507071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 844270854 1250 844269604 844269607
    0x70314010b1f0f020a061a030c0301050c071403090a240e03061302040906060e0402010809030a360e180a0804060305040f0f08091017040311010b1c0c050307140411 72
    0x5c0c0881c03190320074411581210021240c40c090302109051402426800c0140241e24160410454203019416504010392008070230405015420700c461941c010603540a5124019020000c0e045c0310600c01990030301c0380ca0f02000c520107030010003516001102440d19405030009000100d803110110a0f51014602c018000a0010030641b00c480440d002d6402402d9200301d030405010a544e0450300b1135610007515002146040120f40c801400b15825004038a440d40b2000100003070905404212401c50031342c0808940c10559809100d02032100c00d907403640340c40ca0042040c0c0d891345000714104944e035800650942c9405d1422404900800b0014010f54104000c00b035075400052011400030400c5005082c1651039008000402420401c402c8010051019001c400c0c4076800490410652194250500c0420300390620000307030240000300c8000303902030302007007141c407800a9021403a58030a000b04034001d181922074080c9a0760301110300071486111950900030302c55182507007055000d60080c92a19 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 844272104 1250 844270854 844270873
    0xa110408161d0c070b0a0b030a0606050a08070f05100e18041a130b0a021b060a0e06011a091c08090301110a0f0509030f070314010b1f0f02 61
    0x54180700d2144400503505030740050820188124100005401808a2119030310341404149140684540c85008201c2404000020503c180c1035014192038200034060340c0080b1268a4004018403a1b80106c038840d890103540803406000010f2410301b030320307040c8282400440c2040308207c141032010321030900b08803040c070b00050661104401c2e501c01001090002106042911300002d0190200200c035101c81c16440c2044465500301d04c02592181d00107803d0116a190a14070701c021344a0480c07130700c500c1c0d2000850b46210400000340d041c801d00009208100b814445a40c142d16408203108201a4560125025494040381d400400710006d0040002c485505074191221003001d0f6a682a5000c000124094420741802e00a160301440c0c0541c90600d08001400d020703245400703201d0010204000403c070481d20743c0302080001511542001181c0c410782d507900c0c056421021800d1045000e509000e4000d8141c101041d4220502c0007403a05065071b078000403400c5800a4881c10f424007144110400d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 844273354 1250 844272104 844272119
    0x6090303091b1906080f091b28120b06121f02070b070801180c081f0302040203011e0602010c020a0210020c1509030c0109050609211504140a02090a1104 67
    0x401c3c0140300d143c4481405107040c510b4418041002409500150007401d21b660f18034082d04401407403a10200c440b25120107003120115096800c132400845010070680010420003d552404103002e4880c43d507002d241e0f035400080c840251240300005d9401d50003151030342c252404c90344800f007040c2c14081005013046e400d5200e504980d0815030b040b40100d407802006002025025000801d0400d142c0e009100903440d014008002c040010030b19140080c9c00d8443c0030301c090410018000858004009544070358456640900d0900d99250301c49500f61501c0001500c14010f004a890184040d005859000c03030580134800781d900d503941000114000c44c4409a400d07928400c12004810103039400a8864014106040c68940c0007844c02e414003090a50420959a500c81161040071043d2102429148480104800b550b4450804941d031b000f40d508401c4103000920b20140700700e0181006288505131803081540b1032601030b1000c0d4118240c030000501120042e0840690307986491141403406980303510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 844274604 1250 844273354 844273399
    0xf050f030406231b09040e120405011806020d0e04020423010212180409050a0f03030504021c020d0204090302120a1e021606110709060b070506090303091b 68
    0x30211005a03a480c00c036003c10004400d031030031418041c1c0c0a070000381000c490900c04148140380b8030512800008050a01392a1a00300c10600ca4040c01111107001484850f400380f0b4105000b0f0314001400d00010000a80440d00c1c1c8104075503081d0083d156524107a60202c0c2c0c00540340741016040740c1c003040006005114045020509841c06501c86a65010388000a081131440692204440820300c003605031030360803c10603901e0480440d000a0500250f2412034240140002c002c1c0000d02c4804810702896011341110b40310303600c00c440488442e0000580503d91007248003010f504080c0480c42a401410035500513045180680104da94105840c0702160072a800238141741c0c000360028600e0402c00c5010105942d04042c0c40c0083c241c2d10301429a04500301d11544540010444885015451840d05024020190003403140034403610b40c0b01c1d20551210760101c0310444a0748541000101d0716079000c0f0541e4098a00c07000035208110606444504101300d00b040c45900c61850700520300082c54466 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 844275854 1250 844274604 844274611
    0x11529070f06020315010302091507060e0303070c050c06040e060d0507170c0906042d0609020a030617011a1302120403110714030a082206270b0301060f050f03 70
    0x100969a450141d48005d11440280f121506041c0180b000d109103985004204030f20f40300707040c0c1c100e07110b02950420704090810031103a941180000803d2185040d0301020302440329000350122404c000070380081c03203581d03c55446068505005000031481600e001d03112403131507d00801c21075620769100c1340f45403103602415407404520350141d42d2021031800c1c40c50302e1a078845030854040180000070100c15010005422070074226060b140030401c0c1e112400c2e1b00070300c040c0180a404640300e07104210003030010700039406034500581c0001403a40b130000c030501500b40c042004902e280e24095016062203081d04224a010754656000e005a031141000543c8040c4070328065910381c0c1c128411076000605000c0d0035081300800c8010020f035407225803000140c81c0702d5641e002c1e2400b0342c0c81d245403102240f800203000c3d039840c24142c01003000401c0b03a481201180e21445404100750340c9041c0d0700c1000850580d0744110441c124052004011150190200140e80540ba0403e1854090420410307841e41d2f1086 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 844277104 1250 844275854 844275863
    0x160c1505010914100509062403040b15031c021005040c03020f0114090607060b0d0302100507110a083108010f020702010c12091511011529070f 63
    0x9100400200b080d03409030300c081d420903c060080d41d040100080b004c207a000d0042c18020b001d1600468280d403690800f942d0090f402c50b12a03841d560383e9201c500070a5200341c07000e6a4a15044005c18503140c4e0744089107036120002001458241c2000c022003040c6514904903400307500502c151142400ea0500415100d40d01c91664402031a0951040100c40c28103117524504006c800902c0c0207824101c10219005104210ba5840c0c0310354451401c0e80141060041c11a00130025108a8080680010b1180d200c600c00b920140540d80c0ca01c4c4040791107806070580200b03a91b210f03121960100d00c5280042038440c84190381c007800c988040d100c02c8040f10444402400044100500b0420b0103020f100b403403c554401c80040d1301e0a140c6800003010450254000340406141350008025030f070203514810001c249480050186260310500a007420980d01c4600545509140200b507031100400c18100c00d0f640b0b0740803103d03160f002d01d4001840e1210480385810b4091420010349010420428401358040c1c4103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 844278354 1250 844277104 844277111
    0x90f02040906060908030304061a060c010507021b0f0103020d0605150a08150a15090905070f08090a020d031b0507090b040b041a100201110d0903090f0e160c15 70
    0x1041407240468210783d10001c10404004d5003403014403408022a9007003508202c012a015284502d40c1c0c0d100171140a10301d0f4410400100c0000d04001074201034800c140f19005d0786c01e526010000b10b011403541100881c0d2012803405100340560181d8003401802d440c05d180013070140c3d107170404500b544061000340320341c1002c04141d5040c026404881641d010350f40c1c211882d80b1003088030210320307000a079028071051a450000d0440d100c5210303150890080030031000030b12150411000241c0b00051109240001030300c06400141c680e000090303518440342e4007030b080001c3e0280580f401c0310b05100885500071100740c0181c09001052007041880040d060400001401c03511210401003154444c14880b400386042c50112001c18058102c038110400c0143e61030b01750006482c408034018000c00d44081c0280b0781c040b9068015103c140d0024105030711944032181d045481d0b503085030000f501807040e000010b82520008003281c84111008142c08401e0900500130800340d0f880b1100886442c91005a040d41c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 844279604 1250 844278354 844278359
    0xf12060609050f06031011091003380d171317161202150306010207030602070c030c0608220f02090a0f061208220b07060204030302061e040f0804090f0204 68
    0x401b0700c071109a05282800405c46010038200260b0240a0440307007600c2500181d461079480384c080d40240762004140c2128408150700d404c0503540852413451807080c02c01031130311140d4140c00c1c6041403c00c5541c2180d5806410400c024088079a0340c0200c00065207074400000014403a9030f0b2644001810180801400300490260390895151403030f0380c41005020300c00002e050250705c503214205480c800700c4010780d91b2030b503070b1a005070b14101099200801030b83c40019078009004260080c2400e892055060009a6030b650504848080003507070a0f09604600c00b00031803560f24803038511500741e4422242844010714603000200e40c40d500300c0e0342c01011a00c2d01000400c0814510426000d4a8460319080c00c180241d15401c0b05401001141e100800031405808402e80703011410130b00409044c0e80b0b4983d01d50780303854914060741091104a001d8441c50012500900d8440003034030071080d4000101d03441d036070741e510307400f100b0203080c2002d84840c3c80411010481c186207019200302004242400741ea03842c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 844280854 1250 844279604 844279609
    0x705100c02010524040507090f09020408190b151c11120d05180d0c03030207031208150d0f050106060314060915010810050a090b01180f12060609050f06 67
    0xf000189180282440b40d15031061131801880d11108a80081d140015650b0301c0d034806a07109182030b04402503a1040320300c00906070205030010700a0320361810503a0110840c111956003182c441c101c0050624180301c001070b01040c40c0d0044841002c03402025a005a4003603102c40070800d0104106450f004000c08403890542802e524083c900e00c4030900802c45c13121903001c018228000c00c2407800038002c0540b00c0321215a0f034286802c2d009a04800e00060340c07030b524640651f40f1041480121303a04a03242c620b015006003d07101d014858a40308090001440c440c030100302e503210600340c0455810100841403c00315074244176104c003400d01c6880024042c0700c103d030f80c04d01001d40204510303c190002c900700310769541c002103808800d440a0a01c0109a1a00c2180c2030f00740717030305410964006041c480c1c00101c08040d0703040020540381c00c0e04d0f041e40b4070205d0344080e0400c0c01103005c2c2c03c500ba045503a0801c54521811013048a040c01410001001622603c142d0143d0301d003920103000080c0c02c4001d002561 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 844282104 1250 844280854 844280861
    0x90105090a020603070c03030914030c070608060619020a0f0b0601090b070503180319030e040b04020712080c0f0c060402011404060219031707030903021b21030705100c0201 76
    0x44444000d000d980059800070b00c0c144801404e02c81040080d00c1b00d8400c0500a4100c207500ca6481204110791100c61410340c0d07681e4011040703151542c440d6000c009415400f0b002d20b5402001d025224510380001e0b60740800820104400f205d045214980481d40072500424515821500c141418030003410410b0004210703241e541c1040100c00020000c4000080340001150107840d451011520b07003142c0900001d041c902e41b55000c0c804c1850214400003050b2340710340003400e9030034200c0303041142c0c003452000d00040303000342c400041c02101d0542e070808120740102c501720b0707100403a800d01b1894031802c1881da0182d600180003103031695008405001c115038001074450150791807188603078102450100025960203055040855803900038044100f8035218402d95600ba114040d021980c0f4100f480c401401401d58000a42c0140685400e0118440b61780d105d860580000401048a0503e0a00d0050000d403c403204403c443c8020050100000c009210b01c1488108030440010105400c4402a003503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 844283354 1250 844282104 844282111
    0x30a02101109060712020a14010213150c110406180f1409060a090503070605131a01060e040f0b0301060b0d18031407020a0e100816050a1503020d02030c03090105 71
    0x1101e105102c2d440031a264401610305498000030702441e00c0e800e289090741803d088281c050142503031400c0e02071031000d0540081100680000168a805698211189154034461250400180c0c1d036102100440c00ca00c035654002040204001115555480301d118902e40900720b400da03040d1182c0301c0c16071103100c0d4071600305610400420401d151400912080d10f07420024000c8035090350b618180410712a08005680d078040d40300c00204a1814486420003042100c030100301c40c03100001ca9901400110051140d0481e80c0b103807034100302c000904003044081e0a4640380c00c8825a40e4455901040d5424012040140981800b0559408444107640c0984035410303e046000d4000403c001e0009611a20b401c1886c0b0403000c4443c0c48000900c000340000040798054402c002e0540d0501c0421403848920700101c40300d075401c603902610f1140420746421141d02c11198014141c1104015100c03040300402c034000001c1c5001450325040d0741e041d4040380c00c2501e035020101c101004010319080f00b440354580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 844284604 1250 844283354 844283381
    0xf0c060e011509272301060504110909060429030a0209070e010807090b0304030c150509072303070501230c010207020a0503010b101b020301090b060a0e070509061b030a0210 76
    0xa1080c607a101c1803103a07407000760550510100c10040000240c5c1c207600c034101404000300284560801c100541c89942c00503440d40e403251001401040252410b4400c0003c0004400c0454000f0040d88003c00f04000d405003400e07805008215440c40141c0d500704005200f118951151031104e5042d8000502801004141700140541c80b64140840d560010542c2e50103a814039182444100c0c91411903080e20303450904540240c01e01051000600c004070340d4405450003407002050300c0380000034407210800c0c04400c954041c2c01040c1c3c03d1005500ca03030400303050300310402e040d80035440e1a0000016242e07c101101e2035265400324500c070840c41c6c000e205c0402400210000d100c03045440d0300255030500d0801045d4207001a04ca0992050800c1c80b00f8608250b030001d008000740f84003802c01c010711744022200b651080c80c0b141c401280d640d058040d04c601501d0142d0344c85081c2031100301405170a80c444015000201c0500090b42104003040005107103803d0a90701074007050325055200815903007603618a80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 844285854 1250 844284604 844284671
    0x3021c0308010f0e0118020c0d09060f05040b0324030a0323190c1e05010609060b13030b0406060323150105030a03030902130c05030f01060f0c060e011509 68
    0x100c0c640304c6000040c1510b490010301c9051503040c106060080c800c40e500c5117403d0040000003591aa0840c0c092011546592142516210052000c8885200e01e02802c00155800d10114114540c1c2010381084a50b111910f030015004120029203880840801100014884c20700404c01c0c08201c0000c2d52028040ca85d00307400d0140c0c1d640b00d411094003216080c01001b2045513080144007401e0404600c03c4a0790a94840c100410f0038828040d02c45401000c91260800d54005003000000c03003219507455102c019900300504554500c3c1100d42d0140046d26156203c0314040003203610300380064140c50b8a13a00c0c044940100d400d049040c8452101d07460810703981c8500422031620301040b84045c03694149400580f114680c4006410324004002070b010041c58402c09104698010000710702460040015403030503a81d6581c101d40306076000c040000055070183c0aa0b00003a0b40b038009200c041034100000c030301d000e1200c880282801e156445240d20300e4550319107014250020841c00d12251301d81e040319 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 844287104 1250 844285854 844285859
    0x90118030801030209060a0b0d0606030518030f1303020604090509060906040209010b0904020c0d051c0b010f1202191e0206010302031c050c06090c0915010e1002010603021c0308010f 80
    0x1400d4001d051102034010488080007558599400440d10301504104551544071011224203030024055409042d020070b00d0800490a500103094100d03164440c00d02c029458022003540f840003035003001d80c5812000c2c034007000200040c1d481030054006484c800c2c8000485241a09409140c200084d10240d002e4002da0140b0015844040043c2d0655140348800c3d9500c10074000840c0c001d01c10944c1c420098001d400c01d01242030b034032100034900d03d050360510740d0701003680b072602408644540110701d0100301c800300c20075200340c040c5150038040011210010b0401102c80f002204650354102008005282c0c1c12544d031000d0340b69110202400d04502c02050550b045038042591401d22540300e20200311580c1403070402c0c42c468022100d0006c0c1c40302c180e40850034003040c2195100410a80c0921034a01000090140d081001451004001c165a24121560300c00c0c00e103c100b1080003000d2007103540301c13100440503072201804040e9082c2c5407086c0c0503000d10503003002002448180c000310811001602c08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 844288354 1250 844287104 844287107
    0x13050f1003020306030c09010e011e060522030501090b0109180f06181a04260a0e2404150341011d1005031b0307030c0e09011803 57
    0x6044580c155007030042c1d6948400700002e2818190200301031b808429000080790304030502d00c0e00d504031808440401c000100f140322b600b81c4c0c50a68001c0e040011028445010981c51801040000b4850b80c1a04020181c071707501c42900392003d100d001d8030000712003001008031540c0d07481030714042c84000d0284445058241c0e5410641c2d8800078001d442d42c0e8403503007680603030031910762007000f025840303050902040b41c2040801c42144085405895070a000701422031000c03c9502c80001150343c01d507071070f440c010700c40b40c094603400030b11480340340c0113200480001d81280910f041c481454003268059500c45140807110114103102c3c0444908146c20490001d01c0114903510103a07105110981182400715480400810241442c01070704404451500010380b00c84c201000303802901050b5640700d03041d034412024100d00355403481202c1e00355000302c1052146c25030004001c188203800505480149a07640c17107418a00c445034100c0a50104008240081c3c46424420000b1100c110b805607a5480c40b075450 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 844289604 1250 844288354 844288369
    0x102030a1209060e030412050c010507020a27020d1a040905070314030f0d020a0f140a1214012408070e0904052a21071e1502010213050f 60
    0x1040304480e03180c401903410845039800c0b02901d1004134049a880c0da6403071a09801010300a034046e101e43c0100201700c005035201384210b9680340e4014021a078201d28101d04448410130312194010704401d217200c2a005040c244c0000d1000c010180400b141490701d4448030500d2182d82d1844903c26803030281d034a40001ea021814404072900211a009002c548480160a5101d6100c0701485c2ca800040c00c0c11042e42c40e5409003007182c0305a50303111504c0c00c3d8070509541a100f100401c0d08602d00030710000450500c00d5228a0002020300404140304e10280201d9120740d400707800c2030a16606901c03104008403d0403004030803955032032801c09810b00785454041c000c80c00403030700280600451400101400b008001202c50700818908002d59030003000342600d5400110a8018070030389814241119610b0f00411180c03407504544050404c152404070308102d05c000c0040d00d040400c0b05101d0000390741c001e1400d0342a1540c0b45400142e03a0f4020a036100302d18508540060740325a03408196149161120322 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 844290854 1250 844289604 844289627
    0x302132d2303030403080408010906113609150306070f0801031b05060711030706020c010e0f0f0603010b03010602120a0e100207170a02121f150b0403200102030a 71
    0x400c040075030407000300802c3c254031036a0806408820000780014148005520400d0011b0060030300f01305040302200b52030b00901c2603050f81c01481c0780c81c0c800b0743c0451114400030800c0d0a44420095600b444010102e0b540700340c11103980122800381d00d8001000d05040c0085640081549000c410741d1710510170151400c0018000680046046085800ca0008a25a04000d0700c00100604d4480c406c6d85088207107007400c102628007900400c50000b40d202e000046258911a05031035082d100421803040c002044074202d046940918503078000c02303e0b91500d00007140601030354664190360b90705110020f40362410b021107000c04401c0801c4a0811198444410858900120ba03136a1904895010880ca08a00360700b12000302d280540800c1c99039100007802031a500c0c82918080c049a580380100e40d00c0c1c10311103484d0000c0180013200e070140041158043e80300781c81e4890114140603154954030310383d41c0050300b0881e1a51400b80349a003c0d450030141c03d849803c024030040d0715010280070000c02041142 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 844292104 1250 844290854 844290899
    0x510180b030702150c0a090506030114040207060216150b031204120c090c0c020414040c0510020307170a0305130302120d02070f08030f2211010302132d 67
    0x210108091610a2100001340b002c00d01c1e0340c40d8a4200a0900d09240e0700080c14900881e403001d07400034450802e001078038102c0d600140000c01e014a620140400f0350301c4100200ca4081e420000c1c072171101816032103a90300c0c60290103801c202c0000c0410b60011600b600b05041d20030307444000e1485c00c03d00c010003164181c49a0155401c4004c542d46070020020725a80c21030f5000d03a084c005240080755105c0c0c040110b0358002c44d002c2c8141c07000751890007901c44c404d8401902104068030148500d0800c440c1c40014091984100c1c1e2a1003165100c85803030b041050a2030101c45000071f01c104134540d050141c01d8200f040303e0700807000300171669400395070340c041c00f10b020103400f03804901d088080c46140e060302e911a8000160200190b00d500d03142950782e10880c0c0032844003009801007240d07821445440300e84900c0c0c0550300180d00c10b1544a00e00da407140051003e04240c2c0811901c00d44810080300702000340344500c1484503101c80540c0045080124110b101000f01c3c0a5070b0400682c0c26012009501c0b8009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 844293354 1250 844292104 844292107
    0x31b050d031d011a13060f051207081207060e0f1c090329070206010308120c0d0e0106050108010518011a0909180d111b04020d0c090510180b 62
    0x101d0710620075600103460180b8040d442e091911040c41081c007041042d414007280e9070072454841250341d00803520301340140ca840388010070080c071540c03c04d214a454041d81c00d0013180c0c800342d45d4801d11850b141c0c00d44401c541d040c4005c00e222040012900482c0030310a4000007905190b02c406100c1d85e81c07015609080350b05080c030034542e4141140104021405150003503c250b102002aa0300081c3c0750302c5035826014000c40d04000514518400309000d41030320b511080a610b8411060b031655040600035185040340c40c810828140000715030300c20000c60318034841c004603426181100142c03030460141d0156000324803d00d00c0450280d0500341003419100060440440c1c06801203411001c0e01401030030b07581041c0c10000380700c82c0c98001c0c03103000518200c1e0030448002c0380007513404503002400605400000d40c0304d02509840d2400c900070780d402c5c98101030001400c103444915200d00350b13082c29450a001c210643c006100340d0800b01e0f2403030403681c218204100302e0001d080c1c00b0f9442c0340d00c1e4481c2160700d000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 844294604 1250 844293354 844293371
    0xf11040602031e04181d0a021819020c15010608010b07021c020301050907090e0307120503091f0902030c0f09011505070803070f020d0305010e0c13030c0b07031b050d03 74
    0x6003c425540540103c0840303411910540b025400142480c10b607201c0003e0b1500c0c43c04004040016000420f540e0140a1003100400c0c07104584400703034094000759580c107848901028000b80ca1010b86078134880c01e002400b810320003a4030701c5244141130704900c0402981c40014050300000324101c514195043d10080e80e00007940020020749141008000c3d419420b04040c0300945500154400550314485400c0003000500901551349116200c0700509c00e40c6402010507440740504040c6501810340010f64071000456a4014040030315070044000c80f40e900d01035081035080801c14010030840076119111a0300da00c01c00146110720521881c1c0880c090724441c40b901030f11400540b103009501c1018142c4900703010700301a01c0d101840340754078014401d5001c80043c1324401d0043c24100c400904414040d80c898220300c1d0000d60168035520b8218210f031f800040003403044400d60004151812035151a040d251600070040c15024030149110044001d001001c1440412100885a000d040010b001d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 844295854 1250 844294604 844294657
    0x60c070305100e07060503070e01031d0d020d1404030f020402070f1433010510050705121e25030e040914010509010e060f06031608010f1104060203 65
    0x106680006140e40030301c8288408401d20381e0011010800d128040d00e401e1030322050304a03464001101e032600010200a00603106501990225100302104512452070810760002113150212003000300c1c005074000a40b07102e060350f00249401901c620090000d240034510f0312090514443c41030041d01c29680080c0741030400c44400c500d1000250b2024480006280c40c0000a484503040041140011200e4024461f10340070360b000040d501001032400d0610741d0070603090100300024103460909000c4204075007004100100040e5088554095466a80d906140c48014007070f05000060748120380d0900c0101214074034043c407104440d501034100c20b6031043d03e0a08455000440040c42c0e08146022405414481c031214003418110650000b44580d0f04d840058608803020107107010039a030171890100700e4615081c0b01103174009000070211000044080b4402c001c441a6511440c1242c1d51800410380e0651303640034050121400022031414289032a42c041e44038821550210201075510800c9101003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 844297104 1250 844295854 844295863
    0x302011715030618010605090606070b06040e12090f090f0411061b0307030e01091d06040209040c0221040f0905091608010b01140310030b09010b180106111605060c 72
    0x7103030000d00b02c030002d09140045030718044007000601e0a41d42003007004102d900300119500e01401000c0c110703615180700b0f500c4195440101500e040da00640350380d14001180010401d0903842040c2015003940d41c8101e0b0100300d00444d0010015001d007580a04000065420041d0710381d0294100c1055500b919146001074514412502c00c1207800f0400c41c0b081c401500004047e01d080b51080e19000d48030700c2c0240040d50b116100748284203c1d400d8020003100e50b26207108071290490005407015013000d002000260507109121860801a030000c40070307500c422100b1b1421000050b04801c0755140604105800403158000e005a216090b1039101061010380100117450035115403052104141da1070b10440c034041d1250740201030002d440400c06c108641000021039016444903851010402c2c95a5680e80c440d40d4000d01c1e495540d566034140c403810381c0312107840c264100302152840c4c40640c1000301c00741140d1000b203047c22142d40a0503031000840b21080184081d608101c810644410039584500d140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 844298354 1250 844297104 844297141
    0x170a060b030c03070f021c050d110403061b0e03070e13050a03080603070902190c030504120605071416110a0902220605120a11070b090c130603020117 66
    0x195001003004401590b490195000305070950701c4082a8500100032079581c00304504032200d4410621030380b50743d00e01640040050b01340b1141c0200d44001d01c00c44060032500301d40e10590b0110b8940c4480124131281c10340703200081c0c1c0c1c0d5042501e910b008943c0880c1d036483c480d028059101048e40c022403445038184950f4004070754000304544c02042c65160040ca40310098941c4d0780248075104000c04d0f00c0900780283c9072549041c5661803506245620201c034804070601054051080c20080031404010544000010600664003c255400e010307000528008040320100400b4006100603007440c03200b922498401600030b03002c3d0547c0315130300c0c0014038107460590001442510001c0c810903c4c0c4044420412109015041110720a85e241d609071001d1081c04a4010703201006400100c3e01561a4481c02e41615a0b100c100c0c01c1080303550300e4411800068450401d80e600c500d128010502d0001c40c004400340d4041014001c0d18516400648101d1b0342201101503d104000002c0081c0705c42d030b805025 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 844299604 1250 844298354 844298369
    0x81204090218130606030b010f080f060a0f1d0604090809090a0b0301020705010b0307080706200c060403420519090804090f0204060c030e12010617150403170a06 71
    0x901032680070f5260020005032040b800031038100b4841141c1c6601807025481c894010361500384c8641d07540141c00c0f9004200400e000e6000118000200300c0c1070a1500d0040035104c0b585181561181c00344000d40810401800e4900c21410700001c030001580c80025101036540a44900c00130351500180003000d40aa088107039010343c40400c120040c020150010a03910005406132042d20341c48030b0205454807602c0c0552030105d00d42e6010150b9901c02a2041017612210380181ca03c00d6200c4e0000600f140d100b68416201907110036040239461000f50030720004120224481c02d400001032400700888400c501e030010309a41e039103000440d090071003010101d144d00242c408208042d07282c03402d80f105400901810028510781007210a1000661080b81d00783d070303110b86941c84020079681d4100c031b0031002040038641041c5405014040040240a00c1002c0d1100792480403114440c00c60051404080c03500c005c111200c1c52007444003098010301418001c1c0f48800e4045825941c204450028080f298005407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 844300854 1250 844299604 844299619
    0x10c06050c13090e21070606030c05011808120901030b03100212070801081b010203120702012004030f020904171204110f030705100e060705010c09081204090218 71
    0x40550781507001420100c4080481d5588180ca9260364021585026400101c44e0312014095030b18480b00c020034590806040c499070300e08522551620260752072a0b004862441030303040180201e6130041495115883c000380b0f012241ca1500d020a070356544070001c1043ca241001807020050791094110461888015048803d02c44124240c3c40095110480301c428550010f008100303524819040c0c10304840742d81c2c008190891015a11250840c5c0d041d0505055102c100300c00540c02c00c036402c403a40324501540000a0241d101c45491254218441e00c6485500b010081400001c4421080f49a0789805603080d25a40d510792410072902c40c05040360050b02800401e0b29107003000034001d80f41c0b04520603c200100300c02100d041c00152500741c00c00d142d15421016050129081500c0003004a07032503440d040450000040c0840c1103940070078815a00d0340d4548400140c0190000d28500c001e010300030052000021b038000c4c2d40e50300e0180340150700d01c003900040c0844185000000a0380c0c0c07014010840c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 844302104 1250 844300854 844300861
    0x906160b0106180f09180f03020c0a050118171501030f021e061605010b1903050d050309030a0c03020c040c080a0f06051c061b02030c06090712080702010c0605 70
    0x85400e424031840300052004448828200320162561040341d1125803500446414040c0080282c0401e21a041c0412002603402011464040c100d0710810b0094001d045002c80303400c280000050242c1010341031040050180c0c0340c400f5211080e03422140c42c1880440003420300c0b650b4505104608a50b14034400d00c40d00040b041c0921400c282910750b1084842c0e46100c14080d61516086040c0d0740705660000042c01003119400c4059030141619200b50000620710040340d000a503900d1507411910341d0b50120003420300130010100820200c103041c83c18928298500344031081d0382c0740301c3e0140c06020404070b0a10401010f000300540600307040020010304c25003607400d80040c1103070000c5800500007130802c0c844801c03000d0103100342e00540740064001815050040d880c0e802842401e0f004035901035503403087d405148907070301c0f1100300f90b0a20b0b4041e40c2d46003c6000a90b16040c405040c0610580062104001d220340c075920240302e095000a0301500c1d0000b40c001a940d100000e1805040c560502d400c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 844303354 1250 844302104 844302113
    0x1c080414100512040204090c081e030c12130b0406050306041802030d051e0f0a080f1314010b04090c0810181b080114180303100308090616 61
    0x2820580e034401115001041400040008108040c40038401240c0c04200703400c001800754100c00d90060000e070000c0b401e00401d13034031600b84c0c0c465584445504d400980b4004141060030307001481c1050140021401c0c08852a1072503111072800140e03050300c10001491045454445c0d58090003482004009900c503651450080c0140e401141d0003441f5501e00b441c107070f000c01004001480b103e40c029004241d802c5900909a4541d4407a00b105401140300300146d81c0d40740302c2e100085c521849000c403a1030f02c8242c925006425400d0103800000200c245070100310030000c0800c101841150800c900075549150050554014001d981816406c5410b10814005203e41000d03c1e8040358007035812145251a99180c850841d8100200401c1030040300139400082400040070501c0c4991540e09000841c0c0d48092031800c6841001c4030158502014041201c070030405020081402e03500d1020b1491441d050701c004a00b899a40001000c1c41030201b580c0c880e90712aa8140d076400048a8070300c8000050b44e092 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 844304604 1250 844303354 844303357
    0x609161e0305070807180b0d02091201020414030d02031210030f0b0f090106050114090f18100e01030201050316090b0a090311040b010507061a04020f0304020f011d040b1c08 76
    0x364000844c00d0000442d00da148102806426068003204900d0601d08055031588140e202e0440741d14207540a01102c034150750307800351014085030418001641c55144c007181104000400b41014402c0d0132904403201e045402000300c95010481c40c404881550301d00360000e800e801140c001500f221000e600001c02c020b840e049050285d03104030341c568015511076818a003030341c146005003400220700034407945408422101034941010000c20702c136200b2123100d0100b0385480003816815001c40750002480b209019025070103005d8103102141d07401035815900041c1c442e2101400590036468023414400c00c0d1031245e002d04000d451210461390341c41000e40b0b00140120083d00041d2412842c2d0326503480346203032510070382c0d41c0c1d08410385405080c0103940c1c03a07600081044030352401c464401c0401408060751248000e0000c80c04000b50191a81868010b10240e48201d031005418480840c0d203410600c4110003c40d081c2a004480101c1c3c09602038007c1481c904100350088041e0140a07d10f04c01c0105900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 844305854 1250 844304604 844304611
    0x42f0d0617060f1501050c071a1809040b0f0a091202011401080a050631081801031a0607050307080706060503162301230316080609161e0305 62
    0x74100c0d4102c3e10364081d1452400026194000c5040307503100344200e075502035005400185021010b075030500ba40d41c0d0606502d81794060010480250020313401992031100c4104c0180400d0642d131800341c504e02560703031460064010b48422000241c1800103803050405400083c2001c0e4081c4c041c00e0703244981c55010340039084141c1c102e035120b410ba400104042c440080d07101c56494020000301600e88980781c28003038580391040614242100714000c50346111016000002c0180714803602c540d07900080d50302c60003100e40445424105810210503200102104440c200c95a030704179200e40e600c19207454003518501c166103008000c0705001c01c036031080c00f1003507020404a83c17041d4207030703240c00011036040c4441d91108d01030140d41102e64541c4212040030521643c8202e0b8040c10885400001d500c0d0030030b0310314000c540589101000001b040501c83e0540201c8450601c0c2d0304100240307040c4640040d2101a0082c40c01c501c0c1180825151506c2d44514503410080070800f003049040c41c1c40b000c00501610b0101c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 844307104 1250 844305854 844305899
    0x12031b010c09050d050c010f1206030807020a150c080901090816050301050112050a1b0509101818080d0204050d050708121602090c1c06050f042f0d06 66
    0x41c0300003e041c2032507019001034680c0940900b000614420044d15113000341c0c201a4100310080025202005580c850075000c0d5005540317141d168445403040048440c07450704640c0b60942141c00407010250080c144215159100d180c0c1c640303444080e00100c1d6a00040da10051681c46038284d800c50003a00070390a1416500141c00070b0106a0300c510000c5500910b6031340051195005000a50105203200a09684116488e940f9042ca82e503990000f072044600b5a250301c413000c40d1120400010809101002101d0b003500700a101ca03c403015110109003081d80b030054a15000000c3d4040001d00a5040390050000104150041046818510750310b0303060b070040f14018803c40c000001181d000c44e069580180c480c481d0000c8200c81d5509000707910318040c10010340241d0034090407500c2c007141c0008010000510b003000401c2d030b20340010800d5030344e506140140554500380c1d0b100c41c00a950340c2c600d4044803102400c10204021203c0c00344092203603c103010341803031030001c001c60301100d0300c1c1c555030346071a00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 844308354 1250 844307104 844307117
    0x6170a111b010f0903090b0d0f0501060206060405100803072003010e03180618060706090605070c020109050f03032203051b090612030307030b0105070605090d020708061512031b010c 80
    0x8200f2208030f844800001e004aa03c1e00705c10005001c03010000d1025001401c404905583e0180c0103000f80c1da4280c00120260700700804014081c14980b19455020b41e285007158500c6180940c510785a20131158050810001f00d540b004280d070b402c3c0b8142191300000360081158042042d02c0310748a0700b0070304506500d4038a11039580002d103480c6013565000200e140100d44066181400c100007a482180105c410036140c0c0d4240012510521410b4466002522018070044c8144001031081c002500100d1241c80301ca00d48941ca40c80010661710004900c003415081c4200c01404500c00b1000b0b80e100a0140c8140204040c1c100c0f20b8044000d00c1180a6400461a0b03c0741420400040400842e0501c80d41c030030310000b1405071080c0c10050030190181421481e0140f80d850b11000d541e401c0758110400e504c20401c034044264100b02042c01800740c00f0191403941040c0b14440314180003814058032503914801703c000320447c14012103840304d288201c142003082880c1000c601901c905a408804500e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 844309604 1250 844308354 844308371
    0x405090108060f01121b03140106091b0f02160603061a0a020c012604050a0302070501021207061e2415080a0903030212040b0609060a06170a111b01 65
    0x140055000e0243c155040c40300f40703c0e03080c60203070100303821180e0064030181e000000c4151180c040381c409001841c0101c0440408200b80e8002c5401d440d440d1307102a9181d4a0034299a0b40494400c00c00d15003410340e86031041c07003081c454404030306d04012103450754000c10140d600000e065030944e01600c112841203041d000303455000805615640038940800c0050b0b0810103640c0320b10361040711501a420340c1c200315043c0741190700b4608403100400700c0301220607911030061001499010031110004107001d20040c00782030135034044480385002c0d19200412854503418400394020009811180e0203036500c1c420000040b180001c2c0d14044021031221942c0003000b6000b081c603c403032094100340c41c64541c40d0409240c031680f43c04001445818000d800b0035600b40141020355002c0481e980c004c40c001c02c09407400d41812030030001038000c054111442240415010041d0541021215201c001028242c8896a440c111801d002e8500b50b900c4031100d1000094010f4000d282411001003106001c008012609 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 844310854 1250 844309604 844309619
    0x60608060c031f08150c0c030d0209090f1012150c2606031209060405030f160b030f040f150615020c0d03090e0405010b03010c050304110904020f060a0c020904030504050901 76
    0x14083c0990113598008144c4003c0400d1164000346d0030041c0e1030b000b1490500224606803d540041151842e4103070001080c4406107001c200282d08514126a00c0d440ca08000b030414890051501c9a100000942d04ca22020701541c406427060440d900f80e8180f1100e0050b00c40244a48060091114a40400707003800b10802c0003011190b21828015004120484202c1402c000c15009085942c0c0e0000c0c00708070201d003944050000d185100200001402030703003840000302c08060507980010340b107288140708110f0401000703c001900f154019900f412510218100240c400130980308140c10141040380004000c1c500060705003a031a00c6509450440080000300007003400103400103400220320074024402c01b80450883d039040741c829400019069950000310b401d440c034a10072000800c0700032007048103200d042c0303113901c03080c06c4101d44102344c52a0690000d100301803102281405482c1c046a07920b20140500d004d40c14250b0001c01102e40b40c609840c000304503500078018240142d01540c000603500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 844312104 1250 844310854 844310911
    0x302181e0105011d0a1503052707030b1302090910060b131e03060c0e0109091422050105090a2d0f020a03061401090605012307060608060c03 62
    0xc4005035a81e801d074004da941e0094212084210300756002c45803020000e81960307101420b0f5090102c68401256502c0c1a07050303110b40030031030185018511907401080c60f16001c080f4030502901e5010030002d641c0d80301d07883d1082c4070158000c0b00a401c092608248030a85c0b0000880c14481d0644400a01c01c2c1920387c00102514004d26074100c2400ca6840005d02000b040c1e41020302058024024030750080303039680c071840207640d000c10605010540400180e50035590100302c032009000380c5c000c20b000c0e07000244520f0300c064400611240c40400c0c100c40c000801e24040c6c21240b1000d410100a114a0401c011074585507203202c60201c4954100d00c145250002005a45641d00d00350240d03800703216090f507261000d405103642012030348982028804400509548242d41590720048050b401c01c0d81031030781c0c0c10103d403041d400c500d040c0240c01c24101c2c140e0481f901c07030365200800e0800b0b007901c41344c50389004000b8020726040080140a10f03030804c245201c0803400346110b08000400c080d0712100f03054068404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 844313354 1250 844312104 844312109
    0xc0c0f0714061201090e010b030a1203061d1803090d050705040b0409080412080913090308093403020a0303170c0f0f03460b22060302181e01 62
    0x183c0390b00001040840d10300d81c0300700c000c0d0045100218601c2e0060000900b40041c268040311440f20007001d12101c00d6141c41141c0151845130600141c0d44680100e41007240402011a81d0300c040401c07110386d85070401d0054440d83c072805880d07101c1c0701115103400da0b101e02d10342c0101d6004a140c0840300c10030b41740600510b1002c0703404c25042c40c6010f00701040c02c007180c151041d043c2c58414082006960076250840034100d02c2c055550005429811460700600701403010300301c02c100754041241a2400f40b540c0b01e8100b000c1e1640c0300c14508603c42d01d90042030000031a0710107036111072400383c00800d040d000340680d40c481c4200c00c1c0100725070fa6800201f100da406003200103107200a0900413091130902c80b41c011074001440c03c4c401c9903100056800e121a1020080ba03c0380e10b66048054403e515568144c064030f21000740c8400d000340d180c4c610100e0500c14010160700030616000c0c031b43c158803440c0d960100c8003840e0050001002c20921001021009005907100c00b1161226014002d0b442d80d52030ba414103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 844314604 1250 844313354 844313377
    0x22b0c09061409011a0d02120a0609180302060105100905090406060e180a0314130b04050f04021207050919080d2607080c0904050112050d09030f0303050c0c0f071406 73
    0x1a5440e81e041703000540e0b0400c40d14280419420801c83e44030040e21000c1c10310a480c1403c000c110641841d1881098450819140c10310240302860940029000704565054500644006a0812610104403004441640056007010b15035060106101c001d0304007a050700c0381c031524003403952600701c00f1903400c07101c01e546204960445407071400001c1c42040101c40711009500320030b0610301820b04235100c9805a6201c580c0402d0300081c10416400c00c01d001d580c00c00011582181400302e68101740c000320354001c18850800100103407104c02a502c030400c620110701d85510040100c0e8565001c00e40d07407040f0700b4201d40403400078144e008074040000200414012107811020103900c8894050b505c0000107031124840c1348040c025481a501d0300c1c80741a008141c8406500c01032012400c02c5810016010f042200300100b004040c00816250140c0d20b10007681450009080d81d201080080280964403035003d0500450359106e0f031113a00002c0071020b4507090410b10034111a00340800c0010710038840e04c005d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 844315854 1250 844314604 844314629
    0xc09070207090209010e04020d09050d09050306010311030f1621081603021e10060801020306031218040903230a1209050721050613022b0c0906140901 66
    0x10088083d000390644650604046510040b600c0003c1d0598000020b01c0e50b04583d1910100d080c002c04000310711128a0508042d5041e0f420040400d403900014080906107101440d103c2c051a202044401e445009400c2541d107103041d8514020a021b0052151240386000d4030380400001c401c48440074908c45d84540c02c00d203000003801c0b10740810f0400c08429429405a03201c0300010356200c00540403441a01d0024002c101c0e10f60140d4000c6800740c0d003011600340c0c03040c000c1001c20b4500241c00c6224550b01e821a80e19003000c58594000c5030403208240350810705080e0014105504180021014500f04032624160090303154090018021841a6400516142c0d620104403900e50b2169003000e01130701c03c1e503101a4aa28011414601c00c05014900054021051042c880180300803034004056050503207241d17015030001141e04031401c0b00502144010a040d10b6443d8002e03c0010701254082288469182d8400032030005007660b00c240c1d06010780842001080f8604036041038161415140082d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 844317104 1250 844315854 844315859
    0x12031905010b03102d080d180531060b03040618111012020a0e100201111209031204030302270d060510090203100302041b1e03060306050901020307020c09070207 71
    0x1062484404550421501d0175031802c41c1101c0c8106a031340054101c1704000d01100b910801d0090694410b4060904d6942840d0310512007a43c50b407171040034200508581c000c030102c0104600d59004a0540fa1035030152900c200041c0a03155000610300c142c1c007555080151160781018622000720114000740f5101c0d140c910b0315007924010410241ea001d00740342c07079021848109881800c0707174884011240803400f100c2d10000286040c1113014000b404503c002d0010f042c81d98040402c0d40100c1c50840c0d07085507500001220000d0030000e0312205070b82e01a0984c1d007414903050140003075120001d10700780462490f0b0220000c02603040c403641c405001810782c08400d6485c1d2148401004c000d40b0500007036260350000980303c006c50014600800d480d0000700340301803031441000100c4103044401120f0a081740c035594205078000109129400742c0f01c0c14030a088050803021002064150801013881e8584010b001141005601071403040800d5001c5480d150a824100030941d4000c0b20004016071050b81d09 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 844318354 1250 844317104 844317119
    0xc051612141207081503100914120a0e0d0812190b060d270b0f1e04021014040902091504051e191203231b12031905010b0310 55
    0x5980e100c040080c0e40d00205916000080c2000d00c04a407e00709651100800c1d030a000c407150b04040070a8844004107800300c4c418a502083c2d008001120050000c40300021140d51604803880c0b4840d43c2c01100345945699071410309035a100c003642c0c8a4038903403040d40344e011a40c03180e100700c15400d000207002c03600b8044400c146201610303444441e0404030f4100282d40d881ca220200b851110280300f60700c00302103864000300e10050001c0007499200804000c04644101d500310003900d070307042601503a4429640f08404002c3d50303c01140100e0641030030002400044500b25070340988500c1c0130480e10403030a241803450609480c015070289a9111008110450100102040d02c94000c03101030406900b00e202100e0346840031600c2d41c410220301a00384070340020150f110440c100d804401c0c3c200540d2458115a841d0000e02400c8941c4a0152402d48210f08240040240c2c007240103e8181c03880d660300e02154050326003843c200d150700401c1c1c1031000201b0070001810070f0320b10480c2121880110103141124 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 844319604 1250 844318354 844318367
    0x30d020d0608010216030e040c090302090901111b07050a0b0412050f010f0b031515010f031401090c08101a031512060106020f03030105060301090c051612141207 71
    0x806050396501d1600003000c810078000b4221401003074010700d102c140346041c0030704803041440055119034035100c00041446c0e000f2400c582a0b030b8050341d19400c650750300000310740104250320040c042d070880810b945860040341890162950000016075017050f03514024055001e680c0c0c01400000070091000380300c0080c0c0503007605001c43c0210119021511158003460031580071444540e0001c0c0c6903003c1c0461803c0810140030040c209000011662600d107500002800c00058014104607035100c02685152080e08400703c130640c283d41c03200b01c550755503202c5001000f8448544021810040025186d01d0340b802000c0c0440d442805900d01140450003942c03404d50004004006100b91070507100119103402c0942c503050143c00008003100e5050034000ba250400401e5450902d40c4104014021a03d403001903a0442e01c680c440440c40203100a401d441c64015141d501080c0c800c4041d0800520400f0001414510b003240c030b4014000d108104585020b105180d001c90b510200080410140c910410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 844320854 1250 844319604 844319617
    0x80307030b15040f1719021003151202030105010b0c1b15071407080d120506030a0203030d140c07120e030c04150e060105090d0303050603070302100809010f0e030d02 73
    0x92840d41e82442e01d10440c81c098020350403c060502d00c504060005d205001c9500805070920b40c018889003850010b8601000a070290013405207900341200b48140380280c01c400c02100075810850919502d406494100141d084026486907080800000b0740c41121012034401d105810042e00c821481d100309814100c090b04001d07a00120084101503101c2441e00c041c0031400c0c403904042800b400c0e100007880c64480140c0002a00f50400560b03104070981204844244019120000c02d240d6200c02c006420009502006509030000081d80e601c000150b911241030f402400c45e000300c1f81d8945500c00351040c010190010300d04070901c0d512103801c074080c0b40c0c001041c002c01800c42d0162507280000c2029200c3d07001c602914220940300921002a080600a610590a01c2c11500300045800050900d607201c44e009801e043e17485c008248152014482040a10b8000d040c00090036007002e80206404012510021035528100070dd150307003001030098140c0c15000754029400d208034005220300030b60102 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 844322104 1250 844320854 844320859
    0x50312070507030602160201020d0f0e01180504050c0d0e210705011d07030309052704111c0506060a05100f0507020d0c0302010807110a0303090609050a110a0b07080307030b 76
    0x20440080044d4550004040f04503a0380150340b1407070032900c006480d1200e19a0310b0000c4c48000a0000c240c48c0d0300006040c0310000900c0d007503103850001c0010325000c200542245400c141071204014403110810000c040d404401d100030049010400050b60300c1c0e040001d40d48410702282c58030352340d40110141c09404407074007500c00095420303000340c0f6203805100c11642c010f4141e00560700410926030011381c4030380100b10995890220480301078002d4400c103203d44800c0c81c00c5410070302203418050100c6900c1130120015040c22030650070b009040d1480b003403090046030640306600001e0044e00f003240d50801103d10180c003030321300e2949603041955140c0080c2c10320020000c080c0035410169481040d8044850301403090110201c2c194000107044510051415040c070103131006c0301f544050300003215040d240d05490000380401c030364580340c5e010384590316000d0700724401c40070380c0d00900451000e60140a03000700d6443e000e4580d04d40303072030509009401d4060500c02d824000105000d001e0f80182c0c1000400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 844323354 1250 844322104 844322113
    0x22109060a1e0c080105030111161202070f1e050315060105090f03061003120c0512030c0714010510080d020c21060405030927040213110d0b100305010503120705 71
    0x200b041810460f22039100030400070306210f004120394103082c8200060031409900c041c1ca042d10a0361441c4000c5030305800103000000201150040358428840d04001c2c0003141310f540300c455600c000c030720144120f428001107c16401d150000741864000b0f448044992655000c800e1980c60800544550b0004010f0a400a801084400c0c0658052005a11a040c030380c1d1500615400d60410704500e1500c21030103814060040e05510100d000041d00c2c2d2440310001142c0b80e42d03540c4006042209000d506030081072040407198220000e0810340120740b04200c0a80d01984c2281e1307411500e591600004040b80240e0003101441c002418100c041e01b459001c480300e80c121501d0220702491602008444c10340d0320742c0021039002c80c80e02c0d002255081141c000c01c034062001080701901e103002540580700034031514080c000d90b040c02c121034010030f6007020007071602910b03155590308040190500201a80c4661074030b910030580c980c01791151505a0314040d0007000c1d407400039910380c20079034040034060300da030b104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 844324604 1250 844323354 844323401
    0xf080a152c01060503010c0813031202030403120e010614132711010503061003050712060906030605101202010c0827030f0106080d0315080d03022109060a 68
    0x8407000d5800d020160010000c18800707410a105003101d2803504102d10a074140f0500c0110143d04c10300c202d400c40039101d41d00030b007200c0500d020b44141c4100040741a246001004020625030002d039440581e10340b600782032062818140c210381c01ca80300c2d40500490900d604400d02078605211030f5039208402101c0d00014003d4840101c4000388480014928001c0e100d1a418010480ca40000003c48402800c000d030442c217100c0001003008481c244440304055462000614089c803a9409400240c41884104050750300d4201e10005442e81e8041a00c80c1820103010a41c42008608080304540b10364001e25025192a40111200030000000f41c40b6000b0a020080100800111a1050310414008508060903c1c0141403d05520120000f02c691601d0010002400c003c14076403458811442d0005224001c401c001101c03c001e0340007011544240e10201404942540c0101089407402c11001303c5038440c0d007500102c1040c110303182501a0005800703d03007a80c0e02d907080544090701d002180243c0c0720 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 844325854 1250 844324604 844324631
    0x20702030114060307080111030c0315151801090b0906092d0405090a12030c050c10020301090608030a0f0807050f0a020601140d0b04120212040602030a090f080a15 72
    0x30003218841c2e40d03180c81c1005100c0c0900d0b04002d108020504c9100a1240d0081038031101054080288001e01681001001130700303101e041405100030880081150504252001c03903c1160b411688200c190b50301407190618083d80145d50a000b100c40d800d0781c2c80c2c9810440801d03c00950070010000f40c10201094525a854040e5021488000c0a04804040e100802c100300416100c010f030034200590005180503021484410701d5214070401800c0100d441b030660801201c079441103a01c0440c05020740b00c603800c00b40a0517001941240c1d4098800e11050341c0302e00d009a2a803068000c1103020407003003034496150358014003402c1c3e417092260804c10700700750300746680c8181036011130780d0440107030440d500600134650328042c8c012840d482900c0300c040c000c11a5581ca00342070400f80000e005404186062070704c1c24402c000480204406083c199116650740e03401a5890304580c90000100345c0340070010800c4181503421a0849440c0bc00401010340b05841c0c51008512481c04910b07020307194481c0d050b003403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 844327104 1250 844325854 844325861
    0x51f0e0a2a081f0b011b08042606061807030b011b0602120a06082e0c080910140a0f0b220f090b04020613030c1503150f180207020301 59
    0x40034418041c02803402d080100001c4241411503c9400f549080d0045100ea42d111a41e03054001922545950700284d03414401d003103025940c8000c908174007103801205d1080845032145d00c09003410044842c941c80d0360041000441610300109410315100001507883c910a410151407201c0c10304104e042c1d80481104084a00050380c02922851340020b2002c010341c0c0202016603001c0c0b09050704100950070000b00c19116940c2202c0c140c1c9018284610261121520220320741c1c0032900c4c10200704081203901c001e4544042114440c00c68056403503181c501000c50b000b0750081d554003244101040d0348480e010402000040062000b540d03680703c2d02c05598841000401c0c45207115411a2806c0721020482c0094400084070031390b1041c00c041c0300740005203188502c01d80095040300c030755458031502c5a004120b00602e51002c3c05802c2e030f05200094404081d0f125900c603c403555020310000004c0c41085c200507205209407200000c0754003041003403044080c41801e0f2441000d802516055080d00001d096 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 844328354 1250 844327104 844327109
    0x60412050d0e2a0f0a0902180927030c0a020103090807020301050406053414120c0712080f0402011209080f0d061e05012307051f0e0a2a 60
    0x20680c40030a4241914115007034103080080c102c61260700d1441c1c4e030300850380354400ba00c5000300780358011070079040c080a8032000c1d03510001e020f00002c001d442c001c250101195000d8006522500300b6200400c0001404401c0700c40c82407e07900207259600d4a98011001060020811f8803800028031400c00143d500303006044c021400f8240c0840e0904000c10740203041340c41c03000303c82d01091103070041340b01d28188181e10381503286890510002c1c4038a01422030780e840c800c00c00e140d1035111225003040300401c8440701a100140c000c2001a40580009a06880303195050f900c4200c02d5020000140040d031107181038000d079202400d008a02c541050369400e140d0382151360010045078010a03110303102d0625120b448010480294840c41d00078595103840e5010665019541c100280c42e18040c00c20341424481c5490717a1a849082c81d0b44002e01d080007612010010560140c4602e0000300002ca642d41d4001d1034002219140a00000551035507001051824980096008002c900d8084c00880d05054203400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 844329604 1250 844328354 844328383
    0x10c2a1122050f011203121505030a20010306050306130302010f0e0718020f1c0b1509192601060302100504060f020601150e01020a0b27060412050d0e 66
    0x1082d04204949001240050300017220502d440402140801c1c0e2000c0d14814401d106200090384d0550750860700f40d400c00702d40107145c040c81180040800c200403045895070380c00314000c0a082988180e4011403c0c1d03919882015403592004001ca000ca2400e2150751440612138000002c0d044485110101a40c040c0b140008954120060400440f00d1004119043c40c03c071042c00c501d007000010003400780c0d0188a071040380d00380c180030300c15516101d2076104031003280005060807500d000101e1440b860794006e040482c043c081099041c40d41c0e01c450040d00c1c00b80c0b144103119522458140c2c1c0c45c0703080c01008841c0070501e9904d607031000025803240c0b00d181441240e59558030341e07550708110700035100c03550410b622002c544c4031000401c0100c555581c1c42c4485101c601d0100b0340c9900200c0100d1902c000c418010b841c2a545000b0300680039681c064a891115039500d51f115611a1800c04946034241220041d003040007211214203039610490042c52110001c0a000034200a0f04801d1807800c04c29109900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 844330854 1250 844329604 844329611
    0xc0213020a080f22050a020310020d1a0319020f040e06090615312a02060606030f0405070e0c03040b060d170309031b010c2a1122 57
    0x48845600800b4180d2095282c1101412824011885a0a10320000c104035034400304e202507000f0014240011003560f0303002802c5805e151501841c10700207500c515050342119181c014944108401c0c98140381a80c3c030014090071082c1402c0c0142259802801c03000c0b03900089240c40074440f40d44030703c21882030900381c0004108500e8000c6a141c41c140003d010040020b040041088041d510b0408800b0820384990391180420f40a100c3c0c0480d4210000488914a0810760345910454100803152602d0f20451401548403002d02e10a03a101d150503180190032850800000b03008580000760150454800e90403103040b15940d010310701c02c1c86001d9403240b24a407000420b02c000c0c881c21141082d00480100c9046894000c2683e640c150119050001c1c65408401310004a80500601c15070301000203002c44001035070326007003901340200814070201006ca00540b41c41c0c14911201c0a9544a5003160000461030f84561307200e6124142c0301524150380040c2c03c00c4802909900a120003014180808010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 844332104 1250 844330854 844330867
    0xe0114070b070f0809030f0906070f1a01170322030c140a14010f03050601020f0a030903060c03050912070606090603110a08030a171b04030c06080a020703090b09010c021302 76
    0x1000c203144011058200001309040c4803000c00007208981142c2d071001c0c241030b90341000764042034560007983c0340074011560719a40101805001c102560801e00b41c00d120500d1a038071800000c910214524400003103600c1031204a001c1201c080308010b50000340c100e04a0110303a179554505e19045650045446c0c007140a80c404158203014002c42c016103030712600a2003405845000910500311070070000c04254503000401c41d6640280066101d1052020989084a14078140030b0622540785c801101d5040c50302e240545180d1103441410f0042a0303050140445040c41e03902c81000d50809102605c0780c0d41c2c0e908002450049521580c401140b00d03800641c52020001b0820885905550000101c1d400403c41029119807100310002006083c442c2c031a8580c4071403c48082e5002c10b0140102800000600030040c86041d0742030000712201036881c0d55481d074460030792000380d0242c11002804034002e0070050012590358400760803102c4041c901246038039026000510b050640c0802c100a0980c002007a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 844333354 1250 844332104 844332107
    0xf06020105130816020409020a080a0311190f03031116110102070f23041a0a060f1205040812190e0106030f0f0f062306030c030d0e0114070b07 63
    0x2010ba001c20081e512a4400e542034641d9103840c41002c5214443e11250507404045581e5980325041c469006052a80c40c41d403580e9030b090341c95040a034180d000c02d00300812043c030040001054013800301854045812144075944040c01802c5c01801103080c592240a4914a84a01406003484615191002000803103078100100340030751402c81c06045402005040c44840d0f00d80030404200e4051201c0c0e500c032840c44185c0b060000e0f55840388075900c1424160000030301707403d000d40400c1c03079402265844d000f5580c804003941e114600300942c00200380011016041001c10b82e212551050007244418582038403600ca803c50301320b0403175110b444c0701080c40504c03070609000d21450850f0f51021008000d01ca0664580164642035160000c0244170300744483c0c8104518001c0300c100050348606c0c14007501810210311500d2048070749100448040540001d00b05280002e0408003c0501074058030041d80941000c0b80d5449140c1549030500c05803c0300ca180c02e2008800401100340a609400c1d02810003540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 844334604 1250 844333354 844333361
    0xe0f22050c0f12010f1d07051b070b040303090506031e071101090c03030f1103091201020708041d0a021c0e07080f030309060105220b0307210506012c1003020405010f060201 76
    0x88006400303003100c1c494200300151b12040e03400c25250f0a125403070b43c0c402d2158068104c07840010110501a12400280b0600003102070419607120340c66100902d41c9850901000c0d0001f00c0300c1c04221080152141c40030300541c40b035290030040c0e038a084035120345c00044145c00d5801031502240d203506403600c1002030590005404502207100d150801c02051034500d41ca60720300401284603c18864000003541a66096046079915648107024a45407591030340030b9520384048940d01c000144000002030301e485014070803620360354030820b4100a81121350245100914080c0041c6003d485100d40114840c40d01700070382031201d18408011a600d141038030110b0700301030060f403109004140315030014032501044400c81640c0100c031100051462000c1340003038601955940034410101031001c1810030b54035041414040c041c040c6003291403d03640d50035480344024544081120030b44e0660424200326554401359070704000c81034004070000351a40c0001c0e0442d1001c1c1c1c00050710030950340c410040e2075020f00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 844335854 1250 844334604 844334609
    0x80f010c020705010c030e0a03060e0304140306011815181a040e0303041218030c05120c0114161a01061404030c03060b0102011b0e0f22050c0f12010f 66
    0x800350442c2c9103448000f81660040302002000d114400804080d00e84442c1c0031800110707007110342400640041c10704107032254002d0080130640c40f1302c161090014180021214121400c41103121040340031030404200410341c01141c840ca840145500280c007a040c0d00407206075504401000807100c0040c2050000103201e2200c0310300603820001c882c10783c81c4000c82520307405900912480c152040403601101e256184180c00701eaa030458503404824001a0320386d18066540548000459a468000d0965680200302c0c409000030213035a00c00e081042880050101040d903602a5092210281e6a190300500e103014012402c9900900411900794400090041c10303941809003450181591141030200c00103000282c5869110502d0310040d034402d600c8414140320b2003116501040960350001e205000e030b0748030f55100e00300b1040d00c0440d5260507071480c509e00c90941c003004544a44a0387e00c2d406001c005007098400e850a00c125580f185d50000200401040b80b87c0c08805581441c010721071014058 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 844337104 1250 844335854 844335857
    0x7091d0105152a0303060a2111030f1902041b0804020402030601090e16090602030c031c060b18040f0b3109150c03090203060403050703031401080f010c 67
    0x6400400507525181c040e5140140c1082000d41c1e80c0c3d00c10a903540710051003401503d20b0721030340094031182e02c5003c000341d4007030482125800c4203541c0d2880c4044e221149041600000c000c13020300c1c80c00040e1242420600d80380301405440619951800c558102030100c1c0102c82800c440710f840108514151062521505a0b448019000c007000704000341004401800240500d072300101165003a80120902801000c055540700080e00d48034058980c04d605400300000820000100851928008429111340256020045043c00310b160002035801010015040506944131000f02c2d940882d1001081c0c8488131144c1c060303d4100301001c0c0400c890a80c600c1ea1a40380c9015801d040c0c0f5079400703a80030181034011541d251801c0e001408280324410303200b15100c00703604c0c4c18a110f04120754040c9640080d80c0c8000d081010f0086490b00350181d40111900941c10340094000800080c040c00203810b14601074540002d1403444503d00503100042a00083c50a921200507404505024040d0b9403415010703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 844338354 1250 844337104 844337159
    0x20702033d050a24181103090d11390307031406060414060d02131a1e010906050d110a0504031506030206091507120c0c0e04110f010e03060709 63
    0x407169038840315070b0083c03881d030003800c4480400034411900a500c0700c0c0d21481c0306c1542e07800e01002e51a510509034003a0400314265200e1983d024001043c08446a00c100e800c0e003410031a1018140348000c0c0c102c651083e0a0090015605161070411840c40914401c01d5460b14110100c2101842d21000410007842075081400c2c0340c038180851005903410031000d640c4103582d144c880c800581c0540400c0c07480b1191078540019070054104e841c2e111022400d040d1110001c81140103c0c04045a410007170352070201d000d8a1302000800e21941c002e00d1075100074000050211002400c7c40460b900c0340307050b00c0002d0804101030041c840302e440c00c1c1724801e86010f002c0002520710f0740424007902445022511803203404002104110801085400300350307201c1144154440e07402c40250070070054982c00e4580690910020500d44031a074180c41c025500700300300d12561100341040060780c0c0540d02d81c02d130400c0700c0c242103038030540c804000e924014182030311110b955a003041c10050040c51840300d803e020540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 844339604 1250 844338354 844338401
    0x90516081c030b03010912030204090f050c03180f2407030504020a150309060207050d0f260c090607060c080c0703080c0304020f060724020702033d050a 67
    0x2980040031188007003070300340032034288001c0000034014540418007500b1001c90310861451240d159004005440c034040e001c00c401c00b83e018980c0c08540d01102da800c101707075040001c155030f030f0300080442e5004c602e038008850705c2c0581c19130103e08024030b0030002d401400341c0000e0340d0700b04601c5e045555480206880c00308040e11741900000c140460307074400d00800040401603000d180e4420340210500c00e405c82c00a542d10340c110b180103a544e0a10740f440c0f5000610300303483c6003841481220b640081723000001d0505448120208010707031445019046400b401b004004212076601d414014044450080b1030010392040b031418040d0407410000d000728450710040012900194003d2505a0040808a1a66203941d5144049060540610901584034074081034010802203041e4000140c0402c40c906481c51984006585050b4060614000e5243e08800015100c00d048604500c5a0803071310045032081141d0540b41c0200e066403145800c1d1826107401c00c0054000c40c90061820804440404e041b0054 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 844340854 1250 844339604 844339633
    0x30d1b030e0a030804080c160e0601170f060a0302120f0f0d2a062a0804020a150c12091406120c130902040b03040605060d050303062209051608 63
    0x7450b4000040500040c03401203000e2050324410b07140b00300001d108442c6c429841c6a801488145035200309a0b96108407000106c807948560105010544032103c2d029403030312400c203076191481004241d560446c204c0a00000981d17544000b603019240110017500c1d000056485603070170922900720307092556200c0040301d9810b95002a1210440d07028000d900c0e580802c03c034a4048403440300e03030050040c0741040410300c81c04200340005800480d1081d15076640151041d8142e40b5041308440195210b40071403002c1200010b00740004504440d6490f210129604c155030f0307100c0075100700e0049000a50080024031041190000d6400b001400300c5011342810b9500e281902580c2d001006c40506600102d1b201c40050303450702c803100c082c0c03010340f00554503607031200c2c0000e0b01500103c0f0207540701c504000c04074100d0f0600a084003120790b0450702030b6146640e0202400408070a00c00d00740384520740d400070708050000751300c102c5214034860005040000580440c10700010321980018030141c02c0707a2000c01542 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 844342104 1250 844340854 844340863
    0x306040c08061c05010b060c1e0703020a0b09010c06050c09120a0c14010c0507060e01080105010c030806150c0604050c03010c0203040f05010c1518120201020f09060d0905030d1b030e 80
    0x325aa200d883c080b1111850024050442001816042040440c0d14181d544001c00c1d400c0ba8103440072244d04031600e083c1c0c88641e94003103602c0069001a0540000e109840850008003030703054041c10004110f001d031b0398444080f46c0c000c941c8100d040c000404e038407080e0320301018a0304461488000402c00302d02985c1b08e403039501c1070328454400103801d142211306290f402000c00c80d58007500a01a2880b59903142000b4101c0e080060a06000501e0200003250341c1d030042d9000d0441c5174141d5120300640c3e84842c2404004851800e03c030b20f6018060103200380c031402c2041204d200e148600c000d08810560001071600351403030b40f29003005640060009024407441800400100e500034a001207022009003010f004c462041050100c8a80c200700400084041c1c031201f004485110f54000300c401288120224201d02501d80006a00903041182820903e0248060600181402000105d180b803e41c3c0d80b80c03440d8080060300c80007545440743c3d108480c00300300d45140607103103d050510001030110b1003942c49 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 844343354 1250 844342104 844342129
    0x30c0d1e0c0b0f030403180608181f0e1002040806340c0c0623090a0b03100612060e01060c0c0510090512121c091203020306040c0806 59
    0xa42215205041c01022048400144915642d560740c40001048500055100311001c0c0c010545071454003481182400c60481120480c0d0390f0181503850700d0190140c015940b400750342c194030131007130001d4000042c4080402d02c102210300000b0044070f1040b9031428038041d4548000e05901c180420091040003265950b4080d040c00a0303108c51448410b401c1c414114044090304c00381c07001d00041c0c0380e10758101c00c0303681000e4000e00710180342ca5500c0c036085030355091800516100c00e80d00d4042242c0f05a010010300740440c0010031108a081d122141c890a42d00704807a085038600821000700702560308481485000c6d201e9200c1405880e0809603000c1b0381010621400d010000724100203400e210000d21000d0240c40003c180682c020038845008200710418040e451090015100c81d100900002030881188100400f0250420814004003901445500007111a071900e40341114009510038492580b160229180140c0740d01705841400222135003540d14105008010302440516902d58014406 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 844344604 1250 844343354 844343393
    0x90f2802060f04120606060806101d010207120602130f05010c03052128050915090a12030203180c030c041805060a0e0c09010b0f0706060509090705030c0d 68
    0x19a140740d40b20b042c03418415503215a4100d0000849681080a03640002c4210340c2c0c50390383c4c0c00594880e082040090100c0828480100b02c0c0c1448107201002140c01007880c140c01401a00e09884e40c032405010030a4245604076101d40d40000c0300e5105c6500800c00d107003e80540c84682c034900d0303f00070001e0819140003502a050040100b94125030030707076124007458880305d40c8003403112a04107440d04100c040106e411149490324041540c0d85808214032a651046000c040201108403481b02c2c13100b14280054040307a9107000d00d1040402241d1444280012000700b55001030b9a071400b0f8030307081d00c814821451122181c200480d141c0c0036030f0300015011013154040380c0008401a507810391040380210494001d10b01d0040c3d204000114889604c680d0301c0c0d800600070b903045180003030200a02243c09020b1030440d00c2d41813000300d400e400ca04015200803440744500007000e90300c40700020100c501c02c54140311594080d40e010700140c00c0602030f000020105841914002d0155540c4901c0c3c5140920003ea = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 844345854 1250 844344604 844344607
    0x702060115020706080c070609030c0606140612060f03070602150c1c0506030c030d020a0c050414040303050402060d06141305100b07081329030f040303020c07050603090f280206 78
    0x1042c54200d0300c120347c45154020010002002c0614000d80b90801e101c0040d52410301c3c100380024189030600078450611401880d076460311100f90b901740c00c24003024140303982001c10403519a0392a1802c000120180c0700540003445545501c010413980c00c50002c11f52114120103100314850582e00c80345888640d0300901002c03c036990b400b40840d14000700caa9041d83c0c54410401c3d2021003d80208401d11000e00504131300400360b45410600003a29480012540c1100032179000902180c42640480d801c03520041c08140361000a05050040d600d8a400c52040ca41010100112928002c116915511b04120051010789480380071128031040910400c0500a40001c0da081000a8541120308054401b072003043c00e95154020005419401c00c001100e100e0b074000040c4000100030180c91044600a01310000b581e11541c0480180d08030b02c10400d254441d490011030356540da200914454007241004151105004d5845850030010002a0341980e00c09603045010602841c4002005a010388000c2e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 844347104 1250 844345854 844345861
    0x5060a1b17040323090306011401080c031b070b0a050f070f1808030a0503190e06071d04050c0c01060e0c070f0312060f06030501080c1e0301020f12070206011502070608 74
    0x290340e500413120b003e2000100c0b05007045490800134020703010501060f81200ca660fa00d0b45800501036202e00f0009001c90440c100003080c105811703004661000a020081c1181140300d40b00000755081a2012500d003201c000400c03c0b400000d10031030b6448120040ca4004a003002d2501030028800900e0320810802107003000501190740071041d2008041d00c0044036981c412541c00149160070980701c022a03050201e00000d080180350103446070110a140240c031042c0c9802c032043c2c0d440880303071a003c8202d084a40c000e10307855456100c0c461141c10385944544e654156500d0b074908480140e0000300e4001d03804403d100c1c42e9100e1800b0b6400fa6a8005c0c80580b02c207100381030950b1010403a240500c03011381403580114900300321090030821100281c40a001590b2101c6401b170b111182c0c1c0940039040b400b48000c0000ea407044151081d0b007004007038001441c1c00c2c030042d140390f102d500a075400e244030010302e4144110305504000e510700510312102c6000b1503882c0301c0c2d402912002c00c2e204013010014000c021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 844348354 1250 844347104 844347107
    0x1113030b0c070209010e01170f0304150306170c1c030801030f030309020904030203071205121302010909020a03020915040602062a07300203040513140405060a1b170403 74
    0xb1102c1c402c0e00104040410340c0e4030000040ba100702402203004104039542900c4011400007036000b00c0440e01000b540c01c10f4141001c0100d00f00c02c040d5002c040507200c140008618200c080d0541d0301800800281c8030000d0000180a24402c886880200e00380d032000c9100e004c87d90244002e419a9801030f07416000c0d22a0f41070460140042c442c0c060b52044004042c4410190000010041c0e140303e5102e5003c2103801200030303a03441c040d81034032080074801f0000040e00c0d40e0201541c00300561050503c0100d541d101c1c80303040100c0c0c002040141c08241d001a603085240307800303008410f0b000610500c82d841c1a0400000a40315407000e84100301540e0000e4050703403850707512008001c80c0e0b20580512520760820b414462500a403041203001310b5492119003003039122600c07090f51350044503a0029450980f40c1018420703100b0b500341404204545d07400d0302400504041c08544d0099006000520300c82c00c12116000449002050401c1c00d140301062038010380b50410810700d00c0701c01001c20002142d655040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 844349604 1250 844348354 844348357
    0x15090902090d0b010f080d020a020a0b0d0e030301090204090b030601050a0614090d0317060901081e031b010b0a08030405090a050a1e06080d080c1e160c091113030b0c 73
    0x1402400540680c0c0045800203045085c1c0044650141c02c0b500714284d00f03001170340c507940324034006900420344500901445004000400b0380c02c60000c0001411140d0ba080303542540c10a0700800802c503000030341002003926500841d2490f200440151016503d09800107054010a110364814070204050350b6130103c83c0d02050314820032000c3d0061041c500a403900524058043d000e071800340720f200020071202c2c00c14801c828140c40c00c01c8010907403066031151031045910303480c0340442544410058070449036118205000d00002c0c0703600110b0301c110700c001000668801508070a04540c4103000404c0160758002600750403032161180081c1940340c1d960020f001d0443c3c414500700100e400c8074800c2060405602c00d000b01c0d01c50f0b805403182514000d4046504800a4070980f1294606210019492200f00d030a00200c422201106180076442c0020801c822000f08050720203074808401008049410700031030078401d564000d458a40524054001e03540d401c00e000150526410000150b40c2941c080c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 844350854 1250 844349604 844349629
    0x302a0304242c061f0b5e05040e06010603050f09030f0d0b091e011a090f271006050f07152d0f23091f0e071509090209 52
    0x40102da481500161a00c50134008036502e0201030995001d5500c10006005c08514000603049503201e1410b1b450003040080260030014801220031035000038043d9a1485103a0741c400c6c03407101038107082d8586480030f003c558008100100111001c3c0c02c11540000100c00c6800e0300171903176207044d01e0384540070090009010309211036400c15514814000b424140b011006211441d21203c491241e88698030320b100c20040740030343c0e450f000d0b041c841003803186411158148a218050080e034503400300030050640310000382103890707486d002c808180442e0181c50f884c0c6002824a50070701c680f070411009903030b0700d007480f4007180500031074101001c128101c1101d410081d100000e21843c0f102d10f45816610881040c0040b0804003002c3c501902501000914040c000882c10703045074451030507502241d02c540d00e490003071041886000d048505102104020802c0120300c01d19480012040442450240350450640100e00280b0618940c0d480980d070240120064608150001d80c940704d20f000400c02c0c103c00301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 844352104 1250 844350854 844350869
    0x131205120f0a0b01050f04050d1707120318020609040c030e070b0a0e040501050f09040f0206030a05060316050303030106030e03302a0304242c061f 65
    0x1002807200150560405901076007030b0390b10402c031030316090005454a201c0d4103111a01800140020046071400d10300d00c80c02640a01c44040343e5081600c001d6500c1e92040504031091190040c00c40c0901d40d1511803140b01c590004070340c0004038400d40000c1d00c035020b05401d081c0706903160007011001c1e611070780020b55065090402c45841648071109891503411112032176002030b803a03400ca000c10f450640035050403107401804540310384a018041c490046001402501d445030038880d06401a2500c100840c03245c2e035940c60000d224105070b0105030500104103e0112407011400c400d0209035000300890741100d0440c1030002e5200c00200405003035004010004080003047d5501c43c3c40880301000d41510100d60410340740003680c4064180d26419149401c0c9481703018021040c40038021001c009540241c0900d030302c00d114072001c80c910400621400c1203031518070b0f00e96001c956401000000d4200c01003210071146007256003c0e04d460340d1100c0060034a030729603071040d000398480b05008038990040c1a10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 844353354 1250 844352104 844352137
    0xf04080d021e0405010225140d0c03150b0d020f040f0902060708190c0c05190504021c06060c0213090305090607110328110604080d0804021206131205 66
    0x82110b80007a0040c0c03050781e01500440c0099400900681e1420340f036005440e42e002c02803410000841c00b1011801c280981124058030200046450780d41011b00440c8900711203010301c4c80d4100d0003c00d0b0f4a2050800c4e010b02580c5000300c0060b6074054481101203820742d00051640030290912021380900c4001175003180340002e080052102d014010144541840242e0340703d00c1c0e00a0701141d000e03010308405410001e803804140b2003450311500c036040b50502d5048001056461b03c00003401c0ba409404006580a109040703143c64000c035001d014000d104a00f0a01c075512a0741c0c002c92038101113105d100503025551016942014000d00070340e8220034019260503210840380c644901e424124507407491091244c02c0001c103100880101c031007000803000701601e8540c921550396155251891080701d030b0009041c000405d98000c200080034012030346560f11009403c1074018081e028840c030718443c81c0c1d03400c040100310305801c0b00814901000d40c00114168030807004141280d80e4081c501415203102c25 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 844354604 1250 844353354 844353397
    0x183209150310140f010e01081c1e03020a030e030f0904111e0703032d0f2d0f0b0306070c050a060c08040b07020615040e0304090504050a17030f04080d02 67
    0x4004100134461621001c04140c9030362240c1041004980900c2a081d00e03510050080c0b240304e00e05001050040494103103601800c0b80e11f1031203501030f0080d040780c200296000c6003d5515544c54010304030045401030256242200c4280c0310f10b071070320460111900807500c400d0030b4411222203504481c1c0030380c0500070505040700112451002a0302824082c3d0004e810070149010b601080480b0a11002850f03400d10480ba80001c1800c0c0070b80103104040d003460350340d101002101c00301252070302030000c0300a0030040c4948801c05a84100e07012580c510b1189490300403100c003291000500550002514105078281a0846c50b040d413806407490401017150341025060001c1a03002040540110310030703c030b2100d559031042000c0b41c1c1d07004200e801c11030340690494030841a0400758403a044030310700070050302d103080c0d200d80b0950107550707041c1e40c1181c1c0c0d0fa018062050a00c5407040e0f2500c4c59038603104900d4550b081c001c0a201510b00c010388054988000052411500d031066412199040d501807240c55100784c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 844355854 1250 844354604 844354631
    0x2011d1309051c05040e0709060c020d020d05060c0a030f06050d0206091c051006050607030804060e03040306020c0312180606040b010903050f1f140408030403183209150310 76
    0x4001c0d01c16031b80d85415000104138200d0084001c04260b44140da40d4203101c4c9031036001c10420940c0044203980120000307500c4808260180000c5110300700164515640309041c8500408651103416400c0c9001e24040b4240302c9076403002c5804581715011680303c0d44030380240c03001a21a036070307600140c11005061013900007080400300700030011844043c400c001040d61141802070343d120b000c0004000032203130800500080d4403548035624480c0c000040781d040503283e0341c4440490b88040810442c2c0d51001c03445071241806150141d0344680c22000a47c421a003241a103962010b0141c6003501c50340d20707209e803060b4603403050007a680159049400c8039000d200c40140c95407036028070500034601b00c2c081e00c192200b07400d1502822805207071581490000741c2d42e6883d000780a400c003800c01c40801154242c202440c0045c80743c904043c00b100100c0301c0c8003180a05442011104448044a40014401d1420101e503124424580c1c85403484101070f12000c10a4002801c05031203074602d8084900c1c008203a860320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 844357104 1250 844355854 844355857
    0xf1209230c010f03230a0612030908010b0a08060103030f05190f02071a090126160f0f05040608060301110c0c0901050307300507060c02011d1309051c05 67
    0x1d20080c2c0302c3c07098480440d14101c042d03a54006810922041d0b14140740c20a00002c5200b503400b202492000a92a07121010782403503201314074084d000540001c205101c030040030310612003800b03011a080ca2025180124207521a681480090140503240034800c0c10745020300200c3e440e8100c0501c0785507800040c5800504030781d0b044c40c41000140f060745404102d000c500c180802c20040310b442c075681000c1c0083c0046501c41c5052018680746012420b680d801030078140740d41e07800b90780045021040801048030040018484060031000c00001c9500f40c08525085012102903521b1881c0c004080d5541d100868050841d80da46108801c20000301a0b86c1040c0104054010090454000f60305980c1c4404055440009000b41c800c06404000304410702c00210403064800c1da040561048400c50f140c4406050030070701c0d48460089a003490000c400c541e403001d40e0a00b04184c01144082c29a90007000ca2001500f500d02c9040003566106488148001000070130b031002507007800502902d04100000341103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 844358354 1250 844357104 844357123
    0xf010f09350606011d0418050a03121806090218042109030b0a020a0c050708060a0b03190305030a3b030307020a15020712021c0f120923 60
    0x1441e1500a01c91240401140b21405402d051390b90301d80c41d80102c0019030010758090182684155140c0c0c01500302c40f0041410301c0550b000340007901c0c0c1401035081c040c0140850800c103030001e0b85000c6850064500001d4061401d542015000900780f685201180d5050301c40c0c0b40c00348407109104100710070008030062114003900081d407000c80080d00b914085c2d8680c4503500000304000c400300e002500241c2c043c3d014258a010318508040c08000540342c541c201130b07560700240c41540084007003003010989402840c101c40c00a4006000c3c84005991004680303803103410040401c1000030208150f2030301600481c3c00060155083c3c0421200c1e403c2c94580c0c075080c3e00075109901086070640200500100940384144510b4024041c814000d56480c082c002543c40804c41696090110101240e020354540106120503001814103d0007882c01c0d500d0400145075100400c6116449000e24940c05502c0c1030030b219002e01c01041c001b04034030341044c02401103440c0188071030070b04000d445840000910315a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 844359604 1250 844358354 844358429
    0x3091401260129030115090b0a050301030515040503070b09100c0905100c1709210313050f030c0402090406030605040c06080f060a0b0901020708070609050a090203060f010f09 77
    0x1403a01150405800407440e0b540e040c40d00404e000400000348040208207881c00030346451810141c4a2000c54002c1d04011400d500141c0b0110060040100c204540b94400300c40300c0760b201541c98a41c0e5140d94902c1000c800420148107107010401d50041045001c50543c82d1490034041942464002024180288030711482850514041c48809004511004002d034000d2810910300c0e510400d400c010345d0000800d036412500074021508441c2c03000c0084401090f288019640c1ca074070065084511002c1c0e074120703502c22040325540c08642d660014030481ca08005590250b01d6070100c000141c0201100e502c05020b050504081204004107101501c00b5074005881c0e28989458070300a140320450210bc40c1500907541030b6003131104c402010090b01001d10144103da14050711001c4581c04c011465200e0404540020400d0002d45806c1c20080080d01c441a01141140781500002d030804200d400f2403810b000350301c11030080491141c4072000160a500b500801e0b1141c010741c18a00032801041002c0c3c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 844360854 1250 844359604 844359629
    0x340c0b0d1e0c02011805060414121305011107140409080403080a031e020a09030807051606180b090d02091806070e09070804030c030302030711060a0603030206090703030914012601 79
    0x344175071156003088540c0743c00030000d20b410364555a8003003000c03010071047c4003107100300d0202041a90220700208103100000415041c03141c9403800140181c0c800003e00b85e025000020280100044041c02c001614030465020a40074094100340e6582e124603040501500800640c1412031a01034005450304000320700001100140c1000000803402001c2d000d400091440d0030402c0130a5250f00a400c201d80104161150702d1341c3d0907404c8000070490b5115402141c0445140003d001c41034200c3c000502c01800c80d68030780407038100050900404000024803034a040320110309614119101099a1000d00e02180e40e6414028005804030300036880c454070403201440090481c0348580500c0d40a907a0640341c54481480e0380e50300340e010350001003951082144c2c88070707480001182000700700d0080e0b02c40d00001440300e045040003801c0c01c41c001c00c058100d505c4603004100080d40404468101c0702101c0054410750781c04170048841852902c940c00c4000c4180c201d01c2c0f00b9019000c0a00e0407034075203503001c3d07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 844362104 1250 844360854 844360871
    0xa111006031a2211030615120f12070609050d0206151005030f060f03070e040212060f19060302040504080c06090708031b0a08340c0b0d1e0c0201 64
    0x20444011600704005500640105114440c118141c0010720b102c4da024030281c01c42140841d1800404440e201e26000761811004420b0411406c88083c298106c0060000d100c054030b0b040d6664103000c2c40b84402d100000a02d9402d1244503030156154940c080309030f80d441d03480c150000755540d20680f000c01201c41070841e411070701d15102c0401d40e070f514030343c1d224a402c45d074400c61030184a0074000c26050700480000e40c9148950390900100c006000f03880080d00d1103003010b00501550000141c03d44050340d00c07040070f00c0170501c04190f90641c000060200c2d03c220440d2620441d01406407644001c0d0442e082c9001c0c0b1042041032000340200315101c8044540c56660780c4d050315660303102441b608085410030000c55a1500c407406403100d507200403008032b0b02d41c9401951284000d91005207492200701900131036825400300c4041c100c1c0580305120b110300c0d03280e242e034449040d035090710710a00b540410006252220700d000381d080110f80382c0002030140010104807000314040d01d03112500400552030302a20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 844363354 1250 844362104 844362143
    0x7080a020d05281403011d15210321091504030912020a030c03120f0c030203040b07230124230102120a03092907050a11100603 56
    0x103941c034a0b0b85a00348480c1901e40100f034505501980b510000130800c402206452550541d0003c43c02440201d1803800454180e444101d4442406040002207200314865001c41d503841d0040c0031800c28800034070402003124003025074034510030b2840b500c00c580745800080b00c51240d50207245228168a00c15103800002d4400842c0c401e15007110010b0200740056024000038045034020401d41c0d01c00792000385083d4403500c404462a409074030840d460300c1c10701d807054103980c2e11102002c041c11090030007041c40340003581c01079241d0041d8096805400c50105003c818406805c0c80d942441c01034000c2038241c8000220514041c3c107095600204041c0e21107000c841c1207100304400307001c0300c0614054900b602d0803545070714424005a5a280c1c114840d031116071421400d000010071080302213840020303031000c0602d00b2680218905d181d04110320729841c1032022000464030f105610034070524285698485208007607a080078034403820f0409110784503c41c2814145c40c0d0007a0203690040441d5015250600c08 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 844364604 1250 844363354 844363357
    0x60f09111002060c09061b060a0608061e04032015010605040b0403120905100c120503071e02070f0815090f0318060403080d0203150108061c051207080a020d05 70
    0x3140c1c0c0181d02440c001022910104040e0001c4040104110300c0c0c1800c5501d01f0154a24205082c20389804c64014014040aa0b200c1d15000700540c02c007500c0d1901d840424070800360080d0140303403100115200000e0816100d4168280c155040c024400003642255000f10303902c100c102c602e810408851b40c00800d03880d00502c01e507411161044070881c1b406096641309031103160103420640901c1800003010070259100a070030b00c00c0c10b41541e509080283d00341002030864040d0003260b001d101042050182980d0312145050303403441803c8552110481050f003c034a031041c1d903809000310030742032400811610008605465030540900032041f8079210741420503120400b001c102c107503e41c0200144031066060b000e803220401c40c0117119504013030392601e840089912041085809990020400820034250b841840c0804402e103008800d5140070008034031b01405c158100780100150390581c2c02004800c21a43c049003130b1569909455030303d01e24045000d5008001e4400241c0a41100909080e00c110b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 844365854 1250 844364604 844364629
    0xf2318190807050d050102070b011205010c0e06040302010804020d0b15120706020a0312060b0714240a0911031207120503040b0106030e0109020307180c0305090606011407060f0911 79
    0x140500106440c0104118041c4c25448003140c0c607540900020f00401c86000004c1d000300001046600e14900c14036115003101c400e2030310202801802100641680c5401003030b01c0650b513087c20021256142d90001980702040100010b042000f820300700030207040a440307004c2080c13201390360383d400e400307600e9249a403244420b010300320040c0d1040c07c03910082171140300000070003121700000042868503000454150751003040701b51450500c0c40d5041390404010441c5d005004c206690510080d500c4d04a281481c180240c80b25442ca80c0716807891090105690509000030303801030485220140741d40d11021190001c0c00250b40805400120318820381c000c2e8201d1784104d42c0315030401d01503805d0200c00d82c020a948230200e0020740d40c9041e4200146c404103c144060440522203080c000100c9800b0310a560511503030104150a140500c95558030006001d504001c0c2401d00e4540c2d0101d121655406020795480502101d0030022100b0422900d9807080c2010750060002a95518491003800008404032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 844367104 1250 844365854 844365869
    0x2d01050417032e0e0705030601140a0201151706060603011206050714070c08010b040903050904090318120201020c0607030e010e131a0405010f05010f231819 69
    0x1c65100d00d098000100455014406420490205144100d0110605202031503180b05496036401488003252003c1141c0d40030791a860300c10300d1841c1c8403000804502020601c07900d42400801c01c100224000c1d0082d0400e0020850000410b80e42c40340188012000c001c8003400502440010505031709140041340c3c16149403e100b0046414036a03507a07001094005c0040c1708100c040b00d00c00202c41c903c3c034001e03c2034501891241011500b0544003600310390720107100b6441035140c07000141c0003035040010b0352116203040310000741d61081406c040d903001c10800c4c4109444024003034089104620746401e040765900030f9086410058000040c892240300c0c1140150114510580459096100300300e59001c03900054290082011800001e4003070f51501500032142d400700544014a900b000c5c85218010040c0c0b078100c4c01d0042c030f00400601001185042001042140f280c00c520f411412155030b4100010154442d135100c184241a00314108004610f500c00c170421031a2403011800410000d00f07940e6403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 844368354 1250 844367104 844367123
    0x60a0206150303040509011e06030605030a061109030102040f06030b090c1207031407020a050c0f0901030312060302060d0605040f20070303090b0f10060822080c2d010504 75
    0x118181112940d20070080075515110800020403141c1740c5902183c02003906411540d40c0c000d00c81d030305950254958000c501018035100e410070480e540040d207000032907085000000c0c4006510000400b80c803514554a030198000540011940051400d200845580c2c2d5810000400390804105080c131095071011595042070002241e050300310344620790010218100000e000900c06208000316108841050158000d02885818441d00f807094100318101100c0541000d26a00b00003020b014042c0405400c0204841003007445004c1980a13030b000e50303002003c1645500c240c1800c42e010380101c0c0182400703141442d040c03080c0b103d1140140d801842644071801a0082c1c08428005260000d000c1903080540307a183d0b050100c2c121104150041106007000d010a08e01664880d11040180d4407031420018401c0130083c04c000c2d5603541070054030b42d01c4007450264030103061454190061811300b9000b8000c1550b11003000d031810001c0704403d290031400c400300440311000d15003240d0045801900e12a138 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 844369604 1250 844368354 844368361
    0x20601061404050f0301021918081c0302070203070305060c190f02102d050618040305190c021e0102060c07020915010c0b1008011823070b0c0714060a0206 68
    0x2d00a00e900c0400d0806800181401d0048c01140441800b0340e0340000400d1000250054200c1800752400192200200900b00500c2c648001c800c408100420b1408040e1b003c00d8071421076406200d503000540c0c2040464404d402d1004140400e544041c0311070782030000508043da40e00e07000d001502022010b0746c011300841e204031041140a451800308415a020358032132400911458070560040410550314009824603006003031103d001007030502c185075418042c0070880003d6001040729144620100070034056024140e003990044076180f0000c0d40080003203160ba410409010841e00c2c01842603007208e40c1519114911b103118400c000010350001103010001b4645a105104a0003040042c034021000040641358000f00c0340003903e0f0900d40c104491707010002d2a02c240500c4401e940141c5409910f40216950a0b00f14a0240c25000c82100428803424151009003e100001d15514105a5035582126802510742e101405201140d1061b0750709107201e0b08000e4182c814a000ba5001031000d0f0301c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 844370854 1250 844369604 844369609
    0xc080925051c020a080328170405100615020d2016090f1107030827010606080f01150518030a0b010303030b18060607050109060504030f02060106140405 67
    0x58846a03010251050390009194a5424164078514a41291101102800c0c410000c00920070f62000c0800d80c024046107444181004c0740c2e88880f40d00c5610040c102c1c802403015500d1503000c940400700100d0704020402400710109203444c0220000d4410403400340c450855542c00d460f00700340100141e0101d10800c402500034414130101000e8072012028100e51070b843da611b0480c1211042040f40c0c000d040c00c10607200036000d0700120804650301801501e8030074008108500034140061704000031800403411081040115082e250020300891002e40818114103028201c644aa200001c0f41d40000a04500b5040d0086045c1e8141e19a50240d84000302c0040b04c1640011003002003400c202e000c00c030720381d41d401c11411139010700c038200300e0340e442d0704d035040180847e40c0761404e16000324024903242ea0000312000410361b2103242145c0290b00e564450910034010700300c2e00c8005004503d030070103100501d608035032011007600440c3c0c02c54003a41e88600084401c400c98810b00c901480c1c041c072040c041031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 844372104 1250 844370854 844370893
    0x9010612200301030f030210090f0213020d0e060717060d0f0201140301060201050a0b01030e0a0b070e030105131b0e04110105071e03030b010f0c0b0402040605030a050607030c0809 79
    0x680d01146001c52098042005a0084c0d000710f407070690001c014410190140200c1200740f03400c10042000812503110b0b072400c2c5502e410001d200d1100c080000d011510141d05482150008240401805829942003680d40c00180c9540f40411185440034080c20f0340c0e00000c502c50301010300107141d450059691280c561007107590481c180403020302d085240203040c00246008140b160700100396401d00e40160000c6a11000840c0d041500f0140031190100b03000501980c1e0039413000a41c881aa113400086440402035041c0c1c65040d420202808542c0308150000f61900b0b002e0300b030703010244075034681001e6014902e01c03070300161040d07003400203000c80c18003405d01c1001007042c180326280501d81e99071012440e004003900f400c042624002e44c42415410301c20b20800200c06e0900314615101d602c00981001c2105600070f009030810750005085442d01c0d00002c00518020302241c001c81160301c0c0254582c10100c40340e2001903e4090a11019841104900d010340500d2006e4181400007480703182c0349 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 844373354 1250 844372104 844372121
    0x11010e0a05011710180c0e0a0305032b06081f05100b07030201090b0109090512030114060c3c01050105010e012601061709030f03130c050a030b011409010612 69
    0x680100160000317400b11410b0440300100900d00700062000c03100040641030f00c0c00e496440d8003c00754207006100089002088443c2291a03803580e9026003d180208409080804440d00d419810a140000d03130100014071611600207030040303240803400c901968401c4810865050f0602403190008100d0442c400c002060b000c1e0003480082481089a169207001400a81c4100c410a54510070403050003001d000740b5090542d98140c00c4e01e594900304542110411603031581c2d00c00e1500085e4404504820064520100011114031850103082d018000c0d0503642661181a1032030308200500a002062003030905031481611400b204600c80b01c0110340e034038400c20700400307a4004507080c00380c21410986150f000b0001c13076894076240b000c1c045000300d600c01c0c05407000409500502910311281c04200130341e80d01281c11400c91540f560542015601700f45a588150380201e6035031000710502c160344140c2410303149880c685540111030358041c0a1800000d00c05c40002695061080b5002e03466900705501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 844374604 1250 844373354 844373371
    0xa0e061303080f0f03100806090a051b01020705090c030105100309031209060f152d1a07060f060603230a02030a0e0f010902030f0607050d0914060411010e0a050117 72
    0xa20035880703a0243c0985c0162100c829044030f01c1c0041280000820809602205400c0075008001c00d0b030365081e64078150028000c003143c0550040506030b920801c034441c005c250081500c0602d040c5403450400319070080c010b107030240b905482c014a19602030300070503481e907505507160402061901c001900030118864100d403469207e140507000c03408940107084c541f15200b034800c00f003d803030164414040240d188146c684480e444120300c00f03030380000000c141181d882c3c02118621083e00c01f083c003524452140700030400361902c82044070b010800d5101e031080d50b0450b2230422801101101d001c1c210603100d001e42c0c0a509540c00015641c5420b5000f5540142d1080303070118040d008918414102100301c43c10800584d51281282c007546001c0081400c4440b110000e0445030402c094001c090344281954481100e0b01e4422500c00c002d00180030901422944003918210300b0130389001d0745074102d414421400115906041c00700380c03505d86400c2c011100140c444d01c0c6500b600d4601a020300341d0040040c0b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 844375854 1250 844374604 844374607
    0x418200103021908072718090c12110937240e01180207052b020607080c041206020c120c07060c020d020108090c150a0e061303080f 58
    0x5803403129036401144403c149448421003032801e54001440f0b6a07006a1102910840344080444950314903000020780e5115500720a44001500c0510064000c030340009003441e04000b00051140c143c03081c0315050a10921140034070186500801c41000c00c180c96003800610401d50055040ea5200c501c4000c074103100ca82c40030404030302c070300e072004a8030701d25106604000540c0c100c0c07500d0385060a0840c0588070030702d02942c43e54100310380101041d01198240041c65400170b00101440000c000c40b500c00c161420405901c198200f24020444000e21580300140c403a42010424082c015035a031445540c096002038141403030704941740c9a06420180940d1841e6007003101414910050111200d00c41401008542d07850f800051a46400355542c000410414280600c1c80183d940b100d03e5407000f502440d00e90803548030450100e04082401d40a5036201c6803003d20013210200300c8003c1c0c03103219190b0b10707880c1c0c050100009200652203040030148403640d08420500000c1c5449000c2c000d05a100358015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 844377104 1250 844375854 844375867
    0xa02030706020d0305090307030e13020f0706060e06010c051b010302040812030403020d081504241e0906140909072718030c020907022a041820010302 66
    0x9003440460341124005030020984064074903018007420340c1101c4510000d40c03410708580c50041c08001044807042c4602c140c00000d2400c0085a0140c0b45e170100100c1a0380c0e075402d07880c40c1543c014451841903c2c005005040020280d600a96804441540010140c01003440c0101c4008202c401380c00c0c483d050540c284800301c1d0403841003004030b201d440c102124968038209810083c0c58a00310f4100132040084020030080c82d071081330007080400005440206505041004544070840da000240b540207686020010303010503111100002440f18540b1629041c2c0c542e150682079403020302a6007140e100004d60100c1c10f00f0491003295000c4100c0043d24400303a1500312041c0c0508040746a90410300d810b000d1080c4444881c07160b00f1209102c0b504406400c2d4041d036015000060005000c0c2c4540c82c4440001c1160b0300074081c00107007844411055042103c030000c0350410202e903c204600440c90025101088a4444400302180fa00550303004c403800350b00d1030307600d284850484540d41015002d1151 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 844378354 1250 844377104 844377109
    0xd03050c0102160614010b0307050d020a0509090406090201030f110f0c0304030b1006020d0f020d0e06040f0e09010b0f150315130c0806190320220501240e030a02 71
    0x620f00300740c4503950209030010300d00c550880310302c0103070406900d403d8100140400703e07411208841042c04000340241e1140d2918405075483e01820500c2c9d900031800c5801c000400901e90300c00d0880c0c43c402d0306c080041480103a6001c003264541da041146864041014903250000d6001520000406e40122817a190300c030b0341d0f00f82c40080d050310f43c0141026400024003117a80c060000c000d64040c589042d11020080e078100070754524800300c02c00701f070092038100301519840b000c1c1194050301040491100789580e07450000c400701c100720b401220b01d51038844050340b0791501d07040c207000c0c4c014018401c040c00286030740c0c49103c030303400544000a2a10b0408400c002c5444070303251a040079600c0e080004050074031160280028200038066446522031150080c818000800b62006590b0442214101c58006841c00a00d20401601c8294003009103090007044040a40f00380c08141d050301c0040c40541d9035042c401c12003d00200c8600304d103250011b056600766200c0c111003103040a005003119002511fa401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 844379604 1250 844378354 844378387
    0x6151704020d0f032001021201030f03141c060b04081f0204080106120b0723070606050d241406040c1e05031501020a080414030307080d02270d03050c0102 68
    0x201100425603210200c17030b0180a0310075181600101e10020b500c3c040504805d000c001c501400011710140540b0422820b240c443c00d0108a01a04c07040d220795900e51803204400c01c3c0c2a110102c0708020300303124012800b454603606581c200c030010350092140003203901c12f040806000c2144c0e42004c5030b00b07110000da0080c2c00d01480c03008100014460349018064204040700b10001040700e41440380c1c20800c09481c0004003030451116201d0385410341c85d1001d40c0f0348203000e8066980400c2e40101124030083c1030100310291350300e0b01d112030018803000490780d0100200380e60520000214000b03400c1e0010b02c55040c02d4000c01e401d00032601d41651910140c41550303510803a84d0480c100025004000c2205803800b500e00c0c3e06051500340001c200425859603180f14602c2240a040e041c8402000c0c0078a440d14100161202c00c0e03401000544c499041d941c110000b0340003090f203100500701c141c0d07000c60012a201d031070710390004026261000b41000b9440540b0540c0c80780708903d06566003080004072100070b03443e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 844380854 1250 844379604 844379633
    0x270421030203070e030313051908010e0c03011413080913051008070909050a02060a110a0311060106030603050c010e0a051206040203010b0f181e01060206090106151704020d 76
    0x403401a01d03410f00320001409000e0304102503010340e000300200488941840035036022590201c4540101f003e45180c1003000032035640c03018140b982007140c0c6081340800421881ca00030001e50080000c1c0c011041000c02014049d9004035003141d41e0902c0c0e201103201c0d0f1004010055000d00b0244070b043c0d480031404100d030011244891034845150050014610602c03c80005004414081c004903115444d09034480b0581040284981d40004811000d5406130300c0354a80a0511400e54143c1c3c1d046080251414001c0d12111855028500000c10340074003d115130307001e0780e4008000340302110490300155040c0950414103030b40450001800169980c4040d4002046042d000140400e42800c0c0306260075926400b0000e4410b524a891880c2c140c0c461240c004504900d0b0002c074607a03921002e00c810445412902c0d525076941502d800441d61a800240d103501401c000402041103e9581c5e4071210b0020302081400f0000c0d16a40c0c624090140d800724054029000031702500201140c1d90726030401c2036600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 844382104 1250 844380854 844380857
    0xf07080106121418010f051b0702030c0307080f06100e0a090515010801090b0a2a0c08030a0905160602030f1e0d14010e060a18022115270421 62
    0x10000842139003002c0c02045807503042035000340305a080ca100c10a0401c0c041440300059400c01107490b006540e0f0400c901384014102070155081d15464169854a60b800b02034070901a03c01c4130040b40d031a110b4410000115408070a400c503254884c030540e480030f0100c5400c2a21188030380c40340901d0403420689641c1c02441070304000a070b005c02ca0b00c0c040b01d442e0801041d0f0148140303881c91030322900c245021201105030000d8208c200000341c0a8098400c807002e084080c0004001208219071504103030300c0b02d06110700800c03c980807200d80b0414420600554043c101c0142c00601c4440750203080711000c0d180225040300d19a800407001e51200100e40c1001d41000070403600c5580c801406e000c01c0a01074050003035408048482e1030724002242c00c500d005e100750621038041c0e422100c191a507030350640e043c20380d45640e0341024007603201405080c0740c015500b48003401c4501c0401d441c0c500e8600719a038000300404030291b0321f0100b012104101c90500802c1074403940c0c82940941e204403d0140401a0004507 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 844383354 1250 844382104 844382131
    0x90411030f060118110417121614010207020112020a090302030f07091409070b0f0f070c09270b06030f07080d14121609051c05060f070801061214 64
    0x40c142d601d89051340316000c5610345460101200310400b010070495041c0d41031203009400201402c00c6003860402403810355464050081303001660f940100703ca20000500400c3e50301041c803c0034100d03900300d1107100c80003400710700400c00b1450b00405a40182403410362600307100d8861507503038000c40e01341408824200c03201d410849060003000c0702841001e212007a015201461882c1215080350b90b10400d0061091040012804215808411b811a41604080c410b0213803246154a0702508000c52405210a888c0c288110319440203000310201101c2d007019083c0c8200d40c11144c0b07511f90b1a02000e05a180c240c003914034180c0b810081008002c0050000d0f0000b0001d240e802203000f8401c46030704c0c5407a005550100850f190b040c5d0a40f0645410010300b0f0058214403c80080580341030b80d13613a11083e00007840c01c0d041805c00f2250900c0007811030040056810700d1307a40c229051131400e02200c0c0036011540440c010311496100e051840c0c042101d401000a4444032000750f1030310081e0880703014000e4030740c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 844384604 1250 844383354 844383359
    0xc0801180b031e06100801060b0a0c1e050a060605040c09030206030c0c15010312050f12190c0207061808030f0a021f0606180305070603090204020f0a0503061e0d02090411030f0601 79
    0x40150b42c0140030100003040b5050038545613000d03d1160031004006c00c03010781410028000389235007040d11124033001c1c20042810783d1402d07544500300c0703e02c22381d140303461701c000022203003803602511403443c2c401d68540034a0317803d550800c1001d401c0903002d00c6660100344101c0703200c10010020441c10520b039807422085136155150541d440c490b08128801088001e221f5030b88038203410002c0c4c4801c102c040078144180c0c1c0d80c07185501215611421408101818080008502500402c00a05550240d034032071069041d482c10205048220303204100b40350740104140b010b102c02a9000d00260b08062050391414003407010b60f1056143c82d030b41e0342c54140b5034030032040141c141c0000480b040f000f00f00c1c07048515140785441d80e6840c0c00c19440358005140e01c4840d000110758495044910f92802c84410507212442014010075075041201d01c0f90061041c8000141c2003400d592485c5a009001411041210040e40c280003803020068802c80b0349110303844a81c141780da01489500c00c0380d140b400080031b4562 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 844385854 1250 844384604 844384621
    0x905060c1e04031a18060a0f0b0102120d23040804050a080f0d0e060f040f06030b0303251106070303050a1d070e0c0f0a080a0c0801180b031e06 63
    0x116655210107054100000c00004000c03c01120348480c0740c55000c0710a0b9130301c0100c4c1c018000b51200344e1025005e60020881078105507030007a9030240d0230120820500c0101c2c2e00590382e400c1011951000c4c04030900100748110482d802450019030b034a00e80c0c1caa00d1400c0580a441104195002c0302c40140c0400c0c184440d0030090100e4005242d1031008107055101c214050b030719000302000c2041003081c9442c2d2080151120011070300c441d10000e901e00d50b5070340d43c1d049a07500c24040d800344c4e0002904110515002d03180000540b203880800303156442e1200c0d07050f2203038a5010f41c10303c4115011505e80314800d08650b42d803400703058007901a4601152603d001d554ac8c000715a1101500c0d07050340440c40740c6214ac0400000c079103003a6100c1072100c07070890315420044504c1d80a9101804510080001e42c81c28040d80080342c0b0340158040001804074150100e81030310401000d00404a051100c00b0500064a03200c1e0070243e54802d003d41a81c014800400c01a071145903698054560b540c403400030702020342c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 844387104 1250 844385854 844385887
    0xf1b02031207031103060d0c08100506040c090617060103060b040b071104020c03070f080c250f0e1306110a09030c050913022713020103050a0b03030f0d0905060c 71
    0xd0031900c2e040100320001c0484d00ca09000c0a40124094140f0048000c00c1100e00c40d8000050130105003140c2c40c404030400344801a000840700c250240b4101920701d403041d03004210074020b4450725102d03000d151a0040c1c40030f0145600400381e034100758a801d000079107003d41200900c00380c80c500c111103640c1c4080d0300740b02c1c1c0c400c02030401080c050383c03042100001c1c5034000300948041e183c0c04100d6200c0480e84c0d08002c52140100048256103025000215074901d040c200c007034200d694410495100345a07511801c6e83e0301c154a1290b0320307050050703000056012001c1003803002e0580c810000041c0042c42100d83d420700d81c0140c03990030040740c6003282c244180b0103001c0d43d0a0040c80b040f5240d0701e1600d09880d0240c2500107805000303021341a41d400ca1030031407440c0c00358048030303900e0028003481e90b241601140e401c85075100000e0703002c43d02d8103011503074020743c6001e5081e11142c041d00940c500107502009c510554030110806401c07503034400c540d20009809101060260010741c4142d82c58801c00c008030300f401b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 844388354 1250 844387104 844387111
    0x7050a150f0810140102030d05010f03050708060c0921010e060a0e030f07060b0a0314010204140108070c0209060414130204060f060c0b06041107032c060d0f1b020312 73
    0x42c82240810012808200c40b0f40070150741c0d6003c00c5a12100791400145d140d400b451070700050540c01c2c0360003c65074030b1112801c2401c41b401041200c101e01d68401000f515604240c901036541c0008201020742802e100d0005603100740002e1041010028420003d400c40b00d0541c0044160740154003030000b407003280d000c0c0d80798503c5680301a6107011001701c16a00c0600c102d131402403e49440e011000c8840c0d40e07030500340009580050705800310030600301901d4001e40c014098030144000c03e82c0c880403a07501c1450345502c0b800c0b550300c0c0c00005031495000c110700b4100042030742d54413585030b01c551030035000f540400324007815640c10f400307120a01602c10802662903a4200ca003900d482c0842c200240c2c0e90107290140e40c5038110140c04120b440d04004540030701a18031001d40e1850000540104069001c250b5004000c58880045c601d0500002c2401d1040011046030b5800701c024018002e540000c0c0d4401021070700c900c0000900071036480340c1e03004a4500001c40e040543c0001c540300310940000c83e04140c1c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 844389604 1250 844388354 844388357
    0xf0a020915060d0c02070305030f12010b160311010e010c03090209060102030f27100e0405060f01090306021b061306050705030f070f021002040f05030c04090515070207050a150f 78
    0x100c604201c0e010800a02441d100d5040540c0c81d2a18509820700034021040619040b03003c2ea0f0b6194904614010f450344980054070082c4442e0b00005490340c0004107440c0f10381d1083e25081c5a0207101e8a08950700640c00800c4940c955840014035a030080910039545200c030651404905891140108040d4003001070003541950420803183e0014081e00044607480c4001758421014001c050b8030710011844120215900908000112202d2a410213803101c446032048800780210307540c40d02071020310f01e0b5903020740b0301080f60030f003082c0002241074028114141c00350320011034030151150700900d440c1c0240c0c3d00c05d1440000c082d0100c01c2c1300300e40c082c0341d500846038105646035013003420a0581a5800034022020000d4160862407224420304c6101040720704036205540b03030307512134403181c81945180c40b940e8824400d80000380000e00f400d0040047d800e8000c1302401c180540900400d2805a0041000e021030080b5400403541e139480111080107404804c02a500e0b281007010040c04401c0011990f00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 844390854 1250 844389604 844389631
    0x1060f080d020c010f020a020a030b0a0f0603170711060a080f0c0a02060c07050f010617010b0f18041e050102090a0806060a0501051c0e0a03030b060f0d0903110f0a0209 74
    0x507070107a000184034114080070700e0030040705110303039000302c0c2808401a0004c0d808804540000140594050564040e150b0041c04005c0490443c000720b0840f1158800100130403400e154000000c114103018051b40c07406041c0c1401c594002800090180c0d202c2000300b00410038043c107209401c2000700485038400d40c01513030317076240043c3e05502130355685004207400d420035400075440d02044028017541418200900081c01600d441d500c030384030040c0940140c01c0b0990f00c0d140420760b8602c1d007c500040554009014031424680c405591490408010010745180110f01c40460b1034004a0b400c0303c0f840f5024000060303c6070110320811808850b2980007178141d5015806100c015651800c003c0304840e000d0074090f50ba025482030610301c0010044500585a14150049000f00f401007038a05140340720380d41c2000403071005800c100490040d0b1000010b682010311802981490650086001ca23010381081c5500c90800440c0c0d034900700c005040d15440350410841101142400e007000e070f411a04410141 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 844392104 1250 844390854 844390873
    0x30602040f1a091003020c0a0b1b0406090e0603160303020709151805060102010f0c05041703120c13090519151406070c03080301060512011e03060e100e01060f08 71
    0x20b00b01409030002d420302c9201007108000c00d480c06941155901c0c400358055807003103122810303c19a581c0007198090802c0001030b6803200302c00e5040c0304a600b81c94007501c600c01d0140c14070460880501006201e50742502c2819a0303064400c85c4044250011882503005000e001e0900000a007a80d001c0b00031445c0b0103140050a01400b4102900c034203150030030841c00100383d41c640700100d000d05844201c4904003441c0007c10703800260b2050080c0103444021101581081205540559074803e41d0072140944c40c5000120300b0f1150f6190007400f1004250100c0e9a0349502c170801442101c0c0706070f40c011518004240282c00b54021401100e11171b105c00424140a0b07480c2100210301e803001003c805209140006401080042068011f00650307001a00d00703441e0343e1214401703005135001d07107152003180300b0279000001c07184210005035006012000580c4180ba14564610003d08144000c0c030003140580d907003060035100325105000f203240b40080040780031032400032003030940001600002d1171380c0c000f070949 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 844393354 1250 844392104 844392149
    0xd0c080304030503041502041d060d0b01030201121b0f0f1706210a06021c0905030904110c010c03060f0e06150f0f160c3318030602040f 60
    0xa0340d600c00d07014244195250345602d0528051902c02101d00d03100c6102080c041516114026031030070b40070851034a403000e03455a80400240c0c0d00b480384010441c502040041c4015481100c00c4c0700ba01c0040c1f0740108041e560010f40c040d00341ca62001c06000140e0880101072441d500c54100711032902241060b4a140c4c1c00300d14154404207004207014040e8008401c0c0700c04295502e090a190a0504411b90324982c0c0203280c40e201940c46420200712112340e0150110f1030120501c02c940416512038005d52600c00840144009026421088001c0400c207002865844100380101f00340305480d541c0014410b400c010001c0002480c0d500114500d40b00c103030410000c0d80f60124900c1e04038454081182d02e40030007801100007442090102d1f030410b013010501304003041c810285030f10710700d104080c040038040d150701e01440609003e0750100c80c1c05424a09500c404c40c4042010482d608582c075010115800a090340900100b0340c0c1d0040300c0d92070340041c041013020840d6541002405004d0a40c0700c1ca41d200486 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 844394604 1250 844393354 844393357
    0xe0d0819091710020f1315110f0a061a0441060f0d020d030503012c0f2d100f030c0902160f0b19050c16052d0d0c08 51
    0x40758100d09a00048035905c5c00840d50a6a2180c400419010420303500c61403401e81180200640c14085602c040880e21f41c20340114103603104a000f000146240080307500c03448003502e80074010075046401c006480c029520355014a03000340c142c072940d81d0303000c10350450700a268280c170840304103049a100710f00315501460390f070401e500b004046501d8580000c0540c0094201c11200c680250f00c201040071a8041507000320155040700e0407000020240108220704c101d00d075004c2c264000041e10034100042a02600107151500004001014252408000da072202c1c120303101484c07400f41034015400c1003106941465400060510f0580b1140c086107540d6409104405038083d111042c0d40100e1501741c040c502c5041102d049411010014204a01e0b0508644580d425035840c030410a6820181c1d0b401261405846e0295000c0d2282a290105445c04401c00815084086440d409205c032003038006000504200712011001030364000c190b002401c840e181199180911003807162940c1c410300031450840 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 844395854 1250 844394604 844394623
    0x15071b03140408011b090509040305040e091c051803162c070c02010810030206090402130320010f11060a020c0a17031b04050901060e0d08190917 64
    0x401030310400c10700c950749041e03004079049181ca0b9840d12111903002e8044600c038061400c210f4607074503546611101070143c0300310202c4010300465800c000400c81c0d260362070310056200c03000800b0b03500103415006503410202014466000082d60100f10050200055414840c182008400410b11408460301c00e06888030300b4440c00760304104502100c4880188403680d4100303402200102d4030180351130a009401c001c03818009900042880d000074003500301402244003500d80003422181803405040401c00607501c55242804004000780d40080000c0c0444c007908000180d4000608030045440001040200d000801134100181240c2e400388100d0045803c6030403800040b405070b5100000592145070000c440340c01003500800076450020078408102660080e00012030902140e07201e6003c2d100f00e03016178007e0960150491004003c0a1b01070f0460706899180645243c9a8020710388070801c8580001400361590881203c20010103607000000001a10356040b04d11081c9000e20741c0a40d1b00d90005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 844397104 1250 844395854 844395857
    0x405060601030e161503110901020606150c030f030f07090308090d02040b060a0807030b0a05130504110d140d050c0a0f0201050c010204061e0f0f030b060403020901030515071b03 78
    0x10b00210043e04424007210380002c2e107110030080c4866640c403460114072111710002c0300003460030740e214841c510380504440e140788050303004051644401c010421991555001c410b510b010070848210341c602c051014103180c7c1810045180c0382d1900c02c14549001e1801084101000501c00c414000282d981041d10758a1600fa60564100080351003c24000e100c081c1c0c403e40c2c02400407458182c0d1950007842644a440982e0303007807004500140a0224a00b00390040651125442e4856201c004080e0b10240d445401000c000031005100300102e0301d806500c5100742d4424070801d612861b1008100804091a84145040c9282414041d030303039615102c4c0300c0b40052460081d00036070415603114400341c503480c03c0014000c540e680e42d13030540504280114540030001d403c01c8109501d10034049d920202e0314441d95160b092000d4800c0d80228000c0a088074125440781052102101580340c000700d0601a6229200130144100720854031208014010105410001d402c41c03103000f1041207003244203210303906 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 844398354 1250 844397104 844397111
    0x10e0c21070e091f1e051f030c0608090d080a0213080111091e061b07150305071d0a290a020d120603051207020409140c18040506060103 60
    0x48042040c10400558400b141c80740e0a80305000e201c04020070054020598071082c01c50156011400d6000d4900485e0092004e10460b668201000f181c2e800969112042c10741030024140c00300c81c16800449190070a590704c02d5045d4060000f140c009100302d40240aa5000741928650800000c1600b180140345015160f000b0880030305034094846000301414080d0028043e1103441c4d50b004a654000d001e800d4481c01d0008800300c1401945108122602c40160050b803030a4844250741d4a5070f5001028008075104188000529000446440c038031811603542c00f2859080410000b802c01603010072500c41d045074444c552030a80e5401c030060003190070000d05040c0040366a0000c08503940004100840b4460000300e280580b03038040b1701907681d40002e840391800f001c0581c1d040c4003103031740e503001c0141980c1c44418101d0000c0212405012414401000412400000c0ea220b5032002d0544c1c0796034085500c80c1201480724640140c40c01065121004d0091452500b510703140e5454001a003482d052559 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 844399604 1250 844398354 844398409
    0x5130c29090f031b0f04180807030c0f0609030807050a0e100201111b0607020d0c021e060a120b031f02030402040e0d0806100807021b01050c1e010e0c 66
    0x940c2c59100201c0440102561074541010000d00303078100b400f64100c0d1084d01604240d20307582c0750910585805c0c1107003844020380412195120403d6901000d0306405000440b0b1494000503030a410880400b417040318045020800d03464041c00100011303003544184a0f00707205110031980d0007005094407003001c85003807502070b2201c24180e0041c640b42e4000b5000c0000054110700718010754000011403c600070407034040344e5036140c00f2a114020611914005480001c146001d0714215001ca0f4040740b48200300c1d000440e25900003000d56110f13100010102e041c503440b4407071642c0c0600c03070045058400c2e00070340804920256600924403080d180740c4100359000c0045001d5441f1940310a11a0b50181304807903e501035001c000e4400c0d18100ca115103e10450841c1c916242d00c034902c40ca020300032503001451000c01740c415640404641c43c44050400a0900c51405d0b40801042290103202c1496051100c40f0001011076080d541d180305e95115640c0304540c140c5042e101c030215907040d2824070300300001850 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 844400854 1250 844399604 844399609
    0x20606041508070b04080d030b090a020304050304170d09080715030519090813092702030a05102004030c060f0e03010c1d0a030c1208090405130c2909 66
    0x340303180c01c042150f1141c0c15010a03a03a1642c00100140c60880c0111290113030302e454100e003522021260a500141d01402180d10140250055500207200e00306980c1407070f40f03508280101540c075140d01c1c0d00c9907000c4040b15200300e41004a400c0600003c4000d42400380c105841020400321902000d81010364079400a40c50302c07031a203010021040e40910034031821241c0c1c107000c0c40d01d801c1184402d51108491384d002401c24002d11503442200c01d000110003d000c0c0641c54110080d1034032205903014010541f1250000d1002d0002c0d01d2428451100012008440c0c44201c0311241e0b49200d03844609410031050000c95022070101c4111840d6260485503502001800c0f51070b44280704060390590b0a281000045903008407010142000049120140c0b02c14401001090805440040d0600030680e030280400200440c4841ca401d0040c240715240c1014030740468100c038012500c40580c1107260300c0010812001105030780c0200900910b07400d0310340030500d0300c82a24540440b2030700040b000040c0e014807038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 844402104 1250 844400854 844400891
    0xf020d050901090f090c081501020d03020903030904090b090c0d0506011707080d0206061e09010b09120a060e060f0f01060e0d1506080f0d1d0d08070f02010e040c02060604 75
    0x5203921322101c03240c69659403014014018600d034941c003240c4110000b401814a284031941c010805130b00402c541440154150002e40c000541c031130b00350108024401641e110f174050485428031800c203800091a04484c2e8034101480720120520441c500940304001c920001041b80c15603200d048000c01c0c580e000d1b1307400c40c42c1400b1a441300300140500003459103204e4010400c2c5100348000d40c2c08880300c00d003070025003507458000c2c0c0000340e000742178034018004014204040c150801d0054015100015000d18451501d0005642260f5407a00d608d00c0c806034007002c0c82031581201a494141c02d0380d04120b038244200300014000c0d04d0400c507124182c2e8129035601030513000c2d01a00b06200403503940c000703002c1d07001130601d50080c100180309407026400104d00019038592081c910350f5580c102c00f034900d230325aa00300720b100b500381fa4002c0281c64203401081c507000050659500c181c3c46281220190300c0050444014180b940d8411407918014201c541e0300412002d90103c0e089900103070072050f0b91500d030001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 844403354 1250 844402104 844402109
    0x207060f030b061210180e060c03010b0d1d0a0b01030c0504020306210c060d0b01320702061207121505100f0c0b010b0a020105010b0f09120f03120a0c0f020d05090109 73
    0x211810031200074840d15440100d00804480c15509149e0743c41550850501c000e220719450001c1c204044000701c4015404507400b0030f94144104101e0380005030152901d030030094283ca1708509440108108030306903034a28000e003003e0b00d09506510f003410004280720480c903256000038442200c020403050052025114544009003c0b43e11201c80b50000002480200034060100c0d0703103440c4071040c208804660650070b813059104070384803040c40100700c900e84d0002c000403a0041d40a000031418640401b03101440b451480d0f83e034501d14004900e01c00d00765141c0440140c24000b09840500041d1166100b015450320035091405d0f0242150004031903d00c0b90940103401c0c0c401100022541c200200010107045510b54024071060341c861881920a20504611140100d81000010514200460510703040e156510a403142049200401800d691009420001810b4203208000c00b41d203880c807a10407241524038001c120110710480c040c0d83c90760001524002c0c0139010440081b1680302d07101c100c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 844404604 1250 844403354 844403369
    0x50a0206030c07021003090506060f01091a0a0f3b030109150e03160b0702030705060a0518010c02071403010608030c06070e0907120c031107030207060f030b061210 72
    0x1d5901d48101d00c0c4442d50001c1c60202d00c1502c034001490002442030042c007440340e8100024114503298001007201001e0031218041c14047c00a400142101301034010510921034012040c1e512402144e0081c441138070764000e141404081156440540c009030f9101503a84082078502c0c40510f4140394030441081c1664495500d5820484000e0800048840c40b4032400c2e0901400c0c000b9a045603001070300d90140d090000740801200c0081f40210f440031201c0c45e0401d4060056070700e01401601e4890500e41d00f11a01846a525a0240100b52003403d24111403140d40304001c020040703080c00025124152032160f40381c0c40f4000405408640e400790301c5800100b5220048940c0c03604400c3c90503480300800c486010110f00140c3e0082075500304480d040e441480591380e80103c500c05440c10030002c01d5510168005c055951001d0a6203600b1036004008590298000b04280ca26101c8004d24108400d41171408250a1598090940d11403000361a05040700c0c030180595595030b0510102c0919403980710340c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 844405854 1250 844404604 844404607
    0x31e0204020d0e01113f04030c02030c040903080601080c0f0c0c0f040b0904080d060f03030c0528020409080d0903050d0c080c12040f14010c0815030703080304050a0206 74
    0x10760054581c1e102000c110f41d01002845542018090b500c100c0c01000c120440030011070850010061409400c014400c0f07504107013480340100808201d61200302110b0840100e00440180c03000c0d890100b20441899004a0f02445022844d50b07005100e000e014007c0780c14080040045103030402240b054a11001980064503161074501c20b60964414038034030f034640200c500000c084403904060282d40700183c0042e00b600360fa80c6403640c1f0302d586a441841124541540c071000400c03403024101c09a00258001d0b51041c85204060034910f040120300340340f00c103e1107850b0190b0040c440710464000c64480d01290000b405000d9030601c40324610800c101e111225181103a15420135401c8805031a105011120030044150201425611401c0075101454000421700c9800f502e003500580d6203a01038400c200d90002d5802c9540c95101d4099403142c85c0f4052394450707614450303403680326203110f40c0030900c0040d20302c540c00705c2c40101c0e40302c84443c0000352105500000040500c00100903042c3d0141c7d018003000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 844407104 1250 844405854 844405867
    0x1a1501030e15070909060b122e23040506011b02041b0309290c09030f060403051c0b061921060501080c122a030408030906010b0a09031e020402 63
    0x1d00c440d0043c05864405445c104020945e542d007e01035601c20001440390f0102a2250910004258019030701c9110311b240c01b40344003204003d0503180700c0060a0b110001c80e08011000c01e101280e00c0071500807405189002e0400c0456a40842c0080e04044401c111940d1942a40003040107045912030f07081e640c00b52900b18001559240d07000040184c0510368412801c4120280340406070140c2c6842d098894094011401e080d0304203004100345a401403c13500f2a00024540da8100360f030444007900450804150314401e482909290414050740d9801004400300c080d0002c0d001e030084039181c5041001007003421408501601101c480031f4802d0148050032809000300744060400d500030b0500161809020407044c1140c40d054a5080702105000b0100341c2e40c2203103c030301105c110308065804814041050340000501e800640c0100c1c0669812a5649001d00340c161074a141070b881a81801000c001ca5100c0c240d2007940402940e522021040b908070b8000e00d1403c032032191850203940103200044c4d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 844408354 1250 844407104 844407107
    0xb0405060f0f07020303071b0b0a090204180218150306040b01030303140609070c0c0f0303090e0609010303020a1b05060d150602010209060d1503080c03071a1501030e1507 75
    0x303144600041501c0050030381d02e040d0402000d0b1020746021001d0fa001303001250700c02d801000003081224a41ca000c07109030000b03441d5020700b0002511455049a5540070003000e609250050b15a078a5074280107280c5641541d0101320580e000b5048a41c0c0e21180e800401d544c1440c00b4200016031000070304a071558207203428031107020344081c84124003291404003018003040101090500c2644018583c2c00c041d0b40c1c0c150184c1da291000c4034122031512a545010036500300074041e04000e54007039941d4184407401e000084421400250032180300300444401040029030028448241e5940300810051501d660380041d100e5403900d0300041d41c003c001040240001090303500c044200c01c2c800602ca030180380d64404c2a0300701c0c4101043c842e0414801c110300d0b07070145419081400c80e642c10ba40e2401c1c1455490315060b4054210950a041503000014000309000903014000b0752080c0004103910607041010002e02d007021240319079818940c0342c0504840c1402c090052054030400001e1888a901d0903240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 844409604 1250 844408354 844408363
    0x2040b0a030b0f130f150603060e0a031211030c0f040306050103060b0f010e0a051203191707050f040927060c111f0b1318020a090e0a110d0b0405 64
    0x6000c20110f81050010f14031800744569098080d41044038401c0d00d480545420310364040d00740b06e0380e014540399170300080000c8481c411074024100030000341c110107170380340f500810b075200340090425298100490300340104d0280040301c0d0440140050980e0750019a4800b052a00666001401e41e5292030000000e0100fa9000308060620031142c500c900c0c0f4125006544442841030140c4c1c000f81e4014040c000d42c14034400080c40801e043c0122410310b03507004e0040c20380d880340340011000190241f100c01c0102003101515038004005040c140d040119802c4074810f0f6020f513105141d19151640002c41aa4494030514100000b800c00924800ca540d81407080c00703000d0420303c00000501c9000001b0b840840481c41c44258101030f0218070112101e40c1c41ea50140c00c0510362580d100740c100310040013444491080510700f1980100b410000d02e02c5004000000500b50720191041d420040c01c3c00d14140041002c0c401f00d54002d0b00f00782100b400c0380205420040207400100000329000511040c842c0004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 844410854 1250 844409604 844409611
    0xe0f0d1206091a120307200a0812031311031603050f0705090a3920190606090212060306010602010b03191505040803250f0c02040b0a030b 61
    0x10030034402182e840603080b0480740c201003040184045000121143c0c90a030303001c0c040c0b96058100b00c90030702402c2d4072140710156248140d01300c0d070b142a10030265182400c801c100f00410b20f0101600f01040c03450b203d480a40700c0100100413482c50031103440d00f08000419031400442c8090115030b91440d41220b124088030003404107172050700c10380b020310b08030f9000004c04c08180d40c005003940b40c454940075a450043c00180d860704100e11040d010a09010790790040711080300480030500d000920341d058001c1c0c0172090450040b5040840040c05444184002424a00d642d0181682072050001424854010042034006011990000034542494000b00400c10b00400c4201c1c250750250b681c8600903400c0700c134218180740c0c0640041c0b044036010801b050b180008240211441981d6661f042c09280071900c3c111011100f00c000030061001c15a14901d17202e06540c1c0d00d001c4444c10f080710101c060882d0480031041c01c00c120b05074142c6021074845070030101409101030041d000490b140d02e0720f11803015040307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 844412104 1250 844410854 844410887
    0x81c031b02031305101d060405030a12030e06060a0b1c061806080303010501210608150103051b01210e010905030301080622060903020a050601031b050a0f05040e0f0d 73
    0x180022a892511151440c00418944c40742000008280c0b188100042c014078071a5201c7c605200010712510140107404034544151a011840c10006001074215011050b104010360301410070000191521482a001e0702e0b4014181601e440201d01c280c0750303c206140544900c50706040c40050003900d4901c4410713112407500e400b404181e485442c81c40e030b01d02003485a030b030008801000388008405c8203c40400304a2100c0f00114a039600da500d280d280142d02d41c40054010f003802e0040090040a10114409034904a02c022401000400003000c3c0c002c00001c03991090711031608070104856a40c02103003a101c07240b00a02c00c5100303d040407911303034009129011883c05800c00103800399520351b48002c18940401e501811025064030f6030801403040220440039845500540d001080040014a000b9031060302da40000d1000d0400e40329a424681e070005000300d10343c9106000d031000d80c1c0c13201c1d000d88005990014038583c80b00c5145141c580c018290080a018038015400342e1680b01d804400006c0c400e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 844413354 1250 844412104 844412137
    0x108040213140709081f0902031203011404050a050f3903010609120507031b050909060702010f1a09092427061605041a22081c031b0203 60
    0xa1700003591303c0b012030100300b114a5000d952950311510303803075014210305030025044600c000104103070032405034400c0c4c108680041c4c082403903110034035081c0a49a071000c07950406014030300f44049440401d2001802c6403190030400300e4800b05e8904040c0c003107003959004480582e000f40990004000d66442809200c0014000500202e9000703051180d000900703030301c00020300c61a07245440d8004002000c000401841d91a80c000040c543d64820107940513040340409410282007025010b070131904850424a079003418100c51041e4203602c80320f100d400c0d50003070b5400e00765503450698a50030128191108403001603509824100e2030102c0714180d104080e018684e48000840c41018407140c0e04504100481d036101c1d10007e01400b91014060303c003054281403d905144c1c0700d80402181203250301c0c2d60b28040c03002040c40c0e8014a403601000e0700580303e00c104542c1039400e00080340e072107110038a410101006d404002a94441c800e60058039203000c034001a00c94461040e80003500c83e4000e0140c6031400380c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 844414604 1250 844413354 844413359
    0xf120a05010f0608010b0c2d0601150e122404050606031f020a0e041107061d0307030c030e03030d05060907031a010e0a23090c0403110108040213140709 67
    0x8294040c0094034016101c4c012241e18001e110560fa500c001060f600a00030580714000c00f13058112120205200350070070303502c45c80710f000001d46003a1050f800340c92101041500c4050103500080c0094030510706540e100407081912040d207103021420443c611076016600d00c03001c4080d0101800900440c0710f50107845164480c030041541d9480303039080c620824982e035100b604a00e115a40181000185400d2945440544400040445490fa1885042c1200004d01d4600300032085c4100e002c13802d02d80030b031000c2031001264070555038056580c0042c01d0000b9003015a0a25011310700040902d10000c4c01c8a58a40d07540c0a03150140106655080c007441c1030001107003031603000e40901c4c042802e1110f01025030200010044500c00b0100c2840340d00960000c0c0701040254a50340121440e9400d00d0b81004020341c400c040c0700c032041000301030f40350b2044180414000281008500c0351451401d107003c07e8030b51680d000060b41c0240207009040b000f460540d00044800c40300100314070440c01c1d501c98a14490707 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 844415854 1250 844414604 844414619
    0x31303120e01021002070227010f06050f0405010507020d0605010305010f0c112a03030d0509060c040803040e062e110d1407050703080c060613060303020c04110f120a0501 75
    0x1da1250580c0d0240e080642c0800300c0c08440d50180804e07a00080000010449180081d070752040705c240112403013001d910041c00340790581d00f6610024912464540e00d08118040140d030a80241d00600d0304001c40014650103542d00d900203003940c3da0b041070040240c0d51f964600180289401e0030041c0d8140c1c10f01e000510b02c64061418240c2010390000908400da680c4c0b495031985005034903200b013180d188031880c400703035440400242129001d600300c0020a418200d81d07032403503c0d10042940510100800060101600c04025102200d6601030220429125400014900e4100000c0f0180050b25a0140311000701d0003102d05256074055291394480030202001d19849444942c0d103080030541d00340b41d048840343e280b801090190b00403420380f1401d684a03542c04545a01c1706401000700e0b8004d006012003071401084140d503044000c28100280c0c3d10710756010391a42d560f040c406100e1552004800c500c840c03128100d40c036041a02580643d60700b0700012010008209032510b145a6280000108148 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 844417104 1250 844415854 844415867
    0x1060e0c12010e011d060111100f11070c060807030207120309030e09060a0302060315030114070f17060603070c021306030b0a0509280b0415150609091104030503130312 74
    0x20390004144001c0000005c46040c6900009080c690410051140724901044203008100e0610003107030020416444801c002c400303039441856005c2020404010500020f58100b40c08812aa000e0414106594414805800074000d008015010303d001035454106561b05a002041c998440e032900d0110000003410700100071411204950455050700e01072000d403030603001442d48000310324401c1d420580e0500c003207400d45040400e1800180725250902c0011342d0001084080160303d0310b03000d0707915204000340c003010b1a00601001c0c00313404000082420a4441e410308050181c02410460035002e082d10400c00525080c4000e03074400c2c510703c01140f26a03c6501400d070007485a540100408601d42e881040000a0420001a0f03050313468043c8001403102010075100e1030080b1002d40102036802c1d203401c00c0d1201003420400c0300c40410000c0c80394680009190003980c4015100048040b04014507212611a41c0c1015050703200214203113825110140d4040e0a40c0c0c407444d0b10741c84907200c0d05403e90b4507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 844418354 1250 844417104 844417109
    0x1030b0f010612110d020c0105061002030702010801062006090f070b04050d0209062107090506030c030715051e07050d140d02090d020607051513030903021201060e0c12010e01 77
    0x2051443c0d00100581c0c1c540120092000c40b04446142c00030801810003241d0140708a15410313512001003044610740302d00003060740304450000d545030800c0c0e40d0008200d5001405542e05200e00c0d10f03100c0551045410b4010f401845940480b095810850b4510f590b4450001011f4182d00c100c140c04104003000c40c3c180c500b194000303890301d000d410050b07080121049000b40800d421013400200280795001844d1a2003516440d5000b4101c2c042c204143d520603580010080707402903100f40481c00c13490310002200002c0342d1400310480410300a80c07a04460070700c87e07018200710740034041109045120b1000e00805986200c0e104550303200131500e0050700e105003111601c04403080e05101c0403001e124190020091008014a0703901400c10b2640010940d40140c2015201c5038815521421403c8170f403600590009030007514090b80032810340d4010170000c02804001c0c0600d0020390400920442500701801400d802c01d601c4203103103002c800000040c3c00c4031003400500340040000058a002c0c5802c030506 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 844419604 1250 844418354 844418357
    0x503030a08180109081902240601030b01121410060c2d0f050c180c072a080607090603060e0406180203060a020c1203071e020a05070303050301030b0f0106 68
    0x1e076951030a00c41e14012a010480d2a9501e450004c800100f045005210741e94028581c9400c0c42ca803920000c0c074000c05203d000d0200f544c00110001c0f0840f200d01c0f4107a00c8242480d021611a800301c0048550004044000e45040e0400081503585000561f501c0d00c00e9030301b841e0105c17040f1756030002200e15a40300f80d40501244070000c08120204283c0180b4950106010b0488124a00c6e0396280c59070b07030039541426100350700700c0c02c0f0341000c07481c1000900c280610900c010f10705509144000d80140e00c550030f00200a040b0040d41c044203401500e9202d0003c40003a4803003c50542c2e80c00d929a1a00780494a000004000700004100b0303a021b4864482594a0100f1900c02030743c4990f0396400410400c002d241c4c02d003410703100000040e0f9082202d01d200703c080d100c001d6210348084640510f810b2061401c180c200c94181f042041b403a82c4034840303000251004203a02e400d004420f0081c3e00f40360803824050300314014801c020051603080780013141220b12a14120000b642c03039504121030b55600780540c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 844420854 1250 844419604 844419617
    0xf0501030f11160318030305040501020f0a050c0d02010306090501170d09140126010f050411160201051309020d1d0a17031e0109060e130b06091005040f0906060503030a 74
    0x84100c010300ca14034100c0d413190500184c081d088214000707104a0b02d80c400c900080e0002814401075a052142c00280c0c0c5806008005400c0c1544c0d40b02d4403074844828050265084408010a680c801c0c4c011710300030071420300c0801c000e50310744140c02010755102000210307e109960242001c944205c0b4900200c07440038219440b101a82001140c84122211188441e011071600c9248000010201c0034000c0240a80c205803c0d4a01020300065940201600311280b40038800d08480d005903140c40301038a50709180080e551074010150740a4900c2e103801c030740601440406c240e03502c041c0c558411102d224800e40090907403e01c101d0201d585180304903004128000000c074110480803c032025580015120301010311481d0005249900d000c0d090b4042c00700c094890f00100002d20381d000310103400c40c41401002c2e0340c0f01899180c1b014188000b510a500559a5100007118112200c90410103000014001d204100c005010480a07042c64a010b489452403e5000106031030000102d46007682e558aa00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 844422104 1250 844420854 844420867
    0xd0c080a0503041703070f110a150b04090519030306050d030f0f03020d0e16081216051f05061003050610080402031203012304060b070b070201150f0501030f11 70
    0x2100d41c0e401c0500121050044101d03a03000201c21000658400d20069941090f078481e510001000d0314514000340c403094001e02c0360300c0080b42d55a80781412072400e402d8007064240390b142c042401001e0039000500305000340403000e520700d612190288040c50099134103000690b200c03030410681d00748002e00100491001c28842644c640101d40ba01c19100041c1001414100c0d086040c0f410748040500106854100c1040c005054100e482060060311000005051106c0d1850b000209485080360210800d01d401c02c8540c10006c0c2084803822042825a119401040c00001d8001030001030f42e000b4801c0d0291841c50400038481d1003514030900d0300404803140e0160182043d210700c14003500c1607030180204030980540300b1101d00250300801a0700010310802c440c4840e000034883d042c411107031141c0d0401700100010181401510091072f0042425441604c07908026801003450074041c402c2c0c6000442c00140c2c481d1031011000444e10f0a80f02801000c4c00310003024211111603040c102e4014007407114 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 844423354 1250 844422104 844422107
    0x602120a050909040c0b0a12050a0c090b1c0c08011503090203060a0e030702061803060a0e100f0b100f090902030402090c070c1802070618020916140c010e0d0c080a 72
    0x4050b0480d000b0301c040c0f8001a100c0d0300c4c86c241503106070f0190011078800700d4104c4035410b01c0e02c2703801e5101914080421503604040b10017410005940b02d904683c1c103000c102c4541d500f007032460008001000c1c01c3c0400120315490030140440000348200c400404003220129019030090040910182c2d009001d005140d03203800c1200010309111900040070321080c4044001a15180020a03003a06204c941c207400c4900d4008041c0313041d0008101c03000300c03803d02c00c0341c900603640081c200d50a1507101e000403640c0c0224000d181e004010a07601d20354459465204e080309140c00216201151070b01e0b544420000e5203808000e000d034401500c00a4122403050009801d0403005805400900d104026072407030281c1c1d4030f0400e16003492030300184115640c0011010104002c910070200e00c6c5c06140041e2600c1074954002034001c4400a0071301200000703803200f4010341c911941c40e51844541c603209250321004d50ba03103164000d100c0c00c40b818910f4481c040b180c1d407410380603424014980c0d40c04400d0925211300c4100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 844424460 1106 844423354 844423369
    0x30c07050a1a03040f210e03071505040308070618060b03010c0801030f02130b0d140f01020906041a04030606080102070b0c03090304090e15100602120a0509 69
    0x58074208440c06903035001d504051910005007460034062005680001400354000015915813446d0b9003000920f42e48030030071340450381e00c40c1c2c07258400c1741510013161004001c07800c107000401c0001e007000c000f4040e1300d01c140c5020926143d03040408076012908102190007603180c0e04c0e07501e81420244600e080300111880c02c40c201e940b4646071401c0a800d4204040d001d0104413900c65561001604850f002d0000540640c4085400c0e043c03004646075034642c082c040c0d00a6131003848d81a5814000d07102000c0c1e00030250f0303150500c1c001003503803034511201412010800a03c4000b012070303660701c500002410040000f60340c4811519040d000d5450040ca031a144007810700c14041e0000000040d141511410300c4005088000080d666250025828074443c1c17800040c0300f0032004135200d04100086640039003c88942c2051780c06207200e140150b141000015030f0901070106a07203031032013 = true := by decide +kernel

theorem cover : BRFrame.Cov 844244604 844424460 := by
  have h0 := BRFrame.cov_init 844244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 844244604 ≤ n) (h2 : n < 844424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
