-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2160
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:50:18.289231+00:00
-- url     : https://prove2.me/submissions/af9815b9-8b7e-4eb2-b5a4-666e1659c9dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 388309352 ≤ n < 388489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 388310602 1250 388309352 388309357
    0x305071b090b040f140105120a150506240a03050c16030801030201090b0408150a15060e09010b0a0f180f121a0c0403060209030703020a03050d02010f060506070204020c070b03040305 80
    0x2d0611980c2000c9103501800405d00c104504e00e40031803884007441e03003007200b401240091082040000e01ca00083e200118081d448551030b51800344e10042100d040000c01c100c06032403c03246a414018004012498014404040303031101061420086000e6840000c4031400e4001e82070310030180b400541c0068205644814440c0c140d078400d80301d070b80c81645c441c2001031030b5000f5400381603615072000179a41c225071190071038141d101c4a1058041b0345401d0404511141400030790003c0701240110031204c04600e00348001d28091b10300b03407020a0070610380800090200514041390740900c262814443d40e2203078100350b580040c00381002981400c43d69254590b050107100041031f124864402104007201039884216402500c00c0c44015007003a00f5522030100a5100c0c41d48240c0c1885a201d00000503210501802d00a50045018009400b0305000290a4601002c00d0240c8149030020510455840340261002260141c80044c2c503030840740f2800d440d0071515045034031034402c00b000f04410154003d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 388311852 1250 388310602 388310621
    0xf0c0b0a1706101110061706160807030c020c091f08010606090312030b04060905090105070206061e030304090212160302030108120f07020d140f070e040305071b09 72
    0x5403201410140030040160394070694007181d0012a01a44100641c410320001e41c516039560142e0300c011003500c1e07909007160300070b0f4803041583c00b4010b032042c0070307402c103014040e88210001001581079001c2c003002002c490700100204140341c3d0780e41342254258400c0182107680100a080941242440203c4041404650007030440d0710303080e02400304000d08103000711000c4078115242d4420040c11035654100264075480e1803001c15994401c005903640c0d803409024000c109034040051107041c2032080302e0a407039000300100103560044040c00110303281c1009403003640c0b00c18101248201040320010f42913100307540c807240b40c540c004aa1381c0705101c0e104030340391301803501041e076541c14820207007040c0c0580c0400d00c02d40c079051304040012920503003854010110f80391619140780ca00401a800145280340b015010384001c030740f060010b04411000c100c4641005029401002110320b88070f42d14405001c0100010104900840c01c4002c010300030182d40c030202a040101a2241d07200c0308080002c100000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 388313102 1250 388311852 388311857
    0x2f0702040c02030d0e0c060a110a06020706150b07020306012607170706090b0f030403050403021306030b06040603170c0312040516060504050d030e011803060b0909120d05040f0c0b0a 80
    0xc0c2d00806900046c0b001401103016103010f0a00d40601403d80c0d16044401918440c0c1c0112180c0c240015503510041c00d038103100341800201c0f50940760b111040c0e238046400200c40601c0400400c4056540025002c2c11100380d4503084000008081010025042e00380070702c1c0e10741c450740e040400e414000900d000300914082c801c4030400703541c50780b04551010350740c454124401410808208c09403024002941c0c0203002e401c08901d4281c1e26404030750b04100c0001080006981c0303d406004000846c03482c070760410340881e0248009030640d16807820190300112050b5464100066024442100380140d0703002240e0745180255524080c04c1c1035403502d08845140a021850b1600030483d60300036003d039025560701400c0502515120b95003528815440200d50741400342c140d6035444025a0070f21000c020714410140400d1001d240d5081c00755001024002d0f00454211101e040c403144020002d59802002c00741e03000c180c940322410600c01c15880c1d00c00281c01c4172440e880200e801c4080000500d080d1440d60b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 388314352 1250 388313102 388313111
    0x13112107080f010303030c02031204032c01020c0402070609020315010e0604151806090609090c0e07141608071218060f05071502040f06020609012f0702040c02030d 72
    0xca50700001100e03041009542e4500500101e1300c6503010b5907006015004503490280c5a188080c000c5004641c220009442c01d00500c103042a0304680c07100c240c504900e1480c410000c440040c0d110b0301802c00312400b465000c00c49405015040d0800341041e60003600382d81c00c031105a41c1807003c003a403d006500840700f264021650a0a040c070452000701d62440103503002a040003051101201080385000301c3e130b522044042044da40c1072050000074900000300062441c000c0c504070b40390b815154000182041580100102d403604001e117040440d00d1007001c256034848109a8000343c086043c00a801400c0206420f400c00008114504c0c0100e00350311240f8031100500c041c191300e014940035050001c1e20300c00303940004502840252016500ca1101028051441d0400904030782155200840d03503003a01001308003181c0c040c0322554026000c0c00007484100c2c1c1034801021900041840342100041d00c14410540d0405003055485099005000348204031381d01000950300e80150740155045840c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 388315602 1250 388314352 388314361
    0x14031c02150714030402131d070612060e06120307050f060109050c07031e0909180b0f0c040315110a0c0507050102030405030604060b01140f031005010815131121 71
    0xd01155540d004042002c5407840c0d0301c5a09101f55118a6000320107101e44409840b10492072099818031401450b000411100d0301e850301c01030002d81a500b90030034a07883c000040c0034103c0040a010703840241035032140e040119141d4101e1461050380300207020780c0034820601000040200360b9a0407070b200c41030107000941b10848885098460b2038802004901003099032140301058040e9607420b44014106001e443c0e54619415060f1805607090450341d0010140072000c00c800c451009400c5415620603031014a45184170f2403a62045000181c2404c0c3d0b000840120844181c00800c00000451001d40d140c941e44480035040301003522040305d043c0240301c004200d6502c0001620b01702c4c1c0b80103006044030307200c6441d074100401d14124003070f0401c219082e550b1601c400280080c0f00384840ea03058140c2c0c0746414800035005030007540190b81044407240500004040346000b60382900400c9654a1000a0078030300c11004140d810420302c00c141003c10209003c0070b0580c1c0c9085641a00f0b02c500740c0e41d586 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 388316852 1250 388315602 388315607
    0x3020c060d060602101a0121061d0c0412080f070c090e250303031e0c110c01090f03140f0d0216290d06031b090c110714031c021507 58
    0x1000c11b9000e22050041801403103580714807921400c12000010041c01a0003903841030007a152140c00405400d04a1059a5011841d00445651103100441c030720741418284005040700214440740a801300b480411441100e640c500215488aa441600404181e40d1240d4840c05002c0c0c0d103034008110300034240c02ca1403103080001d00d505030f4038503401c017000e2090450b502a80104040c02d801d4000d44c0d00c8002c0300070403000078810708103945d60303940762a41c01e0016641d0b080e00d03050f00c1859140c10040c2c0014100038964012a040e015a0b0740500809680f43c16190010726242c1c90034600182132090281619000380c02180442401c21010b1180307000310b448003104180302c21000070745210000b00d50010344480f54580c01034001c00340041c1c004644a40ea940317880503503412408564490080070780f010040c2640620a2070424002400c0041a01d030341c1050080d142d45c01c80c440d50190503080321280c0d440d81da040c0300c8029030110840703540081c860343d00b100940d50032911090710210840b01e80415280ba0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 388318102 1250 388316852 388316861
    0x607080f0a09030909090302030912010e0d0e01020312010e06310c0c0503030f01050f030d1e11030706060e090a1718090a0519090c0e0403020c060d06060210 69
    0x24032400c1909840d0315544a03420060450b01015010092a4240401c062001e4052040b005000ba4011030f240c06040c001c02140680302143d00c0c032680e24024503105801008a0610b103031000d2414015005d022000041c0d0851280320410908207502c000082043d084080c030741c03809100c040d50060540101150101ca0041d100e40c1080b240b086480ca50103140a0960132a010760b500b0b07031038041d10110f4190f0f54280b540d04181c0e600480480130f40b0061015091401a0340c02c000c9089005000d000310b0b075640a82840c40354200440004001000140403900440d103440003000103070202d82d954410350500740e000303150600900314011401c03004a20144000a062140190000f88214034984200c0e111301950740513120300d5440b0028016108125a01c08081c5481a1044440891149440c0060240c0c0341c5500c418204540c0c030b001e407044041030300800000c0503100e000b601b503140c2c4e07103650030246e03c2c0c90002c00702036620000000b072005a4080f1604040c007203034001d4003140ca8034101480d0510565 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 388319352 1250 388318102 388318111
    0xc02010e0d02060408070f05030408060618240f0a060206042a06050a02070f06020f0c03070614070204020c03031314060106050f160210020106030506010b040e010314030c0a0309030302060708 84
    0x69103c03070013003008210740354002c0c881e40b4414440c1540c541c00075902e01c0d095401c664011940b60f04510700b04113440c10160a1000500307200030440c03015181c01c1c071000f05881052a500307044000c2814807600b95032104964030451400c0280a1031003181d0b00c60000f503940d107003260101d80074400440c100d242c212a0407519401849054441c1324000d091540c101c1e4603402c034400f10030443c4182c4000050b02c1a070f9101c4480035082942c058144034240342c0100789040d461901d181c1c0264004d44040041d117500c0358060520034051029141d55642c1800000c2c00381c011600034201c607001c00002e1240c03100a43c80c0200c8100d205042400b1803403c09410191110001d01c0b07044085007040210005112286005120030040010010001c1c04036802040ca4220086180d10141c1c0d076840b400d00511104100241c0100708514001c4d28290400c80c0050141c4410311000f005600e207100c003039903034403c00d200b5a111015a00220b4050071124100108409214401640540140300104610070310030741085114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 388320602 1250 388319352 388319357
    0x1111c09021f0e040c080403020f06011419030c093602040506031c030f0b040e03070201030c09030b10030b130b060114070507180c0c0f060b011b060c02010e0d 70
    0x8507541c980b104491072042c203904100e19a18402c1059449100d03020b821980d0b99500c0210f45003d00d4041d14011184045113116130101d401003200d04c1c51090002070010040d01c954400b907a42100c2c012024070160070040c06424009408144086254802071403515054403d20008000b00301c040991400e14840d01c0031342002100c3c0a015003041c0e040507401c040058100d6411884541d42d03905e1503040140382200094030f0320707601040c0000c1806600085075007298200102c1003582c400030b60720310900d00000d040c12b4071075002c011b1550160b00103034002c0d40c200c84641050314142521450510090008a5103001c400001c9540c4d180e80c502c0916409a0141e0800c507a506c0e218011f50f28504a40400c81c03083c1030403c500000240140b05d224000c10001c0c0700780c07507403150b44411502034a4518441b0030030444040a110702140b0101200e844464100e140001c03103803038800040360240ba080e5040030841000d2041c2201b00f01443e1b01903200c8000e90740c020000101c042401a07128020301581000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 388321852 1250 388320602 388320619
    0x1225020a1106041203030c0809070e04060c0e0904050a0b010b12130204020f0c0601030c140a14150403080903120306030d212306012109020103090501111c0902 70
    0x581050040300090790010300c071904196a0320040220010105011400262510301c552542500010400d40011030707000501072076400d00d05001c1e41c42c04018001b400d2540c0742c15038207141c24010000300c0d84074030300601102114078080c103001d0303542d652180080b03c003d260302c000002c15a0030941a1404920990007000040c2c0394040c9003580000e403044140c1c2d101d542004403503d0a0100002040c0c08000000136110540c990b050006890103258402c1c2480f00310040d00d81a41d41e16881d1240c152500040011109204080480c0040c841d80402c1d40c20584005000300500052001810850100701c2c121071980c0d01d03000c441942400b0598010b50194091118070f8000313801003a00c030400c1040c04d0380354072111031206c1d000005d0302e005400058440007561802c900030851243e40552140080c01c1101d01c12025003074061803602d0400401c9079040d95154120308580c0300350060200250010020f100107401c048141115174407a40f1020714200d00ea429800040180307000e40040d10750010b100e0030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 388323102 1250 388321852 388321873
    0x130b010f05060d0c1101020a2001050c090d0302010b06040b0304050d020f03090409060915020a020f1516020a1a1f0e0402090414060c041409090705060c0a08122502 72
    0x640710350f01c0000240302550b000903001c0e4000f480074081c6500c23203540300c0440b20f4445860015111020407100d0950341881c00b0018545105c5007220b400103800d9502680e4240581001c07401001001c100540c403050014001850300c0d075a5001d11b0150740110165521450103800591341c4405070110010303981c005000e00300040ca043e074800b0007014004c10700401c054115507200159001040b05e0604519400300380307254066410070421260034842e10040c96000c0c0041c410f500c0c45000207101e0fa441001802801034924400d00c035101017150b00070044400c000160012004580c000c682c44040c51220703060f4015410003072040f000446644107464030311030b280d907000d119160200904c141c80c04041174510440c016010058680700c0c1c05c4210728103440c0c40c1080c42c60070f10041c500f5041c40c03141c2c850030305001d010b84c0c0110b036807421144112812076440d54882c65a5050101004010b0b111031000b052000c00824584c950a104884041c00402c036890340d2030b10000003221415082c001a800111481d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 388324352 1250 388323102 388323127
    0xc01090303120b0a23190509060103020f0d0507031803080406020f091302090f01033c020d1e090314031905011401172e0e130b010f0506 60
    0x2201c0b032061088002c9000784051002c101200c20607440030285042c15071031507446000740c1080341d10580d003c544100d1490f451000105048290340110ba10441101001c0b0700f02e603000380e040312414507060b406c06494501c0c124400c4014241100c10602281c205002e0404288058207421102c6605440e807281e281c4458885c04002d4100c0032416071800c02c07c006900c90760f6940c4030701803000c1814810143e80c8007040e2007808203c50041501d907040c1400d100d400c81e15030440904100901005190a900d4800c41542ca11300450f44007240310074151000038030b45040d01c50790b00602d40703406081d01855422400200003008980544034050000b4000808050b00d4a050000031504159200d012031490340045440404903402a840f901001980f0010718005507017101c0d00185a0750008058021403401003081004000e0300744500c01d042104502d54018200c03403002540c0600800d03e180500c62030255003002c04861449002c1d40c0c2030590200019001c114240c005040c0d0b200909110308281c01000305 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 388325602 1250 388324352 388324367
    0x2030c0d030b0a1e03050c0906010e010c11040f0b0108010b070c05190b040b0c011a0a06030c09030b0f041707051b01050c1c030b010206060a1202120f030a0807020c01090303 76
    0x25940f0064003500010700310a110001c07100c800109594985051462070540c0c58007018210341c0380200d0000041214680c2c2002600752000703001e0034866414851840d1002e1f03005011001380d580702d490b09078048031062040e800200701003400e8072045402d90302c1d044500d003e80100e401c010015000440c00707201c07500340240700994240501480e00e00051702e41207858260340241d00a0191014080341d00c80754014240110f4000c100c0004220589840203008150210500e000b1001855111061003440c80d03c83c440c070784001c40e0002500102c1d410b120307400740385c011001e442c1034500405c80c0020300302d0035426500301e0302030300d9200c401008000c1c0c04142e40128820600e14040c140b010601c03080c00c4041c0d06100402d00424443c0c0a03541043c4000c1c409411182c000c0f2400d41158000820480e0980340c2710211001c2c0c03000d82922144002c02480040c02200c0041c0250f46540102d006180c158940000601031600c030070740303603d4011769480c6400c0341c0c1c0d00404250315000801c00c40041000c24002c01d039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 388326852 1250 388325602 388325621
    0xa030908190b060f03070306020a08100b0717130b12010914010e01060807030906020d0b13020a080f04171201180905033411030f03040501080703020a020a0b0f1602030c0d03 76
    0x1030f5000706a031f036102e901c00ca030030071a401000700e0404004c1000c0301e078140c1001806003131245511810032010b80c49020408207200c003400c8484800080300c1c840104494030402c001e1454460003503403110a01c0c000400f4500a00c00c008420341028100040c100111101905984950062141c6680b03002e40445075a00301034116814141c0e100a0440403400d2030004040501d68000003165180d03000040c011021008181521040d2050280903032b0150701070040f0350880041e02c8081c40d41e8545080c0f00003c1c11022901d02c2d4111400a01c2080c0f400c070041c0c44504903860f5050490002c1701c46481d490540d01c4440b00108030381c01c10000001d030a181d1a0180d00c4140f042c1c5840740090004a24699a11048000c252000342c103c01404126107810001894074401c410061410107103000b001826003100500003c042c5600800c480ea61148204840017825070400c0310401d07103080c0411542d618000c02d8682c0942c800d502d06074504800d0000003100c03140c4039410002c000c112031410707044009005210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 388328102 1250 388326852 388326859
    0x60b18040f0501091d0d090611150117010509010b0619090803041d0901230408190905120d020d0c05070e01090b030601140d061d0a030908190b060f 65
    0x410031401d1405803041c0c030b0203080210000145100001804180340034540c1c2c0b0302c515944220b000d4100f80c2da0084010040313801d50300f09540f4090400000fa41441d80c01c01d0082ca441c155076000050040b04c00e2320300000031903070324003c00103911440704481c00d95400c181010b0b0480e10070000f00da69124026813202400e003181c034108078480e03100d40e80a8215489607100020000d8017a80b1044200c1c05610843c0d0011820002003000d1140188584000c8c403000f1014034180c0002d00c00502031107a880d0072241c52006041d64103400d40a90040580034103958016140a009600c07183c801c9402e00103003541c0f4406098000303010f4018610011182c00c0c2c0e80c0380e0119006d0090010009a140440341480e01a00340c000c000714810a80205051409805030321013104101140300b24045a110001c840d8982e0350440c2c07000c10410300072200c44030f450395103030078000032442203048050a00d42d01c80c04400c196065a81503031003406030202910501e01100314068902d42741000410304600d0021070900c1aa034015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 388329352 1250 388328102 388328111
    0x1090e060102031b0c0409080910080f06061c0f060f09020a20030c0604050615030a08030c0a0e0d1104050a0c05030a020c120d1b030908070b18070f0305060901060b1804 74
    0x80111b020b5484200302118402c6000c6107407031181c40c2100315810b001c6c0c2c0b00e10b070403c1c09241c0144800b80c0920081c21041c024040060615a04c40c0d031a40c010810341c151b03e106000c404200e15500e002000705216a8840900014010030013004c14000c1301d003181c11583d42c000f87c0e0311440846c1e51000d00c807941031218900c010800c01e14030a50920210b4840e0780180042c000318640041d240e41039030300b52a5020b2181d00f2101001001034201000d40e5001a03150407081d44860304160140c820080550840e41c0c0b2400641174901081050305170003e031501c00751070501c2207890340a2540b040d1028500303d40007150040c00010780c004941e901070040700800000310303200b0885080c0720181c0313540140c007407468940d00c5040e4125090740b1100281840307d19231401f04580f40054607502c289005000006242041400c013148c1520301c0ea0101900c80c032614410750b040c040d541d07050740b54040304910044a0a015580008101030010b206070030885034056466458480c102120b070824580c0021030f2036119070788 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 388330602 1250 388329352 388329373
    0x60515091011070915080d02060a0203040c0e0906040203100b0a060806180708070219030c0b04021203040b090316030506040f0309090f0915060b040b0705030c0a050a0201090e060102031b 82
    0x200050fa000b00101c990014030000104100d00984840d43c02001039544a170261409883c0e0010740c83da4000031802c40141c80751107030325041c3d81c41c040c00e900c4103401d44041c00901200000214149002c0c900c01c8084400010072624030405a07071048041c5a071100c044041040828040c050350303540614024107000142c01c01250783e00e0354990940301e03a00081d070114100543c0355010000c020700e007040705c0300d0303a99074949070b503401070035480b1090005000a1000340400c1c00c54494100b24802000410180d035280c61712102011500e4200307040c1c03a8032901c95084846160046d2110384030603030360480054103980da41d540301c001c94105514011800c0040368040019031030980d118400c2c404010324008030b83c8410034141801100400e2500612817454a00c0030801c10000c0360844040381c82c40c00c25291541c41d10b05225046014012485d022030050814980811038086541543e182c401d0300c90f04c00007a120b9040f1080d2040444009015904c1080030384001e00440081d210600d24139001c40c4c1c3c65054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 388331852 1250 388330602 388330637
    0xd06020c03040e06030d05041503020715050106050904060f0e0a0207020303070614191811010e0316090c0f05070308220605220503040306091a090d02010605150910 72
    0xb0b9444403a4890780310b400d1000c94034042c4150704134034111385000c0341802d003040b00e08042541c81082d50720625500248500c20011002054401d41c050403100708250369646001822130b07407201c08618821440d0440100d094400e04010030185c642e41040282d56603151541c4a00a51000800703a034140304c06d010260001c0c01c1409220030180135205120164108050302c000100141d078900e0102509055200c0c850741c12248020485a1704011140200075121005840040c0c0700d00e41c02d80c060080c0e198006005070140c0a8000300d801f406000c12218002d030100b160210740d5070340307031800145003000038001007032154040c1e503008407004c10070018000d200c00910501d28101c1004039559501c07071007000184155401600d100d5104a140880701e01c1c171990b03c0c6c80d00e91055010040015650703c102005020310900301c8007010809040030905403d04c0740322140d5618070000d01c100150300b02034000c14079040004605517400d400b41c1d4614140050b40f010080c800f20503407c0c10f002c016102141900c1a079 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 388333102 1250 388331852 388331857
    0x4051c050706050403210206070f14180a0b0405100509030c040c0804060c030c090302130e0a051b0109051c050c090a0204030309050306070c031209050a0309181a0d06020c03 76
    0x16503c0d0355540e0340c0703035203000e01132500049103010300d8441a01c03180c0c0c10340742c000c81c11a60001c00380c54446c09c00000100c00303880007030000004911303240000c50409502d1807007410070044028212200900d041d83e5261025030b0b4881c0703004282c0c004d03031a000c01c8201940a880030b4007441c4402002c2c0d451030015000450212026086503c00040d00c55051005205051003000414480b0389070501c48034102c240090102c400703071320009001c0c2203500c0c1c1002d400d1484d03a0000c40074110381001d07a1043c0b0003908000303584020030468500b0703800b5101203086040d800749100b0340031030b00060705a14102110300108601c4004401c4152100c1c001e05880d91941d036644180944541c001e807100503216802c50400420010040d0451401380d030260040c8466280c000d11010031682c0c1c1342c44d26030302d000c1141a280c40600300144005020b4840c0a5225041581145441c010348100500041031580350466600c00c0d94001c1c440c10321120a004801041810302403040300405015070b00140c9048100c100451456 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 388334352 1250 388333102 388333109
    0xe030f0309221b1805010f120207061a090f090723031510120b041b0e01030803072d0e030a0c1d01081204051908010509061602030f04051c0507 63
    0x250035450f5504145801c20004900708003000c0c0781034440e60411001034600300c81d080300074007030101c0c203e9003084000d03e6404481200c0c0c0d2241e018403c0e10100c840300c3c800892050043c5105888d50000241010501c28510748201c0b40c1c10010318605185c800500d0000d070014001000c0c203c0200000400e5450410001003828400881d0914a241c003000f5510602c500e600120801c1c00100205c00204074070b05030141d080b540240c3c295586007420840d1501c0d011103640112403c0c0740110000043c0310303240010314800c483e03945444a0030801a000548940c8212201c580f18052080d2031200c2d031841964140c0758035030301400b1540b003000306450390798003030240d039100e80800740d40e90283c3e0303040000c4200b446004001c894000d20600184064001e01405030380101801000303a20a1014503002c0340250100800f0324500030031980c10300e50302ea5600c0741c804441c0e8078810800d403044400703464400411114081d0905000c181031504007010055040c9011700580003082114401e40c020403400d11012005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 388335602 1250 388334352 388334381
    0x180115031d070302010f020a0201080c0906090d030309020306072a08091905030d09031505060d1406041106091012090501020a050301030b01050108040b0402091f0609060e030f030922 80
    0x42c0740c510b20004004e07510040b908002c54020890090040c0d810010f0140c02114200c1040e4849085c180810002e0041d001d0311648401d2100b00903040c107425511030740d00a0b0080d03040e56525a03805d1819100c1514060803861200116100d01202a0138101c20080703240c81442d01d1482c15410900164005a0705400c2040c1c00e00d100108022910302004841c030507154a04256100c146161031361489907400311271801001d5101d000084075540da02080200740e0754055100c54410403202942079407900201c5086454003400c032103ca0040c90000141da640200c000d000c0d82c0c181841400468000b9885542000c0d0a5190f1a068000400c280082c118a8041c1c1d902c0f0b6440758514204010302400c1a0f10407030501c45a40705001c00301d0018034010740d206030155490152501c602c2480043e0244070303144c4000c802c001c0c0002061b0703d5404a42d9038200c504554800103105035201c1056103c0b102c0042800300d0b035004020681503414044c0c4640d20300a164800c002c080c15442003940255110030a03040c02c07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 388336852 1250 388335602 388335613
    0x1f0e040803010e0402212506080c0a050c01061404050a1407050d150306230601050d091b080313081f050712020a030203100918260711030c180115031d 66
    0x500000c0350038070850030390300c100c0312150048c42c0520150000030041c1c0220f49000c1700049150240340280b04540b007064401008214066490583c0b42943d0241003140c0d11880c14036002c140424124001e002d079031030611003648580c1d00c50520030340d6182c1c0240a0b54103407079166000d00402e07094111080e170007103000c0c1c1c20214040398500700c0300e92025850301d07144802e510800c06100041e68000b042d900c0300c501c4090001410f13060350130f041029801c096285405600050170100302d600d40440640200d10401c0c1e07040031050f4540cae81030f684a080b4559012618140d03200703446801242a00030719040b0040741407980c105c0c18480e00e21426a400785039080b0200e90000248403959910401c900005c10411004100c1e40f003080c82201680c00030b070140a88612a41460015480f55a02c206c281c00d13030206003255a00c126610f0641010000f91111a01c60700441414402e64142041c541e52b004c1c0d10139480c04001c0e0301700805207034000c40044040040560740c007081d0041501c104651014800076500401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 388338102 1250 388336852 388336873
    0x103080702100f0504090f0f1508010609140406051008030a08090705270907090e0a060f0506090a1e1d0616020c0f1201051f0e040803010e040221 64
    0x400b501c00c41c0b0758010401c20204000400d540101560250b80b0544030101ea0980440744080180014103020070a49141c100001e201300070b0306014030120398210009110441d41c4641110031900400c2050318409540350029001070b10b658407143d8400c0c070298400000355101c001d49031944e00f040c103900c00070419250030303c403980000708000340082030304407101c92850640684070310700390891b10002e00c0400804404034017100f1040c445c0740081c2813003a2081041c83c260341c0c00e4540d103034601d4406484151503d540d0381c101c0c03281801001d00c01c04000d00b200c0b80e65290380354643e0090022038400310003850054400001407016004004d0b00860404000d003910103210103a90400ba0042d110126102c505100410515001f2038100d0100b0401c0fa0304800c80404107000c6070104080070150301c025440d050820280044010300c0c41d0089051002d2080c055031030b070b55200d00118098a002d031020038248010414400410841c030303030040c8060882490f1032220b040101c17144d058900c00c2c2c0c1d410741000c944a03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 388339352 1250 388338102 388338109
    0x70903050601210305070f021c140604050d050a05090d15240501140c07090e0d0507030c110f03060906010501260601050a091701020403030f030c080711070e0103080702 74
    0x50150424948080c4443c1c079401800d941061551802018024086032440034005072640781d0601c190003070303d0550f030300380d02e02c0104e0148510a0012201e851100c2840c0c030852070002480340c4103540c8000100504a41110155596000951034104024040001c0110398880b4408400c643d4030840c02104440140070504041d01c9d1203100c4044580603044e040c1d1ba080740c0e92501e103000c9841c2030030151005509003061508500c034403c4182494416050000303050311007030344040c058903020800e40b985200307440740440d2648203c08c03002e030000d0900ea4644000c41d202504500300848003c0441011072401e0002c01d080260407210300100350010340040056581203d003102809410703a000c001c0004403074040a40c00c2c040030301024104000440e01d051160701914900015104181c588441929084407544c042d41c050b0008030009205440d0006180340240180500d030740940d11943d1159403100300c201c540d01d860407003070056803080140010b0b1100d5000b860b44c0c0614040c0500c949d40f003820f401803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 388340602 1250 388339352 388339363
    0x60203091b0a1716030609120c020d080d06090e1e03040b22150e040507050f0d05040201111005040201090e090c01121b030f05011a071e0618120e061615020307090305 73
    0x1036027849030f0603015000513510308800010150f8415141074440681d11410001000903030000c1051030310b00b080c41c0c41869000a50500900e0300e41d1000324005404803c8661240640e12450317481e407406000b1080102c0000460b000b10440105040701503a5980c40d104d84111006d101c2e820208210351100240c0381031038054554040141d041c541c0c90051746282a04040c40360040050f40c0c160744401003002c42e80b00b049040d0b042140e01044415001e14140768400424055600b03d021501d00301c40041c031148808221440b413419030001d010900c0c850750040d5410812401810202c50342c80110840c1c8901d400710909180180f0b50300000e092151200744c00488034182c00407a60018847c0780080d826201d502210246a0703c00c10203070610410b01010800281074001c01005030782000d180f144180d008100aa5080d40107445590404241d514140e0303070b040e140110a50890b9080120f800c944818000c1c041c106449007104000b0041c03d00c442c207040380c2050312004009107201c0310800600a00300f00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 388341852 1250 388340602 388340633
    0x3150411150d1a0303130b0903071e15030c05070b090709050702031c060503120d18080a080a05040506150d12032009030c040509010207020904060203091b0a1716030609 74
    0x1941b81c07015902d0b071260906c0b50ba21510039000c50001d8940e4444d01e0034040e11004100362a0b40c4401490403030700050703401805000344240210794039041612144680104860b8082503202c06240c540345850700001c0d00d4004040484504c82c0d110006119101445410311401c01a80a551900c02c404400c0520404022900c080c150030b0001c28409541d012aa0008000402c8081940e908100c445200034060300c2188806103042540d4000c01e100d22003004000000a654070580d86580f0200c1c0b00044031000d540c042c2c50b0b68400d0001800444064a241040000007401c01c4020001c55442c46110515041c40c14002922401055041981e1036450b01e05a010815554101410000442d5541040c034691078803654598000c03400c0018207504407503032980c0160044105140909110010707500c252090300d014802c401800c07002c184c2e5000441140c120042c40340c4586031a006102c1001c42c0d1203020003096004860210300d1200c900c0c851507000b14417401c0c000c40c000140c1e04121152400b80003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 388343102 1250 388341852 388341859
    0x50f1e160602031e160e0d05190317090a06020307020a0807050706090b0c190f0209071805060a02070509060103060e071106151c3e03150411150d1a 65
    0x50500c843c501174224115071400a5180200b080d0280100007590360441007000f40071400b0f095108008101601c0c00030440074000d071200ca4001e05c03042c0001d4441c1c81d04171100c4555402c5134041000040990300190342103070b0306104461046401d0b44882c0b030704d544414030441d0326074854802001841e420852440091400d15012801d01400c0740e0040d86030b81c018100004400d1080d0690003c21a4042c08840ac0c5070f000b070241912031814101c003a0031020b2090030030800d115500c4c0f0000d810b113090301c2169140c06481d0b02a05000386003805000d480b003030280c60981495241c00d404150b40300000c03080c074851040b80d507030740a080c510030080f541016805014018001400194041c0d035880c0c4909240f0034132340a0390102c1c60207010342000740d14102d103c9000c00c100c002d0820361080020641c804412860480ba4200039030303816003c02c2550b02c001c03e491101545810800007400300d60071441003a0000c3d00034040c0380009a90400200082c0d1044240d00c101580e24094500081c0c0e00d409003600342c18069 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 388344352 1250 388343102 388343161
    0x120b0a1a13080f06150a0e04110a0b091c14010516110d08010e09010e07060f1103040e04021c170a0f0201110316031104080d020607050f1e16060203 65
    0x4400340341c444000404185c2003420614042d032080d1a030824000080a0100c064941818646499110441041d4001e0700c80c0c0854000400c40d2004c01c01140d1681400400c005649900d818900f5540c00d000700303040e120303010042001c5211460a000d0300d8401c15998020003100f40c40140b000c3e091000d10f91910047d070780a80205264141c0000042c1d0544a00380480030b41e84c4d441c00c2d9014054854210141018007520000045094103c817003200021002e0721519008040705180b00d690b40110302c07481100b504031030041800350804074801c0304904900b8103540178014a5403941c404e10280343e80c51140f010000540d04950b00c0d445000601d400d0302c0e901c002c1c4403240b000e0390407108500020b05804103e025540072801d40038004d9208241244860502949035942e4070381c815124440700800c00c000d4003d0000003580c45114070103e6444854650f030070b504102c1000d110101007011507065003003409003005a0510340000f0b64114041d14440c44025035030b480c00c440140c10f050004000d107000382d03041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 388345602 1250 388344352 388344373
    0xc03040206030a0b0d02100f0e0409050304061809050c03150f030c061303020d08070624060e0d080304061d070e150103091406090111030601120b0a1a1308 68
    0x80790704498000c2c4007802c0105030100e250740020418036404000a600c103030710381d60165000f40c0103110907031180344a4a403481c00150503400d110549207903174001449170301701b00018800a07003d540701084204c40d40c404280303000e45820009003110380070340e540b8091290200030040f5490095001d159104030545110083c1903042d00070960300ca08288004c0d10640c0b022910f0007846025142460003150007c00c4140052203d047c52a855407040381e00340c65980c10070803e8820301c50013074445a019000411511220b030302e050801c60f5105554807102e64030020a00000d40803a01402c0070714019406400d00003a1652082e03c400d0140d50307990b0b02d0705040e422080c4204081150300c800954821750703601d10b00c032a201a03c2e004800901c0c2c040360043c98441c50b034040c1c00000900160851145d80100020041f440c0118804c11450004450041c0003c090000010341c0480740c0e00905402840945082d040680362210050b454481010100c00c810020448012000380150800e0003014280c000d0909080c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 388346852 1250 388345602 388345609
    0x9050a0216020904020f030d0503010806060a03051504020315090d020106080105060a06030b04060e07020a2607080a02010f060b09010e10051e04081614030708060a0b0d06020a11060c030402 83
    0x248501c040d200e0340c0314000240540d1662103440c0403400b0f008003a41d4840b21034100c041c0054000703006520b118030500c2c00042060401100c01001c0e6078000000305909030852150154820008004a030980986012902c0351403000d1703c505e01406043d005001e030801c0b0110020b007129216840764035542c2c1003105100d05510b8002e100c00030394402e4500442d11940d480c0204018202641c0040e030180e0502042000c881e50204519407414421086038008000386541000701d0501d0012511020b14100700040c0000e2054009145410503400003007008925010106c04a49903503000040b1030400241502c0c01d50713440000258403082c11140e000c002205060010614082c2c080490000055046a039005400e0a0280ea0041503444222410486616100030100d40340e8400d6070511207103813103400000e10303003c241d0400307895801c2d00400c41d5958004110020704940d80616404c80c003034a94080100d1001d0001b0030b140303840381e00d40d070701004103c1303030114070b0150001c00c2c44482c038506000b4400140c2d07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 388348102 1250 388346852 388346887
    0x10906090909170c030a2015041a040b0603010c09080307170715150501032d0603020612010609080a050c01121e05150301022d070203061009050a02 65
    0x52401d440002d14440603d401000c00b4858180042038a40103d941000044000001c244808566403456050741040d000d040080160091a6142e03030003040926008003407045540c3d900c580030304400f43c000308010070030a001d008252402e480080b2004204a0f0504003401500b520000900e40240102c0c60018460340700d018941004049050108042090348011000e550280c0c4e08448602d40d806509580c09008094880c0c500c600d492601100065560003803241e86070554010f02c1202801e00b0609e00340120024034a08010a1a5140000b00260304c9010182c094410910301c986015410008064060790140d0300620917a440402c2440004001049843e240312083c00c0c98440400400311003005841010000005a5031032660460001d02507003000d400b0ba80001c1000e00e06c402ea5401741070030b0b4030807058200900542d818031041540c1141c817220301e40801013554113080c280710b0f600085c1001c0042d0307400c16001c0001c4500703125000051003000e4000140f044c0442c60000b210883c49400c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 388349352 1250 388348102 388348109
    0x60403170702150a0203030105180f0601080a0608010c110f011b1d04090807020907140f210403050705070b0a09060e0a0b13030c0f05151806040303170601090609 71
    0x240001c980e100031511032508440104801c00441600c64401040c020750340d410900c9141c1c4110a1900000300050880622a0045804114500c025a038250054400c064090301c0c0203040f80e42c1d81c2000403100c82c00e01c241d000c1000250345480086c0d203685082c529000f080519100075900d00304d0060f1101c00c0820b0f401d83c00550504140322142c1410b00b0701140d019070f061600c0c1c1c11504080c03c040400001400808070b061080b111f0000395142c40e4022a0031990041c014017000d48104541100c00c1100c0000d0151031206400001c84090000100560b09509403022804228042006010851b00f44552005090549020fa052070204040104038540350b20840c405c1c0444000303041010f8039075801c610090301c0b0740c3e04841c0d40d804024091000ea09150310041c3d0301c1c8224490040b4605000000090444d18002c1c600c1c54801d84c0b240ba44403040d4407502e04040c1123800e2811411250300d450010f0b2008600070b0300c6107410303400c00b4085c002007510010041070401c010040b0910000c0e070011040800d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 388350602 1250 388349352 388349393
    0xd0e0a060f0f20090d06020c0706110d112a13020c1b09060906010215010b041802030c1e1612260a0b0d021302090109170a120912060e010b060403 64
    0x115141402c0c0300d0000d104000b980034690052403401700300f140c0c00c903050071200f0bd1082d044608180007080115900e10185050304a40d40100c0c5508105a81c28042103a1049914111035408006840000e4244501d088a0b0a6868012814082c1c1800c00e005030107280154107060014905101e0020f0b04c400c400404452085000b02c0c003003003c0742d00c00c1000708102a5411300c2541c440d61255800c11a5400911036081418420012003140d4031140c000d49000340c1040c0649410008014240c010154031b0382000445c01000b4404188994506038501c0e25480c0a80d000400d083ea00c19070003010301c0140146072401c2c0a1180720800e41c0160421416407055402c100042d031120b002c8001008400c0f40703903001e0b41c0314004078010113186242d0740c01020307840401d0f00c584401c40d0303680d003034405034204280110348250060301c01503001c5a4600c510701ca900352640fa001d580540c032030542c40e213040c2c5150415203e83c1e80d1800c0c25940003600344195850000c044903103a0401c0e1850741d80c41801180c00300c06045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 388351852 1250 388350602 388350619
    0x60e0904061107050c0a05040603020a05040c0203120c0a0801060f1e02010b061b061617060a09060b07060605040605030d03020c030d0c020d1205010b0d0e0a060f0f2009 74
    0x1404600d602a4491010441202c2d54030708603030400b1030752044000c828502c5555185400036080c640b0b4816001202d50182c811440070b40b4001c100002402402003030800c1d40002c004404c102a0140902d91241d41417003d0161201c4003030a0007851444143c12480074820031842c03840200b41c10400041060b05c01d00000c030300e0411002c00c12405411a40ca6942d003080022600780d01c02e02c0e0300c0d820582c00102d10007c8072032550b601030704075210741e9856550790049003611209000c03405040c045258050009080c0c0d0f4805a80c8030b0480b011500c9540c010310554102084180422001d401284d00601e811035052150f107040c20002511000e9010004050641c0003031a140410018002c0e00d031101c2000004000c1c440c4441c201940314020220403400003282503000740c01810030713807050505803468041c10609040459440c0c0006003416465001170344070716000d00380044d1580c007904400142c0c80801048074855503c0c000c003a586400d01141c0c00c106822030b52845c1b40705110580d90080e80072200e010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 388353102 1250 388351852 388351861
    0x2040b0f09010609440a08070b0a380d0c03080909070201050c090d05150103140d030614010c081b030703111617120301080d18060e09 59
    0x180803820550103103822201d02000050000c1e00f1401100c2120030080080c0041c04002250310302460050101d080c0012990038a01019161245400a600c16210850351040380a444010391600f00c1042202e14000120400c4803500c2c03940030340b401841600c1c034868242181050780c80300300b4400c0d1068070302600c125044440240d0320300001012035604080516502038a0307042c150500d50000c0740141c003c0c520305001c40d90f481d1052148500c5040001c100600b000300c2481004031400420300155094402c000301c07aa5001150b4200c0303402540703d52500d11f064014540d540d800c1c244242d0011050500d40242042120201c0d820790951040034a800e140100380c618200815005003000d07510302e003000c2e956400c01007000000900e85507002c0d4451019410301010380c0c0d50354a80c1d4014900c4aa103032110100700000d40720007486030111445007a28100840d00300c000c502c0741c100360301c8400d450784840419100c003a0002000c0c04a12494221481042d00707010020f08044202c00646005622060014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 388354352 1250 388353102 388353109
    0x90412090b03040606140901030f0f030c05190302011803020a060c020307050a060b03010b040e0a0f0501020d020a0c1202030309190c05060c150603010506010f0e0f030a080307020d0203130302040b 86
    0x40040d20708041d00d5601ca04090400740c00034916800340e004031298801c1d42181c2c91a2866841e8126130b80403036510b1011001d40d0b10348070908520b01c811010321021908450004e0340910031034410003035000402d500c0074540d084c0242510100d20541405c1080c0c00708002c00709a001c01c583d403191b07400803404241120703400012407640c480d1a0001d8128029481d9113410807a45800c40d02004004400038071420f100d00c1c0400046401064020742c055000070385a400190403058500d00c141d018200050900844c4070361401a40e00290300c1900160702958188100550001e000e1709240d9144020340c10761420704c0101d90359113540c2035100102001c42c200e0108003d540540400030f8400a090309880712414010181d49810310a50b1900074180000024098101485030070320440e4160354112100c00c0921003980c0c02c6841018481c0c1180b2038900541340c640b002c00403280058464048030396a4941084006d0503d00c20703622050464200b00088151003e2885101054940440e0000380e10241c18000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 388355602 1250 388354352 388354367
    0x2d011d060c070e0c070506010509060d02090603070b03010906030c0e040b071b050d170702010c0207060518361b0f0d0c0305010f0b130603020f040902040305031314090412 75
    0x6800002a000b04002014040040e002aa06c120700b200d9169880d101001500502203d0041d0400b040030701040c0076150041e404d64100e100a4280e800d0140c8072601d00400d5803090b044090300c29110b480030401c00c06100c0d1240018030060340c04401c1401d15a94030321558402410b441c0400c0910a0171981e07451035404102c05841c3d0040887d0317101680400e018200d02c0d440741400319003440d0f4100040100b401801000d90b142910b50140084506041c420b8406412141e4454079030702201002c40e5440d107805090340c015514000e46e03041110040b41d03d42030104050b004404480c8888410701ca110044010500d050036041910240c40c0c202e15181c440d603a00a256250007150704184a905404d07806500441c141d8500b0b503040c4024544491510740144200361040d00008802c00303003081030f507220b9406840c4202c103c00103507180c42d589014007820398000d41c00950b40e135000002d13496100a44000103000500340c1c0e812421900c00140000b852480004002034820320b01c1d94a18100588181403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 388356852 1250 388355602 388355609
    0x10b060f0c07080118120509010f0302032805040b0606070c0909061407080609010801090b22140c0108010e15120c0a032603010b0a120b2d011d060c07 66
    0x17040020380780440b08071546100107050303406440c16900d01921501c150f0031101001010f845103003a142c1403040c118025400142141720718158003c20038034070060401143c1c1d80c01c00c403800214a5003042d051a48900b08050411071203024200450000110145d007500115030740200c00068088040c05d04101400035050314008501c20780081042d5a030304001e5290040d507043e5a610b40e641c2e02c5450a5003211552040030780520306403000200c460001284400300d070358001c014900e800034107995511040c200b139490b1040300d4001030700100032540d1042c8014014202741a84029030700700012030807940c03600021000c0c000c3c00d01c206401b000e448108040411407038040c0290403016030b282018000e1100e4440c004205e0041e108164080c40703110804d40b41a10301c0c00d074003141340c100360401c10b40d04401d5002843c90f01d42c1e1950120301540c0e988900901c04206104070311032710020300681850400d060540e140c6c0c1070025a842080b4040c10080414100b940c050314107903035031034040c40a140742405690 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 388358102 1250 388356852 388356869
    0x6050d02150f130312080a0515090603071d0a05130b0a090309031704090e030903190c09050f07031503122105040f0203060106170a09061e1d010b060f0c07 68
    0xc000004015444045c2c0042954a9443e002507031074900c0240c1c144c9505841100e00c900446d90700071040d240c040101c6401420040444241641e209a04809801c0404920070303440d160348200540e6904600400380d100d24140c50100c0b44510780e5403400c043c1c0c00044e01c1e100380aa42c50710740404043c0902c4160000d15008010030400050782c0741c900505500500500c124075003004040c1c101d01d41c000007540c034801d4004025020b410300c000718000300200d60741402d0310601d040c420300042e44811845203a0041c00400c00d114031900e0000c10140c1034901d00c44a85012500100d0100302260040030520a119100c0c42d0940652070140001245001d500f40d0507000a0301d00400d2008105e8040c05006559100f076050714001e0303076500c10564409140d1401c4500d0f800303016000464003417169220100c22841450700050fa8200c0e2072600d18080c501161020b48130390f40748075148004120401c40000c41d010f11000340440b0a0a80200390140030709080328400c450b01103490504c040c030501650340506400e0f0f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 388359352 1250 388358102 388358137
    0x2180f0a180609060f0f0e03040308091305091c08040c06050c0f03030114090c03090604020d02010507060c080a15050105190c08030f06040b04050705070f0c0503030c070906050d02150f 81
    0x4d0a10400822008408400491508946001e5802d40b0301410740c6440404018605052541d203441080b94402c1c030103a40c0c021014080c80c010840c1d6803040034000c0c3c95041c0108401c400c610700f8030032028000b06409042c030910104101c001b03240d00c420340055603100c1c0b4045858900d001251442d020500c1510082030002100104d10485150070210800c1030440d040b5260703494460003484a03200548015050b40c200e540010054101002c1c4241d9444c41803401914200c02600c0303000c11100c4a0744288001800135081c00340c1d041e998012502240c2e07030b0018480b241d40c03034013002a100703114803140100c812220b00a403003015409602c1020903941c12800003903581c5400e00020150110464000c0d12807854030401d01c4003030400b841514850038103511401d04d000015100c0b4050080a510b00722810090384001042648050002c2c0c084001c00200500c400c605101228007618126080207000720807014080f00981d0700c1c4512401400d218904455480201c0c0c3c18068440c481c040e060403030903095 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 388360602 1250 388359352 388359371
    0xd0c0902040801051e1519180501090b010504030b040305070206042706060207050d020a081615020312150f1e09010e13020108070201200a080a09230a05060703050402180f0a1806 78
    0x14003a011408e401b0300401000740381e88606d40002140c01c0c0401071400140184018000601e80c079000981082c080c0c244181425050b40c0040c5c840e500c20341140701c0700d003100d91280340b68000c00c16400c1c4038444000c10501005e070070080c0081d50381d0b02e00c0c4541841509180007080030b54071814001409030580d88280d420300d411450b1030300c44130380f214800c00704008141031000284038408070560f10301c440940072049260b04d401c11400c0c11000c405000b9a070028480407212455912440c945400e100451032601c043d0707031103200b00b041c12103050b0301030041d50700c1074070070001c05ca601e2140120003a039090030f01c19007607200d00c1c0c4202e00424451030082e000f10f030641c5480e404034005a01404108040da52403901661340c0c1d0781c1c104161100c1c100c1c001e05401c6822003440b1482d001c508254104400041219640781c41502d41e1440d001c400d98120002c6076940083c0815410600d13004048a91902e9403240c0f20300b07010008a442c0c05001381130007500c0383d480702c0b50040c420401e008008c0d46a001074013400008030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 388361852 1250 388360602 388360619
    0x1107050106170a0b2d011503060803090d0f0c030b0c0301240c060c020111041e05010203160201030f0e06072a0503090f0d0c0902040801051e1519 64
    0x80c02e0081000910a907100c594190742c1c001598240309a01030410019500d5408504244800414054000f1100411000500d2105a13811402440204a00c804141031003a0150898009402010094004200044150302c40035181440141d0203105403c02c06064142014014503d4000174250b400300b80074002c0507a41030340a14141e500030600303100f10303030a13801034841540301802c20700020070040000d450200381640c3c01910806d4142c00041607920038104810f51503072003030300030b0110554000105a41d28280c1a07100b00540003e00040d880d10502181c0c1e1949002182c2e4024101503c900340c2d000d1380a00d40e001008044a45001c0b59500e00700340300083e0180b114060f000c2c0300005560203610380700043d580301800c883d400c8005185000300180c10b105008040702001d58200c109001c14800141c44440484000c0c05c0c1d0103c016152401e001e074407425640d000d08024291542c1b4404642d10301c0c050440c142d08401e140d002806a801d052000ca50292030781013140408007542c2400094101c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 388363102 1250 388361852 388361861
    0x3022d0d0915090302011d130606030e102c0a0c0605031501020d05070212190c14040515040c020c040f0e070e0c19140a0509010201050a2d11070501 65
    0x1c0b1400ca030072001944038a401c036999140342c48042e00248071420020000c8001100e80038071140d000d040d4100040303180c52050156180f5502c105c9c002030340d5100e41110480b09010480700841c80800074402d180800c0d82c4001c1c1ca20031038808000d41c0000420f8100300107420020000010341c086d0000300d05c00d40c0c2d1134010385650030480c1c11400600140403800d05661010881c0030181c2001e0329000d0405040c2d8003403013454807045881480d40d20500c41d080301d09400c0c1a11310903c40344039808801642d8148a000c80700170442d05950760103141040d040c4030041e401c0b50001c1d0031010043c1c8000403408a0140201e10b4540203800a40e007252500400302680c4505401c0319203254412011264496691003c0f4800d016040b108106443c0c000d000441004020180c1010041c01c3c82c13420341c82a42000c14100000d0344030300c40500c040f400c00200014a0750f0280901640080c001004101c0b0304d103441540715181082d40b1190f001c03058402910b90150000e980070105071071698488944034105442d0250003030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 388364352 1250 388363102 388363109
    0x1305090a0f090f020111120f090a0509040f0309080d0206011205010b0d2001083c01060504060e011815030f060803030103020405010e2e24140703022d0d09 68
    0x29285071000d00300c100000800c0d84803040ca511f0b92510340040c40c8545041c035000606d90661000042c03070700213800c0d6035019201c0e010b18010140c02a0240c601c0c50003804120480d4000741c060340000c40c1c0500c0d080c0e008a00f40c1d04440302400d20140f0782c0c00a00d0703d02d00420503140360f6a4030000505862040c0003421b014140030255110300030181c0c0100c7c0d40191401f050464818446ca1b00307103244400c2e01e05009031000c8146191006c800e007560214078401aa01c007098000000147d400300c0d040011541c03044c800160b1980c05e0901c5001d4012032242c191268030390380920b202101c800c0c1300c400046882139100c407a5100240108018094654001c251664001e06c0146d1043d0700344000440c1d02d0444a1401c0d0150303c85c0d8601d0786900d80a050f2100034407850300d1b40d005614201c0d0200050700b01050f201410001c40f005040c100c117100200003d0b10790f2407400d442003100310081c40f08400198000428030440c01c6420020310107000d02900400349424020a00c1d08a4000c180b104003046070440018000e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 388365602 1250 388364352 388364357
    0x3030f0412050f040311060c0a03080a20031618030312050906070c0f0f1712010b131806030c0f0305010c050f09010c0515070c020310021305090a0f090f0201 69
    0x4050744003200315860f000c0c0c2111007805100c20031040001510300104510031501c041c12403410215020881400c2c00c6080c101070300450b4240042000c80c000f42e00c500c48003c030319242d0400d240c00700140041c1c2540001880f103541804204441041c2c0da0041181580a02c4a5140302c0d025903242e01d002071190700611014041079080102080a0880101d14180f04503c2540c5210707031000d40d610b031813582c245602c4c42501d01400c1c01d0382034008500c05880c11344d00c10311001c00e2580c1c3c0305a11020f01451401c140e002100d4180180414412030140c0b003156421100f0b0040c102184030116100d00c002000c1c1ea80c00103244c8101c034075002a01e1051101c44130101c07401203000b00b100c1d620418054581e4419403c0c80c4e244400200300d28083c542c0a107a07414180d41c011801c81e403a0810031401d442403c078003966204040346a0348407800c110f1400700401a5203d5a030b02c004c1d801c003401800481503000e5280543c6200700003031000034483c0142030344a80c9044101c10401d018480440c1401844a007000340260300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 388366852 1250 388365602 388365623
    0x91a0103050a09020a083a1808010906060e1021021f0206010810060b0d0c02190507050a050d0206120615031005090a0b0306010b180d06020a02190b0412090803030f04 73
    0x1f003402016032a1900b103c0004414025040440e008039200d05814140022030384003c10f0100d030030102407190761201e070310900b4001400c9013031401100d07902400502208010303442413800e00c40c8481c00700ca10402c5a59101145080b2803440c40060041070040c6c03d242d5070009040d250070310f86540015960b04846800040e9441502100d041000742e42440c01203031a000d500300410260b052240d841488400300ca4419180803944004000044c40c9038080306946560090b14280101c0c504014401c000f001b00311132006070100a58046603450040d0700c5c017416207040c074100140785a111580c0712031081d03000030400e60b03803860040b00c11009042c0c00d0050303501840004c0001418004a03100305211050b00900404039a071038032096145075800243c0c420340070340e41d6005507207042e15070220314007107940305031000340e114040c0341c100915003550780ba0400740480c1c145450501040810800c80d07002038101c2d607550402d048140065804000e40c2d40000420304c4000100040003013400c0f001d034040c2e0301c2180c401c076 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 388368102 1250 388366852 388366903
    0x1804060b010e010801080712080f07060b1216030602030a0e06130c0509090312060307050301022808010312080702011103130c0501050a140304050a0602070318091a0103050a09020a08 80
    0x10384c1d01c5000d0040720001d500c0700e02e0501000c3c10b00c00e00c072041c451041815070b2030040450614100382c0c00c844030031a051500d41090089070300e01003a01e10b21011a050007031108818100350140e0620152001825255001002c1602e41d802a000135281120100484500781400c4500800c1c1496601040e610b2220300f6801203101c0c035002c040c02e401040d40c1c0d0002c40c1000280c881c69510000050007903a4148075500c07000407140c07001c0c000361a002c3c2281c409884103494540d56059201c49d8040751000304492040144005100c00c039010700c1c1d012041c541312400d03a40c0e80c10280c0c0149002c000708010b04501108204c0f0b00d014600f9504049403050505804156451005403890f004400a407001310b07608240f07a80e41002902d0140d5030180c041c108031012905140c540804a0b40960750a8001602a1901045c0c541303072402c00c00020800c0f0001040a440d14081408801c003580020504040d150400300700d40092a170031000a807500245454a8141d40b00035030743d030342e510750b40c403103040e14111042d401d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 388369352 1250 388368102 388368107
    0x3020a0f08211b1501060f03050105030604050307080d06030f14010f0e030d1e05010308030106020601060509010806041109040e010c0e041a011103040b0c0d11010504030207030308061804060b010e01 87
    0x111004401e4961040c01d14015450f100b402e10702c5031072244024407400c198550305201c0340ca095070080401d03440b001440e8290600050607200143c00c00c5009070b100a0034040080c6e40042211241500030001c40e80b50890006a14050500da901c041c01c08840400700e94140000d410a51503410a07501c003c10490300000045400d80d844c000210b19aa0814883c0f038064603004d0b088025031080098101000101c900c20101c2207a00a0b041603604400100050102680401015015150508000b401c01403088002040020002c04950103980c90b81d6007490f1040c24803081e600c00f2440200300703000c1e1b29080c0711094002d01281080d000042c030450822207890800e0300c1040c1405d0300f42c00104c0c89103100c10b07005640e008100300e146402403000304400500003007050041c0015107a44409825001c2c4444e100825184130b03040d200c0c0c903d03403400d02440b000980025002044a0785414040d0003550b658002a2040d1a81801c6841046200341044200121548000d1220030240ca8003c00d4984d043e004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 388370602 1250 388369352 388369393
    0x518030a021305090a060f02213310080403031d070308030603031303030f0f030c0203091003020f07081b0a0b010b0c0c15071203051006030b060403020a0f08 69
    0x1e0340060400301c4035904218280c2090768071550003000c807054920556154000c451003078400340c0da041d40c0400d4003c09004a151701844950341106d010016080000e03108007100d19464042d0001030702c0c640c05100c030149107000040c4440c0000d04803001000c171a01c010f450300004440803400a883c200d402c100045100c010541c40d03500762002003414600355030b03600c201580083c00740b03941881b082c4240040202aa2003c1e0003a5102e951112055403004d503000d0320300301859011105144c244400884e0b083d5002042d030314900000c0b00d107100880b5441600750001c6c800c03100c0400700800001003000c280161000104210002c0c8001e603449480c0603043c00d611003030740100003010000316000400201160101516010419400362601d00318100c00040741144071545040120b98003140c044c0c140106040070060056060405018610b4050078021038481140504030525a6a00c203041d41c0d6101d9a00383ca000d954058440440d094880d81f280d030000b40e140c8510f1803140704420f004041e59000d00c0b036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 388371852 1250 388370602 388370623
    0x5150a09060c0810181d03040603180b0f04020f03010501080d18060f140f18010f0206040c15110d030501080d0e01020703020906040f052401170406090314030403051803 74
    0x608100716040c003032400880c0910128821000307886d011014000710b90f001c0d00c0d20075000003100456840740341040180a6603d0b000d500d00000120039260390205000b00780d115404400d1550100060b0f64170301c00541d085244801d45a0551310713200002c40d10b80b20024a0200d600d5580d1100b0a0480c0742d04603550362070703441c5d01407040045c40000c042c02c00903001c1c108981944d10a15003250403c47d00e2104402c1c45c2d0446a043c00a031401380300445040e5800c00d90f0002220a1840a07003001d1526444040340c07101c2c5481030031640da603034426295550707210300d014900303950324032003550045a000a802000351500b8059220207019844600d480709000c4c05100402540c10780140c01c403907246400304440b001d0000c0610342c1194480c03111304221900ea11030144242494010341040b1041c020b04481854016800d05050002101c0399502814809000d260b01550080c2c0100380c2120381e28080b43d10078120850420603000110a000405070081302170f014005034844045040300a50042627920403c0c00c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 388373102 1250 388371852 388371871
    0x60e0610211214041706061309240b0909011401050307081506011b1209050301090b010b0c1504030905100f0c02153601020606061605150a09060c08 65
    0x10b01e195020300400d01d00444840710080c450400ba074802c6541c2050b07030291031500352904a003081004601c0c0031101000902031140040110b8140d640c0c5072440200d00c80c0fa000d0030304068080320040c1c41c0341c81d0001680c1000142c4142c409044c00e440090182c820300051500600000c000850325003070000700c1d14100c4051000400c804410400d07a04003804001d8045410000040000001d1000c1c0c8540140507601c04d400d01c6180c0421550000c00d07400d01a00054440c0c2d05261005001c91031a0f4005810340d00c00718015941c2d07110b08001c0300e20f40032221017020844515882003005050704080c1804c1240c2040d1030019210031001c1044a4181c03000b4041c0c40030031581540f4501608100b54028442d03810320200c5403400304280c0d43c0907480d4440000c01407012541e028040700d0000d250301d072151a95001c0c00204050300302080055001c2c0038011075001c100601c4000311081c44130422040015092444544115081545080c006852180020340340c96041c01e005c108540c1c400e00b01240701c0e5400d00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 388374352 1250 388373102 388373123
    0x3021512010312120e030a020601050a0b040504052a0403060b0405071e110f0c040b0604050901120807020a1205010513030816050d020c03070209011208070f060e061021 74
    0x60303481a00c0e01e83c00420103010450840d0380c540f0800c03907500c00d800b004544c0c0f000451311202c601c20002c2c03400d601600014040d0000c00790800107841080c09850550341d04035000b0510b80d40341c40520303105680642c80240000a404150100e80103e6402001541d0050700e00788540d20180c82030005551055404d0f00014034400c5100c05050b14000d55086020001d00d0000c02c2013412542944c68855501a02c01841d0400303500340070985054810320308507c00c180c41c1c150070207103400d0014120090501c140142c55001130410400c000340034044401c4c040d4003d282e422403a40300d502c1400d08000320f0070700329084d600e0100401c101a1142800c07000b4a94140d5803100203646240021882c0c10034070342144148007050090309501d0f00c10340040c03c50b5440010055071220003500420540310342c103903c40310070020300d402050042a80f20302101c03002030f04110100d020700c1d0350745000801490040344079001c1d03000b01800c0c802d10205030881c0c2c5040311940b16112044244000c1c070305540e0b000350030006016038803e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 388375602 1250 388374352 388374359
    0xc02150a02190f030f080108060a0b06070501050106090f0501030e15060310020c06010303080f0906070e01030902030a0821010810150e0a0902091e040b04050703020d0c0303090f151d13060302151201 87
    0xc1c0c0c0bc001d02c00d030b40c0640b00038200701c0d4a9580c0ca096072402c0c0c01c00c1011608c5918144011000c1540c200000c000903c2d00740040691090030720344800484850118080310540001c030181c40810042081107038856086680b0401511a66140c2c0340a0104600141003140816424085000b03140d0081c001d2002619442e1103c09080d0358030565a40c110f410b0544031020079001d66000c0c0300c14010f4078060441270f95101006201c1800e00030307110849a1814030083c0041c4820b07800000c0071041c0500031200011031201e081c804440c41441640040f03540c0201e1000c20905a02642142c0503542c4242c2c1d035040162550412080d2403140e2141100c4868080360006010603201000c41da08140603c0a80303203601d4aa0300810540000b0907400e80c0c80c64102c03d000c008041d44480d000c0000c002211041b2805403d01180024614413251594100045a0f5054029515901c0c02941110740140740400004e200035052002d8200b500c801da20507100c007071010039003d00701001c66950113500040341415a0a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 388376852 1250 388375602 388375621
    0x90607090503100f0e0111030901110403050d0509131a010906022410030206070506150d08030f041b080f1b092205060408030103020f010c02150a02190f030f08010806 73
    0x402c4501210a0341361172181010386030070302c56802161030f88051b584d5a850722000c51425540041c0014400030b0040008102140020442011b05401440c0c8103036601e130240b00254a544483d92070303034001442c0000d0340c0031b00c03242c040201c040380300b0a072104c0b0503455950b90f041c2e0b1540d4030218003d1110000c483e00d00010380c25000255404000401c3c0e13144503644a4001c50110b400042c0110f403160300c21014041d0490a4080d201c981e50800c8511006145160b51110003030300025000c011030741006404142000210a440181e0100035090b0a50507a602c5610342d994902d112450400d5004010b2703244941190800710324080d80d4003030000c90b0680c4130402141040000140d203100040742a284030800148207000680c010b60040a443d9146d50443c010071041400c180181e0307050041c540301520040c1c41d804042d1404850ba1030445031900314920302603050144001840500417441b2406e00104420b6040319500e40c0d00940d070b15451410410025602c800c002c0c09106c00daa40720000142c465034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 388378102 1250 388376852 388376861
    0x90a0510050d08040f0617240918161d01140d14030d020d0609020703020a080c071805070e1c020d0c120609031b030e090717070809060709050310 64
    0xc3c0f260415900d0640d49009911010f10075401500004042d0004904100c689849050b00015100708101c0c0a40c0a80d906580242d01019040d006090301030005446441c44400e17010300080001c2031b500c0781d040815462203d54103500410b03101c03004408007492054007048805058428030a4070940181c01a400c21a4600940b20210703600c80000001e02d03800d91050016001d00460050b0160300c40c00010510700554000c0e030456035103644148102c201080e400a842844d0540040320b0543e07905e080f5400c1410500700c0d420040b000c802d21000400e80201c00c0d4001d512a0344141d03181f01842c1e4400301000b000c00000c03d22125003081c2c1c80c00c100c0c00752414480864030039100f120110000b55403043c044c2c038002c110741c0003982d01c50b96a490910525802180300d95200c09440c60181241c1c2d1241da0181482e00c01005850180c00e00d240058206802007010700008141d0148800c510300e00250020007440d0300f1075600382d15019160100b03504a00a22002054a00c018050015100c4001800f0001c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 388379352 1250 388378102 388378129
    0x120411031b40090c080d030f0e192102100b09040302100510050907030b010206100506070b0a0e030316090b120103141e07051509100c050109050318090a051005 70
    0x40c0c0da41c240c450009511442c3c480c0007042040050308030f109406001404803840503020101150030403e10340302750500802c0950384031011034104103442010b070420041c11040e9054185842c00584a00c265080c1c0014052415501550084c081c50b003200041c081080030035500200564480007050309034180907042140c0c4580041e85039a002907540c0d0001d05000420f44244010030340d103820150441d45e040c0300050b070102034400c1e0310041d545444007082c141e103d110b00242c110300d88240401c0c81080b094001018800001040300d40303a04003900f1814060b04108003080200360101400074180998800b614021400612038070190b030b10310b44416400e9017103081f0a1102d8003440d80841d8004041f003601c0c000b00560000103200c041e0904c0c05003e00b02980e0f07510003c00341000e0010114030785e51008052000d4480f071508120000584c034100d40504880800148503010103d24009481901c16103401e68003400c690404040d118560410111881030360250b009204490040c4100c0c1004001107908 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 388380602 1250 388379352 388379479
    0x230c0a09230a090f0f051b010e0f060408010c110601060314040b04050c100207090606030b0a060e010c060e0303041a090601150504121103120c03120411031b 69
    0x3c0c0e0220740d86601c100004800c003150742580c07502842081c0b1000708980d2004800c4c8000440c0955405030010709040740f40700040c0e1007207000d1082d107119034507400c0540f401040000001d01280343d407505c4c094010b44c4440322006c00d900c109400010341c1e500c0b030301030840d00c2503116503c00307010340740d0380c1729100c00100040c029500c5205410100f0740617140c0590103000000c003980500f0900341450200c0042c1c4e00d959100300101418480c82c0c0d10380b52f4503030400c401180e00d01d0500824132401800141d03080c460703840001c3d111a103407444402e000c69001c0019840303503100e08000c00500000300700714203801405a5652000e544103e005012400501c00039080a14044c1482e40c1401d075103291a00c05000d030791804490b000703180300c040c038080d08040000c084881c1074800828140303d1581c40d403139a2030060103a914001040a03002c81c0511040c003402000034200601a64166020598000000808041c440c0e00900840c60090503c20b0082048050407202d95141501d0f400c0c0c01003440741c418900c9140051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 388381852 1250 388380602 388380611
    0x70803061507150b09010f05030c06070c050d0c14062107050d0f152103030b150c1518031611040e0a030f0201050f07030504230c0a09230a 61
    0x80b0303000d100005035000030200f000c1030704082c05090004900040c0d000030000340c0b00001c06e2003141d401007441c0c44001d070290350f000e48520450414288503d141d9000786d80027000742d20464141f1115007140d07800e42c1d1619140e454103e0038481800a988151684c4d443c900000754032a14144008801d0f403908007000780344c22410280c0042c51407040f1120001d6824419030381e184c00046181c0d8901c40c1d00001c10040c8144011040f03060740c00b401d16150081c1c001d04243e9904000d8030760307549e0103035581422555004080e85a40c0c05480340c075a42d00d140e031a100d034010018030004a0101400e0900c001d100029005903040c20f6400041d14078a0001a904807034088018400582c1030304d65202d2050b0002d0b540000708010300c042e050203442004070342d01d07210459041c0800c00000907030300da1940303401c0861840c000400d079a60b400c0c03000c0d05d03100c08140220480c000e0410650031140c0014001601c04048501c540803a0b51005404d084405040d00f010b0b00000501c000c8404a289a241680c00b07040c5020114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 388383102 1250 388381852 388381867
    0x30f12050310181401180b031b010534060f0903050910020c1305010e07020f0a030c0f1203020301060905010e0d0b1009020d021c051b030c040e09060a0b060708030615 73
    0x108213003604500304541e0840c0c421405001e05004000342e480d0250040c02c2c2d07003400c07641c40c044011074103100181409400102410010702400014062800d9802d00c81d10802a62080c0c042c41d0360140740a903a218203201224070150b240b031044100880e8144c0300c240c80c00d601c00c0301b800b60051203065103130301b58040c14005000030344841803280060540c00000140560500e0b80c0203081440240c461b804550282501d074802101c00920501d1807501410f0400000500d0b2030250400c11224900500300894201c070700f02e105030582c01560680b80c4540714042416215030044424070394130001c4070f5210030b000c0c9000e00800c030030b802c0060b000a9280040c3e01c0094171040340405a130300943c9101d0a055000a0b0034400008494908160400380103080c8483c0c14100341881080003562842010a1800800300d10488118001c8030000d107481d001901040c07070812125a00d82c1000c86000c4c2c03610741042c0c40e0140c18505001140d14035540720f40c1441c15a01c4404c2800b00c0e01000300706229469508000c0c48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 388384352 1250 388383102 388383131
    0xe1210020304050a0b16170a060b1314030c0a1502010209030307050709150308030402090901020c0d110d03020c061303020703060204120c090509030f03060a03020901030f1205031018 80
    0x1903202d94041d82c018449045107160a24010000502d0380010070292014103040f80c1e4084900e5080d0000a85509100d4480c540d8000003000741b07a1043e0807090000070421040030700821000b08030792014034400140342c400c40a141e1103071a00c5c41e01d42e034440c82020b0207004c0002c8030300080001d64030601c0010b0170161309202180c6103520221058680d035004074000c00c0030401500443e004000c001001c0b00e04103280d590358040500000e400280310304900b400240d5031720f00035410740d0240d05803e01203d130350705805a80039181030030b11a040a05c0c2c1c021b050105545c140213001300c2d40891680401007019a81c2c2c501484145200b42000310118011b040c1c0c000085a2140040d00261403403c155100440031440d000c2c00100a40d0f202c3c03040c00b800c05041042142c000b00c16103c89401001040384c0e80e690702400607019030001d400082d80158804004000e105603211001015442100c07201c100300791400091302c540c0812650890f09036039100040c41011400481400001d940d0940415511986d404a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 388385602 1250 388384352 388384357
    0x91206021e16060b0f0d060509250501030e03030709050d1a04080a0e0f030c1003090f050105010305060c030103020d030c05010f0f0c0e04090b0705090307080604050624010e121002 79
    0x641d070484100180c440900c5410304c44c4d41d00760311040320b510903008100000310b10682807000f00503080e541d98500043d80e80605000f81842c000c03190000141540a6030660001002c09020360303400645010105170b5801000422240920283e440741120a40f9090030462a001594000c5a01d07008081c15544424000030ba1a400340340306001c4280c42e90703c17104008246c03441c8085c03414403c4100d0041c0300000d8601140d01c00144d60140c44052aa80380c50a007540607203038084000304030b0138088084405000301980568180d920503426282c898441c8030002c6103501080c00040e40c865449840400041d009100454580c0d20610001c9000341c604914642120240824403180a48503045d81041d15800130612040d580e04480c208a8a805500c1e04213a6400083c07140060240c00664102113a90402c01100204001402c03202c0380c2ca0300d840c006441e2201134807558214001943c0300b900c140b41d014001105a141a52000030090702c00042040212150903e038480e030090440700070204840d07000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 388386852 1250 388385602 388385617
    0x130e100b030f011a120f101a0406020105070503331305040318140f0102070b0d2403030e2e02060907080613060b011209140706091206021e 61
    0x242800d190314114520368a0618010711343d070b00070001c10010001814101d02250802d08540c05644a680c2e070390040a00c101c059046404641c416075028006082118010400e855040c1c3c02131090b52242d5409440030302080d00c9800390704402e1080c900080d1301c60980c01424841d5000d0b058402042c480c0070651801d840301240a4141d10b5000704028103801003200042010110484500a440c1ca0180d03640d014661903c0361286200e542a184c0d240e00c2000b0140150500d10f40740e60765003400d42844c00007000031101c5074031190780817031854454240c11611038085980648403940542c0c034400c10000c0008031000205003400c61100805d1203034886a03001d180c0e103040358006108504021101624200150f0b1180516900410400c21004500740140c1c602a40c03011011510022680050f039200c808010003404e041c2c60038072004e05102c3c00c3d0b41d4005034400103e041d50700194480e4003c840d0103102e80111100c0308480c0102c040004c145600501120384110f0010b04080d6001b08000e00540c8100c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 388388102 1250 388386852 388386871
    0x6050c0702150c070302042307080f011d0606030a09120c0525031b030501020a08391e0403061d1902010c110a17070506130e100b03 58
    0x28041045040c000888000c00d605040b40034240303a00c101e0b44903518000ca020082c05151204807418a002c1c1003041c1086020f4800348800e020300d0400c4004120001c00c54940f0540c41c2e64100000316508010b0009042ca03030040411030480c0e0f100c50610803164006491008041d1b901d1104002140a880c4488044140c6907104140d0700c0703507410b01d10301e03065503061540c203c00840e2041c540103500469103081141d0740b203281c81404042880210f42c200f0000d80c0044d00d194000540100c216601c410001d20a240c80c0b01c41e4003100d15007075410000b207480d110700d0003042c103008148440113119690240ca40d821003402e1415001c14038251310b29071504194800c41e0201d80728800b00e21070b04824070030768800c01c170301c0d0006080e180501700ca803108840d413050019043c00004110300c810301c00c41c4031060f002c0d29405001020a243d0b01c11010044400344400c08407140200003011400307240c85811103c02104400e2480d805034200301c45500c92030f80250082c1032003034102c01d00180b07032400390010314440c0300c146 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 388389352 1250 388388102 388388107
    0x20030d030e1203010503030d0b06120709051816080604060503030f070b22080315030a0b04050d110c04020a0c120503220308190b0a1211010201110412020d06050c 71
    0x280c64142c641582c00e003207030b10601020700040c400c54500009807914407031f05000114880d00c0710b8020500c503100d0340942c06160b04a41c001c00c0081034000b0b03264421a9070a90301c11a580303080010b06211004140c52145041d55101c0d006020350f4400c1d0020364202900510000b80d4a030b40b500040d01d10761242040c03600c8504017058440c1404101441c1550049550403220885503440c1440c240481289400170900c2102102194600e2071000c0244d12903440070f012102408130504100441785412182116644215443c08815030320848880c890300d03801c1001450b04250310b50802010750402000d100420203880703003031004070b0090300b04006600d080380c403002d6490416424800b160a5010074403481030200c681d074000041c1e441624103610480d442102c1c81d4212006020001801d03910101e1a800039074541c0101da00103010a05e403000c2440b6800843c0c1d10380c6018016400c0e80d0048440e000040c00a201c108401b001c4030b09812122840103110760200903075603079204200c0702e0944590b500b04401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 388390602 1250 388389352 388389371
    0xf0402010915030f06050604030201020604150b06070302010b131a0603092107121d061b0304150e030708060c07050708120a02251502010e0a03051306180320030d03 72
    0x10b01c1000090306c0240c0d0120315160031500040d54426010304020b00d5100d60100410541d01154000d40b03040c1402001c0c1592050141002806001d0301c2965138401e145481d1b0350020b655042c40b901c0e000d851803d10541100e031040d0200042e50304002d01c84a002d001e003030364041c034889444441a42840b1040c503640c0e105c00260400032254528800d07603c0c14004503101c286841e20342c2108907801d40800b140c01e80e039103000c24151030010000c0740a841c0c80500c0041000b25401c02981d2220903003030100c1d130741d400800406104143d9210010b01c14031600e0f030444400310700001e02e900002c24149020344202c44060342c0d41c6c8403803858201c8401c10040030081c045120b02205e0350500c80304107550340011004080078807084e400000c00c4002c1c418019403c8500907011038030b50003034015010114040302503070758480241c280075056912414113106d2201503800089100340c00348882c0010017a03843c2c2d4002d54242103a81d844002078010b44016503c0940d07038450076050340e0400c02d6900445640d50040b80d01c808 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 388391852 1250 388390602 388390631
    0x30f091a0c0a0212160507060f030b0402070f02010e2d0103050a0c021c091d0103050d080c090f1206040c081908190306030c0f0e0c0a05030f040201091503 68
    0x4080c012503a003000402c0000031a41d03002401c3c48181ca0340c0c44085a490300c14401c072884071013000340010070501803100c00040c1c00b038000c458410742c88070755202400500d440c0d1042008034800d0300c40081c0800d0b02e101da48805035108410180d000440500090001e990740c0c09040008000c2041c2500040140071180380c665905010b042d80041c26030000340701d0b540f40c118000c1c0d1075150920711100074480e855501603440b8810b0320008014515440c803142c02200c1590070400c60340090106484600c2003c42d000001031007400c0c1c01e48204000c2d551103051070030704020088440041640c8079801040142e05140b000410300c81e01e406548108001000c0768908200c1a00f04240c5001049013a001c0000b000085505241180c01c42d01d0050f036070350601c1d204004154001c003941d402c060714019041c0781c00b00341310b2880074004050700c410300b44086003030769400c0e91903c0921402110718001103037070010841004000344101c0d04144141001035100e80c0710f07100b400f80c00c0381c000302d030800003910351788643c20595 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 388393102 1250 388391852 388391903
    0xf1112071a03041a0604020d020d0219020c060d020702031501080609210901030f060e07050a03050a05010f0e060102010e010f150b03060a0e1f03110108060901050f040b01030f09 78
    0x10710103015415890691103000a0a2184600b42d190309034a00014201d0f9490703504a880f0380a08000131521010ba510164009410030b8008021250121040c442c090340009501a02c1110080c0440d18007401900c081d0040c1d00207450480c1c15102e10f4514030072a102594405010340800d1004011514048095602e02146c2c0090603000c1024116002c12140c2403c0403a405a0020708004c01c4038039490543c2d0004046981c45a01220100818400c92907401030050441d40150f035400e000f5615608495030444400384128081d007440790404100108039204500e901c2213050000041d01c40c0d14886d0a400d549c101b1004110003591141e0b010b0b20518924404005001e6503141941185441c0c404511100524001e500c00e1030900d81c00502140342c418013039000701c1e41e40400f14a0b410340e070380f40c00042c00204624241c0800c0000c0c002a1980c20700d4408e85040382c10042c0310328003650311201480010801c038400300c0d0415407205540c0c08180483e000345041c2c180302d80010b45401d42c00c0c0800c0780050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 388394352 1250 388393102 388393139
    0x6030f071205011406090a080d02060702060114010e040906020717030612150604151203050a080a0207050c09090102070c0b03040303230103030f050405041d010501090b010503040f111207 82
    0x1c5241900501440041d065100000380c0300f030b280c1903501c2c00c8210000c1c40400081c2d02c44041842441d008a04007640030031081e0040600c0d0302250816603d0303000c00c2d03e40c141d01800240c00581c521606031a6450a50020101c050081100520700b50242e1076950740711658180007402d16000109010301800c080c0f400a560b040d10300f016004040703210307800c1d8040010150015209584560300c6520700004100e0b403c00401180e0920320840b1120700d00501160840c40c80c1d280807034031100c000344c0d1075030550084442c2d2a6021018200000d215402c0043d100409820050290750a00400d40003420300000341c0060144240070780d8407480e0030310f40202a90310b0041c06442d6089400b01c00e0350030f00d400b090700c41d041d40c4c5e01d828032040c80d021041d01164103010703503170000d640141482000d450b0b48801c15004100e0b10104030080c406a0307240c0580406803245940c0c00343c006001007000902240d500910030b9181c5101d220300985030884440050b000c0064134106400b5a04040c0c0c080260000c884c1004024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 388395602 1250 388394352 388394387
    0x10303090914010e090309030d030b010e0d110910090c03022805032406030a0207020411090312030901060f0f06020d180303050309250f0b04030b0105010c05070506030f07 75
    0x40b45001c80110031052410700c030301c40d010070000d0003080101000340309030303107000d2800360840b6141d00c610540180a456900742c11408510b8101040e1200d0416041e0581c0d0150400e404a8446045c032041c40304030040103003c0000c100c081c82c0045000c800303e0040c0d02c91940b155602603141c0000d40760054140d0103200b42003102c0708500c82003810454005d000d40c2e80c802510503406000000c161446560344041d0b082c02548100300001700010741c00183d000e444410300039142001110b40ea240e101591703100d03a4825541c1580051159010050042d008552042d040f90000c0b03445940e52400b4040660950000b22105410000902460b07a041003130045000142c07404008095001f00245031400390790001504124000001038054030080000c2e203041c02e1804a000c0380c105030000300400c455841d000e40c00303105800300c40c0010030382d0842e02902c3c1903a4200d000010703140d103414019036401074885011030707080c01070981c001130568400d00a54411a08008814030520f0400350060409074051030007900d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 388396852 1250 388395602 388395611
    0xb0d050a0c020606010c080706110403140c0f040f09050f0a031d100c030302160b071706030c091008060a150501050a020c150f030c1e0a3c080103030909 67
    0x101c070b038001109a0801401c3c24041d0400d0100d0814202c144102100034210b01e040c83e4080101111120081040f24055040d0034407000c002d9181c16100e5808800c00b03940904a030a0b00039452406500401c2500c841c114006503005140e134505081c41c407001154070381500100c0e0f1841c00e154200c001c050250307050744194000744081b000000c02400020300715504000804401c1004c042c002d078101c1c0c401801641c1c8852240c4807501d00007418041c111646800600d1070105884600e604866541c00b0303400007805441c2504130941441400d8800800d0042481074112000403020030031f103c810b002e44910800400d100b06c0c1d0b10304154280e50154041070410504000c1104425804070f1140c1c490031040f501040c462921000c407128501610b420703498010750003c140b144081d6644004c0c124440007040c0607542103540e0010310b1080c0913100b0440081100b0103450b6034040801071401034030024003091070303d500d040c08060031502ca4003100c0d1100490f4090b0018401c2c1a0001115001445068803d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 388398102 1250 388396852 388396871
    0x513241e061502060106050f0409020304050f010f140f250e0306100501081612151404141315090b040302060907181505030a08030106030609090b01030f020d0b010b0d050a 75
    0xb03581301d905209200800902040c410070100f800c008032002484210001c6d9103a00b0700d03040072a22104519109d0100750718140a1003810b144901440c440501940c44000040d501c10080d917604800080210403103000c6d14510100c840030091150440061a40e240c40b101070020f0b0526142283c054203140080624030b00c01c021907030b800242264400701100c03003a0f403000050766040c0c3e5080e2032180030360221820710144500c400c0c3c003450044200c8001d55400030803161902d052200700c03001c009030003080d00d0303607e00003c404455a004090120344104141000040f002c000c140450f040072608444801e1401c09100c00e042c0e0400840e60400800300180c201e0328541400d1030045164006c181c0c12441d103944e500500312000040e09401040c01030700381c0e8070302c040b00d14041265501c2401410082403419202040320754080c4122101598409072a168076425134070795103000200e10798100da0000041c400341f000209201a460700a1842444064940700034080308800e4607802041014203603d00008107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 388399352 1250 388398102 388398107
    0xd1401051e010c08040801091b030f030c1106120610031e1a03010e062202010f0509040b15030115051207110f16030311010513241e0615 60
    0x2001020302501c181d01d510025800140c0c0c07000c40c40c800113001c410000c0f03800580040107402483e21144164070800c24100743e0202100075000c6800060402e00103900e051000078003500000c82d5081c041c401e407191009540c0300150856000603a03109044201e1001e005841c00d206003402007000150800f8400316000d003800ca1040c00d40880e1500e8019110010200881d0112440b10001f480150081c000d480302c2d184440d90394402540c100e40352040d25010010303514010100781040c1ea50507941c0495507011800103c50607003084400d00e5001d9540d450442450b80c54008112540440040d22600c03585802401c0008083c950200402d01c01c1c100700034400340a8401e0081d601c10928103155013070b52047e800c032900e8032080362500fa6481c8901d69a0208444031000b601080300d1096640b071048a19581103582a61401d4a5030321060441d1080203000628500800549120480350b0410b4940302072902c00644100c94040c000c0c810582d1509114801140a820040c00078001d06031a441d5006800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 388400602 1250 388399352 388399369
    0xe0102030715020d02070510020309060c0301030b0106080a0b10030b010909021309091a0106030e0709020a08070c03020f0d0801030b060d050604060f02090a3507030201031a0301020f0d140105 84
    0x310075199034005440700c056801342d8141d03131415070803c089800c5441680b0201000703603c241d6554529120300800a0010a006002c0324140da500a10364901a4a8248155008480078200320300c640d072a002c80900f03549804051415402e1107690100c0e980031810000b600101d099001a00c2003401000092103044480341850b0440302d0900000880800303a041c000d418400c503600c426240807058000003442a41900100700e007c244809851240d55685441406c07803080080e0312000c5068078000030742c4c040c0030380140ea040d10701900585000000c4410400d040400304c104070b60205103000011700900000032121540710201b902e5160240300305465881c1e031030b8030051005150380c0c2c50300941004102e86805641096402504820b0400c3d251040b80301c0030441d08050802e6072a14402c00540e1840b0100b01c0b151174445030003d001c02506580045000d00321150304002d03042403142c180d1095407401d10050140032070388a1440c3e202c0c4603d800120948400a404075505508080140b00560300c000c00d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 388401852 1250 388400602 388400633
    0x903070b0712121523040e150121030305060f0301020a030e010f141f03060903030b0108090105011413020c0303010e06180702030a031802090103051c0201050f0f0912030a0605010e01020307 83
    0x240019405c44190144032a00d2441c0000c0e0010304112481d0702e542000076060400341d1500c0025076140c1c0c5c03070300c6101d1400d050385041420001070600241010078040c1e40466007000c0040d03c2c21690301400300100b0309982c020049000007d03502d10302c4401001c420710811200700b0100074180a0203914844060040300094240342d40781e550020140d4000a01caa0310310b005590000050051008905014000f08094000139000c9501e103000030303402040610815045e1048401111400f90400040c0300106120655144009a003040781d011944000c0003d58000d141d515500343c2c0d940f8100052003251600036451210700444074061014007a000300a0315241c20359882c000601441229030081c50b0b02c0c00c000d000c0c0d0048207110010042c004e0100f1400440800101070440541224034102e0803281d040300d901108980d0800801d02051a8501450b0000300030011540314400700f401083c1075505c241c0300703095010b94522081041c1d50704800606903060090014600300310380703a110400c0d203021140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 388403102 1250 388401852 388401869
    0x60506030412050310090f020d060608190b06091c1703010e07030207061b0807110307050a0206071b0602030a02010c03020903030318010f1a03160305120903070b07121215 75
    0x4001740c5008000d8412000070102e4003010711510b07400c0080741e00254414094494810300707002001c00c42c50b01031256070b03004e080c0e15030302502080352202000b8001c0001c41201136000f08100001c1d169a03031403414004441c0e18624910507500c58600e418840507140c1ca65106101030305000400070441d1b03103001681d01c0600e40c2405a40d074007051810700000c0003c8030340342c1d001c01034140a01d1032540d4031080c1716120349031580f82e0181160302e0700b0b8071640e82d009880c40106680c0c08541d0101c01030800c0030150944900c2490780410019001c2d1f420645030601d038005200507400071800364a00c0b9424021400c40c0566401e0440c0b800d450b98001c0381c0c0b00d1200030100c1e5803100880c00710290040c1d00358045507a11500b660208031440410304124813013402d03448124464403a20700c0104683c0c5800c2486003c80354000c00401c5841c070410038011403904146001d981c54002d9080001c0c04114a00013001c95510404ca2007910300c0f52400d014210071424032203003000c9480d0403070b103800c4950207500f554150790703a11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 388404352 1250 388403102 388403107
    0xd0309120309020f120606090903040b071509050708030c010c0503100501081e1f05040203090303040b0c0c030d0219020114130615080d082206020711090403050d06050603041205 78
    0x340080f440b1903c0021301c0039085000b030740480d003e01002003461800303030f50111380709404c589820324803d03501c3c00346009090703058808000d0000000d10800074041c08400505c0041042d4140ba2602400c2102503407104040790000108546440d03801e224003036800c0d61a082160071070802241412460190340926418840d001c0082044900310b401000820440c0e10904c080034036041c136514624045034040306521454402002c41e940ca0705000343d82c0314251801c0150b05543d101d8441074007070f501c0500080300031401004003880504d800e000414403402c05400c0036a0343c0f8000c1c440f40000540b620181811a454140b40d040500d80300700c45640c10001c0800c607030420756607c0c1000d0009140c081e2881a44441888000581c1d010114a102401c00f041d2101c250039682d4101c00d4040e10811004c246003003040310905030004100e0b9014000d428080c1120700b103011980300205800c030344183d509501013039002c03c02407801d610902502c00079244c282c5080e030460034603684800036042118850030a01102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 388405602 1250 388404352 388404371
    0x10501030506190f05030c09040503220b040308070c09020306010f202b020607050406050a090302030307060b1f2c15070303060603020708090d0827030d03091203 71
    0x40e18032010842c041900104040c5580b0301c0c071300c06000070b9841814020301404480050601e081440300d4403481d0803c2c0a903243c03210004c0424001c4900d180d143c451005032000120314080680040e00140d4450491265150700c1d600301450700c0d0f001640640c603090700404c100000f5991011a14a000c0c50905004040c0c00b030f607174001003a0141e05a2244418820511a408440500c620340d015803012038030811071410030100c0480c1c48550840d03950300420000c00040203038500c030340001d0423210001e19040181980707943c0024110307400031000b62541030300c0b0b184403002d03807078107a41c1500c010605280c804201d0070000c0000d04440c1c0401d1905c2d0541c0070380d062541c0102071103101740059580060103e0303149001d08034105003039040000260006440d00c0310200b0f106003c0d2080f126001c1c0c10441c09030403d52624100301a420f40044100c07214002841300c9501203061038a001c501d4015214494038500d0a042814074010443c20804101800c2900f110041003001041c1c480b40259483c02141c41900d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 388406852 1250 388405602 388405609
    0x15112e0b04020f070c030213061208070c0e010803221d09100e030a1205070507141e0703020f100806120f0d0c03030507080c030a0f11130e100806010501030506 70
    0x840341c03c80b2080301d002410310100540c00d48064150f9108480400c07a40c1620b800c407500b1a40d45004201e03491045110140120ba8800050001d103032003480c04010823a00d540881d03106c420282e2204c40b1035403011400c00d42181c5030b018a40c034495050708041c0300303980c82c092032180c2d00242e254040c1d081c5003001000c078040e01e406200031061910a00e1080c043e850a0790041e0380c0d02d80c00ba01d03d03500010309181101f0505c1207580507142c0205900c4c2d03900d07810042c45854100826541021011040c481d160110b01c445d04680b01008800340d001010308140f91a50041c805102c401c0903101e4400e800034158180b885403c03582460300701e04181e640c0503010385440c42d440d1414148480c42402e6104442c904c3c1070544c2e101500c455600e2003664240300c5c98450400c2620303060300907190000001018000140c071015039601041d2094400b203004221b50144461000080d481851a15040036202c0c600380003039045101c5407a0000721403c841c2c6440d43c60000e0319611617106010380c0f13041581f5980404d10542c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 388408102 1250 388406852 388406857
    0x110607090b07150c0c020a0b041d06031006080c0a09060e011502070308030a091a04150e01110f0403030e0a080c0d060f180323040314030415112e0b0402 67
    0x5110348000c0044c1240352001521200701c0c050120312814050001044010303542c0c00341e408450016a10510300700d400c4540b0889032000501e0250075100341039040703402c00c2c01f90141d80020088000070f4000d80502e1820310080b64a150007007406642031180400070002c1007052103046484604801d00301e40700ba04001ca080414551000e40000c02c0401030180300c054035030144405e548200440801d8402d141e1003003581c03200c200d6002d8011b01c0e07103c44000114071507030440c0702081404000016030b05103e4246c05819000403141d184d15840c045418010181c00c840300d0042e00c0c004590722800700d80350803042c0350344035400c82e0070500482c1003981d85020001c0702d030448050001840004e02c0080d0000e40803902c3c4040c4d040050f00018803c415200007800303404082801d5040d516001403916085407103066008044103031014080c40208000070710301800c281d1071240e0018a954410042405541c04c41c07402c4c0207040e01008002e80d000e50b02c2049906441c1d24500c079041a40c0c046040110130000130000e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 388409352 1250 388408102 388408133
    0xe0d03020705121e0d0b04060f06021b04321f0603110f1b100b01120b0f061308070b2136060a060e0c1c020d0b01110607090b07 56
    0x159000c034200c0c150700708541060a46100503a0104888e9594071000d5100700314511a5401680280c0da0440414107040020114568098404140480b440c1e444004400201d02001080c07103101d90200980c401c445d05140d0440c15200c0e040a24240c00090384401d80220310658052540da0241c3c0c031040c80d40f010648860700d1000d0210f40d00c0b0801c0c1d151547c0c001c070b035000001c040c50040011004602620b03224003046804107070f46d411050702030300c502c1000401d203020700143d1007020341c885002180e840c40000c0c221040c80c403100402c80c3d0b280524040c45d102840c2c02c0706a0140301801008500a211070b070380b01c00303100c01d0b096104640d190780c410800c50140d6801c44561300d80b01000d1140c107146c403a4107480300071010101110349550b02c0150420444880d40690014030001c040414039003041c60014140e035516280d0310120801d0380d4510f0f10100e038003000140d801e094950214194944c0c014944603003c02901c0c010f4000b920340a640105045154000c480e0750020104400c41440107001c03a22940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 388410602 1250 388409352 388409407
    0x3020a050d09090c140d0e1f0204031b051302070204140403261005012102120f1501092304020c030409051e070f0509030a03030e0d0302070512 63
    0x1608020700d0020804442c0c0d0207014507042c10602c80c80f03402445401e4440c1901c401c03800007401d00c0f13015818030000d080030a000010b54420f0701200070b00d1104003a00030003008402c04005a51303600d545800c1d42c403030030421111414040304220400a68617903485420b4012448840103980314150b2000030003c200741010351807240034007010001013580041c200c41949280603401c0a028a20010704003e8240482d40000440300e031000402081d4002d00c04003c2520408010129405107041c01c40201d07003010000702c1034851a10b061120942d8003002007a00300032002c02002101d100b920002c1e00604481c4100940c01000030b004107032141e40d04c03040c16040710300100700790f40e11415240515540e80082c0688074416150074049100c0c0da803c0310250804501c0074050002c96914010250b44450380c410203007081c0501013103400c010b65000c1c0860725109100b0b46002030410b2003503010920b04842e0200903801d1510400c420800309400298140030801718140741d48ea10790500d000d20362015600d0452001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 388411852 1250 388410602 388410613
    0x60d080c01140712060311060c0c0904050309091b09090603010f020d0b09011220010302040f0803070c0603050c2b0e1c02030711120705060406030617010c05030f0403020a05 76
    0x400c40d1002e58864010242ca41d1034440e8450350b000c0780b40454a41d40310003403040c0040039402041e030510f400a00492000e01041d41e640003202404248001c0045504903a16000042e000f80c7d10728080306410782142c10300b00141e41302c010000d00c6c506644100c09141c0d10501701c00c00010072659003504201c0e00c940b07a41e10195161443d503580040500103003051544981061720000c1a01c0c0c030850f4400e080c00b90044003d5540c1550400c4a460f5582015013042c1050303003c01c808070313803818521a080d008051260065607540014100b252202400b42c020008040c1810140704070304030210142c2d2600c0040044008581400110f01d0000411175410002807034203040f4101644500890014800c13070018801c510300603280041280c60f88101c101c01820003900304040f201c1410720780529116414001d080360032203500c1d00c0c0042c0c400d070002e502690000351180300a10034509001080e05e42c5a180d00002c1c406070800742c0000d0030b18040108140d51581c922000902812700c00c00c888002c03031b40c000c020b644 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 388413102 1250 388411852 388411871
    0x313061125081b10080406090803040b01030303240b0d0204030b01080304060815060d1e0504110f0114070201030b0d060c080615130509100314030c0d09030308060d080c01 75
    0xc0728141441400080d01400004800003c1c9007100015220070081c03107130341040b500180036141e80c14090015900c003a0742d15503036000501c0a5008502450003500b4102c1c4035072440c54020250384001d01281d0034050b4503a407080303103042c41090304010f6810a00c00c0d580c603a904041124002d00a540c00580920181c03000041d454002000410079074145542c0c480e6155240f0701e0382c0e078805251061142c3c105c90304000d05903240301e665000110080944c100d9102c030b0044258040f081d1407050314140c0f81c0c02c00002581900c0d2604010302e400c4c0341c4080c00c203003451000160702c40c5507a00560901905040d202c0100e40c4403581d40b080c01e0b01880c0d9020b10104518402c80400900c2004200d507168003541c1c204402c00c0900007401c003078460031725440310040041800c00e41800500342020300810703049008842e0200004003e20395042e01d6140c0c00c0029615001000d51192802d8480151601070205041d021300201c1c0d801481243c0c089800c5e55110204285407a22007203903c50002100c0140d480c184246 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 388414352 1250 388413102 388413163
    0xc0105010f080c03030a09030605100302060c0d1b080d0b030102040b07111305040206090f15071118090601150210020a0f080603070501050a030e070906030803090f03130611 76
    0x1c60a0b00c080c44202c0d0941d24910051540d603120316141280070615a020130800608103412659104160700d01c1d4a0401d96250301144094024800c200610b0304004081c00401d0391080380c500ca4148038001c81a000c0072691500c0502e4030a103810342e004152902c56242c0c00c2d8400750103c3d0020405000c02581d1242ca9042811314442d03103070180f41c89007031030742d000000388000c2d809628011034009120b140761498500400080340e4441030b0158000512890550031200244090040e0700e02a10510203600c1100d0300708241d01c0d0f6030418180c0309003079180612505600003e04541590b90340c101442c1c2d440f40c1007009900c3c02086c9048110309030300001c1c282d81c0095000b0f5100c81240c0980d120400c03940c540d4810140c03212041e000e558002001031040035a040d120b41c02075042d4400d02801e490700316071680c02c028280c50311358106844100f000410b020a030101004140d103004c07100400303981821000c4040c03130058580c41c441c1c1c10401450030148620307850244951481c1c2d041840a0491459611078a03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 388415602 1250 388414352 388414379
    0x90421050a0801050d210905060d1d01110a0c03091e090f11030c090105040315051e072f0708010e0c01020c090103020108040c031e0c14180a020c010501 67
    0x181000210b58074000601c0d401c00e0710040c0c0003d0b50005195500c5c200030301c4078030b69406c4607480d00b81c10400d03482d03000205034581c44000d05040e811044007040a0202e0b074138101400c1252103071002c0b56131518822004d210f4061050302c41c0c0e103000d858000001003103414101c581061a410450803561901c001440910304154600c08580f504c0405010791741001944904403110100b880d0b48085d070400c0001d952642d039200a100d41c0e5014100f02d0308160300c03911040078072134503080250220399450050102410b1001d500c4900400121840c00d0740d0310f44290010100010500c81d00324000100c07404101055282107040000101d1000b15090580d8901c030f402e010b8154200885058001c4480b003400303035480820720f480c0b50903001d805404980d00c1d55004403202c0500500c1561200580803001c4001050b80902a9074801c8001351b02c510710f8014240400c03094403a900401d16041c0c00415032240351140c2c40007007000000105100f429549402140d8080c0c4a03c1507811050b5280034008926500754000303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 388416852 1250 388415602 388415617
    0x207080f0f030601080c0a02060a05280504020f0a0819110d0f03111b060a05041805040b01090905250f08071a280314041a07080105060909042105 64
    0xd4110380750305c0b845155443c1f88100400da00040c0c02c0700c0300107500d41c041a00425001003090989030710400c0700401b00c00c03480c15466058003905848ad000c2c0019490440d15000515030122036510b8554608400345035034000c51101058075014500e400070500c102e4140b500707500d034006491140001d42c0361411040e6604000070450220360303010002180c841c8001240c1c1d0012028203201010892030004200c01030708045812810000704000c0883d0400b00b502402c07100e800040d10201c1c0741d0800740f4101c141d05205802c29044d01c2e280100c040c2c0402c400190342980494076070603943c181c1c40401610650040c4540000e40c5581883d200000d0601d0005400c0b8202d4481e25420b0030310100b495102e801070310905000b6444100b001800070b40b00c2e241040c50100d5081c0ea424001078082510203045c4440c5822201078410306c61000c40b0078100340410100544c4500c6910f040c1e18076604020000b0114001e295485005580c03034400a4200858403482c40d503010500c210642c2c00a04000000b8110351007181d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 388418102 1250 388416852 388416857
    0x4051e0303040b010b030610030e0f0d0210050a0b060415090510120b10021f0e0d0f170919020a0503190201270320090c0408012004090207080f0f030601 67
    0x788401017841503a00601c0000e01101a04006180490141c04040c512604901520140c0300c100d55040200ea0032404113030b00500500001c0000480489400602101070141070010b190101d075100007c5900761810305903151045c10503140102e03101d4050303800150b004203c103400071540c2d41d002403c0d82d044031103050381844105004401c0c420364242071440540581e10100040c03011140d40f400c520049410458009154480448a40d14001c4c03030013081c80100300480c1c10780305080d902c2000c00c44108000290340116003000708600e681d510115103005014440c501c164403c555900c07111400401d001030440d1012503000c44850302410564408a000c20280d0381c6a49000700c00b1803040c04080f500c0c0345070800f040d10310740301c2940c000891034008280d40a03160b4030500f50340e1145005409408007118907501c907400d2084c12403c440c502d040c40c1080381c0312074820240c00b01c0740a0481e030a40f458080b0141c0c50710501c1c0380101c50746c001d00d960329840c550f010078070314035504604010310300c5006e099 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 388419352 1250 388418102 388418123
    0x18010f110408010c0306080c121204121e03020606100315092a020706080c04030605093016060905031c0506010806012f0f030c070b0301080a0b04051e030304 69
    0x4c010381c221040b601c100c101f41c7c0c200c00ea0681041c5440c141c2044c18950600a44905803015001812142e2140d08074900d24944070b080d0f402404607111103440b560300c4218210400116580b0069500c1c40020078481c070a80d11880c036403001501ca50003404a030034110900b8080c40d6200d41c00c010240a12116500d81288181f003181c01e84a90443c0b03c9030200510b07005071403c0343c02c0c00411183d2540040c4400000d0a0070000040000c22070b105031071240791054080c3c80345401101070340307244890030800e0045084088668070303046205c4804907407400c0d00240a50020030518500400503228004000d0594000401c90007402c1c00b42c6101c03040c0000c4030403000c004554410f001518a2802a1584c03400034185015000e41c103000d0709803584d2929101191090040103003141d080c98800410b42c450701d0b6820101d050702e40501c080190801810040441b10300f90743c103001c0801d41da81010000a80b18004600c00f060602c0800d00103181c013040c10440700754011150104155072980195422130720700044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 388420602 1250 388419352 388419371
    0x11040f0603020a060c0f1a070f052118060906091014010324020c0c030606120a030f050d150302090601092d08030d0506030d050f0318010f11040801 65
    0x192080405a95000300050200e500f00070b0115007a01100c40119440c241d4210381c034000c259403108200641098035075090341441d104000501d4a403021724000c06000c01446500c03207549007040000d41c5c3c60bc0e0442c9103026540c606d41c145070110012a9440c0c3c2c00c0c0940e1040c40b5024001184461003034007100101d54910b0000a80101120203080d0f1a03155050200014000101d80401c2d450220f440407070380c03506004016542104a0384100840402035001e000c040400c0d0034180501a4007040c101c80c4820504100391b04540c0760403a9201c020b0400c095110101141070088007526200340742c1c1d42c03042055418500300301e000829540400e1703108229840c00505958032849284007500c1c000344000111405070722403a40e05108604e02642d9540c046280441c05403020805880c8a07445400046000d00b1304505040c100420020300b0710802c0800c02c0303040c1f42000c10604403604103c1068100b850014514821401801c0818507040f01e00e0920190200b42100480a0400c0c0c2e0f0001e0001c0180615 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 388421852 1250 388420602 388420631
    0x3106020a0314120f06010221040501140301031a04021c03050901110624150d0b04051b180f100c0c05030c0f06070305042706061d090702030904091104 66
    0x40c0f8042041c04030100c400040400040400103500008180102e6030300c2140c6640c0105907201088990025070030102d0200084d40e803210410840c4a43e010a2614550441c2c4030018015040c0700140030035268080858215104c5401d0310400c2c4042c0407003c1407016051030014001d60000304501d0004d020303020650404103020511600980801111a810248002101ca4000d03c4a10800d9112071000b4186401e0007254008150810200c50f0010ba6a00d46104010448030090140c13070001c030307a19001c60300c07401140d011541c2084904031003401c02d4485500207010440c2281303981d80c005045030002c241c4560406d81d0000e01c03130701c9800d14262440e04c0b0000e05580c0c20b15410216400328241c00910039508110b0000c2484078003d20f0030601e460b8941c4000b90003500001c03410811410745070064003000e10309100da200500348510702880001000c441d01c45000300710a0100b4420085640030802c0700303000300110f660465024000b40014281820820000c211131105180103d00f000c884006844 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 388423102 1250 388421852 388421857
    0x510140601120f06060e031213030308060406050a060f08090c1815030303160306060c1106030a062d0b032809020415090b0405010b3106020a0314 64
    0x444404940005030390300e10045901c042c1011907000e441e550340e03c2c1c3c09841c82d024098000a0459078654010380010030040c50328100c2c0c460f08080d229113040c440206501141d8410004607030b0140b4084e1080c0c0c46160000700101350039445240c0c0524003100014036590409232540c0a003600391140401550f822400d1510b40c002010103aa0115030450303c10009103502000c1d50700483c90317802d0900410780c80c07408245140d006954910f09001c201c0310010010368117024400103484246002e281e00c151a641d8035813000c1c0d80c0034040d03104540100c0081d020500070390104008201c44e03891003100b18110907051050b43e030841c0f0300c906507811114001c600e104000d4100d0b4010b418000554061032030800c030b1003131100000d4000003001c81d00c0b004480051b0351640100c3c245081c1c800310a000880c68440074004590205110030b014034204801041002c0a03002031360079010401700491090400034090040703428035011140c000030002da10100d1865070000e00355074981d12070b4480d03504000c107810030a01c260 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 388424352 1250 388423102 388423121
    0x30e221a04230a0f02120106020705090109060b04090b0f0409140d0c0f060c11120301060e010309111c02330f07021c060f0c0e04060302010e060a0e06040f030510 71
    0x2d08503002080d04030800e5441801c1c2e04c03081590040c10485000c0781003006e14001c2c2c0c4031400507803210405215078a810310040d030060a0007901040700d94902051440580a54810020841ea5907114070b011130b2200c555190024074000c9c02040b9540a81c5810040034110b402600058800d402c0f08a812a010304a5600c080380c00041d409030042c241d03034400300a02600a4010100031100a1500c0944401c100110035000340d090324540303d604051004000040c000c240c80c0c1050300313024400001c00c85003112411a40781c00d8070340c0e50840c8940103100c903403c0c0346000000d422018034110b4803140300c4541c494500c802080741c0c20a018242c0f80d1110300c081c0c019060700c0303d95100e003007021100518142403902d0003541c5d8840030f0b83c0c040d540c3d070f26180e0850702e40e52100200d44c1e031907014840305581e0041d444240e9080c121010002030341943c00082074118a6003200d4042e43d40064403c494500800128049010040034a951680c81e4014024032020710b1100321070a2150358000c102e14849400f816401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 388425602 1250 388424352 388424411
    0x6080c01082406030c220b120c040803160b06040902130c030b0d030215010501020d2c060a0f0306060815060d1134030e221a04 56
    0x158031021820700c0182041240340900e08281c40782d4030700603100d04024501c0341d00000e280a80740d890303054181c0f02081051070240c0c968551000280000d00c101d0054485500d1240b06004240d0784108404880303200783e82008803648004220442202c91050752803044510441c0d9900031501c3d801e0520060300c006440c000d6014001c0c1040c05003c401c1940080f200c422540313004220701c0804d8010400740a0700070f9040e0f006800641c03003102217103080712409005082c2032000300001074950000600103404941d0844000341c03208250b600b4109410101c860311100101420b0b07660600b103401600303052071b4025110200b800c01000007001c501510211340704070744c1003512090001c132110410802d68030200018400994600d101c0c03403154500c10107005006480d1411400302032440f007120071203080400f09401600d03c00002003001983c04a0303c2080040700340d885034035080e451030036005916412010100a03501d813078024000c040c10400f5a0580d800d040d68100320041008100081100001401082 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 388426852 1250 388425602 388425617
    0x807080703021309020a0306050901140606030a020705010e1c0f0c030507021318080a03060911121b0a051306030e12160c0f030303050907030b06060a0302040902130906080c01 77
    0xb508002c032841c1e4424010460004454003e41d001401e245444d8006490450b624010451049024801c6164409181c8100b482c41d150120015a061100400c1240b2164002c00c0c8482044009d411941106c902c1c141a08c8078503460100b41d40c240e032000351a40c0c0004560421b07042121340103410141b0700d590541d65440c5048403d40a0081465a140c0b4003600e180da1100c1c0c070100400728000c9807103010b2058110360781d20388100200400351506500715100b1546003240d52030b140c602c441c00311204005802000d140680d0307540c0c1d440c0500740c0d8140d074026008400184c0c541169500100804804549068a40503252030300343c1241220380364035103010554441324101307980e43d200714050500c08968a40d41c80b1551895078038082c0001440e8000800714000460030300401d83c2500410754003610070300c014009146540c598040d0720a010b05050301030480001e943c07280612039012900985046441075584000354410b1701d0a2001c140300394003500c0e01c3d02002081031030001c5550031100105945d20b4a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 388428102 1250 388426852 388426859
    0x80c0703050f0f0c0c040e16050d050c030607030902271b0c03070f02040b090f150d020907110c030708030d050a06090e030301090b0a030c1401021513050708070807 72
    0x1d0701940315400d40ca5500405200045070b40811500910000710704001419082c81c03070a00340029a00c2e5180e00c400306030840d2041c1c10345046110400720481c0c004483c0c0d042d060036a03060080c02d220104900c207406015403001c110750b854150708400ca940344280c603002040c41c81041c0c070f04004000c50f603801c010041c07150045203d080713400342401040201c030402ca0703241c229621242c1c1d156500a01c001c4803042101c05c819030540c64203108000404e1015180782ea00b0749041c03080307105548002854800d40c2a4802d00f00e0b00c1036203e0045c032410b0342d40e01510741c030243d04029034060003011008070040501c1c85528101c0c0b0840c28085000001c54402c6e0006500308410454004040e01c030007052840016581c10740001c0035641070040404180c100d038007641c1e03294102281c54042c0c1e000280d540d0b0040c44e40d0b090410011b0712161510342280c1c0300c403089903600450040100d0400d5800c081e044603000510b0309001022882410004e1560322941c200c90095903103c640310b403129110f200e05952034000c11404c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 388429352 1250 388428102 388428107
    0x504021b1605091302150d06090e01050108030406110304090501090603050f0a02102a030f02060718090b1309060e0d2d2105060f041a011202070605010909050607080c0703 75
    0x2c502c914802000004446c1d9841300640d0a5000f5650301e200f10307600d0f150100988549803045130200da8019009205642c10440d00035031301d126070300c151070030001000c080c402c2d5190180103030780c094541c09205012075603507130f14900d001d403105003c1a6514040d001a01c00e030349a00040162000b64050000c0d0100150a4001e8483c201000c1d11050304050001918086018000780900114841e880d0500c1744080c0480c028a444802000a03003403002c40802c40001d941d1086a24044841c000c1001c5001020800404e0081ca104c450442c0521705100120081100f1a00010707400c0004900301c5600210714070080701c01c034010324944944251001c48007246055114142007043d00d880c284040140c00f0450301d0f070310a105c010914140aa911428400d451a000302c240d4000d0f50101d0781801100076a06039521840ca00c0c601c40c0d410b104040c4e10440c51400d030303a0140c448094004000700920b6942c0c904000c0074020b1405d0464a0740114400265000c2c0aa40b82d24010300d070301c403841c07414040310ba5001e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 388430602 1250 388429352 388429381
    0x2409020a05060c072c101d07050f0c060405011a0904082a1525110f070305030d0e0303041a040206070c0b1911250504021b160509 57
    0x83d14807502840c42d022961070003069880c02c0c08803806030104c0c6074001c012503a80e080100907040100282c00501c0801040000055540c600c038140f000ca41d0326511150000d0303d20b8407402141362844880800c41c104003990208080b48254000c80c02481200c440d2030002d090420110681c0c0c0d0b01400e40400305020a1384c0c207029081c4240386107101c441ca4507006140c440c203014000f00f00b0700d03150b100f403045c6282c40c4011070101ea08500c0f81001100c1649424802150010024940b10100700024400c2d40c811202080701070300003007054003a15000e0ba164107080b5200d9111071144403c1c1800c080074903209010000450303100710b40100b88550100030621800d140d114018000782d07405181071045d000414004d075680d100920340f540308965500c005280701c0f81c0c01d4200e0244071040c05a040b980d01003d500108120741d10910713003050711185000d01007044180c5440e5400498001c1d202080c01070342c0120407001152101c04850031164985050282d10030085114003405401030280300202d40342d500880032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 388431852 1250 388430602 388430617
    0x406291804060f02070b01030c150509012f0c040b061615090b0109091b05013c020d140c0d0528050919030203070e0c162409020a0506 59
    0x40200741010b50f6003624040c0d1300716040640d0752200f00301c010410010096150070040c10b00649120b040b11a401000c3d0590284074113680c180000b143d400c42c100da804002041451505c60720703000040005a011556605102034030074000c0d450301202001d01c1c50054281e07420110070748140c80d072248055465180720032142d031440010980b24030102e40082c5052043c540030b02400305c2c00040220b5181801000c00040e035405c481c02907001c034000e01441c1da000700030301c41d44595401400c07600840180164111880c20305130011000164842c0500107a020640d100c0e16034841e919030070300213500031030307843e0314440c0c12800402c0c1c1d80308000c02e022341802400500002c16160034014110344c4d8084100281c40200b101090000b000010720000c2440d040300c445001d113542038003a241c3c0e0b6042d40c3c0400d58031042401402c12103008040090300850718901103801020344410061a510002d2400c188102c0300d00480c110281c200540307038007075103140c0c0c801d00c00c01c0c03600200311a207241e142405200190b400641c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 388433102 1250 388431852 388431863
    0x30301052404080a120801060305090a03140d0e06040308010812030a0f0e0f070e10030302030306150c0d05030f0c120402040c11010c17071b060e0c090406291804 71
    0x100018a020f41070040402c034500031005404003c600c104020891501600610141071a00d424051054000034421804550504003100d603c50007003060300440c003581d48941d221508010174400444004038a4501892103a2101169a40c0360220140c40b071a9443c01c0380b9840400384000f0360864026008400200d001070b2002850b41b4540c1c4c03002c1e09000b5003190380d241ba6403141c6c40401641c400c864045078051620f01000391451706555000b51644002380c0b00600c2128a480ca2148560f19181260444403d00040360711802111201900315001180d58902300c0c3c1c440340000e40038840c0501252402000c079446e5a0999a4139130802c801000580382240420442a0f01601c644009100d01c0382c494803580c9460b000450741d034100042c102001480c42e401c04c1045a0144901e00351500340c000003c0d40442d02040c901068813081d480e0104007103801d503215010a040c03000348685035100300320024964412845408517800c0201c0340e090820041038002501c503050b8041108481c00c03041e000b51055 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 388434352 1250 388433102 388433107
    0x114030f040f0c090e0c0a12081b061003030e010c030e01050703021e07050f06040506031909020a0b030f09060405120c1c0f080106020111040e07170c0301170303010524 74
    0x5443e0306880a545800c08000700783d541042ca00030360000c00418241490446104401ca4100128180491440380c402080c0944c0858600420040c1100041e458001402100e80c03614050040c0c1c0d10254241c841500441c504540f201007a5124034034070240b454240c0c6640d071280700da0354011039aa80c448881038045004d03000c026440c040301e689250600815150041c44068100303000c110b41c5005240c012881075008110401954407040c00f80c80c1c0c000207155170751010403032246804014080e80700b030003903102042000104004030440e015500540d107100c1c0740785c0c26540d0f40c034266980707000c2518060700d280d11203c014410355010030010f040700d81404007951001c042070883c686510a290489002250740e00c5e03035002841c1d612031700351401810365100a1188000c1902c81401510440c055400b520048400184c0c066024030541001c1e0002c07019003d007545420101d010007a002801032018100c4006000c4882500010a480c1611030052242070601030440c0750080c80300c2000803044407240700703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 388435602 1250 388434352 388434383
    0x13230a0b0316170312070509030a0503040f0e01270b0112050c0705010507180605090409150f0609020901140a020a08130305060f0103030c06051504110d0b0114030f04 73
    0xa1004692000301c2c6100c0c0380b07859041c400302407039000000842c100036a02c00d005041280c08020f000e280c01400d2401c00c01da40360000c03400300382000303100c40c0058024800005c000908556075001a006c4420a90300c0907466600d68480801c011400444072000c9032078210b1796140052980d0200704400030504000c00d0a40e00c165500d425903c04840361884254013042c00d02c2401001c1c0207041c0e1090701864661450000e0300c0e644180f8021030702503a003c000000c07501804030740716a07012000081c2c0140b01580c50743c1680030f4000241c038403641072140b92818400c0c0010080124000d451180e0816114031414840c501203102c025005200721a04511910b403542c4003042c0244010402c180002502059a60860038402d00d000d00103401499903030402c0004202207580002c1d45400b41c1d510070784c0802c0644404000d80384400301c1c0707018103500034540700b4000b0300980039000901244896000034031000100400540711990018940d070b0501c64100002200d002801d0b001980c840e204103e000000d252 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 388436852 1250 388435602 388435609
    0x323040906030506041401090203060115030207170d06090c020d05131706041e030903020103091b1203090e060d0219090906020406081305031803012913230a0b 70
    0x80c0d6401038034613801203801d00c03061200501d107550760a101c2000074400004644e01080e03981405109510440c074410f2108254184290112015503800650150031002c101281045e20340c48664001e08a1740381c2103002880d00c0e40c80c06501c0c101109a002f800b9084140441500c4942c4420324100c02d85502c0e003004500c5480c0101400084054640141240d282501d444540001e00d1140391a000d1040c402070b0700043da0044041060300d40c2031a0101d541c1602e80340026066080d00200c001c1da081d54180070031000848201a43d00b05d001e0355540c2e03125907031007210340b5000d9812369209410103141e800c240098280100ca107100954007140003100650f0343d092070412500300e01022a80e040d000201002100c0c4d2084441d074000c0040319010201164660743c29039280308800101d599801d000b00d00a072561384c01c0d40b01901030050801c0650743c4008403c0b02c80350109100300480e00c10740d44608510320342100c40c81122440100a80a9841c02440401d9200c40e00700041c9201090340e21900400390544 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 388438102 1250 388436852 388436861
    0xd0f0f0b0105090a02040f09090203013e0f07110105160303140a051608060109080a06140709180504020a0b070b0711010902011b020a0506211303230409 67
    0x1802903011000650410040254042000e4000603075240144818426480c502c03d05000b101c070348450000b4074580900c0401d02618020000030541802c2080b8180501c5000c9503640141c44032900d03801c500c2c1141600c08000f8000e0107060118200107001c120001401c280300380807070110504020342054401e0881448101e166881103000944500c140302c9c0d208051840c1641100040000b4005d5203403100441e500c11151030b034400704122524020443c1640503500200181458900f0b6402c070712b581c1d0600e03902501c1e03030745075072000c4c1c074265000541c4151051882c00282e0351480100742002090544900140001400c1a42d1080e0b9040700050704140400c000c004061180703008800398640703994040c0100301d03503001031034040c0d042911450041c3e82c4842401c154500203181040c03200c81500101b040b803a456000b46420950005030b040c1080c240d1038804459284500c0401e1042d91545110304000f000d05c500100405d00c2c000000562052081196280c04c100440c0d00e400d2030760301c03464041900c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 388439352 1250 388438102 388438133
    0x117030c030c0a1112030a141902010504050613030503130611030a0e010f020405061c0b03030309070e160f0e010c2301150b03190f1a2404050d0f 64
    0x80e0b2016443d002000b00e1401c00c1c10f064281190a200098509404e42d62a44165018401001031000b00c1040700252403080d192003a0030100e5510400d0940c1c0406030007020203842c1034502e40f00c0c1c0c200140415442e19610500c07140e241d40c609040d0b465186259443c000e00020031210180c41d1507030701c81c4410b543c1015603c5442d1004000ca859480039800c107084501c0208024881d500412042c080c5817181c401321107100c058020300628807201200140c008180d070602e5a41d050000205000c070818002501c07205030f0304680604880b40d00c403d4030865018105415940200704590131000c203c0b40500d003680d01c1220181403c0c17031781c010705076100315420b00d04084806410908600118050400344608282203081c0400125107605114004a4500005014140101c0c1c0703070640c3d000565141d01300000c0a061030300184164520281e80e285030300741c0480c0280c02040c90360702000d01d00300c01803406880c01704409041c503e09420f00c4184a000c0c2040c01040c7c5085070210030201c001090701141c0c100d03c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 388440602 1250 388439352 388439377
    0x120a02190f12020d02120d09060f15080105070f0804061409070f082a0a0e010f05010e010e09070f170a020d050105060a081f050907200a05060117030c03 67
    0x4409540c6040c011070b500074404001194002d1012100e41c0390009200c465500108458503160100041c01e5000340950a07401003965007043c1d082100340c3c2e015003180c00e20700316203d007d1010580b22050765003203e070100ca640780005c02c00d070001c00e140d0b03008110b075a4001e4024000400c444030008200e5088803400d40700081c0b194005901041290035416144010f08070060184c4075002607440191006042101c060800c3e044011002401e41d032414481ca0041c400307807622049070740c3d40b03600c1101480c0c0349208003404901c6d945030b810807541c4070701960083c10800400890940d02c030300ca800c550684076183e002c0d0030300040980803218154003400300c9114840041001d40c0d11060041d100040d104103034056030144c0e00a100c848006a000020b10350f02802403401c806e030310540c005030040302c829640c1c8060703003202c803510074051010303405140000d1010300040c450840c0c01490520980c0e80904620140c5103411000c0140086031096200c4103500181c10212030405403984007090450388140000d079003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 388441852 1250 388440602 388440623
    0x1c061d2a0f13140603070614030103060e0712140c01050301030b152716050406020304060503070210060b07021806030d050919061d010503040b070503041a07030b0a0e09120a0219 78
    0xc03a8034040124001400c0300f2300d0301210000030f4901101c0c00b0f02041c04000c04842c0c17a056100780c00502081000014610fa20304038a00381e189060030b400c1c100d105c5c0e0b210001806808100010795004108071380c101c1ea40000d40c4d920560350307241201001c52944009581c007180f400c1c0481e001401a8074150342c0181c1c000842a01814000c05543c6407000d058170001c24014180001c000a5802200303440c04c032100350070603e40e260b407070150403403c20014005c0280890714000f008548001c034480a04040fa1094401d000c59620100c0001c6008100704c90080d07242e44441190243c0502c1000034002001018144101e001854071100180710714507003040001505986c001c0172961102c2c020b0340d038861000e081c01b03032640c20241c031505440500240720304223000000021034204280000c980e8100b4882140e110740505107103c008020f00340e4180300703e00c51410404e020440a05110003035010741c0e840d03070080c44070030400611048940c22040c9500c0035405500341083d030703010780e0744281f440d0184100481d69 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 388443102 1250 388441852 388441861
    0x6020307090e131e060b03031b102013030b0103112b240c050a180f0501031104120305030103060e03181c061d2a0f1314 53
    0x41e180e0001003400680c00c1c48054850007041c00d50b00320000c0064501000104e1098078100035010304219180260107120020301c0310b00008032000004949150a016580c914901001d031006445031414150380d5582c0d041e0446ea0240c07080b100030701a40403202c0c144142c6a41d81e0b141c13000340c00c3c1c0991081e205c510070fa20382040203181ca00404508804005003000038280c504200404141c51280014010307001a1100082c0114400b01101e4800b440e110134000e80d104050f00038100d40184030000c002c40c3c540c004401c10039404400c51420b945500710026007036441d00c0c004501410081e502c2141c640401c000c0401e1200308803c6400c150347c000d80b2100c2e40ca52441c5000d10440c0c2446515044680061149910006440b00020140b0b001180c40c12105800803d1014111c1e2503843c1c000d064600c0c0c2842420304003035156140400382e03017100990f0a8598080c02280e10b03980d140400700d0f04605200380d024501c0c0703031000e15030118140141072098000d0140c000c0d10111195900c0d04c2c00e00500500c01c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 388444352 1250 388443102 388443119
    0x1031508060c0c011803050f09010c0602071407080c06120a2702010906052107051b070302090601230703051215040506030f0304090f02070c0b071a0106050702010e0d0602030709 78
    0xa6550040c2c1c1c88840007907101606c00074110302900c03001d1402c158001900f460036a221b8544650019009901150780314500d107030085a90a40e1000e04a80b0b01607020001611000807802c00d0101d0301c0505124605110301c000c981d245803000b448180320340d584680700e20001148200e40014108a83c220010006580c000900031821903401182041400c120000a8540548080c99100000401a841354540e2801036400c1c1c000c20120700070070030361241800c0d01100000740d52000c4034020341d1011615120f0000441c0c2116101c1c0003540e0300010703d5004404880301c0c40042c05064001d2500c40d0402c00c00100d0300d80d2400c003e8440340b0b9010003150310026603281501c11160080d82c201d004000c0d520700300c01440c2d183c0c02540302d280c080d140d0340c010440d42036a143d0102c0799040d6010000c0082c481c0c8a0b01c201d4401c1d0801c4030240d6407c607010380d450428006c0ba1040030f06a6400e9121b035030400460f58011100c1c00a560880340d0014441d8000d8400200180061401258180c0f60340c1c00c45424505070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 388445602 1250 388444352 388444361
    0x20d0212030601140702040b060d020702040605030a0804230a06030b040f0c08060609041e02041802070b010e1306320f040201320721020c01031508060c0c01 69
    0x80d60940c842002401900d0b0b0b04800108400726400d107030a83c0b0b4900e10300001c6c004050310158035400080c0020b4000d4174480d107038014000c0501c215400c11035281c5941c1416a996001c281c0280064004c000c144030b915000780300e01010280036400030007541004c0d400700e20507240700ea00620109403250001210380c50036002e1103100c400303e801c042180400040000b8882980909101d00640002490100b00d4445801c040d0482d8214074501d6480e445800a0400960141c890b08001c040421141d103060106070080b100b0f165003003442d49d07000ba424600b28011100000d0000d00c0106409640c500009841e405842890b030004890404000d14003401400d04024604500b1106c0d00cad0b200400450000b9492041e81050702880c0600004580c0a103442c4c400951303115842c00007079000648050030011200038825184181d42c01400d0001600c04108100e1f820703044000544c01c0440c01ca44154402d602064080c05002d000002c041d0392a0095810460300740c0d001c4e0002d02e00003034031119100d0240217 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 388446852 1250 388445602 388445623
    0x31a0a0c0e0a090b0307030203030c060a1503050606040b132c0f1002160206030406091110020303070c020a1d06090f0105060d0c050d0c1805060c15090a050706020d02 73
    0xd001061140034400101e01c08240e0241c0c0c8182036680380710902c03940b17040000c2c1d001b8503030280449590f6070780520416941e013001c580d440f0800341003082c540300c0410001666012242e00a00822075500c038407003000080c2c09450b81450700502100701a04201515020304480400d651140107401120f1103600b01e40502482c0c800043c90780301c0e080300d45030b00100180d0580e9448d206030005032149402441c1c94000748000b113010f54003180200520080c008540c0c4843d0400d40310344900054a030340c0754240306d201341c1006994005a042407000448050007500b031b100000b0710041039018000d4480a4054000181e65059042082114200601c0b4140010010780003c8543c00300505e940c9490002a410b1290b0b20140c414076443d0100315580a006a042c0c0b038815030310410500101c4000c5500400340b40e13002000e03004040180c030b00015141051700031105074410503005801c0e140d103c07600b01c5c102450040d00c148010320a0080507000b0410621415002c0d20aa0340600503d001d405002851704c0030124 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 388448102 1250 388446852 388446857
    0x30f06010815010c0f050f031210030b0f04060b10020a021302090d0807030504030b01090e160302060d0e0705091e090615010c05010b1905010f0206150d0c031a0a0c 72
    0x106000340828000b03070401d0812001d10740b00c04020030518050b5800c030305a040007000d5100301d22021020643c04005007101003000384950b6000c0d5180301f40d903039107152a0703c00030b444e218001d0003040610480c107800030351182c002c102c04540306d111031002c6504c120400550b1340050304504119001c51134000b0303504402e099503040a509100f400000580e90441039400105151f2000405074101030051059071b00458202503150380035039660103002c0c007400354242c041d070305070040785440307103400000700f090740d0a40c0d4000c3d0056081c80342d0701c4040c03030052200d00c10001451042e5940050036540707108401e03208001c0083d0070145120700309107840d0f065201070050002c50300850108510101c502011103210402460400d11500d594105070340145600809581c110548607040c8448031140c1560a08030364082c0e076101c80341240b41e0f0f0100d0f110041602c00720542e50721030f040150303185022011919058024100718612969990b01c11b0304c1e000c1002184490340c100d4104000e0824128400c0e00014003050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 388449352 1250 388448102 388448117
    0x1e06051005120f093408031201060e03010204091107020f030a0803060103020901050c06040b0103050d0f0e0f03120318060604020903030d2403030512070c030c0b0603010f05010b030f0601 82
    0x520142244440041100b11108030a20000380c1c4e5050030801050140b4a01c520901d0120300c40d240c800d08103110740c00f04a5686110b0307900150b504400000c46400c600700b10b5551945074240700b4101e40c05140f0700b02d810341c550340901000c00e8501451041952050400c224543c1c0c440640c814000c2c0d803400c18014a200350880d0b086d05010501c40d00c105d95206000346401a5120f20f01c03001aa0103010300c02c1c50005038422081080b08000760601424141c4e0b0141c41150302c1204203201c1116040c510700e024400040d0041102040350900010b001000080101a591144501d2805a485820840d52242940307521004007005080511810740c2101e03065400b9840c5c106a03402082c0d5900c6000d45140032603035102c03980741e00407941c48000f4210400b0015200091562410000e109812004101440404910100b10709078003442d41d03030103080e6042c2c135034800b405040c0d10307003490a00d0002c050396015526001000c089002c988100b5000e00028014a522030400e05a580311200b002040c080c10b10048 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 388450602 1250 388449352 388449367
    0x1b0c100c020706050403030e0a090f0e01140702152e1403070e010b0c150916090b0306010e10080d0c03020c01080714090f03100501050306090a02150d1e06051005 71
    0x400100c07002d99800d81000c44002380e4203800320b0000c1c1d15641c0003013522403070300d080d00680c0301954004141d2210500700034403080200c0000e107181207800380d83e602c0c096030101c01c00c203958144481c52a40d001c0d8000320000d0114080d0b214440651400c035500b100c40c10354442043c0041107003a5403004190406400424a4a051000043c07803200d0600642c101c990011608040701034080003168900a40d460f4054940c2c00c140c0b118560720400e00e04c2c101d203011521100400d802c0103034864103000c2800200185100c0c4d01e4500059041c5602600076a0130b03540100020039404c03003c001089003136109550f40a806101428001d0501040b03200d0306040125020501603101e50201c0a9081c1d900c940140b00d950f18610000107030036800d10203225402d4018814100030b0070940d54051b5048907802d406582c55513641d100026158203e0f00002544113109410984118502c1d50282464100c46000095104009900c082d24600150b01910301c13075440b107009105a007031150b407000c407150043c02c2540c0ad2100b0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 388451852 1250 388450602 388450607
    0xa1e08040e04060906060902131703090103020703052b1a103009020414280b120a0303062313020f040e0406050106050906121b0c100c020706 62
    0x24610507440312101120102e010300c85150f100c2d40b4810b034414400c0040302c2c3d07640c40c0780020b5040303140c0c0b8000920072040009400f0480c913001c00c141c08100da01a510300320303200f00198029004403009804000d0180b010b0721a8504111101001003074080740c200f1142c21800d0240140c0f102d138001c920f48811540c0001009407541d8a04103048a07150400c41c16a81e1002c00c5107843c0140311240702d000c2c082c030400e55001c0c240341d5400030300042d00a45040c0032100c440c62085000300070594110140d0000400303000c0381d02e5002c5561903001c3d0f402c0103000c503401a10f24002008208200c40c510015000845c0c00810141c0521904008200752509000703044103180c1c06000d0407100110050049a43c0400e102c48070702030782e04460000345141240e60300d07213480344800b854543d022a8116003161401c0008150343e4090070685005400040c90149000d202c0c81581c0b04000000c1c00b0380304401840b003d91047c0700300172005040982c1401c170041c4031214142e101642035809050012003590009101805101d9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 388453102 1250 388451852 388451857
    0xb0a06020a15150b21040201020d0302180603040b06030106090510050d0c08011509050915060f011e03090203150103081e071718010314061c080a020a1e08 68
    0x2e801c10400c2055018040e004405000070118000705000384400224041034070074041c280c800c030f0542d24800e100b103e00d81c1909040c0310603a80039015a1010421744140d600c42c0e001098002c481c520843c20115201c0046500764009540490302d8800c02c9003000011b003000d1041400422446800380102d007440007051401081c0d0f801204d0192907c0340d501020305c24100945401001030303400803c9540c0d0201d203100c110164030301454800034206030109001c48400191040c0c00000c002e02c520040c1c44070400c00c210324411051603418022054001c280c0b807a001018000500519180890880c0350340c81014149110000480300c1555400c0c01400030519800035030320081284500b4880c00381d8070000e03803120b900501c00010001031a40008040c0200d43c0400341c80740c10b040840c8080312490030030054003540c1044046074410031800b00000d41c107207080c800b400362029042400e0080c0074515120041c90354003801c0380c0c4002d0ba1000d41c80208102a088900744000e0f80d108402c41004420b40d0f0f21902071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 388454352 1250 388453102 388453123
    0x1030b07051b06010b0a090b0f0f160b0a050a200703030e1e0304173f0c030406020d2105040212030d0b04050604180b0c0705030a0809010b0a0602 64
    0x80450920320b51011a500c40300721907040c030102c4031150b039240e201120b994408155180011489040040e400003140180d40f80d030203e42d03400750b041c00d22100c21560643c0003508521041b0031080c02c041d0100e410b1b04d00e013a000e442a26404119464400d03446d01c140c1e010a642100005600403522034100520000d8400c00e55040c80c02084003e004401c0038502405c0c030f14401c9100c003e00200a2140400100500c1280ca8280b9003100f0412510441c0b91039aa0300030040680044a4007900c4011008a900d0950303441c83c1080801030010800d03440c4119040328802c3e161580c000981800394035010070854002c82c401740380811171810040c083310038011103200e0242e04070341c44401150840d90f450355801480c0e81c107441100c2d1a4a030040d80040603004c0128454040c92070b04001c182035042500400c490403000a5980050511303d558610481000134456004d440301405420001102030005042542055450040604007003042d542152122700e80584506007020f0200109a008214034200303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 388455602 1250 388454352 388454357
    0x402090901020c031219060b16060608030a020703051b1e04020d0c050d050f0907030813030c03080c06061c150905010606020a030e04020414060c010e010507050a1701030b07 76
    0x251112003009000e8010341c07101c42060302010840031107502d0041600c0b0f1080e00502e5904483c84101c200c4031040b200907014094001e501082100000404481040b5000d41f04100000b00035555068082c01c5400039001c200050300074140800600204100039500860640195040003603030070001160843c8080c0040b51a5008858504940d40c0e00d605640e02003140100c00d110401065078020076542c0100c01e0841c65a00c5c00d0301051500c06282113007881483e14a00030b0040d1421a1220403544d00030b5242802110011007002c000140c040d22541c2c01035100d00c42c0e2640710a03054091070f040c0f2000402c0903001d550001c4200c4005000103460070402ca810041c1c110503045001c41980181862407000340880d8201400040e14a0703000a02000c094020390350700704800d400008100580c0b21b98401c40c10404c100011010310b5142030401045c1032150340700001110701c0b0312000c203070a40301c08441c1600443c1010170502e072f2158200200446420700c040307418001d50b065546190305c50001030004400c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 388456852 1250 388455602 388455619
    0x510120303060e0a0f0510050f04020702040e0a0b091c09050909030921150c040504150f0b0405010807051222020405040c03060c0c030f140714060421080402 69
    0x3414041e80c490806018840031802c241d00d0f140358038002401d180c030a2404080c0c9020300152a00341a04020004c0c1e03500100031007454620001040301a400007d4240d80c409d90344d0344039140c03542c010000004070328441c2d81001c0051901e050003600786a00d520009120300e42c8801e02109c041d900c440d00d4002c0d500c00b21356280e120f813107510750780b4a14004c00301c3c119000504c070f0300745001034401c0361450101d40f41c90800326290100d146000c1d8404a90a44a0103001003084c0800e112a25081d0420242110380c04c82c1c1d015019510300005007400c10690011740f01c1c01d0300040622003542e025200e9540036401b81040c80ca0001c01c0441100703a50300040c00c5010a04914072900607009000c0840d42040307400400c2801103003000e05080400c01090321080300e0251819861480c0076000352011101c1c00c0d003588420a0a0850f90750564280b003071005240c140ca030007004032800103142d400d020503105c40c04800905842c5082d00e0820f02d2248400c000440070156100c0790207545034007014a50340903505540c0c010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 388458102 1250 388456852 388456889
    0xa06080708061012150305070506120a020306060c0a0c090b06030408190905040c08150906030d0e01050d020703110705090c16020315010305160f0f09020a0917070807090510 76
    0x1a010840d07151310744103840c140440b41403020400202c01003501c1c096000d4542d03040d900c0c01000098030800c0e881192a090800c00500c1d92580ca0b40610303408400a00058680320680c0d4401741000765181c412580d9a000e902c0034840700300c01e0301c10740106c0038003600c050b4907509113070703c912400c1d00811004014101c0c4c00d2007102032451164030b44500800c8050024070091038000005020b5180c111104a508250031000c4807c03450240c80d424042c02000d1b0152015008082085074440a003a40c8141442410030050300105114130081c00100d00a80c0c5550b0400c0c80401c00906150241d0b10081c4550441024001c1610070758088a032071070602e03210000380031010301c0440c0c04d11480310030340359503205800000420b100f40030405041800f01c524600c00c1c40350300c0d501c00c4d03200070034103000f00150420b030243e0501040045a00500380b031040c50a108407060750361112014155541ca044402c0f5810001c0100700b810720800c2000b0142c0701c03001d400d00c85864011011418100d07503100b6031000d0101d00f01901c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 388459352 1250 388458102 388458107
    0x1e0c0c0901180504020a15030608011a100f03180b07020c1219020a08011104050a0f0b0a080a0b040509070602100219080601110106061d060307021b040f0603110a060807080610 77
    0x1b0018020815180103041502c1c40141c000c00c1a80700c1d160b410f5080103131120f50807022100315450b51034000c02804500c03c148000b02d5601c443d0b848442d042c980e40d03a0305408500e55001460042c82d106255440b014540420002d0408459a12075400341050620040d14a20041580b04200c1300c90302c8042c140c8041c1d400000c3c020b480d140d000d40681c0d4a03040d00c074840c1143c000010415250251a07880880307540d02094003044450b4810041040014414460f44034442ca150075040200e040b03000c0f4014103280001030031a0b0083da1552600c0d40b00600821507140c060042d01d00e03000c9403c408506007804d20b040442c0440000c254a400c00001e8400144240c1c060018040c40c10306c2c450007003000c0c0b9200d45018001d52800540c503d02d1214007242d46216141070001c41780705118036409001c00300e0b00041041c401c0005101126407087e101d40341280c1100d401d20070031004500400c071042d4a200c0340c42c244000204160448010003210008001040381c0083c2600e410120990364002c5000035801d04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 388460602 1250 388459352 388459369
    0xf09050f0406020d0902060c011a0102030f0d02090f1003050709060c11090a020f0d0501140a03150509100f02071406010f0317070609050604021306060903020d05031e0c0c090118050402 81
    0x294840c001048c40c140c0050150b00041e41540f145008070100c0d00c11000680c0c0d2405000800084110200f0012203241002d801406d046040644002c9a505250001411040c056400c94002a5542040100035540848144001c0c190303801c1100103050a9103d4641c80032880f85824050420a000b00e0001d000e40d50444034a0101d4001c02a111184941e460b0080d28081c4105640c003a11217520304c0d0700d1f1800386210b004680c1d00c0002080c0284406c0c00050103010014400c449500a0024000c0309000d14000e1400f02d0303040c03410050f507414007482c06110024801079626100e41c401c01c014000b011010701200c09a980114000b0400340407202d1141d000d2144810060400e070801d904038042000010380540220301c00c0303404000c5221140c66038021a2541d11451001900030780c010405402c00c107128901d034a0150003541c2c030300034030701104022880c101d4072440b804d03580005212100050034480e0745000b51342224008100d5141c201d001e9402661484010342d000e960b60041011581d48422 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 388461852 1250 388460602 388460621
    0x14071103041202060403061407030b150910020a0203030a050a030f020c190602040306140402091302090c090a030c080708070b0309100e0f0607110c0316030b101a040f09050f0406020d 80
    0x1c00c3c00106248c0859039200d00058401402190606a000c4103501d0014100c0e480c3c3e800101c0c000e0301f09880c01041001030144000d1050941c0550201000542c806100404501e4083d4980d1540c9a5a40e00b00404030740047c280c5a148074414070039203029420202c4e0b40da4000b0441001300303000000e40e0034094000d204550000304010718013403501060300543c880b85031141d40211200d81340e030798401c05400001186098003c2d0300c40840d0001590f003840d58800340000750009880c001034151130782e54122148103950045140c0368000c11007004240c00411543e809070010035011401e6083c40c2d507002d55101115000c1254060f154140000090800c020300159141e42904455890601120281102070340429010b00e501035440070f0b030910700700010100000382c80390b82541d0030603181d9180c01c003942c90013424011103000716400024428101400703a03040d0200c0500d00c1d135030740d92500c010761542407030703e5201d660700600340b60420210303e5486c4455503010b42c01c443e01503900c41258844200034900d052 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 388463102 1250 388461852 388461863
    0x5030a111c02060f1f0302011209020616050c0604030c180e0102070b06010e0a0806130c050a0b0c011a031e21030a06060e0306150a0b03090114071103041202060403 72
    0x70741002180d07500180c0f890141c241c2040f24000c40d1070b1a0003562800b0b0948055800404034940200b0042d4850038005454041080c000070301c085440e4000f503240d034400300783c4200d148050603035a801d1000501410b8001c0380c0c12140245410720390f94524801c4140751060b12406140f40c070708903040c0c402c680c001c82442c80d1054002c55035030721a490507002c3c64500350741103030020304107028016460801d90001000d441c9100000e089da03a5030f0a1141104481c1ca0108a506440007880050107455a0316002d001d0948141a1901c5130001c1908074215260055041e07014808003c54140d15100460100d0b070162040300108030300041c1007211450240d46a03980c4150a4003258014a28001c400156009030005c800c1841004c2c0d07227807001c6840003404907036164160072180c0401c503035010302103080f21104401380080791095518001600d2507001100c2d9050241d441c0d6440c0d0902000107c0100d91282042c1481d20010899800c0c8598a0085001d80d2030b40340c92400091055685036401c2d41e00669115 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 388464352 1250 388463102 388463143
    0x907030b18060c040609030f08090603090a17090d110d0503031513090201020c130b0301021602040e06010303020715110a0f14030301030b060f01031b02030306010e01080405030a11 79
    0xa116140314201030707a05501d0700444002c503000040010849044072520350f1400005425a202c5400c10101818100c1d01c01d441000b17540104d03211a00594440c0e9100d0001d0300e41e0340303214180311003000f40d038840c4642000d03000c22407280c0c0d035501c8200d0442500d401c030000000c50740841d4046007030714142d10320203803040c480401040702010700007030462203a000076120102c42c104941c803910705955031000000c1c0540c00c10355901e546800c0c01103618046a01861010801003020742c042400c9900405814840d203a58115040550801e8018551501724001c0103102561468400a40302e40c000d00804140c140c0d40c1a03a58000c1d44580718410590308190103444c3c42c1401881c090030301c4007205d40c00b1030f11249101140f140d10070012007968122030300601200d001d03a54100030884416855070701c05040c5999801058076110786080c4070844d24655400844c5e0340c0c00c0410014111a00c400880d904120030034040200054001c01503601324080da0030f0460071040034007400c80c100040c0840c41c0c00443c1d0070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 388465602 1250 388464352 388464361
    0x30a12031d0c010e03030c0c06031b04030f02120d0212030924011a0c0316060e01020d0f060803180d03030b03030c0703030305070305043302180906030c13050907030b 73
    0x4200704001442c00d03219684100301d50401c2c581c490041c03170004041d0303411403642e040741400c0000045621240e000c113008804072440c480150684c100d81c005a404102400c00c50302181404880d558410301610010251080940c41c003e41c0c40399810000c018414000c008241e851008000800d00082c410f1480c4000071140300308650219030910849a03010b405000d4680e00008000450300800c5162019600e01005001200f0b81050590800c503002a61298505104803003840a46814095280302003400380280444034281c0e001c0b604511419041000a104c96150091045c01c1c6500181c1d500c8954100d0741c05c069000f07156450075250035020004450381c081744c0100d400300a8912a840800891300c0d40c00c011000c40303808036070080250446c450030041d110f00400081207851045079800c1c407501c1641b200c002c1031360414105940701d842ca802c0c040c02d45152400200380d01a4050b40141010307840100040c4da12020841b0400c0c90b540d03a03201203101c9241c18016540a19080850110b05041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 388466852 1250 388465602 388465661
    0x302030304060507030603120e06120f04050c01020309030a02040b040b04050403050a020d0e0904081c0f02090a050306060901030210120207030507051c09090b012606010207060e030a1203 82
    0x845049035a640b9120001c4d1006000c2e229140c1034a801411881143c07003d00b0003920612441d13165513034040001d00c04032000d04e0394416003921071750390005410018146483c0a910b403002104560381950014440e08240c0d03180041c0141590781c044401140c100281c0001c640188000c42040e50041d0400d0208014181c0280c02064004c20f1075084400210080e10211103e03000010495400110400810301180c01c69000e45220611b0401550341d080ca00204102290302901c40740c2101c640100340c107001403416106803001400300350f000d0b1240b46008400078030003c0050000a201c2c103142400030100f940b10b0002158080c001920465554900c0d05000d00f49400c1140d048030603115161200c0b810050a016011404000e03454003144c1c1824034444402401401e83c080c1c0c10000f001183c0c0c0c0c03c00c84001091090b04080040e114914140381c00024240000c0d6041041440780c0c0220407140c80e2000200360700c1454010002004002e01088210041d040e11001d00d4000340c824241c15070040c0303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 388468102 1250 388466852 388466857
    0x7060906020406080c04080a0b04050c280f121415040309030221060c25200102031e07030e1f0801151e0212040303020304050109051c03140f0403030203 67
    0x3412920b0b44c10080e0380da50311a8406100d540140d02a603009900c07400d0000f016031f034042d85c00502c9441500c076440c0400c804226800130242011015900b804540040388800d508000003078001c2c940d003424250b082800c1802c0c1c060701c0e2900140760110982d1000542c0c0c10500030010100e1000704441424100380c01c2c01003007620640826485082101e035015000780c0e4620080c80304c00340543c0505140e40d920021111301d50403a013034084a0b0306540000700d030405c800c0d12030100e03468816000a0424442034a80d62408880c0c0510a415035004000c64482042c0c20645081c8041c0c400c00300e82d640d07500c01d1408841c48101081550341100c0f40c2d800d002c5500783c1e400d08544c0a070b10725644190545c1e0381c440c1d06500f06040640454042120b00d518122030020b078031418400440b0f02e0040b243c1d800a02c04500304207500560054005800204041c40b40b580c4c048181c4005240403122294190300d01800502540c82e42c040083c05e01620050141104a150041d40d48200c505240140c4496407403c002e900c03903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 388469352 1250 388468102 388468109
    0x51204090605150322110303070302060a0b03070b030a09171602040c0f091206020702030a03080417030f07030e0f12090406120b0c0d0e1c1e23070609060204 69
    0x2950840000320700f00361101c059900c9003808003061400070754190f085920b00e00d51104107690b5441101e2a80d1440e84007000144030043c0300c1c3d0300502e5145490001c090480d40240c1c2058804e800c107100c100301001956058030380284200d400029009824030b4588100071880e01c00caa81c03c4000709288a10380b40c00820030b000d0500030b0f6018402d02615090031500c458080c918100030590100082c40060568021003098038802d0328018a00012500042d00d881d03d020000c81c0095640c03800c00041250a0070410b60303100b04c001c200c0b03042d8100890060189400180620304260303480b11070450054041054803402071240c81a01c0841d84c240c600464180d02510100d4001e03400c010b000109030410481a001c61604250080720390f4552480c081031942c840c1d5030b48505a42c46142c910741d9160203000d0440322090f401c2c4441c2c0c2c0700c4841c90014000312480100354151400c40800c10309140d400544211400f5503480c03081c03134040c000ad240507500c0d0256690240c62117140004c03807801c01c03e081e40100183c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 388470602 1250 388469352 388469359
    0x15030a0c090e010b0a15030605131d0708120a0c0210050309010b1207030b130803150405130506010306050c0706020c25030f1101051c06090c050705060f04051204090605 74
    0xd6803800b000c10742c26a00340310304582d08501c1e030203010404200b103980644e040d008546004140580e031a00041e410150b01001da11000d030f0b54001400ca2403200c0c88000380d0780200c0101a01e01103180001050b12412911b90862191030b000820f40704040c80b5070f4400342032a03402025040391100340c0d14000c1c1150811140c1083d42d610300400d580741072070074075440b1903400e00baa40100045415603940b60010440a4039000000c0d4000d6100d2000502d90406948103000d4981214842012441000300741c5034064078032040c000c3c802c2040808a4408100e41e0b0640b500001e010440791580115000e0521603600040c01440c4042003542003408041042c6081c00b5200054146c0d03070120540c0840003030307038900c40201541c054016500c0008c1c0c104051040d00d01050400e181408590403007210060304628040f04126034425040c041545684920700f21032840c6d00d1300d2420f11100350b54680e554603025213041c103610344032000501001001c02c4014183e43c07414a51079221940e82460380c0180041d40a90387c030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 388471852 1250 388470602 388470611
    0xe010308090f1201090c1208042907051005010f0335070302010204030506010503060f01060f09150f08151302071104021315020a0305120901060e0705070209060a030302120315030a0c09 81
    0x4a07d014100d04030031158101c10380c180340600c0c290a681000254001c000e04036400306408113040041d9101400c80f03d400740016201e002c400c401e4080444070160403524084014440c14070204180320084500c50440005640114001c0000f131011100d000920309018980052290101681074003c0c00403a44110304a0308203903291820140c6440c41201d020080d52401d0004109940c0715401004402078981800c884560f212130028a20146220f43d00740400e201c10600c4881c035910026050744003210f4042451001603000024002c1d0002114944400703401241240500c52544000c18400ca0020001c650f17801107180e4a00005045115012484885901520f00707540080740c5179100135410398806c2e15042503210403040c1c40c0805031042c1c815640e2650b000c02e1400504914174050a80c90329017513245c04c410720401ca0000001000280952100581000040d40004c0e0801400781071805484d1640c3d42c00003090350b41040789510990602c1150340890500ca2004501406d42c3c3c100d080512 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 388473102 1250 388471852 388471859
    0xa05041a03010312050a0905030307030906022122050901080f0609030309061b070209040c0f08011a091e04080a0e030c010f110a05011b0e0306010e010308090f1201090c 74
    0x103541d00007480003900c02a100c42c0581c3d12144140d00500c6403002d20305041c1c4100c0d44034004203145400c4030b034048002c9203041cbc40078450759404001400c92803041d668140004c40301c840c00070b4418043c0e8940800c08081d0f10b15a240382c01044507140d806004090f000d440250b03581e10701240c0d00c24a80344140c43c58040c410102d40302400c044110fa00c100c0c5000000c207060340b00d041d1400d107020840260220208000c3c030041c40140d580c0c2c950140540c5c0141c0360200c03c282412401e85075821075920820a40e8074110000c3c01e0b0000000340705103614002c0307a00451943e900f100c0c9242c216007040010010703588010030442045134010103403507101402d68400040000d01024155108000a0030324085180d0720385c0c20708860b209074072018222030003c0c1540e04002555031494255403410b00c4460001010590400c0065400200020044c0d412002404a94500320640790f260206000240c00241c0000f02101241ca501004403100d00c0098184901842406010380c001c2c6103201d0b08032040f07807000380c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 388474352 1250 388473102 388473149
    0x50702070b1603091d06150c0d08010501021c0c060f090503070303150e091c200c10171503070f03060f0b0a151107030c0b07050607021203011e0306020a0504 69
    0x13011401c00e105c5005080e4940e0020008003064a03804580325110401c902c1c81200710902c00321041000a441e2104654103240029003410178001c91098100d4040160aa01c0c641c0986550102a0070034000180b4641c040d00f01c130042c1c2a501c001030304600c0006000b00c1050b80c5a805001c81547e481100c6646a4482d8050400076a041d511844079900440c807800c003c046103200c11461349441d0502001401d5031803058041c044500024429540110f0410036a50a02d010300310201b00395454003941e19004c03441c406614420140104005c01c0301c002020403661010480311010704407049a8800b0181c2e01e14010001c6c183d0120b0706a24a81006020149401c1442841741907521840d5031210350380c0d12070780072078107580c8c4100c50301d256100707442002022400d0b50750140080d03c1c02801d120390344c034030f175003011032400401800079811913020104a44800d47c04605807815250100401c0d8164201c0c3c640b008000c404c20340010b031840c1d00c0080c000002e681c114004204680703840e200c0b6241c04102101c0c0c0f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 388475602 1250 388474352 388474379
    0x3010605060702100c0b0c130e090d14210a0b01301404081218121605100e010e0a0203030a050906070606120605060919050702070b160309 61
    0x24680c001c007050021000515116a41c04041601d9151900c91a51031380c41c1e803861000c00f41d4585c0b84084001649041d449902042513004e401d01c852040000d081c42c807003042e0f03114414000c40d4108980f0401c00920a0b80030b0041310451242c2a48110508907140e440040b081015103001c00d17003904d0100d850600d540a0344100d9030403c01520445468001846c100f00e150030b0204a1000c26980c8400100c9203281c0c01000f54001c500510341c080d1110b20321003141342802805024842000340600e40100c1d1101c00040030314041b24000807840c1c440940103039094140c00c01000c000c0250146942e59004c551031035001c4036110301d8040081c0104036401c0d80007900e4507024100030f9055002000f064440074041d030020410000090010740c604100c603102c1d20b0446840d50080361000c0c9180301100c060000700c0c0690f0b80c00c04400c4a041c0d11074204525002c010020462142c1441d5849100061200e402405214010804201c01a6503083d03485000c01d02d84901a6084000c2804a01c02040500e4400c10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 388476852 1250 388475602 388475609
    0x150703050105100e0d06050a092306011a0f1812010e0d03090b16090f030503030406150e040615080a0b0117060118020c010f09032309060d050402040905030301080d0905030106 77
    0x81700800c000325032a00740c050200101000c40b0b0f50b1302c40a000d800103400d00f0601d000e800d83e10003582c8111407202c0c8258106541a8440b0442e907801c81201c0d0070400000d011503c0501200c01013030764400d4401c118011120101d000e103035000e0381020b840c984521064000307420540d214000e4034810031039048150304640103018058031030780104001031755140d18603c0c6881d20201e94180300000503a90125040b820085400844441d0008000c0c0010807009000c0e0f5200000c10380d052200c0b80703044c0100030420640c000d00203010350345c4541c0717000d03011103003c4801e002414000d010786900400e01d04102003400700a1248003c4c00318007048444c00d41e640440c91505890556401c802c62620703922138076003c1e4000300f204003925540d45c0c00d624a0103596206a450303c5100c0c0d140c0c0106042d844c18034603c1c0c003141c0b040080305139104000e080001d507140811540b0354030924034006030700d80752800850700401070300c08010001e00c0008000324235000c0001c1c004076000041c0d620300742c440da1500709143c02e0b41c540741b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 388478102 1250 388476852 388476859
    0x4032a031d0301091506150804022101051008100c0c0f030302040b040e07020c040e0c1c0b0a02070b1501083909030c180a0e150703050105100e 63
    0x4828400091049402005004141000c20504481080001c0c211614a01c00b214503904951102200403c140036078001001296a070b07507903a0320002d6000d0f01105e40103200038491400100c49028040700a800e414440030004020081e51412078040450703503c2c50f000c0c41c0c501d03101c1c401d003544104280340520701c0d4000d200e0f580c1e107002400d81d944082c02c9000070b94040f01815000d00c00401d6203194800503100500410818142e20b04003104081d092141813082140500c0c1000c000250102e00010301106401040c7c5404418000c0d020742c86040040203400100f90400800c10301c010158282c0251408a0007003502202e40e4503030400005100c0101033f58203002c900d0400006500403000320380340c00324601d0504c2c0319104003180303105051400d81ca42030380d00d00c60101103050100b40c1001c000c20141201c041e0b80c020500f03801038140241e0a10001e201c0c5049139155020b2070070343c000501888014500401050321581010b40c00500544400d006242c02a503880c004041d2180c86010345040c07d29029 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 388479352 1250 388478102 388478177
    0x1021218060708120901090b0a050403020606130243050604120e04050708160509030a020f0105041206060e0c040506070f03090503030705060f010e070225090908030403 74
    0x14850700b070300401800e56807040140b03c0250302d850038803407181c80781490350000180d01100c0e103411303100d100780035040c0701009161100304000643c0010300b554101404503403440400301182d102d08060f2003807003090729000100c02078040450842032540300300d110300d00d103032280000007543c030340d030794180b808040a003080c1d011002040214204e05a00b21311081189092114445610003240a8a4040e03030800002110a000c1286049000140303201e090704502c3d1961a20718024002583d400c05c0c4c0e14044e100e100b4020300c0e078003a42c0c05001290002c0c00500c2c0340b90b800d42d134542400700091145108085c2203000d0b010000d000b105201040700d064400051000382000c4103038a4241c10040f03516001c80034001034900124246c0d50400c00b811044d446400280b0a6140600151032610011b0b44001c40030072864003442455500414960740300d1622107881c0a84060071202c0c04581c50055200700c0074186080007120520104c3d030000c0d807046020380c40740450421280d0300365a2030341c00c50984c1505003004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 388480602 1250 388479352 388479397
    0x90e060a050a020d02030112020112231905070203030916030c060305040507030203030d0e100b0603011205070f180b0102060105220e03121b0405100f03090f0503030105010212 77
    0x1141e114640102c030801c0010300305640803411004903031003a08060a0039440c43c07102800c40d07911407004c6850348813145080c0580004100801c04202e4000342c85503401001c0c50001c1c81c0c804d00c00d08082e426524011040c001801c188030701079241c0c2e00903195846603004070082d48400450040455081701c1e8840d0042c032160340341110480050070054000c640e40c1c0038030f803000000360307400700060140d410816000244810f45e00785094a8414113411900c2132074145110f1342c0b0503603103200c19241118205000003043d880d4034075003503060050039040811032440c44000405c6042c04004041c0400d400303a84104606200c100c016651a00248501540042d10b181d808803864400224074003140d104140215010134407070b0f0101d0460700301a190000b00300d080010400e01c1c220b0182c0c0d10f4140d00c084428140f03031606010202e1110300661007030a040c8107401103030070440c0d44a6403250264941140c00e02003403e40920f821616a8000e1048034010b118100000091040d4101142c078014109001280740350354 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 388481852 1250 388480602 388480621
    0x3040305030703020306060705151012020a030209040c1a0301090e1617030c0a0807020a0506041a07030c12030c08010902040807030204090809090a05060102012009042f0310090e06 79
    0x14400d80d0030242c144032070000140b08200c903007040f00c0b681c070300d000440c83e20022f0150844016484030008039410080c081c056101e00c4407e006a0340c0581e2031341507035a918100200381c4801540101c0001c40c0b00700389062000b88000107181a211914001e00c0903440360b80040d03548844800a410600f01005010080702528082c1c000b46a91142d050780e00f00b103134000346a07003030840b2102c0590300d1941c0010301c00214a4010103038000b9140803141c0754185820010b00003507032141904560800c2400080a03802d0600440c802110035501c241141d08123026240002c000d080385074403030400705074407100106010302c0034001d9405503101140100031203032035034081001a0441510956010a0401484a641e1a00f10400c1e01c074110441c00403801c1d0400f003000a0855103100a21403001c84042e07503a00d484c1d0085070440300c003624119408100744a03a55107040750808240b180d588800540c4840b4030064008034044d510906c4403483c5840c06540d903880f07803010745811500000c6640c00c2003000888694 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 388483102 1250 388481852 388481857
    0xc180a0e070819060611010f0c08040f05031303060b04061710020d0f050106020a0b0a06050a120201091509060311040f03031808030a0e03010b04110a030e28030909020304030503070302 81
    0x720784100c8000418020f070400021100580c0010000480100203094084424083e9500b0701e40c905004005500e50080700812031000944002c05082240c0110000c2c090100280d842e110359821587c0301c125a02d203080001030003d02c1e183c82c0a9410443c001610841151303851590640310000740450085040a00d8025070115500103aa60b40d101c1034055104054820f2602801ea250001e08040c007142c10800300c90b800c0204031003443c90500005205584840c251507045640820040040c0d40c003510042c2e603001700680103070500000481c4640102944404110304440403500c080140204094150341070344101d005149450001400c20000240714914103284e0302c0394503ca0016594a8003007450550b440301500c0070004070082c01d5071200746000c2c41001c0c980d080c06c50381007128060880100f5030034054202c01d4800e050360f9054158011105004903541c080441200c100e900003c1201d80030b4000d0210401e0300090340d0110080f8a40080b44200c90107160552621410752743c840c0340490207503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 388484352 1250 388483102 388483111
    0x50319020301150602030c0f0c010c020609010309060f051f030803150a080a05070f12030c120e040608030d0c0503070207120311030c010b01020c010c1106030703140c180a0e0708 78
    0x42d0350340c04640c40b200c5a020102000782c1010360195607901b076800096490001c44011400e4990040404901243c0c7c0040380da11903682c0c1580c8840c0c5880e001d40041c1c000700800c040c080c3c40031381400c43e034141130151640b18a1148041000980022424001c04d040c041c44602008090341810404a6000740c40c0701505141500700604540050752201803072030074880c80d42c4040707800e07034400c650502000e42c98100003809001d50818a03541d00001d5180102032a01c20140038200301072118546442074440c140c0b1540c2220060401d200300c85d40c80c080566668000a0141c0c01d02d407510603ca4580c6204408030f90103030045500a041041c20705000942d0740b4801d0b80f040317040c00000706005040e20030038009000340b038000301c0000500b07204110019082903082910241000760314181700780040c45031880c040450030b091354150f469944400040d00149588800765040f1002c0c4c0c4100504030002030010701c20030300b28000d1000100d00d1f92043c014203201030b02580d4210b03011500020303403051060b15400c0e4031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 388485602 1250 388484352 388484359
    0x5131b181a130b0109050f010e010c0302121b06070504052d0d054c0209040207080a0212070c090b040f060801060f1a09060304080c190212010605031902 67
    0x300d6904000141c0040700128000b840580700d9400399101d6821002c038200805007502d014a0004038140000c0c0b00c90104031400f030500001e9092401418400c020f145099110045020360b503d00f180f20202500c0010078194807103110700e0f400180d402d84507005650868202500c0d13818100026000856021014441498400380c9188074601d165a054064141640076101a20104e104459044031502101000c580100d450001d10074000381d10f03481c80a06d01d440803e0070121080e441c0c4154008c0c1c4603041e505c541c00380c0003041600501400760000d0224038140d03003c40703040301000d01000c0c03900d006030000a0b10100181c202001041c9140c6c200000d11301c001000000e04062000c00b110490b00240c100080130f80d95041c0522040d4000d00d5540c0180103600e50101d000451100c011000703204000c419030140202101103410045401c0650b1429820076003659001035080884844d10042043d05a2023206180304c840c2e0b44513018403404003910400780240c880b03100d81c1d140c0381500c0c0c200c0d003008070380 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 388486852 1250 388485602 388485641
    0xa02040e130317010605070203010c030903200f03190f03110a0507050312010305011a030a020d030309050703080c0102031014030c0f0a03080708040302040c050310060c0f0605131b18 80
    0x80e0074040c1420602800301754843c1038131284140141400c640c50002c450302132502d4810010042504a501c40584a072042849040c20040390081420281000340c59803052002041906030340700412040c00700e8030b81555a5120720a4094011419544c0b0040894a030907420001100020b21503401070510901804c2240d20380011040c8400400c0030903031040c3c0d02a5520301da940241c0380341030002030040f101100201180491900003030f07000c0550410050626954509220800c41c00380080c0c0005c682007070b41e083c2c5805460310104d0107980211590380032100403c03404280811ba214440c150080c01400a102e20b54000d0180078480c50640c1255500a510b8203000001440b28002407003e244a84140fa440701d08e03510504c030542d2160740c429014040c080c020454555800043d20045503458a010120903206041c05110003000c080058102401c00081000040c4a03075640240140314502400264921b08440ea80d03403016409488010010745400500300c140d250000c400100d01400c6810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 388488102 1250 388486852 388486877
    0xa02150f04170319091208030414061311030a0305030613110a030c030b0d03020d360e060a150c0623060a050105030108150603010b040e0d12090b0403110a06050106020f060a02040e1303 81
    0x146482c40c01c4402084408cd018030480030010450702c3c071100e9000c10b800410341c0007440e42c0c000d821400003c098500500e0401c451441600c0395400200940220003e0305d40d0f12019494000c024201d042d0f04075010a041425407a02c0342800a900d440d002e805038054840b130714034090200e6400102c0728409019401d80400580c0188582140601100c641c26411050518003000c500a03414004d00141c481e0398203c00030018140440e0b02c54070440a01e24040501c61020310300390b4003c091420040961101580f0600064514480f80a00810045030801c0e03100d991200119100c0c8402d004418454008916a407010b16a60f03540c260007690050000c1514000c140120301101d83d0450580c560f680a030080420b144d400c03502e07801e1000b10500090010911a84980c1c14042024000800308807082c3c01507480c5801c14004041040c1d48408140415651620000d585145c4c601807413400b40500347c0072901c01c20480c82103d00329084810b0780310060b42c0f000c840e00c82c84204010142c040c0110021707550f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 388489208 1106 388488102 388488143
    0x10606090b0a0c1b090f0903020705010c020f040921020109020f01050a031b0302030610020a050601060f2703140a02150f041703190912080304 63
    0x303940d841c0070942100c0f6112403403c0641010354003019901d0002d014129601200c006a4040c44200380036900c100848505160007030140c1c0c02044100681d50040090940b0b45000500b1101072800c031740003003010748101020899080c202d9a51001c98007032400040c070380580b19031000300a250780950210394180440500c0c0b0307060050118840700c86a110350007080441004039000300c11640c20740409400b81d0400c1e2101c0340f00703504045103460103600c00034810a490f5045030003031034a45d207003100940d1390106c401410420010350074005883e00d840c024020b0f00e060114441c50030928503509124001c0301500800d030483e501b1003d540c102596403007180921309800495101e5036903a051440c10000e02c45c3d0391103041c0030060944021895500403010300b04115003900350603031200c6000ea04484030b404c84c0c014901c04580d04400b078004110f03444051548203205280c829201001c9400c2d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 388309352 388489208 := by
  have h0 := BRFrame.cov_init 388309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 388309352 ≤ n) (h2 : n < 388489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
