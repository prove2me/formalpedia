-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1417
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:53:09.218376+00:00
-- url     : https://prove2.me/submissions/c2781482-b4c5-48a6-85a5-2629fc838549

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 254676258 ≤ n < 254856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 254677508 1250 254676258 254676277
    0x403020706080709060804150f24051819020307020a0311011e1d01020720120d0807030b030118020f040e0601140d05030a0e18041e05120c03 62
    0x18101002440500c1034410b1403040b540c0c0e5944044940c2411421502290b01500c140d4030508007803c0711951403c21710841da54100642000980b802c2c515082e0301a00c2c00f030041400d001008000c081009440d07103c00c00020078142110f00d0019640e84030702501034202d07401d005c0341d124408010800d01c1a0002203c2e40c40e03034041c0d06c030030700c07011081c0040d98244c48d00c1080e51088680102c001158541154022420013045d008080b80f03198482d09942e070898014010990340c200c09003400a1461107465008000a80705850342d10342101e00c803c1e00d039503c24007040001e0070001da09000502c1c00e40301c2c1e880082c4a0100400030f2010104020034034200723017505041a8483c060013012101c95191a11070346511308a014042c0c4042ea103480100d415400304654100e0b0001c0003403040d030001803c180700500fa110840d446148148071410240a030301e108108520000e89005000e100c0031801461403003060194440009541c0320161510700e040c2101c45403114541d480c08030700c5001c15070011001c0c20300c40301d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 254678758 1250 254677508 254677513
    0x120c0801050a020301080a030f020c031218030f031204050c06071208010603051302060d06210507143303010924060905010f030e07060c03030b0d020a180e0304060206040302 76
    0x101d4450b9a034040b44001e20401a15a10800c10f5100280c0558104820200c990043d221008a10008217052000e141c840a90511000401443c50038550083c00c41341c00c0160000c004036506803280d82e50b80c0c403401d0484042076480c10001001c004081040e00f00e4240d000d4441c40d00c0311901d20b0720840030b41c54030004102089043c00042a400d120340f042500c42c24a0170030181e4210181d030248007496002584181c0b1517902c4640128281003189045064144010001400c030717602c03810000c0c241280e9800c42e4004071881003101300c1c41e60321007640e0b221740c40c3c03c8d00e04500c1103000c007480c200c1c40028024000340f40385008000000c6040307840c0c1c8180139210481d0b04ea04c0c410781303041e4a0344480401c41e01400c800b0840e40c207002d000c203503c2002d50700070461407400c0020310205245070440c68001c995102c940024000300d03a003020158503000d52030700030b030040c0d880d402143d4090340010410f00850042411981141200c4c010980c03940d00041800d10f00801625503568984070000d4880d40708480a40161 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 254680008 1250 254678758 254678761
    0xa030507020c06040b0c070906080a021306230f0301050903030907060905090703020c120f040f0501081603020d140a090201090807061e0c02060a080f090d27120c080105 74
    0x141c00490442c8158030010085032030141000c4880300b42d500b088080b50518803450346c01280c80402c0d0f00ca4640640024001031000e00602c0c07040229084402e520300c9401030500c08100f007000c0c090042c03604411401510030b8034090310b000115140c0c0041c0100264558207000034400150000320085008000741d80a41d2030451f126902511645201d01c580754002020f400021640e030304c2640500204801c4030300750307030031860304000c079440e40d8000941104038120700250400c40b507641031031408020b110130f00b4075040a1038607460881a00341c81c44030701403e00d82c00103040302c0d5040c5141c0c05651480e86020b402011402c102540c02d0081c952003004a010812089010403500c100107505412a04140d40e005075508050900103100d0b65402ca02206200000c10700c0d20059854001802540b030603070341d69501ca840e01036110112824041c02200007034000303540e401526544414406044104082e941104800c0d45000301d0811a003540000c0b5410b074100a20010444a4001c000c11a414600203011a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 254681258 1250 254680008 254680021
    0x2160203060403080a0f020901120507020a0f080a080a110d090503090411032202090a1a090c13090b060406050f0c030406020a05060a050f01060c060f0c020a0501060b03060d030503040f05030406050a0305 89
    0x40307204030108d0502041c81442c010b541c1005030b40020f40e1000c114030584900c610030b9035400914008800301110040004a141007055500a640903401002e100d4288208942101c80072128403d45c1101c0f0013040d00c07281c0210500c08208100c441010300500104100142d5480004c201c0d00141d56a0f02c0d01a03049924071107030f90248035610b50007500100030b41c1458a46640300d00041c01094a00c0c100c0601c05c10710b03804147d9a11801307620525000001c55520a124440110303081c480383c20010034a440d11520014a0701e50f101510196034850508582d18900c01400c0c0e4508d01620019000030321000402042c1d60340c1c04540449094401d504031111604c565841100f642c0d41141c205400364032100041022030304c40d880004155000740d40004890f90390000d840141c0d03101c4c42018001d42d102182d0b480070814248603030300c014a4540304903411030802071b00140c490305402c0c40180422034040b01040a110030301c4842c0d90001e5008044075a01d655403031014100750001500900461301d4a0700140b0b0703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 254682508 1250 254681258 254681261
    0x21509060606160c0b0f09010f08010f06050a0203090a06051c050603030a2a05010b011202180103020702031606080103060605100207030204020d1517070605180402160203060403080a0f 81
    0x3180700030315890070701c4152a0321024440401d40c00755114080c0050026890000500800080c0706000e05035503200340030f0300017510303000d20512504100901440100b11000100e0701c2041a201146042a81da00415804074554050a041198450088a000181642c01c08010300d0203008003c42007078040810030342d4804545089800c0d58040c0c0080089900c0c05120f0164002c4151039612848a0303400e10002c804503048048900f01c480c1e84d0340d4202c4c0c01b82036030000c002c07041140c250748095181c0240b110f17907000c0784a140c4443c1c070305241c0c01048410440d034040c4408034101020b10455a0310f19521280144040c1083c40107440452502402140e41d003060041800344940302e4000b403a00610359403c0c880203500c00c00b49040c0c180e903990811008035103d401031400500741c000280818480c1880b80c40d0030040150322030014800c04210081c1c0d500580262980d901d401103800585806814928030000024840001e600d8000e1a0800c8101900452100e0050440503003c00c90b1910200c00a030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 254683758 1250 254682508 254682511
    0x30b191701110414220509060601120216110d0b07052503020a02091801060909060c0206160809010f060b0a030c08010b1b070506121e04020a03060e15010602150906 72
    0x2d15607181c00b81d10b01032604141c20071030307000240c2050441ca90755005000c1c20031600c0a54034440c49411160509c0015a80041c2c1000d850001800c210b2410f90050060580c030b00c10800c005201c0d10500310340d02d409554500c1481d0810b41c102040401c00d242511006015a0040b140c5601086540510300b15034800082c40c100415030540062030400c80b660204401414010000c2c041503440400c030407203004003806004020400c14031b003c50f4003042860040203071424514070b01c08540c00070080140740c2a0440050444d2113241c24402c4140d00c0d40b881040c090402100e00401c418204032000502c41100d1009022189440d64100309460a00c4401c03103030301d5401c0c403500f480c41e00c05001080c00e4621003003c0300445030744201111039080d036030004a2150f4010000300451740035250100315407041c0b4101401103c0c116044440070a103091350000e86071440710b002c017800060b6122400c801e460400c100040801c120640d2050071507a4451009507035000c4810040106c58162021400a010018150703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 254685008 1250 254683758 254683769
    0x307020f070f0f031401150609181401030b0a020702180114121b0d06090303060515160809060909040503040612020f0703140403060c08010f060c1101030b1917011104 73
    0xf142c440c0c0307191900440402490f640d0025956250366488240f40f121010344010700507900c0d554140c0340340c04405607054103035922202c2041c0c2000440004896a00542411f580e804103200200351541a00c481c0203010310b003c0207401c02c401840042000c1c002c00c1c0e54a049903160309070030240010760824010710749905044001c681c2c0c000c940c2c40b0655840300d610201c00c80400b900c00e55441c0e0403512088156404180183c01107596000c00b8009400c0803d2140040400e40d1040c5203482c0150003600085061424054085200441d440500750b0b900401c448208030018100010b0b4109404c05a4030fa902c00e1003400003181c8244c0701103450304118001e9030707004509a41d010b41010780e47e403400c1c0d030114501002810303c07220410000c40060340d2072298589041c0c0340d544540351503040007900e00c8000c0258202106120860101d03500041405140f214244020301c0c4c080b8800036050045903214035071107010f03502800141004684950103017460180003034810001e0141c4c69030002d01100720b201d2030055 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 254686258 1250 254685008 254685029
    0xf040902070606150206010521070e0a060803040b22030f14060709080717070b032e0506030a0b060f27040506010507080a1209060c0f090f032301020307020f070f 71
    0x108500c0c94003c003c1c291420700089c4441000c501400d07a5803d141c05034014902d10300c00302060043c0e00142c8d2050f0000381c50000000c1d4134080c10007408445074050500b0384403280401c5448040c40000301d044260003140e020308550382c03250f0381d850701024100701881c0030101c1d48144c0001445240c0b042000343c1c03c0300c000c00c020b490740c00e080c44c202c0394803043c1c00c03d4200701e5071050b00000a2021403403801507224000181460741591303141021082c42d041e11100101a01c41124003d1100759a6402142e0300141d810800140101414001c150b55000300c01c030748003a58001158000c80c0ca001c00c3c1d030703110007140751101c01039001d9844020042203034016505540092010302038040014410b00003090802c005050103d040ca40a990714016188880000c8400d261149180e540d16500140006c0700524a0705140c83c031141032400304400c0040a12014098110f04086510144071509000320000e940c540255178074036110741e02130740d10040c150f41d40c0e40c103208201000600c100011401d40550b0a044d95 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 254687508 1250 254686258 254686261
    0x3020d08010f030206031816031e0308060108040212060a0b18100302010f110703111206190c05040e0c0301030203160b0a0f270810050402061605030f040902070606150206 75
    0x303100b00c0da000101103e4907490307c0101d1141c1a5020065400c806080101900c0898114940700080140a0b2111940c0359440c8820384002500844c106d940300c01c007842c000d0040e654500009000c4242c0ca500507006000700c505000105880f80c120501044c01030340e54481d00f48100e14004050041111120075006250700148015849a0084c00c0010554038005901d1801140510b0504441d0340c800c6070100d6840740c040c012410003160101c1d00c0780f1602d02804c028500140790030b80f0715000321101c6591541c0e512400c1c230f141e801401510081c000e4281c0300c0da281c2c5400c1c50f0300d0340f0384e5101b0301042e4406d10922031480780d0741007211940400d55100a0b4001e0030303d0351000041d00d400c402e51f611402400480c40c0352002c0b001c80c0301c0c9110281c40045280645161416290a003130a1400c0c00d403021036401c180c100005600c50100302c650b5070346151005546000c1c0341c1002c2d42140140ca142c0110740760005400190010f00b42c014020b041c2c0595000c01c6400c5c0d039002c640c4101c200402000703026800c003d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 254688758 1250 254687508 254687513
    0x80a02010c02220501060e0f01020a03051b030d0506011107140d0204020c0a1127010506070317040302010209010807050a0c02040504020a051203040801110a02150a02040f030b0403020d08010f03 85
    0x9240501541c8040c000310750310a20010003414608a28011281e0241c0e2580100300c000d502050007c1c0c0c142d001c2c1c0740700300c0c510b003400300007074848030034800c06010300000080c0105103030798111903130110402120a0742e4854101540d4080075010545015000030000d449043c91804042045802c8425502c0b8141d045a4418240450305024130000c1e81c0c8207600703000d025110141401282a076611949581c3d1401000b00f081081446081040c1843d1b0140c0c80c40c040a80c0016400040c10340d201201c0841c0c490b0000d10302250000f14020400d040100090140010550150058072058400343c0724080c1a81e41c2403004c403428094607407004001040d0480010142c2056030055410500242a4500d82030700c450105514810010170300810340d000184c108640c050a00c50480c404010206d007600e00804640000d6031904140009500780030410041185680705034100e070000c0c9518581491603964034100020001e008840a50250203001020f01c040c2c0d10901400303060301d80141c020224242541c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 254690008 1250 254688758 254688767
    0x321060109050d0501090605100506040504090206070c0b03070201060b030708160e03010c2006060d140a050d05190e0604060e0103060e0124020a050c2b060608010c0207080a0201 78
    0x29201606000303640c00003252903141c2905611000c0d005000110b1519030503e007040480b0001002d1000c0e07140030603014003290b92214201c40413254210b40102d550646800061818031030b065000b042c10804807000141d148030040614411031098008210407642e170f20656072984011640d01c40052200c4000404000d41d111030080190514902110b01180c1207012a003101e004240c2d4101103079800182c0d5008080109003500c0c06038207000600000d0800c1004500f01030301c8440c0c01048860200222130040404110201107107400c003044642c00c0c2d04403e40500181e018400002d034125415a82e41866801002001d400c084050810752820f458140c00301c0b41d50f078503030b036a80d4105a1604000034010f01d500b141b080c06049440b01e06505154120000d090802002000d0400e5400c9001d6141c049000429200d06010041e500e40d000142c0d00b011010703030201c104003201809203255001c0c070288146580030100713640c80e400c004c21140d441c410060307070707140050b120303114166216010500c0154441e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 254691258 1250 254690008 254690011
    0x181801090e0d020318212e09052d01050a020316080601090303030f06081209030d0c1a070306150f020d090b0316140408030c0d090308091e030106030b040b06030321 72
    0x408003021800b46204d0f4a0504101080a40c070144070724240d6050415907084950b0240509282d0080112220f9655a1032b1603a2000107048003584270903140542c1840030039640d95104002500801051a10354080402500142c81303040c1e82c5043c0a9640315160b000701051402280c050b141c4221003032a5580403800380c0012605002030984030b1400040c0c111040100405002c0903070703400343e29944a40189440c0280400000d400c10140d00280d8001c2629071400c0c070310300d0080c241c50b03450176900d44109401070a0301d58000b07413000c07034504a001d40c0941c0c08a01841c60010507030070340e1000c2d81c41030012100011240240010310000308085420540c10141554894555003418100040c500302c15070490317007140c0c0c811301c999003001981c00301031402840300c0281c6d4002400d100017031a040d52a2407500b4003d030003105010b1050310b449a00f070040d00c0e03281840710150040c02440380c0754032444d14141d150303015a0304a41030743e0701901181043c600442030310b41c9540e02007103000480d0154000074810500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 254692508 1250 254691258 254691289
    0x7120504051e0c0406030807150606050d02070203070b03070e03010608031c0504110904032d09142d0918030a141e0c10060605181801090e0d020318 65
    0x1d044a03c3d04561514094a001140030724021500c440da607042c2007a00d24181d80320700702c0d10751820505016890700041a03620107900c0e9900140c40f2115131020038a406250b401c500d4181c07070040100aa06a4001c181c448024416002400039556800b1425900c1c041c650104420201e01000300c00b0308031495100300d62003409158229041622030020843d111019101603002501503800d030b41a2501140801c1348460340d1009549404980000c01400c051041c002c0508040402e100d0320460f54075000000108091841031040c0001104803a0030790765501251540503000d8400041c0502c1541d0f10601c81409121014501d0082c0105040310316019080b200080a64207025907030040c41c4540580080f070b50301b080426600c1c1c1180e00d200e803402ca042c465509a15042460a0240c59800fa0549850440c1040c414851500d4040018a40399025540d4040b00c140d00b0000200c1407413541040005800c950103890244039a52000c17030300c030b20980b00c007020007404112203060380f400c12000d0409000b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 254693758 1250 254692508 254692513
    0x61c0210050d09020a0e04050f240901021308030a0e0102061b0702010908030f07031706010c11060403061506171b09011101230709060206010b07021804030807120504051e 75
    0x81a030005d9100b0489400050702d18407408208001c00608212402440d24000000c04042618400b0320ba103100078680c81a01800070500407560b6080300350152a000100741588041c141c1d1916400c65480d08240c861a0006c2e596010300009540081200c0d8040d0000a81150100222141e945010b6100c1d0500300c0c10050360000005901c43c0520141c251011044501d940d00c0005040003041e2401c04c403680c5d03083c880c0003401d01c0002da030001a1455507980c41908040c101c2d0080d0001903071030113030f9407000e480642480b40460702d4102a5481400b980c44a07100c00071046c0403003ca82880303103012145140d07040c21a860910f0854000c2001c0c02848005250038124907040c246400d095800075100d00c014000c202204512502c141a40e00b03602c0320315890031900403440c0c4117000750f8441041c8210190800c0006610b415901c1d882681c00c10080e12201032152030a06203402400b0440c104c90450000302c80300c4860244030f01c51b0282e04d01031380e000b400030404844411040380001c60701300924440362 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 254695008 1250 254693758 254693771
    0x60207091a09190501150f03150b120f0a091502030a022104020916020c0118050603041a0a020703141b060a0207050114092d01050f061c0210050d 64
    0x30380d01d0340c290b14411080b190810001c0c0c1540d000d10800e440060b00891605011070001e02c406650103400442d080c00d85182c04286400740311034241c6022015000390280550001d10501c041d210090302c0c0e03002d01001080322030942c1d01c4911200c12940d081c2e0b4000d0030070200080c102601612078001d1604140000d60040c50700030b0790742d1000308070804050741c00d01c0c0340e1a08041005620b410001c2603403140e00c4c2610310944d1241050004d4030303240f40c9601c29060000c01d101c50010b001d00d41038401d024000160526035681028100040740403003c0f421b1a80302d5000c0000101c41300d60038001d841d0015816144c4030110143e84020403940e41080140b18850103c20702155180a000c026940c0240213416005a58280c10f041460030745030040091446082c00c002400f610360000201e108001a22008108000244141900035680400510880c6600307090a001c240042002c00138000d0b14221803a4400201c0303040d41c244130301d502c0c502c040d6010601c001042d140358041c0c4000c007262a01c5041c001100c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 254696258 1250 254695008 254695061
    0x3030209060d0e06090a03050301052e03090210090602030f03090c0a0306020406091215051e0703050f16090b09030f01060e0403080c16080f0712170c0406020709 71
    0xb5000508415900342c0c440300d2484100c801400283d401454000141050302d0040d02e01404910061007018010f01145901c8003507078031803903080b8640c81c0f4112042c419401541c5801409000401400d9104400894a002805000d0010002101d010350061800e292440e90b109031b5907003005065915600501c6058011680c42c1441e030006544104001a215811320300000d00c09100340e00128040c0400200b1791020030f4190303400080c6400404404103075a602c401c0b0070070034252070b000032224810b40a001c2c001c006d03403da0006031103805001c421228a40da62907452101c051400318040104d9401c01c001d200f410303401402001b10318000b83c1128801e140c08014542100d07102d0b48024001d5078000144420580d0000c40140c204522a41075428210000303801000c0c08400e0a00030088240080c0c01201e004940041d642c80503008864a01d0308118000701a04066441c6918000080c1c0400021030072040c00055a05560b0103500800100e828810440d00504c0c1d03458000007041001540c4003007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 254697508 1250 254696258 254696269
    0xc061321030f0b03010605030705130b0904050d0201051b12100b1809010605040b030c070f060c050c25140a030803190f020403080a08040f02040204090911090c040b0703030209 77
    0xc0a540694002620400504002046a0002c03000034400d9042100c20402540c0001d145001d03214111a100d00407003410f16010010140003081c3c07074206020404010510101041d042c04d0001290002e11142d5202c3c014483c0084030354107100f00150301803000358690f00203001603e9021a04041c200300464030340b075188050390404007090841c0b000242000205052030340b1141d004001e02e0034014240741c200350740010607010084c440c1c0c0c135030341e804102c15040c441070148070705445811800c10000300d907851200500c240e0040803011894032403d9241046840380e403125003202c2801d030320280541801c0c042e44072048607050204941c403c20003040030020881d0343d0000c602410301141c2c09507000c0710656106060b15040b00200810b548180410404034068034215000030000e440d0481c6184c1c1c1d103140c0780015004410700a0b41261001c40d010444201c00d43c01249014003034001c013603404091404010324200120781042c01d154081c04104461120280900401442810050300f04140c4101296 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 254698758 1250 254697508 254697563
    0xf0e04051509010f0b0d0c0303080c070204151e030b070f1404080d0f0801060e0f01051908060f040204120b06060c2b0216180b03060c07050c060c0613 66
    0xc1a603592400394401320103e5100360007041c9000c3c4d410178110b000540319131207081d4451001506102c002000038203c10107010888001c40e50042c0104494816018081c8041d021070007030301d100d1001b400d0b1080444941200300011240d204842034529503500e90704548070010700d0408020311a0101d500c0103040180c0300540003801c0194024100c0400340309000b0507103040300d201e8901307100c000c40040c000a54809030114800318144c520081000d0750300d0040b14903100310350a440c2405600c000240c001a03002d80894000d2008541406203d11603008000c01c074803c5100d500642100540303040c0024845407041940139500500c81803d01d8503c51440b410400410100d00680c0d400320b960001912510b0951038601c44035200400607078181e04041d1120324918001c900800c041000910f20005e1243c001660b0040050107a03211420048684102a080400e049507603000d103240320540e6040a0058480700d251040040050f521011a81010b2a640510654540309072800403e01d00c010080b001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 254700008 1250 254698758 254698771
    0x1511040302040e16061b061104030212070f0603151a0403050607170a05060f12030c0d020106140f01020607030e0c04020f0c0708010c1224120309080303010f0e040515 73
    0xc00300d6010a100081e61040185c000794180442c4640c0030b8a0380d088440c0407141103034443d13000034005e000d80c2e129800c20300585c3e00003580158840d50081c241c0002007010801c0300c200400486050b52115402e9042c0ca52040c0c035401d1000000b4030070000802441002c1804a048410440c5000d80700c1e103c05081440440744100450420429100100f441c001c4043e88504103c004000c035050080006255a03140d2007018802c007101d04185c0c50840c4180102d4020141303500c103d40407603692000282c003810751885044480048005032070b0450900300b081a03c800d9059024011559801400741c0041180b012005524400c002d40818a038403948004c14030740e03000c407102d1501c803070070201d5261903c0030a80120b84c180e418144407004550300102d0b04400d00080f4039003c282000c0c595000305103014001d1100c150800803020000e454200c80180410035402a510f084081d5142d80d051980e0b44428401c03061030340e4421104100e0845d0890082d034205118005440a0305640400301c481960281c4070b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 254701258 1250 254700008 254700013
    0x9021002030c120304021c030315060905190803030c07080c0312150406030b0703090f02041404030f080c040b09010e0a0b040f080609060601031512060501030c05010c1511040302040e 80
    0xb4101407410030840e8a8200402611452070741c541036001c40c140d00303075003506038042c3d4021940c070208060080d001a000600302c014106240360b92800700038101c00d00361140c503002e5840100b00c01d44030300740c4a041d101905c45c030400452968a0b08903001038264030142059541c2501401140f10f051414801000c61002c0780342d0800150034a40101601c1f50842c0c11550301ca640f41440800004074034600c902e61185050800040c40c4810b400c6c40f18800071100070007907001e40b4041034a50f121000071082c0340154041e079613040703140074041d505440640041d1501c03160300300280b00070000503a20708010f0014080c18500340d03da102a4101042c5015a1608500040c0801080c20712800c04c00c01034030070003032a40704000c00d40360501801c4a501c45001400c100d041546420780100b08038102c144180082445a410800d0010181401c0707004060030f01084071240640b0100003459845584441d200d182c1203200c003401c118075559070000500d407400c101140f54505020000141e0b88500c01e410000055402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 254702508 1250 254701258 254701267
    0x19211703061c0b0402041104030209090109031e140d02040b0d0b0418030903080d02040b071202060a0e100c090906030c08120301030309150201290a08030a0f080a0902100203 76
    0xc00c410b9000704032114032a000c01040d25400304003840c805a422903019500001c0c400c00d07004c1c04507664816604060b412405030710510896410562007024024080e03941c00204844111018580c1d10391400e2050025042d07948201e03c0c001c07000c0003000f1a40c00d004005151950b103140590164110300300307592a8564680101c0d046040c14000da0600c945802d4801107070f0741d117130782d409001d1508901016003413200c081400c442891072076044030b02401039030311115180c42091600f01c4454040001c40301c0140140d070081a50005a409600824992a80500200c01c4410008001040c0e1103a0510801030240c0340003481c03404500c286070196008144d84424241049816840c1c00a16403007043d04040808c01000030035401020308058450701e04007060705103403180e8100e02511301d48401f20701c9420f40f002d100d808030107074602040c040e0000b950030324002c3d55140385950b105d008401100e000310b002e0860b40c5071424442c0d80341c035034007101c1488000f03075080040d00880c0c280043c154032480075a10000707 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 254703758 1250 254702508 254702521
    0x80a0914150912120a0905010608101a0a2c0106020c240a12060b0a09090b04060308092b0c06140315090a0b09090c0f19211703 56
    0x1c0c00c0700d92240c22a0001c15140754004070800c070502c10b507001c4294649030400402c01100450304800142c0e0b4108009004403502c40301220744030a504005182c1103841d10001d44c09030300051b214110401001040031184901d0441225100100c038880c0203030740303020440013440d14440414900d010345030720303402005660120024024001844050100c0c03140300c0400c40f03250840c560088500c074500d40d05e882c201c2c1d00c501c13010f06000b40002da000000c080201040e4400d107158860080b6084a00045007800203400e1001400100d40e02400007503e859010080da48050038980c0d150440083c2c0c15806c042c0a07095101900710308150040c044940040402c41001000d40c015020322165101000319403070340c1859045c0c031145010901c1c041e40540040d00000d854040160310941c081007024280031314a181003e007280d1070741c0b41613a46078452400c8004520f60360070843c1c0c001c20000d00003c16071400f02e08004103c400d01e1220030b604005e005002c11218001032814407010303021152041840d17160305151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 254705008 1250 254703758 254703793
    0x50d0b191b120506030703020d0311010c030b010e010807230c0a06050901061d01090504031715030613110d140f0102031608071d060c010618060603060b0307080a0914 73
    0x82c1948030090506041c003030309075000315071304046a90488125400007101c3c60305884105000c40040190f5190074030004905415401c00308903000242d0307412103802100001511480703002c0c3e0742c00740060080043c0201c220894180780b00c3381d12550441c01d0030b013032000380400c0ca80000c0240403070709940c50303100b88880c9040c03d01942c0054254544071013400440e41000c0e0303050140c1413107500002c41d240c9012409050240101c040d45401000100b00249003c0c0c00800d80e05440c0c4640600074410040010410b04603080c0011b03255502c6041d04a0040e10f01c4100000c030090f4a00585950803100a03002c03001904101c0c02344003800705000544c80389082d04032210341e88040b0040340c0910100e4030810400320b50041691400c110081c2058a8540b8000081100390007010980700c080e40c0792a170b0100e09040307880c80035025400c940405006280e110281213090703800c0c500c60000c04040500104120502407420a076100c1511300d0000381e404119101ca41803101108000d130300c0360300003401510981990 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 254706258 1250 254705008 254705027
    0x110f04050f0307150c02040b0a080c031002040b04051e1815090c30010b070c0b0a05070206030912070b01080d030b090601031503051e0610050d0b191b 66
    0x1c6020f4000036240801012600d0704550f98082004001c1c82c20f031086603160361101c1081ca001410114280741c80d080380c1651500c58001c203074031134400d00c5581f041c0113400d070080342c06684d20440d10b40c5c00c1c149001c0c14000d00c0e075084444003000d40c0d104605c00203103444403112242c030b00c403448e48401034074202000541c1e4148a0350148074050b40199080084480411049680e200c100c10012802e0400c4000c1d00705a8014180c0700074910401207000040604281e4041c0a82a008500f080c64165503991000702610a4421030300c0411400c3c0031030809841c050003d1940040340400b641d0440c14044041c031160386c40000c040f40c0c0e9503030890050014400801c00100660303164141048400701900c0004d50b1800d00910b01410152184c4c0078048032a0308001d007000450f800400c6070030000387c01c01c00710022460b07400c003142a48592800100302e07034611016030b4201c0b00090046280411146c031400d006810041100c03003a1405080348841d5188544074001c817a081140240032400c800c1d41303004044001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 254707508 1250 254706258 254706289
    0x906041502040e01180209180601020c09010503070b0f040906090f0c0e0904140a0b0a0605010e060307050406080c07120f020c040e15042108040c0608040302061504110f0405 76
    0x810b000500002103051801030541d000c0001c90090310300450710f140e000e485100741c1650080c4c603200c400003403149410300d0540102c40c26005e4519024100c5e007845008c01c1d09100302035044c1e1000d030007040440d103080c0c02000b1b4041d11251451400d500d80b0903410984100350b11030214507569082c0311414480e188074203641d01c1c80070b1602d2805400740000103412100050b0000e050600c40040141da520820052040000e40c03003240001c0624141014200500d030b6841240e0108800d50003a500c10319224045074441d00254964900349810540100ca271401c6c003d0500210304c00800080740868161208201d0001c443d50740c801740252903130002400d2211004110380103606011503082c0c00310012502141201280340010003d90704c5042030300c14070501824920824661580c0c10250642c03040c003440c420f82c02014000046681c40108444140d0708640240060704038a000c2500403030b8100c1418440040280045049407402a0407600ca40c000400c01c40081000201001281007841d040a100d0b070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 254708758 1250 254707508 254707511
    0xe061305072001021303030e040e060610180f030501230601090b07060609060305030a020f03090108160c06051501080903040305061b0c030d021c06050a1a1209060415 73
    0x145040003a00701d500000741001e00100d144845040a4404d505030b8024502c0001300b50b0503d6900d0030054054440d401b0968042ea0074146a9210722000096071406414040c0c4801002080404201c0d80b50a00d035031400d200d140510310002d5021100c4c44a0009076000b5000010340c035200410040002d4042c0d14030043e0034640d40c08100d440e03070304014080111014441c02664484c4a0f00d0020000d0503e07401401e120741c03401c00c020082c44800405000c981500c1c0c2c080390a2110242c049030707903070b02038000d00c280002c24200005181c45245142d4070203001190805d16410301450b0348500941300e04032031720480711001000c050301c4c1c2e603072011125800c0141d20000d146403d085885603500c4150092058554044854203510000034480031a00c42e0340d00d03c0141c1340c492400200e14000b0f5403103066000c500000340c2ea40980d02c45818801c8104030360000785540c42192400c82c11a010404242e0091a500d03400d0040c140405220a0400d20a65411015002a00c1c0ca8030b44030040d505000070010125 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 254710008 1250 254708758 254708761
    0x818030d111b2116080703051b060f070f050d0f0e0d050a0321060324020c1005060f090a060501080723090a0b07030903031e050904020a03020705070e061305 69
    0x15191200c40c100c2920f00d101d0000741003000d500c034181c0b030524a12149007440c0c103184000108010081889020b403486035050351180d802404130100300700c1c9483c0307002e680020100800c3c100400c82c0001004554420305840c041e82803103898450414800780d0351071010510807032038580e039113a12405204400108803244c50844100d81c0702c07543d8480050300001c003403091005c2072001c0e011208140c03140c25a410002444055140d1808000303204410309010800c403a07044010003503c209000b40c131240240c0000404203c45141288005000043c2c00346422010242c0c2d898051784841c0f065038845e480c910404101286041c0004001d03071002008107003082000401c1ca0b8110420040600c590071001c0586500d0300c0400c00010015030301c50b4052444104005041c07000c05401080350070840c0d01030344658403000071060000c003100e4000391044000440c10030404075145003d50150a200c04149401800d0411729170b0303107501d06016900041c580c5080b00c010030801c4d00d401148003072154502201401203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 254711258 1250 254710008 254710063
    0x204140a06140a0e180a17040602120f0d110d020c060402090124180b07060b03010507030b0a0636090b0f0d0f0201210204031a0408070818030d11 64
    0xb24001401009074203171020110103001c078041065000342c5400c0880d40450603224000c01c00254058800e20300035000d00c100346100d56048000341c4030248003d0b115280b03007020300c108020080000041c14a010b400a01604c0e00c1e10615101030000903403580020856410140104406450142d0103040c0b05240710f11000f200f0b41480024500481d801d06051040034400b038196940b0798042d0300454940740300422035006108094000000c0f180c4150b008000c16140c2040031000c0c0c170024450309810014104080018030300c48c410380e1044041c012981441c07403461129880075030540b4400e84220038845102401001e03118400d02c6502e01e812035000080300b05402c00b04003220322000003e80b054200c0294207040d64001d815203204c40c1c3c40a2401442040e4840551000b5007040c003041e1880203801102d01d05401d00070882900440d0010340240c1044003c4daa461060f83c0a0a03110301d540301413003d085000e80342041881d0103070120740c80d98400054004425441c00748204448212550848403c406 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 254712508 1250 254711258 254711279
    0x9080d0c08070302031c050105091e010b18060c0304150503090a0f030c0507030303050907060203030f0c030615040803031815070503090304052701061e0c0204140a06140a 75
    0x302a03500261180c0c851100f420264190700400c02500c0c40310481d034000002003040d0340d00c05410f030340302281c0c1700031280c07a1601910f40c8890303100d040700341358140080103021120342c04014015441007050125042ea0613803000c07a0403600300c0e0114142c0c0d41d1000c582071110fa2140c1c510008040701d20719086003580f0304180050f0b520412580040c0c501116011003005242c4207500841501d03030440121303a00240e42c1e14008000b040b00300e81019003402500c0d00810842d03c00b0040b03e0145840100c04251074540004c0b800345544080d00c403a91002c0004002240c248411014000800001e8055922858a00d603040006060300f041080240c001f80d50a52207034800c814815000080c51404c9900d80c1e44140d0000e295119682001d50310401d40e085050b00c19809d00380050300071152890000d0300e6640c1d01000c4c0c0c0c0e41400c4000d900300446a03040190543d5110304900461240028008908c3d1075164494201d0342c8800d03181c0160325900c1c1c5a091041c04038030354480415000955001c28400d141420206 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 254713758 1250 254712508 254712527
    0x304050304050d0c0e0f0a1a0a2112030203060f27060109081603060f06060f050a05130b0a0f090605090f19080312060102150109020a030e1b0109080d 66
    0x10310400581c0102c5050080790348079107001c2c1c8031061800206081420b611040386c901141e000d00c42c50301b408510030b4054203000034850918006417090103d00d0901804280282c3c003480004806441e00b1702d03030070103d080d02201191100c066200103070342c0c0c1814028031843c60000301408e0f000d800a50500841c402071103150121f8001c1d003000c0341080b80c8942c2d004980125a503400f0840d94420b05001d140e4001c2054600411a880f0705820400c05611407000026501644280800700f0381210030b1030704460160004100d110f105d494000d151a18120003200103158540001c2c1d01d21002280801d5201d80000345141d010402c0c0c01c0250540786030440044c60340c49481d040c3d80c00b03081000012074094660031591a454000345079504c1e68240c031681c00e2640c0b90040009246903542710340c00f10f40705500100341e119010103074858803080e80e802c00c0c6408003c0c5d88100041010540d450000001d58503062000d490214200c0010002c0144c00b000018441429a0440280d5401000614502c0e680045044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 254715008 1250 254713758 254713769
    0x7050a0b0d1d0106080c01120501050d020d1a010609181103061e15030f0a0504020f0d020d020916030e03040e0103030f11030d0902120c030a06051305071502120304050304 75
    0x400c420701007800010007800e80c644030410b2582000404101940003045844901c0001c1c1d98680c92440314030f580400b45c0350f00384212500851400c00c100054100712241480c0300d806980740d00b107015013800300c2540c1c00c4030981c44640021140b1105000d80b0031098801904051422414051101c4510301c3c1c010621015044a210301c0c1090345036280341d003a02103442e54121000703101c281d007a01d024020314a698402c4401c1540092603c00103900200307076114660241e41c001e4103101c4c10281510500407030355054a0180d90284441e001000181c1d10221642e03c2404844c0c1c03000c078103c40c0302d4000380070786400c0015030045ea041170100b4028501e0010b84681101c0c2c0510300110580000c1005680c98840302409181c1070000291000341ca1005411004181c0c2c8240c560100040340144c1d490380350200ca40103180c0c540c0199041d10003281d0ba03608050b42207103410104a0034401c0581e030315854401144e000c4807500c6041024090020b4040c0651340800010380307003941c55880c00c0da45d5141c0b81c0c0700300c2c001c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 254716258 1250 254715008 254715011
    0x40b03100503010c1e140309070f0515041203050d020309100c03090512030c1e0a09060c121d0307060e04140106050f0304060b1003200a090509180105040c060207050a0b0d 75
    0x90040d851007640c4001a0b0706c4491001d0340e036400c055000070303141e40c498007c504070062420400240c604080000070132040c5d6026030b03c1d003018102808100071030220b540960800c0403d1120101202c124401103000f2060354000340812010cd02000080d41c410311214014903207480f0404d004640003003850001542e881110b983d40c0e950380000031426004505995600a409004841d00056103600600721032840761148810180c0e2040f0443c3d6840f00e0520050001a00c000b001c100c0070b004004051603c0880c4220216161011001c24903201d081d502c64000580d2600c194107181c14503100b0000030304107401d07800700690704001000e81076100726080a510400000000b80a200d440e40c010b2002401c0207007020445580804028080c1c05031142c400010b60a010300300e0a50101c0b1801c07101480025219201002e160500300510310000a100040c840d00364482d0f005610070a1241a1050b4420011401c007681803100080c40d00c0c0c0740c1d4020782d0180f40b03001c0090007031494007400d40d0791510444c4e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 254717508 1250 254716258 254716307
    0x91a0405040e102909011512060512150c07031e03180c0e0f01050a05040c0201090f2301090b06040b01110a0b0108010b06040506071b0b040b03100503010c 68
    0x14101d26042e85085407003203851400001c40840600d40040b140070320241d6009500000da20803c1000c40102031050302001c7c2e00034268044928000c50304090f84204008000070348954502c0441c0c4080c5820141c0d0701507401c80b603150b082640350680380729088410180841e04122003640c0181400054003202e51041b000741c10742424551080c1c1000e019050310030800000141b0914052102d00d01c80d0083c06200340382980001c17041d03001c5280fa14100c9000906490842d0301c1c150034807000b841c1d003108100440d500c5020300d00101c3e10000000528501c0b920b40300082d04804515840d50701700c2c401460410764101042100440d1101da47c01c0e4104c10b040f074000a0b205002d40050311803114a0003c0080741c01610030040900070b001100c103040b50740f01c0c0d00038000e51091705d0800c80180304500034150700c004140618400315009141c0c0c203510302c0c2d25242c40c52001d600e07020b03101c480c0d800c04c1d030006004460000810550300080f042540c0200702c10f03030090180c81e400322030251030545901000042501c0007070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 254718758 1250 254717508 254717531
    0xc1103030c130f060c02100512150301060f0f06090806010806040201140424080a090506010e07020114042409020d150f09150c0f0c03030c090302120607091a040504 72
    0x400000c01003001560007403c40783d0311030001c4d01d03e003102142640b140505488091131303180103200321040f41c0c20003404040c1c1c4d683c840d000074035000f00e0345000a40540d600e103800700b500d5a00f100b80c44003410400400100140c500b0200400c8001d00317400500c0d00ba02b0890042144c1c40d400262150040c0d42420b0402c12600300d68600602c03801143d00100030203031454548410104600307042d103c0504950f68a2246031380702505c1200f80d03182c144000300580d01c520010021800142e02e0313036420201c0d901c00440d00802c1d9665000001c04161001c1d2032202d98012400744a0440503180021144580c2c0203102600305600094450402440050041c62010008014a00450740410310f5070311144000c0040358090b09150341c88030580d2380e828454a11301440030711014001c00c19507030003802503542d10300070342d5043c2c3d011005041840107103018484214808030041c2e5800000141c2120303120014401c61818010090a001640d404042c200c1090f1b43d60300c21030360b140d50469095400c1560041060501e22 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 254720008 1250 254718758 254718787
    0x1080d142d030103320304090b0604030605041208090d050d02160c23040506100f02120a11060a09030212090a030c0902120f06060702040908070501050106030f0c1103030c 75
    0x25844025038030070010011040102c4213218004d80800012409103c00d2108200021060b12011004003544140410000c143d401e400000603080c0c064100c0d42001d90381d94420095802c15101111940d1440300c0c420348069019003107550003643d110040c200700c1d500d20750240c00361107581895500c03981c0000d03904175040e1084810340c8a060380081054640c50781c0341c5c04682a416000b0003611104100d200c20b11040c6814051030780110801001d802c00f20607182030564807400300082003c158041c500001d603800c507200380035225000321070f02e0b070000c40318020b0501410a00000c0c04a11414030f480500000709074001540350004000c0380c3d003031383c2c1c0e803240000040c540041c03540007c06101048401081284003900640001d0b0150750103030303d00f52502d460800c25810101e883e01c0d0482e50601034040940360607040461003a0094a01502e000d1668440900356034098015101003615821520364110041c4601c03c21800c00703280c0740c1603d900d201d041076100d200183c001802b415010407a01c0004d401c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 254721258 1250 254720008 254720077
    0x3030f0118290a050d050c04091a010e040605091b09070311040f05040507021f050a020c01051f0b16080a140c0a02090606042103020f0d030501080d14 66
    0x1040080340320081d246664a840128442c0c075540140044100080c00741485401d038203840342c1c07040180ca100c18141c000c0c40003c0c108030b503055903488181f01c504800d00c1e41d01c3c0c07003007406408800450a42490035007001c0c01900c1c00505201e03620f40c020490784911641040b200e150000044604a002e42c0f9001d100300c4c043e00c0b07000040e0703140070070020b000a21030000920103003c442041e50140308669034520180c0c8c030741c0316180d9280c0d48451087e0001c81c951030141d000590210381c00000500780412060f0303290850b801110280201c05d0075604c03880c243c40c11030756001c1c02040071180c0c4900d441103400c6458800c100501c1d000300020400f04403c000c4a0145c8000e480c1c200700125800e41b524030701d1421075582c104009080c0d006c0c041c0f1710046585410804111829100591540302d091194070130a42d80a600e10079095007140100d940d016609101801410340242c090b070b40c040b441e9410000708905001c81d00c0103140a10489031451450340c100d56007520344004055031000d040560070411140c18054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 254722508 1250 254721258 254721281
    0x910050403180806060a081c11120406050706050a050c07030509030c191707032001031d011a030c010f0c0f020907031d07050303031302040b03010207030f020d0203030f0118 76
    0xa110101144000c0700241140c031558040740c06c1032425540e90302c0d0644980508803201c410300c0d0050000c050180c064181e40f02144464402c980c0717007903200c205440685e0020b410140c000b40c400225102408001d0143c0b50308814140c00c01c0000f4244048036181910403004002c041c803001080314000c42c0c0d42480461111103020300144002c05001c1d407003840f0000b041c003504209100f44402e42c801c51000190703a005480d44003c402d900c610000c2c00c00300e080284a034820741056107c8201405201400500c01e0703610310b4040002c200c100024444e9591a60070f000c025020740c0c044012245030760b0340410559485021410000f10301d001508040d1000030f03088201940060184003807012396a410360051211103110704a50300300c1c101e10104107840d180c0c10312925900d81d2090005c1031090b10f0725858000594402000001c00407050808603003642c1062000f0b07004206030034400204d5039010f01c014451409144007640c0b0750704d0308803034030b480c8450180a0108580c1c0d0640b041c03910310724140e1200707a00b0300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 254723758 1250 254722508 254722547
    0x16031e050112150605090105010c0503090a03050102091309020607020f010504090908070c060e03070e06030705030a0819090f03060504030309060905010501052103040519050d050a0b0f0910050403 86
    0x1038540b00c6940c04858038003001c4034080318031004040820420700c966420703200c2c020086c080036440c00c80111005200000191451b000811042440761b49541c4d111006620450000d40c03070318000010003048240c40700c00070b24954109140040140e40c3c080483c0c0c1401c0c0e0448004000041810040300c0501407904101152071a28150b901484450303405001401e03c1841f0211407140c072103804a07041030030ba001440d0564007203107040c030050041c0c41301c4990010016080310a520755a0740002d290000804041d0b680e40000164000f007110300b0701140e0301020807800c2c21101c0a06e40400e5000400c2c05210141400340d90320007040805100b90000d485881c1c01400034850a11a814914001c203428401c09100301140074000045d00e4450704911401034514024500b41480c100c1400046088100d81d050300c00d9102c01d001c203060b600c00c805d80c00160302a1000305130140b140e141c80b2400320300c040c1030130346000301c11010481c08000009006407010043d0b0b4011500752540d160130b82d0400c42444d074240411 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 254725008 1250 254723758 254723761
    0xf05011503080408010c0f051801140a080f011509090e0304031a06121f0509100207050721110409140316050c0414011a2b0c02010516031e05 62
    0x3091000160040d220808006c201e4404009015109002400c40101c0828000d010862a8801c4084070903104141070416080003003c1b1011644d40382c1c0040c1110001c076400b981405031895029034200d0240c060355000c0c1e54200781b040000b13801c40ba03040c440e20701c1d030726114507620420350001d00594005503030080700f42a922610700c426001d440421500c09024200d400c00f082041c42000070708680c1c1c42c0300300c42820102c0c16204114009003800400c0c1c0403040c070074000e689003511403520007000341900400103000000d0070410442540304043c2280740304a07000d0030b010310110701c544e01004285982113500080e6031020303150904502d0100c0d81c00c01224000414140200b000d2070722201788051281d07081e80d0000250208100c00c46640d906035141017107102d0010b002d92507281052680c6544020308031400c021481449024003604200d651100504441e525000c1543c28080c90f0303d5032060380024051480d26680382c101411042490307100b0103440d034100b0141890503079024403c01e00d291109205a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 254726258 1250 254725008 254725013
    0x40309150c020108060103050403090506090111100207020a060e060409020c0a1b0501030c090b0a0806031504050a12050a0e01031a04051f080d0c1b1e0504110405030a0f05011503 78
    0x4107022a0903800700e480e40c40091201c2d8403074415107100b00d03419100c250802d07082200740106078200714052810300c540c24921000c203100400a00b9035103220b05001507501ca4052040c8140300c0300070360005081c41071801003442d032956020152025101c020200503150030700080e00c5c42c44c1c01c464072409450700303003140462215860ba0702d100105640b02038a0034040140c00d4901142c414283e88289049004240030420a543c4288880e0350002030050031a00310810b020a8070505072410384040b9001e80c030841010040101429041d520350f48142400c5040680c0c6a5002c0d00300f0402502a604060762a00d25041c2c040300907101002004000e00200003e240041203402848103104500310000c051070800141c80c0e9001601b01541d01d030a0340c07250050742043c5d8070b0710380800c40c106a100e00c2030f403800c10105003140c3c0310804d000744958000c08100f69618000602c0b0481d8480c10780c000003250300300800d20107600c0c0001c0e0100e0095002100840b2182c06050480c01030400d41111403001d402c0301030020a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 254727508 1250 254726258 254726267
    0xd0216020d0b0702070501050a0504030204020a090e0c040303020d0806130e031c0b09010801090c0e2205060402010e012303090304030b07080103060f02040f0b070f0203120c0616020a020904030915 86
    0x41540d944d0203e4000c151610019070740742c001c90b550030000071004c11061005041540246c460f100141c00d100e0a403e0f04c96005500c41541150b00780c85581c2c02040810034954100000c002801c4941484503c0341071142c0410405007081c40901d6415448210306e440e4800d00704101d9048951003051842d03855040c0d0389000281c03042c14000342c842c1c07800d400049407001c01031040040c0c196205040c403c1e214540044603d200200404941a1034201c5201000d14011085080805031184000d800c1030701d41440050440c10380c1c0c8003c0c0e070401960010501e4000205480c20714103852066007692030f69a141c1c5030381e28622071504004c2c0914114000d100455030010041416248902e5041c06064446400b0340704a0060b845006a180c00c102420090f0100e04401000300038001c0c0011940d0b11110f40210746080c004580d46c000d16200042d0b01048070380709200702e40d0014a0000654801c9140307110003540d80502c180060321400c1e44001080406005988140c0103110280c8040405120b4440241 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 254728758 1250 254727508 254727511
    0xb0d02031e0c0f181b18130e10020c031c06050a080a150207060e010603110f030c0d0b07110a0803010e0f07121d071e12080d0216020d0b 60
    0xd1291140d40304800952400b43c4502541c0107001d811140948080344401c1c400308009800d240d4031550507211403141448000080076404030501003140c1c00490720050103810005100301041417890113084100b9180c011400f06c103107000c0103101580718488200b03a80d06620032548401c00d03100560300c80010007105500070108036841210300d4200346036211a40f035100c0299081c0145011240350342d1284e0221254040d060450040c00009180e0541000080c21160240c1080e601410003421004251500207810b800130441074001c1c20907850010089402c0000c101310040c01183d543c0d0000b4800391050050030f11080c144030484001c4942070030014180d074000c0c0504140c1d4144500003440361914042421b0160142ea99001d2810704d461034050003d00c0c58900702c03200706180c805040e01d0b500c400c200c00d102800001950f0f180941d40c01c41c00407503016081d40098205614405845c001c10000400c3d1002c4046c00d800141c5c3e10040840070250120074070304020340c864041035400040c45412620507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 254730008 1250 254728758 254728813
    0x20102090904140708030313030f1101051512010b0105030a0506060c030a0507110603040b13080d0e060123030d0507110405040b0f010608010f03020d0c2111010306060509040b0d0203 80
    0x6488094071480c10076187c1c8000c980c42c0356070140c2c150008001900c075041c40030310340d07900349029165800c00c0d0818a003580c2054480300c40d0240c001c4010701c0c2c6441c4c041d02d4114104040d03002004a0100b400c0040e016000091608155958130030001c0d03c40d07102e000031241350110704419660b440c45c51440107403154004403c199110b540542c0d4404040c100103080300e0046400401501c500d50711011040e08600c1810401c661312041400b40541d002404c1c007c80904034000700140c00503606202c106100e4a0402007501c44558001c05910059200440c2009250503103141c03080c0c0d6400c1600b08400e0203450b02d1001e40e0060700d050200414003100802827402106409405040307079070b8900e003c81d020203080c0200d002000d001e200820042c58625103003605a880fa140c130f00c40a0f035407003412100500d00001c4030a000b00c42d9081480421000e55440c102d1b00c03000742410820302c0c1c20702100030b03e103028080034540210303524840f9000e140d0b0340341c4004052903402001c81c0d5942100910227100c40d0b55030180b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 254731258 1250 254730008 254730013
    0xc0c16030c0509010b03040b09010f0e0c120304030317040f0210051b0a030210020d0603020907020601080d1d012706180603061505032a0301030c090218090702010209090414 76
    0x710300d0f40751a05825040301c00c4102603500315100d50f1038040006c0c2000e000304211759030b24103100110000c17502510a585030f00d0806480303031891480a000018910082080442d0010070043c00000d4015015142c41c10032841c01c900207a40314139208421201c04c0c40c002c1c0d400030305044000181a8010010150682c1c035080e0b10700c005044410302680e98440d01c0c1d008000d078100440b00c2a0300802035001c1c1085d24040038000c00c0e016503940104400507401e5070f0036401608004018860715500b0030a0301000a503074075215416045100342035002d49904220b07181000501809140904801c2e00504c5091034401c44101105a88100240614602140114070403000d514006503050281c0700310710480307005a040c0340c01d1080d455001c641070ba200418880d40b440041083e0012659200ea21300607451085000590301d5065080412000440d5441130080c94010000140c00c80d0054004442880007510440150b44640c201a030181c0260080d4682288807607040100340032070310340f0103017074580c0c00d506 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 254732508 1250 254731258 254731283
    0x1050f0f1e090108040b07050904020f0d2f090a150f0e0609090a09081303060c0801150c14070503031c0f021e0309010605040507120e1f050c0c1603 65
    0x14180290b00801c2d441c640400c00d64000503003c1002c511000c6d900941d546042460301580350b0000c0d00300e03008200c003030381403650100b000340075141c06200f00d05440d00400780c143c154411440ae0b8054141745000c020300c80d01e9002c14800c0c3e96403218107000020b408400500403606d500a140209141c5075070300f540001440e119542501f81c20300c481105c600e08005492541b069031400c6401e0040c081e489002c4902e10010002e0440707200d2200d40309030107548074000100e0a0344070100000e10b08201a000070500c4155100b0180909070000b406481e81075120303040600200300a0340017414002607910480c1c06003c0040c00c11461011030130030b8580c40340700500802c21000784010300f43c100c0c0550488048100541110041c8001c026401f42d80d01010000021840c40d032590080740a0310400d95040000c076890f40d480a4040045001e013007600f001c1000288040001d0312030002d4120130070711a20313503a580e03904003060400f20840210349a0034441c030100c5001080500c5001102031581c441528000d55140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 254733758 1250 254732508 254732557
    0xf0302161406180d08090705030a0510230711010b040507020c12070503030f0d0902030a060501080c01140a050c0703080a0906020d080c0702090a15030b0601030b010305042001050f0f 80
    0x48007020380d8020f5a00a149000d4003038800d031548440946903607080d220303406000500303542c2000300c4940e65100f400a01003400321101d03000700343c4460700c80d141e40141303a1003480310708031200c1c0103426031000151030310340600a201c05620340107010400d440d0760080d060070b08005010307070000b07021510410223030f405041d014801c101403a1244450b018007a450740003000200e015070f580304040e00442c01c0d642c0001400018a030f0009180c0060520211182500e0700d00400035030307074188046400c140c420f081091551220150a00c031a20400b020b13101400b40c00f041e4088034000800510000d0350340440003030344e280c1c1d9540001e8543c41491084c01c00500c21101803401d2244100741c098002c00b41e00c0c0f503007403c050036982000202c1c4d4000304648a42690f0708115450403503008110401140241d20500c110308140000400340c17130801041c02e05040c20701080c0710010b9103c3c42001042410300d03c0700c204020858004a60f14403030195010000b42011888401e416005002400240c0c8400b0b440c120303c44003034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 254735008 1250 254733758 254733781
    0xc0106151106100e04170c0d091508071b0804032d0503040501080c091f080601020a08030408030a0908070303061e081f06090e03211003030f0302161406 67
    0x3103c1c060002c014440741044240c0c03405801c990000e12610302070244895060010710540c200f00807240c6d040d800710070710102440d0084441000340544001080c0d002c500e0b5130000d410005c01810030707800c2201c00139030104240c81c49029003404590080c612070359141d89080002c4c102d141454062908030740d120500e003400e0b1083c0e20682d0800e5000001c0c41c1024900340041d9000e00004184004520007000310240e5a625020290011750b003442d402c01c2c2400c041c80d0010441500100100e041d9480420441d011850080580758000c1d4002503180d600d90712101c0d0b00700030b00b0249a00810740180410004201358058102c401602c3c100c40020186055411201602c090703203101c4d245084c1c003c1002c80d2014926449002ca4070514403001045036541c540c0e003141290000020b62500e41c0011880403000a000d100e200a0a0580052107a290420311845065601244001001d02821050141a0a0190f01690340401c0c480061500a641a04003904a5140781d041c4202c14001d000c0014442a41d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 254736258 1250 254735008 254735011
    0x40803040f0f0806042001170106080a050114032104030609080c12040509041104060e10030302060c191d0d110108091b0f0118030317090309180c0c0106151106 70
    0x40002c588401c201c030f100c6d054500020003011810014903141c4c521601c0310b0244c00500810180c0d44828152130050702c0801200c406800000034014050010408c9580006100c4082000080d5a4000302c0d4248400c100502c00c42d0300c003c0c1050301f0200b0710780c00d01c0742c1a00540020112107050320700701541c1115150303041c45103000d001d900503040f0011802140d207a42501c10b8072200940000340c480c0d10b44081e072901e4181191f01880005210320148101030b07040c401c1075080b040d20300820b8146a46821031140b590700c01001036042000241429506001d1880740d4420440c021700400149040e9042c0440818010144540412181c5011a50940c400a49941d0b0050b40ca0411040700c48030a081200303400c0c00a0740d42d070401807410f4800ca00e117202140341000030340c441d460708403841060301e01e5240003040c014020290394006016184c1d058480c846480c2c10501c0c14a014800c5581c1c118521109005000243d07203258039245d00481c80d0309000d4003070024258180c80b50780c0c860324108001d5a2b203800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 254737508 1250 254736258 254736263
    0x2070e010302010c0602030423010515041b301b0c030e0918030c0a0203070803030403080411061b010507021002070c15030b03151b0c0312040206040803040f0f080604 73
    0x2c04c0654400410003643c041c5030403610071a6004260070540401c5801500030311311040c1c0d00d95491050120503c4003905178985102c00351014000c1440a014800b4031588820143d0240826140c40c0c1c050b441842c04240b1417464403000f011552450101c11000a11080c2c00800c048060843c00207103443c02000d0f8155015410390f9000707018401101030210941002d03b800c006c0400f0311180c04d41d003c038248003501080d80814001c0c24080241e004040c40c000c05940000c00a401c00c200707100100f907011101e294441d03003240f17805c3c5c06640b00802151107442090504220320240b940350301c41186040d0000c6004000a508695500303e800c2031002c101d1061440040c4a030508600800c200720030003000790a040d407030b07007800910905600042070030090444100c071441d0161004010280180b840380d22007500c4055031440c20030740603080b0b89a0364854070b46900d00d0340096100180c2159030b081d08541c080c5c81e0b660305980e104c503618840302e4515256401061440c415110002c10140d60000780c4610954 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 254738758 1250 254737508 254737517
    0x30f04290a06060e030a060c02010209060d05040606060c0209130f0b340c03080c090a030c030c060804030509090402030717030c010b0f0604030312110310091a010905220501090203010602070e01030201 88
    0x1906d950f1010010915000e070f400075950203004400c0c07180d481c03001520b15130340c8000001c14a071419152600407190f01e604a8014800c440e480c1401580742d0170ba5140e80b043c8081480c0d5400325190074445054070007104001c0c4001c0d94403003009881c80f00252200703590715182141c81c0d003d1081034034241412000f020b1107070008003034104003004030303101d100301640105030b03102c040d46403205a101062480e1016041501c0f800c0303c0d00020400c020149800b5402031070940741107213042c02d240e6001130486c030845c4500b0384140a44c0c3c010400f595014400803008201c00b02081e103d503d040c80a072500d0340c01090340c055555280080c010726a05003c402c16850340c0c0028412071034541550340c19514000d030304500844007640e502d500e544141c2034000460280c1002c00c0c209440310314104011303040c1c07884480100c2c1e0031804000c0b60245660001c44503020b83c0c0040303455a5080c0e901c0381e07d032200700620940800340b07a420800006001a016030045040e0754080d802d403100710b5140c84400c07030014070a100080c0040d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 254740008 1250 254738758 254738773
    0xb010807030f110f0a1107030c120228080d020a05031b03042304230403110114100608060603011a030402060f030a1a15030f04290a06060e03 62
    0x310311950040c8a07010801800056800e0354403000740c1c044e08582c8140c1c01038100050808599a00201c4000440840c036000308445402c41c0d48540340b40e6040d20039180b00102d5402030204650b03800585c1410121003040da801002d403440c0c803940ea43c43d1540300b600164000c1400c40209984040b8400c100d07070307030840021071608010b9185003520804410707901d80036000500c408500f8000711404101030742d400f01d413a2800c0044003c100011980000c011100480742d503601000c111001180403a070140d01400e228445000620089015003291000e046510b40b5500400552855001c80035040c0c8040365100302a554812040c0307c0140301c01e006554080103e00c5081507056010f03802190710078409003080d0704050180d010351145400a6030700a0a0039140c040e802008512610164040364040710342440d008601d4070138840c14440900220400b410120002d424030801d0094003075415180c420002c1d1341a11340122400c061003d4604114090400030006034440c459007030119103d2009014104c81d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 254741258 1250 254740008 254740021
    0x2040b070b06030118060c020601050901080c01110106121a0601080709030f150608011e150509040c260606040b01080c0901170c18060a0f11012714010b0108 69
    0x15540002c0442c0d80c959215422010b900515900d114030440c41108007141500d15094068249081604100d02a100e102d004000c4050002070055604a0030709203080811982442c141c094000713074220000c00c1170100038900410002035613102421000704880e001c191103040044032117420555920300007961440052000c5000c1142c12030445219503440c42004c041d11900c0019148981c0c4a1505a5511f0008010002d0780308100c018503650104108152000d1911416411100b802000c1c001c5900c0c10005040040e0410103101801100d10140402c40940142c420300303408101d0020298040c030cd000c03d40c1c03810315000b0118403200503114441079546101024600350040761901e07040008008603030924070490400c25018601d00060300f80e58052110a6802d40a07090100c240030b84d008106080415501002c49904040b891500c1140790a44018150241000e080b02e88045440c06032002e1240c1c1c204410745030903e103d403950100c0c0c0c98048034558200e070007290740710b4040341088000509 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 254742508 1250 254741258 254741273
    0xe250903030935101409010b01090501051903060b07081e160b0405011b020105060f0604180e0a0c08012007030807050309030409060803030703150609030818090a150902040b07 77
    0x1510004101104d03814529400002e0684c0d04a1070350501d42001d00b018410460028010b00c03c42040030709124142d185450002003080c4101e9903202c00d42c00c0b0300798007840840d210f6081400100020306080d6152a01d46c14610819804020740041c403414040543c0e030300004071010745682c410112030180c0e400340c00742c4400000f800c004000f100e195581d014000b2031480c4002c0d00d80d076060066800004c0324034112040c4003031034080d10396081c401e190501007003014011070f0000c00c4c009079983c0b1000c01c2d100140c00d0210700d07000c0c96081c001c005600360b0101143c04030b4150b001d074030155110110050f40d0051451500707298801d504d005000910203900240c9554000c0004641007180001220301d4165903100c070b002143d020ba0040d040582000042c444001e601d070264100900c4010302c02600140740c940701605200c51480000c08402000c64401c0320b03500e15841301180326201070320aa000c1c1c548441c040740240781080c400e41812980c054080340d80d8406200341c8060321000d41125280400b00e0319105d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 254743758 1250 254742508 254742599
    0x14070906050703030914070303020c030c031b010e15090a0501030c300c03090b06040605091305010906110a030f111b0f03190906180e2509030309 64
    0x3d082c5174881a040340041c400c0402c54410280d00c00140460900310701c0c00a041c1800007000c0d5109512614a4081503600440c7c80700c2d0114103048203c01080d840001a200c07000c03040010350b4429000305045450000701030003000c062004407446a89141c48c0c0005500b00e1701310071000c4000440781003001c50f20900d50300b5064542c0060180342070101107442d181900765400c2c241c8040c0040c0d20303a03011038104000c07141c045800950880f0144200c60408000c21000341e0024143c65a0401241000c024441d007944240032085c0c005205010410454851401503403211803400002883e020f1124800100c3c1e1040c2000560080d01851625014030b0080288017100740b8102d180b03000d0003141403841941080144000110400c000421010030034000e014000c05610440a0083d04009011042900a40c1c0340503200502c11070003483d29441c0c00707046000b003094a21003081c0700d140d00701803115030061100c40450344203685e441003180c1c031501c02d285040f480303122a9203844040248000414031589691 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 254745008 1250 254743758 254743763
    0x706050c340c0f030209010906080a3f1214070f03020904091109010f0506040905040f06060b09040f0e060114360604020a0804110109030506010308030901140709060507 74
    0x1080114a2a162030100c03801039401480e81c2c3d030310305200300118104900038a0041c40035074020003220f07107880301003601c9441c5040b004200608522807408810288070070300c1c071010412801442c001120610b2051a254200103160200d40d624800c02c016844070f0280002c0340380b1000e44080780c1e868070882514100307510b5107501c2c14190240202c1c0c01503201e0b813044d80040f0340645804054540316030244600c2d4001a0000490411414001d11940e01d446007110100c48942c10300042540d1142450200d09a000e40000d00300b40c01c5c50f6000410a030200054a080801241c0030014007801014840071152001d010800a82005004000c00042d00d80c442d04007a901502059000610960a00c2e25100f403e0884c09005407400484610320300e083ca4075540424269400c61400b8014403020306143e10040c0020031000c800700d45000c2e5a48100c5800e8004c6500102316061940c40341b811005540046804107415031807e080b004e5a5045001c3c0940581d100d0346a12070300070b00b07210341200c0640c80494103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 254746258 1250 254745008 254745097
    0x31b06160e06040e041a1b04030b070903050102070605010806060d17130e100602010b0d02180402060912010f24030b0403030b060d0902010e0901210c030b0c0706050c 73
    0xc054454000145c070541c481c644640198512240c01041e55101074401c1d082d00c4a00084110060069003c840c21380350011600c0d50b15680b42c00040312081e5280d040107100354000f1522000704102c5400460580700d01c0300c15121659640c0c2e0034010b84000f50a00501740e52100c1070600d00d910b59540041c4009065a55a070345000d458008201002c0002d1783c040c40040c04005080001c4c1d5828800c02c134180c0e40444601100340d03441c2c1c00003483e4400301e4902c03035154030034070022508640e1303190300302d80066202030000b0074106416071045000f042001c0381908185c0c00c068a0b1580744000c0201c0c0303980408564050b070461804c4d0340340d503011a000200301301d06159550150340100d03034661001c1c5c00c50014160011881050702e1000600807080c4910a41c000c50320300d00180290301d005032198031603040b144442080c865107414003a900284c82d52000e414040d40c0401d201920a04c4002040801c0c058101404541c440340d500102c107106180d0203422049840c0c00d44d8680703a620800e00c1551080c1e0511 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 254747508 1250 254746258 254746267
    0x1d0a0b03041b032d0b0105100c0219050910080d05030a0b03120a030c0e010203190201020f120f090604050d08091c0906110712020d030507080c031b06160e06 69
    0x464503400100f07400c1580d02c403e240b05005003000640c007404011030740034504142e13110065036510701c0e185030600803640304ea0070301b0402107103c2d03105420f2480100e4004240600c8038406001c0050103180900505000f00750001c0081c0b0005406032950b8101c0300307040300078040420005000c8500742c00c0036001c84000e644030081003120780d4041004102e00d2144628031961a00311001c05070131650703182d250074144030360050440c000b070fa0003005444058209010a150391000705000f00c0c020f201e07070510700c0546800400c0307600d00c00361200e1741c0610404840d0301040180c0c03100a02503680d010f0454000b0300d298044c4e203000030114414041580c0113014801141d09008184c10b03900081c094480d00c050024110340d200700000d03640008140b560341901000381c8075280c10f144010140700c50b8104007901642c5121008001c240c4904101d860468020280f20b8594405e00c1829840780e0050314103d91030007201e4141c42d8081e80100f01580078000d40030481036081c40c005015038030510750483d501d80c40700b020310 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 254748758 1250 254747508 254747543
    0xa09020604091401140904050d11030d02030c03090d110706051c090b06030c040e0a060e0f03040801020403021e130b06040b0c0102041d0103020108010b03090a060614011d0a0b0304 79
    0x140034940341141480c0c80d815810804a40303007103540110102c0c0303d106c0500511000c1500417801c44481051031a000d245205070000003440c0d4030a094030344603698030000030030000032790340b10256018005941c142d555a52008400b2076450020340050790842d003040904000304c0b07003e600101740982c000c90581c606c00340f01d15600c50440700340c02d0040d01c6135204402048103625040c8081c004801c0101d60400464045002842d954801000e0050400d80c0d145031005003e42d003000a1400c403103208084035a81c0e038599000c40d0203504680700c07c0f80190803107040052040381100c402c242d00b030806087ca401c401b102035903d00c06420454030450700024100030101c0c096946d00020410280064005a540c618000030540c001203140c2c01045414140380c01400140c1c2d000703d030241110f24100c00203031aa26201001c0b410a084e041c4000c00003443c0603000079130026484403c06374202c0c2600c0e0402842c4030109013080229040141641c00b0799020300912032801c1200186400c00d000c1d14a003c868403118 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 254750008 1250 254748758 254748761
    0x1701060504182307090e0f060405100c0f1b17040605070b01080c0d03110f0706030c1d220b060d0608070909080304020114070f0b190905060a0902060409 67
    0x120700140c0e01c0b0640e05203420502158242100301c1c4100201d260800c1c100d000e072010f454549902903400410707260b454106e0501c9003084400180d040480c00d40d02c81d400d05d8680b82c0d654803081071039601c01c079007410303003100c0558040c0300c80c0071700c01030291500e01c0d04000d041c0b285005903814100403145650a0f04508429041c020083c1c4040c01c2941c94440e031701c8200c3c0c241460900380581c0201e2003548001c00c0141c0d142c8a54981c00d0089515040070002411102d03d4982080c030311440c0100e1511502a0004070b0b04c1d030580014941c200c2d10348401e000141d41c0044084d40c041d05240d00b90f001400150516444406650300000c00c91030702100080c0f180c4c5190000704217a1023034101c1c070141500c4620030300644005009500041211020400c0550850303900d07542d80380001480641402005481051980800c9044444c1503500c08241c5072019828078100e20045400d940c454404941d001d49200d416465200321701d180c540003030050480d9620303825141c020340711490040340c1103002404005442c030703440d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 254751258 1250 254750008 254750021
    0xc0607270f151e03051503030708070602030c0c011803030b030105090d11010f05271f0f02090603042114040b1303080a08010e071704020f0619020f061e011701060504 73
    0x70b540c0102e0302d4204407011020700301280e1b90b06480f81d082040800c000030101c01c1158080c542c4003c000d600e0b6655140d80b65124000c07010702134055400c043c101c0784109804a245d40007a07201792810070440e00c0c1c200605003207031030031100140f00768003a05020860354010008482401d1001001240e8004205070f04401d131002030355095180c0001249240280b50f002c1040044141c01c0802401c04503840c2c07111300c0c034180090f031100307422640d078107a590ba14040c0d680469819402c09044a41e8a0070503207018028401201c0045000903482d9000382c40781d510443c07081c2000c140c030289107420241004d03070140990380140c03800208039000200003c0000c800308041d01c440941501d0340071240d0b140c0715044040e000014220002c00120100080d09500402c81640d006601607400300b54010070600400c0e658070511500201062500000c622131130382c001015441600305034166210364071259026030001e03400000e01300c2090081401400150512803030140840c1c00600046801655035000c64110b500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 254752508 1250 254751258 254751317
    0x60206071835011109030607050307050304060209010c0c0303120f020306010212091903030216081f05070c080408072c0f09030405130605030c010f080a0902060c0607270f15 76
    0x400b0801c903203031b0f1070705006059200002c0e0920074030394940f10200400038400240001c6c001c0740d010800440b203074420032030030507141e80c85165029140d859003000340c04090356071a445105818140c40394904500750096900820701030300101a00c054501120b41303a0f0300002e0341c10b07412030105e00100030b082807080155030055000b0307001b600c03400b1a0821000d64921103034110000030740c84420b4190040c209814550000c61540000140549a0b000110f0320780301282c0e400340810034042030110710207101142030800c544124045d0060100114640030301c4008202411284c42000070020f400d030301c0c04203d56035100b04407074140c030710701903c0f4800982c01014550150845035901ca00c10300c9541010414265400001d0a0580a1030100c0304020708000300141503150007a2120f401500f1500d80300140d4ac1e9202c6154183d64852518480c01800307401200003000304000500034a01c41e2451400c65281070300c1c00c441078030040a0424840c082000c1c1039545074000c0003460703000810700400d400c4034120303000c0717 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 254753758 1250 254752508 254752541
    0xc0c170a05032109190206070305120406060f051804061119090906080c15360a06051c090305190c11030d020705040b030a020a06020607183501 63
    0x28207680452000340000d10100d1303a6032100c0c26002582e0511703c05403c0b40c1c5e43c12122070796910500e29084485001701000392042e441c0d06424441040015000f08080d105400c10a030704203a520020407068480c0b5207401160003256401280100f002c4e50000e26210740400b03401841d044170340d4034042031040450a00000684201402e0204d10304c180910001441260014030700c1280e80000038036000030002003090510300c001180300f0f101d00300103810b541034a19600c030745010f510000c0e00b0303002d4040d9070300f032051041034401800703d122070080301501d18401d003800b040008803100c048100002c004c1400e00b0750034023400780100080303100d4040940082107060f944581c02e0000e02e00d008607142e4005500c0b135200c2e0304580d2103005074660008403517044410403140801c0e00e10241d00401e091070080c08019400105419012440b80c0e0002942402502c0c6c5a036218400001014240041d2495000345400c003e00c1101a01c4460f4000350456901014103026078485031003c00307c1d41c21544e40c05589042c85 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 254755008 1250 254753758 254753797
    0xc0315060905010f05102706050706060f0609090c0c0c090c0f030209240904060b1305030120071b090603140105011410020109080d0204080d0c0c170a0503 68
    0xa070580d000712070040030701100402d00c003400c000c00149450703651580c0780c0030800100003090301401081d41485ca1640708182155035941ca8000044c80c0e6405004251000c0d0b04150000482581044600782155516542c00040702c1c02d180340307080907150f00c0d25140100000c1148103c003142035440b24400030007230414000b0300c01110240192a240c00103469070f050500c144100000343e211044140c8412140b809124900d0035002200002c50103900195504a443e00001040c101c881c10003c1c61286651860641c607260780d8800c041c00e984126a19a610310502c4407040c206811050141903228400c90038400701c0340c41140390704052316180d030005480507141c0d2000c00500200c4508071011100d06802401192b042401c2c215401c01d101d92180d000346240702d22240081c0c800e40c44405c0d074981c807417056961384050295503006034019004030f840314012460302c1b48050b8041c0c102c00c84025401500d004a080c034000008642082040d0315155601900690070002403082c0014482c40c003850083c00300a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 254756258 1250 254755008 254755019
    0x1110403031205010f050f03010608100203061f02030711010516080a200a030e0613080d121505060306030a050f0a0b0105030d050d050a0b03060405060f150109030f0c031506 76
    0x781c2c0000e8822400b00e510305001441101150b1100b901511410303600c2041d40d940d014042401231245034400e00d0310380541000f514010009400a40c05082d00b103400c6280207503001c8103170755014081d00301344000da4410021440080c1500308001208081410120300781907070346074140a00385147c0c40403601d0950018a40705103c1c0c205c0b01400d03480f150300300024102055005510b581e0642042c024003441580a00010141e445404a900c114644103095440c13a60b55000195900c9003c003041c5c0104c1c40240f40281900c02d60700c038a9103212420307062900d42c0381c0762030140021944007034401074240c01341c2000040881c000304640d60f902d036034500040c0340080c120304103c01a694181c1001e4403a070000d101d600c545951040550715020301c04100050161200000503004041810030b45405004490400041c480b0204403941325440e41030440c820f95488400b041c83c1111110240342c0401c503a1b290501c041004400d0301d094041c441c000381e0076055102c0d20350515046800081c5c081040e104c0b6001d008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 254757508 1250 254756258 254756267
    0x120303090d020f0d170a0216060603061406100c030207050d08041509080304030b061f080604050a0b03070315060306110a020c0418420501080f070b0304140111040303 73
    0x850111840103400d410030f51401c01845d0702c841d0345071007100d1184000482c02d8250261f0440c1c2d10000325503c0c0e4440c0c441c0a1820001030880ca20007920074600c0c041c0a080d00c028140c43c3c041c4242c3c002400d500c0c11400c08601035401208410003038007184507250000c50241c6034014040c0c4103e0003018441d0f2200e01d013115100541210904210402c24030050030003c46000105541c15243d00c0ba801007500e030344040c00700704010703040000541c01c66510b5404000150304220058002c00c81a18144000c0d5280007040303056034000b40c0751580551160300e0030000700f00d00c0a03a40305280c59501d4007240f03030b80d036984510f0144c508100003801d1004e0009041c020264040200648501080e40e041c400c01c1c0074940800c000c1d10a03410b002d04240741a1001c95406c08a021b41420381d032041646070714510082c0000d40f8403d40d40e074480c90711680d28240010a5040340040e0041c05118408004c20020f41804865121070304003030f204170b070003d0000201074031100080c0902103003081100409a11540341d401d0051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 254758758 1250 254757508 254757523
    0x4150c0306030c12020604061209170a02100e2a030105010e07020607113403151401030803071107030f03210e1e0309090a0b120706020c0d02120303090d02 68
    0x42c1d868140d2184200146c4409094074100d40d010306201c0c121684d0b841404d00a082c09202c01403107460320241c00c903000e100c104043c08041c00316908840320798004204600480707072241c0312180b00c3c0d4400c0c9000201d031588450440300e140f03041100195030240340c0000c170b0f0a496081c1c01071074408888a0401c0f140c0c0d41d0401c002a44001d140ca00300e000789000032a40c5440b0b04142c00122405000140555402c000582541034a2441c0c18000341138203039203040002203a0402504005040e00b0000c1404c4400807030443e10b41a241c2200f00645103448442090780d21074450300300309903240201103000000c500310140c59440c1c0da010f0b071610070f504024029000f80c140c150042e02c044241c9485c001305404000015a8021341e442800e04200542d042d10803980396000d50340001d6408440e82d01086000314803500700e150f060400369024940c49080a2060362075034410b00422006030301040080089142940c0d50300c0e50300d4005403900d1030410f046007010341560f0040360000700c01d50100e1051801c0c180d04214a2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 254760008 1250 254758758 254758769
    0x901020607020d0807081b070501150f0f0506250b04050607031407080601090807081c08010612050417030f0412090b0f0c1c090305070e0c0d0504150c0306030c 70
    0x2c084480000c3c00241c11001e02801540c104100d91000602c03054107400c204025060f6485c0e040c1d212086454258064900040c0c0000207145140300000d44a440305070810a0310805e06440307001c01e0820341480396035000405801c03180c800700f22081e049903094140c08255680100041403051616003441c9142090141c13444041600d86442340c40b0501d02c0b0341003980c01c41d9291416a00c56150500101c07020b12844e000f81d40c69000b800c40c00035000d0700c001500d480c1c00418221320020029007041c143c6021509115260104440003845034105110368000d0364402e104039100001c203140041c05809a8104032100d01449021000703001c107015600d11020b45034101464150002ca0820420010600903c612080b2110000c5000c060b144404e014030300c0c0e810380b0101e2301205a0038610703008280d9802403000f51428010b81401268005916a4143c0b1a20f00d034900e8a20700300b180d00b0501c00070b0900500c180e0310306040c0105240000300c0b40c00740703084070b17203050f50003181302c0b4210306260580e0441503006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 254761258 1250 254760008 254760013
    0x9080d02031b0a1731170a050609010e061303021f1404080406081503030d0902030a020d0c0608010906050306180c03100b03100207021309050a0803040308011409060a051e1203090102060702 83
    0x401d5603062203603c1020660791203aa0042c1b48014040d201880d103502170000078160b00440042214103007056100f49800800c1d40100e80140c0c448040c020140b107443c980240050f0445000f02e1105100b81e00d00240c0c1180072800006da150341c252204003036003c10b80c0c04035a1700f0000101040966402240540c110440380c59100c0b04003000c4001a5032486800461140a900c58503c4002e5581c280519440150054a034842004c0945440002481d580c007400001c1038150001180d020807034400c40e010703104007400900f10f030303100c0403882400444d480311044528451035141e50340c543c030706000d45841100003800c08a0399200c008105810854003400070a00c03507105000c000c0140e80c0d03400d8928180b51683c071000508040130704056040c18886d0300e02920600000017400101503000400d0b0741210040e15075180c00903064020416402000e6610b140c0c07201c85d908050056107000b0900d154a603404521440c0f40030542d0b400320321010300024040c1c1698101140340551942c050005542c0300e15284003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 254762508 1250 254761258 254761327
    0x2040f080f0601030605070504170705041d0a02061309020d05010612020a020a0b0a140108031201090501052d030f071503060506030a0e030f120709080d02031b0a17 72
    0x7501d03a0b181c0d81480094152601e500108004a00502c1118040c141d000c1c00c243c103114003100941c0d612121413060902031031603c86c0d44d00b1020b01804181566840a802400c030a0406800308040d5400c9104c9111380802c00e5180003626001038801807004007103081020a096150110246c4480100da081c107a11030b00400420040719070204894403926405800302d50241c9859200750000e00b010003401c01218840300000c181c1751400009040390880e200d400c100280c1e02c84003000140c0314207108441d0400340b00c1201e625460300ca080301620707403901c243c9140944441440041e280020281520f20541c0181c18280300001120080701c415440030305080c0500c62800010907200e00c8000d280903a1030b80e4034044000403080910444420f0540c0d0b454658a400c20031420560b01c090a8420701c0c00303c1d0007010006611107002c5078201c01c0e078001d0b402a50034403800d4024400b0340301b00d04c07400d80d4090040c001039500003800a2a6036910020341d0180c59241c1619805006415184e000c4a00506000c000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 254763758 1250 254762508 254762533
    0x30c0915050d0f0f0501030f110f0a050f0310061403010e010b090402220903030b0f03072d080d02030a0f05070c03030e03010213031b060e0d0201140403080d02040f08 73
    0x1298014590b601000038042e044201e08401000b4070039100300440c1c20040000140f041c4800c40011180c0250810030f40000c1d00410040c0514240103140d801001c0b018003080b9030b10f0b150000c0c035103c00011341554200b000f41a1028110b0341ca41e001a540304602610101c0c076070401344248005030841c0d8008100480580000400803400100024420003032031070200c0c590f07188605500030700709c81c00f41d050080081c2450701030301030000c1180c6075008181080c944c4905140c0028030408845031842c4291040b4011901400c0c0c0034a00074050452001080001800704020003c01c0e42e040010f0703000d943c442e9010540100b460800041d03d0080184c1030011a000c11100c40348801103d9050034a40244882031010034003a021300300c02c420688174003003000810320007404142811540f21030100c0207000d84544003540c080c21030811030794000700220200d03030065008864440581c0340d00d000860501d9607a540d5030321542c2c44020b104c60816001b00d0100000701003020b200c005024810302034003802d01c420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 254765008 1250 254763758 254763767
    0x50f0d0903050a26040b04050f0103050f1504021c020c19030801050409111c0203010b0406030f1e0203060a09110a05010f0f110f0106050906121b010e0907030c0915 72
    0x2410103440201410b1340428030051285144244040c904141e0380c4490352070242121036000791183c28080d170200188001d10750710a00c1410703c901030800350384c2202e46a8055010002c6110951741d500300703030301300302d111514550200c00d51804034050002594580c4072008840c2048064901096000f0480301c1c8940002c0c2c2290042d410b540090f00c00191900b05424001480e050641400d504a1008900c0d181080d040501c5401414026802440a00444024081265100c1c48050007000c9441000c000007100035184a0484401c0b036818102184a5000030b42044408c3d2540210180d03903400b03407003c2241554403100c0c0c101089944007900c40c034003400030b015044500294800c02041e2340d0000621402414200d00c1011030714122843c40b4040551230b0b000b4031803030180c14420500f440002d42c80f464000484c020b0045968054101007080510010550b480c1c0c170390720b9040c4025080c0d620b2468841e440700511a4000d40d8001c01d820441481c081c290700916000002e00d035041c41c50008285402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 254766258 1250 254765008 254765023
    0x209120109060b0a12171908060307060207060516020d02041e05010b03161206180f050f04050a020d0f21030506030c01020c0f1306080606190e060904060e0109050f0d090305 76
    0x102840b04000d840d901d070051107500c5688032440421f0154160800420740c031504542c402d0a040c1c0c111b403680da40750407050740c3c1c0d145148900c10008008200400100e146844120f0b880c0d071024014011300c2e0480d81c0003400b952540840c2c0d0b200050080f088004003246070080900620038101140e04d182489a074003044c4941070b031074400622081d07810025950b50a6441840103000d01214240f1102c040d12048010309404040b0344c0c0014181004500141d007002c46d03150055510000030250810541d090080d5803030004c1094440078030250303404000c83c1c000704428800440c2582d040031031202154001e41141c00140510f4001d0b841074404656990b00050304600c902011940450809060b00010b00b41243d12194401800d04241c4002128040021003501075041141c4444c51807840d44062001d600242c460611070f0726114020600a09100c0c01464101d8026500442d50300800d500c21405c1d90002c0608607500d13030040c00c6c080401501403081601482061a0605601d480c548905603aa01d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 254767508 1250 254766258 254766263
    0x90b01082d12220b03070906030b0a03060c05281e08010e090109080c0c010e0628110102070b0a0507050c060c0a050c0709090201120203040506190209120109060b0a12 73
    0x40c80320b1004001801c1e0b802007203600002116080c1c0c0744c038010302c1e5981040d1940c0012408140c404104140280074416003013001a011140c11480c54807494007400038600c1e4641401001c02510980d4030301304500c0c1d60682c030090f44038800d41c8918207004110300025041e07800049000c03003189200f96400b440041c115141e081d01d2680c2603d51008060041c101c00c0c400400d84be00010b06040103d6010030b00100b404800d80b01e400740441c50101740701091044803011700c0f40300a8283c80a02d1750344030680400081c8814a808001e040126141c1c60882c0d10900094501a108004024100e0102e0003000d5004140307140c80e0381403400c083c0c030195440c180540004800400494030403680c42c0302c0c40c15144240c8907030085a8501c5c0d82c4060400c0145403020003640000d14640c0c0c808100003003070003141e01a5500100904c040d0b6120001c92039061902d5080220050302040b0b9048036a592b0040701190782490000010401c06600d1703e0000c50f40b003039601d940901581c0304c0422400c08600c501060307054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 254768758 1250 254767508 254767543
    0x70c1a160302030f040e09010f020301050d12031107061a040605013203190f09080d0902010207090e0304060207051e060a051213120e09010b0d090b01082d 68
    0x30361a2400703a045004400788840c030440701043c0003400c112042c00650140304914000c0203d10301a0b2010400d91200b402400d40040d0345071444c000040d0740303920300c1c400d401c0d10785000500b0303a8100101c91030744ea00c442e10a544080e120704100054008280300f0b00980b20040300c04028142c6080c0019100202d8582e240c401002c9010b0400749600d0342301d21000100b000340e0821907481c46d194000341d06003110f880400380745520f81000300d0700aa00501c900d030750f03040d0011205400c3c4000800580003402c0c07404412411802220740000f070301e084900030910021440d1019544807410101c1c001e282010300e80c040d0340700b80020800404c0d1600c0500c80c0841c0c0c402c06555041da0740f0410f2000359100d00c9541c944c1b402c80c105e014100b000c1c84200c41c12407003200d441031101441410702401c0440d14010100a46070703001100a00400461141e040203005040801001083c00d04160b15080c60f0300300c09070300c440601e40040d541640c0e050307490360000404102507240c124404452000183e540d0380791600d142d1544 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 254770008 1250 254768758 254768797
    0x70914010507150504030207030c0906060c11041b1e0e060703050309120a02030409051f050103020c160807081c05030619030501020705010c080606041202060f0c0601060203070c1a 79
    0x40504458580d080e12404800d104c9800c103440e0080d1707100c1441c401035603a11031448000c5201a164060002187d44694840302c01481540351030902006001c03c460740181d403140007050b00d000e640c44030b05140049071078003240c0c0c44e070843c0d0700744a504840c0d281e40c04209595403114499517130780382581c07005078052610750f03203907510b01c00141c0c982911407981c40c000600100d130441d03119500200502c01c0e02c1e025203061100b42c0320102c0700e40b04060b0401e009901508003042c01c0c0082d5109501800a0000e0003088600110200e0120f0b940040141c000d0381071900319480500590b1000c01c0f01030900d66000d00808801c0c001030100420a00000d004948210100d684002c0f45031b00300c520b2440611341020003113603580b4040c500b0a000302144c407d40070200c3c03c900005441840d080c3c0075281195030401e030b00d0f5030440b1a5820406264404190310b010307031106000e54414a842080040c1c080c0159400460f40c45ca02c074203240c16010259444181e0321341004001615040c4030000350742c240d030149903003082d51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 254771258 1250 254770008 254770013
    0x609060c0b100b12150105070f061a04110408010513050a0b060609040c0e010e0102030c10090602070c030f20180601110d02010f0b040504031413030209070314070914010507 76
    0x42c03034801e511a610010740480c183e5000f503000003d02c0c0c011990080384131074024029005403814092404090072188800040401090aa800001c4054960b02c40c140101501c500000d08a502c800109002d000c4042010b2042520074440c0a80191002d0650702400c01180d84044d5074090030940200480e40800c08603096071691010780342d8100d001401400541e146410040460740c0e0503017003e001458014036828254004400c40302d0410142015002d5140256680c07806003071020300403501c0a608201c0c20011030342038403281c0061171081c030440c0c01103a1075003010941d0301c0f4003070b00c40c04110580d94070100b010350b0f840101501500314038144140e00c0e0307682401665484407001601c0000d004001100003400c1d4107602c030080c03000b2910410040d402c1c6500030300045800c11035008001c078101600100910347e075a000303003540c02100f80d400c140c80c41d01d035404a00311004c15652800401d4941e03c007109044030031401c45600140516003080f802d450204040c4610780d113403100c1814088001840000e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 254772508 1250 254771258 254771281
    0x8190206070c030503030f16110721080c0303040302070e0606071101180e060a1d0a1104150201050f18070302010809100e0d14040b0306060d0b1c0c0609060c0b 70
    0x110f130402e0941e40c0721700d84038428a005034801c5990b040303a0368207a6071001c0800d000300112008070700001c0c01401c205080601c8444128154029443c094075642d00c0340e4005400000108020820362000d0f54885c1814a40070f403500d130258102d80511007001081025a486001c2500d034101c2d08009000a10300c100d90040e0340003025036410900c00000281c1c04640d6a28040e070f02c138090041910f402c00d0240e42d503010072901c07a480b0b5100c42042441ca502089002841d0b0300a0400b90112302030003881e0a9460407041d040200c44102c03070b030240c0d440f08104500e080d084c0207a2070784840c06048071030000d0348042440743c4541039400000d0500c0420380101c0d40015041102500c3d0941c981c404000400000c61103d5981c82072009640004008a0b1549007040c1c10f2010744007192210768009013551242e84c20048213402c24400300314860760755055844244c1e40c1c101d0482809d009551031130501c2503d8100001400a030b9000102480100350040090310780c40007258046a070070a10540007600c0f000821803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 254773758 1250 254772508 254772533
    0x90603060a032f03010b06041205030f07050f010c0c02030a120302040b0a030e1b0306010b0c2404020f01030c0504060302070203011b020303070801080118081308030a05090a0819020607 81
    0x34640f40d00030350000d01103202c007100364551154000403840d10030204410942640e010030400364100744240001c0000e545040c20b444201803052041c4c0c0d08001c086100000341d07810142050b82e2681c091600c1d007500e10800c0c03150950200c900d02d04840c650410350046950307214014402000401340b03c3c890641140300c7d9040e1800760a0030f1150590714041c844d4000c01030007c1400030460f901601da641e000284050400301102c50b00a40600301031303864500e1401a94011280c400484c0c0a541d40c0314541460b90610400f000040981005203170a02c0d0040c48515440b110044c0e05052900e03061400840d0441c1c11740e021900d55103000f5a680c240d0f0710129002d818025140305a4035a6040011100c5401001440c071503140b958403d070060384e803440142d003a2a040c040c1d55030616029000580800c1240300100000d121070600b03002419580d401c22803450740a0300c0850f000a1001ca08040c4a1600c24840802801307400d00500c524001c1c01440c00821a181d80002d11402000500344c0801c4400c06288 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 254775008 1250 254773758 254773763
    0x210e011e050d060f06022a1c1707030917060c19020304030c0909021320030405010209090c091915111f060f121106130807030516120305090603060a03 66
    0x14004d4980d00c03c2c011359a90348034000040c3e5407541001c01d03041020481a0f000a401c0020148030030821541c00307018018543c9101902d8030f0841c41030000306280c80b08002d08009200e5a210110540383c071040c0c0752040343c19560f40645030410707000c4c0701c000381714003094400080b102c0c1c038403406404902d40d017070745144216840107140301030b045400035078000d031039124210550080e00d40c24039006500c21108202c5031159078401c9205011201251500c040202442c0c3c071910070400107140421000010b0301258003280d010001e5100000c5402d0301d41807031401c88010240400d94503075003608003034001d4a411140b1603020b080111921000b01d071560204250001d200c80c4c00c3c040200782080710040c601800b034a000d84c07002040c04520002d0107891500c1c28110054100301e00c81c600018660400449a004400700340c002c0e41400c0e0041640c05040c800c0b078001b91310680003844034079800356100e61601416401140344061000415000c2500a800c84680070803c5030210754a59820f030024001c407000e50400f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 254776258 1250 254775008 254775029
    0x20f0a09090c022509050910050903040303020304090911060c010f0c0c0b1308070803070801030611090f0906150c0a06050a0605030d12020409050c07051c120b0409210e011e050d06 79
    0xe1101f040d0303000c40d9907482c42510314010301c001e90707400190342d07030700d11407848010016031040008000000c0140d00446246d0321681d02585c1781d41c1c5110005c0c0c0503820505403103060703035507818620001d14030902c1403040c2c0c10414200490740a80342d8640d08500c810040c0300c00c00240b12000244100004076040310101684005251f450341410000188400b0342400100ea81c1841c214a40c07182d01e60300c2003581d4000f8401800b8900c2c280e180307401d11001d43c0300907140030f4004a50240e00f041c65600503003d080144840c100800340071a250801c0c00036240d02404104134070b03140100c00d2240340c030701150030164001c007420101405525500000000d120303542c41003050074944014050000c0036800180340e0640503000302e507860300c015001d0203180c40010b0030f19408144c2507a1081c01c0103480d40c2280d80150801407001a000f185901d62001c0d203000000140f40c0d010700c80c1c10011625401900141c10101c00b03203001e05c4c8515034000740380082401e16106600303103c00490710b41c10144982c0c01000107040080503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 254777508 1250 254776258 254776261
    0x3011e0e0c0910141302190f090311060a02070314030913060803030402061606050705030703150e15120d2a0308060925020318040213090c0909020f0a09090c02250905 73
    0x2201d4130030030b03600e01c010b100080001d8503e050a0f48109c80c0c40c8140d0b90044400c030207002040d02000010380c0705412240075802107050010100e07110308002404c8403a010091aa20368514081010f03481a506d001403c0d0b510300b20090052034030000540e03a008e80c0c1070311060b650341c03008445250b440d13030196002070406042074100682543c1c8900a5070051299031000c0c00001040e107600e02c06185030707003d00025043d10b140054211700c130908178100c1c1d0803405000422030040c00c0d07078900d042540850000340858241402d688201c20301e0140100070047e5440d88031151610340d50010419500541001e10455441000c6010500c540302d52016504080c109500303030074400320303000e9140e030400c2100281180f00d03d115180242841c0c02250044482101032542079400e0894000003000c0d180c4440341005400d01000ca4414010300c000d1400009500d14680c441244490040a0400a8004802d450f052401d031800054002900d1241850700f0300070010810808401c00310410080d03405005110708040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 254778758 1250 254777508 254777527
    0x31905190813120f030e0a02030c090a02040305031303050d1106151f320d0905070f09090b010b0f1204060b1c1109011a030603011e0e0c0910141302 65
    0x1c92001c1d40074507103080c043c40d10040306e4107403a401e0881c0e0194051b00318007420600d80c541110071980c84019114014105a141c0d11040c0ca580c000c0c0c00740d100107609000061080c0300302000f501500705131600d080b92141c2c0d210211141c80702005894020220b200b1008030010f903503220b0b01c11020489555520540c2c0351103000042c075206400c0040516014400981c02c100c2d0b00c40040100c0402503600300502d0011010704c0000105100d01c0c00740c406004218010684601690f80c1c0380c01030003500c80109035190103041c00141290103900013000d0600030000c406507101840c4c20390709021104c00d480403c607941da00b003a401521503290038a50156140a5010304a07801580e590b0303106025500050740c0040510031f01882207420300039400f1414441000800302c424140085500c90000350000c2602d400d21a12011110091501001003e84964500d40c06a0080003849060081220800c1b924101044008110480b60140320f4180518a080ca00d00da100e10200032102185800215030390304805 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 254780008 1250 254778758 254778767
    0x8070b0a03021b1e010b060708071103060f090708030306012721060b04020c12070c1203050a110a120c0501020721120b0102030a1d0406060203190519081312 69
    0x705002134403a081c8240074a4014414030916040010250025250407200d4a5041d03054020103003c890320708440c0d8660080340ca0902c4410b0040c01d45c01068242810015151800c140340c94115800f0381d4030a00410141e41c0c1d008900c00ba4050a80303d1401e0004140c010340b000035136440e0401540c29210000359500004010803424000340145c2c1c08214103841d410402c4140c0c450a5890b41495100f11090790304101800020030300c80e40300d80004402266110b18441d43c4032036643d41540420808140312074019046085d04c0c401c0b50f00d801c003400b5001101d44d00c1e1441d140007a805142004603214045081200035030440b40083c0d046003403503225400c1c4d050304212020403014140000340140c00300148800450040c54440501600614200740281004803007088800316110f0720003299000340080340e182d80c03091501502480c0d02031641c4002501c8081d56003520300340660304029040100d42183d070700c1c030081d50f80c1c00c12091405001d541c50302070b401016010481c1015061280c054100401243c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 254781258 1250 254780008 254780023
    0x1050d0e0c03071a0304060b0307150302070303240306022115040b0d030903081608070b0603060c1309020901020106081006030218090d031d030703020a021908070b0a03021b 76
    0x403011192410740f9000300d003122088004c0051000482400418000b039615001561001c2014040340c1c0c0450365030520100c2550b0042000c004641e001581c4028581c0c035014600450007525210382d2010540c1c9a03d0b00301d405244806803c00ba404100140c58031000c4080c1920040f1a1221403c50b04060101e07104c1e20655860703041c0315601c3c01c4080340050910788003445425815413a0304044920b55101c015a590280c084440180000d110140c00140d190014155907409885054030340d01d00303081490300d002c402501244201c0000c0c801203854994581346401501e015410250329070803a800103038003401c0503801071081c600548016120100c0c1c980e22040c200d034000c680c031022003c1d0640b003401104500380e13039024481c0c00014101c00c0aa0181d04480c526403841900300102a4140c8025411500051000c4006070442e603110420f51420211059100300c19002c48860b09251528260381c0d001750380b040940758080851020106406a070588105203035514102c6060004100c0300b9803138035207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 254782508 1250 254781258 254781283
    0x1180503120d15080d0c020301060b030a0b090601030b030d260403180504021303140a02060d0f0e0606030c010807020309040501090b030f1606051b0706050304120203070b070e01050d0e 81
    0x703081d003043c0c0c40e103c440071044112550403001d003650441c03907881100c850f45e1010050760159210000000e00710780c070b00000c0d40700e12140703200005d110390100e0801150785c1022307081034109824189820205d40e004036910001c00154105443d82403d080c2c600c101ca003a03074086640d0400340103000c2000b03054201d01990005200300317504910301d60b15402040b049001700000035070bc03903200c5001840010000140038225400807811100c103e0072990004030075520032840003010341d0300c1300c03099280c81815008004118003000068141d515210010035a43c243c0840c180e8104104000401c0465009104450755544064414007096840d4400203000e001d0b03910149009100750010000e003d000400c911088102000416441d140380503800c85040e00071301c00190f50b00b0700f82c01c01c540c0900e008000000041110780c8078035450b881d00b030a110002c6045a004401550030400c6140c000414104580d54800503500f4500030980d01100102c07014083c2030001d100091605c0344441004c10001003022081c503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 254783758 1250 254782508 254782511
    0xc15020d0506180408030c1803011508070602031809252303070804061e020408010605100507080406200109140d09060e04090602070209040803011a040b070201180503120d 75
    0x4224510410000c80f0441e00903040c001c0520105048560000003402200036000121b00c42d03039500070019084a55086440c0384540c120b543c00c004c40b000a0200e0b1006140a001a600707120564138540458000d50040300c3c0700e41d88240025580801c00400040d00354600c0103030302295401d034072000d08022101c0c024584560032560780c0052104141003224442e40b00c4d0f555034029a12655141e00c05072800e0780450280c3c0e00c070615403004000031840600004c1c400c54001081c001e01e400f0900818011804003d42000700802030742c40413540e07440031502101c0603440c22585805c22200c2058001c01c0c4081025815400c0c5440c110501010b581842c017480e40200588001044200096840c070816102e024046510000400707400c0c0340c1030b80401d401c18003803d00540341c070001d54002240c1c801d085a01b25400d00300440180108840c2c8184000206410700d0107a180c10b00b48030b26805203000e01c8000904001200081d010140200f80c0c0f080001d140c0a8111000c00311f1908104880f500280d0803001080d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 254785008 1250 254783758 254783779
    0x30204030615060e0f120a0320070302010507110a03020406030516060518040e0a0c06090623040b031e0901021210061e11030a03060510021605010c15020d0506 70
    0x4080e00b41c1c8508541d03003521440b15030b40c1e2040034004d291a101520580c0304403040c500c0e0101c00000e0003114880c600c2540e074170b00d50040d90702060901e02481b001441507540031900c1480140d2b0414110340c9180e0704507412133041190340c00052003101e04c13500000c0d00282804000400c210300081c903005038482c10303d185000303103850300c0d0304407183c1c007032103103000805090004001854101313903101440e0000d0361300c01c0c0ca1800c1d80d141c55120200c0c0d070583c02a400038404030020080c0507405080100b40d59042c0c3e482c2c0960780980401c140050090f07014140c48040001302103409440002842200b0140f24034240c1c41d80d10340380044034000c1d0040e15184d003143c088400043c024040c0102d14809507034040d1203c024026200c1d9215079a6605200b42d4014000c404d11100c1006008002a200c3c1401c0c80d0343c0030813024180814030212030700b11905001554800d00c5000b04e00c142c2e0524bc0e030309503182880d0014490549042c01003040a0081c8c1d01c0c5d840510008070f43c01c2003c4c4a8000038414041a1000c0c07500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 254786258 1250 254785008 254785031
    0x409140a09020918072c0714040611030715050a060f051e1504080a030e03010c080a1a0904122712030905031903140906091017070302040306 62
    0x5940207084002d40c400c50b0300340043c40801c0e002420740011980700045450b9282c0715054070144100d0500514941030f00003c0f41c00c041c3c040e5000180d80100c1524040d14003500f40540c1d0750440c0560301860003403152510b403600c4048010001d5690703041d080500100803840c40542d0034002c22060b01e905800d5800c10101055061005000008031703403001d003022207110742d00075a4094102c101c014046c5e01043c80c1b503076000300640300d82c094805070000c0340c0a4801d04501c0c1c64040c0c101032841c15090700990414202d03400c019003041085034002c80460010481005002c00f048071121040c070071a80c070600c1340c800c1c04103002501000805881c901d480381c00c01d0f0103a9032150485490301070440e48050010420031f100403c22071a41401c00340c0f09040c481ca070700751940002400c010034151008244040701d4140014194044190401c1540e05c3c0912840c0c002e201001c04c0146c460340346501d000d986645005e1911740c0c07040c0780c90314250510b48481c05031030034a00c0c030040c042d5003c2e100c203950260800041010303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 254787508 1250 254786258 254786261
    0x130e2505030109021503040501090f06020309210d050601200304080d02120708070c0e0a1b03060501092c09101b09090e01060807080f010e010911060309120409140a 72
    0x40b0f0a070010300c0c00070148030300300c5102d2031588010070032241d075500c0b01400c90000700c440c049190307524030408002d41c03a0700c1d059480074038011f8081002c42040d607448104880a052000484031b881d049482d000c6410b80d507160040c3c4101c03d02c1c80144d501002c0307102c80c0468950700440600280c913540010b540440c61050000c903030701c802d001c0c0082c00c5d66034104906000210300a004044482c45000d1007015030740e44400b0100aa24100d83c1240c1c0c8644640301089240c0c07070400e031804e2528640c02d040141e1403d280000308400c03854021480d60f0819242c821a50202c811703c59822501c0400100d200c520305000ca5540b5030584480f610100340c2040002c4180c5010344a0941e581000303075452481ea00d2410f145800540340c243c9440309a9540e0301d03800710b4041c905001c5c42002d02035a40045c01e2844c1041041c9003102c42101180710140d15064100c2c00003030740300c0c41c8175218542c00c030b520729120f88800700b9035130912004606051254400090005038184582c011200010810700c11071015a43e1004079070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 254788758 1250 254787508 254787521
    0x706060b071a1008010219080f040b070c020105121e011d070c110d0302010c0e03010203010b0f07030915090504050a05070e150706090f0501061d06130e25050301 71
    0x1000301e640305455074408104120902c0d40f00d45034a481c1c1e000b0540d00e00e8040e08a900240300001d550b01500c40043c00315800900c032580040442080c0c4107645130548840c4021036002c2c150400308100005488113581c803440c2078070f4042c14640e09043d064140103a07115002294043c00154520a0000026403440424926003401124061004044e03595a00403206100c80700c6007184e40c6880b50030445600e4481018650f9482e1182d0000500c40c22014005000c07640c0142005101703a004000504c01e5280000540311000206085540c840b2924941503603594010b030400368242080da200702e84840d80c0028250f040fa01c00352020452606c1d20140c2c1010381e181140e00e0000710700000109502401c02440411104411152090400546a44035000ea4004403000d6410001d17031940401880b40a1150701c000306014071071301c8854100c3d010141180280180345501c54080038188180004031900900d00180b5010142e0b100101c0064840c806030440d010150a881c518070030200d56405c052060a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 254790008 1250 254788758 254788763
    0x5070501020d1704030504031b0512120f0a0e13062c0f1008010c02010603060b011701061101110a0c0303060e011220031905060705120103060504051c050706060b07 72
    0x9022007510f202d41d0790062001d0011401c018003080000b010a0811494683d2510002500310b08189001c040044080c4a0b482c1001c2d2a044440c0c0d910058041c4000c4400e8000a503c616490352041e150070745070318507003003070340c5030010f02e65003844100b8000c80c1c1c0004265007100304005000401007004400605200d6416002da4110030080b070b000d240c0a4030243c0d4001502c42607041c205403507080c1c40f03007501c42104042004d42c1d119901402042107600449280350303c00c3c038020480c03411000b03650303d040c1010b10928080c0503803401107420700c507001e4100314190906288665901c02c0c006600500c014000c941c107800080c40e0100100f24040e40341d020074100e5002c6005030581402e540c5852802c0c0d8540801c0e02c580101040c625000c80c0c400344040002003d00c1d01e9030503007031320031424001c0c00c0c0303a4010404410007100300a00c01024900200d91810360760000d6000645681d6071a207240b81c501c0c1c40c000110101800c07408640c8940c5d00c20010305800f8401d09007031000c5503407030750090b100d8003030744000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 254791258 1250 254790008 254790017
    0x10090902060904020319020c0d02060109050702031209010b030d0509040b040903050316120510062601060f0e031506031011070f240609060608091c030b1c05070501020d 74
    0x1101c22450150041d5401c804146c501c6496007081c44115000c990000c4e5500305aa0040c0c0f01c034507140c64040c40035500520003030406002900d800c4c0030007500c0384284289500b42806103400309030100c0c07096000c01c0d00301c640681180c5480300303040310281064202e461031030300c594103100710401300d404c050103420403007981515180c1c210b45402410b8605401580c484004200c415505d041c0524103502649000d40310254000c98241d040c54001080010100c50042d004013900d06061091444030030014111356a030314007098207420380d50b030071100c01c0d81040300b4950503c030307480c0c070710004055200b490303400360300202e040703e16181041e0003190960701109a4061041d000f4032040f404190b18007030100e43c1070320034900d0614203404246401000181c9506846c00c0300d90b91203080c0301034402c1344103400241401381099409440c0160f44966500a0007a040b048078203c100e50040c1d80b030294204000004000745008805590fa407998401c0c07600c0204199868810b03101c0004465002041c0f4218130611982c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 254792508 1250 254791258 254791267
    0xc030b011e0c020306010f030201031401150e1809010f0621150e03030106030e0105060f131a04060303020a0b281104030611030702011b23160b1009090206 68
    0x201034400381c1006081040c000c07a0200900103135000c1c403100303010f06501c030340b07600f0400e0950000400300d4140d49024841a42c0e010010f0100310400c100100c50102c652034000e21074403465010401403201c3c0c1070415201c880c12824880b0303441040d00032000030741d881c0c00b0811555694010501803082c52694804800703200f50184804104030141d0788004190301c0c0d80100b0b240d19000c868a1442d4800d034000c80000390358040103043c0718000c2c00744c95000042140d00d4071901107603000050340182076140070f13510255214000b10701c08030a25070705000c0100080c070802003e507480c1006520345070444402c035044a407a000050346111480715410741500c2c140c131030301030f640b1030607069000a000c030800c81c4211810500001000940f07a003d221207041c00360031891b4903814082c4c2c01030b0a484000d014111650130a00c107039907002c1d60003100c9800d40441c1d004103021980583c10b40c4101445807203140280401502041801e000105407089e0092000d02c40d44c1002658550750002201ca460038000d512940811 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 254793758 1250 254792508 254792537
    0x51e1b04020c0106050306070f031103010501050d020a0306050a080a031e02030703200601060c050f0705030c04090f15050103120305040804090b0120160e1029040e01090c030b01 78
    0x1d01800d01c0900640000138555180c0001920b040b9040b43e08074002942407007620300442d418000c152102c10183e410310b08650600340080c1850281c05460513103d035000c12012079039480b94000500800000d000c4064075a191240c07107407225400c0405401240400481108482c041911440d01121542c0a141803c030940d0302220382e0681131a400c007081100424804980718240955802400f25451365483c13144603103050f40c1009070405a0100380d03005030038104140e4a0108081c15152400c0f00d0000b445803062400b642603001020026104200c2c00e009a5400740c1194000c0703043ea030180c80e1030324544c607900d407040f001da400c100c030014542131003400204803d40c42d0350005103c44030141064100e888149404440f200440803a813030803540412140190360b500310040c1c0002d07040b004010f0301e20340352840340070042c00841d200748c1c0d8050701400b40e020b61500201c505500200c03020382c002c540c1d0b141c0d2040c984000380f02c280100c42d4124506105444801d001784a501c810b9081a103c01030b50b004e019 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 254795008 1250 254793758 254793761
    0xf010804050703060c0f030b01030207050607080a0e1c0801050a080a1203061203030b19030b06060904020405031203071b020d1202010b0a0801090b0c04120b040f0b04051e1b04 77
    0x900308444520500c0400301c0064072600518650254503600c0340710a64110200a003602d00600340c66041c5441008054042280420b61951202607400c20030126211020313004003c14001031003120350b005505140490312803054410304011407956544686913240d200f04206204a44100002548100483c4d00041d100f81048803407003481d804c0000f4004d503140170180004003d04070490001e65100d103180d50074540440202c2160150742e1030f4051003404c565a0032007411000d060188a007c022445d0300b080e42d980d404960151030060701755054010304c41d030141016041524820081240065649000300041c0f00e0b81e11b0543e002029601801152b846030f10358060003000031130440d501d803202c0340c0e280c2d11840481c1c030041543e00000920b821290815001c07110000d000076101450030003041100c050301449030a00b035a0031010360b2016888900c0c0c2120000440e03075009020402c03c00c100700070301c070340807030b145c030030300d0006039607001d0032035800c01041e07202c45400c51000050304c10b52500c0103090429 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 254796258 1250 254795008 254795011
    0xa020a051902071203020a020a090203151e03030406080a0b0405060f0409030e12072111061c1103010305010b04091509020a0906091b030c080106050a0c0219080c0a050f0108 76
    0xd00660b450152507400980c0d181d800e0700304c01c2d409a44528144811410003207407200080200060450450911002920b00c2d079030940c074080d00c201d1080c8e10140c4400d12803801c2441110b00141282d0f035481c0c0d1040058540f42e0101d92241075546001503001c12401c2502a00344901c00041200c0b04103030081d0104801440d04e10419000c00c03107047c1c140c0c4000e44516003240c80820018008110725442c0c01d1f0000d0f40c03401c17005008403002980c00803000000c0c034111801441074004640054071000c01001c000c8070b005208003040716a40c101003001ca020000000118180e030301400007401017103007200c00d00003030b100440f000910341c029240f40c00c60340e02c00c42d03403052003620300c01489500c00c20390341c50104050f1940b54000d001d0250b079070041d40035010380309001c1020000c4682003c1c443c0c0c607203441c0080c3c42204140303c0e4030240030f40003655030806d910815020b0380455000b0906150250505c410080c0890580201c40d114850404140708602c3c0c401e070400700300c0d400149100f0320400d01400441c0c0300c140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 254797508 1250 254796258 254796307
    0xa14010b0a091d0601080f010b0d0506010e0403050d110a031b080c030601020a08210f040b04111f090810020f0d0903050c0d1106101809050705031b090a020a05 70
    0x58201c01040f40420500c03c0038000d00e80840205100f0341e288002d40d0071225130511040c030404d411342c82000000e102269560444400001c545650b80e00c9003020764080c8100460440150700e08800819190540c0014140015003664100080c141c411f00002c103c0765500010804a401b081c00941e41c12006401140d000b0818410348000c071840d640c45e440b4a821a001202440300800741010900038240c6006510500310280303441d10341855110070600709070240000e007010859000381c150540b20300c8103a4a40c0300f07040e82901ea07071841050004002d0340181c06624018040c504c600001c1c0c005900a88040d80c0c140030041e4a05070000300004002c00341c140d0b0071420300006102d8240c415000780200f404410b007a84803003543c2c0510703005060800a008103041c800d0482c1d0030f0140031501e10003a4141a1541c00ca00000300c03240c041c14000e24003180780e4440350303140c440d17010140e01200c1d42200070358041d83c06440070b00703284d21000445403e90240719020703400a001400220008000f007250121000b5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 254798758 1250 254797508 254797541
    0x70206042003010609050a0c0201090312090611041212090f090203060315100303090608151207030803010b0405040b0604030302030a05181503090d030b1f030e06090a14010b0a09 78
    0x19100702103820754949a018401403580c540402c05151018003401402203103e200030040c0340203660b4040d1440d0002030481500c65a00d89035407040240b5540320f0054012000680c0340c070345544980e9502940c840042c21264110740c01001560a0300401040341030310900762119510600301030030b80000350401030400f58107200d01c110440024182c0852513005181e9448035035001d130306500b0040c20100c42030303014504000c045010001d5407544401c008080d04802c846030310007030f400715074204d103804090307000504031010010000400303940040040044683c00c2c2c070241700600d0024100085409980700c00303000f6070001c0001c07440540c8684010281e210781003042c0508403441002003011140012142e0096400c0001400b40702e0104100d03013060f01d01c044c80c0074000801400086100641700d034882e030051906407003040d4003580c00b940205503d5090701c0211900341c944140f10740d075540b01011042c1d96031002450242d000a41c1802281c0c420302000e810f041d005403401c1c140000416006603107840701b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 254800008 1250 254798758 254798813
    0x60301171015050a060219060906090b07120e0c0904060209060d1109090604090203070501030b01200105070801060503010e010b070822060809070311060306190303050a140307020604 80
    0x1120544942415100a0b0900071080ca00b0042444410141a001402558401c035a80d0141425a040c0030b04100d80c440d4000c02c85e08507928012018000e201d00c02400d0841c680208030039140c0c840c210344c0c0312802c0c240c414840c44012014890311405403210b510341124a060010700030541540003030080c10720291141d8a04400d1070094800c540c600c0300308500000340010400e009191110f00c25410090880f0204004451580060f0b136842d0b0b11f2003681c0c1030581302c040b0070402d40c0c080e03207a41c0540701010303101c14202944410702a0007400200c0f500c00118a0345400851414810029030303060f0703003101c105c0c021181d00b81280039403075400c01a400c41d107030002080740444040b00412100107000300018001000c90400300d0140000400400707208040d44034560400110710942b0420032202016102259643c07901c90220388110105500c52444d0044000d0000c1019170100040115090b241d0f036010001815103030308805844103444041c0140d000d0004500800d0b503c600d42d00840b030010120307903001e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 254801258 1250 254800008 254800033
    0x60d02031c020307031403010b180a120c03152f07060204061815051c0207170a11011b0f030f051006030605030703030c0b090304031a040302010f0b06030117 69
    0xc0072501205040181c1001c19003104042d003042052030a12020076080781150f0400e60510203901680308001c0019149003404985030701c42c4103441c00580140e68000030f0341d11690420b84c5500d605884222416038050544221260151052510034901c403a201d014004001c03228091103101d09015065a04c1c0410460000699520050008200740c2d107621181d0040201c0e12034a134a03480d4802d0840014402c40601031035402021180d40012401040c03a1003040b46040c000207004c2c0e0440201003902d480e010180d0791f40400701504248045503038040c400034400f62602d00b070701d813607806030441c500d806904074160324058200380007402c65528000136103082200c4090150380c829111410038290401c018400c8a525002d46005010241c00504086203566001050001d440781c01070a9101d840001c00c081d0982401100c00643c1c0041c400c0d0005010000714014606050700c00318090361078100c104820f040b090140d00201000200003a055a1030801d15aa82e2818407000f50030034054141d40448 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 254802508 1250 254801258 254801293
    0x1103090f19180501030b07090807060f09051005030f070e0f0402180d032007080607050903070b0a0206010e2d10030c080606090c1216090b031906060c0308060d0203 72
    0x225641c14000b03d219459400c00c8400c04c2805880c1404118280e40c050007082000100c85089032154509400e00415865003200d80804503001107520031f988500302003440c1c0d44840610f0041c24070401c8215141c50b00307881a280c8641c0440080d401003116503070f2a0b014500307a40900140c2c070612005a03807840c10003001030480d002070f14080300801d19036503021194201d4000180080011f02000342901c07030808d43c107680c0d10040180b1304810000c000a40a8a5403014401400101016251162140c544500c081e495003000d010301c415158107100064924109603419003505080e10010405031091b070f9442c0c609200e0700810b07024030800220390010003c2d1071142e4101c020900d5501a0805003020020400c1245000c2c00d5020110014442003100b1035446042d2034001d68440451240c940503100c09943d4010326501c160301c540c80110411503003415000e100c0a40c0c0301c0f0007404100e40c6880c0c0006a0b28a500124040c0014070001c0004482c2e0800c03041540245000600b20741c0380070380310000b528 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 254803758 1250 254802508 254802539
    0x1a040e01060801050a0207020906040c022b03051b0a2a060f0b04021218122b0501060c0303020c1e150f06010807080a110301090204061103090f19 64
    0x105a41d1484104480350082c841c00e600116a07403020f601c0c00c4615000600d02d08400380407140300780d581e1500100760038020000011103d91100c1c403030030b200c0c00054030f0013030b4801c548542002090800c0c0c001352107952811111420300a590b001c1904220b4105011115500001e0781103028500d85600b032072050700c4801e0b51510f2a0b00c10240499890811000703041682d03203000145000b14014802c201c2d0542d0b4802d8050350121101024007054980210383c2460041030301d901c0d241c048030018492484500030300e411420008c500d00c941011500b01c100c100700703c5100344640703030006045011020000c0e1180d00200040c501082c219120401010200621480070000d000b4460340401401c0d201c0c2442e20790001d9016584140c078266500d41100083d0403800c0c010301403400c1103980030018084000c00d50040140f0500030207030315181c1d038507030031060001e504c03500510780429503480502c4296107002084561040d0701500c0580380750509014080d40701c0c42411408c80782040c0690100390940f0710110130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 254805008 1250 254803758 254803781
    0x6050a051b0f012d0212072d110c150f0904020f040e01061b150c03090b0103150e01270c030501050a09110904050606010f0201060b030c03090105010b13091a04 70
    0x14100c00c9082c0040f6000202000b480b0240c41c5c014002c21843e52014002203070b1144450500500810031400c0f1016003405007842c0e50350b0b6207025507400031900d61000c901c42d0802894404c80349203118140403c126000598481428040f08100c0132845980e01000303801100f1000d0070260414141d80c0e030045290300903400080940324010010050581c0c041441d458000d04601c0f5031449003520f44a0b06941c6500320000e004240d140d0949010092080e4000030b00300d600003008448a50b16450034803001d0b046081c80c0700000e420101c0c40803003c60b046c8104065031030800300694a0001005840360300030b03c2010f09450080055100001180703083c018188a040e4001c400162101c8515000e5601000200d1450090460f807007040b00150300046c0c180d400c0710007400d10582202c00d801040340905104d4004921001c000b100340700e40180c8d01c50241d030291152030001e0000c1d85e02d03448800c9540c000c0441524488000c000100502049507014086202071000688194022040420182c69034001d40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 254806258 1250 254805008 254805041
    0x30408010b0307150503070513090e01061a0c070302190305060a2c0a03120605060d05090f0a03080103060e15010602160503070f0e06060705010507050c0706050a051b0f01 75
    0x540c071103150500560014000300080290050103044006203130380001091301040c40740009002d5084010b4504440c0103162420060003089600d52085001c1d01e0700c0d10480040400c0009484020010b140954045600c0303040181358042c03a44d0200061828100c0c03091664001210006c0085a0180700d9940b0405840e1404203805209081181c0074900407012181d03031801418100c4005134000c0352a00c2c3c8903401d440e0040c00a800300704101c000746681d50005030703c10300009512042e011140c001c44e00c66120101a44d58450f10400c000c0d803201d00b0004000c0000b0421401400020300e2a4032228003401c44100b214400a20284070800521080e0091000f580c05440700034900b6904284501c060441a4090a00d813864900c89008403101c600800c0d0084564400080b9a901d40750180c031405d9030003600902031410443e1002d011613005040c11031041c0130f00000403031100d008c0c0044500464003580d411f0b10340003c01085419121112003490350302d015904107980b81d45800d00410b680c0c0c0e0a800c82 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 254807508 1250 254806258 254806271
    0xd051603050f03042111100e01180b091002010b150c0d020706020706030902040b1c022412070e030715030c08040203070308130b03130204110702030a03030b0d0503040801 75
    0x1001e9261100d10502c10b1100d030310400c001d1020409136008400f10f000100132242544405103800780c2c04120075488181c1000d4102c0001e284d45070f00000c0c008030b0040a0321603191405001c2c85141c1d0203222400f66599002c010030680c1420b0a15070031807000b04100384000100240c40c0c00000d020188800e0144411b0301002c6070810100e030b024803800318850210f00080180e00d283c030801030740340d5100e4403c44090660701d86210301992100e40206103c58001010481d92a400d045681c1c03100c1d1240605070b0254642028050300f8030043d540031440314104031800d9040c8007514a14203c5448020107003400c1200d13a40c400421500c00300400002f400d40080f81c80120700c10f00300001d08441c01c66043e8410042010f00344400350700c01040d21002c1e25009090a0742c0c411410302410007640c07280c1d0048100e44000000c1090b0000041906c01040740300b200d007071005942c0c601880b8824014010003075415000340807100e0000c2d0180d4003a40c81008060038031040340e0300c251103c0341180c10590101445075120007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 254808758 1250 254807508 254807513
    0x2060105100e0a0e06010201020c010204090e0f07030f0b100801050a090201030f06030201050403080f0f070c08010b060a08180f030705030c0607020d050f1c110913061802090d051603 80
    0x400500720070242c070303000e8500d900741400120b1a802c10311030b501a5114600c041200d82e4400e4044811505038940290755890b0b0301da11080043c041000ca00c510b42c09038880c5074000040100e441421290041e00c244a00102612620990000079118800f041d0241c180082e10392401c2c0100b91040d00c00c4180003451504900025082e200078109115041e40350640c1400180e03004030560307003926080030a094440030081c1110b030081c40351000c4a0945030000c501a010007000202c00c078192480701c8028018542c11905112241c0180304020003ca0b05020004803401f010901180c0c1d0316580108941d81c0103016980b031415079122920649894000080310030030200204145a00000c06100170412016000170040003402800010305d0400e100068401160b031220700c0154a8038101402005520b50002066519a10002d4480c0c01070001c482c1c1d03140c41028030b101b0070040742c081000c2c000c4c061481311076180095010007030981d445106896410041881045440d12143c2d105c85081032103801c60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 254810008 1250 254808758 254808769
    0x309020405181b0607140303091c0c03030c0c02040614030c2e02150f0f06030705060a14130306060303090801020c0a0605091005090309100306080c01210c02060105 72
    0x2c1204800072140a028040103030001220040c0050010782805402c84a030b0004100e4450184060207024035400790086c0c0c158080019070103100040700b00d0b454400f54842e00d140000c000365004000c41d1034207041c0c1e40424040e0300702007030a0b551490155501d4078030340d00040403074009802c6010800449176480026040c01c200c1503da4083c00c403100a00c00120354005001c61501064981d07685810309400c0640b80d008000c00041740c5001da00d1400146404100c000d001c003000c840f0380c6000b001520100f0170074140403c030707070b020b40d80d01904142c600307915160283c0d4800240b0b60809980d40d07041000c1c02e420b080b049400c60281d07205941c00702d1024550b080c018003c20094001040c2c41e44100320758580d0860008070b1400441d40020080b441d0307540c2100301403d24031083c2e0300092660401041107900d400100084c648504100c410240240c1d04400840845d01d10340608440e0b5442185003510701e60150485075001c0d4141d01d2045080c2511800d00c400361401a021500580e00a500600c12031401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 254811258 1250 254810008 254810011
    0x101410020f060109051b030402090402240d02070b010e0906040219051509030d18120807080c0a020109060905013e060a140c030a090203030904060e0f0105010c170f040e01060309020405 81
    0x440c0d40c0c0742141489d0300000c07583c401c080d2000740700e030180c0314034401c0ca00815010700034241c100e0b60354951031380ba242220a010f90301911080b194106098004078051540380c042c0d50260081000405c8107a03505c0d420702411041403450352402e44281480040e41d03503107250007000e1010485028503164100d04080c545008035500803070007808010210041e808501040800440d40d456910b0001012181002d85d00392003103c0c0050060030001a83c20a0340d040092840503a5200b80e0300c00c0c02c07150b500d103000c0340d110340d1038090b03140021901400d01d0112991645081450280914510003130801d50159100d55030110307081c0413154000c9420000700b00360504c10f40f044002d81001840303052800040e5801d481c4002010480d50555030079140080d914200251000c00e40b0182081004503103d02c0500d211000481e120b0980c07040c0f100c00030a96510403401c542034640d0000d0a0b8071080c40c03802c9540d803960480c2c00740028544d41400005040d890081215000740101c1e20006201d04090041c801550030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 254812508 1250 254811258 254811301
    0xa11030d0e09040816060203011e050603061809070b120106020f030412020105130f08150603241f090506031b10180503011d06101410020f06010905 65
    0x7000804a120752141e005280e805980941815a1804860066004401c4080026010900c0480042600c9450389e4503041410030075820700d800c2e1669242040018402251025002421250140102110186450741106205059540c0c4544681d42510181c0000207c251803402c50001000103d4042c003020600b40242d00285103041e090154003003600882510082c1040800100303a4030352607000e80340b0740c0035144502c200c0c1c5041c1daa402c000765503202c0351540009406912404100c4902e00001c1141c001658020083c00c0c00556407548101d005005107005090701c6004c06510481c000050550b0141481080000785402c10308113040c6842c2c01c11b241c0c2e11561656078450415540c0e10030003030101c10380a2410a0103c01c1e03d018181c01c010700c9901c0b40c3d80540c2000500d4085965a8820180301410f4078201c9a075540c0702c01d0301002440551256603200b07050007040240e1341c14400c9822100301f9082c0125a070811285c41ca0341d01d0030200f684000b00e140d0703880b001d210a880054260030030864 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 254813758 1250 254812508 254812517
    0x71e230a080a0f0201021207030f18020a090b060f0307051305100801030b0601020f0106030606032d020409140a1208060a1a0903120309060a0b1e040b03010e0a11030d 73
    0x8206555074401482a007086000b400068602c07102128400d40440d503120407103e50303001135802c040101074003074005440301c9600281802242d81a18440c0d009040c274154009154640180c0303800307807480050002800850308007804200074400701107040300071341c05260199642a9900c22281e01502943d502e41c1106110304e03d560900140c59601000755819a03070850001a1191a8000143d1604080c185580210350030038000005010301d50f445081200d029820301100030110000c1d00039014031110501300e100d4100e100030000b6050070340c846034203a485019105100c80b07807488594a00018010f0480d446000768100d800c000f9400300c403403500520b003510700404940c11321240c0d81c0007003003522000c0240d5a01046c40c200340d9401f0803900c101040524042a92810100c41080c0c0320320040320007041c42402c2c003020511900f480900a1352000d503078449040240701140c01c20026110700e24290344d240d902d402051942d50000e00c0754110711031058240b5204141c8003414142040c0e07140f00f2000a21 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 254815008 1250 254813758 254813773
    0xa03030507020103360b070306120311030906030c0a11030a0c02010810050607200f06040510090302040204080c030f07050d141c09031a1506071e23 65
    0x65000030545540d60350909010610213021840d0b40d000380f5940041d22070242d41d5000c054080c4602da40780400c0e4600907685a00b0a5954001c140c09490b01489139440031090391440c034001c20300c42c24100703c071a0030030741c16a444c242c11031002440c40c0c0c00076128984941000a00032004a40020a4200422a00014600303040403000089c00071540840040e0521021600142009410003481c401428000301715030317203440c0c260500b140100307491540f000345a042070341610b0040c5030090034801c0080d00108141c3c41d044c205400d00c2688500300f2049810302c000d01a0120043c4e8941c0050b00103040000c004020038501c00b8101840c040120070705008581085009202c0e68454500301d070b04481d0400365114504030005c510500d000307084281c194205181e0b10340414216842650341044a0081040c41a4800380340660400f83c041503a5101c0c180030b61a21054203420410042c101890040485402c2602c071302c042003480b0b42040d20200d07115420b020380003030083c06800d48005100e81090040c401d9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 254816258 1250 254815008 254815013
    0x10030f0c020a0201051902100905010b09090f100f0b040c020102090310180209040f0605010e011503020a0f080613050f0403090807060203040b0f04030609050a15270c1203050301140a03 81
    0x2031b44101d4000312203905030b8840109800f8000c005022240d594178104101c900017506080b4000d0441d00d02c0140b090140380081140c40e240066400c1c0a4581e620140003a00341030307203029004294203101c0d201c00c3c03a201c1d8035810042d9101e02c1445070808a0340c00250380c840580381010b0811550700d06403c45a843c1c20721700d111842c44884041c1040c0c1d81500c4802e40e54483d410650b8003001c0224000303215905003000450548002100541200c10031950341001101c907441c00e8059010310401c1c0d40000d54100e01c007414940c41081e81641110700601444005030000b110f610130b0310400c5039000b61141012040c0020142c3c082c0e56040100f0000001c2c0003002d0030048020340321720071031003040811100400c0c82003400700c2040484c1d005640c03104040010107000d2901c1c5031280c981c22400d07036113002018850a6400f550b070141d1900e50015008040b80c4805100c0c01c1d85010303e09103010303a442641d58002107010010250604120b80c060b889440d141d40c58003000c030044181d6a01c0c8240110100c2204000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 254817508 1250 254816258 254816267
    0xa030c11150f07050304031e0c0501080606070b0c0f040303021c020c1c11100e1801060f050705010905011e0b041802040b1f0e01171e090c10030f0c020a0201 69
    0x1810125120b83c0c841580c14a2442c40c051a000a403c41d803500c901c2c1e0361803030110510300c030307203603209040c604070560307a8800540350b01d0021a14a600041e0801c0703104001161651117561020381c007c03c0500f8801e1011180983d900305410460259115000510a0028052000c4801019071000f40141114800440c407140c00c03000c0100c840301e042140c40070400010410079000e480c005009001364590458000b064000c00300c00e91405209401c01c00428400c80303400d06416540c80fa00d4003038180a05000458290340b0500c07082d03485540c0e4000039030020300280505151140b8900b41d4413101140351900404451700211024411403900000000d1900100ca175180302c9a01102d00003032130820040070034500303031540841c41c030142c00381c9072403001c43d0f03404c4429200c0c0034000ba61258075501c110441600e0100050303c070182c00050b401030410403401e6104101d9481007070796040da1125140b20010a90446580d4260710200b40c0341e08170701103030f07020b1403040c48024000340c40144194841900081c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 254818758 1250 254817508 254817517
    0x90516090e012601090f0b0411120d0c030203120a050612010e0c011b02040e01021309090506040b070c120503340e0303040f09090b07050c1218030a030c1115 69
    0x40e07007010021000c0200400a60000f94001c0c2c20203d0741e88601b9092030031180150301103c08076402900e401d0b8a121504000000c00004243d03200184025080c602040ea000c02500c61b0850441c4400c000c0321540c202c3c409070303441c068040400c001c035580c00c200c0c08119403004003554086041e0b2501d4a07508820b02c1c0022400742621003800c1c5a051741001d901003180d240349482007c6d4203d4184094500500b805500814400070f491070914462038540340303c0c0c419204540c1000d88640d200c00081340114861611140c0c1103109810003503412402c984d81c2c0344d603151000d5130441c04a000441048201640200c134141c400385250145407001c680316070078400c07950030300441604000e04844000115101002250060440d1640d4803280315550b0a002002e0070707103000f0449100300403001141a680c01102601d6045e01c1d240301a08001c00030095446203604644c1000d11085242e4581c003502c0d071418429040307a24003961700c0341410a1281440c15000c8845c40f1000e00500f2802c1200c6554282101a40c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 254820008 1250 254818758 254818799
    0xa0e090c1009140f100908010507170a0f02190807021c0c0b0a0e070801060302040c09030302071206020405090f0a0c0219021e1f0e0f010503010e040c090516090e01 72
    0x4810011000012513114070f900c40340e03640c00c18841103e54081e81d40001c520821141c04100134072140d81e03403038000c40d03a002441022080c0f0111102c0070420401c2d10741c00018404c0a00c01006042c8000c801d004151980c103c040400456a130500f4000b440e40c0c14401ca880004200e01c103d046d0314280600104042a2a0b4000c0c0101c00602c010440590320340d0410000000d1100c203c40384680c452450038000e2219101c1244034501d4060b00c00c00c00e82c000d1106c50212601500900121803600100308036011201404892a5908000101d000c1e50303480030f00c0b4000d070320101000c3c1541c54407800d5802102c0700c10f0000c000395406080340b00d248100200c47c1030843c42c0e054640700d4003c034400b60401501344665100942c003a0a110b810a02e521001d1a2403244896590780c03000342c03036010014000b803440c128182a0004a04100600c00c0380100d0410b180c105115840c00c0048542c2e0b0410308040b02c4003030340c0104103440c041c041110001e81c40186880070b40ba02c0c0131443d000b5403402034403801501048900303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 254821258 1250 254820008 254820029
    0x2010501062a050c100f0e03061608040f020915010e0906100c021c0b0f010b04051e13060303030b0a0e190c09080a080a08010b0c0d0e0d020a0e090c1009 67
    0x42e0042207410700c031016450901a003000c44088000d24082e015200741c410440000b5615008450245400540c01d40244406004000703048814201207840b2030b0001c00940c2c025541540d200011b0321800c0075135102d2134840007142000c580c044001017810030150840c61280020405109040d614001c81030304030b4419041c804540341080c804920002d001102c681c2070040f0051542040c008074003681807244410b0200c07801c0e00e03030321103410344400e01860240a1704402c110454852507a280b06501065940c020500da200e0065600d181c4140c511541088000035102c0c640401c0a0808040c09006004601c9001c3c22900e041c00180f5020f0150480030300c07000391180c050a12382d6020354201c001815980c000c1e24110501f5042c11010355200c2e0110350000b48a038800040c00041003002d84468035a2140038141d24807440da021640b549c080c600181c0d0015039084031400607035900140c0e40090544410f0702c03106251081c1003500380000e0714005070040c908280c02c0000c0c143e001300d500e41a2010303e102c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 254822508 1250 254821258 254821337
    0x1202030a0e0a0f030e030601031a0c07120f0905030a08250f0614060108070e132c160620010f0903020f0c0121050c09041104060201050106 61
    0x8850260400c45074a958600a8508160601010740b01d00e00300103001c0e4482c007860700003420034103954038003d01c00941403a0201d4400880c5010302240b20b5000101c0003201428800c1a44070b0b049000c00c40481c00c40030030b001ca002100c41c2030300034180c90005c0030304901400c2c40942c2c9483d10030b818480c914a001000c0e018200910658030610319280005400c29102080c9850360b01d4080014490385c00400111749200c0000b0326150b1040403500c3c440c8520380c1c0c414501074881d00c1485564288a4070500507140c485d140300241d004000022080c500c01c0d110040f8010f01c8400c46d9074180b0100011411611158000c2803000b10b40040840005224141040b0511070020b61742c58010150900d85045550412003c0320906034002500303000e05804c80188c40010949000640b125001d469240c1000120141c0044580c82580c0c05030b613014400e2641030303141501c2e500c001422a44002d0130208405408101440700a41c24810107014020300e08003428007080c054100a041c06904200590b044450070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 254823758 1250 254822508 254822521
    0xd090506130905090303190515010c1505150901080c012316080304021816030b150c060103150e0a0f05031215010f082502150a02091f120203 62
    0x99070018000080200440c1c1004519503450741c3c001d40301603500042881051020709503620485002d03110703070324081040d0040c6078010341d08940c0c404c02c00d403102040c01049150300c01490082a1180c2107180080e9000186401041036940040c0c0101c03d1503400f40042c41881d98011628000e051460030b480c00220071014200c1d005482090403102a8020548101d82084402000b43d4000c0d4401c84861003080c0b00d00c8128401c40400b150481408414481d40040c6903000750300c040100440034160b252024806075000348542e01407500c80403035600010040051060b601d41d01d02441d03a2500090092800440886540e0003c0400161030188032068540410408004039882101c0c2c000340c0c40c1c0707240360101030b140d541c601c1001003a02091007550403040083c41080746500c0b4454a940c3d51034030b451440070b1600c05600d0401818154461803140728081400b05820500c01d1000000242c2c1e1000520240700b00b40440c06001c144000c001c038003014400c2e41050303c51800c0b8051000041e101c0d580ca0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 254825008 1250 254823758 254823787
    0x5031209120d03060518060a0303030e1504050c1011070504020f0c10270314091810140109030b041214130905010b040509010b0d02090a120c080d090506 67
    0x80e410079201c1c190120b665940c041d08100c0440b00100c9040c003c11090800304000d9540403102c2d40d074480d24001e000d1000a0096000d00702d00540c100484410f072041c1d101001101100340e5066590350700c51904000c4501e005420b081500c180d501e005500404014201070b6100580e0090621898012400f15880341c1c6110940d0004d6408008a4002c05000100c050040c003803c4c0301d20340c820342144407040e0569101c0c54941d00c515817503910320124a4100340c1847c0c071034014800c1e0170350054800890300c8082440b0070704240108003403090005400d1410302c54003109140441c0050511400b8501080401d8000003080c1d80190018036500801300010421038ac1402d0191111a41c41c6011a2540303c0741e0882216000340ea0081000b00300990f01c9a03450800d60040d40308459010083d0700c01440550030040240211211800c400350400346480000359071006503811020700142e10f00c124600380201c051503a0010300005018203045440154000c0190f0070600030300b8050400080d000e0594a401d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 254826258 1250 254825008 254825029
    0x605011e0302030604120320030703050709050f1c0209040c0f08010507080619030b01062106050609060f07151e090804090b0604080d030507080c0c070302101106090303010501140405031209 83
    0x58895048099252070988c1c035890708195a03480000b0315150000303507150300420818065540080c103070080c10420000300009203d4100b4590740c000d006103004030040e150220060b0045214041c40032000d81440c04003e0340404a5000610583c10034051028186d04584130030f403c55002e0303503a4160319961f0004d034a043c4407103902c014641c140b40000091407550084041070400c4a1040b102c000c1303561541c00da0f05a64550240b00d034401d608009078002ca29054000301001c40f0451012400d0100e40e80b2120106080403041007412621385900482003101c4207007012900c2c07400f610400018081d80c645030a240650b0050740041c9544000a9000c0d60320002a10028100c04088032202e01c070f5080014040c2c101998008081081d1102007000710090100b41c4d10112104801001071901c1c58003000300440071a2214014841010041c00c10900140440c03172042503108015a56545440001016180c81031410091040d003440103120b0b80d50041891281e40c02154041c580f60300f200f00009001d400c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 254827508 1250 254826258 254826281
    0x10c06020f090d051b0d080d05070908060108010c0f020d0c14070b13050f0102070b03070302090402040b13060f030e1b04020f0a031a04060b1b190605011e03020306041203 75
    0x810003052002c021300013590101d69401c041301d60340c61400030b4003881195140d1300b0004010103000c1c404410425125440194001d040d46440304e20660744441c0350341482b40a801c0f450150b51140513081e442c3e5000000c05880c001d6a00c01404d0740d030072040004041e80003c0c40c008185590071401d80280c0802007101c4000340c03c0700101e41c3c0d900e810004201550a107584501c07030156891540d100029070001c6900c604a4580d029503d03d19500e2081c01c45c0250311400020354003950901000c55040f5204d03019105201080324590402070501001818041e5542d600b00205410800c2c2c44241d0b007008140c1590304c40e8000001c000351283d04002902034000c18110300111040850b1500c02c2070b81c0354002c8085002c0310b60a00554407441018001907481c0790140d046102010800886000c0620207085d401c4441e81c025640d4072400000c0c18030311201d400b54290b40e41900c2d41c00500000c0510b070440c08041841e0703003c0c1080e1500e5640842c1e250400140b0150103892105074640c0b506010780c006504024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 254828758 1250 254827508 254827519
    0x100902030106210b07090308180a030f0501020a080a020322021503041203050702060720120307091a0a21020d0c08070e090601021209011103030132010c06020f09 71
    0xf400000489100800810968010f903000c4040b844503801410b200040d00d80088241e450140d00b41190010344d20000c0354550031040302c54001002c666204003480304684264000360b541c00741e14400404820000d490071070841c0c41001885040000052500800d191038a5410f034070740040d0000400c3c101c0340f031009540103e0000304200810a0780029119815502d071001c0065803100382c1d0490313685408651000104a4800003c1501ca0241c459280038075409805c40d03080291102c2c0320703010303a0816180280801d01c40c0006202d040d174081d58000115802c421158100102c0c194010414940840c0024110300c10761340414108910b50100c5011041c1910b00f4800302e510040c009000a000300c0340c00e800500c08041328212490300e002c2542c06468164024007002500200d07082459100c6400c0ca814084101c12800b541102400554020300412400761100c6184255000844030b510389440c110010741410891140c0e001405400e07219000350380140c4640a1030300c1d005071846096001984007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 254830008 1250 254828758 254828789
    0x50405010618060203040303051209010902030f0c04061406040e0711030a080610030504110411070f0507082b14211b04050f040207030c02150705011b02100902030106 73
    0xb0307002020080c882c45007a01400d02c0720b079100c00481c0c50780a6070000400040c0204420748281d1014940c8a40101c1001c0000504004990003e441d000c01c000701003a06400520507048246030901c80d080040c4070084046030035044020000320640304500481d40e9405180700403511440c410300315000c80c5100d0b042201d99514012401905010085401d680703c1c1d0040c1c45140c0c0940c2c42800b07403038001c036400070705407203910802c0b001c0101070403410288001658051081d00003181d0031414000903180294085e205c0755043c0400e03503041500000b00c252500403034940c144101c510140000c6610340080c50046c429407074003060080e4510420402104418080302500f01e00103e20029034000c0e03102c1401640301d0000c200b45c044041c043c0b449081c0e4882503000c00398990381400d40040019030f129190001c0e00864903400520b5203111040b5000d1440e0012485604020b4240700d46d2500c610386821100c100e5078400c100a50f00c403500d000c0d8000f030586580c245402c44d2000d40000380030f44442c0c081c41407030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 254831258 1250 254830008 254830019
    0x705093706180b0412030f03020d0204090203100602060403170402060415031a03010608030d050a0f0501120308060105070c03290a020705100e03030c0304050a230c010305010b030a0c03020405040501 87
    0x40c2c0d24050707407841100140c040020041080000c50342140c00c140725690780d01d5a240c0b03058401382c0030640b6040906408010030201843ca9200920140000e40030050b10307400e04da083c4141002c03558009030305640c001402d100100b80c1100990a051108850030f441039980ca00c04100140503070f5019110f00c003160f5508041168054001e40080340714482240320104542c81094280c43d1244110081a0400c10a40b00c486155400459114040900100342d4014089a900803141309910072020321121000d64801c141d4010255a000842481e05500300403094844415813045480300070004004a408540c030400844131301444a007540040f8440c5c2e2400c80fa4880296016031012219030003020049248495248611400c00712104021411030752984905190340e400a441900d1900c940c40b400b400040d114203001110481c1d907403042c10500405800b641c44c091072141510306041c01c200060048144441c20f03030364400300c079180200f008008440b0580080c03180d60440780e0800c0c20600040340 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 254832508 1250 254831258 254831267
    0x2211031515030a0b0a0e070302060a08040b0705090603130f050d020106170f03030109090804080313090e0309010e0907030b3d140f0408060a050402090705093706 71
    0x104651065020300e0800c0034104241d1a0b5400100050201306000042801400d0320751104001c10800000c541d00c0c181c8a80000301290400c0383e903680054400b00c00c00c010802c0003540140c000c01141070940c1405040e600060302800010301c00001d9169100080b400c0c801c040c1c54459071181c009040d100d10400141c0000d0180c0703554041e258414503440c0c00018644000a01c4910100103034026605590034508800041e04140d0810f4030711400510010591031818030003070000f14411028003100c60302c0d094030203054885220324003003039403c01e205800403660485459400d150040303840e4000ca550f50002900107001c82541c0c650007680d018480d00c10454144d410400111528000a100c414a403140b41d01402c1c0c4400c0e02000580f03030790301803145162814082d0000414402815041a4070b8500322890044c085070b40003912510340b414402981095680160400600d00d001c03032400c280500800c04098914140c0116a0800b03002c64581080d0f02d105c106040100d40f00020086d0740e503000061 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 254833758 1250 254832508 254832511
    0x60d0b180d0507050a02091308030a06080613080304111f020f060c070201020a12030221071d0a050120010e030c0105070903110103050901060b0319110322110315 71
    0x85a1003180805103120b4001d500b503034002c50b408402031100680c01c2d4280a00707280051314000380500a00344200009103c440690704c00c42c0c10700310000703a80386001c15540c5010005000380750000c601140d52408241200c040700c1d4800d8118407000300d11141a004510510510144070709945006d50703a601c207180d40441d039540000041740848099848001c034030070f498072840d000213026a021200c21800212071441680310314401e41070060030280d001c15881035031402c00e0100700c80302c0039201c204401d880e0040800400c1c0b1640c4001003e0120220b000b00e503ca4519010344e078140445041c103011101e40e0414108080150680284200024445102e98a400200e800b140c0c40d42018001000113100b01b1040c005c80350081451902c160703e030801900100b034090810702311340d503e80754007240d6145444019130051002803c142044001d080d420401c860314800000030b0000c0403c181b1071042c0403048030480024203003480040f00c1000740b40c210785030541c1c0c180550300b40c0110310082c4549021117603142e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 254835008 1250 254833758 254833801
    0xa0e100f022a010c1103060a1425121107050106050111010e0d0c11030d0e10030203240d060501091409150708071b050714010c0c0509060d0b 62
    0x891080c6005001e82d00042e180c40c110801c0c51031090001182907105451014440303028440701c07640f0804031030210341031a000702c6883d075030640c0303a250600a400902c0503d9510030009928900490500f00f66694000e402584000410101241e8990048503ea00692003010b0f105030480d41e80810b8500640600034920680c2d01140d540c441ca8081c8441c18011301c1c0d83c4a080b44054071940036060003d95102003034034415500303000100404685501c08008201c00d14155071102101904401d08000d08845c0c258130040405005000740700c181030600000720000c5054402100e07000040d4004115116074201010b024141000300000d5555503980c00032030740d001082028049580c075107120a59502007844103148445903540000c1006200758842c6400502e13a01d003007080c1910181c66a582403095100a441540014904100d03c034950040d1415200742801c0c14224400d071503c070340d40f0740d484500c113840c002c141420001b600c5582d513003040869103a10808044650410310124200d000082185 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 254836258 1250 254835008 254835013
    0x1006090506011e03020a050904020d05041b0303091401030e0d030b03072301140405130e0105010906080a080d02041212020c0f06041205070306050f09060c03011203050a0e100f02 78
    0x101d045940b0818111441ca40800c01240710030114190490096010324024410490f040c0441c04c12981c0e00d0005080080d00742da8080703404e040c981840d44500841d04e624802980052904000094100e03c204040b42c45c082c000e510400c544c040180d01911404a0001d0a80108130250141580540c084040c20006500310351a050306c0d995041900321040001c3c1005020980c622001c56100741e448110880303c1d066044d0405036100c01055207030f65580b0050b044151252030404528900340306140c01080302e1001400b50f0fa107807442860315000309071806000410300217016448800360b90100c1d4004d0003408000503a400c040d0516118070520316100300010700894101e640c981c600354425214100300100400e242920700242d00c10b4403914413004441c1ca000d01030707001011070000e1140611515004810384c4a914083c0441c9040200080c1070444811050005002d003201c4050080b0400b0381c1810801d17550ba50750b42d000d0b02c1c00081e03101d6141d032282a0144000d0100d51200304215000525004c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 254837508 1250 254836258 254836261
    0x7050d0206010e1315020706110409061a03010b1b0106030b0103080405040e0609030a0c02011b03050c07150e10031401031202010b15091c0c0803040608180a0b1810060905 75
    0x1002a07510100303540117460030028031a00050005950b0040c901c0c9445110001091702d5500d081c0000794002e0342c030410200e5a10901001031064502c414801103d181000f03920b19070609203040003501800344141920303401d44021081440f42540000301075900010f035011a9a5a403501480c036034050b018076400340d0300f0b004040610b8900014100e000d0500a00a1360410054400446040d000c90b0016410007004824503503a04262054412003280266511561924440d811030f1511a150344040c100c045010040c041c00e07540482c80c51121101110705108003c0242c800f100500f031002c3c082012402010f00000c2004800841310b40804002e400030700100e02c5140c1080b00d000f03c00c1c9101e00c0016010041101d00d440e00404c031024514550703001c800f041085845400d103040382c40c1c1006050390300001c0c00780110384c0c00019007588550403180d802c50303504842441a84030880340a0040c400041540411100500704d0101c69141c030420084032502c000c0b42203c03202078030603032180300607551400c0e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 254838758 1250 254837508 254837521
    0x33040c0201090309140316090207021207031e0f020306270a0b060d1b090207050c1e1504170304090b09070906230406020109050105010906050d0b0c07050d0206010e 72
    0x10b856000c2e0700350315841c000c0e900c0c0100c0c1a01039560054499414011807007604041d86844403008041c2c002c8440050301d0319218414409641c9640b070003a1400c1c0d002c403001304000740a840c84845c48080c101c003402c60001c8549060100e076050160003e41c58044c20042010301181522a14030405102003600da5102c032262005844003020700b806408805ca00c0001082401c4c06440420742078440e610058101d2424070466200031899088445e05a0b000200c500c1071201c204840c040c100000c44450503044043c01e4901a440140c20641d0701980502c000843e024042609503001400028800d21081d185488920303103e602034096400e0a0f40b070084914024101494482c3c840d9409031a80e582c7c8509048080c1c0d0180d8007040902c0a50f03e820400c004088217400c0944000c1101c0e07000810b54144516000b030039104144c0141a2152800b4000c0116a503401d1504202c180c1060520619449481c18008035104940018065219584000940e1980081d005040b03840d5121030340704a44600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 254840008 1250 254838758 254838761
    0x41a01090608190c05030105090a1401020f03010302040b0111120c0609010603030203120406230403030e0c030309040e070314030c0d0f080a05070c0b011511010b1833040c0201 77
    0x2d014800003680315a50301c0c1c0002c0035503400385181c83c1c020038441d50b00319034880009094034401c54032055a600000080320420034408407010081c51084000c0d0700f40200307203071600d01c1e0740014800030b27104c2c9840c0c5820685690180d407040c0701881204060705d00d4190341449058103a407284000c5140c5100b0380001032041e05061280400380d80c0e040d40a54a8244008070b1221000b50113401550361030b81d203801c0c105604c003031414030508a82c4107400700343c00f41c40d02d8200541202c042610100c8203801c040c45034040c83d94040121001c1640c21034000540030103645078a807420310550002808000b00c1350f83d040454030000050414582c0a0040310340c8500c07281e00c203d410b81c051880b02000b007146074000c150869400e4002c0b42c0d1264240c0b82041a105054030317803200e102401e0303000b07600c3d4544001084c0d50340780d44400c0801703907500301e24000d000031030100c804201e1203180074aa0007601c603030490105816080c030321a5490f003414040b031010103075140d1148a048004440234100e00c9240b429090f40c8465006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 254841258 1250 254840008 254840021
    0xc0c01090f03030305100906030609021011060a15230405010b1222120801080601080703021e01020111040602100605221d0a0b090c09010e180307060203041a0109 71
    0x41c070721001c005491641c0603406084040c00f4421001119400400e0b412400d200b040004e6005040104544101c0e00500c0441d82c40040124200131b644c004860700c9a8001407001d030403079003103c4000751aa02d24460b441910031640c021103415244041d070b203140741d070b964402c01040f24021181040240da840c00c0c5002c940c482c400009920807402c80c00030306110f03100480604c1880110442c0c120114840d5907143c0d09a25607a480c01c081541c4500602080d0010407c60740504a1301c4000c0aa00341507400060000c411011003090100c650034a14925901c02e40000b040884072a41803070320746480c2c04002c2d4070380038103c240ea484e040c94480d000501c4d180000f210911b24814105800d200c07040141d0300c5010b0200d4416400344100e440d10615651182040010301d403501441000d282c3d07050a0300f00e141400030000c22648140c41c180c00600007443e8090318103801c1140410744411203080d50302d230141180110b01d00134041c00d1020081005000e80400c0b4002c1040d01c0c101d680e20783d46c8e201c17000c2d507044601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 254842508 1250 254841258 254841269
    0x111002010b0a09020f160311011a03030d02092403040302011a011d030c060c0705090a0203040b070809070b0f03010e07030920010c050106030302010b0306090601080613020d060e030c0c0109 83
    0x4100c40208043c4600e5401044c804102c60502454031845009501b40c10500c0001200020741c0103d9a170700b240820300ca0340071040003070b10b4880b03140d40c0c19100290b9079000c1d442182c002c595000a240005030b4484d0102d105840061070b5a81010181d4810f010003904110f50a5016501303025420f42a4100503407011031124050b1034a01000e1501c21103a45a010a094016051f00c2a80f0381d042403651810007a00c050094800101200740c103090a001982a018004085050042c002e1200040b101414207500c00024070b040180c55a44503400c42c0340c00d106910000050000090292900500000442c1a036201d82d444000c0303174a840380d04800710b480d052000340c000c064082092800c0800d07c084507214040c145812034040302181c075140c2c00c407252980100c0260303550340b080c0005401c05001d40c9912070a00c2e4064180e96152500998541c3c900070034260b26170384900100e800715515000c00c0f414450304110100b0680100350121a07880d4028071910420784110aa9240e01d98070a00882d015200c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 254843758 1250 254842508 254842519
    0x9021c0e030a05070303020d1b0201060b12060907051204081305180c130503010e0d020105060a0f090b0409210210061815030b071d060a1b02030316111002010b 70
    0x30320b124040760b45404c0440c4c100c0815400300449040c0380014002d8041c8003542ca0a0303481ca80198034800b80c2102d83c3d560110040e0541030244074540101c44000030350154040c1d81d209000d07a1170b20780465591050f45c4840b86568150001e12083c040303220f015115601c52000e0712800d90751100204400c0b019400c05130450b480ea040c0004102e00f86070700c041d2030540040c1c865561800c0d11500001d00750f403881410301d0129480f400355050f145509000d0700e45c0007002500d00d50071003070402c0c1d102d94480d441c07405110754807902c500e911001030715503a100300c0f91290005a21104800074074000905e500ca40c4c01c0e000f00510a1070340222041d00300c6d2044c20100c400034126140004c0d41d10a1400190090074130550100c01500c40c000007180404030309500c07481c825610301c4240c0f0810002c40d2885105035030081d002d502c3c1401918109604035089030010031483c02000e02c600c0c0188000392441c071564410f21424202114980c040101640746002c1d8030000b1a03480c48800b490840c22801ca030300e50038905501c034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 254845008 1250 254843758 254843767
    0x50603030306460902070507030615091d1b061204020307050a03080c010c0e0a030206071103030f09040e031201031b0b03010b07050c0a03020a2601050109021c0e03 72
    0x1890111280b43c8050308515803003c1c020b08001c80c40701c0b0410342440c3e801e032040410401041d50154154000050040c1e800c085040000946400e992100359000007044c4650300c17030f08841460b0916107000c000b413803c154103001e034403440c48480b200a50b182c07d014041d0b10840c0480c004860b507100c455001400b01910650038807400c1940716143d4107010b08166014010410046440c0d00c3d10035030000514015140d180d070700c2190910082c2100c614150342c9041010303114104009584a17038002c3c0840386c04441050f2141d65a040000444c1b0706440702a6042c400004d007042c0c0034030a040940215802105c0402810303469644081d12407281103c9c05445200002c01440000c190040c00e6140c80894448100c02940700c103c0e09009174400c2c0c000c101c4099020070050100b080411071848103805c140c0c0c035001c0c000c0c690f6001c511607103994000d060198241c8a0b0392600402c1c62400c0c2010310702460000e0208ad607403412680e00030b41c04111240d01d0080503902008038840da03070183c00743c00e050a40003035141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 254846258 1250 254845008 254845021
    0x7180509070e0a150e070f08070c02180c0d060e1b0f07170f03010303020c090c0c151b030a050a050f01060c0f02060d0e0f0d02120403060b01052710030506030303 71
    0x401c10091031151a0420134030100c0e01e200fa0380e051601c121405e844800110b01444c5001c0d1102c00014402410084008400030068841c2c400480e400d05207448410305507101d0701995a4540101101c0025180c500703400000c000d039050342c2c40782c00f47c40c00075501c40c0b8400039102d9000031846030008030401a0341c100321402c00208075418003803400320ba40c800307142040340c14008040203500a90054005900104040240f072805004298220f030480002c07520340080d8400b1203440c2d40305003000320441440721000440703143c14500084030010784143c2007556032a00c070403594000c2c41d058520340442403604000030700c441313186510319044e100c540c0c9a030300c40a8000c0d650f0f100f00c2901404201c0e00448184000901030456011341c04200c0c40250250403480000b150036071424409000c01c0003107600601d8154018400c5100b201c068a800030b1011501c02e4808006032068407a4451180756020084533900118118104009054400300d404140028062404800740c620030b540c2560305030410004685c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 254847508 1250 254846258 254846261
    0x3141303020d0807020a0b040302010f03090302190312091b0f0e0c0d1805010912030c0e0105070c0803030705040f0501030605010504050904060e010f0207020f150906071407180509070e0a 82
    0x40e80300315001072421300035501082142d00540e00c4072400c81ca01080c113008540c1c100314403031071090840c50b040007008002d450003942c9418100559843d0429005100145440b8842c6002c20030001c48040c0905200340ca440070721000f11241d007070071a03c01c4640118501c02c1e10b16654088600d030050b00380450300d400c50902e03002d610003054410b001e81e0318100400d004044800703040003240280d00024145021b800c1c84114008118910010185090400d0103180c0d081a1b0509031140207180c055101c2c0b51500d40280c20110a4100603541c2c403010041040e2241e0000c000e009803503100c046443c4007581e5030019001d4032410300030f460114030203010030301a0b424500341040d44680a540081499400400640d00b1039150788000a0bd0f030760002060415420200803100b00040165645054840180701000860240e0480f03288904030011701c00b018000c1280344440d0110780da5065070840c56460714407007001d6000400c0c40e4901e9050000040114030081440021603600300381e000008d50b13500c0074110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 254848758 1250 254847508 254847529
    0xa03050a0813090606050301031506270f020d0608071502100c0c0c06030506010e0f0d03030c18080709060905090c04021c09260a020309090714070b040314130302 71
    0x41901c4012080012050f01d58040c810007088992150340d529411402c18040442003008458852070900300c0c200442c0f9074440c035a080b15103010348048135560004d40c60300e010300305100c6104007290002c1401e030038100240c0e00180485183d030b003c0f0303102543c2d0f829228a400460611640c003680091103032183e800400e4205201200039480c004600040c0340d0340d0440940f00c0c0707820079400a0307580c604120040d40c100304c1412a8a0342214145008203080000855801206100804042c0c44559031f04445010300307410b800e00c00c004c841e2058a9622080d0143d601d0f0600e10900c071202d41818000500c00c0402e1043c64003460034000070b0405841100d0900000e035100b0800c000c105451a4107085850015221303803082c081c402c20001030404c140c01d5105114440224032842043d004009192406c0c0d00041102c43c8200c096800305066900c0c04000d86a48070030704008d03040075100140c80000c00200d480064884c5100b03031241c0143c09070900c045c80c00b43c05040100c1c80d4240c0d81c3c420510151404000d0b04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 254850008 1250 254848758 254848777
    0x906060912010b010801050a0b0f0a030e0a060504020907080402011710090c032a020304030308040203011b201623060a02031b010b130506010903061506030b0a03050a08 74
    0x240340c40c0d824000709816550100000030709075529002441c031503a21040480c010241194001d40450620307031480c526114407001e0200036400050001c2c0100d0207500409400c5285c01c007a5a0a02002e0405401074041110100d204101940000d5000b601480c07905000b86e4060303407406a160003200380600c034018081c01189802502020004401f0220300603907105100a43d4041524402d0f0440c6030800ea00c400390320242e00d52124080000d041d80002568102c9400d0718040940d9100da00110703004090301640b106807000b0482e03500041d26081101d51200500006581403030f44e0075071001c41d8079002c1090412000c0e0f04480810070914080a844003012030840c80d283da20310008400003801603110b042c6210160b0408104403000320124800418a5a40301009201c000c608000040988240c8114214200d03a14400300d06581d1041d00004082d40e4441d408011040955070f2019042d1040d114030300002c0d0400380055210705040c0154000c0b240e0010043c000105d00340d84070600c541089040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 254851258 1250 254850008 254850019
    0x1a04050603130b09010903080109022d130303050306190608071103270109080d080402131401090501150e0f010323010b03010f0501020f0a020111010605060f180102060903090906 78
    0x100040350010f1601d9009400c3c0c10300020b1048524036028060f250b05900c4510194030500020084005030503881020340c0802b00b1565440c1c084641d4a40c1c1409019400c200418540001004064000001f140260804c91b071a440c0690107407440310a4400c1c5d03005404c0002c101e00041032855011340818000712a02c2c500f0340c1d00b841020107070844200004805d058600001401d81401540c118141c03001034100640030300b10050182001411041001c2c000901991210070f0400c01032640d0707844919144000150b80d403c65a6038058040176100c28081c003818030042102002d002d80c018200b80a44540c09400100f200c680c00340190006d083c140c2d0f80c610001c500b000070101120300b4205450184c00301e41c0c00103460354100310034084064034617080759055620030051845e0001001070901c124950902e03096010304501000107004d000954041c0c0d811410114821103203204000282c00521840ca40000803101043d004903a203d5050301c0002c2c0ba070b081040f000003541411655154040b202501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 254852508 1250 254851258 254851291
    0xb04020d0e07140904050c1504030b070c030f030212010e09150405030a08150d02130204090c0207180c080f0406090f060e010507050406090603050a091b0f1a04050603 73
    0x1444003550900007105195400c80c1d0801d1040c940450140c240520055034202d41c1460140d80341c5542d8500c1c02c80051060042482e010601d11a043c11200910b030320a0325440642080b00016203d00f000a80440200e120500e603203401b9840b0b442620b00c84101c0d0305410a640e4a090451404160068050540c0c6d00488a080300e0095600c252140150300c210003e45c0d8482000200a00031007000e0b15a0341b44000d10840610681d0703c0401e81100d00ba01201d0586d40050042d00e540002d219980c800051203080c007030700d0b4092940105280c011a02403010b17414428081080890403901c44946400104441c0c1000c00e6200103440712040c0d0081c415a130000c1c0000c00758441092880720008101c403440d03100c90404925481c00e02590b5040000c07401d1941c1040e05001c000342107622140a01c00130103598400048081c4110b40100b200c854010004442c01602c1641c07070080200307240110f0b90030509071100011603d056141c0b140041006880244c01c2c107041008114141d800540243c0c002d001142 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 254853758 1250 254852508 254852527
    0xc090626100e0708040b09010b06090108061306060c21020706050703030204030503030103060509010b18070c020109030b070818070f05010c2a050312030402100e130c050310090218040b0402 83
    0x4030ba0724050a05030f11452620715151904605540700100342034481c1e41012401c0c070554590740269080131300d003401c00c0312003541c07200c0211b50004206840510181d00b0040c0001d0904d411545107514103006000d0700702c08004901440310f205401d6244240182c2c0035450400807a072081e00038100c0c1d00c1c400d01d0054070381552512490301d10b400a8005803880d07662031081c0b014002c400d1050064602081e5016103141910104807403850b80c00506000902807134041000c00c5a205051030030107903501145400c075038100300c0701c0140342150451b03502844036403050f00c469100200140c41d1702101d0b0500101415207041500450711a1082a401c84200001201c640e1444540884281c0031910b03a11400c071b0210302c0c02d802c141c94018000500f90b032030304d820818000980c403038900036010f001c45070070110303020750840340032546100d899020b240c90207141c00148418107520074002d40c010440600742c20103158550000304220b02c1018404ca02000c900740300034110f800c25030402e850482004200504021918 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 254855008 1250 254853758 254853779
    0x213060503090304170c010908060402090403110a15142202100e060307021b040903050301120503070f0503090906060c0a030809030d020c010501050405181002070213020d0c09062610 80
    0x440385d9210941024908031800d5034070021904c01800044c00070021070038503401141440c0da0190001c0c0c100030350300c0709002164108225200341380c0c0d4489140c0d684585140103801c0104001810303510503904000208a0100310f0480302004044600381241c075021055080000c2c405141c490402400300740c00e845e010565401018500c1804550050f0031036130083e8130802c000c2d0303e46184d507512503031511150b480440d5001058038196a03074419402040c41c014180a8614003600030000c120b03a01e0400e0410405c0070103c090f00904000341e0b0311410680303626080040c24024a58451010f42c8100c2a6001003881103451300d4003c0c8400c003e5034030f4881550000800c0c2e900c101e40c0c3c5081691581c004210a0403d8440d4030740c40a03c020121010409000030261180210050700010a402180c8403065658000c60042c030400c180d8800c5654025507514540a0000c00518001144105400007042402595148101140340010381400c3e00c0d4000181000000a098010b0384a4500700c04260300401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 254856115 1107 254855008 254855039
    0x2040605040b180423010504110a200f030418090f0b0c0d060f030b0a0e0607110709020c161a0f070602070609150c030213060503090304 60
    0xb40c4010286890240c3d02954000d01e005400c1c0c014200c400202c0f00b403140c2c2c949401c48980c0e45c640c1000103c90020b1894403c00c4001c010420309203110304020100f42d000740d2000d800301c0104540fa1460300316098503206441c2c1c0000340501003c1c40d050004d003182350f08640c0511540310341c0d40d201040d05420384c400816401d50140401c84c040a080b06483c20f210740e1250411103140c2d91000b0460f00302d07203031005880c0080380e100071419000d007901400c2c05022040300140000c0d111040c044501c4907248a406425000c1c990300491080303c140001c1001c21940700041003000a641e034240c1c5901025030040c2d012009030441c01501c0025482919021050701c0c4640d0b4841f9038601340080684909940204003030b00e02007443c0e040111181d09158a2000f41d90200001e0b2403600703040e0100c1c42030050b45210300c20250010070802c0e100c1da0056502000c03620550342400d07540c00000c1101d841 = true := by decide +kernel

theorem cover : BRFrame.Cov 254676258 254856115 := by
  have h0 := BRFrame.cov_init 254676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 254676258 ≤ n) (h2 : n < 254856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
