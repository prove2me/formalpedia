-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4830
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:52:42.057165+00:00
-- url     : https://prove2.me/submissions/92939605-9403-4d1f-aeaf-155dd243bda1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 868525179 ≤ n < 868705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 868526429 1250 868525179 868525183
    0x60c0311070515060406030507060c0f080d020304260d0b06090402071407080a080922150f1d191821110322050a09021e0408030d0c020c090405 63
    0x148080e080c194049903880740014842030301d41d076010107040303270740701d4a403c1045504c41c070803810005025000700490070102d036980640662000380b91360400380d008400d01c014400b0f0240b4040740c8861154445081c03d4001c450114640150455207440d603030b5401044045803220300455644c40c100400840d41e81c2600e10340f02c0f102034079900311030103180b0a164005c80d4a0100148500f0700076007040c0e8060400740072108103c2c0350180050103115807901d035162a5001115409240d075880c1c1c40e07070a01c11005051108105000786141e11805440c4400c90b41d04424000320141c00340c03c10b0030b603483c003905001d0035400c40020b06001e03202102a50301043c012014000e40c11120a200e003a02c624941280c03c3e08101142e800d9100d41211031603400400509981c2d8590b0712001e0401080c000c82103500e41c1d92600040c080c4851a8425074802e900006d420303803000c0c11500e80c90a11b184038100c907801c160038901e6442d0f40c0d010708015401042d5641d0300c104056030007044030341c01c0540300805402291401c0d10f0103079 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 868527679 1250 868526429 868526443
    0x30115060201142d0705071a01050310060b070807020a030c3005061501022d010b0a1d0a0f09060905010b040b01080f1e0903090306010b0c0a060c03110705 68
    0x83d0300741c030b0004034a0410800c581c00b500b81c40200c0c40081000540e0707040068910f0064550000e000b03007000410b0014040600c42c5440602c100301e502d125603d82818903040072800460482003900d001002d2240d006a031064a41081c0c01c86c24058451200344085104a05d160300007070b0a40020550004000761511040c2084420780c020051206858000340012110740e047c00030030039041080010b001c805100800f01e0007410500c111500b1100751040404050451150310181b500070840300400e0403000d002e495041703103003aa035699100d071624102502c0340c050300c82d0045640c151800030414010303080e00562400e1041c03003820051025649403180082c03480520441d002d500781201c1c10141d141a101d00d180040040e10b510311560380f49602c2c4440540002c0c001c0144501c1001d41031604209001e030b8920500300c405c015550348481c001010310f402c6050307000c000c03c52020003c0305072800703000c50326989540d840302000c01ea81218039416070140074450b80c010340040e0049000c009101c0001440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 868528929 1250 868527679 868527701
    0x200c012a0e04060302030d08040203070b0d0207050c01020718110f03070302120c0327031e130b03010312030509251e0b160f060204060309051603050606010e030115060201 75
    0x724090a00603050000f600d00070b100181d8583c002a034500301090042c500598000e2000f0151140c80b500c44011540540124081003007969020544070208082040240004402400100103051030141e00b280316090b24200f8803400e40d140c81801d0248203922007510301d01540724440b03035241d16080100a0003504040c561901004003100419aa404544216809480c2d50303808512120007800f07200e00e841501460f0803402e03200400031010201e503010b040704030205640c4101e941d5500a68403a001d0701c070080d04400c0480302d04000410015850041d401314650050a011409644400556003001c0346104060550341c2d1040303407190300900342c80c640001c2c0d6101d20000c201c2140320145410844509000700c80741c4000070070408003400c07102a10604480e106500291200507103030f5030101030b40c04c298403900209441e0011078040040a00a1101c13103024030807038480311880d507101d482e82c0b00c00140415050180030f00d01d002030307a1003c5d001765040300034a511040d601503995000074002e095a01d90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 868530179 1250 868528929 868528937
    0x2091f080f160507020a05030307110a0902030106120e0115180c02060c04062313170f060612070519080601061e0f0c051519200c012a 59
    0xd008480703600c44240500400b001a6510851498083c1c655521903103080ea8441540700300000c2561f410401060514881e0604250401464040c080c030b20b1055002080007a00520051141c20307403210b0300c11080c400400c004104a0604116280103001403030f45030102504000f00401c0601c01a40d054100b8a440d1b40708004850700c6440880e190340c020b460b0103190030010001003182c913205240c3c40b0401005a2441e148000d034805440841d9404001d00b0700c4041d0b511102002010011042c440c0101c11040207016842c4148490079100c20004010521810030104400340440003040390401600b0050070035611111200218005421035224207100c610a02001180c880d10a580c00a8a0001001483c0509100070010348032041c4d40c0c80c2023003c0000c00300b106404940204040e0485194001c803c440710b080c00c0c0d031503407400d6802918950409003031110806152120b010a80d111000c14015580c80f003400b0000b06001d0b00c0c00030300703803210070040c1d00007030f03c4058207000d81e0340402459480b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 868531429 1250 868530179 868530181
    0x2c0d021b0105090405070512130b070f050910091a0706150e0103060e011e020a1404120209130c030b07080601022b090305030d0605120a110607030302091f08 69
    0x80200c0c86828016a003a00045041c0050149420542c004541105403420f080e8101401501003d0010742c04941182050b50742d03002c0e510074029018825908000c01d03141c100050f081000c03000e0514420301c6032050050700c0906851014921400700304002e00401102050205600e186206444c1c0210405a40701494018600e01125200c0110000c4810100c00c0e9505a0b02c2c64581c03800400e05041c0c18544c0e5521040442c00b80001030b85480125140c030780c1d0068440001300d00003480c8144550300701440c21000c00051013020410200c00300e0050b811144003030705503150149030301c144441150040c4200d0000002200300304040798164403580030b50f900d114442d51404012641c502528040e405d446049802c603681d0b040320852040131405490614075821662540d03031618541c00701441c2d5850381e90310b00050069182900c0e00b070608110490003000150015204c02c0f491641c3c86074103c0c03190100142e00720030580030727406491030307001300811130070a141505101d55090756242d2000000259210 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 868532679 1250 868531429 868531453
    0xc0c21050c040e191e030314070e030309060a03060b030f04120203180d0206121014040603020906190f08030315030f06010302190f090b03120304080d2c0d02 69
    0x4411442c140004100920340c0600c002007078034101d0001c000030b56a1301144d07500c4180300320940c42c3ca166211b00c0b80e07a0001d039880c3d2240c0d01c461911400360602c0100841060740c3c2815543c0002036230a0000d04030394a598035a5500c0080e002048a98071480d1b17852000700401c80320980200002c0d01c114068a00440307500901c131000c980720310a8981021007500c402400b00050f080500312040242d2000c1c1405180429148a000b541c2d001214140030581d0340c00c0c4148611858811411480d0030252414010242980d000600d00200148600d0180103441c851044045500c05d4080091004040380b40010307032604241601d075401241c415020500c01c000700c48540c18001920081c8041000c05004c451f4210b83c204170f98840e110200c1060362242c070001046d20b091a070800c5d00186000c080016030109942d00b45030078803034001841c400f940c4043c010400400d5450088039011228844c0c001040f1000d400c076243e02c4034001c41e540b413904e070040314140107441c070018030044501c800f6002c07580d0162000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 868533929 1250 868532679 868532681
    0x50f0f03070b0a02300603011d120306040603020604030f17180432010f1e09090f0f08071403040f12210513090204060804030c0c21050c04 61
    0x300000a15a10103200010a40c02d8280d005c1d09140d81c074103400c400b000c070645100f104100c0190041c100301003600c0040c01882d117001d22030480b006491880000d41d6990030b411aa03158000f810304844403500c0080000d001f070707a5903804074000d0b43e030042c46c00361116200d0615000c001b191142c200d900100000241c28056101003d85070003d45c02c203403106080e00346d0000d2101038604501c510301c40b0360004a0000f62031101d20000303034003041040004030345503152401c026081c41065000301d100441003000e6002c1e903802c0d010080c0503110409030105500d0301e68500f011440036462009002c2c2107801091104020342c250090482038012120754445040694103a5120b21881c8107001d049020380750100202042582d030300602c5401000303020342500c07c0031589800d40e8070207040324000940016051300c20380700c0700004402410290384110700b07060234920050704d880e20260015050085d4032140c0404c0005000303ea070040c2040c80c06032003150b0041141101000e82c000030481309801005c003503015604007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 868535179 1250 868533929 868533937
    0x120307020f0604080418060e181b0303120709030602070c060e0f01050412030903060c0e100305040f1713080d12050411010e030f03030c070b0106020105092104050d050f0f03 76
    0x16540c90302e003900e003d0942071580d06c1e80b882080d44613118803001500022404485100e03a036001c4030b05031440c90181c8a10b0505103014000000184040c1702c031000303510b00009640081e042d800080401e078036080070550b6600042d0b1720040405000044d8201041840c00c1d542c000c8035229251401c80107590010421008074000701e140c0010800d02c0204201c070096980e0b140901d002c4d00709000790755141e0b1124000d8034030054200021a04000700961142001481007000d004240303410002c07820035950711101840742d1140a420001519400405c5800003011212200606121105015544d13914243c8840c0c0c0b426030300010071541d980e00825040680a26403080b13a000241140e4072020074015188915690242d1750980f00b2075102815981d410002540103481242c11039842da0750b640740840c0214816007000d811a41058107200c402040050901c0031040000a5000f01d40440d208081c8580150b5102c0d071307801080884084e0078402c000c59409040803100003540d1001e14981001590307481 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 868536429 1250 868535179 868535183
    0x50601080f19021606140705070807200301020a210614040c090f0305070e13120f0e1e04060b1303030f0509060a11010c031802010309020a08120307020f0604 69
    0x14100000440c0750250b4010102c481c095450014207042c000c040c45a440c841c5410211110740d550417507001c84044800040c2da00c801107107040c5141c0a42581d0b50400750045070030084c079140c002c0905030051405210180c015400c00307002152561040c0700000c0941c030140c0d01d5608088034241c034800b1620840e014900941e4140d240103030034040000288002400c3c403e1400081020580340480d809940050001c02140200700a00c6a2420a02484000701019000034643c1d020424a1000204d444d8418051030620f400c1c481084491103609441c2a0794140c1c1042d80100341d0000390030381d5110100c0d20b0720741cbc0005403803c00c00582c0342d081400c0d0038861100d480c071406c0110071040001038071520202001840d9490414141422840400d040e80c00c01c1524002042503015203d060034024490f60348110b1b61480c0912400100c140480001001020040d0405498881400c150f40f0b811000740d009110703240407141d543d00c041c0c200031843e0f0801d8980d2030040c002e0600c1c01c0709a0380c0009031a801a6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 868537679 1250 868536429 868536451
    0x7021203090612100e07020f01110405100f0903080f0c0c121e10060e150901030320160e10060e060412050c03010e1b060f04030b0603030d0e010603020405060108 71
    0x1c2c4080001480f6290000c11915a04101002c00b1400240400d00c040c0520181c3d00105424952540e40d9429070392400c14003c5102e0060004104555540d0b45480c001c20b0141440c1c1290314030b08600b1515211150009013005800282c07000c46541020000d12044044009407440b4284860802001451448003143d00340c0c024504110381c0e00d00c2c1d1504460055038402100c4100c4401000e15007603a16640c01402290320103070400c00001d869071850242d29a049469105940c1035990127441072201443c8101003138a115114404401e0400413050000611501000b03626500c003200007010800b210108610b02c10b0050001d4200e0041da00c040300e85000509040c1024245110b19202000c4074500391068462943c0414480d1428818042c441ca8000050704201c03200fa840b240114456508a501450f000c00404034148004429102503a81c8405180c00035118900000e01e035014030009100300a182c100b20a00840055103e4030440b4400e4500b07000940c0c8007801500e40761411a1000c102d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 868538929 1250 868537679 868537687
    0x8060f010503100501032c0a1104150b0c030708030f150a06020a020f1c03020705011d0a17070e07030905060627060a1710060801060b070f030212030408070212030906 73
    0x1941c017a4014000005c0c04281c0e131180440c40d031f1068110302c0c050520601c040c1d041601c541e810f01c10380c3c41d032034500202c080d41c050040d540403550321040510310344950030381d580d03000c200c6c3d0f081d02c10306000302c800312a0030040654890610160140c020b000075585100001c0600100900034100f41b000300f42199a2030b00684003900543d000e00000802c10200c0c9036000394002402112106000710b51151203001e40c1c010607595013000009030207240007440a041011215000000d55a00c201c04d52003625140000c1310441c2e9000da0105140c0010b80d008440b00c0b15040e801c005400d81d1641c40b405110b4001c00854400351130740c6051007400c5046a00e020040821907101060281401210a8010102074810000d4565401c0c1807210407480a00d5900f0580001600e00104400c4c0c0c015240509980e178020042c0b02e10f44104a2054400c01a009201500e00032810b41854000d00000310f4100c90980b14540d6813600349440d14144e03210603012480f409170030501e032030514400402d644205a0141c007030342c50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 868540179 1250 868538929 868538939
    0x105040e1612020103110d0c02010b031c0c02031e102007140a02090117010f05071e1202041716060e061605030706090308130c0b0c0a1208060f01050310 67
    0x400701002d05074140354441d60071b10540a40c40c002401c940c00c04040000d04901000c0d4000c2c02d440030f9041441c442d5000c8034202411142c1c401011008200504180111002a2010038149005e034805600e0313140b12b05030700d2406810003003081c25209004a4040010758401c03080c554950380d0741c0110310a101380a03c000310001d4400e03500300d080101e5010444018603071650024810070006d82140100145840008600000c00d018078800701c080c10340c0a01c054944400c00030300024000c204603980100100348421860b0044400e00d101c2d0b06110030075542c8649070b000d203007445408100c0e030000501c106010842111022884841070b9411a5030381112840000100103507500140c0424242e4802114881c0010304104018104288140c0000c41c0c080d805080107400707085c0080c54005030014100300b410028692009000658184d0202152110804c0190515003040c1d01c00c014030600140e000480c1c4a40c204602500c501001c5a0b40031007030500b600115a54007003903800c03000e1024074a0302808 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 868541429 1250 868540179 868540199
    0x60302030c040620011b091d1b1b0604121706060c01020909011409070c030503130c03020603240f0d060c0521010e0a051303030c0e030a08030105040e16 67
    0x20f100c840c031a09003000406a03131351007401c5980740000400041200d000c41281180c11101c0c65004048501d0040780c202c2c161110200b40000007080811015a102400034500388810142e03a40714465144c0034501107890782c440c03951030b01d007075030190f60035003101d00903c801d40e1046148000c0d200c4190000585601c9050502031150050384500c0300e10f54080c4000c9581d5160080c230280203000c3d4600302101307030703000606112100c4000350413a4108240742c20b0003004682c2040881c0c0c3c20000300034101c0040e10150500306d04a00300d60b00b00960003040002441029044a0461007140d1a0300124030198800d4030b00700150241d400002941203104443c0503008100b0545c4803840314081410103601c0c000e24880c907907821880d400c0c4c0705414018000010f0000840c0000350a52204c991402007100d818001201c1491820900c0020201604c0e050b0406480e0f102e540079004100c0c024040340e08a903c5480d0145080c0c009000e1540a24907000c6803e40c010390004001d40317202081080c2180e21400c002e0014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 868542679 1250 868541429 868541447
    0x10e0f01030e0d080610080705220f0b0307030c020607020c0108150a03150509070e0f060d0b07030c021c05070332041418131e0c0f060302030c0406 65
    0x281410740d2200d492042c014140140d0409940d107650f4590385242840801807400d201240000410000c40100003080c0c0d0003000712404468080c00c2c19100203440300642c20150381d0703500700506242040b0400039003110000055802200592000d01445101d204100ea844004840c0301006a000e00584402c41d401050343c1e80c2c10020b65002c0c050159444004a20141901e81c002c48402c60044d00441140d1858403071150000d00e0b21026104607490018030b424400c0000e400705501200380703000300f04030f9034440000001103580180c82000c80d181102d0090000c04444a4800240c06192641518042482c074100a419803075141d107400d09596850494140c840b00d0340b00c42c1508550800154942441c0c0c40018100c100544804d9442e418201ca040043c000344407184e008403d0060f80b20040390b403e885e0710b03274810000c42221600c800c203410036001c01038071402c0784603500c2441d116034010b2204804003030b800d9409030052602d13500d507511412000c0340702c110741040706000d00740700c1404131310f1107243c1d45 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 868543929 1250 868542679 868542709
    0x31401110d090c0504110415020f030a0f0e0a1707050102070b0f0a1403040f031b03020a08030c0913020403060c022a12010f050901060512060c25150506060702010e 72
    0x1843e00d445001007021540e60214544481078081030411013a022411251500d42c89480a04014030380a15003503981c2c0120071000051000850040c0061751090310360b291120030041ca060315507590740e61050196041001c541c0c48600541902158a50000440104039480e16821601e40707005142c0703410300c1c0d0304965003020800a0341140188804800750186010343d000d03040311040001d072403801804030510005c1d200c01140141e50040701081e0041200b01001e60003030046030352aa030f4010f028400e4494840125403103010041009080700540c0c0c00307481030340d01c100c0040007460b02965042e607807044050490f041c403036407480012038803030460034074204041c10152414612840140703119003522455001400c2d43c9645008000880c1000d01900d00207007400c0c2c54030155501011642030316001c005000c4042c1c000c0000b0102c2c0140c4040c00c510748145071510142d040903100e450070f40344a0310349164080c519428880403520700c0c981030084485d00340e816114030f144a0302d0541803003102e0340e45d103100f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 868545179 1250 868543929 868543943
    0x90106030c0303020c090f0f0624070302010b030705030c090a1505100e03071505121312050406120615030f090c12021c050706053001031401110d09 65
    0x1000804111001d4080c0d486038018103001038182c401c0c0134003528000c100d820b840c80d00c14140804d015840d100386800c0b400940b56444040403450481a040742c03081a12403100c0c0c0005860401c2c90303819803201c144402c080f07041d11000d1b40d0ba00100340e515011b5406607903000e2030441c0410701d40801580081528000b840281d100e0558400000b2030300030711f0304500c0000c41c9070b81c07a59064600e014030421002c0d1241d640e02c3d000c15464480000c289000752407114410050710400700d0210301c248800c080905d81e11901110b00283c810303000174101d030014424203022640c4060044010101070180c0e005944026010208898244030214081c1c03c0a00030f0000da1580c030a50040801c010a40b010003400d60b65400b0301d080b506520500960885091742d90300352002ca48a1100000c80115051089580a1038440d4456601d03c1c003c0e43e500c80403e04100c0440804042c219500103102c107802d04907402090240d4290b460300e1001070a8900080c4c07250349000040203414450ba80c0c55000444260080d09 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 868546429 1250 868545179 868545191
    0x6022a1e0622050c03070608150405070f050a03090203070f0806160c060b01120e0717490e040b0409030f051615020301031202240a0e1906110403080904050901 70
    0x1c017282c02d04407280c00010000f03083c03104002800328440140500148140c40800880c900110014030455400190340100407000407244031883c8280c0041c0040d07030b0014140da041c20740c0d07001c2000c95540310317200c3c0c0d0a0600880c0c000032886590b030340b469880120592520100f4042c1d542e6a1303401008800000d0b0b042c1b210078001640044100e114038081102100300800345c4a041c21701990f0390710289000401240d000f2540e81403161810100c1c402c9030445044000c8c1d1203540503c410781c4890300c400e5103054481400d81d00e01565a07005005800c0c400c004e48003007007030104100520094443e4038002802046a0782441c050b070320300c500010240c01c041c2041c3c40000c14402e0340c58013581d24100060444035a004801030050200314180030b00d25042600052200c03203d0440b8843c00078000d6100d9230b4400506000007406030845402020301d481003002907501003418419400d09503000310302d00743c420750318003d0800105200101141e01307480d0070070521410f0020034001c000207032400402c01d80c2c0d01e540b0b0794 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 868547679 1250 868546429 868546453
    0xb0f0403180e1609210b01120c030b070309081914040302030d0806010905120102180f0904060c1e020618010203150d05070b03160e0901060c06022a1e062205 69
    0x540c000341000389500b551540081410886c00e00700c410f070801000e5408a415820016220305501300449511100c011020341e68000164000c04100901800101c000600752442da42e000403038010510068480034000c07030b100142c954a902840c000250190311250701d06441901501c0920f0f440141458240401502c60011600481c0443d60300c07a100d03074001c5000d901400c080f01189000c02d04c1954088a000d09480010350f040402620240c0020b503100c81c0504018840c0240d05650300240444140c0c031185188002c2d40d410007151001035980f012041c21803000018000c9901071005031a0014103c00c00100300000e01c10010000c44440c410148005501007140b000b6501c2100310411000e140201d04101070440c2141003c103502c9416188014001d07590048100311700e032a00b154005886400c4c01861504445030700c00c20344a9260044071003181c5900c001500e000003072904090101b8030244d2140950768203c2921002d181c0e20381c010211582c1801c10750801417440c000c13011076079450412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 868548929 1250 868547679 868547699
    0x7090b0d0818030f01020c0c04020c0a0209150d0c05010f020105091c020a0506040317010909030c0602030a0b0d0510110c0c060705031207082409071b0b0f0403180e1609 74
    0x90b984913242c1d4010903020300241007030104030709654094805614049c160310641352a8626404000d2196040d1800308020034403211a4407081e1001800416808a9600b401c00104e00740d4411a40083c01c640414a0800c1c4180036483c016802c54004000140012084c40130010b41c3c245480110303c00d414110f0702044041100c2409280603840d07405031070001342c07090208820140c0064a00500300244140003d61140074031007110b400c4600162691992580312018180b4800d80e5540403180454010911501080915a4501c0740e00704003c8080071042c41032850095010b04540c54010681c0c3d805203003005001424000e1154094038980220850440e00c241800c0e22203500055410003041401c480711519103508502111100c0060360388180012201040188500104841c0b0000844c881714140840c80b00f941e4403081803070180c40d140030b00343e200c1c080895041d0001443e0030341282c408900f0322566015036a1303c40410565030b50b40c4181c00782514400408104000703080000041e08010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 868550179 1250 868548929 868548943
    0x9010b0402071506050121020f07050d0201060e1005060f0a03150905160302121f0513140f010f09050907120b0f09010c020714040e060f0907090b0d081803 68
    0x400d08140d00704504443d86401240d2054000310b041c0248503c003203400398a40d0761102040c00e907944c00035a4400210080e55064011030b04000c0c0309101740c0c50100301164064102c0c00903104440c00208145c1d82e00159139129044070b104440d0040f40030442203020541c400300074004206d09003408a00507410580340444a00140c1c09040d03c20368442c140b00040307080420034500c21003545025400c100607400713084094640030340804210310401d00c046802e00b070003203109001844001c01c018481d0303445c565610050001510b2000c8595119800a114002800b0300710f81a00c8000c4052480e042c1005075400042101078107541c02407180c4a0000340d0a40400b4200c5501441642251400d042203031042110050280484215034100502c1c180703c941e00051000482c1c01d01080d4600d40c84a11011500400d54515a200384e0700610040051060019288602503501c200850740304995803010542203c14200c001c5501151980d041000f16844901411079210b01d4480f0009612a5000091414107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 868551429 1250 868550179 868550183
    0x11202091b1908060301050c091903050105011503050105060a0504060f050d0c09051801230d0b101a090306010608040231060e0603060a0507021f1a030a02011709010b040207 76
    0x502d98444000b19074400c10031034100340240c0080c003550a26031a45203182c02003405182c00380d4051740c040041080741040f400300441c0c02800801c802e5845d805590003100c0c0042c5813101282c107080000400c0c1c10030750210760902c849580da4600f41401e2107800c403100c042140f41001008003d000e400b40d01401d5105030500c82c14281c1300c3d4400d2501d04020b202840504462100051049900400144110b00c072a0f41039a888485404a0b01c0b0404000605c40c010b004409441c44000e40b00304841c036a144103d18040c1d44825000c418003003130f10261980307d841001c0d0429090703005240100032450240c124260460300c000e0080001c2004c04807101c82007046170010900701d0849074400b5040041ca481581c01400e0f411031010070131b20b03045000c40c1e5100006040e4210072540d0b0070003d40b030700b0301c248031350032803401500c05218001040d00c4c070b0000501a480510410140d411510101516001405022955040c1c480e01d0444400441c0f080c402c110003400110f055413507114600301540d5500c01002201c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 868552679 1250 868551429 868551457
    0x7260c0309011d0307351516050406050d111207080c040308070f0201110d2f060411060405130518010606080f0a06030b09031e03011202091b 62
    0x900c2180010411151807000c000104980d1507004610303103000c01d10501ba02d40b06540c03150b4080f22290508a07900304a001c0c444140d200b0030f2400d056120204248064000f44810050a520754001c9904c414018554400108400300810003046010f0005401000310b4184c000a1880c1c400240c01040c1d48410104041c500c14503007045103c0c0c4c1c00016507a08071020b1140b10341004e0642d90b8148d403c2c070030034401a1080411561307510442e0310844440720391b501c0c83c2082e28015000742901800031618400c2c495050b015440c0203203d8854004101000d5140c140e009148548540c1c031140c5483c901d18115941200007000041801c1d11110000c06003606103030f1001449282c0041c3e01d08040a44070385540499040c030004005040d8455801e6810030040701c400c4009485010b01500240f1032a4001040d03400300c20100145036001101601484011400341100010260305017442c0d072000340a16008401e60031a00009418404140759105203640c84060090709031162001c2903411100b0440401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 868553929 1250 868552679 868552687
    0x111b0a0606063c030f020903030f120c0703171e0108030406031b0e060c0f1218010207030b13110a03051e19060f090b100f061407260c03 60
    0xf025000584040360703040c2c04908181c0c580e5014805044003019210826442e4034000340000010383c11500030310802405c50340d84000c58108002c8a403c01410300d80d4504003240040c1507118410201d60b251a03150b55080012240d005058000d0749016001d8410850f03040350540c2e030b5014224801e4060700c40740c40103548881ca0100010140d03040c01d6030b0061410000c007040604035400c50004021100100c60054031031450b00380841c6400408115505944240d241802201c00c032130b40203020340c24180485550041c0001e005a81d00d003040d1000816524032980010002d03200401440500c511800c120b4010007080c000068003042c0540081c0c540b0341010806403015101d141c00140c4501c07400024001034400d5914000300e80d402084003408840d2940416070001c01c1c507500c5004c8103a8441060003642c01c050040702c4d80749046000b1a000f0681000002c00c2c43c0340541e0446910071001c4c604c00e403412406076103040b40042002207242d1079075030b500f00300305241d42284003500340c80d08075000950311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 868555179 1250 868553929 868553957
    0x70b21070915021c03050624280207051c0b180715050d11160f0605070306030503160c0503120d05064f1a0301111b0a060606 55
    0x2e40d041009082554060300e12501e240408420782c04c1c101c0c40509001600c1d640344000b094601511162012500100c225000203001c1c28a01401c0100107507802d02600201c9480c100c40a07420041c1440050f9000600410051a10700d80340d101c860340c05503081056000300e5443e440701010940d9180b021f0707580740d001c100c1d014804001c8440103080d0941c0790030792808003010140403841040c01000001e80c03246175004030758805100b2200f001061090340c0110658034103110a100040f508101d8070702d801e10022071b81c2e0622070b018500640b90050091032410b111182c0d520b503044100041112080100c03240040c46581c10f000d8110070008000005a6442000120a0445100810700c1340b007030307180b40d4503a00200c0030040c081400040100e2036030044d02c40ca400310b0a84000d80a0320a0000400c445118000c00094120a080103000c003072080c000d40c2c50300700301400d1b11103002c13000114100038018200391112508207101e0400c408026500000000c0e102d071750070340d4240d42005012460920407046 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 868556429 1250 868555179 868555199
    0x702220f020d060e070906080c0a03021c33090515032e050103030507020d050c060f120a0908070b1308070803160801030203070b1e0729010503070b210709 68
    0x70707001d1030700e00e0035155480c140100234009450160180940c01e0020600011041c0690304848850506800790f240594400340c0d0302c0c0280c00b07001d6240060015205440045d0307102048900308001c0100765400304681482c038100024400140000512160010891041d4805200c2c0c9840060300c2c3c11a00c1d000d9100f40041c469904800c02d104503030901c0d000040001c2175200054511140d8101c3d1004081009820710130303e040b050241c943d41c4072400080c2008001041e1000b000c0f55010213000307002d40d5645404072000c5404502015084005c01c01413400050003030032a840d40011210a0300a00c554541c0321005650001e15049032288400424402e80c41228a1050441c0700140352448540d0b041d81d0110740c80314a14403559a904401103200450315950342605003100500111481c0c4401d401e041c2403130088102040e00850a500c91000c0b10740c061242c880c941a43e001a000b04402d51030400160150351044030398011032140040c1183c0e1043d41c04d102c1e5400350013203a80c3c032b900842c10048241 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 868557679 1250 868556429 868556431
    0x31314030c060106050319050721060b0f0f120a0603143721140f04140a090e01060807051009030b06030a02030d0f12020702220f020d060e 61
    0x250180e0080c41500d6410340005074940c1959514a0314039100e4443c4848420fa000c00e0300030100400c0e080104001c0050360000d40c80808121003822a900307500000524412592107000d680004281005901d16002442c1e0080000c02c840c00c2c1031515241b40c11f1882000b910050b2013001c54551603490400c24080040c4120382a036010030054140c000b01401d09078140c4420010032803075445903030021500c1c5207404048240301600020007400241e010740030201903080b940785001c04a503485440c0300c003640c016820784039801032402c0514a0581009035122034000703a0500554480342440d0003084c03088940c0104517800c541040003041281c10000003d05054094218a00500b40b00740341d09070b02a8041d640a003203d0300038407445850345441c00840c1c1003045803600650148602480300e140c0c0d41d44030102c07120b58021551880401c810b1140882c041e40724128011307502c00080381ca02611400c001d0030303e00d000e002d1072000007402d130804141c0301d05a170011109142056540c02040022016083e244c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 868558929 1250 868557679 868557713
    0xc0a0f03140f0a020d0f0e01030504050f030f09041a030618011d0a030e0102010c050906090406080d0801061103030403120e0109060f090b0f10030305030c0f04120203100c320313 78
    0x86e01c140040c0b1000030a110704c43d00c0100d0405403158040341c1400f00a202561441c6c00850941c0d030b030303241030381c1e40308180da440360100ca40224034020701032800c0b00e030f20007080092040050280139942c941c40200c0100c4004031030b600b6084d558841c070007004115400d4028800c40400c90251800888505000e000c070300d00f003140b150569040072955030945510101702c0b40d401c1d5040340d5080c0c40f5400080424000c100c1c5402229480c864501381580b0b56800940c110304032942a41c4540900361020a4681c8030b002c19a4000c2c0810107210000340c00000a400c42c0010f0030101c40006448949600c950741621071032820b1001b9a03a43c2c10324402444600c0301c9440d4031001d9105c50b5400d41c1001392248540d1240391001800f0898080003003400c1801c91011110410b001d201c40c1502c441d1a01401e100130104402e0407407080c40780303651074402e6100074002c81072241c0d410b0321002054114036040e9a1015807d41c026500c01100f01500c03603441c41480e01071406450304d40101b090401c5d1601c1c1c101684924840c803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 868560179 1250 868558929 868558937
    0x91c2d08040311011b1112360117070216170705040501080712020112110301151d0108130c080d03050c121303090510081b0c0a0f03140f0a020d 63
    0x3e549043d0030113a0b200d40001719940b9001100c002020102400c001c404042100152400240d05150400d01074032002540290710b40c10f0348151b10160000700c2100d1000c00c95010580101d241d540d0090b02e0801c8590151143c0107560a002c1c00c0c8045400c4000c10350007406542a82d4817031000303d1141041103e001d02000e580c2001254182201d056480981d4800c000d020254000d0850071a40700b601d030036664401002d41030102d5680721800b9500c0381c00900400880040b04000c503d912031240d020707210507480d103111021180359980c00458030540002d140c0301c00c00e4890082a800104074070401c100400500019000d84100c503c002000d1340d501810b4096240400d005114420349076000d45600040090100301e1b86032564034098407849515480a0f50008040223440b49103500902424425445290040d001a485071468007890056195806965018800400005031b00031120101980a401c082c8800183c6100d0129a0360000452080000000c24a40e984980400422030702081e2424 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 868561429 1250 868560179 868560191
    0x8010c0206010b2101120312020a0509211e0c06042303070911070506101a0c031b0d0e030703150b0d0204061508091c2d0804031101 58
    0x48000e6898006000e030821143c000500c00740da150928001403c1020808500c454540c0d40e80140e00500400c10000e0300403940401c1c00c1111518517100b02c035039114294a40c2c5003001c8080c4103120b91032480440000303003044070040d07010030108200210090b5003216001407901202c1c28591a09042e10a04960b000750028081800700d180199180441701065131202e444085140001130b261a445600040d01c0500e0442c00e600f102d6007901c020a0110f000b00e04869068441c1c0205883c0c08103a445008030442031101550300c0c40380c4c0180145441c00111080b01d04003403014031403803a00303080c030780e002d0ba282c0d40800c04004485801100400b01440100d0180c142e0700c0c555240d8200740130340308840c071111591700c1a41c00456540c0402c02e09059801410800c0030300c0d10351980d0a180e100c0076214001103900302c3c0000e025604001400c072003443c42600c030b84118210450040d101d00400b038944000d10742511901c4808801d1440c0e41c02850015941c55403254185402c01401030074140940c0c101c1a41401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 868562679 1250 868561429 868561451
    0x1e0603050307080a0c1e03110c0f060d06030c080c09091b040c111002030a1107020d030c0c091806050901020703020705131d06010906080312071b0213150801 69
    0x1100b0340c0e410540001e8203d55900220310200e420200c4000d008102003840480c07001124042c1e141c40312100d2003502e0b48118511410b403030300d680d010090042580100000b00750705050802c003004d4542c0d0241c401d408070300d05440b50f42d80caa007102150004400c40d072140c80d00c0320385442e02046c035035002020311014040350a90005210604a030070103005014607150642e800201384150b0101651400407000c0d1038410400f1202000030f9032080d180422843d040503807002078030440d502254009903000344103501d0101c0c03580d029100520200420b0710380300318000c800030340c04004c1c0c0109101d284140c213494041ca2a00d2800d0703412602c029054055580c418803907a000203030005548800d6882c1101c1c2d142c0c0c00c8205164a0002e48044201859910004450305071603042c002206030595149640a10009849074401543c078000d0458603960301502030045102c1d240507000b1101c003505d401c1c4280e03540f003d407078002c2174000d402e2050000090765a56000303600200791103044c41c0035150b00b03c02070201800031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 868563929 1250 868562679 868562683
    0x1150522020a091707050405070f090e1506070809030111070f02040e03211915120314070b040b0c090102030403150f050106090f0e01060c0f14060a1e060305 69
    0xd030405104294006012103185008441410040040842a0b200880c124400c2c40d22400b5a1241d14000d90501021030400d5000d0fa454000034078040c3d0740c000c2180e00d405000c4032035940182024098003d48155500d140d1614401800b120380200320310351790f9603184c00030b060071161003101030070700d031001400090b000580c04805424040d40445e800f10300c68401c440214190b10800d9960710500a4410a43c4c1c0321043c0d8045013849070f44981074047d40c1c40904e4818500f81ca030002503c0d560b4041c014014044c0703084603568484524001c0c5003410710f0450320705020131031f0350207180c050b03941d80803000800042001001c21181d0005212007030714104042000080d45c0c81c000d60000070300703100b2414107240441c900b9622020011055440030700803540c0d2440003810840da24000c1c110111140440407810010f1010200d04075036607586c0300452002c00f62070b0340905861224003240e034020b604401400445d020840d0034001c45840c00c0000e40380d03100c8483d00d9207a0101c00140d054a80c14400100007080380 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 868565179 1250 868563929 868563979
    0x109021801030b03101a0102120a20190b1618060c020402090904060c08070e010c1203021306030515010e030c09040f290609040b0402041505030f011505 67
    0xc00c2c00c0c089003014008000a0404008101c0240914078140d9035099400d8050303c400c0c2c100c0001e0b025224030003110760303030032034140700b540801e00102e40103c1c2c410900341c030b885640310301e81c501d4541070703070b4652a048840c00b80f0305603090b0b025101c101c040c1d0180100456021402c000040301810302005080218a82c0070004001c1d1140b10b0900c84d007040e8440039034903160119094410014902e000a140078900140100420254200050a80400123078540e0185400c40c44001058407540f15140c4240da400a81d200703100c82803403c0580901040303002c1054159440041c1010b610003190310f14001d482202041c40450300300341000011584042e9607100440e6480724001e040e240340d1034035070781d6080500c041e01295900501c00420400c030240d41d6074100c580c118080c15040d081d4502c54544034104040f0300750030364014040100c20070124006241c640c0c45810040800301107440160303591030019040558440703a030060759441d072991401480403414804042c00007140c40b41c0e0001d08441c0c09007520f1030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 868566429 1250 868565179 868565227
    0x909050c0304031d01020a0f050f060609150409150c0305060f01030c1223070503100b0c0c010c0302280c090e030304080a0e1c15110715180b040b010902 67
    0x2064100611151b4802e01811000d107811400303881454680385841e640d14510710160b4415401520045002490640d040b41e000700b44100d00c101d1401a85030400006000c81c100485900384614400c0c00302e070f10a4043e0301101000d5807400501450040c0605c100001c554000f14101481d008201071103540040c0b6040c01c204c0342c1000020700f00044500c5c800140c600102030121814441d0400ca03580c0d0380031008510031964000034405503503548080e0400c1d802000942d1450f60405124104036520522940411070702a2044170400450750b00c0034412001510803480745004446201310078000c000b494200140ba00c01d508105141c0e075800665242c1c000940000c18181c000103501a605104c1c08603054814001448800e0081204032003424050f9280001c6800c0303640003142d000034075100c0c8900c0340a5411150200c0ca424860f40d20907a81c0f0089100560707006603605011400d422448600042135803140305962207900703090400c40e1340b07070343d059000010950040041543d10300a050155010306 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 868567679 1250 868566429 868566467
    0x613060c0507050604030b01140402041a1309180311030909010512012c0f0f07090e03070803070c150507020c040f140705130f0e0f1305010203070909050c030403 71
    0x1001494500c0c201803243c0c2c0299030110300400c020080c0194400900d041350205650800518010ba051200340d0141c0d00c202170044030440d1440f1000e02251000300f00e00c5000300041c0c01c0d416140d02416007111121401d800c3d50a919114100c01c0640040824109440f080021801c003803040300003414022050040c1c0d4014000d00e4440c6d044001700350011881c4d0005074030740c20300300c00ca200303c40028440d0031401d4080030706c00d03070110468085011511001c4001003102a121140c184901c0d17202034001a10b0a01141c4010016840404c3c1680007860240c445030382d50f01748040180c201200b0340318403044100356280c070b001c0a2102282d00019000308102d0240d07008540b19500782003240091840d000e180b00ea4ad0520001c202e030150780600100b81c00081840784050032511100d54241c0342e0198003038000c030702c060b4802281d03401c40d001240c1680f114424661010388041d5981d0982a40c10540b4482d002c00c404090620003000c150007400e52020564404600394902600c0040c007510b08598181640 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 868568929 1250 868567679 868567697
    0x30903050c0d0305370e070e0103060c110f03070b0c090d050706031a0d02060d09120804060b040504050c190807080f01050114100305090a0609060b010905061306 71
    0x160280d000d5406050100c070980d0414040d404014003c2e0404607525080c14a00e240781000d0034150301100da05110a6000281c2c01d50043c100201c004c00c84100310814900c64100f00040780045034440d28080c500c90800468030815444c00640301c10402e203090760598028242e040710031440042500c0c00d8a402c40703205803030343e11017044000003440f0303464590f50489060700e185d00902c0000a681c004481095138100b0090024400c140d0700e0700d030144505c69002e00603941603001352800102030001d010007040002621038160751059128109640b5072000702d41e204003081300340300940c81074100f48001510300b84620301e401d07950240c036101e07007079403641c03150403100d00000d284214501d881c800f8009120445d4006a15064030a07078032501810216515806e0000210f6030348014a0402c0c6001c0024120003022103503c1000d80260078003c0c01540a48130b44e882c10703c0414460700555004034098480051841004d0000408140480e00000e001c0c003020400c0440c0d104c0065440d2086a076903251254174 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 868570179 1250 868568929 868568933
    0x3030b031c0225030b01141306150e03072403061202060d09170f070c05030a030e06030a14181506090c0a0504080109050303180708062214161d06010309 67
    0x104040700d030000342243c20005e0000ca060612080c070083c0c00ca008458004130182a0402201511800c2c0510307500c0c0900a0110350500780a200d404c181c100008065450054580c90013a40c20200b80003641220400440a00e02440d00341c031620001c0e1440c850b5103800c840c220f40115400d841282a4810241c0e030314489201405400001074140340d1150385882e54810704002d425029400200c020b544000c800440000c0c1031800051502c141d0f5455200c680760035000c40100b1180360001080d00c040142c8070000031000e40c00b80c5e008144a22107011820055464000b0117500c0c14003041d000c2c85850200c0b20501016a40b58130700140c1c0060a9002e0650b904e28001b41107480340104d0340400850342c2812021403c0242c044091882420890f0084250394503c24500d5076642081c8601c2046410a00208035117424520003141d124105034207400000c0810354803441407100c250003005254105080985030224244d5552000300b414413000008180700480190414001810340c0303050560341d501c4982 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 868571429 1250 868570179 868570243
    0x1d0d0f1116060f17010f05191a0415170c090102030c01061424160c05060a170105011805060a0306030c03050601060801060c050a0210021903030b031c02 67
    0x40500d124a2850301c00ba41d0b0b603405005294698464070118080b681e002d5121078101c0b652074105c03034802242060191800302030013811840c82c40141d289203901840400e41242c6101008000d0b0405500142d035545000340ca0030082c940001200208142e403400d90010400004000e80c028842e0003460391385402c0740c0c005038514403d00b04100d446500340400052940e20500480382401000c0d00c41c0020309240000c0c0700708900c004034041030100000c1c0208504810445448130f207143c07051400c0c5250517111070004102d500441084c100003a600c2e001031548203580d800290040c0300a00b00080c1209001c100307060400c5d80717401100e004200110311801c0b45031094010340700440e005207038408241d46070700f0032030b8440c4424040c03800407810010001a41c7c0380318608403000c0c11f412802602140401e81d08110080303426004007821441003480e0204990900b072845911184240c400107250010303070051508004001e119180100d00c071a020b1000d294000c00c40091640d2450582030300c140080c10201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 868572679 1250 868571429 868571443
    0x3050f0615100206191e020d0606020106051011100905100c031104060c0606050604080703050c0a1802161b08300307030f1b020610030c060f03140a1d0d0f11 69
    0x403c01003005506204011b003144d0007460b004076404030510240c0c0d10b03104180c1c01e85819100d46a0040d03418a4216040e900c00c83e0700c240001c1d44102a260081d0101c10749009840d0304c0202641d45420440070b0b950413a50078401e54a40c411181010720492048008484190203207101303075018040300504442c10841c02d0ba101c00d025240090119448980300c000c00b40c0d80d03602c1c0d80011184c6e441000c58020091602d007402c6400c46981440c4020407915030184480030350405824080600006108c0d100000c0d04000500c4120502080364401d83d85045207940c03428208100c0b43c0d502e4400401c0705041006426810b030f060180120301c0581d00e49986104900a20500048965440ca0800c078900070a042c03440c5400807503003507800c031075103034603440c01c02c001ca5007845c40001e021405c1b00f901048914054034503040115042e0030000380c6020b841da514610036000b190f1590900d40d50701101c00954009184100d042070030700d802051070036081c80f005040d0f42c1000017080c1c00d004904002580b1320740100700c0790b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 868573929 1250 868572679 868572701
    0x3c050403050a080702190e060103020702060d0c180e040519020d0803010e070807030236120d02012025051c0f02211303050f061510020619 61
    0x45040c1c0c5810f0412aa041d08503030403c9204150040c002c0c074000b515031009400790364200d40c0e403409907112107005500030340c458941240c00800510014000d01c803180321b0200e07040991f8a0314244030900400080101034290000010f03000d003441804049100000c03042149080070b140ca0386075954900005140401c2c0840050075445e0000001c01c1c6000750583c49402424142c5400b0701c1a15240002e0b030690007003c101c110040c00103140042480384024880060040c440032110380000c0107070104040e4800d50032040a150301500c05000c08690921076a00c0c8039107140e09030858840501c0c4410f00c1482648111822101d140d010344659007644a03429403c40c0d8030804849107101d1011541e203000400101d030781c010400e441e88103401980041650003009020500c40398100405066100d115048010032141c0c4034040140400029010820f50240c803404a00800c05403070480050b020304401850014040c80004c40c220f00c055400190703080d04059041d031410103461001c5100e01c0209600040c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 868575179 1250 868573929 868573933
    0x30f08031503030415020d0e0907080c0f0c07050a090525020c0d110f19032a03081c020f03040f11060406090e0108030c150a090515073c05040305 64
    0xa012117012500c500d1005003a000e4810118007904152901ca946c6095140c10080c00000101301078490071403158810070640809007081480c2280350180e8100020042440d4050340e0140440c0c035003c0241c4005103c41c903818800303854407546142800200f2120283c0c5800301d25070401c8242d0080c4900c002411024051041002c2c0904040c11510b000c3c1503d513015000f003641c1a03109061a04519021000e80d203da08a41d600e150354a8551802d00c071849030440c20208004410000202292070040d0300491b0001e8132210100705049211419003081c101d03180c4100803454a550361402030325407194004d454084441d02c18100440e440303600402155000c00c0014020981c2500190120199884c41500f50351a0b030701d80a5160b524442d07020410310750f5101c4004000301400e00c0c564158420700041c0c1c04900c1c1207503951a18548145030700e040a8080c038220803c03c05940c0b0810410540400007640318805001d0038900b01384822110f40042403031382c1d003114414030b03a000e0b004960055a110341 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 868576429 1250 868575179 868575187
    0x519021011120906070212070302010902100302120a061401030b0103021b030406110a0203060f040203100c092d0b0f0c07031103010516021506150a03060503010b0406030f0803150303 80
    0x4002886030344441451042007203541c010400091000404c248140d100d5001031050b003000c00941c016681028900310119074035024010016241c0000301b6090b0b1655480150300e46034401c400d0011f90000410030113003145800410007081100402c1c10b07441d00c0003820001410021480120083e12031003c0304000c01d0a040c90705c2050000c000010402c0f19020380e00c917044207140101c1c0a45403000d8040203075059001c0e00220b51803400803a8603a0b006403009040300c05c541542c00d00c01054581c030750524170100310004410048010f240c2249150f081500b029440c2c00242c01c0c40c248003030007090281160510010a0000f540e90307090080391401136860080b1001d1540da0328000e0940a00400564040c4d42003030041009203a41c803881040f5184290041e001c0101d04202058491000401280e484503100035039111900860004082410203582d000c24860304007000d041c250342035020454021403901d8010401f1400e082280c204880d80100f9140d038944030460710003403908690803d2641800001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 868577679 1250 868576429 868576451
    0x60c130b07030c021e090408090d1a0103120f0203030f090c0a090e24160c020909010c0f0206100509040c0e01080303010f0902031501050d061a0c010f0b0105190210 72
    0x400450129100b29000c403409400c000301c45c1280c0c81400341e1175400000010120340040c0c00f174400303020074540142220420741200d071221a803510400060240c0880440c0060041c0880001911422491410a041c100d075801c2002981c80c4401004205e0048819004c04e15406090010030043d103001420845550b468103040b0005240540324003200d40718a20f00031409442d4413010a200c40b1240381800c0b402d50702c40203c07800e03280100b00312204100c00c1201c050010780e134001c045401804400c00000f50b000c8039080c09404400c402c1d91400542d0700138410440210100407420302618070540d00e0100070b0711141b50008a6220ba41c00c4444801c54103070001c100c807680040518103c45103c0549984641d079580900100d100549140350081510141c0c40700f0380d40a80000d205885284d1000140e441da5425113402100046914a00c080c41c0003510301000842400341c82c030300c00c4240100f00209260500080c00920032001120b213009041c0b58076628150092003001c00004ca08041402200c402c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 868578929 1250 868577679 868577687
    0x70201060b1c06080616120f050406050f0f040b06040917040b1c0b060d091103100501050f0402030112031803050607090510110d05030603120c0109111002060c130b0703 74
    0x29000c019040d603e0b00b980015500000035215010302c80c20b084002c46283e9a02c421a2400107100004d54202c0d2908802105c55281d441207510a5000d001d000a140c1071117892442c1040020b071590141035030741800c1c4808100b0540c80107400080840b80001c442c944d903c2c0c40607841100e0140d821150601050001d1400c4c0741c60020401140710348405940000f24071007030310864013030031152a0000401c0c40506401c0c0703c5070344040002c44c046e05c414050742119030006032130403001401121080c1d40b10300040260341460f8a5010420b2400c880c15415581410084090300c83d0451020301007040228040d2459000040000041c41d0881c00ba1000c4d031401801c003420f0400e05e441810300603e1841c80340c807000c03403160300d10880c90440314000d03129074114a40e00310b440f5000500690340c14041d84070700c1c40c404088100107007c40c0f07800d100042002d0306035081800011551a001e00e001e122403040d420401d075804200b583e442030500e1907168803501401ca80e2401102c03240c004408030880016164245504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 868580179 1250 868578929 868578967
    0x11e09050306040b06210d03050c07021e0103051302030c0d08071e03120c0503130201091203081537121109090d0f051e0307110705010c08030f070201060b 68
    0x81590300e50310810780601258000c0c00034031b20407160350f0014070040e00c0d42d0f4401c2e0842600840840205030038000507400080051a001200c1d2910302002c2c51110b00c01e5030140100d541c8100002d810034003110254021985070402d910310300b4860700c01c0e010b6241c00c01030940142c034541608450f030717603159452005c1040c0d501c803680384065010980260044070341304402d00500e010a5040c0d5106030450b1113107030101c200e0008a440407030501401d117401150000300c8040500900f806640c0c4c85aa034100b020001c0e004125100819014031440742c001506400681c1c0e074401c1d03c2d0700000108442000403900090b4024140e003000100c03480c80042c403014451410034003000035234229684d02480d00c840e001966515400e11100000c541280d00800c80303c0d000f40c01405181104012a8180046103850b01410340e10840d25240424020354802c0c0c81640100300003409804217080c035040181f650b441e00c5c512400000c109101803804180003501d01c40c400e4008000808000300301d292904030b10541a0b181c0b8507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 868581429 1250 868580179 868580191
    0x3020319020c0325030c03030c020708030d1d0c0307062006240a140f0105070506100f0806090309060d09061b02010c1809110c032d030402011e09050306040b 69
    0x7080b04043d6901d98138002c600c080725410380f15040c4c0403200382d41c268040d10b039081d020820740c00303050000a01507206000400c5120502c800000740e004500e1840b004600d070b00c1800c9111079000c40b03040b80c070300d03100082c030300301640c4960818020710042d80441c2d8421141e1030f00c204d4030324050301040c001d403030740c0006100080c030040219040100d8481c0e406d02841826501c503248600c3c092035085030940c14403c0c04200302010601d050b0b49000800d07110b682c40e01c2016104480900404081001400400c60901e009030081e0009001941481a40c05030390b40200c2c602c8501c10355001030000240303c0d06502c0110581c0d03100b0414044080101c0c507141c2100050b480010165003440112821070388a00030009a1000c4070107680c610a0074442c4000040002120311203481000b008021021802000036003905c0c40e129484228880d640c0c1c01000c22211140d0594600110600a01c00182e0b00003c4d002c4d4184007151300e400400b074081ea400c588040d056446945c16009007020320091010304203000c1d00c20b031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 868582679 1250 868581429 868581457
    0x1203200f0a0209011409040206090d1e020108010803070309050f060c0109050606040b030f0a08090102160e09100203060603070c05030d020d020d0516050a0c02010215010e0f070f0203090103020319020c03 89
    0xaa6100c00b124118141102e64a41c01046c40d80000c00502d48100503140424000d0f001c601e05440c00d50303500854101c081d907034024040107441084115039100e2010b601400c02e0364060b40c1420095580501100101d024141c0f183c50a4402281c15480300d03816600381c1c40c20ac1c402444407840c9800e105450f00c1003078601c03d000300c0c2803c1c1d01002d2402c00165030510358080070020401c0d036001d91a02d41e029086112810f045001d908031880705440b80900040107800b165240608508140e22260f02e065008180c106040d070040c0304010240d514a010b480e13004c00682081654000c6520f8198254450010340c86801d42c40455600041300d40383e400b1344048400700c4400c010f07030b440d00e07003d5440020203007000400294040042d111403912034150b2490051042c012602c1110f4075a0202d1800b1109802c440c1441905804100c100e80407103c3d0950070000740e0038085000041c600d0b00039181c1c403c2d070340c13402d05068000001c0f0303d040c041e80c0c4c0c150095072110380c021515600016480e507125401219140314032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 868583929 1250 868582679 868582681
    0xf1306020415030605011430040503041706041218030b090106031718130207050105010611060a060501120911060c03071b0e1611120408010e071203200f0a0209 70
    0x95000318141d07014030000c1d80005042200454441c0788104034641c1c1c23030340600d4400740701101900d0a110441e004501c500091505c550501340142040040841400e1141e1310070703414400413540c980c055000480f007918000115180d02c0c0942c00d6a5a0301e0f5000604040e021740c10800c802c80d066010b1003d0b20702c14074181c41072090f07250558682d4000c1c4904035000e00c51034031045807a80307000039440c48504c84c46a4050b00307200036501d030142199401d900c500045072202d211078603080001d2001c581d00c40c4c490b0a0402016082400081c8100461800c1001e5696502504402c0c090360086007000071000a000c55540c0d0500c14015442c2e411900d01141d82a10101c2d40c0070003140c010030b01606441c03134100450038a65500c0d60070382191500003404403c1c020300a002c4460980e003401108511294205007540c5e0394034141e800c1d4211640d040d02c400d01c64010040034445049003110400304a40c251034405a42c5a58030300d03811151150b0340d40c8607882d00c04c01600410484000c5181e400141c006c8401103a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 868585179 1250 868583929 868583939
    0xf060e0a1805061909050f0603010c0801090e16080703030801080d0e011202040801291c02040b041103070216060504080c0d1704031104180b0f13060204150306 70
    0x220459a00035400000d01c828032030300001d015035006a0303000d6001000f6200d100c40d101e44080b41411540c01070740c0318644820410030601c18007203180e50400c40a800800c065000504001c0c01c02c2c0040c000c80c400c0d191034200f2944051010010711112038085803042428070340e24216103030707a002e0511085001c600d0390030001071940c05c0402c2d1805210002e4480354031254680c00111100e40304800031000d866400d200203d401340e002d04c2010b01c03c1c03500000d000c1c0136242c071444030301a4124a04510b8840c41402102204c07414955120038601c3c3d40c10745002c90035010701c3c000140900421000ba0081a001208001e0400c0d40040d002c0e1801c1d51100c10b2001c3d0a48071001203c5d00e100d44e005184460f40719046c508a5400e082d4010510b5502919070305010025044d119401a400303544280d482c01130001040c20103107000c1c4a100e080c0b81c4d000c0307a540c80c841c50755645c01030003030f80080521018140c4d00c00018000500e4030314001c0d000790301600456482791280c141d1203841c044c000c0000c000928003640454 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 868586429 1250 868585179 868585189
    0xb0c010f0203103302010c09080118030309020307120b0a060f03030c081b1b030c190b1c14091507050d24060905181b0a020c03070f060e 60
    0x2010700c00009603d00010b00f480200845160040b100c20604c8400701140e502c041e40b8502050b41000703a81c0d0010460102507c0020200c40203a00211080c0e490b0440b1002d0080411766816030080d89030401043d21805400002e05001095100440654058254104003c00482618072902c40818200b1030140c9a610304600b1026902000740844c80440708000030414900160601d100051201540c0040a1181c541080f001c11584040907640c0241d07c131413442c1c244594040c0e5941134940d41200510014580c0c0403c0300c501c10046083c400142812031280d00541080482c4002c2c0b034140140820b61905003407184040322408050301400b140080c51411004c1c9650041c413840e81e070b0504216a07011a2001043ea60800982104015501d00c880c3c504502c44500200116203445141c5460710003401360b107111000303003085400c441504019a0441c042c008080d6144040f864039180c3d4800d910503480c1001c19043c11754548603004d4002108400c224190050b925640d54a5a4044448080c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 868587679 1250 868586429 868586431
    0x1e0304060212160609050c03012415021006030b01091a091503011d06070e010903080412060209090a050709080c060711030705131a0604080a2a0b0c010f0203 69
    0x84010303080b551080c00e00c004102c014000c3c101000408240107603e82c1e8484003180c0daa80000c5550303421032030100b94180b60030b1207104a1840c81c40e03c3c4001c5911917104d82014000a40140b4402100398200c259029108008003030040280707003c10003115849007022041c6102c244940461241008900748102042040740f80f8803010182070001140c5542500700200d00468142c075030599650200c2c14100ca011100c02d03501c2101c0711015110300e0a00400c000c209482e103104140c14020921020000111001c04450481c1d0016210f46080350f8107142001c0030344180c03c0c0300d550280304042800821245a03000601a42035910b940000650311103216031901416540660b100340e05100500c0450b031a81040001c00000a050700d12058941000450001400c0210000c03180d60300c40410039200d6200078201c1a520032140c0d58249458281c106964003000038009000290640c8094030040c69468003050404070025100b03502e603221004c00305940c22030000f40605600300b10020b6800c101c0d0344210303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 868588929 1250 868587679 868587689
    0x151911090405040203031e22030507171c03141b0403060e031b0303041b260a02060a0509040609090218071701331e031407021e0304 58
    0x403030406000e442084000e00c401042aa0107010030007404000c2e80e0500d410581d0500782c4607004d5100e0046064000c10842d500011038080d800c01e2000740007044001034204101c0c4d007180c61f03c614100c0020f40050406000040500050114400c0e1200194058200c7c4100a500d03107001c0e091030b40c511000c00e40c8480c15500188001500700004c0c000708945420160066401d1300072a03103040d0000840001940e011405411650004818041040500c0c0b03030703049141e5048100700c011542444104450018866003d034a04052565200c260002c10706c141e9908a400a04894944800d18400b800e25406106903500c00e6190200c082092143c40c0304000803141c000e043e02200030100a940e050800c0040d040000f800034040c0c00e06e2140c142c0310505400f81c4440382c0300e41d001900d110142e01020444403003100c01200030b5141c00804550011070b88220041c0e030b454811800020744401d0740240041450440b00c0c0140400f008040e90f00001c20106c0c6408540c1101742281e281c0800740e440e40a28022 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 868590179 1250 868588929 868588961
    0xd0e0306151005070309120f0b010602120f0921010510270b060f03011409010e04020f210106090e06090706090315020c01021303050105090312271519 66
    0x1c6811988070f503018124081c0710707013001a04580c4448001d068001c06900c1214410070b4440c00c14104020107139910300401c0180001c1039003400300d4100700309a001d20040740064080108095601d0342d500428030000040d00ca410718000044801042d01038001151003400c80f0b503440b10300244900c1e2100c84c0c00003004440304201400703518602400050064400e030b180e40100d044c0460390145002d540110b0091000c160711004005400c1c00b40304840005030300a0b6000c201e04c03410000035072998415040c5048007210a41900c0c61424600d60000c100300d01c01542e598a080000301d401381c0c10750300450402d0b5424080318526130741e51040350740d00c1e000c0340034140026104120420008848540048000c0320018007d4203040c0781d50001800ca0300408840c1e1461039100404206200707081c400d40b030300400000c010318540700b1850702c28400c1c0ca9000d444038045020450440d45002e0035080103100f01d84110302616006804615811100300c0b0641d00b44070490302030190785041012030303c1a880310340d140f956 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 868591429 1250 868590179 868590199
    0x614100303022a22050601090e040f1e0303020d14010602070915120f030906230d0b0603040f030806012c13110a0e0406031a07020c030d0e030615 64
    0x1c845400103a100400c01c4071041d06403007100165a541030031340781550382d0100f4002da0402c3c201004142c507400781820b8140203001c1c800340801e0584003580380d4069040a0210099a101d20f040c62a03e101c1044080c280d01c540760021041640c10340041c882a41c00741824401c000c00d9a1000304021028421480940d00c6240204803e545c1a003044850741c018419a8104c2035a4003042c0c3c0d504030383c48108448280d550004d040400d170b088801c07000900440e203000060070301202425422880505400c200342071020400a04075200f680094404002c041c1c401600c1e41040e2620301d02c446c0030790b10202c0c00318000000166055100c3d45400c1c244110300810000710320080c0405c0305c1003030075000041e500a00d01c858131510381071003402650900910b0000039642c91880200082c0700060b4900564400c6081040c20008901c00e10701c01d440750f00c00080400c0300d58232044800c1e031a2089046070181c260052804540345184c200456400c9060240e080d035110760740308480d1a40c00c804020840c4c0e440281d0712 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 868592679 1250 868591429 868591453
    0x10091d0105210a1502190329060d060b0a0807030b031e0307020d0b061003020c03030604020a0c060609060608090105060108041509060608010204090b1507030822061410030302 77
    0x1100d008440140302d050301c3c0780203c26141c820400c0c2c0800d01d8000d090743c0000e5810000c61900680032480802450100b003025580408950200e510340c1c4020140f20b1924100c1d4490355500d4201d510202d00014200186a901d135225103507500191a2071002c11503e800040c0c2040c041e008980c0503500c000c02409056080c4982e40c00700b034442d1880c04540303100c28000780005840e1818028045401202903440528105e004c218504101035494410540184050030f00d40340000203036a0004c2c0122009621050b584000700c1d400b0199510103000785090000005007814140c0c4480203440c4169111445036485142c4a8240c5a041c0d54450008070383c0750000f40451640c5002e80500705c1034040101d00d504a42e1180007e94000350481102c603540000c0800c40c0544034828084943c07405e07520000e51003001c1c0c0600445004603080541881404000100903004488c1f51150b04500440920441c0e60ba6003010310040410140d200c002d02401c50229800b81c151485520840e036240c1c0c020480102c0c02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 868593929 1250 868592679 868592719
    0x30304030305030a09030e10270b031611070303170c251b0306062607090c0507240b060405030304090b030c0a06021c080609180c10091d0105 62
    0x502170039010801e1000361003425a1b6400d421030401c8010b81e0719000c8290f1040c800c0f84911000342955603210244080030492044940700340c3e80d001c100f05c519a245540b4552095440e810402001040ba010b1450080205504071041d46a002c5071030180940d035944d4070305a0b00883c480c96080c6050388031041040000c1e07511511000c1c48607031150910780911001000301d08410400c030380080b01d50980311041480040741d00032103000c506800e069040c0e03100740c22021044d20360817076004030403019881d0f80b100d141d868010740032240e681b5845004403109400c4101c20254400c0301071114130301c460030640440c44515150090b10150351004002d1880c1c146030001c904000d150541649070140200d4a040b419962165000f100418a5030003030106400150541190310038a0328002c1c1c00d2214010a000d841d407154885240e20155254115280d100340b601094a041c000310503032944040d80c07114886035036501c10000d00881d00101d00d218194140015170400c6250709003c0c1d5038000c9010101d0b410030841c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 868595179 1250 868593929 868593941
    0xf0403120930140304030f081f0303050d0f0b0906041d0d02071a071101050a020307140715020303040b040611040807080313050108040302100c0327050c030304030305030a 75
    0x3040422000400d1220010740c2251801c07088004041840740032100819040f801e44910380c1039506560b461840e10742d9018080443e00ea0130001002a41c50004d51407000c580007002c50225520581000c50b5a240340c010720f1584251500c10b451410842c4600395114103001d4594075220040c420f5070035a40781c0c02800018030201c8004241c1034a0620804542c1c02c2c184000651030402d0390141c402681071407a080800b241c0038100041c1901c0420903040030451080c00c1e441750b00800d20b04243c2e03c440056080f840d42c014000060140a074820100c00c28280c0007503654100c1c1e00c070600c5203507070703a401e0002686c41e4042180e02815003294800000c0025600368001d95840340e078446100c1c2460744a4040500c1c058403608000100d520021b40000c083d106080700800400302440c00031000e141ca0354009455002000f24459199160304a030021140290044141024503138446424100c80d9a40c0c52a0542e0011050300d180c000d000d40c003802810040200c0f000c0d26007589440380b440d190600040b0007001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 868596429 1250 868595179 868595183
    0x30a0b070228330f3c021c0c0915030605090f01121410151503020424050706050411030f1b0f04090812010e0f04031209 53
    0x6516000304545a2501c0c140b01c0300d440080020540c84620300e8803100c050380300020f00074203001c0300da60300b0288040300d1201e001c16140c1c104041070f0220060003900251980006000e2800140986011141a00300307025504050f220b2403514012445140c42080f07100d5101103100402501d031040e80a120650812181c0e9601803500c82e03909552210b041c9020800c01c544e0b2800262a04001c010074940400c2e032580041400320140a254500b14403441c1c4842039840040620800305030001a092007400001d80107681d00c41c0c180110324421482c195413514030b0091640e01e000c035807100c4014501c680300ba502030752441202d012058014105135845040c106000c00304021042080f040000c0c0c2c0741c019140100d114040b0a050519030504040c02e22007860181d001070707400741d04c840204000c0440c580080c1d40d011788068000c1e0000c2c40124000d4655100c0241808034001403080000c100d05002d107049400300c520b007071180d840b80100c0d04107410003524060300203070743c440588000300765a600c03100b0594 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 868597679 1250 868596429 868596433
    0x10e0d02030f0d050c01051f05040506041407030606020105090f0d0c1410020d0b01030e070612023114060406030c0e04060311120619091502030907060908060402030a0b0702 76
    0x61a9045442e142c41d401d80c40f96400940003007420800c80a0074001c0540054065025030150011803107141c01c003006601c41c4602c10358171003001c141c0c02e865035030086076041c013810b691228a00d80144064040d008911600005610388400581c41400c04148041d800c03801201421003840007640480e0403136a8400161034091400801381c5080208000c100414800c0a8000d62110300210000084a0388064105d0500d0304006507242a2100428568284e0b81c8505155044100303142c203003802400303812200c40071201e01605951070800c850380242940111792201945840e141c800c101c103841402c4941c02c2d0030842c180003c0c003c44e03001c2c2e00181041503662800009911030600020140e8459900070780e02004401005481d5050041c600018903c0020040005041010b1400251a880c0507264001961041e0700c4080040b0030325808511a01088150340740d0030440416520b07901c1a1040001241c4500d40020700e5030004504644103a400402404075001c181d1030702050f654000301590114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 868598929 1250 868597679 868597693
    0x2010509031504050105161d01080a090501020705031315140a170f0a06090b03030301030f0201030902030d0905030c092e1e0e01081f02090109090f0b1e010e0d0203 72
    0x1c0000d4142e0712441c0a5400800d00e07003003964030341a409107000441400c10120f59190081012001600304d4084421300c1c0800b80c44c0e641001c413500a00003480003c00650000500720300b48100000946a41114041020300542c0c0c0e0742d07488080103408034151800300740100809001c004420000d00300102507420107200c620008000071548500496071081665400e40600400c40c040d4410703072020340309451041080a11a40001c0d999000501c0001c040c0303c01d042c5041c1c2164441e800c600000e070760103000c40340c0300200404040c09002041c020a40a4420760000306510f1810480325402503d03186242040c48c03c00c05000f60f40b800b40b015a05980e8550088002107802e0344460901c80003400800100100e07083c82030b110302224040c0c1c01203880340d0001005070f0900c02c0701c49a412850f0102100160385d10352040051f41d49400591204420515000f01280d03544d03180c0c2c02500840808031040070f8149080b100c00500500390503007040c0081c0040200581c81d0501290089031540000d00b2501c60f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 868600179 1250 868598929 868598953
    0x5040809090702030d0b010503061e032d0127080d1b02160905010608010b1c050103060b0301050708101e23010f110d081f030c1e0b070201050903 64
    0x40024141e80c2c14006038800240440002014070501400e12024a0903501c1d5040c90000110840c4d400b20410801d09070160f8007000c1c4e60750411410100c865080103d1030100b808400c00400c20481094803201c550070103400c1f0318032000e042c207120307000b64640c40143e401c0303621070f101c040594000c200f40051680c0c0c2e07004018000d07040b9603000d0300071800c2c90380200035030b000814145582417242d0340400546400c0100510100f0b80241c15070b41561071011459444884275485503e8548103511030400c00c1d40760000220502c0f80e25001080ea0000a170024095038035500b01c210360a8500b1030300700580b0a5400ba00744800b00101404c4036181d0803180400180544070804020840c1c9202050004124091618801380d600440080a540803d0402d01d4002051038946607c0e6600710001c5c504204500000800550070720181d40506011a0340b0074070095100e01d00311100075400d0182c0300b0720881c0700300c40310300048180d6840c8090b80c540003d520304100242d801580c6d9a00060002541400340e0302034250 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 868601429 1250 868600179 868600189
    0x170402011b050120040503030702010c03090e0f0123090105190513091e081207031b0201060305070f080a06020304020607200f060f1204021215010e181005040809 71
    0x1035014040c00001690034008021403032010081204612085011700c01000a5a40802640c0c0c0705074081c2000303220b05c0030742c0c130b42203550080c11b03004542403c142000303000301c0103500d1002c0382c1a2483d50103440100485401e0310300c180580c0e1a42c1c164064100c00042c0320604108041000110340c64000440c04c603201c50000d1121a078070000c10403035a80d50340c1c1c290107014190072211801c103d1030116034050081511050542d00c20051080052030881020a07031243c03099226000c14808410074403002d0b1001140240070700001c3c48250b6251003100c0020552240c20a080c00032142100000c1800c0d10b40c40c0d4811010307400061060764411000d108244c0031803a40c44968030300c0c801c0d480c01181410260810005800c1c4400d00941c09844144a120032003140d6100700c0c0c0d0a0030845403034000750740d00d5200107040d8281040d10803d182c042d888500007032400000559041e20082c50340210030341d560000701c243c884440b942d83d1629a0080c0855500444181e0001d41c000e40941440c40c60140a136021070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 868602679 1250 868601429 868601477
    0x10f030e011107051e0d0809031306020c040b01080739080a1412150409020310090302010e03070b0c131208030a0b0a14130f06080f060106080717040201 67
    0x50b00c1100700040c12004c00100703002411000e07158080c458400d480414409594049100116050001000100e0001c072000c005458038009005000c00c41d01d611000001c0d1140a0f0011181c05141131111581c0304d5030085500754401ea10a41d40c0f001c52006c2035008480a614001c0c03100c580d1106081000302c81d81030410300000c848d0191128a5071011040e80040840c2ca002e5803484c0241400d00c130780d105c600440e61f403060300000e407104055036411408001a0050685103002941885040c9185c3c030000c1c030302e4001d8482580030ba0000c00036640c48800301a00da01c2101c800801c200841800140c91420800203403010714000045800c00545800b40b6120098040c4030540d102480441044040d045034018040b03c61400c2c0c4036045890318000007550041c04141103148180c1a1805c00445600254030108044c80d00c11802d0200c181c2e01d405040d160021408054a24080d6000110703102e809010300da40030b1076242d950201c40343c0319642202000c1d031000e07004904000c0b246100c500e8902d1496502 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 868603929 1250 868602679 868602701
    0x122f040e0717090627011503290114061608040306021228020a02011826210c0d05040302072d05280b03060f1c02010f030e01 55
    0x20701c480ba1140712a11050301d90060a980859001c84100b21580c0624400000c42032800101c07030005040e11040a400b40c08108285024409402c43c008248941c5401c005554811240c80d1282e1105071145041042d40901a00009100792141401c00f0b0a01034000c00e031a40302d0a548840c1c1c100c1c40ea442d112a40c0c0181c1c03080c0c4205402044012440d081c1c2003446801104d01e18503030b2a9010084503d0194501500402c80090f9000c0b58120340300b4001c0d0445180340c3e0003000c03d030480403490715221a0102d8640074903005281e1507080c820f03e81c2c94100032070390396981440703941105000e03007541055800c10080404030b12100521001170840700368003a25005a1203500580015400c00403400290b4403030615484d8000e0f10000003468401e0301c1d04800c0141c40d81591032a4500c20660f41d424202c400d15040300c14205031101c0700148090014010f14004d03d411114024103100500c200301c0144400441c0070083d040c013182c000015030180284581034082c605020501d842c058903003a00311030520f200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 868605179 1250 868603929 868603937
    0x60207140f070f0e0f04060213030f11010203250f17030921070311070b1603020613150903030e010626030c1c02030721122f040e07 58
    0x140d0302a1105112580151083c24091181c10385418107010702d20070090003580f0000422404103041c049142c049803030094900d0640c6070010364034a001c4661300d880501c281c40c0c0b81403056007a829584080119807009554503412904d0014150070305140900c07402e002c46506007000700b41000100c40200e140e0081904034101030b1645414076415007071201c49100c2e007059920002e03a0300b0391200e030b000580e01c9150301458a010060080c030035081c50014160030012802c1c002148030814240d15403052007115219509903111511110b0000d0700030400b908008090300341e1071103c8410701c02a03601c50403005000746404101c00360040703030107807c5039445e40201e001c42e090b80201100140e018020340d40c481121000840c5001ca084e1540740d21034501d0b22000d08048c2900c07800701601ca02c05c00c103a23003540303810140c1d50750b05004a040191030007103100b450502240c0140c09402180d2414426001100019000b03000760207803c0d8440013a0a40280404c20005801d00010840c1808008814410001034031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 868606429 1250 868605179 868605193
    0x219091802040b0f01050d0209030a141f05010f0302040b01020309090a0e15060307060f0507120806040e0a030804150e010e030309330c0705060702070f1208120406020714 75
    0x148001c0c0c3d40c1006550380034420080010495980c098102c4006229451005031101204000641440303141c03080a0030b0048a0110200c4201d008200055a01e1780a0b61b20f01e100b80c8890b9820040c1d6200340300d001d4aa103007416080015040a8211043c21031051040d245810368a00c00580b810000f500d0820341950f0340c1d90201c8484408110500c000022082c1ca008903181c00c000190380e424060244504108000b0443c401260151065943d12903000d003541c601e2620003d401009002d08841c4544980d0402c95080b4442d1400708010351066010781c0c607210150b5941d101c0c0c0d0001c0c807456841c0a840e030b544550218a01800303203d004410803046002d0740e540d040460030b0500c3d08016108100002c40c0e001250000d4512001003050700086448069405540f0000d0101a601852001801c940110004c000407154007068aa003641c03034200a045150341c54070383c401c2400c000d282c002031008808008004448181401c0f090340644108005440c0003590b5841c004090400301d83c01159911540e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 868607679 1250 868606429 868606433
    0x7120b0d03020c100c170a050f120f070503130b18070602060604050709080a12020a02060a020a14280c08070b030a0b100e101e02150a0203010b0702190918 68
    0x7032080102c000c0c51700c1c000105406544500090312503800101111590001d21000382d1b074024001d646004011681450302c90517010284071405004440e800c80c02030b10000059034031030150083d28054500c0442001c0b4440b203a40d1101c0030340c2e00142500003181521808601403000400250018040c16030161200303003440d4040c8000d83d03001a0401c410b06c602000705100c415000107000040c6900007400d1100b0801403001a400d051007043c019410100004010a24035000200700700890310950405c0701c8804021542030700c5d21250301280c450040c40d59145440c0309548101602058025503008820556800342d4174030740040c55214006429001c010031a1100a902c110001c448050712030300400d480780280104040345105c81980324140402020380c1d420701c0350006051100d1582e0710540e60340080322001e561164540c243c10b85200e00343c00080d150035085c7c000d0b24100d600082460f424a0441d0b404c1002a0806043c0070000742800d04001a6200450003120b071145091038598002e621a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 868608929 1250 868607679 868607689
    0xd0f1202030a020f0a020f1e0a0e090606090906060f030c090405070f0b120105040903300e031206090c070503120402040b0607111c061b11070b0307120b0d03020c 71
    0xc60980b02d2140c008802c00b0000d81c8038102001d40c1c00300202c408c140350000035500c500c41c07440c403811361b0340e08881c02140201751651008841809408040111003240d80c90404120601c54112504035494129401049550516a01100d882c040003815111030035044d40c08940710740c4080310705075001d0780309201c100010b82250040c1030240c04010016840c2c0380840005406044040c807039640603560b0340400708141446440010a0300e100707800d2007071002076181036011900c1d002c00007664105181c010707042c1103000700004882c0394a4100f50304154a82d110700030804801d10007400c0100d80b400c1007010320001541072004080301e100c070034580d503440d007428010710040f2864088480d001d281c0c200012004030313100b00a041c9040170202c0d41c0c41c8413030f0340100100992086250009040038201840801d6400c04c081d494840c12140e85d0303521085800ea09c03269690f03904070344a50380c1c841d132081000c00d0000b8840d41c001c503081003407104007117214110b89001c1250442147c80c01d500507000000300b0039581c80d107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 868610179 1250 868608929 868608943
    0x20609060c151b03100e06040908070b0106142a0a0b040515060d23100603030305061c02100f03090c3206040b070f0501110304050f12090d0f1202030a02 67
    0x3640f040700c2c1140f4112003100b03c10a401e0103500c81403a02c180025840e50f8642c0c100c0a1242d40c032607880764441c03095150004004500380620404176020742c41c401d81c00b40342c42007910748805c070490340702012848140d1001028800002c5c1e91415019403100600403c91248090340214410b400400c22802d0040128a140c1409844140714002d0900220081344d02c0750b40b0b80c401c42a4485ca030703e03404007020241c203140600c005541c02900d420901e0020605400d0f912080c8a4001a01e46280b03403049030310010192134039080c000f0b51284a8490f00355840384540e001024040031402e0005201e03060b91500d0205149a9010f1280d80308035401800e40c5101260240482c0900104089102e0440c10002000d0f40200e024480e100c04c008140c0d0000d001001000300352007908000204104c51040114441070b0b88201c50565243c45505800c880245c1c00042601300c0c0c03582d4540507800c10409104000341c1010f81c8105541c0d401d0803010050101e4030260039400390344440e40043d603a422074110040d0070814 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 868611429 1250 868610179 868610221
    0xb010206060a151e0e13180b040c090f050412110c191a09031510090207060b1518040902150c19030e01030509010203070c020609060c15 60
    0x400320501407661514075090703050b140c3e601000300741c5800d8802c0440d1001500400140402c2695400000c03050b0044aa11191982995625100b50001c900301c0b09039a08108503041600340d1607024000314000000440d0854460884000c01540d0781042000340c6500c1020328a4460b62101440108003000d80045100c0b451420224420542c07052040e86070709107d5031181c0154036201e005110921032541607406000c0b95050004800d86000000d00c0030703005014814000c2c4524041c40030403a52120300e90b403146615441c02c3d41c54604000345d05004e5000880700700d841a07203c1c220084241d54000742c80420031684803500e80c441c07401c07606415980746090f49083c001e84c507003044800940c84143d40f40c5402c2c9000010580d90b10386481090b40740048a07200100c0103010324400c80c04040d88072241e403203840c100740d9080c40283c940034840c600300d2109907a0103000c14154843c4400600381800504043da100410907401e01d51030511190034030444a100e1415450000c040000075000407075202c210030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 868612679 1250 868611429 868611433
    0xf080c09011e030b190509011b020f0304090903050c30160b1806010f0302010306231011070b0408010608010905060403181701150b1e030a06120f060b0102 68
    0x100c03000201424a42c0107010107090440080d0015242c03001703411004404500b100410010b41c0b0b01072500ca4003d150101174030030301996540402c000c00e0310000d0714000f4900d0300300255242601e44a01c030401848914012410301005000003845c03030505200c0c061503c414114a086100c400c60380c1480045516074101c641604284840307081c815410a44003012a4032524017000d540b103070f004c00b800020503002d03603c8140c4945400854203d14030502003080740d1007a201445010f458903250750304581c0411348040d010f94940c10700c900601e44040031000903446420040e10140903031082c0c90400b20b154215410740307280002c0400a00000340b0030b4034024040d034270080080d000301d60746040d01c6900c0a0b00150400000601c0c1401041d8014019801801554a03501000d802c8000c4940a4100018156100400f00e10000741071031800c0d080f5241050245044a0081c1c0b060b084030a141e08003412031003c441c1d507500042001c504900b600c1e001c0074011106000e4003003042c03401d5400d4030309030300a090440d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 868613929 1250 868612679 868612709
    0x609060e210a030b06120117060606070f021306231c0b010e0a020d020a0f0f02060709050607080f040807031205180405091c030f0c02030301032a0f080c0901 69
    0x104116020b072440c40705070745000310f80c1c1068840003034514056520350300071601d000000041c2d4001a031214040c0d1580b240b0507039849680d02401c00c00180110312020700b4081005800200514041559514002e05c1d0600040c00720b40b40c1001d04031600821a0701581e48803a502040a64940707201d03141c0b94044501d0305040d402c030860313075100480803062190a03c1c00890354042141c0c01001d40554102c0749041e00304548429402c2001002a0640600e90010600382c490031515948040380891007114a40c0300e13000420710b40303000d0080e40c0d803000788c0039900144107200703101c1060311140041c0010b08660b00202403090640c02c2c04850700e41401741d401d003404000c0000c600c45403070800c0200146c140890f00042c02e44d0300d0211031401d00840b149911514044021903118840d01648402070507103102004003e04112401c060342e5030b100a0001401241a801c07a402d0340e010300b140768900011074182c1d200c42c841e688009045409000d034200190603041100c694402d030a044022900404186000c0100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 868615179 1250 868613929 868613983
    0x30506030f010e0309010f090b030a0245010c05070f0302040c0f020a0303090f050a0f06570203190503040f0b0702010209060c06060307050628020a0609060e 69
    0x20303a100380401710741030003c4402c8107103a0b07a00801540008099812060ba07032443c0050030f01c8001d600511101e01d030320701904031348604801d04024078481582ea09401001da24102007507603410b00180340c3e90344e0401075020800b10020f0030a020302801000602c1c0d8001e0501d09510400081e2000c10211008004120140c070b1541d40d8009a0303245850b03014103001841180c6810031a4000c2d400400c06400ba10170015510200500d00c3c120051660140c0d404002c420754548804081020042103610380c08200001040c3e01c01200c000010035940d80c0036004002d40ca4901c0c1840120b80a05901e0b02681000c22005000c031071035805910f948c00d0324600245103203015542c20304050760890000c0d202c003c0780d100042c03a0f94001d50448101c2c1c800141101c0d02c0e02480340249581c2c0200305c4107503019002c0c3c1c080c00a064101003081d205040703004d052201d02c00100c003090030003c02e14044c0b0350045114682d00f640114640d48260000c00303014080c0812982624907103d4540031600b5001c0c401100c908240c422 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 868616429 1250 868615179 868615183
    0x708010515090f060112060b07120809030913090c0e0703060603140c07050f030301080309130605060f07080706050c030411010903120f0908070603060f140d06110c010903030506030f010e 82
    0x984031651483d40852a200c800c012207152860341c0008100fa450200e01003418102040500303130301446640d042c0003403025030308111018602600c0c0340c20702da40140b00a150520701880322485a6041d03c80000708010680c40350040b29015170302500c41c000803801804030b410783c1340c0900c0307025103140e050602001e0690b040342d00001034010240c1c2d55544000c1019001c110050100f1020041c05204994495071604141c0c2d807a0740c018082544644245612021626103e0098804860004101c11f045c17003628031900c00f840c0e00c00d690460701e0200c2000f100000685c2c0d44100ca0180500900755a141d01d0180f4069000c420aa600d103030512028210420020340d40c90000040c4420350300e0001031250990006403403c0c5410b803c8964a402105404182c1d5513055110398122a44180008145031340c4800c1090b117041002c0d032594100d8403031080440807550f9074002c80440e420b0340a45524241c007800750706003141d1040804400094030380e001d100c21031604001c40d14464144800030800304801446040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 868617679 1250 868616429 868616431
    0x15050304060b131a10031a0105210f040b07030e0c0f0a030803041401290105031e04051e15010302040b0607080304030e130b010c0f1103030705070801051509 69
    0x800303030754484000d000310b81c4841d028a80c480407699801e00210107071550250150f524542c440d40140282c08840410b40d11038000c0501c100204050302c0d40540b00040112419806040c1d0006142c0b040750440885100e4469501e1040e551a004514103003844c1c138141100c8030000c0d003540100741c18100d0590000d68040b40c041210002101c11503800c1420710007046000646510203040800080200414800714620854034403241f8002003007040112411609000d020000c855481c40c4c0000c03000400394021802940c008290031414070080c01c1c0824040580d0108840c1240ca9400460300020403500c0300c00c202074600c01c0c038405090845d181440c14500a101423001034895601c0711290051511024100c072403039a0060621a901d02c3c003824094061421202c8645c0102c0761042e150028480c64400c3c003000050594030280c0f5000359484240d0051500c81c006d03110405109102d880640e81000100f400c00d10a8010340342c0c05103031150642c2110402040d5004180c05000401010b945039044a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 868618929 1250 868617679 868617683
    0x130e0d0203190c0201080f190e010f06081507031a060307020a060f0c0c0b0c0705060403020f0c0324060102010f060f091107020f011d030304030f0b160f0e030c04020a1815050304 78
    0x100c0c950b9900c8c5080c40c08074000c80e615050705490162100e65030803064001c100d48001e1017400f84003043d031b202032840e510b80b1501c6009500ba2001300c04101c00a00c203400c2a00340c0454140b02035843c1c54010000782e4240e10607070781d00300540e1044040004000141c0078140304002122010809a506450007802980381014001d02e4a0b9011000480b86100344080d5442076800c80111615032174245400307980c030b41a4a800e9001d600c00c4074004c41c0e15240009054101513a090740307151340c46050744031945030b00e00081e0125040d9501d40d141152810500d126400061901d4128200e409191618000880700b41070022400040c04000c072a001da01d6442009000140030b280920808205018051000d0307a4039140550500000a000003444003003080080c003140510519011600c1b1a60006010f000c40800030020400e0041d0b0180454012030b2801d00d032800240c2a44c152404001c0054100c0c1d00c251030000124152100c801d013407107684001e0034003504080d180c02e2907403014410043c1070744c0402440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 868620179 1250 868618929 868618951
    0x30d0c060905060c03090609010e0a020108040302010905061f0806011a03071206080a140102030f0609070905181503120d0203060a1206050114010509010e130e0d0203190c020108 78
    0x2150401403554014000d141d00a425154541459a984105644141d4040305a407140d00c000c25140c50040c827680040c0241c400040030384c0c0105900660300e00388018000e0303041d0b55a0f00003007404900140985172044c10080750b00121545040c803580d13131200041c1c11150316a8808401440f10302480e0000289850701c03446d8840d1a0741d038440084491490b504418001941041d00c001440880000c100c1c005078800d00c51407440070103102d2810b00302e000440f4044805c102c1d21340070030b0580c1444d00182d5044802d03498403031100e0b9110000720301c2d0b80b848070180304114003810040050040c1294071b010b201e080d089018000b240915401c91400c3d0150349035082d07070381c0d03030010108806030340b0007080304000c001c0d0f1002c0e100200308904180700105001d100d8071503000c0c07000d560003d80d58418000c5500804050312514040349070f4405000e680c0c00340c00c4441c0c0505940364051a502031341085024100c0040798021030742e40c220481d0740c41f5200ba400700f4110034003199441080040c1c1c0c2005100b5804500368003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 868621429 1250 868620179 868620197
    0x1091401080604052208120109021213020f040207051c14180d0f03170c13090207020402120127091a100f081b090103020f090c0c120403020915030d 65
    0x17555151542e21121042240d021414032201040241310103018240007203e0410510780c1d803001c1201c20b0707100f1154000044c0c604c00c00000c640c0030030207001182c0c15002030501014100d00d000800c040764400c0320151055403240c58035918100f200095050f1004030b516044041e40300d2150301441502480c10f4a498800900c043e4500c07548601c0d5a080c1e4049d04506425604051420054410107080803a1294000030b040013400110204003143c203400b4805603003254481c68610002c0094001b100200e030720680801c00e8080c400110042c1c64080e2031a06036100c410210030341c0070042171840003481d6551604002183d00800d0143d1040140120011400c00a82c0e5886034031164030803458004071000500c400e00401e1907000000c40c00c402d1f000704054124584044420050151000d01c4000d5124408010350707203450929180b103c0e0403420030204036040c1403411003101c0c105600e00d40c4902e040c40c0d001c9410800d40c40c04500250700210310901041c91305859001281e01c2d04c2c54040e100c018440080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 868622679 1250 868621429 868621441
    0xb030606061b03030a06080c090103050d030915021803240103060c0516030e031204081c05040308030103060c08060402090a141203120901150807180e0609010b0109140108060405 78
    0x40302d080040c0340d60540b9641e2404480f1100108524040c04007035103e15011400b0700d0520203c1d06060740e0708000181180c1d051100200c2c05844000c00071074200000d0252825080ca03180094901200315810152880790380200340362500512001c1c00045488000c1c034544014030211000c1c0c1907a8108070302007070790590800140c50030300c10300800080041d0a0b0784080c05241c5d200c1e64aa0802c1e00440c282c2c0c4c844a645940000c0e58059801013140907000039451800600d2030102611480c0b0540c14032070304040d52501c8250507500240e00a5400540310010b000d409944020070950083c41120110b040145179004941c031f103240ea008000007908102c10f5034400b55180d201e5075020801031f40c11203a60b00d0303401d101c095400c1c400342c50290a560801a034155004500c241c0310741661481c0009080c06881d140b03404040001c080050780304155a0008022101d40038001588240d00c094004290000740d00d00040030811258010302528211482070207040e030780410300940112044501040903100c070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 868623929 1250 868622679 868622707
    0x12040e04060605120c030105011d0a021305060c01020a020114040506060108060316060201140606040305030f090d0605070f0e040209150d150303020703350c010e19020f040b03060606 80
    0x2681109503c0914102800c84c4080c00281054001a080e0003d22459903603040110b0740401045505d0340c4c8228140019412050039030141080d0b80740741c02c120141d00c6e0b0b600d010801962190201c100141d400248903204c6940900136041d00b43c240d014924118946511019115070001e0a00350410281c9008a800c0790b0f42008001e0103540d0000d00040020b6031650064002e002911030945c0030f07240080080d0851810601b40c5040303030f03000800f4510340b20080400c02e800358000b105c403640c404041290200410080e1190a10500c05034607890302e001d10100002c0c0625400308041441540104144000398031005545070100d10360002c09074842c4500c00d6501c0c043c00c1184c10b107552a1960316400811316500242c41c8049074003404443c90400c50500e40394a10340d10104810021a500c40c02c2e9458240c0b13003000070003504012400003c1d442c0301ca40c442da414500e40600034648074014515600551406058003d42c41008031020010043d210000c00d465001c003d020302d105640104d0380b5070025901c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 868625179 1250 868623929 868623941
    0x10e0c160f11090a090b09031207300b030f070b1801050706021204120302190c05100c03020904110909010501030b0616030201020d0f0c0c12050f0c01140912040e0406 73
    0x4040246138030300a445140103100c20032081d940341d030070080407940c81d03400403045400b2103980da40d5044c82542e5040d0705440f05040c61028020000c01c00b40030b150f0403c1c404c94114086810940041100c04660782054602400ea00080c00c030390708540000c000e030f400b00f070046502c0e044001450034500008007005a480d40528800036109a00015403201004910300007107115a1140000d0b02d100b044003141181280610424025414820190301c80140d00804a81c6052442103044030480751101c842002038030a010707480000b00360042820600d614040c003481d801c5040c0002e28030f00b0700f0384a8002900c0c940f010720416051580d24400c41d0129212807044989001d52403115034030340452840c00900030360144074061140792510070b5201c55009075004990340506a0f5407440c02e600e4007507c9a0801604401000c028090100020b450101c0e014028000351000b001c0002516505480c200d0101c0100400007411500f0020030300c0808840d5000395010380b10488071108542c0d0382c41c9441d034002c1030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 868626429 1250 868625179 868625213
    0x1201020c07060f0503090303060d0807080c0105010f05010c0b06090403050c03160c0b0f1902030c0a14070905160c02032a0a060305071202220e010e0c160f 68
    0x4000503490442503000120082291400d544101105291000842d124001500e1041d4035400820100c0c0c2146403154030446020301880d5154900806556104c0a41d0f000c0c0341c644142e6516900100400e0300c40c2c01c01003008003400e003040518a0345c2d95840e00c5071070700005e1141d40b04d1004100454245881101641d18810001c0700300c0380c0d00c1100021800380155020002c0303400481001021030a0014201684ca08485c2d24401e24240980c0140081d5600807600314001140b03c180300c1c0c00c102c04010031940d01c005004401d21744001c0e0707034082d1490a0944a03080b44080b613081205111060000c00301c400150740051034043c401003035610009040241c1c5220100c004610f0a5501501103420b01c460380074440e049400909141d80c031082070f07050b03540071540000071802c0110f20303568203000c503001803081034103c0c1d040c0d00804104924100c2060016003000456555250043c002c4001c6603002c41d410a18001e0850309100075018404c40bc0f1080803c02406200303031140802c00c00c0741c500d0124503807034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 868627679 1250 868626429 868626431
    0xc171b042601061208090d05240c0405030c0907020102040f180f05060306011e17030304050f070e160e0d03020309010e0402130e040f080c030307030501060e01020a0605061201 77
    0x1950341c40040d1040608145445a40d0030203140c002441d140501c1010101c440c1907010b580c00d0100c80d211030090b034000d424560b40092501140d0400a031003404400034181034894134403215103401081450840c4001e1601160013002c004c288107130340d000600c46120142c120f4070003505a458a500300e0181c019907001c0c4c41191a11140464840c098000310000030112000070088811580c080c0d0042d60410380c0c60715090340040005011012000341c0001401c40c4c0d400f482d0709140e666011036a180344251810030b04540010040c030041080c10f200c0c0310071007040d28005240b45402c140c418402c0150142012910304541a00305411901424030b801401400400300220400b043c14042d4490744103826840c00104411640c481a2402d4070a4650b4001011030014542d402c00740800d588542c003070003e440c1ea40c1c03540081e6000458280040110b048503c001d541c480c00c01c1e4101400b07881041c1c11100c10700903204807045180c2d03800100341042c02c0d001000800c2603212500403609815059414440e65 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 868628929 1250 868627679 868627687
    0x40506060c012306030a110103020a03060b121f0f141f20031312050a051b04060501080108060703052d010e09031614010f06090b040c030c171b 63
    0x4a01600304032040e68a00d240c3d806426900e06040640700c03d00503100400c00d0001c000c2165265101b60301428550fa00790034005241381d1035a04400d145d82089000100c0140f00d40c00300247c03000d104094605907162000d1810950342812071350b01c103021a900404000751450b10405845a450f401d42c648002c0703d009242070038510540c0010308207103148950500210302101e0144510300000101d6178800d845604100c0554100f000c611804031040406a41921801c503016002c40c1040c021030002440030b02c02e189030418610b040c081a100c5545c8464144103446d0010021703440e01140844c4d000c0b0171460300007100e40e500c10005010044007461130b041d0000e41400345840c821103804140c16200324495540d4113543d030110b000c0d40c074420b83c1000c86400000101100003e9402c4c944810240c501c00e00200c3d10711210100a4103d4000358081d0b00140c2d16200c6080380f5090500c2000c3c001445031506124102c203000000c1c10500e5030300d5803c45180c801d000001c2202c04400d60305850018440c084550b0303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 868630179 1250 868628929 868628951
    0x6031e091e080d141e09160e190203040309031b0b030901090309050a060c030c050f030a030902090f0f13060b1314071b06020c1e101a0f040506060c01 66
    0x20342c1d006120b035180107a18103a444141060744d259190711030361003404400c13880d08440d09504010308016110402521403240780b001c0d5049100f01060203005c2954920401e03280c140003107210801c80310890240c0e10b1040083c030010942c0074000c10309694121281e1580f044903102c07046c615078030039030100d00c0303414001c030501111141c1900412090b038040d0b59175440c6141ca507420040c28040074459040400c017000d41a0000a00443c81100c196000f401603502034417503102d180e0706551107260144002640c4207403140c1146425000a90000d03200024054140303400703020341c4042900030300442401100040d694040103101d811000485001509070091440300d0034150028001b075842c40ca2185642d6000141c92760f00c962140d00100665212051300703c184c98403210000e500c004444a10390040d4401c016040200c406c0784207514180d01c004240c150350072a414000c80c1c1c1c84079420804116440102e81681da6410000b4050b08000c9500041701d407210400600035101d0308001d803010b9420140c800d20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 868631429 1250 868630179 868630193
    0x5060c1f06140a120201030507021624020f06061909151a03070c06021803150709080c06070206091c0f020a0911031609091401090606031e091e 63
    0x10403980c41114000300105803030b0401100c0700c2d150240000c11200c810312200958402e03006150804640c4c01500c0713940980c00e50241349182c050300811000c2c41d440c0040aa10700440501d012400494806010300848250010340c4800b0b0151680d4425404503076005641c1d13400703002c40c1004140e01c0c1d1081001d07a0700314400e00124a0f081c070612007030b9608081c2410001c0810000c0b244280707510368070f98075003c0301c0351f07070300c00c025000b0410501015003c190360141d40e8030100f00c28945030300d58401d00b41c030030b1401140041c500c02491f0042542d5070006004e40d107098403000180d5452b9541107410315100d414650119009014030300440303d091b180201c4410900603520300b403403a181d0090301c00c1c00049465200110a031204104483c024800400010b00c0348200b10211409400003882d00f8441d85a0341c0502005560088c14140c1c907511360072004014102480c0304200c02400c541c20144400c0f400200b44800d011025402e5000d841c1d144c03030040081201c1c4001068419511141e415020085410290 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 868632679 1250 868631429 868631441
    0x22060b0c1b031c110312010314070f080a0b090114010b0706050603032a1c02031336061e060318050319181d0a020f030105060c1f 57
    0x8407104100c0503010168140800c0810590441060b44403400301900c8003250000c0300d80d54440d8441c0001d000c801c1440c502c0a4a1034003e500400440d0350040c3c801c40360a080031789603840305910840c000001c0001c80404290500c0b15030700852032611954444995601401c0300c1c88400c0715001b1b180b030010480d0f882c0c15000d01129030107245c1c1042a40e0360305041c581e0700e11030755020b01074084d6034500d41401c2c29201800c0804c0710074403400351641d040d280d80d401e0b400207100000020142c0c00c081005891901381e030701d05d44010100c0e548074602aa0120b80311003407202c42c901c40c00c03a40346a94100040740088503040742c001030a200c101107040b841000d041509222641c0500000241800f00d07030042280340004001506030018055132824410030904108007070303a032480784180440408071b01621903500210900800761290000744402500b5000703a142c1d0401060405203c6c414000503010401c400141d0341500e4041e42c1e16982e9008150805140c00329071901840c04001da80e1070781985c3d1180790031030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 868633929 1250 868632679 868632703
    0xb0d0902041b1107061b14060408030604150315230109020a0e041b052b02030403031d06060409030509040e070f0801060e190605100e090604060522060b0c 68
    0x1251040e00030b2000381c1c40b81d0304c51284900007482010142c1413041c0c48411284c041c0e228405200000c40d00c10502801c110341160306840618002c810007000d4280341c01507490524500d0b00f49803415085036035550320304070002003541d00c03240e4404050201c150114068104040780138240c0e1807a60352000f5220180d0700a184240c00141e40c11191140343c145409903075040d81404403000c0e04000030420454a03900303c0180464030369a0000440d038064005000c1e00503d0700300001c00f590364079042c14083c0c01d60b0340380b0f0ba01c90741c1c500b1081021403803282d01041d8181c204000325004554140c080c24221003d019400100b5406440d00c0301e035084ac41d100003030010480d65020323441d903035450740c0c2c408241c2200c41921400b80342191550004001c1307222400c0c0140179660310b4400090703640c0c0b5000402d01b1183d4812928000c1076803c141c0d80032901c6e140c0105540504112414000a401c210208070500d0307000c51000d042c0100c803c0390800c50140d83d0011005050340b80a0940c485d030100c1c00c126641d400e140d0342 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 868635179 1250 868633929 868633937
    0x111c050c130312120507020303131104060305011410050a0920120603070e06011713050111040801061e090c0c05251a1219140711160b0d0902041b 64
    0x130110590b00c150061512403503250300a1421980c404a02c000082500e0740304850100c142c01c1540960b0340d851040740051800740c4000102503c516a0120442101070f0680c1d1300450305180410040e562641310f60242d071080e07240030a21289201000891144210b0740100b03000010600080505c0c0c2c120043c0c2c4a46000c40c119010319544010f561101c5209565280c001425690045600624400c485030400d401e40c084503d21748aa40307400f030840707200d0220022000c01c0000e0400400f01d017401410003501c040302c0018114043c00c40004420f0105104680f000d6840d1890b034113a150286d04001c01d400d800c10b0a07200c200c0681100ca400d50030089007101410701c4217035004141c078000c500f29040d0040004000601d407055210494107843c60084c002c070041c9422803030b5a640744425000b6808029003205070500641444c02c0098100000c503242506e05600a0190030403581410440204540102c04019039450281140001800401c100030390423070f08120740002c00c10450305a104003040c02342c1c0d07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 868636429 1250 868635179 868635197
    0x706051c050c09180c030a0b12070303020d08010e2a130f06030c020109050307020d080f0a090906170a021005070c0f0608060d0309060e0406031401060306111c050c130312 75
    0x1801c2c80c4e89210a40b10440494401d0000600070860b540c00f0681000e8001c0540001c0030943d90050b1625100e504200d0041c1c000a003500700060b0402d0b50240500b18809095019190840c0d81d200b03021000c001e490b403600303000409034041000e02011a2080070350000010a166100e038079031003400e00f081c816040001d240901e0401614810310031010103035805409985046140e80800084011a03031064401c44410062991080042801008801e80907102c2c1c80c060307403402c100c030401c4843c1d5510164524148004c1c07900c0060020035000500c0e0340c101d645000300e51209030200c805008002005204004110001c5251809001c0c0c10080350301e130755a0056140c1e1854144402900b03a504010007140301d06d1024002035000b03076401d86510743e0103400020015500c1d140c1120b01b4556692010041c1d540b10800d0041c002da600854441200c0c2d030000c1c510b0074050700b08074199204800891040e059549020440a0080c2011181000b0b090100510069101d0810400714501c5105500c003042c2898 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 868637679 1250 868636429 868636459
    0x121b060b120705010c2003030703030b010e06030c030a0f1104030507030618050d0c1514041203021903020d0f05090607030f06060f030c121b080c0c0706051c050c09 72
    0x40c91a0690f0300c1a5207956410500c2e948901e4080b85003980840301484068210855460410141c4161802a9030101d60508208005010345160441d541e000300e404104000101c02080200c1e504041c07059000503c0f00c181e0711410000f01319800c413070b0a0501000070004140040040c18909490180301e0410040f501380c9948040c3c0d9000c00030080c0183c000010705002c1c40c0c02004d1594480c0c7c010400303080001d031411303180811140b00c0c98000c1c0154001106220901c0071080c00c0640e08032260600314604002820402041d980a02c0b04204040d000645040080c0079500074401c9041101014030082c1008400d45403502c00884054000a24241a00100030110b0054104440c0035403034441080c0d603541c208502401c1960030b02c1083c00303502c0f20700c80c0c83c041c0d05104041d0741240100100c1d04040c0001d030020803141000d0b040c009031403801d11813038004000201e042400c445080c1089035a5103503540d80340c210b94540c0404d41c003040d4503010030840c1240005004040080c021110041004204 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 868638929 1250 868637679 868637683
    0x313030c0b07211205040602190f0203180f042d020a1d0409050d02060702100506091503070801020c03190c120813020301360f121b060b12 61
    0x80d14010f41000c1d0406000341c011403005a04956249030f41c60042c625107010101e0f0001c1e510180c80c1104c6d00c960000e00003094140d41e098030b03c4032007558901116010700d0032400a68a004d00701c60016500150b09480d070070390751008400c1002e01006003050001c490710500c602c200c0c084601d50003d0780d240e000484143e181c50743c802c98150741d580c1e480b00d842e6007460810310540c10000f0f203840c0d60801e80d00c0c4481000300c1c40070012410558440e500815a80ca44030400900727040c21324002664850800040c171040382d6400055039481008404060000185000081d01d40b03803031940709000c1541300080d400200107010008004800415010004002036114115444001d4400143c00c06080c40f0f500040a0311407038456800c6119422580c10310304c000e0b00040e085442403100d40140010710301c1c817103036000c66004103903150021050552069010580f02c40701c0565400702c000304002102500400041e004400b0b04d050780031964121010303c0740b18030f001c40c0203002100c90944620351070400d8803841080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 868640179 1250 868638929 868638937
    0x10c08060909120307031d100b120a1707080406170136060510080103020f100212030406060f180501080c0f060d020708071514040b190e0313030c0b 65
    0x1882c1d004115500c08101c0250254101803c480c0400d0740780c000c0c2104a044580008000715020f00103480030700c3d002d0f110601100ca88204590040d05000f8010000e07020101c0e0800c681604404107850905000e2465640c600c0703242001041c044000c5001b1403185d03400558500e041e10092410209640c0710b215003004010030000600c3c00c1080700000790614000d294140ca12120b0301080450500e8698000400599002400c00300145203000100203620f410305211005c0f84090300e4000d00c085030214000c0d2103d2940542403c1410300001042c20132005910000041200f41420030040ba242c901440b070240802c861145c642e82002c0001c603130b20744045146c86480b100240000c400304040c000f072041c0c40d00081200c494441d0301380010070128801d8402070040320711480010388141d03080c030815402c545a060031013900300c3c44a020000080c1038101d5040e00074801d251101030024440500502904d03440b40e1409190202180d4448241e4141980e00c064034030900e080e9120b00d841e413400e11071302e010b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 868641429 1250 868640179 868640191
    0xf0a020f0a02100f140301060314011e0506130e0c0904150f050d0501140f1b030103020f0108090f0a210c020303030105042004060f030506030c01081b1605010c080609 73
    0x100007007541c80050003066580c41c3d00010703080c003017060740600b04049502d4000340d00200100e5214003060341c5000c07410958a000d4400145501070f00c2400d84c84035442d0b0340441c000c217400b9410001d4140c040300b80d03101c9264002c000c20858543e0501e0680080000b642140200d54011420030407040490616400f4030310136034107203504900442c1d00c0c00d0100000b85411030015070381da541e00c22600d898000c05001c1b15200e08a40100c0d0091400d1140042c04008d14851503400320890920042c00103030341e41d6019000c1d0310000d285c000c289850b94100e140c1048a00c68000b086403241c84480410000541e01c014038440481c20700203103030781d10b002042d02c4043c1e68803070083d41500200300600c00d81c0b8055211501e1040082d001c4200305a09a8801d81d240c4e003d50440808110203070f02c5aa0315170303858056a644040b065001d0b11482040c0d1340040c0025801070544a040c00c100d0030054950304840d800d83d4260115004007100e94811410254000c0c0410b4440d4800501000d000644900b4a90030050080c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 868642679 1250 868641429 868641439
    0x10b0d0507260f0a1502120601050a1b1208060a0602123406050a14010e040807020d050c130c210e0d0504050a08010504080d050601140406120605040e0706180504020f0a020f0a02 78
    0xd69070400442b81075014210f210305200031101e000034020004a05031aa41d885004000c0b4503404060002d40203450040c400d034403940352507070180001540804e403050080c0040c01e0030390b215950a2502074000d2040c840f0060606030400540c0c450400d4040315260040c040c3c0d8082040e80c0b1424205c0068624044081c40c0b1034010030010014112a03100503944a40600410303418a1016030000b03120009882e020b03660740e80f0100002c080703482c1480117942082401d00c0c04000d5240c111201500c812036041c030000c42c1019414031400309185c650441c174140f0f05403a054806c07406880001604a0700540a05400b9440101c1d010506400501c603881c06290008aa07508090b280420740d800341030000c1c4414104408a5070040c0048140702c003034009000300b903c03540d85000d001451002200d005500042c45a81041a140c400c1c00300402c01c0c1d030554031140b03008000b50b0581d120001c00c11145902c040d8020741f001941481500804002d0008000306900765486a40c030b444c016030781c4480ea288c1c007950007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 868643929 1250 868642679 868642681
    0x307080a06080a032f060103050f0601140d05070306061e050a0b030c070c031211010c021609020c070519030506070c080405040902130507020f010b0d0507260f0a150212 74
    0x20a0054100550202c0d55204000c1c9075081c4008001c0b169401d80b485c05617945c0214014010050103100914070942030100038030540d0b26190080a0000d4a109400d00900022140e481488010b101401c00345030420b030207000840d501c2c0061601070b058400c1107a1040c1e001c4101107040d01c1d1031180a007c94200807503090039a207442d0141001c60384180e600703c5031031080c480004001224900c5801403c6069219811207030920381005081d21043ca4440b803c6401210300380a100c034030000d07031700141c66203150016100c035490302c000c62030980180c0015a11017100b041c1d0b48201c0c1c1c0035111035000e8a1040050761900c0d20380020a4480c5000707403c0090010005020900c886d0400d80d0150440310300042585002d81d103c50900c074100d60055600800503045100c202121f40740901070840c94503016a0140400a080c2e1980c98540501380038210207051118204000d03205031a00303200d4511401c0b4142d45030614031090440d0307940c002510880e414602400d812a802e446403007030740c507003c51891654040d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 868645179 1250 868643929 868643933
    0x90f02040e3a0e0a080106180513050d0815210d020303010e042009100503120a08060d0c0f06120c0f0e0f060f0d050114030c060d0c0203040e0a020307080a06080a 71
    0x240220140184d081000c2c070000103204a824090400208011700703e041200703a0308040b080595100806003d903003592844100b00140c40042d240c00a0f000c3d900d01114241c5510a07001c0405401400c060b42c01050001c1980c001c50240d44103552184800c0100d41c2140029241a6140e0100f44909000c20020f04005070100c0c00c45451901c00320710900b41d07401c510100d000010403400069030030b00c4030b03421b000f441800300b41410002c1e240d200c1c0780001d0440c2000c920f803400a01101000b89030034043c17000300481c9410000d00c01200000341204025000041d03807200d070000c0c000010b1f00d00002c1164203200440720ba20b07000e14103009040b901035585000b030880d031100f846804600184119081241000b00d1041c8514030000f401c3e1800b082c4602140552502504c60750b00344a11040c14400d0304008010b05081c0e03584421140345a07a0040045403040c404c40c030680c11401690301040f50b69841104120420780203a0003184a406251a51203440c0c4880c0382c220110ba4403801002183c2c1e001c807002d500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 868646429 1250 868645179 868645187
    0x1305041b0c1103210304021305060a03060b0d0f03050c010621080a170a09140102042610111b0a15020d0e010903050307171306090f02040e3a 62
    0x9000b0000d4100c4a107495144910050f511035000d1110842d4800300a00045281c601102c110342502070b4424031031400c04034000340c0c605800744030042c80d80c0e070b440980010b01d85511041c560b20382d070010f241890808480c00d0103000303a40b04000b166040c0d464800040360036820a0340041c1107080344844184646115680c3c0f41344d59004d5060802840742031010402c00c0c0074400840c91068003d08000300b040035107850078070502d0b9204042401d669005100038050345c84000240b0020b048640c90360074100b800c441032141019602100c005609080182c54000b40035000000c0c010344c181c0101007203181c051416125100d603044a00204600c2201c02e00c2c065000240e000303820500c01050001485180250903039007120141c4c402100403070310110810248070380044060240f1441c00e20014a03070318005c24040100d070032000000344280c1e03865542d403003800a230300c80081d250303039002d0010020600040816503480d40c951220b110100c01313810008100322683c0345081d0607040004e5600386c1c0e0038440310040c1c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 868647679 1250 868646429 868646453
    0x10303080f25050706060f0612020f160804080303040b0613050412110106080f1e0f03190c08120103050f0c18070c080406050a09090e151801021305041b0c 68
    0x1000f000018031604000c182c0c03d01c035081c01170005105062815241c60f07005001000714114041c455881030012014407690242110600035541c0b00f035900c503458a00c0c1241035030049400c040d4a5100100400007040000c0381102c1c050b09045900700004102c0d070085003f56001164024040e10b002000c0003c1103010301c84102c6030301c1c800000030800d241c44064807484c0c03c440c00c0d90016980e02c00d003082c041452100c0501c40c120220310780a0044000401c08031a9a072013a10409122000c012000b401c001d84140c15158081d640004102d58400c0c0c500c0c0e11100c0c0c0075080c04183c501c0d0054141000500d800041d00226050f8080e0090064007085251072824280041810341805100e010340340000300000c00900113406252240c0340c60f10101240244a80c1481e0410b04042d071401d005140c45190000342d03048440142e42102880381e40d0300c2e080c80622002180400801d6001040a00741d514001d1207210176038030300340c40c1040f00c41428001c000c0b0204072000003070041210140740b0000b10701c80c16085 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 868648929 1250 868647679 868647751
    0x9040509101a0906090708071d1e09010f050a0513091205070c05090f010306050a090503300105061b0a0f0b04050c0109180207020103090c080105010303080f 69
    0x1880c0070418001c403140c2542c80e084034150056880115407021450412102604000181c40d40211172034000702c05880d001001d411902800103a0702a080c0044040c005c0801e110700c06440c41d5000b034284500c11082d8030441e00414030911010001040c0e01500c000c0800c21600c0092650658900d0f040030b110903441c2001003c01260345440c5220007080d030465201d03040c2462641c445a441c2c80714105205641c0b043c0d00300030706c80d40c845410b10000080204030141541d400010010301500c4614022004001c881402025070001194003c0d0040c0c00f001606080c650407690300f10b136000040f40c2402d90020074001e85900c104207212030070101103400c041902200c0c01204542d2900483d0703c0d01d903200050340c501294403844039020041041018084004407080030701308419550704090245009185107030030440110340c041754081c00e41e07108e0f070010b126403a02300c4d0f054804183c660089a000c0c200901042d000301c0d0340c0f08081103155800481061099141809419040135617010790703440d550140b620 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 868650179 1250 868648929 868648933
    0x70e061206240a1e152606010e030703030518060906040b07050703060216030306090c09060e01090e040b0a230a020304021f02060402032802120307080f0310090b030309040509 77
    0x1244201c100d83d500c2c0c1314620101d0b024a009444c3c080c5402e0484900c00d100e83c00c00080000448811760700040310000300880c4001411155035140040b5491244040c0ca01c0c0e0610444c81d00005058004000b4a021a441d09003802e404115109010341440350b00903003a04a0b00c00c0000300000d40102d00600342c000c0c0300304141c40344141d994580b0016a0026450707401c1041070100500c1c1095094412003005112a1900b0f0208030310920010341800d0343c5104410901c406009140da50703a2041d8610800b910403140350b103c3c14101400c01070002241150015006c603e02000c900460408031125402612075402c0e0400a80d076503a000ca002c0d40002d48120713000f0030528480308e8a1101c0407103070342c03220480b5401820743e07240c113004040c81c1102450010041c80d1a0b200c003030a4200d001c0400c03048964050b5400c0d020a0481c08510303240d441540d40c0a807110f40045520300e40200007000860003100f20b00104003446407504581e404981031020040d0b1305a104016040032410a600015405000e0b101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 868651429 1250 868650179 868650199
    0x3180206070c05031b0405060a12060b01121508060c030c070611091003020d14091218091003150c0813050a0b07030b041a01050a110f070e06120624 65
    0x401e2403e4045e80c90a007150000c0c0c601c0110506140c400d05a1000084894803441c41c40d2981c042c03107446981c0405442c01e9120480c0c5403460b400b5040001070715000c90020003500380c0d070680b50307020006913018200980c02801e0104019061a509513405241d9203e111440c00c1455642c0000910740344c41c0740e25050b4402d02504103543c1d6081e039031300c0301e1500c9900c4c0940c1e9104c0c04131200d0304494000c078104c818821700c0c0050028000c3c000415020001100c40308998400414440101108032203120b80d0380040078004010001c46040b814004403446100c0580258030140c81c440e094820104c0c0000c001107400000880125544403a40fa031540510706940068205840700012000c0031500980401d848070001141d40c1450700c660f610254648e8030854000d19044002007043c801c01404100300a414458941c05c91014000720103a08510782c115503d65564180580b44881c0484800d03106600300c4208000d008001b140315032180c2981008904500d107509100120200095003a6030003101e015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 868652679 1250 868651429 868651439
    0x8010b280b0d05011422090807080f0c060a1b0c0305070c0306020a1d150304030908060f0a0506090f1f030b010b03090706090305060c030c0909070e0405060103180206070c 75
    0xd00240140c280c040710224a130340c1402c411404001130306120b0340c0903014500c03000d4003130b803464034062820620f0010042000e41c46800d01c8045070181c2c5030040c064120015010030b82d0800b10700200302021511054502c1d903a10038a022044400e441141c008942c2c0120400820354400c1a003041030900c40c1c14154100b03800d5413110b06606000e43c00072a20b5076030005106019640000b030036420010425460703402d07104840d012403a03201e0880e0700751800003c04030220703003094002d119103406801c075039003100c0c031a00d0b11060b004c10095040d11468103035850400450300c903091030806944102c80c2e44c00c01106a403200c8015a1001d141911141100700c41c0c07100c0800001d900840c6180200300b0b85042d15203038109140b05c40d0030b0a01c21391203513040c000e81501c100005103000c1340113079010030010001034070713a82c42482000c2284244094258030104090170040310070303008440c24640c1e000540d4104090b40d0340304015030032110351a007200603180b0700340e05480040c40c10000525040d0b00c42c4042c54500e035512 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 868653929 1250 868652679 868652699
    0x9040e0a060f0515010507080309070512010b09010f05031e190302010605030f01090b070302030c090a0618171005090a05060c0409050a0209063109090c08010b28 71
    0x40c0d5048511603164103015040150500034160800110840700d0704800000c000a4801d110301500102000008000201c0c0c2800c10b22941c00203140140021000d04240340e11603000b091803140c0c0902c22162a00041407107862000c0302801e40e0405001080c1110707200300c4030034061001400111107881031503441007480301035000c5107400c18881d80000c10350b02d0070203007058242400a240300c0c083d030b0314011071807012030881480d403034025200c0e060041e900e0307c8032112882144900842140c200c0b0303010000140040c1e00c038210071150003014030020903954607511700c00c01481d4032210355140b036444045049401c1050703034440c0341c0143d03424084480b5844280d031040c0c14080202c5d50b408403268041402c11400e410f07801001d40c03100c1601411482c00c0140400200c40340105025100102550821150302c603c00c40c804102c00002c00542440b601e41c0d8102c40d1014000a040407504a0104107001548290500039200c07820801071111800f040f00031300c1d83c2d480c5981c2c201300811221504200003500303142 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 868655179 1250 868653929 868653943
    0x50d11160302010506090426161a09070506030703020d0225140708060103110d0b1f0b0c0307080705030712050a0906170a050901060521071509090209040e 68
    0x850061044403640c03078100030b421600700518450043c415036040000203440c030041052000c001c08070200307002c031000d800c1150034020704000942981d017140c2254140880000b800200408c0307000d07429400d0b55030f0500d168840d8010321449070044030a00c04180380b103011360050084003088240060401106402203141941c40300421019044080c0141052000d1100010a070004c0040180a15450205829a650014800904214240d510601003030b61a44101002c1c07070740081d1592501d08148101c216004d032040703541c410100716100c00048040b0001d09480c0620a0f04001d5400c044c3c103900d0320740941e0301c0b00c0b40c1260140010030521002413040000c40894050f15540c0c1038844e4100e03000039100c18842d400c0a001d10402d80d0b20100e409a90381c0c981680300518440100f61500c2d03000341d05015040c1d90b0001640480d13940d000c90705c40c0c60321a14100050a1080c00ca07808180d03140000300780344201c0c007031300c100103500803009004450003030300200f05000024000091455002c04441c0c20800303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 868656429 1250 868655179 868655197
    0x60d052e060314070b0414011b050f0d1101060f0b030703061d010f0f08030315040f0e0f150708071b0c0b07050c0109350d0207080118080406050d11 65
    0xa05041c0d20300f0303c104204540140884961003441e050030035019480b03802800003200d04011813019013046c10600c41001c02c9040c2c1e0301c20120b42842c162000d1346921201c2d203020f00000942c0343c07a8030301010341050154a0459104107900c101060802101300303541d0f030004190381e0606407201d8002510212030f0400c000307800d083c142007500a5041c000e1840a098883e84410b040c124010010301aa00d030100480c1e401640062010701d10901e0200454040c0c0061042c1184540c07401e030000600c00070200308c07034805090407000c1d030300188030743c062007805900e003a00e000c400103007d00001040180640e00e0000302c83c54901e80c0040101036540e944982038119002080c90075000305180e01001b0341044800103a43c400d00b0002c003c141001d00000c01d00c410111043c2d0b0b4074021000365091a4443d40c00464064007284c2618030340801418003075036030040c510800c0240d620740f9036000503190100000700780d803030741c425500b901c2c140c40d111045490b50442c201c240324040d37a590314082e00d103282d1401468111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 868657679 1250 868656429 868656443
    0xe010912052b030b0f0a0b181e01030e06040c0501140c010507120c0c020906010c02060d05041a1605041701021c1a03060f0f04030207150504030b060d052e0603 70
    0x59001e0b1070080940304207510f514050308204000d62219074030440220152030f00250700c103448814422849000d656141b61050308180134000c89034100b40e91203070f001810407082e01e09100743d005414905030b4840044030050940a4505000d0000c0e6100360501c034203502c0031002042c20200750449850031124181c4259022401703050000501d40e09a00415144c090142088009008141c02048188600910080c100032088581104643d56041a03414000c03400380100281e203800e180c196159000317004172199072255400010082e200c0f042c681c1d495001d281d603c142c105131601c1d9032050540c030140351010702550207121004a4092000c2c0503264001c480c0404100521000500914178a0000005010350409010071080c034143c3d5401c150011801408404180e4031424201c2c1448602d411480e8a01010095080d1881d441409001503038018a400c01175a04c4001c20400000080e000040054000108a0038110040c1ca4550019001c1710710301c406900f40d01c07407200120741d01500100c403a2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 868658929 1250 868657679 868657753
    0x70b0f0c0f131a121803043209011a0703030603530c070e0f09070504090b0f07090b070605100803031e040f0804120b070e01091205 58
    0x105881d055590f00100c81d448514084164030004000003009240070f60f0802104040000700c2002c2040b0340062284083e114105018415040400400020039600d030f046904503601c424542048628100d50000d8040c4281e03152160b00e605203504401025418140c1d600d0000000c80d00b00e0b101e900102c280410000100f24000c0c40c151502030030140100c1240c1c005005040703100e001036480384000300c0a40340b5140c8a8000107030191804100b50840c043c10181d5505114440d9080c0b40c4580c0149220030039120800d4483c401d110444400800c003405030310440e00030031000d564020b01c95070044100d1400d248a075480c0e12880044c1d5000c0042100c0e010354403402c00000d41c83d600b05800240107048003840c62340c2855007401e08a6a01510344010401b17003c004039040100406940030910742c03107030b602620345907107401c0121320103025a000d407040c40b424400a040d6510516111300000300c1611070701034107810f044294030204602e201c1180e441c03081c1c0d0405c040e44c0c02102c0300700503d050410024805 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 868660179 1250 868658929 868658939
    0x10c020405040f0318050d020904080f1218011419060e090c0f030109081e1e07110109030b010b0702060903060c09030712020a0605160c06020c030c06070b0f0c0f13 72
    0xe034048101480011710484018001076507011240241c05030111804080d03901c0314140f00160b4031402d000c800d40c1650010381b2070000c0c0e90944003644075a0251140d1400064011809400c0c4d400449401214040000005500580c1040008149821401d0000740c194403582c811081300801d1b55a009160b00481140d805460010503103211000294002e000510060b41d4100b100d000351603e0fa03040c40f250f406c2c030b2001c85412030147c176014212103d03240922103440b03d030b5103a180d200980a941c1c1e40c0782104002d0b45940220f1641d41241d51112580699a00e01410301030030b41c000210880c0d115104100f6104e1039034017006903038020b81494600d00e640d03107001e008040c070300707184e5070302600555603481c3e801c1025a44031401c41013200d00f14201a540d60000340a08081e459220000904444032460041034555002a1044c0044000c0c3c08803824452040200709441c020b211008040071040300004129000c1c2c020b21541056045d0301d181d04080c940662000150040f20f600c0005e42e07000102044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 868661429 1250 868660179 868660187
    0xf020d050a0614060f0301030602070212070f03021f0801060e0f03011d07050a1d071106161b0c1419080609060109090b0411030c040213152606010c020405040f03 71
    0x20040710204d50552410701461201d08180c041444003508150303000c940780042d5120b076000d4642c00083c64054070b0050f507d81940780000c01035800107174050f120000440e40c0038600346400901042c02620b415155038a04003086803ca55440007145d084425425840040c2d00e0034041c0259084085039043c21080ca280c401502c1d11b04c569000c5880f030310b8502c204200c00c28800c4890090001400d600c00e400c0e0b52044801c0d80d00e02801802d50441e8885d4108000c1102d0110a403074050301000da0305e00c20074500c08502c201c01c1c1e156221014001c107888010412128014118034100c00754003801c282059164048001040056540700c00b1094000c5010400c080d0001d010540c094280d000003000251401d4a400c20701007801000288050304240c28445903680400c00f520500d00c008105664498400b100e42d1604800d900c02c5d607400b00b104030f64946029001c0c5090710580550360704440120302000d20304005085000c0c00184c180210103406d107025880302e028540c49507024040c000703022030943c81c00170 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 868662679 1250 868661429 868661459
    0x813030c14010e100b0f0406060903110f06030901090224040b03091006030c0303090b040303050306060705070b0f04061805150d020c070b0a02100b03030d0903110307030305010503070f0b09040f020d050a06 90
    0x2500c11441c08d0703c14012503402c030603182c00303698000b801e203180da401d1500070801c0d003581103d01031341c400004402c01401d0f10054102d80c9465201f030341c400b402a01d808070340240c0060002c000c12001002440280101c4130500301840e8058070f0103040302c80c10b03540a900c001c101d54954006407229500140c0610501d13811299807002010000301c1103240c1032454400801320b0002900207441a100080d6100a010042042002030500c81207500e942e10b1101554070215406403040c2c0002c2103d40c420003a102c0a080042c85c111040a06514101840c81c0c1c00100240e03c9180002003165080c003031021910340c10080c41c800341111040040d5100c100c00380292800201608180a0504050380340a0546011050340c800d8100c094001c6201703190b41c80c050710380b20603003810f981c010302c07020031004d041c1a410380056040b11820341c1507a441e5030302c41c1042c0b42e8041984c040d100070520100466074860625501c0500d40074400e030350050070a42603442c01800d0301c0054490840c0d0310744510303084c403d0000c20b010708 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 868663929 1250 868662679 868662709
    0x1303020a0b0c1501150c110306181009020d29040303060e180a0b060a09022113030e010e0105040506210604020405010e04020a140f03070813030c14010e100b 69
    0xa1002c44d85401004007a0f02d81c0007110604002050410908210307000720204620b06008003a5130f002d01d0041070307030486001d607615009904d11031007650051080f064820000402d4010703040340060640e546403182562840200c1c0c19410005091040780003d115220300d0203a0f20aa9020900e00e1a203084502010320103403554595141e12581d102d840040010341580090b44094203940079500c00000441c0080c85500551b20340e80001048007110008040e041c903100241d501001c60782c4c48880c548180e07071700c8081c80100482c3c034008203400650b0158116000187c014900585070507120004140d40c1d40216100ca0000c400c184204c02d0050740705840f06501c0041a2821030510b40703440002021000424000d034040c0b50b00041c16401c141c0301c0d1541049080c4070402c1a607a400f000348100010360700072a40ca1000460743c20210780000041d182c0091402d0b0941d40c0c100c0d48211507220480c92943e081c0302d1010f90f42da10214100c46189c144a0007011800c055800103000c288a403d200d0441c40ca0094 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 868665179 1250 868663929 868663963
    0x907050a02010c140a030911130219050901080a090203011d150702030a050706050a021e07030e010503010b0403023a050c30010e061303110703080307051303020a0b0c 73
    0x1c0c9924400c501d04c103440aa00080c075001c110300c1e01d0b609241c5072a240380558180c000f200080d02400314200c6400a181c06044440008400c0d807400c0c1c000c68403400b50000d014001131114000c640782c0400c9400111903280020000282081358031544003200045818020280d04082210030080c0500e02a0940c00441d03030020310b00d00a10410010f11510600000410007a81c88020030600c52099055500d02c81b2800e041030303041ca05001000290350000c0d08101c00042d140380c90420603500c5542540e048500b5501001d0625003540d080054103030801001c600000c0e04002c1e0351548001884424009083d05801c04003040310506040b0b0410410911940c005c201d8600c1801d0740c40801894400c01c500030300744044c4030b1064400464050034030074500160512444050101c1044c48400c6030100500c00d03100e101b480030b041124907072146031500c00540a00e006200082090340900020b0403481d80c442d80140741c85450360f000400c4200303030b600140c0105801080240c24908204902a810032048074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 868666429 1250 868665179 868665197
    0x6181103060f0c0a0c050f0a2d0c1239080a11090c2107030509010e0604080a1b061a0a080604081c05180106050f010921020907050a02010c 61
    0x21100b401344114001c03002040400d05401050080030300c0380d40e0104402c3c030292200b2a210342460302c0d4840140d0702e0001e401409054118600720030750528501203901200c807a1300c1d40d02d03107002581a990a8130081e51180500c04440911000a07002181c0c0401c0b8500d0002c030403028000303682d84501740394200b1006940b2500589010604c180030b5900500e408840d41d901c103544942041405018004e40d140d40d20b592010140c1d4075a0b84040e000744030340d4032503038200550f41e144022242604c0307408408400e950060f0001c100441c509030000c04180c451410003d00c1003010400c0010a41c00380314042d40c125507070302114012107002c0440d28a800c402160000c0e03040782403101140c2c994001510082044a0001d05040c448548401c1071030050b600c070200304480e00c0c00c030b0103000280d001ca03403140b40c05501c0c02704046603901c0d0001c1ca4241c16581a580d80103200d09141003280c030109000099500d41d008003403480010b0313035500e411303a105e03100030384d03e103034a40d019448045d007503031b039001d61060a02c03010b07107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 868667679 1250 868666429 868666441
    0x1d0106050d11090705040302100203030105090f250519022d0d1101090c06030c1e120b04090c0303051215060702040c0c021c26041206181103060f 64
    0x2210a81c1140003c0f070300121141c89036181691584210350009401c00309854845284070707000f00186040318000d446004095660b41c08031415444112625075180c1c1200d0f40309031040200d1781c0485500416400c01529010081003c0360748200b9108403038005030700c100c201c0c0c03030f02c0d021421124550740c03c2568040c441d50303a4000303405d4171258810104010401030501480307050400b5000018155000380080142580750301e80207001e02006c5040c0c4003c41e40442211440300701a1540e040c40702055560258108901e50300c0d030000d42061a14694080e4a6205c9000400c2a1003080310045210391604c50fa2625510026029410001e100484503030f8084209004c6448500c1207038030302503044500085407880a0420344076011241006500f01c02403400000c01c049440030104541c1e4080c0791411a2910401d00840e60009440500032a015082c0420010140100c2844502604c2038101081da601d101030441e040c1d1a1080d07040d10803644d446032012541c1400d10074980c02090030244020320f80703414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 868668929 1250 868667679 868667693
    0x4081b1c181d04081204081908040206090114091201020c0607020102190e12070f080f010207051c05120c03060109050303091503101a1305010804050c0d060f1d0106050d 74
    0x1880100d030002c1c1d00d007000141000000012a50310900c1800d00c0b0446007801c0c1480c408640000781c06c9015480d41c1082001b405025a01c203e204542c001c02c036616060162004484100c010071180e511002c0a01c1403003469a10207603103140301481c0070001a110407080c5115854010050150740669104002203504018100c2c00e40780145070341d05013002c0400c50078010405085078503544c0046405600300c0031a5840d440c0c0c0e42c940440d1007101c201d4031102c0c005107065080744202d1400401c10350009224603152030480b40d15140c41007070760030280e041c08a203401c9a9481001220007962205002041168940e0000408800fa2406038011030403c10b01001142d03100042d10401c460300000030001452100c0c05d02d2200002c1d010369007051804214206001d42c0d59041a03100500d024603e00300400ca5511072801d2601ca240c02c20010328061418600b40007020035004002d9480d2511918458980302c1c49018003070b005020b032030100d101d88046130285400c44400350041d80c8a203030000074400c081402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 868670179 1250 868668929 868668959
    0xa0914060f0103021b03070204061a22050d050706080a29010c08030103120224150604171f0203070818011401080303040204060e09031c091703180303010b0304081b1c18 74
    0xc50080d40d445007424cc4081c484202e0b5000d207901030f00c546032042c00c010001c50780b8811104162a07ca80070303180c100e0b50000360303400810034151043e210201d00b820301d400c9815681e54403006040090b07051159842d407400d998000d800598000b007100030841c9030103504210401c0b040c124200081508102210f500c10780e000046c0c410901c489841a002d8100e5403000100ca0051003000c0c0c8600c4c0c01040d51501d1900c41202c0720703802d82c400010385580101310340c041c02120b11440302d540c0d030a045569070100044045000c88a0502c1a66030f921a03210f00905120005018001900007140c5a08e4a88104002c1d6041a005201e00180c1c020a00140c810004281c58240c003807400340749200180041110014001d900c80500660b0341222f04040d05036007800214041c08803621b002c21000c09a0088a079244800c0c0f083c0c4c80000401c0000501245407480542010710245008003511013060401504e8002d103850010104016a013420082c690491240c100c1014500c108012071440c00b9500291040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 868671429 1250 868670179 868670197
    0x6070507230f010614030c1e010f090b07210c3201060b03070215010506040b07110d0b070f090b2208010c020c0a0914060f0103021b03070204061a 64
    0x10a140c070401c030078001480b0425400940308000c200056403402c509440c00c40c481c10180c080c1c0110032040c1201c0c100f0540131101f042e02031314921200f020240c01180c0d0040f1040c4079004003c8804404a00c030140c400040880e0740c01050716510700360418608212502204640c001840f05002610000521204000c401d60201d66070f10110340c030316542d42100d40007040340203d0081d482d20740d021400e1011840a5405580e0396821a040d4610600e503000088200307028156102909110070801941c00a0003010040e11520402d80d0540020f0042118a840c0b02e00846013449110100035500360300c48056281121306151503110030385000404407071403141c00d00789029810020f042d40300003000c8400ca2401400c07014000c2040d03001c1220025156003041000601c911600440000c86078041d01941070107103240c6404c41c01a440382001c2100880c401c8611905050702800b030308407440048440342c0301403135005020310350700c032603520402084a0441e0800d0800c030090f000c2d06e0580400c44000d03184940 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 868672679 1250 868671429 868671473
    0x5120a0909051b2a0105090c010804111509030a0f0314091e030109291005030303240a090905070e04080307030207051204090e010507030e0309010503060f091806070507 74
    0x1e0049001d40b04d0382e140d00795100300300054840c42c0342d4004205500580c800c42c0460191074503041c0e0080112412101944c016006446900d4445510329004042303592034075400106500c0d00c00610003080c00d090800d10151042c54035100d24505058100d2000f100840044c0700903031402c030910001820406500300c0c001004043c50000404984007544010b0050741c1003802003411101040c0c0d0020440c0d9820713010603103a100c840108885211807507456003035400003005181950b0f5180b032185220700c620004003040d0b1034900c0d015410354807202c0a800c003800b241c41c8041005121414000d02d04121a4013004550548004110101d0182412769800200516002d0794504d40c0381443c628004140d004541007020000d00054a04055800034080612110090116650f142400d4007115100c444405035030b04200000c51803980324000071680460018008802c0c0028900400d80c2c2e40401c0302e401c0085180c020458803000c404111a03584140586031440c07410340b2a0703944c40d0700c2102c6403e09492203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 868673929 1250 868672679 868672687
    0x93129030c0d0618061d0d090e070e0a0902040807081203070c0f1106120402011b11040915050403030905120703050d0906020c1203070315080d051605120a0909051b 72
    0x24001c190300c0c0180e0781082041c4020170410f00c11a01186c1141001c2c1c03120311852200c40d00b564080e030069011182c0c2d80c69108510b56802209941001047c40b50ba0740c0a2844880032a04a01034406000074040c0030f401030030003a0414442c2d9140c54100021541c25130b405008121803941d00c43d05900b075207a846448050f02188501d000454000103001e415031000012400f004e40c1c03078800710740074031490007641c40d182c5400c1129180b848080c44400007410903100380401c0c817030f5410140c04c80c09541e442080421032001d0b4010250040300c505940850000e9181c2110a06201d020130000312080b0180c2d07451480c0c281940d40180461240d40c030348a10050325002554144086030341540c21015000054602ea02c110650102c0380341e0080343c600300807900d802c0b4600d13406035884204900ba20072281c000d014601a03000d05846030340000300070900e00103c8a00c500001a003c0c0481c601900c000c02010f9180d0801c4600500060740d02e400c40082140303088204654440701440407868420170301060341d91 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 868675179 1250 868673929 868673951
    0x71a07121e14041406040807080d0816170c0c060c0a02011b08010603090201031e0b0a060504060c020f2202033102090c0d06140301060605093129030c0d06 68
    0x5c280942d6003c091030340070742c1704000764504022940014043e175503034550101e40e4402c0d07007d40c20b080b16402e4260014901035800b800400c2010882e0390080244004641030014480e41d081c074260085a8006605d6804105040c1c41c43d02405034501130101900d0100302e40c10324000c0100781c0b06051044e101010740310180d02055900075446134508525800544c0549003c02020380082c043e500c0403107010f602d0a45001070001c0c8218180c1d41918020f42e508500c41549408011411410241c207a03445980d0404000f481d0510780d281184158450381d01580307030318242080850005c803c5140045c085000344509002000440c403544099a0480710b50000351152200001c0f1070080c031b645002d1007860090045640340c3c44001100c02688220003e01600f81c84000449203030207400b12140e00328094a24443d1f60070140c403091002c4030343d140396038900300079859445010b54140c4840340503200010400c504030700717a0704030000000520684c011300c001c00404001c124004031442e0007a01a6582e88203d50b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 868676429 1250 868675179 868675189
    0x1203051308090406171b03010b0105160503130e0f060d02090f04030908030c160504152106050705040905090708100c090b0c2805071a07121e140414 65
    0x2d0b205c0c42c081c2c3c40140c41d0501c00255100c0604428805840740400070103260301d01400340344010b03c0182d50b01350070500c1005420700d541c121b0b184201c5150005004107801441c641480340018480d00b081c81c0c1c510300708201d224841a2010385001c6c0107184d9507272202d000da1110011503030045c040802811940e41c0c0c9003400c0300e400c010b0780c000714201d000009170303080c4450300007035409200e000d001c3c10181100c0d0707610104004c0700d012010f082c1d481c6101260400068504510b0355104560406002d21541c1042d501c000885d0000c0f1580740c0480c3e004242444054840e1040e40e510465280c001c0001e5418107a405c0d07078a420080e0400d41c0c0945651050a20a100f24020801030021000d10b686421641c14041e84401004d00700102081c40c9080c0403103115125071201044603003007000741038401c1c2041500c02118084828002a01c1c004009003000920200300d5441503202035035880d040c501412450b06540c0d84800c010304100b143c2034000e001040c00c0d01040701d0850310b0110310014545c0581022031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 868677679 1250 868676429 868676441
    0x70303050a210e25080a12020312010b030406050717150a0506190206072610240e180610090e0f06010e040603150906110f0712030513080904 62
    0x11825042003c074066100e00000c250b03c01341d00b0300c3c28160002c4a644040311041265200b503424641c01144134501041c1d100324295040300491065034500b44d0349100707542041d4030a0388441341d000c03800420070081c8085403113000e411080d00e1500664241d00103580c8201e448018180c54400b1007206500c030403940d9941407200013484e010b80801d40701c0c100d103817880003140c8080b144134001d401039500162000b4454084d03204815400403000c0c0c406001134601004200006103840461010603d010402100c03110f058240180c00d505203000080424000905004108000c0c03809403444850a85102c2d150300c14050348654191074203114401ca058086540314015408041c0b6002581c09200001c0780d10300070288501000e0300c40901c41c05000c0c091108a410030710026240352a2224036200c1603000f90451110a40113510120b104142500848840c0c0d20681d44ca0000d41340010b10742e810014040c404c1042c030b1030311b07003020022031400c4000000c00c0c103000c080040c03050318005a6507070103507903030f034416 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 868678929 1250 868677679 868677737
    0x6060304021e10050c06180a030c0c050d06020c0f030a0c060e010b060309060702010b09160305270709050f0c03010e0705071208070828020c0102070f0303140108070303050a 76
    0x81803040f14210006881030b440804c004d04203015600002c5c0055140c41542e0f00366000d540d00a02021103c0d4404654184081008480ca011003110004080d46d4440d003000b6813600560005035124480f18203185081080240c803029608144441c40d15641c210718101756554101c0c10100b42d2080d0040c0e400d00407c440c00c2c48544c400c5010080c44890480025940c2c405e00c0107400030820340c418101080303015141102c3d80d081071400741c401c5c00c0d011482500540e4011030140100310010200d0620010034011103058121250f0040c90f0400400a240c00b8158021400803012a21400c201413040b000c1d110500813010001800b102082c2050b218004586030540c0115844125400c60f08000345514000d80f03504001400841c0460035610001c2c1280151041c89817015150826401403600070790002150b1407802d5600b4000c03000440e40e0518406900c80c825600002d2442088885084181701a00403815542c805082400041d400804451400c84907041134940c203010451a070107182c42100d50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 868680179 1250 868678929 868678939
    0xc030319020a1e17042639060309100b0112051e0a0e2a04021317070b0301050618040218150c120c0304031407061706060304021e 57
    0x1001454403498000d20b01d030a40308484442042004c250400000c0c0524050000d030540c0381e00382440511a88003481c40d4100c004429140c00b03000d01000c61800301d850442c112625208600020b00180801d88080281c003000c030365803400d60031704251080e560601007440740d41c1c081e665540d24005030300590545a402007041c4041c812071900750400c7e0621000c1010044445001001082c040c04083c05180001401200208000400c1003414107004408180840d05211000c108100d2902c480c001045418407030504191103601c1c01204064070200c4802040703994002480c180100c40c021801c072411554121201902d40c7c406041a40c11109280f0f2110350003071001909948200b21031140711641201100d805010a1525600c0d0300c2e68071804641d40700c3c03500301d6100c4898541c0b4035000b4050880b0907404581c00c00d900c1c3c3e900d440a8559045514819a103c40d00070003005a100705026046621071204070828104030010031210b00000c0e200901c10644481000500b80d1003030380100c000c4c0d1000741 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 868681429 1250 868680179 868680203
    0x102040b030c04180b01080f10090f0b0a1a0a0810090204080604020306180d0c1103010e1e01060303050301180e060109091401021e0d02161202010e0c030319020a 71
    0x520503983c0b16100d2007140c42159481c20585942d1071049184110040e1508200c542d6844a0011104001003442c484000a0800801d58a9152144c0d0070b040d1011700f00056200603130000c00c60700013059031101141405503544030402c1c24020058610b001c0450a14120980701c0700e606100120325a040385021900c08a800a0041c0c0000342c103c1c001c9000381c1c00d6500d01e86900a00410546c82d4040c03005191784a00b42070f8242a01c5000000180c901407070b00d080f0203008860010342951543c0414150304c2d480001c041f880510060415882c032045807000b0040c0b940345036005400750105204440d00607145203070740d039201c9540ea00032504000368402518580c1d078480a00d4401081c81e10300595500420b105a810044c105200300c92004410540194008070965480311141d44200c411442440d000d0151781031042e1491078896425114090710303010b03101c140200900312143c00c40002c0d015804070010b14000d0b1008001c496a140a0740001000c4490ba8402a840c1c180700200040802c02c0c244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 868682679 1250 868681429 868681441
    0xa0b0406061412030a0c0c0b030a0624020a0609080d141006051c0507050c010c0909111e0c031309020307020106120c060804020a030f11040b0d050c120102040b03 71
    0x16000c001900c40d4031091045990b80ba00a211410f1401080d040e065401084110800c501800e083c0c0a013900c00c04805c1e00450f160302d0110041d4200f9a000d222a03900c4400a001f282c440c9075505080e0b288065003040a8070841a00a6030b42d10703120005880543e60700c2c4c0410a211034003045803401000060144113811250800c0c040c451301c1101d0203480c1c00048000419a03600c14422101c07007402481c0d280710981800b107044c000500d07000d40400c050080400540d01610000e00501603d0b05c1580c448980c4607180ca40d44d00d050710400542c2c003100790f10412040800444c103080c06030b416408450042c2d150030494403940c2c0303148950200440310311400301001491140a4000390320401c0c5680c02800096515002081d60401c1548014110445040280318035442441c00c0f951150000b04110220340d500d84a04000050510701501c030300045c0f1403552080e0610740aa650642000c3d902c5040c200c146072501d40c1c444480304425032241407250a1043c01d90001d4041c4c3d0050b062441c015131b41c2e41845 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 868683929 1250 868682679 868682681
    0x60e070c020a120c09050c04032103050618040b0714070f0c06030e06070c170a0315080f031210080619050702030f03040210021f1a0a06140c0a0b0406 66
    0x100c0101d1107000e0200000c43c66040d01c1003140790342c0c0c0d4042d1254112034141a203030350141c0402001c4034005c20092000202003202248203c02d9446002000031b141d600c5404005c2c1035480060085021381c5041560351034101d11290101c3d40240c00203c0304a035910782410440d08007440040640c0300c4180030458005005003088203841c0d240c4180084003400350ba601c0c0c240d080d102c0e03680c1100b4680e080900002ca506014420210000b48902550340640c94100116681c0b41c00c4145110006592041d08060111245501c400a8000300300140540b240b2141003e6072446019140340d20615a10302294841e6110007648010f00060303010341d18030740391030b80c000041103618041480c9118103003408038662500202c2180c0d442c0402c00070161079a51150240102030300c54030158130440c894843c8058550140c10108100c44030310240103e002c1040020051080080c850504c2c400e943c0d40d68208a102d42018051075610400306445480b544000c04da1424180c9510000e00700550300c4041008028403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 868685179 1250 868683929 868683947
    0x100f080d021b030705150d0204030602090108060301060e0703020906040909060533060304030c05010c0915090e0f04050307120e040c0309050d080a11180f060f04030602030703060e07 80
    0x1880c1d08640b6007500804901d000319a0b00180150180c000140500407400e0801340150000d01304051140ba01140e0369004080780e00950003a01d9450780400d40902543c0c1c00042076411a804070000d200f0541810000a1003203005810303281410f50005910010f51105001c1d02d00405002904014100a43c01c0c5000508421a01c050329211340f08180390810404007111042904000700380b000c82c10048080c410b10368006807050f000e10400441e01000141c0c04d02808030300d00060382d2050b1180d890407582c0c031841014029030f1804d205078420240003400001a078145e000c0c0900003003405a40703a5007017090841c4150301c009880da22000000741c940070f800003040450340c0303801c0c0d80400149540147c01c800329603080d00d00405030b801040d801540280708505064111000c49000150346810a102c80620340c00702070081503000c26008003046620304440d500c00e40c488151221450200c0700050880c00c0e1050b4080100301d02e90103c049a9614030a6005101500b91403000d02501d09110030040c0c0781411b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 868686429 1250 868685179 868685203
    0x180e0318011709060103030e150c16080d02031210030f030f17250908010606110f030c0a03050f070614041106190c060b0a0b0403050d1803020405100f08 67
    0xc614030048011444104106210f0100400548040c3c0d0841d0303800c83d1b065418407c03c6901201941d0102400b44644004202140c414001410544401c80c0707841060385255010303510036003003900c04440c2c450f00402284c0040004621034551035440380848a066541e640010b00407603207801100081540066602c2081111522034018101880c8041e010102c1c080792800c0f55651004809001440040034003614100c00d03040885d110b070384a2103051f08442090340054002000c2610102016805000400c0b9410151000c1c52801620303424a030380c6d4525013070340182006000106a04812007076416150a103070303c02e03000d201c0001142d61018454809440607a8003c036900400801443c0c05d804544858800c100304d002c5200249006807000141c00201b6503d080e10f810018a0503503a042d40c1c1d0010700f1401c0100d580752811030400c50f2802c02c0e143d20034410320442101c2091001c4072160003608030b82d41190b0120305a038652140c105d4403603a0390f02c85400b00041c0100441c203c0380106a542b0003807 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 868687679 1250 868686429 868686437
    0xd02030a02010501151407020103061710230105240f0c0c0915011d0406031a0f06030c04091a010b04061d0a0e13080706020a1116180e031801 62
    0xc0d0321152503000a070005c01499003c140b400651072601256a805802068014100060410342e500b0181014404c4540140d09030341105020003e040828882c0140401d950810b210381c0d10784000c84a119150103004051040190010083c00c19407040c86042400d000a240b80b600d8095280f400105500403031601c038118060380c140d580790703400c140c007105108501900c00508002c01c88401540c030300340d24211410b0240800f507066100ea4655000c0c1d82d008511400509200343c284c139940c0c5040c01e42c0907001d6040ea40010007400420f903000100c2d051b00078421180000da007003052070108419001400d10b500300e25030703a100001c2e4403a0703003401074000c6401980355803240c104c00d585e90441505035102c090340d01c07d12026050003103d06541b040c55001c008115150060b1000d600c0388001c0d900a107404440294001a51345002d90340220340701c00a0030940c1c003c00701c00c1041440d404030f15015010b80083c1480d00d86d80521880310507000a0f0580c2d01600c1920b98442c06030740b0410902000b4044103000c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 868688929 1250 868687679 868687681
    0x1c151a072a030b0610050c0c010e010c1709010e0a0609050103150e0405060423031c0e030d0225021804031b03020105040c0b0703090b1602060d0b01031d0a0b090f0d02030a020105 78
    0x85400303001165000502e00380500100c8d85088010b541801c0008204c03410041481e420200080569001ca1480f0800300401500c8100030800140f0250313039002c490b40595606801040080d03000480041a03500900b80072a080602822103034a8103100e50044035280444002d00061000216020313000d82e000d400040540f40c0078102152148000f0f2112503296032081200d031941140c08005081c02038900b8034081292000d8811040c9103400a4002444c2d083e03000800207114444c0200c7c100c4510070401aa012000980d000901d171004030008d15012040781c5000102090302c2800d110491420f4500c0c140c6100c203490a00038001e0030121000c42d905001644041145d10460b016260b440b50b040d42c94035481410201690125001080b12005a1003ea20707500010b980d12000750814a00200380000c4c2c618101c000142a07039502ca0503100c0100000303200c0380c418240419896a002e8200310180390a0b11003124103440c06401d828402154019055500d616507404002401b440d01558000d01c89 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 868690179 1250 868688929 868688959
    0x20d0203040f020f06090a05061c110a020d1b060504050c06031512010b150f09040204061d0a0501120218030a030309020307140102071a1c151a072a030b06 68
    0x240b4843c1b40c900c1d81c0e001031409020007051034194001e048000b0305141069010502412540580d008021115440400410003010081e410004640b0f8880c15141195a078030034103180083d00411040f028201c6030301d07a000101444420407140416600250185136607207410f815a1a010303118a46581c49441072403111440c110050181203142d0340b0060a107581c10110709480c211503803195800e400034900911400c91203035514409030000b40f102c3c3c3c072504060b43c0000c0704565a0704016260a214014416085c002a60701041c407100b04080340c200143d40b842581e000e2500b00403030784070481e40351045542003c2015899003019914510940440c5d001c00c0d101c0002d212070804a0340300d1350040c0d12214082041840420340700750740c4000e0120f483d1502801584820b1030010000f03444905544808161810ba0300711120940100427810440c400e0840f0400004442e101d605005030401407510030000c41550816110800340014185144545989203494407400344100c441e40c1c4500303429040610 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 868691429 1250 868690179 868690189
    0x907030b040e01060b04051908060903031602062a1312050f060f0703020a1b0b09061501021c0302120411041a03060402010c050705031005090706031103011206020d0203040f020f 78
    0x7035170000f08a41e07013880c0c244018840c14148030b008448001c0381c4c40800146501c41400720078003030300380a40919964544540741070402c8801c60001e40465205908214045c20f01032814070401c2c0e1405014010421400c03029265402040c0c0c241c40340c0c8084540000343e01e541c1048582c0054442c10907a191004207100b12604c0e92403c8807004c4c020b2031101d0014900500c84d034000e0416108500346000b044880403441d00d100d070305d290412030300000c0380000c0c0448400d007000b08683c002c1551158030b0703030410704100007074030341d84003d40000b54240300301da00c000100d0094040e60344450710031300310b00da0600e85800c0500010024207200c80c06185000180c149070030b10044446680880a0020801d03911183c0c011601e5040a01c820740315030081541c0030610350307800e100e4542c80710803d0b640070a460070140c0410f801d000e640d602c0b00b0300b49850002d03c07011520315441501d0445880da80b400e80041c00c40d080c000045e106200c0000316881c1300000300020824580c848000c00742c02590600610b0034040c0c2802 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 868692679 1250 868691429 868691441
    0x106080c0a03032d05070203100c020304030201030207050f01110d050601080f010522020d140108031e0c01181a0708040c09020903030c030a080402030d0311190309020907030b040e01 80
    0x6070808040c44050020030300681d8502c1c1c40701018a1003940c46101c0582104007652420400700014030001140d00c15880d040001c403030315060182e0304100b2642103400c040d43e280b00b6131100034141900861004c0034003800b4008000304501110090200700e4036003102c19419881450245c0815240c000071490b603505c04c0c0b5045215034035001e00903009900746030411022011001034801545194400e103000d00d50a8005400c0300c11340000003181244511a04c00820441600246ca00354014840c01a400d00e1588203c1c160b030411503080e55542e8210000076014081524480b14a5005900a00304000c10032030004200b60000326a000c29444080301115554000c0e540901409020381d002e005100283e8010010000010220781c40e0094180820f429504072101101c00702c3e465004000660a0500441d41d20914503c1e003003201103001c001c11003003400750f41440c182400c0303003c0391101c2c03890103035100c080c1858009003052018642000001e002d41000c0d6610b9000d01c0c1410500100c90390140160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 868693929 1250 868692679 868692703
    0x141603021615180b0a060902121305191a060f0a0311180f0105090705070b07030506010504051e010f0906020a02091e040606060f0e0f0f03010e071205010608 69
    0x4264451182c80340071601402c41e25800c2c2540e0f0f0741041d901da010342c24001da04a2413140d4900782c03c0b450500501d00c111000c039071244622a00402c2000302190080e0070041c2d1004401040280c00b030b025040983c41d10b09082140040030809040034024800c01081d441c40d400400700c2022032030f9a40b9000e2015030306034150000d41194a040e4203200190058990410b01c0c0c401130403914284035100190036008a0035943c84406060010040c010750424000749640000f83c1d0804501e480f1180c1e07106c2c80021001002c010800d0340d54000309035103a22a00441c1c0040c5401054031042d84021243e01d80d014001c4140d083c0840c1c149074540314a40e01840225049401640181146d10a2034003482043d00c0024005401c14850300076a048030443c09408502039030203500005050f5040000141440020b1f82c00101440b901150010003940c4221030070462181c00d545c804007880090340881d024058a21008000d401200300101d205010802c4078610140288002c3c040c46544118444d165460a188 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 868695179 1250 868693929 868693957
    0x10c031a040507050f0a0917061b0304170d05090c10020703150209060708040303091409132d02090c030f0c0a110307110112050f01170a0614160302 65
    0x101000074a02a032103250302141034100140f4140c1148441203299012001a81c00300c0d10b42881400450386198045058202070002052507082000b0340d0191045000b030034003451400040000e0800c1318045c4010b8241c01c0080c289500d5040c110700010252404440424032840f42030760014003468102484c250741c11094000c0c01115046486421070440354003030040c0320b19001c00424000344c4501001700102801100c4070354071281103190080540c2a558044d0184101c0d0345520071f810307609c031034a071500031428480502c0700d0402031404240b03940640d014051303168013000350341607400f0241112800c8640700726030101040d030341c010200116000646040c96041c0307040c0d000400c0440100000e207840c045a0034443d0b010700d5140300851556100b40d00072900310f0090002100d15580055900514a10202c0144210b20344107181c1540315505125034021074200c0c0c010b101041038240401d00b94240c20010911440c090a1140c03428404280c0e47c0c41c602041c80705901c05c1c0c00c0d110780f0980d5004400409 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 868696429 1250 868695179 868695221
    0x60e010311101418090901020a120501150c030216031b0801021801080c0c060901020a0e030c10030b22020304140723151215030f0303011205010617060405010c03 71
    0x68444035640000200c1c0383d460140e41c84c6120184d8900207550300c5031028000259461410704001410341e441000d850044c02d0619006100c00e8414880d02c0032900010316210000d5001424100d241031482c600d00e41b1040d04942020040c00035598100c9000c1084086400290b542c41004600b01c1c4181d040046d840030000711002425881880c803141c002c3c18000740c2a042c0000c11f50300700d04040c415540890181e50010302504030581141d001400d194040700030f03050518007000842d00b08c04442c0610710070940d550751a030120795104061f0114050740c41c5088a00b0084515400c402948140c805440140020200d0031a105001030315109070b5070b03c000c1d80100102c50001089513121640c1c2826403000d032162181c981c0507c01e0010381348510307120400410750705000c000001502e45e540050b038040d8201c0c0d201c02240c03900000850381120545100c0d860040c001d0305105d801402c10350400c03110700d409094034a134070710800180e060160340681d00070418410040c4090b01103030b401c1c14034080d045102d59 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 868697679 1250 868696429 868696457
    0x70e040f0f0c1407120509090c0c060c04080a0311071a0c060a05041509020f1f1403070f110a0b0108100506041b0c0501060801051906090225080d060e01031110 70
    0x145c11040901909003141003014100000d10100800c85145891034000706030f4030340c2d40b0f00030812107822218652038685840d0401c2e102680f150480301000d424410510f620324003440080110708014207207102101c0c42400e0502c40d0b540d095221503a90442845031001140550200c3d214680c0600e40c81042451200080020702000c0c10f01c80c581683d00600a0a115400d0744031080942d82806058488806400d0321203000307081403d891004d0f401070704003031040088007a0052140c1001030800d0510b500c008000198080c82d111010304001e044041c510000031f00070000280c2076030010380108042c0a180d44140a10003141c40585003d00325000d00c3e10a41d06080c0104a5469490700503400491280c4d01c8012460075103000fa117031405400b40c03d19400c01e05044601c00c642c0078040071030040d0726042c1c8000b481c9252960b03c0700399544006007802c0300b40400c2001c008480607560b032a042800501d54030020889400000d11060703403065203805001c0700d64038112a54040040303060300d40344c1c1c41030445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 868698929 1250 868697679 868697693
    0x2100f141314040c051c181406160e01210f02030117120a0f030e0a0b06040b0402031e0601180803041703120a1104090e03131211010305070e040f0f0c1407 68
    0x300800b140c100e50b54010105205080e0700d8035590280523095440c4d5528124882c54503284004164074a401ca1503022501c0d0a688074210345924802440c14298052750303181c2d11080030742040314042080303252110881112800c2e4020b94100d4042d5501800030012840c007441d11006a001c000c1c2c2088000c200ca414014010a0a0300220302c25140001d9074501d600039040c0303410402c5006607104401c001c204403840c43c0c03501824015071000e4400b907085003004204501240395203e2034030822018031000079180d0341300b89054619052064001400305958051580c2c485d0b0103800b44840b511004400e00d4054600081115104d20005010b0340c0c540d512115070740000d041d8403c0c2c500081d107080000182c143e82c0d601503014030345103050203107a907811012290646120283d1003107200140448010703000c80d0301c1118100703d2003401c0c00c1c0030803556a482c2044039040c020300c40ca164401c1c075040c4c1c4180c1d11000d960100704034145464042240a140074002e8400041c9128001000001001000001020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 868700179 1250 868698929 868698967
    0x1605040f0f2f0a0507170f1204020a0b09130207060e0613050705091e0c0912010f06270203070c0606080604060c090b0a110a06051305010f020702100f141314040c05 72
    0x11b1640440c10036494034443c44481d4844565880d00d9404581800190314111502d00020500400b031945480003810200d20a984101200c3d42c1c4554003203030794010b024040d00f00c4486012503d0075962a803070b020740010b01e01c00c1d0304c4a040d40c09100d00d41d00801d103401d040f030185014241121481e14400455092803104010051000c101c483c401e01880c94070f51500e660643c042d84180303001040c00c1c0c90a848403000c4801941c050402184560703400b0090b85400710820104291000b00580d480d80d44e00301c261041c82c04a103006112500d0001c000a00c40390106135980980e208950030b0040200262003142c000956010303804041c4010081c800049000300e41c0441d1160030b041c146d90101c0032507222070003252022640d043d080f00c0884487c00400a007803145140c0054441c82c11414007840d074010440e00501b01001d8018010a584603008280c0079507c0581d0030001000066643e00040b10000f07681c0d400b81c0700d0809001c1c16403001c0252071500303025405548000e13990701c5007020080301c50301040c160 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 868701429 1250 868700179 868700213
    0x6090e070e041518020d0b0402090108071d030607030f0c080123030f01020d15080a0803010e06040e070303030c09080123041e0309171605040f0f2f0a0507 68
    0x80703001c80010b03038a000a00c24580d41e02c0d41403006071154100d84c2080240c8407c0c070a010701c1544100003181890381c2100d0110381107901442d0100600d1042001c081f080c1d5440c80c40650305200b00410420074aa00d5000b041070400101400e000420020005590804007805002c0140d440428841c1701906c4204008514010007011282c0581c039268440e822030b405880c0d0b40059030b40721080e6081442d00020544002c0180310000c0070b81402a0301c0b006030500040c05030040080710304003c20708540d10307038005083c0022648103030b5040c2c90340d81c5400b6009002078130708900842d1003810001200c0b541840f510700320381e801c01150407000701c0e501d902030f503241c0c1c00038000c50f0503502c40a50849a0300d03c0c1e06801c1c0300307940309499800c145800c10840c1c1c00309995814003040c16500c04135900190b404d03422200c1c0200e0300282c40110f4982c00740036045024101d0b034004002c1072464071544021001c0c160490268648290b1240002200082500701d034503c580c0d840c3d00301190301080071000103a4211700ad042625 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 868702679 1250 868701429 868701461
    0xc0f040f02042d08120304030c0210081b0906220e01030305030108150106021902040615030203190207020102060c090f09040303020c010e06060a170312040b0106090e070e04 76
    0x240c2050080c00407a049074111016595107018100060400039698100d10045000d80e00c2081d407070032801c680e4601c410300102c0854400480428101805000f06415642c0d006200342248008013130001d080610484200d04804043e1360b4004414503042c046410480d800384c6141c2c5804000c01c042100903400303011501003620760280010b500d0f042c0c282110b020b140300f641d800740d0302e51500f2040f6280c0906001d11100852000004021094000400c09103440150b84809a21021800041c00030080c81d03001d40301d000c200320059034a1980c1340e40254450144e414900742c404890071031200c101e000d05800240507901201c0414400440080034041c40e100083c10340c9032540742c40011913460f5406490440100340c001c1030740821100700b8090100131000d42c0000301214a84000020080503092254900022444041c4800c0038401d1045555012821805a104d42810300d4424000d800074814140016580040850705842c20140307070307009140c079a486140703810301082000020640d45110308029 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 868703929 1250 868702679 868702691
    0x90f11160f1b060801090e2806110d0e0714010c0818102604030504060c080d0c02070503100c050706110903011409161203083d06050702030c0f04 64
    0xa1042e0800c5806405150358000d0701c1e51610300c003203080e2100b00c580045203801966180034041d100c04812161220501c840111028190074160018840c020920310880300004000074204081d400036a81d4510600c103c0ea800d41d40d626446801c1c00c0789100290014070b00401e900301040021000d014070300190345041640c6544000001c18050004241c44080b035032002071503c02c54400c00003401001e005156480b12842e15a030002c0c200d100c0ca029500138011100d4190007400401000e55552001c1e42104220b0010003082c060f603078800c584030f5188244107024100480d1141d50140f0700c100002611140c1c14070725560b85034006807000e40c0d6050a4034100340b25152203035409001d071406100750300400b10a6410500d50707040c00c101110b403d00311121b00d004410047d5a000c00343d2805541c0c0c1502e0000c2290721f643c002e20b013116145001e8098441190380382c0d0400b0003452031207249218058003030160000e0f6601400d0320035008824001e54180c00150980b80141080f02c0c0340c211a40c8010800101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 868705035 1106 868703929 868703963
    0x712081513020d0204050306010806010f060216060c1130010908030f0411030f01060f050d230c0a0305070305060c090a030609080f04090f11160f 64
    0x9140d00050703401e011940f50f8141d84c068000207043d80e125594030b203001a075030b01c400c0c0582040e182d0a80c0d000a030490001882d2160f07940d44407880300a6918000c019188081c03008026030f214500740c0009243d40e611681040070980451501d07031070585031003645d105509542c031580c2085a1400d650840810098425280d0044001d16100d9407035840d8640529411581c52500d900351090b042540e016500c1034124009580045002000c400c1c0d0751300030000d49504020005c0d01244070102482e41500c06801b401c1110034003001100c85a080b81d84c085142101d01d94415116a00070140030700400c1001d0010700e401401c42c00403541004c40560000e600c85040d032100420040d42c0b404440100032443c010340701040310a8002c0c9841d5075a410824011380640720340c0464051401200020140c40d49090780c040c0c030001181a8080d9091ba41d03440c2100416175810b441803d4108681c000d = true := by decide +kernel

theorem cover : BRFrame.Cov 868525179 868705035 := by
  have h0 := BRFrame.cov_init 868525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 868525179 ≤ n) (h2 : n < 868705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
