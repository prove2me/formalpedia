-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4430
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:35:16.206641+00:00
-- url     : https://prove2.me/submissions/d965fa88-4baf-4380-af21-f6fcd9600975

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 796582733 ≤ n < 796762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 796583983 1250 796582733 796582747
    0x702060a02100605060309030702150c151801020a0210020c03040f06030911060a0c031d060a050403120528030b1f0914010221070818131a15040906030602 68
    0x11003603e525038415485000180f04007c40800003008031000325034100d402920a180b00105461300340140090740c102e07071203034150110001041d001598028200c0d0800e02004001e54140e041c01c0c1d02c2540d42600043c0c0005121010081c000c3c0c015004429690041da800c1a446c0c42c0d00311003405082e4450340c006903d07108140c003032082501c403400d210003040c1d48040c83c110001202038000010303180014200610300e10820010300210b40c40031000c08004210301da8030300c4541e070001d04a4000c1d000a80b003001025541d045602d001d1400c42d525296100c040a007840c824992411001e194665003a0074162502c1c40746251f50b4911040d20702c0d03444002045103083e110030000414440980e0004031030311400c007229124507030700054140f4004000c10030800980c1407140b40d407101c41c060385000924022010617002600907066001e60303110107056802c88528420200964203440444d0402c1030140c10408880d444c40c24400a214400c0c0710040c00c840c60503a40e110755070308031549a481960301540c04a089 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 796585233 1250 796583983 796584013
    0x17070c0e24011d0f0a030f06021c091e0501020c070f090c090506030402060f070f0506070809031306050a02070b0f12060d0825060c0e0109060908210702060a02 70
    0x91181c84800307282500c0240b0640360070f01456201511001d10503007041000744070301d9490402403805164000a0241d9140f02480c0c20780294000103114010541d504604001440e503d03c03641d41c51903002b6401c030301400301d0303000744000c2e640c0c4102d81611595020000e2200307102c02001528018200d14842e020011f1a1040b0602104d054480c02c03000c104030303034100b0800d50741c8072016260480e030100c6801e0358840090003c0301e407620640c2401040b5031090358a01042c400003003034840c8201210b484240039940d40450083d164810264072941e5801d0a043c14000c56200e0806040d500b640b900403914541e84400c44410303a5007081c18030483c0d402001030354070b41d06405958602c3c1c0000c000e99800c42c82c2041c5c2c0d6541c25030b500031121001d40c20410301c4607131160082c55132416190f9503008130b420400d500b401c5c00c00415070a50021403501141c9100e80c00100e85120301c0c0d1244c1280d0100c8003501001030030005060354041c99045215a5170800e00c42d10340980d994100511f50300c0d4683e001402e0981d07044401e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 796586483 1250 796585233 796585291
    0x210080f010618091a03060106080609060d05030a031d10020c0c0907021c030f0f150e0601050409150305010e160609030309060c020118080a1b0317070c0e 68
    0x1c81400c000f001c002c90108034000701005426654102d1000c40d4038600346000c030044c62810302040e0f41c1072040d80000541c0d690090b01c86800b9000079101ca0740c0594610782402550185014001c1c00342c0d10400c071070b841c41e520a0340a24400920304190030784091100f83d5480c50245d10000b80207440754001020510560b040000b00380b0070300c4c25034848415207071102e0f01a403240318145141c0442d0070a508044003041c805e03400118481504001003180f161642103020060042600303d14000c078040c9008113190f9138555501e80303e03010596130309103080c1c100000b0034054100c02d50003001d8401c45c148040300090003806002c5600c1ca0201c002c0501140c0741c0c540c1c40704100c142d801102800b1220382e090020075801460b0805071103607030400000380c02d05480100c6228a14091007201e1108425010400900220345c0d070101034010b104055030a10306510700310340108a817000074058170302d08407084090300c2400003400d8014050a04d00340209e58a0304c3c83c600c5401c00300c0d250008111114800c00c001301c9501d00d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 796587733 1250 796586483 796586489
    0xd12030f29010c0501060e0c1b0a24060506070f0317010b0d0b210d0306320616051c0302210c09040e0304050103110a08071b0210080f01 60
    0x4024210207600300c0c59501500c0070000c450303041007481c3e5601401c0c00800d41064000344000b00d8a000107241c010388801540d0800b942d01c03115a40e0280d088074040000081c082d003055005203400388031403995240c5040d444a841400300c2c0130382c0c59410010300707035031002c0c042c09081380601c0717440000112500d002064100c40d03146440030580042d0050085050200941c0e103040d540e00310014540754000c2c0011505031026003d020b4804025048250102e00440c00c032002d80b4040d10140078403502c8030f074040241000240103a60311090300130001850040010010000800500542d01c0c040019108a5200400d0102070b5503560100b02400b030500d94100101c890075840389011401c180070301ca02c04600026101d000319481900501244007184101c0c00c44100800013002001030040642c00b080e01c98010784200c50101c1d1400030348101600c00101203642142142e540c1c041e0a03a42c0703800640c2c0e24480d15a482e100c10304105052030050300c0fa0340445a03400f409485503001440c00d58031840410704160 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 796588983 1250 796587733 796587761
    0x1b1902100801080604021309022e05210705130f0f0509040b070f11010c17070c05120304110d0336030311010e0102041814040314090d12030f 62
    0x403c1400d0010139181d400c10750444040600300320b02c4005c403014110390400a940041800e41b061899403900c04031241140d0000e8102d8010081e075101030341c040c005c0100c00b0b414400301184012003d44a800034680c040b500e0705209040c007260042414110507907410a4031070381c00d0f49d8403d0009601403400d4000070f107021038a08038249002c1d9580801c95401805640500c02000ca000022a00075060600302c0400d00740201720720712040ca00240040c0c25040346120366411040807908440c814149507502d0754110300100002c076842881340301141e00080c015075104010900c1d0060f180d55060f481c0c1c1929019580300288244000c0c0700c20118407078183c044076021031401c0c480c43d0a01c407076046d440840e501030510b20507102075408031a025254088210301c495100240100749800c141009604201619808004a86004214214600d801d030b0703020340814000600070300507003114070007015003120141c080000c0041f103544403820058021880c2010a44410031050309000520403002841c00d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 796590233 1250 796588983 796588997
    0x307060e120f0706060e09100b0d050706051b0a0606030b07030504052d0109060606110d09050607080714060a111c09470702060a021b190210 62
    0x1c40300d40c1244035894800050399000314542050040941c02070006003001860280145081154281c4948142d0003461990349008464a01d40c205209204283c81c2d00c00000c11314036050a070180d500e42c2048034981d8601406001604c6508820b02425a88038070905002c28580d00718682200003800091078442014a040104000700300d00040f46000501034803244a43c400381e101d40006010b01803580410307158286500d100810220351310407001c0b9903a541d01c200c0c484428100594440c1010511440019000300044c4902d02c0d1040040c01503034480c0d00c0303451600c4015941c20038140b030f0411800b11107402100400c514007500780195240030000c41c0a10b0b01c3c00c01d60040700303500015189011030111f9540d140c3d64040002003034240002c00c1c59010507980051145100e2a45042c8051514001103641440301034a144060a61400340c0b0143d0090f00255a170800182c0003904900c0c50920b0a01083c038100741145802d011040546c091520360811110044c01808146210f0b02440340403c218 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 796591483 1250 796590233 796590253
    0x603061207060804201e01051b0c04060501020d0806091003020d150b06040b030a180c0e1b09030a14071a030a1103040b0109180602030f0a0614100302030c040b03090307060e 76
    0xc0c0301446d81c0301d030602c0c4c59101e2201061100484503030140780100000e4008508025130360b80d50000f0380001003035084a06100301502c85004a0716207040d552143c0c041200c8070041000b03454000c80059218910386110800c955a83e00028442c03c80c400041d00c50b50030302d0303c480c0c604c010035000e010810f0354280c4445107080d1600711500050711000f080284590ba55649400303146a8074003c1c2845107410030f0b0815421511002650b0840c0002c0e504100032280000e000300d4000c1d210350aa800701c00c001030181c104810366480c0c0001950f04405128640c0c01843c201041c8240540740040042901c001c0c4e00303417a440c0c46641002103843d20b02c427118116005208000c0054400103055054500083d00481c1032000708030822600d40510710300030304250020081005007040820b0591280c0038102c000e00609940d605071341001641416010f4002c40140194030440c2d020350020343d0085280a00f05142595645010010303402c19a09900240c00008880c000c5c40100d004481c031500c5800090074140003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 796592733 1250 796591483 796591489
    0x1b081803060717090a050f030c15040b06010e0f040204140a0f141201060e010b0306210d05070201052512030213031e060627050103050309060306120706080420 70
    0x3d980da01121540070312a00140007000d051100030005507000017103811000500303840f2a165008900308005501c00e90105100b890384050000c1e016540051075252681c0315100111481002010881d03001207846039094a00c1d01d5030720041c4010441b5480c5036000c4401c90080142d0b80d400c40d80010000341c66814140508100502c0400140707104545510410405030b968a0142800381e000d00c0d4003d0110b80009801d1000c4c0c0c000394400c1c1d408540c0951a1008410140505508094820341070741c4400c540c0181c2600400040410a005041083c2808280b050b5890101e8810185490406030b00c81c100c42041803145922030410058102507007030412050741c000c0c0c002a9840064281c0002c42446266419199007120070039400080520030a5120041d25200e0102c0c60480040414813104402044109200e41c505070303680078000d9490701e03060030700b04107039900701502c2c5550005015144030701703850003005000001c204c1c0c0d4035168083d15140c10404026100c101108051120b02e14002919503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 796593983 1250 796592733 796592747
    0x6020a020c01112808030108010c200616050c07090e1e0d1803061b0f030b01050409090606051e01090e0121080d0c0309140111191b0818030607 63
    0xc1d0800c16001261229145a0fa5240c420f004040d0885c0b60000000c5250744040d04400001c075405c0d110380300c5006824106000d03074020641c00f040f041d0080f0012500305400c001c0d40007010040d92071b040342800c1c02c070741500e030406c181d5500000d8190b03503a00c1031503003044c014044030350050701200c8510407400006030356071b0300c0d001203010034801c02646003000d444609641d03001002031600b001e800c2003000080c0300702c00707440d030001d52002d404a007803407c0d88401b0b00d10900074070381107420683d42c541c01d0510700890040601000001150519150034001c1a070b5105c10186c0703541811200f080c0380100c0040c1c000944000032541200c0045406130340140070400d01c2c25a0103540506d4000040e0080c48142803414190188081c0f1000140c00c02c08507a5007540c2c9034001e0400580030700311400388000010400d03400c84042903000701e503850041c031034060b00d86413840e0800c0b052907050071310107042e2004640400301b020480008642c00000491005c035046403440d484d00c00c80c041580100b0f10b40c20000805003685c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 796595233 1250 796593983 796594003
    0xb0a030f03020109140c150f0d050c220f080703030503010e07090305012414030c120708010213180506151b070b1c020306010c020d02011b06020a020c0111 68
    0x100c4405811404051007580300d4076250350004c00031184040044141521141e2040e84103219001503240480f0720040e41c1c0132918001c07401c0740780f94517054102c000d00700a40002001407200d02000e20105116a0310240140c08004c0c2c008a15802c04c1c0c02d01210750300c1c1c202c2ca07401180302c2c5d40c4450000c0c00020381080c01c070390540300c201d0100c0b0840c0d666550111000f9045808c001d10550900ca004072121102c500a00004051054058400c68a410071104c00d84200c0c0e00850389a48016004542c0c0e0070050025840014182d043d100c0c1291034030300980c20380e407003800b1104400c0320214081029482da00b0301900e143c1c442120034070007070800344000364140c0f08660032b062a5a1000803061a130101d07130b03d00098005c000c40240c0d10141c0c3d071064010a50b070844105002c032400414040740c40c100c250310071a4442d41050710b94104116030343c0c0038030850315110030040b410311000903e28920f48010503404101a8414400503981e4070701000000d0501c3d84404185040c8440705550300c003d610046501300342 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 796596483 1250 796595233 796595243
    0x21080a0c060b15091201200f040f1202040c0318030e0612010e06040c090807090f020f0c010b121b19050603040b0a110403030c1202070f06051c0b0a03 66
    0x2014101d04000005181c44440d20b50b019400c80081c140c0d0712860b5004e0701d030521040700d00000b125001c400c8035003611000c6000ca00000c5800300d0b42c410b544024000b03070204403a80c01e01981000e84520000000341c41903001204003000c0503501d001189001e0240d18801c035103c0ca4240301110300400c02052000103028010180318151802082c0d50702c0740c005984040b41080030640195030744807004034202200341d607080d0143d070608520f03402850260010100321514113000b4182c03245494403800007410701e40c69006191340c08010341074650020318098400c0d90345080002034030b0304a883c100007402c002c5d0b14401095030001d24800345035540e044400381110f031069420441c0f000d0040c1901207100800d4020075070058001c002e2000380034160103081c0c8618100c0034100400c031b458200c034164900031380c44000c0001d001c5c07600741000522442216480f2405d00e004841c4100e4071100b0742545580c00d03030003220001e100841c2c89080311760a0030301d1855603107065108103d440340c4500892042986800f000d08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 796597733 1250 796596483 796596497
    0xf07031a0114090303130f05030106030b0c070c09060803120919060f0905030a1d0603040803040201030b03010b031c030501050f0a051e0406030807111e120a02100201050121080a 78
    0xb41055030300c007118222680202682d0b41c0e2415440a162034540501802240b82c6041c1c1c3c0100721824144030341002d49070400c480748401d13a1004200e14071613002c00070440e0b0810f84510300281c1070003940989409494500082e41d10b41200f0f41d000503404500034640c83c010350002007004079203c502110b03218a560055004070341d100d0034080a402034000100014014413001030010501a84110810b01c040a9211910b010b402c480d420000702e400180d0300a400a0003c00104d070056029134400d8400314006400070038868403d50002e8205030400e288904242c00e055422080c03190301d84a40380c050003049880b400c0c0040c0d4035000c60080c9842c1d005050140d0900d404690381e084107061003603854000100240581500e0346000455034001c804203e03401c5401800c0b0a0303c07860030028001d6a80c00b81d00110b4025840d110400c80e14907154410480e81d8001c04100c0409600c0e01210f100c00c801442d00003248035450030100c1d15201e10705003e0030780303011641d5407220006060b4104035440d1021a2034101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 796598983 1250 796597733 796597757
    0xa140c090103020408031803070b1e07050a2406051215100f0303031b080403080c030709081204031a04241119140c060a0207140708060f07031a01 64
    0xb80081c0b01355081141e980c0b10205003000c11103400306c00508401e2013501680d001590703403141100b00380100814034040b03000340000116000340010240080354096001c5401140203034441d51640307542c2500e00400c50984035010346156050b402248020402969480783c403200c0d924003941c1307a0701c88941c92045c82c06584080f0340111903c4050741c1c09049141601c100b5181d8a01e4060700030582d500820340301022030f400c1c0b001c10a01407002c0c903200d1905516060340950380c3c0d421804269000800e03882c01d105800e0000700d0041c0341080f030120102891038040340c0c0c890560038440c03446100d004031044001000d008000001c0d08034181c0a0784440c1c0b113441c13420b0411021080c2070203001d4066900c1c00f001008500c0c04502c180106c0c00e41040c074110b458150407603001d61030441c95849a5910b4110b42c1c2d000c48017241041d2010303802484414050a0701423880001d100016091000d0b41d40006200d9010000340070311680b1181f0155046105410100007580500300022801c000310b1001034140650354080c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 796600233 1250 796598983 796598987
    0xa08062a0d051306270f081308030c0105010b16031107090212060328030809070312020d030b010203093a0b0f090a0209060909120f040f0f050f130e0105040c08060a140c0901 76
    0xd10980e0910710f1600d48c0807174450584aa403900956003042903507085c1400013503100c1f640c0c001c807507800e10a80076240d03042d001a2015a43c400e405944500c00713200300800010404118405021105081115580c00d070a010b000c06181954a450403401c0720414208680e00c000542c203900c3e80e442d03150515074000d03038030458400e0038072120f9440603000e07e100b20003c2e030b4030b140d01140c543d0002409403010803141d044d8400490b602d015405445402000180340f83c204501c04506075070340c1c2100a2440c00d200d0030010a6008400f1031303500210785101d80d01003071140d501200c82c10b041e4800908001450462696000502080c4000d80260701888403000451603500c414401602d03c0d90340010b07095951150100d00002982c001c0c45081e005100d4610049001c00c07042180c0411204001c1880f03407608005003c210841200c0b081c05402d4036034607444000c0300c12083c0030703191185006120404055180400725400e280e00107010340d03c2645081510040407800035031395508004160000703612402c2038001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 796601483 1250 796600233 796600237
    0x901031b0f1419030507172719030504050108130c0b0912010504200117070e01020a1a220c090e0a0516050a08062a0d051306270f08 58
    0x443c0d1407042c0c481c0034030382c510b400d038102c5402501250b55800c009030801e03000c200540019100e000c0849496206007000c44201889540c4800741c402c182e8032a0101d181000102c00b0001d2821004924042001c20003507070440205a4005c42d00d0030201e2010040d65070f60014a20940129103074418086941034980d11400c02a075074912045008001c01d0178a03041c40d145210000842c90340d81f28400c003000c40e0552290042c040c9901c2948012007141d224000107640c0400080380150442c454030300d040d004920507003104e0b4200c2031090000949401c049039a4070036826201c402c00c0803c11701c4912000000c04a004180c221400e0b0107001039003903004165542040392440000c1d01900c00e1800d040002e04a44140c0350485204a40b81108250f23641003254a13180219036006d408410720807000f8100241094941f01c090554a00e00d142280c11400c4004540d0f003990540d50403103546200c601007110610840c4107a034194001b803110001c408580304141203601c44001c080a4021280d04100520702c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 796602733 1250 796601483 796601497
    0x80601051504080a140d0c0201020c040f09080a03020d0501090605033d05060901090903080424020a120b151c020d090f0b250c020d05010e030901031b0f14 68
    0x1d6441500306401c0852040050300c22030480741c0600f8646c05040da000304007080341030741d042e000742030004001c004210050004000031006070f41c48140703840005003c4001002828140d03100180c03904100c0d01c0000440d034058210810b4640313010014019079a0011f040c1c1542890140546842444908019024410410f1403102c0318085c0040c4a04680550090b0388544c0b401e039106445a0b90f92088802910307000d80c0d014000c50240000308011a000101c02c0011640081207412a1408058110101d0b8080d040c10700014210459440324010075000740300f20100100c0d20b42251044139042e18031203101d41404480d114180c031021400c1494a5015034812204408041044801a04052a08182005c000c81340c1401c01c00004d40100410094441e002041c5000b0280e10350040109032030541030840241d90240a100c03140300050310900441c2450040cdc24007841e1374003440d10025094910020a02800103c0383c07482c0c001305035005149850002480c60024952000740302d1107492807044407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 796603983 1250 796602733 796602749
    0xe0904061407091e0f0b0d090803040c050f1801170703050109080c0d0810030204020304080c0f0d0e0102070b0307300603030e0f031b01200d08010807080601051504 72
    0x1804008456810002e050220358460341415114905540c2e000310000380c40c094105c1c905850002800b030404038502070000300120383c00000d04540d854850300d400b03810494013110400020301040c0481d007040c0150040d00030040c0d40c619141003811102c044882414040c1c00e141c01515070505041d6131007000f0700c07001560050001c2001c40001d042c000c409d0b43c81a00512158805e20410380703a21071152854500c20078011082018083c1150300b04006507001610959500f001844800d40c8010140024048070400000800065040f6040034054040701000d4506541140104000c40c550440480c0d07444600303864002e80c0e030f030b50000f0401220420800011000c00c40c0003100403450a26500c40c90650780203449588824200908024002c0d002112054064220b40248a901c2500d040700ca1700c03c0605042401c0c3c0341441841c84407071005000a04240b81d0b100400a2242d030f5003012460303015020b030501402c03d0908000c04603543d2901845817901401448007040e5440e64502c0643e00584108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 796605233 1250 796603983 796604021
    0x50f06131835180907021906020403140a050c010302090a05090402150708041e0b12070318030507170c12070812090c040c020c010f0e1903030f020f06070e090406 71
    0x1c0e488020305a080107000f1020b82a00c00780815a514003c40303c603104107100d500400602448040003d5091900101102c0c0e094082c80048001072031581d108801d0451500203242005090418625210aa16045050610400c84606d0603100e40701c0b441c0903034100381d4620803143c0b20f520103c1e40003140444070400706000446c141041051820007031045501c925291510031f40084910702490445220345241500200010956542d0f01c1062035404040c0e410001030304109100710443e080131042c01200054170004502c0d0030003000d41d40498040602c5026281450b5007000c405030b079003004815040c040200842da000c10811f5403002c4410a0b4038800c01080c2504245000d55503c005203000c10707118074280000d02031800d03c00a181c140102c0140d5504c42040d01086098904500401c42160046203608007001003101600c0d088005500c29600c0c00b042c1c1082c418020304100b4801c54603500d9030803201c10700c8119644007002401400040321181010b45491810704020a00d80691004241c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 796606483 1250 796605233 796605323
    0x705010c0504081b2803050706021011030c0a052503030501060206310212031207090806070e040b010c0f080a090902130902070c09050f061318 63
    0x4050003034002c8403100c01c1195004411001803500c0801010704054000e544000d200172a034801c5803040f03801e007800b41d034110360503526030b103456040000c180c2106025900000403400700032502d1241a0798018000c80040c21030a00c41c000d0710f4140303d81c5c03081008101000c910000c0280c40600120600860080300c18090503542c030340580034090901c92240580207107000645104201003410040c2805051084501032842a11a040310a44c40782641c01c00798400d07155440c40c404100030302208142d120748010702d19140200515000150f00081c030144c10036001e001c4c0050300008102c80818003154046403814403100122541c940590f00070b80000e10844c604828415160001c0070400c02c43c0c0d03525400243c44004240517442058165400e0100502d8100104030096020704021442101000b41403a605c44000041c3c0d40c0a0311100005d000c0d140a00c01c0d02d143c0a061805458088141881282d802644080e00c0c400c488a01500501c000c1400d440000050550910001e2100c0704e00064112 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 796607733 1250 796606483 796606487
    0x100609050f0f04030c020910090609060f0617060603220b04031101060e010506090a0b0a0f0210060303050318100608060906092826090102070902090114030603030705010c 75
    0x801525058107a694550120756407a901ca10b00038800c40c1c140e261000e0f000c1280e824040640002045140d02610444002c44d42d51000e0080300d0041071008000314019007420441c0040c50003580c0034405101003540000045001c000c0750540c01513046403403170348030754a0883d035141c008443d65031115002041c10481d010040c1208005024a001c0e40e900404902d18601807403ca8800c2d000c0c507202d41c207000f0010411440e2200041c041000c015016060496a42402c1c51040d0002c045400c0458030250043e440c0742d9040020340948407400c40140982480c60318041d0440c0702c040d0440e40400414504082c0c1c0c0c140c204030328407038208120707001c11440740e0b141e502d540c03030746001d969200450103000007050700d002c400590000c2883c20456101d4000e00c817540b07049843c803c141c00c125800440c41c40c403046420401710202100342c00042001c0d5440000c07000090420b07030341d600141050f510600c49200701c0d986c014003194610000219a80d543c0d25084000380ca14040c01038001c01540c00e12810b010781503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 796608983 1250 796607733 796607741
    0x110609014e06050a05030307020d080708030108210708030703020703090305060118061a0306010804050f010c050318072412050a020915160803070c0b040516061103120702100609 78
    0x1c19414420042c007a2076500b00402481c55100b07913036040c1c0c07080c0051005840e00c800d01c101c08034440c0740028034040117550344d25510f03002603200990a0300101803035002e4004600324100c60121242110303140c441c0a0b40c3d0640e0501010f803464041560216000d010103000d4440d41d0007542d08134044944540c1d43e420380c1d00a224282d10110b01450900340b0000d151020054101c000820307201e03400d400c658a000c01140d100500400603a503a21502075070751204102031160b40c030074041d80d82d1001c1d0303a4070b042140c440c031000f02e07080442c81c0c640c4240740810003144034600824000c01d40801c8104106003a40d801c071050b55402e29400b03210343ca00400c0c420795002c254010008404182c0d03e103c2d0007820044900b40308c1c0240050524240300400a110009095000555014100b400e02d14104003080c1c961404908084804030b4150380010165000e008401c201c01c8000c1043e85449075044c2841c142242e141d00541d20400e080141c032402084d2400d00a000740c0b1400750b0003e800f00324065030b803400d1102030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 796610233 1250 796608983 796609127
    0xb0a05190510080c031c0e01050d05090714010e0a0302270c04092007080d110c010b090a0b1f02070806070c0201030b090421050408010c030911060901 66
    0x1d11a0076074807400c505005c6003c110f00b10b00003042d441146a880c40c26198010340801f880e0400c8000c00402400b895a031044a02510080d0024032000341460646001110840070303183c140118400f030018603558031100203007603a82c151034022106034402010f400c140f2040c0c03210000748288030100a0341c10820000b520071034807201001d001c0d04000918111464040d840401c0390000104081000300d90a2070040c0848000c0d1a00000c0700c480301c2d00840c03182e400030054400c01c2d94480f41c0750b1425240c100c21050300410010300820541c82c0060001305031034070003034038000100c0c24600552007031b178024002c007401441c1d0041583e4843c9440388005089050410b0708a000c80e24250f00c0444030f040542c0198801c550050b01100d541621212240300c0c0a510401441042020040468072150038025014814a81e482c00b08020845207005071100c122501c0180c003882040c0079003449a0b0b409202c2c030039001ca85c030201090602c89402c00203041901c950001d800c150f1303c8012001111b40005d030400316 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 796611483 1250 796610233 796610249
    0x102090d0b040c0b130e07050f16020a23040f0e0d12060e011401030e10020f04081b0d021e032d0a03020705100909050c03010302010f08040b0a05190510 67
    0x110f6500d510402203180926009407041c854a40024481001d00d030402c076400112a040290506507180e1352410703180d000380801503054034a100e0410460800f206880c0140c41e2803e403032086100050308400c00303114051a2107100361344034030100710307208029071113108941c030300d01e042e20795120348110301030304440340b440c490f503031003440c1440c0022a403089171100b81c1641c80030004568207081840c0110050074000c1011419401780315240905882240300a00e5241500b0281c151100d140804d268141010054010070000c4005000940e40e0b03100c10350301450301d904488809954003613100209814404078030391030700f5105201042d00c0341041c00101107206511041c1c40016604e0a002840c0ca895501c2802030269000c403805000503d011081410040030b01e142c804041035607070158009943d01569550300c0080004018400e551b81720784202c0c1008844d0a002d44070f82480c0d40c1d41024000018511543c56503a040070412401103e2400c0c0202405220113100c0d41c14203c2c1c0010184020b8420184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 796612733 1250 796611483 796611503
    0x80d110c0114041b051f180611070506041203030e0709050a02070c0501020c030a060c0e0415090c020312040b1302040e010f0501140303070b070c15060303021203010b19020102090d0b04 81
    0x4c6503a060780d095100751000034041c4070310040308001303100c0e100700182c295909000314603088514091240d48000f0042046070b4a5002c803100d10f00609080400300d0304998011001080705101410408131900d08059252030009030280b00c01145508154007074100c1d6041605140c14044c0d150426000360100368004c2e400304401a0f628001a65510100300295030181c21910700e0703a01090050703004001d0441c060419000c62500b2400240c00c4668840d014001c0c0741e1416030078007034801d81d803003034070202c0c0b60600041d80b0341003982c1a410b15000f00104006c05242c07030240000d0b5080f000314503c84505a014005201c035160241c0241e010701980000601a5442c020000441d01d800b40004180c0007000f9010314039004032a1650058404010a01018017246d03045580000b00b2000410001c0303078080c840043c5181c11803170000d003407401e59007504407080f100748014000990050300700c820280406036903500001c0302e41c1d000d0340a40181410a688a16100035080510403030131080ca200d54032a2820305 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 796613983 1250 796612733 796612763
    0x12090a02010e04050f0406050a06090905060108060702031e1c110c06160f11010603141506010503150f0a030213020406021207111e030a061406030a080d110c011404 72
    0xf0084404c12185c2900b1034521320049400b0504691100360049655580131070702c0ca031540d00b0361060300c00b0014101c0789a41304100401c41501e003130040d80e030000034070720242d460003500350100c405090525000c2c40c410302000803011649c0c900030651a00030706000c401031044030301310310503002190046e1030304803481d01502000400740a0800030380d400320310711601c0b10041c10241540803640c100392840624090740d80c1d000d012020803406a09a50384400000050001491242850304400d20143c05141400800d0040c42114010b20856882c2404152040301d000300780040010140c003070f03079440a5000b40141d07500d0007980a050300144141e4002c2c0d02140c17092824100206000e01c0740c0e00c000350840d000d05031060001c0c0351104089030250f0103145252000240940000c0c00c08400d1a411038441d0303030391282882084103500f111580080103c01a100e20700107034940341c1d61440f440a40e1342a5903918401107a08441c00001c2d00e1965858100810000b11050748040d44900c095806840101c5981c80039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 796615233 1250 796613983 796613989
    0x7060909140c16060b0904050f0d0e0d0222050709080106050306040809060a02120f0a1407020d0305030a0f060b0307230d02030402060906070c060908010c050f0f12090a02010e 77
    0x64066400c44002d58905a5003000616249940040071110240c64001c4046607507030707040416005501174070180101c44180d02c402442c1c8a80750103414284000355200c140d66983e03203801000d03042e40589040742d00311503010074201186070100300c00b01c04ca0b1910081c81001d690041b03a00b410743e0b4208000704000380d01c42041666940d01107800a006010811006d4040c0c101319014107a0403d1500448024001c00d0341d035006a0b030070171220000c030010081217451079a03074884c1d81c242d8080000c203805890102142c0128400b007003c004060240900000462080f40d031560140b0182c01c3d101e0402c209040d116030200109910503155500041d01036484c29040c21003003540210a90711041096240022110000020390001401030b648524107000365402c644510000f015554841c10784c24280710309100300584250581c0e00032003400da14103080700803800d070448110381c0c10b2101402482d4540301c0100d10f880f4944a0a00c04e440803c000e2000e01c1a900c000140d45a031842c400d88414000c0c10b011014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 796616483 1250 796615233 796615271
    0x1406040620030402041a03250501090e0604052502240c120402040b0d0b10080609210403020a081c021504060b011116080118020f010f0c0507060909 65
    0x101c015950000c0011030700514250348614070007401182d10701c90300780e4107000107400c0c42140c121520090310320130321401c504da0680300b1080c0075150909003a000c80d428140d480800320700050415000b00c0e074510205524210340a5046000b00e50901c48031503014120340025160030004162b101607201f003024858046500710f0303043e44143c0d070000045040160760750481484400160087e030300103030360700d581000e0341d00c4461034500326500401e641c1065090030460645403ca450388941126080343c814000082004605044d490309640800c40740080c0400301402d081c403460740020340c0000204800502140c0200d030008141461001d84056642d41c950305030380340c040700010400a00c80d0040007800288a55201b516105d006140c23480c046507a003181c03285001e00c1e5808100c4256000c110400045000b400f540ba080021b00e03070b0030b041d6400309a002c6400d24210465403810303c00070550041d841445501c82c80035494115003111090b60340d0f01c6004d00080220700400c80000d0030720428171418051011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 796617733 1250 796616483 796616531
    0x8010f0c1101140601050a052703161406181c0c0f0e010e0a0e0706050405130e1506031203070c0b0601051218150114040e070602070b130314060406 65
    0x141102c82da541310001100c0940c00300d101c41c02400000d0001c0c1e140c1d00144202a50411642a0081e086d546590101480c00f210b030080a085010500c4c8144001d4503808503c0c180d18209175081d54441820300030b0540c0c075031030740070000e42c11800b0428661031342d000c040c0b0104001d60081c81450741c041d4031504500c1d42d140b21405a800c81ca404000101f19410143c0f0003194480c1c070f44080003c060103c41941414461650f0010000613008036062015250058040c05003450b08882000b103186078601c41a19040141000038201c401d0100041c882e441c2481003141c220502e5041030f0752071900d823001415459803400e0544405d420030000417481d50081c1c0840790400d101c441282615903030119840c1041c0440703030791101103006400708a43c1740341a44401c2c0e8080e040f4006030304d00140f801c409000c2100d000d441400990340c440582084896008903d52003514000641c0a6850311610f42201c4421295400200400104d81c8000c200c100042070007030049104020901040c61072030728451721030800403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 796618983 1250 796617733 796617761
    0xa050105150703050a090308070c030b06030708100207051615030c030c02190203030405040c050c2503060c0504050a090515031c0e13020408071706130303051008010f0c1101 76
    0x100790b2001c070340203034041c151020707140c584800f5a41d160341c4d9284440e0030010303040b070321250590b00500800141a509070741c0860140e0081c0302e020724105040c0e45c2c0e14980e44050807600d50000e0b0440501106001c4801c544040b41d0851380219074506080e441c600c051459500064607081291041c0c5100e4016690b008103540e00401400c101010b61141c0520044022603041c481044006011340315406460755401094407442d807030b021200542130520b205035100c1514207039401042d083c100e200e0714070a4103898010a00090300e01c1c01e0b00303080d80e0314401c0350010303a800005480c0c00109400700380c000c1ca10a001104010802c9021801816901e4034041f94034008000c001483c0803031300307105000600712810014a865055400b00c030707039034040707a206411121950f0804030050200a0f0900010207912442c28024a020316040840061600c00000000e04154030303480440d040440d949805400780900e03000800984000901450051241e4400b1401007a5002c014441070501849202030042460f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 796620233 1250 796618983 796618987
    0x102040b0c15010b0f030601031b02010e0c10080412210203010312320f07031106090714100201090228051804020d021f0207090609020306010e011b0206030f0a05010515 74
    0x4404000c0086d0801080341c0c2c105603032002c8042540d801c2c4400c80d806030300309400000701480680520350401c00e07040411801840c034000200d40196021003a1507200b03800c03807103004030551030b080d003201d011924104401f40314a0804903a1090b5038241e0007541224801d100b5644071907094101a9045086108030784080405548201c0c8445005103484002425003109280f81c01003480d44480310340c101c010142d000400302c03075a0348880c3c041000b5050300940001e004091280c58408845514010115824020305140b072030a10080d000350050800c0981c010010b007200d0038440c0f80161a080e00704070303019400c20b4203140055181041c001900f000400307854005925038540d001d011511040c02c80072a0040e800011380301c01e80c0c03000c480c3c0346c2550945501400100d440d00004005407284e60308064042e078410000d105450783c2040645200000a080c8100b0f40c0b500f6a40d0a94046103c1d14040d422101c004108485010052500349c420080610b00f0000d91341c0f01c60922882c20f20b8013010201e50502 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 796621483 1250 796620233 796620247
    0x20109140102070f0806041a150f010e0904140606040216060203100e090a20091602160e0412020106060503071404031a0a061e031b080102040b0c15010b 67
    0xa04080d004410310103004480340d8940c0d5605035504150f05510442d0281c00140c144020002c1802104644000c00b400c0d41406041813252440d5100b41000c410744205c1c0460520200d60b40100038403615000b00910242d000d1600b400e01500320f0710810510074060083d000056400d2800d07200740d035030304c2c982c03c03031061100d000c00d5540354003e51010749040241c40304442c0019054544240311441001610082c00303030800103203407100c3c01e140849665500d41d2080244c41c051601d6050300240d0007030104d440034940055500091f400c2001c503808006070410026004202803003035055483c0030b94031512512241e0010600200c4c03c0b00d4150107010000788040000c00c0003130340b141203403c14400d14000c045150580c0c2c2ea80c0c80403550800c1d03803c403400140c860100b00700c045940c400c05005181c0c1d41070341070601d94200a0b01241d6641d9000041003902c8200d8003203060148200d032803016020b00d400031555540c6400700c40c80540c10500521140e84102d03c003000e0b2920380001054100d907641c0354040d0030010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 796622733 1250 796621483 796621499
    0x9012a0c05031f0f020409151a1810110105070c03020705060301080303130507080d0903032d031e09141b0102071a0c0d110d0c0f020103020a200610050d020109 70
    0x1583c444544c0321310317800740700100d034101142c403840c0c01c086140c0b0b0091344036502c1c2220b1548040c0f962008442c07845024007078440e04625075818108100821104422011922141926880402c00c0420542e620344020010007540000304a20401c1c0280c00b01d40c030303841da96010440300344424091070001d9082230003c2401d65007a01103607441d8601c50b42c10344111581b6403941901d03101410800c0340005002c21020030034140c2244042400f40318611440040c0c3d00d02e5071070841d0031459403240604045d41c8175210b000221804050b00150300340d070401070249140e5030500b85440c0b808011185213a00583c03c0b01d41c0c40080007000300304011410f03006440200d142441d0400f00d1465000511032100081102c4411030905000600d41c105407502c54420030350075040602e1900b8044001c000030300c12503140b8500400c1900714607a030000c0d4240390142ea0703161400800c8411301c0b808010442211001c9000714880d0002140741840b6004103813640104035aa0010014a800c1c0c0c800c002e408149410024021070b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 796623983 1250 796622733 796622741
    0x9130e03120c07060f1b030b100513050405090a0b090a050a02090613020a27050603010513150b0705101b030c1413151403010b09012a0c05031f 63
    0x40c0c101d45000d03050000316144d04007518980703451388002d5981d611000e580402c001c0c0d100d90b00c503c0f8034601044031000d041c01080c02d1049007090792041c4040860a180211480c00c10640506000303003013400641402168981d441300312500c120340311041000011407009002070700c0c0c0a041e070004000c060052040c0c007030004043c2c0141015400c00b481c45100039400c6000d0001300f800c40c000741d40700e20b5001c0c0c8040c1c810785180002c601c001441c034079a2608210b02c0e9581e4017540e05642089549290a080725441d0720000c05140e006442c80010882e00000d08030034000c042c0528500490940f4007480213a904d00f0200e440d00c2030400e059603401d40b519415584a44e00ca0011200741d41408844c030341d40c1d1506442c140c0c011107110640c511003420144142291010500b5450101d410003042022203556001001d01050181210300390001c24054540d83c46003aa400ca00205881c01e103419510428940e215080e11b014142c41c02540031000040134240000c2c0420600704a031410f400c43c01c00b90441801030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 796625233 1250 796623983 796623991
    0xf0b010506072f091501021213170f010e0d080c030103031e020c0909070504110c0d1404030b101e0b03071808030c030c0f06310b0103060209130e0312 66
    0x1c0b204581c3c0400301c41d01d404540c18080d55010710040d1215690b0700009141c4038018041480380c880600030f4840140c41c4600640a503050540c01b5940c000c1180121403800041c0c040014032036081c400b401600c0c45010031803a281c100340e80c0c1c4181d995658585841e260380703c280300c000c0015603c00c0f00d94410f41d000b548641c030109190300c15104072994040010380502815110f00c480c03070b004100f04006514083c810001041c0078592128207002c50107040c1500c500c6404817100902444400c3d0503441c22000d81154065948424140e0036400c104064400240d06801003001100405040b000f050341c2001610702122050820949581e03a444412074141d40d45680b160000307811030b0b001007a014401e00107412400c5514008548504518800c1440c0401070812400d4030341110041c800e0074020700c07021859001054203c44c001d0415682c40a008204088020702107030000b00003c0100011398006101281088951000a05508690100300c85070805400c0d002d034001c001100c4000600d13480d082d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 796626483 1250 796625233 796625303
    0x402010f0c02031204080114060306040f0819050406030608010e0d111203092b020a03140405030307060e06150a09050402030703020d06090b070e060d05090102160f0b01050607 77
    0x101c42607503020a1400d44400700300310101502150a11003c0c0c001d100382242040c0f25041c5071150b080c0700707000c20349529001e8009040f01c2d1111403a0020300059108950000258a0f1050340400000100a100da003282c042c2c0000241000c000042d09041406800480302100000c4d1508100c4160281c81890a1300502507160069401024440400c00007441c82040c022015011007170503100e084004681c0c25015a0028050001404806a0025468852542c9030408443d0840e42141c40740c1940610b6201c142d141c88002138160401225400840e10500054100d50107900d540001152000026940c41e8102d00012420014500c094009603005070015084d04e04080c0c0701c4d000b103642030003075101c144d89035502c0d0005101003181c049a2180e100c003a52800c42203084140d0009009441080c810409003922540072882102080d4100c0308030100325a06940354040c1c030703e4104546a004442030b41e0207444c00d00000b8181c140030003240e0045501c003450204001c1d11215401640c9440640c00c6a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 796627733 1250 796626483 796626497
    0x70c0807090e1e010f0227040905060a051314100e0721020f060403080310050603010b1204170a0c03020c0603010501050406050d06030c0308030a0b0f09130201180e060907030b090402010f 82
    0x4885540384000c00203512421512442009840003106c048004249998060380ca270103d00d101055001c0341e80f40d000312140c24040381a481e550300030f0170094a0340101415005461080bc109020300103440008550003070310500c03a10144070b14151302e030314152041e9002c0d940c0712420740b45105404008c0c01240c61004051140746415140400d103d030f085504110341c2c002c000414000c0103207510260304000c02c0c04031203061035503042225249443c05030303901d0b458014881c940414200140200d5160000792042c200e1500c1d0b0405582c02801c01500301d5041e40980a1508918560b003805011203050714410307103449240614000c000c58081d4032850444080d43d540d0240800010383e85031a500045000c1c860040c0ca81c1400c9501000704c54000304080e114030010136075410750391034100c41198888503c0402c2481684603000588001d0041603004900500c824800b040259400c4901c034000d501c20b5a03030304003507621118160120342c0301595840d030007006440024010340c032a218100f280b4082e45030082e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 796628983 1250 796627733 796627751
    0x30906110708030c0a020a0b03160e04090b150f030a1101200304140a05010c0b0a020a02030426060714031f030206130e0c04030812070c08070c0807090e1e01 69
    0x743c115040085142d00542014403407400758030300030508802400c110800140746003000340328103503141c12150f81c00043c4051014220000e64a581c046121103801507140303410340c0fa2007503017081040c91a412862140d001e407141ea807a40e050000710004205e52081700c01c40e1801000c801590120310001d03010200d00441032036417000820034400741c80200204161842c14201e9401041400c03949508000c1c1080314107884840800c032110002e039003000790708c80010ba4420240108904501c120b4114420409043c540c021003940802d00300000021008241c41c441d440d44041103c044c0c9014a8802e10f04d003080c408201080c011102c0451458650b088081009a40ba03001c186240c001d0b081221b02c0d00b602130300400c90310b20000801540008803001142c6000d0075999400080e01421044e24518021030f40003540c5207024816800310260400c100686030280703850f00314102d075210300070010f00f406108400100c0307043c0307030007115000060f60024103002c0910500043c1e03807010b4400c11000c1592608441 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 796630233 1250 796628983 796628999
    0x40b010f08030a2f070b040626040f1506060804110607080a081509090f1b130f06050409050d0207050105131e050a080c01020f03071a0414030f04031e0309061107 71
    0x1100052440702000e80d2600c1c038040e80501040350807844c0d184540a99020356080c107002c0103429a01592016510710184440d0800340c098a03841d03040d00cd002441c00b0004a04940c1100505106901c00d41304a0300c11000c500601216004100d0020445c030802e108200c0c00340e0080754010390100b21041d420121407440c100141c3c03c42c0040d10401d1254100a80340c40c180b2509110040180c6664403162000b43c0100020562842c88132003507040c20341d40d440726448503050503000680140001001484054418140300e43c031001100c40b004094401e0200008880d405030b010f4522207171031954903103038091a06078039101c1484d4080b04408200915070b004103195441281800282c42d4a200615071041660006441d000700807141915645c01031192000203240502080d4086108010845040d2514901800c0341805000c000b4501c2c040450134014601089000d07008072030241707041454184d00303100c20549407600c0020290018450740300510589008980c50f140742c2010300d0849440540d01c0c104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 796631483 1250 796630233 796630243
    0x5060c010f0612030e09070e01030c030e010501080f0d0e01120c020a0609030302130b03040b1609030c0b090103241406070203030408073618020306040b010f08030a2f 73
    0x3100e8450512020402499840300300020b172800240c80c000906d0510349000782550800b04e90050405890301103140c20148250011303845140c0d150024403841d6122010b039601c5010450400c045031040f14040980360f440703180d41c689280010384601e00c02c950316019000c040c1081c0079003c000c1d88903c003211800a04070380300d001804c501a94006850b844090108040158141e0000ae0384030001d005004c04120020089038014880c24411881000c8c659401c1d20240c5a560000d40500549140080c1d243c05a000500500c40240d0b820420003100741a1032004032925000400d400340300943c240407071040d90444d416101c40090802e8280701c4254002031451b40550000d0101d80c010220400003075104141c061004c910a20300f09240a21880082d180c02041c0c2420305642500c841440c0e40c0d4070401e03802c1440340c0b6005001d50f43c0c1d514050403e090502c9080c41044503040440c4400210b014000c824ac070a030007a071ba650381e105c54035000400d540d40300d10039264140500c82c0052725a00b55508001d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 796632733 1250 796631483 796631489
    0x39031104112205010c031b2603090d051c090303150b07020901141806010c06020a020f101b0e0604051804050f240a1b020703060f1505060c010f06 64
    0x3161030401003040c6100c440d00c010b541c06a07042c041350480d0000081d4201000c1d0040190550b0412501d030764500300a40c0072108c00664190b40402c1000100741041050029803041c803070031084032680c90025904849900c90390000b08a0001e0b02161001080e07007540110603440e019150100d084142c1810030115030b002513206203a900c60000780e503030440c01c214017018010b115480c148807164000300080381903000411a107048107a10000000c0c0c0c56802041d90f81040e0750088000c54a581d22450003960315045181105d203d84909081c2031541c01d6140109498400302c0c1d5145120b00700c40c04c10070303242c0c42d4480400d540e020030107000114150f240e4040c62990080c1303144044940341424102a42040c080550020158104110b500901c5c10360b0800e0031130040750100010199a1115501e4005040b410014500b05c145200b08900c8698001070a4090380d014070310420540c1d01d11100101158100700040c3d40c00804030030204070074a07020010b44a044440b400106151580f200d40c40121500d41d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 796633983 1250 796632733 796632757
    0x8031206060f0c2b090b0a170115091208190504030b270d02070b160615030c0b040305071719060b010f021609020705030705240a0c170a060509043903110411 69
    0x142035283d500da0b00014800084c880d15964950402c240c6e240c4941c0c500c9440090301c0c500c55030500554006100d0411200110342210500306541040000c440f0040e1441064f041d042008980c1c840c941000411010a40703e41500140f0a281c60080407058540003000d00085001c9440c0d00301011554502491002c41d5111000240340703811071600074808291600041c03d014070901003407000520001d041400e5406808403000340c0401d0003211450320702c00100090440c50b105074141c08100150f001070004900903200c1c6210302400390022070391045030341200c04050081680802030b880165008144550090060341c0c0703400155203032585441c0c0010341d440002d0315080c44034503001e0340b034402140c1c100a00300010702134510707001c000500040c1c11425501301d40ca40400031580e0034285da40824002c10001e000081145030608211881c41142c0ca240300502e01c2e285440c03103110460100040e014036103413079460710203411034503842807103601a081c640d0841d40d0f507014a40c505800034041d01a490310b00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 796635233 1250 796633983 796634009
    0x2070311030a0e0118031b03050705010c150908071208060306060406081c2c15190804020a03150506040b030708031206060f0c2b090b0a1701 62
    0x5140080040c4828056050540c1042c460303050426800524411564000d00c2e2010b2141450081c00210748850340c001800071910f041c4044a00b8444180841100e003d00c09030782030030360750704010741e110b030301190000700024110320b804003040d00d144d071145648134001d00310702e03081610300e50b62118003c2c0c4000400002c160100200206440e0402c0b0719603202c0800e4405018051804e41100e80c0c500c0102c0d00200c4186443d104c0c401098071540c40711401241400c580d030768040c8070701c0021117800c1d075113441940601d000c4210700e00012400030480d8040b0440658012a21240c064200d607501c4020303004036401781c42d003180000070840da00d01080e01c190450200195504007030003040308450200c004240240c2003024108068800881550110103c4c10007040640d6030750740020381c1520a11050050320346010230022442040011800c1e166442c40c0d200440c100c031a00301c01c8958a18190000d400640c0602d0b0600100036800050040300302c1504112007400301d80d06013664244401d030050b03119a002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 796636483 1250 796635233 796635247
    0x6300f040b090c151c1505211f0b130c0807020a0c06050714010f0b1504120201050d0b0a15021501080c0d1b030309170d120b0a170102 59
    0x40c01d00401d402007501c0c0700503c0916446408114202103448483c0d0740340750007082802d108049048421301020910204004450403503000d0300803034190b0301034680170304200440300000c001000701c0c401482c3e100c4401008601d207041e4060f4000d07080340035030030308058644072101c1d40358940422110103552072034801314440114250060015000410240442d840305d2202004944004107040a5912514001c0d95817403241c100b82400d1000091307040b90542c605500e00e00105d803207905c8603407002c5d070858602a0040f28401ca444090007540221241c251940200c140158000c2c00105420340d201c120118501514100046048909070300c1494413032070350509040d64a6042c41041003604c0685800b00035075060403009030303a560356244024001e1100121540a0289400c15044a0518120500c80c056200e18000b81000490300c20101020840945400545070205541c03e01490680e110003a0350303105090500a0103c01c842990401a100c1d008104403d4203025001002160000035948840d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 796637733 1250 796636483 796636493
    0xc090203070f030207020a0614070c0305061b040303050306010c020f030609060a23040206070201020a0b090102040f090b240f0703020a0c090b0306181207120311030606300f04 77
    0x2001d0b100c1c00400d44104084030040e038035800c948003950f07140c1c0307040031102215048208803885a048068084960304000000b00100051034034030800c1603881e00100c0e2a441881002c40380203c1c04020081282072001800c80d500c81c01c50403141c24001040411a2900d110100e804d05500b9980300f00241c0002d01000600ca015010324107801440d000309002821000034030b04c2801d00046c100910880c0c3c0054890f041d68400c00c519042c01303400110211139814070307040250007940a482242254420000300140369142031150b54408203001c0d001d86482c1e2010244010302210a50302104002c10a0180b2540c4040e0b020241003500d210341c0003080340100f642000320f00c002003070303000000142c2821030740c0501d910003003202074210130030004004a074010683c10a00700f10400075207401848003c90b140c030500c10103c075400d50a9400e51001c20458031016040520b80c44100d8000340c00032400c00580e50810103002c0c0c100d0368280402d000c080d0095811a12600d4004c05a850300c0d80264141c0c10301007800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 796638983 1250 796637733 796637747
    0x6052a0d02060c130e06150301170709020f030f07140a170a0504020d02090a02071205190e09010b09011707030b090c180f010e0a06081e04050c100c0c09020307 70
    0x498107a80c4c01c200c000254952590b2590144004400c600c030085030703540e12100c03c0c00c3d48812070548101c0d200d6031101c40c1051102c03150303c0501c0c032a106546001030001a944211407007400a402d400345142d03030b548802c0c0561100a0700b00c00070002c901c82e0740f03145982c008000e00500c04050307549144d003a442c0c04030020440b00282880e00b05a1a00c4140001039460a804094140d416103010b160740d616401510002e004803a4007600042070310740e0303071003910b5806002040d000550b84004492a54589030440d2400d14008085030401000001031001d501c82001038481054140341a5011609149800103036040c243c1d85680800d0325030031003600701c0c545140c4042d07000d50003c03181d5040c40010f1b4030318284910910443c6001d001340c800368451076440b4100320710381d1610162212504568401c07009001c0350081b01c1c98485481d541040103000c1c0004141d06028030b81102c000c0903244050380410081240c108005d10078000c400d10404005000d4044990041c01c084100586900d040131001e0502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 796640233 1250 796638983 796638991
    0x7060e07050f1219020109031209091112060f0a0b1204060c020d0c02060d0605120c030d0f0e06030a02130f030b010f03080318010209120f150f0106052a0d0206 70
    0x80c2e0443c00c416219288001284100b4615481c000807407131842e80010f0799401380300d800140208005d000503400c010f420155540071106006002c00800808407803400850084401a071070540d0b140c1c0108510f817600352041d90709640010403045410740e5580d072000c4240c0c0075000150703040810701c0c02c100502c000761107242600070860003d022841c11020300181500b0030114001d11400c00811224802070260380001e001e0729015121b200c142045024007542e80d802c901600348203220300c041d1005000c1c494030201c62400059183c0c1070752401c0c00c0c030800c51150402094088496403d0101100c0642c00001c000014010144100d2280b8151b0402d4100d040c1c0582106440344600d0404000003140c1800316039022240203251411000c000f1079803400781c8941c1c00b4040c0c0c80001c40452441c0040d0200d012010380f6400b8084401158031038088048481088803044841451980100480c034002c00040403000f0100746521000e503600d280d04402002000e24403031181d844a80c00c0310b207254041040ca030300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 796641483 1250 796640233 796640239
    0x7060902100918022203050309040b030d0516110409080705070603020315010c0203010b090c0904050108060411010f0e0307090603060c08010513230a0c14031504090807060e07050f 79
    0x1400d42071003c42011000940184640305900040025892000c002c41c40240b5090600061289541f800d003280d5a40141401d2803042d440c1074000da2440c0303400180724102503603a88407103007884824510000d0203071000f40161a500343d04485454640e44e00d2050380c1e1100d10400d009510780a55003009403405c2d40c950004c10034144100280300044000e00c00303500d070340042480c0116019a0601c0802c1c05020110003e681022200341404190f20050010b8003d02c070040d2410859687da4000003a96030342d081d500906042c0066001502e81e51203030b08210a001c0003420045541d41040012902c0c21800d41d00100420360340c2c0b6418010405a8043c0603040c18203454100802d5040c08001280541a1000c414009940d610011034804d800c07818442001c0c4c454860b8803031458410401d001034404800c481c0001103100000c9200c048004003917078044d9007440201601e0030310a9080c000203042e42e90050f034104c942070007442c0000d4034500609114500d82da001d403822916040502914500b21204030388 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 796642733 1250 796641483 796641497
    0x50607020a030c172107020d03020306090703090c18090b0a0c090626090c01090e0103110f04060909050a0606120b0f060a170706120e15040203120706090210 69
    0x40400d501c202581c60007070300b140700c048001c98540d5000343c61788110366507400382000c0070017480317075103911040882c0c8613100c9a02035640890030310705c04504903c070441e145036002c104e04000c500e080b0b20940c031603920203201d00c1c40d025100b910780d071800349d002c80318072100041075071102c5088041000646260b9003180400c8014004902c0b2480e019200401c1801442c040001203480d031404bc0c9200056101d0744440d082c10b2920504280803000c1e107078507088580ba804614000703400910f07080c07220303d070fa8120381d04480402141a050030130440744500707142215078000d458242c045031039907040c414080d24500ca40c00400040d620341c41d2807415600309500820340d41103803451900104120380040760b44800754043c1f100090703440d040010a11420b940298100603c000a0907805402c00551002610fa45440703180046048220400650310f8240c8072a0450300314060310399111810720b81a42e000fa10040c06e589036100030340b130b003c1c1150700280c01c01d0ba402500c070b044030004d6040280da00d451001407446e2400d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 796643983 1250 796642733 796642753
    0x60906060f031e05031303032c01090311220f0e0d2f06040803040b091f020a0e041109040e0d08010608130204090804051309030905010c0303110a080405060702 70
    0x143c0380c407207144038041031a040f000050801605000f1030341e00e841d9618241035002d80b2410020900f8881d801d04000d415240170080c800c1001d981180441c00130142c0d119500a410350350340c5442811611310f404d802c0300620358501c4462408148030000b051a03030708001000d065404950066464200620381140c00c04000608801d922102c4800303501100c25086c4456401401420200c0d646441070009501500090108000303400004600883c0184030f16200d039103900c45501d840f0000160ba03000b030301142c2000d015040105401414100003030341800122680d41002080a442900140180d20140010205002e2800c0c0c4590740442e000b4100810f006654018040c1020030107006500034000030200150a200c1081403035031105074003400c18815144a4540000c441c1c009004151140842c6043d1880c0b2000324820208416055a50480300300d02c1e140064034407051114080e010152075030a202041000c11000f48485c0450356600e061a250a042040c00c5c5a0040c01000454004010340d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 796645233 1250 796643983 796643993
    0x307120c08010b130312020102031911040302090c120a020405010306060810091116080a080105010e0d3203030a2004090b01030b040e070314010c02100e1207060906060f03 75
    0xd0760640b4858202076680d0001813540c0405501aa0700003084016604240485190b064021b50302400508074100000081d8a0803801a02e04444010320050020321040003d45046004e03280c00480c100091450040041482c9480010844802e409960001402c1242d564140301751002419145030903002424201c4c0000081c3d41940f0a00c405940c449200c0c074241c4005004460200c0b01000074840b0000c600c0c500f02c0180c1c3c211802c80000708411f0400040d0550091f1108110010010b00306801da5006698807200c0702a020b40d480f04144941c00d070b48480b072070821910860641020019900c0f40341c140000030907030b012150302d00340d080300a8180881e1a040c40d410b0b941642c40f400b2000c01ca0500243c012401030903e2426a0f03031284c1800ea000704170440c0071402c08140c074001c0300701090000c00f024216099a0300552000c2c01a840341001d11110081e9512200c4103d096000b41c949041c0c4030304c842486a00603201c240c820036036410820080051903c181e6004040c98038102c2c01e00d074030315258 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 796646483 1250 796645233 796645247
    0x90c06022a0d020a080730120c0309080708060f160203040314120d09020a1e0603110c2d070501080412030603150902030105100312050c03040f09020307120c 69
    0x4035800b82580300c0d050421943c030070b02d5282c040c0c20a241141c4100781d403480e08000c0001c0804108603200b208514101d00c00090807250f90700250012818640400e04400c1104c107540002015010020801800700d100c3d541404804000c00300c10009082504000144110010300603098212041c07400440144190300441500e045a400684503003e031400c80c0d00150800711442101c0700c001200044d55808510945e12802c182c900176038250f611540c0b100411942c081001c01d8285000c00b40c3d40382040820301c282c12800302002d00303104440c10200d11803540781c5060324140174480f5803c54040764490100e40340000c442c0090804c130092881a18000000c0c00038880a0000381958000c10070b02427019002e44c11882c02035510040d904541c80c0d4442c550b034024001e5000c224480d50a0070003080111060741c02d06026250440f0740b0f02c800c00300004081c1d42d160310040704110540020711002403040395044840008084042001d40c1d84d1400d544001c00d624441c4404044407840c12602090035030b4331840c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 796647733 1250 796646483 796646563
    0x9022208070302540703060f090f060302030d0908060705090a06200727020f0301060806030a0501140717070e121510090b0a0e0411040e01090c0602 65
    0x5003a8004d2140c8004402540e0b5460184104003000c4100000001d41c0008000703445000c0c1c880c8604030f49071908118203452040c8124040382c3c001010900c00302c509684180d0350301c49882070000d01e240e500d46c0800d007480d4001d00400d01191008004010065080c00220b607c40e01350301d4806d1030300415100103420394a2a014100030000c080551035288681c4030000040c181030501141c400560b590400f20900d46200c1c400f96489001916500351403515001381c0e41c00e50002141d1303605584c24548111741c3c81c9801040668140314881c20301c400702d0300a102d200018210440c807000c8510b00b002020b848010050300c8900326085107002c000d001c65001c0d228583e038440440340c051000310035444607450646007100388070750f88042c03d080c4540e103c582c0c2e4510086a41a080c1440030100c1d680404c82245500d00c680384803006040d00280001d45150b500c00b10809004200088d030300f420215240c01c5481e20720701100d008105230014054950108003199a02d0052050f00b5880b1108090115802540f55 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 796648983 1250 796647733 796647769
    0x160812070803150a33020a080403020f0301090807150b100c170405150d0c21180c1202090f1512010609151a0a0c03050702040609022208070302 63
    0x1c640f91501c0e601d0031100001003803007181c0b605d4142c0b101090094210714080c18250726100042d10034400074008191195419044a0304d50f04191954080c44407803450201240d81c19560ba00208001a1022000d050654054108002e10b4210790032103208603a000501144103000c40040c0043d020380c040c18029442d540200d071400310070600d0011a0b02800749400c001c3e8498044d2102d103082c0c0c49010060041000c0c04141072040218804040d10f0302e1842c2d03043d40800400c0340c8800f20503e80607421000f002c001c0c80c1502c3c0380c0c2c8a11921070300f00800f580d80040036103036107209010081d481c0525040d9048061180c0e403811a040c119110402d604040310b0701802441c040c1d000380034061082d8807410042814241c18010a050b80b007078600c0f020350758081c0a103180b000259507480482000240c5859190703c0e02d644020310b0441c0c50680e11038100030030803640305480342c1e404179403200c090024100c4c14801c4c55980807030b003100e00034a5109c0c80700da80000c10039a02115080015070350392415010704041c1c3da = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 796650233 1250 796648983 796649011
    0x90209030f0303242e091e2c0a18050a0507031502040e0a050c130b1b030c070519080703030c0210170c0f0c160812070803 54
    0x15202090400250784950401400003004100b00c5107a18592010303824542c02810b400f824000e010001c40703803081001114003081c01e100e1049101d070403038180c81d446500e504051000d159140c00c40303048544034600c5d4440583c105c600400a0003103144080070f51280c5001c0d14086610511001442d00800416005405481e070040c3d41c46001e081c1840292241c00009541c52140c40382801542c4040c0343c0b2044544401c0b1140345044076600d4826501a258214407124403078a0710b0b16000080c040151040c41021800c0103036201041c00520141c0081501c0c200c0644c41d503034145040d042840303013a615441160401c00c2419052500070800c6c0055840c21141c042c0800f00102d400d07030030140a904040d1440c45a8007011042c150885601d09000d4402c855603803d141d480c4104440e4156140700c11080d5155010104071000c04190140c01c22440050841e410018081c0800346020091050884160407161007842842e005108695191040c415041e15207003495035100c09901c4028540c1e80c0301c4401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 796651483 1250 796650233 796650247
    0x503040f02011b06020d1401050105160201140d0e0c190806040602070c2102102d02030c031201090e0604030504141c030519021f1a0604030c030b0603160902 69
    0x880103c003030005802c204d0441d01da080701003c1c140107184400440184400440000810798410b01c12500481e0300306442c0c1c02891144c3e030065a00e52022901070a5581d0103005031210b144051003a803600d1080400100768581e050020301c6190040f205900b06204014034003401000d0700099140d800aa112100503907951050a18174030008490300000c03803547c10240780e20b00210100440301c075a0380c02161040400728103d207041c0c1708601ca1011081503041081d101c8840c18264076903040d8410040c7c0107a85c03070410302c1b03120700c1d09551000101e011044400c0b0014020048a0300c00d0300c2c400c0b0071840c01414203040a40b000f61142c0120703c10581c1c0074440511244203525134118401c485055000f038590b1410040c600036140d0b4002c0c0d440400703034180d40308032490f2461000a802c19030025a4081c0959541660922000f509107589541410030000c0c0c10780c101501d40714000c00095020f0200c50400b9415880e000407100c10181000d80b00e80d100507040740c4a11620800c8a048400b0781000607600d2503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 796652733 1250 796651483 796651517
    0x131401021b0f0d1119150c1706100324180204030c0e0901110a050a320904090b1303140a09060c060f1505030d0c1112151003060c0503040f0201 63
    0x40c1d20020300c150045810a140b0412407580b0106100c0006c0075010700020349503400464120340d400c0380040303500d8001c00200c0c3d03440c1040040e40d52421018035002c2038400a05180b00014407901d00030086510321035400f0842c502c95032204059601c3c01e40c0d819450030780303541c80d4541080524001c1501c0710b94240d000c200040401d40c45403403c1c000c0700d880315444021500024105401200f0301c03d0101e0090101140c424010079882000e4502c1002c48925a1402ca55101400d4000b031545a810650328040b48010a0031001d0103489550185aa01c3c0c614040b4907006280140d81d10340700c10030003030600100000e82d801c030840900783e40380783c83d003034008843d5828000080d0800451010040d07140248010200c2c3e508489074080e994140c0c1150245209d110003140c550003000d80260064060010387c0004c2d05d8801b4145100504810445581040d0300c14041603a48003030320b0309452031610190400070080c0d40d01882000042c2401c0007806c500d442d49031900a46618100203040158074083d00e0040b06c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 796653983 1250 796652733 796652743
    0x2060910090f060504060e01050a0c1106090303040e0601020111040e0c0901210507030e030403050717030405090a0b10032c120c15090a020a0e131401021b0f0d11 71
    0x18000d420381000030f944200c00703041a8003074042c401c00503110010340c007501d50044045502400056544000ea10f045480d2803000e112000c039220741c080c04c20050041c041d40c1c00c00c064005460f145400c0026402c2c608006402c40c0c0c50a10744074005041400200b140d025070803a8142c1c40303135030305148130380d990141d40049401418107001e911411000c00c04441c5603001c01e81c0b1140c41740d0301c42c0c0c4003040018000b41085030340e400340c1d10009100b684a9642070003400403220409a403418142d003241d01341511079002410700c90089904020301940c400b45201c483c9042d0801c030480320ba41e41801c12001c00308050113101425035117003045030f450542e01102c100600c00c105034180850940350b0261200ca540a910341c980784007490044050020381c1c0402c0460300c001c83d0f1409815130081210b40518031301009109440001081000b05696001c0355101040c600c40f4498008001c0100042c1d80c2c03502c91800b541e140d0204d0040301c16030351000c04d11041c0c0c2d400c00a540c11220a02e030030001d500000c4011881d15103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 796655233 1250 796653983 796653989
    0x70c051e0102090418020a0f080705010c1502192c1903050d020c04050c0f090d06020405041d0105070f08130507080a0b18031e0a0c021504060311070206091009 70
    0x54a4291000d01d480404420304425a100326620b0f0101035480c440c0d001c690318540602724007070308400400c204541c082d0746c102c0030091140380311064140880c40444100e070403407050b40c0050318481c120440041e612100441400c40314451070703400341040414642200510b40301650082210500c0c000b013031030702c1c94105070040d9071050071074822000d094002911180c0c11b4007500e019500340f801040d03411003108280c611510301141c1c80e0381007050440820212000c82041643c48550030003000c601034075503018880400c820140d41086201311160011308640c030081240040006038002d01c01103a502401c003030342040002c40c410841d40503d00b40325041a516074496980e6104500d03522080088402c4024864410dc07030705e00c0d28070351000900070384070310401058402c401c100000c3c0a002e130160310040c24806034070740b0b000c0300760300c0003035000c500d2151710900b00b00c05180000c20104071640c1e042c0220113841009096460800d9010307400300e2202d028400a45120301c4144940090241c030812611000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 796656483 1250 796655233 796655239
    0x11107030311070b161128020d0803010e06130b010f030f0b0603090c011e0504121a090a0210030605062d0a0e01030b01080f0714090301020a08090105070c051e010209 73
    0x216060511003c20034805d0081c054012808441c2c01307440a50010462100110b00e80089000401d40101c40b4030a280402208a0340071b664200c42001251035840a98060004601c60b07032146c0c00d1110420140c100381c8004440d446041146091041e48d0003c0c0303c0c418941c09081c046821854008944094502561080c0c0c0256001c42000b014900001e403100100380283c807108144000844000ba4041c00054a50b000c10810001081440c041c500d000b03007158020103d80c00a1240303010042d00c1c170304c17094551884980c0301c211484150319041540c001c64544c0c40c2000c100c624645070104a40740036045444100c00500140e44c01203608201440780020900d904150340c0c0e0585074009484069000c08a42c0020310341000e41c1039650082c800b95000b19800e540c1d00700241d890f600d089030000041040c00d1200b030f00602111074103031401d0014190780021500c03480010f1038914045030071283e00178206804c001122200d0030206202107620030041c0c08230743d410b41c0800c0722078084601901c0b42c800d000e50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 796657733 1250 796656483 796656503
    0x1a090d0c1a0304020a0806040206070807050c0a0e090d09180908090a120501050a060308070809220603051504030507020108090705090c0901081501050d2403060c0f0201110703031107 80
    0x500e99403040700030352081d8801c48034551000c3d12001156a60202128000c2d0407540802001003c20200d83c054484907200308105c0700c0001c0c030030010400010309584003a42002a02e8244100b00a05100000c0101c8803441d003481c2d030a1404442c00d00f81e002d20100d04c0103071640c6d00d410b0070a20042e032040300d40708003020380200301d0f15643e00502c030040c01c0910b07802e40e03565103880d0106001d21000e01821040340c1c1c020ba00700307003404919112081b055000e5514590b004480446240c0030384040308030005041003803500000c403646541042ca090010303117401c1c0c2d41206200700c01c000c00a50000c0503a24030540a20385985c41342e440e034000ca8a0280c02e0340225030b0048007101084800541c050051220b0002070303880745100e44070103045116503c036504200380881d00901c002c600300e05d213940c4052840d84070001240c50880d005461a86a014242c02c04c1d00c9250b01da4103030460041c1c106500c0f11040c091880204041e2804034603c080354000c0e0000242010707103a604107104032401c902502e0301236410050801d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 796658983 1250 796657733 796657769
    0x30c0d0501091b1a120c09180432061b0d020409020a0e0d020a030605060a03022805030a050312131e030311040503030d0c35011a090d0c 60
    0x2940c0003c85102e1980c3d080c481c0722140720701d89007402c290b480d001000030240a0a48a00710081c0558105686140c0c00c480d00e45414180841191021402036015241d005100001900001e24840d884803a421030040c4030754a40062040008945030b00460305021801c2002601d0700c0300030203200d5008103001280c000320300801d152171968010b107501517054681c1300c0d101c1801e40500550b120610400381d03025214000810119020b6000664801d40003800400320a4a950029805501484403a55144207003112401c540c044c0c5030503000a0442100104034203d441d40c4c48503502d04c50780c0d01c0c4a00144450010521036038481045095440e0b0001603940301d0750344490b01040d031101b000b0b41500041d09220080c0e0b01da0607440201c406a940140c0554540340b0340110820107040b5404425040100029444040154011004c10700301901511080700450280c240c80078550182c01c0000016444210b40e00420301000c101e4405140566804c402c4031424103120704505140c2d070001c600310703280030101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 796660233 1250 796658983 796659023
    0x50d020f1809010c0e010c0611160303020c0d0903051c261906080c01030b0a030c030507150212090d03090f290c030426030f180f030c0d050109 63
    0x3a40b02c1d5900748001c0256149052044955140c00da854901042c40450000302086154001c001001410078900e0318007507002902ea00300e4074103c081500001e5011480821011050010b9261035003d8517040c038400f4115194a61281c040c0038880314a04843e901c6030790064090521564401e98075007002c42c220540c049000516601140e0b509041d05920503400d9040903d8400c00c0141c030307035001c01001d0506600005500400c0b43c440e032540d01900740c0c0000800079003031400c0c060145100e4409030032031f245402e491805484040c00148155001811010400d2841d01c050790300034a000c80b800440c10445080942d01140f4507040142000c1c40c00c0f90110764212202c5400030f1000075200d480c08203004095080c1c40b54000d2480e4800c954108120800c00c0d01d214980b849048000131003801e02180982880390b24641c00041104408076010414000d004d040c5440c41141c200151031080d41101203a00003a124040d940d581c0e48913030120841007051060035402105041d9011324040c494035000086 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 796661483 1250 796660233 796660279
    0x70e041a0603010c0e060703030e01050705070c0603200a17070207060e0f030601031412040f0311040b091902070501020c060f10030803160c0210030b120c0a050d020f 73
    0x24000808000c100811058201403080322000e00150741c030896056101420400381f42e00a6100b503080580b201803070b251441e400c0c4101ba0241c5000d4a07555901c0302d59241c140e180d001c040d130010090510307080c00c4140300011955082010301a04440b181d40b03000d40344058480307002c0044841502522401040403041d000a00b04043c1c0e080c82e10340424103881d210420207100d18264515415400c100010000598280c0f00009260126815119034003080d080744c5d1802e820036071000b6040303480d0840400c140201000c000008030b1007a1014000720350b10002084d4a1600640f282d01041e40c1311105200d8044140d0680d8140e5610134002d543c0d5110b14511196a4882a034114600f5840782c408250745014000541003200c0c0d0003003c042c00c40d50342901801c05145241f408100388880f0b20002001030380d071244509035116090f200050003001910911040080580050055030f0251040c83c41c1d41c0c4c0c40788c549404880085492070380c001040d1011030510600c0e030031415000541d0300b21f24a240010719403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 796662733 1250 796661483 796661513
    0x30f190f02070309090e07081002180d050303010e060603070c0209040c12061401082b170c0a121503320d12051509060d051c02071a1b070e04 62
    0x1044c03064400140c10b054507507102e0300c10440d113270340300c0d43c2c4014038207003141c02074104a000b000001c0c0580e111800820401c8206050446541d040040140030103551990381941210050f2541811440d2440025054010b40c00c0d001c0e00c142e802d04001400c1200c4e400c020809803851000380ca8052000703162510282880c4075202c4550b14000c1c0012a0203d00090036440114020012042c50813065100400349040384244a0400c40070780e840034500402c0c10b07801d80c0a0b01f040c0944039664440c19800810a0b01403000c00310702c00d41001c42a2141b808981812810389411103c0ea401784103900c050800c041000d040151042d5808260700d00030350300003141f480a100b2503a1961082c2c0c150305e02c2c04800310ba40440b4802805800d0251452080c208441c0c1d45502410182000450707244d292141d92400200c14100c010741e00e40b00c0070400b401070b41444100c00400041c004000c0b4580300c0c01d1201d00d01c1c004c240307441c4450801020705082c101000c10108000b081c116881d50f01c41c3c2072508146400b06440c2c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 796663983 1250 796662733 796662749
    0x41b060c031e0503010308030a0207061416020703150c050408100501180612030c1104092a08070e0712050108010c090b090906010509030c0414100b030f190f02070309 73
    0x1c41d00070268007886011050907403030750341c4030384ca180c1c2156a0403c40780c1010b440094140d90901c0315000141c101e105103108044091340c00348641c43c2011040c0c1400a00b0303165841150000c0da0300b00b0010707212205085141800010108000540e40d00480e002c0c05907a2184005e0300c0340e44981101003035250700041c1600d00c501d0401da24400f400e6a42c1041d500c0601c42c94021184071b5040002080c494885145070038132030f6041104000c66000020b0503105204800ea644840342949900301c1013003101030180140f21100e03820f07151480d0124041c0ca07844140b240c41213107291000010400ca10421940a030303040594000c10485d41c55100b424001c07d180ca400e00c01041248101050500740b280541743e0780c900090166865998040044410b40c114203e900d4251080d45440c0d0901d554501840d503456021340300128183c60540685c01030034500d07601c80380a040003003040c440c3c0071060950007070b0310000e4107460000345110340300110b006001103010310100324400b260946c20035601952100888401c1c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 796665233 1250 796663983 796663997
    0xa030b1c060b030313121109040629130b06071203020405030d09050f1e030f100b06031614190809010b03070b0d0f09051519050112020108041b060c03 66
    0x30707600303041daa80b20302e1802d45403200c5c901d0400c00c10701c80c1501c4d1070001e5510810034608028000340c0450002e00741620103c4102d62617030510388625070583c101d110440c1881000d143c83d07004107030100740182584849401210344030300ca0701815445070000c9a01c0f09500210030b039001101030400400940260041c18840d0040010741c100396481003001c402230b60b100611851021600d4010414003280c44441800c40404042d180307135165409014400c070380e0030b400c0b01070314800c45800320500888040355034403840380780c040c424080849180d080c4810a00001d0910101d0100480300d00d03d0b443c01500c21048000d00c44c83c000001569110001d9070041c14074100a10101004000300741e01c0c0e40244c010040c3e160010702c000f140f0828140c1080c0c01a0030440c40000d2020740303640301c0c241407440e45842d500f46040b061046c0288800c0080c080d08250481d4801003016506280c5001414540e00c0e8000c0d040001e1400810103200c0240a500c40301d00000442c01c01d1380b640ca060142148082070f038113902140003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 796666483 1250 796665233 796665251
    0x90f29040218060103061a1c060b0a050304080c190515090607030f2a230702040f14160311090f010c140313030605010b1804020a030b1c06 61
    0x2545044a0085a000346802d078401400c90070488458401012541007586507103001070b5000703008000700c4600500d00b44050f0303519914401c84448400500c030820340b151811508104140308041034034030f040c9a034a0300381e9a9445c6c40c141090b843c050156515114003921002c440c003501d480e45207030b1016200b0016100590101121144000700841340e9607200c1d0060300028000c68070030340c00030b4405041c040000400141c0200b120395005070051203080c90040c1c3c288640c458942103881c0f4002100c075146000e4564a400c1081b80f506e0056400c0240034548400a80243c20780503007102c1e820000c040c0041480740351405c03044030702501701160100400d18010310300d000c164403003049644106000c1e0001c404091800e0044030060364100c8261190041021701c101030b806c00344001e144914a4003058001203055080620485006078820040714004006100c014000c118813412400d008480060300c59191050a42c0908001c6400e540d010000b010340c2c1c030440c10b1192030403e00d580658420011140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 796667733 1250 796666483 796666553
    0xb0d0b040b10020c0f010207090f05070206090a0312180b0f151008010b1308060907080714010206070815133614010f09120f0e010507021201090f 64
    0x1a00182c0d0005802c0426800c1c3c0d00d05010038200034a40061040310a02c44ea1000c80204542070180b41135207080e01c0c0d0061000361a0b0400c580742c0c010300501d01810b10502c8075640600b08021000204a503540c4813455216508001500d01e0180d03038121115903110300c2c0c80385a0084044049030038850074000b5100d010200d0401207206540b056868a0750001c0c0c2c0d0070090110f442d90881d200d041c001240300308010462078401d2104c140a49020002080d8003070401400b142040c17040e411030001b007801000402d13130603a4001420368200c20303035080c082401d032289401000000020224070341c12415441c0808540105039201110300020556103805855401c1c80c00f040142802c0d2071505000c00035101400819003610405c112440e18030300000e4500c5c54079201c4070603944169400d031030502c04031070b10f900e2264000d00480160941c500c0c00c04d4000c203039000003070402c0c0180e403006802518400d102d8100180e007540018400c03a08800380022007001032a01030200c0a14040708000b0803070484144074210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 796668983 1250 796667733 796667749
    0x120709080703020d0f0609050a12031103070309060e061302150a050a200604080306040e07150507080915031f05030c121c031d120901180b0d0b040b 65
    0x3510003400707454403a14540820407150560181601c806480c0ca0700c0700d00152013407041c24200c91295004d840b0b440c0d581e0401d20052075880356580c00741420f240141c0d6400a211080348c0d401012810009881055818604010085400d00c0c103010f100e1501803150030003a0310b1080d011140b00315400703d50b510f0b5402c44d05840d80184001c001c007095040c03010b0f40306540100d169001141014641085072444119900d01d0400144c4059401040010034000503003060f02803c100b50008000800401e80303040074501e8104910340c499010040c001c034402e01041120001c58203003040080620580d0b40010301041a107a01c1540c20303001420081c0d081d800911201300c00f420454031700030044c10700c030725900d000e0140c05155001c0f103000c0350140c118050704015001e20301d40c00d081c80b6954009262006121084014200e00d00d40001c280e0100500c0c0640d58403030001c81d10556030030319143d070380054000c2c440d480384821038110b24035007000446c240c0d590000f01e511450418000f2a0b05014041080c0305202b030384 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 796670233 1250 796668983 796668989
    0x22409010e0106120b06010c05030a0e0f030303060a140a1e05030c01020f0c04090c0801021605010609060302090402040c03060513021909050108061e030f0609010b06091003110702060f120709 84
    0x4c010195004004070351410762040d0301180605001d4517188060341ea15081d0307030042520300045049000411030f54106030f103503260754101c00d40085203035040000005d41590060b20600881111245402600b40c8440035070400803d21000346020200484008020114481c09418043d2007800500e6100e9840042c103008040040c1000d032403501d242c0c10601010346900f66003658800068080094072800c01d100030042010f0602c00c942c0398055600c3c0c031609681c00b99002d2108941001001c3c000b6948885400d034201d6070403140015406483e000c10f03006000c0300d5105581c0014030708a54059000c9640091940498407514a04610f103880070507202c98145004060001c1c402c50009146400d107118000c02c00185c4001c40d013002c0301d100740001d2802100c88040403090b0440030034800c0407002401007d0101c50220b03841030800000001144103404580707901300805071928002c0184203109000c4a2030281c01070070f019a2807005100094180d400700c0f55109003000c40d1800607034024800d08140003a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 796671483 1250 796670233 796670249
    0x501031b060815040605060a0201050703050f0907060309020d05070303091508010b03071209020405150f06040506250c0e2203050f0c030f2101090c020a0210022409010e0106 76
    0xe1a00ca010720701c0340225203220f10507001603885402081e02d945242c040d101c461301e10b5002289038a080500242520f90241800b0800c003004001e0058410010581d10151083c0e41390018161840c0d000103044d007900144045c241d0300508038044103141e4800c40350002d81e07005500c504000c0440c0502160600024422014103520510120740d55034810710030502c1140c3c40c1300e030100ba010b846400140440b54261030100140400c080e403500d83c1d042585a15082603c100e40442c10503107010046200d501c100c0c030400e40340314404001c1051580d260a50004200d400412000300c090302c90845440365841600c0462407864a0759a00507014003401110408075410744c0e9550506030f0f4090151520303005600c00c548140000d00400c1700036084480540446a000648410150613080081c4d40403d01070308036030030044c1066010031003142c00241d1020f94543c180c540d08408642c41c02e00b02e04140070f82c549000c1c1100070f01ea030b0299000c0c43e12030050045031000020428060101002d900b01c9101c2e00c51590 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 796672733 1250 796671483 796671497
    0xc14030708060907051902010510080105010b0409021b1207060e1609110405120d0905030d17042a06090609120b090c030a0b1e04150c02011e0501031b06 67
    0x2d4507040244002d0742011036810030905104c00406103030303807050000b982c040060b9521020030922501c0d0285010091500c0f500820465040022440c41403056000d4a82081d400186483d40100d0780d032401c10b011020f0341c06031092511000c0e40f02009603c03072803044d01d105003001d880b802c5944003c00c0071501241c0d10071410602c1032820f5000d101a041c00c8500c98015807041c400040c064545026412340000111302030081800d000341c02800442c003e4101d02d0013a030101940181c0281c0051007000403c80c00c02000d0180c1c2e80d5072510070900c220900120b10101d41403c03030720104039080013201050740c100d0b440d9500169100c02c0e080b121280740d80b050840c110701c1485900c000c10308220400d5003245a0781d06556011354440d000c68a010080e100440e2101101010040c0741000b10ac6861115844c10408417541c2c102912a50030000003c95070489940d540d500b1260b06c0e42c000d5009803001d9074000074051074886400c908400504c4240720566410b59861030148100c2c141e507403a24195a10740e22181 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 796673983 1250 796672733 796672741
    0x10051b0a110102130b030603010f0203060114070f020d11040c0f0c0f061d0d09060302040302060f0a0c020919060803070308070f0e0a0f231c08120702010c14030708 72
    0x80315607107610030000055600b085000e00f403441104400000d0b0848442041d9603003458414140ac4410044080310312901c14410300415031f0340900c0090381a007060383d12544503c0c1c3c50800302460ba581001c0254004070045549041008885105001c10401c5404014810281c0e0090725a036103600721080004020f070741002e0000355040b4400350301c24000c06002880b0500710200c1402c407080100111045e60004000e145000d80c81205c2c440645124601541002e2440d4041103190044c841e05030000c4c1c06c00724030030b928030348220807658900780c00814941850800c00b4401403504081c0c090321000078140700f4040741c500800022640c085501d40c0d1032002e55075581c3c0d02190900d601711130060400c0801015001980c1e20702c0c41c000040c001548529210305d04d070506501020f8020700c625040c0e2081520084c01903540d03102e0741451301107014094400b02c00c281c50440124440c020f9a02c1c10320038000d05100c5859415400031941440580301d034012503514180000f0039020484d600c1c000241d02c04005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 796675233 1250 796673983 796673987
    0x31e050607230d0905160b043c18060e04110d1a0708130302121c02070c0501020601060c0c060e04020f160b130c0b1e070510051b0a 58
    0x140a0b003a4070002c2c0c0c80c40321a00080d04200c60b80c0000240e94440303841d411842c050183c14001440040c00e0f001d02c6800705441d1598588850045100740c2000304025030032545180c080b440035001c425510340141c049400303501490b04040059002e41c01c01e00740203001d441e09003c0b55220746015981c0750312207410160b450b550703113015403100d030503040741c200e0030310000c0c0750004514135400780781d00d800944000f0481ca0f02400050480c0742c001c0c8012865034400008001094012036004c02c00c03088072041d107070f4851540c0d180d00024101180c1d845d144501c0001c800c0140803640c8605001d4501c00d90a51f00b0300e9a0396003040314207100002d40500705440d080000c0111501400c0402011480030300b0160900061903990741e415000103100c902284a00d1110320100021203004a52042990a074013180f200c99072540944030744640104107589070f0010b6000c4151014407448030b6409900c01c495a500c000c54030301541c456400c0d181c00360745681042e01240d0340100d499030b000b20060507070307900d903061100b5040f007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 796676483 1250 796675233 796675247
    0x270b07050c13060801290906150c01060807090501031a0406090b010b090931050c1002070e01050301021c0b040b060301170c030f251e031e050607 64
    0x41150380d4070030070141030902d45411061155003029542d00241d40c0746021286030948089003545804101082c8140c402d8890383e02801e200304200b0b507194003c0381c1c0c1d40c001080d0901d041096855020a011451505d2000150003090a4403003040540d51110340e280306200c00d498080c00000c003140113044141200d08440c0d01c20a512034082c03000030840441d1030315146101e407030a80004080002c0054598910305100c41615002052515880349026001c500084800c0e200d942119030400406e03002c5040c080700300704141d0603507030091a000742d4541083c00a947c0d44014465040d8010440313000060602c0e061003030740c00d1213484035401d072242003d9141d480f00525022169a40c0207640e07551100b01521014090340c064204400318400c28140140414075046981d600d40c0e211ba407041c09180c204840c04100d0f4401c400d01185000f000c081c0310310501d2128401d542000440d640b041e10b210a00980c00340964044034021403591416100e4190702c000c4100b6012009004c640c451030201d01010301c1004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 796677733 1250 796676483 796676497
    0x21504050c06130513022508160203030408030f04081605100528050a1d0a030b070c060507030903090504020a0906050f070605011401030b0604060c031d040912270b 72
    0xc124600f00f501c6200040401c03550718100c0f200307207074041104840c48a58681c480360395558001c0f0100808003c0d51407031490f00c02d0564070380c0c2240e104000e440031901d04005680142182c601a0703074464450049000154200348106c1560348a030301807424001c0d9103e82510103644020301440b8444c0c04011080c0e5845d4070904070702e0007080c81030014000303c1444407030035429004150380e401da8030245028020b100206050302a020f514040301e409009543d46400801206e0384180c0f04409540d5005050f01d1401c034007000a031200c4d04050400001d01c2d8142e0040203802e1207038650004040d1078a052101f00c0c01406006004900104428410130b4040c501074000001155500c0c3c0c43d09005684950981e042a44180f81866215085505030340e00340c01000c49884003600c006040c40c1c9410001041c0c2584002c01506200c14660400c140071041d4001c1c22180c400035100740700c2d94400b40342414401c40b69401d0f0000082d041e00e1502c681380300c40e850001e0b00304203081e0140d444a05000c40b100d01984151 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 796678983 1250 796677733 796677757
    0x5070e090a0639030507050a0c0b07030216050c03060109091e051906060512150c0702010912080d050a0501050a030b1f1701060f120303021b1b01021504050c06 70
    0x24020300400340e40b0030f00d030465416081003000807110301404090255040a0040403d0040c1402107603040303a4030501b82203011707401903c0ca801c540c1b01e01005400903c1441c1d0941d040210307010591050000018807154409130540446465030b0385e606220049030110075009000e420445056414400c0e0b40c8440140e05000f20241d131110594003100010210346000c04440c03c584030b40c0200b08601d0720b0400d01c4200d0210f240503002074803520000c41c00c00c2000074140c48480d04042030040559108500300300191180c6003280350102d5980c14107414603005010004c1d01d090500d00082d40006450003414102c402c0035184440e441d0456441c0c040030301000f40105074002c082030312410f009150090000040c503100e2150b1200c0a005c140e55800d5944580200580e00c0e4458010026072540d0903081000c65014500140c070b03a98124084c01c00c40d42404500111403041c508401010303000c1701180c00c14964260215521403407020380703410210303008403009040c1c2e4124400e8080b46050010081411100507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 796680233 1250 796678983 796679021
    0x1090b0402041517070f05090403020303220c090f0f1b0c03020123040210050c0c10030e01060f05040f05131e0c0e1b0c0d1d06030a0905070e090a06 65
    0x1441401310040185564a000c691200c0420400b41c8042009000980400e440305825403038035440203566480040c2400d49000400b50103400440458910070800c15404460454607541d5064207102401d003110319031240a00d4500c10f011450424418a60140f5600401d1a81440100301c03d40341c14415200130760555480d4003144c1d0317180300780340d0141c07401d141e158400745800d003040d0040c4080300e51001129001c3c0700d41006248110200050300350f840306812030b10100710300e0030100100e0203016005240f5800750300780100420044110f45400d000d54105803820040104180c0003103054600540303036824040b480c8007400380072030030302c4a420321060003041c002d01c44c000f0555944041c00c1404e5000804c024201c80a00414503e116000440341c0700e058100350420003081c4155803104850f400b960300340003240c404621410352841d410841801b000b06101e84920340701c0c4444014180803001180c00b409100710104610950400450061000200070070040410b681c5d444014000c01d01ca0001424078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 796681483 1250 796680233 796680239
    0x120e030a2402160c05011119020619030506041b050403022403040809091005091f090606050d0c03020c030d1e02030703020a0314010501021207140703032001090b04020415 75
    0x701e000614091000e007040c21420000c5081400c103520035a000386040040c0810410308580e000101020456010b10007032900440920004e4824440d2003d0110f0407410594001e03181901a440f02c0d1280e9405d503028000c94450b0410b202440307100100b40702c041401800140054105190000102a0040030f647d80c000d041000c182c88a8204607811034103a040000c0c0f984181c00d14180e12038203c4200609a044103041c1000a2682c0c1e100178102d01d6035a415051400d480c00c603a0b181e05008003400c003801c000e840d0329040d008105038030180442c180d8900300b41810340c003684070f032089442001c0f000001d03500307081800214602812110707000101c04644000e9540c5003244910085000300c80715100103a648540400c098185e41440b400e56126091810040006980124401480300d1806000039610900e51404502c1440070513850582407081c13034408020180c119142440e0745148866131607042c1000c0300d285003a03412018000704840294000324005003421741000005003881c030303030801000f43c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 796682733 1250 796681483 796681553
    0x506010e100f1101201309051509070e130b0a0f0807120f0503040906170c0a120305130b0304050f06011404020a0e031204230906010e0d0807050604120e030a 69
    0x84202050102c00c0006281004070031800200000f013540580502185c948a2785d4244402411001240180c05000c00107103124400c24030440380c0c000061422400001c0a1888001065144000e40c01071030002800304040b000e80b00030302c04891030b8400514059050080c004004060b41a003101c46086603404440014070a01c041d0000d03000011000a00d0341c0342190400c0c003c0196450611140c01420051032541c4440358820162285448081c000c010903150840d1644a000c141d2002c1f820800d00c00304002c034a1a00541c001c030700603012581100d05880321281c0301c100a02c11040103e2021003504400d00b8160041c1c0400101c40c14000840d103c0480800d0801d03000d003c65180c04240010706202d0105945000c0c04000c0120190000302e6600705c02203220b280010b171103e814461174203034000c0241ea0b8803400949556101e2040785d1070b40c100b0b01e80150340341c40a940c100c5481e1070f01c03201005128490b124456070501d00400a00c0455000c0e11503c034624404101003100404002600c55260 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 796683983 1250 796682733 796682771
    0xd0c15050415050106170f130209090705040507020316030f1103030f09011b081b09060f1312080d090309090c050c010b0609130c20010506010e100f1101 67
    0x1401003100c428401403500d02c1d0000c594050300f0540138002003200240e10368100c0e010b0345500c10b80f41d00d80c407245a00c81e28003000da10703244090004c4d4080c0200c0c0030407800d81d001003480d40c204d40e403d032028401c940f1003000c280d0700c074001c00383e42d410180b10011401000c60f1042044440f484030b035081603007040705010b5201e0300b0f60341b040750100e9400c81d0302024888003980c00d11400c0b50040b04180c0c501e50920b07a44c00000c1a03248060f0403501d00e020300b0746203101c0424560044685000300180380e140e64804440c0c03131001c9a00160800000c00c041c075040000d038079490f821788180d00e50b4005606850081800c503128001c00d29014180c0401003400d60120716034000d44515011080503464440e191040040114292000310202c680103210600c04402c450b12052820800b05900200c04950700c207960398103d031402028030b1002a010f08445c0d00100c1c1640642c40350340555000c6e84e4041000d5840d5060040ba502c03841c0000300080c0106031070411441c4644001c41201903000c0001c1240420f0101c001445 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 796685233 1250 796683983 796683991
    0x80c091903050123190219031d0106180f020408011410050d0f0308040c03020a08031e181c0803011d0a0902011b0c180c021b0f04020702010302091816110d0c1505 71
    0x10a80d99181d01400426040c2e409040c2220540284161410b00310404100582d21441ccd148198448400c5803c02c403850b0191800341071100002c000c0205c00c100401c07007050b0305076820a00520040e00c082654200070f0608440d0641081c0c281084150f65074084600d0000244251400c000c03021002c0016238508005034020681c0400640d140c10500c2c003249015203100c200c43c8600402040100d1325102496540003c0c00c4003280c1007000103401ca800e4084d4911b00c00c20040c5030341c1c40000040303181805d18030003000c0103a0810b03007a1000d0b96410143cbc0c08035546640b010703002c166049601200b0300307603070790003050010f2140e40141c481d030703546540000c5142c09090740050641e44030300c039001840b40d04200840c091b0115504801c1c095208002103505510344604c8140142d4001414000396402030301195902000600244800d81c02c0310b440d03054080080c0c510000320b2050804640c0308030300c0742110007080003600c00900100b00c0e00c0c140c141c070200c01d5440c040b1003d0000416085079006c940c8152445 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 796686483 1250 796685233 796685237
    0x3090c0305010b120127140d0306090c020d020717030c03070b0f09060f0103080d020c0604050a0201031b0806040207030903021804030305070816080c091903050123190219 75
    0x283c0c44403000c1100000d44801201c08607031600e0082c01c0e0703445081d19000b07aa25040280e071440b040040c1010010200130ba802c501c218815036140114656040e0700c1032017124110300003081a03040700c0208a0722180300c10382000041e4040d0c1402c1c4544000b58201d25803903034203501180c1c9444134594405041d5040b008099584084090030001d0641d101d510380d55110420f1002760100703181c082d1504004000600024040403c041500c100701308440e0f04452005071908100c480a00c2c0514003156500d100c15030813800a0306000300d04041c100b0702c4505249042d03160720341a19940d240d0003840001d421510094040001d001000005a11601038501020068050184441c54036050140076600d025200d50208504201081a89502c0c504d004100014922303142041e43c50b404081d01c1180500b0141640c00f40320229038051080416a0080440384280002d1000f991211086415400c4241c0c0d0140100c805c0e0000682c02c8400b240258100c480460005040081103101120b201c5194072080c80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 796687733 1250 796686483 796686491
    0xc010c030b040b040b180a0921020d05160311281a060d0609020a030c060201020a111903080712050c1c0506060d0c0c05031912151503090c030501 64
    0x401e400c0c6406804410f0380d0540f014032040c4202008241c020010900c4101050800320110310b00c041070b90031078000c10340c001f2110783c040520480310038031980040c41c0750005031240d030080c100c0d154007030803d949244521994040c6139580c140c5007960424124a4810094001d204a8030404a41a50917035403c0840040c40705c00001d80f40f80c042500d170895410f031a00030f00414104003256030780541030031040398003500100d0441c0c981e10104840303103c81d800080c1000700140c03010803003650550140616520f00d640741620341500e0480c054803655102c00031a000f07016110f080010a004404954103c09245004500d40640031020703c112074003960010306d060800211004130000c3c09004503c4004c1e01d4000300024109880060b40d40d1007607910501e000341d21081e440a01320b009000038440c0540110a9a5440c9581198000c038500c6a004600201c1c1900d000d2040410040c410b11082da01c04041d05200d030b0b801c000254002c0c40070700401c0d00405880b40100c130f00061811880d60011441040040303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 796688983 1250 796687733 796687751
    0x330306120f0a0303020f070c03061a0a051021150f05011803150b03030c010b03123412020d0201050a0e03030f0703182109080c150c010c03 61
    0x4150349040300440d41055200108590070740001007001e040c80c9a2505005a8482288141c02401d01404030054110030740d032a0b0000600810750023085100042c580c950081e8034550082090120240c041c00341c0028034584888075183c0a05041e1001c1810407824080d03001d01d070101b42c030585280400007030b000d13002c0050401c001000e003032100002e01703c2400c20700a150124009032045501520001c5c2103050014040c04054031603900c040380c1461301070700717a07541c0d40c00b203005042c00b81506a01c0c40b07010b031050340c10b100e43c1880080291608041886589208560ba20741040030801681007540d14508001c1d007284001403184001118008041e00a0310341141900c90103400c640c00100b20101160078103a2640310300c0004001c076a4041c82890607207a061300d80c81000c0300201441038400c503007000140308040611048484000d601c8408428001c034039804e54804503007640c620310a4035595030007091059020315204004c41341722040445030724140540d10103541d09442c040e42889010075600c4e6040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 796690233 1250 796688983 796688989
    0x7150909050c04081b011107092306030d03020a141b010507050c1f0605040e0708061e0105090403230c01060503070302010906081302130b01030b1e330306 68
    0x11550200078108001c3c1818a400c5519403241c01055100c0c4c400c50a541007030200f070b0702920300384500d6a40c0c0000c65030000d403551300b00070090002c13840c0301401407030000e10310134407102812200303102d44006030240400700c40c02074040c0c02940003c00c0d91824000314040310806881d008010f00010101000a03895205d501000b25086481c0940710808200c2e0402080c0c100740e0002426442210540c0d25112204441c411100c0c01060140c0019034814100038100400803000125841650451004d807040c580300c1910481e14426280d1490901842c52401000b0920f003205000354824024241248000c68440e015400e41341f40c054034a5880d40081b44440010200b40b20f8640a07240690042c01090305640010388042611b208000030015181c000413446007801c00089039155010300074620a00702002c250740509078140d00c1d0b5002a1400701c03290f4a5183c481c461707403550150104101080c1100340140502104030f24200030307140409910050a01001503608608680200b03042d07610b90908000f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 796691483 1250 796690233 796690241
    0xc0f1005180c09012c0108010204061e120203090a1212150803070b06030f0a080909070309020f130e060f040302060709241b11010305060604031a040507150909 70
    0x18100c241e1003035424000ea0f803100041d06054800d09000d4617106030501c80d10090601d02c842c0e83c41e140e02c804600000e03042038150041c10030b886242d240d0311402d03030b14000c0384908440d03080f254000040c8500403029041e1003079801542c10107102c03019a8103040054a60300b8030981c0711840c0320005041103682e006040010310840000e01c0ac10491003d2079854022007541c3c13401207000150840b003000011074215a01080403041108101003a1208440c2ca4101040c080c1c00c511040d0303010320010400070b8101d07486846084100fa900071303c407102c0411004103010003510701c040c1400b1076560742d42c00008039200030040e4030b205204c1d007040030605207000c0c03070028200311010744450144140c200003030081241883e42c0c03400340390045c0c100c0503003a030180740e080703d409841034802c403049480025408184a0007404411045d882a00c040c4041c0d290041401060f1040e44806840038032000f52941d044040308840c240c0250240703003110160390f250903a6030160071b411100e480220f580508204200001030007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 796692733 1250 796691483 796691521
    0x30e3006070309030e040b010c020a0803030403030f09030210050c040f03080d0b060705150603100204060824010219020a05060406080f10270e0102030108160e010311060c0f1005 78
    0xa028820f500310303a64003901156203405054800c54658810b6501a442030703c9145e1465002400446101d50380d4142036201d51041d60700b500024180400c42a840b59140641405d450307040d030050102d503081d20b00341c070010000900200b165040400c400205c2d019070382e05040181d40128401c650b078083e12810078040312000090309014000c00d0003100702003900410a160618030045170354042e030383e82200003814610400f28502c0594800310307010031540d62003107d0501c038030148041d2202c10b098620850b46600d030302d06101401a448000c025906020400c040300c60544050b01d007a065644640c00541243c01070f4005a0000f080340c1c0c10003140e90441030245402500101140c529603040444001e45099290007102c10f00140c1c0c1c52128841080d54411502e00f14840e000715144e50311001c0b4a1b441306041641d49034107505100f404a01d810f00c0c40400d40c1241d900c444020035011705042803040b43d13001640c4402c81360040308511214500c01748260101d14400000c0050b407850011010b4445a90201c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 796693983 1250 796692733 796692737
    0xc010e01090b1801020f030403030c020105090c0a180b0a090516030e1207030c0501050109061406040815190516080906060a0306051305120c0f1603030e300607 70
    0x5074254000c9401c40b24019000b1075010f600243d92400f141c02c56019108510095014040000070001810f41c59802040b121402d82d00900c00d075125240000d80e56451509296442001c020f02001088451407244e482c00704c802d0000305501c0030180002d114114503921040700c4035100c108001001c03e180030703031b101c204a01e428200108070316284003583c0d81c55510030901d86c020000038000149409040c0e044400c0d98810300070300196850703c41a1003d003000d031007002810b005246006d8481e240540a0305c041d0351034000100380ca6421102d817038070002000f602c82c50100d2623085200c1d20211107401900e1040400c182d07009503104c0e00110040440c040240074004681000c01030001d00d540b006001021a80c01c1140030035980c6070008000154003640100903c1c0344103e0300c401c0300010b001006014842030560541e420007444030441601c840b8804a00240095440c80510020b801200e0300410b64202034040c103100330003081d00c030031200d100d044080009005500c02c00d001c20b5042002d01d62111b494 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 796695233 1250 796693983 796693991
    0x60201110406020a021e04051302010e2b03090e0708061c080a0f0504080d1d010e22060f0e1005120c06400e0c161a0c0c010e01 56
    0x20520080d107138803980400a02c00e03003039140110505c0d0140c2d807111190180c014001c01c481c1c1400131503200e030a20b038140c0882c080303640c01d090040d032881c0061044159000b1201c00d48050b4006040b40341c40740384030b407104805118070b40401007800c10060342200c1c400c1c0d805031a11842400c1600410039007001000c4940c010401d0759440c0400110710505941e444121810f004c8200024000250360a01641d001100d09102d50058590304680c0046a401102c1216022000a400200046400b55030322038440343c108060b1001d4599004e12000106441c0c0c610000014103143c4502810044080341d0f4000454029480c040c400c2001c1000d01c940300a010803030341e01c3c00d01515001c04030b0b1981d04002c8000d102d0303540070440d00d6010308110041c0309041d005a603510240c802c0c004c00300820000c1e600f11490181d8820801007404081e004409005101000c1407600384a554054042c8018004104441c284500042540501000c400d114086c0f105610000e4886407640b80007800c4907800004909540c1c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 796696483 1250 796695233 796695239
    0x30b030c01140310030210120b09010e01032010090608161d030a151e0903050405090604140106020c1008010521030c0303042004020306010e01050904180c0602011104 73
    0xb9440c0c2c8040e039500d0b01d4075169030310458513051540380ca078000b940020242c480846565030002c8120f4450070103140c2000408000028803202050034021406096002e00050000c6a17584203030388418030916030a07083c80800000170603107602080303d98102013680000c0500920350007400c41540454000d83d1140c0c4030410a40003031003105031642070001c1000c610482c840d40c0d1410721070b041c0907a0b045211071141e40280d43c1220001c0008400c81c29040100c1c0804405d11685801007010841d050b0380e500381003900741400c0114100300a850554419070300c0700780c1c144030340c414607a40d4002c1c200d0f03030050b000400e010710078001c601106601313440400c5055801803003280c2d1580308482d20364001c110040824007503890302d54903520520352807102c40e100100801c0108841d158080b1a40b0649012035041042c8032018041680004d459035400b02c0d0204450b01c4035544140301030106401d001f40045503900d118190702c80c10306080340c2c0c107550303034410b01c18148075280e0240140301d8120b42284646141c01c0c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 796697733 1250 796696483 796696487
    0x70b040308060a120819110604060b010e030f010b091006140a020307051f110712080405070506070b06030607080c1b0709050c0901021527010e0616030b030c01 70
    0x100000c050200c078001041035515107445140241c8100e0104000d1201d6504020566070081e070b60744840c00300c0d4200b0126200b40f00e2641c0f00403640a9000800c00740d103950347c03810090201956146e0400010b0010300b45540d800700080c0b02c0c003110801c000505d04200394140100b10000803d40038030b1481c0d03038508000044d886180075a11f41c462200164484d504074800302d040d44510100a00948500341004880400f580b01200c0d00c4a031440b801c200383ca00200c06000c1d60301442c0805024091110f0700300b852540280c4410b07521620a50941e5801500c41e0005001c03504062000c0e1002003041d000c21030181820003000d80c0200c020706140c0c0083c5400845040030340310b500c10b612010503501034142030040080240a021b042080800e120500d0100b500401941009036040d0043c41140c01448250442c13508a502404940640380204481100300d45030401c062130f01d550f0550760740c8004150404081c8051801011172107003000001c01070410040a0715040780a2600c0394101203c81e901c1c0d40c0e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 796698983 1250 796697733 796697753
    0x1003020418020304060e0313150305040c1514031905010b0306030703081b070311040f0e06010510050702060307090e1501020307060e0c090c0d0f02070507030f2d0c05010507 76
    0x4115000543e907a60359143c6540540601180c030b1200388030100300d156500110b0360051098920041c010421a90040c2e021000d4540c19a00500350310002c172810b10904c1d01d10480c1c54800074190400c1d0406650406907074500358011200012804c56807044019620303803c1c040d6038014491410303041d00b141071081c0003945440c00742c800140700c2600080e09280340c10304144c0c01117000740c0803001d0742c61099a0703080180b44484011101031156107051318039201d0058a1040d41040c42c00c0600030f2089a003000244402400c5001c80f090522006000725030059a03480c00442c4507000c203984444055190000c00c00808201800f11080d1003001c8400c1c15550364008250f5084036004400807546a4040a03190b00f49603c4906454002ba1181d042000780d10318036004116041501004100010319020a2400c901808200500c40c0d046030504001144e07015101007402c40c0203900c5001c0c031150303500c5070601c000284200c8e08030f0030001104240501c04190001801000700303080075481c0800f6a5034418946c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 796700233 1250 796698983 796699019
    0xe010509030d0318080a09030b060d030e120109080f090406050a0803030c03040c05040c0e0907020f030d11040b0a03060e0606040b1e0c030d06030b18060f0c0f160210030204 76
    0x1580c503044c900c90b9030580e46140c1c0103a604550003a41c1c0f44980b4100810000640c0810380704084030760042050b504140d4031001c0400e030542d54140350706201004000045035010000d044070741d00d072001407011503c3c0500078003101500501ca40e50340e10944003032005540690340704034407900c0701300c0c0d04019003034001c0300701da6000c1c04100e0b50b42e6883c0c2c0c03146040c1c0a95a0700d50442a0040d190144241380309404c10089014144111011070b075a6a44400490f03030740e14103503e14522a0400d00080065000e190403544c1d80007408420141803588500e10708a03150005010390380000d403600c408000350b160001c02c45800c1101500c03039a2810b4103022007040d180c4541c80510303414015150754003294517403117001d450001c00054280ea0356015540d02401c00303460f06020560360341034060003180500015040f00d1044008440161000d582c0701914501d0340c840091040611610401c00207010842c00801004040380300301041402c3c8400c1c0c01840310003080344808005043c410001484400c0f00d80101c0b20003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 796701483 1250 796700233 796700237
    0x20a06050a08011413050c031b18010c0c05030a080a090b090d141203010605040e0c0c0a14010e16060201180c1518031a0a051302270405010c0e010509030d 68
    0x2511000441d50110400040c200000c6c039041c1171110484815000354010100188405401c54280d0310321919445140362801c1020126040c0c041c4075402005000c0840e802040e00c84600c95981001c01d05001204c04200c0d2950000900918500d40102c0340b440540200044a810050f070000454200e00c00f8a02c06031501b0102003c6401c0a1310410400d10f09044900070280c495944034400782042e0810300a0400c04589140050000300121040e2856503682200070046d4450588410300d40c0f0603840d8540106540f03031841c42c4440c0da0208900403400d050303030300c844d4003d40c90000024211000340221102180a54961401051042c44010280d40c2c88291924910200a809031b030012041030242080c003001d0711000042c065072000c003046810b02c64801641540d039603c0040200c4400b15038036040be01034651980e0150400012034000c01044000c0703031420140070f20308280407000031038040b14240c1d182d001c0084005d038055400c010240d07080c04c050341003810880c00030361510512142602 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 796702733 1250 796701483 796701509
    0x41503060303090308030426031005010311090904080c1f0e15010506030a1404150b01020303040b041205040503010504050c030f030c060115090b0c07030b180d03050705130f03020a06050a0801 84
    0xd00020010b10311043c4d0232400c1d404000c81d9250305160290308101c4080410301c4803107200041c154080d00a15044621141413549000b030160200138400320b002e0710507240c03504244100700ea01441000070f00005a6403401203007510940c0c0c001c400070fa0f4844000c280d99500010305c1c001d040e808841d40c6505491040700c940781c40356141c1503990000c2000903943c00c00300005c0018403003800004610046040364480d403d021040d004801a030b500e100907100100020019000140070600c040d0310300c0480500c1e0b01d01240341581c0c500000b401c3d030b0400d036000d075029000b034942108207180800c41d0407004280500510b0801110b401b4841c1c03a5181441024503501c00d07400682c008510a4120300f01414038001282d4070b8003800a185079480f8240d000880d2040001c4000c159070b0116030510302e80e80b450b008020110402d40e030404601600020706010248201840020f00107401340d030300040544030703144941d95014654010888020b0190f0b0040d02845801c00110007007540c00741c0e03134034190755060013042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 796703983 1250 796702733 796702741
    0xb040b0d0b070203093f060c0705010902090406020c06090105061302090d1e170f18010c140321160c050a151d2e060803030a0204150306030309030803 66
    0x213411031040d119030715808194141002450381c0740e03044038507039000b401804100c3c07181040c2c000003801d401c0008254295010b10002540d906560004051042c4600004110f4058981c0072564100c81a6400c0718a640c000c190703e82c504408102665000746260b00901c1079013070120102d0a00403d19a0409050b90001500380b001c0c2c5603031549011050340002501140040502c604024500d140c800701d07840048030400d9117152400b0825561441200c1011900d080d40b00781d03115007803c5000e81610705101c0c03801c205101140015204000d100200320203155110821a2845814849041c0c110841a000001d00200d001000a0406111a1400c2480c0380070030742e003081403428158020003891800018260311590f45281c200307161003212000107945500750029a01c7e00c80100c505c191a04107045e4002a01c0c1b503800310420785841803130581c005945502d515065095a0084a04022840e0001402c000300401d1119940709078045150400823141940d070b00501d00c4d2011700c005072203a60301002103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 796705233 1250 796703983 796703987
    0x100909050c0711012f03073f050a110f01151403060c07020d02031203070f080601050913051801020409020a170f010e041403030f15030109110409030504030503030112060b040b0d0b07 80
    0x4811040d0000940d030b184100c01d00707460f0031010b00780d204146002034519450700d07529540c0d1001d00003882c1309d44a16090031030000c0115607410b000b50078400e25104560103005010000c0c4500c000494511112941141c01c04044000c14801007913254000e034030110401607207010300c40070b44a036144e048440d0301605510f400001d151921411062803810170000c2031000b219044010081c40c525142c4640d03003180d5440c401034a59006005640d82c000a041194610300c116940c0003e030300880724881d2041c00b100000c030700d500726001a0040c0701c01640c00903046015a420060a014064040d4100401c901c1c14411a0080709410300c50389803d180d400000ca1b081000524550480e40111412281c880c50a40581240c9910030340d0005102d28030b074200000300d418180180d2080b50380240a030010080e10070240702c01400501000d5081000c14007010000030401e0000718001c095000c0003038a14621030a10404951018641034821443c2c04080c00b030f00e0310fa02e20300d014800c0e000319840f489651400b0007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 796706483 1250 796705233 796705237
    0x3170408031b01230108100b0904020409172b0207032a061a0411090109270207031206141e0118060f020f030405010905100909050c0711012f03 63
    0x1356a034501c01e400f10803440e6030f42080d005040b0782c10b103011240c1c1282c1d04010740044980d0000410740001c056800940903041540022680500c5070003040394140c07044012004076001000b01405104860564190781c10000440d00b142d011002c40443c503107412658080d0902c0740300c10003109038802d01c2030221607a4004c40012011150001401d010340c400e004001044c00201e00a500d00c101d10345034548402150b282d083e150700050607101c5030034640c1403000300e491401c140c55400c006003c2c810b0800e03040d492a4000f03001a2446901e88038060b0300c001034a1416110f49400880400c1c420041e90702c0203944008510031503466481410114405500040350b10014011191100b140484800100ca030780c442806010445d0719401d480039200140c1c01c6c2501c0b44100d1160358001880e0240a0005d8544101e0204242019050010080c4c0c1d0b40c0c1c0d60704058800842d4007c60840b400303da0750040c0003510305028800c42003480c1c0300d146070980e100040044030040c0700300f070360505000300b56800f803104c2082 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 796707733 1250 796706483 796706501
    0x1150818192402220612021305040c031d031207081305073f0308090a0f0501051602030a09230d06020706110c0a060203060619080103170408031b01 65
    0xb42d80048901e840c218201a40c040d104680d0005150000819400c5200400900361559903a0305401a2015507818001c1d4010414200940401110000c0d4a56552060807503d007817640b4082100020002d240761210882d50100100d030f0020801c008440481c0c80310603901108908000c0015100d540861880e29030740e800007002c0784078140022404039072010301460600040a1031400b040b00b0301c10140c0c002c9c4a00321b0854002040f505d808000240140d4480f03a0000c0c3d0301303044801c00700858541f580720b60481103040e2641e03591041800840390300103039801d000c44800e0005501d4603a06030710052030240b091181c0000e40800c0e08614a007911410010007074440f0050542c07600c0c0d0a80e0130301030000c0d84851000c442032032400019100c14100d40f016651a0300e019005800c0d6140d41d0340b5400e000e5400101029802101007084448a20803540103040b450715668484803158107524000c59103c6000680540d004000c1c4803c2041150000031a69140c2c9107980e0b000b085040051510302603c1e00f01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 796708983 1250 796707733 796707773
    0x30c09030218040b2a0304020f090a0902010f03050c07030c03020c030d0201140106090806070f03060510080708060306060f01120f020f130f1a090a0e0115081819 71
    0xd141090010700c03402030b25004500801c41e8051039107540e8124082d0881c20090000702030a0301042c1a40e82d40b100c3d000d180d0290000c0c001090908480f000248203403000c6640c0c456007948d4070440000d55901501004001c900782c1801c02890801e65003402450260a0f001030401441d2094041018401d200e40359000c20007500b129400d04807014040c2c080c003103e040b0000b88a500b64000600c01d0b1107425001c04444c052030181c017890311500c3c011200e15002030710f201c090540b103000000d915125807140c5204400c0d43e82d0790041c3c0d401c012200520311100a080c1072312940c000814000c45907a500e28000040d03109081504000303034010420783c05007950f003d907070683d0b0f40f011a031365409030402801000300701d182c00f44012045490304040c9500144a001d02c040e00900246151041c14004c8010200d0300c07401862059501c1d03481e00340e10000002600b041d1158005c041d10301c0034071900040c0e91500b254805042c00c551002900000b541c4100480341d036242c2e40ad10b1256503040c03299105030111054400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 796710233 1250 796708983 796708999
    0x1b0c0312030e010b06190513080304060f081e13020103140108160905100509060f03060a0209040e06010e0705070f05061e15030714011704260316030c090302 69
    0xd080050000c1016400010082d424a540b0224034030f040000c0b1120041314000141c0c0c4031001150450b010703002490400c01d0842e0f100130110306850200003800c020207070f9695585440740c401c5401040c440014200000825141d05183c10702d00380d508100da4080c00307281a100002c1c1d000c2c001200500120445000c0b15440840045455500803500c0d004081044287c03440d415503802c1c09404131002100c40c1d070010010795106215038070b0702c3c4904d142c00810052244200885400c0004d041c0304007520400c042c0c0b1303400104080270b8203043c010b450030a07107030b500505800d41c1351400c20260408010300b45420040000b80d26020003107903568504030250400110740e2280b03460180038030810000c1085c0700102c9240000070303c0031003600b064100707801005000360035001e00d0f21001c3c10110444400390740c184010041300c604d9043c80e844465100314007401c0c51240301003441c528004644100e040221120344200104094050001508030310076095240004094000380070450f10811160070003503124a0f8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 796711483 1250 796710233 796710263
    0x2409031412041502010518030405010f090506030f070e01020c01050403121b0507060315140907140a02030306040f06051008040602130e0601020d030c12150f060504140108071b0c03 79
    0x210f64030140303980a58008106980302c1b1030220b85084402c1c00000c0701540100400e04c05540701300080318003c80d050801507843c544800026400d9001100e000c0381301c0e03201008000040e90b2100103400004003c0c000342c504d6001c1d03940002c01512581c0400342040d01079412072a52030b84076540f020010b101100c106e09030445ca601d402500c3e0007032407140300d0003c8c0c141310318810188031090400003140c0c011a40500c0c10f40001090205041006140c0014003500c8540c48000c03070207031030040c520b4100303e07400f40d652440c00c90b0402c005c40392600c2c00c02d00300500d4582c0c103005944400700600c1a00303016013041c0c08d29540c7c40c41c0c80350107480b070031406041d20080304030300083d4132100d1078140b8000d140c03d03001d072031310302d10818021800c4441000c030910000d03541000c241d0786003031264010340c202c032220103445400c180c4030102c0295007022075101c84009040001d04000d407860a5459805020702468540010f091180c4000c0c0701e0305440c4188a80441c01c050280d04005020382468010b50340f01c4910310070005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 796712733 1250 796711483 796711499
    0x51c110a121202070603060509070f030f0614090f1509090a0c1d0a0e071401020309030105090616030605030604060b0105120c0d0b03031213020d0503040f240903141204 74
    0x20b07101c42400c015104a490100e101402801100165080500100103644c1d40c41011216403140040103005d16a451140c00c14540c0a801058013130040d101c1e190340500380d42418401d1501c80103240380a0382042600b84044281c040034a8046003034200d5107008a82c640030840c50411010400c0141405000c035000107900102c0d81800c2c01798030031100b03075510913642d07a00d0b0107003501d048501c0c40030150402c080c184900d00401a0300c0021480600c1224241514640440d00f158026240b4510030391110080001001c0718980c00740c0020410301c0c1c180030461404002c02e039206000340005108945440c00505240d1280050710545040c0800c003001c02d0a2003c1102d400340e201d81000e00d19241404090040b6040000c00c40307005130200543c05c02e40ea9503200c9815003e00002200b2607101141880c0d20002c28010005000030f800c803c0c003d212018070308034943c905103110b007440f049074424400d4540c00c040d40200c40d070000c59410034100d001190300240d07194140701c200034900c2002e40c004940400c01d15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 796713983 1250 796712733 796712753
    0x203030c1921060501110d020c012105040818010f080105131e050723041e0506030a02091e01050d15090608010b12010203040804031104060306091407051c110a12 71
    0x910280c0313500211b03804401407551100c1c04000c100015034031903021a1078030b510078041501480f5480c95081c1d43c00740028440c60540720306440a441c005008034414203d0540e0f8a44080080000d0800d980070b0400080041e1084405105040c031581e000e40019000c180b55401c0100f0800300c0fa01d000f03201c0361924401c01c000700b074143d80c8180058001e458581217540e0380e000d0800c081840d40015401e00d0314280060003244240d524181914004145c00a02901e4040165014948407400942c6032070f411001d212403011001001018030740002c124904590300613084910384034080383c000c601c6881004c12166031030b880d540101c100502d402c01c00202c003a410f40c04602070403001c840e07082c600c01402540318241d020540e0042c0680c1c0701000204005580d44019510b1340078082d0021504c1a0b594585a04a03024520245e0b010b00501c00d0301b1490400a01410006c0c16003190050840300d4851202d92100a094200515250101015011b02d990302113505000302031170610044102c05c1031515002c16 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 796715233 1250 796713983 796713989
    0x604060201091101020d17060604030206032a030c03012606280e0d0f021018140d021207020f03070801060806010b640203030c192106 59
    0x8501c0c848990f0f8096101240c81c29100d55542d0b25011400d0340701c0c081e50343e060b5000d014241c0c014030400c03000005889074130195109032180c00120060010702002400700c210903190440320a6400c20420100c4200307181940d0646000e840e04c0d031075280000418001120307401510455500c01c1004010f60141070380700c0c90413302d500c03c200894060b550395140040c0c4500c40a800220307001004800225846414461251445441210306003805010700c5012510321050701c412800d00e0b41c90103800d000c00101341e50240700003403004001c0b11403d04002501c958922a00c0110300000103881e005650f109423080240d004000c050344c9504e81c0c2c80c504103009021506c01c240e85070281d1400058030703040e07803419600002c551003604d0750080e2040204414880600016950503010129060012980c1c0d0280006076920074007000346610600c01e10b440c10340d000030451400c5500c10010055602c040000781c9600f151603002006103030030780c032a0030b4640ba01c0c40800f0b00181e003405d031408031884466411070021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 796716483 1250 796715233 796715243
    0xc210c05100f180b130827041119050d0603020301110c060f07081902042c09070b041a07080c0115060f1e1218110f0d0b0c0702060406020109 62
    0xa0591925032403010008010005402c20100d0030000399804038612520010030306c034030a04c42c80c181c04000c1707120440c4801c010103503580718803002e002c881f424503115803000eaa404542d150306156085480403018400b040610702001008030307071050441400e400240246500400a00079100030040900300c3d9040743c602c006092207100040b0300780b903c440b100e842c0103c10668880c079a60f50385107056041210220182100300303508101c000b4140400006c3c004900707951640300e0503109040610314030880406840661150003500e410040d941c018011182150581075200383c3e40c08090044c041c0c2e50050020260840000140c01b10460360103600039045d508940729019076480c0c845034101c0760300103401980d42c0421241003810303910a104880200c1014690300e88036a480a10709444c82c01d44014070901d20444884100b410100070075510709244041050303c441103242d0490001401280620340c016050303c07280703400b0503c5c0318110411103140c250080c00c1d11307941d1551908000d00a020001094070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 796717733 1250 796716483 796716491
    0x503030a05091305070927050903070501050703050c160f082a0d140c0a0c1502061f060503041b0f150e0907110f01060303090806070c210c05100f 64
    0x400c803e501e10409010714019503070f0704019401c1072080d007105801000c04414140f070342d80100b80d10760254010725100755a948003031511075000e0f240190950340c010f4012410301d82441d0030408681883c2d000c2e125034807008640710100000b242042580c9040008004e0125040010407265505041240d0045072000d03045c2066265280440c04d034490704440785400c0014401d111140030b03202a8000342c500c0581d18401d40c3c24460f515a5030220704a9a0b5000d01c12030484482c04034222901440040d60008031106420280c688030141e1a43c600b0700d5010701c400b442404400320381484071007007820b1513a0030704e0401220307030076100d01d07001d01c4501161051192000c40030f1003003681d040c031903004603481c1000601020040c1d1204802503449041d01e100300c0d0b480707105192401c42e405d0001d008034001540203449620206080540706810070f14020070642c00d002c1c14607610000121481000e004002a1056517510758401c88412514400000d02c060094410035240c0250b00300f445d030081e00710302c1051101700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 796718983 1250 796717733 796717759
    0x5031008030301050a0303050c2a0a0f0e0103120513030c050a080102090d02060c0a0203011104050a060801030f1212020d0e011a0307030b0601020a02130504031202040b030612070503030a0509 84
    0x1079580c0c4400d00400e07400c80c9410303508000180c00340c2c010b004080052810780703641d000682246c80c951800d61100d84143c00b26a441c0f0019810850740d804003400d4501803c0140c40d06045190303003000c0c010312004002981003018900c0941c42001512040403400440d010f2260303803818280600400d134007a02d803040b61680400038400304140308039501118080c028400c10699074081040c180c10000d000c102c2ca006009221005030380030301c42e003c10001141c0005840c1c6040c003091182c1910560000f5042c04a1752005001050b901342e080c5903100e903c2210281c1000c51110111110180e055042403524008283d0100170b08a54001c480d8201c0450000c1006070900e14000307080700081301c007e5415401c21242840410f604002144d8040011f0044a02001c550380c00310307202d480a00c11560b192540c4070140000c00d0350081d50410488000c41d410b6041c2130408000100030b10021341090f20030304040b0400400c0440900610ac02031400070162500d0710400c11003e0000d03405011031038850918040c02d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 796720233 1250 796718983 796718999
    0x303090509013003030f060603021903050403121a06040603020d0e01020f0a0507050c0a0f030c0603050c0d150816170106030b01123201050f0411100507060c050310 72
    0x503504075568821800580c0e0383d07404a40700c01d1407008401d40c00c00d80c449103c540c0c00042e6010b218000c120590340103070f50780300104499981c121001019001c06044c0410311010943c01811042d905145803800903a10441d00c0040c01c3d1040d02104203500508045000984d194041d4003600c0101c4981e141440a43c2044800034200d11a90001a01d00d10090000c04040f6115001900e555441102118801c2c4820b100044039000c09620001044011510902c1040100b01d01071000300658101401345043c48407046501c1c0c05540300c45020203694411041e4040c000340702c04801408180c0a0b5080010a2003400010300440d005210382503205001c10040300e8014403d450840e500a0008501a401d01c040100e00201510301500d40b9440446100030307041620307101444070107400d07482c690110131500e0602d00755000240420b2041c600041000301182589100300f0100204981103d061411104c00b40d410740a40c02000c0d1919240c00d12220140d9040001540524a03010024141c90360f58088 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 796721483 1250 796720233 796720259
    0x3050a050f270f01151a0403080405040b01021f02030601020d0c08030a05190608060712020c0606060d0e031803070503070305031c0b0607050109021512010b0d02070507030309050901 80
    0x20742407042c0440030480c1d0a00001040000d842c820a00c142c0b62010700300b030034503400d4031007240e0880780381120136100300a04040211283c6c45095000c810718181444d50301ca15403140940c1c07140c540074985450049000d680300b400a40403940301c140c0101d500c07c07000d0004d40000c0d0000c490081c0035110700d103044042503000c0d0010075209944030040501c4c59451444c0c4030702400c0f020b803501000c0403081d82d65811540441c016140900208002400f1900e0080c0004080194407400704100320700c10400004545000b003646540000e083d169242d45150810308000108a01c492401f403030300006c10340c0f40b01c00894a03a18202200304500310f85602e9120b27001c260b104c400c01d00c0001d01c0c551080110420703001c0f84a580144541c0083c0e40007139180110004070302c40c1e9002c030f5011211030355141d0344501185006128040e0b854800c0441904100d0107103c04821000b0602610110160104450b090a000f030740445020b140d001085d2080150380307280280c0ba403442030040714480d048040c0081050358031500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 796722733 1250 796721483 796721491
    0x80f01062a0203121b0c060c0c04240f051206060a030314070b070f020601140a06030b27011d0420120102180103111e1b0a0303050a050f 60
    0x84a882080c030501103a94440200c800100d070140202203d04d8981800030000e040380d1108030440c0304a1441e6003c80c00e050800400350300d8440c440038088038803010000540441008005d880c002003024141400c070100041e4030301700d880740421102c0d01082d605081d03a41d850842d002660f040055910207101592600406c49000350004110035081012902c1500807820000340040f546103400c00d540c80300364075410100c50b10400f00780c00724064603030305034104105070051010704000080c41c04200000f58040c07040b48215010152a802c1d0071440c0d5844040d90403c2030504103070680320095481d0000a0b14100f4803034400b001c60800158280341c04044002482560300c80b040888450340c10301000309c0f03104807440e1640c01605180100c01038042c02d20041400820071801000d030110324000040c01c0c0c8034407440d5400719403014001011454601d181410021540500d101d80b00c071418000002a11002861040b861150103c1c80f000c1c1509035000074060252400140010b680741c140045241c501a6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 796723983 1250 796722733 796722767
    0x19020a0911090d301107030b1f08032b0e0715030e1b03190c050603190504030c0308010e0609160c0209162a02040b0f040c080f0106 58
    0xc42210b50340740050610b040144200041610003050040c04154115880212070b107403075410200c1034809410016107400018500c00900002d403c5a6503d0302c100c0000c0c0001c22141c00e800c0d04001c106003190170301c4000d00701c258200c076240c00c2410420304403260000204511070b01c28200d141e09500711809402c02d071b5005500106412407408007191001c0800301000c00c10199911000d581c6034400b440050700c294003d00319441c0f01440e40f003c02d4144034030081c00d050030030964880c0c4400208205020021514100d03105a01c0343d690151030310348a40c030a40081d07049031800042004040c1c0010748100e030300d806030707031508016a04c648903c00504801d40d80640e002c04800001140141201c0d404240800f82e80351483e280c008035408158000b1040e502c418420f1000c0e04110501c50340080c14140b240c050000c0407001041c0c0a08000c90000d40f071001078026500e414500d42251900809400c061101402c10040b258000700d0040020704169200d00c00450f1410000a005225010351205000c03c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 796725233 1250 796723983 796723987
    0x41a010b19080c07140c1c020a03020907020703080d060e06100e090c1605010605100206060a0e09210712050a0203040e090f0307200114092119020a0911 67
    0x144505403100c0c0c0008183e414414010098100000c0d00800281c0001440e04020076503410301c881084002c418070f0f140c2005c54400c0118400c056618180481d0440703805441c410150f45540c50124140085030700b0140203520700042a030341c07a40041c5d114100f140c03a2260540c03240e889001c20828401140e110342800681080034020340d0749091074a0941002d003266039149804a40d010450520304e60b12005d0381c85940d5102d040000f814581c80b4030340078a01510103403a00b8a0803034002b4244040ca802005051000000052a0304804001804e074400c01e20f4000c3e03222880d06900f40c01c20f40d03c82001194000201001c404505000d14141d8510a07115005507080ca03003000d014500a941c01402d115507403080c0c84d81c500040c40107000070320406028410a07125400b0203644091003203015000c0c80d0410034034622440681c144082a900c0c1850112030512400d0303440708503c0e4051801200703c0d00325003e100303c481045401c00c00c001c4040c034070030b951190480341d41c0c901960460324985007040d460142 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 796726483 1250 796725233 796725277
    0x708030f030403180501210e010c1205010b070c060c03020309130614010305010f1202060d090303140906061003091a07080a0f051005040c050c0a0803011a070512031509041a010b 78
    0x4881f449414403124040020340340811401e40c41c203503210000315001196030161007103590a40c5000340c2d405001852421443d2100f16a00d80d1460300003403140c1810400310881c00c43c1014801c2c421100c0040c8010640c12500009003407903001401144640000840803442492240d40070b406554101c4d110718882108044c5400c8124a44030310480080360320070000c00001d60142d100d88204a5014001d603800140b550b110200300b004040040d2500d14543c0c0301c40c0c20003027103548000026902c3e800510b400f18240e111841d1031000300100c40110280c000f00e000410885585c00341380c8071701c100200c0700d0a02c04103002040507001ca035010b0b0303480c0b00c920201e214280803c2c1401c0e000883d80e07000c50b00e00b40c0d00d000d890b40c0350740d400e0602c000403c90780c1490000c010850141100030004070f4520910502e07283c00c0003541c649a590002c0c1d5000b0000300400f00000d2803450625480d1421540301510402203890249003540700c9413259941d42c0341e9007012000100d8503103000c40c00d81c0c0300003506400c0203e141c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 796727733 1250 796726483 796726517
    0x150503010c1707020705060403051501050607150b01121a01020d0c021c020a1802280206040209040204020903010c05090406080607020d050c1009080c010b0915120708030f030403180501 81
    0xb00041503e02544605400013070f0341c0d1180d030f00400066014401520064486400b104480001070740458401c1c0380502500010074801b0a048801080122000032544030800043e603100c683d010744205400d00d454542140030000b04414a8042401d900f612050320b5800c6054135801012a8040e4000543c1c18190391118500e80d01d848400340000c1c40c03020510b40d614481c034070704d03518000c0040e02c0c2034000c521548090b10340350f18651350000c1050f07010b03071543e40d24000941e500f20084c000391089900c1c0d0003141c25521258100c4e15140c0c0d02400903c244e107403624010b0a5030780403c141070301a91918100043c6c1920103e811401400c003039000e13009000c40c810048503503400040244045024100070368800101d9448cc040480e807080e1901c80d141e48050507540e0031500f404c4841c50017003080d4010040103022042c0301d13200c01c020031102c0b418003020701c0090b0351810209405c1142244000150130324030500d4000518031680c480da44002e003903c14044110300c026054841c5902241201f050001089 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 796728983 1250 796727733 796727777
    0xa03061e0216150e0610031103031c02180406060906080a021201120809041a040e01050f070c0515041412071721070305090c1c0b060a030b0a150503010c 67
    0x100c0601e004513110020800c0c440c18040260f0b0b42c816605880700d420001c100c0244086444c109045000e5418540c1445050403114200180101003580c00030b0a41d2111482c00403100081c10050400c000b10303a107586000e001d01d80d40323000b000c0100c0c902c100061244806d9008903080011007100b000d510380d1030301880d6580300e001e0f80c50440750024103101e805000e0725588200c010344d41c482422000c6d074075010414002201c601c0c55800d00540d0404007005101d132600819650050510714150f00940b4143c1032440c10264001e0043c05449200414030052003a85018034152440300016101040c0c035104800200344215400181400e0340c5907008050480c2c45009003400c030200005040d50402c2482c488000404100c81c0d84002c69501c40c14450442c07810410860204002c3c0d6041d0520000f402032203c0355401c0d820700a1500d00c20b400001c029450b100340c21001140c1c0811128200d00300b41e010000a46440d940c07240d100d64215400042c0c5180500070212181c880b91a005444040300414003551 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 796730233 1250 796728983 796729013
    0x4050403050d050a020703030b04020703020d0f0207030503031008160303020601091d01050a0f1d0601030f140303131b0b0d09050c03150f130804060e0f0a03061e0216 73
    0x1c001c0601511903002e410340030702486244589401079540303c891801030100c2c1c162410031400341c0c2c814400300000a800061540c00d0b02c48904080b04c5554684008a182605a80000303049020100500050240503803054043d00c9440003038a003481600384c80030001602030f10010300142e01c82001041140c00c0342d4880140700501104008090f04034003001802d4a81c02c0c0c0c0c10316129940d070f141c0c0d0b00e894016803040d41000911104001c0c59021540003482c3d80f04410f00014240c02800d04e20359041041d1f04811003504140c14083e2926440c000603880e400c64962a019a4a140c8900315142000492910324090310302074010300c0d0070300b254100322200510f00e0580c100c803944030b070044220095404001c82220795212080704042480c2405000010315406402aa0106c2900041400048904080d5030a59002d403600c080704940840010b0502501131900d640c00130781d03012020050200c103801000b0618030780c2e800c02000c03580c002c2c442d00c12841003103800c240030f01e20f041d016800160001240a01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 796731483 1250 796730233 796730237
    0xc1c0c020118031d030606010203120603011b080a060b0a0c140f10240503061311100305070f0e031f0906112805041a070507080f010b04021804050403 66
    0x41d05910441c0750b4207800030300c0243c022414050080f49101c0e0504060301c07420300b098001e01120b0400300000703960f81c0540d150381700c1500d4281e00040c01c81e0b01c00f5403015145401c1c0e620400112800e1103000750821300d054410b1080c090500da8045170046241d0200c2e840d031001569500d00d1041c1540f0340036a0b0845510264000e0300541c6000c1c04404010425441034920101f00010980c00005100040244c0081801414000c11000f04a2035a01040041d0701024841a5070550746132847d00304403001d8510015a401050415140300142e070607800903204180a8031160050941144151200c040100c1c01640c1075218000304c5d0264410362150f0031121003110301c00304000030950703076540c01d640310b40001d504041001b140512440080300c10009c0c1c81000350b00d031200000c1e50021f00070814412405040d0401840348000d2050b49031100856503540d82040c00d440070f00c0d448620443d00d650510b140e001e450740c00c0c215207045518091085501410740c0d8040346e804201c0500c10312000c0d0034002d1041e01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 796732733 1250 796731483 796731491
    0x3140615060d0e0706030b1207031a19091a130b04080d14090c010305010509040b01051e1e03011d0a060c1b080405212a04020703020106030b0c1c0c0201 67
    0x2528443c1007007030070f000d400c16403008103229011100f800ba66210382a5030742c0703240e40241010008580d07011704c3c1030740303150b41c1141111075603407015080c107032002940101018a40c60401d180084c4030b000903540607000740241103841c8644030042c80311480f0310701d6880900348035900f07404140040d0010004007150f01c0140c0740030030400e45418061055440c101c81c1884d050f0007825480d101580d06215503405401c0c201c1d04014542440d484505c82e100050280500a41c002000d40d031011518190180500000414482c8a44070726800009007014801341e01d4042e40c00c0820200404200071040d00c61720070800c00070300e8060300544030740c800b8000001106d000d0082802d4000d58100109141126140c0079080c042c3d602c924150074403000c0b0481c0445201404100c91000c401040003181103000c0180b440519208004c0c5811a50702c4030741c5e61003040340c1c40b030301c0040d003402059010340065044078001e401c2c505680d0f8404040846134441c1555071110040c03e45030078414001943c2c00314508814a00c0002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 796733983 1250 796732733 796732751
    0x1a0f010512180708060405010f0c020d050901020309091504110a0e0d11030d0203030906090d050d051b0c0a0302011811190909080c0c0102010c0813030c1b03140615060d 74
    0x5802c01c6219041840c1a405c200c00300000d001c1d00b40200c412003c44000104010b1080c1d07400203484407004c04544040040c0091294031980c800c00681d00b848000034414802c506281240803984a103020b8141c0c01a4100134070804080150780036945d01c50210746030051885020f00400c10202d48000044070300c440c80e5011400036803000c0003510800d8410740c0096540c1e040c0300b4100f0b07103410300041006031103034010504204c500d548201a41d0480c46105004501c984602496506202c030a85040300c00d92808a2840d4400c2c0c40014500072207800b82d0002c114050241001c1520694580e50207000f064400010100c1b500340340020003020103a1740701c85900d880d02c0304541d4043d902014000c0d1100e0402066601690324184101c400c201800d0000308080d520b8082d025040ca20f0003420700981c00400c000d11000d150081a0220795982e2040b81103100a401c400b0850b100740650200752407038141c500041e2094400040e107079000c1c4000501000558007030804100460340122041c800c00d5455221003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 796735233 1250 796733983 796734031
    0x302130308070308100807060e091e070e010908060f060f0a03060509010207020a170d0e0418080307030507080907030b1b1b06100311041107080a031a0f010512 70
    0x1504100f48241d03550102c40c10140c05040030032071203421076107980c0c02603601000060340000c0680180541942c82015036074611507200c181a2400a451003441030f45010803000070390142102034080e4007600d44d03894107074440b51680d03500c503030454603107803070a0300d40002c904246000610640c044000402c03003002c241d1660744040913220207407181c00c10380c0c0d0003054060440c80d040000c8406804449070302e0000c042001c0a09a5550700142c803441841760754500005903840300d411030111103d2000c05003154454078506141c0c0340e44102c80c0a00003928080100300742512034580180903002000c000e04046080d43c40700b40c0c000401a005aa421003aa44220180c40304030300681004a11342c200d02c0010003000948034181100185941c010305801c243c1400040c07034454002c1980401070311300241c0140e0069810300244591007018002100c0400e105a031168142c10482040c54252421910003590300240000740038540c100501042085c042100f40c0e061903840d007940603903050a541c6104070640b1070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 796736483 1250 796735233 796735237
    0x902030a08071a1501050d0c020c06040605071502030408070308310201020601053a0605180f01060b0304020603060d14031e031b030705070606090c110d0f0302130308 73
    0x229040d00070048a011a0780900ca407484d4403c00a070310b00c04001c0d00301d07000200035110b41c16004451b0395942c1501401c8074802c10448420a0340075009a81e1240c490f44094810341040710115403003400100040382c008410b000303481c003442e4820750540c20681c81d950281d55210004240c02490f42029070a400c00040992044550001001045440c0710041c000242080016003003107010303a042c05c01440384c009080f20b001c0e04041d4212820030408414030781807100d00f405480003400450500c400d1000d11004105c4142c0c7c0420064101d80781640c0501649081e504a0b10520f10000402d200040241c24000015648564020402c811100c1e0782c0da910308160189041c011070684c40810404002e0700da803071040d111000326404040c00d51401c248020480c06105100c4800300d00c004c80400c0e01e9070b014600755070651b54424170034402280c8444600d002080c10028a8001544540001501d2030000c40c8518003681c9a9460400310550100203070301035480003000070703213400d1250400800700e041070300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 796737733 1250 796736483 796736497
    0x1103030403030603020324010b0a03020403080f0c060f0106020d0f110a05010b1c020319080d06090c0e010804031d0a0314060105012606090c04080109050d09060905030307060902030a08 81
    0x90010300f903400d600500d4900380101e01c11101e141c3c01c1020380c1991b5080c1e00701290440342136055165440101c0d00c0300b00e01038020356100911100020402d451042d64000140105000e840100c0700039a0301c076040c429003100b080c400d034000743c0c2001d03450001c00b9118040000100c80c1c1410022106091030040c07615141841c002a139607a50f5a2400f41d00301c1c94440240700207003c48440001081046c0d40000f0744070088a0480d00151550810705800c0064085c280c0b04d0101000e030b02009000e40d00c081c51005821442c10350380000d0540070f1030f01c006d58011081580142e03096910b01d0001c2c0f600000410080c0411700c0455800750043c8000400211880e90601450344114084c2c2110f502d008009440c2000c0c007100c2e4149000e09846108410181071190780e8040d408a6049015841f900b1680040b0300c62038000b98915400c1010b00014444000350007134401c0130769598010841c2d5551411a40c2d041a4040c07264035810400ca8640421807a4003c2003e90340010280e0b070044059070f85114041e40030b14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 796738983 1250 796737733 796737737
    0x9081009050c0a06050412020f0d0f030912110f030f03040303020c090a0905030d0f020d0c1e0807140c1203010f08010c050405013005191a06191103030403 68
    0x803038040c1046414064140038100581d02e0014044c14048060320500983c040c0102d018006000d0400f03554405180d5400700c60081d24030410b06c0000e041c0341602024000041d00460030943d40050280544000440070f81e400294040b500340606041142002740d03c03070280c0c0d1501c0b070616642c40c8900144000c0000b5842038004142c4688544d0030300443d110028442c1e4440d038940184940456030110440d8030507030762070000140006080441800900402c07140c82c915a240165003803042ea0402c00013022803400c1007240c0341ea121401412a04200202c0d442c2002404644581e40c0a900c3c0324040c18a022a890a44214003400362649500f034200740d00a811046007030074100071a000a21582188030001e1a01e28a440e0030040040c0c440c2d01c1002c15a8030110220300c240321424824007010743d1351f1050000900c01414541071101d054140070b00c2c4007880c60314111107841114041707501c0340d14034007014021a0404070051807402582c0c440001e00ba0078000300d000c4144c100f50080c0001c5101d80e21039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 796740233 1250 796738983 796738991
    0xc0e100504030501060e0f0414030f040609030605251211070b0f010e04110d0303020d0501030501150f1505030c160c06111f0c050c010603140c010504180c090810 71
    0x600f00f50b03003520042c0e03201c403588175942018014242e0f81502c09641c047c1c1c0082000200300c2c24100003600c0c40c030070041d581620040c0400e0201c3c156074001d4500301107902404041c00540c60f41400300d044045d000a0805130040710610350180745000c0e5240c0d4400c2e4150b42000035205035140c0c0c00f014aa03204010880e80b04606204120000c00c0d0111005d000d0404541d01c0006440c05a451441301481014198401c3c55060b00c07040170948241c04444401c0e4020100f0300a5582d03d00d0520302034000420550300311080d014010480805d0003c01d0b50031250110b0074100b410040d01800c3d00d06a0003c0e010b90070708201007102000200900d0b400210345881045442d47c8c80749090f0004041c01c0c81007010301c52980196504458081120300c801c814407815580010709003050754020303117080c456134110944075400c060b80042400f00103001e40c0b405000312020344481044c4400116000c0c86240902c1903c1204541034000d0030347c7da6400030795a45924102004401e440b020040d00c3d0101400c84d44401c2a19 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 796741483 1250 796740233 796740239
    0x115150c0b0108010e250504090c03140606120f1002130e070c05011406011d041d0105100b0304020603040f060605040501090207050c120a03030509011d071d190c0e100504 75
    0xb00300a44085040d0020303800c002e07000c4400040c106c00025120f120700c1151651800000c0c04013091120000716844001c500340a407211840355140c00c001c442c030a21400400204064850004c540108040c01d128042d03d40b110074076a081d0021340010b043e42c1e44868440c4400300740e0700001e040b07590240310700f51a48003006600d4680682540c5004071042903d40f0880300380006a60005a820086412219801c0101c200700c0003182c002e01c07000528140003294441c0b000000c40042d440680107015041d070725103000d9281d40200a49210545000b03400800402c0020003040800806511051081202056880e6a007000805840d001e0304004039480c1d000410b881001001c102100c80c1d0942501c641400c1a4666411030f1200706014025041c1038a480000d0880c0c04207510900080104a010f45074140b01a11401d0365150a400313903da040c100f802200b05607510840c1e40c1c0c1d10641d2240e41500d1200a40364680020b040c014101009115000406c030429540345600c05d01c400000390f0b0f8031900e0358a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 796742733 1250 796741483 796741511
    0x10b0616060f02040f21050607171803032e030c0e0901060e0105041d0601060f0909111614150a0f02091e01090803030403120e0115150c0b010801 64
    0x3201c42c40c564801c1d01c10841000030384203000091040341c100a1410070040401518151203440c00e140080c0305000c0c00040000a030780100c056a04000044641d040f02d0b56160200c400c041c01400300c851040d81706100151030420010791034540d10151408102541d038a075426544100da01d50000ca43e400301341c0c0014003107000300550b180c0c0d2080100000f4040d551a019a00508010601920307004a0319181c10704c0410322031904000104404008071415582d561400801c00014842000300040b021100018444901e004c0d00300c69003000c0041c0f61800c0f5450b41702008001d00b403103080340c0355180010b655843d800f050055821103404038218005514100e0221001c40c2e4100700120301c0d0074418008a81651255518160958000c164682030241003800690744122960b10105451100004100805602511403c89810441c605000641c2082c61580c207885001c0b03c0084242000d00c420819142c0540c0000c0310803070035040c50b0f050320a190f100c6081d000b5003600301803070305da4554220402040d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 796743983 1250 796742733 796742741
    0x204050103050a1a0906010302040f090221011a1303080c060a0b010201180b0a110a0f020d0309030e010819020c2107021c110d0b060f0306010f090509010b061606 71
    0xc06219002c12181d00c18181c040720130401c122206000d0006440051150390095045134043c003d240d00741581c4d20f80e1011040043d50089030307440340040d5000b0340d03225071051420516040e140c000300b0442c800c10403115100925000203550f8091210050000408601440700400c84e20800102406891515038a08800d8034100b0300c015045a15107068201108403911060005035801007031442c1c0c5442e440c032000c5c01303480d07440c0107840ca03e080010344140150300401100f0081e48075400b9154282c1e03100318160201d0781a1340300030340408e455442255540d8412901c09074854002d805c4401c040031007600c884220381000783c440301c25a1190f10211001c07000703402051008204200900e2401440c2d1740407480c404c0c10504a0201a810314806104100e0301d00c0080801c160094a01803c40c1349909205011006c1902d006020f80c0561114000c2c60030081061070507500076100c0c42c000c55252a084800425008158010035503968032400d040b5034908004210900d4038102d10304580e940c0b130a00700119 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 796745233 1250 796743983 796743991
    0xa020904240b0a020c0d0f1703041a070e04020a1e020708071a0a180b13170604081818010801020307090602010203010323032802010e0c060717070510020405010305 72
    0x1c01d05000b10002d9a130b0016080315201c100b610714090000852a02c0c648480c500f83d001410412028625072052580b0005184202d010342840002384552400398907200006443d902d0000c0c02c8120446841c3c10250004c1030812080c5c9002406610031b0005404901c2d1481030400058000d0107007006544400c0111901500040322085080641040b042d01a071007001d070200c05001c400b10b1514814101204004000c008000100e40d80300000701192616002e28060b00d000c04003400d80c00188900001074040c45640d0043d2800e04d880f00b80c012200d00c00e07501540c050340c41442e03000d5211010f0b50441c60b850007440c00c1d40000da140d080030300020704000416040b84046a10600041011901d0701419a2140c0005040d41e8464003035010024114031803c00b444000c040b00750022130f502111000d03003203400d101d2035000704290742c0b9080301c075a2640744500102d82d11010070300040d008070b000100d0b050780721203880640e28034194140d907034141402d900400c1e45500d198007090812681d41c05005031680 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 796746483 1250 796745233 796745249
    0xa12050c03092a091b0a0302030115030c1416060603060203040201020c0d051515060310050a05030d09031518030207081c0c060c180306050405011503050304030305030a02090424 78
    0x924a8040b40799003400040724030140c400c0090401181d00300040542c202c0780c101c50131085d81d41d286005071028019500a03c5491004110000e0300a45035200e40b0030194117654a079a400c2400302000c045420680090000365511440c0444550001d40303140f05090046110f600c0142c0c807441e00c0c0c00060b0030305d0000b0010328012000d84080200052011a00e8206080780c64064401616035000b80c6018081000301c054000400000b4040200d0520322420111181150092441c90b280c2c800d06440703d0304c00f007104000c00c0c3c060506100055030b502400040e0106420300113200c4500000200d020341a11506a016800a050a100910090200940c00c07455010a8011100307250802007280b204d480001e004181e84410000d1307018411141e0440daa20780601c40c1d80c0481e1282803e1001340001e40b41140c41d0342c41c022100c07144a0591440b80c00311303908000514101461a1016100c1b0b51008000b004003560812031741816135590b200b020360010001d081c001c5d00d01f02d0110002d1400582d6088000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 796747733 1250 796746483 796746523
    0x1b030703050a030c0302070911030a050a110711031204060c06151512090804062a020f0603070c06090602090102010c02010b0f041a040c0806010906050a090b0a12050c0309 75
    0x450350002d0440881503052801c460b00050a080c101e0900440742c006034052810444080406100035010354084c8240320000c1205231580c55680c400c0342c4403050700340d4001009000c5074000c225645920b07480d9000c040d003a544074004100610540e94800e810500c041145100d00f441030180f1803280b01100107121503c4030400d41049000ac1d8a07100780759191042051425002c040c03403100b42c202600c5250302c0b005e0075440b03035183c42015140898001c280c4015800c00c0c0d07400742c000080c03c880c8000e450380207051014a006142d09004180d40024140300901c842d466420340000c40c5403186448081c05001300580703a25801000a080d200400b42c2d20045a04000c01500316641e48a1608200503040b40c0000307400c41d42d03800c1003281291956406600910b4441d41010180c4c03c540c1d032500c200740c260f07100c210080c2c0340c85059421303014035800d2500040c4901030600c04041c0800003001408040d04081d6074000b0001d00c544180d4a0841f00000310060100a01402a41c2040300215050400707044407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 796748983 1250 796747733 796747739
    0x80606030402041109030a03020c130902060304022b080d0608150105131409010f0606020304060909021303050d0e04061d040609080c1b0f04060806060d0213020c1b0307 74
    0x9181400080c00c040c0c03040c0d64821460811401500417625451341c05810788991120ba0f0501a4a6040392082a405901280d011509034140e500c80c01000b6580200100c0c11a107440d000d11813038000c030101c100d50241c00e90550600e00b040300c40030041d03110f05c034404241ea20b54118a4034800e480e1254403c00303896204240c00220065095000c5041d0b403800d660080a00c10568031060142c07144111400d4498081d606004035410306400038850b62a032502e040c020a55504000c9903170744100e20900c40042d04214051005644d0b5400a01a405071a615031103070903100d880f001e0400038070740c03845001308000038100211410240129001494034400394801418403a020001c807410041005010030340c0ca014140800c170311f2005840198000104541e64600481d49822402e00d4810744e01e8401d8414450407101440c081c00b954042e100604c010386001d0b2500028001d4a4407001400c0381d001b01c0b0350311a490106410703c040c18403800f10308020455142505a1098040140020103001c0d40101e5424 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 796750233 1250 796748983 796748989
    0xc0d080601021c05091c02030c06072d080d090317101205031308060708060301110d200c01060513060b0301060f0c0b0112031116050f04140708090d0806 67
    0x8120800b108844034003030f548030180840d040d11941c0c420307079030140c02a000c6500c03040f036050045c0300d1103100760112903914480208004550043c04401445240980308882a1364001450b58001080411b03808943d92501d80e15108907400c180040e42245a42d03a00d020300303140d84070185909414000d81d078158641080c24545181c88158098031849400c442c01402c0bc0041c10002c64025003201c050085005441e8410705444840c03d0f40e0650014141d4008036200380303018842c0082d0544151b400c240b030092441c450740050402c6201d04049080e8607005080310401c46002040000d0a24000141c1c1c0b40c1850100810035040c4010f0100c030921302030b003c0c00889032440440381542d051303080011030a1003440d01201c3e1190290f00040040390b505000060030341d504401038038003a10981b1500300c8010b40000c00750352808060029009504003c00800c070301d050007108a521101c02802c00328030116958051800107405032000c0c0001280039040040080062140084150fa0f41c64803040c44c0c1080000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 796751483 1250 796750233 796750243
    0x602070f0209070e01230c1c021605010e0913060c080a060b0c0307111c050a120509130b0d02190302180c0d0b0d120918060b160501150b0c0d08060102 66
    0x10b41700b1403004010350446c82d8140400d90304462151411118406514080105018100c0c45050003522030010658822500020b00710144da00607034907a0000b01c03c2800b008420903006e02030f48030f0f1490520001c400725501c0c1c0140c0002c0c0703205481c1c00d2540e08190b0625070445200740d01034040d005042c80002c044010100c200e07102d00b5089141d44000c0d030144030016070b60a41c000107001490030722f01c074268104000810541c0c1c8640c01174241e0041150301070001e4036248500c40e01140d200c3c5011032001100a21380c0d100c1c003001c11001e441d21002e00c0865010502402c0b003100015172800c0b00070340400841c503251038808102c03007050404200034201640351014070b0140070552a1055100c001500032a111580c400c802d041d086900380040c0000e11202410416182c0560f80781010501070072106a542c5010b120304039140060114130300301d4114110850115484403c850b03e5480e8074032251410700c3c0d883e003400645556500035550340d034543d1015280410440d00241441140c4040003850383e00411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 796752733 1250 796751483 796751507
    0x1b0f05010912080309011b021b040506030c010807021e0102120106020a0c030308070e09010e06030705031f0b0d0c0e160e1012090602040b04050a0b12130f0602070f0209070e01 77
    0x24060b6125217520300304034050082d0500002102c0b49040c040c1c091590300107050342011742e2915180300e155081506100540c1c00440384d80c1c0d0141d1000f080081c05521034400030b03034405d51503c199204421210590a2480d003008800c1c8807503074021a81040c5142e00c2d01c29140107150500003000d03c048103a44070500c5c0c080c184006800e20609030005032485006130209524810000c1c6000001c0da124103000d61410302c15107590740079208107100031039907040010340822508040c1c60005092940464490050312010136640d82040c074544041d00011420840080600190b01604040380342c500c00307050007080c0040d40e1070100850002d4412480d12200c400c151034001a00d0a01c2106212088000c0501032112004040b0b80c40054009903e0403c64042d00071381d801181c01d1401e01d9550480c0118a0041482d0351210950072004188801c5a48000b0b9100501c5120482540005078031448100d8102c0c0c103090311030180240c2c08404510700301c02c072180e01c4840c1d400c03c10300034514080002c0403550524 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 796753983 1250 796752733 796752743
    0x60509240c041e08010b030d02100e03130b0405091e070804230c1005030c030c07050a2015070510050a2903010c020312070e0406031b0f05010912 64
    0xc08205580711180c01c86014119811500c03004014514924a205416100b40c403403c2d481d1181e5000545008602d1003001d410a0f0300400d040381c00d804030440105221a1011080d1008020640c6416011000e500c010020203c0d0151150324000900c03e503803400500c0d003807412505081c11455020004c9055402c80c0e9145400b0031950390360b01d0010b0301c00c10780000200150070300410507010200b001801c11004401600d141c0120315150600355500d01040d25500c1c11000e0a20020356112405005010741e03d00810845102c1006a22081e81c4440c14a0380c020407480000c0f6072055504141c44c8520b0311803500300505190a542e520b8650711050a4a010000300d40c4490103e6030380b601c107030805220582c1200e00d80f16807112000c1d03107030840212851454000d50070314064413a43c500110617038900307508004211a2580d100502120480802007a0a502544d90280131011860080c6840c01400800444145d41c600748411100341681a62000d410000e4014003407110918461000c800103500c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 796755233 1250 796753983 796754053
    0xa1503050708071e0905040516030605010c021c05031902160b0c0a030c02040e0f0f0105060f0901061103071e020102010e0d090e060303190822031e020106080d030603060509 76
    0x5000c403202030301c0783c1c40187c2c06030403c020711551000041101d0090620343d201082440e50303c0005640005107820043d5122010801d00710031141007100e60052940b00d82c080c2c914068045903010045588266210016413081c8040258400300190701009004c4903d0210705285c503081070785a8680701145d00900f0011720084c00d00c11912070340c020100008201e825120a250240319555482c030444150010940c2050f005c04c1c0e0354100318041305410707080500f01020f903a08042080d0f880070790011800030700d40f108102900100c0d644d01076005501000d81700800d551240c600009080d580e01203080441500521800941141c000f100141155064503400c4103d94492000071304500444000108246891405a43c825401a442e80c4034881400002c5d0002503c00d40346513600064850041c04941e01c5144002c042c5400041c180060701c140c40040b6000d07889081305400c2c8015103c0348004030b07880301401e00070482580562070f80303d40004002d0a803084250300100d10342c408010b105050000b2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 796756483 1250 796755233 796755287
    0x2d0b0103110c16050f0d0305030702161710060b04051003021207050a0801090e030f030901092a06080c22080118021c020f0108070e0a150305070807 65
    0x41d8205005800d124456151a1030702c9604442c0c41d01c94181d09054411807503803000c10213142080d000003d03601c3c0609101010145540c091307a090380042c1030312040d8400c2c010000300610180c5500400742034441800d811002c0c0c50600c040c504241e188245035218144003003841040842c03804d0718100e07281161203403107480746104164028030504100005c80010041000f038103540010081202904503600c406c07480c1c1c0d99110b42012903c4500d0320010302c0d0010000484c007030100d0b90255810100083c0001043c03a4256030752898000c5001d00c01085850b40c82c0c0c5d808040c0340e0800c94100420840c207140e8164a809500b0407841d1103184100300d020007054001c0c0c500b821614803003a01911140000700280d0082d86091135005404540880c4640c41801d24061204600c0ca030002d905c0d0381c00b6001c480e12100c5c60b4010740e4191801004801005002c00f5141e40d580c1d1340b00c0c1580001c1110341401d00448581074001001c2e00c0c401003000c002e0110030824400d070541c0c0030701103080410000e0f00150030340312 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 796757733 1250 796756483 796756487
    0xe04031d01090e011d0c0703090504020d0b0603070c03110a0515180f01050105150702010813140d0c1a0c0a030903201e060112080705030405061c2d0b01 67
    0xb10a420003010303905030b0700000c1140101d24420b445140302c2800b16425076510f03003e10003210301c181200200040c4402008000e81e01300f90300a059510142c4c44040b40621a14012034000e4100b00c034180e0010341c40c107040c9800e15820003c100ca000c1204800703812281d00603140d0f15a1103c2800d4181109008940060700760420b03072440c84241e440d20015034294110500c440c42c00303081e0a0017103611400c160b05290543c400c02d4001c40d510b903541a100c0c0810340e95002c0c0c03040c03500ca407000004c2d9000904410a804003003024000358003942e100380c40360704444510b0b00300301201c060001a032180681000b0144103030400c51a080e01c0c2a8551840d010614445516045445030701c1d80c0c0c003641c1500035400320480c80b9640407a4481c41c540c584008222426400f8102ca9520f2000b0303c86c95405a6002c00c98902142c0540300a080c40ca0141d03089070320b03150355100418030303e07441202c40c41c0101c60814000024181c2c40e00856200034600c0300000d00d00c5135038407110045820105102c0224594500312102564 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 796758983 1250 796757733 796757747
    0x105094209240c0706020d0f0f0806010e12032205010c150e01110c010c030507080105041805030703050318070e0a0c0e0918010b010315061b0b0109090c0e04031d01 72
    0x70b14110920b6032034441c900a9240c0d503039058013542d009801101d062540061003080d6114400703c15a03610207203c400342e0002c1d950104080d21590400c0249100011a0744450300d448154101d030394000c44d940d25880714201a402000041c01d00041001ca400300303c1c607a40103c0410049821515454040022080e124000e01c50462812400d50910450500043e03001d0041c240500400d03000b44030480340300d03a088013242c2040b03c0b4070380030484840040c0014201588841e4000f21540a902c49405c580c3d00d0b10303850740d007113044114001240001000f00c03030088040c2c440600c1d07070080d004000c01400c00c103a166808400801010641c0e0751809490fa11503c15069060303050b00142c000c580324280352261411509189004904960816070300207050351103071154800d12250202d10800860610750120742083c1500d00001013001c500d841c04000c1000c08100c00c1c000c0c4400303440040c0401c41481c010300c2a00e00ea9100e0041081d0000401c40400c1d005900407480d000320003489a407109010740180d90300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 796760233 1250 796758983 796759039
    0xf0908092b030203030f06040b03071401020f01020d0902031c0203070f0f0b13060b10050304140f030c010b1507110f120f1b150f090105094209 63
    0x9001071492600905030007000035070240c3d2000c80290504d59560041c0403c1c1c500c0000000d401d6401400c08022100c0b000114800704a0144151034840414000c2142660042508400c90543d41c035a501c04602d0104803030700003520341d5504014198001d0a01035100d01400c6005040241050121020010740820304123034682e000e0010615402c0000001c9094100e80604031079407890000c14031940c1c03400618603c41003820b55119461503885558039409a261546610010b200d000400d0307141c5101031000d4090b0880e907000014049101408100007144003810007100081c4c1001080301080d6030207002c101d004402e0382e2098010780b028000c60780110018008421074090b100380d91105540100e003640d010036000c078402450b80c0c5031004000320344113040310070f50350365800b0062114181540b0000d0b010b14441414107a0030841c1041c080380040700d080c450358840581e2130503646d01310a012180000582d843c02c10b00c003140300105110320910300c40c8401203441840a1003484071501000c000e40028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 796761483 1250 796760233 796760299
    0x2010e1206190209240427050a02040b04090207031806120608070509040f060b030a24112d0d06060f02010c020307240501030809040f090809 62
    0x20303a80c2044054580e80181c071503545805900c1c5a0201c064881e000340c0d07640070300c02041103804000d01c0c03003000741d2200f101e03544584141c0306020000d441c1c1500c9810080c0c90b02e41260786088020a20740c46406ca600041a50503618030522080c0428038040003074505a802d9400016035803100c5045c191900100b01010b1050300d128800301080c0c5c0c940c00031001c0d041d066010700912107203846e811401e8494000b802380540241c203500c000f030003041c001626240c02c0b07400b4160024185074014003123824142811000e6807030310010b003003545565100d007103038801d6801c101c0020480514a080340103014410101c1c1c81001c000700486d00c1c4950101c0c0250105524000d0040c19961505801000042e002c5440780c44081003201d0303110103110b0b006000780c4195900ca44e01643c50140180d50784000c030382c1d10704c20080c2444209010011010818410079011310302540c58039840b4142034003008180c0d8114952a01c00b42e00f00741102c3e0000d41258190b139000301c002c54081503408002828000240711181c40900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 796762589 1106 796761483 796761499
    0x50d0309170307050901110a0201120f240e010f0e160309080310030b0c090a0e06011e08090106171902060d09230d021902010e 56
    0x100503216010410500c1220304144081c0d410803500c6802144c40060101138540e0441600e94032854094000e000c01407859000901501c1180c0340c0c080e40c80d40311011410008100e400c900c61804621090f80491000d1010002e00803a03e8030500380118041400404d600d0a60401c2d00150b40d190001032690b03440304540c4002444079650031307004055032030071801c00040c0500002d50040d90200303c2903030824110b042c102e4019901a0856001b44d40410540c8800d403655114070003201c102101c40f840c180e031340400503206411401c8a030280b0540854583c1461038020103400c0c01054800020410140c03500e04400308050001d0300d0b4403403948400d0201c101d003503405007445412403010304240e040084e40c2469005541802008440e002642900c0010780310618031441907034158500204107081c00848081d4550340c031850003c007228204440d4038213590060300d40d110030a81c00b4250340 = true := by decide +kernel

theorem cover : BRFrame.Cov 796582733 796762589 := by
  have h0 := BRFrame.cov_init 796582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 796582733 ≤ n) (h2 : n < 796762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
