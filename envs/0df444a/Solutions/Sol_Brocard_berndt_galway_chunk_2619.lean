-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2619
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:15:04.259002+00:00
-- url     : https://prove2.me/submissions/55b322da-0149-46b1-b4bd-553105cc20ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 470863309 ≤ n < 471043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 470864559 1250 470863309 470863319
    0xf051c110409031e03020c03300108031801030b10050306060d050103050a06050c0306060711010c0506090f0115030c031b120308042f0d03142d03010b030403080916 72
    0x10046440300d268543d00c1314400441c58811403c030f00441c55000c0482d230040003544136505001204403510710f84241ca00c80218070700c0715210710b105000c0c0d0120110f03074004100c42c409460700b01000c8110b80b5003843c0c1007100b654070308001540c00b0641d00c14101806000004514035407240c208440d0f030b038469514140030b6540d403407420341c0c0d40c0c4070000d80680d002c501c3d04c00494441903441084034040c0000a10369810b081d0180c80b14406602c1c0301c4100e5040c003940008510010f0003e00c5072511981e2420041c100300c0100081003820340e0030b2a10306003c0d1800c2c144051000405280301c001c00e480e007056107010032020b141c0201c0511405904003200368050703d00d28108140d406001d0310722651080c0750b20181040c0c20f000b0085034140c0700c483d0070301d840c040001400080c00c16406a100c1640649000c2c1c401403000b503490f500591004c0311031065080c2e05205032901e20540c2c103200c2c01c000d007802c102502d90342c500543c482c52800b0107080101000800000704510101c10000007401c40521407005c0c4c030b06940c2e5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 470865809 1250 470864559 470864567
    0x40c050415050a02120310031401090f030f020f0a0b010603024504050402030c13021b0a0b0f010b1204060b030607092108031306090c06050a02070f051c11040903 71
    0x6140d100300611419441401c1d440c5c5042c203481c012451100e1507880c0900b99600c0c000c551a01c203030703c00310070340d40c81d490040480c00840d880703201c16019450709003c0c2c2200c804024184590300d2204100e940c00f0114007030000d400400704504480942c50300503140c1c0a40200c95003078029103002d0060140c4117449481c2c0700294208100401002e550340c91044400f202d0a00050703940444000e5030503006040c0c9024113090540e01501c2101c0031000c0149402085200800b03904500c909141c1d5076404051000d0410000088041d00325482c00c1c10052550b144c100ea0400074410407081d6022000003401040400003c1d8000c4105150f0080a881081c94011030003480c00c5a00d204120f0030100c0000d428545610303c8042c54140b41d0007400c154951360b20580180c44034142408100c41c520341d40c549200120303008444180241c10039903100c43c1e80c0c0490910007482c00703506400c01e001040031442d0400560307541000c9019185280c801c00081c501140c18101c480722501242c03550414180070002041582c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 470867059 1250 470865809 470865817
    0xa09021201171903050906070b0604050c03060d14070906060f120b030c040b0f0d050601230a0521030a05130812040e0a0e100504021002011a040c05041505 68
    0x1500e90009000d0303a9800701c10a4644102c0d04850342900464514402c210090240b28155402418454a4045e206003c034046a10015050310740ca109601844a18070b040e0007081e800c220800030660860403d04001f5103c00c0f40010000c1490140c3c00100301202d02c1400035000a00c64041c0030088241c0e2840d002d042c1d02030029000c80000e18800e0042e201707004910500540280281c000d0070032200e40c0741404003e02c2408141c55004404411548a45d80c03070341200b4520354410009080389501d0195408280654803258480c03404c0c810078064525105c01c1c0e4072004803001242c040582c00340c140326200080e189840342c4012800001401140580c010005100380300402c05d0380c4c0d0500da61142d070300740c54010001c0407030075800c030400003084104042c07034009400c4401c14800082d60201c41091a1805018186814a140d229000c201c15441c000304402c045141c5130009015031003581004034012690440c0f03142c070641e61200042e0341c2c54860701c2618040c1c240500b4141a54102190240940d04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 470868309 1250 470867059 470867077
    0x12092a091f09110912010c1b11041e05070206010f0e16080414032a010b03060720011d070b0f070303110c16050406090902030a080a0903020a0902 64
    0x20364100854241c1c461901c0a045125a0120707030440c0314140502c1c04003420030601c240340f40070000c2c8a04082a81c0342c1032075421400001e800010307841041079003d40114080414980340c050500b15000203d1078225000200c11811900040e2210074011820380a04034403968042061603d000c000c203090b00010400c0c1070b51046084001180d40c1c91740300901b040e1007140c482040c0b8244000d00003100e401015040d400511a118560018450300035180ca10b0300048031011190019505c008800b81420b200090000300040c02440080d00d0240441d03619400a080502005801d40f40501c80042d041c816000c102e41c0d94009024012400b680c0306185000041c4146c0e0600400100081f0b0008080c03c0751400c10352844024103084071510141d00408050f01c40d41402c00003008800c0480c00305000d0100d5440c801144c0c3c201171800c00c018801111666040400411315003145540503a60000b681000300d680311281030750700d02078504103d60700030180e84000d4001c40502e402180d031690740d40241079151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 470869559 1250 470868309 470868319
    0x1060e0112090f050105040308011203052205030a080d0c09081b130f02040302130608060c0d15080105160207180504050307020603090a060b0a0308030403080901150f0501080f0c12092a 81
    0x203604c58414410310048bc00b002800b00360104011400e03c91301051141441c00407001040010790b403035011038180401540d04541c00c000000300c0c20925840d07842055811017882c50b102134268180490746660751468a602410305501300c841643e540e4400010f1014498141c0e0207102c00141603000101075005800120310440c111028920640014410716007142d03030b00c2000b030045807030744c94192075039034801c0040008158891588510303042e1000207a600508845000040f10325002c4420b9110100c2804d29404641042d00d040044104861102a0300105240c00040540322460302a1540c41a1600250014004400c0040d007590110f180c0700c0c0c00c0e015400501000c403a03d4204070303034001d99003c01080e4240500c0420702007803140e0700f503552141c450783c00083d07a0110074179844848a282ea02998122207000010302503540d0003500c1940181010b02200d0140c03c020100d00414000c001820310903240714000941d044104200016908848072690650b0f18402e459135405081e6a821a0b0700403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 470870809 1250 470869559 470869561
    0x206060402030f011518030c0e06040c0503011e1205070e18030d02030a090c0f06031a030a0f0206040b072f18060d0b240901060e0112090f050105040308 67
    0x3800e140c000c40f4425a1202100003107682004081300d140001070811904100001c81c2011501da5459a01c2d00071714011000c98035040d01c2c003100e046007000024203c0c1d0045041000400c2100d410800380c074195060144401e050b030400110308080010700d036000d4000d5090005450b424403d0100b0b070328094030780300030011010b5990326642ca1201001040c0c001c0382503104015112041e1015805140c00140880000c035103280c150701c0b01452010550400c0d00c82c44c42000381049440c0d05403240c07104002e0140211102d00041400082e124100600098280b4000b030f40301400315030b115030440d4040c01004d4540c03900c4003080c0c14041800030750000d0404544402c0101d5400d58485208100f001e40b10040900ca440c111442c54000b010402a05454020300306c96502c100050612400c03510a0804420414222009200c42c8420442d082c5009002d4980e000043c0401c81e44810204406a0282003014485003444030140c000c1c0300b8880041c101d6240310344603208006042d00b06e01d0245001e96155105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 470872059 1250 470870809 470870821
    0xc080301090506120304060f0c030e04020a0809190507151707020609010f0b030607030f0b03030a050706060608060105031b0d05090a06140106121104170303090f030a0842010206 78
    0x9031b486140100c4e07010449001110040c00e10a00401030b480b88a440c14100c0001218082016a0400e401448c08580a0b0040119015040080c2400401a000380089000f941d440c0d2035100d046d1800362820350310780d80c41c8186c64240540d1141424441c0589450058942250008c1d01c841094803484440d500305045103e030102280143d80c0c0c502d5000300580225211800c0c10380080100700c1c0c0784610365403950010442035038244060700c44640c10f5111641c0e00c2d0160b1a00030115030941e0070150911910000b8048141d9226082d01d03400103601e988128101e0200e0038002c0380d400b61210ba01001d07418001001003a80003c101c80002600c80c00c01031155514450100c20380c894240110030020300d0078580003ca10180c6e40183d0f9900c101c14980302d2400e03450758441031005050301c408500c80e500010070f125104100b044400005c0ca4100082c505110101000400c01d10380904061100c2042c0c00f404070503400d0f4258031b800c0c094100005540e1340f5000a50030007191000311507903400b500510340010344e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 470873309 1250 470872059 470872063
    0xc06090506180112150825030b240a14011205012d030b07170a06050d0b1e011e06020a0f1407030803040b0402090105060a0c020f010c08030109050612 66
    0x1580e000c2e5055111022101001144d0301d9260048900b000798a0312206505140e40c00c14010241841d030713020b0700c030b00e2030344100e0300c0d101602d40d40183c0700003407500c04208080317442102e255810103405020206644800070070b040002508076017880d03005489142c0041c2c0000030f1240007030129070a0302c0d05c0441144030321200c0d085840c00d2080010a0031085c03441003001c05040328031140c0300c103620214550213480703449121442008469500202c3c005248044600b5440d40419501c000a40c0050003454209400b20340484103801c0000c000d009103202152414000c0a12a981c96115000c0f0004030760b07540c2400002c04441c1c95450a4030003604034003043c402d101068a0800b41d40140b82c1c505004025038480c2c09111038a88081c40c14000c0b60400310010341d000300158007460150598013010308040c01000b803081c106a10451007030500704004803060760495441c480300c90301103a11181d41600400140e84400301c0c02402400c1c440000004131701041e81d507000c28013499064416904002020f10016 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 470874559 1250 470873309 470873317
    0x1b030105060901151211090f060f040501080406090609030e0a0906050102070e041b1205010b062a0c0301110309011b09090b0319030f0225030807020415030c06090506 73
    0x290b0003050000c010300080304001d48541040e00380d89000c61035810000a4402140c000440034621004001904151894800e025841c4036008866461a2690001114007036105a1003880c0c1401429000070307003484416030203100742c00d4200b030b03040c00701c0200e40c03034010460350f4a103c0b42c511a00300d058020440316500c1c0700b0803054401c10b80080c507109040851451041c4801407048540000500c09500803da01e168a40b000740364406c200040349246103016800d5401c2440304a00405003440b802c2507002440143e0403005c0040c030070b9605c101c81d41502860400c0402d8400a07010360070002511060b0394084000c6100c1c00680000300f180c0051a1007442040012400751400202c0c1030ba003d10080c0d415a01c2000c92000042c00c5400c1c070100318003c1040381c0754000080d000f05c2d8150741403921540e0140002c0f00411196034002d20341210941e00080f20418a01018007144404034416046407184d0380020035200303140c1c1d2503079500d07941c0e49000a401c2281d8001c0200040d00100b00141a0420400ba2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 470875809 1250 470874559 470874571
    0x6030f21120b120a12031b050a0e030f011e050612032a0d080103050d0e150a0309020406080303013605040201230904060617010306090c09020a021b030105 68
    0x1070000e100640d1010300207000544011a440720074515000d2200d5020080c0c10229842a04e205d140c0007401c0c3c10180441385c0745c03903403200c00b590601c10102096030f02c41c0850311080501d0170805030444460703000c01d1410295454114040d03181c048070021210303c113501904420044038041c460781d0380361401e0003103041601c03010007015132003031103144042c4161400c0c1104e1907800c081540d03080b00789111418a015140301211010a001070f0040c01407000c107004880300c03c03000e401e246004032064404542c2d207400e01c5104940b6810046181c51000d8401e03040280000e40040062000035210a0100d4a035482072040a04c1541e44d030070308180f040ca680c801c01c090714201100da101c621103584100c00141c403000b070040341000400b503d5041c110207650300c075040d6020034000142d160041d04040c041107480e150000414021100d52002c55a0300492556040d03a40c0030001181c000f40d01c1ca0030380000381c42038100e00f01060000c20f000d40b1091740061500d034400c0d01c04500c0f1740d100040c03605044c202c44040e619 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 470877059 1250 470875809 470875817
    0x3180309090c0c030f03010905060a0e060a0902030c09040219020114040b040b0c0403060e1b0a27150b1312020d0b0916030501060512061608130606030f21 68
    0xa041c12026034040d03c01c418001003940d00d880c4a42802021551098110f0700000d991031050041c2418290001005032104000d031200900b8042c001422002c2603106246200c1d800000140d01c01c902c0d001640c070940405081591074420040d10b011317490b041c0c058000b0066103040f9850b42210707400449103002d15004200c440c0241c840b52a0205d03d070f07000500034844202c04000001c009106071203040403510b110740260250200c44256000001402c1d025a44503071803c040511a452054807460040d00350050200380a00d000c0745288080c5c0051150003030000841c00b0001940c1c10000020b1020181d4007010480c0e00e9280c401103900503007030b490302940080e0065801c000140c40d07145400c2d01704002d001254003040442190100c2101e03150000c68007651108000c200a05121180702105416003015081301e02c0d100b81c11008142140c8400d4080000150118003d050100981c22035290481024400280c4906240b0003000003c50b00711010031a0700482480340c600b4611800c012103042c1d403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 470878309 1250 470877059 470877061
    0x2031c0209042705060f1509180a200d1707050c130b1305220804050612070e0f0f1e131d010203070215040311060702030318030909 58
    0x1000000707401c800c000380e030401d9507079500943c0f0255071030f0300c540100500301d40d03500506040d1420307509150340545020040e0945106100c03007038101d5411010200e1003a00d0070911640c40105030f10f495504161416580d0152950f1042171201031108080d2400b85019051000f180a900388880c002c4141c0014140e49000690b50340602c2c0844001d00140340104126954454100c00150125000300c00c030b00c044075038800310103005040002d44084145050601000035280080c079860302c0162800c503920601104944280804c40e04005540140030007500c100c0c0c1301c5c59403041c0d8403003500b025031b60b01021900f60240f840079844c00d00f44400d50014064001e140314048001400400d00b01002c40d004005030001c6810b500381c4840101d24010014400e010880f13109040c039076110014403042c0903d103a401002004200c0380c00150305421106440c2c050546940c0d1414111034501424041c0ca5090086c4003d04c160940c0c008055405890a281403074008903018505a6803031251604054000400700 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 470879559 1250 470878309 470878357
    0x80f030a0309051f060513020708120705120c0306040e1621020d060f0b010512010315020909070819021309020a020703020307061d060a0507060e160f030b070203 71
    0x140019600b6482070040b15040504064089038100504014010309a41e07800c0070401440c00803405000d64000c408118035003511034032081554412100843c504445042c007103415a80306100f102c00603015a1940c0019041110002c0c41541c010356140b071140d030030410b2035030a0400c007240c841802c0c00c5851100350054940b800d4a0210380b1010b9031604200b040d803103a400961264802541054403070000055058440c0000000f00e54002c001c550400205120b000d052641d15200c460640390410781412114102c240788030040e10809210315008109074052003400740d0000c051074003580c0301c116000040944070900d0b00c00c81c091001607030000c50070100c04220001e02a0b00501c10b8404520680700b46648a0b00424034080e15940000001840d6a0036501d00d10074500304140442011a1030610344002400010218007692a01500103941c48640604071300041020713110170340489081c80c0a2a0b9580007081c183c81c814801982c10505020020341c0042c030100031100d118a81905c0f00c600e032200c1d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 470880809 1250 470879559 470879561
    0xf0b040305010f06081b190b0408011802010f080613020409020705010605060a0906110a050106031a07020a0312020325020d020115080a1b0b0301150e12070611070b071209080f030a03 80
    0xc4c001040d0130010174400020148004a176901c05000070351112365545261020076800c650f0482100942e409c000807443d40141e07408080000d0b00c009515181d10682c0790403000600c90f422042c16121603034400600000e50705407a401428045008a0081201d42e54600502500e0301c2039403201c8000400e41181488803030f0181b940b01d00c000d440720080314940c070019a200c608440c01a042502d064020070540318090341c000380705e5503000c3c4c01c901c0588400c19565030090111002100c0400c0c0c6140c02000103084c8103d404d0a5841c02544204229140181030fa4040d4840e021428204015400c04004044404a01540c1c81c02c80700090020309804403180c03122650364080c41070901200c22030b0700001805422280141d4080c1c0041050b284222401e014058050b1800302c040c1c070b0180d0a103411400c90fa010110b001c2d4201c983e1400c0a1510340380c0140403c1c20110780350040e00800d600070480406008611114001c003004a403500c48a26807a030750450b6503102e40e0100c8850346d510800c0410601442 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 470882059 1250 470880809 470880853
    0x3050f0a0903020f0a0506040b0c070c060522090c090e04020f0904020112050709050109080609120c210904050121060902010e100804031409090406020703090f0b040305010f0608 78
    0xf44107840701c40005492090600500201c1510203038416011702c0140072000500c2030b0130084201e50b0902e008060b58400c3c42d40000e074400c070707401d000c0082000381b0309041c940039400324001c04081601c070781c41c0c0b564404002050301c80396400000f84600004a05220640c00190007a82c0090104240c0009203040114050b0004c10807810440281c0324484909080c0c042c0700d0240b176240e164041c00e51700b230000042241d69103610840c00c990180302400a801c00108400014074581c0c0340842e5100b40c04c01d02503140000885441180c51040b0804900d01c0340410090202030004503001c1c41547da8441d80341881c00da10b080340b42801118000d4840004005a01c0080c90700d1041c10218180364401c0d00198050707094001c2003001c20002c204010805070b1010074400c001c5e924051050520101401140c0001710007000200510780c00628401410f008001180007000401c2090702104c1d140c248100346034103e4402241d00d9824003404c02a0070620380140340c107880d0342000501010b26044101950120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 470883309 1250 470882059 470882063
    0xa0602151308041202030c0108040305030a09081b010506030105100f1e05041b0215011d06150a020a03021903121505130902030c0d0b16090b03040c0303020d03050f0a09 74
    0x4801d8200710010740300c400034100074011340030a02c480f400c80d4018503080210aa1030203040042070000c10000079003003800e590f041207480c00000b4201380d0300d24000901d40701301400340d00b040c10040752140e4041c505401091251900b94001d21031a01e91040403640e1218038003401d031440c512404144140e00301e9644c045402040407800082199480d0040b80884820521a510300392413030101d018481d8040200845510a44070704607490361408041d140c07081d02c0c05600943c0180d0b5030020980b141c3da03041c0b0b6804640c40f00480740d90303a80172501010303684401d00c1c10110b02501400c49802204001e00e114242456007584808144038600e0444000514400c1914200e4041c1024042495203035122500b03940380c03000c00000b42c030004a004040c81c21400001040c0308a99010030170000800c1401d00c0340d00158104114000542104000d0b10911100d030403005659002100700012b1001c01a440e030202e038080d8080d0384168101c1030701201a9502200c0c05050b00c0b10300804540c24121035402021518 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 470884559 1250 470883309 470883331
    0x16020f061b1c02211f0b0703031b0e0306010807060207090b01022406130203011409070203071202030304062f0901050c1b0f01020304060f1b080a020601030507050a060215 75
    0x102c94004090226000481a9081446641511200002e2403190580c000040711413510070808042200c2001480c103005001602c2404201d80c000c060198008146460641c2031050250300d1041c00288120240300c2c0b414403911a02d400020004000300f01201a148154060b103010703410304617403a0250464044140c1107100d02c048080104680c94401e14052074600529000c6003408010022041003017140c03030701d44a104000411144503409100c1d43c0f00113099600c82040e9131003520036030560051510240a0384450b04440c44100d074080010762241d807284a040140d44040c880c0d00000345060928285214460449100003030701d15000340c244c418051504601d403010700e24085041422883c41e0000a6040c41c00741400703460200071400301000300384011400d1918001e8001c105503940714080040c000c01d44500d52080004610900c9065008140d040d030303426443c01d000356120130921041e03406000d90200800c40c3d10b03050558808481d001d80c001c0c58000c103810100240c440000d2301c1100d5070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 470885809 1250 470884559 470884597
    0x50904112a1c120905250b03040b0411060403050a0219080c15042d060e030601030314070b04080904060807050d0b0a0213061205100e0f1302030616020f061b 69
    0xa00c3d28020f0f50100f80c03054000c1c21003151031130320020454514000000150040100902c200c860304020380398099000000f406990b101d504000702141d83c02c4480f035400c0200010040180000040d801001d6403081d10780c00301d043d4017400c00203600082030140344a240c001d5009801c041c40d05104410b14004441a1180740c02da5500851300700d40040100540b03410041c160503031201c20200300c014020001418000c0341003221400090b1103440c140001000e01542844421020b0440c7c0705907070301c2a40c000301e600542c1c00c003030070507588039048120001e2040d42001c1011131803c80c08100e0380c045401c007408504240700e03540d54000745000000d0030514031560900192040e211070601d01c2d00105502d48507010940000000c0c4400d8980091006131181d00c041020420000c0310000f05901102e049054a09034485074268402d143c00c0040c080d41c14818070042c400d144a8011181301c04000540071a484591000d0f856520350504541c2403600e0780c1078401400c44803030480001d00302425405c40305000d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 470887059 1250 470885809 470885837
    0xb090906030c190807080703050705062d0306091303121e0903050c070e190222091506020c031b150307020109030809030304020307090b01050904112a1c 67
    0xd807802043c80d004855050340800c4450014424103001c2c042c207201900c6036900750384a00743d68401c18860280502400185158210036565400d8552107086901010820261390322a28030303001030300d0702c521402c0002c001c561149215074200001a5068507402e2261030711011000007002c0d01d222000c50b0000d1030451000e040f034240b0402070310a04ca6150640c80c0da0701100d410345440042c0d001884828444130902c80d1000329002200b044c914601c1e405a030300c00341103c0c11892001c80203102040d140e00404007085019007034000300c2d54402002e44007000c1d82e50f100700c02c030307600c1d50240c05180e01500302000c00c031216007201c1c50b50740e02d00300b020302509080711584400d81e1540c3d004441180050355148512020507502c8801c00ba040001c0b4401141181055000203454102910801182c3c950321801940641d001d0b00c04c0e0351068400400400c2048403440a20745240c2c07010441d1070f5940d02e200c180002540b1901d0501e004100014000c1c420020644001c5028816004031101400261044490 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 470888309 1250 470887059 470887069
    0x1c081807030b040b070807090e070504030b0a1a0f0a140604080304090f0513030e0d1115040504060f061e0207090906020903061b0706270b070f090b090906030c 70
    0x100840c407800b1180e403145001c2c20400d10100003d00321a00308a1b09a083c0054268410010410b44800c8082e4900f42d03150b891b8262281e22a95000510030401482000380340203403030303000e01c070090380c0702003100010784034001080300440c00009107580c450f059540500100c0c40c070502401d0f050a0241c42c4620f13150b1034203071862440d0070a5005041c201d44420000704100e21030b01509800491010140300c4150255601415034043e00301098022040c8125100a000000c1521442050007603d20024440c41c4100750382035500078081c1e10301440c1045000517040310604403920844400b0b59130795401c3c1b01800c2c44003501800c240c2d480b42c1140715040001c5003820b92485170b45d00301c82c4982c1006039a03155120034542881402001c1024851400340ca900880ea0182c044850310f640c000740000e80c800081c808d51813072002403800580c24000144941e4200700140c1c5402e4040c1e4045c0d250720b080c0c80b4104500f06c510b00e816006103e0780f12801d008900d00360802e14a4150002401010b840d604441a40420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 470889559 1250 470888309 470888323
    0x305010908030709050a1a031f0b1b030a0f21020f070b0f09060601030903110f0d0207090203150d03050702120105100e160e19150906021c0818 63
    0x74500c41800018024940d8214490900411003600c10000c41d501d041e03000150080400c500080351803000000a142d03e403030500000d842040072540d5003817551140c0d1840b825401c1340b0105e0b0744c540c05074214030511203000000da807030320117490340c80742000f50f00e00c0d0003150b1b5000000d26500d6402c200c0341c0c041d120000940094001c0e480c2080c80c40d61a1122410080500c0e0400f5160030402c003c00701c1408000c0c44c0c0071400550204007824082862001450102c1350480c100400c0c080e180281e46070384201c04004582c0913450082c40e130880d00036589461082c0200c1c80300b03844100c0360303450020b05d164150038070107800b1582d18004d04200d810a881ca80105014044511301030720280d5441c0100210341a000f01000c02400c2a03181001c82490403c07504010310025013010350500c10400e103404556660220305c0c2c07029800c82625081003503510f1500f003040030803450100f8003240a22030041031030b51002680f422188420641051200c480607002e441000c809408512201e084000900c042d80f4108069 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 470890809 1250 470889559 470889563
    0xf06060608150402070b041103030f0708090909070803030105150c01020307020115060201200708160c03050d0c02330c03090a0f03080a050306010c02130b01090602031c0504080403050109 82
    0x86841d1414a400d159240c07811400c0503c00c9205108000205042d505095440782d40400c4030358040b000080001d14501a40740460001c4600049580401030090043c100040041d07034a1003081d22000344103a10b51003a0f00480350f89074410301c01044a890844078008402003404560761a200d400f021050981c1d00403134040c405070791103c1078040d001046803810700c01003490784000c00ca24220416504903000340209003a1008c4008545030341803291460448074401100550101c100302c0d2032605400b04c1c3d01c075100556903805594046204540030b80c589140007540203121240d816480d21a40c144424031001740380c05511a00b070025004421500204007800f5204011500c658a00c81041094103268001580001d11035000304001007034502902d40c89101c6043c03450310317983c8000040310340900c01d003030181d405101e1211602c05c9481d00c0c3c3c0712a005075000c0ea00c9100850b2a1801603139240300b4400b0b403082c000c0642044000b0384650381e100700d422510404205180550f203449042c2514440082 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 470892059 1250 470890809 470890817
    0xb1504051501081803070311030f131505090108070f0c020a12050c0f060f0a0e04020d0b0f0108060a050103091b1511011422060908030702010b030a0b01060c0f060606 73
    0x907880c895a04001c04035841040c1c0e455071044150304640e61903d81c01000e200509020a90001207442c24050003a99801c0f002128003d4642c801001ea08092070364601c1105d02e45043c1c0c1003a480304030b11a0080310009c88060311984c020f6140c6106c01c50f6489000d640d01004c021880200d00016070720007588000400c10160002c0000b405170400c50b0038070002400b2148078413040504100342d40c0310541030f240003803403011102d5190403102000703952510003524910380c0700b40300107039040040300160300c040c1140070150303201c81400c0e680600550722624152403d50340b1034440d1a0800c2a03611039002219031a1040e2800b0380f800d000144420585122504900e220940d00110207400617404081c10070000b107400001d0141461000380b803c04003002405102c4980845100008401c0100000e40c00c0c40d680510104480142403d0500d030342c0c0c00c00d982e030304c0040d400e000010380c86242c001509a9515044800403504d80d2074642d09491205d100802120b20002c039805400c040f41e0780d0320814000f8405912 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 470893309 1250 470892059 470892091
    0x60b120309030f07030b04060c110106090f06090212011a040803030f040201170f072f07140103090b06100e0a0905160f1b0804050d110901090203010803070b150405 72
    0x7010304043c0180e0901ca5035911050080010511011015030405d030001c50000d10000b019200311079094400c0701c0d84040e90309000b0001340d01c3c0181d50080c061074440300f6040202c0d80d100c1c0c0c44102a0303c0340ba45070355203080c0103800502150f03050b00b42a41880700ba03103403a1b516050381d0751081400c41c1c100701c9101e0034200da104200810741d41c100d020381e004a501a2204145442c0117000c80014a03006050401003100080506c00d65050011800012681581c0c00e180d0586401801c140d40344010b00030703520383c001c061080304c03400c1d4024082c03800e1859015403100615034514050040e614142c6100004112880080c080300351560020310000d00802c4901050528000c00241c101c0000815160100146200152005e5900c21915062107081c0c1180d400c25040d1030604031141d0081d5023056034003194100745c0c0010082207070402da580400a03140120280c0c6e995960104a010900c501d00154204004200004030484a211751041141c501c4110146c80c050114041314411540311400c41d44481c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 470894559 1250 470893309 470893327
    0x1a0a39020a0504020408120a170c0c0c01030b0315040f0204061d0c0708041509030605090708071401080105010507060f1a030115053d0801051e010912060b1203 70
    0x800881d014160540b0103500d480e00c0d008440341c1d2200101c0300c0503407050010446103034480c03151079009030312440d200001c8194203204480800c3c60340304041718800c600c500481260030354028003894444000080290100201456082d01180300c020000c8804018401e0a01c0040ea114071500f030240040c40011040f865401401c0c89007103d0240261504901c2032289400107440b9030103c8003903440180e040c21003161380300750a4032181c8040d04028416402c0004110780580000741c00f104480210f0200d51100f6031f68000e09013503201888a450010700304900500142d4012401045020702c00c40c0000744851035081ea000072940b10000c8048160600741c0c3e0012985000d0154001070844280a4810503103064000303101030304c800644101f0400990034050b202000340814001002d1440c45000c03058246480c0240b1002090040522911040fa503201131512202e140541c454410f84901c102d0a05180714000507410b004000c84846842c0c0c400001d150710340ca80c0154030401c0d000b009588130900302d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 470895809 1250 470894559 470894569
    0x703060e0c040b07060915091209051503070e030a140c130b090601200109110a0807030c120602041706012c04110f19030c1a0a3902 58
    0x6001070180790350a020034082c0c50380041c100d0b130030715a2000d00055181c60514020080c00400000c52001e02d02e440700000502c1008218031101c2d140f556946107406440302c3c1003040c5030442c040841d41140c418000110441e000b0b003421864070500601321500c100386681c452401d1000e81c40840c40c5504141400c2c11181808030301c050075410b40440030702c0030b902c03031101060a5040046c5000e041040031618101030800d50b10940d40411a04030090025840d9030078000c3d1682002142c0d14000c0c0714080d0006403005020410300e09490380300703003055a028986028100000003004059558507420880020320005400c903032041e400720306014015a602d400038240c0224040300d000340f6140d815007038420400c107504d07240c0d0303600990000044429160700303c0410300c641b500c000040d401040b41d01080514101c1442100100c80c4511200707000c0c1510354000310406011080340520389001481001881c1d4020542020f1094480014484020b03080d08480c0703591881145010110b042110394605505003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 470897059 1250 470895809 470895811
    0x3120603161508181507090b0c030705060726041104051f08010b130213090908040305010f0623030f070f05120309010509150408031c0c08150d06140703060e 69
    0x10307660850b03400014142010381c90305483c80000390507017000d80000f0040c6018244110207800508130460f281c0c604404629925806290b082e981d5204c2c507030005900780e2240d241a491100005031a5003123200640070200c105501a0007101c80114034450744909445a11405200e5100748442c2c100040c0210004548030310182c102c0d0546906201400d6129140d4031400c170358405070007000603910750040074000c1100d2401e0300420921401c00e4482c805103c01400940182c0c0c0c0140001c02102030603845280c1101c8540c81542c511050f07001d0074a11200c0e80f101401541030020b810380365506031410340507081c60388981182c8008107441e8810300541c20500021002240311000846c5041045000030300140078040340b0501c561070701c0c01510640315140b02a02e00500d6803508682e101d5207280741100c00f40450070b0300c1e58615450004203003011449040c1d210301680007030408040c501500420311001080d0316000340c901daa1194000084049182c10207481600e0503a00064042c2c1040e45400c5040c0c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 470898309 1250 470897059 470897071
    0xe03060c07140616121b0509090c28020a0515190e1902030712060c030b06090a050603101d01080f0f03030c16051b0301180503120603161508 62
    0x800a010408680c070078072941c070703c50345445c14202da13501021031601c40541130b44000403008008450407403100c141c014010b8032400a0460706c21815039107500100c012805084d60340c0c1440c0084c07220741c0c0500360400c0c01e0780001101c02c1c815a8140c50703e6071103040c5800050301da40d1400c0e4003080d04000b4268081e894001d840e84480c07805201002500381c415998842481c0d01400540b02912004e08643e030400c4036400078251030f203220a141c0f540d414030030000c0c4a19500c01e00464244202800750385016003ca40780d80c6402001c500a440c2014184203503508000c06a440c0302c910244049004000f120702c651801e105900501803541c1030150302402d0510b060001d002c0756020490201c865100401526408020301e640d0030740341d40319040c03020051980003002400c503004010342010303081d1240809403040780d8150000c0c0400c1c2110480900440c0070884003502c29001407200480c00040c0059250300450010708030f078294082d4004c4000c407148a41d02c006400c11581054001c0d41e07421282042d4019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 470899559 1250 470898309 470898313
    0x131416030c0c0b06030a02091006080601140703120f29040c020a2618040c02030307020d03020304060f1d070501030506010906030e070807080703020301050c0406090b07030e03060c0714 81
    0x1c0440d03100504045a2880010034007007043d40003a41e6901c0800c1030211142e00240060840d090555003840c05500b980280c100082d08080003031034035401409048103200713039025040d243c40c40c5914100d80b900310701500c050242d610f039a4034006003125409516149942c0250310500c40459400c1c2140c3c140b2020300580c0101d040000529820707402050900a00c1e40100d03005040741c60422140d0598880c00c3c000090012000c201c03441d02d1303038101e200d2507040e24081c1e8041101c4021500103903641e000444003030005034090071910104a1113a0099600303c0c0c400c480100304602d6501d000f0040c0c60080851102d07119070211000b0f1040b004208507001070000382000c111608010000070504000f5004903c181511140f001c000c410042003410001d00000c2c040d200321544031100180c885440d40700981c420341c02d10003c2242c248023071084030220349803501c0341c02032140f404180c1841500075220540070700c039400003007983c01e4500703004140c8200c0e4809070103075031070005162840c05101c03081d050440716 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 470900809 1250 470899559 470899571
    0xc09060609010503070201230106110703080f0c01180803040b01090501210f1b0f060302091f020a051603060c050c150a0b0d05010c030c02060c1813141603 68
    0x6846000c1124440c0d003080ca440e69480e50fa40c2000d07800f409170341c51400c2141da13150301800e10000c100c52101d41611590780c1e508140054041581d070b81c80416020203807041c5c104000064580e03813100c00400424071460004510f1007640c001c0703816a403003425000c1c4d07040782c400410031040140d004403d50140c000200200001d504040f6261005010812411800303c042034400b01402003c100c0803a480364450145200d89004400f9440d0f5403419100d071008030032181c440440c0c1070b4080c4c000c0e034400080140c8a010304943d002440c88600c4401003800080d8040c105250380400d4090000300c644800c92041408000e02e10b182c800112030085180e00100442800000142840481c0b1303108604010304460a00340c8501c1500d0340100303031403001541c0c4140b03512244d4003001819000820f03a1031403134030b0400180c07144510580c0c43d043d00310b5016200c41010000003640340880c170b05c25001030001500b03484900210390041d0044030320a40720198100c1d0120104a201014105000c008001e9480e044c00a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 470902059 1250 470900809 470900821
    0x50306101404020714060405011e021213020d1401050403020c0105040b0a0c02061303060b12060405030307030e01020f0f070507230f0d050607080708060d03090306021e13080c09 78
    0x940c00052041c588038a400207020350a00c5100c101d492000c800000945056041514016009011403a10801d8600002d0710003004801c02d40700f550340641d80751000c540550b503507c0c0c0007a44035110b40b20817a4820304036001d041c0460042e08000c20317600c403400000103403030600b418083e06e410039402465041020410050100700390000c10380340e540026081c15100e8041f1440042c00703502409003c3c18403141214000401d01455030089020725005540801c0548000707420192100c8088502a0440d072040021444040c4203a2003c84015600c100060604040d068040c14030f80c00816181075040003c41c010041c400140004030060420705154101004002421405c038405030300801d01c1000b0341c0030110303a283c6414003a804100d6214040d40c01a180240e0058851081903900c1c0b0005610800001c48034140000070400c3c00c0d4054681c41c400b40e02d1079940001075400000c0c80c842c03d0b120142c46448440c1041c0160035a00401071a0000003030410055078036000000d44e50600c502c2d4400d0074004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 470903309 1250 470902059 470902079
    0x14040c091e020c0f010507050a0806040902010e0d031b11040f2c07050a1e061713140a0605092104121e1a090a1a07090e0a020405030610 60
    0x900c0c20069200581c03518650310b0360301c2c101400380c03080e1841355003003404109900394014020a404040c40d10f845c143c50b2280381c24001280c04440f4000d0116024940040741403800c1c40180d060140b280c0f50071280c081d0041044004900440f00488440240d1524054180ba040c05202c842e40c400e007804101c45190b04040310050089500d103012040c48031040205688014003201c0080d000203006248034541da9204140710500b01200030141d08840d01c00030502c54032900300f140b00550305203002c0b1010348450f03a100c0e0702000b64180403030b09030020303040c54400103000340702c41c4040c64051a0005082d00e05000d5040c202140b04524614008400d00070a1002540c4800c2d01c0c2a544204080d0803178412500e000c203100c00700001400350382c01640b02e070842040782090180e4035102100ca8210120345900c202980e59280840008103968500b55520400c0c0d03070884c0086902c03200310711f807503088141e0300c41409021680c140c80d0071004a030002828040c13402c041181e25084050b0041038210140b5140d4144 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 470904559 1250 470903309 470903351
    0x90a0506060f0a09060b0c150403020d0513030501091a1003021f141602040b0612191b0804050705010e01090e070509040c0809070b0c0a0f060f14040c09 67
    0x81d01c5941000c012241c1915030340e41c0c11014004d100d10030400c00b80c50790410100b5400c2050340da6883e105003003419400ca1a0781e9a03860080e98980c005003e403c1ca007410030b450980011141005105130f4000010100c0d10074000c00c5102401901d4603003040310702802c03541d00004002d03d201c903401c00c00712040005032110340e1000b54003026400380b40c8000c5450301c011500c07945d400103c4900d40740c0101d9108003c1d0444601c1400942c4211000c20580200e0270902045020300b102103820310903414000b038070034002c503a07056001140c03090300064450040c0042c824100c49444031800061420402c0104001c1c040203540003504090a041c0d0203200b050000070041917042c018112801c0c11f203404a05110302036010b460304030b40000c00134400d10f102c0d4800101007140c11138920000c8d00c112200026584e48900480b18240c4800b0081c3c600c203451900c0d90502c200c0240422a1002d40e50100703142640021310410802c2071803030f01b00300351900381403e02c0c2c24011440d4010f0340582d45444504681098881051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 470905809 1250 470904559 470904571
    0x111c030806030d05090f030106050a0806090f1603060c021606090503190f02062d0c010b0109030c060c1115090907020d0801030303090f120f030606030219080c072009090a0506 77
    0x760014042000312380589515405560400e042c0b81011421084c0402c4441c800c0704000b080b50324441429080555410b2a00c3c1019890400d509091012841a4002001c08801401101e144100c510441c0c4409260b07540300c840000c0d00c62030f09115914040c480c0160302c801c59402d00c80e070705080d0f445285a5541b0307410700034880d070000030740007604111581c080d50700300c0030484801040103159060190291300a0038019010b52801d0344900440d0700404141050700d8000700c00280a40c20b04c1411740d0300b034050032402e07501e011030b03030301d0241e400e41d11031049240c0c810091940f6920b4880c1c0400744200407a014001800b99003141d402c203000d0720750000b9554110303a010324000c6400c115a04104440b1240020098403010720586603880c4d44c0d411240d8200034900c030381c2e02049081d548501c03ca04074000c3d241030005120300c8800681c0c2036485016240d0700070322980f41d02c41c0b03025901d031b032080656042c5900300c2c0481040748190712018500b400000350310902c800050a4032403496918161070343d10007045 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 470907059 1250 470905809 470905819
    0x807140409020f0f03160e150d2a050603191104030f110f030102030f090c120a060b040b1c0b06045f130b0a0207111c030806030d0509 59
    0x20110150ba0308200d81c80c9040640070000e00d45d152a0305510034050300444243c3c003200526180344d80182440304e1270044094202103006e2034007000365510500d030071410a0802d54981601000300c2d1580d100f500039401050006401100d0b8907a080522090790302c5c042100010701400c2c041000458900c0b501c0e1089070740e1200c9070340000514880080c460f110343c00c02903a0550300c0807007002142820071102078000c00c5080110b40c90704c00034104010001890030440c02454100d40300c0c00d0b00084a58004690541c001000883c03001c05143c0401c4402c040b030700420300c1444900401d502445000310340150080820384050000700800007400c060f49540740001500715006030462010281e00450250383c802909600c400b601c0c420031046699040c542c8403801c0d1120311400450509003080c0f441a0f5095400340107808260382c1d41c243c000007900600001d981c1000350021134441599140080344404403501403114081b20709050007815000d0003401240664005500c1c0c58800303800ca07040d00d035881000c0322 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 470908309 1250 470907059 470907079
    0x110c0318060706020f120906011202040203060406082a191205070b0d020c072319030203070e15030c090c0904090210030915020703090e0705130807140409020f 70
    0x481e01d248202c100280002e072001c2000883e08503024010502000303e038421400720340718084415120074084c03052112402c4519003244c014107103a000740d54001d90080c070000d1004d075a00d61042c1802206200e080414218800c52034003030319128036141348070106803010004610302d072000d4140f007a40e0740640035202030101ca1110402608004020190a92003001511102c85010001c040e4110f86060381c900c0c0200c07031004c1100d5080010310300c011819418403990350342148081c0070341408440301090b01c0406480c0d021026841c10402074000705240008800ac62503e6030406404800200e040d03442608104096a15a520034401a4003c14401c4c0480d5481441d040064003c05013200000d40050f40d0704002100d40e505030b0f001c200b185000c1c52402c41086031200100c812032040b04c000801280c00100d0034080800119481c0c0d6003c032550400a26000d440e012114142c112a40050b6407907025260078880d00c40d19400800704854141d5051101309665400548150b0540e01c03414021080c40c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 470909559 1250 470908309 470908357
    0xa1415060403170d0f0b0307140609060304080f07200f0904031b06150302090618040602030c1c0507020709060b040b090307030b010801060302091005060d151a0904110c03 75
    0x982110f56201c15020200460300e00ca180c17240c003034070811a407103200e4082c54600185048010841100d8041c0007807101e40b80a512100f081800d420241064513041c81c240504c201000d000002462014061042c00382c40c0c3d8603200c0c40e1542194010350040c02104102d16040d8107031108241d071354125506090480004543c21710300c00c0310040c00744018213240c0c00c040e001c1400021080c1c4c00c01c2030702d00a403540d845564541060041c400384580c1111194010880040c2c08104150f0103980c0081214803418a0310700d400105da540c0244094505c00940e9407801400750301c0d40c0401c50722000b03000d02041406140d203044851442c90141d031068203000d40002030181c10954061000c00013640e0321191903451307035031108230781402043c8500003207007e41865404078901c1c50030303119507138111800208003030f05c0c0c1034100e4178260244c0401800311024014082e0f0206215000d075800144141c0384e20445920345c004802040165803000305000c92070242003042c0c41c070264000c4112001030030311552002e070f501407031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 470910809 1250 470909559 470909603
    0xc11040504050115060c1401060510030510050901150306050312070609021f1206050303070209010909020d050105130611131511011506030b030708031611090a1415060403 75
    0x102c040c6080131078a042c3c0403910303a401c00c100843d074a00801c41e41c0003079030000f08007608840560050300e034001401c0c0400d940d9140300f5000154403654200741011902d5462006c03c058404c01c2e04101d25142c141020400403543c940f050310000e00080b4001c06890040c00c00c03040086c450404090000d6403114051415900d640d100303080703220301001030301c4011039010000900d00c8849000500e9020306090001600e03190001c1a80c90302a001002a1901e03403900320714000034032001a0484c3c112141c900400c002c03a0007031103224810030300458642800c0025190480498100e40480c0704188002e00c80e2550641695464406a8028002d1400e4940030b0a006440400710790b900d4140b990300300b03110341c103c0f00504021ba07800c98105032024044001e41104243d100d03081809802400d038020b10610040e80309500101c420076002d4070500741c03480d0342d65010445c00d03a002c40b0344103445920785404081003020308403a0740d44003003981402040d00c024040020114400c5100182052000c2da004001c0c8983c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 470912059 1250 470910809 470910821
    0x3170d020f070609031805030d03020913090803070207050904051c120513021f0f0302090a0b1305150403051207060e011d1c08010909170703030b030d0c110405040501 73
    0x10a84903036150180b5142400280220740c030100c001038189101c8031041e514480c0c03c1829104001c02412400c013041108038000d411180b2807941c0490351403610403004846100d4030205500031000c00350782e8a05108003a180c14001d51003a4094805842004081507010400341e240340d04142d07030744007090020b12084a03000841003400c00d9552a1109000315a1090242c956505100740c401a500307a020044c01c0002e030403617a6001020600c90548140410300c030b44c1c020061140020603440c0821f4171200c6001d0550004140500b0b007900412051005251094501c0f0044044100c0c2515003400c6079602500d03003001ca440c1000d120030100d603140c108000764000500e071003041d00003001905500d414031a00d40083c6082030100f40541c039075031008031200311401034444940d44c4500042c0e07441d1035455401400d04071004c0c0e5200340000508100c0304000705c01800b01c01e0090380c0114525a0000c10981420780410084007031006401303804000402c8414407100307111041750300040c40d5813181801ea0140c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 470913309 1250 470912059 470912077
    0x7081203060424050a0603020304080304020d02011b03050d2409021815030a1104081b040f060b0703090e15090603010603080406030c0e0306040f0b100806011206050702010603170d02 80
    0x6810500103e005080c1d42d41e00319001154980e00c00d540d5018150100c2c803041d10003925810003000001c2c05800c00142c40c0701c843e0f10601d403812090201c50101c0c4031a881d1043d084000440010b0222890580c82c018007401112000d6104000649013a54101000541c4175140c249034000c9412000c9502c0380817800c141001c00382c000b41050312450f40900c0207a10840f00700d951513141491201d03e000040742540d0aa4103c80300030075809005d030a01000b0020305070b410640c09529158411021000c42c082d0358014030290f080691038001070300c0d02801c03224842d0001440c8403000750400080c101a0620704e0b01d80d210a841000c03040d102c40740443d000d0000340d000070f0004030300042c001440a038950b00c040140301c215a1802e4a1401c0074040645601080c0d4016007020070781c1d00484085942c0c54500d50f00700e0fa0b00318010014543e50808a81081e800340d1019110803060107080d8144135540c010150712590301e00c020062a400d554800302d01d2010042e0542e44070002207004490315025904403a0a03034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 470914559 1250 470913309 470913341
    0x209010b0f2205130c1206030c0b0c0f0d0207050a060309051504080909011404060905101a040e0115030e0c09071206080a11040c02031602040b0103110a170108070812030604 76
    0x3c2513031061030024040f01098680018107282001d0320000580c810300d41074a5020540000c5540b038103181080c0d60f0003104040302c49000707452450035101c130308100c180e000c0f1519401400b8140e01d00800c20544410680c4200c1c145400e080c14000080c0012840b101c1100c9143c1e08580240c0345c0e814121068060910601d8110b48440000f0480c0c0a2840d110503c003e0112400e002c1c0c10f4545960a081d92000c0e0b9480c030380c20418070810310002810390001c1c035484494281e203504046d07941c034400c81c02c150700f0b9102c0d6943d048001c02c5401116410b000d4401c000d0101001042114a5580071840c6c50400400035400c0102360014010601c03d260892001000c01c9012075000c2d1125060034201032001e074503030b288141c3c80e0402c40d0898900102c240c074030b420315a10b40005001015000d22001d1b1420801c4a03041643c4c82c025084550841c10190100a00341d59400072051800082c0c01a0100184c000300480e0344105820450704d0340000d036030603105008074501030f00d0380c880328003080c0603000070103c0c8440702c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 470915809 1250 470914559 470914579
    0x11040b010c0f0219033207050607060504060908030a0203011e060806010e011e021615020a08130b0a0c02030c0a08030f070c05040617070e04021e01140a05070209010b0f2205 76
    0x10880c1b00f224030817480a01c0800303118403c5454039181e80e80100e110b1142c02c101d007072003450089500e6510099009000b09000700b80b4050b00c0d5181d02856000712800180a680400103020809900781c00540000c4040d10108015060541c050040d0500520003410002c5032074200605034401c07d0005426400404440d04005c40c00e500a074613400741441d00016001d000000192282e030030445001245a240c02401807607805458a51050303001c098100c134142d40b0220009000c5892900600500d06603079100c104507046807040500b00070480c10003a1040c500c0410920612001108a64241c519008900e0b654082c41c94421043e2950f0750040307a03c64138000c030004554900b07540c40500820101c0540e0f082584800910345513001c2a98040e412404414016400c50004a82c034a01c0c04014100000c1554900740b00200503441410910006540840c4520031401c1c00205c06002d0059103401d0b506022004501c0c0768140030751000c1c6501d60074a00010390100341c00300d0405002c1e000107040c41c80f030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 470917059 1250 470915809 470915843
    0x1d0606070b48040b031b22090b09040b06040216061404020307240e0315011e0b03130821100f0806041502220311040b010c0f021903 58
    0x801500314410541420804044200103094041160f0590300c064074614155283c0c4444843c001180700c50442405d14200030040c03e5142041940c0703103c0503644071690a10f802c0c055807905540c8403082c141d0240110f54184000030307034001c00700c075407148ac02c0d140140c8030b10b0110301035071000f078107800c0152a42c0c4ca408540c5204030b50b1501024800c0e4020340445a642c0d80d81c10707440c0b9039805002d2111118000703210031012498401c520003400040001c0840303103c00e10143c0b4610381400c0a03440003200c1a081114070609231513911000c0d0003481070080c028110300d0300c1c0700f0300c2069a0000400500801f40002d65041107000c00c407864200c540c40046045561500404112501c3c1160081900c1c500c4d8411001425607000901a4400e40e4440305900e04480380e110032801a40120103000010403410100802d002c11040008004500511110841d00e00c9a42440212400c4604490420070500301d00c2002c143c00e0039407070201c0380c0d0689204c5030680140c118080914011780008100c00c105080e0440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 470918309 1250 470917059 470917141
    0x12161701080105070305070f020c13020f1303060e030a02101d07080f06060a080d030e0c030a08070c0812040312090308030901140f16110c0303131d0606070b 69
    0x8410001c84d14100841d441f00d4009071040400c90318250010380c0021856803040c2800c841e804205511468058185902c4824401550308840708850500c1c0c00c103041082400301314058182d01103c1c0b20003440ca010410301d0000d445601d40c942020b0791a0700e885c80b03010801d44044144001c02201400da4140d241c0b10440c0c86d40794040c3d424842114800d03580842c400345081071407002160601c030002c040d1048804000d8000e8000c0301503d40680c01100c00c203110507101448442c1c61240b01c5d20007140c0d5030710240352100d030745ea403a500403002c154804a120109003240004a50650b50440d6500c00e156102e00400c43d155115600001c001110110500081c3c9005402c4006104071880c42180281c0d030700814401d0010003110b030100e050301030b90f0720402a607008080d0071003599840700588602c2d02050000c0392850b8010160400c02460036181000154110b07142c13804404c1c0e017400c1440040c24000c00041150180f2a03024040154200114140740c11808500b1404001d40300107550240040403001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 470919559 1250 470918309 470918311
    0x3070506070e030105010f060c110907170c0a020a080c07151119030e04020c0a080a022401060f0e0d0615090c031415030f0a06020a1412161701080105 66
    0x401042c11030380082210700e410302485043e12a01c21400200750701d0440300300d40380c104080064480c03400820a00d000f580303a00300c440d0304c520925215a00b1180b20800d01b000302d0280107003107402c1c560b0103200070320f080307039007c0b54201100d074100154580711200843c065050480d103a11078100685030034100820203030040d228101d03002004050347e200782500204242d050004900060000e5142c103104030b041c3c60305501030414244008100c1e1007a00c0141c0c3c130751240c1c1d0b01030b8072000e002d644a0b81c0a03441020724450241d5001100701107072180341d403400350f018080804010300c1e8070504c600c0d000c8480250b01d4100c91400000e400040a000b09484400040d41140d9140a440030250904440400c0c0502038000c0501c0618010f024000d15544c08001d4003404e80705000fa5a890700842d014404000e5042000c044264010f0f540103a540c3c0030303d000070700002e615104400e0b000f2400e12128812601035000307298480e13140148040c0c001b4400303004840e4000f0390404014403104070800480c200c0c40c154883c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 470920809 1250 470919559 470919571
    0x181605040605040b030703080d0204031e060e0f2a06070f02010207060201111209030702091015080c0a0e060d0f0920091603090609030807170709050d050f03070506 72
    0x402007540c450090000f69840034040d25055032102c4020000a4500c0008040c9400661001404c1603125580c80d4544004032004a5000c03000040d07000901000303105110112041d480144041c90449401a854603041d1440ca51081c000707004516107450350303441c4c1d401200002002d095407000c640c545061140d40c021000e0b4014070890b0408a03407207005103e00360818003610406070802c811400550b0301d4042c01800700c4110701040c4000030050300c400414034040e85132039220500303e50070092407041626000075454104400745041c02190790003a001c58540311900d262040d03a1000030001301d03c1e10710481c0010304080303280003484030400000354030030160740d80f24070660585803411444a050300002030002c15801100140411150f400f84c10b03150340c4281182c01e0104211807217440c0c00c000c45000c0d41c000d40104a031101000a03591f480441440740000401823840303503082c10f031401085035109000d82d5026022540c0e070003051020801031180500c200c501103070f13a070b4560751606907101e803415151 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 470922059 1250 470920809 470920811
    0x81909230d030203070e13140c0d05100e13060b0a0b0c07090504030f05070c09020313050c010201090506072025120201020d030902060c012a03090b060918160504 71
    0x140001c92090088a000319035070740d02e04004080340f83c2004000110004c42c0c05e4610740c0c82c040007018481e001d21051140b180a14001e032101d2401440a007951401000701030885000441130000c641240c160540041e014001846603074542e00d085030040c03a9204002d81c0c4a1120400050840c0101300140407401a45043c0e0700304654403204481503076001d44008000c10f441070380d900c012512030000b61030114003400350710390703215035404441089030300a650300400000d9402000007400b00030007494180b41000e2000308141115500c506885281c06000c1004008500c03d24203584a08240b0340030131081c10006886140c070500c1001c003111001600030184244440a0000e82c0c0c0c065030107214041d58040e00580482543d400781100145110a0100d038018000d008a801c2528248200011001d60300c42615075508000703e6440325051540b04403003010304000e2502c0001c0c644050315078000c10103527600c15580d252007045001c0112160b40b2040c5602c60f0460003045032025201001c00c03208182c3e8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 470923309 1250 470922059 470922073
    0x10e060a0c0315050913030513080c180f2202031617030703090b1303080a0807090b042411030d0c120621050304051203181008190923 59
    0x111200720910f6218603079102030303c01c000920f441c1d01e00301c031000e845110b49041450302075070000f01001c8080b5a00107584551040046c0c80c0c0368241b81041c1ca2415001d460249090315149008480e40300c3c006100001c2c228184425412415074501d901c000c0650003030950346030b07030300000d4843c583c42d03c0f52040c107552800380041040902c40100072100219016907070003d45a00306104900540c0c4040c2c0c5071201050f076038000101040030300020745205205540c421646041c0100000c0502e915a04000400e82041104108004441d0320a07912036044480f1340308001c003045d1058038038001c80480c1c02c242e80000615030000721055031101d100007466882d4400d030041e02380039010803244c4030b0203172000f9040340c04a0b041251a1407550404440d11440c1241d1916480f90081038254182071440c1c0180e80c000314000e5406041425800003031103003961000350004e06004001c140d0303100a810322911010010b22064490b40b1078120302505900b04881140c1c1107140301c51800b492640c503542c90941c1c01070308 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 470924559 1250 470923309 470923331
    0x6030d0c050106051c1a0f0403030b03070e090109050706030e07050906030304120f210c060b0d140d080610020d0c030909020f0d0513021e13050f1006020f070e0405010e060a0c03 78
    0x510f0780381c042c2c0e00c7d03048200c01c60b43d61560107400415031000303110351504c1441d600042805810000d80c0c880c02040002199400c010f18040d490b12610390005011f05050110310403c03201d001804408a9404071600c2d00c0ea511080046800c503c1250030102052000d07100304030a00120101c1440304610640c1030b0b510360002d12054016598108503e4000541c21003502030115900d5080303541e2102c002406010f821100c0e581d895019007200e82109002d8210500000d100343e000f903002d950190081c2c4e00c401c03449a04040c025154a0f421f0710040c180010f1108400925200310034110181981100465035691900e44420441e04407640302090315080400140040203144c10916031254041e00b81c0c200001703020b01a0660061003840550015081a50301280110500843d80030361050b012040080c00c00c032802d01c41e02d242c22b03000a000c0d54010240b840300d1080c0019001d045800000c0341400644480ca0114050072001c00d8880c0148508c109000d0049081e51282c481800713552400c0143d141c0c40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 470925809 1250 470924559 470924603
    0x609010615030209010e060a0203160b0a060e10030b070207080304030b040b0723030612010204090608070b030c0409111603080121020312070602120108060703050a0506030d0c050106051c 82
    0x203802001c5c0029070b0fa58001c100c0b1305040019201c0000d25005580c00c2c12844480c0315066003d540303003940c00d00300103014070511001500c40d460142c240e41101c80560f00d4001d1007035100d40014400201070300ea0a600156520f40309000038800b816000c01500d5403035980c1e040075627028a0580b000e0303d26443c64004180c0b20fa00480982c109400b9a0f900e145100705041c18418040e040284100d130002c0146004000d10744003880148082e2400000000e031507030a00001d035141022075009101107070420008d0096170761751142620103c3e4500480030170a040350b40024070796405260061928480070103946400c05400120040c161010702101025070500c1c1c0124403468400404080d405420240c04081d40803030060040405c0d074007940e005840c0030445455007090035401d92001341d65404c000d061081d81a410b010b640c0d0061240306080c09203003054400a0303200d0551040c03000c103200d00a443c28042110a400140044c4001422005280c400d5200c1c06620010408129151292503120701d50075510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 470927059 1250 470925809 470925817
    0xf1f08010317090f220f1a18150d0804180f020a050d15030f050703060509070501090506210c04050f10050307121103012d05100c0602090306090106150302 68
    0xd02d59950600136105100f0303070080d42c103424190800ca041d00b00300c0d40f05250084542e807020180300000c4c010812810741050340042c684051040d8691050700c21403032070b00443d250300410700100307507086204100c00050030010b40c118000d0034040045000201c0c03480d401c03940c64040044420920401c0c040c904520100d100f1030ba2518081082132001c880b1021055104000e030707140758148a80c0c000e4490b25662040d01c50b0441c210340c15484600c0510800000b4060f140d0410703142c8008041650500e00042e041c0340c854042c00b40200c03404502c1c002c5e1807040030088108504c034042000d0250030f100d058600d1a51240c0075a90150340c01e580c0004580c00e0041c11180c00d108540c2d1100d0a640f00e075102295400d44082100080303d46645851808140c140d0003540284840840000031980a01d10100e513513034801e41445896441c10000c003d41d4075076000703001070042d15182004600007030f0700c1c19100078020110003980510403101004069601503100a00703888860b601600c182030802012416031207 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 470928309 1250 470927059 470927077
    0x6050c0a170417161506150813030809010906050405011d0a0c06050a11010221060f030703080a18030b091218011b0803041109060103020f090f1f08010317 68
    0xf40030185420342e100001d0151181e541d0a03c80b90380740840e5521400b644194803600d142890f41d45103403c0007401c0c9504014004c2d21901d0a00300c04038645518260501011004043d0a029a040010760300303080039401600c5166126008200c1c50900d810940c0c002c100c0c0d5070311020030010f90720417003000c060001100c13404190700900d080d112904100d42102c1e950001c41588081c003041d1506015503803000c0c00984010070b0502103026420007c582d0301d5440c1b60b40035125a0117000a50505001611701042e010242c9400041c280c2d0743c0d03040d84c0005c0f141c7c20a4111404100d9911180c0030080000020300c00e4015401c240c2241c40308441c54000c000584280d44040003640c402880001c5275501503101d43c401c1c030115000c000b010039600e45664120364800c64085031200c409080c0c141082c50071126644d08400203190441c1002c00802c1183d440344104814588114045420807100d6a142266106100728241d500290090111006403580800303000c12034012040c0307491207200c81d84600585400207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 470929559 1250 470928309 470928323
    0x10306181401120c26030f0306130b06180f03010903030b1923030a0b0703051009060f0506030a0e030c030c01060e06061903060e010b280804080307090306050c0a1704 73
    0xc1d141140401200241000182e1681a02c03940800c617144c040c0081c018100c3c0c10720003e0394a144c51000c0140341c0c424000490300e020301c0c044500d84540c644109844002808039002401e10030181c0c0000d0001c5a0f85065940c507600307180b10a420554075030410708040c0e50540b070401c0050f4000340074040c0901c1e00c2c000c1c00100050703503a81d040c0000200c0786900140001a080d224131814a840b0552261806c807190340120f038580003031104400440301c10348003d2807490310820120b4105440b0090800c55841030a102c1c0b02d011010031105040d07540701071414400317881106d0ba49c920910301d080c0c903600000540c50b103e5203404000038450025807885403042400501d842d05d00004424071007164105045410201a070b2500c0100381040c00c268000e01920002e0f04003a280e01300341c04146104241c0c01c810b409a291008009480541c1029502b03401680c132012050301e995a44d001183d00e1075080d4000f804590030702090080b4550b422000b0041c6000541d100c08410340c204010007000f03103040d14020100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 470930809 1250 470929559 470929583
    0x6060901050f0114210f06010906080703020703050f0c01091e020a091109030f100e160918050a0305030a050c09010212030901090c18180c05010e01030618140112 71
    0x10343c843c4100b100980e40340702925003801500c0c0c07017004180340324075400d082031903190b018800300c504a600501e51042c003d1800c40020350902034018190f01c000b601d0b88044c141c0110791501014051400d0f50089282500b0903034885505a90310342c06400c54170010380303000c59040c0703511503050702c8030048404461300600402c20041c5000b04100042c032881906e2032100b1800d0050500669052141a147c1101c0000410141c006521460229070944004000c668040c614088100100c00e0341c1c1011626036490005050529401c294403042142c06e00502d42e010343c1000004044d003102c0594040d0503000400c000c682e9031503143d8030705442190b545038056072102c40c101c0c4a9411030300003158000d01071000401c42c0101c560f10952080d41603000100e0420005802c03403200d6600384150404202c032304000d00b24605007519240d003200080e01071641045410304100300541d000340c00130f81c01050f180e903410032041d20940c00784000f050aa000700c1480c0c50520000111103440454940305650401444041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 470932059 1250 470930809 470930839
    0xc040e070c031d1c0b251e090b0408060a0c05030f0f060402040b0f0d0b01033312050d1d060409231603050c07210c02030318030606090105 61
    0x194010003811340c00b0304070048031200c0788402030a41207103d02c121800071190500f19003400381401c10a503414a8101180404a52643c0c4840400501e000d5440c40901400c280d1200304c1d01103070355400225079207200190001d011140000d0303152051580746410000038452800c1101c0512084da080711000d01000c000c00c081c0c2c180034090035003164000704018606a510721101300f582c0c2150794140008400890760f5075040101e07015680e5095000d103420030265100580007140000c50703000654040e007442c218a5080004920900068542c0c440000c4030b5000034608559906052004040000c560b04030031503640c02c6640c0d020321007150041c8000e06003820304851600030404030301c141c0d204410800403414982400351311240200719001d4804030500810038050256038000c0c0c90400220700401c9600007003a190805144600141c1d80c07414032207012032404541000049034069414000028018100094410b0407810380728242c094841550380c1c1c4c41041b00d480c40900c141c5811038404008202 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 470933309 1250 470932059 470932097
    0xf21030c0512191b0e0f0a210501051504140106020303010603020a0e150c0d0207030503070308040501150b0a1101090f0206070206160606030201030609052e030b0c040e070c03 77
    0x140c030002d0641e89016030b0400941c4a03007030b513859016941c51514200b07200d41110340c1c018000c62854800340d074400d8903d988540482d41e000e04e20320900c0f20711307100762000c10311040031085d1110805400800a0200303041021001c0340510030303c4600f51082c0d1418420711012408480e002e41210307090f40145080d17a00e842d0065000e035000700780d00b001b000307445100d840160360303039210405020b4850101513071a2017906420601d80745504c9041419948115410000140000103d41406a042c40d0404580d100d500c1d20380d000d0120a458603141400c41100400c02c000168040c1c10074122a07694115003000c1c140195088840801002c0c0c40e0b800a108680c025041200c014108184080c00007454540c502884401580e000e50084400c181c4404040003550380c540111b00c00b402c8143c1c420042c0d418061000e01c0d452151101240140c0c002c8141101318001ca500385500840d0060400c03c0c1d103182030320341c0c001c5542c0305014113041d050300c840216000510440036004616450748611b100b495120820308 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 470934559 1250 470933309 470933311
    0x6180103031b051b0a080703050d12020412030c030905010f02070b0a0e150903010f023612060916060f0e030c040c0503071416020103090602070f21030c0512 69
    0xb01c50540d03196032400159080000307002542d980701c16081582001e0b8100071111159610005659110510510102d1804100c1031400c040e181080002c0c07401201900000e070045500504141254406450506411000d60214144a80e440a02d00740d102e04c010741d002c0880b44030460060b80202d005210310340c040c03001403120104e1810304440c8462106c0000d2050707543c21403d46450f06020031010b90f2030801340240360b03d2410181c6c042d402c2103008107112001c0d100040c0d0703450f004a24440e440d5016403c903100000080f50240008844000501c0107983e6248180c3c0d06252521a407501c052900d4003002d220001e507421a83c41d11466542c00b103084480403c1480c290383d16004010a40401c0d85d180e11075060041c030030b9107134251a890b0881c005001003018003541c05614804100201d03a440744900c10b6404140d0900b0300041000c01d40c00c3c494003c0c010000300420700e046c0c03190180180101500024000f0010b03008008007811a8502103055514012810b4003049050040c8850300030500c54003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 470935809 1250 470934559 470934587
    0xf0f0705011404150e0613120909060b28051c0e061008100b1c0606091d06010b090904020d0f020301060603021c14070c020a0f15080618010303 63
    0x1142c21a8207861200c0481e6040d241203c200e5442c0c1103e00542825000764560001c2070406080c4910340809600c0c0502030600004000c0d841c00f920040202d1301071041100501146c00080224035101d08200344a42d200303081343c0110b503164038048152204400340100341d014080d40d4071820236400c804803061403c050448450b070540c40b40c0c03510070440b0b002c0104502c90380104101c881401d141c0008035040581c8041282c0c2001d06010405120f5151a9500c2c041c005144104111408650410340e00410558004098140c10041116041c604038110040c18076070110955a6690303031005111954851409402c1c2c028a06400160141c42d0001e05651654050811600710300201d9002900719481500180c0109501040c9690119591040da015035103006600304035448181c910010503c10007049081040b400700c1c0d9030340454550780d11045c020141c41008138080d507101c000944203001804070384800a89280001025860f0411000900e0b06550300f01d10401d0342145c4003190020f540d4504 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 470937059 1250 470935809 470935811
    0xa030b03070b1623100c030e060f070201021605010e0705031b0616150608011506140903011503080d05070503041a06040e030c0c09060d08120709090212070e060f0f070501 75
    0x408410307420a9042440c40c440034402518171500400e94603070490300d40c00c805408052500880301c560020006400740c2260700d0900f1540180e45854040f400381c0714440c01c2c4000c2c0c442030f65105003004015001966500c3c110000d0300d007090b03144c0080c5945c5148000103041582030b40d0002c0344941c1070042c0108960a03a0200d00031400b4540c1d100e100030042030251205500d0b681d65403c11400200781314a038900c800032a15428200c1c500000240540313030000c0c04807600c2c280011f0503000d554003540915824500085000754203580c90400c500d0070b0f0058055800010300786800150f841e0310401c1124803940c0d2244807424003803100482d0044012000740038680064bc0c030120b85481c45020005455100040401000d481071004103200203940080d05040c040d94890311188006030450302030f9880600700200c500d155a440070b03c00c980a80320b41c0e001000180c40003941a141803078010a451042207035841e040788884101e811f00c12144254030054140b682c5c2032000e446c4d198941c0006150440c01600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 470938309 1250 470937059 470937083
    0x20304030f0206161b060e010e040203061215090f19030f14030108070609050f0a0e3621040510140408030c1c0903020105090315010b0a030b03070b16 66
    0x54003034407944041040da0017202c13201000a40300c0104060390083c01c440e01d0302a05e0410f6100020380002c4040c1c1100380321715000300001d02241c0701d40da02031035607a01c5c0304211013414280b12a506020007054499012601a050780c03020485000207030040582e000806400c480031664030b0464040e10150400d07030400034400744040c41040098060360192040e0005070551710700e0000013800803011980901d00503500010450131559689500c84212003a030800c10a141d90742800b00c210b120a61030040d1141c200e03070f0703a203015010b0082e6054200d5284000c01c8031868103008500d08a040c02c101040720140c1030800040c041410006502c10901203a42007805203551100d04c5a503c1d500150040d8615074404074120031000b00803c9543c1a190680703010301c0c0300c200c0c0040010314000c01400041c1c1800000914081240c404120401582600b9215032606503110f072001c100039400401010006410244182e00e94a800301d10390741162904001c042c580018074a440d00e8503800600c0985242036174917 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 470939559 1250 470938309 470938327
    0xc0a11070303090512011a0418120f0e01050c1c0504080307050d030605090903091e03010c0816050a0e040c021f06090f0506090f150d08041802030601020304030f0206 73
    0x403104001e107220b901c80b618800e0500d400c1c403646441c0200350142070b81c10309030011300b40c0308a05600410894159400308050001421502c10310410900007000050b05610290340980d00000200954403a90348081017280084011140e500a14904500384e410003850483d00d01007a4440c01100c0c01182020b034201662030219a003181c100750010b0720580c120359418a10590f00d0300c101d4011348001c43d0b1413503981c04d1652142d03a481c004c10b00118007501115080d4105c0728070f40e400100e100c00000b0300a02c000b202900b002444000262989180820b400700b410433018003c1003a0350f054155a914480c44000c1c8804100c05071500103200000d41c0141316514114004400f84024440174200c00402c115280803030b800b00711180c4600c40320300c4525201c240026a560343c4040c0390009240455031405031074902c0e01d000e164649002055112a110044408211901000d8411205e2140448004400604021050b4482180ca807401600104010310001d862091b484c2801d1b0b00103000642412058 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 470940809 1250 470939559 470939563
    0x1d0718050d060203011a0f0706020903120f191d09220b0f0a0c0804150621050c040911060d24151d0d02040e030a0809070812030c0a11 59
    0x24150580d030b45600000140200c0302d42d00041c00c1b80041c11100d00c0e1828028212032070705805a030130010541500041c10315110b0380c041208901c030b041a01002603a80c14203510090b12a40008561781e180311040a468080341d001c1c80803010440b00480c81209103003000e2040000c0b80d400201560049080b9002c80300c050b14011070404003042c4603447c012420300b011842c85140306002056041c034a424004074101407544860440d402c280c0c401e170309000701100005004060545500320a0a54000701c42208040b0602c502c044000d46c0108140c4424100e030106010039203040441c080c1c90001214189540b50801c0b40080802c1c10065000282c03002080c9603900d4030301410501400525403614003444004601914008030705803609011400c101d1000d80c075206410b16500b520702c82c408071070b00c2c2030a5490b0340d004030b554400341754240ca6440c00c2544019241d1502a0748404075441100004100c002c8006a2111680d46444900f8215a16801021800c1d44040050b20402c450342d41001140001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 470942059 1250 470940809 470940829
    0x170c0d021318090308222012011b260c131e0503160522020d02070309050904050705040209040209041a121f0f0b1003050a05011d071805 60
    0xb11040c0800c0803001801e00a0403840094000314250400703c40019405103c040c2d0f0703203d1154010300503c1c40384a944480c00c46a0010721499400c003540c5828a90705e07201c194069548101000a40c0c49a0785054004640c0f40020b250b410000482101c1c8507068540c0c40c00c4184d034415561180c00e45000c8020091840d00c01c0143c3c4502d0b4080c00122305809001420352802014100a80040844803039004141c1c80080b05031290b50b0140003040d440c1424104000d0207502ca1a084190030365662182000490081d8000c500c2034001500300a40440e2a113014150345015540017002807408504000800000354400707100789603c039900f0410349030903446901a54030300303a1802d00c1c1b0030b183c002c2c0c44040c08620307602c1d20f61403090b941111200d500f00f0301028a0104034003011403800100c000780006414000d0800d00b10107548090ba0030001412150725801c00381c414100d030306080c070160766180154560010b03411400c0099001100004600e40c0c82041e010140615101c0402e40f01603a0700042802005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 470943309 1250 470942059 470942099
    0xf030106170d02061803071101120207140c0a082e0911030f0102041d06030304030b1906060906050d02090316080307030806030c030d1107080d03020703170c0d0213 72
    0x201c94801e040351034050013203540c0400d8030943c0901e90707060052407a032240308544006000b1110148c80030416403240300351104c545800c0d04115038440007410603130600c1410010600075440b440703417640f0396418801c2d0150210f4600b070b4001d05001c42c04041098040d80d1740c0014a5414540312960301c00c49055001d4460341c1e034040d444195808685906140c1414240c402d1100168010001007109480500e03076203151582c0341d401144640c0341c1e84006030840c41035500c080c0070128500144a088183c4e0b03902c4000046c0070070410442c05503202170070349540c1d150380700321000f041040c044540062001d170010541080300406503130030041480c02d5140311400c6038000b5100f0350f10210300c420800d1b41084501d504400110001c10f4003100500000350340d03940c0700d003201c0c04214440014203400303074003009000060322810060b00e414401c42076008000303406c480c40a030001000908603541b065a0803450f180034040400700285002d110248040c00395001e0360b44142070a1311004e00150400d1010381d2807249a03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 470944559 1250 470943309 470943313
    0xf0e0a02190503151e0f03030706090302011d0601030b01051314010803130902090a05010e1c0506061f270803030f10050117070c031b050f010e0111090f03010617 71
    0x205101401021320000c010f20700380030340ba01345a5803040c08120450754419950031600a40301c03680a0700440d045010307003d030007440a42400c145004241c0c040d0486250401c0b0108203180108008042d555200806c1c4406802c207582400140502c0c20030f01041d06c4485010b0358046007100d4604000d0440c01803d0b40a21190f42011410f0700c00b44950080701001803034044015401d02c0d48040026540440e548200381c180b12054501348401d880e16031748000c1c0d440a407100302c1103103622410010740b160821541a4450000003114060f811588854a20110a241c0e02e00003e80d0b03248810042070880d41a8a49101c088003c000034024002c00045204502030142200b207410040340300400b1107c5900180e05200510002e0440004c006044e1b540c400d9141c0350000c9244071a01701594503031007030304038003034140383c19058801880f0340000d24000030314184008001d901d00880e441400c0b6036024a6924041004000c0894140350604080ca0714140050001591035a80e6071600c200c1c191400001c400c076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 470945809 1250 470944559 470944561
    0x19030b0f0d051609060b0d0b0f2e0801060c03110f07142b0b06040603061802091008030d0f1b1d0109030c0905040311060702010b04150f0e0a02190503 66
    0x20b00c072041c010f00003481c241c401800001d0804080c03200310300901e8a0304000d1580c0c0c00c18040c590b500d001e5031107030b09080a4402c0c1e0070039043d071800c401c0c0c0c520303035940d071b080040340103e021000144552250b50495081e40c2d540c1c414480d41707607412a007030994100c08901034070403198031100004041c030448008180742e0460180d021181001d111280301a82080541110140030114802ca42d0300a41c144c825801031505c100c07599005c0004000341241d4101901d054644080d100c4000d814480769100c2074001c9a210260f55102d00101003c0080c600408081e80c000f4449071242c400290405c128081c3c0340a8007180c0c0f80c141761302d4602d003186440c04c0e440001c0c1c0150110b4004201c0580b54104901d020b02c0d000306058150b45448003551807a10900120f180c0d1800044c091504c40c203e0b00c060203680b0019030703031075003801c680083c040d04c030b070840c458840e9151a0807034600314040a81c1808640f28110700d620740038944001640c240c08000c1070041d0103a000c00614119078400c006000d08404252110364403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 470947059 1250 470945809 470945833
    0xd14071113062c0403080c1e0f0901034502040903080103210f050a050c061f0801050f0711150c0a030c050711190e01080105040506070519030b0f0d05 66
    0x31064200300000483c0030408144000300c0d40c010052640703c5002400079581d205150100044807505203201080400042085050140514014240786609a03401d001801760a1100010500c407940b940c00404c603e8802204c0c0b080440504083c0801464141403100002c1d40204055902440c0111700245840c0014030800c0254000d000e003c80d9504114052015400b401038100f2103501090024800c01040c0c1840700c0b441003007150602000c0000741d54245c10544041d80404010003081c42c1300c0b407014007000c103081d40c3c144200c03403040010900c0080c0300e403900c0609441186102d441401d40740505029005110712900c1c81c2c5010b01d007244d1400703640300e80352500201200c076901034940801c8070410201c0041002140c2c0003036000c208407091400c4070805200314003c3c5510f070788601a00d0710340200018121350190f0080c1d109074000d4054420036070303c001040311980300d19044e59410200138640420464443d034043d44446102400c0354029201440000c1c1d03244030002e8003180d05034070507441842 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 470948309 1250 470947059 470947109
    0x80a1a0103030f0509041d010b03010c051804110702030d0e031c080f0a02042c130309030b06030118140c010f020304031e120206090d1407111306 64
    0xa801004604100455046640040c04a800180c251040140c0465685450396841c0d20030390b08041c10307031505800381041440a90107041031408082c400d5290060125806001d601254218418080c820004900351002c000003403450300708500c1041002c4c48440c1c01a00d0810541301680c006403249458002030008042c5850704010f07003161540e403d402d400310001d40112800ea040058044480f24030f680700c8031048000c0c000d6900a50b104583c91100c01c242542240c152100d50660004a10181d03452503060048410000c00090004182d21010404074028185a6400200040012401c400a906c1c8525040300301750041c0d40101907480c20b486e140c0300c1044000a03070642070030902104100c2030b9000c1c1d02c80c012480301400406403030882d072056140c480903140b90154480041c424050810704000c1d6145802c03a0740e4142c0c0d206020011031080d000e6400000d4444000d40424075041860740c54450a0381c0c040080c64000c5203180e24a100000d05004920282040348d900548080d4a070f24064 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 470949559 1250 470948309 470948333
    0xd080406050606040b04060e0d120504380d09021003020910020606092208040801051006020105040c03030c2906040606030203040c030b040215031905011d04020103050a090c080a 78
    0x30300c201400c004c00c004608030582074038216451801c200ca43c160103080460440101000010041440d030141c03400440c3c3c104018200341d580882c81032020001174100c00c004410802a5841c112100c501043c2c000c030030140007440d401c9211400451004d44550206d49842d01c44410200866000314010760384e802c103c0138240ca48070303a91000381b40509111011510150024142505240f24850a01040b1110151004034141d220443d41d658a96448055000f00420f940c0f0883c0d18240306c1d000903c541c0305002d5a406981c000708a03012013481e6503070603201c800010344c0032650808102c6100b0041030540c02015000f107842210104646484001c000031182070f50085400c0c103105100f8000820a203130320480c20360382c0c04034a44082d92106d00000b48070f035018100c0c60858200c00003c000e8900143c5401d01801a500c0034103100c41e0343c892071009011508000c50034440054080080d0156200341c12294010381202000120b5180d507888200c440a01900400301691115909500b0011021290 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 470950809 1250 470949559 470949571
    0x30a0302180d0c061b050a0b0a0501060801031721041109060d0b1605040503030a0507021e01020d1206050a0b0403021c05100905010f060e07140c19060e0d08040605 72
    0x2070320256580741d55500c1c0142e56401000200103040e081d9a103080550303605e09101580040840d524480d0702d02d0a01c0458008441029000323051030b000007070050007a00030505803039001841040b680b10600586115401020311959480b4a41c103403101144d815800c10b5015900850400488111140600044510181105008105170134551012904241c8040d4203c01c4020360020043d02194017144c090155402c0650f16000010382d600065401c80010319541c0c1c42910049110300408116051041502001a01503000707a590050031f01d00c00e00711044807040d04200000c0c1c00c0c1c1c940e004a10f40740c3c40c6800c21801071034002010710079031402e42c90688070600341d160320281d10a07007555807d03224030841030503040280c0c5801c88501084002e422902d12050f061030108052070b503d01490780c000c1d01c00d07902032011030041007a0780b0340203c1081c200c540d245480401407541000d03080703450f06c001c66045010b0314001d81d50b40369290300b0b00e002d01442500ca1000d0360b6000d0365080a0810404032030303014101d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 470952059 1250 470950809 470950819
    0x3130f0813120b070813170706230603070b070201083d0b210c09040906020301060f0206070504050f033406030e120901031b0203030114010305060a0b0912030a030218 73
    0x4100305500402d9004031b601da40094605501910551081c0140c0189040102024204200540d00782a510030614045441000c00006030b200d100c107054036403106010b800c140e803004024034409135018401090300000c40f1400c42d104948000c4000038110780c200305194507103400c01c401020030190b001d00200609810f00e0032510f088007005060122003230f24503001c41e0340d0b601400000c4541d40d6040543e12080e1000e8401c0c00000400e2070080020342c0240503000100701e820b0b0800b0107192000a81612405e07032a05d45524241c145001c104c4540d0244024030303032600c41d03030a80d501c014600700000405e03004020900b030b540320807d41044251415540045003050316025409001c41000914009031201030031040b9603500031a00102c0182c1f2038448008090f403c0384614141c69a07001000f14129902c140c010100004d420004400303031281500c1642d40702c0194003080c0003800c0240000d040541004000702d000b01481095642540c004000c0d01c00402c0c0d01052402c2d43c214440d40410003480c2c103d803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 470953309 1250 470952059 470952061
    0x5010801050303030714190918050601080f09030f0f040501030605150f0d1113140f0307030809041418060106030e06070806060904021611030303130f0813120b0708 72
    0x2011907601d0100400c17017801c120170085165480c0c5011030441d6281595410540400302064001402182440c4a00380c90101100041602101642300340c0e03000e280141e40d20311680d11440140004075001500c40d00c00c900003045252011004c810060207811300401c0401d455500e00300000d01154417941c4004d00a00319130740380c014070107210b1045030703402242c8004050704c401c2401c15100090080c11410403400100003000d8201c0c040b011440000c440350052440c185030a10014062031008610840b50140e120f0382003840043d00d0301014010312180030f4030000d00410f440d1090542c841055503080024203046600b181d440c0d1051040901411903414140b1a04000140541d5a50b400424100411111070301040e019512101161803080e001001552543c425a003900d140c1810031808481400c83c036420603000d400c011090702d20610361354a480100e42e1480c3c641c01900050654125006041006031007120310503024107801a150124820000e0b440b00c0c6050100c1c07480107000d11080c0b001c000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 470954559 1250 470953309 470953319
    0x3050f120304060510030c0803070c0902090109030201111005180f12040320060a030f050117030f0708040302130e160509281b02101b030902030a0b0903090a05010801 73
    0x40c1100e401c16840345001445a56400100c01d02519a03000100004032486000465210002c0038050301ca006415542e8038640e180e40c654103d200300d4800034041613201500b0800342d0300424056641c0900300095031507007847e0b54500c40031900d007282c0307064410142215280d000d00c2d04025680c0b5401e41440140540700f40c43c40b80f51600d0145100c0200700c0b4441d0400400c20700061424207a090802030325980c1c0b101541640500504011002ca81c002031805d000010014030758050030114041d19000b85141401d4820941d429070f10a0f0340540320510100000801600c502c0c0202e4042d02c090640024012145031889090451105080c0440050b40100380450b640351030b41150004122594210b98000b818007820181c0d000d0b84003148018070708415900c00c00c03540611581d00c0c0078168203498452036003080220448500c61481c0c0181050540580b98450190740070301d00d2503000604a0b031207014540c0e40c0c0840d05204603940c203440d0f000070541a5280c00c150003440042c00003401c08404a41c142 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 470955809 1250 470954559 470954593
    0xc0804030204020d02160b0901150f030b06150c0307060f200a03090f0c08070f0b04060c0f0b0907170111030a02090402270114040501021b010212040306050103050f 72
    0x10301000c0e1050350b0000d900034210b011035049404c403038508100548100c1944c1800b2013604001c13110b6111701d5081000e8510b95000030562807003910f0600110540190664a40d00150f22001f810a1b030405450800300e1510100b48002c1c0201c0c40c0c03084011981ca9019190070415104e2080e29943c1c114180480d09046d21500401060741b0200208001c0e2100010041280500100305015004851070100d0005001e401000b001c16070b40100100c60f24641c2d43c16034410380070800d00c00c06004000030b20041c041e291081c421042c810b8011102e0103810308064650a82c0f0302c005032086030040e40000020801c0c10031081c03031000191080002000410010740c0c00c00de0510004181688190b03001403038078429500d59069821200c4044541c581131040100a0130446105404250205030b108445041551240c4221401e441d010303400344c41d0908441c95503000c0750502100250550041d2000004a0102880540002c6004610202c0c95500d5400d019040105800303260149402c6140003280004403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 470957059 1250 470955809 470955817
    0x3031404020105340503030103060c020c100c1106030f0a0510050a0302190816030b1014120a12030c140f041703090a14031c0207091104151e0c08 64
    0x2c04044030788504c0c00e414440c00c580008210858146003003850190902c200000614140c80c400c030300c100100310800c05c040ea40c540c00800c40d10b50140c03920304400382a0740710b914501009882500e4940c64002e0346000203040750021901491024890010001d00c0a1640a040c1d044003c50001c5240c56040201040035028240030203401038030b104002c48000d036200260320004090754815a030b40072800700b0100151034000d01c8151507090b480f0010520828901c4441001c4079070005601d081c103050203041c007080e50f00e80d0107400801c2c00350f40c91a0000c14030409040302c070050ba5a0340020b40d1600c00c0c4016140b5140b240e800d003900501880381c2c0c040b0440c082c0440341a0703648100600c18600c41803000f06e103144140c01040d5000200e400000480001010050703001c9401103040d0f4007c61101c031000006140340710640401640a00c801700506040380e0700c03980302c45190344407180c9442d032107a8021400300c4c0401b05560019607410509204500440c158002249161800e1580303c0c805031102075140c01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 470958309 1250 470957059 470957077
    0x121e010b13120302010203190b0f0d080c0604061b0c050705041805010e0607081807050f191202010f0216181410140301061d09010e03030c0703031404020105 69
    0x500303400c01481000403000402c1010500c0c03a45401d00e20b8024085e41080d564a6915001e141304504404003900416420600c054039070304521a6004c10480e180c00880001d84646004102c0c00c00700840c14000b1030f11483c0500c50202e4010050242c182120b85580c44080030001f64031070660000c0c0c4049030003021070300111030104600d54241c004802d84424807074000e20a41c40e12010641c202400301e82d640c031412254441c2c1d00c07035544483c03201060a012103002c100d103401014003480145000000342203041d101910600021604c1c242e8401ca0f120f858000c2d840b0030100c40020011581d0140340644203c3d00c40c40508181e01c1d500f91a03103203034540d5008001900c3c06900c8080c80c013030b040382d0107007804071000e0310903140d64109088448c00700940c90082c640ca4410904602e55141014041c2c0344c102c4010340c2c140070a41140400b02c000902c03014089410035522081b0113507004800f0009540a005c802c00c1843d03072500d103071070b0190458884000c407005280300e1104010143c1c0e00305003070300c00c488 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 470959559 1250 470958309 470958329
    0x9120f0206093f03030a091a040c081e030a0305190c0302090915011709010923010608060c12150d21090e01030204050414160303080c0702061611090705121e01 70
    0x800b55107070880748c1c400042806211140103170204818020903a1500c01120b0105040d915400345111000001030b0032400081c220758010449201c43c40d20a0b407000354408a45001805882020814070f000c3c4c0d64801100000607401080e203811519002c406181c201710089034220361248028006031094000c1544202d0101034000080d42c650000c1d00092301c595400381e106155a002014904040351504100d4400b80d0710301500441c01e9840002c6841c09041c04000550401044410040510038010983c1000c411030000b62001c6071106201d450101d0700c1034440c501c40c4484c0b0b10180b903225850119440c104203003860304000031124903107018152501a2000700325503546040503420255003030322690480c0b059104a0424000f600781020603240300c1d585501094841e100c12081d107016020b000b9500002c10440309400684010403c1c01c090f2203100300b00e00ccc00e01c03c4c8000a81d03140041740c03188045200010300c0107000c1013003002242d2201c1c101c0c034801f544440c60500300c0810041401020404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 470960809 1250 470959559 470959571
    0xe06030d0c030e191e210609020402040e1801090803070509010c210f080906131703070518030303090a0201110a05030c0a0b060109120f0206093f03030a 67
    0x4940f02e40c00140581601130300009038074002d070b0003600500ca084c0c40303540081300300002a00364180000940d9021200e4917190484004003c120b10210406a51001c69146075509403020042c4c44030b00160005048100c4070b0130861070b0101001544489030100b40300c40780d1420f2585030000319510192500140540792041c0c40741e502000694800e80c9600003d01440f034041178500c80400c240c607101d064241f0b140c1d81d0141a082c010000c0d94034036400d580302c1c0926007110002034501984c05480300795550241400c100303103056200c1c20880070761082c1c50311000183d00141a8171145a600c110100390b0009900442c074510300b9a000a80b40c2c80841c500904002011380f010100703417000c04c8010130264000c01965558040300800d29610a6281c4003120a00710a40c0090000c3d801003204904455024583c0f544003038103981c6440c0c4864100400300d0b8020700500c80c10185440703200e03540ca8400c5004141c01d5418041e80c1c0f1a440c0074910740b04855403403860a1f5114a12100402034a8000300b0300c1e00d0208072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 470962059 1250 470960809 470960813
    0x70b0712020f12040203010c110a14150109020307181d090c03010c08090706030612030c030519020d020f01110912150915010b0306011707181e0e06030d0c 68
    0x19100b03402004a080801107801d050030b042501403503008034801c81c000c009482c4111400d4442403d44401003000e604020b850700c0114522000140c3c1300da00080c15500d1921005200d01c650240070303006612903650100c10400020b801008441c1079860107500b404000e440c0454105402c401d403256050b100300000d0214107240b108015086800030010300070b004003840c0c1d01009101060450305880f031032098031300008602e4020b03c1010203407144010349070790201107a1410345401083c21012410800b007003041041c1180060400e81c03081c1526400b4290301d518040000b841e200401940d210b10340d00d403207002c0c0300e1240700f41c0480d018004c2c1501c0c821070100038010480e0500800700e4000e28072089510810503440c402040009003102c07400742c0340d2002d9895030840f4107980011222640401d116000211081c0044000e07168440c03041e280c150401c0c09096040400a446507115414940800b0314550f01e040c0e02c024018058484900032124078a40000020350b540c20b2401c0060920140c0c00107001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 470963309 1250 470962059 470962061
    0xf1005012d050303030a090201080a020a020a0308090304080a1203050906061c05010e0d0302030f070804020f0f03010902030d180506030402130b01091d1e15040c2c0306070203070b0712 81
    0x6020080540e1780380e00c2c0212110000d0443d40c942240080c54001c00201c8030305082c4292890f040c410360050020b50591356017078030000000342001c44248801d001c0011001c02c10440251624400c04405000901400c40503068031000740540f2002d4010100b041025100d1031000102c1b50170020908141c01390909290780104a80b4000403980e00403101480c44594068000714080c6d8a002c107400d2150f40c94100c203d030104020b4800a501c000c04100d071140c685404120316055010040000a40302416400a46041107442404e00803481c550009010380d40d51440c514000e000c01c2d00c2c80344c41c5d0315250380041e610510b008041144242e0352401e88400d40d109014400103050101d00149400d40d880704200c7e64201e041710b0b0b0400c1030005512001824216018060190a41c004640807101001c01008041d1545049610400440d90041c9252202104600030a2000c0b80b451110f001402005d00d414224000c11030f8080d58410850240003d400320203c5610108520b04580c1c41e41203440000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 470964559 1250 470963309 470963399
    0x9010c080d0207030f020a08090105070816030e01020106050d030804020d03021603150b04290f10031a030a08031609030609080a02010c08240301020c0f0f100501 71
    0x6840d8490104109031030740203503802014854040d4072400615682c4880480c0d69004c450700c000d00403481441049100d50040d8017a04c801841903003140d09100c06000e0012a04000e004144c001035042d884a01c800e58081c450701c0007403c3c00342c40d24200780c6440c2d14003401200010308000d0140113900200d8044c54800e001e003e00190034024480540d07540d90030b0680d81c40c3c1031400c404a51500d080703049081803400e4070444100c00d01000506542d1250520114468410ba8200341c0c0c00c600480c40301190340e51500a2120829119200043c661141e400070385403503102c40d07080c1c0b03000b07910240130b207000b250160058076488002049031021044140c8000c4801075038661009091500342100001007181c0000905013007100b590023000b100607040e404540128041c0d4414403034100a4074941d0101911210b40860300324043d00161405101000092416000f12500140ea4001e074400e0000c0e20010b10841004151120080c440b075414007000070741c21130b10401400440b0004504154801c01018210 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 470965809 1250 470964559 470964563
    0x51f05012a0c0303110102180f0316092f2d12010e0f10090e0c0a0b04080714010e0405090a021003061a120103081612170a09021509010c 60
    0xc50000246800b002c07045050104501003407802100181800e414426258000101e0016114154000040c080c900075003041003501401090121030b25130700120000f200510000c0b40010f84151890301c3c2d1002c00c10b0480010b1301d60102c1200d00da035860004c006940f503a0030040c103503c02c6010340e000070820341500c0c1c95010b022804007044810340554411001b60403a40743c02040c5101340c0d580c804d01220000c080b071f001c9940c81c09100003484070100d19808450b00703c07400c10441b001021104c00044e1455408d520040144030000f0303041c000e810b828015070b0000e0034903202d03d1440300301c1100041c2055024008a601a90343c4000042e500d02d020400e0742d40c3c89401410124036080034003002005000280151090a00d03000c20141209018000300c81d51680d02d00e005048690a550700d0341a5a4442602c03690024282102c0b00042502109030750110881e5403100401074081100c07031260b8600042c800180c00e8640402d11001d6280d034000080007800c41e03406c03107503100140c80050760b440c4541c03000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 470967059 1250 470965809 470965877
    0x80703110f011b170f190605030f070503011103040b0c030408040b07030306090b03030f040e090c0a080d03050c03010e15010212070b010821120a06091a0103051f0501 73
    0x84410600803d100080340070307035a80d00d100c3c03150802803181408010a4401c0465040301c040003c1c140054030071108401044502c0c003049190781c40000901d405800151406c2c0ea40141c081000189003d1007aa042e02980358406411441c0c00d4440c00107109000f070141007209000400103042100c40e504880281044810554441c01c3c64100200100840e02507016030614055003480c0c40d00d0000141d40c1c05418040c8140d207460b00708805a18a9480a0000e03001842199026180741e51a8183c0b1000383c054840205001c40105000409440700a082d840000500308018002c004219480ca544810a006070500304601440100e2501d8040b0020900410000c01c40302d00300414501e40d40e04a5807848100c0d015a92000342e8030410816001106001100410641c00b0300c4401502da140c1c401486140012801e1760f5480305000e44500d040e09490318040481e10f01002e41c5c02d80b003802c0d0001d17000a41e18010400500504104102c1c1d030048170b050055880d02c0e401440d1110a01085c07007580104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 470968309 1250 470967059 470967071
    0x106050901030b091203220f0b01080303040c0608010302060a0302031f170c0402030c0304021207030623090706080714040503010c032306030601052e09150c080703110f01 75
    0x40400d0307000410384100c0b029020342c02c0080400180c030006d90340648040720f4100080c104110000412118a4004980010400c65883c000c10110081c940c001c103030311005541d40385080e1403d64004000c0da0000e0007801000300040c405600d0300c40c181c0b100d010039410300681c1d035203544c100f001c540c17000081910114420741c20041264150300300103c0308042d80c502260b940c2040d01c0c1c104000e9020888503100084000e10004025151403c0105038101802d0701352807201d5103035184c40e8140d82c1c0f4072008050100e844c074003005650030040e48150740301c0382031400b4100701410083c0040c02c100016000000f0403502c0000342108118101c1290010003004008100142d06810041c02070121841d15400e84003000c0002202d400704540000d11440004024242070fa00f003104220f0364004004c0f403030403a43c1c0c642d0a07a540c0c41d58981100345d4400d0b65500d44030f1040386864918900d0911450b80d180030089108000c2001507402401c2c0c42c1c1c02540340c1040c003c2d88031202001c628290451103c07003032940c2011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 470969559 1250 470968309 470968313
    0x111222060c03230a050c070506090307140a0221011515030501050a1401030c0302120906010f050111030f030912070609020a0f140405040503040518270303041103010605090103 77
    0x5400964442800e8405200201c000c4031000048142c83c40078140400c0307000300180901d50380780e010720b0f403041180300402d00700521a110300f40380550490b6901c401d40c3c0700141e0350051111180000041c044000c0080401880c0d030742c0800c86e00035014006c040000b4600d100101c07044429002681648580e1843d108044d83c2c4864036181004c44443d540301084ca00070000c01d450900c60404803d4440000d000d04003031000d0001140180301545003401015801d2010913016030030480514000c800940040215504101d2a1302c9480041d5128606010f0000b40022030202d000c4107642100c6400600c0d69269079030040d1203418058018095050f008002501000f00440760b4043d8860a0081e503215400035140c4c80b0b07003500c01140717000baa00c10007030003504146a460140c02141d4050700c200141c908143e40c0e080480d00c0e000300e44421540066408040044260011302c3d180811036203408003040d0880c4103655144c42c0c2c44050009029400c5402002155032800d400943c02040c0103005280c096940b8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 470970809 1250 470969559 470969561
    0x3070303051509060a060509012307050606010302032a0906040f090e01090201050f0a1103040b07020f1c0b04060624031a010801090207050a0506011403070911122206 73
    0x1111024495500c103500002c240c140b00003050320072400a803c91141c20304244083c0c5051300300004450401900e005501c035a40794292920048800424401e034440c5001e1800e50300780340380202a1410184148100800b14686c0544900100050190580d46003180c03645007103d4807411480580100b07000400154450754403446108036403441e04100048030851107410b01340c0701d80c1c06000e40060810700406003003500c4800100000340710f0381405080d00c0380b142c180a05580055020a5500002040c9001075040c810300d050340c0b44404a80b641d41e0b031007402d1030003030744000f210714058003915520000504104c090390040f800340c41c0c400e114407400501126481040d040103900400040c1c20f14610410010400700d81041c080c20507100c5d1a41c0c1d13800c000110000703400101c0c007a50300e4880e004c5c135100400c00501402d400f9161303640010105001c03940505103003505591180e251300d451f003550055045a240c0c180d92003115010524115505d52180e546d0011219010903c103421010041c0c0c400c101c22 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 470972059 1250 470970809 470970811
    0x7080a0e10020a030207060f110703050f010c08010305030301140d140d0f0807020706120b060f04090e0706020a080313021210060b0406020712030504080d05070c170307060f0b030307030305 83
    0x45034841d062611800040b42c03a207030010340007030241e40401400d00c04940618281d0b0313544581e40c500300302e003c08a0303054070740750828550060360b0b10340007a03144c0c0316400402e004101c075804003810040040d51456039141e03668801445950703403841082040070003a964060503801502d81010984d240194001503080e2038040812088001c543d1000c108144d03140506071140c803582c0281c0180c003c50f03103001003e80f4030411851141203400d540300700201750350faa608064032042e80c0034511181c441c0c1c2024001403c0300c0029800c1c407110f6100941c10800346500080344031880d5030020646031a80c582c0b0410b02e5040c2c401e0030b8001d41c40709a032641502d00d610002000ea030300e500644000d210303555407a1034a00c81032040d4000c1000507084514203200783c0800f01e00c956403c5101303151031407a2a40e01c0000c0c60410b180c0c250503a0015400084403003d01c070140c2c01d2500641a015602c1038a141d05083e103e47d42d1255110081c002621094140c038008241d40c0030001002c00942980e644210313078a001030041070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 470973309 1250 470972059 470972087
    0x60603060f0412030902030c030307081201090e0601090b1c06020a0818192108040c05010215071209050337050306011101020405041802030c0108041e030507080a 71
    0x2103250005000316010a415901880c0c03c81104001c6442042085010b404050700907030300f45c403a5141200c03030b5450404c002c1515034000c503503e5444040c0b294602201c480107911001c0c081c0c0c1001003644c4c24020225032181100c5000c2000651603030141d0104030103140520030341300744840581c001000c1c40f01c10b80050041c3c000c0b50345d600700c155403031482d20403c0f40001040010315078401050340c1c2c06030f404898a0031110b406829000d070303003803968090412010742421030744001842000c14402003100250b030040c00340400340042c0200c0308030032020402548004200c181003004003100350840c0240d0f64088181b047e00102500c0c0d854080c2c403c41d62051005e01708422694200d1a03015291002c0f280b0080000d049540d43e081c5192100d41c0110703100d0300c600c001b40006550801c8001b85965075441003103c010741c0b40c1c00d04a410f000e1401058100700b01414440d060114850820000035041c1c0d00c41404002410305c0c801c500b90b41428111690f01441c10010310720701d8009003803030b13025401c1691130082c54 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 470974559 1250 470973309 470973313
    0x3161809290405040b0106030b0105090907030903090b0315060a030b0a03030203090109052403180616030f020909010501110304030204090b060a15020c010302341e020f0f04140405060603 82
    0x3640510030b2208a540440700601400c01e10401400720741c0c4a17030403101d0f48000502d0140c3c1001c4c000f20009209035070585000c008241d031160310a0405030011800d00003001c18058403819071510f135502d98001210707541018071890001825000040c005d5100b0151204083d00c100e030466145c0c0b40107903803030b44012003030350206255110000390761800b60050000c0c209804c00c01a144807441204c41419040545810703a59400207141c03211a0200300b0202d1712400540d4818014a1202e078400345c00c503440a0f041c40101c41c0108044045500c03004081411203070203203440c5e9030311106200b2007810760103907402c02540503040817010818040311054850107000115038540149544103144449031940010400168120380032034101580250f028003801c00b849100e00803501024800000041203180c5142d1126a40280d040148403500b5068003480302440c01c42600300c103240d000600f441210091007031140307c001c20144241e0f12560400b08110424031440005810f0900d0565251441100c42c0b42c0030f8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 470975809 1250 470974559 470974631
    0x18090c0809010b0607111005160c0e0f15090402121b10020606010c0813051f030b01180b0d110f0703030b0a03031b05010b031204060305090303161809 66
    0xf51820390103d0340070035480106e2403050700c000300a000d480381d030008107601803141c140140d2001c1111600c628103414880c4035a1002d407804c03c0c9018603125006080702c1c42c081000303020050140115012007244060458550b0510303079070b070710001e444c0440c4450190320b04d01403401798018414211512081446007180c00100118a61600301c1c1e640d8000c0350081d001404025003880030a204900a0842a0103020000d0746240c40720041056401c00500301d0180c8242011101307082e035407600c03a290109109107440c818180350044a41100310300c5014080c2c94a00005203021003030150350010315490400d0980903200c0f0703c824452001a0070280c02500800c0c101200805a4541460b1541c20b4031f13496161041d01c00300c109103c070300014101508848035913031150383c1082c03942e0401c1007214038180000710f0f5a4650030000000c05594000e42101001e50050050140c1c4615003801514400c0d9103290404c1c0d1075400d5404005140440d034010b5600610f4081c40c24589000c20501110389200c41910b200302c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 470977059 1250 470975809 470975831
    0x207170d0b011704030801060807020102070c0f05010e03010b060a12150e180102030112030302070311060c030114011d09040203150c0706290f0102010212010b071208070f18090c080901 81
    0x81c2c203c040328010001410b41005102d02c0c1d0050202070b0b08800b00e4030006050108554072180000c3c1c0c3c85c0c00c50309188010326000c0101e981e00100c580c400501c20ba00910001d0601408146240141603141c0309201704218215010300103940300c500c82081c2c900a1030007603507440d0b60916903800240c1d10309140500448001d0368042d014001c8a0403103002401d00300c030f410b08688084000703420594007141000500c0d9801400b4a404000c0706015070a1208866601e514200240b200c02468180d000e050082d180a000480fa0142030041050f10f070580d44242695654400079041000000c40754264500c01c0c010710206c0c20000c009040e4691003000200015511091050441d09410050302145800100c0101e001c1c28425498044540180005414050106161010f84000340c028240c406000700d0091300b8032411251041c802d41c41410140c001d418000340040c42100341c008410b0074040c064288071a04c040e101e2002c3c0080294400c1081200100c0b00010541c450903248031504d98204451104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 470978309 1250 470977059 470977097
    0x51504060e0a0b1b040915060905030f210f0703030e011d0307120228020910050a09020f1b0d0806030d050a030b190f0816050f040207170d0b01 63
    0x225240c00840091840d070b00c007845a030300c1440e0440f08440d0201c003170000040c0c3c03c200b80140544c040004421503151424050002c00c1e441c01c0e540014030a40c00b145101580c0100454407100b80584201e0300441c031a944c507100401d40c03040c145049049100020130805040c0d041d406a51034810340e00090010f030a030103407141303400c6202c0508120950000c01c004800141615000c0807601018019a0f0800421801c2c1e007000140024040c0015241620048114540041d0140d880b1403440400d000c00c1d42082e02043c1905602d000c2c1222040d170004503d4006200d03941038a00e40c031446460359000d81700d85080591104c0c510188513000c2500c0902081803860007288180310740d640c0b566860f040807039205007180508820321f0403c1c0c1088201002880d240980c1011130050245543e07800061440d10005c24904484849080341e80500690300340300e542d42d030b20100421030304c04840242e21a0365605010040c3e2000644041c582080000d1101c05003010380c0042c0c00e4440c00f6200c000d242a40070000c04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 470979559 1250 470978309 470978323
    0x40e0106110a0c0509040c1a070203070e070503070c0c1206020c060711030a05070318030f21020307120e0a0e0601030b2b03020f150a06060f0c0b06010c051504060e 72
    0x4043c200c80c0c00040c069800c000c03ca1036031181c010300d01281055914151200b0f45091300080190a0400107401d0040d400c0400c1030800601c031510204d80c4600e02000014018007001d070840c1d0401c0381d100c80300d100340506111040c020b0000a02590b10319055407070701034000c0d0722226011060f4015180000c4265001e01454244e0f035600f030340907500c1c0c4501e005080321640d1005100700d00744040311030035081040b00442d01e140950320a004c03244881e100d03030800400b402003d0341203d681c4044000ca441d072055002c030a8810b02540070054481031080c5401c02d03915400c80d68840b68111400c00740001300c1c181d121507894040c11089e00c3c1000354082c00418403e10072b0b600362200740d10041c0e000d004400c280c10049407207601c40c024410380c0c41c21038445d002c4a0034480c0e95044c03032a0600b601d8040c4015a000d501c00c040007003406060501c0c0b45041418090300215a50f10081c00244107080001c1a50b4044d0307036000101c0380d0000503100c1c0c52441600202814009560036a500c502d00556986110030019890f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 470980809 1250 470979559 470979563
    0x60e091203100b071b05091b0f1b0a0b01080a021c0201140a0504030c0f03051c0207120804030b06010c05121e1810050a0f0e030111040e0106110a 64
    0x40d022110182064550aa001030061568654005400039220342c402000c2c10b56203114074150400c01c0d141240c0145a00e50b580c104030704ca21640c2061000f10074812030111151600000c1075520307540581c0032403005018032401c0880d00400d14024400060000c644800d0b0140719a02c100103d980301c01e42166540f0314140025000490140303d40716900440d003000b11920b10515010081c0e1071400c881c84125007250401001103607021405008210b2412036441c06080c424071031074a84c3d0300d9500c5081c0e80744200c0403003040308841043c2880c1983c0c401c0c0450340c05004801c3c1c1140c2081c109107000c038503035482071005940646814010504541c42518809401500540100106280c030748000c00241d111a941c0c03186880c10104100d08a50f03508064000ca079403881031549884585410300c0050070007941c903001040710402500201c250015640d103010900391070040c2c0b00c0c81000c80401e0042c0f148484440003840c0118000503d62a01500e0034180c0d1595601c4800c556616a181991030141c4180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 470982059 1250 470980809 470980813
    0x509250f0e1c02190f090c0e0d03170112030305090313051509040f02070201121b0c0f0203060103141c0804060203060d0209071e020a050c1c05010519060e09 69
    0x80c141c041d2400010241c040b00c1215000150214140d0002e050076060f0b941d1801180f450340740400450303004004180c02805d815105018000d1740c280020520918240d0003440307407101000d0304007814401e008000b060442c44203180f00075611050b244802d071405010490000723040000182034000003200780c81400a84100b01e031400742c1070201b00040e00305001a02c852621040c1f04041250352603004140804404e100c0050341d68035036000040010392101511440c50f8100089030049003003030301c041d002c44d2842c1d20b440a407607402c0d440c140c40d000950180181d4503204100c0080103101184401072655034601c81102c0d00e04954900420f00c00340c044401c0300200c0c0841000601003003140d0000e40d4068001484810f00c0c2c2240e500041100134284c03200000100f603401c2820355480107503690151186240020541c00071306903109562030041e0010700d4002c28800f2008031030b00101c01012100c0d1070303021000340600c1c9082510150303c03205c4000350351107583c2044800600301640c0c00c021070051403a540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 470983309 1250 470982059 470982077
    0x200c030303010b1e0316090501030c090314071e0504050723030a0612050106081204030b06061b1009021003020a27050a0b0d0e030f0318070509250f 65
    0xc1d540825130420798803502c9641d40030504c418541c20b03031401144103030071103040058000100c40000380030103c0fa420181c1418507040060035102e8214240d64211790740a5207200741c0c90042403e550500d903040d40000400350b046903001041d450703445c1c04c0c101522819a000c000940c0d940340211002484203c515122801c200194510343c1101002160702c041c40400c0882d41d00e946440c9000c6100c0702c6172042e9450b954404080c086031070140b00da100740310601c00545041c40c0c00c5886202d4401405032080c1d00c6400b0003c0d0650072094489007984000035100e0940b40700e2070500200c48041c142c0301808070300c035010446504940c98000e100390f8a002d10f0030303943c003a60f901105ca0707440105c0e41089403016241745d103408002041d66070458000c02900c003405580d52108c2c0e03445e52441c1958040348200a01c0d81007401040070f4542d1100550303601c00d203415900a10140c00100103814130000d0303041103410004800070810407e4101e20241c1030031524102e0849001080b0707400b1101201128004400940080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 470984559 1250 470983309 470983319
    0x30f070f05120d0f0b090108030f0c12040b0d05010e070903021c02060a030b040501050301060302150f0405030a20010c0c1202013e0a020901092a200c03030301 70
    0x103000e84a441081103491081c14002100c816421400c415a6055254202501a107045008041500c1416907014101d175042203103550b124040c6007a81f2020102c00b00d01c446407104100103109080c0c142848460b0303500e48030310780340100d944040d40c40d125440c102000060484846041103120f000d2603611490f0b024110f40c20800000003035812600ca220340c003804103016075500c80003802c075030903941ca0004034541c00b401440203540e0164402d91190345481030410158840480f1580c801414450031a901d03034000c440010140910b411150f09846010400000c0220b80703000512040102d64048034241031340001100c100020402c010070f45051410204281c0064900c1504154414100100070200384000c203810700116010620f0344010100e40403c196849158802d5000c1c1c0c180058090300c20a03802040a0540601c40d03800f94943d9180f100002e0010040410011000c1078040c07416800401e000525500301e28001c44022456003400c14480c2c1ca001809588844002d009142180c0c070b40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 470985809 1250 470984559 470984573
    0x60516030509030f030903010e0309130e100f02070201080a022703011e0504140706020606012105070e04060503070806041707021009030611090d12110d170702030f07 73
    0x804120144407050020b050103a4051000d142400030200066844035500300c1018256104000380c4680342e041007100c02c0f80c07034441d40901d84800c03851b0a004601103100c001c5191800c40c609440002072480c1c10201c40700100035400808034035000341e03510401c079250501524200d2182d1a280070321580e44c00741e54002c0d00d440040b030b0310103030f88014000285240c07480c82060380d84028110f1182c0700c95650041004000d219584500f40809200040076428140003010b565000040c003058180204080041c800d0f040082078105012030400b014041c1c0e091942000d8948181080c080380314030700f0030b003001c2403e0600240520442c0c7e443d40040019846940314510017215500d00f14400ea41c040291102680b40d016009100b26400c0c0d982003256451400e2440886440d940c0340c080480b020021400d01d0341c2c0b0b202d4500304a50700444000f000b8021800c1c01d84020001c0d02c0d100f126401a400a100115000b0315010200b141e0222002c0180d039a00720103d8603441070030340020800d40b041c82100041606 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 470987059 1250 470985809 470985847
    0x1a04140a06020a2d08030108010e0d05031f0906090c0206180705040f0603020402040f03050c0a15050a122d0212041511120414160513021210060f090605 67
    0x900e080c0600c480425025135920340140094541e441c0000040020040900c999070003002c100015080a01892100401a20002d003001c0c0d04111080302913a64500014195001007410382010861079a0385c000a40240041e1030202026024400000e0300c09840600782518000085001d480c0107410941048014440c000403010041c0e0780f51310210050f115440107002800440310715a01c107030b00e1443d115243c0340003200780740c3c090800354400304000001d40c1c03102c1403203140030f00f440390700d4011001d8125142d0503400180300c561414050740b8071007a100000c40100c000345d6114580f4000641407094410391140f6421045181000c1c0b0000f0041940c0500400704914841000b1404001c8211000c04503040303481502011201201400304025064031100f18680b5610058074016180c1010110500d64900c1940e006101c0c80c0c254030141800c9a044070901c0c415920a000a418840310621401c1c1482c010840821001d0750191207172802400041d0131601290740e0240b600460640318851154 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 470988309 1250 470987059 470987093
    0xe010516121503021e150c19020609040c1110020301030c1a040905090d11060708060907020a170c0105331201020a0e04060f0608040605040201091a04140a06020a 71
    0x42e0200110040c1d5500d14480360a402007820f11207000c035804200445003000d11000020074600700001d0480784408164030359508400100d1020201041c00820828420710980d250310170f14002c00c002d5926000304070a10340050500888005c1585615080200e110078040909910180e8408010517061007a075440185804804107080507503406e05241902c0d41990408440c0e00000342070f1140c940e0181c0c1210384558034070002d10160402c1c21015141c6100034200500806c0407a00140070346000300180301e05903500c4403400042c40c02c04012616140c0110201001d0f0b94240404907140c00a00e200c2440c0e01c0103800102e5101c05044a0f54040f860204074495400410070800d1000f007180a10140681001c90340b40c0c080c4468a801c01c01088a142d0340000094690018050004a9110f0110b0b0b601076400f05002800751220f00060364004540da1025080304400300482e85040b0740a8003038401c07102190807140c000003280f410800707032080f00d02600005034002c0d81480d000c05c4841c0d07000300b46a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 470989559 1250 470988309 470988341
    0x20109260703060b010e010314060907091203081603021905030a060306020c010c09050102010c0518030a060c02160501020a08090904060605060307050408190c0b030403020c040c030e01051612 84
    0x164505240074104240382d801941c90a5860300c1c001000e58010440110310071091a04002c40c0710307411030710900008041d0405e4010898980007600761303402900d10001a1103000f0041c50800200d11f00181555011202c281540039020341b0420614000d00a440c42c031440020030041d55180c3d003900701c80b107030401042d940e5010389032100000810560701c000e0600510f01e1001040185040d000036195040315070043c2e0441e8513001000c103100e0b51250650301205000c1c03c40c80c0c580c103658800603140c025003440207800149044c0303503400403c3d00080c4000d4100d08015101e881c01341c0c1d40f001640c07105c54005000d00001c00802000111380380140c045a803103803003001c001415a0700e810105030241c10071501c0c02e001c980002414801084100089000c0d0003d9110003d000d589070b54030340d001c034a818402c840340b500c008000329007007600a001178044c00c0c001910801101980341e000070054042c5945500c030725464000032541890407415040c0c40d05840e601d502e6807a403009913041e00100302c6030300d0442b006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 470990809 1250 470989559 470989619
    0x30c04061a0a12061401020d0c0c05060c0102041a091f0503180a1b082b03020a02030c0307151103090c011d0d15061502070320042c0109020109 63
    0x1c01d0034440d42005d0681c4c0c0008600300d070401000a850864019000e1050121320a0b0620019401000507410781d0f1094402c0c3da203494070086100d000e8001c5400c604010880d80118010407200b64004c0c140003641111380b03450035080782d41c2001c03680f400e40c144100014800c00000b4113002e458445102c1d6001820100c500740c180b03580b210441034003510300c5002c80610307081c0200200d100821050b034008d500c0203518000076001042e0200c0030704480c3c40d200c09140d0041107160b8218000e1042d036149124a0055030350301d0185180c2025240ca4259003104041d180c1140382501403814401d40780b160107900f00510b207020f800e00064840b80301a11102010409028040c41180c07a8004260085803044038404886036200d41920207070b0381143c00c0314000d40743c2005d203906015070009840040b02d41003440d0503140049280e07440c1c020954800641d40140c180401c0c450040d00290001c007107280700210f00c0b035a0841d1450304500369203402001030b0004120344024444a1080d00c0d09218840644011400c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 470992059 1250 470990809 470990837
    0x3130b04150f0e120c0310022d07081206041d030a03050903041505190f050a03020304110901030f0302071e180b030105090615090403051207020a05030c0c030c04061a0a 74
    0xd00031103401d480c1c5903800000317812034503007810040c11030202e481c10300650512a00844d11203001c04298542c00c040c00340384403030081440702002150410751f003220006640d80b000c24244c08100c5801d9602c58012031410342a0200d64007070503004820500c0707150282d8600006c18904801a250140130801103001c00c100004030b49280149c020000011a1945900c9201d079801844200300f810703c510050090161500001311350040c21240718885900700184c4945950400342e212850410a490304500140c0005c001d0044080007820034600c60386c2158090307922190003140c844241c1450030003d00a000d028000f11680c051044c0c600d9035515000540301c1c1081c40020b094501c2038405110540102c414001d14004560700844a0b640650f0601010b043c190350090503441000d0810140c400480c002c99500f6109105420f03040b90484126503c403080c0c441c201d51030707002942442c1d20030711400c000081541024003901c8201c03555884c10310f101084041402960307a00581141d01009410f130340c2074075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 470993309 1250 470992059 470992069
    0x70e070e0906210c01180608010e0a0608010603030905042301060f020114070c0b011703070602180a09020a090608040c0b07080d050c030a050105120a14150903130b04150f0e 76
    0x1030148281c500800041d04c2000024143d210011a400c4558031024002d11030b55400000c1d8074115030316a0740c800c90b5a03807820f98200003000c1541002e0ba1030350034400b0010502da1f00c0207407801a18421202085941c0c18502e55070140a0243d00c031080080b00031004021481c000ea0300300550000301c1c00007140314a01a0000141240103c4558021910404907002440b5440d081140589800d2144000e000054500148e40740202c450007401d0301e40015429200f481e01c103081d05040300014084000103a100d646100c043d40114003024001a6004e0001901074828144a8000d07500444004031082c10425090201c0d80142c00c1519920804c00500c09019001e00c40c080c0700c2d0203240601b544038101242d000065940c10f0f40000c0c428643c0300300a1074142004210800b0450303006120090001c884070010341044110f180000303141007880104814003002000a110303040304008854000341e11240070b06103074041d03030244035103d051401758411070380d002d80e030843e160202078208164440c41c4440051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 470994559 1250 470993309 470993359
    0x6040f0b030403141608030402060d050f07020c10050313110603041a070f080a0f060801141f06020331030f0b0a02180d020619020d02070e070e0906 65
    0x46600e000000400083c507a0100c00d00d46454051000c07070b4070b090115842c8100c1100f4018000d08506030010101d021580e552041360311070307141c200c000c0c0700c1850030018244004108075591005809031030038025072031a08624411094449894a03402c41c0c841d1540049880c039281d00841d410a050f0a0050040e41d031503020f54800c84c8146041c400c145a5040a941450030242c482404d000c50405d40c5095103420500356540726152200001d4060a0244400e018102550140c0d085518101c414443c3c21030758414144605034180c1c0c0426200000f0302c00e8281190b8511401b40140c2041c08064582c040740d8a2440720900c10b81c245000103442090364041110741d5500884042d041c1928800030010015009540051028030841c100322240030745240b078418004066201d9640550b01000715904d40e010b48a0000080203420841c04c480e0b1006035803240715050107009803080134000036659651183c0d81d0311032001991900c9400e80400d0a1100c0c1200190070558045410407019852940740c201d81 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 470995809 1250 470994559 470994569
    0x306050a06091d160e0a09020102012c1204050306070518030610171b040207062405010914010207030201141603090f081605240406021b030102090109030305030606040f 74
    0x110150040490f521442d1000c001c40c01c940c0400c24000401c484840d9000095201001280c04100c43d2020b2004074010300d010b030340c00848112078111003244104d0a40c030344009940751030112001881100307200301c4e45c0d000d144241a4154041400200000d2096000d00494142d46204508421000000a040c00000c44803619502000481004030341582038540c403410181e5005058494100c0084d012480080082c0b9401141c00045400800074264880c0454140c2c070810b1011500001d4400c000718004c0344901400200380e260040b030300c181e000c40c541c080c1c0d141c160010804285140d005441c1c25010000c2e41000b00c0040c4401f10010740c2e22403041e20b20718803030b41e20000b03041d0070066003801618043c0c00400281d030110303001c180020420103240c82610700444101280da00640f04a82d44a284944070464000c000f05000401d02d0300002c408070907920342054007030003071440410325080303002daa181540007a062507010008240980004c580150b8043c10051806440c0c2d904441a83c045d6404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 470997059 1250 470995809 470995841
    0xf0602070305212502120301090b01030605150304061d16080d02070803040b1e0414030114160f03020d2a05040609140414010902030f06030105100306050a0609 70
    0x403080110180903c82d80c1244807211030b8240f94108001200550b40c44a01c0c00134440310061214810700e07008100c0320708a60380404800d9038a684401c40300d030160868200c02408179041000115036440c0240d402269074500a000a00f15904c0362603001c0078000e94284580341c0043d5101041c03600c0c20512040b9508840c2c681301a400900d0001414908400544102c04541180c40144100b06001c4101d1301151070b290051a2140500210411080c0304000c9800c1d44800000c0c0000e40d01c0082103602e814640b0031002002650b40258141d07103034090480c5c1240d01105c41c50b48850069005005c04100da47d618034005042060258201c421111400042c090f05184400d240d501071000c00d0080360040c00c01d24201c1d007481e2501c000541400700324062210406580c1014841e152602d030f11000100fa0340008103e06940d6035080c80f07009520940f00022100150710002d80c80313040501805001d1402407080b01c0a25181d52103c00081a0181541184680b1008001a00c2400d1b005600340621103800e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 470998309 1250 470997059 470997067
    0x1120c0c0c0b030112080903011b080414011a0402030415050910180c06140d05040c061209080d110d09060c080f0115050c0f0111032706130f0602070305 67
    0x80a0802090703070340c428010400c0802c014442c0740b040c0c1a41c03175901e907800401e407501e480c60240040d001d00041c60708000c0f0815680d00500c80a940b1402031801640210101d8042d40c8041500c503080e1a803650846840100114442c119030500e94015070340940540d10714000703400407482c1d48003540d03019240c100b0154440382c42d0502c0000e040c42000c501007146c42d004c001c2003480f9030355108140c0c2584110011f0200d181d2000d0944520300044030190061804100120b19080c80c0286044915000b004000b590104018200890740c1c403c000035150000035140c1407810004448014144008440414040521940282c1078650007074601c00341c481c041c0420032101d4440f0040a140c0014001c40745a42c19400401003844042c038840f000c030a4518005548006c0d29a160385044514506202958a040041c0c45000140d0004d50f0252550103140c501d0403041e08544e4100000d028484001034111002180c0000c07091080c2181c0c1901c0b0719013100341c0c3c00081d25001c04030303040300a0035404100001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 470999559 1250 470998309 470998313
    0xb030105160e09060a050409081207020303072007090f0b040f09030201140c040e130803070c170f03150109380325050d11090405220305070201120c0c 66
    0x51242c4082e55003940d01ca04140f80c01c1e0001561520544211070081356190301d640103200128044404203041041c21601074101a00025a01e0340119001e10000308030b4113559040310a0344482c800c8034604c01c001405210708010307a44000389145031088250701d550303408502c02901c07a80141c581d4410b400c500041d6100c02c9083c0a030959840c000c0da9044003216500b009607802e020700c10740d0700740c4d1004401490555a04030001500b100d541001514411012042240c40c2d0340c400143d0007064890141914108104501c1c0309175405542c04601c8011001e0000038106089141c4c00d000d122414545450f00c5c82e5039091400350010a0003000c0f2200c02134105041103060344000031401115422040d0b840c2d1300d050102100d0181507100d400102c07012203024011810305ca0025208001c1444500b00301080203954092141e501005006010b40d042100164448088181c2c0740708090882031001c0c900a0307944d03000c403010f5010344001c90600402d00b0740000401014460a030a9240607241e0140320703000c41c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 471000809 1250 470999559 470999567
    0xd0e0c0310150f03081207050714010b010f18030b06031c020318011b0f0f0206040b0714070f120606030501140105241b03090d11011706030d120b03010516 68
    0x1540107031030f0395a030800040002401040c201e078100c8812600345652a1100d81c070803255481035000140c6200f41101c16010b06402c10b600404c100c0600340c948000128103428140e0300080c00010420103001250402c1011030b81d803005050f4000c030300900340c540e54011911b00040c0d107801002d803100140c1c00407849903240100286102203800090070104103915000c40480d80c1d03c0320140c001080b025580c11010104081083c101024680c000e02881d1110745541355070341e041e00407840503162400000a001601800030407854191802084202015410321200b2030b46d04610100807100c480d900c010000214000b84590000d00001c2013510b40d00754540b0040204c610388031913040c1c4280307040810100384060814100c680c10003180c3c24945480b0b18544050b4114098074080d950061b41c240305410030091080c81c0685281002d80362007106450030004100700300340446420360164490740441d00058000c4000c61000452a01d000c00d49003080e40200703003590000d48001c4603050410014440040d04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 471002059 1250 471000809 471000851
    0x203070905070309050d05070b0c0d09060e0124050607030302160c0e0f01061106063309120303130f060216050d110312150303190e09010e06060d0e0c0310 68
    0x2c6e514016040000607100c000ca840f9010f015110240320010b02900d1640151304039038032103600a1010005840d807000020301074518007040100c020045220340803400010a080b10560f030000e0031290078500d940d5800e400035071041480d070310709507a0341c3c03001c00c002441440d44402901006043c030019041204414041c00810f8210320b003400390505a4010aa600142c03ca9120008541c0c40c0c46c40e4506071407602d075801180d108010341c40d0901c0e214070844942c02c00141450b81041c0c1381c0c0c907100100e0314071658403404250380c25003240c5040314121001c5452002c0e08400280500801450304030304800c482c3ca0340140181c2103c45030011440390129540005090485140e014003a40c98291044d2105540c040002c0c210b00b500c280064412a280c1c0f020000d4520003000c400b81c0c90625a58001c020f002411080e040510460039400049649a41800180e0181601600040c00d012124032030704058074a51010079031a01c644410b1441c941c2d41045900101c204d078a000041c8850354105890710180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 471003309 1250 471002059 471002083
    0x702061303060923060604200a030203150103060302030d080601031805060a050705091507060905070b130503031303030302070516090f14040203060f07050c0d0e010e0a1a07020307090507030905 85
    0x1340c5803101e011440010074665030158040320001040b0742c0074a65141c821409000303083d00c062010540b06001901980210300628404000303034110281d50703004605603003203800000d41581000030394256041c010b41d141908984141404184c0c10100c950b404c010280c1700c0e20584e0183d000340c0a02061648500c1b5581c3c00002074904146811101d1010980040091010700c91440b000180c10050280726440000056803100c01d4400540d907419500110b81c002c2c0c0b552140d15a0802800541d6260010480d90100d079620b4414283c01e16544042c0d00942001c601941c9a0148840c10010340d507004901c0380281c90f65840020b071000020224001710741e8444460b4883e40410400e0202507540042c040c0da002000c1800340606556819046840c0d0007151042c0b81c0601c80c2183d819003103600b00c403084680c00c50a98440180e04246000c00c03540302c0071485000241044503698017244581b08000f4108180003400f01c0b0701065640c40e80701d044400858402d00042d03a00c40d40c3e0020450300f03000c240750f442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 471004559 1250 471003309 471003353
    0xc0c0a082d0315041b0e0f10020601030506010603061508071e030203010906080a11061b010603150c0f1e0c020607290103210c0b0405100e1f0207020613030609 70
    0x43c1d02c0c0c20850003c1914841c10045c03250901c0050179503a0741f1040e4a0400c0c4000d003a58031400b4031410065940c4400f0b02080316207004802c00450707161720a116550466000c01c3e200d5000e404400c4068a000002418090400c16004024200510b0000702015420310533500165658134000f001c400b00c4400341c10414150700104400808250109082c1c921007004540b01551000310000720540c12849407a0500309509010000007484802906039040810001044c0818040604204c2c0c0d103041410090010900d00d0710440314001c0d0f24034620510501c10704140400c4034864002400d9500250811182004002c035140030464000c0da44400428114100e02c0c425411580d0310f00c80c0d0490201d40d1900350400700300102517144243c42c41c1d00c1346604008081d85d42d061504010b600c0722074540c0c124440a0411450a01e00e010008084080c502d0201882015492201c5c10401a51109030141d034000d0303081c000301040c19000407441c070080d84078090004d01d1005600d0314840c01c00641012603980 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 471005809 1250 471004559 471004571
    0x5091806120a0302030d0c090e0a0606030b0d1e23030d11041d0a090c080114010501020f100221090703060f02030c04050d06090611070303050c0c0a082d031504 70
    0x6600001500c648491b00100070a8881c2824000c40d8400855403042010454210a00c844003555601001c16510300b0b076014030401010f03200703008140c041d800c801004650051a4000412620840000558494140b03591407010700c1c1d580c0f050820303810040186a4100081810034102c2901c505101e9500c1d24503200c0c1000d180480c107140d8200c104448a041080074400a807054266034000072201d64001b115810039615600c0080c02000896038800403000506c00118031513000152139071401d50f00d04000c04010542181c079001a4212282161200000e820314a804155075110389116410440090070524910300b4000151116858982040341c41003050003003e141442c11102510400e503a804011201c1380382210007400c907840701510141c5400e80550b4000240310041841900076a000d105646410711506181e1080b040d0880c0c16038465040d444c00151480080c00742c03105050703001509041c40b81c036020008080f540210318800e1000040004140b25401d2001400d0b1007580d0070000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 471007059 1250 471005809 471005813
    0x8070c0605090c03060a0e19030c0f4e03090501060608090706030213030210110d0305090f030f0304030f0207030f06020a110c0d080903280c0b0c0709090305091806120a 74
    0x7200b98008107502c0c549a000c11003010b2500500b14424ac3c96481504d490050009050003060b1424020100c4059580c011090020554007243e01c2144140b1004800c0d00d1556070710b801c4003915100c0003c2061644034680a404a0028843e950081c11162140704451400c0d00c4401d0620b2002d0b00442c1c01d051041c04079028a01e40090300700245e0350705403244201000048420ba074040035182c81c05c00c0034840c8480d11350081c2e81c503821a90190780750380c2c11101c4c04542d035401d25071030740034003601002c13520b0342840000c000c00c5c800c040200c99165580199881141c0f25150210542000b5038255100d640024828040d540c0c050740e01c1c07a18134040005840000d80e02d1000a074809107660f0003800e170004c080307600c281550382485000310742e000c0c01c40021a0f41c00664290022400c03e104142c9584020000010306110398104569498038100090a103003410700c503800e030003400848019400c00000b400603d038a502c61890008044c1a0400c0c1d501c601d01d00b820400c1940724410740101c000e0b801054030342d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 471008309 1250 471007059 471007063
    0x2150c0d020a050c15190c020102070807060c0209041110020102030405070e0103050a060f06091e0509070518070905121c020f0703062a090801060501091508070c0605090c03060a0e 79
    0x30082508464040114201c013000e417110340500f001240e814803040312a040e400d40c001203450040c510030317003d031140d1540c1c1d03903241501d03108240300c0c11012507031617a005001407400c4a0050303070092003103c4490800030142c0106181c0210a014000546c0d030000c2844180841000000d00400ea80c1501c0b2001e0b41c110758400340c42e17a0389044000c01c9542ca60490b1a042c43c250341181000d000b2a44c401c20103245134040c0e01c1e0098440d201c005202c2e61078000403c03c0d54030041000810768402a111100e040d1400107007c40340b0900810060401101180121b0301799130300e01d0000d00b0020b0207002090b01585c0203ca4051411680009070b0565114052022400002080c45400c4980180d00011180b8405a103c0c804000549219008a203140401e40580b034000540209035180000208120f0380c03a40015914500b07a40a003c800c01c9103a100604524441c01031142d000302545404a03806da4595500420780700c06650411080e0441c841c401a81c4c00c0c2007050507030100507194140920016041619 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 471009559 1250 471008309 471008323
    0x15010e040906060801051512060c0921031303120905011202161502040816030c0e0403020a14060105121b0103050903070b0c0306120120031302150c0d020a05 69
    0x14003403a2101c0048061000b00d60001e0028000d00c0d00a000f40d26000c0c0c900c01c102c48884910342d1040541101514403894000341c070a00c141d440c1a00d0138604420386040210356200e00c01030228010f40310f0041107080100f0f0010b804050b103403d80b001c00707503400c61070519416541d0306802420000008005c21080e070b400075900b030040c807007400c005a4800b403d00c3d60407451600000f0180514640f008642404078182d030040c401c8602c1c241c1507800e000c0d6400c812212540c0d030b601c0f0103040000c05190501c841d0184030b2529820501ca40101d6039000e1159581c100c4d501211110b0460a4000c080100218104084820b070605c441c403020300301403c00c910006940140824a0f181099680e000003201c0040400c00c84829581201181c0030b02e14103014500d8042c1d01c1100c1c55400b5075000601400410814050441d1950038048203000e03644001511000340d0300000d121229824240c1400c00150b00d62204841c1e54201c00f50107240d9459011015903e0b1402404007402198041242e103c0800c4003c2020303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 471010809 1250 471009559 471009587
    0x1404031215030c0b0a0807080403020a0210050d051303080601090e1b07140102070501150b0d1e140604061208030f060103090803090a0209010b041d06060708070b07081501 75
    0x200c1844411111401c890035400007070494001400c0410710550b5440900806038565989800503690340800312a03090043c0c4005025905c4406420018985035646400c600e000346055420000011000d10039078000742c0e04002a203000b072138840141648041070319800803080c02c240d100d042c60944242c039400c0009242d002c5400c0f035898401c911044000880d0710307141c0c2007125031981c145407010660007503000c1181250158030300f82170901ca1156803007122003110944000d640c20034802c1c0d049480030b0007481c503981c401e0b21001e80b035404540c4400d1240f00810740c2e41d660b0780341030f5180039002d01003142e142c4d0704035800078082035450000281c00d0070304682c1c0c0400360843c8a001503c407032005030043c20020f18010442c1c9000b00820254a0340012110a0540201c03085440b40e641c0d8040708203640300320300890005804c2880c49801603628130079401c1e00f28402400441c80c040e45501c444005820215040701e280c1c0c0440c090000302940522429000b00e4100460300305007280c4d0001034003025040e401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 471012059 1250 471010809 471010811
    0x120203071b050a02090f151e0f0316060207080c0d0f0f0c030215070605151e0f030a080c1b030601060c02180c091e0906150d020a020303040614040312 66
    0x51504001c0140200740081d54054400e1460f410000029030220004131041a02848001f0201619243c64403e0102c03125441800494403982c130b40078860285c43d6010020b41502c1440301000728582c08170b125600401e000d0740a020000e06201c1100c2c2080c0d03c3d8901b86224451010195002c40d80000132600c01039880f01c881100b200c0c151030300b65060300e41035201a5000c110b2501d20320040d0300030300052804901c240c1c42040681d60312106401c4440d00040c2c900d40044440610380e00802ca00d0a005005203002820b0702c1070200c050002910304120018222413505010a009484071740404c89541c02d80100c2c00240703000303128400840c0ea12181442104d08111410250f2400e546440c40c3e240d034550404c651000300c52501f0f44061929502145105014a120b810343d012810805118852802d100812600d2592184400c105421191000000324643d0400c4050400c0140d440284041807080d0040c41e142c1c5003608182003150004001c500c004404001040f0020f41d1000c0000b241e5004040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 471013309 1250 471012059 471012107
    0xb030706121a1842040203100b0309010b0301020f1b0a03050a030b061908150607050712051501030303091109041509210503040213060b1204020316060c020112020307 73
    0x803510044880614204244003205455401d103401c01140a0070713070b1202155006070b03082c1c40c0300c240802c0744030407210301540000c540d0041c0300882c000401150028400030011802d0b4500d000000c0c2242d2080350001069600040c400c140042000398000c030107100e4601600141c50141c4000e41a8820724161301c040550300c844481d15962003105541003048011545134400c60304101c00b514502013600e11103c83c1c1c04013002071a55251050460740b801c0c0c1d008002c0c1140743d150400e0580c2c295020760b8221070740e00402c0001c004101e500c0407079038001c41c0a643c020801d030441c0c5c20901150b00f0249602c07406100b0700d408000204059a6040f4120b005803100020f003c500e03030a003440e10003130705a04c0c4044014418140c0c04541d600c0000f660207140205c4501d00000031400385402220100e208240b1425005e0020740f892031944d0704d6003584103002070103036400f003058070401d4811203106800075408903990148407815035a200ca0344606011041000b1031660070034040152141360208649100b02500344 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 471014559 1250 471013309 471013321
    0x6041b0c0803060d1e0510050c0a080408070b19050a02251401060914090307031413031704081902090112050304081002190216180b030706121a18 64
    0x403412101954000e00c001034000034000c50914682c5c943c680c10f0310b0364841d0011506640d00284101406120400307441c43c9001070480d805c2c2d0326007900178400d540f940c60511030b10300415014503407144075007003414260100e03032002d88080d01203c1005c1c000030080307441440386046010b100384c000c511580500403488196641071600d49540142014002c13941c1d401c1000004591000e5000b010200710610030b55042a40c88090403941c0f0702400c030000d000a0005044862203c1b4844c008060400c0c0c0d8a46032160300f61692901d40d202450826056031170040080d04012200c0140680040414040d440312014403860f0006200808180544011030200c802d040c020054104201c130010a441c0040d030b40203041c4030001000075007101410242c800040400074107a41e1011400c0b080581a10045010841c24520b064504409450103900e40641e1140101f0495404000b000d0040403e0355540d0758542c052400b00c000d41d00705880380c00484c2c0055907119096550454920224041c20b0036826540d40d03a6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 471015809 1250 471014559 471014569
    0x605040b0315030a060507030c05160605061504030f060b12060106030e03071a010510020f0d0c0f080d2009030304051003060e0106080906010e150d150c050306041b0c080306 76
    0x1c0b40c2c1d415894801c0f45009004c0000710b8002510403400c0740c604220034411044199401e100e0301040101d403d071420140700c00101e269010135008040513080561060030442000229485608107071012640d144444082001902900d021841c05489284880000c40e4a55135900c0c0180100001d00d0303240c4dc5004c1149604001380c0e188540c01c1054220401092030696104440078040d650050100b00d180b1001c00c0e0001400c5195400c00d04000d10b143e00c03c001d0125080c08540a00b00c81c8025500c0304107002ca02000042d024044003106e00145581d44526030440000c289101c1d0822407000303125846050b038012083d102118400e0392565417542c0d441208030b00030050f94201c1010309007060004240540d00101e40c9200f000c4c10b2048440c40c0e6203039509030808820444000c1898900101e0300c1e41d4a04203145501f8000c1e2117001ca00c0340c0404602408025180300741d040000241d404010001c1e946014015485403074921681c800700980503150041140d1b07004a0003820800d030000200b01680c8603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 471017059 1250 471015809 471015841
    0x70f0f11130209040e010e060411030a0209070206071d060706090f0c03080d0e010203060f0613080f101811150d021b0c09100510110a08120a05010605040b03 69
    0x5018450050100308104029001109414007451424a40300d00e818014031070249280501c1f8020b00b2103a0b079a6446e802c000720400c4a69400d8050380c502c0600503140d90034400c0c0204517640280c5281d2900320f100410b0011200d0034141e10009508613a811520b13680c0c2141c03503081c0c111102103850f001c0b5082c00790007a1303800c0c4c1d80100000d5461000105000d1148050a00421a25020702000c070b400e034916800e030f010a490303481d806800c540c0b207a5510b02d0004001c1a075110700304000400c00e540d414015081c1242d0200303011068200f030450300d009203180d114040c2013111074050100c08043d01d8030f807038480c16850800c9a00130b5018124090007c512003042d00e0034100610400c0d503030740c05d1038891280d0408600703c040b401072140300001c2c5254600101c0080c46a5103603c107034045140382504005d506458001c01c1401d1000320410036010417010720020540c0350103403202a40c0c40551441a9080766001030061008502d401c005000aa6001303040304c048503800100152240ca40005407400c0d000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 471018309 1250 471017059 471017093
    0x804170f0d03200f09060702041503061a01050c0d0302070804030821010806070e13020c0a051501170601063912020102040509190e03030915060105070f0f 68
    0x31440340120007041c2e00d0342018007024a05040000d000308000018865805000700204920805001c111902d04000300a4803c05000400100706068070100689406080b034000366401c1e5120f07820682e000f043c42844286041c0c00f8680546054117140072651607201c5861400c003015000140c210520070b208043d01e010b903401004140d07807585200d002582c0344444140c58424400810000281180007088a92142642f41c54500714003000c1c9081012940c0d0030303045441056800c0c04030f00d040d542c081090102c554815130003032410501c420141103000005070b0021417040c203030150202d076184000c11124111040340c2000d94982c0350003452001c100802c0102102e05442c41c8140c1c0203180303401c02d98242c815009040f000b9004580003412401d038881d0340101070f040310780358000c501908150450052490320003100010410701ca02c0d03004c0d041d51301c01e443d07409655000c00f1f01008040b0b03005000341e801c000c3c01d00b0228a09201030f1786680300c0c0040880090009103d81d0700c18001e2180d04a41905142 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 471019559 1250 471018309 471018313
    0x10e030c1807091502010501080105061e0d0201090f090608100501050a0308030a060306020a0201020d0b1009031407030503160c05040606080402060711060a11060105040621140a08030105030d0c0804170f 89
    0x100310f13a0000c4c0289800d01c50b070582c40d0700300070110300c01e41030041050305510504070503595803038040c1080c070402c44043c800490401c001d0300400a000c00c1c1c081d14440107042c1c402e1010840501d4840600d14090303460446506030b03890907004104c1950365185c034804803030344403d5458a91323541007500402420582d1010b06207500001d41c0c0901280e0650041a03215881da00400c004412402403140001c1501c1d00341000c03030310540c41400414103a400702d2000300f01c10001c9881d8507450f5070f1b689055412500301ea40c000010a1084000c005003c49040040d0070281c03810440546080341c0148040f0000e04060b00422000400d01c1c2802030712140311401071005000160380d01270045004103c0880000c00602d1806510000308407440c0c503009104c11150f0704000c8000c803900d40480d00000350f07400d18080360b19001c1101547c0c60b4100c14850449407a00514150391130790315150506050000754034803035081010403801c0f83c00041030303101510f05072608440c0700384054500d42801454070307203072801c0d401c2c4034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 471020809 1250 471019559 471019589
    0xf16110a120c0b090609060604200a090302090a0b0616020f03060108070518061509060409050a0b0f10020d0e0406050904060e07080303071d0d140606010e030c180709 73
    0x103681248801d203403144a0a02200543e4a100504d61a4682521070906582085001c50032a2409170401100d80d00c0700600d000d8004c0c611041617150b9130003076040d440031650304001001540f51052000d60300580400c42401400c1d600c100140715841140c09030886401004020700a45d140e0004203125401c0203011101556151047c0a036100d01ca442014800c0e44000d180c031060b07000005266004540250a0406103849050f0313407801d40d0020101c10345c1102c414800000c42e0a01401100d000701414200081c0221260007031211420521403514020b00c11864544802c2d40e0009004040e0619890000d401c2c82d000d500180140c801580134980c407052072400d0005109040e8420400e14416008a80e07805036920031944c0c0700e00049481d81c0210780c08400010171907000200c40568007100a12002e14520380c0d540c0d0b1890305041200d114810750103d42000752658000141c0d40703c0ca0340840003071210780d074040001020340003801580d502d00c1946802050b002d43c028108840502030000d405221 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 471022059 1250 471020809 471020843
    0x51e040c05091e1b1908060907020c0904020f0d150f0c0512040f02060408011a0406060c03090b030a0f24090b1309060f023004020d060e071e08060f16110a 68
    0x451b4161242d901c079180883c0070030a8107000240c0800001d0000d420b00840382c1c0d50b5000c118280c1a401e10b00e5403c58259800c1e40c001131a20111500310041d000c000085031a680d0010300c08443c0300c0c00e00c0b0f105002003042000703500d6291000380d5911651200d1513418003460340c03010030014062a03025842941c00c14140002c4402e00310202107404c502a1000c00801d03a0b5004116164100c110005d008207900d0750090020a648000659110004080c0420703041c00c60b40c82d04c001c488801d01c100010b50748070500c41c02c3da200030303410190040c6a10392041c0b11900c0a0b40010315510b0f003101c440c2c40040c0c1c3e99907400c02040b800b5000f0b0072500090140454458040b0000003045044201001c10000398401c0701c0541e02041d45991400345402601c4400449210380d2a0310040510304c0240785a40b064000003e050803030a56449525040030352100300092401c881545480009030100540b1881c05040143d0b0401c0c1800385007a1001d03d1614080702181300030303083d0401c028a0809400d07107001c8201000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 471023309 1250 471022059 471022067
    0x14030601020a0c121406060603160323160807021b011115010518090a080304060b0d030504140a05130506130f0203060901080a05060703051e040c05091e1b19 69
    0x103001030140405481c0941760b1800b1075124902290141d83c000c80500100b8040c505854060040e40c0c5182000a00025000c180d00b4203000800403080d501000802001141c2c0304514071031900402904061078203050118002e9200c60103100c0c7c00422561040c029040c46c1e00c901c0c0404006079513441500e0005101c1c0005451508090054a0003428443e04850b11403103017105a0744076400d80c0e00542455000c1d555801e4003a0b00192080c0c0d84582c0f6035410304415501c41441c80e64040c4240c071242d03651840c10b5a4049800b4584521501c40c5400342000c0102d626129907254840024200000d90360361120001001c0c800c1030f114101d416450102c000c6441000d9a0041d0f000d59400c8883c40c025a90f02c90381c040e59014030f01c00c020640d4103d640442c04040c040d400c420b070000040202d00c100c0b40002011544800d0080354160303100440388904000d05c1c100952441e40250705c541c1b01c0000c040d818842c0d5508150042c4c9401c40c0070300010402404149190705585c0c1d038186440b6241c180c070106142c010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 471024559 1250 471023309 471023339
    0xe0c0406170c0306130e15060307210210090b070303140a181b08030a09050907020604080a080601020703080403030e040f05130209040203120301030f050c09040314030601020a0c 78
    0x21454150541d0503034021840501d100e000415100e40c42d5030758080501c4075280900e42a40c41a6455603e107803000328003400380039640d1300d5010b40c81220786002400c145c079016140c0d00003198a120703507070b041d001409a224420300ca0354054450b5020f200b024101254400140c2e80400010480400c800f4101941034004100300032410f04546843c0e00c0d00c2032620121044120b418155592207003003071002a010030030001102504011021140c2c0d5a040c0300b904551125042d00f0004480c1d10f402d1040e4603046000580140c1703684010980d0707142a80d0340b052607204a00300d46007803001000000d8000ea10800c400302c059a0300c034101c00d03101d5545c3d140181030f03903801c222000d10407070031f00a1103c40a101403240c10700c00d6222841c5e00510740300030f0b0240050500301402c180c4c0c1600900c0380340c448100007040214021442000740300d440251905119040950300d0301101d03c10f500e941c0a00c000b10b58082c0b0100c069020b8000c00f90fa5a0300d07602c0041c4c1c64141e014500800d2403545601c00aa2044244248 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 471025809 1250 471024559 471024569
    0x90c0c1e0b0f0912030601091403010605041d12040302101b021302030405060f060f040f020d0e0a050d020615120c0d110a05061204032001020d021c0c02060601050f040e0c04 76
    0x955100013142e40744020360004031809400505108410095841e40c21030300d25001d0409800011102c0c0c4440100f020b0302d86401c03400c401300003d82c450a1242d90104450f1412502d03281c1d240382414110340c009281c0e410340310304d00c1040010010f00a481b0060700307946114400e0b402004004070002c10341036030029420484c1d05031524064003000485250180700254481d8500902c0c0700001c00382076041000030488243c1c0f61a016034240052a01c00219101e00d410340c050010060291100a14115150030341042648045401c140148980200c6203000c83c2d903154404c171150a2a20320402c2c07207518000e01701180540c44061002c0d03140501c00c0321031190050300d02c25a0640c1e186a12101440344610844403c1285218003100080c0401c2c4503560486500c4030040b18a02c0201070004002c1c207a070003030322911f422194006240545095810a140301e5603902140c02d2000c400382e9940607403031700001842d05041c000005903032007111340284200c03005040450300807900c0d4200f000410200350418002c3d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 471027059 1250 471025809 471025813
    0x201090b0612060c0a141602030c1005030114010e0310060e0610090902031807060503090c0904020303030f04020f0604090b0306060a0f0b0a0201060e01030605060109090c0c1e0b0f09 80
    0x401c041d818150081030b40020320600070b002c40d49a650304145260310000d03d0b8010442d00b210a10740404182e0000c1c01c041d0301120700d0341500340c0d10380105803c241c0100c3e9040e104045502c100741445800c071040e41e044800c407241c806959424440142d8034600d0910b00a07a06001d15105009a92103a9201c1e509070b508600c0300000d00d036203140611003101c000c0000140410b5200b00300f000303000010b4000710303071080e50500203c1d6450f1a01c1d030b805107800b044c0c1d04040007144000c01003110f5000c0410100340300d03a104607610322441c1041d0300401e880740f0014000c2400407441c400000e00b591124500303403410b0500070f02000d80d60781c1d454044074001e0000f0b00540744640602004108145841104141601c48a0308106231140c40c00b44840203503400b4200300d4040d03540720b800001d4410041002d6600035405a0400b1500d450203000060008006402c900e852919044082142590214204901702c1e407042282244207446011b080200d00040301c01000011001c04101428640075001c80c050074022003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 471028309 1250 471027059 471027061
    0xb091f06020111070f17040b0a0807050403030f1b1b17010b030706200109110405090d080a0c0504050333090a08030a150b0309070f0b040504021b06070201090b 70
    0x103812070a8640ca591500c14510090041902180d000c0300e685480f1841004016180c0142103000ca860380c1141c0c0c804415042c010803104200c43d000803030315500c4050f91420b14030301f50940d54007914030a03d8038420400c100250b1880d00c05010002241044142c101612100000300c0030407000d480070303c0780981c243c41989562640d41244050241400880c0002c0240103480e00781803040301c0c881c111958641d140e420501a00200300400c1c17041e0901c81d070241041b819509401014030060340c00140102000c3c0c5c1c40305c0080007466501c014100c1e080300586801254980f601c1c44222800c5c06240c00080e407600030a072040b00c0f030f1300061140d0021010f0241c8080caa800f4400483c0901820464942d1981e130071610b071250000302000d009551000c089440024100118001a40f20b03c403540c2100f0200072000080c090724540030840b40008100308841320800300e08050800703610b40039611850b8040e54010075a0300602c01007210400201d001c41c0d0848500b8640340030002d000c4d1004039001d64402c0b450714 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 471029559 1250 471028309 471028319
    0x50115061404090e0304150c020a14090411030a080d0501150512060603061201020a1d040932160f0e06060a08070203040f030308041403090319060b091f 67
    0x120724925810704241c9828100b80c98404443d01a0408491201d082c4c0000c006c00f00302d42011018a0142d103680303a03200c0009a444c0d01c140506051507400460b0001d280115642e5199a41010650f01c46c0c1d1046070342d440f8041c0900403d15040603644d0050100c1ca01142c003407003040303c1c0d0348903a040300c400e0a18280290070541c0255818410344024140703507041000090240d0074181c00454101d0400b0344090506204010f1540c00ca030001100b031400034020b500401c08075611b104284001030000c0301e00b00300710703003c565032440d0340110403000180007032102100c50303000070108071104182800842a60030003c0c41880d040074076801c500a2074081044410045504002d207001640314080103003889140c180c600c00300340e0302074400504110443c0310801002c9503240c030032990070b0000e42c420303282d10506013000e20b001d159205110b640121141d10a11021083d40d0f00001d07030b1044000400e030000c8500c0c4042c2000405041102000d50300310960b20140700f1804040004181d00c1140f0100e8060210303120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 471030809 1250 471029559 471029567
    0x328032d11070b2812021206120303071b0f050105161409090a0b0f06160b0a1b0c2603272113090507080106020706051b100905011506 59
    0xf01610f05294442e04000c0d60613101542d0081052540506000214284210244040e0381c030800320301822010f01c1c024804181090101d1107000d00c1900061406c520340100e0003442d800358003400540f4241c40060040601c1680006d0b604001c1d0080024845450490300400181c01a5031340d000001d0244459402c900d1a94000e807060321000034910080c0780c440000542c003601005480540c4900d4065050000e5582c500042421802220b000c80680125040094410600074140b40c15181844584202221030288160150029080400328004c440c1441c0c000b20200311200d84000780c5400442c050081108080c500c128041c10b007860141d50000e04941c44c0c1c038980c4402103d10b50020350f42c150803800403000c0c6401e0010014100c1e0070700e81c192862055100417940f003440740719524814084000d0b40004000d0150980c0d000815050307140c00001032203886502c00301c18145001038460f0504290034402034401842e08003042c414000c2500f880d41c000d0484501010292030070000002d101809 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 471032059 1250 471030809 471030817
    0x3030603070b04121410151d011202120f0607031b0f23070f0b0a05060a0f1a090d0c0612060b0d09060e0307060b0328032d11070b 57
    0x10880401003c500d0b141d0755000d1840c8a0304010b5500d01030003c44500d543c0c0580700e44682d64010300d01e40b0540781d181c059050340d600502040d03400c2312401940184034131481c3d01d5008082c5503040d07403203403541c0000d4404241088208000049180102402c0c894084e03456040740d580b5050a11103515485120709003522175800340c81212012441410302c820841e10721001325400003203981e0999141081e03658900c0110020b01d2011a1070710b80c0d01c818000d61318000c0c800d090740054155001908503050492445680400e4420030142c00e510740800c550701145001030358020742024141d802c040343d8a140c6880f054005010f0100040c0010310035001c1c0320503034019070080f60400c4c1c0402d4a84501075505401900c07001400707445598803001c403555116001c20003481c0050042030b0018a108040007014104407010345a400302c120a200140c584c030300d8a01030b000d03900c2d80c50f0400705c000b034503104a059006003011880e0388489016042c00540c079a08890348048400042c410703a121302c2d481c0c811061003401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 471033309 1250 471032059 471032069
    0x506090f01180f08071404060b031b040b03070225141201020f0a09060906080601090506070c0e0a021c06030503030c0f0409060f030201020f0706140706060306090503030603070b04 79
    0x210359103004950048080301d031154101480301085036103c0200c60310f00155507208034601e0348854802c0005100189100c01e0802089405001c00381c60954501e0309400050048940001840800c0c03200340c50b200100d070300a040706000281c44c3d240c40c074030103521507100e5200260b240b201d02241c94041c101c0b0780210015940450402454188984188041d80303c0c0c14103a5030030340d9800c0261640d28034428016120180050780c440411a0501c0c3c0014428000b83c2d000400f0b00c800002880030980c1c0118402d000e440e0b0580e039598030703521141089070b41151160312840804100c4000c0c002c00385080d80040075039001680140100326500841e55048603910306c4050306681040c400306a00c1c204100043c20101c600d400030508142d11501c12104589080e446890210440c071410411560144101c02181045801405005182903c0509401d0180041030304002c0c000410200b00600c9900050186801920030030071819649400399684d4402e5480300d100303100c0d1000006510b600d020449040d61 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 471034559 1250 471033309 471033319
    0x80a0e060a180c030b040c091104090921030c0e0303090f0f011205011d01091808090a09060b070516030f0206070c170105040b06010e011b053301050609 67
    0x5651000410010198010b4080b50019000d004801240c50410760300040c40c0140e500308983d003001d14106c000c224195100108490902c2858068500c014050740d048683d080c001040e1000d0324540003d00028030005001c407a95440003101159615500001d01c41040d41c848095541490040561364000e41c540198040c903072071300d0070b8101d04149608502c05807041c1854580641000420300c1943e0090f0005005004000c0c0341c90b0025a402c080f0718010001004208451840c03a000e644030503078011405491204002244925a00d4090078040180b1441404111140d02c0e050701000581c441142a40e441c880c4500c0b1000b0852484003250803642d0041480c900d400b0f00b0f07801d00940d134011303900c207844004860724002104080086c405171004104030000070b09280524100e440e001002c1d00ca40d040001102c2d0064582e40c10002c00c8444400c0b55a020345500d401d4030f0910b00c4e091842c110b80088126045011081c6185c40c0080810b051303103080d01d5240c0b0381c0c9910a11801e03003d200c101a40c42 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 471035809 1250 471034559 471034561
    0xf0504090822030f0506070f030209010e01080603031309050115080f180a06020301120606060f171005030a050706021002070b010302060c07031415011401052502030d0f080a0e06 78
    0x5040201c140d804105082c03602c0240c1aa41e803542c2014030803e610549984c0c101d04104114664891541d0448108a0404600300700310340c0c000820000c4a40a014140001d500100f20030341d8040056034030090610703800c948201e45859030031000c0c0800380f06400204440e01d10000b411401240c68a1140120302c9070b0125940c0d030038100d9107965a2214001105014145403040032408500040d4080c4c20041c0171254103160526000c0d04456031940700d41c0800500e4004501996072042d204400644251082441511114024070745d50b0310039401160b044c490f1102440c00c200000c81c00a084075010740a40e07008402c1071000f0820b9201c0d8550041c240360301e90005000514020000d85209032941044440303050316a41d64052403a0345001000440d84554024058190080403482c05030105040701e0502105510020323101d400303014003c0c00c5105488c03050381c0b440580758815a40c0d25800804a4009802110000c0c0980710314010060004481d0310000e40b08036600d004940c20301e00044000e22007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 471037059 1250 471035809 471035827
    0x31908030c03040c0f23030a0305092e170a060819030c0f1506050a080307020906030f160603051305121305040504060203060103050105030d05031f0e100f05040908 72
    0x110b500040c011214034608240118080051080010240c03103044840e0260344c82c2c014440e9462055009214466400203c0c00c3c00001d90003020765400b2601610300e01055004207038003030002900e2080010042c0070b124090304019a01c00344204450b0268900041c02e6100e041c0404151211340c01000355542c041060000403900c41b8000304600d41c06458041c82d045055920707500c3c0d4100341c010035030f90300d1044800c00c25410350b5489044000d0070112400c40d011480c1590740c3c0d46900407208043e02c290700010010750141c13414403074001c801d1001e90039100c11003a01030b4490102c0c2d101d405003200003464140001c1009000040440f03250741c011005220380c07044000200c0241d0702c02c42c1c001007076480c1101e00003426120b40c042e85001d1840340d040980c0320b181210004089480507030045200e648904903480310315410104498008620300048402c5124291241c3c603443c01a62115940c0880d1104000c1c0c604100018881a40c1100c90303284021a42c0d1802c0001307440507118042d1020390b04014000b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 471038309 1250 471037059 471037081
    0x60a0605012d050f1207020f0c04020a0801050d110904030804060606030c0219140d0201061502030403030801030803040320031305030c0a06120608070b0c07090203040b0103020402091f020c03190803 87
    0x101507109100964078082170101d403000c220f0f009440c910056802800305450900c0244076200d14000b054030700f141450030040c802084140107202e240e0103004065222418031409601c00307001d0b40400741c8024654245841c0c01000d4003001c4030305980c8a4501080071440070300c0707400346482404842d401003200311100340d00400000381e40d1038100c540c0800018220702401d8103000850203061b080d000002c4031071400e00d40c1c02041c0340d40c84010085400070007081c80041d8019105c581902d0f000203031582c480d03880c4c0c0f0b803c0e00d01b040f412003010005c007640c9100e1407030b80200000404426015004034042c2c01d070b03680b0a150b6188681d030302556108034181d0b01448180c0c17190f000c00c044071401d041c01194580d47c1e00c0e41c0c40d0a00c0016003101c000004001500317421004200700e10310042c0f0b2800000c62540c5402d845042603c4030601000344a01c0c0c00040314515680d900d0100f268400c00c0c1031039000107410a510180d9910f01340c0c10780724040c1c014400c401c0d4049070800745416070b00350004d0403246103a5a8a01201c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 471039559 1250 471038309 471038317
    0x1018061a0f0f12070b04030c0f05032802030a11040c0206010b03070e0103241a07020105040614070b1006020f0a050604060914010f0f0f0b0f01030b0a0503060a0605012d05 75
    0x5a0000501d00d102030702000f04200281c010302c50200301c903903541e0460500000310001030704806c4c205540e40d601041607031000600039009455801910324a460140386070b0410100400e0301960600c03c104501040c01011010001018000c0302c0c2000011074440c01640c0f02d040c248a200014030f401c3c00021030480c090300c1446555072381494000741d51440800304001103e88290181d11060107054144050214000100e020f05400701c045410407210783c1c002450b43c4214061001040b90b840341d601c3c218414202174801042c2d00c0a444036451500300321100c0164210311601c1c0052040015103080407101140e031f0000c0b00e0b0040c1c044d0086a8450b1108005004450002c079440710a00d550307070091810a1151b5100c561141c240814618000082a801d43d522024001000c91403c11905401e5882d1604094180c00c203007808101002810000b42c5050b0b500d42c00941c040c01101c0800003006000d0380208281e8000340c03100f142c0c0103a0b031000c015221040800d068150001e61040e18691400344004d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 471040809 1250 471039559 471039589
    0x41715060f0303071505070f02120a03150e090c01140909041103070b0f180901050d060e01020d020c030c0d03060b07151508060f011a0a0e031018061a0f 67
    0x403884c3c00394650702c50300e010207038204524000f0703030314424021000e51013282c0c0e8280603482d10003030810f40860010540da51068a0b0454141030303448001c5841120448001001403001c03404440c180d10742400450384400c2c1400756980021944914a140040703100140e80e0140000391413100346945580d12000121409264160b0501c0303614000500d0321003500c010b143c2810080c800b9511180720429440410421480041c03280c0d290700014049030311080304040c2c00c1038110401140d20103442140f07500a228081101800c1400010f1207003c482c0d0000003020100908000c1b118038803000c1c4070803000c45030140101d9042403c02c00041d80400d040c01119000001e01503800200220911440d000300c00340ba42c4a43d406802010030081054000801540100843e0000030b0584280030217a600c10300c507903c0604103101d060841d40002d91402c00542000025a20f030410900004003048030701c3d0b12040030300712140f904020044207a100c0c3c108103009030000261406000d00d44c03d4041019491004c512 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 471042059 1250 471040809 471040813
    0xc040e0f0a02011d1915020102030613090f0c0f0f09090206040b0a0207050603150906010c0312090302100501080f120a080103060c030f060303050319150b0708041a041715060f03 78
    0x101c1c1c400d07a0b25103180402c100c0711700e181a80b4243c6003101c1000140040b5140c0401c3d0b9206004020751510707440d001240c0088001c2d4005050703403c89c50308200506011002400603410150013080043c4554001003d80d100c8044824440e55140b0711401600c00c40b00c0f0086d0000703400d10082151070105009050002041d0060398a001d480f5404541581c200320717101841e503107428481d11054105117141c0398201c01d00f803801d000e49109a44000c0c141948282030715201f039070385001c43e1042c144280065444901014414051565a0b044036559445503040d241d190f4000d5041164a46051008030b03049294251070340590b5a10b1030b114140140301c504109424143c860130700f0b80c210b0307545100b8100594402d480e030036140e0400e40202e0701c8c0254582201003502c0c1c5000d20505001c80840c1396841100d00e400d071800e6a601c00707880c143d80300c0e004951024403110141c580040c2c0413244030000d8015158a000c2e9060f41100360360600e075480302414445c00d079044041c0e000c90708038186107035504030001d00501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 471043165 1106 471042059 471042107
    0x10f02030a1d0d0b090303041a01031a100b160b220b0405030c2a041a040902151309053102031e0c040e0f0a0201 50
    0x4002d08070580c07050100080d54a151042e004035138003600e0003000d4102004050f6507078009a5080350103800c00520100642480340758181200e400001d29420510f0507450310701c0800010701803034030180c450301c0046000c404a8008000c800c6000100348400a0300c0d0030400900710f009060841d4060400e001407068900400c040da0f540e0703410214410043d12540340440c514860802c240c012800b0385030b00c102540240c15240700083c4040003100d054004d03040200002c0300d59803c0352004002e4588051840343c103055003d25401c1d4030241110b107a030044041ca0610076008213040001020310b010003805565468090303d500a1840307a00d200e51450640e40d1549030803014494000a082c544100d10300f999410008001c0403c180d00d910030b09842000040360721042c82240181c0a1420404500000040040c075803030003010f100060f108541c2c0035401103500b1403d8400c2c4501b0044141 = true := by decide +kernel

theorem cover : BRFrame.Cov 470863309 471043165 := by
  have h0 := BRFrame.cov_init 470863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 470863309 ≤ n) (h2 : n < 471043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
