-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0998
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:44:03.48943+00:00
-- url     : https://prove2.me/submissions/5223b059-fb18-4058-ac74-97a61ad10d56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 179316546 ≤ n < 179496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 179317796 1250 179316546 179316593
    0xa0c0b0702030d140708130c031104020d1409060a0915020f090a031104110909040221070e180102030c0403080d020702151b0f0c01050d06120c090e0a030e0409 70
    0x60461002e03100301042e10005c0001e2146e100058400a10f241c91404182d880040d120320380385191601c3d00c8650482504c96882642040000d0003d00e1741d10071401c00788056403c0612600d00160340c1420454000c1c0901c20060900a26a000442a0300840c002c1020301000580300c03030f003074843c0748800c0c0070324600550400c1c015407010050210310421103400d500101c0b03040c0420340041043c0480c078000c015289400043d008082001480e08503802e01603640060000b582508051018038030303019456100b00e901031103400c240542100c418905480c2c10203840025451402c0440740300c035841c0b241e8400540049408107896142524a404492949800900b045081d5084400110181d40f140407119041c100c070300003c6107804004242c2140400004002d4403200c4880701c01507a0a81c0030a41600741541e403000c01080c1c070303941d1017a134881d100e014449550038a82071000311422103544d002508502c3e4810894500005d901180103000c640b8103903800305484000e46000e044c0603150b8220240e4050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 179319046 1250 179317796 179317811
    0x509090a0206041e050a0b090f12030327030901080601120f0c030c030e060c040504090c0510020f07090e06161134030c09021303080c0a0b010501050a0c0b0702030d 72
    0x591102400388501404d9850b21003450341e900420040302c1c860310520381004014011039880e8500700c0b48042d04000f02034012500a14042652410340e40200d428440c0420181c481c40c1101c000000d100f219144540001e6151110303100c00a0b041d5000289264100010311401c20034550580e044031139030600200781441303c049000e0020b400b03401c2070010000080d140c28042e803110070000131040d01550350b402003a803910303041c6400e00026188007501600d0403004d00700001040e031201a41000c80440035805800c5039204450220b08040c0d250b403101191500b0300d070b1032041c20480801c405402c0340142c46001c03400160b6107415200329078041840c440174050b501c0080904102d1410281c9810102101c8030500e41c0400d0110050280d6408003a10034265500c09111511080d40101150344600c6002d482c056030b41d135580036a56200700d000d9902030700114940b03000c128280b0801c0703014100c01d003010b904009500354001d080d10f601f090082d01c14104c0320042054540244100c90064200101c18030004c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 179320296 1250 179319046 179319059
    0xc080a02060105092401110a0b162606010c0201030b031c030e030c1c0207030807080705010b06040b090f0406181509050603031c0b0d050c01140a090509090a020604 72
    0x10803003441a01e0007210124001491400880c0c50360f4004103075440f0344e1740504802001141c0c0d4000322890700e0054452902c5d024040342c00da502031403280c403070b003e8514000070100c48000c0c40e0030080c00c0c000c40384514540d004071850740004226a40244280382c800544e4842c1d000480180c0202c2c46c4040d01809040c070031010180011182e87c5403808551030a02c070040410307035156543c1c41510480c000541207276080e419842d501c0314094280001500c116403120751203031601200c44d800039204a030450000a402800c00000303000380c2c103007001c1c01c44809050500e0420103104a21480c0501442002001c1b0340c00344540c0d40e640424050292002650607580005603d030000304080400d0200780343e203004000400480d01d0040c21f1040c80d028024505261600c01c5154001c00116880b18000d501d031011200543c85400718881054000c000802c1400b182c200054411000c1c070000d400360143c200b103c60166a0800096021500f06917030040700d6a81d10103100f42049000701000750b1103280020005402d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 179321546 1250 179320296 179320303
    0x10b0909060a0501171003060203070503190b061c06081e070e0402010903080a050c060c0913090c210602030a0507081503070b03070c171309020708040e070c080a02 72
    0x158009490300c5040d6154242000140c0b00309118090000301c41404100b81a56a44549500f0200d030301d214050054803646d40809a8004542c000001a0f021007009a041103000b030b036406501a00008111100081c404a20b040c4100e01c103102c4a6551202d0000c3c400c01c880d44060000c0c02c009007620300181071b5a500780a03034801813618141034403402c403000c500e000040481c00e018581c16102c10f11400e143d07a690a1494004003144024050140402d400c10507051000c00d224010343e640c00e035a14007007007040000644c50b10b045422000e15282078040019400308461007640c503110800c0c40385c499450603190b104030786100000d013854008014040a020940c00a078010780060b282c1001c656071300071300c41c4040d902c0ca034070f05c0c0da250307210135020000f42803014002c0d0b0b040009480c1c000700c420303040e8845074244601581d524198182c00144070408441106200d409003401d03a2065117028041e03141c202880c020390003458201301540000c54007103802000004030305544803400d1501e403802d2802c043d48 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 179322796 1250 179321546 179321557
    0x1d0916060207090f110306041512121106090a030302130f0f2c0f071106180c0a06050409020a0302071407030201030c030e060a0e0f0109140c01090e070309080909010b 73
    0x9803410001d001180811170b001e441c40c030b100710498150855540001304400b0349203850881e002d03039500c080c0100b2540740210350000c03510701801041c500e581240300011303d10a011001d03800700c0d803c080140101070001041440741241c051401588a90302040300160a0025071300000c11814000d60000300e144a200055084038145010600c2c14840b00340076413071500075050003140f28607508000504a02c941c103a00c0350070018524140704548088603c141c5440003e880e8260004010000070918503010002c1440c0d644080d900c00c040b8601d0608d01900034042c82c0a010030084c1c0205040209910a0781503d50260300b02001940e842a141c5030315490340d9141c00180d000905004401030654040c3c020714148410741802800580c0d0f641514000402c03c400c00c00c6510302818102d19849142401380003c9540200320b280000c00d24010f400340b815148105940c1408022030742003100e101510310807903000d481404c010403030017441c1c0f901092501c03424201e954031141020001c115408260041c14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 179324046 1250 179322796 179322809
    0x204020d0c020c13023402040203041505010501023c070f03030807090302060f0a021f020414030c01020a030f030b04020a0c02031005150f06090303030103050114010e011d0916060207 80
    0x1950101c01c21108103034400c0c80d610344d10713038125100a203141040603103001d450181b80301020002d070f9440d030740000d041c1da2003658195425000318012043c804882c1c4175190051a090000b0141c080c20701d0369000899000d601c183c4e0010f00c0d0340003001008d040e000102d81d1883d20350401d44001a0f00d49507455003600309408143d00003021040000c007080d00610126003642e8000b8a030724140180000d8046850b44038041e12811030192800c134a105683d959a0070b4420030b6a50005038846081820b443c2c1c01a13240980244030341c0c4880807021071660082005410030340c0500e44100c5064240c00c0c150081c1007540300d0300d90402e1000541030001c69111402c5e100b928400c8041c0d46903105211150001e85800303440119180c40c240310a64480c1c42c00700c08003540660044c11590400303031080e00290554209910903100703a5101d000400070b80c408948428098500d842d041403155041040031400c420802042d031000009042c0421850320b400c000d520080613454504088081d1507481c02501c8201500c01d03803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 179325296 1250 179324046 179324059
    0x10303080c0f04050402070809100504171b010e1206100f17070b031017010509120c0d080c070210030c021b0105030c0702010318060b0910051c0204020d0c020c 70
    0x1d025018500071160707003511107604141000e0402040000a44c840103084070071003020414640c0303075141d400b1141c960f03d00c2e42d00da440c0c5691800c0b208174800301400e101340305280c02030410304030400b103034540c5444d015000b0300e030141d8546c0c11440495030071100451516000c0c441d0500300524030122610600036169852007200c030480e80e81c4103c840704031481c0e0b040c034043c3e001864144500250301c07025582c4000c00380350359040c80c0d42d502100d588404840c480c41cad0b01a5164400c000d07c11100b0481003a151070311f0007890b40343c10036000b0034584484100c0700305002c000e41000420003090b038042c1a521179540041068078100b0165102600a2901c00000e1015005142c60224001c010000d28041e454060312000c0c511303a980d42c1900740035405103808034141680c0c3e8004509139800d424000e101d052040c823001440b00c240c0010000001c0c00104100e8000d40035810a0209803608503608080c1c0314441d1f00d0100d1100c0c1480020064010b00034800c181e82d103030544090660b6400500c4040038103041d580c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 179326546 1250 179325296 179325301
    0x1e0f0b0a031d0a060e012903070b0a0c08090d021008100b0a020703060213080106030b07020106120c030204020901021c090f0503031809090106081002090103152102010e03060f01030308 81
    0x2000c0b07450314049810111a0040c10004000c0744c05034020001c802c2c1d1100002504043e06980460811042c0c030b0555001d04201c1650342003030030108494006007030b008241e507041920441000b81034140792580100700080100302c1d581c0030384802e14040702496000b0b08101c0640c000703950040c107161045409150070701c5160f40c0050b0040c001001c940c803112980d806401c0440c116115139019500c20030a08030300d5000010006601c40082c407940c4051482044113400b42e04021034000d095981070703004000d01e84801c014038000190900040d404880c1c0c10b950250b100c203003403030042c4c0c1043d0355a24965407040c8031482004029a02c90700306d00c1a6510000025000c640310414182c1d240170384000c0c1002c000c1014100078031407130301c0100690300448002c000704905841e911106c2c00c0c02040d0031154103041d000305804a19607011f0240c60000202c019507403410920b4410703a83c4c4220303c611200003820003e100184c066900ca405e0b4081c4150001d41110402d00b8068000b825003002440140d0014003020003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 179327796 1250 179326546 179326571
    0x2010e06010b1c092a0e04060c0f02060105060a08130204060b03090118021c05030403140d08010803180105090a0b0c070317071a070302040321030f020708041e0f0b0a03 74
    0x2609441035040188040e607504c0c45000c242c003603010484040d80e45091786200180f011004081d1510980c451240482c2105030610f0107011600460070007402d6401c0003005000581b2094141d40b2450780c2407400f80a81d40784e080310001d504080441c040d42203400c081021801d10007503c01103000b680c070000200403d0004050031415000b500100a621402840e8001168001e5141003030742c1c140a60203032454030742d07a9602c1c0c0d5800e080507803078160740e9000040c038498401d400101c0f44e801000841c000d103240401056401e022600c6000030303035051050105040d5860b03241e450058000c2d10580001a44d18000042d82941d5021180720031262494003440e03480340b2006080c01d4420965203c05c4151103000c0c45544c1000141000304810304240d4280000000700e02c0d82201183c041e941d0904010300e00081c0390008090700c454a03003148800780100081e40004003518101c07001c5070741383e081c04900107a082030a0001c01041d54032840c600c501a100100d924501c0d500144442d000c1514100900700e81e006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 179329046 1250 179327796 179327801
    0x8010219020f011404020405060609131b080c070b09100603050105060307060c050d050d140a0518071503020708090d03081009180204050907050405010b0405090c090603061002010e06010b1c 83
    0x104405132000c0c1da4041401070901360020703500180000d0000c0d0401000d0804965190062120002100c0d01c0320300f03048080c825011722a20144561412400f18582000352010300e1003820340080c040809400003e103d80d500340030021440178080c80902040c1d683e41426400b034081038824910a0082c1900068614094001c4016007039201e40078000c5850b403041d05a0703041d0090304e8240605074403030700d440f0480c558003002948580303000e81d000659403c140308a28003825014500c010940d025140034001100504c9940500c032090703160269a440c035901d0130030010b00401c0b24040d00010ba01101a04154000c001c0324801c28404015101550350343d4101025600e102038101c940d610988050809410b154104c2c50344841100111005039a40d03030085012110300340d0002c10510004034040c0014074001c0354107900140c1e107038141405d2040550002e9850f10000e044140301f490300141c480c142d40e0007900131b08001e441d00c4056402c0c560307444401c00159440501800c3d18060300d80355103582c039150b03403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 179330296 1250 179329046 179329061
    0x3060a030b09070905130501050f060a120201050f040807080f0c130b0609031204050111060105151308060a060f0803070f030305060607050102030a090b091903031508010219020f01 79
    0x20024142a4515111040c120001030068441070140c20004607920503980184c5d40141460f4080007412003481c10003d00b140e1002e09403a148241d00402d0200da40e80307509034a81618a0164850602011480141e4680c4a80707008a030044a002c240040e840c0c00100d501750449400030161809082c3e040001515420158902d5910280c5060041100f010f990301050300f60f0380182255107030840303020000b40303080b2000301400f040039400541802076513402041507c00000503801800b5079410007000131040081c4c0b150000501030b021404203001005c0c828480000c00c030600c1550168100088414090302d81400340c003500c00150f1000140720f5000104940345607401c800d2469a00d4001d540442c05440c000d000d441d8040b0302840104080342d000c0c80158000d03000d0200000d02070201d4a80140790a80080800943e90070403000c110000c007500d8001884194180350002d6000440a80344988000039008055150302c0464521003000391640d501d000c0b02125000c440c00c03c402c0031901802c2c2c6800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 179331546 1250 179330296 179330299
    0x1005100b0c07180b1206060102010b0a120209040f0b070f0e01080c0a080a0219200a0203030d0509031201030b041502090a05010c0f0602160b160804120e061615020306 73
    0x1402e800c00c440106804000d8240015241c00700f0403120342000038959200c1000008034640205e01404155070302480344190302c0344280e0348080468980803032400094042c034000780c000c01c07031180010104052103180c28803903640030b40b55241d28240680300805462264104c1c8000c140c02c07202e581b03499802070644503c6503c107009001d01d0000c07481d904032680c1c01c0150403003030165004e100e211f030340c00d41585003084207e20703e13503640010100740f9140190040c4544040c0c03241c2d1700444001000b6880101c1152250400d8950100d1151503041d011803940c481c14008000c2001120b0012007080b2118403014083e134010004003020401c01d4002c2c80032172007138054850b442045a041040154055540000003d00aa10324100c1d6840e0380c0f01d402c140e80c4450360804440301c0303c81105041080302c044035600084e4007518100400e0314940054504200640064070075018910240410b40c850340c26407584c2c00c0090a04c5807283d41106103e00f01c88200d0500f1030300703080c41e0892080020101c0c803d59214400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 179332796 1250 179331546 179331553
    0x6121012020d11030709020c010c080105062503090503010603080702030c0406060e010c0827010f09030201020601060e030109060c031d1204030204110c011802041a09010e090304081005100b0c 84
    0x1803a6542205512030100202e8050188417000a10b50000744007501c0c3c580c2d002e100103d519a11068010311001050b008144201414889139802a45026100404d52400c001c401800012410b041d00c4c24903c81d801903030b2560030041d002c410041440090203e291003070703084031035205c044801c00c4150b83c00303030140200246a504400242d5032040d164112824003c020103803401750300c1c0045003203402005252018200d2040e0012600b0f59014071100358010091410751806c0b8150340c0002d40300c6006219034020811480c100c0c6246950a40c001d88086034403130410055540c3d12034000d07000d09480204101d076084d0001104107444004500040d04208500b001d900d0241950308001c01001e0500114898000074010050602002d1117082500c801d00482d8440074400741c4100400e503451051034458080c0c40b4440344039543c95640e41181500c0c187c1008261584e14659410711314000d84c1d1214600d88600424003201805590100b409291450100c40c3c1960701d408039400f8034800e0240c1002c8651 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 179334046 1250 179332796 179332819
    0x8060603090604110607050a05070302030d05030f010b0a0504081f1a090a02070602070519060f0c081501020c03030f091c08160c1205010507110d0207050105030a09020612101202 78
    0x307410703850039031350001d00030146401c00c401e035112507280400f03400c801c8881d9403064400780154034041104441103101482c0c0b4900d14a42038405002e400c6042c803401507120300c04508011024050310549000d4500702044500d19840e01419801d20b12015608404152030003150102a045099070490600b101500c00780072900c0310b4820704000d50080b0400d4904981c24041d51001070170510880004c00c00b005102c040c4504242400307400c55590301c1000408601c0c000701c104038950040c21180d4028600d250301514540f00c03600503418580100d5090780d041c000041e04034001c1551001a1206000995144d0074284410480c00341c0c04c00520006451400180890440c80d812140d00600b00b0b4443c40003e4000c03550348904144001488408840ca48d45980420280c030394881ea13641c0701c84051a005110001140b08041d40301e05407406900c0c108080080055100b0714240c00c19036400740c0c0034000f544d54102914005016200030b45483c2440210000c0c005a81544030407950030064008104c0c86520 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 179335296 1250 179334046 179334053
    0xa061b0219032306070201020301030c060c03031b18090501030c18021611030c010f1b140609030a170c18010c06141b04080a1e12050a08060603090604 66
    0x74103070a021110100d04610000c00015581405042c494a41c41c0d1403c100c0700070380148070300700b042c002c0c40c600171684188010004a142042c492044502d94203001c0101c0c6002d0a003100580b0341b140446c40c0009105240580995020040038800100d00940054032a00c41580d007040d20000e20003e0001c09010a040c001503c118a420b5500c0c15500c00051401c040d003c0307014850b220758501510410400080aa51414140640340b104202440d001003428108a070180c50312000780042d00a119030030401e0010450f0b0629113554500c51f20044910300d280c5801039070b40d00d611401154002403841c2c4049040c1414040c0850f000b1900d20300c90740e04283c0030120a01c84038824102c2503041042c60746459011544c0380c0f02c0c58464507000c401c05c1c03a0901d84461404070801380001d01801024040008014210003c2211b660303855020000e4412030365180504a90219080009400080307525000841650032600600081c5d03540d8541d41413980c1d440341000b0381804100c0307545034540c001c0400038000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 179336546 1250 179335296 179335309
    0x120c01030b03030c0a03020c04051e0406020a11011a151804021809130605060f01021f110d09030f09080a03080c040b0f180d0507090504030519020c0a061b02 69
    0x5024000e400c982c20403140080c00c91070540460025401f60300044204190703806c0030301940758403400d00050340119003400d058508101200410150030703141e001c54a480e6080c070860983c0e80800d2000000d00940c030340c01010342c031525000411148602030b042640c1c0720f885141c80983d5414400503240504044c0b1620a11000c2d50200c0e51850310408a2182c80ca015510006284d006c2e548a00740c0d41c0f541030b004d10705041121005001584961034080c40b02c486a82e00180c8154281a460a81c1ea0707030005550510703015018400c03841380c4400020802444005250340060802c5000e80e9488040603610070081e80c005009005440c91904101c07001c50109010700f85440e0441c0501580c54074065039902005903d400440000042010014002082d1209540b9a50b0009421540d11890003c02e40d21550f036080c00313100e0255150f1b120400541458080c50030381e0320b083e003504241d8000e0030321004000e4480e10301c005414031503062110701042d11482121030301e403001e02e100230340140e183d8640c00f00002c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 179337796 1250 179336546 179336561
    0x303080c0d021306020f0705010207080a020103090c0e0408070b0601083601050c07030809010b0a030f06060b2a0a02031002090d08121009050606090405040212150601020c120c0103 79
    0x2078550200038110484051243d81801801d41e41e01920320f4440b20154507007004100d80c0000d046500419080c441c0031004202c0700241e50f82404c00040c94581d61030314035040300940d80000c1d00c0e0310991080100344440b000003031490f9845140e1655090b940d1034019100560103a8141200405400e21155007a240c140d50034000b40200d9421152f681e0f603c00c0003420340310222001640d060300455010209030700584001c0e00400c50300000d000d0101204003060741d240d20f5220107025a5000b12611003442401d9220201402040c0b80240d85c400650313820002a940d0240906015807401600d038014241c080f40a4104a80c0200940a54410f10a514020390440c010117540424224001d000240208001785810340c1d008200040701d142400309000d000c2041d600c07082c03040e403c02e402c002c041c1e0394040c2201e005100468000907191038034008600e94201017140b05815124000080c43d1181d6a008500d100305800d03401c49500466110500c5442016011074142d154082112000298020b400686 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 179339046 1250 179337796 179337817
    0x5060f09090106090f0e010b0f090d06050106030516020303040525052106090604050c060703031d0f010c0315170c19050301110c030304060b13090b010509060a0303080c 74
    0x1424441120001441c815081e44243d003c40e081810410004801010100045c400d2084c214600c0d8034144140042c4c1c85202c000700403c0000148070181a0f03a140b01c0b1081e01c90b007001c410881036840c0e0340c000e0003c0c83c5c10703100c4214980c1c80c0c08490348414800000c50f446940c0c020702602101c56400552a9212140c101410317001c28a00b50100d090740751100440046500b03110940c00755072000c1b042504000380038002c00c00540000301040b01051000407809420708003581d215541e01d8403801c0880040180c8400400d0704202090b00284200c4000b030f000c1041080a80200704140d0501819411528400c11a0105580f40307a001c101c0c84815203240c912220860003501c61074145800001c1c601e55848103840c540300c034100c0c410f01050031309100e282c08411210003c189403440004d00250380c5e000c011320050002d0748480c119151a11181041c1500c0c0c0ca0400042c441a885841e00034004d810034014140200e2006000508500d00b414140c3e040b26010780b62044561951005d090300c640c481000c64 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 179340296 1250 179339046 179339077
    0x1b05010605030d0c0b0105010e09070503190606030c030f0209010c1509060e0703030305060604030804031b1710050604060e1803090a06030c1206060e2b06151e0506 72
    0xc1c0303644041c841c0c02c0e08180c141d07441103403103a01d0b80b81038100d000301a04200c0c100400502103400d141c45013503a0711340000e140d08001c6c0d01d0341e45005d100c07001144004050a005d50403e8030000d05d040d0036411000c0352200e581c805001a01060b56020104d0040d2800039000070070b030900d1700010441d411160110301086150214480ba0940c45040546510300c0d5804c2c1384c0c0c0e029203020400c2c182d040c440c403a08440301710358051806156480782d0120b4049ca000142120103800c1c01078040c0f04140741504020054215980802d80450f011203031100d03400380b03504d4861400c2100291043c542403041c0401c4c0d40d11600500f000d0b450f034490050f04002200c009500a11082010f900d43d65191b000b080001d00a13a500803039503040002000700300c62051034140b031215080c070b0303c240b240f1900181c545401d4a810307203200204108018102c480d00700003104800c00c000244400b0014080e280d000209039200750340c800103c5560700c560555070441483c905540380b8241c04428001c5141403030080c01d2143d07403030402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 179341546 1250 179340296 179340299
    0x5011d0f0103230c040e0f06100f17090105010819080d0905031c021b0606130c050f0c030a02240c070609200405070c050705060309070305060109050a0605101b050106 73
    0xa1112003181a11381490945021508001b0002512112a44481c001000e82003c0c101080850340c11b4000e960210144a501c82c0f140341c40307902c10030307111038044210030b08802641880c030500c4c1d000780028007404006000320420003000d4003042180c10b40590b8440720081c50011442c40c450300400c0110780858403800b00700400140c020100e40c1031108001c246000603503c1044041c030f0288074070308280e07400d0240c0080c1c0400486943d207500ca4404410544408581500307004c408980a00c1515112006001d01103001d00c085500000076000404003602140c441c18090205114011030400c41c100034030389100c000806044040f405040e03401d01c601004280e540441e034070440d41c050701402405000c1e403052a0b4042c6440c00b4014227400288900700079000345041d440c0c5c0d03a1580d515005440c0142d80c0040400c4016204004440042da048401d803006540c4170700a85018250070344444e4840d90800201042c0e030b1804908200084885455010000601da0500b0f01408c0714110203840e81d542c1d4140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 179342796 1250 179341546 179341601
    0xe03030d020a02120403030e09070806091b09040908220302030d0f0323060a060503060307030807051c022b0509040f060b0a0e1201050919050f120405011d0f0103 71
    0x180c801b4500c26214080030b0b001a40512071a04401071280e400c0081d84000c0c40b40540354803c07000d801c4800340507a919500d00400400c0e1440c400d03001459040742c94215030031f0901c40c0070f0b40503217115584032130344a40c80219241d030703550207064902020303526070809411450303064007415541c01e01014604002c11051070b084400b56481c01c0055072032014500c088108042071601e010b40c41c001d0a901d050540c210709103940420b6841019000007009048001903110900008004410b00403640400f5400000b84004000b5241c3c0d85814009419a21100ca03003c45210711804004001d001d0f0396070a400c1002070800c0001a010740c80750b6400c055680c590210784510100c1c0140720304174184c0c070b980b50004058000d0202c0c40e690129504c086134905018415180d0010a140c56402680f80003070004a800382000c6090052030001280b0030703c15001c2140310f5900480182c400c80b802602c2d02e41c844810244025885140c640c0d11980c050044400b0b000c0c2e0f0b600a80c0002c2d1444d0380c034800d1040d42c101c02c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 179344046 1250 179342796 179342833
    0x10030c060908010c020a03020c1216090c090806060d030c0f0c0902032a0706021b03160210021506010807020313120204180807200402070f0b070e03030d020a02 70
    0x800032000a20081030a1001e03403424090141d203000c451004110210705914020748600c2c605000c1485400300705248500e40404100800d00c600b840d94480040e5603850384410021f200e00001390002c03c422000c00100b021000c01c10b240b00d00070181c4201c4001006a50484101307002e010210380b4a400e2101400100d14011159400740c114080e005076070741800800742c00354842e000040d08150314031611803804012030a0549d60407d030312050141e1540070b03928405142d868002400b007007900c40820340810800c00b020100740490b00a8032030646480030403600701d031100c1c0c0d00d00d404000a440c1c3c002044107035200d003800560140107441941e08107a8524807450700c008043c2c0c031030f09800c0300008001d8150303d0030b4800e10040000070000d40101d003490360b6889607540500f0794064112070912982510b480c0354012802c40244e0024011941c03403911749005403007289441c1050300c005442c00001409540551401e8265100c000e00031814102d0b107100e107001961007000c5007821802401d403d642880401c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 179345296 1250 179344046 179344049
    0x250b09061b07030c060b0a05030f0105060907030b0904030c030509040c0801030c0806190e0c041811030f1f02070209041208151e010e030304090b0a0b07031710030c 72
    0x6001401080c10300c2602940003102241c1d440d034541c00c041014100090700b00c50b50f15600e0340e010f980032881c0d0f50440001034440d101d590000e07803d030161211400c7d2544065001a20810046460310000d4868a0046048505001d0300307a03004032036031001c2008240108084000c2c58800c1c50040e29045810000c1403e07180002c7d0b54401103822a0010300070407607544847c0c0c0c00b40540b0b0b802480b103131600002030f80c40c05014240b0709407503550f60499074403514401d00815482c1d50019100b4400d40749009401c44030100d501c035094810000494110125160100702080080482030080c208440c1c19030554045400d40380041190580c01c001c02c00050301e460600c1031246004429020501c3d40700c486c05400d4401c000c2488100c42a40b03001c24403113655180162503200080700300c419441c101d910058500b0b07615641c03015818440410005141c558640001000c03070011380306203079016034450406000303000300400100420b16102c05d208008046031011039200764a41805030b06039569866000840540c0e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 179346546 1250 179345296 179345311
    0x16060f06080a05010605030f03040314030408030406080610090605030601030c1e050445020c0106080d030c02010e06150a0b04080d09140901150e0a09022d250b 70
    0x102e0980701403010a1003001e005090030340151200c014150003141c0c0b07a10407400010b1502d200300000b461040c03010410307a00600340000440780d446446540c06000704508586880c4111402c168081e4018800c0c001c0d0003c460f540d458a41c103507112400154080c150380b980301402c2040e915090000c10a041410030002107082e26a180e0319801d1a150300e82e040808148250b16503501941c090140780c540d41c104041140783c0316000070141080050002070301ca8401b11081070340c2060300102d03c60b01d004c5090340300014240c5003080312400d0800d041e800d0b144003030040100703a0090000a003580c1852070200301c00e4040101b254055580383c0ea46000c1917049604002600e501c00c44d1204040d07604161840007404801c0c10380340070810b0400c002180c12a05000e844003004814080303950450150490245000000301440c0256403550700300d0b4000c1d001101c6500c405800c00c00c60310380703200c000240e0600040d007103545180b03040307600c401000442941845071441a450311034414081502c120825008141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 179347796 1250 179346546 179346553
    0xa060509100e01181805071b02010305070c0206070309050310090c15050903122a060a0c0e100c1716030f021603140106050603090a110d12020a03031404030516060f0608 74
    0x312200d810700306c480040812040c00411001c601ea21a01220026501741c2c0c2440e02003165964014111a24500c00c00300a400a0003c02c0031000c054000e0341d10419100198100d598200d04c0c050301800759266014054030282200704240300c0000383c540001c60502075828034515100220002c2480d040e00145000c4c400c540c0459985460b13000c400107082001c900d0020f941405034224491a00d903640500342c84c0001b540c81105a0440d07004101558444d00c1c010442020083c800da400707445c81030200030403501145407031800080c020000301994140382515802e08e00d0044a0f40e002d0b202c00441d16489402e40c4282408084501e08002d03011001e0b510400000b0005000c0441241c2075901e1504024880d100500400c0041100091050354035904000440849600900425841c5408941c05481c0500303441160071410780000d419440144203035010002c0101c4940d000300c401074180c4000f0300080f0304103d640742c50791500306401c01150044c039002552010070050501218910742c04031000d0740 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 179349046 1250 179347796 179347829
    0x908040b0a022109060301060810050303160302060c03040308041509050304121101031a0105160b010b0a180f05040504050c03061008070602061302191806050a060509100e0118 77
    0x301c0340f01c1c515a900c80b40081070070b000342200080c485000c14010300c02044500c400040c0c0c80c850440e2250010702d009400c1da80d4903800033300403a00b00b1103140d4042d80540f040c41c0c00304216140d56412648074030b4044c1d9860b251074880da541d60094200c1e8404980c5010b4030341881c0d00102d4000d10043c0020700d60f042c602c03450392100c1d00e007203403a4500e032008040c14185021a44079046014403240020308800340381c59a503802c5074417600039061034180c202401415140d000032440e410a58014000c074021500c68802c01410b940c1d601460900c41e0243c07400001b0505000c001505040c0c1005400500c0384054030404c11030700300401d140035001c5422446004011000300000030007031081801816152015111f079207010038a01c99a141030540090040110300051218170048104c000050564211106c0c0c14000400705030018020314000e903440b44440010019038140140e045030104500a030403003c5404070850141d581c21404240e05041c04100c08404030b66242488000b406081009800c00701103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 179350296 1250 179349046 179349073
    0x5011203110114011e12080301030c05100903170d05070806010f02070e01120f02061b0d08090c0f0f10031401080a020d0b1e011203030e1b040908040b0a02 68
    0x200c6600030141c6099140006030b241c0909540440750644007800c1070640c008982104c84e441a0500e03034071160322019140e101908200d600f50045040b40c0c064540c43d80c2c015200e000300507980d0403103441c6e907002c01c01007a02080021340d181021501071015410340b0f4103040115035844207442e001c9866000040d0341034104151582c100c000c0e60b03c4a2624801081704505041c148806504180102c0c0c8920b410044188100a00001d040050b254090a2562076000f130000003c16084a0180262640101c210398074101d403103074030090302c6420900c00411302e8a140c28140f0410700d4030312060b04e401207417415a00c080e0391610400307040a12180d9a00244407090504103808800044c1c10803034682d00300d0103040001d070f41c459041552940d00300c0c500700020b031107440900ca20b00107a2040071103150001c20000906c01000140d0020160281e141400a80010303000c49da02c8100c5051401030040750240d06a20340d082075403041c1c030001d204503200c42c500b64480e2040c0400360420913070f960059225546c01c404c2c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 179351546 1250 179350296 179350307
    0x62a0501021e0301050a1809120801030c05180402010507020429010221040501050f122d061f020109020d0b04051501120803070309020406150e1f030203091005011203 73
    0x208100000d010f0865040c0400a9511043c91003004485c0e080003202c004c4048583d4800c0085641c44a0310b51040940342c6000780c045c040c24401502c041041c2940015642840c200750302c80c84104d0a0881029968bd600550701600050300c00da0304a50381d503501a5084201116070004002190750440084489500082c0340441d01408000052502038040c007131081200c040c3c5050301c030242482504ca80b8903009802090085281c0504200c0100091003c2050b29010040c2054a40c19110004545405180d225000144c0d0544c0e0012610706c0081b00c0305c02e03840060401d0404910012401040d517030001405000425810f41303612020409010410070b04002540d4800100c01e641c40c0c141d850403106122500b11350b10043c1641d0340c004001640c075442940084482940208200700d00c588a202461480b41456200004180a00129451460f2901c043c1410032002c010314484a40d400c41c08034042c0d000500745199921616010141d200128084e050282c21498249158040c007800c0c01040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 179352796 1250 179351546 179351587
    0x603050618030f090d08070b010b03060a170601091109150c010b030d05030c0904090228091a040b030106050a0803120f06010f030506150a020102040f0816062a050102 73
    0x140da80c010000103448800340340a4a0701148102d880741752102e46810a09410311a00d0002070100b102080040394090074200514050402034844042c0c186d215401048407910144144050f940428010402c02e07000c1d8120000c001c003510ac0b4a4108000400415030713401002d240c071901c541000c203205014250900c80c2c141c40401c200c1c02450180c40401005c0d00c1c904c4040d061902c028000030b0980c030103440b2a0011440319038003400030304904c02d041030a500d1021600120080385403103c0c000244145603030003100604c00d80d14914215443c0070703a00304401404104c07801038043d501c50070f002407140da407074103007100030001b42001d180d503240300c91036120507241c0040c076440307180482d1814060305903444002107108820a090000b03964850300000358000300350002040001100082e800c0f0156811740107842100d41000307034480b2142d180c40c0d000c0d4442c0580741d2180c04500d03001c8010004079100c1c60847c000a04150180110b402c5042ca120729400c3c6e034800160307407507034000a0f001c1310405a41a80c61 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 179354046 1250 179352796 179352841
    0x702040c0906050a030207210807030506030705030705042406170709060e0402031009051005091005150315130b0319050309040906020d1a120102031e0a0f06030506 72
    0x500441c20007001034a01d00907030b104c140805601250000820280c40d9175903a60803401c9242d50350b42d94985100409180c2c040f20443d00207401c00001ca116070074009803703c2a20030082c058180581817106000003007206424803505101d412211004801c1ca604144014003110790b1909000c0711100249101302d100a031030002005800388040007015401210708994020131540076a59403104c008000d140c00c166000300f00840d25250520030140c00159000044810544d80080140d4480c00d5002140d5110704c2815080041d0321404481c0205010045030f02c14a940c100c0701400c404100400d0701c42e85e1a00400c0503071030b0ba56014440c14581004a90001d810711000c41400580c0303940c4803600c034002e81000310b0140b504c42200f402004141e4054400030b141c001010807a481c841e08a01303404030b140600326030050409001405000710107001f2244940104c0158513488207050103041e0103c2001880b2446003551074090240224444c00b8503001107000714020700d0720307041c214420340d445d40e4080e5850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 179355296 1250 179354046 179354057
    0x210020a1b05090a0b030c451302030a050303040515010503030316030c03060e04060504020111060702190812040302071a1e031515030a0b060405180601030e010e030702040c 76
    0x10001a5030f6180859801801c50a01240a06184010921b4041480940740c1d20100340c021251000310505a03160010013040310b400c00f045040e20006025001e6440c4250a50790940c0005400e00b1500142d10380ca548041d046400c00282034407500e0554005a40803a10340c1c0104910b0f2080b812160942805001300328040c5246080c8600b0f001d818614040703104091503111150114030740e0180d0b004000070100342c03440e0900d6240c2860403200502e41120102d010034014500040c1d4a100010f2040c4114441c3d0010418810040c2313403025104050f0108841c4114100300343ca40c81116580c803d8000c82c800c1e0000c044650a08101038105420b200c142e4600c0700f010700091000410300103141204d440c2d0702d40b205959031202103050214000d80c2000f83d4119282d0b06141281c401400300852040c0b6071008100f20000c0d20004000c0b003072169101c0d85900c903220f0144411060354000c681e980040c0141800910a228999506e0079500f80101c0c0c4c0d415a00b010a203030080d801c282c05581c0c91240103103001c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 179356546 1250 179355296 179355299
    0x509010c030b0325080111070507060801060c0b0c0d0906021305010e01052a0307150c030219081807090c1701060219050106180207030e0307052404030210020a1b 71
    0x1181d640c01d0310510400010002c20802514004d4807421400a89581c0340248282c2c6105699070b001e6078401d00d0202d0391441480300001b6603d00c0342c40c85038140e500e242d5800e2941c211548810341055000b50141d107101c841044100e50381291846a0b501852041c034002da201c403070240c038000d0450440d1b403129060003d0402c4044c41b40c0c0c0d001046603a1420a545612251101340b601e007800700d10781d480804114800062848140000315005441d81d440e5541d00b400301e0b210001d411070981c000d1006030560194007080034203034503010f2500345600c1400c0043d21a0b04091308100145070031003070342c0300e451410f03903d81c108156140d1081c0d00300d241c07145440b1143d0480d41f401d80025550130060086801d003040e00e2294404021003900310000a00c0c20414410300e190702d09400e140290b1140388114041002066034480a05002c1501e400300d0320000d1000140c03d403c14840326030742c2613405000c031580c2c508000200059681803400121441250f0081043d122030745061004640e40b50610380000148040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 179357796 1250 179356546 179356549
    0xf04090b0c0a030e0f010608060108010912030e1005190c110303040b0903120f0709090903020c060901090902030108010204060f08040b0103080a0306030b0718060f0207050d0206040b0c010509010c030b 88
    0x5103504040a07401580e9100c1c5006021030041c40346003640c18250240c0c0401000880054001000350381c11a419205542d0f40d0701c40c09400c03900106401410700820601e468056402a8845c0b09462440400d403018074100c81041000c540003101e84000390761100d0540001e8040d18858074132000c0321418843e42d80d542c4000c0003a681c2c080100020110b041420000e60080c2c002e00a031408007404080c01c0030303203003049038428120700030440c2c0580014000940004150381c07030380102c0c640309405401a20400407080300340801d5500c0026440c5c140300c1c000c000000c495070544000c60003820148c1c0010b84480c204a00184007040c01d80c518402c0020703070801d10000c940c1c004105030440e0340c4680d10f0f55440140d6070381a4007400ca40c1d031002e004400740d0420000040d420518589401c0301002c08c543d0720a4036840242e40c03040c015804480140e101c0c82c424002c40c02c0000d0440d03c031500081c291400c25680e0110944682d2048610b064140d4461007403042c440350074050303448484040d0500703001c0c5011840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 179359046 1250 179357796 179357813
    0x25050d3e090f01030b15040302181e0702010605120a060b0a0e0106030b01020a0c090c0207080303090304120204020f070f170f090d060b030105070905090c0406021c1710050f0409 78
    0x1076858412500c980070060103a00a5118003030400c0040e19a001441003403118140c0c1d900b0500c800c3c2e002c0c04c00c3c140c002520020780090030b441012401e424002d60010065540750390b181c001c109005543d40c654004c00e180c0d503007074008800007520000805100361700e40303031000c20b880d43c0340c034680d000c0c0c80080420f00041e039001002c1030540c0c03841d00c0c0003c0d0100c514030040345014030720f00780640f41403140c400110302c0642d00c0c2c000c0c50b40c0e40b949030200c070201c41ea1604520303900c1c4002c03a95180c0c2a00180418081d14603035800400c03c2500003040035051440364180d14403641c0c0080c0e8112101a9188880c4080042250513044460302d4001d52a00b05880d02ea80040140305030303040b0620420b0648400020000650312414003050041d008201c02d00e09144080d040701c217240203841c41100c443d40000c0c0c214009001b282d003620882e03809000745a50724001102e8602080b00e800d814021245084200f52500100061245224003c5254054030300340911106803180e504450080f41051309040102e040c41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 179360296 1250 179359046 179359057
    0xe0606040302010513050918190209061909051612060302010801030b04060e0706030218030102030105100c0305041e0302010f02030c0604080903010608060a090c0e25050d3e 76
    0xa00b0314a030b4910b001c0d03254007517a0100707803c0158414000414000304a00018416070461000c900b11014000662010052083c403414001e5100c1d000c0000906a400e10ba01c2464090310142103040d030301034a03226250192207088400400312440743d01601240c0d98410060510414140410003102d411074000034032030a01400007078058948403001c1400c01009078041840112504290346065440b040d004020b54420408540c0c1c9074601c0401e016a450103200700c0e8100d034001000003002c000104419034500a04800540c20300805020000f0340004c1d8008507100098890341e2038400505510024050a0161500c103085501c10300c4500700301c40c0e0005119420603004541d0f81c0d00c2e00c0741080040d0140409800001643c010541448806900c580010041d684102ca0100d41c60f80c447c00d030201c1b59070080314285808600024880c558007007000c01459503505520b4040d1506540c02c0c081001da071240781240544031116250051080411010b1036100300c035201e6205582d0700c080c2315008440c00b85 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 179361546 1250 179360296 179360299
    0x809100c0c12030f0515090f090307140c0a0e0f0a09020621010e090c030712060621050d1107030303020d020c06040f120306230a0806011e0e0606040302 67
    0x6a000040a0310701401124900607880280100c80340003039900100501001e00c014190a400d05021a0741c0440741c03004948020301c0175165072a16901c0295558800070003800d0311085000c01c01503000071401315941100f680750b00303d004000300004135040c0700c1c1800d074035030240001a1901041c4000c0c10200080c0a400840c0d0302300c003203107238011400000e01c184a1000750b9105800b9004c17420301c449410211890498019100c1c4402c5c1c1d940b1500c9035038070b0351807a60051380e158000c2c00c0c0c24040f00d01c0389202500c4241c0164800542e0079210810303403681100910711485030004c0c1c3e034010001c121701044001104419071a001000d46080305185aa583c1640401018103402141ca50302c1100d040e03050700d6459a07200211440e03801c2c00e003003688070f802815000351a15280140c0050701103000f809207004442e0310310407143c9159030b901e0540b1100204e58100070f038008404600042d1481080140c00d000e00b00e042814070700a40007401c8101e180142c1c1e03000001d420034910070408107a90315030985080781e40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 179362796 1250 179361546 179361551
    0x20c0604090b1906110f0304050102070608041505040606080d020a11010e0102030705060106050405010f050a02030304320c0a090b0603040f140a0c06032403060b03030903030705010c030b01080910 86
    0x2d0b4000000c02601401558008070f1910900000f1641c0e17005a908608900c14800c0d11a00542009a03a8482c4a0b80c0201405a800303440e04004c1d51f80b18020700c680c46070149800c100c40103c2d502c980710644205480c19a52540c890300240488841480210030420081c0018484c104503680c1d05071442c0c41030b007401b81c1803103400e5081c6241a4028000c071002140c1c00002c1e515a981c54007406030441c5c1190240c0781c0003603600401000b985010300204d44c851081c0d03400440c110395071551040411006100b0340103103008040c0b006d0346041140d200080c4c0344da01c00000f42c00400c03294014040c41009030340c45841018240101807005071281402c481c0c111742c11881810030300f03800b41891100d01e044081901c5251180c004481e043c8071500d46c40509454080d90140203a842140020003003480b0700ea1407480140003078804000198465200458410001e42039a0414140600007401c5401906082d40e182c0d4490814460b40d5030705103d5004500e0313090070411174900313265041d5640e6400d6803038410101507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 179364046 1250 179362796 179362811
    0x5040f03050d090204020301081b0a03050613020103090203010c03050a150605040b0a1112130e0903030a09060f15030203011506050f0a02070f1e05120a02061c021612020c060409 78
    0x114030f9042074590b1600600b0565495a581801d076584624290a02d0b40d0094600903000f00d034a0b006051340d04a9401c1401403809031190740f10081084107502c001c9040c035980300268001030b00d0a0044000c241d606450000d1940343c0b0340c28034400d8546800e0766404003680a84240030540c0c000080c0c03000d81d02110304440d1290b245c0141900c1d20284900420454810020b2049101801000814040b914442c00c03226071a55130b00b50040d0000306550000c0c1a800610010303410501e10785c41603038900e01500c40840c03e5804806140126031754101e07415514080d80000744154182401083c2403242d0031140400d00302d15120000b0030501521801340b4411400107000f5202920822003000500424494080e242d03070b40742030401343d4650364003403100c1e03042d000440000d82d858900600e42142e42c215010340948002642004441c1e8003880201c0100d41400d00340d9803192040e440500362100c0b50740c0408219a899040054070941e6102c0407004551100c9003650407a150390050724100ea507487d1000c580701 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 179365296 1250 179364046 179364067
    0x509010c140f030c1b030403290112051e0c0103060e15090c3a060f0603150e0a060e09030406050f0708091005090406060207030209070f09090f05071205040f0305 71
    0x17841000f50049010500c0b1843c44e05150000c4028001c03603200b80540761401c1c0240411550480716802803110714542d41004100c010040c00000c001140300f2000e9905803280300051071168111202d06440030391050800404a5800d84101005455100003602c0c0074170f01822617645024800c00c1040c05812440c01094a01032075000f91151841c422496804100050782c41d0341d4110800700d010000440e041e00005102412446a4029144000c1590403d641050000e6010300013284401800b280010000618110203080d024000d0030030900205c5c2c0d003490040c51510801c2c01510700d40581d00300308420000560410121002201c40406d410b4544146042040c804e0052000281d0411441204641002c0d8001c004040c040412202084410303203482c001ca98400d42400300940107104c0341c0c0401c00f0140620302007800b0b0342d201d28280ca03031981c94441c41c405503041700b030710074a01d540c4600c18000c5080c1c200e41c00e500040b00750903080003c1e1510385c84900030140824000307824088001081d103500b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 179366546 1250 179365296 179365321
    0xd05060720010509033105010e0a0807082b0e04150306050a060e1003081b0a0503040602070e06040b06070b0c04050a030b0109060905061003050c19030509010c140f03 73
    0x500722044020401440c0041c82c079500c80e030003001042c42d066444007081565040007050300d083d610101c5151282642460b00541e44540c1400c50203601029040d000680d0a45c2000300402400c121005441c03001c40015080307000007420190039101c000085201544103602a2030b90301140300403180810140301506900c0380566032070704040c10300e03400e0108000c0e0611884c0c110204942c075031003808034141e845203035880480d0700a0000900c1244104151710b601540b000810401a04141c2a0b84c07200c2c0e030345d5465510b103070f005910000140e04140c81c00c10000c103074650785e543d000409480a2112105440025a00d0312071814010b01a8a080c0701103140300e6610b900340c4001d404060032003542c540c0c0307a04102c0c03001d003000d01c140700a060400c0300119055101e802201d00968000c0c080c5e05041e80346c844150060700b0000c0010000d104103020a028461180368181c501c240141c4000810307040914049003500c25081529060002051038030f4180c1610b24229040c45411300c003929200d448041030041d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 179367796 1250 179366546 179366597
    0xf120f020309061008060601020a020d05031204051014010e0105131d03040905100b0f0a020a0609080c0c15040b0a0c020303070605010f0609031203051302040504120e0d050607 77
    0x16410310100c1003011402d80018514000d031802031840200c2580c4500d660769a1104544050050f004401810f0040c100480c403c19024403c105482c2021200907490001d44001c03902904c042e03020134801e1310500518840c0700d144d1124841c819640b0360610083c0c60301c1e607006101c2d643c02003110007100b1034810f0055014003407800c0c072021190f607114507115010f9900c0d04240107a6502c2451302c40400c242d4600903081030110b0784e08000d81d07070810380070040c0b2840d5a0081e001c12010f40c0261880701000940901c28840140e01c03610302e17103458014010466103006101418113014417403d9001d03016a08900c0f0a036012600c0002000b9561a0400011030f0206a015002501440085800d00030001550440e90688403c84002007175560360340e004071408182440051701c00c0c90408003030180c00d8800c1d003050380c0c0030700030680f03108060019502040c00c456003181c05446003e08100d54250246d80700042d0200c2080403251044910300da5144d5988880c0b015001800340440c412001c0e0104200381c00a54 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 179369046 1250 179367796 179367821
    0x30a0f052103070306091806020a11030f070b010b09030a020f0f0919110a0914270604060602010c36091a0a060c06050a18050f0105060a060f12 63
    0x401501000080181d50b00140c40712000b1034201140420004c21500c6070380c41d0030008110381c5504a0031a1140002540904e0b03e003000c0080301464869244130400060100c41c888140c4241d64900030700703103030094002c1a00f100d0000c100400080310b99640c000b4800048640448007081640881000100c2810340240c202d5008000102000040803000c1c01c100b640c0400201c09004440702001d12641c41c0c815510518040785418000380201c000a5502d24200b21b009002000c00f5040c648400750b40c0d461041c51016088002400c0203054101030141e44002c0480740000d0040c042100d80252174140254090003049105001d41e21001154124107100d001020f164141c10b144c5405106005c3c090a050410001141d00e0001980e0b05200b210700046486d00d903141c1c0c21a921903034900f0060280030303003040c0f400b80c1c69074144a9900c440c428214007940c03103000105856227402062a0a407080140b11620070752201ca070810131607030007250340d6050700401c0c5403000c0d030300c10780d1450b0b000208070030000c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 179370296 1250 179369046 179369083
    0x21f0b0a120606050109150f03060e040809130b0d0f050a0605070206070f020a0f060c0207150302040f0e0402090606030403050d02030106090303080610051b03040506120f09010209030a0f05 83
    0xaa101c0685000d040440c015030040c804551188019a4845410300c509018028140c034202c203081c1c403a568001740e5040c1c51401040c03a075907070818900d0098007581c2c2030780c8882c00040c02d50444d10344000c00c1c0c240c03130015501c14080301100c5000110302440040b400b80941880034041020460184042810750382e00080030011418450700c025a0303510204c4d004d60115140400701d00c03096000003152600300342d0141040c016041e003a600c0340060525010090203610402c400401d10313002d08050111000d01d5640c0050322680303810321100009460f5400000c0780c0802c0c0b014400941c07120b03281c1743d41c400419100207607280c8440c6022541391050f0641503045502c00300001c15800ea11009410490380203035a00717111a120700d02000310540c10960341d0000300308100002c99404a10940c914600e8070090141c90400d640e40011800c03503131025490700501000c000c1001400811000000e400a0544d0001c5081014030004280e4800100a02400c0c002c80c07103160b54200170003001140150b00341c51009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 179371546 1250 179370296 179370299
    0x60e040308060a0b07050606040e011e0218010320031e090105010e160e010e030a0f060f0e0d02070308030a060503010c02010507080901140402063a140106021f0b0a 72
    0x10180c01040d01c2ca5031040c800850002950040314054450b4290001c01410490300d030303403017004010301d41e0f00803d8905540364840079400b08000907000b41c09002d245030159982d2800c250101400b800c2d240c031203052500d45a00144030482c0001d0400c0024061030280ba41da40301d401000c21840d2400701070030240750503042003200c102c07410740000d4100c0707500702e20350a0b1a449000515454885070740040d00091103102c3c84120039842449401103100340039041c2c03900d8400e96114188020701c505000d90741c2c41c0c0c0310501da2040003980d1003905012040c10020744040c1c03c104030700940742c644512000d0b02d90540070000c40d001c4405a0f011b0401054024000c001030309942001038040d020485001d800f0810000028082d10750602442400d003201c400d8840340d580d12682004150340054040d401c840002401c558003903e40424064040c4c40342c42c004958441451a85c941564100c446c40c0c0031039440c21004200c000e0300041ca00140c42004601d0070b01607012020700720000c20400c141c01e54496090b000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 179372796 1250 179371546 179371553
    0x40c1209140703030c020a0e06010804060b12100204080f0304050120070f080c030c1c0605091903020a110a030b0a1a060412021305010b0a0804052104061d0a05010c0501060e04 77
    0x1c01c1110b03842030345c40172040c942c0c45855122070707001112789031b02084130030000070300040b80d5520010101400030320020500c2078400f1072a00c4d00c00c40000d00c0d00004e42c00034040c05051002c0216800109616000f140ba090038980020514000e080c1404120141c014412080010038410700e4042c00c1c00040100c00f541e586c01500c3c1e580c8141e0b0304618080c4c02510b0a4086030b0404808607100c18110307030301c00c0100130010341c0c0c0c404c018035005041805500507840c0340e42007030481881010109010350700401100c43c47d0306080725068900045944034804042d000c0002424003101d03158400591100001d041c2e181e00ca01c2d041001c4811312195204000290214120038104030151040b0300030b6405100390450101c0d008203c500a01801c0020703003043c8403410414bc81003545942c0103105a0135200000e1030070300520711450141300384005004001c141806040e510410204461034000700c180c480c44049800b0500441d0140511030411901a5446003409801d400c12030040980111000d280c2c42c00e405e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 179374046 1250 179372796 179372807
    0x2090703090f150f061a0a091a091002010c02061302030c1201020315030102040503210d0203010902070b0f060a0614120a05061c110613050d03020a050705040c120914070303 76
    0x803c00d0355000d291204410642d400c0703204840030794011090140804980c941d0031300090304805a0a400c01180781c00126024403400d614085020000302070644481c0100d0410041240c8074540300110380c505a0360200e090350000341c5d242c028411091801d42c0800f58004030342013130b40c0341c403d99801104030384254003800170550007588540800750001e1403120008003014280d200760b00ca181d6040d0702140a102c0c11680f00401c00c0d40d28800031085600d40342d0030100e10410780e0800d0b8002505940c0c01f00e5001c1c00c2c0401c5070344456006003003002260103864070728009018a4518001c2c441041a03020058600710300c00c808a03101c8000600404030780340b400c03017800c0c2c010b0b000c222021405006080c115080314111207103104940e5900c841d508100d44800c0040c008150803030000130f243c0c03000130300001800383c803032403001d140c4640a075007d01700548036810418070709512607100728015468103c020411641c060250500300501020204280400f4100550250b220084002d1076001e60b072000004c05030050b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 179375296 1250 179374046 179374073
    0x114062203021c020303250c08010203040b010b070803040b0601021e0a150603050304060e0301020f0a270f050622060908010e03090604031412030a09150b03030702090703090f 77
    0x8850030362000326116980c1e00103003610743d00203400d5403050108458240f4401129184100f036090507155010058035114080011a403200d101da035030000602090081400c542c6014201c87c02c40d040ca0060184c0d1201c1540c44028406400c003034408003c01c020340e1003403000c00200d01da0301091401d60400b46000544945540340c040b18084203040311080c04240e00d008840480c0d401402a5007030618000d001da50205250b2a10b0354903540c208070550131101910043c00c0c1c850081d035218101034003070030714140b003180000c4216400d07555010401c00c502e1201181d200103407101a078040391507001034a10719803846954600c55900c40016200490000d0340400101c0481d11010005d0144880d482012134481c4280010540c01c40700401090011440c401c907034884104401080703c45030400340890514a4000703641400c1c4482d1500101d00078001d208184458446080604000c100241d9001035502d204004000303000341c1a040004159500943c04821400d41002c0c0d410302d0215246032988518851 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 179376546 1250 179375296 179375299
    0x11d070501031a010207060c0c03020a090f050604090206040b070201050c07060302030402150421080c0105010b0a030606020f0d0305040f080f210402010909360b1e011406220302 78
    0x83c140c0c80d041001c449200b00c0e86194041e0083c0104506014044907645025042a503101082c4000040140c075108968001000b0340715002072052402403c200c10340307901421145c0302d2070030201410b0160755418200d600310340c019103ca80d41c0302000c1c40142d41030f002d00c01c0d0419040c06902c03000280315405400841c8110702c01ca412030030041c2c44c000380c50118000da000755403141c0c00811800c00c138440d260340705054644c0a1842c00b401c040c00c05401c1d03800d5032000d0300180c43c2128040351588110750580980710240850380094498520700d4021144d0b1900320180c40300800d0b45440110741404446444004030b950403080007035641c00318a0400c145036004400ca030100c000601b9903048840c43c1e18004d503000b80da05a4480310228541301c0b50f580a00082200c03084140c00300d41e401c0d040300901402a0003107803800c410000d800070244c10050716030301d40100382510040803a949174015081e031160650543e4440a01801500001c5020031428060804240c3c08030040700b007034946076011001c200c01145d20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 179377796 1250 179376546 179376551
    0x406090905060708070503010305060411280602070b0a080c0f040b070b060a1a0a0309031206030b0604051f03140c09010605070b0604020a2c030312070306060813020103020a02011d07050103 83
    0x1038085c1c0031110740c0301c04d01c40504507801090124000800d1440940004400184114502d40740c5000584840200321044e1490005000080141c3c603014400c100c0240b080d8802d00d8240307400d44401900c6408000e011400c2c2003000541981480e1006090b41e020344180c44a09403108068903080003200341c01c2c0d81d02c0e8428603a9100c0003c48a0500a100061641d00040c183c149040f10000f94090140607a0840c00e20103448080554881e40d881600000c1d405511074200506160092004450001d005041c1e9403900c1b60140e59801079104a1304100e03035020406415034580d901c2c003113003481140544c8982c007484120000450a07448006801514050704d4032525580f078400401049200b9081c0038004200b59611000b1408076644803100c150300a400b100075036482480001f8115800150a03160340043c035018011900e60601c120f1000d0a040e0401c0da0310703820803030305130312440c4003204000341050340000e14410000c0c805c2d00725246006000209149000800708050307100c40300c50003a20300091 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 179379046 1250 179377796 179377801
    0x6020c0303130e040f140c040b04020a0f210f06030302010b0a0e010513091e0519020108060d14010c02010e1221060a03120305010501080f07090b090406090905060708 73
    0x140100440d41c680d80042c0c0036200310761401280380c0c20654018019074003070b03a1582160300450601c01c000f003005400500642140600b400c1080200c50200846500540c0305001d01050290040c500b010420722900b0840242c12841d181149050b41540c400090700f410410f02045280341500100c007a03031700c00e400a0189422038400c0c001d104100348580700091304110010001420002c0c8014100c1a0300f040124550101d92103034040c1d2008000040d0280c0d02084004061002c203204400300645c40c4c114841c086440c60700001c1400f04040d100d00e100c5c40769000301d40200804451084004020a4001d0100c42050303d40640201004a100328060040050b41400d800880c0101d0300080c0c0d03962080c010b00c021171030000d207070280c0040003181c02042c24071020020a241d0103450515030803d9401265a60410300010030b1340c0005001d40000449440900280c6900110600203aa81e001e02c031544800404001401614043e0700c54100070b27252155074000d002010940306c3c400d0006844000164 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 179380296 1250 179379046 179379049
    0xd0e010f02031c1a06070c051206191503020d03170714180409080403110406050105030603030702041a0a0807031703010f06050a020a080309010f05160c0f230706020c 73
    0x24842c006810415030f4545121545024250307100f84442c41804d1410402503007180c02040b0550703c4420107a809000d084400c1000d4030b00750071100c41180c000c1d4050229400d1111680d845a1411003240c1c1030561a20084011254182d5042000303680090080662400c2400c0c09800c640800c40550b070410790480024030a40e00820f400035048000644591070006450011401140b0000c0d081c2c1d8042c0c1c980310500042130001024101440c040c04d1a445110718400c00c02007101c01d250300090600506008010752a5408000d40d2407075078065a000c0303041039240e001e4aa103103075410310301e03680f1030f01903030b40804c118000007505030070b4a11a24008032005000700b00a012400244520819440801c0d021b00c0514459405000c100919004031140b8031010359406070280c01c100c1d406462a0b54400310449000070074010325411101800107075110604800d0b00800c0000400c0d405003000001001e0324080001808501c04031500303050303070754285e9140e288034991942400c1c441c0000511403008000303d03e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 179381546 1250 179380296 179380303
    0x605070f030606021e0109061d010c03092d0606091e0504020a05100504150e03010b0d0b0a02070c0b03130b0106020d0206181f050106021b03070e0402060c0d0e010f02 73
    0x41c2c032000d0b00188010400d50400e50003045160304108807554a4001800000303511b4040c1c0c07009801d00610192703440401c5500d0500b12040c1d02016802c04d4180001039000c203071036040e00d02012000b80000402800f00340e4401c40c82010885005142502d0448005401c0b0600d034480340b00842c46012160418070000ea405040e2030054130042d40c000fa10700000c201c0fa1400b5201c2c3d840c6440035090290915039100b5078200c145d0352a6103504045548511482c206107400e00c140b904004040761540301039107060700d80c041842d200420f891040342d0f0014002d03041c40a11f0a01c0c5004015480c19240c0d81e2502154901001c5000170741120710100c40c0c000402c2407800442c80c43c603481c00c90b500806040c1c1d280d1030702d075003101072a00e0100c6690251403014642e210703400c0320b420070280d54488007007419450104000e181102103808071600100f8940041ca86503008681c032000c5426025000885859900000704640b04100f209100c52044841c1c504445800c038241ca1042013003601c544107141e226140c280c4c0c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 179382796 1250 179381546 179381549
    0x10f08030414061c0603050a021002060f0402010e0109120f051e0a030e180f0702100b031e011814070e09030d050705040b0c03040801060f030b040b04080f04030605070f0306 76
    0x420551a4600b500e2820503402410319814003041010380411404035120445203507400c2905c0c29044481100700b9402d185031002c0c9940c58910041c02940750501103031007035000107031000341000310041d82a1541d030310074581100603180e45240554030010515190180f40940350302110140202040036486095440c03e003240c034909040900500d0650b0f030f4040700c1460041001c660701803c0c0210500d42c0b40411080140320340b00840701003006040144001c1d00d440c0030700070f1441344141840040401c644000c24515032120b111340c0d4804c2a1010110150f014214910a50941c080c3e80d45d6132005010101003242c8400300e40c1c00568000303549419481c805d5100031510290103600410100ca600720b01c035444035a0214003850a6804d080c0c80f070986503103d40c071140076040030341e00c04141800050720a01c0383c00010400c60400324440c83c075603500c184480c0c4004002409510fa0034002805000d500012070b17841185001c0090f6440c0c0c0c4901e000001840144d4620000400e0302e00c0aa0005009208400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 179384046 1250 179382796 179382809
    0x50f010605060304031103270102060a15090504060b031204090608011107230d0909050c03040f08181503070219051f0f090c030b0c0a0e010e010224010f080304 70
    0x502c2e40d031342c85c0c800383c9004142030031016040c03100300003101001c00d004031468443d4482c817040f403500100d004002403410601030034544169142100d1000740c3d221100f140012140c5160340401d15541c0c03828184010040030f540a034141c014800401ca280e85150000e000783c40300c1410811811392550101c508948104529803814074041080a004c50008890144444e1240501c80c1c000556a450141000d290030303441c4011401c4608103010811030b070f004860b48009d03c0c20116003503103029150350303002c14695403000d482440002121802c06483c404008000701000e050506a45180c4002090383c1d4402c841c80001400365444684440300b0482c140541d40d9006402000241c41d0958031540700105008c1882c0c0660b034455020a400c4114003c0c1024180500420241145142094548190014842d682018040140c0030f0354076041440c440d01810700b8a401528040f10500507490031440b02c5210f02e01c181a071240b088402040d0044030b058400801e034024146980b406015543c0c01a0b00940 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 179385296 1250 179384046 179384059
    0xc060f050f0903030c1510240c170301060810140d080d020904050c07210f140c031c0b030a02060f0703051b0615101d01091e03050f010605 61
    0x100c18100400307000e010418001400d44e440d1220709480d5038074024401c005071500503a25800c10002c2c881c03200d84040189000c81c0e4a5001d0f410501d50828400c40340c15010341445408030483c002d0104020400c00d407104008516607a03541c507500040c10082c1e0443e9480000d80314000042081c1765040c1e20700ca0400ca000d0015407858800341e4a40043d0342000b413407003824030342c24029921580d03640e0007014090309664105542e112020f0800d6091520059544031052020303070f1545044a501461407903044009246c11502c400c80c80d003024070644102680196184400b1a03081d442030381c10060030316604d91610301046464513040a154448141c1c80020b176000c1c070f09009282401f1000d100a142080c030900d882403070318892100c00908003013802240b107583e03800641085498101381c005140384a40c2220380b0b070640ba02d1101d00800300411602d980c01c01030b8150721640c503541d00980040c806440a40c00132002d04684200c0f45406000d9840709031107920030800c0e0070250b56010b201d540305070380e00906031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 179386546 1250 179385296 179385307
    0x140105150f120102190c0c0e010e0f0403020106050d06020309010c081605161a040318150521090a021f0806060f0c0706030b09060901051c06020d0c0801030c060f05 72
    0x2c224024140c00140c1040e550208140c0e4021000804030803c8801c0381c0d142c0d0a489051403d2005558005400050101e64040010700c00f80100000a9a21840d2625102c410b0356441c54201c2c090496030384119002003040440100308421900654412400c0310003c000c0b116070141e04540c1e880c41903030002c0d140c440c50700c40000c480d17105000406078203484245101400c02644d5600b00d485924001a0810b008100184820144e228151100f1610b1024000d029a402e00c092064042641403e500900100042200034105000200c0612502a51000585151040f0000d03101c2e07441c1700080780306101c04a1000c1d2807031000c1120146001141d070b00e02089540362401d210444d48186281d9031180824840c214074114200010406400141d0300810107000701414402c01081c0601443d114000c0f031030060049440c0d4036618054941d498111540d1507105040200c002d2281800400c021414080d00940c001c1c3c01020360381c100c034824013494500c40d0b40c2c1c86003214411001d40e29400064002c010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 179387796 1250 179386546 179386549
    0x15040b090c0d09020d080a09060f020304150f0e090a05060f060f0313150e0c040f18060b0103060b070b150d0302060402060310080d030509100603020d06051e0103140105150f 76
    0x12040c0b4661005e080c9454403011901e40da40c103030700801c40d0344000031810b101c00d0000e15841a1003904419860000f1400c19040690f9400c241d0000c0003860104888048440710308c600c500010344000d0400f41022680b410500000341c09400700300c070141d002c0d8046803040c4031641000f0040303071040b0f0840301c00b903411034549003d0400040c44007482525034041c0e412041e0041c00c158841c0071040c4008a00500149220900303200503140c101c02040600340c600704140481e482030484da4007410380c0c00702c4000748405010006030300030300c01604107210500000c115002040549410540114101d040001400410320108102920988002030041e0800d0300800d0060522001841d04485014140b410380c548030000319140240078941c000020791182c052011021081c050100a16004a0180026402c507008298958643c440091800c0d9889001440940c026a9940882c1d0004034281005507580c6c02e01810b80154121903070034035441d1030b011440208003810130240d4034402900865900c2c52940 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 179389046 1250 179387796 179387801
    0x70e13031e020a12050304080a0e150403030201021309090512181305040b090106060203090f0d0b0115170402090112030e0316060801080102040b3015040b090c0d 71
    0x604505105490312000a000c0e003644802003440510741c01002c1c02d00b024200184403034044c200c43d02c1482410000d10000c6210f11045813000301c010304104040c21200c0004c0b543c0700103030102410f811a004074003c800c00d541900140050041e0752581105140c50389442c00c1100c1004600030025480340303801550003240040a04201004420750881d1010b9120104075020405401001d8581d511b0040000b0030480c40103054015117000020005a400c0ca54069942d01c549040320b482090300d1143d0019560300d480c903640d8a958480c00c8024a9692800c0043c40d003003c80c058100451001c8070f20941c0b10030241c0100d0b00c516002890311351580d203808a21015001d443c1400d8040140c0c994203804140c408000e41e11801410316199591a80350170402008600c06811804040c1d0041004008140301603080e2408500c0c10144000f0503d02210682070314140c101c081e40d403148079041040200c17410030000c00c2a0039001c2c1e600f4420b6410300400c20a01c000c080f00c8200542509200e03513031710070303000c2e5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 179390296 1250 179389046 179389081
    0x303080403090902030103120f02060f13020d061109011d0a0612020c010c1d010306030c030b07020f0d02071401050a0207031b0e0c0d0b030a0b0723070302070f08070e 73
    0xb4140034405584642c054026079200340c10640312001d144001c0c05546601060380c15110081d0303c090003050800c045000e00d07000000e040c80401007002002003080d5612a0045002d85034081f20400407040046440192038000000f45408191000010780e01000a51143c6205410003032000c1c101c80d0601409079000700311085c0d03007143c00da428002c0c600aa17000f4031546485d41d0040e21035081c8680d820307454070710120728110030b14105400d00d0307407c10015131218030300410b80394060040c648a0351404003ca10b00090114204058071661103010304181d00803400b601a20b5881d4421410311045500540380c0b07100d6040c3c1240168082d200400224031a031031480890268100d0131380301c055441c00c0700425987c00303580380091208005040846001d040c0709115140d881900035140300c0015440d401c01304040103180c0f10620040c00304184404402840708c082401c00350402a458403401d0500a540d071302c00b40605038036100c0340240461400c0300051260100c466982d502e00a9544042c4622242e5900c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 179391546 1250 179390296 179390303
    0x3031b07021305150d02090a0207030201091208040510060806060409060f020c1032090109060501030f0b01141003020c0715080f060103090f08070201170c040603050c03090703030804 80
    0x24012100103950360344605102005400001c5400c2c01c00840442200d5024281e103445172400c000c2100c010707114814125031011b0607440040c3c50710003500b4240e000d46240728009140402000c400782030303d500800034030b0045004004640b4250320000c20202241c50074007c002c00c030b41c42140040c01a203065000700341c00511a00e00811010340381482c0304282d0304002036500d160b400294003104040c441d40f10706070303050130a2000d107106410001400325080d03a004810032080f010000014001d81c1003500882c0206502c090100025a501c0c10518441014404102c0c0d0019280f00005031541d10704440c0442030100824540307006001e280150002e6100d40102c0d074160103442e40024800040020700c00081500d40c540024514120356180d0300410003c01003418580b42850b03400c04500d41c0d4030f1b40000346601003e016aa0303144e500042c0e40424205242c0c10f5841240700400054911b00345c09803046424a440c107004c41c2d199800050000c0c0001c40f00c03000d05034072252080022034880e000e0140c11502 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 179392796 1250 179391546 179391601
    0x70618030b070c0b0117060916051302130902030109050a0b091305150c0a12020a09050108040f020306010b09030c010206041a041b08160503032d0d051603050105010c03020303 77
    0x40f6940e501c00d141c0401d0b80b01c50202e5911000311400c0700300c1401695070101101c0050420f12030801a598110717655401410b0141100034100817007070300903904990816a0305640200400e65900303114002e540709000344202c00b4201400304104000a024000c01a94000c0036184a6a1047c50440e10040355180a5600c0c2c4180314030b04070a4829005440d0041400204c0140d90301151766024200d00c21020351484a540304011011340c0941c840c0321075094070400d10f046052919a8245040c0310075214a003e9450b02400000141c21080c610060615950541c00d403107904641800598070790200321800f5069602c0a00e00301d462004008203a60302c10f103d600325850344004480306400140310b40d0050300056101480c6c00081c14221407030368005107000c80085142103100150151100407120207524124040710401c40d145010100740d803640e0b4000b0804000500d020210000d00c400e84040040121307140000101e1254407072010740141d2074040c0c0007546180c60708002c0d441c042d802c8a402408020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 179394046 1250 179392796 179392817
    0x6060a030b06070c050a0609030305090103050403030608010203090c0415050306010e0903070c031202100203060f011d03191707030c0308041b060f140c1b0616080309070618030b07 79
    0x15034540207451054012849613400c1c0382070409101e011160303030300074009000381c0090401c0081d602900303c5440510078a001705075901c5920307040c0e002d06036507040401c40354000b00c20000c0b181c00015040b0800001202c01b449600b9012420021541d0fa60003107603016040980107010604d2101511034005c440d80080300d1801d1066210000f000115800031900440440c40c0241141d42c10481915200c8400400314558280500003e42d00e5600c84a0981440420342c001d080c000c0c40b145651a41c000043e058414180821000d0b00310401d40f13507000c03110340d0701400052440ea0340000c00c2d80c0200b640350711102040142030314140e5a210340203004030344100710910700d8580860428900740040800341c44807000c500c00c10b5030150031440f12030300d51241d02c101840291141a00001c00c0b42100080b00d2040000c80002004030f241842181d10f000c0c0780103e80000e6408202000f0300840c0300b10041030a6600312926808c0803030b1800d410001c6c15001c41c0c8564014400b06015121a94000455080a40742c80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 179395296 1250 179394046 179394049
    0x7060c0f141c0815010f0c08040b07020a17070611210c06070c052d0f1c0207030804030809040f050711160806010608070912201806060a030b 62
    0x401190210322030390800e6070500c0710141003001caa80307038160508041a040c44c0003c0b040c001c4030a481c00660400845d0303460b401585000340c03010f40905800c000995070b60b545440321000c0c2a80207070310803401161025000510840010700200400c0b244402074050300e80b80440c11100316000350b8400c26280541310382c3d01d80c4c51030540b0101c654021080b84183e21400f440882c941401c000038910001e0240a1183c40c00007100468500e509506c0480310aa94036900c000240d034206410404009038424860482800c10002413070314640c0031100b824105201384000100d0316820070340b00081c0b000000384810700001c2e505502030203003071901034000278410040116003410b0740c1c8241e84075000300d031400102001040e810300107a150a140442b003403000c00d240c07241e0320b540e84005102e100c003000300d214049183c50b41724040820060200410780307064520641071036100d5000c44030342c035200d80703c40c134101022a0500c5000c00000492103a00945155600e4051113510750104c0c0301d075001c2580d60710065406 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 179396546 1250 179395296 179395313
    0x3070f030c030b06042d090501050c0c0d0f0c0f0609150b151804090c0e0106020f060709060e0f0301110d0207020f06030f01290c0303070e060c07060c0f 67
    0x1140200d4600c4805859401c2840307000300042c2c00300303009506088200c070001d4412a211080e0002400c4102c0854910040c1b405c003c1018071402803803542400d040c01143c20502c0043c210606c1180161340000940c05010703500d02c10359940c064046500702140c407012400488014003003074040c100225003c4c00e40d85e1080c40b0100011030842842c2e6482440b10300500b00002140f0080c1c0c600c01c00507107810120148140c0c10040f500782d41d0312594036104401704200d0031011740f40c028648680c040c80c0381d586038034007c0e40350800716420b42c0080c0310301d00c00201c0261007413180d001145c10300c0e20303207074011a80c1c5018802c5030407240000c150199240c1c0c0c5480503040700c2ca001480e15180c015001a11070301360340704000c485000c42001c98852141402408048041030b000e207811514490b0344801d4020143c200c050094001c2d080f5440300002c0402c51031b070089408001584503c4460ba140c9240e00790550800419015018581049910801e010701829000b042c8034841e0a02810140c1d42900440c0d840c00c08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 179397796 1250 179396546 179396549
    0x10030c06120c020615090402040902102c0d0303020c0c130603050c0306040209010e0417160501050f01060807030b030102040801150303020d2c1207080f2a04050603070f 74
    0x141e0010000030680454401c0c056000c66603c003070700b0181404801c4036040d240800040b807007091600702090440d961580142080e59014050540d00110041d0103001400741c0c0f010782c01c0d2038102d207810344400b12502400c4500054004c5c0007510481042e142140290040c44e0103403040c2c880c501c04914641e4a50340c002d4458005010041140c60661805905100f5a81034190003580300c00240070043e518101160305540c0758100010140d9528280301c103050700c42044800e0703075904c009039802c402240c8075a01d08241d80110000d000646a2442102c00c0c0c61702446100c0018040e14040b501c600d200740c2040700401802000542400d886002c42c5007183ca07140c40403444c03002000030420070180c040c0942c01c1c07101e990b8107003052880000820403071442c0600f4401d4200745510425480190342703801044000600190844019640704c44103141e54844502e803c940502c1488540441d111000e65000180064003083c0c5490380801420320000c0c11000d45050382c0760242e21008952141a042e80c0c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 179399046 1250 179397796 179397809
    0x5040c050111060906012106050705090f030303061f0908070f090506060307091520010c021209010e12030403120504050103060906150e0109050303130504140115050310030c 76
    0x1424a05030025040d900014800166600301004000c020031012074114115050518001a24000d00c49040300302100908010070180c9071030184481c1e41c0d030142c0a009200015958a600380c0c0b1410101980ea0108440d22580040010b20b00c0b55400b0001c4070040c1100e0240c2010441291180901070404526811001340301d41d046004011061b0240aa103401240c00e42e2142c0ca1030824010081089485000d00314a8a46122415410307600c544041e0955481e01d041c880c010329509800240a820b003207800b90b006100c1d21440911100f0224110360307030300d07805841e201500d40b0254217000c815485508614001d0006100002c0440c890500f08007051f80569510b983d0303541460000b4003291080d0300064040c80c9004010b01c410030070031149000a03001810b2050f4100540c80049072040d000e80c00054150002080064601800c1d003d4041900d200711010301030040c20812011055400344100100070f540440003200060040300215000042041179803400f5449460310b82040c900ca60004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 179400296 1250 179399046 179399063
    0x12050102030a0513030f030509070e1311010f0e09060301020c0105040309030309080a020d030e130606030902040605241e030f1807080606012001050c0304020108090d080c07020d060504 81
    0x4403211045201d030581c440c8485265044c03850882d1070080a4440c10486141810355640124042d901c080150b02e00a1800c20213440e400c1c681009000000025000c1c1168501e058032080d0900398040c2e0103240d2450750540d0307401800120201002040c031000707000d540c1c041d5030800c41d0582480080c050b051003540030f40c4610740403d02d1032800900d101102d81c071254203600f02c1c900140050b541c01008900964041c64100418429080010041c141064440c40828504400092007a80580205d00c04038000c403800c102580d6a1414802ea41c10001d104510961240b500d20b02c120101d080a440101e0f120a01c0315080c035a203214119041e441a14001d4900d441442044800d44660201405e40c0003c0b0300580303022450700360700990700e8a000e0005418814007810440c0e0b443c030769401c2c840d21440764500030300a42c20450440d0100d68401c4e0360a0340080c0480303002624807400003803d0443d542040e615403400d0f545080d54907840390007017401260b1008440b01c040000c900580900d500036402241c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 179401546 1250 179400296 179400301
    0x31614101b05040e04030809010e060403030e251710050f0a0f090f0201110f03030a0f0605101b060e0a03030608190f170408070803030a061a0a14041205010203 70
    0x541c0c0034078105201c50040040400c02405550308a03411240c000f40c0c1400e06004a443c2c1400302c501400d030203010022548149402c11040c50307416000365000302c1403401034400340013030014180c0c03800081d6031074440141c440030000c10050700c05005131600c00e1006e0041d07807a49203c018448003a104140c0b034112201424605010f012a407a00c0360000c40b04c09000c04014402c070564409004000e02c0101034144408010600003807107040c4264403141e030f19841136982e07078500300d0081001880002e0b4080f4001d0b15014000c1040e00b03000d0207405410020f5203a00446d50380c00624401c00e00300306401100e506885600c1e00448440401000d810144a610702160250030700100c2072900d0701110441030072041d54031454010403850310901d5540c9030010344044281d00c0004001105100d03582c4050128461090700288548021010758015241f43d5001c0c0f1900c0d65581e01e20f41c031803c802c000140440800c11440c0e14842c0a0a600a00c4200181701d003400e0941c0c403000040103035002002510280d400004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 179402796 1250 179401546 179401571
    0xf06010504020702011e030b100306211a070302070602070308040302060708061e1503012702042301091a0a1215120501020712090303020f07050303161410 68
    0x14150241409850450070007005400003464810019004055488601018160b587c4250000c50103980013034503d04100c00201c4004006010601ca802d2609034000780c14801c1980c0d00407104c50041e002130744200452079000b00105501000703070020303080c19400c0003604000340403400606003032402501c030500070b0b00c0c1c23500300641806c0004111170104a60102000b95513640d0304404100d400b001103040c0c00e19810302010500307407039101801040e0100040000500d00207103101c0c109103804d0480712400d500300140030344002c0e8080d9001c3d442e0040003000c001603001d5103820b012600c602c0140f60125085540354003198001e50b2102d14040c503010000b6102210700d4002d4400700309400c811108000b481810304050111491a01440d50018201c440020602c0070940541d90a56000007204120360038100c0c02812403032541c441100940103145681c4000040800c600341202c50241c040c1d40b030225520103100700603d00f403008441c04280b80800c1d5500e03203003c002e0300707006480f54400003519020002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 179404046 1250 179402796 179402803
    0x6011b020a06050a170417070503070606030809030d030509070501081e040501050a0e0a02090a0c0c0b0c030106110f06061003020c060f27030703030911040e011401060c0503120709050303030103050f 87
    0x110b1021030307545d16000740400600c285c102031500e007855030041e585802c000d00d03069096110780d0202504113800c1c1080130040c0042000101100681181100e12070107403200d0a409642085070321962070703000003a041101d940a040340b5540404e14500d1034a0300c410500c40e5000703141007900c00350780980d0359004004900c411403080b2400800030000606100800381e0019485100090000e92150b485e0f0720030740740701e0340101010042d2035848845980d81d86411041110b880e0000d120328000520852551100d012010400c26680b2407100c0180800d5030310b402c24010000401d40f1454200355013000b4208611209105403801041001603888181c241203603419108903040b282030712804a00040607590031300c000112821650325050100da03c0f0780c2802c1107450b0000d4941a10f801c5800c000480908120641c0076150b8100d070005902642e9807550403c4540c0382890f0401030040d031082015076040d810002d0300c81c1d840366543c500350b40708070748403c0800d0541d08203910441d01d540c480b1403080e50005061 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 179405296 1250 179404046 179404067
    0x201090f050604090c0203090310090506010f12120216030c030203062d040f0b01030b060915010c0308100503011e2906070f0506070e030606040b0906011b020a06050a 73
    0x610152801400d0030700184203881141304201c0e0145c0e07141e03552500c403030007481503c9050782c00a0a0300c441101c10540391000c6c1c8140c000c03c54060182600114115401440c900266109040441c070216415640c04c900401c130b04002d6402d500c02c040e814000240b801071948040c40c0300d41c21309004146140b051501d04640a4509183e20100b0409010320242414600000b032242c0c03516a40d40303440e2400d22009111204d240074244400c2c02d00007000b0301c103904140d41c0c0503800540c0c4800305c0341e1341c105e214240c1c08884800b441c00580b01074403080109204072040c1c0d4110018a441c0a15aa550400203084551100d000c515107601a00085556a80c6101d60710902e0303080710b000394400c0020341d801da0842141e80f4030107226034400f140d03d00074881d0888514503040e52240c12500181490b10018240d80800010140700b0f10071200003861a04050280703a43c10000030700441c4143d151907006503015204000681e013900c410488030005a034400d5014001060306807940c4d5528013601100519000303c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 179406546 1250 179405296 179405309
    0x150111030307022808070308090c0a050a180e01050907030312140f070c05060f100605070b0705030c071e0b010e13060f061a040e130c050d021c030c020109 68
    0x500402a00300c0d0082130041e203220100441d5811164074000000e660802c50001600006010480b002090340240e5901c0c05000700104a034960310005041204192503801442e13000b400b030840030005203010749243d1400c942c2c0000082920048020f0244c00c41c2d40031034010603241c0c44120704005140d00100c05559442680f5800c0c440c089003004145017248001e03103070381f213004071000005105e5445100d0904040380c5c082d0580c1d1480c01c10f0340507082d0100c803e8031845500b03d010b210000e15140100e08560340d260f0302840c0e0034242c2c0d0300c807041910940c200800c0074802d45000c000000004001d118001e403010140260b0500001031402c0c801e14600058218141c200c0c2a2011b01030110140781c038188000c1d074820408204003044610400180280f5440b07600b003440400c0c0341c45a441da0120251043c0c0350840f01d40740e001d9807041c0d030112801c2030000f03018240b14400302c0b042c450790406051509a07580040d11829040589440c3d601d58a41c3c1e59100350000780d550803c2c0e50456900c001903c004007417 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 179407796 1250 179406546 179406553
    0xc0f1306090b041d0402151204020a151407031106070309061107051e031e03010801051006050a030b012f0d02070605121008070e040b0109090309030b060d0209150111 73
    0x44c8070888030411408081500b4800e4600c00041c00c5645899080d441e1030742100340b00d0707103030320b005a4000f102d20b1090740c1c200d119880d110701c045090340c40140318084040c855a104000c41106c00c004c04816406801c046c1e04000c1060b1980c0b60702001000001c0c014141d6603000a5031351121f007071610490340149000ac1e500c44003041200003003000050845901e156040c03180700340e035030358052180c511700c10b10845901040e460241c1404400440010718100d40c1c20100030b00803940c0700c2c640c0c543c8180740303030080801044003405110342c854482e91001c0154017040c100100c000040840440000301d802510601c440091260718240c0c4c0014400401400c4071713800240740072801e0140c0038055014021071b02c1d034480440000079019400020300c1400404d41c65090300c0c01903840b8040c95204135070807a0241c4017402c00800000b07242c02240b10f1081d02c3d64050755032003080390440d80d900c1c41412014100e1075011000c9105c01c005030780c0c1e0702d840c2d40c0030b0f0745441c9440c3c3c1c1018881d0005000294118180811600f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 179409046 1250 179407796 179407799
    0xd05010b0708030412030e06070917060402090403050a120f020c150106050d1802060301170601120201051204030e0306150a0e06130b0102150a0902091810050c0f1306090b04 76
    0x84880043d00d41003948064000701c00f051081302240141040e56494100d03118940034005c3d0140c12aa13031703030140d49600109044850b01d4001141d0744a005a41c02500024040c0008010074031500151005028a02d003d864200316510404161a4454120b01e82a60b0000e00b100130f95408120b47c900e80407980064910940c90b15a020304180a45d507009030120361104902c9501003201a001d81d15568010126501c1e561502d00701c0342890a014a1280d40c3c2c4940c40011981001c0045e001c01c1969050b9a500d25201ca040c3d01004c1e405002741c4100c0600c40540410412540e042c840948282200d4502c0d0402d059007a04000342440d140d030100c44182203134420b02c480d82e15000c00000c12100460800b089084a1b000101e1800ca06110100344980c001400e000040300e40c0c1c0c208200c42ca00031a031100541c0c031070b03100b40f244122920b840c1c2195617200e411140d071012080d4011070760068501d4042d5040208002a90b00301d94805001e400c2c0745029200309022250304032008001411b00700010a0405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 179410296 1250 179409046 179409053
    0x1b0e10051215060307030f050102031f0f050d020a03060c0c0201080a0204061202250b09123606040f0e07050702030d12060902041202041103070c060e12040b0d05010b07 74
    0x40a0b14082e4068411500c000a811030310704003e03c500442c0d1118648013031030410704249000750030542d5000c1944c0b080490406060000620040236038601c900504451840c1908100c0310004d4460b0880e00080180c4001010801510170140240b51513102c2c00d10f40080c9200040000748004c00c0261840e10601081c030110350702100089402c0d546210060740d860300c3c502090380786284a140002000040d06000081188001001e8054160f207800c642c1c0c20401410707402480c2c061008081c26051859129959100181e4240d40d01030016040f09504810960041a451342c46070b08100301caa0030300c1d90b0400c410002c00b0743d110b43c021100d245c400e0900c403d035400203407185d18605d000020040310f03050346e00c16003078164003450061540301c0045507205e07555401c02451412a0340d0a91041d890840410200d030384031401c40b0b110309460707a100010a035066443c03400034038400e892030f005803241d01c6000554114540044c009000e4440010f034542072110301c0070081e25016001281044130a04c602c9000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 179411546 1250 179410296 179410303
    0x10603050708161b080c0d20010204050d060203041403220e090c0907021005041101020c01080c0f0f07150b030607020309010906031d01060905190608030d0203041b0e100512 76
    0x10100c044e04d000b0780380b0800741000e401a000c0d00c0540c1c00d841c020f0041404d0b1481c1c1014000d4204001c14554400b8a00c403595454200c1c0280c0c407801e078003e4510441e4200291282d0b004591061084d10b150041d441003c000506c0e680088043c5141c03d042096448142c00010541c00700070240d500e0500b5661602034103a50301c40c00b825569034061100c01000c111003500a11002e00c400da40082d041000c1e05e02420441c4c2840032000840c1d0144c02500d0b4801955442401d82c0c6200d040c4109207503252120b45100700145030b101c41c085100588045c05400000f6460310340d5150351203062080031444184080406080c180081e0a85040d54010000401141d0700401010f04451050400046001c5a8034049004e0f451300300b51035180303519111000c80d0500071503000302c2c01010900c0309030329a407040382c02c1d07001225503d00030740203a80e009001640c5089031580042d54002c0c824281c034203c04000410301042d025241d0811b041c89024001003192081d006604c03080100011621a022404040410303501d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 179412796 1250 179411546 179411567
    0xa060801090507052e090320011d120a0803090c010504030b0f04030912030f0212091305060303090a09060e070c0206160c2c010504090804151701060305070816 70
    0x1031051202024101e070020841d22100c000d0761446061802c2d84c40c200906c408800d0004698045a01101001221101c4401196840b060311088910b141d6056a40309054000c1000350f070041d40400d1a02c0200c00901c000c05c1d8162107032601c01c0c0c032810300c200141d08003c1c14407146410020240000c00c0401d8100e00760320380041d100000c000060302c03941021504c0f8860703a042038020800a80c1a2400c140c0d1108030698030188541c05c3c0c4a0703424a50008101500c1560000b80e8800030a0b04801e49160040d480250064401800c80b0b20305400c0002140003040154000940e00b951403404000703008404128580c46481860029920511640000c0301c81c007070580d2000040c030074100d0400421629180840203400b042480141002005600c00d904002418907501e805600600000301401c1a0241500031640f0075a020b05003405d203c041011504060707100000c01010300030f404402031001e400380340600401d9501048900e81181c000d090440040c2078080010035290303581070195448010000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 179414046 1250 179412796 179412799
    0x3120206090d0804060603080c0c100f140c070f15030c0f0c0b0601030e0327030a0c0e0703020904110a02010b0f0a0b07140d11240a0b010201020d050c030a06080109050705 75
    0x182c3c0d40c4903810514000c1000d0b41000b0030101000a40c4549030b0000540540940740031030780503680c40044c0b5001c4842e23300d021042c401296910b944a038016581c40003920394110b0030300440705034503a5640a0071810303000386c1c480c0381200f801182d4001c0e0141d050080105c14140ca0400f910591240720b401000702e00303404030260180e003200c0c0110750103030f100380c1080e501d12221404403600c0d00c3c52040800c2d40d030030942d594001041001b000400d1942800300700091002c1e000031076101d0403131070110300c00100e00c401050182007503400c0119402c0e55580d48102060255031001103508c41038040406070031501c0048100e07106490803400c00d03081e5912400f980c42914481e11200d40c40d00e6003464030880700c0da641ca00c03500b032500595108140c503030b41c850498a0306a500c40c0c102c0d08081040750040340780b0f030703074000300c2007480071011002801044541d0005080fa45062000524000803c640c02003200c1c020383d0744400c1d1000c0042031001900c0d1070300409002e4010b880c0200040748040c2d80d140d94a184030312615 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 179415296 1250 179414046 179414057
    0x14070507120309270c120c08090706020a050d0f140708070b2202010e01020115121a240d0b0708012c0114060708040e0a050c070f141e0703120206090d 66
    0x1c9140717a02c2a860120360945a0000380035008840da400f0346200c50859500c07003248039200001035594800540b0140054011028209444000ca4100c4221860108a00506c0042520004c4a440d58001054408d0045190940350b04c07807031501901490001d020099001d040e100d4141a042c801c241d440f84243d0309080c260012581e01c030040c0c0c05801651001d48050035040c0000403010341580108500e28401c0d18400c0305034100f20032142040c80309880c003442d011617070102000020941030010452142c020981084e501c119038401421704400c417114000246400010031000740d500d4192400d26021001034611056030300243c5090f800140700310b4040003500c1e400c5241d682c507440c6c01c88513000d401c599080d60b9161074021000d00c07007009032031000340701d4508000100d08101050588027410380c00280e50420b032500b03881e415040408140804154020046c1c03201c2000c00e9410011100b400746005452160f1450615041c0700115a14030003e54008204008104502060070119002d070380c02c20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 179416546 1250 179415296 179415311
    0x80c04050a051618080a050102090f0114030117010b120102130b0301060c0b0a020c0102070c210218150a12020a0504141803090603100e0a1406011407050712030927 72
    0x10340c2c4041740d221130701d0b50180880d9481840019001010950415140b0602c038a10000044036004c4a800c3c2e03c2007118800e20051010344a400c00c40100d0307104200010420722114800250144e11502c411a030a030360008001c011066800103c0c001020061285070842d8580200603282031007a04005066443d0080001c0c110110b07541500d280c505014000c64580005151500c0d045881d8050500032031241039040034282c54164041162a50152a0581c960903a4003601c214680181c041c002d008611068206c86d900e410040d10010805007000c000e0100312401401854025608518003031420204d007201d00070616005107030807060170540c40c421070006274442c5086001341111254020701c00414048e240b10044180c0d801c0d240d14018440301522000c1000d0200c9500c184500000c000e0000010a19800f420040104401d4210218039154440d5503071030500c0e18540005403044100201d89040c59849000e400141c4008a070034203c259092003907042d0400f0704108120f400340c99681 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 179417796 1250 179416546 179416577
    0x90604021e1303030809071a0706021b03030a06051c02010c03090e010306020a1e02060f060d06090b070314090c060a0302041e030302210904020706060b04080c04050a0516 75
    0x15403040030301c2860794151500808880b400c05042c1c180b005a001800e80780105442c094046160301c01c0358001900c80b2481c0d0410300385021141c000302000da440950070303c07103280c003502e40c0c01415580000311030145d680c0b8a882c1d5204030440b0115008a400703501ca50f4070031504130201540100d401d603024240b00c11001131614048a0881840d00160401c022500c0000100b0600c0e4003d040c5e403d070952622401c070614104401d0402040303040040044e030001c00807512160f002c00d54541c10490140c482c45402c4040d032156800e840307040c1d50407a038030180142004203ea42c10322880c41191005040b0b40c1c0c0504010000c40c0d82ca40380c81c0b121070721600d80000c07100c480b907000ea0704072001402d021040c0102e01c04641c01140850800f0320065016005103d0b0948200c29401c00c840031989008035880e0802c1841028440207401c01d803011501e242c0e0b1068040344c00c4045901420007419450010282504e410060000390346000d482d5203182414402030045a4001a009200340c0c003080c50b0040c40c85040d00c3c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 179419046 1250 179417796 179417827
    0x102240f0919060f05010e091f0609021602031504020307060509040b130c02210d0e0109140307031403010b03010506090a03020a0609080f03040506031f0e07090302130b09060402 78
    0x20310450301442c20400820400600740c0040721400e9405800308030a0b84e848007040d40740041200c01401a40000c070382c5000520350255030506041000c9000145152145520401c0b1b0388854003c2443c1481e0542160071441c042003407011a649065150300309050981c007283e80d51405010b00c1d0140b0a000c03a9600b5240c6465101c2040444000c0104c01011941d07c1d09000500303003500c0150050040d1400c0014185140142091111605d03000624111003050800c0080180c07500b8200c0b076540300c00d202c0c8003280c201060200d03040d0b548009541d07258003d240181c00b8040400125848540c01e000410a024900003600d04503107017074030b0050703031008408002100455183c000035400030180c42d0206e070155000001c3c00c16200c0800845001c0d1500386509a036034040c600c1000c1d030100d01003000403087c08802c040c2c500c00200d5490407401c415100c2440346e00911741228400001080c9030420000c0d4942110000d00c482001d280412941c2440c80206004020040a0b0346c0a05d80000c0c002254900300c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 179420296 1250 179419046 179419063
    0x60f0304060b0d12030f0902010f140c03040b040e07030b010e0105070f02041118120c150708120a060501081501140702120312061c120e030303150102240f09 69
    0x401d0008281c103c0d00d02440c0664043e80303070354000b07403030442202c880c1090342c0b141240003030301610350441c4002412001c80d1043c24400305881100410700c88030f070400c84208050800362a00d40c1103176448604020114004080c02014002014104100307031140340d0300154100e01128080c81e00039600c3c505403c080d04411070480303009400c6458003103500032030b1003000302800c905400341e480c101443c1d00c2c0e0000c2140710207504140c0f8240350400708003d0741d03518000d045084c038243c6201c00c0905000503a100d68041c1d4000c0003100003100e07048810490a4030203441080c0c007800342420141c11504255210f0a12420015003c0d0f05016510201140500c440710035203013855030050000105070040720119032650420108042d0003540340d004a0303400d02e0503000b0b1503c40c0743e80d103e003044060326640751042c80ea050905a41d09200d01c18842d00031310745061008503c0b1716034a00011083e462400c000a2506000380349204170b000c038400201042c40751404c80b0341c0d0410306045041240d9141c0160003400d09451 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 179421546 1250 179420296 179420299
    0x903150612050706030b010504030515091207140c0a0602030a0f0203090307030602040317030613020a180b09030d03021312020f0904031e08070e040f090b090a05100605060f0304060b 80
    0x1e070001901000800110308081d11074503a0240149800702c401943d103402039001c000d201c0c0c0c01900300481c00302005561258803800910840b0403041454000c002254409901a51034007540908103142c890100710b0707021014410344050b0482882c00000a4603405035811060030002c0320084c2c125280d108100780e50301204003c007511902d0f5940d1800b040294400d2200f124001c2041340450444006001524070030003014240c07903403448100703030501c000303501800011081c007036000e240c2c981d8840d0700c45140010340400943c19a07035030700a4040602e000c2a018411081600401008040d500228170110842e564074115003c00c8203d4800201050505840c0c65000a200c1e01048240755102c100b568202c5800c1c010807030b0000d42d02d48200d4624070110b6020010a2180c1c00d004141d0900340d0081c0c408502e151000a01030004c5d55808240700820740381065568071800c900c006211003403200d5412900d4102c4100140e40c6007801064641c05001284214403001000180602840d500044d521010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 179422796 1250 179421546 179421569
    0x30f2410030b0306221502070b07030f1503021c0201090b030c0a1103031003171309020c0c0306060a050103050711240a0c0914060c0a05030304020306070c0309031506 73
    0x8044001402000102c0d0032038442d00c25400481d94842405080b41164001a4440d0034030820a4646141c0c01115100c2101519401c00c40c8202103103141603540d00642d601da8004c1400001001004143e681d0392441c070383d2240e1403217000c00042c1c0c4c80300e0b50a409030b046c40b420024031100c1800103032110205548402602a00002044030641c2844d0050103010076030703140d40d00d0101c0350305041560387c00300312142c05441d401000c1c14400700b0a0b40c0c444000c01c2950f124190b10300a60740ba005140100c103980000501074010800c040002c1041c011003840200507070082155151140c0099400342952003020f050541c0d60022a48451103920b0080d035005c0000c049840c1181142404420811012100c1e0710030205200860340c444018007601d03100b24035565822110f40e04054844081c502e030302500700e600450420034050498410701445003058080e5000e0f589a00c0c0900606040910081404080001074044000001d800611903401e0700e03042404417a2902c115007480e0002c15054025080444 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 179424046 1250 179422796 179422819
    0xf06070c030f050f030304110105070606050d050a0b0a0e0a02040b01051605061f06121104180615020109020904060e0a02091801060621020706180c0f0b030f24 70
    0x52025440b448584210100d44501d1445002180c0300e000903140240308500310210700030158425409045800c1c010754000403443c0e510340c0054038000d2084011221900611011414031142000440c3d0001c00503400703100491030301c090340c1e464120040300207105035500c0d0404c1040303074465000c1c0c40522641048901001c42230f0704000c0e82e0b0303200440781d0041d00f030403030f16080c8100500354070381900321030651300c1c1c2e40c660b040e08441c020054403540600201c030103810b01000030200d403500c01d882d243c4030ba085c3c0006850790a0140015000340c1e2071614000790383c1003964940c01070300c0314080941e10030b403c020000f600394581c4503c103082441816002c1d502800f0b42082c84a00c15001000850f06801b004c02088101d03540e10040e192000003109480c03011080c1e003c061440b04640d002002d0040c45000c8c0024000c20700c2551810030f4150f480182c0d81c910841e40203005c00301003c0401d002800e25001c04038258a08000e03d8880d83c2c200418241c11048034400d0703410701d140940c40700195800000d10b10070344003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 179425296 1250 179424046 179424053
    0xd080d061d0c1e03090a120e030f0304080706120204090204030308190b010203041206060b03090102130603050c030a0903020309040e010b0a0609030803070e1903050c010e1c020f06070c03 82
    0xc1d941035103180d2071040e484000c80c00c5009614200c418a41110b00c65800405150008010130741009101d82c100780075a4004a000070300c42c440c0c0301c51440807503c0c0d2072500700090b0141490004800030111144d8020802030002c09000200c000c21600d20b850b0442c08001b0010b0584081c0c092903000303050290000c00c01200301a0010412032003510a00c074290f40f1000e0014100058428080285015800400041c040c020360154281410340c040c13200482c90590760440700761698811900c0010507580441c02d804a514807071410030045c81d4901c1c091049040205000100d0b1101504000c0d80e40c2e5500d032050b08040c000d005031454050020000c01c07210761115183d40c046e164001165118015401c00030034450300520010341965007143c946419980c170a0000e64030004800c00b03181e8000c408141112180020204910245205070094034610524800144c4007045041805200380c0e800011040c1001564444000700b80c4c0485600306850001030200d00030380301e15000501111464000032061 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 179426546 1250 179425296 179425319
    0x60a09020d061d13031413030506010305011d0c041805030d0603060b03011a0d05191209050604050d020103112101050310020a09090b0a0b04061e02030c0a020d080d06 73
    0x200c40b44554404030f62122804100c000c49000c50b40d405082d43e9044135800824800c1c0380e040a1240c44030b1000d45071800c0701c2044c04042e6410790088413194000c40c018420850300f8091500d03a403040c4c4220040b048508007a0a48924082d08201c1c0581d5841000c000000b0820b010541115003010690355103e4221030340001030115800180c1d070580c188011808cc03801c0511481103c05000d20050380c0e805600300c2082260064400c01382c038148500b41c40316480e0542e1440a10501d8811504600d980c0d82c2d10b0009001040c03a98010380c820b600901040000d9140c03101d541c00310650900e40014560180440e0030594080c81070110356009814000e0ba0b1551034010444d0f044c1c1c1c104604883d1408079a280031000c6e440350503500400128101005c1010b074016400607824124000c0040041944038580072a0b0381c0c01540c82040040ca4800c042754013107400918411000b135081c40038502d48080c403110156540b40c5200c00a019401da0078120050200309400e0f0b5082c0030310414180300060b641c00c0700da800c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 179427796 1250 179426546 179426549
    0x30f022d03120405220e030c1b01091401080901060b030c0c01060e01030809060307090b0d050a1416120b0604060306081005040b01030b06010c1a15061e03060a09020d06 74
    0xd106500c25582541c40140544040b13400090510161210208845000301524200107801036250904055000b40c00c1c0082c02d07803502410020120311900b004ca01d154400b85200301414400009014050b072240740c03d904e00c0010007801d10342440c0c0c0b0f99403800c43c01003200b0361010314445008028800342205410007403000103004d070300a200e03040d1034444020b4503181c01c0c440102041d00401203003026040c60009140d00c070ae02030905480b01075403150706568903801040450580b55a4008105000d41b0610400e88010744019a6804514007070640e4030000e140c2c0800345041c001c41c0d111118202d00545c02148500d8401342c0340e242c031940c0e00c01010300a801240104626400307502c1c0c180005652503c20580b041d030b04004100c06507465503d0700c24104801402e030f02d041001e5901188042401600802040d94005502ca00d1504d03018042d405100807034181302d44542c008119842100400345250f89801c1d0103111b007195280c0755040000d4124880360f003c18021030000c5181c11031005240e21420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 179429046 1250 179427796 179427799
    0x130b090301110c0c0d1a0f060909030703020c090a180f1419030302160b0f0f0105040c0207050f06070b0702030c0615010f0f030e030403140d03090309030f022d 70
    0x41100c00706641c00490142e950342c00280d40c4801d034401245c2c035000640354403c5001d82c1107001c402100011008a11004550090400d02030506000342420b040f182c05500960b820061414140580e800030740301c06400fa040c0e0304c5900c044000c01e0440c00c0070350046004448031181e40445d50680c1c03a100b051043e10f0841a0f03424000c0c02d0707a1300382c24440410020f011101c203d000150715940c907913041c0c0080d080075400031b55001c02040e100c40000c0520076224000c441c68120b42d1054906403c58007640300b0160416400b4600340301010400701e400090300c505548040302c0c0c80c140c08500b54042903440c05001030240200c001c40c001d1002c010b4000c00140100343c8008242c981a50301d035001e02c06000d105202050001c3c030080c0c00a070109200b542e4000d82c40078140380200318412003820861558005400603a520902040030303070941e400801103034000170b03524141406030301090344002e403401e9100e2001505076228400303c041156a9001070555900c030300354082c100c04100b020604908410050110b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 179430296 1250 179429046 179429051
    0x1204050309030312150102160e0403020c1507050c03010618231806130308041b03060204140f0a03020303092209060b0f120c0105070302100c0503060a0909150e03130b090301 76
    0x145075403020450b5800c0c440042c1c0c52588d258580a0f030b040740320000403c20780460013a22100700d250f9a038490411680780301c0c161b081341c881466051440c00d04580038030440c46607140a100300031402201d080395004040e504000200721a240800c460002520650901020b01c503404000030748108100f100d000343d64440403240700d40e50381c051103407481e43ca4a60260105c0e048000003070018080c05c0750900c901c002910310540d10b9a40396119030582e001600301e01212006242d41161900341812200f000340400c07200c1810007480c3da00420f48038854040d0341030041c40101c0c1555620048500d4900d1070504083e8204412941c90405130001d00c00c1c104060300c03601140e60002c000745081c01041034205010405001003032580c00040d03481c1d9222490450079402244144080ca102a1003080800e880d00e440e502c1c0d4909d000010440d000009410079031071a03103040d40000103e40041a1070000322400070001400381c103840c0e440c501d14041c2030b40e03070b504d8442c6c00c1d2008035080010fa4054404400c046c0c00a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 179431546 1250 179430296 179430331
    0x60306150c0305032202090106020d141e030606070b09010c030c02060402010816180305030d1107080a0507080403021e09060a0302031f140a0e0c060a051204050309030312 75
    0x4941124541c80702500207442803022420001180e0b004041c84441e100e03001c0140591580814100340c001da0290001d6040300d02044805900040003089023004501a40c1c900100c8015500301520143c0401100d50004000215a07403191411120800d0b008611304400d4941214982d018080304864040003030b00780300c2003400700c0d0f00004503940034940c140c40f0105107955034140119483c00e007140c840100200c02c8082015881d982006902550040e000345590f500c01302140e406651950590a0807440f003000640003141500040d00c400c0034480c600196910698184a4120f001e81c3d08080c5d030007203010035200380510002d01440c100450540d01e0403aa42c1c1e500081000c4241103100194041c0c00c1890101d00d000481c8a58090080b002040010706d006081a101d421502c1125141402c95480e0002c21131180100583d401c1c1c0e2504450f2949002c0c2800f0b40180030380103040f00c10b03441c400c0240200302041400d0060b0341020380e01070120307a00c980b9400040307000040305590404c801c4e6040b40b071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 179432796 1250 179431546 179431589
    0x90a0c0e0402180409081c05100f080a06020903210309010f0e0304060e040207060c02150603030403080f03070c080a0302041409060a030b151e1f020606040f09050106060306 76
    0x2660f445008030020100f1030a0458203200103050500710898220310100080c0500c40e004100410940e1190400050345103041c2d60720f040e2004158000c034560780794400c0100003c40d4005080311103554000405030301d0309403600c013091800450140740070310040200d0301004220340f0710002e50302c5400a400240010078583c00300c40221601038000300060f400800c03040c000380d40070f070209401030711000e03200601c0c001c02d40d192407080b5255010348000580111181c025080c01080910390000780480107546061300e1581d03101c900340714505882042c04408400903e949005d41c2d0b41115098118849a64940310b403400200254400d01a081d8000380240c6035403c18107040c02190300c12000070b801c0001050540c1c03600e800d4004014100700b04030001490741201c50300d503440031180b5007031694412280784400008011f00340340d00505c030500101072030f8011682039a0000d0340c1d58116409480004020000051040c09000c0d602c6000c6d11560070004000788081e455880001210300217001010788884445 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 179434046 1250 179432796 179432801
    0x2a010f020304150e04020d09020a060305060904110d060615091e032a032004020a0903030806040f020f0a0e0303040305030d05181005060102010605030a03081b09090a0c0e04 76
    0x2002900140e1060009000701c0301108004900c800160a0aa0300c040d40303440042e040c0d0388041e40c1001103c0d26441240c0031420300c907058001410305402c0500103450034501142950400610180c0314841d4000200c8440d1104000c0c00041500710350306019682d02e90720801300781c0d1071039401d03800015504080094180d030703003800d031000e101008031480200c3d518584921842c004400b180003111f8203004030103111b80e84e10100440040d441542c090752140c0c1c2604003001c03041c410b0301032036000300e0041000c07020055229183c4000d41e541400c0c91a02d54480401180c01032007481004030359280b00003200c1e6032141210029022200041d070700c18404e42150004d0545900640c48020204c2d442400845045800c85c0c1090f644801201da010360254a00080107203800c1c1410a0300640680c0c40c3c2c2807001c296820301817040036043c260014900c10a056800400c407000c020074943c403079003138003041c504400303142c20840e0450302c0000c084440d9810140d4088000701200c030380d407001140c50045543d01c642000e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 179435296 1250 179434046 179434067
    0x402091e010b0c0102040f060315091802010f0e0a030b06030f0d09120303020d0903030b0406080c01090915030c06020715020106050603070c0507052701050a150f112a01 74
    0x300405403592a00703141803003641100f680400c09540034480881d13468007952240c0024400da90703010882c1e03901581051403040ba0f60b002451030a052006084503200c142010b05140e03542840c2c084101400c0b80401c98400003003411040c1d0180c2c80003400014424030a81c0107000340c200703c05a8030b0301889501200e030384101d4055244082200024100069036131100e4204040d40a07003405450700d166200c80310700716554060102c001c42c0e0346010701d00d9181450b21840f07001e4500f40000308111940000003030405507040c407a5040c04c40d20786810141c40c481004500008561109052051544402001c8d4456030315004180007840740c000e01119003441409410304880010b041145142c031200422103c280c841082500c951240c480d000a142e1581e101a403243c1b404007071040030440a400504100c9281030340900e200c0d2010500602c03240c10040210b0106100c0780c10041500701e40e00d5401d80e16081030b160764502c0303400b41217814024401260100d4041d200c204064203c00d0481c0ba00556000070302 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 179436546 1250 179435296 179435341
    0x803090d0f03020a060501030c0608090a020622050d2102030711010f210501180e0312041b03030f080601020a2612010801090309050d0f02060f070812040209 69
    0x20100c96008640c010510800403402403042e10700b071455030380303e84003565020ba01c1107681e440c044a00b004440c0c0d11407000382d0496065009044440c1c002d400080e400e00545103140c00341c02c03501c075842820750680c84a81e8001c1c030029000b180d00d070f0b019041c503190201c07144000d05040e2910004121005202200721031950390b00010b410341d020302c140c2c01133806050300c1d2004011b000000403818400050703007081056810805002041c17540c1805215404502e400e40c05c00351341c80c1403d140341080e140c00f01c02d8a194000011104c0c805580d54141030b00508e030510406000000029008410b0603449409400100b4103519500501d0f00c49200490f500c1c50030f0303100900410900000c44800da22a5075000d5690414400c00c80d08154900150000360fa03000c1c0e101c860f160703541d54010410960800c8600c0010882103e14030441c15241d201c50f1a110300403040207104880000c0c3c403c0761115080d00366200071ba00070070315503121401807501e24242c01d42502c0992046054900260100c0c00010380380e220910f1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 179437796 1250 179436546 179436559
    0x1e1703091009080706020c0a050d020102071a09011e020909130f030804020a1e050301060e011208090a030b07030f060801020a0f0c0203010e06040b07030e0c010c0219230109080309 79
    0x30300e8400400034071482c4011141c00604115a8001c1007140c005044481b050350054541d1401b5854110304e031249240100087d0f90045c420540410350315681c030410001d00000c0b801180d580d0800c00e5004015101a01c030050025000700711400103a0fa024114a04042e02c3c102195150840030600550016200034921412407040c080041d208001c4ea640140c4060034017105143c84484000e05441c085001c0080c403501b0f040c007008a0320b401d02642000300010049035495506022500c1c2c40b18101c10360107003c0400020300d1401545441000b00c0045810009400702c070309281c480100a0404412010842070400c540803652000610131211034046940700d41d81c400303014a13016100e42e00b25031004d99065583c0e06c00201103030030034030503648514401e202841c2c1500c3c0c140805422a50402200072182e0b02900340c104041c0d80080910801c290100c5c2c00f844044411610104c0107100d940142030648801da0320009440000000d48810311026280d0305101354031004485d51b280100b910340360b4400c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 179439046 1250 179437796 179437813
    0xe0603011b0c0309050604120219030c030b041401142e051e03010207050105090d08010506120a020d1e1a0901050418060e100b03030c1c03091e170309 66
    0x380500c8500411a210741444d9807416503d00006000341c1250340300d200342040040710802145070044450406483e002c0c42e80c0c8240341140c41308110380040e400010003020040021500703000f12040304082e4900010000d02a400303882400307401c0c0d80700c01e03100946200e484038406100c55811140030301404201c0131a0408080c5040d00700321481689174500301c1039106040c54110661001e00040c01894014030000c11503040c100c18291900048003046001c04c4041030040c8110340d01d9030215090390780c008850704186e40f5050000740007803180c408108055880c190048064120b116008004026110020816040100e040540401100b041980e200d07d00b040144031528144c0d000304010404091a03048106240c2e41d424100c1d03018001c0801c00e54880c0c1c3c082d0116400074028807003624000e4000c2c0d405d144a00c0c00302030303031441106506001520a01140300e4100c0c40f9a120010442d00701d001c0480028032442c041c03185d880000e0f419130344050501803080000070500c0442e40201810f800030120315 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 179440296 1250 179439046 179439101
    0x4020901050d1a010806060304030c080d1b2007050d230d0504090c0504081005090c1005040e0f01300b01090515120c04150e0c03010e060301 62
    0x258010060181408000d01c9a00c02a206921448002d600900c0c001c07000310b9803820002d0942c3c2c000400c2248289070400c100310029510031000c000f00d56000352500d84903503500042002800780f43d8601d10320300703e040340c01c1400c5643c000d106107010b0030290310411907149020701070340e22403501e801440c0d04603680c2d0b2010000101e00f0b180c0400e13502205118100c0f1644540c801c0e0f410540c904824a000400104092180900b644100f02c406800750510301d28140c0303409415600c0c0c55254032030048072a0344800090007000c0500004808400042464811044100d405499034006014404071700d000c11002600c03184440e0340043c10b07600c1400f441180c0e081c0201d041c6c01c0000c40c40070103040400c42c1152440004032410080d6000c0c0511220218641c60000024180300e039035600c2d45032080f06c1540341d414030400080384036009088291008290400341b80c6002c40b060085a0180300454038000402000d042050081c5045e140b510703125101d10389030101014240c1d42c082e00d0030481280c0042040610 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 179441546 1250 179440296 179440301
    0x31a070320091302091e0d170406090501050406081512030a11070801060506190923010809010504150905011b0309051c120f1b03050105040c030203040503042603030a090c0603021804 80
    0x1007860050042212000300d980d08c10b4030315460780c1e5000c01800089000e12829030402e1801c4003808080c03810302d0600d0b1514100802150014200c1c860b4100002c000c81040c0d1540507032414074114031001c980c1c3d69002c40c80700038000201d07804080c03824010503078007040d982018000c100844600030300e001d04103204c0c3c5101c42403081c103902202007807000c140b40001e100003103070101107504c004603004804040f440400140642c41c00070010700d866454401048006140041c0c441d200c00601e460001d15085680b810b24010210028102c88445010615840841e070540105a04a20070400d44180d03202c0031220071440300d54002c805000c200c0091300c030544191154402012031810000109502c002e00701d801400c941240104030000f81c4a000501c060f060a000d100c1c0d41c440e180c42c2c11840c611342a294261640518042c2c00e04440b264902e8408d009000010309a01d804143c003582d60340e007002428080103141c6c0e08000c0712002c60580c000a80c071070292090343c2181050220300c0d100303100701d5000c0200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 179442796 1250 179441546 179441599
    0x803010e060315040b01150e01020a03051b01020d0603050c10050703080423160807080a0f0501060b030f040302010b09130f0c12050c0a050a031a07032009130209 71
    0x4052045404451619140305909405035008404851701541010000d034003081c00350b040c240c00d1104201102a9599001a512920340d070185030182d00e40f01c401c21410050380f42003031001c2d1958000b254540d01558260322a1003181d01c00d40449449a05000600034105018403050002c01c0040c049403000c20300400900e0f034400d10541446c4903480201111172100280c2c89103040381a8007001103e500c070890400100c0180c4207890090203d5441d00603a107988034480400100303442c2c00c03003500c402001800d40204010b41036150303c503038130703841c0003000740840f050201d03000c0d0019820004249040d0900b910014020042014460490b0005031150105140b0325002100c40d003508044c0000c6010305002d10284441c4664040e2650701003040401c01f0490f5150403003807041d01042400c000180306400c0c540c0c0d8403246503150989507500d6003c10f400a0441c050b840c070801d0b20002800d05118406002015460003c942070481c131803207045003408030b0144803020368001590403d484207500440300c00c7c0c2c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 179444046 1250 179442796 179442799
    0xd021003090c03080d0203100f1401030207080f0a02030d180c0e15060a020a030905030c06030f0a0b030a06020903210a0c0f06060602060f0a0903021b1c050d090504090803010e06 78
    0xc003090f40ca07580d0300300e1030b070024065903056a1302209000e250a1203030200320041c03004440c1e105420b41403001101d030600741217003070b00e06140d40024004100000c640a0342c140c5489118010f803100280d041c0603440b94400010000214074100241c0c003890340c0201000001500248400c4426080c64200c2c2080300010b042e400e00b40301007485031388d03855590340c0040196001542c00b80040703400524002d840c000203600007504c03903004440d0303520045d110300303040d240e0000110044075625191008094014200411402c1c2c060040e07501003400d100c4281c004082e016415400c540c1d903180d43c643c1600000c110928a08001e001c104000524188902c88660400340a030b04000d0030794120f5605e50f01100c010f130307200741d016030010420080360490010383c09a003c0384090082c0000d50b041e69000b03484400d4040c076170060104484100b01d81d0344811500ca4294020707045c240b5210185c03030425550fa50801d517003140000d0b0a2001c0801d4a041034040c00c08001d6011403568111303400c0c000780c48080e000041125 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 179445296 1250 179444046 179444063
    0xf0b150a11011a060f09280614160f08040815060d0215090a050414010303030e03070c0e07050c0f060105030d05090603040204020f0c2a04020a170718060e0f0d02100309 74
    0x400980d41d4200c00c1c0c0101d1642d0605400a81301c0d1100510311030b91036540720405109c464130400541104060446050641040547c286400c051901c0704c451000418040c20302070f4045404206043d00141d03070203843d5000441c1c0d075000d541d8201000f800785054103009407c090ba1000004920f5851070150910800007881c4800b030680311008036040700d8410000040c060075000041052541600c00c0110341c083c90001f840c504055030725626012007851050030500d100c03510005400c0c52050301501c1c0740c1405030081e0791012030008000c2d90707144d101380113551090058551417110240218119080e100c4042d100c1401c659454007003000940000e40c440e41080030800c941e0035002814800b00c106203d2081000c0118049046441c24110b1440c003a10b004a204010ba8980b01d5000015a18110303640d0010380545d42c6c40007003c6980c60615250f034030035401b544d40301141890304801c07118100b203c10303110145c1000111007084524139040d80040d4002652a02180c0d506209410108405000310541c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 179446546 1250 179445296 179445307
    0x61a0406030f02220e0a0b132406090207030c3513050303040314070603060e01180b040203090d0210110301060c0302010e0a0f060f060303120f0b150a11011a060f 71
    0x131303142541c030030070708070025a0001c1420000b0024481149908452113980d41c0c41b2091490b03030f49110001c3d000c0c000811800b41080c5036809428940c203d8805821103180c01e5403610aa850050721402c60321404545201c0c0c2e04071004d020502010348140d9440780c22140b60341101305000e87c040140d00c00341a6003840c401c0d0101c0460369440420040c80114440c684c44124a44004403150501039550810804c0500b0040100805010925200e055880050490f040001840303181c4d401410503e6035150042d00200400154460224008815120640039607035240d800b254100103c275811400201040410b200601c11f007841000c507100c40e203100b800002200d44014094a20304008100d04880580c0400030a07400c101320b500942c03180f8680110240314645c00c60782d01174641f0070800d0f4581883ca80d41d0540300c503070186681000140760320151400640800102d4940d1159110255071404102116a5999081014071995803115100e4040341e94494840f000c002003903210030b106e4100d03250705206 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 179447796 1250 179446546 179446609
    0x10e1b04060e071e0201020c0c010e0d240f2a0207080601080c151c0c0c0b0109090b0f01063c11010612050a02060f0403050a061a0406030f02 62
    0x700b02e402501c0d50b440c3d9900c1c212503501040c5942155102003021640140b14140c4003520010320980e0100090a00c1d0721106100c0004c12403262003424040d00e0300032540c040d50f0250002000307002d03040d65071070b80511800c01096402d4095614413882140c5020360b00c0441d02404054801d6107805110a20545802c56501d6100f145048030a030040405900100c10000c1c051602c0ac203a0f411101e1000d5465082180b06031100051840c465488545161594070352b250351423241103004407241c0d010390ba0400300c0d6101c21180d001002601e004680b000070100100701074440180c0168103c9031945c2d80c070700c01c400141c08051081d44a05100110a04003020b44043c0419a607201c1c1c3c0f41c080e203c1e42c0d2200340f20084804a4291003055010130321400071035202401107440440c075100e09130380583e19184d6481d03a4010030f1070395108580c400307401d502610034a034040120b01d4001400740e02c080354840040015a00401c404c459691000038240012403040c1c0005003440c50207411441c1c0d181c04581c03c425940c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 179449046 1250 179447796 179447819
    0x12030c1305060f0c1b030d0f0302160503030103120507050d03110f0409050f010b040b0a050702030c0a0f060809120d05070c0b090f011a150d0609020403061d010e1b0406 74
    0x151000b83d103210101c2c032840540710030002c1d81d074403519210100b488001030b42c4c00301c0d40320f07a01c5000150403c11102a07103a0074a0294040f5460100c21928542825510381800da80b681c001303000c00c588450381541c1c0084017034072034010b443e4100e8204d0068080700550820540003803407001814001001c060203100071054010014100900540e84040b50b18036142d20090000d0300141c101c1e00d810b080600007848074420010607900e282655043c40fa076115078900009241c115a03400341a031200d01c0031004510b240001c0300c013004442e51510b500002d501c510740710907290801c0c4020303a00c03100014080c0150b1100103404c5240c100c0f201c0c4c180b03503084600d01e4036a000003642c2100c0741d0304a98820001d124803040c091041544596820040c00143d10a5200040d1103500c0d81c26401c840000c003007004d89803650b065202c08002d09410004660319a07581c030b0b100c1c018059035960b588208441078941240024113000d071441c000d4005000e012020300e00c40414050b14030140c0d0564215a94001c0400c0340c44188 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 179450296 1250 179449046 179449057
    0x1824090e040b0411010f020318030c130b12150a0c0c120e010e041506050c030c030310050f0402070c18020412050c0307061b02060a030b0409060b0f0312030c130506 72
    0x542d4102075901e401d08050b1601c1d43e2040b1002e04001540b28004801035011040e26130301400e0110200700039004d10002807501c0d8080d444254446c800b40714856243d0840c1d4010301d9980000e5654064008000900b280c9070181000201e440410f2200010000b0307409900040303141000d418a15200607054448500b0440081c0c5d649d07011a020f504020869030304100b1141c07824908840500c110b00c102100000e0101c82c034803810040c4003012411440c04901030054900044400045944928201c2032103012a100c6214003030051541c40c1d99004142428001ca45440d038101c0550101546807800980141141f0032190884c8c560910021800d2046d0a44200c5214007510081c4134410680c170805007010b4141c0d010606100800d0340700c41094000c030440742d0000780c04856080d00d0740704005040e000b41c840107078004d90282c68a4050070070001e903036001340c40b803540c20f8030000d01c8282c1c0c2000b80350342e41c89414949103d084041c000200b030f01c01003c0040800242900701c10641a5941c2d020508903040b2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 179451546 1250 179450296 179450303
    0x1b041d0114100503030d0903030b03150106090b0c0312060112141509010302010c0609020102031608121f14131415091303030203060406050307090c1824090e04 70
    0x5460011080c0520088078503003240300c255100d4041c5281900180da40d04c200c80c1100e90b070750b4071041003009060003540601c0007548094207580204001c01d500d520242024068070001c03404001c008141130700001e003075038500c0104200540c5806e005e080c007002203907801010301c0e041141d035011880451401d4018008201c01301480c0e0340b180d003031020288150704111a0070a0040c0c03d844010001360ba440410301504540204002a9050541c00101c0c20351003082e18880d01c21072080444410010342c9001058862006203100c3c8076601c40c1c5a151454601c22910064011403040d020b010070441410560828140144400e1030320800100301d0082d100303000a501d07642c800b07007820050448108280440301450480303211120b450b000300301014025060001404050f400300005000d5117540d841a0040d10340101150312056035038019401500544610700300051000d03a07034014014521420303200b0381d0049113100d02d10a02440b5400e01b000052968201000a442c000043d540406c56401340500d01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 179452796 1250 179451546 179451551
    0x504020a26071d1e01030213020c060c09120a020f150d050c0c0717030a030e0129040b0306150103090512030903042c010509060402040b0c030406030b0d051b041d01 72
    0x70100041d000f00c000082134160340300120200808401060507181e0f0541e98120748000c441007045059600034002c0049265585c85107405010340c159208001d00900d8404841203440140d8200c5401c2d1034043d4024029000442c1c143c01c0c80b06407501d003529410200c003801ca160b00749603c4248040907134505507a0a24000300000709080d010b001840100b000e811452842141c1c400b030154aa03941348603000042c0c003010b0342e482c000c004420081d00940c6544500c00c050603a040c150220006078103c0c50781340c41d84580d10303204a002c0d8030b041c0819414402c070404002803818046490043d0301400c3d603000d0442c1e09000b0000300b40920b18001000d14040c4107620019601c0303905040d811148290905003600d01c1401810350b000250306400e5289054035000c0c0c0f14041203855500100c1d01a02803900680801480400e8a8800c01800806401200d00503a01800401d4400c414048002c405d404007406a40040e80d00328203400b15000c007481c42e100c0140002419034000c40101c200c00d806d81044c50b02c140d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 179454046 1250 179452796 179452829
    0x71a0403020c031c08040f050105090606010815010203070b0405210406031a030307020f01020304090c17180a060506010c0807081e13060c1104140a050a0504020a2607 73
    0x60341008002c102e1501580100700f8a01041040c02d500c1c41450400401c00a02d880040d0400c60b880e540c1c1d2400590141c000d10a904191069540707600d4220345040c00103c003000060719007070905405c800b040038180c006d11f28025a5444109032808020400d4031030303210b41d15592406407564440030401c011005003040c0c49508084004041d03c003a8030b03ca00c039030080d6011061807903801000711400a40e040b22507007080f501c8140141e0a500986c9d006a040c1403810400110707258024445c40003001000e001004a55903800b415007104a00624112580e40440c1180780021501c2d800b05400c801e050402c0f81d01c00c0e0540c0d0f40e0044552001008031042c076008a090300301c402000c00d0f02c02609036410240c50400356401101d2241d0f0317449100b10000c00561102d0328041c000c0301c0042009490000e04244030f850b503824103858076248161303601ca0b00705191100090301400a880350500540e03004040b0180b991825818100075210000300f18641e0580300403980b00b124003000f120004102c41031a1401e4903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 179455296 1250 179454046 179454053
    0x20607021504170702030115081014161202090d030e10080412051b010c091701020a090e15040515030f0c091605070501020a0c0c1202100302030606071a04 68
    0x411003030a10150503101205000001c0d10b4141103c0070032007000d9450341c03141c5203400024050000a03815040c079510b00b00300802d90460104040d24207086204050041640031108211800400c89071024080400104994160700c00c009071401da9103030000c09420131768908001030f6000302c880380c110701241c1f28003564803090408840356070701a0b80c6401c01d08210b2030301d40c1b9281202c2c02c048121004104002481c0d6011004c2d2b640c0503000205103030020084c1c0b1114004c0541301c00035a000300d410404d0708070110402281c050003140c4401c20b8603510b90301014500a103506801d03402408840b21042059004825901c0b1032241c80c0c800c104944000241424800c1072504040c4011a0f14040f90409400c3c440e95031603100419400c002c2c400042400880d001000f00c5907401241c00040465000103030f000c49065108007003404860207500d002410b10360360840201036070760f8000001d40090200306000c00c9a40264065076001c41c028008600e041800c1e039541d4581a400f81d02d40461104280a20050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 179456546 1250 179455296 179455303
    0x506060d1b140c06041209030c0305030309070f0b09040b0406030b070309061121040f02060307020a030f05160209060f0402070501150602010e0703140309041b030b04180201120b06070302060702 85
    0x59410b103182c0185045691100c040d1160b20080000d803000d440301545182c55846001e0751001540c001202c808050b407a45003d545036401030750120010311800001203541e0320341c03205000c106c0342d094400c60700e040611808d00003d441c081c40c003582e000780d4035071000003c500c0803040716201d4806c580d00000c407100140b800d50211000c40e4030300316901c8030501401e1030074400c0d41d0040c051a10340f808543c01c26595843c010505408048000f03400403004800c1c400c40c0c0303400080d40e0009034481e032258a58a010340d0000c07600340c0541d800a1103040c90b140ca41d540542003000c000340d0480005081e043d411580c94001c00c00741d0b030181d0000c480981d52030b9034080f0608100130301400980342d80d100038042410031411240d0303907900c07500000d0710078500020341148000c4100126541c0d40c0026205000100096500f03080c206e090f56500000729081c440d81e0880b40c50300e0320488007500d40e81d10190a0010607a001142e8030288100310300c441a41e10380300e203001561014050007840d442540280020b19143d50000d0a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 179457796 1250 179456546 179456567
    0xf0f1502070c0e070e01051c0c080403020609011e2415020105060d0c030222050f0405160303050f09010212040e0108160506040501110c0909010605030c010816030506060d1b 76
    0x802c3c40030418020035030741c44242c05003454800d10b0000c0d15002d21845022070a19403042c030840607031904440c44442034216241e2031103240a502903904d155511454242a64401c6004001c0031700d0381c10028101c1d08080c0e0202d40740c1200565024465103c0c00000f1051300455005403074845d50101500c02000e034240107059001d1021303103880c4450041555a0040381b03403c1d0100038483c031116105190740f64203082013045141c6028405216900f040004550b80e40030a0350213660780d01640002210741c55440222a007141d5055807036074038290701e4400e80b41d40ea810541074541103000e036a0801590b6007081c8060406005112515113195140070b013910700d0490450b00031240000609400c1169954603010b95045500a00308049101c2020480508255403400e503164010840401e0220801c015808582522016403c45078045410300054500f060101c8412250201e115000c110f814031030707001640c11500c054042400c0002030b044000c00e80f804c1c1c070030780305a100050948041003030740001c0445 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 179459046 1250 179457796 179457809
    0x7052a030115080706111c1b15050109020c0a020f0406030503030c04241202031509100305060604090b040f170403030f031104030302100b011e02100b010801050306040f0f1502070c 79
    0x2594183c1b42c5115200c0c0c42158040152501c4000c2413200790b800b411891006403509509000006107514201445070102c1800c40140d40c41e00b070002c204041310380700322801d03140a20020540c0d981d145e400c00080c0e406002080d6001a00c1c1c07000000040c1e4104051401071084461003a1214240302202105010107810401504490140300c0b1328a50171000c4052180c42c4c0100c0076075641d465101340304d1004400c80840b41c000b000c000421212080004656058130300c80c0094403600c0e220301d0104001c4e268010320140c42801c0c00c6011070005035003040e40b648890300c501180700c1a580303042c03401080d54006a01c140c0104074628402d030926030341131264449001210074500c2c00c0c182180c8000b50780f40042086880000d68656840001d6030081450341030a51035108001c440f807044400080d1941da14143d510041d90408103542c50542c0510a124160b61002e030090000742d807544c8442a403614504001d450010003144d02c100800c1c210140c0e5080a0089030015036941e0303080c54043c00000c110b030f0009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 179460296 1250 179459046 179459057
    0x3010b01030b010906050d021207020d0305010f0609050906040b150c07080a0812100302150a1b0b0f0a0207060501030b04030806040501080d0c050c0613030b0a0207052a030115080706 80
    0x440b0355a0700501014103984040c0740003526000400180d000a11921940e20f03400072032002000003040e0b000a201f68066180d5805112031703660340420700070940700e03409203c02107650450103010724140001034940c0410014001f00e545940703200031440003401c0d030051b441405d0000410300c00e098000c000309801003403108000d144000c515144e910751401100e042c1000d01c040000414507840e0310700302c4075014540061548988001180034403205910021400d0040b884007e0078070801c2c3c4c01c0502402c000c80c0c02103d4000240c0c1e500c0e401c04090b400082146141a034248a5400424944d1140d20301951040b04200554200b0307040103849190001c11191240f81080700500c441d001c082003028032001076040c58016881d5914025003414145440d80b500604c1c0800c4098100d03130303141c840d5001c42e809460008400e4880394100c034203074402e602c005080c2d85d00030982a4060709000d5a06015403d038030003154400341d8180300003800e5420328141c11034010f408410034011400b0500007107000b00005d00f00b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 179461546 1250 179460296 179460311
    0xc030103020d120e12030d060b0313080a020a1b0f050402070c030b060604030f05010f180506060607060216050c090705090a03020907050f0301080a15050f0604111e0903010b0103 78
    0xc0c00d0b04980301c900a144080700d156005605000d03440b5400e6494006114240640444038050341c0d0740c0040780102c00040c10305400182283c0080304580c012051504030050849860712030b40b103558440c1c60380300304510441d041100841c80f0305520344804c000c85040c00b0282c0f894081282c0035000c3c0d40e0041c52146104100703010010f04106617040c201daa000b803030905159140303400501203024a610140c01c4e4413070345502104110f01940f0080046400304400c02850586144a071400c1d400c078000200103030300c24004209a4540b51000e045001c0c89040090300d03010121440c2284001c0d080e40840d0103512010b544141c81c40d00f401c0896111410749441070a203c80c1c0340004800c0400c80c40064080c54082d000310341301601c200110b84400284622107603a13540d680040d1603072849003272016600c10316101c1c000c140710a0b85001300c5003d81500e00394110b941e03c4060411008104142042802c08003c0284100103203425070b0180c100c44402d003240d034030354281c1c00606003036540c4400c40504042c9403586 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 179462796 1250 179461546 179461549
    0x4080406080a0225080c0d031517030d05060f120c010f0e030a0f051510030b060a0f140103090209101a0903030406080403030e061003060c03050702070b090a1a0c060c03010302 77
    0x40c002030703120820046410340c4869007407410b0180316030300c80b011040c00391150700c40c0e0030358050b04500c4900c034958030400c03881c6540d10a000c071103140880300c03003d160300b0030844e00182030300300e800dc650001002401c840c09a00038400040d520114807107090701075085021985110360f0080f003000c0d110032250500c51a601d40c6000080d40f40c88507820001c0865003004400b07402d001041200b007481c0300004a41d0340040c2800d10b058170581d881c0d84001c6554012036000510703203041001290040300c20f041c003800f070741a0629a4000c03a42d038020001c90b042659843c030070701c013580e28001d195004280408040c0c14060034060717489900c80100c0220200c012080229210507180002160112500c40c0341900c06a00d883c40c085018005040714507080b1304c1182d007440442061034000e102141d100300c0003000091200d120540590b01d00311458005a0000d09040044500402c01010342d40d10003051596103a864090654411484180200e00344030081a4501408410000150031941100301d4a0540d0315690 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 179464046 1250 179462796 179462827
    0x1f12030810060e01050f09060c0a051002090d02040e0a060501090b0a08030c0604030c0f0605010e06090604050f042901080106030c081c12090b0f041b050108040b1e04080406080a02 79
    0x40041c1080fa0001c0c00302d83c21503181c0d0036030b10301440048c0b20345e9440c80804000c0350fa0701001c040c1070310360380181c070402440068603108486d0a00e42c0a003401e02344505039000c0000925400c03002c941c05018900c0002e001070302902c9001d001e441c0340d080000d03485a0380428480c800205802800c100d9000304249a9292800200e0750340c0543c2c0341c5003070091203c0a01c2e110403070402d40800148411b0401c8000b0522038400481e1610407641035641400595070700c0c00304819164181c03142c04010b4018008500400c101c0b9040f410040402101160f80309062002105c0140c403d0303201440030303503441e00d09008004114024000a09860307005140d424103a12494000111000544e001d0008402100c0e8034051190400034013a50032100001c1c1700d1500d0030168445440856080320918507000e09000c0c04007400d00c822003074031811ba440155030b43d190b55030450760200c06031000c6692185094149441074510b100548a28801c0b000c4903101e501e4410b02810700d90018058207095030041c031840c2180703084c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 179465296 1250 179464046 179464067
    0xa0c03060c090f091b210c02120705070e0115050406030b0a0f0e0604050108010e0309040b0d1e15020f07060917030a06080606060915031f1203081006 66
    0x34030000782055800d2007620284116800b41c2c44244600d0000100b42507035902003020010100809001c060210008603203016100c1d2801c0d01c3e144800030410318550340f6601492080c85240101c840c1c0d0441011582003e41040c0c600311070581c8907a03c1800450b062090740c41c01810f01020600140001107000b61944c05a40507aa00f0199507502001055882078070341401012512480106107445034100d004400080710200d020f40e05040c0001070101052081d40070b40351100000d9801d01101c24204805450802c005d9a44100d203041e05201007132400340c0402d000c83c1104c1c0302c1d0368000e41ca45404c1c5600030b48110444c1c41d081c414011281080000741c1140c4038243d100b4000181031120303103031030b0311001000f8055140c050700100c204407002d8800ea019409481244d0119506503440000b000360900c070b900b00660300540c00144813020480520b015581091910417400c64035802004012114000f0740e20960110303034028660790071f0542110003a5000700740b081c08c40d00c0ca90f00700300e006020680310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 179466546 1250 179465296 179465303
    0xf050618070903060504060c0f0e03100902040e0102040b031605120708091e06010602010e0304080a020904020321071a070207180e030301030515071b08030406111306110a0c03 77
    0x218000541c00d2882000c03010003a56021000b000f00f41840e040c004010180c1c050b02c0ca0115600d109246061409034040b1222040700400400120010404a2024080c0c3c00d83c226000f549904410a000300c0c00c0c000762001e80301e18481d40ea00c1c2c0c60440f04215003100004d40501c10300c40d04122229001c10310500940c1e0044207070510b04144c2c2caa135440c040c54010701041a0f070b040d01c524580049112400702d8258100c40d03256000340840c01000c10381a81324841c13481080c006903c200032120042c2410820742d0751250009040d114641d105084240b94000021085ca641e1100002c0a0f020460340a1020a00c1d90248140b10418500920702942e00e401c5801f03031000c0c203814640180190701094104040004481c4103417601c070b503500d03c2d015945888941e10008101241e9001a54241c13040c0031200c04500d20b0481d1001c5aa40d5495908071070b0b08c05881030311400d48645c07070030300c1743d549140052400358428110710f44250b1610800034880916812030001ca6007114010201180d05421a1803e8a81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 179467796 1250 179466546 179466589
    0x70b041401142a072313020903060405070e0a141b04080a1505070201020310030807020d06021c0605040e100b0f09040c080f03031e0403120510090f0506 67
    0x420000c0400c0d405410710002801c0a6424520a580141d4451256200f12803044500b8a0385500e03014003840c0441c0c0c0e28203c288180b103088201c501d0203654500c143d6040c0000185001d01c01000302c0d042907802c880aa615a0107120201312001d0040300d8141c2c071140c45001000845020460b0300100745014004c0241e0602034103e0400002000d42101e0082068500300e41c0004283e244c500520380c103401e1400082c6103414000303036555006000f141e10039459071b1403802c5c0307480c20f40c0c3d540307640c070303081000b050b6040b111091900002410503c02021041d840001000c0c00c0c04600c003904d010f031686070300400d004504120318071101000c00a03050305000c01801c000b040307405440000c1a00600b00091aa52194031003007032105210910000105540955081da14240380304610703560380b403000759103002680300c0c81041405a450101e00c6160028071034984054240541d84003034003500e4040c0c9045000c08900350080000c80c800707202d9181604541001440304c0d10b0010001003403c010740e4070002e1a401e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 179469046 1250 179467796 179467817
    0x180d1b020a0e10060806030303070c02060a18060806030c010c030807120f02070f05070e06010509010507080d090501021309060308030c13180b09060105030402090432010e070b041401 80
    0x1912070341c140010305032580e40c0d4482072914028040004a42d489004003141900003c0b03180780c1408400c81e0310440d004d0f110001d041ca000e500b40400b41d84480001c0080150354403191845142910f411070060804d96103095503828200d003010b0400304040d01941c1404091860b020009812502d5990310020714203150400036156031018010700032140c84a5405480044e14a0410100c000c0c40e07400c141c0508225283c1307580321100100f11140a8a05602042c014400c0150540c464801400307a58030980d00305c0e0402e589601c1400649040301c004a640307035001720340045407038114500400100312203282448034601d0f60702c61081c0e520000d402c1801c1450009041c0c0c42007011050003900a01040a0174180840002c0d0b4200c000d0400701d22030b510500c403070008034900b584100248d80c0982d40081c43c0c00e0303088d01c40d980c420f2a0702402400b218031a1085581d1080050b2480000811103541c02c00041210055621900d041007203d0f0050411108144424072408540116280b4401400c2c01c02c08460b0703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 179470296 1250 179469046 179469049
    0xf03020a02070f0b03010303090515030408090105070f051f0606050d020a020c0303130305010f0c0f030b1c05060a0b010206041e050a02040204031101020f06070f081b12180d1b02 78
    0xc0001c1c1c0005000443d91407002416084d50b01c010346c100c9000e561603d0429484030308025030021152030340150444c081c0041804241444000e00340814141061890a07016541d0300c0a0700c10014001d075055000039400198550b000c1411414136102004100305060510ba0301801c0384c0510845e10315519404684c190000b8020460021460f60050440380c40d02c03c006110041a41e245c001100c19509241c5d000d070300b40c01980224090580c16840b080652454072608038000e1201102c0386130710500c1024440c0c800c0e10000082000390b40214003600c0c02e0307d0900c00100c1a1014031091070b04540c480020003000c280004500c8208000c00d1003101ca0f9141c2a013810b07464010400b00c00b035803003440002c0000810160000d20740d83d01ca0203800b41d6407078643c8402c610f51980402c0344e420300407500070718065010b14807070300c40c441e8000030607640d15410381c40c80150000f154200c60a1f5480e21860340081c0f2040500c4540e10810b104520f60086c4424108e280d00180405510000c600380590303241542001c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 179471546 1250 179470296 179470303
    0x306090a0f052404061505060a03020c010618020909010f0e010e1008030406051c06140409050102040b030a0204060215091b010c0f1110140f1b07060206060f0108070f03020a02 77
    0x495562070381c401c07210070a2003045600f0360107690032a206440c1400c40b800381a1a2030b20002252001062a410b10000c0724050300a54403001051000e556108404100c920100e400c0c000107010081c00140ca90300c1d03103070030f1003195101030300100441c030525541000142e816200b1070381510621048406140c458080c0c4030000d01c40307500513800b64003001c02e012881c5644803028025401070704100005507800e840004040300d049001e112408161101c1c0e4012a08060b003204040600c508001441d056131211024001d80046c0d900e42210b9400180410502d80c0c100024079005003514110051801c0800c4016038818040c0b03a80100095046219484ca81c0a48141c14184d44c000f0b00018440385546000380300b28118080d094031520f00c0c1d8440400740c0740314284000ca907103d585146843c01503018400380e0103411141a822400c0d0300c01c801071200720001e220080050045400401d1642042e4042000c44035602d0381d9241086048002c100c0070562100140790321192508006a5a07030f81042c04908 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 179472796 1250 179471546 179471563
    0x304050a03080a0513061e030506030a032a1415070c0b10120b0403020f0703020f040e0a0f05030d0b0f10030903020c03032a030f1e070b070201020d0b0306090a0f05 72
    0x1081848010004c0c040e600420f105400038510511080b50b460840d00c2236003200d5091302c10581591103201d10000080c090140788600344022000146500000d0612800d003c0d0200c804844008a41d08241c02d01e000402180d040045e05000c22a440d1a00d000d009204005000025015040e090003041041c40300c1843c0e070780544541015151406110f05003034200c60340c255012030040c418484900340c801808181c441c143da40c0105400207020070b040410002d003a154880c0201d030701810110b000003601c0041e400e03800902c2840690b888408a082c08000c03505140300050003a0714103220ac092559924801d051032407490308002070f006d426418120315011050000a401d0f1000281d03900500c0c010014038045c0700b02c44450407a140092400b895160b02034515452075529091004540800044402c1802e240340d8846850504405d0748030403841920030740d8040050307540011041d2f010322050240c002000c206800405e02814864052780e900c4805081c081c0000d60110b09980070441705100d10368 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 179474046 1250 179472796 179472817
    0x40f0e010b030705010801060f030203180a031112040e13060608011107020f151b0a241404020a050f0411070b010f0e090304062604050d09080304050a03080a05 70
    0x81a600050040c000d0260000c050300c079115403000010315602c62009241079900e03941c2c0c4c9250300d000c84078082d8065080648490b90f048100c881403084e0800030025822200e00955400050b26201c540b15410891220900e1403404000c01c01800302803400d08184d40c004020035501402d6011a041050080009170820789055090005e85500e030400b2402401c8818000c581200e0b100c1001d8041008600c1042800c402034401804140003800610341c1d803460845170f9105a80a546c0c5036034404001c07441e181c0e4101c45200d0072071113861200c031180c800d5800010032404140c0b218202500080c80003901032142d144980304000c1da070f10b040d86031074210043d032030324071807500c0c0c1c0b00c104a00d000030b0718038030034000c14020302920900001e5600210600901271490a40914900740c2001c504403281078100c4201e0110041d180d4200030f40485148000f0304c124041c3c00a0007900a114800502850325030703000100f6030380244414056991100e5030001242c1d84070074030a90326120f4007001d6032940251158031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 179475296 1250 179474046 179474051
    0xc0507121b0c051801030506040303091719030507110c060309100f050919030504061d1306050901150e0609040b03060f09100516080a0e030a0c0c0b09010c11040f 71
    0x1c40400c44140302003800c0d540308903141c0091085540c00801040002d11010b8042e82c452000b16011a00a030301410300c01e806168102107645c10100d1030a1144e10851145020003c2c03010407400080d81485402d411900358a4150410100103400035070f40d6004980862007602c0000c04111403140c10483c01003000c02e064402c0c402c0c09032441d03020300200021902e481403801400e040000b2a01c2c084c01c003041c070f181d150b25001d081c42c0c28040201cec1d080490003c800510005000d040748035507141c00346854652039201c03010400c0e60800d410701c0744005c81a07000c0f00704038600c00003c00e00d281d0009111404114141c1d11591160f1102c0005405050155030b020b0b00340c00741e2000d00401192074019180f143e00c403001140c492440520301e80b001c40b44200e80c06101103000403940e03800e013403054101c940c100208100200c4c0c104e00b2005c40908591080e20040c1c042a4981019000c01074004000e200400c0e0541c0c0c228181810800084e11304404030718000c21000d040c06000315a43e503540c1c17203c0c40c0d03a44405404c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 179476546 1250 179475296 179475347
    0x60a1e09030201021908010509040b100506030f0a0b152209090f03090605190807020f0106060c0506090708120c0a050a0305040608150604050f01020328120c050712 72
    0x60b000307605c00314074800c40d0f072a41c2c0681c94540c0c0c0103d48650489002034240384143d5120340701d000c09140b001c0c00003510190640000030740c0d543c41078051801110380000144071401d1180c8074104070307841d254140d07000d1702d1300c2201322405c11a0003050f43c00c084800040d0b0b441190258000400e084519003105da010352424060600303000d900c000b00103c142c484e4032400040d076102d200a6840d406003542407100c800481002004552092204170f401c1409030048170484018a40c0c1c0c2803d44046400c80000524000026402c0c418108506a001840c0340c0c041e100c07040c18881045e0300d0316958100708100c508002403a16680c2d1003008203916050304101a18840748092500400c0c692046c424000081c403901c001c10940c20445012920840000b0001890149020b083c000b1b0307081c2118800e030540c0001d01011a490b003c01c86030b0b60212209410403403044da5072950150511141c003001c0120145402c0e81e0605e55a04a41190a526001203d101c1c4000b00428110341188182c42c03042d001140000743c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 179477796 1250 179476546 179476553
    0x70b0304032102090f041107060e21030618040c091505010f0f08070f11160512030403030219020a0305010f0c020c100207140a1d061e03060a1e09 64
    0xc0a0028102c2032003a03084107502c2c07000210581c0520503519503c10004044814286080c0d440b03011880c6e0141c41c954246405c03515108215001100e8000c0c10b50400d20648000c48441c1100b40300441800c0c2b001802d5042810124410034107000108902a00041c04501030105801d40c00c0010418100b05000b86260f4110383d9a80c10fa4602c203280c00306940c1201d203a40c0ca8060000c03c4056000c5d03548062090741c0c1c0503021110b0410b4030001c501404000c62070552a110240035941c0c0d60390380496080000c500d04828048142206050f43c1c3c810f4000740030038030020f130740030680204a0580204440d480c80d40340c000900c0301d00440c0d000814540c03800500107400d4405c1d401c01c0d56116801d40036034043c9200f0350f09002c11304100c500590b0040e000200148429400b201203481403810140056101070b0b01e03001003400c031030b004645180e504001501000442d140c002d590611120202c8600c00001c204007010941e10315018281103011915000e18008446010803100d50303950000300103110160365401e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 179479046 1250 179477796 179477807
    0xa0c110f010c030c0906080f150a0603020711010507050d050c1e1c02032b090b1e0a06140d2a0306150501020706051602060a031d12031602070b030403 66
    0x3090440800d080c44c030b0442006016000c4507040380c2039030b122080581d543c2401c3c4c00004000034490001e041d10312003185543d40b1403a010901900711078500503610f118a060aa40791521090307801d0421204012000008a004c207030103598a880d41489034803a031004641504207031804050140700c0e1961a428040c0c07107400101c01e030302c1150001d85e109108075860401c980f248034040c00042201e91070108540124216841c035038580003c8030000841e0006982e4030070081c0f1090b0342c1580411208441522a402010721481d04403029450802c0f800f40382c0b840710040000c1c0e820749503214500102c844818044690201001ca5044201c3d01a903020082c1d40c1c040010b074603000035108146401c44001440e0340c8401044141e070700503002000c1072032415100300c9140c1e00c0b082c540d0f02041100800c160050b1180703409400a02032a44001c01d0b16200a04024a14010b4203c1c0710041c1c2d00040c1264032070400b21003101d40042c4a00551410801d1104c400d0746480040c2d80f189200642c00010003040c0359000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 179480296 1250 179479046 179479061
    0xe0907031704090b011403160e04060b09090702191101030b0909010c0e01020f190f05030409020d110304031715030609010b1f02100518030a020106050112060b030a0c110f01 76
    0x2030300820001c4d1855004407018416400640318000040002c941c4ca48440c0f03518042c0c0300302c1c0f4606050703100c2c0200081001c4e1000d540c4202c00584c8085402a41440d08006140c3d0000c583c0c40105111540611091041d0f6100c0c0b5001d000e908990000041c213912a4212160000014210022500300302e0714a034028400d24080f41c002031382c03040b41100c03035610204d80c1960808614009202c0e104411040054080ea42d020440d0342c400600d20b1140050001d00140008014a5500589131504650720a007a0303940e030f00c10103ca5101c10020040001e80000300035111000c2c2c02c5582c1b10039aa20343c05012455562100f45a15105410030000c030084150007007c510001500d840002900c0c00e00c500782251034040c258405a04115861002c41d01343c1c0e40602c1c0d118810407a80c50000c2c0b04540c405043d0760105410b000182d4480d4000d10995810407034071041c1c4801c04900300000303460302200c40c0603400003401c803542040d1114035031410b10740309222000040801c0300c1910001250b80004900a0454 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 179481546 1250 179480296 179480309
    0x30906081003021806011b210504030302060a1508030f030a0f05040c1203020705100203030403110c032a04060f030605090c0d0609030c080d020408060903030405070e0907031704 78
    0x2000001d1102035082030700307204507680500b4110140f1140310400303103c6000140010704010842c3c10240d402a4241000030420303000d000351030f014460540444a0f5001c498103504244642008108006507001400542c040f1141000184118007607255035031040f034550150702ca5220114845008960950085016914581d0304000400c0000402416614101d03009490003210314002c204480030700e40d0584445119105980c2e0042d200c0000624407501c112141c00103034000b0003088101a0007295903581011a40c00805c0a541000c0000369a560342c1041001c50310007c1300c2c2e50380345920300401414201c40051081c03102c03644841800c02680c1091105a03606410180480da98010109010800c0c000240c03a0244001d1542c0b582e03806050001012020003981900c1000461840710240040c01203035400540c0d258502074940e80360a902801000d000d4004000f804001040020181d0450b0280704180302d4039991040b00c5800e04201d640043c111a203014004001c41c0b010100030f1050307890 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 179482796 1250 179481546 179481557
    0x1b0b060f0f1002010e1011040302150906040906171c050f04080601270204050319051501030305030a150e04060c021501030302010b010909140612010603060e0309090f130611070f030906 81
    0x11000c51030581d1007d100201c11200100818409030400d90055109907207803400c01807130b203100800803644682c01944a05c010a40c0e555042c04020440c548002d441440c00c0c0090203881c904054402c030668000c03050360180314000441c0a0031030614415200105104030030348503035603542d880c1980040d8101080051401c100351000d06c0b01c021a209a07070039201c01070001c0038100561702074018a50000c0100382c0b010700c81d162a0400307501c0200c09080c0694400d46d6000c5e00c80c104155540142c402c80c640c0c8041607049444240102600302c80850780c000d421000c0031842d20700c242e85c180d060014082036010070010260020007410380540002c0c40e0780b075082e45d9525015942d1040303e002c40d441000e00c014200c10903404148a440c000540d80b0803207111000016000750f803991240d0494402562a90340313908041002076042c80d084042c1e5511071050303541f03140c0714507002503943c0c604608050010203060b6200740014072818280141c03500180d2020145c101d0607420308010b06801040d1044000140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 179484046 1250 179482796 179482813
    0x10060e0405060915160306030501051003110f060d09020628080a020a05070f1b0303120501080a02060a050a09050a091a01051e09060d1107031b0b060f0f1002010e 71
    0x15000100341000c400e40b807186104d04c0d240c1d1451880c100101008200416484104c01b1000c601c081c0b0a841c003400040001c0b03600c82c2d16600d000002e00c2d0400100300c1c130a10b800c2c00640b5444c0c94500480741100c81c1603400042d44000f41c80050f40d5802459148003200383c501202c00303010360000c40301411500c001c0d21244501d0340d90301c40600c142c0c401c001400002450612516001405100030a1400d0b482422040c50025180076004498049980150b000588000501d81820083d00c02c1034050403485010b0080c214094010844600c140c900d0301c0308103c000a20840024811003e080192a00828410500795101e5107000580444d4281d00c00f12191b14004a0b2158040c02c1140c80003000d002000644280501a0710b01607000149000e400140401030943d4100151107085101e0462044250b25000eaa0070001c1107041640d45a42e2480b00c0c2501000c041106113205691000045400340c0220110b80301145801d900c4644c0650403000c41e40d0480d442c1c5406410490000311220111040d81 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 179485296 1250 179484046 179484061
    0x8100203070f05070201020a2103150303020604030c0f06050a090b06030c090a0c1106010602030403050d02010b0f1519050a0f020c090c1b0709090b0601030209101110060e040506 78
    0xd21007a035041010034201d032070079401640510060241c1900500540e41e212050742c0b214150104800021041e031201d028180c45d15640600c98210303060a284031100b001c42c116a00a95507242c0500081e007800031220f0041c0800031a94610b00c01642c0c490814400c90402c9107480d00039044640c000c40c0c440409000040c0141400101504120310083c4503040702e84418600c0f000030407405a4400c2000064441c003004c000081000720b000740155401981d03186d2843c2091424140310294410131a4145201d1050300d544011034084401800c9452005100c0c0c40f0403e901e50f03100e0780e4116403000707002d50442501030340c01a028003005004e60b1910070a42400f248200d840b24011040d15500c000441f001c91054920040505624102e1040700d80003c040c01c481140383c5405a03008c0ca00ea141c5404ca140100031441c801540c00c19402e0034254242411700001462003041210380c50700b000806000c0c807098040801080000f050a004104411512111020f49501040302c00782d07450310035030001c42c111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 179486546 1250 179485296 179485301
    0xc070e010e04120f02011d0d02010e030a05090f040902101710030803040809120a060e15060d021e0402122202030607030b0307240e0102010b0112022d040810 69
    0x1c1e41c0d1142e020001000c3c01c9600303840300c2204141070811503603034060b11959000503e0400c1000c24901c0f0003854100e190680c028213441145a510030140c00a012312012107400c102a0743c0084000c5800681820841010500801c44120069804011101042080ea41006221042c24800700e02c144c0725135140f8490b2400c40a19210081542d4410000203020456030805030481e084000c00840c070300c8040800b618074141d4994401c0d14210754910200201020811007840b40c098610000c000d5490010300140c0781003118035000e4091008c080b013420b008286500030405440c0d00400071501c07200c001c00c0412441c5400c44141d080c09040e0914000e4400c0e100c00d500c4c55032640240280110780d9800812409440401103054141c802c011001c100400350030b2020980039140c400e44001d02c8080c000c0100748034141483c050541e4501030f403039421644e000c0108401701414407000b6a503014000e1401e80c000d8120205284032180c480283c0c001410490000c004407403d000c110340907046040c546004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 179487796 1250 179486546 179486551
    0x10020304060c060908070b1810061d04141f050f010f0302150c061302041a03070b090a180b100e1809011e0e0d080108070b0702060c030c070e010e 64
    0x1040c41042c20200052243d08a042114400d01e602401e1204642e100f13805120151940946100d0024070614540030410070207035403d400794414802c580c680030384142440380c1001c0104030352600400080522050710302c0d00742c900c4010011900b2071aa804904000032400302e940524140c10032010031000d448030380000d81a529008100030249242d0f90801180382403000c900d40e21601c06200058006405203d003a200e0a55040841c0310084180b0400045614659100321800d14203950b5600d103890014009050320904100036960703c2d211000034501090680c4055080706014403481034820103508002c02c00c203000e543c0003c0700c050744681070b1510400741c181582c014038503104880746001c2d0b006041b600108c54800000702100454428031420500b003258507800c0d0745a070300780007502c10208041514a07045180400350355040c03540c6151240030f10b104440081c54041399880030356070340310b04a070030188803441100e0790381525000707542c3c41d40388900c40c0030700c40e402007400020300300482d004161 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 179489046 1250 179487796 179487809
    0x50406110723030f0d0302030f01170c04020a0e03160e0f0403020c0d230606030d0309020f19180c0207090c0e011d030a030e12010c1706060d051510020304 68
    0x10100b5040b207049661200b00040d450312401e44800158001400049005182a600982c1c1d03840d26005800c12514180e00c907580041d004060003e01f8440401c998080d0740c812103016039201e00f03a05088a10040c50070b4056071501407800848410000b02d02c0100446050030340d0030580f81e554030615003da8208413006000340c1c118801d0380800c1c3c507000780c0c40f1400030710820f00000e80303511000e4600703443c080303e1a10f140c150b4403c400b4130200c0c1c601004620405e6001c0d2a05014050b00e560200d40c0e008055242c181c0500c1107400b83e0a0711030401d54154016241d01e0301a5070030007110300b01c1400030b00749001c0410090f005104000c17520381c109001e034280459042e2250300400900c1c800455039660584251030020300316601d045110740d02032100144c60f0740207070b0b85e41d00b11050310001c00c5241c021070f100080d41685400c2010b00400e400040f108100c1c100c02d243c2c5041d0b039440d07030085601441250001411245030a04100d1034912004441c2d501c464142c40380241742d1b44481007640d4034030960156a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 179490296 1250 179489046 179489069
    0xe06030d0c0210080718330903080f070602190e090c03011401090302030316050c060c071a131211010f0909020903070308040608010608130c090b0301021303030504061107 75
    0x1024680e01807003d151700243c03145007030700e9140040a4010880500c940003000f00040f03071110b03119002800c041e81d003021007905d100c019019079904406080b200082c84024840303407001c14400d00300e2010030305841002d5000201550703180704640e92201c6144400c010440480e251003000c5189042003240c0510580000e075040380303182d007403440500c211142c24848604200c0c06a40100c01601c0c1440a0850b11100035030181702080285042c0f418082e48124003070181c9010b00003480c441a000800034100e9032800f5880c100d42c036440e6038490041c441d0040c50400b4070794408000400c06c0208a0301e10400d40945003500690130100011a500c0d80c40c8086800081c0ca000024030898003a07034005c0149035401000c68007410303541d0707440043c4d503002984030700b02040e10700c07004006840c3c1001c40c09912066540c0041a003500a81d04d04124100030b00862900e00d5540c0546605514250b0440d96510f0030707620110901542c0b490014280d47c4030340507800020b0b0894030500d20302c82c2c0010703418050300ca01c2c206a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 179491546 1250 179490296 179490319
    0x20a051c0504030807080411030f060a06090506030a02060703050f13060e0102031206122103060907171f050603090d021608071202010302070b01080105091e0a060b0411040e06030d0c02 81
    0x8486c0c400000d0304c141c0e802d140041c2071818550f01089181055803070840506600c0c603000401e1011507140b40d1047c20a00e0510040080e507642c0444d81480d02a41190815142d580b5414219000e00030340540501c6800c0c00034000c0704005c000300704001120081ea81d0143c02c1940b103401203840b409092816204107050b0304c0498083d240025200c0d402605040445590100784a205103400b0030000305040c01c0000042440b14038102a0071003544400036089c411207040e0820f181484084004004015108514003030800002c030181e000c000506008010545a0078000b6820780c50303038500041c140162198255901e032581c82c4482e40e00c00c03201c1140c050f0840d070345800c0c19140c00300701c4148100c9c1016800c101c1c45c0009801c415920b800780018000015403850f00101462400c1d00350212a13420004418a1009a000005800e150190f00c000c010070200c0b018008503010384042422017064060101300400c42c000041206449030b08118201c619a0001140c00d42d040503104c00080d4110100300030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 179492796 1250 179491546 179491561
    0x10030201120b03010e012405030f0303070315030206040902030a0c0806060f0c010b030601030c1a07080f090f030106080109170f04051507050a11130b090106110f01020a051c05040308 80
    0x814200b402d0b000e000407801004a00700c640c00c403100d1a82680c1042d10944031071060301c000c94088000f4110940040c00c121559000141d40c0e408020020380415442d0600304140502c42c1f4144401154041e008503181c54840798100069001290041140e13880c1480c0959100d105900b01406004c000d0459407420719500c00080701c6500502c912001507488030324001d02500d00300f0009008500984007890340c1410070344000c0b032040e8405110504020103101600c042040b40081382d440000b404004c0c2d550340315000202d0b9284119000c000da041d46060740020700e221064010010700c920030662840040e0302030048556a000d1054803240110092106004d1400d00e00007180d15595580c00c0c2d581858010b0303a501d441e0005040c012070b1580c00e40c3e0701000050402c0302181c0d81d003000c0580180031080c5010081445c0c040140718120812440251049445800340403030800303074001d50002c1d580c401240750b0144c200d0384803000c84a10491014a80075098000e485070601843d4183e40d80c9203035495042 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 179494046 1250 179492796 179492801
    0xb01080403051b0109020915010906050a021c02100905010204080705011706090717010f0302092d06010908010e030c070503061005040203191802090603010e0a0b100e130b1003020112 80
    0x221400b12541d85d031a0b541025a03141c65006202c3c0101c8051058451212000184410300590001090040070302c008030035a50040b50311021030000812041811720140390803440d250106200100407854034946200b80321042d00107005a482c40001c03226820340e52401181d0f007413a02100074048544101c081942442c2c40b950461700701c441441c1600b0f860031001034a1612540c00c2e03104440c1e000c4010010002c5040500c121607120880104441120756031003001c0c0d400c42c0c0045160740c41c4010840c0007540b01c0c0c0c050310032100580b0705403000300420410251391035030380c2d07000240020161258007030000d0245000030303a6504c10b02c0d0040c002954903240c9410310020350800741007d081084081c161007400d001901c10700c0c80544044400650202190041c05068440030380043d000b42d041424444c201c0000042200e541640040e0500003599000e020790b00310b03c10351b004043e0754085d100a111075248225072442819024130401d182545425002c60703405c4407d403000a0101e070b0000c01c051207260555 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 179495296 1250 179494046 179494087
    0x709150806010915030507150e0909061303020127020901051012020d06030b0901050a0e0d020a020d060204051801080d050412030302180319060b040e061f08060a0903030b0108040305 80
    0x3038050134140b0b6280c0c0d8500b400c1407880d401040095408004500c50075034032605105c0003070800d0750750100f0360030b04c0d445c0c1d1900c6241c0240a04e003102100500f06003014800d5221194031440340c55980112802d11043c40b2800c06d40e580d0a0384102030400000c142c0303280c5030810381c503000c240d0b885030101c40d40e00300200d00103508585e40003551240d490b000000411514418284038220080000602e441c04100920450300b9100e440b5406500c0403680101040d000191500c0e820740496100c1c0d060003452428501a1299401c2190461074004000b01c0400e003070000f842c16280f102050380c801003084a41120a80118410031024810b08010013003c2400b81d402010b150307200c81c81d080b00800030107020910301101111050440c1d21035842d48424804039114009499008942c1400111100c5040664640e0007a100b450048171100b01001207610041c0b030b1000410301c40058035107524000390400300a00b492041900400d003811601c45280d0300c43d8441c0c51082d07034141c445a00304007140c00f000b075240b07915 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 179496402 1106 179495296 179495321
    0xf06040510060207050103150801060e0609070e090c030901140c1306090f0306020306030a06112502010c1412041401110d0c06091a070207091508060109 67
    0x101e501c2049400911f03011481948102ea14840c07020140e000520641c45c101d4006440d480a0085a20840c8200d031340030115075580c074050b208034211032070256001c141c5800081d120f02d60f8001540e0071410940001440b10801c19003480800002c0c1c542070a64000030079002c0d40b80851480f03140180c40d1504e0480142407414103181c8603144d05000041c603013900880020300301d440c100800100d1a401040620517146100e0808040f5031000e0000400d150310f40b140400d856440d0350100403010b5040e503880c1545205600c07030700d00108010405400901403105c550f140da0b1074480140015221401c0342403071008000f0000b4202d40494680801c260304540c0c541d65500380c11908500c0030350b800034408035100784107142080c2303421036081e08500d410030070806020403658001070110540362160010030020b0341d40d0248043c00581071013415039a510a00041c4441011504002c00140a = true := by decide +kernel

theorem cover : BRFrame.Cov 179316546 179496402 := by
  have h0 := BRFrame.cov_init 179316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 179316546 ≤ n) (h2 : n < 179496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
