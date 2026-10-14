-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1786
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:40:07.436694+00:00
-- url     : https://prove2.me/submissions/2ecabbf0-858b-4f51-9479-1bd8b50f4dc4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 321043165 ≤ n < 321223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 321044415 1250 321043165 321043169
    0x40b0f0a09080d0911151b0d020d0f03020d020f030403020105091b01110106031506030215030709260105040b06010f230c10020705010c0908030a081812030906010609 73
    0x3003410044614540c2c0c418070588a11100302074002d03107035150710b0300780843c581c13001d00d070071400405444981d0000324442203950030200295001d003454260030802c0110201d0900c0c98804546d0141c92043d1400b5011340c0e000c89900c2808d0105542881050100d071405d02c02801d0b1112030100c02c43d10b13844c10b880c0c02800e540c801460342c2d100d074000543c0380c1062401e0a0300036010b0310003401c0c0000b5500e4804407484c01000168405800c00c4440f4100482c4440c0e56800b0b82d069078000d071000a0304808079080c500e461f1000360782c0e060008140c02c0d02040404028484200604200104100d0349107400c040b0b02c0c04d490301640c044c0c5000c101401030001075078000846140c1144182441e4659844240c00840452407020070600c68800000780561401414090280002d00700c410854954919042450003041c2295403000480d2000d140440c100038000241e50340c042250703071000c0143e0f40b50795003a421050070103040c407518480c1c0c1e0908617003c905030014601c1140c12900420066241c5840208400f420ba = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 321045665 1250 321044415 321044431
    0x30c0601090515150309120706090b06010212031603061d0a0e0109020109050411070221071a0d0e21090f0405060306071b0b072003030915040c0b03040b0f 68
    0x10b00003000f648034440c1e48822000d03001d58103501c036a2002005400c0002c141044417041400140f00c07010090580d104800a42c0600c00c03090290351410010390351171614080070004c1400900000310240d01b01c1d1894007402c1781e1843c000c182a03958080303814140c0d0201074801d1540c01070f0020095007203a00c0c807900d580c81038000007d200904240c1c0020308030400b2401014010b648401511402c3c4040c0c90844d42e040380d001d00b104080d41403040d090300001000c91405001070203040c01c000b070210307242803042d082408100e5459152240c0d140c035880007400c507103c4444050044e1140d20440e281d44940c075540b18490280005d60712a02da20400600c080c41c1c3c041c0520603483c08050001540b00007400703650041080c20305c1003000c240311000d40f00200c02d074240109081d1b48001082061a8040d030000c64540040300441400d280011080d601e0b40000c8564170110307803044001c0042201b01d41025608903000f100400324840d01c4a40c40c50455104480c00e4070914001e01c02c1c0041900000e03181c0342e11202c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 321046915 1250 321045665 321045691
    0x1020606010315030b0a0207080a020f0607020c0a0e0601090b040611100c0e0d0507030b070e01021b100c150c0c2105090609010519020f0706180e1008030c06010905 72
    0xa903c0c0d04003000e5a01000c0c1ca0071a0a20005030758802d80c2c0d0494505075000414951280c428040095880c90f00a220701c609009030004160340c6400054501010040209030003007460030300300003040101000302018100106188001403580125008202070b00b907940e2060340a19058550318a0510000c00500003645401210009a5803100202c1c0103c0c408542045076079515043c064a4150305400c0601008100d405004e0b82e6600162004441d036402c2e02a00c519060081e44400c07007207040c1101503080000500303692003151007203982d2202c6c2c40c456003082202481d8006081c00705c41c8403050740e0020414922400c014818142440c0c0841034540b4039025400d202840000c20b035008041006018070401b01300049280c0c0203c0c191400092859510200a510104000e544618403a030b010150b01440e0008640d15100301810740b450001500c441c0c80d101d28110140d1207e6a00912070000c0c1c0c0340390b41010840701d40c2032009041a08050004000b15414003040d40c003240c0025003c4c4a0a2031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 321048165 1250 321046915 321046931
    0x90503060c03060409020a150305071e0207140a090618060f080a1502120403080105041a010806130b0d06020c1624020309210c04020a080103140c040c030506010206060103 75
    0x71070001201c2c0d2100d82601c011070031a03000d10200341e0054058110340e484240d8907001c0781c103440d03255014502c100d41a948440f82c8500c0a131041ea207800c3c64810b64801070700f02d81402e010340c7c200601c4101c880e410140c03071401a07942e540c1104d000c9907529004424204400711804000e100d0b10b0240030040c00d40c0d014a0381540785841413460743c4602d0500c0c028041106c0503071007a5400e004e0760503641c0c40318442568986502d454600100307501c03001d000d8507100c0c40c0b40c100c2d00300c0d84240c0724400071122001a1600742d15500e6280820841150302c4070300c0c0b084e003611803203040175545800d0055140c8a01c154000758881e01b17500c4940d410b110f80710402030011152013004229500010841d0214a5280c0d40043d00092480c00c0890442c41114665900881c0c40031200c20404101064440441c4900f003d84030a041a4000c01069114010f004400101c0c15001407010440c2025806c80c82c03148607007140d56034681400031500f501c001c000700d0310209503200d00700586543c051150075072084003482d080080346 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 321049415 1250 321048165 321048181
    0x1090b0c01020705120a080f0c040e1510020c01050a030e0a020414041e02060306060706060b0f0a020601080706080f131b091d120d060b0408030c280605060103090c0f050109050306 79
    0x90300007007071200014034407070100c0c1c2c01075605c400b1100079000d00124800d06240c00310310020326633207080b1100d000d40e03210115040594800304038a80303261816501d20b860007503144400c80c007420141202913454000d010b0f8000040c0c2d16803290f04202959580800f40900d42414000344c0e0071090f030000c10050914035001d000607515003003240ea00050454a01e070b2100c41c1410100010007060b008483d0100c80001d800c03c100002101a080f5000c0942c210b841503a02c411402ea20b54401d846480c0110b142d0390089104001c910f008103600c50340c0032aa0364920509620f988504100c8441215030600202c3c41c140800000c82c0950180d411400c0b10b074070310a81c642e00c041a5101140c0c2c04d41c1402d090003054400f14200700f0f8004bc2c000300840c410b900c0e225a1a00c004a4503075010003c1c40d00d85120b07100724003d9004410550000b10414000440c0780103404c3d44880000d030000402c0e00f4101a50344c440728000840b0300710302c0c1001c0d0200b04501c140b003a0030b0400140044840781c0210f40f04c0d900c031504000540c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 321050665 1250 321049415 321049427
    0x506011d06010e15070f0b0a0c090e1b070f0320060708072601090609050f07020a030c08040b07111002010b030c2403090d0807050f070b040201090b0c01020705120a 72
    0x88090301d4441c4c071051035a4260815000f04800140010142140d003014032034112102da00981d0300c61000c21410303402c520140c4100b04a48a548200d0a400c40000c1c03010480d43c034500d00300740c501c0040515202d000d036070345c0d84038500318101207020603d0142d403445003580b810103544000f00100c0040031710b07061500010301070060041003001009a80341001d20180d504040700700741c004440020040558450100c00050f00a6006080100f0b28040014641d00f40840445015455039005000e6441c4140ca0803100240310b130b40c050b607111380e04010010f0005884d00090a10390b000d222041c210300c011000700032102c07812003100c0707086a040c40124080b5940c04604045c035000d003102ea103024410740b1108040d2600c2611410500c1755000700400400f00d9001c40c407850a5a440da40301246c2d80d90f03403901911310b802101c100112588041c408540028650441e42c0e80090050400510540c2d4812209146510900b102201a50086542801c02600300040d00d54000700e5001142002c02c52003004000e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 321051915 1250 321050665 321050687
    0x18091208090327120606040c08040f030f1b030e03060604050c0919120807061b0c0b0a0e160501020705180601050d0b0301140103030f0c051e070806040506011d0601 72
    0x1181105a0032080c602e01c40d0b01918031a10300600048221a81c001113142c80d00070444895000300d0a101104e041507105081440c8603da000c40d03002104215910f00b29019050030307210394140301008010511621907816508011846956082040803600041c1230501c00c0280400d40124181414000b036140e01034152141840c00b525001c0c143c2d1903d00c2c24030340c0d404107580442c1c4034401c003110401c24461524020f21f01c86001d00010b1040c1603290441400c0120032030700c02c40006107068684000510414a42600040314010202e041d030060405681000721801c00b140003500c440c602040656014000b002c001c1008513060904030704403103042c040c0f4a0009100904000d00080c240c00e907810641e0059641c0100038000308042030702000400d60418081c0020340128000c010301000c414810145109007542c0f000c0601030484a4100d0f85800940343c1001d0714950240750004114040100401d603c10360283c1c0c000c0c202c0754034200700c010348250000c2c002900c5103172000070800c050742c04c1100381c82 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 321053165 1250 321051915 321051937
    0xb0a0b0702041407081006050405060a0809010b030708030408070503070b120c0d020301121e120f0504030510020d15080318130f090b07111e0304180912080903 70
    0x154499061001400400343d07403100e0546075010005014205a02c01221445004041c4920101c21f40301ca00a84040c0258807845503c018100b0180d4480c83c450b44105422070900400405c00d1824800001c2c04c041403500442819480846c041042d07820400003a00204400e4020b0b103c858108009041c035441a4148011079284000104c3c41b0070b5646c000720750011410640841d12940c540c1d0324420341421003d805e8403036031000c400200451030704213504800e03103520094000c0a02954003068900505c200b0001d01401410300000003c034a05109001c100000c1d00801680d800c29a41c5107008c968512850010b81658075009000030310b400403c40744858042600b4440b44031000d000200303084030140e0708903000f03801d211105d54040303880d402556400e4455403541d5030f95941c1d8942120803201560b001300e541e5000c244807a0032440d01070040329a00040c2d0007074a00d0582c1312881101000f04800b01026015550f5604005104041138100408006490701300390324188490990b070f41e070160140030b40f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 321054415 1250 321053165 321053167
    0x60e0c0304110307060f0807090b070f2603060301061505030103080d060f0308030603060a27020d080a11060a02030c030f09010e010f0f0f0902100f0207091e0f0b0a0b 73
    0x15041c020701502e0b011800400404540030141c4442c0d000700002c001c54003030004185400d000c1041240200901c0b4240d075800081c4078200f0b521510345260100c880c04050f04c01c100603806040c2062802c11101d0320100d405800242d880c1411010706003100c5056106411403114004d1101040d036100040f241140e41056079980c60380444d9880c0c90040420707602041425540c404c0010030804e541c00139520401007103040d02c0709a65480c08284c240c860100f040d400c100200c5086082071401c03101b8182c1501d001415a01c44074000da03032120301541c05416034001191072140344c1e4807100c0e001c000f03c550101c0c0310002036003503041c8001c110481e404054520003074102544c0018030340420942c841c04d48854148d0003400801d02e4403d201f0010300c0c03a6125008610f040513440b000580300b900500041c5503001d000d400308990010000c0f01c458001d402110114041d800300003540000c14015044290380020301c203000001e100b1018400c0754860340ca4101d44034241440280580e5907921140100c03913600d5022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 321055665 1250 321054415 321054421
    0x3150603241e09031e02030f0a02070e130b2203030c110709020301090e01020c0d03021c050403052709010b1e0c061f0308070f02060712030f0f060e0c03 67
    0x400d0140000700003a815000c022910700e5903400032030f0450b00e80340d07000b600c40c1c0e54400421942503844000a41000004d64001c11441001851a50041c1722220252041c3d41b10707140c5513600c0125600003642e00d8840003005071884410310404c108601e400800c000418900823014640501c84404010000340915968440402e95140500c3c44008510903c4096581d415140c4201500a40080c02010a80c80c9010300c80c0c0c2c00385205108a40b40b00300d00c04014406403a400508401940c8503a850b0181007400c4a4480040202406090f006500c02d403600c0f43c450031b40300c1e0854241900030041c0c2d174424541e110141c0e00c64880359252815940760b00c100c2d40e60741040c1c1c419003044078090007100d83c034001d000842d404028004503040303006445901030402d5100c0a0b02c003e02a000c19400701502c45281000702c0f00000302c2143e50032404510203031410b410310b15640c444d20f803c500d12403540c4020a0312421b06140046030303482800001d01442004001c035900700307005a110000003c040d49600d00d000008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 321056915 1250 321055665 321055733
    0x240c0904090203030712020f0706080103120e100c02040b0103140a050c0c0a14070b0c120306010903080d050609060a0602031c1409070905070206070f0c030c05120403150603 76
    0x4000300c1d103600a01103035075442c0c0d1450b24954104c0f01c01d04690040c0200c0c0c054100c2444085a00421580305540e59a840c1c0d0941d02c4280e4000d000180d003500340000103188140d95190400c0003134212480ba21401c5015850303005210a07038020380203c0c1d04251400140b40c1e44900d4007007450781c00c140c82d10800a07050b5038003a03845031540f0489103c6500341c4642d001d6170301000385507981000f04141d814140c407120356443d20309400314001c2c01c0e1488140d81109000c910158a0f280140d54001014035001e5404c0381d40391140100f0740d002072059010f09483d1010170825060406501c0c0e086403041c0c4224017041c3c90801c000b5240c0c02041a11200d1342d104804030ba07045045174002e40420003641d5036410880c10709030230540e030b541c03000c0c420746d4011410f04001501050000c506a84104d0b25521204124820610106e81b03000038010110113100050101201040c0208102c00d019920000718540e541e0450800e400c003010322026a021761410001e043c800911000c56024080c000e0688d080c41014111030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 321058165 1250 321056915 321056921
    0x100513080c10020d06050a080f0712080913021207020c011209060b060a0203070b1006090608090a0507090b01091212031e0c0305221101050a0207050604090608240c0904 74
    0xb401d00740903001049514004206a00c0320381164000c41c3d034070440359960201503468140c07081c0420143d0300a00c404100d4210044200d200c01449030485910344441440081c2d0580b030201d1081d0302da203a0108041054607541d403c0250408103900060488444220000380f0a00c0d449441c0851182c0381c926090800007180c000c85c19880b4000c244903199090394200030b50300c0d00b15080a8412101010100d0340c00403500007180c05442042e13031113801484c2014402e58844201504144131032040c0540c3e2008030340248002e2000c0c0241075800b16006c40c0079800142a84d086421502d086551804144d00081e0800b0802a6066450402003006e10110000034000800811101e071820300308146e0200266155220034454580c0744440d200d0b4a520844080b050460180c0007041d4401c2c01c25903511130340c01030002d40300c0c000d06441214101b03900e130000309070280c10503132244084907207506041c407500c001488040004550304c030310000300030791006101c035590b0005448140341100000380d41000f03071181c0d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 321059415 1250 321058165 321058183
    0x6240105270d050109060e0706090807060503190c0c02030706092d05030f06060a170a140f0d1206061817010b0612150102031c05060d021908100513080c 67
    0x400170028010181090405003100907a84240c80c042c404000c9100d50141c089902074a107241c0080c001031b414800b040c5ca640d0300180000c11004694048004800f0181c000e640d100d504d03903030b1404100c1c0c03020301c107240c500250b40e080301050043c1441c05005043c0c1d0300c1095042980443d880020a02000c40410712a018507001160140074105c00010b030203000241c1140580425103800488540e40c3c140c036546020460100e02564000b0031141c00850ba0a0412290610040c0141c9800040c0d100340e040c603056198900030080f030341900070501c42c4036862103240300030965810401c0340306500c4200342c100e2160038002c42251f030380301c1d0141c000f600c40c3c00d500004200401800300c5a4030074454480d8070305603404841c1e1180041320300300c40f40c015508c04000e80340e0311200644420300251030540c1403405000c00406843d0042c843ca03000b400942d403801c1d840c801c2888020801090035003004901410000201c65004509041a00b4400c1c2000304103800c1441541040f60f4a45490054201e642010f11407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 321060665 1250 321059415 321059423
    0x31e1506040b12010605070206030403080a110a0c02180609010509190c090513110904020d020906030f04030908010c200f12040f050a030c0506091206240105270d 71
    0x1040c0451607603045001403c3c41c410304981c10b50300781e1381c40720304684900c500103009412039401c0c404200081d0080e184603421202e152008a400c03020300042a205030082e605140000710b41340800303015410410501e003401d500601c100c1100c2e20300140419400c02041c13144500607800c0d00f00040e01800c2c5150340d0170714045032040600485168030740003405007240b8000d103032003040700d444140c011032090b100e000561030102020606045030b0340308220094103c0c110390403441d03800300029003e540d2040b0045118180840380d88010b401e15040042003104582c10840340e980c9000409510140c1042c2030010105540841000e0458004d0b0a941040e0041c2d0303400740203101c0c1c1d20100080b10000340c0500242d0315210b407071008103603407401000112242c500c000703488000100c20600460900000030500c0c04e41c0540110040f90007d000305180000c101c800e4030708000210285801ca0b0021041111030041c2440d00a08000d00c03002c2d40741940045515150140300e001d4031144c6a5103401451808150b04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 321061915 1250 321060665 321060667
    0x10110303091501080303070801090203060d05070b0a090b030405030304020f18041110020705010e06071b1404060f030b060f0a080a0606030506060a0308220e09030c0c06031e1506 78
    0x15070442503035040c0c030003885800346030b081002258039400041a24800e081d1a950300805903c0d11074808020750001e440c454101006e40c0c64140410020132034440240300320107040c1c0c2e4070b00d0018401400310f02c5541080d00079034030400a00c40815000800d0300d4001380c041b40c0120110b0185000914178164410140d089504c1040c2000103110302d00070588036000050b03c840325010840c090883c4c40303c00c070b07010355030124000c0f00d82c401407420300310081c260903845031014055890394000c00421211580d4040d040203403d034040c900a03400e0600520f8002c1216441d2000201d045603a081540c01c1c0041c0543e01540301410380c00390654031070900d50b004080050590b11074002d141030142c00b414460100741c50908c01d150100b5949c0c01e003045060110384d002600c0c80d042c11404241107600749070800000340400d8a2a00103d16074140504a17070082000c5401195540181d42c50181441103c06826104030401e004101c0d08103442007020b0000c01c43c0c3c000004281d43d0702070340c0c4005000d8800f600c1e900800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 321063165 1250 321061915 321061921
    0x210c06080702100b0109140d060e0d090905060a030b0907090236011e050c070f060206060f010e04021605030a030603020102070e160e030c1306060e0604120210110303 73
    0x28001848034061441c960a80d050501258294002c2c1d44810034480c2c0002c040740c908020050300d03a0000071a03500001c040c020784600710307211641540c0100d04141800c0c0c2000010144407600084804000c101803481400b240c602000040c0d408035103440064082544400041c020510611058000d4480c1410031900e03080000e203084155566180b00500d0341c0d442c0d1280134903041c1e0285005440620581d05d040c6030302d4143d90080b60380b84144644100384501401a401640b80600400b009031003103a40c0d40141901d04203000740ba14001030b2200d0b0203500d41c01100e40481e6071140d0f0159440c84241d4015a540040341103203a601032017104007500030300021540c0400154103400c8241181e000364200d50459031a80350a01c440c14082d50801c0c01c01450610b080482c07400341120715202c4030b00030f0541d00f01c0c640ca0408240360700d011652005480780e40e5031050081c00d030880031500c503052081d201d4900746400c00514540800600760040d128080400300d1410091040e004202411151000d07291242 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 321064415 1250 321063165 321063167
    0x1110a0b04200414010311120601060210050a0b01020a08090a0504111806160f1109040302011e0903050f0c0304051206190203040b0a09110a0308030a1a0604210c06 72
    0x780ca10860b0300c46281e041c010301030076142600862600c101c0c0041011150313440d45e61f03a100c41820715585207400108055004900388004c0c00054024901c0d500a040e00409001c4040d084600042440c6051071800c001b00001d030b43d000940441c141e9100b014159501070880008a51129551210381d00c142040e07402d28000b245a40541520106018013016035503001e001c0100502580e0218601c24812519041c00709402107000c5000e580245101c11901942002041101c0c90840b803c0d070160391105040440341c25002c8034a1340328400b080c02080551314135600188184650f1030350540c0e40e040410200d0981400b4401c580041c50300400d400c0c1d62407403103501c0e261522821103400c0c0c00202c034a561034049911600072031380f249500104105040c0d40b040350704401030120420507540e080c0710740c1d941c92203900c8203980794000d140188c50060301c9160a24082e02690b40030b030074651044003070300d6074141503495002c00c1d02d0554201c4606850300d0306034103000c403511140b0400d010f8030801b401c4500042e51 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 321065665 1250 321064415 321064433
    0xf0409050a030e0411180406060503010e0a0f090c03110118050a0e040606051f03230a0e0a021c0215090102060f0901110703050702090a3605030408010518061501110a0b04 75
    0x141d00140d47c00c1c0161555440309070751301d0000348910841007042c80c0c00150309158990101c0b1031004071410000d11a5850f0300c50140c13440c0c03d03400071101900142a5007440c1e40c1c211a012000c0020100e60603071060410303000c5102165944212030010311945d000c02e0410041d03400c42c40c003800d0003805a03c01d400a480c10140e4414070480280c001c80d1038104100703844040e844001401141091300d5905d142c81d149100c2c0004e0241c01001c030302c03d00a10030302c0c0700160f0341c0011007000c41da41030825a007020100c0c010006c220010180d40c0c0d0201d9400c00072160166004030b007003503200180384842419903946505007800351981006c01c0d02c0a400000d15441090380082c06099110b000360391407400355951001035421540410b8007800c2180c00f881a09028040c6441c10382c0c05141825003841100025688051454001d500301e615640d440300100400140e03509030714440304140c1c0008020034241010104132500361070341614100034850f848410603040400002d01a542c0c00f851a54017854242040285 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 321066915 1250 321065665 321065707
    0x90c060c15040804052d060d1506120f0e0604060b0d0f05030d0c08040c0b0306040f15030204052d060f19080c030f1917030c0301050f0409050a030e0411 67
    0x11a02c0804080705144a5407102e20308401b0500c02c111500700010020008990081d03018024159110024078004050f002580c40c01810280c4410100104e01004001518003880307080401510744085045444000212207420a4100354002001d140c242d011945c9252038201c050f02061058540b00b04000001000305000c00342580b0411544400754070031182000709803405071004400c281c05100700c500050040d50451300007440040c3e01889032035840300b903403000a1100e204015180381001581840e009181c1d0100d612800700c1321901c21150b1041103003207e201c50300142c500c03100000d000e540300c40250ce68840c01c0189001ca942c940d90712310a248100c1c90140c0c01250213005107400007401c0000b0b50441e81144940603041d9030b400124a04016200b204041d541c40030740c0c544480c0004030541c0218000c4082200c03040e5658100700c288080f41c003040081e603020b18613184500001c90740c04148442141d5051501c92000d070b00c2540094003a0030a01440e161140c0300040107262030700d2403260030203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 321068165 1250 321066915 321066919
    0x3080f0903100e0619150f1e030803010308030615030a47031c0206040308060a0b0405040506190602010e15010609050603130602040b030a14090c060c1504080405 71
    0x2d44410328040040a403600c08444141c594440130200300e201c01440310300080703100c3e41c4000092030a08030300d004214507101c3d0b0101100d40350b02d4800380002501c1da00d00c03101d00d03c00380c039031a100b040c550394440340c440c4014032000e48484000b00104007a0360320010310003004000130b0640c94581c10240400350040c440c4003240f00d4191450b1480400c1c5103170104015403c000c03400716400030b54a540e000c003030700701008405c500e616001d001004119800c001c6445942d500e003903801007207507140514000d00011005403806208100e109400c00031300780b0000c120790648409440c0131540fa1600d4010810f50014214081040801c1847c045000e41e4151f0200042e546028112076810024076044021480b080c0120800554035000070b00032404c4c040010358204810450b2a101d00c41151946000c0b40c101d6008000340c1d60001007807018200080c00340e0481060201019030442c1031513100d8030380d41c036990b2502500443c00840c070403180220070b022a50b504211300700805045d282900c2c15055a41c000d00900c1c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 321069415 1250 321068165 321068173
    0x80306040c0f02190318080a0b07210b0303070f0501051905040b0f19020703021506041803030507051e0d0e0307050c01050f0714010603141207020402030a020403080f0903 75
    0x12900a11a0300402e28200080d00501020045007500103004050010141d05000300d400c4c010400c1d50b610083c5800400c043c102420343c0840c2c6e0b2501200c0860050828810451040741c0300303450f00c030f070002c060f590700740325503c001000c0c01c01c040803a06500601c0006020710414983c0602488810f4120138414030746040f0a0101e049110304080490380152000340c0602c130070500161508141614582d000200302c1001000c51020a0000301683d0010400b240180c00c00544100c4503c507a41c166a00200102c605000034908130003c2c19851802d0003005d0105074503a00401d0259003d001150700b0322100031000b00c20304800d8407040145a00503c12083c80a1502d03000d0b4a2046010003607800d0386a1180c0900700501ca46801100e09404c4107841061007441045900002001d001e01544128900700011a12900e541031120011070422000c07803290304011008081181c42e102101c01150781181c00503120f8480c050034038001e0040ea000200308007800201c6815581c1844003416803440220116 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 321070665 1250 321069415 321069431
    0x50601091202040b0a081f23271207050c01030b100804083c0310060c0503041a1b0d080a05040f1b03020405090d0905150f040308030604 60
    0x46420500901c9081c001030500000e5600501e0160406030841d90020300300d04800741c481c1d45450520511841041d202041101031030341d03010300d03030180f444140300040c080c505079401440e071014400c8004094140e0040140c6803540300070b081d01c0c1002403100305901250624110004400c800b0743c01194180c0b17040c0b04020842400e50302ca4040c0180b02100a00a19030ba05280a0b0580c1e0700000504222a20f80d014072012540164140102c0145003410498044400448107a1030300c0c00310409100c816240108200042200341500b914121541032910100d02c40460520b141140655005299040c0b01c0080d118004164100505030450313242c58107c0000c1202c10703059a40c2d00b41c50070b82c000840c10305000034194101c6a48440d80c42400740482d8510a8115500d09000210910301e940103412040c05c10f00950400b48900caa009201c000200356602034200e0240c0580814410248600350009031910070340383d1101583d00102c40856400c0e152622481c0c1031240707800444603136000703910700162 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 321071915 1250 321070665 321070667
    0x603020904062a1701150203070b0702190602031501140901270603060e07090e0609040305070212030309010e0609060f1305011e0c0219021c0203061819080d050a060816050103050601 80
    0x6001b14103059800552901446982d10403488500401110a60007022840070507048042542601300d80304840040e6685003412681080120801d00b142c104480080e02c45041c045800448080c14001d0030506240e80d910740f25001e0005600c803851001120107030b00003800795010303007012060310303404031340450070340d6950404403254a440d10900c0c1c040c2c1d1444012984a050140069030024040e180540c0342140f02c1d0049108801003c080d0f5010b03600000070800910002c1c0300d01408400700310090041400c040354503555460014086180601d110004520410900c0860216440c0c0c850000e000840203403502c0d022806a10b034400e1941070a03e0b00801006201140d0380c40c0c00c8a24004c3c1000161990302800b0107401291288842104c10682c8140980c0d400c2216510544040b103c4801e5001690384182c140080d1032140c90210344c0c0c8418200002e00f410701074a0302c401d046030f00001c01d0703a10681244082c20082e4452445800b03081060881510b00d00041e01c00da4100780c9043c00107490b0400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 321073165 1250 321071915 321071939
    0x30c090f010605031005040c082211091e1305070b0703170613060b070212030301031e08040f0602030307090819020f1311040305010509010603020904062a1701 70
    0x11421808000c03500188049401400a1030700304040285013504175440d60045401c54100d207600001150324241006882d0b01102d0400349905c2002201c208400c84941c0c8801d088403540155034403030900c2c40300040d0011090060895119003e49000202c0e0a1880140e5090403102005864501510201088903075980003240c42c0b4941c140c1c0c6041000903050106c0030280030141c0100d9101d50040001485400e10340a03a2000c1c20300268000c1c0d0b64402441040702455903401020600d8005000401c007207016148c00d10741c8816a140da1740c01901452030004844d2150f0b400122003440c2c00800801e01c2076000000d940b040c051a181d49a0f0385072902078480d41c901030b81c1d5801500d0b207100c00703000c4014106141034030b04850001c1c1202000c2080742c0440c07002d41f40c00251a091100d0302103810828090240074203600b04501000810045045801040e00700bc002003000c3c080c907171245d002c01d1182004c040b002180180880c0b4601c080400c455000306980d1650b125105100421000800d10b40d0b8105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 321074415 1250 321073165 321073171
    0x19080c010f0e1e06040b0d150305210c0102030406050f06030601030b01120204060803040e041217060108061c03110d18150203040b04080a0209011e231e030c09 70
    0x5101e90400790042c5042014160701c00001c403c0e00c2c10200300b100040d481e050040d001410070315061588501149a043c8100c4501107141d5041030807006040000c614007040058030585100c2d101500c950880103c070b0058811403000c0c0c11191320002c1000244511740e440f2030301940455401c141a615902e040640c1d4140c28040a00a56459801040303d0303552400f20001e01c51014102040295440520a007150480d9110762042450503080004116551400b29260704160034101d401514a00720080700c201c00805148c103102d400008070318199156009800401c40190000b0907a00c080e01c0e0081c580c2c0c201000c9222540306040c86810703600d02510340c10754a0210004c0c2c5c41440c80c500700d11400e1064140c5124070550008000c0801c0c40e0340c100b0000c0020308642c030003d02d80c0e52031902c14800040c1c8140d04c0070390040c0780256160104088040c240c0e00b00ca07039940b801101c005a01c141002500001920954000e10322003d28904000000130603103840d030101c040c1c44618444405200ca103480071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 321075665 1250 321074415 321074417
    0x109060b061c02090409020901030b040b0907030c06050a1704030306060914150702120604051f0b100f091d090d0302120708040615080a1b0b0403060b040b19080c010f 73
    0xc2d0341d0034803899140e501401c003201c0018804640041e0540109400000c2178106a031384140480c104014003a0f28000c054001000c00c00512285246850300e01e40b00641d4010103003042000034540b003189200300c9502d08451604030340003119040a280190007004031744201408501c0003040040c180c20910041c0103212800b610030465051000f60382c8016900006040381d00c08182500061912000c000e12132046205400401c0e0041d4180527500d0500101e2000106081c205100a91070380c9902e084506002d400f4180092158814803040e5000a5136400c10216000760b98a6106100d80c2040c00320300584129055400083c881c0354224103078825009840048614040840d0311248510152903105002e440c2c0000c403a00c0003110241d040029034008849035109030010f85c1801104118a062804001c13480403815140000304003c3d80a18480917004650702d100d1145241c4031504400141c0d41c00408032610f11041f60004607094200c0c0c06048003034490000707820419401407541008206d01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 321076915 1250 321075665 321075697
    0xc130501021609020304170a020a05060603010221061305130c0806060d150e0a0303020702043603020309090106091e03020d080903010b0d060b030f0a2a15020109060b06 74
    0x41183d1034000c1e60015100b15140259400d440481040ca0380240c084100309030302505044440307003402d600d01940a8507152199104110321000320500d5054000303419103045584d601c1d942c4a100140601001c3e40082c40c2d42c43c20728082200030305000d20300307460f2207110f00c141040590300e4041c0e1070b556210403280a1f03049005003413080003280349015100d03060090401d02180c103400c409000d40c10031003241402c0780440d40204480c8114981401028042c1d14607141c90707450100003900104000d51a66a000400c02c890004441414420300441d8844100500030f4205540c0d42e0a00410a00312813180030000c0d045080c4030003c001c5141094001c80350000c0c4072444104032919a05c4c0310340e10071aa07031581036596090030142a21010501038105002c0c8400082920300c00c1d042c9410880e600d9408201c07a04170315418070029658000301d103c441403490029603d21904820040d08000c1d98000c110301441280c440e0420590540011a01c03a200e008103000b2500043c043c44a58050902d1500355122 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 321078165 1250 321076915 321076919
    0xa1e090b0f04080d0903020c0f030604020a05040c0504120506040311030f0a0509040609050a05160c0f1b031b06020106050607052512140c010c0b0a110f030c1305010216 74
    0x12a0005070420301a100b06481d02d40018413400c1210300c94002180503070840c1041c04d101e80307008040c2d9081000b00f540984410b1a0a03800036280000c1c80c09580e1080b65100c00c0c41c1d50340f5100740141c401800c0c00c01310306042c402c0b550030229541c9208603004c5001031400c1201c4045001e021081d43c0c2441030103040c0314100b40680100791001d4004000702a00260360f600c0026803441c803401210b00490542c0300002c0c2a080080d41f00781e05010705105101445412042c04c0e00013280d1108402c441c87d0009000c00c0f2098070800180f0301503819620150080914081c2c90440c019200041030031542c040e0020001280e880c2c040c03003500c1c028003070301038000d8121004407400700034041070080c0034000c410f2051207210f440d600d03940e48200381c2000c180c03070140d015181924400350401111b030f202582428002d60311403684e80d54141d141c0d070003000516004c1d10342c0100f4696000350026100b0100c202c00c1c0c510b849281ca054521107640005c0807407445a80203440000f015400850424184a40030710554010380c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 321079415 1250 321078165 321078181
    0xb03010c1706011205010e04140304050d0b100312021c0311073f0206130c05060c0a20090709230d020301060801020919050a03020d0f0b0a1e090b 64
    0x1c00600e41d9040c0030207401883c1000d02e1502c1404e010700229062403c040c20030b41440e2036581000745c8503c0303050b40b003000188030300c1e42d03200000c85032241c1c0213494206507900c40d0031401841c0e1440d84010710a82c0c4060050f1811500441d14880f00241445044901e0350601d000301d00782c544c5d80744a400c1c1800200840c0f40411001604200582251244042e0591000160b0f94220320703c3e10340000c1c0358858070358010085506020850300886100d6586590408640b1440b50b070b13038000d22400d8815400010120b400440501ca15840e00340c004041c0c683e41303615603010705071805188441d103115404820000c3c104134020a046415100d074030020103000355007107020b4040200005040c40e40080d01c2d03d1481f0050f9800d0140001800152001584400824040c03104000080088010301e05a0381c50034402ca446c1c0c840c4c89011a40c0440e00b08505020300c0c00d10000d0140341500260078800400100140c4406542080100c1d0303400c0a51006100070090405044850034500241108052000b00e0420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 321080665 1250 321079415 321079457
    0x1e0c06030414010b03060c040617090d050a0915090e06010201051303270b071b03030e0607020402090d1a010815060904020105160c0f051c1b0510030f0b03010c 70
    0x942010b0300000359102c003c0300003032070100100d03001c4101c0d81c0700090500c05694403841c00404504c000f8481141c0e401c00b10300031078031245456041c1c010040c0200c0d030800d00610440c02c4000419004c1e80280c0c0304107001000400c078010038024540b082402d80082180c551051080380d220701c40141109500d0102564100d072805508400100703c19049442c1e01c1c1e070a98443c0f404002030844145003583e0740320340d103000b031183c20145051850340c8030031103405c0000c20380200c901cac10000c00840349260384c0da84901c0010000d004140c955504103180d1607035042000400008e5034507903001e86205500981ea2511600d5403100d1000e1803290607020b40c000f0851600740307240020780281c4141131460030081c6202c0604038072001d0100944010018401c00c2100c03a448070802e0700601070513105060601000351560701521800c030300040525405018020a205800300d034903014100c010006c2040200d890401406880d5a4003a00d684500d03100c01149035180520031072003803100c5170300d40503401c8032090b28200350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 321081915 1250 321080665 321080693
    0x40612030e120f0f01020d1d07030b0c13030503071703012d0503010213090507140f0a09030c09020715021603050a020a08040e0403020c09070503060d0501060302030d021e0c060304 79
    0x109204001c0070b5203e4050070b10a411041c030101d400103807500342441010056841c003801c540b51140645e505040e904402141c240c0640790402c84d1300e201502d407d11500d030b0510654500c41089040c15a012081041c0030000b4590103000304000031240c80800000c02c043d100c20310900041e690a040382102c81040d0415803452006581c440e1a10340380e4640110742680d11030807140d5a403681c40b079410702100995125564000e8268a8400940545180140f2581c17144245800000c20301050101d050752261960801031741d440313901d0804040e550301510001e500480c03006c81d80c5121414032080c0c1603c492090318480400b070b208807403010300c007510b0a84050b0b00c01c96250086029081d0050086510b190081005009503078505060f45000c0c00c009080c40d039545080307441111303204180040c8981c010203594004174100c4001075100c0103490b00600401c0250300094040c050000748a80703894000c201c581025070b5848000e0001c5000e0702c5ca2507100c010901c034265000c4020b10204012503044011200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 321083165 1250 321081915 321081949
    0x6090d08130c0803042607080309010516050d0801080111030402030a0201050f0d11030403090b090f0405061309050c120715030f1e0504060b0103020c07030b130b0114040612030e 78
    0xb0495111080c4a0565001d078101c6201d006510b040c5092451110700c0e0b0440c0440e08801620300e5609140c0c0c3c05480e48101a0720703504004003c111120080b001d04c03805149070740e0150444800c18520300002d40704078400d1091641039440e000048050310f1111003180d218540c020084d04000e2615401924140c00c6001a030740044010701060038505003c2c414001c200c1000c55034640c6038503151400400c4648903030480400c0020a01a1030240d0710303906a0007804110440b00480c041e556000030420f03c00421443c10b9549007031806c0e20703042c40340214080100000c01c1e907007a42040d071044031041c2e0341c81081c0300324060501d2448541004601c254064182504001d001194401540c80d0ba0b101c0300e0400b105403003c41d5640e5040c801004032610174142154402c0c2421344c01c00711005c01c0251140070070701c409420042190006403600c0e00800155110942c0038102c10010358442816004011400e41c40034000e900d45807011440800000c1e4078014a540344d617a03040c000c54910180107500242e250131003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 321084415 1250 321083165 321083183
    0x2070b12041e03021005100b0316050904110c010b180f1003080c16061817010902030a0b090c0405040c060e01090906080c04051003120807020c04060e04030206090d0813 74
    0x40101c141403184100b150080c2d008100c2540420b42d41021250041c144401d1107003040c1c1c00708252104642078950007142d00c0c42129601400010070f40c0c0e6885626280e0398401c2c90010483d1902c1c2514000d49a04212103001304034082180c42403000006050400800000040d0001074000349003024081c3d2050140c070885044130303505c0d030310040240c00001c0603840035007025441e8581034450040d04802003155160000d043d26402d802480e80140c0b034010710000703642c43c0c0b407035207041c81c001d4009086080d03018044032941303501c5040565601c44d003030b29150781e14007030170302c00d114240740c41d005440c02150001c2d051201540380c08402c1d111110160010b60500000007070000399080d03140f00d504002c010000203081103190060070002181c40051010010035450003040c004a00700000c1031140f083d640c180101039880d840000e0340340080e006100e56000d81011000f00e00749405903a2140110300c43c0c0c08440c1c4070744460000c2a21504804190780000b14094001517590800559810405010b80800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 321085665 1250 321084415 321084443
    0xd0305070f0c030c0b1b01060501051b01060f030b043c0323090a060c11012706020a020108070309110f0d05070b0712140301260f0109060c02070b1204 66
    0x4c280b24030309640160703580f44010030315034510145480040301c480c910344001c200441c02d0100280c2180503140500007915040106082d00081c00d50045000c1c052080c0f141d41001e5591074107900110080745c089030290030304105c5c00d0342840616142603100380d1260546510b1b00450400f109244041c1e04190700b000316110560b400358096800002c10824004001a078038003a030010704c18086110340c07101c0104062a110a40883d005505681c401e500920b00703024040c01044001c501c0d20400d09400070400f801010000e0550b800181e041403140c801c0e203c043d0260303038100c400c0c3c0840e0304401c000f9200707085c0140050708914000452002e980e03c0104540a041c009031a95490f0032800d401c0000e4060000511005002c0c20300c1e00c0b500307658000d10748044c981c11440c400640c9800188a01c1d1102d0104607206082d401c0f04c03a120384000351140c8200c60300b100d22140500d0103801d214505580c42e0345000c0d030074000907102040b40c2040d111171561091070010302d40c0742c003481d20310010300030342e01c0710360300100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 321086915 1250 321085665 321085673
    0xf0423010b03162c040b25020a11060406050d050603070314070f0617130302030d09031d0a1805090106030f03030b01080c13031103031204120206010e01060806040c1103030a060f050d0305070f0c03 86
    0x2100c500a42364020881e0751680d00d01005041c0c0600701140c0300d07800a1101300940c50f0700800b1261161218000401c682d201c2d84007080c941050b0750001001c2c0c880400b2001c1d408800003a100c021105040d2410340c001d55107000568520783c1c40b003d900d42804070400014511511840c4e40c039000d910a204407454809154a100d0450380404001c5000070964081e09045c840016008808210100c60307110b05e007072400d648034005a08034010701142d00d844400199001c0800e40c031030b000071600100300f00390707184940c6070040c0140b000199a83c04245030b40c0118904080c907206494800900c03403219561141551210441f00c0400c0d800590701d0305c010400c4901c41c0d000220524001c601c00c000e11003102200d518040e0500f00140c00881c0c0034007420004100c40ca5002c221240c10a40954002407901a9030030100c41782400014410000c2c400001400a00042d580c4079000f15064140c80e2009291180200300703140040b00340c0600011002e0005c01d000c15029014012960b100d10481e140040d41c90391 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 321088165 1250 321086915 321086971
    0x10e060301170c090603060412020c0d06020a081e01052101020a020705130b01090e07020313060801061101110304080c1009030503040b0f0423010b03162c040b 70
    0x100442c001d4070082180da0000d0200207400c40f0780c2089541e2895440c018010a1351040c0c010301c068001c03144840b150004900030300c030964003104d01805144c1e680d419800d007180a5800303501040000381d281c0c00010340035156004417400480045603003603203e0f482d11003002001590520003640000200108001c480300901c010910061160054101c5a182000b000010340ca0b15209402560504520740403070380e88140c1c1c3c40e0545110110903115030b100c41b50304038a14098812480400c824201000c81c22680104080f4121341055407042c0180c00200e02c0300d8241d851818000b15942e03024400b0074006000d0002500001a06004980202090000040c00c3d1840c0c9042175004c500000140400d0004456106070301940d4240410b41c0c17400d0680c1d034004100100d035050610a200016129040e00007900321352203003040201114501c0c10088544114100d01c2e104000c200f030038090004400c40824099101c8100c503080c4981c5141e961515250803100006250700c24030352071106410308445d2000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 321089415 1250 321088165 321088169
    0x71a1c0b04150305060a0207030c0204050708100803181011070b09090c0f07060914071410080603100e10050721050c071e020d080a0f030603020a030f02010e060301 72
    0x1040800c0c016955000d100c100e90300e80b9802082e502c90340100348085180000c1c05500401e08280c0160b4076812070504850180340c0e0440258030600b4a824022500c0c3d0004546000e0050703103544c05411079450211030740d40c1c42240410861045400e030010150302d40070f00201104412400d1041680b40480081401c4c6000c0e500120180c01000c6989400c2e4101042c02c01d0b480030407072160604d40540420141e032580a6207400511654460500b00c042003a00900f9410840240302162003e079142c9008120a4404030102c6016810403035098003400d200c3c9241500890014000d00b070030103034294085001c0d0158908030505071041002110304140c9034407510b4070440581e03446205a100740511100201000021075100504020a0001c05200813040322001035004807800f4401c0d1155a0504444014010182d0301c0906100c0b00001d01c0784246c024206001e20b81c0e40d46054010045040d0708440300e5010107500081295000c0c030000d9003c08504203068014107100c030103902058009900d40c0c1c070036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 321090665 1250 321089415 321089467
    0x1e19110406020606010c03080105060307030b060c030901080a0501030c03140f0d0909181205070218090a0213060f0303032c0f070b0711060306060f03040303060e1503071a 75
    0x9020448a64103003c0300390400070074039011444581d00c2d28020005001801014481c83c4000046001940654014071856401070304594642000c8140b8039240e03000302c41140e000c030f0031042c00030702d5800d0584500e030b050306c0d4001c0f080f039080f60840c1c845034081c001a2402c4452031062441c4500da6103c2005080b40c00c5c0d55907610080d80742d041c068140107407401c7c40200c000301d80a02d054000043c00806a4400c2e0716014501a6104c83c640e00009901150006844039075074070780c0050201181011a5020307040c1c0c002d89405000741141a02203048502d64030448004080720901840020b10a4200c80200d54039041c20b041c180700c5001d20783da01d181004a003200240e110340407800c899042408000000c0515180c3c007414821503454410044070400e42c018816030002000403000d6550000f65900e5139401c101040d1a485e16140c050300502d00b5000d202c0e081900c400c0018528800103c02c0c1001181c06000340c0012868031440c00c01415030407002503134540062056140040d28003100820f21041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 321091915 1250 321090665 321090667
    0x120509060a05041b03210507051b060715050f060603070c020f01171302010f14040b160804060302070b01051c0308060a080d0c172713180303050f1e1911 67
    0x460300500c0018018006c0072414800284801e01c00711300040395410410540e80841442e104078500003400038403401400510107001e040c21200f8403030056006504c40c2c00d80300102200b94807040c04012650004071030300c9c00014110070221006081908010601c000c040c140104604a0050310a040d800304507007003910304041510b40070079582d004207502c3c0048101d04001d0f82d01c80110683c0300e540d100b1030207a900141d00c0080d00000b050440c4684802031030300f164a05403103940786c007001000b03980420030a682422140c000031510303141440000c0d4012900a007641c4a800c2c190b5400c2c2c0c0c0d0000c008142d48d80c8084d4012002403840006d100302d0740020182d944e0801d880c8000e01e4086c103041046010b04400c41030034400c42c264080109800722000c0d0507003c1c410300c504610000500c14548003c0a81c45180c1040c5900759800b220301d000780c0e0054442d440c144041da0390807280d03e0061030215250380e01c007088006a40e182410000d0b0064020381015152040343c00900c40780000c2e035401031104070302070308 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 321093165 1250 321091915 321091943
    0xa0305070605340308060901060e011b080f03090705060a09050111070306020c0d03060806040807150b22050a050601080a090c0305030a05040317070803221a0106120509060a05041b03 80
    0x3c2d002c021720307500c040c040700c03612a00d505200c8c0040110540e4074129040c8098032812150010b140250303403185941c4043c2c440d540c0e030300303041c0d240c1565003013030340d00e04140c0c445c2ca031001c1031030b1401c0310659218680310750b6101070a0f4075080044a00c0040ca04a82100b030003060000300101d529030004000321641754000301403a4108142c024116082540240400d1b08984107100001e05000300302c0d0076158003d030502003180c2180c04a10001e2220400c02c0398441ca4418000d0100b003009102000e9200d00c2000402c60b660340d0161503400d4034402ca87d00b60008d441c0d4400a4081c140c2a84400f00490060714039240842d2a41d41d05851544946507040100700081010000c100d03000f20701c61f024070801008181440140d56841200307000140552183c80c2010074101d000d00f2903846540107240c1c2111107071584402d4101c0c4189803050a002c0c4000040e0008003644140d0b00078001c07140121640c40c0180095aa00403075400105000b9100b1181c804c1d0080c80509031418541b0814040e44c0210081a0090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 321094415 1250 321093165 321093167
    0x6160308061201061802030702191104060e060a09020c0c090c0414061c0914150403030e031c0209181503011406030a020d0222020d0b0a03050706053403 67
    0x285011400020b03503814241c081c03040c000b4507400c40c803590170b00c1e06015880382c407a2072050307040481c840d5012203090308404d0b5140c18805c0312000000800010344003000029252079118000c0c000c04c64007c0e40002c040d840030042645264018107040028105642a180032500010031000c4c05440c50390a8060100b82480344450755414042e0f8107208441d02c074504107a00000c1d0804915400c55400380b01d58442c079480030320864998403d00b110914042d20900c000445203280b000c4020345050700001d00c1d10100000c810800411260a428012040c014032084241400d020354004c0902503040b4031380e04110740c02c00c860b4010041c0200e201c12251054810b00a00749802c484495500503803a4001c0c405229490b2004111140c080f501a0f0f440d51104130540007051541503550404c01e4028100306070076072414840c2d80941011200d0b810140311002041d0308004c411006800040c20681201404000744c0340201d0040980040d09040c000b40c403055088292801c02060000804000f4070860640c01c00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 321095665 1250 321094415 321094429
    0x14130b0306120319030f06050604091d0705030c040f0605040c021b010e0105040e0a0608030c01150e010510050a1b030e012003030a09060905030310030201110105091504020616030806 80
    0x40700402c0b00541c2010300020424039140d00030a03010081c1603413040b0804e175000060f080000030308000751282c1e503181d0351110440b00509000904000c51003010580004030791020669a00711180103000381800700600e0b040100400c0f007541e40c0c072170f616550f0034002002d484900500c05061b00c290060040281001c1b290b16095007801020b0341004075052744000b00c2d07a0848103a4042e109080c11280c81c1e690380c10700031002030a003078109100030306c004100310000760015001280e0101d040303500081510342c0c2c0d0048034845202070048550009031301c56001c000300c1c07040016011284032840e0003140ca0004200700c802001d041e28003500082c0f00000e0110255805c1141ca407906803410f00c8417694050500c000d207440c0d000142280750490746610000c001c0c001c490700600901c54025068a80d84e00708051280700e003002c1440100e01207101501d07030011016041c401c0318407075450040541683c6415a000c0308043c40c0041c000c81c6c1c890401c0c005410f20080320180a101c00c0d11944920480d800c00c00100048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 321096915 1250 321095665 321095689
    0x2070803091e06360901051309030c0c0803030a060506090d06020d090c0803030105040501080a0b13020d05010c27050607020f041b090303141914130b0306 68
    0x400d510030400150075031a00d86031910092402c007240b010301580d00d00000d600b07109441080351100d503400c4c001010940c00c10b05400c0d00c0250386520212030008130003400200102407040517403043e20346070809a0b0781c56070b4101598880c402d240c045c0740c80541c3e58504103030803155002940c0c030342e00100422800d20301511920010300400c9800c0b41c02d1002450020314a20310203000240044e03004600f40c90304040700c2d08a940d50343d50001c1d21604541d150182c2940ea0f410920580b407160742410000071b07415102041440307105800c800031480342d980345400b9050010803c0b00c220f8200d24542004008180300f8460b134281d411541e91944020200c0006c025007041005100e44c1001110310750801040d500e0360300301d401c0240d064035800103810650300010000c180070781c4151003175000201040241a030002000041c0ca1080d2500045038207059041449400f400762806412101e6520300300c8014090190000c44110000c04689414640000440e00c041654015105e4030000f2062100514004100c1c00c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 321098165 1250 321096915 321096929
    0xb1312140307031a060409090501061e031113020708070c06020610140d06060303020607021b100305040213060807140d0b070c0f0209070f030b09060f040e1509030a0207 74
    0x100800801080416910010b000341c400d00d0313620040510140d2000300c88412030301d001030030543c85683e01c0013004081c040c2d450080b58194a0002d020900c001c40c0e8071246400102d404170049041d0840d07484007161030000340340f80d901c10750720340d50040c1401e440d000a01c10079120300c0340152103070001d01e0440780c206402d0300a0301c15904007400b08001c020300954407800f1104c005010003c110800000f0406500c603604001e00942d04090020007416000501c0700d0048030503030708030303110f10b460a6400e580360241c5050b4180d00844000381420b4452007a00525081400144520310660740407a011044592a62045106400c00e400811010462400c030700310801080d2920454a01c1e990f8881052000007446002442030081038481800700800c404103000f5405040043c850420320b801a142405006100340040c1c05c1040100307040c2000041c2c0f038010724015003950b0100108004000180c0799200307402e5070b00d1080824201031141d03000c40960145d500c0801a40d541c0c2242c00c002030803d852500014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 321099415 1250 321098165 321098177
    0x30d0806012c1005070b01060507050a0f020f0901090c110111091c0501140f070f1d1201090807020405060a03050601120312020a020d09050f1c0503070b1312 69
    0x18140d8001c004075224410950b107a514500c000c10200070480ca850b103072160003800e60f042d805011500203000308440790241c1320740103050707a849200f1038051040100080c110f4100d03010890000b15040400740002d88002c04200e8013001c40000710f40310000c04d900c00301410351960300b26042c56400c51000c2c100704403800000d202d03601106030040103d2060105003402400b0180d24000d50504018141c1082e9500400030700681c0899004500e0340c2070103075040400c000514002c1038003030b0300807451f17049100c4a5844400400340c0840d55488600b0300f419255410150901181c41207180a20402c00c00c5845908102d803507105a0050104a0354000c01103070050005100a101050300028594110390f120526810785a40d2454211184001ca592803078456002290191075642c0109983c000049103980c0c2007a00c42d0349908002c02c0882111000390000042d440048a43d50035500ca015654081c2084a1400f0390766614101c104e1011035010311450390740b1082d1010000388882e401500b6809140034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 321100665 1250 321099415 321099421
    0x703020433030b33150a050301061d010f030f06080f0105040515060a091a2e03110d0203040602040f0e07030e1605090402030c12101103092509020a0e030d08 69
    0x2240081c03c0348600d1480b0f981d40d04955810303031717035801c07164551541021441c20b880d500340481c0079107590802c2c0a124017040403015554061101d40c502403040d041d050391410311001a448042d401444880d10850000d9200e26000c140700c0c0b0100004031490084400000d003905c0e050500c01e040a181d0503d1910036134048003480f00c1d0f5500c0641660541e40101c82c00540e010b0096040b000d0078982a4405821003403d25100500201004661012061020014240751480d2070103c00300d8465000c01c071020f03601840242d05004540d405954010b1040800502d0a51108a12000702560b0391110340456050300405c2080d075810b00a500429412400a0801c19181010000c5030340c4c041c0116402825444002415554100807001911030040c10400c44080c0d040042030f100c034000c54a0305c020038207009002e06010150004c881c8110440d1000c0d0080303400c00f02003581451501d100e64201c80304050004100c010b681d1004020404040c0c58045034010340c0022316042010010310401881200820 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 321101915 1250 321100665 321100711
    0xd0b190605040b10050a02070f0914130b0a0c0504050306100503070801020f040302040b0f0a0e1f0311060304050a1202100608060402090403110304080a080a0206090607020703020433030b 82
    0x3910703d00c1d2103803e05c01d84510103250304038036017802c2e41c5c0601c170055160000000c00b1609a4010204090208440d5040348c2c0d0f101d460345582e5050f540c00914a1521100081444429078003000c1c40384214648140340c10303a83c0c000a0700d00340c001e450540d141d061000007007116140401000d001050658001d40c203110000d840e8007054012444080e010740e4550404403802d80c0e0322903c200d000c10000b002c5050540e1030b070032a920240c00494007400702407a6074480d00c010416a403200307006c49034406034050501c00144144450f9800c0035004031103503c1659507440c00907509500704540c00e0469030042403000d1000d0121402e8864079801680213402403401d01c00941c941203440760384036415041c0142c0021410389013901c0c602c01c44e4440c0c001030203200c200e8810400040003c01c0084407070f908461003030320764281580d1103c9040c0c1e0b2400141e4048042040141030540254030782442da88105160303040da041a070b210110281b801401d051142903030a00800076042c0c0788a4105251035043c014210039240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 321103165 1250 321101915 321101929
    0x109081203070311070c080106050604050906040903030902121516020d140f07200301020405060d0b01020304030210050a0306061809090609020409030c15021e07020d0b190605040b 79
    0x1034030591405000001480c5a40203800525180e100d403d41c59985030018200340c01d603481d29025100440d400c08400250914024050318240d030300c001c114240c5030300e40b441000010410311030100c041c580c03909441c501680e18a10000141c54000b400f03030008041d60039045629940c0180744901d003416440ea44126642d0004090710004240d0a108541d0382034a038041d00d01340620a44a0842000020303054200700b003200c0c616958880d42c03403105900d10a914105401c0c1d010381d01600d034020b642400450b20041c01a00031104c80f07001801541d02d05a00d0760003150302201d206a000c80464400620f05d04215810300c50840100704c80d191803402446507150440480c44c140c401c7c0350443d80c850915400f400785940c082c0c0300e510340c000c200308a405044d2401515181c01d04e42d06403403444074204c80c01e07815207940c000c0b6030713808081c6401603c083c04100c0107038103540c00c1010180d8000e800440e040700015585100b16004401c410400c14030998031502900688401c0e07000240503130b0a2030204051510b46c18 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 321104415 1250 321103165 321103183
    0x70309050418050f07091505090705031e010608010e090d0206070513090c0801080d14040302010c110a08030919080705090c1c141e010506030709030b0f070e010908 72
    0x1100840c040c0505003031055520a0b4030005889801583c441040b1814000342c181d04403012a0381c144450039030b400e0511900b803514418160010030320000a200184588001e592102501040450302c040302c001013020b42d042600b001020650540050144548001c003056200c0b03178000c010200380f000420000e46511000c0c1007042408400310f0032240c01d80382180d1581c0604010b41301040300c002c001200078469030080c480e80ca118010200c034962594451040800c5d002c1180d0710080c03410b46581e004490004c90b060f415a910500840c612410b40e81e0001408001c181c1c4d24011515548a03008000100600310901c5155a100401c00c00c8072a1f408551201101c20071149080c035035403503a117070b06001c0c4103001039202e03541c0e8040f00364006401d0640c00b621440488919158041c2d8412031002801c903c0d601e100000d40d400080100310700d03c0c0c004000e65012480f842d00b05000c03030350b03503441b4400791009031481190380e0442000c04c24490b904c03a009200c100000d03c1c0c01c3d05018038009040780c440d1098 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 321105665 1250 321104415 321104419
    0x1209020f0f0d050a050c01091e0e07050403080c16090902090a0b0111120a021501060e1201230402100f0c060209150a0c050f0309060a230c03070c08010207030905 71
    0x11800007120366800850088250300034060742d81160040c545503455502e2180b1141c00b1402e174040c04030324003801c0c426101c0e10381d5010501042d840d0600b40300c800c603548024007043c01c00008100210001301c0300c1002d440c0c8034401c20b005096401081078800c090000541103240d4851400b0141805a81c40c0c0c803513960040844a00042c6c5003060000482d0a01c1d25916180164400c15110743e02c50603c5a009100c9040c040d0300b514074041d0b070480d83c22210320f828802e00c000600301c1e440e0010645001d10085030f440d86810300000c0c144011202c011500c040c54803600c80c400d0b52030010030041d42440510a0004001890038419101034203d0181c4a00c0316403c0c085e02c3c90380d0105806031281c51f2207001640640411203001e4403110803580c01013220583d44800c0b9840c1c000c0c242c00c581c1c00c0d02c00205a40c041c600042003181802c20409084900d8455011442414800f40e041c035666940b62000078002c0d40c1c1d0840c05595a41500d0500001c64005640030f0b91741680304006901c0400d50044108060300c1c81 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 321106915 1250 321105665 321105679
    0x1e11030f010c090e060a1a0706381311041d0c0f0708040504060b091801151112040306020702150301050a03080711030114010918050d030c140d0c1209020f 68
    0x5048041100703001d803600241547e040507102e08000c500380c0320141c80440c0c810002407040d0b5003200765100e41a0942c2410f50303100311110740c14070608171003d0000c3c9170b07220000c0c0405100308002004502910600c09012103402c5000500780100c11546103d91400c1d8610010341a481c1000d2001500303920800080160080020803204c080003010742c00c66005120090090003440d444040c8112250f00000b8030603c24072201c8000400e00d02820b02060484100410350092060404c0094400b000c00201300380860140482605c02d621101000d040614054400107032240807901c10700ca8038001c040e540101d403140a02c01006959500340c3c41205880d40081c0081d200c051a241000d501550140c0f0f41c0d81c036508142c81c01c1c01100c60040407038100ca110400900c002566148a840c0c07601401001400d1904001d910142060082c0c02c10214810245054501007620020110300c03504160361329200c09488501a0b0720f004d51094a030703041106904401c003c549441d0703001810a520800391a030080e84 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 321108165 1250 321106915 321106921
    0x91207081e07140d0905100e06031005091302190e0613020f030f0a0c0306061205070207030c080d0e0a06020d0f090504060902131e09091e11030f010c090e 68
    0x1401c060301c000e654865040743c07030f024402412580b6010492124400207050000010755490a089014880300319a02c1d2420b01c0c410f16005e10001d640000d00030100b801c0961000209030302c3d080f130380c1c07841615500207070440c0148520420190b122000e68a48a01000302c3c000d11a10b454020a070303030080c82c111040611154241a520040d00418001e0710040801100b04a00614a034210501c5942c0450003040f982c1019103059045400d10302504000440e200c4c0c07800c0c408261584440d8110318240100c0d6051079483da2412081052078100c0c501941052802c0302d00c0d2504800c0d00c03058100d0031103030b0032400c0d401c0420080d03407514007034003940820032045003890005026014a03405003070003130014051603844401c118080d5101c0410720b0407902d500c00001416140804520b0301d80444142c040503085d103004c2c100b034003805060a06488144940b16100c60080403c3c40114816110b071428900d0300b940a4100340c28400c0b031190718906a4140700580000581c01818482030350108270520301551 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 321109415 1250 321108165 321108217
    0xe090f033c03090c0f06131a070204060b0a080105090c0a05030a0e0d0903020306060d0804030b0a060e0403090e090f0706120f0c02010b0a0f0f0603090807050d0809120708 75
    0x2080307450349245850000414001d8022010030142c1c42030740d0507501a10507810507402c1c0800d62080c20102c904848680d0024419200101c0b40f9611030102610b00c7d03410401550001401c690440d48040c004084c0000ca8150254001500500411040324541880d00d000303003044c1d500f40304492034402000400800030300c03200015484400c1408000b41100e900c05c5d034011f805041c007112404103902c20310404001500c0c85c5801910090440ea101080c0c41c01c0503d9070340e50601d1020050100c035400c68441c4000b1410034100c805182c40384c2e00a40d2000c14041c6081120301c0ea026000d04001500d0300860b941c0c0d101032344005610030840b03d813803030b02c0ba120030b105400900051102e5410301441c1420304510480440d1305412039804103030708a4002c60000d0341c0741e2104000c0503c031f20502484400c075040422209000794416007429010703080701d13032910301640d540500300940d00020002140e50b0700300384880c1d000104108030401210071041c6d49003101a84410b80079009c1d450400f10314500b1281400010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 321110665 1250 321109415 321109507
    0x1704050306070c15090b0618250207030503180909190b0601090b0d06080106050109060909050c0706140117030705100b0102070b071a13150b0109050a0e090f03 70
    0x141c8181e42080000c2582c0f42146107100166000c078414941c04114a00e04e1650282d041c1c01420707410140c84062941e5400c455012704031120127800c2d8010244000041070342440208040f034284840c60902038102000c100e2210700240c081c1005511021021a8403141e0341d429001003a0002844062540d84400407109010700d0b4102050000700425440b08074299500080141c603a0f520003801000d45400045508071030a214440c00240b00b010300b00b01100c1d16074803440e0400c1c03c0c1401e080c64101540c0342d0000342c4542c0c01e5000d02d201c40d000700410011000082940c000d01c1c641010303601c2c1110540380c042d5079032020f10705903101c5a90303480014156030080140d100100140b441d49130300e8068905060132503164040c54829035150350350014203c1c150000d50300d004281d00c0543c5c41082180d1000020091501d00707486810300500d41c0340802da954940300440c004140e80c5c00c00140354a4140c03040303414609425030b90100d03035000740706841c048003250340900d42c088032100082d4600a5106118101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 321111915 1250 321110665 321110693
    0x1d0109031d1e041b03140112031e0905120c0f04020418110409051003030e0105040308040902090409060608070303090b0c060c1e0d06150f0e0613090f0501031704050306070c 76
    0x403e01000070204c8140740c01d030304a241c140d011344882180c1a03990b086c2d201c0c506480c040b80140007840181da14202035010340c0850b00248242d00d000300c0390300c2e22840402e240451003840c4103001d0b800501ca821543c50440030b860410300040c0e405605043c0340006112101c49000200080a600e07042052007400100c400e5500402a132542400682040d00c40003108141c1400103400254618084042c554010401c80f01100d07800b0402c189002d1521042400a40101c1e080542c01a1910755060210315240100350140c1880300250000d5851071401a08141641d8011f81400c2e500340b21403003031042c0109040c2d92009480716000d03528030305402e20500f2132042450b19028000085040581d84100350300000030355039260606400028608010313076600c00a03101e07020010300304107400461820300c50701410b1480c4070410781d610840d440c2c00c2d001c01035403081c00002c00080d0b5510b00401c1840844a0005541c003103a946184c503050410700803d4070340380010021000d03c898042c541c800c000c807081c80045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 321113165 1250 321111915 321111941
    0x2090d020405070507050f0307150507021f06140103060b07060e120304060212151f0203071505072601030204024902090f0d05011d0109031d1e04 64
    0x2c180380620001d040c0d0740024a0540701445103601c451107888000046a0b203140c1c101003160001c2106a11900140500620100442c01000303034040c80c0444410020081d170070718003404a071a6052603040c106c001034501d55141090704090303041201841880c101e450454000c10003256980882c0040703071801da20450346090180c2c0000402c000c0c0314285d0702500102c1c15030090181c0e80d441c0c00d86010020040c4002145e4020543c542c5035003544c405011861480c00720f80142c80c1492515152050030f048019000b13000300b601c030303010800703000e50050b940c10103c1031047e5101c00300303048101c00b106503d40500001b4083c0703070700050303e51400301940d0f84800c410200c103d81070303002800c2c2c04c81c07602082141c0c031049003140b90382240c080d5038544500030b442c001440500b200e590600c40c1c0c407c000d5542c4c2600c0c4161242d560702d02030641d0101a030303913080c0d04a0881e03c0c0045492905441d00074184030101c10360205040f51040300c8403031079444984801e2420300d032003101e00500c0c03c03a000250050010102c001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 321114415 1250 321113165 321113171
    0x80c0304080d05041d061807020111070303061a0c030a08100f030311010f18150f0203040506041a040c060c06060f120212030a02030912010f05011d0709080303010902090d0204 77
    0x340049900c94018019540c030000d80760406000c0b0001d805e09508165021944040e0700c80e034014119910005d01580006103200120703007101c1200ca00da1039603008810590000352203602c00d000b00079011141c1e010f91944080c2e640e207054050b40e807248e26405026180002c001108020440c241050014500541207043d000c1c4601640d81c230740a800040c000f0b100c8500782d400c01855400d2042c00344180002c49041001200240165540d038004222500d04805062a41ca8030303444c02e81c0e07130140301840c4140e100307000415090a10b4100900c00a00c4015a41ca144034040d0803c03000485400c0d10340101d501a00b0402801e129914140f4094012900308207019160742000088188000c000214084d000307a03000c2100651200e080c1da120300c0340442000250b441000303980340c42d0901003d0803c880840500010390b51078280108030a48c0c10a910814802e4201d42d030904024605010003034019480e402e14049440c0360046107a1a404148103605e5030550119030b00416484050703d00080ca54014010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 321115665 1250 321114415 321114433
    0x1912080403030b09010909061d070b0901120204090b03061f0303030e2e0b12030901050703050403050105010b092106070e0a090f0e0715020a06150e150108150a03080c030408 76
    0x1180003487c0034201a5012414200b80142800080f0910b01c0c24a2503080900344142c1000605036040e4448110385042100c080c0106841178401d2000d8006840444004a000c0e441d4404061078020042c16492200c03285160400d14040c10941c1f060480740d2504012071f01c19000701040703081414840300c1043ca0308120521450044000b480843c00c56118001000b100212000b40031480075609024441030707008100f2109550300400280142900c2071401d10b14041d1255250360075140b0a038804402070f000480c59004924086d49244040070320260b0300151001c0a0800507561500035082c0402d00c00c12102c0c100203602c40c03034840c602900f200e03a41800f18500e010350714402403801040c03585682c0980c150105491a01b04418440198039900512800b01c03503845600050000306180340c25480d0b44000020380c1c07980360001c988629030810f60340d09013010040002d0020b45004110003138200011141c0300700d60381da418001c800d80e0f40080344241c85640580d0918030b548556000207496109176600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 321116915 1250 321115665 321115679
    0x1d06070510051f060c060b06040315060f0e130303050702031b0601031202010203040503030a052505070c080610060305060316080703050706031a0105070204060320031912080403030b0901 82
    0x410700910082202e41414034035901c0320f040d503000c03a01031903000599820840021415640118290f000014100c51400356655a2810807000c621980d02c2c1454882500300003202d1400e001c40c000b82000d01001c06503140480030b00000710010b01000382810782d00c3d40403c1e1340700d00c20070507142c1c030f101c08d501007030f0590040b0b6085540e1200240b0049600140e0f0550301080980306009032170140341d0060055003551034100082c3c02500e00104807019030030800c10185044003208048018400c0e01d611402c1e0307104841c1c203104000307642d00c0e0401020740e4081740910842c000d84058841c1161a0352074005200e40302c4900090804241d00784822a030f4000d02c4001c06c00c51408130300c2e40c084910560889011740d071b4170903040c0d003079030001c0740c03556584000501805120b5001e48001c001203880104001030440e00c9540380c1c071030031103013182d10700a070710703440e00c4004860404200318520b0303140b45041c4206481c803070307a9940b13504000c0308008070403c40c10310b01040403d4041c0c1c0140c4801e040080c0641d003035607140d000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 321118165 1250 321116915 321116921
    0xf24032013031110171306020432011b0312060b040501020618070501120f060611070603090203030904020f040b122202010f03020a05090a080c09060a061d06070510 72
    0x42580c80314056240a503280c5801c080c0a000c405841c0c0b5440f0b0141201701c00582d000354010400d40c140804490041c00040d03841c0300820241c80052148040114512450000b075841070800540da5070104114000c41d0380c001d05080308100080580c0e0b80440038510b001c40f00001004100e200d80c038101003010820f408500c0c06402a620280d0032984956902070404050b8141890002d400e5000b459007808294861503800c0b040c2c0c1000900072881e800b43d0b5607028100ca840d54044070008032072607030840c1011801e00030b8500034200780c0707406c2c008207010350006612807117066101ca20450703000420214142203079080c0d40040070242c11054880d035503480300304107118048950030703613820541030003100c0d050100c1d84000081781c042e0340e0f410007445c070b52405074020b512070f42e1400305000042c4902e08031a52aa40408050f221010140c14500320003414000c030b0600c0501210b00c2600340170b4043c05069406a5445c90142148600ba0300441c002d001044d00f0380325114020380180290000030032001c2c5190 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 321119415 1250 321118165 321118169
    0x2281b1b050303070203100b0a08162907030302073008130308010e0a15030501020403020a09050c09040b0f040c0207030b1b0a2114040b0609070c0f170a08010f24032013 74
    0x40783300c0070031442440c102c140340d09030110006150f0001d00007103003c684258003826040e44511341d80c81e0f00e00e007000c05c0b43e0301c0c8170508036400303030502800e5846400880e80070320840c1d00040f00301c0d040008810780d660b01400c07041c1c050007501c01021034800060b104040c1da42007100100b0401645102464482c240340303020b540640000d03405400c248500042d10036081c0706151040340e000c50042d060000c0c883c2088060007424200da94481108803049800b56907170f216009500c0015001884010b1031031030601550b203002410600e4840703805420032841407220081300c80c826180c0c50701c0c0c0200d0700a0f5a1510411621401b8803000901c0c045000a425600206013402140522000b958a035214801c02525a000304c951f4030000b080001c42c00d0000303031800050302085118440c42d16915a01816a443c44c1d000008013a0021301e000d0010000100103000c81c80107032122544e90071242e40b031a402003442c111010186420595180341002181c1303035103000d40c0b142410507203505a4408003c0717101702d05400c0074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 321120665 1250 321119415 321119429
    0x20d261807120201080a0b0120010903030b0a1424030a09261e040506030f040c06020a050c100e0a060203040807060302281b1b050303070203100b0a0816 67
    0x200041802107a20b9001c1c0142039059450f1811551a409000d0107020150003150500010907954808a0108682d0a480707156041c0005003500c90350038010140e43c1c1c00828030340901d0344c0c40303010b00c04115010301034541d491b8103036440d1002511000701420b2003184044440c1091801000b8444560760300c0d0481c21925004220014080720342e040c040d0780d0072280d00400201da400c00c000c0e1800401c03040c070480c10035081c124941400c0a40e100007043d41da50048506540461446042004001c00700e14444003a142030310003031010000b10b0340d40c5955803104c12001c900c6840740c0104850034501c9401426050940603205842190380c0d00780281d540d030032034019498580074924001c10024480e1099a014601c0b110072092418804006401c621006580c01010400080851400c40380d61f00b41c1e40c8600c0b441130f01801744041500e680c08a00310510381203544039070410802e46015a400042046220462000029880190350000b54240c1215031111640d03009100170400c0408d1001c4482d412180030b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 321121915 1250 321120665 321120673
    0x2206050906060a120b04150308091c0506040803060604151806030b0105030c0708090603150a0f2303070f1205010c2604030c140606011e020d2618 64
    0x441c0200003040c0508182e4200107040d4403602000200307160011000004007900018210854003144040e091240d001a14144000a13084180741012400c9454400e881c04029803088180d60b1215100c10001d0806002001c000c000320311903a0f969401c0f107000b0610036140002480020b0005042804d044070945501508a4400100399000340507544038070340d059603494919502c04c28429042d810034901a5901a401e10600c00944c507000025806182c1d00485040e00d040008104810180c80d03402100e2204402c180030402441965140d05500740b00030300084c0c01c141c00d070002c03c3c600b0760554026140302e070030001c000401500007203034980c00c01e02601c0280140501141e0646030504020240740140d2114010720700010460b00f2056081403103458000e40800280d11500440c6c0086d0316030b020320380c00ca082800095038000c03801521a50000c002c602c0d04414015029440d552420b120206021780380345440310011503450046050341c80100c0381201d5051440030340c280d40c9008180c0003002e00c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 321123165 1250 321121915 321121921
    0xf150d1503151d0c090c1e0408010b03011509050612102306010e01110118080406030e12090f06041e0e13051e190605091509030403060b22060509 64
    0x255403a86400c4642043c0c0050041400090a104607210010000c1c0c0d12400b0510190382402000c2041070440c8520448103601d1303900f042081400c591401c039203203220742c0c900b080504862003401c01c002c049940304d5000250740c0d03540c00d000c2030500c040d01144105500640d601c032107145995501c0401c03c004001a1800206501090f5a6050205840e61804102104c14100140d0f101da240034007800c0107040003103030f10000c0590003400c00e200010103eaa511300450103001040e8035200e03030f40030408207a000308070300040200d030022903200744540140980f4040d2a85409600d0b02d200b100c0003010381e0560b8409000d501d82c082c84101240c0d01801101610760380104000d1070b28490345130115a0030202038500791030307601d8054801004020b2201e045009003031550140448070302399202480d004400c082024a0300d07010319801d101d45030481c059490007050500605a000000703071002d8075803200c0000b4404203503100040004001046020010b400407510042892091704030780c040f80c400fa280500c0d551 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 321124415 1250 321123165 321123191
    0x2030f01020301090b04051b071a040f02010305070201140a0c0302041a03010e09060c0f0a0c1b150c2a0506070f0b060603060315071b05070806060f150d150315 70
    0x47d020f442165140d694500c0b10700306e21701140c0003010620721640464023204903c1807182c003900c0e01207134107644149541a200c420f41d601405055400f089070700c002c00488881009140c0288400f60403144150380c0c1e541c0040b041030013541140d0140c041c610308003102240792914021294401d0088014048051011a404032000104603002c1c070326404401d401d20b1080d0b101d0080580081901c172042000d9100e00c0c0000c01c905d4599207814100500a10240d9420160b02c03a100c00c0c141d4050f40100207010007044086a5a072051981c4205040000500a100d43c5a483c0354040b076500001e511501c0002c90740d04204041e101d1040440c4550b0207603201c1c1c0d9460013080350341d003c102c84490b00364108000c4030036011491000c555200da0203007011581d186c00d0205d14203607184586011203860f40114003d20039110f0800c24594000d200721164214201007001080d8410307c400300c0f4107080745e0043f4046501004503003040c800b0038901d52404090310343d2802c0801d4046070b0490800185d914040c40d42c01e800b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 321125665 1250 321124415 321124421
    0x1701020c0c040b01050301120c0b03070804030206090d09060809070e010b04030b07170609060d050f0102070204060b0f070b19090602120709050f1e03190c0e0103030e041802030f01020301090b04 85
    0xea01611464111303840c2140c4440900c048c14012189403e00100200d0100c64450145010b07440380c0da28400907142c1460081d28242018042c4030f03082d40f140e00001c3c1031070703880301c494816103180345049100d80d15651a8580780081036000303504028104800403c0860701600900103e9020b070382c0040ca90b86505400b50307030180100c15042c00c00340b0040b0005441e800c000010a030060301c05041a9800031582c3c0390241007855a051801c002d03500080c0c00029403829000700b101030b10804110a2520111400f01c1c3c410b8407600f074008007800024030020359004441c100c142c100304280e440c28007142d40b281c03070100002d40c002401440d8820450012800542c815203191f0b00707540c1c02400c1240e40780d1103038007000040000c0d502c044020251040004400751010302406807894a004480304403604149032030000d0707001681140b94402201c800400219600145903401044250360000d0050300105421240e0444241c019425101e029941c0644040560082d412501108020848410708030200025 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 321126915 1250 321125665 321125681
    0x70f0321020f030411011b1b09020c060a0c1e090312030903120f1d01050601030e0303070206060f15031806010803040506030417090d08091309051b0a1701020c0c04 72
    0x360509000140c0000c1c42c41c0311200d1803d1050512900d0303000510940c207e0f0801c0d0160444451107000400030340c10300c050b0301c68000b904044105508104d6100b84e159030b51100140755840290300c8410070a007190048080c10880c003080304a04002c400d0744903015143c4680c5200460342c030b1051138001c0103014030078454900304a9142d5a604501c900141240c4060708107081c034860402e41c1c49080c002107072211005210400d0111001003124a0090009421610034006440c1c035a002041003040b825408074502c0d500a804403005800704442034080b406000000b2100049601d00000b400154100b4880701c0342c0c0d4082c00404c46c0c0d4160b03201c0304800e031240142d2040a40010303042c40440c000030090346186c1c0844511700741c202d042800c0c280c00038151800301c44040e10b241c0720000d031100460074540b003031801f0350290340800e05c0841e071180c2c2d40581e540301d1410b0b40000001c0004441840e50b6400004200904c003030640107a0400088100781c0c001e41c401e0740f070074005100380e0051580608260182c0a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 321128165 1250 321126915 321126937
    0x1a0a050408070b070909020c0f010e060f160203090924060a0c23010612060b06070206070201050a27080c0406030c05011103041d2d0703020a05070f032102 68
    0x20400ca81c503501c024600b01c01a0a8800340461301c1004a1b07280d400344064081312524000408040c54440a81e80c2150441c0c5810082a0400c03002c001c01ca98154941d1904404000302650360406090412420350064240c6035520210010a020350390000715003242d0b0101a0b01c00c0105440b04c030704108011440307640900b0000c40d00f000c202c0c001140582200419000d04e1812921070340d0030100320f0508450954018150740905901800180615480340640c1e000b010b4807524074010164000856034010840c0007410003500003610750f070251242c0d01034003e08170880403000c0d07209011004d80258586500a902c80d13071207181d40d442d4091416001d07500c03c99070070602c16409c160070f00004483c20310420546100c2884200000191035403200c1c148444581101c03540324180c00c240684101240d041c0d500c40a071401c51f002a41e0207061a4801103401c10110b042c0140d41c2e001d41a81500c3c94022038070f01405070001d46000005140c0c11070800e90410014054036154034500790b408400b01d00900070620 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 321129415 1250 321128165 321128167
    0x1080f060405061f050d08040303020d050901020c06030604020904090b061c020d17160516060c030e130b09010305100c0c11010c02042919080303131e1a0a050408 71
    0x30300c0c0b070160380c4200c00921660614210703480c0d03200c1c0301103078984200020031035503c0c40000d02003042c18bd0601c03619007031071507900c0c02904e07010000f80000e541d4601541c0681c0704000000c0860303002c0d6516411155070380382c0074005007c030440b1030500308035801045400034080c03040d5607141c918041e0b80c50096a00e07180d00501c514400c90480e120204814455802203d81035001c0203280f050400c20504010068800c60045c141c0380101d10740303000703520000e51081c1c0505c80700d00d034180002070300a4682001c80d40c2c1582c07030b5401c003440004104003070300100340c000743c005000c1030001c4188140403e0110301d404250005001304118004202c908002411001d403003d05800b0503040c444d8402d203000000c1d680014000729515200d820341d8241802e01c5c10074071214a2081c05007008504150012305041c00c61500b0342410180341c5030705d02d07449210042c0010b080c10940342200f002c01c411031840d21181c0001304101c0e080d01c0f9144c40d003094014030076641601c4880350320000924001c4180030380c0f849242e01007181 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 321130665 1250 321129415 321129421
    0x60a150306050a0908072105040602150a1e060f050d020901121130030f0a050f0417070314030406120b0f04052a0306010905190f0e01080f06040506 65
    0x140c00624016001c950f03929140c0c006400420f0340700c0007070044203000e8a504004d00c0510b0500920032180c0c00000014481c0500080125680110b10045415160341020000d46c0c0c4000c0d07103600400e00d040700f6100c2e01d14401e1850484460a5100c2270507109510840680c1c561100200a1094043c00c030081d80661143e0060001c0c88003010782c00c04842c4548510080d20100a0028489034903200c07050f0000127610703800c0707080c21184a07070b01565003100c0b501661038584c20007081c229a1050760000414080c0c0050040e580d41a041c1c00c4038005c06448600b60000554802600c2d110380c900c0c071064440501e0108507070b001200210032241112900d07240d4244541403503901c800a0181070001c1380e4042c100b0441c008042c1ca842c09000d1080d600c107550b1004201c401c08103505c4056803400c031003098040038800c0241513600f21036038206803903040b80c8258005400081c0490a81c035203400a003044621120001880284032420314169001c0380706032940001c21248031950350f6821200a0819031103d808 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 321131915 1250 321130665 321130673
    0x30803072d11100501030f0f0c03060f020a030b0409030219020612090304080d0f020d270611010f02041409060a0306060f091b0905010e0303120c030a0c080c0405040c030f15050102060a1503 83
    0x400685d0034270400741c4a138216541c0c1c41d04401c598980b604681039a40026450000c59410f22a411801d1400ca400b0413405800d0340307009644400c2412040400711140500c4029075a4050642d00101c5110080c803560b03181036480c00c1d4a80d001449000000c0c42403d5041e6541070144810740340220007580105014010404101c8100ca0248400781c40c0c80004408819012492000040076081c2c5895040c0700f415000c2403142111091015004440d01c1440248446500c45040c200f40034400c480c1d680b4540c465800040c1da11903035a000602d16450004005140846c07a00b01c641194605501080440b145c1c80c102513040601e10840000652505420300c410b42c060908008980d10260032281440704283d548154020141d544a4000c0f1000c8100f180b40c42072801940c085801502d0460035030308000690b5581c0380280d001e040d2141c3c1d281c02d90810000d100344c2c0180e0100d84041c20034842002c40c408031001d11201e038002c00d401405000002205038419000d4460880750031100b89114507d0345d21 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 321133165 1250 321131915 321131933
    0x2060306060c1006241202130306230a0603080d02031f09141303021e07120c031502161403131215050108030a0c0f0206030f010e01050901030803072d11100501030f 72
    0x700c40c490713170340c923603940403001c21003a00c2440c5121601818404645a98003200240c40c200241881015800c04c2c0061002400880507951141400240541c07680c440b040000c4c190101a0401c02d58034015032000251041c05801644803170080d1705204400ea2201c031120381811f0074017a0b001e0301591155041024103000780100400e41c000d41c030142c2e0100c54070f034204441880c009110a4403100c11080c0140b050100c26007000242440c01e00c130840ca845881d83c04803281309002c20000e4052400c101c0580c14000052044490100c03c000340424842c1d2540603908180b60a142c0545030819a105089919515803080c00c0c1a101008000c40c240071820400301c4610180c00c000b2580508030901040058803107801843c052540c074051588298104001040c03411016442203100f40c1d42c1000401c00b184003d802c90750001d00c0c9103401041c2c91412401003c811740411000350760944040034038101c240c0e0144d0782c48646c41c04441600c0c9079490015112095a10a01003d0100c4c401d843c81400007030703a048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 321134415 1250 321133165 321133177
    0x4020a090e0f010e19150e01060909060c0e010801120507080d09030510050f071d09010605030a0b040e100903110304030f020103110a090302060306060c1006241202 72
    0x2019081826291180142928003001108803180d21105021000b040d080c01803000d10140800280200414900811041e819012001c0e00502c01031120351402620350b000b0342441448034000f413040b995030f2a210802420b4000082d10310f00d02d4002111a52846401e5a20084034140d43d40c1c0f859909280b11302e803480f80c4070030303003259144034200c0300160007141803100504403e074640300d0101991a50402ea4100740c448100311003401d01d418100321211045031021900207140e032503c0c4002c1c140c525007e007052500103564641c4a642207000050903903000000b5031090360030b10418001c142c01c1e6014081170b1103001040985640049100300300c980e95070b41c420b41202d4001e281c90421010005240c070304580c0075030002c1c0c900f1000c1040500035540c050143d902e07400c840d151420b26110b81c40b00d00414141d21800020722840c2c1c000041143d50742c40a00740c0e1420303036121003a60801040b1211590080132144950b03400441d54030750704580030343c20ba000c0c91910400c41d1540100000f0f030742d081c24001d50002c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 321135665 1250 321134415 321134419
    0x5010e03240f07050c0304060f11060a0c1202070314070c031205030702070f2d0b13032013090203011d03070303050a050c0a050c2e050c09010503040b0402 68
    0x1071008512040a441c076041101c4035000d40e4905078189204a2040d80500921100070b000d820400071141680000440d812500580303002c41d418142d0340d804913110550000c41000d50706c121400d0090400d01a0b104a00300219521a02c520000000041c0c069000e01c00703002d070100d040090f50f040c00105800052000c14407410f00ca928103501c079a24540c044201e90804400610007004200c041a0100110030150030040d09072900d840c5010100ea00c4d980807031001c009040e001c01034242d444c1400000a0003e07003c1004d03a1034941703011100c01740c6c80061341e200c10b582403464600b10025840c015546a4880303a00601501012b09a106601c006081c0244c0100d03050340d42d072001100b441c0c03039070003405006a00107405140e0f01e40035824010306641015081c0380e40c203841d20017440080307078000c03044500031456070a1145d12402c42c5807000c2e0030003551141d0000220041c0c070403a064408540300d651500f1126103002c10803610380d1162030989000d80d4800c030740810810004240400c00129220b5445440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 321136915 1250 321135665 321135673
    0x303052521090204090b0114030a020a0b16150903090510020307021c0f060203040b07020f100f14070302040609120b04080d021b0f070e060d080f1e07020a0608090705010e03 76
    0x20b59800b29003101d41034807003603440d1200e810052192030f50103208001c4c29a011801022411059000a5518080c80c40384136014000020554505c0c0d4800c02e062401980000a110350030705000611006015030f6002180000d00c032540104961411005050040c412640114184180790f8203108680c1a940d00382070f2088203000c28a400682078030214003116108490168585c1804e180000c0141d1000d03288006541060040301d44446000501740440c20440001050500a00c0d05d0003004008450b4054078101c0c100b403c0040d41c40e01030b001842140c6c5941d03940607046030381d5443c3d0300d00220314800061595000f0400b150104041002070704a072000000010301e410a000d9190352280003243d5841c006401850b0303101c006000600c05080103003400240b10044c0e02d070600010700c030b030401400c006004c0c03540813034482d01c0c01f12403100b41c40c100d08004124207000211282107500e2900b048100324850394585101003001c502ca4010b940c051a080e0000f000c0c40e600701001911401c81c0310781100c1e01441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 321138165 1250 321136915 321136931
    0xf050408060c04030b06030102070308070e0109030f08070b010819110f33090d061508030403030804060c0507020f040b0102100204030c03020a0503030c21040509040303052521 77
    0x4401d000090280c45101456980e9610314039180750b101d070004155620030707403040c4584e00100382c0141c1c125510007040d10780030050360007100045e92410f010340c1000d401690302060038001c102c803110041a0720340c0560285880381c0e80c1c548a960ba0350b180019910700b081c00e05020000014100902100e1021004005400c1e0010410100b400d03054101207680d036800e5000b0462a980040300380024241200b410014609140c09020680d07844c4040c10041c034040d5108590003046c0440d00c52003000d004090103980c1d0303071556414002c0188009440a9444501d004e0048100300c0c059000c444010f0760107800700842031443c41c1000010400c500d0003e05500806005981001540c07008201039442000300700c0301c5504600601a0341c010315008140264030401c2162880c103000900b004030840742d100b03062840c1c0644280c40189000e1503202c250004001410b1004141d0184c02c9a841520300000c07003110300c2c1d014450381c245041a48400300128540d608404070481c622110521410070055012503540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 321139415 1250 321138165 321138179
    0x1020a110103090b13060f0e1b0a0914070306120c03230303240306130f0606081002090103230106050c190c030215030405120901020a1506061418010f0504 68
    0x61130072602c02c500c43c41c0c403210240c100801ba100e40200070702c10150400c800c0310a001429910b5503e82c07040b0042254846d11154150ba800c44d0071409440105014003007030504400d82070200c1c07000d407860404642030120101d8110950300c601001540c0000109000a01e1516641c8e1400404091a42d01406d41101e04c1c0b800041040254020314444c8010f40c1e01c0c81d00c03801c16001d81961040881d1180d0854400c2c4420301c005050b8158401d40c120000c2c10750b140300ba1518400070140c83c3d024400a000d00021804412140c0c0c1c00b4112442d401e0b01c05000d0f403140310b480700307100c3c0c010070508810312041c0030018002c42c0d01c00c03800740110004c0c1d8403c540440212102d2007012160000c02211580002c120600850800c4e0380031003080300100261074203500780341c1d60349a10b03102c5044c60304a803d000441c01800680c42040401202074008170140414120b420090000d800c060048a0209080280202e071240e52081111700842c800003841e91240071034001103960b10040742c4e00b881080005d1001107808 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 321140665 1250 321139415 321139433
    0x1518010507020705030f03161e050106090f060509070807051b030705010c1b080d090230060702121b070b0a170a06080d0806130609020403140c01020a11010309 70
    0x382502d800a100e20b9103000c08040c909154a102120241c000744000390724040804d40906800e680300340b1130703100d9202610300d03d84082e49002000e0140c0d8240f510008410556038030800e814261710400340007450b01e820a01000c2c035016500100080c0d03280300018213081c45000a00454446500b400414854070b0041c14a03582142d0310036600c40e5592010007031171a810102c1130b80c07503a0444005103600d07038494840506a0054804143c010764560440808544d961740d1281c2001000544102140e412301c051a01d410740c2c2403050408500c110000300312881d0000601c075002c6040c18000c01d2a022012000001c0007440c01808a860b1141c176001050a0309040080c4c20300c40c8059450f501541c0c86c5800c013103d408000f400f03074517446182050070300000001040c1e03410103185034104103400b91030b0000410701c1c0d408190f00800990b4640103022503421015002401101c1c064020100c441c5101d106141d142e0050044c1c060150b80280d0014000a1000e40c013201002c8050600280811940d1209900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 321141915 1250 321140665 321140671
    0x1170408040b1219050610120f020d0c0e0f06040504110c03030c070605220605090f010e07050f040605090112030c02180708070804080901050f07061a0109140315180105 74
    0x1107080c0d4004c00511080041c10301c044481581e0003800b150074580c0104843c140301040b8030040003000c0c1a8211300f04100d4100702e101d0240e4503c119643c0c001c03190a54000e2141680c1c0d40005100001414030740c4c07411083d038075030706000140400c4c9441d02d0281000010000080102d01244d814002d80c140c1d41d10a00246100c0c0101c9000e070b550b9a1181c2ca45242143c034000c0c070042c01984281c100e014103503010b9045001569000000003640d4440c019500d2030010110701505140d803c0c01d141c0590301c10040b03501801c0703c1c01542c0107a4241c1110080000740e030140c3c007076203820040c2c6000400a00100959030b881140c003078104094048040e8010500400c84640c00c6980030400310207000c090f50b44000702c542d010105181c0342c1c0150a250380c60324440c0c8982525241000804280d5407071802d042021a00401d90041b000c00402c41ca140300300083e071f8002000140400c80007500060903c1044181d40c0c44548010080c2c490600529203c81d000800600400c0012000b00007003803180b5024840e03140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 321143165 1250 321141915 321141937
    0x5090613030c0e01080f07121509020d03030f0b010306140d0f17040e070e09010501210615110f0606090c04150206010503120711100309080a0e01030f0b01170408040b 73
    0x3c2e40c1420030361840c140190340c2c002e00550140c0c10400a0102c403020342d4401c00e0b0300400d45d000c2103000300c40750409020200360203507000c1c071503080310800c058055011801502c00f050b414031008020b040190100c1c0c00314410400840d59a00711040d0a190142114001c1d501c0b804102c42e5803641d507102c44d90000d12600801c402c00d0343c000703424403030b501c00d000c0c9881d40400a45480c1c0d031504400404540c040c481030ac515818032280c0c1403070b400f0314000105045480300d418501040352035501e442d01d042506100d01110082004200e181400c51004122803180c0c5050714003c00013030701c0d05400d02c200080018038011003184140004180c2c60804208200c4e18207180c2c3c01814554100400c00d400d1020182d2883e0314100100081c200164221983e0100144100c0740200000c503d044154042d08610b88010a121000a030f01e41800740c1101550118440c281d030104100e5014908901c101c400721503007280072442c0c0380b407130032403014641c00301b07540c441d201d02426814a582c858020b8015009151091 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 321144415 1250 321143165 321143189
    0xc0d0503070213200711040501180903092106060803030f280c0807020106051f0309020d0c0f0e010608100e10210213060f211b050909070605090613030c 67
    0x400340030165003142040d040869080005525022040413490402b140d08030805031641c0318641498084c513051001010b038240c41c0d80c04519000500d10502d420100c00300c0c3d110340303406400700f8003120000541344507001d410044000340c2c0b00d0306100e081c00c00d0640300110501412403032508000d40c20f0300034200c18850a89a81c1c2d85410082406030075142190040350003a031207491a000002a1180250a0140107040004010b0040d0000c43c6030380750444001703400f05003a01d0000410314415565101100c90424140d00182d0702c0b0f9404546800003030f00d07201619210340a081c01070f06850300086400c102c49680c10940c3c25540c0300352078481e910a020109901060395a07903015030a10fa651141d50f204031444c1000450b08191030f00c5003032109402400d90070007c240d00741c1e0510780348e044c0640005402142c200300030050ba1404d25100307901805868003034418080802c40d911717400611602a81d009031a502e05144030f48051110b41e4104038403007030101080140c0003011800e070540e10320152940712901 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 321145665 1250 321144415 321144427
    0x7060b060f040608250f0e18040c0e090307110f0306010b0c0106090b09070e010903050f06070e010302030609070e040204030b0907360207081b010902030c0d050307021320 75
    0x40c2c0341c0700d001401e4040c0c807100424440b00b0000a100c01720408246400d05902204142c3c504841d25035030410a541c120038414101c0c06885401d882c501e100324441c0e070b0060207164544140300d01030403040c1d5020059a009000710000112019060f507401c05002c0c1c65042000c2c955800640b42040a070300941c0714810009040d0364244080c09640c000e0040b2580600c0303800580804a03840e140020a002c0c204018004410150ba11869000d07000f15002401c8030506400398240345d40f503100a99006021450240500ca015406070003500e00c0303614000e00070321242e640c3c03810944e4030701c02079000d083e8403990811002c000078008102e100d01800c40f201c0104031103420030941c2c0300003845c030380c00030302c6010100100341c1d0200243c8403280185000c1d6210140c0c0340c1c203c5150140042c055510144000c103040c8605c0d101c240e40551204189a000305d00b02d8400300741040070302c501101c0801000e05280c100704080d10140c00c00d00702d1543e191a1140380050010040b80144804201504810508400000301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 321146915 1250 321145665 321145667
    0x402030627091b06040905090f030d150f0e040f030513030b01080c040225030c021002060604050f0112110f0a030308160912121202130f0b1e07060b060f0406 69
    0xc180103842c121118418046480c20019566019500c206c20121f030f00c5000040065506101c009001c000c01340c201c94035081281c410b00d01411265000200480395039400240c0340c021031031000100c400411811343c1c15100d03a2255002201d01201c107400703021040016400c40081c500741e82c4019800351040811a50503c00c40d04c4c246400d110600c2c6c401c60052190003808007481650408555108c503000032051001d107000c1c0d400300e10f0340e40301941c0300301441c0440d03d20503004240180310301801c0340c00700020365680d00540c0c0a40301c00c2c017904011001150403030b00011030300d520808004000804c04400d54140310700081c0300c000d8681048000801480a1150781000c8907140d0040240c20b06200c07200d10f0401240f029240d40e451000303070512512400000c0083c1c002c0c89000080c00c1c180c04290369a000310009596001c50b01d2141e807058195210000078084100c606a44e40400210600d00e80c071040d1019260440d00510400d8403080d94030010301d0050f554010050200016042506480303d02d0604 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 321148165 1250 321146915 321146923
    0x30c021608070e011e2d061d0a0b090103091a01030807050f03030708070e0105070506010902031b0f0a03050606040f080604030e0d0c0603050c090904050304030506060102030f030402040203062709 86
    0x105c4002800000c451613045404411103010039a441d07011070369540811055819129092446810010030035084040703021903101c60481c070038007900800d0008038807020052000000e15489141d001d003109004000c110341c4250070580c002800b8100c4800d545131244a10b10b04400c085c1c2c01101c183c0000602034007080f00600030f45415040100245007985090716001d8016180149910102b10400c911903529a000300240c0380300d150400304a0ba05985c5606d800d4009620036540c09a0301d4100258030700c0c4100303895003215210031031000761a04240c4094401d1700078140c090302d01c82d4072030400d2101090403242c600501004260310b10090420b070603e804c2c060b1400b00800e204d9801a00c0743c44915020071010851036086541034900000c680d6140400300d102c034060bc42c0210303444141c1e0070070f0109200002001c0e0050307e008005445503512090010380e0303030703224216031203414000c103000181c090b03c0c5c0317903002e0369010b10040e00989020000b03c800020405c03001807505401500350041c852648030401c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 321149415 1250 321148165 321148169
    0x2040911040803040501080a020c0303150f0604061403040609050604080703030f0c0c38040c0906230a0b0327070815060d141b040b0a06030c021608070e01 68
    0x400319074603150808000689a104600401c0d05003e2031002090011105604481d14078003581c0a0341d4070f901b00703107149110411407400040e00c41c9016584981c414504003003103030122a45a102d07020f0111450700800040c0d00300500079541c0c0e42d80c0e07c6010001c52000d201d4144100e10600416a503003180e8035000e011692181101d1403141d103051521424240c00c0741d5010f12840c1c11102128840004100c10060a0300300d8802200403a40749641301c55010030440c2c624099845920f0080d11191203824a81c04c13650030f1300c00c01c0880207018458050000f03071f48154500781800503280101840e198003801d02140d0090f1880752a50b04422103403918010f030403480007a41c100380005410310074684070b202655062140889503001010b400030645c541e07603050710389181a034441c00d514100241c510b072664407420500d07401d40c2c5010200c607060015160922481d4000c12001f00181500742c10100d040340285146520340703007036205140120030f21144121810008080800003088030600304903d841c074841060b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 321150665 1250 321149415 321149441
    0x2a02191e0b070f020a1509140303090f150d06230a0e0106110a0215030f010f0501080103080c030c10020a11060609010506070512030703140705160b07031509020409 72
    0x160300180034408200e411500055000001806219260700000b1074405696000c030200103e101d11040070607801c4003c0341d003180e0300d1411a0010940c0034040c5a01c070b100c1c20000c1580441c1d483c40b0a0321a207083c3d010602503440e03130000e6605016894000134215055504206180c1150300030440540403107202400003c0c4050b2894020345140850154400d20103008441c1485414000003090071000c102001d03060307030005e000345c600201c02c0c040036283e81d2098030230301d03958030f2403c0000c00e46d07039851190700c412200183c1d245540c5070710b1130702c0702410798201007085841070200b0050070112540c104140c2582d118400c40060703071490841000b8260001200e1201c4075604110b041080554030302540d00e044400c151241c0b1340c2c40d03074245070bc14184020001c83d100201c0000c0709000300306601d5440310f040644c1c0480c842c412900d4041e400d0700d0a02491030710b90004840c03030301982c0025001140c01d03070300f0000b5401c0c0480c906c00114004c6480d500290040034400e54040b50030007000202c0e000d490004004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 321151915 1250 321150665 321150719
    0xd081506031f2301020138090a0b090f0f010b0708070b0f01080115120602090a05030a110301050c070203100905011e0f050f06150a120e060402120d2a0219 68
    0x1132404280c143d880c4196014010001e2040e48901b0303886581402c0b2072082c0082003c4440e1401c01741032401002c10a4199002f08a158009038188008011140c0140204003007550203a10b0802001615800180115400c14040c4800070015602c54582d0780100c00c0800c0001096061114042c2140c1c0182103088400800c800100608004100d1f192220381c0c0001015070358204420200d8140b1000754000394062081031180d00074003d50b84249001c1400c120020300050b1900d222010140c001d0800280d4550008280300c10191180d9009030612803250002040c05900d660408905c8181101001c2580c0d444039018900102c1602c10540c3c03201c90090161581e0038900c001c075055014403d9101400d07400000c14100050281442441005803131000303008583c14803400d45d44405040d1000ca0090314141c15818407030b9004580300360111980c6c0e4900c04030300d81922032083c3c00d20908018941500b2041d503802e016840d00b00400306510700058003140000c0c64080b200302121500d10030101c004803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 321153165 1250 321151915 321151931
    0x3150f1507020604030c0e09150c2215050a020c04060e0c03090c0406030c0312030c210e06091c050702010906030e0f0a0b06030d081506031f23010201 66
    0x15448044088030001514480e4a460880c404149248256000508030040d072503400510f030394200102da441000b83c1c80503601220f0801001245e40740c429107401d4105031051140345915078034002c2c65040607102c4500503007050340c0c490110085001c04408640010000110b942c000c03a0100b0240440007000e5404100e840c0c60444101c5090030050180c02c4c6485000001c0340180307104100b05110400700900401c003980d40ca1409540650b40f0707100840e00c1c282180c14400005003c0d00c20300e2810030564544149901d541c1a0704280d48580005800b909a45c9518030701400394200645031003000d1400080c24102c5002c070038400113001c250030400801034200840c42c01070b64421451000c80c1c0c00f60401040c0c9801116205040ca00c030301c03130600b003140308814a00060101c6942002d00440d4241d06a48800c0c4521100302e525000803900da504110f4501c4038090300c0e09040c0c0095501c540d1081104141c1120950145200e1245601031a90b0300b2407020040e103003c0301e161a20394804000d00080200348 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 321154415 1250 321153165 321153169
    0x240605121902030709151a0a02100b0402070b011e331403070207060e030f031803010204050d060209040501060528090f0305030c0106090902090115091a03150f 70
    0x19864105028000714404a0504544040100382c01030000c0d80b1060080351000842e80f512113043d4401e026a00c0fa03078444448840c400381040702d28000b026406009200988015540500146d81d0010340141d802c0128102040907100300a0280080d001b100007001005d2a00704c01320340e07081e00603112181c940c0c8404c0c82070340c40444507103494240446c80c20030038a00e107507000d03a9143e480f01120500c3c8100041000040d5038040b401000ba6642d035160221101b8002003450750f83c20f42900c251040354407c00c0b00e10500030050074401b503960001000589000c3d10703a0003080b1051040030302120034507004100707200c01d0724181c02094054119480c0c00c60130034044804520b1011207558600c0302107561407003545101489002030f000500b040ca210111895500c0c54129643c1d489403c5100ca55403801d80c010440702c590b40603108480b034004003030010b181d0a040040640d00405500300082c8460444006054440d50742200142c0f220380100e1601c0707141004200921195510865100e031210134404034040d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 321155665 1250 321154415 321154423
    0x1e03061002010e0a0b04150501030501021b06010f0b0c07080307030c05100902010c02093103030501140d03050c0f15073902041409060712090803061c24060512 70
    0x45801c200c01a41719140d604251104c02e003030007400d8040302e0800c800407060010540007006101c00460000c100d1002460b1010f0701ca00e02070065112580000000b0040305a1010140c04440d840105941c611595207500c94a07560000d281100803405070079602080c0700080c44400e440d003174802c1c010f0001004d0355000030710b01340d1001d0700288030780340c04404030b00154500700c140d02c0102045100075009100c20003984c0010722000e4011400030342010000b1440c6950034071446032544014146280c1e40c1c0d80c541c0d0954058000b422030411314450480510f0500004025800300804454201842400c0401c001050003121410909203003100703040c81010101c8000c900b400000c0086041c0c40303d03a0b00c1e80700040160900c0c04c00090318260710402c3c00f041c0000801c000b4060402511a5485c0c5000c01440b8001e48a40840c040e00a0b00d003800018864203010030f040010001015002d80c1d400705542e100750514018450018405602003904a14104d540c894a030186c401110700f00b5004842980c0340e9031b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 321156915 1250 321155665 321155683
    0x90c20070605090d0f050109030e0f030a02060f2b1506051c1824051e060126090105060405010f05030601050f010c0c080f0d030c0804020904081e03061002010e 70
    0xa00100e04e10741090049011448201d294098028400c0c41030500b0010f1200d040c81c1e1255208418200c28000705d40f0b0b0004030300d100c903540900030302d04065601c1c040a055070003c07004d840f011040c0b403540c000c0c040c401d0200c200480008981c001200d200070503106026000c19080311040c000f08202a540a80e9061002d0500c08010340c40426031500d840190b034280b2000c900002c20008411308902c00c40014241808010300c05010104001d580c0c0f2020b4040150400410160018040000c100306510484002e1850b0b480031001c506020320500c1419924501100d0b440201e96440703041c400c43c0d1405000382d5004002444040c0300c442d0400d000a6140c07803061090038482c1c622101040841e0740501719032401035420000380081d45170350301200754039001003105844103805528040c0c00b81c94001e126026803a41d0507034071500b555546a09000d0f4110002c0c000f070390341c408103010340500b0012095020b004000700300400360b00c0c0d080c65001d0041810740d00c00c0301819a4105408003c01d940c001a003548 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 321158165 1250 321156915 321156919
    0x110d0c031415040f0b0c1c06090b10051206031c021b090c043308040b06011701090f0e01051f080f120304080d02040e01140d080a0e0a090c2007060509 66
    0xa5989031000d0006c000d1042c06010910030740c00301400f00c1007400315800700307040340c01c052002d21a00c600c1e0302c00c0000001198210300007180c0c0a200380400140e818260a50001024080f40c01c05060301605410604c0700c250603c0040e840400301c180e071621501c0c00c0c00745524050704c4042490526075860080340c004c0b8014205440d420001000d103c800c03105d81043c40340c621412078101c0300a40c060050904c103040341c0949a0718001d402186855200b10348200c0484000525a9100d9082414000c09482046554002107440350350200942a00f88155400391400c402c1c2c16403045900c7c29500d625007035503413258030790750050000700040340780200c2d1200945654240c2a9902d6459140a50a5000e8000341c01e02461001c10007041c9107550021103416505d00c84568580c811826007045013038040124000c2114009000350104240681c562110030395004050303803104d548070010602220480808503000501e0070b0b1460301e030200005041c0070400081000707030003980c0c180000541a8810801528 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 321159415 1250 321158165 321158183
    0x1080c0907021e120a02070e0f040c06081306050c19050310090e07080604050619020a020a02010513030204110a0f0507030c030c020a0e090606040b06070f110d0c031415040f 76
    0x3c041d03a00c062101c070038482e066440d1140c80d10201e82e0025170f0ba000740c1c040c41d8100001d50b170208030300c040c2106d411440780c0d6012600010b61400c0170703000c440344000030300b0000b42c401034035250000052446c05694403910344905003d0302e400012044503800301010820b00103204041083c402803110b09620101078400000010900038101003200c1d29140c0154400c040c2805107600780020410080f5000f03009144640041a110042d1003d800491150543d50700141c8e018081e0100107500990140503214902e201c41c49405a0740d40106080c0c0d241c400d01c402c0e41003400183c9440c95500700c844040c02d01540d2510ee406c000c11540c01a01d01e604e1640c000e000c3c803043c3d01e0210115a1484411005030201e00d040403418107015070303403594600041c1ca80070301c12418902403804034103020007540d41068000e1075001c03076400580c44080b40318000300350b040c1d00140305404840214000d958242c00a611404000300810250000c20b8100800761802020074010b410a200108010f1a00d030120a0b412600417 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 321160665 1250 321159415 321159463
    0x1051806071103120c15091c031506030207020a0f050a0e0c09060c0c030705041b030e0c1c030327030e03010609060b040501090f1208070501020c100501080c090702 72
    0x5008203081c0c005050f454071429603500025062000549000e185620480f9031180960829045242040365035a846a1048007000f018410171801d00340710540c203003000a0740105a0013081802c4580d5000340003c03030780000d14641103085c0241c96200503c080c0d03260030001c81c14000003ca2480d541d120710f1001c0d058903004601c080394500300b103035031000000b01201e556082d0350f54082e0301c5101d00d1f050035110b405140d400181d2801c160003440307514081001c0b10f0396440071800003074008004085040c99244101d0540120680310011030340d80345a4220b4007078501540b80d103401801c0d180c5100005c20040e21400280208080241c58107164580c18142514800c8180300482e0040c051a840b01c010070782441c10000b99041c0541c010820f4460070b83c0c503c1c3c050358a90341d16981c02c0750035116002c00307104002e0529002c621210050040781e032207100058074014240700c83c2450100303011403400b81c09a44100401544d0410004125602c80c1a10f04815034541301038040d4031404c2d0000620f510480b4601070b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 321161915 1250 321160665 321160673
    0x3060103030215090c0d060c0e0d0b0a09050709090803010510050a050304110607020307090501050301140618060d060203090106150201090507090b0a03050a06090b0601081b07150c020a0507050105180607 89
    0x2584c0017104040c3c00066904040c2c02c0010150034441d69007008a101600e503401c0c2d500b0003a024521503038001d00d0f503001c140c40e44a5800c006020344c2600399114054204c0c0403c0303006250040350201c034041e00100f5125418032082240d80b40c0d00c000040c05221042000e0400a5000703170039250310036040318100c4140c5481c0404038440e0f109600c80294980910007010502010751341c07109050b65001c1c3d000b004a04143c48000b4400704007a59a01d901080b8404080000051500c0e01a40400c0203170090284821035a52141603030829101c154482e512640140b00c001007607806c41c0c070031010b17134802031241a5594459584500c070382d014810000e6220703200d024103515030340c4400008581c400101c030310323028141c1049401011901d500303e84542d0041d0109525601c01c01019000d640e5840503500c904001030a004800e40c030890045a86400d00340c8034044d418903500c6032011504854014003102c40c40d0785040e07800d00740c0c00e800c0141803180500210b001048514060b840c0c00100303540c82d650f60703121400c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 321163165 1250 321161915 321161923
    0x10031205070501020c011b0c110d020102010b100306140103061d06012a0c0b0405090703150f0e0406050c0c4b010f0c1215180e07050306010303021509 66
    0x2000d400e82d030001900817103000e8150b001c10f103103106c140c400a940c010380400890704000d00c3e500141960b2343c0355050314285e1814a000034041441400005089144880031a213000b40d40380412002c80c0d81d0785410849080507200c2c2200d10360f001d02e410002071341440e00d0110030002c001e80b140700144c207410000e5803030303400f51581d04001c20202c0c003132030034410070030356407061105000000320791217084000000350b01500f4074190707015a44000c041c14643c0d0b070b894004130020800043e0004c80300144801c00203078800c0c42c011580181101015807040340c03520742818007c0d9040900a0108814108a034038a980d80c04191440204090300310b510700582070040c0e1901d1003000c0d044007004011072140d601d030700030741481e48003c1841910000f40541d520600d2814125061141c0304404951401070018081c1c20560050300f520108140d40c000d00307074480c3d1521104914140c50210000e55502c42c0402e0076004122000c02850100d000704655030460358000d468081c9050222140303003000c4082a02c01c00144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 321164415 1250 321163165 321163177
    0x8040b0910020c0c0406090c0507080a0905090c0306011803050d1101140c0714010e212a0c0306010b0a0807120207050a06060918080a0e030a05010c1710031205 70
    0x281c0a64650f4003a0b0f419a441c2c13112030b02040e20070b901c0c0c00c07130001700a0403500030b02e440803425458003428900191220150340e80164a9401003242c10f00700400c1c55510740c4102806080e42240041d12464064005089402a45c541c4032001e00418800c2000030740015035416200720500d000d5452014581c3c2071030250460040308842900c000e401c009400c1984005855428020500243e003c8a0020001d0032180a1890700300281c01441c42c00300e0000c41583c560f40c80b01c0c03450110b1460301c4c00c1401c01581c2c1e03110982d289915504c080c610708000d40010801c81c0469181100904559490030050a81c0c40c41400388450510445d1000200158020049405011140e60b015540c844080c50526200d03407018900700c40a40c03034502d01240b080340700c1c0700c3c1c51031174200304203c1078241001780ca901b551900300b10510030812a010712000129202440b00f070340101c2c810000411005802c40018042c0300d0518440c4044007886d04c10040102d03500c40d204404c50ba00030a03007600041018404440d98030a407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 321165665 1250 321164415 321164443
    0xf11090f062d1315121208060d0506040c030b0c131404021b0703030f09060e0f0303090a030807140d05030703090519051c09081b040f05091c020d08040b09 68
    0xe00701c0400308030200d800460341302d00300320091000e0300d446684242d0300c410303004409451001c01c046030071070b280e01441d00190040d00c010003c000c081041d83c0c1c0c00d80b03010021102140c141d480c1d40c03000c20800152507845a04420051a85418a00350940e81d60a40400b40320708404481842c01c0016952207d904131001c02d41264050190203039400b10059841c10944011030004030300760300d41640144070352088010742d00b890381c0758881c0c40100e8003007000d508bd44601e03440c1e060204000904040c0d480c1a410b00c0214402c41e603203a101d0405090541441c4514100048203403c0f1411000c440ca900504603580b040d458180050a54458100700b8904012000722001140c6400340d80818098002049a0a04004487d100c81c23002d00200840d0210750f98400c90460381e200400c2c440026180308201402c00d07002600c001102400c480704001955400d440c0600399800ca00442003840f10540882e0040328094001054a0804140028140100240007602260100c030101c1c04c610b2050140c05040014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 321166915 1250 321165665 321165679
    0xa080d0b1504140102072601060b19021203220c0306020a0e040c020705090a0e100614150406120b0402070209241903080c0a0f11090f062d 61
    0x20000001e015640540510460184480c50421a42d132000444a05842000101b104541100c1c5401d801070800014a543d86540b1031074081083d220340c42c0640141ba0013804000918045810040d040c02e1740040740c441c418070100f00300204035803034024a25003005241410502420b00741800344044042e42c10046c5220f0000650b03440c440d500000310002d40310308641c1040b501c001000c0603079035030441c1d203da6508560040d001640c02c41141d88910085520072066541e0290130011000031200c450b0004190b60007030207003142c910300340750074001040284020f189203424200f01d0007511800a01c4d499180154954125402d541c64580646845540c050705c81d0140d8100721800b052103c1c4407140380c4030307881c07844050b045461828003000c025440c030025141b4180f508546600c802c030f610444a0b0b01043c802c401000c0c0c0061800ca500389007290081400900c0040000200012108041c100380e40c0018000e0a00000343e450505c03680c07100b03442c0b2170343e42c004651181e0404400c02c00c10529a0348080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 321168165 1250 321166915 321166939
    0x5040305030c0a020108011205070302060f0705060c0705010501062307150507030608010c0201021206090403090308030103030c110108091b0f040e0a140d17100b0f1305120a080d0b 79
    0xc0028140f2201403003600d6005507030fa2110301d102526900004068099404541c082015050560042641041c00c5001d44d02d40b22031601c900e807500e50213440501e05540700085401c1444030078410107001d481c0340d1a00d00540c0180141c15a0321322000b014000000074001400c0d8104940007012900001504009100d68501410003400030f140910070100207500f4100314210031441031007118046038410b00043d40b5034841e0014001c400e84c0040084080c0510050084042010500618020743c440e599a0100c0030035407400890580101c4125414019400248500c2020100e507403000c040e2440750b1560b003d600e034070010701b10304024008682c02034a01301e10345203c4070001c01c072485180c3c001c503e112000c1554006d080d99940c0e00651240000368001b44c0d00e2803000c420810b580d00080355501000d0b8490301c1c4c082c0d405903517012100c007501d1034000141041d200d0b03030340c4010b110041c1400c039485660000d0f0b088002e900c505111800900354000050111000d07075090f404110041e40241c4034240f10b503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 321169415 1250 321168165 321168187
    0x30f01020a0815010c200109060905010906122a030b031b010c05011d0c01080903130312020102040306112d0d021303051006050102060a05190e010207140d11070815070504030503 78
    0x21181b814280020741601002c03807400c0c000c640390412201c041e90703a81c90f60341c40c1c00c001701c444010b175518200516459100c1e81107051070a82e10f100055034025801c00e00d08032075040180c2100d03041410351b8080d03000800d03440340610002038941300350402030908401c800740320b00d010b0740103103024002c18000310342040381344008500000e00300118039800c1e21624003036103980c0c4d440c650300e014860341040d0315413400b50140005090b5085200500c3c2d0396000140c1400d840741c0d40c06040c2c1d80d298610b44a00f860100300c100360b0105401200d403280585041a21070b100b0b00080d600f03414802c5002540c505600010311040042055194100664010f01035420f0081542804d40c0a0092441807600510408011660010321882814010103c00341e80a00d0032000c107802c00007414401020b03045655013400325402103030f10b142231f052642c546035020b0501c003500410003070414507100b000c440040d03003c50002e00c0500d00005400342d02c10403c800340a82507a078010110b07010b114641000f4014000841c42e00c02c0c40c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 321170665 1250 321169415 321169463
    0x1e040c020c011719020901090b03010b0306040506090906040210090b0c06090111130e0c0d1a150702030a0b040206130306020a080604020a080a15080a050606030f01020a0815010c 78
    0x200c00241d8075685841101914110b680314151100100c907103498441c404198402e80c0100000d14040c10104080c959271900300321182c20907844601a18000010400c1030325041c0314269000000700c41c00d041c18200040040c0d50b600000304028014061904030418450103001c940004001804903d655410701844560700c07584141c5e1205095800c0515200309000000306440e01d4201b804007250100303140840c8041032407006000388001290800204280300350342d009000d901e16102c1a024071000105007400810110001e010070310341c40620071900181d0380030a0880c80b440e000156003041d500c490001450902c181400504131803e4a600002013000940240c10300704515168540d0a940b8241404280c0c0710390170003034000480035000607030003414a600444411a001a4002c0c840340c0b100415407030960000006d0360580d0200c0b04000c0946020081403080f08190030095040492210010f80811005041c0da840700c180010b141e2440d900c40c102d5240402c1c1c10083c03403805056405008258 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 321171915 1250 321170665 321170683
    0x20d0905010e010903050316030f020d0c11010606050403021207090207050604110a26010b3309030a0b0403170412081003030813060204030c09151706061e040c02 71
    0x14a50070490080c2c501c5006100d0b20031000d4250700c0702d03840c540d950314100050091302c10b01e15050503a18080f0684003149480a0507043c01d40c2280002d0320200c0060203050401e807149000c541d6130500d2420301030294060141d43c200d943c10740d00e8100c04881403003c9070500803282c120110103440070500b5810722900040b024041c0d07000b12a070701c0c0100415000d20203076580c2400f07204690040941c00044070241100d00d18040f010b9a0000564020503100103004112112110400d40f050407216030880c01e4000e10520302e100180e954103185c10464008070b42c4a040503000a8500e401340b500040c03d140c040d1210045402c0d4034681c0d01003030b20702071518600b070300c403c040028001410310001800c064480c445c84020b44ea01508d410050380c1d00c444003009204202c0d101122010313000d100010005603103000b000054940805c0104a60100500d2401c180c1b01c1a4484031036a440013250440d02140425803a800410503640000d020920749060440c07803262400b46500149814a1030b501d02e5030128102203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 321173165 1250 321171915 321171923
    0x1a010e011203050901110a02030a0b090d02070f090507050d020c030717030708041e060f1a060a0804030c080702190612020a0806060c0a0b0a09051009050a150609020d09 74
    0x1290390700d49200000e524100080280852820809001c0c0c40d0b0091a01c0605220340c03908689110310316074042401e0011210003220745000900a000d01d2020034424840a81130b10b2004194070b074506150114203811600c943d80d079080d500c4001c05c024512402c100da150109800003595a0040580c1140c1d480c3e11114080d80d0312012045208005010301c4201c03401902c042e6a40d118a0b06c840d120348440da810184d408140301c4107411039600186030350141ca1100c044514001071a024988680120146000c07045481103004200d007001d096006500b85810a4152a11110021051801d00070610070100003035841481c650060059504585080c0c05442e52030741c0351303151040b40c44103003016401614162008151345200040790780c10a040640150010901203442c4915603071079900b0340d0701055403031101658a540d6041c090180c100584c1e0080603800c82c0402004449440b0162038a941d100000c2a41e000c6054009203a080c0360071040251440f90300c1190303100d800340411001042c42e00422a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 321174415 1250 321173165 321173189
    0x412140301081c030207150e07090e030d0605061e03070c06020f03070f080108100e160f0e09031219141501080c0711010c0303090c060c05060901060503070909030207031a01 76
    0x283c03d129000303684940350701c402c00c2a40c510410000401070888084006150311a003c0005601d44241c00740128440404000e1030b034420300100c0040c162513458115a026000401c801781c840175811004480d045280c16400b80c80e5142e0071411110a011514041d200f40d0003c41c103034650070016001107000702c1c040d0f00c4480112031100700c140c9041d0024030843c2299000060b8040c1c0000303140d01b05e1801031a150341540d440103007034201d0311800c0701a034101c40d0003074410f40414820303c1007411103207401c46100381c0198240325240610200704040101904444420109100074029070343e00080b11071b080340b040c02d540b282707083e1080040030400f030180c01d80080c030040081a00032103454100e8001c95000b0015030428090302005540d4003d8006044040544d549110300100e41d403075100c5400303840c16558200d1b407925903082c414680074004d4406956a454100b041200b9580018003e00316810742c90041800e40860030b06a05101c0715a02c0588070071228882028500b29001915041e501d03011040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 321175665 1250 321174415 321174463
    0x1006020f010c0504060e06040909060506150c0a03031e090302011a04180f14010e07091d070302010f032310061701231e0a120b041214030108 62
    0xd0a95282c8801c481c003154041106200c4c80e40719a00d0454240806070540d8600b558442000b07044490011041d00c4680c3e81d9014051186040301a070398202034100c140c181042500c8901a46440d05250018149036841901200041d420b103039003641d00b0400e04081241080b00c6c14082d0281042003044c8100c00c410201060b498501485044040f00740142ca82c0c0c0e1072601507851042840a2420a9605c3e00349480f00780c0001d1801d0103080c11070340100b0081e00b1762030315007102c04c01a59030b01c0034039511040e02c05003c3e54981d00001120b40460341c091920750790300c001d040c800f50014002c0c0070031505c10300e5491181001103054090300c10700602d0034240c060041551400120b500c4c1d0aa0f50100032040f0404c4010800b00566248606004040c2e41d02e60300c2d45c0c1c1406000513011555140d104101d042241c25030680c174a0b00050030380040002c00ea804c0d24002595485448041004100400709044466041000c611030b401070001c81c400480c030300d0790342d58540c0c102a17035441c1407020320000d508002401d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 321176915 1250 321175665 321175693
    0x100f0b03030f04090f06052106010e060d02090604020903010204090e0706030c02031605122a21160506040302030c0601090204050a0506071506090209090604091106070317100602 78
    0x200c90802c2a408421410542046059005840070038000c04150351180404074080c0d4036102d1511050310514a0705180c0c0c1034580896090230030591005034200c110108221550f141e004e144055154102c5880d075599607908005802030040f010800d0701584045004540e0100c01d80c000e00b4600c41a40072901100d5a0300011010780b01410852001a081807080c803a6a00c4107105c695416841b54041d55006200704c00b04a482d2340040901c204006a00502c0c202d19075500c520300c004440c2003c0180c000d60744980301e9426a8210108030501154000900020781018413000324005940305080e02c0300747c102401d0007550303a049040390800501401c800090408030034030860301105d00192100001c90310b004108203094018000a49542d0004e0090054002261044001900c1c8510b001070319420444140a030a19008080c14050751401140380007158060800071298601101d020795611003503d0200c1f1100304001c000b0702c5500000050106110010700c0e92402d81e4000e5085401c00f03245640703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 321178165 1250 321176915 321176917
    0x10c0503040f0f0507320f01020c090c04090903080a0c02280c08010e06251b05010212010801020415020120091207090c0807021903030507050f0c030a030c0212041203030e100f0b0303 80
    0x2001f00d01680c4481c80d0154541090092154032030089d9200320304080c2d0b240c07600010303a180c40508034002040042046030031003040c818147c001d6820b00c0201044031318200c0c81c96103da1190380c44000d4541402c180301c10450150a00400b4000c40d44c020711007201c003410003a540744010755007000000000c0f9407101c1d2020080d055806120042d58520590f001038040140000b01c85000c01e0326995002c1000c0384101084c0100c0d14000c00204000581e00c07231034010300028009154021104590504411031410901c51302c5e2522035442c0c00805560f070701e607410000303002002d01600303ca07281d001d00b00c0000340d181801c0c1e0012035660219190681503694462007261112849180b00300d5043e400301d90b50008c41e01c00c0d4409a4400f81904229151515804201c1c5017608407943d007007041d910009101381c6880c3d1501562070004840c0c0028080c0c0502e030340b034444480c041c900610519030400b5070754005041c03081c0c00410600d030b50001615402c1c6800c0b00c0e04d030094080c1c4042100200d0410680c142c150038000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 321179415 1250 321178165 321178189
    0x5010e010506040b09040f020f010c1b0512030f0306151603080109150510030506061e0c1c0914030c040c08090601050f010e010309020a0f06090602010c0503040f0f050732 75
    0x31034851f0350448070b6007007103805268032000c02c1c10800107004920010f03001104001031440600b80703126210785008104552120541c0c09020203402c18403280640c200600151781c2c0019044070039208a0190420b102e00a014000140280c0248034110005158000101030f050341c514a00500c902c0c082c40c07a1403a403c0d90a8030030641c02040d4006549142c510130381c006604164010720a901d825109a190120b03062001d00b4600c00e0000011a2002d603d8104130b00c0c550380c2c40040c0003200c0f8061600f000b43c4506006d05c50307080c8038a0294002109a40c003030000c151203010041c4200203107000f10400030302400c02191603400c43e11079000042000d182c100801201030b0016510440c10082710001100544011041207800000070b00010540c02d4801c2412000307406140c3e03a110615140000c0242520f005840c00740c14004100184404100ca00d1900b0010903080705000000c030a4918220785060351592001c2c104801c20b0042d5140c1c11080030f0094503018040031042e0081c50031004001e101c40040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 321180665 1250 321179415 321179423
    0x2071a0c180d1703010605280206070804050102120f0403110c0922020604030609051b21150a0c031518050403120510030218070c0b06060705010e010506040b0904 71
    0x1210036100e00b440d121684501082c8a150740c10050705408040b030429400070380065012403004106401300c0b90243e40c81d8840750a88542d907032074002d07180002944032034004d4040300c02c0080744000a03003031000940403500b02446280c01030940303161000e044c18905c401070710200d002454080900c000728030009a00400d640e40200340c09003d40391200c4440d81580f1101020461250110030240507945207406040214007a00c0080f440b40795a190840c140780d003003142115482442054909684c076050741d00700d2803a0400044154240920308541d1038007000105001c00007100c0c0c1d04108600360aa003009064880d2030b00e042c05000c00c401c00c04400488a406202c0d4403449601040070841c038540c000b9600140641000741c4007035a1350001c0d45c280c5008480540f9080305013102001141841c8041001e41070100161209a0400890080581c9104140901850445070200e0010f036514403c403559154000002c0214480c2d290129010704070464071540300d90700e010300c03004040c10410b041500c560b500c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 321181915 1250 321180665 321180697
    0x10f08040302151803120714070309030f1a0423010b030c151204080c121602010809190c140a03260904111206060f0405120f0102071a0c 60
    0x43c82d00080d0b4120b41c000c212246510a0003450b00b5050814001401649465072041d00345103400f0314007800a0580904d20720a405080104030f000c44d07481a900e0054940c01036481d8038444aa040109294048014a1451441d00340c10b00c010820300b07400442703042805403402660790401e04020ba00301d0700000055a01070300480d85080c140d140411048284585001c4600d081404d080080d11619100b154100c0318017800041012007003d003041141003260500b02000d20303240741983c45500e0750256900003414058500c021981c8150184001071091b0495400c11500c03040600708406441c21901c9442c4021160415148040c10306d081c0940aa83c3c00c85120b0800005115080440c1010303160f0070b42d010b003c00e000984881d5100e0042c415100c400ca0042c03034079560360100c243307000400501a944140000c1181d013010802d200255412104102e42c0c04800c0c1203081c0351941080351203004040954400100310301045a40b941c0c80d40032505540440503503a4808002d60100d2040d1280102c200c54 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 321183165 1250 321181915 321181933
    0x606031606080414120a0207080703030906081503011109240a0815090c0408060a060608010513140f0106081003020123090d150c030b0d030f0216030b0105010f08040302 74
    0x4002c020258100f48600ba071200c0180d4580c41032400c006030900c01e4500b20b074001400600107541000044098900c0002500f102c0d8a1070785c0c083c200824610a01c0c00317014034400011140007004c0c14082d804c00014000340003145410805d4080d41e80f0030316001d0b01c03c4459081c2c0c00002903454040010300340c81c0064091900c44884405c0d10200401802403254101c451040c0641e512004030f49030003094150000c40d00c60303013070541c8c860502304010712561504c5d1510a0402ca01076100d903001c0d046590a40b4160003007843c0d4001c020150042a42080481a200c4107122102090413100e604a6080c2d0b51551615110380301503240941080c44081c0c00140c400b0000c5024480c04040e40381d01c00428400c2031700e85070050010580ea2a0741036401d0700e0518442c0e070b690300f60800a018491b48000c69160820242800300c001070b86420301101d0103000c00c100c4030b668850041c000c00800c0a150300308075141c00110703a81c0c54062820310342401224005100b4422840d4918020b03c0418050f03903064002d81010301d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 321184415 1250 321183165 321183167
    0x60309050a2405010b09150f0c07032003120a0815030d0309030e0f0d0f06060513020901090501050f07020f010207090f2406090b0904020f03070e030606031606 70
    0x455089429142030054446000010b10300c80302111460508060004200d507801d00120100c0744142d1003c8070702c200411007140300381e40361010b14070915910300055444a0f051142e0303198500030102080100e100343c3c8d00c08400c1c0052042c20f01403428403906401d041d050075505240e00c030700c00e12150780e1219509102c810061130103200100e61080301460810010f06031500003c1c074103035010034880040f81d501c04822050661241c0101502c980c1a6480d440301315455001c0364025680180c05444025201c1c3d0080402030280c0141c8028840103200b104014442403040c402584290741d69404220800030000d101e5008005031020682013003011030034401c45400b409100001c5403503550460085600218080c003d1340300f40c04500c180c0c0e107000900e4039031520016080b0918900d030385c2851882001e040200f240e001d082031b001cad24160116a9180d40030390004c100a030242000e2101240000300403c000c40368060b90189401c42c040f4201c2e021900c0e4a82456100c82e03208011070b41159540c40144006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 321185665 1250 321184415 321184421
    0xc030e0301150b030603060708070509010825260103080d0207020d060e0a02010e0307030203030f13050d080c0c151e0f03040c03020127050f040b03010e16090608070603 74
    0x8240600046100301551035402e22101c01c0d50031903d480700f00031003444000d06042003241e9200c4180e0a00300d896090411000e071460041d40003880c1049003250002e45128607104025200032903d04050340d10804004010b0003050810607600e0b801000e01e150000d000280e28400d81c100e98002c0e40451514100d450408080e40c00104107903002060f0030080d800050341481015407824509019080507422480010445251001e21030300c43da111042c01d0004d0780d004001c443d0f05c9101040c65035500e03004010807041070f100301d42c00240d1002100c40d03032030284110f550003403040140c0701080e203071080e030700c401000725038034001c0740c89a5030200034400a0100007108000c007040b0003482c031495060030345400359111944d10488007151080a103007410000c55800040d05807440a02c2417240c1c26818500001000c00b05c401c0c4119032056490f6070840d4284e8031194030195100401a00902052059150700e60741c82c03a0307101401020a400e000c000490280c3e41c4102000c1d04c503e040a890100d10f0801c0807009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 321186915 1250 321185665 321185687
    0x3031306091b03060203060f15160c0b0f07060b060703020d050f0d110d0b060705060a0515060a2307020a14010912030801030b10120b07110d020c19060c03 68
    0x20605030310200c071030701c0b030800c8520300000d500c44e04c3d002d0307035901c2c00b6414440a904070741d4010b030141d1401350b05112070607441810f68044080a9050728503080711414294000816907100711031840c4d0000e00c00c0c5d040c100c60402829010300454061082d625100240081d034440e40c2c60140040c1c02142504138441d1041c1c0041c05110103201c10242058203401c0c03080304403812807051041c2880300184240c0011079a000c5d86901500c100c94075400c00c0c0300b40d2500c3d81caa0700000c024440466903440056500f02418807800d092440c00b4060035225030900d10007400c050090415184001c2d00030ba40225102492030440d2091a400b070803112100345016208110000c4803000d1a0500004400c0482c0b01c69080c036441e13035054001d5a40782115450360401030180030006d800c0b00403642c0d40f11020302c500424070740d80714000c542c08010740095558440f03044420142c0d00c0959409402580d0307582d414030744e0000b008a45005d04507a41d03608000700d007850410614a40c0710f10404905402c90500c0400c2c001c52080f02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 321188165 1250 321186915 321186923
    0x2030d0905071e0f05030105190506010504030b161d1822080a0906090f12030c120207080f0a1a07020c04090624030c0b071e080a0f020303130609 64
    0x152080d103d02c01c08101202c141010100c80054076400c000500c000c6190030001c00d400c0d0300030051820b00500c00c1020840d15140f504200d600c035808181c950b4424811a0019504246060464241004c40d02c011500c09001c0c00d0000e13200100745001c2040704003200313a07440001040040c0086030b0b640f038440340103401001c40a140255071026808440030b1402001c09510a07100307a41e07942c0001c0c10180061120b9040001041109013007408280180c0d845802500c1146040c122005501e00e0110b50b050600d0b40010034155407403100c4c1c0d241540001d200420381d00304000742c0350803400d16030410342d40b40d108100251a2140d500c0320b00c142105400382143e00305100384141c9a03500601c90100d000d807581c0300341c211134103030b40c401000000380d030b6114552504d04240801120f13a44d1541c5c0311300d0707020041c40c040c0808200002400c0d004016903c5441c41701c0071001c0c0e0052505240e01d003490326503070308500b040b0004107804000300e4107098070200840340310b1142c40305640240c0d40507031a000010705100b40111 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 321189415 1250 321188165 321188173
    0x906070833120601081501060e280f21020603161101110d0e16031106040305011404020f0303310902131703090310050c09060705030d05010609050102030d0905 70
    0x54040e8503488400c0b041000c0c0b9400600d843e5140152562801c44010100d10038502110014409260f0100791260745000803120b11085018034415401c20b6101055818014140000300080b034424034400d040485034480304807070f080c0300744140581c6900440c00000b03600c800704100240d50041c0011107042c12440c140b912540c00200301c4894bd08591044d4691682c030b00010480b003030b00d1540c0c0e0141c80000704e6940302a0135980039011100100304507501005007005810180002c0765250001580d0085401030028080950303210301141c4a07203c05e8400381d00a0208e5200303801103080c0001200d8403011012510360f00680e80540039418130003800c2c1182c40c980110350700081c5402480c000342040b40c01456502003c00d2400c4000c4d12900e18218013000f06800c01e200c0d940310fa69010400014803041c249020030607948907840e80e81c02d8407a03021103e42c0840042551424014000050400b84180d1181002542d0b01d5010a036580c10785441194010307030003001004000d0209400c01a80d50f0b101d4802c503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 321190665 1250 321189415 321189511
    0x50f06130e0414030304030c051902090a0509010e120d0b150304140a020d0515010e07270306180b0c1327061202011805090402010f230309060708 64
    0x50131a4001e540a40c00a80c00c05041c006100701444012440942500c0030740341c81c060f0b91b010614100004000c124000c0d5a040040e10611084d00840040c00c1c04009071003442c807070300d0074445043d000b124050080c10314102c2c2d0000c2038108007051151a8031080c10a03800c55440b5a5515400384000c04070b81d2150003900c10b50401a250707420031f00b200c9880307403003d80a0601001c0b900e52140030164800c0026010300d409101c05a070b0130440300c403042c110030b000c04000107103000740703e41003003203140d01c0103040e9440d1081c50030b09401580044e9030100d10a8440f520382e43c460b42c400c0d811a01070058031641002c65800b0400c2003c80194030400311400703940c20034502074840745850040340d10039401200ca200354a4840f50071582d10250586642001200000d40e40781060040780c161800100001c0c14450384d81400d002c428040c51820028416001e0403030160301280140090940007920400003034419400892000c1d80600d00782845101400111022000301c582100240700d8000f88400d4a100002e040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 321191915 1250 321190665 321190703
    0x180803040503120f040213091e03050915030108100e0c09070c05100f1401030c030201180305030c010606030c02010c0815060c07090903021e030f0711100306050f06130e04 75
    0x2041d103d024180e16071344251800340107126070341101c0301c90180c03180e18005060700040d0001400f00000d03140300120001f000d10398941a20300344503000050380e02150700c00c8589400003001000394182d8001c24141d9507100d808684e001c094803403040b501e023a680c00c01d0004070700c3d40c00c10002e8164044641c0c1340429032015151a900e04046852120080090300d034044000c000c140ca001e001c405290542000e01c0540c50358031103200c20069400024108085000d803c04140c814401c1c0c0780256030040240c965030008190424020f012502c41c80012a007040148217402d401886a5a460701d441d848428040c1e6484c242100b09403900e00d03406174840d0040c0844400640104401d10241c007455200058850450801910f80510007503240070a41404d18401244440442a6903000161000c0c2d00d8641800b451300710418481d80e551039030041081103100f03a502c0d0349500090100d4405803200c0f4080003a4906111640c41013034105000642c41d5841003000180420359641e00c42e002d1401c0c000310b2000104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 321193165 1250 321191915 321191947
    0x70b1314060403140a02030606010c1112010b10020105090c090103081606020d0f0b1207050a030308041505040f06060602010c2f0601030c0317040e0a0917040f06030609180803040503 80
    0x40c4c43c29481c0d000400100c21410200b1000750440b03001d09081d42201042d40d80c00301c4501c400c4030098003d4030440c5488500180940003c0d1003010003c104d070540b21800d4000a0080a00b01d0f200b4103148144044030305d05041c0909100e050300c1d00300f45079a26186842d60449013034849003030104c540a50800100c0c0051000780302c0c04035004070078040403c0108041041203807807590b00d003842c070058010040400080e41c4d000d001c2400c807035150030301740f07404d0b9260b0a241401c1180c110420850324103041c10002044107040c420002540315560812a45803107000032402c9452440c5c45001103868450507020310002001c40a4156040112008295030900701e00c9080000a0740110340307440d0511030901c00c01507654084034203207801003981428030307191407101d005540001d080147e01c80e690341091350610400d0883c8880c805014260781d40d5a50395030b40940e418071250300c00d000c0001d18200340802c80001c01d0150800c00003004800c11a040c08945504a1581c030240c4100d5081c801001011b0741031801d09 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 321194415 1250 321193165 321193193
    0x91a070906080a0c02150a18030305060909070e15040e0106060504060908011509020c0a060912020705040501080606010311120a091101051c02090607020d060e070b1314060403 77
    0x95162010356240210180550b00040c0c00100d0f810304100700c440c1d020b0740c0040c10340303101c1c000801034400a0300c1e05150700004048a003903541906261120050038550035802c440d0040005136480f590590750903402c1c0e61107980714014200440c02d101c02042e04c182c2940440345240e0001000001d000b451010f4003400c4a045a012002050001c64100319050304101d180c0d0040c41e00d440240302c07041811466810821241c058100ca0f5a40440d258500e01030410143c408158001010071050700f20341080080c4c2e070a28a08800180b1138980045080e00300350080034100ca194200030700701030701c0705401507000c0c0c1908001d500e001c2005014104059086400f2140250031007400010488124201403400210100f5603d0502c1420405103903400d4180f1480c0e840180e03240c20050312901108000703001880b5441019500905002c850030a20440780d12601c5051101c81c110b178160b45d940e10316440c050144030440070f000118001c1c10484840d100688032070001e00180141e141540b03c1d901c20b85024496 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 321195665 1250 321194415 321194417
    0xc0203130f0302010f020f03091e04090b0a0608121b010b03070608191a010315150305090606120a200a08011b02120d09052d07060c1203091a07 63
    0x4840400555030442220650741c0014400703054080c01d0703101c40c7d903a2032044500160140a94110700c5c003200c4404000e901e50301d00001c009001c0c03004603042c08095036805039001a1402e14216000034048800980f01da000c0084c1c1038070034106074050310221056103919594030102d540302c0e2000905550305202c220050915510341112a050007507140d582c415038005600b00c03151600c0c4120b0140c4030300320306101d9020390918000c5a12849c28951070035003140b80d0700242d003034010741c0320440005825400841c450a0703100112581c0e43d44040404c05d0311449544410042c0c0c01512136403010075402500d00384c0210140900c407911616030400700780c07003001030f074403c11940e5507070440d1141116100c8000c5074841c81c213200070090f8100380d6540c09564410380719030b401031343e41e149402c8040007418001c0d1700c0354003601171106070080742c141071104810301410f1000c0303141c1c001c2050100e0310f1401034448182040e00900c8060a40740003600030340040c543d980b401e69100c0041452003885225100041e4442ca0403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 321196915 1250 321195665 321195689
    0x807110d2109030c060f09020d140f010615020c0405040b010e0901180f0618031e0e04020301030516060201020301262a0301110301031a07051c020403110d11040c020313 74
    0xe01701403040b2200d030621420070500707005004015a0304d41c0c40d4030311155000350500300f403603a480001501d030100c00c200500095082c140c000800c9031019160060410254003581c03070303000c1c03500700b00300417120101d50041030004d0400041c0411691310341c40903840443c04000003401041c0c26050107440502c0d24085800781c03241440101000442e0090130401e8440d003134840840030702ca5901503c1b4550351090241e4a002d0700e60b030040d00320701c036104110548001600442da40c1d6100d06044c4e071a0126600030f110b4201c1c2403407001640b548140b081301e040b2105a8100000c50f005840c0c5103480102082c0035804512403c8000c0015041c0040c40d00008602a018944160b0400c02071501f5107010251001b00000e00340010008901c0416a107801006102140840783d960703600b00f59074900502c0100003904c0000b5040124680140c1d0040c001d407800b07862001041c221440411207032011000000704800d080845184d1b0030704080d040007401da120303801541c0c01e08403891102296501c00e40c2c020000440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 321198165 1250 321196915 321196937
    0x308070605060a14030607030e0a020d0c06030c0f0507121202030a0e070f240314010803040e010902032e0b0c031207030203100e060d0c090c0807110d210903 69
    0xf41c480610001080c9000098010354a00c10000f0703222100145203500740764541d0002d01d00001d040c021a941d0950040001d110300f04030b410505501d100b68025000401d01d880403104150340111441074000c11b0310781c0c4a44c5031981d00d40e00d60344030b030a01800c41000e00150346600850009980060742c490013500307800007000b200c03480219160607600c0e40002c4400d8403802051010b1050b04010246180308142d281d000d6000d43e000407401400e0202ca0650228104ac002051840b000300040041340c3c4400680c0102d0307600c44889404910041e22404260030a00f00c0f40305603880d0800741003165020345200524816a00c01c000d0850b0b90202407102e503290000601901c08804113041e50b6088186031034214110320300b0400a4015605034010305800074000800242c0e203503034506080e10f13442c1c1d003d0404940c4503503500c0c104019201c0702180001180c0050300007802e49128801006051000f00c00a00c032420f82640181c550054a140c07207501e40100380c41c00500e8003000c0c051201990310031364400c80801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 321199415 1250 321198165 321198169
    0x221040c050103020901141c05010e090c15030f1009060f030b09160b0c0304051003052d070e0301060302100e090106080105091b0d05040c0f1a160507030807060506 72
    0x5101d40001d81450300c10302c0521940c0e6030210900c00560003200300240d98080c21a807039040001c0007401c8008141c206000070861011604900340200060380484460365041420000c0300a00050150102a400d00c0010800c4c002200e04079004200100450b04403078885400409690164000c800001c4600008000300310004c0355251b03000138064041c040c4100c400442076109030704c0d031103404401040850303480c02d82a024800c40b002000c2c02040d0003090035400320058042c05d07003207400121618001c24201d1018002050f152000b500c040302006441d910a101a00c030944078520f035039050340d40c4071404070041e2518500030050440395103890001c41850000c001240074143c204004020282c001003005458050080303800001c11102c409019103204221040c03405030443c1c000559080000f44421710041851001c10b031000300a50b490b4403503c628050700082218040f14007815401c115594148031241070101c44d640c450401e69000659a842c0e00840c2d81101105940e425510b00c00e104030b034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 321200665 1250 321199415 321199433
    0x2060a05090306010623040e0a0207210309060501050f01020c040f0e10060f230402030c0906070c03061d101505100206220809010e0112110903010b0603040c0b090103022104 76
    0x4001240320040c64a81023a15075541c8400c0623201140464000c512403041005001c0f100a401e4101c01c12005950001c5400402418041e40d0035901c06140100105050424209251076460103030000c14500f4a01400e200042060711030000200c0d03a902c0c9843c444030300074071080d070301c51405080c003051460a010000d02000d80c5507001d9800c0c100002c01014240d60035160300383c00e00c7e004880040e1666115a074449640c401d0030212680f1890028a600c2004036007034a0034140e80c0212810031003c2e120060040040315100e80c2240140d00c62b030705400302480107401c4403c810301c113038084500d0380d680d030703c04076041d0b0802c0b0071000007581255040103690012000c1d6494a001c1c682d81c0d201c0402c0440d15a12510b01c0b800184034100800426030015a90059488207034401c40711008110b24260145112040e800c0301030b00520030350801d02c04240b9460304c0800c1c0ca00981e00100e4003407206150003e040455441200002d041c5a02444007850381c140038001c080864002c894001d6507450146400c00319 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 321201915 1250 321200665 321200717
    0x631020403031d2239091e031502040902070305030901050601020a020a140f060a020d08010f050a05060705010e0604060914071401050a031d03070c080106060c02060a050903060106 79
    0x145401c0c2803000c000303200f440009100311003609400240c55200300c4411000c1080084035950200020104160a6081040103042510071b5aa40104981ca03902c0c0040c003004506842d043d4003018040a1021416040514a18410070840103107496651140b18050782c10040050700450808810030090a03402c3c0201c65004d4424405800d4607409030740018118019405120b801031034a2030010010380b502544082e002c580185410344680707200b00006e58a4042e006244001000c8070700002c2c05015a4030000e00b90368004000900340b80c140b5040c000c941e040f07500300b51100d6403548248005240c082c0603460089025034000b040480c503030309041d88450f01c1640790420b980c0c80a00c5c20000280c450b120300003103500902e40203a850512010407000740c4041c1c0da20080201180000308008100000100411032048940603a4035035170b051440c1c221580c0348a01004202c4c1419030000625240004000307541150515070b0420300118040703494802c01342c0001000c83c0803404440f041c102d40e01d001d480 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 321203165 1250 321201915 321201919
    0x403080f09030f180103090b01030506160216090c05040e040506060a17250503030309030d11040b1801141c050903090f0906010203210109060e0631020403031d 70
    0x300d030045442643e001d620540c01522811200300c001850980e21a80042817070030303002501d012082d61a03040c4a51980c5040d2500040e240901c4202481c00c0d001140c001b014021155407514200e1406402c0009000700090f08000c004c02004007144041030828128002c9004400822480c54603030184000b00e002ca40020441d540c0c06481c4041c00003000400c202c1c0d00d0110a5049071144bd030b0803208030301d29a59000182d05000110411882440c000040d101004a0340c0051296840301758010007144114042c4090b052020400301c034100381403180c100300b100d4062504180724042d18441400310341068001c10403215510940b90159400360040c282c0044e0700c64051807901e01c10400041c60704185100080c09145020005152070307000340242c81c100d500c80311922501c60342c1030709200d0341c000c0c09000300400280f0b092408a4500c061b9404584a03410192059200040b54503240603024500c00301d00060b1030b45200000b00356030f86400540010340c0300b5181d042450a00c070203114102c483c2410428 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 321204415 1250 321203165 321203167
    0x3090c031f050c04030b040f020102030c0d0512070f020307033504030e010306180e010f06081f05010605120603070b040605070213020708030613020c07030804180506010207050f0a050301050403080f0903 89
    0x201c003146e400310320160090b5104c0210300c101c4200c0d02c0140e0450094444a050318050110f070030800503003042c02008400040300410010340d036072203016940b51444101c020b00503402070214000080c019600c45e040c107038855603130320350048a1000c0710f84810040c5c0c5040c803114a201042c0410103420141c0c1460403035003428240189401c001030740a6441016071a12000d6071200150040c009080d03100e20713800c102e01a007d00c4995160070b150340e0f49041d50f6a4003480e86900440450b40030319076124060603903400f550780310716203c0258003903451035070082c10050781402010000205140d4020050000b0003042c0c84180e03c0314914010000e5500e40160400452801044110700081c003003801c40f60702002c1190f49003104401c1c0e07a00d200080c00764003026071080c810110003109105401003d081150306c811140b6105058490505050328002d840c2d241c05a03004410502182c0b92001e000040702d0070103450400481d6540d0002030940f07205a800360701240c2d920007032000340c025071101c59a014140b48011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 321205665 1250 321204415 321204419
    0x4030f030b0409170702010513080106050915010804030c11100e01030f020702030d0f180f15020c030705060306061201091a0315010b09040b060a170901060303080c03090c031f050c04 80
    0xa80c649000b400c1c900c0314400c001040c01c11a8008d4081d10343c860440031143c204a5140c03483e860090006000f194890703000500007880303500040c40a25034009042c2d407101041e8690765400d0701c0b05072480700c1c110b81c0140d030141c020300c1c640c40e00011002040c1c10350341d4550000300c5983c005030807103140789000704046004021581c0940c60004aaa0184110385811001829581c3c42150750040c16050600030031402e10000410003642c200d40e00a4402c07034011461780711119042640d13511980808949c01d60020002002140b4110000e1a88085c026109514124404403a88004c0c00700f600000d0400351b0701c0e080c44410704001465561040020350082c101e00d80000c00402503680c051150945c0c0c100001900800e50300d486e0041e00003000060402920342d01541c0c8040c041c540301c440d502003030701c10080002d00d20000500405080781d030541c50300040343d1240c1485610300d6100410301a0148100403604100351002c1112504581c1d05c1200d91003807096081c1c080040e500040c04401078407a0901003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 321206915 1250 321205665 321205673
    0x90c03060e100303090b03100f060804150209220e101b050309070b0d0216080702010e0402040515090a05150307030e1c051305030601091508010603030206130c03050604030f030b0409 80
    0x321206950045500c51f440e56140c0a10142c4034603250410800200070710360000325144c00c071402900451285003204814070500003c00220f0107904038481e4130180440050645101121120380f100c29041404034040da946400300c1d01d00359000c95103505460703446080c00804008004c1040b4451058985145181440c90b9001c0e580da02c3e500800e01c8006000900c0201a82c4039811280c4185a107090564051124102014583c000072001c0c1d0214050001a801c1803405108490696500030b10f901178081d2602191820b075080300001c2038101d850002c0110b0a9a0307400c1c1d41c0c0318203e1341c1d440c400c3d9584c5000742c4001c1c140d0f201d07040400e05580c88104407903200139080d001e121042c8094507200d512080c1600c01c0c104c420109034801078150084000220710748221b50468121981a40b000c40c41c815a105000f508a41241c880900107070401c0c4045108404000e0410501c1400b503414200c4094603521020304015041d5011404100300c2c1d11611503003501401444021441268200042083c03070311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 321208165 1250 321206915 321206927
    0xd0305090108090c1305010e07021f022b0618060e06060c15010f06030b03031602121f1a0906010f050307030e03030907092906030709090c03060e100303 67
    0x85403410302c080e480003e101601c003040300c68200000113180290000f898810940100028020320220555840c0000d06031400014200140183d01c40741480b0a605402d199000703400c0318201c100f25007404401400102d01d0102003a1440c5005200003540b2071a01061200003500800d940740a00c3c20894100041c0c104040010760020301520b200eaa1403454015060400c2042c03812140d9188400002141c4c1e0404d615600042d103005032410003100c000142050703928043c0240b0619000f1004540d1801400c0c00c01c04112074080c1c1c00704540b944507c44298003001d41520085070360301507450008158540c4034203036030071117203c0a840700310b00c0781003600c0000c01c0c0094014500041c07100000224490b24402e0340016911a21103007684e85030f0030050703050b949442d0350f8410303161140e04003a22146000d40110180da01141c0540742c0240d070084010a01240f80c2000300520f060091010000400c11501e009201c8405480c3d51f000403d1810320345c1840810102801c0c1442000400300306000290300300e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 321209415 1250 321208165 321208177
    0x807120804090c0309050a111c080405040c090527060f010f140c0703051c08071d04020403080403060510090507022508120406030c0503160804030c210e0d0305 70
    0x100481d618601103c16406040d008500502c0c0b40302d06030185041c01a52000e8149040040f111144100c0d510180801403004614014056141c1000100418135240c0d019010221490400600d0b581e540c0000804c4d0300100707511480800b65104580b62690750300b000440c1e004508031b82609030007225000007070102507250701010a00035601005130040d17a081058405841401d82140d04098880c900b0546038290000f00b05044800d0200c241038050280d20028407900d105c2e5100b90b501007949080b442d807039068541d1507420590801002c000310b00d040d401040511f000d100e0114650502441e00a00c1d204903a00c6441400e280c40180907032982c1c041240c00c0c284400345140c010402e410401481403a0b4203603c1103180340704090719641040459009002192166202001502101c1605540f14070080340e2001800d880d940e100c00751503014034070958100b4080d03d0049442e090355912030b2981000300d5481400e5600b12050304200c1544801c0d1007200c2d0074140c0b00070340ca80c002c41c0ea01800f140524 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 321210665 1250 321209415 321209429
    0xa0b0a030c09050907050a120e1203040c0305070b07031d0a050d02130204080c18091207031211040f060c0f06050603190602090f0907081f0f0f0807120804 68
    0x780650380311070342c4600340c02c40140100403c125141d0500310f1020305a81d018240310340200703c000740c100c0380b040c849228102c0428464409845030189030389a001d01540001e2044420300800503004c000305034200300c0340010307000c000121a80c40f04941406000395100d80300c1c2e44000c81203649001c1a54650301070200848409440000100b041407000440c140c03518002d6082481c030108002955207000185021a00403d8841094005051495000c44003085030f0305d5205034011148078424009010041200c039000780f81214007042c1d40440c0030143e808206103101c1451001c06c0c10300c81d000b5125031090081510342000000070800c6e0f40e8010101d44540c0c4041c143c0355907080050b4103a1024441e80394061006010b0000141c0139103040f0009402c104040c0b03009074071002c00e1a04a0421100090050701d41f0b80f11107160799244224140c03100b85140340d03070200d000d000d00001502e00d00903010b40c026010f0005224042800c1603912441d111855001901102c1410740e12004140200211415180c078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 321211915 1250 321210665 321210671
    0x170f0c060d0e0f0a032c01080c04030f0b01081002251a0112061103060f28090e0f030f04030b100b030f04031e1209020d0203120301080c0a0b0a03 64
    0x80c031250760003003400918500c0b0900402d04050310641c408503086084520a8840c50300320180030b0f001c9465480d0401c040001060007803084407040d801740032510760020903048480d1801e40c483e51040b40d4100324140880ba0307903112034014010050706003c48481e116020000310b040130002c24028040e101c00c3d4500d0f0420141c0841c10900780114910b0301102010f034802510f026580da0b44070143c10a041d500d040e50444d1800000255007107056045a02988005041e0b81c400b258442c02c102146078614034044a030303040803904009000914503c3c40003001307011070000702c5030842c0003542e007400e040b95603c5200f0740042081c011008080002e4900387da400c0007074030b074580d51006d112480d2445150401560302c0c2e0040300700400422510300491085119954101c14002843e03101e0100808403115000400ca1603068101c00c0c3c282a0b10030908180014148d901c40d076284e402207403c0034410002c1704281d140003c014001c0001c10810b60110220941d124032095251510800f41070003900502410076032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 321213165 1250 321211915 321211927
    0x180a0206130b03010e0405070503070f0501030509010608060a0b040605041112090c060403060e1005060603180a021c120212030103030e0402190305010504111329030709170f0c06 78
    0x301c034415440c050b100000c0e80c80d076696103c216500465108407000c8a03140f00d006004a0103050100d0180100d54204046008890405005401a21005111800c290358503d40013525020410409014015032100012221021011301c01a1144c0c0d400a03400f450814a8812580034444100c0e5200054411682c4c415100c1000c1182003c1200f0b4020f603202d039000c04c010040c001158442e8142e91f4498080f02e03442450304500e13000380d03081101c0403070348541c0500c0040c3c44c90b1a1005410208a0107000340c0701c00c604240c1c0007070107154120003184211014207022000b048000317414024030120360300040c0b1000d410044049154401400004c0403c46085242c40c403d49590701076451300c01c140c41c040b01c1d1540307020f00000d004000901c9114403c60130301d680c8500c2022000d04a0380902a40040000d286007440700403484a10301d0381703082030100a0308010f42c2c03070721010704007035401041c081e034840b00c0c403928145044016544100803450390380c014907400d90702c482d8006249501c444080c0c1c2c6490b203c3c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 321214415 1250 321213165 321213187
    0x1501291e041502100f0e0a060f020708180a06022a0103060e0a050403030c0e01141305060d0605040f0c0219080c0307030801050a1a03070c02190b0d05180a0206 70
    0x4000c0303500450b0407031910280c1c8190b298002c1000c40407039820002c01c02a032025021200143d0b0300009074441d494210f00b00860201d034190300460421544014003518002140d61803003a194000c0132006808111080102228603081c81c5030801030145200801071400c010300c101158030010f551220740040c1c240da4140032039000b0f81040c2c000f403100e454265020b1420340f904401804c400c0f10114000381c94100542c0c402c5000d82e07082c0a04031410396502d4804036082e0141c50741f5a000750f000d80b844c41500400010b0030f60300d081c0104804000120042000c038640301c240001da41c5909409441d13075040c0f403410052700e03500082048010040c2c3c0300721407940700c070780c102080a032103002546982030100007602070a041c1c11026007412900d061b1010300c0d41540d07a4440300013500d0402d03000c4900000401c0800e0016100309212140c5500084c2000710b040e600c00c100c611402050780c01100800c0020032541c0e8001058440c280e405040303082110b0804e6290032110f9220420003100a104a81c081803018460b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 321215665 1250 321214415 321214417
    0xf1804051507020a05010507081512100e0708010605060711061c021b0609030c070b0c0f070626040203070506070510090b010317040617070309051501291e 68
    0x140c000074024880e90a02d990300946880c0c0b849800d940940c24900490b20461141c02e2080c4260481461a0880c01c030110800030b02d089140d0f40380c821031107200c0705400811002d01c140c1c10045105c0c0010041c04d45800740301e60075102c071035205501c995018007060022403140d000ca881c04020450f2001da4495030711950020341180c0414040d02e0034404260001c130b0429055052541d071806008a5203903941e0045030030341d40e2141e0000f4070082d0b080030030200803400040c03010300314003103c820903500d958502c0035507103107014440d074480c0d000210262110b4900b0035090706444500b841754240c441c0c07186015004241c3c3c1b03002d6407003010f009800008900091200c140318038070030106042070a1240310128100500380300d40a010941d0580c90309200c08031410381c4201110220307041c1703403200303002492001d20002050034000e00c294181038403807410b5000503a05100c609020320384003500802ca94100326440b001c80229003d0600384c05070b120710000184181d58240d640300c603041e5400c1e0100420100001890b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 321216915 1250 321215665 321215683
    0x20303060126040605100e1303051308060703091406060102151e1e01051c0201030b0609090702010c0815011205100b0703020c1e0907080606130e06040b0f180405 71
    0x2d20903000c0621003002000d401c41e0303000340481040050182c3d142c50240007c240240c4aa581260300051500000fa00803006058840b1000d809002c049542c1c100b038a0030b181d400c4521500203070f41da00c0000c04100201c1d280f0203503010040000d0500385040d0380041e55440352a003240310781c5141c3c07100144036491648400d200f000141d40d1145400e080a400c0c01042184050300003441c009940008101428a08540b2802e20701d01102c0c0310031000c0c4c0e80c00540041841c07000b030a400c09800c2240c5a00d40d00d400d15207074000c1c1e603130380e000040c040c0449500404118000e4500940e03101e61801c1c252060381d0001103545c0e11f0408610004498880c40c0e07001e015151181c1c001002c0490200302941419004211000a400d00740d45044071603d40d20010700c060314250080551000380000815520b0388a000915030210000d88803034507141c000c2e810505198090390001400c500d6110030000141014014101c030550180c41c0c0050801111f8001003c00c0c800c07800600b1803c141c1e0b00007405200040100041c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 321218165 1250 321216915 321216977
    0x90c0818160603020c100c140a02011b0e15090105040b13090903170a060e07050d1d0d201903050d050705042301020303011a1e070c0b04060203030601 66
    0x1400541d551000fa0180d001104104014001c4aa8101c12102980039442884240f60f540c52210581a254102c56070060405042150343c1c03030325491040e444040750581400e0081d2101d14617800d40a00300a003c2c3c2c068540449401024003911204e42d802c001178900b6240798507941034079004103a03062070700c201040d80401007031400c00d082c038001c1c142c20000d41000d0b19500500100f45554200d190030544030030348201403e032190309000401c404e20450250100c084010703804184100540d6081403107030011500391041e90009142440d90130342000e640b4200b81200c0e104611001400d41c81035465a2080b42c8455182d6110303041d0f070003094868022240a2800b01c0c004000d070303003003084000702a40c0203030184903000c6806601864412003610468102810305074010b500c1d5a003040f08511070903c483d15a0780b42114244007805048000c081c40a00c0c6c0a1100840740e19080b030350a0135280e40045d60302040300700c0c0041100340845c130340c007000310303648490b013800c1c50035032100052400d600301d54118014030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 321219415 1250 321218165 321218203
    0x21b01110c09040f0b0907080706140d0603060506040b09131e0506011e05030313031e02041b14040e01030816061415040608030301030213060b0703020a0c090c0818 72
    0x2080103010404204c2c0e207402641088440d90718a20525514a0540200700060340035000420050340f0807030018040e10401090203051403030750313034080d0192086500100c492640303c6080189506161040f101003000c104c0b00a1502e0400c158400c003d080900740240c540c102a00381c0080490000c591700403416481000c0396015a540c6051140c80c0403d40c00780203042400500024031498008182c5200bc002040c040464518598a00a041e0410310003580808078586a040140c3d54a119101300503c045406012092210700000e10480524101c600008001d001c24002c016108182c20b041d00c0c1e000040c90340e981c1d01c403405014698112a001031600f030500088031407003143c503a4510b01a0001198200c0b40139006010070040d1810782c05070601d40c2e80b041c0010170261501d202148000c03546500002807003a220910f0980980c4501d81c240c0c0540d000960310020009183c034420f0090440c00740402030280c2020008119580151000c902140d0425408903070100a0003c5a00c0032010007110b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 321220665 1250 321219415 321219421
    0x1305040c021912021603033216020a060503100312020102090603070c030f02070b16080714061009020f0f09011205070906030510051c05190c08010c021b01110c09 71
    0x3c207001083c00c81925006024640b80d01c4601c200ca9410501179070b030705444040200703000d1034075201c102e185411201c1c5d550b14403802a40002d41440000c1078443c0032440c40e0000d800c2c02c0e0052049108282d40003004003c8208100420386c08100b2500381501e601c2680321051010b090801ca0182c01200805a070161002003031048072a013000c8205074080c405e44407552526034608050361180c1507407196070042c6ca020003090a84881d00d408148865100c4c0403c0390601c4100c1c0c90702c0c3c10920144043d100300b5030116080c400b41c072000d4900c01c0010600403106528080054000511500030102010342e0042e003c50800c00030303030284c801030341021007004d402c00003450704150041803008680305001c0841c0c602004540c8407a1100c8510040d41c402400c2065054150541c0300340c48640d01200380d401f80a00d801c0d58140c12034024031f0003440fa0013501c0008041e410300c03000c0c6003112407000040040d54484ca0b00c40522441d00c8400c0403000344242494048070342e00c2038805007400d0b48044820b034010942010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 321221915 1250 321220665 321220673
    0x9060f040302040e010c021b03030c12030601180b04050402090f030f0606040f0e0601060507032001050105120604020906010509030a02030f0d08072a06021204060e121305040c0219 79
    0x60411a802210f060046004881c0860b080382c400c62403400050f04041d100c1036001400c0c02d0320700407240000d022645003900c643c2d000350810300e205c54401c2d00c06d080081030081940e4000d250145410700214400c403c1e038902180d03102503110754440c1902454002c602028075540343e0462600e40c01003c0d00761110310700100030403a01c446088952600c01c5103004596280c6485a10032507042003000b400604084c0d0800101341c8140d08910000c07020400b0300e083c00c80d034180a442580110360260000840e95504080c00c020302000000b802d8003e0b41d001c00208005669400c241d035800440a08216a540380c803040401e0403da40400b000c0d4140c030407a80300031081d98002901c20451401561a82e0f0b00e9110000110344c009560b8810b840744151035580401c2c1c0f031000820849210388229401407070031681e50310080010000311016030b9425507940b9150030f4001c0c2440300b0310001041883d80c3d80350100394a98001418454025580034554551302203050703900821191180100c1d65207083c60301c00d844e1038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 321223021 1106 321221915 321221917
    0x100e03040306020c0a150c0e010804050c0405070504050402040f0f050f0d110117040506060a240e06070606030f05010c0306230a18020a020f0d0c0b04050309060f 71
    0x105d100001d0514064480d0702d40c2d0040d0101305090440d0010740742c410f10804050602110400b0000010804140101080e10071900043d07039441d1203030304440d5030140c0c3d008142c02c503200082c00305009810940f580b040700d480c0c02d401580030342c0700c505205031246800c42d065084441740420000040e02c00b100a80720308818074012100e540080780189810b141035400f551a82c0054060200c681850b40c1e101c0301078071100c20441e00d0307103190b104404030b1084a0f139074610811040c0d00300c65070700782e9801d411640019000001448201d03124107209103080c1c600c40c1c044172290710f06280c0501c9140280644011503001341c8880c07001e040302d00400b607840c580390102d0542c003426a034030101e0005050a1402c10300c108070300340140c030ba45e00508003074585801d011590711700350300040103110501d0344800590580e5510100440305511140f910b2031035400381d148915400f9070b0200740c036010004600 = true := by decide +kernel

theorem cover : BRFrame.Cov 321043165 321223021 := by
  have h0 := BRFrame.cov_init 321043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 321043165 ≤ n) (h2 : n < 321223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
