-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2886
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:02:02.354261+00:00
-- url     : https://prove2.me/submissions/19754bb7-6bca-4c17-a04a-d025d8026cd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 518884892 ≤ n < 519064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 518886142 1250 518884892 518884921
    0xf0303240501051902070801020d06080d11030307210c0e131505040213030c0816080309150f07061d0d02071512060b03040b150d020607060b030c09010312080f070512 73
    0x7c00c9800941d6130b6010f80d15048040c1c80303103104c1c1c265030b072082c2e541d001c660320b00c1070000ca217207600302502840c55502c07012001c54030040040e0802500c042080e09105100e509032081c0128400b50380c94044100001e1410003d01046e015080c02100c3d041c00080205144c00030010700541d0300c21100141c03078006058140003000000e42004000415801000c5440840019a039808428001040a805803924000c030744034020440020b800240d400151000c0e0301240300607040315003401340c44504102450f25040d041d42c4110814000c04404c01e1902015104103000000c482c4035680001c0c0041da2a020200b448510201501010400c40a521010340b0100ea04290b0003008c0b0304036241c0e16400c15044c04014007600303903000107869540300c0c400149410484501e20350725070010941130401c0656103403d406080a03010f01641130260190701c090396541e403410b9030301a50041d007440d2a00d68590740c004d403100b00050078040d80c007141e4500f0082c4140d4031804070f48403808003500501ca40c0e01e0364011500e061 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 518887392 1250 518886142 518886149
    0x607140c10091a04030806101d09190f090204110301050108010303051e0307020c01020c0913080706022802060a05040f03051b011b0305160813050a0f030324050105190207 75
    0xd420061201785030b80b04a00310300070a411a074a1224401c034540544103218072141500d445424800c07244020b03d0f20b4000c041c2d0200b05940505e41e00f00400d0b0301c0710211808440c403049400e036620000d13420350808d8405d0f407541c0c1c0b64041100303103503505007800039140080c140302c0141002400241c41a0041d104418450a41c7c06059103540724100110041c1d160307028020941e0052281800d081194071f010481c5a00455030070418000002d40c54407064030329449030400341c0e240c5400300b28201c181000b20156042018448200e58250400400020301302180a0140051641060107010100d40100300d95900340f80d0508080b0b5661800c000100a80100d18003801400d529003160741c00c0e001c040401e03101c1101d905a404014550306c1130723402c1ca003e0840c5280e1038000340505000403107002c004041c0014060103001200d8100255640b001003000205c007045000030380b00c24034121902103d03d0340003110000342d43c0b0042c080b403d20b00001e0007801036508080e404102c2c400f40180d964020700c02440034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 518888642 1250 518887392 518887433
    0x70e030d09060f02060121050c0306130c0e01060512063001150807050d0519030e040e01020702102601080105011505040803070f0809120607140c1009 66
    0x203403240344000707001040300d44240c10114074002401d4042ea480441c0150580704411820300c00020841c0b594000683c024000322003911440111109c243d07420000c0070700c5140300c59a00c813024005407400340d07007048485d40500c1d00030017240d00521034a500441030f1650024920703050102aaa040d000600000a00300102040010111040034101d80700402c56801da1040000f44008840f864216250a4103440b500109810482040c0300620b84080c44c102d4041c02401191541c0398045110f40400d80324003000c0780450640002046181428010000040340380c100840c140095030f00854008483c0c200d2920400100c0707003a40b03054020b07000749280900e50705503c0c03000359a15034a205009080030b00807402000c03031164062084901c40e1381250b003a1598000690b081c81d89582d124108640107080c00c444c80f00c428007140e8616120f006803004107084000080980c0c1c185550f01420310038500c507241c0c030700f004c0400808000c0c000005a03020301804581000850510341d0030800000d26113003114030603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 518889892 1250 518888642 518888653
    0xb070b1501030216050a0302062a03070309080f090f04090302340602011a0a0b0d0207080f190f050406050909060301021204030f1107030c0303200f100f060e010e070e03 74
    0x117014001680c008090300c00d408545041d102c112658044a00140e5140d0207010b01e000c0008031004244055500b0150508001c00c0d9502c00b55a50000b81c1c00400e088a04410049070300d03861131421a2802c1244803094908014940c21381e00d00035240c2031a102805002c00d896804500d054441d80808891600a5070040540c603888240c002d002c1d1404400c42c04540d82d8400103030b241890403000f02c80880c0d05426446191007000c801c0c80c40a03401c01d22007918500b40c103201701c81440c0324040c01030070529402c41940b10340940510300945000c1c03041c3c0c02407003008010720080c04807503000412111244000c071001d940541d900c0700003d029110b1341e880001c90350103103014802090b0b00150090302c800080d48421182c0d90b680d0302c03115a02c108600c00903050000410040010078040c1520301c40c8462000700c001107480800c441c80d860700c01212400d003803552002c008480c54080c0340c4a50011100d660106204162400c0c072005410001030164000000240300481c1015025080100d030840d0702804fd150b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 518891142 1250 518889892 518889937
    0x1a0708011214030c031e09010e0d060e0a0b011e0e06041505060a030b0916021209040b090f09190507061103130e0103021305270c12070603060b070b15010302 69
    0x60712030b04400704a04543d1151140041e04000302c4051f22080c600c10303514461007a4044040280e031848601043e2405a0703201200e84087e0810305c010705c03895028401400403940760548111a00080303403060315001001d513000340000c2500e2008180c0081085402041c950301e40b180c150050400c1e6800503070302c500001142020540c02d0703001845800781c1111030882c40c0c1e607500078400140172603604210058101043d00031007400101e01404841c2d8001e4030000d860034071080403500c00c580c20780386200c480301c0110070081c800b4803c200c0601401c2a00d07200502c0d1a050f5698140c0e10201c6000d5101408041040044152401c0040c1c400340c00c00385c55282d110558070800c19107803181c02c3c00140c0c090880b0030015100d0b0041d50050038082d20700074100d10715a4000854103442d404a0082900e09030180300e100020591f99011000300c45218500134218052801c0c0002d0103c400c264010550707001d050156601203098141b0700c6500101050054601d10080e40048000303121722201210801014582071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 518892392 1250 518891142 518891167
    0x1120f0504050106060f050d020d060b07060e070801110403260f0c010b041802040b06210108010c0e010f030e100c0804050d080c0723030c0a1a070801121403 69
    0x6070241e0b0180000300000c54849800325042c3c8500c0006c0004103504001c0d00c8401c070307050380c018484003040c1000003030f82c1612034456080f5070f408800252030568403941c1c0b08010b542c1c1032140034000d0641c4002084842c640c1c01c40080103001c0c1e88005000501150100325007059800d0b40700003508031050f00e16503203410301c0d10407501d585c1054144011562030300760101174a0402d80b2649240e040008040d8841e08029400c110180170b00d01080303074012406121604c0d202c0c04420030036100c1d0961000f03c01c05903040902250854001802ca0302c10401141111000d90b600114600c0103040c01d450301142100396a25003915000101c00f101e606039252803007042200e03520150322801148a20709032503c0100030b4078200c810b03101c144d500c00b012180c100641c0d00007138000070903001c1c241345103820035481e17400000300a030a50300000e0381c20340d00c3d4115140c0a41081500f01c4502103600501e01d401c8054104a00e00401c841030502510103035404020400c1c0c14401168800408100b1a074102c0381c0d00d0b1941c0140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 518893642 1250 518892392 518892401
    0xe060702180c0a0809070501300507030b030609060705091011150405100903050d090c1701090b0c030c030103020d0813090b0f060f03040303050c130303050403140f0a080901120f 78
    0x1c100018400c413012130520180494130100311001691208101c2801021810b0301d05d4200c0d44c0c6503034500003480c190600410310b00410313200304503984000480250140c02d0600702400103025100d2600f0250411070f0b60354014081e5482c83c00256950424102c0101c02980c0c2070780304046100c041d104039a15840c950844031400d91140e44a80207840780101450007240680303540500060200e10280202d400c0c21341982d1010201a0168905049156071102001c10411b40040b00c030b44280d44401a030818007071700409494100c01010001481c2d880d003192005c065000c1800000d105804100010092280e4101134580e66000c5612104807aa0b8541512006040d500f01d05801591044905034481c6441c8003651850b66a40720780900d1640c899504a000b060010001200d50b0070520418210014101d9400b01441c0f01ea00e0b965555403d50525040b440707010005400306902c81c0081142c441d5003c54024481c0e940481e40c00d0b02c0d40c10000050316140301c01f803078440304a468a02c2002c480c00e00c5821 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 518894892 1250 518893642 518893657
    0xb0703150902041e050108060112021309020c0f0d080708040b13080a120e190602030612070f0e0a02040b07110301110a0e1807021c0909050109050f010b04060e060702180c 75
    0x208004a54845c01511108421a0f60742d0100d40c50314a0403580040a030020500d030096400041241038a5011800481c1c00c0b01524a1860340308001900400204010000502000b030078440843d2074401c50042c40c610009000800030001c800100303461018002c0a650b01550085c0180d4807a011030600905109a0f61044403d10742090b03412001541e000c0782c08841c4100f07640b01c07000514030036202c01c40650720103400c880c0c1051410305650ba045000703200543c040d0403034418002100b49032000040402001030b0940f90f642d441003004000710b0a9101c1100c401c2d580c0400808500303201d90000900400191001080842d0006800003420380d1150f000d03c07030f21a040381e44004841a00500300e85400d0b04407901405640480e822003d5050031040c01450b6444a02e80201c026850f58803500a480081c0c1c81f80980c00c3d181c80034801c1001054252034003408400311428182440c0c40001041c1c041e000e03010a00400700040c0d000103544610400b09130400f124589034445003440c0d208614940d10590 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 518896142 1250 518894892 518894939
    0x40b090601150e09130f08030910051504050a090209190e1b1e1503160c0c14010302090301060b0c0f0c01020616030e010e030a1b0b070315090204 64
    0x40002c218520100000d548401080d42d038120640302034028070240f42000307000055081c0c01d4108100c0081d205804e29500139108105960304c0741004007c640c9040c2605403013940541c107000c208a54000c42c0c1e244064044400c840102c0d803038542e80120300041200b410080d400c10004d100b00490a4941c00c2c101103440000312003048494640840e42d40c8802114070040940201d4520b982c13035624107481c0070111290101561860b545030742000032076001540d041c028880c0800303c1008402c2405d0b80c45c2178044050740c2800d082c213a01ca0758450f661000756018034600690399101d0130355103910a0741580d18156000c0d00030003201762240b0480c8207580001092040320b20909025045298001c20f5100040d503041c0c000303000d6600c5219050021816003440c420405640780d4004502450900035070300d640302d005002d035a4440c21302e240202007154200c61003c070941c00e420050b000038180c07600341d030b0301140341c0c5400200c6117404c981c108030300002644060031060020801068060113846d1040340300e142403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 518897392 1250 518896142 518896153
    0x4050103031107060801030c090b3c03060f040b0a0902030f010605191401031a04020d05070806040908160309051504060e041404060b1906080a0f110703110106030b040b09 75
    0x160400c503402502400002d1544502260070001d01a840e084ac14650100420b0400c00c0090703540c0000080c203031001c88000e100c1014003005030100c544045441c0c60300043d0040c003030915081d0031942045801402c010900c0202c000024502e41c05035005410040c1c0c0182a6030000b102080098060320311409418814102044100704040800713113864100d405a1000c40c60440c6410300640080901680d0010504804200c200d4159128801050603143e00540029907051111004120202c0180034a006914140000e40810164416103050b070645070124907501059180484841d1081c1c0d000d0342e00030411a900c5d104000c402800381094448507601c9455201c01d40c41044103482c0752180141d02804420040b6010400c0e9030800c80da440710241000421121404c5152100c80b140d0b0f10030000a041034050007091880750042c00450507018405200b00030f40d1001c1445107104008000341405003482c18122081e1080d08a50019a00250140300038070703081c02c104015800495040100f03004a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 518898642 1250 518897392 518897399
    0x705060a050f070c06090c0b03040b1b0901020703060e0f06070f0e060708182407051009050c2106070905010f0305010b031803040302030a050c09070c02032a04050103031107 76
    0x4200e02e922582c1c03180d40300b00b1402c000b921761070000c110354901960604500d039800300c1c1103808000210300440c40740182290701c0c50407104411861406800840c2049420826030301c3c00d81c1d0000f8480184e030b81080001400c0303110141010b00d000c20714200000c3c54040c0c01d08121020f600084115001002070f10342c814020707450401c03c8064403030300700024070818003070008150701e40b2054a600110b01c809810011b401c011102118004941424428009880040d12908100041c041100003010741107081c00956580e546103170b2114404038045002e5800c907004400d090160b09016400e02680d0410759403130f400c00f0f4200902e450b50394001c03240072980e00c10841d00701c0d40c884d00c1140c0c1240c1c1080308090668449580903e02d0220080b810040da120500010000da5814450300f540144200d0050807013500e040c05100b460a0000d0061003442007280400c8090b07180450b9480130942c410860160a44034800441107641c0f965291a070071610303160010007010f8100040c80d1300b0700d210b04200d0700200e55 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 518899892 1250 518898642 518898661
    0x1080a0c03080912010e06071206030b0417070f05060f01240e01020307080c2d07061b2901140f0609010309080a08061009030503031306110705060a05 66
    0x21145002005410203510800200d20040d014000400006264400b59010680e0140c251481480320501541160040c03244a5401a548403001e10102c2d00a119071071540d101d10100400007000a050602030081014003907403034008555410354080360341c0c100c010701c900f40075a8425040300c0d40300318020701400106500200900020b8095030310808032100c4090901c0481d101000c0c8482036040d84030900800e400118800c01404203801d0010051022400f802e000007001900b1080700440c02d90703601081c4100040104021094520a042865042440682d400780458000a02800b0f40642c1c0c61008901c501e121040c104000407074003192417507621008288182c0000186031030f4000d8510143c9121070130914003515184105050025109903140c44199269014203180000030b10703800c04105651412000103a00303001c251a0541c1c0c094250f42d1040c0ea45e10026052026001c4041141402c110b09500300301d1640240400190b1145524500711b80c1d1210103980034200303941040c002507030424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 518901142 1250 518899892 518899903
    0x4050606040e03090f060d0c03020c010b040c02151b0a020a030e0102160e04050f0706090f0801051b070501060302040f020927060126101502060c030c0c0304030219030b0108 76
    0x2e80700c0003a51810040204000400c01c40d80003035500141c0501107011011290f1084040b501080d0310007581d135446803106e20b400c44259610b1b1074403562518604805041c5d0010700d01036402d2130b440c44024240c450002002c107070400e1a542e0b40c6100790004041581c05d5000c240ca00c5428445c0c0c4440c189540701600581c0c94506c0403001c0410082c05007410440108a00350050f042800b0704240c3c1d4120040000e8141400d16940081001c140b5466081007600d41544822000348004e02c02080345041c0000c000e4241c2c0811504d40c1c030311040101e0001d06021007903100000440c0d00604c108590900c1030703210006500404201c0e4030403443c02c00c2220310304401002081c1c103596281c01c03066071551040c0c010740c1e01c010b007080c0c4004482c1d100414005048801100306000300d44019170003c4843c41c100280c690310541340c00305130464204005011102a0000640b504188803003101e944401950700610706e1400f96620103584911403045004d0308050610102c800d1340d0003000d41441580c0c07500c4230196240c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 518902392 1250 518901142 518901161
    0x305151b0418180b0c07080c0114010305070b030405120a12050103050705011101020f0723060112060e0d120b010210050f040b1015030903030b030f1509070f0b0a0e13050405060604 79
    0xa50071306002034000344102d002401340910a500150034200e0040045003155560480200703440901c10050042c00820819a0028441c00709010320311b15190b41e44548900484085102c40c4801103000ea132858050007640c0e070f82c807445110410403036a4906000740d590700d02c0c1c4038440c085500720511a500c00410300840b045402000030092030907499a03100d107c0c032418411074010403a00c0d0038000e012003605111715402070000c1819001d4104582c10048116260700810702410362200ba030506001d5088004011605006100000d200c080c0fa00181c0c10300a03011031416071503103050300b0403150710142c420460045002d110350500a0b030340d00320f400140c45054020150554031298034480c1103071003500201718040c404d02d4007280743e1021401003841c115080304e200031a50809880041d000302901e0402c0e40c040e417044001e1000358541440f01d2951480c500a00140745e81c0000d46182540c000d6030b40b00040b07030014003180703079140c14491707000001c00059500311464011140400c680d4034241c0140d4409 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 518903642 1250 518902392 518902403
    0x1090c14010c03020312040204060308030a06060f0f0e01080714300603060f060d08070506160e0f0103020c070807151d151605010c020102090f0603010305151b041818 73
    0x8100800700080c9141c01b008004990082c1c6940c0f0100005010202540c0511314800c0c001c00d42508000026203080109031420701041481652104280d92110300c070381c069002800d22090645450a04480807055072110038000c0078002581c030b03100303400b00b41c0f425000d120801c5481203030360310309120a0510105427480360b855401130004c00c8103122403140442d0480341c0200940c03030f0b601031230f99919455001108250744c280c2180701000301a01424140405181d085d20742161704403020400502c41444d284061410140d01040f0a20341080c1000f000b8050149582120402940d4101040d010f41380340c0c1c90100019092140d140410703441e03805103c0c0c21080217101c0c180600d20440c4402d0550401c041802c522b400c60003100010810a1007102c84c0d6041580c00942d454001c03c080c01100c0e00140d200c00e000b010f003000100f02241c4003044a03009142a00c0000d5255140c8030408000f580c0c182810352131200d4001800608150516203007070b90984000000d001c0751081f030700107007105004000054a03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 518904892 1250 518903642 518903647
    0x60f031306150f0b0f121f0303080403080a0902060f0a02010b0d081909050a0303030c1206090e011802030c040b03120307030606350c0706020c06040b060324060109050301090c14010c030203 83
    0x4150700d1b0041d850b817000c4045481110320504d000001d007040b00560040e00468109414803040c0343d44400b100b940800042c00600100e4440d502146140c4185112019200c2011428031100d6201390000540c0d2800106003031013020715401d040c285030340001454200043c1400c241441c940c00707811b9030f504680c001015017500c00d01c0d644060340640700001180f02049140c2068ac0314001892080c900036105400000810044107548582124406001101554002c248541c016500011620741e10041602d0101d03d00301c01d040442d01d0140300c56014109070802000b04855181d0541c058021500c043e81d66030781020740600d4001800940030b1800c01d048600030507000d2540c0f00c40010a07004200c1d404010b01e043d402e625820308070b8101d140c040c18140c01c40001d200a0042d8440f00d036400ca2400c40c007408084e1030022150503403e20107440055010b280c54005140f9a00584040004000150092001242c91700c1c00c1d0125581a00500170945549104149254407801c02442450340c160002c51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 518906142 1250 518904892 518904907
    0x90601030c0323010e01050a061d010519050d0809090f010303020303161b0503040e0a0b06041404141312050f0d110f16050d0806060f031306150f0b0f 66
    0x408010050250203d01400e01500300c1c07510401d1140721200540d00c4000161030070241601029501c81368015905000340d080002c1007204004c01e0141191000c9404000d15901c1c1030810030800300c140e001d01e0f40b04030204100c006105d8000010300b02864101c65a2500d44d0f9000500c4c0e02041081c000a0f0050b4018000910034826082450f002e400d407034105055201c100042070038161410709030446954001140c00c001100c0411026900101000f00070b00c2500840c07c045509402544105540303000442900c565076200c075132181e40094820000c0c5032061403c444480f81e42d0a01d84000c5a80103081204034501c80e22070019240e200502540761071034051a02c03205400350940031352854203408104a24a5412250001000d404290300110410501e9600788503017850b01c01071022040c00b0f40001000a665a6032085442145070501c80d01c0e00e03a00e650385460700e240a40c02c00184094a0706020350950490340d0940003c840c1041c1e18010481d466401d92001801800d2040000781c0c018031128 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 518907392 1250 518906142 518906153
    0x150b03060108070216060c020414010e060121110c06180334030c0320030409050a090f140123040201030b030307050d0905042304081e03090312090601030c03 69
    0x543c0010043c41102d0964418030302c5d124072500c26a006a021070003003d40c100842c00c0c6030098103206030410b8040c4616600d0250302c504140c000504107810041e03041450b140500c8203001103805040f08401c20080070310581e000700007640c8132a07058145880340d04005800e54552503104404020814090340c2003244114142500c2c05021390449840500c81c030380061071415080704080035902a603110015030380c090402a00c81d400200b4040f540b02d0002c0240b1040c140b001048400701d4905c0080041c2075644c4c0113400e002040e00b408010440310039100300209102c4540c100b2540450044001c0020761065004041002d41d941d0700b191250410380c0016004d503001e5032110742c4980010341a81d103018410f54446040103054240b035000b140f01c2d204c0c1403080f0b043c1446a980904440710741b41d40d20040d44e0080c4100340e440107000507d00c590001d003c13800c0b030300103040c0b00c02c81e104002a4942c0b682008188948c498024002d207043c2c1910701000581e0290000456904a9070441c130034062903400d50320741c17 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 518908642 1250 518907392 518907407
    0x201002090f0909070902030c16380103030c082b0c030902010c150605090f01080106170a0b0718060e0f0105090a0303030507020c0901090b090f150909010f090f0303150b030601 77
    0x1044240d150900062101e103580c410561205840f400f8a43e41149000d00c80c50100c0141082034000d0000c41c02180100c82b01003080c45040d01c0d00341c03c000304041c0303042c60b00081c2403140300303003039408a03104114408014060360000e140b800455241806480303850141102140c50125000c0d0000310b4100030000841c030b1102c4000441e003480c81011600039100e0012445060303043e50350182d080c08150040250840a1060401414040d100000418031201d0010340d00c56a02401403d002c61200100740d1041c003e94111601c14201702101005030b80c0d5103000b80a0080c0124558000d20380011200e21035846007017240c80d10303a0010049490141140c0301100240f42c0207002c842540720300d26810241d03503190084030f8000c1c890440049209800d11080c0103603074901034850882d134122802408070b00d80b81401c0302c50308400d099a40c40e88a64901d100c0d180903220216074284445e04c0d01c038100c001c0c001c55610146603a4001e0b10b06122503c400b2840e10031124140c451130480310030a0005c02c440f5849080c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 518909892 1250 518908642 518908651
    0x6030c01120f060b1b0703031e09181e061d04050304050915040f0b01050901030b03100603050d0f0203040302030c0105073f05030f010501201002090f090907090203 72
    0x1000501c540341a06200849406030013016080710b000c00c00003085038a201d11580940b0010018141851541d500507185180030303801820300401c140c0121004900c1424070b48010086044402e04050146403014001c000c03000d1010340750f901c50200500c8070107040c0200d1049038100c0140010090f44100c1e1509100006001200c46000410001805690349011a03000c1c0c01d0b1030031003562140101c0d041000b240d010345813450340c050420300d68101d0341e1b0b002403d48a19003c20300300412800740340e200182c02c203444985c141d211a444e007503000c0144000044c0542940043d9101d500d00e05020700800c3e40d5900441c40000d60642c80f031900d0708540d510a03c060304402d4030920442810b0482c040314080300030360301e8500e03442c062000405840c10494030079802c07a29032a2400c02034070358244240800d8138000305003c1c0da4144410000e03016a03141408089504504070300080d00c800c424041c94010281d401800c0d01c0317128080c01040851240f0300b50311010f01804032480103000062801d80e0a030b01a400050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 518911142 1250 518909892 518909927
    0x130209091002180a05010314040803131b08120c031e0d0903080a1a090a2a0306060906091805040503041e031502030f01030f150603052406030c01 64
    0x1c1e603194121103280080c00126a0046003001056008001d00042d50707003e501c51410982089800300b0000c0310a070919800980041c07134540c0c1d82d61005440a050215880010001081340e116080380c120035000003020b864510090340d07152601199021101e0140c025482078a800c1042400509130100313880e0186400010b0641e804c0c42c2144102c08200c40c0741100c1900410b13076420411400c200c1c0d03072203400e083c2540b80c0c18005440341680e0200b403101c0c00c001c01890000e035070b860300307800e5240c4016903003610650303075030101032428050303400080141c4200d125200204e0811030b408150303035000300421002c0e90207240c02c121014a0841080c0050003010300284c400c1e000411020882e03003002d2002801c055070b008502402c1c14914030301a40030b1100859000e195034414810700000c6102014154112504030101c03c050301d040341400c051048010401e200810b180060001c01c114001c00c410840700c0c407035a40d03001c4021028003005088031088409642c55081381042c40c00540c042c4000c00810102c0b103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 518912392 1250 518911142 518911153
    0x819030c02060d0906140112030309020f120a1a070f0806010923120c1f05040f180b03010c020715110105131403040510030e0309030d030b130513020909 67
    0x1038001c103202e030780b01d0048105a90785406030841405124004c94040c1c000c2008004090340c0352107188241c00e0704c0084010304061300c0e408503000f55540c080303283c40390707100080c000c0c45c0d541a100501e07542e034051a00b0031203500040d800c1c0c0e0490310480c904118864840f40d140e0011440b101e1000b1280000000c103104d042c000e0400300414119290020f02000318000010350031501d0b11740003009440300c080d0750005081c1c0e000c00003505541d00ca8042d0304002c040d0124442e2041c0d040d0100642d500d006617044010300c00d10310711002452400d00c148840b50408840010840610002c080c1801c0e41c5003e480c0c000580d108050805c0030f00c00e0f00008060480709858050008807600160700d0940d0400e6645111038503404180320107010b010f101241c01c0d0301120004614040c0751201181212207a001d022043c580d5940011441050610881e041c589000701a103502c10161000070f8002e0408031416401000440141010001c451060b10f014030003001c4040c5019403140d0030171403403500040134410369000b01c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 518913642 1250 518912392 518912417
    0x80a02072a0603060b0702030312061c050d090605031b0d0e011410060c0b0601030213030203240c070f02040f140f1902040e0406090c1805090c0604081903 68
    0x9890868100c40d00a0051001d0034a0160020140c1d440c03608141d0402400f0019040165400011207802211030410611199210000511510401d00300d020b0492514420391007003080100342e000440c05252a400300298407490704881c1400110b03001c0240c1e802400c00701c0740881d02030000e00304200da5503002003440a100c428460948940201e26040081d2680c01d01c0a1000414402405841c0c185040c40b80d11640c0c3d2214840010007400c2d5a0601d40c0c00200c00c102c4030302d91100c210146402400300c0d907005010181d41c41100c0340311402060702c080000302041018075040102e0764526004a082003200109408000c01000c064445800280d038912164045500c1b000896100d165100c0341e0f02090704d0100d0b4844c1c00748816400b4440858410041030140000c250b0507190042d80140001404004600c1c2c445091886504540e004c12844002e07032800c0041c41d040a881081081c06842d03d510808043c010300d8003960050040640001ca036400d0201701d44010101c05034020325051100244 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 518914892 1250 518913642 518913683
    0x70507050d0309390806040308010e0601020a02040c02061005010f09031e050105040c031106041511160b0703020c0312030c0c160e060f0306040506061908030f1e040501080a0207 78
    0x300139150300450141041300c3d607980c05002e0f03565001007602d00d02400703161402c1e0340c0041500d5014002c05880c0b0750080082200c0c1e902c204119041c0740d03405032007008542c00a1030040c0d07035a038084424489219129038042600e511403d81004150b01a0321854481400c42c1d45403034001c0440c581003038507820000c902c2c2d40803410034012a4043e41c002d040324114a41982403580c1d42c480c9000c031407030181a0400c42041030041e072039541c2034540c1203442e0810b10358002c03c15490604106070b407040206048600042500541d001c02041158800c2d021900036000c80b0007815207030603681450160500b01440000d08969011000f400c4030300b95a4141c61007440d00d600011604120340d04161b1102d8000030070440e43d810100b406101000d01100104181d142039520555103d41c0180024099103440109510004500402802a00d51802a2500c0312034140151000d50094042c8110394100341900600130b903110740c00c4a040d42c0041e17460340201d50b1006004006507201720402c480b01c81011035840c00648 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 518916142 1250 518914892 518914943
    0x201120b1f0c0b07090f03030e0d0b27070305030d0b130606170612060a0e0a140a0b0718060c020616060905010605011d09060a05120114070507050d0309 67
    0x110252a1000a19050f041c1141c42c5040200b01105002e101d49080c01054004200502100e07854602100e42c2c450a00103d101131050300401404290042c05000400799241c48003c418000e45002d018800e028a241643d01c0030584005081c6030401c110303030194406160080e8134001405816528182c0c2001104c80450b01e0396800300340081c5020b0720700d040e0032000b00303001074105c0802c46d008900082e14040513604c9140180c0208400c131361358114659211030522020040580001910640d030b040080c8150710b440b0900b600304c1c1c6403403618000441c0c1d9801108050134840090542d5004541409415949032068410584e40001d061003000c5030b11903051600d0200314440c100c0410351300390b146001c0e8292041a0030250602c0480d90451004210400c641500a01b0032a10303181d5913224240420a088501d4022680007400807407100c0307aa00301504440603294a0902da000955a52002251107018546009045400c001c02d60825144039030084032415014001c2c024540355189035810119 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 518917392 1250 518916142 518916199
    0x20d030e090106050901080f1b040e010e0702240a060902160312020901170402060d090f030e0316051e09090c090618040803090f01020f18010c0201120b 67
    0x55540c0140515904280300030900403e840e050440c02c100442e00064a6200c0c02807001003480c82e000c0c000398507011207a8234030064544a000d0280d445480e082d180401003824091000241c4840001c508040c3c40042c444684803002c48404032507408248124409410150881c041680c4400000c00c025040d0f10040000030641040c44008514a18020b040c15910340c010101180c41481351030306690300400100003000d03a2001d501150742d11071001400038010801da01d40b001d4900b996078001c00183c0450b280700da501907240c500c5690781a030308142c2e0700c1180c4a0340d90000510000104000c0c100340c4820307c2e02c00b2500144a0440c802440400d41d50352044800c00015406440301e03a00904200c100769801c20f4042c1e46144117140242c01c100180c0e00060401480500000001020b00c00c0500074214000140c100965680403c040c803420190841c0030010300751004000d41c26034075030203000428034403581a1103580b0030686a005190003804000b0503560840000440c03500c3e40700e05605d903848072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 518918642 1250 518917392 518917397
    0x240f0307210606200d050d0f06270603031707050732030f070807020a08160e06030105160e0f0a1502011b0207031106070b090601150e090f07020a020d03 67
    0xb0b072030450001c02c40d0064120042000411100805010030082650300c0340290034244075a481108110080042540360f000042c114035003000407882805804642c080b101d4243c038144400403140d0305070811034480d4400140880d401072107034921913084100700e5a00c1865402d11a090007a00c2c0c840306a1001d803110701400e403600301c0004004070300410580e601008140f20040d42404c0c0b000803040c43c544500300000c4d0a800300403406104654038007103080040c040c88000d9411101059a0300700c00440c080c0608450301c009400018028101440791500c505145008154080804030058607020030707920180781c0140040420038183d1300d4042d5040c3c0200f000402800040040300f03c001d08540f022600c569218011141d410040c0ba030014050040c1d82e0080440b00070400000300140961180c0e010007070035080031000304111468007040090480743d05628001100c905c05404a0b4404489054940d01130700c03c2c0c0c0400c3c10005412101c0d580254280100c0f06451050b030009030040b9000c4008500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 518919892 1250 518918642 518918651
    0x120b0607050109150216020f04060b0c101d03090f0303090301140906070905060a03020a0e0a0b1308060c04170717060103060606140a050307030615090302240f030721 73
    0x104500c1c0348844984070401002142003241b0341c200044910304040300070f44103140382342e41007000307a0300c0d90b008070010290f6511071640c8200e41122180c60390500340028008030b184c441d41040c5c4c02c1185594485408061015620304105241004030108a4403070058061105000140240d2000d208000d0341c180020440300091804061062400c2c40c02401d840130091a09410805d0b070702ca80c800d403022003c0c682000b6845000702d20003219500b98203800c030b070b5000414280c000340e641d0f5010018031202c44082c45103241d094035103c000c0c0c1d8528060301d5901d0103400c10441040031000c0821085070b0701081da019109415030390055030905c90302c0c05042d4203c3e0340101c00100100452407040344014852801c0030328140c0c029221986150007000d000304103020740000064802840baa11881c040c1c1354925488401403160440141440d501c1d001c02c0380140302135041400380d400d0020b880103c4c1c25809000a181051072080c00c0b00507040904100c0c240300303842400354407004400c2d200603001802d81c0e20014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 518921142 1250 518919892 518919911
    0x10120f02070b090a020a0b0f0c160e0f1603111908010f0905040308130303090f030201020d0c030506060712260610032f0d1b020f03160201120b06070501 67
    0x4480304010b007200c0d88507441340c81d1080060311101a400b04940304565034584a0074070201a452903c91004200400d000da098119031684484074160252000700000020716a0b60014044018806a910791024038a00304121303a014406c8d0403804003450460800c60814181549040300288208014001b0442401c01400006c0030703c10410028040e2106c2406681815180984801c2c406480c1d6480040101800303070505001e074110300e03681940a5640b4503c140e02d070a00900035007103840460409800c155607003800c80d00c24081d00303006100060003180f411929643c2d0310507030780b40325680c001802184001c0083c00c141c2000c05036480180d1404041c60703031400720b08014903400c5000d028002d05260000c4040d400301ca140025014058480c0c901c4100103502d9584c501da03010301140d007100076041c8403080d8410a491070003c0700075000c40c4c0031501a5100a01c1003500e034010044804d180000e11000a00035600c904245516170340a003600050305080b85010178602da00c45042a03596a45039821030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 518922392 1250 518921142 518921153
    0xb010e09210705010c05040308220b03040b07110f0606130b0307060207080c060f0d0c03110d0b0406080706120506010917030a1d10031a09010305061f0b03010510120f0207 75
    0x209a0341c551460187d00d002c0c00c50781c642205005040141e02d201c3c00d007403104406180d094409802822a01c0c0a0544074078051810704814041200c66200003408240c1d048a0620009500c40e0201420005004240e4401c07087c01507003002d21076611807454580a41c5095510f05008600c05094580d02130910181450506454038608070096409041c04200da100c000c01c1c0e8800b55107869801280c04a50f04405080c120081d1624400d045e03203507100020b1201c000310b080d50000d040c0110581e030a0005503680c400c1242c070b90761944501c0000c01c2d0440c80c222030b500c202c0d0303022a03840704050501c0b14000d03403512502540c184014401462a52000035003225480e089075403a03070040c03610342c2002c81920b80c00022541c1c41000480203020725490700304040b402803036000710003000d1b41f010740105035a40e500d080c03107070380d03100305880301d013580b06815084201010585400343c06039056152074610796440c1c982070007400c1e10160000000c006080d00c1c1981108802d00500c89034040384c0001580302e03001d03400d21 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 518923642 1250 518922392 518922401
    0x90708011502120f090103060806100f0e090d11010603081b100b061c060e101d060a1505070609050c010201060803041a0304080712170903070b010e0921070501 70
    0x71081035600076918403041e01c50300b10490300100c44820503262a03425200050700a851103400c0480350780194810803082c1568005140c2c01c40702c80031180c08001c0e41d10980001c500707005468561031500000060b6080c140a034001e003840300c0810b0000154165203840710b50280c2c02c15070200780c111101201d403405c8003200b00040440d504044000300042107444000905034410a44040c01641c0140c12a5410f118540d018034000c0001005008042c07800c2026005050750901502514541c0050440706e54100700c84540d200c1c0e08043c00c21080c1da41850340145080141d0152502089010000f610008a05000b4402e50510420040c01c3c00c0789000300290a41d000c07a0403207031940c0e006001c10070198012401c0440d1080308005115680e0300c0c0c0d402c01c0030451159403400b810103150818424869075001421200e990040340000b415038640799003184c6c580c03041c2c80028110004070320050251a00b8901d0550304110000700303c601008a9044400c0c991301808107018183e5808100041805028000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 518924892 1250 518923642 518923679
    0x209060a030c12141902040e030d02030c07020a0e1003150902030f0a0b060d0c2327010e0402030d3e0606190e060118030b060a080102040501020c040509010204030209070801 76
    0x103452500c00103145c8030112149100e010740300355100c446410400350184101c0b02609030140b005d540d286050840c0c42d00700d9001120032401803005090028040c3d56201c10f842c056411020400003051858a4004a2040c2c07129172802c0c0344da407110f881c2c0040c0d0b0200445002441248003a001120040c01c01144044001382164000c10740da4444100084485010005440050600c42a40b03260700184100d10514202030395000b0764851005100007010500030a0080501d240d0040f2585c0c95000c1c1e070480b6902075034001e4169003d480740d01074290017041c02020300110f0403050002004501240101da160b40f0108109140010030710000091040c02203a51002c800d2320b0320512801c0110f0011f550310030300e100b41c4860707981c0032000c90016842a0441003c842000040031141512420b0502c01c074442a02c0b550b00c2052420000200c007903043c002c3c3c85c00c81d9416000381440407581390600000c0d050007081d2900a540c200301c04001a40d401c1c41e01c60090105039281601581802c2ea490601c400001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 518926142 1250 518924892 518924933
    0xb030c071704033e01120b18090601080a03050d050714031603060e040309230603010e0601020c040605060a05070807020301060608090f010615110a35090a030209060a030c12 76
    0x1002460121003c4200b13034803a00d401e1801c504c0da004d05c01752640041008010b00ea50000c99a100c0701c0f24002401612400317101004283d40161f6a142841c0388d48014042c00100429001d000302981c4000d203a02c0290b112800c0c0c10084800d02c6c903c0d0010b07ca5504c01c9990400c0d04c182011401540c55051207444083d08000c1c401411505054402400800c214070420111186141c4d83c040701400514121546400181070039449585520004d2202c40e801c44149005105001164080c1d18050041030122034014040900c0c005c603520341121039500110040e40c0d004000c002c8040141c40034440c00c40103007800d584c3c48600e8105030b100c0340e00344512a0041e110780c1e0704200d014801d90883c50410105580ca50030460111312401406a00b07107000d5402c05000e800c154209148001d80d603101e081010003498054507034602c558a401d450314081c8902c00b503000799140805100501f000481180c1004005003c454120341d80d96550300002500c0d0062860400c1c16003010b001c11811200f081c000c880c800c0f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 518927392 1250 518926142 518926223
    0xf06060507020a0e04080706090c05040e06070c20130510050901030b0703180803070206010e1602060604090c03141b04050f04021504050a120c060305010b030c07170403 74
    0x2a0000b811940da540140301c444900400070170100007160080343c0c43e00b503010703c00303104000c0c4605121a034600a40b00b541d01407410311000c641800c401140d22446283c080d1034910401c0340d2500c1e555250001d00c4260007074a0140e106026141e5074210040406045c4040041594030f030582440306110303055071103d8002ca449400501c00110121150b0364440349078a00005d28000804505100c6450b106001e0b00134003002050087e81c99003c12110706a40d40906c0070b0085446201c40c8080501880d0f5600c1c0c010303000340000c200b403031525800441000d800703025842d030010788030b07100e0a045c10ba041000620551100258a4000011480c0010b06101c12a001c10036460408800842c107000100001c4c440c44a069824200b200c240301502c0107024044c1000400644905605581684403c1c09441810030324000140203032003805068162051607850b9070558580d4070381c0014640002c02e08075a0301030203144143d65000c151010304000c6001d420001c640b202c034000402c000d165000700095182805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 518928642 1250 518927392 518927407
    0x60b03030304080d11130b120105120a060e12030c0406081006050a030c0306030c06030605091003050a02060a02100c0302190806010207050609120d03241a0d1508010f060605 76
    0x6078080c0c5400304811311020585400410000640c1d103e00c03100e42e00280404100440c0030b0a400005c0c041c0683c410f09035910700c2e40c8036020041d01d01031904164100781d00498006c00054466040240c000102108131011105d001c0034604250304100c541e00c4800d10007007000c204480c0d1090656400000c080c51811200c1d042c1200100603229840101c0b0034103403204003000784130344682d1003a001180c00c440390b52141610707240024060603180c4519440b40c80207070086040d00710203001d190701f1264403100425041003a03500f80940c60700603401c00800d600800005c000ca0074550b00608800002d1381d0b400603550003030940c0c44052122110740200801150f41c3c200405a40c0018000302a0340c012920075454904560000b54071020100c5c8110340b81c0200061642802d415420200404007035042c8400040007107010880d429640b440f41d00101885050400414001480103000520718040c0118a0ac0001c580300b80c0000f00c2c1d9071001b0b0407a075443c21020010082c40c801c00300038110138503286181161 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 518929892 1250 518928642 518928653
    0xe01140c07140d1b081e060f0402010507082b2c0102040515120c03100603090809030610030302062211041b110105010b0a020d0327050307060b03030304 67
    0x81d6401a854900038410b1004016903443c00000f503000da005010302004c207a0b040c0f10f6070105210307128420f114859007080ca030140726100c0302c4400020042001307003d9a40e4507203171240031640180040c1e060040410007200480ca205009106c860b0b8203c5290300f118074401181401100c8207141c400c240e40c40d006030300c840031100d800c80d45c0381c0703502418542c13001c44400c0b211a030080c41681c0c0701650008062521411540100c0050000c9640020030a5900d560301d181401c3c8901c821a49107982c1185890300b486254026886000207601580b211820035600001092038030300d0076034140050201d40c1c00c04008141e810044141d021400c540e01c921141c00305480d01c0314034140c0500007401c0d040307440041410741e1103c0c3c1c4180c06c582d00130580c04000307070f0f864007000e080360340d0001a820036942001d001241101e40c003011036900038000d50040c0402d080c590f40441c001d2203192a030524884640f2813580754100800542e880c418010005181d540000b842c08808540d20445400c2c0030342c00500401000c87d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 518931142 1250 518929892 518929903
    0x306121103122118030a1206050409080a080c0d0513050c0609030a020603060409210f03140c0d06090f150801090f0f080d181a060a1502010b0904030e01140c 69
    0x80c6140741c6016070f500d0b01340291400050524602c1078510011a85a90480c1d0240012031000031580c0108041500c0c0c0307051006a444080015041140800001e620944625141da5103c00e650710903030b0a05a8140690050358000e41e00c113a4131410010030a8203000040c02411903540080350201c8c9050710280101f41c80740200c4601a10825022001034113f4a0303d8001c0d440e5168048950016511707401d4030815400d21603002d441c00105d005038042011406071054140c01100906003000301c0c0d94081240031141c3c004411030001035218440001d404006019400502910f03c00104624100b40782d80d80940750030740d204c1c3c801b0741e0402400380003240385122000070658108400c540c03d01d80c0c608110595105c1c4e040c0d46080d040c501141d140340e1907070403614803112070703c510300554120030b142c503100424007003e80ea260707844109140108900c49101030f40300c1041e0710030b000200c3c00324103c0c0d0001b0b00c400380c211825001304100f050780c0c400c41d42c0d000340e0300a40d10301d2882c009410300d81424040795986 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 518932392 1250 518931142 518931187
    0x20a17100b25290417090f0405010815100b0d05060d0b09071a0708031506040806040506061f0e010e0310060906050301050f191503050d02010c0201063003030612110312 74
    0x25500006c11b01c0d500d89450007890004031014209210a59440b0365081e40c49084804480300ca0a0010100d4103502107080b1070340443d032400c08090b0900b903500720840020030020305120783c41002c0c1c000d1500010054241030344280b0101c0b026100706890035036400103080b00b4401c0d400c0d514404208a900003a110310581e40c00c003400d14100c02103003030181e01007000c508c0345821801c1036225120800c4200f00002134014841c0e0404d482400403d4107240b0040350100d0800074000c003040e1110030f0396500f54403d044454015000500f22951040c80d8840002100c03940d07001840d001d82c0342d060038802070409014098100c048250000b0042c588550f0005d070001040b103000030b0341a11124866010301c0703206070703900145400c41e0945100d0b0100b12000f9000380407190320301c40954242500058413031248202844414000c542e090001d01035050701c106005034240046050541d035000101e0200c23840c106030081d040c4900d004102c0d0784c00480802d850b01c5c550032800d00407442e0800008208040500b1100d151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 518933642 1250 518932392 518932433
    0x100e030307080717070501090201120605180619080f010605010f0f050f0706020f03090c03011b120615020a0515040c091805060a020a17100b252904 65
    0x442070340e860060007801e0211038001c04c01c040813030103a041c410194090910280b00362142c000362116002618141c43d200d105107940303c0c008584103003180080040032035000c94024160050507140d503513014a100203a40014400b07a100640d40d15041100b4407441c00501000d0030407070803031042c0007c01428820699140000c0140101d5495000f103010030907030b021390740e10900c15522a207001c40440d0a81d041214804e00c0340c0f140c0d924070900703030406200c0e00d201c0c6001d03094413030342001901c0410b0340e44003074410070100c5003941c2d03442c0010483c103040401d40c0000300580c0901031103000f5040031860703c0c00440704030698000080170310002a01e00301401045841c07003070002c03a0440300140054512119980003805901070882040500031150303005041440044d199103104c0d1420074003400c0071080c12990718288d1150030700c0c140a06c400f20740140c02c0044e004100300147c003a20400c1d485a07a07078100e03821035111031903200c1003400e1403030141d10010104462800c1c0c0c8039480e194035403014441d0099012a603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 518934892 1250 518933642 518933647
    0x709060f06200a080a031401051e0f040c08010609060801080616050d0603080d5108071701020901021e010228030501060c030806010315150e100e03030708 68
    0x4031076000d030700300942942042082d43d010008a080c020416800915040006483d1000321400d8491945055050b150082c00200c8c20701440e0500c420820b08088040d507001340100c801094a176100e0003480c00d84086581c91001e10351500f58041c2c446051a0803090500c204100180304804001600e50380c401e941c030002e002001c003107010a592900c1001000c1980c0c0d4144203001c4140300d03200b0010031005c0d1400b001000180f00481684000c29412150a1340c03107601d1080c01ea50889800074078440c001c002040c1c0c400ca11500c0102c21200f8146070744440040d4005500030040010000700360084440c84400a5140c400103100007515200415055040420b52415410f6541c1096060755010745100a000d02800008015200c44141c65085000024200340000c03d810b8410458100310a030700d0741382c4e000651078490041d4045c0083c0103803140c0c49c100303160300080c0c00380701481e12180460a030b48a02d00d15401c440c00340090720401007001d0003030045450200c41c040c0c50000440d00714680003c0d5198 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 518936142 1250 518934892 518934917
    0x1c0c020d060228050f040b0f04051e1f020c1509061602040b0303070c0e22030305070206150d2a0e0114010306140609030c210709060f06 60
    0x150080800c00c009400386101192400c000b281002c1c410f02504844211450f009480400894242c4203c2c0c1c2403200700402840f04010140c078610141000c1801d00d04480d04027a20340003c982c003003200c85503030295905c8510003225141003144244088440701d01c1039403070440402c60040e5032640920006400340e90410401c0c2203000014054541e07802008100d2641c5601c5280710240141e88a031059100d58600003c04070149000001c03943c40e19480b140944c8003a103006680e00b03c2c114001d01303440101901d0f00b903413040c0c2c40b90700655140003482901c0016007402c000100901e40100205507103002d8011401d022110707900d0301d8080800700d82c02a0043c21041c40030441c2e10313000c80d4002c0074220010306c40001017642c1030303944040782c143c841c05502c2107c035a4900300110266042440380b100c0310124a203d290300d9042600c0180b540d02d90107011036500007600c901007203c8411945902d240440520421004520180320050040c000c2d01c5080c44401d00b808482401d524103171107030030240301600781072030f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 518937392 1250 518936142 518936149
    0xc03020106051c050f03032502010f0606050c0c0a260a0510091505040305041205150c0d06090b10110f06010e150d05060103080a120213050102010e1c0c02 68
    0x1003025000141121049030f180c49590380303403140d160780300321018014020b007500c1d400c4000090300e1140314a034000d002c0b50940c50f408541c020100c58802c6003103540f00c03104440380c8541401210010142c40d40c0300740d0360b400d0b103040190030180900410740c803940409004118904580003e8280240d042d500d00300420081c4105a2410b2008180207109001e94880440702159030350001980c0c602910348008900345c540006401c94504440050106000340b2050143d80035155103110380394411300899a002c5602d50a05410100c100d810203100000010110f00c00700c1c2c140239a40c02841f241c1014044030b40b06000056000000081e0387c8100000c0303140d4040a5030342004101c5036403401e00b00355941d65031921140510850100d4080281802030401000c0794200b0103490640c1e680c0280c0501896400c1d540c6260701075120800210810101d02502c07400540b143c4004c11180c0c250131188418149040006801d40d00b40b58541c1e20240c0100071041085440c0000f0174489440d60700d0a503901101700d2001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 518938642 1250 518937392 518937401
    0x100e1f090b1506041716061e05181e0a0909030915090e090304061707050307140c01020f03010306061a030f070521040c0801151404020918010905090d0905010c030201 73
    0x803402c0700303250000178403480e8004244010904c0204810f00c80c0b403501c520f800e444000c07400d62503c50b103200d180c1c111455540300300c0c007400c0c00c921114001600e0420101c001281205031301c40c45403c2940545034441c05141100241004004d0080c0c180441d048a0700c014110500780d01c0b400301c4c0119894071429415105060041c0a080ba5114040c01c03402c241d68500e43e640c00038010040480e400700701240e207080500641030310890312591003628590305c4040407101da200f10204c8180c004010710209130400020b00250600c928010b00558407585141040001c0c0c82d255400061800001c1003944500c485200840c1c1c1d11801a900800550b2a01e90045515200e09a0200342030810150007621710300300c9280c45d5018500501ba48140300c3d0300d400c0303240d080301d0401e1501e00161075101410006050443d0095410f158018030050424194030f011441c40d00c0081486030b0314403519001800703050540e10642d03030880611001000292040c140c040c1400e80301c3e010300c505000030004088100741c400d400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 518939892 1250 518938642 518938649
    0x20d0306060912170705070f0f0e010b1b01091203140a0501080c061c091202060609060306060d0512040f05030d0906080403051c2a080402030d0f02100e1f090b150604 73
    0x2c17600c102340c1e219013600d420650350041001c81d040d481000900c00f10f29643c040d050b00d0a141525142a600c0c0c0540040410f40394101450342d501d9400301e00c0401c03625900c003403c03c00c40f502d001c5200070050b04a0f50a00f80300410150340a841c01c801404060400117071030301d40e08025039100e41d0752010122a01c40c030f45900c0b0090795a003414643d112003008180c0070064447c0344240c080f11400e440e04420030a0a180c1143c020341c0581c05440007500629000e4480207125000d40c043e180e03100005980140140d006400c04500500f84403c20061400d0410a46403564200c0c50120309a50521000420104002c0c02c0501002400b05807000100b40044802000340e0340250100b10020181103101d0701c05ca800c613500c0c00541404000181014001c03600c6612480d07006000e070220510400301515045000c4c50382e141140701d50542444d43e0821441010741c4a0071311390042c801840f0100c0901e0140c0c2103100d40301c4485040000140c00500ea46100d6a0041203031082c4925044a18002c2190307030241d6070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 518941142 1250 518939892 518939903
    0x9051606030207030e040209010e04050a0902030f0a02010e0307030b040605060609030d030b0a140a1701020708160c05041407030509031e030a0b0a050102210d050403020d03060609121707 82
    0x9900045958165006007640380c460340750351010702e00010810080f4002c0000950204802035118030340c620b00ba901039948811850307000a8002e00c290082032800b000100c0000d03440d401009400c05542e04810b00d01c0c8400d20407002400310700e08640e90110758450140c001040b007500c80c0c012601c16582d01c03054400018014040310b8030b504051000034003a0520740c490502410843d440410500c003214218580080003901c2e22650300e00e000c1c40a41e1802401c10f0174002550b0901c058000141c01000510915040287d010001c1c8540c2c14079000412660b0702c65481030389000400900c042000300d00030351200742820300103042c0d0b58951141e8110301c41c842c0441d5003500c610304034400030301c05100658018144001c04100303000b107450600c103400740b42c0d01441d809a84a40614004070041d16594803071805214005410002100080700a0f68400d44044025800c46034525210035810f10440303004080d5482c0c0712404c2e03032414a426400b42030080020301902c0d80384511001500c4088103e038050383d80070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 518942392 1250 518941142 518941183
    0x120d06030803040f110f030d08040804030206130f0803070c2310050a1b05070b0310050303071103010e070609150306030c080f120f0a1d300715030905 66
    0x911300b134a07088141603412507880300c03110301103445400d011428000448000e0010a41c07c5441d410641e9408401082102c107281e0400c0040010707190712021b40800c0015480b500038550900101c0e01a086064002030359540c07090020002081d41400c0e05811a5111400041410704170103658400d08130743c00d19550440d04401400e20040c2e4800003c1802d50625981d41c01e00c101c401c500700400007e20031014003e07a020b0041402098901002950030020f076900d803442643d07803a4042811500041c20a41c1c4243e007910f100d911508081c0100500c24060303901401c1110301340f40f405030001d8114000c102085150781a080c0e5614080c0d401003000d15040446002850707603e07550940d44030b41000240c0500c0c0503403284081011000c40075202c0b03900c2e107001814140b1000384411140c401c111039050041035214520b00100e42c68080c1d6641c00d03c001400113100000d401f080c41004882c44070310920a81d405000108040d00541240001560f446c0ca004510056181442450041e01d160f54240c06000b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 518943642 1250 518942392 518942401
    0xc0201020c0d091a03040c0902091306030605010306050c2b0213260d021005060d1b0303080c0c07050609040219090602060a1107060e070f0b030f1008120d06030803 72
    0x1001e0702204490300710300007600b0708003929882c1300180020340b8018007042c603513041400141d1b40c3c0c0d000380003603017406040f0009940041c0c140310140c03080c65105175606580c903401441400000c0c0a074070340c0144140c2825191140041c0d12400c00c00e40520030300380c581525441d04083c071000f47c0458603d060f00180307582602e41c85511000c441045001d4070600b02d0011aa00fa0510704082031141d04245581c015082c4040d11b5aa100050200240032650060b03a041072040001c007a0100c00c960360800440700d003039903811071a014041200160103409410820b000446110034001140016141e06580c01c6881e401c0200128019004144c042c241450503205090707140c0e5880100c40085422035401c4172003e441f0076000d0b00440e500c07884203840121080011a012a43d5130704299600414030b4115107030035030344071031070340c0c0707020742508400c0c3c41907000014048085041d1040a401c03000003621409503515007101165180080b00c9146c0540c000442c2c030b85e442c1442584800011904000c20903981d280 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 518944892 1250 518943642 518943647
    0x30c01120b044503031a0a06120b03012d0603020319050105070504031101180905091e0105010605070335040302010c020d0f110f07061e0c150c0201020c0d 68
    0x2c03452a00d0400c103502100746149411148003c10300c1c040c15110080c0a001c6910120081d06440c8182c0c484002001e828003075586880f2002d900030407103039903114130000d03c2c03100ca9416200001143c1d442a03050800c00559059140d4a07510411160120b0000b0b91400325161800b4188941c001703907040c00f40c2e1400c050f55580e03400d440c00700c00d4880c10003040181c0d14204244c8441c005c034000545800d240708800c0c1c074554000d032814451a0b02072a2010f034410394407000002901d900305ca19803101d800c0402d240010001e08078494524030354000c024000e541c14544010315074010144003404008180d410704841810f00d5081c03440040000c40740c40c41c94205904840303d0300d03800b510300710015843c009c40d82c072a16101290301072541d0451f9640c0c0f00c034a041c640b0102c0d0100100381811070140202c0c001d41c3c01604007003003c80c00900d4184c550048103c4130035111400304072000700c09001d015800d55020001802c1c520b241c500e403009003030f00090422114008074028003078400003442c01d1040c1000030a00f04d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 518946142 1250 518944892 518944931
    0x5063a08040b0901020709050c1b03090a0807180e1b0a03080d050f0c030f150102070819020405090f0601090213050913050111070b0f0411030304031208070806030c01120b04 76
    0x80c217030200c0d01944c2d907402651084410480351101440406d03c83c074001e0403012002c090501d0682d00449051642c0d0b41c002400600705544185841d45c441d40c1d08004611003004491f100340e0050030200280051030040944402040403820304904030081e43c01d065548004848005c0c5070880061901c9014103590180201000e60b42d6408404042001035885a4904200c2c4e12070b521914050b200b40d00c075000040c03100b5800000d01c0d819805204c4001c90030b80307000c0141808102c0d1030804c10900140030b0040c04210b9002602c8407401d60403100221500c0d00300041c55504580c0c4091006959240d101030b80040000c485d003280e0303440101a0181306e200b2600c40102c100d0180100002c1026a540950310525480b4000b0b006180e0311072040007076001c20100c105240d10a005510740c440c1c0301e01c0200040c1c25070b030240d00102c4240b09018140713420f041d0b11202c42d581c0005103040544050a140c0e00003079503151400600ca0410200d4004603481d205685c2103401d010f94081e00500040c5601c01c400794540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 518947392 1250 518946142 518946157
    0xc170307140a0e0d0204020405040e01050a0c09080a030804060906050a05091c09030b04080f1b06010e190c110f0c1302041a070507050907030f05063a08040b 69
    0x51685821404502041011a07501604607251140043d22a9081c09102c0d400d000c1d003a0380c040e40c00d2100142c90344070350164107003601003403000003800d20f401004182101c580300015010020390007800c2c0041c0303500107180c40500da003600703101d482541c0d18034203a0040d00c0c242100811309420702042c0418101c15800030b0380104107680594041450180e00e00340e01d50300c035880c0e0b007000824401080020440541000c0d400c54000c0341060314241034400d01c01c3c1c941e4400d0001078068602c4a22890351202c09100e80740c05440c0d410401c2d01c0390f0502e10003212007141d040090040703840d500d0713900048850190701c1d80302c4c080444c00140c5656942e040c034065205c1218071082e034002c202c08407881c54420400c0c8215400c1c0e62090300668460903190305002c2c165000752404407120b10644c4000b04a079541d40d00c8552060b0364541e4003268441084111a05644010381524010028201070454801d548a0348101c070703180200d4070440290035200180c82c021b0000380c0c0030f0501305001a01007100d280d14801400c0f507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 518948642 1250 518947392 518947397
    0x109050d0903030807020f061b04030b01080c011107050303041403011506090816180b010203040e040b160503130312141906150512151806040c05070f060c0c170307 72
    0xc4e958441c07046c1c0c1c458102c01901d615035000000020310480044d80000c00e1100e42420031801c0c55101d0307030358017840202030f00410b58075031000000010941e4003a82ca40c82030704006015140340351800f00802c1d40c900944c000d00e0100c4040f040b03d060705440c2588560104501004891080b40da9203c0140804e41f460107601ca00b0301410350617074000706c5000f082c81c0c1296105014400f04c60509400c41d0010000f60f01c0c0380f41140801c0100158800001c000a40030740c0c000c1603500302b10300f407030b940c1c2c504188500540781007404820b01c10402081e1105040340da1044d0142420003a040d80100310300e0040104280c0381c1c8091450900f80210440015241c408103880c4a40401506441d90807031202c4a03017449401000610400c03403005c0f0250310098850308021000040409805014005840e418600c1e01040170310034040204803d519190160600514840c24101d02e06586600caa00101c01c2d184c13030282009440300e080100e107602c03a0741c0300f9180740d810000c5100000e42c203081241d80c41d881940c06000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 518949892 1250 518948642 518948657
    0x51303020d020102093d0201022a03070f0203070909050a110d050607110705100509090c210603072c070801181a03070b0403150203010f050d050109050d090303 70
    0x540144225050700500401c00c1200c070040582d10722181c03d2404038006c14014a0f4055200340d031b4000a041c0c20040e00350000350712000d01407450600001d04c040040d0a1030301c01110a513113040040120340740f41c2c6d0401d0310b00044c1c2c4003900200e454030051707501803004907250010040a000001c543c0700c544500c07405c1c2c90000041088104400580301c3c6101400f80d0b007003240800d080078095481c1030039414283e016158919030720f00004001020300707032110000c82c20000303240c911440c00700c10300d0f640051a5002c1604003250681d07080300c001000504804403100c40004288680d40801c0240d00070090f1100280c05c403101c002c210704a060114030002d0144658401142e00b80c1c0c0a9211981a00c1c82020440e01d041100c0c0ca0803400b420100440c0180b035200005d0440154605001e203001800241414035030310381c59032602410000c0341254481400c3d1040c00148444034030317a4134400864004580c582c1351140103040260041050210040061050200c10003103680c000b0085c80449000351500c21 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 518951142 1250 518949892 518949913
    0x20c09092103100506160f1a1f15050c0a0c0f060f020a0f060e07031b0e150409020112091b08030703090e0c07050106090605040e19111305130302 64
    0x1024002070707a060081d400030240c20304c02410030078090401004030b00c80900083c0003544038a9200c0c841e800b0151407500683c1213800c0c6e400f00c0e00f0713142600310301c4544085480420b6540380140c001040c1c05039100d60100002d0007505c1d0740c85a41078444680015003954242032a628103612000c131a44582d00c105103d00c840050010300620440c9211455600a8801c190305651034024003a04020300700c842070b56036072020b00f2200c010480d5601542c4211482d400c005181d40303800078580e1042d884042403801302070401c400d0303440b5034a034604c1040c0b00f170342c0c04240c02c43d2910060760000f0300150314040300f5140aa0000c2440030784901020711011545105070001c0d105e2010303a480e4803c0800203800b14050640402c05010355070421644036103d1407541d8182a966a581425030714036a10205089440708810302c1685440d11901505042c41300c0208031802028800d1100c60a44202c00351403000d80d00914140e40c0c032103401c4428807002c00b81040042e032400301d082d00a820740146040c1d005104d2007a40c01c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 518952392 1250 518951142 518951203
    0x807080d0507080409090c090c0c0302010612150c03110705010c030b0402030c031305010f020c2104081e0109080a021b0415180902090103031706091b03040201020c0909 74
    0x3200e040760860f0314545000d08041445006c3c1140c15030450340602e0340107001a4500c011312179010111000d5607070202034103c5060090070342d0700c241c1207806440c013980040400500c03105050903040c4255440440c44108101041d4010540000d108902c07880000e2034100304001948140c01011498a080120f004074030b003440103c2c0402c441c0040b5000d4100b022509800070300d080c0c0280b042c402c00001c5813441040d01400e059070402d0340055103941c808800d000800d000c03020380412a07001c8941860800e0b1400f8000c1d5034401e014114142c071980c5854540c9078524017904122141a00031654a541c1c080c160002036440c96031041c004c081101100b89241945424010800541400000405c1060516640384840d0044032891039405035194a030100580380d0382e008a0085000340c442c1c0c0c145002c51f1007400a0440c00524041c810321072482042216080103aa6270039950015640790340700c1d626031005030320700300d5001201c1d82c1c82100c1c00c0403c15080000200e42122a540f0b07848290b403400c1802c2c1d0b8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 518953642 1250 518952392 518952397
    0x21509010b09130c210204110f0f0318070321090605091201060f080105010302031e030703080c09030a060c030c020114040b0423010902091509040b1b040807080d05 72
    0x507668019002008120041010300031008158040c808072100a40d480101141c217004c0084001c440740f0f007040000d400d51600c0e02c101420058107560301c500d400054903901c240c600c80c000841203094404004582550407180ca400d0341c030300401c0c0c119400b098a82c00e20f02c1c0151140d0644680c5240003100c00b2024a11680d440e074101c40498484505000c40e103c10051644159440410703107660f10000096000400141d400041142500008003941580141805c0c090041240e90b95500e003213041150301203002040700c45d119010706d440905510740001c03598462103400081903040c400c040e83c1c03000307000c0340f07030b008115500403500c0410150b15503e10503405d039a010341400b000800c1103000540840c82020780d295000b03201d00411460301d0701c1d20307176041c00d25540900c5811650390350300a003000310f00300340d0003003500001c00350035091a0204c3c040c00601c0d8420018802841c0000090105d14280300e0040c5042810f2414030405d40ca80d502d44525554840040c82009001d100b500c092144282c0070b41e04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 518954892 1250 518953642 518953661
    0x91e010f2f0318070f0504060b0307120b0105070203101a0d0c09020a0225060305010b04050904060e031c0e070e010e01060e060f04030f03110d0207140609090702150901 74
    0x915508400410303078249180c0d000206040700070b0520f8441100d4242c0144010b0010307001c220344034641c03542820b05100c100e401940003c0c1d28070408005208080f90040a42d03071860b01120b80104000c494040100c5242c0102c8800a4040c4102d00d40e541e502a5a60010414203d444113080f2002006004100d45008141000344c460281c07010140100fa40d20380090582c031043e40120b42e515540c10311401ca0800c0b9200700c201c3c440308240401d1008907898007032540140b44400d203d82c1014101380001b150380101810040c000c6580300324110302101c042c82551600503030789003203034008510b90710f544000d000e0582c02e9098a00901700081215031543c0381c41c505951010310560703201c1e0300707003101a641c0061a1190940c000014003040309a020180d005102541c814020403241c00e0051030f015102c07040161500a16030070041120301744c541d0005401040790301d5048a10000c0d00683c0206515200f04000e03150895403440420012540026030042007074018148c0d0351150395211030060803076240c001d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 518956142 1250 518954892 518954951
    0x60e0705011b061512060608010203010f050d03020c040618050906092d0303160806030a081c0b06040b040e0f0720151501030f02090d020603091e010f 66
    0x408012015103078080380900c59200f441c0c002900d01940d9441c60200d490380c1e21203a144c050000c0c011003009440d000b400c0003040d4000c000e500703550419501e541c80c0050741c0281c034021110300d01420301b40b520800c000c00b10281c0103402003081584407000640d610340d511504408460a29000c2040a200007402c81e105120100180280c51882d050341c1030240002092000701036144496030003105801d00c000c1d40101241c80421409200c1050080e0a15500800b49441f0b508200d25001c0800d4080c0704940b0000e61061f8907404151f00168803e0041003071000d06900048003190220b1001c400c00e008209031030074103500c1c8010303989002c0104140b6504540d00000500c5640b080c00a1105c100c12501041d007000e0241c2d45031160000c002080d201e81240d1490042d480c0c40c4403145196010311a4008510140d1020361814011001044940b40403044c002e01a807400400510409010b00c102461140201105407120183d600e0090280060b41007103400c0a00e8501e034500450748402a0b8100030b100d19 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 518957392 1250 518956142 518956157
    0x60f0c0b0f090f010e030d0c1b08130902070803090712050309041806020d090308060406031e021f0225030f03030c230408071d0c130308030112060e070501 68
    0x6510110041c029005901ca6001ca0741c8048000303000d51030051004000541d1a440c0c0050088140c8c3c10a600790014022078080044020004407800301007650003040c1d0302c0d5100d010360941c00400c3c0e21688201085440850040e0400030002c00950264400c42c04503800e440e142d4020840c0c0f103030148002031440d4003c000303005190074075400480d0001410101c40d0b4440a082e103906e81a81e0110265036045e0b90344101035003c2581042200d0b410610956080003500c0c103665403210070740c1d6081c0c04412041400c0c8081800c41d540c0880540003500429203a20011440e070030007950320301b000b0000d0020203c7c0a0001440c03048401403a03130450740c0158034034283c01c505490980040003102d41381e800b00b0151503411a44080708814245880e200450025075030f80c07070000c803c1d08118581e000f503501c00e543d1144035840041d0040300c07290000011405242d4690b1031000c0401203000c0c81d8402421413070701200020300c00b000300744c80d0440c0c240110750501c803070200075002c44e480316402d005950104424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 518958642 1250 518957392 518957401
    0x60c100b0d06020d0c0201050a0b010f0305060609060403120905031f05100305070b040303030b0406080d05220f03060e0f0d0302090d06020d09021206040201050702120c0a0906060f0c0b 81
    0x1a044196aa5000340c5031039501102502c80030b0699009800d0103906039210510541e980b542441026440180700c1010400e250b15100020100c451014510082580301e5002c0341c46580e03510101c0724410303c001e003102c0d03840da0340b0715021044d0034211401c20003241c1c0031b840c000b41504001c41d9001d0400c014211030201010b010f40514020709000d0507052030f0710190040480007036402c00c64280071384807012100d61030700d195140040c00d440200003030074000e0b420b01d20700700720702d61000840070700e450b00d907080042e1200ca00800b801d103607809640200004040460740007500c4048801071100b901d02814017481301c4060003401c241c2e9116020340b070035007603480300b00c0d81d0000c14480d60280c0100080100b10501e0309810340c031000240c4e0000b40002c6100c540d00c40301c100c2149800080281300c002c0d01005800f032490300c3e40002e009070041440c0640620301061040142d58420f0100700b0034004028803d200490b1500415401040c0c140203440114088951003200c035802560045141d80d070081c10b500d190f0740c3c4e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 518959892 1250 518958642 518958673
    0x20712081812250803071e0b070c030f031a01030f0603081c05090d05091e030a05060723030411180c071208040203061302030f0a080d0605060c 63
    0x3000c400e2a008075074030301d921201550ba003102c071810300808400500402001e02403603510740ba10003107656206103040d001080290408410f540810740c0059070091000ca007010083c62070080355100810b1002c10340100b005640d0425107401d01c0c2d50184d46ea0020f401700801c4140c0403248907494060f0000f600403210b1800d90310a8002014038103a080c000b050003552a6180c11003030701710340d544414480c21070003040b00d464214441c8035809030405004040b00801c070a07029204c2d105483c2503a002c0c0da0000051100400c2d58140e0043c264405022144921030301e00703141e0344a072800e0310303183c00042c81c401c081540c040c4544039040e0700c002150381d440d14588840c1d94040707600c4400c0d0310072504403206d8001d0b148100b1140045c18800c481c050070080c0c1c1d90125151800022180517010360a002c101c02c180005a1070001d0450790000d1400824050880c1741c0c000a40781c000302107084005481001380b10010003c2c500060880c0b1001058188502915042000018000c140590f01d4551003080240030580707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 518961142 1250 518959892 518959897
    0xd0b0f07050c01020a110c04020412030810050a1401020f1c0806040f0e0307110a06140c1524120303040305030408090603131203050105060d0207020a09090b061002071208 75
    0x400d42895072601d41c1c103008160980e0085440040403030204c580c03809000c0028442c5c1451114104c0342145402d052014040b19410090005020084c001d400180b64095001d03408000d4800100942a6641c5e543e440c482e03d07085e894000c5005000340c202460005500099280d200c480f61001d01c0b5840e140b20787c00700d50742100208415805610307414111440421031081114450301c00010303556580c128103100000890300e0003020700612003048100003050b44030030300c4c01004641e000d19503611950300a0303240c82c125000094500903a8800240000c2911202030380321410070110084e90701c2d06010040060315100d10109080503081000050300181c440ca0003564041d10980b25181040d5035107020500b00c2e0004c64440903006400000e903824030011240401078035179540360500040d070401010400f0fa00400c2a4564038a8020074004215910705c1d43d40c00151994003001c100304000f0741441c4010a0080c0c6141d40524034040813500543d102050400a480b102c00b00c200c840351081d92880ca07682d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 518962392 1250 518961142 518961151
    0x60e011d01110a081803060705030408040e18010c0201020901230703201f0e010b0d02060d0b06070605060405070908190314070609120906090509040828020106050d0b0f 74
    0x500443c2c529000207407004002d0301c80004034007415000c0d500c070001031600e4010050302c1a0280039082c41000300260b000e000311402e035a089921724045807540000b8201d070007403145219509500700240400c080b81d0550107003e01400c00d0341c91051252582d103950700d01001c82c11403030b00c44810802c004000b0030b01940d421081d101c40310601801c0300014080040c140448052282d80d5140315001c0100d0610b1540220006400300307000800c030202c0b250f00015030b005541c0034001d00a42000c504064081c0036030f0300003c0380b0000070b0096179849a461810070018102100e4a9224918240201ea1200d128494007020384503980028000c00f004814216451691180300f18204030300c180c91403d032030340b101002e000708511603280407801111602e4036034004181ca0f80c2103c20032104403030402c0110b07442005801210029164903a030740e280c1d400e00044522035400000850b0206070f0b400d02e0310246040c84d41400d80480d0f402003004640300e5040011120100501a046100d503202140e081c0a00351a100d410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 518963642 1250 518962392 518962427
    0x5070911040305060f0f0a050603061f0f08160605041a0304020d080d0207060e010b18091c05040303080708070509040b0406030615060305060f01021c1103040f060e011d01 75
    0x900c0d07503e41d43d940ca0310100b101d1880f07140ea18001403019001e41c000c2c8040e0884403401060000e4502031020030b5031414010720906002d00480003403d54204400e20741030240c40402c0019142d183c03695405582c80b81052440a09039001444c00144540f1480598055401422049083c540810107001c103a8002401c184e07800b2040c005018001583c1c000106003031143c0150240e201e02e00360400c0000c1301c050704903510850341002c1c9030300007603501c4107400503507400d9402e0080b1464441120a0345000d01c4951b00400b8103000051034455142c02001030004c6a10a50724400141d60f140000c55580f10240c4490010541c01d010903003662400e50860302c10303400080d00c0003440c0c1d07a894a4080c00e0700c400682a001c100c80c03a110500ca8194980070310740d0b00160680b81004402c1034031000075641c6130b07105078580c0d072401c4071030314007c07010f101d540c46840c05071034402225240c50b160314207002c1040051040328041100f040381c1d80aa5401030308a114503060300d0741d00d8180743c044c0c10019501d603600002803a58 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 518964892 1250 518963642 518963647
    0x10f05060f0f0a0c031116050d050307050109050703021311070828030608010f06080c01050c070b0409020a0f020a03020a1707140109030e18011e0b03070810090905070911 75
    0x188101e0080074240100a6588941407500c0e217003400b070800b00511080c090316400c20110440c0e450a001d00748030448001391542c0c18105102d00b03119007103001d40c42e001805c5509140c1c8100a00c20700003141020b4900840e84000410090b81550040741c0e800040541c000c0c4042c842d4401103000032000d48000204021140c410b02992840e40c603a42414000f4540840d80e610300510061400344203105030b1f090b240000f08007480c10203d260742c0c1e9213181c4007aa810000700043c0d40c0400c04003031000c4002400c0c05136010751030b9511069408060f400200400e00021440a01c10291a00c0080d184014a4140c0c015125000450f2526100c0b81104046071001c00400c21403140051081840c54004084c402c0000130b100843d17280041002e01c030b201400f4455507041080e00101d00e0074204844c111007900403440304c007011408100c90000856440280b40c2c00000c030803c006190440211386c4a2905c0007001c1101c2604c1d500c40304200d4000c108050078650140c042845070700210342c0040c41c02041424100d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 518966142 1250 518964892 518964907
    0x4170a090b03160e060906180a0b0a081501030b100309080415030b090a05010e150102150a05041101180e090a020d0f05121602060702010e04051f0509010f05060f 71
    0x3280c550003a40d58100b121059480900807542c441058500a04c0450b4154502030703441e0009040c1d40500c142c2410350f080d075046500342036a50100c1910042c9400e880d8507031202e045900107051200200c0d10303090745188481c00e19110758130038401c904a04000074540b194600021200320000d14014030b003240c1031502040301003907610000c0c44821412115035004644a9040030134000d001801610030010a41007070010f2024070344400280f9803168440c1a589505c46150300100d00c3c10208440c004c03d0400303554144140c4619179004103105a004e50035412800c0001e4004480204c3d048001520301d80000c0b205011150040d0b0005030001c1014003114118003281e0001910b0900d803880480344582c1030400740d001c0000500c0904045003024100c507003404401c01c3e0320303114503d11a10003071180000240701011680030b4424090340050191042115240056509107182101c109031100c160314440d00040c103160682e8840c0c180c43c000290031404519000c01e1049540100089868903c0240700c2070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 518967392 1250 518966142 518966159
    0x9010b0301060b04091a03060402010c1a1503010e0f0c0f01111014010b07030c0b04062a1101052707120c050103050a0b180c0f0d021b0604170a09 64
    0x3800603010b0301c122965180d01e0726040504646c0c070514000c100740004040301b50103680c089049035020742c0a091901030a000c42c90b00c2100241c0300502040b107070003107c041c0440300340c03041d11100100400794002c010401c9118080ca03036401410800700d91650012060014505100c038440011a00c1070400800014440384070904045860080d00009a5942003942802450440c0d841c010f09020180301d107850803545009240c0c129110001c0c00c480083c602003400c004081d4001081e03180104111001c02d0444914001030b0082094508006142e0b0002261452010b02c60540a81c80b009085054600e01e03100d000103182d0f0050540c10035004550000031800c50100d007071840a480b904503d60307040c1c2071a0016003140d80c09014810340380d1414803481201e0300c803015020414040c42501e106140c0c0c41d0185100305124921a10411410220b401341c1c119143e03070060042c684100d884103214908070440c4658940e0110303405000c0c441c101d05c1c441c0703000d18003000805110342c0b14a000c0107420340301c0b4810b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 518968642 1250 518967392 518967401
    0xe01121826030a0218010804031b080c1606030501080102040e060f0103020910030e061312030b1f020109052118032802030f0f070603020d0f0509071e0b1209010b0301 73
    0x10340f0035168000079203620808000d0301d24007003440d003401d0061a42c103040d20010550700c8501503070a00c1210412200c4103000f44c140c15182d00c080c400c4201c030140301e507030b180c800f154001c1c620540317020a04000000c10f010303c040c000c3d0b0302990011301918044d07070b40d460108160621841c0e111418107600b0046817005031a0b02601c46407a60050310003003114032083e4405031a02400a00400c01341452036810310010310200c00f0880401014980800c0800318680000e41e036464007150020142003059052000c1c5e0703010340248412034010415150329844807861484480606424160380d0042008030041010310135010840203c805000c84000007201e104203d8042c6100714600b030101a458540801c41c070781000007028500c6017902400b040c07020744052907624003490040340c0601d90081500580e083e13956101200110410605100030304210111586031801e50007569030340104a8040f001c0c18190983c00c40c110703150310354200d10f00315442007a900c5403480501515460f5403510300032680e65809014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 518969892 1250 518968642 518968651
    0x6110615030c13110f120603120901030f0b03030c0f120304020102070e0a0609181e0809040b0f03010f0c0909360213050106020d0309050a0b0405070305030a0e0112182603 75
    0x4c580d9030343d99146d0700c801500b2400505c464400e074085060300482158180c1074600b44842820081030b03900801000901804080e40042e8240c8004503d24000040004121140d0640902500c2d000401038492440500c011240a405a03200d0141001401d401140c0c1d5680540740d03050000b00142c0350480501640c00840000401074501007600c41446200708040308003010514030003840c0e03d07003951101503034010480644c0c803e6560b0302210455031039104191100c003400500030003010040e18140c9004014018030b66000580c030b02004210400c003481084030042940054801c542d06e00c200400c0b4812000600c9000b604d6100c06603001070705c450036114000c00a52801103031039814400024500311613403525408050070141500d0100710080350010040350009503150080c5d03610f0404615040c0c540e4402800b901c030000f10011120b41c01968425a91401d80c0d481d15100a0f00c040c402c140c0e42c5141000b162003018020301c80c0007882441003000003100350034030700500c0c03240b0441110040c0c0040300c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 518971142 1250 518969892 518969917
    0x80303040221011a18250210140109060e010803030a0f020d0e070929090403030b03151504060305100b150f0714030717030c120106110615030c1311 65
    0x21503d034a42c50140317540100000744450315121842c004040038051070104800102d028842d2021218440c0300340603620500003500c40a0109140740305d00c1040c601c8007445484484c2d4175044000c1014000c4d86080c2e070403240030740002c50a54981301000070081c160107803c0c00300d031a0b00304202600b55003680903048c0303c0f034000740107000d20501d030041c0001680c1402008104150b03209008c03021855403030b400000c11600640b00c0440a41d1985410f80081071035140c1681e05204d0704000341c602401c1424030394419404910300c11400c0400324280300c00e4030650b000080141d00004c220721a0b20045500c104000c02c0000c1c0216401c51070300792a031402c1d50040782408060880021503105110011030070b0300d8441c00000045162a046480d00b2120940d0f143d41030328907010000203da2405404015502140880f49009815595507000030b010f500d0b0000d1603036264004c440000d03404007500204d006021801502902c0c1c40c000d48401c1040140703c80390608500c0396202c144d5140c1c50080b07406041000f80c9031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 518972392 1250 518971142 518971181
    0x30307080f091f0903171608091216201e1807020115120c0608100902040609080105130c05010f051b0607200a0b0c0d0c020313060908030304022101 65
    0x508004110854444041ca513506c65002845954060f4072009840003120385480c0b0920384400d1056810034003001820050440042001c540c2e1040c1858000c80251140042d005d0315812420480f8002540c0c0119075803142c2d402c9000414a10350315122010550010820300c04000010f80701c0b42000b00c00c0e0340e5540140c0d980d1080f0303405841d01d1030040c005032001d924480c10038042944d503010038900a0280000f00b200c002c0100302801c0c580d4281202400d0302080540d201ca0b15000001c0aa840500c2038845a40c2001c02080e2445001c1009081c231517007150300807440600380340055a0b400000c20420081050800000103216810700001142c440c408000c1c103890304200000414880d5071200d00c040a0409002c18a0a010002454040140e010001d090680d40d0041e00c05581d00490400c09401c40c00e0491000005501100910310984480f00c2050070585811040b43e4002ca240104519a40100f001c00c0151411300d2401565030001c0c00108004481048011f003950000e81060740300f40c0700d0303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 518973642 1250 518972392 518972411
    0x302070b04082505100e0a080409020a091211010302220801090c083007021c03270902090a080708030d0f0c200102210a060503030307080f091f 63
    0x203110b55480143d481280d08240ba829a01c51540f10900682d4a81700242d841c01d540300c2c10002848245a110b070000c1110b03850310303075603501c41e8003075845076041800061104101294130340200811464081c0c010300f080718507000440041d40258400783c41518204c0700910041100049001c0242c00b038042000041132507015417926215404c45034124080300e811120030116020200c0b2001d07010306404484030020b09050400c050710511035110081e4014610144002801c01d03641412001c00388a555030a2802e0144e0418004c0c007248055500c4400701100010000050a03801030481c0b0840101820403135982c4911951820a00c0c2c1d1014443e80c1000c9906030200d00d0602c034800c5001512081400148c0700301c80700802210b1141c0b0f03a0754101805c1c1e03d01c040b40c0402581038850542003000c003441c140f40d8542c1d441c0040c080c1140e04002e041d04128012032142404419280a000303151600307503454803032811100990200410b080486d2107040d006a907c96a00c40c540c2040f1004103200252603401c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 518974892 1250 518973642 518973667
    0x6180307090207020d060b180403020f16050117060f060c0601152604061b0e030f070e0c031302060403120201140408031f050907090f0e07080109020a0302070b0408 72
    0x5580000c40440c414040e110250321501140c01d0f00d00e500510001c0c0f1007d0501c0019040007903116854610891802044105600014a03110452200080340c00302084041c0102d0038004500a0500045c0a9201c50176040500000e8540142c401040740280480c20000300b0400e4101800c04216548803000400c421141e9015004909080e443c01c80c200c40c504190383d4994401c1e007104024141c00100014061002c941e000c0c490035504582da1850081c00043e000340580409070100b8441d001c2c100e0440b81d03250000a400f01180e0030790710402125039601040140c03940009003500f440b8008e00c28024016541c2e200140007461194000c0c0804d0280001c000382195070b8501d2840c4c070300c0581803d00c404604200c080d41c4d446803000c8040c034034030381011540003001038056101d80d420515a100348042c8581040031641926410901c03503ca995070741c000214503203015a510004901a0401808118015002460400380078100540303000c1041e9188052510112804e450344617022817441318504 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 518976142 1250 518974892 518974903
    0x222030c12050c131e05010f0b03101509080304080102040e06090403020705060a0c200415060c02060906040b3114120a050a0b0a0c09080309130605061803 68
    0xa034030161910740c599a80e603001d56548003c00454820341e8508110503000034660031402501035801841c6241a0a43c968040a03000c2070140c0c1401401c2c01c0c0340407502c12010019244104855000b1140b100c0c82c00d02c881c2501000c2e01420010828185c901040c4603200300014801490713003200044e5203518020359045801700241002d481661514144004070ba40040d100b41550030445202c1d641d0034051105a4070b1800080c00200b03038903c180d003110401401904001c03039034402618184035031200740c44001c00811590043d000412014030781e0704098102039018022200c0081c004038a440d84030720170f025543e04a0318002c111107140d81030095130303100c40401c5000d44012012090403c24100406180c0401407050414001d40d4558203041205008004119040741c0140c150390f0301d0151400c243c8901d11080358510912030800d07090122151260035580203c0d1007043c0a9414401c0d4501002000034400222400b115110308010039155504c03001800b40e04086810b0f541c040b001c8405060030103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 518977392 1250 518976142 518976149
    0x60c03030108060703180809041113030f05060703140c0703020106090e0c0a14030307031407060e150718052211040e09010605240c0339030f0d0222030c 67
    0x1108480341c6d0b4000900c640c0c041d1100001c0c101c0b4046a20852020103583c1d902400e90b0700408805104400010b0218040c0c50b80052400350041d01c046a0b641d400a41c1540c1c980c42c14145c40742d84082c000703138040b06048064450f8621a10020400a41e10711684058440c620116046900490701d00b0199180c92201c007002040d0800300c800b0410030050004c4e4030703802039807800713405e0101464107030020f889002d0132149000c7d4480c00410600c1050861240d03280303402c0e4003a220303400807174000c02c14690007000441411a0903038800d001b81810401404000a640100701c004140b003150744290200d400c5c0201507081c1011407030f00303482c1d52428800c50503d0340060081105030f45030500c1400a5110310441d98055003d1045017100910b0042d42840d181c42003210314142e5010128008007600009500c150740003038246c0031121030b003141c1144d04503042468508492240c1c010012520200c8210000e07058034822800c005003800284100f00d1542031001c030003240602900e40341030040185403519107014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 518978642 1250 518977392 518977421
    0x8060610050409110403080703020c12010204150e010219121706060301060c0512070303051b0c060610020111040b04060807140403020f0406030f050f12070506010e0402060c03030108060703 83
    0x46681625019020b44180d0080440d42500d03150b10400280e400c404580055612550310369075400b09003030003501e92110f403507154441e840074082d10b81012014000e803400d913240d400f42d400c800c40c0049403c4e540d0f4100b440e407082c19401003580701c140540d8050300445c401e40c020030300002c4c80059018014410041081941c8100024906000c003d444041c1680d040d01c0c1a030030800700284e03190611915154050000080c003542c000b074030508055054011a000d110383c0041580c0d03d03660100f1944080c014050041090b6100900140403481c0c13441070001c200740c25000014a150085415040781c0e0f104e6000081c01001c0013600b0017080fa849514264080624a800142440040b06614081c843c1c1e10020b40b2501e00d029008a0310b60f45c503400f5100a5601c01c2e6006010740f45464100c0d2590098003448049020301121000041c59500445000c258440054802a0f0074184010242e40002d00300381c3e0018410f00601261203810001140a04a0340000f0616490254001402d440340d51403450030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 518979892 1250 518978642 518978659
    0x6020a0309121115090a080d0605040b120a03030b0f0a2403230718080a03020d09180f14040308090106050f010f030c120f0209030c0621091510080606 66
    0x40d03d4089105864a4958228200541c841c1c10b41180303401002d04024041e590700191620f21501d0310740c0100c044032002d88041c060407641d801000b11107002d010710b11030260840411400004d100798061051528000d000300500e800b61b03004109100700b5604002d4020074170300321511b8480d0b40c20810300c06040c41c03440d043c405007506d041e821102e0040b02904003d040080e40c0402c404c2e41c051781d4150201e41c0041d00d0b0060003551220203a80e00c0781d00b031200b1f50150051f48031200d1003500c1b03002c0d00b400740c1d079404441d8411006800700c114020080240c000d6401e076070f5031a001079428406010305008900a036a105242d041440080d401c542482e800244240d0211303511034a40d0360086c0d0030060b5031803d41800960150040c1c0207a6290003100780b00f65903680381147c610104840350f405021030740c2040e0304484d05034440e001404024030a0025143c4105424920b85520710409440e80d40e00001110644051104c080d9405c1003402003503c006248952110060001c40310811501d503110b0412104100c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 518981142 1250 518979892 518979917
    0x6120b0607020d0b041a070905100207260a120e0901140f090402040e120301061706030709021e0409061706040b06011d03120309071a09041806020a030912 68
    0x550350001c040c3e0051400c50703184002020700502aa40c0c4401c0c40500114202a00c1c0c201001012013070f0a01a84e48907804004c00490300a1000a556090314000100c5650510700c101c00d501d44a010500c00701e015202e40100000000c42601350081815440d072030311180c00005004105003840160801070500d240607826200c2603580178001d003e119026100c4040301e032a18000708014080741c000c810464401c050a403910040000e005504035102c554803d20807410b0b06181e0454800203640c12541940189400d01420304250700402c02500c01c1941410b1150b621303e00c0b03480b50b80290748010f5034075541c0c1e28100018649500461000000e200240c00c00740b4051303848410002001e00700604014030a1001a502400b400040b121030b200281104c0710420b5480040d01d0542c021503001c0a5809070940c0011410f40344801c51440001310003090341401d400400384002001040c0211483e10441480440810f2031480208880340407540c0220b4005031500f00003074092038100c18601044120000034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 518982392 1250 518981142 518981149
    0x80f132615010e040804030f0b040209070306030302030d020c1c12060918120203040b0c0f0d020f10020d02042303010c05030c0403030507050a02060c0d080112080f030604060e0106120b060702 84
    0xa810f540041040020f5502e4504083d0710340c1c041d94000a0044c10400e10441c144844050554401c1d4403c4070384003071903522000200e00741d84107444000c004d03900521041c181c170360385500a0a01d0580300b008484000322580341181500c004c0100d058049100c407641d4099003032141c0074107809040d4006c8280f0000f207152003003841d100b60b540300c080e120b41c81c01108050030620034022039004102c0c0075001034485400c1604c8e1a20761181a090183d00c4c411020120046800890407000c107150300805810100130170031075030000c0c0d4841e02d602009a41d007088007007a0f2000d1589980c0b2003c002d1503c904000300400d0030706003110030026a20080c03000c01c1c01040000948882100c054a50510b0042e0b11f41c05146030080c030f03200191800a52003070b40030500d01d020f48000200d650103e40b050f504d014159984000154160401c0300018155240800c1402c80390040e017401107801460207480021a1542d0b45e005011425080c2c120bc0001502c0c4490001c04810394010300e00100c8003140c8680c640859a17000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 518983642 1250 518982392 518982433
    0x120108120406030b010314191a0d0f0302070305060708150d0206180105070f0b041a0c070201081e0f070e010504051c140a080a11010b0d080f1326 64
    0x2e0808040c0c44400c071800a03486908415852419400240d85500b80651010500300340000b480780c50310710380f50381d00d1841c0111017600e100706500030f05400c551120075110b100b41130001c05816015031041010010018008100c458032900c05550341002d242001c54000d4000d198116441c0e1040006240b0003000d0782d250350441c0d46540c0c140450707042240c081001078070207001e41400a003800c07060006203414000040780b1148180d00c14030120607040d4040341c00c0c48080710242e41c0301b100180140001c10055004040751034015000b810010912201500c2c1042140c40440300d05404000d84400e006420313030803001485030483c090802904040c00d04012070005804601d182696218075103d41080c0107030154507400d044407400a4a000643c40d003000181540107a50b200001b0b1104480010300b0381d0184258102d19000526000b07000000e600c84880c0c03500064080840014100004a458110030308840010702010101c4c000351130f004e40d00652681551500e003003a980018040031701005c1c140e140c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 518984892 1250 518983642 518983649
    0xe0405070b0c070801050c0a11150412050d020a0903031b03080f07030b0303040806090607050f1c0b060c0106051003091e05120309100509010c020d1d0d03051201081204 74
    0x5a207444110040582d490000f890780300c81281d5182400f403180f60311001004281200d4191501400742044d2075083d951200441260320b8040c1d608000314000802c0906452600d002d45d00d00700d03003020803c1a480d4101da000039024000304425020030810590041d0f911890003581c0014101400816280a444001d008090003005100c0000260300c5134040d6101a03242c00000e4202c07501caa440d1004150f81d0001501c52070010310480001500041c49802182c05c24105941011b05000068903000d2591681c140e4088030251a81d00d40302250300d80b00c0c05006601d00400020548074030741414003081e019111408001c150a00c1406400b0451310013100d5050b11152040d1000f8482d5401c020b805c00760f000c0c0e1000008078000007440000c1d00d00140590100020a004001d03649a01c00c80701e0032544c80450003409a0020140100350b1400b0f0107040528110300180c0102160101c00064505100844200e020981c00b04d45c0c00b60000700d01a4103409030980000914040600d0100f25519003c0d910 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 518986142 1250 518984892 518984909
    0x90d03030506121903020c09040c0504020a2001020711090705091c0209101502010b030606041e020d0603052a10050c06010b0c01140c0a0503100e040503130e040507 72
    0x1030101d4a19103c0d450b150640002c2c0c2010740307400382c40d0041c003c0038164070707880240d005100d104021421454001c1c1c1c2c203070245920204100000f40f609041c80080d41019100800717109621261000340c50082c0c084c80c0c0c0508044000503601c01c0c044c684440020340c5961000d0103605610308001441c1d41103012900000d600705c4900b0004410001041c0355400c50810094100d5841000e20050980c0c1c3d0300840280c45059010081c10500140d0403400c0340d020306011507150344030704007040d428200b0b980691034078420b01d210071941001c440055400e981c0a5240907a0380d560390101001408010b201205883c1d4040f08a594004490300b1034201c602040c100e03003881940000c405401c1180904101d86508403240142d8019682d64061780510741c02084c1d0982c40d42d42018186802c1160782c007049442902a10316142c1080c0c10000c3c2143c5540005089207810045090041800c0401c1d1500c944540d100b40011a0b891910310b50f0508045181e80c00702c040350034003800b84030004c0c2d000300341c24081d41c0e03980 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 518987392 1250 518986142 518986151
    0xd020d1103040b12101502010603120203120a0b03010f1b0e060f04090b0103090506100509010b1e030a02160b060109120203150901063305030f070c0305130905060f0402090d0303 78
    0xa405e200300040d4158811a0f101c2c1c0c80740290550f4603010340080c1c0440c0e000300c200200803100e440341031382c83c1d2141c0010a41d05220b440002502a11540d100701c0d108032014000091800d10100ea0804072603034120044868190005910001584502c503114074010940e140c50610340040388070000b5025502510a40546071441d150f0180d00c29800104040c3c1c00c141241d003503083c2011780410010b201d00880303024144440c00403880d44210000c5505101004d18400c0050401250500d050b400140550f81b46903020070421685041010040120030b0182c554402c45013050f20015042400a502c810402e0003058040340240e60f000c9941d02486480c100b401d00c0664400076690f00604032500064400c49065810000074080d104c08544a000d230b40c5500e0400314240b020a641c140030807980b14604841c0240000c0199109804c0000800c0c400d080440c1001c6081c1c2c250b40070a9490741010002035515400c009103413400402508548109807011440c010b1b007030000c1001a07800c081c028044c1a00c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 518988642 1250 518987392 518987401
    0x9030516030201110d050a0c03021927060f021605090c0912010204081b09040215070305040306050c090f01030c0e06070813030506040b07030501060207170f0d020d1103040b12 77
    0x390803622803005842180c4d41d0381e503441642c5d500140f50555607846440d190002140c080d9010f403085441da446065880300c1c2003000103100f210145410346080b1028080c02074075800190044141202400864955000895140000a01d8600e5070700d4954991030550300b04200a4641c81281c5400c41500c2d000141c2c0c0b40d003100701041050402411a074134035840040c0010750000b005c41c000843c101c84580c098003174804801044100c072420341c3d0280d4414900365564980541d12401480000c0c840e0801904180d80c3c1d40b55001203400072a64541100d00000300e004640c07401040780e501c00c100074202000003540c804001880c82865649840c001e000c00a411028845040144e882c2e890446904515594403454000d0322244d0035030781192000300f224041280c10b4001e004081c143c0343c041c1d000341096454041502400c0301c03007507d024040c2c0119403502a814100b400b200b90700c054150000c00503032030240e0780100494846040c40160790000c0c0f0040c0074400a02044843c407802a0242180b207454 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 518989892 1250 518988642 518988647
    0x405011425030203030613150506030402190602070302010f020f0d0f0504080a1101030e1b04090602070f050c011202161101090806010608040b0a0506011b051c050415030903051603 79
    0x615070400349095107001441e0101540000254840d003410386441c1d10b25010019194240e072102c1d080b400260b51a85028400d07400c09801466000f4001004101c1e100c82c0d5100c00046460160406401600a0349043c020f65800002140c014642803000304840d0a24806a5498196100d030b10010032103008a8102000d10034010764028060440541e156441c4525010011101008013540400d05081c10314100c424003207a2854003904101207125004280c0b8208002803c8010013101da5a034280100750105a800300b03043e0145119100070504c65041d0400174000c00060815100c0b1240108036200d41031461454000c40300740d0100e141009006954010303217030342005070014032140c803c4400024041c1e074861051802203029885640351070721082d00304020790b9002c480710703404500780060400002e070701000305802550103401512000401d032a01d480001a580316030400090300402c1c144402012004c140350031034294182000510000e0b03a000e052030042d604000f080300600c610381c009260 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 518991142 1250 518989892 518989927
    0x60303071101110d051305120307032102070b060f090108071e1a070317060117060a03150e0609010b03060118110301120302101e0911040504050303091204050114 71
    0x281c03e005a5099140c43c250041c1a03400948003101c4806a0420001c0d203400d0154101d805030001001541c946415500c0580d020601d141035508000da0684000c2c6030001c3e80d1000c0c1907601e120301441c46081c180b850400003000f800c1c5507040e01c40c040302401044450b900040180450355400001c2811000150040f030120740960700000e0f105c10045d0640a800105900034000c192007a254124852103103440038138465021640c20f40403039031141660f4120341e480c082c0940d21100041100107040e4482d690444203441c076001c201541a202c028041c0603100074007500390301800c0c0380000c02c140c4440c20002507403040c06200e104003068100c1c0c000e403c5c038007554000700061302501425550f2035a4441e424108103000c00426801806007020070f025080007400b8503c042945070051ba0700307420760580404010140d811003155100c5048042600c240c4070b6010f241d1240c0d0140c00519168a0803242c1541480701c11290441380340d004010612140e82c00c081c00d980c240c91400c2440c0d8440a09202116455 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 518992392 1250 518991142 518991167
    0xa0c050c0d06050103020307092903010e160906081207020603090717060402040507050307021b06090319021807170714070c081b030a08030702010b0a09140f060303071101 75
    0x94007072620010710203140c100354101da00c250304030f69030507907214888011078020036406200701d0b2a024404a01c00c00d03c03403030740c92180360007030000031441d80f000511480e04400c14100b40d04071000c1101082401070314403ea2009154440181510324529840d0200901c95860000c0c400c175804000b00e44194410800d06004c0c014607202c02c1e403802c00c10312400c2d589050860301240b11304e0818000501d141c0c4103070180e0303008541903001054001804035440742c070010582100c5402240c10f100701b028a68040281509050030182c484003c00c0050044c07000e919040080e000010812005003c0a168840360a0a0b5170000c601c032480c41e61900d0808840c807238507904401c50703054004980a002c2c8a10070252000703c81c0b0b81012105000710345144c0f003a44e9a0291039031903060700a454104042442c880007540d2142080c4000140d40d000303080010790f183e18641065070b100380d0f951190340c56101c00d01350507508036500d0104410b140c81d213100002d5592090142c020002c0b8104d07001a0402d0f40200b4291590 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 518993642 1250 518992392 518992399
    0x709050303040303020715110604020f0123040f0b07150b040207020a0305100b1905190801092103110d021303140a060545010c05040e07140a0c050c 65
    0x202c90392030400039030383c561900070a1803c0c1250054403001c54086c1d0038a0f0200759448025107025039841d020010181d100419160502810000e008101040d40030300740c9502c140d40000c151224144a9111004034003900178600c0080104500b1000c601400c44100c60811150303030204039002d6081c0850082c2c0182c90009400c42c600362804010824003141d01d4040f005a000100455003a80c8100003c00700424802071000c000a030081c811800e102900d01c0c01001c10b0210301131181d0b07841c0305c1542100e01148054402c24010341410030f91602600081c04c8010180c80d00b8022161500f0110350741d8421001030f0f456181d40010100180741b41801d0410046401c024070600f0f0044140790711b43c0b10800e0305001c0385d010380741000246400b040b141d854112811007894462184001840089010310038419003549214804246034000c9400d0090b64001a0a555030589881c60800c854440d079001605420a02c0041a03030b290080d110101600c0300400180b500022a0206d4240203060010a0300030940 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 518994892 1250 518993642 518993647
    0x5250207050315010e060a030206030a0f06030512040608010807050303160618060e07080304030b060103020304020102071e090605220b0109232d010c1a04030806030c01140d02030709050303 83
    0x10204a0344010f030b03048580f50702d203540c030f95070f206802c0010048031400002d42c802021320106120300c00b2580011540034080c40009000d6499494082c600380403804005007005000800344002948424554010118000200400fa05000001e900c0f4015a041040341403d01c011030810300c0f8854105070700340c00103001d2074081c0c20113074103001010300021a485a0070344a10400000c510034000104c0782101e401500440c466140d0800444c060350002d48107034118824210b01040c800d1080304d0200828101c8503846117260325103a00b0a040d150301d58421881480e0720348800502003d000381000170340d140c0340307400100d03649e01d0070042c1c038484200e40040c0c405805141446c082d6801ca807000000c5044121860440c02640b0f0500d00c1254940303241003060021946521541c0e5402141500c07401d52103007007980f440d51144819040a40411581500010305210900ca00ca06040c0512205510300b8640304005c91450b2540e444248281c1d0486940319600000060700540b02e8a29400031b404014207891303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 518996142 1250 518994892 518994913
    0x160803070903110d0201170c0714030d05060109080c01111606020c040f020406050720040504060506010314070914130c05271309050f030301150e04052502070503 71
    0x203207440c0d42800101c81401d103980d40d143e0646002041c00d8000c5074140d5a69160710b0110640b580ca5a030081c1515195580501c1130100050000005401440c26000116200c904080450702500c4014003410f042c015112400d01c0156004180201c11308400e091080e0f080195400710b0303151040070503004440d000f04050115020b94089002ca245030f5044030107010002c845940603040703228074070480c00810020843c41000800c0d0070b09840d85440200c07a50100b81503240c0210b001e035042100d00b00c2d003c0b941da20821280c4d43e010320400c1e500701843c0c80103d155191444000e084000103008a500102c41d0039071503d040e03a1480340c04220445409000e000150f0003c0c400f6000760851081806140e14040800c0e030011271500c914500614000c01c4003501e240c00f80000b00051003803030000c0e941800b58980800080100708000d5000342125010501051038086000340100308400c1014891414901801600c8000c4068074030345040d1a5402a200d4081e10002c2e45001d00c030364003103901030040e100d509 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 518997392 1250 518996142 518996147
    0x30e091003031202040f3011030115052d0a0b0c0f010903050a0302070809150a0e0d0f022806030f0c030c02060103080f0f0d0603062403030516080307 66
    0x18080703034460b803100c49001440c0a0300e10140d0103207002d440d04200090004001600d00c01e2121400b070704490040d80f04004003100c55201c028000c040c1a1440710703254602c1e00b03903401c0911401d001c003e610361188030003034100000506088920b83e200082250340318001e4046020000c10702e5001203000340f0380d080041d0342d104c40d0846c9400861180702070b0700545800801c000d6040c0074051290741c0c1603503014038080c0300d107c0550080d04030326030a49d01001d0501c0b614615807a0204d501400c08400d5010300d8481e2044000100310400458200d07000d5040e40c0303410800500c1101244d4401e0394116441600ca0340244898401014007041200f03e1412115000824982543c4100b202848a4100340001e403005402982540c40101c15500180c2c409070041012684003030190407074249007000c0d030f403501080d0000c1c01c0464110f105039542d115624401041084007500c18000c1420f0031005005800055240700c036414111880007034148200094404c002d030409a440102085c0c0c4240345903144c2c2401c0030700 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 518998642 1250 518997392 518997421
    0x303073f060e010305160f061e0e0d050c0405010b090a090e01110a03140609072c190f0f0e0c0a031401060e03060603011512020402090d030c061a0f010309030e09 71
    0x2001c1406c000c500403070100285071100083e600607032200d400d004603880700b400314050140410403c01500d40400102c5030750b80070400c12194010001002d135441c040040000b115010b03441500d04403400c002c034003143c1d101c84162004075150b940e00042c181484001c2c0f01c0c054000c128400c0000b0700002080481180c26038050188444088000c010aa0303030041809504403040c0c40c1c1c400480c044550a25404181e940c01c04002480991100207104540c0d010900440310dc80c0041c030803015120061000c2d60315205524000e055070710703000503c5850421801c0e5408000703008401c41e01d000003000c01e02c06000703411140c10b40c0441440310840e580c0d20354000309801c0c001901f07a40b1a004440214105240c14003c0300b4440f44001e80f006141480d15400d6401003406a404981160b000d0140b140c00d5036505041a8845000e41c0340da880341840ca00d4400125050304513108200700b13440c0f051078a5034503900504580740c402803c0006900b80700d4182035998030b80910446070300c00501410001d07031248e000c02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 518999892 1250 518998642 518998663
    0x9330414010615270e1816030c0b0d09020a090504060b01030902090604230f0f0717070f0e0901090b030c061204021c06020c0303073f060e010305 64
    0x8000c6240c85032000d801d14030311104a1000100242c41481c148803034000120b100c90401060114030a96070864070804820841340846e211128030750008442c80140220504020361402407540141107658103618948540547c0e018240c001c40e5048844080303a111851480d001000c401c0102d80d83c00210003c2c0508840441d00a0f06000a03203410394006e0040300c0380e079607004180b11202d0b90703941c0502c00184101580081d900c0c4100c65203201071401260080c0c00381d9800001101d2620b05410408456000a029501040380010025100800710102e00750400900e1422021281281c40100d6104400b031540c3d0703500003441400024511400e5120081c2c0c040c09800341d400c40402081005558090603c03a000380500c0040014010310388900c2d0160344030400c8050400e46080364580004907081070551881070f6000000380060b464010b1042c5142141d030903000c07003040400d0b02c4404001c03a001007103010a00103004480e410200107070400f10182c20b00014200c02981c0d40d041480d5250007240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 519001142 1250 518999892 518999933
    0x60c030b010224070509060f07030908060108030409110408030a030c14070b0a050c070b160e060406050a03050a060510030f050a050c1b030909090a05010c08093304 72
    0x22000c80d40d400032850f0082c3c0f141c2840511008401810706218414008000c841004070410602d00c040e540c40d4003511514100050894031180c2074900039024101ca5040314140e03501c4040100041c540000c100ca00f40c5403443d10100b0a0300120104c18218001c0b50400600340c080402c00300151981940051040e036013940d25103202014614020203d882090f502401039600742001868031642e680106400200e072402070341c60003456841e03906200c0010b9500034078550000003011000e9501c04290380400a0844925180c03a10780b5002404a2085201c020240754680000519140316a40b04c0c0c802031801420b0b20410248e0200018010f00f50340c08028181803403e400300c2e004841500c00e4501c1841050365062500209015010980d181c1040000003844104640110394442d02402d501a03501c0c40003c00521000c3d180150940300d11401c000304201400c1d0410a03096030019a01c400b4181100c1445c22421001d46200e94000101c03030060514069041880708108a072002940d1080c1d88a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 519002392 1250 519001142 519001151
    0x15030b1603020c0c060f0708190306050108070f0818010204090b091b030103022202040b030114010f020d0e0a1508060a060e0901181812030b0a0b0a081f03060c03 71
    0x114801e800b207001d20703640030750103900028241e035090400c0c0c0001e040b0301e10089503d5003022180c0e501c611440e80031040348450f074001036802000040c3c150043c68043c1809003400c88040c80c0081c0028500b448403009142045006008210180c0d4041e9054070b20260902c001d556441d122241a00586a0f00041c14094036050000400010801c42d4025500c2a030060702850340c0d1031030702004080208210480c08000c105038203800020002d10003040200143d00005849604d0250500162030b00b403480c8506110003d40780c01031044d80400c1e052000c00345802c11003020b80e119004900601d46035004400ca40c0925003940c1c606c030ba0064010b91250104a902d00c0c1ca044d11020210342000c002070b400e941010f40d01d40140442504030400204805007241e0006000c1d036403201c5207141c0c20703c0b42c40c20394a20003030700e0101c0780182c0c2c1405034198120050b5045080580b034800e0340311503403150702602010481e0100106081c84068400712001051910413010060707264101035000340640b160b001d02080ca007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 519003642 1250 519002392 519002431
    0x1a01320909010e0c0613060503091009031e0302090d08030c07050304080a11100f0c020111030d0f06150212070524090d0806010c02010e150a0e040b01030e06130615030b 74
    0x10021a0840b40d28461006c4003540f904506984580010341950000d0141c0006400000c8251240c418098007940c2d98000d000c07060008460020f801c60915030415004000e135a41c41d848581224901942c000701c21552960b4a010742c1e8001c0c01242c030014002d010000b00000d00c210000740107070b2098015003040e940784412400b0080445d0088100c44081360086000c405a54010304c404040c1d5801810101c405400340e8080508543c000b0704030b112610398501c00714006040700d2140001030100e41d41c40030f101820f8044080c4d920001c1c2148010364410000703d003c100700e01070050880c214009000b400c118507070b00720701c100000030403105419030707100f01c5248100052103030391810b01a13201038584034107032140350700110380446441c1d00c8250803021700d14281c5100060403005110030b84407640c502c40c4203146602000305844481035040d0416042159030190708102040164008180a01c00b8869482611b031000203803c4401000d590012106000030502c0541c05442c0d202e024020b0104000050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 519004892 1250 519003642 519003649
    0x60702011401090504082a0106081f051306090309140a05010c2a06050912030414060711041406041422030201061802071a01320909010e0c 61
    0xca000c00d00700e54508000100024503203075100b250000c0c001e8400f1880c10400c18040c1100365012401d00780740d000e2104048200780403e00c0340c10b0190000038041c01c500b0784800c49a03240b408000c41610042c942d40c4020405840030750206803219903101400744a00c1744582000352001c810743c0304001c1648880a5042040c0ca030265a41c0c05440050f1111908801c5944030113000052500e950742040040f20300418410101a0b002070080480b540c1d12036550302908182320751000181c070724404661040c4024000326405510500800100780c6845848501c0790800c1d01c00d90341c0e41c108954005141540380810400800c0c84988111800e4030240907600000300001161034080f218000c0d00348400200c54186181505007084540c028800454243d4440b03d04800d20340c103154000c001c0f140c2c0014000304000b29403030440341480d859182d4000d50340c9002c103440c1280160401d40d00c201840e01101c12000c42401c0b10f8001c0480014104a0b058648404090700808900c450071016103d8503503026410b14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 519006142 1250 519004892 519004901
    0x51005060a030b06010e031b1c0507050420030c0a0e060a0f0509060706231012020f060f0d1a0411090f0307031202010c09090603021807090b041706070201 68
    0x9030040d0610784080c0c9103448400315650080c2c2514100520903001030f0856804000c0a581c843d84180e010071811900c0c0c080000d0881c1205402001000451105001c40d00229800044402c00e80b400700c2c0a60b03500b41100a00c0d41607541080c0c08010100500960b042c001015014000d03450b02c0d058100030300481000706a00a4008980000700c41d041d0503002544202c014141082015086600301001503a070041a9694460071501c030004d41700a04208401e0b281d030043d0002284400c4100b521b00780f0b40c00030044540701e00b001e0700441e01450141640d86418040f1414950310514150b1641ea0f808107002c003400c3c0807481188400d003840c80b108071600d02842285248221689401e182408074030a0003062000d01540d2941030003140400030100745a88135070102c12038550700004a408403984068000b01c004c0e08105501ea00e4510300340b00680f01e10414441006800d00c9500541d41d07158400c0b10040703d281c0108494900c007040000707082192615a000589143d416243c00e5910803104900700ca = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 519007392 1250 519006142 519006151
    0x12150b04170d0914010c0c12030c050c090105010c080309120a03021b0c0105040e0a180803101a030703200a021501121e0302010209040213081905073f051005 69
    0x11340b143d5002541540c0994442c00c81103204002480100d580c644d02800050f84003203065007c20841c240c0c0c1010800c017070080c0b000c440d800f12080704455040c24002043c10500304d4000f0922240080407402c5044200100740710f1901032414590f0301c0e50b203918018003070f411003c0044a11100c1178410014010085440e8a1faa0410b039285824135140c82000810160f0140c444c04030296520800142c20900c0840d051165006500950b500e04105a9140c49a0081d601080312003180029070f014046c030050441e60045101d2801141500002000d1050043c101c041582c1c040000641c81087c00e4001c114207503402942d606001c01a039940b5251070701c0032880d0348001e0255003015500400382160401000d4481c1c000c3c0700040c14114450080f8040b81d100f6010000051200759040204110401c0341c079516402c8030041c4102024941e8400340d070b03840d0034000c0c480484214800304000604449000500e2002c070711440c04525088998801924446101940d0301c0c0645914003508907118003405004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 519008642 1250 519007392 519007409
    0x170d02032806080c15120106051b0606030a08031503060103031e0513060c0807050718050601030b030d050a0e0607060507020d08090c010c02180a06080c030a0312150b04170d09 77
    0x90000013007006030070040b0f070480d0410340c84240a12510300c042d10103900d01810071905d6043d52200d941c06005414918001c03000d01580c005020400300b6100407407402841940800b0007501c82c0c46400100001001d0455503a4051044100010902d548050b0b400d40e139002d24446400d042480c14821503d42c49000070303a007222542d001c003c002d10ba224002489400d401420260306064150391a00d0520285034000c6580729052894204400114800c054001b00242000c0006201d40804603465210121102e8140080820103043c15401408011003088006290302d030340c1e401501e46034005050945414006128030000b0100b028003071006076002c0e20403080107044000281e0011210705c0c00c2c1c0c4408a801c180c050408255440d442c290315401405c00780350110f032450070035024600d072110441c4020b209e030784444140c0002c280c21284407980f00070b10540114220303041400410b50200b180d030005c8039540300010300041aa10006811001d6008403050364500c0050000486100d82503024103182c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 519009892 1250 519008642 519008653
    0x209010813021207121109060306061912050102071a010f0e07090f03050f060a06180506060912060717161805031006061713170d0203280608 62
    0x240d00d10314050400355100402030320303c119584071603605155017907210148101d900d400d42c100308107400c11000c0c41b0080a91303004109245c242d000903a110030180207540160300b003002690354004040040702c02307000703103009083e601031551410300e000303620500b01034500140c1154201c0c8113209801e1902d040713410003007101d0348450801c1045810020f018090000303000400800195007502c5400400c02140208080c0c45890801c05140d400d0400040c26610103a15104080c000705a8a1040480b00d8200380300002e11f6aa60030085680c1e8440d0171811644422051a80c2e0030b4000300242c0c0903c0f5020300d0b43ea80c901c0d440008090079402100b52071051400c52407550a0724450701c00c00c81c0b00d942811584041110301d13540c0b00860f042554940300c030f0383e101c0e8540070306002641e0010469208419560320181041c035001c51484900710070840001c00c000310061090308026500b41c141d403045c142c004411540c80c10701c40000c03484c1c640b0200d241c071803030501003482d6022140c80b40b055900300e1b4680006402c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 519011142 1250 519009892 519009901
    0x70506070803090c0a0e010513051909020109050405040b1b04030b0a180f05060a0608030c0a1115210609040c03110307030c0e091903050f0a1e080a0f02090108 70
    0x442504010b14007000c0e4800d4406001c0300b45d44500c030280c020300010031001d046d03505041c14400800804281c3c140c0e007600b000103100d0b51782c0f407110758801c29400e01c49000034219403502c01216609010382c0300e19030150402d8140030a204054401c2401420781601c420040016014031590a000361310011b41074054480005007940b0309500142e1b801c03640f4640c00c0024943d20b5907410750301041d845003034403d035100c0020000403c025120b00c80c0038210a000a40c00c10105d8240156240d0b0314210082c900c100d190401c540603195046441c84111514801c2c0d5202c042c0c0041014a0300c07100140c50300306a124a0204029080081145000c0d0360001950042542162110382c46001c00c14032b82d6415110310703800080400c1110400c0805080400605a6142001c84401e8501500540c1c05080940808031000000b03402c501118154903007030840c0c9845820852090b203221016030340c9401043d4416500080043d0712100c02031048200700c5040240c113642004032030490040c1050140400d4103140801c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 519012392 1250 519011142 519011153
    0xb033d0f0c1409190509090a0c06020a0203101523030d0905090a09080412060f0c08070203270612061003060b0703030b130603050a210905010e120f03040609050307050607 75
    0x2071304a1070106050b01d040554032408648000c004840c074075801d4022514150030486043c040000a10541c030040c92482081d40000b038440742003084001d00c140c0da80c80003254502d5500880c100915086c11200300703c564841e0404800581503113414400d000e00304c00307120400c1c000d10320340e81550400760112026964452100d4010400c1990903620074109000005101a1b04424103442da4496000403840c86e100401312402e075000c20341c01c88240062023080106055000060f1000d0501624030b20041e080e1040d1b103000c0d800d03100b91415401c681d00013180003032003203081c1005006610660f840c201030240f0300000c600b01c41980c09101c0c0d03250010006400072034425002030072b02090007844050341020900803030782101e96540c8111403980018900c0710900c00d4040602e02c064520b5590b40780f843c503100d00000c3c080455406290705000c0d055550140329214000c1b500780d03c4c0394540407501c0d00d80d503040d1030598036041481160000340148402042a04002c50030104540028110314140825139946 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 519013642 1250 519012392 519012409
    0x60b0a0e040207060e032110060e090a060506030a09050c01022e06123806010c0503091e0a0b0f090904021206010906060809010b033d0f0c1409 63
    0x20ba43d101c1d03c807405c1d0b00d9400d00038401400328010134400000c01ca00c580f403202c5151003001785008414103450100300800c5401c8030440d44400c50481344214103607900b600c20b000801c0306401940d00803501204010302041daa50007440c201d8068011640740181c08801207968910703003e504a509507a8817010308589005a15800113035400d40404160345e52981c074903801e00100d80c0d000303941414084914080e84c030400c011042030b49100e030100c03e0f00540108555400503101410341d504200e0304815800a1290130300c10750712194802007802903910721880c0e0015260400603020341c403032902c2075000211122030070200d542155145030341c1400e01000e0010440ca03c500100261382140c038030300f111040e18800740a914040c09500c40700140c44c3d410620010b2140b0002000507826a1400d004079019680024407000c4202801d0101800c0846158075480510704031203a0517003403200094064880c101c1c5420481c001c01203118100b084040307901041f07460400000070f0390303c0403100301305000507410500c18 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 519014892 1250 519013642 519013657
    0x905040f14090706090b0307080105060708040308120105040501050a030f06021315030609050a020c0c12010f0f050f06010201020418052a18030c0a0603151505030a060b0a0e0402 78
    0x40c0010a25200c9000c860300350011680019150803143c1e0030300c402d82d007049410700944020890f00c3c0c114905040054420f4206005141c880c14003c5041400c10050b070b41190051507000f540c0039140e102e114020346950000b8040c591042d418040003207400e081c001c0418003100d802405502c8101400d4868500070b40c44060901550202c5c1000891f501e1f50501c0040c000490b05c1e074000801a00d410f032010200c440152021217681d00401102a25880000d480411440704441c0103c04903014180c00703004101790318030784804a003000301d180307095441c0e540114851a00c114040300780740d50b01c8004900300d02c12400354111445207400c2d5441e203040c16600c099402690b00030905841007010f101000c40080003c5c50215404d000510307100b40300422841040c03400019030003400c0c0e949020000500300d40c460b01a401c2050380d1900c20441d40000384104000602c4501041c3c002489103100086c1240c1c002c49549050030b041040003d0481c43c0c510880e1a010301c070f0765440038000000400c10020358000003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 519016142 1250 519014892 519014921
    0x9030703110a051f0e010b1e0103092f04051003030f2c03010f0c02030a030b041103270f0d0c06020712050c0705010912020f0a0801110d060e0601090504 67
    0xc0c082000503000300800c44078a04507000c411070f001411018041500d600741412945030b41801441882c03900da10088d1880000740c076000c8024200c002c80100d0040c580468054035404821a003080002c40340d400d0380d039514441c019a00252002c03101071000b6250107568546542c2c1d00c1e40d400f000402d1040e5500481c604a5141400e59100f45406a41c6031404036280d00c0c02801110104040d1480c0074400c000301403520840038001c680d840000a51a8040c83d40c00c0001e060b19200c2420b100e0381c8903403000c8007924541003001c1d02c07400d1180544801d002c410720400110103000301c0e505c0fa0344800040078020400418000e00ca40c0455060485060700d800d18200d407000d400307200045c00503003402080f003000c1d201c958610791503149608010307280c8503903984102d0501607800e10038420b04001c0031000000b103406841d501d003c1c41c60400401e000850740e40c030000310395107840b00304014034a40500400b80402000700502580d5201c85003100cd582e82030304c05902107501024208000c2c140b46e04034066401224 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 519017392 1250 519016142 519016153
    0x105010b0d0e071e05102c01020a02030f10050f130f0201121d07050604060905040b06040305100603020f0619081503010603032c0306040f0807020d1a0106080903070311 74
    0x5400c0d000c07030003031840c400c40010368020b03005100c542410506406c0700191032418400c01000540e4562019000322200c201508030350044000690007002a00c0c1410f501400b1a02e0a841d188070850f02c3e409241300c4004e203241000c0c04034000c180c2e810003060080c1108100d0304900012030b61644c00100030350070704038140700c41b03200c2145540711180b06400199030102c044592822281d00042e00702000e940040d403240d0024001440415440207503402590400c2d900054841040c0c1c0010389a8011a4070080107440f44c02da50f44035148568100008480c82503e41d00c075400791003010400c960040c50110b131000204040e030312003518403c3d400d85411100541e24621078013040310100b42510b0341c80d0820b40110310001c170000720080c1010101584413840c039801450b801a944002625280081d0000c0c0c00849103014110912080000b120b042c0c03640200018010b050310302e004030040d00d1000090000510550001640b6401442014890300c010000b851034204255419141c1c0d01c05948c06802e00e200e00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 519018642 1250 519017392 519017399
    0x105060403122a050a02041b0c0f020d06060305031305030705100c1b0f0519120f031106010e0106120b06040b0f0d05010603020c0f1c0f03021204080c0d020105010b0d0e07 75
    0x100f01c0811545008002801810042d40140015510079017100080d5003001d00d417100040d5444501409a65841600c0865800d15030000807828020288060700c0750745001c2d400010050000000c1801d0300c0d4035000307036501e00e98400400d9100c060b54807031242c00100c00310005413458810f0a28080c40740c0305000171310034502804002c421050460b0804900294405010f000914040b64001c000c04404140c9a04030b604002c4817501058101300001d10500324807015008240c010700701d1103081e40f210800c43ba61580d641e80b00c807040f00c1080c4150004207140b54201c2d03000100f41c0c060359806020160841d0b243c289841d80c08101a4007202c00503c2c3d41500740660541c290710380c003415000304503541d005a00c0c0c2640f1081c2c141840c00031840d070030040d80000303081750021808003150f0741451014101041c005142c130800b60060b200303414150b4240282c0384204810402180050900e626074002250307510003100405a003222030a000d025228201401aa402100f2075000f4030070301140c440070781c2e0b06c49a8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 519019892 1250 519018642 519018707
    0x100617060d0609080414060f0f0912010203130b071107150e0303070f0303180c0b0a0504150f0305071103040b2803230601082413060806010506040312 66
    0xf01448100c8880ca00098100801039203041e48042005007140c8440c5072060081c1c0ba05920b1084440402c82d000001c516861255600c8400041000d2000e000350354902d000803525400ca00d03001402c80f400d00041c0045482c1b1072040c01c1074100307100d01d07100a182d2603080014845041e40c1100181c820080c0004800810340c400340082e0000c244580d00c50038980c0f205141c06003e0361140c0340c907000c0c00701c842030321000031444580100c0d00311040003000640c1d80c242840200d0b40d80c03146170083d204c40300010344541034040d070005502c00e5482c5241d500700400e44440b0400c480354404c481c9084415401404280070400f002c3d03004103405206032007030442a100138502d84040e02c601110100c0403d0340c4001c2e501e0071505001180102c1c071004d188107002454041d00103804100e01500c0d05030304011514020b07050303000d650600c00ca0600003c00c8408482404100c4a000d081035018143c040c2c0181400005c460402a042c1c3d07050300d60044d14041c03204c0f2825002c0307400002c0300d00840804041058842002c54 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 519021142 1250 519019892 519019901
    0xf0103270506061003140406020a09030614040209060a0501020705010e040204091b0f0305040c170c03060a0b01110705010c17090603010312030b011d130b090906040b100617060d06 79
    0xd00c908042d18543c0340c00010421101d81c070014001c2454181004480202451403100350b000b81e007e0300060310388807426021035070203a0301e40005000304d1401041d05034094044c3e20080c03145100b00d40095440d5202c40608c20420000e100d8103000d0781c000c440034440b5600910803900e911002500050800746c0d20340d4060b096486101968040805186856400c0c0b9130080710702c111058a0704080c010742c00c181d50784104210749442800d0041c441d04d040c2d03042c900818050b400c22100c00404403115400d080494130000c0130741303184003804140001501c6012400114080c0c0485805840d110720001030740c0c450600004454960200d5a813040001c00c60999400b00650702030b502903060392170f00076003402d0084c0440e06da054072181030000c408034003000007a0380c1064804031a0180e8841000140d034015440c00380160301655640a0418402c101200e000094803034840c034003400307660380c594440d050f031402920303c140a114002075540f02103c5442c90702440d078079008003015200e001c54814a0f21804c00300c6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 519022392 1250 519021142 519021221
    0xf09180109150b0a080102070c09050612011e0b120a140a05010908040303031a300106120c17061609050d06050a11040501091703070b1510030b0f0103 66
    0x2a9440d4040b03d05410132100110107014002e000b1031903c00c00307458840c042c82d1244210b2008a840740b00050700c1d0b8440704440c043c00760842e0300031f1041103032600f0105514100e405100d421689440c011003801e14001990500e9040c00501611100c1010313181c44488148038811507000d4401c00864200154091041ca1103071401003511944550851078003d0039105131700c10800c00110041400200340c2d03180d804120f411092695800b04504885100d0542401c12113500c0321154a010400100040705081200c9100d204041150a240e112240b0140c0c50184020a0741254804800941040000a0307008000d400d2030510b8200c00d983c802c00200014884001222441e480c1c4003400b60000e00d6018141e82c079118011103904090030300000810301641407240c9404520388143303460030b0800c24800c544078980c03c449003140030b141131401d18418002c1009020b0041e803080a01401c1d45100b4821055162070003080403800310000d0b030044014006280ca11013804201c0000c0300c01c107110400d082c4540c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 519023642 1250 519022392 519022433
    0x204080a0510050f4b1504090b071101060308030109090339210f09060201060e040204090201121a03010b060918181905010b0f09180109 60
    0xe44840d11001c41680d40c00791104411300d4062040c40401a440303000401c44442c86070820855101001c10f00c5040c21218440d00002401000c5400720b075208075100502c01c0101c0c44a41d8036950100301070004554211902801740e41c181c8021072260f500c00d00656404d06406070003c90716a880741c2b10b8800552081e80042100b9554002800405400024002c2d400b21040c030794480d814204001c4a8a10300c0c1c0c20f2409011a00d070401c010100401801c4646020442200e9500b1412030300b5030107017884501c00d00010204407191000514240305001d0101a90000f0386007000640780d6a003400007801a005049050003a511003071a488015413180310725044030b00c40e40401d1a10034100f4542100d0703c40d45c207107004e00005c21480403d0784503400c1d0108402001001c1012070340c5c9032071035070004910025407000c00e802188064161241d502d000c1c807959a0140b00201300340000c0d0410050b00c000c2d91a4141c0d00300d005e804c00582c0b9002c40345010040d0f1181c80e400411403141c140d440308144003010aa140c40b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 519024892 1250 519023642 519023653
    0xe0c0403120507140a0507050126100305070e09100905010b030604110a0b090312070f080310061413051003060302060c1c02060f0624070605010801150e190204080a05 73
    0x1401340564035081200e0024000c0c110442181e25455180c1255003e03880c10320035400801131000300d480d0550703100406201d51820650070b041d0103540e5414640e10041d1410b11500e040455000c150b0350559000c1e15501004203a005010104000a090004001c1d2801d5685822805241d1000d001e100d105034421001e420403041d1352010002ca912058000d000324400038000e001d0207440001e080d144610795105016221080781c80e00303c0900c40c182030001d00d000c101100384501090b4074401201502c19035160b01e60b5510711025050075900440b07140c258144891030b401c1107a4108490b800b04441c061345000b0804546070f0300480d1f013503031112100d056030354810003851801000e649180400341300c00f0b1000e0b102608061403400380354803002c1c09440c82030403508296448540b0711448590204d0192424030344418460030030700000d1100b441041d40303039404c2021030040020029084000ea45020003001096111078600d07a0b1810b00240300d11000d80d50800021a032003504000c0f00072001e00c00c000400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 519026142 1250 519024892 519024907
    0x201090b0a0305180102090a0905151005070201020601141f35010b03070828050a05071e050a05090406080f0601030507120c09020702011812030e0307030308010e0c04031205 76
    0x30031540181344910343c2c0d105001842040d640c0c2d022420440707044900205040c3c880c8020601180306103201c3d5a4080d10b044e090f190500d4000c0085c2001c58001d80039985241e0782d901c0b82402004201019503400390740c8080004d084618854132140008880c585021501d5006c0c0d83c0c40c9024030a050381e10504898155103030340c041c10035203000e8013401140440c0f03400c5091a41c0050302c8200068800d003d41c80c0c0340d120380b41c0d01240d00909011042e03000e44040c481400d2031081d8034000c1409680f00c10002d6a281030b00d0190b12221aa003074941805a030700d0910300740350008100c5558000b41841507021f9203840c030004030005d04001c41001d01c1288406010254914034105e4079001d2281c0c40f1a5201d141e030040c00001c215049880c030101c44007851701507a01c1c201c0e03100480b0f00309540c2c5807041110b0b04540010803440d00d21800810301c10312a44500c65140c05881c00c06940740242c0c400100000d0010006003c01e0028030420b540000d0b18080b8141496143d03942c14100c0c08120604c800003940114040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 519027392 1250 519026142 519026161
    0xd05070306030c062c0105090d06231e0402060a050c0c0d0b250203040b210a020a02070605070b041202121c0605010c0f0602180307140918070e040201090b0a0305 71
    0x4245c40c100128440003026100d0380082c009000b0042090301c9681c2c540e1458052103519000b4000400865080800c0510030302d00c007000001c0c040c0e078068000c00e4a00c0040b040e1000c00c0710400c0c002d54000306428100f081c0002d0403a0540c0c841c90301c0c502070f405598100b48aa4035075108002d1442d00c40c1a000d02c80e03180800a00f81a502c5070710840001003840c1030301c022101d070044210707010741e202c0102141d9601c0f04c084080b001c038044071105a00c0e49000d03808000031025558068244596140e0a07615826a25942241c0038014240c00dd8880d034071040115000505100114965800d540192910341c0e160841e81041604803003c000303842e85114481a6a0803018414500036041c01d09003900100016117886408400302c00000f4641640080c00600d40ba9a001c04101107040003011540580d07143c0000e04076070758403e8091401072041c40041350b04250000703103d010305114003000300500d614203452102d030700e08050005c0e41032085618021032440c42601c0240049511510003049500f00015403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 519028642 1250 519027392 519027437
    0x21c1d060906070903032a05010f060503070303050f03180d02060f0105090c1207031104080307020301180b190f060e0601080c1e0d060b0a080a0f0209060d05070306030c06 75
    0x950801e030700b0400402c10070503080003816003544c1d014138096030710450311516030401132041021182d2031808400d000d0304214054018400d0494039000500000f41d41c2d03818182d41c0c0015000040203c0c0e4240a40100c0001c2c640c003461b401005104603854158001d6100c84c01c101c61304e0001e8006802100400000d80040c0501da40142001d41d0300c00454606205040c140303000303103044089042d44900100d8802031198020203110341d42c401c040381c2da03255141a05580c81d40000d400320700950816188158200108060380a1b81350803403074945903540d4106030035030007921284810f40c0c1c003540c1d200d001603241e13240e204036005000e041d2020003060500320005001620002c25200703240004024080820b10030034501e00c1d01c450011401c54039902c81c001d03810b001d4031103500b0003841090049201780e010b90784508054000c2200803000c10076015080b000009030300c60100d046030851020082c2040030851580540d0f400368642c60005800e58580ea5250300c40403031540880c000550402546051160302001e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 519029892 1250 519028642 519028651
    0x15180c030303160c051e010905071a070f06060308070c0e0a110d0b12010203090705100e0a06120209030a03230405151315090312050309060406021c1d06 67
    0x560079443c280704510044002608030030304002c42c50303824208003c0d00b0881c001c0202c000084031a408202a100b40f0700800c2c001905942a1040c00b4001030941403468242c0f0b401200c41c0c04079454640c0540710020461802c00c0115000ca644100c00004124a0405400030620070300c1141201480c151440881e080090f06201c107a42c0b03009904208481241e003203604012582201049012403c40000d0f440084100b0700c01c200c0d4000020010a5400412103100350703181200c5040d004800303483e0403108161a40301d041d812103d09001800f120780540d00c0941c000410040142c80d1160401c04a13040440740d040460200b14a01c141c03404aa01410f070700703400038900d2485a418a0314003030010394044041600ca5401000005901e603403030300c80c05912000f61082280c5400280240e0400608012040c4421b6944500722035003205103912a601f16400380f100302c0d0080c0340a49440d1140002540083c01d40345140d85481083c02010826002e0302c07041c3c03102c02c0d012119895840c6d1a003400c0190040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 519031142 1250 519029892 519029899
    0xa05030702120a050720130b0a090e030706111e16021002071814060d020105130f0302010e0d030e120c04110d0605090103050712020103021216180b0708090315180c 72
    0x48a05606464142c408001c7c1da07042003010506400280108040000a82054143e1030411002a000540010007800014800c0100308100072011b083c0c1107a5001d41300c800301100f09d4500c0a2100d10941c42c010340710303414400c00c220071840c60b0703580043c1050300c00d16120790158214400420404005501c00120620241d038184001d445500e41c1004908000f840d00303200385402c10810b019a4130540a55000280060014400c152216060803c0358030510080380007030315807011704070241010400d40100c01e138107403074104048140310308105405642910b451820f1007040ea4010041e03886000340c280b03150300790380c4042d074400300401650165000d0b40c01076030040015000420025000184a104844070180c1c2d0300e00e0791445200480c064031400754a282c1c2003080d4ac0910840303602e01c0c0340a20a080003920740c4840200c11185100c54440c1c00d01c60850f02e81814030040d004103a0303107002880703003000080c1900c80c6140840c144042195041d5060785011011801107542c802003040540c0e42041d088 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 519032392 1250 519031142 519031193
    0x8040303060503070f12050a0b0c03010e060102011b1b0b0a0b030609070503030f0a05120a0e2407050f0d060611120906090f030a0b041101020d03110a05030702120a0507 74
    0x800a003814400a201b000a00360040381c500c03060100501141a0003684003001e0052818041090026a08207001c0d44502c0300c001d001264266005100d8120801d450780c1040f10101508801682d0180360380d101d0078406202e030541b000004400f0581144289584400020710210200c1498505000248001c00581c0641e60602490f58004103541c007800d4044030f010368645980303804682500034003840340c40d480c02c0344060081048642e084080050030340012144079903801c0706000c00241300c1450715102d11045d03101188000d8861300c001e201d200c2c000348042d854000010845803c803046944003200180d100c0800b0610204280010640895004800f0742070500520026886100d44101d85100b907201d03103400300503a1030910a0344201038005041e20624074285c1048107030022841e50080c010300620384030000c081d010f07124466041f403000031000d092002299017508d29078000740030784044d0b01c07402c0e181c400d42c140c1090007001340750f0051751004c2d20360406281010302801c80070607144247d07a61 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 519033642 1250 519032392 519032399
    0xa03111201031b08010204030c0e0f060904060f111b070512060609070c120314060a03030905190e090304080d110c04240308040e22060f18030804030306050307 70
    0x30030405815250030203030145010700c1149401c5507000c101d602c0302000d5400480c00109000e40141d41c1c8045401001000e551030b40d5400c0703200c66500048a03956800042e01003c0340101c0c0c00e90340f10404a061030400003820210a0700030f1140c0313400c0f0100000241c40c01c0001600c0300030091100000034001076520594030152a40000d880d18401800396015131a44400101610321610709074171801d400503820383c0301d030007240c9009000c1d200851040c40a141d10700c001c0b40c114240708000b4800c0383d8059841c8060903040808000041000145414241046640c081482c1c0710810303179240168031445c001c640e5149400c0e500b03070804038801c2031030b4188000c0ea05003174601100807070000100d410440d00000c210110500b4040c08408544614020b220b1000f004000c1013101c42c0107209881d1740f620040b1840d511000c4800580ca0b0655500746900720130f4120000103450307038200084a9a00c680003140c020427210114168480580d0280c001030010424002030541512450300600420340c05842c1303460a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 519034892 1250 519033642 519033667
    0x20c0d020d091401020a0b04060b030d05090607302001060e27010e0325030e0607050c0913060507020708072310050c1c09090b0f03010f020a0311 64
    0x540d480f49a8045000c41260405603209004125905038407094403246410a42400801448102e00c414028071525820003981c80c01601521002c1d41e00405039031074604150394070300303d0142c412821151224140d608610110200f207103a074008407150b0700c4507051028141c114101141546040400782d01d007002c1400310b400e441c880203601c40102484c02ca42074510500c18001302c2c041c050741404a528106200706d440f82c0210007005420312548181910b00500e142448900780e02c0d80009010541c6541480c0b06402d00718040c019050056041d1100c003d951b1011500b090011104068110440d109800030000c4070b00c58070760005036074402040c0c03003414020310a59400c41c80c0180382c1e071070b01f034500010203c142d8148070507070f0490003901421102c5131100015100740c010314020042401810b802c40407580c0d00d49280003222010342d613210a42ca1400c030080004000c48886690401c03108240351016071004d004000050400e40401640c40702d4103680142194010080164043d0080290022280 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 519036142 1250 519034892 519034907
    0x60114090105090601020f0f010e0f120a0c0309091802090f0403170901090218100b0f09010f09080a11100201060308030a020901031d030c010612150b0a0f09020c0d020d 74
    0x20030a40f42c800d060f46a01006034608600508010618400c02c00c210b0b05151040d0486401c150114085900100c9150211034036001c1c500340341140c019007400340401d4144207102520319680641415a94030307450701e03100c4080da62030440c061011055004a07504500300f09540396407282c114003103403145040965006000c8082541c5040030515110081005050b003948040c0120754000c0c5003510500382c18240c0c500100781200e03000401b440404c00040c00355001e13002c49813920904c030001c614194500e0f00560f19030480028280800a0410001c100414100708031002640501458540e4901410405c605c1003000f042d12411641044020000142170381d041d03c3d04407205003409a00c550310200101c00030000c203d5120560b81201c0003c40624a0100050031013150380d81c003d102094a075007000405080252004010100c140e503152881403c0e640070040c4a00024181100c0540e141500002803140782c00c18032105074000303103030300d001d510420422810754045c0c0054008540001009070001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 519037392 1250 519036142 519036149
    0x60f09060b12070e1306090b060c0706260c1b12041412030a0807020607020c06030402041a091006030b03161206021e090103140f1812040305030a020601140901 70
    0x1128041400c082c02800121010100034004240305c01244803460054240340c070804c4c0b040c84c030b00f486004050520b6011201030b024144001d083c15031510394116001040c0c00811000745072005003140c2c3d160500d02c074940c00b07500514a19903c0da040c0c3c204100d94181c40020161140d405400c0301c1c1c0c0407500c0a4161422580240c0080460b1600314000c5081030710940c0c1c2d224254000000c2c40381c0d00a80040820b8000c0b00c10303a084405668a4a800741c2c1d60f080d14888180e0701c0740e01030001900503c1d15400c2841450701d000d1806a03006002d202240020106917a1803100110400c42030068030383c0f500c10040b02d400d0880083c0304c81032000ca09040c000405004d40e072085041551b00205000700d0b85c04941382120850500040011009064441a003102d14050300080c2002c020780c9140d41c0100040b80a0401c0e00002200c0751102c03802c5a01c08103c50a20820500800035100d49114458000d00004c41c002c1e00903554610b0720840013403c0c40c0d0160030641110394008410300e4162514005030307054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 519038642 1250 519037392 519037417
    0x1e060703020f160506070908030c03090f01030e07060206070f03021c02091504090b1005030601121d070824010819080f03040507051005160f0201090513060f09060b 72
    0x101e90240c01a4400351183d400b00b180c1181107045008200040069842d10a8603660b40d500e50058035104103940364407665110010039841401100124074003ca000781300011305040000c0d5603109050500d040c03103400d078000c1c1c025030011400c01c04400e4000c1c0170034017031100702c0c03a0031407501440c02c014154401c1c1f20b06014000e02e901207500c2140e07880d2841d0003140c94642400700d40e111555803009801420f030b41e103d228050b481c10301241c40c2d242e00400907240a00310503112500120b03480b03810031b00144811820005e08114002d25207030001000c1c41654007070028140502049005a01d100c000c52254503003594031203148000400c1100400b09452880c040c0035801ea481c004003600300b1345003234010210700c10b54078900001404100000014a6002c4580170b840d40a1103807031186081d501801400e80c442c0e103091003a4120400655200071040303540348141003520402e911000402d408007024601c0c2440aa80c4050901210201c002c40c10010004400c0512100303042100d107001900868007013106 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 519039892 1250 519038642 519038647
    0x11b081302091504090c080313121a040222150f080709020307020325060b010f0909021e07050d0e0303040302211f24080c0d060b130e1e06070302 64
    0x1011340c3c2c1c0303410045c2e4054121040041e00c40d04c51100d1a04c1b603100c5801440c0100042c200000c03440342c0901c40204251f006601c2119a2040c00701c0c8031180040204102e13800150380c68003003003250344152509943c0522a82c0080c64420700b90003030544010355000b46d00fa0900c2060104600c40e000604241030700d120f0100540c503034861110903491402918060540044400260003e0410420300500382c6030180b0300c00e0210041d0740c0300560304460700000031800607040007418011150280c000308944a404080700b4075604034900c00c0c0c041d80d08a504200d4980d00040a003041d00d6500c8818110441d50881c007640c68685141d00040c204010080e418011007a101440c2e60802014005010220504c00c2d211010200d8410f50900401d0714000b0b00c0026003040070300c46410540c418106068640c0c102c0102080f500c403c0c00c1008165002d41d00700c0d55140c8860742009241c0752058840c03802c498800c00401c0030701c59640700e181049840d03001c03004d0644690300d480d2902c02c0c00051268004085050069 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 519041142 1250 519039892 519039931
    0x15060607051f2d39170a0203180309030307140a0b01061101060803030c07032f0604020112231e0103110406060507170a0e03011b08130209 61
    0x20042e10302c1e1039090310000780301076003072860308150444034032040c2502d181040400559488181080c08038502e07030211400203200013680075030003d42d40141c0e00813070900b0551406002d6404921600448503c0500c9802000340601110041100c8104950600246081020b180c0210f50369000d030301b802500c5e003541e200c1a80d24483c070612088a003150089810040d941c1c4640307001d0130124101380d001c00c0b150328180c3c002880c0000802070302d0041800d0080f180c900407013518100c8180c2c00407201d10401213001c01e81c04041c0f0500710b44400400c607400018044501d030600001d05146211000d1951140c04c2c0400c60585003912803500758074044000c46180d043d05c0f8001d003010260400000d4000b000008800401400050514600c090070304031400e01c00c55860766022a100d00a000c4001c1880000b038480403003210240018100c4d0a040c0d14000f00d0904c80c0000081c00c2d41c0b20061242007556031710204032040d9a100d0fa0069014041d50026408003c0cac1e079000c03485242004105440182001c462207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 519042392 1250 519041142 519041203
    0x3040b0c04080109050f1c201501030c090f02091c150f0207050105180714061306081902031006140706050f16020a080a030203040201020c0604081506060705 69
    0x1900600402e800070084801c41d45000c6a4603804600307100e055204d4140040d13150440116208500c0019595101e5041e0703130603003115901c486541c440c210354092030820b1010b08486003050350081d401000590543e45c60035142204688010210b485001d004111007034017516082c1ca00851000003800105910080d03041c03851010604103940710103141800c10070f44410300c554001d4074009002d10001c010780c1d01c55031541c5403201c4206500b842d02d030304a481e041140039108500e4070344a07100544628a411131650022030403a025401c0742c0c000c14925014401180c40728018505400f03402c800840c6582062803000c055134920b0f01c00c84041141c031509144501c0c1d90700c0151242c20750b02074028041c1d8280440305650112040745c0038029007062070740d0b07071881c41d01c00100050425004848a03103010ba54540c11400395000900683c194861030002c0445622440000c2005200075000342441c0b82c5400c00201c0047c20141c07605100d01410b11a83d004942c0200b206c0300c880e00e808003c503031709013020042b1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 519043642 1250 519042392 519042397
    0x2010507060f0515091003030c0212010b0a06030614100e0d050a0204020f0403141b040b030c03100204090c020114060126072129060c010e1605010f020303040b0c 71
    0x38042c1090500c0144112000000e484115840045902c032038550b4034800845c111105070b04c4043c0008007139088400242c1003041410030071104110000c1000303284580400d00703c2c1004d41c8078100281e51103904000d2009024842c51400d041160a03c3d1144030040700180003944840506114070048415075080003803c0110203130013030780a4001c1d0349840c09921401140c0d00507210a482411035240707184981c040c0880c001c00812007407072090325039151602c1404010241c2240150b058880e942d01c4030140d80d42080103070810040c090700982d85600b08907120081c1c5683c90720b0030b000d582c1041c12001c4007450850b0750ba0741c04403082c641030700218551a04ea07001107120f04010444005c8400030700600b0303a4000000d1140e200001d08650381980405c038103904589810211181807450311000c50007108411000141d4800700070f00d610f0800c40041070700380c21140c140984914aa00410400b080506080580340052109091000002004ad034010f91207102c0140010840710384000002d4800160f00e05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 519044892 1250 519043642 519043661
    0x120a09120302030a1d1e0a0f0f060603050303130507050d0218060303071a0105040c0c080706050c0c030a03150b040e16021c03092f01080a0929100b070201050706 71
    0x140b160050b011060156100d02d40003039041d4106d0581c9008943e0070a0001b11460901d51240140703509020f82c1d02c8a00c81400c0130401103a40b82e03101e40000000c01c4042003d11300904076022202c1503c880303031500703d20300741007a44041d02441c2e00000b104003582d110407419580080405201130103590700400642540b044200007030401314000303043c59104a900140c00d050b03031000c1c0da0800000200d0b0405981d18500b0303d1006122070410003140d0f0004510340c1000703402c203080c04a1142081005950a401c0d40c201907000000259140c022884d52444800c9100c01062441e20722840d1904158102c1075a100007410070740036140f13141025034017520801c007800d049000c0c0c2d51307000c07241c840071640203010340707904401030b608501403429516803019258103001402ea00c0c200c1981d40101c00100644030a80024804011039070359004031b00118030003000d080f09040e414090401d0004a40a410440310300c0505118a8004414024080d8035039507004c941101d602400c100e038032101e031860301002074050707101e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 519046142 1250 519044892 519044921
    0x50a06080c010e04230f07021c0c03121e0501050f061e130f08101422020405040f0218040201080402061605011508010f092d0b0903120a09120302030a 66
    0x7000d0085c094401101405121501e580b1900c68641c101d00f03e946503902a134091301c0c2c6043c0502c844886000741c400c1c400c0ba81c17081c10921800079218a03064103d510481d010081a0b480c0240700c01c480344984903032405031000b22f428940e010ba0003800324140c0e000c1c0fa02488000f41c005c001b4207803400f4103c019a02c801c001300c030039010b0071501c403142d8600b034030801e2080071500e01c50610081e038243c4003406281ea07404c00103800040d0b180d491503052074424072204558860014030b80c1807440981c503a0f001c1da5108a000d8180202d040c0c03041c0c818021040c00703010000710091a050240720050381e2040c640c80d000707901190641c1d101c1c002080c0795200071980030b000820942c6808640042c2107100d000800848100800800c070f2032303101420100a40718030440c004d024500303404d00c07042c10600c00d5440700d440e0f00110711141ca868000381d8882a44400a03a0100d00c90790001c50340e00c21003100c038510242d1140c2d6040e02440ba0014070758484048400b103c1c40d00301030580100002d841c02585520405500b142e14 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 519047392 1250 519046142 519046181
    0x40902030a0603060c020a15050601110102130614070b0f040201110f0c030c0a0f1203030e100203060f04020a050306012015090609010204050105031911041701050a06080c010e04 78
    0x41d24501c0042c041803000b228102d041c05003840100b03001140b00c000c02034106080284420140d01d24000800c00202003034140105a689407180031003d01c050680803a40728804901d09040c4031000c5c0090b80002c0074040b903458108a2440000e040382c010341d80104132900329080f1a1503510040c0e8652440f04100600c1c2d1003200d800071800342c030019440003001820b8040d40d802c4400b1303c05110105c5291f001c3d041c190481881c040102801d490b40c44002640030707142c0007a41002c09182c00e410080c0300d64003140000d40100602425203045200141c0e140001c690441c40c0c600c03c03200150450100a05460622080203000c100a0060901c107400034441c5600342c55000c52010494814410141e5408480c0c1c41040d0000d890344205108403030030340b80143c40d01c60840c0d46500700440000300c0b0020640d82d2540f6075000310241300d90100500060311403801c0e41c1d00c0f11101089010308407040100311039521418040c0030030200002050450b000c1c2401c0c82c119069903109070100b0041d105a008540c100c1a16 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 519048642 1250 519047392 519047401
    0x170d020906031e0123011103070c0b040e01090207240b030f0a0b09010204051c051c05180a15030b220902030d0807050a120b09150406061803080c0304090203 69
    0x5288225003c040510b5071a60b0a989541e050500c1c151000803021060b070150030410300ca58050701c81c10751010003403021249000090754441d0300c00d00250b449a0320a0348081828003000f900c42c003d450240601c440c0860409110ba12112141c0801c0440300e0401c0c444140448250700c0d003278212010081010b012582c0000302d0540ea00d541c0d00c04000241c0b1402c5c00000803070103009040c0204c2e0100c4100500c103040852600710b40d40c03100b00c0c1210f41220603106801580d041400743c2e040c04803003001d00f40c5419031182d03111040503903400e6500c0c0803a07128440825080c06040144602c050005140f0310b0b00140d000e0381400071507052107d029100308801c0501500d084440c107641c104c6100c540c42a000c1c0c2d2078044244d20141e4601e40b003542c2e0b500100c0e5040c80101d10703d9110788100c1120b41d034a01003300365500c141001c40d0364090241d45080001361040b007200e819007420f0040c00010442c1c2e00e07000d60f5041d004180c011a00b07856000082c12945c00186a000e015000c1080e20054400480215507074100b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 519049892 1250 519048642 519048661
    0x150606081e04110f0409030f121505150d05040b070e090f07080a11030f06190b0d050c12090c0301061a040506090d051207060c080f06040c1b050f070b07170d02090603 73
    0x52002048000541c0d241040f03501039014000e00140301c420074000310f0350718100000c00cd40100d40017a12188844244284104c4565a01035240124007030b43e4204080e0400003801000c0c4401d044c0964040c2c485007007400030010302e5000ca590300c072440b440d250303649440d554101005030001004060b0114404420710001c0003440340c004d03020b5442144d9901120109a56036450303507400b80320b41010450305102041c8170a072240c0150707034048540c01c6006d00e84803441300303220403008040e150300c00c180d0320404101143d41405d10456020344100c8401e2842015a450200078a110358001e141c012000425095296110081070300310140d8000103452900c49120140c1c10940c010350016203c0c5030a06140d5407000d4017584a90f4005c000c820100c401035621b080500002d0407200d40100b01f08006451400d0650054412501d0b21501c00c0c80900640c0b0464020b062034190070707800a0460310310402948001640d118400381101200040c41900c03415100c5010f0001c1c041c500380c1a07002140001001100340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 519051142 1250 519049892 519049907
    0x30723090d031814060307050a0905040501060e0f19050d060e0d022811041806020f0a03061a031f08030a0f170103032307150606081e04110f040903 65
    0x1210240700c5100f03550346408801d41d0080d0301403690403d0042001c180c40902c42c3c070051039000c9240c10308072529a0b072080402c007150701c00d03032001000a843c84990107080c42d0080341c0d9021071404542c00410420035050040c01010300c3e100d031500c82d14142c0d5030b8204102594000040006000043c0e41c41c0b50021000a0b4488003442044228960080b03244e62040700e10441903010250441103141c2c03860340303600070300004006000175400c1c0d100200c001b000003d4498001405a40040b0b010580c9800f1010400780c15501c264100c45884a6101c1e840c00d500d0141c8015a50300c5011315000d03014144e0584115000c0503825000300c1101d001c00a00160016000090f40a030a500e070ba649103407952100700312500c0b480c1e003808014000341c189e0418002412412050302840a0501d44c110306d8031140da07035081032901c02c81130400310f682d0311100101b20840d0800d141692040c1c4107003083e001010200c140c1d07804040001c0c402040d1044134441d408840e150b80d00e441d003180700041c004002e4100d1906028018030b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 519052392 1250 519051142 519051167
    0x240b0415151706040c1e120b04060b0d15030c12020109080606030d26190513050a0b04060b10020a110103020903030d02030618100e0a02030723090d03 66
    0x4030351604888140e40e22440c40b400c00250400d00030340403900c460003080084c101c0840b058041146000700c0d48000f07003a200c0f2010032110140c0b9521514054002d1140a0310400080306201c3c5150034010031076010307c1411901d891710600c00000c0d207144a01070704c9644510b01d07000a030030125015000b0880c0d60b0045e4481e000c580c000d80b1140e110702e54900e905e940d034000403961907400d60004909413011a0240c0c1e02144146811200e5003030b101540040000c0c80c10084800d45813018150071010a000614400c99400861303030b0140249030000e90701c9640d9140f907184001003000d0910310005040c00581e5000c10a0078000401500c0c1c215203d00c0001c3d5500c1c0c400c042910140c072100304482c610f40c001d00c2100c06404001d000345051081c0714070514025000140020b0b00318004c0c0f240da070383d8004102d182d148039003640e410321130039242000d000240e03e80d0003d241400305032042052000c5241c000300203200585d1400034126110088010045650003040e05040d0440c083d006004201600000c403520b60 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 519053642 1250 519052392 519052409
    0x31b2103020615010f08331c08040e090a060e030c0d0e0307121e1a070e0901030204020d0618060e10060906180b040b09010318240b0415 60
    0x80391030f14800e0441c40c80202199a0110720001020401070b40510341d480d9001d2568110300c0c558404800c2803a91440780040030030a9203114540c40c0c240307403811042c0100001c001000710741c2102003d40e01e56000748194014000814200c00c00110301d25000c002092002d98403210a01003030303e5030710798640d07250050340729408140100f0340e07090080340c800d20f82a140d0b40001030040c1071040c40c105e2140c28221094034240c41441d007030000340d000a92034208134100d480c4214200707440250720701154282541c029000504102544140341b0482d80c908002c0d41c1942e170120f40050f41c910301c00400d5002041c0f2036014041c0304c4040604040078000b285d106a040700d1418803400540d1342c0741c01100b04000d28a0042001040f140703202804018403401c180c007002c444022004e031a01d51120844030b03c541003030380301001501001038030382015640360240180d2401c9400303040120300583c0d955145084002c86440c92100140c80d610342c40c2d4a03030b0b41c000424051002e0b204100720852401e401c0c3c0c5d48485402442d18 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 519054892 1250 519053642 519053653
    0x60b031f09030e090702060615030603030a0e03010e06250804021806031213240f140906041206060803031e13050102130f050d0b01031b210302 63
    0x155420085000c030640900318036810102040c42900100910120318140c1c104400359491180644501401302c3c003569691b001052645040c0c0108031240d03100000d00707092601c0c1070081c171940d5140041540d800900c58181164540161004680105145030341070360382e807240c0c0040c012208090f03403188403544038000c0e003615811a500710070340fa411400d943c020f410054421103202158046e101603500103000805480c0c0034600120582030a8100c900d00d004500f1201c0002c00070808607882203000e0080f80c06d02c6407040c9140400c040c00d10080000500b00b845444944411091915011280c0c00000201915150380d2035061a0620051002d01150303600e00d004404120002c000040e284030b410503011401000d04078014005c51070b900034160051009180b55030300001072082c0042c01070720074261044403040c0d190100f84007040d4000d41c009401481c00441c11008501c1c0310481905507500458904000d913083c1180040d21002c550181d100d07200c002607180ca16030300101383d0844a9019034211003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 519056142 1250 519054892 519054911
    0x94819090906050306040204050a021306020c13110a0c05010204090e0f06010515031303031404060203060414072c12071503110a030b18070906140c120d0603050a06060306 75
    0x201c6285009060b03043d4007060001b001403605811041d405010f210001d41403801c0c040340e440d12007440c0d401c49000340e0058108000b40d820300c89141c03d928103510310140414040c0310846881ca1088596030020800300c0340a000134010250100c8000340040320003000b6088803203200301d458044003500fd80c0b150155900010700d6280018545036848050f00c1c64920350b440c5c00803440440e41e0901c0703080f8140340e107400054128030910801244200e009501c09607030380c03400604000c111800103400e111a04480e40134400d8241d03214450101d04070340ca08101a04142c1e00303000e4090034050054007548505c0c00d00840003050008103801c01122111010b220500c0307002001030b0166441c0609080c1a0750090220400b550301c04d40101d030038400060420003031801012241c02c0c20b24422140680403608542c010010189c0c0421055000c1c001e0150890401c4030340d10100d82c031a501000d0617800000c0204840000d04d00c290b10207001503a001c411202e40c51918504480501858402590131600d00460341 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 519057392 1250 519056142 519056159
    0x1080108070e0106050703170c0d0c141c272006070303050a021b06150d1214040906060e090a0207050a02091f0308040509481909 57
    0x11070030765480c0761902d01182c0c24018101c80c90303004028217404010074110750100f0851920034141c05807208400e241c3e80e40c080a025282994040c004050130002681e140300109030000c415903e03008403281002c1e1829500d495944040c0c255144808104072003200b50f0b07004801d4911380080f4092042404001400e100e5030826140300302d4641c4290026001c110100000b840380e0305c41d40e0b0207044501c00509041015003007010b198445140140642c0c482c01c2400b503800351100782918a4a01103d00c80b0b5275000c0b994440244d40c4168030503101b0720181c0d1b009400c010301c8820076600501808501003201680d214802820715801030005402018800d0124444500da4000c403602e45410400070000f041c650307401d01c40c1d1040005c12801c2d89080c02028a0303400b607403a00400b0b0065001d0380c00552900c0c10704040102541000e03220300e00036924042070000009900300c101801250b42d8500241d400e140c2c44c9103592a0079484862003008000190b0942c800c003041403000c1c181d084507135905110686a480a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 519058642 1250 519057392 519057403
    0x6020d20010b03010f020706061d01090f0f23090c0a120206190e0901050108090604030f030e10021e03090d0e010215090f0601050603010614070503160308040314070c030204020306120d02070501080108 88
    0xd414406001cae10060002a2a40d00000442c070b00071400000d07101e8a110b44101200c00d0700004500c26400b020880b024402030610590300205c00402070001c0d0541c2d1000107112144a00c2810949060400030405564604080c1d0b00d04c0703010880c2e000c0690294250040402080d038082600c02e22451001150175446480e1540c0b0585011b0020103c40d200c0c1e440c144d600b444281d0041081580310700c2848454142400f414a502003c15409a11040a021019241072803c1c1d0441344090050040001c41130000598211000b03142c00c0500500942c140101e003800b500c0d516101c01d080c0c00303005008000c42c0c00500d00d00101400c5094904998075001040701603c800c1c0b049070000307488034400708880c140103801450214424402ca80c9022011070310681c00401c003110070380101c1c4a030010001130540003a203500640110240303003443d181503652030500402d40c03400041e020b29070100c0000e07645e884000e10440b46010070342c03c50f04484400000256910814000c060000d05400000036803140000b9030b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 519059892 1250 519058642 519058679
    0x150106050a08040609140d0215090307080304030302090411030405100b030d110c030a050f0d030b1f030b030a06050a0b12071a0403171306020d20010b03010f02070606 73
    0xd800c1e25007080c0110448560001410a4035550341c1c132028480010302160440c180c40381110090500b40c1c1c10b0b038102904042038501c407500c10345104400c001600e90040110b6600c40d0b030208185440e0303111400d00314000d010b40740b0016081031418816034683d00e4014061813240348130300c00321005464060079081c10380358001e0a940d015480003000249460241c03000700c100c0c118030412a0320761100ca0000030314100e1080810341c1d00d90040c9905d03244000c8203100502c6040c01c1030500f400032129034004514005280c00c4e80c460a10f14003c0010f00440c03007a008004d98642c020125501c490030b50401d1001010240e500244c4246488845400c3d402c0598017040c0d0a2512000b03407900782c0c9400c0f1000003071280703140d20000c41c0604202c00702c00201300da8401680740d025015101d032a900f116169100c0d42301c0300c2c1c1040c1c09540c440030002c000e240d800800255004800c428850340d404107540744a014104003c091a80343d400c003035203810f0310f000c03d130301505015009010a00c400c82e6607000c0c00005801144 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 519061142 1250 519059892 519059897
    0x9090109210507050a0605040c0608040f061107140d181220060a091a040e06040c030f0207050c09060a050603040605090304030f1110090f060c0819050c150106 70
    0x40601c981408448800c00e40801401c001d4605016940c0d45418000300c90012180145d580b0244418400100210006000c03503042c03064240c1410380300d01d000210f5501c0018192398949a5000c40e0340c4040b03064030392550380000488100b1014284040d16040080e40b14400104210179003080600d100ea0706c0b90444110740300400100ca0306031a01d5214860009020714411030030140c440b5140c039400d0046c0800d034540c0ea10600c0c95803e0103442003000305030b040e41030f15620090005000d000d26820700d076500028229000500c40001d43c078190007600700036501c4083c651003c600701301401404542c100c0040422245a0000e80e0703200308210f00c48559000300c40d00030300288006000940d032648516007049500040740d091555a035120241126002c104460022038032486013030a080180340d4041c0180542481509641404107481e0700c038003903208800070480b01c03030803903814480070324200c0d2134180c544400904031805180001d400c550008401c0d0b07900d4070074414182001320501c40107e050751041c1c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 519062392 1250 519061142 519061163
    0x81009051203011203020d0801140d1e05100b09060a05010806130c050d2a05070c0f030c03030e0306090d14040b0d02040609080c130b06130e09010c17010504020a110a05030909090109 80
    0x38041c06800f04032080d080322020a12078000940d02044940800c519108000801c003000d658130302c1c503041e6a8003800c114000e101071414042307652e8404400f041510804e181400329550b441c00000c00900688c0c450450461900740030303c010303070740c841d00a041c11a240c080c07c0c803846c80076101c08000b4072030790000d0403401210300c3d0005001c0c3d44940020141203014920707280c4180e8441d404c1e01c0300780c00329034004c8640c503041e038004104154110005403d40d51003200544440e181104500380c88400040c50181000041d01c5201a140000d2054130060034400366840d4035403456294a50095200d400b900011039420100000c42c00400201001a40c40192202143d100c450a03030b44040c20841482d141d0015081c0210010341082a24200007840321008041581c14030990160841d040000342e1020820000c050898a40030450a94116803003614011f0740e940364503204a5240715401d890100710300801c1000014060000090b002071107003214002080d80742c026143c0e080314901350004108451a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 519063642 1250 519062392 519062429
    0xa050603040803160203130e06090c09150a030908160b060d170a0c020904050706090f0509180a020a061101060b0c0a11040b13050a0b0901081009051203011203020d0801 74
    0x4841e03401398141e80112030802c040106400c00181d1140c004e41906070304a400c1040e24a042030b48117030000b040317001071480c20000030040703414480700c0c030b00101e007244000800c406441e100303174444d4a0307564112100d140c485480340c15442c05192608010303a10100071502150b10303491b0000702c15101c540e0208051003000c518044000399a000300507880c05015030325000c1000b40e03c50316101d41c8100d21417030282018908080b0082c01101e00fa0700300045004841c001804146c503412512074116049000381d2a1103c50302c905940b800d103c030000290031910503540001c80a030864841009609008024490130351103480716001405158030185456000120800101d20302300c5a10514040c05400440d07804601c0e404550300300c3c0145a907070000d6a4070010440d0404503441548640d100464803161603503d0211040c3e034640c2070854480d805907407586010104101006540f41740907201c800039071030b5a56410749a8100780d4805095000d8020141401c280341d02c50301a09040e00c18484030380049410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 519064748 1106 519063642 519063661
    0x30708011a1c021315020105070305100e061807020c040b04060f1e051806040b04140c0f0f0c030405100c20010c060e030301050a050603040803 63
    0x30582580419074494004494005902e0801d104000054100c400001e100c0c1d40e468110b6034040d9400050050000d0708403208501d00e40d0000c00980d6a580401d60a440b001c560249040750580018404c9080540e000e0307803c428081c1030f1601401d00d60203c405040c3c42a202040980d1202c405005149030900603d000c003c0d0540d4240001031401c0c3c940e40c0880482d020b41101d00c00c902e809041c005520030280c42c01001d00814803043d40e82c00040ca90071100e010b8800034000c0d814602840b0981c2424020202903d1005200c00e01e15070f54000c1e550001c0c0c11913404146160700800000c01c48070030a401074241c91b040300b000f440d03841e0f00d0320080059548501c0741c0042030160700080040454030111840300c40440d000c06507904003640b0300048074968a00d1400529070751030049000100400000a141030b15020354081074095215420001b00e4041260000c0045030204006141600b = true := by decide +kernel

theorem cover : BRFrame.Cov 518884892 519064748 := by
  have h0 := BRFrame.cov_init 518884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 518884892 ≤ n) (h2 : n < 519064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
