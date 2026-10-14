-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1870
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:58:30.486178+00:00
-- url     : https://prove2.me/submissions/accc37ea-f4d3-4de6-be59-57a76a46bcfc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 336151079 ≤ n < 336330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 336152329 1250 336151079 336151099
    0x605010e3d03050601090e0307020607060b030c0d050d1e090b0306060c06040f060e030304120509030106090216032d050c1005070e12010b010f11070915050a0909020a090506 76
    0x20101c2040c075000745010710010325096141800400a83d00c19010b010001d80050003118016103664040e42e00e803940c8408003181a08490300407900d040c14428409501410564100c000d020000c100241700c06050360f103403c01010840c80050982400300c841c440020500d04041042c030402a001e9604908020803640c6460b40038a80c1c61314000040d141500c0c0c150502540c0d10812100744203148006450102070340c02d528064a62004c803a0640c40204148540001c1c0601e29075400e6001d01d000d0300c50070360304640328440640346040a001000c000c0b00812101c1440c0d40d2001c0151065401400d04440034000c040a0300740121400d4000301e032448454403070b000c090104032585d40100c902c01c481d560b0301c081149001a0401038140c100c4240441c01e07074945120030001c0c0c0d85c003002070500c2d00100d0919800039040d01400d1403400110f940645041d62a006807a2103620704544080d00315002220f480c0071304c40d2140302c08011110030000003540b08501c10401c001c3d1902c2078102a0344140002c04002d0b807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 336153579 1250 336152329 336152431
    0x50a050c030a030e07060e030706030c1106150f010302040e070c0201020f01020304050a0209060f01020d030c09080601140102070e0c0403110402040305011409070918260d05040605010e 81
    0x99500a0700d030b41d4001c280c0300c0b080c0b500c0c1c45400b0000403000b0226458000071141014021030b807136144074041c801c200360300c49808a0f81305000d2714003000603480c2c2c0011070b4000d16020301c1c1c202c040c0410007000f80c407070302d05801074642c01d42c424003e640607640d14507003011780360b1541c0c5401d4a1100c034100c8100d05500a085009810400a00c0514480c60040001d05034844040c41004840c02006025a20543e206921303102c40741d03400039070b07410003840c14140000e40c2102104103442002295000507070340c9c410180003182d038002600e03182d02c107a03900380c0840b184a41c81d000c00c00c1ca0100c0c01c55110082d51014401000400d0f41295541610000608010b2030700381c0365220075080d00d10362801034410348030f004e06000054604000450040c85105010451038a010249002908443c5c03005041084080381c1c0000501d45182001086e00301d500d02c403070382c5080d10180c44d000f5140846003038503d1403801000041c000e810080c620b01c215030a0341234029068026400c100d5910070007003009200381c659500848 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 336154829 1250 336153579 336153583
    0x5092407060f05070c03020604030f0e060c011d03090d0b040f0c08060610020c010e06030a11070b2508060d0501060f0f0302120106031a07052b05070c080a050a050c 72
    0x8000c90040301c1c0880d00b50314410205040d11400780c1030508101d40303e04d280c00469404601280c115525203045604586034460840303007030b080701c1d82180c0c2c1f01000041c03442000c0300c1544903030300060034488001d01c0d0b0111103000780d031030340a80d8503000e412803e0803004100254411441690041c801c030b4840800814a40301c607002c65165801c000301304c2e40824140300e280c0ca0500401c00b11009540300403d403214095000810710220aa0004e009000100118803441d82c140c02654400343c40c07803445170700d804a60600c49104501550110010264880390042c280a40c45007203030005407548440b6955210241406544181d01c80c068800d550b07034000106080004600d4070300104081d26034201c8450940c01004034001c0303140200c2d01c0903071404004000141c3c04500003040b1042890000d0803659400300107443e01d214101a0094114042400708208056610008618881c04008112a96806400f034030a4a10800b0140c402d180501010495a2248006003c500840d141c064144040180180c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 336156079 1250 336154829 336154837
    0xf0803161a070f0e09101404141e100303140904021611120106140d0503040e01030605220f06020309070b0d050411060f04060302131e060e030c01050924 67
    0x1000181c01441000f01d0280e00008144448000320707445866030030209282c18007070655229040c10110f840350852200c0d81c031644002c2070740c405402890342c2441e0404820b420036050138003031170781255024081841000300580d90350982c1c0d81500d8903202c0d007000f40c50840b41e079045252800d901a4080101030001d12261502d141c084d0301c5040d0b0f13000000740783c2e02080207698040c0f298070344c243c1c03402ea410498180c0004021507091000e44210751404190704200f400c40c03055820924440011000004c100000c0b0780c4070038820304580f4501120751b082952444500c01946401030100b042552000c804600300b070f0300030b50300501c01c10f003201e10082d80c60404000540041071a0001d56560740108024070450b400a142600c80485400d49070801000c4140307283d0043d0300070601059400300701c1c13004280c40480c085010b46210500c0540c45060940c0c42c01e14031115000704800110052844800d6050019030121041c005844180c200b10003070341071103c2258580300b00b2090036000c2c1446010914010020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 336157329 1250 336156079 336156091
    0x1003021309030f030209090103020d170c030c01060f05210f010903050d0b0103050910050406110f0a02070906061b06060b0703080a060519060f0905060a12060f0803161a 74
    0xc41d210606080160660101041181c14103004220269203a61488070703960660750b04885841c0c0c40794050a2480c0840b1a0300c00240701018001802c58020070004054a03d10113104c009005168940d102542403915038032860350010740c1041c5101c04c00d241c401e410f00c0311854000445107803242003044103094030307a6000242d0124800085400e90044140103a42180e002800c0034000790803c0707a040c55607110b00c0480c81200030341e550080b80400050741c00054252501503480b076140c3c10000c500c041c082e4850f2400d080035228a140c00120b400050003910211807807603c4100701c615207001030030380344100b4241c01c644d0260b0b220404102c0b46002400b400d88180203689408451425081510480d0000c0e0801486106c460b0300d408502440301040105075103c07860500d07030020315800166200c01a81d00040d510440102d01c02c41032a070320855042d00e03044020818045655210b0903000c0c0d804a50007a45480e800030000d0b00c040c883c40740040020706206510504803142d0030100140880c109480c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 336158579 1250 336157329 336157331
    0x8160f150f23090108060306280902030106060e1305090c01030906090803010605030603061308070f050c0307081f05090c040c12141509060307050103051504152103050307030510030213 81
    0xf68200e95a01c0150258001c81c25001001a414003d10740049a0904002c3c00f800800c118031b9903112018a40000c03c01c0c41d03014000340a00342c1c480c440075203001060401e40340a02c201112410020015005850041c003061019044210480004402231305150005641040c2c884221200040c0380340019402000a80d455540300d0a02e28105401c0150140c4000b0f0449550300040d400b06811008840b80c09a0103410f41000308442d280c01070030903000140540e4180640d00300094504000f18154445103035010400040e80e0000050070704a0703030b042c2c0b8080c100354000c1786a1361940c02c00d0b50181c149410036050440c900620800390702c096411188148542100100501902c3d014a03410b01001d84011520110241750aa003c0380d610001842030604140e1100046a00b84a01000c0301c40c5001010b0424040c0c540c1500c1c44101c1c1e0304992140c081400c0c0208103800b84c10000c00c004805450f071582d51907255484403c0118040c0034043c0803901d04201d1881d00000503500c1a8a00b8480c10704010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 336159829 1250 336158579 336158587
    0x50c06010b032e05040209040b131d0a05070b1810020a02090f010e04060f02090312031509010b03181c02250f0306090f060608160f150f23 61
    0x145241034129800c402400e00c19400c038030003c0b400080054903084e40c00c02c0c1d030010b864066000000340a000103181064000304000c4d950320440e02030f0380114010b0b4151341e5074411401a00700b601c035070f903c100d190302401a401194080c031171903040d10014080801012924422404070380009495841d11b1603103100564170100e20702003142080544d540d400000017642c901c032513140014000e1345080040c40104240d640b0103120709545c0f2198140ca8855070060103c0b080b401c0403408282e0305610648401c181d01c1d0b0582c413105400e18201c6c2101c1d058428143e003480c10b64a03100408a540480050018034034055202017284030742c3e50041c100808a0294000d04000140d1102c4400008940ca298481080d81e618180004010400c40b802243e902001c0012039800740e08004c94403100840c0010030701410201d0000304200700092000b0480c0c2c403615035022880d901d00c6410440a070724400c50f89030801100d034030310350580101c1003004c6500140c2060101002052108203101601d2286902c0a840100d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 336161079 1250 336159829 336159841
    0x40e0a0302011406060d090f05070b04090501080d0c1202010902060a2703030912020a090f050702070e060913020d061d1e0307060b1203070c05010806060315010f050c06010b03 77
    0x10144004101030f0120300c2c40350b8282900850100e110307059491080076120302c801400c0020658160300a10f8002e03054401e80e54407801101c03c254401c1c4640014075062074000724800710040345101e5010942e40750036140842ca030751824140f21603040d44109556031490742c0c0b00542c841c0c0d00207002e005021342c0c076042801c0d070400f807109503480d02c002e048081f1107401109000094000d000b4406a40b059071750091568481e100141e515156500401d04003030a048192138852410303001280607103855000e848500e40c80301401c451007081142d8060380407990f00041003c2d6030b11003005000d1070340044c14180398481e55881300c105882c0321485030360303640401e520801040300e4140010f0750038a58200301440400c1048180980c0e038003992001405281e603450044403030755218500190803034641310136a600c4052030300740320941c20102d1181d02d01184c0c3c840002001e502d0b18004480c400c966891a84641d00c51800045039681c42682602e030a1007810048405402d400301f01407170007004401050307690791400e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 336162329 1250 336161079 336161081
    0x406081b04080c09130f0b09100e010b0907020a0b0112031e121803090311061605150a0509030a23040320010207030302100207060204030f05010c091703220302040e0a030201 76
    0x144080c04500000c040300001a451207a81c007002c64001c7c1c400d444984411407054244094204c404d06807138542801385a00d02c50642100d03c40e0307507040300e10002a94550f4016a181c58401070001d01c00d82024005000c0410040803050341c9034005e2a2044111003c482c00d0f44001420740c01e070f0f00104040c07000d06440c0180741d00800e401c0f0440e0155403065408140d8000c1c00040441c0002809400401c10006a03500d455080d03481181011140c50020007040c14040c0e22805001418101249007000260b810585401190700401c0ba2100961030464442e00c110b4030403000c00419500c20306c04001c50810801481d002d0b00c00f55025030784080c5c94040488006d81c1e010760b0902c0711410354102c0541040842d0700455009180e44115a01580e608603503e400c000378170442d000245a181140d45072010320405601c10350003c0d005848114891751030306d00288080418030640a600c0d4402c00c9114880c420000c401440c135040b00d9200e00c80c4d00d480b540001e0136034081c40032101c0c0742d5114000c01000c0c0760b42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 336163579 1250 336162329 336162331
    0x9060403060e0c0609150309010b0901060f0e010c110f0411030a06080c12070608090a05100209032109040b010c0f0b0417030907060c1406010e01050102011406060406081b04080c09 79
    0x440f100c0d031510501c1000308094046c04070011100c1d000110018a44c1c501c207410022452500400d2000950f03103429001c0e040030080544c00d400580481002c14440d401070803c05179954008014046880a4508004004452401c2c4036000798443ca03000c1d44680d4090040d5018468548000c0703200da042030051841c110300c03000e8541c41007600c206181c03011080801c8400a5070700303615002011f540c480503120b1403c4104c3c1802000e612407103241280158095004c2d1030040021000d949089017660703111083c40c410f03d182c001c261142003190f88402d01c1e0580c814003041c041030500f801049025100d98000050034001036408416890810003000001401c80803005041136006040d8100800c0e1150350318403070f004480611510b80c0789582485862510444030b00d02c0360741200c070300d0f684038108006180300c203128040c05503081c0300c2c680c0304070080702c001c0c9440f40901400303240c1011720700801142c2c4104060400000e440a00420801c0c41082070003c00c040c020007802403207d040110300703102413110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 336164829 1250 336163579 336163603
    0x20c0a051020090405040305041a180f090a0c0e031c0e01050408030a050702130e0a03300f06080316020f0d050c091008011524020d120209060403060e 66
    0xa99000e02c0710765429902c02e6511000050f00d0001c3c882ea541d180984080c441d5400041d110f00c04002503502100d070034001010818034542603110824181e000340041d040d4129081584543e43c5400240000303125401180916941d14152540980d03040c04a800d02e40f1500f240b41151902d100001c0120390400c45948201f102031070154501843c10910680b280204a0b0150421000145010540da14000d000658441d512010080015450900c0d652040805802c40c04034420a4400c5622282d900b2000500049501c2070404820700e00400310003401d40b40440c00c00a41e60307032004542a242003010303001d01e260407252110548250b0040180c20000444000d2140e0640c0f440b01c0006a0007203106100f044c0b00340c400841d20746601304040c01445542e0881401036280041414035001c84a042c00101d90002000402d0850000051b07142c903030f05101150050b034011140180002d2160f50303420300342654007000505081c212000900654040da20640e000f40e21841124840c42d400d101410340e100c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 336166079 1250 336164829 336164861
    0x90b06060307140903030403140609011b0f1803051608060a0b0105180f0402031e15030c0108040807060204090c17070e130e030307030221010506040b030406020c0a0510 74
    0x460700d200010101440103020b001422004a03021840e40c80c1001a47d015640c020402144020395180541d9158004c80e010105582805800034960411900031340490200741e4035a0f4008107020701c140d95002408000d4030358081f9101c0c0c00404604180310042c82032041741d0903c00312600c4c00e84058034045001c2c2a0f0480c43c1e16141198070382d0303a000812100400e0312941c80d40c051542120010725071201b0801482e41050000003003140700f0345145407018500510341c01d4201c02d44c486249200c40c2c154252291a003560201599861960042c142d140e80b051040700c10740c0c0b034440242e80f040700380e801a41c007402540352a19186603205420404100703c01d004641c1000705440c090900a000c80201c041990259003440072000c42991190007021543c1e08150841e69241020030001f4001d50140d402c604200a80101d081409000d4414050481e44014140303400c09041030f8080c0315640c0050403c03600e444c3d0800001004803414080742c2d42241c040e0b000ba0003081041c84640b4160307043c01111008035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 336167329 1250 336166079 336166081
    0x50607021c053703080a02133503070b060607061b11013b06090312010b0715020d0b0d031205011a0d09020105090a180c0804030203091207050a0306090b060603 70
    0x21200d00381218440c4d014a40800c4944a036030100c8003c2c0f0601200d035060700a02e140c0860300c0c10203114105c0350101c804100b19882004041006481da842e0305800e10701c1e030410081c540100760205481500941d000b41498541101991264100d409032180203483c80742441d103840419402584886802c84000c000b4401d1607003842800189030182d02507a209009200b040c0590744a45a101c2d042000e40c52040311050704090100b15980d80048008511520b204400072840f09124403d684003d80d00079800100d81c0054410304000c2d401054000d180c0543c0c584081000c2c1e6114a03494550501035156649400c2c00c40d680744090390380582120344140c0c0b0000d600c000701990b80d800c41d0500b411400f40091481d00b85c0c40100c90300c0c0f0400002580c0b202d10324030040386010380c6500c1454168151402042245e20b5042c0c16500b4801c100e60203009070308203000c65516030034461a03514007602014141c2d021240c88100040c4407000c1c40c6c00948200d0354032160103081040ca0a40280c00c41000c0301c0c41421 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 336168579 1250 336167329 336167413
    0x9051603052203051306030515030a0512071106041512050106020d050d0f020c1c030c08010303051303141006080105060a05120705130b040c0309020a050607021c05 72
    0x7008064007844000342c5400801002418410300c10f60b841021886000002e19546000080280106442481c0c0c82007240b074042c10140303800130740413032485e80c40f6002d01010b5442f0344000d0741e0358100010680d960300904001e041255a13900042014200c003c50094040c00904401440743e402c0722040000c0d180f0380b1006000d10b64001039a800d00b0320749803400326a110121100000644000607010607c94008640050814030210303c01c41c1040c0c88500c000114002c07030701c00710b05031f49080308010003083c035400060001c644641d008210810b02100980d200b141d4a82d5003017400300d075040300700f451034124071984144007019000c2c100082c985a0001d0100d810702c04000382420b94684281845400400d5040850701001e000c00001003000504050419180601d000050f10201d04200c3c4120b142c4a0300b03100d85400f03407285c0542c254002d48023203880d034100310a02034281d1008405907884440305030400e4500c215050355400c010305c0391002c0c140c40e0340002889040c00240d000e16420f201c01588090700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 336169829 1250 336168579 336168601
    0x70312052d071509110f0f120a14060717130c06081b0903031813050114010932010c02090414010b06180d140a1b09021608130f0905160305 61
    0x804110444008955100200028030301f20703565082c290f008180c0791521609880040356a15000c0c1c000c0d4003c05103444040c51050700c508e01110070f80c01080d81003003031000c0c1010000e1040e900041c280c1414543e041d994851461440300383c0c0c0310314001a0444204152040148140d8192000304288241040c212a0002ea124015020080d42c0c00035200101c40742c541e43c4d04800c83c1c083c44013900c100429612440a510704588240d11540801c440401c00242c0d142e48041881103002840303422484600040d10340c00801d027010420314104103142054001690b01c4010313450195104d054001d54000c0c580384034500303480070302c0c03020361160b1810301c801138a240c040341e007d5003010000c44915961103d036240c0881900152143c08100d4850400e12008001408540b46401080d01003009222a615614802a4400d2801c0712841030035004442c40020680300107071562a55202c015980140c83e1400c0c075011180d0340d400144c21a031500c00380701003114213120341ca030040d04900c0c040c44180f2340b0b030001c51 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 336171079 1250 336169829 336169853
    0x804050d02040902060d020d0c050324060f0c0606040c0503090a080f131503060f0f050105130504180b01060e090c03040510020a05040e010503070312052d071509 71
    0x28010305111000a046546079448088650360040006407036103940303506d0100a400015030009014035081d81000764601442c15280b107010154044081c040c11502c5100c0c41d1040140400e4000100f40031402c001a060b4010f80801d1a0203402052240b070030104000980b0b104c10010030610008105010000c800400c04112440c2c01c00342642d5651400d4410000707910802c0001e00c1c40e007480050107d50041d450b00c00c6210b4448541e418080240c4940034541400c1282c03042000c1d501007000d08200d294001c0d0007801119070758100c01e501043c0e40d01c022400742c810703c44000ba0011000360b5003000300310812680c18090851480c0c00511543c080b00070440696001e080100642400320000e001c0001c10841040404502902552994400d2101034070725009800391190f5001d0106c0042081d040015020003266003042c018101d410344130380240c410368412441e40381c2e03035609200b00861030541152207440441004190075a91503c50420702c0000001c1d60080140b241010043c40101d1510b44200d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 336172329 1250 336171079 336171089
    0x60106030c08180616121404031101050f060d02060c06010f050307150203030105150c0d051903091208060d140304030b01090e101814060a0b0d0c0306110d05090601050f010c0804 78
    0x46040c45103a44170a07141c1013480244c4420190401c0e600c1150784c01508a058020391080c2c50f01c0c40340e600b100321058241c40c3d0031181c00c1e48449035000096414075280e01302084085c0090101894114801c0a00341801d809811600e0011950301d0b0400c5181010046400104031090300080c2c00ca0324004025140c1c4418410903101e045180e241a004869000c115403848449034210385001c98150005410360b000091039a0051400d100702d41e10941c00780c094a042c84d80c3c082072000588d8004413054420074400340c41aa04034861203054000540e4410940d003011002600a58550b071441c6800280b408058106920040c100403a0728040c3c1000100029007084500c1c1c00304e40103e9480702c3d4003181e074041070003030309241c80d030f16207842c000c58041005401100244014081c0e0760400c0305000024241e40b000800900980302e0410100b81e0369800280c9800482c68028540a085d860180a03204241c65810058010100421081c58800e1284003c000b085c2490079007240c903903c403011140250712070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 336173579 1250 336172329 336172351
    0x3110f0d030e210f160501110303010515070b071d4c050c06070c08040e060402160302030912060c0708030a0617100c031b0c14060106030c081806 64
    0x104940200302d03405155900343d041401c441c080300d03900c0c9960343d41e03000200d00200301802d00c080110301075208000109825140e04015459a403a250510041d4a440046408803080900c55000061041407074180124581c0d590170003030100c0820052080050780100c2c0d44039400307509072201d1102c10880c0c0d070000796441001c5164a0600d0541a07091045020007242c04d800407400e2905002e904031001d490014240b5040b2103541e540c00c6d0043d42e0105490801800318501800100b00c00c102041c6140d90141002c1c0025061130341440110000d005481002c0300541c02c0842c43c00c4503410101c0321140d100286000812660030315030080030940c8255503010700101c20003c009074a84d007694120200909842c84140d49105180f001c0c0d90700d560490380e46581072030401c0c0304a160180700c1d000380c0403090b4042c0072013903614400c81303c1610a03028090717084a50488001250a010109015075070081020380c402082e101c9225200a00440c00108520a1100c0d40b005540d02c3c000001035042d03101e961100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 336174829 1250 336173579 336173599
    0x103020901180e061612181401020910030b0906030106051f03110c0721020102120a03150306050603010c020a0f0b0c041701060504060b1602060912060103110f0d030e 73
    0x41e0b50300240070040c00064091180c80140185049200055804070165a44511040006a02d030a00b5a0b694081e17a52080400c41201400f09042c4280c980440d2614070006184c909000d0104411241a6110901190703591140e01c1850410550a0707034000000c038001c001c51408c00000071890307203020000c669a010043c40318000035000b07034080c5200300c03a8405031681729038524480075500d01e00c074000c0341c0c41e51408034588850440c20203008411598140c002d41500701d03200110040d1a0042c4a41204154072501030588401c015003070345001d0350007008041941c1c41c11006041c29030b82000003841c00c65002c013284070089410704404043c440c0c2e112814045c0390b1035003880860706000c1c1c3e42003078141d0744030000380b0040ca00e415400700084500a8030144912a03560201380014003d900e2a11a0510005494801858480018202c1d1707a00100034090076060503000b545801d400360021a001500002080d602d0300d0f00d41c1c508440744c1000ca400700c0240c99a990014000b11601c4681402155500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 336176079 1250 336174829 336174869
    0x3040f060f020c07180c0f080105090406110304030c060c020a08030123031902010f090b19050d06080f060c0301050d0b090c06030906061206101202030705091006090902030103020901 80
    0x42c0403100a03c08074011185101c2e20b4620181800d001000d44204082c508440c442000340150a00022401240c80e00480750b80381500340526544028011541641da80d4a0f520f645608000598000e5019540300030510b42d076494088202c030a248140c0d81558002a182c00005221074200c0c1d064400c0c210340c907400c01c6613001803d6010341100601c0741d4035010703200302240d103204607441e030066840c000d0b81d4a0007403810307501007900e00054500500e1200c40d010440c4242d24418403801042840d004d145c828070381141c2d1401c1b1401c40c0c005405c01c00058000104100621000300142038101c42d074010b40c43d156501d44000103d40f10b070000d40050249a488000510200090000d641702e03042c05089590349140c102d0010ba2107020403117150340300c0c0980b00401164400c0000341d20b03110b10340c5004021900707810f0451070f1411200c8290300b2a030500c101c40004c28a41c880d0701445000f41020f1410016050610401074007100b002e8105480303a42c41400100050703912103078900d0445250030b03902042c03c0c56803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 336177329 1250 336176079 336176081
    0xa05070519030911100c1b0e0403050711060c15010902161410090b0108010f0b010818070b04090501050a080109020f13090507140f09091b030f070f030c0b03040f060f 73
    0x4940d03013580140e90035069194941c02c02d0303c000c40346e48035501e80e6140e004e900e200b0202c0009a4014029003204000011380081d00400051034164086c00c0862011803e00c0300241c201c4c2c1c4101d2210425030881105400f15030b03c000d2626014244010041d42440400100e203100124072031400390904400c0d000d00c0003482010302403151610460342c41031150302007070704040c8040c0c0421702c0394107490762821580c0101030103035108000c815901651005180d0300c0301a2880301c0d2024459901c1000d0050380400030307010050354002e10081c94803020202d440d41c500401c10410350090391000d5116410131480d400160368001070f15842e000100c80300601e10b84020080c8004001c5500024064850103030041218081c5404e01100382074100c5901d41ca428024003072000e0120b00b134a0050950b0311510001c4101c48071140040840708015044600345102900143c1c03414000f90b02c0850300300005c00c014828042113030000f2026008010601e0300d10f05203039550111894013400c0140240d80d0303482c00d0a0f07005200e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 336178579 1250 336177329 336177353
    0x2070302151b061f1409010911090301050a060302010e030609060c16060e0708012003010311030a080703091d0c09150409020a031409060601020a060b030106120b0a050705190309 78
    0x2800045a000d45425860130407041803400740e0b2070290141a00004440c415400010304400018103504001d918002c10b800192104242c5010454070500c80c0300e00d00e440920410307208030403c00c0c000c5062851070002400c00000449494020f811020400c40550760009140c0d4001170305c5100f0030f5450003001080032103100c5204c4002d100b18100344800c200c00341c0000d618000e690b0160000c0250441c51f84052901d4000c60b409030348000030a00040004c1030480c6245180800c002d010743c0d902041e181d440000d035900041046002c102d074401c041c0300d1440248200905018010890151400c1241c1d80d80f541c0d0003a000f1051056019440400c40d0540910980c2c00401c4126401c1d52107007c3e1120207000340000a022030340c2c1244601c00900401030015456000d500c0c1a00602034488a0341c0311000034154005c01b00f42c040d0748820000038814000c250070341041d80144440c00c240e0614081c05800d444000d040c0d50b0400c4002e02141510110a00000240150034180015402c43c1d5180c46250925 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 336179829 1250 336178579 336178627
    0x705070c03081c05070302030108120d02040f03080c011b050301270e0c0f0303160209040c0e0703091e03080126030310060f03091a060f090103051c0207030215 70
    0x20100e40d4210702e0241c40b02c18450303e14000c2c41440a5030754076008034100c8c0424414003009903c281500840401c845c0c0060050f08100c280c0940341c240c940014982000303d07584211241c600000306110030007020712030462145c3c04140c04a1606806400003041b9000c18020110b002c90030349540b00e68801050207480005005200034400f80300c840441342c1e00e40c400220720a0095612119103a039a240100466918622103044500c50304550303028000844001041140c04103903000011804d0142c0b150305030b104400507a070101d9015068900100903100b4001c14a210ba11404d0000b40000c2c8c00000841c1528003d40850741c4009680c0556030440005403510107450100005101038400f80c00d03414810b5601a45603901c1c52841e10004038200c400d40d240182c600103a240252030915002e8a4081e00450b005103041c40c00c1c05090000368502c0c00c2070f0300c1101c0c0c5610100102c01214002d49030701c810424103002401d46686103401003501c03240303041420302e101c000c00501c0c1c2d034cd0384400743d40c03000c1040c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 336181079 1250 336179829 336179843
    0x3060103180503030703141605091c120e270a090602270102060114060703050405031f05060406030521130311130c0e190b13030210080403080705070c03 67
    0x403036070b030421640307a0340203440c2880024145001e42804c94402c21601d800740c41c40d640b05144584101c801165a0342204000c56440f04001c07035407280c100401c072180000b0700d006030000c5800c840b412002404075183c600009004030b21542c201d201441c4258002c400c030f0090008090750030b90340c00900c440288000300000f070100d44081801c0352509083c01c80342130507041250300500d410b800c1600581e41c40e0400d10400d2000000b0710070641d59400c00300040d041d01ca00c6410010304054403240003908205000e000c0041c1482c001e0f54440c0207080c130340541a00540190340411800f411a00c2e101c0d10740310094880e800c450300c030a00f0300035100d5072481128550034400000c00c0c00e454680c40c00d80b18082000d08800c0c03080e058000b071842c040c64984243d801c50900ca0300c80e0a041d1400783d00703202c1f1617180894600c1400310000070000317100030a03c1c010501c100c0b0106a40043c1030451041041c0382114918001c2005070301c00800001980240b801d039000300032410015190f28040c0b501d00590401500000c040e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 336182329 1250 336181079 336181121
    0x604060911031806040b0a0902030c120312011505090d110607080c0c0f0a061206080106080120030603071e03050304031518051c030e0a0c08070902090a03020603060103 74
    0x70034030700d01460084480501d6000c660080030402c0f982c40d081030310007420005a0001080c00d100040e4030030080284098107840c01c00c0705402c0019603100b000d081c400656000000c41ca02d030b030201110941d024080b0620605000c030748011004041e0b0040d0f604550241e21b80950320310030301010300f41c8002450001001156a2070321803410000c25048014000c01c540700b60852040549070858080b45400400303080b8007042031500c0c0c0211098000f14038002003182d681e8401280d001401c1c001c0c40d02600000e000031620a054048220050f004031659441080d0240180030240d940464080101c070003400e00a0b4602c0d80842c5c2c001c0c0e070010707e03600c0102923200000340001081404204011501c0c3c2a002c01c0008601d1214882864845050010040c0d00645661031070041e220b006203040b51110324001404a950054061510b40c03820801d070764815452104008480c001c004801c040c2140c1d00c0198200798404010901030307030342030100078810303000400040c03034607440395100940131681d0600798075030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 336183579 1250 336182329 336182351
    0xf0304080106080709110a12090606080105090c060f040501080705040e0916090506010c02120f1906060b131202011214040606050604240903050a03080f06010806030d0806040609 78
    0x82c4660f200c0c0c00ea0b9401000b00000d00c3c1c050500c1003081d100704010034580b41030700300c400440d4030307001c844001a4039603564907182020680c20720440d806051000000280390611410300c914004640581500c11007003005100c0740092040c041e14100c803c02c3c02c000310103454007403041c1c2e0b25010f540c100c94085540e250400c40c1c581d10020b221a405142d43d0620102c658403140740740280c40c0111140d901160801c9030341001801c0910401c07001d0388807d4241c039403442511202904050560f891031029104550034841405418072500001f0907505201c0c0d032410701701c1c1c2d001051301d40003441400900f0301a142000309590162500803d4140e200100304500c200e41196016580020b88040c2c8480f03103015400300301c2d8203244080310159034a1003d0f030040c2c022180c151142c00e0600c04050820040c64140c0000090360821462485911a481d87c12803071410303aa0100010704020310341c5040020700802d1041c20745021400181507000341c039000c4043c0e640e100c0800c0191000740e0000000514104000310 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 336184829 1250 336183579 336183581
    0x80c030708090a090b1c0309050316091113060e0d0605180c090105010c170d060605030f06100c080c0c09070908010f02090a3327081c020f03040801 65
    0xc02c5000c2141c4814103580c88000d0041129051807500390000c074000c815003104030f80740c1910031810b4464540f00c0309145d11940841c1c00c0601c000c00546140c24160400d0251000c01e000d0003607490240f0b1b004900300502c1f4042000c3d80c00c841d215070000e01110b4460390003507032160b8038440300320360300b01c107050080741005002c403102c018103610a0401c900580d6544d402c1407401d0b0078038a04943e4140c2d03a5038110185500c50442d00031380141004803080f400c010000f1026030b0350047c8001010315880341600c03483e105010140036240104850b10440d03d042c580c24030709811002c50140180c00c211704a4481030002c4041c6d01e0b0074005c03102c1660012440041020300c55001107010144c800c14402070024010150191043c0c0c00707a1071840e5802503050f0010701038080c00e450895801c9a0701c0310b0ba4403e409020448111065072188254001594a4075440d111f80d0501c40468814108034414282c170b510707207038401d611089031040e4a42400a2214020043c40c8200000092208084140c0341d0369941c03217040300c1c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 336186079 1250 336184829 336184837
    0x2040e0601080906090d1d041103190e030d0b03010f1e0c02010e0604350304120c150506011808030403110102070609030308040f1e110415050d080c030708 68
    0x900142c24040001d01c41c1002040139030083c490b441c014110010109400d0340c00c03070107089082c60050301e04140d0440594585c01810012140c03003624695905141201c2c0402d0803000151840031420040780ca0b1a2010000880f1070407120040c0008018000000017800340c119902003110190030400c0c0a030134595010100000198400710400101c1c1c0c00c02001c0e8240d5200b2456a91f561300325000082c0404c0300390341c0b81ea5030b090111002d101009c000c041201250381d0240300000e00d0b10808401c0008124996543c2c20303400e00d0a0500e0018441c00c0d40d1a035410b25944440350001903114804070741107034000c2000c0d00800c03980c3e0541043c51500c1c1c0310115600d0b009803009035030a081e0701c0c1030000039500201d040001d8030a950754542045080d610141d5603440050811240070000010a5000c13454004a4402c204003d80354610080114180200321400c602c1c0c665204501c4c20742548201074006148000b16502a500c0c80710710146424490060f0180d101d0059090000046d12404c005600c2c0042c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 336187329 1250 336186079 336186091
    0x8120f19030e160e04080c0114100501021509060703090206040506041d010501080103020d0b0405030d09050c01030e010b2b02060703050c06070203040f090b040908190207050d0b060d051002040e 85
    0x4480556841d109a118840e05210b8803004d2448000450003161100c001051185500000032800d004041400131031001c1c00c803091943e48000c56424440d569040c0641603403410200650b400604002c140700d0344812001d13150314145550348048008548540382550020140104400c0d2200d0340c1d2803c00e81c0c00d0840044100f0309481c0d4000102e0719600400703555040e65000f401e190710200c1180d42d001c000311000703070060760288400d21500c80907889078080c1d440b06500c1400682124206803001400382c5408040105017039043c1000c006403515041542c0b02040a9040e0545100074807600c840c0c2c41c8441100040d420050001d141d0f024184c0090084c4100d0403c5800c40e5011340d1707100b41c22a02c9000358003074403115100d064010800b99a00d5000f00303150b40c90042001842c510941d54100322a400b4944410079030fa02a0202d40a081e0140f150704004c010540d50120b0208856503000c0c400140103006a00ca201c4200346401489010810000600700d9000d0840d44c81c0d84801c1050b81c881001c41e15 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 336188579 1250 336187329 336187333
    0x1c090512030a0212070609061109030f06190b0a1a0c0f03070302100b010e0307030302010c0e0603150d0c0909051027030818070b0301050f0a08120f19030e 68
    0x40d800062100108075030208000e0b9016011902c2000c0b6411495804180d090f520552a144c421010035624403132642122900e040160344c600b00e5000f03150a01400c45541d00b000d4005104015003656058207100061201c0c0700001aa51000030001e099604c40c0d8001401e5045004d204407507501482004108800f00a003c031440f800311050800d95038426080000e0068000f40301003141e0400c181c000c16900e0405051100884c1d0340600803910388070190340240d0040c0c0d111914400110b812843c2c400e0b070a0002c0d40c615143d40782c03000c06881102014143e45004a42030010314091004002c0c0810141c00004014461100d0505141c1d41d2810410141c41031079180c2034807404180c0200d040c428442200c2486601e540000d0384058a02000041107080300d441c1c401c20500c0e00303070010301108000d0070522084903200d504140034400404640b000380c2e4000c440b100c10500c080940081c00903410442540c00c0d59441c038070445802c50a00814010407115040342c1426138903160141c1140d0b441e4028201 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 336189829 1250 336188579 336188599
    0xd06050901060f08130b0403080601030c0f1704081309090c0e071b050f10050426030406050907091802040b04020f0702060f16050703050f0304061b051c0905 69
    0x400c0064104007881032801062001c010412414021000740d80d00640c1d941d60b003c075100700b6840f9030761100030071201180050905c80030440290780510582c0300b9052a0b20780074043c4410440040c02d0702e14042d070020090707400000082c040100090484542d0043c41000c2c0000540d50099000a410805000c84190710b204c040802c01000000b08984140d107a60360301500c041340150804826103446005440b60b0044200011390014100040c41222501c2c00c40040c15107014102456410402d42d11026440710903a2102400b021000c1680d41007130f040600011240c450a8846160a40b190300c203e81d06400c101d003070090700d48001740400c6e040d07000b52010300c180080030003000202d100e41c6800c0850000117000050250810002602c0043e8020340020301c0e241041da00401251001340040750143d10800702171041110901448031042810b178000c500b440e04002c0090828000044a61800008450f03d40c042c0402001030b4054218401c0c201b02100800301e900605004160182d1405589020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 336191079 1250 336189829 336189839
    0x1a060310150f0f02031614100203010b0d050a0b010807080702190b010608090a0203031b1f0204051806030a03030905031207020c010207170a0308041a0c030406050903030f010e0a021e0d06 82
    0x4004c4a01c1070001d55803840300c01c070681d0345040700c242903c01c3c407c0052250070b41c241200c4189100660203400c4504030305d900ca4154012282c04da1320010302103064141808a070452036600320903056040030301410240350380e65649108a1400d210700c0c030700c80071909100340d6440610410b00300c158103845059540d13070110b44e00c024070780f60350707c3e120500250950300802511401c00e40000c650b0040c00004000d50301ca000b20a1004240c690942c501942143e600040400c0b007846c040000c90380ca000c0054a400b117038600030b00002c0c0c59440c0c80720040c00381910f810f4800200308052045450034082070308240d41c18209140700942c4c0c2e400c0ba040b030601503c11018080f507061907021a2881e032200700401414003090943e030407611014081c06c100c030b018200711802030a003801c01f2a201d2059a0700c011042c0c803482e06052440a0b2800030300350007030b00e170020414400301212406005044d180e50600340c207015200d000b4044020702c0742c003092403605c1c6c00d011090380380b845004008203803982079240103202c05501d036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 336192329 1250 336191079 336191083
    0x402030f012c010b01120509070824010e04080f0a1116030b01060507170f040b0703030c0212030f040b04050c0406080609061609170109020d0320011a060310150f0f02 73
    0x244c10602d001c1800005002d11410b49900300540c4100c1c0e1909584031240d40340d070540d00c0c1080800a40000502a200082104c0c1da0400300034010480840520f005040540b0b8034110345c0b01d030750124074044000240b0483d4040c01982408000c54109080f10340080d081e41c4203546902d12400201c414039003050000a6583c819001c0d95611a000440300c0600c01240f49040c0d10f40c0c0c03110804c030418801c1400002240e00c076140107040c0070786c06510b0100e840d6409050003800c1040000f00d600100c9401d1041c401204901001c0c0765101e81d0000042c146502d0340e00300240f4041c11080800d40c030130705045001c1920311001c589180200ca00c0d1044840759240e1815100b94940c9080700b000c00502218420080c80079450740340c4000a1100c0300000381400076401250720070991000c254003042d0301c0b01c0078091151080543c9080d030244400204039800049284070442000c01007018400e400c04030121b43d00d80d0070b18020308001d103c14801c2c0b26590458030006081100d01e40318480c0070070001100e0215203400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 336193579 1250 336192329 336192341
    0xb06060405011d150a02060108190c090510030b10030201091505031f03060510060807031b0e0112020a2003130312020a050d080901060b090306010308030402030f012c01 74
    0x141c4800c02d240d680c011152180c00c81c841091a48407204908900701d01104e14001c2010101c0c90b80030f4079031581000c022030f24240c20f00050304401c032600041c9801141c91082d580096036403180c80412282c4910054030350000280c1c001805402183c1e09001014145140d81c6086030f20030f0302c400d5600740d0b680d811010303030b482c20041c00b801040c070800002da45620781440b0198409120b14000080b1038490311000111a0100c030492484589008103100b403d400c55021a03205040340340500642c00c071866421004001c0c2c43d4880203015a103002100168010701040000c00104c200440d1100d0a045000307052198a001a98030402051a041540301e40407048841010300380c1c1107050180d16641e9041c0d40b05a08488040c114019400034800198041c046120800ca5139a907017401410000d0904d421103000d0f500c010418030003089201c20f192001704400b81180d030420012601e035a09c90000c281000314456106145511b0302034000c5108481700e98942c200380c880c200f040020421010140d00300c400c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 336194829 1250 336193579 336193589
    0x15040602010f140406270809120303040c091109120102070b0705040e040b06040221060102060106030e060f31060f05040503090f0a0f030b0609090105060d081318090b060604 76
    0x801003000070302180c0c00e40c000c001c0810f041720b01030101c070032510079004080395602801c5848200000e244d00707640c278142e10541c0c00000d65402540c51410103640e1141455900d00c1400e44240d101d01d6240660441c40082d40c5148030040e0100b5115540541c40034000c1d400403e0481e0301201c0d94004c00c00c0c845c0b1500540b0180c40044e0f500084588444d110034509000041080c3c2e8055001c00c41128440713900820300090300d04200c0b03500340781e00b801c200180c01c0c03440503003008080600e8154852809800041c855400034200041d59031140c40d103000404480500b0103010001d20049210000c8541250070f690b4081400380303070300308003403c2c8a4441c2e10580c1d1060b03502401c0c580c018882004280780c02100c1036403030b96004104000d81a564902100d112100b03610584412442808008940c1862845030307500448440080205240c404000b4400d87c800032005810b05502088440e243d04054000300081c2514251ba03008401c1c0c00c00940018118030764003143e4141e20400481d08a040020507503058030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 336196079 1250 336194829 336194861
    0x100e100e030f1305060d15240c0809120d12090305030106030b012a020333072607030c0c0c05040f021204050c120c01090512010b15040602010f 63
    0x8a500e42e403484035030308242c0400c840249500b00001c3c166032040c00400c0c8035840040e021070040c40300d898290800c1010b0b0700048040b41c81d0048445507404005941c5041541818594002c052504107212107008600c1460b80080301702c104078086c8a0300050545400c1c21599a14109840a4444c3d030240d0700340102c0240401c0d0140014440079000350442090001d040c54074102c0391000303900741c09200c003140006144800c20002c4440950030107021003d4403000c10384820791900d0000c0b140d805000c0311841c46244101c09007010800701d5100d5000e1218000c840960700866090000600c0c0142405030341e200b004c41d00d81544d100304039015000d540e000541041f0b80c45812450031050001500804606a140c107908000031200502c4000041d03000310301803001001c10b11050400d2241b041000b40c4502c4040c0d01080700e0504503079020180704191501515003481c1e0401c110b1035a0f014140d0103a515030700001044810102100d00303406042114141d500078840c02c84911465411245d00f0060341181c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 336197329 1250 336196079 336196087
    0x1305060411010c0c09151406040506280906090e040b0711010222050108090a05030313021201090b07081e2703040b07050c0609030a0b04050708100e100e03 68
    0x4900300701c00d0301d240c04106041948485402d0b030b4544500c1949a08185802c41e5144601c4100c218a5050800901002400c0c4070302e0380800c4000980070300462007418480d100c002041c5151204040c03650390800381c000c6507035901540051028204d864540901c0e0001140340000003001d800c0800e03039078042e541080e0900c0f0130703031228081190200b03980d0a400309259020000e2000040780b546042c01800c0b1040e24a00d040360924000610101010302104000e510050f0341d94007080c00403084941254000900301c090303510b00d1000c02c000300010074100c1c060394a044448028040d41e866110302c20380e000d80e6500d046580d4205541c08214891401c8803d07403c0020001e207200c1783e604c00303e80404026004c0e0468440c00e551455140d90b100d500300e4183e607040410b007001045410010b0b21182c40084504a0070b003030107400801d83c0c1d083e445001408008014011400380641804108040e14000003070302c041c402d0b0348a04001809000c8403204091140c2c40403010888c03000d20412400b4500700b0003840c64 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 336198579 1250 336197329 336197333
    0x1207140f0703140c0706020102090f041e180606090c020105070807140708071b08010e121213120309020307080f0c060307050f180306060a050609060703030608010504081213050604 79
    0x41040c010701038803900c41c0411180c0b1220200b0045170300180416400942d6440c164002d108080f4109040c280c061814040c6081a29134101d00700b45880400c40d100183d8450607403609a12142080c101400d4180b403c24041902d07100c540096150040c150024441c03034507140f104507001d0b0300c115404000920b401c4e0b05803502d81072140050440b00c2c003403029181040e90580390442c0c01114405d4040e0340d00030340e540400a2480038052001e443c00c00c0c1b009000c60400c0c540307800340280709518903144200a02000030303100c03000304018044500d40191180c007207400c081c2c0020700280b5056405031722034480e109000895890000f5071110300c107100c001501c031400c15001805a107401c0500040b05002090008000c2101c0b1138000d843c0f5400d58007160b0311105800e900b81420b10201402d0f1a000f1103100a040c40b05032200c0702140d100300400c0d03801550758440d50508070004c05080d00b01700c83e55401c0900740024090600050038402c0d4595006810940750074201080540c90200000c10715003281d030000b00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 336199829 1250 336198579 336198587
    0x240225050d080705100b090c190c14060103050d0e040605131805060712060b0909010611010207050a0b0108070807081203061c060f0606050408070312020a02061207140f0703 76
    0x207440c82a403449081400360340c0ea141c14481c8481a24909560b1440200e509192865440d504096a5a0805c2c607001054100c1c014408a441618050005c180040402c100c6d001c062004010b1099042d114296101e24065845400c600040000149041240c0407913160034822501226002440d40005130544032801c6c015000c84620100840c842d103081c08007090701800440c0c07240702140e680454074040545498101e601c2d0707130040712281c02c0a018018031034403054450b90544d402800d00c0154441a5040107005e48150240240313140a107842a03420440064042d0381030b0b031228015986542c0e01c0c0d01001d9541e090500c50b2081035072000e0a4100c0292010005640002d8044c0038422245404035030158148054075044407074903600c603441c00140f8458400c2c50081c084a00d000b0349001c0c038201059940e21010f000103441c1082200313024002e64000c0004c12100390b4013418540d120159281608100350007260901c000c1000f10580140b100b1030f83c82100c3d07201606c1003105090104a0310211 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 336201079 1250 336199829 336199849
    0x207051011121501030b0303121b0a0c031809020a120e0303040b040611040504110d0b09070e0120061609060504030308160e03030310050f1002030f0c0724022505 71
    0x5052660707070700b4000d46e2030b14140010034044544440c41000d5080c05000b10089408070f54014881c000d00303000b104c501c0c941c48090075487d136400d482d050700c4182c07181407200400328082d8084030885100040300d55109802c4168508440d441c2c81c420040c4079007031041107403288022900240584c0319100000d002826a50000744068101c2060509041c0c030f0704089011a140754001d080140d42c00b15208102800d80d0058441d001d40030b132042d01c4e26060814010706001c40d1f003010303d1b060000e4040c0780701000c41e11034100e401044044003103440e81d06104a482c2c0c041e0400000450000d183e0440c04240303075010b4001c0303030112a85503840b520a80c2d0341d11100244165296801002c000c0040c50000540e0303010406140200709507401c1c0c08280c0c0c5441c04105c280301880c01e103103000c1e0205032010b505694020003036940008521450030350724254603141508044550b045552284014542050392580d604052614140c05800f22880502d190001204040c141c451103641d09c920031906226030306000c000c40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 336202329 1250 336201079 336201121
    0x6060904150c080a1b050d0b01022103040b0c0a051602130510080d0309020d0204200313030f021f0c02030f03041b1a0711011101020705101112 63
    0x807036061a039480c0c1e0009903048003501e0400502000d042c450b841c0034500c101071024000c040f034140340060180014003540200300195240ca03945168510310b030390023400344c0e4190038080e075160404981c00d016000b5048d041560161030306003c01c3c000841e01030000c0e013110300810141d2245400d0039007540a000d4082c00100c03080b40c00c18003801203032103086030301d00809000d80da080b022200540e0401c0500d46c5003c0c0908101030406041c01000310150300e942045609558043e5004a0503c40340442056043c4100c1d0700c0300852500002040302c100e21034400c10310110303c00d940303228018444440480c1d58a64000c564124030f5017948550f80005001d60042c608444a4015a802c203a868589810310341c00032202519488a82d000301c0b2440d52881c2c6503240030301102d0052a8540083e0101c9258a01039000002c0c4080040c624052003a030290202408065542000f5992890285010354545a8000b11034001e41c1c142011025039182070400e03035410001d025010302c1d43d90748030801810349041c0002c2c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 336203579 1250 336202329 336202343
    0x1d010306080105100602010b030a020901050d08090306041a0f01031a0a0b1c0203120f03190204120f0b06120a030e0f1005070c0e010f050402280c0b011706060904 71
    0x700c5210a00910b803250b100396070124a0329151480103400c1d20940040d480c0f094115006100050f40c440c84424107480c015102c1c0307803000c4014a400c2c100e40c0304419071154113100b1507003040204040b1131044c6824040f030201103080f40d211581c1c1051545421b00000f0f003170001210003203042c00303000c0d2025648094000e0010910044100100d01c800c41d01c0581e020103546050100c10a42c10108900114505142146840c1001081c074544d4580805041041c0c2c000700d982449a102c4415010365018180442c108900302c1e119144c19001c0f001200e40c210b810521100c0041d4080c500f4010070742d10342d0101d5010341030501581d68101c48448624900b65480400e21125022945940d20820342d2180e0b00c0c5c8800f56500118103180500020301c1d4444605030a0800c01841202040fa00e403400300c07801270300c0241c0c0358040300301c084071909040115500c5c5803428400700d02001d03911210840425006136401c14050362180300d0840f03ca0035000c1034003202c1e80080041900c0341803007500142c0c05405440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 336204829 1250 336203579 336203591
    0x1211131e120803070306210606150804020d03050712030b09070201060509070f0903080d20040b19051606020a030b0405150d0c0801110a030e1b0f01051213211d0103 72
    0x450403116047c12a540118443d035203100b50100601c9101c3d507806003281410303a01100c04000d4004028800003800203000f681ea038000740c0c0405000b4015580341540c014042501445200401801400301800c180d2240303c841c40030407181030040c442c0c4815280003038109130340c03a641c1020a49402d0360f1024040c0800180b0a00003020441030700c05400300c4403a00742c02280071619504a0810161000140c4003c02000c0008024401c8014100c404c00c800e51280603040c50303040704003654a8061161000301c143d1a02c0715010400c180e0b680181042005034a00300083c0d0304640511007203480456a0f0012030400542c11220b0f85010070606021510880c9108031994139908448d007991b102c010481c9581d5004252140029014054205c085200c50024000040c5804829030001003a2a14a020301b603c01c01c000d125900c40e41c2128070400d03105c21802420309040300a00e13000c4c0004001962205201240d048070061494584140d1916aa40c3d803240f91586980340c58101e00b050141c90b05140d9508 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 336206079 1250 336204829 336204839
    0x1218110402090310090609050c0a06170a14070909051308071b18050106080612100b03030405041508120306060304030302092215080f07061211131e120803070306 71
    0x8069190414840d01012600141f03518085241c4419151454440d500f0b48000b40b1003282d00090b03280288410144003e016190001114018100b4502210040003d40100035a1a0304101b00e6000c407880070340c08210a50310840c54002003c4607820003001c041003000000c0c0883c0581100c500080010407100594a90714004105810b81a90401d800240c882004018054100382050f074011070541c1e0489440c0f103100c100c1034407045070003542004c25a0b00e80314801d4586082042d038000d44406401000403a58034113954011345018807035000f0f41d200305181d40b209991007105a0340200c402a0580b400c1d52201e5030300303401a42000d00d20a03000700340341100503001c40d0445010900b80700550700015510120600c4070011003501d812001040e44505001903604c000042c42500b00c81403441c0a020a0030034980c42400b030404007048403d400d81c0490304104420800e1514811240700140110400046a1b80a014581284520041c0c491500c01100128240b00000d42d4841f00c03a1400003042500d071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 336207329 1250 336206079 336206081
    0x90409050102041d1803070b27030c0102120a0606020312091002030a020901020618070501210f060e010603060e04060911090901050114010302071709030a0804061218110402090310 79
    0x8050320183c003604800d01c0700315507840c400c2c400d5030301c01760000d1403403d0350544800c2555503025060414100c444200c2c3c803419290a09a80d0010032840d0540b60385000b001400c03401b0750003c44d2102d1b0003408403404078143c49079a103d0307202158803035000382d8107010400c1092100150000e101c01c02902400c802c40c014190f083c40118426040310100580702d848a83c002850070720010076102942e80000441c290107680002c440303046031404d10341413000068080f64520000c07405080f034a482414a4002150802c40d50400010b90b840c2210902231603a07580f038200e013584d103584620000003840401103804200c0701d41103d414280101c5212035146d181501092501e9411191910907035910801407060362020004c450381d50009107400d5081840a4840340b44c00d6040d07021903a014a40010700080c1070b00d040c00b901001941000c060398889540760300203005e0441c3c1c0202d14078483d150424200110803041318890489030049181408002c0388020310000354848007095a0612030b5800010a44041e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 336208579 1250 336207329 336207359
    0x1003171b0303181902060c100e032502090a0c12231308041e0302060703080619080c1e0307060810050909100c110a05010b190b1207053106050f09040905010204 70
    0x9c0c1d81c000c584d00c011484400c0564804180f00040010a0320300c910003590b10108419040940c0e00000954034089090036640007612a0300340304502e05007180600822a9003100500e0b0300301147c0614000e540d9420303610300b44170355007000038407822007400103101c104902e840c0d28084004428119807010b0700da8000881680000c00100c1c0004c2010b410000141054500c1e02081c0c52284401e6201504202943d0344541902071502d010f070032040843c441c51180900210300e144800fa00b07440c2c0094981c00000c081c460110740d80740348800c20010018480c20306c0d2401b148500c101c00050000e40501018a40103096244d01580800035541024405143c09011024810f40b08000005005484c14280300360713880e559070084021258400e00f049452201001c4903000c0c0b140c118185410740e90080d040d07403a40903644008100d15a038040d0803001a40b4510901d00d601448940d069030b0035030301c160441c0c007032041c41ea01801540081c4460441410590800008039103d80009801d0640328100d001c81118 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 336209829 1250 336208579 336208601
    0x6100f0519023c0105070210020903010f0516030b100e0409020d0203030301151b0210050f0c120703031b200a12020c1003051003171b0303181902060c10 67
    0x1400003c0c048515440e100701e540d01160000a0141c1d1400c060040d440e20795000500b1803507074001800d07944665081d84483c4252001200030410f07418030101d1800040c2005090201280c40c0c000341c5009445c01585041e85001c181c0d440c4614105d03a0b109000141802050883c0c109000c4022103005990900c00746006c1c040c1c8070b4103a1902e1400060043c0048441a003400300c120010b1180005038440001110031001386082032550b6a07a1301200a03201c0c070690140c041c8d240629040c041410700c1e0038000781f110500a0341c1c24041050100000c40407400c1c4444400d000c140c3d48150060404500542460110413200136108100465290f050146690541c0480142c020001200c0c107850200802d0035102854a400c021500d0940d00d1000425141e002c0a8045440d503940d800f22020741070125407001e4000d10740d0700403801324940165334940055803400c42c120301c00503015690080c0040d034441405010142265890007607028006a070380000d6000d440b40c01f55544420070548580101c2100b50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 336211079 1250 336209829 336209893
    0x1f020a020409121d0306040b10030609050705010e0603090d0e01050903030d0c0f050a08070c11030a0501090c0b07080301030212030403120e13290a1d06100f051902 72
    0xb030522200900c800000d652900c1c413054054003078422034400094066000d90b200c81c0e080115140d803180b2108010b15948000c0c00e8608100003c000c1003400301d00c0c0c04c105ca00a8941c550342d0b00622080003054007040f0703035142c2c041d8030050120701c0c4148120080c1311200c40c10f040040c60180da000c0800d00b103030300c0156072124a0740c40d640701070540741d40001540c0145d9100d240140c24001103410040c0481e4003d030901080000e1022900b040c800c03480c1881ca412040282140d80c24449071401ea03020380035811042d05c216101e031600242403241082126110369000e844180b850b820350303013000fa0710000038002050912040c0320100019413041d00040314410b6540300e0840038140003040140a41041c031341ea0045034205421580540c0248180d8409680b842c6480501c0d01c100c64040743e81d55030154000c20f0611400d06405005c540c94200e554091305094454100729001d011007942e0080142041c00d002030410422044819109040e0400032005403040e60407d64001d00b4074200ca040b0840d8058241d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 336212329 1250 336211079 336211103
    0x1f021e04080f03070b1f0906061d10050901050f2a01050a0207030f0813060f020a0912080304030815131a010311030a0f0e070618090501051f020a020409 67
    0x40d00700308040c240c20b254440007036250064995800b03218490182c45024207449144104090700101c628003406000b810500700016a65a8401080c0c840d01035055860000d110248a589043c400c4031030b00220505c3d290646446e01340c000458495012540401b0500001c1c030030b40c403e11446000300002402284103100c1a00c070711051150131924003a0655407400d10406c0420300007031304010143c04041060400165650b81e65514201802d005807004001c20715203101c2c04012001035000c0d10407100b40b0381e111200c0e1503d480355160040003846002d05400e1003440080d0010740b040003819030124007052000f140c0b038280000315041c0e414030252074a0781038882c0786100340420242c0c074424003540d007440c00f40010b0500580b008020301c0040c100e00140c94480e60341c2c03007020714190072841c003042040040b54281c0342e840e58010095090807050b11f200c040c0356070002a808601c0d005c1c0074141c890041a0481046036030142c142100142c0c0ca44000b0741c00340c1700142000d07036210312915100a014035144115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 336213579 1250 336212329 336212339
    0xe0a0b09060c03070b061305090606011d03100501060f0206091002030705130e151c0303020901030e0a050307030201231303110d0c0b070306030512030916060210050f091f021e04 78
    0x7e0800d40c010b249036000d00d400c003006210440000c120385c10120a09140c00d245502000000e090070540321f0b0950140708bd07103400800c01c40180c1c4428103c0e40250765140d60b04000f40c0741241c80c1d56056440d01071580c44001b441c110194180d0045030005441d041c02441c00805541c1d01e000f640f0164812000d13044400200040c00021b4440581408011106202000c02c03140074410380c1c1d141080090101903000ca55040380340d0003544800103242c2301a046481d065900c4ca4903650325400148110015402c016010700e8482c140d58030900b41d40c0c003000384000381c2c1c1e4894429074403201010b00160200306003031010050684060001c50b03111a86640c800c208030a05003010380c1d14080141a010400d4a40a401c00104101154180c1040c41c02400c41d69030f900d4180300713140b400206412203103005014510000310700703400044201255030000001e0085075250719050050240803250050305030886ca401410404100008100d54070003800700600740602d11000301d00507182840d8810b04a4400202802 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 336214829 1250 336213579 336213589
    0x5030f030903100603020315040809031f0b0901030218070315121a010f0603110f03070f0216030b040b04060f020f04092004030f030507051b100e0a0b09060c03070b06 73
    0x1800380742d1401e01c1054616400b2036a91410380384a2039003230300070070301081c1003065503011a411004010704841c015040c407408a02c42c0030002007280550b62a10b1240c402d1420520801030481750010000034031100306107404402000c008219800b059500c80400c00c2c1040703516134142c040d160403444007540d241d09207004481075440b0100e00c1c1101c00701000411200304290185020b85580b45000301d0700000410021310310b4041c08480b1a00400007200308041e281c2d00c0810509800941c5e82142d0780d2010071a402e50310b205aa02016007001440310000f40880c1d142d21289070010702c1880005044041b04122400302d0f000340034884070b03507500040c04220760402c0380250041500e460b800b01c4600c01540030b00010900c9544070080181c21b2100400d41031602940c26248119042000d5070640c00c03500e000517900900203d640c0d4410500d1056200d0503074840d446080740100042d00300c54102e070510750601140e4106d40b14081d40400100a040c0030050140041c00c4842d1046290005030b050040400c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 336216079 1250 336214829 336214843
    0x80c1b01080a1104140a050a0b030601140c0c060306060d052d0f071808030403080d050a0b030d05090a050a09020a030e030304081c091e12030c020a170405030f030903 73
    0x11440da030400d503c070901c2d280d908046800b03c0d42c00481c01098454150081550745603036920181d4441030068000802c1c445070b17002107100352800d030307500c0c0a980c20745880f54885005054041ca041e90054060f014141440fa0055410040080c1010300b010040100d485c1522000c448030700200d2640900c20070794410380d8440b01030301444800c1540741c80c904a441d400526500900704410000a40c0465807003012170040c50300a8044002920380c2c031a01c80c00d01035455070180901d0101246450f0008034a01114031850143c0100100035210400c40c0041c11195a0010042c050303020075041d02c0007031265a8000c0b9800289074401004d80c4400003070002400700c406d04238003003000da001003081000080007003084446148041c03400d2464100804018001800c2820004009188051200611084012801800d240f044802141c8030200500440c2941d1025910b4400b507448401760740d000503903136180304c10440780e0112100d0500d50b880b07001910f030008041290189030800500484c603801c082c0308031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 336217329 1250 336216079 336216091
    0xa0803040c0510020f120901020613020415090c021005060d0b0a0b060a08060414070c080d1803021507021f1a1503010e06060901200a023a0b040b04080c1b0108 70
    0x1d0401f0281000031351103c0000f00034214910645420301d0855486512007000c4000c1140403032283c1d0384401c120070041c00008013080240c407a20070400046c500340d001d030503c141c00c094445440e90049030344018001c5d4000e02852070664a0728018429500c409011f0901c281d0305544902d06c9060030000d102c1100d0451408080340c008401c200240c26800115040380f050344000b2040c1d075201015000d800400d20000c1c0106140e802d40d00c5a0141680042d043d4044a900849c0c80c6140d280d030141a0703a6240340c00101c000c41c055145402e007840ca034642c49814094061902802c1001b40c890010b400a04584e40c00381d101d403008070041c41030010f4602c0165100000f40d400d1480c0c05284000a00341716401b440c210728054401150042651051118903503456000d4444000d903182d0f00e841c401d0282c1307000e03a10492078400850701140481d210201c0741c95240c00418a4210751140c1e1910035020100070f0064620480403c80a0880d20701040b0b2036603c14900b40c16807000311008000149200b1001d051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 336218579 1250 336217329 336217363
    0xf020a080f010b090d060b090103080415090806130501020c060c0c0601061b0f02241b03160f020117010e0f0c09010f0807020c0904050c19080a0803040c0510020f 71
    0x10b00505542d401101ca9800f4115100621700c0f11614000700a000f10400098001114038000401c0018043c098001e4854101d000d00014000340c80441e05010903108000f1507a20160101ea114040c00405881280c0944005840e103e09003a5040c50204203540301c0740480c000282c0c1c10584030060102501628540c50910000038410120070224900902e0182c81c100006c0240340855566905481c103082d0010041415031000f075561424540010080020403205641442600c21001c000c94900500e101c2d0990602d038404d85030b4401d8100f07228402ca040c002c90b444e0b0010700115160405000300540001003400c0d00d000352421032820409403100343c0da9842813019604030307038011280810f0000d045c030f404156999051012894400200314250b0440565000c1c4001d1000c080f0b203010440c2d0041c0c6e445100b0302c00c46210011404254403480205400c0742d0000000103c02c24003c50308140030380e15840c000d0f41c030780c800a6222040081c60b03001682c4500c84081c2d00703200502c036222080c02c41d44c203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 336219829 1250 336218579 336218581
    0x405030c010507030e011b1a06120c0310051b03130c12152a050c060907060c1407051002010203040203060714040905040501020d0203012c01031e02030109060f020a080f 74
    0x90050a001700c03200859050000716501d0b4031424008035121409503401c071403117074180341202200c8130700c1d0741040c0c8034240224204030030340040c140000342d400700c9e00c500a0001e1a0380144129000c004007405000c4507003441910200b0341000001030051030003441c040034118094001458001c445140541c090072800c0b44640494000c01c260310015507103e1062500482d07105546d0240c500b2150300c40f02c030381454a0901300110b0049600c4400350030765041540c2114040d80390180402e560704480c0c401e030000038114540200001c0c0d90100703118080520340c4200d6200c2c94407900000d0501c108550300c0d50040c2e50100030801549001c2020542058290a1080c100011003080f440644038502070401d0b000d440c3c402007030400c5825412201000982c100c115240c2d40c640030b450441c2c406a014002c0701c4407000c2015001d510b034400b0841c1c100ea61082e680c00c4600c185c070580c16450fa51030301c405e070b030f03d556191102808a41140501c00351148034100c01695220050005408290061302218240e03020344 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 336221079 1250 336219829 336219833
    0x10807090b0a05100c05060705040e06040e2d06011203121a100c0c0f0e0c1309050c16030e01021207020d0609020d0f030207030b0a05040c060f020f01110405030c010507 74
    0x11150009444054800000101c140d4109130785c2d01e0106480100713240305a10030040140c0c0c0c0300018000355001a1124461611002d04010549804a017a06019044090086203204400310095494040201c002034be03074a4040c0c0d55401d052091f0300441403640f004940104042e03000e1001504074410b01c408001c00b03405402c1050342000440751440c050304100428008080c041e482c002d10a90b030284100160a80382c0441542040381791198420003135041c0046219950078506031010b540c900451100d020b49404c5800b80607183c00342c1070b400e00c0c0104208421102500040015440d40039880d40c00310004c204000901d0880582062001030350140f040c4030059655000c06812290444030120740c205241c000200c2003680114000e00c071007890b001e14810141c011400c01c040303a01445050b0b08036a01c20b0303c4001036130740480d001054100075500600005009000607001110b02c0d104513405001e19540d0135084603680c1410400c9608081820007591908210212012100303103413403400d065103a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 336222329 1250 336221079 336221089
    0x101205071511030c0102090316181806020d060302011112040b030a1524092418080622030914150406050304030806061c0506040204030b0906010807090b 67
    0x50140701403001d01006188001445161403015145128090f40e90b10350038091079074001c0d4024003a95000b40614a60b807122501801c0d646004c840004000304c1c000e03400784500713800410748030800c1e002800280c902c54001c114036101600c1c40f400c46200c0050729a0840c0000b5101c004040100852544458500718600842c001901c0443c0c407102c03070320313501c98940c1d035060009080c41010309205000c1c20880021609109400700341148522060383c08040c1c1e4049089070500b119004a001d540c081134465105c0d101c580007003040c1100907180490006152440c02ca0446480754414402948000240520003000c1c44503141c800100300c4c4a60000e50300c0341e4024103070700b00520650003486010b4034280315a07140c481d01070034059400c2400e141c0c1c49855400c00380c0550411345040c1c00040c2d401000440c2800e11000300d854030f10940c40d4100c50a4580504a07000c1c0c84014001ea030015001e04c00040007410300b0040501030121040504455810002c0480c54042c150f44040074080c20485104059124 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 336223579 1250 336222329 336222343
    0x140904061808160c151d0424030c0503071d040f35090904030c0c090203010b12060a03080d1e0903020a02122805031902010f0f0213090509070807060305101205 70
    0x111441106e040c041040018005002c440d80c0c1c110206c05015030394400e81090307140d0500742c1e84200040540a6268410705a441c401e40c082c9481d60700146403a107240541d0342102560041c071586441c1c3c0c90750b82c6565400400b81c20126407994070380e1ba90b2a940e441107820402c108030750980c0d1207240c2c24a840400015070015026001409001086038042d0501084205c40005170400c120150760700d5035503580c01c00e1654800307c00c0c0d00c102207903c00486c10a2609010343c40480b5000b69a036400c4c80040c40000d8014810000003204881e55404500d441da242409180c000a0198004c1d241c609410300601c400c0e0707561100c441e08142c004202e90303101d948452050754014102070310101802c40c0700f40b810034914403900c0d81e907840d883d10800766000302a505400901d41c3c8110f2010500001e850014010181c1c0550341c032034520b807100c0003410b00c02e64040342d011a622104031401c84081e960346101c000d08110542e08107400007602c4404000011a00408120044c42d1904000040c040d9a071266071321044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 336224829 1250 336223579 336223607
    0x150305040b040b0403050c0615090702030c07090b01030b120f0c190306050606120a0b011b08040e071404030b0f060a050105070f020103150b09030106140904061808160c15 75
    0x14050012506061080055800c000c6081f4111102420802403c0100d50b03140c00401d403080c1c0c1010700141c6158800b20036201443e1041008108030341c10200098050843d2450b4181015034410900055965090842d100300703129170050001e0585900440741001002070040c1d004420011440700580030326545801204d41041001071507883d0b5100141d054442c00e040031085c83c038140300340401180d46500400380c284c0c00362100c1c8600303c0c422484131001543c0c48030180805074140001c00014101c42e07612580030500d031404010340d103030010011007550001c0d00250740400c0e59208104a01d17203590405904003404507503040302c1c1c2e0300d0100024060b2160450040180309444510f0045900a03048140c002c5900c6a04032051900c1d00f218003504c0c0c0080e04214032960130114006020b070096070303440c20085005028440c1e513a031140c03582c3c80031301862000b40508442108000c80440c0c41c880240c02d0000c0d040904400310303402824820b030f82948a1308142413441400c0e00050b07445d40c00555590102c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 336226079 1250 336224829 336224843
    0x109061d0a0209060705010b0112180f3201050a0b0a051306090614040b0f10050a0c08040b0703030b0108270106030b040803040212190f2604150305040b04 68
    0x9640c465041c4041c1c01000b0074581c10160108008003040b006402c21500181c0c01e980700b1380000407403600c820a0700c440004801940e056281580007040081003403250030f50040700240081d490b00a850440c00c15043d0307510003a8920799030a91810b00c028002d164000d40000e01c14064481d201c0002040000d1520400340705070b080e0385001c084400d80d82c100c28020711002204010250391400f00240120800804500c504e2418100010600d0840c024034a0381c200604903010302d280f507640c1692130f680143c0d18201400160a03548000400d8180240701070410f8110241c1c9550b171600e800380c140c0e915095000d061160480812010308100d07400000d41c0c101c40044c4614104002065500404540d0009040340360301400300820f10015000842c060340c420760301902d05c0d51140c9021034071403140b903410a2001e0300c81d50000e00030540a40d041101785019207500745030f139800c50710701c24250341e603140e80407810f6017011504102c40380b0f0b0901e500780c0d0443c45040c10b01c528074090390342c000c8240000b40014822 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 336227329 1250 336226079 336226081
    0x30705070e070e10050c010609110405040b01020f030d140105090405100b1c12080f07050405011409041812020c01020c060c07030b0f01140a03020904030c110a090f050109061d 77
    0x703540305103100c400303c08000d0498400c524040c040148160700c0300d40303440ca4541c00d01a00188084403031184174041c1d248440c08a0425061808010292901908450451141017558091503605000030321a0500c0084001000042c4146c985130310401684460301c255100c0003000040340c0e0120fa1040d0000e4031000c00142c071722a000c0000c4814034840808450401014214410800e408500950b600d6960312040c1c09903550351100140240115420030029101780300400031940210300c05151151003100f00ca0410210402081c1219070149003020b00d0100d980104050003054000d81d550384102d0b102510022003480c00103955914010a8103005040c001808000d80b48203020f014090b60b401100c4040303c1c1000c55420a0094084c001c04a03d8981d00c0c2e20101d0f50314020007030004990707000d820007125507a10b4030140c600d40003400040e200e418030311014031803950f50044114083d040c001d10000350681d02c940351804030360050700064440f40c0f03081c6003401585400c400c0c101420940500358902 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 336228579 1250 336227329 336227341
    0x307060b011404090e0f0102131401050f070b16020105060d0b130b1018051311040b100c0b0f22030512010b0702100c020f060711060f03040b09030705070e 68
    0x40d03801c81000b20319000085008219200190000f1030b542d91303140201c03100d418800031054200c3c0301e2642d02c0201c074280803e0401ca8003014404200031030300305040483c1800c54840c2c03910346c15404103104070348003640326003003007003008010303c20150112141c4001c0240e49000004208215042e030f4010b092b01000c03000140f0680c620440c8038a031103500c400b503240c50b4100780082006000c1207000c1c40c984031040d541d080c00d15003842e2290501c9000d103902c20f50021166904c80c11010110403000942007911542c2c0712400b9140c2c8441e064444c4029a25854140c20b141041c0c2c0c0b1a0901070102d0302c503001030f94107100c840d1081000742c00b09241e020622082482c901d15050b0703540c2c895506c41510a104880c000a100c0d4400c20161103078a0082d95504035006020708202c960100c4101e00030743c000c0e9051180040b90400b24081c090161140c3c0000c0c00c0c449441c400140580c208031812462500c0c004200020020703400b00c10758201c842c031f2000710b0401c3c1982e07940c3c680320f0807140103440c40300712200000b0714 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 336229829 1250 336228579 336228587
    0x513090b0c0c030913061d040305040611150403020c01030f020306281d0f011413020f04090518010c0203030c03071b0b07022109010e090402010201060b0c03040501030506040e0307060b01 82
    0x201800b00074289040092105d4803607000e4442032045188004412030007172400d415040e5854881d0740d0590740c040ca481d003410011b8880042c2c4031600700251261804546490902c0703150540114080c1e001004c0e0803c030000010181c4009540b60004507005005000b60f54a407220350440001000041094010319a001d0302c0001c1c0069002e0000c09a11b00365042c3c5a040c80c0300c0250168501800e00d03115682c0b11800180d51310f25290400d50008208190006040d10341c1d03028103007242401c240949403556440386241910000e450898400d4009190409210400d00c100302d0550032600155043d071800d407000c5240750000515180a00101c803640301401c4200c010a0180141c4c44000c2c10150704040400035078505100c07420381c0030b0b5841142c9101c6200c0f0064141c030386803c8140d54412100f6101c0c81449581e5001a00481c1590b403201300200324200d2040c0502401082400150307150b5140200050646001a00c0a80614588001c0081d02d10300802159020354102101040c07207110794004807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 336231079 1250 336229829 336229837
    0x260c030714150c0d11060606031314011b0909140402010503130510020c10060807290903060103050f10090807060515091501020705030c061219090303060513090b0c0c03 74
    0x414000d2140701d00c41d01760006000343d80704421504072400381da2600d00340641444103580e80c0e00071529014808001612841e0480b800300c0e000400450b04190b03001480d41000c0003030303031240040380e034102082c0400d001d248908070400ca4140244090760801e42c0002c1c0403071001030840040182911100028440c040002c403060a046401c1150b03034407200c00c00c182d1540b030007a107040900d82c20300c900001d41050015511003a1032000c41c68441861030301d440c1d9030307140d110301124405080c418032120380d1a940901040703000b54020b1019004510300c4180e66410880011100043d60345488440380106407070380207a542d2245d02000005081d04ca20340d030103511700b0040c0c1030203038482d15201c1009240e04403042c100004607000c0e02145c45241d241e00030151074940901409401a5041c000e580450a541000c00d400450802d0b542e44107450202e4041d054440c0740c0c0c0282c001c2a1541d00030401410401c401c0c511303aa103541d104020640080c1e031103103205040a0651003140b2800b28901d481050240126 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 336232329 1250 336231079 336231097
    0x403120f0c0c14010806040603030f0309030c0203060f010e0c120a09110409080c0d080408030c03040212030f2a070306020f04210302070605120f10260c03071415 71
    0x1080704165501101c00400001076210f500003200c410204130b0500702130041e0f4090381d916807179150b0000d580c41001c60042807030310416410080014440d20150701c0611030140180788801b11160b040d03060030001d82c0341d0003019151214514041008080c40300890000c00d421202000010a9840b20703802c9c1101400c3d01e501c5201d0344949081c180b881013082e07004c0100000c408880540e038203a044800c0a07560103504950241c401c05d01080040c2800d485000210b50241c8001d241d00e01252124881610350341103010a21048000080c0784600f05007101e0303591050080c0042240070700c0a000b000c00c0d464a16912005000a0700030504041101c203080c01d4030082c1c0b41c1c51041d80e0f640c1d8000030f448910740120740000d4015002e07049000c21141d05c1a0100d400c0c102d64005c841c940d03911a40710700380c42648028a00001c000d12408003040b4011000f250b40e0b90303644054116502da6801c0100303141000c0124281a20a40c8460700401c50340206000704450701c2c070101c3e000c2c950039507450187c100c20302c039003810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 336233579 1250 336232329 336232343
    0x60905130204031401050402130606090b0f040e011805060d03020309010f02030919050415121202070306050f06010207050a0f09020f070c0f150c020a090c0c050304140906060403120f0c 81
    0x4d013151404c415032060744140e00844901d603241d0880d22030401220f030755005102c0001c0300300000b481304450500c010030210060300205031800381c0d0313121446003a002c01c0e0802d1481c0c5001058a040c4540c1c68000d00d600603104030340344019240302c1d0303801a65034413455801906200c01c6032030500d9a0350080c0103480d0322000c054502d19002e09540500380d1150340c0b500a881c41031b86444a007170109203d81076991b0680300300d0072800144d03035895102c1013001d55025001a0440c40303100808400988540540784c042e0021042002c1c6a040c00c0f000079040000c1034104901a0241c040e00b004480c65020740441203c05d408001607a815400311a0b550b203104040010304007038604c0b400000c40301c101c40000f100b100c0c00f0031510301c0c09a1144c0350841d440040000f01940c0b0401400e820301c5106103a42c801c0801c80044d0500c8118904555101411030300203500008060150b4060340d0183c0c2400d1500075400601219502e1600c0e043d0ba40c0e115210010666200402055a030303001100fa0050b50040080c40d00258 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 336234829 1250 336233579 336233603
    0x10c1b06050a020601080115052101020a12050609041e060e030a02030406090b030621010f06180b0d122a060501090e0f12030a0605060d050103060509030406090513020403 75
    0x4000c1c16551181000384010310800e40001900a010b11032600b1680078681e5031034a00c5c6c902800c102e040c2040710010490180c040c100c51070f85000900c010250140c0589408072048088400f10003203800092155000e03c4419041100140030912064005841c003500c0144610140c00e10f84010840c008010050303100001d00d801d0800e03000005001106c090b80d880640040e2180e1581c415404103485858200d40040c0f456601c00d10b8803417200c02c081303a1140c000140394030703120f5450090319032650114800340c0c000c0050404000441c01902c1450b03100751178044c0d046a02d66245407c442d880303562541003080c4442c8410300c0020340310108001d600324910b030b0394220000c0c0c240b4a000300b01c00e200c0c8036040792070000c01304601500401c0324640d0500c1c0f1809000c1e4007000403000b80e25a1b00042c60304c610340740e1351034011030f155880340302410300e2444030500040d403981540380c8002280c0c000b61030600c8551040c4000c01c0065401003042098981c03e49502c084010404c40050280c01103400003404516008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 336236079 1250 336234829 336234839
    0x9070305010203151c080d0c030f1a040605030c0f06070309150f080709030b041721061005090616030c1e0302060a020319021303080a021b1509010c1b 66
    0x62821810746004696401c04401c3c00045c940c1480a901c400600a40c02030040705c803240075650084188800904000c40c40300d42c5a4030082c200ca2010f002a0940e03407200c0c0d24043c0c00d04081c03040c070003c2d020550041101c48001000680d03a00e641d07040e02c5224141c002540d8080520070714640c801070a01004150710070410304006443e2421400004000421030301c00100e10318442c000010807260003400070010ba49983d12100020b04501301403140184080015501010a002d8030a02498420100402505184082018481c099481c0d00d040100a00c110401c69555030304445490f968135143c000d1000c410720381512030302d01c40c0700d01a090b491040b151103814a8100344d4904014444c1d401c2d0b809541c1c83c51070600880c042504c41c0c02d11140003c41d03d041e420083e9001703012482c00c0f034070050700b95503881d40e98031420380c842c26803c2c0040c1c000c2c0307610f1511448850700c44400504210344403030100d20001e107400894001c00f041c40f41003004540b1070000780440099100012444145030600355905c078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 336237329 1250 336236079 336236101
    0x40605182404090515010f1b140304080c09220f060f0b03010c0309051b12160e0106050a020a0f030e0d051e060402241c0b010e032409070305010203 65
    0xa2044507a80750500001030880104600e0564036074130147c540211080580c8011a950344100c01c0ca41400414000340c0c80104209400742d400022908004580d52800c080c1c030917040c0a070207105c86000b255004107020b102000d000003118410100000d0300303071035022400d00c280340150300c070001b502c502d18114070072040031555007280b414100c00750001e200315098031008900712040c90b1006007603500158940c0d80c1a14611407070b07006410340104084850f1003d11701d16801c042c3c01300021405907008510030448801e43c0c0b00e94500510300340c18094201a43c401002c2d454401c4158018181c0443d0400e003010035000e070640b0101c0640290081c00d40341601e2510964402400c0e8903200c080040d01c0202440d04400101907210329800342c01208540d40d03c180764081c0200328000740101c14400d20054000300780c014041c50a600241d0000301d50300800c034001401c94004c5401d460b00a0700701c9660b000d00c1400f14035505000350000d000b405d080e91f550070540e80c1405a503410050255000000b4400103c1403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 336238579 1250 336237329 336237337
    0x3051b0705100b010507151104051306080d020a0c090b04020d1505011b1a090109140d1205010303050307080a0b04090305070c08010213030b09030d0e0a03030c03020406051824 77
    0x1030b40700100680550b142c0150303510301030307600e0042001000d5880405000706075084615452440410281061346403400607941d1802503005030070241e0350b060100002c00040007007107000c1c081030002d080c00729810748500f01600c0d124041c0c1084240c8410040e446034503158100e610781e5903860ba003000000340180038100602150300c2201d00151000320001030b40a1261307242049503500418103100000c80c95100c14040707600030031104481d582c1d014500086010000780310785412080c0e01410300003603204805403022003080078070a201481c1800600c0043d411000f125001145402e14101d160342d01214440604500203c0f1500203040175101c000b055088001303040c1a62050845020309501c8504840c00c0380541164441c001c04001c1003000407070820040c051300b03d00300d2815a890075009024900603540181c8407807507264855680351044c143d0503c1203000c2d0603854a8158a828500880104180100068031162802d030b022110642e03600c94807601414054007035009034602c43c0300358420103504 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 336239829 1250 336238579 336238603
    0x70609030905030d051c02040308070b0403031103040233040801061a19120905060c22030b011707170d02150603060106080901020702090a0c0f030605090703051b0705 73
    0x9500808540c42c900811311642e03141142c2d51740c0f410078000b528049021500c0d14030661070154200404808141c4020083c02543d000d240111840d05144c90010100c4994903100940c0120a105010040e0784042c0c000c0030309400c2440e5460070030700c10070410300c0050803042e44043c02c100000e0002081541904150120f8160222501107075182d1208a80f403407090b80e401c4d80341d480c100e980b10701105015000c032070985009484002880d004951318145403110648201c00701100c0466454100200100503044040e010034500f280189523640340c004042040c050301040d201c0701c0300d00300c00c1c0c142d0402400d001003805200c00900d4400f0807144c1070f01d9420110002c0010300405400b4441640440361050040101800401d940e0380307044000c0b20110340240c041c00c8195020009640503039104001c090140b81902f00005003d0001900904140100c40341d5030305250402004009941c0c0340c1d00c2c0141d01615a04010805564102c0507800241d50400005142d02c030114102080c00000101c1c51000b04e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 336241079 1250 336239829 336239837
    0x1b03030106140c0f010f0e16050d0b250804020f01210b010203070501050f010e0105100905060921060a240312020312010314011d0a12090f0923010501020a08071707060903 75
    0x6a180c0f0310b80f0107203230b401455003290425840d1400039945a84e69544206081d209065203464281000c09001600440e0070000b9950b42c1400b0a502c0c003184440311010003420886541c950100024407160041013544005a9071403080306810f9000f0302c2150034080d401402041146002540c1d001428002c0c06031a03812140306002059a0421740c42c83c00500c9640c0d29403561480c40c06080284907070000070300c180c002411178414140031220350a000c0003100c408000d4041450080140300403950002c1c2012900f03007400070b40003881d03040094042c0a0b41e4000007500407145241c88280d10314403034588071281100041000005009000700050050200c0e6802400100d0303e6040c07c07940d40d40300340c1d4400300940101c041d07900080c00c503640310139802600d800c0042810f41c0d25900c200301002981e011500381a180c0446170000d008680c0d50049400d50340c0381d00009035041c00c000035902c41310780344002e01c140000100b8100340083e1810080c040701003000000e81c2c0d100c0ea4034040c405020701d40c900320041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 336242329 1250 336241079 336241093
    0x2191a120c0309100c020309060a11061b0702131b050301090c08011409040507090204060207091508120c1203010603090209060306160309030318081b03030106140c0f010f0e 76
    0x7450610003103e0281a65000500501200029507401031075005080c100b5071208000c07441c036544610313001d84024406a210400008081c403481e90408500800703010007a44143c809450050181c0e06807072200360181e4010741ca8601a021b4a001000900c261380c6204000300e05141c0380ca0380c000d00071130584800413003d100c59901c52200792040f00080c010010800c4203110424140c0c1400c80d001548640910201c41444d50b41d1600281264019046000103030403001040c44050114064104080e00e00c40302c0c180d405281110168490f0707000c42c80c0c0c401d5400006a401180401001401d00e080325900e491960b07540d464001400608003418100e0058038041c0005c0c52615020404c0c1c0d103e02c14010100c42d10510403a8110010240c258045081c541d0b035100d2140c0d201c01551004803004d120307040040e51040c2c0c0344088103400007500b078509200e510400040c41026030000c042030342800781e25001600c4035036141c1d40b1420096500680c182a610f0715411450100d0f580d0465a568403201082d00c500e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 336243579 1250 336242329 336242341
    0xb1308151e01030507030b0703091a1506070b070507050a05010608060609061008060105161a04020a0806160518062a0c030307020d020f09070302040e0703020304050a02191a12 77
    0x103a0703042484060066080b030b150420115260b0340b07400e94401036a1500107020354143d80d600d209006080311079000503600383c04104c804041c40c298881390907021070300e06003003040c1030b0354101e080000100080c04000c0f0201d07219041060401640c002d20380c0c4034000f4002070307071118105941c5020841d0050300c51f000e05c01c08101a410b203083c038240d0304950b03982c5250361941c5a0f001560a40d02103980e0001c2240440b5200ac08101404031500b290101c4900740714190410380108050104160043d4065401c0402131080001c00680214640032080c2011600c804045001c8600300201c80f01c042d80003c070000d80030342c600c40a03003800151044100011041c1001d0348176059540c030954202d950705503008103c0030b4094a0b1045159025902c020f01c1340400e110130b000455480001611a100829000f19050141078040c40c40280e200140d45011425494952102c0c2d030b440c86010400b0740607070160860315030281c1800404c40c014010711454541403000001076880942d100b0951407520207010000304803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 336244829 1250 336243579 336243631
    0x140312060a0e070305070908070605040e0f0601021f0f0c0806040e01020c0703060e01020d0603120908010533030102041e0e04082a06040b0901051f0b130815 69
    0x291000c2c1c608000b00b60759141010340050002400d0b0100b8019500000181154100321400280c02e0715a54a0348603860003c0181500304080c1c40e10b00c607000d107541040480e0b45e00040140030200c5e11086902c0c00504810602c2c001d003e10b03800003914604003461418560b8010007900d00988080d10b00300030b480e00c0c41c8161400c1340241003c0300115001041c0030000304045400c00010400702c90001840e0440c130090b01d8084585947c0100c0e11250b40c521844101d50700306e0420001081c80f00000e2119140c800d10186200d4025a0f0b8040035481c0c0c0c80d81c9001e62901c4d0544440d450f003010f8003c6540301c1d10f030b2403000400c8000f081480b41c801c42c0039070042804000700312007a001d9036010901904000c88808240ca15401245411180e40340800c0359a4103028100111401f40303001d5070768030b8040e040000b015825100b00401208048a250300e0101d00310a00f03a400d00f044540d010021a19800c4a107180105040154000d5110b441200350801040c4102104030f401040b40c01050011540144800702c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 336246079 1250 336244829 336244849
    0x507051629090d061415090a1b08090a0f0c0503010c021b0105090d1203090605070806010e061b0a050114060a0f03020d030e09090601062c0f0a0314031206 68
    0x1911405011820b41801c0c0440802c907a43d01c43e9001282c416500f050154004008481d6559002d9004048407002d0a00c11002030b003115180703809201c070900d00101da48680d00724981010400404100080c109131052150007225a40706580310b6081e500b40c01c10001c861031354004c5905c00d501c0c0c0180d111240d8000601040400142c191280500071042c00554841d0007401d820794003d40030102907030000d40342c8400030ba42541c10b40c900081080c02410440100e41004041c4030500c1032030401d01c03180d40c1c0c110402c01040d40c01110030301c1d554500c0c84d0300c042d42c180450801012a103c2c0c1a200c00421038190001c444205440785003206560b0f40c0410400502440c1c4581c4185026110707050000d4100141c1c1e4070704d01e9000781880d902c1c10070320f41c000c100c0743d000072500c20f502071304600018050168002214016800341d484c50010034000c00c103043c01141000d100a92141c014540e80d8074640d180d1815403002190840721051042282e0010542c41f58800412031107012140e20000b44617140c0202c40f1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 336247329 1250 336246079 336246149
    0x5060408300601121a210f160909150b040b030703050616020601030b0f0c040e011701060603270609060207080301150503010e01090c030e0304080709050f01120f0305070516 76
    0x1386140e4200c0d03414481c01074400c40341803002c1c0008808018481b4020440022541c1402c001094007040c43d0500c582c041b485a049816031a00348114400030441111025290070000c1a00003120310600300003400030b06003e103415800d8040c00d1400414048085900c5202c0c01905034244a51071152004a80b541024040104561124004943c1c1a107071151501d80c0110200096850310313803101400003814030240e01a50020740d0b5a034607040300d030300f082c0210401040c603810b0500c04c130740d0400c8944813440b8004010100110400342c504041c8a03c0b034001c01b1005811000841d51002e07103041001c1e4030b6100340201c0701100c1d0301c0e1060304039942c1300350101c0741200e10213000800a80d00302501d80010b085100c6181d01055194076020302d009405000400017000303c580181065882c2820a10580f40000c0c03d101d059042c000041241c1e43c0300640b01280d103540112000b001003082d240c140c5d980d01400300040c00c00e00c01e240322071003000c40c10854041618040c64030440f50a00d44020800512040050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 336248579 1250 336247329 336247361
    0x10801020703090e0c2a01241509030f110319020102060c03091e03042d0b0a120e070e090105040201020703121b0501060e01060504030506040830060112 67
    0x300131804141c44040d4110661154041c50400303c428040c0140050804500c0000314907440c045d0541340c24407903094005410442d40710849103001c0086501562841410403007240744114111881c030440152019581c010800f1080305c2e480e00708001501110004c403400307031142d682856200031842c0c810034450b5030b05070300414041d502c41040e41f0040d00702620310b00d0580b080d0210408140321190607180b061211800564540e4501854002c0c11100c5245603088440740c100141c0f601001942440c00f500d030f40d603c003aa914100940d04640343c07801c4132040c8111918004110b18140000704003102152041d00f9111b01c203482d03102c0980c0c200d52060f03030000d0250b44010780410020380e0004844440f80324a05020848800c40c0840010194407581c00302d440fa5500c010500c842040000210b02501d440c0c44c1041c20719080da5203d075652400039001515101c000b00d038100500080c01c0c45c04080070035032241c400050001c0000b0480401040d01d080340402c002800301122a07449100d9801d9020920340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 336249829 1250 336248579 336248597
    0xe0d05070b13080702040c0804020406060306080a0b07110d0905010201050c1c200a02070f0605120c1606020a0e040c052a101514010f12051f1d010801020703 69
    0x4400c5600302d1601c001c0314000740900c842805079681d8450340540a20584410107103152501c10801207884a402920504d4586441400b0802000562240c507544c0004107000d076846100099481d00300020224296102d00c65140204e207612001500440c0c900780c0013403001d622003400b4010240602c1001030042d244400b40c1c485000120f40001c11500c60010540c3d007020602040c5604540c440410a0056444034600300031a400740d0600d50020805803402904000d80d1a840303844002000d800b40e0051800841c43c1c0b0481012500342c005503a60040c002c40d5900360010700a0000d8400420080c0720303c0c038004590a03914002e10444514000740d06031030304c209142601c110248001103100c110f1906caa40d644465141240c40781103074001c03413a11002c04144c90107034452400004910307018100200d641c0b0100d802a0869000101d5007140c46000c02c8a42c0c03024800c1241b921b02d5000d91491011080b4000707030f80c2c0d5190000786140540301584420390ba890300c1c040f44c280e102c2d00400800003900c0c24 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 336251079 1250 336249829 336249841
    0x3030d050c0c1c0f031806060b040e0108070503060c030915040f060e0c0102031e0706060929060a030507050910080114030102040302130902010c05030d050f07020c100e010216090e0d05070b 83
    0x3500420f042240107030f003079901c06c4007500c40604580858002c4e03002c000e00000c091016000d910307440c034010080c10004015aa050401094072888054260300c5011030101c02b042110005101d55402d504050303190400e985000c3c100181c070000b030790006480300f07440d1076000e981d9075001040807100c1403410380045280000c200b001c82c02803000b0040c91204508103105010015100d4046c4800800b140400411501008002c51840070041190401c440031041c0703500341c4503114241611114482428001940e0350750003000e450320310a00b03152503404034454811081e11500135807880d069a40c021000300510780d900060600300e208602000c0c1d807001c12454580040c0003150000e900c180d1061400d09890009981c03030a1035600010158981039440b0820407460346d01414070584c0c454020710040c03d840305041c01280414001c407884104101d0040e00702d41d00d0f0790080011650305490b42001d40304c490340d541200340c014141031000303120500844441450081c8204152032980790802c88000003a2505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 336252329 1250 336251079 336251081
    0x40c0312050903010513050730030509030312040b090d0801230a080f1b060306040b040b1306051c0b07051c1103040c0f0f05010503040203030d050c0c1c0f03 69
    0x394014000c200c010410455182c80c00c0c0920b40c043c1d0740b00c241019982c111441c02a04012840d0010014160b101211014080800d84c0c40b02c0384034458141c0010044d80380c101290240b0800d130340c2da80c05110000301c10751b1252070304d04198403c0d13014582c88655504d409440c0ca40328880d0030005c03400102404010b01c2108904851146542d21011941200b04090804592004520703401030525410001c91011004014442405100c0b1000c441c250700a280c0e5000440a003c0500340d036000c1d80c0c0d1440c0c0c6240315180c55200807002c000007030441a04800d8001c52101900203801220b0007400200903014405100d2040c01d09003640c004910713030380388e41c0f429012a1540c0250f81040322003a001444480300c04c185d0f20906482c0712900c41425138074902424840d400c5d1890703510500f10304156160400c26011a848503400382d40303017403800c10b41d00d0b00c030703400001d180d802140040303070301c40d442c0009005d5a491000c000f040401d103248140d540d0714141220260349824159205070102d00034030544081c841c82 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 336253579 1250 336252329 336252353
    0xa0e0f0a030521070207030b06040b0604061101060302090c0d1a06041712071101030b03070f2913080d03090c0e0606070615050f04020c03070b0c0d020c060717040c03 73
    0x50f07450307030301d840301180c0c282441d410302c2a90000c015070440e1505100b8421001400c1d644040d0603101032094000f881c0c00b01e8140c0c411031192404004410610b562500d000b90024001160024101c8105050100c1c41c0c0142d90302a100ca165030b00d262107007800b40211001004d28410000030400c3d4140381c5070031244409942c851010416900030142e007130a0030000381c0054a00b030790080346040349004034200003404941218800318403a51194000b080011007103400360003a038160364100c03080c50f0000c0032040c11185405050750702a160110300551030040c1104590226840d003012110b0081c0e80e100150100e0342150702c0174020590a441c140810413500e07a4032604106c0103081c00d80b80805548444040750b140d60000c2150710b000d00010402c9140015004203492412502107181206400f800d540d41c1c070592100400c4805040002205c40701c5080070755915000215095503030329010110b0380d132a96000ca03102d8010a0700c244104000415140c0305501c0f41f6444588421351a0030b40c0c0700c0a0b02c07842 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 336254829 1250 336253579 336253597
    0x11a190e0117030d0507030204140d210309150c170907060507030e030a03020c0f03031813061a071b03020f19050415051314130c03080301030b0a0e0f0a0305 69
    0xc010020300c0030301161381c420244144565540180c6550406024444885541e40d095105040103404100407a2038207841c4190031020704e0380c0d0750b0350540c1103c007038025002907240982021094545c0e0034031040503070017051000b26281d4814036016102044180300b10f0b130945a01489034410300c070601025005900510b002406820191021000c41001030301d419441c100840041e04078003010702d0113041600310400030707440c00c4010b5070800203d030216030b158198080600340f2480c1300c424591500000741c0c1c0004060000304009100c9240c4264941e05a540400402c0b03070050720100d00544c0f8a005024000305503076004110343e03010406201040001c03490351900000014482c3e900143c0f41d41c031407040944007210362071a0305441e45044100301d09081521921200141032031800c940403880003050503440003603e40044440001810040c443d17074840e800042583c200040040140094001c0492140c0f58444042c0f0048008840068441d5a00b00040402d036100080b010f0009010700c02808205c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 336256079 1250 336254829 336254833
    0x4060c020102070504180309050907020c010309170708130503010c0503070507140f070816061e020a0501051014041e0207060b090109050402100201150512010e011a190e0117 76
    0x1a444000140446006d810811800001c1c48018401c168118980000030701e41140c8503440c0d480e1440c400f82d201c1110030031150405640d0030b40c0c10100010b0315000403500b130060a00c2c544036035081c50244042d0f885800a0404042c10420001d058541406030b170f544e10301e065031680c0c210784480d01c0c103803091380011408039544042d240c88120f10380001c0180120340d4142000a1040d540f8000c00c090400411003500728505204c00000c0c02801d4104000402004003402c150304514a803a00c22818a094000010590b500340340a01000036490541403082c1c8810b00040d201250120040008440c0d1b280b55800303a543c01d00c500100401e0a547c043c0100a000740d0002c04d148481c80005a950b0030241c00000b00c481e5100144400c1d41091a445401c06c0c5150008010360380030119403418882e0940301b07046c403482c0ea403104e0904040082d0407010061030301c800240800101c18002811454148500d140581030414030590344840007006201101ea120040b01c40c1c0ea401c01c520b056203807440481201d4a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 336257329 1250 336256079 336256093
    0x515070309050f030a1b02030303070516060c02010c091d0a0b0f06030910050105062104021206040f031206050616020424080d0509180603190803010f091104060c020102 74
    0x202d601030100050465041001d1030350f03030510040c080c10318902803020302030f114030000010340142c80000880f6044502410615250f0b4422780e00080c40880c00300f001880b5600b00808242c065805402940d840e01c4d03a5103540720080d4554402d0407007040030701c1c0031210205002c40420b06c01401e83c0d200084504018006031216100507010848503402030328001c1c00c0354030000c1c0e41c2000301784a12600707000d000202c481c2407414041707200800c81c540c0b407030290401c480d40000100d03085660fa800281c108103521029189903180905202d4280040000b05801144000310080c9400d1018803030350041e02d600400c043e0801c840c44042c0e0401e044600b40032600a03540b5003001c008002d042000d43c9030880131440d560078041c103000c04c0174104025003001c88203100c41800100030f84d40d15208204001032810b20300c080c242da1a01b000916108402e030854104075003c00030f510a1000140c000c1d0f050781c03003d100c40b142080d504d404040440d003035008000e141c078000740014404a071140c1c03120041c1034014411503400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 336258579 1250 336257329 336257333
    0x907050f0a080f070c030c060c0302160809030105061207030807020423010612110306010c020d020405161803051c030f050106030614030c06040b0a110d0207031a040515070309 77
    0x360781c0c0000c00c80700c08100c14038208a10452219030565001c0c1803840e00c003801001694014160f0000280c0051829840d601d809078028401e5040d1404c8180c2c140c40541410164204808194002030f001d038065402c0c071000906a00305556040020030b590f40003404214510340700c500803a04140c0c0f049030f2094840d01403080c1d102d50600d2450148a02c40d0a100c0d1952501320081c3c04014140c0e030a414050810080c6c080f04c4101d030082ea90711207002e007000382182569100003040907004a1009521620746800c0c040700c2c0e6902843c40411031780345d45805841e80d5000c0d4401001000e81c0c80f00415550109002c801030900d1441c2e0b0203158084e5041c04905440e41e281c04001b40c1c1c0f801d8015500099031030703008000504058003005400315096002c0d2a141d07500b074010500070301c900d0264500c400030000c1c2da109030318411040cbc00125051342054030345071048804003c0d114102e920040e85d4404082c050052184940030340d2901640c0c1c0080105954441000c00190000d001081c8c07000340740c3d4400310040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 336259829 1250 336258579 336258607
    0x412210504030e030d0804080d020f09130213080303060f100233281d0114060909191b03150c1b050c1207030f08070c14010806090705 59
    0x10140b4403988926038032503c1c020a00d40350003200c002450401c5408000c0c0b00214010300e080b00d03074800c0c5843d40503a503540141c05941c52841500700301038101e18859640c4650b825030383c4c00f0341031030b5160070180c14189a443c000c0542d41d010590b0669407000c14081030304013034500340b90601d10003d402e00641c2d950180b09007200b0904680402c0710040480b110111001c460b02c02c641340380e840b9030404c3c16101329070700c60810171f01441c5401207804040e030b5440c0c4005800f404411002e030b130b803542d002009002e404001d030030100084c0c0b0250b405078080c01008000c1894004041a058100d584110307101108408507200d002d0524010101b034054201c041001202103001d9907551400030a41400c00b083d415003a517001400d09040d0030f0a00405800c0408030800500c5c08611440851400c0390311032000216640e11070309050740c6070300c000c04c5414034008407020012914050007515014101d4000c0ba95680d031242001c015420f517400e400500020005a641d01d030007000071350411344034a030081c100052410240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 336261079 1250 336259829 336259831
    0x6080c032a0d0c1404230702100f020910050301060804030507060908030f180106050d0b0a1d0d020606040b0a230603071d06090d03140c070f06120504122105 69
    0xd245203151a00600644161060000c030900d005c0e5020085080c401e00c5103400d4010046800b99071109a4000c240203510810040b040c0341d0202c1d208100c0e111120468071300a501107001e0502800c0da1004a124250199060702d040301c9403521511081c6d40e035580d084607550320000046680030303035424440303003c05d411801031403007004860030244690800700c2d05044140704044400355240e0609001384030320745812200300b070101d41c03047c500722854036005131150141296610303075100005003c5104160f10800207000d107421200350261074071503c07660180020380e49620368680c2c00a129a0040294102044081080f0060020003401e4040c000c00060030383e038410740b200740c0062010301d08911803c414865000c0b0b0b810044070550b02e011052804110244240c2c00e01509000103a03101703161011203401280e003403020007000c0d11185070715401c3c180a043d18500070700000544010150070400440d00c20940030315040b2094a0803101c0c1c0c98011602c0c5980e510040840004407011078680b44482e010322 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 336262329 1250 336261079 336261083
    0x170a02040b210901060503250812090108071b02010f020a060c03050a0c030e0d08041703040c24020a021e0a0305061b07080405150714060a06080c032a0d 67
    0x5541202c0c1d841038584120303a02034001040c9902d0200200100d41c1c001400380d21411412040070341451201180c100c045a0b258031540317180c0540d0001c407a8400c150001445801000d807103103007040d01c401c1030854410040e0006906601d40980c0c402025601420403940002a51720495505001d50340d509001c0c1e41004c0e1032100840c0e1070b4010700c42104028003d03894840d03010700e4200200d00e4504607180d036400c81d4a200b102030040d8070012038144140c044080c1700400d010008107669007403a140040f1441080c1c4580c046110038002c03845000c01a0103c040c03a0110070350300426000300d40341c0800441c041c0600003880004040202e8285c25210051640c0085016801514181c98102000b403010304001030300801c045400c1107601d00207890007080d241512410755085481102d808082c80390303845035000150149802c11074008040c1c4000075800d1003440b61020070f00041c1d69501880c0d5482d00c2c20090540c0c507410a1a4490785105104a5800d02c60310144040002c12410404a080c10fa004141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 336263579 1250 336262329 336262357
    0x80706060b1909080a0b010b1605030f0a0207050d120807091a1206030c0a0b0c101406120c01272103180b0315280302011103040303170a02040b 63
    0x41070382c44982003040300001340342180182041000315501d0b1002c141050013503005032000030454070301c140c9501807a008001d92101c22a580c0d042d00d9510480160070202d811001845111804280f0381000e40555448175840b00c0c60200d8010810010344000000500706810824552170004882c1514240510000c260040680e80c8a2561006800321344006004a0090b0710001c501061a15200e550703078101c6403512030700c030344450442c00d02138207111320030101e0f001060901441010310121211920300500c0d04494414070281c01200d01c5845050004006011440314800315501804400c8040f03a08000080383d910724503110f0205000b030b6480c02001072020010801400c0800d6005811490041d0380088042045131410b480c4002c0751000130042000200034014681d840d4840380b1848940700260f001a14070300d10031140042284c3b41c1484240d001507031040e5039040016000c0220f030266505540d44030400714007210b0b90320324045c002d064641c1d003540c20000003031074403cac0348080c040030000c0c212 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 336264829 1250 336263579 336263617
    0xe011107020a15020706110307060c09080c030703030210091e063602040b03010b0a0b0d0b0d02030303070810090c030c08150a05040c0302090a030807020922080706060b 74
    0x500441c500759030032200d83c40e212050080d0702180c001070304008550080ca48844641d500312021800c6000703041c402041c4905007140003040913002030101042e207001c1400c070707000d000b032078010503030382e10054030000d80075800c400e940648030072060b041900b4990041a4000303031031141501000d11510910310030b070b6040307949106d00c2a80c2801208403101280e0a600f80e01c001d00d10300b80030005183c0b002c50000344180d58524490900b92003e4001070b0382840300800d01c40e402ca981b843d000c9603a0740980116135010b468200003141a14100500c0202c02d90050011401c0d42e440c04000e56441c1c42c0900040b0010700d03031100001c0d901c01103000707082d44a81c0c0d036a804200d6450b01503001d007190101400b5103883c80d17240d41c0241c401d0303100c0d4940745003115000c0b00c001c69400e10301001a0024415004180c1d0043c1012001000740075034080140b030600d100396007402140c0d42e02a034110181907409502d8000582904008001c9007039500030f400040d020f2000000c0316982c80c44100e84130b40c0800b440181003a9440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 336266079 1250 336264829 336264833
    0x42c0a03030e06042f040507090305060907030c05090702030f0706020405240d050c09040f05160c0209010b0d1409010c180602030a0c1103030313110f09190e011107 72
    0x701800a0b40800d000080c0800d091954a030080001d0341014a0140f040da040048aa10001c095035882c0a0000c2d004000d2400c0c408001880201039010946082c4605400306081c01030000302c0c803003100d80081c00c0400741420b003c2088608030001e000003003144403e1008603600c4001900619003a841500c0041e0f84920b45814000c401e043e040800300103040720140400506202412601142c4000000040ca507403202c25180c0c040c00f484071000e40003482c2ca6103800d8400131a0748024002c803205044687d6088000d14201e17010392181c1c0009400c401540b004004140c1800040c1031100000400803c0f802d000403400310f0816800c82d840c00c420707910798007008010380d003001d50007055122030801c07019014100ba4000c0e64a2107049110820003032001c0050040c4025202100300918009040d650b80382040880030421710b03a580810380b4540e07004022134009103050758441d01d0304000500f1440d2580e403203186140604808440400312240c0750141281440e0080c82640300c40360426550648580840c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 336267329 1250 336266079 336266081
    0x8070501021c200f030601031b030e07080303061c06022511041104120206090a080c1219060504020f030609010203071107031a101a1c1a042c0a0303 65
    0x80d11010b42007407404005140460480204c800809010010503540d807580b0004a00030170540e00142c4003401413242c00c461199142c1c12207000c079840c2c1c808480c1296114541ca80c2c5038401941d5942c0d0081d00003444c0038400c8804000c1c81400b5010381001420b00001c3c180e400a060340c68a01c94607095912440713030041003200d810800d04800142d404109802c26001001000e00c03844c0180707034002041c0c10b800001c6684460484d04641c002a040c1c001d00340d61600019a125507003c0d02900c54071035a0641c5441d840c1c00210850500c0042c4c00290b41e040b80c40c0c50b9907004001c040c0043e43c111510541080540d1020002c0c5401041c0b0346000680d030f450219001810001440e803503280c150070411301000031030b00b01da041c01d0302400700d521040e80b580c550a0510045815a610003209140242c9490840b0004140038025a0700320079501030282a16480c00300c129080002401604214045044024102035104803100104101c00d04000c03014250300d8040b00c0300b4080e8601441d44419800c400301641 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 336268579 1250 336267329 336267341
    0x6070c03110706020c130b09041e0818180403020d12060b0a080f06011718190b010302010e10020d1101060906082a100305060f120c1810030f08070501021c 68
    0xd61b004022101128000840626006d00082c185521200201d5440c85070040e48200321548810b1840c1d42e034a40442c040d01840707c40008920841440e501901c80205405009120366415800f52904010740d0000780c904680c4040130341071940c1c1da0308020503843e50520040403112165283c0108615085038101e40c41e0304001c02c403a041200c03904a0b4840c00030000003040e081440c060811039803040d48520700b03142c04214840c141d103000d810304040c07007880f074050b00303a42c10381c1d0007070380c6000c007100c40c400520000a5072141400d005a0000c0103891300a4070490101440c881900004600180d03120003403070039607515400c42505500400c81107075202c1d0b403040791141a00b5000c1c4003854012080c5001607603100c00610300754241501e81001529566031003a0b0341c0400c040c010004503652000c401d050341c2d50b1445220043c040c0c8060b441081130318040a290510928113600034a60303990071503446070044100d000c002ca07141c2005008290001d00280090082c1c3c00115080041d103800c0e03150300b10144c502c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 336269829 1250 336268579 336268609
    0x7060609021806070f0f0b16030c0c031b020907020d031505090f18010501030819230f0c030406081f0506071e060906050610030501050306070c03110706020c 69
    0x8810000c0350407024190442e192150000c56440d52100c406040a140988680b50b0080c4014030f000c080d0800c0101c528030450007245000c0d4040ba1209035001c05a00300c50300401c0900110350055035800c0080c2c0f01c1d9255203070704086150f0100f01c90610343e01060303904c2e1060382d0f145d000d41c00011500c0c03600b90741845242200382c5025104804603140502207624402e020704014400f8241200046040900141c0d14851042900c000c000c41d6075281010100da030003404900310a500c01741c1c0c401c0c3c00c05200744140907040000241b003007d5540004201c607146d81c002c1d420300c14118001d00181403149014005040145500e880724581882e20802003140181070400000d2403021199090007107840c2c10341520a160340c0220a088118041085140b0910054030000c00c0c0c2410240390070104440b03508203501458050300c1c1c0001c00d4203005415026503000b40540c5801d135000d04006107005120303803000d892040c044d042c00e50000600307290081c1044140d03001500580d001d48003100a6040019801410302 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 336271079 1250 336269829 336269831
    0x50f0601140403170a020304080f160b0909070302030a0b0603180f030a0f08190c0903020108090a030e1504050925090819020f0402160501060801061a07031404060507060609 76
    0xe070841d514491002d01360035a45010340c5010130107101d130030f0082045801034516007046179241c4c0380e44000640d441030b85044010b40b195008000094190042080e6820704c0c5000b04055495990b01000b10300a400c010a0011019200c4032050350030744402c0001c500445a0301002d00780c8002800c95185465200c0c03c01e076005600402100d07452590128400b08039070035502d4401170740e440b420000c101c481e07191014541110300d0400102c0e4416004410304040b00c2c800c4c0c07140030035641c0d0000d0890b180c4050f04c030041c0200e1403002100c001031a100a003000d10b0358000d44014206a10340c804130b14039100841c0c0e150548094032006641d01480689100c40c480045e01d01a01d5080c207115506440782501c0803211900800301500c0011991040007596072040c01030803c545500f150a03001607242c0c100041600c0303e51805502242030001801800255071000ea15200c0c1e144c0c045050384990b5000010a0701002014408041a03030680c0005100900850b5507468940900e41030042c00c99400743d100384162 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 336272329 1250 336271079 336271087
    0x305040512070923070f0905100e03060c0c03250c17010b030105160f121802040b060708030c0d1116030807020a030801090e010b04020c030a11010902090109051801050f060114 77
    0x3100e4045400ca5000c00b0606d044d0840c0140b0b41001d903600029508421340c0807803196000303040641d0100c840115848114103c0784240c5540801c12402d106115800b8840d410803c64540410238226024414400302048107046446c01d460311110702800340c0000103881880707604002104400d000b80c1e908041e00301c008021504050140313802020100c0900800d00600707502d080d09050182c43c007562421a4007406101011a41c070005030310f407c00c1c0004071b124a01c0c2148034402410141c0030b440e1401d074000766041c50f41d1140b04002c00540c000d140412500c6032210646030001e0304401c05403036001c0340769181034091055403602510b0400e00a05840455104d014000042035000e541581119800b51001580b0341071743d0340e0503000d084002c000c07903049800051808038145c00003004003400c0c552a9212065041500006400e84114083c0a90b02004c0c040c01445440040e81c0090f41100c8200c0d0810220f04091404a003580e00803551f141e80406001c08008003944c0143d8101520306914940c20300d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 336273579 1250 336272329 336272381
    0x705070e010f03020f12010c0e010f1404090b0d060606050a030e0309010207030206030c0702120a0204060b0c061501030912090e160c060b0d080304051c030e0c0d03050405120709 78
    0x103080c0b584806403041d1148000507215890b510404803600c400c02000703115420a00c840904030074000141140010442c8104903030701403158218070907402500000502d49444c0c41d010001030007070151181d0b03200c00701c415500c0004600e407103000000c20705602c0c3c04d900c400060002508071241d2100800d1290000c1001c0c0c181603030f010440c1020369604442e6507450ba20b850704e100c222070040f820000e40000102e0200d00c03a009002450b21000761017240c1c10310010751140074000e0b0a01031240c1001081d40450302180d49008942c080c0344945c00c0c1132400080e04a15a11a6400c1904803144000461810700d4107101104500035030706d510a00c2030780f000102080340e0000074034800580001a0400340d480354802002e030713211202c001e0200d4010003d0b644904040c20305603240e5a1102c4614128a15400154a4a400303402069940c0c0e100d40c0180900055600501109112030307034080302000f03c204008280c0b40e40340c1030f81c1c40740c40c020800100b1086007081803a0044031105080b071804004100d40e0011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 336274829 1250 336273579 336273599
    0xb04030f031809090302150c04030b011a132403020306030a0803151f09080c0901060c03020f03130303020f0105040206090d031209030f0f08010812090d060f020705070e01 75
    0x20a4681c103240c22a0020225040072034603503540e4001c005020b0034101000d080c1a070000d5140780c3c80040050b886e0341601c82c51a17059491003503202c01442c0c070020f40010400080381500d450052204030700e03028504030781444a6403202c001900509030504810280030b125400c6d4000e086441141ca0074218a14180030000a541d000502c0c1c0041c8164000400124031561b002891304805102400081150044080c078140e00d000c0261002d001072144600000c00d0071001800128a11025004002690808200701c81502421009600b942b0802680b103200140400060000c0c08a090390300a6032800c0d454000e081482e18051006182c2c1400140009a03070383d08101c8120405c01c44050905515518003520f18501032032000f000503241c000e43d0414560003100c40c111044603642c40700d10030704044400741d9440c0740138005d001907580715074000403100000c24020484103030300800e282421805580c81006503003051a250030480d40220ba41410404100090000380264404142196041171a00e039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 336276079 1250 336274829 336274853
    0x1504051012031b050304061103091509190b03100902030f2217040306060905040b16030902060408030c06011203020c010e0d060f0b09070c02130c050405030d0201150b0403 75
    0x710015245202220806006026001c5002903400002d004110a803c049849030841d1080c003022030000100510481408022140036180c01828600164413500c03d41c0760681003140c080780c100f60441d00100b032070b80750030703020074014400c40400355560300e03201488400c0303aa0035034408078140c0e00500c18480100300300100300e0f60003c2130100450000101b040c0c10038540f1040ca1001d0000d10740d088040d444e138031503400180180c80c0940c90601c4240d550380d114004444003150301825500200020802c0e03100003105400b000c4180d07103004103481050350001101a8019844a2003503400000e880d00d200e071040c848a4010b01600c1040317184402240c0f000780d00d510304d07440100d0401a40c0c0fa102440703591a17036845884541c00c01c2c010014150600c08100050042c40c850b58170410480000440c0e05100c0c8080c00c0505501a0840308403000d003d20002c040c24031503c1d89428042d0601c408201a10704014003403c050066002103a620706541c0c07071400017081d039003250a602000b048140702140000b0024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 336277329 1250 336276079 336276089
    0x60e18040809150307080a06050d020918100c022506020d0809150c1c050106090e0a230a0e070501050301030803090f0d0e0a0509010f03020d0f0c03060515040510 71
    0x45035241c00c00b8001500440e40c8001d40769010f400441403040041c3d01041c1c5522500c04044200038150300c80b001c0013001080c2c110b00a6000d084034001503428000c1074407511849102e2403c840b45055144001010f541078049000b005a001f0382007020380310029601080c60b10100041c50042034148a8002d4580141011280900a0070008203090100801c00b078440d41c84500c5041d20b4074207010120001c607a0200d20f40405c03503817900310300707440c194210312505040700d4840d2100c2d4016881e200740c4241c6141c00170170803500140e03940d0300c0c4500b505003100b01642000c0c1d0460079031407500d02001c219046407480751452655a010170341c14440c0381d07042000c40b41566040000e254603541e589450301e25040502d0345150f654003030540b030701c40c4a5030404581c2d48605401c640c852070b490740720010f11503015000d100c2d02d0841c02100e04204003609010b0300060460f030080d58070000c40341d840d84504038004504d5008503107450751002003061400c148004070301000c1c2e0889040c40036051011946d8400c2007a0300072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 336278579 1250 336277329 336277343
    0x50d02120309091006112803020a050a1406090304080303040b04110a080f100b100f050708041206050601170f060a1d1005010906090b0901050d090c060e1804 69
    0xa805140e10003002512600380c0c009060307038898545482006908a95480b0306408200c0049248000c0000802e071124410140382101e200040c038115408280e01c034082044d400d40c090030304070b10b000c617400344040444140070b40d1407541801c6160740610701d8400c000b40551120781007817000340450398001c801c0307a80164001c090010552201c0c00c24400c1c441e044414160710003000c00d00021000d1020076880000094a03054480c080503400211041e982c15540d0280e0100040b110358504600a1003444021143d921b841c50615803269140c9605a201c1c0d0400e900c415040e081d100c00300304546c00b80c5540458203107451240c1d504050740075040030001900e0480350005442c00a00162101084040105502d030800402480031b0058081541419a8090071241c01c4440c0410254055041c001c211032035a42c818030300f1450240c40400540007500d14a04000c4204003e11505009004990455001d803408101c4185001c2010b010721407480d60281c080c440e517881905110b20b5801e8502d41c09030304824 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 336279829 1250 336278579 336278599
    0x303020a0303090c050627040e03040b030a02091302040504110703080414100207061407050703090e0c0d0f0c030c09141e04051807050a0b030a0b030723010e040204050d02 75
    0x190503800b071300c0c480d04156045240420080f005013180d402122001c40c07074900103900c801c000c41c18001503a101b08010089580b041000308140080b0000441d80040d200c0c40050070202d1200c0013a15400c0c016a84092071394010400340001c1c0f40030300c03e074131501c01c0e10360146262040030b9901030130080000b800030301824810036508100e040140b00000749920034910031550b810062400c80c0c01042d2290646400003071a80002d555a0f001d003086520585d0547c8540074128908114920a07080003040c00841d103100b402880801c83e45801040724100c0030700313000b15044040400043c05c442c0c01858a030200030044408110b40d4880801100403d0400e480c04c1c410785410705000e151000341c4921054100303141c0420450702c2440011081c0d80040000700742d640e195074502c20401e080b40d903400f40c8111910104007103030002c405640260200b800181c01e564400740d03240082641b60880451084499880480420080d80c0c0050b000d071030b0980458003181010704000100f41c19400600000f400b404c0320352 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 336281079 1250 336279829 336279833
    0x308010e150f030c0411040305070b030601020a02100c05120a02060f0403050405011116080c01120c0806040b130906020307110a0c060e1c03200c010f05090a0f0f050111070303020a030309 82
    0x2002d85404c180c8081c0c0180001c4d62881498012a80684026a036900410740c01180c07002006003101d01800059009100c029240e8003040780d00d1900c5a2104103001440d105c003000564240441c901c09403d03054a40d0321222090000707414010024118660183c40700100400a40c12400340c5050b12403c1c0f03007581c0383ea44060304aa1510049400350400391985032800201200b0000d49641c140e0b00c282e0b60f60080140400890081d40e80000c42000800e81c8a07000910604141d1311929820400908014800d883c2c0840d03030045816002060b2000d035000002c215085403c01230b51b680351401e0700010300c151489500c4110f080202c90087e0420007a8006c554900c3d541d0b1045001000c00b075040002e00050714614014107a40ba09040131031030404021407920940c00c000c1800c682c0310b0b0301a152000051142c0384101c80704d0740130040301170740007043d41d01c04102a00c0c66605400a080056080c0d60a28104400036002402c0300c021220780b54081c0d0810300000c4c1c1d010400540742641810081580d100718 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 336282329 1250 336281079 336281083
    0x3050309070f090b0a0518061003110c0d08090c0105031b041a090306010501080f0403080403031b020f0601050a2603090d030309030809030901090b0306030106050306040c030308010e150f03 83
    0x168480089002c032140085035800141e400705003160001c5400b5450380f81c1c0c44003444495070304005001555400c9100044c0241410709001e01c00101d286070024882c4181c3c60803410301d80200c0c8007080640e00186d048051f0940102d10b80740c11000440c02480121b00c00d8000820900c40280013400300c60360741d464021600340340d10030798001e0b14a0301c403801d520010041a40e205608450020392080c42044000102c55006020300d0740941f044110010056076252001c0d00c01c060054000c504043d81c96000d246000b42e00413035454500d0695010300b2601c41c0380841c840c603010040e0041031180340c2e004802c00c4011540840c00314401080010920a40700d800c041c1030446c0030300418a50429200000c0b50304041d0f0540c4007401c1d0758880e4071202050b0311500d0b01d2a0b80d0b80a51492640428002d400030702440403150017655000c20010008904075490f10042404c103801031301d0403180f82c41440e6040c01003680144505014000704c2d601104a4640005441d5002081d50800c50140307081ca0b9805ca40c64800b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 336283579 1250 336282329 336282343
    0x50606091e0a08120c06010e01061706010903021507170c06012105010606110609012d0609020403050102120705031b0306060c0d120606020114180f06040503030402040606020d0c03050309 82
    0xc40e20680760b1100c2145414401588011617444843c09044004105043c25150340d41c142c64255880d0606003c07103600710b101080c001342031030f410300c14011000070044c1d8442080c041700c1b0081045294031181c05252a4521603403519694621400c1849805a85a400543d01e811200035401641e4003500321900d03140005a0010054910750911070085100c035000b1403403074400d84144003180d115640d00101c040c00c9941d4105504142d00c0100906260100d21400b064070307403003c030758000903420703941c8500008036405030707004442d180d40104940400c64480c05015500a009050040c914940a152285020a101c00801c210000072000c9051500c0b806c0070703554042489070445440c1026900060502c040040f400028941441c2d000b00e4410300c107000750211044a11005c1c9545e440d084005940c980790315102207981e2046e052101481c030f400b0019980603a0248000c0c6a588c00c20740107000a4990f281c10200640d4402c0000314031840d0b0190482e80e86942514105880c0c0e00e600100508101d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 336284829 1250 336283579 336283589
    0x40309080111040501080115090311010212070b01030201022a13020c032b0207030801050906010c0807030c0b0f040b0703050c1e041805010f060c0c0f09090501050606091e0a 76
    0x2c6009059140864510700800035618240c0f54081560f03640c0d903080218001c0c1c0008800050025401000001e816007010000e42c4014016220b00f9240c0301d106c100c2a030440b10702900c8070701c040b5004005550301440345603044540421034840305070b1a070210142000c604140180205610100d1010381001d65041d54080075403402540d030340300b00b0f0166503641c407202000d901101814400c58000c0c6036000f403084a07001541030b240c0914a038a0801042200d0000402d443d050004006200000031441c20040c10502d01c20303107a0480d8039040d4103102c1703c42c60707000741006004041d02090002203110b065455501240f00d28010540e80d031507450015490144407200301c0c0820001900303a4540c10440044c0c410345580402507100e4920411000081d540c0038403d8810012060070b040c440a44160b044068890103540040e9586503144035076840c0c0000d642c17151140d0341c0c0e12101001000004c1c001c20b6013290003116034504000641b000205030440790042c030005055407008414883c6c0302e180071040208 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 336286079 1250 336284829 336284831
    0xa050c01110f030a0501050306060d03031a041e0e15041e2f090106200a08030703062102060f07020409061814061909060b030706021006050906060d050403090801 71
    0x900000c01c1c582c1d6003080c2e4140c00f8943c05c050001c209814002a61b621815004100110120f80c5481c2070b8000c1c039110120000e100030205a2003180c1d2680d028a01045a51295070100030901034001000c40d80c48100c0705d50036411070800131030ee180300200c031250045d03003000007030400c8101080c0c80706511180c9a4020b01500c1180c003901a200d084801d074540e035188840100d00300d01c0c94102006090319007401000c022407038082d8107250b0001c00a000000c4d1401003801c440001c10f154a0318061070f0000c581540000e500c0d0700081c0a281d003c04100555082038002505542859a000914501131a041c142040c44007103510000e42d40d490300a2080607802900070040501070140480410801040c15116041c0100f055502441c0005456214030117209280c480d040d41d0070a034901030480148299401616410f40c0600c503a4180444d100808041d00180754209070300d02c1d41030945002c0d501140c400e0802c42c0800c841a15001d048940d0881d071103100103400d956514082e10828207503082907045d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 336287329 1250 336286079 336286087
    0x2070b0c010207021e03010c050906190c05060a1b03140f1003020909011401050a0b0403030503060409050105151908061302010311030f040c0b160f1713090c020c060a050c0111 77
    0xd14490712600020f084180c000340a68070300f4800665842c4511102140c2080d42000b0100d11031a440039074558a58852514370a802c0c0c042d1541d610340542a901602107503901c9003030301603d0340b40700c2c0c01040b21a42401d00740405c54900c4060300101e40001d0900180c0c2280030b000610b040c04122910300503540c0104404814148041140d0007800001040410311000c400049060f00c0c081603120f048803003250140c0c1c40e050031070390103c8030f03500090810390304144c5848000c00024400c0c000e8a100c3c00905600080310401c081c10010402a600c402d4403007820866014001e031074002c00c03203030f43c040f01a080e11000c0303443c0351004a000307040016400c62959408020b00c4420441040d130b42d4016802001c150b034140c4d450f80c3c1602030501c50b6102d86241002e102a030400000d003080c90042d0404e014400d02007039600400100007603940030303444500303081c002442c040c17196102a200718a800c01e00b510040004404100104080384590a103030010b2103c046214880074600350020324540c02611041ea0321 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 336288579 1250 336287329 336287359
    0x70203040b1809010506070f060b0a050d080909070e0a0623040b0d11030f07030b1203030a0e100b0a0b0706060f1202040506090f0a09020609100206070212040602070b0c01020702 78
    0x21618000b00c0e664420458100001504e2030b151090740c2d04180c0048801c08120504d070358040040a403a01050b422803202c501c00a5581d554018420406009100c1250784440c402c040250115005104030309100c541c2900c00c00c2a2101000c481c250307000740c01c05c0c6040c28401030369503803140c044120448800e400014081141e454103030241c0b4030601c3e01c29092112031920102444c1740c0c0000c94003a00b5251f800c40c00070305100d1286d0010011440098000c60100c00d0749a030260440d80b00302c600003c010744800c51902d612000300010301e0f003403071b40b40d104001c075800300340c00511714031558880d00036071082c08151042404955030000c4000c041500301c100e40c4965403580d41000200c42e0100b41d205516002c0010305609200e0b1000e4400e104120164113165103124980000300340f020340c1a80c00002c24015a0910340340e0700382003101e5070340742d4000301a40e1030400d000a00d0303d05042d085000d5101d0900c0200982500010114181c540440f807060300c8a05e0416414028040c2d0803010b5400154545078100c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 336289829 1250 336288579 336288607
    0x40b011704140f0a0b06011209020306070801050a0506030412050a020f16150219240204090609051012060c1106070309060e0c060910030908031014120312070203040b 73
    0x781c40ca1500035030324607500680f003150316071213152030241c01e901c000700c000384440d8410081401418040d01002549403050b8000c6403030660b046070070102154443c001801a490f11a00702030041204603085481d501d042e84d242011401e4130741000c0300384000800d100318028002c5c410741d42602c02c0306003101c58281d0031081c0700003000101e214641b00c0c00c40341045601c40510200e80c6000d5032020110101d01310403e076682c00c454407409800420f03c0c907030320000e00303d0f1407a55000503c01041446030214100d420190100202c0b00060004041803020700010464a464010b001a019811000020b102c055202d0103450b40303509414800c64034003651042110707690709a409012500d008010401041a0101000369545640007026902c550700f0710015403540343c500c1c0000980e1396140740214200c55a5520300c0c2454000340c03010040159036400501140541c4415002c1c01c080484410a090008c0500b841c0c6a10031160001c101800c1c4200080b0810300030421035004040080c49030703070360305141501c5c24 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 336291079 1250 336289829 336289853
    0x50c04080c0f120f03220e1302030102130b04080c0105070302060a05130807060e0c090c1209030c06011d07090e0105060706060b1b0f0601030803270723120c040b011704 74
    0x110850400554160703080606810011341f00024001403072034a44010b102c1c940e6119110880c2c0c159020083c0b14900f048002000004011910625488500303241c442420b0440c0441d00f1810070400307200315800701c0e50004401e90040200c050005071354655442840102a202002415038800040c000040044503444402042160820750b412851003038204040c2280c01c0c0c034100340030801400018005911007000e69000301052089900d40a03420035036508040090307010202d202d0170b00320158000c504282441d50310480500c0e000178450f003400007031501d881040c011746000d41404240203080000c1c4d6071000c809440010402d40d1500070100051120f2004ac1040c920301e40583c9203112908080040d0140c10f0301d41c840ca14038207503503074401e80980001d040042c2083c001d19038038211280d40001d10045015120400800d0318600041099425201402420f10301418505607009242e44001c520158054011280441c04445910040301d010056040c0c002106c0c0456090008100440c80c203a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 336292329 1250 336291079 336291097
    0x60f0405041a13020a020c0a1e150f030c11011d01060503030301180c02160605190c02030c01230c10061208030a09080d0e10050c04080c0f120f03 64
    0x38400105915410104220b4180055030440d0003120650240841600030744400c0000384120707200042c0c0708000611b07400e082e40c08400401d4a00500005240c4580405005000b2000315404400602c003001440304141210303140801d03a42d802e0025040e44100c41c9151070540c448009c2c49540c481409204807141190b007103c0b519860100b0008041c24048180da040710810100b5030049404a04003a0180c42016903810860141c00240c0d81104060019000580034990311181c40700d220440d01c0c842c940c01705581e00c0034400100a10070040c2e81c00520411200c1082ca401940c2c0f0884201c1c501d501d054001c100703154004086001450708100107900d0b0016001d240e402d05c0f6007941c406100b0080307542c0e0240500b122004200080e11405150441d06031503105500942c03403c010441c0c18011101d00c2d59440307541350022003a00e04900d90b107004040d084452000400c0c1340c585440031080c3d941803014a194059103245445489999030000805000844102519200f60504500742d03104d610580c0e41c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 336293579 1250 336292329 336292331
    0x1206180d020111042c040b090c0a050f040905030c0f150c07030507060c090e2d06010c1b0801021303050706030203040c12021518120f0606060d020702060f040504 71
    0x28190294414080e0f070070001a03102c551880c00b81030083c40328481c0071a402010f000d410300707104070028860100303126110b603019007039079403081c01c00c65161428002039402103441100040420720155403540007400040d10200d0700015130b400c06160040c110b000f81c50070307921035025000c000c0110076400b2401c040310001d000c0b00c0325425170398140700c00a24010100043c0000f20180b081000044a0303900c0440c4042440c240700e046655a0b0a6200841d01c0c1110110f003100c5120f452810402039294000034440c44a20410500346810000240320102e04076024201c030b6401c00d403103490702c0311900783d10018202c0c00000390b54508602c0c070240310002c10351104841e10701c503840b400612b0714468800c0ea40956449444540503600c0c0030406120b0012503001680d01950001860002c0d002c030b50018031543e000c14440382c0000c0ca0079820000003040d4403a2800094225205494078500c01044850f4031110071564144c444542e400c0c01d400074003889100075000040016040d25405e02c102c043e100f114001c5030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 336294829 1250 336293579 336293593
    0x10605190e0f01151107051e0f040e060a0f1b020102040609090c051e160b09070801090506010302280609150309050a0209131704050405100303080402010e120618 71
    0x184051144400d2003a1340420718008110002c843c41010b15802d416114400ca4030300750303200c1d0005480001211024500c2203c6000c807404207003444010000401300441e41005102141080591184402040380780318969a182d079410340510380d070000544140c1c81d90300f6504620b0455002e070003980103000d10000b084000300b0000b401c400502031701c0d61110f401e0360741ca0704000450840400c0d51621440c004035502c018810000501e2014440204460068080404905020986d60704001d042d412074601c59047c584d259002c01c0d40002c1d018112941515405040e003403d005403582d407081030200341e06807170506500240840d407081c0150250b030322541500070020384512054044a1a524008100d9002503c001015140c102c0d24640c1c448900d8a120000303480ca40d40320006941005421800780c40041418080750a080c4500c41d07110a0380c50b241940c050441d01d02170f10403071000f0002810408900c0700c880e180d4480d1300b64110044242d808980b21410001e050902081c02c8a0321100c191052007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 336296079 1250 336294829 336294841
    0x2090102070f150302030c0d0f0906241502070b03090601030201031a0315070509060a05071e0515060103140103060e0606011e030f0209100203070b060a051003020c010605190e 77
    0x404040480f0741844512003a2840ca440070703000307504010004807001c0b0040c444141c5e110300d103010f03078440300b041d141001031100c45901c0c00001712008010300c50b240101c030014601c884682c5d07030400b8050351000d46241282c181c445c00101c0c903044c05904214407844010061100b403c5002400303d060f02e00c00d03282400440f02543c20703402041d00c0305000a600d58440c16000d140d14071400d81c8290820042d00e080d901d48440700000ca03200d45c1c0180c03030482c0007503400120a0280400d04042050905150081d10000c0f09030380c82c0d0541d1486003403031101108204a000c1281ea0b80650701c80405014103045010841d030752402d108008081c9040000307620300507280010800d6120b070650704090801c09103194903417006004100c00034500f401e905286698200054100340d039881c52410000d001c564015546e605882c81c0c032001c0d003840580755900508024005000c0c0303650f00207811020342c00314500141c45952803600180984080d40c0000d41080b003400e11401307000c0e10303031000c141503c4200e030704514191501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 336297329 1250 336296079 336296099
    0x90204090c090e010b0603070503060a0510121508030f1305040510080c03010e0303180f120c0d05040302060306060901030f051005040b1c020f0613180c030203090606011107180209010207 82
    0x5d409510b0b4010401c1002640341402540916000540074080c1e0038911749850200c2d61410301d14001e480860112002c0c070b14101d0f00341c0030701c00240313a05400140342c491500c40904d03528040c4503036841c410320b00800c0080d020110b000c0400001c00000304148030314105a4058440c02a560003844401d0060f58840d2400341014051308141c450716178011482c2d0742e1901041012040c401d0800c920038001d1550180381c61740c08028400c200140560242c2c0d03140c500741500da2074200e08000000c00e20009000030409603542c0001e403a88030790140c992540d2450000d0040340140f011100302c095903441d110900c142000c0c05003054040da60700341ca0800c1030350384000c100503110206007100e80e008200e480d81e046c014100f01c2402548100e01038000781c00c2503411820540040c80640100304009890084d00b888104580128602107000b030904500c0c40c20068182134448200030710250503c4002040380384002070070847c21004201c07545c2e01e4200c42e000b000c00d4070080c1d44003074a10b500600c1014408513080000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 336298579 1250 336297329 336297341
    0xb040203060a14060c01020d140f010b030a1a030d0305010305010b0109030507210b07021b0a0b0d050c040f0e060f0418110d1e0b0c0a140d090204090c090e01 69
    0x8018040c11500c1d01d4000300f40307412500086081e420440501c403410034164240050b00302c03100706074004110091218100c400c20b4000030650080d14285900412807440c00104680c3c000100700d030042a00304202460440e160a018110340c1c25108040340006804da1503409503050303d10a000074401140310b00011501e001c1030b4000a4042d400044082000c14020303e83c105a9000c42454400c15465039118607440f5007044403000c02503000080000540f2880c2c0042c01e107265012a108585141404101100ca01072003503621386a5a0369008511450083c405031001000c0d5120148117050700c0c0e91050f400e940d01695014002c1680d000a1001c9183c980540c1340002d500001c81c0310030024540310100c0d81c00224100d00c1e044581c112004000c0b82c034032000c2e0110505140c2100e194201c85240c0881c1c0d40200804000800c1c170107010b24021b070355011012814508650100c81c1d107551461542c600140452003009501501c2c14030346408201284a90301c04490302000e0811900b09584501030a0700c034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 336299829 1250 336298579 336298591
    0x309050f010522090203090303010f06050712030c0c230106080102090127080a0b06030d030e070612020c01060e061c081c022106100c021c2f040b040203 67
    0x20007401686403c030b04401d426070741c0000c1141c01100281c1e071040725070308a80c8182c2d50040710341c000000501030401c0d070118400060401e0f19203540f0f40142d030340324440ca14a0b10200081010303100c803414100540f01c2e070088100039401410280c13001915128030350050300a0b50003000c00394200303203000a020b00b0620aa41c100601038588036142d8080c084090001e100000c0405044440100d0104919a08202a14000d441806501c2c21410018201840c001c4c02d081610201402c02500d51021000420380804603201820450440d95540211340f020f4024103caa04003981703041000a01d003400c00540d240203e13015504a6808826000700048101426102400c6690704000e00400c550121011078a503c2280f0382c010300303000e0b10355104c010042002403c006156140001d0284034640b10004481000381810700151100c00c40e400b10300c0309200d8812200150a11603c0a800d00254900b804400d0104140d911104208001c2c81711002a440c104140101c0ca00540f60500e42400d01c2100c1c0111 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 336301079 1250 336299829 336299837
    0x80c010509060a11070b0f03070306091b0f020f10150b0403031d13050f0109060506211003050d0207090c0305070e0d02010216090b040e06060d030f0903120c0309050f01 74
    0x4400420f59040d004c0300a030001e00e00c0f4024000a014607800c016008280301840115600d082001d0000c0503509540c1003000940d150054401102d402d90201c404c0b015094104209406182841a81000054040f04100e8054441a0f10700840c2c0350784950101001c21507030111003034551110f0813160103140402008110f030310384180a034940100071040505002084103944042041d28103041c2d4105541c0b0000d07101f04400103004d04151401041c0103030006484041c1000c3c1c0400c00d14540706589403c000d840313074500001c20708418039120064003079a005011682060364850740290384840314450030700054641f05545223003a01c42c3c01a070380100201d66441d41c4003000c0c0820040d2182041d5000c03410b6100b048191348900d03049900440060a80c0c02c0d0004144030000207000681c0c0c104000da0800350800400c000c2d003903440100c4041001e405141c0001d984000405c107032401106a0000b4041d0050910031942d406e41c0020340d007142c01c0c03080e0340d0207020380c2e85d44d800d00c807410640841c554041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 336302329 1250 336301079 336301087
    0x5150901060828020901080615070308040809040216031b20220b0102100c0c0b09101a030f0a03201005070f08161b060b030610080c01050906 62
    0x951080b800107400ca4400002e50b00c0a000c500030082c85030442582008415801090284581da0000c061680c0103909607032240706461404200a000d1054200040500880201003401d102d410700a603041c44d080540115a10800d03440a680321400c07400084001490341c0403c0d850303524202d06d0140300030390301034488480340d20359002c006c2082400c601a190820440800021030042152449084012010340066100c007250b0009003007091045080c00d110b820b00e0340c1e80c6480b960100c00380c0c074599002440c9031520b440e00c0001600f00306208550004143c01c240002414815289421408274400c5003100d03503c80070035020f10340303688111002030b010425502298007c011245c1c106d26011000c4000ea4120011024030402250f0701594a00d00003903802d001c2400694002d049984c0203000100383c4803603404001c6000340ba00030340352000c0d5480080c0515400070058150054508501e008055030700500e41450324515071019482000300b1846605407801d000d5000720201d4002e5800640820301d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 336303579 1250 336302329 336302339
    0xe0316210528030b0405011e0f142407150506030a02030607030b0a05090124020712110a0503060708090c06090108060d050c030601090618020c031204032a0605150901 73
    0x1040d010b8508105164440ca82141d560340c8a01c80c40e400303001c1540b11071030b0442d032115050f400d0907103e030414050068201003d00c4081641902030303d49000440c0c54603004500210904a600c001051080c035680300030548004001d10080c2c0c440303000d43d01c002c04000c2559400209036a65110460182d010b40180020840c914820b40110350b046001130600b030071442d070301d81c04548588401da200c5500d00454640340e0003d0311030b0400e51000300540348000d2120f00d0400c0d00c482c002e0616040001e00c00d0120f40c44110aa8a65000c84401031200a00b80ea60620b8034450203001742c0c0d0126a01c2000d4090050040e6007440e0460035101001d106030355a06090303680b00184100080b10120030346003032044030f03e000c0c119901085828003070030200c400461450300c0c02061900003502691a10826401440280c000c10400800c3e246500310800900c9034648031801c2c103a903480171958610658aa6407080a010422008030402c1e280b0320980080149554841034411181355050305a40e01180c40c4004000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 336304829 1250 336303579 336303637
    0x15070507181e050402040e0d030203040b060604060f0c05010603171c02030106090b0c010f110d0e06012d0803041707093305031e0c0a0e0a0e03162105 66
    0x1501600c05400041c4e0b05140b100d5003448c207128402d003000002d0300041003100f000f010300302607500090240c1c2c0c4281098100403015080700300b403250880c20000c00e90211001d01c40b013504a60010750f084104078268110418003141641d0124558400400b000074005511040504c210390480c2c81c01d68606a9560405242c00241d03481892401d110713640b10001c81c0400c02c1c00d031281940c510028040c2c1a83c43d00c000040c40261103e2007000038964012030010000241c0c4c80071024400f01240082d40c1c4200c907043c050800c0844617030030182032440045408240500403d00145001800f40c0c210740800d503481d4090019181c00048040030b18040e0000c100700e14021010703000281e80484490b041d1076403aa0027091074074902074406003110505a102084041e82840503940c2c52700140d0308005040c1c10001c0d11115640c0240001b0b05066880940b01c1e11040b090068985054000b02d42e000b1034203a43c10524607081d0b0395070b5501c64103d461306864114a02407000c488081d840d840198941d0310810040c1c3e5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 336306079 1250 336304829 336304831
    0x40218100b07020a05060c071d0601081503033f010b0406050f0d110403020a0b070f120905030601030609050607080424060518040c05010e090a0b15070507181e05 71
    0x1341c0003813443d10f001c110355030741c000a4000295203100814190b407501d9510850551240c034a1000721000805101e03007640e101c00d00d542c1c400340c21105002481004004a0700e544200103040c0b201908802c3e510340c0180a81c4c184072640c10074200c411224003d01080e01341c01d50401c2c0300310f0140042c00c004c00c108441c0540c0217008200c20041030281881001c952690960382c0b04c0c40d055a13007920000741403046140070080c01d03010342011503210b420a00c00399251541c0e06106040501500c0240364180c00c1c03144201620005008080d00342d41d403a503501e281040103031241e40350484080c000c1c800003420301441064038511443d00b0124800070b00d1644506600f035101144082c15038141c96031004645519462100e84031829408486817041c0340134200100c88075050b400150421842c800105803640d41c01e07600581207042d4082c0050b2000d2903100090340d041c9404810170011038080b91500910102280e01e2003110f0142e000400341c107150410700320894119002c2c00d10f085034403d040c40c942e4043d540c400307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 336307329 1250 336306079 336306083
    0x9020309060f07170627090109060f1a010e0301020c0d0302130603050c0a080a060b070f02100e130b0d02030607020f010506012f0f1915090c06050d1112040218100b07 73
    0x200c005080640707149240e0301b080711001c905a44440944040103200d00c9044c4045511410400c01d04115100304448408080394060403c143d14402060b00d550a6040b9034101158200310f039414000c070f50b03028000e508080302c1d0369006a0024030008029000340142c611480341404401c3c5040c49041d415140d02002030032800360a580c8000c0811040c0d9010020070f0070038000c041c41021011944104440c007030309c000c2c0d0b0030100321480c1c245002c4c0b6100d200000c128441d5071240491205010004a840310750001c070080c0d41441480c00744000560045424641507030401c00078000c03580c0d9500107450804c5c040d08005180c0307904458161701c2000c5101c80c079500c64100000e940000c031503810800e02d00703000280c0c13940860900000c1481006414000503c40c2c403003000d000d01901129844c4d030800d420300351061605200b07000403001d0383d03906035030b01011040796a100a00c0c0c41d551035000303148541108813801c0740180680100ca480710609084500e00c04c2c03004c428860000c40c24901503103081c1e0401042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 336308579 1250 336307329 336307369
    0x5010522030308041506180f1806150906060206040f03020f060a27050a030503070c060608030702010e120601151103040e090d0c08030a02070c09020309060f071706 72
    0xc0e014580c45105409000703600965410445050a0400860285241405c801250301c0c1950402c1080c10954004490403944040041c140100700720441c041c1807082c01c0030910010781ca58143c200451640098940e800c0e004000442c191208081800c40d09140210340142c1c0c86040020001481e038401d000f07c041c82803060784d45680c4420461403410701d0580f98500c18a4407a001040d60601c44980c00344120b0f03580c680401c4001c5161075003502c1d03041c4040040c007000800000580d8041c0074403043c9200d40da01c09170801c410f960328014a03031030b41c1211904038005000803809001d103180494140c142c510419000d00581e91a000c0c0b5140b14403c83d5800d00c050104420820144000030b1014100405442010010764548860102d00302201c0c03a47c403005000f00c1a42a0000c40d000e41d0541c0d5010705000401695070115081001e030020301c507880001c02d01d00010400410601c0030945901489a125109909455006084c0da20b500b00441000658541400003880b0746000d9001c416580d0315428 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 336309829 1250 336308579 336308617
    0x50108280b0a02090405071e09060509091e010f031e11040c1e08090105060612070f120c030c02070e090316080d0e0715080708150310150618030c050105 67
    0x440c0541d0401c403080f00210703445103448c8a1248003498910040626031811a140074142034025110b40200f0704124000c5180000027a148201c10912030b400311060740c11020290382d206100380e1480b006003c00c645845400e4038a074464000031038000c9800d54010002111204080103000041c00302070900c02c01c001310b07040d052003040400c15140070750b540f199032807000c149006a1102e00356030001d08100d005400c2003280303103d280c801c9004260130610303a1900100c0414070781c2e0200c80321245d810b40c500ba52881c1c80d4103d002a030b0075070700c20381e00c14049400343e6691a64580280410407404c0781c069820703400400c015881c4100d840d0b81798200174410400242001c0c0c14140c940e00b141d5050f4030079009a8081d8800384510b0080d50000440178540745046041d80c40c1c509801004200c000e0090380000b44107924000ca596010b1021514045c61030b2020000e010400c1100d18040d021446204041150005100d0110154070080000e0340d0f04803140c040c0302ca150030700444480d401051402c8801e50110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 336311079 1250 336309829 336309847
    0x10501031505150d06080c0d0f0302010b060f040627060c081c14090c010905041802040e0303061203190f1107030f110402130e0901140a050108280b0a02 67
    0x461040f070301c0006400f1600c0b01c2c511544041140c100d40c0000b92141c0c010f503031020071755852441c0b0010035039000d40c1d090446135062a06902415110b0081c5600c40380104040c08005440c601400071110700d42c1d154501200700f00725100555820440001d142d603044641804558060707040880914880e0b203640d442c02102d183c070710020401d84150501142d440d82c0507416503030480c101283d00840c01c04043c10120b00320000107441c01940303104041c09252240ca060081c080440e415800140d0060024824960b118050382d07102d500456205119191500c44042e20050010540e1040d201e500c2800368110380030f20041c0e413030300482e00300325003040302d2514000306032201032083c00011032140c205a10301d1400b518045200404600c441406103105101180aa08c1100405401c9038a800021003140e11010b007020301400d901c56045911342e00d0002802401000f680c0324078121400380059884510f080c14514450200c80d1a14100c50b60501e200f42000c83d000010031a04240712680045c81d01d00700e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 336312329 1250 336311079 336311089
    0x20127090e0f06010602031c0c0c060c0801290304110f0a060302040306050a05060d11010513030c0e070c0308070e0a0e1504050901050108070306110d0608061801060e010501031505 79
    0x4400d11110394008048544a04108000040c05060a0b00207141010b01421301101c8d90f482d055644003005468003c00560300b801800c0310f00c03010307402010a02500d0101c20303010b450303070900784030b1028050208600f41035122152548400810300742d9420503d141c0300c0340c43e4610b034144d80c0010190b001601402400d030319511459194024201e9071000758842c0c0c42c40c1800000c45400808291113a400c010810120ba500d0120350564298400e00c100c0e080450200102d8031401400b00901c000d0014002c080203001c00c2c52802411208903640004c0c043e521400d0460342d0178100c1400901141500d03000c41e00c464064018000c50310380c050071010202e40c0c0d8810711881c40d0b10070780e441e40203525008820081400d11707000303080d03201031008006c3c8002d514040c0526621300241c8000380081d0b40e0343c800380c1c03804038072402280c2c04000d032a0b03010b20110f03403610f40241d140c3d50300307681c416003a503030410391001c080301c06016840c200c1d68800031000044e860320f00150040c058601101e0704c285200365011665507a1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 336313579 1250 336312329 336312341
    0x301060207150e0a0302121f090b0a0b0d170c0601090606032d0b04090807060209011d090f091c05250c050103020723030a0e090402012709 61
    0x85503004020051030800d1031490402d07007041090400244420b600389070385401c0000350480c1da054902c0d0800c4641d4800b050306094002170550901d80c03190b816100e170348a03d0f0300f01d1540a4040d9010148688a60082d4012a00c100c0f505540180780c805681000ca50b242e003100300320503112166140707010440e0214a0602c4401d8201d480300c95501d4109102c0140d0600c00c004011072005907140ea851004030b498008000130003400140b003a00c42442c0c6c038280c1c0307440d0030480e12580c2c03281c200798403a2014941132010350418600701e8006010035058501413110109032170240b2030b000e0640c80b01038403013186001c21210020146c000ca032041c110100301a07022404107100d20400760b07a509071203a402c1544400401d00c0b0350324a518207182098001c02052440201d041141c801342001641c03001c45241850a40c54104105d0074100304005544082c901c0100c000c1c107601040d603644094113903040080040c0240180d8001e40001c10070f40c0d800c14510486011118142010305d060301c0a2a5038242c10306c1076883d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 336314829 1250 336313579 336313589
    0x70533070813060e0907080117010f0204080a050613080a081506130302010e030a08270907050a031503080d1d0d0507020306100e040807081306051206310e030301 71
    0x200001040100f581d10070110400d01108072401244e07030a020f00e000702401018022a9003ea560b4100740685640c25407200c035620880f400117540341ca640381d5160342c80d20178410080e66103004103800603804604001c03102c410b45078000c40c0c0707a00348484200100e47d5004001c140d20310040034100b4518842e640c04000d00500c0301900400c40642d400c0d0710004081103c0c90240314003075031004aa840000c0c01d900c080d540d00c00c5440340140e2801c694038010322111881d4402a42d0410454000c0c09400b9034000e000b0b1109001c2c5403018032004038641100841850343d844054409402804541940d2506400003008010040c00700010541c24240032810000f6008209010400c0000e8420031030500b8013050f680901c8984070b0400701807622440c01408071000300010f28a0f50001104410820350340291460130b44880000d00000e512440302030442d80c400d0802d5100100e009000680e903140060f01405461b003020526040c20406c0702031280007404062100b0341103911569196600c40c01080a58001d00f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 336316079 1250 336314829 336314857
    0x41a16021c05010e010506010c060908120717101401050d15060e0111010902090c1b01060b0309100501050a0b0705070e0f0f01240c03030f05070201020c0705330708 72
    0xc42c1c0703403403401c682004080b090943d04003000c00070103a8100e00c0e400030b0503130003800c04160500546000784072445003022810b01c803070300242841640d5511507115494030006041400480d11181e160395204003591040b1100140100200c0045520810140010480c0c01c2c0300030500b072002c44840c03810010b031078009400103102e21210403400d60f44001d00328005000800200700d592507035000300309041c80040c0500601400001c0401702c8d800301001f40042c01c2010002080031607140c14496600d9801520407640c5032294103510400200140300312412034500400141e0707420310b03291180e0040e400441c01518180207030302d0006071452003002c41c0c034801d1a4090454080386010141d2004d14003040e0884150294030305000d01905044115660030a0f450b41482c096059040c9800c80c0500340007400d540a1604010034044141c0e01500038124810700c010696003881c0d12242400f9071f420051001d640460684002c9613140021039110000340400440d010380703402481e441d548101c2d03000700c808100007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 336317329 1250 336316079 336316129
    0x1109041a030d080609010e07021213060908160e060105040503060c03010611070f0b0306120f07030c150905100c0c06082a0d0b1c0b0f0903041a1602 65
    0x620302448000182c02c0c2d14100310030b450810901040c9100c5050140500c0703c01c010300402d80e601d000700003030141108113680c502d646400507205000754102c240714980200e09403000200b00407a010569980003038945040303c410f070b07181c200c03140340c040d0014003d035050150400010546032414011244034903c1610342503584c1d4540440280031107000030464043d60045070080c0001c5418114590485040320401ca07140d8807510005500d501c110004030341075108000161280c40c001042c2c0c6001c03a8002c0360120429542ea10100d02120b08903ca410005492070406210741d01e40100c0e803111000c0f0030b140013022a152583c44039000c1e455078001401045c0e4103401c00950083c490000000703440c0130000c04591840150b03802c00349001e6000401310b09602ca85c00c0040503211242a1011001d03040d002e00c41d55480d6040010003000199959100c00c800400052008000001210101c0d85280e125542c540c0544511680540000800c55411451465040007594400c88400c0351100b000c0c04031040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 336318579 1250 336317329 336317381
    0x30412230f090a082a0f040207050607110106051507050106030b1311042007050a0636020609060c011e0212090d0503160e040c02070e1b070303110904 66
    0x29010603446810650305c2100c01003040710119092103080528000b001400ca983d60700024403003511190f10300d400034404281e80d0140000007605900a5109449040c0480501f02401d07090307807094020945c0141c842c811030003001040000600c6103901075400002c00c2e607181d5903003480844043c0c0f008070326201d4010b02081884140d01004083c22021102040442402022001c540144d000c0f102041007000ca0070000b88503090000002c219448101004900c2c80388144840c0b480240c0a04e40044403172084401d0455070304207108001c81e030001d214034240010001007002c180d204e840744924075500c40400500d03010105100c0001401802c0e00944c07030f01c541c40e0100f0302c0c2d40801000c40e219684005407200000b41c00104a81c4c20003a410800034603a00030480075201c03400d8800038150464503003c0720b001156408074081e0161452403031080001d4852039150045080c540f050022403620401241001a0095011403584c00080c50700c0c900741090840000c00300e90b000c0080508500010b01c000704 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 336319829 1250 336318579 336318589
    0x60a080106080c1201050f06220612140112080403060e0309011103090d02040b030a0f0c0302120d02060c0306040e0a0b0a060b040f0e06150c030915030412230f09 71
    0x1500000000c10203091041e20a803413882201e040c41a2030254040c15903503c0aa11360408840090f604601c4040414184440070659088540710f01400a4001d00009024202c0b03130041e43d0f400b5013650f5165195902b031070764515a5400b8400e0407034038150100000000606240200208400f145000c0c42e16102000c0c000340a0902e00302e603501581e0010418151160b580f60605c00d039950301074a000a0322295000880d01e0003c83c284058000001040c00c0801c1200840421041d24030a45201000b03610f00d80e41c913a83c54000d2485200036070040c5e030000c0d440d001c0980183d640414006c0010411034201a02c00b0b08100c41004107880082c20031041000958080c09804c00401c648200c0c140740a2a12503200303501030081c0913209042d148040443c01a40d500480103001c0d40c80400196540d8454a2103256240e010310328003802110040005000e81d035a0700182c901c25500407c403050204400c1c0e80403100107015602c40c000080140001100d200c02c0180580658800c0801669a1b2040101003103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 336321079 1250 336319829 336319831
    0xb0a1b090317161403040b0d2004050109122d020f0906100c080f13170a020d080702011101020c10050c07030c0305030a0f09030302040e0a0605090c18060a08010608 72
    0x4440b100b042007070070083c0010181a00341d00ea045508003445600d84c06640741503100d154071405100001003040388007181154080504001803d1419441a21f590580c1300640994402c950209413011800c2105015100340b1024540c03140002c0c1c0000c200d0300604a070b5000c400d004c105214041050100f0440c1044201c0e1510700d10112600d140500e0700000040d400c003203260001c2c00304503540e081901007100b6a0142e4a030100200149a104e1402e40c140020141365841410510510905001c051407400300380e81c141716802030011011082c554885507265840018100d04100300303242e464841135400e101600d12000072101030301e441411800035000761040541039114842003004181e000035041030f0b003e040d040c1d00d400c00039142cfc0d0780d8040e17100081850300e01a440090500c060002010f5059004009407541c0a1804c8503c2e214160200200e55a1b8000d46070440846808031b41c0031581403024024001103c10030040c1510030b41c020540e0354009640b0314010408a500500c80d03290080f10306 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 336322329 1250 336321079 336321113
    0x5060c1b010504081c15060816030608210d051f08070e2e06170108061e1302120601090e0a050307061d030a1205090102040605070b0a1b0903 62
    0x3804107043c2074903074404600c108901c00c0c052042000301185602c58540040004006140c1003610080c0e13544005071450b5011500c0a020503240355502c4400f600071b10400095400c1403001b0195910716030682805c1c01544a4001c030160000c0c048216100060300415110710134291034215451460001c2d0056149aa007040100f5089148280034484001704a558009420840d46201c503d032801d968603118500c0481c00d124452010b004240c0c1600070400c2d007881c80810f4407140541c3ea072032000310744030401039038030004040100c60243d00400c83c40c1c1c0056040b0f040ea0b0354400d89011981d000a04050090100e02542d400200c01003041001a118040002080102501152005594480c1c580c842d0010013410a40c1c1e6607070003200c0e03507030f2120002030104281d02280c0d9a610010000f41242040b030420741201c3d42000c00080852030706000343d0301182c1d815122281000c0c696561f07504144802081c00c000c9030790f1b4403155502c1c4102103c030f03502a00d1031503c44589032411800e201101c02c0004201c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 336323579 1250 336322329 336322331
    0xd03200d0306140f0f0f060c06091014070305070216090608010c020114013008070c0515120903070501150f0f0b040302010c050f07080708060f01060f1b05060c1b01 72
    0xa030300314a4803060314000c0302c038130211a811440310441c80000c0c40d0748002c0c91015000702c4085048501104001091405030005038200c84486000300c3d0882e0940f0030300b001000700060420042102c480c000e80296410003a28010340e07001d508003201072416104c80c1d0384559041ea0301c601b8104001d801c00c0c0316144001e08907100070b11078240b42c014020b800035018411110360740d4003007500511442c0c1e0420081c408144041c4403841c51181ca061412003504903103415182903e890900203414035004183e2214051031884480c00c1001c21812201900b40051640110b8003080100d14000395007840f0300710307200c1545841e146416084c41420015030020350400e000680d1004818884410b07540305445c1129030901c0d10340ea00e030f403e62074040d04081040801081500c1110b1b00440c4604001c242541650742807021142d4a139030b40060a16005020320555021036200c080310700d4800e01c220000030702c00c110f087c1000221705c4560340700c620349842295814401e0a001c01d84404080524014042d030050201c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 336324829 1250 336323579 336323609
    0x51002031b01020c190c09020a0c020f0405060306070e041506020708070b030717060d02210c0d0b011a04080607090e070c121808030408030a030e07030b04020d03200d0306 75
    0x1184d550361020900f036a00c091610181c614200150807030044050210301c4804d64485da4030080203440ba542e011000c138420281881d540500c4d080030302c90b552203190002e00400080e1540d039410340b114802c2100c9103411540310811120441c01041030399005140550040280c14a0984054100b100c81d40003a4400501042401083d583c0f014551041024440117030f110742d11a940010108050942c1c025005078049844802d9070340c0303c035001980040c0070425120142484c81c100a070b1049207503c0205074030301c0140103105d194401004806103040d81110b0310720385903e03002003910300403040350107100080441000380042c42000c8071081c1c00042c6d6003003007803d5a0080c1d541030289070942d02071104011881e11410b102d0080009004028444401981d91301c03500c928285d5200e07400401500042801e00b003402d0300e41000050031404694110500001c40d49403070303007000240b0400070800e808100788222107003401004894210700808000008000040b5010006802e40d18039034017500110700343c88 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 336326079 1250 336324829 336324847
    0x4151415010302130e10150903080f0706230912030112200607050606190305031905091e01022a01030e01090c030c030318150315051002031b0102 64
    0x500c8140c4040007401c2c056100d16013071310804901c00040c0d1001d0030002d042d0040c032200604502101040e294030005048001c80100c8080c4c40320300e1103200c020260181040140740501c080d1016201c00c1c1e110b120045044042e1500300611290389140f540803000d0420b00340701a00320704100c0b840d80303254031a8025085600d800c050b1504040b21303c0300a030510700c8911040c1542c0d410a245000c0784040189000c0d2139443c1c60404542da17807000c49240340a418141d84a0702544009034100003140d900030001c44c070b0060880c010700d614540780480c00b420b04c074040c84400341c0e507607942c032500a040c00b004100d142d03d83c1c0c2010009192644003102540c1c02d02c580006101507142e411400340424200313080114540940707207622401400741080c0a00b1003a54a180030017082182107076141200c0c081d903160818045101d01e01c000141141c40303051507043e900d1810104840c000c1e000b4030a96060300080ca43ca1981d1000030401c0407103082007000050300b0014054010214010a40300500c82900085061a07081b03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 336327329 1250 336326079 336326101
    0x30821040b04060506010309081911010b0f060708070f0f11010807090501140409060b030f0c041d0a0219030204081603020d02151b0a0c06020a0203070302091b03041514 74
    0x81d1001c2c0003d900c59000a00350790094125030344841c4d101c0c400e9603039010681210803010309084c3c84040002c1c60759058002d6000305011341c0300c0540006000e402c941001c02c003005456449900c0454030702c101440042c0225811928002c0424000c21040b02d20710751030702e0840d1522641c0032074513040c402d100d17080c45501680041140c096035001c2c00c0c4003040c0c4403d03212400041c0210b034041e00300c07603041c40360104403200b110000d1409284203000c4918a5126001c026607140164002c1c1d001d42e00c961214150081c051017031441d04003142010051809401e02848040e042d003885407540800d40000d0704001200702044880040628075540942050642d4001164200c0024000e40301d0219168080f1003030501500b201d0300c0d950480d030101010032a03c08515183c2002d8107040d9044181c54000043c11400440d0001ca4554001e003d010440d06580c20020004400f9140407004003410082800c030a00c0d0304010340c0102d004202c410344814451070000184c6110100c040001c00600c41402100041c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 336328579 1250 336327329 336327331
    0x40515130605161211071e060605060f0d05070e1905010801050103060e15010519180f0602102d050105041a09070c2105030601091a0a1413030821040b 66
    0x96402117078116010b40030951601030303440b015048820003101c80c4184070070f03000201000c9206040c10301c00d507580e880400c036290260b200141c55408040200b0621890704e075100580c00903036418400c00c00c4481e000490b0801c60703c0d813004a0b988070140001c2c0050741e00040c00b1401000300b460240316035401d0010348160064050490600c070180c1c0703034448040343e01070b0041d20607548000840c1c10f0740c4103205c00003c082d070311004040065183c0d00742e40031035000c601601060556045800400b03044500c0720701d02c1c00030301150807500e8410b405092254461620300170094145107004501107072650400b07082108690100003810000788034440001c4a40d00e412013041d03880855800d20955061040c1001c1c0f0345802c0320420801428105441c1191081d08403014501980c402e90381c0c1c030b641340d0304c42c0300795100c905c03c100300781d10000404c1c0014841144204002c0076690381480303c0038102203032400d01c02060711264104031000ca2000c55401a480f21540f03402036068600ca0b13030242941402d880319484540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 336329829 1250 336328579 336328607
    0x3151808030c07031d030309040b13020f04140405041a100906081612020a15030e010603150c020703020913060e0d02010204080f0303060604060815180702070617060904051513060516 80
    0x20b12402204c9055407a012100100bc00c5640c040d90b59030034074412000c0c036501c6030054407804990110401e030242403a215261189074015100c114040841800c0c800c1190010081402c10071011000f00c0e0821444c0200401000002e004000480803001d2800480307026800c964012480f10600e200540e940024100c100c0e50800d106d0075003004945022800b42040208800c05076003400c80000c10003a05090022030408402d07000c005c0305640000807a1250043d10002c2d60140095000c5007038200c01d95202c084003403003140001412100003000500306024007480a001d03175400714080201c0783c424031a0b4000c008040003e0740c55460140d001850300d0165025100401060500080c281068000311129401000b88203245a00c0051540c1c1c0700404200c0340c680050191500c001001e5000c2d51030b403070351f46400101203016036680406101300c60000510076140c40c812155421b0300310380e07035110180c000e003000300980d0804d2085042803001d417000904400c42c03405040f0b82c0c92205550120942c40c0b010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 336330935 1106 336329829 336329831
    0x608060307210b0f0f0105060f0c0a05060403172211040e070f0b0c19030e0a03080904110405061606020f040b130f03151808030c07031d03030904 64
    0x805c1d0390000c0d10403485c2006200501e4000b0103000328199401901e400e10b0109981d161030a90140010368146e040b5070140824103500142d07181c03d01e102000e020b88030341849100d03603290182c0082c0000c00a02030500900800805c155480703006d800062061107814499441d140e01c90ba61481100303a41c005c3c0c030100188441022080d500302c00d92807000340c05803283c6400045204070301d49a084041220303004100045030703289140c0e400030f180142511601c981082061204680e07060040944a00d0309010400069540300c00312000303480d00c00d40090714100e040c82c06102074003401c0803d901484012070701007480700d07410002e001040f601704507210820b907440c194130030a9591400301526082c90300031a09070545160300301107112030148021900c8003105441e40b050304d0b0030540350020030010003d50001811360090070b60004241c0b00c0c4182c0140c0150a0000e90340348101c6264078011 = true := by decide +kernel

theorem cover : BRFrame.Cov 336151079 336330935 := by
  have h0 := BRFrame.cov_init 336151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 336151079 ≤ n) (h2 : n < 336330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
