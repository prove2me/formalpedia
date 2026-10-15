-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3845
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:50:49.43083+00:00
-- url     : https://prove2.me/submissions/a8474250-0755-48de-98f6-85a6346b7a75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 691366906 ≤ n < 691546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 691368156 1250 691366906 691366937
    0x30405010914100b040605010203070b22140d020105040f120e06030f060906010203090a0e1b16031403010e06010f0c0507171903051e0408010f0203061f080115 70
    0x3544800c0b010000050a400452102c12821105001d165074880c074180380081140e0382e400030623515541c3d0481c2c104650f41d20b80528603030000c500c52150a2001031030b003000c44c0900164034148234602c16000300303485501c80040c00403401c80f8403c0394010312040080300750320046180042000041102808e2108442c2908000181e0981048440074044882801080102c0c2000711102740c001c00280011801c00da5203c0004a000c4520301811030440400700020780e00380c00f9410b00f406006210048190340e904200890080204144000e90118820080d0220700418100c1100c4c103d036609e40110059450b07c0c00112203400081c0350340000c01c011000100003241c4244550340040004c0740c0010341c007414034460b042c02d1041c0f0304841c22120b50919007007008242c01030200e500f9001241c0b01c20005001c09140d5429074016038000f80d045d9803a00c003900076000780560096010340c1c0110f074080503541031031801c5141446201c288100043d1070700010406207026142c400d00a0009090054419042c1d01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 691369406 1250 691368156 691368173
    0x16050f1e030a0504051c0813300f02070609090e010222050109121a060d05060903090f030109050d0f0302070501111e0c06040f030c150c090506040810020304050109 72
    0x4a104100b1039032072080c003080210800211000d84201e07045600300d00302d0356030040c1610324000c02000010100c584d068003040310300c00311100300115460914000e00b04d00c066101c0b00c816000b50b1400460030000514010600002e421403c540b5941d40d440e03800c13800c002405000e065a040102c0c110340d020702180c2c100c2038522003800380f4101018582d0394020b181c00c000508812007a03001070b40300c0410008031004182c0018526041e4a04101c01103d19100c510104a091210100c0901103020f43ca05001041102100070200031404a4108065184240c00c060890b82d0002d001040f030b90020b00c1d0103043c1802169074140d4004035040050034892507480342420b4414040042d5811400000c03c016140741300c0c0f4008014100f03031508242046084000d0560b01c02c030140c80270f444420308011084c20180302d6a06404596800301d8040083c0c6020038150000c0c202070b030580d1000c1041420301150b942001403d44044030300c104000d004004141ca07101c4001d40c4050002d0f24255200c0100e00f010a1004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 691370656 1250 691369406 691369411
    0xf060c083904150f09120803041103070302031501140f130f02090d0602030f0a14010911160303051e07052d040b071e0f02060a0c020301050108031216050f1e03 70
    0x58450000184c021180200a4001c3c0e40100c01207071142d04881020617154801e499000798000c01e501e0306400024006442c214180d030000f5410f200d45600c1c66000355080704083d040b10518080c511065114200304003044051210842c8c026610181460390848260003d418003002440010f142030414070202e020b0b401503180544206800100b44a60b0289588003035a0258142c6020024000d030b08401c245410410b214401007143c071403c82413002251242144c01d0301c0c0365650b680c1511607162401802a007000c40e03880e220b10034061647c00200b681121600d1140c1155a66280350284401d03154804900003202c900c020f000c3c05080c00484070301c0764020400307450701d001d81e01e480f84018030300f002c000c0040400144520b41c01402c0b0800243c610404802d40780e50448100e511181240341c115001c1c00300300d8001c0d50646c01c1c000002041030307000c030040a07001015500b030305103a507a0b0039580171282e00d2108000005041004035460783d04054000d07086004d250908044000301c2443ca4600d0fa8005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 691371906 1250 691370656 691370699
    0xb0f10021605041a01080901140a140718170f150906090309090406091e030807020c010c051914030a09090b01020f0a0803130f060c083904 61
    0x201c0201000c5069a60540c014841282d003402807201c5007104200c400540400141405901c00225005020a40124103042008007a001e50f0741340c003007000d4000c1c2000050010a0640d41c001042e4403e1041c04c00ca2040720b408015544014941610b040f06209a601e40b0940d40c029000c024101301000d02401c0c00c2141070501019540c100103548a081142c05040525198410002011540c039170f24211644107800800006504031941002c5184008212048007036a5019102070209504540454083e87c00369003283c81080c2080019590000f850704080d041e0b5000000f1141ca0315201200802c95a1181c100d0388244c0c212000154990b82041405a020513a20601402040c02a01c035081d0810320910040031798002141c0615200d82100d4006000b900e800000901e9140c9001d01d0000c44c16030184034420f481080d41017941c01000b88608103c005201c42010514051080500340440042514910002e5004052003401700540c000010342111041c0000900035042e46011541d035000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 691373156 1250 691371906 691371913
    0x90e060102031c0e15070c030f1202070b150a030c0506030a021303060b100f12050403021c0507020f0301020306030d270b0702090a0e0712062021040201050d0b0f1002 73
    0x15458241020041706840c0c254215000c10428841c0d0300c42440d45400740c050510950203d400402220101000070392040d600340000340306420090450f500074410b0500b122b548c2004000141041404400d5200c05040d080790745405001c107141070001190000860a030040c940400e4500900008036540c2c001d0b540d6030383c0c810380300340c5904140c8607480e040025494140101da00171400030344070080f50980c0701d000380c2da14000070701098000c003ca03072034101d9181e002085c548490400240203a000c194200e0141042c2c00440b141414140252405840014090410032854950885d60a100e44015a59000c000040e1401c4080035400d00c0001c2e040301c800c10b6685006500500900780006004e48488034a0101d00040c0c211010408200b501e042882c0b840c09080d0390f040c4100038000c045813042c0511000c50910b02c2101a0301c00400d0125000c4454520700c0700d4511020100c00412580640402c1042000c28084c1c5200e40c40103074505c0004118903044800d030b030040307144402e5069880d00560b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 691374406 1250 691373156 691373171
    0x12112a07050910030308060a240905030f0a030c0312050403030914060708060609211e0a0c330806130b06040e090f030309150106030c090e060102031c 66
    0x400384034403005404160754058032030602029240e04940343d44009020040a400411541d90700c0e41c3c807000040c1591548000078040c0880c1c1340c40c42c2400714040201041c205200085c441c1000714240c00085181c001812600e4601c1c1c4065640102d03086084040001001e00084a0782e41d510900d4000e42c084d50340000c00d08003038a0000040094654801c0b40340d4043c100300b052a0741d11181c0158001c0c0c4c20b4034103070b0f182e248000200d1030564111130130004250090341424482440022501e01c0900c1e20b1031050442030240411303644070f40b0302c1880909108020b403030501600c010301d840034640b1032080ea00d4078900ca90001680e8004200c00c00d0000008184200340301c107038034104090b41d80c16051381c081040580f43c4c250004003144aa41705101c03045100100107003510405009110035041d09801741c0e6964a41802170588032440e500d03840501c00d00150010a8683c031a1241f502662490b4a402c10070307a0801c142c1c3d04094600428044c11448104405a006050007220302d00f40500b00902041a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 691375656 1250 691374406 691374487
    0x330060e0f10033c0209060a0b0915041701060e061002030313081614150903070201120f090c1401050a020a0f0303060e0f0a050105060a1211 62
    0x3940040c200c141c9200400e0107210850200c1c0001104681e8007640004030340e0401d90f0300c840201c02070301c10b03662044410781282500060303220754222814422980d01415a541c00100300f450f1410b8054102100401c1c00000540e00b00301c01281c0012000d0940c003414aa40c450a100d41a4464003401d50b113651501c40800c0f1244544003010341001c2c2c2100d14200ca056440c50013076490100a02c6054052912244a000d00c101d0104440d075000701024441c40316285030030102031130f543c48029407507a44140d00264040e48030080303415018140d594081c41c500110354004442807460503404080c800d5a4002e120101e002a1081d041c2040c490342480c2c80785450040f51104402c20000c00f94148001000401c03406540481c91482c1e042e03020784646803030083d5041c124002c01c819013115040300b1100c0309011440c0203807210740d481001b0031807003801580e881d0024403450307010b080380c10b401113020341802521500c4640c02080b5100d06807441c460600c280070003030101b0311078404c5041070110584250111103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 691376906 1250 691375656 691375679
    0xa030b041416120f11030a1202150105010c14120414180c0301030b0406020403021e030d0e030d050714070f050a14011e02100905010c0e120703033006 66
    0x9002c1904400c100e5140f070590700782a4807280190080c60250882c0b045810000d0080320302c044d100c0301408949038141c0518201c0018850441f0305c0e00544030f0802c10060042c10004070034162081a0344940f00480665220000c4d100e4036a08420640103030000c00c0e000c0b000c002c016000038007040100c680100308a42c1807040444540c03100c50318600740031041140c2280d6200031641101d82c480d900c8940e42e82c07a42007041c028050740d00001e5000d0039101086403c0300c005540700b2040c11048084d1a50280c0c0702c0400e442012000e2941c0e0f400d50409010286c86e1742c060005011054080c1c07035040d650400359502641095540d8021401800626034248800d081003245400580015030b04506600c135000e0020341644103080c6e50320103450680d0540c1c4010b03842444440ca80c0c0c2c2c01030a0a002214181c80d145010342a0f109260340012090004100c891901c07400c20f0503010b203100040c18241d41161805c5400300c0298030031204900300d145041030395600d64501c03520031454681c0001412800c00020000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 691378156 1250 691376906 691376923
    0xa2a0b07031e0507090815151207060e090105060712030209010908070308030709080d09030f1a070c051c120203060406030c0b0309060c0a050a030e2409060703110406030b0a030b0414 80
    0x210f940c0700501c0c140e507139601240069005058100415aa03000c8c00000030105d07002003800101c64040d42c81c0005a5641280c040040100b040f00d440489071788400510682d1702403400064051140700410ba0400b500940c000e1101d0300341031609810303407070f1500c6100e80340840503441129099400010408007a500c240d0800103046040080d1507075026110b0000d04003034040c000944102e83c0c06090f6000c0013044024085110701612900e03940e4904610050507100500000342d490303001d8004844c400007000c241c0660420b03560f440701503c0c1c4620000c80f0000303402c000d1030140c019560300760210101c0c07111318100c0300620042000c0c0d0b5172880c3c5000d480342400300c0074014545c18901804111240c035084000e40e82d145141c3e18000030851070246600d0b203031601100d558610000b0441907170000344074410990b403003260380e00200c2d041515820f40c21001c03a8445049a240e200050000f802101d10a420010320b40d60001c0422041903202c0e00e4803062040c0c20344045a80c802c0b41900e4900702e800500010360b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 691379406 1250 691378156 691378169
    0x1030204030210051303300203130303030b06040515030a0f0b1807090b0c03070b3108040305031305031b03031801050d020f0a2a0b07031e050709 64
    0x500309480d50740400c082d1190a64620f060010101d941c02166110590481c02550000050140100c0f14580c428180d0812081608002c2c001181d0042d854000000c43d60101050030007061601e2440d20210001d004030b035a1591310000800c000201c9036110001680703000d100c005815a41d082c4088001e007240c003802c01d55108a4203024030061682d442d007904d1480702c0400400328004c1da60b254030484810141750080318194602041018200400101030700c0042c0c850391041d01d041d150200e00114407480034000c5241ca50750b0300708003800440b40003100c030001c9101d09000d900302510b0750388140c03d5030060400002c8608200a00300300f90f180c01c002d114039440c0080e6016058002c10740210707440e172040c84000e10b0880c5001c107100c3c401c0d921503c221800312400c1c4078115180c1215404d005065070181070001d002a80d683c050285591200128540c4014401912014081295130390024043c0052802081c16503407550103040801e6044e040394482c880b25000940c82c03504581c00b9003084000c0c2c0010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 691380656 1250 691379406 691379411
    0x4080309090a06060c060b0607060603053003010b0a0c0f03050d0c03020306091812120f06030d0c11130e0604020312073f11010c0309050a03032004081b0103 69
    0x1000900c0d0050110341c5c8080c0c210402081e4480c910010801038402c080300200820b1421b00001b0512101103494500050344014000c1e02c909407021599585d40002c0700c1c081301d032004100400c618180362004040c615840e00344203407003100d152074482c0c004035070607029408100001080f030300a0340c151140b1141420a810110301314100200070425510300100400c1c07070764105c170480060300c9000f040507038000610700f44d0b806e41d54104000340814a28050350710420071000340c000704455250100c0e11419910090380e410000d0341041d101c0c00c2800c171000ba500c50b00301e144080706000c00d040034001c4100d038002e6440280304500305481030615100d020282e8252a8601740007150024805004c0c0501e03d80108101c008034203c1190050307046018144c160b505040503444804a20340c00c0591191554401d41c020000d5462081e400e90a50b19900401045900440d80c000b001a000307600201e041c001004000098084415210005a1198000c21496030108840c810360b0b00c40c0400c615410714080ca010f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 691381906 1250 691380656 691380659
    0x15071202030c16020f0303070303090c0e0f0f0c0d060605070b0c131a0c031b010e0d050a1b05010c0302090f0402160305071110080103030206070c08090f041104080309090a06 76
    0x10600540100040c83c0083c5040c46205400e554800038010007210000303041d80c0c1d0303506003807070040d005109107a01202d841070225030000b001c7d404403010303900c0340a504104854035503c0a9030901181e80050298000c100d0600030603c004002d440b075100908065260b1940d56006410028a40d8031300610404050b8010407000d4007100804147c00c003241e078411045440c000728065990040d009031601e2030020702c07011903070002109a04482003034051248000300320f15454220705540307038080141c2d054041402044440c0410b803080da400407015484a480100e516559624103081d55611904400000d4000c210401140b1b0107a0b0f1189030141c3c01c6508614080724500c44010b140c5124601405102010072000141700c81e030440c240750140024520054501d030b1000161201d40d083c00250014440c50001807031075070040071105002604906881d04044802080108000982030b2044d0000e440301105000c020768040980003505148000c2d44e11200c00000380b04180b100244030780e5240c0e041c00c07030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 691383156 1250 691381906 691381921
    0xc060501170f0c0609040209010203070f08031b0309120903010912020607120e1b0312190f030203040b2406130603050c04061b11030d0f0e03012304050f1507120203 72
    0x2c0325458032051b2000f50301ca4900e1801030f411806117410251015080e142d0398400c00000c1c0c0001c510440340801810011103a40c640d02009000440316403016911600a9510303031414000984500d600c000d0003c18890043e0b6100150b10f01d0100005000d0391202b4140442d40343c0005541d40212740c4001d04000b0401c802110f1a9134a8103c0105207426011080303107119900c051180855400c502c24205958011036070658015400c0b890b1000000b032211111190071510a000301c1c0d00803a00b10550800d55162083c0300d02041115102e425660740c2d680125034000d440303480180c07041c0042c00703c00840a9141140180540e00d00502c00420380d6002c0009000d0b01c3e800c004034030780b89148049286403071201840c200140e40c10000e112507241c42000b218021003944420156245500b640c1c6280b54400d2140a1600740c6820070140486201c4041c00c0986001e001902030358421300903000c44000f14800c0d214581002e054030301c4840c4580040082052003a08031803180404280c820003180b41d45452103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 691384406 1250 691383156 691383169
    0x909030c0204150e041101080105090f150a080d0306030b01050a0509071b080d020903300c0c04230106020714040b040b060a091a03070206070507030c060501170f0c 72
    0x354001d00c03450303640f100030104140008482c006402c0e01c01120400e414282040301c44c1703086500c1c07450b00080c018000071486080c0b04c40160b00030381000342c4410a0f502c40810100c00807400030380ca41d800c80340980000544080c02c011000181b01e0644000030611300314100749102d484c058110303901940f0a02d80c100401e07240e0f08a800c3c0c3c003038a145043c008050200d070304928010b070a03450107085100085403031824074120360b005040e02c000031400c44440d14819111416404000c01c0004400c400107504a0103100700380000b0030307540e0117540030354400f201544005400c5810001000d18160822040824001030919489002d001d803400100340740c500e00743e415101d2180000c035850180d6182c1d56080c08644550304160107008004006540360611a0002810044240308090183c003101040c8a201e8240c00c00300c83c0184020b5001d0100f90390f51010a5034182e00c180411400c01401e64004000300345a40701322030103801c3c1601900384c5400c01d0340c2140e00e130645009071a4100c1d0001617200c105030b40c0e01d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 691385656 1250 691384406 691384427
    0x30b030709062c1626070810080705060a0212070b01050306011e1203170a0e070902070c14060d0603060504110303161410060f09140702070317270a090903 68
    0x2810030350b42c05441900880d511100000d460072600501d45c0305035900100c00707095074403484069640710f01c5075460880640a20303085115000d40c64211081c10f02c800c1c10103000410350908180102e4004030310283c00c0251660000c0304c151040b50101005201174503040c4406401044c1c00c906000c5d0016a1044c010b01d03200d118410301522400000c1c038001014000c2c4540045200390f00000030480c40c141c0e0310b08000d0525410418034500a240020960300c081e4401d903010560411519040b035820280400301e000d880d0111950b00450170322003541c0504013401600045c45c490080800d40e0306180c0740c20815400c0102d061880ba030014002d6004040454441002083d0480644141038402c0c990a0b41031840300f00c000d8140701d04100300419000309000505089580d880c2c000c1080c00003c1d400042900400c0d15000016040007030b003040843c0c00d1f03505460414880c1c10005141161880080d89804907022407a1202107039480b55460620b400b951074401422503030302c20301000c0c03a00d0340c0060200411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 691386906 1250 691385656 691385671
    0x605030a05070309060e0609010518031909030c03050c0114030c090409020f130510120c0608150607062f0703050c07090e03040f0801150312030b030709062c 69
    0x281c000207005144250042195030303420900c02c20650034904400341c2c603140d04440e06c0d4102d41c00c0c103000c1504040c06649100c0d912504101270350422882c00c3d011050020b03121759000c1003000312a4040041040c440714000258030030300041c000310321b079100050321002000728243c0c401c840a10401c22101310300c500b242e030030580c00c4400040304841c42c130000344842c1e503640d525034120785030440002c00240107038400d500540c500d540707000d00d1907500c02e080c081203002c0e03800c01000030401700800c00c0003500910b5005d40204401d640b0b494060505808250700d50401101503500c9600c6800000710726500c001c0020441d04031252804210400603c9080701d403140300d00c0101040b90015480c00c0700c0800344000e8026041c0d518007031042a404084166803034001d40110040302258003400510002c4c1440340079040c4d04a40d0b83c1d4142e040c9151240d4610340059a4483d007456120101c1ca605580c00780074000140c0741c0241c00251140c03c1594040203a8100300c8295541c080020310302c0880040444801d511264 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 691388156 1250 691386906 691386911
    0x2309040f020d0603030201050121300305010e060109030b01060c03110303070207031208011208090d0b18100605031b1207030302150f060d02131503060b01090f0605030a 74
    0x10000225005000c900c5503091014804501d81002120540283d011280254007d02c02c60f40c88040c100d1000505108000c0340716409400000080c0c48521444110102809000004d07408240400542e10003010380c5130010756554014030004e4040c401da01d4100c1e10070710b0441c5806055680d41d40441d2811b015100500c0020880306007014854201e80b00088001c0c82902d490381000c0700003035600c5010740801c48070852105030000c60b5500c592400fa0494a02109102004925448110280c1d001908a58114000d01c0d0600040f44030050554020000703440181700c180e4158151a0034180f40110681c0c02500b000000c20039947c0001da5018401c0c0c052840c2c0004403030440000e8101d800020004900e801031000000605402040703038800c414ad25250154030f076449035800000903408855242d03000304800d41000c00360a104201481c52295140700117141d030401e81c40c1c2600d201030740d84111030003a01c50348902510b590000d072480041840c142d001c51054140030014249000c010006c01c203255 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 691389406 1250 691388156 691388167
    0xc01020a0c02150a08450601120c061d091608090a080f09010912050a03081602060403030e0c0d050c0a0b0a0c0609022b170c3c1005060123 61
    0x7440d40e071058182c1181c000315006c809001844032940c02c1c0f0700e140450754014400000780400340d82c2c1c0c600c00c84660200480000c2c40c100f54080d10f0007802c1040310103560060035a44004c43e00c030303903107614000c1c60034403589155000035041c002e104a10003031140b2191b400410381030300014100b405861399925800e03110703515404840c00403618550f41c0e91080310003280b01d03c000c070180b08002c126980d4850080d5600685a034681b190010130262141503900113900290016011a100b0352108540c01d1030031060ba2005603080d4000b0380b141c8102c0c0004d650b640c02c1982038404a2070203544100c020103845082034101a01030794042d101c4c000d2008080d040644400350b100440d56207a92145010550500d5109240c0c2250a1242035441d00c3c40e0071512880442460718100f00307514207550840351050000e003a03010b41c00c91030300035101e01c2850300c0540d00704070395810f1503803a456410070a01042d07600042040220010800c410741e000078010f503040c40590b050134041c00b002c074018468504a00c0b0100355030740 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 691390656 1250 691389406 691389451
    0x6070b240310091b0e0106020115060813030905030d02100e01050403080402060705070308030f01060f03050c0f0c07090e061905040209040320100209120303061e01050c01020a0c02150a08 82
    0xc882d0103004d002d404002e8440460140030102c0e41ca816540c1c0e56008112045400c4000910b0b0042e81c024030010070b460100007180030303c1c0c085000b110036101c0d00e03001b504c0c65900c00200e860030011170340c0340340582c200850001e4600114411a59440480802408070341890740b0701030a0101c000c2c0010740900d900145032030500c0300422604009540c0107010940da0325000c50004076002007805114000745079814844207251003401518040c1d0124008149800a1048030b4070745544000050182406010b0000405203d40d102d04110701e00d048001d81028540b01c240f400d00c0105420540c0b003070034540410301003d80c64a0003c0f0740d1013580341c00c0c81150900c1c80805d4034201c1a5000b59460940f042102200380c0c075555801602c8000e1090301e010494421140180f0388900044441d144c2150100c0e41c408004070b16000d40d01d800a0f418140686010010794005007664812444980851880607240003103017800149214600d0780041c41d00d09080b40f181004001d050090202010903480c1d40c0b401d80076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 691391906 1250 691390656 691390673
    0x60103020f1b0a0209180c0f181f17120d0912270b03060f15070c0e06060a0507060e011b110708010605062706070b24031009 55
    0xa144080d407001c0c2c0468910044607994816049080b802114050040790b03000310034190311500054510054103102d6016814810382c4400040e01542c08940154800007030000100424081e1011461b0180003400504510303400408039480405201c5038911880c8483c440450b45984442c400c01c04203a80f000c103400114058412128064408550080004460b42d0094441c0d03a80f41101521540d40e10706950103954842c1c0c8600c03801c400460200006035007441e04008456010800411442204030b480362114629040030404580583c01014140024481c0c0c4544650002044440a02e40201600f0040c1a8003d0082c010301954a9403074840800400703403c0310b0150b6040c21070004403020840c0f0020326980d040380a080c0540030310000498101410702030582996009480546060640800c40c2019074035001c1621540840080000c83c650b1100001c220075801032160258909001d1404c64240d40301c802c000310400180068510340391000319100041001191001a5a0001381028000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 691393156 1250 691391906 691391917
    0x2041505070c14130608010903120c0c03051e0307080403090803070c0b0306032a040b0301060f0323060a0204090e0c1f05160c1a03010b0403080c0a020a0f140103050f060103020f 78
    0x940b2070a016021503101c005601008d5140c0c0070381d89009a5440c0c1014000031640d2001508000412035221480440e0150000b8028503031354111211068800040048441e08251003030400110204140800c0c190b001011b50050708440020310b20740300c103650360035001031102c0c840c4024001000c000921195002d1000903184003038818124001001c2c680059100c85450780f01c0c600c2503207032101c04809400c0511854041c2d400c417184465865046444625501d4005900c840e918204282c0010311803e0920a081c0240f0b0040c80158880e030512490600307858584500141c154031050301e03c003032552000040c0d86e609003175403a0482c800d0500c0c01c01321054821500b125482d4086400c8550030009029450380032280074040e0b103081c511400940410a20082c42140c1c0078840c103000508c00700d0b001ca00144060280b03503080300d000c101c00d036020508615043d40007910382d1035002c1042180d03c1ca420b44414544000b46820130031403a054408525102c0003629280c10954042044555942c0c88411a103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 691394406 1250 691393156 691393189
    0x6061415131502100e160803030907050405040c080a0f02041409060703150906030c14030304080c011805190e0108010c0507080906070209010f03050706030203042f040e0102041505070c14 82
    0x100b00c6045c910309070780300c4e0311004d541c4448001c0c4000180e840c002009503805240c060001c3c1410760b190104103c00b400000c0c00568003960b40d02000140c1030000c10008501c240b041c400c600c28117241d801000300f1154011703407030601015201c0400860070008190240d10007000e0400080c3c1c0100320000003c00c0d8065049001001e00e070060110600900c1b50011041b9100711042d024404112024940c81e8041c034450012207a01c1035138150071030741c000d000d01540380324201040058240d50764001211000c002c1c10b03821030803103c01418440c5507000c0d81140e01515000c1c000f03000390b240720030009186200e400c40142c2201d00c00720306090340f6a40d18040301ca0154006102c026996101c6914038400c41140c80b0484451141440028081c0d0180c000d603441a5040800184015281400303180d1811030200200721014401c00c090080c2d076502e00c03d03000d00001f080c00042e201c07400d08a0f03a4802000c01d404042c240842400b81070001401030f10100196811001c105246080030300200740800c480d51100c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 691395656 1250 691394406 691394411
    0x5010c120c0f0807200604021507030906050f0702100c060506010f0906180e04031107120305030a020309100203100518480304050d0e0f01050c0a0606141513150210 72
    0x1840b0340e86001841b180610b0081700c5000d0b90516107030a0400a109038100140403d52861003046414010300c00341154500c0308000d02d15280480e80080c0b4103003040c800c3c03840811400110780c000c1c44141e10455920a10a082c21100c066a07010b000d0b01c4110700f481200100f20107c8030520310040f0b006980402403d40300c00c031803298200351a0140890400000c0910184a0104002145120842c07088242901034035214996100d44500f40041d61008101108512602d0b802044806051000711720503030410309841c1406080c00e080026a110f000000058450b2003400c7c03100488000703035010b009508020022082000301c40c20010805445010104181018900840c070040d01c00000c5100d50300c2202a122040a030244c1074401c0040305120035002060448448001d5000710018180307030003190120b0758650a5a60f6003001d4070010f400000085034408070504550400c80c5021b440c0108103e0554104003220311029803500e070a108002031906802c0c0e80c1da01040c024846e658036004075080a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 691396906 1250 691395656 691395707
    0xb010e10050702131a010311070b0c09040b0108160804020d12090303090501210203090102070b04080d05061e0907050c032214030613061805010c120c0f0807 69
    0x40c1c025009100140c1c01902c0018a18513100321900c1070781c1104040e0103d03024500b004000440007010318410312a507501e420000900410000d0440c148620100c0c0e80c45a83d464080041c4016100c0d107000290601c500d10060103200c1506015030201d10380f0030b04d45070903195228000a1102c2c81450805045c803e002114070035800c0c1d0103900c0f04103690181d00c54010850f0b6950044855440000d0b800c400e40d0200805143c5103139058000b5034101c0390300f9001605014042c0c40e050305642d070036075044541c44000260042c0a0000b40159988094201d5185100c141600400c50f070b24061740003942d04c181c28010028564500400c05d56401762106001c513900c408200e4409958007045040c01902c2c9020f0a03800221951039050303180003608040c01410786902c91030039041047c0c0c00340008030380d581c0d1544545101104240042d14100f402103001040328440148043c1201721844406e14645013420b10441410740c10030348000c0e501c0110310742100107543d016070883c0d2840001d84824140c4008018 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 691398156 1250 691396906 691396939
    0x1e0312030c0a08100819030909020417010b030619150b07031211130605030c09030f1c08040b07271203140406020c21060703021c15090b010e 62
    0x7402c00210141c0f00e0300781e1520b400e600c640000a0600c0341d0381169110054926060341030300b8001240c07900c60b0801c2130007940c681c84031500380c2e00b0581100f0042d9841c5418040058005d001e44132451901b50058030746070411489a41c5080740400e0310f8139216440700c0c601c1314000c10840c46103000701107084000d0345846482c40c00070142c08191028a0700c10f801c10400c0350040c00300c0d504440c0b00d01ea12030802c1806514101056680c2c0c1c0000308103420130441400b28076000e4405001040307524801e20040c0500c10040503000f601c0c1102140f24004201c900340820001405000c540c41c4c0208082c10207000020303510b14100420310740a6503043d0840e640410000f2000c07008103038000380741d02c40d86039082c080700c8240362220365024500c1344100503400002071900c0703030900200300c030310010700019441c40041e0003000081c40c10409498140000c1e03400910106c81070454103056254a00218060013010060070315808961814028884c80c00da031100b00c8100eaa01441c11408500000f5002c0180c0d8805c1d1034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 691399406 1250 691398156 691398181
    0x50c030d06090506040c080a09060b030a0606080d0f0203180f0a0305060a0e010b030304120512071101080601031802060a090e0408031f03050a0b0601030f021210050f1e031203 77
    0x4106102c6608010206a82d441c0070301035080c00351490340d2580040e9079001c91880103450581410385425030313181c107007202c0d81d2018001440c0140c051000401c8452a02c0100b600e0303d110207518204121107070100048195010049403944071400f040d89484555050005501700d0510b10f03515840013490f200042040400306819119004103401006000b85201210707081e00c2512480640c1034000700000d01250349407112611110340500102e524500c10501d0703005d9a0341c850107080e1032460080c2103400c084e690044c0c85680c412020b20f010300018101d014840311b88102108020700c1040081166441d80b84612550740003030032080c24800081c206414040400ea1060307610f4980c00c1d00b843c000c00c00302c114144c10002180d034048001d1616500f50789440380e440d140640201d04041d1204040d040c1001c450003d072408441c40d1008100d81e040c0050050140c84065100c20700407510001040103a1ba00c00c800001254a07203e0000e40e03446070400002d092aa9003800c0c05078061010003030000207180d05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 691400656 1250 691399406 691399409
    0x100b0f0c010510030c0906050a0e04170c0a060c0c0b0708090c0307120528030507031403010e06010f140f0c01182405040c050f01090503010c05091e0f10050c030d06 72
    0x281c0ca17141d045070302d40009100b5920f56005482d084030750504200000e9048508543c0d00c5801142030b0710802400a001310050750140c444412150b0095075407500703201e51841100901c40395800c0c1340840f02030f240d4500e40070750002000c54003404085000198401c0c1c0910100000040003805d8401030368a400107038499042c208000da681c0e00c01c10081c0002c0c150f050200386103001c0c0c09030a940c40100651b80840c2c0507808000f088040141c403507441140782c003143d4065406013014101c0c440840c0752200006003644c020320440f004006c0001502502100300108882c0002404c003240c0b40d5807103503103020354090100862001386a4409050940901c03910507555101042c40b803115140780c000505401050318001d0714003600c10802c1500420051800b01d02d5083d9066040c107202c01c0d116070703c000003421980681441800b090000484000310310b4880c40e041300c60450002010071042d030b0f90f400300c0c0003406a040d07000d004098600403580c03198014016904040001c0d805c0360f94a80e040700d52240600901e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 691401906 1250 691400656 691400663
    0x6070513090c020a0f062d050a090c051903020306010815100f0b2208060106030b1f0f1814040b01020114060f06070204090503120708100b0f0c01051003 67
    0x6400c408540d1201501a0760204140c5074000c01e04142c094440003001610100e080741c0c0255a0307c4079a011100460b804100c002d0014170452080700799529120580750010040c0c904ca074034182c05a40000c80800b080d109a90043d11500710740340d11100039101c401e5181d040070b03505201d48800000e06400010705204440070900e040c40325616031144041c11104103000351300001801d0310b0309001c0d1880100c050320040150549208240c000361501509895032070b080100260050001071100f240c0601a1807546001501c0400198204195402000c4102c10b90b03501002115021004036030700c00c00507030342450784030207101602c40c2e42c41004003400b000d2500755034000c03820003003101039a41c01803052001c1e21711014051142ca80e07400c030802021510700200d2035031041c811b229010141c1c8813849140c00f403a1141e001153340343c1e2075900c00640108018100c40410000300200901150b100c0304100480e154010b0864803008100400c001034080c0c1d0707411075000d600e0001004181d400c4125901c0841c2e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 691403156 1250 691401906 691401937
    0x90c020706080a0f02071a0406151211040e030a03050f010621240b04030b09061b030c071415010801290d0501020a0c05071212050912060705 62
    0x401141640c03511003912032007012450308000100010441c0d0000f181102d2a10b03001450400c0613543c403507003152581641860860380c102000300300a2140b10324149012101000c940281c0703000b110b20a070400482005184690010710060b558503103130028540d00801c0021340e40c40b8514201d0040080038201c0b03910103104140400000c080d4080c24580040e43c440d100003401c11007103600d400004d0000842d49010076208003003008072440d089090603026114181045a403945941801e4541c507601424a88007034006005004a0348207850140415000c5009038a85039500c0b031015103018051120060319100141000c4a2480d0020a034206464a00e40d404080d42e6201c2881908a136401c003100c43c201d031007107034084030301701907015502d45100b10040038a441c8940c0c682e1030701d007aa0040702014010946245111003044020700034280a08120100e0401841e03d940b102030300304104181502c1407002c0002c0c2d00c1a22f480e8040a072107020b064ae8100d902a08140500400691005a4401d2141c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 691404406 1250 691403156 691403171
    0x120e0405061c05150a020d20030103020108070e13020702030618250308190f02030c06010e250e0f0102010b03070608181c03110a0c0b07120e0709 64
    0x160610a80d80650700c050b0a060a00c8803080c2588601140c81c08181c615100b00039614050a400c054028401c54042a0168640d0500c0ca268001e0355140010301c98640c02c2c4100d2141c80100c12000e80741101c1e02440d103680f480d16013600c2900c680340140300107a0045074280a40105170741c3c035001482914403c1d07003181d044c0ea4800c02e02c0000d0001812140241c2d0701302881c200036001180c0038014042c080c80094021890303590f44c03002580c0e4041484080842c049002d4000c10a401c040c0b107842c00203003400554909410b400c4200e495403014010325000b40d0380e0070003003101000d800e40302c109140000c00020805000ca590060a034803540b00304140700f4940390007490480d52060040c0840000c1c040c4c0202440e900700709040c0c902840c001c101c03030408030080c8141170201c802008114a058102508136a502c590f5070300041c10790f42043d404810504041044030307078007540040807107082d98000106498075218500c2c00c031010b0108022640c201c9042c402c00c600c640c0804950681141ca440c0001c00075034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 691405656 1250 691404406 691404409
    0x5060f0405090705010f03020d0921050309030a0807050c011a1201020708030c070201030e0a030c1703060d06090c08120913060518130210050d0b011409120a02040603120e 75
    0x1e410071551482c0d16003089600700900d50140f009100c110509003005400c0800002c0010119100703940c3c1940c4005803c0300501030074414480545c0b1030503032451f0132891480c024401580da07100b00c01c3c03260100407800e800220402d02c81c1041d2000c40212400030301c40c4c0c1e0040f15000c0e22050181100620070f00a003c0d00c0c060201051081b1000203500c81c010a0541d030f03c1042e00d1103550014074059050580f81d901c450300190b400c1c414800c46511031380300c1051340c2d032140c01c10b501c505905900e1100c035400700f00184186541c4802d072500301c2c1a803001c804122602549840040001c0700e92040815124007545203030311510301c00151403162810364120011030101107101c070030748060f80728403608240c14050415840420706841c0d0361003d6a080b80421121490380407030018850910303490009071010030400c3c46e2505601841d4552802440d080803455194989031407244520b40800d442150242c0d218881c545090010024150700240304100550352800c00c800510800b584186c00600300d0b01168009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 691406906 1250 691405656 691405661
    0x14010c020a060c2609031227040b060c0706033b010e0f0f1204050109030b0c040308071a1e010902071104110a14030c07060203060f0405041b050321130801020d05060f04 74
    0x88c0c542118460034030041200040c91680b10742081c2c45600d20601b64494200902d001c0000000426032580340950041c111504000c111411040d106608005205040b00000060110a400481d807081c60340c85507006105039610303424140259904030404500100b80000d14100d10f0701501d500c0c0511920b400e240d482280100c0d4041200020b0500200c0c20f02c0104941c411514402d103460301d602c07030702c64618a41002000b25000900303403481c015011242c0c51150340041584003070310751846a04950181c800b1050203904241070b4003180c404e051080400030000f4101c40039004000d09600f80e03042c86610b521041070748000c110030080341003040d0401c80480741300c2c0340401807950606066a40d054007a42c000381070f40c4d0b03000380b10615450b526606c901c00d00f4019440746a0b00568110b01c40c1040308440c19039071205201e83c018058010804400030300d00c100014a80c286180c0d20a0031000f19501c0101c16040f01d44a0742c03000ca00721001c45013a6100324041c02c411100c10310203407200d0040000303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 691408156 1250 691406906 691406917
    0x5070f120803130f05070909030306050409030f120b0405010e1e1312030209100c062d0509011103180c0a050618010302041e14010c020a060c26090312 66
    0x4031042000520030f420b05124003200d0740c8590110780a80005860b101c1c80c250b896009014411b54a840c2c000403d030b054030481e4010f10043c0c80c10301440d00c40791400b82107042201c2d4001c0900031041e81800911049510440411200805c00c025658440d06114201d10781200c11495208004810503105002001494841c032302c501403141e07000038140d94a80440100d406104141038007400f80c07000c035548407100742120030300e240d5030304d40c80c10354605010303007902c8181184400704102221084610401e4103d50700c1c051082d00e0003c01c080e1204116540100f4606000307000124012080c400d2804540654142c000901d4080340c40c0b91103581300f0400650068851550b014808210125003c0e502116404400b801410010305241d40c600840a07421460a4003822400410000740080314039440c007003950340d0f000c1ca0059404440c60340818400c4800340140e406012450a04a007000741820140c040c550005c415036070060410094107165170001e015452290082c0b42c40c0b006880e940c1ca081e6907 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 691409406 1250 691408156 691408163
    0xc061505091909212010050c0702040501060c06050f1501121d0c03100603080f0313080a0c0209130506010911090d030801051011060f090f0a05070f12 66
    0x4295100c8601c61031901003102c01c03140800342c4404098000c500508102842c40c0054070b5050104c2194131402041e208170b001d80c8510482180752040c1e0701c5000001c1d8a40780c802181e000107101d0300c03a880001e60300d001d0008000c3d40581842d00200b61a81d00117074074800c841c4241800e02403a244d0000300d1a8100049a003401032040d80c0d0620304103076101d510107820103544006c0000d14103200741c2c04280000d4420341d020b00a0360140658001c541010440b2000e0b40c00d181d242044000d09607610390340ea0b8894100d06d000e0706040413003c90101c4440c544420540c80c3c4c0140e00304d968001d1954040c00c030010122050740701d01040c200003842c1304080c184c0c0c44600e03075100000c0d01290f82030201480040c01c100222500e50841802030300082e40312009610801070081d19a130200d585010704100a00900c201e410381041405440c10400450000320a0b8220071385103402141c40da00d01d12042c2c900f8052800d0f44041d44200580c403401d100003c5079010543d050700d0800c0414a03100c003c48a0f01810110006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 691410656 1250 691409406 691409419
    0x90e06030d12140f0603120309031806040f1d010512060a051e010b03090f03040b0d020a12090b060a0503340f0e0621061b0d06060c061505 61
    0x150300080c401c2d08801006129030400150100042c80e040e003850904445551600720550240300c15843c040001c0c04040040e00300302403851500401e02a161302402d1200549024000c186000a50307511703044c2d031701038902c030242d00c030f030666482c51100111505003c1d0941c40303400e07050020800c2e04021324049101c510800c002e003000c3d20b400107241c0013018000d00700400740c0041456070280302440c271040c0b4001e08211403c2612420213140301800d00f00006034403032031640100401c00c03084500b541a00c4141c664600c0c010b071240aa00701c01c0d5408286003450000301803038052260304000030f40d0452070040a09a8018510700d80b62000d15542d44030030141510802d520015540c0e8005244070b0408411451509860003030782c3c1d6906200c5c180030680c011114481400341000310b81d017024428094010f40c0006010b0034030350f4480700e5940303a041c0508100c04182252020b03030384510b420011035140050724a020041c0300d660368401850f55401c410110740f414100b004c40c2408101e03103a8154191103004040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 691411906 1250 691410656 691410673
    0x120d06061e1103091e10031b05030406140405010911060319020c0a0b190c1403041e080a020312010b09030706080415020304030f020f120a231603090e0603 68
    0x1501c6002c03542d95001418801000b901c03c1c1501c4407034205446442e02d05c1c120f090110541c08001ca14501001c11004040c5001c2131010a00e00009070781141c0c10460a16a940740c0f00e500301035024120450100000741051004c5c4000c003d0154410706c40c00740614910b9000070850002c104c03140c413050300e8100c034480e8826400360440a40fa4001c024030002d0000700d9a8806e881c0e52081c5000b04200c490422280d0011240c0440c2d40c01f6000f0690b03031000700d1601041103d05403c55900501001d00042d0251400086107014900100d10707610983e50044445903e40d5601700700259641d1000c0700101e8104d103000c1c000901c98404030b05840414000801405000e802c03c40c080394800c00041c030944950900d0024211041041c0c030085010354042e135545480d0b01201d21002e0316040e032003901190158401e4103032402c901102c000f943c01c100041d180014514282c6421000c80c041c02108406028500003481050394850302504c91815110740c548644007a610701841c1c4105070226560f40d010b420800780c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 691413156 1250 691411906 691411967
    0xa0b0f01120b090403030b100e10030b18040b01170604050709020c15010906030b0c0304030c030e0d050106080706110a0308040b071b030f1119080a0c05120d0606 71
    0x4401c040080c03072140060000900d030b001400458040c0d5042d000702e40d45901012042c148205440c1903901d190a0100000044402164484048c0b6405104150343d03841d104016943d030300814400c0c280c40c9420006d02d07007030034181803003008400e11450740750344030f18001c41b2031a40000c206940300d141c0282c0a000483d28041140b800ba40c005030414043d40101e00a50081d1a500380d1130030b02030803040078001882401c0d498001c00900700944560740e0840d09204003c000f0394000d0304070100551614140401c2642a00410783d003c0e031401000309954202580802c6004002440c4000c4130090703512905820100146540c0380e00101c10701400180c04000024003003901540081d81020413880d121204403809001e510b1001c11800003140064040e031044011030780e000e00c000d456002400d02401e50410080058131a88000c4c0000429600d008070304800b00c0da0103001612012504901500c09004601d20501e50716480400f844c03440c186040c00c04101a4030030b41181940721408080303c100500c603000b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 691414406 1250 691413156 691413167
    0x602120a0306051011390a05040216050d0c0c090c020c040c0210050c03090d120f052d04030503010e0a090c06020703231e0c0306150103050a0b0f01 65
    0x90030303000c1c1500d8010006058646038030b5800b9460541e600d511031443e4440c0940d04014001a0700c0f40302c02a07810144e042c05400340c6100b070000c0181c04400c20040007030404950809115031165602034400320700d04c0e00798000c109400a6051040d401c0d1942501440c02c1070b2003c001c41c3c1800b4140070854141440f0003d415401007003884251b004480060f006076001506464000d2000c8006070403009070410f20f05814051250881da142ca1101d003146410349640341e98201c007000d00d81c100005444c02180040c56540104800031000384107020914100d604101161030111410380c004030400c60241541e03400305140c83c0613545c1a40c82e1861a440c01108440d8698003801034161681d9070300030301000810103c901c1c0010a00780d005030806a15500b00303450301e40501100d07480c444440d01d8103111482004281203e08a12108900c0707000c490501001e40741103040c1025640501c10142400061000350700c1c01c08405400f6a4280581c1c1e480000b48401c1d26509800d064201100d0310030f1020541c000c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 691415656 1250 691414406 691414417
    0x204060506210a0e060621060109020c1c0509060f04030b0906090d050f030f06180405010c0e06090604061b1b2408010314120f0904060512070905040f0506070f0f09060212 75
    0x40d45000c1100010007d810700e5001c4c1e00001d403150f80001d044841c80e605005502d070804040b200b0454180030305001400d540304151506100700c1000604c0d0b4103490f45d0000380e4001d99003000301e20030a45805c100c60369442d2380c140c0300c0301518400e04048500c400c0c89507040742c01138120081803e0039a2a40000041380400180846900c628413843c68170b0400414013106101d5402940081001000d051000e080c60300000c12450042001f040b4000303107030316005d0464088648614200300307054000d042c18080d07032030084001089000040036041c040c0c00040041c9055403082ca0342d030f1155081d2a401c0c0ca122910780140c64001c200c2c00801000410080942811065480c4042e10103c114032031648a075a03000e0b440103030074500046800f50701c0d07041900c210341c05000181e60b0710000740f85942070142e032105540b10300f0707078529120800141000915041495503541c0001140d00b60f042c03650016158911210300c2000003150130300f00c40d1080744a020320508032019034001d00488000a150051140e020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 691416906 1250 691415656 691415689
    0x9040209010c020d0609140313180207080a0e09010609031211010f0609091115030117030403021206040b0a060b07060b030109050d12060801060614070204060506210a0e0606 76
    0x442d1808003585404590035070f414802c1700002460304103450262142104c10540100c20703413042c05000a41c400210303c1e507041e5013506072606079001e40c5040b1000a4411407400421000020640394101904a0000110b032a400c030344035615603813180c00c1216604501c4c0300182c0300d10b60301081485054003a05100c05844190400451715030304000c42c2c4404d954581c0d0103005020364640c5110709110500c0c4030601c46110072649032058440380750030400e150206000c1c540c010644100d901c400880100100c0e0011079015003100da0070200c03c510140c4030b034802c4405880e2151000001954882d0794807800080d21801e03a132283c1880d10a4403124006c1502c0c0401940541d81c50114601042d000c0080e00001400390345c5a441c1c00441211400035a642640041c0c000c3e0305010b41801451b0300704803046000034202c0c16040d00c950990000030040d1004e68000c0c0c5e00900c000890f080c4440c540382c80041c0300f03074154160b6a41a1910b1000b14100c030448111520710b50010000300780149840001d00404010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 691418156 1250 691416906 691416917
    0xe19030507060917120a050f0403200d0906120c14090111010906020912030304020a050105030604150e0702010c1707031d010203160e0f1003020d0204081e010b090c0904020901 77
    0x4a5540d008003800c842106091359040104013404c102000c41e0304a54170000d000b8041c4114200b0440d80d1240c60805080242840900071366521720104c05850041d280d00300c4807c84000724000000548142d803103001d000b0004020b00300c58407000c28540100c0c41d03200d42541c0e881c86a0009070f1803c40254110020490400041101c44644001c0034024140c0701806010011780d101862000c00c00700e01103c541001283c2c00a100b0480540d45a6008408603a02030a1059403955001c0010713004010091090007a000036410104210201003501c901c10f40064008000151546106807841400c0c0424120008850000aaa80c07486078000d0f10b4050000310043c8065001040c41038203a8004451002a4886d403c400c070300c1c01e0303902c04424940e01ca0300f610b1501c8420090341c0482c0b040074030145c0c994185500007031003000c855510b6049074010088001074030811010403003d16014203100e030f5901007640c20022101c2441c03a105101034041d04000c10b0a41c500703034502043c08041d4003d85c0b2224117002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 691419406 1250 691418156 691418171
    0x30e0d06063803040b070509060304030903171804090f0b01140420030f0601091706040b0c04081b010c2a06020106052817030408010e1903050706 64
    0x40c03260141c030740500450801d0500c1c01c0d0b042c1c00c41c80b100351030400b000b4010340d9041d05404808107800040320780140c1c00c0000c8100036556444140c8061250404840d0085c03000402c10003810391094128050342d00c900c892072860710310404000014050b007405c03012040038a00c0721440c0c1b0b1400d079100d02c440038810202802449903c0d2900120803109a000c9946001c10034500352280c0382c80c2c89101e4a40c002da01c2000400e24075815100107070300005140111074064140810300d140c1c01b03030400800074000c00c0300b982d007035201b0010750a072541802c0d14100c4013400d80c1c00102c0e09000400c0280c8040d158514002c1c1006e01303a042c000140302d42c02c1d8220707074180080160030001150b004d03400f9034008400303a2048049003002d1101c0c101d50582a501c21030071645001d40c103000716650813041000700e43d54108000030900040703801000020050b8080380080c90800888c480010010010340120f5070300c5c1000f00300700c0e0a15041607440e504041c0e00c084142209003500c01c0000e0003000a44000c80c054880090b403031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 691420656 1250 691419406 691419413
    0x1a0904020d081c0b041505210f03090922080706061503050402030f0f0c0112020d0507020c0a061713032106081002281b031808030a020a030e0d 63
    0x16400064079201007804003c0e007a0802c030942c0a0707082e040c84252030410246c01503015410031120071307010301841034002d002c011000130b9180a803c0c0500304244296104441501c013060342e20340c0b01001d02c0340203039420400259410302e0002001c03401510755130020003900d150b42c3c4600e25940295811146da0740c0d2000d02154000030743e4221400d01250391000106810a40100341c601568802e103141e80b5800001950700d00d0344049950035030700400313007031001500405400c900040e000d0500d507510f080c0c2c540000c000c00c0e184e00145000c080707a000d84240c010070b9211401110109201400400c02c03602c43c0010420300c01090080c07180c1d40e4000d02c0c0419000d0b19241c6000b001d014080088503401e6210310303082c131a07142c0500080f440e01c02e81c2c140462505401c40358140030300c446a0310080b030311009210540280b9004880c1c000344c0e0188005119205c0ca25450050301441410003041e503a44500724001c225414008100e507580b600c40e40042460807001d9a003108c44816002e0300f40d40120002d10200d000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 691421906 1250 691420656 691420673
    0x30307140705090a0504050d210f020a17242701060801140307030f17030109050406050703061d0907080d170f070c080703020a08040306021209011a0904020d 69
    0x404011000d0400c0c10300c2c02d003c002c000345000e0300450101c4d10b000c003840b00007400041c40c0810f503000ba0a000c04140202010101c1c440e85140340002c016003800b94412a80040b070740100031107000e5450f806004c20021203c2e8100c1c01d8200c50040d41d4420404a4800d40f602e603103022101080020a80c0c03141d42822503440d048100903410000350101003e00601c811a0032410840c00742c0000310f0b4411a0240d11000a03545035014032010b0100c006044100090046005030003650f07140105161b0703520f50351814071500404d000c44003030320210300c1c203008100954480e0050100b200da104454400340a075001007003041c21070282c038074802c610507035200050f06402800a400b04088541790b04500100f0134070302608803180101960500f5058008001c0e1080c1c0141c1d8a00c21140c02540107030700c540541c502a80381c894980c10103040444081070000801c15203400601da80105944510215282c0d00e05c264280d48200d0740b801da00813071350701c0501020b081103465036900500040c90b031407003d01c0340c3c0c842210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 691423156 1250 691421906 691421933
    0xa020912010219020c010c03080603070b0c1006050406050108010306021c0f0e010b0a030b0f09070b04030804060e030105150d06061d061005090109031707020a0b0a0e120714030307 79
    0x2281e5000302c1e09500c507030300b00e00d840307081032000740043c0401081a1000900303080d882c040050a101020340811b0960304c08110300b03c0940008000142c2d00d4040034140c1d1b64810260070300c6a960350420b0808162420640641011100183c544074116400c50381c0f50001394004241d01c03c3c01e0100d2000c600c1103a074081c003490282e011407290029011400010032825147c004440a00a180c0140108001248070a42551081ca061041c0b4441c0e150401d049041c0b410760b5010a85038080800c0110134482c03858010000c6070a941c480b8050280c00c50140341c01e8071801c4445041001c40b603001400e207418070a4500c10100d1007600005403964031615244899a05003000c581c420f51718074100006400d00320003104109000b0305095090051180c0000d140c00386a0000600004003550f0494208c2c081c1ca041d1082a40d0040620f179a8940300d038240c0f400c58000001c0c403c0041c4110740b661019050020132090310040b95030141060a00341010341b12845450900c00b90140b1007084040d01290500c1c42788807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 691424406 1250 691423156 691423189
    0x507050301230604050108070927050703051b18040f06031221020d1b0c050106051212032e03050706030e150c040b0a021515180a0209 59
    0x58695040021440c0b10300810321401c20301948016052455035100420788007241d45c24a000c49280da00c56104985a176101d9101728100d486a60005c00e4a8400d52070020b0061001c05c020000c5680707003a011401e031581580c099400c0c20a0252240c000300c40400203080c01d410800d9002c04241d184004034080381ca2810b58003188680d03c0200b0b1080108200c0d1031441c4101070b1602c01600c075114906a114490312184014141742d00099000030200c082e0400031841b80d8280125403212a1040302400c0f071803500c441241c50f946001400f05c0c407490000c0040e01c00c10340620017480c9140b00001080300650010b04845017040041c40034046000d07002071144010446107003120041032640c50300d2481c01c1101d03000780b8189810901503415401c000913400e80d541002c0d90b0f204800380c0707610101d02507034803c3d5008000703002d00006000c516243c0004014207030650042d00381103150b580c0c440c6902d4a0040200841d440a046c8061030000700c01c00880c00d42014800c0c0d8010300c0c2c00c040c0300000d40404c0c190b20054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 691425656 1250 691424406 691424417
    0x240c0d0201062306030a0504020d0204051312090807170c06070f1217220506090c031b0907050a0e0d0c06170426090307120c0b070c061b05010507 64
    0x740420030b0f14078410303844042c0c5049483c40001050740020114007000340901c0002e55a14001801d642c1e034410303d441034a801030020031050400d0114050030301210b0382c0039580c0415000100c05140d00c100038003401c4400c52000b4040d00307410858404440c240d0758540840c0b901c06e082c5006c00d203596400c0140099449400307002c5141400d4600000c00450340001201444462031255906040219034154880742c01c240d0130301c2d0403203400b4118901540d2490040c10b18455102080b0304c1020004550503540b808400300d0b080c880d00800d04503c50a03180c0c1c1a2504a251040803070802d5000e00b002d00b60402503814807048041d200000f2600945000805580340003111a08108458010040825003140401c0300301e001e00d0640c840e038080d40401340e13413000c841005440c0030f00450a6101516040d10009066030152541d51140c900540300d0000141c0304c5054a190015540b030344002211046544040320304240ea14180c1c042c2c400c01043c015160780c2407517a00c1c080000620070b00c42c06114034000c0d00c84 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 691426906 1250 691425656 691425659
    0x305060907031203021c09050a0501050c090a0f05150a090806040302160501030c32040e1602031312031103120109060603020c1002130b04090507080a0506240c0d020106 74
    0x1605a8044501c1c3d10420325204200c01c100d225200c940d82404580030040105640c100c41c900300346807a040007030140c40365103004148000a1400303c01014842003c503100e0325a039403910a0b20001c81041d10407194094002005149408280340107400041198100750a10964400d2081e04110044404800580114500845038009183c068014010a20301040100038000002d0152030149050003201c0001c0305400d81609140c51588089250140030a80c64669031014410b03d24020395040134100c551107050501c0d64400015900a080b01c0000d04001905e400030200117046205025020021086810040b440080004090001c004000c107640ca603d04600241202c500da00b0032000c060040081c85421000060007100c1003090a40040c1e030f403091181060726020066103c00030107030010030006150301c026440640f0455440c1c46646044d9611224941101d031b044503469030000c84003002c86000501c0c00c54007090b01103c94105864100d441c1d810b41e1a01d400d440d070440041c0e4490f01c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 691428156 1250 691426906 691426913
    0x14090105071808060402120c030115050306010e06181504020a0804440408070b0315040b0604060e041d0d18030c06050a0306090501060504060e030a05030f0a0504030506090703 77
    0x2e040c1c00345000385200782101420103005030340f64034029002a100e80f245000300000f180041c00440c1c508440140200f2410b52582000c1080500c28403907076110740a0003000044001c0a003100038407400004210012102c040c00400d407901c1000b42508804d00c040f0002c00c6200d458602c010030202c9416201c1c031030540b416242c505801c0c002d04410458040e944440b0070580340c0d59104241548102e0032007a02d444014481d01440c0e801a41e200e103c052150002c0061020101c0004500030802c0c03000c40d00d8540810801e00065a2051803d550450000c02040102a12948100c0c10902d80204040360030000c51003000382542c070402c08550b4907084003134028295900111509805803181e51a11101891a1078401d400659807146d00140a800145513031464400e501260292214603001c21807543c49800c01441c83c0c105000d0030300818400c0410300894940042d403401c5180d8000d000f9440d10a8054003080c9641150b40c1d131200f440024807011001070020b1000394403070b94500c03008003011813650a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 691429406 1250 691428156 691428167
    0x150108190b0a1202091e39190e0307060c030302070b0a0c0207051e0d021c110f0f09010b0f271804050604020108070c15060501090801150512011409010507 68
    0xf0441085031250a51b20190007202840e440d6014580d440401e10703010030400b8040c52111202c560111191600c0010b01c80480504058046c082903019210490307c2852425100c900c1511561581513000c9041045071a101d1124500240d119140141c24140199100741c0e03210302c2617400302e100340c3d1660480e42c6d9541e410408d040c02400100c4851941c105800181c6e69001680420349009500840000d41503480c0d004003a030b00e01c03000301003a00c4207d1560402e448204244070410f48541010f41540d50103180150204060800042100c0e049034a441c1e22410309174801d1070595440402840aa41602c154000d403480032521040b000e2907254401080054040701c010310000ba4030407407824040400d400145440d4001e50a003840c3c0c0320358803040e805845880c4240350003060f941e026901041c074102250481c904031002a29409090350326500c219080c0c40d0780c40308108449100c00c1307081000e85891540c0034251110b43c000040d00000345200e1980c8500225105c0f590750f03444100f40250158880e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 691430656 1250 691429406 691429411
    0x912051506100801090e07030506042009011d090c0301060b1e03011a09130c2619020f07060c020a1502090f0613090507021005150108190b0a120209 65
    0x100c0d641d40c0007030310070b00340a00402018041c60380155900ca480c8208400c042080c81c0c040d40e0090200c071940e1074a4940b1428007070040d80320340119002180058840c0c1490404a4140e85030780034036404442900d400903d03001c500511f1500d061107280c01d01441070300c5c00e20410b4091b0040038074140d92010160070020b11b141100b413240c240b40004000400a6100300c180711040400d125603007541e50500c090004150380690701d000003c080c42c0102c006145034000040c00703003413003000d03c907600c9080132100c0c0100207280842d034144010308818a404000f01c4194010280752100000190030405682c42ea6421070358448041000350740711310501e8007401040169252040c08502d401c3d40780c000850042108000c40d010003602500011810000340300000699001400c484c940401292030702000081d03075000c03449a40300c1410700e001c5c04218204105c03809111521010b84510341162203c0c01a03040c019681c220313881d0300e541d1340c2a000003990f50300103040c8002c1c45030240c0034100209d54010481e150001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 691431906 1250 691430656 691430659
    0x10b0909030702010f03061a0a0806010f021b0613031b0f0303090501141b07140301020712080403090e09030d0c1803080d11030f090106050a0b09040c0912051506 71
    0x1580208088a24004100c1d409582c0c20700c1d0145404da800f4800340d0141143c2e80066440004d43c80c411006803c0702005043d00a03c1c5680f5028191611801036a542d0900c02c0c4020050f00103004446140a211071070304078524000e080b940c5400d0694601d0100601c00d50401c17665440c1c402002c8003c61040382c00c000103400040703d40c0721960310319074002d84140c080780b0455050002918541d00352509990680b1104903481c5000410700596909050711001c0d82d00840392590b800c0410305a0605051007a14001d950001034004413120465003034a002c040100304400f00300c60b03e0004244c0c9201210424080d81804c80190740300e1440c01c0380c9105076404171482000300061480700702d440340341c1480d48404803034011480f95641c2c802461220040d20400d10b000910090010a00c074042d288223201c03e1113902450000c00000f501d40701008085405440f8445518100f441000c0f4686480c1d0b10903181d000c000d04041550965558091034039110004050360b298002e10108081141d03c9100d05502200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 691433156 1250 691431906 691431919
    0x181605032125021e09070302070b011202030a0210032027060903010e030d0b06120a0b010302191206080102030105240928121721011205010b 62
    0x100084060140a0207000c481c0516102e030008a54110080303400c601e281c1c026000304641e00c108425250a0080e10741a60f003c0e40c16000090040343c824420b9400301d580c8032148400692030165004c584d0540c2c94016030781802500d03104401643da0385000300309120b0300c0d00e011840c404420398042c0b252800c074026001c4c60208001003405580d6420100e00000d04440a48007056110008030344a070082085a0340c16618250100348144400800340c4200348040500b448000c20260911030a4010300044c0d0340850510700c0802d0041402da0482180481c0c103250040c00c11078029185003c0d5440c2480040c0800d0035100c800d5100b1205000c0c45001c0c10f4500e0080d071655140102040d04508042c031000960b03034081825611981074032048072007444004003a40360209107007070007001d204a020185c01494900440006800c00024041c500054108504500002d0f40007818a01c40c2d1140710800c404040080c0703040a2100c000b0b60f040d000e040314000e03512100016180c0503007140c11051742c1d28481c1c036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 691434406 1250 691433156 691433203
    0x30f090b0105042a02150603010e06010501081b03010b0c011404021c02031614130603050a02060d14090c03070e060f040221070c0303141504020318160503 68
    0x8403003980090442e44180c800043c0c0509510080b140120519030701643c104001103588000303540007500c0080350008140c100d10355120801010f00f00e402e01d0411300c0d4140c00620041100c0d40c05100c1030f50344850322443c06074a01086000b050fa0503231090301301d00a07150000c20300600347c0000f4450402052040d0070014000c1c00c0c80e0b0002001d101d000f901380303120303080b007441e1140840d2030901509149101c0b1240c1c084800e5101c5c0701d200e003001e0040c3c1100340960b00d240f84000c1798074000d0241001b16504040503040c00c000980030700c240741c0d1002c0400034010303031a880303511440d0b102c9400c445e100d041010040c085a20110381010b003071504503404058100c08180c18000305642c3c140e00c45040700400c03940107030385464055142c42c200100c2d030b901c1c0d001060641e04110311541c010100d103d6491003640c0400030b07000c040d440c0c400701c01c80545e07100100d0700404e00010310320304050b40116001084c180d500b40907054040b000c14500142e4594110302c4445075a010030003030400b0464181e5040d007440c5490f6164 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 691435656 1250 691434406 691434413
    0x501060e0d111e0904060b0316031511120405010b0108060f01090b03070309140a2d02011413030f12050a080c07020d021503090d110a02121e0d030f09 66
    0x14610b072000c803845440924042424400c00448442407074001515180107403030304c0e051840c0100140c1c892107000740200201d000f000c0e281c50034407806690b401010746000040110103103009054007100034031001010010721040f0100740f030180d48124810710002c07a41c00604000100303450702c09840c3c10b000e01c2040114900c80d07038001080b40305488001c0002c544aa03104d410890280c0000700000d401c020a18501800c94030001c55810b41541c06911540300b500b03d42d4036205c5100107400c41040901e51210f013407000540c8585008006a10400c0459090400706d0340075054072261503000f161001ca2000b03e94003000821140c100030042a4103103c1d052901c0d507840030301800700c02480880f000f1000101d0b1000c560314610201e24080c0c010300516041d02c005561a41203074030903100e2100c00c0c803a2401000c07090344208411440eaa031074401130200c1c2c0c8000d50030701100c9001040c0b400254000c2c1c041c0c411254044c02940b04000601100401d28a44480342c00381c1101e0f0398210801146080c00e0480021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 691436906 1250 691435656 691435673
    0xb09070501090f06180915080f1c0c050f3f04050d05150a0518060103080a030c05120c0a11060c04030b13060c0201020415091a03280501060e0d 63
    0x4866250802807000c170f540c100591800050ba03085407800c0c80c6044900d05509401030180350950b0710100031a002c01529819041d5100c07203820300901000318446072075a0051040d01c250414620481c202e81038010340c104028101159002420140c0f22400301c5a45441d581410a0f0402d000824100522081d080c00d50b50161046008060040307010340020001c000d020809400451054000c0c074400d030808402c100f014000030303668100040c0f240a42c00340c1140c0c0c00b0074001e04807a0f001142d1441d0008541e000d4018003031518003501409001e000031021684038520350b40c0318075020107640713a0f148465840a841c2e28100040742200764001401c000501350140c0c111ba069030b4201e61500200c0d034800c018400414280e040c01044181000d8542100a405401030400d82c0c0804504040702c0350f08a1003280c0d00c0005200e0001101445452200e44101e1100110b402c100d460400d524902d0415508846040294200d2035000d80d80b2001005400d41c44520036420281c1101e184075120841e032502c010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 691438156 1250 691436906 691436909
    0xc0604030b1803040b03010609090f02120414100504120908071202010c11031e060601030e190204060308040b1c0c1d0102100e0c09150102150718030b09070501090f 72
    0x80e842c1c03010703005a2001000b0001c0d20010403000800e41c1e6250f84a0360000c050a520b845036500007400c103482450f40c0c40c018000d540030450b600c501c0c4402c565030f0391034003212500c1c0b40e58203010743d0048100c04070303880445000d40c600c51405a51042c186d0011980010580b6131786030b00202090308140818031181c4044c0e00c3d40700149809103801c00c085001c43c03c05d00510003c80c1e04c0a0303450b2281c440ca001ca04019035440c044007070b06c110269039195032400010360a841703000c00c2220325900103242107411203501c01c400500041c00074200264880c1c50b691250300343e0344541c00055540070081000c203481c29021040701d5124aa00d0303014040520000c4000e0041d0351402064030000072046a074403280c2c8d100b04203203a1401c84da801d040c00a0111001c1c40c0c0d8032006584c21b10f40c01003581000041c8020381e1000c481050810603401400003c26819403c1c00300700000c3c0449042140d513102c60450b403034140706c401002c2c3d0b00403600590541030120340b291910f91907a000505000012500b0420100d001e1400340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 691439406 1250 691438156 691438171
    0x2070507141c0b0604150905070f0318031407050a0b0411010f0c2003010618060b031b07030c0222050f0f0a1509090309060f030e0604060e0a050f0f0c0604030b 70
    0xa5904c480000070301804806ca1040c1c0000219880058620529003010b406026292181034004010385000c4054030040900107129580842a000000b845041104490301494030b01a00300348250392458200400c2140640307981156606000138004000182005003a09007000c10a184001401520340e0424610242030b41c80e01c144000c07505141b250490380e100c00001c008208107500e982c011110b0000001c28101054502900860030010b080c08a0f4066500500c4032428120100000303110340e4030144c1d0480410100a0100380140c590180c100c1c0061010141300c0c202c2e03021551400c0489800408185c4080d0100c000e00c10401d00614089402002c600e90100c2c2c0d01c00c8002c0c55000046c89540f140901c545030050040900d0751190350390054440030380c0d8401008003907075011030550712503400018054120317001003000504550320411010700c1c547c040d668000d020383c95207420608440c01921440c3c1084442045070142442900010201290307020304050540d110600036076402042070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 691440656 1250 691439406 691439423
    0x30302130e1e04140607020718060b03011a16150b0f09060103020c010e0f010204060324060f0c02130e061305031b150c091003061d04020103020405030102070507141c 73
    0x9024007813100c0e90b0102002c042ea045440da4241800029500c3c400c1d440b0f40886500b406210018903003050040c04c0480e140d5018003400c43c0d003002104401c1103048058010002802c21403e43c00062658113840020b01555030310351480e141156a8040c2c91402c00610312030b400c0340c0070004080c1c2d08c42c1d581c141c01010178640161581a00c18004d801841e000400e81454420b150320707074043d207030150014003c0d211075a03014000c205070f20408500c090404110080c00303042c00a424003440d03100e122021040783c1d44d0300d021904800c00790080b820b4940c514490a00e8103450b080084c920b42800c03c11103412040300601000f006a640d11959202d00400c80721402c0c20040ca04110305e45281000031124500c20a64401221b041881d5058140c4d071004410a000380788101801191358000e118035002c82d5000440c0d0015001c5803180d821282c0e1000740201e049c19420302c001718103500c0c07d10240c0007462040004081d49801c000001c00d121411250151003000f0410510400071041c0b0460039910398003483d40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 691441906 1250 691440656 691440661
    0x70b0c1516140d090f02030c0f0105032d04081b030a0518060d021201170706080406020d0f15051c080415032306091f0b07030219030302130e1e 63
    0x440324810b50f500e84801c503042100d4407061000c0455116950f0f0b100701c0407201c8030010306090003580207010700c035030380465070070310008501405000c4d00c4014903040441000f48418118414203045070160b400307442c0010081000609240100b92240b428001d08004509080000c40018801e2158400404218400c0030f01c1c6c81c8240c5030f0405481c03150989000039500c95114401c440342d103c01c2441594103107400c5078001d0307800e00001b19a00064850550750400c00b03035190f445500203540030f0b245046801d0381d2000f1072211400a1f200b00e1803d00000301c8203410311440d010801481200d806080e40404110890301c10004162008940890320b0103900740900401805050b00181415880c03801c9801410b8070074040c0400c402c5140b03100f02e03c100c504024988405140c0c4030a900d841582d41440314603c1028009805503d000d00f02d010b02c24411074150020b4045038121490801208030040381d0081810704403440c00c015001e018200700032620300940b804403200507a10810008469280911001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 691443156 1250 691441906 691441937
    0x60415150c051005070314010e06090a0504050f07090c0906030203060f0d020d08030c0304031e090603111b0325030c020405061f09061b030801031211070b0c1516 71
    0x42000410b0440f8002c0045260428000c3c000c0e06c1115000074142c1217840001c41d403409140e40060041101501c00019680c03941001e0740101400781003a16103228100d540c0241c08410403c0e94080c1081c140c1c0400c9040182c40c000e020340601c3c0e08000249801801003240079201d40344141a07200007251520340e03124090011591201c0d00e00341c003a00c520030000070041b54010140055000d00d00c00d85e1580400315480f401500b1140d11244d4010014041700300c100001e80c4241c012820365000820030030b1809c542442c5100004001c00082c0c840b03034001080101c5024070f480b4200c42e100944007040e0700c015920f030342c0040036200b102c14000e00c115078034408184a600c41d000c6001480c51610782039410703240d0036600500394481900c43c200c0040d454030000030000c2c0344039441040c11989034440c800e180c1d007982d03503003520007210b15020402c0118401d1400c0585104104100003440000802c40d03031080c2c3d9000b60f9040480036070041c1c481013264024041402000b6924203000301940c6009141c010f02d450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 691444406 1250 691443156 691443163
    0x8030705010e0d0306060c200904121403061f1b030216061115130c06020c1905030c040e010906060f03030801080304151b020306100e100f0e071115060415150c05 71
    0xf400f6278000c0c15040411003002a9210000320004454441c81c815050301c48404c1094442101c0c4150084080c0c80c81d0340e60026060900352a07240790303050145852450006006000303158040940042e80a441d0080b14154860400d40c0901907a1400070b20151990b0b0b0500d9941041c11420b030540c11300200007074542c031000780503046050303849503140c030300d45595081c003d40e108071020150380f28941990450707821642078440d80085860240191200007a80c108001c001c11000ea132501c03d5540310001940012410300c0707400c020705800c07403000945504604008290002c1604461026842040b052240600d038441d2030135184502c0c6031450300986104060501c000001200a40520400c010300900c0b9052030000c1080d80d1004004072040d540340e10084101141c0c5200c0c221001044039400c3c8140c4200011080c0d00100e1400c1084014118160051424001c50902c1600c902d001050010341e14040c02210140440ea00007138825034103001c03801038080004a400010b012003008020304120090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 691445656 1250 691444406 691444463
    0x50712030b03030406030509010b01020d0905040c0c14031c0b010806040908070209010315110f040501080c1b0109020f030a12050d091a0402030c060304171308030705010e0d0306060c 80
    0x50305484e215903603044d003d40a420161044410f80d401c00e03500304000e500c0010140c1c242e4003035940e12000035140c5418400149403001e4040100040369880034040b6400c1640842007100304001542c1e074108103140d818040c0d00c520682083c00341032207030300b610307980e440806543c2140301140c00251600c042d15150b000c900ca03c20f0003d400000550000090000c10000d8808800c05007101348500c1d4a0718105401e98801c805083e004000c00b4030023803059501c2124415802980041c0e0b141c03510f080ea074800602c0740075224650030140c1d100c400000c01c50400701050600644198014114020b070780c0e8411219042080251701042400b0a1142c80056990059240349402c00c1c10031014520000350340c0c0c84c0044c1280c0c00e034002c0c0b080c8410b041060800c441109d200da030704064403001142014101105c40da0041e81c640d603a09420102c08240080d00b03000038250300b4401c600001e000c03803020451b2410095804900e0701810714048040000b42d4102c2d5000407002d60114404c159100788070400180002d24 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 691446906 1250 691445656 691445659
    0x1050a080f060604180507020f0c090c0a09081605010201061d16031b0c050c0607170901050f0f0d051012030c1a040b0901050f060d061e02030a02070215040501050712030b 75
    0x100841240451202ea003d5030052005500f5600180c200352009c69483d01c190117001c2d0004003601c00242c619009101901c4060b503075150207280e03e541e950582c2d141000c0c2c01c6038183e0410305000100090b607024401e0b1002804010300e4420422400390104801c0000244540564405290071401a501caa0711002e20301020710200300821892040041091001540c102c59070312442c0c90340c5625150036015100583c0d481030141e000c541c20265612466045901e000717041c050140a81e9003160804005040c291140004464542eaa100c1d002001d4030800b40100c40d5010000d0743c2404264035800d00080d0310b50301410140001c00861400e0010401501c00c0e0b0300e0a1f05030b81041c40f0401620690340c6010384440130007400280c45000208806140c1501e100794001c1854501e2000500030f0b03004031216501c030084007800806a4804682680d108076424242240d0000e508401c5280948100c5545610740d0b0b0b4850070b090030f1900103002845102009011259440040c400c030f144030b608101d502040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 691448156 1250 691446906 691446929
    0xe09011e140912070210182d08060c090a030206070f14060f01121a09030903071202030309060c0708032b1a1324030b010501050a080f060604 62
    0xd005228401058000080c007065000341c03011811240c1d00150484403001084161440c094543d403c012210f90035a01ca0703000e110b030304254808220392203040c0500601e0039180c03400c5028007540800c04400303800d40317000031280c030340c2c01c014070228000142d81a03000c4e0400265507034038003140f00082c6000700981e000a40c009000500c0c4010815650304102031148207860b409400b6031300b02205502c541044452030030907910380004004804d51018050036650140303c2c203421880c145603590400300002ca414101a50000591500c1820b003002841d00030443c410886400a050ba03000230380760b02c20341c90b1242c4035400c04a825180c150041c402c0b9401441244201d076560f01202180300315071000102c0015105d251a03000500b80d0780309010f180d407071a07260700320101c09010b1402000300c00805460800700280e95204416070b9280c55030960100e0340241c41040c038a40d45945801b011010b4140c2106040007014054070b69125041045190480142c1611740c51aa403031601048190040e0341c8000c10044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 691449406 1250 691448156 691448201
    0x30718031505010b07080a0c0201120e0a0506010b040602251205010c031104031101390b0721020d020d0216050f1225020909100c030b0a0e0901 63
    0x16141491140c0301201c01c428000b40c0ea8400da00c01c0240034605000d00130006c00c2094450107445040f0a0400c80d2050408448030040e84281c03000701c1300f10141000c00ba502040d08441032003810000c190040210056051605081210081d15104101550842011883c40300d0140031403e040784000361811501301422704066007003035406050b4520062000c41e140500d5003400e40c00e039100329001d50b500007040c0b1180c203c0c0d01004445100034007400248002140d071781d06417840000c0c002c034161f903c404001410b01441d0780c1403c002c410303805841a02400b20001841204c0c46946004900301e006c3c5940058541401c2010100030740304440406a080748002003607400a03c0b44451440c180e4000d408807680758068884056550001e9285800800030501c0100211600041c0c0640301494103000b03004c100c034440d0b01040d50100b0039121941c064000c0048680303880900d2188018451503460103204203112031001c02c0442e00c0324001d2440c45603a03400024a0110250400e4849402081c03900c003480 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 691450656 1250 691449406 691449413
    0x30c051e030307031a010c0b100e070909180b1305012c100e100e010902060417061e0c0a020309100906020705034c1505030604031403071803 62
    0x90b40100d4151002c24900b21003c400c55410310130302c940d15901038480205030308103616809428030008040c05202c0380300758404100c1088001145000d82c03502d455240071036003090720308030584450b038401c032246800f110034036030208182003201500084008582061000c05040640c00740c458a01c086070740500d08440302c8900310310b00d005008030b580700b0015910b1210240c21210140c0d403040d90502d003070790722040c94440040c0844e8003d03410910740e0705c00000c0a1015501003006030f00b2550060901c07540344020700c01c07200070900001d40d00100310840880414498a000424181d02401a440954001c54131020f840e00800c100c2d03007514401040c0300c0185000d910010012081405090010700039000006014280042e5807901040b00011401813841c1642d160381c449081582c406d00214a11002204400e010498130000080c2204010807818800010441184c1d01c507841035003c2d178009010807002c01c3c3c3c880500c0503148048072420341d80742c4030f25208452000d0740b8240d0b500c0340d4420b0751000042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 691451906 1250 691450656 691450663
    0x50a1410180210080708060603070201020403020a03060b04110c15040c0e041103010c021b190b0a080402040b0a151206080708072103050d24260102031003030c051e 72
    0x8061084075214160030324030900311042c0e1401e17100300d000710754103501088041c44e00101a5520003540c1c4001401d00750b485d000900d01001540c4141d440d076545601c1090f49091071701900f0710b41028035035a00d03d000c501c0d0700c90995644521400d1140c0444040104003002511607030840201900a02000e581c02e050a05484143c440c40c03940744039602e010ba40140c1280003060012003e4821880100203580101c1408038045d80703a04a0720317100380c2103100815844d035414050a81040f0301d94501005141501c10700c01194a00417006204032800081044054030b003000307411800e032031171910b020200032541a80000d0616078200901a0040c0840031802c49400203140046610b41c005481c3c004022040c560000d034194030020700003410401c074041000240307030014403d00c0c2c000750341803000d460029501002c2c7c1d0090b0304885006080d00084941d211010031030203489192010003145142401d442c211004d18062000030309101840311046c051040034848101d070500700300c02d010303100881041c00070340713 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 691453156 1250 691451906 691451951
    0xb04020109051314150102070b0903010f0e03030a0e0111030c0706090c0b070c09110a200618100623030c040507020a0b01080c0a0603021b0a031805010c050a1410 71
    0x2644d070040000801300e18108030351050290041c2c0181404508085800c2d28550210500c107802d0b41d201c4005040900181c40b0300c18030f1002c580007441c2c030307410700e9429442901c0d207410120318268180071061451450b810100c94010f6a1061600c1d590715052600d000035280040020300034020f80000080c40c0c1408000503c0c025105003a00d80c6d606464a02c100300300c400041c02d1100140051100c0d01031540a808403010f100030071918102c42c016292200c40c602803040750030040445a1005c1d11800500400c2444e200c0c1e0b0b04000d0a01195082081d0740004198052410820141c0b255180042c0e850600c881d070f1450300090000e0100e071410120180d41c50546400440342051800300000300e0a4001c610400b0306803004001030502881c10b481100030750003d00c40701001c0d040001030908000300c102b09401055100381c44038000c151000414a55030f400c01da000c1418000080040310003c1e4001c180159226400190300e56012440ca0009103401221000360181e18a814070084406052800c07168 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 691454406 1250 691453156 691453181
    0x8040317090d09050a0305060121050d1227150f0504060218010903120302091203030a06030507050307320a08100c14092202180a0f06020304030b040201090513 70
    0x85099035101309000050031039203c0a0815001480140311103401904000054041461440070140054a6450819111083c0740c408202034501c54205840d60317015240308541810080381002201d82c142042c0d210803900024075004c191800e0440000b101c2e40011500c6106203001c000900e0a85080b10096104025041c44040c00c0803c802c401c0d84a8280441961b500103d05011500e100ca01500a50041c060b2a030384172540e10003800e90320b90200065413182c0740e10f4002203601c80c82c3d03003007182c00c2c0000303500501d00a030026201485101f1030300100c143c03505402c081040d00c90005513514010016031a1207d54080c00080f00000c11902c00907e4000e00142e49034200182c102d0903a09480200385c0010240344103405110404040c5002e01c00041c44140580d0307132080f41c200d843c0d001e404070303030156079003105200c910b0381c2040990a1036074030040030b05042e801030750300c1d9820910b02039940d0117544801010b92000c00c0005045921511203c00102400f07032182c42c80c0d070f48003d01c03003010302891400107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 691455656 1250 691454406 691454417
    0x60807031401150e0406020d02030a0506041a0a0302060f0d05070f031a0d120201090203030f0703030b0a0b0324060a03050402032119020a140a05070f080d08040317090d 74
    0x20107041506120702c0d10011459402651607a242420425525400030000d90305182c1c00c0c07011303d01d0844140002d520800c2c182d20000f8041c600401004100d441c3d80307030f5002110150700300380c00003501c43e166101c06680d0129070759a00d40e0000007100381b4901c103843c0c03014161170500052051180e08414414541d08940d00c0038031080c003074910b03805210701040354550791000304049214041020384c00c10341e0b603514040c0b0001c184841d950300400c0c5140d200b8400101c0c660b000140ca04207055040c480c206d0740c85001ca81d200c42d20f629103000540c2c0d030300000d08918542d031803120314004a00b4110f4003e0f130101c10302500c4075440d01a5458060020101150242c0c000d0151408450b40c10042c24443c52020400f2401a401c0400300010310080807030b000d0700d400551240590302402701340340030703400300500e8540801844514841d20b01907045c221143e01078000340d651184140715000700800e0a400c508030902d40a000c65503181011030345126000341a001140c0b50030180f0021100101e18503484c9a4640c8a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 691456906 1250 691455656 691455683
    0x1a1306050c07150e01120e0a0309150203041401030b1c030203040608010b070c0911090616030e0114030714120403020706020c01091d06040b090c070b1303081603020d06080703 77
    0x100303603a5400d00303042a00043e84c0c241548607558010742e12580b52400722400001e90a141d503129900d019400c00003600070038a5442d003000f04d5010b80c211000040c2c1244045c6003003515002c5205e1403c800d44c0700380307030515484401104c2c003900e0304104041c10101c5a032458000c038800d410003948942c0140690000503800c00c002203807110740c60044901555101940d40b031800e242079100310040c84180503840794035100300701820b05960ba00020b030110000508065510100b0b524000d004541440711042c140664545102c142c1a0b944081ea41d1182c0d403414078212a00f5600d5520a4500c1046003e032a0101c41e4002c2c0b03c10325900184000564006800b19480410480f0042d2146512031040001a0030440d80804013141407005072a00140007800114200f0b55a03c00601d52490454880c0c541c60804039918090040810450350040782d0785c4400004e8602644004064040c01404d400030484508107000e81c0d24826070450b0500800d12408100558442090f191151800d01c01640c2205c02d4222 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 691458156 1250 691456906 691456919
    0x80106090509040f0302070b041e060201060605030a0902061b01020717090a06030e010b0d050607020601120f0605130b0a091704260f06010306050423071a1306050c07 73
    0xe904059841c0140b03a000b050b40d86565440c94140d100c0c100b202140180b49001070080d080700064030107082d030304a1844c510034595040348507018466101404680c1815020002103400004413038214034409008101c1810b94008101107200380c00e00c1e000e0b02031950b040c486118506501034030780e6502c14a03034951420540c02c00c985840c05030440e241d90103104d06a040084602aa008040380383c40d070700020680c1d0b40030364000342009a21000596068021108010041d90f040c80418003400140241e42c5900c150343d25201d41141d0301c581c1c0145456581d6020508280d01c080c20b0740000340e8811031130f01c2540703003a40418018101d1840200d411405442000c05a24244d0342038a00340d0b0405c1c4440d0b815085400b500003080c0b42d41d0040511180103008400c090203a040c0105c5010718000c0d0070202d0b107814589040d12107400c20080500d410400306201345580740c008a100d6003140c0c0341d140455000b05100420402c68031645100c9614403400104c0050004c1c0c014025100008811341985d1829540d00b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 691459406 1250 691458156 691458167
    0x302100e010509061303050703230703030906140912030d18020f010f05040305011401170d0c1101171e0c0406080115110303180f0304080c060f090303040e0601080106 73
    0x19103180031030310901083c0c9403400d01c01c0203081180740c0c01ca24111060f56a850712410a0300540080da038109200004200c21181e100300420b21410440c02441d00c0b5255403001840e02081c0d000d0340080010101000c1200c41514058828001006040021001c0d281202c0e0360349034801d108420b845d03800c0603510007080c41032448034501a034000d040c14000140c440300460368900b410150105200c0b0901000c07003c0380c02442a40b030541c41240c05840c0b60750503c1103005031041c0c2c05000102d640c1c814007120165a61000101c001e4541c0018036694004c0100d00699503a000b401c035054241040c0b204100c0490301c591600d090041c10503000542e16122824800c10380d120380c0c05104040341605004200b15811070390350749402126890b282455804940b0b980c2c0c11513105482000040b40c241458003414030341400b048058603030001c02507207054509070b003517074844410301d408902c20107000c0345600d02c00002d0f2049990500c401003c1e0303581c2e19116004e1403040d13281038a249000600380c60001c5035860186 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 691460656 1250 691459406 691459427
    0x806070f0503010506070501020c19060b220b030c040e030403060b0a1d04050109020901030615240507210c1a010b0f0c0c1207050103140f22080a09030210 68
    0x2507440c42e01d582e00700001c0c4107036588034000489031594201320002d030040d000e10180d0300d0601680e03420700014440e07081200c00d403002c0306e021610440703840d03039a1004034500240c3c50800464100001c602031400e5030009040c00b0000d00c0882e001410030140c02e081050120080007aa0701c40d0b00e080208200712005d11104070761a00641c0d070364070b20ba0150681d14403c130703108480d40580720b54004280e54a1503404650301d01c6082e80101c1715039459074022080c000004034140302400303203030507003071844042408141e01c01034503610900c00703010f40001e4070000d0100c0e4a0203403d130900c5032442400316402c1c07502d0013040c0c400070388000d4410203507036820100441c034903440980c1240d1001c0718150416040da02c04800315842040340754094440d040000b046a107030701c0c989140d203550550142c08101c2ca0b0000240c161117000426490b80380c2e84804000501028484c82500a0848010301944100c00e070f81d15000a4030702000504000f4001c0740960b00c0b26485070306e5070300703a03482510308080d00d41040300305a6502030003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 691461906 1250 691460656 691460687
    0x3010f0303090801020421050304030614190519110903070f180207030c150f0c0908010e03120403082d1b07051e07030c08031b070f09020310150207080607 68
    0x703800845447d82182c40d11210700b40d0041d01640c0c902076580d0703281d00441d41001c21900446440c2000c11520459a040d51039213420545c0c000d001e6443d02000c0203025164030740140c1a12035481100d0b07042d0043e004152000d0020190485240a40b100044800d20750140b06501d484c00340b84e850440d02055500a0355030155041e241d101c40d000d240d55418900742010a06414450303980d8000310704010090056031413442c46512101840741c1490b0308182910310300f40c0018903c0c2d0040107018218060840020361044d090729003903400d52620070b108500f00031108820b081061800300b0620b40480210b45040c000e2030400100044020f5800c0d003d0024054080c01401c039800010340224000070750114100300b0086030041c0c0705c18544070b954200032045603030031440240d4004144401c2021101ca900200c20303032514010450986403140d101507034141801420903090b004004902c043c0d00349030101001c4e2264181c481200e14188000070b594080611a1410622800000c41d49590090f034a0f000c2c0d1004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 691463156 1250 691461906 691461929
    0xa150b01020f12031b12010603060b090906060c010905060406060510170601030b030123041a01030c0605070c0e01080f0d05040602250503120d0f06050916031103010f03030908010204 80
    0x40c1c030f110980f090b4000824181000c01080c0c0008100c1503114000c0079000154080000d4a504100700182103801e01e030040d09000400300000710465841110050380048210780450380c1c2c0d02e000105501400e00c00303000500501c200000d110400c00d0a4204c1d03800c0d5801550320400b8603001401c100c030703141c400000c00714110405038040380d2194482e4001900014020b0b0000c21b8822961408001127170380300c03840c440e15071001030030b210401c004842507089102901d900202c4950454489941c6180c00b4800c2c0b40c24080d000030f450041084070f2624400600800407003c44660f580c000c21a101d05000052022034015416020500360080059a017503450395401401c000388507680004d000c01c07454018442c0c05082c1e01c00005c242d54204039001e034031a10380720b03000d446101d10901c4505a803c004060a9054184401800182c03030300e0701c62a81c805c1c880050300e0002e82c030500050340140020f1206160400f00000040f5030f0312400c2c00c06008480c401e5540308030159840300c0b41c500b01c3c0a50b0141200c00c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 691464406 1250 691463156 691463173
    0x120206061008041101020a02030327030a050c0904030c050a12080612070b0f0c0105010b0a110c1c0204021c1a031902091f0603090b060102031309020f0c0a150b01020f 73
    0x20307402c0d40c4c50901000c06004aa000c7d010310b800007131654211001c0e0f1409800034100180c06400715420040b0300040c1071b00101541c16103a030f5105c0c0c07103900c600113490040c082d41c1c0000d401d0610810200303202c1a00b0074165803400304070b41008201c2c0540c6c8060100403c08180102d1028240360548441c00340c0c01501910500703041004488a940c80f42c003102030b14070014490450700c09400e21840c2d0003000701c0c0c04003559401503000e0107001c248485190080c1c61b08111802c24103502c0b1040c546d1f00a25a12030f418a4078140b61000600a0140240608403107444038551a41c010250384103030001518948051340d0b40c081c260070076944c3c41103814001e4101214142030401400c000b06080d811000300c0301003180c20800c07880f20b101500b844d5400a40060340302d80d9000b040c05100300344d0380e4000c042071011b5450034294000b140b4414126100e00e641d040ea00050185290100c0c100344c0320400c01803020784030702c08074034280192021a4409a40303000303803504050b60069800000c2c00d6925038018005824551b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 691465656 1250 691464406 691464413
    0xc070b0610030209040e07060906020607051c09080a0e09180a020904020105121306050c040e060114191107080c090a180f030302120106050f070807050304030204060312020606100804 80
    0x280590781900c0c090503000e01c5a0051503655004401e80e4101341341c010926a031600000820658450740081c00350341083d401c0c841316036031210441c2c10b003040c48104403c80b54005080c58009295250300540006004900c4064583e480302105040b03a2044402c134610762503031010204030782c00b4030080c43d0b1554400c0405000604203d61036540c4103005045c02d03818060100102c40010300e0480d5058100b0300f980c140e0004004d82c9200c1e06811000390120030703040c030f8200b40160303540f448090b000074180601e0071040c82046040e14202c880005424804010f00500c501016024180300010307044140560100459030150000f2a5100d8450050004850340c40d42044000241100c00d440601600000c500d070012030b01c0121704401c203a2003983c005907504084000d4480071207040e00f0210420208101e0340103010743c3c04003903c0c0c0142d0858001603a4084902d40b86155109540c4002d402c5814034800100b803288000840c418481e03240c09882c2c00365603174001c01c8840ea0005107401702244200d400306010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 691466906 1250 691465656 691465669
    0x120908030406050403290f1e1003020f150a031505060c0606120a120f1d010509040c030b030a1103071202010c0b0601030b030604060209010224070e0109031a0604050c070b06 76
    0xd603074211140c802c0c65004003624407170019040380d10300d5200141f6001d01140c0f42580e02034070100e1014000803c507905249802d030217403d00f94070010f4030030202c444105c602680c1d0301c0300300e40418042d40042c0d59205c80400700540136094003850707171018001903000064281014821110750442800282c48a6618202000350410904c0d0000b070540c0b051142c1500001c2c01c1c841905d42c0030850b078403485170f0380d5008540100f40f2051207001d00041e5206d200c0803000780c1d0704041914138a180454000c601d0f003452120850041c120050095858400e00090005200080a0000d0000c105900391b40500e0b45072600400070301c4000c3d1000340002c5030300e82d004001c030b030854001d41e0704441e0501d004107041040200003450310790191015613686500058019007980c04011045a001d183c0544041d5449002811703101e612000b8160343c2880460805140d95030320a444840155900030b020b902c540a03560701c60058603400f10b44440c001ca2034800071540d1708031000d080d218001e0b030150a100e06a521031090204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 691468156 1250 691466906 691466933
    0x50606090c1905090f03011803030b0d05190201170708190b06031801050924041118010e060607050c1e120c03011103070c1b0909120908030406050403 66
    0x10498042c00b02a4260350704800103050b0a9903691450380750180ca00401502200c1203010611036031611401d0048400c50070300454041e0303003606002401c03250910208524002c11700005146006501c0c0c824a84205680c1c074511090003a41c0c0c440840e85854041501c603103040d905000403d01c20b100252954010002c0d000606000410100c2c0742e442c024082161740e0001e5611803082e1030800080c1d86044802d208840c0c5c000d9540d8020000c0d04c0c080ca07440c060384505030107819807a60202001034240084003106101069010300390b0f04002103100d070b05040010080c040c0c540d11014110108030305240480a80740911f4101000d001ea052894041055410b82e00110302d8004072002c40300da801d170f903807250100401c0c101980a4211140c1c00020107003125204000244968402e2091100c002e5000c540d81c1405a40315890550a45070859082c03040754441e4000040941041030b80c404110252400318940c03012612035105803a01c0c0c0100b29202e00940c012180000c90502c000c002142803410090b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 691469406 1250 691468156 691468171
    0xf0622090f0e0a0f02040f020d02030412021609020d0e0616110d05040b0c010605040501060f03050105030d080f0c043f051b0d0606080703031205010f06110c10020705180405060609 79
    0x1f0702c2c3d8445003103e002e0381c102d4004800c00c580d0100c10003040c00407080c0b0100c0880388a1004e00864201510780c850107801078015803028640c0401c940c0c0b605845540040f280c02500f00842c0c8807480e004151741d80d0301c190150460300281917540c10201d086c00003d040b9480c6005a1502ca0800381403940070181a040400714035410340d01d80000081c01e48492003003e010700466900d240038207039000805000c1e0341041e407040e4001e0b80301c1d0f2032280c0c03031560201d0426004048840c0d80d070450385604494244034002d6800171040c2014003041d0046818500c0b90111514240c4076a004504540304002c0a01d00c2d40c80c40040c1a94003c0c0a42c80f91140800000108070355000b40484114200d6032195011503c080d00203400a40c0044001c1c0181604010400800e503c45003051081790f05004444a6004543c401c0c401032010040384158049402c0c40404a403c0e0041e0803001002030600c2c00941c3ca00591082500449510090b1800040910070952190341c00000034000350320340c070082c0700c3da1130300043c00130 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 691470656 1250 691469406 691469411
    0x406090204150503070f0e1308070611040e160206041b120506010801110a0e0402030705160614070c081806090d03080105130b0306060f0622090f0e0a0f0204 69
    0x540141d480348618840011211030303820040f402c01003030501e4000c00b82c12409107132000300420814551280412a401604c3c9101801e45440d54540031245000303592000380060b04042d00214101c10600c00b600c2183c1e00d940d4032a81d5504c0f0761000d490ba070540c0220400051b0054400100403c1040e03051251034501c0420300074100d940c802e43c4200084002100300c4507900f1140042107065001d008022410101e03c0713626143c00288000030384031052140b513043c05580c0101c0020340041c000c805403181205c18030100078800d85145800c00091000c50380c3c801c0c40607910800301d619130380302d10341c07091001c0e6100000760325240b1701c030300e2a11401c500001e09540c8201d04010304a4242c4982c091020306501c41d0300c0d1140294180130800c20109424017600200d60315160043c551a60001005500608280c60a41501030f0400c0410050321a207480100950b1400101c03810245505040340101d2b00380da03408102c40b00401c0d40040a84080083c50107441d4000010034001c50700c50800120300ea44001c000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 691471906 1250 691470656 691470671
    0xf22080607350907052205270a020114210a0e0a05060a0c080403320415030b0f060a140d0603030c110a2108090303040e04020118050d0206030406 64
    0x81030480242c0001e0001c00548000c0c032070030030310401c600c8019001c11a42c0c020342c08003003880300c4110000d024031902d8030740d11100403c0c11201052000000e000342c0c00d0212018a081d80341c0b169070303800d940741c007240060b01c26a010040e43e09040d007aa840e01cbc41740ca0308031400a25101240e1000c030006800102d00710354500041400003030410400340920f1141014110070710700342203207100303c8064a0b9000281f0004008100005c0d90000200410280010550448004000c40440316181c401000e000d42d207000900030403a0248079901801c0110341d9a000d0002500e030074248420000b580941c980c00c0034040c045403d40034021040148400c90380e01c9a1030401c0401040c1c0016102c660b423041c2c0201d040d406a441c28814640f40145040c001a40e1103220ba510300000e06d07070b8188030140350140d800e00365594001040f80e0b43d0704031206e083d4010203e948941d1200c00c012103141096504074042000000c8110940d542401242d003103520092910303000c3e405a4081c8000c641c001001105d006955564 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 691473156 1250 691471906 691471967
    0x110c010c061113050a120203030f180d050f010606050412080a0c0b010902040f0e0405330103080d060f210f0501090b0a0e010603050c150f0f22080607 66
    0x9008a016640800903d55251000b071140851180d0800100022550301003405038400008680380c031004070b01c200e50b4400b540403480048030040ca2945a2060080e00c0b54402e00900040301d15031a00410001c0140555031030f0306955600c1284100200020383c22158804200010040d118001035801c04440350f0807990768082050009822083c00d42d9408181400020017014200001e00f400020389800d508107030f1600303940c0c1d242c50b41c00d0000c840784040300080e03020000c2503400c00c0000c103080e40e101c0740d507184e18001400c3e400c85042c00b10114a000000204084180c6085040b075032940c80152980e40c042000110354102c1940036102c00181c190b6200004070240308201850b4021801e900301400d00e0400881500c0440130303504a02e0381402014404210081105400740100b10750003101109900e103031031543d000785080c4d1044084081844080c1c5940b890050448a00c40c081d590f040400207900c01d20502054064280a50b114030b001038840c5014803188004020b2070607a030302c40981d0400c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 691474406 1250 691473156 691473191
    0xb09011a0904171b0a030206010b21060102121308010b0a060c14160902070302061b160f0c030c0f0f060504060302090103270c0e060d021005090a06050910110c010c06 73
    0x4044031380c603485801e07441c00b450390500030180501884480d007403414120682c150f48001c80c01c00f0b001e00c81005000451081d038001c001c5804c46a04018080c0d8545c0c00f0003000c424400c0e1a0701c02c044495007804032540c224030740340152100350395064858070290040da403074141500b030162241c030f00c0740d01c90360b0031220803500846e16007401403107d07920150307654100d03140007401c0a034064030164510744071030180405d00c520f076026038a80c04031000c3c202c07101a4041c200f1000100840c44050203004014a012041c460380d40c000800740d44140c000301c55031a548940300c0c42d144141c0c0c0325460006400b80010b1000c540b20381c0041c8150041407601045060716146014000100c00004e030701c0c05107007001d004080001511182c40108011500512145000008070311500c150480003482240c455011104107401035058401c690350203000c40500ca82c4501d0050619408020101d204007128441d41c1c6c00745109080042c04082c010000d007450079440001902c0707408800c3c404681681c0c907001c8016003c040c2c807 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 691475656 1250 691474406 691474447
    0x70309051305070f1107051504031a0f090f150702030702030607030c11010e0a03030207021c0b04030e06091810030b0c030a06231311070b09011a090417 67
    0x810010756420003400c00b4214001005990007403213217001360ba80f02c0040100c0c00b20f00b201e000342e41d254008140004100064840d5400017400e1b221000d819104184d40c1d0104944240300c10000070310140c0718840c09540d2004080e10404882e40811003207101c5880222807250480300c0c90040b13074282035441d4006410704900700c806c100041c2e618040c4d40002d07940144c0d407006c0304502c030700200411181e0408098650300c0c3e689001d4145500000c0201c21034035500f54040101e1606404512760203840e260400001800f03440507400074078015055215450400121103044d10010003100c14541482e14104140e1801446a0401480d02c8000000325504c80101845101c0160006507240b4000c5185d01c21185560000201902c50001d0144115100026604003003c04c40c2c14058981004903804080c025000e6005004040481e040c010001c20b940f046020705c0c4001700034000384078442109403c0241b1900309682c07002e01d020201c3c0110304803841c0d10200301d069414851a03c0b040000d50400034504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 691476906 1250 691475656 691475689
    0x10e0109020312090d062d0516031a010e0f03072402030a080a090219180b060f092115010e10050f040c0306030203190204050912070807030905 63
    0x1500081030461a003840656a11500007003400e0505031018040740800c002000300400301940c84482c800c42c60340000c4242c0d2001b07028185501c0f450011000b460280c0001c0d0f51001c00c00004845408440d80170f030040740044901c0010a44a814482c401120030115031504103803c107100050005854409100340310140c40d003505e600c08074840c0c0300c280d0030481d08950718000464005000d0002c0d840d0f40208500c1d0414454500491507a40c60700005040203a0301c0d2210a000c030110400082e0711006004d80098105507000c06c0204010140901402e44260401803411110803c42696146442440c4031780d141e0b54071800140f464030ba03148a5203042e0060180c2c100c000c4c402001000703060138003001d841d8005442d86000c1005458600842c14804682e00d80320b200d00d8a61701c450b400184694080c500458006048403411810003010030a07110f03000000381d02440c18040010640080058001c4400d8038441c0c0f51132610b01d032619044900d03041440201e0400c0180040001d00d0795500008400386000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 691478156 1250 691476906 691476911
    0x60f0402040b121609061110050106030b04051006080a09151109150403030903080a020f0706080612030f0a05070f080f0306090a1401061101110c03090a12170a030e010e01 75
    0x9506040c1c04283c800420143d103100c003880d8240e04140e4001e070040c0848849040c000c082000c0c18038110700b81100e00d1140e050721860030000050140c2d05402c0101c2494007900d041080740c80d4441c0c00030030304450380076500110f465403000c150841401d50080040038000c0c00081c00351600340c03001c4e400383d44001c8ac0b612403040c3c001c50181c01c9840c19414241a00c1c0221118915040c43c550700500082014803016045030404241542c8050081c0540201d042600c420b462003980c41b04409400d06805a50700d80c0108801582c4c0d0300701400c00802c03205001c0010326400e080c480e00400440d0300781e005460460f11035030215012400502c250f030140c40910b44120203a43c403460004180204800001c2c581ca60040c01c4c0140701140440420748241952032500d4034807001c003031480c496070142c2401c115014180c80d0000350807502c00d0f8044060503102030200d8528020341c1e55800c4849a4042c0d0340e0b0082d04a007081061491465100300c0101040303c0d550a004c80c0e000c689000380380c210340540d082402c043c1d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 691479406 1250 691478156 691478167
    0x405211e04030215030928050102030a060303020d11150402041b051e040e0a050408130b0405031c050423100c020a061103120406090506041b050103091505060f0402040b 74
    0x500040314104500c90000480d0843c03400e40c80f001e039a02d441c0c5007c07520407150607062098040c10a207040380d1168001c0c00940d502e007062045100180303075500c802d5005001e142401709a041c412810400c5011005001302001818420204c0c404a00540126030041e52034136003042d0307045001c10340f1524110031b880303440e1240700011501d1a1040d030b0395400550f4110401080c406950b01c4503041e41c00510b4642c00040c1542c0314601100c00d032080807140c0d2140000040e0000d01e01c01102c00a000352003040d401d98060700131000e10554403255209001c000300e603003070000f804811402c051071503010101650440c08402c601010178590001c91016000148451245800b541800e81c810b1000700700d646846c902245002002548900800c0f10191890250070702181c20301c2030582006018941160a8a885092500d4140d2401e042c0c0040e0402d00514420005210b42c064031400e128540c1101c04c00c4c001400d070750703112801044010b1005600694100861a5607141e034409800134142e10203a0669a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 691480656 1250 691479406 691479409
    0x706050a11160618030206030c04052d0d0f062a020d0926061e0901090c0b0a180b0912060103170c030d18020103050105090405211e040302 61
    0x1048944034a00705980b12021691490000781200c0048030324600d054840200384184820f00e5040641c00603600003400310510038056008070040c0f0448600302d84c1400030721030786101181011006c50131185514006040100c4134100801d40d010f441d442803d55501125a59507803c041750007808045001c80170124070741401c842c335298044140ca0482c001440100e2032004000c1c020751060140e440303804254140025803178096684c0a152622010685d4641d2603c031710205a0320380780c00101d80395115044003280000c0018805c07250003641004910b40b54508010050540c0d03442400349504010303500481003080c00c0e901401e0b00203020007011059171242c9010421034400c4440c5407500f541c0d007040d001040010082601a0001072140201644402c08582001c1c19406040b000c401010b080c0481d140c850240c0302440304030b440c400d0302c0030441a62034805000c2d800e03800300c42c024080d6214442140f1842400c1180b0b01b03020001c2009076181c601c0d5901059507448040110f580922404034061045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 691481906 1250 691480656 691480667
    0x30308060906030a230f03030903070b0c070c09090809180604060b090901090b060f0a03060306060911090118050a091b0c031202030603030706091a07030b0a091503050706050a 77
    0x44842100200803410076a201c041c0d8122502c60000b0314410081420f1821713007410310402c041060000141c0f42c41e4a494100c1c11b0700c0c1d60002208a5090b950300c000184c07400c40c240199407415030003840e0030790300905084984006150450041da01c56006000d45403045d921030089007a00c0844003031030039113800c2139014070060b6480c80d002a0307a031050174407070884540c5400c01c06904586c045000850000b0744040411250705c950284010040703000111240c1e11609a001501182d00c41d003420420b5940c4c0e04a01002c8940041d54041840c0080020800d10340c418610660800d010303d4000c2d0080c2d5031f6100141003070995900c40b203040c5840f1265042030303a001d0501010b06054a0400c0030b030ba410240d800030041550b6402c00e0008580c040003041054808005981e2110f520020400c080d003074074140b515a000f081c0040700400d24403540080c02040c0700340514034a0450213840c1142e81c134180417422000d80341942e07540f8203804d948000000441c808200003c000d11440c0c4903d030350741e60f80c100c00606 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 691483156 1250 691481906 691481911
    0x130e09100b030601140d14190c0f0e0402010c050c1f0e03070509012304050a020d050a11031305010207050604081b07060c080306010309020d0302010506030c0906030a11060c0303010303080609 84
    0x1094010300f004110001c009042c421100a00702e903404003800142ca8403883d8022001006501440350303501c0603035081c0c00c001c2c001d40064004d010101046903a542200c1139581140140c800c0d46040c20013040055000c0e02c1e464180504c20401c0e901249a03907030103c1d20504000c0082c6509400700710200341a00d400040500d00b00f0070503400f9104035424040031078402c1d40184a0a12000d24500311141074814410040881410042040c4514240344501d80c0103900804003130400640381c070002c102c80340302d50b104800484140b6180fa41c11542c2d0103404c1e142402c9003400648443d5002c0104500081041c050b0700e20640c41070640c551100c4100c856104580d02450740502c3e19400101c0500141da0002c010440086d40405940d41e00e03600c660040740500f840550083d0001c07400381d0703030404142c3c040d007100388601815402c840e020034000c1c0400020034030546645030190010b00256000c0340e1b5030302980d07041080261080d40b41c40840c1800c0d500c2d5501c2607100f54001052103040c0201458001c04c00368 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 691484406 1250 691483156 691483159
    0x909030a0306140303090f12010c181403100f02070f060e011d0c0d020d021002100e01060302010c020904061401151704030e100e061c0f020c070605130e09100b 70
    0x404030103d41c4042943c900c200c038115841907203520300300e42c10707651007030039100c00e03108034100078400000c280340c01a00783d00c42010708182440c8100301c00301c0e41c081d42d041d401801440040040c10148620145500104043d4a0ba01c21054003000000b0224041e10b201805442c4101c0d00011206400350b8041d007140d4500342e00d003074000894203265a10000010711851b440c1c6d000c5401d1403900040d44000b41c19908816070007134000c60800c0c15440f01a4001c1090003801e0803090080c80140c1089861500b02d480e9400f009000c900031002460160500d4004150b010b81f0491000039800b4201160350b040c1d450907448900070003c0d10002c0400554000303010201d03101d010b11403880d581001d903070140240445d00f0802c1c2c042d4004e1048401018455004080442c802614140e070b40c0d0001070040d80248182c40409410900b001c03e1840500100e2080b10742010650b405008130508110341143d050303200742c00e40d680c14140700380c000c11075481102c0100e004040b044000c008140c0c01c3c0f000d1501341c0e4484041907 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 691485656 1250 691484406 691484429
    0x703060605090f010611031306030518010b0114030406270c1d0c03042a030b1006050417010605130509010513080a030207080712030c0809071401030e0109020909030a0306 75
    0x341030840c510603415601c4504191480b2215200d4640c5107001d820441909212340c440c0001e041601035000c41d00480100104990034032091040794203071110200c0032400540b8202c40f00f144241940c00ac1e41e0000d101d00e90104000d480010400001e413035407524005000b5a072140c5004101d000d079400401000a1580c00041e001081601c01083c00c0c01042c10154030400000541041060000a07065088412001055a001030301109800c1400c0c08111041c492000c00729140c44600d16a800c01c0301c5e210307918145030605000e00000036030803240843e1441d6480786400b05007682c803031440c0c40d600500218002124a040fa94150030340380080d02407801d0810000507900801c140304200c580076070301c5040c0961744052074986400c0341d206078080034141d400070364000b44089a15400a405070301607030b07640210640f507192009440301814441e0442005000ba0345902a50181d009039003654521000054554150340200708a48000c0781c00203219040000c0154140b41c15100380f001400c00640340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 691486906 1250 691485656 691485661
    0x3190c122f0603070f02010b042d020c030d0b0a0b0d090303110924040e0c0703080106110705041802181b2704240305010507050309190212070602070306060509 70
    0xb10380a480040c02c00000c1201e190604600c550007500080d00c2000c02910400031900d0801d02070f1124030741b9810351085000b00d0412440030510500a50b09603503241000745140140052001d4010b050103c1030036003025003110002142603602002e490103000c103910200c0c4040712440c0080c1151154803018840500620038030030035886083d004808900010a6131107851202c2c0300050707041c0119807100210040c2c201c01c02c501442c800d00030380700f030314030a0702c4110700c0d80d072664001d036011032982030140d032950322104040010385841d410914000c8c2c000f800c0051605c0c120f4022a1401c00c800d4032981c086000701050011380101c2922114203400c0d4416914145010680d0a00d020001d01c2d030365400d994a00d0b210151036603249c0e4019880740c100c010342c03101d80b06035030303151036450744501d1000341c40d0f5510f8080012041e5008030100d80c440c0c0025000343c50000051101082075090f42242642c0100310380d207031399114000030400303072000c0e00e0240c00a10b44c0f5171071072819a0940310941c00036405000242c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 691488156 1250 691486906 691486909
    0x10602030a1101060f030c1806030206071209170d0801050f03030a050306060d02160c050603010b1603031b030e060c0c2806090f2003190c122f 63
    0x50790054481482c14004000001c14140d014000e1a045a16030f03802c840790010400403800e11800c121110306d20300d07211690f030710200071040310048d102c040e4100c0c00421180f000240b2224107a0208109410242d080d43c5d2039a100a52508407d0402025544812420340920307030082440e0f401458101e58609003800c841c0301080d108d0180801e01000d009011011038171583c1d8400a0b9003001c3e05821045440e0002c58141262288110005403608503a041012031107090100880e41030b0b8000c21303800d526101c00d40641101c19809400c0940c02c0564030302418105400c0e02e01c039080001c485581c080741ca0588811618246440501000022307442000308800c4080e0101e00b040e8070540780a01c6207904581c481c90441c540f415240010015454950588208600c4c404140002400340c168400420607070802030040025403030710940c1c180d00402109100c104031010301d1407101c2c0702c0c0c4c69140440d43d8500701603007425000302c4126102c051540000707190384000d842c64406110550013921441c14180c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 691489406 1250 691488156 691488163
    0x1611030c030f030d090c031e0c0801091703040206160b0a060603270507080715030501080a020904080a050c0604121106040b040b13121101060609140405180615040b09010602 76
    0xc01182941e11443e1807018401c6d1000d800c802150003044840201007480d980e40c0316000d42020031200414020300102c0c9203a01440380c4084c2e00e500c0b248036903507640382c145510b40701d0b00000e00807a4058020400c00301c640310a2586801c00034460401d81d41d1908041020100303844d0541c003c0410075180030900880303402c401175461900c001104403029a000d050400505042c9203800c0101039108124001400c0941000310100c10040e65070100305503602d4944080d110340010b00080d5105050802060120f5019801000322110340e09100c0c0c43c3c04410310010341000c208131020b95842e43d0b01d49000c00101d0300004040c5005c00700b60054680c5107080d940e00b080b41c0f10040e10103401213001100046031400002e0410000e1038000e0009540c40c000f00c10024650214000d4481d210b50902c0000580c1a00408452080c0c44041a0804030050340000740802040e000702150064121522041071031882400068020321004958041e650410014032007644c41240e86580110341000c010070070780e507010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 691490656 1250 691489406 691489417
    0x60606030b1c060605120601050f010503040515193b060a090204110d05071815140f0f070309051909051021021806090613021611030c030f03 62
    0x400040d00840c40b9003442c1d0024002070b000f242d04402c10a110b01100200095818101d0318101c0e140e5a40c1005580115000d00090b2001005544805800b00120145094140d8040c010300c106080d90410701c1c4080d42650704818400000c0f070350400808040d0840903c08ce904d0070184000b034000084030082c607944c0c0300402403170410070765510700040c41107665980000e80980007501100c2d489201200110004003810781d10a00840c488030100d1025541e00d120860403603100e2030742000200503425040e95103005030403403059040300400803440504442400b41c000d40500900003500e42c6007600d800b0700b420000e42c00817403051596401080c1000b204241850640b00038036408180fa488450700c0b401c1e808900d42090390040155508661141050501d020606000701d540b040c0c92654800c1d2081d81040903113805421000381d400007041410240c6084442d0216a540140b50061194908031101c5401748225503500c140d2a5041903880d08100c50408841e0441c041e100c90f2940d60681079903032055 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 691491906 1250 691490656 691490689
    0x120907030f0f0503041d010806090105040521130609060813120e01030e010504030203030915040f03050c031b010902042301030303110702030303010b12070807020304030b0a27060606030b 82
    0x142c5009004124062090714020305243c3c202c24140403203440406030f82d83c42400345040c10b00c100000900204414000c0034003842c1c0000280030f003100207280c0c03280038484030f40b030b00034404c4001c00040c40e01e0a0500c8070351004045a6541c1c201d2103003405002003003694058461000b101004010b2404140c840e10000343d20322003410500c0501035800b005030068418050850043c0d46032100300320034940c0110003548256204015545441000d070041c4208120664000d13003200803051080380041d024200405001075075508a909000d242c414400600041c41413018440e5162903882c01142040e0041c0500e284262040040f40d01005001842800c4144800380030076464490310400940500d088500058024003a25079079138564422a110b03a1044070426140c402200c00902190312428205020300d0785079010307601c0d051550319503444440015150205503903071100c2e5a064400c41e10b03d400b0902c105d0084404c5480d0043c200041203a8036540031900b03143c1084449103c0755500d603002405101d9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 691493156 1250 691491906 691491923
    0x60903040f060f0e031e0d0504080303270a031107053f01020d020301212a05090103150c0e03071719081c1808030711070b120907030f 59
    0x43d03410201c401800700d05000340c1502a060014940e07025400c4c1c1042044410402c46091045100c41290a449141304010280d0400d10100b04020745407807c50f0512040ca5001d0801142a89002c60070312104c460b040300401c0d891101d10000c9041400340d50010300e03048400c1028a80c0480c00714071841e04542c81d00058105500982c1c1e0b44800000a04030141c610070000c40d142c8154140c007000a43c070a000c3c0030000240d0401390f052400d07019184003400d0794000480d480c02c40e1040900c40e00c50b1103407500e070455204244030108070b507110b03130002d14004c5008808242001d0442e82c00b010441d00b05d80c0c986020040441c400003d15240015000101c078040d14002c0320086a5900341d40c1051039030300301c0c82c0c1c841c0c2c0060058018801e0308005442d040b0902c070380110381c103501456008121803800c0d20114199540218178004107020720080c65015241d418000400402201e42d41c1c20030034281c11a0031441c00120b02c5514003540c101040b03a01c03007200401842140d013103484000c1d128881c56401800b03540c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 691494406 1250 691493156 691493177
    0x20a080f0403090b0c0d0809120405100309050307061e06050f010c08040b131505092b02090108061e0c160314040b071a0402130c030b0909010b0102060903040f06 71
    0x180b003030000700010324503c0021381c3c440c00d125a14940300d41007500c0701000a2845804105a10300104030569144402e2881c14545803501051040407040a00e03070400b815540c6152801181e0244001d112492046500080011814001e00c3c1d040c0801000e035108286004400c0c80941c5901035699607402c0242054840b81d2850f01d4140140d225076009150350030f00109910345220034a116003001e89095603421404000345000c21134150085007080c580c064001c0550340b0384029030000c5e141030390b410300c6540464100ca80c0c020414041e0281d01c0a20158080300c10170400b140003a2041250031f94480d04580c560425002245840c0100b90548100c0d00c0b0303082c0d0304d80400d405001c1c800e03481c0c0c40c070200c2c45450715511845201c1e5500881c109807004036100c0c21504415010114092059a001b8800241c1140d50307520b85008280250405081c10361356041a8420740c0da10f54034070702c900d181d00d00209045500740002810100040d0403800c030359000703120500042c1d036090796501c240c4a20b40ba00043d0513 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 691495656 1250 691494406 691494413
    0x2d0601080901021606060e0112080a0f090e1e060f060912071212021b031f020d11180102070312030c020a0b0a020309010c050406120b03012408010f020a080f04 70
    0x9200710703181580d0020700703a13400c1810849103401c24401c03202103000e6203005a030384a62104980100c60801404203008002035031060740540c200200200e91481c01c030804a48404403104007000944455600200d202480c00140b044140c500b9400b5000307070f0304040d82035218800f0a002e8010360080034406d0603080c1228181b010208161001003841086503c000100350601100000840e00f6090041c01044200c0c07165602c41e01e0300000e5220f0280091807482c82d04041c5462409640342c0f9040100c0e020480b104d0840414002c41c00e800d0700b040c40e00e5551700d040700c0440e2181c50580030601d040d904004000c00224000c7c600d00c28900c6001c3c28081405a0f02c1c2c00c04034180b03101c0c030350004c1c0518450014850049034a5025510078010032000708881e25414900342c0d018021441038000142c1032142c0040127130800d8004d411502005030001c140b8121100700b10410f0a4000d01400f10b003910a50100320848003409440e0540e88002c03811413401d1b90603a8024194a401082c0051101c2d0500104041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 691496906 1250 691495656 691495661
    0x1e0f070807511706100c06060801060801020414030c011407141f0b310e061e07030c3f0506031e0d030c05212d0601080901 54
    0x3002101c40d41d5800010300c0070070401141d040340b40d2a8002051083c20f00600030350403004502401c8000c0882c1240c525011003210408035246049480030b0f120080099030307a009000e50070103800e1080c00540c9660030000d64008041c1c20001f1640b0036400726a00a144c0d0f41c01810551110800d12801a551041800c00d0000c9600620800c0d045220700701e40e50390014280540b4005c01c04080e1000c1c44031040b40070401c214010103441c1300c0c5548000180c0e100e82091000c01100910484680114441c42c603504860b00f0090201e07074400750902c1c4040e4202d40c00b000500d43d04d50141440c10100861140144000d100440c0c80d04c0c2c4010403001e2a03801ca20440800181ea24280c07114920146c00185515248024010031307241c450080c85500038284174151000201c2d0700b0004280010b1a684240120403000b4000c90340503c82844400c0002c540f140c05503c411204805001c038804025060600a8000c80141465250002c40501c0179000660304410582500b002003444c084c1407644890402500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 691498156 1250 691496906 691496999
    0x7030c081218010207050c0910090518071509090c0c020d11030708030403210e0a0602030403050706260a15030b01030606080f070312021e0f070807 65
    0x24030203020036400100040202440d01c10840002000155a905180c0700e09034010200018090b402c100c1c030b441041c0c200f01280a501c070300b0030101b0880b41e503611002c071011140f0580f0b4901c2d410020040c4a200c840c0e040080100a22074a04c2c015a2104030040060010920740142002c960311110410b01c02403284081003c4150010001d5198104078500311b4504071440b18100d009014054000460380b402100366070460b0b070042c03030b03841c1002e0304417401100c40f9803140c5020040c080c0104904416444013040c13000544101d400460382d4034113500b0300ba840e2209551110341000044003156483c81502210301080c0c40004a4070040c58035010210380c0035180304441210382e00c4030304800200780080a55400d0407640580000c00c407454445844540352004181e0b05d00d01507200f40e02c00c00000f01c1c01090b403440f2542d588182c612051814129020a40e5115501c00c0d469002151200303e24800b80800b400502044009280d42490180324000280310310041c1c2100c1038031000a01200c0c01208080107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 691499406 1250 691498156 691498163
    0x30f02061c05101e0501030209151c14010b090910050306240307060804150b06130602010b010e01140c01180507060f090b03060f01030f09210c110607030c 68
    0x1100d54124400c0000d040441d1024090109018001100044820601d07100c00588400004c800d04040066000c1d40c00000a039030042e5491503e141d66645400107401408944081034900d03000d1042c054080e204041c000c41c2008040c01d0040021030080302c00c8408609003502c400785150794058446466501c02e500c00d0f501402890204070300440d609890b6030001c2c1c0c80222800304024104181503a694a900501c40400c0c0c03503001080115621840c10303205e8007e11680415a10103800c003040d142d400c03040304608030034002c1506000b0300c1e4082c000c11082281c01e00e0062801e07000140000c004040008600040c003000107051400300401b0342040c2c00c04103d0b040b014031800080d20786141d56a25603c6140c0c00a101c14500482d01e80c41422054111141c454070705045468403c2004460400c0902c82c0b4141540d40c214002d05001c603001d400d94081c09080320042d01d02041300085410300b010494802000312450043d0002a6807071a003074005d0809980654989109140580310100344030313000b8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 691500656 1250 691499406 691499437
    0x60d05011d16081b04090c1a071104180311121c05010806010b070615122402090303040e060a0b0d02030108100903050901031a150910050c0601030f0206 67
    0x60340711070300194011401610032550012165110221502c6540324501400509520b260002c01d919058000704080c60169005415241c0e881011146000c8072a541c40c200304000b00c0d2000a0001104082d00e0500003990203100540003941c20740c0408e000001c0040500c200300d17011001c11a42001328020300c6210501c0207a40701480104209410000c0082a107168188000411945800308529049844112040d410a507550340e900e40903100c4050b01c4a10040b00506c00982d908803046802c10050041d0741900114000300340103802001c101c99108801030042001d00d00507280001144e04071000340308006910784401c40095102d5006502003102c011001c1120000a8600c0e070041d4100c0341c180c0c0443c1c10798500540d0f10800d441c686440640400c0060000c0b0030395500a03000840d00803101131186c40b424000400050201846a00c44141c245000c9605daa003414440d2031045000c44c2414250b003031203410031485640f804140802480078078500180700454a03081e064039260024106007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 691501906 1250 691500656 691500701
    0xf130612060b0907090501090314031204060b0102120f0f0c0705040509062208030c09010c02060406050903100905070b1803030301030f1101030c080c0a0e0a030f021801060503060d0501 81
    0x101078508504660f120b50907040100d0115030240701e10408032181a1a4030400602d10b4546003894100c1200e03002490000700088044d4144c0348905074400e600c51900010159142c000080c500000c103808040c11070810403d80c3c40b860740e0750080d50100c5080c4c919499617564035000c110b041005561169400c203081c5000d10801c2c079004103480388903400c10529440c2654180c5c074000c104941c07101001d81a05410400700300030109490090040c484181003103040c800081d400710b1144d92041d484070000850100392101d0b10b00d002c2c4015010140400d800b8411403d040e19256100c0215104081084030000781200010b0b250101034141028014103494880da5281000c008804101904880016014944080640c040e00c14241a001260fa5040c980e699000c0005482e40c0300c491080c0500c00c90002500302503603202e0341e0b203020f10302c21b403180715001080b803041c131003e040c140d00301010700c3d07804100600000d0b03841400e4030b92145048a1140300390e103103401e1042c01800340d0804041d41c078902c10035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 691503156 1250 691501906 691501913
    0xc1b10061403152503090203070b0d18080a03050402010c0f0507050406080f07031e0f0606061b0812061503070207150f09180221010602070e04020f130612 68
    0x7442807a142055003542e20900c468020309428500490318100861031442c003103060755110140300c2d41d02c54603600300010017241c6500002d04e0449241e201c0c46100a000450712403c030341c50700070718802040e140c03004d8035142d4440da10140c542c0141d890034010190364000103801e5a21680c501c604154000300c07070b850902e481d03041040d1111218001c0500a0b401c041d000200114002121107105581f040a400b85600316603920405920200d2801c029100182804000c21454031030302c0012482090002900c525050000d03040410789a000d81d0304004084018000c500d0040c00c84890000015040c0010380d01d0b4000280e201084034013a40d00d00c4404001c01c141c10b40c00050034416640354032a00d10080d00784010440e1a101c1c5440070100080703101108000c9840e0100742c101842559002c00350401d01d01030200082d801d0011104025a4022401040019010b000c3c00b00170b8900200a91407074a070a40104148401c00311031580a00d142403681d60481c113503940310305c1c0030f400300b41d580416115036801d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 691504406 1250 691503156 691503179
    0xe0604050a02040e0c1809070e0d05010e0111070b09030c060106121e090302160f030204020913020a093b04030c080a090321080c0307030b19090f050c1b1006 69
    0x1b5100c0c01210400a54161619000350028403500d001e50380c0c200f018948000f400102040c3d0042190b1642d2a240d5104c41d60000303008010035003101d50f04e005d44624284c101107001640203010313010690010469130354203140c045007a0341075030641c3c185121910021901c04005010414101681485400b018801801243c000e01d05d4280640e08541c14140313854140c10200740076114214850304d5440c002c100500301a0090304203c000100064896a61218071074188d0b17114007090380004011350401c1c0494081444c0b0041c6006c01e014143c0034440d40c10003d889801c01d07140071410308101040c0080e003010311484460140c290f010030582d480c3d41d40340c07401425490460008680000000e001d08540300d03242402d50309449426a143c1076291100002040658000340402c020985c80700b01c1c0c050640ca8644808600400c0402c5035440f4515181c0500119607442100d01c0708075041000b4402d4201280c403e81e1810100f050f00a540b2a890030b80491800c07000c0a1080c250600b00b43c070000d448078481 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 691505656 1250 691504406 691504417
    0x3020d0809190804031109150f030c12010e06160e09061309030f020d0c020603060616061b0305060303210613060905040c0e0c030c030c09030102190e03070e0604050a02040e0c 77
    0x100c45040c01c6d4200c480810818a004075a56403d20281c104002c0c0c1520304523299020118010342070301c01500411002c00d401e2503205a0100c010783d104c840008448c0801c20405510400b442c0301ca20b620310500344002d00800046001911442410740032403143c3e610050300d00071940c1c280a003041915010300d030107429404401004400b60040d10b504280e82c80c003540d803c200186d801803480e451640c803401003003803e07000480700440c0080c094183d000011568440d00301250144018100b03003a000702001016a0401060320303000c0d410600501d500c5142c040e20112001001040c0340c0925039a80010580502160400400441c00c004001a06001c1c0b588a00e001c0c600508044200640b00c004c0c200485209864110790503100308000b0304002d030018095504100300c030031030381d160001000c0001d0036604015071590040284000410b08982c200d25604070400042d00a454401c1c540342041d6802400102481e008603241c0c00042c0e03544007180e0442d0301400040407020107034200740c51074400d160083e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 691506906 1250 691505656 691505663
    0x52b06090c08061e07110a0b090f0a030e030c120a02010305090111120114041112060406030c0e06040518030702041517030d0e340b030c121303020d080919080403 71
    0x1e50301081707200744a0071002104118900042c0104406555400c40c400c50040168105009030200250f0040b1306101d1804181d00950300c02460101480030107081030a94a0850310450002610701d084510100d03001100e1602420700003038aa48600501e4058403550001d80c00801d000100c03083c0c0910001d10090681c2c00602d001410014068284001c1f40e1071708040c03115201003030101c4c040b03001d5101403156020074040d00c00b15913a9a00d03076407005441280c0e0081000c000140d410004da505040c0701d5541d0205900e80c2202c01c001d820f4606e56280d104864020340180c0d114094031a00958816a16008000710311005a071b100b10600d0150312074100e01003000390300e030814800d138034504000101e010074114882d8040d010000760900d1342c402100b11711495421035403003075030004850100c00b019611410407580c103d6176681440d41c0180d000d80004150007540305801e80000b010a1340003561000e14150b5040c500d1160715000355891800000403906000312450703c50072003c004040b000343c41100d10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 691508156 1250 691506906 691506961
    0x90a060b060f2a06040b0604050603010b09010b0901031506020601180605030d0c0515070207060e0d0f0b06060d061d061210050c130807052b06090c0806 67
    0x10100482481118042801160203005542c02c504191000c0102142803c2502c200c520403140070310b0800c541280d050392403038071480812a0320f0501d4041d2580c040b074118020000ca44e041d0001881e09281070007080245d400120700140301e42d000c3c0c8e02c020904415003041100c80360790343d20025580d400034015507403a40c0e26090102c80e07006450158000380c5c0d50090142180310344000007260400c0c250b80301500c46100b2288500b00d1244400c2416002c1d640340c0d4090f1500504008000c0c085114149034180640d40c5007420901240e11013100104e00c1c1e5109104204d562113480c0002d400e4080c001c5030000451500340c2c00100b141c0381c0a50141010000b030b049602c19558401000850b144d0f9800300c039410b41201c890140000002c1d4407940d4441d8100d01c900b42000c6c85516880d00745012600605a694891740c801e020074504400005804260300704010b83c0c00040c20303a0146141241040100710503155808002000380302210b010207406800101d410610b0702c1c008518450fa01034122a40c0d011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 691509406 1250 691508156 691508171
    0x111009080702040b0d08070303050a29030f1506040209030a02060309070905011202031f0e0d180b031618181e06050303070b0a09050d09061b020a061b020405090a06 72
    0xd00861030a0f0451b0803a140710705080940d24107601030600104901030072560f40c50f1040f090144042148040031142404020742c049910a051800d44610302c0c003201684520611515a60107001c400c1d40148161000350b228001c2e0400300c1d240081d087d100030751088000c0f08100382e48030006509001c407212400184441d0340ea80b01c00d01030301350314044080d4050f0040900c0e40a960054080d4490708000108005136007183d01400d2414155803100b8040000c0c08410b2200c650404440c061015210741c6403000d02e942003145107001042d031010a00b0041c0004403552844500b1401095001010401c0d00006520510b041c400c00516500c03c4420002155403501700710760380a88030382c500740c49016008500d171008549988004101c0108001c4a9607100c10380d02d40001d2081c0a255000d80064a40343e07445401c0907405051042800c0705503201c0b80d040c915050160b582c55500300100c03801410201039100840c0d601164040d904000070390014104030500c410020002160214180620010400e61 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 691510656 1250 691509406 691509409
    0x30a120f050a05121504020a0c0b3103020304082b020610090914030a080906010806060f0d051006030c050103231f030605191407020a03111009080702040b 68
    0x5010b003030410700028006001080c02031514440c1d81e50018500c5c04010010442207000030144d80c041c3c5920000034001d40f51482c00c000a04682e42c1d08aa46881d14600d0006440a100399810280c05082c03140c2440b40c51090a00d0300034070455024000a0065a10020404c00d01404440c584081c008864103030140c03052000348089045405400903060b0040c013030389400980c10183c00380c060103454108040c03c1143c0345c2881000100605482030312084068501500451700341107050707110b0031258003c2002c0010903510100050031030340044682c08108609800e005260072955180da0360400d262840100621103502c80c0032044807001d90f02032141c85440d6865685d100c0c644500c0c050f909000f200480c910b0320364201c0c51005402c140801000856503900c6031030a5580550b04015046c1041107902032989942c0281d40207000919480145407c2c8044000d40e07650b20480f014040000700e404060200a051114080c03415420500b403050400038140480590300011089101c0d51a181e00702c03c86 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 691511906 1250 691510656 691510667
    0x3090604140312010603020a0504170a0b0609041205070f060905060402100201020a080c0a02240103051002040308340b0a0b041e050a0204030c120501050903030610140702030a120f 79
    0x80d640580f500b90f602d0b444c0c440141d010350030800c6068240b000c14000420090007540d60030001352542001028110180d040511080ea4090700407806405068100008160124039030f804120561030510307951000e03030400190051021400a10709401c1c40c41c41300521100049a0b40a603000700d40e901d00300201064260300700c0c030a450154011a40d01e900007203203038070f503030010704443c039007a0065540740d00503400c551111001002603140381188140040c014031404020402034403480040462405045444155940c0124507031507044406141c40104c0b42100203000440541d000c0028a80a8000c1d20f0301d621800386c100e41e49900b184c5402400c02c514030b054000c2d1004d005100350400300c202c0708a2500c20140c00c1c018800c2100c65020400000000d15180951f4000c11103246881c2c40d80e401d5141c41425a0390180069a0320750080c014003010740d444150880c0000c540d801e0000f801c0a400d00030400c2e0780511900690302d4020b8021800c1404031128242c4000410b030358a00e50380c1c1d445414103841 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 691513156 1250 691511906 691511917
    0x13020910061704080d1b0212040e1801150b07030e0306070906050c010b03030a030207021023070204062411060708010e180708100609050f0c071403030906041403 71
    0x1e003480302c850b49184818070400e40c015029201039032078107150364101016203009201c00b17551501c2080c90701000541c1071102c40220064030742510718051514018100c0f0103006844d0300816074036890440d007940401d40c00309111000c0d40301022442c0340c0c2c40c1e0840c613203600641020380205044024460140c0b40100703c1501c1003c007078803071048a5050030011101074120028400340c0e50340c1e4100d02d0f60070366000c101400c8071110700d660150350b800c00c40c4144940c501554a03a002070000a9070403011804403551041c51a42d0a10840c1d03440c0c245600016014200980c0201000150f040c240c00208072100025940c8007020340b80c0040c0c00a040c804659031b2002200c076000001c05500040c41070003940000d85800282040303083c0300c401c80e10700005040c40d00c40c1d803204200754400300d000c080415090203010010400b1031010495407510070300200c1c0c080e4000301001480e0600188580c1003210160000391903504080032030362a494840c20300c80d0f5510040e01c040c1d030050781040c0c1100c1906000800c484 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 691514406 1250 691513156 691513169
    0x306090b060a03090203070e1f0602010506090c0d020412110a05010503070e060a0e060a0305010303030e070f030f0f08161e150914010c052a0a0809061213020910 71
    0x2882c0c25000d920440007000c0c1d0031401c81e0715010b1540c4c000750316a40b50039040d0003901600c1c00542003c50382840030714460807039448401564100000c000007691100b80966210749500c41c4640c0c2c41e1408501035000b4807482d0800d16810360b5158040082c004c07840c0701e19400c1001a5846182907454000542d81c0d800212404000229a840002400d0900001034007808825040040802c50303200700151242d0000b8410400195480004106060b031600414004200d404050005d284c105803900141400d039002c0600010742c103005200402201036802401690031030754494a4810b013213001aa0204030520a50b10080c40c118802c84030340c0142c0c400713800c4a40c800016071200205004440250450f43c0f0152782c04660402c4d0100269828002e145043ea00c66854555a0b1110314141a203044102c1c0120014480f0b641070420041d000690710301c500d900014001e407906401800284288601d107a0b07103220200980c107201c0004c12003030340060500d108a5003148903a8405212940802581c415003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 691515656 1250 691514406 691514419
    0x20705011a1c0c122a060203092e02070f090c17060112020310170304030507031e173a0b0607050114100b030f0a020a0e12010c0306090b 60
    0x108032020044420b1640399202c0c84144030090358800070281c8000d210031045d110146207240000012608800913070300501100f20000c20203080c1100250f6a029a0503e0340c02686444185215091550b08204500c500034680940801030000d00a442710051310480842c00c801010104080d01030340113400103d0b44950341e0780c0052040c01001540c0c6000940980d0521848101000d11041c6500003144280e00b81140d0703580e003501d0481c2411900c0c2501c603010905802c188410705c0050004036204c0105d982107007000b6100369190300e0842071038401101c0100303411001101070007202e80400140217480c00c1691201040400b4410900b68207120514045070040719004a03268802c0d82d61003460324040140c111400c110b42640c51078210b5101c0c0e240000c8625115081000d11804a1a94000742015030034450031820302d10f81000c180c0e81d01420043c000c41c0c003c20241200780c4a45203019104600600100c0e03111020b095a5000f41030004066001030b0405c8000b040e103004034086c0744040040034100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 691516906 1250 691515656 691515679
    0x7031e0902060c06010308090f030307021305040c0e070206070e0301091101052a0705030d1107090c11030a090509010b0a02340305010605030d110a151509020705011a 73
    0x4450091000d0082241e110300305110701e01040404102c4640039605c14003140e43c0e01e0049a0070040ca220455000921a500c204044001a1030700544a440f40c0052213001c90540c4039482c0240304c511194000c0c0d409001ca403402c02900c20350004d00d01e8001c9100da00e40c4c00301d00502c901031500762074060802074030203106403201000b5944200005c00c4041c008643d580c52400440c55088005140e03c01c0701e03030055000b100c05200030303d800d000ea02048061820040c0040303101c0c0d404691a01c081d03201d80c62525a030f0f2601071101c0c2d401031141060000f507410a5a6454805c414090302c0c80e0040d00541d8006c41c1ea000010581c124044125600400070350020644110081100750031320b01c5850f00c0001c00f16a0204c00211120345608100103103200f6800810741c1c3d4104000c0c585843c44140c18001009421103040c0c000040103d4010000d54010b10008043e52a80c0c4694000d44030404000c5c91170500242c00083e01c0803d58058008103108100900403416110411040c0d0081350780c040d83d1003030b18500d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 691518156 1250 691516906 691516961
    0xb0103050618090708010f200405091305280b150a140f040c0801090510150e0f0a12031403150d060f0603030c030813030e1e03011109090703 62
    0x50642c0d00940e50000c613140b20f038540c4403240c2526000c80741d05a4540e01d9524000c7c4110044190984a10a9100c100d0400740b4000003e04c4404000d48112650314080401ea010b0000920903580000d840c540300f250740d10900005401c40170286042035504400e83c0c0e01086420300115113800c00b41800800c910b07040b5041841c0b0502d1109000b200c0341d40005418003010741a152170280b4180c1080946031511150300d8510049d054840c001d281000b28080001d05100281911006124006691a2405208030ba541c00301d010380840c040342540c018204000001c520071000c4c0700060141c401d94801120090020b503040d050300054600c00000180b00d00070940500300b05401c662501d0084002195900745005a10100c1c1d415401c2a0001100c4454007001e142d048140f5a800c0b42c00709200095803202d81c1c030020312404c001080c503441401140e06412003141644030005aa4100500070003240441418842050340b103540d0840c06000c02c08005000ea500910901c412170790f01d0626450a00d240b580c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 691519406 1250 691518156 691518199
    0x12151c170c070f06050310060302040315230a06050102010e0109080316020712081e0c06041106040b0c010606031b0903150603050312010801061a16080f030c07060b01030506 76
    0x20540e0210b440390700e2001420b00d8010b51058024002034480d039660741009141000d21342402d8004000345801088108005141c1d42e11b5452149130783d04001a0b1103401d071071840010f8cc10f0340c3c04a07124003606006d21039030102c558410400c56409800810042c5c4101c1d69803400e031605060060180030302400000c042c1d00c50030717401a082010b07500c1980e043d141c490300a60740b914900c0c1d0090b50802004038400e01070034001c07031100f50190f0003025240d003171580001c2150790f6008002d0000300504034103110304145444184c10f460207841005215501c51031407451141c02000c442c03040d0000241000c0e8044c1c2e0b0401d03000d04601c3ca0101c60b0b55000040303811904c42d0b1440300e0386401480121a510310001020071801c5c000307088034a44246c0404899450304a07900e0a4403241d03009668a81c503407060b0341807807007541421104a0924000c000800c40c0440c14a1003540c05901490740001c140001001101181000244410352241d40704010020300a00110225081120400d4209254a46000150f9242c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 691520656 1250 691519406 691519417
    0x103061d0f0c2b060e0705130911010c0f060e1c030506011e02032508040f23060901050c07031205040305070905161412151c17 56
    0x150140309084498401903032505000a0060896070000c00440b920303494008003450b11000040d00039240143d0104400c44890b090807002080f00e6520f03210800c201d182401158000e113001420840403405910b5807002a1a4402c07007280d01007066a485000343d8065101d22940b150040002e14030041199140c0009011040c6095070510505502c8100f0600340c54000b41010b0341d5942c0400c050804a00140452001104503100b410f50004268800c3d0f03400401d0312014806403600d07158a2a040000340d101603015400a88040700c0068080742000881c0c00307003803c0700c0310300152098403000c9401c801d0724801c0115945a0002080202c480150322540180c0700b0000f5010983d41550707507035a0381207901c00410300e0000101e5000714081091000c28441c1100400585000f80103d2910381c1c000503828001401d400705104d029074481010034212000d8443c005908404416030741084801c01c0040100307444102c0c030034200310104030300c017026040100954a03440b911031030381c010b49081d4140040d04803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 691521906 1250 691520656 691520681
    0x80c0a0807030f0303090b191a061909050d03022508030723061501020f060402030703080a050c0709020712020f07030222060e060102010c090819230c090618010306 72
    0x2c610204000c070f0001b039001802013064801c070b100c00ca4034085589054540c0e000d55410750500e0300c0100402501c070041100c0be025084001c0c0a91080c6420b406e44540010f40c002542003031849240c00100b5400007075054140c9400706085906814a980140c82c4242e64080c491403074000344505800a20210041341d28030fa0b40c4d103040306900103082d00c00303881c098041781c0031120302c5100360000800c0c1d60103214124100220b8000f44c490b510b440c6d00441c2d501d201d640300003442d040d000600001d4991240e425034500310401401e941c017140c0d40b003010130003940000030b060755a0741090b524101060300000d10504180303040b50250210a203140c00b00070082d142641410850100d42030317501282c0000c0d1042501034144440c1065650404500080c01c440780b0065032814020507003010300416074000755856810002003070201c3c3d0810b4500c1c0600b081d603a4280340c5003940784246040302c0d64882c00702760454126016188a00c8030340c4c3d44c00800c0340780c0c2001e868000c24140004018000304d80217800a0b041a0034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 691523156 1250 691521906 691521911
    0x50a05030c0412050c101d0607030201090c0303020d0e0907020615010e03010c080114101e1205090c03120a050726071b08070501080a0207020a081204080c0a0807030f0303 75
    0x26520200c0f80303107540d0941c046070507401c8900319140d1403402c00240d0381100160701d000321610f010300f050160a0040300c00d0140c0302d040d0105104040510035005086429408550036400517036034500a981c8108110301d4a010460800d0355189a040283d4024401d5190303034000c12180d1038021a00340400c0c048524a8100440c070f00380031a60b52000d01030700186165a507155905985003a18423407240c0700c0048181d06c20f40d45a90f03986071042d840114501c10045040d05c2c2c110500740074a05071032110b6003404c20303101517081c0703000c00107465400f145152030700d00180c059454140502071640c416202c5c5100040100341c080c001e900119501400d11800b2118075072004c500310101c029020703600d400464044425040500303a1802c2012035500110091800600401502d0f0401c4006031070100c000781104901580800c401c010355480503511001003d01c8000d40300e80d02e000110074072041c0c1c000d002e003410300e200766007800c141401d105c0c10581c00c80e240640540304980c00d42c1e96140540011410a804254 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 691524406 1250 691523156 691523159
    0x1062304081509030708040501120902031c0f020601030b1b07051905100203040203030412021809100c1716050409050934030b1003052a0603010303050a05030c04 71
    0x45000041001c0c004090003801c1401d14400000c0301da800040c00070761580c10a025800005da100e0041d60103941c001d003031042068402044041c011b08410388065130500c02c0304444010110050140c4445039030660320401088400c40013a40d8549085c400144860814400580c514181101c00074000741000c071082c0c40d0440a4031643c6c42c042608080300d0400c0300c043d00c15010020304000b00201c1d004044015829450290000b86e241e0199210b640118a1b01448150840d501c0c88180465550704109141040c10034404603a510400d20195526162030503007001803031070090024119000005031800e416643d0a9003d0300030440400c00141800400e010204c4c164856005141c4943c110303500406041d40088100d9007501c07581e17405020022843c0c2d180080d01c55a014100082c2d94100c204031407140c031404204109045d59602c05080be018042068020400c114031026891400140c0000300c4541041080311510080c40001d01055017040020291070051001e1548592030311003103401c06 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 691525656 1250 691524406 691524467
    0xb0a050918090601080a080405010c08090d0605041e17090a050306040326060913020a12060b040c03020f0a27060309051c05180301020904021603020706170106 70
    0xa06405a0041861201c4800c12100d044104441401000c0d400010201d0f5030498444102d140f01e01d01415040000d030300c1c44c04d03040c09a9042210078229019020710400840c60403c5c3e4002c060030b4408484803046030f07035102e203012141c42103540c0c0c164110f0100e00140200040305403460b4045001d007600b106501d140001c940c0e80030711906200714080c5c4c860302d880b60300361301d0b0f102c0111141300080600300c2100c400380301d0310303884040744260711100c040100c041300d22403400045c0c03560605611042a01c808003900c0c004014140d08001d41c0030809440501840802d40c03402e800764020030884e40c0310034005101840e940e030308c2413000c210308213011044a910510364508180360030109820200110b5241e00039401081400c000000303a42d0f02c0500d260181b4008032600915038032405201d101041c43c81c1000d48869603080d4125444040010300c1107503517440d070b6102e501c07012151003416005809501e00000b1000e00903482086526113070714040a00ba82400404c0c0d82c40c01c0e0b05110328004407561007101c0e440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 691526906 1250 691525656 691525669
    0x1e0a090203070203041d16050309010e010c0e130c0e190302040c0806030c090f130c08031303020a09090305030c0a0e0415081612030f180905040b0703020c06010b0a0509 74
    0x70b031500e0b4041d5a83d03904040c442c000340d912070721280050b4031604040040100e1074048241d5240c0040c0b03050b56494440602e02409400050715144071946064003008038150041d05038a807048065a10043c03503805103114400b110801460507000c58000d2444400a2410b00d843c542c0b0107401503072121645032aa00403c04a5141c0558840811000c4c01400000d240400680c8c00804040b1119409880c100e8050341041071b024004509491816090304100810030308014058020481126211003841241c0103280103688016400342803100b00110360120507000300884944c054481d2851034840f00c000c840c09501400f24107041288090180d0b0f0565501e0040701d03003000081c4600303107100741480d0300c0606210480347d0400d4101c05003003041040c244014000b4010640505204160324403242081d00c075040341c034004806002150030040780220340344e40610300950048890980b01cae42c541d030b020340481c85442081c04140d8000001004004c50000c02000b900c10686000383c00c2211040c0030400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 691528156 1250 691526906 691526911
    0x2809081504350703030501210c030303021803060f07080f22030e041e0506040e1b031e06040b0609012106020d06080c040c0e010512130f11030607020c1e0a090203 71
    0x1b51200010840c00102c0f07100c140044106074043c128a100c80e90f60385545950611000b0145600031610600e903140d11780050346013940203010386400d86800e06058100c41401c41d4000003160701c000204101c2006001d04612644499101411000e00d21440711000410800118100b000c0528010840c0d10f440c00380c1400f2a903942039850600c83ea108940f02030720001041c1d140528503010b54002413a10019414031035002d480b0504000014002c0400e051400422680c040d03c040180d12480c00b24000501500c03c9004007101da0040d110700302001202c6500303100700d64010702008600549403465108410042b407184600514000051100f0380594105d940000c815800c101c0c0400a04c0c142070041c4405112103180c240402d8190800103071490140c5c088010801000f84002a107240500c1c407002038894002100d450741221901d0100c0c1200028540240a40240300c041440c007800000c00316181c08004002c6d4900604a0422410120311881160750000c5a8180000e002c2072a100a60 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 691529406 1250 691528156 691528163
    0xb090403180914070e030f03070602090402070206030702100510050d1209080f01020705010b18160935151506040308070606030201270b28090815043507 67
    0x58980701c1001782202c03114000450098010345842c65010034040b0480300c5440c1d000c003005849d41111004100240107441c00250060400030510209540028031041041c180c842c003804140c0e03c9035400c0c0b005c0380b194403425820420041e5040d00144030351582c41070030341c3c291402d48200c1c0d0785d8180d001c2c50910304d80b00603003203039600054000c180070080c01001d0080d682615034940d0001d181d5000d8149200c000c01403110030004004000c04944221903000080030b807401c801d10b1b0181c0585c0c0d4405030700600900784010400901c07000c48000030204414007112441c038103550341303941c90b4100e90091a00c2d0480140d070010b820000480061070901c0500581030140400241140c218070014080349001807440c68054400c0440003500c81c4844a07440c2a41c6500868039102c0600c8a00040c4100910100311821440c120000090079030011880c0200c0e0441c8084130980d401e51201c3d551085416100a071400c1071a024000c5001c0d12070207a1800c032401801e5403641421003032482001074001c0f41045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 691530656 1250 691529406 691529441
    0xb25021c0c0b160f030e030d0e071a130509071202160503070c06080708010320011b050d2025050603070f12020406171801020403030905130b0904031809 67
    0x403e482d80c0c41098074190300b03158201005800c0d002444c90b03541e8068181081000d5483e0511074000110600c91500101116018000341200000f5003c480d41c100305420624400c1b41600090146062800e10b4060701c1c940c1c841c101c001e5001000c02d0007a500240c09401c0b865504c01c4210300140d820801000301034055410700f18140e0600c200105010005000380040180b05070041c00850b8004900c030700900248010100c0000c440f0300140c40e09054400200c1c0b01c0c280108060013070000c0070910001c0d24585030f540c0d880e0240028002e0081c0748800c3e04544c0c0da6440002400808000105080441c141c2101003001240e81d40d00050580e034070842d40c83d40051401440c210f202500b2805055000550940c2035081c03604001009024501c02540207503103032001000b08800700101e285038400340c00402c009542c2e5503200e0038041c08281040c41820300500030040c0c925041001d034411642c80b000c008000d2065615107403412220300c0040c1e03601444090035050300141e64009845840d8022081d014003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 691531906 1250 691530656 691530691
    0xf040504080f0f0c07080a05030a0809010605060f090a050a12020d02030c09130506060303070f08031b0d0e062208031806070801060e010207290d0501030b25021c0c0b 73
    0x6045c10600340380d10608060f4010110b50000034004000d9405101075441e00903443c3d81c5845820340503205079070240b500a0740c00201182d07546202030043c550744034251480c1c0c0056690b00c090255220341d521504d0301420194080800518080040c1007080d400242110750f9241c3d2140090009802940c0c4803403440c0c1c200552408000d4103020843c0e0001c0b04801550400c0d50b01d8990008070301e000358004291402c0080003c055038140180705684003c950303000f80c4c650601e164840c0042c070603401400c040d4800c090006103400d420400044a10300310b480d501c505140c0c01e030389492881d04047c207401c0140c80c0c6103208441301c09007080000e10900e00791395040211b5150042c05003141215900341811500080414885e68060307001e00021780c00300ba9422600300b80940500b050310b000b0070392102c0307108c4d007464000000d01200a1007180512000c25100741516100c10240452503468803062015800c044060756103092800340032656035481e41803030b01c0c0c20500d69840707040ba204200da81042d2500d2072a003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 691533156 1250 691531906 691531927
    0x21c03060806280c050304080313051c090f15140d050a150b07020906010e030a02130507090618090207140303071d0307050319061b030501090f0b0f040504080f0f 71
    0x243d1045801c00c0001040f40c00f02c80742e8010a90b1200034009800c0b1040080828030b008100344000010f0745d040025a030801c2c0420655114001e803070a01d520000760f0340c04020805160000c0b00f2400ca60300300c1500c40300d01081e0b0b41c00340e03107141640038031202011041c03001003e60207039800b64510918454a00040c68007107a03580e0359a0200c01d4101c502090018814440142c98103825190446000d00744559151421130021341340ca140030100a412030003030002080302901d681c2100c0d01030b60071905e9018909455940455039500000340d508031100e8140390400a0300c0d040e83c024828180201400c00551003038041a924550055400100140d0307100c00000f41108406140d26000c0e80031006019100d1410b400a691203203000c103071841c21810b0800440c01c20070301341c2c040f001c031455020410803047d803880c0026005080c00d2040008050a20710b080d804402603206002c900080100045d04c002102814000103210003441203c8403601000501c0342c0301d55010141071801c203001c1c0c1440d81c0780030b0b040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 691534406 1250 691533156 691533211
    0x12060903031523060d110301030209070e010507060e071d0f0f09070620010510080706080c16020109090e1623220c0903061b021c03060806 61
    0x1540c0903800d12100100744803103002082d480d4052083c19810200159110f40014024803070400845d0b000b503d841c1c401450b190342000a1070490f4000c035409041c913941d000040e11104800341089000034030812580b0002103c961094072200b81e85001c60384540d403600c20100b40582d100c42c10101610216041054091152050319846540440b41c00e16500344141c800b036450300d041c055242032214810440c1c044400c0803d81403031920a1600134001400d00f0f500500b480111030003a201035000388240400d01600801000f401000004145890150354005541c000013000d0030072410041045070002d10a4000c4c0640307003551304120085d018903042014450311094076603004082c0c1c4101b1809415181c4e003003112001d41142d050303c80c0a41c45041c1b101d09014100d40d0540c01e11554640303400c00c00046c1e4002d272a2015a842000100480000f000202c0c181094903a03e02005920501420048203c2d00c4900380c4101102d041c0410030980303810349503041c0741c4115030580402111200d00d801c80340340b00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 691535656 1250 691534406 691534421
    0x11040f0810090213230a09150203090c010f02031e0d060501092907080c1005090a0f02011202130902071e030807051c09050616030b09130c1206090303 66
    0xe0703000c00403000c0c1503020522290120b403106505607900c00110100710804101c400201038001e03002849841c00c0c03194103000b00440d01c410386403680042502d01c0c0d480c01c0d80c42124014090000140b4103003016100440d1100d05210166046000501c40b0044210100030080d401800381101161281c184200c01c008459040c6d008504210070b40c2030401130366a1172031000480d81d0f042c940110001d25481c866490b140314440c4001c10000d800116980c40c0507005c161010505041b8a062295880e08021940d69043c06000a4503442003c0760243c01503000d40d85178030556445200c00b5040c001c511700c0328140982d0f10b0340a103540795000203080040185880c00c803c2d100c10311401250726000c0c1524020b081c81c030002e2500d407c1c44000a10f01000a680341d14000b202d040221060142820a01d0400d40311502916101c0844181d43c80c4042250b00038094084481000b1f00541000c1e5a0402200d000d0212401d080c1da00c21501100071540b404502030123109a800351101160031700e8507283c0207040300d448 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 691536906 1250 691535656 691535683
    0x30a0b090d020d140c19030206040b13020609040507110708011e0504031d03120a031a040501060e0d1a040308010e0a1104030f030e100306050f040506090c0c0111040f08 74
    0x9050810015600491804c00181c080d0210301d855558082c0031138a009001440041d03a0414080d03203e0806a0000d0190b01c610f00c00c081c2e0220b16150703107442540a4032100d030020b47c03120040c4134014035400c1a602050340940c062030084007a0144410260038280389401410740d59454030f1100402140d90303000c45841030080a4100312034039050701c0080a041500f0440406261000e124604543e400c0004480803c100001d03eaa504031019014000b004042e0340d1600300510b22525511525061181e00c0c12503d07140c5a012031000048100030440d50b40700e50440e00100014000198901c490702601e12980c800e489050f907950420500b695000c4008100854260030040e07401d03446000030056800b144ea000c0c0300c00d07404910619040d00c0350611440d0b501e402280d1401d1160351194541c102100312403054400c481199002c00502090321011541e0340e420080000c04070320311099650090101d81c25504c0006810f016801d0340080580c4654440103044002c80414000e000051043d040b0800c0b2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 691538156 1250 691536906 691536913
    0x60804052e141033090503010b040e101107051b01020615010c030c02130f151d01030201180902030103030e0a1205061611010204080d11191b0302030a0b090d02 70
    0xb0f044483c4210364400780541002e102c1da054400c01100c0d0b401d950115194085400a098000d1031180240301c4045c611943e8407a6007004142c0c500b81c14188a0703d10505508400b6021500e5000700382005015a00901c8010020030400640802e0301071003421800241034560006800034034000900e0030501602451442c08031541041481c1c3e0400000c901c0c6a070b15080c40c415441c11400002d0b2501400544c0040850405000b04821a07895200c51401301d5007450800707929440d403441d49000c40c81040d00d03d1822044100510141d805801d07078020884048002d00e100d030361110390a8069030401ea1048000c00c3c0464600140362600c0b82e10311000d40348109154084d211103440d000d40e5000080e242c40d107985103c00340400310503c10b03004d5640841811009543d00c41d90303000c030203a0303508101c0c4803000010020760ad03044070b00401040d15120300070704045003a0b02c0d19494541031a140c2ca1048650b81d420240c450000040e2801e21100791003034000c00d01184e030703440d022403014140300009d000380f411500b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 691539406 1250 691538156 691538161
    0xc06110c160b16030c0213060503100e0709150f120201080a020c030a0c0c091401170705130b01020309211005070c06050901060512100f0204060504060804052e14 71
    0x1060b810341e044048105105150140c503801c0549800c005290040e41000084000004c032240c690412012a01c0680032205c2e041c0d00b0080d188100c9858040c851040e401c90101084101c02e0381d0040207100c104000a400f1503070f0b4038032035503a0107400c40e1b01052012010028200a40d0303000050b00780c0c0003500707840035071411440030381341034032486000012820301081c03111540911882192600180800c42e1003001a41d040201c0c18043c4002481510140103d21008018a02000c54420b0881750003074404041031080c1c80410380607018000600341140f2081c00480705a66500c1340b00400da24500100c071460800411219040a01d460400304e8410305003028028066805000100c0d0250807e07400545900d07003140c840d001d058194050303a4032800800350b14010880c0454000078101c0c4d00d20081100d008848010010782c092441010b01040041c0003c2112038020200380e54070501c25070544810303100086040510340284940681c0b404031980308011a00414840c0d048601c038902c041d6030b000e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 691540656 1250 691539406 691539419
    0x6042402070c180b03010c02010207021e030607050c0a0c060e0102010b09011809061d0c0a061b0602070305091002071d0408090f0a0b030906072a030509010c06110c16 73
    0x4000b0391207080e60000030a401652031070003030390207141c00071801002848204d01c0381100074040d4000725003d034800c00c0d240c0c5c0b45115041d609100c10076a8a009000780640380e0b0345c042c0c00e03100d64001c940000594000c03036003640c0c0081d0143d0882c5d80940200e4079860340c0c1c03a9240c00024211090086500e000d10001d04c0184600c0e41c00c40d81e50314221204650104140e22140341001c050190918480207a0007400c603081c101040105440300500320584108200301da0b54001100c8031421084c20f2645440000d003160042140f607001064118081e0802e20715051012001c00e0840725685d44000040c0c03c0700740c050203000e41800f0710702c00c2d05030b00c41100440c504080d11003101c5c5100e4500380c1e138407d25504a100c0041e40b00d80aa4070001c00d03100281d2512454926000c03500c41d80201d4003840020350203081c1c0b82e8409042040e040c07000b1076940f04858842ca0310707038083da41ca0b48a1604ca42c1400030325802c0000007012400754102040d0038003286600c07221000ca015242064065500c03d94803415031060041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 691541906 1250 691540656 691540673
    0xb0a0206010e060f0316030204050f070c0f1a04050708062404021308070306060312080c0a0e0f12010603060f052503140f100605270f030604240207 65
    0x5460903a55502e21507150b1400090f4500400c1500302d816004022030196041110502c00c0100c80c0291400e102d19a280245126461011a10307072002c900d0101c4004040342d5105600440f29111b2441c04030640410980701900d900c04903008c031116401100305010b90032090004a030071401d1119401d01a01c2c02d44d102d18604030381030319447e000e02c0c5c0c0402d20716a49051240c01900a0481d1010b55024039100c0c100907001d00f04030300045d1040749200f4200c14080f48120040f42c800d20859480e241000c964240c1241c10000e24030340d1a45c8140c10f801c19900c5a41c9000c000e0050000c414000180b5620310304c6c15406449211030742c241914941020011000b00000c8070049012081218481d008551581500181600d40b04815524810800c11690984038400315000780c0e030814120707001c3e907a01e01c0120341e0f51041e841c0f00d8411030714901514000f600c08503800385900800070445004d0305000c00c04a441d20740111030035200c02d51040a150304003400c40061102e2801001c0b002c0d4035044650311030004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 691543156 1250 691541906 691541909
    0x40f050108120f13080a031103030106091211060409140612030a0c0303060e190b220b2b120f080106110a14100b1c060903020f030705010c090b0a020601 67
    0xd5010000034501c622030f0052048508510030f1000140c3d00f60b8590209594034031850400310041070070888400141c400001c19281211407540d24a0307003840c1070001903e00c0c0d800c000001c444a1000f0300000c030360307980c1d0b5501410203060003600028401c0e1b0305031502014000003820301400b610000c9800d01c002c40c4080100c811549180c1451982d182d040c5c60110024200c40d489854814102c0041c00703055031407180c5071840c21240d401d062201540030b9082000740001001d0a000354124504174a208120a402c01c030b525040042600601c00e9050402d19080f102a00584880340100003500703041040800040c81003070001d1a02d26800328010202400b03010041c0100c00500196240d2011402c10412034020000d50004c400d100b42111408070507a00d01581c0311001185083c1041d01d031090500c506008000110b912210800c2030711a110480100705c14603050301180907510745500b40f2001003006003600c52207003000194031111880010080c5020ba009201030002c20081d03007001d142d00051660 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 691544406 1250 691543156 691543183
    0x60306040b060d0f0320010b0901091e0908031609060806090a0e0a14070b0f0d020a0c02120303060f100221130e0a0b03280f0b0901020702040f050108 66
    0x18820380b07800c0c2c0000c403c10303142080100a4014605000105030b4800c18500b0f10811076200302d80011682c40300c06007611100c1d04083c0d048030f10701004025840d0150010b81140f00c400c103129014480c030407142c00c10f0301c10010307080e5200c1078004244810b442c4c2d034922007481c5418134a42041c0c483d0906500502202010b0074043c8104110000310300e0703e43c4144e0008802d00454003c503454887c6501d0481d0701c0710200c0101203401c1c0240040000c006012504445480d40d5061240345400410107002000f0b401c1804a4810001c898180d840161528400e001e0300b00c40e07070002036450345043c0081029210703078810194040c14245a81c059042c1c0c001403180485043c1904040c004540f07102004000d002d40c82c00201c14040d864000603282a100741c0e80c60042e84080710902c10b0305000d509043c0e860089146200e681803d0903891011060b0000b001500030744a845400c0c040400740d280c2c080d2003038059480751007603503000076201c0c1180703058450114503807228a020b2050758075110003962107103c8a890103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 691545656 1250 691544406 691544423
    0x16030b0403030515040c111020070c050a03080c06071409061c0f020a080c040b030712060f0b0903190b011403010f0507080910141303020a0209040308061806030604 72
    0x54003145071002020414940a002084490140031000f041f070420710f40d6100c02409100c9005031002110f000b0500901c4c5002c0301c54003038504154401400b03600081081d2003218489101040035500c0914100017140100c0e06182c1fa0780c2d1064042d8100240036020b107081c060012640f9031102c1c514030070754103001c074100c43d000c3e2161040400940d11810300500d0700003261070002001e2030400305a01512680c0740c141e5801c00c4560b00c1c420920003d00c01c43c091658040810300004407020311456030700d01041401600422070035920038800c03d0451260300005102d00c80494920000d04040004e6581d1281d5400180c03208071841e01d0f269000c02042c06a000005000000c8800646003504a0000103900e140104554500f07960010700504050300d00090070f0007400034070700340c1c0d0303035180511903600882981903002d58940c110041e440d4100030104806501503d12a400580c2c1c0302c501d6603111318080e440c2d4141030300c0c00d5410440c095080c05180208015900280710351511b001907010361055008800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 691546762 1106 691545656 691545661
    0x109060e0408030f101505042d061107050d06050106021e0c01180b03070f140f16110a08010b04150e19020d02040b03010816030b04030305 61
    0x281440341e0610106505480c40540d494021581c0c0180d05241131b030715041c840d0703004460315081d4003041020030200800d445121619402c03c00070030800e1b0020201d010725180a6503035009a03003c10014840d03441c0c1d1841e0070848200a00802024061301101900c1c200001d06024000c100c01030188284011102c9141305551f045048000e001d1711750100c608004450401000c05d5211040c040703041d00061340b242c9c550041d80544d0b081d0340e404601c200000009045213012004802021504100410b00200d5100c01d0310401040308004840c1400a414030356482d460440302a0f0744000d140ca0001040881540513082640d0240d50071700c0b0030702c2000f8640310303126154841c1810140344107000802d5080d56100c004d00780444540c005080811400d100d10803a0040e401c107921104d00040140001c5c042003100c44503054a0b5071021034a02d0859803907d00b02c01e0064001000d154840c0302 = true := by decide +kernel

theorem cover : BRFrame.Cov 691366906 691546762 := by
  have h0 := BRFrame.cov_init 691366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 691366906 ≤ n) (h2 : n < 691546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
