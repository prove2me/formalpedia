-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3567
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:01:54.268894+00:00
-- url     : https://prove2.me/submissions/22b09702-04fc-4f2f-bfe9-d15d8b4bc05a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 641366906 ≤ n < 641546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 641368156 1250 641366906 641366911
    0x3140c0a06091202101b1a0108060708041e060c02011a060319050901060b0403030801031203060b0a0e010e0316140d05031b0106180f0b09060325080a0506 68
    0x411040140c0206060740b090003400129001c604101e00d11480c99028006003001c4031002d90704002e590940b520501910300c070b40a00c0144145000084030140d201e001036401c0041c0c000080302e8005800b840202540840381c1600300344c04c00105091400c105940860b92001808020310040c100248548000c0d0113611102d2500c00711001009603012490411203d44030031500d241c51511288003181c0c201c03043c0d502455101d00e00704000a00707540c85545402998100c1d501c00c5000901c0d00f00107008002201c0c1111260040904050205500745040e501d294082ca00000040000c0c00381000f04a85c4141a07041d501d0780080c0a69002c011921300c03407000c01c1968000d1800403852440c44856904011101146894000340550b0030040c1d4401d01601c0288403290481803503407504800300d020f0302d01075243c54130860000b100003404101c040448042d02c0d441c10780c5601c9003014000b04a4241c8000c20040e080540010701541d9944c100d4088050092040d0041c03009071080901c1c00c400c21200054160 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 641369406 1250 641368156 641368159
    0x12101403060103170a090512060712051b0703050d050420010e0a03110303040308031509060d0b0703020310080f0601060806121207020d08030f160905030a0b04050703140c 75
    0x6984025100341a034419081c4402840d8244c4401003100000215015110400705840e00042203a51480090484100c02d4010b00281d0007050520070210b401502e90701680c1c5501d9014003440c6880e0000ca80380c0b880c012202c0450b0140040c803141018032400c100caa050031b03024420009800c107800c00000f0022500540c400d1403509401070106580640854400c0c60301c018680036040b03007955181f181413517401044640511040c030006c00001c180401661140c949540c103030900c0558202004000c541c05801640100b0443c1083c8001c1b801442400c0d80c07041541c10050b0b5030303032600d0505403402d100b00c2c0e201c000b05000b40f806e1140c20b0358010032541d04943d41039950111076100c20040215025007120502c55591140007020b2043c10303490080d100791030006000c10b00541680d160305040350300c2201e004644408e030404211181d00d00e007032001c09042c0185030442c045c0d410a00841e68446000300050310300001c00c000201008405c10604001d1948450114032829011141a50301c13047c5c42d840c90b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 641370656 1250 641369406 641369429
    0xe060c0a0506072c010203042c012c0c0c0118110603010b031b0906071115030709051c0204060e1b1309050703140711070803041a0f1210 60
    0x19074014800e4004503550106114505019141341d401e4140c8118500c01440c150301060000003910405040b0922020701c20401c2000c80b4200030b0900100128140c201d5290320311044110b681710343c080c406400011981d4402c0e03010366280d40500c2c40f02c500624084c44400c0d801d000c003040ca851051403003400d0091080c214410310030426010000140824000e891001c5001d01c0020038500b40c074110444d1014250b0201c0e0314205442c8041031482d444800c0540703140032603500e58422401c20aa558400d103000b00402c1e8254104020004c11040c40d900c102481460710f0705c009545c003440700d15a6112141c0c020300801050760748500c1801d2251080710341111110b00040b0010807800040111441d200c0720120490001d0304003e0580c000701400b034120410103683e1030601c80c0300704400800ca0b0194500c3c1d102c1001a100100c00b5a14280c4a9080b900c00c982040c0010000040e249000e96120941d4051083e00d0359115840c141c07460007542888481d1454943c10301c0f06034500500848155510341110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 641371906 1250 641370656 641370661
    0x1c061a0705010b0405011a0a0311070c1d06012f03041401110c01080112030507050105041103011a15072d020f0607030f03050a0603052d0d020309040c0e060c0a0506 72
    0x130401143d0092154003030070540c213a903401c80c2c5107449005002c03440407402c00040ca00f504014038070150700201011520700c49800390034003202041000c14200000200ea0043c590700d802c80008120b0946815440703164002003072841c111142c0101d10340c2c3c4800c1c0c0c100c1103e03211555424410016001810220302141303040d03540034009000426040300002068603044040d0340390110412070b07020b88207000d80402a082c030029001403004c4c002c260003640200030441842611500301030071603c2410340f60041e035840440b080f0140c0c03030b071056005600207541c180c1c076118846030400902e014a00745555441c01d03540d140710940d5402e103111000c50540280c4100b0303401043c030424880b080c03003443e402901085000c0301d1403540c070340b0a8008541c081c0700d450011480135941d540399441c210541e4400400d1014401c00700c01100d0b0114098a011024800140041480f203e00a5120b00c500306403a805141c5501c07a050000380200d190307407041c190240242d80c1d210f030f280d8862a100c8895150072100c9004101c00b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 641373156 1250 641371906 641371909
    0x30f0906010f2102060a02061014150901030e070602061e040503030a0e03091203030117060609130203070509010e0403021c090603021b190c09050c1c061a0705010b 72
    0x20000d06032118104000001420240114120043c080f00034545075240000d00c801a101c0e4000750007400441d4008010b1400e001e1500f5070b500a0540010035221031070300722084603944150500d10503180d0030109070307a40c4884000480140c420303c4e27580007180c0f10b5130100042440c2d000800e00c0c840c0300d48100d50202c00300a007400111803a0103540240c040c2d403040c4003041115110380d0000130305504110440e441c210428002c43c01100340850b250034541c0010004228094030300d000d1452000308034014024030b261490010f0010034014041159420110a2401c1151400c011306409030100500c24461580d441143c21502c83d4200e800320014081d00c0009000300e41d40031801c1c0d1072143c60343c5038580304c03c0c10700b6022130003504110004039650080e40501910000140040c2c802808421031030400c4041a00b440750000d80b01c2d5000f403c2c198a0402082403003c4003109403031102c400345840158042090b070500303002e400550002051100c40548001584c44140001e00c000781c4518000d2081202000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 641374406 1250 641373156 641373163
    0x3030f0606070b2701060807180c05071b0e18010b010309020f0f0102030d050a020a110c0303120c09180a14090c010311040902040603060303090e13141f02030f09 71
    0x104480f1559020410500084800c11200d68042012281c2903210078505800d4030303401d81c40103459401103001400907078000901050700601004092000581002004015105900000e4603109030034080011046001c1d40c040c0060110590728180c1d070816854001e80d41040c50190308540d0718107600550103500a007d580220380c0c0050410001e070ba022030a12180f00000c640d07150440c0000c001d2005481041d2080c0d9000c1c880b24140143c0700c0f4070103007020303040351072100c1203211139889441c081b49640d40c00007c8401441d0001403902e0241c0b01c040300c080360b6000c2c480d40d140e030001070103600344910389004030154840e04101000380f104a0098004000300a000d40344900d0a404c0103046001c203502a8020142c4c4803600444dc07484c05580d4142d40d01203812940244001079240c038010402d05078421044006412458413003078075030505200200d400400c090f40100a501c82403c1150703401c005104840b004041c19011007000240345410340000e500454108014406010101c1c89100000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 641375656 1250 641374406 641374417
    0x10801051c030e031213050312040305060c07170a02100f0c0206011e2403050c121311100305100609030215030406090f15050106030b0117100e0903030f0606 69
    0x4081038003407070307602e440440e45000710350006034051144071440029140510001e10550400c004941c44c094107120070503081c88280124407500040a00c41400481d0001c64030a800c5521a904103a0305c01c0149841080c080182e440c44615002c0443c126840503004503010820162940b000c10806025200220445010501240c016030000b0010b00c00742d42019051121034804010083d8819698031382d0400301c60131550304000040303010f01086102d94140c000e868000060312619410704030202c80004e44050001d00125032400488008003d02040c0845043d00304c0c0090603001030f804800030b001d00641402c3d211580c068002e142d00064485c454100502642c1c0d00030014207622102d030034428580c1e00041c00c26540c0316900d20301400000d400001d19074000d8450140060720b841583c644008a40301640100249030420107041309582c3e1145081141c109d011414607159100c4400b400351404040c0c000180001c400300520200000000240d032003034510601404e01607461800b8048940a132 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 641376906 1250 641375656 641375689
    0xb060307230402090f0301050405100b030307020d02010e220e070b0703140304080409020d0902040e0609030f0a022d0d0f1b08071a01090c180b0a11030403050c01080105 74
    0x1c07000002220702d083d0b0003c01150400901c0001c010160400080c04c594043d64211261b030301c40c03c060440e0728124054a034100904501940c14280c05801107500e407030103498002c0c10402100d20b00740143d0740329182d044144016041710116840300c90300300740c02803c425032850b1081c81000303000105000100102d41c41907a0641d42c0703030400781224058840b40c1d0009407080302c170b10341c0a02010400001903c00303401c680d04080400710b0240101d005010840c0c1d500301d80e4a8081e04180d04200301c2d0308002084580f04d46c0404030aa544d002001d404a061075286c1519030740800805200541c002003224590655004a10980e4030101c0c4240701520b4410f004140707000410b80b652a848055601a2201c09006004444152901e02130756a906201c0482141851409081800502030079400e40306405200710b0328241a03000c40c2c0c88012032900f241c06403054101c0c03200c00080206996200f40c51070400014048122500c80e0307201d1030710544a81c4641001800540d50f4400015503103481039246500040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 641378156 1250 641376906 641376959
    0x51f020f09010509030f10060311041b12020c0f0703060608150403140906070c0f05061c0c030b060d06080622030c02220509060606070506150a030c030b060307 70
    0x40100550390f6411600368180d050044c0039203e8440d81062180343c080500d1101c4c00501c0c5421841c00346039900e400d080941c0254900782c0c0f800407251041c04180075a00c2c1b1424012700256440c0940340184c07081030800300c5c0303502600301ca032020260f0006e204402d903031084506020b40b41e2294030b4960388a01d1590203900c241c040d4800304021030302503060701040ca03000c003100d6458a20745801040700e079480f0764821243c0d440f1031030040000701e408440980241100311400307882c2100d101c0c8101e031095541030200801070f50b20102a940703d4060f600c56004400080d000359201c8021a070008020095882652820f0040c4000100d00c50210105000b0103140c2018620b841c01c01e41e1422500190102d10491304400c010000740c42c0042c0341c1e0000c1045074211007000c215440d00e041e40c0c40c10010082c03d071601880060100000050700852004d0b80034078241011000c40711960009001d1a80720b9101078075110561030b0100a014041644034071038041982250030540e070b61608012480e80e845c440111070003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 641379406 1250 641378156 641378167
    0x9060b0403050c19141f1805030106060906030b040608010c02330a0c0905030709020c37060609090b0906130302060115050417030a02121903022203051f020f 69
    0x31420340100d41058006400041e001289000c8501521106c0d8018408141ca8084200c0071403081d50941020b004d0543c001d00100e8503006001c0d0004180d80110000c2c10b4031903103110340b5500c0d158070a40043c040500240200c07116024040d4a03550f060344d01d0000000410540780340324598140e186141c0d4000100741241da540c00030804001c0c1904400e0070704000600f04009110f50707081002c20090818014010703521212a0701c043c3c030308151f22040d8003054080701c2005c419000c00d1103001c04150001c80300005e04900c00c1c42c101b0b00515080d0402c000702813501a10800b0322400141d140d2085850204031030740c5840e0b00120340c2440042c60340060060348000014456480c03844840d030503140706810007504054480c281c6c00340c505010f50318000c265102081070482c45030304200010f04140f140801ba8940140d0218001e00c981104070010140360b000070341615840c5085420340280440304940911840d22490444d882d991302c44480d82c0040c51410420b650390203940b08543e1554550940c3c40d107000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 641380656 1250 641379406 641379419
    0x715140c06072a02061603030f11131e0603020c100f020405040b1c031b05030f030702120a05090405060114070f0203010509030a0e210a06020903060a0b0d0b0a0609060b0403050c19 79
    0x1c0b41842089042545400d10518111801c0c014403050043d82c3e01400d880360bc0c840c414202d6009a503100e00108842c400001064201c08050300044e101c80c0e16025945400c44001d8900e0001c40d0301400c1c80c1030b860481c01640c8440b4a40c06041a2402140d05101080c030000811820708a4544260b0440501d02174503000240182c00c00d80c0444c045c0000071140906945460b815600400d0195030840303000010007004940c18001d03410180e9200180506001442800818034043d03d040c0c1402282d030380c00030504980c000e8048182110b0001550380c0e50320307103614210b000e044d004e038070490080d03080c900404c8c05850b010043d202025415a50048161300311010058080d88420790b11076038100400c186138180e401030000d82d54450288501680d81c4040b041410728040d0f0090441c480d4524003004950740d81d98103420800d1040c1c000c0980b140b1521000800b00003440d19903c0111260310b012800100304003040040c0085a01030340a4a0410240c00c007401800e0f41c0c0f0b50030224004004d00002e1000c6c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 641381906 1250 641380656 641380687
    0xb15090102031c1116021201050f190605090c0d0608010b0f0409080405100804030f020601270b040e150a0213030b071704030c11030715140c06072a0206 67
    0x5040b0f0f060b0b40821986590070340c6250680c040d6400742e0010004c0c50042e400d5050420040c03540e620090002c00007441c042642400d90403001e406c4110540554505005011181d0095009000004c080200f50f061402c840843d50380100c1a0813415130402c080007031802810303c1070101c045009000c04801080c1c200401c80103100e20441124103c006000c0841e407610340c1c1c490260303030400d42d40b20901142014117000d0404186548450b04550046c0014840304003104242a120800f0490420151030040031751400307441c0810001d90841e251000a29902c0c0000490400140c1140469542a1642c85e100e0b810b074401c000c191400301c0360184040001030741c182041c940c403090618080030700c0b102d408040c5202d0340007541e041e40000d1b10f5030710071428056101178000e002c0c80200d000700802841e24001d40e200c0e10201d5080c0e402d0129441d0350021040000088403031007403c8609940c0d00d07180000c0d020f4003004904988114100104102001141c20004a2440180c005001505144881c40c54505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 641383156 1250 641381906 641381947
    0xf090301061d1e012702130302120118020918100203010618050319020a03140102030604060b0a171807090e0f150c09010c140d0f050405090c160c08010b1509010203 72
    0x142c855840c0703429011404544050900c01f00004006000c071232843c0100015444801e443c43c1c81c0f645480e004d8003180745080441102181e05a4120f4195520410b103000c104192180e40c080500505d4030180c2c481050364000c2d4182c03002926002c3c0700c481e5108010f007002482c5e00906415030b005451304200714641c0b07078048449510003000d140419407659078101203454008440c1d01c8980d000306c14800340f441e2030f0003036102034041180c1107030812a1050005100110944c00b080549007810040f40081d03d89106103449654084111036410b640c9064100040c030201940941a0060f0041d400000002144410100382501400e00c025100d1100d141607a92010070742605100c0700703458130030000f40c090b101504084d41100c040d0444074102c00d401361400c4030f003050a00412004000c1440140d0301d031600250414240380e900d03a16100d020095100c004c241e11805070203001400d80002d080d03e015080f4020701c400c03d881c810000c4180800141060203121141c03070142c0c005022414586e000d0003002c80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 641384406 1250 641383156 641383199
    0x715020a15270c06030227040f02120405190302030d0b0a1205031801090810050c0702030f070810060f0924090b040e060403020703080f090301061d1e01 67
    0x881c1c9079120001c1035001c6041c0000401840b441003a10300f880306203d010f900410039420300390700e0524030710050140c1d460119550b0b1042c102e00e50b002e8826484e10b50009485140e42d10086598008050105440003411281211a80304402c8550403904005610000c40d0b03915800840c00c0416208810014001d2020700e10340120180000049403c0d030b42c038550540a000310051035955000103040f0401c5401c26185070305000c0840c1042148000004000807501c8410b0b10004403a128039080e241f8500c200c2c600a58544100391032800070782e401085501c111400041150020800c040c0c49005842c00c506c90400203c0452200304110001a045070380c2e1124511420240c5c600300b405450a032072926084141490350701d91032aa02801c2038441c015606030108010007642c50f107580c0c02940e0b410b85000080281d41c0210b2403803400f261100540b03008500040082c0101516048401e50b80d91610145046405c0c0c050040f841c010141400340700840c40e05003140101d40e090906c0182d40035186400030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 641385656 1250 641384406 641384411
    0x3051207030e0d06020307030e01050405030f2a070e07030c02030a030509030904060902090f013905010507050327070302010f02032203020f1f03090204020f1b0715020a15 75
    0x2c51090b03945611080349180305030780040c0c40b81004030008080700c2e007002c07801c9160707032400c001c1c000400e200105607808403201d104159a01c29500301840c28018404041e181e0302581004556401c602c003280701c1741903440d000d10070141a9120a8128241d0710502d0648015804c100980c44d070042c0b1a40059610041800c03c81e4070b8003135440c0200d000c07102ca80d882004144c2c0d02103440c2c440761505888029245d0400d05c1c00103040200070f0b20000500c4846004038006c8111091340092642e00051800e4a5a401c600204403d240c09400038016910444100849169540c0c80460503c03158a03408208a0700307000401721507007141e0041d200000c8140001c0d055110900011040c200d4650210001d22102800d11000c1c40c034501c1445104448646024820010300f84000084980d15044680b65403441c030b8045484441400410000d120340100380f08003280001d242e40103501c01c1451091507060f81d030b08031950255545030700c100b1445007617280340041e040000d941000c81c4200310448a041a0003800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 641386906 1250 641385656 641385677
    0x3120909040809100e0301150e1f0f090504050d0507050615011206140f010f120203100302042301140a0b0c010f05010303020d110606061b010b04110702040b04060305120703 76
    0x44d000c403500800349800600e16040d42c03485070800303000c1d5400d8128a90280e2110b1414504500040c0301d00402c0301c240012041c03060b0034905c4a0482030001008150310003004640c1b81c14400011340000c95064800f1301c01d204d01540054440c5040700d1000340c010019140c1910b51030b110981c40d03800502002c2c10410012030392450b51090b4451a4000d01e00c5080c0b21880c000e241007070241032218000c81a041c00035041482e884590421440e03003034035000c984016a00ea503800020114130051741c101941040c90b01103002c22081e001d541c01b0b80071807406042c030070070b17680d981903462141e0b1103c03004c982d0001c0480604000469440c0c0c0500498048c003000881d00102604901301254001da000350010fa00c206413585e24a40c0001540b08861460300207041d6600c1d105011482900c00d640300c1e2079003480c940d2213640740788400394090144804010700c14418900350041d800303442e0704601c0003a8401c07860080d04207074a18261180c8000c47e54004041c1ca8100d800c00101141500040d50607070901400d00c90 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 641388156 1250 641386906 641386909
    0xd0b030c15071113020d050105150a0f11150a0b030a03140702121b0909030a0c02010507321509060106081803041206060e0403140c031b01091103120909040809 70
    0x14024007110480c41c2c0146c841c0d50405514040c1c41040e4000c2d070261043c81d6444418042d51421641d01d100f0a041400304908042d80846543c810102448001c0c003074546100c08020300e80e28800d00404802c0b034107228000e000ca04250300c1300f040b11b000038045507541c1c2c5103580c619420ba0103091214002081c820716025040c24450130001c0800c0200000c00841c154602a40f80c02684981c0102c5914011401c1018202d80604085002c5070007078140280403414a0030003003a001080380d054030b034090102500c0064007000e4804036415030310080501506084201021900d01d40500c1100520010103413646042d00a640098020f400f495601400c89409171b5049001c0004100412101030b800b6005100c81c1094001c1fa01e02ea0090031950003c0c005020220ba8080d442000f000541c480320f581e107580d6107603002d02c1d500c1655016041200400081444402d041d07019004c0580100b03640052240801c00b05501c61384950404505407030140a500494108100e09550062141d41507074a0a9a000e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 641389406 1250 641388156 641388169
    0xb1017010e0702120d0f27020609041d0c030c010309111003060b0f090f0604030218150a030b1801021201090207020105070602030a02130803041805040519080d0b030c150711 76
    0x105c8005494548070710602c42c440900c6003840e0849194003074010b0480d100d00020001c03100d2800070780304800105010f0801c2d61603034060502c8200e103c101700c4c542000a41000d07194400456058468080d0b80c4034240d8950286c01540006d503485140240c10920311030030081d6410358464490101940c0f2180414800b04030002080c89000c00c01c0c1081d210b000034401c00c0150bc446000140c00b8000c24841003006855845c0b03204150f012583d40b100c3e86136030320312040b8946a40c01b403003260302102d481000001d00c0302e482c0f41c9a019129030713104045007a494440c0d0b2402d038425400140c0020340003070010400180307103078007070405684140760241c0360100c192940b0081c0e0b003066440801407a0700182c1c00305c8604400801c03100034452013015500b00752078141c103100300d0801c2c050300003034032621000000c003005018000801c035010071b020414114005820700742a50b4100d010380b0f04180d498050100010700c4d00007984840314000502e4041c08072800103100040d40c000c07500403112111188041d10260b81d560 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 641390656 1250 641389406 641389417
    0xb190c090504090c090e03040f1e14220905060a05060f01110109080301091e0e100f1416090608060d12050c060106032003010b090d05150a0b1017010e070212 69
    0x9200442c2c0348d80c21300e07008180000c803a0313015001929891004071140da00303c5154200b1540c80c222040343c1c01e4512408115040010081160a072580b001004881a290391041d20528059411980700340d0320044602d0444100780e9820341e103d402021100030f95803255200b44101c27801b03500080f0701240c0903079540701c45800070382008051a132143e03d01e0010520501c03000072401a0207005111060041702280d0b150684102240021a20b80529a040003110b82201805605900f2004800d00d0b024000543c020300c1406110001040000c0000345c40384125141802150028100a21803074960303122101a01181e1008040c0942401940b04508080c0072441c02000715443c0496142000030f40501c2904038a412001228010b200600501e403280b4203031840004180c1d100301c189541c90604072310301625503020350540c40901c0200640030095800c0b40404141c20f49a44c8625442114140c4441c810040301000203106040104907568641202070f801a00074015034107414841000e844c69a03000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 641391906 1250 641390656 641390681
    0x3231f0c080c04090908192003031017120c010b040b090702060f0a0e15071202120408091903031205060d02220e07030b0907060c0f060b1504030b190c090504090c09 72
    0x1640380032103520230800c0c242d19114004401644c9140340a0142c040000294010208014442e1102481e6a201001a0348803000ca4403203058540566521140c040d00c2300390002c03405141005940e88550818504450050101e90050191565207440702c0140c104014000c41d010f0741c49440c124860340b0306001405046017035074112442442c040e000501203d070f2100e9480505e038070401507900c1011560000d01d0300b241e03200e0201c550f64000c00c0d0001c0c0d00f103554200c0c21025114064000400c1541101c04444044482913080c0050341d2110100a0000314520b4003030340091000a800d04c81800001032200304180a201c00035098841c1241c0505c1c08002c0d410031541d018030341c41840f6020904200b000010903184c41c05070b1a201c244da90300d100308405884010491a25000301c00031981d01d1460f45006081a07444443e01c50b40d076400c000c03905810640d042a040f220b00f000301e5500381c0890007812a01c25154035031450703907450481408024401c103801941c0c00ca0754a41c0200d072015044c064000100c80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 641393156 1250 641391906 641391917
    0xb03040b04110d03020c1504080a030c050708030309030d0606031806020d09050f0c0f03210a021231030b150312030a020a170105030703231f0c080c0409090819 70
    0x14140140400400540c91314241f100c0c1c244010003010b00001240901c0ca0360520340040d51449a2404504d018843e8019102c0d5000200412071004000006004801d034290814400c8030703652030301030b01194181c01e1003010780400b100078000807030b81517001000003440390800051a0074a84c1c9a440c2004845520307100300e600602c0065103a86403400d0754000210044001d820114103001c80920f0a803843c0054106113100072800e60000c9000740309080008104000d800d6079060141d034440001035a0405040c1d05500d02e60400d1820141201588240d9500c00b0b0105e0b91911840c0a2640d03481c43d0700f0322960305201d086039540c002035180000d18081c1c40f80c1580540c40c1c003c512030103445803c0080550604161040040000e907500280d804100d82d040781e51840761101c7c0000354203c64120b102c1c02c02c15403095600e8409031445030340d542c000380b01c00040200585a100c5908650080702074821680718042840309002c1002582d004100d40c501c0b840c4002d00e41425500c3c85030381c0c540c1c2d104d030304d201080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 641394406 1250 641393156 641393173
    0x31a0907050d150506090103151505131d0730090501050609090a11040b2d0a030302030403060507090e10032009160908030c0606040c03060b03040b04110d0302 70
    0x242c500400c0c0c881115145000c40950401000c9400c9008008130340d8100354031a00005403641043c190310003d8140c5902d4107010050300940a40643c1c48108071422480c100ca000066486c01c031444400640020550ba40107515a40c004541c442911162000c02c2d5a000ba00e00700c2001c01e48100d000104502100462624103600b055030846034001c0c4801e0003110101c080000e104008210070f684154042c81d6500c240440c4408113000b0064070315002e0b0461042e08051a82c644d0340b03003548400b2183c00022200000600f401d02c014600d0a00c802005607005001c103100148154106d02e0f03003d1081d03e000031129980c0d0300368140819040c0ea0340c03901283c40003000c0c400c3c41125055060314900050308400e1340e5007544081040d84400034a0580c466144242c4900c0d1b051203443c2580042502c003003100d80f20a245100b280c2c80781002d49030944110b00d0480740211440c042d02a1000710382071038603000c1c21075442c1d8035400290100200211030700415203400c44499903a41c402c800d01c540c0030f44d0043c030782350303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 641395656 1250 641394406 641394427
    0x2013e0106090606030510030b041a0c030a0506040605030a080315030a0f1106090a090905010b0910170a0302120d02041a040302030d09150c02030c130905070f15031a090705 76
    0x440441c0c204c0d5003014100420849401c0503d14020200e0b80e000504102d80d9565040c0400705481112a4507000b45090041c00b43d00400c00340a9400744c00c0c410401c1106449002c200403c0759894821140c05420091441d030210380210080c40c0e00c208402c042d215049100d100007420105020412901c2c025415001c030280a02401d00e080058000d441d403610340f60185001070800103c912400a64540702c40340101040000c0d0000d2a401401400c000d0705030800001e13801d1030903001d004040e21030218491a000d400300004040651541540140c00d10718240c0b43c5c4a01a42e210000c40540070307808010010356026415418045648144000c079159400c61040500300060034020034200030070401d05100c1065000350300442d2407028202751055541c1031002c28201581509900d80c4402d400614402d00c13130382a04080c0c1c1c02c40c4207005a80a080d11100c8200e6011018000e01d51141300b440b816060030703802a07000b0b102c0410142002c240c0c071001c0c4000510107034011110744001580104d00c20520 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 641396906 1250 641395656 641395661
    0x303020c0d0206040b10140f040f0914160e061c0506010303020d0306080a020a05100c06140709060f020c09040f0209040c09050105012a0201030e12040317030402013e010609 76
    0x1200e604580481030347c6c90301c1da5a0501b6020300b12810b01c00c20b4203d54407083c82e501c1e640601030700300d50280c0506c100f0215003010708501c0381a000d019480e000381c603910400400546c210782c095030040c0c1869011901e0703a005010325026020320041242c41c25203d03c002003802046194000c5103c0d0b801044071040085006064400303030b0740050342ca503000f2910f00c00160f4500b419042a030f02c09a41d948413400c00250100c0c0c003003414a40241490785411525105400480286440f458480e12a001802d96403241115901c00ca00304000050300100d031180c0c020316007001000c0c1c00901940c84801224115000120412402d6030111210381080d80b00304031844a502500e0f00400e1b09080c00f81d050043c00d20301440300a03ca0a111401661b840504002c6a000358030030000c0000d0b1000326803208104c1c20600e0500d07400360201f501d5066142c0b90000844800c0700440c0d105a03410307174800fa4451071030341020917880c201c6e40d020b0580c0196098014080c00c0d01d85804890304280c8000841c105140490301001c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 641398156 1250 641396906 641396911
    0x1b01021908070f0c050c0d11090912070b0403030f0e1b030d021002031003050d050d050a050c1b120c07050a080a110907170f06091e130303020c0d0206040b 68
    0x103000c028820080c02c2500041414a10402402c04074240c1c000b52505606100c1d083d0501c0c0c1d8000c5281c40004103100f000b0b56603c000c05020364440c0c10300d85274038800300e994040101d420070072420100300d000c0004c0c02c690409034000d4441c2c01d01040242401c0141c40c01d65a440c00c2603824ae602103400c45510002820030500c1590064020b01040c01380c9201c001e40f20100380348240d00541d0008003240000030744851036001550404180c803010092110003c02640c044242e0f14652418680814014520b61060501580706440c005182616005c45810030000c21078400c0c005004491524000301500d00050039148041006000024148000c200406c1d070075401c4011107512406010000410120081c485c46100b110010120b94a031042110007030100025140044a03890900c43c200428444140c0266400c07130700c5015594641d54680304003041c520071601001e00b00b42c0480d642034038140d070015009009180140c908008550154a40f400c4026140e005900000c10802440700d03840d1a10f8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 641399406 1250 641398156 641398207
    0x409020409140708010b160320012306030706030e010f0e030327070302010c020d0c06020d090603020901020a03030b0604051e01020c010221030c0c1b041b170901021b0102 75
    0x1013180d410640c0852080c0507002410100b01400029030f02450700401d41c0940b072200241c10248003590080100e80038015140003000010b042003003101d00c074141025418481d0074040c00422000c8d00c0d01004601400c1025600c0c12155600c0d045c2200302021805000104d010b034a004581e00d0408120a04500e488820003854150f040200c0c1a040400843d65030112078091a12010914080c00028480c441100d001040303200f45020006856401040c1e40705400000d494a0907560b95400069040c0e1080303829580c0140c21401c62500024041c0d44aa4186480585091b04098964000c034070505a0350055652084c032901a4403078a40c0e0410282d161003400707101420382c881c42003100d518407848085060480440c0071000a03003880303501c1d003a140462000f0301190480d606050391944100d00b40303000b2501450030003d09501103c400d44070440d05510654406c440d4140a01c4400340208002c0d00195195408000409142500b00d401085080d0fa2100059a0b15203402e96403042030082481030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 641400656 1250 641399406 641399417
    0x10f09180c081003021309050c030f012003040f0b0a020c10050a0c0504212f090604020307090905040c081f0e0a02090105060315030d090504140f0c0a020304090204091407 75
    0x504c0143c50710071540c40760524010020409810742d10b80141842c10500b2141c0e01446400320f011500740054021824440700090856904020540d03071040d075101c200c0d00a840740315500c9041c4000740424411651001075000d0040c101048610a0381c101985500c100c1201754448085c00100301e03061080003528501c42c10201c0c43c040c03a0522148502e5409130940545800704c00001c4140104181c02d085062490601800c031258401188468400720130344041c02050080d001400782c2c2410310860b07004007200c2e100e44000501e4003000202411004108a580900400001900070010402c0300c014581001c2c40050510414107072100710360b00102112019800b0615050150b210120b0705811340d2410b54402d80d490b07441c41c45030b0540c05496500140c1503c280d55180d103103c2c0d40a043d060903604100c40502c09070401e0310000480d0344040d01c400042880540c0420130b9000008000e006940940c01502d003001c0d90794000808a800684c040808251140c50810f2042c3c055101c11f6070008450074030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 641401906 1250 641400656 641400659
    0x71205101a01080a02120a0204060807020c030c10050c06090706021b0d0b07031b0302030106020f07080c0d020a15051908040b0403050d020d0203010b090405070c11010f09180c0810 79
    0x14410304040c0c0501d010705200d882400300711600040d070101c031074013600700c1520449030401c520030b00001d600c680f00b000d001031102c0f40131800740c510105d642900707180024024071000400788200181043c8a050801c02d2102c100030312a0507000a11105100c3c60154014056442c0786c240081d04058010f0300c03295008105c081111400d9503208240c2507001e070801810041d55880100c20740040003254040c100e040707021074202c0000c0e54141c00850580303c0550135038a032541612160381c1d481415010702c101d01d030401c10300c860140c1002501022814001014000301071350b6501d03510310401c9072008c444009400000e035400340f5540800c81c001c0c480c10a24090303c051805844880c0c05081c091300080410500149495000c3c00d00d4040c3d4401e26a0660700b155a56510201280c1b07540c012b500b024001c6050000064119010b11001e0440e030b90000b14014501c9402001110b03d4268048034009019038403401150101e44001000d40207d20f114000649501540b4003800b18500280044401050703000e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 641403156 1250 641401906 641401931
    0xc03030705060412110316120309050c0609060f0a08040b0709080c09040303020d18171218161503051005062706072d020108060d110307120510 63
    0x101a58001d07040f030020003014100e4541201c42c1000768441c010350303110105420986000800100010308e21031418040f410042c0715055082d128101070181483d0007250140d0190304101c070007000343d8a030060a07580750516082e4041003581180343e4a80002d203541082204000d581c02a580d00800c1c1410301e4440145071401c00e43c1d840e0280c202d42da00030550803000c00d040600a4065519004170103e042c00324a03000b51721001c60801c10348065402032060a43c807440c0c11203000450700010300c800e840a40681d41c02d80000c0d0300d100292150500c42c410001018503403024107030484041c0c0807510301c100484140391001020307100054100d020462040008100d2a81c07900c0444400c50000750010441125945910000700101d500c0c494121500190391002c008407400b800c101c50710350502805075004078041c2100001800030009007c00c3e5580081025450058104008188111090740048003423401190500708160b202c50954022504c1d4a820000c1c140800402c40070500410000d42d41c0040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 641404406 1250 641403156 641403163
    0xb07030f02150a1808030106030b011d010c0b0717100305060708060f010e0402040f06020f07080606031f180803070906180521010216020a050603040309090c0507020301050f090c03030705 82
    0x601101c1015518124050440c041d90361121340e11740c1142c41c4039140d60759030350003501400900302c46030300080d01c00700b080d103003085401c2ca00d80b80c00006035205421400c0c580e403910b12480016015030140030854855070700014031139203094424040d48140c4c10002c1d1640c40d00c41d161400141c03a90040c8030441d001c005407a01c0d655110704145100740b0b403150740031144c0d501180003803282c0c1d0401d001c00c0d98501808605a500042c9881d202590007003111802c9075655070b035544400c1c00f40c0391198590031142100e482000503d00c007454500a45000133481c03141c09062180c490380c2204126503191010041222440d004082800100880e0038080d8161101c44548161000c050151502c1015070072420700c0359920440302d0704042000c000c001c5503502c6041850300701c00c0f90019070880c031441100001003070307a081100c1680d00403989500c4215549003071041142c0640395900c950800c00070180152005aa0240030343d07030050b11000c08154060400c01c103600d04141c0841103840c000c0d40100300b8240010b0000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 641405656 1250 641404406 641404411
    0xe0f040b03060c0a03090f0606032a1e0510080709050a08060a0c020a0b0403020a170f0712050f041202030601060c1709031603061b0f0507030503090a060203010b07030f0215 76
    0x90100c19074815942c801a8000c006d000000b44c6090b0581c5040030070415154000c40541e1300813150300a50f03002c4ac0032401204a4520341054040c0d01c1c05e0810858040d171035900e04000c1c00d00ca50340c88800c980364004603100091002c040300011f94840e09104030950800102405000b0507140702c280d81c5d05114520740e856101400d400107107640d0303031940b4038610310901003600080e03484101403410b4185414000d588409007013098074509200d084080015540108a84d40c4014881c42d084c00c055942e03c03510341203004141c40600b4060700b0405921241e0411004101500f683d0b44200101a682c0c01407514058058000c44244100c2c0054100030031100e914151840300300e110415642c01040d4042410072003854411040e02100080202c100869500034120001c040004001c00c420f50b0303002242c070614403003056404188200031500c0400d100c0d0008640c844114411100d4111140d03580f40100d0b4002da00c09481c1d120042410010180e101c04060b000000600c0186405000f9400120415401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 641406906 1250 641405656 641405671
    0x4061d0f0309010c15020f040e090102040e0f0a1103010b130b09091f030605070804030f0e0a05041109061b0709290d150c0207170601090c020f0a030e0f040b0306 71
    0x601111041106170080480c8484044400b5134440c2c052001c0c0700340c290054010300c0c100b1900e91000401c2d010051003618102c510700110498183c43d105c80e50300008002801c000c4410361261200c3c114841c2c40f031f00a500a0540540345076450306801380808040c1529009007403150410001580180d5800c10140d800c0a2020400340c040c0c50507002c0880956100c0d44000c0240b802c10013040032054105000c00d11660207a141c1e010401f1052000b01d07241188030b42040c0d40200e40e058180a1130030716a11044001d00700744c2c00030346413450400c0011790356001220321210321002c003090000e01c00000d10401004201c0c90100344148100c8121240720b40107a0308280300034105010110a050350340303200c018405500500b0b01c0d0b081d1181e00e50340d0342c01b5090031041c40001d4400d5000c00034000c013941d0180c110030711019003e04031503400c3c4484840901654010141148511343c04044410402d00c80c80c07000d24841d80300d41a000807110140151b0251031041c1c14440c51400003070840c00e4a001c60401e500200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 641408156 1250 641406906 641406917
    0x11407030e070306050709030b06041b0f0302120c030103020102070e0106021f0b130e0c010c0203190501110d050106090b07020d24112104020307030f15020304061d0f030901 76
    0x1006811841c01049070301c01340107141040c05010405030000b00f4102564010b130210050365990703609000940b20f40c0440c6c2ca100030283c20740c89078958440d00404407480384510b0050315000140340e014104030825200c0a100c51400001002103603010030103000205041c2c030f4412501e603d02000a5100c0c0034200752200c00800020400e0712000940d40054859080184480300c07607030032100c00e000100140400d054891040320340008240d8010014403c910340c0c028002e02056240c801c0d10341c80d01048c42c90403502c540d00e820200c904608210051700071802c03483e00014039985017550040005015601c98907021030100200405601d0380701c020b60b009d503000740c803401b290207868408024604400c481c607801c091502034469041d868440c002c001c11148000d14400407007107111180341c0c2040541e0700952543c00a541000000d51107031501594a001d8020400f8811b03080070381c0b00503a071048604458541e55814085203c11104400c40126070090004140c0c4030008900103030b880c8500300c5101d06014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 641409406 1250 641408156 641408171
    0xc10030b1e03150106030524060f0d020702090f07020c040504110105130f0b041d071707020a050102120123060d1505060712091a030c3006010e010201140703 69
    0x11803c1000142400002000514643c0d4810340203000b420282c40504a5118440240383d080d41c42484c2a00c00d220b0040189240060030740185409900c18921007078401d80a00c10a03002d43e560801851040a098400501a150104000742054000b9807064403891805040c000860303010b0182c20a01842030a1160362504031004626204c40598401c0940010080c004100d44d482540a042121039041c5030351180c41c481c85440031814001c031003040000707140442045411900034041604100b0500540300808ca0b42d8075001e003664809001100c0d02c075143c4004101111742c03040409a000031840390b821a51443c41d0004580b4844c80400d40580c40d1142c001c0780c07a0240c1c1c9001d2400400e001070010703503100211318054010b44610803022010403140300700021080c0c0580f40c0300140080a2240301d24599a034020b0a00c60b40241d601d03042a40a00c1050904985030301000c804064001102c80445250070000140481105403401e81164104407644001e0b2804030f00168001616040128208 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 641410656 1250 641409406 641409409
    0x2809020304030c1b090f060b030a180506130c060e010f0f1107151106070e04090c030206030a060e182d0a0309090606030b03060402011d120c10030b1e 66
    0x3c12100b4006030041000321100059280318101500031914814014000030400c0c81448003222680d104420f085481040002c0018003d6800038480c1101c001c0080d6500910351039107482c11008480c13001c103000180411b9000c0c4002d0804190040c0f5044c03070f010040500800c00246008003140d940b5080c0034085a21031f6072203000d1140c00285203109001c84003200d030740ea85200800c445511400d8081082202c0d40114000c0c040b4140b40b04076881c1d100d241e4071382c01040c28040141f0f000c1400f9607000c6a400000f00041e40d543c80218040d60000d8400304089040180c00d0060310380140c8564090301401a9450b00408045041c4040260102c440c0c0020b00d1013050099032003111074000e8415008aa40d50020035805c21800d4081e540309040401c0516200e1074242d003144c4e640d100d00c5500d50701500000e001984202524080703c028280c202d502400b4040109840041030f091310701d00c54224004030390035420400c008006180b0f0703a14092090480d80c07004604041200700b07201c1c801c07015086512046 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 641411906 1250 641410656 641410667
    0x4060c0f02030f0a0803150405042303090607060f0509030406090b130e040f0311071206051306110408100501050f1e0a060e030609010905121308010501080c280902030403 75
    0x25030082060740d40c24090785c5031840059004076004d900c0c101190100702201c1c00c1a11941d0302c99035004c07024442c560b036000d51100c0341c13502d9020341141520041003614021344480c40a040700c01e2190101040b00381c101d0700701000b91100204101050380c0144802c200300c642c40700815040340d5003141141d075202292501c12003035681d00d400c8450131041c15000d22080004034208041064040c3e07464004da0301c00045c070a519861940700f8081c4030281d80c59164041440b03584010780041c10400f41e0740c42803019544860a682c903c4004221010020a08000c54902071005241c46605808100004d605010001e4116a60b01c604180140801e05c4515002655610324504011004083d000c2ea80d5885400030031001c10a40240d0103400740720003180100b03805008107400198800083e11182002c8221506a504200104148001030100c005080d83c001e21426000e007044002400800f8201002e200e0032514155808801c5103140001c1040e50720800484800d5468040d400b40e5207072540d08040700c0d07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 641413156 1250 641411906 641411923
    0xe21070213050c1902030a080c2803060f081614060f04090603060e0a111009120b010e06100801050405060103140a0603060b040b0904080304032607021204060c0f0203 73
    0x28510300001d01500307503804000b900d0360f48080d48100d0131402c00744000300d80701e004d00611040807600700c0001c03900d159a41c4019020300144441d02440816008600541c2904450040008a9543c0c2e900380052207442c2c0780700d0007402070341005100802c9501e10704404c18010344100401d410280c0f414012640c1d91300115808808400d810544440d1104407039401000c00e440200c55192a00c0840c80c2100004034041c18a141c0109442a10150000a0100c1c941345101d0300301c01c0108001c1c0c04100c1029030f65010b070006014150140b119810a12201814140603040318402c091024000c000715520070240c50549400780e501146545840b0016000346c603443c002c0c50403202903c1d0030801282080d80c44541203e004100602a2040317070341c00e00084424201c0140c0d001280e03000010041001a8000c680180c42490b000115178114240182c14017954100e0f420401e580400b4829115810446c0c0314030404600000d901c1d0030b2400f003018000c84107000c2e00410441403421504150360f007d203c00035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 641414406 1250 641413156 641413189
    0xf070215010303050a02070f06050d090206041205060103050c030a0c18020d02070f0209010e0c1204080c06040515010b1c0f091e060e2e0608150a0e210702 68
    0x4940d5616490080c280d0341040c003c0000500ca803c00c0000c020f10030080c031004491458440307030b241601c6008403001a068942d000c0c1d8000004000020b0000e33040c400001041d07004d0300c0a00300c10750551411034205242c0180d064880c0d4803440c40800414803861010003143c0800101c1e102414005581c00043e0044a40c041c10444c40881c2d000b052107031290308001528400c580c06410b503a22060103800e1940141c0d0000303a80303c4113003d140e244040c622500c0340c216009405580c140410081000d10b440d030216801c035a103402940646007a41c0c001e590440c01742c0102d109643c2080c00e507001111041012903a000e5860307850b020034003580026580102d0aa5030080c18171020149030070001e4207444d92200003110554603091003120040e0003c42c1c1c01c55501c801c061140c5038180e2940b10900c0300d0802100d0a80c00b980d807540c0c00039071101c0400c50782c60312143e440740c2c011262800d03040da04112520060740850581000c1106404bc0b03c100e10800075062000c3c1140da22640207002040c09107204030042c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 641415656 1250 641414406 641414443
    0xd08130e1528050d06140f0702070b09010e1c0510020f03040f08120702030306011101090f0204020a200c010e0405040218181516050406022d1e01180b0f0702 69
    0x31083c0320700c0d9002195109140400f11b03115031a1510b030004003001c100d072424010f0300110303c01e000340c40c0c0c0032004240b140f0052420210a611450000728540c1d1403141c04401c0092405540701000418002e000841070020400c50074000881040c548600c801080100041002d46c0d0300c0003080800c005595001d10a09001c0c0480d25001034046c0d40c035401550102e012461552488c0c002071340c1406001c4940b41d01003070603100d105a540c203100180d0070082040741070011a4210301e46406143d00b4201c490191140286400002c000c000761144000b40340190290342008104805a10b5003000729800c04500c1185c14140c0d96101480d03003000e21280030760b00c060b009900902490481c806107440c020b00c000413410210310100b80d810f80301813240d4403a050160700100e40564030b0841804088103100d02d21140c146007228107594041c10585080c2c40402c0300c41c0f4100f04817810300000d02c07581c04012079440409000444e02e495044200b10000c19016482c81d8038400286003610a1017000f04804520100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 641416906 1250 641415656 641415679
    0x50703051614031303050105130206040b031003050319080601030e1b1f09031106031e0a09020406090207060b060c070e1005030a03020322060801140d08130e152805 72
    0x4111080c04e9100980d241d6080402040502054030803074060903500401c0645007a190815038403050b0001410301e11107041040000002c20b8003440101804029400940907000c01f2001c0070f0318400020b440c0d541018504011010304600001d05442040341c11408440035800c18000035815800f90440080c107001083c102c03842d4241c205c100d410a4034411101e250210040c8401d1103036a000890b011601040d00c0b68a5505a03070510924a8100e00ca081000c18010065008a015160181e02000071a0341c0090f44074140702c041d100320005042e00300c070040d14103501032072343c550b89030b5050180c81c032696040400300d00451541003514008100c080d00703442004002d4180a0b48035048401c00704c58425007a000da41a1000f40b101010642c2c40503100d503040c0b40d0070207110001c3c800c0c0c0c0c00d0304681c02141d02d0303080001256104010b446054000d45c0287c2e101410120074405030703030024104144428200d0f0140710940d03030307484403942d2128010721080702000706606907040c1009035521860300202002c25 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 641418156 1250 641416906 641416927
    0x4030f240f02040e010909050712140a030e040e0a110f0418030801031a06011403070203071a091506090f09150c070308010806090c100216120308010605070305161403 73
    0x79000701d0f00f890364100c810742c0e82d8000c031005031a1f421000800e0360708042c0c81032040c8481c01040c200514054807000aa040303031080c000f80390480201c800e4000c160b02c0008444946800d00030032100040d4500500300c8162a07584881d280100c42e9003492046203c4040c00361140c4680c0e10800360400c00040c00240e41c091400c01501002080c001504d544410720000f249690700c135128140941c00603074801c00c4c10b0400c4014010980c01c05003c10085020400034103010031480100c0450045159180c9401806c04810035440c0101c05c0c40e0383d0900043c50301c10030405545140c3c00c1988104464156180e6954026415007000251400403202041700002d2051110818011f0440184a5100e042003640ca82075819074500d003c445801c0e0550201091811a052105501030141914011181d01c1c048240500510302c070540c101c0400b24848140300d00616a125000303600524540c10b050345001c181c3c0c2c0f001800c85c0700d551207100641c510107054108000c0d030f140c260b100b0052140150394a80d4507510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 641419406 1250 641418156 641418161
    0x6030c04140403020c0d080f0901110102181c031d060903060f2409060f04020d0603150f022701091208030412020c01020c012a0b1b04030f240f 63
    0x54040d801441743c1c010b0b1814600b0250064003409400c455403504254111455000320781c010540e45040007140d503003014500720b090020304a400c0c2d6407100b038414440e4800a120151510302c0342103000c1c1c011165041c0110b600000705070404210051410f50440d0407801088182c85a00020358051290000b00035001c4802c0b20242e004014141041e0990840303207202c43c5100c906142440d5000c03a1001c042085482d20740200c2003940d0014201504110b41803880d07030122a00380c0d0090f02c10070044003540d4841e4929205002003001c255070308600b000340050f00b1f1002c04030414411540420690100c4006038069220840241001346120301e01c0e1b80d4a01e840d080581003950211008414116400300d143e00214105402c4001030f4010041520070000464821413124071f14030203105516200c40c0d2200280030300c105000e001d40d00803552400e190b4440c000074843c0d061140c03004202230000f80b00195100300c041003540d400c44510f9002204101c025075450041d0001c0803481d0385041c1541c4250032064 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 641420656 1250 641419406 641419411
    0x301180b0103020f09040c030e030a091a04030b130c032001170105090a021b1009030f0c0302030d020309030d050106120b0a0b0706050c0d0c02011a01020a0f0b06030c0414 75
    0x5014080c80803128019410381c05404400c0851034010f00800304581020b0380440e5280c00c95140200310540030200311401c42e4400040400020a0a8810310042c0d9407107850350001c1c0c50310300d4001d02c0e0070f2854a607002001c10280c40484e0100c40b00c21024107001003050f80f85c0213190451140d0300402044980d206076a0b0040a40b207011500e91100c00c0d52a299820030141207800141007504280e907001c001c00e00a5100c20170000c82a08401c8400000341c0c000c104a0707060900701040000d07189420f0034060080d003001d002d00f070208150074440c580043c2e8088280c0d00c540e42c0003500562652601c6c81d42d2070035409500c140010741c0d4a840000110158812132040c50741ca1000420040e40e02c40500b030040c402c02d035018203094220104100e40020703203981c0c030466200d407a0a43c4c1c541030905149010301941c24404880006030344900740d02030298540c0038008241d1600340003c0a40e06003d40c0c400340080c20480d009084036101100203807203601c080c8991800070400620401001012108052004405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 641421906 1250 641420656 641420699
    0x50622080a020714090709090b03100204031a0c0703051207200a121803020607020a0b030f04060c030506011205090c0a0f09050105040e12090414010e0417180f0a0b0301 74
    0x910191000c1e040085c02c45000d00010359034500e100c0c0c101a4140c0140850b140c065805205042000c0103071a803901c0984060b6129003550b008080c0740c0c0810050750140541007910741141005404002600b000483c0c6040100c0e070f01b41003090340d9401d42a501e40c541318038001581081009900d504201c08238010301e8651085202c1d04d400182a50121103181c00c1214150200704486401c1c0007500d00341004d00101807005003024a81c540b00c2001401c2034105544402c50420708005010400c2414003403107800ba010361908118510703045000070512070008001448181d69800072491455050216540788500a080012484c0d5120f040d861510100c1c410410000d142100124080c43c0602604079545241002032250900b44101414694403211440341e11503030702d8880440e00d520442c64140240030b044a100c20a24050511058203009511410807a1104112141c1e4251140d15240e03d101c0050310b903114011180c1011948548a03500001d00c515004000020b070b02d024402250600030b030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 641423156 1250 641421906 641421929
    0xa17040c12030203281b02060d0c0801090b0619030902120118030216060806060a022806150b03010b07020d060f05061c0201050a08060415080c030712050622080a0207 73
    0x42c14150b0100355075100c01000014541c4414088801084568116587c1c0001c040d00c0c50144d40103d03003412645103541c46030100d29900f004006038503903440b0700a05804151155480e004000740040c80d103d006588500a1590380d007090f800350744898102000b04203502c0008c0040c60810350000301c103603481407000c400500c00c1c0c1c1d0001c440d030b030390613188202280e9840d01c5030b100c5a1604030400140c1d030000f0108408500c110041d4005007082c1a40c8801d85507940040ca58054105080410075510440413409250b61003900420064540b80122811503c030f018825494016074800503030703003110354000078010b9801c101809058900a5002600454003240c1e5410340b4803d244000b0f88c407a40c0c0c10350182c0450000d10008020600901c00302c2e501180040001641c4126400303004001c81c11604440364a5024440c41442810308000082c05400c2000c5000038500740d994416540d80c0f002032a4000204a0000e8107a441184c0c2c58074212166004440544402040c900295520070714070840600c0c88 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 641424406 1250 641423156 641423197
    0x70e010f0503070f03080702060c1c1d0109180b06070c08190809010309060905030c0a0b0603160b0f071505090607080f06100504090c030501090b0301020a17040c12030203 75
    0x2d40040c0c54000caa2600104408040c07854607402c003a0b03003200c902070341c01510420a0300c1242e030003802802e2404020344051148002e142c240107014054465070780710f5241040000d020031360382003480032044900320350303042d40030808402c100005041e8000400350409404200b040c10025040c00302c8098800110489542c0c1c080910203500001c1814006807861100b0803454025502c42d8020390400360003040080b80740b07601079850628603400200916115000304600000b04030388400302c55000310046000f8004500d0140e20072049018600c951902d803000014100703140d280b0b000c1030310207154225000210026045555801500044400103c18012030000030115800f031a1404d0043c0c0e03a00704000c0e640d035501130901c540d22181160b40018858107001c0051740004500801441c000c07682da0103c1c2070352524510384150391800d034420313201380d00602140d2401030340000150a9004003250000481e115428201c07100107190f082050032015841d0b80c1004d06800100604204500040080540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 641425656 1250 641424406 641424409
    0x708010204150f0503131a01080c0910050a05120709020406051c090f020f04140c0a080f0f160e04020406110d091503020d18030207080609010e0606040906020c070e010f05 75
    0x1c90389400500e0115101740081070038074021082c2100040d22a12100a801d43e008044020501003680b080c4030550162030010591b00b0030000194100e2100a242e016041c00c21002441404903802528003401c4191030264069400300076600042c40b00300001c668540d1541e10041c1994001c0c01e28241d026041c115841792002e56200384400727542c111100d940701c1d9600703030700700305002e40103202e40359000b03840e455411700d004850009240034111500e0415503c10010402802c81440102002d26000ba648100807020124120b40381e4001c55846698010300b60b00001640c208000c0c031421a00b02d840070502085090304882c0b01c03512142c1c5103046440000d420201140c0501c40b60045024190f1036030300c100c18440c02034000d010380c0d54030001c000c10140c010b0242c0d86601d02c82d03440c003500180d111070b00070449a5030a000558100c121440280404494050015511a405419940a544c0e648a981c041c40401e0307040e95004040481a03c813003d6a49010b24980c02e000c0c0141051270440c001c4c000b465 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 641426906 1250 641425656 641425667
    0x109050a12030807020f030a1d090703020316020a050604080a022107140102090f0405060d021c020907080708040308100512060105030f0c0f0d08040e01030f05060a0e06040b0703020c070801020415 86
    0x41c4002c0d00000c505c2c040020b0400c580320100c81e84103142103115403140d2109c0e50348900c1e006204a590b950016104e160201d444105a00711400b9002503404c40c2c034111000c40c02c08901c0e81d60241d00601c0c2c141d901c8061a50807898182d0400c01c00090300c02b55404104000d03106030003004180e000b54a100000c9540030000e600300c0c8104680f0550205500700b440e41d890619800c801c4d1302141c0102a040700942e1034002c6525201400030035419620070a0042c0c0452070203a00300340e00b0058a00d40340c040f51408490140030044c2c003900103002c0c0001c2400055181e0590b9404201801d0040c0c800148880045a0655640340a0003280d00c0b90040e0800100454400264542c04020023030062101c42410b10070721070700b24103c3c0302c1941c8005003000045207401a241c0620300851040103d0501070000d170803e54101440945900c2c3c080b41403420030607001200107495034215800030703483c4103103407a032103400d41c000d104400300003d07a0301541e840000ca41c81c0650203007003211005a0f244034030b1903800404642 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 641428156 1250 641426906 641426923
    0xd03150509040b0405011e020d06120206030c0f25050106060503070207170a05010213080d0c020a030305360f2b1403040e07030f11030c090109050a1203080702 70
    0x10000d2403000042c010803080305100e0b400502840c00040c04441ca00030f0030b000d4800c00281e103424144c000900c1c0001c0c42440c454440144803d000b80600e04409500269480c80050088520b510001c0b0344020704043c600101d40302051605441c86461181503900c1c1024400040e040d00c0300d500c1d01c0e00026005001300210f902ca03003010342c0908a45428040000c00c10400400c2c140564405c82405034000342d424401043d19407000081c80d00d07405c0c90311800c44d01d0400703410301180401c03078012003030401600c8000c054004d0b260b0ad4180305031500c9001c4866100300e1000303641d40e0080ba100744032002540c0e00001b400c04840750180c6801d40c5102c508000d1290b03500707004080c400007401141d500c012030324000c83d072500e03514800c1c400008203001da0400c0e00d203150402e80105003004021028031039455010301c25600c03024612842448008040d1060020600000b0090311100000240034456607210703801f541e0103044020900000b540c0c5a100f4a807040d051b0500c11804290a0004111810b000099a49 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 641429406 1250 641428156 641428159
    0x31a040902030c01050c0a140a210c0303020901120603141e03071209030b07030b04050a0e0a0b19020c010b0108060603220303060312082211060310050d050d031505 72
    0x400f01d200000115401d500448117960a03000d014030780400a083c04040300c1c43c2d08681d2000340030b619018101030708040100f921140b00f05210080441000740c000008071110760701801d005844410b0000140c900442850450f860700d072030107401208004c1e10f111102d1780c01507a4821250140302c0c0d0100040d002d540040c2c3c2d40d480c1d9006000c0030002500200c030140001c0024603040c84002d82d266600498140706465140c040303502c42218080505103841015884000454103005080307d15503595210702c81004050502502c1000054005d4a40c0d20400c0740e006103190300315900c00740c0c0c0c50514001c1041031400ca002030100004500300d458520240da0048014500142240440101034600c1d04030781030b011024140c40313010010100c1d40c04240c5451031200758441d0896890401c5c110b918105480404c00312801035081b140e404a1b0b052a04044201c4050355025030faa1541205030f4100f0b16981c2c4096440100c070b09441b0708000001c90128102117090300c4c184403995040c0540032004425010b030a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 641430656 1250 641429406 641429413
    0x100806160f0302070b0c0f0421050c0f0612070203041214190c2328051005040b0309070b2101090207030c020d020f040e071d010f030201230a031a04090203 68
    0x81028001c44024140e0b07c2054401c1c9280503510145c3c00b00c042401030100300c40311101c03113034a01400030a00194000850440e03070181410760f113600040441c0160711070706c0701248140c0d00140201d8003c208540c05004074042103044042c0500d401617403258001c1ea815503901031003100d130034600c808044640d009680010108003050030010702c4038401c1d84a03195015421400c9100103503075180c06c02050100c02c1e1a80318031b4200c0c0d01903c5400c9442030305900107802086607480d4407802a5100095806603024686074903903d890700005903240945c9a04002c41e9446c0002c0c40c00c800c1e0010303040181c42c41410012140203680e0391845541240141352002e03000c281d010300801f0052a2034043e02d4101c61000340342c020200c00040c00308003202d40c02c0512004c20b91081d6010302402d082003000c2186c030803490201c62459070424410728031031055413200906000c2d0803040c080400d41c088140b68801100d841701142c6500a03070310004e000c5c224858210174484601c413008101ca04040c0114042c0f40c1d000f5008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 641431906 1250 641430656 641430661
    0xf0a0618021309061d040503070606030809010e030d0509041a04020c0c010f0c03090603020a0309051f0e01090f170409050703060f0b2b0e030301080a140d09030605100806160f0302070b 81
    0x1e501700031070000d00844043c00f0802040d00080c0b45840b440d0041c40c021000d40d038075803130303404005001407041d416098841d51060040703e03a400d038884201c0e50035036016140403807604103102c4058446802d01c3d0610f0b0f4481e0020030090020840000c0071509600709980e41070300c4045001c2d054503d40003843e000340000b240d00b002442414040d0300103281441e0141303030000d60b11080fa1242400c100642c500801c03445601072410141499034040c8207180c20110000700104c0801d543c0d003203860b0f4803e600007040d000302d080610b03507103201000a990082001b690240882d1030102d2008005000310b014940400b800d540000c200c24020300107840c241102c04030b4014924080c541c6851800c0c400d409580001501e82240550b451403d001441c000c201e9030b4003c10720103143d03280c4108481403104210607035030321800c0543e00160b40041c0c60002c0300e4012030001620381781d00506449260b516040500b607032007001c0901c2681440d02c0402694000746a0f114127400001031021020b0b031081ca180034102c076284001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 641433156 1250 641431906 641431949
    0x405120f010c1b08160218090606120606240a0c0506010f151103090a0315050c03070804030c0224120f071409040b090c0d0c090501080f0a061802130906 67
    0x2089002c01c00300f45d901c1003103140d07030000301156440022110118000000e0100402c0308000c542d40090044504244200910712050b81c2c40e04004d151a104200358286581880381e500c44030700c007a841100c032090360f070b1414840152103100d04030380440eaa0312540000080c1e9180300e03450b240990351304ca8000c10010900080403075440b9103800c5c46454500007006074103640c0d40d9541d8800d0040d44075180c2c0c00f5500b07035081c03001400c9901c003c011294007039081040007046944001c000b580107030315080c40f01d072549481c008168000c104140352104e98541c4039455100107030a90150240c09000d0100c1400d41d80c4081042074212402d450400c08141d0f040401a40608000043e04010f00003a0000813180c3d58400000d40c4038405890441c04208000740506d8100507a010b0081e008055003044c050580c81c100c0000c1c06900b000709900498402c14011075240149034010000401c205c071010030100000d00c202000a47c0402c80000c002e9411940004d22003405000705c00c1219400c1514803100c40c25180c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 641434406 1250 641433156 641433173
    0x2061b04140a05031b0f100c08161e021e0f0f19060309050708030304050c01260405060a230c07080c0a03034701050405120f010c1b 58
    0x91901d58400c40724080841c0a031000c1040040d00d40c14035420400000420092103030003503080751041d01914400520005080c0c20501ca510340645c0b00202d1950340715070300401a001c1d0400d41c80100f400100c0380824816030008540c00c8e0b5954000c99110190b0520b2000301f100c4500380c1815640c01c40940b4200c0c0c3c030940b500021a001000d0081c000c4000089003a00158070a0800d80141c004690f840100e00d082c080d040001030080c10508000b076245041c683c9400359150181c465071810000440c4080070050010381c03102c0b801076480c45000c0f9a03414503260a54480e40f0840302d190910707281c4134668050340c032024042d030381160303451540c2240c40c0c51780c140b0300080b0ba00159040d55044000c002d011004030081140c19000f034000ea50014114071403040030042c201c46045680c00d61444c2000541d1502909840e080c1d000003100040c4811043c0b00e0f0068405001d554001b40d03200c8441c155003161800c01141351404036041c2002088840d8801e041516402a0380f4010241c000b000600c4000080807039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 641435656 1250 641434406 641434439
    0x10f0c0b01210204020c0d1404080c1c0b041104051302180c091e04060911160203070f121e03080406050a060b1b0f01051303030908070204150602061b04 67
    0x10b854450040b050340114083c0c1c0e00034103c03c2600d17407141e06c2c045200c50b0300408294441034922446450203240540c2182c1d5507503800030191007402401030028203a11440e00480015a011030180c103c0c1c501810f0042184103c0358840b4011070a0038001013000300c1e00480791411a5004010b000305140c010a081c04d803070001010001b40364001c008142c4140c1d90844045945607080b00090007000c2d14078180b2050b1969a84000d900c581040d007200e2605400c001616603944480032840400c3c1e0460002034980011540700c11510004088049603058020101605942c02034030311070f180445881c80c126411100c09406000a03004c00086000100c49400c010b4204000d00000b04405890f45030514095200c401004030035003c0d0103da00e03a25805102040740180e81d90001c02283ca0714036803050007001c1104000b07003090740e1184141c04002802042d1800c0301d8019108102c1046600e024404000c030300d003e00c4016224800000358803a0b400c041003510704a110f01c0a0b42403a1070302d211803c203c10f80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 641436906 1250 641435656 641435699
    0x190e06090301060f090b011d0105031009050a09060e030702090f0a0e06010b031510020d0f090b0a0e0a0905060607060e0c1906170c041710090f02010f0c0b01 69
    0x400411025940c01d010f0000680015911141010320742208002250401202c80741400754510000628451040807815400000c0c00c219035a5501c1c0b08001c144030043d03405c0003009920300010300c425668203601100260348590020000013040c051125524021041b00a60004481c00051001c58140d24081c0d0005464103010444480500c00c0e5424018240c20581c3c040c03a02004011000d1500c0111480341c0c0c82c02c0d912480075011820009454a455980f08010310080c000711481b072030710480d2800c00801c0c081489540740d25100c0c400030040c1c0b0306105a04d01c2030810032400708041c1e03924803450340145070040c2080d2414550f0b80d50b200141030003000340e035224051080c426104d600e400c0b040d4404143c28001003141c036070410304080c01d101c04983c2546800800b1030200605002182c007140e042e612003080c00c01500c1e040305a028540540394800c91402810500c0c248200b101d051840341056100740c8560700d0000b21950115800c1c1100600036040300402001008441c07803008130480290724 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 641438156 1250 641436906 641436919
    0xd0207030909020d360602090d0f050d0f11030904180f0f021005040506120421020609010507050313020d0602090a08070305060109091a091606030b01020f0102190e 72
    0x80c2d6059820498100006001d41c040d220000308601c00f02a81c5c3c0b9188075022180c1d003113443d040000d1900700a103519500240a9680080c01c2501e030368411642e01c0c902940074107442190300c03861901e82c0d150481030100d171010410191401440c2401114000d444c451680d00540c282100d000c1040041e140c4401e4056051342c05001c0c94000c250302040c1280c401e80540c400d12030481d0075205000326000082d441000700182030100f0322a43d55404211914034009019200f030640f550708102c9050b000f0419070a0100c0d01140c0014001900424021320401c2101c008010960b00d004003134855100458402300c00743d09003001d4000514092007003185840c0580c00050410544802042d2451000c0d00040d0b050740c00200c0400810030104103940c050001a281807010061603a110421441d10812401d52001d126000a021150805c456000c588030b51481c0d0500a603206030140c01842d5109500d801401000b201901d03a107014007c88851003135032078281d92030304501c83c0100c0780c100140498990120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 641439406 1250 641438156 641438159
    0x40507020c010f05162a05120307060b151b0714010906050a020f06010b25031b060227100905030615010306090e0d18050603011215050f06010207090603080d02070309 73
    0x3032a5170b000c3c0c009502c80460038044a030242c808a01042da02c0e03881f807032050004924520103210301005070790714258096004500c0c0074000b4001145e13080407880b00500c1d03410206a015151110800714442d01000c0d9095075130326607c841c0041d41e0009026007507400314401c45010008207214000402c04a80c640c4160381088000e4070340181450401e074031003e01001d02051102c0d00c01040300c100000038800f552443c0800c15942e0300a404c0748881901000640c0240d94071206201041d0100c034480d2008060544084042d08041d11800c06030200c102d0091007082043e400043c0a1122038080d600c0c01001003034260f85162401e41d50005042c2c000341019113071580052038200c0ca001c2c190741880f404c030261062580c041c3c402001c0c030398840350341c40500f003110104200d2500c42d082120b041d81c4950a0b001007204490824a008403c80d441e90540240340c40100070a510203038000901030b9600b68281c813002a95444d40b070068440e58080500710301410007614500400310b80c02454503c0c400c0c02c094a440c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 641440656 1250 641439406 641439413
    0xc0d1106090a0f1a13030609080706050f010311030d0e040b0d0c0308030a111318112113020a050904020d0b01030c0509060d0503091e130b040507020c010f0516 70
    0x914283e0b2090584030400074060204c10402003004161040403013416040c40219414041d12400f28800030384581e0380e421000d07040c021200c04580c62180c0008042c48641040c00c02006203400034442a1401240100001101c0c6004950b001c0e00010594800c0004203c1c541040000c0018542142d0f2101c01244520000b4401c1c1c2c555100450191b02069240d25081c1100c8050303440404034000c10800400140001600d04001c107000c3d101c01d941c005505224490420b03001740004020f50001e4280400e803110108184004154130321500c2d00c2d4244562540301a400302c414602360001e500c14840d500c280030b6814002aa00e0303001d070004103041c6251090f074031001c7ca20402a081a50003c3c1a03030001d100f542084101c40ea08850185c1d00041c1d442200d840381a181d00500111600c100d12440080415400140100d078820340003d2141e0003a480c5e0490039002080c01c55882409030b418030000666a078000f141c0300301b02b85810307140c201c2410740d525400c85181d4080340d17060306a030b440103034141c0c0030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 641441906 1250 641440656 641440669
    0x60c0b060420180a03051c030f06030f020415050a09020c01110c0a0308150603070806040902100905030106090b0f100210090b06011704050c10050c100501030b090c0d110609 76
    0x40c551100d4041d91004408a00f015200001d00c442e0b010340c4504000300700003200080c0b42c3c8017455085c5501c0c100c8440c84503045006c0c14142d00700d078100c0350130580f001c0f0920000705080701c00b0714030845080100324500005803844554030310407254072003d8490201701c42d281c00e4008240d10282540001a0150b50310710401d015000f02c0e200c0b041c998089070b032401c201a04105086c1c4c12031a540304000d0303510082c1e400205140f200030103201c20451448d0210b8925141c54016806e0550f0003000c0818a84501900400e00341d02c80c4552031080d0300304030000030508624031518100300000f0302803841c0318480708140800c0880720100c01b81140b003200c0440c0c001610501c10046158403a80c070855250a0841c0010400d8283c181c5000c8402e000c076050200080380001c001d4442c04040d0780b90320070254045401d0307826010340c405801703a41c0210365032520300b01c10691015050341d1203200c500f02c0a49940001a55884000152a40001e0501105c50124103180c14601d404000180043d203080c5510022540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 641443156 1250 641441906 641441951
    0x8070e180403030605090f0105061b1507050c0c12070b07151103071101151a04090203041412070503090f040b1e01030c05121807080f160b04060c0b0604 67
    0x130b6868005109914007030101c9600082021803022195062000060151041c01407100d4000003c640790311100030280100c0481c95103c9151001034904610050311650003910702c40c0e0300740105229042d040c07030310421502d01c84900c4001009003501700303030003140b40c3e0781302d01d8060b10480c11441580c42c1d501a035004026144010071542a22400c1a02d40039180780d500c91209441030f410040d81400701c503c111441c0e0122820701e80038a565400c170515600d0548995008210b40340c1c000010002032240c0c4c4141080003941100403680200703442c550119840c06903242c01003058008000e07104032840c0070901d400010070700500000fa0301c1340c81c00004d210080c00002c4030300f0181c4160a250199a058410285502c20070300340585840742020052a180760000e050320304601c100707002601503071010040500a04102030032914501c3c298a05980d17a84414000a001d121300072030003207481d0191030140c900f22005511601440009035079403c3c00034100408880d000ad41e00e400d0700706200c40c0000c01c00c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 641444406 1250 641443156 641443163
    0x14070311070308130f0e06040b0402041a090f010203041503021c140601030c1b0213090f03020a21050405060c0f0102040b0909100f03021507050115080d0f08070e1804 73
    0x182d035061300300d400c03600340302d4503034082500e44000010030401300b00c24032401d9520480131180003c0308c8840c0d05c0054028000c0d504101900e2169242e1040340600900051501c501c007194054000031100c0012030743c070312950080003045100412600b00d058001e030041c11071260800380310f4a0082c80005404100c480b034883d60340c44000c6010521485580512030010550498501408003409030354418007110514000207000301580c4980070481c0340c1d19803280c42ca060744042c0321018034809040080d95010f03c0070040d24140c0c082803070090101c0348210301c220312107010341700c032400d0610300810400242c00062038444a401200c21600c020341c003c1c40240054070486154507124111241070000311100144020b030300c28071040d0244034545903603801000300d942c1240c1d01506076518806070040ba0241980003002503092a040c03a80ca040c0548008048e94081000c070340305016500320407207800800320f01c10404a00d080c404241c140d071188845540e43c1602424a001d4901c40701c440302503807481101e003034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 641445656 1250 641444406 641444423
    0x12a1208011e050a1e03080708210f0a0e1f06090c03110f13030804080706030b04200c01020f0f18030604030e04050a060905090d021c140703110703 65
    0x184400880c000302e24030307040034032828000c4960901000c01e201c0030003800307003d03070b00e405a00f41840c03031600f2220b83ea40596800b42030b5640741c0c029881d1600c00d9401990102d400f800780f440320903800c0711500d60500d1007001d898600307241940f602803a580003094810341580d420b004400d0042a1150012030042040c1d071401c1000952070324101e40c0c00d0881c0c69214124042504200841020602e1041a0740ca000418014599546002a256038200310303140e10081c10103d01213000901d816022900380c007114019113041c404048002c0801c021201e00b0304000d41400116241d070482c08148a010b450111042000185491182c4c0003003401908280c0b804034100714000380b0403c5908130301c03440206003613054004241500f40343c0d9000d484201c541c40d00714015a130f50070005609502d07a4009100620610500b00100c0c14175400450300d403000c807003076000588500c0e4000c0c926400001d1088800c06900c5e42c030342d45075464110080380998007440d0b0980c00c2110904031803501200c1800800b00070362046115 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 641446906 1250 641445656 641445659
    0x80f0c06040c061106010b031005030a080a03150b070b091f0e0706020a03021209010519020303060a0e0c1c0b150705160506090d0f0602040902090406090b012a120801 73
    0x2c00300c2c4030160040802c0282c4180341d40840400020140d041d40c030402142c0740c403540e60210244d00760103036034001c40c0d06108180d2000144140e00c8010220b40410750303401d106101481c025290294818828080d1901d0300300720103004640c004440380e8102070420309441072940881c00140c000c0c00700d1050306c0c44050740c4901850180030100441e030024941400603146108007514043e44902e0300880b07a0707440c5400000c12101c42e031b01c56002c13118520700004205880c200b031001c00954a42080300d40d28040e82c00018046492440741032001d2040c0340c444a111b18103c40c04426101d40304c0000c0314040c3c3c40c0c1d01c9400701c04143c4d841621038026889640038054071615181001c40c582094000b00c80c103403802482080c44292600b030126402c50b6810b8030300107444442440c00c02e891201c28200900554030104012401c50459001001200e00846091107100d0f1985181d00440e0700303183e900c50100b038106403c0b5a00c0c2e00c02164a1002200030640040e900720f41e9111a0310070f0f1084d084040010b03452900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 641448156 1250 641446906 641446913
    0x108040320011a030c0a050108130215030603010b0406030b2a040b12070c03021e03070606090209010e0f03070302090903190806040609150e0910180b060d080304020607080f0c0604 79
    0x90750b242c0f03240c0450081044040305800f160108595024841c10411100005001401d035104000800303a4040c1034000d4a48101d440340100d0b40050320202d209500b059101d044c47e107064003d420a807904482c0c410a80d40300c00d50702c2c00d039003460801110398040c91100851907903070f214d40143c0010711000329200e68682c044030000000c1800180f190040c80f0f000755841c804641d00150b102c000410300d0480030707150301c00d0701c00c06495400f0b131000003007a840c182035003c50200b0035500542034003402038072603803c0804040e040001400e482400b80d038040d44a040d0400c01340c50302e400340d43d402100000c01e881c9401e40741800f0003440d42580c80b0640208030f0381814000d075402c0c80d00c00e100084c0b00600c3c0401c070a81411a1100100905100d8078100c10450000308081e0101031082c3c000024440b8403c011a0010030841c40004d60814000e540421080380000c1a03403d00d04607a044941d80306140301c0c1f13103584076401c114103034001e40c006070307071041d42803002080603115040100407903032220009107824a428076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 641449406 1250 641448156 641448191
    0x80a0e030c07090518060703020f0f031f120305220e0705090f0a150804032a020307080606150f27030607031a090a200d0b031209010804032001 63
    0x401100381041e005c03022004165002c148150807511620380503035200080040620180244020041001800002e026141c071100b001d2030030165035010218500f40d59800301c6001840c16042c0500451402c00945032102c444000c082c0b440041c0c01c080d0310100f500d911601d00580011102e80d401f0910002c4c0e000c0003880c103542119403809080f6401c1585d2414409055102c100d2068150b050004510100d810035014017542c0102c4160070038502105014100300e041043c94843c0242d0282c042c126000c641080c001c07421a1044074043d210b82d081d10100c1e00950b22990008038890313401c003428444500d168803070019000b2421400390700ca0164445910800d400d001001d0449003d00d8606103c00c0a164100751000b00000030480701441c40d944d540780300f103010740286202d1034218030b209184200040151805424002c2c6010b03400c1001c000709000f81540c40c1600d03004091054000c3c80040029032042030644d600c01d20a140c410840103020070a20b03d0009408100c07030440e5100d44400c0441400760 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 641450656 1250 641449406 641449411
    0x40311120a0506091603030c0201030b181e160206010b07051f0209100c0209011206060308040b120a050105061218120d0b0d0b0a0908070b04030215060603070f080a0e030c070905 78
    0xf52401170b0146141c0d0081c1c01d1020844009050540359800e0608a94520200d40345044405958030407078500b41c0201e020340d00000b03503103855062601011401060035040c1c03404080200d42c00400c0d484e42030160140302a00040c1044401d403242d01d401840c07500301404400c00c1e03c10314520160b01c1e80704072000c000340e2910b1491200e08100c50016000c01680d503034280981140d0a18514120040090900b200500301030341019090080001e000141740d482d502c01841480e0460100803040d032541031007201960000e203c2ca50780000103000300e1441d69041c03140c0c2604081a0208180c0c038000c0f0310506420610303e007841c00031034100480c0050701c2d113003a4001d40c000b2250440c1d021072036840e02e550f0390802c1480901600c0c0010394031510f200400010700c044842d281d81056500710140740c81e1030000c0d43c9000108007480d07940030280103d141420007100352ba0241e940c980350202801c0c007039201207690742801480001b180c0d459a40b1824a04002c4c801000c1030522440078183c0c0c2400c000c8421300b0754001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 641451906 1250 641450656 641450683
    0x4050a06020a092111100908030705030a1107060c0602030c0c011d010f140109020d0608120c01060905010308030a0b03071805040b06060403050d030b0a0b0c0102030f1605040311120a050609 83
    0x1c808813000040e800103044604602c04841c0300309a0300d250a01110b19005ca60403c40c40e610000404000b4440c2c00030252407400c089a1383c142c140c400b4a1100c0c0d442d2103031441458040380081640383c000501c1038019503441015039400d2401c00030300c00741c140d00359041d8444010011145003290b50402c0000c2c0118604254448010722103e01c0000f01d0f10315114051040c0282c20307034040b496564485090b00100000c1080790215103005400301074081896000e6084045298681000000c1681090103100d0480e500103034041d00716034550300300101800310f5400796075042c0074045001c20303240094521050114a0307140000703818602842c0a514515000c0c0629100e44418032007000000c40001d68141208940d28000c52144c40c20b0340030840946064000c000020004a010f070111503055000c2c5101d500f0441c241069500d47d410122500c851802d60b24000400421050012820030703403100000303000c0a0003a07415541c000c40c8a608100542c841240c076500301ca000d0082d000820400d09460459 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 641453156 1250 641451906 641451959
    0x608070507060204151d1804020301060e101706240d020a080109060f09050a1b05030607030911090c0412050f03220806010518090a02130b0103230105010804050a06020a09 75
    0x18000c001f80708115024050152180044001011900c00b904880001c0108903090100360409501040540790580504a14262403884441c0503890018031540180c60700d011109034100014001156046c0b81c8800903009a41c003242c040042c0c03100100130008042d85000003411090516204003039400c0712801b80111810205e401c80480c0003c56240c40456100b2110240b000e1801c110031541030080c1d0010354140100401c00c2107198040e00010b000c503109840e010a1500f10101308408180160307880402441c0074482030058140700c00e030404015018000b25060380144500343c80c59680841610400710036000200041104034951100c017416a05014100c158108000b242c003240400078864981c100400124200b850300b80000c002841d0058504e1381d0508105683c10003404803481c0450003c1d107450003040c1d502c07a44101a9000202c03540302c445641e440c08004641600c3d024205130740a01a4403003800025120303100801220250341c8419140d1840d00e01d0071180307402c032070403042c001d6074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 641454406 1250 641453156 641453207
    0x71d0a020913022a03030f070923101b02061e07080903060705120703091106220824070215040f020916020a0b1b13050f1504060807050706020415 64
    0x4002006603544a100c1410540c51950340c2301d01114980d90660101c13641d0500070035264005036280301180c0820300300352406040340003c03c1048424101817801c1c111324080e054403110052070800001c0001019411288112030460340c090601c0d82d1140794215210b2000141d85401130805101c810350003126800c1850800c00b00307210322554060000c5c90309042540e52308200080020103400700070301c0300000e0285501c804868810304020b0010840f41c104604100c4000141c0301d1000602002c1841c1c03034a241445c04c003101c8111420500c0250601c8203500401020358800504001201d04c100c0c0143e410381c0e009000c034010b0000f000c02c040c10b008180041c0c0490a070b00150001140c01c15258040c0b1640341640da1400a100150340c81e98009044110005468507910f01445c0b01c1d100b039440441c1d03000c8282106a082098920180a03603030b01c1e42109110800c0558010108154804840d08002d031801285654400890340a500203201c008200c0c460500c0260340030443e1401c0218102c00380700c00300d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 641455656 1250 641454406 641454487
    0xf100b1215190e0603010f0f050f061c08030a0e0102030c070c0b030106091412010f0209042f1b03040303050304030e1210020a050903060103060509060702071d0a02091302 75
    0x807000e409903040c581028401315000b6102580040c400741016107041102005040c40c140240000b518140b02c19074940011800d145002e0320045e43c40711140b04c207801c2d54401c070717905d90410703420040544000d50b031340f0041c074000c054080c0005c5100c5c1a140b0031030355075841d99140141107445d007500203580e8000180010700001e90811031100035907040e2024042c602d0742510015024070900c4800245650030400416001e000c10740142c0040070b8200d80507c9010001d44080100510641140102401d4280480900d0309a2401000f406545182e020940740c05105e2507869603019910880003d01300004120a041e40015440c00280084403540c141501d045410f56951180f1121000302c1c07640003411003043c60080003162500040941030300c48a60b075030309040300140011101c0c00d04500034500040e03031592010907d003083d0703801c41c404090b1000e080b1440d140d81c0c0c2c2e4004e0092003519401c110301c400700d03036a1081c00b5103510491040580d0ba03403007800301c02400ca412102d0000c1012800c0c240c00500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 641456906 1250 641455656 641455699
    0xc11070602030f1605030c011104050307090b060703050c0f24130f02060901120609060e0c03130f0341040506030604090614041a15090f100b1215 64
    0x440060781e103004041c442d500317110303080d4410301c0c0d580d00e0558a81542c0f0101c2201080213030007220000c0701950072441c3e40c1d00780d50f001d480c145143c8540c0207104002c5000000d0140c8003400500d1042c0e0b04413001c10b80b0003072810389412608080d0100c4106442420800079000042c01e0354894509191044e180c0029990b404c0d44484001000f03125580100e215a9aa44221440382560346040c4e002e0001558549604005003028011404a151800000358504580c1000c5900034000c1c03079419070a40c0d003540c980440d400080380b011020400701c00c000e9601202217440041c0c040d500710145840841c440e44104a2010364403500d404402014031040000b41e490200b0740394890800e07107004c0703600c10540c40c00314020a0440c2018000c840d0010501091107185410800b074580d01500390325454480c2084000c62840b400900343d40981c014000407072040d0400c9165400210200a01c11542d0300c5601029981e004080c0030003210480f1810410000b081104003860110305980c3d003111044901c490181 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 641458156 1250 641456906 641456917
    0x90a120306180e190c0302030c030c0d110604030b07030212090f0a030e0d0606030818090c0715090b07021617070510170a0f0516020c0d03120c11070602030f 69
    0x10343c3c4981a422a4805118600d4540312683e184005210640740c0180300241902083c0e00034814904546e0140c140004c0d0805031003c010300b104100d0285a030303003000c040c600b841ca090300100d0a0200200044000c008140210501d0301e0244e110b104014580c01039050003400480740381c2c07045100700044480070846858007509841d022500e0994640810b04000c2944401004289803070000401e214070f0350003034001d003a0b03119100030220845100b0068080d5050b14104440c00d020812500001c408241040d6001c0c01f030380d80410900100d440301c004c1250f04071640d00158028650600c0c980c42d14841c841c02130115902e6052421568420041d5140d0413401031074020b1800c0c107001068a40284281c43d040c4000c501c0d4107045241c01154107015140c5501441000c070304050105156007040b0000401915081e4014a9441e0b5800201f100d07188030b60000794140308412003013a030a80da05001e402a002c0c40c9444000c02c2c81e40320070001340b820b4403540c0300d0320464005102881c03a082c0313160211078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 641459406 1250 641458156 641458199
    0x90406170115180b190905070206070f02120913061401030b0405101514030108070509090a020315060d0b0a0506011701060c080901140d09030e01020708191109090a120306 75
    0x100e4035a13030400304440d003a0125a500b5000c0003100d000131612a5034005a101704c1305035090700c4081d00d8404090342d01544112015000d078001d00340c1c0202d00300d48040603107410040104030780307a2840310725199001c40d001d5420007080c5d003006c080da10300300f5600740c01071105100058500300064644100020f1000740704e40500184203400149500c0c01c0d80c441da0201303c1048011030303440e0762941e560008503070740c2d2000d00c43d0b83e010380f2002c1c0003d4810b14002ca00c0d10155900034014264010030070103204590003004204643c400b10040c1121b010800d904409231149074448400038580c10140009020300741d242e03c9499400347ea40c0014400e1542c84418581da240d48000c1c0c1c2d0751500310820050794070b8211800f02c010505004908134043c40d0158010804250003030721821040e1404d4801207882e010700e40100340050b4401c9810032000c00f1221b82d814286800f855200325000c4e004c60018100c3c0405540e01001603208104030010300c1f6154942c03000c01d0503070381002c01c90280340074444d0407142030000180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 641460656 1250 641459406 641459411
    0x71404020f2101090b060301030302062e0608150f0d0b1b0304050105040210020f42070e0603010e060d050a06050c0a08010f0b030402120309040617011518 68
    0xa0303203021000815100001d50700d250300022402801e000c1062601c00348034041318281441c11000072410003004603810389070075501a186d0b82d40c2d0304605a146001d100d00100f03040d4141d8082485169180300c2c000043d18159a0300d01407801c01c0d401801d125900f1080451080301c9016904600350f03a000074131421741d40d01640400340c958642d50195814000e240790031643c41e0000040004010040d40500d01c034a10841c0c82c070200d400b40c903104030b94807201a0b803403503a2507100102e003000c2c8005803e0b200d26078650841d14101c0d600c07a070000000e064542c000001d5605444102480001608140d506152603001e0311042d08561409442d80b001e510090503040c040c126002c960f1007446810300100c40801d4108800740030f1804c05030f01c40c1340c255100c0f0303c000c4001f90040d4000701d1002c0c400b12070b04c01160a034410460864680b50200030001102c02ca4520461004001c04181e0b80c0b5640503000050002c40c40840c0107042c091400c43c2903840c6100e2507071450800c03101c1400600c0120400c46c040c0a42003800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 641461906 1250 641460656 641460667
    0x9010b070308041505040f051e0d030e1213050a090207260c0d020705011704020306010501052a07050f040506010c26070830040f170c1b010207140402 66
    0x1030050b240c0e03144c3c0c00e181035081c181048248a1440600a00140f0580480b9511054008000003580079200c143c1803a4000d0b811580e401c40c8a0b4010f035107070791820020b44040c0e60240a00079565840700248030b02c2c1070741002041000f031900c0700c0003070001c06161000390f00c1c1401903036907010075441d91040c0752001d882680318055800652410340c0d406001200450b00310552100002e550ba124921130b05000489400041c5926100e82d94024000ca9001d80100416401e101c01500e60703810070a00140020000410461001000c40044c2d044850741c0010703025181c24282800385090582030044d0241e802c3c03000b800350b240d0744401c10000742c0d034000000062110840160400c1c2018030321180400050118220080c008503400a08850b0b0495107010351801c80d45485030030a180040d50000307030b16541c4ec0081d010400149680044c4c620a0b102d401c0000e0005510900c25000003080103101e0b03100d9a59601004064152550184001d00041c00d1003450034950400d2240c803400c1850069401080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 641463156 1250 641461906 641461913
    0x618010b2505030a02010b03100e1b010203121e06040903051c020f0d020d060f0f06030915090f02040c0e0a060c080c01181a01060f081008160e0609010b07030804 71
    0x850141090344071058a0756007413110301c004d02a01c4c40300e012610a000e103c14800c0504868860402400513a0000d03000013100e036240071454642502c1640c1c10741c041000080741c0b228036548d4803072042050810200d645000014441c01c00300d401480e5900803446e0941040201e50864166101c44034880203100d109080302900d28044e000720742280e00302c110082035001c401d0101d81c0160580400c0c150b010402c0e155a01da0301414062648540d04107000782e2502444140d2094200d0b07130155020b82980501840140398800c119a070500e410340d0101a50940d0808603c0c0c41d010349501241246080104c507822100005c4a030a03d40c0300c0c3d0001c2c00883c00c0c3c204e04000c48101507891081092000b00700c940c40d1400030207454002084102c500001d14030b0a01c201940028129060b40c3e142d640d4001c050000200c140c81c1030001404030309511801440010303d81e1401c11041d00150441010a0078945c03400c3c041d4580064094103061041c4404030041c004820a00250f407005d64051510102c0b0391121304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 641464406 1250 641463156 641463217
    0x9100e07020c0d1b0b04080d022103011503060302060d0c021b030c06210718060302040e04080702030109051c090906050904080f130807150201052a0903150618010b 72
    0x20f100d000030031700c0800c000034402008540e041105907a6001d660200e42c502c50381c94100004256a07051140e014001400001d4046c2a03603005030b086410b0000700350303403071f40c0008100740c018041340703510300361182e198039560359051002480d105110076402e100744004500180d00ca5410703c1009004030008240c03402c0710100e5250703908080c00e89030341000c02d80c1000e190003050300030086042e60300c0c010700c950f000508a210b8402c4a044a002102c50ba40c1c907221542c070b14010b503000e50720a90303041d903c806980b40402d41c203100f800e03110203000c10008016000c8440241617000e0690110300c1c41c40c80c20b0f10401c0643c41c0c0511141c0e100e036110304502c1da9120007000316441c0303010303181d00c1010301000c50f5004280b503100020864291507429480307c1c0360341c0c1c50241c100e098940c200c50700701c21754590400c0c2082241624400c55030303e1000c4102c0c41d040850f040e000c6403230079003881c4c02c00c1c5405200d0800d00c04103090001035500b07481180a42000590306095a4880606c240300c0d400e143c69400090341840c034040d55 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 641465656 1250 641464406 641464409
    0xa0501021c1a0112020d0f14010b0c0c011d092a040b0d050606040e1303021b1011031603030501030209060409051209011701030303091a0628030209100e07020c0d1b 72
    0x3c4204000b569903040c11f480c0200380b4401c2c6056001c840030008101031400d82e050300c0c108035060340100003048240004682c203e41240032142850206824100c04c0c4d81d401002c980f051410604038410780e4a00740380c0454100c507400c404c030041002003100384450450542101e094220381c1c11701151030340303584021407028810750b0f1144ca01d22040d0f20911110244092118485034025400c60f0040546450046a040200403000ea0310000070070f10304801a000e0000d40f488110802d043d641018070888080ca140c0150b440d0032400a80c0d0340d0300500440c94480001c540010041d1401c020514080d03403000d64901c0311081c201d500c450701251420041e8400c2c941400c4c003070410300c03c030403055a4a240207805050801012120440c101c04080916005a503820b44526030040c08100701102c0040340c03180c030078803210038219a40d1110f2000300c0940c8035020038a00444284100c200507600d000a43c0300701410143c103030021500a41600a407540d100748041410300d4001c3c25900c940c5564079118101848a03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 641466906 1250 641465656 641465677
    0x9020a0b03040302060a0c080f0103030e150a020717070501080103080f07051b01030513120c05010f090f051011070b0a020903150603070506030f040b09030c0a0501021c1a011202 78
    0x2c000c00c03d80d0214200340141a90341c001d0107807803800c00056816900450f2190041c0c0070700700040011038070502d809070b005500034204401d030ac840a803c040203940500380d01c001503489098100180a526880f0b604030038201c0020700240381c107000c0000c024000621001c0c05844001c80c0700324640000328120380449170700c107044420381c0301d45c1c406100011001e1800d09007c2481c02000a804002c00105200f000754000a074140b0041900f10a40724080c0c0c00005807035641d685d50410b45000c00d13500c11040a517000380980300c04150246003482c901004440201100c2d814200503058060b52442a1120507510081121182e520324001e00d00a0081402590341445101201002d000c40508034070701404c000c0c0c055610550701c59040c00b0744c41c8019a1032180410a100024021039076580c4900d1700714001006491402c58550340c898680105000c043c0d8a5940c00a046690301c0720800001c410066101c02c00c3c4800c244040c0080302c1d2090070a030b1541406011001e207240d403040380d4121211000b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 641468156 1250 641466906 641466929
    0x140c0604030515100b220b0901080402091003020315060415061209030507050d2001060605030a0903110a1a0a09050a0b04080d0609021c02070c03240f020a02011b0f0309020a 76
    0x1b40c2143d003940c00e0380561030001c0b94003c04400815009000d02c2220740c04d010603103440c54181c8699003807000082005200d140d0005840102000694091240344406070100200c0c0f20941424001c104c21514080e01c122101d500c0002e00300b00f03a94020b68540281c40d000b806c0000c84c4070050078203a54a2180b180000c000740540207041c0c4685400c03030022094544148456030f01211146201400c8600301c1c05120f010503018400100c00300364a03008200824801c0c5800c4515880e02071400b8581201d0710421a0485124060540400c0c0440356140d03000454030001d2004102d2910342680700c001840c8007a0554112000240a01c980c1c001100c4c12200206001c020aa950f00b240384001e401201d08001124070b0304246d41d58400c3e850080d6041d07107400c00d4014402a2079030782c6918010300d136100f0394907001580e0310204003408154032803401418041d400c0580da03503030301440c0282102c20f103480c002401e0032015089842c803136114400712011100d80c01e00007806456800012980041944031038007408 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 641469406 1250 641468156 641468167
    0x9140601020a080c2d071430010c2715030507090e09010e0f03040e130f0209150306090a05031903150305010c02061003110402090f030a140c0604030515100b 69
    0xb00305c0305401c02d0845101040d10051500c5084022185a0042c0280d5100003040400081c001100c4440d40d8058540310060b44542c803a030308206e003500d203040c403074802082c034120307010148c040d80207c5851840007032003a400301d840c2071400024010108011850400d44c0e07c90004001900031040c4c100a02030000340b40d440ad141c910002c5000c0c0c10100342d816654042c08002c10038108000058505039040f60000130311603074442e100814900a0060f0a0318489203c1d0014800b50b125450101e0141c7d500c010804810180b04061600e040d01c0070b4090f03903c5601840e410320100740084261249400f044008a05c6e128061500318054107003542c0b40910a00e0b0305200004000b415840413050562640a07a080c0e43d07586400400c0305d107041d100c09090960020007012292400754010480e003007009001c1030a0414113000300b494800415011075034080101c810035920b810801c50f0080c807200c100c88080c60b02e82103a882c692200b810350981d030f0300810a907021a0406140c01829006800c80102140e100c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 641470656 1250 641469406 641469463
    0x702090c044410090c170a0b27120d0c05031009020a0923031e0703020d0c030f081206010915080c0f0a020709140601020a080c 56
    0xda02920070a281030102d10007403441c8034060070400020035000345060449100c0201c0104507080d04103030715030290050107403082c06003529100316400c45004032170414042d81045c1000c3c854041a40003103005601940c00300300059042e045240d400016014030f542502d4050400003d011060a030b185628080c54510f20711002b4080c3c040c0885a402900078003021005032030640d040d1005030b818440c1200901414403c0907140d40081c156030b8064505600583d07968034020031034014054240f0708400656500c4400d5180c10089803903489160728a0140c0410808800c0c2e40d40c0304180300c028050010a80c0341c00900a800170034030001c507002600c0e10b8118560303243c03044040d07100340c4080340c0b40f1f0205008602d4030351140c0d84d8241071710070704031010754011304602e402d66a50000820741105060100f00717005003401c02c40090603e00705542c000303100c0142442c40c1082950101400001c0202c0d40c0e0302040110b07a0700289a0801c80d0300036803050358890440f21306908011110f01c522400c46a03540001021 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 641471906 1250 641470656 641470681
    0x110a030203061f12021e04140111060c0711030a0515090607020d1d0a0801020f0702011d180403020a0501091a0a1a01050c0309090103080909160903080a05070209 71
    0x1402c003290b0038940b191010114140d0b08595002c2100025440d601d400540a46507006042c0030030002504401c2d190700f50100e01c5268825040b0240040c00140c507211196000800c4260480381d510181c40140b4201c124110917005003807001d0854803400210b440c3c1d80d01d060041c41070498004050352110244106400d0042606940c00301c5188a04d40003c0ca0041c80400d00a02c88101c658603208110961003c00c00a1540b000b841644800030900000302840248000c4c44080007104403d500d0309510300001d003c01580101d044860f1000381f121403420b0360b13001c494008201d00c0201001c0c00c2d0306c840c00e0403403400000c2c49005101c2c3d881c100011042c0080520030141d52b0314401c0800a09903102c0217010155420f44007a90a5003c08600d50140ba6010350b020f001595002c9040b6401d00d030f00a00001c1400000782e0055a02060029040005080420344950b2254203440300c0c681000da0800001c00507440e91002030200714011400c50708480c41581283d12140d00140350000b00d040c0076105902 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 641473156 1250 641471906 641471911
    0x6090203010b0702030714100807032c0f0616050f07080c0a060b0618010807050c060f071e05040501052b0509160503060103141e160f050303180301110a030203 70
    0x8a1b00c59101c1c0041c030304070b0941c07442d180b0358806403515049400c40c403015102d884000d04100203058035401191850118158410741040c40014088140e010b4002130360304000100c070021902c1d40004081101030410f500c0c940309240c000e8940070b0343e101402110440750303010b5004001e09403200003404803e10b902c0000c80d83d00483c010b4030100305ca40c440404008541c070601c000d00f002001e551180c840e141d0302405105034011010b003411403400e0070b1340b40440c5c00d01008940c054039010f5070500b40181240d01c9a440d2140841500701108041c90401025125001f0351180604000001512003401e48290340710320b0603401c884512949004000080001a00e41141c40300303003130b1260360350300403c1c8022240e500c0c044039000360240400d42d09503110860700c1c150303031141c5260071310442820b240f03100c944201c4a00718400940141201c07640720b110705151541a5170000c0e02210035a01d05001591b004812903000c0c6110000710703481d0b0031001002c640902a207001d00b032441c1002152290341990540c00851 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 641474406 1250 641473156 641473159
    0xb04080d08010f14041a1c0501050c04051e03010209040c0203071208100e1e0720010c3608070509011a12070306031704051023070606090203010b0702 66
    0x1d0540c1e207440e100c103a038141600c2440c160b041103296820450525512003100400f2001000b100c2c0f41d805030100d44041086a08035a01000450010052240a2003080d4000943c40802483c242c40c10740040c980450042c0c0c8022041880808540113540035411288034402c090405d0010085441c4040d40300e8000709419100300b003030542400d00852050b221b0324810f84100d85019103890921450400064005140d030b140c103003820305898003a2140b42d400c0c500c1000c090b580ca03540c2c540030500c2c0710b0819825240302c0c88940c1c1441640711140e0b40000d15086000c014a100001c480c00402e075000c9074030700400b400f0800c014002c401256188000c1050300c03c0e2402616090001d0341c3e1030b900c115a44e00344160716100340400703100b200c400340c204020300390304140c0342d180121304540c49850328200c82c8100300010409200c0040d04001900b400144400756801380e05040800b82805440340d840c02080744101172001c480000c0f440d080000a51040028000190b411512582c484070500f01d140d210b814180d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 641475656 1250 641474406 641474417
    0x219030b1e0f01060212090406030606080106150302070f060c050d0c050a0f1425050706030b01110303100b0f0d14010f1725170a02130c080c0c03040b04080d 69
    0x1d00000d002d400050490300c1e40e500402c03100b02e40d0701c081340307454101450079940241c440a00102044403402001c020706245000003610604e0450740c00f580c910702c08000010b041c01070103000c0c0810403003920460b80c0c2d0782020000c1070f003c0d110324040303446100f40b503080f8040b02d01c1c255034105220381c400c0c090517220100e0780b940c6030078036032120b0161001208040c24010500042000a01800d0f0305410000c01c2c400406016400441c039a070b5003810203850360059800a030f0f59584080a543e40100c013502c1d041a6a0b0142d443c50511201801d40c100450090040750300c0c0006d02840100c3d03130507044440c000b2403401d0810041c8900c44c1c3d0402d850000f0303c50032404105e4400c1c045010084000100c44c0803402c7c000070302c0410344540060420f6030400c0d1100c0c0c40c0010304c0c20300050011141180c00003c0c071812010340b030300044620401202d00224201070038080c1c0b9203040d11100940004507903400070060610b89494020070366000e880e44c070031078200d0544c003900482c000410b064006040b80d02c0102c80d80701c0b07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 641476906 1250 641475656 641475661
    0x60203040b090c030723031c1e08130204110c030a030b030f070e0f060411070f031e0e011805040e03040303020f0303191509020a230901020a0219030b1e 67
    0x1007545e00c58182c02003419941d00c82c0c0e00244640007007100341c4840c3d9405019250001000c0b411440345107100340c0140081815070042040c985850315201001001e98140078407203003010f02c40800455442030000340581e941c4e4800c407241c2000700040e500c90741a52002c60b0756074a5800b80c020301806000c22154064800c03807001c8000100040307210401e0310340e0901c07604c0b481d54611f0666038100a0203400a40c1041c2d039200d84c81c0e0445031102c010001349010354404107174a5028030b0014040c055a051f6485a40001e12145007540e40c02018409110003d00c2e110440901d0429186440f5440d6480640e0091800c216100000340100180040728041c0d02620750079280c0481880d180d01c012a202c1038500c0c44040c46801c0e4070000c0c1d0000c002025045540306520340c0710f420200480e84201d08100100d080101c0708500c007400c0d21045149001d0014490b410055980001317540e980407404000c3c841d420845651314509040c1d2800401175400c105070910342e04101e040b101c511040f020b1707486c0c2c03601ca01500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 641478156 1250 641476906 641476909
    0x152f03070308010b18010f05040906030605180a0c06050702130c0309051203130b1e0a051503030903060a051305030315010801090b2206170c2d0405070c060203040b090c 74
    0x1c0c0c81e9401008105c0d03807002d4104000440380f1204410690051100074080481c0a9800f1300c01c0602a40c8100d90000d02c07400c3c01d0240740709a1040c18074222aa41c4a1001c4a002542c820580001c94285013851074841e400c80c4002189980c0781481c3c05a082e24203038031160490360540107404142e0286042c1d031145d506072241500b1503c02110803044454003208560b000405114005600c0540e2665801d08051080000880742905442409566441c0c0060218205d04a007510f408100114000c501d031030344000200b502d5040c018401a803480c4d941c00010038420309140b0801c80c140d40302c0c040d80c1d9240f50007070003100d400460005860018800d00b0001c6001000d5110b4507014600c000e0030140001c81e005085c0400020020540e00d256468080000705225803007010309120444c8005020b10b03540c4a41403001c844111061401605001d803e1880000012035001007a5901540c010a195452600641d424100300c20024140c074030000400c01480790500003540119011016111b80004400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 641479406 1250 641478156 641478179
    0x181e09010f14090c0f030a05040507050a1a070201091509140f090a1e0e060a0e0d050406050a0e0a090f060603020309030906030a090206280207152f0307030801 70
    0x42548040c9980c0e112450b91030040903456120342d486011900d000c00341c3c009100340760070a440d0800d8a60f00c450510082000601562020300004d0304c02702c111500d4255101800c580f05000a1107841d00040c6440540e441103d1040c06000d81c4122040d008802050041c040103141c03140d4443c4a20380703202d0044a1034018802100aa001000523690352646103c4d038000317207407540403500040c00d1039800c00100c100c0341c002c00080350210005401c0c02d00d0320080d6402603c130100708004160b003200700f1364031102e900a03054070113548031031500300c3e2910301c0703008151140c0c028040116801030030b0310310004010070107800610b90100b442c0820300400e65070301810b5050b40816100304140390424060b01d906400e001000c1c40d401071400c0400b1401c103549802060b2168840d040003854604150300e180c000c42c21000c9100b0740c1061503c000c181d05072a1031040520060910011420454405201981d81c2010031150b0340507482c1050007204004400201507a95004500440c0821480000020103c20a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 641480656 1250 641479406 641479409
    0x120b100603150306020901110d0306080c030303011520010203010f0602010b091b0705100603050a0c0f06080414010b101e08041505130b040f0204050c0705070b181e09010f 75
    0x50110b404160304507542c2c9000313074000c041305a0410024803003520900008011050b425030003a100007841505001a5070704207260402d047e8001e40c010001001821001c1004408481701460030032120b07918043c0b124174162200b0707218605e660000c00080752540d441002001107401c1c03a0020400045e8107414016004000c66040070203c0040c0c900400c0740c1100300081482e80c0c03058094600052461462804840c940d800a03903080d4402440c503410400d8017a00003024020030016180c1e01480d01c80d00a1050100802c001c1110042c0000d06203045000d42040701c0c40b0b00000c10032505441451002050031b407280300040b000101150760781001078042e4410398003030394001c0c0410a281400d007e80e60003402c0c0207801c8942181490013003c010801e85600540500e200d980c9111355041e65004000581d0340140403a6800d0030204210b00008030000380050071908440855602c42c0d0b040c4481c407201d1030100200a4220310b104410314040d0704081202440000216007894059884405050100b0040d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 641481906 1250 641480656 641480681
    0x108160e0415180b010b04060e060c0a060c0c020d051c0e03030f0a0e0303041e0501030e06040201030b0a1508090f0a080d050a18111810031704120b100603 68
    0x340c1c11290250b1400350807502c801c2c00b400001d615040c1c16903980a000f070109a00c0702d00703070817070105007400386a0f03020415520000f000c0700d000f410036448224136a1143e03a1080014155070365910b0009103580100e40394102c507500105500310007501400c00584039281180c001021449000141c081107015074a0005074180240040d4180403c0b90a40c14042c1d1103811807100f4000c980185060554007000108060700c4141000c24142c2070407024840f103010740b5000141130604000701e448980300c0c0010159800342d02440c004c101e142c600c00c00318407450f00a40244408440c1c235036490014070740215940703003c2e1208100711006200c80c0802d8a80314211400c004002c0241080100281280f50304019004081c8d40c400160402180a0030702010900d004100c03440307100d080ea409490302c0d201044602d000c40311000b48105260045c0820841d01c030a00005107280c40c0d0180948000e1411404d032000340014088800391480da504001c03100801c2100d41a0300d80d4074144002c181d10344a401684400c814 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 641483156 1250 641481906 641481923
    0x90a020c1006152609100b15030402010513081009150c02060f041a10090c08010e011205010b060c070f12020114160c0905100605031003060903050c03030108160e04 72
    0xc080d000321070309604c10100c0280e01c84c2c12900714548407815100d850042d100300300100921100710005005071000426124401c00c00340161824200101040f03d03070056091800c148c1d10031400302c850004018603000010340b80b0804410100302540355026540c00da01600002440b85407210140050310354003100c03140180c01a0b408940a145c5004010780c11a01ca8281006040e003040303404002101d04645094800c034000900700690f200c0c911844440c0752151400c4400e540c14132102d140c4107081841507034081546600c614040c04401c0d8480700d5681c0e001094140d49070400315010fa504c1540d8040d1180c90441319200103482890324510307031001581a141d0298088000c1d65040d940d420088072010004540f07034603100080c0c0e40f540703103502401c20341e9000600ca00b003290381003441c2903680c6c01c81c000b441420824001904c82c1c45000c80d00f1680e000401191107412443c0496283c000c1c521036800d10321002c80040740a040c04200d40c070000042c0700d522200560b48441e00f2030500c2090b64041c1c0b0265 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 641484406 1250 641483156 641483189
    0xb03120412050f0d0801061e0c1104020f04091d030a120b150c15012702070f08030f06010212070305090d0516080f16060f0309020d02090a020c1006 65
    0x1d9180911120050081080e01d64078050304002030b060420030300c8030400148502005201040d0041e0000141c055031400c0c294400c1241c80c0080d20858480e1009407201c0704c220b10118103030b03451345c04541900301d80071003140d240e030341c1d0303071844405400360888040000c060a0314501c0d2100c030000907a84942419500c41c0100d040b0005940000e00c44a40e003190402010144000b0240307030b84004010f03080c4a4030007003200846d4404141d1000030184c0041009140c40e0f407201c80050100100c0803c0703d07000160040c0d0320403d41c1340200c4610348040d0020410341cac01100304200c2041d07240c2814802c01080e020b4030850098842c180d003032440782d000d004000c988140b042d080181480449180042d206000301c4a0315246032045801c0301e50b82d0303441807480b42c2c40703000c0c82c0d00180c80901103132103040540c200348000c00b4100300b8003800d02c00482c1480810107a40d5002c190942d81c5000c921000175402500a0910741000480200a548032500c148140c2c4107040d031640303240c10700744560b9003100c078081d840c4030025 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 641485656 1250 641484406 641484419
    0xc1b03030c06042a0e161125080a0507090609050402180709030501110d0b0a03050a14070306140411090919060f18020310150605090d0b01030c090b031204 68
    0x100f190030b101040e8041c030b13043c1d0b0100c0c400b82425a4003034603000040383d41510f45410f4009201d00c8141d141820032907500307070101668600048442041080155980c544840006d6001100000754400302440c400c546040003440000b0480c90140d880030707002800069198100031090b20001c1e10020341000c0e4108400c030382c81002030200d5820421a1a060ba1441ea590321224203440301500c00d0450a1000117041c0301c0a140361040c040000e5003a00c800c0310321171550b1a10f545841b403019000e40b0141c0300241800c207500d82800248080e6a100070300300014078200038054042101211f0444280281c0d0140c147c01d8549940c034103104101150007008a0604209104c0081c16100303001c03200c050f12440c0075108031f5079501800300240b040700c01c01c4030004441e004040c5442070320a01003155a18103424280e00454203070b11002a2401810600d0352680c48201040710100c64202c043e12400c07400340003000b001003c400140c22518140401d00510314000100358490442200600c452001000b041145 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 641486906 1250 641485656 641485673
    0x11803020f061312050c060f0603010e06040b0a05040c0b0c01090b0901091119030804120201080601110c0f01050c10140615070209040c17030309190b060909010e01020c1b03030c0604 80
    0x202e421382c80c14a0501c00075060b1240b50070b9050300c1c3c1c00218403c590400c40380341800d20030301120500c0003004040a0425071650317842d42c50701504113604191034a00240074444e20b14078a0004203080302c4116601c2440001850007132030741e40800c5a0841d442c0d00030420340070050040b45120f0360000c0d2020951040c640800c2409481031001081820b0503d0000001c1211340e0b0281000b04800036402d140040e080c400140b190318010009814003101c1c00f01c1c901034980000310250310400c1036331400500030795030005031540c1c014600b105a541c81a4115070040001e50b4024512401d1440714031800c035140c0e4000c00104110320500d060bc511001d110810152030888000c03904036001c0d200003150140c0340d007901c0c81c3c2100840320381ca800398000010b10036540010400100b0b108201246c410b03100100c0d99815105141c080c00c03140c8a100f66001068040c07a00b03601c80e200e02c14002008564887e2000c1a46803940804001e03814501d80c480900c88141c140402117485124110f0080c0010350384540d5503500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 641488156 1250 641486906 641486933
    0xf1006091d04060e070803090f01090b12070c0f030216050f0310020904020f04030c030507060c150e010b06210f0709120314130509100308030a1d011803020f0613 71
    0x3d4064640484e000c41490a10944000d0410f00d4050740d500e201c10400e2103980d90107001054100318020340100709054601080e46d108085001075003c440d00c13228000c0b030704c0800002002d4a500884041c3d403041580020b4001208a0300800001901d56030300d0810080700f4903c400380790990403600c80041a07040660052090743c030000c200505060a078521412103401a802c21202c000c1844014402e0010030006100101003600d4004880c0525588540307094000d8001052942e0b1198880b1311440e900707400c45103e60741c018006a46443c65040c10006076100030000803c030107400008280211004030040744181001d444507200a0f1801032840c840300d052560513010414201c01c080d52682c0e03040d005204d0304429010300310030381d402c1104001e4644d40140138a0301d020450301c001c000040003001620340c0184407071000202c0034101e810002c800c21003924003100c254071b4600104000f099000f00c01c004035020380d013140c14080070b65200540d500404d80e000030001210740006000110351004080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 641489406 1250 641488156 641488163
    0x2503030f1a4e0303070c15020f160602120901051e041208070903210305160e010806060d0e1005060a0303140f04080d1124060d020a030206030f1006091d04 68
    0x2402c0160a241450868006440340c0c00000c042001020030b119031419042a4100440000c51514011f1030b0b50303034201e2051400c01c0f40018040100c2d01c0c140501c81d81500c004100d90040c0246624000301105d00a01003255a082c0194034000302c082d0055851860700e10490340400c101e9000291a03a05a441c00b0004060b00100b018081c4003100080500f1a1755104492500d40711070146114400a8240e840040003049444198011320781a503500c040c0c0d40d443c101c1c003030a11041e152030f0040030032514440e00c1c80310400a4108070560102c4c140002d00c0d500380100c02c032000c001e1038445004110582c0740c10f11028000494031030a00700000a0718004102d4040c010325220301e4507a480c41d686080c0082c4901f604007045641c20310040d810001e000c004040100d00d1220098002400314291a200c00500380f00e010302044901d110454440601100c0a550028413043c0c40c0d15156000d031403c80b40c00c40d10741c00141d0724034100091440c041c4d03400740244e914400d4100c0b841c0c103081d040e250003110010401d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 641490656 1250 641489406 641489539
    0x7053c061617091e0a0b0a03060305280b09070807030c0515040e0106080a0b1206090c0301110d05090a05010603050d1b0b01050d151107172503030f1a 66
    0x60103c007000d00500e10340d02e41e0745001c09d015140d0b0607d00c0c100407a41d04280103003c100c0710550480b00104c0141c034000c3c1e0740003608401c25120b1004042c07801810380c10a0f642886a50004800e2248801000c003c90b00c0854244001f002400d1911510780641d102d0044074008400051081a0003000300980c0324551020010b10004200000344c41c0c41032094520781c00b60400d6050090002c814400c840307620b03000350000d0142a50b80c0d0b141941520030342102c000055034034400b19201300814031110301e040d07401900034800c2603260b003019501c44901441080224450700300c5644600c25404181c14210341081e40301515a1804081c400c4a10a086003181c8502e001c00d440b1010f81100d00c118200c11403440105511b031101803500c3e5955410000810403204c000744008030003007002c0744070030010710141a51625500d00501e416000b5040d161400942c0e5420310f0840c1c81c91072400414407150f01c0007180c0c446d07150248070382c4520303c20b4001c52491040320108000d11246142d1401020245951015070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 641491906 1250 641490656 641490659
    0x30c140102371406060d120c021f111c0207090504060219110f0f0a080a170a0b01031a0d0303110d140907053c061617091e0a 55
    0x14818209074540c00c5814101c50000140c0c001c8080168603800f505c10394120b0003d444507242d5892180005044400300000c200040381152988202400d0000405207284400400c2a0015002c82c0702000d4903111889000500320a02002000c410f04c50302e102d801900d5001c0c01d1a254001805004006481d080d408000c1515840307012608009049100d5540b982c600c618001c2c81404c11541455255881d400306481460104010600c0b6440660114800b551200c0455041d500d094042c89800000c65000c0104040c0703c0c4c45410048000200760fa0801a40400968030b2000310201030030310750007000c0e10600c00002070080c2d200c49400390540c0400350511030000b034118151041c4003169000b03c0d070488140a460038040084102034002211700c070034034080c800010320b07810010080b0440c24413040075204804014101c07012a10044c0503001c036985805400040805001d02c11040342c070350102c107240780031689030b19040e0b42c0c14030f81c02010901d40503165071b881985010300050095000515180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 641493156 1250 641491906 641491993
    0xa150f03060803130503010f0603170703030b0616050c0a06021c050c010f0605150705030f031e04030c1a0105060a03021305031609051311010f0903150204030c140102 73
    0x103442c07411300c00c12114902c9400c1406150035245c010410b00001d07070608206000186820400c101e4550104085035203908041c103007140a00382071400c3da038203e1070014030b50031a034907500c010b271420601800c1112182d641e01800d01c00c941d0707414402c210040c4c1007500d001031030580583c49a444c0c45840e2500360700b40a0301948407802c644444e0727010341c25160b407848100401e003000d0f910102c22040c0c1e441e016090440980303510b0b4607441010b0b02c004014800000140151562030f80800780703041050407506e4280360a107405085601c0c54070b0b06407000340780041900c22144140004905803440503110900f02980c6c0b42080d40a90081580754915408541c0c02280d507440c1000f88a076010051818040010701c1c0c00783c60b00c02c594002c2c08200702d81401c10428400b00f0240c50300b4560260303080c6085102032032011001c803850881343d0001480c0802c18a415100800b0340d401420603280a103150010359030b40c1e6143e00b2080485418a1809070308070044848030034800300c1d00750000da12030000141e290400040d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 641494406 1250 641493156 641493163
    0x10e0d1104050a060501090b12070513030c030305030403020115240903061104150306030206070305090f0a06020c0f0d050a0209181002070b0603010504032007050603040507080c0a150f030608 84
    0x1150240d503ea42c0b440308001540e80108006e00610b0b04918503441d100d2140c10118414900805800038010000b503010448000e4012003002180c000284c035090035200d00d0001c1039580306460990056080c4880003280d0100b9840c0641101d070b141e00451540d03940c18a06100b441c5408418109004800c10000042201401041c42c8040e02c25641c996490800840201c844c280103440000c152400c1c0c414801a00d0303d00840d000316400d4142640c40e0b11550303000a00c2e4008011480d13030081082e40300004d9854002804950f65182110051010201402801140c625060018005500000301000542401d0003001d8128501d10450a2140a02282903180505542c06c0381080e0303500250350390a014080c190f01d41c000d01d044003f070010b03080c5034600424418400d0310491540c0d15240d4031408100f01000621700524025201c95201d14090500e192078013120300c6070742c031903004001000e282480c0036801c000a80d40760384407114080b00004001c55420400240034414165120400303d030585080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 641495656 1250 641494406 641494411
    0x18180207050f0a0c15050904050a020403080c0106170f0a14010204120c0501030501061e1808071805060d050a0f0204061a180306060a060c06021b0d0305090c010e0d110405 75
    0x6400500280703aa61600300050480b035445400041c000c05c41c5402c43c01c0d03000c0105c80003000201c030b0202e041e4941c201442d00911440e070004050541c0080e0a005068041d0000380c01c03198414000540640002c140984400092a40b041141c111548405c005006450000c8521030740400040c20036807940110700c004071902c5802d9608004480e07040180d5a454050940501818600503003541c4078041112441d05040707070810140407640400c5040707000c40036030160042540404460304d00c0d0341c0701da550b103141503c4c9848480040c00c22001801c0760502c41501350805d58002c000f02021400c81c5c1760070705104107801040341d01948400c00028014082402c1d242100c54034882c07250f89900c007512100e103070f05002c107060b030003504004100b003d41c2d44c0300ca4403d812141c2500b007917034014034a072038824001d1041ba01c541c114159401007a008054001801e041d90140c1510104803c0c0c6402da20141d40d800c2c0c0506603030004203850081d0307000f810003800542549101d024801c3c0e03036100c40e50010301944c608 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 641496906 1250 641495656 641495683
    0xd0c080d05101e0e01060f021005070504170109051509070b120a0c0206040201050d0c0905060a05270a180b10050c070b030c18121203040b01061818020705 68
    0x244041c070952190842c1c00310b00f414810003c0000c0d601d0203600419481051041070140300760200d03c82c0b1080d0090018100500040c5810020381c80c0042d00030f003071900240180d140c90b4010b08040003403407805204081e14a50054010081702102c1b0501400f5603000420324009800340c004009081d042e02005000300300d03250802e401e0304c4e1500204140488680a1144045601c007200b8003001d80d030454100c880c8421038178008201c00403c00e606440b4203043e035000c150840320005080d0000365010b4090022041c900107109a9154611203240c0c04081408109510142102040200404400b0345110601c1c0914000c50303810508800120808820400c2c9030102d04000786c10702000e002403000340d01900c421060700341142011801c440b040d0142e0340100544908042c0d2640007951105a03015681c088181120b004002c2e020001440f40c00c10b82c0c080b0340250000001162382070103000c550038203485180485403182e2410100070050308030000c00000b201d500308500303400b00300c1c00d01c80305050240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 641498156 1250 641496906 641496931
    0x130f0507080c0307080a05310311122b0f06030204050a14041e050a03050d1521082a0f0f030a030510090f0b19080d0c080d05 55
    0x140218060009880248202c8220070204104a415604071080a41003107502a000699540d40d058000c03000211800074803142c2c460040c14981f5084020801035600d00c03a540d00f42c0070807040c08a15942d014141180700c4520030501c48400c40344210703807452005210141205900c412002801400c03203140e074a03908883c40c2c035200c0c10b00a506060165913048890403800300709150203420b140c0d025401c0548001c0c400003125a140c441440300c0240c19260030381020a40720340301c8051401415542c46000618152410031020b480d00c21070141c071300f8080300c4002d514a01c1c204600080400d0900c50054222043c10051241100d2264490a4445604441102c001800384014055890000c29404103d20b50340b0822030754400342c0d00030007950807112a80c01c01080c10307101c48600351140741c101d412981540703160860381459029503800c8081500310a0341c0e9003160000403e1140d2030400c0c940174200e06070f030250940e52051480303100c1c0c108580b4083c0000380e00700303560202848241c0d40140c6414074030350b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 641499406 1250 641498156 641498161
    0x3201608011d0303010f03020d0503090a0b070c060c02011205040c08100f0b03010621030905040207150e060f010b0a18060e2119080c1e071205031206130f05 69
    0x19120300c482d04501d241940150705561610403640c0c0c009045010083c0a03400001e0020108001041541d010240040c00101403540714400455560000d01003500c0000f0042d000085903805000c20000940c0c06075208001615220b00800c007504000d8012a40356281240000d0312041c00d00406000364207510010400503660100703113050b10004d51005d03100c0c2e4075021080261000c80c0045a50029514130044038100c2142829a00e02450b584402d400c94000248082040352440c004440045460300401046100d400030ba640d48408640b13185804c0c2440005005544a11004d0150300e00b55240c880c00940381c00d404184001c126620580108404113010400e51030f01d4040030020140480c1ca1012034881c544807180d54812049860819510030321a00c42406522400c403141b403502c0070116076500c8029001c01655a8a0340b80b40595070140380800300c0c0d14064a58180a0a81c1010041d818900d09080841c80341d17202034113540c0d1051904283c030440c441c00b070040ca104001607100001c3e451 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 641500656 1250 641499406 641499431
    0x1e070812070527032104090e0a05010f090b070e1003051b070b01061709070608070903020619020d0201020a080402270f100506070b0712060f08060a11070320160801 72
    0x8100d500300c02c0c0a01c5c1245100210200101d810b44040700d11000022510b403a0421032641051460300c006055542042e0141010660315004100c0c2c5521038000c00115640d1841c080b20400040340505500c1820035a103609032520942015800050044522414454078042c0d040e641d80107020448201c000080104041070b000000c207180d6910100000344903280a003034582d02c40740345004000c00e000746400454401480358a214019640c090061644c0c2d122141041082c404540d04540040c401c030a10141490300c1802901c0100d20b99444d00351864550764200301160300c1c02d46864aa0400100e02100544030160b5041d0086140002a07440341c2055489480c0c04001500314a0003818108407200008007240701caa41e0243c00da1800f40e00304055580901302030101030380000800e070409840881e55000116409001c0c20800c0c0003007018410200c0400306c4d40c0155100540803c440251300419100248a0140711440c0310f0290b4905200181200021075440c1c2c01580b241d03035403810b00744e080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 641501906 1250 641500656 641500663
    0x150c020306060d0c1a13060201020702030c0303160b06040f050c04140a0f03030f032012010f0e13031115071803080a030902060714031e07081207052703 67
    0x40e50569600c83c0d0341d00355407194041914503105c1c00c2d00c146001d00b0304041000403201514510b0003044c00d80c08805a581c50300a000c0d4020180c20b07840380c0101c600f000c1a03880c0000450355115000d02c0310340d03005c5400e41c459489444008125603005038485100003100c03030307882c41180e11031040d20b04501e40301e50410205c43c2d0801e484105c424016810b000c01808226084a451001c072541490044110700da4002c3c01c601518142c085c0a51515030482c84060307003803440b4058900841a98219441d586e60340c1004510b41c11b462003400981044240455100d190f03407d00002158081e080140300028011161490010b1611035146c02507103080030710948690050054039900300c2298480a894250b448a0f001817150000748028580e82d9803c1204640303a01702a114000d030881c08042035050703906a07080c0c4941c072940c14406c7c400100014002c1c84480c00082c2d9140a400051076428649581e00103060740c14050105000d1000c1800040d08401e0b0311000326008101001c6441c0e051800c0a091624 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 641503156 1250 641501906 641501911
    0xd090611220302010c0803090f06190b040b0d02010c0c1802070b010602010506031c260a11070b0109051905090a030f0e090c0304021206010603050403170708061504150c020306 77
    0x70340041284040015030f0b400028500e4550b040180590740f0b454110034030345040c2104444000d14000e4004021400009000c1011440d0040d43c0a2101c80d4183e01007000712200130400302d500680782815000503511954039003030400d10980e40e40c4280750300d4050a05114030200c860124058000655100708204034645900400e0940024406030814200280d02d035610300010b000c1400d07040e401106854840c00c1502d45803080c00c00d6042c02c0c424100c002d1002607400701d5595000d40d003044643d021160005007108d00d2150482c44a10503a420810078801418000d0240e101101d4044500014060b4034407495005001d604000c0035000f200340750162400c00841e04201c240525901d22140b25121001095802168090102d6407076540e0f10028103a1176800045041621650002203a800c2d0140c0c440ad0285002c0e491300d101049602041e080b681000b11069030000348a0301c04038080d400e00d8074840301c1c2e0302d040f0700c2a80c1c2000d440c0d005441e829180700b41d0010004882d030702414190300b410302001d034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 641504406 1250 641503156 641503207
    0x1062102030c10080a200c0f07080601032006070c2c011206021c05092401060e0d021201051501080c030106210e070f06020115060f050d090611 63
    0xf242c082403442d016044c030f44d00400c0004400d440d2412540780740d80c41d264000d2402240078620740c4440441c21070035580c1c000703807803000c05920404402083d00e104c00030720107040b40c1c2d11904000c0c04415041c504006594401036982c0c0040041c0f1511000038241c60111001d001c640600d0b90107200e81c00c9003140003040040811070043c00b500e00501410700d2983c00110115002100542d803074804c03a402403080b040700345107064694030300b205011242d40d002c152054584600304403000079080302e10019054a10a200d0480800e00f00100c0a1040c00c0081a032868540000d0031200ba15840750aa40d0944100301d03100c49540d0b9486c0808080356070010754260308902481891410366060142c05802d21900c2d41000e071000341100700b00000700c019034125144507100c0e642601e41e0b032075840c1620780c0d21350710601a00340554200744042c410a07404c503000404556095030740852803c034005040d03451b984003160300164140c03180a2040420b140d40228081d18216015403a03544c6000b542d441040410400c121 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 641505656 1250 641504406 641504419
    0x30613150b0a170a0804030b060a0e070504050409050c090405030301090e150403033801030b0d1106090a09110301060201060501050307020304031e02033a2001062102030c 75
    0x10748590300c80d05119000e5900c2c40024a006000c010303d034601d03111440000800010340014040100070401e51001d0050506540700f211598440c0c61041c0005004c83e02d03000060f81c1803004211a02d0150000c000090041050329644158213000c1181503c1c02c82d010b07913450b48004010424442d0380d105000104481c1c07130140c09249942001d0081e030341e501074005401c054945801030340518040ca203410b140c0d183c01d0407400300c80013155103031040700c3e10020089000c44c0c60316603903100c0c81c01c045d07520902107640b0600402040301c040c82005001e4118000307c98001400200119206400e4402d03d141016149859030b01d0398501480203081d100682c10650411009000340602183c00200381d5003900e5011082202210482600c5011025640701c040c2d814031030803140c40c603020042031046181c101c0551008003003050401c4000715061503071319a9800a14100c03030300c0e4042c980b134002c00e8908155800000c54034a503104e05440140702d41c060150300b1314450295080071840c04104800410b181039500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 641506906 1250 641505656 641505671
    0x3090807030309090c03061d0105010806120d23040f0e0a0204060f030c0c02151224041a030604050d090e0105060d0209010e03070f05030f0106080d050c010b03061315 73
    0x2e00f000064810384440c1500d40071025000781c001d800190180960414228002d1214803804101090138030400780030480e07050215085003868020b5400c64191480180140312800e60112400d200d010260071048411044d56403a52010500500041103144401c0892030300b02500f06004400c05000405028030401081107120380060300381c131000b106c3d82000951100ca4802c15214130200c1e0100942c44003080c202902d082c5072400c050141d280ca41010280196100789101606070212402100c0b00c0c541240e00c01c03142d00e0160489031042118620702c07640e00811401281c40c2c588256403c950700d401c0440480041d9501c021203c00a20300002482070300e500d04008119103105200902c8001900040c0410450b40542c0c007640862001408442100d90745004120680d6254040c191182c011000d0640d002c9105000d0b41050314441006096030842600099456a1004641d22055529805078044a03601071001e144140100d401c03010303580900b45000345031607030f030000d100c0c0300540341018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 641508156 1250 641506906 641506913
    0x20a02010b0303251703040602190f08010519170f2b0f02150f0910050108070905090a0f21030507020a0209070212041419030305160c0509130309080703 67
    0x219181c61241900130802e00c000609050201400305d941000101d60000144810000254010b03ca40350f8240d0011041036000c2d0401c840d1000c2400c1240c000401d5a401030195192440782991192800e00102460b5a41c504465084212180164003150440c0c400304030404010301c103c02e03107200f440c84e528042440c00001d80884170b80550440042209500f11500b9080c000c2016580400340201080c6580c5002c2c031b4030480c202401c641d40380160165030302c00c8801e40a40d002c3c0d0fa0507554490302411450b41080010f4000b001c008050701d01c075214258400000c1508008542e00c014021030400d5502e012004600d20760f00d0606980c84205443c020800204c1540400d41d0512150b0440310058151594402245400f050b1008510012000100029665210350610604203c02e880300c9201410304508658040d00c130344005804502d08214041d0f80344001555842070300e10078203203880e010340c4031004907080200403200040820288200c0c2d1090580208440000740132101c01030554908694 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 641509406 1250 641508156 641508187
    0x608031206060f040605070602090306040c0302030708031206090405030f0a0c06060e040515040203010615120c050412140a1707060f0612150905030a12050702010c1d2101020a02010b0303 82
    0x17040d98108000842c0a9040103419011580d0040004084a142e800c0908043d91401854801280301c1c0c4250f90300000c1c454404401d4807400d80070031142040584e40c05003400389030000284116801e010810190408035048406010000d8071540d56402010551a00b00216806900440c1464168004020001700c0010715800f10501c160400d02180e184ca1010a016041542001c19241c615100403802c850740903e2807101c101502c07a05000c1035910440c141d60920460151683d0041d0700041000413805030101c841c00814440b0841e01b4002050b1a07102444000c000e0340880114001a44000d00c19280103803030652032004010005a45405202c1d00c0001c500c4000510044942c02000704100c1107501103400c00d608401600d55958520b54014446d524084405a03800d190401140c103482c8144600e4048030515100c010b020015102c06c1282180c012101d2a8170200045030341a4107800c0e00b4b181062403100b180096200c000500000c1e00b910001001c1c035000798820700401401228030b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 641510656 1250 641509406 641509409
    0x611010b2202070c170c040f091e0302030f030f01080c01030b011b060e06090319021507030e03091306060e03010b09040b061503070203071e050a0b070c0203010608031206060f04 78
    0x207510041e520000c030301c0d01100d5600c0750350109404050441c0c041c05001c0c00070030882c521540880702002180780d0031281c031045031145200607211144081300d403504501c070907501c600c2182c00303401180c1c00c00b400c10b2016603050344102c401a6031800500c0041120160800c0000b81124007400c081c8600340c0c0041c002080302c51260840c100c51130340c2440e24428440036074051004407040078207a845c14078103801101d039281d0041460003071004040d1161b030b041902c0400c0c480c958109032100205580c44103641240070701150703980a103c40c0420001030220b6620146214010031030044003013116444c000001d024540c1980b01240240d04010841021780e0b9041800c42d400781c0e1100040304a920780b038010bda1b04445005000c10308910000501c95100d4000000d421840e109240c1d545000181c0a00514003140d500c40060044d40200d0b0414005020407844540c000d200e0b2800502d510400e4000a09494036684010459000080c1444403803607a081419401002501c1031450701d00301c40b62071407491085 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 641511906 1250 641510656 641510719
    0xe0606011809090501050f06060301030c052b0309050a06020d0c060c02071e0e0106090602060601121808210903180307051305071d1e1201060611010b 66
    0x107450081100d8240c8030901014000c030120410080c3c01a02e0194000c000550700728824600040008249141030f600f16410703281d010000e12403ca00c2c0506211040300c03451200c0400703031100c000384c4900c10501440c3c445520b0080c1e07a0091003903e80380a0000b284a1500a80d04642108180d0300c0f490f90041c00e000000d552021b8009014082910102d0a02e11640c102181d80c00144100c401c041800141d000140c50029400a240e40d80c1c0d241c050710000d11521512002d60041c0d40000c070158091100c2250301020108049030f201030f801030f25200c4418070781c02110104004203101d21325011202c070b242100b40700c0f01c41c624030a040c410403c46e641e02030162921200e1303040390350384942902d003031007844020700014046180107203c200605000e083c0c00c50300100058042c603c4074004a99040303120b10320100281051500c09040250550031260f070328007040e0031651100121410940901c1180c000f4000b40e500d00b42141c2d21822088c2c2900c0c0c0306c200c183d01c10600314034000480c55010080c00c410250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 641513156 1250 641511906 641511917
    0xc0105030405101b1101061a03091c030e10110405150903071d0a0b0a15030b0d120215192c010203070201110403080405090601140403240e060601 64
    0x2181e150407881c03c40d0001485040900381100e6030740c1e244070b180902911603500d8817920f10071100d0009103402c958191055440d041203400721000340070b19500095030000301400035909580c0d00880c0040d0608440c2410400095035401d015030f18002c00d00c5100d500e040e03600c00c00d0144d50b412100b1410b46005a000e09481114000110340880c59554116441c01d880034080e00c0e031041da20320200312010790346004400902c1081000421004444c0f040386910310380213181c000424200f90000e020a0300182c86603050590380c0c50403101ca03a4070751710700a90062203004d0b104200d1201000007408c0c641d100043c03040c840c0400040c05080700284600d00507202105400146041308416188080740d04035070552601c440452080f240640c040d00114031130400c54009000b14031209007128554400c9100141602d041400f040c401441c01c40700d070b140c1040051512000d586c50404401e01e80d07a0184d88110b900600c040c0300340d81c1e428043d55403039012590040040140590445d042d50311003600074502ca0402c41c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 641514406 1250 641513156 641513161
    0xf0301030210090f08100606030209091501170406020d0c0c3c030816020d020a02060306041103010909030f030506060904090302120f040f1a040e0703090b0a050f0906090c010503 78
    0x5100fa1010402071a1040c41e65509a9883d080c00340c4540401608403901400c01001003801070007402264240039001d0b01c11603803951540d11180303107600c080c0308842c1004086100010102440c603202070095015010050742c42c0940c0455204170384411206500b07106245da000004590105a408010380c207080d8030003000200c001101c20102d11200d0040c9110b09408401c0092580c004084d520500340703403800b41002c11501c941030361b4070741a6040032801a8407100401c401401c1541c05190800c1020340041207a1030045641d840540090300030780b001642e07803441c1d903060562000e04512804c00c02e0604000b9800c2880120b140c81c89542241e40c056525035662104042c4200a0800300440020105407121307000103000b03400354810b1050988100b80c0110124013440c4010000386600c0ca0903805034681840c002180c070074014010000f505140d41c03000c01401140c841505d41e0300ca030060080000305454440003842039004081c008840701d42c42002006051000000e07218020b4400742002c0e5100d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 641515656 1250 641514406 641514439
    0x409050910020c030c0d0305091908040801110a02150601080105240d1406120604120c0c090605032104050d06020d0603060b030d030c0503160c0b040312110f03010302 73
    0x1c26414011100d0600c00a802d010540010000d01074141c004001d6a10111000c80207c0c180c0d00c6c2030b103501010340c00c4420081d4025410742c404190452050090300d003001c1e6100805821036400013a60041d0100004208561660511545041313040540d103415090801c0c5000a022000501480f03000e04001c3c42c0d8446908100e413500d01000126240499841c6100709119001d4640c9421003802081ca50f00441c0091602c0047d0701100c0c0002d00090809a655480d005260041c1003a207000340f000041c000808921801c004001900c0600742c0030034564a003109044c40d00742c1003070181c03000c00c0402e0121224410f00d0310881e021980110746400c0000320b41d0802e00700078825805211042450810000f0401c202604100341d507103411020317070b500029048002e40c1910f254440da940004c4003080019210350000c510501040021703c1d000282c0c0f4a2070b40c544aa5040584060f000f0502e072600061110046002e036500003580401002e040050544d03281c0300074003043c08020300c00c404846026001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 641516906 1250 641515656 641515663
    0xe010902090a0b03070b07110904210203130b1c1a0a0f03050111070506070c1a07030e0f0703020a0b0a210204090b06030609070c14030a0201050907050a030804090509 73
    0x206800070003209a90800e01030b510020500c07108103a019004540000500068000a03940c1450700038641000381c0704000e003000890803009000b110104124890113003042c50400800c034504090341c00a40c1e40d050003480034111008250301c0504c41c18001c020700c0d6680f111003a082100c050010001252a440001c24050a405001400d50b04410f01031800a2840c404144501c100d0340a41c008100c611704c1c800182d88103100e8040068642d5012901040e00fa0744170303829441d49035000b810340c03213804075a80148108485041d00c01d840065195507050492407418489416001402070042007824607590110302048428811131490041c04038401080b140510503240c01401c01014030400303aa200c034568002500a401f940000074900112010241002c40441c0d0140c000104400010354071940c00f21120104010101c4105500d20f40100c500300040001d0225074041d90008542c038039000c240945494180d5204510495603410204082920001290242c3e21454808035090b80c582030790500c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 641518156 1250 641516906 641516921
    0x30901032a031506050f07080304020102010b0907080f010b09130510030f121403010f210803090c180f07120213032301090b010501110a0515010608160507060e01 71
    0x504110512108041c182e00d94800703c0c0550b2801c0c0da01403074985030075003110710380102d80b009501302400b00708140124480c0d502135503105205100120304000d1010105140700d900b40e40d4000403401030001e1008000d420b100b402e0152003642c0b0401e0500180e0000500b2001140d1041c41c0015610800700701e60105039840c242c040d58105880d00c1240300310f49004416090480180c900203a01800181e0814071410200c9040350001c0842000c3e00e0b040030701420700500340c0001c0f142131110f4040c0640000d44080040d501c1100710501514880c1824010b00c00c107146c1c0342440044443c415805c0001c46a0716404280c2c20084038602444850070f500200b10092091000c5000300302c81c075003030000403c5450100d0905182e4031301880868804a8000e09098ac0c00001b0000c00c1520300c0b03070043c000c0b07510178001c180d05080c005048540780310b9982c031494100800d00c4a190200e80180b0010f01c100c1d50050045500b110b90344c180d0410101c10380c18002c000d40101ca0000300201d490f01441240d80009410101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 641519406 1250 641518156 641518211
    0x51305100207050111070c0e01080102160201050c031e03010801060905090d030902060705150105130b030d360302030c060705070b0912060708160e0a0b0904090506040f0b100803090103 81
    0xd68406c414280340003489180e01c1030700f204242100010851140600a0702e081d92004400600c07000070796401954180c0100103596003504c020700c00c0c400a900c0081e07801d5003c13180c170300c0c8541c2d9a504140d42c0307a0a450030703034201ca4603041c1040d050104180e00000d9119402d4414540010140728601c001811440750120283c598070501b14075162818140300c2060403030790215075940812541c04800c0d0103942401412a902d50032403c81c0c00c0c40c82c3e01510700418220121440c007048642ea01070322100e105076000c850356003a01400c0e018011802e042000c0f00101e001100c81a0030000143d0f1a660b95407541e000b001c0b044400840c070031009403580c80392070503030808010a80d180303407800640c003d1014100701c581c0d00030f5998409d11444103d02500080301041070141211801c28205801155076501044085400c166914001c1011a6040c0a09400f952013452205010625800d001105090244c4a0b05120040310320400c4280d40000460b24401020300380440c401180c0006401c070440983c1c180c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 641520656 1250 641519406 641519441
    0x12010b03100f050106141920060105031908180f0402070f0c1502070e04140706090303120507081807090510090510080d0c0606090218040513051002070501 68
    0x9a007590026044100d90030840c1108102c141c1e44c4020843d41041c0b18072126010031010010151044488501c16100c071881e42481400340100d00c4000701404280180b1a00ca0780000c0700602007031405100c8106864003881c408010302d4216110440c0500c200e8002c010041c51208103645152600340c0564004d4500801c00c64544603203040a224600d4100c03412600381003400341c007044000c000c403452034500e0200d50050441034240180004054000742050394901002d2000c19203200b010002000605100e503a0048017034950315018065480400c8400b00d021705140811141c01e5010000541c04801404030380c0030030203501c00650801250390440c130760b03c03401c0c0701c10012800040382007281106c403614010442962503070b440003c0d0081c0c50084084a82103130400d406010700c80c080401c030043c0a01d0000619541e12030129040307074448903120070060b00c217041c2c0c40d0443ca403900c28a0303440703580d0b00d94801c40c030840d50f43c469444054044155080c950301048884c140a000d600100c2040d4480380303031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 641521906 1250 641520656 641520673
    0x160f060203010e3111030706020d1202040506090906130e030a0f0302031005090c0c030c06040201092411030d050c0d0501051507030804150510140d0308040212010b03 73
    0x844040c1d4000d015501a00c103048000c205064403402d0700c0001250a001c400d80e01d00981444403102ca008490140d030200003950745170b44941d6007071014000401080e001440c82c8008120050001d560003848500401e2040c4010420b5071251000ca40b603580048840c3c0199a881000107618149241d0003168054034055100302c0100c000001420911a2501c1e29440b644800b03100b01e081c0d120072034020504858841e801c0002d81412944907070010108071100381802140c007061455500100250800799110000b8041503503000500c00024104c00540307055000c00c1d8205065000c80c81c1e440c03800400c01030001d8412130b43d406000342e524940d11524107014906154040c260280c00c15078035411100d180c07800000c0e8a01c0c003502407000d85003016403440d0806100361804d03204044010320130f5841d400785140d0394000011901c50384e4130454808800c24a050f00301f00c0340e68140103040e454503001c0c15042c171152021a0f004500780fa8010350454031f03418030000c41c0c924a0701401881e40103d41620580c1e00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 641523156 1250 641521906 641521913
    0xc051903050601081f151b0515241002011e02070c05030102071e0f0606061e02011118030a060216060f020f03060f0406180c02070e100506160f 63
    0x12403801288240d80382d40322900c0749421403030305000441e5440c21048160a0421104030311640b005444800e0703040074061416807445036010021107201c203c8042e0007501d100154803e1104183d07800c07041608445140018ad841034859030340d034400342d043c402c0401d8110021058401d4118030400f5600c00812900140c0c00c2400c08003a401180c0215152002e410300460181014030a5132070a9800801090156050348000c4000700410701d810f030383c0160b4811001c00491543c0c000c1034000c00f000e82e0303070440c0740d074680c0914880c020b0132100f05030440e41090b150b51110301c0385070306a45a098400300c13a4000c503090200080d00c1c095000303c008003498004204005103805030203100547e103001d000107000c055003030550074040f842500c0c440740c2144010300200703031282851205001c641001800000e259501da4840a1408414a018000380e90311440d0580c07a15906000005c01085424200003a500f01620413100310112401503d00490000c610203101c0c1044107a00c06986400c18450500c039515800c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 641524406 1250 641523156 641523161
    0x60c231f0614030109050d05180604060518010c110f0303040810020304031106010b0307110a0b04061a09010e0708091509070501080708060109050f0a1a131502100c051903 75
    0x1003000d0841e514005081141e0030f040c05104000c41d409409414020011a41910642c01c0514004030151003c00c8040c0c190b1103440062010b07016540711161078440c8a10352804d054045c072002d81c10000d0b0000c0b6000010024204141d40002c200c2d4803001c540d1682000c82d26502440d44100c0c1140304d000c01401004c101c41d4021402203000c4e9495269000c00c00180940c0d0f08000c5c802c078422540100000b601040c4540784039219040c0c014103a0f103d106458454526404e81a102035400550307a030340c00c903039901003880c20000c0e130f0300190703000941c940c5010005c007040300e40140340b0b40501203034500207010090240040c40304000d04554003000c1d03003000e03004556609010300856020600e080049840c403800380c80e0851040a0507510240300d2814241400402c448101000e41c0140341c0c036502041341e4482c2c0b885050040000030805442d490950509400141c50b580105815000b58070030305d0107294003243c2070035105910720b400700e4491030b904003c4806d80300384503003d80c0c844456284280240d5154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 641525656 1250 641524406 641524409
    0x40203090a150b1002060f01050409080f130905150a1a0c060f0108060106141c290f0f0310180f0f060b0a08150c0d05010b0301080106060c231f06 64
    0x3e0313550b04407807112440140d07603500040e207a14404040180c010491443c01e45c0140c046a0320904040f42400c0c0c840c0145a1030750031504146c03d92015002040c086465140700d0310b03500c5445840c03040d0f000c506500125481c9080e5004100c0300600701e017842e50301142c1d0f00341219000348408045940602d005481184142400e0141d0f4010707000d00c030700015185110780c044240b44a4040d0046103428218441044210309161981a10ba030302d80c5142142ca02c42400b0b400300381044000c505819a0900d01086800704041d20158411684048001c1c080e40700000c214044041c142000500c580029810b07404081c5143c900501f0040c1c0c40100c0340800c82c61300640e0880c0307407240009112849000081012a0115000340703066644980505102e9104100d01c036604550588002407400300f800215400b039034801d0300160418840040100144d050902c2803400500003450182c0c48800c040e503801141c4200d154054800740780304c02e0079070003120082c055000b1809a0150841d0590302d06148a00600f005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 641526906 1250 641525656 641525659
    0x1b12080702060a2d0e0609030a2c06030406090203010c050904050f06011418041b08090a0b010b0a050c0d030f0b061606020f1c0203190207050705040203090a150b 71
    0xb41c501041080d0901d00403445402c00f0182107041200186003a060f401a40640702042e06441d086101c81900c02848628003486e010000740d6585c00351458090914005c0a4441e6842841c882d51020041000d1a030001c0c2075008a6140744d581d284d43c2003140c040c086103403001e5450351905a0002e2059005801403030031280949061080d95034424240c0200d50040350b40a02080706920340c103c01200000050991205103c481007450045101240840e43e005a102440841c1419580b60f09034006110690140303030b042c000e0103840101d644514412206108501844bc404261080840c0c010f005640721644200200c411030700342c0002c000d01400020055800043c64070445c03001604092084619030300d11808901c0b400446070762810002d50004000c002c01d103509200010200941c0f20140e030504e000403001503148d0078424807060511130f904641d9813510344108045000514040303091000c6500c1124010703241d60390b01217000e080c003900d8607001b032485400811200d4504104c0e0300109a5620 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 641528156 1250 641526906 641526913
    0x504170d0318120503100905041b0e0702030a0309020f04020a081504021812010e03070507090c030207051b010912150c020f0601030f050a1a1816061b12080702 70
    0x102d881e0aa00307001c1c035181c0c0903010200d030041a8500c0b500a0000303580017021015204280c5a851940d00300301c40c800c1d24101d440510300039007803000e2107000d0b01c5240902107080e60f11034a41003801001e552803003817180c40410701d0f444078000d0301950384440e6610b8140c800940700307561b00c16051000901200c400c880c505010240000c00d9201c5040610940f118190190340c0c504e000000d030410042034592a001301c51035903484200700c5648030070500107050302e588141e0040c01c0003420b1511240c2a141000c400004051050107100d004c0351001030409010244403002c04221554900103c540fa03917903030031041c40041841921020800360030245601c100c10300604004c6c1441740320007240c0320b500c4404448010341c0204014400b00b000501c0c2c0c6106248a401202d18540741c69450303c2983c03a400c01b600506001e14410003901300c20420a0700c44480c800c601405210f01c40b0508400f40d450030380035020801070220201840c220500407044000380d00801e44090120307c8410080803104100d030050014007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 641529406 1250 641528156 641528171
    0x220b06031513060e0c0a170a0c06170f0c030c0703030b0415140904080f0c0a0b0408190801030b0c0a140d0504051002040f0e0a0b0405041101140c15070504170d03 71
    0x400301700420346590042400072032501d40000c1c0404940c0750f1807804024000d03108602c0000703c140c040c000003400307070340c0782d0888000910614041c140c2c002404212050865070400440210200450780d20260210b0707100e1703c84015060840042460390060b0350028944460201a00d0700b02580710115003544180515a02e280350500c02e203d48280d500800c04201400103018100c80030018010301410300d01290006d0011b901e4031241c510007501e0950703148400040c1c411002c1d44064222004c10340301e090803211945182d9079804118001410f5030700c003082c04100e240ca143e104242c25030001900c3c40b1043c2d102d0340840b4644c4002c1030182d0b404c403998426a034000456a1850099400300e1701c604e04504190b170b00c0c05800001c02c4030014450348201d03648460a50300385d501c92007014003c1d40030303600c0b80d6080749008001605245c1088402e0942d00e106000c0b070310380034600251b50550000401042803454076142400d0303825009070782010303810603c0f03109100f80580002a6020030005c2d01c0c5c0d0244a4031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 641530656 1250 641529406 641529431
    0x305070614011710020c0613030c050d181224110409020a02010513030e1e090a0509060114130908040510020c1003020a231605010f05220b0603151306 66
    0x30320529a2010161f0000f8000174a03644200080306081800707401e18a04013103556407001c0c2054681c444d140e02040c070410702020b08035a48000701c0040d100304040d00c0042600b41d00c96500c00c0004501b48030300000c00f409400243c1410f41c10880341e0f04100c44a0945840e12600381201075000702c50303407800541c602030019451003040418400d1181d010740b00d43c42c401c5640024003140c41d090f142c8049407107500d0084ca000c50345540900300c2c45240310364400641d84c10b02241d42401d001040e4000c100300240a40b844801da51071501d20000c0140c1c107440020080b20510703080b0854000c950019500111020100c8a030b55004141c3e00c0c00d410080b6010b4182d801e550b4010740413800390381043c01c002030403e00451040822004021001c54a6010702c42c01c09481050740002d500f44020103c4071303a51600c6c3c040d91018818080d0341e0300000310894010129181c49072a8178490603d0b00041c1c22001448003080f03c60b01c082c0103800d60060040f207017540302d2600aa20040107104200221410341ca01541032251 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 641531906 1250 641530656 641530661
    0x3151509071e03060510020f01053304270b0601090605030109020c0703050304060201020c0106050d0209161106160806010c05060a0903090f0801061d060306040305070614011710 78
    0x281140d03250584100c4140c03009205201042c0750007410326030785070004600e0b9543d11030111007a40443d801004094500d004282c00d4690151410182c0c5940220401d0302220116220140158642d5050f80c00143d07013000030040c0180e03010741131034842501801100c10841d0000c0c0e03030095005040040c0d80d900c51100454010032144a1100055014070041c030011011f40c00604d1a55000c20403a0280707a102c1c1c480b50308560040e031200300540e5002495044021007801503400414044928540e51101d94011804240e030042a070940308144c031780c040c41680e0107002403200900800d01121010b160040c03001c0c5800c1040d45810010954042c002030556116103041c8003c144e00c0405060651510b610b000d014049458046051010b05074006c42c4000c0310041c00b00003850398400200f0820300d000807043c06e0801030f011960125499000700241500c0024060b80c10690506d025650746200b82007035401448403000c400c40c4072103a00000100400d804d80ca05c882c4148140c01c0c0d803c0c0417401d0b40f54004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 641533156 1250 641531906 641531911
    0xb040503060702150f04061b120f110a3005040c170a0b0919080d2406140c0a0b0105030610030203150a0608030415030b15030a0902060903151509 64
    0x8255005000048800c49038010040e040b40c85524045450b403801103a56841443c0031401d01c0010781e25241c0c81c002c10042b401100307101c03d00300b1401c01c180d000d1500000914031509102001307108000284071041540d0030211903d0341c60b2100c03c46552a464903002c0050401500c05a03154a1600800710f1041c0390448120039840000c802418001c1d0a5039403900031102c010850741d45030082c501c0c1040381201c500c01c900c4049108181d581e9a5150600d080c504907107580010b00340c1003418404182c914000180035400784c81140c00c02040a80d000e0f01c03411858450282c098416001d401190300801c002e070302c04507060b98421010784803255210710810000007003c1c80040e500d54000324482e0190303822542c085800c100c12140100b14a911000e00c10720f15071041d407117940d000c1160754104001c03d03454802d0140c0d444088418400c270140703013541c00a041c04040c0081200d03d68480300c807021584c803401141c12010016041d1400c5030300e0f107441e40410b00802c991100075264091050b4543d407400d0011540b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 641534406 1250 641533156 641533183
    0x6090c0c060b01050c0a06060f080307080d0b0a2d0b09130504080f0310080c30150907090608070303050a11030d090b01090f0e070b130f0b040503060702 67
    0x208541a85a290150004080041c1803004c108445180010213000340c40c1103500604c0c010a00700d241020000481015621190346600107102c0940017901241c101d460303280c0104008900701d005003000507007064455200021200940340c00c182c0c13020380c5a01c0c1110030b244070000c00390b0b1b039556900350034010303c10f0001d0681d12112074016464008456070100d07800c540a803002c0380c10a140744d91521b140390302c140c41503ca80c0381020010402403504000389500580283c0342c016044400d440080542c010380c10074480c01e07440c50102100508010000c01c0c21010400c2c071610040d08003208001e403221111702440150505145010880c014001031050031607a1607900c162520311035510840d20204c0c10080c2c01600c0c08100315003c80005280241d182660046400460301e5150082100481b40784c0c03e032500134103040c0003a1186100000c40c2c00b908a82d034850340c59503100341446034081c140307801d1b42021418054084001c5080c80c2050050000d4604c107500b299500d4a40c8001642c0c0d400f00380d00480c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 641535656 1250 641534406 641534417
    0xc080a0e0c100306090e0601241b05100c050c0f030903191406010e0f1305072601060b0d061703031308280207050d080306280303090302010306090c 65
    0x1038460401c100b582c103640459141c006281038030703039800c641620340e0101611096402080140f0104900ca004801d4001501c179000c3c9121f2107041003e00b0b03000744000803041c48505c2da0003403030500078140000c81c1d042da80c40d8010424440c0c815000b4201d500441c80064042c0704030703170328072841d200004119028802c0090045c03809010f024603081d413660302c1980484c0d42001c031500000405004020441c0603107140610710501f490b00c1d00540b0117414008043d888410300c2c600800010403004036040083e00c125100503d49200403c00c400c0c0080040100a05c9561070300c0c60010302242030300041c0041c8109094184001070b030381c55940325600445038441c0c0c1036401c10000b03c0d0100d4035403c03407444020700c517545031400d11516100307804200c01c1c034a01d08414002c1c20b140369885d0341d0f8103019401c05420220b80040d00d00c0002d4840c68030300e0100402c1180205002c5140c0915640c2d01051a070035448489094540146c403454010600703a801d20080b400300303040a001280b5040386005240c803400841e07441 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 641536906 1250 641535656 641535673
    0x20a061b14031f08030c0132150a1d09070f060e18070309031205130206070203030d0c02100c050301210606080d031508060f13030e0904060c080a0e 65
    0x7910407a031025183e50100f14102e840000740d000c0700d041c07038001407035030341c1c080c40d1141010040e05081d81c96120351340c03c0401810344030707101900d01485482e900350441d0b0200c6c0200c1c0e0300d043c4500ca0050004902d01e03400715050000040c540b0452440728061003000a01c18503a46583c00015034030400ca0140d8080f6880342e04040c024079108541010b14100c004105280f048040b91118003e20b106607402c0f00040d846000c50020316410200c030040409413006c040003240360076282d43c0642c10075008028410070000030084c0540da801c0064600c2d13040d020100b0440b1050b11a00a59180f524901c20508241820504110035001d141a681280c030407007029015041420100c46000c0d400d00003c5400940e200d0020803003400c2000600100b050305d450009510101c44100304207070009611000c9141d100701c041084146410b100c140e00310100d0b103000390301c058041c502a13401c08031040600750000c0051081100348074094001c46000307a9107440f041c206482d40d070f020030280c1c1c0c80c602905111b036004158 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 641538156 1250 641536906 641536937
    0xb040218120304090504150b01022803090b0309071d16080402040213060e150304150915090b1806090c1005090607051b180408070201050705010c020a061b 68
    0x3000c0302603420182a00d03c2e082d181c0c002c4808031401643c0c142c9200a005482c0d502c8071016100e0b00381004003d00081c400d1402260300b02e040e50240040b2100f034030310741039a0b640c00c05002d03510380c10107400c1400e20992245801040300d40c0c1c9140c10700c1103161040c56220001600303044070281034040c2c210b6402100108011820940d035100c00500201d0300164204840301d002510301a84c00050440e941d20740c03020746800010050801d91101d011b148400c02082444009859500402900e200042c0d000c00e280040382020580c03800000d010092003801c245e041000c01c003a8442c0c01c0c1c800c0c0c0e03500407443e501001c500700c010750310281120319070855808040b200040c3d04d07004a1502460300c4034034040340b170504014003003040c0b50055802103c0f04d91000c1440300d01400001a500c0f00d416091742c0d001c030164101d945000500c1000340c800383c007101c030005d117150079a4401c5080343c0380503811034000d0140c200440c42c025924140000142d070301c14500174020707024581690b001405010f1956801600052440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 641539406 1250 641538156 641538169
    0x40c050f01120e0c09010b1809040c03020a030c0603140c2703010603050609010e120304030c0606121a0606090303180d2907050301030f0f050a14070305010b040218 72
    0x101003414805010b000791490307001400b81e86030092903200030707120725411441409060001a003000a001c5e60502c120a00641120314984408200b2030301c000c681d403501e052003803c40c01c0135080650094100c40010042c4113011040c0f0048447c15078003007001101d07038000c100000106641050a4410030081e903c00660108843c01880000c1c1710704252003441000004d003140c2130356004403506e40040042244400342032048101c80c1400401a2030318114003400700040c1d1100500040610042d903604009200389640320b80e01a00070b07180e800c0140c0d002c0b07003030102c18117400440e011107080c02c000001c0d18a0030100244c1c0c2d83c0b000050000c43c01c1c2410490807800c03d0342d00c030140d140c0010308103d4020200e801e4a404010606207940880441c50a03101c6036603c0040060240d020b20004000420014214041a0031610741007807030449070082600e4040e04180c0c030b0a00c00f0340411b080d00bc0c810400c10300411614201e03441f806c02004003010103c180f006a0080d0100a81c04600e00c0302407921314102407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 641540656 1250 641539406 641539429
    0xa0b040b090415090f050a3b0d0914010201090b070e061c14011203090303080702010e120c0d0219230d0915110709110f0705061e040c05 60
    0x204041091219007072081803900c410790050300e4007078451040b0b0f45c402a55219064000b28850404d014101440c0b940e0500c161141c0442d817000c0390141c5101100386102c8094503403404821080d60848803054200130000c01042c000d4901c90701c00d03403404000701e600502c64248440c4e8000303040d96441d41c1307a8038103503910100124030a03041038003000170f0140301c1e00e006080107581a0300319001540d5a10041c8140054105820401c800181c0b10305010200750041c0107034080341c2c1c0c9490400d04030750b101c080880c094800fa1274010058403c107100c0b94110301026001c2c0c4480c1440d0b2041750074542d2041c80881e620352045440241d0b030640f40b008071021403211030ba6081c80203e480007d01100e2950000a40741c241800441c031f0024000c000b0038420310a1207068030b0181000340c60244143e881c48055551180755038800d040311155190701032000b10000d44280c628541c0129102038441c2c40d41c0c180251903480889413500286040320f416007002001104150089420525101040e8100030a201003028070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 641541906 1250 641540656 641540659
    0xe032a0a050d0b310602180301051302010206100f030f08160b0a0b0904031b0c0f031a060303040308040909050c0a0b07050f280809120313050a0b040b09 67
    0x24040812140c89514200c088140f15691080b41450a6a2081403c8504062500c12900030301d050041050100d80a6044960407044c0140d1306d500c40c080c41129000c03040b0b90203400d542001c041113100c0c031410000f80c403170314006c0e000d90721550346842d0a001801d0140c01031005011500c0d2050001c02d50070380c0317008040c61082c401e1610b01045030924072114160103500316042040241040b0b01001c160094004c290015551541c007810180e40c05014081d45031a4006480c0d0074110440601c101100041c0082c2484404101c085813241000d82404466a1501d40c030701242d000881c8007420000202c80891703800c14941400d0030b04149001010704414103003540c60b84585100341003141e881495030001000d40c4085a5941c03045481c0c141d0070840f0b8403008400030b4001e100100c456007035030944400f1a20145003400b64441c46481c161011b40607049510383c001d04000400720308110300100400c042e16a00b05103c400d0ba5903039080210441c094096a14484003d100401240003810080e2140300c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 641543156 1250 641541906 641541919
    0xc1407050f030f0c1504020114072f01031505060319060e01180c0e090109020a05040b16051207020102280f050106060f090305280605070f0e032a 64
    0x1d0052466296402000c1e182842c4600001d00070b6944038108500920002441e4212510345031a40000e004980e4844e1120800c40300002d50701c080043d0b000f251203000400c00f6071140701e00200e030011140b54450404c054042464038041004c3d18610b00e4030034044810052030b02c0c0c510f5441c3c0003c502e980c0b0b01c1da04406121500d640010070702512001d9141d010300011007101d00c90301c1c000003001041e80c80c5100d1440034000c003a031000070285c46100d82141519080e51000d65940030b4243c1c1110648950342c04203400d401d012a1281c8800f17440001c0b02c401c80d001d2022126121280c0100c0000c42c0329500000b0b0269010340201c82c1204070004520345d0320580b04090034800d903460707200c02c0b0815032801e0080310700765036405051256581061070359100e01100e00e0003020047c00d40c1d0311695242c130007101310b21045800414500700301200803110400d41e68003ca05102500f00803002030a0404400f05460100d524030078110601d04002a120030030500500c00040075049406902548210b1040403681192 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 641544406 1250 641543156 641543173
    0x10503072607081f0b09010303031a0310020301090509060c0d1a090405060108010f0608190203010b1206061302090303120c0f28320403060c0806030c040c140705 71
    0x1e070921410008001450240c203111100c925070640321805a00310307050780d41c9000c2043d2556290311245a043d00d505050024040c9000340401b800000d81d41a030f160305104203129408101d0703894002e98101d54034924144610303211000c016441c5c00d0100d500c0280400d01f4804503410a419800c0140b00407a03100c0310320a00c060040c0820303243e40b405c40301034030310b540f1644c01045030781024403c4168010000d0410002141012602901d40c10181c490484440404000c5015540e082d4060003006034020000c000c1e100052002d6a1a200d0071202c01c0e10907052007540c0c2020103014022a641210020003035481c001680c01c20040c503100103400c410054106002d41d40801c1120390041888825482c1d40502d521001003100b200f5120101c092010444110a00c00d888011034100c04504090741104441007040c3d4054007038240a00d03480039000714284842c4050594000304a00d0184c07605030145c59213640014284405ea8a9040c403003030015072241c051005c12078841024003d4581720b0825181e964 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 641545656 1250 641544406 641544479
    0x304080f04031e030216060203040303081504020a1d01030501050d02130b120c040e070e0c0d020702100c050d030902091303031104030c0608100803190e03010c03050a06080601050307 80
    0x80159003500c80d583c03203000420f01c0c00d154040001c60442e40000003048001e90a10038000c2d100d009520006091200c50b10106402144250084c2c0001d40090811034580101082c01007110b40500d49400d82d80c5451060728406500c1303402501c1c10382c1c0014200c8004043e1541c00c1c0140841182c4040c07101030341e07428110310070f0780e5812507007900d96a00d940280182080002040102d884001c2605260381c01114204000f0100c500100c2e030220300a04550703165041e180300040a4480c0817002940b040b01c1026151459030841c1c11101001d0291044910420f010f89040d0222403210310041d500c032030b19400080c52420309071a2260340902c6480d0220307024511000c40b94107900309070030407120011054070034806070364800c400541c01928002468500c41c40c02c44200e459110b07003400c504101c2c44c400804100f071030140c50b52070310401c0040c0003004210303440c40000b40249000c1d500828445d091000004003004000745035816500e0060203002441d01d0050120039000031041003040b40004000c20f02c854 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 641546762 1106 641545656 641545673
    0x7020f010309021f09061106090a12030b090c1b030315090709031b08010f09020303390309090a0612030c080d0f060f06030c02030304080f0403 63
    0x6000d0340d00200c4c220300500d4014254043d00d90311018a00e591204e460030480d26150307548941040e0700c100483d110102034035115607a9020300309110100d000048000c020b51490304000074841c441002250100808580300c007a94480811059980c0741b0003446489446140e5020350318520384000088030201020509a00482c1c05c1400202000d00450645000d15044070050703041d9541c401001c12148002d0041c00001c0d42000d4901c460401c15000f800421907000b000b2318200000c1d648031110540d00402d9909200002d103200e0f600d603007103841000c880b804500c0095580c0360743c2001404460a005441540c8051900d038003040280d0b400443d0307688140c0e041c0313401c42030741d4030354240110702d80074252100d5407180c40d080754003c940e1210351200b412510103041d800410ba50712007099085441154144000d60000c000290006001c0c01c010700094080324402401c1c2612070301e031030702d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 641366906 641546762 := by
  have h0 := BRFrame.cov_init 641366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 641366906 ≤ n) (h2 : n < 641546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
