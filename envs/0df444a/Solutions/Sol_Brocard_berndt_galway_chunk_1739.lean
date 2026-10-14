-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1739
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:29:49.158667+00:00
-- url     : https://prove2.me/submissions/0b6e25f1-0240-4a16-88f1-904856172255

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 312589928 ≤ n < 312769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 312591178 1250 312589928 312589933
    0xa0905091b0f0f0f0a0f050903120d060b0c010c02120309030301030201120f240b0a0504090203060319060f3602030f2508010c090b090f060a1d040204080d030e 70
    0x1030700110305a00f0050000b2403001d08030103980e084040c001500c00b40071000032406000b03061080903295500804c043c640710b4102e0b0f40003035a440c44080d201d0010506504008140e0402146240c4405015030003141800000d808486268405200c201c2c1d481c00700303d030107044545c810001440107500c18940c2c03051425031404c0204202e0b0308590904161090707180000a2030322120b60201d02d00b010f40c0e03036450080400e001110310707021003400010131505c214052162915000000b28942c1c0c1c40404c00080b01c03103000702400900031500d2a040000d044180402e105003814841c204004070141480000c82880016003840d60002030300c80c0c0004410030b180d042ea45401554126019100d041c8101e4012528000050107032800000b8a6508140980c05c0550240c0c90b100501110b40c0c4c03c18490b8056480e64090b0540f111003801c0064410903150340890380005000c0750308200150050901008800303044500044a9407944c1407000f02c1c010341c0b0941c040c40e8030001001a070305010317a101c081046c260509 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 312592428 1250 312591178 312591187
    0x409080708090109060f0923030d110c220915020a020304030510020304170c070906090203061f090b07050106050301050705030415060302030a061109030a0501020a0905091b0f 77
    0x150481690003006007610007900014030140590b80c0b0016800103024203051031400f1199520b4024032100190080c14098141e0114441c000350583c10311940741603008040384e8200107400001001072590340a603210520404a41c005240b4040c40d0910045500043c0c034260140a0505000504141e05c025201001c0b524108014180380d400140010000e41c0c00841e13446156142480c94202291300c0c2400c5288140300348000a410300440301900d0030700b00c9045450f0903c0302e12050030007403a640243c40451070864002035020958020714030403e41100c010030b5190344488459807241801c085400001c0210704240310404099000e401c100b4002c0b400024019150b03030104c1d00311101503500030003041020080204011000c500180400e492210902045140d40c5c0401d640d04002da8000384416140d180b08801111604160341c0007207001000c40c2c904192a04009000b9846401040001844a00301140c0c0b400c000a0050244c425401c05000d074011244080c005c54208a04080c580310b030411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 312593678 1250 312592428 312592433
    0x5030a0e100c120908042d0602061e070f050c1f091106070c14060705060f0414010c0504090e19062301050f10030e100501080d02070317090409 63
    0x600c00c1500c1e610640003502e145000009404210a24035074000c0303904100381100041c1e2100144c1c0c00702d42c20f0002958500f01d240e41040848003601c80342c098030820004000950035070008042d405000700d440701c0c00e20511700004043c032464003141c1e00d001103140442d0302d13a06188600014080c201a032415500060440300c44a102514910f482280d4240c440a004043c08241031046408540c1221254a404840e50f50440d041c2054410320480d075058212032951a11960704880300c25034011305886807460148940e40c21144140d4003518003007520708280f01d0344c2d10305124000016142d61901c504080c40c2c242510060711802d04030211500650a14100403040d5418041c0c080b03100f0328002c42c0d5030940581126404281c0185082410700810042012f42c030b404201e24034540040e144581e505450744000da0103040f105465000912800c500c4980103880fa50102d41660004c2050758469101c022003203a0384c002c6030001504141e000a02c040301840314100800b4010400391002c601921142c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 312594928 1250 312593678 312593683
    0x807062309100507030509032b1a04050a060e0f04170403050d0809010c17060414090a030f0c080703080603010e0304060f02070905060102120304060b0a092301030b1306020d0c0c0309080604020d0305030a0e 90
    0x8004041d680d41c0d0001c8e00d52000c0c9000d00418dc0d000b000c0c040100300d02880c0084046842c24041c00e40d44000300c4050105041c0300c0055002d42c0036192110300648d07565a2403401035a00c5690741c6080300010402c601240e02818180148803400f5070b10358946a05025500243c0850b000203410568003540d1158142601b801c030814161003808080058004807842e4140a00038000f03e111200c2088280d1050200049454059a9a0340c2e01172030400ea07030b80d4078400400d004100c01c100308282e0b4400410005001a030204c1074941c00100c517400e07111003e98441c0e01c14103584040d1405e60168000d5101c100d0540000c00145500a00501c000b00b090032019010507014001d0350410071509441e005003d41c22115032040158002c0070302607143d155851501e130a00403c001400c05079410003001c0d5110700748500782d0103442081e02c06210030080b0301d21100700075100b8501120210007084080c10006001d2078041220380c441c54001e006442044181d40d400c40d03150713000510b003492165540380510300d0310604 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 312596178 1250 312594928 312594941
    0x501150f1110051f0303020d080717010821070c0e0402010c1b17030a09090c05040302060301121202030c06040b06210a1b030807062309100507030509032b 68
    0x22000000d40c0e420b000c1e5400c00c40e50014071113180c1020403040c0400000b94006500c1c074040c1041d00d0314084540f60720780c0c121035255103581e03011491001d4000110f02e05201060885008510a5015070003810840d50384072640100740303016240d40d203101808c00440b449035442503030191052400329008101c0303540e0559030403124040c01c803141107650010320030070020b50100c03060003d400d00114101800d4802c001e0400c5e171107020f044021a104c0032040e112600803c144c4001d55401003180f5101e40e11040400c0d42a030f5a12000e860340704a220142030340c0c07400882140c408600c140d0103000c0740c0e50742d41c403069240500680700a40003032003010440d0881d015403d94400a43d001c0015004c01103e07400d1455080b180f03203002640d0748501c1c1004000145100d421202156805280441c4082da0403840c51054628060640d010201034810021201c801217440200c20320074810800c115160200120200e910480f40c0011551003000303e00c214003614206c0044902c814621034100744501c0d42d9a5003a02c0b003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 312597428 1250 312596178 312596203
    0xa180b03101e0504200307180207020a0e161d04050711010c03050105180a14040c08160b0403060b0a03210924120b0406270501150f11 59
    0x1550b070348203041841d81200240300050304030740a001c0c80c10a9152260243c2d80d290105070851034081041405450510000c4018815507808080761401a00d240019503c034041c224803811a5190118440a10200560003580c0b0b00c1030a41c40750f281148107407040d02c1041181c94405d01c03400d007404c0d8150341c0c44c010b071441000c02c1ea8403803001a024109850075552a0001c0005040c2804010f010f96280c50765a2051407100700034a002d55125611350714000d1001480300180b020701b4004001c10302005020580880d818081140e0320054450905004100c0034020307c05030f030604100400110f81ca641040022107002010f840805e070303495030f135102d2011503600444e0740b9001604a00e23a4458000d070714000103020640c2c82c11010300801d500e602040d050704402c20203101582c3c80c0f40c40c2c400c0099220301404400604208007054440d0fa0b580d003030803e24400c003400c103c0d05080d10384545440e0700680d4101d44c4600201d0910100d1040c080c1c1d0031203022100070b41080b069201c481c0244c0f408220015039001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 312598678 1250 312597428 312597431
    0x515071b0905060d05030d0c030204032901060206102d06091a040503030d090c03150911010302090a03170d0908040f1509060c0c17070501020601050109050a180b0310 73
    0x5180c2041c103030076200c00030304040c82081004080342c007140300842114160004020700041300c601c06101034001b4003071500050300000307180c0d6881002070341c83c030094002601924040c900703a0b03a81d40e00890380c55404036002c05115000000c1005070104003d13060915040c48110386180c0e58414407079000e4080c0d00c1c0e00003800a102e131501040607842d81c1c0f0203c0c91074494210180d15140c01c0802080e520303c9178641d4400d620b6918510030051008001c0c241c009168800c00c2000b043c10360b1110140507000205054555a1100d21502034941c02442203410b45200600300c0202d103441c5445580740040301c48001541c0c0642003011650405880c4200c10425114111468540b0704241844510548a400c06a0325400e25007101c906181c1069046040310f805152280c0c500c5110714091107108603661240b0300240d0314a20f511801e41c80401c98030103980c007e80c21100c513030381e0f00d500446111515128080e081500f0302828420090040409244071000442c0800c00c2d8500e0008245004c900e840d01c03010340c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 312599928 1250 312598678 312598733
    0x12070b300a06050103061a0304050109021806030601060e031507021018060c0c020901030602030601050403060c03020d1b051e040b1b010606170f072106050108090d09051507 76
    0x3401c0703104040c0030349001e00e0b04000e09400c00000e44001d002101c12010405004000601004005d4009a228982c040c000345904c40c0b100480d42e0107500c00f551103d11130300a030000440e0782d6104160f074491500303004006050f0014100606861501c0103040c140071400341c20480e05082109001d00940c1c5480c0000c8818500d0850521030211784c10300041104000d5140a01409a074505036141c4c15039800c5800140d980c0c43c3e20005171014807856000501c3c0c24145604401035036095805001010100a0148146809200c2000c03205c4c00030300703281c40420070900825216440c180c1005102c2903030211070742e250079100d400080d11030700510441e42c00182c40c00031088000d0b400f8002c200c0204090b091610800f2442c8020f44140c03800200310102042400c0006403030311b4807426184212600d84000d61000f40043c1d21800050001405418082090315001c280121070002d041080c501c55503894510090900003004201003101da040c500421301480840041400d0120344c404c0c10401b101190100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 312601178 1250 312599928 312599941
    0x150c070303060b0a0903150b04050705040e060a032a0506040906080d02030a0504060509010219060606140708040909020a09061e080d020d0503060d1707050c12070b30 73
    0x1980c41ca6001007000040038084004c206402c058140162603100c0d108000b219800880d41f002040003c1034598401d00b80420b201540390000300400581d1021140001c0560321982440318542440c44010880401000c403034014a55162580318021700c0a0300361514141d03248005500c9401940000c03503407075070f0340108228103002000030400000141c00614244840100060002d0089100780e40a10000080b4104c484e032081c45101d1555547e600c03050008005410010014506402084007080020506030401801142034a01042d4020b001c0c40c6003d04101c40300b8080d28448000300d801101c1000b02094610490140c88098107101402d23403200c000c506240f00c02c0c0d480c1a4010016601319040c0745c45116404034548500c100d0a08055507a030300c03241c0204014580425004e400580c00d9611001103000d040b00500b1f0143c010003c5510003001802000201c08405000c414281e00500041013140c0030034004d0701071281c0c400114003440c0f10152a402c40b111400881d07412682d0300c1780c20402e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 312602428 1250 312601178 312601181
    0x1a010602061302060f0d0c0215060f2101060302090703090c0e0f0a05090c040e0c04051f090f09151409300c0715030501090507050702010809150c070303 67
    0x604180c030051140d420042d02042d0b1030809030002a000c0c0500149020b1500c81190481d000022185802c01201040c074800a440f00d00c641e801c03900c45259800850307841e184c84028010304890082417104c0d14000328900c06070310a110086c1204554803401d0000144e40d403205071302d11401c00740d200403807195a2031a00c00b2044196402c4003030203504e2041400503da00c0e84802035417003a00e01e00001000e4131180507032480d041702902842c1e442401c1003200c600944000c0340c541d0441702c00352001c0c0041c1e01d0304580f2242021071030a1000b00c035496014204250308040c1c11940d406805039a002501d941c461b2290700320090001c2c04106807a80356500841e0305504503030456442140368026180e42c0b003280307124001c8a8200440f0302c0a45000c0340e5601ea1035003400e002c6640070020b40c011509280d968410003555250074002d1a00071a241400000707285a0394040c20744181c40540e5114a841c0c03459006450344030005c1d065861071301c5145a10300d442e0644030f040c54010043c3e0001c0684070a100d2030001c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 312603678 1250 312602428 312602431
    0xe0102130806071b02010305070201060b1303050c040e0307120507080318060906040b070f1404030515011403060a050406020c070609170a0c170f0102030f01061409010f0e06040906031a 81
    0x14100118044d43c130004034009407411000550900e0045520344074001d04038050400758014668141e030000f0500b56001c05000f40000701c80c403c905942c00f90030344408110880e6601100c020701750300200104000030700c070344c680b452300f040c000d0130f01a04001442d11100b803590012031304400c0115036028282d244440412216910425400040110b0701d1305039111550140b0181c400001e00c4150200c06180d24000d0314107a402940b905e0215840395a01c1c1400740d914002c003600c003240100c00030008a004d2101004c04001044058010089921403018810041100400c25038500d0f81c02d100401d503e00090140000501455442d4244541082c0104451140c02d2134043c9955221001040029402c0110002140c80f454102051420004201c17810140100400c4d019035200004200d00e615613a5601c0b41a6151030ba10f00c2c2c882502c8200300d000e80d00c1550f0046010465042081440f144683c0102030b01c200041d0407035040c15500c44407201030722034641049607562019a0074501d04d500f01c80c0b505 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 312604928 1250 312603678 312603691
    0xd02040303091403031c0c020106090203040b160221090105071401060f0b040e0a0b0609060c0f0c091927080403020f04020909071215030302060402100f0e130e0102130806 75
    0x11841c1100f0b040307030320074200c81346c2c0500c000c901d4803110b000300094000e6000300014890590107540e42d2416180031000e0460032210510b03007601040d0141085440050786000d03005d003901c1040c44070009085084001e400c10b14040b4100b0004001000010b018551b008185044010020511030702340240304e003030f00c2220781101700380040500040000510070920385403c010111000100ca00a003c04180c43d4419003c070103402050000e000a040e06000908c001c0108156050300d0f043ca2004040100040d0182c0e41002c8140b0a07030444841d5a000380e000746444103001040380343c0c85080f140010891020300b442520f0780c41012404005500744803190303080301d100c00c4508524000c454000540c030140701401003410094414240c0511b00c40a60003040040c4c070b04088000200e580b407070000e58032034040741d04034051a2510b040303401c000c0c05041c049003084403507103034032603142034801c107120710f0391024991354124a40300c003005003c00f00c0c207100625642003030100c410300e100d0500c00141e01e04000680b02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 312606178 1250 312604928 312604933
    0x30c0b0a0f03111b0c090103150b1504090c120c03141003030c1518080301051011120a0507060f0903021608061308121501091a1e0d02040303091403 65
    0x494403050718900440304c1888900d900800d010f120608020f2501c01419036580d001400c0e0400441071001c0c45600c06884002480c2c140715901c924801c3c044040100041201c04640500c41442250500d0b00201d8420320380e0300d0041c42e0144075070b03031a60586140d50712840109598144044520b000d03012030035481000b88041111403441c40c0ea008000c4000d00c400070f04807400451440e41000c843d50040020801040a8128051040e05001115a02c00c1c07203510310412441400c001d1040c003640b10400342d041540d0282000e2911803042c40303a15480000580104041000218000b594030312984d000070b0340e080000164518a0715000c0e10b4282c00400c8006c6075007074003604000241d40001d00540c0142d040c143c02d00c800c0940c1c900101c00d400307540f441c0c44104d001c403001c1204041c0ca81d0710000074104260784003407046986990b0040701920306900300f101540100301c120010307240350030150100443e4442c10380c40d2000d0b86aa040490700a0380080300001c1c0030a80801c40400c0741078010184d028120301 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 312607428 1250 312606178 312606191
    0x60b031207080a110703050d030c09120b0a0f0209030106030b040507051504060e0d051b010318051207020f0d150c2a151a120a0b0c0310030c0b0a0f03 66
    0x100d18056010f52a140420008021082c1c120040244a9a0001d42d404000c43d2249050781a01030040d101e000300c900002100c0c070341e0002d501d190302d80c8a1603006803c41050314158460403002000761444924904810741c0030003070041d00c0e45091050703200550286100451a09184ca0024184402a0b000c28492451403550b1901e404000040701c0c1107900505200c2071403c1424081070340700c01511805480c60040b03640103400341c000d05258696004007640c080000e610201c80210341103004102c003505592003403a140f18a1003c43e0001c2c001140000d0840710071043c0000001c1350001c2c1003600f00c801111003040c40c54440307224007690640b1035983c1450b0b085d01d22178040300706e100d1b070040d0310744003468040c1c80415080c004162600303250b0703089090081c001001c40d020142e883e6a64142d081780140c01e50024100700c02404a40e124805a00501d10090b6465500c1c461035642c001a01d500300c8404009000400240f0007c0b00b0700082c20007000071900c0f0340010401602c0600d507100d030381050608120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 312608678 1250 312607428 312607433
    0xc03050405030a0e1903060f050714040e0615040f090b06030105090609041401020309010e16060f050c01111204020906040c0206160504260d0903020d0204020c0a0f060b031207 77
    0x582c0c060f94941c0c0780c60b40300013109100090980c40100039070081000101e001006018554000400c4001200707414041074541f41811900500b50f40c3d13207807141c010184414482154410901d5030030680050113494400c820b40c01006150384258806000302d919002d0802801030b06000c0c20581c00c008941a506540c50480819408080144441d1040d803960f80010708200b5003001d10450810100c00842d00c9141c042500c07402003072a42000541c80c461f24007a485200030300460141614440c1d6202c021192544000756420b420100f202c100342d54881d40302075a900410005002c1d800c1450401c18a0750504e4018440d0740d52020303000314065030800395849440ca400003941d507041001d006144282c001ca1040443c1d030f501807900880303140d4004414012480324695503132455030a84100346e4100b991003280941e030380045840029000074400c0c1c3c019000d45841c1d40034003080085401a54240002962050348188040000b00c4005941c0e628140e45810100030146140a00c2c4016038a0300c0482d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 312609928 1250 312608678 312608683
    0x20c0c0a06050903100905010e010903021b1203091014030c03040303050c03040b071107050a0b071a0112020f060f1c060906240c0f0302150c09010c060e010b0d060f0c03050405 77
    0x5017900c07154140c641202c101040000d601c414800c00740a4000c0203039a17150318001b51290724030010040107405100b5000403524041d580e40c40000501c60045203400403280610031000441c10b54070090010f5215441403010340f41000390b12032200802c2d01d80e40e9107030a150190481e83d000e0310641501c1c01c24000c01001545c9100e19941118107820000c12105c3d1280c23110f8603042c4507420070360b007128140d840040c1c00f465501c05000d209210301c601e0603221031000300d9000d4401007441008030a1340d0101441d0050b0500031100905508050b1145160000c18840c842681d4042140b00c2d682d00c400c0207000c8910640e1740b041e1400340046c1602440514503100040f0155035001104c0c15400c2c80004104030004e000d498241d080d50b40c04071b40955842c4540c10042e441c1c0c00415034003e0101c80c120001416941c08404a61001c0320586a030f01c1004146c1e15041c0040a40c494480d031700750768a00e4500e4507591040350307180c4420b118800216a24100050f914282c40404024200f854205002e120004201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 312611178 1250 312609928 312609943
    0x3060a020910180b0d0603060b01020c150904060b040b072a031403040302030a1a1501051c14181b0603180a02100c0b0702060601210207020301020c0c0a06050903 71
    0x691500914880111510420503d195030110010002c0010f80da50000c60b0741d017114017128068001080941c5048005984881001e5840c40e88101520580100001604080c1c070107075501500c0090301984401d44218a68080d80001010540c0450400c04108110b144120b01142120030035198841c0083c03c4c10448286010041c01352601842c00c406980301001074070010341c1c000f402c45c0c028801070f017810a8800707015510801c010780764400142255070400402d9008a1040e0340382c5240800300d0559003119014030048810321611514640c984807100142c007402001c009488101801d40810060b00c1d0401943c00d4961152052a28805983c2c0d000181c0c0d07803240ca040a145107240d50000400d0400070722100003940041404080001958044c1062800510a582c00100c540310300405a81c1c840301103070070030f0008400c0108540c0e088010314910b145682c0250000d820310a65600203800c1e600014180308469200841204161070080d42c4034005054904181d85050241408a52120308 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 312612428 1250 312611178 312611209
    0x90d0504140105090a1202120c0f010c060b10080108070f08031905040f0e100503031204140a0507031406130f02011d1e030f150103060504020a120302070503060a0209 73
    0x101009401e640d01400c115600c00c0001013142c0101a1180420900325482a800b83d01580d05c20740301d070410300c000003050403c1c0c400081015030000d41d64001180c0e5041041c000b140d040e5200c104034080c2d902c4111060745c022540d40c03a040c3c210341c140038000e4035011a991280a041d1090381080140403c04001c0f6489040150071000c05804564804e8591344190740c400c030311030980c05000180354266442c0540c020741c442c0282c0d0034125600c404150b40d90007010319010b502505280420009000702e85070500d51500e0109a90b0841c1407030b00e810b400c0c0030707031a401a2a0464401c0c0a005252428800c00360300ca025202001814001703a2102c104e400310402c002414807080b0307649001880c01070300d014103142e80c1c020008410400c12030000c40303800600d00070b2940a4402c984404014080219103071148601c81440549942e1a68440c40c01410019100741d070081d50f02e25000ca5406201068000c50070301a400900045141406162030003100030203401055206202840c0d40743d541032068803d154 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 312613678 1250 312612428 312612449
    0x306050f061b03040801090302010c03060509060d050c03150604140910020307210926070f141515091905310303140108060408030c1201031406090d0504 67
    0x205200c070341a0b00c9030303000d151030410303448045130000d032420054102030342140c4254001c5c04071040b500b40130380c20303a0306e14010103900c0a519030010b842030070103070041c1c01c203140100104c07101032030018082410401e03403116021184011608201c5142414090350607120455001c06605140c040c0100d07403508204104101c1c207980000105042a2160a004507503c4c22200001405038100c9514401445114000c481c03083c0f1800390f03651b01982044603041004041c440c06440e1019984e105000308020a004072040405141c502400346001c000700710307003030000300200c002a06056032002411854182840d03c0360b51702504007c0035850800426110b4014458003042e81d84695500e454002d03c0c242e0204006912403040c0c0b501d62040780143c4000500030b403400c00c0113020b005403c0024600c01d0103840015440000400c0c002020310303004680c08944820341e2410700d4140c1e0406001030100f89e009461302800b80d0070384036911005002d1140c202c81030800401d0107060906010308240100d11412500c030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 312614928 1250 312613678 312613687
    0x11030a050906130504060e010312020c01050301050103020f0d02040b03100b07030e01050c191209051c0308090717010b0f0d0b0103260304050708010e030a050306090402040b030118030f0306050f06 86
    0x2c0304500704460141c04014006d00480d81c40308038102c00e10009102c183c5400d0344a184070041e060011071a003e2030403060b504e091450f8200070066000e9030100c21007007a070840030070400c192070080d031010303001819409503055580d061960030101070043c80c1e0000c180302c4904221010010340c000d5880b030440b04017030a0003074590901c2c0180500700038a892104030007000e2a501c3c0341c01c00003a20344144801c020390f142e6100c11500c5005101188040c81c0791200481007800c3c003c03005c2806900e015038848049811100e040b9103400c001d01040a210800e098140c0d10b80320308500310700e00030184660245c3e0944220721000310f03d0720f07203019202c018400030341b0440306c5401000d00000b21880d01e440345041e04500c240e59091130b1901c0340c0d1703a01c041c2c03054011a51030400c0314982d140000c8201ca0941180e691058111f49400003041a03001024104030b038044c2c0c0e01c501c40c4045031801e00841700390714492020b01204d8501400d001d030004422030490000c25141c024240403035629a09041c003581010764080307848 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 312616178 1250 312614928 312614947
    0x6081c1206030f0312060906290c0d02070305010b09070e040507020f0a080c06090604050a1506090609020703021b3304121406010b03060f03012a11030a050906 70
    0x240501c2d0400703050070140590345014190010010900908003040800096949086650442e55140248420140d1a01c1400005811444240641c1582c03c003c20300e0031011045291802c1c900b40300d0310026801426007001480700c00c1c86000d1001d40203440141e003518003448028402c0010080440c401c2e0350700c402190300c061081200c051600b0f591000c13603120b00c10700d052000040c3c0200c6120708c0a4030034000000c421803804540c3d103008691050050a0f0880f02c0e075222540c10203001e480400b4541c0d251000202c0c4011070041c40d00600350700381e0041e907030700c4a402c009040c0b1040e0001300168900041c000c81150312215106116000092500081c01c091560b07020400a500d508400d1040e2000c40e000c681c00303085261214455108840044d805000c2da000a03844040c2440389801d01801800043c08904215540300b1000e00000c0c000960341144010240c160401018410900c48090040d044016002010030f044078081500541c1020482c0600400b18030406e118680070398404100c0114 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 312617428 1250 312616178 312616181
    0xb0705070801020406030b1f020303061c020d0305041511030a11010906060305030306030601080109080702100e030601083301063203041101050a200304090f0f06081c12 74
    0x1e402090002e5503034569030600103000d00103c200c081d01c212001c141640700c4460a400101801031160055401c0da500c010030020f42c8065083c02035420ba03411558500185da41700320700643c2902c2504d44a0b02d0302c1c10411003182021201040e88180705564a102e20400000000d4444003842031520405011000d00c0042c003500c4010b10041c44141008000b000700900400603501c29281641143ca150380e9460400782641c44044014180007010406403000d41059500713601516150300709030080484181c046403800c01d00f640002c0580d004460102d02520b5214810280700b00020f011020a01d90710518046000c4e06128000034415a880d001d11032020041c1944000c01500a00184201402e01013041a5000300c4088a4040c02031b90388009940c0510152074074090190307210850300311040c01d510303108440204005001d100900001590305090f004581070201d1040700440d00d00510580b020039140a504811034035048001c0822440c07400410354400101c1c5441c04540b04990107a0300300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 312618678 1250 312617428 312617443
    0x5030a030f05060a090c02010b0a030c090b0a0b030c03060f0904200102070506040e0a4212060509120a110c01020a0b07080a0f0e06101505070201050c0309180a14010f0b0705 76
    0x5400c2032b8500b000105200120300040f040741c445410900c10810408200a00d00c0c501d40602d0380f218500b800490388007010035001d96400a40a011310710f114552000196104100301e404490320083c8001c1e0881e118117045006082075020b00080514608042c0060403a000b140501e15514641e1000580a903800d17412161046e04c3c520041c15910003001d020340c000e85070b80d090703c0051415140b0361003102001070074100d040310300300c0303004140f01991a50740001610f005041e00d1161305c155070300c8a0030621203100801c4035601644070030700000103190f542424410010200e03070564014200f1100494141825a030f848011303464110100d03a1840441001407030640c1d141c0155514052170001e02d69000140c00c3e0040300c101e107001d1240780e0742e00c86e064001440d403070850b000180103004010065000742c0c007401040141805481c142040800442c851347e05190b042066500c6000c20f025408480e0712440015181d165180402581040314401000c1c80a01c114808007600161040500000740a107c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 312619928 1250 312618678 312618701
    0x17281e090c031211060603120d090f150f060504020306101815082e14150f041a0901230c01050f0105030d08040c0303031e020705030a030f05060a090c0201 68
    0x484a00d03501010003800c0190800044c0c440340f0440000c18a180390003e1503855080000c40d80e580350000031005076018003003100046030107404240c4030300000341404810350500e030643c0b10b000a200300c2c4d0200e00010382c5c04540c040c030300517441001071100c1c6480c0c07a082e02020514074142160140054990500c00801c564844007000c2c64503c40c1d481480d40c46145540100c400e04012a2405999406011540303461440c41c4d131100f07002c2108000c0f0441680d03000d078014000400c428801028808010702941c4500c4003010b05000000c1c01303005506901702842c50a010038441a403c05011000190108100400600038100b5140000500c040e046044445a50f1080c000340000d007000940c030440c0342c600b0f0180178840d01880300b610001c5841002894448e5070003010b008005499038030306070014119500074003102a4022030098103094140024a0828800d1008581c0c40900f400000c00f110188104400b04509010600c4030300d540f00340c48141518a90b41d40080c8030b0306411400e90040c620070046 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 312621178 1250 312619928 312619943
    0x10c0b0f04031205090c10180320030a110a060c0809210307050606010e04020a09210f030903030305061c020103050601030e0f06011a1c0c17281e090c03 67
    0x810045e003d001c151400d20746010360310b00c640c400c1001d1003501c41105110200c55401000383e002c0001c0b0720508051410040c3e000040500d4030103000209007004541ea000b5545012220081421800e001004400600061400e0844400380380d84004562160300301c0584030b030100d0700c085040025000251a011076820007103030f544007410316000344c49290031110240810f403d50341000843c14107000b0bc49071f03103611b80e50b100c44150a000c89060000302e62030242d2602c01d898024200060440c10500401c180a0303220340b50700d1417a40c90000e06655008080e58090180e13104c4e907802c150b90342c0044544e11542402c2c00300c0e40e541c4540c0124002c1110103120301251140c03029140741400085610390507580201c446c0f00d1480d01c490f0340301041d44640545007010f000f00200c03100c900c1300319900000c0c0b04d500900c0c01c0c6ea801550004060303600e4409079560200c134a444044040d580358602115000800d1140d02400140e40102d400300c0c0d180040900c14401c140c0340d100440c02c0201c50031509002d90b41c070907003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 312622428 1250 312621178 312621181
    0x8040614090c030c100e0d080d0603081b030a0801140d0c120b1e0f13060507050301180b0a0603180c060f09090b1302070827030c010c0b0f04031205 65
    0x207010303551905690014000d01608500d82100d00b0700e20300724140684991244204580e01d03105101e50380c00a141c0c05d0381d00c1d9800b44020307081281d081c0281c4009500410000340c6804c103040d900000800048649661640100544080550440909811200101c404a158492150214103000b500f0080107043d040d0b0b8801c04184a01140c52441409000c2c682c0000d0130b994038941030300b00038440349521020040000c001200f500d0300340006a4404540a101c801c1100b40707030744141c103443c01580e01c1c1d8080341c800701c01845401d5441407002d010143c11032003805000003400200300b515441c0c0c00b9590415882d455080da003005050b0362091540d5000d103160a0059503108001c00d03c1070500d00400010300c610000048240d1b59014490039064024001c80b00b229089082d28000e5002090407070302c00d442032040e4014110080000c01d4050021007111320301c004000c00300740c1004000b4050754180120000d105001c1001c8041c0140d110100c2403c0c22031507100c1e42426030316000110180c00c0154103240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 312623678 1250 312622428 312622441
    0x1e041719050a0306090504020d0209040203030c0321071814060c07080c182806120c0312020d050904020d090506070302070c0603090f060f1808180a0305070608040614 73
    0x20003005465200e50f02005000d840c0c850800036240c00b683e020354010840c0018601514002110541251004049a00d0880364907055404c40d000041c644220108504c0d14003603a070201d0040a501154500e0154100443c450031100b000310540644284009030209000c0c3c0e9444003011906040310400442c3d0f4a40d0341d4401c02c503690b2040c501ca45003e01400c804074021404104601400b030301d2103501c00260414134100d24a81101c0201403002416100c045c0011560ba400c1d0044025500524a91380b0740e504505001c8900c4070711240070000c6500c4100030915055000007580c0c1d070781a0454015950b07d915041e010003070300c040c010240c4540541e006008416401da170040c40705a11500c0034003103180d0382d0f9a041d811200402d00192030380e44d15000c05c00003d132590703101410619003c0301c0061040980c240000a82c000500225460b000024040151150f0708081a02c0d41104a440b903049504583e00d45450b03241c030384075503400c0c443c1d942c010608201e0150445c052103c601d920290b11440c0c401d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 312624928 1250 312623678 312623687
    0x50303010915050a030308060a030209181501050a0b0319181103120403151d0f0c090105010509011214070507150c0503150402040b18091e041719 64
    0x28070940c40304074502245480402d5105200c04215540200852141803641d01d0980d80d001c030040225a0264040c0c1004c40140e480e404843c0c01115680e0003004003900e82c1c2e9035185403080c04001000082140d80040103036a0b07401c85070105485402210301e89985a1204420008650f0014485036a00745419280c07507240810074155141c0c0503a076500d460918000505840b5514640c18402502c4108803d00118000b0b1945072261020b50800084565003140c00004c03c2104440345051a0404180081c10189c20002500d0049041b00c41c1062035140100180c8288a90340100e410b010303070064a41401001940444c5c040506002440e10702d1070320420083c0765038000360080f640101d03445000318240300b8502c20704e0080c10190310b455155486161140940a070420f0003da8403a0702044041380c101030140140240c200805403060a41c0350705c1081010000000b40b010891151084d03000c11700001e04c4040d6030b001a00101c0464103a2000704540000b07100d031210440c10806c14041480c41d05500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 312626178 1250 312624928 312624931
    0x1603020a02090f090c0405041a01060f1106010f03030e0d0c060504060807030509120f041d0a0507050313021c0210020717010e0a06050934060c0803270307050303 71
    0x202e96041d010350301c40078038000d05441615a0744150380f0400c1001100c2c02c03e64070450304140034814000d1020741d0140c0381c82c0d10340400d8010000240c000200e5600845d04200d21400010b424000b511031581048103c0d46810098880602005046401000c40d901c483e0303169103a180c0c00c094651806500d4401c0603005074068802e020006101c0f00001da5298428030519015a040b240544224000e000c201007054200f012114480d00f0100f200091000001e50814040f802d40c0046882518055038100201c1e90002d040d1401e00104008015040345501340220b2001d50484110100c6110104c4c000c018994520b40250001560300758500341540000741c4404646c2804000c0a020020048007405d0740d010703038104500f0b988200c2c070500000c0d03103a0300411380c0b001c1c00f50100c5000300d484012030f0f000c9400da8100700803007440c0844034020450b003c01e20b640203041c1d00e08140b1017030765a56a41c40f00c1480300070824080107162503050342c1d103400c0742c60500c9081c1d0b81c0b200440e500c0781618203056450f03520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 312627428 1250 312626178 312626183
    0x131d070f030608060403300911062a0114190f110f07110301020307050408060106020303010501080a0c02070519260718061d0441031603020a 62
    0x14201051119110b03008100c1940c4211001d411070ba1140e0340c043d14021501d9600b040d0040c0030340060349111102100724018100d0402002c5160491420140c560244c400d00d400e01810040205030610034400034a00844182c2041080d40711441c55809401800101d40c924203a101c0d030400d01412045554641d9020380c0360040c20000d80290301e1080085610020b00801c01c05d03406e0016942ca0400040581002401440380c007652241c2c00000030300726401210090003044020070b06010b24007080002e41d0141040d800210300e1541004006840031100404250f03096881e9010024040c0c801c0c850040201805800380030340880c040c01c280300c00915401202a1020812038890b514003020300c0480d078001186010b000900d05001e556000100c1d0503140450a58596400040c41c1ea180c590300c40d103541d140080a0714905007485c118070480c2e240040b9a10241080c4030000d5a0100000c1e2807501c81070104441ca50301088901050541c010204803a00e08055901202c051640109000c6407903071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 312628678 1250 312627428 312627437
    0x14040308160f05090315040506040b07080c0d020f09040903030605040e191b212f040b0406031707051203041a070e1f0305010f03020d0206131d07 64
    0x9442228500c0c202895495200019215400c42d15000b070107440140600003010302030301c0e000304882d1003544a0f98401e507012115540700100304000c2c000c0f4082c40c1070f0000c01600e8005031300d0428840081c07036801042124020654002050081e6540281c122a80c09101070030910185070a42006001800c8500c9218040e03401c00c4448420800042180078160a041394061004000c43e210508080c25000100340070008100c07000c244844001581e1560301d040c102941d0008141d4035003103802c070144a0f1241284402e41e01000f6800d04e000b50b0324584402d00b90380000380c40b4846070004010b41803a40c009454541c01a021a030046510340081034500d001c0c100303c0781c0070f40c031081d8144100d22048074043c00401a07490356488918103404003c1d00603850b4035014420000d9140010b80041003087c0d80c200c0503808802c0303044925010300429004010440516501070300d076401103001940111b8009202c0d0800003001c400c1c11040c8804803028010b10001a103140c0440c64520ba0145c8040d10881d0101c5d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 312629928 1250 312628678 312628681
    0x2090c0c06240d1e0516032108040203062e0303050c010b09011d06031c1d090115030213030c06090914040c06110a120e09100b0a0516050114040308 65
    0x908141440440c00c2d035114503c040d44c20b07107030301c408075507010000300803940d070b0003002c01000b109035458403080051401904125850140d12071140041071082c4044402e101c0e4840400c40036940c0428400c4e030002c64101c0d2940d00c6000c0346140d0140d0303000f0340c04c003080380170b24514048241940600501500c0c2850002000a0241242003052a100910500c1411001250b12044010042d0450341c0c220802400b02d80b0306080d2000c000400100700e58800000424005100c0946070410550b4a0880710540d585027095060220b080300c02e81500080005043e0000f0304c0c074035049140034902000b9604002c507005402c3c0c1720b28008001d00e020b4491265a14104030300100c02c02c0c0c941b58a603008a80c400c6070181e44900c5c0c05400d6821101800300011680501364032800814201c0c20b00403245825503880902200341107040145c080c4014041800d90b5014810511485407280c00300c90200100b81001c81d21051f0705800381d01d0414009000600070350801c450003075098062010140200d1080e10b41c444e00c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 312631178 1250 312629928 312630001
    0x1211090102010e060f0712060e04060504120c050303060613150915030c020a12050d0f02090109080a1101030e07090609021309150306020318190524010302090c0c06 72
    0x2121130507112480c2142c50240410981c41c0900d04100e02003845840124169030f6402c032400500d00201c60076508180c85a040100308504007a040d5a00d00d050f082c011036140701602c030543c2e2070000801d5240105000515004041e44070f140c00c0c00100701002002816034000100241014102d200348810341c610002085801402409004c03001c0c155903008200401d2207031200040162501c00c01824042c08100369094a6218012040e41d49d52450300965034160100c001030580303020f039000e040729400044240001541c0d0542240100a09290100d000417060700401c0c00c000d242d0740240c03019807a024001178841c0d059000303448414514114050741541d00c07105401900c0004200001d0020700900070f1000074829400b40d40c010a1090a200c18071070608000d614003010440315030011b00552201d41c003081003c001d01944103010b00d1840c054290807009021510b40103000c000d102d482e5000008064107030307a10075203544d20042c004881c1d4504202c1d170700d0074150407014400c400c40001c016004c0702 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 312632428 1250 312631178 312631183
    0x40f030f11030909071101050a0905070602120d02070201020f06071101050709030201050d0c052b050a0e03040308031312030e0c010207140d080403050102130603060503060f161211090102010e 84
    0x7580e0020002440c54a00b0140400498402c02070403c1c081c048180c0c6420384110003407140303602c140340d0f280300040c9000082c10035500e003e84a40c000811540100107103903446102c88103962240c0c2c950700340540c50b241c840c40140e080001a141815091046100304540300354007060220184180170300800c203946074080c00710742c950f0b0a804003a01040c010401e400b080c00d4175501000456206282c0b190030401550034404042c4801800240c443c1d01c0f42c040302c0c02c51000c030f10880750000c0b40032070104840d00044201c1510b034051840007810723410b004400110395242e030840c600c440300d52050071200d020791100760184c010030620551441c0741c0b0954000388904c1d400000c07040241d40d00b440100100900307020401c058808500e90490b51460140300020000340b00340081c116514080e82c0d0300d00d0580c00d0142c003c00b1a82c0035070120384079a11200c1800500c6c5001002c8941002c040400003802c10300342441074400030400d45402640030300d0907640d01d0f51005610f000e40f4a281099009001c0305409680c581e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 312633678 1250 312632428 312632447
    0xe040209030303071814010c03082802040f0503010e0d08040302031309480e09010b0a0210090f020d020609180105100519050a0c0c0905060f010804030905010302090a030b040f030f 79
    0x107011032300c5a584800442e010304d14056001c95640700c8242c44800a01155481c0b500180b070140c5610340100d03040c0400704041403160003814090b4001c2101071030310b2010640e070741524803005050000003008141454400d00865920316080007850382215035401c0301000601040c0750300b50b0900c1408000081c40003d0995440840ca100c131481145041990100070780080304e1842c40c020720030107140908064950f03100d0a4020030482c106941c84140d40600a070400300818611100d01e8508040b84001171041503005401540640301426a6840303072010541510607804190391091405030603030200443e680c03a05042c0c420a8407400b0718010190820740d10703400381c101036a203025140d66440340e03581d110307801808003400d052500040d07100954131100c0c400d076400c2d003017000050b8403141004242c0c03c0044411030404020b00e00a00300e49020b4400504250041c066035041540008200710140e440e030034840d0185402c400241d8103070030035261540380e81503250411030218040d5048420418014402c0e83d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 312634928 1250 312633678 312633719
    0x703030c06060902031005090a0603020301051501110a0506070f09120b04020a06051c0e0a0210020d170412231809060f090f040807140a030311040609060e0402090303030718 76
    0x200c1038181011f041203ca80d00041282502581c4c0f800000b003d0b0740c090096034003400c0c1d0315203190320b0140d52070001007407504211080405503224001010020b0341c005003a55101c0300c10b14000c0c45840c0c046d1070484e1240e00951101140c5440c17200d0380130900c001c41c40e0341ca000d14800c072003140707a450b5a01d4099a07980680c0900403003c2280c4c0070519140c4515030861444c0b00101006c0e10b5104485a0000301c2c0316161041201c01a0b00c0042040402c542202d131182803c00b1140000c0b8840c43c241ea42c03417001200e181e45640401100754640c00b103d22134050850300b440013040d005526015603100d04450f030904082c2035803207003000902080040c10280011180c180001c1c101d4140d558035101120000303000540101e4030714004100e4040420070440680317014804a04c003504012502d401d004003594003042100000040400c42044403641200b100411220a41048004a031100b40080c00074041d1000c815094000003040040c0303a980400604454181d004a01c902035440710541955900700e505078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 312636178 1250 312634928 312634951
    0xa030b10090909050a020603090703030e04020909011514041707050f011b03110a0b0609070801141203070b10180203010303050f0c0a020a15020f0609060a020a050c0703030c0606090203 81
    0xd10000042c0d0b082003080c58012400c80d91a002e0300d90200e1501d44c0215244816a0414141031007010341c000c0c0a080039075002c541c190b05080271040018000f09040c4900c40000e04420103507000035000f0615288171030440c0c0420707622a90fa50302008484015600c540c0b41d1401009000b241038605000b501140401c184c0d616002005025404d030f500ea500c0c00710030b4041c00b035051444804181c0030410f44040318442c0c28009a035050030310a1106556010700b01174284500c010043c4040d000d50b89000317408071400c07150a20700a03015400c050640c07150300d20140c0000004000c2100000101c540c3c5011142d0948140344d2034100d813444d0100300e010a00004000410410100d082d20220b100a4013000000310151012100d1aa0000344180c2d0341c1d40c020007820840103d01c025450301800f0304071544d480d980240001385842d940441c1c89040042a82035031907404203443c01c82030300c60301c1030314100b00b10303401110b003401c1c0c80c1c0c11b0207483e03603070f1050084500c2400c240001c10b00840600a880c003d582c607264 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 312637428 1250 312636178 312636197
    0x20414120a0303050912040602150717070e010309080d0b0a060503160e010302090315100f080a140321061302040e0711030c03130801060b0c060c07050a0b0403050a030b10 75
    0xc0480103808040d0610f1780078402e00c0781e03500d410b1711008001c00041c0281e0f00100340e07001c4203501081003188000c0000041c003e6000c0d912203030440701c041b4198861503510f4444c0c1d11950040c016030003800ba03610041d204c14000304520204480f80e03480031054050848850440c1d99403958129090b1004560b544941c1c0411915590058040c58500302c200c44141009403d005a40780031070714014a80c1c0b030500d6015190000d02400e0404a40c41d1005000e1008005000504180509548031500707880240290403004011928004c24401ea6070303801d82d481143d0b034169042c00b104c42070060007902d659100d600050384a240b881d02d10300c00c403000c881d0607900817507450f030354160240d074030641d074854046050100304000c01c0300302400e10060107081000910010150304212800d42160919040020f0904081140311003080c030000d01268030542159202e5520456490914105120b600d801407450781e410301171200b0950000c1c040c04503041156070400c8011401010041d020681c41e000300082020701d071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 312638678 1250 312637428 312637433
    0xc03030724050901020d0c05040b0909040c0801110d0c020712110d0501060801090c0f05150c01090c0b071b060e010c1a0c0702013c03091401020414120a 67
    0x1a640e54460307800360241103048110009070903200d003200e946010781d5000605050000240c490f0441c0585280380480c00c2a04000130a40144a511400d07440b411218001804101000644501406250300244010014015802041d40148400128140c180303030020301414070014031442201c0320190018242400e5840c0c3c00c40c816030b01d4012a42054800f034800000c5a82409075400506019000040c0c216480c00c1802c3c0400c1e403508250140c044010080099a455003400e0b0802c1c0901d1030211740ea11600000f4600401074660002c0400b054020001140405840036203503081c0a030860400392240c05c015a5003102503801014042030007400d401000b9407050284c0b6000c1032007821203100b81d1140001050003044220f900000b803010001d440070465074005001c91107904210821491a807040000c1c1303000c0c2083d880302d00088046410500c107014130907085048040d4210f028840e5120690074445d002c0d5115008800900038005001e05183c20680c113890f010b130600101420600d0b5007613 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 312639928 1250 312638678 312638693
    0x30905160302042301290d090c1d01032405010305070510020105011d060d0f03081909021305090709050103140f150a1505040518060121020d110604060f0215060117061302040e0f01080c030307 84
    0x448000950124100164901d0dc1c00740c4101c0f80614001c4000302035080c50032301008400900c10211004590503c401000035140c0b03030001c04100303200b445806050303594001c0411500d03610b5450181440781070700050310074590880101030280c20101441445154000024000d07070700c003414000d401001282c05001c514a20313600a6400070607180070358120995811680e015100c0070f03007050321a645884441803c10318100006002c21400c0409800c44d80c14101034806180c030001c0544d10040e40341e01c003a04070305000700d04d62406080d000704104154100700d00504200c4118503a030007004e00c1a6000030480c6014481c2c071003940d614039680000e20201a41c2407003c0c88004071811500d129001a1925442e034580c40074101501c030070b030703105a015200c42c030000707282501e199143c3c0c03000842e000c00c0c00702c96680001079001100001420788002d40320000451180107000c0e1528140c03030702c00b007804140f4495008046000e4020702e02880456604d540002d0748031a00030008907810fa004001c1040040c012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 312641178 1250 312639928 312639953
    0x70906031a030c091f030606090c080717040f150b030d050f09060d02040801050717070e060a050a09080f0a110f1f030905160302042301290d090c1d0103 67
    0x12170ba03051002001c0b628000c0217a26800444040392200c50500801d0428465a070030034449141030700c40c90601d450060803450765001c08800d410300000004080c0207203e10340d02641540940c1221103032400884100042c003201d00311a200e0700072107050202c04d034841e0042c4c603504c1c080010800d140100710380800807940e2003126050401502400f000603441000e120315442001c079902c560800400c0d5040403101c541005103408103021034081b000c01c00703440318000d07900069110f0500c20781c0c0e1910f201040d07a0b00034141d40030514912582807604501c1c1d001003556075140707106488142941c1c80e0740c0b0811880150101106812058010f2050005d0049070400c000d07043d594200000c0c005c0954507840d0412600b541da580d510500341d0001c10460810b881200c84145411281c0a11071a41d840f0300c541032001071045845802c0c0c2ea082c3c540c0170840070707030070f4003502500300d803103141d8030074401032800c025160124043d50030000c12000012401d0380c1c40f2260926070b5414000c081182c3c21a82c8490000c0345 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 312642428 1250 312641178 312641191
    0x11b080a18080111120c1e070816051e0105010b03061513060e090f0411090702010e060108010504110a0f05060d1d101a061603020312070906031a030c09 67
    0x80710100090984001e1159130040c64021004030344e100780b080d21500c0202e001400b41e0a01410800c003070003017480181c444000030b040c03040c80306903500d0341400c00395a14000d920f00c4001402c9444084010080005078050500303081c03042d00f490015041150600301c0d0802d10401c42c00407010070000c2c20350714010034000880340e0154802428015041d0a01e294101075810050105005810026492811021a41d807050240c03039410110301d4035503110403021108240c07041c0100000c00224880314003e4001d801040540801c440300e070b40e510848103020704804e6406560580001c00700150714205820243d00b9185440111000c00e807501c1c06010455100d00e48440c4800d54414209601a56002c22122449200401400d24541542450003107030b078a03055086840d6141c907982141519514251000500303a02c03001c030b81548050070143d046109150880d2920005101048601e44e00150a20280e840b141d5040011240c01d0342040d0a414602054591580c01807880406d20300e811041282d0141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 312643678 1250 312642428 312642467
    0xc07020604150201060618151416030509091006020a031d090403050a0923060c15090a05070503160315110d06050312070f02060a0201090203100b011b080a 68
    0x40d65005008a2841003050b4840141d440e0442004002e6100c00c2c0650011f0801300c0761150503140180d01340fa40d50011840b00c2c103001074078000003007684001c800d548141400900000201d421858000c180b80e101a003c140b01d095100c01040300d404000c0e50480603204207400030700341c00500d07803019100f01110315080740007141e800c01c03120031644039029485d0046110b42c4036281c03515100d10024184810750b0700103c1010042d00101801c0004640d0300d18003040e4165000c0e07594845d140c0da1142820020f100303510009952409010710300d6000100a02c01600800a80701c1a68442d4101612004003603a0030143c41e52203101880451580185007002071200e10000401100351003854526400c14806041801d9445804014604080c0003855a400100648520340382c6d207541c8240d240070025001901440010032003100081c000d6104405490700242120664145416100050094212184c0c0022907103404651107428030600c1c640e1443c2d2000340541001440c0c50201d481c1c260748949043d054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 312644928 1250 312643678 312643687
    0x30609041103121209060c0405061608041410020f0307030806040905060109051e1905040c0308030f0a0b04020c15150603090f250e070c1209030b060604030b0c070206 73
    0x340e80c200914035403220001101901c8044d00118803245010041074004603400080411a041c2106011070382075074030440e240c070f48810b072009414180c41d000200c0180b0401c80040c0100b8000903003151186442c004840441c00300391000f03c100d0300d6881d0b1040d180e1160b8420701c00340c000680280500765001ea4081c000040040940c0c4649180c95400e03440b14048542d110244920407078103500700c2001c1d1015152118407401c04281c00388091201c01d00c4601015680c40c0810300300202c50300d8510007107402140090b200c1c10108081006d0200542e402e0f4071091a0020105803070034240243c60022042001078503100b46980c10414042d20020060944440b840007a50a02e0b5511300245000c0d0701b1800003880c0040d80080b0041ca010304803103074610080000d080d01074100030850b500000ba203a8110003a9540d440d180801d41c0c2c44043d40710300400d13034260000800c0b2000e03070140560044070701900c3e0710400c80e2a0403082c85000d10850102900d5240420009040460250002d10740031303201030038107440c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 312646178 1250 312644928 312644963
    0x120312020912150708090109020a03140f10020a080f06220e0a0305090a0609030b0106110307020a120201080601030b0d0303020903030f0412030807020727060b030907061403070503060904 82
    0x80030a840c500f00c2e100d00048003030116440d4803401c0d05500081c800b008100c0380c01ca42d000100c8401991100621022542030310f2040c908050103221915280f1104035064196840a103101a421090305800042c003410002a0341d042c2c0c1041c00c1d4012800980601c0710541c10424507440c0610707090348004d14544450303611500040c108081e0350b882e40255281525440082c0412800b1186179000ca8100400c0380c2090000c11140013032541150860b00b0300c10030b5620320783e803103504500a095000c1d620401c001c00001c2d4800c441160210f040b803003680e0b1001240e80c0c0400540c11110007000403500000084081c000081c041d41c028035408a00408070390409a81910004c2e43e41e20940100455000300341c600820181c1021003280c103c0142e0000c1c0000c507080203451240c10b441c41c01003994030095040200c89640c5513a01c640003610107001d078240e40c0d14007401420340d286000d11a080c00110342d80c1d00413010307030281010399004980564800b403545c0c0344c0808212021201a20031b42d00a08500c010090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 312647428 1250 312646178 312646183
    0x2071103030a091e1505180310020301090f0603032c090c0c120901020303220b010303020d090b07020d03140408100c080a0b03060106050a11010612020406120312020912 74
    0x2445400c3d0f81c554008078100200007911940358907001400d4041e0310402d1002030128601e080400040d0329003d40c54081ca03541c42141c3c0951606407a4041c011110205513040d01d680007141641c10340b48017070182d40000c0d001c1c5000c40300c4500c4064000344090144560a00c1c02e021880949041480c030064400498000a0701103441a22800301a500000c2e605800301000e004e06d400f1700c0c0307403080341500b030000b9200040d48a2200416803201e400c3c1d845107404406044020410f41c1540181a50300550b0312860003a40e51060105d121001c247c2c16a80003d001850340d0880d000c1d1613001d05041c140b90308540c1c0c00e58640d41c0c0401000780c0c480042c0000302e8100020000b13900401030501c00403c00f4800104013a10084028059408003414010080860349002411504645031454101d0b40c0342800b5000321740240b201c0391a281c4075400c140c03000a118001c02c00781001c1d50300071038040050303654540f120080c80c101044000e003c10328402d1007681000381c0390301601c070700040508155540010540b1590 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 312648678 1250 312647428 312647437
    0xf0608030c100b0d03120902040f050901090309080307150b040209030a050c0f0a0e0f071e0e100305040b0a020901020a1a0a0501090203060607080c010b0a03120206071803060207110303 81
    0x1030340c82d0300005180100c06814002c04035240d20a0b82c0307490408005850040c605000703089034481c080d0300c0b00b00b140210740307a650082c10340d1290f00d42d0420650500c074200074060100300d4404d0f400100f54035800720710308802104a51205078402d45200e0084601110100038100303d000c800c2e8491f50901c8022519141071000700c440a1054000c0c00d10f0f080140200a840b800e0502d00030b003d0801d40100344032250b0300090043e00010140122a80b958841504484241f803001011000740a4810b4502005801c0030200750903002c102ca002c502c12a808504800b01c034000c0f20041d05843c207000c041101e030b065550044c1a120010b105441071a042e584565030f400803039241020001d481c150420002012901c140742c09003501c1c501c258910308110000803402c3c0221075014040039000110b40c0c0c00d000d02540120340c40600584001e480c50760300d0400350401c40d144110800580950400203584501c1400b003200802a610300d24084c8608585440d030094000d00000c031a200b5000412440d250380400252 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 312649928 1250 312648678 312648697
    0x203180a12050307050105070311090d020d020619080c0a08180c1809060a15140105070605070c050f24070203070605010806090d0201050115050f0412060b0a061b03030f060803 77
    0x10f40d82d07074031149002c508440c001008079041614010140191601680072160075640031100302c0f003014481c4c000a180051035890084d800b0358005220400b000c0d10400c40034198000e5140c0004039511120001d8017031045403205000a1400d80c0002c607148001000405400e012908451950a6200205200b02c0d810b4000218071690340d020480124820868207510070f07880c90f0140850340d051041032007409007038040d02580d0016180f0104150340311f07200b0745613180d40040050280e41441d98002e0000382c042c50b81980c180c0113900b500f46042d980040c001490042444a44c15010360a415406101d200940b0f1002180020860700c1c001c64170b280140b9000e030000c1006400c0700e00b00540c03000e160030f000d400362800b03590501e001084000c003042d0720300300800003600b0420750310ba080c01c2e41403941d441541c00131040c00b1380c0f4098200601c00700c0ea0100b0034801041d40d205880c0d0340c84010541d241207007180e0282c40c00084c81940c00000c0d1190300a0201c1c00e40000c030104055440c0c48100f402d503000b25220 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 312651178 1250 312649928 312649933
    0x20703060b18040602091c083007050904090602070615080a1a2a09240a030b0a1a0c070b09060403060e191a0601020d0203180a1205 58
    0x50061020a200d22180c401080b603259510550940d461080c41c4401000a0109a03010400c6495616a59450a2003070400d41344207603480d00301e150094554008180e103843c8903080a2040755402a880000b054401c0d003040410708a5031240d5040724903038801201c8030340044c0c640b02c070030300003580a00140a00c907115a00220f244d10810300d4100c03580e00254407111007507111244020104601900305000c03144d41b0300003038105942c0c040107150700c031383c8240214035040c506030148100101c00d140a4010320000310340d00340403038412007078913101e400c81c4111010700003000304070ba84202802a88041c5082c030015007407100842e69070302007203610f1340b100d0600d5100940009440400319828404800a040c1a0528a04040040c408903541d405107000c0242000c0d41d42c000100d82171030800c24100b07814101642c1d021219038600d840186024417240d42c510152481000c11001e60010401d0398004003242c1c011400e21081401901c034400c0c20010071600200304e01d0022030302885503005101c58030301a500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 312652428 1250 312651178 312651193
    0x5190f0206210f06010f0c05070806010e0115090605040e060409020312070312060e071404090c0518040c1b060902060403050c0a120f2301050a1d210c07080d02 70
    0x52224411070040000e0f04101d208010060240c0e0414000030f20252649030a615246861805625040d0707190002503c0d0310032200000b4140b880c41290506075940000801601c1d52078010036510a00103001d0200400d806200900c004030410941c1503104800601c0031901c10341c513401007801c050750181080e07600f00000805409140e0840c02c410701044400004001252405000039000300020389440200b20b0300c3c0d0800e0740041d4122041c1e030050241c02c031b0200200122410040c01070352103034807030500f00400044158407914082c854951403940e2030703c464010746c3d2811600ca40c50000508112015030351000700001680b2850007510213103124600601d8007400001c10400306080542c04840c2e0040c0d0b4080e5480000e50038500004a0b0344e200b05101e20740e6101d03034101d0b41e983c41211140102d5610b488200011149031340c20944150020540010b1900d260703403102510340807150407400d6003e000b04520340400810f00003d02200c0d68550a43d25010f072100c4105082500340f0000500580c00140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 312653678 1250 312652428 312652477
    0x9011b09061704050c010c0f0503032d150907090f090221090c01080a1d0c090c0c061302010504050303040b180904030e13060b0a021e070305190f0206 66
    0xa0303042180d120505080030300d03443c1035510107a4038814500d410341009001d0506a0800500f9410f07501c1c040d6001c0252512031070300c00c40003000c2d12464104903042c1c901c00071020900c80e12483c0c0207800b80311001481c803000441e0605004c1201c201405100c200109843e002900c0c007500071503240640031640025954a66041040c0200c1000202c455203a411080c1130094069001401c41858070080c2468174280c1e03580b103640c00c0207060803020221200a050414280c250002c1182945010126040e540c182c4403180b41d001d141c000d65041d605541c0c0310718085000c5001c2416038998203032051518501d829100e101003800c580160380103c801c04804611350071401c49005100305c0d10384094512903000d18054070004c02d0041070900550080c50701120090f140740d9036800c000040e20002001c01d40d00c4500b40802503585500320742c050b20f0101680001e802c0b981e0046225000c0743d8004001703054140c4011080c0c941d242e0440002c0360350031118a040310060320f076240034006105106210302024070150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 312654928 1250 312653678 312653687
    0xc04021b070501050c07090c050f04060c021e0d0201080a0e03120702010608010b090c0315030f0a0209090a0c0b030727170d0516061118011107080304030b09011b0906 73
    0x60b005641801810721110180980004d80e800c00c88400d100d0100380e900f020300050312039104415042d00018130000340855851f80050280e11254402d80740320b003e07400303113031100c00500c1800015180e0007200b5540c1c99015600c5000443d4100c0450400080c1450b60b4414481c9940c0c48250004000e0400d0300c01c001304281c081c8108401000044006c0c020159a02c00150940c24001c01c80c003114000400843da18484480b1074108510028080340c0d520544500000d540f2041c100c0100c0c401c82c1c2010014082c0300c001b150707400b05503600c241d1a6089a09100a01c8000d40006161004002c43c61080444071600c0324500800046c11080540b00c41d828400321100059219126038040d0340440b0f03007407115690160031160011019035507a00c0100040c0b50080140142000c000b0889101266084840c4504040000500b60980758203104160380d0218688840252141540c2341d0410300041011507807002c4440e0780509020000100350f004890a926029003461240c000101c402d201400060b402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 312656178 1250 312654928 312654943
    0x60112060f05161e02030f0d0b090c03060a0f05030a032105070906120c02061b070614060f01080f0a051e040f050f190f1703010e060103050a0203090616020c04021b 72
    0x4699180d411380400310041c1da00e110300b855100c400076000420720030b80e102d9a40002035903d0014008140f50820070028001500141e4140388984042e010000e541101e003c1d00074100c0794080c010f4201107640341c0342030356000d22400c0039101a4180359040383d0302c4030451007424890641911171280103420004010f24500b1101500d110780c5140070819200c1d6500020500da10428180d00000400d280001b0309a19000f661401410310342460f103142d881d282c5c0c507059030348a668252480c0c2c0d1724001b19401150025010b03a146000c4148c0c00780030030001c800a41109a02c4440329003aa107542d1003081240303c1030241110242c6200d24100b142d001048030074406902c1100d801001860034100790000c402603028541130080c2440f40c01c8100008002d42c00d03244854495405804a4507907a48044060304018102e800c1d0740041c3c90700c40041c6140e0342c0c6200362801032860074000c050700c0d82c501408809200b0790b101d80740250320880000300e40399640c0e40000c0842400a0403803060200030f65540074134080c04c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 312657428 1250 312656178 312656207
    0x30c0b07051e0a12090f080102071a040209070503040606121a0a1505190b03040318080303073005190b0a030302030f0d0b04020415020c0111060112060f0516 69
    0x1015440b10b2403200c0c00140e190704040d000010756016600204003601c03080e180740d004c0c541d000d0649800003200101940a03058150280c41c0c0c00341d88450341c004140c1c1224084400035401a880004a00003d1056000e180e01030710440000800e581ca13a0101719a00901c10800c903203007120440709034046522221041d0300140c002100f400501c001c3ea0300f1280002c00c9005150290101c0e41e4046440000c4070340000040940480c21580ca050509008000250544c0c0c0080d003003d40c8a030001e030b00f41002080300e100707580356a03590b103181503400c140744405480181d1907040d06a80c1d211240d402200d5124040c0102071118401c44195140381c81c500944031140303201d62044420090400110fa004000c44424a40780b41905581d08600500c61000345240c0e50407a4006202280105000c50f03c1100e4a2403a1025001c9801c14400800116190800c00c0c03804c2c0c01a41210004000c0c42e08000405040f25100307550120b48804009030035000c540d4115451507224030884c0281e441681c000c50300c03088041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 312658678 1250 312657428 312657463
    0xf06041404110402090a0306140619050a090207031106010e0a0c050418051e010e10050d0f02120a02150a110a03020303040308151e15091c0c030c0b0705 67
    0xa85520740700d6050080b1034000c0c2c040c03070300094013a0099590881c1300d000b6503400b00040110000310b146000d018402101c2d0382d80241c030000c0424540c0510310b200c0c401260300042180c4900307418040f40c00065001503030308809108407040c1144c402041400341d0350182c00e98001017036240c6443d43c0a5400d56400c49064002c1c44000c00090041c450002c00c540000600300c0d1012031291690742e00c841060f01c1d075031040c0c00e10740001c2001080c0c0220510b501e60080040c04544801c584d122001c200c10301c05250030040c1b40446070402040142402c04c00a0300d0004480300707448403081150080380b00c5031560340403910003000005989000301d41003c5031a1811506200610b51000165800b9684e844064805818030403d6000075402811505980748195406800c48a400d25114643d000d00e8059118051090344d468034100003401181c03041e03a440c410010720b44c26498060b0a4401c5040d0324410040e40c4a044062000c008686034044100040045203401da9480e002802c015042032003500000d110b04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 312659928 1250 312658678 312658681
    0x3060e060702071d011205030c030f0306010305070e03101505030304140a0603060e0114040209220b0907022a040e0610090b0f1314390a0f09030b0f060414 68
    0x120904c50748070305484881803400001740071420414514092040d0320b2140c4c1c4000942075040e0030300000a1402010281c2f82802a80caa008080e20500c03200d4030140c1d0164000300c101c540d81001608140a079240f10b1020442c81a1101d010a0850340142c10107803000700011038900345810101c00d0313038000f070100d80350070002c403801c0c00c800381800001885154101c500035a0080c84a58807a4100c4100d03070030082170368141c0ba03111820b00e00008510703240c80002c9841c0c44002d18103410440d410300d1041d015540903042050f100c152014a05e6030118140704060629030000d80340e80c031240b14a00707086c580c046c010902032038070200d22040c001032508000103c0d0306080785e022359500d4001013a011801e0458504001c003401d089800000d003900e088518a40c041c900a006003620f1200b80c00b5961101d401000185071410551022070255000112190312000c201024015129100704010104903103802c04100350340341c80d50965608180c60b981041140c01080c04054502031086040b0600c10851a0055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 312661178 1250 312659928 312659969
    0x80706081005060a1d0418050d1706061e030403090e07030b130c0c0b0f090c04021309050c0c0102070b07030c0e030d18030609060b04141302130603060e06070207 71
    0x314001d640004d8240140c0856039480102c0c1c0f210480c0d85540c000d0030400c611a500081c005800385801819511170080070a82c181c2644100e80a01c00903170408507540742070b2681130a0004680c0401b032055400c03c1041e80e007803683c1e0010300003580100e010780d071210b501605010b040c0c540e55901905480506103400d0400d03000392541c080d040d0004031460300010f030b002051102541d403a0003450000300341d400c50790304001e182c8a19404140c01042d16400b121091380c84041400100c0c403070100091081d16004401b0407420300e080d00501d0313100d1207030b21a403824440c101c40003e003a0f030803800f81224003094240802440c59418458410000110318040d0314400c0c990001c84e40382d46444111801704440c5046480d501480e1039901801507501100030040d18080303044c1080280440906140300d41d0503d0009075840310404082c1e0300422405081080840c480e070300700702e000558080803042d9140c80754000804101107120760341400e060780e005402980741100d0006d003810b80c030f5040366083c0b50001814000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 312662428 1250 312661178 312661189
    0x10f020309100b030706142a0d111204030215070b0703020703080601080103020607030e0406080318040506060403020901090b0d140c090619050904050705151b1b0f010e030106080706081005 83
    0x1c08100b0142503599800c0b84a4044030400745c1036118504c1980090f8000910290018450f040501c00340d59118040030402b030318640307490650000c400c0b5520203000c24000351902102041410b0484d40c58030b4500071469039118510003080341e156020a030b000c07908509268010544a510180034a0702d503203551305650001d4400c0c0a081000380070422000e0000740d464446500900c050202e0070100d984448500306403070401c55071003585500840c28403021820504188013501c007038030740c01840c90b4000d0382491403407001448505c482da83c0c05a10b0302e03540e2021420311550004403c20364005840d03c1d540c1170007400740c80400500502e0003030800c400e80c2d60f00d454010440740709541d03080750580c180e41c8070360900e24a0040d054101c02d2740300f40702d0014a0209404880100074000d842d0355420030708101e0001c0e05441d0544595001122045184030000603e4640c05c040300c0c1030b2050401c521055107190100b400c4903c2a0040d0f0302c1b0b60320102c000d000494000c4d2245030b000818a0011100f0b40c1010041351 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 312663678 1250 312662428 312662447
    0x4060909140f070e040b361204080d0804050c0d0807060513030f0c031112040501110102070305070210120606050a020f030705210408030a0504090f05040b01060e03010f020309100b030706 82
    0x81c0b01b83c45100218412070140e0556000e540703400f01c0204600241c107940c041c401c1500c041a1640e0b4412120340f034521031030aa00703503000c803a0800003500b02c80011040640c0e0925000304200c1d0640100319001c141e942e944055a01c0407800b50081c10785401041c070700041200c80182c0350b0040303000104190b100081e03001c5001c0300300d80300503e0301c60440320b56860195561049201c3c2410365004c0e1302281c1c141145464064030880f00240c5c1ea00d480721100660f4a4201d1092034000350000f001000040094180440007003003198061625105240c4403200000445441d03400400c00940000344451074540e0402c1410340c0d0702c203c40055403030100320340c0d50740d552040010042c0503240c440c0740f603a0950704c3d141e50568008144a1017520794030a14090004c09541c01070181c900303114503124844a440c1c03110f110f00351007180c2c82002845142d0a02070280c0d2031210000b0440e0303041d926442044101509400514003480d02e4070300806145442111680c06d4032940c40501f030080c0c2c080402040f010760b0201c10107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 312664928 1250 312663678 312663683
    0x1270b010302100c02030114150108010602101a1c0203010c0314010e06060c03030a0c0f0f080708090f010c0203070c050f010c060513021f020d030501140f04060909140f070e04 77
    0x5246840229509981c0c1ca04d0400010398554a0205050400301c0b000d6841403082040c00d04500d50407444200550300000280211001a802a00f070500100d8256008c4440c2d0305c0ca13000e01001036210131740000c0341542d5503102120200096009403007141001d0103007104c050075070b040c2031103809013400c00302e4502201446100f000745040d201040d400d80764039003101e211410000c00c0d03e90340d1800540050150010042c0b0b040052002801c1d1255680300e504841212503030380c0c0d9601c10070b481d0340e43d04a41c0002c019041d242030f0b0055101c50089000c09201d240d8240f581354003d15292001814414000c0d000d5034030040c06021340c280c0469150307900c0401084010b40c0300d41c00240503202d0341c001180c10b03114644000e4024020b01e6400200c2c503040c4c81136240c2880301ea400ca030810350515a049040e54409c0c41007511004400b9500042c624101d030b240040f0850260001918a070340d40ca884081d80d0400da000c1d5015441e100d810342007480b050100c0c83c0030380600d0004043c280c0c50081981c02c6240d008001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 312666178 1250 312664928 312664939
    0x11d04050a021303050f06010515030403180e0114090c181e0409081c0e12070602192a0209010b090303090307060e0a08071a07032001270b010302 64
    0x303502050254141c62000540f840c65988035a01d0307182c025a54183e48400d4201c1c0e20440c1c0000130f1f02d14003440303440700c10840c40070308038115102e45d40e007a942c0c010710000b4000d01c00020a004903031114604040b50081183d406200d180b45000360500c032111a01a265007005a01040a102003088505054244160646404004074004200e61241c140c0b10340c5040e0307225041414000c00e00841001400740c203c3c2e035020782c115500401006030220780c04e11011814a4201c800c900340300c80c41032000340050030b028410252629000729100c1c17840303100490242010540f602101d0140039030003c00050000341d601d064031001e4800f90002002103805101c2c00c001aa0000b80040c02c0c0d840c14010740d0110040034084441041d141c5401600104911241d14006c1c0b000c28070009903c1da0002d0f02e00216030700d048512484003d01e00b41c554090740080801c1d41801911452043e114081c40d07060820400054000500a00c1d03a200d0000e0a018094401e0307128094a9100340200310b0304e41c641030469904654 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 312667428 1250 312666178 312666181
    0x90804050a0803040807031b0b040603090308070302070b010e0718081b0a030c15090503150403110a030509060906130e0613020a02030a0f02010605031501030c0f18150302091e06011d0405 82
    0x20000c062030701ca400449c40300c4004100003c9a035055081050310b68030940f00c03c0c0003039a5040089089004829014080c11601c200400c42048a07405440c4c0003155440c1185014486444e660441d04503644144403940c40750030340c002150000c80460041e0f00d4200c1e2243d01c40b07450350311155031810890050110030341d600081030301e28500482c0c14038001c03c4042c0941d9060303000c42d00c02c40580364084a05401040c3c0340d0000c0011001c020441d02c20f0b055168071401d05155004043c400c603a0050740030b07180c00040405c40c441c08030701c440840c08002d20500703426032078500d807107820701004418055150b801a4018044159066004003d8a862140903d04003e00c0383e46120101c2c0540501c1d44402d03014012812034810144040008038142d034040d6040c1110b40340d40c2c12020055810134401c8100d814620140f061051420750000955543c41c0701c0701c500100c0d12900000c2500c08150b90b0450041c0010f44900c000e900401d464651060300ad09003c0302900c0b00c880c0b01020f66140c420524462a034a50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 312668678 1250 312667428 312667463
    0x10b0603040c0303031e0f0f0c140a0516050f1011090114032505040306060b0a0509190312030902011d03120a0201020d0207050c13021303060c020f01090804050a080304080703 77
    0x39003e00603640040d0a10805007c0c601e8030006040580c03200d4003140c10f028203200058020286500111144071200740340c0000c881d400c46154000310035444c07046408441010106408010345003418104402600344180b2103131192044492607a03006c860b55a0a00c403001403603821a004442405030f44202a540f580c441680800c80103401c0c8411103100d0008001d030f0211a03015000e44103480c0300d0b86017000025105d00101045019102030800021741c2008961241e040030034541007074180c40c0e00754841990f02c0303a4400b181d2020a08c030700b0000940d240300340700940da4444080601c01280240d03c08985000a000c00d8480086910081125000140c42d0211500c01d60480e42c942c0e032050030442d221307009441c000e5245c1c00b68804491003210045107492040d00c4510071250800f004556994100e40303550388440240a00d581100150b014000d54900819804c2c024001d416220f000c0b840d40e036504110404c071600540740c00006060b4030030b0006010b035080c0001c060003580d030040c204010110000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 312669928 1250 312668678 312668711
    0x60e0a05040f0f051501020c0301021801031e090501090c0b0c070303050a052a010507140304060b04020408100b040c0903030212130f030b0403030b0603150f0f0a17010b0603040c030303 81
    0x20003c00c202c24a0304007009040c0545111507504200d003642924000c540c0c1c90101402e071700030150b107072030f1540d1490007c10700c41d802980682640c2d0111140000074009400050040720390410043d6403594460210300c0c2008130f144181c1c0040c0c08076a0b00542801100ba407440e580c1e0703426010040a101002500314080c0d4014010b442c005014100100450311441070012422000021040742541c00c09011925250081c00050001305d0420380c071a0455846455981c080c10803100d000b03811582c204804a884c00c02400f01e008141c141c1800032a9a0940070280000c0350381c0e00342074804002c0300c91401e000107a07000c2000c41600a00542d03e5483d40c606080190789001168480402c0003c201400000c1040c3e010550340300328000c0d1002c1198040c02c4050001c60710040324aa0040c81007040540918a042c1c0d400d01c40171031001d0000c00310b050000002c00c4445c8400c3d044141d00b40d2442c1044c050109090182c6c00d00144140c030100d09609040d5a4010542807902004041c15140c2e20a030000080f00e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 312671178 1250 312669928 312669941
    0x5040821090301020a090e0c07122d1808010b0d0b1012030f021506060d09050f010501080703050c10210f140403230a030e010908040e070801060e0a05040f 68
    0x2d00031540c0350204403000d810748010303100300f01017401c2e080c001682d4880d0100a6500242d04007c5441d11503040e810101c2d8030221081ca2158211902c000c0d180382a50110400c130740d000ca03c0d0712500301d003003030030b05a0080f01700c031691102c0b48580c1002d0101d0950384038000e024039219403000e202c4d205038481e19000c0c40900016001064691030821840051550121000c0100c8440d07400b1f41c4c0400c0043c0600d040c0c1060104d4503942c0090041004101108059004500d41c5005c6c50a0300c2000358220b4415082d11001e07840174031240e100300400c0c030a00009111840034420100c80100d034401901002030210594400c039a00c5180ca000910300c1003550795000040c8d0b20b00713645810032154170043c00701c010308001941c05074001040d000c44031742d9000301105008802013a6001540c10152610030171005014030030720400f0030b5500c0301594000907107004050409060319a450000700e01d4445002086000d05034401020081c04540c103220a4031450354040903190140c1d030218a110601f40c00300d000d043c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 312672428 1250 312671178 312671197
    0xc030809210c0a050109031713022b0c03030503160801140415090c0306150f021e0106031a040303051605250f05061005040e06010e1f060809060705040821 68
    0x80042c1003041544c00801104040700e11400c02c4903a480d0b03410244244101100c000b9006407500c5034044a902d009104201c40203918be2a842c20110241c2e500001d0240c254011808914003009120600034600c0101c1e200264510b42801c0ca58540a0842c858001c4811100c0c0126902c90f4a9030300b11703608114000250000c402c0038000e588070b1410050092109100306104411101e0200c031b07032039101e290401c08464080d40108458400c484c000e01490403052400c0f0120b41d82e66200000045035100060070215400300c16400d00c0c0b030a8103016080d5400140228100140e100044001c1900001a12003003441c10481c119415910b800380d10045900c410041c10f00e401b41102d8000f0030070002680c0b8411030511940900c80703540c0744140020707155141c81840076500114010f0081d00040e04059070f004c1c81c840100d07078064020380d01280c031424180c2c1114000031103400c20000729a00400c00f1680000240c44c04610701850481c450b501e0b00c000b0209005174001c50112501030481140c10b80d007441a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 312673678 1250 312672428 312672431
    0x20d0203010e0f07090c030605090f1005030d03091209050307030803070302120108030a02010e060129040b070b01030506010b070f12020a020a060302070501051311120f0d0c030809210c0a0501 84
    0x74007260515a0f101132611842040d20709145071005c8040c800d02030f00c001c4607405801030429880300a4403040b040e078000d00c3e151035201405400205943e0800c410390320303d013154800159a060a0030015250340104542c801407007400e540800440d1400203c290440f5041440a5129119000101d02070721a100c510f4046407907940001c50012000300041c400030b05990020042c00e00c51003906901c402007441145c100201a02d00d8041d003c081ca43c000c0d0740c0a107540c2c10f00b0700d01a1160ba02c0170407908042c605030f920302115001481009002c100c441d000d848080049030401a080ea55006044560354008181800300d0b00c1c142c20442c000c10540c40350540c001c020b446000e0b100c58005000350032280d4107980369824100070411807403000c00700b07006047c0c01070144080390050b00c2c00e0010703209414003201420b110301d0403000380114040c00741e1014100d00e95903881d1a91002d041c01030510300b0150242d151074224140c2c0700e40d94000c4038103084120700b8980c405a103d80c107003040c603400e00d40304003070181a65 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 312674928 1250 312673678 312673693
    0xb060d080c01090309050907110601050607061b05030906010b0f03040f0614010306020a020d03060506041a070f05010b0a0815161710080f03070305070b04060204080a0c150309020904020d0203010e 86
    0x1503003180c078980c10b1b2601540d26501943e2800d82c220b50b0480f12030140011500148018001801d000000701a1603018650125610204034801d4500407568a0780c40c3c0000d8010017440030840f000c3c030071240140045c04616082c02c19040307800d00e03c0e02c00540000c0030959108051010001940c10a9545603401910f400040d81d4034100301e00a50b0209040c0001800b0f4009003028a9000340303c0c040644034003404103424036051804841c0c0280d002c5401c82d070940c0c0b0500503a00002e8103400d005000c1c40c8101c0003c119150040d050041010041d040001036400140d400c484c6000f1000085a0241441d80d20400c2203490800035125450300d0411002150349680801001240d0503200741c08035200c4030122a40540100c2d103442c0c43c0d0284c004010001a801c101440c0071400c982c0c02c560704203018240052034a9034422180c0d1a10000c01c800301c1d00c809a000003080014a05004019903812904050001c0301642c2c0c001600960004c200904c244103420804056490940c001c40f103c45015084480c02d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 312676178 1250 312674928 312674933
    0x30109030216051207120302011d0703020306100308120a0608030f04050316240203041212030b060408070504090f0609030c0c080a0b07030b1503010f0f080a0b060d080c0109 76
    0x5520b0800440a201a041800001c950401207200c25001d005003024240640c1441ca040301e0740401c0080c00d40031036486a504801807590400115440400e0b04000e05015155105240c102a002041d4082503c0c602504201088200080350b504524050840720303503980744942c840040c6a5030300003034611301c00840d00d10120100c4000501c141e071300c01c03421030f4211400c540002801c80c07200c0c0255400319501d40480a83c207400389034110340414440c0152400c0c1610b40510340203c3e805880c058504120303031001e50083c0c0f030701881460300b0301d441910420326050408545507903500041c441c0501a0347d54482034401d0280d010400b00a031580120706202d03100c0790303081c0113000409a0304140c0b0300a1684d0000115040c00050350103401e54000844012640e4880c0160014407144070301a40200b4090041f01c203145401000718064264508440300d11401c7c0000e80c1c1140080c1e0300800a6548901d0006002c54080000b0540c0010111803000c42d54901c0e140030300c3c16020381209901150b0a01c901c8404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 312677428 1250 312676178 312676183
    0x11b050703050712020f03060402031e0715081504050603030a0f020109170301050307061107050d02060d0c121a13050c3f040c0501180e010b0a0e09010b0f0702040b0301090302 77
    0x5546000301c60003480c02091b81c042640b01e00c0107a031300030343c0342e48150781c444d1844061000090701404920180c0d8912036642c034607120111540c0f020440003a182038100414032070014095184004d0543d4100b00a1801e800881e075a0300c030f900240001e0044064507243c5082c403d422840845130b1013400b648150441c202d0703171045600203006640c40b0b4050041c010480c0c46c4241005003a1500c5400104a0940741c10240a503020b80c1d05411303a0482c9080084002000752801280031a01c0596551400e8450b64404041110002c00140001841c00c1c1107154141d540c07006205012012800e00041c1a241c200d0549101d00c5103104402250b24a00855804a6183c0000c104000c10f00800007100710f4003c0a04080c40724101e8000f011102000340600c100e51207034010070184402c072212440560345481003811240800d034411b800b89140040c0106d0790fa0b0340120840c890503025541003042d035050484400b1795009041c40741c0307241d82e03003c24801c0c20b6603540e800c150f141060140080000e9a07a0b41402134 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 312678678 1250 312677428 312677459
    0x7080406090e040f0609021810031b0810020306120a05010221011d1504020c010b0f061312081201060509210709051e011e080c011b0507030507 63
    0x42a905603001411540c840c04540c4240c0d8030100200301104c841d51510020b04c510181682c020b4a9801e80710b4003c1c5504884c40d003d2108540070303010036440c0d4600320801900518440303007046c01001b0100103d00c030004140e000343c54801c2c0096280d99400001c0303658000040104400e0f44103404500081c8007065009205030001c0100200c40003419069203072030600c2c28450b45044480350015042592100c0c0c2d15107800075680c00840c02c003444054000743c2a80c0195001c11080c1e5501c4a6884007031628034140e202002d000d480c05030500312030513640000380b03a40740b0482c9501d44030300503e1010080c1140841e40c0300d15050070040c100f9616010000c0c217a030400d00185000d031603a02d500c1d050360700fa045001e4103030314145002042c2403400d00c1c12030005080d000e8168035401e1f0340640d1003800480006000c0e0b01800c141c022100b030481c85c00700181d0007124682d0003404031740c01040700e908260341d0083c01e00c41c00c200c00340000c1c607458100f4075165181610a50000d0080e004102e40814400607442801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 312679928 1250 312678678 312678689
    0xa050a080418050114090402130509030901020f0d020a020d2f0405090c150a0c080a0503041a270a0c090209040b040605061e19030203040c140a0b1c02070804 69
    0xb00508403000d02003125028040e0004400c0400308000480c90840d010940c05880a0b204050304c0d0718a018020540b907064644c1555504041024003a65a040100c2212821048000d000700203007800c000c1d4907511940000b9000310200c00d00c441c05d00541400f083da01d2500c01941a27100c550184801d03141702c6842120510030341c100800302c0c60304100000c221040c22001041d003640c4000321202d28059034081e050786e070144104080150b000c1503e07140034240c40300250711115620702e002e2911012245500c0e041c0c109000d0040c040c4590051086600d90070400b600260384403c0c8825440c0c03602c0c08002d4503009040c403c40c071700046500e49c01d5801420b6065010340f410302c0701c00408c40030081615891300400780c1051050000c50240202460301500e90342003400c88501e082d02c49007014000408010810012940010034031081005c010409002440012400064030000c48001110340106204a00a01101080a51500c032013280341001d900c00c0c0030700840d99504603241c11070f40368000b481407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 312681178 1250 312679928 312679949
    0x2070302010f08040534030506010905070c11010c020f030d022d37030c02130911090403110115090e06060105070618020604060806040e01111206030a050a0804 70
    0x3480c080e070301410a15000350f60290141013400c0803c2401b68142492601c0100c10750b001031840b00c4120807490004001c0c50041016107101d60400d0f60755801c2e60f5010b8a600d040045200112010440308003410b5040c0b0000d20b0016000e10080c00001c4040ba10800c96039410b0042509102c4410780000356000e404420101400340d80c00c0000c004042c0201c000c1c03a90b4543d8010320148411881c0b5003904049100c0c2d951491180022024500e9000b8140100101c0100c1c0502c5202c106526004c2ea4081c11100e41020501007041e095540d40e64400b91000c141c0e000700300c0800401d04050261001601442e0300c14020009820903005e281c8651200c0c1c491000c0441c0340c4424082900c50109905128240c183c56075847c0080701c1c0d40e100000d0440c20024099200c0308000080107a484c8001000103203407070356540c04e903814800200002c65200c8117107558980e00d004094904c40f540c06042ea80b070109130072844401651914046410400c62090080823401204a00c90402c0303180005002030700d03018180b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 312682428 1250 312681178 312681197
    0x50705040c021b1206011d151f03060806090a1703010302100507150f020405030f06041227090207031805090a0203071e050d0f02040f0506130b0a0207030201 69
    0x240400c44811078003500068024500c1031403981d5440d880608100d5000d000303d03a01c0342c4c1143c010382c20400e00303800448407078000101441012010b24540398201c448440782011103070082000034010000c050b40406041049402401700c03a0107544000d00403c0c040c0c065030303030300e18050b546642c440920f00f1045541c0802961500050345090064906032035019100da0340403044003609035203a4104000407154070390154400050f003502c60083d003001d0004444050f8071241048101810b010204082911079446a000c1001081d00545100c04601c10740c01d2420800003100c1c03207215066030340f2410103540350a14030001081c0031107a0051461074081e540b81b6908a1654401054006240c0b05040c0d2024160000caa0810a15402160000854100700480700c0b20520310b01019800b101c000c402040c40418072182050250060007a0220780c0c510440c07074181002a40900720b0202e018203405100301003043c00c014980591320790007070301c11243e140c1d841c0e06404000030364401d601e01040f0300045401c107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 312683678 1250 312682428 312682439
    0x8070203073309110d150c0801050a0b13150306090203040b0709050d0510230403020d0206010902130909110a1403070501030207030806012a05010912020607090303030b0a0f0801090507 81
    0x100380d1540c5a8080131200b034402d050010008100c8a000040e20811011460a188240f0301d100f1112020b44685510840358581010005080709651050450040411a00c680a070a100407502920894500c4403001010a202100201500c0c0c02500078644000280410b00c050281c01d00d1080d030665840c1d080123900c034018081c10f5084100010700c10352081d102d01014030785070b0704880c441c0f01d107404142ca00790000d001c96a8000e00e05641c01d4000d600310f90800c404047d41442001c0c05031200c110150319020108500752103180440c816000c480340c0d21014007081028100c90b86108040042601180c80c4d2200d904244030f2481080d10380c440e200700e407000502d55000703000f40c42500f50107032615441275035074400554039007081d40c0060048047c949010800111201c0c0c840c400305000303100000d0000032503d42030400c21407015008056601c504d040102481e40040e400013669030525000c1007901a0a01180c4090b0b6590410460f440b00c02c10045042c1c60150b102980d03030b40c0528116404070b1f9458 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 312684928 1250 312683678 312683681
    0x3050613270809040615050a12021603051c0516080c0409060e0a0c0207030209040602070c0801050a1a1206070c030905031b01032f16050307080c0d0f02060106080702030733 76
    0x1046c010040f0304244904164540659880d4902e04503844000d494a1014503507041541404282103020030400310b00003040003604c1c401c420510511140030001c905100864010700c4100d40c1c4164100320201700051102a4101c007035034000c1a15007c2880700503190f20076411164401ca4500004920303000018000c14800200fa034202da4005e05000840c6e00ea948454010398804441500c0122800000040d80d010901ca080d200da0300c000c60008051905041c12500c40c01410800f070b10850480072001c0c0f072108041642d80c0c0101d410b040401405640f49021380307241c2e016a00459242c050b80301140302200590000b010741c1d2900b680c0401802c26005c415280c060041c4505a00400001e03100c03d1104110308018202450b000031034003e4642150b440600e158025602140c110304081a03409645c0b0080150041804503030401c0c8103022049100255190b2051103000304003d200c0010414440c0280f040340d0b11a50416a51a005020034003010150400c00c0038008560b40c80c0c800700c91000c01d0350b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 312686178 1250 312684928 312684959
    0x80f010612020d0207020a0801020406090b04030c1707030b07020321070c020f03030f1309110a0e06070c0506030406050f0703110f0a0201060e0a05100501030506132708090406 77
    0x441c1c5594681ca642084800000d4001601024076280e08006241c0560b413504d840d6001000d5101c009a07a50741070000080c01c080a6a0200b004600180010300c00101400100800d076420040c1070403044114075551490a60240d0010300300d40c85503400e02181c6075000c40101940410b04000000128103220414144241101d2480000b5100e07100740d0010314118401c044030120007030440e418075031a010000d0b402e40c40a030030012200d41c2114100010a00d034010004040300070000d982c100101640007411807a501c0c0c0349280303c0c18000844c081000030107240c24014210251103c1d0310b9103030620b00440101010356540c1803048650000540c914800d005440703d03050740205e11410404c903285100c1e460382104d20b144056548aa40100e0440c80c00c40c5400d03c00c0449010206003400d02143c10030101400e604220b04040c280000c0008903203e94003105012500842c0c0041c00b102c155284605040c1e001c00e120102c00c40320640e140c14001154080c010301403088408001d050b0742c0d8410b03103055000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 312687428 1250 312686178 312686189
    0x105160b0402030115060e1c0206041a04030c06050c060108010510090e070504020a020706030b011d0904110909010b03060c0301050a0b0a03020d110c062404111b010c080f01 76
    0xa01240510005003055802608284007800101d070a014007141400f8042450304a00006100c56410300300510305070400c84200c099901e078101c0d102e00c0640214081c3c0c81140600c0516090031096140c0d032101000071a0b0080d80c11035225031820b52103080040441d0b002401028061003404000300d0600818440e440c061401071425280081c40c00c0c40e5a005001d4201d202d0b510ba0064005c0001c990f1650300007000d41d0452940640080382c1001000f404948a040c54141000f1401041c50480a980b500c001052007003110a0b02c400c0e900d44c60210869030b1410050754000c4886030a02c012804150412080d0310070480079251541d54240090341d59000c00d00c08c4a03444502a8810840b001c0360b48011b06d040ca68074500513162001c2e030128202604c03908200701d083c0c18000209403429950502403281c004503a210603c410071021212150807003c05a035071440380740c0d12084601480084421650070300d03650000c0f0100c008014210781d00a00e00c8001e050085007040c030001c1c200a403492035550507601d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 312688678 1250 312687428 312687457
    0x240503030910090504061203020f030a1b060f09080c070506030c120907120c0f0806060d080c010f0e0106090c1803030804020a0e041211010b180a0b0a030606080c0105 73
    0x1142001000306282c8036400300e80c14031410b54400314050322280142c001034084110b0b03200f108215850002e18001c098014a026a04140844034186a2003400e0300c040000700e00b6412946105400c010b0000e107a41070002c1c10340c0c0c2c83c00100b00104880080038092040d2000c0541d68600d0742c5001340300e4a80f1088942c0b001d0350004102141c415601c15050b25044080c0e03408960b11140c60343d0b10a940107143d036105682d240304600040002201040b400409410003002030540c5040c5080495078000075510001c2002c41c020640c10320042003540310110000c070080c2d00b0b1000400440703040d4003c0909000d001451410f00701141c58450003100e02d101001030140b1440d01052441e141100d0388071016104a901241d1180d00281c001601042d6600450042d007243d159a100850090001806c40740b040b40c05034104405c221044c0d444000e16405072440301c0d041c0000307542c0c60601c03100400051070704a50105d03c0c840040103001180d8040403c0d181d207042210650b60003140103440902402d0b0b103085459 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 312689928 1250 312688678 312688687
    0x430090603060602060109021612020c0f0d030c020d0516031a01140109170118140609060c040902090310021b010501060305040f03120f2f03100e190504030324050303 73
    0x403142a401003502000e0f00b0314030010002d2507036078541252150ac10f1400160300c146a4060103180442c844110303204121000c2141040e01d580152103d134080c00040d109664140c0c0302c8041c44400c2c05000b21a50b89045150896526450400d124003040e80d0f403007035030101420010413110b19a00445141e01300c1611140181d901c0c08042c48000d103d4046c02000c00d541700d030007603140b0a4014a16039041480356011016030b892110200740307046001017007031070303180d0140b810722200b2a0024100c40c2500d95200c0c01696411070103002c00d01c0c141c007443c003009182d4030015030160724001840c44d0001c5203481100a1000d81da803900102e0230788105507005000c480360b034445200043c0c004d1f940722880780c130285408a105880c0e40740d1101114201c440c0d800114640d8030302c000103106680e16582008405010031421400d0244083c0c07a8a009800307104a680c09503c04030b0280c4002420381c5070040c40c0401c09002c075142c94a0024090a00050080c0007203440c010782c2e03041c02c1212019841640c03405030003503091 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 312691178 1250 312689928 312689939
    0x50a050c030c0a050c01092015031f050310060303200d0503150910080d0516060905191208090f0606041d06040501020702010e060412080304300906030606020601 71
    0x450b401240f000f001e024080000c040d001200b8020940d1041c040c0107806408945100035049821880c80b14610a0340080120b441c190f40c1e9030152500142c0d8440b041d000300b1000301c048615004290044c55140c450000c50500d100c119130040010780f07101f940c8103c1c10034000b501102c4051900e42c0000c0a5800c0207800e1021030f807154029543c801010312035401e00038040c82c04100d4a080a68040300311104181042c000c080040011070a2081c0c1454010301d0500c0003d4401c0761708514400c014000c0e501d4840505c180003080042ca105d011089c0d103107a00c000c5091800e84c000411070ba0a140200e06601c000440b5070b01d010031420000082880a0841c650341d8404200c020b09522381e0b02640500510001190f1040804c180c1c0c0c8698444c0000582c0c80074031740000342c51019240b680b9440340b13070100000d03c21000e5210b80d00d000309501440207034503511107241c444501c1006240b035480390310440038071119030745d407184081c0b00c03c14154440e1403440b81ca56908601381c4a5901030400541d001e030004014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 312692428 1250 312691178 312691201
    0x6050708070c0b03090d08060a06170411060a0306080c150a120e011505041406030d030e100504050604030e03070807120807080f0a08010e01030c091d06100603050a050c03 75
    0x3002d01c41c502c620900c0c1d880309107004042d041070761480d40c0355100c07106100c410782d00251400d421080c1100c60041091414000904202c0c20092850340307ca105000b0a0400c41450621540c0107402003045485040080c0c004004210510500c0d0b10380c810710504017000e05025528254401c02e40d040d080c60111403850075100326240c2412158000e5039006c55030b4540070284251090503006962521507945000200000e460700d2518a403524000c03982801003d940c006001a02c48445040100b54250440801401d05018030031040b00d242c1071101300410410b021800c140300354400c0d100d0b03004080f040800c0c961354110900030700340709070f11280b001c0c0060b0400a4080c0343d8a445044c0e010700d80b50790b0f41d40b6000f058112013030b0a0301181001c1044c00385190001400746c00361502c40c560790540c0d0324540700d1940451143c03042051180d0b4a41920400c0000a0f0102d00029440340485003e030512003400c0a503a41d00e0300c2038000081c94600410b140c1c2c0e03194042c060042c001940000c1c00c6444800c61850f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 312693678 1250 312692428 312692437
    0x10f031d030f04090e010c1e0e0a030b0f1305101a060a02012703020a03051c15051c0b040b060105190504050f011e0302030a0b09010305010b031606050708 68
    0x103440d1161900d0090303600c2040141903940c40c80c9000341c0c81d00d142001d81c40c190341c0c201c4045515a4108082e03071244580c850320741c905060726484000b03003140600750103540407107500040365004100003a000c070520441000c554043c1918412500b0140d58181c200e03003100145490041141d0484034140c01088056040151078a00200000801e80c1c802d13800101c041e804192860050b075124403400c04918040714600c002e045080202c00da0341c548954000b91a51184000113080c050040340020301100c180b100d2001407050740004002041d007030a41010040803512400b4411140c0c030310200c5103850f030004202201548041034003402e450f5580d030701002c020000d04035410407000b07010820356005038a000c05103202407500e840380c1d214200f4044c017607403c42401d01075050101c814250b02c411000c14003442810304442c40d00580b00e07185c0901c01c1c40607205480d0000d92100c0d034031002209001c8190710100e0511400c0b41142c2045001c001411041c0c2c0d803d114000104005000e4500403c090350003c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 312694928 1250 312693678 312693701
    0xb010915031104320f040b24030a060e0d0504081203130f0b0103020906180f06062713050106120b0301060905090309011805242a010b04050402010f03 66
    0x21900d425510b8400c01c1e030741e003c041a040c1a240c802c0c540303d0032103071894591703800840e507000301c207000d1510f83c6600035903020180c08041d41600070101c0885d15519840000c0b00100024103498074580b15017090400b40103a046c0c0420280507100304240b99500480407101202d0190340a0911130b04004030303004883c1c1005200c2030143d00314821040024401000141c242e510034002e50900b9411401884102c4c003000700340500480f0f100c040000171600d03840e180d45d03100000201c120600c1e5158000b24000b40610800061003450210109400c441c5a010510b20085c0c01c0e25030441c00302c045072810b000c0d81c0c401c0c0b00e07180105050714100c2010030482d402c542900d0501800101c2c1c0e00d036450013410101e800444000e00140c0004c958009190b07400300d403861421100e11020582da07400c240c0040d41030340080340c403052103201748940d030004d0000d10341c1910141364803001c1610280a901111814012102c004078011f5481d00e0f0800001c0c1c40c02d88101e0740103a406070b45059071180804070a170000c00001080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 312696178 1250 312694928 312694931
    0x4050907030b09030307110c1c02010e030609100b04110405190b0318010b090106090b0a020f010c081b160609080903013b190c0b03130b010915031104 66
    0x1c004a00d104040d01d00595000c0b00a5a6034982a900102000080a150516a04610480062a40c940c100e038113000642140c50a0081958070068035540818107801e41c050051008000705400b011685000b55a4613031014003462104904000894951850b61403c088040c0018000360412031001800c02c10005200581140c5804c40ca501c1900115a09a00003000a07080710020364207005402030802c0035130b0b80c400b095040003005802002c1070300520760341d440701094100b0040e01c2006401c0075207540c54020000c0440c2c07110010f01a8908845181d00d02000081d08240c2403115000c0302d43c1c50f1400c0b004160340e2801075540750301600b0109002d40b184402031000409941c1d003271103076004032100500030b06200c0b41da00345503031000d405034600c440c12200309402c0c10301342d0700e00811040c1102461200c4450340310f5041c40d20303295013081c540101c0100b000100070000309907006400001c09a0182841c00f0701603981b10404000d884a81d4580a4801c004960400004420015000310100001c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 312697428 1250 312696178 312696193
    0x40f140a05070b03010329011703090a090b0916050d0504020a0302040f060504180b0c0304020307030c0b04050a0902090105180102070909030305040210020105130b060d120302071709030705040509 86
    0x19441c2c503064850b00807142d900e0000004100700001c4205080e1850040014002000080254610710110510404141d0103074121222500d0506208a0703916100003400481c0c080d41b1007480c003006200e699071240c000c060010206800100c01c111203c4805d1459586034039000281c0b800c3c101a080183c022a088032560001000603621070003182003040d01100c3c0082d1482c58901004280c9504058402800302d04011200124131210720a80d4400c2107a082d280e6241c40b98400300703150101550010f824220070b00030204403050030f48010130480c0d904075071024003980c46000060403071088030700c0180031910800644148055030750001400e20b00500542300d41982c0d03804c080050b51060309013240000d80c1e50081000311310b0200742d0780159440c1d40c4002c0010b45002000142000c0e01c840c00501504c032040700045081d0782e50b854801840340e01244d207010614103403201802940154408840c400401000d427462440c1020540d117000320010006c0040d50b1401b420321006000191060010340202c0c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 312698678 1250 312697428 312697433
    0xd0c0206040e0702060a050a0213030209060d0602031009050a1506120905071e0803030105100c1707120e0306042a081605090702030406091701020d0c0f03060b03040f140a 75
    0x14030140f207120181c011304041d1801e1030905c0200d88000745644403641c8144449014080c01d280c44000f640d034191005480c40d02c40ea40012100c5d0403005009182600020400004481c84090350003280c8900c1414800fa8450704521815a00142c1410403182442001000b01c41e10840400c40b45844e2070500240204080c0c45460070300d00750781c100c2161801442c2450f80d10a403a0001c0302c0c01402044007450840d410440065200c9080b00b001504214050b00740303000303103c0b034084090045031101c49403a65600c414039000c1440b0001c40c3c90f040c0403c00c00d1031000094140444c140784074540c8070b2580003900030f43d1604000018020160b0001c8001d4958002c03549074410000000f524440201041c1d050385820104a00b9a40c02460130b01150002d00c000c01103282c00000c0e41040d41d44500c0032040700302c4049440b81c024025030250495040c2000601c00c0700381d4020309214007529490741c0600c040740d1240c1c00c0701d01921040e01c00412264602d060307140451220200d420015040344161900807603140c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 312699928 1250 312698678 312698699
    0x9040b030a03030506240a030b131b091e0b0c0703020d150c090e010302060a050f07240903120203090705031203010e0a11091020030706060501080402030d0c020604 72
    0x401c40203c0e580d0424025280381242e1062a401300c042c240c03110050350541a04a21b0203001080350030305841c0c0c810b120440c1d80728040f0b1660710030000002c00619104c591802d0002400c030f000c00c1c022441c2d91401140d80c4c08007003038000100002410201d840b0b8a01059a4031680c0100100b003110302401c02c000c4016901c286104422502500f0100d205140c040101001c03944000c4006041c0002600c080014000420101d030440360101d031826140c020300041600c1134032900e001612007140010340141004103000c083c0742044101c0032421480a2984401801c84100600240c0495904440000b051100d44c00861b4071001c00303000d450101d543c1c0d9011030b00c2c210040d4400354405e90080018480b224882910319444008020706100c1c451a1000e060380600c01e1944c1140114044507400008502a91414050f0505011602c0a0500841007a07807250001c08044410074180030700012190301c18404a806541c004014003001906110305446001030600120b03001030f018000001c0c0c0300140c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 312701178 1250 312699928 312699943
    0xb090d0b0c2209140403020a0807021305090115082a040b0409051e0105130204050915070e191d041505160e030d080106032c070303170108060c09040b03 67
    0x142e15070300081c107040820120a4884c41d03c43d07040d404a0b0350782008042580044c41c0a92507420841c202e0391100c3d280045880303c103144100d04121810b2034180041c03000150f0000420101c1900e00d249201d842e1010311b5207860444c1c01c4524200c4107059002c0c160020700b41d85949a900c010000100c4040303100118086c4d504550301681c0c2c5410840c1e0810112402104150000e660100200500e260211005250401142010740541e65510000d0600d6000300140d00e94510250300d82d40051820400050004649190041c0524040441c0100900c08081804240c0b42d0380601421180c0c07040e1208007005100400c140d401c1d0250748481c485115851054a00510420450310309440917103201410099050140d54026800303110046c1c08103038070050041c107460180c50081400488264180e900794006403005541c1001441d54148400700000d900040b24425111494403150034045d6440b40d080910405a01d504860005038a1507540f00081c1270251006000042502000700461f190a22 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 312702428 1250 312701178 312701227
    0x2100b010e0d230c0102100216021f03140c07031115132d0201050c0c03030412030305010f15230d0501050111010b06071202070302190905010b090d0b0c 67
    0x7210f01c4120309941984103152100700103400180400f040b40e0000035521405e000210034004c0e0302091000c0030103541019903580507002001c0f0001c040388005840000803072440100046403500507030b042c5a00704101080d00c9074812100490400c00203442c00d85d030120542c84120030f54040d00c0481c4000a4603018040c1c081c2007000c0403007910411a1520f8800c4084900d40d17004075440720a5484181640020407009a075820b02c1c10300d4450b00d080c1c3c4511319003101d03142400d506000104010031544802c0401c0c885050080d9000d10080c5d0340c800c00c0004504844c041c0c0b80450702c1048038164543c2c090551052481166030324a10701d00103100c20008150800c6072118101030700d5a00403c119a0f103c10418003520f4540020001d007002100040c8003032060400007000600c5203080c1d802914000c1c840c880055401038001c40b103101c0da035502d1018072526405250412843e21002140d01c07581c0c40c00b60380c0045000342900024414545a074820040020044004018100900b400364422289040351481c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 312703678 1250 312702428 312702443
    0x9020108040b1e1f05010306051c0519031e08040209010605130506030718060302040506070f0203070306020c03030714130b090f03010c050403260909430f02100b010e0d 74
    0x24103c0c084c4810700e0300c1c0da01490425040060900107559140840c01e401031403001c001c1c0401519190043c14000034003540d40209403200448800d140e0840e14040320222603400c510000f2007a02020b0b40d0503d0142c60194100d110103005201c800e009500401c0c1400085024180107030b0f0740d20002b54980d20840300b5000040d8a000b0014400007155144400b905481c1815402c05040c032000c01d41a000c0c820014064041d00f070200000e54405100801c003540c1c00490235035945a100040568950058440c0b100048024403a10303031010041066843c4031500e100341c5c2413180d107042101300c2d40381c005e0a210355000c0d1000e088810b036950244035060826503a91615520780d8070310305103403500c680e4996811201ca45040c07805442c0f070405204403000e1090440c0d00404a40780d81010010094441c0c80103440c0110100d10543d1000c4645408800010b2451004588640410003103a01480304007807440980d00c490072822040d065504174a02810041c500525882410800202d8001c101c0d071040e16100b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 312704928 1250 312703678 312703711
    0x6101b030c03030e0607020c0f040615170702071404020901181716030f0605040c09060b030a11120a1109030109060c0e03030a050304150b040c0801050f0409020108040b1e 75
    0x5078150151304000807442c03024205900e8000c4010f9180c202c0603210512403000030107070784815038550340500041e003000d42c20400e2440c10101c024100c44100c001b0003948a00e500001494644002941d500f40c0d4113400030002c00c041524207100103500000a0981807200015850248020f40b1218000901840101c01e4810020725581c60520950012210040403a840c091011680c02c110050078190b000b180002d007070342c40d8207062604400b96040b00c558075060410006506c06030b940514046d108543c1c0401501c04408065000b52003154200420209100c00181d21102540c3c05010085800d0210b185000b4030000000d0864454680c1122250354681c1e041c1104c541c002007861291005130000c51601c00598009081c502008100134009880c10340c4c03807800f00e50560014402c816000c0c0040c40303c904030840240018600740590303030141545840c00100362401d4050789000d41c3d0180c45078202921140c813400d00107074004200381d01c144910407080c41c2c0d0071410010148130322011650044407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 312706178 1250 312704928 312704933
    0x8010e0a0b130f1401112709010e06041d010f1a030633120a110105090a030b0a1113171501150c0804080a0b01050d080306101b030c 58
    0x160903015202d40011100000460700041504003002481e036045078030705a00e20240c9104502401040e200c04820710700100b83d595502c13600056054150901030420030072419160240002a0750900c150629001c40350081740301c50a09031702c0801c600d1460f9145d00313949440d000d805400e42d01000003000d1070311740c1c5421314084030611700d00c0c10754440d40840144c40d242c10540040c110117000d0203040224a03030100c0c0800100e880400303d0701030141024007010206000a06841e4a8800c2ea030001c6d9540901c414041c00158800d400310390340b0b403100a0505880500315110042c07407040042106140e65618020400034402940140007001d10510f42580c1150804905078100001002a91110b0f44800ca01c4100d924000c540703c4d041d11440741105480b040d85560849003a4005840901182c10019003c0f032900e40c04162009604d00030132040c030300e40e40e892060101901003060042c03c603100c1400469117510305001c1c030078105501444c01d0f20262103d01e06407a2113400b5180d0880219800304242c004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 312707428 1250 312706178 312706193
    0x90607080904061e050411120f0a0905060709030515071e0207090501081f05060102100b01050d0c0216060c02030606090601140c0309041805060f180106080106061803080906031008010e0a 82
    0x14a1130070030b47c85418641c1c000008000c442004e081c85210b0701c1c3c40e40010303402d00f41d10741c440a4016000011600107003030201d80903022030300d1703408150340d01c2c0215082c0c2074000792594551030140189a40b00f000030304403208090000304e014a400c100318003584000003041d94403400b941e40605007803000780c08103960b0425240342c0c5c00030b03c010400445003440308010f10b9a8000c1a0904c6030104647c0214002c842d040c01201c0c280f140200314883c943c41e11070030340d5030f1075030005084c1300c0d202c085038004001c04e80b990000e0317801c04202280294540e202e41d00088280c1083c19116802c00c1040c140b1007685016441c2500e450303040030398944c449170b101160b03030410303854940282400c0340d01c0d4800c400490291074a61a480c1c80300101303a00611800100819108803a0000902c03900292000030416941c44040e42030181c003203840303030200280d180c03403d0003001320080c2d220754200ca038040344491411a0a00c240400c1d42c05c01040c1c032007105c04030100022680e9007030003028440a44074000d0716a09410340340058 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 312708678 1250 312707428 312707441
    0x9210f031905010e15060a03020408010f0e060c04230604170607020c0901080d0804080c1b0f030607050d0b0d080c010b01091a0f0c0a06110a14090607080904061e0504 73
    0x9250582800d004400b503008585c0c44100805480e4144d44441500c01600a0301c00c0d07a00c010340661030720b03400141400d075036805a9a80c4040c90103441d40d80e100c000440206001c0e078064011440540f078611204400c0b218840c20b030501c03010b0080c0703003480e540364104100c011018107440a940c00c164100000319a0500c0a80a41141201e10b4210780d4102040c1a955800050100d000d2000c52404102031201d000d007079600303400d8410122051084406000221507640704907541c094200c0d000001e005103000308031380d44581070030383e81d0750304146110751080c0284c002402c80f1504460711501400100f000c03032004010325403010001060b188400320004100340c0c40c0c1d40c08012070480121009000b843e19a0484040100134820701e070b1106140c86201d414a6a8070034020704407464141485d1450311444007510003040b0750340321080c50303100d00b0690784024403c0c09801584030204112003c00103c170100640703007a51001d00000344d02900c500003039840c503c008401080310440309100308200d00d010700501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 312709928 1250 312708678 312708689
    0x50a030f0f080103030e01050c01090605010f0303092c040807020303130e09010e030d020f0408070e040b100e0402100512090601140a030209130f060203010b2109210f03190501 77
    0x1c0360300d41c50754500501b804c021010050400000041d04401e043d4250040c07400c4a400c64020009540d490a104041c6400c5100481c00304501410001c0c1c4e411072510b041c0c040c034078054410200c2104034007007000700e050000c00458540105010050140c1c8041000d400d40551110031580000c1c00e100c28494450402041d03000aa0b0500c0c3d001007117001c01100b55003d5103482400586c07510203084510000d0300403904600405d115400740010740741c080268550080340120740c0704506455400e880c00c0b00301c01900910729500e280c0008900103040c01119401d04144600d030003410700c2954805020102c00a40303000e40203500c89801403100c441001c800d40c02452041300c61034180c510f9640868058000140a41c0021180441003001e2200c0c0b43c092503030141d8803120466681d07860b2030a40d007940d049070b02a05400e80f241c2507642c0004283c008500d009200d080028055480305013203040902c412140d00103000c590034420400c2c1c148038200910701804022a40e48401c000c100d911004840c01603114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 312711178 1250 312709928 312709937
    0x3031704020a060e0609060f0d051008120a120504030e010f0f020c09070905062d04030201020615010302040f0b03010e15011d011b060203040c08010506130504020d050a030f0f 77
    0xa01005903100149041250f5450424a8451030a0340004003507000d1062141c0e0040000101d0200c0e40d1007100c01004085002c61041005031144c5c14020a86032035806050102c3d4800c03c8a4503007000d5001c090042d800c001c2ca080e5a101c0c200c1c0e030011054540c1503030103c02017010f40c0714903185503030852201c1000d410140ba01403609456044003c0d600d44019074458016012035010071400d901c0392446001411002d84202c1e51103555040568907003c4810310352280c1d00e6040595201010014100d03021282c05900801080d11207006a030903007500103000c5410705508100004007601c8070740743c0800400d07518810b079449600d4014101c00d1240004c00c0d8004d03502c810414a50240c4e00000064003c85d1030990000740300700c0e41001641c1a50303503240c04841c5000c181c0034070410000c250700110310842c031900c92901ca061303451340202d0aa80341581d0361270303010010280e0000e61001980c451917000e03000030060102c00390641c0f41d0138100a45030100341d000030304c1e0031030303201c1e42d90f40000d100c281d441131a280 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 312712428 1250 312711178 312711181
    0x1b0c0103050c0a0e12060426090a030602130f0f050102010e0f0715091805011e050f0d061103040308040209010f030803040f031107080106090c020615060304020102150c04030317 78
    0x4160b07524407581c801901032000100300b007081900c038a00502d0729603030008202d40c3d40e8201030500380009807100400015045612035640c009030012000d80b80c000340061f10200281d82195520340c083d410288038a200d5050f100c030005000203840d00348600074440180118803071805d26000a094546c40f000b0841c199110208525181c00c0c00940001150300f074410000c80101c801804440304503069200481c4000509099076254509901c064100d458040d038400ca01e403408407920203050690322420394088a00158942c160800c00090321038148130f00700000d8140c2034110603050b5038009030b80c15000500030b44108021420001080381c00f50000ca035050b0000f41ca9907031036000911004000600c103d890505810415000e0301d0941d080d10940401d807403165407643c90590007026242702d1038200ca403c0c2054566258008244d0754003480c2c200e0000340307003c0c410b2400c0c451030340c2c03014004030f04503c581d5441a20503180007000f00d004000300654940c0c0c552960500400250720003408043c8a0380880 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 312713678 1250 312712428 312712441
    0x19031406040c0512010f15020a11090a150b04260607180806090607030501060e0f061602090a090b0703110910020c0d05060a0509120d0b04060504021b0c010305 70
    0x1040d4490011100441d1000300c0007012200c601070b1009040b03444540c40e001142c60580a11042c0a9a2040744820941d20708003d0499072024120005060a0a0341e01901501e0525000c2580d06c002e034840046040041c0c1500c0481c100043d500c02c01901c54041414025034000301030204408108040710400c880500740781030b4964070b003e072610050141300c0403650702c1101c800203068000c0c42c04406039001c515103880c503992030785022119203000915160001c12850b008043c400100c400141818401551410500089034000310700c1880300500c4024000061740c400c540c00d885a090700768041450245460000f40610340501184281414030907034170041504142900c0c00a4000c0798401003006400300c0903810321908801c4a0b8100b112010b0b61020701c42d00140250160013111420440d940d0f0708050f00e0b80341c018030300781400d040808000a504900d0243c02810007001e00910000340c5a81d40c200160880c0c3c080d413200d60000056020781c4a0382d2006002c0d00710161400e003410b110601c0c180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 312714928 1250 312713678 312713711
    0x6090605040908030a0b130515090c0307020705061612050403121d01081b0f0c0c150405010c06020405030712110109060909150b0a0e0312040602070e060f030703081903 74
    0xb02002c20b459521b203820f10181d07440c030585c4d210085c014002001a4200204003450203102c000601c0c0c064031007000442d00034501c400c2100e10400c0350740c0c041c248007800c100400c2069404840c06200007060780d844100428480300c80019591419104c05940b14510b103021440300712100301c034109102940580031917a01c000e0072403250080c02440c0000603940c5920701c01c60010302c05410884010760100755807008ae5124001400c2403a556021108201c00003800c011903880401d580050621080c0000c0000b0f5014a801071007152254201505050b22000400c4c42c05907181d00101c214426a11410180407041e51940e11500d070a2811112075030070004003502462151081000d416600c070107006000c4007422056000e40003d00803199940d900c1e4034028291a07903a0b088520a00030020700300408201d2208850031111160050318031145480d10510031540c00a140c65085120420b00d0f0700c040e42d0502142024510841c48640c80e100181c610f460020703e0f0381d420381e0500d0300d440340654640300c02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 312716178 1250 312714928 312714931
    0x10080318010305041505041b0f0b07030e0a031b09050a0216030f051e120709062c10030f18021e0315180c150d1104050d03030609060504090803 63
    0x3802e000c02c43d501c440c50000c1010b1449549903601c0303450032080c08108000303200e6080b68150710381410801242c8402030007500b1031562107a441e050108008020019002c0c49010b00c00d1034009021460041d6030303031039042480c0e52205268025540021040c425020b2611440746c00c8980c50710114144070a10710b001c42c001c02441e80103403c0c400444a40701505100e042140c15030403480083e110324001f400e00d40d0006030071401d0107640d6260350f0310029007140c1c030905022040368465503a03d1001709080c060010140d0341c0c850400c200483d01c001440741e5803030b0244841005000c03540e00003600c12002d03103500115240022100c104800142e091000341c2d45840201c0c9140001e00b2280200460600000b4503084801002092180c00041000b104125000d2240223201103c402c2d10314003d103100c10003021004100c3c0c04204900203000c5807080030703a07540c840700c41b440d026008289000d0710b40d000220183d140c000100d00003522028144903180d802d001e10340080105480507c94050b1a6031801e0701d41c0070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 312717428 1250 312716178 312716227
    0x40c080915100f0b180402120109090807061b0306051f14091c05010f09172a030919051f2d020c090405030414030309030d08100803 58
    0x500388081402d03121a09a40e00c0148401204845016550031640215800c000c2041c2c502080004166410342014000c450080e1040c12055035103070708141b0040c00811400e079040d2a07084061100d0b40010f04244643e0784d4111100c611070141c102402c0c03005082e40c2c01d03900038500428024205500c4050f10422a041d4440d40342030040c1650504502c03495940140405983d20a442e140c020f02144d000c4500e0803141402100203000280308a110031054520000000746212220034002210781b00d490003a1149481c2030710780000858004041056050240700b0030b40c940e4000041d107005510f0b043d200f21042514040c9607220003403130280090310500c1020100820b1151100b00000e802c0d204681c51020041046407517204080d0703800c2e11170070f00c40e07090b00054050b100d00d03002202c035880c00d081894421503101e0001c510b010b003410710241d810030140c0c0c800f030f402d88010301802d031845d9000e0003000c4102c4407a03502d070305c29490111103860965844d03501001c001e8008005040a80c88820854501200e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 312718678 1250 312717428 312717463
    0xf09020609211902130507080a0207050f060f16020a20240a0f020c10030c0207030c0905150909070504051510030e01050627040809090109050105040c0809 68
    0x150348840d002403082c07103071403610303850145070348640100f14070f400d407400118001da03144880d039042194200e084502c01c3c0da0350004213031220005001c0c4401c980080c01c01920400669000c130f8800d01c141d620301031090f0750381d82d0301810080410a5141540c0c80f01d82e401401c901c000e00340f8242c01d0f125500e035034804d5486c1c0d6036051884000780b00203484504840360189006209102c20000003150b07003030550003491011002540002042008620014848016440080c8011040354600c0c2040e0b0051803403070180d0065001e0030100001183d1446007010081c02035038800b141c18985249030480841008000340d00c11603051007800700d244000142182940c10503a400141900d80f040140b00070b001c01c544090f0300031000d513900d940c825030640094845030003200090005842d003c041010b004012040b10241954101d4820000f00300f1000c481d13040f078000c05c90545403e50708004141da40030260001511542c443d401080070703080c0b6100300405400c003031030314049508001d2001911000c500300540000d8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 312719928 1250 312718678 312718699
    0x901170a18030806040518031c060b0c10060e010e04110102010207080703022a0d0303021303080a090e01090519020a4811150c0a0b06040f09020609 65
    0x120095408207030212009821415540c50910b4010060002116081e02407410800860761035440f00050410b50710088010f103052580d0f030310f00c01241c0301c000041000306a88849001540c07100810041c100564400e000d0701120803850090002d54801e544250049041c10004102811400c08a0380e00107a003c40400600420480101d01a000e9100060310145000654004140c0c0000320403c03031803255040640b4070b00c2d8078007a0303051640d4010425500015401139010011344a80d004108800c0030a41190080d84c4984542d4a2900072402c0c3d90082400507030144103002c07803403000c9130041425a0007805130b032031321042c65842c0356003c0402d00d0701e0395000b040e1302100c0f50141c94010032240a100b9841b42c00d4100601032540c0c0070a004031410210042110040d00e42140c1041d19461608094085184002001030000e411780d400300d0b007030380c52105000101c04e800d0240309040803180914810311650400400700400c45043e4413038100e10754906540d843c016264003046d21014481110400720303d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 312721178 1250 312719928 312719941
    0x105070807020307270603031d1c0302030703080108010203090a080a0c0f05010b1002030702030735060f0702011e1802030f060f0f070e1c05030d0504030212090117 72
    0x354022148002d5040c02519000b188003001d45003e5a01c140c000c592003440c8501c22000d240886605003c0500061681e0301d1981c0041c5100d07040c0d1100c203c01034111440c420300c01442828a0303060b248200c0c010303000001c180051551003003140b03000d0700401008618504207000a41da65250a26000b08540000306030307401106c1c016149503800f2900b001403100d000c04540b600c140240041cdc40c0485c8182c1404e015414075510000982d03044603806801040000c0c01c2041100e50681d0f1005c015464984158064545005a85c1d243d02d15580110060426013072880c2c3c210707080140202404116803400e44120b519100c021032201c0188014030000a2813920940d00140c0105c100c24084c0d05803060030104d00074681c00282c2ea5118801160342040d4944644192200c4218180e42e00e400140851640c040350345000d00741c40c820802c0c109a03e40304003905a07501e40c2984c00c060483c540581d640e40401040c1030301406048001c0301007140700d41c50a11800700103002d06a480c1c00c04829500d40b01c0000f00c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 312722428 1250 312721178 312721193
    0x80d0f0807110a12030f090308010b03090109231c05030412180e01030209061203030106050c010902041805060106050408100509014212032f0a0605010e06060405010507 74
    0x11070102c50400d40d00d1041040c00d00c140d040101e1030b640c200103441c0504d264201c4001e8807805802c0795140c0d840c1ca40c00d919142000c020b0b42c0001d001400c1c42c0d540d4610020016070300c0040b124000320071300d0034600040300307414000e424504d02400003050700000350300b1105050307449411241c3c000c2d44850005512400103100301d41140707500310001d8242940b000d01240c4021191090f0b4100c0340f0803900ca144541d42c1106100c00720000c010b1617240c3d54014401849100e00420140102100d050000030b280d03142500084d0603540f08202e4403111006c415414010b000d0240282d5000d000b1600344030707180c04d1070302581959440e10104040d0300d0507032310004549510401c2d0005450000e040785451206031141c28414203241700741c0100358400110507081c9444c608105080421104503124044245a49460584850080c0c814022400b02002d411340c05c0507804002d28900c2e04c0401000300451041c80c544141250410782100c1c101d01600d5081050303a5a540d800c48060310000e180c40e81d00c803403041c0381044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 312723678 1250 312722428 312722447
    0x71d1b0406050712030e0d21151205121305010e011107170c090106030b01020601082404020105090d03020106050f0306090601050f13050c03100e040f030e120601091401080d0f0807 79
    0x2140c1c0c0c000c1e1f40401940b103900004100c00401d0395442005007a44e5220300c0c1085440c001c3c0620000b061881c1c2c03c000010141d2010710501d4001c0e8103442e02c2d4000c0d48124035241e440400708117021400b1020a010703d5a00001400c007095007824511344000d14100190303940c3c4a03c0c0301d140002d00400407443c860300c17400c0c008005481c20107030100600f541c5410380580a031183c806841d0051107480700009a10324002207424244200403007040c29400c2084482d107181c003004000340e050000c20480740c00c598443c04008540e80c1e000c2d80c00010500e04103020000d18650070320b402c61180d401807092020382e1801007195811124101c40100f4102c5290021480e18000f6008562140d4500401c12001a40440080d845031a1807030500a8464032602c0100e0040c0c000d54016040c0710440c00300321b0010340900403030b0540c040000c20b0f40c3d201c140403e40c45407810500b6085104055110107003095052081f002c080c0c09000c005014007210300a09500815288881e8100c1040143c003401007100d2074041d1402c1c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 312724928 1250 312723678 312723701
    0xb0414040b1315030f0b0a0506101d1f030608060726070c0b0915070906050d050a15090207060b030609030a03020a0309020d0b060a0e011a0c071d1b040605071203 71
    0x5034504039410600e140780307422280d047c48582010000780652912900500007030740c0030348030980c6100142e102001076001040c0c3d029080301642002c0500c03058071a1602c81311501d259400b20351141080d20707550500a02400803424016032034081820039808460349520000480075503800d1f55207000040300c1d0407408060241c0504000000c2c882c5480c1302040412460103800140701154850300700c03c0310f01001c039124140001d042480b002d401101641c008580111110300b000ca041a09888020b16000340c0b58000d020842e80003404004001d854060364200c100110701400381d906e019100262a0302c200e12840040650024507550981d0003544030001c1039402034400c01988002d0724084d08500021341d2264450554080c00040c64000404d0140c1070b01e08403e174204007494009151006a04062491003881c0500b08021614074612205001a1545c81c0c000090500b8034041c4500320140c20768049480c03400404c4140040c0390000c3c210792481d13501210503440c2e80c131481011001800000043d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 312726178 1250 312724928 312724943
    0x40821040914090105010618090c0c06150f12030f2003040306060303080906150d03050c120403030f0903020108040308090a02090103050f0d0e0a0e071202040b0414040b131503 77
    0xb01803190742503402d54402ca00c09002000b40740d17203d02e01540d105584007102da011002840c0240010489030f045400b41e68070314102112140c9855130b6200980d414441c20041290020800300003031740000c4414402072610000041d41030b07078243c40051a214500d1620340070302003508000b240103001d0440000c1e400c40c280090f0794035143c85c4d1030003134041c09041c4030030740000d8100f0020851a40001c111140151021161141c0d08a00b43d002e02c28080c0540c10141d0034810140854012408107210b6008858030564085640d90b08510b0054004001501c2e014100f01c1c84260500040c1d80007440540c00ca50142042909907490054030340c078082d1000342c02900320b00c00800002c00c04c000003403110704c0c0d41d05640694202070200d02c1c003240c60801049203250700c44804071042103040e4110008a0b004041f42c40c0680d81616500701c02400c1c0c0e40941d002c481c07001000141001001e507814109000401c1c100c03000d000400c1d1847c000391003147c0301d07280480a2950395031010410001c910801000f103030300030b21 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 312727428 1250 312726178 312726191
    0x1050706020f13091503030e0d05190b0c040308030a0b1201020d0b1201020f040b0a030605030d090305010f0c020318060c0709051603051603180206040b07030f02030408210409 77
    0x20b600441e421183c283c0800280c20000410003048070f0250f1501c00701d4100d2444c48207442c0d92011100c0043c0c4107415508003034240c00400200343c043c8580e26400a8010071040d151415103008a03444034002c4c034400c00789006000901c0006c203440100c03904252028004076503101000c0004548888041e0108800c2d840010100e007103110139040b030006520708641e51702080d01c544840310f0a038860044640d058040800c428010300010b000980390740c440a00c3c3c006842d9031030b04e02003490004039098007c0499411501002040000d014a520144038204244a4007503e0300000c2d55a000da5040d0070b42a0701d40003031044080e01c0300302c02e1340e61701c044000c02c0f0351000d80d030350038444000c040c252042c030343c12442103401030000c41c001c0c01110701601c1d250000c2035007110030304170490041030f03010b5107000300c00d02e100c10120140e5111405400034000400c0581e50b01c10003860301400180045040c041036401c2408200601074000c01c12042c041018223581e03080d07401c4e20070100b042e84030f5a049003071114507008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 312728678 1250 312727428 312727447
    0x2404030f09090228140d15030b090a11010e010903080703031b0f0314100302120c0901031218082d060c0901090e06061912090503180604051305060105070602 69
    0x1501c0d02c807a40720301c0b4010400d9032040382040b41c111a07065075141701d0741c0003044a042402003580c0400c03212081107004100305901d07951980d86140041d20044802c0e4071aa1004e0b041c001d903c1d680344d00b00582400d20854100c16840084d008001d0340c03001a1115401103100c0c1c00f0f050007078010030b1510583c011160103549a91a000d09882803091484d400207261204100b010710100017402e010794000038401c030120307145508000303844980007003081c100d004004110549444030141c0d41c0c007035440303110451284c2d80b90540061035003506c031480541442d1105030802020b60049040400e04034000192a14a20000180300103200510b4034644c035031007410700b080340360706641001e0511800260307941081c2603520261000d82c840305682e42540160108000585486805081d44800085050180c0030040a803884011510981c00035034542d00009603503030303c90140300c0ea40a144001101c00d2400c107030801001c1600c0c01054610401c080b40d44402013001d40e0b000348282d0f0402035005405541d90300300c81d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 312729928 1250 312728678 312728707
    0x60608010609060503091015120602041a12010e130c0b07062906070f080a110c0303071707020a050a080106030b061c0b0c040b0c01020306032404030f090902 69
    0x9110300d00005142c1400401c03c144540103c9001d880307010020031700703c0d03c0d0001890092062040c2c4404209500307030300040001c0382c1401c07400654003c400050321a458400c0004030300b1201d00f00389122400030030803442460b4420742681c1c1501e00400e00f0303803142e03038424809000c204141c0380090031a44158000052140c11800180781d0a445036405000091011700000d11000c0c11030400c2030301e50111900306200c6e080020150001501a007124032050103192071b0b002e6980c0c441c414400000e00115001e51400344100a09600c040068004518056468845120b070381d801c5010281404400921034003590380b07a40e40341000d04070003800b0700601076540e544c40d8000c0245210413241e02c600e101c002a000d1401d41c0c42c0023043c0740d260301391280c0c03d10305075148a205c9400808100204006000110310020001c018040c84003144d400140e03207080140405181140e42403a0080381602902912441c01c803414000f5007103545418418001c442ca103809903603110054000090891000c211b01e00f03540c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 312731178 1250 312729928 312729931
    0x111608011503020312070302070b0d05040c0b0306130b0406240e010e0904060f0f020d02070b10050d150b04090c03060e0c01021c05130e061005070f020906030a06060608 74
    0x1640000c2000c50340c0c40c0c0088890610500c0080d42c160009038020400500d45001455860301c00c0c070507124181d4a8102c0580c0b203400081034050307400d031781c5c0701004100302d10202090301604111505c1811460b05c0c60000300d84030048114128510746440c0201980d441e0382c2c00041c050203d030000000d4002d50400c102c1441c1100c442580000342d120001c0712043e50050041385040200a0000e81965455403151001303000b81c541d02c41d048940d90b0300340c545480e50300d02c0a404502040e5102580c3c94009040807400c0c954098030601c00754403000e0041089903540e0421030183c50b402110218090385404c410402444955285500035041080c90b00c100181101c4000541e48220010044041e0034400711b40c0e15038600c001c26001da030000b541200c1080b01c0700050080b14000c2d280141c0f402401002c4141a080e0700d512a5603c211031005201481c58010005444030050340b500604003501c1c0d4a030701901e51403030007010b80140d074407a011400903207040c400e1142e070541080c4103101c0c89a070340c24010a100d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 312732428 1250 312731178 312731189
    0x1008031b010213060807120216080306120f250b0313080d0603061b0807021b03011d01051e09070501050327060a06050f060405210a0302160b04061205071116 69
    0x70058011100302203d00c00e82d1880c110120227102c00e40e4003a40c41c0140c55001404455111490074900a03e00740100805683e00c0804806412010400d040030006841d002144026648682100b8020310028000f0b0f40c0d4003610170a2401481d211a007007640b80c51150144c20b01005040810120a03c41603801031441e0007100501d074425503a00c10022942c40340c1c00d1b100100160045503c40d42d03005001003d0310030b0080f0007800003030300c10304e22a11605009c0e082e1519103026511142000501030103003107403102c0008a40300600d007070b00e407a1103210b849900501500b0305100b4044082161420010381c00101d08a50304c40c6c030501c40383c44022007981c1c1c076411a07080c84010308107130000c03c0d02c0c02c3c02c1152010800c0050500c070305250804082103030311010440e00c8000e00003d00c0540720900d40411035428058042c0d00a0074035031900b104100e0720b420702e50700321000709601048104280d60b445801c0101007000c500700000c060310780b0041280c0c00ca03080c4a6440c0b031071040c0c0e08107a03641d460b080030b11800c444 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 312733678 1250 312732428 312732437
    0x3070309050c0111030a0806030f010903031b0c03050d11040506160c05010207050f09181203180c0105071e0602210a060f06050a05070f03080603061008031b010213060807 75
    0xb0b02502c011240d4884a0144d54041e402c14810b41800c03e01a22025030012001070540b00b40201c1c4007001c80c210760b003e603400d8002a4480044071400303148000e0b40804c001551401803000700b80d9450152040c4900000c4c000303000d60b01c182405804994a05507009040024203007a80c81c0b000036000c5200c1e12403410140c92643d0310321030018080d800001d010048a0029100d0040c0b503003513904001064400418800054128001030001c4002c01c0c090062120303001c116a0b600c0341041e54002c1c000041000070012142d1201030001d540380c0e08101640c0c0002c2c2d10002d07400c010400c5c032141800c90500460010041d40c00400d103900141032a00d421022280d00c803140c00c00d00e80c0c2d58204902500d0b114070440308010803070709062191714490002045103000c14248180b804155660b4449200e410000c1900003d103001c091248510b400c3c019075800c0664102405141030401c9075144e00c030301c100c040e032044460030382c1c00d40880e1007020340584d8400382c00ca0049040300d0b590b505010b40700003011245c3c0400078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 312734928 1250 312733678 312733693
    0xe041802040e06060a06050d0f02071b080309090c21040b01180203041112150928030f0f2c1c0c05040c110f010c1d011b06110307030905 60
    0xca0000d90103111305401070150000c035190040c141d80591151070416841a122100350500f92210f000501c001485003080526107440d0708408100106181c00c491419001042441069510280c00a400102c804082a0b1300c54140340011100c200d00d8001c0c8d039404011301c0420060103410014503040f01e04c1c158507282510144180c203c200e1100302d80c01841d480081811024506005140d141960f070031004940042580c89503112031170904071054a0140d021881c4824800101480000e503041e45200041c00802d4555000d080d00303403d46411410401002101c002c25445121000005400c00ba0424002c0d21011151100945407405a41c02100c0c9061917111000d42106584502900240c2c2c08600608003c100005010004010f80c100000e003800005105001d00980000850050000401c203100b02000350400001082d00290901c1514900e000f690300903600007104c0350b40c0b103011214000b080c64890700410880035070304c400c000007008200c1d806401d9404012140d01400c21a00780 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 312736178 1250 312734928 312734951
    0x9140c030a080f03280207020307061b020f130f020301080d0c03081801110c150f130228150206090a030f0f020c1e09010909030206160e04180204 64
    0x181c41c00c0d06030051a41c1c0c0200020302010610304042c5401a0220960003130041e01003040c520303000366072a0030741425640058420110b02d4108120401031076503003400c025200442c14100d410800c59000a40071b55600700c9034403410b0303880300340300e00400248000812683c3c03c903000d9800290001d01480409124030100d50036464001e070400010a0740c0742e070310401e007a9621040c80090840f40d54002c0080c0d901c03480d014014280a402405c2001e104030024506041064082802d002d80500980c4a207400711301888880c1c00c1c20040581c00c5501030303c019400300513600d080c8041c804010311104000c4091080401c0c030241c01d180d80300c081417807a4210740b141c1d220055000c0e00e4103102d01c00180425511070a8060300c034000c0000c5401c00101d03005440e40c806040780840e101d02003041c101218400e21a50140051510304c1e82103002d0071402c0420404043d06030b8010f0f68070306000d041d0f02c19198201a80d03220351803240c07183e80c20181d03010b0014044002c804056511040110004034031035030400c800c0e40e12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 312737428 1250 312736178 312736183
    0x10b041406040b250b1608060d051011120a02033102090c0d09030809070609030c03021513032d020a0b0c010e330106080103060b0a0909140c03 63
    0x152482100343d60b03d0b00030748244860007204001e0888941140d030340604400700307180031101446100000888a00349032081001001620006e001c0e91040c0704d401202000700e0000034407076108420020b400503d202c480d401d6110280035241e1003010568100c03003002881d81031a0051802064442c521000c1c1d50442d4100c0803604004030310341d013040c0c4d0a10380341c040549421a08a50415018030380d4920f009401070001d81a1132481c541507010460a9050221108080140300002c20092424101c100c6c103540c0d5100760701c000c034031010740f25010061046040c05501400c55000c0b00750419604a030940d60b281440c3d0809450b19042844181c80790b5030416404504a001082c50f03000302039494660070302101440790b0f040940480010340d40d8188644500104104e60502c50600400014003c1c00e100c483d03d080355907409802d1308100481004200302500008914152a031210b4082280810b540c04203803c0700b101d42c48140c071141025400c0f410700174542400d052450031541036900a10700300b030625a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 312738678 1250 312737428 312737437
    0x10201230a090201110d020a17071a0a0e030c100c030b090f0403021009050616020319050706150b0a14030106020a03260c04060906090e06040b0d0b010b041406 70
    0x400303900303864000603100c61942d444003458500c141440041102c559010702d02c0c3c80d0200c25204c0159000f203800d28107206d51442c0310344441006104c400d103481d071142d80d4140582c0d81544000341d840302c1030011441107007540e04580c0040c0ca80c40d0450f074440200c903800540d10909044020b00030b0749005124140240710340149030301e51502400d40070191b200c207810310941c80c0c002031050b400c43c012013800100100142c0101d280c154051001041c0c64240740c0c41002c001130f0740003915030941d40f041000441e501200302030160607201ca030418907100c002500301400030f08800c0c644e400348500c19160200b8000e115070090320141a844d968140001008000144503110038000c240c05a030103600d071840020310032080390200014049161203000004941c03114021f0059a410ba0f111002180c00e000483d0300c43c20000003010203182c035100750791518403850007105018019030300075134581070441c03d5915071440c1000d080d903000100800c1036030b4810b0314680306e030440e004541302e130710b11410300c1541031503c0307020383d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 312739928 1250 312738678 312738731
    0x3060c02010507092309090c03101413050a060903050d0b0d0305182707170709030b0a1b0918050603032b0903020c04240323030d0b010201 61
    0x144085017014400154010480c010024072104404004129185d40b440140a10715000003050a10103400070582010080011040b03081d141c50306041555003066040d5420601400340c4680191043c14a030b0305007410f111014006a08010240c0c0415620a00403c3d000d0700a11003001204186800c10900030703000c040207000100d00340f040070002c070a81c00740b8401d0948000c1518a0700701c6210400b420541440000c68540c0d0001c0040203480c030340128214188101b5011a401585041600981600500d00000d8102c410000024030191043d0348101d14448403044100c04a817407080b00200380060b10b00640b22000807052004040d82064051a40a04c0b4020042c60410650b16003c402e40d102420342300000f02c0c5254440301404142c0d1181040649c0030341e000e05a812803880a00042d01d01c205125600c0d4403409001e104512210440352044d603901000580d50311000003a040482142010760300603901001540f6800d0b002c685e0710006100d642a0001d0001c070340a44060090b500404510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 312741178 1250 312739928 312739937
    0x4020a0b090105090406080c030705090112030c060b090a1a01050f040b1303020d0f021804020d0b07020106170f0f0c01020d0e060706020a0804060e1c120917030103060c02010507 78
    0x1408450300e800003034900c1040614009040c924403d0001d0305a400390341c45896180c02c14103801c10340d81001c0c17101d0009010161116001940751961a0001d0503541c140a000c008611031b524003009965048400d2074100144a0398071802c04c040207100414009511607900d00003115810003a50140041d241411343d016240d60420b840e00304034442e00d40c0840c503590b05050709001c0100040c0d80d40285890b04078001c0452101c0e0600301c1c410721140c80c5162441a8406c20030204220043ea91400814109988071203008032039250305105038090700983d00440b00310319810054004130752000a240c4805285141100d54004580c80c1150320341c06d40004580c0140c001e0300c009a0070728000c50051100036005016646030046c0c0e61904401c076008900310400241001050100380070039809101601a031a101810151140007807141d040180441c902080c450080c250005194180d80180040398003e25090041082c80c040649558001d010880d0683e01d094800c417035907881403148610501e2a0b840d0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 312742428 1250 312741178 312741199
    0x305060f120f0106081f110f070c0312230405090f130b07050702030f2e060e130c0602010507092303070602010c27210506040f020a08060402 62
    0xe01c0404452181c0c281000d00c00c030750321034048000910803000202421805800141c58202e4240c81c21a12605181240c508094201018180c0042101c45150785007441c65070714036003454400c442d004203610107000f040314690001d44450708100310300045802021601e0041401441e0700c43d150003107004045d0408181400034000100c020442a04401038002d14000e016079640d420201880c2140c038036001079800b180c00401c50404110031000e1445502c003030003000c00e148030050040c1c211410751000c0781e0002c005800c84c2e0b80c025444400900344600c4550000c2c80d0a80c0040c1580e0b54804e01200c030804001c00c0050440c0c4107205a41c00748100355500b0003030707034905000d41a40494101c450001c1c006220405451581e0811004000b071501c0d40000c500c640f080040074168000c0c04030b4004100c42c41055440261000360850f409a44113440c99120181d2462030300f189104180078018440d00c1040306102c20300999150b02200c462007265022301040d1201001511030f8010394000350070200b0002d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 312743678 1250 312742428 312742459
    0x14090c0304080a0c1b240e1011070308090111070303080402040f020d1a100201020408101805030a081f120f050f0304240c0c03030305040201050d090501050601030606030506 76
    0x500501c0c02e1007031490107220012198440ca481010b07109001d000348503029204001d170758a04000300c1c0e009501000d2001c4000304082d0043c01c181e40c40b080407807080b00748006000c5072070300403001c66810f5000c2200322442b00b034903031905600650001c004940401c4070507658081c0c0403000240c03c010f499140e918401c5a848a9003403002410408041d0707200243c003801720304003024940c450100062140d00c500350038400c0351818002d00c80000c0c80244116401004217100c103510000d44000c2d1507070402d2001404401c9040c0050070750180d0310000b00700380400203e490241e54030490050080c4242c02083c080505000000599520188203207400541101080f4000c5850581d003a9516406030301035130301c8031fa04026064150740c4260422001041010300c0d40700540c0c41c0d0850720f050440326040c141aa400503403140320124201e480020304150700d0b03500040c110792003941a2540d00140310010300c0040076928060740640000c980c054002454000001a801d1081c05001c0c05820054103c01020b010303030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 312744928 1250 312743678 312743693
    0x32d0e101e110d020c0c04241802041a070c0503030a140d0603020307090e010e010b0a05060a02010e06070f020f120d0209060421050d0e090f070e180114090c0304 71
    0x56601010b2400a1054882d02000c500003007001040c50006484441048400c0104a682d0300070400d5a003018428054100d81c50310f0b4030700c000d80d1201143c001a00f0b00415180003e441680c12130b10074201d850341c0200740400c0c86401703090710f14400c0405a030340d181c0320010b0603640d008000c084000602800904540420742000900091032000804500d80c0d07241d0b004a490800680d100c80340d070560340c40002c40c0510b03083c40340001740c0c1512030090151907403010005d080031519015035403140c00001822806075000354000c1c110182e02106480c0702c0c0c13810b50030151140f040c02140101501403004164201c0d90007281401000004034003090a082881ca543d100942107441402e030800c004200201c0d140c0d150800b1501400d100b06401c540035501450300904054500600805100c00c40c40740144561354203040d194041900b0304001416aa01001240c5150140030840e400c94011610390b0641c8010b51617143c146c40391003040303078041d440207010b00a60100443d1103004007a002d101090005810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 312746178 1250 312744928 312744941
    0x170c060f0a090609080a2a030f11060903131512020f0d0203040c1e1d150612010609060f05070204020703031112010f0504110a032d0e101e 61
    0x6240000d41c00c541d07a52954210351102030203417000d0f00b011070740e80242d681c0b0076920358450480390080c20880d0021000c01c5100041c0310b03002030901c0140c4070703143c0c9030510075202800c4c401c104400301d40403030508140e130365120390044491132403c0f0410a004960950201807070801c0700301e540e580079a118611480c0c2d1f0000d4105004100e038401c005c20000218062500245001314041c0d07502d0071446203803038842251000071030219140000c1d02c0c001000308007840402c901800018151008050342c032540c45c0c24020100780441540030402040309040c3c500b070506018182c40140c1c6075907080380d80f69601601c20801144424000503002c014400041c203064002d00545071017418045001034041d840d00311560401c2003541c00c002c4800004000e20701529013902c4c020729064808000c461480034800d101d40c401d80806038141134807641e5062440503a05001ca214285080305035503502040091340022b0402d4000d400160f1203090200d5140d106607100b007800b280100308448080d050360483c0310024182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 312747428 1250 312746178 312746191
    0xf0b0603010f0e010e010b0904020d0b04020628020f010e0304170c040c020f10050408030c090f060c0a060b0303091020190203060a090816020d020a080703170c060f 72
    0x40700d1a00350300b810142c0c000c2c801e224078150f001145c00100f0310140e070b007100d48082d86548214200f5041c00f0240c1c4030502c0c0c800d00c83e074002106007001d03541c0d4008103125104032001581d900226110b100104100d42d032003825000341a40c29158800714107181c1c0d03801e0b20144181121660004c1008201c1e4000250107054800c0c104015030720752860301c0c0001411910640d4404025030444440c8152140080c1b2203207000110ba044100107504168403500310f5408000d00b41400007000203601801d03076031003c4a40c1c0d24003500408040d40c5d00d2004c42e805882e9000800d0444031642001e041d410180340202c165000104090f00707106000b600240c0482d120717410443c0e01d100348c09010414062040041c07001702c0c5e241690724071194101902d88149460407100401ea421494544070920000440d0f01046400040301d56168003403042c0c007400003440440555000945c41442880c001031785400105410049034021456a207030710285030003071211440f0b50b00c050340071500100d0000e00d000040701015a006139 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 312748678 1250 312747428 312747431
    0x5040e0d0503070c1406070504080609030406050d0b010509030d030f0f0902060a030216080c0312091903030b0307050901080109020f0108090705010c0f08120604150f03290c07020315040f0b060301 86
    0x2400380c401e941c06e010099442800054000606000c0500704200c119000941c1c20000c0d841e1074a009001030550050ac2030705031215444565050031603218400342c5081120041c1603540c284c000ca180900202008000301c3c0105052840175100d5020301e1140019268000d0321640ca840c1041100700c00941c4088500714900c034140d0354010102d13500001512031003000500959450b8043c40c840e981800004124410552200403c042c8600d40071060010b09a81824040341d2108090006410540181c10040c1c004099030000900300005412041090303000f5070303000003400c4044004554440044950313200380ea001c40c0b000c0125520400181d86201e000b200b0201c081015a590b01100758405802c00703000000000074400145428401d005a40780b0928015540600c1c0c0329001c0e00545107844003070000620b104c0c0c1e65115603483c000707064581000c0241e07016540303814501d0441d1a0403001c0309901a2182d0015400d100c6568031045000b01c3d00a81e41d6040840039580b01c1d000060014078150700b55 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 312749928 1250 312748678 312748703
    0xb010b07060905121309090f030309060608012406050307050322080f03040611030118050c090d1b05010c02130e0c0402041d06030d05191b06020405040e0d0503070c 72
    0x30414000c0040d80150713071405560f185200a00e000106001d90004c0e4007242c43e0800010004410101c031880c400c0d41414085041b100a090030f02c020102d56105111550800c1c24085150951419416103101c643d000c061840b6101c0d134048030a070000300c0d18100402ca081000c00c100d0351200b401c00c5646280516525299161541c4050300b54010700a4102504004000c2c0710411455016149015407064404c0f403d5614100064080310b10740e680d56008540d44101048104401404071526003101802c002441c4809181141d4940000786a00582480c800d00104080d0300c94001c00f4117090300145402c0f44240400c2c984c1c0002d0480c544d5195640c03007126030f1511551150300190004041c0c460101c1c40d2940804020880c801000700050b103c2d410180b0241c0030590031406513008006406401c00c1e01d500822403c0d5800607200f4818000c88090807120020080990020015600d080d0742c1801014401050180e43d100d441100c5400b04005000044505100f254600c001502550150b03c28 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 312751178 1250 312749928 312749933
    0x717010b040f0506030c010e010f0c0515010f1701063c030606090b030115060c150912112109040605041b020c01170c0904020c0d0c031b0b010b070609 66
    0x45900300d28140d07100c582c0f12820132405107024040a046000282450702a141407000000e0642c50014400000d20019840f05024440c00700804640c2c11300c100d00900c031030358440f0b8510600c1b03040d500c40c0080c9130504003c00c0c40306010601903e0102c3d03401c5864040381000c03084c0030254405c8800b000b810b0303240c2800702c1107a42e030091808650045005250008a16090600c20415a40e01d4901c503802a814819501108240d130082001143d0796860b0804000542d8035102107510004c0c1d080d0b1650380d0800c1c400200b88060503038100c5414007103480701c8900c803d5010036241c0f40e4109151003200044403180c880d13202440607004015111005000240098544002034200c0341c450904c00e1101c0e400812089500d80c04103c50800c00a0900b86010b00742c00055194411a00041030b107500301001080410154071150142c819480300070f81919018001c01e80014000c5840c030b8016800603003016480030b154000349a000f4025034200c190180d07a41e00b000d902c003189511148080741c800c2d9445c02103401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 312752428 1250 312751178 312751181
    0x21c050d0f0f150b0405040c030603080c030301090501120803040b100b0d0b0406090b030d050d090605042009010b0409020705070807060807030b090f13150c230a020717010b04 77
    0x5010001e0600040c21855000d001c03000c070303000d00590321030300400b800d4103000d4403200354140c5007104c004071800701c1e01c4600c86000b18007a148942c4001c0c4074030004600d662b040c50303011000e0340c1a00c10360a000c02407607a90300031004103040342e0038016009050400c00b080109403280c0c0e1030303070340022840240c03000903940b00c20001c00c6500041c40c0010362540c43d00b441d4102d25181c00f903d001030011100070b00004030504002078450000c005d51100348400001d400c00c1d00a07443c1c00008040384c211004000a00c0c003400c0480c0101180c52084203c040c9460200c03195160521681c0e0507521841c0d00107007442c1c00d00000400951108009803000d10a40038001000002000704001070315142d0740c0c84446042c0f0000141c151140160300b00d00c02e040550420020300c00c0d00601d15031009045007982d01500d40d034180444070340442d1810184c01810000d0064100d9046601d1115080c8660b101e04030010403103405092074003903480160010b0700004030411240360510a054007019038400005405600240000c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 312753678 1250 312752428 312752441
    0xd0e060702030a110703020f09151e04050604090b06190f090c02061b0723012901020c031908190f030608030a02070e190e0604120f021c050d 62
    0x50b07000040d50340f48154405015407411418000401002e800c503070001c3c5400e4a207011090080305141d001500d01500d00798a296492005095403600d070480280c2203240030105500c81d401039040c00702007240d908142c460002850f0b0084004442030b112681001054075000200342d440c0c0300b04460104035922040c1c0c42900402a40e440080d6058203d00c000e82000c100404070241902c00b40c0482c110b00c4000412035000c150b00c189010443c8a101500982400949200016135071814481c0604208c0e4100300308821444003030340344516141100120b03640c2c0742005409406820407040c0c0000d0400d044440035107248076610f00340c00c180311501c0da280c4041441d6809030000343d00001e007941280d0944600400b5040860181d0328054020034065680d42075441005050032802c000524504000d1a13580009081142d042c03200c1904904120369030a0161380c00c1e10080c00d8924000c40c0b0a0003604a100f0340e00c01900985951a10150b110001d40c11210b405014400708004c00ca414042d85d20406c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 312754928 1250 312753678 312753691
    0xb030a06030b010f0305070b0f0d0f0b151303080d09050d020105100b0315010c1401021305040506060a12020a05041a0d14010b0409090606090c11060c090f060d0e06 72
    0x2542525506080104002c10b90040340400c038083c101307101140020900b6002d03128000700b1295074242c4d031903d01c0080e200380e4400c80049858030414500e8107540e034106c5804000100c0341c01c5c00350000400e4810007446513070010503032504002402c100103420351010b000581042400040c0900c0c098844c0360410712403c0306217005035510800c000c480311100300544090040030544038254640b082035005d061890302e00250600206018540c200322864070f0362001540d08074025516041403980420b20860316020b00c0c0c0c81181040c000076010704060060b030f43c80719610b40d15075140e80e9030f40104a0080d8000500c00341044070411002c00c1492860170710f000d1615166210310b58450f00c0d03901c403008503400608a9091819100010031010b41802d060303d00307131600c401c000509440f01386000c0004103000c0d0301c5402e1503070804040000b15500301c910401340c801d0707030001d6a615645100003644684104505035522208044030985142400d101401440280303820001e00400b54000151410104480c40d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 312756178 1250 312754928 312754931
    0x110a020c1e1f09060804031706030c040204080705010e101e17070504030302010f090c05011b050d08091e100b0d0c03050d0207080c09040308070203131d0601020c01080a020c03040b030a 81
    0x42e40402c2c0c0c1d1141c5a1030050003940f4185c81541032a41c1d000b804045000d114143c0c1580c403001041850740c0500c4030706171411008004641e507035661262581c8800540c4150380c085500c5c61019460350030000d042019480207a5180c2d4005010311071000c1002119140c1e20041100410084000880a070f622a0150b0307816101c2e16100d40c654500242900d00504121007100e007020003a40c0002c14070306500b8241d50090030080442c02403803c9003001181c41c8180502144945020800070741e03040241580103c02040964000414458030803010540c15840004158458042d485403000958810061208002e01c07a442c001da0580b51043c082203940c00c1030f1080d03007001d90b0341a03040303404102100042c00300c0f8000c1d108c4001000700096095000800141c1031000207c0000c1455100340121494080b03841c01d1810015212500c1e01b100014440049442c40071080c00700d40c032580005441111120140d56a600695805d00440040e40000403d208035100500000c108180c001c805988580070b403500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 312757428 1250 312756178 312756229
    0x6031803160506100b090901051314010f0611070b0a031d0607080604051b09040f02070b041b0905010b2b06090207021905061207180905040501110a020c1e 68
    0x40342d484030130240d4000c1c80641010400d5400a4440f02101c80c1101c1044440900641801105a015015608440c2c900d1110030700041008060300030400d083c2c50325070741c454080c80e102041242d61205140500f0607145c80c28802c0c56000341c03282d04220030340074018601d00d038101a0402614906501a500316021030342c40f50030007005090500c14240e1107684113000e1f290951240c03036103c03038900c04c002c00345004076107845c080460801ca0760120790407aa803060f00b540c428070f080d04003215029110900803c0b10751640000145c40d400d40c1c0616416520282500703850480c071040807030700920840382401f40b030096070381091690004d02d01c01d40006210501c005a5103680e10b10401c149118024660912403180e03107014001600ca107029101c10401d0f55000740300350303101e0070300c1500c021b903004490500103c903100021541d600140c1140380031340d1040c0024450b60b804550301c04a0f6024440460005038868802d4441038602140a10500d0300c201e410002d0040b400804a040645030240c107842e00c014485 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 312758678 1250 312757428 312757441
    0x1050433020f0d0f051c090807080304031407170703180f03020102070506070507050d080c0a060c121b050a050d0905010209010206010605070b0420041a010e090606031803160506 78
    0x6803e1001d2035490021110740d040c04016000e8007518005840788000103ca070f9015418640c410a00560403519003900c8401511b4148690f0f44102c40071800940304c180341c00d0f800b0070054261041203500c045030300e910140b02051015590014102030302000310100c2d001c5024003071050290080c0c0100700c003003032180c1d007540006803501c100f56018a014402c20040900400e501003212000d546080386c10030300c44856410010120301510035043c01601507213040c0000c0101682c00800c40c400292644c1081a41d2000030310120b5040c280103841c100d1030210b14440c014400d6004103408801400e00d1400d15801da6040b03030480d980044100c03026940016010b0319580c0400200340100303d589026450440544c0d10100c0d1054040d20080c00d620201c0c03103c0c4202d40d622512000b54900150040201c1109003004013032590343c0d1915240400c10821103003a00d4141644000d1048101404075451038803110380c0416210040d02c0b14200728001481030000480b6a8081c00e0401c60107540200450f05110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 312759928 1250 312758678 312758683
    0x1a090106032309190311030c0c01080f070804060b0301060905090303010f2112111f05010504090b040b060a030206070803010e01050105071a07023c060601050433020f 73
    0x1c150085208046070100311640f0030005080340d050707111100e82020001c1ca850180c80b00100e284406105001c04161810650000520082c000c18242d0300d002d110746a240740c8008409080e1226400692244009004188140c0000d00c0112010340002400e540d21211001143e1054800c1c1001e500000010130201e03410807060f002030b0084540c105c1620410a0901d00068a0724a005150080751654030007218021159841c40341c1410003031301e055400c64800c86a101c84110903403038bd0342d80703001c00100e0340d41000d10407003c0c8203a01c4180861f05440740c3d140c02001140080c80144d00c284500c20100040c0c40e110007501000c2e20030b4000c5612541043c550007590041604003604001040c0131a8001c650300c0501c844c0c1d0f0803070b034407584140780c1c03641c1e44101d0500c10281c004802c1c9801001036840f8a24202112980404003200c0c81003990701c00c55003040d00d462060751000d0000d40184000d020a10206c41d131006484500c8000303c450340b1421051300b0b0124102514140907030412041d82a0b86d8506 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 312761178 1250 312759928 312759971
    0x6020d1d151209190f050106030804090509070906080a02040f02040b0705030a0219030f0804060b0402040b0408070905010f03140a02040f05091e1c090504020d0917070b0a1a09010603 80
    0x6010241c0004440c0c0d0325030385413200c80508064a1221503e82002c1403000a6001343c018641282503165903540347c032745086c082c000c2a1015000c6100c1c805000501c00803e02c1800c099030204000391150310110303001c000241050040340405140d00708030011300b10020a001701609031140020350340f078004012002e420a032241c42141d2022a800307d45000103540010fa4100c3d12401d421310407060f48503824100300820110030455002031000034081a03900140028100b103400d24001c64000e9038440c80440e0a0720401c5c803403000ea03001080800c2c80010401004101081511402c80b95030140c1a00000c0c1550012855000c4003a42d0b00240141103200703004590a43c51000c24844602d20f0003020309035502d00080202c50f000100c182c0c240a40307840b8a801200400001300155180d404030401c0500a00070382c48100c0d84100a040076100c40048035064844407600801c5c842240d0391024107580c050683c140001c01e21010207481740d9181d9a400c0344c41406008030740e40009851000100c503070340000d007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 312762428 1250 312761178 312761191
    0x9010902030702030703050703030902090f0105031b13020a0216060e041404110402091216060905032a0d02130905060a11030610050702030d0f030b040606020d1d1512 73
    0x1001004986030f00042200c1700e4903850b1030400d5036000a07040c220000d042c02c0b80000d501407582c0b0184154508034002060507503204405503040c0c012200c1100441c04400c50000e600145198003451400c4d0440e0301502e0941124015180744c1c03440412f4840301411603400141c0802e50340343c0d4158940c02c15100300d074061001000c0d001500d05013521811994454011094403c68000403a0429a01c4030b800c5142c0795003200088401702045071280c501783c82d2880c050080001c1c4082000900340c5000106120341340344224142042d402200e4040c420310584c0031401d034200c00f5080c484401600c5080c0d08407803d05ca280750010740100546811400c00300b010700343c000e01a0400d0715100341d4154441c100da4200c034003240c1c0698400ca6003c02901d0071b000d2124041c2d41806101501031420350403034052240700705031755001c000138075201c010007084a005004100040c2d00c14290707111658019180c0c0c040202451445203400700148001030702c1142440780250a580d00440e0142c1802400415140c1000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 312763678 1250 312762428 312762431
    0x30b1008030a030515010c0201080a09060e1902030c010305010f0905040c0b07081803010b180a09050102030c1321060c02070503240a0902102307060b102a08040e15090109 75
    0xd9500000cac044a0003078420046169a007080d8404c01c88590300c01c05881e81000140d4003100c3c800c1c1120104440703190006e9000340503002101025620a10906041e2030380c00001300080d034100307111b180082c00300031310494566030b4119012410000000280840d60f220b02a156607034800c0042d02c000410b98100200d02903810022405540c1da503402078403204c0c0039403641c40790701c55440d11a401c01078080d070400036100b0751000041c80050320030707003004041d04821012100e0a05949040c081c21b01c05441d144101000c81003010b6100181164000d01a05001031048806098440300000d061903404e10075079040340500020525030035203540c8c21079401030346014100050710a076004205580c07a0049203804000311100b040f0f084006941c40d0904903601ea00101d0380b00c000900c1c1c040001d2042c14140f030300c10b1a2103515403000c1131050f210700700b05800301044140045c44044240504a81100003210b00000c2400042a0480c1000120344030391038a1070884e821020351000c1c00240c2c1c030706820174010075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 312764928 1250 312763678 312763697
    0xd0e01061404020a020c041401030b102303011508010219050708070204020f0409020309010c120b0a052403090102030f060d120c14060a2c0601030b1008030a03051501 73
    0x407100c024010a40e820640300542d84100f048022070814000d101116805464444482c80d15000b032060f644c1a2403050040b032015403036034415002080090f1213040c1d888054444d80c1e00890340442501140d0b41809000403c403165105140f417030348400e40e0001c82c4682c4d40400e048000c0c0c030112000d13841d007250504016203001440d0f115030405100f1424003901076900042c108507200c001c241210002e10380c0c00002c54a070b0511013072050181c82c60084500c000b0b83e03155240b2840800611960100c401c00400c401040e500c1d006c14000000c016040324030444400c031104a031401c000400a51258444030001681d0389019004030310780340c2c0041d0103540079040015080340010104800c1361049452824401d00349690b43c588001a811382d10719100490290206010200107260000500300da80076070f0350b41d6110000c0d0b108015140c450445521164024030041022500d0541e8840e0411802a0450811526024002d24580c8121100000240d0710b0040120910704c03004074500c1e90f00c0c2441c044140d07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 312766178 1250 312764928 312764939
    0x606091a040c02070f0801290607061a030d0207030b0c0903030403030e0a051e0307060e030a20120601060e0d030f0f020a0512041e05061b010b0301110d0e0106 70
    0x40c00002440580a81e94880e10014100d0003000030b40000d0a200218041c0705032100102c034040c0804800300304805952400303900c50004299103060500902408480c1409803070344400000d170411a551251507604039069081c01c1e2018041c01c0000001a00203100740f500e10b141c121100c140080c03619141d1703102400031400c165030100460b030850380c152401101c3d00080310b00051400c0f98560081d6031012007105100d42d41000d00198824220f0304905454003d40d6914040c1c0e0040c4076141000d525800c02c038080000902d010b00745d51141e07844a1740c00d402200e48800030400c0140c01281e03440059001000400c0381e160701003d180480d0a054a0f8240340800944e0301401b11404480c042d0103000403640b44103210351082008440da19041000c4901c82903651810303400941c02405003e111094000710f42001d02c0480c2811803c03a1005402c86107001140011300044100b8075a140c0a035540b41c80c80340c03036aa5424011501601600341005a503102c2d000890001c83d01c0341210300300b0990601e07404201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 312767428 1250 312766178 312766211
    0x3120908120301083d0c0e030109020f150f03012913060c140106030b07091a160c0f090b130905060121080301093305041503020d05010504060609 64
    0x2818005e240d114144030311070710800713400e207854140f150401070410f052000c80a40d881e00030f6040c21025840722100c85a9241c1858242d0719181000f0350404040e581c0c801c11030078001c200d10300b200c104040f0303035041c0084000c200442d80e1003070307000401405e20090200f40c0310881c0c11281d4008011030340c84510b4005002404800914a8410342007446540c1d0102070901400300055200003450900030070083c2d8032803034404070703088090300c80c06c6c000b03a41c0d000c01140d140613099032041c3c0665800e16085c10010070246072500d000c102c0508948514001c0302c005400f000702c01e03400c0c010b0083e904002c2101450300040c0801c0c9060f800c010026039051995981c00304601095003810340d501034141400003403918642d060045080302008001903070000000600541701c4d8048600c0f8448036180e031180745400b4840d04075644a41e00c004503031080032003042085181c2a44241c006584407034240120503030325000a2144e07606844140c801c0d9468008010030840d882c860200034081c100c0007007001c08601510000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 312768678 1250 312767428 312767443
    0x10305062b08040902070303050a06060f022805070f03020312031504051b0705160b0a020d030b010318060c1701420c0c0605040b0702190312090812030108 68
    0x7250494031020424094648111009090018800d540d90403285c98010003c200c119614004a8500600450b042d4031460307405420030000da0040089a40c1e41010b444080d5400b003030a5204c24282d8a502d00150342400444001c2110040c01c841d5030b407640c018503080882d031404003000804100100400000c0030301030b21165081c01c5c0e90000b1141e4414078881c4c1c0000c111040216500408903240d401c00c40c000440341c0c2c3e0000300040c9603c805d0340d100c8142001c2d0180ca2442c6026811090001c01718034406e50015025450506d40410881c100020740e030003208081c101a94581c0d12401c1c61000e4a400143c19400c1e20314142850200d9072420062611513064014685000e84c00c3c1081c41003a01e1500c80c8011602c202d210a0001e510420309025100f066240b10840e01100301d082c00140301030080c001c0d2011a1101c0c04014644005036003080740507064640d0380795000791440c0c0040041100b9256802030340d6202c0d25541d2245040403000c03031070040080e150030242501040140a090001300b400c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 312769784 1106 312768678 312768739
    0x4030c050303130302090c0d0504030e031e210702090f01061409010c030804050f060a05060f03070f050103020c071a190c050a08180a0f0501030506 65
    0x1078880c00385002e43c02024591003400c01c09814009a0254040d00c0c03141e0451600c104e1407418004c0b18010741d402c2c1c00041c402000362148d402d0400c00219256a100c1c52400341c62442c940d00b81c2d407152840b60300701c01c40e028481000900445001070320b4075194020038030035840c500903003480040b0500340b041100050300080080c800e488400200d4250540c103950303240319070403d0345080d15851006003040714907108141c58410803c00504c0103501891001a011a0390300f000410001c4110a04505a01c0381d000f483d02080110340c2e500d00402166420301f800750b02c0b02c00417402c0e6811710f1181e83c03000040c02071030308031031000301e42010050505070307480300114000c101d40b5181202e10701400300000700190b00c5490800d000c116024040c0c04090300c24120010f4180002c400719003443e01551000d040d002d01d0074014401583c040c051690301080c01e1311001c00c1520a0386022700000c0c0106800c = true := by decide +kernel

theorem cover : BRFrame.Cov 312589928 312769784 := by
  have h0 := BRFrame.cov_init 312589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 312589928 ≤ n) (h2 : n < 312769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
