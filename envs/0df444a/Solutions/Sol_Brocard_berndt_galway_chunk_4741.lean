-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4741
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:35:13.401984+00:00
-- url     : https://prove2.me/submissions/632b0117-cac7-48b9-8ff1-dfa8a86808bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 852517985 ≤ n < 852697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 852519235 1250 852517985 852518003
    0x70b100b0915091306030b060109060212030a02070c0305060702030901030b091605130e0903091005030c071e02030a200a2706150302040305060a0b130902030c0402070602030402040605030a0209070c 87
    0x2400c201020b4800031b40040310403444010820040e035a201e0b411100a108600c0185a0890070f11040320301c504c0060141c125164001078298244103800d60b41d0b100641d4442e007180c10901e0050740094898201c5031165001a0400c0c0a0240078500700da03e407400792040201c841005007880d081035416902c0034032860490640c8042c0040c0003d034181c1041e10411200014503610420340e0100611030001c808078000b48039050048c41040a1003100340c07000d0300ea2000011a40c80111301c008811882c2c1d004000f5450302c100e0f00c00c40304002c44155500c3c090181d0100c50501c02c141c3e03400308070600d0043d028003409280c0c2c414000d00a01140010b10601d42e02641000496580760887c04205200e181c0d07640d4040b0b03800040400800c00c2c200420360344080c103084108180d0100d00001606583e201d41c0e41e012203600c031403e200541d078041c840d0102c000740c018001c550b580502e2600b50301079041103405911813498560001800d04004c200a02c1260b4020b0404215540718a800c1e103c1403110082543e01f242 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 852520485 1250 852519235 852519259
    0x9050d1203090323040e070504030b0103171312050c0306060102030706090f0209010803070b0703111b070e010602160e010609210813050405130c180b06070b100b091509 74
    0x784d0b134000040805002c0122035483e4180b1a81841000d0050004810483c04000c1040460720300d02c45141500d81c42081d80d0400105000c619519026036100420100501c032400140c00a50b1040444618801c0041d03030504640b0008254031014100c07192400360b0000c02400d000500c850340007c1519104004580d2010901d0b0040f600d8000c00343c10210081d40009198002e00c000e038050380c1d5010010349401d00c80c00d0300c4018003c01e28007502d032070621041c101c655440700f40507040c40050702030031010300201259a9509070003581c40a100c0501c5415401d6482c012070308825800c10749050301c0c2d1640b0395076940f901d044a40340c0c4040702c1e215604449030800341007100046480d001000002a000c0c83e410340581080d040000b203031005801d0701802c00c19240c1c088002a11403420f901103601030410307a000701d000c0b452158040c00000400e581e0090340002e01c6003c229420300c07403c1c020b1907180c45c49100d81da155800d103c2c15200e01400990301141001c00d80b91081c81c100b0040c480540082c2860542d41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 852521735 1250 852520485 852520517
    0x215130c0308120417070c05060703030f1a130e061605040f090902040c0c02090c130e01030f0c060c050c06090f0603190b010c02090610140d0c09050d12030903 70
    0x1c1c002d4940f80300844400c000b84400e0012001c1142016680d5070b03015803410b1403d0340c40420340d641134480c1e44e002ea0f00116410b42418041e0340926000000b458003031260108041030200000c0000011600c81d2104074080422001140f0031400c91001340c5000b4019516a51441000721500b5910141001410000130401040039003000c0c004040040340464103507002c0c4104001d44100c40801010040385103042d0025031b0300c00204c00d800034201441d41c7d5850402000d00c4840e4801303904075a2821000c00d0000041118200d02e840140d07000b48012030450391941012141480503410240c525480201c0c950108e00d401c400814070f10000030628401004280040340c099081222503400f64900c507003840309510790034040c0c10800c003002d180420211f05a540091240d4001030b1a0f54000c2038412041d084160240d40c8030411f80145808040d200c412003420b0314080c05058604d00700003500503000003100d01700440085a002d03031001841c403507916400700c21401403241003400d40400007003071400d001c40b03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 852522985 1250 852521735 852521737
    0x80f040f050f161212200102040e04021f090b0d0b040906020c07060206010612050a09050105040f060c0507350d0c080c0f0f070615170d0215130c0308 66
    0x440c207400c081d000242c0354030602c1e1003c100c1503200c101042c41d160718600c001140038683c0e000500c0705041a220340c0ba84507040d90004d000c48000020603600c0001d002c500341ca42007a15510681c0b08423481a0001c3e10081c0255680301c00006d40740100300a0345041c0201e00b0310002608180020130b00015500d07000c4c000040941c0c00280e42660410b500198140c680c0e24240442e2000e00054001880329501d4a24010a800c0302c2c0d0640203c01d541da074001c5109804150030918405400c60004e2101d42040c3c10b2900c401d020449007182d01c1d40c41c046001c181c1c10b01800036202c070359800140c01c4800094034021003443c1041c440044c480303040803104d000107201c1884041e080c1c2c040c040700001016400450b01070080031024000340e13841002402464502d04840c0d00301c1c0da11900403031801e074540e01d80b03180140c09041c040e000408044650302c000b01d00f401c416400445140030120440c0c110500007a07041c0d84400d07540d400c90b130b001d44103031000480100c14002000c2c603c620802c140528039589885050103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 852524235 1250 852522985 852523003
    0x21e0a06080415050f06120106050d06021c091707030c020a180c050c0c121513031e0c0b07090f0b03070806010906021c090306050a0504051b01080f040f05 68
    0x1003140d150510052141c2a4180c3d10540941d070010455030801c050024a07045000380a54441c0034944040300710320800b0742245e0003c0101800071304011401e850080c0103504030801100c024610402a031084140c1401080301c03d90f040050301c40c04010702207541a00d40d00c042415006d1100142123100140c417017031a000001e003c6a1200040b0031683c09810055407450840702c010031609000032041d0000119004000301412151a0440d051120310304d810400c0d540c4480700c40c1481a010440948055000896954840c1d0f445104241d40d199880c40a01c450000240c00501c4001c00000004d288060494201a035410a2148113503590700a0041081ca5004525180404810722800701e40180308280c0028090800000a0f8248480250703150f840c031181e14941115005400b0990703002c1c002c000c0203143c121800340324a1610f4480f84c0c001d44011f580c2243c1500c40c20b620300e40c0c44040c030344440c003140300160754400141d00c9079026440c800401410513140045002d01010002e041007040c400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 852525485 1250 852524235 852524237
    0x3040615030203033601080609070e090c07121b020f01020102090d080909060a0501021b0a1517010905060a0e04170a0c0312090312020d110a020a0209060307080604021e0a06 76
    0x101e121129850364240500d804440540070080c45005c29142c1e801100b901e90003d4159401806940c2e03c10702292140401c400070368005042c8400d008940e2100c2008100d00350046a00d846264820b01044540e07281c10304100070303031031400000d007130041c0303001c0408809014052001504100c0d0480c0060603501620704101d4100d0070020b030700c500300d040081030660b000200b110750a92031464140041c1d100e6000b44000e016190030181101c800360348408a1402420004156205408110801a0034950300180700414190040000100310300280a020310690002e049643c602c0e1521510f2a0340341c4025104407551040d170481e00f016000c402c0003400c00104e1981d10807003581c5050401404180c2909444c16209041c10381500200303400c50f03d1056035451040006a852881402e401c00802148405003d2410f0018500841e42d034006100f0358800c0c000c454000e41c2e91110010140e6400803032248600e103810550014004d4580351000690062008094110600102c1e0018060703140c00e4020340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 852526735 1250 852525485 852525517
    0x4121803080904240e060906090f040c1805010602010f06081f0618020316020102030606040e0705270f030106030507120c0902030405030406030b030105070c17070b0114010f0903080304061503020303 87
    0x1110300061305c40a908040c06440420b01130a02c04081641c400c0001e0084100010040c0403804120400b090440200400b59030f450300b07404003000c600c010341400e00c5040c006600309668111034401a10039241207401c15802041d180001100001d0050410003503403010a1752000c0c00036400c00c80e0030000b580811103880050f503070300e48030607601d02c81c10502d003060b400c40e17105104101c03039900d4000032181542c03419080050390b541c0310b100440e02885141303000c0c01801d0140e00b60b049a1141125090a20f0600702c03150030304a20583c09040c202c0304a031002800660094204012180b0143e034a50002d0b03008542d0307110101d0b2a500504d060b0381c0180c8013107403260f100060412045074980300d00218150100d009000ba807d00030780040181101d07500c0502960014550050300c42c0300034046401c810380c40798034a140b540e590842d00055000e22240e00d80410803048450107000d200300852801d403903010440d24199250368440380f00a00d081031045903504100d2f4000b00240c1d600300003030441014441189 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 852527985 1250 852526735 852526739
    0x41040b0708040f0f0f0e04060f0207150b0d03090e06040e0a050c03010b0103140610270806130b0703090510090b07030605060405060a110a06090305030412180308090424 74
    0x83c40039040c156010700b00b00704c1c0d101c009200b964174514505007200c0030710300c0940d4180c41d542045401814085e01d450010fa10000e40754040041200803543ca50551220070000812107405002041411520080009007129414054441c004e02e15030380011001d08002810782c4041c50551420750451029643c43d8821010400c10307140074041e40c680b1400a01c0c062200718031450b405500e509016040c5031140384682130304e80e64a8800c83d1010a90041581d044c100e1055903800506503070043d0203003883d580035480014480019484036034083e00c0c1c0c41400032143d5500c40c0c0c0c00301d00604403000115818000c003070544003062081e02804a126000340060000c5003003000020b0111803032a80482d009071f405000c02c02c1955148020b40386030683c0c03403e2410310366176914034550800d0710040009240c6490840d2460038190b11001452259101e150701c410304010784101a00c41b900103600e0741102c80340c540c100780000780e140c00c00740c8500e650180000c46d61036a000d0380e90741003412400454507000025042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 852529235 1250 852527985 852527999
    0x1009060e07081b0a0b04060e04090803101809030207060809030c06071110140105040908090603010603020a080f13030c051f0e01060501030504050307030513180b0141040b070804 78
    0x499011203c1264005030745032510640c100d44d0301403407140006010f001903075449182c450b508a03101180c1d02c5400c460341da182404001010707406900410385044146402100d07410014800c0305102c581540050850300d00d400d4040b80e2501e80105039000307a000074800600444820400103019400588400954042a45502d8a4a0001c10034507040740c4c01d003000001010071802c40d40341920400e880101d80c0c2401404d1003c90b600c1418003c3e03070400000000000c040d54560b015006201745550365840d65110044841c0c91502e0542c0c2141c1481c1b000a45030000a008040d804407581c4070710705540c20020241c0b103144804070b00391007039a040e548503580d4110980080c8510f00c0a040d003421b00300640d041549800b0f80c0d9024200d8001c5c14800002144420822a4190a4003e004244005e410030070121500380c05001c905086a0210b80141540540071a0404123007440008001602d48144003080c00c0040c00700c5006480104058208000300700802c040004010203401080441ea0b510300e0301031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 852530485 1250 852529235 852529273
    0x518030c011a0108161d0a0f03061433030307050c1302120115090b0309010b090a0507020a060b060c0106081e06010e0a1a0a0e0402030c03010e1009060e0708 69
    0x40d0850401030103a04011a42d80c2c01c8507417000314601407804003414082c0c24011034162007042c806541c040301d5444001544c104d00c00c002c0301901d01ca444140318000441f0303150642d2100585624044142c5050740b0381c545001d1200a01d0f150000c180c4400719007160a010a055601070702045e142c4c2d8014003240d03680c9080440d0385a00c1032110345402c45c84c0c101d06900b510b44030740040c002c6003080ca10440050700450b1182184801a000400342c03141d883c140300c0c1c0a207008003074a01c102402507100200042d10340c5800e118a9205030055006010b1004607aa10480140003082542e6441a1b05100950a0030307800d10402d8007030b00301d200080c03442c0714500c100b01d813441b2101036003283c15030b00043c014400031208049054020400b400c005c100342c040c1102c140e031000d24083c4400e80003c0d03050703400507101804000050240f0300a0702603601c407181c0b4070281401c1c0d8007425a050b15030762260b0364610601240d40d0001c0c2078103005a9001400341d40c944001401c18040d030340210010351101c050000380d1343c1d0080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 852531735 1250 852530485 852530531
    0x92808030f0d0b0307084806092e080903130b0a030e100903031b14090315070e130b0306040326101401020109150518030c01 55
    0xa0000c504215030000c80d80250710801001810b490346602c15509261000c205100241881009a80d1800d000e400481c9403404c1c442d805925002a02060b0003103e00d0105a030285003030b05540c04c0d54495020824403100b0b911044650b90440100c040940f00e000d528090500740c070341481c881204890b00c1000062a00202a11221813908100700080600720346880140484e90304c548510f8070381c00c010409400801d1420406843c902480891a0138800658085035415100c0e890401c030b14150006a0a05100e10500f824042078581c0606858071032440d0141200d440020100c4202c10b5504010400c000002c0d03ca140c042284a060b0046510349814414203103d44002c082080c1d000b00b4000039501e000240c00641803020034a001030300c61660840410001805010740451420100443c102500f101c1c440d860000245500100a5600c1030043c005451741150f80d5003445600008050b0041c68090b11000d985440c2114000180c50140301610107a00100d000060158600800c500844252 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 852532985 1250 852531735 852531749
    0x3190e010216050d0201140706051e0916060e13020409020315060a1710030b0403020c09010b1804020a0509031603050120070b040c181a0103050c0714030928 69
    0x14000c1480f140c0c42e41003070440b116409107088400344454404082c070920542c1006400320f400c000421074000000d0b60808020785074032407001c0c500e69a18812a45480032400025004480340c6001c00440c0c1c4141c2054483c0c1c18000e102180441c80d0048160803030303005134090322003107130084200400d90442c400e0700200c1e80b0080c0c680b03d24010744503c0c01814200412040001c0c50394640110781c840c2e49000e148400b45030b01030b1401c006405d09040195845180d411f00600c502c10703038000820503400c5001603504030079844002980c1801a0400c02c40a500102200d008201d0140a101e1076954100070030840f0001100084840500b982000c50039200310700ca00c00d04201520382d00500800c100d0003110503082c1c02407805501e5480d00d24000c1c1145880d03500000e4060f03807403851901112910307803111080305145c02c0302c4050305290030015002e440c001c5480f02076100b0f0501800010a000c09019080007020100340d9103401820390000d00b107110412003288001c1d01c1d4410586240c24549070002c09403040b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 852534235 1250 852532985 852533023
    0xf0e01150506040b0313080c060609100503070506070215030709080d0e0904110a08060a0e06180705060309010b0d060e0d0201141311211603030f1103190e0102 70
    0x10a00460880e01c980d22401011a10000001d402c030358801140e4603001d90700c0003050359540703103a018040d91110107548451260b25044049903e80d41c140d140041140c374040c001e45441490001048059000040142d07004003450020b40c0ea4000d4080045204aa00d5100d800752103003000da0392854100c20380d40c0001440b03014501c1d010f2603071300d985403598020f910040712180c02c1381600114a00100e030b58001c180622a8030184042203005400800c041c481e241c0490f40d00d5039602409001a03030414041e0310b0642c2001d40d09002034104130f401598400000d6002140608144000c00c40b501c80c1c0c440103507541070343c07900107a070070080c00d000c1000d078401d00384000d011421f03484070f020458010240c20580144038906d00b04080204000100e400000018051144456407100c005048161503501a442c1c1c09001c2c10400606800f4082d078080e290180d075090700c228007149054840141800050604e440240320800e140a000d503c1403900c440c9554401c07881da130111001900e800e4030070040400c0c2c82d132 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 852535485 1250 852534235 852534239
    0xd0501210309051215070503330f0315090c0a060f140a020c1905090c0403030e0609040905191707050a020f1c0804060f0e0325090f0e0115 61
    0xd807121510b001c1e104200c50890348100101c0049150203800002803122905031401c010b6841d8002d0045c5100303040c205084242030081c04403480304201e21040031444030a200c0200b8030103041c40c8017036080c5504007400b00e42d038080300c411104800141c1101d1500890f031100d041040141091501c000041502e4100300540c4610100302426001d085403801019403008251400000d201b00b11520781503101a00c003800d00a0032007017503000720300e0b04d006039406074203420045404580041c044030210380d007540d161400384c03214004000700c55111800e000d84c0162200c1d08500403800600403c480040380440c0566541003e2511720034070380c1c0b040f04102200310148a5240030075004601728100b1903048441d01a031805a100043c2c6440c11424609090074a000b90581001140801401984c0443c3c8031400d000351060412283c010388a88026016000301d405921444c0380d2428194488003958a0104016201e40c0e400d0121600090034403030726500d071280001c0140085c45041c014401e000340f0041198 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 852536735 1250 852535485 852535487
    0x1140103110108070302130b13050306060108040f060b18040201030e120d090c0801051806090d0c06090309170a0314030f0708190c050c010507032009010c080d05012103 74
    0x4011180c0311414400343c400000c00e41846581140c901070224500315840c680c40700310246441d0406140310094184210000c40c4030b141c005400ea218180503950513455648541e41c1e44481c40c43c0300400ca50558480200010700d55600c0e003007095500d900c0401001ca881e01e07000040c04d40f180080804800d8018051004041c00c040088490807407082d00041a10482858502d842e01c603d94000c0800c0c0d4a00000d0110051002115088079103c1c40b088812503282c0c5440d59894041a80e41400030401c08011a0009003468200c0c4800a02a0420a11050341d525822440d2000020314074100c0e0000000f200425401c00c01c00e048410300191620301b1407428142c10f80006002a00c08014002240c00103400700130099401c0203a04882d410a2002028959014125801c982c0d14403901e075081a0019021610034411800f074038090742c42d401f08115041142d910258070040c075036810000a0a9504040f071149401840006140c1800061541c07406140b01c0444c4000c106a84c250400d15103145d02103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 852537985 1250 852536735 852536753
    0x70f030b1206071404120b1617010303200d030501180b060a20030c0703060b010f0f03020d2307080f0708072a05061015080f0606042601140103 63
    0x40420f50900c46010752204905845a00456104145c100007040151013000b60050307056010311201c0d400741410103030921003034401700c020f03011001d00001c7c88001080820300c6040341e400d0b41d400c80d02c0ca004052020441d80e5041841c51031200011a40365030042141c20303014030840d42c0d01103810a0400020007842c0000704280b0440c3d40752420031070324802d00201400d8400c8145440342c411780c100ca07510740b80e4003200380e121b0410340b100ba1880740ca0800e04015550103264544c2c804485650381c00340b07404c680036042e0025000031103a410159138032860060380c40c070507d0b002c030400e00903001e00e0303045407410700002000403000405c9200701c02c2c686018480d40035000003800b60030061505041c10300490003040b0140f84540030381824551850b91300c02c1c206010000c0b41181c01074840206890000762151000600c140321020124000780c074400001d00200e040307488070f6400c03401c0100b40a1405684581c0d0704001d59240c543c0f80714004848175800304890b000d129403601c1d00602034001d0561740c0346482c2c05420b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 852539235 1250 852537985 852537991
    0x2030c03160204020903030406022a0105070b0406060812040302190308040905071218030e010206010815130609050f0709180209060103110406090303140c19110405070f030b1206 78
    0x7596410703454030000c5540c0d80d010b55052110140459844d10358400000b55201c0100d840266404d140c1c1e82540011910052680968101a11060310301807165940950303051009009481880e650300c00412180d03c03e10180c91041e1000c038040383c855066004001200801c80250101c00084100400020700c40c0030a49049400c6a03034001001d90300ca000c2902c0c400305d0010701041c1d0a1520703440f11070341c05904100da42128000d50340c0c650102110801641c1c0c820080c0620403043c3d01c1441c40c03000c04100d110b10141d1101056084c092034400c1c554030030040e2000980c08940f90303000a48904015202000381700c0003403600410070300c4400100b8440f000411150300001c1d0003200342600182d5103900a07048041e11004058003d0380d15550342d071000700342c145903020480020350f500c4c00c2610b449100000365900404548040c24128030307501390400c48883e11107000c42d411040782c0c0100303c09581e9881124891080d80c1c1700d080e0703250038401c401406c036900c5451042c0304000d11910071562010014036558 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 852540485 1250 852539235 852539257
    0x509010b0f0613030503040905180705060d020c1203090601081605130207050a0f0507171b10022e2a12090b04060c03110301080a0201051303080d0c090602030c03 71
    0x30f0340c0c20320766510340d0440f0a103800107401440b00082c00200101d06900c041c3c4101d024120003040f4001c00c01c0701540303071600d038070607a0762180091003440d1114125034000d00700082d1403011522060406000000c60750030031590781c01c05400410040241807410300c00d400c01303684129803103541d060812000038080d5000442155540d50b009c200f2008004040000c100a560082c80008120ba0246031556603541d46009440c500000c02551081003200010306525041541031407040842c2c03143c1c140950011520210f03411440303002592152004c00e4280c885810240702640c801440f0000605c01c16551107405615110022400d081410040ca03446090608903500e0211880c141d04401400038001220000d4841410b40c0b05000c10004140d00205042c2150749043c400c4e442c115100440c3c6d40424850074030542c100b030542c0c0d40158803030710092a408146410801c0f215840b5101c007100ca4008503500c500d20b075501c0c601000615000040740004105910055207050305501d4401d440c2d014005500c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 852541735 1250 852540485 852540487
    0x10e0f163015181e0f110406030b16021209033a1106070306030f030804020118081b0a1514070506091f060b04060c020f09190509010b0f06 61
    0x1c42081882e0035085442c4040040510603003159000040d08480f4400003101c04c2440302d2403405908002c000480d1081d074000c00c1300324240c0800d480b8888100c229040481d4040c3d6100004000140c940c1c1503a4000c820010310301d0701c1c0104026001e441c04948000c0014030503001e00444805650000307145908003000f40c4c910740f5000e661070442e82e6020305445a29000180080400d80c02a4051700c20410020100f044915035110140c6c190204e55540c040070304100c141c200007001203070094052a070024810700d409803100e0710142d17203041d0009070b0740c001c44401c1d0003480c40c0c90408601060000c0080f8404c80398840318602e024904202d4540c18946507003480515940844c6244a00d000e4568260700310003a42c16500d8a40302c0d490300c5d401821584800308884061410104085105000950b0b210700c1c91945002d040240030358a0030110b1000301d82c000c104003040b03600364640250ba507006405c00c104da0b001150b82c1420501c1520001481c0f0f160580c901039009089584a80341030b15414000e0741c1705 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 852542985 1250 852541735 852541829
    0x1204080d0603020603071805060c21070b10030210030c051e09041506090f06020d0e040213090501140d0c1403030c12090103180b010303050c010e0f16 66
    0xc48041c00095001039407015001c010868000d400c1081c40712070f8440c1140b003500040d2034004018642c011040d04511030b80c0a00c200d014040341d03001310030040c881c400d508ca03801e103101551515031030201241c0c0c481940400002c00c0003141800000300c05041105e00f0280010307112440024502e008030490500f48079505405804101504030850300344440281081c0488080a1089642c401c401c6c07041100080c0e8248000528207000d04446054a44950207410a0f00f900c00c1d08949400c210f0055540c001c0c0d08100000242298084c030f40300806101c4e0001c601585040c064041c94110901154050800e600751b010000380c0500b161001d40d40910031000c0c008910902107840d501900e48030121034483d51340304000c502d20b403501402a000b82640c06001c040901380c0b0782c6000e100003500040211103280c0041c030001e40100090700d00c0402080002800c441e400030f10600c0c0076000e20140046400010002150b100c0042020016048410415070240300d0551101030607034481c010710f1510302c1c0a0401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 852544235 1250 852542985 852543007
    0x2101060e090f04200d050f010903020f0a03050f09151305010f03091a0a0b0d0c081207081e2b18030519030204031406091515010c080c0102071b0b120408 67
    0x150480e0a0300700381210b0381c1d610182100c7d8000c004174003080d000340c4503000d18140c650301c0004618413040e60581d074207402c2c000d21f02c01c2040540c0103400d00545c842d074011285e2220100c030101601c1b5040503074480c0c0401c070f490300f0b0025001e4441c41000108060900326040f020690031305202d40301701c01e0329048403060307a10030085000404812050307660110f2880d811400344065040b41d1002d1324041400c1c0d44071a8080705040c40c0510505a004010308014000d02d2001c0703901c1180142e554403000040e0f8a08644200800c146418801074140d44105800440803200403c1c890009401d01c041c0044200842c1510064005d001c0d008180140750f22155032071200a200341c054500542d40701d5010500d078021010306584662084030741482500c00c03500c444044027036100707520380110140030018850341c1c01d81004544400f0412030990f841a402c01c100d2902c84400d100415030b09000d10145c500040950b180d1000e01603007031b844659804ca062001a0120820940054129030304c44501641c0d4020b07541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 852545485 1250 852544235 852544249
    0x21f200303451e030406020601050607031e30050a0c05090d0606030f0807020118061409150a031d01050606030f04140a0503090a1d07052101060e090f0420 68
    0x81001c90382070f0210b40ca8050034000102900030350b04d0607021780e16181e80301c03002c0c4900d0f03003d0900e02400064429140b005580f502090141d100200f9140c000134843e00344161810081c40c0c10003000c1e400182e000071441200b01446027a4000000001c00c0c443c0700a035100003407240c003c1c480514411941002454100708403603015000562b072080f994a800169410401c0ca160410202a8040780c2c0801130440c0004c01030300d4190035200c10b0b481d1b02c080d182c580001d00403035812564205d60414503900303e1442507103004002c1c00071724007141d80100700b00103040d90004180f1022603030202180c1c101018000207607204810769502c82c500106802c3e03d60703102d042000890a890344505c245001c0e1024000611800ac00201030340481aa000c003103550780c580b44610400e0001d044140071420758000324906510504c0100401c0000200c214101e101d00019502c0a11003030344410003160180c50340031200d00f4840522a400200c609401c409864241c0303400c0440042c910f52281045101188540c940c0c2e0303415 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 852546735 1250 852545485 852545503
    0x1802130b03100e03030103060b01180e0c070f1b0e10090218130515030c150702010e03060c07150e0307060c03020c03040303031505030604021f20030345 67
    0xb506002400e203810106442c2d0303100b8041505c4190074181170075204d5000f080203140038140e503c05100c500e840d108100c82c101c0c2000e4003003240b6600c104283e40108200c80300c3e1f050300901501c0d152a1521011500f41d0024140b980f1080c16100c0c96410072820242e610080c600f187c02d00e0b2030251740c1e414041c1840f914503104030389050303009804000d0748882054950109115407256040700403a045004101a910056050041e90001c0d4684040c0300140c610f4000d004498418100003600c2e070483c40000b801c2c00302c1141d1001902d9004280325051014006c048003c42034501410000200500d860740e490f0700c540700d00905400d45800316002c2c0203100c0d60449041104c25001c1d80e84480d100c0c640280500340c049a20b000608444070040390303070b00e0b002c03464500403603005180080304500c8580300102c416215000f00705109500000c10150002c24a02c0b58032291a84e020715a81d1404000c2881c1d07100f200c00400480c6006031240384918000b1110b0304689505041c29a094002c0240d105442e003036840c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 852547985 1250 852546735 852546763
    0x40f0e0903031f090f0b0102070b0c0a2604060c1502040518060a080f0c0f06030709060804050a060207081207170a0e010b1302070c06080708010302040b030c031e011802130b03 77
    0x5c0950441c074a01c580e84501c640940990075608980c4d0344911060003401010a0142580c10400200c0001001c04031121580c403480351907000c100b0000044548503411560002010904c03c840000030000103482a40301d2a07901d5500314203003420700e000700d41601d0300071a00c04403c07905200451102e96500502c64002c1c0307804400c03a1440c5600f8100c45844a410092450240b08440c48900c024601030042d81e2040034a552407900e001e1030140219620b20000d0426076403402007520328000303d900c1c0e00042c21001d0140a5103507442a42e00300442030300038014070404c00c01000f0451444c1144045400a8115441c1107020840041140001d801800c0a450055202070180e54240c0c0070386680c2c002d030000900034099818115640c0d801550031030412601d5900081c600c41c014001441d0030780c000042c401c0064110f4450705110004245040202d23004844180482d140765002242c1c03d02800b40c40c0d200b0400400c01010242d400326004902c00c03800d0101b81c0e034480500d0303070490f00d00304542e0300e0041d61 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 852549235 1250 852547985 852547991
    0x70302160506011712180405040f08070503040e0a020c0606040e0f0a0c1a0414011b060c090e10060203030402040f1b050309100614090702030906040b040f0e0903031f09 74
    0x954442013021105801d000000c501807000c2100700314004c0300941e5410700b02005200307809054101004010540184203e410554400b403030804200350030702034480107100d00c00031542c071410111000d136488002019410003c0c010040540602d00c0412003a80015040c3c80c040751041d006032416003001420f040c0030780d0511500101c07000340000c04800c00102c0300e800140d0b80709003c541d0000f1026200e58014040f1524031028130300c40ca540700c1c20340314028841000410504402a98808068030011807071080041c1c445103050000144141d10590409000c041701c8889900c1c040f8040e469010007840a48102e40d50036410354a88180d4110005050042900e00d694040010003d00a81c00c1601c0403c103601c03035003460054014144c4250400d8945425081c1003078116082080301412000704542e01318001880920f03030a40701d032030140002d01000d03a4166216030038a41c180501003280e91003e19500d40350014054541d40200403250030031521036011a1140840c3d000b403a07202c00310f42c0032420b0186 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 852550485 1250 852549235 852549239
    0x1020a05030a0509030a0c1b090f0903020705040513030c020307050306010308300408070501060807090b010e0d171e030403050403021e01050406030f0f09060203010e071707030216050601 82
    0x903000340114410344201004001948031040301c51351300d0042c0024513020507101c000400100320300307040a880c0315419140020b038031b030f40303865521080d1010b00c0d0340c85d82095241c2002c80e00301501400490058002030310100300c98904504031544409110901500744205000b00109640b014800a0041c080c01740840c0d00c6540c1d6407400c0a050707400088503407080024103044003c2d0009a10800c01c0d0085043c04e8410070703031138645a883c580e90010f5001c071070075943c2c1c030800540d2078005d110300001070200c1a8001520070504001600c00000882c000c1d200d00c17207614610740042c02a056400c15804040c481d80c0d00c54101345031503a8188947c03d82208407140100c1088200f42d801001081533074800c1e42c0c440600210001d00408448030140700b640843c60030b000512105100c0da000a0302a003841001003041081c1c0d0410380d00719000b90700180e4140b0380000c01446100a03404405400846500c0c0546010081030759061000501038080401c0640015684980751303800e05240310340d260000180c99142d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 852551735 1250 852550485 852550487
    0x405060a090e1f0323160603110f0f07020312040902191d2704050105011703040602100c12050f040c050609010e09061804120305060609031b060c01020a 67
    0x460520a0400e48501900001c0c2c2c502c00c5620701815402400742280151801e55480039004480e40c0d034801e05d110600420381c00c2c02e81c010030540c82404051288001128200b08000702031f2490404042041c090400c011904100040d08803541002c016030102d8460781c15200103424032024078042d8000100108002c50b48012660041002d050240c041d0407140340401000e0b22500030700c50b4241044c05000799000b4850625204101301c01007403c079040b14803120854420704102d8265004e0f5100d0b9951b2005002006800c1d244005a40c541d00044d0b091618103400290b4500100c52a555855100c2400e1950140135400701402010350107006c0c0301c036181008148556401c212004e403818035500d2000504ca0810104072180c09a042e0740706091030314040c0a004103c1d802403c40c640102c04408500d4000d074402c6c1041d03004034490007182c12010a0040014199000649a544a0b02040200c1c0303100e40d90000700010b4103d482202e610111020380005007142c0a40a90700045500000b2445407207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 852552985 1250 852551735 852551747
    0x9150705011b0203190804020f01080a0b0a1805060f240d110717040f0b0c150f07030509030f0a181806061803020d03210f0e0c01080411010c0203030405060a 69
    0x25211403510b0b5103d0100303003c070450b8600810b54002e0740240c0c00000c1d00042b54458941607070300009492020034504280000b0801c03264280c0d00007950132200520709401046c05004d00740e00302400311000504a090000020700803c01401a522155030481c0c2c04100520f60405a9088901e2154100100d41021f540c1800703660041108460000384202503c0000148c4400c0e5020754036148a00c040540c240741c90100158080400070009202e444119840c141c4400103042c819003a05000d6a00307402c02d1388014096a1016140032070b00d401c284110001c01c0d00c082c00340d410302c586510341031200000c03440c00d00a1660481d0030140c1c18200c10f01c900d004a40c0e554008804a80f0700d81d40c3c440510440070a58101141d02d400002d51103010701c5039883c0840d100d0031540300d03280302c40c50f00c0c91911070405410400f00c490440f942d402e800d407150f003840d2600c1010300c00c0c08090b2000b82814440d41c41e041e82c5042c68840842070042c1444608101e407003e64500b0000d42d0054403010300380307030398a01000c007002d400303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 852554235 1250 852552985 852552997
    0x1509090a02030a0b25050301090b0604050301060f081203040305091003180803070e030102030618040c0e10050922060c0507080304060608060112030e040b1201050a0b01080c09150705011b0203 84
    0xc2003500c241004001e15080c5d003c1544180c0355441c141142d090041441c09841d0840b21180e011806101c04902503034203101304001010081c2d2905540c615004040d801c0060010040c0c201000c203000300700110340c021085502e1084105da82907006044100150020300c8031840c6131607900c070343c06c1078601048080402507004aa20b6190418460440f000701401e0303120880340180c00c2454489040f100c6180c800c801c0d038000b0b00c203401079001c1940f24485041001411142c4081414076102c042180e0300745054580d40140c4ca1802480c8028100c0d180440d0715840800020001c80d071383c421f24040030744500d0a5402141c0d00c0180c481d603d08190a042015107a20f004000fa28000c41c00001a030700840c0c40440803581c4e160302c4243da56031101d001c000080c004074840c039411004000001980200a10410b44035a04128001503050240000148491b00007072003052501c43c1009003000f81c0d81c1d40903203490500604c403020b541d2603d40f49040e5015002800495085c8034500c3c0d401a400742e00032000d051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 852555485 1250 852554235 852554251
    0xa0615080307140609010c0c020d0614070c0c05010f0e090c0904090821070f0e0103090212031c052a0c0d08160203040612050a060b0a020d1101051509090a02030a0b 72
    0x2c1d40717403e03003218221041d4024100c041071864411a0050400c40f106468082c0200c0001540d408400111203c0060480720000024440000601005401c1c03d400e0301500080c40c04900f41c50190744060014290a113401344550300c580c0000f034082900d0360442e580d4280251083c004650305240140150300030100c16540004464000004440d04071595407003030210383d85080c1a0201c018040d07882c040864100c50400d501d480d07001001d0f0300c402d64a4550180001c004540d60500880d00300c0041d01c4800c520840c940c1018107000c0708003035040290a05840e900981040c0400001c220b5038541325480c002c030075a02601550142c415040911584a0102565111000e1610000880e01d9106600440e008518a03150224152480307a2106a00c0040d070740000034890349461400200d81c22104600005030b200c5286000c0302a4003018901c01c2e44801d000034483d0741800c020049100c7c07408154030703000e00390307003000a00d0501c0200105030314640c014080d50302e03d4856061001c21b280302203c00380 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 852556735 1250 852555485 852555493
    0x19020301050105030d0507020904060e06010b040905060d020109051215010311090108010b060a080402010e0a3b04082b0603020916020c090c0f04140f030d020a061508030714 76
    0x201c6040100b001d200081d840e0751811f2501c0810b6003001406034010b041a03030400d90300c4200f48100b000c10441b1602906d103c00c1d03100d0b20b03240303465241030548600411060040e00f50703030b5007200183d8100741c240c801d548040320000c0c0c00c0480c1001552a040c80c030783c030090a104038000004140903440010381900502500d034903603960b0b21041194260345010304080d07003101c0c04011580c0360394400c407000b5801920514004d4002c0785100001391b03200b00d00d50419180485291000340c4401518000540c01c00b9203d405104160304001200116580c0204050481c00001031031b1001d19640c01c54170304011785d1900064192602c2101036800030301c26408100d01504584001c26084915101c4c0c5100402c02d80c0d006000406840341808042040503107020400082030010741c203984030a44c0580081e00d4503900281102a800f01049001d6950107401406a0480c2d03100500701035020030980203c0e600441d001c280b08050918603107001c1c10547c841165400301254100822042e45120318900300b8280482d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 852557985 1250 852556735 852556739
    0xf0d1806061d13061e0c111f020a09172503022d0d050c03060709030c0b0702011209030302071401060612090809180403080106030b060d1d190203010501 67
    0x1004042d1080000c160040c4070140080c1c0300040709200c6119a511131400441c107100c14071a48075440064150300c032041d545603024100002d43c498244091140c00c4002070800c500c02007003c4007254440342c40310b0802c0d500040c104640c3d5001e22070300300091680038000000350404041c140d84864034407a5a1142101d21007040c0d40001c000c0400e0010b40b034000300300718500420b503c40404c01081d0003004001034401c038844c1200d241d68048404842a00881c0540301d2039250000b05030900e0b80040031001440302e004014404604c5a2100340181c0d118800304507a1203400d400140c54641c4908410b524503410481c10034101a0302d42c0240c03048520440c5a010041240f03003540d030907500c03240900350001c4c032281040f50019401d40c008500f5107004003440b0345070020403008030320385155110010300324040c440180030405038070040320760040859250400c40000f80d107000401c81e1003201032810045407101614103024013422440e000c1c40c1200d8044071000550701a4030b4070140ea444109911952a203800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 852559235 1250 852557985 852557999
    0x4140115030b032103060102150a1a03010e0706110c041a1e0f0f0103020d11031b070201080f1906180f06050d1b0306020d1b1806050f0d180606 63
    0x2040202c0781319862100d491a03400c800c1c0c08880d80009020310b046110310b0b000e20008500f0380750000c4c000caa628101103440c2c40300c5050110080d00044269000c0d030700d498622032039001d02080c4031f800d864840c9004844d8120854110340340c05a945036441e441464807002c1c4078018621780c2161540c3c3c80903200340800300300315000d1140e541180c40805030455842d460203c11443c15441c00305044205040c01400d00c00682d2000040303a213000340881d9042d80000c1400590507100450344080c60501c0056413401901342e00013044088050081c1d4406140c060100c2d86240c103000c0d02040f075018840c0308004480d40c0380740d80096080c15072401095180b4008004203012087d000313042c11b880300680b580c0000c42d0719694808024400000c0008064401d606c040001803e03070001f0001d50000300381c0814101d5500c03281900402c0b00444500a12800038484480d60140e42c911604491a6040c41c548942d50f407860844144100c182d007407801807400c407124040c4021075a00d000f203580240c42c100900ca8555034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 852560485 1250 852559235 852559243
    0xb06270108061017180709021e27041d060103030810081e0102270108060604060f0e130903090e091615020a1208040b0a02180f04140115030b03 63
    0x10f41200292440349070100141e41004d220783c101204040403d0005405140c00f4205059504a8030300c194000880039507400c1c85d441c00c0b1100e400c0260b507591801900303a8074525040c44d4600d14007a41070701c5a144407250b07034035a80a411a02000f0007a031561040c800c02d000d44594090000300d021030700c00c802042c0f1342c000020350f01d02603c00e503c009020707003000400744194400300128402d6003503400300588000c054002c2c2580d50a5551030000c00259005540058850540213084d1401030301d05001c200082a4004c8070782c602c41300142403003561841050040b804102842501020060408070170804066100d260350003100d424109100884d12401c0a0039200d0f407448401004140c80300c1d509000d2a55075601c3c01c01c4000c02801211040c5e80e0560700c068520f103d18003a000814289030400040c00750b0340d0706131903110700802402c518044c0046084082c038020404240c1c003c000803030305401143c0719035100d01401c110248145c925581d440000001d13202c20803214800280c01c1c40c494240c6418001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 852561735 1250 852560485 852560509
    0xe10020306103608012a030b0a0824100302030717150a05070e03060105060307180302060c0c0a060219020d1b0f080d02060c0d0b0627010806 62
    0x1d1685500003260030003211407200d5000c50100b4034400481c1c0030248500240e601d000d03004000d019801c0b4525121300142102d10f010000700f0080b1440e40101e81860008074501c14444030b6003400900b142000c804500c103208150441380007445035100c0280310490014040d00008204401d4032025075819124411840c40d510000350981d001c45404c0c0484031140e4000302080101c44210f548040321500590088907080d11030100c600d99620500003215400b1910a88104054001f0580d0354035000100303c16100c010a0300081243c0c0058401119081c4158100116001042c00340c450911040060f11680400d03e51440740004110010b841400411011034000100810003050850354080c4414141a0402150790038461410a521402d015000001400d003841400211341c1c2031409491410300940d0f0510250742c401b004000703561508034203c45c55100c40040c040740b154400f90116900c0d002c0c2c9001101c038074252000c5a40c0b100b160507424112254240e803651241d4403410288a0b00729240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 852562985 1250 852561735 852561739
    0x6060306051009260a0f03030c1412070e0103090b09280f0b04020607020d050c04060f05030c0d0602120c2505030304030806120a050a150e031819090e10020306 70
    0xb081d100080004804c0d01c02107203418000c156101203130141d440703446052410501300d011070380d6188070700412940401d110140c010ac100c2e01360310b4420000154855000d00920810812580c01040d0724503074401c1d003003410007980c011044c60380ba050060440781c42d441c20307590503030784404203241070f500241c80c51020b600480d4011110010040320f6441e81400403070020400d0380c01100c04c120100050b1240c84036604d400f401080901070b01c0c454041080143c40343d81d0300c0758409966940c4188950799007c02c0f401e02c0c8100403129100380002a00e4208082d02400f0600091460898100007004460700d00402d40c070407a205500720300c0d04040c5000c255100c002100980301d0f038030070700004001900510449822590041c074840800f140e14481c01d02d09035590900305c5094110b15070000800504240d140c4020350303035030b80030b000c44031000c0740282e074a000c0c4035052812051741d06814103141e11031111819003844a00c4007015802d8540c144e03003028086001c0861310a02c40c0b9200c1000c00180c91090328028280 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 852564235 1250 852562985 852563009
    0xa0e070b07062f0d0b040209120c090f070f0819020301152d08040501060b0f071a01060e210105070309020909010b0a14120a060e1606050406140d06060306051009 71
    0x50b0b44c80000240546075030ba64225500300329400c11503445d100d41d00c164229640c02030000ba40e80009110b94420007a2103444500f01c464144000183c110400c20400780b181e00d0105182e0340c60303650300d02024480c14450507403d0b200100110b030f0180400305086022a29444055496400d034132801a071243d62a8680070706919610707031242d100e11424080c0c1e0818081c80020a203103803105048007a41e804213020f4400c104000900d4010003414140a1840c41909800124150714207100a4074401e8038141d13030b81c0b0a14020019174000000c4020030120030161070b00801451902c5800a00100240181a071181c1d800d40005021041c050042e22101040504030060301450841a9548269500709080d17001082c030015114030740040242d510f00c1401264007040441000003014102424062021410804480d00303100054000c0201d808542d12803a00e074039080254030b0600018002c101201c001d45050040010760b195168114005589084904141c9005005402c2c2d5280b0b09510a600380c0800c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 852565485 1250 852564235 852564247
    0x6120c060908060a11120c03060f03070b030a0905030c06090c01080a02090d060209060d0504110a0605030c03130f02120a11030a03020a0f03050f13060e010c0b0a0e070b07062f 77
    0x11303a03008a001599400502424019458a50b03038003076004a800300041d0001004001032441d0508411252103011f5024100460902da044030b0705120081003409250340724444030b01003050400c100d6900000f00710136a8254141001001d40f0380d00c030850030ba8001142040402c108800610850701c91010040482065030100d07035981c400ba4115241003680081c040c02102000141c502a403842544150b5283c905140140108481039501e9044203081100a0041282c141c0c4000c003200e03001b4052040d200c44100441c9041d01300383c4020714000f50030900942c150b5606402c0003500720b00703041c40b80200002011403807003416516412040040c0c016480784071154046066640c8030b2030318038028981030740340281111909040b039003c41000c040e009030309101044107991000c1900d6101c2c00c2440c24041c4814607454ac20045400908a91503140e981c0c1003803140c00204100e40b83c010011505100d40314902410041c0007440d0300000c242d40d011507030309250300f01242040c071201c4040002d91140d051003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 852566735 1250 852565485 852565501
    0x70e010804082116030b0a1a16060e060106020f0d110709020a0c1509081909080d0215061807300203073b04090606120c06090806 57
    0x40025000b65035a201c2040f01a2000200d241c2141000055244031981070900411004100100f10411410140f8080c2c582e502c95980509001c100c42078915403a4107214501c0e011441482454444045c0d03240d5015400b042040c1c0d41c00100c0410500c005503486a030342d600042e070300c450000e103007000242c10031f08000200b580074075601d40500b40c0d0f1a0854802588030040b040c101e910001304940460515010481086901943c507541e02400035001e2101140c56940c0c00f105002e94505284594032144401c01d00c0d512035010720000b48189001c40c5d100040c43e84018bd11081b031582400264600c000028000d0f042506200c1003c600c01c1e08200c0315503640c05011200c0410031983c100c64642d4101040a454941044c032404403000e034800107a0b2401c00788809003040400c02c02211040c42034003013920000303400c00c41c0c4440120125914409140b0f041002900404200e14000c1585241441c04a01c1e09c036291071071034003580f10300c0203050120307260401951000860b08c1402c2840d886400011164 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 852567985 1250 852566735 852566747
    0x307050c010603060507020a050706020312130f0b040b014103120415030c11071512060b0409111303030e01050702040207060e12160615051504031505070e01 69
    0x40000e000008090740c4a80d1100d0944d00240c0344000146d010920160a100003400b200004220b580029032404004039001101500002d00c655203041c801c058810600030350585546500f94025403004881ca400c3ca0100d024000038006c0280ca42c0c02501c91000030041000d81b09500b0381440c0c8142d041035a044540d0030101d40030340a6a0701402000c110142000c005c0024201506604921260b030700c80ca100c00400711812096401c0c2001004000c181000c0c0003c540c0c0e1040e01c0180c840c244505081c2d02c002e56440c04280044c0d0308651500c90002515881c120190042d00c2d00601c3c140038800040041c145603004402c000d00400035952010400280200c07040d03141144103040280c102605500024200d801a10003596103d445d040e03000c907900002d001c52050090040b100c1402c003413242c0071100c03098029800082c1502c4d079844446100d40307500c0b211800100001400481904152440e4500503002440103e50340b000307180c1e10100300c03071940c01114466001a9034240421040000450701 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 852569235 1250 852567985 852567997
    0x5090d0507080d05070605161b060204080d030204142b061d0a060b091e0a0207060608030a030c0318060c0c0803090a0c05030a1e11100804110a0b030705 67
    0x66119403140052449030500c4549103000e940d841341500c0342010300381070041d202c00421489003160070b80d40504c80f150b0030485041c40840303d600000001f030b20614241c4020303c0760f03421201561040f401c601e590700f0b5044d0014403d4404050b0749281d081c0d002000e100c0180c008003801d00a00c2c0c09a00c00c0c0d0010742c1420a9840c41900480005c26410804481e1070024481e0810281c41c9400c41303000117007800654082c0354142101035842c2d1513980b81502c80b66a420007410b45d010854450800407d1416000b0380545082c20f4201c001040070641e11008150303250f206051250220782090902e410a902034400d2407081e040100d5034010301d84150313442c80c004104c0e044c00c03181400020440000031604070409176115043c40001040c4515160034941e940182c254070940c4681d022080c0c1000150200c082803085a0a1401c07241903941a0704d44040c050225000d0070790020899042d00e070800741e00c01140c0d80103d000e4170a0700503014280041c0004111a4000c07450a040c0410100b0003a034803400003444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 852570485 1250 852569235 852569243
    0x10b06030613020d020711031c0e060702030708070e0108060a020f0f090d060f060f091505190b120105090105010f09050918030d05091207120c02010c051f060b040605090d 75
    0x132411402d00001c004036001034070107a0740c40c1c00c5025440c805040070010344d0a001e2080c013030b0b4007140d214032100520a00500790f4050183c04081801011500c080001001030203114040d01d124030b45550340358100c060b0900c01c43c0214402d0702d0110307490240c41d2003290369001100c24010f1500003609600c20341c1d80d00108105420210014039030000c604a1710841002481c0314001050706490160150749406103908400001481d00c00780b1517014200301c0544046840c10368400309400044c1100580c071800e15440a6607d41e40020260581e1202c00300f0355068890840d500354450f41c0741c80044810304003540101002c59501001070080d4034085080342d9104900e8040785064119401d8514195007040c0c182003003071a11241403004040061000c20111140c88052a00304480e40e280d00304501e01c41c0110b5004e00001104410559214131a00b822564200c0201c8080c103200c0d00c13200c54000c55862480205514140740882c10a50038400c030f5048500d1030b076600b0700b060b04030002c028180c010224100e0f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 852571735 1250 852570485 852570487
    0xd0b0a090308010f0e01060f0905220b010203041d0703020403140a0201170f0a0b030c06040306060306050609060901032a0e06010e010306060203180a0e0906010e0115080a090f0501060803090111010b0603061302 92
    0x30381a61541441e075502f0000340100104204400d0059065608601c0c5150640d0424030090146110142c0c94601c025a00c050106664131000020b030002e10803900040c0441c0d5002d44450500100040c965404a10030b9076a0107002c0c444640d071041220064a81b0540044401d000c1a214a01c80d0042d50394904014192401c1c1c00c040400542240d219600455a07240c40307803810000d205d000c0c807400d540510309450443d15450400d000070000f160502004001d1b510340607500c10307440f46034400c4020300c504d40109460840d80340d010156035442c08580e10b6000a0310000081c4030755200b40940012141075030001c43c140842c081f650702c920b105d0b1030307442904052003860000701322443d1002140103501d10700c064065941000072008480f50f0503004600d0a01d00b5020300000198015001d0703a202c801c0c0c400018180e0b0240c80e0107629080c0c420009012503003814404552000040010b100d03215090b00c0300200300e07884426590a8441a031030240d40040280005440307814562500d20711454060401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 852572985 1250 852571735 852571739
    0x5070609120b0642040f03030c0510090f0506060d0c140f04050412090f080712060e06040b06040b1804080a0c05070b0306010e1c0602090d0b0a090308010f0e01060f09 73
    0x169056520344082c0e081c10a5003039198201903105040464084e5601d0802620781070921542c00e4112a4511000742049080c0c5841818024144010741c422501d081003070188144d039060003003942e42c0d056029074440c0125404181c26280c5051070202c6541e0201031072605c646403c141e03003c005003200f4050340060402d00b00c0c2e00035603201c0c4582d80c4228421058604250098a00109030a0329900a1425a0040c00d02800a04800103281c81110151000d681a8080030301e0000d002d440003011000852040d0000e200070002600401031140c03101f52400c2040001c0f8404000c0408158242020f207803100101050120381910000c0c03601c00e03180e06041c100c0622030365900d4942492640420002c0740040140250317076070310000c901022102143c43c002071120110480c0364448040c40f004082c41c1e4005082c11464862507aa61801608100641f58500d40301c5034100140003800e034100c0c0041c4c644000480c0c801ca80b0803000f02039601d00c04440c100c0d80e0030070409a4280040c0240b001c00e10001001c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 852574235 1250 852572985 852573019
    0x9130203060d0f08070308060d081e071a0105242712060105030d0c1208040c1d01091104030503030a1e0516110d140d020c060f0405070609120b06 64
    0x10300803c441c071900000b03a80b65082d082c010003402003c2d2403544100382c003d00680c0854403000940b00c00b5581070a030185080c2404000c01c1e00d612400c140204108000c0b44440341810f403c0301c0d010f04a070000c2d9140000812008507040708000800c0b01200d14013800d20000401c64425140c03200e20440802811700c554000d40000351800300e103d01d0a0321281c0c00721340107010608003072180d0058040c0504020544222a80d2455680f6100b01514410024032500080038814110070901c020311404048200070104880134003c10300c1c0901451007070701d050460901c080611102101c0450703401801841c2036032150100356015002191903200c0c084924154054481e03140c4c1310b142d00a0b0200c4849000a410740d0b4070190024010030001a425041181c4036003100307411018501c0d0840d03415004c580d496400240d0000280203200702d42440d44111010040744000a4108034090750041d412181d0301c42c1e40302e40c01c0390040c00300e025500507a00700c007900d44000b44030813420940006008000e98075800b88000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 852575485 1250 852574235 852574253
    0x1207080f04030c150f020303070801050409020d06020a121d0c150c010c0504061116060e030a0803090d02100203060604050d06020c06070f031406060f0a050f0f040f0b09130203060d 79
    0x21031442138086600c4106240c004410078031100d04d900107107086250504002c0c220040510030701d03016584408400c021544c50bd440352030319a1340400110f464120444000707140100381e55085420602c0c242c100c3d170001c000c3e42455561600c0d500b000700484008a0705116450780031422003007055070140701c44094408280281c54110b501562125101c0c0c0c40d0800c010070f01525604411080c1d040200b915403800b041f0001c0100340c1c0c5050416a030b00b500c9460101389462038418003e0301245020040c0280f10a0120b1a5403019003243e085402c4240001c1c00c007400c034132090715540d5000c1c104000400c89801c10000d904100d134080d0500505001d041020f650070721004076050000614003642d80a281b507054410300030350024a42c071000e218604640896610301c01d1060000d00c5c90b001203100000300788900103d80091428010303a40d00c3d0904015110426000b41c00381c0161481d858001182070b0101609640741603400404091004c000222150001d500142c203507a041403940d0454008114107036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 852576735 1250 852575485 852575489
    0x5130807050d030516050d03140c03090a1709060d2c0c130b030d0e12010905060103080d1d0c1305091e01021905040f090221100f03050115081207080f04030c 69
    0x10301c0c04100360b00c00180301c0b05035800040c2b180115400910a1201c0800000381c24440141d211100d9015100c020600080d180500900745900080020b21000211059000030351108006001c9105080702d48030f070002c9007920001e443e4641c1d800080444014500036401c40c03110020010005000c13800b030b8000c40c0c1081d241250309804510015031440b840d0421000d0720400784c01f200002c01c107140250b40c840343c641380b041c4030240448601150301c1071076919560180041e040340540d001848001c0031040b85e203070801400030a100f0301c1d801001010103502401858800e6036000054240d4094042d040c0e0848110444219491366090106016006002046200c400e40c95203a09072151300e000007a02c80700e03882d6040702c07803014014490380f00b002200800401c0440c0020940c5510b40ea01c404d8181010960b81e0300030311511050345000070a00030107511941c030f50844401c1005040b80c07600807596982d03c1000e5100002c0b04204541008229400064503058104a0500c0d20b000d50304e8843c078802405c29 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 852577985 1250 852576735 852576737
    0x300705011424040917040611190b280e160b0406020c060f0c060103121e050d1109090403020d0207120201091401170705130807050d030516050d 63
    0xc103107040c444070154040d1a0310244115050825040c011800c1c1030031071907800070394040c64851500300304100312440c552452140303001d2803945550792040024003044640c0380345001806a10980c000d10310800003094880794010007680d046840300b0510b02c1d0a410004c100301c040900d45600d9001d00c1d071840c0607000500301c040c17004104000f00d0304100024110203078000e101394501003100700031464011541e0004140308645064035a05e403101084c0e40c40c4590715030030b451b50007088004020405041e10001c0c0c207032000d554410212501148000c111400042004049441882140e41148144d040003040c030345000092424050301c2808a0540c00059500702c0c05604000340041440d075040106d0301c000c041901c0c00b02c481c18150f8001030403ca4460007000c404044101d400110350b4040c86610652442800c3c1844440c580884010041c2c1c00c8244906910006080300090b050400110135080d280010082c035403076201e980d0107035030640c800030005803100d2444590301c0c0411403c0c801c8402100322 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 852579235 1250 852577985 852577991
    0x90a050a061505090103200a08160f050f0901030b1302040912022a010c060204030f140105070306050915030f1f0b0105031623040b0c07060305060330070501 69
    0x5400b00c44501040c40c0d000140500000300c01040454200d000d0b903446d9000d4241661006d00e0008046200c8104030f402914031481060340582c20240c0c800803070b80c04c9034140040560701a45034810401d1144001c0c1c0d0320743d800000580180085a03207105500d801c0b04200480b0405807020760b0208083d12500d140590702203c002c400c0d881132a80500c00c80003c000040d150203154903150162018485520307004a0400200c000c0351810480c6d664100c401842c5c104c08400c3c21608a403900c1e400b581c42403c110801942803802284e6450702a0080e1401c2d00d0340105008661307901d050080100760a00c880169140c42110b0701014890014000c181180401c00c484004ca2410400001c058600c007280301410443c0400c00c1000501ca00400039081040c6450150011000c81c180810451449898039210100002e80001c0d00100c80d002412102d240c0e20a4420495071804160100c82040365640e0701350704011003000300c1c003081c28078102ca9598008485100000d0001502e06542c004140440d01a95 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 852580485 1250 852579235 852579251
    0x1180842011401020705090712060b0d020d11040510050f130e0f07020a080f0a0e04060815010f030c0302090a020f03101d090d050a0e1801061209050c09090a050a06 72
    0x10242c0300b600500c02003030000340085840c14001c507004090003014001000040301000c0d0249601d41c01c404001c04414a03425101e04843c0307003150082d80050802181d0313500c4c0024401c0741c070400c04192012200018103c49813424200e5040d03e00d90700c5188440311004082280c0904a02c050381800050030441411101d545448180c0d90304080c00540740000b0f550014818174000349155049820a10304a6034103500c603940b6000503102c0e81130600c03401d603010b4100700020031001c80010b40c500802d24114031800c41640da4080c0c1c14003c1e103085c00050142222a9010700260900c442c020350010502e410042c5459002d420100381c507082503960700c0322507103d5041004954250030156111071001c0311580010300b130040704103135510100003054040c82404100411414055003260040e008041c160310080802043d043d081107101740110808902640e03403040d56041c40c4d2042410792503000c002401658019405c00c903005100a0031303480d09104000002c000a0001d100391900345200d01008202c041c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 852581735 1250 852580485 852580499
    0x31e05040b0c0f040303030f1d101d070302040e15010e0a050c1821121b06070f0302092206080f01020a120506030a12020c0118084201 59
    0xa20103030100c1042c50b01032148800c00302011003110f007100d5140c140050341d900100c8041000e48000c1d080c80341c3c100c648192030100108017050502c04801010401c01200745502c000402d611450200101c00b94001541031005050a42c4039000084c1c81c0d030101c8003803160602103103100c0340c0c09030003200c02c6581d0751062044080c03035809a6900f000e401703210103003400717484800c00107030075600443c0380d202d03696900308214400080d20a0b051b8400301201a108900c3c01c1517121090741e480990136100b910f00c206101d5170102808124103014a00f1030f540e0203045114143c08a01a420800e0090340c80740305030484a14a404014113002c0347ca000480108040d864481d01c54142a0080c5010881d41d00403c4004402c6a01252202c0681000c040000e41612181c010034501000c3e544010000c440b4848044195900000d03002c141440991ba12030b10b5074250000f006600401e0b00c0340d48aa9070005a000e103409210900d065940101944030001c04400075110085000c5400300d0181c41b170303e080c40188495 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 852582985 1250 852581735 852581753
    0x302010605060a05072d0b060f01110712080d1b090506210a09020402130e0106090e04110f061b01050c030618040317010e0105030f0d0f0f031e0504 65
    0x1003100b00e4155081c460303601c0000d0620b00c10140002c04688608030030080c0c080c201c402d011101507280040e08040000c1d40380c001905001924040d01c9440211013480f100d61007211940c0c044031024016040c000d00c2c0041030b40d4000d2214004690020b818058280084224171880700040c00c0c0080c003041d1080c0311040640005540d401580c0540410482d5100740c08046074104100050003408500594030300c0780b0f45c0001c04c00e4040095005000040c06001081511900010358848500d071840301d982e9040306a40105042c4100c510301c3c0050070003e0301041116107160b00c14400a4030b9400010528000221190720050715032403c180740041400200c08244145644034108160240c0381d4103200c000101541c1c0e086d030180c9900b600100c006400c061041050b2100b424205401d12038650312404034100070741e000d0180c45e02a21079a00302500160001412060103503042e2140b002c44802d9030b10031680818222040400d15445400741c03141c1030b02500d02c4420700484c00741c0010b2581411318196540c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 852584235 1250 852582985 852582989
    0x40201180b040b0d0906020a05030103020a150f0503070e090703050a06060801080c190317041d040c2c041109090a030503010504050a06030f0f05010e0307030801050d1703100303020106 81
    0x8500c500305007400604034500840b0151480000255124051850f644002d4007140f40010101d500115030103003015000000745060f00e10854910501d662100c02c00729003600f089000d8400603229105004205004000540d00100945003120b15900854041b5080000603115200001d40e0ba504000040c038103885410042d11035031a121840794034014074590b035210341c6036503244280710440d403d404041c0c0d1000351900466002e417980b20081c1c0501c20242036600b1034402c2e0722140e00c40101c04401c501e60f0380c1090703104562101c41d0110681c100031902008201e11584a219000d00d203283d148021000b0150910940c40740d440c50b40312128a80a0000600740a00802d43c9640702520b040002500182960f065a005030390005655030703200880000382001d40e01c040c0c803200041380381000f4040c400110240700d6004400911135040c510480360380d240305004018000640c0c210051101c0d280595154403002d010300038520b08910680100c403000d6200b40d8502d500442c2410302001016028010000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 852585485 1250 852584235 852584267
    0x501080109080d020c070e041202070b040302011d060405040e03210115120912081b13090e0c0406080d1202040e01060c03021615120203040c0536040201 67
    0x364003680c2e5410744540140b0b49420a030a0700850544903c2a04201010060500b1801d00b41035041600305054440e40070444540140070302540031940320790405c200e804803541030791103628024061603800c2d03101065101d1190300900401c40010155030300c0c019401002e41344005156200b05a10700103044007443d01000388170003440001080071000c0413035051408062801d0100c0414920000c010007042c2c40e060050000c0d03d440e2000c141c09600403141c600c550500e62000080200f504087c1c126400384920754000300c2c084840034800201e042d0003229440e00800c088a4066010740001020386c1c0258100d8801603100e0040f01402c02c0d03000c8183e42d401101510114605420011045020f0005000718014000340c08049001c05200700803040c20143c0c1416a00c4a20b82c5500340c48135222484410140018010080c80740d640342c580c400c032030003240d0005140000e145070409000710790004c0a445441038042c0d4210300040e004c1510a1004903d610340d208085140a10001d0404038406803044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 852586735 1250 852585485 852585491
    0x60d0b04140705030610030603050604120806010e061c0f020d0c081509060103111e0310060531030501020a02030307201e030c1b03150702100209060c0a1505010801 72
    0xb2260b41c21004403030300300c001595403050582c0d1080c0c0950107400c080d40001c1080c8209010030090000c03010003540c161549603070740003458940c0c10044406070b0f12030a0032076001e0310401408054410341c4400000b41c208041c00801e0880c0b801e42e480c0304030303000000c031042d41c00d072507004680c1000d604c034924175804507004200000042130613000c1080f80000400040c18141d603581c41c0010501880f040d120040c0400f0301c07480301403040000409181e0400d5030403002e8000c441340041851030140781560120025000002058540142c10900c1b0400500c1013100c05120000040701145003030004140303441c840d03001140c0d0b03800d0000009103c1202c401701d4058140300c2e0b090030066080c020881c140e01e01d1052038011107082c500000c50b811482600751110146c441d8200c001d0034803000501c44035040108034107442c1e045256403047c3c0981c01003181c5013801a0081004080007003010350151003079600280601d41010f5480c40803d00c0e01c00700e1402a150342022a01008213103075140a0301e80074100c604024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 852587985 1250 852586735 852586741
    0x9081f230f10090219110a080f0901110706030203160e0607020f01021006030309050312040f090f0612061d030c0703021c02040c390609060b060d0b0414 67
    0x4014000c0080e180780c008004080c04619103a4001e06418068011030408540c0c0303c03807600f058400700b00b44090780000b00da81720301c40050503600410f100b504142c01080451a0444465071001280d0201c400d0906201d44143c5059a0060401220b000b070503158400603580c0c14140340c42300200c0b00001044003005450070310340003d07898000c240e60550f0b605940003804c0c8a4003900603802c0150302c80011415602c1c0210000500d58040303000000c0381e40c00d90503a003920340d105002c1d180500c41c0d405007c46a1640320800c0100740030560294603906e85a8400045080e140c010b8203101c0030362400c003030700c100e0389450f00c0745100702119194814180003c030013540303070140610009407100074902c0041e1091890000c0c1100720010100690341d000e0b40104100302501e8a80000f50103400889504507006071050121b00000d840da0240c1d411004144104255a826035039500380a03102c0240e040701e4054030307040e039800c4640390500909214070240801007104464141400708840d9040200d45400d1440014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 852589235 1250 852587985 852588041
    0x3080a022116020a0e0a0b0405060603040f170408030307030b0f0103061404020f090409080a0f0c0f2901090b0f0a0b07020904080f1206040f1505040c09081f 69
    0x210741c0781c080c10340710b00c030040e03181400050402c0c0815400201100c4241d0308211400b1030300e601400b18200101e60030031940d1101e030240041d900044600070700041031080d212001c656220f48540d8007103941c150707240c80c09813500419401c0d5002034402201007900c40b4070340790280c50054121300788880c007882e0410501d032525803165103801c4141c41349801241c0c0084c1038a00b45c1e903901d04948100001030010f21500703a042c41e00100a501c800c0200000590301100040118032031001844610b8102c0f921400510698070b0783c08540c00c440c400303020380701d40c0d40c00400d06440c0d4003192503000304542040019100410b03001d0100300c0792003410062241d1b040c4030b0144202180c1c002601c02041d010346240301d00740d855242021151003000c1c2e030700c0d4a034180800d40710000302c5a207200521503102a2414041e100e20305610006482800182c03516902c41e030303031062007141815481518051411b1a0a140c0e20355503050321404c4c5841c80c0400909828030600711520340040e0f0040070702810045c500c1e88817410440ca5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 852590485 1250 852589235 852589237
    0xc100218150903060a02031924050a150f0c06140106180605180a0b04030b1506030108030a030b1306080703140c030d1409092a1e0903011503080a0221 66
    0x5c0210800c3e58040086011603440480340104141038040402040170702c01d00ca2102a18000c441e00d84401c11004080b4260030001c40c00802c480f0f1500b03c0740c0074903415450030348400d06104410f100300001c019036030009c1000e80c052040b0704d005002e8180c941c1e5040010040c02240410108444c40729108810000140c0c000c040f180840090100951b080d00b48100140c5650103507030100480d20f10210b00401072140e14010180654440e1499000b1542c901e4140329041c0024824406550000d0100c100e038980030340c110700304002d4000c00b40c0c14103d40140c585805c5172015080314a6039489400b003481000540060884586180070081c14910270800c0004e0799001058101003c008044090858075400c5005440d44000010060490341c030382000e4600c0f000f4102080684015080c010300f000c428192000c0396262040134003000155406401c1d501c00b00d911142c0d03281d8056590300d2a9102903000400c1b1240554452400701e0340e544c1d21601c00034681070001c008030100c007000012803d1543c4c1100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 852591735 1250 852590485 852590491
    0xb06040f11070c0e3c0403120f090f20210613020907140708042408072003070519052a040e1905030c2505060c10021815090306 56
    0x80605c14045d01d082c0a8400d42005000480c4e4032803051043c00308041c5c10211003240b89070b1511081000c00a921030310707801e5808007040904660032418400000c40d0701c98a600020200002d43e54680303510310b1000c02c2d20211400c100e441c000c1c9814170346c605441424030886170007003440c1b020304400324446d4000a18414000e0580750900c83c00000d0131004401260039500d200390041d00b4a46c80716a1104144140181001c020802c581d404843c80b5484c0c0c05039019500036150340d550540755040d607459010030081988c1c07000c40103220904c02e4200107001040010780d200101c0c04d0041c180b14a61400f1032a1640c000d580340d80304040e00c01030104204070400100d101c060201c1e80840da01c01244044c41c100b116000d21101140d190844100c140080000184161501e00382102d0f01c1d46a6210510f50950715000381c8220b01d601600c04000519028000c1d226130680b200644000041000075282260300c100303185800425050400c2c5040e240170b20342c49050003041800545060382ca2000641c40318001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 852592985 1250 852591735 852591781
    0x5060412051614090106020114070e030c030604050a0b1815220b010501200304150e060403110418021c060b1201020301080c0a03020d0b06040f11070c0e 67
    0x403024410300c201000b80c51000401d0050700da41aa84034504404003200b001d0710907004540d940c00000e043c82c414898281c0510300b0b40c481c5022074903080300c100c40c503c00d030401003589849003070000d00d0326690034403489000720f00c10030042442c01050b00c0d1403001010010000340c901ca000168550f0040400308143c40000c80380c1d940202e00b07a40368134601c12031000c541104401805005040d00801c41480c200c28107030399090700c410a241110059034540e045812240c0c03002500148810404071034000180000c0384600c0c00e08104030043c22010030341c1d80d0407a5106071401c24890281d034103141010b104160344101e1000c181c849103d0507401041800e4012520541c0c150b0305d0301c51071424030506501003010004010214803000100d1008903010750428090302d5098043c00d4080c1e401860081e5079041260f81c081c1c8440004c2220342c450003141c1000806640c1c0281d06c4180040800d501d0b4454850610a10003000f0340380d04550420550340d0003280c0020f580c146603442800b41d9001c03425180c540d94860 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 852594235 1250 852592985 852593009
    0x10b0307030f1e0b040b0f061503060d050d18120803241002030d060503060f040b040305040f1512091707050106170102030103030807170f07050702030d0305190204050604 75
    0x510f44441615a00c2c0320701d19404015528031020010855501c6000e940502d054901940b9007010300d0b01400c01c251078107039101c602c0e05d0b210444466007002071907000300700814031195070b10280c40d5181081210f41039040005c0d02c41302c44075107962400c2000e001414140459204040c1c540d0749050b030510020300f031100080724090342148500d1062940006a88001c0c1c46c0c4011550419006581c03508a144215040c6041c1500440c082c18002455446400c18003604800358540d626040b1003800c001d0402e8003005000c000218100a1344c21505005040102c2c000c0c50000e19560b000700030b0010a80c0b2030b0041800c1c440355401007081212045184200500340c9590740c07085140590040c60b42e40c0c031070000441d82c020030150b2090306501442c1200d02940f078440c1c0310b5840e07403422582d0081505410b03ca40e00b510b0080b94890700200356090303204a0034148035150241e09c0d000245049160101c0f8000079072241d00304205541e444944529000c1d05900075802c06045c0070004d1400d0103103010b440c90440ca = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 852595485 1250 852594235 852594263
    0x602010b03060f45010f0e010504050601030809060c070602151501080a0f06050405011403011506120b01141b07050418060b01090e01030f020319050303040f05070506040f050909010b030703 83
    0x3418601400745521003800c1130004501c41e83c002d070301030a00b1060140c01103140c40c90785c490707554042c0604e52040d50f010001e0034032a8295502c400341e13900040c5802d6040318050200d426004007c11060010306a40d400071f00248812145048214000600c442c07801044105450359a03604010341541000f0710040109441103000390201c000e04540d44040d9000342042c00000d650071201002d4221018150001c3c0a480710041240c41c04046030300c5040e00060340303401a03c15540d0740e5442a003c5000500d090024000b09106001254100c00e00170b941c1d07000d48000449801d0010400702004101c1503c09000118140d581310f80b040300d805130094800c0c0e03160002c00c1400d070720071103408000c0c009049004e01c9550f140d0611500c0d44011941c01ca009109150580762207911340c281001000354404020b514583d40c0c0c0d51448501c2894a504903524407502802080325503c0c940079001400c5285d0714005002d2030700c010401e02407000341c0f2550207a4540f0362008400e44000c0703400010349422a510f081c03205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 852596735 1250 852595485 852595561
    0x39030219080c0c03310e01140f0a03082101080d0c061104080f07050906060f0904090b0a0f0b0d032721061d06220c0602010b03060f 58
    0x44990030440d05140000a100d0726132107242c0c031041142c0483c1091001d16442403000d05032802c0c00706d0040c0186a004034004020f8040004c0f015107480790090480500c804d90f51001c204100e9454008603900300022515452011000814106146001103d4901035141004540d110181148582d040207003000c2e9880c18030000d6006040700d00b808004903962141c0c0c0d602182e480c0e0076400c01d040c0d01130042010010761481e2035a045405600300800940c03030445007501c000314540c080c12940b600207454810381408a0903411344584541400034001c0717880548003080c64100c95050000501c80d400c0d940031300340420703031219185856840302d405010301e401e40500e5008018040303500210324003424144100900b00c0050508481c54482c000a01403081410302d0280da12802c0262541e10341d0110000a02d500e407511904411001c071101510040b1030a510f881c0e0358004070707402c080090303074507103070794070702c142001c12425500c0030840c040a015400c0031200440b550a181c20007140c0d401e001c082c090318074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 852597985 1250 852596735 852596737
    0x2010507050607180b040503061501031b1e0c0b0a0b1504080102070c081b010522080706020601230103110c0a0530091339030219080c 59
    0x40c0d00202100c02c40c2c90011070042113940c0b1214a10115880c084001800d4000b00040e0303425200001d01908183c0c0d43d000c22500d4070f101801c1540c2c1055110100030f40422088a001d44403e50f90b07aa030200000b8011010002071001c081088003045980513800020070082c0e04500d400401c414000f01d0016684000204071010501c0108480440001d00007011801540148120f5200d4814554540c1d80d0b5510207440740d0f4401c46d040c4101c0551119035013a5071082e0300030180c6102024000300c1407090309008030b0403080260050103c036408a0303c1440811b404011250040840d0a80060f013400240e104441e41c0c4400c00142c4d042c11307101c20085942e4a80306c0280c4620800303003400c5910030001ca040c003c3da64001080820030403400340302c00d0a1000b4481c020500640c040c147c0302454200c002c0103005402c808403a00720062503499101c4d101e4803000302c20310342401d02341c120007400054802d0700d86420715901905103400c0c1481080310160f0302401600001404d01d16007440b1480da41c2d0030f50004d000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 852599235 1250 852597985 852597997
    0xf0112051317070605060f0d0b101205030c07051518031c020102030a1508030a05090d0f0b07020c0f220e1006060e0306071b05010f15031b0e0112020105 67
    0x2d2014900b150b01801180c58050b000c410300903503003800700303490307180601c5400103a6458680d04404070b032080c030000c42c0d00c40142c00c0d00401c0040812045a07925184a9440e0607100c0301103400b50070000f0521500c0c0010412500035000c1120a07042d008901c1503a01e41621410801c20400325460301f062015a03070a120b03149032104855141d8a0b005841d8100a00070340c001c0702c0c502c00300d91401c06c44140502c0310850a01c00c0d515448015032a04003801c8050b507a940080708010340c40442d00c0f900d000000c1c900645180e0b01d520500504c03581e4188407c2c0039052102c00c090350390240040b040c07040399076502c0c410002d20100148284c4082d2110310242c80f0048d2505440324011449480501e00381428154410400c58a41d940d85140030320700942050748801042d02c0d24400145600c515031030780c1e030850402c0407c142c4210000038140c80c640703254400340d501c0004000c07070700049010100140071446c1400240310304811551a010f50a003810844d1495040c000c1e040400c0c0200344c22011a40504100d0310 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 852600485 1250 852599235 852599243
    0x30a0917010f06120b0f010302061605070b0d0219020105060d06020901030207021f020f010e030a0f052704050901090b0705090a030203120301080c0303070f0206030a1d1b0f01120513 80
    0x3c035252041801041d140000c210395a4580d00005046c0303816504485058941c001c01592401c80c10311550004090040019291030103180000a07000400744000e21134072034898405070b02d80768103054143c0720f009140039540659060408100d4035540d000150001d00d50b210100685505010f40104d00a02403841700941000d0300110202d018241030140803540c6440e0707801c07030b401600741101490907a550350000c440654001d104000c46280280407108214281d03142403030800b40d070300707151042c0d4005c440b41340001d040419014004030b0401e4002c803540421000000d00190600c1d64403038000840040c03000041200c00714104c078840c0d032800326403002540c0040490341c00454014400c610342d40203124000c240c0c851503080c08803504011068a11319500003d070318808030294ac00340b01e801d6100901202d600d6a80310b066035848184540d490003d0201100205550f10503c55441c02c0704616180d014030403003104034801072aa81c4501d811380c0d4404401000718a50301d460702005044060440024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 852601735 1250 852600485 852600491
    0xa050712060b0301020a0c021302070803040b180d0f0207060e030a0b0a11070525030c09050408071406060a05041b1209021f0e1509010302030405101a0111030a0917010f 74
    0x4c000184c0c00500c0d000003034009c030313840624040420b40c600128030030300f18002c1002100780300043c04507150760b0200750b100300080501201c45034410b6000c0d060003101c1c125a00441c00715240d03107015960401c040d01c06802c1078201119200354440000c0c1d51160f024000a042b500d82c00001603103200150082e03a222040140400c1e115545031070300c4d54450a504038040b4114480d2920500320b0003070304d00c1c3c00003140e40200010349200c0c1045a080e01600000f04192074004041007200c000907507000480301032180e50005098030341803c00c00c2280c0c2c43c0442d0310241c8107509019040ca20049140307814a0440742c58117024032510002d14407000982000a4041d50100760b102440c400700c0004887c0c0501c10005a541c5210b00c5c442004018207400032904a90349207000388a89806540658011a00b06000b00101c1d0082c4207003006035820741e920203c903820500c8443e000b1480c0f65801100c501c8440c0c007200301039400c00c1e201101c001d18004203441404030f640d9075495002d240340420341c0000c41d078110f815014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 852602985 1250 852601735 852601747
    0x1050d0b0601090506042c010510081b0d0c081f0501030b03070b0c0c1516061e060602030a030b1c080708040315050613020a020d11030c010203130c080a050712060b030102 75
    0x1103c14443d41c2400e611100f0f103003041c020341c401f15420501d4140d4800038401d60280d0051101254000030041030075a1400c0c2070080000c000c54924081c1422541c08680810a501150802420030350081c0c51004000681d200d8a1918072085075640706440e800c0c41c00103803a088000029140c40002d62042c0c0c0000d00005180281420202c0c090404075400d0311420b2150358201e010840a106160300e401c940308010440c1d100040c00c9030480c00b010340358000c0803001c6011168150044458031b45c00103015903c0082d042000036010f002d44208160119150005d000c02140310703c002c12440300c40102035010005040e400c2000c6c400607540915000103076403400e9098540050018041034408901c01c11080010400c1031a05008440402806602500c00000d544405951b21088600d600142d8002403151032030502003480a1485042d40c401c1c1e0421484a0303013040c11a07905680c04c8a21142c02210050340402c2d40001c0c90300480e80d0150410994040707500f403040040010465166140d4000103038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 852604235 1250 852602985 852602999
    0x320c0102030609070816030b040e0d11240f0601021203090601030c0905150f01020304120807140106050d0b070306170a030f0810050d060608030f2101050d0b060109050604 75
    0x16510580c010b6403244007603100c080742a58824001c41b0040c041c02c4104518245043c4250885440c64070058004500c28003484810350801e468680114006007182011050400040141102c4003130480004e030b900c2a11441100c255001c010004a40804401e011900e243d200f0000b90a0500f40c10030301c20f8403400c080710303c15140c6e0404c1c801510401d02054010545400701c0c070415000303840c0d03440384500d400c0c1e01005201c05070f01c150800a065000078440002c06c0c1a94a0b9420b8115100d4110242c2d034815914050300001320708240b50500703a142c105c1c18040c944409812011490304041c110545a90316a800ca000c0c0085800864048030380031200e94188000140c0c2d81c0505101c1d4179550702c4070813080000c44600c542101c1a845c0309030040805c1100d4186000e143c060f0350302071100884c5c681d031a0355649180d41d02079070466401c11000640c40c80300c0f1456460750342454001184520740395141000141c003040394102c002e050102048042112680516100c0c0020040500001d844070f40d01d580c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 852605485 1250 852604235 852604237
    0x3100b0f0a0f02121b0f0105010b04050405180316060603020d032114150103060e2a18040b0d0c0303051903140a0905030f07050d0306060f320c0102 65
    0x1190008030b04071a5202c0304403800440e500190b0b94130f1802c0e041c03d090b20300340000c11402915180040c240240c800b10a9151400c0c0143e501a05550714040d50b2245030038140000c95000902c41c4d2103071400d00c0c50420703a2100100485440c4001d910340d580d2400d03241e04103d00103015980c0300a51040300d007100c400816070403a8411300d45520312a50291000041603100007603403803c0840303440105042001590106554002c6a4541c8062600061030380e01c50b601506008000e8030140c0845c10311740d0480f140080110141070380010012a150300b424908104024000320890f80f0900c61510341582e0921901e4040d07080402640000c01c3d07071403003642d07410007511551090710380801c0c5043c1c000d60800040d02030f016402d402210318403404200e5031344151260042054200441d03450004100c0044200b003030001614003d801500a0040110000000b9045941c150f00c1241031100441c6e0f401d9455810410f60003a8502d4405031140c40e00c0c0d8002e9402101183d030303900792020342c4003107080320703021130158 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 852606735 1250 852605485 852605497
    0x70606090f02070c03031115040b041221020f1c06061b20010309021008160f0816020712150b0609090406150f1509050f0a050603100b0f 60
    0xc08220704240311400c0780591259050180582184150410002e4410a0380e030284070030030b009550491407040b2030812041000ea40c01d40740ea01540e02030209000043e2501c1e20b41c4451802d114504d1441c0c0c1500288500341d0b03800e0f0002896000c110020904601c00c221180c40c54860b00c11442c6400c000c078000d00602c203034050900041c5080200003000c51801a080000c80d0700700030400082544000340740320603050000102e041503190305000340142c5407110810705e0420951170b02842c07840d1091000800b440c174483c42e1003c014400c4490842c05411420b055001240050300385075001c0000c101340d00d0540e084d40003000003aa03402ca0385040c01004000c040b0000040d680a0013042c1350708040000500039515040d034080f59403400310300016029401442000000521400303216660340c2c00ba1005041075015242000016010f40a01c0d980449642d000d80002c1f10750b465180b0280000c117903180c1c0d0a0241e2802007200201003211128030340072120050101d2020315584002c03001e080b80042c1c1081e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 852607985 1250 852606735 852606749
    0x10b01260c1323040e0312130c030c0e090a0308010302190f081e0105060105042c0f19060305030a030207030e04020403140f120d0506061605061b090d0605091002070606 74
    0x15900004044ca0680104100010000015810110b1034150f000300081c024007030001c481481152480010600400540150f0180d420308080c3da140401c640c543c904c0041002c001e03504044200b41c0000e4020b0100ca040d03940503200000c5503122246544044495500420419540008002842070001414886040005a54a11541025201c0e07800e031003050300d000340410001e010920070b1307031180791075046407031800c4654503000e001204203140700f181c06a40c2e105590803c03504016459102040222098034002000c2000707a1950b110107469000740d0001074101038000078000e091600c219100190758078000c10841d0748a942e480c5c601d17031414402444103018000d031241d11502e100041100c3d00261602c005840ca440b064280c1c000c001c0c0001814940d0008007403001c440d001e10701040c083c0d1a03034406e200410301400d0103103a00a0ba0f025146a40d10081c40400040f02941c13107001910314030316403220340403809495603020305040018006510382a24400704d030110034001e80d9003240080341c0748 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 852609235 1250 852607985 852608039
    0x902180702070b13051002030d091b12030c1401060801050c03090d090605030106181e0504290d11060c0607031a010c02090424020705010b01260c13 65
    0x540c3c0100703151030090a11103a0440c0c10000d04110700c0c10410080d0301c401600d44140c6c0c0ca003045003204042125401c3c04150341410884e80710f04400b800c142c0c215006810940c00300c14040301c081d0b50040c210080040c00400d034840601000c0007015094101c400685400c0d0b0082c4000d1400302034800007504100c5030b04506114010511010300d0058805105032111a42d40d280740d030303007884020340b4044090010030020103815140081d44e00b4011558580340d070700421413103c0142c605400c1005885c9403494002804c904514000c0001000250395480c00030191046594050a810105824624009000d420001c0000c540105250105005200300c0032520200989201e03504d075545004c81da000380c1c6000c1001c80e0031410143c82c040010741d520501c03803030242454040402c2040060b04418100b8561a07801244520810600380569901074400b0310b01400011212081082c6010400c000682e4142d100300c08214054085401c42d0f861440c2001c5107980580d13107411039194001d2000b03151303514800e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 852610485 1250 852609235 852609239
    0x1104031103061e0411030709060b0a02100b030a0b0402040b030106150912020904260d1a09330d03050304060e0a080f13050a060503070f031112040204090218070207 72
    0x64440c844140c40003c0d20307401030070740e481359906400b6100d003803a415403500c1030503400680c00c0020701800e0050000707030032019118800490040d141407c4408440742c0076092006080150b2000519424440c1e0440c00044298a69002103401002e0f9002c01d19019401e22802044074604107440c1c004c540f80740d54421b1074080d41e440442d4500700ca8000000d61041344c5034007007001300f222094075410034054801c012410324000042860305500400032031038502d0302c500350011303402803811071522150015904680c81e0310300000d41081303800c0d075440307005280d490110a051200030010717006100300e407000e0001e08071035555007000741850b0001c07103045540c2410486c2c0f9178200c42002c43d00450207079100300c02031300308080c803034461165801c52000402c105040c0500050141e45a5044100401144d180c1a40d01c1c00e114a009040c200701008000a042c20300542c00c4201d4107940842d0038055403210708201e15221440050054000c8000296200c030480901031280f00c240c1d91003500420290b001c54003c10703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 852611735 1250 852610485 852610501
    0xe04111201150b0307120e060a0f0501080a061509090c15020309031f1416090e0103080405090601210f0f15030f0c030b0c1e04081906110403110306 65
    0x105080160381c0d00d0b80d40e0714020000103540070003a54000300d844c213041e41007030b44c501c542c0710444940b2080d003c02984900c0900541a02a100b031a003a805894414020b660409030241e40da040c00e604028507043c1d4520000c0011165451104007078020f0407800d0241c425541461a182c0c2e0ed00d00172200c1c410b0004040e40c1900c1e00000880d41c0c080400780140825600c03031035150617011010900f0210003600c40741d102032810b5880912602c1441c1890981801c2d114140c002460041c031504000070703840c205401030000c15941c0081c0c604650080b04c0350070f0a0354803200100c940c41e1031207036003102424040244840f50f050603008007013030791000302042100e101e1404054081d03c07040d684040035003200c0c0c0c50901c0401d0706485c400d00780502500b03c240185543e40d45a600e903440880c0d8031581c40b403000c81c400e9501e491102a008016000d001c5085c02c00d401d200f54140c41d18041c8103511103440408010204020f49c94004540070518420742e50748565407800c0ca81c1039109a900d1241c800d005640c0082c4100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 852612985 1250 852611735 852611741
    0x280f0302030411090c0d020d0504051603050307080c030f03070e01180b040302120120030a0b01080c030106110f100b010206130507060f0e060409091211120a090e04111201 75
    0x510703000f00e03d400c0300c24038210a000c50203c0c040c1c114051240104108409400c0c540028102032185030320004443c80c05052035405d04407101c0da070341e01d04d1074480c000700003191002055072485078002200c1030761441e484016900d035100b011a043c2200c0c40100401964540002035241e031501c1c01c1c1c0b01e0359440c1c11440c2c40c078850354015028002401106100034000340c24080325004101c0715200000945109020700d14000481000410020070b030300001304000d4030004d01417076a5010080c203103004181045402c00c1540c1c001401858200500c120813800c117007004000c521406130100043d580300c140716400d46c01c05841c03002c030154094440e1901148800005000c01c0ca0300c1604071000d000c4150034010300b01c0f40281e03000c0800d0b007084801c4100008a0350b03001c00074001403903031a1000800c80f0441c0383c00f40c01a095600804107010310790402d045a22008110710010b000e04d801904d942d05140c10058600d11000d03001300c0002c840700340401041109012032030781032030300c200c81210500d442d49007942c0c00d0f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 852614235 1250 852612985 852612991
    0x80913060609140a030209010f2903070e0d0f140f030c10090201051e07030905030f0c090c0c0f15130804090b0a1701061505040305071a280f030203 65
    0x101c4101e0208a52110000304080401c0f004042c42002a600c1c2c00183c00103000b81c00a1500c1240d08008118400c004030105101c1403480303c60b06801003c40c0090700301800020900405d008445100d962280e5420301e0710050154408501c4a22142d54240359294200205020703102340720704081c418a141000003030356210000b540c000c1400014068a0001074070007200d0480c1802403d0040b204080350040b80c00787c03100140080c107a2103040508008061004580c445d2f0f020390840c81c0c90304c10202010400100845069503520b09a4032003201070080f030f200d02c4080800070b0040700020314070054007051f60020030b4110005102c242e125074010042c10617500700d000740b0b02c0b07000300402c00c03813041c1a40013542807330002031541d82695518580c02880c1401c0d81c1924030140d548203010b10550545c642d480804804918040e42068159690707590388242038004c807480c1c910310545020071500f00310f00b16074000d041c0e0120aa0848041c07404800c081c4021001d81e4081142c0b12915032109202c0d1007070ba84 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 852615485 1250 852614235 852614237
    0xa08031209160305253303060e0f0c04090908040317041d07120e0313170304140d0210090e010603091e050f12070b090613121b0809130606 61
    0x40d00c000b51456100e04400700c5a8540400ca00f05d05000030109104032103441c030701d030306903911011841131001141c8034011881d0244051616080050001c084440603140c0d0080454121b1450703521aa00090854003565005c0e44035241130101d00c0c010404211302900449100341280d400000742410303414558010303800b4217840c0100318007601d10810a003d00450701b203500360600913400c1103000f955005440c40311080d111030b0351000915000c01d00c0c3d000404030080c90302403840042c1001c007684298580c4280e00c5503104401e810f101414183d5a181088608a0382c01030200c40742c07402c2c80e00003400c2c010321032103089602c002020002403054001e005d1595240d074041c0a40042000d400c4a2030a00500b0720015651413040010300804220f04010401c1d60940c8400001c1d01ea21483c6064240c0d10002403000d06580c01000500420300d0b151000004503a40c44030300091554a8040100c55040e00c9140011120307000d015030806004040000308150742c8103464202a82c072101d6111402c2c0e400901c1100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 852616735 1250 852615485 852615493
    0xf0301111b1c2a061b0f02030d0b030312010e070801080f0c09070c05060c04050f150d05041502040617070305060d0b1009050109050109140103031d0a08031209160305 73
    0x844a11a140070110860500a0401c00c0030810000f8243d400100000b120115612404e403107549442204820b0400d00615140701c0110000000944a0050400340003140f9110410340103169070a00035503141115050b5240c80a42e50f07143c0855420005940000c08681010b0010850302004a9050315030850140100101c440c00c505106002100614031030420003100401000158280a418002d411102da156121801d11003080511006460100e200b108821410710b010300499055401c107400480000410355100d04115068203080440b90426510002d004a803c541007007800d050b00d1818130002d42ca0741c0d5002815000c40d1000e4030b48540c0658400c4c00c01001510380110294000b40c0342c1e8200711195554000b81e82a00c0c0c0a030400305420b82c6620042c408045180f0440039042c0711003440185551443d1000b804a4a0031040b0040d007151810603401141c031048013160042100318100c80c4ea480642d4403c604200094400110074060380030080b01d95008000c0136000d9a4000d4007030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 852617985 1250 852616735 852616783
    0x409060824040309030f0606061e090b0c031603020601030c09050c090d080c0102040303030917040317030601021501090b01200d030902030a12050304260301050402090f0301111b 78
    0x34010180014070072420040c01038800310000b2051002c1b400114030840000c60003500340240a0050b840036883d660545070300003032150855078016102c404841c404190f09036602c10541c0302c030342184900c040d814208032038115424205603000034501c0c1281c0c014503904244a88542480050300c80554101380c81d10818440301c0180d03d002c2980100e094842c2001900e4040d2201d01542a44c110b03a10580110f86d403108003d00b4000005121412443c824041900d804e0455842d400c2e60b50030490500101907010000494030b034000c2001c20f40810760112a81403541c0d50f03c8051000c4c00350188180e00013403000d60890008042c1d0040810484d00c030402415041e02c514104400918115200340c0c1d242c410101a0070104089010803001c800655a45075030703034a01400c0c0b48111840514038800c0f041c2001c1490f07140e10f41c9070700035681521021078015965000510000304c443c140391070b659600d94617001151464034030140041c00350031070901052140324201c403040d03522030b5207800e40b03440701281c1030041c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 852619235 1250 852617985 852618043
    0x506090f012f15060d290f070e010f050301050616021005040815360114180714040e0a140d0e03011e05090304180204090608 55
    0x400304800061400080d8220601c1d485604281c02c0c0e0319107a1541070310a040840301070248840000689460b100f601d0609140b408148240040000070b411400318864074070300c1c6007421520a480e41c1105945d07005ca802d080703400100a40060b0740f8803000c1000c0000c0c032002c95020f0040c032003c00f15191039290031680703403900788406e5600040042c0d400103144a9030f013006a84004002c01c94014580c6c8950300c0c0c6043c03000340ca14003441080642e15000101c81040132941c42e821030710b0040e0035400703144a200000022100d124401300c20940d00da5500300076052195441400c42b00c0c6c4101141c00044c6584006801d0507926440c440c00340c003410004400591b01d440c18150072101ca82140402203500c1410503071144201035460713400c82d445680202004420f00c550003001030540c000d04400801540f1034030300060702c00c00d001c00e400c0e001c000d4507080000d81c03142050040c1d400504038440d11050f03844071401c0c0344000754814095104c0c7c2d6890814045030303601300007454001011940b040e0941e00340003180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 852620485 1250 852619235 852619249
    0x1206101707020a02040e01052a040308071a0a09020102061e0a2003090d09091404020f040f0905061006030c0f140403080a0c050606040e1218030a21020106050609 71
    0x806070661080c4011a40180c4481c400c1031600b2910030000103203400e0010000e180982450b41410011109030f9800c4040c203100c2046808507548800d0903a500c0c1000d1034540c0e603840304191141a80b29903841008003903102500714080651007642540d1f40c13955014950000e00b000d00305010003201a6400282c40080ea80c1d000c080c080d520f2010310360040d0520b085000b43c540c002c4591290380c2d081045280030440c0c01c01d000001600a0100c2400304408090b00d2405042c801440640300314025100c1c2c8145032110b900c10098544010303418800e0502e681400c0b80e42e040269100c0350300b40d0081c10300042c0c00c0e21a110b03e84d0941203e5441350301290a0070000c03146006a070380f0501401404000000c0015240b41c020444109140c81303140c44401d250610030f0518600900c464013583c280b900410380345030041080d4144c64601c040301da44410134900350300212085000010323054810700010b101400701c9800003651485040150250389501e180c400c03400e0700c045104003030b08050203021091452900c0c01d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 852621735 1250 852620485 852620491
    0x906110a05270d080a08071407030c02040608120c0f03030105090705070311030d0905010e150a0f02043501090309060333080c0102070e0f13080f12061017 68
    0x10b041180741918a100154444440e06400c40e100100003c08414054010003000da0000042c1001c80420400a8040b28244525040201003140d6079115508540d42c40c0d0089010380b05d00403c9032650b012652040d10540c0c070040700151103100d901850308044900004803070503104068001203654a80b03140603145900701500440c14002040c444501070842007001c1c0841100191000c640e00d90f882c00c0081c02c6600e01481741001c3d030031120303414007a0070364040d00981062042c000001d04074601500c600003405184c02000c1c0c00c07004e0849034400d4204140010400b80c50580000d11140c2921840c2800c81e00c02020040c04a040c1141c00c00406010b80c1c00480903111103412000440c1020004022034007011106206407507400d07205100481c404c104110340c0030020b000800921b810024060b0f0228402066200507a80020005280400c40c0c0c00d9040056402620680ca420101d00300e007460380c21004a422410103540c00107007883c901a90100300500143c4c5403104441c080c9902c0d591515001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 852622985 1250 852621735 852621787
    0x310020903030f031512010c08010b0a030f0f02030403091d06131b110f0115051908121806040612090c1d0406050f0606190e12010906110a05 62
    0x6122203c5105000d000030b5224034160146071101c1224030f4100301c49400844075070102a80350007151075420343c02450450640e50000d4107103450780307034101080380640543c2064000903810030400d00c25568540d0080c6006501c640ca40c0c003281e80c0c841604842c41c035070380e980c9001e5582094000c00c5643c14061b60030401c050640d0800300702008410364040c47c0700180c1280c80002803149a400b69003c006005c031010b00740000d0000d102094403a0f500c208802c0c1c45002d641c0c840c035082c2017480c40309043e2194910003000420140d90324412035000100032074001604403000c12580580c1469103140c44021202900e4103502c0d00000d00800d006074100808282c40101c50b100701c1c0c14404901a440f044200d40c80c0c101540342466140390a15020707095500182c0802e100e8400310303081c8115a6200401d5600b00f0f100200548902d030072001d005c41d9a8400c0420854001c800d00b0444030300f140d0190841914507015a01c1030100031000180e003003a520400384294009a418048030303040700e481074081100c1a46c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 852624235 1250 852622985 852622987
    0x1020a02010801031502211b130e0c1312060b09040305030a021c050c0913061a0705030d1104030b06030706141308030a03050103032d0e0316181406031002090303 71
    0x41d080070740242c10140c0c0c0b0741009210821040221040f041c4440c1c82200d4403031030341235042802d450f107140c0054205002e50b89035092400d00041e0540111003d0360b00722900c1c0215000d0300c0750340b512540000c85071100e0503119682408051035250420380d001c0c7c4d000729419503820307203942d403400c3c550b8000303400002d0707541c91040034118401d180301f42030f004190044550707000c0300d130703840b0011000c00540d44001303200c10015078200081044aa020085041c65038648080030340e03030b511201d241c03a40c114800c0821140c2c01900d010180c0d0007541400000c1c0003928400c0c80e001c0e030303603880380c1c0201a0786455620131817000440100246c060700c0d20010182515001400072a07041a071203540303060454004089101c002a1f42d00010010b0580c040c0c2c842290000941322400704203004075251f01c50f40104e200d01003d110403281c0c440b2852310104000c142d0030511422281201e92104071066603024481403e10038182408078101d260103086060034040d0100400806040d00390424090207500300c03400301030381804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 852625485 1250 852624235 852624247
    0x901020c061308093c2b17042d05190905251e0503040f0b0f011a09030705040e0705090c0408010c050306030d0809120703031a01020a02010801031502 66
    0x140c9135440001070500303111000c0303005c4100700c01c440b114a110703101840480b040c06607444107480703403440000c5100a00e00080381d44d900721410328007a02e041c264003c000440b001d20012000341d8440140003507482030155206110084044201d200d08040201440300c1c440442c10000313450006050074180025507a0318520076502c0f9101c1084481c00c481101c00c002c0740607000242c454603482c2901e51301c1d1181c1131450304010551210288541741c0d80c1d5903024840e0010218041c021307100081c014440e445194402d140c13400c661390f4000c2640a02c1980024002e080c40c00b142c0302489401c1e19240c80e809002021000d00d00002c00003e440d0190413404a0b0240c903501003030302d0321981c01c094032401764500d030b440d030302c0f4035008100b8211b41d08400b41070104581032092040b50b40d008103103258075a40501d00401683c9588800d141010380401400000410010b200410150160002014844540c4032010203100c900f005a0f1a140044030090000310880014400240c0f200090002000b4a417001801c000f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 852626735 1250 852625485 852625489
    0x1806051023130504110a020304030312090804140a17030f0d0608010606021507020c0f09190c030e150108071505070204060f08010f0b090c0702040b04090b0f0901020c06130809 77
    0x540040b8615a401a0400042c01241042d01401092901050105140840d00c00c8025180d0182e0b000041c2001040081d07480c4501968221380d0407035400083c135a03035071665003c10041d40b074949040075001e00910320000034100000300d080d040480d80c50340074501d49114040d400510344e002561000c00342c7c0d40e4240100f0000024401ca1018041030380091483c0070240340e1316100240010b0500045601074500c410103501d40c00d419044060054500d45866118a45140000241104903901d22450308010807112035040d0421503d81c1c0558094403000300301c102668815500034044d90034a40e000190400903400c041092400740215031810314140000ca41c001002c0d11032030b078044880c030181c0c3c80007800048000e209240101179015001c01c03044d5a29400304424060003421070020701000f003004020b54a4641103c08003000082c8200074140c3c191400101c0300d201907481002b031540c0100020100e45051088030b140c1d42000006082582c0d5400394000d18481c481c0e011106143c09000c0d0403295 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 852627985 1250 852626735 852626737
    0x11030c070b070302060108071a070510090c050406231219050303040c08011b0f02160e0a050702031c150512071505070809040b010302040b0d061806051023 68
    0x6410074406050b580c555030705000b49040c0c010b0f0007a58480c4c0001d20100020381d0000f140060103c94012042d4641980e0f080085c00c182c040b4a07919035070381c2001070705000c001c214407a1034251082110100701060319060100e1820b1048280f0382d01c0b002400b83e41da480f0f031500b11500104056240121210020f483c0003a0a452010042c111161303407011051008014410180101500c0c00c2c100030080510843c00b0b01010340100002c000c240301c070940c0708a110b03070710a01403550106000c4034200011551021129402001158100c00d064039040101d41170a2000c0101c0d01307a0103801c000342e100540308020342e070010005070202d00f04280e008075000408e5151808019a08000c12000e030501034070f00352914007400440c0900d0400c0100c10006500091001400c1c0c40100c0c400380c80010704010583c006078000c1c41140c1202d5002400842d201c00c0120703680d08000c00781c1d40149010303041d0070304060303031501a00c003103005071a403040c83c85a150408920911261100a50135500741c0c11149200e40e5403030309 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 852629235 1250 852627985 852627989
    0xe0a0b0c0f07050a3011010f0e0a050708010b09150a170c1002060621030d020c0a03091e06080402030c100e0a0506030f0f0a02070b010b0d0f15050111030c07 69
    0x2580d0031130154030040c0080d01c210600c410045c0d140a070682c01885030300c40550180082e084050180c082e20780d5480b0282540802050b00b04000100a51940420100c2d030700c120043c2d0071030b2584201c0e1004168468180203812241d60054a010a551200d456006400800b564956082400038400250802444120300f04210700d40c1c0103007100229003414864280385502c003ca05540c403c00030300c44c1c1515104282e001c14481d60140b1760a907104400c1040c11841007c5012203214000b14071740101100218481000d00e100b80c480e507180a5858285000b480c000942d0410b20780503d910401002c0d010300c1400390b200d0310081c10760b0041d009400001d2041082c40300b40c040001c112503007840250900191610142c20105c84240c01d40c941001d815608100040c00f5841c00c801075808034084104680540d06000c0c0d00100c10b24417903071506108941030b04104250b800d02801c2c00460704154060b407003200300150b29810000c01c810300b0180103441603000c500c1c1081c0c42d84070402120046003411710110780 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 852630485 1250 852629235 852629243
    0x30301060507210203031f0510030203010e0a050106020d0c08070b01030803070207080a0f140f06090d0909151511030d0903020c010f0f0807141602040f0e0a0b0c0f07 73
    0x24440c10982000c2d03040c6181950503421100001d88403200f400d800009403a0b0005600c12203003030f071075102825400d00d031080d6804181c1021001103118589501600594140c56040c8070101c1140d941400c2c40b429201c0a00c80c0c03a0150f000040c1d40060030348659031409401e0700a185c000d00c0d1503600c0e40d034a084100e00341c0c0169030380c1e4004028041d116605200e4030300101845c00c02401d29081da61245078880001120003080c40c3c0600302d92440703400c070074003c40c10825030800940301c251800c8130f00c1c01e4540c203044002c1e07000642000c001090286a1744a5281c641c04090b0b030307c4090700c1c00c00404030044c1507080d419505100c2c1c090b8003850014000c0008001841c004003001c115100980350103442c0001556030701d414480105001080158031140e41e1207800c282d40360181c3c142c1c803203020507941420315051001e072008002900340201110706114220b0b85100ba5420440351180c643c600007210b0003440003e840c0d410584684011402c007400e09a0420a4410301c4d42ca42142842d6000142d1310040c4225 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 852631735 1250 852630485 852630487
    0x9011403010e0607050a26070e3607030e060403020102090906010f1d0f1002012403200402090a0602060717091e0304050901060903060b03031801030e01060e072f0a230303010605 78
    0x14403428503d06252b03039005030280c1c0d044c0b4407003210391140095010030800300360312091900044249209030484064180340d101034443c50305003030400038080d5000f0700840b070003140100d000c120b07076510074014000405240d80e191038200d001040c4030320f44001c0740749019a0091500300754080342d40c1d949406d1180d6101030b4000080310f10201503210b0039000381d1201401d2071410800c081010030001e000c64030300903503000356142d0075000c000c0019009000c0c103221f03c0d4110f0441c42c00401c403035800082c454099481500c03214403d00081290350780e0080300721032018031a080822500503180f80c07040210303d00014641580c2c02c094540707007c100411800d03031050300012080007040061201a106804604030241e0145180000e6150896042c21210400a0406980d407075403d05034002940014060902494414058145440000d10315441b1080200ca840442031120101c80e41c1131000141e490f20b00b60113000c107101d01da1661200e8030f072602401c403080107601c11035403101c075001d01c01907004e0720703003a1569 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 852632985 1250 852631735 852631757
    0xf0501060f06081f083a14070501060b0d0518060c160503040302092a0703020303010e0c0d0c0306150318080a231309142409011403010e0607050a2607 66
    0x321070704e00703400e01100c82d18407604d284512070300d90b004481c1080c006a987d00250b44101a1415038014084d030b50003078040301400b01c0c0e801d113909200c1c1c01c0b03203002d0704508002ca543c141c1c0080a45403940c41c2540c071844180400c000000c103401601000c80901800303081624180343d601d40214101420482e45588005a09640c042d100c0b00000b10740b018001c064540a414074803144d501a50302c0c4410701440c550050b004000900d0b14483c901210303000310f5022410b00c810b00d402380001c1c001e001d4900407410744070040030002070200d2082c401c0790b80000d0000042480302c0415250950198400c1e8615410403500003454443c44682050020300900021482c03503403010b00c480d0700001c000e041d0300300ca0003680c200040c0307814688114403090b8000d6010340c1e00c1d0400035000000c600014268000326130308484550000508120310010428160074150005d0000305c2c40c0041d81c036250082200e420011460a0105007200b5115000000300d42403113421702c0c1c4810701c2c00d070701c24010040100c403944005005a490 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 852634235 1250 852632985 852633043
    0x513140d270303050f0408010f0920150901021507080f0f01030503031603060911040f0e0c120712060b030601110105090a0206090f0a030f0501060f06081f08 69
    0x400340d80040300790794041d184501d0220760107407200c1d500c005410080c01003840e0301d00c549420111001400760307200070011810090f480d08090301d282c21050700c1700d90481641414003644400540450040280001040003920000042c00c0d00301400b40343c114820542d102012584200840f0b00a0391242c844440c185171203e80c04500140013031103c06040e41010041000134400000c1e6034000904c2c68142400101e203020850040c00715a018000045c00c005140c03100f00c416100030310540d07000c4808002c00c2c81d1103000c1560b4240e4103a81e069100d100800004a03e1000079540c142c1000c0e00385400340c1c06141c140000e105560103500151085040003051204568000741d04201b5a0000d5000380894607004e094943c5900406070061702031000062210001c0d540d00c04919003400e00103100c1c1c5003540d221b05003075009080b00d100440300c130340c030780b0394041030b00400307110101c0031151190780e02c140e00e95509040300340d0350190380c80c40e00c0b0844640101180703030303442031000180810305080004800c5451200b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 852635485 1250 852634235 852634247
    0xc0c0f0f0b13200f0f030c090a06170304030822080a080a030e0705010e060d0e01050f060a081209130e0a080a0207050d050c01082e03030807050306010e040513140d 72
    0x181c40d403100d943d0b2007680c825100c282c426030101c8421070301ca0102c11009404241400c0a0809856004201c41c04000740520103038411003d070746586152010b9102d005402036500e215074000a810f40c0d50900070f02252000c2080c0c503038802519806011201c50340d4a003140d14200341381104403002c5501050f9550080d5140c401c90b000544c0c0e00c0023310f200d0f4a00700019000000c81420300d40030701400034107064400c00c0d6420492540e12100c0007040fa83c07403e402c00c1500c907801614914444e030288000019104400941e4040b1040742c0b0311124685008a02000240e02030115451859a103621520340000d5042c403020603424001c0c600f486e5200e01464000b418031401d1381046100304da0303842c101ca020500004103500303655400c1c03c0580064440c0802c10100812001444480920840181d0f401a0380b080644044034420385881e0540e851b06402038405009c01c41c0c145000030b60106c0700c100e26140c107070809a00324017406a42c2e00d916030982c60740786030120b03500200700c4641c5c0021410706c101d03030b0300130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 852636735 1250 852635485 852635513
    0xf260d09030f0c0b012606090c0a050102070e060409030e04050a060f08150c0a17070903051e0303060d060f0f090506010503071d0a0b060406120e010c0c0f0f0b13 71
    0x110701580120312582d41e0131449803041c0901082c1090031000f480f10003c0c032454246401d01904121001e900d08404210796906000c1c0390240101e4000c640010194000100d0505503003254003800c11030b42c4c50b2010300c00180401c1a09030308201c00101c41128030344892207464000c64008502042603824100c0445000e11598450b00c01c50b132040341c181c850030111f003003169080152400c41c2c0c1c0ea0345400000803180f006861a0490300244140207000499070061195821a44524141c2c0c044075040c9007546409265060403192580080000035841d1400c104c03031050207480341a000400d5446040310320120382c00c80c400044410754034402c01062290400019005100485c0144503090404501c0c2c403044070305008042488110601190407100c403a005510004000307405692559a40c040041c50702d406040850719139031410861005555060080030034103c9151201d00c400a41c540d661010940d0b2481e0613140355a0003441c0d600060039110707850b4015841c0d07810f500d030311030141e0070440d41d0f0300c0c144 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 852637985 1250 852636735 852636737
    0x11010b030f03040e0c1e041403030915090102011d010204080c030c15030c0702030a08071a06032112180709020a080c070204140901020a090f030f260d09030f 69
    0x10008405030701e0010440e8180c2e001c04050304e04071344031040064118002d403e00028400e09100140480f00c0c100d03009002107504030301f2031743c1c282e4480900f49030b100d11030944130360b070003000d02c11070b2448800b4003500410160506100006001040e0440c4103100721042003e840c269400041c1040115020070400e074111408501a20b502441c60b400141c0c00401c980b041d80c5501c001000140c00f60002c1c0c0300b81e4210540182c2521140c103c1890000b0042c3d0082070308130755502240c02412001e11080b03180c1c52094102900910807502d6500111100b109114500ca440c60402c100000f140c64803401e00c00c0c000c202940da6280c025558080315810300300710b50890782c0441d10500040740010b52002c00f40e80c00c819050442542c892050000c20054100c02d03450f2810030b60f02d041405507000d415401002a040940d456017140354849034401c151401502c000303000070703c504282c1004035440c4054400100342c0c44901040b00482a903114400750030011186000d29a901c1c800824560000524004c107155 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 852639235 1250 852637985 852637993
    0x41b0e01030e07090b120d030c1e1205130501060b0307030c0f0207060c02040608010c09050301050105011b060c0c0b0906010303080a02041d0c090d081b010203040c06080705130611010b03 82
    0x382002c0d1561811148680080d40e6140c200000b6141c8850864616541400095540000c0c20400c0075000d440080e80d44000603180701018100c8400008000c090600907503602c0002111a022107009000040e08820400101006090000b42d00b44900001003100c00305158130791400030740280850350600c480209001010040c40341a903404204007061f92068145403102908900205004010b1034006040d198030300751075880556000040c4200f1031300200c0c000d01c0140c0c1c03900011120400340310740100c1580e10114200740010119005906152002e180c8002007a44580710501d2800c01501c60501540221005100703066118184a030f0001500b80203600d054034151445561034980411100d113000e540e0081028a00700c1000c40e1820240145111880056414141c1c0c42d40c0c4541c40a034220303c900c51020401040600980303101e260403022a0080781e01d480000d882c1c03001e00a0403441041000c10415021840c2006220040e0040d40d441440b40400382c103002c2d08640740001900d00c0780e80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 852640485 1250 852639235 852639251
    0x605070f08160c060c020604060608031e1810050d050a0b100c1113020d060909022d061902061b0a140706020711190b040b09030c041b0e0103 62
    0x80c1001400b03070405444070444800c001c0e511003c441c0750083c0440180300d1402c0001d020340d00c0368001091030040e030040b20100015555210510358910800c1c440b90440070031030b014290544289005071481558602481090580c3e59001460b074010308540710022136070114041d0414802403285070350041c1c803103104020b4411810002007d40801e24410001c020a00700068100b0420700000401c407030010b0210390740000c4548036100a074001070400460300d490103d0024000001e80035602c86581c003d05599aa1003045020221912800356240309000000f10340c842c1944658005006088900b0386914946e40651002401c00501500700041d500710f07221480c10004844046490320082410059400841d9010700d9001e805890000741140d480490084180825080c2c6800b100c1c1c41140e40c030a100032100d10450340750340e1034012942c80340d20500051011071101c0c1e00030480040f0007800c0f11012400440041c050f92024a044c0c801c4507031003109083d16a0b04448020495202400d040c407801ca = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 852641735 1250 852640485 852640487
    0x170c04020a20010629091806011101140705070206040b070f0212010e06220b0408071e0c050607030509090a0b0906100507060b0111030c031e090906130e07120605070f 73
    0x45039482d841c91016401400c100803034001804c85003600d00292031f4a041e04a20b15142c4050142201c00030701045041d029189517601c1845001541d1525071070394000f44d222058122541c4d0041e45007280c00c14400c01010960b001108058035003688a00f035950000c18191041c4500545104020040c0c1e13130501c010540d41d8900440d142d603002e00c5014001100304c140c056081c19400d58040003412084a070070901045c841960001c0c207089001c0c0751600a1342840361008000342000003c040c1003610f188000b8860392070420004c0801c54005d11b8054180903076180060303000751054a5580c1030035a04d1600005c54100200c1041c0d114200319062054032000d00000341c868070031408002c10050b5644080010baa010306040ca42905007041129144c0c00903414103640d1b03a104407810b000c800382d8808c1c001200d902c01403c440360303035101800300030090321384505001030301c007445504a0029450740c0c3e0300062560200810001482c0070340d43c0c500200740720300380042121800b8041c0800c100540660340c07001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 852642985 1250 852641735 852641759
    0x9030803071103090d080d151230030c0e060901050f07050a060504080403050105010b03010f0e15060f09040501121e0510140f0619170c04020a200106 66
    0x1151003800c290221690080b5020700790700c01c0c0d0250340e0340260000300c4a414020210040e02034184680f0082001018010003520888001e2140e4500c0350302c907001a0002802900e44040c558089503030b020003050a01c8854400407400050000000c0e517030781da441c941c59502440c8524502019240e01d4504207450000030a80d20503542051034500c000294402002020400055242e8214104105504091500e540958001d11058030079609000000c201c2d15018011641214000ca4492400314a0440d814142d40e00003020842d41d800c43d00c5020409882e80300c01007440060200140d59a007040304108811680103801c007203034070146007103c080054252061030207103ca64040d118420340d41c03440c1140c5411202030000a0550400c000c014030000700114181c02038402c0d02d84400385076100380504c0101030314a842003140c41070141d0108080608401c20804502c82e2106a4140c00c0000d000719007039901c02c444403c00228a0450007421a8060403a0301003201003400031b0042c140780c910340f2582 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 852644235 1250 852642985 852642991
    0x1031407050a0507111302070b070201060803090907110607050a18150804290f010902071112030f0c030d110703120b06120717070309020a12020103111902010b0109030803 75
    0x2d0000004000c03052140441044000c105c0c010480c0510f515121411400ba4000003001c440c1c80c0d0319000400c408500602401082d1025000298100700c206403c02020381c0000c1c1914003840196003410400340014004d075440f800558840e641d40d441c0c0f0307440051180a40c51684110310740b131400180000703e080080245002100d01c3c0003d65030321603040c04e0300114400d24100c552000b6240c2e5240d0154040390b4030601c1110000e0708585035a0361035040384264031031200d008099209449030302c03c042c9843c00d04880d0080e002e40449040800906e4510b16079840242124459030001c158181059914085e003120282c15940050400a0b195005411107405901d06000703543c0340c0054002c81d84800c000e5503c03141082c00140d0042c01c1c90300c00540003c0b000760444007412106800224054041d001ea6096140e0180c4002009850a80100c0854070740c180124100368441000c5401c81510300301070704224242104540c4481001e0307101908540343c4981c0c288c10b020f046481000403e2104050301c0d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 852645485 1250 852644235 852644237
    0x405060403081308031b040f092a08040204090c090906050a0c020a0b0c2d030405010c051611150310210b06131b170c0c0c0d060209091501031407050a 66
    0x40f580c150804100b580c7d00650f00b000d624440803000020301e003021a00020032440050b0240c10103c0412000f854102d21014a030502049890000c0380042c2000c2d448003519900408802240c1da440d580c04006a0b030381c0c1d1400362170b100d49074030501041142611601014111500040902510503954480a108003c0c0f10688440020410005a030140e600344441406858076414141c0c5515204003010b410990741070319258030700030350016a14050411074142e5010071311000d0304803082d9510080020a4049425046891403020010421032200078600600c04079610703920321400c02480c8400720000030081a4081d418204020124902d1821035030090310558090419407180d08011010f4500440740b0b000841700d012409040c154081c1c0c6000700320005514405070754403140004203450040364648a01d940080c95450294540250084804c5201e0000076080202807000200c207840c00700d4049820904014a8420070340e410b2168205d0356100f03005401d05410700b290000c129025541c1000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 852646735 1250 852645485 852645511
    0x17030f0f1312050a0806010e0a050f01090306020c071a0f0d0b061303120f0c05100b150a1214090a23123a0207060f05040506040308130803 61
    0x50021007080084041250012100040d40b0300d482c0008005600080a000001e0718190101d202e40d849403403010145103009200c00c0e070560412080098480d050341c521418480301010000005256001810407800710401501c4900d151051581031203035042d004804040b2f08210f00f089016402c0d0544a01751100301d40003c2541483c000b1a0f094420000050030003261b0420000400c2a02400050420400c0e654810740844031982947880090301d950050031900180d18040c40d00007035902c802090b410040c50072001c0720307404402c06a01e61000401100280341140302034141100340c0180018020960442c001c40e24042024a071107600c100001442d404044140e0150010003d4002581c007602c0d0058414040920030100c120f81e215640124a0900d00b400075640100c002c0541400c65440c0c0c140d140400c00f072213030080000d40c4411b0040390056520400e0890540c1e2a11402e13100c2c0d80320344020140390402c8d04010b814900003c04881040a03c00703140d03800a1580350035250410303543d28000e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 852647985 1250 852646735 852646741
    0x15030c0415030f1d010c0c1a0604060512060405010b0117271b12011509150b181806010509041a2206140109140301060b04060c17030f0f 60
    0x8801078020003110310f50f07082c10b040e03c0e00c010b41e42c01228034100c00c0008001700302c48207850000359981d01403844082c05504420480340341480c050341031254458001000040e42d40e48a00000d031b840c0b000410710411980c03081c010481081401d1082648085090074041d10f110003152480c50140c600811404802c1806000f81d102c0d0040000e400200c0b00c41c1d40c0030b5498001c180c1602d005030070300204025114244000c10074000f600b06104035810003000e641c4042c22503042c044060042c00404c00c12406038421400700041c0d503203040c006031869580c06218041d234070400c00c08000070b84981c00400d160306d590303140030300400360b0300f0400321401f012003568045841c0c0d81c01d12a550003100035100c01c0350089040b401c0e10b00072021034286411203c0918104002c5103890b5540601180364801005000c40c410b0203040c0040400200381c1e05940100600119010b622540c04030925007195004901142d103152100c410422030845402c4049103030071410341540307008008017080f0300b00030b00104840131000f008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 852649235 1250 852647985 852647987
    0xf080d090c080a020a050f1f050408070b0d0e120d1a301c050f0d0e01200c060a0e0f060c180909120f0c0a1115030c0415 53
    0x10154020307411194110089035a071900359181c102d0746100301e1080701c81490105071803401701e0144440c14070240c140001c10602c3e0540b40c4282d111351f10000188203051100040c04617040054101401203502e0031505c421b0380c41031001c2034031094641980346420409034009502100401c0d030b580319103c91004265001544c0014121b1030b44045555004000d03048690081f5801002d6120000d280503064034a10310400b1400c0e84410b003c1e0400340094004003000b020307441c40341c030103488000c954500c05883d100018403900c040702c0c2d04c81c0c40400d00d40d440b400e0b001541c098006044260b0300c3c0c4482201d00d44024496943d455030001007021003443daa4200711952120200400e06542c40402e0488640d42042074a400164028aa014851030840000900ca07030800000450203a03022200a003043c504058503166260884049000110307400d0000d809400020400141e03c980204040003808020900341b0002030328040901d000d400080060102c418040c1c0111022544c100412007218054404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 852650485 1250 852649235 852649241
    0x306050121122f1e070302100509130b0102070f031a0709180207060b061c05180727050c1c06050d061506030c0c2909060108010c0c0f080d 61
    0x1503c000300a50103d030a2201c3c4448409003281003018608580aa82c0501c28114800c03000f00b0190085802c4240c08200600345150020351301c51250070a103081980344004660b0f140c910b446c150303807180d0301c81840160658040c8421006880041d16801c101415615460044030520100030001802e180025480b0ba00c50b0642d0340180c4082000c1c02c0d46280581e03d100040e40202000380d035200e02d407840c10550707440c11804480200c9a074211521740040d0705107504000381b00003000184c00804111405005d03807401e20803030700074101131441c10103104003440c010394600d1030101c505a030701440e0505100c0b10301104400e0347d8685892001144800f641c0d4081c2d200a0101ca510858008060000e2401002401d802c501e42d1210200d1610f03010590b152400c40c2038840c0f80c1180030210300038003042e001158000401104441c0c1242c40128003050034245030301c80110480303200d811500b0050052044000a0103914020b08191902e000b8200032074890424440181200515040d8001035074004185590 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 852651735 1250 852650485 852650507
    0x702091504090c0906060302130b07060f06090608300d1b0e03160e0a0b0a08060108011d0a0b0109020304060b100e03071a09061e030a06030605012112 66
    0x1e070090041c0c0a5525200035101c640340940b1079901e040c680c021515034440e10030350b4a40c0d08030591550285281c81140d02103984924025a843c58458000342c00e5032a05000d001c00801901000203000c515010f00c40c0d041c03c2c5080f03d140d00d600e940c1c20202c00d402c4524030031003961220b40307400320b503950080250071b40040c40286201048006034007460004541c01042417117882c0816419600b1441850a100b0b8130007085000e051071a801c94008036010445944c132502c10100060603001440ba02d8200031807a04000360b002c0422603450714440c600c0d041f03a921070082001000c7c4000c1c9441000c5a4500b071404605001c0c03450907550100c0028244401c80c0c1040c090008080d114a4042d841284020400c81030003960a00a206d5a02e0014010f8440d4074a0b42e0684002ca070b806080550000400802d036120314080011001d54108000c40e03208100001c40c000c13448403000103101465403800c0819a4816440304420728088600d018180d05000f0342da84201c0ea102403511030046031240c0a0703601c0c603410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 852652985 1250 852651735 852651739
    0xa08010b03072601081902061b03160b040c050118060e040b0301050c0304021f080705250c0e070914040c0507151a0603042307180906050a0209030d0e030307081801080702060c07020915 81
    0x20308590802d03c42c0440cd018080c85c01201c1c1c3c07200c000e0300c6034019196112481c903b0f001101d041321041200f14401c98010b03681c008000d00100341c0c001c001c0000b900b90b60003512511032840307000050008600d0110065058400c50f40301c0281049030184010744105401008031091000005400b8641c2400003180035180340b591819040380100f0b0705100f400ca80c1107000301151124130030007044082c3e01445640c0100d8040e4804003070b110001805002c05000b1000c044001e0200c140400c400062443c5250341445445000c0081e48551008082004441d00c524a50007400b04005100202d2882c140c248207034500c2d0840b070002c0401d07200c1c2c4145030240907031103036180308840c4011266070b051903046014250f006030000e202c50344803011520100c0c480c07509095030651040100d112240e009100a8010030801015603041c032015031600102680a5202007104040c0904003142568010b2002508000240b00904c0b05140c80a14254240f11b00800a8410754070000018109288602554040b40340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 852654235 1250 852652985 852653017
    0x617150402070c0806070f1e14040b040b190c031205060a03050607020115050f090402150c03160204050a1e0b06160b010312050a08010b03072601081902061b03 70
    0x14a804e21916074000740c40d40c0d000155901300400c0d40c2c0f07204607075807801c0303c0ea4038200c08400454003500b03880d032076604005840e10160034000003d584414001800040102504299940188a0703805a502007500d92810031322061244c01c0001c241d1182c40110041d50440b40080c003501c43d1800a00d0411040c1c0c03000b0503501c140340800064684c107400090551091000344000140c41d041003110002800c169a608403580100041c05072514064624442c1c05484103289031000b503506803810355001240070001075440c000c0c010700718102031041c1d41c2e00c810019420021155000c1d4028901d82d191110b0080c080d4581d20703218455540e00e0100d0b40180f020003842c0442001500d0070f01d001e00000d10042d56443d42c030030503011000d4002e50469114241c0340c0d54051482c2e003000098403e0fa000504403808004425030005010b10300c004a96801c0c0d085101100480d40c50070010381d180c08140944684401901074002c070041e1600003d480d40030018604141e003503140c07050a04c0c51740c041d542040c004080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 852655485 1250 852654235 852654239
    0x50307030e101d060c09010e0a030614042a0303180902030a06170601120f140307240b031f11030a0510120312050903041a130617150402070c 62
    0x7a0350108074040f60480d807800110302c0110b41542c0310503044407824008031080103280110740c481e580320a00c0640080c0b0040325140ca81e00c842d004c0b41c031005498444152498240301c203010301d9041e103000400091f011001c0044140110b05804260382c8401070a1245982ca49000c4040310340994002e0410400c045441e0b1400c0f002060281c911841040801c13180b003d40920190004a8228161032030310151030301940540e48c2c4d400d644500300c08195641002d181109117141418001001e903180610304000407001180c0c0400503102d1f03401c111801e082c0c0b4022941083e0380f4003046910481e0a100ba01e0702800c2e103c00d022030f01800700f4003054000440c0000400020410503480107001d603003080301c217101c2c40d134a503007455603400c5158a02030b01080c1441e0184c02c40c2d60b100d0f00403550060300c19041c2c90030305507105d412086004054038106000304008c61810100d503c6003400c20000c00c01490072420503000000f030368000103006051250440b041081400c1d441e2034a40450303070030f5684007066001e025 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 852656735 1250 852655485 852655513
    0x203010219030204030c05010e061204080904060909031706010e0d050c0a0602071d010b03010e0703091202030405010809060408030f0903190906020c0a0302090a2c0109030210020705060601050307030e 88
    0x58007030300041b9641c15a168000c00e09511445440c408004080c001e90314211580038808901c82c80100202c4100e4800c0003406581e84440c005e030380c02040c0450002c102d103006454003030891412651010703a150401030401c0340d10383e400f850240100f81c055841181484260800c1c6091248107444a508100ba1030000030b1030b01d5000820300c040701c00b1035120703060081d11440d803501200300078451090503820500041c00742440001c8103d401400d241000038458146540e007013400d07032944c02c816015800100301040130f560000001940b020380440a42070500d481c1c2d17a4030286010103080c2031482c8411800003410381e041003080740c4c5a84d49420f9242c2810b8040c0c0c83c001c100c202c06000e07890050082402042c1503081004e0743c042941c3d4000e1801490382c1d14161010f0040074005084805004002072b0109002454035440e80071002210010a200e0500e050191400003c06e074400c404c01d00c100030450114a01003015500260b003483e01983d02c1d154080d045000c3d1814101078402806070a5155100c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 852657985 1250 852656735 852656737
    0xd05150d02010f030e0a02190314030f030a180b04080310090504020312130e0c03010906060e032503140307120c1a04020117160206070203040e0a02030a0e0d1101050606032202030102190302 83
    0x41c1d1003085552b41c109281407603192240140b4802e114691024804200908a10740010384d00d50805060b8000b82e81554952130350f4201c0644064890341000428054a030b000c950701c107005014100028005400c1503408039a8407070000c030240160010120703200c118401006445801801440c1c043c011300d080070f0194881a40c401c0c42040349551800d030000600a00504405607041401006071010f00c1e00c9880c3d26581d00c4804030750134540628444007200141c0d8007001c030203940e4003c0c801940c1303407006851301e83c8038a8000450001800f000c10803140c0021004138081c5a0791071031102080b843c1c0c940303100682d00161014a101180070760030f0200081c4503000c00c000004e40f045507003140d180b600c3e40d00080c0e03183d20450095040044254000400400d510b40065411492060b000900f50307003407182c2141000311085802d800104070140d2540c902c442401b40307541140085942c5451810240030180300030803d10501985d100b5491140c1c0155a401e6040c6c0d112011072072040e0340c05c070383c260344000c000b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 852659235 1250 852657985 852657989
    0x1519080610030b03211614062a0c070509091c09060c0305180d0b100e13020120190b0f09061b0408030d05150d02010f030e0a0219 57
    0x226070788a80c8030461031103405a0220300001501808684800d8007050000c101e50451400c500541004120300c1c416640d2211010741d40a200b80180002901e402c0d582440302c09000b8a005046c45500703545c03c002040c540e410301a00103041c5a90392190004690300b021000d900c0158088070000c100010a4008503188020402003114014600c1c030030b100545814003d4018880000d020400840010380954024400a101c540d10f800d410240c80340001c4e040314080c00101c461049403020720440045d032441c81d001904508400c200319103400078500b0030300404c030400a0304002e4034001a41e94100e50718070350b00c4410014800d0340d4540c40c250b24a01648000d245080790030401c2e180004450300c0030807240710b0003125964050116610742c0741c0b110700e9000c84425100c110f01d408100c0003d0f501803c100810311002240c5c0046445c0c0ba00c20208010f2501c40c500941c001c084604100c1c0041c0e03809916151088800e08000403a4070424035858582142c1400080d00902401d2151240403900e00040007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 852660485 1250 852659235 852659239
    0x1e070f05010c0309050303060d03170a06030c080102030c090409230105160206100306090312060e10140117101a07110a141527100c1115190806 63
    0xc0c002d42907000300c00300c2c0d4101e07101518540040c40800c205180901c40400803e000303103042800410903218184101c13005641d82e540f540d070782c0d03142041004400c0000c44010f01105d4002c41c118544a000c0c41e9051040565441c41030395210003ea0410000200e10303814059503100058000d00d101c1c910500030201a120403070114002e214858410780300144651186030121101e4444070b00d15920b01018100d07000c011800e01996181c1401200c4070307840341c40b000780225110303404507007006202025040d050390480381c1031007143d16900e072540c2d2308a846080310f03000100c140b1150b0303070b1404428151281da54005440782c03c1c00b01106052024100d0203010058005c10105103204016000c00c14003504510500309414034000c460f4071540340410b10000c9051540304064504104d00d4075104c0160b001d10500c01c0c0a001a205c0311606007843d0a450100d4070003030500b11f20017060741d11907907001d03030700990110302c03c03080c601c00001080d01e998152000504075011420b1000c0c14154050800002214014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 852661735 1250 852660485 852660491
    0x1507050f0a0207030611040501090b07030e06180a150206150109120c030b180a030f120e011e0e0c0409140d08040b0a060b03010e060a080f0d080117121e070f0501 71
    0x501ca1103d0004440232110140c5400280034034000c0c5c0c001094216600a4040c04400044100180c0721100206040a581c1030302914180340c2004200e1b4600050b04000c3c814076607025100355040e00010480d400040b98100800d4845140d001214911125041810300703609100340b0384108051040500162485491000680d54030032004040f20886ca180800082e8031045c1e500c030210b4061050981825858604a8001040f0050f41c4081e10200c0f1400d5005039514041034404c40030090942d902158032001c188441000250000c0c0d036442e1a2655034415680c2d0aa000b040142c0c44a80d03800c0d90000b902600c250034004d040c080c002120031542550070072132840005000f00217a01c02c00060300e03034859140d03082d40d0800c003c0c0201818001c09058021a402a001c2500e210401107001140c02000080c0903440700204010328001c41a44400c4400710b1110610741d901601140000605945080c4d0540394288070b548910900c01415044401704030024400c0c00f40403002103070345000c1e80518028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 852662985 1250 852661735 852661751
    0x10305280f180305040308032a0a020c180106030e10051513060f0b1b01050c04051903020321040f06121127030c03100e1e1507050f0a02070306 63
    0x30402c00d02d400900180007880802c400d0002403280710245421040c0d0044030112040340380380e02d8240102031161445803031004500080c0481d410040403501d588140d4007200341000481280340c42881c1070081405060720340c500350781a42820403484014034510b40d0f052125040c9104500b4000d0b601a04080c000c2c0c01d100030300c0c100050315010b143c003100c074661203514a0619040c29003c40340c0210300d6021490107909025090700e81e0074000c42c1e00030314103c01038960703c1740303803400708520809800318801800594640402c090394001c24041c02c02ca0900b103103011070a83d10901c4101c284529040098041d0510b400450f8079644160318050000070001d0400c03d510201016207168000d9600d440b4001c4c4403090302c860310400f6640e091102507070140032100104201c3c40060f00780f001c0403415900841e514243d078003e502040105140e000c0a8401c1e400704566448419501d90302604802094080f154000c901024030610442c0c3d85002e01c4070301c9648450f40c00d1070080d100c005920040c0e07005801c02900d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 852664235 1250 852662985 852663011
    0xb1e030c061809010b03130303050a09020315010e0717060d06020c060a09021c110f0109050a030308150603010f030807031206030f0204110906090f0a03061d0f06040b06010305280f 79
    0xc6a01070345815038120fa5a07d581e660480290000800f0040da580c0c8034440c03c801038408202c1c0c101c48011b0108904900d604055480d00d000c103009009004004602010f01e1000c0d8003402a1600624161440592900641040c40281c03283c10703910606031040c103041016400d401e40c0700d0b201980c8201c070384d810041240304101080e4003200b103010301041c40c245641107180c5020700525031200d0060504021141c0e0304c0d0002400005541d10540c0840c2c4c81d0300400405122460750304c4040b00084a07445d04550414070341c031168031150301000f420003100150720f10626016050902c0914180501400159142c2c41c2c0304c444125151012030045091040e038580013180d5500f91010504007401443c14201c2010401148070300308015290040b403685c40100114105008251390709580c40100480c005042100d00e141078055203039294603402800030300c000188078000303050b001002464041450349680c468445642ca10701d2803640c0307545c039002c00301c00d003040b2a4201401d05e102124080085240e0040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 852665485 1250 852664235 852664237
    0xa0c024006091116030e0603010b090109080102180d030507020a03200d122106150f080103150b060d0e06070e0306040f02191806030c06030b1e030c061809010b 70
    0x3e00320345400030034818020601d03110044038005074003030305c0c010103281005d801240c0c45900a8020311100c04000803060070303030758119002d0301c01800c5050085140c0070024540001e091024203400307204050f490121020f251040c400d95071003a4004203c010700568918080400b04050311008032030182500d82060740740307400010784158581082070b440743c4041c00c0c0c1044419000b80e03900280ca0501c1e26041e1084011303e44151009000b217998000b56015001c14003a22000c403c03602c25040003800320041c400126681d501d414406905100800e443c00b401000a21500802c041760039101e1074100c0c400180c4400040c0c06000310200e03190041c4911010003031507164981145c3c00342004e40f404031002c0041c200340c070700721210a4400402942e81600c032117139801d00c0000c8016031144252a400140140404010080003c1240303003010486418000041141d01c015260b0300b100b4100301190358801c40e00e06010600c4201001441103554115800d09411090b4482503c00c1c0034060740c10000c241460130340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 852666735 1250 852665485 852665501
    0x3040909111c06180609060c020c0a1d0604020f03040f0204060b21130507150f0807020a12020102040b130e0109050402010c080702011b060f0509030a0c02400609 71
    0x421200210300141c3c03600000b8041c0943d42948400c510081d03d4086000c5101c2e4086071845600045003d440b59640245801c0b14041040e01c00d1841070000c01126403d078107950940341300c8840301601542c0708030000b002400380c00c0e40001c800c1c40c00400c2204100c0e6208914200c64800c035000c0190035211505240a401591400555903408800c5a5031200b404d001e003960000080183ca01d114010303566007805c04480341c1c40710041c2e002d4440c102c40c0103500b06009684100303503464404010b1404420081d034412802002401d82d032154040d10030111b10039011035003d444401c0030107513503104502e600001f40031148a210780e08100d01001082c80c500502402d80181d40503990028001140e0700e810106501010701203052080003205050012400d02c10981070034010b01c4000307041c841c440540d10a40f9030040024a141c5c004110315190160018900d0107000d40664501054041707446030500060400142c198804540303008078040c41c0101759410892000041081c04805d54440c402010780d9000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 852667985 1250 852666735 852666769
    0xa020f0c0622080f03040311010f1e09170703030e040504080f0c0c040903170a1b200316020312030f0c0711040f0c030e0c18060a03050304090911 64
    0x100b0480c800419020b0054142080210b03648600a40d03401c41c082c901551041121041e80000c50100180204101c2154100000382441840501042e500405440e40e1072048010300050104c14280c080c4120040b6020380380000200184040d0411001c0c4c4e162860720044000504c5011041c0c110f04050280d14007540d44124094207002483c0c6006641c1e030448100c840306445100301030002a034803400743c02c40d200e000b80c40300070050000030541800c049000b800300b507600c1c5c181016800046814405000410030610707000d03940d03041c58112000c400f4060121075940d88000b0600000c141c00c50540765503024807c0303017200c82c80200d51007442c070180800c54089401e106030500181b60062440c00900d4401c0c0305008105880500c90300003400c881950101411055460620f260700d10f405110303030107101610b2001030440c510103000258503000c0b107402844901c9030143c0410025110f0f0002400071b50750080075030f40c56903150135203a801007040240640d00c503402014003220340d0400c04200000f280304 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 852669235 1250 852667985 852667987
    0x10e0d05070b0727030615080a031e170f090f0601150f0c0506101406040803070f0c08070b070606050604180b01141c060503010b03060109110403170a020f0c06 70
    0x69410a0714540c203d848642002c01845220280030300142c00404003075441110001061018228a047d803449140c114010544c8116500400700b40c0102c0080d041c0024940d100024008290045900c5481d1000106a50320352809102051001090161140d45560210f40384000101c4000c0e03030b141b50a10900c81002c0a01c82140e42252248016411001d21420403540d081019600c0d61b1030001c04480f070807000f040b080750034003090300c44684801640d01c0440e00e02d0300b094240940c16440c0d101c0c00304014801d44164422f402000048810800140500030035140a1640e5402c00344c041d512a01080303405515226021805140800c281c40079900002034030108210241c00391030040c400c40311f002d81444007031480c101028000f000205101c40300000a4a0440000a09002070b24001e41040b44030740d040810b010030715100003884c14111000e00c14040b07070142c0018040070345440703145c00c0904140c070840751100b079000b501c90040030b101e100c0d6801c58440b1015420764a480759201c8828a6000c20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 852670485 1250 852669235 852669241
    0x120905030301091b1713120c12090f091d010c080712051b031b18030105090703080334051809061012020c0706020f060c03040807020d0f0b09010e0d05070b 68
    0x92140c174a0340700004080c05103800400e601da180700083c1860740403001a00a4100f842001a03200a26003d050641442100c46041041c2d1441c1040f09010320340202d50340e50000b0451000000002081e0415030008110060381043c000300311b0714044400c1c42c0401c01c001c15408807000e841c480c01d40b00c1c1d40f1a0300024512400000a0001c03680050001011080700c105508000400a0028018100c0707030589110844002c10a06003968001070020b8242c0e0480c2d08100045503507042100d40c00340841221009001803081189880465402c0c10303420300070419001e0400a8003d8024200308a401c0300c0600304208e4030040243c0213004403519500444a40750200015004140c8041c6000e504180075017482883c100203441c1c04a1a03100e10700607070140e8812004ea0005011460f00300c654110200d185161644400081e4403c0e01e2009004140e10a070000610015154940d0555032010030102141001d0500714041c0404c0c1d0808049805645d80c02c030b20260040081381c010942c0070a1152140d6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 852671735 1250 852670485 852670517
    0xb100b0306040b030a02181e15010c0c0f2927040e030c06070809030316080a020403080313060b0f0307090e0c0d0302010204060201060f0513050601120905030301091b 73
    0x800050202c64161285e08110700041c0d569180c800380c01075150054440c07901e003002da00c180000902040180094014040c0406004503900d1000000f60a00b01900303800c040389030000c2c0780c2009a220914900880101041d00c103c2190b0f11081042c0f0721a81d031407900c51400881c20a031152607444070200401c500c59001415010900c80c0040704014070015004800220050540e400501c250341180c00c11000c0050280e00803030125081442c0700000d43c11464100c0740e54140700601c045100500180d0700014813000c20315012540515400101e0603121b00b003a10000c40364180003070b03084601c02d040010b000d02074181010700c280480c90040003401c010b031425881c2d1000308445440c003403030703801013100c00d0700c0a07180d00402c9030482d4070a0b4001681c031440d01c1c0c00282110350346d40201c200e13003081c0c0008101d1595001c00b1209038400003240003409481d00b000588100c41d0036400c5c4400507041454041c24004040041c6041303503c1d03185c05000a0390210000d600c103801c2d4034101e0000c919041403c880c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 852672985 1250 852671735 852671741
    0x5120309100b1e0307150302190f0c0305031005060a0507020111011a13020d0c020a03030b031c030507200c1311070b0702010908040e01032609060703030603140a0b100b030604 77
    0x200c0c0190030b584000f9203d850740c0305003004a07105c03680400e0700020307500c04195000108411401160ad4004004103505100800f0030300407213006401c000c5c003c00414a0803900041c03880042c2802000740b17603613040c1820080d0281e00099826808944032040c4041d4051041c01810148403c842100e040d40015404024005030341110410034103500f40140040404548141694050141c00074081ca00403840e00800f80ea100c0c0394005d00030f030890181d02d90a01d01d409e456039513034030030b500700455142d96070740040341c900400c80080070740c005400040d400703614004942d0805d0141e058500c0d07103400340304042a0044c0c90a02c488030780440800c00c1003c01041c002101d240c0c12008030701c00442c010300d884d224210650001e0b08294611400e001c010410444102d10740300c42d01c44204285640c9445600b07105070355000c0c1c148054000d50b000a0880c04043c803a5000e000a10783c001c19010f0f181c41c102d080d0356680ca0303001c2000c4074100300c010080b071001c510404a22080f1507030b607402d0515543d1102c0c20f101c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 852674235 1250 852672985 852673039
    0x121f182d1a1e030616080601030504290106020c2403222d020a17070902030a0f061205060601050d0e030d0b10030b0a051c05120309100b 60
    0x1c480c0c542510850941e5a42c0350324041008041a80810686450700301410890090f201c4115002c210b0021040550081c81040c0d20180900300003c05542e03d003403008860200900881c440d0404842d840b05940c0a2104c09046e22410744c200d44160780040b0911448030501134a200c5004002141010052284001958050781c0c0e42403003279940b03500c5030304040030089130001200c41d4040ca104101003402e4102c04100c0d001c04459081407802020740103c0c0e418845400740c2402c680980080700000c1d082000b140b4010035500c45c085540f85492540d60000300070a40349545c605007170020000d0600040541c40700c0c6a600702c0003501c41912208015103c07035200f820803c804644580360550440c0050000d09481c445000c00031500b02030410800000c84c00071000318050600e809104c55040e15100100d00a4600c1500e110003103503e99071161060441580004269202c0d02a45510704041080034500402c14041100e1790071490104040c00d840c007100c00107405c00b500344800c03450318000c4102c0510b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 852675485 1250 852674235 852674261
    0xa061b0c05150403120c15201305040c050403080307121b02010f0c050c1b030c0d120e04020f09040b0a0312030209010e0a0308121f182d 60
    0x100c69592040860300c00d076191410b0401440010408005110142089030701e03203491803914484440031071351100e1035103216039018248641d44d210107085065404940808044000606607120000c9900c02400344446015032406141040a0110303403a01a0060785c00b07980e400000e8908554030b2141c1203800026507807402568070b031201e00c2c100901703c00001c01724000b4610760001c560007400c5180001074072104000c1070100501007254035502540851418042c41e10101d500ca8010300c0580040d00d45811302c41400c4c1c4c40510b02c40d01e58100250305180740c00304251a2140c0585c22001c004020481c050701c00b02855200d010480c1c5000c0f4a82a03000313484001c00101200031154503500c0b003c00c2401440c6480010a83c0010700c2881580c10528110a0850803244c2d60100c6045683c2c07000280240c841c1054030780c0041c0042081ca441d080d203007150a02640307203004142959405902c568031a025407402a0903c2c2600a05a40825582d94001000e180f40303203501446e0900c000900800840b0b402c0f00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 852676735 1250 852675485 852675503
    0x60501140a02011506080915010302060904020c03040302090c130e0f01030b04150f0218030a020a030b1803181002030c06070f020114100504151a18040e060f060a061b 73
    0x440401441300300b101405441d43c0f001d040e4501201d0340c600d8162400511002c020120380100300607501d0400b00c6103103c03030595015881d052080802c51a42c051504000d50260013002003041401080e00544110461840c10b42c504568030100309008540c10748403031110841000043c00484d118883c0940c001c2c0c41003541c11b540c208101d80907001c035082101d00350f1046400160398440070381c000c824140c146d40d003140500190192039002810750422840001c018800728400140368038031a460750b035034045044007074999032003085035816259800f110989100d40075414150102510010944241500c003000174030543d2500c007015643e8081226440c400c541d200c0384401200c2c0300c1d90748a80d02605542c080e04c00824104401c000c00d42d003c0058500088440b194100030f92a507414004100703210215181e56550203071950001084900a5000c1d006414210688ca451100044140c0b00e01541070054145840350403c101c0c0c1071000303106143c00200d2400707108848800701e84072800964403820704d80b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 852677985 1250 852676735 852676751
    0x91506070201140712110d0207140d08071208010b0f0912030d021605070501050708040b07030516082113030806040204030c0b0c060a0b061801020f01051f09060501140a0201 76
    0x303035071076804414101c2e0000042000241d04a03007002480080203003906c09801024910400203507602158441c9803010005010601c0103526071420b00740086400101e429a201c9142c01c1190503803180004000004912400004640c0e0011084e5804900f1030041c05152080d254100040d1003003040200b42c0034081008562250f41846c4003e149012603106541152002800e0040c2080344070b910540c144481009494005041142107900b5140401015500c3d0240c03030a040b2054042c0305000c03400c854103001c0310360610880001030019181130709170320140c517001217000700f03007a0900707860300d107440c107100020311000031b000e148165885403005d4001070070503070341c2d032240e0341c0c1030b05242c1c00108480c00003e1002c03462b1f034090010540c80000404c0910820a04401180c020300c0348071541030884130030310301e02040e5a00c240101c1c9881c56401000340640c2c03c0c0341342204c1d00401c040c000d01502d10340303e1200054980b134030f014103000c0b107905841d91481c004940c45414480c0e031002541d03804555070b130014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 852679235 1250 852677985 852678017
    0x905040501080c011b1e080403020a0e0117070b0a1407052b020105091507120f060f0f0e01210b0f0f0601030b0a090e0c03100c0e091506070201 63
    0x3a0500034000b800040410000141c0050100320044020101e5216552135a1001c18000440000e60f2a9004c6441c0030101280c18041032a00a5800c000c0d0320054900e8001a6043d80c410a139058135807541c03000c0050001d03444000e075204c000380b00740501924144401e1060310b01421130300d01c0d0074501e40742c52031612405945403418403003000311070351105800da4400700307000d02e10303107800418001c45000030401824240b010035510f600030090140101d01080c005601c00d03119452281d9001c0e602d1000344240b10003034801101420b80d5001e1403c01e1250300500113800f1240d00d0141d41120480000f06107942d0030904000c0d2000707031142c100071414100c204e107040003500045c1d005201381070180c1040c1c0c19041c03042c006000d0100c060441e41c105424003c000865503201281181240e00d401300000728184442c142600b80501c1001c07640c2d06000d652000c842a44260308112003084c4640d5401c00240848000c100d8900403e0717030440400c05c04100988040d082400080c25120300505102ca00001d540217 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 852680485 1250 852679235 852679241
    0x10051009060801020a181d151324030b160e1201060612110912010b040e0c031c0219020406050a17010608010543051207030501050607030e01090504 65
    0x1008226a039070014100044a600c010090000944810707043c1101d4034259510942d44000c000b001c440a10301b2000c14202023050000140700000a003d0707251003041c0018090050008003800004181e80c208018080140380c800a001e4941c4011002c05c1911101c4a0800c0c0d032208a0000050054000e541c2e8080d5660030303485140c032501d5100126a030390034200d0003046489060060101700d400e001242d540c60300d0010a0782c174141c0342510480408821044030b1809041103000c00b54125282a2120744040d40c0815405081c241c00d0b41102c0560314a118820415104011000016000708403241442c11124121020581c001000032800f90b880b20700064114000d5440b4444401c20200309840d150f030280a420001c0540000030845480c041450222144120080080d0007003030710403615007084006408003690650006400e10081c0002d4080c200303a00006130403501c64075940015107141c0c4240541c5041e03c0e000b4140c2030401240e40e405850a40000d1030040c140000300001048948680c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 852681735 1250 852680485 852680489
    0x20d0f1b050a23120702040902010e150720030604023718092a09021206011209120f0e0d05030a030c0e06040506090a030b07030c0e030a0201021005100906 68
    0x1c00c007100410800483e8004400c1c03c00c2c04007440d0001c0700065858103100d0151400301e034042d030300401c07800380741e20040355a04200003449900ca2040c0c200141d07800081d2014148103841419181e800c1c0141c540002c15040301013080c2d0364598881c100140060800007a440c1d801c11489005021880b42c5010b4980341030000b0188902485803000d0421507000b005d02d44000045200804012401d280e840c0c440d031401c4452584242401c010441825418100d0110380080892000440d141c1c1424800c43c0d4001205030b601d140024039030b0816100c600c8061040c01311165001400070202950080300b1740305585210100703400d00154950304100c0c0d8640c0250384003280d208401a5594100369900a01200d103000100810804502c00302c000e280c0741c1400f22020f48504a800d0346e00c408890000841e03a03001c42d00028070a05160040c0140d40b60183c0010307070422203030b454401040560100b450f584c1d030001c0c1d2002c0d0050f805061901c184010b5544140e420400b441c14000480e911503170300100b1b440c126 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 852682985 1250 852681735 852681743
    0x2030d0501350616020f120301050a0e0c0304060b0f09070f12060807030f02040e0d080103050c0402031905090c030a0c08100b180601020c0d0b0f0106020d0f1b050a 72
    0x111418145110314410481c1100040000031000305510b10b9182d038840c80140101000e4800015124105000f004071a8042d440107013100c121103506420401c1d01d800c00e200b254040d445251000c201c90441010191107240380b02051415a500da80700c0d9800f070140c030b06585401c49050041d12219031602c40e0b0092140b0341685542d1140600c6140040c1203402041d091a840751401000344511040401c1c120122600040070b050703045590f000003801030200362a40d100e5445071012690b4083d800c002c000b412a4040e1090350080e1081c2c400780800e0740b0080b1142d0181040b82404c1178035a0382e0340d80c8001d41007050402110740c039038214030110b85011401c3e8003d40c1da00c44130400c20444103d0401c8005140c0007280d01c1800074070040e60200b01e020362002c603400b0300c8582420000b0075a900c2044424408000284608400c070081d003800c1c41c102d038050300c100031900e4030400045005400050388a91040803566280b05801d403444044800580100070720074144c0c6d5030349203000800c00421181241c0360003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 852684235 1250 852682985 852683009
    0x2030a0f11090a0219092d08060115170c1c060515092106060d03140409020d0c1d060706060305010e010e061501140f1303052107050d0c0302030d0501 66
    0x100b0130001548a5200445010890740342c5047c4030154000c100003c00d41440d545120720b104445008240d02801074000c222188100000002c2101a001961b24603040380c1e180d08541c1127990803000c8a0900031a0030181c80b1204100d1003001a14640c24034001c80120300002401c50f4444000038182c0941018100000101003030701146031400e4094005400030503504515400715001c1c41644030b5200400580c4260400c031800024503006030201d08154216000f8150f40d5a181c1402c2e0303000b50000e43c185000b030f600c0c104480c005603000b4501c8040b500c100700b40341100d0030140d10801c012076000c0102201c1458031500000300241c000d01a8500480000300080b40281c00482c0b070921f03241c80109101486d10b0f809007a03c08598009101581800c254440580d5900360b03074518003c54483e0f9040c844401050420010038880c3c04910090648400a003005002c40c0a8503000c20034020304102418035002001e29002003801208241c0059103e030040d83d0501103d950ba800403610264410310056503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 852685485 1250 852684235 852684247
    0x50912060613090c090c0507060c0804060518121e070f05011803080f060f1804140106031502070c0f09060f05090702031b03040f030c1403030702030a0f11090a02 71
    0x90080c00c00c2c0141c0d000c8002c00c0184000c561115041403100d40b040c0071541e542c410600c0c0025220750202c0303210b2600502d0034401c6151841008103c01001c031803d5580700c0c0703080007007003070380442141d00e4108240c110003c1429080c0c814040106a202641060070000d024002d24408079061014114550003040441040c2c0041d05001d400d58003c065100004506d200c0c0c150002500303d40d2041d00703c40b0248501c0c000383d881401281d203000c0c10500d41607200d05420856100310014001240c42a44200c44180c0305610a00004c0d081ea90180801041700307081c1030500304000403542c05401c10b940615200c2c664541c3e80c0b06082d00804d41600306103102c07a00d401c0c1c00d00000740c0e10100c0100034502544c162044d0318001c0e100948038041c0303640481c10000c030142c01c3c90000f4070400617200644454207961204239501d01d0003143c80380d80d5229040705003103136028641c81ea25022098a002d180c010780035050b100c659540d50100221110800c03985035100403044803003070311a038032014892440c115005aaa031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 852686735 1250 852685485 852685489
    0x8040f02370513050c03071d041d16060f050d0f02030405030a030e060615070c03080a0906030e03090121020d1508010f0b030d0f05270a08011401060f0509120606 71
    0xd4a030203d82c1586400c0c4418031540c0741e040400c90b0380c080883c3ca000c80b00311003400e2550141d07110350040b01d60b1050406c642600e012412900c20903140c00341c00200d0704500300d82c020394100c4401d90701c41c1c00701044046c1c1c00e844005019800400341e550001d04005514103203148900c0403130304141c0d02a2803540c0013141f81e40c0486d400d441014140c2c000741c0024012454030078001401c402101003540100c180124a250800c09402c90680107941d003ca202911012107600040c00d4088a100d0840000d023401c030301d0410400f02104403a03014206943c0e90f0980c00c5140b140d04e00095080c040507404540c20030000503100018424031590035803a4036100b14a5141c00b04403405d6509102030343c80500d01d406141070440d90006484805081107003420300341ea00300b150341a1038501410304207040c401220124680c00c0c650482c588416004100d40c4100001c1d1079050f424222660310307200c01a07040703040d001449040e000d581032281c150b055240c400d10b080c400b900840d01c68511600c485074181d00503003d0003014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 852687985 1250 852686735 852686749
    0x6151e030a14101506031a040f0509010b0a0302030307080c070b0403050706080f1e07030605040501080102041d0903090f060720090a0e0a26030106050c0d08040f023705 74
    0xc00d81c19800d00c490304c8070040380c0c130540341d0038860300060580d21821030203001d41044103d4070b5244001d02c10000f1752400042c0001410084a581d00d181d403800c20008604d00d860f107692070560b80c015004604284040d40c0b1036000d68059603241c02c940c80b42c801c0001d00c08465000030000341d441240900700e428a05480900720600191040c6079601400040000d1202100110040b0980006040e2620307240c0d10001c2d00181103c1c0c01868005081100200c0c0d5401d0540051003141e05141c81744901e01490106885007400c165006410364004220302d520919045000c986c0148000b030003146084100d99500711894460201003503c0e440a0741e15445030701d040807000354000002c40303003400700c1081c1c4442d0540701c07401c205004058031902c060070300007805266200f180030f14461501d203a0740c1d42c44039030282c1580c2003403541742ca0a11130b150f1002d180e14400d00341c1c03d02072503000403106078810a50342040081c50181c04450b4200c2c038285402d8000c44070700440542d12003c60200c0e0030040e4140410300c0a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 852689235 1250 852687985 852688003
    0xd050712080105300f0115060309080f03151003140105030705062d04030803011a18010806030f010203010924030b0112050c0a0e0105040e06151e030a14 67
    0x240300303550703004110030b403035244d1100d04c000302404c040080460100d03550540e14154001c2c4400c548624010300881d9001548215180f500351001380407803564600045007924500c08005100c03c5050005a5207a595103025540045c034480d8003210b030b00101c1c0089020700320549110000252120101c154000314901614050b01050300a0300170281042c02061a1b0b1041408600302c81d20b041c1e940d4035280b000106840b0041b4804200030b9501d0791b583c2400d4010b900280107402d0b040100541c00039444105c0b2040312031085420a980c00380c3c0107000e0064881c1034000b00b03904c0c0c040c01101002c5140a000f80700030350280088260021712405100b9125980480c00c40d204182d207400c0910902c08241c03090032240c1102c900800c00c0f28003034a0342c64014204424a400c554000300620408030326069201d5006044e50010303a810040201048801a5140b00503140d14000c088801c1c054001070a00d1080d032203c070f0071030b07601d00c2491800c041d0109103080034000c3c09a0302000c030480d803245096414044881 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 852690485 1250 852689235 852689237
    0xd1101091509060b0906010e0f041104030302030307090602160e0c1318060801021c0902031203010f0e09150c2d120f242b0302070b120415020c0d050712 67
    0x1703892030003170300107440b14903070028142c070170440b5203850390704c1d80c0e20344d00711801c0c101c211040f280d19240d1b6854069030300d030000d1381c481c40441e5440101140403480000c842d103200a1030000c0d4180b1500e081c0410800d950060040c000382c41e002c02095840720340b1494030500600c15104c05d80e51780305001559404442d8903800414590740100950034005234514003c0c401c0000c100380025241016100280c940740903c81c0000f01320300044000101740820400344011120b003040b2a1100c0e9403091310a9480ea095100e40e0181d00c110800030803410641c000c00380007070501c105e082030002802403d00c81403d03e81085080c84c06000020025070007820707400c1c42500107001c0c030040b020508007500c1c44001e880a82102e420000708155031302009641d8101c010b541c4d80910500ca5012103005035100d03154a114003030540c0980314010f0300062001010f803c8031846c000002004c000d84d212030343d458030346100302c8804d520300c10b80a01100c1c03405102071103042c13070103000c0b43c6845940341c2081c0751000b02ca0450340000c02c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 852691735 1250 852690485 852690499
    0x13020d0c0f08061c0b0c09100c0618031706060915070606050103180303020d140f04030f110d111216060b061c0506041b0905120705030d1101091509060b 67
    0x210400b030300900303244c082d5030300c07000140040e1780342c2c9131201613401143d007480e6000c500e40b00f15483d01c64210350b43c082224050712041c480c0705103695818141c40f010320380c0100060a541c50102c140403034020285c1d080880280b0b80ca2504000400040441e031546200c0e442ea8080000e88000304030382c40c4503c6006003801c3c242440000040f2141411103001d1050107010f154000a8409002e0400d9000d52888030340d1701c1d041404c6041505010401d0340044400b100450408003000d540d447c0211111040c0c400c031000180410814640c4c1210382800a4912000310301c0341300321a42c41c0c1200440902460081c8002510103414a030402505603002030340e2035401120708008420b109414000d1900801c500004003180b43e03250200810300403e000803610070400d0fa04403580b21000e60180c51442112401c5404000f40020058141d45030303400c521881f54907604c200303102414540a0260701302440d107110700000d0307401c0c61a228003450300000c914164a1650781c06180b810090303070780b042c88220f0b0f1040c0da4172 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 852692985 1250 852691735 852691759
    0x609060b0405130204031e260313030507080705060720070b0f07050a030509030d030608070e07050f0c0706140313021c02120a03091e030213020d0c0f0806 68
    0x40c16503114074000c041c091100040c0301c0d01c00d00c0c0c041d0100d03801180d109140c01604c0000c08410382c1803c01c0582d0449122100c2006429003035880304204904202a0380520701d1921441c0c1c10203240312440104406104d01401700402180c4200003401d039040c000d4010f40000c1c9440c04004040326481d0000b20b0748800103c0c042c0000e0840020003c0903150209040d07a500e001c8001700700482e010350803000780320380700340c5400c40d04056200c0041d0404081c190100d482c1192402e81c260199032084c01240740952200c0b8082001d20390041d2007540050050034080c1c81d0960706407402036183d004c5004900e042d40b040c0300030003400e94000ca4400e502c1030b48509140c298105141c04607411200c061005c0d100ba4641d03800d08000e01b018100c141e1405900030409060b001071070304140d480d07501c014001d402081d62000d000440740c04260b4030075060039500400180840c290340c200800407403d40085040b165081c03080da4205141803092604640c800d40355800801035400d40140603882c020844d500038004507e036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 852694235 1250 852692985 852692999
    0x9020c1e070b030c0a0e060703030b1003021602040207020d1218331209050604021206010302222007020406060f0f03181e0510140601081519060201060906 68
    0x3030b04d810119909000780d4171040c04100315106603030311060507444400050801d04064150307002200d40354040d1000e0364100c00f83c80701a4228001d07009186695500d04100c003005151030750040003400e100800e203040030546038845140221034100d1a502007a49a22000314544410f82c00b4002091480d01e2f0542d448030b844915150445240d00443c10007004c21001000c55000d1240c00903d024646810440000a810920390b5080140c5d820f031700810140c3c40c00346442c440070440d10b041e2500680400d01e8141001d090343d44100760707881c1c4040b0403a543d0884c440840070784128600d010042040d240c0e01c4003454010482180d02692000f014060381d2411802c003103422584075403404009080004aa100304c240c1c8060000f514035008114019021001c0000342020320030303141140c001c3d0200c480d0039080c00d55450072214581d12040c4e6200c8560300060666100d102003641c444031f5031490804060202020074111020004071405641036140240030b01542407260788018042074034207118031440e040c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 852695485 1250 852694235 852694237
    0x15150206130f2004150504050604181e06050403091d040b060105160c060810060c0f0602031e0705031e06062d0a02070509010b03071d0a09020c1e070b 66
    0x1a0043c1444035072888490302035910304140d400020050414400251207100c482002c14150180d03601c21460030b004a00b881c1454462a10440700c08804030f90f62250b1601c0da405280300d4030300e80b20401c09540680900040d5035001e11806076120340c45070304045003030100d14001e41c1d1005201c0340c140440b8100708404a001466141c0d08804207007416541e4001c441d44002d060091102c2c00fa01c4d4002c045400500682e00c035154510a00341d103000d0480782500c9000480c0c03056400e05016001410006d12203011541586c001c64112600160413680307180c903d00303081d0b18a241150004017040c40801000742010301040703254178400b00413450052515100b40055840d010b40c81d062458504214032020000c0c190079081c1c80240700d40d4503100c0c0c03a201c2c0d01070025610385007409241e0058020800010700e03000320030190382c02030f0510340300c0306260700843c521010401c2c45442440c1d0f2002c54400d0000342c8400070300c014010420318030094113400701003512580d0030400c281c40c96a02640318035020407000307804c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 852696735 1250 852695485 852695513
    0x60108060a03140a0206071208090f0c010e310e01140f0402011808062403030307120b060403030e0405070c02030d0f030b10080a1d0a02131515020613 66
    0x258a400f18895046009840e110070104000d402c50400141e403014424640301c0c442190344e00d07503140703121681d54001794bd0f220000300726041a69407114500b44003942c00703061220820040039284800410289000517820003074840d54003100d00405010405209042c020442d100d00218000d10416601159107001d1003401800f2082500403500802d085a100345004d440400c103840800c00c805450f507010a0300ca0030160f810441c601005a1451844da00344040203d0000000703001d18103507900d192003036a48880c1e845a001a0340c0d81e41c1030711001c0d07985c0e26000d0009103000c1c1d40c4102d074401015080c402115800b40192040c0207902411400590707001484985410951410b4000700c0c202031410b4003d00384142209500c03102a081c2ea042c4180d2029810f48281c3c40340c0004e2047c03c0c01c0c40d50090040715180c8105843d07801c03a05015026040c5071031034248003942d8100010b50700c8054440512006403542080e01d5000c030000c00010b07220360400c000c607000300b090454407140307444543d10306070b40321302a03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 852697841 1106 852696735 852696743
    0x24050c030f07030504170304050f010e1608030304050a1b090207030507120f09050d170c07080d050301061e020f010f0b190e0c1b0708060a05060108060a03 68
    0xa0043e580155004030340d405840b06d04140c00c03101548010702c01d680c548201c2c0e443d400c243ca024881d04010900d410003400256401c4102d802c01c5407101da0000e02c0c954000d205201c0403030804194800e0a5a20040d00709104c1c90701e42d1001d100c55400e6001001413840812102d0a046e0402e00501c0c46031b20038210200207840d0404150b400c1c00411896000180c0c02060602150400200c1001005e0103003016402c030b032120b20803a070b030503030700400140030181c100c144208402b050412041c0f01c3d01d5214200079007150304018004180807410142d036940c0503e1a0820382500f4000d01418203003595a9000f4411018007c0b0b402c009009880845030060044407a101d65142c01982100305075020007042184503100c0d00d5040380315400405410303020041070b518940305c0c040100600d000508241002d0051460541c68000856200910040c1401344002c10032806680b0440c0d110f055a80c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 852517985 852697841 := by
  have h0 := BRFrame.cov_init 852517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 852517985 ≤ n) (h2 : n < 852697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
