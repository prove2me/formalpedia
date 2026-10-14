-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1424
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:55:10.419892+00:00
-- url     : https://prove2.me/submissions/2db0ea39-5b73-42ca-b5ca-fa57277acdfa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 255935251 ≤ n < 256115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 255936501 1250 255935251 255935291
    0xb2805040c020105091c1706120f0609150108250902131701020309060a050604090512091008070c06090602090603070906080603070e0a05060301020909070c0201090608010b031603 79
    0x81c82d00003107414988404418181400007500c030310304041c10145031000d02c0d40b260707002c00506019552401d2036110280090100440e48520304e22510901d10130000342d103400314401d80250a10000c48030018019160f41e070420400340a03880c8160700003081d850b180c20154880c070f002c0804072000d44100d50b40310003821060343d00c148140c1d404801410001c0140804018010410740c0d142c8000b14150b040c84074031991541c102800074140705031590003041c4103640741d0740701045150740802100d4072100402d017401c40b1500034804485c45114581c216000d440d001c0d202c81885064166588070611407560341e424003d160011094441d20350034002f12120317403242030045004d81000d407941500c035890301700c004204160050a0b01e0182d04410300c100041e14094850540003c110721011900d81c0e80c1c02d010a00a0050140040e8440d241005000c1601e8010b201d00d2291030007a84c50501481c0c54680940d40540700303204004c094182040010344a103030340204001107260a02d80840c0d0150302c4031502c41406 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 255937751 1250 255936501 255936521
    0xc1406010609050a080d0c020604050414010e1005030a1416060e0a140a1725180b0607060504021f031515090501050309030913020309060a0b280504 65
    0x588500014411290003800d40001031400f100d4684000e8148004280c0300c0351013030328403800d024451002000315134407101614094400038004005801c1d528200d0800711303000b0320500001c4940d070b0000c81d045405588440080c0da2010300100440205170340c910071920b0016082c0a0607003e03d0b4140034082c0d0005001900400340360b694220548040d10820501c4001a0b005600d5050781030b202d410262148110b08044034118000ca1414203018540e050800c5006070b2010348100034802001512200d440d099810b80700600024080d140d9404a13102c04c03122700d00000c0382e01000c18007240002400641100364401d101507c0e40486140c2c0006524103881401d42c100086500e4001c00309100030794103241001480309230403440d09038142c1000030746011600e00403d4104180000041d54a050800880d034030740001400e0810b100f01c3c85840301d4000d405c10f4070340d03080d10b000d000c0200e220a4030900840c842d29100601e070070703000c10700c0174010210001c90303015042d0703070030003600c00010540e4551284281c08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 255939001 1250 255937751 255937753
    0x11040f030b2d04050c0f0f010e030304030c06111b0603010306020c0c09040b0a140c0304020907020f0304030f06061413020306030f03070f02030c100804061d031902070b1606020a0c14 80
    0x24103281c58024141120403802d28001c490255411003143c0d02d51f0009004001300382002140d907442c4c0030209055224642019240c80c8240c20000b1310076078050340c201d1810f90800d0654100c2d40d0035a0800b042d1507807118829512050500060001c00d6030381c1e0080007501341c2d150407510041010000b04045000c00c44d002d03106516440c0403c0000c11840c0248401d00b546501c1c00000351620301038440c000c0c08060800307801000200d00080865000700040304d40b190180c0d0883c0d07222552440c0216a2340c0400d80304844007814008000343c04003545811440f0b0000080102c0d0b24040c0039042d590080d0401045543d2610481800b42d112000a2004010b01030040a500d0b002c401140141480d0900d06415035008070701c1d00c584c2101080d4000034154201b076101c1d03030200e8a030b0340e41001007100500f2100101e900b400000f810311000540071282c201e50065035000d0361851551071440707030164020100c51043c07007140d81c080d0100103a003503030040c11511000c0c100805d024010f91038078541b0072036000a05901e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 255940251 1250 255939001 255939091
    0x7031b17010b07020105180d020319030201110306010c020d020f1003020d0c090305300a02030a0908061b130b1207030609111602010207091104060311040f030b 70
    0x604106401800340c205626080c2c6405580d60000381b05104e800c68092017510196030a031181d649400511050980050490307000c4084004000703211085800202d000d98030788040d4041ca0000300003500e00c2410705840e0210812116002c0c010f08800800c0b080760b01ca1810b48a02074550f45202c03010a035440e040da0300685500d141a960000c40b03403a15400000d015070070004000180b030018084030b6130300764034194280e0008526040e00a00c92002658a0510746c04546100080d82c0000030b00071a040715910810342d29611806103464400c01d40d00008012890b10f00c0905101e640030090156034170302083e5a05880d0360ba00d0707060090b0000c0040c00c81b814100010b00c12419414040d0401600d40c0c08c4d02040b58a02c2d1400c0c480f5944a0040c3c1840a41c0c2c14820402c02c0d0380c000c1c0300820003030521500901501c02d10744020f00296015002d0740300428680391150b8200c24900040e03a054950a44950601c2070541e2508400b505004200c1e55022400d000b07105283e101c02286031540754403000c8800c0f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 255941501 1250 255940251 255940277
    0x11e0c15060302120102070f1b05060f2101060905060f04080601030503070201022103010e0441030c070902160510090b061815010e03060103050a020928020307031b 72
    0x124010341840b00c04c03460780c01030028030302007002c01d10302d4819150700040d1b8020109490305002070302031442d031141e0382c081c030003003111182e01c5c004400800858001d0200b00c41086050480365031003040c20b0290b000000c131075040a02072810b100e001450200d00c84501c143c18030b035480070103519101090704121070390340000c2030440031135804100801185042610b00703030303d0044074101009640014030a684020402034049020300080304052041d0200346400440c14262004c50402602c90a080c010741c043c08000440c51410004000e076000c56410b04040c1503030038a090721600c06500400211440b154500d0380702000501c0800c2040001b02d242140400d048100341000b024216008202600680e4511b45c856580e58004018035440500303030040c61030303850702c080040390b1402c031070719000d41c240c400c80e03001005110001072072400031031084404400d143c0d9000140740d205c203823807080f0070702e502ea40c00442c1c1105040341c3c01866000c8040c4c0703000102e000e64001007852a006012412020503981030100b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 255942751 1250 255941501 255941509
    0x30204060f03060e0f0d0f0504090f0501031209030f020904111906030c03110d0c020111070b0405190f030e03150c0a140f07060914030f0301150c02011e0c15060302 72
    0x22884c10b030302001500d81c0b0151a501d4541340c13a152404a820443c0c80c0d0003d0003030a02400c25038001d040d811100b00900010460303010700504c3c0a00040e190652003880086945105285030703025203502111022404031103a0031310003402c0c0c010304116180c1d02c440c681d16126840b1aa080c6004420550315086a685000006001c6038003003200203082601300500d000800641c8402c4426522111000003494216204101d004002d030120004012800080440c20301c10720300420b5016601920640703001408042921807440b442c010004d2000c0c0c0c245040c20701103800780881c601484c002030306882c00d84a50060804420000712a20203e0400100e0100c00c1554803042040b101c0030002c050038a024460703410302c0c20b24055031200400068803580c8030801c11001d0f00400b12640c000200703c0303455001c890301d010207076002400b031080c4c026114100401003520072004d00124a4060310b0f1440408c0600202214440c01c3d20f46403814084d102880350002100e80e901c030941224140c2e80061020700b03510400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 255944001 1250 255942751 255942761
    0x402030f0105072111120a0e0304090c090f050d021c0f03030e010b0307240905040f0902010f08010e0c0c160816090203010815061504030809091f0501050f04030204060f0306 76
    0x2051130103190080c0803201e001c044040b584811409030b0207000710754454240d07601030603090f110704605000104002441c144190081c1004c2092a1100698162160022031180b00d45100d8240d005421712201801741c00d01110300085d5032070030048080d4100c05a01d4641752001d43c110104c000990b200c000b4807490000b0704c6201d05403802280584507652906448c15405004032040042d0810a400201e085a0141511000a000203042400014148000c802c003c00a2a0050340400c2c180300a942e8000e00c152407440c10707a0741c0411480d0003500c0b48a2000000e03009449030380198410802c002c1e020004400d8183c0080c07403100010160400310000c0c032141c1d130140d070744125035184c01070005201c200d4002c210002c0221141d14182503590b0382000082c06000110000c3c00d02c01000240072007405003c030f00400f13a540c002d80b10341c080d80d141c02c80c2d8540504a4000d854002d808005400d01c4550f114400803ea4000700000c3c184c10280c80c0d8000808a85c1035505c0707101400c003500d00400c20000e40d4017035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 255945251 1250 255944001 255944057
    0xb0f09040e0606030c1020070f15050403080a0e0409140f120910200601050306070e09060405101a0c06090309090408090a1508070207080c0f04050402030f010507 71
    0x6040e05003000300102e0340d10881e80d01c0171486182c80d03d03910740c3d0651160b804080301e041c501c02c0c3c13000c044040d01c2c0c10b01e846413000d008414101c1c0d1030301800300341410880c2105040a81650346c0c03038681407440d00c50300c400d42c0100c2401001c000c02c586a4420940e164050322a50a00401e1102105804c07050f29500c1c00d410011160040c0d0840507a040c0340421640c29103480345819182d014540c15030030303000c0350380d0064902108140d450350480c0c80408000060414140c0b4802e07021505107031680c5405942c80000c01e4110f036404104074000400500300b980069820288003030302e0341080c603221119403144c0d0b88540103480181e070000c26030099404040154682105a82d009940340000280101c3c2c44000000d10141400c04001a60080c5856280c00000240302d15070907402d50041089000300500030031b650000040c4541a0041010003010910b0a0312080040030000c1498854040c400689401002030f6858004d005511002c0b400a0003130510a030100c1d03456103640c00951a05944080c62585 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 255946501 1250 255945251 255945253
    0x4051c1b020f040207120c03090509190c02010e01021803070506280512070e03100c091a07140601170a02010206070813050d080a062702070c0b0f09040e 67
    0x840c01604400e00d5424415015200101044100c00204010f4420381030000d008000f24940e21580316400417104888510a0b40c40001e0203548a040103051003040d40d4922420b54143c1012a0011107a0b00c201d042c1e0b0800d00020927000310011a1500b2030b00b00d80901c01c0880d08040c2c400400b17181c00e125060241c03030b04072003041c184425001c100c420900010310090b08045902d256818190050007503130342803e9050203044140c03402d008000c02060142900030f00a1150041c1d00840c9443d50003100c40142865035441e880a1a0805154151200000385503141d00108070359001301c0e0030b50b03e030608091030840040005502d04041c2e4413400b80e5110307c0c5103954010b142c3c0200180e0707010804c1d9030084910b03d002030702034591411645045880c5100244148607070500c107040b0a40055181d4840c400301d00040081590754503403908503003a50f440ca04134101c5200c04032940c02c881035018040e201e009480440f40141c80c1e01c59a04a0390104182c0101c0d8000461134469619043c0220011520400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 255947751 1250 255946501 255946517
    0xf020105090d0309050a0f05030403150506100e060424180e130c0b030a0e010506040e0c060703051902010f0605012f1006060e0f0108010e0f04110904051c 68
    0x841081e0701d4902d550744440030991240d8032202444000c000010000d41c1000011600d286103251441e5a03901c284000c40e408003001b101100d08401a00c0b441d88562001f90034a80034815043d021190502c10350001c03980104207100102d0158030300103084180d440126031070001e80c1c0f440d04001d440f140818042080d5170444840070302c51500a1200395400100f030034845107070060140307008030480340d130b81d0018401040301004001c89034805801c0a46c400300807400800603502c402c014402503804c0d4011004032030748103202020150821070010203c0c540240361860400030f411130040c004d001d071000d080300140c1d150f1082078200051486010020031003401e1a2141d001c03400750166205114945181009500220300900c0d1034080c0000c150082c2442c50410401da1034038409001840c0440d400b44c0141282f00f40d18000c1e502841e0794905031609402610b416903100768014004c1000140126100903140001c0d00c1d0307075114030b403240e0f00551194014000b082800941450802d20003590a804c00ca090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 255949001 1250 255947751 255947761
    0xa110f030a020312101d0a1103060f01050c03130807180912050309011508150f04080301050603071106010f0312030c0509060f040e0705220e0601200a0803070f020105 73
    0x4403442d481c03000c00e102c192507980c1c00300541c40c41242d900c40f002103951803000b100b00c0340392003070303103d1147d003414a0810000d0500d444229560100305e03003030341d0040e0004608444541c00345000c0c0c02c03100c10701340442e4500351003000d0481d800340e19948030000e00c0d4002c400070301c2000c41c0c98055990310303a1078a07800c1000f000b10f81c458480381c208145140d81401000000300700100800c0d0400c0080c24004104188019541c4032040d541d441408614011512000d010404917052400c0c030070300840d0029010350560b420581080721940c0050441d5081c010341d0010401c0c071503800e00801e03000307080220030003071117600e036080c40100410150442002c05103001d41140d00d550300182943e00e01c0707034240c130340d6600e48084880448842c401c64000c80310903071440c01000314042d4088014501188030103000c0c102202c2401085e400000c02d400369039101407400c0001000c6511803042e80081d80e04980c1e49000b10380d00d042d442402d05800f01c1c0151a1000700100f00a689070b00080b10511075640703407008100c00e10740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 255950251 1250 255949001 255949003
    0x18060906030809150336060408041505130506160b01060c03030c02011503170403140d1404120b04061404030e190605030f07110303150a0e070507020f03010f020a110f030a02 76
    0x91100944400c46da4100d04150300d0f0002d0450780000b8070f00c0ca046856505045c20301c1101a0020b1007100403004138010038500503482103094480002000e10402d80c22410710f801c011582c2c000360729121245141042407004038540c2003029008081c80d44441c840c081d214100101651404103141065a0510780c0303031f4804c5086c5008201c1265003006401e105120281d05070391042c80303154405007185810305c422510f00311012405402000c400d441d1504c40031624185a042ca000381d200d900d1002402c14004400300c1c0c150140329501c00d2040000140d0314800740e141c0e13182024142c07010f40c00620046075032076070b50504103224460340c080b040e0b448100c030746403100062880c0301c001d00411211400c03501241e08103006800c07240201a03020240ca03200d160083d5107081c3d100308145801d01c194004400051b042004e104c0003400f91400355a60303480c014031038081c4068407408841d445c3d050742d6107400c40403400c611071028000000650303403291682c8100c41c480600e1701412070100040d0385c200b0481c0c0030441d50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 255951501 1250 255950251 255950281
    0x1e030c04181424090f0708030307230703020a060f0513030c05161824031b0504020d090b0c030906131a13121404180609060308091503 59
    0x20340562501039550403803102500380416000c480100d0a040d240c0394180c46980143d9510032070203002100c480703038000076205a4604d10b91046000a070410804914070500c229192401c2520001e43c1c4d00c604e4825402c0d1112a0b84455003e030700603000b00401030f04108030350280c83c514145002003840507040c98030303400c1d1407003210b00d40080c03d11400101c1003082104c28080048000d2103902050801d540d540802c1e14864404010780b400c2610f492001080f980c00107082003c03000344540303642440d0f4110740c0e4420052184220450320310f0070f007400008495445000908040821030310108001c6400d15084184003000f41034414018014000c01c03603101e01c0010b1b000d41c0811444840c624041960401c0740000031040c0303580003600c912204100c030390202c100c1609000c505c00d2440f0100200d00e420708a42e64030039410800787c00342c6c00304020090000d042101000d00d4100801c0010026034603010320341191040d5200315420440442c16181e545000c0c800151039044580c5e0551440c03401d1305001c20409 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 255952751 1250 255951501 255951503
    0x3070606080d11030a0c0609062307090303020c060c151609060203040e0604020702150406031a090609040204050a0209041508060c120f071215050f03070b070605090c1e030c0418 78
    0x1128406d0a028444550401c060300c54000c00e0400070000c041018800c3c40c0300c000075904d03066500c10040361040c1d2140d417161040703a070507601031700b007003101081002101e902c00e01004625104e050b03040e4000404103d803450240c404101e01d0340c11030502103805804a20300743e008c942950820b05c810030960340d015400c1a844841200d00581d2012280700051502d413031007071768001503c000302d00421555015846203610000b04035001181c2c40e034203001c1091801007103941e0303500508810045001810982c010940005042c1805800e200041001c1000c44100302091010300c102d03198100200d070010b100154000000100f038600e0581d80b4401003d05040142c01007803880860300014207880e20a40c0544000d0f081c1d0342040c010151f49000141031035456010b440c1c8600440341004480f490001851007c0300e0141540070300b00802034130b0f00030042c04006c00c400c555000e40944007105035201c05007204040c18001071038501850020626151201d800c1070180250325100c500c8545260032401c00440e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 255954001 1250 255952751 255952757
    0xc050a08030319060b030906040204060905040f0f021c050c0922030e03030f04290301081005180a05060a241503060b13060806040221040309030503070606080d11030a 73
    0x3416545040f0801000c09601c0750440303071004400d00c101c00e000443c10600440c002c0b0b41c01d00845444520070411518140d5008210301161000c10700040e044030300b0341da400ca000034142c90110007681141d0a00f120b4200c421211600030b292066401e14040038190b800c10300020502c640421514130200101607035000240500a42c141c4000e00e0340e80c10401c9a0070240f540001c20b07140c560b50504030400752249007006004054061071640002403c001317403412507581100920426036a076603100c0c020b000140002c0e10030481c02010000d8403904102c0030011031705c00c5000705420705d0816100412204417040c0080300340500e075600c0c15044c100e08110390540302801c0c42d4101401c040101036004091a40c40300341c440401080040c009060514401d00302e820b0781e11100287da440600700400c078401c000e0582c0da40c0307200b4201c1c08400280e440c4007a0380070303100e42000c06034241c6a8a43c41e2450b0010b040844407140c4a68050002e05401d01288158010034101b61040400c80c0040316100d0080c1030b524410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 255955251 1250 255954001 255954031
    0xf0708090102040f060815030d0207210c030506090d020c01020705060a030b03070807090f0204030c0b070309080f0325031e140c010207030e0a081002090f040f090c050a080303 77
    0x8030a60403076005003110300d52008402d54070000604140000c0716002410f00303912030040914100402e6030541c02d01e19a000c3c0c03407030700c0c10703c410581c5484041c480601c4108204c2081c0000610f40041c1d54040d41c0264005c10b40e521304408140c1c5441d1140394005c04640100c01321207400d9030001034280982d24111843c80e21100c42440c00c50050101c9110140e1510840e14002454080800c00c0420740e1480400ae0042c1c0d6075041e01281a0301ca503100c014140c200e0703404200034800001307010307082092081c60b1506e500c1e95503060310342c0b070a0300300988042c07540c00c0003a50790002607829085600c500c0082c0c6d0941c001010302c0d01e010300285013603107200800075440d00004903482c2c482e09810403c07031850240280c9901c0f94280480c001d4014100c102c0c04590f804540d818141380014598040324610b00050290064201c50b00010350006008190820046403600d00c0668070b41c00382c0082443c407140000750481103410310011490700e640c8018005c8034110380500105002008407507102011180220f1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 255956501 1250 255955251 255955261
    0x703021605060403080609090102121f0315020309060105090603030d2412060b030601120f050c06040909200d020103050c070c06050406030c03110a03091407060905090f0f0708 77
    0x600c0d8010500520500505007007104041d004020310303015040c2590050034a99699103ca03081788610604600d0b0aa80342d00060b5260340c02c549032612602d503000b08900c1050b980d640f03201c070301014402070070080c54000c01041100b120803c03400d4018441240c100030142482d0000c43d859225040c910000c440d100c2c0300d810341880400071b00084d145a0703a0504940155901d00840c00540d02c40707000c039a81414450101410303d000215030b4180d59a030700d84103108401c0380e0703155000d24801d400200c5541c000c0c0300030501c60b039850390083c1005002056011480700c0039031a01a5802c00c0e03004001101e4090410000981e8440700fa038508130950a08001445469001c4440e00701d029401e001000a40280c40100d000c0d41e011003c2c01c02c81c0c130342d03403400c0c07040340b01d043e0040c1d0660b0200007012001c03035803d100000002d8402d400031110540a4010308681003040c003005410000e031a0801d0740410f00d003400400107810a40c0c015a44403003400001801410300e1051105101800351810701000f141d50b001c20 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 255957751 1250 255956501 255956527
    0xa12020d09020a060201020a03060806090d0f2a030f0906270305160f0806010b0a0e04021e13050d35070308010e07111002030703020d060801020d0b03070608070302 72
    0x100300c0c242c0003010908450360382d402c024080d601407d007080009060507000108050001160750181d400b01c000b800e00c82418600c02c68007107181c200340404002080300281c81101c0607244600100f0304480100c582601141805007001b9801d0b01800200900700300200a066400761024417140454031403044141b40c4028034101c80f03081030300040c206001d910300a5481c1c000c14002c020880f046c1c9000840103640e680c02d40c07a2910824401d540c4001410410140e45510950000109040080c00141882e5180d00040901c1004041c4004500000075000d45214032600ca808000c180c1102c1c244428026a07881c058040001051100c0f038440e00441d43c1c10710480740d56200800b4600f240402d80b00e1140d42001015011f0031b01c40c0000070714100c400308002d030f44110000c10500028000508107600990b120800a41c0000c2248041603400d000c44980d0794001e002d130310000d10b220000540c4a10030910b4003011200c1e00d000903032103644203070400c010203078000e1000ea40c441c509050041e200c40c2000352035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 255959001 1250 255957751 255957761
    0xd030509010c0f0b2e060e0f04150510050304030c020603131b03110a0f0b0c031c06210b06150d060b04080c0103060602150709090507050c060705180d0f05120706110a12020d 76
    0xc1c27030303000341001c51482d4800e131900074810840794229145804036030188800e442500c0300751406000a034105080c1400750805c1c000664010481c0e281d000d568003c1501c1d4480b090740358502250611302e100340308000f80310b400300b040c2510000840f0210565454820103800d0306c8803500c42d01d05002d0000c981c0c0042c4800c18015544030b0002c1034241560740b001c0c2d41409006250602039903104044421031225291080c100d4074246030340c01800c8980c0c1e0340b100402c1214500c0d016108055128003005008100d81060154000402c200f0039665220780c1491030385400c02c10b00c154507904045c6371100411003598001000140302550805140c55900d03040001c4541041e9a00f0140746039003094140400d056000004040d41003003002a9001600c501104071114443c00c2c42543d8040d1031030490040714a8200135585205101d21f4000ca14006142d40e0a070820402005100c1514808030b80f18085c00494018404140c0360310340868508100300c00c0140c2840543d441150000ba0f0100741c4104000881d484 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 255960251 1250 255959001 255959029
    0x10204050a030503070302060f0606031f1e090b030d02030a0f02030d0c09290405060a0e09100509010803040e1801020c060906010f0f050d030509010c0f0b2e060e 71
    0x350081d440c0c9034205036580380c0c04000b04030300610644000444c00c0d03900244550003540000c100b070303140d501e6001d0700d508159202d81c0d042660780c11100000a007944082c02c2802c5030322800104400711403130b014044046901c0254080e000740c100c3c4502c005070329404022605c04403168106204051007030b00c0c04a1540c09804800c0030708624204580d2480c50b040f130b500b04110f4420000900001a40c0945d07002240c00c00a0b120303003200400c3c48240440c2c54200d0240c48271004515041d0000304140300041d000d144d080c2e07469001710482c01024481801c000e60524003410710340e4011440c1c1791608942414601006118a280c220301c440340d003160490030740454003010002021030351103080c02d11030651034544c2803043c01340043c5207070700c0011030b800c4d6010000102c0350001c114500c0c1908545040d520340d8044010b807410050a45000b07000034444001040141c0d02440c02043c80340f400c549a5501c0708c00d84003500102210002900000c51540b60101058805031314008007074442880c01300d100d100900038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 255961501 1250 255960251 255960259
    0x1507030219080310080f07092310030201020c0303071511090402031e0a0e1c0e0d050105061305040f0f0c0906080a29010e04050a06050a020c0105010f0b0d0e01020405 73
    0x5007200a01c59601d0241d800b4038034000701219010707600c044941d80c442e03048800340504e07040403104110156540e80082d0104080c4c085c0b004842600c20008800a0411210700100300003142c014002c1d961f04003c1019103050560040d864038172142c550ba00d403541c030301d80c80c40103040c0c4516440d0100241001a0303034500d400903100b95221700380360045808041c40600081402c0421748001110072035140503644039903140314043d24a130960103504a0702076031085100010302500c1140c0d6080d940391100c442e4075031170040c000042d250400000f00000c1c101648420720320103061405000110311400010707542c7c06d5124484211000303051510010b2a4000ea0140c0a40791514400240150010404118051041c20600800c1c24600740003003100040c59411030303030b2100081c01403180c00045c3d000c145c0c00c50f0184c021036a1000003a07641d10700342d0300205e50901007140c01040c40544218240111409003040c4000384400c00e08104401e5294010b032007044110b1a2104240c10302140294120340217880050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 255962751 1250 255961501 255961543
    0x8120a0618050c0f0c06040b0702030a0906110c0d030c050c090408030f13331109120703080a0e010e04140a02160605010608190509030d0209060c010603060506030708070515070302 79
    0x2d817100e45407601102c05440000c040000100414404400c82d03503040d07119203034005040d05008080350b0f0301140000c2a2a0307071040d00c99180450b40d5a42e028102d0300c1c8aa9582d020952642c90f120307041030285a091030184545030f040c400000c2440e0180d07940128000e00b40c00c8140c0e90703d044114002032800f0043c0c03c0080540c01d0000e00144201441d40031526071814040e0031403654050305c11600003900c03003c0080d100384640000352034079440c400f0344180700f04101d401142e1a901c800e281c50380030230b100384041121050081c03055604144000c05105044508010118007114001c0d03000c400100baa0320203903030020780d030481000c400e541800c0c540d070481010030040d07840d000041e020403401c5c1c80010071080c1c0c00441d81070303c0c07585000f004d102d4040c0348065410486a01c1074000a5000582c00b158480070134011581d80140034401e5800950085401040c00d0400b44141810400325030808000c0c0d4100c1c12051105031190041d03507142a0300210070a5641c000b0703007400c90401d0968006034503004041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 255964001 1250 255962751 255962767
    0xb0d060e0106080712120c0201050c0601080d030c031e0507200601060e1c020f060c16060e0f1503040219180b0a03050a0b09010b0d08120a0618050c0f 66
    0x5601c82c80039501e004007203840d0942c4644079a005918503110003410510050a00700f10188151701800040b803046c10145d0134a031140e04410f0420000f600100900d9014500300c010aa625000e20003890100d41810080200f0207800b445183c40c3c0068054040c0361180f01060600c0e1182c0c1b1281041d510075051103031092910100c031a25000d0a102c2c5000152042d080000740d80f600c00c880a0102c0c1c1451100203900400c1e50900060850480d4040d80c03103c2e00340443c826503031051005c0e0011141103104182102d080a01c040c240c111450b00f060301503800140c0e0441c1d152608040c14882070104104907407641c3d11840018402d19904280207145503284000042d407400401c09134a580e1914902484101701c044d05111041b4000d100181c081c1d4444000640400d80302410550032031401d10011034482040400b2903602c1520280885d03001c500000c0aa662511120107690030440e00c19003448518500f0760600d0f4001c01c4001304041d540e95a90200c1c4040581c201150b94185068104581f10303c91 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 255965251 1250 255964001 255964003
    0x302010f050a1401060c0512120402030d0203130e04230307060e0303070909020d090203160612111c090507031505060306010b16050703020901080a0c080105040f02040b0d060e 77
    0x2030404200485410240818008291405102d00341c0780c54556200140e86405070803a1910560041500c89010303a004000c01259940028081c40580004c1d07030819017082e01c180340c600304c214200401190002d0280c4c044040b080f0180720b04890360030545002680310350601108099500b4040140d100a0152000c00c4210110241103214080c120801c120030b140500c0640340e1000f2106080090042c51080c0071400584d800307804006002080003030140f225a020a18010410300802e885810312801040303101d6000c0001e5804c0c025040c03081c451491b80b00d221a20380e01400b525142c032200d000c00142340310b103516440000c1c01c40d00081119180d40d603a0810b14800e10348035011206003800c2100055645c10005901d40c101c900c8e0045c011301c8c2000c514a141c0c0d01700c05c0040115281c9c012440e000000d603036281c105502030498000540005a10303482c1c07107441101c09074416403140c0d0421f0100000703d04040054081d007a0103a4020a00c000c0400c0000e000c1079150718010207a6180604100284070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 255966501 1250 255965251 255965261
    0x11206080706020f03040b041511070303030e0d050c060609040218191a090a0f02070f08131a040e1b0c070e01120f150b03030304031e05091806010207090207030201 72
    0x10083e02603d021014800d4455124170481c01070780300480f4208810400780b20103450f140d07003401407441e014004c00283c2405605010346680260300091719800d40704441c81e000e100020940441e42000340c9071094400940c2d84449004222a10602c01c801c0007a06545402c88a1451542e8111140c00d0034500035100c2610070071851080d454240c80c120325850b0901031035446104200008000114030340e280e151210150004070344a02c1050b070203018040010740140c405040c80d44c4910406501c81c415040c24481d804a0b91b440751600603c0010340d000c484d0101802c90b400e503204006806d42e01e0741e0328035a020384103c0c58012096114000101c10700b41c420302203034a409031480c4808288260341e0b0b420001c4181044480082c0000f01c418051000050103c420146c52016105003c180f10844000090941d0002c541c00d902058040000ca807018402480015018095090403810580601c01040301b0700a8443c0121200c0051000714410b83c0c0200709810060850003025961401c042c03030002e010b04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 255967751 1250 255966501 255966509
    0x513090f1b2610110f070501051b0702060a0305090102090901080a0308070201060614130b040f0905060103020331080307090305060105030102070203300301032009090c01030b0112060807 82
    0x4520001c40030041034070030092950305042d001041008914100503000b0101010728032408070082010140c9852542e000d0141036004200018082c50300d104c421001c28135040036071007550020410359005036504000d81d90903a40302d20300082e00e596100b545c14024804c0e0240c080d440600c000002807146000141200c0c1d69109a80304045a02c509030142d0a0f00d840d4095600070a00406400350400c44400c041c0240c040c84034054a0015901c3e082440c550b807160300711410b13503038070f00205014568a40c0500358200100f0300c0e0842c554900705030400002e1b800c06003840341a00e081c880480961584145506100da0400481030780d030300700b801000c1c21210349031004881600642000140300e1a0601c00d0301c1000d03402030041c1a1004d215000d0038941294203103028110410112480c01400761440614081e5200c0c3c825041c2c1100386100a10607481c0384200c1c103200f1050303c0e0410510500200d00d40c50300940c00c1c00c0c041445a00c1d42c0c01a25005402d00c8200031403468003000040303100001a05800712 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 255969001 1250 255967751 255967769
    0x4030f2601081510121a0a05070f18051309060e010f0b010212090d24020703030b040213090509070305010e0705180903030f0a0603061b12060513090f1b 67
    0x3e550036400c0c02d01030150840c1d090030304c021080b804000500440b801c40b407003a0703c00e040c003529082d01000303a045100800d03070342070701004e544404105007581c0200900f0791000e031500780903c11074100d000154900d142d5019650042c03060400d41500790509800c442c110744e90060062042031012340c10140200b002d40c0c0100355080c03c00c4585081940080384e400708500003e18510b1419003418240f00c09410302181c01c0356007816604e48120001040d020801618849000162740d410907800d00405880c81034903020f10540c810001050092054a0700004171007a944002c2259a42c003900e19041ca0340c0da42c006880f0b03509241c1071029040000c1444400e4910468401c104c550a0918110859500b10b031012815402040440d44101101c000d550b4400101003022031115204c1d540c4006862807038a158486482c460707100c010b40c9802c0f07a005a8003041c25501000710b245003400041101e0600f00e00c080c0b4055942c8a031000388100b141c41c203075041342c0141d040c510213156403000341c5c440281c502c81c01c204 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 255970251 1250 255969001 255969013
    0x909060e0a060c1425110d03050705100b06030403030903050d09030503010503011503170c07171b040c0906030504020a09061806050102030a0c0308060316060f08090f030304030f260108 81
    0x5941d010b00155006540d4040d0010301444180c81c9a2984103500c0d4002d61b01c01c84031040b110400c3c2c1c0d481249103030191281d56070760784880306403030860700d814240c0c2e1000c0b480c04e04244802d8560345a600a413944142c051401241940590a09a4003403049142000046090404207414950420003c6040307903001d4000704030035021009040f01640c11030000414591400c68001e20002005000d094220038244c04c0e00d10b1241d1710500044080402c25a02215030000813035940340861044402f4100d04094800f40000102c02d000144003031002e004070304c00d144e03850700410155241c20302d0342405000020410030021361910081018000480d407141d080c0e45c1443c1e008034040d44003206031107101d0255190108004815a02138030410340082060b0342602c1112000d145024080c00d509001380f005403242e0a0101003020000c01c0c08000074407081081c0d0020540c0040c03041c0c0082100c1c0e021fa0103140910b602e100e1214100e030183e00300960042e40c0b14025203504a488541a40b0504881440040f611 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 255971501 1250 255970251 255970277
    0x60108071e030c030212010615030507030b0901060509040c02010b100504050a081203040b0403021009060204080c150a05030907241214041202030c0105040609110307030c0909060e0a060c 82
    0x54006007500005103a000c107990108014107104c1c4180c28295407603800032420701d48035211010b030070000400742c0c1c1c0020389070018408665094030603000080c50030b5803600400c0d07042c007201401c144a1311116a005070f1369602940d225510030340c080c0003101d500400340c208514689600504580007030003007032720851560300000343d402c0000071954420803465a40e182959210f485888540c14001c105405500a03a4001c0c00002c59521071400c416100d50390040c1c4441c2024080391510341c0503075905000d42141c9071101e000401c4001902c0a12259140c015503aa4400034164185030039540702030088040300480c100380d18401880c40781c034494555190034141070040566416101e002d0803562202d6075900c0860003107038813003d802c442d1010f140100e0303141c41e5040014a00710f0718111003d9a10a9441e0b00040422005a8090380d00080840c01410210b0660700c03005c000c4c040520500044580c0c2d0916103041002c02d0700315201d4545400c0946503000364504201015103081d00c10b042c001044607180c18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 255972751 1250 255971501 255971549
    0x3060a12050a050d090e07030f0605210613051b0406030c17010c050a0e0906040b0a0e190902060d0b0d0b0901150816120609050102030c0d050a0204060806101106010807 74
    0x1400c1b1b81079203c088109807641c24040c0c004010001d842c556070780c0c65031070100741500e400c81349511004400d403641c08000f002c11506400c050024040d007104803400c0b020f2038041900010f0fa10715441c1c640c0700e0040d09100c1800041e00400310740d880104003a074500400031317045008072445000208000c00911150020355030880701d074070889151401182c0340700d400340420308242140540c00440900005403541a80c40040c289200d107038451141841600c2c200040f03c540c000880345180c41006050000500550000d04507010304040906150f640b5580303451280d40c0c07400c0e5003495580194201086007000d01455001c1e010307007006441e80003103100c800103000400103010341c0f8145501900b510030342c1c240424032900000101e002c0c2c0c3c200b0345540c288070100da070a20095000e0f407560305145964111456082e8251200100003403061441407208120b669000400c0c4c0d13502007004ca5101e0081c0003400c5080e03401001020011549204003800802e183c48006421001d880400b115072070129640d0042c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 255974001 1250 255972751 255972767
    0x319061404031e030e01021909080a2f060d0501210b0114030705040c03060602070b1c0b0111060a06051203030c0f0913020a020a03080603010903021203060a12050a050d 74
    0x2c000596620340b030f90000744042e815840700c9040e807030046034051408800b1400da8100f551804400f05100c070381440000d411424a800a00f40c00f400351482c105a91621008090f0480b00d90506440e00d8040441274000110304540c1d00d00c0090880740c458031031400700781c0101000d01890040010084030704e400c560341504000c400a42c880c0301d03100d0603070910680e40e04605050790410b415104082d03002c80d0540d118000c8201d200e14070307580015220b1034920002c0c500340ca10b40c4044211345081001c0f0030f9509201c40f40d810700c0e4202c0030000ca00007c1020040710304100440700d104540c06200b040c49020002278100c03008071030341180e0000c3c5140600289070345038401a1411841e0b0039080003485856680d07a0060180324100a11401c11a02607141440c1030380d102030074890040e0003140c0c0142c02c2542113407102d90050401c1e0001c000003442d0756006507592a1161801f102020b000c80050002ea41d8183c000000c1d01e0a0b0504000407200340c91700381c2d90b652003074404a80a01030b240c080080e0520480388 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 255975251 1250 255974001 255974003
    0x40f031a090d2f060a0b060403200a03021804120513091a10020c0103050a09020f0919090c0e06030303060120070314160905070509040b0d020319061404 67
    0x241002c0c07007030503070305403240a000c04501090407401d03660f1030307038a60340e400d5220300c0380085030f010705035529191011100700c0b540420030301d2050000f4001400071510b2150405c0a1321558038006000c18000030000b259440300e540000d40c08500300c40d9988400c03c48080441c0250b21405c0300c0c0e8030600071624103840c9030040010075181c102c210001044072264541080428260444140c50b80e0700001000c01d2103556802c40c5040035901c1171400101d40e59040c811968040d0700403000f00441810b40d400113019140b0402c0c2ca0f403107148800c0200e6600912003144e903034030b00c0e004c95040100b11014505030380ca2046520800c280b8035001000101c0ca0f0402104070303446190161f4480c2155020300d0034003485003150500440c0184903803000400080c615001000e41c240c1030b00010403041c00d09641c041c06d42d4801f904082002d40c02c0c18140301c0790b43e4000d020382e100c03218100c41c0030038654074030000720b500401c0001001c1d5251146101d2024001380d003007120310095006030002e11407181449904e441e80001910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 255976501 1250 255975251 255975253
    0x91201140703020f1c021608071101020c0a0303051b0f070806011d041e02031e0f0f1f0e06160909050405031c1d0601171203060d0c0b040f031a09 64
    0x607420303400c00801766983c901c8080c0b200040c14500c4c0342001d45110302c3c903070070115406c1800007800014061420504080c81c002440142080389201010a02184203840000e00340580401c000606d80b004409100e02017801e8002c81c0c2d0016500648140c0e144840d105440c514040c8100200d01d500070b02401e0a84260300c1c0902451a40b52650b4410b4620030100d1340c0c0e1083c01081003013000603030f010b110301e2a02c0d540b4900c034081d811f8120104c042c00c0000d03045000249910001184146900c003141c10f8035001d0f0005240304012036040d69110107804040381c40340250040d203041188080100202c185003170110f56900e10b1040e2a80400c0007120001e0700c02402c107900510402070400076110b0a500031113a00d6401044240e01000340c1c13400100d141121422a80100300180101c0c2a050209403c0e02803100c01003e002003008400000c51002070640d902440c040d61824003846486c05c2820010b0a00c0d10900d1f80d101d59900700405110781600041714a02c3c0000c00781403030109840502030048007140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 255977751 1250 255976501 255976507
    0x3070e0705040902040b03060901080a0c031403090613080d02210306010c0f0b0403180e01050f06040b0a02011a0402070308150a0819060507180e04050102091201140703020f 76
    0x400010802000102510200081000049401c40241c0082c00044c595a03a240d41c4900301030301009404181600035500c6680006070701000704241401030f4040320340082c0101450b8000000240c00d503c1030200703547c0c10210025000f104c43c46a004108121600942603030441300b21268101d803910ba0200c400e00301c5030440720050724919681401140c1200050600c10500e201640d00e101c1d0211203004140c48283e550010882490740000d1050b5400088132984241c9a04049001c40144418083d5030f0007440351520110050701d0340003c40703001d0071079094902d0320ba00014000074083c040d80ea20624580120f42c28508090030b2500a8456203076164580156542d02c0100380c0204000a1070744940c8200e801d50005514a018445480c0b0f50742c0341d419000004803542407036400e949010301a04108103a000210001c4041c40c0e5411040d681c04010340342058403141000c030b0190080031404ca5002c05280045051901c0c15445000c1c1041c003000151032942c0d0321300313082c0c0c224091102613102c069010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 255979001 1250 255977751 255977759
    0x20304081507091d1501081905090c2d06120a1a090903040303090e01120b09010e192f1c05101410060c03080601020a1b060f0507020307 60
    0x1816620b03a00c0189880d0502d40d00341e80e01844504c81c5060661900342a41c44014844921181070300c56601242c203080c48903107824070b24504a416501082c0588103683d8810118100a80034018640c044100600384249560851400c1c56004004080d4080000e1080742840250408006032034500e8028114650350381e4514500c00b0103020415003c614000b807541661082d940d03400540c501650b40307a0003c640b03071800c1d4a0040d100d140c481e0001a01c0103841401004440c0c05d508168500d540d10403006901600c0d8925070301c2c050810701c40715000078010001007000101d10040d243c0d00480c028607a1404404010b116451031002c80109124078041c03000c0f119881c1d003050108007200010965022407070252130344a0604003180003500b00c4905890f4407044a100313080b14420364008a9402400400601e051000350440d000c1d0f0000509000001d400a4400c0c0e00034003190f8490b0f5040640c07018011701c10840444070049500030100131611614114900910900c15035a509602800400d026810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 255980251 1250 255979001 255979033
    0x40f0e07110d080f040807170a0f050c030f16060e03071109040203060105010818030f0d06051008040209041a090d0306080c4b09062d01120e1c02030408 67
    0x401002038680c00010000c200c009230581e5445452007100c51030080d00c800328007100030412050070030b0304000c110040c0311080039840b020040701d00100b100c0b008181d84204901c0085034141c91100017601ca10325083c4500388107040840103200481c460941c000300138102008200300e9030420b40c3e01a405a04c124014416940500030322a0040c14043c9508201544a030403a0310310b0380040045261880007140c1c51030f403414075000c3c0b1400303840100c5844032803c000280c020042c9070000e10192042c5100c401181c140403250b008483c901e00c40d0703580900070380b811464865984071030414100c00286001c030001200e1001192808500d0700081045007850009a4041c0082c1d1201d2014043c2003002c108200c00c1a00b04180390088001440210070000b21000810081a00080046004915841c2400910001c014404507501d00e803440030300040900c200100c0303d51881e4039600c2425481c1441c011035150300040c16a485404000c41101d4100c20418200d03100d0146206600543c0d000d07050052803112 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 255981501 1250 255980251 255980281
    0x50c010f093804030606030507091e0207030e1503070806040c0905040b0f04061e0b09100c141204030b0108010b0607030f020a020619020c0301060819020105040f0e07110d08 76
    0x1600070082d442c0311280040b0a015880b030b43c021500c01d5600c032410010030906201e9600100a8900204050921802070b021040c010f801c28464141c0c1c001400d204060251007084451140a0281c000000d0b171560003103050352042d58401c2c08640050001201460107015083c842182543c23840076080c40e200c11700010300149402580d00c0310241c0c03c3c04a158681d81301d0030001301156103815078074031206070303201c021006590070a0041c1d100400150703850340c40d0f10300050008940c91820808800e46400c1540242c403001c0d042010500034042c21020b00500c40300070b001643d000b07500b08100c59030b88440c490300301c4000442c6540c004005011a0010a0140c032040d9141040c81c0142c403c0d50a050b07000842a030b0105103086a8103200c105089003940d8104060401c0c410203400800c601424802203d95400e401601d40d46144502c050180440e403042007650010420344031401c11454480940b1031b0992821030b48140040c166488050480c3e400003001214010603496156040d2120401c101c034120f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 255982751 1250 255981501 255981569
    0x3020604140612091c0807080601050304030c05011e06060509090403030b0a081f0e0f1e0124060f0906080f0601091203021c02070803030a050a0603050a050c010f09 72
    0x2090034042d104120380c8250f149441303240080003a0001210400d12200450010301d940b0040219060030490074640018901d40c00c49002d09000d9140da0b82c5207001c032000c0d51007003070003810755081c064501c044901c103048100d92035000c1da00900c441612418210b445010303040081f58811a60008500071901a50090401d85409049008050740307a881e510710308a9203009c4501100704c1c1130101d0072051000d10654982060001c050300c0c00402d64251107a54102c4041c0003243d10280070030900703002d8003d60000c000062a5022140e68242c0c0104074003010070584030703100100b200041403043c1c00d446400c0900680c0c0041c3c803a0324140d22199005d03155404010100780c1842030481c0041014a01c20081030500b40c400e60060811614088443c80a04a6600400d00f55481000280320b01000031058a51000c0e52001c00a016541c044020018000f154401790207400344048900a001010494118140003a210813104d40c0b40b07460115910201c9204100010b1007454503849401e005c0317244020b00c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 255984001 1250 255982751 255982759
    0x801050607140a0507090f0203090334030206010e0114031c0216140a1a0f030a06031202060f0f070e010305070207050a0f0e130803070c1407180b0a0302060414 70
    0xe00c055403045490105071003c280c500c1e0340844010041c001940c0208003402c0c1e020171042d811400e1480c40ca5903a0b005507404070380f200088840140044003811048005060300404a075038000c0f960034007a40310130003801000d500d4501748002103070381d034581e800248081101034003c143c00c02d15010160b00c0000072420010460082c00c004004c205a100c0a480103042034480549610345100108102d001190b402162030028130507071501d4181c400d80c1500d05020b41c2480040ea00d0f5204075440e0000c11441c0c02c010403140040514621890340011418070075400c40d0182140c545805540c9807070804106e0303040f40010034a296501d2a54800d03044107406c170945004564a8580301c4c00094011a9503411011220410400400060300085c4000e6000045d0b01c100c901034009a480301882440010501024404a03800da00200804003010240c0300d40d10310290750180c1d4807400354640e0318001c3e010900c9180c0c05c0521035205032505803018400c995000705018640381c5002c107807680a0180081131640 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 255985251 1250 255984001 255984023
    0x40b030a0305161b061101052a0405060408060f13020310020f120712140613022a010912020d2f010e0109061103040b0402040f0e010e06060a08010207030801050607 72
    0x1803520130241c0607021844590340f04c45410400001d143c4410540c1703a600c968101401d101d07000b0161a1214140910040105210f00d0302a800c00c4092003075502079604100d00080c0010700900100701d107030041800f4074120145848001c0d0540d40c40d89482c0d400381d4980c000d400381c803009007281d50080401c40d82402d15142014030384c0c081e14084420496407103011a2004200000107184e500c103014407426600051882ea007000d0307002c908058ac000241420701030340040d002d04540030383c1c2008440740c03400081d00c08400084a001c0e50207000c0b1900c041320000d2100c000b810885002240200005d640c0e0b85e0f80d4000508200d8061013203003000584808694035070032084490417000c0c01454842c605031030011440145d40c0c503001c1c2c11610405110b5440741c00a00c03c3c40f00150180d503005800c0750301181c011410041d054000b0008001100e107000c003940c41c00e007003070081640200d221440388a08461854500f55a42c410703500740d01c0383c50402000281c07194010700107845c02d00c0c060102035000d0507401c2c02d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 255986501 1250 255985251 255985253
    0x21031403060a0e04031101061d010b0714160305011a011b0c050d0b151005180303040b040816140102033727030b16030f0218030606040b030a030516 65
    0x800040244d90580001d41c9207110584807520900a03a8028052006801075034120070941d4192410103029248506000207010402e10980001030800040024141c600410241c0098808101035100482d05542440010b116900b07442030040340c02441a10b030743c200307007000c0c6034080c140072105242202c509110b0350000c203503a125115640d02082c800d000405840c10141d0b0512040b418008615102d441c5260050203a240d10800b90b8462034810a10041410307101d04c000703400d60242da004200c0c104004240002c81c00c03030016000002003509012406081c0e00d87c070002c040d0550316910940540d0003044526a24211014841c1d812201800d4807820b4002180340300c0760f50000d019450002900198104040d1035040782040c01c5007000d51000c01e452461503443d0340103000f005000e95a480d0260140c0c8820900a410580385000c0c100800c550780c02091184011003141d110046000380f18210000b0424145441030b030b0b045040040041100d00110396003211580c0c4101702461400003151035000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 255987751 1250 255986501 255986519
    0x503070e01180f0c0f08010909030903030f0203043201030603020a05061e03070305090d110604080f0d090b07180803030402090603030d06060201050f060d030e0108060f031621031403060a 82
    0x1254001e13540c2e4840c1c20880000c98000c104007010b030032031209686401007000c0080d1300070040b40203c1742c0c1400c00c469990411541641140500d038481c041d00114011503492201421181400346400340f01082d00715a0340e480110103c0d01c0c94003000b07401c42000c40d414000e03854a94042c164605400582c1c540c4140c540401d80f00c10341007502d81202082d1940144008020240410340c1411100e1814600c0200745a400a50300e410103000540710302000180341c1c6203201c0d45412101391244042c400d03c003803003140c034261403d1001210444000b41445039005104017510784000d0440d1406001182107448a4003007090304007000d8051a89440100280b0f07000940d5402050000c0c56039800014075458aa11145001e5070700401c840e101d031030090510800a40c00c5544420f405000b07107000241680e030f44010a010401040b9a00c0c0d15118281e507520b14411045040d100b0380340c01140342120001f03200501c03c01e50813118801000324055070b04078513100a20a01560703100900828514800d41c0d940120 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 255989001 1250 255987751 255987761
    0x1c0e120d02090306010b03040807031b05030c07090f1104031709090f01030201140901050a030c09050d140705030a0c060c020103020f030924070c031101020d020f070501060503070e01180f 82
    0xc03401458021402c907801c2d14081c030400380106250148103141d4a0079540e0035004d4401c002c1e00505101002c41007107403510010300c440a4040d803280c1101d9580c80b5617505942d480301248614400c2078201001c0303200d401843e000f5010300c04805540c140c18141540c1c0c440500302240e490348070910301c003444000d00d29558202294020710f4416002d00080d411400010061442ca03070101e90360340701c10407007d503030360364040112445110681341c0021403840c1c004003160703040703165804958003118171181c104c00e010728100d4180b01045c82004642e001580c0780700381500d80000c00006000101c00c0a0100300c80e90148140b103c2c000d10501d00140351415080c0c0c0c03250950004d0718451020307403040d0203404900714454950303100009405400440c0f442e29640003042810803010080800100024070305e00c1c40025015241c840320f25034030075526113166000000c0184c006c20300950b881e6091640014003400e000c0b070800c0544420007400b81c07682c0c2c01c1880b066404d0818803040d0201c10b07030b00c8040b000e0b117107198424 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 255990251 1250 255989001 255989017
    0x50102032706041e0801051b0307120e010212010f06021f110a0c02030c090402030718020702030a14100204080c010503060d060501030804051206060d060c05120702030409050108031c0e12 82
    0xa000e038251204c004508006400d802c459032036850701e002d01000d4091941480703031001d400300c54240d036541c80c250121003064060a40e0803005042201903200e0403810740141c082005045414180c0307030780c0d440803448805254800d510240e04080002e41c100803110032000c2125001d0030303010404c03040011801c8100c0d484403c120700001c081c0c00d261011440c0501200c0000101140c29016906098000985402c2e00c0e209236841104120301a28109a00d601620f00300c6030002d044d10300b08482c03410107080c03041c40d10302d803650301d4016043e081081c0723003851081d00c040e540610010320341a4040ca005403840c1d400500340ba548902918a9080011000d0017218086c520030400c0b10340388c80c608030500c51902024032101001d81c105008000716038403254901f080c03181c0c009202003280102030005494502c5904405c021216160301080b02c503540000080045603001d400800040c1c0c0d0382d21a050700c3e8007800d00156030300b07540304d80c860110720407580040c1814484081035a80c42100305900c0b0391598440c2403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 255991501 1250 255990251 255990269
    0x1050906040e15010605041802070c05040c030603080c03070308010608040b042915010e010302210c09060703020105011a09010e100210020c010e0c0a0b0d0e0a02040e010f051005010203270604 84
    0x5414002340c0f680800c00b02c0010a14442582031900664039440b00c00303001c0c040d540c003480e540c03002603e1041c0310780c00c0200199040000a0b60b907042400c410750302d03035100c03032402d40100c2d003c40300000d40d182c07041c08030f02e101d55048100940117446960300c0c0c2420011004040552450203045988150031b0000c0160145503244200d42144040c80005030040450418281c10f061050008030100840541c03000c84a4035145000d040035074400e500c2803114002d030105550440e8000c2085010150150300050685810b05503141406108c200d550b00c65204603190140060161081c10300d481c2403040314401e40c806c15005846500350310641010480e0480f0120107045c0c0c1d16103001d0001c2c19418031000540500c240c403108001420301ca44240d42c1d110f01c8001199180d540c032f065580c00c1e01c05000701da182c0744e070040c000e204110024000f60b010382204c00ca02d100c040d18000c0401d05402c0128006401c403101a000f450030400f01c80d11030a10801e0800b08030b54549003800c3d032254240da80c0b0009002800c0b90300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 255992751 1250 255991501 255991507
    0xa0c060206040f060c231e090a090f0608011103010303020606150a03020c0a1203095318010e030105070914030c1507151a210d0801051801050906040e15010605 70
    0x800021514007c1d2404645040410030000151a040f201d5000c1d00d84941c4023003182d420031041c18005242c1c6038001c181c1940f0789850004030001841c001d40c102ca000341d007240d400f40c59007010842c1a1a069100c0505201c00300400907215020b90058213142e0030000680350745420b162580e210040d1003800f0706001960b18180d40082100c1c1510110000155103d500c028588411014204000c0c06800c0300c01400c1c0004940300080c80b10040010318580c1041064540c0090400d0001400c1c944480a0100d510a860001c503801c0c14880c0d24810400c40d500e0040742880e060ba1001c1010030741c074007203070503020741d064401a035221003400c420302203d0003a1907503a984041c14000c4081003078001407040c0e01d04080800b400500c000f0300a03414008101c0d005c140720402510424841800c65441a105014844103000032503040410241214021b0702c409142c450002481c14000c1c809001b120303404000c1c4000b050090409901c2450b04202000407030300c8a403041c1601345aa04c20036402813000075000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 255994001 1250 255992751 255992767
    0x804180608190f060e1f0212040b060d080432011e12110306030606010908060412030225050106090c020316050309030703052a061c0216050a0c060206040f060c23 71
    0x40d81e4206c48103004d041e0860620440c1f0341b211080340e401800107400e0203014030119200750b0700c648030080125445100c26a8450361441d01da41484401320428808024452450f042c03d071116114000d1510141d44d1054540001f84e290480b03944058965001c103e18a82c40c207070b005c1d9251241c49401300000004a442e46444c1007010701d8581c000780320b80e040001400040107074a40c00181d05070025445078040300000a19441200240103e00400101c80107145420210340104040c1502190044009100f0241c642c01c50b142a03810280061006a1081200d040da00000340f5200300c900e0310590569107001c10300f43c0000d207002e42540050383d55802011840740c90341012070b82000459544280152012542c20000b0300c14054100082d10403190400d08030910821a13041b10724103d0b409807105150081410311075030b2030f130720004110342034040303400701160313860002440610450780008030402000b5642c0d14400906080c0c01d2001c10301c00d0b14100007090b0b40c0e500700c0120803032071114811038a82c840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 255995251 1250 255994001 255994033
    0xf060b0301080d090305060c03040201020a080406080403020c030303010b09090c360d0309030303020a0903140c03010e06060906130b0d0b5a040804180608190f060e 72
    0x1c109803502c2404091001000006e4020403401d90040c4003258643d1640d54030300041c1d040ca0000300c0000d155440004010440b0394000005a02403802035003150002c110040a02d0354910082c01904100f40b01440705880b1851302c03410b2140d1016202d50600d0600040300d107917690b01300110701c280921104c000a0540c1c5a03026040e610000b210413520b1340107000301910302411240e0a400041c0c105500044d103840701c0c07405000007c00440d40190b40030352004c0d00b450410b860700c4040085c9031003075080812100c0c8000d00040d000e409100700a050b03440c2607e4030010800600b64036014030f1040e44d02e40c2c0017042d10b940c030081c82c03100107401a98268250f15041071509581d044c0c00800c01c11249800e40f2222103c800c5e00880890078a440d1001d4400c00424100d10124440103c104c015281120003007000f048008805001140c80c1c880020300040305c1c0c468600f055503441e005080c0d2135072001140041e01080344054582aa026200e5400d82d03400685803801602c00503810a401e41c6d01014100e012596 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 255996501 1250 255995251 255995263
    0x503071a0105090907060f030b010e131b020c180709080f01050103140307050c01080c0405060f0703020c030d050d05040825020a05010309080405100908030a081f08030d0507030f060b030108 83
    0x41302c1015029541c108140a8100303003003010300b03500309640e41400080703e03406510340903080780c0c0081806014000a02c0d06202400c003103c290781c2400b8034440951039450000176140a0725100611008050030a481541003110006112101b0000c0307100c0c00083c209018000f01050900d07810000c5404e6055081c003240d40e000701c01c805060303940200104004900f010991a001c2502407909207801d440302d130300c1425280603d411907a80028005a074044030350b030b035000800e003541c0f0071740070380384000441c40070161134088a00d242000710b0010800798055440d65808558003078440e080c070303d0400074010418404591000074400e0342d103420000280540c600320b4803080c0100750905c1c06000300c014640e42c04132a4000c0f8030038140a0100103012065940c0901540809007604504507a2956424540248003060039078002c14090a1020454410007040095000741c0c2c00420003180b40c0401d482000b4024800102a01c00f055514110200191458000e0000038030750810362a4907541001481c1381055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 255997751 1250 255996501 255996511
    0x60b0402070b1f0e191d1006210b04080a1b29060102070b09030f060f0f06040c0e130e060a060311030c0109060516020a0323010504021c0503071a010509 67
    0x95006010004400311700b201421141520540108040c29100300706d440911079550044600d010f071640e20f144100c4c0b0380c0e01080458500e40c029500c409000c81e091040d001100101401c001030074000038000c904480c004045178440c9281c0010041c107040000224103005810072101c01c1c0c0d4103204800c40d685008500304806107c40c40000b42030404a0010b541c07101c99100340c0c08410760204484030709075424441003500701c6410060791818901200c142c1d500e00700890783c1d14840e0710035501051050406200b001c1e007030415604d4090703134130a92100300040a1209a48501c0c160303210746158640d9401840303940c2c0602c09140021520504603d400c12040c0700114035507000e5406080c640314035a0b4012990421a0501c0c1445a602c1448151038010100c00650181d0001c0f00d06000104015521841020341c00300c2c0342c0d84074820b5441980070390030f844054602940c004104412800034200840e4961110341c0308604507403038202184c0e980d001040702003545003480038120b001003186007800080a82c1c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 255999001 1250 255997751 255997769
    0x206090d0207050f060f03010909021c050a230717101b032004030305040905061903080a020f0613060b091023060705071509050607060b0402070b1f 65
    0x10840000000b5500c0c070392840344030300c114a42810403803151110401c40b15640c104014403660780d0303110b00c480400303022250012030145000c070901c240300e03440b03030354010056640c040d02421100e00e054440c07c1190201209403212109803241090104c002009a203000b0030004480300c040403d000e9850341800000d0820b10400e80c01c0c840e20010920f85d13042030b0401c3c040030341000500c0542c4414006203201c500600c4002c001c0000030040145034005015004803039455506001c2552403c05201122003407002d20303334110345103200a00004000e117004e4000c074221361044513061b01040350340910304001135076400100682e441482c0d05004490003581c000e400c00307907110280b0781044402000c0c2d00200780310344050300c03070b8864141030421400504401103031002411140c450103c3d0800548881c0c07540716503103004011000e0b8500d03503400b82c4240c100f1034400a11312030030442941c03100409442c2c000c40143d80f103030f070812540d4002100a1012400340352040155400c04008034074074889882c542d0045065 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 256000251 1250 255999001 255999013
    0xe06070e060a0e060c0307020306040c0f0603020c0c04090203030906131706090307030c0f02091603050604050105181f030c09050a0b0a03140f0706030b040b1c20060a05040501020609 80
    0x1070300108203e009203020354000356614800c1000d18118002c15030000d6050042e601444180203ca0300c0a0060f20b250b4050103104940c1c0e02ca0070750407841140b120030601e40060050b9641c3d40340c240e01101e0814000b0301540c2c074208030f10000420541c4541c1e5103c400a603480300c1402240c00c0207500e110106000d200400d21802d110740059030782e000b554001010040a081c0304001c01c20a0801c90450703e5026211425a09102e4241194840e8464030070001038644000100d40d07182c140102812294091714000032201c91000e10a401440241195000b08001c0c8042100041e856001e00086000761a440038171420003101d88283c400192242100c1d034100308240071195103110b00401101c0d404240d03051403640d022100c074241541a2025405405803020002d4115090381100724811405c1718100000d0103c0c1040003900c0c0303101082c501d02154000c5020002518400700e684017a60b503c40e0034a80c8014840000700b0a502071120040010400300d010005540c0401c40c06070403c540c10040c0503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 256001501 1250 256000251 256000267
    0x20102040906050f09061c0602040e090c100503010b07051204120c090903120b030f060a0b04060b0c15060a121a2a0307031e0b030c0d0c12060f0e06070e06 68
    0x40043c0080c040b5481a00307c0b035403142860340c040310500421a03104038199102e5079a04456041c1020448141599000d8080d0780b00551400d20b2510101c0c0100f80c40d0242542d081074188040c903004107100712600e101d010078908070381e1008000361005001168110403480d210345029040e00b071503070703008a4080707040c0700700080040d41008940070801800880000c540005c0030003e03141c11000400c18041e401080144074110003150001c0e4241c0c0029201817104568482c0c0101032407180d2903126443c0d030425002043c0f4902040b2005400500080a0030354181d100c03201242c440784200811102d084610300300f2412a070f01014001d6009644410481d03058140d0341c0c000d03420f0044140301640e0400c000000814250007079100c2e000100000186401940c104412003008100c0441007621a1154620b00304032031800c44024035038690700020003900145041c03601d1801030004441254402d488007041c8118000500c03400000c0380c2880d009001d0f03401c140401030036400b07402c2070840c081c560410000d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 256002751 1250 256001501 256001509
    0x5060a061502100b0402090d0c0e0705090303070f050f10061d070c030807021908030405100b1e0f060c0d030507050f0a081003120c110603040201091e0f06020102040906050f 76
    0x11000a241000403d13a200840c0008000b48203a1501071b61142d40c1e0146241400080310260056400c05040c121081e11264003e643c9400f1b09554954140d1080103041c0020340d002c920703080a544140100e1f9240340c0528080ea040a01d4048540120f5076140c40c10004070200d101d601c641c429030000070300d809040081c1c0c010301c0300c90310304400740c180841080401e650300c0c0308005000c4141d481c1c91084580c4206031405240941c825181950144a00340ca2103180002612524090200003000000c080c1c2c0e208150b1101d018141c0110fa0b071000e004030303500c4d10b81d032107400c02840c254030910042c01f001075160a01400b01c42003d08030004120003070290700c1c0307041c186900703c40c008060b50611000680e105c00c4907010b5040c0302d030030040c000b001000d1100300b0700d07400841c00400b02d403042d0b0030840111090021b12803140404c840c0a400500c0c208001c0016000d0507655100ca480402100c003440d58a42d400028800f5441e4008070051798001001c000020b16407056101410048605042890b241800a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 256004001 1250 256002751 256002763
    0x10080411010c02100305100b0a12050604022803020d140f16080a020d09080c07030506010b07050a030c02011e08070215041106030601053009012306040e070305060a061502 75
    0x40c00c00d040e665000305940f010320087e000001c0000b03d00c0142c7e5070034004c41c0107048014910b42c9000d540d0030203010415604c2c150099607104d1001840c4090000844201d60300f08511080140007803550800030402040360b98000d01501c5210004001d4090406041e1584110030007824640007021f10302c0c0c503d2540340c0c40440d09030031200c82080541c413103011000c00070081155130341c02030107010000343c1e802030311401003170410450780a2001e0701c1440c1e07600d072050b501a118285001780580c00a00d41440020301503880d10307100a0041c98180d4070880180c4804000a90b1461000c0209400700204446103604005a00f40f0004a01c50440c16060540d120422010703c1445039204a03004800500940d10400940e420a40080c9039081c070f01898600f00d08010048510110450040340d00150241c2014094030f00420310010b000710400c03424803050000400060070790380c2d001d074680f01c200d00c801c0010012807004d1805140900082d040c010300c1c8504482565200240040c0202c00040030540c0204003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 256005251 1250 256004001 256004029
    0x1061d031f020310120f031e02072903040f11010e011d0d0503040303080105041d030304060c09050301020414120c15220905060a1e03020d060b10080411010c02 70
    0x5a100e8480a00d1645134007000d800c0100c0d0300e0340c9009003000384403004180071451070103525000035a1110008550440400d05081400b42e4001c140800c50b44c99240070720191078400031150040c4030b0030602d00f440c0301e0384140d40c2a2100c600051030341c0240701e5940b4900c2d048000c2401c107001c00603110740005c1c01c0269042d0500c2100768080e41801816111100600141a40182980e640310b80743c1c174010709950743c02e02031b190095281400450194092415100b00007601034000c500316a036540e9114040c052103c10034040094994000405860034000b800207080c680e841c9a0200c3c41e058188001400341e0114203025500114030b41c107141d1540d580344415260b11a00c8191f4079142581c40403040099182190016001c0680000f050480f81d030000d8003030b040445481680350f0382c0b445610030103100003840301c030385ca1034040c1d003080141351080d040a0560310980c800729018041c2e40000d00a071140c440440040b80e105810003003008415180d9a05000c4242028603070040541c011650b08520500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 256006501 1250 256005251 256005313
    0x30e01030e07230f0d0b0117061902030907030203030d021e040b0702060714030d05041a0106020d05091309030507030909110403020d060b10180e13030c02120601061d03 74
    0x384016403125002d08098074400750985c0341e485114500702a24120903c00e02d400070f06408030040000b0004100603000e5407030410010149010a80e810f00254406840c01140d80300e030001c0080183c6041c40500840146051b0040c0c84002c0c15030000030201da040080c0e060a20f0401003400101e40346425110300903010703280700b43c40703010a181c842c03035251042400e11203620000c548003078a1402138000510885c0701d6107146201c0300c4200b220310021042805030b800980c00042012102c0762148000c0c1848501c002d1000804070b680720003403800c840c5514000c0c0c0002d00c00084601c185a046403004000300a00e031000c01484001251f9044140503e00000f8070609154000d1014404d10350002e48444000900b2601d5040203402e0240c0210300302d031404c0c1c0b142042d10f08000713888005142d335184a04031840040542c0003c40d038040b50002054901242c1c4039280200041e40038404100d20740c080d0049480d00503054102c0e144101604c420768101601c207500c17400c010b01c2007000c02400301e100b03502040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 256007751 1250 256006501 256006559
    0x6011805060112020705060106031109010210270b1503150a090c08012c0708120a03150906060905040c020c010c0c05040905031b01090c03080f040e04030e01030e07 72
    0x1d8012210b0500910760300b07660600121300007052000c040354090490384191000c11080300810142005030184601c198096001020441c003108825001032008100c0f00c0700c005a0000700b054420014140c0321402d81d0020000810070819084114013214280e07000c4000b000482e0308901e00a6500c0c2c40288020121511080500100709000202c0c00250150000a0160003448141c0f0601c2554803c110100001e035200320202a43c00031070404142d07203140c00036040c02c89407d19088031941c4008000c0b030806a0390483d0b0050b0b15808800040540860140418620f1800e14002c000c105950400391042d8a840007001c041030300015450f5045400782803032100c1d1501e50502400c1c086440d8442604181001120000c0041c04401000c1c101d418510f004200c104440e101d500300c0e00d4801000304100c40c40042880400c6240c4003410907110a40c1c40079180949034502170321840c1c42513030202e010607054103c0c0301c540d41e0540500807001821034020710030039180c040c01920780c1a28500c1c4100314404c20b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 256009001 1250 256007751 256007761
    0xf15150f05040f0e0601031116083007080702070b0307110a08160213090c1208040305071206140f0114030f060f0105090a0902010c0b061906050a1106011805 69
    0x510650b4002d21514003000314450390341d00c01400b031140464100b40020f2400800d00c4480d09500160342c0f04800a82000c0071403aa181e6404900d68402c840e0910080842030510b0302d000c0c58220001c4c0f80700c40c42d04101e13881d410a000050004030000e0200e500b5074210b10b006000425040c41620f610a003d4038002c00c02034001c403125810300788001c1300500503110004050307200e000000c12905143c1d05c04d440c0070903a0070f0801e800700304444901c41c0c000c10880b0403540401829050107544058a4000d00003180780a0f078a81c1c0d500d1030300040750f0102c03007482d02c860002418003426118604030700c0d807648913a21440c0380c1070466140354001405000c901c80c11414100d003050b10700700400741c00c058000c421203546081112030203003c20780c2441400c1c450540704000641e5144036002e08002c0d20740c107841c2c1c61031705103c65907800b002e003d008010580080150001c0704903004007140581c014103280c3c907081c1e55804c1c1e0450090143c00001c94802140d484440104440741c80d5446450700480e28050005040d211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 256010251 1250 256009001 256009007
    0x1d060d0b070c02090403090510090806041b08030d060302040b10090501080a022a0712260f070b0907080a0b010302130b0d0809040b0d031d031c030f15150f 68
    0x2401c1030213900300700d41d00d08000c100741d0400d08180a4a0f000c880d4002d1801101000b210810381c54007a032181c0c0d0b08084042030000d010304028010519940c80408001619008080e1943c1c000d410b42c6040b854640d01c041065091511480c646140d094803480c40c200d020382030160035010540b244a04000720740d00001c503408101c1c9d040c0c9210380c07001c50803454548441e035604136002d080200c0211650250700800640d203103c1072409000300340d00c880184414175000c0c0241006035408550704130717412020025600c4c2840c1a0b00102006441040c0400080c01c0400d43e45140a0554110000c1e07a0701442c01000414000a81241100c0e411210300c50b0b81c19036049500c010307080c100031803078215501031001420880035001800ca1042d00762800c01c2500e007000104038181540b8038000d00890101420090442054400d01091000103400c968100030320703c2500c0d40024028500c02c0020380e440c104220a071341c060103510300209000008549840c1000d002a41c4040603244030014031085014004603d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 256011501 1250 256010251 256010267
    0x90d050c060c1b04090512070201052104110f031002180409080705060c041211030a080412020a080c0105220b0313030305061203090409060f09050102041d060d0b07 72
    0x900074004644440041d09050703503035200c850000b001c06081e44418405420603102d20402203802c54000c2c200140e84401901c00d99100950076030420408000990b80c001c0c0d18900b2901e480f03c4461184494030303090422100c01900007103958814020b180031807510759400035030703809404010440181c1c0c1c0c440f21080c3c42800c4582e0320f1030313503049030400c0c554100b0701c5185d8014290050203a81980c545689000c0c0440b564070850241d118880d0406108001161080d4060101c049001d42103035030760034058a440130f45030042d07408131880282e580819811414000c2d4808003d01c8548024610342c20002c0001c1d00c5402041e0b00101941401201840c41c031141a2084006060000c00160f503800d242d400d84515030404e00059010030b00741f40200d003517406c1503004140d144011001460801020804000c050001c2c00810340301d41c0d480719149404200184200c4032007610600c001a0342d9031622003080d1030701c81c40e2000b014204a041003040041e84880295010701a17000303040d22039942d140402600c5003e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 256012751 1250 256011501 256011523
    0x1a041a0406060905090a060806070e0315090c0f01020c06040501140d05070e010e0d0f230304080708060f1003021909050a0f0506060906120705070503120106030501060302030103020303090d05 84
    0x19040140000b412a08008000d00303481080d10700800355610241c130b000903034410703205080311980301a0025450038490b5400980c3c00c10001c003502d0310143c07502c017150a001c00580d0081050f4200070f07a14000380c60214005a94140280060000c110390280050024011071146605012034890001c0441890408560146076442d9041005080c030200040460780b44140342c0380800c20640080b0f4881c90081d0381203082642c8060300400310320280c1d40380141074240d05500d20030303129a000401a4580f00340083d0014160900c02840454600340c00340d49030400107403121184240c0c2c20300340b0500300b580040200541e50151441001306e000d40e1891285002642e02001066142505100050f80d040e040f2104c010310394002800280c40301420400144140c0b800c0641c03100c02040075400b0500030009959105a0310308140382400d070a51241815039000b12640c204113a6010014810582c05210ba68050b100d20300d005c41c11503046a012968030700c40d00300c15a2054407001c41c400100b142c10000d1003422 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 256014001 1250 256012751 256012759
    0x7270504020d051014011406090d03021e0a05071703180f060d14061c060e010e1501030c060203090d08311d04020306040f031e0806131a041a 62
    0x140da40c020010090111158802242c00c20000014508000d41f0400e202c00782d004000600d00443d00080084550400ea8118154000d11881c030007210202d250769144414600013420581015261640c20000c042c1c12003801c80d907030902d501840d80800415503440001028182d001e8009200000ea00302201920b12544001e0000b0030a0341940f4580000c50802c040e2802565152100800c1105819090f2400304210300d03100001c81c003081c015048892030032050000007880714100002c203401c0c0a03107004002224842c0d00e00400802654007010780040500c0d102460429040d0380c000380c6400d0600001a00414002c21500540c02840003050030025000da81c0d1081e0031f1901c031405822014520500301001c0094290300c1c02004110074103880380c0c2d4000c000d45450b42e0340d81d035103000402183c542075080081d104465403104480c2404054407002d29100c0b24258a4890100000c05038108408207001d81811a504a401d800701d000042400d004c49011542c0301c07040705c3c940051344002c1ca4440e40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 256015251 1250 256014001 256014013
    0x31510050d151104090c02060108060c0d0906090803060109090501080616030f1e06092a0504030f03021c020307150b190905041b0e06062b0e07270504020d05 69
    0x941143c400144111348025409024004200c0c000f41d07120790091140c101150001c40000300b01040c0c00b402030104c140d1050f400101e00410740c840000710f6000c800b044a5600d000818041c1070768006038640010407800b0b00138402981407219441e1910805805158101c1440b51000c5a490003a008458541444c0b0410001d07103945241c24840e20400c044c40c14141c82c60a00f02189041070341c02181e424080d681003410004850107007403070846200c0d000190403c40d0601012000481e0000e603240c4080c041c1d401091040c000c5c290411241e4440307004841554030030800c41000078002c114800022082c1040003039503032802c0300070492440c80038156001c1032010203c0854003e2140c1d0025004900a6155049920f941400104600c40c54019002d12500980c0000c80c10700e440760007008551012540b015442d003103c3c2010340345103900551000d02548600c039603800e0940070000040100100c48413030480401d12030155501c0b0710125980420240c80d040060700350b4881000c0d24410030762000031508 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 256016501 1250 256015251 256015271
    0x80c0a2f01051017150c0702030a0507090209090a05010315050402030c210c040213090510092c1c030b03030c0303040b010f1d06010309140d0e031510050d15 69
    0xc1003c042c059078103c0458246400d410110010b110061310320740c422055116150600030032800d80040400301d1b494402ca06540c400110280702140050002d1600580c461281700104042c0240090801102e140f90200400203c1d08004101070044551f08000a0982304d50010905208520711000d0300600d81c2c284010700d041c205103a503010710202500740e810044800003040300380e10903011001d801048140301409076555950000d500010302d03041c01070343c040d901d858003000c0d01c0030307448840f004c5e00010024880d5000c217100c404005008000242168902c0c4000c00041d00703050000c401c0c01c0503521811283c05403010011100e90f1818078003180d4481c80c0134034100241c400f09000e1714440b04103103100040c520324000708415458800d204110354a90ba00b03001180100f0780d0b50400e0f00c1140c400781c146c12043d14284054081505107640d4a11404a420306051074102081c2c219984031b040b1104102c2c2848a800c1028255141120013040807d060b06101440600001440c640c513460440104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 256017751 1250 256016501 256016521
    0x8040303122d0f050702061b090d080912010603020a1e03020303071211030301051509031603140111070203060610111605010e0910052101050405030307080c0a2f0105 73
    0xd0700a02c804882802161642c14040d002d840b000e40d1036401607446071000ca01c0f250105001102880340340c20b0201d060116840c0021247d910490064800c0b0fa8002024450b600b84602407440c60a0620028030090346154045511130060b445202c8110700d01c0b050503003080040c800480000c0da0014112611084a8209185010004920a0081184d1075500701c0c04140100503a8100d5400501115541101c7e0380b0965090740305464030781e0f150181c4200d00200307c440140020284d8001c1c070000308900300c0c40445908440d860144420b6100c1e00340318400c0140d900044903984454181d43c22114035000c280203503a030945200e200b400601440e078282841c0e401010595046503401d036519550f9544020903c0116502512629a624103414007401103082280c01812034460712120400d40c40180c2411900b1240141c070f080392290000010311591a40c800b0083d6041025041102e16060f503060340540f64070780300b604100c4c00010700c14400d800304103110880305030881c21400a2100d40b07000d039415 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 256019001 1250 256017751 256017821
    0x1021005010f0e07090b0f1605060712110c28150f0b0909030d05060a0b0f131d0a0906060f030f120306060c030c0f080f04030303060608040804030312 66
    0x21481d00c1e400040d0310900c9089605d0880e00080c1390a8a4600801340f1540c0d540d00040d4252000764180c200800018010051144221400d5644003000f0001144141c141e6460b04900d00740308105101c0d1f00c07061000402c4d20828007609610000000400200b00100c0341e41c40f010141180d403510692840c044d5030ba4122584e01600c540d02000150781040c100f0903058425030301d007006540103004409605ea0190700403500504024000c0444580e140e00d013210982c840c2c1160000c45102041c85c5698000c100c8144014191140d015040440c0280d046505580000c19207100b49843e0385060007845004d0780040c024082030f4890300748042c0c49089c20109140c0031002200c0400c1d46060712804c4a100348a05019102c540e69088048841c0303031012180340050280039035141003400e01150000c0d180000808900d050701500302d442e9899401c028045540c0782c0e00c41d41c2440000820000043c003450115030a40354181000c448040e41054488000c100f03006500742c10400015203030b0119224502d47c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 256020251 1250 256019001 256019009
    0x51006060e010528110601050a06120903020c040e0c030f030307050f22030c06180b0a030e1c0903120504030b07030e0c0a180e0f0304030b0c0c19121b03050901021005010f 75
    0x81b650240d03658828818050088d10454001072030a49960b2401611500080540c5e0b005e807040760303807540c416400a01222001036410b202c9501c0502d51400a05090141c41c0d810030039a00910f04524001e5005400c5120f004034000000000045100102480c25882c0134410a00380700050802e03103074a0318820f0300f081030203244040b4140c941d08a6600c0d4038001480140c41b501c0c1841c41c204036820354181d019090320481107595000b6810007132456000c0140c203c2c6200e8065807403981e16480e500b0440c0603038400010780c8080281c1044140082030048181a4104086140008283d160409441c0c107107561020020b50151115000007508409a15880460044041c0400007140c400c40084d41c0c1d48003401c1c03d4a104c0d04203000c1080427440010302580d101500c0c10700b4529004001060504000d81c4041161010039038900110900c2181400e650381c00481e4181a001e81e0752290300201e0071284030600404002c00010b1040303440c0d1090101c40c00c55407031020180301558640421400514840c02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 256021501 1250 256020251 256020253
    0x603240a0621080c030f031014010215040b0c12071715090615090907050d1a0108040b0c040b0d060305190812060411030112051006060e01052811 64
    0x2000b242d400c20308088150018280c4030000029000780c2e40d40010368100ca524041280014440c0c0681c008020380250b2142d5040b440c1c0311603090425600620103094603211504650003400750202c0b07900b560b1282038105810a28070701c0d11740da4900b80329145110b00c007a208801c02403581408407030380d0419000080805d008003003c14503075964070510947c0e04208d190303561154041e00401e0503030603c510140840d00000325103a02d031074042004070302482003d071038a80c0020000220019040000e210351203a0060b8020741d0300f403030392400d40024800383d0003801c0a4000b52441c1c010580140262048800400300c80007081d844481c80b0740c2117001010b0500c020b8907180034841d0400030407084800b41c031650940c410800c90909125444d81c11410b8401044650403076603031503e2aa031440b40714041c6000b031181c0c130b4000f1504800b071300e042c5080942c01080303905414103000c0300b4480150441c01009402a00303280064852038180c4103092100b0740c0b22140101ca402c403003200b044a55010174100f50f0108004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 256022751 1250 256021501 256021511
    0x10b25060516020d0c1b08070303021b040627091b0e0903030c040b0c07030f08070624120213090c0f14090604090302101518020309060f0603240a 64
    0x1000698035407040c01c84c0c100016040c4102d54000176100c9141814684810b045960315a845030403080c5030000315003050380503030f02807000c00703014100c401400c0e140f201c0140c4041c48490300d05526403000181c0c00b8440906070707072884090b080120003940410440764001604010700b0f0b6020012440b940c1d0213002d5403041c0a1403200003a2084000401c03240100c80c4203110b913181c2450551201010b4000099a800074080d00c600003000c6a0300000203482c890050144030b54078421407829000f1160003500880c0300e4080f030210703100300b60701d03e48404040742c0c0f20038090f04040c10340303100044900500c160304007030241c68007183c2c0050180c44943c0700d00707880340365074009a295151840b600f41003603070110301c1da4070002e13050000f85141007a401c0500071520a0044900350074000d2140c5041d80c40d030341e40f503411070f0003415400c10012180c907001e004042c03174428046180d0300705010b4068850314002d010700d00350207110700800c0603510204001780c0c03520612006401c0402a8240304103002c0415a03060306024188 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 256024001 1250 256022751 256022791
    0xa020706020102180d14060403020c040e0a0209010303140c060103060b090603070311060a0c080d090201120e07050603042f0906010e0d15060b160b100e010b250605 72
    0x52084400903202d10021036484d08801040082c0c81a0420003100d486400300550940c2c890f0401c50302d1f000e144a9006030000201000a000480c0d912103241e0300a58061007142000d46c072280150380c156070301450055041444046012928410b5441c2041d0511401d030001040c46190703070120006810803500310185071542400c15695134110b00004e403042e030390140149403600c0c01d003000b0b040340c000d1030504001c40004e03512540d1442e00201c025550054440c0390000456a000d0000c0c2c0e10b00340904810000c0d01030b14442280c1d12101ea00070b080c002e40b0000007150a2000f900d4000703129400c0c00c1c0c8e42d028030100c402d080752000d2003e41c032018000c8540e407020900d250b0140e07484e20b84a0f20301400041e0700010b02d4460041d4034410340c4103000c0480da14103001c03401442032802450141c0f8040201001c0303910521300045908401001415401402d040c03c4c00781548003c50581100c500039001030b26004d4075016080b400d41e101501e440d180f1000040030701040f42036007019214a88046182d40740c0601 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 256025251 1250 256024001 256024003
    0x11160b1e07080a030504110d06090308010519120204020d05010605072001080a05190516090b12040f030909050a1b031119110a030206090d0315030803090307170a02070602 75
    0x40d1400040c00750805121480c5114130a900040e84a0f00410a400203c1c4030308001c22010b0880074810364040d0740303070040d52003810340142141c3c0c01484140d500716110790403040c60070912011030240b040300600b820344480c03c1d56a26010348124101c41c5000b00602d580d901005082c076070211104440759010f2000d1040c40d0401001585d140001c180c6501c501540d1300391030314004110041082030f404a601d10150311030700417446081c1c41030348481c22103503014409070030240841d40355074480503400e0f1080199186680081c0c0c0c0268000da0b211040601c040034a250990b010040c1350040602d0500d40300c204040459203400241c507081c4044140310150352103480c224141d908004071244c174100304000e00ea0780b410360007a51400d0600c0e10702d03013002c0929040329100e0418490600603001640048240003880340144030030076444656040410135080366160300380c02e1440300c0c40064800c0c0070100000e002c51105004a681451340211803c0c40d444c0406c035030310401d82024440000501c50b4120101d134840c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 256026501 1250 256025251 256025257
    0x105070f030e0705010302030a20031f03020f0d05030d020a02030403020a09020c0705010e120111030703060f0e040f060615120c140f0307140a0306050114030f0711160b1e 75
    0x112501c06840c41c50b0034113005502a5101405203042c0c65603600ca42e000e401030001210744100f000c0c0c04004d580341001c0103054600850f60f1005200d45207641e40400040e0f9500d41d01a803c42820341d8001d02c0510f03241400b078154050303585420b55250000611440c0650701000820a070f1344211040d12045494940c000200d00400564443c258401701701808103600503d44200008801001d0070038402c00d0321852420365101e150301c15000d01c00842480300c5503402d8061440079181e0b86924000e1f00d841c110314500c0100c000f40c000307800c0c0c4451707150a0041c0700003a04504040c00300480c8441c0442031640740201541c4036450344c04283c92400038234604092080007031001800401d00c84a04003c0c449039840f005902c0901200240600040d4452302e80d00c5540c0984810022034400040c108d207444005403600f04106032604a40100700100150f08038040301c003c0d041000c51400b680850b0100ba125450104004c08040e40038402c1c070303030005110f80888024003c3d842d0300b210488104a4146500007070340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 256027751 1250 256026501 256026521
    0x106050304150f021603080a140c120705130b0a0201060608060d1424040c050906010804060b040b06130906050a060c02150405090c090306130c060e06040504020c0105070f03 76
    0xc00702015400c100110b68000b00d401156030074006191414882600d0110152428210003140c4602c2c02c000c0700d403440703104201001c1c00b60006090589459280d40c22240300c1c6000000007001442c02042c40c0340d208905640b20110b9009079400c0c0c82c0d80b2104480b1403030700241002001503003450b0020520741d20916695014860281c035000114003940d0381d022502c031042d40001d40910554600c1c00908007900c0410500c590341c0034003030159082c0f9003000e4a5030300f10350300414090ba0104040c0b10003a40c0c00310019a010750040d00015944aa41c40000d0181038a202d00c6030380a00c0104403046104580403800342120002b07142004260b82c1c4a05000d0461102e200740c10204510441580141c1031005c40a000090f154043c507190607151000196420b809079032030000f019000c584150a820308212a80d00326070704107030304280001c0a584007414031002d40101c40c01c004800f00741864540f44e400940300a0040107000395182d00c0198402c078000c1c04211180c5000512181043c2a854000d00c2028115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 256029001 1250 256027751 256027763
    0x1a030712030201112a06041101080a020d050109020a09082817030a0906180c14030a050f01051006090f21050d111209060d0b06091e090106050304 64
    0x80e10304801040140840401035003503540b140520090300341c035540244400d6009800c03402c1030b150800401011494292801100c0398418014400419004001102d00010900c2d080d500b5589160440010380141112451118108000410b0700c15450300508403a00c1c056440681351642c50f00b80560b00d00000054000980007824442c168050790301008020300d0041c00704a49000600700034003203a5004840c00648240d4401000c81040f000d406940e4864102c0c01c4020400046910b8081400b0098481c1103841035a10b05e42d5405a103003807100900b20303508601074139404040411054040c0c00100c034030309003a4031088804603000e0701507003091045c0ca07068140403d4071405c04030145079038444008800028001c01c00d0303980020b401009600d903503510700d80e5001700f1842c0c80002c03285840c411114107181032205002d03552068980c0025140c03296038600022616030000004511984211107045411034602040561a41204803464440030000e480c030440704c1c3e80e0303524100c2e103a001c02d881c02401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 256030251 1250 256029001 256029013
    0x70e060406081302041b020609071a0d0e01110d090209341b031205060a0524090d05031e03070801060f020c03060114090903040609121703040b09011a03 67
    0x342c2010b030307043d11940d0f01c05403000620240d9001810f0302aa8006035000050f800712040100d104014010340300200480d10340d1110140510203003131154061014150303040c0756a800e840714444002d402003d0b0140340e980c5580c3c0c2d1420b205003d0301c060700d10074509034005c00d006000b2800d12400890303106031030100c200011000b40001d610b100d6203100f039000070f10304212500074041038040300902e1124007039101392a0081d0041640030074606860009100c0e5200380e01042c4104419220071320110f1844190b031640707403100c00c0c102040018500900000c56000021806030204000c40000140b500101c05032025028610640d04200e580c8000c070750890004404100410100e80691402c0070300c1d80203030060b640000c0b4a1000f081c0fa01d4426070209401d09180e0491303026a0030205209900120324802440c5040c0c00c01c17002500741c1e1070521403074070700011105842081c0701c64012244416904036a038a0380d02d092502708540e58030400e603184601546003481a10231580a10301541d5102c0018002d40360f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 256031501 1250 256030251 256030261
    0x3180127060c02150a0f050705122107020a020604120c26060f04020d02090717040b0711030c0d11120d050a0f0203101809060f09140a0c091503020d0605070e06040608 73
    0x1f40701c3d00030740000c403070f036100c0d05c4001203c250041e0040d06001440c03000800090700144084400018050159020354000241d4240981c407140b00711011b8400c160814200304007140b401c0311060900d035102001e8100d0780c000d9890308840b900d8200d00041407400c1150215150f41c15210440b20066500a60206d00300c407803007005040c007481d1580d03c501d190900c16414425081210700f001012281101c5410f921400c0107416508940c54415101d411001982130000042202d40d075180b1500030361080c040744034284c02d698201001400050215029196102d03000242c0c108064a0700703507640038805090400006402c0040e10075603210701008440d00280074900a00c80d0740c00c503404861008151b40343d00e034010106500f405103000b0030032003d00c0051004000d00708a05e84001692044019800c9100108086840e007842c250903540000000944e1f080c43d0350701c09820308841d0703100035085100c4078001000c0c0111075002e0381c42a5120f84442801c2e041070b504000c001e200f6402801c000c562080b0201d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 256032751 1250 256031501 256031507
    0x210090b0f310305040504050a1d0a0203100e01060503030705030a0305014104060b07120503060d030e010903120f020706050f0a080606120c040305010c0203180127060c02150a0f 78
    0x40140c02404c040b468a502d8a0105041c1c9000f21b0b4200b849688404c456001010104c14204d0031600d1440507040760445a070009480708011345c10b0b0b050182d190b510030621850294403280c005c003c000e04503544d5100364a0182d4407070f040040800080b0349040d00000d184070325031900c20325015540c20801500040001358401e440307005000b640f14017000e403000c02c00e00d448501c14130b005001c54121441d11201c80e0301c1c0c00740b00603140e15166004c2000c14010300081e915011140784070030768142880001e00342c541c00101c1c0c03038010039070024041040546000541c6a04000c8100600b58103a098800305500ca00c015a4103104030740ca00115083c1c01c1007402805031003003541036000b04000b80701c149000381c10904030750704035030541ea40e28442000250400c03c000c4248160032807461240061410711000d014002c15500c00413890038184032026104800c0c424043c1003190343c401e4544000303043c040c3c56840042042c0d100b500100d0080c40158100c5003820416400d540d05035110f5950744c1102914941c00b1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 256034001 1250 256032751 256032841
    0x10050f040222050c070b13030c0215070b07080105100e0915030a1703100e0112080307020312070e0a090203190b01090306060915120506060f010210090b0f 68
    0x4820840c1075415502c020200e82d00425009070903000245440f46502d051014101c2000340516514004600c01100040d8110710840d455603011907002c8950342c082040c0300c59901c03600000900000ea24410020000d800801560607a0b505072181000d402d020813003942d010804080d040c1e4400f41610000350681140d00c08581d0a52018040d1200994196220b00001d00e036164004003e60707000c000c0100c400c0140c241c210003044040b42e107503040e51400b01981161980c000d0003601c071420002c00100c60741d0007081101c40500400342c41c0740a038608400000d05d15040f0380c0c130b15032144940034800a1014064000c5c1d901801c810402004501c845440600080650002e40c0781403004807100003000c40e0301407081400400311283e0201d040b02e019800200020b200c0d4210910410309103000102050340002c10990040c821303901d80301e05004400c0140c0c50080f031507611700d103c20f051203036840402105050890041c070204480c20340c1a22007424070520411010720800895441404c480107135201d072540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 256035251 1250 256034001 256034029
    0x14040203120901022b0e0114070303020d09020916080903070804050f24030a060501090305030a03050a0e0f0c120c030607050d0912020321010614090a120b040510050f0402 75
    0x40f1480d01c403501180e00003121000c1001c4178000210003d00780e0a41d0003006000c00c4180c00d00c0c1111080070b000110403518041d508028041603408a560003545407143e00124103250003e12245142c90038036031000e900014050142c0000d0290340204650882c004151122250300c0080c5070b0400d410b01c02030180e0464007100f100c1e80403585801041140080003900c808100e48150b40c036603a4170300442000281d0f07245038004d47c108a51484200b004c070b4008010360304003020078074001c100c6449140c022000342520b684160340d00d000c0e141c41c04034024000103c5481a48066905840e950519207a440d12071211b0100c0c681c150704403500081c80036200350020312000c0169140012031403a284c492a41d1000280107400169000141c00e0519403034002c441559810030403000703001903040c8000101000c0232100200c80041e404030701c43d10030307545800640010700000c10408442d400503003842400b02c0429901618140207000b4580b1100e0450f0141038807583c928105805a620707140d00740041c400c030703001c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 256036501 1250 256035251 256035253
    0x203220c03021804060b01050717030a06090606050d39031512020909070303020d03020d090209040809120d020703021011010c05041a25080c030d0f1404020312090102 73
    0x100c08070042c0d441c640344191142c0c440d81d841c003007840d00f03190100886d2800f20b5854140300040c040c420000b2010000300d040103c1d2001034645030b403210312824016000b00d820403107d0070305103400480c0e5140d000c00517203007004004800327010015503884d01f107080308000d0307856560565410038041307071130740c984900b034084200030385400185140001142c2d541030502d03812407803011680303c0c5038500b549010f62805401800322005801468615031703003c0d60302c40c0242c8801051507004034013243c10f402d0691080c1e96007600506058501d140a03d0500b043d81c1c803030325425100b0202141d181d5043d18000400b10000c40c0c65030001d043c603a095808000d495806030300d40e001000258541c05221403420300802c0344188158503a980c4650808400e4058110280c0c11203003403403028800803070082950b990300307a007070f400e0410983c0e40d882c0c1c0382c1400d42580c0301e01c811804051000003000c141e407104a83c003401540c1011181045880681c01d2995000c05003901c0c06585684521200070a2001d40d200811072040140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 256037751 1250 256036501 256036523
    0x904120c03180e01060e041a0405130f060e190f020402030402061c1d010b0a1412071205160503030d0b03030c070303021f0506010807030507140711040c03020322 71
    0x2082040000c032940c3c1040002052000040003001c0d00046420544c0504407024480d204041041500203980e4000d1544110b489801280030058024400c1c110a50000303450302801c1ca242c100040549008424190f462040041c242c450660303058280540b503a00030401a10b02c4034503000c0001940001d4400d0ba4000170803c80c40410ba003103022044091880c10101060340c01c0602d00001d0580814a0040091790501d2000c01d5a503a441640105407080d411507a81c40c00c602c04042410602080000389603403155a001068680072040e9000350188920212101c20440b1440c58400c02500e120310741d007581c024045000c05244c0c0f60003083c08034070702408aa081643c1c0d1900707185005400c0d441070300907030400d001c0d00101c180d041810501c51309029009000506203400000d0000740d00502c50001c144d40c0c0d002154155129010681400310140c0d220780d11401e0368106070301440c20306146036100f94078041400010034003d000b524071460587c2c6801003001c000d4850958510f612880031143c0711595 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 256039001 1250 256037751 256037777
    0x40b150a0216120308240607060504021003021e030405030c0102160b0c19050a02010b13060e13050705060307020c0a0308040e0f090d0c06060f170706170406271407050904120c03 78
    0x87c040d111250062401048600745030040c0007040e065002c0c0041007500400041c50000788007048a0024007032415115030b00d55036070601a08501a801e514586940001040400a41c50804280142d4060100e1001c10b4941412909403132080309410420f140d403403845d0998044c0a00c0103021a2025800003040c071255420005140c0501941c3c10401e040da030744000d001a8000905040d8080704a0382000e2140c003107511140da690328184611841001c0002c0042d21061080c0280038100c00058080d8411a44034508040c09030018018400f4100e801c000180c4004500034205004210010203004412042d0348100c40a0500200c1500d0441c0caa0702d00040e000c03826007900004004082000d06210717212a592420201c40d60f208404010b00301c0701819545030588035040d08581c0c8100d000503010301c00010041010100f041e03120b819810785050400b445080619101543c0a04098410903a00c42c4100300f001201a42c01410352140c840c40d804100380200d1000d0341943c000c0c1419200c944c54 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 256040251 1250 256039001 256039009
    0x30b1e0f04050f06010305030307030f110f13030503030a091a0f0613020c030c07050103180305040e1302060a020d1e0e12120c0a030806040b0f040b150a021612030824 73
    0x4280d10447e8250310010410400b140e040c400c3c109800d1215209000c8401c5142406420f0f004400802205540004036040610840c0c402c21380116405810f80b40c0301c0c984080035100502c6103030025211141c0146000794580d0300f008a00b489100d5981240440b62240414003420040306000d18803503581c2003007440403c0300c003007003d441c000039202c005003503550038100010141c4440601024811a00a80c12030000e5044030a803001c1d034000c1c0510481c2e6a64a07a4056245541034601a4001600080d100f4000b50f000c0b44544814540380c540003020840d4151107072150030040441800030301c145c501e5100d2403030004100076091030000220782c04101c03000000b2025030310441c20490b0380e501014480d800c158005000c10b40c46039045504004440003803010414401c0c043c070720725214a55905080700030343d0f50b204000101c07080342400217446440d0680003039502c1040304c150720507034985140d00064214800303049041555060b0f4031074580c0d841e1329107041c84140304640c242115280745e004400058071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 256041501 1250 256040251 256040263
    0xc0301060311330703020a120302130807080d0810030b130b0a0b01140903011104120b0a0b18100b070c031209140607050304030c03060204030b1e0f04050f 68
    0x20041204404503200c0300c04006200c0038103c240c2c610000c0607088030680d46660107442519415501c561550707500240b800f01d04100c0c07042001401c1c0c10711070100400300c6074542d003d8290009081c5580c5050342d10303001002d654144510031001140d000d4118180301c14481c0d04020341180c400e10b050000c00f9120303500e00c00091011a120000e40011030b0503001808007c5140c150000081c401c100220a91480000c0c000d4111b80078140800c800051800c4c00d0342c4007540062101c0000003081c0352a15143c030000040001b41010a443d190740110105030010960712030f000000100400307010020b5940c0c0d211120307102000300141c10240107000c2c00a0030311751020040c142c2d41e20a240c4c02030224107516004035405401c04120301040355840c41481903c80d4400a0b0410030411202d290b100d22417480e205243d4815500010046c18080000000b0800c81d900548282c034031802000d400ca59a00415840208456110f510ba011000f004100c08042603c0001c1d00b10340140180d8004444001246240c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 256042751 1250 256041501 256041503
    0x3060703021e09010f0813062c010b0a0509040203160605070b0106020f0a03050d06050604090903111908070201030f020a0806030706050f0f3403020c090f04140c03010603 75
    0x650001140d284a150340c516100529080c49502d504000300440024074a1020400c05010f10514401141d96003c551a140a0140d4000d000340451581c40f00c0070500300c46800c080c0320713101109400203041c0c0c070702c1030044115494000e0306100c1024680310800c00e1500d40500b0a80e0140a02040103d80b8000d60403a10090310040c0c8405036510744500d44090a900141e1100c011500710307415403030710a01c000c11031060b1150180b4149441d078140300b808000528003948210750250303000400203038511300c3e5005a10300030b0107603e51a03980d2001031001510303071500c0940000e0410484030500c000820380005842003d0040c0b400284801c00d0605803c100c3e03100c1003110000c9510760041003010b04d010020a40903010358035101c2d050000d85452a030302c3c2c0c00b80005102522a02207a0603001d580381d04200042c0d43c442c81c00c0800000c3c10b60804000f070020001c41980140106600c0d42103c0c2002d81c5c0c0c1c00d0194105009068080d40e91741c65840c2034401401d06003d241c018201c1c2c0042e596402d0107410059 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 256044001 1250 256042751 256042757
    0x3030905030a09031a13030804060b120f0106150c14010f060b070b090304142b0c03060c030515041a09191d0a0308040804030807080a03050702070305030a0c0201030b030607 76
    0x550643c281304c5c1c030b00c800184166012055040400070648080ca580754401d55040c14000c07055141d034038040d809070080c01d00c03403a000340e20404000301c10000014280700007900100200044c0340c41d190300c0e0801d0015070b00714102040a491900c400660f00b20681114444050000240d10017075800c07040598481c0e074010840110f000c00d54000b40b05203c4030180e0064a03803401140342c00e103445000101038801c242c1140c401c04101540c81c03602c900e41481e040c80107201c04402589820a07182c650201c0b0001c1c0419a030182c85c0100c01c0307c0950003481000d001d18150000300d9a184d40744070400024140702c554415201a81542c0d180003611080b0010b070107503020410080a0f080604801421101c800c01c4242828215401910040801050b03c02c1c44540514140b001541c031410249070a10442c3d00080040000060690620030600301424005000b582c01380000c0c0c4441808036502c00d003a01010307003143c01c1040300b0f2001d240184096580346106040c08a50440842c0010303003840c00c201c4040001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 256045251 1250 256044001 256044017
    0x30f0301050f18011a07141e060601050906072a050420030c090a1a0403021503040b01090209031212010312090b1c0905010c020d0207060c03170403030905030a 70
    0x20368545607a14011000c01580d003030181d080300303c1c40324054840610500d140030b01212404110b403004d000450f8400d580006414404400342e06016a50318950385821003c612031016540501c40041002ca001e800c05035034603420121400100900e82e441040b08450812100e4006003a810f00c40148202502d500c5401ea40702c2440c080901003903039002548080d000c02401d824440410038081680c0c0c01c16529051103840b50070500114910701041c0d0004c544040c000075030805440310203c014000d4034400c2d1401d2a50020910060149000907503009207085c07007040043c45503890179400742101c28030081c00c0ba9270511001c8203180d8aa80800752041111000301e0050040c0404a030000400004038a41020700c070b803503c40305001c2c03030144501c031f05191004200004038081058101d1540550494000c1010204601c1c2c040e46d16018040c800c0c002d801004e5000500d98001c2d510908020f4241d242c0d040b038407181100c0d01c0c20364440244110b0500d0b40d0743d1510380c04180c00704082d207417200703664845001e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 256046501 1250 256045251 256045259
    0x50f0604060c020c0105180d0219030c050603040803040f060b06130f0b03090a03050c0c0411090109051219050a0b0f0f010b1c02090411210901020307140705030408030f0301 76
    0xc141c0c1c080b000da202c150f60000c3da641c0e0b103a0740d2010032512580b5240c00185049140c500001b1001c268400002c1e5110400101d811400c80611601c001203074400c07018180081d0340c0d001406510b020403600641030320b00034400100864890810400024864040098651000000901d0b6a084000000503101c80000c00f172006440809090380989035403c0d2040c154075046c14080d54681207c50000d04011000c51b00400e804820042c010305424018010310aa40e440c28242005400050016000031010540050903040407810b007045041c51501420701d43c640c1c1400c010000c144460100c5603441149a198042160244001d008203881d80c1005524203210043e1072442c201070700051000b040402081e90240380c90190962000c4c40300c0c0c8056155001140064010701444c9280c10b0105400910802941c0c0c040f5406000d850f85043c5a20381602c5a0044900702c3c0412568840800c0b03a44911800b02200380015040041c40703081140d1500741c80b009000c2c255000300505680b50100840180 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 256047751 1250 256046501 256046513
    0x703150c0e09040503090d030509060403080702100918021e12060306010b0408030406110a020307080102091912020919021201030c0509040c0501121401030809040608030301080a030318050f0604 85
    0x25030071408640001d03160915480703842c4c4034130800603124465030074030182004047c0500144d07491181d00925150310b443d602c0c201005582d20203030b000c910981246c0725019000b4000c014030400e0307443c0541e0b941c00301e10411800000942c4002c41072400b104012030350044844e1600b00030b00f04c2000444480c151401d1880604d0324160041c0c00056600d402440188810301e400015102102e07001d19040701c0360f000e42c02d851810204882e46c0a0340501130038502254607c015001011341d41da040d2817140c5040105048622403542a0003507071110044041041e01603d40552603d03042190a00e07035078610a0320320000001c83e88401068007010106100410070b004441b01004000d2a064030940a01e2a05554124101611f4012213040c4020190009038603c15a807155448050007412004156100d0a02c00d00e41d8001d031304410700c0340b4200306000c10070301408010750b0b040702c0d940c0c002403810814a65058001d041c29558050300800004000030102e03070b040012682c0200039101030002c03424242010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 256049001 1250 256047751 256047767
    0x30a0f0e0304032a050303030a05010f060e010c060b01140309150109090f0b07140c070e06010504080709051f06050c01290d0213021b1903080114030703150c 69
    0x10030400e8005100c02c0021030300c55050540c41c41c0010b60041c10686139203141e10400c00c12a0010340d0180b0003c0704000e120b00603580220b058840707165542070200d80d21007080750030000310408180010740e135100d81700000703682d5000224032940505103044081840b21950815400c1254020b9450384548078042e03208005111860141004460034000841152940e54001d4808031009042442da0300016611a120364011a400201a00081d079900c08118620360781c1c1060340110803200140c140410b0740c644c050001c4400b03e070003200240540e18904200d00c4c00418000f04a0503070741d011018000581c0c20b5050211014240300d0300d8103525400323990315185c210f480810f102e191a040e000c040d94a03901c000c45080c0701860045071554450313030791071000c14810112085034006483c008110041d14080c40c0c808801004900303800c5910360105015402c220403c4054003402240a9400511180c42226030002c00c82e0005011507108541e01e40e6124450300703076154228021075680c0444214143e1207419 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 256050251 1250 256049001 256049021
    0x2f07060507091406031003050115030c1e150903051014060f0f0d06020c0105100e1e01141c050c0f09060312160b07090501141204081806030a0f 63
    0x30640c0c8a0401c01c1103020f075800541d0b210701c55030740400050403039001805580050355006001b840200c5a0300186003015400d40012a105891200081010310800251070200210b41c83c00480640c43e001e1400070008808030381c0c004100c1c1c907030f1010001c00c008124800d00c178041c00d4000078403441c4112400e420000041c040f42e00c60380034444400105e036611076400284c2d03201203a006c9940b0360b032881c1050081c403482d0300c00c000f994200b0042100301e41d40365a1040480d01c901000950703503640c3d013510b8426100540300e41d6541c1404100180409090340c0f43ca504807a0b000b401c030042541010740b003201462050803041310998020b040b10b0030303d0b04007a0543d403498482510b888625003042030010740c03500c2c0c0c1206000d0344131002054a00c20852005c0c841c0c0c00d52500b11819107514200154001c0102c0b4050082901203440c414400b00307006100c108907440c001e60b0290b5642c88d51115030301d41046038003807500c04000105440141c0841d44d00c900080d80515018140012146014100c4409842c14102 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 256051501 1250 256050251 256050257
    0xf1c170a0801062f070f0b040611060c040905070905090a0516090302090402040c031419050f01120b18011a120303100315020706060603050711010506030309042f07060507 75
    0x1800b07160502c1c201108121444c80c040e0310b181032025010461410507650300842d00315098810000e49801d40e0383c000d10542d00c1c503940310b6194a18801241da0307201010340d14151040801c0108000054040d0721180d005801494829510340d62840018034840c0300340d036040d4456550300305010030074018404051003008503003003c9021038034680024090078802000640101d0301c40f644044103611aa206100828860000c078640e41071506071310740d00e0041c14003813140ba00c1c80c0601041c1c0e0f40721030000716412100d0040304c001400106503503040c1c03054000340501c900c01440111a0f03440344001c2c0609070168242a2401041d00112420080140c0034840030500d1a0410000c0c001d444010060781c0d01502c0c0c121000d0b40c55003a002c50250000d2181c401d01501c0507242c00000b04003a03505421060103a880b603a295221403540341c210300d0072500117a03000c0e90702d58410482c0030500c0c105038100500424038034040755402c240482185803c03a030108a203012954001501e0420000644076070782d086681e900d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 256052751 1250 256051501 256051517
    0x20f070506101a040303050d0f0204120b010603050c0f09041d0a03080c07050613030e090a09060b0915120102090d05030310090e0a020409020f03010903030204090f0504020f1c170a080106 82
    0x103c0014034510030743c000601001800903c8a140d00307403a411a100d42c60100404550b550342da0525813408030841001264092100000003032100e210b405101d016880c0000000e10f41903101d54101c0b202c2d40520071464019480d401200700240c1100d40881b02070000384042d111411151400408504000701004402c43c424000b0310017190001860561181c1d40180c61031003a003507401c0566010724003c4549602a03256401c00000010b503400190076170f88070b01020b010362460f200401400203421100e202011103405030040003450021000050300743c0100005141101c220049240c142c416841503c4c1c1e5840002482203070103107020801c0040251075000c1001d141c0040b40e40341c0303445203440041d200c1c64031f510307416007075540b4001d000038600320090080000085918020f0040e400500c104102d05103032401d00e03140b0301d04a02840f44a584d0040000032a03802c610100002d522410129615002101c10402e001a40410030000d500c01d087d04055120480d1200041c0303412816000340301000000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 256054001 1250 256052751 256052789
    0x11401020705030114012612120106030b0102060c0306131a0108090303070c0f0212010c0f0906030b010806120c092404060b070f03021c0509030105010906060504030f020301020f07050610 82
    0x200e00c040c15240c8500101e00c00f01c081d4001d4503100c1f0816004480f10340510130f65011405000300081042860542c1d0008a580e03940e41c090301100d04000327000340580c00450000d2042000d4800079613101c0b81c010001c00c2e5510310114508100c50b030400ca0546440d00a04400c5274030741e040720201c0c4c6e00c1820400114503624101c1c6004080d007191400003011003540c010300b10115954610000f0301c000d45c0d80003c20001c40d88030030080c180d402c01004a40400c0a0340e5000c00c00c14424003606480f22010f840c3d6000c0e58454405000e181440c1c91b000000c1c6003e08031496000b9038030a1010390240500c86201c000c1460714000c0c029048040030740c2d251286140400c200720407074403503054520454010880380080c245504080e41030104c0e0f00064030003120903001d111a46900301c1d0240400e0642640200308a82e21902120102c51351030083c1c8000c02d4042c0020130000f1050743c902020544050b0025080c030761240c1c14116507401401040764150808070411002246043c861002000c40a04191042c1d001e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 256055251 1250 256054001 256054031
    0x7052104060b0d050d0c05030706020d0b130c140c01090602030403021f091e0c080601120c0b090f121906060914010b19030608060c0c0f0a0201090902210114010207050301 75
    0x100c080c5c010240525043c41c601482002d10954581c25000030b8255643c404440a12000b8080d0900b500c0c81004103801c0d41001000c0d62044507100921a1500f00440003200282c0d00d482d089048280c02a40d02c80941078002031480c00518003880c401d80041000c418071229181328180f000380c201350141e2800c10624042100741b40340d8039806460203440f07068507044d41444609105180c210a8003445000f000080c40040c0398120140b8600400c09051403036180c5a0307088161003003c1e0b030240d0022024504014034544600c06011aa01c0c9008540150654030341c6000c2d03c2d0303650102a540e244e030b0785000b00225119402504241d04504041407015810300000e184c9070b018965800301c032004a01c0740d0105050081e840200034141a800304e440510b0201c01c2d01b8890781c0050b0030b05409010740d070038071034587c14002280701c0c43d158161998030a09040907480d03070094008144105801104c55a20318900d2458140c2601a01c51607100710720001030080060310301051f540c03005010768904225462400030f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 256056501 1250 256055251 256055263
    0x607030e100f14090d0e060705070506162f060a170c130e1f0303082802030703140c09010e091512060a0501061106070807052104060b0d05 61
    0x70030000000b49000b90121540010600040e200c81407522103c01c0c030008190004120510003100e036500f034101c0d110b82080c4502d5004a0b0001043c90b402840c081c4005e10b8441c002d00051001c0350364100e0000c030079840c1c41d61711601e1019418101121030014200d80c903103241d14409050815244e00345062110a0001d18400d41508003518521000007c910318030241c0003118242c54186141c2c2c0001d584880f55420880401d42e1541404035101440315040003000341d0000803079130944c6800009030740ba004440402c92440e81e2080309840801d0486400707102c0344c0b000c0c5001c0c581079600042e1110110ba5088a101000b814a80c0d40e0401801b081170aa0b074440f4840c010000140d501c4509500c6031201102c088101e9480c42d54818486a41d130b880300e80001441c0c07485080c1c0e5a000344400e0360b8508080d1000d520307540fa88041500174400290800f8010400f0130f401520a02e00b5038600b4a03145102e00000034a01c02142d00400510284418000c030380c0961000003000b29400c109010456a0f5159100e07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 256057751 1250 256056501 256056523
    0x1a03090c0d143d0e0708031804050601050d020a02030d1418010203060d020f13090807120c02010503040609030e120d02070e060303040512031c0606031a0a05190306060b0c0607030e 79
    0x1031603805203e050040540001040221070b0040741d240c191200f56a603105e4000243c8400d20f0905150050b540c2d1410f4010a0700803941a100d031072400c80c4040000c0c019500c0ba482c40710030361204104108022041e80f04240740d07040c2c289814005420207940c0065104084450800c90368018000e104c22543d0f18010611050760444407080c40c006038a012079030350340c6400c940e07240310343c40c100a65003441b401c3c10007003a481c0e03c0ba910845510402c1d05054030741e0002000003030300054060001a00040c095845030000394024140020310450f031100041d048001150141d2042d08440d903103401581d01088580090070125500c400306190000c0070940d03900692041900c28800070001d213060180c00e00480300f500c1703103800480070608234115048026062504c40c420000c1d24000f80f02040c0801141d40416104001b804000c801f498141001800d001d4400d0911648540302c00000002e45180324240c0208940300703486403140b04000800381081c40050035201818140b51540607004004580c01c01d500c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 256059001 1250 256057751 256057843
    0x6040302062d010801090318060e010c02041b1d040e101e0e010b090f10090b040e010e07080c1804031b060c0e191a03090c0d14 56
    0xa00b2003040030300c07039200b07448108800340340c201c9001095122064105181c4035000761200d02d4001c01c168401285a43e0034811800010108807040742a50300ca4140b800c4a18002040442c84002c2044503038a0602c4040310003003c584003909003400341381504841500356104035410886504030b03d404a480c0c4520410f509040356941e00014040142d5400a143d91032251a0401c9002d526030f8116000f808503003a260310811071000002c2c81038581644180c03064080c5251010440d18190f4000d01510103600050381c86074803242c0031071894909100301b04100c88040300402c0a9482c25507030340e0030b2103210101c0341c1c02a01c601c1c14185c01c441c1c0361074500d130300968103142c40348821009081000001e81e29550090925052440509035a5807200c0d10724481142103800b00034244000c110b0b0810000b40384140c0c51444400c0600740c000c03a00700405503030701200e01800e40e490040a41c0c00149084a040c01c1207490042c19552084042420400d01002d591012540c0c401894030b41c1c0c1c0700f9105003c04000e4849 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 256060251 1250 256059001 256059031
    0x10f0b060f250b15031006050d060908041806140d020105030f04020a030206070f03020c01030204180e01020f03010308032509030f0f0b010815060a1d0a02071704030b090604030206 79
    0x14007402e040950701e01e07900b1288400603410200d01c000c551081d030302e1441d44a403040e00280000444648184001c9070780003040103400400a50303914001d801000010764091a0520000a0303d40c00c0a82c01d0b02d01110000002441c40d08004e02d80c0050100500c01d20b01500310380744044c0040c1d0300f100c200c0350001c0b01140071058680c1d892000452403200d941009401c9500440d0000c01c204420140c803c4041c0719400390340381201400011401c0703008600c6240188211050143d2a91030203911070036000c09020300240c0f400b68855031070801a48280c0c0122120302d000001c100c80600404210712030315800c810141a40503040500030120110fa010107400403184988040420038601c0781546a10390000402e402981c2d04c591041c0c9030360307501e218403c0c0c5d4107500c0001405490109400b0056520041c41c0d2104ca0100c099a803108a01c000d14016032542c2c20801c14012405214209603203141e00d940a80d07440d400c6150000310040040c040c1c11055100000b4040029004a03503254030100300406105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 256061501 1250 256060251 256060297
    0x3090b0d0603080a0e04050a0e060109021b12041a0924071a0a0e0a0210031d0a0c03030e040e2a040608011b090806060108040804030212010f0b060f 65
    0x4048540c0014100c0c42e000075100110b40d040070176040302d003a081303d0403c00c0703640e0020850152124030307010321b080f60054401404904000c1e030107001044000c0c005400280b20500d2445d00d00f0090f0744901d61002404901081040c8c101c074a41105050070f04003250800841c40b0215040007070070000f00e0040e030ba0801101e0704030752454003a01c40403500040b5482560528246283e50000300790b0f000000f1905000e070b10b9040c1d900024890050b140e000c0c0c061070110081c0b100403070007400014400d1816032882c418103141613000300a129140c40c020309a20480c9440c40c50080d29403046640018000e50410707004440600c8007103407501004005035050210441c854810035100440c042809501070325143c40030512030815804054181034080c0d00d0600340f001d110742600c000c5034a1241c2121580030800246155104100d03082c6c009114002c95403c103034481d40042c1c24826045c01c4244681e649036912050031005002d0074400000c1582e486103820704842d181c075024072a10005c03000c071002c6600b40107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 256062751 1250 256061501 256061527
    0x151b070305160203192117060f100201050106030c0804080915161a40060f020309070504060602030702040b120f0703110405010e0610110105010803090103110703090b 73
    0x40103603500070259140c0801002c40303807014181c146015070304a000b0013904000040c94021b10400700700d15458101c040301205850200c0400002d02042d001500030010202c140c540406000c04101250008078056052880c020112030340c000c0307c8420090406c00303110114580707408031102c1c0780b0141e40c80112000000b140c0c064a00c03401d040200c1c40c12080e0a04030610100d480c80140d502108000e8007182e85901480303020401c500c9005030312403140609010b014690345650380160000c0114800c440020070b45400045440c0c1061b020900f42d00007041060280c4c1c180329101c041c0c0b00c110340400003c0d05202d0002c0d41c0703014812000f40115518000c1e40166030b5100592403501c80c2e00004c030b64540100200c0140c40384180d100c00c0303815207081c0c00d00341d1541c40c2c2401194140e9003074420706a82503980f0b2003002422040d800d1030704140511039860b680300c2c40080c0200350290a03084021503880000b00c5c0010f0884181c0740a5110300d500034031080c2d002039408040d407400c641e20034003000c0e1105141b481030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 256064001 1250 256062751 256062787
    0x9021003091a07050c06010b030f010e0a0603020312040e06010908030307030e03091c03080c0304050a0f0305130e060a05010503101509080312180f0a15020d0e151b070305 75
    0x140141803212820421040e0744240208044035507101661082c7c1d9851a041d4543c3c0016540d550132410208014042840f942040380e034003140040022800e641d0300d0700843d00740314001c11041e405200001d402d00960400640c0c0d03a80250013882d110b040705140040080c5c683c00042d1480d0101529040700200d1014200140c0702a210014070708880383d0003201c0c22034003c0000000440200f07009c507001448140928042c2d030301c183d801c1005440480107580c0c450300d04016032041141404bc082c010010750f05d0b07405202c070000c2c2510110801d024100a810071010080c3e40d8040d070704100d800c01c04c2011001551201c40f040360105240800f000d10007000540b00b40c03810390490004c2d440082010241060341e00c01050240c0185198020026110000d450715911314a501441036480f80b02d0507000507052075040c60301c4805502005061648880090301030f200f131103400d1450740e841004003646209a42c140c003034101103c0c036418402441320300d0010300d02d03016168000e8180000412259074441c544468 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 256065251 1250 256064001 256064033
    0x918250207081002030a050106020a030c08091c0b0a050a110904270305300609071119020306130512070201020a0b0a0c11010e070909080910020f010f0902100309 71
    0x30380d5003020351a0b0500000303401c101d03282006c0030304050001407200c4c00400c12048158040c1e40c1d0074600315030360b02c545000e907004072081d60b0070411014000c445d41400201d6284121712840035002c2c0390270802c0300d000603544060030f190342c814607111401e100000c00c042210f000c11416070b030126604005071708051010000e042c00d00b04040c1e03000b88885c00c1581c45401003c04100d041d41d03412100d00390040d01007600c0e134100380f6840d56a0410300030034031520380b4840143d442034003440d11011120100d2007180c1060080010a08210360340040c41017189000e20400b6400f0b01034240018580700340d0b4a945503a0f1400907001c42980c4400070f05201564401d00102c000309410070011045802c108001800410307001c0c2c2c8400006412424840c051071041c000c1c168540010308c0140203280c1000116002448501d400b04e4100d602000030024035202e0340a1001411025005040008503000c0200d09503000540490252482d0404480c0181e9801c45160403c00d903510700087d200c181440d03e031030207820b6415 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 256066501 1250 256065251 256065253
    0x91503010216050105100f0e18030d0e120c030a05030705070b040308070e04110a03150e0709030308131a06030109060e031c0e0714190308091825020708 67
    0x710901e40e000e405032440714092040000704060350303800000e41d120725800e02403005087d5008504006180c5055109500010026800303c01040301002d920300e140d10000f40b400a5540b907044200605000340b203400c0c03c0c22040010f483c500400786015948030311400c3c02d000180500440411801c41c0310320309946060364480780e5100d41c2c0c00c1c18103010702068003c441c0131002540c01c00c21901c8c00d00b07060180c0400000c0e051449824009102010340150400001c40c124094180c1d4000441a808040c03640c040d481946854402a066040081c91030800070030740c40c094615107004030000380c83d4091082e0074043e449040145c0e6110303d40003d000d01000c0300040c240354184514010640f070040000d00c071503e4500b03010101001c1c1514000f0a455107624550103640000c7c00801280f140e00b1444060320b007008200503211200c40c04007090280417a04240d44a0401203404410b0781850741198191007010400c00f4000c7c034000380307540c01e070201c1d220703503a11f00c2d140d00da000309100c5000300881e03406070600c20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 256067751 1250 256066501 256066507
    0x3090a0519031509060b030f0607140c0303042006040305060406050a0603021e0103050a06050d0f030314070c02030c0d02030607110705100309050106170307030f050d02040816060503150915030102 86
    0xf51104024103c8240156401444c003201d08215140010b0008a40802d0101412590359038100603610001e40b9074103903810010030080303942c19a00a20003148114840d112240070125101104540c0303001c03110006006810400c07040c00494070004800e9403043d40100003203000c0d41c544100d03802804050380020741005400c88050b4601401c81a4848017205c2079804202d290355800d480d200350b0303c45200e80c0d82c00900744001ca0700441c2c4d074050345098486c0641000305591605c0442c0c11042c400440d103004c001150208440210b240501418441580c12100f032481ca0250382c000a85403034015002c4018090a682005da2300c10080c0003480041600406205114240c003d01a002e42943c050803119546000c50105480000101d68090f482d8543d0082d800c00c0c2050b5030039100c3d4410000c40209206090010880d0500e0354001803000d054440d0240ca4407102640354480240c03041d8000c034040c410f051040001c4145400c0450110300e904031001d02403501c600154100064005d07481c207070954000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 256069001 1250 256067751 256067783
    0x151403190f0b1509060a030b030102090d030807170f010e18030c0109031106041115090915100207140103090602040905131203020a0e010c020f030609011505010203090a051903 77
    0x661045881c18001c0c1c0f509030039040d85241840c0b00b40724009249900031005e21111804510a9000c05078944024000501d80140440020059080390004500280b40e400410203200d6220090403c0600c1400c215205400c055042c0007982c01c1c14060076003242d9142c00080d80d80055020704c0f000c4001c080055a0707071180700f030305240e019180e698010380104100024143c6a2070340011020704c196080301d40d020310518118104520481c0e102911a40c0200a00104c07009544244000e406250105c054400700b1456200b40214240032031a0041950000d540412500030240b00803850194246000a01c031500391404500078019a04099a014a41410042e91300381506640005d54024401c2c11044210040f044007070f0703c200c0882200049040928220380d50040c020144440d04c02030a01610441b04400b10345403081c01c4504125980d12846030002c01b249815404010345001e1010394a4100400040751162119206403809080b000424222007084c2880002c0995401804a41e225044d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 256070251 1250 256069001 256069031
    0x30727050106020d141804090215040e0106171e130816020f0a03120315091802130c0818010b1306061412060f2701080715140319 57
    0x440000000403078845421509201600003c0c0c03495043c0000c04000c890715011b050101500b20000c08903040010003610b1040340300b0f454041c0001d06000f00107170000e903260010050840010100340309852010ba0306100c2135203580711058451074040c820054481c0c4603443c110361521480702003d0003c44000c40c001112038002e03840d04400b0341c021101d010384000b8500401c0410005840028807800803058071034011130080c4c2000c420740030303002e0244654903560f2a155041c0c030f503055446004080421203175421032400c041c02c00410040c83c0030821140c4061540035000103405809504031541025040c03050103c00d4101400d846030184c40c007800710404400040141c500c5001d80303400700c0d100e181c600116550280070b680420382001c52440b03080e100e030401c0c011413441942c60b03550015164070355040340c030901201c0364041252800ca0300710190b242203501070600300c0e00d8104203581c0c80410240180154001420382040000c0c610180d5030383c0b03a0002c50861142102103100304503003030014456620304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 256071501 1250 256070251 256070263
    0x31b09060408150c040f09090507150503040b0f13030e03010209120303010e01061403070c020f0402030c0403060b040239070321020a03050a0513030b0a061502030903072705010602 79
    0x70221207009007a11356603180f84480c010b42c001c16000c05248031080110200c039800c2005941d01400548a24a0315038601c40b1031008036415510206900000740000c00030345001e00c0d58021090880740380c80b400c00115107420104c40a0000d4200702d40c000c80794069079020340c1104c80f040303401003214600d20001c40030640c494000340706000559a055000240311801611850010740c250741c2c01614541d1041810b4454091954050341c010300c021303900b00160b0301c0d10303c01540140203907015580c44519614005054070300c0c0d0a01c560089005210701110450801850900485001c03a074141c02030380d0f0b0070f494103804514120703031070984510100042070080c10b00b100101a04054030b80a0004040d41050f60303507452102c0c006000a40170031401c0d5603184660041c00b0018000483c0003441641c0b9282d103070030034806070b600c510f503659164001c2105241194000d82400c032940091405c01d030710140081d84415142c8138403152489840c400188074443c02c222548242035242c01048256106e042c025134900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 256072751 1250 256071501 256071523
    0xa09030212061b0a03090c08060a0614060409050910020414090114030c0907030b09010b0a02070e040b01090c090306020703030b030c3f0a03020307030f03020f031b09060408 76
    0x3281200169080080401c0c2c071449840011811020f000d402d4405414941c07040c1012001c16640301303105000628003184504c02400c625000300784604200510808485072580100c400c04400e06504846484017010340b0112443c603074002505903100040780c2d0034035111282e0030844902c0014041030280b403c5403c018240b4003030f1202d0b041e9a80359001c144445c1c0308050042d0345584540007816840c03800003021640300b8503e207008290110001c0200d40c0c644000e0300603281545003c19681e00b02075041141900074020310340c1e003aa050816132501c10400a040c001c003618103032124080201580115503040086500a1045561711040e04000b002420110115446030055000c0d4000d14540010700742d4103668040000c400c00544a0704003803441c841905c410305807091000c610f000128048c000b1001c160f0080d0042d6580d155140780c02800480c941024009052050204d0721811510700252507000d5886072442d1030101c20007041c4042400f6a11b042e681c02800040d01107001200031407013050031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 256074001 1250 256072751 256072759
    0x609030314071704050c030114011a030610031113060804021207050114070c030215030f0604150b0a0e13090203011103070c0308130804090b0f030a021012110a090302 73
    0x411911100d18181a809581c1940082da40c2c4050125007501283d860f07800c00e05c14000c4880031460140803900356445482c049032140890702c010001c400c200444040700d840c001c28803620314a41100082c910301601d070720a40400d940c0c2c149032201203c824003101c8990350404007505850b40e44020040c400380084504a00544440c001d5160f2000001100d005a850503110038545d248106406643c54000300410380d0100c19000001016032169800440c5103903120503d640d407458080c8181c0c4014074042c1180307020701e103002d0003240d50314406d010300c1c0123a8085c0c1d08415622050418101c56014444603a80d0703100500c0340005080c5403095000044107842074000340315442100c024000c180c082202c1e42804202401524000a48917002203584060304182410380d1807074544405005401540100000c140e8031118201c40d464060b101d00704401d0202c008148041d62640403e0581040d0b00f160010b01c00d06600b00e0080390510b030001c040ca1b0045500c45038031514031030401000e4911921060b409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 256075251 1250 256074001 256074011
    0x503040e061806030c040e01150801020a08150616051c0207060905030a0b0105090907030501020c0a020f0316030605070e06070609060b09010e070f031d0607080601050c0c090402061606090303 84
    0x20042c1005420b201e039100501070321524142c102030101900c00060710041a5503a1501c8460007513048058070060203000c0001070325103040c0d01014200c030340c024110b00d00507034030880360902070382d56001155892000e4554540880d44245080c1d03240c60310080541c0c200d42c070190b60341c82c10701e030340021310004031145030b9911804c2a946909260311003c5102011700710101038001446241043c2e00808e07001400381044401040d6641c81d00c0382240c00c25814004250040e40c034080035482c0c4414401c0400c0c0046029008420100107090040700c0c0911008203c2519040012003042c090784d000d400c0d410000d0b0442ea50350700507241c850010702903c081110b01900d42031082109003000e042d064160307042040080040e40b40c154042d101d00c1c112850382c104040d203801d15038020350b1802820302c104190380c8000340341c0d600344201c0c050141000140b825041000600c20f6085c494400614285109010703601040c01740c0325030020a140748100000200007010488540d820031015600000380c4501039601000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 256076501 1250 256075251 256075279
    0xb04091a040615080c12240402130605011715031905010615090b0c0705040e0607090b0306030d1b0822090207020a0e15030f0102071e03140a0c0503040e06 68
    0x5401c003480e019106466001d00001745503800c00e851540d00c06030491044640401514880d032940c0381003800c102000010714414801142001c180c254043c42003500140708642c01d0a0000f03020b001000c1c0b0503a880d190b600081050b0080340d172103c064424000c1c0580f1414400144200c1440d0074a90b0215001e42c6002d80000e4800484616001c80000aa60b0503461502d490f014200e240c1080051a140e0300625000140c01c0e926842402a04000c3c10082c000b1880c16480c0900381c2c0300540c1c4600076045e01081041444d0b0b401084401100740340d070400701c8880c4206e0b8400c050a8040400080250300c0000d90a0313440e0f144e06a00010f00240d5038642c601c225105c80e4600207a000d844402500b0106150060000d811640c1400307a20a050f011440d01c40340c2c40c0e200107441d0030700f15505004241d40c0050408240002c2458000c0f030b030801120151421201d40c6d900130010424080044007290700030070240e40c541d00c01d416210341160800100c5e51102d45850094921040075201c4902c83d13900340070010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 256077751 1250 256076501 256076531
    0x819021303050d0e09160905090a1107110103051501050d020d0222170d020604080d0e070e24090708191a0f030a11270c041a18040b04091a0406 63
    0x214038603d9030b03600c1807161f52800d01844070104010f4070700750700e00c1e4036030300010f007480c00700030142010314080c0b01c03001100f142d0500050211100903040507407800c2c511900304961390b00441124000d09100340010fa503820009800c100a014103411000d0b405400640385001809100313400701942c8804102c03580103038150f0754459031205001588130150704544005408911344202501819003e1040450704015102c00030381056141c1d00b0802903500010300b40301d0914102e00e82080940c10400c990011446660009442d4000082804082040000009900c81e51100c0440804040c000d014082217605200b01e0130890324901249018200001e800380c000d10700090b00403180e5410608400f0f84a007000140002882038200c3c045010039010040c4003011110141c0600c00c020044200e52103a080c4070030f40c0300d084141c0e0405060407005200301c0a184011403144141e910040f80c0014641000502160150000390785c050200d50011028a03482d010303d03119107100d148501002c000c4c2c10800d150380c0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 256079001 1250 256077751 256077781
    0x605010207080d08040f12020f011104121b0b0c03090913080703032d0e0c01020d020d0c020a03020405040303020c010b060c1213080607050c0c010819021303050d0e09 73
    0x32107140d003c03a001c80c00c01409040540d4016002c1d0021001100d51071b100c44095824100744074006174030004038008100000c2c03180350315511454085a2a0038603004645001d1056144082c14801d00841d9080442e1004040311008043c0400304646594054103219200c1d00044c00060144100e0b00c00a5590b101c402003050b403c82d400f0544508080c0b40d500c0842c01000703100a841d040d5040032004240e151064100b00d85ea40c4402c09010034158240c045450401030803840050540d40101080d445441e004600725410004a02e0000183d188900000740c034240c00d640040c0d089460714007800b050540c190002c0c950703244d8010003800400042414405a480f4100b0f0800c10798115080e040603049240008200c0851f0404410300c5203502c0e21986414503a007a82d0b508041170b00020303001801c440910600121502c2401c2040d5103141240e006000c064440400d00f45040d80007403100145480000307203501450700b000c03c654412030b071000d0180c08003c1000c40a03110700d8090b0001181482000d0300707 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 256080251 1250 256079001 256079009
    0x70f17121611041107021c081e0d140105090f09060a0f090602030a061e030c09050403050c0105010305010213080a020d03050c0a05120702010f0806091512010213090605010207 77
    0xc881d140c0410a01c0c012422038040c002180c88640002c0c1410641d52a40100f510100203c4607050380c1340d0b800d00c1085545400003c2800701141d00b040f40c0e80209070007400b40c1c0e0008031444c0a900d180440c03580314404030301c9607494900c1d4061800c00088102c548031800d0038180d950640300141d00342c9900050405500007240d5504865011f00b00141d020b001c250420220790420386004105a01d0642d07074174050740c004a45031070305d0f50ba690204102c412502035004e2260400c40c00c00c01904e6055882c0c06024011034020310303880541356008a420540700f40b040b11a01c0c083d6800800480d42c5a1070264040e6003d00084114000d10300c20100e1195404a0603103201a401040d6007021502d1399130586032074208890f084424081d40b040c1501050081c8540c03070510610070107440d61a512880054140d01c248410001013112800400c801d07a1a1442200d800200340d143c640c40c000007010000729088128442944694008102070110104209400c3c09039540d100e0284030039600e03040126580c0b4110b2003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 256081501 1250 256080251 256080283
    0x10803180f0a1401020a24060b16020409111017070203090d0609030912080a021204051e2205100812070b0627040204061707050402030c0c070f17 64
    0x20301000150081401c190180c041030050321480421a11010042c07a018040980201d020180c54803440045104230307006002c16410140c14400408070040ea030380740e6200000d0180d6a180c3c01c500c103010740301030b16000148005102054191030300000802c100c86903c00c620a0001f4030000c204920700200558507124800f030f10307000035000389480d1040907040b18001030342488407074100405e4200a04040359000d81c020f4881c5598ac10760081e00925107601d4200351190032000303010500c0701da0354000c80300310300780c025090240c80040c031100062164244160306940d002e2203081030400640749a042184240c2000f844660039a43d240a0251130b101d9000c0340c001e03401c070104030605c0021070144001d0b0704040050300b0001c010007410303052450845900c030141107100c40b0310700300b108624141c001d20004d42050303410000c01d544014003160ba00d0485006941c40b0b03940110010f2054080078040d43e035180050070031035640558601c10b52080b140e40707000310281c0074035900c41c0006041700002c0100c20030b01d0080c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 256082751 1250 256081501 256081519
    0xb070e04050c1e0d02090409032601050a3c0303080c070503191202130e0907030201091403010f0c05030115030e031c140f010801140903030406091a010803180f 70
    0xd400000c944e00c6400c01074129a0300340314540d065203a0b882410b134028460303150909040f40c1c12014107280d048905040c0c00007281d4000500c0140c0f6115440c0e4100d90582c5412000003802044083c1200c40c1411001200611044034140d1000003d0b410001c0f240a034843c06443e440b100000d01c10352051103805801c0b80c1c000c00101d4081545d06165240e2900c4c0c0e80f0344444010f400041c0c0c201641c0c880040b543c0001c021714018860004038a90b1243c04c00e51003402000d00d68515030018024800510580e01003810583e40b20050b40c40a4008103c0c02c40141010000c4884c1414068030a0f0400e02401c03440101403070000c003445000384070301e03030b5884400c000a6042058407140c541c03104440001d40590507407588400415605c10300c1401d40102c0c41a2801004c543c10f00e03080360708450088648041c14510b6505020501c000482200d40080d0400700124001c155428015424140c0ea420301c510400c5038000000c0e486000301c0034001d410100c03040700d036944048900f0010740892410f42ca940c4090f0007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 256084001 1250 256082751 256082797
    0xf050703061a250c030c1419031506050d0501140903040f140105120a060312030908040306022a0a060609050114090a0f020c01020d1b200a0b070e04050c 67
    0x142011211982c2111031411007006644d070301c44414400d50007101c0343d80018809200b02e20488140303103e018030596041e00e21203410320080f2085c51003488090024121500150306440031600a50302401020380188100011454624020042155241280b100702c001091124501200702c50886581503c501e40080c1040e40e044a4003000944e1340381804410001a90302c007103a01010b40c403400e001040000c60514600740346036100500162041018035003001c2d100000c058038103a606507034100d580184c96064100b20755503a0480000303840001c903580044007407904d0001948030801c6204600911803140e46200c0304d41980d1080c010410300c0202038a1101d01401c001242c241d05c4641280041200d212042100c0e080340c0c480302d00c2c5002a50000346c04039200300a0b000e110343c03101601e100c4031b2980a0030700004140d4812075440ba404034450030b44004482e20104000c542c0303035401920b4000c090402e8000603201008405a05003d1401c0000217405151000141c801e02c119900e2500745109030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 256085251 1250 256084001 256084027
    0x3030b0103020d0504060b01080601020d02070b07172d030609071805150c0f1b060a030f0c0804050613030806040f1401032a0f060804050307060f050703061a 69
    0x11081858100341d824841c0d20000034060090501950160030002003e040703010004294100c0200418103550100c080707103400c103500060005c02c40d94004181502c800e401c0c5048014824031420701c44000c1404036148030320720385000d40c0311001e0080005092006464200f001181d000881d0341c56030118140d000241101d00680b1000382100601e6600844582c454000400351030034505014030310140409d100080e184100300318442e060a12000309001d24640c0241560016000c140754021440032804446050007500021850500c0c02004d01440740c05c51401010807004580580c0d03548648000324400e031000c4c1401c003840e0381d095610302d0342a82d11601400050300c001c5440b02025940c0d061b03282e442480c0c0f4641103000c0c40c444e415640c25000c3c0071900c100001880000c80011005004080005090000e071000803501281003c042540d501d00304181140145031003d42068101a003032010030580d944014860412901c04000642d1242c10f082d00f0303c042c040000301800d50401c0200d001d011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 256086501 1250 256085251 256085261
    0xf1c090605160203100e0d110703080702120102030106351803040509010308030a0c02190b0a0b0301151e290c0f03190509010c060e01020903010e0303061302160303 72
    0x841c0501a0b440b0141907020918000400131030b0000c5580d51000300301216001c1c003200580c00001d24018244003604210b040e02e884003480014051400010071000b1501d4000c0300b00c00b01c101c40b40003152250394421024211030808240545500540c540f01305000c1d55010840a994030351800090180c0d03a00030be486e010107c1d08141420b18401030200058139501e41554030b010758881d1044a8603030500300d94400c25200c401c42d6201c25034202641d03407901029510750b818215508035040d10007607155154071000900c0c64904081d055400c01c19403480c10040004160200c41d800e40e10003003000c40c045240360701b040b1280140c1181c20304600708002413015800341c0007219051803049030700d0594101c42c0a460304000200e50002da820100308981803440c40703271954401c5c04960400d58946050140020002076440d48000c0016540e4154102801425030540e400340c030002d0000c100c001c541c01009070b034a07001142c59a00c1010b903160004001559402502d039080c00002c50242c50074900d03074054004d09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 256087751 1250 256086501 256086517
    0x90e0712051902070303091403070308041217130201080a05010f0b0f0919080f030f07081b0709020414030c010f0f02010f050406091a09030301050d0201020a12020f1c090605 76
    0x20391488a40b10081c420f4401002d090b480b0741c0300041e8104040c0b8005121107584c1c2500d0b001da41080c80200302094000c07407403a45c01580300303110880c01c52510f242511050071000c400d5102580302000c000350303c25129407101c1020700036250103041c3d039103045001e419903100b40140c201d043d4803402c0801c030910b8400040c2c02ca418000d10528141000a0301141c55000802c0d000c2d501ca20001e4005c000030441440909460701c0300c000a036141108122000d00e29124080005000c031400043d00c1745c0413803142c05201003400c44801901d40d844c0da1051090042c4d00140a071110700c162812311f481c5286800603600d41c1009045e1104c4120340d44d4100d0070b0701d000356107071281d000759505c40b1000c03000e40d2100d2150030702c540d100d40b01c0040c2c046031600f03142c040d01c1c01040a45445410766000d010004c60000181d90449400300d8151a6940079440100d007481c2c613070000140311460344944029142d03008541d50000c03c40041c2180c042c0c135a030007520802401490b44160119100d054180902031051b0000c0c4050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 256089001 1250 256087751 256087771
    0x10302011e090801051003020109080a05030a200a14070e09100c05040f1d0a020a1d040e060c0c060c071214250303060f0e0f0601111b01090e071205 65
    0xb45507610441420340703004070b81e0a03042403072000f0140708541c0c11464500213804e5500c02001d801441d544c41641d00d1103900725071420b0013100333066241000741c505501076120212109a403c0b200c91440c081d4441d00007181194400d00600c000411400700e200300c114860511000149800d14084c04140b0007403d24a0280381001000c10010944d0402005054010706240c601c140d821450400640301d02c05000c0c040e000e0b418010480088042d80c803440c00089641a150034140304280c45002800030072004020703070300c5030041e1010070801c40b51840103800b003056180113481d481d55680741801703814461407600400b404208501252070a00c00e400048250141e140480d29000f600ba0b05045204140c60311102121300c1743da1107804150b0305003e00e00080c50300c5040f0707151309804d2003c0c0f818100d4000300609c1e11648244c000440c1a84242c10342410142160107550340c00121015600000034030302065804119081000150f444446a030980308111a130340b03060b1407400201e21880a82400f408100c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 256090251 1250 256089001 256089017
    0xc070305061006020105071d1216090e0c0105030601050304060207030c0f080c010b0a0501022104170a03031a0607141e030405010305090f060402310905060a05010302011e 75
    0x400811540c0e000303218044085803482e20f00307900282528002407140080200c20620140740c0020b001039580b0215048030301c0301004180742a042d180400032103040c980d5905045001804520650040c1d10507c491419102104146001036030365100590784c0e030703002038000c000007404901540d0207010007a20a1424401c900a242c40302080485400b1b02a0703284140041c186669200910910310305402c162142440c9914010010751240304041d02c00d202c8500130641c0d1005400c21504860181110000012280150041242d038031840c00d2012400300340761050301c68013031450400340781510200921007880c14805035112182c0704a01d1000e110702d44944100403004800c1000511020b411600055854520700000142910006040f502e810f81100003c0158030001260319544950140d80c8044401079a07807400b0341502d014440c808644007800d204459610a940000c82400e01400480341507480c1c007c9504100c420a00c030081c00300d0618240100b400e658030305c034054032812a00301460 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 256091501 1250 256090251 256090253
    0xc010813050604060506040e01051603020c0f0d030e12040b03010311011e020303070f080103080a03150b0d0f0c031a090901020c01180b0106090b04210503070302100b0f0a03080c0703 80
    0xc90700806540c04c4800944074810058141442d2089a884ca00d814009000504103407444844204456031041c0400d500081c1c0c00000240801c0f940360001c1c0414111401885002c10007401050705581d010305601403800615021490b0000791015103a00c1e88040b451a40780d5910003070144001c05115040c04618400c81c01b00901003203000c0c50000040e0099039032031414520080204040c2107041d0140402880180080f03030001d025101c0e40d080318140040ca03035500041e1200d9003030403a801642800d40000e08070003c0b4080c3c1e008281050b44c1004140704002605105a003514802c450405000c080801c0b110320390310340190f0321600080708100052818480700c0d0178500f542c10490500d0300d04512410140301b0070103051803081c014899403601c4242c1da400c1114091492240344203c2d520344204c00403103c1e081c1c0e44800d40010290703000f0b02f06c2c6d5942110707160103512601000d5400003c80c1c034100d48580c942c00c00c0401480d4089004241701801c60640c1e844904640191114820506c100a13002c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 256092751 1250 256091501 256091503
    0xc050303130f050102030a120b011110020a020106060305190c051c0213050f030d0c020a050d2301150302130204030204020a0c11040209010c030c0218150f030706020c01081305 77
    0x102001c03141580d0400300703040261920070a80b1a901490465100f007003c0254164041d08505c10002145800300d20302501c5001283c047c40c0e00c442c0750348980900c921100100d0300302c1e030040540226580003844001e81e079100980444804651100824007541c410381214034050f800798140d42d02a0510504003000e0030216030303104100880700380c43d50b6800a1140102c0344910491802041d0444810b100600c8040c082a258101c2811060a2007001111b002c215580c0710303401070182c50040d003442c0d241d000710b0900c00d052007480035504091030b80c10080030780e0b4102c4c103001d02410310921090700c014203403940d406c0c0300b050110a580240074683c24040400182d650740010f008800190307459a030203540b1820502e8440d400c0da1112071045104020340011643c0224840300b01030b426080917070020650340007103005522103140110707001609400b00410801740da1007800c0d00c0071041da03103000380d28114001e2582e41e8800d40141e2004d60b2008510341265031040e4481607020702000c0c202840140e05540761 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 256094001 1250 256092751 256092757
    0x71d060318150901021c060b22090504060204231e0114180907050702090a0203151003060f05010305100509100306090807021309020d06020a200c040e070807120c050303 74
    0x2c4517500040c8070a200d011071104685002c080302020401c07140307000020715043c440c90140c2c501a4101c01c590b040340404004c0c1c0d14000f01007610050013140f4042c43c0100080d0304c030b07000720005001480c20406d1406403010341142d804c14050946000041070700c0c00e05442121507280981004039007004a114014100e0180035141c4911010130f111404010800048210007021791041110610000d405aa24091003581040c107880e00141e6070b40b6210005110344400200d150782014582c13609142c01580343c0e010300100d0b000b00495604d2283c40790300440640c0c0f0140c0301f10b01d80c20350701603050100d0f103070140c0016040f01c2800c1c112003c069495603290150303004050705840495000c00d0080950030b0900701040051181e1034100030741c820300d90009910308100080074008035030202d8104c00e040d0040c01c81c0503d01841d881504124031001841030b5079001c0c42e00445001d641040d00184100e1000038450341681d507080040d2020300c2c180100c0000001d2400d500740c52008180300c0001b03051300c0502c02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 256095251 1250 256094001 256094011
    0x40c0b1602121e0a0606061805130b040e07060e030c010507060b0a121103010506010507030219080417031903020304170906040b04060309050124030201030b030708070806071d06031815 81
    0x160011629a0801404030f86c400d41c031800501688580c0304e4600061981d001054a0003119a80c0c0703849021400c020041c40e5008a0347d070072600d482c45a40104100150312021200c56580c0d02983c00002801c0c1501d9101c1404800c1c0880d805003c9a80020001e0300b00c2c84d810880035100030b00c0242c0e15030202d24584505601910310b81c500801c18074050800b0301a40c0d9000b102030a00c00d1400311550b034001d55840b40d42c680550304d1040444504d0030004010b08a500420400b00c0550341044a4108543c0303a51000e4000310915a815000b110924042d0080c1c0748207540002d0030382e0b101005d20744419603a501c8490a1607100200f0000030410740310500c05000944800d07640040e1042d520b203856402c40e807002140100210051034400c00400c0010213180a0b254203103400720341d00c01c81d10040707481c5c8011900200014043c01c18003003911400060520710441c800d036070342e44200303060807200d0000480c030301120b5401c1002000040e58032400d0318000c031030103101507007102c0945c00f0f0040391361203045003641c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 256096501 1250 256095251 256095253
    0x204021b06040f0b01060906080a0b1302042d0b030f0405100507170708010f05010309060216260a0504090209060702030703030f200606211203040c0b1602121e 70
    0x1c40003441603103d0134038050280b07418800c2c0064203001c800380586100621a40004c3d40343e00d001078403604c03242d07550719183c0e01c481c80554039591a00300070900b0076020b00b03140c0ca111561600c001008400010f00008030b9500b1850b651950320303102c800642400000303006549500c01c20b107200020305a9441030522a40e955138460050504100091200702c03070145c11842084034000040c0700617144620b0f270000301c0c2c3c000d080010340700b03402d481d01c5406801421250010341e600c4201ca0002d12a4145d0001c3d8032082500046040026841d030101036401102408000070368144810310000c1b10b81d9004000703000004241a0526140c0da00091074001642c10071000100303c03050011080d60450070b40c005001e44100e42000c0e20b1001c4004030b5030345800608044c8600d113500c2049800860f085070300c8040800c40001e55800412121004c40303e9403081d5011520030018180000382042c041c1c8c01c2d940000e003a00c0309012040101e4082048401c0780c440c019136507001f00888186900701000e035150301950818 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 256097751 1250 256096501 256096523
    0xd030f0c150c120c1706120f1b0109030807110a032003011b271802090a05060c060a150512010b18040804121a0108031209030f070204021b0604 63
    0x207003152800f0070764515883c01c251190000e40e400c41820140901402d55640c172980c0c4480004406050210000c1003a008410030f5001060003c68011105080d2400e011150741e0401d00444400d507075840040d200c10b500382b010b40000b900c0c80700c3c014124035000b8855220252203440751084001170002e02030048007805552001c0d420203005003003020401043c0c141c0c003030f1000980070780403070f40b40c40b0009212005141d030001c501100d00c0c020006421402c56042c2e10031440584c01c030082d400640d146100310460070000403d840d0805c1103d01c0400494046d10954965195000290040241a050745212407001141c0c0c4d0320780f440e410710060341c0c00300040b400101d080148450041c0d105c0000e09540f91400c204004a0481400c46048421042295503c00d40c1d40c20b114440400d4043c01080051200c000000c03c1030002010340040041d0300312104030740c0c45000315180d81e44200900584202414030507800075240941c081e0014410b00b01f41e0700d4410440343c222600306602240c0440d070b452081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 256099001 1250 256097751 256097771
    0x420100f09061409090402372c04030c060f02180301020f04031202010b0a030309030204050f190911090106200706020a110d020a03030504230d030f0c15 67
    0x407004200041072a41420400500050001c00e51441001641e078040c00303100012801319201d0400030703036045050344404860000f881c01c1e81c14100d11107218002c45208041f4020802e00001c08407041c8408202420307284500d400085419000350040c000d03020b02101c6e001e6903010444a00980c108220151001a501d101c0c0d015400301881c014410f040c044ea105012500c012500b0380200c5003541d030414403a50409420340e000301c1c094805000481c2d00b101034103000000305604200380105481c400c940c2402655510b40d24610300200c1103a985035004041484501480d03580d6208a1080d80502d8203c03124040072004101c8004081e8000c0c800520500709044052031a041c40b058484d2200020b454120b2500000079a03c0c0490707e00a002514140080151695200301d140c0d822503001d806900c0c941e980c2d0070054001d800610230714841c4802450315440e506240c0f0b903881500030380181806091495510f0803240011030702c0f406400c0c00003050f00c6502198000c0d00c0c2c04e440810810002c12a0101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 256100251 1250 256099001 256099007
    0x92407020f010902090f0c040306060e070f0c0c060e06130e07020c0603040b06130605030a0f02010801080a0c1203020f0f03040302010e01091d07050f0a0305010302100e090420100f 79
    0x241c4803409203140d261868000040c4c0c3c88100c0b07280c001d0803d40d000c004e251900ca503109668071403640002c3c142454060001152041800d805100b400c83e83c441c42c04420340d80e1030a8031925608200180705a00d814002e110181c000d401a410503a4090203c1d814056100a0000c46c405540c0280c10515070500c2001310043c4c2c1005000b059040030b0341d0301803c604007035075140c420002c00360072280f00301400d001e4045003207819440324004100080c211644001c960170a410b0310101d040b01640010300c000d0010480d00c200081c3d10000c10341c0f2030984a882494406d00240035114804203e046000d50389a02803144001c214680380c003c202c0d0301440e80c8520790b2002402c1d807080303002c1d001d050110144003007102000310742031240c02c80100c02c0044095550680c040fa0f0b00e20440401d03215200b0003045407100280c0c9503000d54141c134030a0f81c024a148901840594a048a401e04182d2010318940000d0014101030301030500c07104000d409505a460290000750103101140341900054000340d0881342c07040d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 256101501 1250 256100251 256100263
    0x604020f040204061d13020d020a110d0f0302070503040509040b0901051b07061a150c01061205060610020705031c021902150f0708030103050102210603030d0509240702 74
    0x12901146010304e0203402030116490440c04440400041d03078400f00c0b80e00e0750319500384540d90303003c0e00315034402e10850484001e40020207240c0000c0e03a1010500c01c50400040c1040c1d083c030958550842d10326281c00210f004e50b1026100f201c5900003880005102d8488845440c0207a00c145090101d0340342a2040c103003158001040030b50320168071902c4842e1004e482048400c03050304400003065014241458840071865000545c2d0800030401d206c4c076000c1c1e0711501510035000030038024069555650b41c41c090400386500003410341d811441c0440c8880c508980c0d9a0061101070042d140c06507900c50000341017940c008660a00005c50034040b6200d154140a0260041c01d00c50308a90b8404854000c140800e40d4941a041c5c180400034140340341b42d2120080e01c4000307900c00e492039905c0d07031070f80340044c041e420000f08a20251040b88244001c210b031040701ca88102009070007141007800b1040107070050310000d0148000d50140041042036240f498149842341500403501d40c0650614003002440c3c08 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 256102751 1250 256101501 256101529
    0x2160f030f0c110d02030109050607051e03010f090b12061302040507080f04080a030f06030c0617070e060304030e040f060314030a0504030813170601140108010803090d2102060402 79
    0x106481815400060390003e020380d50010644854004450a1001c24014001d5882c060400c0c41a1400c04c480c003131780500105520036281401b4155005406034019007400207001d101030001c000d4030140462400c82d07210034100000102020b0810381c6030890941400003d440c51900d041030072409109505241c021150811614500304d807447c540800300042c4070340d000d0801042c0400004800c1c1c05144241c0008030082003480040029940d280340072068282d6078407940c000714080c1030000c41a02d1401c80d085104920360340305c00746040790b4081084143c0d0300007081101400415691042c0e070380c850307200c0c030050031500e403200090250460801c10b44002d0b1004000d0166481080400441c540c46416281240c0d0f01003551610f414000035600c1100d8520b41010344190703180704100754049000521181290180c2c3c40d00003190780190300460b800c913824040c8a071316920410078051b040c2440b00344051400d014001d5446480000300c5144000f090f40642880180c1c0034106000641c503240d00905000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 256104001 1250 256102751 256102757
    0x904060f0608062e21060b280206130804032f030c01021009051c09060f0c021804050a0213060504110304050607080c070b010f091a060f0d02160f030f 66
    0x602c0e0038412900e0544c900c00c00302c10420028500ca403003114011000d910805c001004240041c5490f040d200005070821454901c4040080b0700f544032001d0505a185a00070081d8003911069841903070340e058a04000400b214201d030200800030100c0e040c040003000004885000010503401c41c12102e6020418490451082d0000c515026041e0b03000144211000119000420400030303904140d81081600705401c55611800100310071050350014810302661843c1e21900741104100f20115825040b07030100a400008210750344407007146070403100b503101c1e20800c2218141c04070b03940410300d40b107000601081c816886402c140402e00c5c2a000c0c000ea26042c0c400b5990951402d80ca41990b00c24000c1c004030240a0410085500380c1c0e6207078100c845194104074107160a5a41c0e0380c408029550904c40d210040749001c1076207030340d010401055107201d5001442182031446204c607840c1654012030701c0c181c0d03603076082110390401030a007403609016501071109a48103a02c1c608000c3e201c1652000c2203410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 256105251 1250 256104001 256104049
    0x10c0305061305070f12090b0114031b010c03030e030c0d02012f0304020d0309170606100c1a0601180305070503151003150b040504060c0207080a03080c0904060f060806 74
    0x10343d03600c5034482c00e4120191400000c0503001d46e01e140020700a1070401b8107000d100c40c002245128101c4000c40d090b02c0180c08490300c00d1401303403025005010418800d4001003c00c500d43c1c021034481d801060f443c0410000783c03031824240c01d882c0d61801c0b0664001c44090b035142c503c6400c108032050070300741c65500740c1418811442c418038180c46481c480244024490440c892132032051501c54001d810107088a0401c03400200303600070840d9035a02c0704889444c0f180704008080e04085204406030650550302c044290300040500d0011440d840004080300c1c104001588004108000500c00c1c200440c040c202400e64a800c0a060500b00255a4100c5500a00d03020602c00312000e8007042808132074000c2600f0140c401e0640201000d0100a00317010340c89400c0c0420302c8144681680100001ca2140e0211026581e58101464603007452100280202e00c03008002528040c21400a0548840007000080c00c151284084081850b240d00440d0000d0200b00800045003091681e4900d111004070800301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 256106501 1250 256105251 256105261
    0x70305040e1003260d11040806010e0402040b0f0108190b0a0608040507080d0c030e01140c0607090519090e0a0b0f010602070b0702090a0209130e0a03080a141b0705010c0305061305 79
    0x20503105a10070081513503a07502d40030040c6c07405c02040d20301800d041016030301c0f00d5170b4072803008040e0345054400345c0c0318034904620f2452030b19042c4001c0040e400306031a69403041e61180428901402200e940d20201503c0700e0040c2c0075661340f0300d20301d4007600c15500d844040b810300342031262602440b6082541c10303621041141e688d96820103035420030150315250401300d5000c80c00040703801486038440d91887c1400800c0386135028501183ca44d116141a0340c0307500c461a0b82d50100244c0245000b480e5400400050041c06583c0d66a0010081d88001c10304a0310400130542d2410460907084500d40c003d00301d502c0040c0195541403140030010002c452480341012070a400141d0803000c00b40100a5490740000d4041e155160481c084680b610141c404218501c40c0745900d9403200c01480c1b044001581d14000a2011481e61081e4888401c03805034042c1c150390340b00ca840c1c40c0d03103060018500c162081808840b001031424090344053304001d80e00480c0e03074140142408201d242903900545454180000c0203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 256107751 1250 256106501 256106573
    0xa03020a022403010906090b01080408030a111e03040b180d1101090c0801060906050402070804031112030a0917060702060a051b030c03010608060d0807020105070305040e1003 77
    0x28907011600080b40314014060045000c0040c4154806401c0101c000110401107074880011541c0e002c00a1080c54040401140c0c070f903030300f00c400602c051000c3c0041115200b4650110402040041d041071602d00490184840111041400003d2840c0001008200900c00800c690040390446100060000c2912142c1c0c1711055504c0340000c010150f022215500d00c00d402c49800107820107420390704a80c54221560103400300f4090500303081d080c440f0004544c1003074400c030703031180e03030030500f031f10704090642d51240e00a180115895600c0302001e054141c050400f4402000d41d08910749654a60300c2c03420028014060726411401c1541c1c12203401c02600c00c0d000b01e02c5550202010000090319904c1020070450344410b42c0a20010f64404030400040c01d8021001f141070780e041751200d116541d120000c011804050481c01810f01405004070785c0154007034806040540d1003410101c0c1010307100d0074441600b040c00c403440703d4845808ac1c01001401401c1181010744400302510b12007280e48182c0f56 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 256109001 1250 256107751 256107763
    0x60503030f0f070f02090a090b06030a02210c12010b09071407061d03070c1e03030c0803040609200f0a0609060c061506020303180c0a120204060801060603020c0606030a0302 76
    0x881250b41c0e0014868007000f10b044d0840d100680d00803c00d0700b4600300045403600070b001880b811130b07507485000d001c111a490000351298600380e004100040302c3c22503c612078005c030030003c9503114520410f0b8840409654400c0c4400e441985e070000040d9002c20542080280500941078405019480003030301d500c5483c1904441e0300542001010451004050340c40940140c9121002a1404081490000c12003100154003c45a000c444d51000300c003400b8049050320010311000300071a0407084003400013400d180166511a0151a0009010006455600c0b400801511401c00c61040022800b20703440c00d51440c5802c09015503416815505054020700000c88500500c4240700d400300c900b00c1009400c0e0442c24860070000c800c5440a43e8990001e5980d80056542c0c14003080c5003c000403800400107607542240200a103000183c07881c0c08004400c00c038078a5000c0c0d0b0410344802c004503028409000c1c01000f046155030040c0e80340c8044d40380c1ca080410140c4500d1190b080606000302181c1c0c00104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 256110251 1250 256109001 256109017
    0x20d080a050103110f0f061603020f0705030a12020102040f031101020d0e060d02070609050a0308010305390315010f0512061b0307051306050901080109140403030c0e030703080409060503030f 84
    0x40521102c1c010002621011b65075180c82c0e00050004aa146100c0c01d0540711501d140b01e5001ca030344900088110603102e23500340c01071035010350100000401040854080340c080314818000145403a407251a11034060205030400c1d60350750800203400345196410031a18800c40e440b46480f100d00d0701d4010018901e80314803c00807000c2e0340c02003116401c1c4807565000150080c1c0c0001202d0f241352440c50041c0100900340710986181c040c0100c0d11162600c5202060900000b21101c2e0360300c003415610300401ca4003e0180c45030140701c3c000380d07101003080f100c2c40c0034085e0040f9000300c14194601410000000007054410760181c00c500280400e4100361201c0c10104440c400d0301d03613284d0342e44400c01c81d0300b8054800d443c1e6950360541300015220750040000d00e81c003a02a61811406d03078030340c900c0c80c082d10b2000500c040450380307032800034011a10a0b0300100c10410207240caa40080d0382d41002901e49001c81e04183e039040710014080141006521420000701810f401541c102901098088603600403629 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 256111501 1250 256110251 256110259
    0x2031b012a0e0a030b06040513030c02091b0c161d0109090f020913050118050c0d03020322051315170c06030c120a0e030a1d040c020d080a05010311 65
    0x100c41c8011038000d001440c207840c005040895401e0f581e081c14040c0d130708183c807080d00403032601c1c0100344101941007030603440607010f8170341c50f828030f50f25400c0c448030b113000904211559a9840010390300c1052000204100c070886d00c010704161500807081300340b080d16a4010350061b590408031030345a00c070707401a250440d03541160008016078641040c0d8442c0441340c100a50009224040000c110154059081c01c0c0b4001c400802021400200c289081c4034024005046544120644403442ca0910408681e03513110b072040d2410640540c0c010805540c030454080307000200d0381e40a006070309000c00c502e10b0600d080003051011030380803102c188a101d0140900301703254001c05001d421040c1d0403c600c0e09094009051140e581c43c00c050b4220b09900a00030241c0f06154510200384004607a00600c840240b481c000740d840c000849900fa00c4144291100c08515100300c131070840a5030341c07441b42907042069600030f000312081c1c81c40d00901c0c290004006400c031528040051010480008540840318400c2e2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 256112751 1250 256111501 256111571
    0x30601090306021b010e030309010b010314040605070c0c093e03090307020604031101030e0703080921010e0610080d080105060901050c07090b100c05030a08040c0f030302031b01 78
    0x2c2d2107801d042e13400c03801c807811a60a009280c411180c000000b9803254240d03000803c0084800c00044050b619002d0100f0000001000400c0c0460102d0303100d40e401204900349000749000c140e41c0c41110000503841148055540c500d0042085a52032a80c4d80032841d98003c85400600c1e0051000195984c1a403041c0b034200200025003042d80400c00c40700c1036038004040988980da6880c1c0b600c0c01f03407035201c0b0090000c2c0c10a492800f41c1c0c0c000003462070039070341e00540c5a8200200e43c4140308210300800240ca82c05458200300d10070792032081c45808034045d03060340540741c58a841c40b02d892950f552540144083e070f103c00344041e00140e00540c10341c1075600c03c984c029510356002d40100e9031030103410036400c00c1c1c0c003588800080c00441c907800309070b10480540d00e450300c030004240144e44007040e00d075000c1c0a5410400603620a644502d042d150321a100701452496161078800b01811001650001c40c0540e1001800308490700c500440300015000010082c4041018811065120301c0316003030300c9802807454 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 256114001 1250 256112751 256112767
    0x506010504030b0a05060a1d0c0306042007030f0f021b04020c0d0c0c05010509030c060310080a080c010f0902130e010b0301110409060f1211010507020d0506040507050603060109030602 81
    0x2400c00c980040d038000655107214100b5800c6035000b440192040b074424594030a0018032048040305221014221400c0803c241d0b6640a21030040ea100405c41644641d591713242407030301507070075200304103d00101c115241c6030205464050700c2d13050004208401d000b0000010f02c06580d0010700500080c4100c00014003669071703180468003078001c00748054140d0055074081a1131607070200307442254500a010a003046541c41c40156118403c2205168164008603010b00c6203042c070000558000603007142d4595000c3e071f100c03c02070801c008244c0482d4444800120303c00c00b20703024058046d00d03191041d410081001103900003014409060079414860340c50303d289950b1500294000d040b030f810b001d402402149440301020f2190345c454064401c1d007529200b004210300802a25030819a441c0c02e800750341601c85034440740200200d418030281006810040803005859103190100303c00e110b10700404044c1414a0000d0501c842a04082d006035001c2c010001c603aa40004251304507500510010790794011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 256115107 1106 256114001 256114007
    0x303140c0c0316140f1006051005160c1e030311062710110d0506010e0312090d1406070f080601020d11010209040e030c0d1b06050601 59
    0x800d03c079000880c6100c5081604a5005448242c846454850705a180a40006444405800045010107400305900403400513000403142c03018801100603004280340036402022403404500003280042c40304c013141550245c010005400580004a01c43c0d1418444034441100000c80c001d010503003481c00484d0b03044c054030a210356801a540090301100c11214401c124400e18022046000007d40d03403842581400c3c0a460941611b640520f400300e0110b50008081d20b05100804810011603900401d001c500c0c01c0b400740a0b582c4a0100d000400c00e40f111038800100111814101201809000198a803007840a40c0d920b40c607800307150358219000d080a441c424056800082484104e0b8020003125042e070080600060400040400203003c2c1c80300b03000c1d003441c2c503080021a100c07551002d01000ca100c1285042c0211040c0c0703002d081c5da010a18820010344800da54101080031a0703c = true := by decide +kernel

theorem cover : BRFrame.Cov 255935251 256115107 := by
  have h0 := BRFrame.cov_init 255935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 255935251 ≤ n) (h2 : n < 256115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
