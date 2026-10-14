-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2382
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:32:44.720981+00:00
-- url     : https://prove2.me/submissions/4306de36-9353-4515-aa78-2f5d7fa1f3b5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 428237410 ≤ n < 428417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 428238660 1250 428237410 428237413
    0x906111809092802120c03012f09040e0a060207021005030103030804030e0a080d080a050907120f080409020d0b09090c130b03030f040609090509070b0301060c03111006140f0102 78
    0x985441540b690103c001c10110240740340d900042e26000540d0030114403c139541c541d840941891500c0c1028020f55008903454800c040031485411100011702c020010038a00c0e440300003c5407a035550b1203034040041003410f40100c40b910050740c0b130070a00035802203c00781d2046605010441a103442042144e058980c1943d070b0601d691070f00d40d4107030780d04843e00003031550144044002181c1d00c201007144486100c4241d07a869170600380040b10000710f800103010382c4116080782006115200038205000c40d09944007000020301265410680164066074001164140c000203040000001d590810b10f0982400c440c0e4490a48582c1400fa590b5040e1030500c68000c622602c1e01001d8200550125902110150a0380e140c88540c101000166001d5040b540200e001132009001200c080c3c466258810120310040c060340d420082001454001403150308204400180c03400c1c1014403445850b200684560b0880d852400c400043e90051b09042c09848029100c1c001c2c1d4848500d011080e50170089410380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 428239910 1250 428238660 428238673
    0x3030e1909090f02131e0b150c0f032109150606070309051504030b0c0f18060d0c270f05060a18030308070e01020a050606090a090611180909 62
    0x2440720040d16101c0c0041c1c0f0764110798106100540c41c2c0c11140c3d030b200450110700044aa81005110038500c5110601c01c1e02103140c88a100825180d014902d49414203114209803514400d1500b0703441c017811181c5c0605a404040b40d04071084860102d07642c0309078119440f03048070f60744940501c1d98803d020100410400b080d00040341060820340024030740c1d00e001e4908010030035103c00204040480e400005986684005410000c0c401e0082c180f5801441c846c20040c074040c450b0141309164015070b0500c08002d920003c0c03102d081e60310181107820701e1020a10510403080250005807448008004c01d000c0e032440030b601c000c440c48440c80110306840b901c00d81c0400003030405092100540080b801d503403e02100c011210321401c0ca00180000661003079441c02020710300303100000d041040c0c92001d941551303c42c1c9680e10004202194003079208409031000000e5075201010032010708101c2e403000c5c100514000d091900b0b01c154500070a0315004400c2c0c1d040c601c10390707081070252590007103415490580004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 428241160 1250 428239910 428239919
    0x70b0c0903061501030204080a150608150c0904090b13050c0303070c1203021504080702030c01080f06010e06190203031f12150b040612170313030e21030403030e19 72
    0x2000308901e43d03201890f0041c1401d0300c0744451480d011101c00306403400006002c140484200500501016051303013070241c01c000c1c810b401022004a006080d03000a0b90000c01c4062640c0c0711503020700301312030b003010340c0c1000760604032941c41c48214103102c10388090248000794002c41c10000205c0303441c541d00213005401c03075241100b440811105058124114056400c2c01401e214144114500980c0a4001142c1d500c1c2c45104140c07400004003078003030510555000304407091000e0301909070f1055081c2450021600004006401e5200d0040742c010300c03600010030054a1580080a90312420750b0b03624410000100e6203118104102c207214030300c04410b01c412040001000300c0841e0189040c02000400c2040e9401c00140079100180c0003000000309050f03000c0305200102a4210703000c031200300104e285081c031141030440316100240c007605001600410500b00d486811055480103032174105c0a0601c01e40912241e16584503100c01c1d0f00007410b001e0300007403500d0100e0345045110b032003481050189240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 428242410 1250 428241160 428241181
    0xb0f1f030f0201030f0e03040302041a060f0a030f05010501080606071719020601080705060f0a0c080d02031f03020a05010f05070b0a0507080f10120201020316060501050a0f0803090411041a070b0c090306 89
    0x205da5840729524580318056036a500cdc1c500151440c008410b080c0c0c4e440e5030f0b0010005003252000c0c0d45000361181404010003999800681d1180c1000c000d5444560b00d010f130b420700300d0007542c0300102ca03101004c0c0018149180c0e02c680c103801c20500c100340d080d500386981c0c03820b596641e0391482c0203d60b4800d00c10000c03520f14034001c0e8003d000b14907190030b0604c1c18014648032018543c00003180d183c241e6400008105a1080c645d18500103500101c201901d080c2c01c42c0c0106074034500324010281400a080956410540130754162031595a110700380c148035291030307200f40c2d018220941c0c940010500d03650100320b0300d4003800d080c0c612845255901d0007a0070328190030302e0503114841005a055000400840034850740c40803c42c000c403406058041241d500d07000c00c1c03004070703c0e4507071004a00300e42056092003030060100854002070710807034000c03590030041d035103c02c602c1c80786500040c032402c801500a255000c040c005804014007811240040343d8503034014a20a100c0c400155a04d5049140025105180d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 428243660 1250 428242410 428242421
    0x12270f06030e1b0d12021c020d0e0402090406240e150a08060d080c0105010f06020705060d020f090a0e0108010f0b010804020d03031b0305220b0f1f030f0201030f0e0304030204 77
    0x40003421207042003469140d481d10f032401903500b85c0058000144080300400104191400c010403032004000100c1d00709401040500400c0a40c1e02c03a640024030501950b940707070042000707403498032001c040302d10351070030050881c00e0300501100100b1001035480c10549007044600040004078170b011841e00080c03090446000f88000e09203540300ba04c9800b02c00115403404003400682031324800009840d41041006d0b40a801143c0c040000c66005c844107100340d4844070b0a89100302c10000e00545c485084810344106805040c00554001f0200c150008080c14a0702c00c0d18100d034000402008101d51501101060354584010740380400d20200c0414010305180103910503107070080c0783c000b0b5110681580d00e2114041d520480b000203841d441030000b5040407044040c250142605091140406551006150328000300a580c05244c1030340000c04000b400f144e1001041c0000203c02165070b00d0f49069035980e00d0381d260503400a451315005000d001024400c00785005610f600950500780343d030303007084080c01d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 428244910 1250 428243660 428243713
    0xb030f1c02190b070c0f050c09090d1403090c101806050f070201080a09020a15080c041521150303110f1902120114010302010809060601090312270f06030e 68
    0x86660818408907104041b079000301d5200d02d0140c61700803080020840e00380c81c0a80484000d0b006a2a5003000580241070b02111456070007040d0303140ea58026a40d41001c1d042c01810f900000301a040c0742c10141d03c0409812902d0000780c441c4100d81c0c8078601210b541c041d080d4400140481000940c0156004050480d88501030100c0800c4818050780451800916640302c03044c0311440e0190240d0b02d40d0402c0c4090f034400d950703106180c18145020040c210101c0b560b442d00090150f0249159084444540c241030f0089913403805214159040d091007001042501c010360000c0d1031101c3d02d20b11303280d0120307120524000b904000c00c000c0c049809100010024848201da0019038006040001442030103041141601550b0000b050f601d94000580302607070007031954031540c0044042124907a0003000c0302003030b240c0207180c02d041010886c400fa41e82c100d5608505400d00d100300700c00542120785013040410348043c005034020160780c44005405a0764680180a440d0f08201c2e1501c291840c071400d00c95540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 428246160 1250 428244910 428244917
    0x6061b020d0b061306080f0d0305040c090506120307030206070f051306200a0c080f06011208030601051c09110609090408090a05060c010e0105150f0d060b030f1c02190b07 75
    0xf002c2520101100d071564400c07000790700847e102c99042c07642403003650512081402c051059107420356864603041d04a0081810f0540e4810100e50070f5240c1e101c048050310b5200d002c80b40e503041340b130801030741e6020212100000100349508410f20184030b502502c02d102e0800807008000ba003000c5090b034070f241c1811501020341d0310700e80e5024030490b002c004100d0524068162000940c1c10407a501d03013000d1608070f004070345e40d00040041001950030010380114a41081615480b522100c1c0100c0f00c80c0f20300d002c203000c51034000c010820542207030707480204082c0c0700d0744049014610140503c0070500890510700d6120316010001030100d01d43c6030042c464140000c01d641d08c5a525140041e4494125640303010341ca0303545851b0f80c19022024420b00e0340002d1080c085040b01222840002d0404a903038040c54003400d100d6054004010321504458110000207054440100340c03a40069070b6440c0c1e180c82c50100c3d1030400106600da40c00800d41e0400804081d030301101c2007102e031302d03031032510301c405001e81081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 428247410 1250 428246160 428246179
    0xa0f0f021b060609040506010605030c090a06020f0c0103200d110c06180705130b04060305070b0705060f060d031116090222061d1c03020106061b020d0b06 68
    0x1948100e20080c2107005110056420302407100d0092071030290000c1c08103020310b40803418400824000981d06045400038a0059607a80d0740c503072007468900511140d41d070000301564000c5003654002c5146034100c0d0306001141c180e00f01c214011003d403818406001c8211084500c41c45040b21260b000f4556848058004070b010702c5100080f0141c0e0b48814284c4507660800c00500600c81c1a0041d2340c0360340341c006030040500c2d0b4100710010b000303464000040810b0541e982c3d076150240c1c0303403600030385c0096400c03005a4000e1591401071000f01d41c81000e007141d0601a103c001601d1781800d480c22400740700041c0c14107070b910f8415a000c0d1800694001075002a21402e00f40500110810b10102c000d80720007540561904805a40c0c4100200c400404c0d030b0070460020b400344510743c1c0c4030407400714101896200201c40103001001c5040381e4400003a03c1c03d042000e0403040f05041c0c054006808645065564059000318101003090041300724070029440610300308903c0101d061301c890140c020400030000c100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 428248660 1250 428247410 428247431
    0x90308130f0221060703091101030b0d02210c01030e0a140721031205070e010806040e01180b07020f030a0305041e0f06240b0c0307080a080124080a0f 66
    0x6510310341d00c40e09031005807000c4181c0ba5850b0030300130349420042c01d040030b10042c40d280d1745d5414091100f01805040540d900100081e0ba5503841181c164260041c1050000b840c00c052021110031032075281440b45c0c8224041494154070a115090418080d000542a0540503554490103101050000400f51190890100c1d20b0301c1480c1c13500c00e40c03090b450710340e00681030107140141c8490f0111440300301c1b07079141c241002801c0c1d8004100188039102440c1c5004c29a9405000034010242c02c508105c41e5803a01c0e804003201c00711035a04c0e05009004000d48106030341c80c20422643d0b040445040c3c60317640c0092048854090103904025000b034461308001c10801e00181131108000c5c0d601d0002d94201e501d5568200a004071480703507000c016000b10591105280a140c2404c1c100720911544e10603040020b042c0c1142801401a204080d901203400c955801c50418000c042503401e000d5207596108103408000d04041c1031610901c00c0e0082e4483c40f4640c2e541c101040c0c01090b03420502600e040c0c640f010401c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 428249910 1250 428248660 428248669
    0x1e1c050c1008160822051f0f06050402071515050d050a020111061006180506040e0108010f0218011d09010f030303050907051f230319090308130f02 65
    0x10203030981a5103422840c501100d04643c11408040944144194013040c0031401d060710304012008038400c4102200340d1540d14165241c4555490116050240001d40351803000b4280c10804541c0580c040c1400381640f58401c00040b80704d09000107003008880c95a820746544540c00928400e048080e03092511561039000c5810507113041e40444542d0440c0040d0000c560b08201806150380c01c00005004519240032841c0120045003c1c82060000d4942815010741c580803a0388007a1402801e5161039a55075000c0e00780c480741c20700500003554244012921102d02034426070706411a10f004a406494004d4010345184404045002041400c0c4000c62050740310381ca2034500805802c0303107910f41c0c18a1414010102c6070003070302550031034010b40310402c025920320380410441038400f1000d104042c0307000401e480c4042d00310484500c000800200f03990051070b02001d14410641010200a02c0341c0c1f407401c075812102c07882c40c020301180d911008070301d22031751261001c600c0034440d1032002011401900000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 428251160 1250 428249910 428249929
    0x10b1009030b1302190e091b15040803120613051603180210050307020f1f020f12010b0424090e0711010f020403110a0608070806010504170604021e1c050c 68
    0x11101700c4140311041080e11343c0b54100076400860a80544801940a031001151040040c1c000b0310610000c80094901400d030400c1320000d000071012a0350b030303100802502c0c0c0030480c00c0320841d102d070030041d10192500c8030030300400d8803c030496124600c0d40d01a41070207400825035813096428100e144c0b0240c030b00680b940c0e0800303182440d00b6111540c980c6040d00001f031a113504000410f600e6080f402480caa50b000e00000341d500c00340700603005a00e44030540c00031406800741c0701c0c2104041548100001d5400141c8000340103541c28000b10054246007490302220301c40ca90708680307002910740c940802c0762501d00409203421a655240c04c00100041311b0500b801d55003121880d413151640000c0802c20002c2030006200380300020760384502a5898810003500364100200b0300010f200440001550070b03807040f0111070241000040024080f4071080116039a240c1c101c6089000f102c3c18034001c50460404c82c0d092071011002440000f14030740c05906007030b1034010a00111814450425520499640c90071403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 428252410 1250 428251160 428251189
    0xa0c0b0708010e06030309030a02040f0e1905060f091b010212040306063308130f121202030613020d11041502010f0b010c12020705120f010b1009030b1302 68
    0x203544540d410030fa9084400d88021303041a119600800103114940c034040b0710100e035107404840c0041e004400c6850a0b018084941e00d4000900448904118409542c203580704801d00500840d581540d0300d0049a8804506039070360f4003075510040c4d880c0d00c1655501c3c80d10368181c1040c419241683c502c0d01552815070010f800840d0038586520050203007000301d1000701026508400200314407a0ba01081c24000505c503069101001520700000c3c10704c50b00d80d22820806a881703084518031124038100000d2821a00600d0400a0800d060121003044140280c0c0d0142e08001c02c51404000c1c6102144020345c80040802800f80d29584404205801c80c0c01400042c56842440d0f00e40e0f080302c400080c215551038000030b07101850000d0021041e40d00103d03030b08a060740401448059079034280b00740d04d400341590000364401c40080040002250203c3c011400c500080000e100b147c482c0000c00c082403841e1703c3d8503400504000000c1020501c44280c7c42d03000300811349640161001500401d042d01c604280 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 428253660 1250 428252410 428252417
    0x30f04240c0b0403271406160305070c1208030a0e0c0916030608120901140307080a0b060c060a0e010c020303310c0305070302130e0606060315040912080c0307080109020a0c0b07 78
    0x2000c00280901c0e02090079004000c580361031030508c11400b40104107080040c043c00300800481d1800401584100e001c0281008840081c6048510700d0b00903035071341c000c4400c40c6500b814500565001180002c850889a10003800c00ca211f07030b01c03400c46014081c070902c1200100b503103c110005245070103003c0d15100d4106129141c0d41c0c1c0180070005480140034410118945a0420802c1100c0d6405440c040e008100c544001c034a0803058000186a03000b000d02c428090302400c014400c080c1c1c2d2941c440044486420020700440d111500140e03200e000480d05203d0181c02220003100b8042c00540c43e1003504203111010301030b00000d8590610a5459410498441d0300c01c0c0f03001c0c803d40c6040143c284240c0ca102c1003e1043d503c032549640d1310f0b03000181c200c900801d40403020810b92140081580d0b80c0c83c0c4d02401c00c002000366410181d18074100804d052020851403008603d2100041044030710540701515003011036442e0500140017075000707103204e104004120444a0020351405e092038007038a11a41d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 428254910 1250 428253660 428253737
    0x51201150e0a05090f0703060207061b081005060403150506010908100e011103090307020f1c0803041106030907030b061c05030c06101805100305030f04240c0b0403 72
    0x1803003c982e006800058582d0111040484848002405106603035103c4800340c1c90381d0480c40c0440140c05240b0032000c070000c010310b860319142e038003040c41481200f000400d0384000c0c0da9107080c030046100c0c50102800081c40390720400c0112525822143c0c010350189031007a9029590840141800d0100c2c0c40071b031195466011a0405034424020f001d1400840301c042851341c104040036550364822210001e0042586c6003040c030f030542e14000313490b42a42c40301c0315080701500c0c00c5c070f40310486a104690031586000312881c0d0680900b014003d4922500e90040140405411900c0e00b400010000b08201d40c40030441103516811a40c140c00040b4a5200d01c00840d11010100391260814a000707100d05142a0f1826040081000c01c820b800044000b00c3d100046946603040c00400c104480d42024141c0d20000511a062641140040c0f08803082480450080d40c500b609095003201d568038000005410151180041a000000369401c28032030300b00102103000c584d040a400030040246c0b280042d4903003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 428256160 1250 428254910 428254921
    0xc110306010324051015140307170901050103031704050304150309050f0f120f0d150f060908060c03070507020a0e060315220314030103111305040507051201150e 71
    0x102d800da1844980f0b020520203444c12882c0b0910007020b610850608000d1240000a0640a00d400c1d0b01e505401c0c5007200c0c1c0d2441c080c20064407070a180d01048003c01c9440002441070401031242d42e050b683d2580d18500718400c1d207914076100e5040980155400e00042100003101000804899030440c02070b240417603505d000d070502d54201080c1710215070b55501700c0c000000c010038001c2001c1094018448180e5101c400c1e0300940784290280c4615034004502e0b00e049452940212051542296a16402d000c212600ea850031a0303522164410b030441980420045008401c3c0c02c8091131f4440200c4c500142010681c1d0000741c5041601da0003a50440400d90500640341014088854078070100d640b040a11309000b05171034042149550409075100308400f114041500c40c420400b1090041c0d0444c0e612540c4a08202300ba081c04e45602c00d20440308859246c203032503070340d0080a105603000806003244a14000a00500011600402c6280d550f543c01d000300d0719905c020340802402c60020b4110079854036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 428257410 1250 428256160 428256203
    0x403080c0f03210f06031c14030903040f05010c0c0605030c07080706050f091b0f01020a0b0c0a0e04140a0f02130305031e07020a06050f04030605070e100801150c1103060103 76
    0x10b005181341124103410465a924000760240c81c03a0741c0300d40b011007480181c480442d50410744400e40c00c0c01302c1c000414800c2c1808000040c2c829034400180c1c81c0005076507103005460070403040600a044a02c085410170465000707a006d158819480740441385820351a50301c10740d065000d4101220301c1540c810a01c6000707c0c80785001c60744440b0340001080203075600300d080405484180c030401d1248000c040c40b54501d910a02c0024003541d88010300410701d0038000100c40f2150444424200003802006d009440c034500703802006100480c01105a03142e80b035913402d20b03000d0b241d54010416015020406072400200c21b18482c001103000d0310246480e03507124600580c4100000b6002031094905114503c0941d8a080c918012074085042c942e40d1451084444180d034061030f800540300a103004200400b083c6c0160b030b18613a22004407503c000f400b80340300054a01602c01e0040c1c507414104c20340e80c0071503140100e0a030310405018150303500c00e00d0308150001c3d00d041400d80040b56100c02070038204156185 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 428258660 1250 428257410 428257477
    0x9020a0c11100e13020408031b0f03030f0406020a0e03030c0106090f0203310614090f06010b0915040f080706170103050d081905071110110403080c0f03 67
    0x1e049072950009034000c5001040c0101c0d100000784503080700403400d280c11341244d040310001c14100060360b03200e1203101492001c01c0d1000f103603000903000d04001c03103507248801320841e48140100701601f8459116525910f0080d00310341d01b50000c0c0301da50718004a080e0b03010000b41c9920140c0d480041052420041514180c42103a01d0440742d4600510500050100c01884402038a600c94285406002100913421291040c207001821280c5070544520710302ca0041e0003107104d12900350071101c0b4a9401c080341540c8240900c600407034408180941c1201c0d181034030b0941501e101d103442450605888a2100082071010b074040386081d40080f404124a58119030072060700d0030003841d014031540c515144c1c948c07120805002902009440d80010318200c0146040d022040c4110508128500d01584050b2040104c3ca030011014030072030440081c400780b9405800d0340741041500144c2003500c0c1d0f81c1c5030a0340341c220201110550103440522140d00f0001c10140448500d5400e03036501ca100300c40d281d00013518 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 428259910 1250 428258660 428258693
    0xd12261e040f0b01031b0f0312180b0f04031403180f0303130b040f0f14040c12180b091908090303041806180216140c0a03051b010c03090b0c010609020a0c 68
    0xa000401c0022a500b20742d10100540d0605007000f82c170f000740cad4200c2e211140320307040398001020116150f14644981c1000e403044e2441000b0b0780e00e070070200c00c2c01c459913402103161404a46401c0c02ca19022030034800d20044c2c04003809001c903803c06d141103407070f5070354450a83c020121022010030100700c01d100d00c42c1c0507170040103410710359281d86080c816501e0300c4004204100b4015915440e0032555544207030a41041800c1e0380d0310401c070f0300e0f403040e180b8440030b00e514005a4190b1046408103545440108114078890200f010702019a07095a503181c2d5150881082c9a925000a10000030b5072070f01e0000120b10a942030350000340013400c0c2103803611140001481d2200c064418800d01c00c000000c050f801a081350482080c980c40c4c1e000a003214544210b87d48541d801482040e0300004001c40051000c0208500151080c4801090001115a01580200500000d00a450400041580b54000c1003458012000444d00765110564981683d001c100d1020004a11320522001e000100d0b041c0c2c4080c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 428261160 1250 428259910 428259929
    0xd0f0501050705070b010b030601051606051911090d060e010203040b01081009110f0a0810020a080a050402010e06030a06080604030e0108090c01020309040b0d12261e040f0b01031b 79
    0x4c52680f034a502d07244d41405540050340700040410600ea02460a80d2007032851000ca001c45d140301850444064401070b83c1004001251201d0030a59480a0007640c0b020b516183c02603052240310f03030420400d00c404a03c1541c80300d54442050125401c2030009509c035601030092202c65514000c1c2081c50501140b4006085514008010001820200c02c0014074501181c2500c050f2050f0000190451201c1d1300c90742c024801c06406034041291030f000b511100d00c2030b44884410f95504180d003000e450f004c56000b400140031403e0b68370700349400380145403c03044458000510a440303220031441e141d07007554140c02050340d100c51101c1940e84404036543c01110701d8060421240790000213035032806282e100c43d200d561202e03607408944e00d440075084519500f0601c58044400301c1507000c3c2c90380040080d60b10314003031850031103489041d2404086014040203515105001c035a00d45010b04040c02400c01c032140c0380d076941d40b400401d030889409406940140403191101c0381400c0d800e41c180312203510035800b8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 428262410 1250 428261160 428261167
    0x10c020601050f1f2f1207080c060705120c0a090e0601030e010f06050f06130302040207240b0a05010f05040b0a091e030302010b0a14120c0d0f0501050705 68
    0x49601003442411580155000e8414003801400552201100000022200740340070f41400f020750300c2074803a003a00314a9040b040b824080b41490382080b40ba101001101948042602010600300d10010101c02d40503969a50505d21294100340c1010030503103070280010307400f0400f504020790b1701041581054a20710814034218442c00060700c004124810038602e400d8010009101e40d02a4002e6641141c1c5140200542c81413500701701c000340307040e0043c80c2c011034030020100e501d410310604403543c401c035034006c0d2880c55280d80c1c2000065032101204888440c501040d8100b9500038586410f00a02c0854000c40c2050314034082c8400030115500a5040003590325082c2c1c01203400c841254203440e03000c5511a81c0d00c0c0c0c41c178004d0310700c0e401c50f07071100f10508420380950641c00c04a0591300c040e07a00c030394000d01806403803130200b15101c4454011400714080840080200340703060039504280000f208251040600150001240480c0e541d009640403580c5095079003c000003071085d158441014100b8505 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 428263660 1250 428262410 428262431
    0x7050901031203050403030b040c090f0e0f0f09070504050f0a1b0903020105070501060806010b0c0106150921060524060c06070807020c09070306060807090501050d1a0901080106061101 81
    0x20780d5020ba41c101d820306036070b1000324082c14465005004085c07000382051041d80c2c91064001c05003030711407141011100c2040008210742181c005080c0c0110382803848840161101e01e400700f0003420190040e65148100c030000542526140180d0340308503905e480610b02403030002d414100f59140340d0741d02000440b030495080a072035040f001010641c0d030207103046901c54101d46441801000e00d41c210881900c1a08000948450808028040344c44014000d00c29260703170302807881e41400008050030214541c0002030040385600700d001d000c603000007201c4115211040c2c80d03103c1118011340c0c2a41003002c00ca4205580040e41d030f100740ea1a01e00039a0003a2030002c42c07218060303c468000d40340300c0c10071001101084645100300191480b01c1c000130050841810300c0036018004285912900000c47c0c403d0001400c40c60244034020101c03001070f111107190103201c0010f0340080401c0f00d401c03102040000100140c0f5152200c010f070103400c1e44030001a00d9802c02502070704030b0a1034645403c060b030401c20001c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 428264910 1250 428263660 428263673
    0x11803080106030207020d06090c15020a0201171914060117011a0304020a15051c0b0d0201080a021c0209120a0804051c0204020715050705090121020f0c030307020705090103 76
    0x5046910b2440e005840381061310016012a0710021301420752410903951409002c0c40868081c2160b2001d0303500a4802200c0800b130346c03607410402c0c1c06408910103040210f0502102c091166200001150340103415201c2e503081411a0048030070200e6007101082040030558101c060400030307910743d6003110902c0d803400e8904e03801c525083c3d054454441e00031000c0f6085494000102001c0c20b00d481d50701c10740380801c0500805641040318100f1031742070300038003684290101d882684440134002d0002e038130041d10b40c3c0043d203048078007400c034410580d402c002e014420540c45a004072000f4145001613603e080e4042041048000e18103035a415801007106180040d94200490b021102e083e501041d01c2883c0300074100f865001e5000207900180002204000c1102803001d001040700340740010080794462400072070719802042c0c41c00d40800c801c19000c80390401c1100d40200b496a004d4000f61401c0321080b4a11521f4102d503840b0b090950022013808425601032200c2005044207407511071180d8915250350 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 428266160 1250 428264910 428264927
    0x207080c0105132105072c060105090d0224030105121603110301020904020301030b1602031c0203041b060203070605010801091101030b0118120209010503010218101101060e0108011803 81
    0x303440425903800d02d0050a0848003c80c13040b030b8108080e12119652090b40100000e07100c1c0a900306c299841015886604481915500172001a52890308101c140410700c0101e120110302a64041040300d06103084924049130784003280315804520b0b0b103d504d07080074010458400b00034032025401200a65100d0b070503103100700c1c0880341c07c40c0740d01008144101c04a80288960003c0d16081400040003000784181c000b2100d020342c00c0e074066555941e82c0f00c3c004a88078043c150b85a00da820800d0010384020b2042d402940d0001e001e440385076541c1c101f4400981014a40c0c0c0d102c900940c00105032001030000a1183d1801020280e0080c001c0c076981d0b41e600e8510250041007e410301d6520070504c0004e9104020707450700b002501448810082c2c42d22114000241d01c4c00003240f040e80322000228940c14103000390786401800390310681742d2548450401c194004c0502c02c1504215445180030400113090240b01c0003071980b4445038040d5410440c1d003909540c0c02c80e1000345c4090121f8165000a507120450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 428267410 1250 428266160 428266169
    0x1e03120c120509071406131806060215070801120507090513021309030e0108091603210e1e032e050906090604060b0111010e33040f03030f020a0207080c010513 70
    0x41c2c555a0307c5251440b1540d2041e03400c11902000c4001c00700200c0b40343c0364841d00c181c0718140c0843e070f110301a600ca44a41c0c03000031100c0c00c0014924200411031a1500f0382500f0a0310300c036009503000141c86450080c2191030032070714a41e600c10100c00303034001e60500c0d0141c0202d2104210341400852a0b548014184198601c013184c10400308400041c0551428050000710154818000c0d17191a0789003090110389407100f079005120302d1164500c4801038050402c03904184d40180c16074a41200c89080a481203840e0b4103c190540100118002c240c401c01c1c901d40c010f148600c400081988020310004115170005149400c0350f07001105000b6001c40014484d6441a4002e4011540c0d20410f80100c2d6030000a003082c030665030a01080c084518030100e1056069550041d885880c075107000140303400c40d10380040c0348560000200c04180460480c01e19002601c4c0641400308008004402c020200c0c0c2c056064500180c110510030700c41c11005200c16601c0c04000d01c3c01604202508000c07620040c600d225 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 428268660 1250 428267410 428267419
    0x5010b0406150518010509030d0c14150105150f1318020408060f100b07080c0d0f0903030c0302011404080306040b090c1b070503160f06020102071e03120c1205090714 73
    0x550308216803003282191580721014003503d51500c00b005000c1c003001e4101d4012142201e0a2610b007059240c0010704104cc0300341850409481e0b444c007000d200500e102c0e0708030051151030800c100405002d002e001000142e83c00408004464900b4502c4451100140d4007480c03228010041000104000215180c2043e9104079410564490400612048202e0380c044081001c000c0342c190103002090300502180301c804010f68802856410048a10100c580318070030220740d1a03003091012038420488114581e1017800000b5039030180329000c481d508001c40d812503030140000700300701c0182000c2c0504e91402d4002e40c1c814043d400c1114004041e0300031203c0b9000d00e5407003500700b019144401c21030358000b41310160917a030009080703060b00e054841940c05003d5840c2c0b01b00100040441c41403080725007180d00881e4003409800d001e80400e8880e11a0901030302000361013903080320040014850709210746a140c942c208885c0d91081c020040e11002020f00110350003410f010800400304100340e030342d0580100d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 428269910 1250 428268660 428268697
    0xf040c120b15040b100f03050f090601060513050d150c0c03120e070b030a0506090906070f0e04020d1d0123040f30090905040c05010509060702060705010b04061505 72
    0x860014031413602419030210841001030303da203802c800c810400580350b5030288401d0303862081002104000b540c0300300b8603500103401045071912890207081c4868081c4010724240f0b550f44001352040c924402c0540e44100240011006020300384141da41c01c20590400b148042da032521b010304985c0000c0c600e50a134680300e213150905110f06200b0780020301011070300d141d200d0500740541c40007450115111400398010750b020a18810000039238910034001c0d560f50074442e0341e40725400c4810a660100c5190840c6d001d1011188081722805400c000d142440440c0300151001e613613550a440d4824544440c400f260010035901c4448101e0081d4402c0c0c01c041c030350789080c4143c507282d0140003000c0242c1390b40c48030150740e0a1031080e400a0301d00c2103820395604c4009964942030b043c0b08644081d41c00501094003100100038550080010b0203403600c00030042410504030381c01240c1103a014910460f046d0b5914002c80c1c82500e0b15100e45c03c003808040702d05803840f2400c250050040c0c03144100d038580c1010242c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 428271160 1250 428269910 428269951
    0x50a020106080a0f022d040c030905030d09170c150709051c20030a06110c010f0204090c020706080a1a10050a12050610080a02070b0f040c120b 63
    0x3508030354020582c25085814200c514148111101103a11049105110002840c0c032000c0b180b51100082110112070540c548480300d08000041006082000505072201840404198140050014481c100b40049162010ba190994160300404001840c0140c1403100c1240420005011005846020404016522201025596501242d00081d0301600d09400030b0095154140041c1d00d16100381c40302c402100440741501c29009090f84400d8050b4010b848010229050350001161b071080b04103440c0c41d04519801d407038291641907000301e47c2c05400107010482d9510500c41e40004503844d2000e402e060f810501c00415031507016140e130030503e80b940d024003281c0c20518600388000c04001e01a46a400354000040d045400280f41a0f0100d01450003440c0701c06480e02400d071107076500500140300d20429074002e641c0340c4401350070030010b5942444104000303265030103900e004e0700c844e0301103403640d10b401e11f07040070b410743c1c5900300045a5002402100000303036001c1596411103d2a1898000c08544 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 428272410 1250 428271160 428271163
    0xe07060e12030c03040f031506032a050418020102060f101a0f1809060f060d0e1e010902030d090305030d020d4d030a020a050d06060504060915080403050a02 69
    0xc5200c900f4180c040081e00007135441141e022901220b01c102d041148120072500a03904441b0305200150000c1d50301050380400c0140c204403021040202c82d80e92042e00d8544021404455130b0028100000f0f40c01518a4150343c1c0400109501840c41e0000380c0c12403514852510201603544560480f0071110007030325250b2441da106403404101c140e980316840d000359440f00400c003003207540904d00841018001c83c4dc02d04204c12070300311442000d4540340c0307800341244002004044400d480405070050000d01100da4022a417032076900c00b10800003080c810050b0041605100030300c000d10083c03084402d02000041c60100c261005080d2005006072181803541c1e51001030080101d01c5900d01e0b150a141c00707080c0038480561490f1501f00f0a00385521010000c01c2003401c1508010031401b20070510008103030740c1160b0001c0c10740140b94034001d4140103a40d2800002d8403020f400240200300041002e100312607211849500400304520a45951518100041d0030520042d1000d0100300000400584c0a0300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 428273660 1250 428272410 428272417
    0x11041202090601140a030903090608061f020705041e0b120601140114031609080a03050702040b06120c0403060c051908040206220312020703020a1701140702030703030e07060e1203 79
    0x525041541e44c5c214605d0060082103c2e010440100e6510000464202e11800350030744164000350070741c8407130303207911800780104c040030300040c0c0441c4546480400e9580321400b82400740c18200040c00d4003c1c24500d0807409680e810420740e40182200c0300d88a8140e04001000d50450b143d00b5445410200c0140040310b5036400174001621121000040c0000034000c800c080203549415910b140c1c07001d48400d501a2603c002e0507000e800141c06000710000351909501c0704c1030040c0002e0869140c031040442440f40c02e1002c6400500c0200c01280030400c0c07201900a00022481a1820b20300d429100010704101c507558210b0300c030801c05e0f504001021926954100c2c0c221664003680710780321019002e0320404040c402d00040b900c0410010465904030300010703000c000c0d258010301c0c0c0c83e070072800e260400445030585134001c4c0c80d640d2150b000c40c0d510350328110058001c0500368040c0d0380c2c0e08002e04018050f0b4a00440040c0c1946c08101b003001a80d91000c0301100d40d000440c3c20464004c5000d1100d4918003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 428274910 1250 428273660 428273687
    0x6090618040b0919050f01050d0305030a06030204060303080717010506030a020306120f01090302070905100605070c3c030305090d1a090607090f06050403060e240a11041202090601 79
    0x42c0300d4000e0001d500602c4e0080301c0c8a81c00704c0c1061040e41e030303182001c050180081c807656400c1968425100c2c0042e000d440a107070b0145001000081d095640d4000900391281907105801168074403041c0211160310140340e96000407a09007440d0b140d454180030502c6440010020000145e0100c0030901954030716410300c1e15100c1080403501c4041940905500034100c2c4d40341200580314031540014094204d01445115a800c44841c010303481c40e100d001e480c15170140c00308940500c40b1120228907100c04c01d0407400c0700c0d03401701c1e2000c100103030840d030030480c41c500c0b480328001c42c030201502000041d07448801c958900409481c03013540c12000c2e10b0a40c00c900107a98600c40011580d40c100300c4452400241c2d0740c41600c250713956140c07803035803415000c5100a1502035400001d00402007800030407096001149100002021100205074202904601e40c9110301d81c0403c0300c050b0014000000101c2c040c02414a0303c15580900e001d240c003c00000349001036200074000c600c024001195603020f805000d0303180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 428276160 1250 428274910 428274919
    0x3030d050a020a110a0f0605040311070f060e0d0506042d05030a08070c0f1e0b0f0106020c0f01050d0e01060e070507120801030503030403080406020f0d020903060606090618040b 78
    0x103090000007500a90000e980b02400500300b9100824000b50000703500080c01d03086200841c000c2501d4580320040c0400901c03c0c0c0c203000b00300350400d855131800c00c0b06000030300210b2000c0102c0350900b10000e10440304005002e1003460380e040004c020407008a04290015804040441c00c841503801c071104140c2c1d102c500d982030240945901d401d025020008010420040d5640d0086594008040d9000c80c44140050000207050b1902e600160b211000f9801c50b1040c03814055a480f0903554500084004483c06040c00c2528030040020b40e8041049070600341040354112154200c00000030424028200c1528680348c968000d95000d0400b98414000341035040712004040c034042501a0031a03200d900122054252400e6203201248940505416a039014010307515540300d41d1000c441503032010708240c407105ea081292800045081004001c0b01075160f81c0981c5483d6241c0401d1308200006142c0c0b805214104100080c0f641c4403401c80f80300384101c0000c00203046244020a00900c2d00c0020700350007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 428277410 1250 428276160 428276171
    0x1401050a1d0a0f0f18090c0303030f1103070c02030705040219031104080610061115180f0f07031401020c0607051305030a060209030c03070b090d0311060406021201060810050f03030d 80
    0xe0505840044050703071120010030603105004400207084480a00024001d001c447c8402d10002c2d10942005003c603007403880100b0328a010700718452032644240c900501141d400800038046040034401c03440102001c43d821030411814460a08103240400d01c4081015070380c0441301d0420010605460240094604943c441d140182c502c510540f410b001d0b05001c1581b061459540140001d4a01400b10402e081d03078050307440c0c4d11101d104191149640309154000c1c0d103141c03104003208020002521400c10018225180780d400c0c0924080005581030b41664010051504080800200c044d0001c00300c4c035005559000307141c181003c009113034214580c58012800f4000070f101070b41d009031401101c01c5082d00c1014070402d080590369110341c429040000c0052107201003d240c07111541920034000c1c10880740c15036400342041d0404000300d4045a01d190701084001d00107a11401144c0581941c4c1800c09250518603c02d54460405100300c52050400f100900d00e41d0320140103440d82c5100c0e14030140030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 428278660 1250 428277410 428277419
    0x120703080f030907211502070203060a0c18050a0302061308032704050906010b03131a1608040503030105042c0c1504031106030a061802041401050a1d0a0f 68
    0x10340d40280c034240d5042c8240d901c0829108007103c04442c0d8a040d10010880041d403c1e502e40e200580419141c1241950a01c22350025031001d001040c032858044c00300142a002100015141600c1038244000480b5061020f00054450304048000e403501280d0443d00d071411045a540462541d820200041c080814032000f00c07030100d030611021618000005121080801c2440200c80c0f08946a41503035100200401481028900445e00109943d80e092100e403503a80b603940842e28502d102c0d00d2011951400c00100f65000b01540513070300d02c17034a40149035040c162585540ea0006029061155644c0d01c11200b402a101c030b1404003902c0c85002600d245a400f071203130b03038444140c928100d008600c4000100c910f000c01100322070030740c0c1e807001031640c941c66000306203d01030b04024480c3c0445030742c0f0b02d4046040d50700c4003000c0c600d5503240716026039514201040d003202c03070380203840090602005020202040360424003081600044000c06c58900403407500040e014400c46e800182a40e5040b0000b08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 428279910 1250 428278660 428278687
    0x6190207050115230612180d020c21060708040602091203031008031e0a090f0602100c0206240a1a18060a05030711010b120106030c14010e0105030912041706060f01020c12070308 78
    0x40f030076a800ca83cbd003005108403041000071140000760000490700407000280f0b000c3d0003000e0701c81c1c115015200040c2800c1303104001c5011200100401040e03644088100003040309480d003802c000d0141d0002850030300c0c1c1c030140150504103d105561001e140c0208280800c0c611990301e4500614950000710034895030350501130b403101c2110f0b11015459003000b5544071741500016030540204044880302c150140001c40e03142001c81c5145010b40c0c0300c00b01c0c80000804920145100c03451790031004001da5296004075040c01007001850110703000351000e20489000c0d41d002421341c3e40c00861800c0c07440744e045890a1031070040c41745d29082a4091a40d2024000b598030552022055a124481c0d091004e03894140100055400540103400544c1c582e142d404994800c1010f590007903ea139040b109503000320f400f8034441e504140c000001c100b03406600c40461680c2004031540001056544030402110000000c1d21358111080b030340d028041402005e1000030040004000860b000180c8603203903004060f41c503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 428281160 1250 428279910 428279923
    0x30f01060e030a2112020a0207080706030902010503011202130e0c0f040b0f0d0c17010f0b04051320030f06090c011106190207050115230612180d02 65
    0x5100107054181155058280090311140b11500704001a14840d000c2d03801a402103007401803001000010a00b40350000b41a00107441704002c2038000c4c3c001103080490603403805025070300200800d41009078200250360050b003102d06507540001e00c1821000a40041481d140d99200900425881d04040a001d04004a985503186000321a1008080030110400c01030f1004441f001e82e000804501520441c94505c501e43e03610791207078980ba4003441e130703407000c2070760100e1154030000c0c459441d40030780b0028100b14400e001c00c9040444003000700703090060040d900081524001041031401c040100b908601035010104c410380020200e90300309129403207082d19500c09440610b07945c810307000d00e04060340c040e111032110708080340700a00c0300e036231003025600e044848070360508042a1308001c444003091081c010340403245481007030041c15600d031444d20511141c05880d000018001055034840640d1007004690034080d49411b8000380e61076804090440501c182190041442000030400c552134010500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 428282410 1250 428281160 428281169
    0x912020a0309080c180402030f0618010507080f06040b0303040909080910020105040305070b0a090c09020a0906030204081b0424080f1203131104020406050909101a1e030f01 76
    0x1100b000700c0d521000e003581d030f000345802e4903800345030108044403041c1241089688140014122000c0d03c003141103442c10300409481200d48044c007410800f0a6140901456030071054500d00a980c0745031462108402540c003400322842152581001e58007542c0c01c000f030b81c000d49200d43d4100015420303880c081c8015070024032114000e02844006025182c018401c00c1c2c40b445d01911058601109651103008007040140001e034015034414480c07010511081b4014040c0224003070040c1d03200701d5500060704520445e480070040600410041c061158017103042c510b40308030340384078124001250000502814014010140007060040d10503094030881081c0401c03140120309030b410f4084056481a00d400c050340c50845201c1c010070204044440d11640c261006005450020801e00c0201c00a01aa48152300920001d100428020010b252001405070003a41031003403040d040c2c1c80d010420940818100e03604215034404904600210700340200300842e040328010040e0349280080d021007100c802800b4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 428283660 1250 428282410 428282417
    0x90201090503030f0a050c0709050c090405090a150906020f0703170f010b030609070e0409031e090312030c05071a011d0411040e030d020409051510050315040912020a03 74
    0x100098141804011a5021804c0462280c41d15489203000e50740303903200300442c0b845482581e40018500c0c070f2610925002d50440700f1078658030b0340888104801d507034000d410740340a0380044003090b0024241e02031720f603800c815442c4081480341c028244000280035050600000d5200010079500705540613100c090320a142d6003806826403100e50303505c14002c02c240035415061804102065003441c00200751139020384149060b0402c8141c81001c00c060385d10a5200310085200745110f584551030365440d01003070000e01c0c039052041c580b45407143c410150020701410300f81562050503800040c03080c0101c032005900540341d00d00512400380d858100103024459110300780b844d0b00110491040c4d5142d614011a0401c8001075502c11940800c0000e010120114500707210401108411501c5400030304000d28200c58009024030342841e0381c108001d0900c81040c03080c0c4190139002801a04202569000040c080a0b07070094880300000ca001040300071409005103401260744200b0756030000c0d0030318180d0300c070b0754 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 428284910 1250 428283660 428283677
    0x4060c02070b090d0c0803120f070e010806060c1c05180d0206070b090705120f06010617040f170705011d0c01050a030b04090c1211030a0b1603090c0603090201 70
    0x300c0c1c84020500800300701220812161020380303015100014030300d001d504d60f114402d41e221501d5107994803000a0200c1040031500700f00d41144070944846d4401207504114001d2607000300000c00241000b01068441d25021494120700c81081014014a542c0721451000c207024450b4060296007102514000d840391841580c6410700305070860248083e4080c00c02403c181c12951b03488241940240605190f21074070a00040d80d59035080c0c107070100d0044e034025103603442d84068441c6c10004141c108406100d10414801c0f180048800c0c040d0b80550001c1c0f00e103424880714508400401180c8c502407507040340210b00c4006004040d4000d00c2c40301c900d0100715503a00514440261980084402c00380420307400d00034140081d000340c02c40b5031408030003000024402103503507400e03080c7c0d04150071801d0918480315042007009185881e00b07808a0040b00244030104240d42d520441c0038004052000c42e6400e10240428140240c005400c155070100a0031102a10390340020001d06d101c50701030b070029202c036 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 428286160 1250 428284910 428284931
    0x6010f2d0507051b060403410601150c02060d020702042a0c150c030f110408150103050d0e01020f010e16090e030301150912051608031c050c210406 65
    0x11826050544406040d4909007440c54a480e0421000044450f6520b00780e900850008c81903080750030011001d40007194034002401d6401403400c4016000340d1304008181e4951000310390001840d980142d412a61590744590403a101c0010740205880250000e0500846c1c503034000741105600011400a040850480c51141085511004003e03024004610903a61641c0521080e041791407807078458240442d0070302c020784d4200202c5680850103a00c1c004040f07014416240c06020001640740200303400c00d030700c2d4115141c00351035405021501c030500102141000350780c2d0080c40856040720840c8000c1240c10072071801070b0303243c3c480d4012000b0300800101001c6060880340c0320300e480d0394189400860450b030034125103140d4101c048000c0f6040c00601d00000441c10840741c0598003041c403070009083c2070044002c1d103540c401e5071074000114680090140e502008242c241000808070b4078000031550b900d070030752460700c1441440400d4424101030f10b61103020301100180e06000b1845440104008100c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 428287410 1250 428286160 428286193
    0x8040905060405061816030b06030f0916030305040e0601121d0f0f0c0f060705061501080a02070305070b190c0804050c0303040f0b03100906170d020606010f2d050705 73
    0x2c00380175082c405038010114054200503140715000002e0ba00380041c99004900008003141c000321003860100501100b0401e0009040c0080b060b4000d1101c4550341040c15503134082d08900030b030300480c07001489402c00500181e11403140150050f5550360200124680400401d80e620020794003c145885000c00f01c4600c204002340001c2c240c24581c01400044603e02c1c1004080c00215400960002c014805403010400500626018201d1a00e510340301e55080130014201102c000c0403604514810b01841c40441d8201d02201e2a4940c4600a001e0070340c0c41071100c0003c0c1d1101501d01012078a40f420f8000318940003550107000b140120200e80030070011104156491085001d205082d41c00354104200200c00384001c1c64000250200d407882031a2180320307200407a52940d0040b424208a01401100c030901403040b404220150320140845203400380000e0b10035400c411b0b481341081501c0d42030000e090f00c5500003418064004685014801803001d001740503400010060751980240c40918032880130 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 428288660 1250 428287410 428287429
    0xf14040c09140d050c030105070f0906020a02060d02130b160309090917070624060f0906021e24010611010203040209010b180904050319020c060708160804090506040506 74
    0x450450b12240891800a10030b070011241000c548500c038014800c00039641c21300a45124590543c0d03008065500880000e140da11154401c00954004d28030140140e10b46004a9030034030f07482c204c056500d1000e0040014000321a03802046049400300701c040c0104414501200c150740660381e212101e079100c040c07080459400b04801410200211194219031903044003800c1203c0c040c0d540006d00360780801c0890120416401c01c00c803401000f2006000700d5401500360340c041202440e02414050401c02d0180d81c80344652121424407881c0d546000c0850000c115044030710b00c582205080c05010003100b403a0541080c002d4201040340040501c10705541442507a2045030000c2915038981d10f001c00712403140c0c0c402810029000f00e035079a0724042c1c2d140e4000b5540610b00c01e000442d0b8600000703813481400d07803081c00c5003000c64110405421240e80c4d010180c80007650010000c5035075074aa19485132803507182c50340c0203040e031001140c00222403545a100602ca00802d4405024590302c4d403080100480c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 428289910 1250 428288660 428288669
    0x21206240303031e100f0b12010803070b07031e060b04050130021303020904030801051c02011e02070e010e07020714091f08010e0102091314040b100f14040c09 70
    0x344c600b00c801c02d941500d00306041d04030b09148910110140c81c0c03101007100301880c1e04444981d4100284002030075090000b12801001d14402544c01d090761581c892000841c00fa01900403d900c44442c421000c80c048000914a044808100202603581103000c006070468411640440c4100140f0016400c4084502007182c10340800030300004586c1a101000350071001e00c00207500d041840210050716030360036882c012030103500c84201540c505010013440d00c8003200103020791245080d40e000142d030070170b4191584110030b2440c010f003034821031402c9260a0040c1e000500c07a041082c0005200c42090010300d016803100e5090784d82a0f91110580600c0b50004005950040e02a0f0005420422240121200d0400e400c1000801558411f041400c0d00d000d200402d045960025242c0712601d86141d4006001209040030b00244e02841600450000010b10161581411000203110680c201100d40050403981001e00420754a4648026459940540044c0524900300450b100780d401000740c81c0c00c42e07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 428291160 1250 428289910 428289931
    0x201060e1006020721120c12030b0f120307060c09062309010804060e101409060709120807020a0b0418051918121e0504060203120402120624030303 65
    0x902d8101c041c0090551000002580d8400020400000f80d811800b0414600d9954800b0f19002460808407623580e51028134606042ca004102d4540344c8039510321559000c8119000000799220f40036080c00d500c2364060043c80721b440c00c04140d0742c198200083c0400da689a560710745140382c10103203509002c0e0300f00c15103a018400504c5101d803a0b6104a0480c1c1c0e200707228800104103000d07541c40c554584001050401a62900c3d05c8012030381840320100241d1000316540104004e00b443d9902a10005481c000c011420740142841002d00040604580d020350b400386c40c0785109a40d900890703940b80c11502450200d9150554440210000b0340540d50003603041d4103401010610b55280d0000414061641180e8803a03615409004500303070445040b61101c65480d004440c580c00e1021801402c080202c10041c424244000d00c9691b40c0007040d0b030819000c0600307020041e211800000e031042004000c0c4855441404200304400c02200075802c801c40742088030f00c91941c500020952240002c45140c27040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 428292410 1250 428291160 428291173
    0xe030a150e280b04020f090c0a1101090b010e0408040b07030207090b10021e0a14101116080d020c1f05010911120408040503030a0302180d020607110102010f020a0201060e100602 78
    0x42840f44105507040741c4014400c400001d0042c001c42c10b6000d0890b06d030003904101007000d0a8031900000c54076a8030005400030007885099580e0402e100c04103008503501e100d00130740040c08100355481281c002e01401e00c600b03078035441d00e460003d64602182c06034a5105040c9050002903003000d110809600d0000d401070003807010034a10701040785600c81094020383c80740d040d4000c04a1041004030f582c03001c15201070540721207001c0003036040e500d010b200010048010804800c0c0d06240d5040b0002c0154410b081640d501429980c2c403010707010390760480c1401c0c054004507200c012070328201c03030800c03501201c0180b101d80c0e69602e810041b070700807450b01119803200f0888400c1190801d070f100c641c0144601d4103541055281d81c0441d145800910004000c00c0e40001c1d01181c004400c08100401b16040700e0001c0c1c0510341e07a020524a00a1101c01018182d110700c0c0d14111368000c0d00b054500f014025001c6460300074a000003406803186e4403e032114203801001141082c114800c20506541f030540081c480c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 428293660 1250 428292410 428292413
    0xf06091404050411180417070302060711030f030c070b0604020c0705010e040f0e0d080a0506010e06070c0e0a0b130e1f140f07030e0106150e030a150e28 67
    0x1e02002007040304c0c14403000c0103005140e034403440081d02015208807802841e00d814941034180042250700803c440c0742c02e001950001c2d0707000402c1640002d00d482c000c40350503910b4116030300e58011003a140c400203002100304142e203031480000d05000e5006a00200c0b460710342000b484200e104003103000d07140c1e40040605001700c0d4020317403403c6003400000c1c04c0001d0f0018038480e01c600b21104840c19403001d42220154a542c01d9025040c80d81182070403204000728206000081d02036400c00c062980922000f0519000f80404003a4100c000d002c40d448400c101d00e02400094010003810769940e2040340b140c0c00c880c2892265205030354078011081c006220030078424046400191f01c8001510015840705e00281ca40d1444044203400343c2008501c85445041030703900a402c0d12201d84419075541c0c50001d0402181c03036410102c5015803024106241150390382d0001ca400c141c0c00c0035000c1e241c043c40c214044200034891b03120b418140e03503800641c0d1250103406150303030451141c5c5591660708080c0358552030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 428294910 1250 428293660 428293669
    0xf0902060f1605060a06050315012103021f1d0610050d080c010603080a0921030503090705040216020f0d030e090604180f17090d08090d0203030708040f060914 70
    0x11010b840c154403500584540e5072500e20780302080341c25506460711034100b004181020040e2448841151110b940710350b04000d0f1406402c00010b2448004004030020401814001c3c0090b1003000140b200100e2120314501032030018000d041c07280c00360300060480183c0c0c00000883c400e07009101c20840c1c84d58051a1000b00030004081c0c0005031130760341003007015942080342441b4040003140f003184496210f4102a40241016040741c0c0141c205c2c112054425440751010710341800029410f0030426180c1d03c0e120410f901e884201d800058100c0d20000354800d5502550f48c1c444401c1e0302c00c44000a042302060240001901c40d00e000502140f500301d44040a480e00c2807103141d01200103480081d02d4070005d4041e000c074025540080d5242e04a428002e41840b451090200d900c0d101e00c0842454104400089102e00355a803801400c182c0021400002c556540c0101d81489a001021a501c4007180c0c20015800d5001d4400e0000c110a11040060003e02441d880e0084882c1034200d42d000d0303020b010610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 428296160 1250 428294910 428294917
    0x3041a03060307050603070309061a06030a051f081f020a020d03090f02060a08060f09060d08160c0810050708060619030906051305010f02120106140d140603010f0902060f 75
    0x4035854054243d010620713407503900146121761007079900411518103a00380b007400c44a60040c0e07000400c0c009550f4030429250401140d070002d612b20000180c40e0f4880c6030300c0304052794101404d5154400241d000600c06000980105104801000000386c842c48031b480704200d214101c0103c0140e00011046030101e40294800b480f20750084c02042e60b1540c0a130300141140d8022140d60001c80d1090381400700703504000320180c0e04103400303890100380342c1030040008000140100c8000c209410014500f0044064829040d22941d4070070203000c400740d1103022658603001400101406546030a00140c841d0384a2041c4601404000d001145442d42018414407100c0c00c4401400605884410310350020f2828890103110390b5810614801030190b80c6490b80c02d45110f800210803050041c80642105020f800d88241124098101036480070100507216400c0e014030945641d2291030182031a900010703020883d403007000c085000b005190f40c02000f14044428500000e90014014021080c00c1454130005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 428297410 1250 428296160 428296171
    0xc1d010c0b18070f0626011703120c0a0f0216120602160303150f0e01090b0a0909050106170f10020307050702130e2118210d1103041a03 60
    0x7001603803a02c4076590b501e441415440f092000101d0301c1c0400030503074451400043d924000c44c5440703203955040d45034606910306001d80e0310340b6107400002289007041001210303c4501440c2d108816441c0203040b101c215085110300f1800304040419007002540301003240102d051400583d0f55040f0300b007000114540403041401c481042d42088802407022400340c048010621a0303601080c940d0030f51104032211061684a9043c100c2740c3c000c02e012407580a14001e054880741640001c1540b0364100040212180f42d003d40301c0c80c0d01d807001130014814107401036001d44210312a03842c038041c584e60205a036800ba15050200c103400c01c10528a48840e01e070011600a46145015400d0899075000a04094100a40003159940d1102400e0784c0070028031000d80b0340c10514036100800d0180b40140c60461258201a544500c1004a101d88070fa031020403011070010500152303c40d0507055844103561382c49416040010682d0b902c003e40a4620000c21103003501d528503000b420b28140401020600d4001518 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 428298660 1250 428297410 428297431
    0x3050403090509040b0109110906090d110d030521060904060518030a090801050109090305040311010c0803130b09011a090411040923240601210c1d010c0b 68
    0x40098070783d0365200307101d00960203160300d22140e5241c480440121049006280f00c520000e000c250740c10740e6484203490f00c0701819500100700000519054010003c80c02500d42c0c81460b02194000b8541e004024140d1801142c1208081d020243c0c4090320b130a40458590381d06c0f4020800040008400d80c021f40d070040c0004806041030742040c92500e080d43c0200c41403400140c6105000c000400c400d02a207401404282007c1241000301e4a0081c0075106e6400080c0003a500d80816800d140d1080030564400da4020641a48a003440d00403200c40c91845202a035407512407030042108c3e20018490508130b80f0b8103003041120203100c2c4d0144514210001c02c10f0700e004d203540c0650602074a65000382d0b1102407052003403001c0c2e1a15500c41d1a002070003d09200025446001d08111180024a441c82c1d20307990107503107030b069503540c0340100d941905a000b0f40d105400d039400c010b6003451441c1c0105070300340c43c0e50701d401c41d065044030426221b520302c0708102400106140101e40110303a5000d00603411030518503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 428299910 1250 428298660 428298677
    0x506030c090103230a1401140303030402061308060a0f05090106141005120a020702010906080403020607030203090a0609080406020c04020708030f0726061305190b01030603020a12030e03070b070303050403 90
    0x13005030302c0b514012640e401c4e91549440c0000c02c4a140c0d840601d001d010b0201031000514564004aa541e0000a02c003e00a5000180c0d1345054000d014010000b840610222513403454808028000340c164001e21b01e024030308003000f00d260301c0d006010b0201900d80c4140740d1100c660720a004c2108031360010801c1d00234414100b025480719240055102d03c1a18000805642c9008a10004008080d0390380034008010965041c4030000394013050030b5403c8049450096141c1d1105030441d406d121680344020020344c98802403404000180004d807084031116000c0d104405006420710059108680d8020b000c040100001143d10071882151a04425240382140701010107190384401300e03a210b0800c0c0034140d110020080c69181c08007158070740c40d0318290240020309007040b0700c0c0a0840081c0c400018181c0f501404030b900e91190b8000d2000719001099100a159143d4102c01c8400000c40240c002540c4414074100c41c4c01d0001d0b080c000c6400d1983c00070b14000003518100d00400c03014000303c04000c1c012 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 428301160 1250 428299910 428299961
    0x1e08071409062d030f070f030605030d020105090106092f13090b0f010e06030a0b0f0409111216060e060d0f020c06161704021306060210060506030c090103 68
    0x2c0740076051090154000c281d81020310800c00340c41e88014103c3c0e50503000d00f08100403401c0400e01c0c0341900410981803503410602c009a040d4084e0456421081e00761042c0280b641c841c540c15000709004a61050080000944410003034068422640360b00368099a00114529064a811040202d401480301c900b400c1459281c080380310445203074850100d19844120740c6a41c0e141c002035040c0e1a40d42400d18002044040b0302080e40380c00010f001d400320b40e0b03031100c0c905201d8441480d29030007104000c104000c0b070031091400e01d14000080e195903016070500502120340510000d00c403902080e05a211019181c9003a00c22107118090458036500300c0c4041c0b003a00d04074074250081808001c4445005a02c03840d500b41d01506d0018000e142a900b040380c01c0280103100d070401d400f042e84000819450802c0e03543c42c0007042861000000d400c16040c580341d40000e20550115400281c48801d400a01800e5a12810040700b804140c42c0e12000d030078104800e61041d80683c0c40301039070321900d504000038042030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 428302410 1250 428301160 428301169
    0x120714070803040603060509070c02040504051203090a0302010b09040b0115111905010506010e0a170a050703060c0210050f0109020912070329160c0201050c07151e08071409 76
    0x340e1102803150302c0880d081c4015a018000c0e90040d04007550380c40801d14025170020090101c44170040e0050303a40d4004501403250501400c1040c94885940d90350f130381410000ca542d590b46c2081c043c2d0042d464010004414681000024040c0c0e800c0510a8103d03402c054101c5640c1c0720081604081c000000b01d074203200107041c0f041c00812608007210040d09c42d8641001030954100074200c5042041d516000300090b0740d500762820681e098002c409040b04003462100c1d1406c403107050060a43c3c03151500020401c05103805c0818400403030360950707aa62900c0c402e02c60070344200f62051001103180700d00500400455901a0448041c001c0c000000f011012881c503080c01c0395a002603030304c0003400c1202c0c45280d1580300428034107151800d8010191408645050b22142c440483e041040040703039103c019a8400d4040e40e00d240006000d480c40290749200c402c0e000b007916002103000c038404e0701740000c0d1780420075040c011466080d210007a0f10344c2c07070782d8040b42c103003800c02a02e07000a2030500031626a0f455 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 428303660 1250 428302410 428302423
    0x90b1f0f09090b282003010e0106030e06071b0f022808031e03061503010e06030d050301050f01080703020409021b0c0909030d15030f080703030501080d02120714 71
    0x20150780004030800c0301d040625503904000d1249088207071100d031180910549059010b016100280005000c082175074440e0310400c0700600c8030303500b4000480041414074084640504030758483e1010029440d14200071902d0300030445070718010806c1c1101d0041a20130041070480b0052140211000d1812190700113111540c00c200410560000c20882c070070380b06000e007558000741044500850426000568a485085007103a40c00f048184c040041012600d03408420107084c020100169140c1d03071100781206444204580d42e901c00c1c4a41441c9130181402401260305907040600f6121001801a0041d10081c6000d027551003003503402c020000f40b4014503c00703082c40e642c175520b107a00240062070165103090b100c0940726100324180d2080c0444840c1c004103c41c0d068607031200201c1d003880031482c0100240780660028014043d400034500402010100803c50607219480405c1f290b62640c800070341e2594401551800740c0d03c40f1400e85a05036510024058491160704008048141c0912840c100b45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 428304910 1250 428303660 428303669
    0x1404020a0b0f1b0102090109080609070b160c0b0a0206130b01090c120e0a11060a1b03020f06040b010302011b03080c0904090f11101107050120011401050a09090b1f0f 73
    0x2540420000c941f50b91100300d1038005c1140340c00030055030412110b00d5869a1841c03144290080000401c0e00da6081e007582510406500404001c2c2211740e00c5c1040c50041d4803014a440040c007130362b400658144201ca0383c002c110380d045060154145e080498640007040d82141100502c100500d209030b9200060103005136441c08400500000c00091a05014030380c03003005102e00c100814401c038880298000004002d50014444501525242c0e0070280e081a00b00324010300c00740510000c01c810b1103039400106040f6803003030766026500d8403007191840c100e030800c803001400113002e06c0120b200071136110041c3c01b07241001400022542015650000e0000c1c0c1c00000f11410380d070b004040030702458501000017400545080001554101014282d1110303003034007650b0b0610076480306a40d80c242503010710714034021525008020700c41c0000e050901d041000d2040c148502d2482c42d02145016460007a6600c550340600c220781181c40b43e1159182c000107241403d0410380490a0009003105034200f000e0040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 428306160 1250 428304910 428304913
    0x80d090b09010f0e040905030a03060b09030d030b210d0f02030c06010317091e0306070203031612020f0a0e030c010e01090905341722060b03070303030608011404020a0b0f1b 76
    0x18000e9200c05426180c5540c0065248cd0f400d021f00316580d100412850031005040c500001d01d003a200c0d00195581c1480c40c105040700b070f007080d181e5007140f900050a240500d029260500041003000007240d40317204020312a00707070b504030200400014400c004a00340e440440100203040101d10401300702000c11b4940c441f41915821040070b9543d040c140903ea400c5640ba00c041c1d89585805800f0742c52220146440c2810407070003040304000700c001075060751f00010003100b0351507840c58090802020b0300000c3c07000ca4232901800502c82001c0d8090481c003820818180c44d05102f4a141004410003060300501d403043e441038031400c004940140c952000c0403098070400010b04030980c100010420341406203c0121102c82e481400b6288000d41810300d000d2002500c3c0141171542031814601400e2240c0308142c0510810300c2c007000301609504400261008103000300301c0705100105600f0806419a806900009402c40138070084440c07200a060320342c2c042c844603141286140c1628a01144440c48070030300d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 428307410 1250 428306160 428306167
    0x3040b0c06010f05120a2a0801090b010b340501050c0d0515010903120c02100e011101050c040302150418020304050f0a0503030a021e13080d090b09010f0e04090503 72
    0x5000f0608a044040c0205841a910313a0044824643c1d5801034000c01074400200080c00307044603010750300e100801c000d1018048960654445c1128081c08080310121040b0f0440710010510340c3d034a00586a80914401860010030f000310495031044421a60340311101008001c0000428400d0090500500e000702d2243d950b50840244002201d40c0940507480d03601200044400b240e0344103c0c400d0603260040102d581c0c4801204040d03451a400c400c00a4020b0401480c40ca40d094104041518418003a221045d00784040c2c04a80d080300e4040322403034070b540d006001c144050b0900c0c000d400358400c90b080006103416204c0010b8103014107102c200c1880f054002080204205052000420301400c0364020031300c42010b40c0e203460f00da000003009000400ea001c60100508007446450b40e4408075070005996407186210f8001584d055a8045c605052083c010b550b00454810b42c140c408030b0340816a1903040c07c01e004011a0003400070f80c42c040802c0140d9401219950f00c9200d0000303060f100c0c00c0115603 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 428308660 1250 428307410 428307419
    0x19080909010f0f1a0c07150e0f0a0b070206070b0a06050a05060304030806060c031b030705010e0a030e01030903110d0c0210020a0201120e1509030904060b0f071403040b0c0601 77
    0x240e4a2050300001049032000c0d01c204041d00d281800c0800b075a06040d9840604c0007a589006614090400e0081d500e1180000025172800340380441c4080900a540d00d0183c0086041405409500c50b50030307070b81040f1950810403051003a10041d10300d0510040801e4541090703511405000e2006541c08441d659648208000d94941840382c03e006110540d080c1e421803038640c03400303002c10800801c080c3c020310780069020304a10341802142c0380c514103610300362400e142c890f181581e41c1d040110301f11a20340c60404030303613015040003400b4441254180e03a40700c0940c400c0030046016201d140f2088003801031682c04482042c00034402122a50100d0341d40d030558540a004100844c000c08030490155080901c140d80941d9101201c000c0341ca8800901094103554800310354689003042d1013107520b180344c070024481c010340041b008200001007140d00f0700000b522800d06070b0f00ca22401000c40e03051241041410000742c5000980309551800000f62424142e40310400d2003207511440034440d10303410003001441b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 428309910 1250 428308660 428308669
    0x403052206021905100e07081b0a0503150a0c0203040306110a02010c050408280b0403090f0803040b0d090501140709090e030c0304060c0c2309090d0f0c05190809 71
    0x1100f0008482c08600e0081e4544505844d44448820f139886291141000e20f644201007100000030410301c41100c43c04101d159110900f240c151a41034410001800300288900c0c001400c0d003200966009010090703154418007200800d9840130442c2540410f02000010446510400910400113201143d40300481d0000a0071941c4071140f444c00e00c8414401882502e6000400fa5800958140d06e204045410304400c9210208a00010113045910341000200350f0300010980071500d6103101c8030590754490504035140d01480c000d01015030740520042130700040907080404054000e40c000a010007241884289a403401c03108940800c3c81c142d420000341e039070b03849801c0ca50101c020203981070061242000d0b40ba4496442000c00300010515083c0070300000d07030b201c0c80040002c105041a8401d5441c18100c49051b0140d11600c500b03c039800182d0006408074042c122000d96a40b070030007109000e88182ca20070300586d000d440510603000d04580b108082c0041041e03c81c061180551117424000401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 428311160 1250 428309910 428309923
    0x60c03060608070f020c061b031317011e0518010f1a01030504020303070210020f030c1c05070b01051c0b04060e0706050f0f0d18060515040603051005040305220602 72
    0x1c00070007aa0881a4001641c01b10b1075800064048425030741e500c601c12080d412811112802c43e000b400001074201007440040d500c00f0480b1f031842950780d10310742e415130418201d03450300803010900588011000703506280d40d400147c1c8103e01804508101d8084200d0300c2c01c50301900c4000014a1381c9150b059001040541b00142c040424a0180654074140c0d022a4480c010342100078000c4031200010720a0500a1102e08854000001100d440d0585822043d6580c01c03039a000406501c080c00c440e103042480340702212032503a00000e81c0d81103640313410148900340401c0058804407003602145480001c0a03d0052400cd41c02040301040043d0070240041c00c0c1080e50340841e0511100b00107650a41198400f980c1e95424184d03107042d118421203006501406150111038120000303038004070200181d07076000a00448510300c903225001012320501049821901010304540d101c10699800041ca640103994098420310b000c50405060380f841000c5c0c0b01064014003201c0b42203480034400f083d41003200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 428312410 1250 428311160 428311171
    0x11011b09060f0f0e041b02010b091609090f09020d03090e010e06010c0f0507080a030c020907081306090f080a2007120b15060408030406030e0102070c09050601020a05061501110c0105031f03060c03060608 89
    0x148bc007201001c0f80500404000d1090828258946540c3c1c11907107620b9004010300d5401a06000003c14149002031030401030f030191484844000f070000c242655800c0502e4404e95040c0c40d4020001c402d525141c1c2011b804841c12259449400c01c046410030301400001c0100303110751101c00d4010b1fa01d10401032841d0004024404101282c0100103003038540e00d4090b201142c01c071b400001d0b1a407143c208006015642000504040b500040d141060341e40000d000f091500804000c5104504646103192254030038801d002c460400c1c03026100201e0721281c140781c1c01918110000510783e10385400b0400030340056200c08100c4c2c001140c00c0080603010f00594080540700402186890090342e10040840c0b901e004207056140d651001a815034000c0182c080709640100c01c485540c034040e4482d0301c02407003c600490001c1d1100301120024180042c10a0402c10161915401c2d03540c0e40c40e250082070342042c000708070b0000894000000c030780740703100d869400e440590b400308006040c03100280400e0800b030304 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 428313660 1250 428312410 428312431
    0x6041d0304050109092013030b1806070809060a0c090918031403040f12020f16060f1e0813080a030204150c0b04021011011b09060f0f0e041b02010b09 66
    0x4422071608804e00c548000020030100c5207490302c03195200c186c047c1c00300d42c01c003c044466020921602d03941d0211003031820701d1100200c40340c0d641c2d06041201c02d080d054500ea04c450740003101042079501e44d50002840c0406515024400d5a520102c2c0020382d08840088600c100a4002d180305150344001d101c82091400e0034100c3c40e500340340e59452400041c2541c017400e00e407011324241101ca4030034440c0c001c4c0100341a04a8032000407603a84503103400020720480c03002c03038141916030342c045003d85030301c0c1190000b81d500f00014400b41242560141c2c4002c1c04901000f040500900015081c2d0780a403150502a50700161540d0a00c000c3d41903049400c9050814840040040703400a018400b0082e40564182d951a005054207a410388203014184003103480c950a04018101d0b800c0f004020540c034010665070710070020354580b41513500c0c840c20482e02e400110171020ba040014050041c3c211113203806800051164014850131000c0d0f005150b40c3c40060b51200700e0035210b40307801c0c2c0c042504022141c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 428314910 1250 428313660 428313671
    0x90607051605090c03070c031404091e0b04090b040204020a020f06010305072603090f0301021b010b0f01080f070c0203070e04060b01080705180f0a0b07050d020105090c0d0b06041d030405010909 85
    0x200900b400c05201f03402420800480b61600c020001c03801aa801030003143c0d400d008080142e03c1ca0a1081c4c0741800e8904c500d03160007000c041c5850640186d0552941040b4900c5054850307409210180d80181c0c051070651046091680d10880c08000290086000d100a0280340f4200f1032800d410b6075601102078607166001c4180034401c500401207802d003c0f0100d51507284060040b01190190140c414003655142c0241e10f030a04240f03041d003200304110411600c803008a42d4920042d1200c0100b03507020405001c61200143c040d60180c0340300010b282c0020126000103944030002e459038002240c0469400f40c80d10f490641d20350304288025000612410000e042c080000400141b100b00c4035107062243c049030002d452245c65000c8000090295900000da80d212242042c659444983c2a64001076182000065001d280030034a141d100c1c80003015105048080c0d00c4542085030060700c040d034801c1e035881000c10202c0c1460903403048090072802840d1100d242c000054100300b1141e0052905600f001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 428316160 1250 428314910 428314921
    0x70215180a05060d050901110c0a060b030111090d0807121d0a03150f022a070e090607050c03091f020705041a0d0305040306020705060a0e010c14090607051605090c03 73
    0x21002c4c0c0d03140280d04400061250f6401100c1c03800b41080000c0348001c58000989900300b00000304007982d0f603600451082c04600f10401c00d241c2281d8180e00c0280b003400e020f02c580041c6207007591907128080d020395080b41c18680c1a03103400301c0000d0f000640301d0101d10034500c40c06c0c203c0c1c130310710540329145422101d041055183d80c45460341c0d00e00d140c0d9004681559451040d65007580b60703040e151004118401c0088140344a44000b40e0b0201d0380340048081d2040603000a03011000704a510b10800d054400341c06940c58101060307c0d142c0080c0c1450050740014072404c0f40359242c0041034170b12082421903246403c0c0460001034200150b9402003070044e802c20580d1424850b201d0b00c0500d10040c241c0d084244000d890504556900458000a00f22800014040d051000029001340209104081008010303048034055007269111000180464500c1010404100c40b14004d4034034080090131041c034050480c0e03505400e040c109101c400d100f0120788410b00070b50815002007980045411000340c9981420b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 428317410 1250 428316160 428316169
    0x70806011218050601151404080d030f0216051f020a0219030c0b010f1a09100c0c09020c0a170903060f040507031a062e14070215180a05 60
    0x1c000246102600e600300b80001d42c080820b0510322030741190070740f40c840d41c480008003220020640c090002510f80c1180414003141041114100c506100c02890440c1e01e00c5000d034003a19020003010082c0390309002300081c500d0f0f510f81b4103043c188074001a00c42c644d0404242c503156111801100c0a191060203c13181481d000035000c800c0324044004006a42610b18007201c69110100e4010422440390000161011507079245034161001501100b017000c0c00d4080502c0d9078003566459a600000c8101c01c9880300f4080d002c00c0c20414014900c440070280c40d0407590b42640c1c0540d00c52680c80e4007084981c3e003401403c0160141031004445c00c00e140032883d0000940e030751000b4100c2c844e40160b0101290400204000c0764000359403124001c0300200006818062000f02111014041c1c00d0018a12210711242038100d44003d08052120601c2050b0320400c40f11032520361452141a201080f49070056503400c002010000c2000c41050b0740c1301091469160010751064040780a0345d82c2200c10302c0150f45 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 428318660 1250 428317410 428317427
    0xc020d09030204090c0918050c030303040c03060b04150f0f09020427090f0b0106020c1005041a120c04030c0b030403120222060203090a1e030f0f05010507050d0507080601 75
    0xb0122800314003040b4a05103c00070a4403548400c90251400003c01031903000d030803100800c075001d81d064901200099080c140c03a071104842c0140340e101044000d0000500700d503c20b4100c4d07000588002007a990140108003070700443e0300300f0b803070320b50310880104110000c81007039801034041014258141481c2c06a40851501030081c0c0b071540d91701d01100c079800d40307031654400b814890300010880c0100044d810100400c9001780903100040c00703403000c01c0c03600303003041488154580c045541d000d140c00d01c1c000140328140c4109103030a481400400010b03848200003140c0b94060005110394560741c91035854821342c80c1100344d2004101580a00403c40401c0d0880d034080741e1003905e500d001da03640d6006810140742d465444a00e102e103c450381c030049162036000018042c00391094540c9420079445100018402c0f42040c901c100e5440d0912091000440000110040034415108890b6100301c0b0340d00c4609580d401ca91841c0040c001060503402d0f02c2050007016006411401c2500e40e038200303840021b28000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 428319910 1250 428318660 428318663
    0x1109030d0e06250b060103180b18030304150b01111b060f030f0103020102010506010c051e160602010c020132060f130213090519050910020705100c020d0903 69
    0x89501c20035511008101c0d8020541070880c1c1590000c0d00c840420034020110081d25018403201c0054541e500034480c0c1c3c114135100320194181442c1c0f543d540c0700c00c000000c0c200307003141042c800c1c0e60003c1802003001e03500991003200e0610f084007040807007204a4201c0a402d504002c000c040000b420344000c00d024481c01c20440200104030b0b074801c045030700f03031094000991b03407514000108030101081c16140c9060301e00c01d90091005444100c01101d02802100c1d02400f10b0b0480f0a04403159842c50b0140c1114850394810340342d41021507030340490031f004031b42c0c40500540d450b1403420651640c2881002024030385154520509042c681c00b0700b5884a0340c24662a0080392500400c0b555520f074250010800802050700d020403502a0003c0d02035040040015003c12441e040402c40255601800784a40a4141c481c2005c4520007000300180501511911150103100b911701c90700000c600040c00141d00500007800d1107111601d0035000c41d4008408002150800341c9910102f83c0e1000e040d0302104d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 428321160 1250 428319910 428319917
    0x524073309060c0e0f1e06040e04140106030b0708040c0305060c07030306050f151b0715080f0105010504170c04020d05010f0909020904060f0b030a060f1109030d 71
    0x4501980404654a03001003031001000c0302051826a615000d41007010420300c80c0b103040c0720003566104182e0741141042e24150f84400c04841c00c07900f90030004032014003d01d00d52000c20989502402043e61940540c125034500c0300400208424460403801e840d5010300114002c005407459501c58007422000a000c0c1c13410040c00c00c0c04202030107890089a40a981c10409070364103410811160a4690b200c040308602103820000e000580f49003803c42e21682c68006011003100001720988a4059030106c04c155603228049080c3c0e00344034a003005680040c00c5c3c0315140802c0b950400c0406082c15070014240c070079141c2110018880e5903800300581e42101c2030350050360540030040c403180341891211a0299003040c40070a104516046542010303048038407100c00700140c1034a41e1102e2081c0d80307a01d540a50803400170700105001a600c2ea01c16a8900803003400003843d6480c3d100001c0c01c0c08111041501c04507100c0c1c01c0c0c0e182c0c52a8500c21000c03002c04407981c0074a4003040a000c40d448500301d10428050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 428322410 1250 428321160 428321183
    0x3050306220c030e0c040e07050603130501050a020a0e060315060903010212130201030e070b04030b10080102070308180d0c02121203010b0c07050a0e0a0b03070b13052407 75
    0x415091081c000c40309540c204280b000c000d18100c000c000b0010280a0700b202c0c4511200c00049007001d00c41c0c1c07466034060002603c805420300c800c2c0801540050550302403072800384441c2012410a12410f4060800c0720800b40c0c3c1d44100801c01048561100c05151080c01d0800611003c0c0381c8907590742c0c002070015144107480f0402d1400203402030007201500c42035580000d04000198440d00301c40343c00369100f40c80c01c100512092410541d1030006006015404e42c0800c0180085890211815404a120607121003041e8803410000d0a83c3c114280031030100d11a00c05004c0000003c0d003501139086428001080c1e00340c0d21030301c010244598800040c2c041c40b01030400303103003086091100d043c1c1840f04003042e46e62540e44142d188107561201c006650031b80500303100410b0500d000c0080b00120f440704030010031192240c0306c0a4004041204517640e0510618000203811800304020302540a0345500e10340d581c5241170240b0101401c0744182d4196031b005c1d008a00f50310346480040c2d0b00b095800a80d03103540d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 428323660 1250 428322410 428322439
    0x31b07091d030d09230a0b0a14070305091e0d120513060906060f080f060c0a0c08182715010c03120b2218050c040f141e010b0703050306 60
    0x880401c11070400300c005a10788499100d05c1030000712200c905106420104099070340c078014904461403041790034112041180420380c942e1007a008030341c014071190700385c40d440d00641e80341c094801010120880e640d04000751a620741500450f0141c0711515403130050100c3d01d008140142403450020001305141d585d2031442040c045c4a070b102002034003002d400481c0032903c0e02c60040c0d031000b10340f015402038416600040d040b008400300361003034500d1545821003410840d603680c0f0b401e50000c820034800c062044503aaa40d03239440b0400710201082c0c250300c410302d2a0b482d2011065400005100b44ca8884500b0b06090b0b02c0d0343e01411804c5a19050324101e079020303025050800c040c0640002c0ea6511012031000000c880100592404041e11031880400c01484140c07100160b9402400f8040d1050b04948583da42900302038001d503a03a2407500d540000c1402018100c2041c64a042e10b065040b107920100f030080c165034540c551409820b83c0c0700440c0c203008403030360000d160303200003000540a4003204010b503c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 428324910 1250 428323660 428323673
    0x603020706020c0105040515090d080628090b01020d020309030309060714010606031a10090e09010e1207020324040f060207020303030a0906060506040803041403031b07091d030d09 79
    0x240c0c3c100b4000c000340400c3c1002e0801079540c0c1c03140403800864076a00008118894000503034562a0030351503c0c0c01c109a42e440041011107080c2e00c041c5c00b130044030a00d4003480300750009a400050800071200107148103080000914145051203c2003e640c42000030b0100ba035400019920401c0017298102d503182102d15202c038840010311800e00c0c0703030360a05a012410f00e8050304280884032400100c0f29881190b0f100700107803003150b001d4403404a511484d080c0710780d0b215846c0403684100b4840012406603806403000e8075080922004540d61140829030038218541402000b0052000f4149501d0300c001c9c2e4014201c500c80c000e0001810355001c0903540082240c690191042d9170380080c240d0fa26854400c00b92000361409080c2103a01c1fa1418002044a141920a4605403040302e0015410107042804080c5103600c10300503203a041c4428442540c4c100307030035404c030000c2c06059005846c03d2441c0420f408151340c8079503202171100c4040d58035480e80741c03400030559012025186003c582405c0608040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 428326160 1250 428324910 428324917
    0x7140102120709301e030201140a0c0c02012706081f08030f0703300e011b0806040908070305070c06020c1302031b040f03050708010c050306010f0513060306150c020a060302070602 79
    0x140f044420310711202d0203054041d84950701e027803440349451000359901d68028048502580420002c1081c00000b803015501c641d002e80c0000d10000d0710301202070100007150743c600400380d1240000880b54001c021215604a00308400800420322100070541040f5400751240100d80b0111800c4a005c25507070181407140740a00d01d1241c0103d400152644120000723001c540b01c0c60700c41800c860925903003d181c62414801c0c081c81c05511507ca0319511203545080791b000c10041c06c043d50050315042a100406c0c00d0100a00308107103ea280d0560751041c5140c1203841a00340e50083d0155000500c2c1010b00303440350781854940880011006a80b503480540560342c0a8000325400182d800100703022585018801d4080183c1c0d0083c0c3c22120540d60741d03e081030907681c90312560f0b80000c50a02c0400c031554010030b00c240c1200010700f005400d100c161007580d60303001084d604c118002a2106020001ca820840f82070001410368038242a10124139004242c02189a10540040581c00102c0740c0a001080d4143c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 428327410 1250 428326160 428326193
    0x80706020f040608090c10020d120603060e0c01020d02060c0a12020c07060207050a0f051305061f022103071416050703080301060801061d04020714010212070930 71
    0x80300d490b10b44a0710010403102d42111100d54912440c0b0800c080340c0b401c215408640c031059802840e8090703003d20200d50b030094071005103064646034100170001411900501d1600ca0f0124028058410704500091607d079031800001c0540d0445003e210300d0b410345a04443d1425168101030801c070314003070300d078000038031480010720b055014454011490310707030208459080f11800c4844201250700e60594014502d11881410f0f4003000a502012590225412641d4480c0000748400d078844d1b900304501c182449090109001600b1001d04c0404c524840b491501c2c040e07124980245c1545440100507007041243c4c40003988015010a015002140c192000c04030320381d001c0140c600d403641c0e84c03508a1076a00300307004820105030800c0002c01d207184124812802e81c5e002410340900c4401103000d0000941c40018256031039042540000e482c02c0c0d00740014040c40e0070480c80c90060345028800182070100c5500b0900401010300156207044285080303400607240101044512412140703003e0901d90000040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 428328660 1250 428327410 428327437
    0x20301090b0604150501020c330d0f1802091b0d021b060403021506060403080c030c010c02010b2b0c0303050a080c072a0e10090b040501030b0408070602 67
    0x103005041008054415000d0901910144412840d030b00246015140601138240140e001d40040c00281c90915416504448a416a580c4003e071091071182c001024402c2c0454412000801500c00481c500c02d410b0b81c032099800410440098442c02e090000560038060f11882050011841c069040e0300002007011400c040d417580c0340d0501240c500650018140c100150074001d00494254034085500c500ca9981540a054039020407141685103500107080d8980100041c031000c40050f901c44001c1650510030383c02141c07a201c039003100c9429190212116002c59050111480b9540c43d00641030800241c600e082200701c20500c0d030710304124800000041e10b082050500042416000f100400084515948030310043d03607a030b5081003e5104507413000b480401d10b00c80d01841c0c0d0400e40801c104004544880402c00d0340d41d0000c42c01c0c544425140b0101e00072129008004c003075100d118607801c0800070390b01403181d5851903d83d00354842c030050001d400e045001580e60104540c039030403114000103d80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 428329910 1250 428328660 428328671
    0x100606020d09050906010206011521060503060a0b0a0b09060910031d070303020601090203130203010606080603102717030a0501050108011d071223220b01060c0807020301 75
    0x200a548040c21102403010610310039001c121402c1440c15680300c2c03501a0010192070f4130b054000000c01d0150184082007008000402d41c0340380c1070b0700051000071211480815070034140300c00c150038410060440911103107000700020558803003400c0001111011070001e41c6984091000c1005803184000d4540d106000004901d04d07650954084407000d5509001c0010840c080b6501c941c0d1820a400058050b0340640010400f2495a40085901403880000050181d0b900d501003825640242c0000c4081a101800c010040c103040111104442807240d05010100350040d85091000c001e600a034000840508650144100c40b80e010440102001c3c40035620314015030144010442030107028002002540002039500840000d212030050b507202d98500f03525502c50030b590030b2034450300a000c075076161800e10807003000f4a61410b04070b40d20b400e44040d062802c0305034002d000b001e048200101c507000078240d0022600800890f41035800f182015611403040382042d0010740903102c0700952540c20321 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 428331160 1250 428329910 428329919
    0x302120a0501170304030f020648010221070201110309070509070c0b0604090c0b040305160605190c1b06020c032802060729011503050705090609031006 67
    0x90740294101e404801100500e45610b9220355203a1245210280080c3c0850040c0c00252800200800103e100341c40b030182102e41d603a001d412144031019245400c3c07506182480c5001040d480c4034400501500021413a210404c800b08802c00201200d0446241d00d2000181e1007038000d60240c21242242a00552246040341c0c600e40d07110b11340d016040c0201c10320004030340303d103010310704035040c8c13507840917803c082ca44e680c5051000038026010705542480c024480091040b40b03c400505c00b45010b040980b11030902504085d20b0307642d05501410801c201004488111a43c1500503050f1100d01c0c90031900340401d5003402c401600c50115080e05040000400103407851700080d0540032034905905555500c0340000180c00d041042003016003920000e00196801454020f00602d075051041006580000500c000785400140210f00c16072030704801401449132000303d00414580e440300e840c00740498505400020243e00498407514046c00000c9081c0c107466409100468150b03403030a60800460380d85 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 428332410 1250 428331160 428331181
    0xd110106091d0c01030908041203090513090203120a02070605180a1701140402060a0c030311071b090e100216120305060f06030f270f060a1a091501030212 68
    0x81d00102c030058801d100b0140303229402400340c95907554001601d01e0038546443c402000e11084010100d007004100640420150b6420b5228440a001030000143c203000c50310501d85482a000200c0540f0841407011041c419800a440c0d4107840781c0c0c0c074099840d503802e03c10b007e650362002c003102680550303807150110343c1c2c0f01448001e02c1100c0d003080017071044541103500100750900c242d60194224004006e85581507004a041c980164841d1400066044001441c0d202c203401c088001c88100e64125400c01e40c1e000c002440d00003074055054100301071480140200c0e0303107100c0d070600881e2042d00810150303414801000c404083d1904101c00d6420b018682c40010300a10007111000e214201e514a0102d80b0300700781007a00c0c4141c80311820602182c4680009442d4100306501001e030030715030f03004c0c3c2000c140360034041008501c49240081585040401011081d10484494603503409841c15001840d035507044401c903003103000840074074034901c1e42c80c0048001c0d115034000006013180103002d02c06280030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 428333660 1250 428332410 428332451
    0x70507030f0b1e07090306050910050408040602150702100c05090414010509130c03020f0a150914010314070c080c12071403090d030302030c040e040b160f020d11010609 74
    0x40d00300060500d458041c4543c914030000781e44100019888200c02e200040c1c0e10f51205406c000b0384d00882e480e0740010034015041d41e004450450301c2c842c0110701042140d404201304418042d1000f48903603149004d01009640d5441c500c01c4007c501c1d00c818464a01c607021b181150880c5c40054024401d2005440d6040105003080c801e00d03014050b81c1e00002c95400d4131424509886510403005495245107408110b1440c0100400907402125011300140c0003400d149110700400f0251100e011281c50030000c4c05052484006190500d07041900d00703103981000311000c030341c44032490405005804280c01c042032503004649404009228800b910b21803ca44c40d009080440e10920b5103507984102014100d480c1d0040c8141c0d00c0d00104030359100c0d80068041e402070765200c0b44015141c3d042907a00e07481c1c4070f0619019141500d003071140000303000d03494959001252652030103040c8403880c0082240c00a43d29101d003030900e010088a05000e90500c5030a400c403400416940b04c05100c043d01070080b000d003584 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 428334910 1250 428333660 428333671
    0x17130312051e1c0b2b0b1f030f0f2a05030f0d0c03020f1207060b0a0b030106050702180403050c0601061b08070201170126060603030f070507030f0b 65
    0x1100c100d55034854140c07407801c581245040032000f25007600300e000a00b000e03102400c4907640c0b0410b02da103050301c0c0842c0e12110580000d00103e401c101c0144604003918841406002c1550481400c2100400c005070741c0c0b0340c98122a80610010750b0024107090004840d0030f4031030300034903403885aa07030303500d1002046a04030401c1d4280c89c0d00041e001c0c0e0b14020190342d50303003a81c0b10b030105030060003a070000c2034000c540b032401850081c01521041011500428200303840c500d0358280100b80030881c07109110381c91003400a02c0e2000c2d10f040da00306023800c0300b5501070302051203004200040060000115202c0343c90005171656845144141d504041c0b03006071564100301c5601a032446040c00001e0030301d1040c035954602c0c0350f8125042040040359140c4061503808440240e040c80590b050060340341c408501080d0003802001e240c00200c841e904c0c0d5900c43c0003068009039070706920407001d001d410794001c4102c03000915418610f41d0790701150b140641c00c000d0300350b00141072400482d12160600c0100383d44a44201d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 428336160 1250 428334910 428334937
    0x9140c0103020720030f06011509080115090507030207020a03080706051e07051612020c13020f030105090411150703020105010911270d060608010b0108041713031205 73
    0x184004001142240200100588801100112102c00381c44101d00005041d10140940e500c00c01c010a0a91a008003a4015180c12256100c010002640030b405c40024240c520001d0150b04080c81d03107810b2102040c011400302a0f9180701041200340640c0c11a980c0f10741c06448422450358a007844041c0360002e404c1034030a1414030000400025121400c0407222028109002403a22f40c070808a40940101c0c0c0c1c1c070302400c4510410400413500c030400c500c0f0501c40d91b42c014a030110402c0e040c0700107803444280f40307a8941c1c0140b1a0b40b0f030740d940309004d682c19a9800e40e88000156224140400400d2003500110307004040901125013107060b600003010458002e400070700080c1d07038480f00041121604010820202c0d010310507003c400000c8040d01103200390340701865a01222400000788541c1c905171040756400e540b1602005410000e0048460040c42424210014a0240c0b075008000581c40a00d1005840010305800d08820304075144014513041320020b06240c010714005043c0780d120640d003c0d0003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 428337410 1250 428336160 428336173
    0xa0227090c070210140d02040905063f07090908040e010806060f0103051906121a070e1002070803040e01090506030f1207050f0f0d08100b0702010c0f060914 69
    0x18403000340d0864600590113880c0304403081102c103003103c3e1000d03003040d008004082000000381d5400c90740040c0010b4610f01034001424103140e000c02c14450b941e040303c040302c0440b00e52461410104041d100004800b824003020445041185560404055820020800346842403100520403001c4c0508182c800400c0b00442d203917251902250340d00380403200540d028841c06510403640d403283d00b000f07070880c1e00c1554400395140403494803c20b03034956400045441d0510300c849014010706039156039018801040075546802c0c4000c000b0b206000d8a084540160004940c0190b11807080001c8401018000140ca48031134803013031102d01c1e0b100c1c2841240752050405011551500d004980c1e0206000e00700010101c910b04a0200006074000c0e6405440034094500d102116010901100300f003d1401006040d11203104603028040960180520303600c0c2010003c1440703a101c01d081103581080d02401c00030088000b80c500f02c0c2c2290502e00c0010186c030304208114003084007100340c0b400d03400b010a055510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 428338660 1250 428337410 428337421
    0x6040302011b03020405090106051803010e0f0d05070b07051b030d09060605040b0f01030f230f070816030504061b0f0906020a0b060f010e03030a021c0f020a03080a022709 75
    0x281c2c040e6014550341f00c2d00c2c2c1c1d030040202900900090444c6040c0d903081d070213a8520746000900f1244d0148441c05103402031084101509001d000200740c80002e0b080140c107050242d1aa41d105540c002c0c510300602200080070300c0e9a003248010150048110821203030340d0580c0741e0316213003e401c1c20b10040b5829800c0c01c2340800c16207000d005070b02040b1409841488040980801100900520341040003900d607114041451003203a117100d0103101c106001284a030703040c4009a480401c20080c107210800c400c4d281841815446c60801d900031090629010841d40c54a0030200000c0c00200e0a03042c50342a4400c59840f2280c2140c40709507010b016844003250030380d40701001c1e0703103d0200150081c20000100005009407400740040c040110041c0b40c250070402d0901e020910359401206070401580c00b400310224074040344440102c0341d00d5a45818135200320f499a01950710742845030000c0a11014400290340300750390340c0c143c40c0001101c0403240c2c111031080084111040c0d14201260060124500180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 428339910 1250 428338660 428338667
    0x120603190f1e050d1d06040902090f040605130c180303020c010f020c0307030201030e030706110c010b0409080d0b04140106050c19050a020607060605060f0306042004140a0806040302011b 82
    0x442d56040406000a43c900d010226003001c2590140c6002c14101e0180400e0350f01d81c0e60141002c0c0000002c01640c80c119002001200b915070040c0038840d5003420000d000c10380380c08280d0484074203582c0e000304201110643c140c82c10b00080e880d600b9010140c1c0c40000516900003800d80e20324100f82c0712a14043e0082400b2038440494125242d007641c0401000c000552080e840f452650b0701c440c1c141ca003080d096aa5103070a45690910303a40079004086030380c480f03030003080c49000301824045408004141850b40c40c07200b58001c02050005840e62100000016106c640200321000d0a001107244690385908001c0c1a64111039032074105032240b0310038070800f014501c51a04140b07410200030080240280d00304581c80d484440c0823201191540c1d0001055100c07027000d49000ba9504a50944924102c0d0a120407176581203801c2100c0d0480c141c4944400808a0444040d640340007007954103070242e440030880301c01d0964000501841f0b8101080285079040d8044044030b44400b138102000007100c030085 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 428341160 1250 428339910 428339963
    0x703120f0c1e021f02040b0a09030311030702030d12090f03030e0106080c0f0d03090e043816231305030607051804060306020703030c080a02040b120603190f 69
    0x207002d13038000c1e450b0301c041c085001070004a0745020755026251903154a41030300d603900b0100e56000421907609090081503004807030403004001101c000c2d41400d102c2e400180d40ea0907880c000c02c00303101964103444040c1482d508021900d981041c0071200c0305c4064640100240781d010342054641d4a841004150038030040798409802d04020911504c50028000b044241e0300110780890522416a03400150610341081c2d107407290340200e80031620a00c00c06001c042e080c418410410b03010711400745400394200b003442071503084004a2000c0c154400144000d42d501c48554003d000d000c8045c7c441035148060400003003a034004c40101022a0b540d40d132080c03583d150380556170b01e4080f1354207015500002c6100c00030640c843d48010004229295a40c035070a04907070121409400007034a07189440b840b40c0e0003d8415410041c00341c0214640380c90601883c0582c0548070904c0a0500c00e1000300c0c0c1a96403c120801c10310003200c3d002e04000c03900d86481024230200315021500c00c0384d0420314070407440e24013010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 428342410 1250 428341160 428341217
    0xf0f06050c12010905070302041a04030213110a11280510050402030d0503041704080a030810080a02120a020a3201090303031d0d110c03070503070b0703120f0c 70
    0x410b4164203081300348000c0d080090002c0109907090100103280190400303207045c8400300072540c5948030304500600000c848a16a10400d1340d05285074441a14285c01c1112030901c43c0b0b14004003941c0c41c00c8005410f000c00d800404403a215841003014444203100400c02c2240d00c144103d80718018800700301c009864040714065416003110300c0702e5680718014001103500500c249001403050911050f03c88280c0c200c0d41001199070f0000030441d08154108a0b0541c0085684645a40fa50303d441c0c04e03c0e03038841d211440280501c480400e9010928010001800415802000501c49644600325110680149544d1500d4840c1d041c01012000d08403013003c200c2a001a910129642e003103413401e4000d03140310130054005852102c6c2d004030b0003070300340840005002d00390b840440c094010f00380c0700d1501402c82100d40c402d400c844ad00700803c0d600040c400f000c4074041c03500e941c2c59040a040c142c1d10b0182131620303070100780c5c01c1c02c0d80800e01036059849020301030354548a0161140d1800d03205210030520720364 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 428343660 1250 428342410 428342437
    0x17010507020a02091302100c03030f090804091e0c02250506090609130f0b2803030e12070905060913120305150a080c010f020a0302030406050306010c0f0f06050c 71
    0x31080c05404d00121032076001c184a109003078680314950120300c0c0662100c5030074000803840300c105010164180101314040030b0b8003000384020311640e140d51813584614440c0390300349035990500d4000b05000c110340c4814589122010031076a0702590b4041c3d01d40076034071107107581e40d010345583d209114842d86005065407006002c1500380003101c001e0000710b03801300a0f42c0d944035210ba840451280c01e2401941040380b941000851880e0b840302c10f011980c030700c2c80c0241560a0304001d54601038608400300900b00e80d00352501c80181450000842c0e20b07941941414007180c06004c40101c4c514569030000c40c00780ca070540b81440641d44000b0000709c04c0d0204a00188801d44030000151f00e0782c4260810707604102c806864040c001c3d0b15000090b194507181d40003c0241d00110007402880d0b070048652078400190340007030684244569002504ca22950041c10140130f0040046070699108084504a0301d92040744a4000c803090304001c2c910070303000802203448500b001e000990342d010520594000803c01d03075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 428344910 1250 428343660 428343673
    0x14090606041505060d140c0c100c2a0b0601030c0e040b0a120f060f0203060a120312050c19090513091a04032001020304020108010e0604110d02041701050702 69
    0x80002034082c2044100c0410020000030409039100001044a08200d07040001c0641c0040b440001c8a00010000c0d014440b0034003420740030310300101d1031045407800464001113244080070141c8050039045000d115002030544030348003064080c4503181a90380907083c50b40103980ea440044003a1940102628000b0b1040080c0d641d250030641c0000d520003000070520f038030b600e844903142100d00d00c0d40038003519200b0395890082c00380315407440303000759040b000707602540785141100c0464106401c1d4843c020040001d0007801090610640301c16034800311141c014803071410500c00121954006100d80107070a00d4650a0707000c2d280c040c0c20884c0850300c001d800806581c5030301d030001000701041d10082c0c0c0d8860004030001c0601c001c00c0017107803140e40301e40c5490040c8000c15241a07241409891640c0c29130707104001380310250380c0003030910b41140e1500041c02201da9685012501620803140042d40581011038181e0b5011482c1d005003041e202079000301040e9403400400e4600b610001d031000340240c1c2010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 428346160 1250 428344910 428344921
    0x8010b0d080d06090f0f050a02030c071e050a030807110c0306190f061706010906120803060d02090f0615070c12030203041505180f09060f01091205030a03140906 71
    0x409420b00e00c001000c00140c459a03094040d00707503194103101c801d403565900b0341800c241404e441006c2e00200d00d540114114601000f00f003070f00c0d100711080600412109240e6605a4601181c2900306070343c080d040d0340100d045490060243c02c0240c85003c081400120780031148c910000320032480007001001030507292105003e080c02c051641c05100c04603500d89448221038043c900800000b880c000340145105800710407803e08050041e084080642e02f080401c001c0107108082045000303800034080c1c0e43ea0380b10040050981505864001e4200a04400300050b848804420a00c98981500e07042d0300042124240075452280d07840041170040c406006001183d0303034080060364107201c0d0044034901900c901190500e440310740c030010005080003d10b46441c0011000341c0c80d401e030054554160904d01400003070802c12008104a0085d844144d8944542e0b00c84c2d00d410b00203020366003402c0421030b0381d820085e450f40e002c107a146000c24148800040702c80408150281b180490f4005808140c451 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 428347410 1250 428346160 428346173
    0x723120f01051f051602060c15060307030f0314070b0f0103020f01030923150a060906090209010215100909050c090702060906010308030c040308030106050717040f050123071b08010b0d 81
    0x55030710300c0e002c015075480c0717540103858080c001d1a102251340c0041c00400b0001d0704030000342e40020301107800b03078000070070810016401e002c2c550002503042c01c01e00b00b01d40c40c4542800340e40c041d00c800a03003082a12802c0c408400104a00c0906030781c02652150105061a80103409440f0401d9000308885c95542115020420032b600500d005071020301901c501e00241c03c2e104a0240003036607203892159494408118400c518810603008069400d000d504000b400c0c40080c1d180c02090400114a081001c0041c03002c5500e802128050507010204000059242c10300503581c180c8203072402e01807484200404d54440c00090003910501c003030700041400d40e003180c1e194a4035410151080305030380811701c00403000a01e000040e40c040c004c2591204d4560b015810b05c2219a5002c0c000e4215240041000340a040036042c141e0054800c2802c7c05030715410041040c4002002c100d80c1c90010706070200701841000303801c5566010308410003060074412915466403508840c01060b43e01c0d0310441010401002520 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 428348660 1250 428347410 428347417
    0x6091202030c0d0b01060305091204090513020a06023f070503092e0815040b0d020a0308040e010f05011209080903010e0303070f050405090723120f01051f05 69
    0x8040e007030b90301c035401050114070321100b01001203034644442c3d00140100b80d03241c0f00b51a4401e0150005080171155261046414416401011941619040001c04070810b001881450560190208803485e80d20f07003000751218030800d021503103080140f1760f850920a06000103200f422204004942c07a440201300f094280e4015041102e95002c144011401039070741320140f0009040040c3c090998408510300c00340c0051082602c00c1c144003440d801d00c8580240380600100d808402d4030300088105041c40001c540c401d010074000d500c800491404410021040302400840e030180b02000c10903600c50b028030140004a004140c0021862000782516034200d40100584501410300c151902490001080c25101d0203448a08036038000000d000341d00e5400030402c51aa800751604506040c00d10300050400c10002d0600e004110720000c10a801c0241550710030401d4411822050360b03250b01801c4200040002c4600b0343d0040b1910000042609058030030080d418111004100f02c022805801d80f02c2c2d41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 428349910 1250 428348660 428348663
    0x101205030901082d06040608240712020403060f0e0a050a021003020408030304030306140102010b0108010b03071116030309231201021b010516020f0604030c03031e2004060912 77
    0xe1050241c100711845500c000280403107100140e070319485e042d42884203490aa038070904a07036112800307000024054180f001607900c4040d10540841c3c4415004440100d4071841c1c10300001c2c030001d00082000041d5001d81011080ea14051001b0011583c6040d01d07001c1601d8040d029400180b402d400501d08443c0700880e8110700e08005040548800f903d510f560001c8030300310b02280c0d403140c0500c125507503164490b40d44003003440248064200080000d01011040c4204a8005004401710300214090700064829607004000c5a1120513114541e80c40c5000c0e84c4001d0f00810288600441d004902c3c00c20742d4280c842d4075441084c182205000d008408008000d100b07030a56090107085032501c1040c02e00703210702402c42c0001c200742c03d001300002c10044a401c1c01d00250342c014607006181940100f441a07209402d8100600c3c03034217960230250003030071985041c6428820a14204040c9910f00da0001e071744042400c082c200300342e05c1d4800c00303500703489a8001d0f4804039a0754442002106514106044c100c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 428351160 1250 428349910 428349931
    0x807080603011112040b060402031b070f06290102031809070215070e0103050c0a0212160b1305060709180c03020408031201081506062710020610120503090108 70
    0x4500f21080304086030003000307854100641e40c00600060100c80c3d24000d4011408440440ca5400d1030130740c151070103c050f10800000f4601003500c0341408140e03141030983c180c104009004100f4203c81101200c2e807030084240540d00c0000740400c0c42e501c008151014178042d521030029848100c000c00103240d2000b0002c0c0f08500c20003c46d0007a12056581d224044d179400d8541215400384040050103403074000b898070020850501c03615401940c00107405010003a160207143e6610030250b60749083c6485008040d10000c551420701c030780580c54404101040340070700180c80403078850460484291130300d4400c4402e01d0910721405040c10540394001e00440d40c40b82801071034150348001950031038010009c1030240c21640401000340c50420710110f90301c40903281c03a5003185d24018001400c1c500a02c0300c840054442281e10280b88007040003144401400240f1111020000d9400295a05012100580c001000880014000d00c80c1e41715040b103180c0c0b000141d400c10f0541c0740115004c0c0b070010007100e0317107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 428352410 1250 428351160 428351171
    0x703020309011d040f0c02010b0103110a03110c060c0702090601080405070b0c0703061107060c0f0822051506040c0e031002070302161206181a0603030910020a1407030201080708060301 81
    0x40d599440340406103410045e011a094030100800390858601032241814942404101040c100907c0c0445030944542e0400160b5644c0141d0304001ca40124003c95220344035a600740036600742100058030806100719801d420301e80e0340d440111940c20058900034017903400725a0074800640c005000c2d01e03142c0c415404480b480d5961381c82d048141c0d5040307601042540000a254028422980a2030708001c84034102081c00c940ca001c2c000740f00e0f00004141e001c081c8541c84000c3c50007940407403403174080d40e00704d011150403d030441114404048250b070100c0c401c0c0e01e8100d062160342d00440340d0004140000340941200000101c1c40d001030b50002e40b00301e0440c080c070200d8501c0d0800792050030000d040e00c0b6841540c410428a84031086a5400004905805100b00c1c11300000b9104000781010344035400344c100c030607110300005c40d15501030007406640c44038001c207100400a50006035250910700138450300c2655000f0010154841080f0700000e0f001600d504005101ca84c041c2001d0781e0400000b41c00001e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 428353660 1250 428352410 428352467
    0x70504060e13080c0a031106012c0a060312080601030f0b1507050705040516120204050f060702130203070c021309050c1c0c0b0307020609060105031e0703020604080109120302070302030901 83
    0xc1281921048020501400c01f600000f041003100038090520118448840d003200e64044005072503041d07801c0d000501c440d000580313102d42900450021588242118420b1090b0344029200c3c030400c43c1c2440c0042e16115903100b11291030b0041d980d00c1c2101400d00f8000c60456000d60314280d00c45503042e03440b840384040024840e04c0364861944031b40b040d03060b40201a00001030003840d00c10f401400420003401408180069a01c1155010f058002250f0156503600180f0115610301d00350b40100403d00c2c804820040255001300468511500c02c81c0c40f0304018602c030403081c00b10f8048410140c010703406407016480c1c5042080741d0380d04045850141d41c00185c002e0b42d42c40320311305242d00302c2c44101501006101007582c0422245402001402c081c1c0402c2d810040401ea840b070040911400e1082c02c02c036005c000ca1000e00c40d40d009141c02038801c680c0d40d515030000d24060301c10008100c4501d00143e6504001610a10984c0c80403681076011318504102e2a0044a14000c0c15001c8a43c01410790714582 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 428354910 1250 428353660 428353663
    0x90307060203031f08070b1c050f060111060f070c02210307120f0806100905030708030711090c0301030b0a110c0706020106140a17010905071403070504060e13080c 72
    0x50040640d540110b07628548820341d1107556842c0c00c0c4000440f100102e0503c900c0340081100015903003880d100c1520741441c0640107402801c9058010191442d0809000740003000481c9288a0b071006c0c1ca941c042844046c81380ba90714101101c4410100ca12580801c9015204000407500c0f01c2c0014034003001401d1a8aa896404400000710f41c4076034800a9030008000c0c0e00741100100541c103050581c1608418280130f022400000e00d018032482078400081e00703040c0200740c1c220242101804446806441c1c02d05c0366030b03070f62006606541c0728018402c206890320300403607524071958440e2034680c11a4610703039851400c0000541071068040c2c031040c0507510072607918040c02d004100d01e0000c0c004c075440e20070041d00311a501c2d00b0008200b03007030002011160300e0300b46a5004482d04400144040600554054010030b0b00000081032800740e10000034140540150340f003a407400031025200314541e50070410080f01c1040c0300728101c80750321400290f448403401c14030b180c002d402107840a19010103012800e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 428356160 1250 428354910 428354923
    0x21020304060207051218090108100f0f0608030c120c0d0f05070204020d09060606020f2a0607050d020705010305010f060c03030902190609090902060915130308090429010c02060903 79
    0x20324513028041800701d1b1411221030289041c01c0c080d03501c040507504110009842e000011101a0800d81700c4c070000303801180b10b900200b00b1840d544810000c0e41d4903010350b20b40365400380c41c102d17055201c2d00c0c00b06a010801e01c03049454018941005180000507200c040d200c00034114400c00c184001800120701680340c0380000c000000c0080c0780000e801c2c24614002085030002d4024008541c80401c09142e24040001e14482d40285800d00d000381d600940d81c00032150003207218142d0440800720745002009000a0106030360b020980942d00c20644a034011400c46400344145548a00d502200b00240d03400303020008940c0d0b02a1601050b0510301703402042c0a4000060310048040c1040301c20450503034810f9600c0c01522240c01c050111420540008010340102c0310790303a100c1e0031440903045419101e0b4080300e80c1d590300004c01d400300c1d56403420074071295000004154060b0f030400f07032031138078281c0405444204014103824810b071500c1404011246000020b40490300248200300d9203100741d0b403c0005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 428357410 1250 428356160 428356183
    0x612090804060c1b03020a0603110c03120f0115020a03031d06040c0504060603090b0c09010908060a05040303050106181e0b0d0207060c110606060711040504031106072102030406020705 81
    0x9810900d640c1349840c110f40b0746800500c84454450040030f00040e1341da585940125402c51402145402c055040d511551041c00c2c81140c2c50701c80040d1131100e501d501826940f140480c850124610707070741c4145000090182c81403550060700002c180200003802a8040300b207060542203018948120541900d01d0020180e0342611040c0d0302e00360400503894103001d41c0c40904420b04d028400581c255903420341d0404003402d81c03581d541002c00c40c803a1691107400031900420b502e60850b9a00d040480c5008020103080c0c60590010f41030000101c0c0c154000c0d400203840e6001d5640f09124189007020120380032452182c0d1503004400d280380040c04000c41d00280510f08166803005988180500e0a08100c450201e2190f0901c04003014101e0004004503909611200c00d540e0703940d031800c16103030400100c285105003a034400e140000f40701c14540d20180c01481c65210702d00315038881c0c41c1d2800540b070740040d41d54800c5041040c002810124103440c4c0103540c12074030a50000d403c0c81800d80c0c1e0709040010920f803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 428358660 1250 428357410 428357417
    0x6210a20040e37110a090920030f0906010b0c0d08040201021c11010605090709030b060d0f060b0a051903110604410603060402090d0602040b040e09030a09061209080406 74
    0x468841e5401c902c00e01c0d0304030700c24004e4036290a1203018068500d42c0c0d50300c02c1401840c0d8030000c614041c0008c455045880b0381e44112180c5da89007000d01ca483c00c844c16100c08034580300307502c0046441c91828044480d428464001404c2c40002d01c41d048512100c000c04c200e045024601032030818403881c0e80032030310702030217500c1e0f11034101c2e061080c0c44d0071680703d0b034809441440d4031002e01c55001d0b04940f15605498103c0080d1040c1e030f983c080810300480d544032004001c07020102d285000c0c8174996200400324481210703140b286035507030070030400300100d0b40009a0001c0040c02040002419062100d10301c04000340c0040c1c1016541c0c8181000000162190380f00d003416846d84100000d00c0e0b401040d10076940c8901e0f1340c0031880301c0e000305495010062a0303034069540094504081e83c0c600000360049507001c2c60a643c3d4544071036a04071550868803c51492113205030114290301c03004015941d0013440342d03a0700d003062494075030102e920094041c09000855501c10401c0b01054101d8001c00c09013592f40c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 428359910 1250 428358660 428358751
    0x603140c0f090103110d06020c06040f02041b12090c0b0a200708101812050901260403051c23010503161406210a20040e 53
    0x9081c400715100d58040c0502c030ba6042801840010400c4a01c240003035400e40d5002035141030303450504c00a00c2100c070f158a9a200e502c08200800614441159070181f00b61800d22035808203d1006028061094200d0042031003070508112003c016849801e03000e003d2900305000e10703030302c03600c4c003140d030b4031641b0000c0005a9107007900807640340f2200306103004030768100104489032415844545441e1403014204040d0344443c144844000a5500034420035001800341580340702140c0c0181031944003181160201e122903043e503d054041c103005100122000718011341c01d82c0c40d40d0307048605d41d0100f0700f9035480c015900410300b0505510700c030352a1414203c42c208030035505034001c0602c590005a0000f44a0f90005449035003140b100110722040b1603802d200000250561340c002000703405903503658000d500700c19580b00b11038880c044c1814000c1a1411041000014004040803010766184401d11001030130001000104100c1172503e5011001280c904030b0b400700b00218007558040303107500000c810540c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 428361160 1250 428359910 428359933
    0x316022d2a030c03030a02030a1206080f010c0905040b0f0d03170112020915010203070204051b0d020d0501091118040f06080c0306071b1707060203010807080708060705040b0c01060314 81
    0x200080503e11000f00e005504000707400308003c1d52882030001c2ca00401480340075001080d810758011078041d100c20015100d942d0200000c0074000c0202074149000607103010300010f50790415105030190391101811541001000c0e6050100c1d103080810101d08000c8c2d120451150070380301c886098046d081c1e021030421a03003c10700412050140141c54580c0c030f000f400010303e1860383c000040300c2c4607690555003c14640d54003200b0b00d803161104000f806100c1000280c2c000800f449038002c1402c403021880800c40d036600c4942c46000c65500e070081c240b036120304001007080d100f00d08000709620b800c02007010410140a80d100c206840c06940001c03040e62084185a505190038010b182d4011041c0c5821070814541c00302c2c0301624072600d030340a0302d000480c40c200480c0c070b4500411603c21030340015040d562940c2d145043c0e59684013038072030015940100c3c80041002c01000c540280101e54903903c141c00c150a114042c0300e240d006241ca0583c0350b40e102d2000000400b100c0482e072070000240094000300114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 428362410 1250 428361160 428361163
    0x14070c0e0907061e0c2003031309060e0106021203090124140f030c01140c0a03080613060f090b010e0409050105070e04091203150f0b0316022d2a03 65
    0x1514040000380d500c40b8500d0075042e401142d03003000a03040852542054030a500c0b14451b0002098482d4044c0000604d4458242e8a003030079108690342c10400301300803503580c4c03019800d0300070a000303d80050304460a10780c50b070000d120103540c00005520000070031404848402d40b04011700420900b50340703000c100070881d54410b102c1d045250101914415041448030002030b0300d45401440c03003414040e1110756140d99005440c183c0c3e901100560440d40c400300c407030070b001d440300c1022242d203442a030500c118610695050300551003160711008241d41103034146802000079100c0380d0101810440c0ca20311442641c2d40382d000e01840b090251000003154109114024400c0003069441c50142d4200455000020340119041811034498580041c03400c0e154403045141582039031115000c0c000200c00881c1050216004600641614102c40d2a099204100307a0701c520301da44d01e071607040001c480801d0303604030840003c403001e90f02c4100351389181da219048107141a038100141d02c1c03003120116441006050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 428363660 1250 428362410 428362427
    0x190e011502010c020d03020c0114040b040b01080f0d0318051606031505010e15040e0703022808070e1f020a050c01021915060302060d0903030b040c14070c0e090706 72
    0x1524030080c4600c5400f00d20196031402040c4c0300404055001030740313540110b002c0d4840500860555000501da040c94184983c0340c4034280c4050324503200e4071000040c1d400c0e0016207080e103000200090315070700c800d03183c0650090000400d107403000445d40511400045003480304811421022070034003401424900014200e40740d0030b040f41d101c1c0500c490180301c1680c10284020f4160f03001c982c5180005100c0c00e00308868051070b8031562815803500140030680741c05401904215803a851188180214100401e82ea8076440d100c04003c5000c5801140c80d4a1040010020322000907103461200082d0383c008080d0002d8192a4400580083d031030803041107020710410f4482c82003480100580900c09510001149128900814032036401c01210f100040d85d4101a0056800610f00d980321404a000600600500300045000a141005c038614901d40340c03050004600c3d05a40d00060b00d42094007500d000e601401e07082e03550410342c40e0700044c04525801110300c41e071141c901900340355107055005018181c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 428364910 1250 428363660 428363699
    0xa05090901020c012f031009020a0807140403120e120616110a0b0711010b0306042010120921090503060c030c2b111e040e04020f190e01 60
    0x285e101c964201e0070b41c1d8016484103c07444445503644c0d02c401103241800051b42d44510581400403070300c071a41540127a441403140b00c035a140e103800111081c440780628030660000030402881860140c01040c411105411030385005486400a0082c40c5402d9180000440f00f0300c0c0003040d41c0c4000c440c03199104840c600f40720950801000c01182e142d441c0140124001e00b5001040510a01600d4401d400d400004410001509650715030409083c0315038011042c0b4030062200d040b1030109c15090400c6040c5140e910b44030787ea001c424520080030032001e80304c904000d80c0c0c1040c00300d040103c0000300402d0001e840e01b4079140d1941d4030340380c07805042c1080c0c00206000b040b0b01080c001c01081c0c80c90b40b011110f100c0c91922055140c01c0c01a8800040c03c002c904440c1c00c0d4078900070054850481c804014014001c0d1100091240d2003151100341790351203a800381c64580e0508001080050400c18414991417400400d0314801d40100100e44000002035401500140c003503500400020602181d50780e10300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 428366160 1250 428364910 428364941
    0x108031c05091005091c030c0e191401050409051501080610021506210c0a0512100207020303071e0218060916090513090627110a05090901020c01 64
    0x14a0200b220701e0315490007100f40521991900005050300c042444101d0310b20000d2803011401c0d50f01c1900040040041a2003500404e04100b5041154682130b000c04110303441e070101c2c80004d941400c0c0900b2090181120442c14880c090201003841d01040c041c00b44038900c1c0718921121b0040f800700040c40303040064032013405a04561254010740d980440c12400b64402c11481c542240c1b40c8401091007101d503c0701c0711b0403c404005004003200c200ac110030250040883c0d0020f8201c6d242c904100c42c482883c00c40355020303406052000d0301d0030102d8015005c140e000034282c0c1c0c00c201451b1203541d16a62017801ca00c400f010031200010462402c11018503d51101c00c1c03080a9074900400450611900640002107c1c110019000c02040c401c446070741c0603140182041c010118012644c0000e440d40c00340403a40c003800c00c0c1c01d40804140c2a100041803410401c682c4400201c15244c84181004020b1031682010b07600d500403c15407503e04810f40104020f000043c2c0e940d04100c1800d084036005a02c0803200b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 428367410 1250 428366160 428366171
    0xe1507170f07060b06090913142d070914040b011d0f060307170a0c0e0c04030201050f0403060501170606030f06150a1d0403090806040f0303020304060b090108031c 72
    0x400001c025038040c25481280011135002d11000a8124040d080440d42e00019000030041d842411310a40001c4a1245400410b1a512401d4980c2c4450459507489840fa52680c1d10302541744005d0011050421110103a0304040d407182880e400359468410300001c1c00000c0b8040c0300170020848200350040c1101d16643c003200b0000100140c5058014203c0d04c01d402d80400030860a0f036041c42020003d051140d0b170210340c640e81c2140b41e620782d000d03507505890403544814002510441469214414107145841d1841c0074150b0380103540d00d0708190071880036400c0034440400082c0e020b01c10700340a4441c880742c021100c0f1001c164103183c00700040000740244c00214000b6004580041c0b069001441046002c1c0b5174403610000c21000d0629900902d040c049001841304080590304149010b81d00a6985802c6503883c0c07034600340d0314903050740c00034091100b0401800220f80720f94050340d0000e03c03c61011035a030043c41c0c00201c000b1802e80188059400006102c1c074240324015100865242250040c0403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 428368660 1250 428367410 428367427
    0x902030117031617090d111c0b0c03190606180b12070806030312040803040506100602030909041a090106090f150515091008060a060c0f120e150717 65
    0x10180c41290061481e0091138070044074403400e00c1a1000e4a1026019064400c4641001003450000c0018030b03020320412000a0f10381998040e0300c8041a0b04007150b4903194682000c00517995200400070140c00d900030a0b010241c074000d02034000148055a00c020341040c105a029552090710751240d10003102c100300100c8510301c3d9141c266840321890800060766030303070003010a0039841070000410400900504010800401134061070265010713038101c898a0745d130828440280303c540d01480025031300034406c9508a180c5400780c0740c0e001e0b11821055600482c0030540074481e18043e10144000c0e51104030a11000c480c52064030440904600184017400a454041075608500e0045900842c488040e003980c41c68a40c08468000d41d02030844054100e4044004015540070340301d8500c40d605007407000500d10301c9071034101c056940140521444440d50b81e5102140103242d1103039014400399540310400c80d511900106e6581c3c081660311541c40601c1d142c01880c1c01c05060b220302889406114811 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 428369910 1250 428368660 428368687
    0x706110d0807030612030207090e0706020a0f08041502060f07030c0f0509030307020d151802180411060a030207030305060a2412060306020901230a27090203011703 72
    0x120400c9107420000c0c2240c488034011400740039107403c00c0802c0550700140304100361380000d0380300499101c91003c00c514a090080c0c10780b20911481101c0c01640580344010120b52101c0661481c544910072130342ca40344e038805100300329650a02c44940960462020800d068030210041d59102d0a903240801103600c0e0010007400440a401004080210110f012102074404104035068550001c20100102005240541030410080600c08446081c1005d842280059501c02c07080300d0790062030448001400b5200050348440200140d80300d00100c80b0380101a100d01e801004c4018840c2d40260b51626507040181c02d407000600300c24058110080c1c2000505041103d200d40243c00580217102141640001c9030707074103c1640c8400e54280303040d130700004004555004200003142a00c5045440364910801004800c00c040200f0420b5010002c1c0c540c0184a0004a04a5007501500200c4421256589005151260000e50150f03a00000601c01c485d902900700b46e460803a600154508100d002185 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 428371160 1250 428369910 428369923
    0x30b07030c020f2e110d091401050408030103022701091a0906150c1005240402090d0204020d0f05040b040c050a35150a0c030e07150201110a020c03070611 68
    0xc003012881c0200411800308242c01140805c3c4482e80d43c16107444100e45940c0082c0101a42102c100011500900c505103041c099241b15a030480c0b071003421680307560248a1821080c2c0003503452000d603840c1820310a0201f0503107501a180320b001c000f42d107940f125001244070b040d16046900c41e5408404008036030380c40103260240e0303030060440e09480f5000061014900130704201c40007070660500d020010a1801c4030100320f00e00e6409035604801703a6054051108a10941d141356810410080d020009030405400074620a5210f900003c0c1c2ca20300c00c84c00c207044510503201180d00c18051010b0105002e83e45200402820040720099a072500c0c01c0400c1c804e81003003c0c011800d88004c1140e40c0c1403100c40e0701800070600304050540d5030705041c40305800c030f0402c02181c83c4641d032450b01006564007403082c45400c0b440c0401c4802858a40d05281c4a02e681e8000307284684115034a503401d0040f0f401010000d0802402c042c1c005010b416106400c041c1004003a8100b481007285d842e00b441055140010300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 428372410 1250 428371160 428371213
    0x1509110f09061203190c020306010603020a0813020102190303020423010c150603120c03020f030a0507141002040b04060e041407030e2514040e0d050310030b07030c020f 74
    0x10b950810050f1407154110701542495140ea41da8800c85456880c1c0c00c03d6102c40e80910880039202e80e80e0301e8000c290224022510f01c0d80c005a02100010010002503610392545401401181c44129000800ca00c14100702c0d54201c00284d00840e081040418001400344100755002260001e080d221000034405041508003410a0284030080d0309180041e0f0f110038003a58011844007006850b0b11000f0300700c0380c1900c404500500c60000581503944020080e41d202850b0355450034034140c25070301d854511040241c444411401a07080c400310402c502d2004200908501e141961120314040000c0c24050610f075201d07020f54105085200401c4441041e541d1004407410005100e910304c0444901c0c001364003010380780308c141070a40901d60340146803c00e07048540c080304039898000c8803020b21040d00c04c6444241c1071030307014040041c040d40c091405140e0052040440e042c1d01aa42d40b0344441c81c420a0750071070013195844001405c5907034140301c10f51842444070002c0115203164241c021120701410700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 428373660 1250 428372410 428372419
    0x1090b040f061e0b030d02010902031009050c1e010801090203010f090c0e030d020708011a030601141c0605060a270209130203090f150f0613091509110f0906 69
    0x7404001c001e41c41c0e00c000509030b40816410901041000c2c0c000040151059041c42072040481c112036052050040808099001c4c000c2d00341e07040c030131316400e0144c50360400031901406400c2689005440f44006412292490102078206090b0480003401e11003068011350340c00c0b0f004000500400195440d040126120f0030400141464240421a070f00780c82821102d90500580000131200ca50004200064500c140f000b0089805079062a04185e03840c1103040e50950002c500401558800c603c074440b4030000a0907c0309844172180e46140a40c003240c0e000c039000c940e90340074802c2d5401c0000c00d43d009070034a02a025404c02881e1f1101d401d101ea08040c5144498000a80e12aa911ba10102038480c07014414295100c3c1000c0d62803640703400d41d10301010194824640c248600400e0300c24950b010b403440c164060040e4a40304144102e8a8040c0209461a6110003040e40043e84900903c4240c0c200b84100090854517403400300b00004060a400f4440c10f18001001203c1d5222020103030045000c84 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 428374910 1250 428373660 428373683
    0x10080906010510140706050a0501080309030a080a09150804051b032e02070b011703030606030a0507091505030601030b01021c3f0b1905011112030106020a050f01090b04 74
    0x1c0044a103000700140004d6940b00c00304039041002007980145001d800c01100a0107141e807213044165490190700c00e43c9034145c0c0180002c0011482c844014480280c407031400d1242551603031f541c8160059001d0180ac00200603404000512100b0300c4802a41002d040300c9003144200c860009680b0040c490888a140c01500031140928000116052501e00d0403002035403100300c141410300e0102002d20615041240b44050344406ca038001c41240c1c4203400c01087c0300d0454aa01c5c00b910000c10300206030400303011602c600071610441d03209000841c0861135882c0750381c03854580b0004042e42c4007107019a065620000580002013031040d41050340c8020744c039201c0c0d445010401c0040e940c204028607008100c0c508808400c01c1c2007c20781500741582c50210a00410240034280a18046800c0d804100e481c514071080c4040c0d807040d581e06000e14400310445013840016130308a0710030380c800c3e0b11a0307001da4003c50030401046414004c210300ca400380c50007001508113035240c0e140d46102c01040141031132402c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 428376160 1250 428374910 428374939
    0x50709050d0b0a0e070b1c020f270316090e0d051b1c0305041b0806011211121e07080705060c0a05010509060f01150f110309180105100809060105 64
    0x1d6000301400204e0344119500c0b960340e89035000d0030741e00440e9042820681808040c0d020f002500845084021084050b86403040f811202007030b070940303680e409200000802c2d20300030942d000c00ca601c22003000f8425090056160a0050007121652909540340c1d030019400305842c69084000d84040c40569854200c0d0201000c07907450501603000d103501c14000300404110020765243d84000e2056214481e040900e2001c0a4060843c44039442410308aa102600500800b015043d41100040c400d4841480b5411400001076007845403600a030382c194402c1506c0c950302c5060003140040e50441c40050300c0d425042512013910352a0074028180140c0300080c3c241502d840801c80e0450f0f250300680200001d0411521250325480240c0710411181c0c9950008117604041c08003c0000c1450b90711490102c0160f01d40076240703c0424218408640824084040700d505c03402083d010784045c07012000301380d42c140010485409040040d00d0100a0041d0402803d42400600070b0b040d44d800321800306101580 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 428377410 1250 428376160 428376181
    0x1303151a090402130e241e0c0711060d020324060702030c04110408030414040b010f020d031505030a03030e010e0f0a03080c1e0a0908030c0c1216060503040303050709050d0b 76
    0x40086c0030300000380b84103100140100700c1c14418001c501d000400c82035080d0320071100e0702c102c0080d100910f4034401003203281e0000751170084200d181d00340689602d04005c40c00280c02d0480e003080710802407102400001d441c00301009000244008401c0303880c83d050107a2900460b0751202040f1710580159580e540c0c081b00b240380e031400c4d01d000f4007540d800c030703035580761180303940955010b08003002070180d4144580c0307624a6000308408045070480ba801024000d894110490150520301400501003010000c007040b0741c0c8042c01246000340c000d441c08107420038000002030840d800c1350400340543d048508140341c2d000c808202d058203503030503241600c155120100141d8044c803403a2410400c0c42440c00c895004036035400090200e01c0380503154240300d1030b5070780d4103a52a445a40d0900c1c0706038000d001c000039140703009000c0d0840503101c031007165203085068400070907a80d1550440740c0032071008003c110416a00d8000d4540c440780711f00d400e006203481c0c4000715200b0246050014419203519001600c802d51 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 428378660 1250 428377410 428377423
    0x2060904060302030303090703110109231210270c030212010e060a0b010e0102060919150e03041e0806010b0a03020c06040803060102010c090b0304081303151a090402130e 75
    0x10004c1c252a07503410521240b995580251108aa00e004243c00c0943c2c1907005910300300450301c0302e04441c1c200c0c0183c1203010a07900c003110385d0a580304403000509900640c08202d0f4003c50340b01d000c00003034014100c220401c4035040704044031141d8244015000300081401c0b401c030003200c1c0d050310b12a203c1d02480485a01400d00b01d00e009d8060300c9100100441f4140540000c20805003e880e001e5186044000480c1c54040c1265445100d6003c420700302034800589508103c0c0300e019900b81170300700f054591400260381154410b8222580301007424424421005120700e4030b000303c4464901d81c5868110000d480343ca051140b00d05920340454298003160080e0120f6070704d80e1200c01516541e240034036000c1615000cd8a25078015032070144000d82080c013803940c1e10181c43c0c56880d4503080d5034503640d070316501d58000005407104090304a0000002101030a90280d0403a0321000854291000c034002e20740806c45441161003030301d6000501c40540c0302c04240003850b00c200c1902146051510840303518128 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 428379910 1250 428378660 428378663
    0x608071413030b1b03040807121803020f010c0803011806120b0c07030e030d020d12140f060d05070905040317070503040f02151209190b0f09011401060c0203060f0112020609040603 79
    0x210000108401c000687e001402040c1c450f10b03107600c10840e2800c2c111000350901e8280c0092400f249801e00162034020710711038100405240a222120740c0c0d43c0c411209800a0b480180e90350002554007000d100b250140d14058400c1036a60042c203080c0e511081c6131140c1c0a001da41900000040c000c0c1410310070301d074000030008081c0848412507400759000355209507150340f203400101c1c005040100c0ac0754500600d4403084e0710a2005589485282c1d1108100c074001e40a030794402c146104030301c0018000d1262000905041c0c00009940c6014103001d8120380c404040704040e0f600c0c0008022003150840156078000340c0011b0050080061032000c1001c00001481c1f0444c03e0384007203000e0003010100d1269511415034882980c0300792410625840c0c2000c188100104480060800180304441c1504012341c040c1d007885c00031510f09848040da9550903030a8100744001160243c480d419800c040003004d07000031720600c52040703661500344003110541001100034414400050307403113140e40d83c0f034000b900510b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 428381160 1250 428379910 428379961
    0x905090d020d111222050f1e12011817031e0414031c1104030c0e0c0904090c091b080c0c0f0d0309171206010f180608071413030b 57
    0x4c140c1c03184514000080e4882d400070171944c64002048034100550070307440040000c0c0000c0342d42002e070103030581070b1444000d9583c2c0105043e042006c40d1b0b00c09024941c002880100410301441e81824001018003441c0303000000385804000307012529002e10005000030915030580340c3c1e5512240f500c000d0740b2401030b1000040340b00c046100290042d036208640d1103189050410040201c0a0268a03040d008500c0080d00455080c40f007007100c0d0b6000710040e54041c10001a907448d000322100020204c802034041a5403408591401b07110443d014894811f820569202081018542180c02845c051004006001c00d82c808a5619000041045802d11a608140641d80c02c102104002070040030684410ba944400802c01e4013821040c2c5011200074454010003070038166916070064500c91400d440700c0e810040c103c02c03040301d82c1c2034108441006d01256692a80a41480d01005000a0400100c001c003890104108580641104001c100302c940c012858481c65645000e030f81500464641138030580e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 428382410 1250 428381160 428381167
    0x2030c0109140c03120d02030c19030516030209031e0a051209011e0c1e050a05060708070905031c0302090a0303030204050109060503061c141203010905090d020d1112 73
    0x80009001100850700e820b03100302c6086500e003000f015074644074003a403c01c030820100503044030b42d8825002558000d01e040013141c80d15072903884215554540d9002400040eaa400a1002c4080b0030000c2142010ac80d140030340c180320319800020b8039514554441003020040e1141000e030400140300b50b0046940007420744080c00030201d10280203034001b04d907031030010b01c180760280d00228034200c194103254000d03a00e065002c010399940e4015036010690074002d840d081140c12000076020000c42d11110700c600081c0506007044400078154000c081c0518040c890780340024011510005000c400d00c0181c10f000c402d880c1c074441e409500a205d401c842e81d401c00c0200c000803040c9a0980c005100301d440c02c0c1d88040d00607035142c00c100c1d010b000030354001c0c0c0e0020440801206c4000c80342031025256000c0e28542003c01840c2681519004111070350002e508000301c0100540d80c1944145540203907000081c00e201c2d02403000c000c0d04c0742c420071500700522070511000e00f450b0320704000c0c55014204010302c2596 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 428383660 1250 428382410 428382413
    0x309031218020a082107030302040f14041a030a0f15110a020f0c060712030f020406030b09010b040617100e0103032d020c1c021c0312151502030c0109 66
    0xc6220245070683c05800040000103541200084d4400c240e4071001c0c0d003000d10203034000321460030390080700d040d404c0580a00008c035203030f000c00c0c1e120320007022418a080503459082081c007080c0c410303002c1680252008402c10505540740030030b2610100741d018030f07150040d230010710b4818400c2c4203806e48030440e903141100e481c0c0780003c154001d0592540d26021210300420704c2c80310983d81e541440186800030818043d60001500f01152031000f00603604002c01e8042901810f04c04076002580008000b9803948000c0f601c60074460078a5014000101a20b8542420b10340094061000100c001080000ca400024014500c40301450080e02140340c0501c41540c0d00d0900405c405030f92001608640307400700b038401105801e20f042901105541c0c0260664800d404d007008001d4084824000302d039803803000703c41d0051342c400e1103070462030800c080380c0c055405e0301d0304000f000076010307440902001d03250142c00b000c07402030100540304490301e06d91840f8030035241300d13012400c5008441c070520407582080e40060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 428384910 1250 428383660 428383691
    0x20c060f0f0a1803050f22090f0509030301050d02311a010206060907051204060c09290d0204030609390e090c030a0606050906090f0703090312 63
    0xd000310307010000754030152070b4007144400302c840100e100101003180070030890000c0c0c054005040781c108203103102424110b0040c44011202c031700c04440c3e43d141078480018010150603114480741004d840b101002645055000c0540d2440103009952144180c80c201a08550b110355803549948852031301d01c00e051105014039502c0404200c0700c81c02700b03800c041c031000c00b4854103501050342d14030590007081c5544584050007032071880030b0017280c20080100907001c0c103442c00c0c3c1143c50140c0d106203000107401c6c5000c94018000b49054121303041c904031603190f2051511070018049412150341000507560840d01980d13400074445c1f90300c010112801c3c0200340c41800403200388141c1080c03207000c81181c1c2e00084c00940c01440c0e050510f000480402d441706100461400c410158025060750490b06403200210000389442d10780003040315500c0d00da0100f40081c0c103016400c00e4018800391202816401e158840001f40307034000b810fa400b0160380724000d02c00d15210722140b50b88966412010481d1007002550784 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 428386160 1250 428384910 428384941
    0xa020a0303020106050f0f100e030f0d1809180312061a0c01050f07020a2607050d140313020603060102120409090507050d03090e152d0a030c18020c06 66
    0x4c9110380030042c200c404a00b071500c00c0302d480b00d6000b0107940b07923902c07012000c0c2c514507001408640c046c030610519600c40e5104001c03204001c1c2968840c41405503d103182e4100b0172103145c11503140c040c01c0820764031200e00743e80c1d410308640f0b0345420041148140307408058000d00040e0710045000d1225003100c410305c01494000c1c1044100507000340075030380d80c005074440300950a41c0d150005070b00c00324020001c200644100d0f51400040c88690100d80341030304108a87d0f4104c45c80c181c61640084486060180c0c116100e1900b01400c074280c58114584000747c885880e400160107030041c80000002807080c1c4c402d00100c180b417880f554031591210b4450340302000508034030404030742a1041500201d00391521420321408180c1c9680c49507003c80c00c1100c2c1c40c026440c0901100340c0300503030328484100396440a420200801190403841d200501c00303c0304440300ca03e40c02d561402400d90002c10710118803400800ea055418059030b1036080c0c1d10003203800000f4883c28000c228140075480a202545000c80c41c40e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 428387410 1250 428386160 428386169
    0x803010e09010c110705120a080414010f02190212030d050a1b020a0b01030f0302030c01050702060a11071518080408010f1d07030308220507082406040b030a020a0303020106 76
    0x300070107460500c094800d542e5000300134519521411040056103059a10500c0102d5031100b5200c0d041e03000e84d948030168005030400399140810144101295034013054034000c0301800d100501a0221241d0a040e00816600d8080c3c01600400405a1041c20401c2200e002d003600400c01c10691501ca41c11a0040c20303501e01888444041c2007181032050710008013961003540208ad1005583d2840d610180c001e042600300300c055010502c40758144110a1003041e1003047c0c903030040d03d10351901d903000f042101d0301094401c0c0311607002d001c1000400c5205824101c03001143c0d00004500b4215000c40d04d202e81e0340c0c440201004d0300080c0124540b00190012051014214820f01c80806032114510203c0c080c0240d940c1d83d64001001000820f115500c4190408215510b8501c040c0c1070050b0304091240c0ea040554455022210800004004125002882a120300e21b5988050f40c40d61410000501812580c481d03a1590b44008450783c00340500140168000c0c51060300c20382c0d91030064040c0010340328 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 428388660 1250 428387410 428387413
    0x180f03020f01020406050d02130503070b0c010f0c08060409060618021b060c070615030b0a0c02060f060f01030510080d0f030c0905101b0b09031b030909180a0803010e09 74
    0x19032006107005009a03800d41d050b680f40c050034161100400c030029000582a9910100410750014440c1c509000e02c03c0036011200f62299940c130044d01160a48001c0c40c03003038041d146842110010140d1000030700e60402e800711408601002c280c108440a40b810f40c01240e030040764515107400d49205030b401007070025407680300070026180840110761250001c64000c0c0d20300b00108140d0000030714a0b4031984158100601014117142c80ba12940c5981800b00d50350702017203944031107031110b1540421810384d2003010181c01303845914122010400000c16208101d048c1a1103202061413112400711030380c081c000d2030040b5520000c40c80c40040280400101a90200340b0702810403440510a00c40607042c0c980180260005203402c240032203000100910003022a1200c03000d200001da00705003000c0c003e41e4850000c5131170b401d4101c072003001d0b450010301c190b50b60b90040065800d40e07200c111055522000b00c100540980703808800e921b040c803001d00002812041d00000100e150601c0340c04042c05800d8580 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 428389910 1250 428388660 428388673
    0x1023090a090203060106141e040612090c05060c1f0501061706010f080606090d0c0812030105150304030c0f050105190207030e10091715220204050a180f0302 69
    0x605140c2103031014a000ba4041d00680014010706010340c82c0304c01c9440307403508250b15180c401e83c8945210b41c100c0984209000001804000c80342e842010342910304112030080050008542c2c44541c5a08544111030240c0b4000c81e41c20004202448005400c8010001091500310b41118810040100f4010800491108070101000c00e08100d422442107030180c590ba22000c42c1c241c02521201801000c40d1741c480d9040000ea07040342c41c0c0342d4007410b00c648a64141407545040620345401c00881c001d48100780181400100b1244e600c10382a840c25910362000b003a50303902c0d10f060448282d5013010000c0c008d900d00100c094200101584014402c02d10004401411146211000c0c1648075005c40500010f0321281c009806103410108640b0f401da145c10040b681a40d9100005130030058030700c03028170642007140c0f0314242d00c2000101e00d40c4010b000c20401403a8040e2415034460640318800640070f5543e503000500703101e03034540c4241e07d50351890444001d003038428901980704c0100864102c006010340d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 428391160 1250 428389910 428389921
    0xe240108060108032205100207141002120a020a08130e0a0b0105091509030109031e020f07030f0627140628020d1107141c0503102309 59
    0x4101141601e455102861401c42c601c178a82c154111600104100714800304400140c590b62a0a800e20001040e00500080c500c0c2110b0008003044000c06140548120302038210521303400705040180820030344010382c84111006040b46000c00c003100003400c40d00009522120441403103e150b040720860f0078480800d40d1000000d030151842c4921007404102c040c41103103903034178005201520306907050385240c2c200018180082d0948025000a40105104161207540701c3d10f0701c641030b02219400c0c0003d2900e1816803580f2640c44000d480094207681d210460380080005039040300c44c0d240006450b8071080c00c0750001c5129030107140c02e01120300036a22000c140d10a000410708502c00d0952401500c9440c0079103020070500040712207280d04c03550342000041182941441041805c2c2c060040b40380c0c079604240350035540881242c081c1c0c007a541c0050020490b540d80f010741e1004040e2a482d00a07140d44a0180b81140300750103400842c400031441d00350300310860010203a050f022804480c6161141c581 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 428392410 1250 428391160 428391163
    0x12403090206120411030d03022d250606030b01050f0406150c050a020a080106030b070801030b0106031a10020607030b0a050913140d020304050117190b03010e240108 73
    0x200e800094120800340280380c5026000c84805034424001d00c070441c01e440c818400a0b0400075600200300c04280d010034048000c151a400c0745441030b0074070000c5039940c642006405440e0085040480c8405403440759001c500c82500f035400c40304c0d03074080000d01c000360312403529902124090081a021701c0c030800d070322802c500e400d0003080c0888502011000c8c80d4180048116001204804241c45a1080c4038000d00140c540c65108002080e0300c4000060f1f00741140780c01004603101402210401000000500100e040c1590b2a411500c8038240016404084042440c0b07003403180c4490360b40b00c440c486000d10015008281c0e2442042d07148e5003003251021200c10489510000d00a43c1d0b040100640000c00034640f100112299030b026400c1e40c15400b80c03000d0010310f00307207400030301400580020404001550704001e00ca5000003049480101c4c1c4d2410349480d40c030f4032080708101001140c03110921503e0343c8007980325241311504e120664105c05078850301c0e9604030143d0450101505803100c000521441c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 428393660 1250 428392410 428392421
    0x3030e0102061506030903071403030708090a0b01091a061803010e030a0c06110f03130519031b03120c0206040203190b070c0c050406180c02070503030f1b0303012403 73
    0xb0800f40c20741d03081141c100b030004981000344449031510040100301c01213004c00450340144440d0350f008560f2464401d4008000c000003070700700c0799140c0c0aa15036000044178107003164152082e0b507100241c0c484119078410091132483c0022900000002005180254080c2142150031402d5000b4040e022250845650741d102d03803e03c100000e0902c0f40403d00203805da4124000001d040c40344c090604c4406002000d280d8410380b0303905900c2e6824080c2e40304102041c0072045901c2c18042c80d000034000d20742c4015008944021500203041d022140140c01c260064025002c0056505402c1200c1225030720081e40e40c9100b528164131034410b19444110491742060317002046c7d0340c410f030f01030038985038140300342e40d5840d400c1000c440c072030381030f0101280c540c44902ca031900400c00500381c0e0740e83e2180d0140c01000c8840702a0900304540040d04240510b480c001300b203c0075040c0820b240c03669485061110034610750b031025400a1400004000905560075001c1c80d01010f80341c2641004440c0100707000c0e8102c50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 428394910 1250 428393660 428393671
    0x9060219021603080f04050a0b04080c0406050604030303022214030f030c1f0e010903050a0e0a05010905010c0503041502060601270b0a0e09040305030109060f05090a020c0a17030103030e010206 85
    0x641c120070620002da030344c4c00540484c3c2c502038100c6003015220b9002840400154001c10b01c00380000c00c0810030024108540e000c1c0d488280d03000c00105040c040400d429200724000641455000907440c01210406640091900c060080c4c020f895034640b0300b0081485119401c0034481d229a00e00b0150444022045034113407401180148100c40d541035a5425000044c42c680d02003941d6011350302c0f1803078000c0c05101c20880c4650350b0643d9a1800c02000fa200e907510020040c066031043d02d0510469800560132015103000342482080f10b4281d28140b031541c45150070901e0700103161130a5840380e81d000504140140003d0700d4040c48840c9428841c041c0720580c46030324407518100d1604105179413890005100d040f1032840c20f821690700000215a5200080d5400c0300003c80000040145117801d210700c0000d4803c03510f503061402e06c3c00001a450034809840740b911680c1c00914005503050800078103000706e074007c061100d02540440180e001750402d200c25804038001072800c0300150700c08a1000d1044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 428396160 1250 428394910 428394943
    0x3090f0115060e030a08071a090f0703060213030609080403020102010e370b09100609060e0c0309011d0a020a0e06091f050310021809060d0f11040906021902 69
    0x40d25005040b1601e600100351241c00d0301030800900c003c2004900208003a40c00f8039660005031204840b2410402c07002801c1c881e09d03400c104881c500409000c9081401c6a400071005070322034504940c04100c805450384001c0800f032612150030308012030200a40100c074000d80007000744801d1004041e41f0341402c100350040c059100203a03d08104415416800100101440300b140c002c003668601c01d6086043d40d0301c159940c041070980d101c82045010f0078010341400e840601c282c924201b0700280045010300714401d16100880012a420400d500c1110881e0b50260028000c00900841d540c9401489000340e00440d401100801c1030300108000c24004e0030050090041552007103442c103840c802110850382c01c520004000038542d6010013401108100201005950311a410b062039114042824904c0c0500900d10412034075960700c580c4181c5058012020b0b080c2109a46460742d01c4041580c040c1e90320614101c4481c003800456405801c2252004420000c0c90807816020380e40c0c0c0718610070f15010f6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 428397410 1250 428396160 428396201
    0xb04120309020d062a14090d0501060b1c1404061a04061e1401020c21030f1b0105060f01030c17011e0b070206040501080408090a0b03090f01 62
    0x14944414506005000c0c50001000c0520741e00040f0fa01c1d000302e005980840d00d5026880340390744400300c0e00702c00514110307403100308024540b000350042d0015440d500080340c1c00b1808410545681c8610454650300c54000c03c0000d488411004040d001074400e031400101000600d425040a48122003481241c018950102d0740c8541d2020080d10b0801c2c40020700c28503800c2666440c1d00e540c0101c030003400c4400030b02030b081c0320076210701c003e10503203640300740e10059111100340c2d0180d8001c10340709640e820644410001090f940c1c0b4001c00030440a2203407080344800110351007042a104003a00c4080c5140c0c030400d030f18548a00203d820789005694440d805101c200311020305d9030107030f403107500300c200a0305082e80392000c01d00c2888070028099000c20b0014204802100026520184c45400780c001c03180c0c0031707043c8202500825101d000d5030140c0d5040c00103800c08070f014043c40d0010790307241e4440200002e154076100c10900d901d0790810382d00781e50385201e09540f040c075000060240702c0c1045044680c0c1c524 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 428398660 1250 428397410 428397413
    0x8070b130311040b040507020c15030103020906060903210406090b0c1e0705060304060b1002060c07020112111603020727020d020c030a0507020f01170f060f04020706051905040b04 79
    0x32682040d204407079002d9942d89005113282c5450082d18410685500588044807145041c4800320340d68640f83c0c1d031018400c10041c00180d8492543c030707401600c25034801d5210401036020a19003001c08040d111005842c1d4550071110302c100c170041065400f19a02d124015545200c80c982c140103181550390180c00840641d4118000f00d800c20102c4803820742140c01d45941c40021078416402541c1c01d4402c140c076105208140c1c20301c1c5102c0c2e0707404a45840104594036120000e10018090040001c2c100011035000d443d0002c85600402c84541c2001f80e001c2e510a45000315043d200c4401e84110094000d40314001840481e035580e903100c050354500f055080d0340b0034100000003540212002d50703200e076092001100e03031314040000d03200916040e124135613110380c9401040f507071a8110380750b60304100025400700540c02c20180d000d5009002d2000220042d2a040001044500c015888a402610200d641001c0c840030350440d50181140310f0b0a07420f502003c1c654401a614115006002d41c10032001050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 428399910 1250 428398660 428398673
    0x11b06020a0e120c132f04050a1d0f0402030a031b0b010b0a080a0c0504300318080318040c090806090307060e010507170406090206030114131a0d0c0b040e0108070b1303 74
    0x5070454035510400d0311f440c0e103500014a8031700309038102801c07840311051416140c00040310002d810610000300c906003132506500090f65104200c0c1c3c000c080040300f000050b44188060303404040c5e42e5100765034212941e11495600395907000032540303d00280905c0042000d40e04c01e8410540141401c4c0e82756403130300d4100b01c03823082540130407a01660804034101134400f031100d8030000e195140d0711980d0b130300000031404130790f00713400c41600d402588258100b04007110010030076600250b440001610041620400c0c160140e0300c41031264042a45ca0040d034040000a180100c014a2b0b910311403070040107101440102d8508803541240c1140202e0b80c0d06d45016810445112101c0c0d0280c85244003240220a0b54040303400c0782c100f039004011602d000704c031b1901c103460701d1129980217502e080c1e4200503180c4c00c02000d011a20710803101700e01510240c8207100901294140c80c8001e0114120095500d81ea00c00018101c44024401d1103064001e4040101c2d1528040f41241c0a4a0750006065201401c60700c400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 428401160 1250 428399910 428399981
    0x60106050f0c1504200901050103090203010e0f0606010201060618030201050f1c02070b2404021303080c06011514030a152301020c011b06020a0e120c13 67
    0x556140002d2221401c602010484402e40801408200070381d42854540320aa4002c10704e08840c201d417100c41c943c1882d840b0b01d401203044070300034039002c13030780c1100c0c4d0021a00600c200707880d146850055030f4000c801d070000000c40c2da02851007a8000c01c00156210310448030390041c2203125120b8210f280007000550b01c61401383c20599910195145000c035580d88400b1500c120204015550707070003040e41020b0069010100f544032404d40e02280880800c0c001d40c414020f02090454416a80402c00540107112210300030007556010001551317403000007407a030f941ca8000340b15000204541c0d0b40103a08003440340d02d140a070721000b50005802d68603541c040102a00521511110408801000080e40900c8409509107030001d4800385140c240000f0009052440310005181403154085840c1640d542070001c1c04000c9070000e40c0140c54204440044404514407122654400a44401656201c4020490344000300e41100c030601200310105504098400f03c0000784660021801040740c0119070f40e848 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 428402410 1250 428401160 428401177
    0x9031106090909060717010503101d030a030501050a05040b030303160212071b0b0c0d0e06040308040806070206070f090302120703170a02010605040608120a121b02010507090806010605 81
    0x40906101e03450340412000c51045a42c42c9081d40076009005041d0340081b21032884022a40c010a070750741c149404a982c03041d914802c601c02650319400c0013500d000c40c20314098960a40740a40765075840842009000c2c05080c02400d110340421080091b1034a018032510209203c0074007e10309503525420840056118200d0307250550251800d044104808031004000301881403a1203102400780c0450981c03050101d4001401c4c11108010110300c50780001050000382c007851511500881c5c40a02040450080c5d41c001000040c0220300403462910100d4424031441c0d4540c01c48800781e40d554401c13180c11810380010070104a980d8020310150600b04101a5202500400c8401c400d45d03030381c0e64010712810001c014111510206a02320255428011000213140882d400c0c000b403428044865280c12070043c41a18034080003581086945c01034031010001014044100603c503040c201e400c190004603000500154648000a1201d6001d803030803d050714440e00c02024030f40e081131401e45003030b4000fa00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 428403660 1250 428402410 428402419
    0x3210207120f0f150506040b0604150e1009061404050a260d08060f09092e140103061805070611030c01020c0a020a0503120d0c170a1409010c090311 65
    0x60503000315000503407209000303128401820313820694400c5003040b43e0000c1c0580c0e109600b00303d03151f5281c0d6545015101904c0e1032040103916401d6125080d40e102c0d00146d151900b00d120500781f03400d130a8001c907181045801503210309402d11f040b504024014403850217600d078004450340b020b0005170020000f80003211072155240b0390100c41c08001c00c3c42d1030144000c0600080e884010047d450070480741040144505441604440c2001840d00e6200c4510b2515810103415060304a0301c94541031022950705044141e04005001c6202808240800c007408191480c03802d01520018000800e00b21020341c0e50004003a21409081100071907240400c0003140c446848184101c040e5808284006d10300c1c00c510400038207081100c0c0c410300c582c2e180c0c80c0d444940305e034001a00d6031641d904400200c0d141140e41d0440001c06a10700e68060311b09080307080804c000f550303a10040010981060b84000c1c0c1a51051045140300e960f0346103e03500781e5440a039000300103440000104000341544000e904401801031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 428404910 1250 428403660 428403683
    0x1c03060b040f12020103111b0f0f0a0809041103010f0608013203101103040c060302070c0603050603030d09051e010c1b0204060e0408031902040302010f05031008060a060321020712 79
    0x200c2c200302d82010391001448c48203202c801428071002c0041c11004c0113a140074100407050200410340303541c40e4090203131105000041409056955521140360b0b0001190350b9500c81d40c5950b0181907050b40d038060700021521001c004502510904201c0345080d503001d540c4010601c062128000c4603190181076a0140700340090048600031501907002c41040e0010b02907145d1070715040500354510075a00c10000d02d881004640b000c908400c051209540703103800c0c040b4907600c4000229145104200e48040c40501d804685030402002041300766004c7c88c480c030081c452048040805088071080360303207040443d10300040548400a1110f180e082d0500040c400620ba503541c07142c010280c041101c045800f40000820010703051800d400800310149008030071800d042c2190b0010b07000e20795000c0a10140f10001c000180e00c00b80c09119032024011040a43d12203083c003080c0823000d4805800101c4149202c0504549160002603514030740c4180ea41c01010a9131500d2012010754020301c80985507080c500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 428406160 1250 428404910 428404931
    0x1c03030f020c1f060b071415100608100f140a031b150e0609060904021b0f1014150102030705030a08040c08011407050307020307051c03060b040f12020103 68
    0x2803001e4042c0204480140802864408440f50b80e10340100c981e00429203803883c02d20855841609880c0800e03800404016003440c203880180c6417041c40c080846403004920100300f610013403c3c000d00101c564a40b82c65000f5110400f407211054040d01505c104403444500400504003094040313084440080e00c0b4901d46030700d076242c1c2c8190020480e00034410503070180301001421b0742c108122800c420b842c6801000f608040380010034600c11340701214030441000ca4201c080c0d80d00c45d41200e8125100100740d80e11a184242804e031200a04e5640d104c80340100240440c04402900541c402000500d00340000c07580ea03550f206520081d5020517074110301c800e001c41c900144040000f030140300707615100c05415181a20b06080311a0007500911000c1e410140305a6008041d0080c17141c101c0e24500b0182e46903503581c40101c1c030f107005002024080e403103003071941a0340010f010401250b91101e590140012501c0e90507018640c4518450706696090b5204100410301e000b83c4001140f0307205150110b00941603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 428407410 1250 428406160 428406191
    0x302030709030b04050a03020d1409010509010909020c0105060a090902011209050703021017180307031d0a09091407051825020606030d1806050f07020d050604060b0f1c0303 76
    0xc0b9021505d40d80184c4c040c80900d50108032001c10580c2a192440760805007400e507848074080c05403110f040c03001c00b01e03070003d95a01818491003c0c03c91804c0842d100c600701091140603000a42e600c50107015800008100d0380c46130300540643c983c041e102ea100d507080c6542c91100422a130002982c40380038102c00800160354541c2c1c41030000005540322001140816080050140040c0400d0704400312003c864000100201c26101c042e905400c0103104a604078450702c0410510381201030303225046180200e0040c045a01041c445070003121820b00d5080c64101c125502c01d01405500d510400045404140382e2002c05107507405401540f1054411828a0b220842105481e42c00c00250b04600c04110f8a0f040400401805a2840ca00750221a2000103c0020307580640155020848000358100e011003404003194119503018052601000c018107286494410566007120707440c3c10a17000a1852801c000707401c00e0a00010025141c0d6810707205c1410000c0d66080d030440505445201c8092040c10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 428408660 1250 428407410 428407433
    0x50109021e0d021e0301060f0903240f1d07122102330a06030b190209030a1b12030503010905041b0f05040f0e0601050f06070c0609030b060d02090601030203070903 72
    0x8940764410f40345c0d410320301d005e0440480b0990b40410800e049c10100041949030b01d01c0d0400290541c0103060a108422450380640815011900e080d07091030165031000e0000000d2160302400142070761520340d260000031490b0049154007501101c001907022240c82d00c2c0c00110010201d450044038201101c6180309000040c003000c4e00000300b0808240d4564800485e200741c0e074407103048030b0304101c01411962032000061014001e0064100342c0c0003c105040c0d49641102d0344800c0050403107011400a180c40541d404800c8148442c0050303065000803ca18485c01400082e54161109400d603030822421900500009000380d0b01080b0508182d1030000113081804060255441a4501c850400d8140801d80d102ca040c82007019160040001624002043c4030341540d4003200c40c82c1e01c1c0130703006c00061818020000081d00f94240e4403000a44260003c404604480c46110b95441f1036680c00100b240c036542003180a0741103944a000203c8a41c030907030065900241d00d0510340e48064603a128a0302000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 428409910 1250 428408660 428408707
    0x1009050c040509162003040f030c15050f030604021324020d020307020108040f05280510020c19080f0a020a1515092d0c03050109021e0d02 61
    0x4400080610103400c0c0740a00030350040300341130744078008800600002c4c502c00c1416210310800706900c00300301ca000c40074030131100140300745909182640c0d01c90038801040c055078861100300458508014020701e00032415a143c081541c2c00c0c090440d503ca20900005e54017000031240071802c2c140000c59580e0b841480e54480d861041503884e21401d000002a03c0c0122040b104001d41d8001e02544005070b0744a051a903109038000000703100700c0a01d02d0322a1404040c81e01003800006800030000c240c0d108844924403440c020303000c0f00c0407412011211400c0380705413807041e40140c100303d50104142901c2c1c10030701c2103940b00d07142c41d604c0c2c030549500d0b030070384c41d0040c40180340160000c05460041c08241641c05602403d540380810417074850f140a142e11494a01c54441e0b0a91940c2d00301c0d5014005404207030180b02c1c42100c9900f148520822003000b0301d0b203c3c1c2410003091800002003400103d5100f0b130742450310409014000540440c8240030b8a400503085c3c8210f980e0200140d80c00f1845074043c002010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 428411160 1250 428409910 428409931
    0xa050a0b0a02010506120309040b1c0506040506070903030807050a0e09011215410414010c03050c270301020406050c1b090f18060c04090c0503060f040203100905 71
    0x200100e00340282075a2014000906c14082c0c8504e00a03068404800c030f0b6a131400817540001d4211504011900b406500d0050b51859178400780c090f018400c000c42d80c1807103070344114191419591190020b4402d00868080500080c070070000041029004400038440e010203803c1c4140d038140d045001070b0b45802d00345c004100707144480340303401d0030400c0f00d40c50803248404d005800d0090080004100d0701301040001818481071184800350002140000240f1080c0100034000b826840c3c2800c08500c51200c14403080e00795072800f420002c01030301c00e21409014812050306980791145000d030040c4001000c014401040302802a517064654091000704000c25058942949420705440b18909000d581c40405511048401101019503140a49681e01c2120b0900b0b1030010746801d18a10340506800d0f171900401c0c8900803c1c0039a214046016000f1101f461105011240e84900c08440d60300007528129004482c0e540a00b0b50361416070003540c0c6c040100d0071820340956445040206455050714001e885 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 428412410 1250 428411160 428411167
    0x21023040c2102180c070b0a0b0f030105040c0510021203090c010908071202040908090d030c021f090504050901110403061a040c1b050304120302010b09060a030f110a050a0b 76
    0x101c8507058860010b211120410034840700e0035401050254080c140c44580d03603d90000007804c200340941c1500c1400e50444014035481c5846c0d0b000030010181030380661320030521031008400380c2c80c0c1409030382d00c180c1e405851040d0003440c00d8140721240d0303642c002480550184102d003031807005070300026610039255140101081214203001602c540a10380052160360040f8000340102032009800100181e0705440c00622907025003013100c514002d41c01c0e000c0d80000d0701e2103401c00741503000c01408000c9001712031031450301a040092050717607103102c952800400c00c8003004100c41c3c40c05074041c0c4c0e0301007500c1002103490181003013400f606601940040742c00c07503a6846441c0c5007004103d4945a824026101049030b81d4290001501029491300c1100e40303c0305608240003000703000c2c41a01d000348040100700c0600120307071a0280c042c16102031110300410b103c4001440c94130300429101c040741d81016490b4811406512802104429003000c560050f100a000241740d4880c228141c00034807080b80640e46 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 428413660 1250 428412410 428412419
    0x1c020f0a1e08040c1a0d060305060a050f2a0c0114070f020705060412210c0b1012120e06030703020c100504020604050d0c090e010c0908010c021023040c 67
    0x10500071000c1c990030010b096080000007403050607403800741e80361002c91001000290302d04008a00c100d00c030102c14035040c0030000003040000548240500e82824007806190382e10480d99000d55012200b150600f51030000c00002415000440b00c480340c0d1741513000c3d20b09114809000e0030f5501240c2c1d0328650400e55420040c0303441d400142a19074140520180c040103280c2000034445004500a01c1005c00e0225030440400100f4122410701227034401c00d111910450050250a0f071000c07180954540150310700003480b501e00c540245040e40c042a443c50340120a03a01e40030294114080c511040c0091040c0b01d1010784d0740e400c05940310703405680e00565117262410360203082a50710745000403050b0400d0148001a40d8a00644c1c040c1c490aa620710031020032824107014100c810303400240d5031480c00051102d00c82c0d06400088124005880b01c4030695540c800c2c490032901303880006001604164040240202d01d0303040720f5500036582126805013141c09641660440c0c0c2583c1c121442e0860700001c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 428414910 1250 428413660 428413697
    0x91203130f3203190509060d1d0c01090510030b060403151d010b0a06111905010f0c0804150b04060305030d05010504060f06080f07020a15200705031c020f0a 69
    0x908120714051402d013850204074125000b400303c1810180030002c1407015643d201d4006540320100340200501040c0c0703400f050100c480b491403802c031844e0b00400200000301c1d401014004100c2d85c02400900c41c00c00c408804a004004131201c2680c820b40c200000008100d080c444d00101e4091445d0001d684000004c120480d4010320403039030703d1641440d5100301e1654400f051542100c0c2d441c103112082c901016042ca0505d4100b04108610383c1142e80f1075014418154041d90224006c01d104001c0b5402d120015906000704540050038080c09041016000c240c542094031030040c041c0011441c140c4035501c1c1819078005a20b108180360307482004102c2480e02d40103600c010001c80a506580d01d05262000700400401009618844a03a0000c1070100c0d02c00c0251045841c1c00a401300c1829143c0c00c20356001d0f1013031507a0080b10320600468203900c100c0240450362000c0e8420010b518042012078901d000c00e00742c03403041c0b03c041c0d420310480032500d103c80020901c000c413580e9a15421914800c121 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 428416160 1250 428414910 428414993
    0x25061404051f0522020103020c0f06160201020909040f0c030c0605090f101d0f03030408060a0b01020715110c0a091d01050c04050d050304030804090f05091203130f 72
    0x701c0b9081c01c110038040c854032000c22042c425084403101038620030701400160081c0c4030b0030701201c1e05032283d40800b5082c80d00c0800d00030b005240d9204401c4140181e2031040f4203034015100000d43c090310001c082000a00c26152880c00181302e901e810b0f100f60340d60b4039046240460781c0e205001051000031900858a1705010740781c02d00310115020301c100d088106000300000001805406c008100d9102d0f0329080d0380f10310b5207485a4500a040b02d9850ba1201e0031151240001c3e1102e070821810081001115070020849109603210902040701032200c1c03440c21690030300304900d00e0708140280c4400000b00d442c1c43c010341c1c0c06005903aa0125021922100500720070544480d0520503925000c140040248928111411141c003120b07820400c2d216410500c0c11403145900061181500080c005180c0c6113075006600c2c1070200c0b0b80100712603915000c2c0d85441d10030600651004110400009403906101c1d0600b0100724052907290940040e01e03500d45481c61141c40b840b0700480d0b01003080800b10241501003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 428417266 1106 428416160 428416213
    0x71412030f130f06080c1c09030908070504090f021002071205011a06121f2c07051306030b0d020316030c0603022506140405 55
    0x750241c561001c5032000d003600360420001090707090034651500303d403a03549500b6031585d11070361110a254031405001c0040ca01d01910f169441c03206d032048844662007610792500017401d1480c07161812219603c0688100d08110406000038419001d0309841581a12051000410418240d0030000e05412120004800400140c288101500410001d81b40d00c540344a8a40a0800b8024035106800e9441140855800411103500c0d00707c20a40700c980d2003c0039230a81c2a202c0c840403210079030070b00a62003040b8401c00070920790742c0402c8416030094003900f002441c241f140c091900714030041e40314500c05d05903140c0007118140c90b04580c524945074000c040e03a04034481507046400d4070685010964940340d400301d000c99258041d10890b548031040c110010350500e03502c040344d0200c2840320012166262105200760a0380c038102c9a0760b0099105030003402d05802d0904044824010b45080c = true := by decide +kernel

theorem cover : BRFrame.Cov 428237410 428417266 := by
  have h0 := BRFrame.cov_init 428237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 428237410 ≤ n) (h2 : n < 428417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
