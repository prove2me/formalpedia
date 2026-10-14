-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0380
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:31:06.096095+00:00
-- url     : https://prove2.me/submissions/948c2728-393a-482e-8bb6-254805585441

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 68165470 ≤ n < 68345326 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 68166720 1250 68165470 68165501
    0x9090312040b0c0d02040605090102070b041511010209040204180507031802010518030609100b04271a0a05220203030f091f09181b0c060e070806190e070504 69
    0x80095404c0000c0307030083d4005401040b8009030b00a155030301008080000c00315801850300e89070800d0421705540b41d1034a00c003000e0142030544040d422800b90180d400b0390360064011912035030340d8030225044081035456182070b0341c50f003000300301c0c0580710740030381e1784d046180140041e000101e9500445070369002c00038a14503003c040310740c00c01c203a80c148481e6000d056503000402d0603001c0060840b0803103149015003442540392a010744d000c0802010b806d0000311200c16100540e10613401d29104041c070740c405001060782d186c42048400720041e030109000324001691207044090030081c1d450308504861000c0d61603441032045610780220880100f08080000e0f016004c500000326510640e0f1001c00554804204240c00c14080d1117400d010030140f030400c001040c010510b00c20901c0300c0712040604240200608101441c0511409400c0303021312029031000ca902c1240c0e01c810503a11400182d0710441e1514070401c1c2401400124000c44907807808200c003034240b25280108000003002180c1c044d0000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 68167970 1250 68166720 68166727
    0x30d0c02030a0204150f0b03090a060e0f03070f11060702030a060f24080d050f0403080901170a0c030606030b0102070527070f0f1d01030b04060f09020909090312040b0c 74
    0x144c5036030240c0100082401d2110b0004c0341001c19071040c020541d0090103542e00144100000c1c00d40c001081640560040000200121480301c0c075401c0c211803c030b014446101c0000c9140401045004040c14503000d49003600350801d4640030005548507407031000c1d52684c008000040072994680c0a45102000030340c0011316810800401c1c10401c0511000d040d208000002c05c000000052050120341400d81c9480c0b0b02d0800c495548020f0340c02280400b9102400100c0d090304141d014899651000540200900f0a4034110352001301404048040c0b40000b4180100081c28601a002e0341d02000016005054401d062005000d64201c0140c041d04e51000440d0212070750b5444050214081e050550701c01c1088000c0c0c0f0400303008016040700840410282c040308003030300c0071b4800040101c07a01c2440c000c9490301040c40020064803450304072204d01c041c481000104020103a0040c0410101550030082a585801c409910b17070240e80c000d840f91115040c00a400103802080191f4003c8903450031504 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 68169220 1250 68167970 68167973
    0x806040605040e03030906130503040902130902030114010908010204120b1504050f09060c0301060801092004080309030c180c03071101060e06092401050912030d0203010512010b030d0c02030a 84
    0x260380710f41815001580002061100501d400d1082a500002c1c07208070b40c2c6402a65510030780c2d00d21440c401c1c8040e20b0760100744000f0b9010f40740c41c541d0041100d10820b41d16961110302c440f0a19111401c01808250b08800009400d503040c000d542c01c45451900c464030390100c40d02d40c500c108100401c0403a00000800100038a503440d0300ca920300490520f10f28180d13034a000300000703140440207420b607254000c051004011b00b5030301a203c141544c24070000400c1c0e18014851219448149460341f200760880410007042c03880e800000b81003151000c07012991880c080d207050117401082c2201c4e903807001d100350300001c1800b55070100a50708070600d0300e0040c0d441e0030b05412280c02c4400503008806840d16503020b010701031400c26082a00042d010744051004c806940040200740480084203060043c0801ca1b2041c036a21a4210900c2c168048103a07a90742d084000580003d501c2401154822000c12224114841e4140b051030741c1e901c8040e008003214211080300f07403083c06070402c0407030b0316216008a000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 68170470 1250 68169220 68169229
    0x40c03021606090c060905030a08070f021503100b090d0b04020a0b040b0403020906030f06061e0916030c020a03091404020f0c060f090a05150702030f1603020c0901080d0806040605 79
    0x45034180255400070f03c4509502c0c00300e0075a055544110308100d41480e080c80309650114044103000e503c040451b40e5411686070221100e400c0c041c01039030110b50340b02d194100d04c1c0d0340d400031352054104c00c450310342c1103460b00c401d191345010b040c108540100e03c14101c000011000c070b04503600140014152511307a0381c0d5080f0009164400d03009086d510401050400071401e11500198001c2da0880181540c110b0413011103035145401090948255103c203801c0003a02000200c00140000c05001450b580c40d00302604404d0701340400b01d06001070700d45018030b1101407000c206a82c00c154580e1390002c5c0646001e0f0342e00241e240215020740e100d98201702c04003455060380014807141c1d000f80041c01d410300c1c001c01004501c200040c51000075070003101030100060804102d1009c4000744030049041610b692004174a54000c0021000d620080003c0030b02e201c0c0c01c0300d01c24070382080c40790b030071039159000c40018810302c480b00384101002070384a20f444030200c43c02010225400000508006650b030742e24030000c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 68171720 1250 68170470 68170507
    0x3030301120303050a090f11010519170c070302030d0515121005010f140405090f06180c03150a050402012c13020f03071103040302030619050702060c0405040c0302 72
    0x211041d1019220040c101a014040c5a50110311303e0002c01c161203580d11070324216124a10000c000c41d250300c01030703100f580c0100c0696100700041c1c40340110a1034142001f07841e0755003180840e03140068440001d1182c000900450703401c9503040e4003840c1081c1ca800c4050b406040c0c00340440c0a1594100302c4540c250301d821030044c45c015a9140201a2000c0d805555802c4079010f0700300280c000e8501c0e00c180040000120302209000301650f000070159104a0f005040c51040d10449103640140c0301072110503c0818201200003072000280c03003243e00010109581c81480c00300308002284004006014584154095644140107040005400c020200d500c5102da0318880009508042919004e41c203052514001d20040352201c811890b00551030740c6100a40070080400c001c0140c0005100780944050042e540107640c0036013240c6440c204184241b0412260b582c040202c185020005485a44000740e950b0280d071904c003813689801d0030441840040c10400100c00180340d02000307081141e45091124 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 68172970 1250 68171720 68171729
    0x20a23060708010312030c02030901180509040501090203060f04020a03030f1205010e09010609200922050a0c0503060d02090a020403050717010608070b040e040c15020a1e08090d050c03030301 84
    0x2210b65641c15480c00509a400b01c41d4560109840e00c03d85980541c2c00004a422180c0c1c00d09210b03c100b105c45070750303100444041e003040e904140100305000803c130054001c1020749100300c0a44805545020008a43c50011a8007940c8021035020070030100303014030190b00c06c1c0c10007803078401c240351200110a01540c60a034084212039403c8001c000001e4001c2c402e10004d00041a020301544807801b075000703005c984541b00e0039a00c1900045402d542d0f5140000c86407074518044207113600d0100011010000c060403a2805026070800c441c03508680e01c0751b000c5912490700106400ca11802540034070060160080890340001e508000210210f00c08014210007045035082c440c41c0c041d01140100d080da46260711481250344600401c1c000340c0c5440080d201a00c0e40020b0040031070340d4904091841c040c10f0b0340040c4006004030190f283d401d03800b040e00000c090244110817402941004060144e880c1e00e14051320030f0f0320604c0300c58880d150200300c082d1000c3c05001212101ca0000d00000e003181d20a900 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 68174220 1250 68172970 68172977
    0x3010b1e0a0c03030506030a0807080d060f080a03020d210504111315050a0e011203020715030f0605030609030d1a09070206071103040b0405042f070501060f06020a230607 75
    0xc00302c003090780c50302130190b00076810340180400d0075256a80b03400307501800000500c15403020514130300a010702d5001100074044698000c0c6800c0e69050215242c1c5400c441c05e50042c0540070030046000d0092800b10b200c01030705005151508084403185000300303030280044601c100380420362a0315a03150000b03021441c1c0702200011b00608100d40d424074200b9aa07021034001e2080040c1045103d0343d08520604482c1c2e003a14009080c0340c103180880c1400c565802c4082d01030421400125420390550060548121043c01000b842e510b82d401c1542c0e800048940180d90303030041100901c6184541c00c0700c0c4952890f00211564150308400290300902c04944070801a4030210400540d02d50008030003903102000c1c0c02079850141440c07103e5906214901035075015503100c2d40304403130580300d061010041c0c2c0c3e04000301c000140c0b062004034106a0241358142c9440d1b08004001c24a100070514800840c3d0003500100704000e6250b42d008007050940c51f800c0804502c540ea0700c102201e040c0011031141d0a07658 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 68175470 1250 68174220 68174237
    0x9050a08030d14060f0d0309030206030a0203010e0601020109080315040b0a08031905041409040201360608060d02010c020307090e1e1f050a180c0509010e0c03010b1e0a 74
    0x482200494186480742c2d00f0382204841488002d0700d41140b549500c2c0c80640303c0c00c5944126050581d40080c90703601c000d403c6040002001851882c503800785040e111101e940c0021340d02c510004a00380e900340349018205090801c045041c0c0c080c4010301a803200006840030520000798000503164680b154010406500b0015400e496074a02205101c504081400c04c9410a4203003d280c03141011003100c0540110b640c1004a804e5a0007008000c44c0c0c42c1d00d00c1a114071400303003640d05403c1080c413441c0c4011030900c0b2079008a081802071400911a44014002241094894004688a16042c80141c1e014055810701103943c001c00d0080504454a4100500c82c5c2e10400c0701011030b44120740d1800f000394000d1840c00b44020380e600001c0350a14000c100100b443d032603583c5170600030074403648581460500d03000501d00300401c00807050100c0b40c00f12500c00c0603030b030307101c00700d603580801182c4011600c2c00c1000144240450760780900a07100d5503d60b0300c0310340c081c0e6544007900c03544003103004000f255903070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 68176720 1250 68175470 68175487
    0x1303021009080d080a02070b0411011b170a050705030a02030306131a0d05071512060603020405150a09031a0402030c030c03030d1d0a08040602010608061005040c09050a0803 76
    0x2000010342200041c5415a40d041c54805225140d0740510410810080c010000c00c885a0941c4c0644000a800500d8070501c0d0415180ca01e800d042c03c1c615450201e00c42854210320325244d0306c0c031030701c131181c00003140c050b52003003c034145415901400081d03040c0001130150401040081000d0103001034540c006503941d0402c04204030041e040301c1a401c1d485414860516482c1d00710482d0f22031901c205940e4140e0324141c0e8500541000303426001144e010404100c2d1446855109020b81282030964030100b00540d11464210241e210b1402040c2d0410249a4020300031030510740180001400f502d04100300580303d68994441039002490343c2681d926030406d02c000d40c64140000420010100c0041180b0350142c0c0100c0c3e21781c081c100302190308541d2580b20059244038000d420f03207408104400da0b014041c451500ca07440d500240204070040d0710308003000c41d905000240c03582c09440c2c41042190b240c2d190a0410000d884094085800c000800303c2c0010103895940f450780103812080d01550311480341 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 68177970 1250 68176720 68176729
    0x10032910061218020607031e03090b0a1a091902040603090618050c0f0d0501060306091a01030803061e0307060306080111040e010b070804031a011401050909070305060307030206130302 81
    0x51840c500c011a2404110210500240d4001e9030f0244e03040c0ca83c6074035a0712909059543c0c070905541281001c9000f0044078409600d0b610030418144241c2eaaa0034036194000c0020455590a044080f0700a812559520300c8c50550304496001103090b04101c0d1801c01466090140d03007080d400080403a1b03c40d03107a00b0030001c00b40503041d0340710b0300381004070a803e403240c40d11681c400808456500451201c0703117140e543d807291549500020b810200a2162666a14082c40181020b1100382c07146607840440e01d581c005802d008038100c03500814aa8210b0b2512800c000243c1040d50181c555010500c0074072826480c1441010020101c503180050f206150843c05070a407a40100c2d10038410308100801d0001c3ca2401417001d040d01c04103a4a651900c6c0d80d85082d100380d210302d80011306464200700e2400b40809066101c18165201103002c10b0010540304010745080c05082c4d803a540c01b600201c00500018171035804103610002c0101200c849654030f40100c5c620381e203d19214001006207400c00e2065081 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 68179220 1250 68177970 68177987
    0x10908010207050c011209140c04050906040b0601050a030e0609070f09180807020402120c0415050708160302010b13020d27030521090c04060501081003291006 70
    0x4050001e5140c080e15a4a2030345074410001064181700d01e05030500f0307540c101580004a06540400070f4424900c5604680f9501c04511000034421403c0c507001841d202ca011410394000d542c04515180f00d0703102e120055860b41c002c091403804050b51400c588814034400c204540c021102d01c00500006418404080101c20f8550001541d060900c800440b0506d60303100300d00402600011020744804e02c5d480098060704c2440303074101000e01058280003803507500070000c03c03c07140f40c110140400004003c080c0c400b0b00860101070710944c001d1140d202107002610300d07102030740d1080c800000c117031b4100c0d400581410510103222807103983c08240c81813403040a212b0950071700585500051418014900d075001d0004002005040240104007444200ea80a2821079401e0015002140601c0e043c4407159540d40a859032500c0b80d8101040061254000c0443c0c0b40a410b8840c4150f504900710f46849c0c074084141001500f000c007260746803040b9040251206130003001014080c074060340c40d041d4000d0400c0b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 68180470 1250 68179220 68179229
    0x3080306180601020a0b0402212b0e06090d15020c0c03120403030f1b030e0405160504090e0f0a030206090d08130b070309020a060809010c05071709060708040f050109 73
    0x24407006124040c1c0c4c001606a0b1056807102c403041050b0381c0e501c042004400102120030708400142c07a10f503020074000c22100420701d80c240608a255102c000d03070f10020ba0900301d428010400000c00e50380e0506240e8028500d582000d401c2070b081d034890b5503d040600e4103c1c0d000c4004580d010035074551451061141c0d0703e5410046000b80565680b83c508008035104d40d2000270140803003034000089540c000c1e09601d60303401007069400f0b5001103e05025040c102802440b600c030728074240000d00e82c0303444000004080c2c5000d5494a0030030742040b401c0002005011030001c001d2041d0000414150000c204012a180c400c1c0c0c0a0115070501040e5a45428400481d090504c018601000301d4a42900d0003030481c40c0d0020003003400f41e22081c0056009201441010390440e809c22000b052107a0450310b001c0c012000c010081141c440c004400300d80500480c0d4008040000e10a940480f4400c101d014040c400c80c0186024a00301c60ba0b0340d013000d2603006901060b0405400441002150b0300b00c2c3c081030050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 68181720 1250 68180470 68180509
    0x60412030c0c020a0f050f040615050702030f070f1d13030f05070209041a070206010303021c030b0d050609070f030f1101030213092a0f081504090b01180c09061b0b0103080306 77
    0x21418a448404640850302b9580304200d0701084003025540e003081810445292082616015910369561a42ea0581d500030821504804420007113125002524648640401c040c1d0f48035420b00707503034200d070720720740d00a048803c0103c00d00440015a84400980c0e0096200722001c0c0030f48800401d1610100c0c800a0a1400390740044004001180d000300b048942800d07003c0c0a05090407901c0416001042120a02c5400080061000c000c00100042c50b6000e058581e04488400b41d444010703c0604846000007090150784011090002d0000d04001d806048141809030400c6220041d0b81a60225a070190341c01e240c4034060503d00c0344041504a280c01203a0300051181c000604014001101440c42c4d0000c0040d440c0c0040c0020009048249551384020000d100a4100e8104984181001e0148205422003003240184001580c400d100540c1c0c05600d4020460b490400d0030b9555810250036407401d031101d443d00e0b10001e20040d420502861080e0f10311501d82c20314100780498100c0412184100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 68182970 1250 68181720 68181731
    0x30207110f01080406050406060308040801051504110a050711030a08040f06090b030f04060902090a020405010e09070c1401020702150a1d031b010e04050a1d060412030c0c020a0f050f04 81
    0x581d0740014504d40c040c0d00a00085407070f440d98540342d001002d250340080d00c1e080d80030402154a41e01074002034003c80c0420052020750fa42070f0100421110340001036803107200104117501e482d501030360207000c10358052510364865a16080104c0d003000f40ca101e0894145c9000031701884451803090000300908254a0030301c65140c188807a640d42440040c1401c050402c0d00c1d00003804104c040d4004d1000c6650241c000c1d40181402d9103120702030340150003001e0103d44035100555560400250451045102e0345c3d07005101030305900d422041008414050741603540800c40880076845134000580d180c20601070841c1d0b61240c134600108100241d00c1c03414130780016000e9410590354009048403001d800d85900e01814180800103a41d0b0300200041186c101e420301007005460344595014885025000c460840c28080110700c441d1201c0d030464004041c440c7c04650558610b102c0d6200b46160005800c02b04107188550700020402c66140c2e01a1500c09000b0106000b41e003032410f044003404c0000d0303805108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 68184220 1250 68182970 68182999
    0x1c0908061012110429010509030a0f05191a130507031b12080306030601080a0b01090c090e0406050a060b160807030c17040504050c09180702011b03020711 68
    0x600d104544542e00022240c41404000d10408604a40342c10200800401922464000d6130320780f0621000710507002030340003107080704030b5002d601100c0b070030b0800034068100c00f044d90361001c00404601c503041c0c075070344200701440b06100038840c11161118003c201c2c0000e100440700c504012071000070503882c201c24a025540c80000c0d0002618400e40ea0703c016030482141d070b121081e000810040e03100032036014440300325500384024035000b94002c030b0040e415640d582c0e0722112500d0340c51207031100040515601a0040145018641c40400e00d050076242510441d580c54040b04042c1c2000d490a4a40c16581c50030301a401500d4402c0e00b000f09406420f09040c840460302e581c8141601c20000340404030000b0340b02c010544258500f004151b4040703c0151926000e0030f210f102904980102030283e4908004624456039600a48941003401420f03510307140010031407800c2428002d0800000e641d2514081d030710f803082e5080c0404d038119247d540142c944205040062075125640e80d00da0182c0e1140d0000d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 68185470 1250 68184220 68184241
    0x30f1207210f0e0304060309060506012a0204022109010506010e180c07080403080408010f200c120d0b0a121208190207030905040e0d09180b031c090806 67
    0x10740c00c1040035400a4021410310045014000d200d1480c00a03010008000c110709806034800900540034010801c45640c6841c011344034030180740003002000c0180422088145c6441c1100203e40344040c1c0050700380254014000280401c0c600e0b0412000d202c0c4e030410502c0c1d0b500740706040d131102003480e0036140c41e014103020400217406811540c45885c0000b000501c0030581c84200c0705200d610403400740d0399a41e01d00b04940c190700a03000d100a25424020301d806604c6040c017038000c540c1a0200760302d1500050700f500b1681940508100c81c0c00f40201d03591b00e00c8200c0c020024140300c900ca5040032032029880c4003081426030a036080203180c400c0030101c070004030b050941120785e07401c99401e0080c0b42c0c0d2111040540d030045a40368080d110380c0005944420168000003260071140240d505012020601c203070151155401080e21001404d0301c0c0040081105d0006c12001c00100888002082d842100c0401d041c00d562480d040c0c8400208401e070554075a00049003030046c58107001420040c05c10200d1407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 68186720 1250 68185470 68185517
    0x6050f1807140d0c030503030406090c08030304030518190906060318080a0804050313060905040f0209100e040e060a050103021008090a02010e040f0c030905010b0607030203031803040503030f1207 86
    0x5801100100c2840007003207210004c3d90040c641060440340c481ca020700d840c20180c20303440021204155000c00c001400070300002503c1c012030741615464180b0311030301d90200d03402c08943c40040d132214048006102c90303825012110058800c07844003142041c142007000e006d9541020070200c0c0100d400100c000851140000c0c0d8030056030501e003020b21922981056031a5000c0d04510080408400754002800d90300704900364200d03101075034140030f00c5c0c500036100000c900404600d50b40012110000c44038052249008014100c001000001c91040c031100c442e11b41700d4201d81c1000340d960b90b40014025840d10003401441411285402d100a18080b80c52545480c0f00500003418441e1454842000740d6441e0070111055119010400c82103034608001006800e0100d07090380c09511f010a0741481d81815411070f41002d0701900158516140e562401600d03240c0310061a0060105200125103560188000c1c40d00f04003141c100c685032401405c21002591001e01041c050060005403004c00855400c0b50f03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 68187970 1250 68186720 68186759
    0x5060702010804140a021003020301030209221b0f0b04030213020c030708071703041b060201150e0603010e011407092306070606090c17011505090d0c0306050f1807 72
    0xf003040704d0240204181c580003007a00b0081d40444000000542e40b54076a0185040300d000700c9500159403194442e802ca002e0007092255107280003180d0382d10115040810721002c450884403448080e960340d200c50002c601c0240c1200700c807014009010800d600d403002c2040709040086000310f24206070141c0540e56032151a000410f0504003082210511064059028011524000d110f542c2e19081c6005044c0d407808060121459900c1e1001103241c500c144982406c91a2082c0302402c0c5a00b4506141c100400050031554507641710b00c1c11815001c001e009800040d81c20580002075400c1449014202c64000c0c0c200100501708034060350451070100d1101c0f018220107030f51079079898075103082400c09024182c200110f11400c0c400301c040e401d0303400149400b86007510b0703c40b02c03803903601c5540007084c0014001c03040000410034001200c0a140101c400308145104100000c821652980c0c0c600c203603042100ca046203841400100040d0b100209800e2214654000c00340c0103460501d42e0650b01c016100c0c04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 68189220 1250 68187970 68187983
    0x9010e0d030909090803041a090309040e0a08071101020d18030605070e0306070f17090601050f01021c0e01030c030c0903080d020c070e0718031728030f0605060702010804 75
    0x4a000a1501810710300700502883c02052148050130f0421076403035842a1000c4458844c0346000320888400b03c40c880b070052820102451503e00c401c070030403000e0310012020582601402890400007a6940001c0100905c201c03680c00c1020a80c0001901302801c0c0550325003032010f0350f003146414030040010042600d50120f000100750302d03024001c407034442c0540301a40d00352140d8024040d51342d40003000300a0410740e070361302c25001e4170803130460145441c0199240c3c55a0b9000b07a0051000b03180ca003410005220040c8100d52418000c41d11900b4403c1c001004240891820354080d00c01e942e041c00b4440c820401418240140488850000e009200314030015050b803601007001c0070350f00c0c040c0d0100ca04807a604011540d00070785034000440c0400381030315048040707103901101946400e20304060314200ca4201c41c1102c1d84a44480b00b0704215401183c80c1c50b11105042d0300743d20340a0807811058034521459130001080320121028404840440c0c001c60702c2141b0a1081c540140e03802602c03c1e038429031014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 68190470 1250 68189220 68189239
    0x16060822020402070303050f0c040e01030209040f0b0106030b0306280903030b060d05370207080403170c060702012702030a0203060f0a0b0402040501050901030c0212031905090309010e 81
    0x4542003005020100254894000100b4000341540b54228070b028070107102c00f40e0307880d843d81e8086800341d200307602c1100e55441009004002514061648036809801078020300c001c01030310f9443c801a020260807800101e0381c0e5000484050034204000c0d540514411040440b0316401030700101d8113103c00c1c030656501a11440602c080506c6a003010034080005040caa484104010004015200c1261740500750055107172000040f04404c0050002c4400122001e8007140c4218007400c00f030b511410b01034412030703000c00c4000000b81b40c81007222401400315894a4a401d04d0031075541c20224050034200841e8181070711038041e5000404034107000c6c50320620002e0031148600c0428141902c90102a616010740802c025442c401400514401c001b0f210080004074000f900300030132030049010b051300045007803044020303650285d40b002440344c80c01c1c0125803109803614017007550781d882214611031007a840201901c00034120f003d00741d00010701d0400345003064480c0000900900d81c14940b103200d0f100c83c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 68191720 1250 68190470 68190511
    0xa06050306040f021014030702070501030509030a050313030c050304090e1c0914120f1f1a01030b0402070204050103050d02010f0b0904080310080706020d0f080601080414010b06030406060503160608 87
    0x8501d1034512104413046e0075264541464040d403225010710800d8040380c140800184081004002c54a4a690589a0340d080d074a508400d03084202290400700c2c140b03c4418030340b1000c46d2040019200814120001280c41403c0c00f005900707001c20201441002843c00605114164000b40c0d00c50a440c00d2400c0c00030a00c08a0300080c0c0c62840b4005626414056651104050000420511044035881c14800f9054040c16180c1c41114004100b81200004e0581654115803203078002030015100200094104547d9400180456030280d00c200d800307502001190f6041030f028001c00407000d007103100404c5281c40308004500b48101c010001840d103140000080c498005c160a80c40c0030f05041c004880c080b980721b5001a41c0d40b0080c10000340070171400b0100c0400d03244219400c1e48141c8042e521210319403955aa0311802c1c0d0b1a8085100107552540340342c80351a100c2c0006940328900444001c188203140c4001d050801244500c42e00303603000b04000502c491904000d40c00e41040c0750003c0c264559100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 68192970 1250 68191720 68191727
    0x11e141005040c030213080d0e030607091e05030f06010e0a110306060304020103060e01060f08010b030105010507060903020106080d170a020901020a0305070c05060a0f03050106050408151905040b0a06050306040f0210 95
    0x701d400c6c3c42c91003c2081404203000c1c4001801c90302c05103aa4032204c20342e0190701c040641d03441007100d0791000202d2910713060029408105100c00c1100380c0ba09403200040c0c494000904100844980107200d50007000108010a40c03c00c116030040c442d07280c104603100b400c6d21020550302c0024491401094000085821a407203a84048000c0c420303050180010351315004000e00514030440c8400000f81d601001107101c2001d402203c0c100d034816101e44e45410380c141e959a01030110b00505409555850b800010400010304c451a1586e0b45582c4407902076542005400344210040d00c03403d00300e0310600031101981d070001a01c80c40c09806003011600e0742c0c06842c0100c647d0100d81c00c42900420042074840d0381c50b400500100031904140c60a0140361789034101110180601d01c1044c540307521058010f5082d400707108180f41c1100701c5980c85400110b030070841000f80c40c0c3c1541c080300c40c2c0302500200401c1440a120f148080c00007140904440d0a00d40c6480d10029070703450020340705000d5080c46072001e600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 68194220 1250 68192970 68192977
    0x90207080403050f030711040216120c1202101406030604020904051207030f030506090702121804022a030901120c020129040b0f0303030408090105040305011e141005040c0302 77
    0x1880802c80d440d014000d24013907226002403604031542e41058072003c0d03807440c0900989003960800c61800d0608202a12411190705079020540e081c0520b00b4950408038100c0c05120f8600318950300204030f606107050100c8201c42d1070601300c0481e00940000d000d0302d69030100316540c10580442e202c14407602ca42c180710341015104e04101800307407c0040c40c00200364001225001d004443e44041010741d9480d8240090140c0407038007030005800a401c112030201e0300101514a129001c52854800320702180418102ea1281c0c03082642105002d0b20740400300c46030800080d014413030402540c01d00414000280c0300400c605a5485100d894200c2a04114801d61000001c00340c0d21489102c900b4211080303051200c0011203e81c05281448a5051641480a030384c5c2d040c284094010742c60341d9030340c1d220001c40b03800c1540d486040042c02c200c0000031032800d020b4150f1050102d586505122602c0c02407804490620070603001e00581803081201385800b40c40740f441201e40540700030031425040d070710441c002c1c031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 68195470 1250 68194220 68194223
    0x5070504080a060b090115021023090f0609150714190e100516020f0109030c060f0f0801031505060604180902090a110a11100903020102130906080304090207080403 72
    0x400c50031203105100158104c01e10660065801c0096a602c807400e40e0301010204041e040543c0c0080000c80445180f54044911108031881807070407105400c64025240c034040c1e0760050141d000b4041420700e248144840340d0403220b4100100b9504100216402043c00020b08083c140000c5a00b00104104100100c034401070f60189c8554543d911040050000c842d04900036000311400c50725078010500850850714100508070302c070050780d1000e500b0064511042c0c0100c60412502c0507000001070a09030121002e40581d884501058118240040400c200d45014a00304590035004001160b8004143c0300c926072040008a00ba903200c1020076601d215640c072140b0700c02041503113140384001960040f0320461003101c1c00f010544804041009440008104520600c0100810743d1050300807c091404c120144082da203003020102400c0080303070320f400c0003600583d40015003c41c500c140b4084810181c100490100321140c20140c89640e43d02807400340e050b001d079000800c40140700d0144180c0d802113 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 68196720 1250 68195470 68195473
    0xe03010f020325030b010903020d0609050105010e0403030e2407031d03041701050105151c050408090127090c1404030303140114060a12022101080d0305190507050408 73
    0x900b030400c06102210400454030054103081c2070100354030f41c0701e400755100102c4140c2d203d40308141140c0801440300c6500b10101c80b240d0781c64500800141e4203000e030600a098000114010f413a003403c001d03003a034440c03080d0146203030000301d894041c00c4035062403106190056a01202c84e83c0d20b0f0710098004002e89440074421441c01403a039030700c1110000040060311011504075500c50084c2d0b4125090f100203004a0354402c3d074081c440d00c00806080050b02400c140801c060f06504003580d5440c003140c0050700c098601000c002008a002c0d6000f00b00404051f600d41c006030310380301c0107012920304e40000c0d0203284a5581c035480702040b0b251041a00c8613050301c407480340540c1d543e500d00d8094000d00360400401550040710000069104c49891000350340c580c040e02e00c91800c092282e003240c4034444d01000d01000d40e424015203840c10600e030340280900c807940c50310440d2541010340b45441d0110131100c0200f01070902e000c104008200000d1111603424180c808030f20750300c4404c02503606005981241d03a15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 68197970 1250 68196720 68196727
    0x11030706050f0115140711030a0606090b0414040302060f0601030902060c0106080105070203070804050f0117040609110f01050d0504080403080d2901050a140903011119030e0604030e03010f02 84
    0x211441039803450490700c4100c003000d0801c84004d0240c45007080b42202d1400f4041c28000f900102d101d140c1441c034102002401c0c0e07251140700d5504e00c4116981500801a040c1e6559180801c40c01c283c82480022b0354000d2850006241c10350780207503220401008134080c0801c0001044280c0d020750410050680c0c004e0200c0d8441c280c041d10316009145038480e19203113600700400300d01c89900110031620526000460381c5d18103410207083c455041e020300c1a442c10030075854400c080034004199420701580c826480822418501d00304904043d42103405144942400c4542c209035030707008002c8900c00d000818000c112540c55052662242c02141d0002d8161403000645010860255024a120140c420004021450126056400320b402c090a440c080703a800c200011005002d04401c1c800b082c00301d50709500c1c00e0744000110742902c221510484080c000403d0b9014441c84249045614883c1c80c0f50401440e000b02080503076840c0040d0029090141d0007041c0e040a440c290000040160080800e556 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 68199220 1250 68197970 68197981
    0xb030c0a0b03090c0109080d14091002030a080906060f0f0d080705070806090a08220503030a02010603060f1a010804050f070f0e0a05012d0e0c1b1204061103070605 72
    0x825441242c0c60403450041158501342076006807400020307941d5a4006000041c403c241c203840c407c66036401807a07141001c5c0250000c42d40c1c2c185a8003401c8031540c0c080e540310346e4208005028500090700e0410303180c1004c82000a203448041143c00c0c9100c04440c01c0c0c41c215965004030b05500078001d40900320004c0014802c2c18080c0009154003101c80304011200c0c03a9071907030a0b032620b8008000700103207640d108022441c141c4440c1e001c965110800041d0301511203a40e400000d1955000e9907141000d40d44808041007417051a1080c14280382c000501405484c83c1601600b031403000b42c1020310b0500c010107002c03030203111040121005074550300c1c080742c0b0490f41f07a10040d210303038805101c0c2d0703e901c51070030340095012440360181a0485a003101100c4103450008041c2101d0031481400d0b0f00c1c0c503640803400003004c0380e0842c4800d01440382d00e0301c0c2c1641d030742650401358180440c0e0b102c9210030b40d00405d1140700310344e42c0e0b4088070101e600d02d00c1c0c420000406552079a003184180c440c00f1302801d007008144907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 68200470 1250 68199220 68199239
    0x1090308061206090c0f0f0a081605090603070303180306050a020711010c02180613020304080903070b0f030109090312020d0c030c03230705040e010801230408030403030b030c0a 78
    0x3030151070200c64442e00c1d40191603003150b90750812903020300f0ba500030f100500014103142070400706410000b89558014013600c004501d4400b01c6030f214001d50f6205007004a015040001020f02a02040da04070b0060b160000120341d88402c00d200003800c203c1d210360510f988946400f10040556030104050060b41040f03510107020703402005060f2402000241307010111741c06914000c0907180d000c0c01c90f0804c95210308514040540c000c25141d0809024031049840340300601c02984078520946c20709460b80d0001c0c041c94909250360300101240c000421681600b41a14410b4034111501a180880c41e01c13001e1804a660b071403c1e030782884299001140c4d4194500590b0810340c51030816075020030651845403012410b6a00542d40702006582c0524180d071034181c40d9114541c4036629081c1246400d80e64026a0703102d640c00d900040d00c030395460210b4146902c0c2c0d0080d501902e2203280d088101e50030300b615052080d100140006040c1592941c100220362000d00032a00b414000a1003031020564031030000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 68201720 1250 68200470 68200487
    0x41e0503010510120212100c0503091506010215060102010621020906040b0a0303030e030702030304030c060f0504031713050406080a0c0503070609030f03110a03050423090a1508010903 81
    0x24803950a1000081032144100c078458101c80c83c80c030b1460144801e607000e010b082c0380340c202c081005014600030441b080d034071401030f1407040c032480d5541c82d56860086000c1d030900b0200c0c00c0d082c04003070300c207001e00920380c0c3d0000b003001c0c080c1d00804d00e0204944030304005030300402d020792000c917084100f1581030024840704010b5804950080d140700c034645c0d851604000840380c3c0c0381d26065105001e42420310109109030300101e0560701c0002228580130712500000d05d16001903100f264901c14140050004c10303404401d0110504803410850700b85402c5030b48050f031308548940c50b440340ea0760118242c03100c500c000c4c10f10b500400b0301a004001301070302c43c0611034480e04040c3c016207109a1480001a03282030024615085684581e1004151811540c8122380428500010f50400480445509a50a0a100b540d05440c82519401c0c2e45a01d02000007010300107400d000341a42c4281506142c030303500c2c0c43c000307281d00520034440081c041403040c1010b802056a5000802030703600e840048000c26400c811a0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 68202970 1250 68201720 68201729
    0x3060117010c1404060c0c0506030c090a09020a021908190e040608071d040206070c080d03180b01050918250e04050705041e0f0c08090a0b06120102041e 67
    0x3880360502c1c084007650300e500010070140000c4000c110401c0034a20819031501d24503c150a0034940c1541e440000d505030700150781c148d0780880e0001d00400d00380703400f0700e0040c0184004801941007001184020352581c0da500c80c000c081030350b00d00b005001c1286540440b40d20b40702444080e041d2034002d50b402060035540c2d2480307074003482c03500d6404036880d1000100d20085030020110741c11098207402e00380308485000b5004a0300814284591800554121340c0d03030b03000e032440100500c040240301230001c0544004010101600990011060100c0c5210490301d040d22070560319542541c43d0711082450b80084840416500e008111428803000181c010704c11200d00780f1a60050440d0b1500420070300c4080940f401006540a0b550401c03050600d43c01c4840380c0d650444400d50080810ba42007030030340e400480d180e500160340c1c540d601d8840307400030b200c0350f0043e44260050181d45901c1c1e5440d9a05400a820340e1720584107044481d03245c039401d4040714041c0c0000c04101c0300d0306650000344032051559004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 68204220 1250 68202970 68202973
    0x20702130c080121020310020d020405030714040c031112150a09060e1b1e0f030a0c0809011116060e120703030c0302090607021306050603010b04050901090e12160203060117 76
    0x640800713940395031400000e050700100a401000720501e40c0c0710081d0703c001010300416800b44800a04e07658140100002804441400c440890445040200b2603034002c00d200c061524114070360051103180000c0d10031071a02c5a00380349083d25243c01000c02c004081c0c4019901c010032001c086281c450640006046540d207800e400c415440e0f4003403030700303e541c2400301d40700b0085801e100070400d980f8035400c4040d4003a400c08107a86051140085480c1302d900488030b00103403e8031030700002070460b401601107910000d050001c103ca8285d05074100540d11a851241002d50740d0b41d840002444100c1e8022000da145000c100d840d007102e110b2403c0a01c1d000740a0a501103840c113040000454040e00840b40c44600042030f0901c1c101d02ca60030022210000e01c41c01030701c42c4d43c6d00c078080345584409005500ae0000001a00c0c4c55a20340001c001604905800550100742026040a115400000c5c0c004480f441211540c3c1c6450801c00d2499902d0b0040300301075414031522000060343c00d000d80800214588800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 68205470 1250 68204220 68204249
    0x114060603070e1e060a031d01110d2004030c03050f1605060a0c0605010e091006050303030103030804140102030f0a05010e040201080414100218040c0906090504020702130c0801 78
    0x410010107010849030400400e81d210710092a0380b9000030800c03007158614026420100015011802e00e0304110044408a0754078050a02140d00e15100d840c0f10a07012070081c04600d922070364007213103030244074840c00902e526590403141c00c41440e4100341d0810092041c01303440b60b43d03d0400c0c10f03100140744802d54944c02016089000310b80042588003d5403240e00f016426585800b081c0640b0f54014020041001020001000007502502941c0c1c0201034014030041c150034184845403c100340011040b0500f8034003002085691008002c4c2c83c1126054100051981d4079400c110000030b48a10b0b1a04403075100204100780d408686c07440c10300450019008000076038030f42d074080d800281d0a40d40617010a8100d80040e0000c2d00c8040064507191103074090390504100c4410600598101a55441107203000741000401c0c0d003094400c0c141070801070f26000211900c1c00102829540d128084c0d18080c0360005404815915104054498861112001c2000d412150340c0281083e0007030042001c8612030740f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 68206720 1250 68205470 68205481
    0x1c050a0221070201080c0301080615060f0c0703030207050103020a020c0409030309020901030605010603270204090c0512060a0c081306020705120412050c04330f0303020a0302060615040501050c0c120114 89
    0x1481030380d058441c27181c000c111940b201204050107500c2100c04035031043e8104103490340d850b20340010f084c0c15912440142032150442c50043e003001060f07049581018414407040c1c04180d800100718001e280c098a00080103405814200c0207071000c0c24001c0e42054130303003000100704803483e407003113040b02c0c034683d41003100140c0840e03a03008050000d161040641c024003000300161400d5406a1901442030a400c0c0b081d42c0c0c1d0340085680c1000014030700c00c1d50340042c0100700419026010701c1901f50564a4940c243d490901c244080100078004040c011543c04500b105c2080000c114040b600302420301c0e01c54941c1e58821640700c030f404a041c0125203d0059002c4092107003404e0240840303042092212441a200801003110448200598034580c07090441000500000d0316001001842c001d41c00b900a40599040c06850007402511310f90003020701d01d104000e80c001d04001c1e182500d8091800c140d03544440f203000382c90400341010715a8001c0c00703800c01107020001503005a82141c3e044005450555a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 68207970 1250 68206720 68206741
    0xc030902090a021c0507030e011d0717030c030f07110102010c120b060d0501030b100807050108060103020a1710080f03040b0d09020102030712080402040605031c050a022107020108 79
    0x50620080d0048501004903000034900c0d009032a0400600c981d00c100c001400001c141501c41c00e54800c00881c0d031380c0360b405c10344003400c1c0540702400d140341081d0b034103140031904034550b242660300c00e200c844401a070180d8100341d401d00480300c146080004403512240284e004409550013014100c0780d401080d841101194010300490403540c4070340e1101d01d80100481e540c800070b040701306400c942c0402c3c100580a8044003c0c031819028600410042801e4a07040303010001c001c201d9000410681d01030b0324200f00aa0303100b10700a078031550070318000d621204400400c0c0c40c0c005816003020900d9041c4810880b0394045034000700c00721400801111007011020380500d841c0d10841c0103440482504108100904003a500044d450500c18411039181141589490700840c00f40035540c0e000400c1398080c1703c158589030142102a25049004c0c6c00d504410420000307140c0c070003041c5003043c0300e0045410714046000f4041052051581948070f0110505010940d81c1da9001d00c00c1240030526040100e00d51192 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 68209220 1250 68207970 68207981
    0xf0d2d1b0e2802090f09010306050714070c03150624032d151203180603060506090d0201021903080907060503010305070e090703021206071106101707030215030a0c03 73
    0x59007030030b03103a040b8040a100d0000e5031001c848542c20100000002d0301c1c948071402131500070350059100051500345148001c0c003419400070640100030091041002241075014400c044940c068111040c500e54081c821004e042554042c020a510210840740c480340c0c0c0d06050308410300944c2c0c0400c2414080502111069100c5003001c2407a001845800202800380e88402e200c0429140030070345841c1c1e04c401054010511750801c50010380403000e01b11135201c0b0302201d8806042181400c0c04001d0070134004c101c1c40c0c010144910f1041690291400641e40203200070000c59800c2590000702842905018240f03d4003aa00f18a0510503084d0005455100e4070076a0b060303035444005407406515000e40780a18000c003030700003003ca0080f0b18000006a507211100c00d00c6089000180c82d00d40b40002c2c0c050840510714448180c0c54220404004c055820034800d2006e991407002c0b01c0c401a00c1c1c000b4064503000840d00000c2d00003043e4000000401c0082000d944120315113038007407100042c003030405c609459 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 68210470 1250 68209220 68209261
    0xe01020d1107030f150507180506030105060a0302070c0b0301080a1505090604020118050406090e0c01090302011e02030f03041a0c0c0604080307020f16050f0d2d1b0e 73
    0x100300b1401400001c9400940c501d91501802c0c0c40841c0e820440321a5045a0301600c03400c000c6400f454050b030132001d6254118005100031582d19003550b24010210300d051140c0180c1104050b40007031010100101d0a010502400003210300d643ca0b0740e140c81d54150b441000c0f0006075521000001c801c2070030440d0b40030b443e100e2032102000e030010307440d903a005480d1140003c0088031841044400441c26842c1c41c49410014000303000d0104071f1241d003520081c10400b40e00c1e415410000611002d00150343c01501000d503110025808a0b10f242d400f8000b2421400792480c1c1101006002041c042808034000041807904486040c0d503070707241c8461501e07180900c80c19030302e148184c010000190100f80c0200c09190711040500684101030400a0040d0400c80c40107415940407555a109010a0500e41c64411417080d040e60b8a003603e0b400da03100c0490002092550880c43c4840610400c120901307040c4031803415502003010f0005a01c1c0f8001800c14194a00405040c2c00310400000d00d060381080301c141606 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 68211720 1250 68210470 68210473
    0x803011725180b0a060f020f0a05030304020103050a050f04021c0611070215040e063604050f010606050d05151c03140306010516030203090303130e06010504060801090f0609020a0e01020d11 83
    0x2885c00d20180c1d11500581601010750241b90144459890244191740741503201c1c2028560302e2030184000340440348054a03241425140104000125400000054000b5011034081e50001c0c22001c07600312154100c0e0703004142c2820000d0340f08060200f60090812240700311791618450b2035103001c0498900540c860104241611004070f5030038104806080032920000c1301341040c8400050b03c0380f18044400c5000c41410b01d031642017200340101400070644511400b030003070260600d4080001c4c240d000d241082c60140fa9140080384111a211001041461000c6c184d8041210701040c0f1021104046005401152003c42c101d10700d00c070482e003180d04c2080140c40c4c0300d04003008030319007001d51000c042c1d0881c00c3d40b01c204620a4242d03001c002514003039030741480da0542141401d03600c080101c4040d008505005050000340300081e000440e90741960b0b91620000346000c1404850404ad01455100d10f58192000508900d8543d002d000040c204500303800b102c9011507a0b08003113030302100310100c80440707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 68212970 1250 68211720 68211739
    0x903080904060b0a020a12140a050c0c0301050705040e130c0e040213110403020103060b0703081801020706020706020a17220f1209051503040803011725180b 69
    0x441150241180c54009070001030001c0e1514007280640d030050110b1409a4025055041000350080b051001000f1605d0701c41d640d040c00010010050286994260038404040b8800c2c080c00c2c0c04026880c0700081c001c0092255060042e400b034030541c03150182e280345800d240006024a21282441c0e90b05982c4040f203040c161340703040300c64100719102038001ca07408080001103140285460203100c980c103d00480c0584e480b032551002404440c6150b05c030001d1000140100c1c80400d41202104c1c0d8440c40300301c0500b030307a4500200e540d030082c1709210008000c11300c046108024051282d01900b904c410039143e081d0100c4094000c84041e40c0e040b03a0305003108080702c0903203001e50040019020400d00c0341d0040c4905d180c3c255141c882e10b50071002d602000442c40d240c1005949028146841d1481c030702407090385581001e481d40c0006103c1401003030805040d542202c3d5600208008001c0a50502601604120020f007000000310461303124003054281ca100f21107814003450701c103070a5018401051110b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 68214220 1250 68212970 68212973
    0x906030903030209030a200a12030305040302070308130e06040513060c05040b070b1501080f0f06010c060207030e09090f0a11210105071404060c030c020310020a020106030c150903 79
    0x140103103020440800d5000d100b035003156142000f5a0600620138040b2082d111300010040c601e43c00444041441660180300c10060740554032031041c641c0e0381500d80403e440e0340303034141a03103802c0075903000801328500042c40a0300100110f1602040c2d91848204460f103480300010842503902c10342d0001481500150f0b2400014056801194a10b92a0030880c0c282543c428002d50160003900059440d000c1c000d041000d00050580a8040310100b4241f032341c0c150512003100714100c14001c0178441710510744c1000c518039a004030002c6902681c0035800b50341c2c88032540ba0003084004419840c901801d0600c002c148000c501096413903802c200000140007010340d64540c0404146400c01403a0011902c07440b4480400d500d070700410180b41c00381e001081c1401c04000080009404840f1001506802d202c14400241d018a40c030b0b202c642c061411003120001c41c0000790520301c0e40c0440c14901c03440000c1800301e041e01908041c0c122401082e038107030550390360f8009403143c0e000b00a000e00000d006110520 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 68215470 1250 68214220 68214227
    0xb030607030510140f0120030703020705031002031e060103140406152702090f100c030905090606030c0a030e06071706040203010e0705070f0204360c0504110c060c03010f0b04060906 80
    0xd10702ea11030300381c2c5c140b030f20b0034480d0441c22356105040c2500180c20058051049050802402050442c150411461490b20444002602044403c105500b030a50804190340768071036042420440d03440205c50000c0d0400b8a4648000e007251582a0082e0010f0000000c3c0d1000f40760000664625424040300030347e072490340c07804c025801050310907800b9980c10f00e912415110141c1c0142161660b40383d084070000b06040182c41c4148960095101d107021000b000356584844050380d80002030000010b855410022064025145410242001e44a61006c00c42c1040d845110144001584081c01c0e43c01d031a013006004c02ea1109000c7d000004c1c88074004102014031880040c002640a40d4400c005c2540a500240542d814811405401c0000c104611042040b0302da4145140110307c1010f0440c00c6280d40e103d140e4000361041d50311441d5181c0076119002d500310116640c668610064520b40c2ca00a1090307542900203020704800000342c030030b001c0f444a00203021201902c1d50354a0b40c1c528036142c8401207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 68216720 1250 68215470 68215487
    0x9060c170a090212100c02071a090103020a02100e0d0e01081005090907090603060209040c0c0302060a050a020904020d06030b06030703031d0d050f0a03021b09010b09040b030607030510140f01 84
    0xca80004804c40000b0050809202c11142d072820701c90046100c0702c0202000380713421019000341c09441d009130155185038180030b00301e482c005428240980c0704c05001d0303000d0f4100003054580d5844103040015002440c040419076040b030b0101921000b410310704401c011580c401c41190000501c0d0080e6000744554030b00160115440a408400c640780c59032207840b503409844050f40300701c0301d4980100317003130403d8034050041d0400380080c2e10b00319680b0519510000d584101c058208031100ba1f940002c69410106c03501140d90380a4003038400d656441c411a20140144858401900d1001000740441c0e00c501c1d0209000c81266010350310300e00b440e0703501c00d8035000b140000401540c1c0540d5054402c80005c40500190f21000241005031070041014200a030801002220342c51000341781c41c0a45406560b0b1441041c15280544055502e45c240d55020034000c25509806550522170101040101580354003c10700c40c180022450211640d1150754020144c0d82c024019481044080c61031215486942507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 68217970 1250 68216720 68216723
    0x11030118020f0d090501050f0408070b0705041d010302030106090e03031602031308010902031002040609060e040e1603110303090a060807020c0918070b0c030906220909060c170a09 79
    0x61900340540b444001a038401455000c0698580c03440e00c0078440203100b1240e10040540302d10748541b030550740d240010302c02c84900510780b007403400125698074400c0c81960040c03d0110074508220280404001400c6000d200481c820b608107130380404c06880c5da0003150400310940c0011800c3d0780f2411000380444d1001c480500842c442800440b2480310420398900060003040f000007031441c00e40c01490309104000a41098807401003004000d2641c2c40444401103a41615100201909000c00100075190352141c58815104903500200c8500220000d441102e00c95080646a103c52806141d120301540c0007003584035640c00340811103103016141007580640a84141c3c0d80d41c081ca080041c54408c000e5960390320b030b0305030004819182c038420803810010b00380013403c6078180f0300d00341c4000c1d41c1c5c2e102d0415400c5c044e02000c940303017041c41c0c21a04403424a8a000d2081c800c0c00344ca540020b0010300c680fa4041c2d07525424001e6092800e4003070481d0a41e181c8070351540311030a980345c030a0800508103501c030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 68219220 1250 68217970 68218019
    0x1005100c1502070605060f100806040e0312010305010c0801060201060b070b061804060203070e0613210803090a0201090509090606041107050601150e01020f0604060c0306170c0112110301 82
    0x480703820075020744001d10500d441503a00003041c0c14402c003400448150850750b103002d041400d40c101200f0b80c1110101d580000112004250440c8030f5914504501a601d07148031030307010b070a0020040200641011903000c0450341c902c00c4aa9a45000301c1c2030fa41c491103201d200d2070041048001145c4d04601c226400700c0050b01e501d95401039150400f40071403049405031420350340441072006880c0e10000c030321846c1c6011680d441c00d00403444851075400c0c1962140350f0300c00c0c5c0000c20321800c2c01c1c0110407410304141c010481c01c8d03d0341380c40c1c2c00f51612500304079412070000e0b80c203000101700c616104c03003541c1c06004018000c0038039a84a805200040c01b5407030b85549514001e0202c0c9000480811003c2d01a01941c42c05044442c09400d0103058182c425040d20b048d9080060f216060001c0050a958800d03089040030a01603c03100041d0b00504c0b013500306485100c20702c3c004080109d000544100a4203080c0d84000303022907034201c6130085034610880300342d01d5801040100800e803400030010100c41001e28 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 68220470 1250 68219220 68219243
    0x1208011805070912030906030c170105060a0e030a0501240e0a11090a060507060605100203030a050705040306050103030e0312030105010912060212040c1410050a03050a0e030c03040e1005100c 84
    0x1684e02400020b00c003200000c04405042c001603a141c0903501820025003031043d00f200b00300030328a010501c140111030142030040340f070001d5603205000001e401e603801707401c1c0d8607844810304055004c1e0a039100b280d000c0c074000414100010301070400040480f0301c24240701d2181c0c2c40705800d1102030300710321094214050043c0540809555410460340c01072035a52101c60b51151949002010f0315100c0c0d005500c2100c014480c04034658000c0b0490343e00412050300016542c0e01c00c00301355090f0040b0b40010f050285000000700c10141c000700310305c031011011070484011040420b46402c081c4000d002c1d6500140100b0320401a034501c000182c2c0c0e04901ca140007600f82a820002d49132026804c5509030ac20b90400a030030040102d42c0e100c420b5000e40c05807050303180180100e0028101e80f0404501008241d074601c002501c450301a032000090407071200541c0e640b440c100309201d540380c1050040451071607219020880e002109140803084500c09400d8842440a040042e40c1d018042c00f001e030ac12000d0310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 68221720 1250 68220470 68220479
    0x30a08030f2a040e09160303050706020409020d0501140a050130050708160306030f0206030a0209031c020c4507030c0e0102150f070311070c0312080118050709 70
    0xb010307565191000300d0306040d251450841008443c240c0580302c2c3c21960084484c5c822604d140310b41010689406080060f91050f280c43c008000b032243c3c1d84140c01031813004c5042010b083d00398201c98125405410202040443c4030708025040a6502c1a0742c042951042448a1401039003105500364034040e900c0c0131007100380d031990301c1500c00403660000010800b00400c04140310596440340c2c035002a15040080c207055a903a0504c0d52000c8038082d114500c08400103191a6594044070541030014094900b8000050300d69021440c40001c1403000d401036185060f101d0810321000c040c138030341444042e140b0b044180f4503142d00f42d03050b642e1082d500b134568000300ca05810703029110b40950181ea0780041d0706080c004004001d524820032090440d0404001c1110301a42d13034060541203940c2d00150240c2c0d44841c582540140a0402c0d481f0600c90b020034480c0134440c0c2c820940003101c0c0a290615540c14500d034003212540024080c000b003503072841c030142c0c000b0b0707203141e102540c40000e40c208001115201e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 68222970 1250 68221720 68221771
    0x80c0604060f14061002100615020616080a09020411071b050402070201170405010605030a0c080601060f05070330020d06050402030108060406020a260a06050f181b0301080a0501050105030a08030f 86
    0x20b9801a954445810700340c03e405550402045500441e0350006001802985000400640c0302a00c12f8903640c6e19084110155034550388114b401000850340c50703a03604c92520b4003a40c0d900c54841c180c992480201c0c3d000400d801d15008072059981d0507940c400e460440c28905014004018105592640d030307480005c59940c800300300c41c0001d90b009118660100b80340c500011320b0010160031007000c000500365100310981e00041038802d403a0349410302c00c8107405501030340b00f031880108803107040c41e101e0318048134450307041a8000c1500224101d401d10409456000b4030090b484281300c2c107840c90307002000141c0030501301d50140c00d261040d131800d880c001d0001d160740b0246124010510554580b02814005180c9007881800c0080c101941d2680410300c9110014505075180c030812040c8800c0c0000040d070082e40c1800540010380400d0419850f0b58486814035074030302d071528041301c0039840d000010540d80350000f030291000c1e610111251a650b00e07106c2030808000040c010005c2054403001a2507021720 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 68224220 1250 68222970 68222981
    0x5041503021008190207020d030c02040e0303100303020f030703092105100b0f030105010e0601110c03010204060203130b1303110f040f0c230421080c0604060f1406100210 75
    0xb07030392100c0c07450512902e5042810142c0c070400071590320400440e001a100c000d00764010700d415051840c1c20800e43d00105010700206840030180e40000410099003030074494172135050383e00940c229090891014100383e9207100d25580a0080381c041082045000d0340505910a8500084c10303ca00c100341f01e0740c44925001c0c8480614aa45454207861819810f022040302e8541d48114020b004551400104404200b170242c2442e04001803510040c030080b03001c200c20040108083c00855582e0307034551b0000d440e500030401e4010300c1040304000143c0141346400750313201401080302c0d00d10000d155503170320a15401a44503a0707130002c2a03a40740c00400d07603582c880c4050b14a41c056001c500c036510014010101050416060503151255002c002c65280d000180c40a49888004800300700120341c403030400c10a05c001c0c00514005000451008160001c00c00b507002b82d20400c401e20513010b01000600030780710401d4010190b1580200007031944e1510070886540c0c10907a0040c0d84248002050a0080d81c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 68225470 1250 68224220 68224249
    0x40b030723071e031d0402070b010815180304050105090a051909110708180a03021302040602011406030c1909090c140f01021c020312040311011a03070504150302 71
    0xd00801c01c0d0043c4110150003203c041c0c103100308000385990795036004d45000240e0151040403803060030405078940700c60741101c03031a6801c007520b25074541e940d142d03107a075030204441d0315003080f2040d0002c9070b0351940c61207041002a4980019504180c02e190045441c1e401c8040001d42c414074140000680740c60b1080104401034244642c1c0c4410b608109240d000d507803500070840580320f0204134540208105d4020b552840c0044100c1c02d408010140024902c540281c0010b903112544004802c00d9060b0740c2d0060040711000d4000380205400c52070080c081c01c804940043d050740000700220036601e0321402c3c08880d0001da605245159858100c01c01c1280d501c84c0048822402c89030040c060151a0401c0090004003100c0e4000c80da80c0c41d50000b900c40c80d203a914403101c4400b09850382d41c2180240141c400000d0800038042080c9050306004000304601f22403401342d0f511f032002c602d030090061000d007040d109018004045061030502404024428030000540000c0000000b00050356054805410030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 68226720 1250 68225470 68225537
    0xa0203090f0105040503030708030c0f04080d020d02011b120f0501080a0209060a03020a0314010603080a170f040b0c130f14010912020904020609010507141606090803040b0307 77
    0x34031410007840aa00da41c00c1d0101d0501106000401582d41d0000c2101c400c641d0080d6281c0d203a4440203107046940c041c10301003014081011030080b885d4100040c118500050543c00c0300d08a10300750a090740bc0302e04001c0714030242d480d000310800005000b461408800b54080c0400103074032a8801813070003111401c0c0c00000703554010000d540290b00d031260f80b442d00a401191013130700351859940024140c4003d071000520580007145d14010261003076000d00021074020074025650030358074400428103440822782e0854144c41d00c021418a03003d200190340300310f03445201d141e240e4550400207411078201c81031008200304084008100402c0d81c1103030340c004001e0a082101140c070071400242c0100c010760044203480c04c403280002d015907540c96001e40c006405803000765075a441d07800122103a1045280c041c055242c8060869650b0900043c1e4554500071441289036194407604100c031403070854450085194403d00081c450400d0000003103030000e42500303161a10f50403512031110464142441c50619 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 68227970 1250 68226720 68226727
    0x160219060f050c060a09020102030d1e06090203040201020c04020d0e0a0f05191205030402040212090c010306140a090e0718050603070b2106210105041101020109031b06110a0203 78
    0x580ea0054015522041c081c2030290410310002e4025a6910004244144141c1c030f400b000300569001b0700031204080c0710985c0521000303078400030107200d0800d80c00c0e5030525a03281a100040ca0301c2d8510980e0300582d4164064400b28502d0380412019401004085420a03900d1921119000007008144941481a10040412141410f24605004485d100c610303038800c9110b00540000c5480a00b904500c4490502940f25140d90000c41c009010300c3c440607000d500001e007400b0b500000040c080040035401d81c0c05000c0c89031500710f0740308407500d45140e964004034450814001c0c1324007500100c00c2c2051590803580240d556280107042c005800506406041e501c40c144070f401d06060100c40d0242c150080c000e46040d0b041d00e1800900032901c240f58042c0c1034081c0110f900f590318100e0b4480346503414401c5111524941000500030b29090f201143e51007040f03c421219940103015007200d413a0580c030341000e485d1540030030441401c04403034201d58465031110b5003818540c51710043c0111500320f82c0210346 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 68229220 1250 68227970 68227979
    0xc0d14061305040c06050a050f160516050d0611160803040c0806010e0c0a0c05010c1d0a080d0804050316030c11011d0f0102010b100203131d01030602160219 69
    0x16140e4015400900c030340c101803c00000c907440340e030884204d5905180040c0d4900d6190760841e114010104000c14800780040d09000208034004d18054882c0254180c4200040150040e90b40804500c40c183d0840c101d00885800f081041d446000f400c051800c505142800c840c1040501c2d07840248112503950707010080c44140942c0d5088a0013506a02000389095414841d8160780d4140040203403c2c00100051490802c03031140c0001d1003d180d100009100c40c1c200b850010b402003440701e072200313044080001400c44614204c0e1001c41141e42c910050300c01d45c0c810006c00c84403590028015501c43c40208400070007c1b08040000b604d0600030f5440440c41e05181c43c04451109854211604010380884907800e40e02d8007020b820055034048074900d200180d4100140c0c003401007490f0480e031102074044040041d9070007000405110007038469080c840d0b07031942174021060300100301803502007950000500000744194000c200079144040f02020b19481030340040c407c0c8403140e40a140003554000b0400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 68230470 1250 68229220 68229229
    0x5070b07090501021513020a0303050a03111309020a02070b0705030301030b090a05060a1509020c01020306091605070204090f0807060b120d020a12031104060203031506041404050c0d1406 82
    0x280c1112003031500c81080703440d01000070340c0ca4a0b500e00d8030b40b00c819502c01050865040146802c02e03968082d10b12000e580d5681400f03406504100d15403030100c0d00303001c4c408000d1300c000e008488010300100703a104140ca09000a0500a4001107902e00c00c0d4800c980020420035440c07000b0b4041c0320b108000441d43c944c158680301050401c05082c0010136407110f100400040c0012910b0381d40440d07010000500d0404a20711400303842e03403650068040380d00c001484101f826041d0011442000140c80c13004044d00d40b140403e0840543da0103210016a050041c0d200601c0c01d60032108244e030041c4c40940654202d6201e220482d8040310044401a907142030208041c02e1022030070f8240d00202c409010320131555400652a00301158000703083c0100700449408180c000d034410001c03003062100081d1203503140c5001a50301d9109544044800f013400b0440c04540c038100c401c96058411004c48687c2d58803210f0280005030401030300140583c0002d02c020709000000d84201c0303e441e2103401c180c50050601e1020320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 68231720 1250 68230470 68230493
    0x40c03061b051603020c06070506040b06010e060f0901050d02160309090b0d060b0414090d0e030313050d020d06050705070204051e0601080c0d11071211071406040801050103030507 79
    0x38400a81c01c191803031001a040300903145941d601c01c1041c907401080f803908034100000503404135031180c00400c03102d040c0100003908a100e41e01c508120f00141d1030310001914032040010100d64401410003400c0c0c400d815040c080c4c40890f40606060b400e091034100ca4005980100354445a100c00318030004003030551060110000b86242001004882e0340ba00218100c061400c001510071501c42c011803185486581c0041614001170350303601481c3c2014003a071600d034020000780704001520420700c01d40c1850040304660100980d02c0079510114900350501140600c201c3c8143c0e402182c040317140020580d203000d0b00b44103840e0f9503503c45d5108550320401c8200c60000d0310f240301078070030b000c0d5940d4a01c2c440c0c60b44a810410074203060015950b005114a813a22811541c50201d900740300c010340c40c8070061005424018400c030320480551240780300864410901e8101030b039203503110b52800c100004110640b0648800082d04a81c985619400312038259102a0300c01c4000401c006148802c0c4146c40c80213 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 68232970 1250 68231720 68231741
    0x1903060e0717180c1905090103060204030c08150106260c22030b06091008120a0305070509030601150306080319020d0809070504050c040905070f03150f030803040c0806040c0306 78
    0x50307111211580442603035414284d900e2400f520039071440080074001080c0103802420024107074200ea6850f8078044020350410311040f03440f88201d61011860300c40226185a5803140c0402d940016860500c080354581a03c410016103420b44085190010103086000362040402246041d075810040d40c45041904507841c2c0e00421685002c01880065002000d450700000c1c21105564140c03a800009500c020080d8050740841c802c0380413003042070206401400c20a40151801c02c403d98508000360b5103071041d00d0041d27901d81c011000500801760303401101070544a04e0710b40051440e4071940d04510790350091510001c9030304e07a805001d0b1204e60402c191110f015440c50301400d0f07800c200e41c515039a50164007079113101e682c039940014180c45103413041c0c5001744808a014411800c2c801d0000c2c0c0084129004400004d08100300450080b00c03440d0b0300400c88000d0f01452003a94915100d044031600050012502c0e0749040b04000785002040044a02650190b405040118554a0068200c806d100c81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 68234220 1250 68232970 68232991
    0x5120708030403080a0203160f02090c0304080a08041b060305010e0a0c080a021c1103070e0405010b12040f020406030302030c010507080106050414040902100e0301201903060e0717 79
    0x81800540c20210a4604a0740e100b11400d49541c0c80140c140d0641c091b07150303c44404200110890140403042105554407030007a1840c81c406d49076110050024442114040c1100b4030803c0038420301846400020761160180711091210342c3c040b00c5002c0341c40100d602c203000080e220001800002e040c40c014907004482854104090200184050410030006011a90b40c2ea40401c0a0a5005840d522072801d0001c6c0d81007044008581ea203206100c0c2c01c15908200050050140100c0b1410144625416600402c84040c10541100c849210680c001807080b11001250001000182c0b41c5c0d0040300003442c072a8005d5512101a1201103007141c00040400d4108410400100040c5400004480c00c0d900203043d2140d0b070f00128004076001c0c018a200080d081032042c8102615264842500000080c0c00c500900122103410300c5194000a801030111808900b0003c0c0d50030074244040d41241c1030345909006c62604da5845080c80003403000c036102c002159143c2c4000c216000d25801055011130740b2030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 68235470 1250 68234220 68234233
    0x913031202120f0c07051c020609300f0c0703141c050306030a0510020910031e150b0408150105031b01050f0f0301090906050606040b0706050a020903010c0206010512 73
    0x1000c125040b006400c954000c20030070f010030104010390084849194121080701c540c0046010410410404e0003036605c014010900400c62000b00803400502c500a0701c5c840c1c44075000b01c2150340301140e808034482c1410842c06c000001041e40d494000e48070300016000540030851440c01d040004c0030402ca060a100d4001804841c07203980340c1f002d01d00b05800b280c5805600c82d52068086460001c0c0744030050074a03c00c0790704000941c6c4040c0c004194420301034030714003020315080d1420b40658240488201314551781403851841804981d1044003403a0100340804a155660410b51401d9031164100f03218580014039031201154505c0700b000c2c01004113400601e006868811521135400300c001c440303410000700291201d0081740f400155817051452008007580d9503034660004004010180080740e0903070408001600902d49101034504581d41d4400c0140392400d01da950b2001460010306a01100d030303081c0140d5049880920403185141c0c4690014012941440200b004603006956200303a254801e1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 68236720 1250 68235470 68235487
    0x1b0607020111030c0a0f031d01150b040303020c0904061104060206010f0e06090604050405070519080d020102091311040b070b04140c0d060207020a0512100510050d020d030306050913031202 83
    0x400813520f544001d490003400c0c6d100030504c110060714807448000c9030001c1441c9600212081903100101c0000a1122017490f281e40f40030310100d9000f03510000c1d0158208130034150329401c0198226501c06c1c800c1c000091006958548802160000e421040c0103a100000602801640e1500040685030010701c0703401a00c7c000d800900d8004c1e008185034091078403100400c0070003c080041402620f0000c101e001220310001c80100c042d1410710800c9100d208119008480e140188200e50140c10094004203540300d4004014014009400f00a0b031012020040050302417007060241000c0d5101d0105420399041504020048869085445031590400040ca210f1541c031b1400b21b400a0394000805078958205000040300c8040c15808031350805910085200909030100d030528400b07004131010840d80d1170700e81003043c00c0f59090190707580110f50081150301610780341602c401100e101c0c0c90042029038581d0046809003c080d0b61000c20f40032500303a50010175401c500c003544040b224500450400300385 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 68237970 1250 68236720 68236741
    0x6110a0b040609020d060c05120a05090d2709020301030302010b09010602071701020d060b090306150604030201080a0e07140112090b04170c03030705041d100e0601051b060702011103 80
    0x150000b400c0903039483c3c1c80801c6450704603601c10304681161042084202520b070191840d400420b10315034980f003043c0014642c00305413050f24001d079200801820540030200041d90702200c11840c044e54400400c0030550b014000d0100360700500003c0c2c101617100c1d491403a0113420349144403101c502c00c101f201c0041c07041d2603001800340101c0d2904040b0049152034046090700a01c00c4c222490b0740745091035070104216203d00014071403c0b10076006c03540c9070b940340300c151202012000314265000c801084104050741c0705407501d90304060417040006210721542e2641346000d03010b03407201c0800c00c00300300c403a6480c0d0b0308504443c21260b00d449080c400c21565035a03001d10044000d000620041c0c400880301003400c422401c0e12903004400045175628100580c0141c4650032601c00c1d01c111080f0030700b124080c1010014004e00a040c40e034900c1000c2403c141e90b00300c070b00030020405810000300f030200c011204002c0c54a066a19400c8018001c3c41c2003810000f4251503001a0f40d146401041082c001d200c0e20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 68239220 1250 68237970 68237993
    0x20307020c0108060418060501030308060d05070b070c171f0209091b0c0a030305150411070201120e0307061a0a03260d050115080f070c030804080c060f0106110a 71
    0x1c2441e0800c1c9960b20000000c0c01001030807006029004002c1c860400c0010640c00141660300988904583d1b54501041240c40840c4850084c0b036500840130402a00b1030001c080c080d1503106080a802c0315413102c01c0d02041214107941901d640c0c3c089000c103030000c010100340488034502258198030f000c0f0040302103a40300c80050002e01d0419199100309204102c00c2e0151a07030a20603409031030000700b4a040080207000242c5182c002d14005250850481c42c05100702d131043d03508041e070107040110580055030812041034401c2070701911031191002d4030b1001d100400c003051240d10000340d00f0074130400050b040d580f85460980614a80041440070408550810244d00c14840113a81014141d00d1400070314061751a00001c2c0c030741401c0005c01d00c95038400d04020340d01c3c5180c2c1c5595180d9540803031501c03000f9054034100c0209064200300700101f0720030749120380e00034044c7c10b0881c13030102c91405480c50604101e0f210000403000e540144240d1742e10103081c0090005613802806003100c0f54a50880785207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 68240470 1250 68239220 68239243
    0xa1b020c010503060a080303010602030a020f03090117091c03140105190b0721031d0c0a091107020d030f17160f110a0503030703061a04060e01051210031502030702 72
    0x81c040300048081e0f8171745030400003404a0388141e9440c1d5a5607003000e5980d40040d40100c0141c0100d569030303070120b81c0000985009050594403028801d090021000044401500304005401103d6400c4c40142803900104084219503900003030011075011261003010060300305910802c01d10706030781201c000003018141a41c40c07100c44199182802d02d4041046540901c3e00041400a1041a80c00c560160703c40881c0c000180f8096000c000c0300240c2c04d455485a41d4215031120b0b0807203003409a42c51603440052280d2554144a1034007030785400040d2000c241c0d85007140014603249600e0840703a0710000120040c2da00d00000b540c9401c09082c45c940031400c2c030011004101000d0140d03c13030580f20b41e0060500c1c0301407005445030030b04141411034484e03004030b23104004a4140640050300580c20005845802c1703002808a0419041050488584000300c032018104003003803003c4083e100d00d038000a0b00800c2070351700e0b150506180d45040a08107110a084100c00d52041c4100601c43c0d402144640288 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 68241720 1250 68240470 68240477
    0xf14031b010215070203030403080121110a0b0412050114010b0a05090a0512010507020c010c020a030f0602040f0b030a051501050703030e07090608030301050f03070503101802040e01050a1b020c01 86
    0x140000d5004034a01100c40d41048110020300b000c0c40000754001c401580124000d6a808a00343e032102403203001e0810005603200c150042080303203c0459030b0705800720906030008051080c0c450f96500c206242d81c0054000f050181c4001c4201c10421000344903d01251240c2070752010150314260040740980501c40f4800144040060807003d207564803050030015100040090f0350300b5460003643c40c002c1100b1510302000d8480c80b680c100c0950b00681c07440b1107096000300361062003410360f070300d5000c101d810300411034541d80c080c400424281103c10701c2c1c6d001760429012081d224078000070321205850020b00f01c2c20108400c94404620359901c402114469509400e000c0f40e44c0381c042c1d464a00e81a403550188120628090010680c028040000c5040341c604032000d800d0110030408040c2c41e41c0d205d10038590300d0303840000c034500c6039022604040310070790703842c44080c8207501d551b004541603a003020340324201c0381d643d1f40400004495a1050503030419090308a040c1aa004101c007a54a15030800300700e050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 68242970 1250 68241720 68241763
    0x30a02090d02040c051b0105100612110307020a030e040915090c0302040e0a03021203062d1306090f0515040e01020c03130302121c030b030c09100f1403 67
    0x1589445010719003956025004000348900703030000400d190000701259902400c440c0d0700d038800d071805005213801501d0a50005410034070707166042c0c4408144e202100c5026443d140a03500d00704c0c42d4405103110b0249a00540303450700342450010460045103080c2c0344100e00e0304401d5804205c0008480d041d6181c1d000d40010103200714207040c2c00d000c200b80d00095004c1c0c2000c00c000c00e1104049000034105100e502218250b007200c035000710700f80c0421a10244c118201c0c0c0218905000d19080480f1884601c80300c0f00202c03c503a03004554a1500c4165a03000991103202c10020090b240c070924a86c00c04040d803c10103818000c004080c10b05c2e100800d00c1c840d80e00d81040d6804088203504485800d021003003169a10880704811140783d90079072109a10440c10028403d20110700801d00c000d5114900480000700c002c030030000d800400343c3c0c4c07031b00e103805204540e0242c101d80c03103c84000b4051250803080745686850481541200d101c02d801c02200300d90700c1c0030302182c1030310006100e0801860402c0260700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 68244220 1250 68242970 68242987
    0x604020607051903181418041a010303090e010602030903070303180504090b04031e0507061d101d0d0e06180a03080403031202030105180c04080f0715020d05030a02 72
    0x503040d140c403440864400300f01404010180c01000000b404140c9442c4910803d9454060a12405500c0b07445504003030244445030442107541201039200d03108490000400b4009155141d40710001d0300b007180402d05070801404148070303580886005203031a2008515203c924030100b61620407030701c002020310074800781c042818140100c4071800f809018008000c502d64a0805555544007078030290049141301501240c0700302c01c2000c00382c01d102140c4a40741307407844030355840000b88281c400018401c001591400e42c10741f400c1c40386031a6040c81e85800700e2074640700701210b1091807143d026001b44c3e500c80d050ba2690940c2084904068100c11141035440d10440f5400d9019a030020400d00c2d84030b60110404810022180080c0003924060307640e01400fa000d103192141244020b0207110f5100281846161000444410560317010122055850a003940e0700c000a00c0e104e90340178009100e0b00410802c3c040d91780324844484a0030583d100906600d0b11041000e481840b0181c10b410a150b000507a090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 68245470 1250 68244220 68244223
    0x3071410020c010902041103100b0c0a080a0305060114040f030809030c060708030114010801030b010509040f02041503050c09150d05240402010e10080a020901180b040e090f060402060705 82
    0x290404203008080d5a50000000310768000e1510810480c8510310348000051404902ca06503441100415000300c61035042c102d81c542c1503049800b82941c2e9116040c003460000e40303400b0180094920640b000700c0c890070248000350480c3c60040100341488402d10007001280c0314040c0c26021283c2000000f90784052540203e81042060f50f00c03560060800100c04c004c2100001c0254100c80000500301c0040308100011500d0000c02e22001d010414170030700502840c0b1302114040e4116210380708230304070140c5546c017247c103640d10905408200300c003840003001405818001240c4440044070001c50030700d414944007100b05c0301c0c1030303034240100c0701c4420304020001d0403c840c0007078590300ca400701d0004e101e03102003038101d01080320200c0c00102509040181800c1980414800654645440300300b0355500001800070741040130210b04208800d40301c40b01c0490350702c2070400030303100c40350f00c2da0395a60501029011078417010384015a25409001003504003800801c3d4aa04198101c480d265684814102503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 68246720 1250 68245470 68245483
    0x2090a030b04051509120901030e1609021903090503040e040201020f010203040602091536090103120f02030c06040308040303020403050607030b0109080c01140304020406030f060e070905040302030714 88
    0xa00100c000e80a002c10f000000030009501098403030403a1059403800c1304181c5071481108811610041408404004e43c0a81c000001c107900c00e404464200040a05040c0c89400903403011041380d50005440803443c1080c1422025410942000e00c031103002d03603450b5562885188207052910342c0388000b0038110380c402e2100583d2015944001c1d5281e040509054000354810441c071885000114505e828a801c20743c251001c180f18a0548501e03082002041c0281e03144040380c0f0243c10000340e03044805c90b512421007601075400383c00c658190700d000300000340071000c00030075240c20b6503c01c1c4120100d00d01d0018080b42e10aa15140c50341e0300ba212860140c000e806150402409800380e082001354031395051348503503d180c509996220407035a41d8141a40c13260000000140002c55481c99030003448404d000950300706201900000c0c00035941c1c2c46203188d502c40002d080383c506850700d4600c40e01700000c11074800501954034080040b0700f016a80a036880c4116580144004050207d07000b02c00d1062214 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 68247970 1250 68246720 68246723
    0x2031c0c0903051e0d17150307080d05130906050a060f0e09040b1006080903160c08011b03050108070b0409050a150b0a090902040b160609021521040305030a02090a03 73
    0xc0f075a60031407111490028840311318440e134a030310440d0a15110780d841a100c61202d040009254001500d07a6075810202d00a9204070b1341e0940301c0e9680014030a8003c00c011241c2d944d440d519079403110b0850b5180202c41c08240d121080681c200801803086585d4803120600301d0f000d03401c0918a403048a0400c2c0d900c603c00c0e081c0340d035102924408100610803400d070742e24401d448a050107003003e0380b51a42038451510503500c0c440c1d2a030041c440f030940c0307010306507803030100c03d000d040c01c051240da036242e441d0709581c10f04807202d01940c20b60030710340400c9425000d014017404030140a407a5490502c541540346000e144519400c1c9038aa80110b2040d1020f076110000c1c04d4191500301031116154081003040741e011601a000107034810100050141062090781c0a4401903090035240841680300f1a80c0801c4490702030300d001d0380e034540c26001030380d0790000d513200100481c0c110354036030724071351400e1694103140542c00072040031740820400000e81c02400c4a60146604400513152103041000c2001404142c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 68249220 1250 68247970 68247973
    0x140c070306060f090507030e0c0d0c090615081303080a0c0c0b010b03010812041d10170d030605010503070903060e030c0601030506090609070305061b16030905010e0102031c0c090305 80
    0x4000c6003d24410007030030261031070b01400b40a1031320780c40750071000c86030726100296942d0003007214645107213029400b25010902484002207002d889130444401c9030f0f0107a00c004d101544684440c01900d800c081d036994031525604e00c0405688842d14003500302c200082c901080c0a03070710010400f61a01950311200202c1d04983c000101d90384500c404051a402801070070094414010b00110110344241102e040d00c8409400f40082c5014040602c141e44000d000300d40c1d15049440042880300c0100011640428503600810286c02031034400340c00c403010342d000f9604120040081080c125080026142165400385000844d01580d02c46c55080d40a4080760130381a024003c00001030240c0012680d016407400c00541e03000e902e6100f2903d81c0d070200d600c0300500e660046130014088800c010380821021010381441c5162005031198022110380c101c80c110045000c0d001c4c24071080d41d0105a6076400390003070004624080e40782c00351210580a80c1603010405495a00c018580c91003032070a4801154002e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 68250470 1250 68249220 68249231
    0x2070602062a0c1006230d0f3302040e060d030521010e0105030102090a03060b040209040e0a0308150d11030304030602070c2903150a0509010807090f05040201140c070306 75
    0x403c074907203070704100d08481001400c1481c0412140030321641c103041c07034410300d541d045c0310301880f02400010401f2410507901616690480301c0443d061b1019107110031340703d4801c40b03080b001c107040c8407541c2104070800b003240c18414041480010a40c00040e500210201d59440800c4401e1a040301c1c1c1348030340104610140110042481c0c000030703a08540341030b541020110000d90380c0300c009040c201d0140100255201601c0e100c10000b0440c99801503a00e1040940098948a176043c049000e60342c0d83e100d0000107a005100310300a1650104016400c0094500003400000c0f211001464071030380418050003103100400b001c1c6441d5410001c44005640c400c206540754026400c0c40e00501083e4400c2da4440c01960b807485003100e003a04070746191400e400b06224155100e800f031031100300100060491b0001001d0301c0104850b607920524500070800800289030309400c145400f025240d05036202e40c0a5410030040c040140c0e0001d5894820031200304100d42c440722101169480c040b0250f1003d8201403605 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 68251720 1250 68250470 68250487
    0x30a0210030b03010608030901020d050d0e010507080105120a030e13140702060103021c0203060c09040b0901030b0601030f0908090603100e0103081215090105090705070203010f0c0f02070602062a 86
    0x68100d4402c079902200204100da5845200d19140e1241990843c0141c0089070440740a0b40140060181448615400146511a4042d081c02c443d02583d242001c41c100400400c024a0100080700b45008000080c20461016650103089018038481e003510648410740700c034141c1a8a940158100550840051081c4c200707004080c7d21900c080c04268040c0180e1111203045a000900309400345174090010300071507680c14070495083e00308050450b40151a90540d0340551340d4101005e01840c081c502c101f05d2418144005011202c2c4400e40c44003003400c02082c0c3c004070b1051800d0b038888020030f54160faa00d80da01113040032403e065030802c0003001400e00c0040244055000600541c40400c1890b03107641e02c480c80c14500710318401111984c0a42a200148828140a554280c1050050904504186181d0300081c2510004005c105840e0382d2900f51109165002400410100c00c1e400a0a03400d41011070003501da100080c5000b98080102000c0c0788016551411251040e01d414000358403603030708 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 68252970 1250 68251720 68251727
    0x20a0b1003030f0f0206060103050406060312091410020a0609030201060503061003020324150114040b0903100b06220f090c0806060406090905060d0c1d090a0818030a0210 75
    0xc5000030360000340154100c401c9a4011403034010703002da16400500c2a0b40d2400c0045019000040080322025113500380080010340c0d4190000241005482d2000080e00f0f050080000c03030343d8000000c0c800d1035107030450000d054010a80e502816080754011503281842d0406901615003580f080c0e81510404080004a040f0088280107981c421001d40741050003a800315128401c4034068401c503041004041801030501894a10b12203006042c0003010200a4101d440310344c000741e00802600304001062074440c41e00f4480007034002e003c0e010030890300b028400400c519016000700c2c21124070381200c5a580d4a9841d04081c0e00410100145001c480d0b00d03408004081c1503020414408110b030b110109215190110940701500c0056441600252400d40408040e00c80500b41a402c14641e940c0f800114083c1d0921402610014401200344800203107141244c0c40014412002ca400c02d00d480350000b6a5842280d100d81c000c60410140030110400090a040803284025840b170803212000d200540c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 68254220 1250 68252970 68253001
    0x6042c0106091e1401050a020703050d0e0102070509010e04020904050708061608060a030206030a111312050706050414120f06090c03150402030d11070b0d0642020a0b 73
    0x240d110000a0422010342400c541c40f028020319400304071440c041105544210017401c400700c2180304036107801d41d40303848044c240342c51003c100c8005a007500c545540d41d40c04112040040000780c50710491036242200d4050413a5000d403000740300d049900c01040c1440010072409000d4150002691102c1c00d05030744141c0c10b50880a00303080400e080c500040c62a07d0850b540300200d0b45c014103160301e1650b8503842c0c032b8020001c0104204001c0c005210562943c40010764100141c25264403800c044581403c250f03241c880301364080007c0100130802440002e2240114140d005815550101601081c41c0c071641010310480d403840c56480340500b0849081b81c0010780500801c02078040e5400d481c0c0b04506801560030868010b901640500101c440702c6100b0b10502e00c0100c0e6074001d440c0341c4c2e61182814800f036817004c004603400c66111030050299502d14490b98410f5220010001c3c1c00303240104080c03450000074000440712401411000c0394081c001d02030350b08032980c001c440403468030b0306010304c084041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 68255470 1250 68254220 68254229
    0x31c090212010504020a0303030213030606030812010b0c07061202070b0a09020a14090c0d0b150d1811010804031206030c0e0c0a080f060d150c08060a0506042c010609 73
    0x6000c61040300c1907035410b01c610303401075401400007500d540c2143c8090300030758480c010f0700101ca50103c0002004c80d00522462014521442185a40d4500300c1e180124602d010f0300141048501004904282c1e000020340704100c070241c2c00c0010b100303c8080560342c024094140085e000540351820000b81d041e4903407148032114822112403400a440c2d04801d01e104d402c803800c1c02c2c1c1013510351004c033b894401003001038118203900d484041940204080819202802000c002c00c482c1c50100346000c1003003141c000e005600d51460342002d58401c0e66141c040075003907034280e468180078100700420181031090380b905030048020042404810754074034084040c2c1e089441042c203400b49103800f098424050b0000c44107410791590741d00740c4585543e040c0b03c0291001424007907208e000b24160b440040d01011504454001045000520301410400509110f400500c51842423144d01000e0215507071380001e840c1078030040038840c0c1d5100d20708071140c114011186411b0480000741400040c41030f510912400644 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 68256720 1250 68255470 68255479
    0x130f0804061e0201020f0406030905010605060a080a0c0c020105040533070203070e06060910030f1b180602060114010201020906070b061804120c0f061407020c0915060a02031c0902 79
    0x3500c9241c00304d00702d0280f866030200900040004114541c03007500540c0c0440d02510001455a80e1880040c1c466031001d2060308c0071803207043c104201c4500300d1180c05040c55442c00c00b80000c002981c0000c11502ca1030040b98810901c0c1902c407401c0183c07070491003000c0009800840c00c0c0c04ca58261400040e0402c0000300d20902c42c1080100300b9640f04031030700e401000d000d0001030400c2484800c2100520a9940081c1003558500c0721156124090081d01c40c2040c07103000c0125405000c0c50000c08058441520f07040440342c1d60b100704155a800145581161002c4424005110030040100d01a1040d141000c0d8880d10201e4484144003048440b140201000c90306407012690908544000d81c50464019021065503030040482c6805400101c94480c400c1380740d000020380030b6844500302c032004150755410142c604204810b60b6010402c4500c0884200c40d482414941540015145a10030340300c0c0d402860041100b0f800f00303000700705480309001900400d8840e407080f142404000c0c4440181641308 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 68257970 1250 68256720 68256767
    0x30105060a23091302040f0b1b030409020d0b090402031c14030f0709051507030c06020d020304150605010302130302102f0c01170a05190e06090111030609130f080406 73
    0x8508500c03c840c00ca441f815107403202c0520f0094003001c1600000e6100c00b299004039a1444020b0090009102611304a80d00685929490601c0f00884400c040c44a0241c04040d0900c00035030703400501c1941c2c61030151203e60000740c590b1702c00c0b603d4001c4440356010000c1c0c08401d21000728003c4070390b248165100e036141110696144104000d01d440c00203881144241004140003081c414a0b0484007280201000752034408140214812603004a60941e000110b8600d00800580711b03005041c0140b509103425418414180c1c0401e41050607840001d00c103c021340c020040301c9002e43d9003124440c00340c8000030190021115551490300a8603203510f06401980c1d03c5c40d401e076010f03000000201c181c00e94840c90540d00c0c05015001440081c0804034605e20a042e815040d105601450b2a1000302d000680000c0c20520754041c00e407451203880400d0b80c20284104100c585408581c294442421107544a011000e42000000110508005010541c0000300448d034a50040821381d00319200078502d00b031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 68259220 1250 68257970 68257999
    0x2030a0c02011b0507110904080904201606061203080405070f0303050f03090715020a020315010506070b130606060c0510050403020303160e030105070e120c0303030105060a2309 78
    0x80f10f0346082008155091155020803862140c0c01a1140f240704060340030130f000d070080016040b120203c0707084800c1d00c0f0010b081c0d000c6040c28010701a81e014201c04240d403003065550040441e01940a0054803e11030084d40c07405e00503150004002000c0c0d420032110b0750078084c240200f512004403800e43d03040c4980c207000180700c10b03840c0c030b02e900300c80d0580e8030541040581d545900c49a400507000080c184104080800d070f160600c02203000512803030b002030a2499403032041c9410100c082c20344940603440040104015101e890131508a150b0240d00141d49070360301a0b042182030b0f4940800b40940303182071301c080380464105840032182402007003220000e03006404580e05a9030b08903401030040c1c1003400416010500000740081441c11030400701060719a000101c0d0031142c0c101c0d014000509070fa20099007034100b4500c041b10310354280014001544650010950b02d00c8103128160007444005002c0f02161b101d16a40c2c1820070455240c410015a0300781c1c0c0c144a40c00c82c0305910300c1103024162114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 68260470 1250 68259220 68259223
    0xb0301060323060114030d030203130506091c020102160f02060708040e0601121802040e0a05030d02040f0b270105040b030f0105121b0609150307030c0314190b041b0302030a0c02 78
    0x1140500020020038102c142d00900f00d022b5003001d005264001d2001c1c0b40c2000180c01800054810103400004003803007019038070510211662032580c8019a4810004409402c3c0b210030281c002981009050481500f54030101d4414843c83d040900800404a400b00c2d000c00b04030b0341207019240076aa612070000d42118840d003124481c41011890048c4200e94074014200340c1c10400c120740300c42064918181c0d064450f107081d0390050b01c081c1041c640c00101405081c40f1511400d0240c4090301041e07062222855003030704418034540700a180088407464031203160b8407030300448001c1c14141300300c552030342480a40c000c503085007801000d1152030341100180e0029400182a400303a0b4460200200304407001041c40142c0c1d119118240d0440001864030548000210003036010b0142e9030341c0001c0341100c0000013011203400a2880ca0781405100520906c20a84c500340030a10360141000500f4140403800200102010b854200c00e40e88204d1140c4074440d0190b0103148502c01a4106101064201c102207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 68261720 1250 68260470 68260499
    0x5030708010b19120209041707050309040501060512010b031003020d05010e10150e0c070609030207061202310306050c1201080a02010f050c010207021503040303140c040501030b03010603230601 85
    0x2c10303040002001c05801741c94130303a0030140c105010f44a040f0500d5500c60030540c03980d12034402518203900004000701641400e1245500403e803500c3d0440c00c1207486000e4103400c032818441e107a002072001c408075001c1c16000008400540c3d0042c00300a0710002d502d000b502902c404a008852405010440c0078070352418040d1080c2c0c4840c009512810394184203030100b0725240503001052010040c002c2900050552280d980003a01a40041402d18074024000f070000070300240240c00343d0f0061240c400b120a15030855444a031466004117031a1005805501c0c1d8030110b44d2019141c04d0034181801101d0f4080b000402c1ca000c04042401c415a8035000ca5a80d0341803101c0c2d001b8002101c10000c4811244103001808600820000151401e0a241c00280582d10f4444214104c400e0000c140820107825104504900004d01e4100741603151129000c4041c1c09144540c6051548890741c044180d035081d80000091f641c0410460304506079017a14081c049a885165400342c42100004980203151018030f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 68262970 1250 68261720 68261729
    0x4122006011512060501050a050a020307020d060504021f050306040e0f0d050901110307020307030b041a0406020909060f030601050f01210c0917060712020705031c050a11070204020c0705030708010b19 88
    0x1420318200e0304008c21182c541c410b004020850000307004150040e566400820041ca009100129460806d4010030001303203565002c0d4805030150382c143d01e25158020701aa903115008840000d540c2e00b00108035030928a00a01841c1d060245500190106401074040c104500081c0d0340c900704820344503221603903031160003006503141c1d101d01d00c1040000e54480b1000c0d80248506c01c010042c2626082004070700c0b42c02d580848d0840c1e000718010060342030903070138698002e00c21950280d030703c610440840c3c1c44070010300032036001d6241c41114103510f901401c0e00342100c0781c60510051040416512110050585000d29400074094031000900c41040d101c1c0f0780400c2410801800d5241c50700203042d1112a84402c44a2240f0340a00440740031030b81c203102805404414002403c0d510161a0f0a4001c603580100b20207481440c10207000c42c03030702105003070381c1110ba41500e00507641c0c1094000c692908440d0b070f12050b4584900840801c0d1042d042d000588920300540d05050500750002075911040c445000c2d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 68264220 1250 68262970 68262977
    0x905010611031804020c0d0206011a0702090712021606060f080607020304090207021804060902121f0b030f01150e010602120703050a0e0405011205120304122006011512060501 77
    0x308080101c1814011091083d00030001854881c58403c85800e00d2082590800560020f400420441003003080c203400b142402c80d5071a02e81010355001450b04035020b4a60300030410704d250b00c044882640e40c101c3c1c035115218100d0100103411407508002400e0309004202e4100c40d8140001802c80d00020418040c80340c42c0c0286042070304000d0b40c0d0000b50072076071042c1e0b40111a44441c0c803480c0c4900010500844c050500807484824030b005004940d5809030000840760b01c0b26030481140c2840c1d04240c02c0070280c0303000c041446402d20340024a40610b40100308581c1d482c0c0700b4808100140721600001f1100d04204241d13039070382d03a01c00598964110550340e02410204010941c002031045d00100310f00241e03030030842c0f01050010041803c50340240c00210310801781070a41810300c082045001e428016181e5a10b1440c0361903030f0382d803070080e01260710710b000e004041082c042468580103005d42855134000c100c998560b51041c0440c0706d00011747d00100464101e40c0020609203080c043c0b08140c49044c0c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 68265470 1250 68264220 68264227
    0x108100b04020c1c050f0403030503010512070b0a0509010e120c03060c04030507050f0d060608060901060b03040507050103090f05030a020604021201200d0f0f150509010e13080408060f01090501061103 88
    0x40b0602d040c3c080070800801c48200180186681603074040c0c005035000b4ac0d0740f65141e40c1480c09115450020788043c0c507040e80960b130108030345203071041210860340340d61404a88401d10395005942d00b24100202036403051500c1119400c0f413000281490082c0c0048088402036118100202114030403800050201d4101000c14041070420f0211206c005c035028040303503100001e5440b000100d541a80190245401050900140b40000d018540207008945400361542c01d20760345441c0d0f20155407281074140358a5411140600c85c015a02404064000054030b964051012009407641411907049208a80468580a0668052281940703055110340c46452003200b0307058003a19070b00500e02d00110b443d180d2900c18000c403258021180c2e4807040f00c401003140011199803c41c03080c0c403034120302e018920040041105404c03041d5415003164283e0b00c0c40031004400d00b88061180b04640002480707100798006c2c4094642c0d800126812101c0400c1300f00440e0741ca43c3d00c00c40c0c1d12924160801c17000ea0040c07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 68266720 1250 68265470 68265493
    0x306010f21051305010e011d030406080a180203030f070312020703020a0b041415160201110304060e0c0a060816030b0612090a050f0f0d020c0d03080403170108100b04020c 75
    0x3a07102c16040780c03403941d060741c2056150761031030f0079102100600031582c1d440754851084000300702c14980c1505220006517040030301b45800203040301001409248440c1e2500e007040301003201c2d61414a90b60350040d05490b6039054260001c1e0507540840c1082300091840b41c006507034031410f44240c41e0b05542c59400340c042c280c2151611100100050000d0715402c409881c0002d02d041e00300108000ca00b041108843c1e54903000404440c41410301d21048107590410400c09010755078001101d611940c030000000d4002d81102e0010300e000f40710a0a50342000300d5401c0131803c0794000700030f1032245a0116443e80d18000f407500407016666525030751a008030b010310402ca049101c50046940c000360b0b61046030761002c0070341c842e649000c8a100001c8010340100030f840b00c0010007801141c82c00400350005020552020b000308100c0e004185024080140110220b070425115401c500402e4000e000882460350311203079640c1c0c644e10102041c0b200345240001190541c1400e0081e2950065010301038690340502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 68267970 1250 68266720 68266787
    0x20402040312080a0204050a05010c170409090302060a050f0414031e0301090f0603080904110903070603020912060601080a050c13090617010b090408133503091e0f03010603080306010f 81
    0x28020300301d036082d001c004251212507411014100420b0356600108071080fc900700a420221701034402d41626084c8010404141040c100702c80d0807690041003902103040c82e804403401c50054070304618006d01611040d40d0b5465220020714144c420112080042c0e402c0c06007040c045424600c001000b110050007103c440c1e10707295100440c01d5114400d210300d8000420002400d05400340c01c07140c0480d90205054060382056510005540028402000c450070a9000a06503400c000e0210000c10b441d100040c4c0002c1e425400c2d80c55040c2d0920344c03151100d403a146010042c02d918000c00c10b19102191601d1180101401900e60016025241c0c901588403501c4021a6900050110201807251240002d017031031540c40030201d1242041114040880110445005004030100c981e1543c0c014000e0441a0740c4030310b10720300000c1c82c5960719406e44d41060040b400700703582d071200c1035490352800c9400000d1042d0b46000f03600c0f58800744c3c0c03601c0da000700c050425980440260290f140c903524103840e0030f544441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 68269220 1250 68267970 68267987
    0xa0507051201110304050127030507020906010314042a050105180411040e041106040803090d03090b0a0908120a050d0207060f0204030809040507020c0612040f020402040312080a0204050a0501 84
    0x10040c0046208000310043d071007141d205844c2250705a55618060103004060444004034021142d41030b1400c18043c0c81c010014000c1100191040d0810b20108000307071701a41c00f0784140c0c803604154010616186c00c05490040740816000c0c80301642180c0b015a00400250041c01d460f0140c4585007081124468816094900760031a41c00a0b503500b0800c050701412405400103000509812001d442d103480c0240c0c40000f41c0b1425402500c0c18401407040c19400f1066519840d416200f21090b41d1190904030b82d1403503168000c4062081c00910b4401469214a0241c00e48072444102c640714600300711102401c0c41081c1e1014000b60081c411050f0011898000742009400b90202090000c010b100d010300305ea01940c000c40742071a000031103624504060041d1a0321150034009402d04002e001c1c04520a882020002160b0744c0100d4001010055400043c070343c5541c01500864945413245064102c0c0350040e8009400704000c075000404e0f51030b003030080781d050300c8000d400407014526000041d910441c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 68270470 1250 68269220 68269249
    0x90103110f0402272803050c060310030b0a0f02030112060b10050f0c120406110f01090b221a271005060402070210080a06050103091205030c0d060305011d0a050705 72
    0x8540c0310545c4240300488810100d0505400f05125400e14600c0c115242000500c8414001c4100348200480c0d40d02c080b1500d4211390700802c5104060b643e00800c90010143c40d01c00c1c0e1f6032148080008184259005007060107076104000c10030150b4440c9040101010722000040700080042040ea0340c1d0550f25000761600c0095001144c0d15001c204410369074640240d041000080e0352a01403000c51107080102c10856005c1c07000802047e1b94548805d110414000c1451005500c884130154080d08405100c0c554642c202514030b290941640041031070705000c1d142d00c01c44401c15854a400d84049040c4031440c0c24040307004000001c0e520705002c0c00b4060090a80d5442a800c2c4241030244c0c03109003000920110550b0b92500b82e28050400c1022603507203070019410589011440400288a40300e074041141903414102c1c0c40c1d81d034082c109074a43c401c2c2d10078842c0c11401d103800003080042c150410040c0080e0740100c0c003202071007000c0569603801e1858010300581e01c060020004d600300a411800110f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 68271720 1250 68270470 68270479
    0x6121806020702181e01170d03020c0c1305010905010602031206100306081603060509031c0203150a030609060605060c0d1107051206090d0302090d03050a0c02090103110f040227 78
    0x100e51107802c2203a004c100311a00d20341c900348250340c558840c207079641c050f0251000120000000010900b103da841042043c04024103074001400310441200700220104c03060010709001070380c044c90000c0c9000d040300b8403800800d541088008a280d90011050342c01024003100402c2c040c0d51094100401c201028541c00149940c80c035011804035024005400d010103480d41c443c0c60704e0300c0c5203007450869100800c1011240c1084c00b142c9420f00b1111209451020300c2000561252a4050000c069a42400ca000c0d4030000c90300c0c00108010031900101d2440f40031321030800c55956a002407080a105056820340103030000b0200c00c804600869608900300866400c450304544c4400c04107907443c100c0e04900c0c8440d0300c40820800c6103201080410509049442c0550502081d000841d405e1503017a90010180300e40800c4111340c10f0700c1920fa4541c1d10750014807802d0385503520704001685120401d91540101c140c143e041c500c505160089030360100e0001550910380c0b20b00c50044e500d982251844c40d612 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 68272970 1250 68271720 68271739
    0x15120c020106290712080702060f010510120f0c0c15050f2205030c15180604120c05010212040302010b04060b0d0b04020f130503070806010e0601030e031204080406121806020702 78
    0x118140c05000d100030f134451b4aa0405a00f003501000e490924014004090080140d0041c0540d0300c9040700650f8111540c2480200780380c4011341e82014110313554803d0b103820b107820b800c2c0300156806070340303010b40b00e01070701c44088880c0150114109030740302200ca40a51200c4540407c101442050062401d10440000c000f44c400c1a9070302c031070540d40301034440750b8140e001c1c24850032010800400c680d00710380600341c50b0701060704002d440e9844031070050014044151140540c07843c1400340201800310f0768082c0085598400ea690240c3d0f4602c0c041c1d030203400541c81e03c800703501c090500307202e4036064071150040c81d400d2a840100c02800b802354601c440b50426001d02607026216020005003090741407003880544002d00b032a050610340361103a80030140e9603000c0030040102c1c1d90239541c4181c0120080c07034042000362482d200c40f4034601c075100d1882421303118442000240500b050203030007681c625030744031a00170b50820341c0c65081d01c07044040d07228000c0c2c0700c0e025400002d8641c1c0c001c0c0889032025200340f10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 68274220 1250 68272970 68272973
    0x91c030512010306051602010e0c10020f030f03010603050601210b031609021b240402151902010b01050403030806062b060509061f0e030715120c0201062907 69
    0x1903071042070b481160f110741c48909100c01d1440b20b080384801b4008a20003002101d2413444070b035507900c49400c0380c24007078030a6800245019100f80807540c00b00040d08116030fa54142e00707440601e15030092181038000b034034000125199600c04c2c440d03d20442e01c2c05010303102c40584d00052500400034200c01680c544902c4a0b0b400789000c13030742290302c020440c2e030300e0068545c80f4801441d519180c54401d40b88075030704044401e421800d4140c44480707111941000c401d000d40d5691010424114012514400041d008181134284118400040308486c81030781c0240000380c49080107440c980a14040100402d4101d40010000e04110029080f4014858225a000d452a0030a003a078a00c0c01d003c100d100c1c9407515000d20203401c0050616800807010b588041c02d414844031b15140385160040001c04002e52040c1843d507682e001c00c954005003100e003026141808950401030407801407802e030056498140001d0200a0b4010310900c012101d05001856155005071445480b01814002e42280240103004840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 68275470 1250 68274220 68274247
    0x819060504110405040506030303220f0209090d091509030611040506210c0f0d09050a050d17130c0501110f010612020f040b011d211c0302091c0305 65
    0x285942e08019196515401c050502c825200020134050180d88104140040c0740d80c02c10b282801c8001508440440d060149803c40090920f0040a944400140140003d0250101d00a100000fa948505050075520340030009650300040914000c54a089000c1010500e1360300910450000841d509141175114000180250480c105151603013444070320300b82d641c0300050340391600000301d40020350404400500f0a415881650540c8034400c1d150300c807000800800700300241140794400240e40704103140601c01815080450500c0c4071090301d05010070b0101f803520f521103010319002080b0840060034100155201c14192091400302c1c1f00312491440c40c880c0c02e03c5180c01a011010349100015064010442401e204c0582c080c842e1b45008003002c40c51381c204c150040c0f0681d802c404904c1d0f005880c1c000038802c1944c3d00009940429640c11014045004503003c0491500c020303207a189012a44421002c9014851125030000e0020303140c4400440d6112800000502c640741292405070b50300c2d403d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 68276720 1250 68275470 68275481
    0x9150d0803040609030207171b01021906020c0705040905030a08100f0e0f1f09050709030206040e06030105070f09180e010c080402120109020901030b060a030f0308040203100c0819060504 82
    0x3d4440070b031343d8400c0e081010741c107225010080185100308280a400c0302042900c81c4120484668841e05130384184029900a01c038000380c651954268080b808164106980607600440c4503500034065100c000c9003e181c90308c100100c454120307000703509095141c08143d402c91006400c0580304501c480340003a850382c0c2d6107a20f070040c1243c0c200c2c40d2600e040882c031528034440c001d81000203156040d00d802c200401105d03810411590000c03404240d03502d84113000e1320b0b590081d80029400c00c03800900801c0f014500c0d41c1d02d6010b0102a402040a690740000403500b003820288038200203441a40c0400c00c418030000701401113102c01a001420051480c2c4c494211031504820304c0210b00210100401d500d05208404034403049a8004e000b96912a80020742141050100620400c0610003082c2e40ea150400068040c540c4100d0001c032200c100c0c24090446401114120320a100703803121600c1c88042406070300420061511020050349514000100b08041148092240d59540800081550300c50003071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 68277970 1250 68276720 68276723
    0x9050604050c030111030f070e0609060a0c02030717030d0506060906040e0402010e060c0c010c050a0204020a1701051020010f06060c050f0105010f030f08120a020c0c010c0209150d080304 82
    0x204014000b410a0500355881d42d00710003014502801000b55005007003481c00d502c0b40d4140703865000310040c1000500c0c00e000d80d0440507001040402c1c6070300c01d61340005500000b01e008804903150255a940c0c002c1e8210b03240f52408a581e041444204449240e0380c008a400000003400b00c0c0c14843c8081c0455110f400691010026107440c0041c0402d40d6005015a00d083c0000c0c0c46891800444140d4199030f44041c520284c104a2190640024000148022259a036000f0010356440541c080c0c020008040403809103c0f4050340f02c0005003601d040c854004101c082d903103c1711443e94036450380102880800c2c202e100d8954807448411650110f03031007140050000d98a649801e040c05e0300f400343c90b06039004481039640e0702d0400140032500e611064030301241c2c7c0c80300f603d0785404c41c149400007580c001c040714022440e90754400d0000c882c0c055005072406c041c1c00300c11120b48201170001190352448a41e0040d401c42c0303e10011800800da50010710b502440f000d81a4034280560759501e2503103501c03c440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 68279220 1250 68277970 68277973
    0x6090206030f04120e1c0809040203010312021b031209010e04090503190302180616050303010801090314030f04030315081b0f090f0105040c121b0906171303030905060405 75
    0xc20042007460003000e44c8401461401c45188094040401c0a690349180b03614103e0031900ba242d4200102601140c03035581001c2c0056451f965240341c55501c044502c0c3c107540250081c0c443d1085460140303070701d8190810009009000304a04130304540c4003030b400b0040700c42c10088810f62403445030b1035502032031807075a104000869840c0b8114207905030740800e25260004041c0100320f803601e5102c80d105800e243c810100c81e01543d618a007070390720b001941c0700075004000340004000010340c00c1041d0300030800380740070341c84064901c4010880040603200840d480ca034420040004078000c00e02c6035200401102c0b40821800040e0344034800c880c03902e01c1072402c903281b03200789486219090410380484922503805a13512100782c141100d00030f450301030500035503000c0c030307a0380750348844091049040c494140c00000c4108084c13030610015901c080300c4148150085041c0c190001a510310410720084104802c040c0c14005454031081c0d4411240460300030f404142d1030301e442e10080340c4144000e0380038070712940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 68280470 1250 68279220 68279251
    0x6010303020c0a0e0a020904150f03030806010302040b0d0f0e010207060213050f0a0608060103021615060608010f030f29090f030909130606151106090102071e0609020603 75
    0x540240340085000c0824000d083e180c1041103404404e6881c030313401c0720300c0400c050f80f121610004500180b191110442c07440c0020f80c030005124041e405641c0c00d42c1c0c082d40d20140c0903503078803005600340d10a034881c0b03401c1a030b420050b4038603144045c0d20200d2841e0081002094180e40801c500f0b00b641c101c5402079410607800550f242c42c0c0b0380030a60750401000169682d05800c1603004c00103d80c40c00601c240018003240c407000070707035980c4203504690345415014150660421181407000400c01d82003504c125151130700401191050003000950304076030b04003500e03540843c2140c1e20420410159081202c140303424411910101c0300071180c4038040d40307404541e40b2845c685a6451460311843c14807a03641504100502e0009441d1101100d0303000303000a4a15820781c12034601400108916803000043c0403c070703804207042ca64482d801c03c12002000c030450740345488241200d4202d101703046004000c105051420075070080240020543c00b409003400041e00e48203500424003a500c1100e0224262500c01c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 68281720 1250 68280470 68280473
    0x50a0e07050a0501050307050a050f0a080108010b01110705010c0302070b03070806030712020105040302121f0b121b04050711070303030c03060803070b0c0f0903011406010e10051801120c02060103 86
    0xc00c040c000030201207541003022450200040c04500c0040c245408000c1c0c0042c50300c010601034003c407980c0004041815554070127206005006400a0103503c1e00b65082c0700f403d0209621501e80c80d6010319007000a040d140345054019262034500080850550040c44c1e0000341c04000200610310940032034841100d00e1038060f00f00340c240281501310303038480d01589560602603640001035405aa60640e206541100365542007480c041c01c0c0010342001d07414420302d4080309036464100341640c00c401d0760854001200010700984130003200d0840d030441e051510b94600a13181c01e030030194000c841400e15103500d000880405041c603045800c25000b00b81c5807514008120f46c54814080148411006507040c000259242140b220000d04a0300906401042c1d0700c68411040048401f00e410040007000121050200310304086411264140442c142c4003d0030103500301840704036848191035440301e00d0003c40035030700345031401e01007003c0b410009810380c9000e0480301445407090322422900141030a43c0766 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 68282970 1250 68281720 68281723
    0x907030f05011d13150c120c020c0f0301110313030e09100608010603020c0c010c0204020c03070606051503070f1101090210200102090f150909100f0806040807030804020a0306050a0e 80
    0x1812000021901c2c01302c41c00816114490741c5d15000c4000e001041c082c1e40c1d080f040b6214403c842210650030710f0200c1c072101c45a000250417054407070a40d50481056000402c06080b54045400e0200a044c01c0000402001c40c806418002900c20309000340700315041d4001c5028207504540071000d170a00154140066a0040002c900402d9985815132609000c141c00c181c80b10f810003521818401c19407014000c5543e2501950030b0001018126515044e0900700200a0300c25445100e00895140754400f800801768030889110b803200e41c442d420802c0100c10200c0342921000798a07040341d541d0b0b000040042e0380d03a40c14072251002c130780d4400c41081800030745049541601108035003141e104024245160303c0702500c5044001045541c3c1200b10750a00800e4102d00c20b04ca0030340c1c0d00201c80380404c6990000e0040800640e0110310b0030b05246a01c41130825036441c01628098002181070240d040000d1003112003641c040d101403c620400d543d2a0f80f01c1064590907107204418a40703803048250b050b0310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 68284220 1250 68282970 68283029
    0xb01061202030709122406051201060609121e080d150305060c0a050c100603032c040e1903030204090b0f06030705090d0f05010501050405010b12060907030f0501 71
    0x6103000071495410b00c0340014080140340d00c43c0e20034502d42141c8040c02e2008016002204a03034040100d9103111007035044100601a82c01a207206400c1c00000001c50603052007000140c8003540c0f02c100b090341c1001d450b004007003c42141210f449042c4424240340162010382c0c880000e101d0380f0305a484600d02c080ba013080c0d03910030f400320481d0510550104041240045e1440d00800d20103034003651082c4c0700a0072510b600c940145039840b4801c146106041c0000d562110302201d000740d85075451102c0c0d0105c0303e9003c0f00c04d000b1340c2101c880510210607082ca007503444403507030040110445020360049002000c0001042c50287e02080d404241000360151038000c17191881400c80310140380300821000120a4003002c0c1816081000c08a02c90081751a96180c84211035000a9000c0c15002507103000f0b8080c003024050640218100307400000c80c0d40c0d821003030781d40d03d0200341c40c40d20300740e51141d0a020807840c005164078201070b2103d600c207280c42c103a8070806010300f590180141c1091640b101007440300c0c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 68285470 1250 68284220 68284247
    0xa14010504020108090f06180703060e0f1507120c03020c0d0c0501050a0b03060c0304050708100507021203090307020f031204080106050a08061335090a0504151806080a0b0106 77
    0x40101d1851019506d010581d903511860403010043c201c258034124a15052043d0402000a0700c0d100300e2003040500090101c00021501c170880e00304003030443c1d55641d021000e0703802d1800325140328034581b125442508854483c00d0356240040c10404180a101e28014007919010003040d40182d64405001c1c0a0048a074007c1501c1d6090169000084c00b007942d0740802440081000004000301c0c0400105000080091550704103c40031026080d600e90003c00040c0e4120025206464602e0001c00524050303a200c0d03101c55000d1400c0101c282c09201c105200200040c1d41070003001c15854442c07941c1d40240c00030b448c641f4000503c580c02c1c0700901c95810b40941202109500100801c41415200c0519440f2243d00c0f0f18402002e0100741500c1186400d503041690f00750044102e001109108a801303800000001c89a03180d22075612401d1104454000c8501d0034181c0ea125414420b662000c01100c5451038051400240382c2e90380c0b1007a60800b0010704088580c120004010400b0a034480a6044d04c030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 68286720 1250 68285470 68285473
    0x105192613080306131b020f0c0604032010020703050c0901050a1215051603180302030f18031603020907030e030a0c02040e0f06070909060e0a0504050a1401050402010809 75
    0x90624071100d030410740c440c0100038400c100010004102d61a401e644960840107040f0a0003c4c59582c0034007806124403030603c00040c890384107050100100007503110300200c0040e106615003401c0d5108c040c161040c0103007194013000601e00c5100c2c0307915242040c18113400f8903800f6000840c00d6291003400d0080d0301104c0c600c1800c1c4074005112a6a64080980844044012048503040d541c42c0403c030034501d044507146900c2c034003420004084802e20108030703007501c00d985c1040900207104607540c41107030000010780164018494007206040c044000c0042501280d1500b040d480c2ca9030000b403405464203982c0049a4850300100300710708011000e01e030004814201171101200d10107041d9502d006400041040203000001d4005540b5198455080b141c2e684040d11030f0b034940109441da81c0e9109444080c00240b0741240002d503030300759100743c4081d24200c0090b07010945031303130010b1070140802400580d00c034004c002006c000070b00384280800c0910603000003c94a440d060001400d114801821640c0c517 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 68287970 1250 68286720 68286797
    0x50f010e060f06010302130f060e0a171203091e0703060b060304081c0216060504170c0a1101170f0709060c020904030804060e01020f070203060c0405030714010519 72
    0x1150305124500f80c0c851020319005844e030300c1c40112140644840d41c4280d1100388208404641c0b95885083c00340b0070354040d107201c890103940d0071100303441e801d190702025031680010100088803402c02c0000c0da00011044121140311850083d103080324254600003894507071110b40e0420402041e0301076070720030300000c48401d42140b0301900e82000c580f090001e08488040030080284403400a42e040e251481e40c284881c1942c1840d03440d004c0000c100c1980c0907910042060440100060038000b1242d0310790480e0050b28611980d41d48041110344035a0700d25040c02000a031110a80280a03c0139105105400140c4141e00f048d01c4043d050240030b0f00b10908110308182810013580f5041030264200d07500d80740503151a903076030410400500c00c0c52500e8826500000e980c8014100a00c080c0c0805070084050381c40f0303901c4106448540d8400ca106007038054128600800c403080c9901c0c0140c101d00c006051241c94554407107881c1d016456611002c07404280c5201e9140c40341005050700c6420055034050300c0c2072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 68289220 1250 68287970 68287981
    0xf07150507020d2316020405061903020405060f04020f0a03060501141209010605120109020a0b0c070b0a110105100e0609010305030409150b0a020c0114030601080a0504020319050f010e06 82
    0x445030f90351092041404180940d080d03140e0004030129011151a034036181d152950401100a0350b4034015003a8883c0d42444007007001da2074000d4060742003900e6000d1402c0524603681c2444043e0900078002075010804090f090140c0d22540001c102842070341b540260b4031000080040c00f2280150095410000e800384610340c1c0880c5081114103c40c00303504060007550b07984549502401240d00074a40285030882500b90030380701500400c941c00c7c82200d030070118a85a403510034450140e02c110f1a41c641c0040c104000c0c3c07140160081c0015407052030402c0f080c00c0d0860300a401e4490548001d0108000d03846e0404c044000115103c4d013140e001c03141c1600301e5155443d046d5407030040d030180f0003147d9a40c04010f9440000c184000d030041c600c00301641d4503005071600194440b2102c180080c0031812400030000320000031030031248124416104c4800c5a200c0e15030320001444000e0003207030144a031a018064000c6a001c102c1003d41c0b003080100a14007804a840f400e680380f044150b5250381c001c40502a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 68290470 1250 68289220 68289223
    0xe010609120201030504050a050a0302030408100506061b1009050313060309030c0611121008010e0a0b01261903020d0903050c060307020a0b0f1006080f0402010e04020f0f0715050702 80
    0x309072034091074003260a40742c9050a038207040c09003800030228071840402e00101070b008000351089a1481c8251903207860107030201d400b564000c0701c2c1c055014004103c45c02540910321081d11902818400b2202c50300c003140503041c01c82d00e20020549040d400401d030b001910303000340c0002c2c0103804240380922001099a5002e0f0072080c462030003c05940c0c482d5a03034030f0049600c01c240c403011440128484214140814040545821030142d290503500b01250310743c144200003100e506007a48903070800d00c10b80c60f05403407902ca0184a9840b040b040b05031074208060020420003405040017000364070301544d030903180181c5415107000b8500107120209404101103000072807400514002502c9075681c076603c4900813030510380888802005040f0711011300500d0700c0c910801511501c14402e03018089504da15081c0c564400c110f801c40a00349400d00000c006522070f030000c100201d40a4005400e10807010b010840c10340011300e80303a800e00c002189940c2070003c80145100c030b040310640c0c01c210a05102e00000e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 68291720 1250 68290470 68290499
    0x7120501060605071a06010210091103011a01200304150f0210051b1602090708040302060f01030804050103020c0109150f05060a03020f010513120b0f0a0605130b01050c0a0c0e010609 80
    0xb2482c1201741002540340d900074001407040c45041d810400010010345080c01321710f80e10b036406500039881c113a9000b0484a030207208110b02c4d10161509c1e80b001c0242c1000162202e04583c40b841d1602092000045140c5e00d09500d01540d0025110b4130100803103d0380007844c04100608101c040f504013014030000440003e400d1440e581c0900e011a62804178030100e0f0700c02800303000025041840d040401420580c03140038070f40950710a41c00c0d60466150000c200000c3c0c0c40c20300000e0042d20040008226541c020307030003003084240d08000480c404150342c880c0103801d05041d0a00342103d4907081d680e5600270481c070070349078046801c68000200038195004620740250002c45503050040008814020014840d076080c02401446620310104400c2d2a000c0b003500e406880600c7c000c205000403850b500c40c280144001d446026200207580200c1170000800b130080c114200741131113130804c5807400129080c03080c24034043c01202d1142c0950702c1c0c0f000b00014001c059001e4010840300c00c00602c21030545841030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 68292970 1250 68291720 68291753
    0x80409110702130603121d040c11010f05100816030803060d05191203020901021b0409080c0a0c0e040c050d1415100801090510020304060e0712050106060507 69
    0x2440000105203240e541c41005000b07544000c00c00751030401010103410150030340b032088110f008903c0c6d00c0202a03441c00c164029840c0d03030110322032402600741000d034020070000240380342c0803490b001080c44060854884100302114643c480d420003401c1e12907031129000420081d401000c01000b0407910200c240744500004000507000808243e003a610040211b010a030040140c0b0f020300b084106156880781c6010044442c9040000f0703501d4154000c1c400d4480c4da20046e005000c10801c00b1300c4280c4000e036040480d95000f039803032100c0c0003c642c000e000380c002d0b00181030080050031118101008800160780c0301ca002a21181c00300400030310400f040c48200c0d907003500c20040f03491301e902d0302e072100307621242d01c0450a10418650625856900c514140030f007942107a980c0c0c4041e16130b0308041c00d907440f4100107421030f0707c02360940000c00c40590007146d1050088800103078402c040c0013030500301030031540038240301a00400c20780207210081c07068000520150a04c0c42c81d03c00c0e82d81c0d4001460104090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 68294220 1250 68292970 68292989
    0x20f0609070e0a180203032803020c060402010f030e070303081801150e06040f0c0806120120030a060302090702030703020706050348070b010902090f12010603020901030606090c0c0804 81
    0x120813140c0c941000c01c11201c035401800d583d01c802c4103001140340d1000ca00307190031002d8950300c52991118005d208442c8624a0303540607060650702c9070015603048010500da07404055507542002884402030043c040554071035600c426080c1001c84231041400c040c1d4801d903040340d14120b40840909040000c400c129050700042d1a6aa5030300c0300054010546c032104030496500380040e0300741240d03010300a90311070b81c0100c8201e80618020134040d822104081600d080b03054100c121a80001c103101c1c0550707480308550b5400f04101d0740325030104012030000d85844015030320105900c802c243e01400b0442c042c003040d00d482421494403009905540c02001d45101e003412901405a100300c005ca008804620040c190010b20790003007040d8400594007100041e40d03800243d20000c10b0041081c0201d85820344000c0c14510018494001c01c0304000941094614540d80c8039000001a200e550b4580e0003036010b9240055007a180244005c00d4900c2107401d0010007011407071007400141c028040d41c0903203c42d0726 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 68295470 1250 68294220 68294231
    0x203010e0c0607121110060e1e0a0b040f150501110c090c03071101060b0415050c0c0402030907080d03090201030c0e0a0603020f040506040f03140d05030c1c0c020f0609070e0a 77
    0x130243c452441d21412070b001802185e410b40440ba4003500100b08640000e401d8481c5c80da50543d0400a03000c1500050318617007030300d4011545980e00c0350042e00c0c21460080000525013040d140d030000721a0342d0300c003c4001c0901c140d010001903030010f0030403256030a980d001d401c80c0c8200d203002402c4074200a00403402540302001043c41e03d44921160096115144020481d1603111881842c150300329103d070003503854841e28041e550314811707402e49400c00044802024a034210b4810000a0340000f84005058801d6480005000c02c0400c0a04c03004c0300d05440015140410340001006c2e80c0450241d01d0910041750070000c9241c03200300460045440501d03006031503c0c0e40c071600001c148502e5012590242002c580401c2c01c5070640d60410403688150340081882c940c4051113034507000d65504460100e03106100040c64030050000420300c0c62210180307a04c03c60804200c01003180d041110303c0006030f00c0f40c1c1c40850005801c12100340c006502c00010003141c0c1c40c05613403100790000101108001034132036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 68296720 1250 68295470 68295503
    0x11090408070b04061e090c05030d02030d090f0503030a2007080307080903160803010807091104031203060b0d0b0306060102030306030d12061203080f01050405100603091a010902070203010e0c0607 86
    0x20790100000c409442800f008078140000c45e10080d00c1c0c207680644003094060300c00034442ca00010b00030b02850340c94001d58145138443c60410014440a001590040c030200341d40800100248011840b60810301c00c005072400030000011520364100c0b6009203000d20400c10380740801c00803c10340c1d9201d4003920342109155543c1186600b94080c444103100e480f903010f4000000c00584c2c00265051783c202804880d01c0c1c41d0344400c40015150728484021600108000c24000f00305038803a07505180099080201d00c07140c2d0b480c1443d10952040040d00345207961044195114502807141d290001c100344021070031400c062002903181d14642e611034080c0b192107400e40b09505e2054000c840103110200700603000c0003050401130f00d02001182c0c0c40c0407030a102e40020403549810721446d401019070381801310895050000541c014400d0078001c3d601c00c0c030108500003d0128440c200c50180900010241e01e8a80700d00c141070941f030030411401c000703400ca070448074881c0c2c171810161500760b600400b41d10000500b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 68297970 1250 68296720 68296733
    0x4050a06030803070c0212151306110d0203041211030f0705150106020c010f0306030309030f470103020f062505010501061103030720030c03040305070311090408070b04 74
    0x101d60004211080101c01c000d00329030401e002d1040b0900a60703460508008031000c15445504110100e80c680920030003040340411445400d9820314816140040c0821030445120381c16002005083d0718a43c000041000b0071001a804803038030a4203040412030100240da009449009110349a48039220204c0d404090050070440400249800c81d540b00355561100c400a49605100c0c0c2c0060224034000d1351205200e209214030306c104d039056520141e445041d135840400c1c0714164442501e80e6000d125000f07e680c01c140d05580e84a81070071500c100000f010030291143c8070b55101c400503900c0107440040015071a9140380b00202c0b80e04035692542c074030740b0600c03156000e400600029114000b58a00c01d040080550003141a0350b0340351100c03421807084011265580c071046840000048440d40d820181d000b080c82e4a43c0d50900c84003c0c0c03802d01080e01d9a50f450b540107607205491990100c40c04109000c0f00c0007020700c1095003501c00c00c10b01e01e00360f1a55005441500c000901100300540000c2c103007d034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 68299220 1250 68297970 68297981
    0x30e040209060f070b07080f0103030509090402060904380102070902090d1502030a06050402030c090405060109080d030501170708070605070515090a03030c0305150108041b0602060f01080114040204050a 89
    0x400d2040d40c0d032601004c0c201119508806c8800e040450b6450340401c01000950010b1030499074182d680a140c041d070703201842052000904101c0c1c100c1c0051000501c0c3e03070307a9030280b000300010002406a43d0450b0043c0d9544000c0301c0000004100b00c0e264050b80c00f030741c0c08540c21094038196a030140e80c8544010100c0c0e19069401e00103031650005401d940000c0850b50000d5008075010301e4140b000f40e85070300401c812407000352200148880200043ca4190034a504040d030302c078070305040c00f040d001c2ea01d1f503049090030710365011000000c0d070356401030010181700d2810015281440c0c0c0146200790a0107005656504c20340110300501401140700000c1220400640400740c811020050082c100702d20703001e0703071400300a4088010070300b08106074401d40c0c42032080301d105401211228071400c030450300540300200090419150880c0303188094a101420710041001808594010003003071902920304c41d40382106810440780360f4101880140c421002000440c2c105804480010340d5440d4481034000412 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 68300470 1250 68299220 68299237
    0xa14031b0f03010609050a15030905070b0c0c040608010603020102120f0d1e050906060906130902061605070f08030406030507110111040609140319021206090607110307030e04020906 80
    0x2500c040764002240255040710120344454003030540b28003c211200d138141c0203103450b80c82d190620007111486500b0144c03209000e02d09885155844007035044a641c080b030f4100826500c10b884034001401e0600c070315002468040000c101c00c80c11680001c0d11440050180880100003140d060b618020800032610004840742c420050348540c80c3d08070002c2600a0342401c80c25180000140d8203010108406215840060000b01c1555581080199042040b4007403008155030710040300c01600c46400500e0044020300510070380c8001450305615003041600f012195440d004410040000c0000654040c0d9030b907428003081d03030fa680740c9007222941540f280440007507007403203203c80e03131100c42c44018000d03106160b6a040b9281d40711410800904162203046070564840c2001b0a49520f84d4510300d00e500f44010000320003041210b540324139200003502e407188141c0000050005d130580041002c81c000500ea4095030803c500c03520043e00d07030601c5010460040d034000603812010307940c1f0000c45100b030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 68301720 1250 68300470 68300521
    0x30d211104060825200c09060411070b151207120f030c0203060f0a050105120304090e121305030105070c08030619090c0210050702070b0301150c021c0312020a1403 72
    0x10307026100000e1140300305031346480721204080e105d098a40400f041c1241642030107045101141c07075050a000003040c2c0315a0039408071405000f6840001d20003246213014107298403007505034a10042c1003104103d08035522a0890313029000400403058409039400500307820055507010404c3d54107054034860601c0350000c2d814001c8600700002040c1035550076005010035041000542c0e01d0301d0500c0316041d00c940070440c5950040c40100300a6001e90095030803098400c003078a564441d1800704d1031840d0001c089010b40001078030014040d071b003424401c80b540f2020750321306020501e2217a2540c1289220141c40e840c01070782900c18240b032500192420800030905c0310800c101090011030004cad10b60080003800b04c41d0724108000303c2c01081c8000f8070715055801d2100c545181d641382c202001d5000703000070f24520900451b0400000035a80c0c1c44c080c0c02203440221502d400801003490020000c6140e03240f4000014810300c01e02801c141d11040503464211041d8605599440d4030f441c4403201ea00c14035080019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 68302970 1250 68301720 68301781
    0x9030403080715050105010201230901060509010b0c010c050703051b011d03180a0614030a0b0303160303050a0504110103091707050c0a091b0f050702030d2111040608 73
    0x8010010700e101100b070f80c1d4000d04210590729000120700383c0c0e001081889000c1e1203043e644103d0300e4002c00716504200000000036649503204082094410309a000e034482e50030108558481420a00855032040303071601d01545059481c1d40c0180c018086c803031042d10540f000307c032040b6030031009500064011442e40a06500d8102001c80c190313499004901c0681c024110b4841901241000a600019284a03445050007031034070f400481515000140010049910313540303440d800e500c0c02d0005100445074640c0400520f401420013a06a8801070607000f4118a00410071012810021640203102001d280100b0b0b052120300b80459010800780c24445480400290b440400200040c0e9155101066514011700c40e5505d5503503084406041c0414a251000102d050324140706147c1d20007085100c0c02c0c00c81c01e22103190042444c2401e005019408181031000c42c01426405c5c0a0012008203101014410301d46d40d003e401c3c2041c0114820b40e818065004007042d1800c0c018428080e65041d41c510501c40c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 68304220 1250 68302970 68302973
    0x506060d09081e0418020405060d05130f0503030708010506030405100e07030b0f0402010806092e0806070906030b060a0c1502090603090a021804021c0311010c09090c0801120308090304030807 84
    0x1443d80304e4810883c100b4510200c0320451541030007660119400100340c1c41c03c1c5034158218401410004000b00c24610103c51250001910a00e11290312400390004644070304d01410041c14500c41a00a04d100399000e00070807001600010720303199040340c030890115a0034048940d44d40381080e1500001c2c541201d503810454818000d4440c50f1189000341d9450a56445550030b00c81c12800c02d8408609902042000181454000003503004c0701000f003800c8450b160fa52502e0b2424a0025180302c00001d40008003041241c0c0e240c0101c41074440111000c502d012044079000d805900c0c0c07148001d00304101945d144242d0b00c003a43c19510b9228000d00071030b9807464048521a181c18806600728403131300820201102c101c03810740070713944140e03409801021040401203a040d445920550201c0c10030000d200920300e00c0c403083c010084008082d172140c0c4602401d01113000c0641c0d60001088080191400040013402017044013030301d1503501420000d4068489004044c29842030743c10150004100150500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 68305470 1250 68304220 68304277
    0x6100909110702040c0903030504030f020307050409030503040209092a060409020403140607080103020607081b03040609030c0b0c150c0f120118050606041403010b030f0c01120506060d0908 83
    0xc0c814421502000665200c110070b50b40c955540c00054002100ae00090000600f06030655039060300007000c85075007903a60000607090700c3d03030884100d00041010041c0b004500385010794a41154103e8003a009180c5a074903130b005844101101c0070240601d9420010391030301c42c0c0b01101c000d00200c00055560341d89a003403060140701d0711900d0b13800b40d101d0b010020f40d82506c0f9402c224180c2c2d038010300c1c0302c0c58201551140d66458101694007070951800c0c1d04500c00710700d400c000410040c807030394803202002e82c514140b14001e0940d80e4045403100c401044001c8502001103018004000703482d1020b04142c841d900e0101c2d9500904001c0c40656200046030a40e001002c09128102d801c090045400042d65142490507540280c40039504500240030a100340e07811309420603003490001e400010516030010009144c040344c4122880b2581161a01000c1c40d41c0c131615105038071049240501603801d114010030303000c0c4290640f0035111035849038441c080010200071030315085810300c5110355880340a803001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 68306720 1250 68305470 68305477
    0x1707050f0304050d060c05130324021201060309081903060f0503030c0a0314090303030a05010312021b100507231009020d0803090304030507080c04060f0e0610090911 73
    0x261468490038414a0030040c001085900703841000e46100701c0c81d00c1c50394602000e4a0311912401c18405c00340301081c1c01c4290010000d005602901002003030f900582a2044055400400c0c07240e028010411030001d01c84c2401d01070304417426450300294040b1a81422030b00d030f0180260b000b24420000710046a00340e810703002003003503400b070000c0120311a64540805070b4912074030000d41080d802002c20400480d01039940400c80c800c284407464a441c0329000020f045034011141102c080e40d4400042c418014074541c803a8450340d5500081141c0c1d01141100100c050034100080d10560031003105203105445402540c014a5204101803240710040e2080c502071051040300c501c6500c03070704103040100080f9016040500750040c103031210341c0d60ba540312019158001040d030b4403a40b104100000000794108a0f00b0000c041e400c0c040d0116511401c100800e8440c1503000c40d88990840f00180b02c3c0f042c9924906401c00d03000c9610200c0024065410380d840c003400c0c2d105d4407941d85880342c0c981c410109030009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 68307970 1250 68306720 68306723
    0xc010b0a05010f170a0f02071506060503040503043b04020f0915060706060b0f03011802072103141603061d01170a02150c0f01060e0c090a031707 64
    0x80c4640c0d210001122082c2182d00410b0025100c6580c5086001501407442e42210101c180850018035084860b0705a034841002141d034000c035800e5040ca1700707603207101e18000313070800d45001c9145081940740d4680d0ba008038000c5501c5030380505007d021148590100195001d0303000301846900312103891604d0800002c560507800740d48450f0346008180b51841c0203a20608140860200440c4d2610038030001ea000440c044903099030f24180892001c0c205006001c086440b078481c01d0b40e07981130062805900030540015100d59006100c00d80019a00100b01c000c104101c01c040c0082d0095410214094191030f1803e030000d03810301080c415402d04950707641c11003000f10b85051103507a41d100c20040c5205a0300054081c81c444520051101c11142c080030408400590201d821359841900000c0c80c0401006205205502c001588008410180480c400c280c400070001c0100300c1c5000001400c110703000f0030000c041c034000526402244d40b001000c0c0086d5800800302900754426003c80340d21070380302010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 68309220 1250 68307970 68307979
    0x30602030a0c0c0302330a0524010203030406091a0103031e0203040e060f190e15100c0201110f010e03090307171c030204080f0705010801060201020f07020f01090b0c010b 75
    0x41c2c00c0c000034014115041c0c02c562541c0104904668400c01e4021007078250020000e03400081940850b800c108203641340626503800d80083c081c01c01400c2d040c1a4000034a01283c0790092001d0a8007a81c0c01000741c9a215410820200700000c0b14a17003291000030850541292065a00c004030503d03a100175415000c4c00c40544149040c144810b080c0c2e03481c0100c1c1301e000081c0141c0000194541085e10101200d0354014060201440c07d040c40b9440d0540c0c903401c03044c0300d64608010800415249014285250381c00d0785e4a5070030100062004040204c046006414445190301c040c2c4400b008011740c00c00c0194000081043d030f0300c03411595403030381d020710051341c4a441000804079001c1c0c024080008400c001c2001010300404a04255840c0031828104a060560034800080c0c9400207100148082c03a4420241c00c2e92810200050305e030780d1041c1c104208581c418010048620942c000311000030703070101c2c0c0100000c08c0c0c0c100101d46c42105c680011100c0130002c5861000c0800541140070080800c88 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 68310470 1250 68309220 68309231
    0x1050105012003040306090609080304060902090c122a07030804060506040c05040e10030b070509030111030615091207061e0206040f0609020f100207031104020315060c03070c030602030a 82
    0x191514074110001d104250a43c00070002040098103641c00320000d0b912400c3c0100304240b40b40c0701d4030002d400c1100d05036000b58642c4294403c5280c400840d03944030000e140000d00b0700039030382084901d040300203107400031110344425003c0b0000d15552a008050078005080d580e00c071607074500148104e01c02e4038210380c0f2034248008910340345407502a001da4401644d65a0342000e28044411400620180c14104060a071145c040040341c161140e4501c0354085446041e07581c04001c061500b16101c18003085481d54050092000c81e540f1803040380030f030350901d43c0e000c1d482d0a44000090080d00003070f07504182901c5005000030301035400c118810811000d04110103403007a040300c0243d8a46900f107a0090040341500c0d040300000b40c5a500a04519001401009440c0c40120129400383d00c2d07030850001580c4141c404008110440c0e02481368101c00b81c82c198154180100c0641e07448e00000c0f4190720079400406c202c2884181041514031a40d044580410032540d40e040810080d801035421180340c60a02 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 68311720 1250 68310470 68310497
    0x2101205100308030f070c021005030609090a02010e0d0602220f060e03030f0313020a06050d060801060b1207050c1002091e09061309062c0601030804030615030f050105010501 77
    0x2041000c2100d42295180745903540e8204500c401d1300000b0012021f0041070181c000140c0c442c01c855109001c1d041e2900c550740c0c00d2510411001003001022070030300c0d03800b91b0308140060360310041c0603041d284c0954007441450103030320f080d034042d0280050304002e07030041280340c06500c22280410000c49803400400580340d921032004603022050b4441440d09a03004204103201104001d00035644032401200c061150400c50303001584060351540140001000810403011521903071048000819040c1c008020a80c17500c0584a254010842c0c10458184088001940d07180200304440c4417074082070680d00f03022200a0440001e4003c0c20040c0c0c02010a51254540b040f03d048080c0d801d040c1c01003412000d0350712502000b070f040601c07545002200d40c0f140c84000c00101c07940a114040c0c110502c550f00200c01241802d41c854100d0300b6030500d507502607001040030501d290304882c00d80e5007090b800f04060142543d0b000300c40303809a000404524201d4100001d0050662040f07042e01c1090b030310781c07d131030105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 68312970 1250 68311720 68311741
    0x605040605071e14070606090c0201050f01120c1406090901170d05090303070f0510141501140a050901031127030120070203010906020f0409050604140106030e070302101205 76
    0x32101000c3c042000303461315030b44c20844a00034007009071040c000880c00e2500e580800c0c041d100c05946800140c0c0d160014800d00ea2402050240909101e201c1c00c2059182901e5900c1209000d10480c0d04680c1c100d481300b005030b140c290480d0702109019103210030b1035030761340d1124900305601040c90740305008a44c030540426100d10200c80900038014001c5080070600c0d01c601456080740d1070110385a00c00c00d6455801029a40259003000040911850b55032a000c120740b582c0c080f51302109410020480400040c00482c1c00a0781c03c03844144c6005034841e0303503200058000b0002e5000b500041d00c1d002c074042141400200f16401c440b0032081402002003014000d240c00c0c1c034016007064180c44000f05441070030b92414400b907c0360500080002c01e0108180d2100c130300300d0f804070303450021002000a0601c40d80314180a03064000e9003d0b1020460000b80040914081c1018041c1c00d04050301c80d11880480e0000f048400040c540081806064000100014180606540100034941d00301000551000b11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 68314220 1250 68312970 68313017
    0x60f060f2c0106120e011802120106030b01210b04060e011d0601090905070e0a06080616120b06210610080103050a030509060f1c0b0f031506030a060504060507 70
    0x80d070310140a80d642445800d40304001c900600403110355039840c130202910424000e04200315440c0151030034142440c01881346080594520700300c1681002001c000184a19500c14116100b600000d590041d800710340c2c00741d0075070446005c1e001b40c03900d4040c0301c1844040e40c03282ca1620340c2e010003040710140c0c51a000c0d8030b42d8041d881c00941034210b5001004031000035006032004510450644003140e44507210846038560580700aa03400369554802e014840c820030500b900000d180c400031039a44218140188498030110224904944420000072581c548500359505881085808110b0a4001030303401c0c140a401c6030900c0c80b5408410908005502543d2800c2c1640d4010002d0188110141c4041c0c40c4c03075019034803054101c0000c02201040481c10340203819080411030150416050150314202035456031403e692061680d4801e40c042541d00003003404601805541034071181d600c0c2c500107030030501211800740c103680c101010041000440d034081071040b4003c2d21140480c0d900342040b140f4855 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 68315470 1250 68314220 68314289
    0xc090f0c0c03030c051b06010e01060206090c010f0903021c020924040b010c08040308040602070501030b010e0103050a02130803070c060203070305070b15040204240e01021009060f060f 81
    0x14442048880440e03c00e403c10f0700341070000d003012407809100a08140c951000100f205655070820700050048522201340310b07005100c103100801003801c14804e240e0312444ea10445c6411700c844103c420b42e4190040404d1030085800805091444090804c0c04521440f1141d08911400700c0d28000391802c035072803410840b80360140d600e4000f850842c006000c01082007403109414061040d081c040040e008034000c0008d1071280b10b0840c0c5591078944068030708071180e00a0780c10f16040ca2101242640d120290b40c56800d02440d002c00e045d2a84000000288521a410b04000c004407002040904000004040c0e4a100328000d0308d003190384550880c2c49000760300c0000c1c00110b04100309000f1a08000c2d100741c0214585400c01802c01e411800103040341d00c82e500c040b100c1c0c810304000d071042c00b00848003160601e1090a0070a0380b164403c000039120401c081d1420385050350381c00303101c050010581c860003d402c4035100c10030550780c0760141031402d54654411080042040c80b81c402402d090b0721000c03140704 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 68316720 1250 68315470 68315477
    0xb060a020a0b09010e011b032d020d0e161802040e06270f0105040b240c0309040e0309090a0e070501030c031e050106090f080607030c0c0501090c090f0c 67
    0x640341c0b540c80406000000d00b03980f0b001e42d04c9100212001c1001e11800c2c19003c640c0d0340a41e2801507000019050b01c2445014906c800321207021403102440c1072a103900200c4240790010b0f65092580c600c04000c0c0007520105407a44201742c0340d402072540807003840c2c080c0c1d03001c0f61a055500c00c4042a00f02030348540e00951400003d1b24000c10014140405110714401014054a54502500803c0c007203601046070b401c00c030000104010485030074a441100352440054410003003c0c0d40b41003043d10300c4840406d01003d04103000610a81e801001c0c01621114900200240000d45502840b9642c0307400200c030b80c0f4411050403001ca28404114410815070a000381d01419605207800019001040ca00808c1c4080c1605d403085140140c2d101c60900990001502c0009010750520200034010162500004000030030b41c00c050041640c0090800c0e4080c1700c6141c00b082c40c6401d0b4004541c0c0180c0b280c0020070715030030001344000700241c01c04a0400c0d02c2c807522003001142c54808004055680504079070010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 68317970 1250 68316720 68316733
    0x140a14010807060f09080d05030115110a0209091e1b120a03050f07020d1b05030f06040f05070302060301060e100c03050d0f0608030703030b191a0a09091b02010b060a02 74
    0x19000d00204c0501c0842e505101e4000c03603491001c03a04241c00071004c1400500000014404841103443d8010740d081d141c0392000c045540d5020059a07402c200e10041c0c454420040042c3c2030100801c00080c0c001085010a400000100800b0745d071840c018000320307080e508088034404141001e0704902c0c06034140c0c03401011400310645080d43d19a22180729070b80401410098600940c444c0b200d10102c00380318100592a0588040d0100141080c58100501c40d81002c1c048150a200003e8103a030016007100c60080054614078026280c1043c03a4002900418040000100c450300702141001400c8190703102d5542c0c0da0012000c4407a544540c3c802004258144915481d180d01503104800c00410414001000ca4560200c030386103411122040300080d031038600c4403c050804c030054190200340880034004450414841d140c00d80440c290004202202141c41840607200300c0c401d40042910b09810070418400800c0040303880408130300b80025600b03000040945041120448891814540c0035101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 68319220 1250 68317970 68317979
    0x504020a032901030f060501060e0f04022104050d09080307020108070806030a05011a040f050f01030f170d09051e030a0c060204050405010f0e1608061210140a14010807 74
    0x10480c800704400760445821100454210b040b07480d81d9070181d80a4107010404080a240107402d807181604468100070814101c1082521004070a1700e05031030807600961210a50035018640300013400c0c0041e442041c040500c0184007010408120811a540d2006100c1c0c4e240c00c0c05598034821100300031300207055500003030043c0e4401d075601d070380042008090b201c9112258940078259200f40304a50b50018030250203030414680307446407448401d4440701c18413081ca000c0124070804041403002403d000d02c02000801001405070024628400769114940c6811801031303401c00800000d2350450756407003803c81e02c0b00b05040303c10707010341d4013412480254030786191141d048034035080f500d4044803242d4080c44041038a039150301404e80a4080e940200c500c251601056080210000e007454842c0100301003030541c103d5002c02c000340d000d04203a40c13140c01600707180410303490000500d1120103404d18020490301c1441803078018901651b2413650a100d9074102298140c00140300703200f0b4000c40d0740b02e13007000c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 68320470 1250 68319220 68319233
    0xa09020c1b030c060a030b0306070503090706110a0204050c0f0708120c12180c0a0905090c100207060509010c06050a09060506061218071707061d0618060c07080a0b06040504020a03 79
    0x10601c5c3c101d00d401b1460405580200345420300030745072003010032404800c0041c01c00d02000700304014641403600003240c1d120380340096110702c3c520001900032504d800000c1d1a0f0b000050854908900c80c00c0b240382d50340f40c0b0381491091a0000001150f8113a043c0012403200d03914039050300c22400302c0300b4004141c1d8031103e083d0392034501840700c00000c1d4001c040f032020155880f40d01c248011b02c1200804a060302c0d01817036407170030004c0d0034113000d115000700c401c2c9440b0f80f940025808141c0d001402d06035070b1504003c00503904a01014002000340b402c00c01007001c0405070790040d247c2d042c0700e00420301032600c5803001c00985006a0203203050840c60000003400482001c464481104d101605540000b610303001310062440f04217280000d2603105001c1003259507480940800400c0041d24820102964030000070524407928241d812500740f20a40412150703030b40c504642a6151180c115034019541d5680075807100030451040e80c0c001c000c070002901c2401c0502403641304507801450010220304603540c08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 68321720 1250 68320470 68320477
    0x1030b0a0902030f010e06060f090106050d0c0c060204080307060506010801140f120105130b0a050415050603070801051005040b0a080307120c0506180d020d14180a09020c1b030c06 79
    0x260f078184605200308a45140c00c0c407030442540f403008040c20b420320340401400300007814149a6801024644010000d4070380c464162000a403182c4c1c00441c1d11070000000b22452981c00b9800380042c2c2c400100055100310001c011f044140c0315400920560342d40bc001503e03103690900c100004640c0c1d2200001403403800c5c40c0c10307082c200402000a40040c004000c00c41c01c40d80b048600c0c0b40e80c288920428424441c402d500b240c1d008021103030912152605550381910001d8030b454540c0c0280d2107001142c0c1c90307071301401240d002e0118440204090318203030741182c80c9a13506128160040c0c2c030782600c1d10320300e05002c181d00007600d03428030007546001d486590b40210709955200b643c0c00c0124015407200020420321a82e40218031280c000c61200e1585403040d41002c103881c8981c002d661140f049100440d4001c803c5c00741d0501581d82064035240d0380890101c0a00d0b207620380036400b004100000c242c85089901030050341503070310220791035403034100402d0201000c100384659040e440406000700314544034004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 68322970 1250 68321720 68321723
    0x70513060902070606051c1e11040504030302130911040302060f120901020405010f0503060108041401090b01121106030408040e0a0e010207030804021e09061009120c0501021501030b0a09 82
    0x51480c0d580c1e4090412030b00044001c80742152628001c000310300e841e40601080c050194005001c490050b07848060034a071458120744e28909050020050041192072006100f030041d00c184814a480d2800500942c00004800004065a03402003114001842813310003019004418079283c21902007021320340120102c001d0320b000c100035403c0036624010300a40503240d018000360304c440c107100c005450205130841403402c001040c010011541e9104855540050300400113000300d180c11881c0d9800340003610307000b80608051000024140c20070b040c01d4080715028800c0c85d1390081a440400459110682c3d002d8007074101440140004d4150301d01a47d040a03c11000144016528800d20300ba42c029080c26408202d500313040100b0360520130301070b801c1c184c41d0f00c8d8008075000c200000594a880003030600390040d0728540640c501140945030720400341c85400065031111180f0b2400c10045d14090103142e00500403000d07500c2c00051016541410b070b81d40003500a9041d60348110100040080060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 68324220 1250 68322970 68323009
    0x411030703170702041d030913020c070e010f05030304030323090406090207020a0b0a050406030504140a0506040c090c120b03071e170d08042a0b1c0c020705 69
    0x800000281c1c04112000c0960b4200304816161951401003100b1541c004880e00a08102c1002c3d003084100044100d8202d29401ca45488155005000800c002d009240111445200d14007004c6001c50070210428102c403001106007912588600c241134a80c02240f1000b80410b01d0f89130030050701e880e0381c0001c210340e1060880d01418441c0356000281942c0b4030b944814855680000c940c000d509141280c00007a0585400e21131412030440002040341c4510f1041d001010f590340b000ca000c1002030030b802d29003403140b0001c50311003c480d070400d2030300c800d82507600303c0d080344540f14005150185e601034444044c0e069200e869101d40c075400c5e84006084e00d02400f40e45402215070119032504405141c010190700039004441c045c1c01d181a400014214182460071503000002d8076145550081c80e80c0d0b80240e1000403900759007034070004410002c1941c41d8401d94419030820210b42c1e45402e202608010041c1e00c4035480c0710340c000310f148040324a0b01060b0700058018035018031042c1050003144141c00195403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 68325470 1250 68324220 68324233
    0x62009010f0203131d0601030e06070c0312050a140a0603050714120607021e070506031f03080304051005060f0904140c09090d02010b191e170a0302010615020303041103 74
    0x300401c1150a540e003200d914003086401700b0b20300d50070304400b00341d0140c070a0800304619911840d09542e07640c8010308045c20040140071690400d0b110340b040b0501441e02420602c0642010000e08014024540d204040c4503108400540c4030b21250144100f00c0350080d000d06082410f1010300c82101004424054021015021469115804102141c81040c05a028140c019048698103107220010a144078144d4000ba1050050b40d8038807003200d4005129210209101d03d8011080c190145694005081000003000b000306000c004036042d2510841d00c08108103a070750f1541085461032070341300c40d00d800c15003010000c0c2c0000c549444940e0110040003c1b1182001050006110b120003107504d2082034002c01070091800343c09000e150000e000484134100903400c09a103a0389003407624070071158404407480040043c4030360f0903c3d00002e490a4006844038480000150355103429004048006601e4280c0000d80039403e106260702046c200c0c0e0165185840d15103902c01003040d0105000d03454017414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 68326720 1250 68325470 68325487
    0x1106070f0b0a140a0606270b0d06031a0103050a02010305060301290a0b040e150d020901061707081501050310050a080a060506010503100b0d060905010b07062009010f0203 75
    0x54098921600040201003040c01c0802602c4000c1000600040707006401c14101b404042e130405441e180c07524140800c115001c0700058500100e40322988400d003256000145410030048541000c02503034003c0259044100340c80c2114050342e0000d1101410503044440c54000562003600400c1e00518010004114102e60121840231080d00e10303c00645842c000c2d465078002d0412007050f01c001c0c41114850703030401d441c00c0b0f41401c1840700206640140501c480340d45100381d44000d0302150080e009001ca015641e142c20b40a0f19281c09410480ba150401d080000d03840380c49150428410a030701c0304100700b074006581c01035400d0f030805002c1c402c000b0220040030820392202000385000b0310407100100410041c1e801e040f42200d801501050400c83d0400801298145038642a003c80c1c00d81a40c5540e01c02c500e030300c0c01c4020800750700030a00d0b0700d0904000260f41d0364088054007400f80a040c0410507028900c0f80c450b515046800e0b07992104509100200003507008103441c82c1b41c4da9490042e2840c1200c00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 68327970 1250 68326720 68326733
    0x31c0b0d080d0e0c04021204020105030c2703160b0409020702180403020102030403081003020108010b0c0c0301090309050102010b0315060d0804030611040306050702060717100305010911010f05071106070f 90
    0x1103541842e01607620765540382080400c200c626100c22040c0c50440c5000848035204502010080000c2e041c0940000401c0750207817800d0031035503900300717075081e00f408094006030049004a420320316611074841c40c1031844d038000b80501460f0484403900412407401d40341a41d03680c080e420809007645c2c0607000c0c080c400d5001240b0030306244960701c2035000503500d250624014000320f00207800c0b0349049102c0842440180d03000984607066440c01450551681c1c0000030040c03800165001841e01135003081101c40401d0707005006601594001d030024060b044034030043c1581c0b80c25000c0c80841c0400c2602c00b103059420800b41c01620107025170001881c20303071a52121810f446412280c0c600e45c07040010f08005110701481015002800791000d40b0340ca04040c400148080318208154600060010116540c00380500d0a2001598890700901180c856800c000031205440c0c1a039501280b5568846140580300d03908541c1407075481401658106040824000c282d088610107c41501507442d114010652 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 68329220 1250 68327970 68327977
    0x1315090e0103230f0c0613050d030905040c031119260114010e01020303191b0201091202010c050703030519050903030403020706030509030406030e0a0804080d0801050102031c0b0d08 80
    0x595030105211292074450f18020030442c040340100c0d0481105a01d908001040d080045e9000700c0ba11a190f600ca0301c4c03548989403180c6c0c0201d41c014410038507c0205508421000212407007201c0801014000f0340382a025503c21140003908a541040706000300b00c81d503c0c8003181c1c609140381100d4100241c072220810180501c51114005c2d02ca2401004450f00342c00f24009240301c00e103051510341da41000041d5483c080644401c012610700103c4411100315540700005802842000d0401c80326000400b900030300381c1500980e101040414000c04550050003414110040c03941c0f07040c40c207a1a510220024280504074520701c0c6080880252500001c0c002c1c076000d0107040015507601c0c00c252601a1810801e58482e40c03c3c1414841040403801c80401503404680103030030007090210043e40035608040d044a13000781000d001090101c1c481500242034a042001619600c0881e621040166a20f029000315450300b2006482d190880c0882034025004203980503007080c000b450b20785e581161941 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 68330470 1250 68329220 68329223
    0x50709050f010816030305030c030910050a150503070807030311010f020706020a0f0c02060405040f020f0c010203040209010b0c102f0903010609061a21011d010b1315090e0103 77
    0x40c1c49a0040c0040788050251003c1825a580c0301d440d42e0b46140e40c082c3c282d0100412584203003001100055140c0404d01040c642400c11361410010792a0400c2e2a80051198100000d03000342c980101050b141000250311081d610048001c040d00c034503641e8202c13500e142d40d00700101c042d521f03003070398042150f11030000d0441035214036005612460b00900007070644140284450401c5201c03007120700980c0702ca40868041d25001d0343e01165035117000c500c0e02e01038410881000071000000451410804040d809180914030171101041142d0365001046c12500683d811024180c1100e6100d035401d201990002c2c00b00d6031000f035905101c02514000f000803400c0d402101c622001c0004d841c5000789828484d10014250b040e40400400e41000c51400c41e0034102c0f0014594034034000784580c4e40107030b9600e41c210400341070700e580c000d650307142c0112001001004194090107122071001041c001400001d4031100c103a5101c100d481d20340f406410205071024a09410f041c402e4281c004540c46107280a841e0185 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 68331720 1250 68330470 68330491
    0xc030609140d170a050f0103110f060d091a09100207210306080c030a0804030809010516060e1c0206130327081c120218130c02011103011a0705070905 66
    0xfa40c0324088421410320042c0941c040901d440b00f0400980c00c4000e80302c2c1560742103500600f030110280e01080380f04420402c500d6001002045c022017622140c0c2110b110ba500c1010003004060b00e8035550400100d0a1b24074090230f030003a821070002c0c825280c2c094411741c0d003d04000002003040c001c07420044440c0d020180002170321424140903580c41000900321004007034000340840c203042d07160a591030040d80402000c2e5000000c405a41d68407440545400006c00403d400203400c00303252400040c002d42035910128003c1501c0c0784903116804d003d00c030001100360058102603039280302d01d02802c48004811028446040c011800c0b1040301446c1c900c7c0c0d0f0503082c88107050305051802040c500b180603c140c44030342401a207069051070340301041e2000005040000760722143c4002c0d200340c0030400c0440907500501e1540711b14000c01642d8000d01901071250f00200900c4c0d0f00d40304001e00520007400b515000004990341089640380481c010407038940960165440703503448101c0f01c4140d074829202200b03030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 68332970 1250 68331720 68331737
    0x6300109091103070f052101110703020d0e1507030306150e030c03072d05040f0606080604050402060405061e0316090807030302070e040203011b120b0402070c030609140d 75
    0x1c000c10702a01c1404650200c005000f25817a24040452041d894052a805000d5800c001c018a1310450003210001098000900110034998030300d0106400019055005114440e0900055806160080001310018018005211400003112203d030b2054408034101545c070240041c00510320450741850007030035035a8104400194042500e001028044180300e500805801c0240391304c8680c0342d03010003c0041c0507405040c41e040c600d0f0006a266846590402d00f4903841c044000380c2c1fa4030003410b0754180e40310040c00d03480361820300048510840d0000d4010104100510052a046010f0092131480a0001582185651a005280d04240d40d40310809400ca0000091035070042c1032a400f0b44038040081070000e00c1e41d24002e54800b458410083c40402800226040d0345080d0000c031820000350242945142d081c03c001020407120880072078605103404d00e940301c2c524050080301e21032a0402490f43c10b003411919900010846820220380f2210325a80804a100c402d01c1002480307882500c4e240300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 68334220 1250 68332970 68332973
    0xe030c010c050c010f020f070210021504030206040317040c06050c0102090d05060402010818070e06060705030a0f0807020703030806090601170a05161115100f0902040503010e0105060630010909 85
    0x2d584185d10740507951401880190408000c2c501500c1d0340c10340407115a032000380100c1c0d040c0d081c5440c441c9544041f0300c02c0d0b401c0009050b000a0114040e0780b20756105513502c146249031401000c4251802402c03541c000b4000c1200d548618040c2c90400d22603800107180070b40200c00101c010300f12039022030700760708400204410340da008080203034042c0c2088403c01c0b441c2e808804140c1c940c2030300e0044e0030340c007084400803c1d82501d406055034581c0d40d104d8200d80d500da150200c00303800c100c1482e80c2c000c00642d040c80081e01385440441c110084a07415122440c4d25117a43c4108000902c00030091410404900c01840510908000e82030042055110004041c14640c0050301c40150400c080024801c1c6d50782080c0c020310000030b00d002100d0084810606a40782c80182c0508148158411190b24107020f5001c50801030356401002190001c6008010000c4040f0449090707030700480b0265800034090015107441aa4000e00f411640c244507100b8070048081e85104041400030307001070000540d42c800040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 68335470 1250 68334220 68334223
    0x7030e0c030a0c140609060403080c0118030509030c100f05032215050a0902060a0804020103090206031503071505040611031e030f0907270221040b0c120a0e030c010c050c 75
    0x6161300307840e2a858501a02c0105100c0d00c80d03884000c0120600241400e150b003804e503c020041341d140000320900030082c3c18010110382203541c41900c00c0c01240c540401500e095240b1104481d03150b00d810540c40038002003603a50f44c1000741a00d00420701011040c01d403062103112100118490680e02500c0d11760142c03100c003104e074014241d9500d1490b20a0000c0580c2d00c00e41510110300c00c1d46007004482d0369502c01240500030b110700080d0803500c044284609819820040240f440c0309604858100d582c03034104443c00c030040c01454001c80d50030007050125511503444107070b00c112500d003140d15180d49250b08507024451001000c4552002009200070011145401500300010000520f1765500300540c00003012888000340605248040c81d02810040d030783c042e9a80443c1d031089110300c8400181507003526100494003110b4034101900021488003084041d250f120244640950072a40c845071084001d000400b07007000c5c2d83c403081c40a803000e45000d0183e04002e0085540d159103c1c00b036603c10b00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 68336720 1250 68335470 68335499
    0x1205071a0403080f070203010f0608010b0f180112020a03120905040614030d030c090e090a03020f150606090d05010f1a010906020a0f08040503061806010f05010807030e0c030a0c 78
    0x1400010080004002240c8203d0a0703980c0c1440080c041543ca00b85480002e004007110219443c056003840b6000031505410340c04003400740019107074441c0c0318400c2010440301c860030700c440c90341c2011440d00500c00c000320154604036080c03010b0301c013585c030f1612503c0d440160a0014264400501d0120060066081c01c0c01420010b04040403101c40d040301000000b500c80b28050403c004056691047c20781c0548900c060000410b4044211445802d221034066203507043c0340c1c403c1d8094420409268401d1034000707004e2a0417540e10000d0001916150100314890380071140d580c1e072141c05403943d5000b042c000e1007400c00b40901e1142c0010107c2c0c1c450310219403440e4108a090521660301c2c41080300316000b0501d4008254481d60200314402c4c0781c54150120302a61700141e406200701d00807c444c60307841035401c08103800c0141c01c960072a030362000266015180c5005c0c05001070320000100b00203178025082a031041c440041511030840041c808686002e8012400f1354108802c0c0ca0304100e00303414050710 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 68337970 1250 68336720 68336759
    0x509010207050f01230c0a08091e07090b0a03150504050c1c020f0a080c060d090605010303020a140a110f0a09180209010e13141204030c090f050105030606010e0109120507 75
    0x24000fa446c1001c2038501c207000e0030001c501404081800903041030804d010305640e4110684149403011160140d45680d500140038030011589171802d804140d2421803a600200c03a400007200c40b90800c0b000940001d000080c200312181c5c843c008022006a6550019049001d01404414014407450041200c4540f1070300849010f00b0035030009101e01c800114080b00e000344141c03052540c840344411a44010413803508044c01441c980000402016400f00d2802c1d1224043d000c1c08204011040c205521071000c20001000d098170020703000c8844c1411820310204070707001440800115646c007400815a01d1024171401055104154102180f4120000c0c601410703d69000030031030320305401d40e041c840000150140c00e80070700d03070030862008100b0060440c940c20241c3c0410f41b01d44ea289441e20100c8140d001e4001c00e54102055003105814a1040c14100d41700100205400e0700c1e04801515070103070001301d0504204c1441d8001c00c1107071403003079080303031540c0b00c0c00082036002c0c036149070750b8062014600d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 68339220 1250 68337970 68338031
    0x507030c0311090409080c030f03010810140a050601051b0706020f0115060c08130905070e0616031209170702010e0a140402030a0f0f0c09060e01120509010207050f01 73
    0x240100702c451841030f0340942400780e130300040310803030341c20485600c0c00380a0440240d0303c00000d1403040c51001d100030358121203401081b00c0680024070700380c1c0c00303031510f40e920030442c40403c40000b010810305400c029080041070402c00e182410800119001c078078011415202c41e40130800400c00c1c41c0d410418107064064001c001c000c82c1c07544181c02c114801040c8100000c105a41e44080c041c440486c2c100c40d100842c0300c41e12124540d4075a070305000b6040031203001011800c00c030b9203600c140c00d05108590b080c010004070302c10310040030b6034140c1c0c10303030243c001408e82603070340341111000a491450316040b080b007480d14a54644504d44001000e4030844500710380203014109040101c1d600b80300340a404d40408580150310380da01d2180c00c03401800120071454003581030101071201c1301000d5201503c4070340039643d40d0700199101d080a64120303901e40c0d400c80c0011070045d18100d039a4000e0b40900d400601040001d03144c0020354a803186403850945030160b0356552244a4405001c002441b181030030295034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 68340470 1250 68339220 68339231
    0x60f0504110111070506070302010b090702070f1208160302070f060e0f101b030309171c06061418150c070501090b0304081b03031303030b030109050a0201050a0201020405040204090507030c03 84
    0x52a165003145c41214000c220101d40242014001e40042c105140040c042c1c43c0c03d8685041700a40e0f9880e584900c094038191000040303100003514031440c5045402c002903900e40000075580503021001007501790214002c100000c0340958062007074100900c06561259040c0d41d0501c00c000c0091403a1050380d10a580d2082c6640685410104054403070424501c1810038030620b0409401800083d040140200d041144441065038500007400d0029445c0c401d15080700743c41000041125440c2c02a08041004600350243c00002680140482150401505580302c0c040c004240540300303203200e00041d000d0110300348520031820056000200000d10300800c0307851134901030f20f281e0320020740040d0500d840041d00145240021094840f02610b000c02c1303c0d50380c079200c0d00004500031204401c4002908108011b500e82c13030140a001016604000074000c242c0b5143e00644183d4421415101595028840000c0d950b031148041c0c40100709015002c2064544000000c040760b0850441034117052911 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 68341720 1250 68340470 68340497
    0xa0f0305060a030c12081c0203091c080606090a0b0c06040521030f130c030308150306060609270103030306090c02011503060506180901020421051b0a03060f05041101 73
    0x2a850b844c100d4075040440d100c1500315003010019445003801c641045100151090100e0300142d0046d44030b000c00000303913494020724407020900c015010507c0000101c521000c14102c1c50000d00a00e80f24100030310384000e481e511804014960402d20380714011ba0002c404000c148102441042144064800701c8000503005108510190102070f088130301c00c0300b402e0005030442c04010b811850403038200c0001502c280d600d1400030100301c03046800d50500e8242c03240d4280e0300d0800054807030107040001c00c1c4500f030043c20b60900036817080c1000880401c00102c01156540c0443c01c146074081d600a0b41c0104425040583c1003060726030725405031045a05d8148003104800400040e501600d0b8080ca020903540c5800b0001440d140c05881040510f140f1070b01401482201540100100d0341084042000880e601d40b400b10211010400542182c11009040c03603806859503492414640c0107154040d06a00e0b45c0b01c400449d04512904040b060340c403824401400080304010001340c1e02480c0c2000c005800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 68342970 1250 68341720 68341733
    0xb010509070804080301060e0a0b0c0703030e0402070c05040504060204210203150c030712020f040f0e1008060f100f08010903030e031c0509010902040207300509010807140a0f0305060a03 82
    0x5110348003c1010201c6d4008c1036540e01d003c02c90080c010b0f20004c03919180b44850450301c0701424841180440d191100702003090406009640115800004011895280c0003d22000d000010011242d85508000204440100d219121008103100007090031702c80b0030b841494600080b0407000706000c0b02c05010003181c2800e0f4030880341e001481d0b103010000001d00241250181c00f9540e201c1c0000a00410045840400000c207081219103400c155940340e03e41400c0400040c600b8080c1a107243c100c1c10021707100044428459400203010312506400903520b0702c600c4664411070b080a0320030b94450301d41c00c092507418006d0291400d40c080c05103240c00c4000c00741c1803407041d802d0307405080c45071075500103808040e0a5101203140754001d0015503540b491440c00c15135040006d515204131050300f41d0714400302003210b0b164031643c0000e9150075140a4000300107441ca010300800c000100810010940038000d10312014104108035074442031103006001e10041c0c1694001480341d0300409107400b0400100700c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 68344220 1250 68342970 68342977
    0x120a060e0c0a270302060c0f01020408030c150c03040206030c090406091d07051021051806070806090c071103010c020d02070506070c090c1b030e0f04180602030618040b01050907080408 81
    0x904030346d20740d0740b0008500d125042583e801c056030140d520228001030400804001803041c0941c41c405c0e9007502004114150800d28280c03075045c0304217400d000150050500d840259088400004074500300600f600009068a60581002603041d454140c0c1d000a598580080008003001d040030300039079400c010201d401d01240f88540790400c4022040142ca60044100920784000d884200340900c0c9080c540e10f18074003004000d403034154070031500050034503485500260b0203090020a1200c0903124000c15040710f030480c540580b482c0c01d500031296069903092003020302407501c68016040c405041c40c4041c3c100840d6900081c021310341017000d0000500036151800548622319030001d001e071010041150110f4004030030110010418081405040d0808a0002401412a1510102d06001041c802620b210f1004070151b00440c5020100296050300a103610003000f030001c150259240a400c0c800c09015034080d00d00c40785400040c80982001100c0982c003404c41d0601410900703080c0d4900e180c03480f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 68345326 1106 68344220 68344223
    0x25180f030807031103030f0415020c1506091605070204020a020f0709090b07030204080c0904110d0609110102030a08040303050603070b18040e070803120a060e0c0a2703 74
    0x3940082142d202d040d044513100c40c02d4480d6510b121a903284949e40072516a0280204500710380200444000c40c049000729107903e0030510184007840740050400000c8846030280ba401c1c542d0040100c0e800c2c25030544005944a1220108a0401c4512100c1c88014024400300041700281c030f4103c0b80029008420101c503507204d503203055040b48030310720954049410100c1c3c075040720324059a03072551150003102d98918410503100090032104012808450960740c40a07040d00344404c9858044804600f80007c518043c90b03188050b005400042c401810561500001803c3d500e081c80301800402d600c07160039403200c00d0344442d50046801400140d010b1440c0030819140001c000170b02c82e0441d144140074528000c2d2080c03c03840c50720002018908182c2d00c54a001642d0601c0741c3d031062013012004071315030f282c1d01c815500511440000b00c092000441c4090840240d000c03100004040340e = true := by decide +kernel

theorem cover : BRFrame.Cov 68165470 68345326 := by
  have h0 := BRFrame.cov_init 68165470
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68165470 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 68165470 ≤ n) (h2 : n < 68345326) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
