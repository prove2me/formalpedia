-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0032
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:27:15.946006+00:00
-- url     : https://prove2.me/submissions/54df4b49-4853-4360-9130-33ecf60ee1f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 5575547 ≤ n < 5755403 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 5576797 1250 5575547 5575553
    0x203100519030302071e031202031c06030506070f08012603030108030306031009020d06020a0c05010e01021e041a1309050a020318010506090a0209040e03030c0c07060215060904060204050904 84
    0x184941c142d038400d4084901040d21031642e00703905280e100c4492074040c9018001d000190401d88508070380d211a0045a051a41c0c449444841d0f40d54102200351441c5e864004005003d8200413154114126080c1491003110f0448000d1080c041401660a44001d0f074801c2540c01204641c4810010b141c84260307620381d41c4030054070b82c0700d0348181c94041c424440ca203000100d80c081441401c00300c40d40102012020001b0780e46400c0a90007180e0a031050091808a27103000c40c3c3d007801180c0b00d80c0c4002000594503034201000c5100060800c0a200f40480d050005110883d280e0b0100c908031508a4503858465880c4034100c0030410a5800500625040c102030146242c0a60061805401d584007a09100c80d0181c800f6800c958045420a5100900401143d42e1060b154000d02d0a09170160000c20012407074040603185078026901240030007800140115005400e0004002511032440030f00080c030100081118212030107081c00d48a04e449a020030104401da9045400070000034002c4159031600342 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 5578047 1250 5576797 5576839
    0x3040c0306110307093606030302010c0e0a0902090f030f0a02090c1801030b0102120406180509010b0d05070513080309010315210203070504090c080c0a030209070302031005 76
    0x320044800604019403108402250015a0320500440d80c1c2d42080c1d928040c1c483c4220300c81128243c521020440b042d02c04560621031101003101e1140011503151329601d402401c4071380b034a0203801000075541c000780040d603510003844201ca07800500075840e0b008000000381c1c51700012403841d40c94400d003103010a240c038007c5041110a402100c24400d280e49800058186100740090401e600c0c0320500080e0166010b540040d070a544184122250080e004450040d00e0380a60812404644003900a28062a0591101c1c001c1c01c2c05407400c1c00d01d9494459402481d004200114003019100d070300192140784503d007540e07445003d40c00c040e000903540b000c0c015100c0e80030980036400241000c01c8425000355043c40c0c802203980c9410390a941180c5503116402d6915001000c9034140030b084400030b500d035228001d1514040c000d0b40c0a100b0a403801ea0b117140f030844600101c1d40602c948440c1000903030703144405c49238031103080e00b00582c0ea40e0307541d0f1088a500c9c3e1580c01032a48902c081c003603405412510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 5579297 1250 5578047 5578049
    0x90402190905030111030f04050a080301140901080a080f160605190506010809190302121b0d0306030c060c020d1410060504110915040e07121406010c06050702030c0303040c 76
    0x180c407211a000d44071014903099540d242d40d00a01c840082000c503202d0b01140c404140e125006100382c2700140800d94850007194000c0c2c3c069080c0c0b603220b070020061031030408d46882c01440401c00400c50404175030746801060065903184a25000041485130403518058045188282d200b0010049444e00a010804940302040c21041042ca004000380203540aa171510b8081e541144c0244000303149450003c24a58042d04114114028103003802d40440468002d4001c1020080d00080c00e90b0f4001000c914100784034414134105030034401c1c1000840d4150801205075030366444d0183c2d90026074004640d400700044030051090500344200780c52910080380c079a0126024010511003280c0d100108015241c201d0020b06016004003d001224940900c10000c0c0c000c15021050031319079103500804004800312210300100d070700e05a4055600c0c40c42c1c81020302a00000c1e580e11201e0030a207000910019148500405050b52480401c00d018001c10070390303400300302c140200c0b40d032480c051a20325200d07040d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 5580547 1250 5579297 5579347
    0xa030306030b0a020c070b180405090601030201021204030b010501050a17090a03080a06030203060a0902030109050a0302060901060608010b0901030f0608010c03020c060f010303080403050d06030206040b0a0f080106020705090a02090402 103
    0x8440100e10340f0045030003140c03100340910004000c40340c102002800d0304d07406004542c2c40344103c01e141d0045034a90f030140c03a10525000001d00304961450001904000d01014a0003039120f04220034000508055030b10740c1518800c0c60115210881c5070360030b403603603121403500b0b2000c0c1081004004c2d44a000180c02d000b69803090f51259002d03203070132100314213456103400004c2d89a004103000502100f06035020700703c501d0006001159040141e00d880e800c2c45225a01500142c10441c00c2228a400c24003a0400416280c500300411390700d481d14404640c051600d61504054444810091214040e0800030103005c01500030000d0071500d540280095114034201c0e20341e030083c10000b4115121000c0d805040320f0701074032440040d6486a0b81258140c9c00810845c000c0c554070a000710242c3c1f1020060000b07000020340e282d40d510b09042d8090080030b0a80d07c1c1c0b0040003071150062111070741c045548000c55078250780c2c400c516102c620315000a4090005429040361020a0309110301c240140c040035800b034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 5581797 1250 5580547 5580563
    0x10b01180506040303080a060e0702070305061302010813020a0306021603020708060103030c02190f06080a050f0402130c03110d0b0117010501050304080304030c15020306011403160509060c0a03030603 88
    0x40110103240c034000c841c0c401c96078001024481080881c1c0581c1035160b100c0181c080025065485e5940790445c5407054442000503400060b051040080c2080003d0b085400b0181421588c081580020041c8030700400e04c001c0343c00510382c0c100840d102d100a00380070310740c8450103544170301c8402060080c1601800e0103500605c140e86000449100200b40181600e401d030780d80b915043e0703664084c0109110380d00c03003141801c54446c600150101105020341c01900e4559202ea6050500000800c1074a1004c0c0581111410303010903c0010707501c1da400b18510700c40e081400700d84409000030542c003c0c04040f40b40d43d2072681c00034140c0820f450b640d0180e00403aa003603e8900e1865498552006406400d005041c0820020030106010561100155920338800d1070712505140301c0e0baa82005001c502151702c1102500030040c400c1a607000322207800b41c00003225085045190031101840e450410511900c2404000180401251900d1046030303080174400303007200d80b000ca0074030b0002c1c010b00d014801038034650 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 5583047 1250 5581797 5581817
    0x706081b03040506010e06060706020d0603030e030d020d03110706060b0d0e0304141302070501090f0b06040216061a060307080a0b010f020d030c0306051c050105011202030d140d0905010b01 83
    0x10400d0080e240a6500030300104a180e0a21300c0c401c60304000641003640c050303814840c400008101c2d0000b41045640c0e03000200c3c01a01d946805010540344a010702e01c41e40040490b00f03616030780021000e80007401490041103140c503c2c155402240b00d4040090030003418524045800314000c0000c008021b015201040301d040b101c412b040c3c80340580d0150340900880c501d6030ba09145031904041c0300c00d100b0240018a4002c403590f4150071038401036022a103403048402441c0c18007900d4a0340541c405803c1d1010743c40d000c807a0121841c0c001c9a1080201415502d003400d107402840442c40c1d0728984400341103a42c2e2800c20b488081c04500c2c04a4600304e03100d0810010300b0895102e520002c002d06050340080280c01041b0300140c000e0003224803001c01301592510300140e19071325841c00540307115081c0b4403850b111465041c25825200c05810052240010207201801170320f0000d801d80340b0858502e4608040341820080c4026882403041104c4403504140c5035030180a0107500ca20f0511900342c0b510a600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 5584297 1250 5583047 5583091
    0x20702100203040303080103080f0409060e060f01030c050405091f0303020a060501050109060804060507030e010c03021209010b06070209100e040602040518090304060f020109020a0f05012604020105070f0203070608 94
    0x1074403c0b0b0100500160440740101300003180803001d41303154041d4142d002d0500752030f0282e0f241141d000e544808500151103040c02054144604504240741080c03800380310040c09014003801d584580e00c80e581c007809000d400100c3d850003003441100346107180c0c21000e0600340e6a050096540a401030103503a01c40c43d010000440758020315200d01115407940700c10850ba65151994002040014600750504d078403091001060300c0300b0701c40c03020403015584005031141901c0c0d40720005850300606580a580c903086400142d5074401060390300076a81181c40000d1a5501c60081c40b1881c59035010400d00c8002c0010302c800c009113500500291007050b03d10000003c4203169481e0500c2054842c481300d50800c10060003e18854440060181c1d610b000109101c40160301081c02454030354450485540b41450510031580d10503400203214905140d40319506c607801c08246281c4002910080c180900006c141c0104042e003000d500f000c58004042d112201c1e5100800380c04600c0c12240440410141c0d14481c40c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 5585547 1250 5584297 5584303
    0x307050c010909090f06020c0a050a14070b0f03010902071407030606050405060607020f0603060f0a032001020604050706030c0e06030a050703050105030307030c0f050c0d0305090a0902120403080a0213090207021002 94
    0x844d03500b1030440511150961100c1000303500512080034640150481e20020890400100d4180c82c4118a9400740c0005c0e452101e05200e0603412150f0f01e200701704200351100c17102409813811341c0c1c2002d40042e038504251070800106440c0b1042800c0d1070140c01400020301003290b01c02002c403002550144400c3d1b46520402c450392040420081d8042e1140e49001c003181010f1018540c0702001400e0f4443c07000c4d1183c0010084034061b4012141c0401649003012001c4680f01f5650035094280010300300e42c00e1076641d590311840c560240c80100360340d598564281a1141d0410303500000042d12881c1d5a04200600202070501102c5031400f01e41400300003e02401e0000c2101d101d0f81d01541c0b00c00950050b070b600c81051500f00d01003511184240303c0e07100030650301c13030b85000c1402e0720a0b21600e90b20101c010501050b429503500c4603075203c0c03040c0410090710007141c004035840f60341464940141d81d25082c405000340a8919844844908250b001c144c9001684c0140040c43c022144100001610302d001c0740c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 5586797 1250 5585547 5585561
    0x2030303070804020301060513150906060207290c0c030708030319020c0102090301021306170f0a050603070305010608030403110604050607231504031205010b16050a050307050c010909 81
    0x5016401000003a4141e0300ca64405900035200500111f205907940000418080080e1034018003150307070f07035056500040245030480040807a4038060000074030b07050003c6c0d144c2c05a4410810040840c1182d0000044161218800d00100c40280760b1036a60112685a0300c0380003600e280c1c0a40704106c4013140c0c012000087d01d100300001c070005200140a1644c0c14040d42090348500c0080d9000e00040341655800c0c0060a083c040b04d813900203070f545c070341f02c001003041404075030301686601c051052011600c8030356140344d40001b0038440440ca030746803400401d250442c03e50010f0000d518000b40414000c002000800407039000d45405d45188244004210143c0b11314459168040401c20440b80003a080142080c120304040c00c600136113101080c2d4990800c0d0201252090b03c0403804100010542c00940e00c4520303441a41e010840c035810001c0131a0f1901c84e03800441102d61005040c0c0e42000400c10a0000c070340d50120070b0700c2d107800203450015038804204101e180070480c003960100d2681c181e481011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 5588047 1250 5586797 5586799
    0x405010e07180e0109020d080909010f060507060902120f030406020c150702010309080706020304050304050a060302090102060403030b150d0b01080619050103050c04051009032306040803091e01020309160302 91
    0x9001c101c80d000b01402440c0c00103078041555201c138000c80250395403641e52040c290065455075a98610501045450310050308109140c110402c000d121081c1d00c10150cc2c0080e601840021303001000d80001940840e08103000b16a502c07482c00c0c400403d501c040b01030710840d01c41303400301d85a42d4200810070503c0340b402c4c80b0010320303442c0a000e040f0166200384c20022115002c0c04006180030399a031502c2c0c00b41e0303104803010f03a00f952000604000b03505007001860007d10051030110b050500c0031000039103601010f04003508042d22034061042d5a65200085c0b160406456000b9981d07400c2c0c0b9900c0c4003c1c00641801a0206e0f4042c1c001403c05d082018a0041916040705110340c0641414015002000050111000c60000380700215140e2614072101c118400240c540742c403420301e586005128401e486500715010703280303603160b0380360f441001a00c1c0350050360100c507503a201d50f90300c1d1500d481c100c1d83c021320503240d1421403a8420302520640c0298001c544d04015074600220356218012409410710000b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 5589297 1250 5588047 5588069
    0x11010f0c0609060b03030a050901020709023606130e0601021f020a180306050603010b060c0a06020d02160b0906010905040305040b0a030e0607260112020618030111030405010e07 78
    0x20030000780c00364003a02041d4030841c00003d165920300082072854101c0d8180c000032440001d41d4415035a01001818028000510150328216101c202080c0b800300076413624040c403010b1505070300015210a00e0300084680a0005a110740e510a1080c10044141c4a42804004c0c1c180100303c4651020440c203081d58540ea0f109070481e03040240410082d40400b90b4082002000300440311513400d99450325005500400d070202d2503080100c105806c541244102510410b010042282500c0700818010540354000d10700584980842c1030b50400b900c150010031101c081f10542c01001c02c004014014040c5081c04101c82d4181e0f200d401c0e00e41107801c20380c1c020b03011810a0004001c440c8003980181084030a07860301042c0244c0801080b868040240d4041010a0244180080d5240d04914a07581c604044990070f141e5450411107410700c4540c0364010b0302482000410851506045403503a9031140060000c002520034005010b140d90415142100c41d075003410b222486900002032f8040035a2f00a07420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 5590547 1250 5589297 5589317
    0x9020705030306060c0c030610080114090c010f021009060e06070201022104030512010609150207050603010504020703110a0b07030b01020c03120a090e0a0903030c170718031e11010f 80
    0x13084650f40013114140c0140c400d0550495441d02c0030301600b809000f18075500000b07141040052801d503a161000046620098010443e01c05400124622640001c0c03c05c03004240c1c490b00201d061401c1403800d480ea0506041e0138a040006952183c0c3c43e544103c016a28552100c00c0220300341e11a0b42c00e0422040e0303108000481c80b03d00e0020242e0014420705102d072078a0381083d0390394416a4240c0c40580030032903034802080b40e100b81c08800d0001c00054170103032942c1c5007003900240c2c1a000c103004050061764040340d50f00400d40100c481c6801810395000300c1d10440b1052070f24035649201201c5590000e030a0295001065000281c100442600203010302102c1034440d05298080d0060742d01c50302080b10b25200040d152504641481c0200d2040c140410101402c2c01c002d0b0965812122031000c101c94900d0680c0441c0c03050824580000c00ca1070b0030446030010288807212520185c1005d00745070317012151240180c08110054103003d119003c8203002820900066905044500c4940d021500101d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 5591797 1250 5590547 5590549
    0xd090306050601030e010c0e09091203010b0906160503070204060b030903031519060804021203030403051e070b01090b0405010504060b070204020d06030c0602060405060907060c020f030705151309020705030306 92
    0x502d60081c0c040c54001000d5212400090a6610920840c80403c0e0b1040341c0b001300342400b1130400c3d4004800c000a04082c10b45400c1500c99100501c2021a2903102107012007841d941c00084425a948000c1070340a0428641030641d1242d2012908910030381c542100019050056002e5a100c0c400f020b000e5400c40c0c3e60078415844071401e0b503608644c0144001203043e4a400c1c1c44c64400c000c0c040b10341d980429860030340b040c880000c105440b8200da5900620410001941c400101c610700e0021500841a402004030784005038040c1c0000200342030880e900108400b20564031054000c84116020b000c1c5990f9075041c04200c42e8240650443c942d410010000075003820b40040040e0051490009030440d40c0e81c9620800b01042c0c0c11010058000109000520100b045907035081694040504107240ca0303d440584003810351203009000d0002c800d08040d0642d42840660b0080c000540342780340707890303072a46480504d0340030bd130f000045030150000101c1c003141d447c825255000c3d03000c4021851625008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 5593047 1250 5591797 5591801
    0x315010207050a03020d020f09190b030a080301120302030904050703020c0118080409021c110703080c03060109060f110f0c03070801110a0e060c0709020d060602010b010210020307090e04080702010305090d090306 93
    0x1010598204005440d0120107803603070f081c9da51003881d46008500d408400403050b00240c4800111061107a13018040c054080341090046030b044504104281315404018a016425802003000b03143e449031078403040002040c2c041c0c00804400d41c00000030465240d61f4003d01d006000c4040700605088014082400b880300c90f940141015081031001d0400524424001002d40b484036038100001003001c00c0410405804c5008076400c110148102c0e400d44c43c010340002c0411045105550411841202030300103c0e010340700a565405916041e80c0c4000c403c1c101c030907500c1b100180d5890284c4141e00f000548810103210700340e0808540107943d0301e01081a10100c039460400c05143d0791000d0708020b07046035000700301311590062643d1200941c41c0c2c0b01c031105600444905601100a6906103611034006a90201301d8406500000800507100d442c1d40d9000c541508180e0000b9054090080602041c0a0074002500703501d072003640c0600c00c07a03480015003500e13004508c0d521008282d00c030406000054480d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 5594297 1250 5593047 5593069
    0x10911010f17090708010e070e10030b040b1806070201050121030206060909010608030409050402010e040b0105070b07090815040c0902040503060705071a01030b04050601050108010b0f0c0106050a08030315010207050a0302 97
    0x304880d13401c3d894000d039174210744c4003070681421780d4080e140c1048145084959140d10600711214030420902c1c603110003201e032000070070007050441d0b0000044d6480d921000041c1c0d503248400216045840c009101074004c01003030184403c11141724540d0300309074441070001c903541035040d130107013450340c07105001e001c2d00c070402510600c03072552608030200340130704100080c0c030043c215007601103a1800d180c00054108103403582d0b2a80560304102d07a0a17042c1c4d0b00601203820301540802120701d240d43e958002ca5920b20160030040560141c110800240103580407264003d90152282083d00741e43d90081404904c5148500b50701500480d001404880c0107802078048140651800b081d0001100b110082e0200b0980003291440c11120a11040c440e0400400380541428200102c455050404281150083c900700542100c1d00145031181034100b134112000900b006008950500e48a0745026225007048030000640c000801070b003401c0750320008030030b0300f15000540080d0720681140c090110100c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 5595547 1250 5594297 5594311
    0x607020705010e0a1a0406080108030403020a140f03030d020a08090d08010e09071d0106022a0d0206040302100c030809060601080402010309050c09070908010b0103200901090306020a02010911010f17 87
    0x1030040b00051080c104400c41052041501d08035a4035400d05a01a0a500d4107030442540c03540244330074401600e5072144682920520440901000c0c8020700142d81d030255a015150140408903981e2080c48035a0040d0405c0c845a440c6d14030259580e007000340d42c03642d01028990000e0103843c01000103245043c11030382c03c080340c06d00781d50740d403612144045a0700bc86410081c2c80000024010084607905206180c001003e00d400d201c205c040015100210700103a5118520801c0860300e0344003103565880c205c80c0159030280840300c4c0712040c56409014440b030b006094020800c041e00040440c0703000b00751a407007020161648101c0351034540045000701002c03002100c00340706095043c3e02c103986d20500203201d0200381da06e900640c0c0c01c106a950a492024003914141400c01c13000d5841d0200f48110043c03d4094200e1803a200d02694004884440095001812251000643c1d03e130440e27041d00028000c60048501003030040c0100c0c011034200400303070141c40010b080c13500d0045908200c0681c0c1900015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 5596797 1250 5595547 5595559
    0x519030506010210140402011b0308010501050c0114100f050306041a04030c0209040c06030c0504050604030f03020109080706090b07050a02061302040b0a08060405010b060901050f03090703061404140607020705010e 94
    0x4044d26404490041c120701d25696442c0d4100700c11580d1000c0c0c2c188038800d000a400c0440c94070760381c001c1c12168042c050941448404170744000c042c002544800050701c4a2031038483c80781003201d9220301c00c01060081c51307008400190007082030b050001c0d0f1300380500c1d4403081c6001c0001d0320400c40b43c0300340d0024104804020401c3c12560145c4d685500941c001c9004c0c00098000c14907201000c0c049541842c0d08000740101440108047d40d1188242c5017180e4011030301c010405100d1404078010441040000e20305c00001c180441030100340d030702c0821002d2141465200a49501c501a550b038010425544016070000000801e25018034071081d0031148060404a41050074000003000705000d134002c4038559207c8001c01c0140720007402100700b841e409036a00c41c60040f0381c1d80004c0083c881c8002c44d00f404940080401c03421901001964010350300140100030b030300500d141403241c8a400761000d440c00040c0700c20038842c1d180082030301801000d00e900140030b00782c540f40041d103045040300c42e0194440303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 5598047 1250 5596797 5596813
    0xe070302041706070806030601060f0c0507030605010803130506090a06050702040912050c01061703090603180102160614010608130606050411030105191503020c0c04090c060f05190305060102 84
    0x2d0003610000c0400d0702c550150180e0f140c4040d004002441c0140524840d600c810010411a40c224511a900314241d10700380b0720f42403460900390f01c0d04400c2d92009126511300b100005d0b845001001030610814070501c80c0c601c0d83d80d60740800c4014042c0510b240d611000340c1000b00314540c0200e00520b0040d00c041c0010513030700407a465281c00600c8400115000c2034000800354800b0f0028812440a0100109078146c07c0d1246d00c400c644c0c03406070044039401a03100202080c000311803110029808841d19000390350302d00c4110300b00811032203403a0302221158140304000035030806215545d8107940c010340d61040c0b1f83e44d503d4000d03031060107007090554005949901c045000d880340c0c0140154171403083c03002d035500d525180901c8500d5082003d0100e00e00800003003400a1048002020040c0c1a28600503071503540c1d15501a0400b070701c1c040e906510a00e01a060300801502500741000c81c0c07115114807102c0803a401e0140d6203232294444145282c180f1560301041d844c00303030b44890f400a4040c03041319800303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 5599297 1250 5598047 5598059
    0x1050121060e0604060506030408040b130806130b010b09090402010f050903060f0402030f0d0e0607020406050613030303110c0703080a0507020a090614040e0a03080603030d09060b030d0203090a0e07030204 90
    0x203035016009808030100100402103d400c01340140001000c064424901d5481d16450719210350050380280140003c0000e80078881003000345010b00072307203d44030035103107141060ad50f010740300042c41780f08454559600000045c042e00100648444000c0600340c940d05d5aa564011140240c00c41c01c5803080c000144010700e0305440c204000341c8101c10007441c0d000542000d0040518203a00604080700562042c000080b10651000c0356481020060f107250380c440031140300040280c02541c00c455007050010502a01d0107000c050598202c902035107007003040c01e05d10a04d8410030301c1150240c017501e9100600c1000068040b100911243c0c6062412508004141d8001480c016155100e0040c1507190541031251440106051081c000c1c101c4003082164890344c01c250315644007090141c14000781c81d0000e0401e031800d20403035240310002503040204281ca0300d4110000d20054480d58024810740343c08000a5000104990790b0f00401061251f03080d2900052079030555004214408054080c4800650 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 5600547 1250 5599297 5599301
    0xd02040602060a14040302100213050d0f02010909060501200708060903040602070b0405010e09040303060302091602070e010308040b030a0905030403080405010206071707030209060f0309010902010f021501050121 93
    0xa001540e01420050400203a2031096030f440060350410b450500c070174000000c0d000141d070b202c802d9070143c025850f81964142101e0b0b101c015442030b5003103484000404200a0b881c00d4900c2e09504c01d0301c07240080ca440c3e030301003012200140201c1d40071421080c00d0400000303002000c22118480b034400c559141e030321020501e080035400d03901c0402c598000320b011300ca866018040d85014002004000d4109494000000d240800342e032801401882c00790041000d0610a400c0380d4003035034011b001428582041e081c0c001c0c45514004040c0014007400c5400701d460b0310301c1c410140c100d070b0b00202440e0070281045c5100003594409800c414000d640c0c3c1450400156007032000e00010750064003510b0b202c1f0301e000c0019003072800c010310b00c40400045515540d42c1c810b101100e1508038103245001078880c0f0810000ca4503911480c0c0400c440c03090080104002a6015004194014400e03a01d103030750035684c0381050369150062550040c0c210002030050049511415a81d00c4280d909a554108140c0d005d01c0507003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 5601797 1250 5600547 5600549
    0x30207020d170301060f11030a050c010e0a21080402030c090915010303020303100605070c09020901120e01050105100c0b160c020d03030f0605010c031b0221030406031406010e150d0204 81
    0x482d02804801001003a030001c3d1200d210a03a00e04010100b0452909003503103e100d860440010320401041e42060240258403801011048904940c40460241080302030084a0b4030803842034070780e60780150102846610502e0081d5409002814240d084c041004400c00c00100344040341d00c980500d0040c12030101d581d050095010342c01442c4c1c0c81c2424952030860800580114003482420040d03000022020b82260007107944900300141c4610b0800b0041b0f0b05030102503400e00e4694102400c0340340d41d000c107510103030403201c0807603170750a00011001045e14002e1042e400a09102d1003280000d04040f5801c0911100c0c3c400d42c034245404c059246e00090f80085078540680c002980d5104a14502460344a88005030500342807181448000d13030360003440343c00414407000c55800d405c400c86085440d0703401d68449590b01c402910310002511050f160b560b811a00c110300c0003904020105141d20b0042a6107806650180e45051000301044240b0480511344003a07400c00020030869240e080c13000e440548 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 5603047 1250 5601797 5601833
    0x10e0a0e030403060c020c040911040f020d1a03010e01060b0d050403020705060706090b060303030108070303050913060e0405060c0f0909070c05010c020a02010210060e06120c03010507031d0a080901030207020d 92
    0x24001205d203400924000c201c4c0c1c0018081c0d0710f000301c10808200e90100490105004480100d2003030000b480e010081e01030025141182c605000340600c011500c00e24a8035040030a9000f00183c418024915003650661711508500781c900300040385c0703c42030503040300b94080d0003401122040ca40d40d101051a80d8041c42c000c0e03803c1aa01c52445003041034071059242c100100302e0007141103504145a8a40f1018035201c001c0c1807240c0080e00c20240c0d00c403413031003022a420040c0c04010180c1c0d0fa142802c0c00080441d002c40300c034000c030000555542200016908824480724800e41001031400034842e00c040082c100030207000480c022000056024050240940311643c0a00700a002038070019180c013a8010f48415860f0030000d0501c981e4013800c1a007540a8011204c035800b1b4400c517401d40e4184403040d8100c0381c05500304810026003030340580000500030400210384140d0216644030300e031a80c040c1e10000709886020090080250320940207040c5260004000c00030744541940c4034000714822020721 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 5604297 1250 5603047 5603051
    0x3060f2a040f0b0306040f0605030c0d0f0b01030803090f0304080312070c020d060b01030f1406040903050408060c0a0e0102030702010e0108100801021801030b1215190c0e040b0102070e010e0a0e03040306 89
    0x204650609000700547d142d18030034140321903400c1c640041c0c3c8404c0c50900d01c602902007807c00106100b140e0321807050040c1c2140d41010b00c1d585038100240386500072a0040420303c100e81c0e800e03200f040c3c000121001c0310103610255052886c200c50030b0041b050080d11907020401d4405401026035151307600c214a5620514000402200e64000981625030102500070340c21b1424020040240380d40d00115409802260001840c2c0320710320302a030b854045d5410a103020700c00c00c02000032100c00c5000500c2c0500700b64450460980d040c0e401260b132407040140c02400900d044000d010594080c2d00320580000045891482d041e40b0344008900f280c21080c40840c044c0c18220185045d96050321031400c103403109031004000400c18419040d603980c0c6441c000010041c0c40c0001075240d02d1142220161500a03402c14044540f046800600d020402c684952040307140080c4444603600001c2c0701030845080c0c04041109a1130b241c01b042414030f000703180d280c1161700c2c0e00070001c05d04070500046c00518070035500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 5605547 1250 5604297 5604301
    0x30303151e031b03020603060603040203120a0504030303180f1211010908120618040314090a0608040b07030e07060509120d05040f0e040b010308090f12030903060f2a040f0b03 77
    0x1040c2c40e4060f82140c0070030041c103000414000350311070f902181d038046000d8071055926162480840e103050400c08013480f11290201d40c0c0e41c42c1990060060040b07034020743c4c01f801320460700c1d9100d07890b4840003c0d0042c00d4041c03020b849c9000600c48110100141d0403400d00141c003103181c0c58040c0c00e640031400125041c00000034101e80c00500c0c0041c1d90340045003554003240001500b0400350301110c1c09400601400700c15000441c2d50035000701110404400038207401c1c1000d0340c80c2000b4040180c1a10111a007020000003d011544284203003106120b000c0020503000b03180000c1590b0942c4800701064200e0651003c8400b00722080060b03010001159036000c0d940c038030713280b40707880c400c1c8058200a81000d20001440301090516030381c1415030341c200c41142e96074850342d030000b402c5180c0d2142c842c6d00182d080035a819444404406001d0b50a02a01603941c141d0310b80042c0c1c14400801c4401c4869a0440c90020f85444d041032400184a581000090301d416101c6041c8948910307079902c886044000001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 5606797 1250 5605547 5605553
    0x304080d0201060f050d080d1e0906050a0903020705100c06050709050a0803040302030a0b07032301050312090a031205070b0a15050607020907030b040609060803030405070e0106050301030303151e03 87
    0x1180c100180113141e10504240c0c1880001000b04d0600c00c3e02429100c804640c907030b0000555406043d00464580740410f035011049202809400d5080090740c6443c41c15000820705803007409449005070b45a0701030100e0a0500c0c0400859001c0203456504000d400d802000001c0e1641c402d081c040c801680b103110840b454807040284003c040e03040136101c2d80040c0010001600c002451000c180e42c0704602c2c0d40d140d5140b51046000b080040c41d09450340011614481001d0b240340f440078162a429406e03100405044902d101c840e05c03440e10910b0f042042081704001044012a071114166014600645480c0b030319107a4100b407038425a04001016540d019a00b5030707803005c04c03d000061006940840c1040d9040e0009104440000c104d50145a114a241c00382640e451748014050080303c00200f00141d10b0b01d828076030302e800071241201e013486000c1000c2290a0790501c0141214226030300d5603d940e0a55600314040c0a54100174908041d040710041503003003030445071b00c1c1903000c0c2a19120384645981 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 5608047 1250 5606797 5606801
    0x10f140601020a030210051909060506030706180e070201090203060f01050108060901030503030a050c0c0304080307020f030105010509130f02040507020307030906030b0109060309080c060708041101081501030e0f0304080d0201 99
    0x5440c45056500c40ca21040c000b80e0040760040403103248070f000003616560310300c0c0842c2e001c10009480d010646801444002c0120582c40300c1c1c000e140035000c440006442c1c40c07064801c0200032056545662901d04100904010740168603400744d00c0348004140703c40982e000c2458848142c55007801c001c502001031090356881046260701550482e0340c480c0c07952468840700c0c2c80384005002c58210b039449100140419282604480c004a1041d041701e950b81d581d140815101e07044110120311400840600c0c00c5540740500825041c0e61000304400e43c2611014036074441d1902040c01255500d10520270390015903100e1082c54841c90058000e150703200500d19005180602d1030b0420001e051509a40641c140d9200e12070505460b401d00700003410031000d003095042809401d002c0942072040b03001f00141c150380040020b020b82c2c450300b458032070140700c071006556211048580311400800f4a14540c840c0d0701c00e070000700c076611000065a069450b480140d6085511507081548035601c2880c014003195424 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 5609297 1250 5608047 5608051
    0x30a0e01050c07060e0a1401060602010e0304082a090a0905010b030106030c170708010203070201090201120b060306040209060904050c0c0709150312050d0203070f0908030a090b0309010608010f14 86
    0x600802191a06098407981401034110152035942d8519840c11150410044c8201c031940020b42440450f8120007d640a46030314041c010040d401c044001c4450b25000059030159440940540b81301c4c291768001c0c5092060240780103101144007841c0044545030041b07803a0040861140c041103410003414810f0940341c5481d803403806685410301c10404102012542810340301c84800002c4400060030585150000d0f680052921754800801d20000c3c03901540b086e81168801c1c0c0340d01c800103161100382d50031519804d81c600d800c0031003080014454500b65000b0000d06a0040055092010200104044403412203030f40c0e103490340000302400103070780420442c4020803010f1820f1108107505c66114001410a12000780804411036038030035004d001d00d085e0b4250a00030301d4219224031b4034100c02440c4544090980300031440007040414107080100840709120f6040e2540b401440c94101000c03071986c0000d007180c0b0155658100460f010300c0c28054528159084140800c0c42041200034010308480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 5610547 1250 5609297 5609321
    0x70303050f100302010e0102010902030709060e011712160b04030201090605060409030504140307030f120306060503160e0102030903030703080a0b030f0a03050703141c050a05011406030406020409060803030a 91
    0x5078200103035208021a49025264280381241c80b030020040184d0142c020264025498091240041411409540090100d8400b10218034031a40c7e100b4040c03160308140d11180019402001d5151000c12042c8000c2c10740f200101c24420303072410507441e40700c0d4001c0191400c6006135140d0600c401400700c0d0f8000c1c203800c01800c8a0810000c1c0030743d07034003070080e101d188a1301c8a128140442020759550078807a2800541c1c0145c00e02c45d0000441c541190f43c40d0020210340c011a16144000c601d0500c5841602e10034412440011150b20045405441114500000d0f40c1103200811a240241d02c040c006440546e21a440c0c51050303081060040381951034003481175009501008505420200c0003507071002180d0075043c0590358a070365003070840c0c040000c0c0742100c5800400107001c8404000d09140081e03001d00706003042095403140900003068400a2082d840c03a6840000d000c0d0700b0789040c0c0700458009120b21030040c071b0f10350340f1a500c01c25101140c2c408c0070140c00110070886400710b61300414101045c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 5611797 1250 5610547 5610571
    0x301050903090d021306050603090a03080906060d110409080408030403050c040b06030f090f0106030b041b0605030703020d060509040c0e070507080415030207060e010c020d020703210c06020a02010207030305 91
    0x100440414068281d100003c0d200d45e801e084419421070142c0d00079405402d01500c825528030b40071440070b80c1d0b088a12070441c0015a0100010300343c85000c1802801228001d1000d03018800540b0740c6013218407170904960b4003a60b1019900c001500c2b080040004040d044043c5403142c0c51824800c1c01c0803603800c03205000f1410441899910766644040301d42c8030001c031621000d0f40c2c40e1891007500d0b1002c07041c11012a5880c0201c08028003031807084042c4128440e0f0f010f000c4150700d4072030a80744096940326200100302c003030001c994014001c0d0040d1a001912040c0020b10700c1d034540004241c40025541036900c1d0181d00014040d080070b00caa0154005031a00b0213600e442d801e540c45500314411803040390521240da1070020f0700745200b601110300090704100c0c00c0c0321420181d50301c0ca00034038041410300c0140c89038241c68440c0e14008a00102203075000070310150503900796201c902100843e441e0500030011000440400200d961000d0118101140d00040c2c40d68241e1402408580c4080c04a01903d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 5613047 1250 5611797 5611807
    0x1a010207051816021002070308010f09020a090303031a0405040c170d0909020906090603040303050f0703090807060c090e0103060203090706080411010e0301020d020f071110080f07020a140102090301050903 90
    0x2420700100140c000703800f000404034044068004a04003aa20225103481074000030341441450b0b8400f680b107058034907803001c2c2c40d001c030383e600c1c0b91404910aa098410105012080130004a80079900490b4641c00c00c4528001000fa540d00042c11070b20200c404507035540907100c041c04000d0608440c0000324800c080141450a00003030050306c0301d01c0070310036200081e40002b6813904030b88408080e913a04820280a541c0c507824640b44c05005008103c80740d86009036580300203045148031340560b031125900024032500d0201d9039140d81010386a156291418001001400903c0070010290b0f1030083d401003100588a0500e42605820b101d101d074406010840c8510a000108400c0208001078840900b005400703500c5e2000403a000e405040205244548003281e9205150304032001401c04520404156150040d00320403c500c0c1c81ea41c1c0c00d1000042d160100150081502502c802d800141078012990401d4165071048200f54146030240c1c041c0c0d401241306211800c0c01d00030b0b9500003a191028500345 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 5614297 1250 5613047 5613079
    0x10203030112120c0b150102010b090c040303030203041a0c0c07060806010906030911060a020c0103060504050c0f07060b03010504060207110f0102030d0c1e050406020d0e1518041a01020705 83
    0x10b60a80d000d030540800700961568540600b030000d0103a54001110f07000d6142c500300010610751615000d6005d9401e020914260740307880c610b070341e106e1041c2005c0c2c1420b0a0030341d10120025000240203e841291030102c44d00f01c41741c2401c00d14412507078107801542d40d085400e145c1d4104901544450184002d10b010f1110681e0040ba440098a58038a00010300e000d840c1000c001c80000c0ba10381a401100000c0c409100c0d80e8041100001c105080e00c06000155845050100311b500440d0340026071881444882d5082851400a0030b04502495010841e95174460000742160b4040d202120000c2d0300040c0102004480700d400c034610801250a00c540124076000030303489204028005c8002c40c0d80d0148910000e014010b1500e1191181c1c206419081c025500604242d0141c051480035104040758012101c1c40381402c16022800500340501c0d1240b9001c283c0d0345900b080a66020f440e0f1400d515010544591003072514030b00c01c0f803100000d92004030001900302059034000741c0c000d6101111714954 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 5615547 1250 5614297 5614319
    0x60106080903090a0b0406030c021203040f0f05011404060605060702090c030a09080c0303090f030c03040e04150515041a0105070b04081e04050f010c1e02060d23060102030301 77
    0x1114514106980e1a9807100c000e00c0c207500c14684615031100018002269a00f1280d0182c0143e030b074561010021000814026680c038400b4210b480884c000420001380010210451010070501c122031071a03650050390369172401c0d5441c208805050403943d90800003841003600600005200c140d940e68680040d41e00821007400c001401d0620424000010a007910083d03401504016040b02210380c071540b02d07440d059200c0d442036400103424452200f14158684000c02140c04001284c4000d51915241000121070b40740020b00a4941514065144401c12494001c0c24030608d05000a020140c091804120440b11603103a010900422101a03207091b90704a41161040c5030803e0480c071890741c1d00e1800300141e11940621504c5001c1013203030a0740140d55034002d0300c01d651084a0810800203800e004492801310040f018110307800450380c8440c0b6101001030411000d00142902e807410360001a84000d440340a882030414852590b810268881c2c0440080d8120200348007a620395450a150420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 5616797 1250 5615547 5615549
    0x7060c031d060c07060e040608070e04030f0228020a060201020a09030206070c050d0302030309060903030601080a0e0109082704110406050c030d050a05090f06070f03020703020705030708010501050a0b04080601 92
    0x500c4070355000401501d41d1080c0988031002c41d21022201202d0b21101c00404680520303051074003407401c0101c0840d048101080c2d410980d1a4083c416540d80e4070b91301c003102ca800f10203207210154014001e01340e1a4168021514850801d00030170401462a90f20512002e01581d500040031a44103000c01c50780e8540c0b151002c000c03039070100c81144d11108641000500c0c00031550007940d00203105c10702801056004405144165054010340b8202c2e42c0700314490341c0300d10089643c103002030070b2403001418804542d40700c80305903401c810002480b80241d0b80c48034110762101c200c485201c0d410b01c5464640c0003030007a0340c0d58000d80c140d900384002c1d04044019440c42c004c500900703040c044c4c042100c10300603400700113960240d45002d0703043c003107800d040039050010801a14051654000c84841c100e5042c00041c07514000c010070355464940c080d840604030000e4110060032411030050f85800210380e6002c20015010741104000011079514040401084480c00d500408000205000c20000c04901003050bc1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 5618047 1250 5616797 5616827
    0x10b01051801090506030a0e0f03040501051207020f060708010f05030102040b07020105071e080d0614010807031805070810051303050d020702010309150608010c0c050a02060f0f0a0302070507060c03 87
    0x7820103188400681e0350036141e8000c290005000700422004900d2500060001c4d030702d41003694000e00b41d060360a0344910841c0200350110314100304005107040c101120f83d03881107462040c0e44424130319039280350900d6030940320180001d06001c014040e64041c401840c0013400218021454107240c980300d02e41d94040c2c003001a040c04070101c0c01806125022042502c024000d9062541c0c260b500e14048401d0342000c0c0c040003210385440d40201e00c1909044000101500c142c42c0c11020f90340e090021005011201220a00c4001e01500d00e000900e04201c0c03407020340012000f0388000303a0700b0151078007150001420700031588504020000481e80150464060280040e000360f0740d000300e40010703000b405510000030030500c0d510300e0300c0700407029592020056600d81d0000380503100d10201d080314038039540c00028007503800c0191100014a80311008240c8c6000d146511820900029030040a642040b15942c011a8000540034200442402440302400d0641040359502c41d058030000c03d0540b40720464 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 5619297 1250 5618047 5618077
    0xf0b0105120a060c030e0303040602070b06010c020f1002010e03120a0c08060901030b090705060415090f080312130b0708010303090501140306090a0615020307060e01020301080309190503010911010809010b0105 92
    0x5118a40705e0341208540300c042c00d0031a075803400e16281910082d40180d10984039983d00b08045802c66100d8542098441c0e0014601d80c501400324041001b407c43d00e1010405666035204202808981880900b081005888901350b42e0315000c94a58107881c4100000001c00c42e40b070b03041103429a14910700b1810350750410700f81e40b495a1103540241c6080b6280c0c100350703800000854000340c0c01003506016225000a6030f900d4415075a80c410040ea030703c109005821450b00140f12001e03000075007a10199000c2040fa0401440100780e484101c1c41610550b00b0728002582400103209154011700440b00605c2c00386410719122200703030101c115601000e00810712490550011038803e008a802c11740151440b04d0000c0b90014107400c0182d640d60015070111081824001000c210f10010b1007542e048070805400b4511f408015404c11207082a0030019820421054102098586003441140c85003407080c2e40c4480e0804500c0005801408001d1120400ea811f009410035280d901c5010f941c1c01d43c2040c224 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 5620547 1250 5619297 5619311
    0x2090d12020708070306060602010c0f0e0f061605010c170c0405100c0606090b010e030109050c040207021f030c1403150f030109080f09010905100203090105030c070b040f0b0105120a06 81
    0x1080b818141d60b50701010300e038416044084140021a031160044800540080000043c1500c01b40d03a440f107403038141c134003150a1844c4403207541002940e80c00d500380002d21151421107122590035203c82d031480d041e205d42c0e41d02d403280800d1507040460044142070010f90100d0510300648072034418412805038500130345030702a032165440d0040140c00344040c1e0140c003e00c00c030750301c501c0c881004000780c540060006400e900c100c441428184140e5800c0c03038206026101c134086041c180700103540b00c0c0e041245c20110b40c10b0100e0150403905611580f400407580c4c0030804c3e0700d5a4a00401408002c03100002d901000c10a010b40540107264850540105440c00015039240c5000680104000351014280d4000000e4a00c400d19000001700301c004002d0720f4508402c0e8a0702d0501c0080d41030807003294050b0340308100c40c1c1180c5d8019800703550701119404445241405aa0321101c4154050f642201c21922102c603074070070041c40081c030301d014110694030444400307031121105030345540950015100560b1111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 5621797 1250 5620547 5620583
    0xd080f07020f0402070b16111209012a0506010504020c03070201111c0801030b0709030b0c03040203071502100f0b01020d030203060301020c0a0308040b0a020f030103032106141302090d 81
    0x1c002002d03400c0104110f45407441420320a03290041160f80c140110f081038094806c050040e030400d0170521000d80180326061400850030166072110b5001d070b050140d0340024044005041e40503682c07200e41c44407111404e2801e854428139000c0181c000900c40c50040c8844441d00e1400000d4560154091900054095032101c0701418110715101c0e807208080340c102c0e00415590032900141c103c1c0d10a10490300655203071b002c21603403000a4080101035200001c0820900c4040c08060b41d00036000400b510249969040000c02c9401040405005070b0400060f080800a03e803081908503060300c801072108410b4000001c5d181d82e4003c42e880249503010021504945096055501c0c4200740c1045481c02d02031130801918125080710100c075000410800207144400e9402560b070101c01490701c190035a4207560701603880a808030040002c800c404c0b02c2c02d010782602030141500400c840203201d2a02003900c818000c00d90144200319926a004010049842c1c60310343c4c1801c49542c00c5161141c010035442 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 5623047 1250 5621797 5621809
    0x603130b090d08010503011401050108070509041a03010f06030209130f0b01030302060610030c0801030803040f060515040b030105130602160b070f0f020c010906120209030f0706030b0d080f0702 85
    0x618080c150030001010400c500e20001241c050240c11030303c96030080e03a40c9508040c00e03030342004104104260303108010440703940250b001a4118504e82025030030147d26601140466451450100321a42d2400c00b07941c25050070302c40c41c8421560080c0030300180c1c0c1076401048980300b02808140001c1c0051340c600b8207200044101c8400c4030741c0200102a41c1d603580c20021360ba078a0546c0e072184544d014101140c40e042c040d00c1030300f402200c2e60b00d0326401680703151a9800d0640004100340c840c000c40511100c00614035200d5148030300000d021540280b0181c500b1b100464220b5440790740660b14110034000401c031304290080310280d00550250341c400c5509a4038208102030140100703170714909000c1c404010740003100c0041305011540e44c072000209130f0030100da81e0421600c0403400304000c0b82082c401f4501c60703141c601c0304ca068158094034129291000c41d20f402c1d2203103403406154202c030a0500166906000d5624140f900315090130040701d10752140e4040e44600b03007584110745c1d40041d04800b1902c40d6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 5624297 1250 5623047 5623081
    0xe07050f04030b01030b0106080103110103020a11060906010305160608012d03050a060b090c0a270b0301050907020102030702030307050c0703060f09050d080c09040504021906020304030c050d0f020603 88
    0x44011140c40716501e00c2d005401d40000e00040b82d88410a43c008545a48a424840e04880c0c010100c0d101c40890040150003d510a05144013040411038400540000420200e809071743c0f00e0008008645c5181092814443c00080c0182c00c40c0032082c0c01c200041d0b21040660559a690001001d48903244140d01507000d03a0b40706800408400701000001d004002c10207801d414010203090081da8490802c1007100d5a04868000f04941c0c14450341d40342e40e12911184005080450b110488250400ba4001d0301010561100c100f01c130700000140039a00b0700313100180d04124540002d42c1141010680030391a80802095202041800300d03031072b190354404000b024000c5401140400c0b200341d22022003c098001840260341512814103101907051091180901c2044c00b03403007440c1400c903407404102c050314000d40283d9112514004202c00d211600040600800041d0001c42d0703036078594500310001c86015401507200c1c612041d400c00200e0164025500e900f0f80c103e0f0025076942c1d41000d040c03520045 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 5625547 1250 5624297 5624317
    0x60a1b05160810020901050307210509100f02040305120f041d0a0c0801060e0d050102040506030a05100e090304030b090f0a03050a02010f02030c070602070816030201050106030c08060a0e0705 84
    0x58645800c1e00410004604000d0310140710580b0301c42000501d50809038820032003610300042017000011000c502c2100c2100b050901701c052040d0748d03504600460280e41301995120001d4000ca2100c80420617107104801102c00c01c5042542010f01d0b42e22403546400200300d6100f5550b00020b0000226101d200885002e0320200100300d281c01d145103048aa0140e088030001c94051800341c0c0f0b040c83c10b026074040750480303600c0c0c0c1e01d080f07004800406111072035154042c210b60641d000d1101150a03541c080145106904a0000280b1403902e4000c1503c0d5130140c0c1c2c4401d001135200010301c5007415001c02100d06503600484541400d0f01d42e0710915241c4581c45440c4000e5014103922041016400001030480c8445035000307004860000300041d00324403045c0d503041100c0c10100140c41c002200d940140c60018040e44010381020207072881904a0790117400101c0c01070355103d0041c02143e806105001c0c00070110700c1e0001c41480c0060104000076082c2c0521503150440800144035140714801b15403100c00303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 5626797 1250 5625547 5625553
    0x1030207080f130608060d05120a020106090501030501020306191a03060f03010903020601030203160602030414010302070206030a0506190509040209040204110d021e07031713020a0b030403030e0309060a1b05 91
    0x543e5a061842242a030b0090000190101c0302242141c54150351064501d5000005095254444a0000c010742c1c08606110199503e49400099004c441c0c0b04003402140140000f6a503450454104100d0184091844012802103101800890581c1d406031000d80e206c00b0503981e803038440c0400160744000b07070003081b0384c15800c00e0700300c50401d507000c00c9460482e071080e070031504810f6104458480800e502e00a40340103070b00a003c100402c420300d000489640d881030400520740005900840c0707055004a0b00054082e072942c042c40460705220300c0511080344110b03040300d919814000003402840d13010b4000380c814105000031500359034859005529203180303051001c1d600c000b0344030300a010b50090750801682405202c03d0b000404c88030811641c0d0240d05980b46002002c2c2400403080d680c0c00035211000e0b44010540c5400145c84440d4400007a0610040254403490039280040a40d0004d40182e095900103204a92050b00c4500c2520380403019420f188400c211046002c04d01030b481502c020346684 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 5628047 1250 5626797 5626807
    0x605090a1a0102031e07020607060612050d02030304030905010e04060e070309020a0e04050705090903090303070f211d01050d0c05030601080702150109020a0203090a0902040501030b090606030601030207080f 91
    0x3161952000e1122100684028400c89003200160307240c1c029290303480c181c007a111501c885075220130002032045620090001d810302110703807100411a04107410401c03590142c40524418000c00300a40010706001d44021071851500b0343d0010400030041c8601030602140c41d68042e101d0f62a9000240585600589001c0710310340742e04000e01502c02c01c01c00385d010b6040c40b04007041401d031804c155880b66401a006100c42c924100c20302416010090079041c2901061004103480c1c0c2d4244020141d0a0213035004a01341c1409041001e4501d050502078006001001840800145c10003010152031001003180d4158464401c0180d81d01e104549280740818030303003200d1441e140e400002a40c043d000a81e220700e450b0391115410381e03664000041015a843d1071800410001c0510b400825100c030702d61040c1e03401c04000b8070200c0e00c50805074008000464000c0ba040c481342d41e040c42140b44002c81104c0d0384001e4103281c000724030b661002910b000c0c1011b0700020035106000c11007044916200742c03030905c15912 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 5629297 1250 5628047 5628061
    0x1a0c09060f0c0a030e19030503041505070606060801091a03060c0f0705070b070b01150212090a030515070809010603020a120804050904060203040303050c0906030a05060f0301020a03020429030703020706060509 92
    0x81804040345c40c0c40b401d0701c040001c2c81c0c41d405002c21001e49601200852600c4c0c20000d004031403501001014003041420800da40c0048c00d40c0c050480188115254207169504140e80e0100f50340c900c20785107103075902c4c000384443d00346c0d000204140c105000c4180e5964901030030403445014824208003828030301c110701000454402c1d09006141e224040d00350400319980310041d008000c00c82c0000040140d0101645d507141402100042c0450007005045541c181e5580ea503880c2080744a040c04000e104001c4200000d80e07030030140c60781d0701c01c007150001c01119040d94005041d0030207a008000983d085015010104520b40d0b003100c019110040000f042e40c50301c1d00e4004c002c0d60046038100c1c0000d06010100308898a180b06441d8044c800500c85070541e03940d0030014000b443e000b071065611012440645c41951801e10081500b42d04a41d40913236602d083c03545669000c104481c01a800c0ea0116200e90300004c503040a0780c0d00300741185400350307523030307a1508028016020503004150700c02620018800c030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 5630547 1250 5629297 5629307
    0x10c0201050d1406030d0201020a051206040f06030302010207020a0f0501140c0111040f1e0b040504020c010f05070207030c0b0403030207031203060305030a09050117010b03060d0204091e1a0c09060f0c0a03 90
    0x4c291000c4046840407000020228203038000c0e41030f0040031480612004408a24902c0360f40c1d4401c201510010b0001c0f0030201d405d0545281c0e40c0260003507540080d130300080d800c01640441c0a0401c07203a48a44131454070307000030500041c40004030141003001c5172048101c4000e4010f2186414654a425207954031046841002c100910170094410300401035400064003400043c01101c4600301013030b00307251a003030500c0041d51111041417140e540c0d5400c110b070908054441c8034020000350740102131290840c68040c1024655400001101e00140402c200003030303000448909580e40840d00d400012902301c0243c014046036000100607000118001c00147c0e481080441115000d989030b1395006801c04107442c10807020300032080d01d1102040000c40302c3c140700030a14201c500c043c1c40000e61803444e8940c82249841d41e484844c00b406c000c20600244120558480441c910840b04500c41d410b00065002c42071080850960089002240d5000c148140c007040e0740100c892001960b802d07840c24135005107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 5631797 1250 5630547 5630551
    0x902130509030c0607020105070f030207020415030b010503070e04050c1c08030406090b06040c090603050601120603050304030218070c0303050c0c030a110f01020f0904020906070c0605030105030c0d0b0402010c0201050d14 97
    0x1029100703220011700d4007481401041c1c0240915210510520104039045006c0d50040c2d101340d0b00302c0e864228081c094108580b491000b103015000040d0310354100b00030103040c008070307910600c50b08002e1401d100100708003290100360040115070000d418035245030800204200414041c1050101004001c28881c1d0707500851013131f911500c1c52502d940e450b482000b00f21040001c1c1040061107222090100e00d0095010b180c000f8014100320b4a00700207280500c00b50348540e04201c074181c2000c1020400c6003008000300c00c40402c0c49420303108c18034040c6002811201c0c07140d0007408054980c0041032000c00940c0803110100345040a990b40d50700c028502903d256041100c00546109681008541d46410320030341300d00100b107103407091400350aa401c0002a4101044003a40090104206000200440c00c500300501840d00c82c10780301d61402042500700940d08040c10b0245c00352840c101c001070360310f06031107078042d6090030843d20145c1039000403102c5000320746c1d80c43c2da2140f0b0301d546d01035028040c0f5000f40c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 5633047 1250 5631797 5631817
    0x60a0e0103060609080604020d0c050a030c030606050105040b0d02030408040b1206010e0303040503030d0b150c0718021e0d09020301020a170a0912110a0f08030106030506030c0310090213050903 85
    0x1c00b1a6640e000c0448000000b44901e41054101780d02080040c0751005044040d203008075070410030700340c45000188100e0315a5204440d030250540c3c0810030409640501c02c01403109080c041e003010b00d8030060740e08521801c0c40554607a80d0000004003008010700030b0340c0c05800604006030301c9001c0c440c40491446c07800d49403d8003241c003032041d054080c0340010032982560005000b440c186154a1003c0d000b418140e07c24a5010f1150240520703a010000d003e400078030f00c001d00030801540340428a0100c40b10321082505001d0040052203680c24245580d21988426101900e5550170700081c003000030f0102c210000d41c035500005031509030540c400c201025102c20600c00d1240c689840ca081d4080b100160002400907529a0400300341c00e0250007641c2d2411000800d840840e601a80d601d1240e50106004a4000202100500c280c1307515125a40d8040340c140c0040c010740307c002d8002a03684c0701110500ea20a91901c920078115142d4840c0c2e45600107085c1000c1c0903e041ca5024141c407600200094 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 5634297 1250 5633047 5633051
    0x100204090e07060e0103020c0f060a060303110105060604030206030a02090a080f0c01110604031803080406030501180e1002130302090405010b04050c0a170408070b070e0a0603060f0e0402040b060a0e0103 89
    0x114031800c0412040125091500c0e07000ca0140701324010b4010307400c8104c001102c2e01464100c0e20f0114003c0c00a00d103d010b041d080050642d08500d0060010035003201c81c001160316003008c1191a8492108032004c1c1e86d01180d0f00f5442e607464106c014064840c400030181c204010110010740458005807001c00001d0000c1075a64030100f66004440080d11664060300c15402840800e010138000c207003e07001c0b0801403480c132039a542c076070b10380003440d9000d540315000280d03913031004025681c4800328070014003441030024820707018140c440303d503103c07010f407403501c80d00f0350026600d84000104041c04004684c0601446002e00d46410910300810302440300c940070f1418600098116550744084a0b9100c41c181c40f0303041d00010202c0f5860300240d00800444003003404024400220340c9441041c0c1c40f8810654501c0b40740c48504042c0400c0301d000e58050018981003c0d8140030065114000b0405e42d00f140d1500c0442e6995030000601403c0d5009685401200019840c0001944a0f41452000d0002c2e201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 5635547 1250 5634297 5634311
    0x6060e06010c020901031403090603090307060606080c030403030506010203091002060a05070c1a04030219110a0512070504020c0304050a0e010905011d0604020703030f0606021005090105010f03080c0f10020409 92
    0x195880b00c2e44920080d407140c01200140000303040054549620308440084030704103410200400c00d50f52045d5003030120756001043c600c0410515024000280c882481c0c0a562814001c10034117090102030001401c3c90b80b01d00004043d80d1080083c0c80306000000c007466455030455078040e44488050358403c110500b00030001d4050345c0500e070503e40c00c9501c00655400c07143e45c03120100150402410480c214051402d558000558080c0040b4000f805200342c1020b0390038000070003c200380980d2209009007002c40142c81845000316682d01124070a80b005607842c28081409415071050b60881907120312000c0c008601040740c40c90703030b0b0f061f1003a0384000c108590704d4403003981c222340c1c1920342041c40840c944000b40032802d10750041d20100d4402e09011074804201501c0a0940f0155001394005901c200c04145400500b03018040e002240d5500030800e40d414041040301da8002400043c064900000d1050703214442000090312851440c1c094840d402e0405810401a600500c80c040740f5504140d6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 5636797 1250 5635547 5635549
    0x31609050f0103050d08130204020301090b01030e0607080622020708090a080a022209060501080d030c03050402090417040b040f03020a080102121801090203100203220305030703050a0e0a06060e06 86
    0x1241d410b9980040003032000c0d04076510304a42008004010f121521401d410340001615607001a6020b4040500c02282411a2000040803182010a046c405901c0f05d01070103103a07504042c0254000f03406480400800340d60300c030700201e403040000c0f50f17200d40c9100180f01800e01c1002c4011308110b00f0220741010a030359030341041d10303902c50f80c150000e90f020b110281c449010500d1524040d213031301070140300410f00f594151105002c5640907441000707141c128101c24030507183d00d842180d10a500c1c50900304050f04083d004a2071400f001040100700d684400d0311100c109011106850050000741d051a547d1512103400200444081c4002ca014041510000c20a0f51040c001c0c0c13040060007060b00140e03503489011103d43d40c080008915025540d50b00c84202584007481084214040c42402590b24140380615006e0003102e403400c02954151003092600003036000d8101c171f801844c20314020505844521a1500414034201050340c1e610802c5400c0d0b08005440d00180c0031158615000801076607010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 5638047 1250 5636797 5636821
    0x5041703040308010b1303120207030605070903050303160c050d0915030203160c150e060103020f060a0903080a0314010e04151802040908090301110408010506040209090402010e01020c03160905 85
    0x920000c0c00f01c0c3c01d0a0051241031251000740c03903400c40440c602d45403141d403501c807448180502440c035401030700004428400d0000314002c41b90003012901d0310140807841c54a500f616400301a00300011203d20300e4810b980680304a840300307171107608101900c010200004020b465080340d0311440085200822501800b1402407080c0d03846141040b02c088000182d402e070032910080000b5040321700b0050004003041c003031018807a50440c0044440107222550540c0100454801d0898515100c1c0004012409202ea4031a8000d82100c0c3c0c040d0900c0d4803019010815000f0700400407a0740a60301c254400015801c91a030341da64003c0317004509018a42e003400c54824260344e2402d039603401012a880042e00181811303400f102141d4007621344141450070b4640040d0940350303003c6948840070030102c0d00340310800703080c03144641021041b01c0840c40c0021031b03000314018030001440070b070602c001d5a10a01c4581d00a026580e5080310081c140c80c0001114034030400c9081c0ba40c0140c880d068900390001d0a005011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 5639297 1250 5638047 5638051
    0xa0f0f050706090f08030901022a0715090312030204052107120303060b0406020115090e060402040905012003070e1c02090709080303010b07120c03090302060c0307020603040605041703 81
    0x1540d24146040542e80301d62000d441c1000b0304a603100144070300e038004200d480300514028103919001580d1b0380000d424045045850780c4150078458030482014034a4600040d00100300c034841c40300408004842401900d603c00954006801e140359000841d4030382c0d60582c000d000740c41c01121208031070104113011000300200c8070041c0340319520840741404003850001d0310415441c07082c81d010a44a4844240380c8080d00150300000140c2e455291030789000115203a0038002d4400c2210400104841510055813100050000303801142d91741202c4c01841020f41040b03e0b81c1045480e500c4c000d5901c1058481c07540d20450314800040c0551899400c240341c05040c07111f00c2c000000384101d41000319000c101d21070501030201010320aa138040001c0d01e450a0020314003c20302c6d81d81041d180e82c10350409101c00e03111a01501304100c00031005000203600440d640b07041d00e405444c100e0711819030881841c81d52040c000060760001c8040304010400071240c010b1780c805c0388205000400d404485e91941454001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 5640547 1250 5639297 5639327
    0x20a140904032001020414030706020303070203031303030e01141803040f140402040806150301060f05011e05090409080c070504060308072603010803030709080303070509060715060b0a0f 82
    0x9900200700828070030b08407000c0c00011098841d02c11030102122608a0f4400c1d440105001c2108000405c41d00c0e0520000c1c0041940d07001951562512480c02502e034800180078404151142210806052181d030000000304a01d0008000d61400d07100c2810102c4400c403048810091750188204e60401c002c0252002c450b0b13590400c0c10103c0c10a4500311180d80c20b40c2101d1b80180e400c0c0000680041d040040500502d0385550001d420040501814290394940c1c005100c1d400130702c2c5040005036031241c00c0b039440b080341003107480c007c0008482c1194940f00385001b441c0d026081c640001c3c1404030100040c424050007400715070300f169172070301030000380e602078070004e003d074801403200310003084002140071440101204005112840c204400f0607603002030700036000b40e03071010003040a0580c00c0f40ba03074006410100021030840c6080c290040c4540710799000c0074000c0b40d012815204005c0e03111a10b50405015000901040d81c5480d41150302e6008003540700001844c0c103920b00c1e44503010380001100c040d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 5641797 1250 5640547 5640559
    0x60203090d030323010b0301090e0d0f0c03030623030c040e030301050d080c01050711010c08060901050d050115090e070f0e041101110105040309081501050d0b060a03050106080703020a14 82
    0x600e42d02d058000742252810651022510650188180c03080c582482c0644500b08502d51039504000d83d80e01100e000030950501a444440da2000c1140c00c0101c800307132000540740c510700088081c50100c0c0900129401811141e0040118002c0c4040490001d40100b034207030100c0d01c0290307440041100303030f502001080c84076810030401800941041c035081442c95005140491400e8400c001690860b0300403903011000034802621007041d103002780540900380d0824a0021014285000041c5a00b201807007850f10501c1d101e90704800700602074108007001048040c69542c0350b6550741003c4003a00000302c616100307000d1100081008074081010714240c2ea1854101c1c111503513543c0d0754040a4070450610340c14001c0ca1064100d58100c00d0203544e1240d48240e44505001e4a4050040d1400200d030617a90f8400a01c0f81c0180600c3e10b4101420054540150700f18680351035441c0424482c0c5095000940742d5400c10a000c105000c00081040450740b09451401e81d803543c0c2d05450200319650f42441d41d010f0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 5643047 1250 5641797 5641819
    0x306010f0603150b040b1201120506061201091407060306060908060402010e01031e09020a0501091a030703060302120105010806070305060303122e080c0102060403050a1d0411120106020309 83
    0xa2080d4018001d90310240402e10383c03180c540c07607a110207804c1740e8400084603000007100c200d00e1110012250040103107000341700c40c01d45c0f1582d829850385401032409001d6418401454941c41094000201d0907400168040d9103d0030000c4041d1035446074010100820f0a204001514501c121601011902084040e1010b910b41d9401141c24090480300c960405840e41d1f07030f0340b1085800d07004854156101010001d0104030910500040c2001d5522590501803496010030400c0ca154038001a00d00b54440c11960300e94424105400800c4547c002039000451017149054581055002506849207102101d40740e60742c452045081c0c800455075035416400600c200700c002d803980c2d0500341c1c10082090107202c102822080c1101d10704090f002043c2d80c080e0064007044080710038032004648000a202821992519031000f4204d841581040400c010906520480902800360310310308132035000b8028030030305200c025032090981016010361143d210300d000006000740000210342c507100010385800094 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 5644297 1250 5643047 5643059
    0x2060f01120804150203070606060f0903080706090501020318061302150a030f0c05091203090d080706090503030403080103050c0a030c1a070c03050d08010605031302090703021209010c0e0306010f 86
    0x10300c103010301100d000b1010703c00032a60105182241030960102d600440d01c44021781409010360340c00b54042c505000e0700e201c00c0100b9691200d902c100382d03604882c0d800c0d5207d0b00c80ca0414018160404040c041e0752000c414400e43d00c02020a81c91101121421a60f25440f4600d1074160b00f1402d0307800075400400c040c0042c680d41d0b68280541442040760070300040c00c003043c8110320280d41800c200100014400100d948081c0703805201c40c140074145200031810716840d040419016000d020b0302512221011607400c0800219422403000c0e81d0f881000e4076203d080624000d4410f080c00c0c00211128003c400420342da07810b0141c820307000c81e03400c81c09810001e49080645407040103190115808000c080068201203075544040400442c4100c0003400c10006c02032008044802c1070300705404020040007030100300c0c00503040c03105900341c04498041c2582c40c3d400080c2c0c001d215000100c00781035000b0040120015040d80004800d44071501e90b2140c0300e8841c010036803a907000340503803603c80031040c200f4808 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 5645547 1250 5644297 5644319
    0x70f03020906130504050d140c120702030f01060308030402120607080c09030703020607081209030307020c04020901090e1008060a0212040b0402030304030807080a031b0c030f051309020301050f0102060f01 90
    0x30600107800828001d54000004044c1c0b01c04403401c0e140c035405580032204055204024420f06142c00e680c1c1410009a010b002d600d4401c40035038414014800b05900c07040d56010300c021020342000d04020080c2960340d103400c00441d04102c4043e03208401d070b060019010b02d0b012512522600c920713991021281d440303040100312504544d09580d0140b04401e030220050711804001c012681c011401191100c49020b225841f1030303002450b072500f640061081c80241600000d40c00301e0000211000b50300d0301201001210303024020780c030a4120010150a018818208c004030009440680d801e603540b950b075038049441a1310401a103100001502d500080104091995080d00180300409407890642d0b01c0d15011080e4014020a442c00d840c00196286219058841d004141302c02900d0101d46594403071002c2d16104600601500740201802420203052003842150180148418601c1d00c06071143e103000001d4109001e0503005054036680c031a159800003c5e103621441190494001c107a00700014801d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 5646797 1250 5645547 5645551
    0x2040513050a0e03041d010504060501050a0c06020d0501090221010f050904020f04090312060f0531020406110c0f1f03020f030406050f2419030501050103060203070908070f030209 79
    0xc1a0380c0c0c8101900000000f400200000c10341e10426203d0703581b800081c5642500c0603442030b80306514261003040f9036600181a501591503508020f009440c1a0034481c001c2c1c402e008040600134600700003c10150b03c5540030304220600740c414440102c01d030a10000c00d1010038000d683c16154064420003803460000022030303000d031010f003460400c045101c0120b401c0d2002c1000440c042040000841d0002c0b0140c4110070060001045107001c03240f400002c12a0900c11042c40980018003000b59005608610400101100c400004543d00c3c1c0c1d07203240003080140c0f0882c802190f40681021f00701c02c0d20742080017035412500185200c404030b04050002490950b4414014140b64003070080142c1d266040001e9842a8040d00340894549440301c095078111030020501404102291151014190103c2c98810b2240301504c03242e0f65240c4401506510b0481940014542e600341800070080200300d801560045440392030b00384581c1e482d074565a469417014081c0f50f201c10094401003000d844d01108080e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 5648047 1250 5646797 5646811
    0x30103150c140901050408030409050603060907030201051209010905060f150f0f01080601020a060501080105011502010203040506071818020901020607140304060504020d02090411120102090f06030703020c07080c010906030204051305 102
    0x82e282c26600c03210b07d0b0868100d5400400c070b1942e5002044400e013414020a90301401d00720191041d07508507070019040d40a5038101000000001d000a075030000c0940c4040c0505810401305d51803403501d00030402540e2000c0b1440101c6011424201d121401c0102c8200505200201070042d40c003040d00044401ca90b00810940c11840b414000001041441c42040d0181260301e00120345581071404441c0007640d440740311000c580c810420040881e001140d290b8104500f4688454540d07128030142c1c1d201140c81c0c0091401022102c61081c12012590040440f410203800755440c03699101c03016558207102c2c91054207000310030800100000e0700da41c01580e10034801411451130000c25000324241080484023180e2903c294007016076a0700e030840c405522180c8070340c0203500e40006180402c0d0540f03489080c00c0e000b242c1c01b00c0420385050298050340d10f0180010222050b581d0345103061030780c40d030741c101d1864081071180002058480c440d00841d0155080a800100c600441e40b44450040c18010002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 5649297 1250 5648047 5648057
    0x10111903022b11030705120a0b060a0e04050124080901090f1103010506040203060a061103070203011b121104150207050a09090b0c0304021008041109010b030103150c140901 76
    0x80000e00600b0038050203004180300361a01c00300a512002c8446404000c0c42c000d10074804c000d42c00c2d50000407503001e00c00300b060100c10703502ca18500e180035040049500c0c4c1d1200c40411445082c1d0b51001035600204001c80b805d014590340c6464a24000f60b07410b104825280b1405240740d00d030340c024121240c004c0c1c0a030000080340d64041c0c50300c80f0712003640c4004070340c082c1050510712030a00d004d009281e0811000c03101185103017082030004540328454403c620034003001642e45010380070280159051150060002d004429620034400e148140c121a0701000ca00d0b90140e450448c62a8422140c002d41070b00701c1c7c10b05d8a4140160001c061442203004011403080440100d100e40f01c0d456448010996201c0104a07071041e8500001c040d0001491070102a1050082001503030b20031314040810340d10360a10742c10a44032400d0030b500ca041c540811581042140380000381140c041c40c000c5040340d0040942c1410000071030083d40c16200400344400000f816641d1002c20aa0030b0401002611014100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 5650547 1250 5649297 5649307
    0x50a02060a0504060f020d050a0c0501140405030702180402030a02011b060c08090c0301020702060a0c02120102030903030a0b010509030705060903100e0309010e0a06090303050d0b0603040b0601021011190302 91
    0x2101980702200050000d44040303010802d0320b070481c4100c0180012030029101e000c407140c83c01812401000c4009041069146010092060070341c0090021650031003620824a040d042060382c0e40e221000c01c034000c81a0020307065107a40c6000659018035030040103000480f000c1e800445280c5a041d000610500b641c00205002a0b110710030622401da1588468000386010760754a401c0500d5542c9060090340100304083c0140ea41074215482c00d581400c000c0241c80040c00420003410307410000184640c0b0010500048400004c00f940c40f0700e4078030b0380c24000042001d0044a003402000c0150707405d0b80c0444000e009500d030203409801e40c044054116a18a906800e182c8156045c1c2c1450b0441600000342402e400d591005468850803019030300d0140300c40c03410000401c4d920b105c0c4009000c0150126140484254541000d0b4011200600040e12814581060b40e4600e000f50b52950140c0309001c6224203401490081c40e1114010a00030750030039051742c1181074907140b003103400c2d400c04d582080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 5651797 1250 5650547 5650549
    0x30f09090a0f0e010b010201050106052a010207050a0602090a05040b0306040209090309060412020901050103050103050303071b06050a0203100f050a0e091c051c0203010b040306090201030608030313050114040305090904050a02 99
    0x125030343c1c200152400101d640f22050001900716141a040102008000c2003c0a64910801c07504c41704030400200b00b0340a8800f0315111802801030b188004c1c054001d07083c4ca00c091201a8003c3c00441c8800c603100038645039039030204012180c502d450560941c01c900c0001d005450658042d56000344030f041960b01d0060381d01c0010340310754000d82050105054840360102507090400f011409084203003020402c550554032104d95a01008194508101c4541a4551420038000629007100e078481414859824203800c1d0034080e41045504451402c984140042c5400c105002c01d0704540001d40000c80d00c0f42040c031140c80403a001010301da010300c145c000300c0000c803440448502c802040e03546e40d65111000800d00d000720712000c8600400c4640140018841f298501d821101141d602100019502e1211320042c1d004e0310030742d448011707a40800710411104034440070120600502c290000c0100d4903008c001c2c06003030304c030544014000500c01d204190307860811003c82508540034078119001083c9544c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 5653047 1250 5651797 5651801
    0xc0b04030c0c1503060e04030903120c05030708091311040909110d03110f0601030b060f130509011a041503020603220510060e040302060c1305040608010608060702030f09090a0f 78
    0x182c04100100c0f02c1d900701c05081a414401c103005440c07204841700c81c600703181d10024030003100e601010f0301c418401800000c0682c029200300c09060340c04800d4076220341e0141844002a00074001441c001c294400e8140714907469841741521000c1c00d0303c003a606103404e080040000b807500040c120341c20703450350340a44001d55401c8020501c15200313984403d2880f4152240d18205801d009416400f07510a60043c00051440e511480c0c1c066420742d1520030049851000420045a1071a030340d034054a003000744407014006400444003c5029407034400761740305c4041444100c40305a81c000041e07000c40300c1c00f070005180003c0296041000c003039144503059065009050301107404401160340e03901c0341c1d07028a1a00b071140100350050075070f50f00500729440c0c40d8402030348a000041a03981c60040015150420300451480d85014060242c001c1010b547c0b81c0504d24020011401a200700380304181c0026101e510003c111031031612107c04550034020742c2c5042c0f00c1641d002a2003039850035112a09034103400094 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 5654297 1250 5653047 5653049
    0x708030309070e01030507050103050c071202061b0c120a0306051302030a0b060406020a0201030e0709060b0403050f0106061b020a031a040605060603220f0b07050706050603010204060c0b04030c0c 86
    0x140695924240303484010300d0184564050405a081c0d1401000032a0001c1420307002c4a80a0170701140c070b680d071031456070060710400000404500110610450076580060032a120b180700100c10b4072056468001c00041303006141c007000c019400107040c2c50313007a02038001610304580a407c0c0030461070388901c0051040c030020240250200c0d40481080f4100f03009004855070580b080d0b54061600d070410344005c0d101d100c880006418180c0391f5800000154081040384020044240300300700031034480c44005402c0e8001e1000b078909203e19902e6890001042c49000c0446040b6228058050030700100c01c0d0010300850303002c1c0e0303200c2c022070740c000045184c1c0b140c105903640c180303d01002c04d40b4082c548002165009012140605014402c001c035206a0803600c0301d5140614098084401184c03800b050407202916008181085110900046680050103400054414601800103588007000e01d801c07805544924030008011000140114284024403034000d406454599604c0201c0c0e12074200141003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 5655547 1250 5654297 5654309
    0x4050306010e0702060a090201080103020f0f06040609030506090d080403081305030a030605010f030b060306210304030602030f0a0b060403030c03020309030607020c1003051e060109090504050a02010f0c030c11011107 95
    0x50b00741008107655042c444180d00003408081041028035903000205401014040240180e0500d2030751307049a511200480f40c10030008140595a90b00c2c0c1c0401441e2075442d00c0221a40e104100115100220200e100800000c140c0da51040d507a44a0700c048800c004050f280916004c04e41180c034004c0392003400200007003456502c0c00306500b80743c540010840c9148298510403d40b41c016001c5050340c490702107980028084500c0300c201c481d103002820420f10b10399015007680c8000030f0000104909500603501c0790181482d1080a1381c0c035401a03006840349120000d501c001c0c2004140700190085d660741d000b0501900c1180e04005d000340209103000c005071103000150b40f020240041c54030f413a07200761a41528a140501990400d00d007602035248407203039000c1d020701e1403600081b2164480c0408200030710b0140c03414002d5040c0b07400c0c144d031140313542101130b40000c00050214210600a0507060071155056070b55180d42d14681d114503014030b074002880c0e81007148800c805e400d4031404110600203070503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 5656797 1250 5655547 5655569
    0x4030309050f010f0210150e01080d09051c0204090c08060708012405070f1e06050f010b03010501021c030e0312090106090903050d0e1011070204051f05040902060405030601 76
    0x10501d41003142480c020040581002803c00d03103100030310340c0465450100107030f1395030201c4c441000c3c000c00f00c0d2008150300041d03248070704c0100025070b0403000154a42a198141c9800311096102d40c00d00480504078200e408500b1030000704500142410303807104118a026400302c90b241c079160200179052000503a06180002c064030018042501c6140801c401c42c200180040319081740c41402510138001c000c80074091348468a0307000c0c107108410752402c442540250382800e003e5480d1520000810301514070f02414060440046a0350342e01908913070507624140c0007401a950151502d44003840e052501070105601c8440f80d000c224820000f40944000e04208402d492800201090031118150300801134607040521031310101e50058200c0c0d20a141260022403200c1701070309000c5c42e2101ca108000c2005203040952101982035802400516108a606100940320f20460040843e4030200703411902d900d0b9582000350340b4151340540c2e1201d2000c0e241500345552200024140348090b84024503802c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 5658047 1250 5656797 5656799
    0xc010c02060c04050a0e0a110307080703150b0306090a06030506070e01020c181305070e0a0603030e010e0609040209011205160f020a0302060118020705010903030b010e0a08062a04030309 82
    0x203405206441c0e01c0b042e907030541424035280c48001012001688222006d140d4880c01188401050341c010205001c4130407019513490a1891000340545d030111813130030000740380407040c581d0500c0700c0304c840d41280c400030107003419501c549080001088002d880b64201d90b656400010000c5c40901909200d1031454403590034100e81840060300307091031114594400e00840324a04821170203511165013000d18413000c64812245071904501e8040d4541190f54074880310020000b52800da0b40140064034440e548510726440100c00541d070340d81c5d01580d081d512070b5090000303008a08244c0d000c0c003000c460500d8402044100b0070b4103c0b0440d20155481c0308071208582203611029001440c400e90480c042c4000c08c1c240c031094400944542041c098103000c0e00b070b01307001a001100c0b0b603015580d13101d8001d80200000441e80c907014005200303000705980800c6802d00c07603003224a030107810300f0126520b40717014000c140d41d109140d6502e24040000d1410602e0a202e0480e10030548201800146110782c45103e141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 5659297 1250 5658047 5658071
    0x40b030c090d050a0c060e0a0b040905040503070b0c030601030c020303070c0204020f04051903020a050a08100506040e06070f020c030a050a020603060105160501060302031c0203070212070b0d0605040e12180103060302060c01 98
    0x403a00001240151000303a41002149027000443d02210103031040019544c44629006081d48540d5a01916195070301c818000408040360003140200800d0300c04004036480c0c07200603612408201c4a0402060f01c83c3e2101d009810150000e00702c2c1a0464111498107440d20001500c41000d00540c00752541c04074018411400c003810749001620f030442e145154030349003d00c1d4507a42d005148040b464152118082002d40c0c031950081d02c1c1c4c80201c0c0c01a00c0d02403911070001800e004250700030038014458a0002a0b842c00c01186007400e2503007140180003070b0780081d0284075456202a001904010301000a50f030308169804002803424030481c000f154403880c40c01010715004032020880903001c0d090040003046900003042328117003a81580d08289142e16059104e0800d542130784100c84400c0300107101f414200c0660b0104007510340c1100e04101012001c11850780d5041a1b000d01080d48004000c030940301c138222a040e101881c014900401d0a07500d03680803400c0c5030407080c03941081c6d81d114a504480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 5660547 1250 5659297 5659307
    0x100501090f02030405060a0b03100906090209070e0307030f110307060c03170708060d0f05030f07030305010b070201020706050c0f010f0b0301180b0c0903030f0406020f12040b030c090d050a0c06 85
    0x140040c604150700f10b00b000e8541c40c0e25444003501c9842d0882d581e8503400c006881c00c2c05a0f5003a4417400004000f01040ca05000e0058120b1040407482902e410300041c07411030050bc00180c2c1500040c00414416085948078041014014802d4406d500c0004408555590402801c0090045503440701121205407401424400b070241c8040754070744805080003081d940c0031481c1075003c84100c822000384000d0f13040580a02d80c5980d8058010300000580701c43d588020b038000c012440c070996041040781c1c0e9034000d00c1070350300a4180080c01a0042c49080220b24410360103011010200c00594015904052086003110f081e40394850f90f003074030351010000c0c1e443d0a114180d03c0646070148000c100c003c41d90b8141c58020014a49181b0100100d030700300c2c403a24100b082d24100348145441c5547c5944804000c0c0d56140040d01c984141d01c901d401e844400e40b10301050b602119455100c01c1c0c11a1900ca8150100d5000032000c0794008903411512008203000b0002a10314900610b1483d120320f0800c0d400a00d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 5661797 1250 5660547 5660561
    0x1b0806070801120206070f050703030503090c010e06090402070314030f0109060b0c0c01030c0201020f0f040306060501020a0b040f080d14010501080a090201020c0f010c050d0302040e060904031b03020f10050109 92
    0x50001c228010041a0400250480201d82c12281159a01040d00d4903a50708403030154041d001d449500e1005c0105504140152300910446d02142c81c050040401181c1c0c10b9507050a65401c10001c0c052410141040d4002e095007520900309002c05111000820035103410807242e0ac29054800001000340100c00d01c2440c000c0d0591080d03da1812505c003002564540513252114101036481072518202803007036042c1c501c501c142c0c240701c50380e03840b400d00031110f55040340c007040c3c840500e08000041e856000003a90228554040200b0246c2d9070781c0e440c3c0d104c0300b482000c01614400c00c1002505514a01c87c0b02e035410440302d07070070b45421070b5040400040c48288010b00e22120103290908803400f41c0c4e00050740015001086070440394071804000129245050110001e0181c46811043e07510300e5050303005841610000c095042150741d40d6801c1041100003580c0240c041002040201c8642e11001c0102c40241d0081c01200c1690840c0c0c001c0c5860221054145410650b540300184110601d0b0b00844c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 5663047 1250 5661797 5661811
    0x5010504060605031303020f030403050307050606010206040f060b010c021008090d0905060f0310030c0605030a0f060e0408030a09080a020a020a0905100512010608031201051809060a09060204031b0806 88
    0x10000b4202400540780d880b0240140601d41c3ca0142c90750304152080200318a50340446c015652070315601e2504540da504100d20850f614002e450008045500c0000d5052241d600903290310b0200360340b5110100105000e00d034850400c514400040003685849541821010083d03075041c50b245008401c4500f0491070b4041035040041d03c08081000307598244c107449408098078000e0340e4030340301c1e0300c400841c100403603000030051603404400003020b0303401c98080c1d845803003089024004c281224500e60129003a50081d01c02c1804a00080b03400b040f43d40c000b866000c04120780c0012030081649a946081e0441d44000d40182c3c01400c00ba4214103042060100034441950b06201c6401c1910526101c06e402d4011240601c18480b03100304904025000301e4020182c40069950f60107070095800025007090103441e00841c503500522454801d002030300c52080076a0f0001d0080764507941d401c1c3d4050315403800190381180d021300c00440841c09088102899480615506403000d281989480c02c1000081001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 5664297 1250 5663047 5663051
    0x91701050708071803020d08031603050408070b090109020a080c0a0602032107020a0c2310170703060504060e010305060705040f0501050702060408030a0309050c030c0a09180b04080304020405010504 87
    0x1001031182c208419a8000085051128007181131941c0201810350f160f1000c0e522040750207021060102c280000e40c020142007900e0029003004d48400e800780c500540d0b0080c61400d081101401098100e081c482c0c000381c01e030300041407074603240c0c00080d5402e1081e0846416a001002418002d02c0c0c5014401e004080c140095400c0c407807079a4444c0c50503030800c00810000070041000031072451003845600c02c8258040b8450203015129210302c030710642c1c0c049041e1005c113450f00d84211580362a416004100d111960340e910340410001c9130450a80000d0a440700340344c0c0322400030909a0303a50081c10003070102155000a550314506000e0318020004d800c0c00d050003c200400e1012810084a050942d0400e00f003103541c178511480818036070b21441d8414940e501020031044425607044d00541c500a0041d4125400b0411400070144c480300c0d60003d5070781c40301e02c0740c0040080d44000c2e0042c00d0704034080382c01880031616903120700c1c2000030200e800710b50b400000030420045183c0382c4200c070301504041d541 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 5665547 1250 5664297 5664301
    0x40b040605060306060c0a0206030408090907080112120207080d020a02030c040e070e04020d0206070b0601110105280b0303040609180606050d090c030618140606010207060c06020409020a09170105 86
    0x1203a00c41c0310184c0180e004020000e000c2002080420105000e1903000d07003855624506402c01c40c140d500100c0720688905000d01c0825001ea01c44c006c03840c160703860b141803a00301e69590754039080d825034004200010760180440000d90341c80c0610509031402103540182c180d91610344101810b001c002d01409200c3c80c0742030304000014200181c07500540c0c020009807881610382d13000007004012000c0c0002c1d0b01c81400a1001c0c02c0201440d11140900020b0700d036007820008031f5011509880342140c510122010311030111080c820003440c400eaa8941400e00058004a0178001ca0306647c0030b500030401080c61301c03408210030b2415000304080c20342045c0e0b003080440e040106c001c03e00d01c1000803140c8255101c03a1000d043c40481d080c4080110741c0460204012008980c0c10b0046201030030090794103030642c0c2c503500a0a072022907810b100e103405901030141c65050007000c0e030f24200440c00584003140e00384400304002c1103510007403e00900986036443c3c283d1501c455000d0148221411040b96410041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 5666797 1250 5665547 5665549
    0x806010f0303050f0d050a021209010b130b0604090603080a02060705070302030f030c130602010501080c030303011d1314010f0c020c010906110a0f0818010212070f06020d0f0b040b040605 82
    0x68840c00760303903040c6011030341c40c1104030301c0c15054025120411426071500013400081482940103191049083c05890116914080000e0880d080781d20401e40044007940c20300c517510503562006900140c01081d06040544842d0100d003203071615081101c900100295200e0035503010800356501c1100da14003145000130315074000b5101d004d0301d1145604c220000c17020940703001054050380c4088011b08000b0310000d584d600001c0c080c0c8020311412481d030140240c0c2060606003c0110b0381030300c28411140350103d80c803c85406000d0401003245da2041e4403200c05000041490703520582c601c0b4507400104a034448101d480381204c1403030080009540c0241445042640c00406ca00c04481550810500c0307098280c0490f402d1902c441001441c200b4001c4c14001044082d5028044c280641890710822501d09001640e0b41c200b400340515a031401844000b000801420342d110030144501c0000d0b080c06040e500c44001e88045078900b08489803128100c503a1070819200d0300741c4600701220148443c601e004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 5668047 1250 5666797 5666819
    0x606051c050706050f040305010f0507030510030506130f02100e0306010506120a0504170c0307150c0503150301020415020a03020111030c09010c140a080301090c09150305040501060e0c070c080601 86
    0xc401c1009002c40880c1003400016810146c500641e0000024402c3c80025a48200140001c48005020030b00d0301c00407404400b580c0c00716106890b4090000d100d20b803114920b481111640d11400c03141070900070b8850006807240c480748451802d82c0e40341d100000340382c041010308154058102ca40203100038040d4240855160f125240c0007001c1400004468075142020140c4035214100400f031140000360784040707803d000000b4401d00d802100c0344001001c01c100b6800c01d441140020000050040c0080340226411102340020000e009000602e8a581c0c0c0130400541c3e00f15412010144e0040013054041c141c080c0122040e0030180c6180c1e51461500e00001981401100d4002e0304025848032404100680061404501003000b0120703507480a4038035081c100c5078401d000c0c2070416411309500e4041e0900034200e95007a070300320300c3c03200209400f0b04100314020540207005440c0c640d00c0b01800151031018010700c0e40101c114484c1c1d29541d249508002004882c5540420351a80c842c00041204010355 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 5669297 1250 5668047 5668049
    0x30504090903020a0b0702070f0f0f05130e010c110610050312130305060f06010f0e060304110609090702010b0f030a0203030301090207170f07020f0409020f04020d11070606051c0507 80
    0x98500181c190000d090891803c0341800c4000c1420ba1107001b031040d5a600005e0321011119885454080c10391130303840050080500c4e108a4101d80000501480249083c0200300d0034004066000240e1311034080765513080d1070901e008200420b5045a0540f40c29400b440300707641c030088444890000c07600d0800426920108102d40905078178010481c034609140381d40b4400011500b0400300c41c0c09082900002d00010700c00e0322042d0110304641040c0505c0d038000c242d09420320000400640c1583e031203469004904c1e050003074040d171103581045a540329981d06200903001e21030030750001401a2001c5c0900c003501003510502442a8072199070700c0011f0b9000000c0324103580c1003440144e102e5080303151001c05007005112044803a00041180c3c66100700e0800a05040c41c02250b040c80c240b8403203801d1008481d480c42c0d002c0e4102e4400010a40c042c1482c0d0010003100e4003540000038007410303903904080075070081101124182c0c0c0300c1c542007210b860b11036500720081c0d80c1c100c4107000444071507031919a55151 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 5670547 1250 5669297 5669309
    0xb04091709011202030103060506030708060907050603040816030e0a05030a08041703040f030b1b0301080307020d050708010f020309010507020705090703090609020a0602030310090b010c060b130207120813030504 93
    0x107041c1840d034400d1425002c5819014000d5440e542c581c6030500107400c00310340480c024840e6080004c0d18000c0002c4541c0540448406090418100300c00c1c8202c60388002c0c07003541c80e8001080008401c020324103951621a0090f1740d82181c0c103a00000704544907200d64449480f0303038852401c140120380414116801c8543c007e22000103100302c44005800c50095900014a80e044001d00009210411044a2140d9a00c001c503515013900303a01c0c000010300080c01500d00742c0c4d1050000c1801400c2031102c0d1042607029808450445981d00a000c0c2994030741c0c2c44051550740c005c8240710706e0791001d0180c81c2c0c01c4481d50000d8450301d0704140118602d980c00030200410591a42170101c280406070784002c00150f0080d100c4036042c1d0301c50034003070358a41c01919866002401d40c000055041a1441110140601651020046031079134641401034449008080d42c0701c8003000d2132603da82045c0c4000c0a0f928481c000100d1940c59200340940000307801000c82c41000c203d000103030002517100d001c071001d03101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 5671797 1250 5670547 5670593
    0x3060b0d020304020a030506010b0a08060a0e04020f030a1202010204180b010503040b0a2901080a0e030409110f030702011d01060f0e0a0219090801060501020a08040b1b01020d050402040b0409 84
    0x103141d000207501000305070f0021f0218020f03c0f0012a03542d0b241c0008001140301c80e21004000d4075007205010800e0b0040c03240d041d01e407108078040b400610b800d441005450800804a4031405015128113208902884070800035030341c000340802100740401c444081001c1440410402817000c0000a0464800140014190454140000c0b0b52070b07020f500084640d040d080a8240c040306e03c502072441c2c0300780303580224045120b000c001004080d00340605601880c40c14042e43c1403a00e0700401d0009814000301a0043e0081400b03002041c4242202452240c41c2542c00170982c2c1c4c100703d00300b5500809003000c100e1030b030341490070901c100030103190306008550401c029201c19559088005000340a05e800e840e40b04070600b54490300103640204408280d0f42910000c008550780e0380c005aa45d0130103503a00a12100090000300841c18161014020160b90012801c1e0502c10040f40142241d103c000c0900c40b07182d40b41d0a200640c105481907490f0804151401c0000d01078a40b600d01502d80401030303e5031300d10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 5673047 1250 5671797 5671801
    0x8071a040512030403050106030503090f03160302060a020102070215120c0f0301030f02010905040f05010503010f1404020d0507050604030501050403030506040c020c041505060409050406140712050903040506040b031603060b0d0203 101
    0x42c2007001143d0045400c50004c100c84c946030718040307440f90301ca041080e1043c092401c4050461070046001c14084003560300b45900039281d54288003d80c1c0120000f981955402e0045c0409601d0303d02c030800364900007000072540e590450802080280300034001042100050203101d6030b080f21030080703c1c15207030800c000e0f045507034051004031280e0800c1d4209542050402402c4241c10303010b03820a5050b00c604030000c0c48903443e80c030301040403506a90586a86812a03901240140c1081c5140000e01c07809502500c1d407035500c4002040d0b8a5000da03001b100c680e9510000c20091580c10f100d0305802420488080c080d001c52004002d40c1c0d02d40c05118184100e5480c085140d03100700700503901e40100406444140c80341d9603131440100400c411542a66254184502d590181c80c06880c000e06c59512031301c51041c4944d00c04200402440000c5c1000d6044c8003c110200b61541c514010748001c02c04000300d1981c0c0d28080524050280000d0158000e040c00d0450030300c980f4041c08160390454584890050700c80d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 5674297 1250 5673047 5673079
    0x50f0f070e0a0b0406030504020a08010216080c01150815090703030909020309100c170c07020105041203020703020303070b070f360306090303090506100510030b0d1a0108071a0405 79
    0x182c0456800405116000100011081c3e059001b6601c62070084030b2210390190380d00b03101c42c280d10503003010408514801280d00d000900d950017810400090000000e00000052208140050386807c1080d0541c412848500c40348641b00d111940244a01e000d03011a40c60765802404010130341c00303107203075890300400000c000032010018840d029100c040c041c065002c0310b01018051106c040c4084030f416000200090b00c0d0030306407080f07c64140c0c1c180e40b03403490300340741110103103204103141d808074114040d9940c00005644e00304007030080720740181c124040740d04102001411180c00c24040c2000c0c07040b80440e401d0071142300c3d207840d0500250881c11440c01c0c2041990312040c0500354000802443c5090304a4083c554181c1c4010750080c4940300b20f0b01103440e02c0d245004950740c00d00c2901e520046c84170075140417501c6074008113014800546040c4c80840352303035103981004442080d0030845c218040010420344d032007003100000400244a40070801c1e0f284401038481e5100f240102c030b008020030f1540e18a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 5675547 1250 5674297 5674309
    0x4020c0307020a030b01080d0207050603060402070206040308030c041502060708070e0102010b060c0601031101050c0309040c03020702060c0d0806120c120307050f010f05070306151202090d050709050f0f070e 91
    0x11041d0b0040800d42d1054491600046100007809980260720404a1056165000065050568100512040c00c44d80e0b09010040a50f010480c120303040b12003884000700160101001d14002c3c03c40c0d126460f120303401e0440d040c0100c4454100c1104640c002805d0208450300720b04d60750303005482071619001d801c9901e40142e0150688035106034000d80005800850100046030050599200b40e008204e058008401124103001c0e480d441d807016042008030450328030700380e48002c00d00040b40c103002d401c1512640003e03519401a0040343c986402140207000300c907a10610141e4886001c5503103100c10242c406005d40d035004604000d40c0203448107030b040d1601650030400c0d60b0055030700404640006100d030914a003e00f0540807203403030150030000451240340c064096201551041d803041081141070407811103104002c2d0310369842c440d80c2008203140d17a4480d1100108414004c2004102d10f0b8078014006080300c0008003503005840207042070126541070202c0d11034001d04240307001d410703981c200c0b800102 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 5676797 1250 5675547 5675557
    0x303050405120a03020903071406030106030c17010303030e0c030d0e060c010f021b12031b030a060b0a050901090b0708030708040302010b0d0f0506060a0305030d1a09010305011d07031104020c03 85
    0x18410b01007119141990f05400400200c48144c0561b0f40a0303907204001c000d07800c55040300c5540683c0510042c40410f209900240455000b45050340c48490444c48001d5051404c4c0c00c241c4c0000d85034400400c607500c003040415212802036006001e140c40092000703001c56242203a091042000044c0403640c40d40940000004410034070b4115541c0500d5002290b91416580901ca0540611198801600224403d89120b0140a5607070030080c621400002c480c0e40c402411a180705940f000c000c50310740580d1015014902d80c50311125071b2198038200240c1002c24660004020500400c051400a07106100f070343d03002051030900d0019522186816405070026008040e084140e60380c1003400e004017600003a02d410301920a0300c4c056110341c2c0a1044d0280f46004c042c1491f4800c000c2003130041c15580c883c00710007801d015040c160001301c00004400c83e40c00e910070349007a03440e00e0010320b003a44148802005415000700401d600ba141d035807485d40c4852811485803281c0d41c00f18408248078003d1044030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 5678047 1250 5676797 5676823
    0x3071a040e0112050609030a0c0803090a050d0503180705030703020d0302150901060306060503030a0e10110a120207050613050904020d05010207030c11040c080103080a0c050f0609010b010c02010c0303050405 91
    0x4140c0d40c1c44003d043c800300441d003400d41d502d204140c0820041c0c1c00100c102c0355040481e6603910000280750b01e56189560000c1d00d8180140b16400307801011070014010017102540d42e6903260b6982c140300702c0c4c904094040071000752483c0c01410040200d550000f0b5803a040b260b05035a800c480080c03d0600368200590041001e154002d41d40821107602419846041a281306201c2089407503140c00501d603407405100c5852000c104241c3d4001034900e004040d54202c4040c5250041e138410344c10307000d10304001c20310808031058445076415106507034040c0044405450180d42c1d49062041910300a0401042446444e010b001c0180200d01551528582c80c0201c6c1c0d00040251b66a01040c58001c2030028815000d449000035480c20020500e1310340145a40c494442c2e480d40003690035501c0d400c00c2607100d0307c40b103018403000002d001c0010340300f031000c0d010b40e0001c0805003403d072400315111030175100128451030401110600b041e0040c1c1e080100c00f122240c05141c0058240ea036494054a0043c00940360 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 5679297 1250 5678047 5678069
    0xf02090a0f0302040f0203061c06020c01230106020a02100503090a020d0b0402040507090503030f0c160e07090806190507090306110702042003010501110a020d08090306090c03071a04 80
    0x42107800c1216548800c4038401e0360104902e02c05455a401240002e4078101da00c0840501b80048005132311103403210750703405190010f00d800d0f40c010b0003038211200d40c500c1c26200000700441c40b0020440e0802c85005114a0001c1c207806501030303000520102c00c8860304818010701001181c140801041070300012030340940002c850040e80c2c00c00c01a86c505c00c0b1000c0b8411801c14000640c0e080c0b1a102c0d01084038406002181404080302503c650b0740c0240183c0a07642c0302d0f00c1c4140800142c0521480300074648600b0784805420101002012240e440e00b0001c0d41e680854240403e078000e80f042c420001000c2d0000042035161810704480d852031680c03010b4079403810b0030b91000c0e0b461700c1d410060216a00c04c0303400700010b000d40801e0740d0380000610241da0700e141f818001041a9406403843c80003180003136042d100d28001550019800e2000158181c3d00107201044140950400304419500452420000d21310b64001c14000f075940c4001d80036403802c040c49104e0a0341e503a005242503401624210b045 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 5680547 1250 5679297 5679299
    0xc0803041b1d06030c0319050c0402130f120203030301090b0105070501090b070906090f05010309020105070501090c1a091e0a0e0a0507021207030804020603060a09050f0708010906060804060f02090a 87
    0x12002038145084000d1801c91035000f00c1e003286400102800b01500c00b60280c61600d031103d180703220700304a021b410b031042e00130b44000304000e50f2144010106204081003400d000d50501c00400701c810020341140181c81b09540c01440903a0307000060b281111940d0002050410700c0701e004079220701070103400502c0c0e5070900c140d0740104220200801e120713079400e9658030321103030f0b0f64001103501c26180d1154a800c5030b800b003c03d108a5100750880c168003801030401030b207401103903640d05003150001d440c01c0d10890310403142800100c0c180710f200d4055038101101070342054180d1001070071100b5071074400c1440b00718200d0740c000c442d21090300308001002485100760707444ca0102944c00c054481100d015005018280001105801c040c040e00e1403140c15035110040b50762294288900c550001e4403030b03075203d00c40e0f040020364902d19001d61403044880f040650a41d0a20640c050440c1d0f2060b000382c00b046081281c144201a8403948890740150030403008500c00b910020008002d02c12065086c0e042000400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 5681797 1250 5680547 5680559
    0x30b060f041d0d080903040605040317090303070c06030f050603030d09020111100615050301060207120303020d0507050d0b0f0f0d0f14150a050708070309050705031006030c090501060c0803041b 85
    0xe01c28002800b5860784c000c1d03a525000302e69224446c0e4096000440c900344002d1010078604003080c1243c4901c465034500c0c110b80c0100103032868104c05422904500711542c00e1000c0c581c54001c0c00302c82d40d00f8003418400c80c00e200c6d0009440740100341154004540c1c030b40441c000c0d6881201d100001300d034603005584800c0b5204000e14080e00140c0108000016103064684010344250304480c1243c0c0076074043e100c82410704841c54210b4440880c19020180c003408090300900c290312800d801401c19444d09980d801400781044151080605003510500418008075140d4940558544034220200c484200980741450100980b007000d440c003410f8080c0070000c0404d042000a14070001d002a600345420035621802030f541501d00c21111180004d0044021030341d024007a0300a482c1140c8a1016a011540c65002083c40c1028001030078100710744801d03082050190a8480c2c10240c8403c1600f84030740d60500801508500f8850300043c104900000050148a00c607502e0060345101d0400d01c100890307680c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 5683047 1250 5681797 5681803
    0x3110309010c110307020306040b0c0403150501051003060305100f020408010203010602061906080c0d15051005040b0301090c050d15060801021903050403090509090c040504060e011104030b060f041d 87
    0x40c0c0b02055008500e60340c6100d0010036210328550040050102e50340320703620039804d0074010b441342c507200788244408000078041c000030814100000c400040e040d0b1500c02002044580f441c10403060500c3e161086c0003151011400580c0c0c0003841802180b081d180d201c91900a2103643e1241d00170394404000440c100d940401c4031401a04200360901c3c00c000410501c1d0202d80c413a02ca0000b07070358040d003600c0c84142090034900702d0584c0199055a004991449410240c907411a05d80b110030900d40024041c6281500c40c203140c840d0150020800414940d40b42181c101041c050360b4801c90100424004014a2126078110151a0b88e81407203943e0342c0c1c580c00350203504103540c9020341c02e42ca07030300654805200b44141442540c240d0703615400d052409050001c03041000e031103113946d802041c001c00840c0d103c60082c01e02880c418100028660f2048032054210380000c8202e000c0744000300810008070316009200c50300050222a901d003d1000b602c00a00180341310144010b040c1d00d1009540544407003c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 5684297 1250 5683047 5683061
    0xb01020f0f061005060c0c0d0809040504050105010806070c08030c030901020418060f090903080a0509010f0908070b0709050d030e0105120106030504050d03110a030203040c0305060103230c1e010311030901 90
    0x81a08500158544c01001440d00400d1441c5017598800401c0d1843c0d4039000300651a1300b4041c542c000e00e0300038050045000d4500407a401c3e9a543c3d102c40041010f10000c000c0503910000702d142101151003c1e80e154009031102a12010f10b5403808004180f0180d000c0d4103e0b4010840807141c12079503c0062503580282c0700c03510601c0221200c40f900081c03075a09900070100c1050b456030314400c4554400322aa4000c081c00350600c01559610600c100e106c00052241d4600b1501441803261290498509450300f80c10003000d01041004c03c0b482001262035004c0c12800166060900c078003407104400048441d80141825109595807090001403101d40660015001d01d0090007581c036002044141542610860002d5110f0a2400c02c0028084c0b4841c0c2c1c040d64000d84a00e03081c4180316a261035071850100b0a800a1b20704542c81004801e00e80300051598880c0c0d120079001d4451418210001458101c00c085011103d0384107810301f42c2c0343c1e0711030761140071032280c0f00f0707a099207906007049514020405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 5685547 1250 5684297 5684311
    0x3030310060905030c06030f1305030a02010b03010b040c02150703090c0f06110a08030606071401060308030601090905070207050121060603020c070e010302090103080c100c020610050f090403030b01020f0f06 91
    0x10302c5020074641004501e8902e810405003815180d61541502c000d21100018444d4807408030342114080001c0c018802455020341640c004540d000201c1c04260850f1100803540c5c0c0b055160003440c4d0840e80d00450910303040c4038020340c8040140d41d0868260050034004da03000380852492a030102d8503080311404201650302a030b8035607545e2044403803600c0d900c0c0d403403036000382000d10b007840000c04524000005110044c07180d942207008145203a003080c00d40e0410381046840041c0402000b6055a01110b1742004080702c0d20144058108010b0280d103d442c0d50103038604204003a50382c450300074540ca602203042c000444041010690740c000060094000d65008041e5000c2d00070000b400c80754040c1d010b4143c0750010440070190340303181e688002580c00344010101a0203290440d130030300f4185201d198009131841c4c0113440540352200d41042d8030322035030b08410f1064400110302c3c4401d4542c0f40800341d210f0f600d810000344601c41040142d103040c0030702025070b801d4072840da80c6400c2520f000c22500d020f01c0c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 5686797 1250 5685547 5685557
    0x180303040507061103070c0b03090109020a0801090303050912030606030717040308040201200c0613030c060c060605010302030103030e040c020f1f0525050702010c020a090504050c03120403030806030c0303031006 93
    0x90b4107151340351203200701d00d0054500d090741002030106000701030040d60040340410000498103010307400320700c000c081540728000710b0f552540704105054250140660200034003014020f025252110b2090340d00001d40501c1c00b508010000618140c0207880050307803203460940911840c80c25180040040c9000c0b03a080b40041d41004c800200c1c003c007462003c440481ea0009082c0707100f04407040c806aa01702014000b00703c0080500080800d20700907108000c0c1c511075a600800b6119410700f1002d0300c045a2203030303040610410041002c241d01900940010404650224580d40d1400d03040b444c0c0502e100141640d8024410b403580010456220a00311007041c0c1750034450350b902d201c00c1e944150340d00b0040c1c003410280c1801c10b42032284908000c041c4540705040021080500783c011601c023941c2d075080340050307995410600c014000104142c40c4d81d510700710300030282ca0781c0c04034851402d8041c900c001003d1040b1040403c00715901400381c0c440c0c7c15409002c4944915103000c40720700e21060f610494021031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 5688047 1250 5686797 5686817
    0x2061207030e01021303080904110f070302010b010203070b0a0203091006060f031505180a0f02030a0603020906030c01091a070f030306050117061e04020702040905100b0103060807090518030304050706 88
    0x24418001d0300c052400f5030705e070507146a155865070343c00c41d803107804502d61040c0e41e003004006100c01200500502003480803070383e172150304610700682100c00850784a41550b00500a400028920038902680084101005602c17900c5004d69035103425002030500c4100c5080c000f000c5121076102d070301d000003030300f840da0280420000c10b24a6510300403280281c1d60000d401c00302060b644000c81610540060102000080300090030303044000300e801c10f035030b1610b0ba644c40710010002d51805030801608035201701d0151000c43c1c4d1010018002c1030701032043e0559440702408883c090520001510311140d003000d5007801042d407900d0014010100c41c06440c2c04185a4810201a005c801c1d0829204250191180011080c5103820310914004806072a600580801021005072a5402000b030803610030070003003100361003038000442991071640d4068105840c085c010800300c40b002801a0455000100004036034650005480c030144018506c00c2840c4000810f01c07042000004012048800507585c1e0880c070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 5689297 1250 5688047 5688071
    0x20105150a1503110c0f060105010305070302181005040302040f0605030106060206160305040f08070c0906050607170f04050603010b0301030201020709091104150f0602100b061c0c0c0206120703 85
    0x140781903010302000c2d94001188020054001c0d0b00468018032404682402c003950880e669180c02034034483e03031103540c10440040115580600070305802c603186003425410014446c01044142451001c854070410300a410814000d000d00103e4002e0758000d4020b0061000c1110f2500181000c0d2096600a610b00800040e40030310124520b806500e0107503981d20881071141c0110054100500140da0080040e0780d1000000d00344030041540d41c0c4501d60101c03442d49032100742c2044610383d0303002c18042c500400030707540040c400c12a039020380c42d800001540c8654198004003840c0c00b568110b02e41190000001280e5200364002070350485c0e10076401c407004a51504114010343d000180010f007501c0c082403010301c4910b801c1e00300c00350309e04090301216499540c44044050468003644080e0240c0c02c1801d01040e80c2c0f0140c000c0c5883c1c1c10b0280c070b141c2c0c80c040301c2c080304450401002c410b000c20b15517184c6c1d500c02c000f40b080c0a05c50b010b907002000c180d194959180c410380320440640e80f50000c41d181a000342d4403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 5690547 1250 5689297 5689309
    0x30603100504020102030d0207050115080f0105070908030702010c0606120302030d060f0f0b030601030e1009031115070807020c03010603030f02061315020702010c0b1510020304080d1b0b0702010515 87
    0x102c0e40d8103034040c5040c0210890080e010350060030040794103540302c1c001c400040e4450210a801804d0010050880000d851040c9003101c50250030141000754280003882018000012280760550a20b410004075140341020350042606810440054200c100341400349030340040501203914010000700003213559090b00d004e114409201700c05000c04182003c0000d034514002459000006040100307a04515010860908040c0781011000d2035982452034141680301d0aa5459442071800401880c60b001c0b860700c0b40800020400410404d01c6800240728610901010b0308007000500240449501c2c0d02c0d02402940c8007201d1800140f1500d000039081b0107619890380d07545900b007000d06600c1132124111802a60240c401a0f051242d0301d01c101000560a5840901c101e0701900e001c0010058501002074000c074800004045602c144001c0c00500d10101e06103900800c1402c0821410666520001510088420150081d40414104208642c040d04058854010114031000d8410f469042183c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 5691797 1250 5690547 5690551
    0x415020c031002090f0405010b0d0b03060c0706020304020a08030406020312060316050f0d0c030503120c070308010501030504020d0204090501060e0702030406020606060307031103070203070b0708040b0402010c020109090c0201020306031005 105
    0x1906600001d140320392005607500505041c5400f03000145d41c0c0d0300c190080380c1a00d000303074014060880c0c0080e070340d1601c029034469a40151000c030050030582c20801c0004125029138000030703007410381c000f000c04d045684403400480107200b0030b001e03a0303211655404040d440ea0810309400510306d80342d000040d981c0c41c0120f00c0e611400924100001450300b41414030a4110520685a8002c00c1c0075000c039000c682010008001944584000d40c2d5a1710384200340310000002810311035440d40148161000260044c0f500c5040d01d40c00e02e00060a07a40d2400042c1194044500c003075041440c00110905000c01901b0400503038001003280300c0f00d52070703101c0200d0307580c440d6201da070f03005800c0f18002c61241c1c50440700443d000359107460003050700707a02c0301d410300c440b030340309483c00005a480010080b0811204061180d800340302c40c24081da80c2e1810307484540f207283c0001c000074104404408036504684c0a031031080043c220b0518104400b403428000617000398003d5416a10074030440c418800d042d1814000d41d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 5693047 1250 5691797 5691799
    0xe04030e041107061d03040b0d0b010801030f06050c0403061109030c010504081203090709230f0f0403030c0212040906050f03160b03070c020409030f03050a0b010f0f020705030703080415020c 84
    0x2d261821940360000108407202c10360105c402211500c0004000800c00340000e00101c104043e03035840306440000840d020000c6041c10301075620010404a0011070007413000c1e40d040040410581c0d20415004040d10854000070801403400e410b00c010309503090080e0a465005504441c80b00301020015182801580301d07110040d40140602100e4500f40c601454200011500b03c03901262220114425200c100104203c446c0044820f4607500d0800c0e04a141c0203121001010700c182440743c5458180320700180098281516200391502041c0300300f1800c0c014070100c04042c5d40b916252480d0101503d441c2c880c00d0f01c1140d2107c851116443c002c18083d0780c4000b00e034494225907152107032810842d00010400414894840c6941c000b5841c1d90140c220700901c82d0395108003d00c01d620b00034003264009002c004051780382103460003113640c100c9d441c010b10003958204101d031a40a110101c3c646000e581180b50140140400002000550030140090711440006400360440b440d5080f641c03491003407465 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 5694297 1250 5693047 5693081
    0x6020a080115030501030512090a05060406050c060709030213020a0203090406030b010513020906030f06010c080d0c030608030c0703020402030a020d09050703020f03150f0703060e07020703030e01050c100b03010608070e04030e04 100
    0x242c2c0b08c0c2ca1041c020304448002401880805035900c00113000d5801c154451004682c0000703004080c840306002070b5500040c541882c0c061203040d600071445400b080d010a580c420382c00241c20040f28000c005030382500303000034000d0190300d440c1e1800c440502028480c0758041c1e04842002980040c03107009440c0382d110003619850542e55a0300c10454180300141109052010300351840e00428040001040d044d6121900400c1c5203003407010080403140316900070f0155030814004580940340204031002107a4040310096283d84444035504024480c101c20800c0c0c0c42c2c6009145400c0001c00303c0e400d0126802151480100000c0c5402c0c19250500c03040c03220122640700d4001800407510014003600500180380020b4400e80f50000301c20342c1c20303080d80c011015a000c80c1d0108109680560428007540003840d01e41d050043c41a510342d611084204c4d500c0080b51100610940c54900354001c0006000c0d5108030703074003290740f4202c0c201042c40c01d50741a40000d0810250400c6420603000d1052014408010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 5695547 1250 5694297 5694313
    0xe0306012c10080303040303060e0105090106170603010209030106030c1a0304020a030b07030b120a0c091a0603040515240301090804051201060522060f0b091c06020a0801150305010305 81
    0x10399425600700808030803000c07000110205003500e0070000340d84994401e850005040d804c01c107a183c03880905a00c41c074420001000180542e59100487d401081d03003042102c0d280362516400240a4010809010303015840c10000009000c0050a141c0440c0c1038005000d041206404601203035100031900a5003090011404200090f0a0705071190b016803103180000d400340c100e600080b0624400d000c0c0c084290b1052101e401848440c403030142c020441241e04006161040c3c9044030485804000c1a203d01c00120008041c00030920001034a42d20004004a0324a400c0c60808128928080d024001d20412104401b0a080c140f140c4401c1c9a0400e41b40c5040a103803900b0000000d1900548074030300e5488071800542502d801c0c0070134054421480c0400540260110300c8001c4400c40ea0144001100030702040010300b01c401c1c212404450281d4180c42c0c154440381d21018603114040004041c148000b41142039254803024480c140c4035aa8110921000303001c1c811402d5401c20b000150058101084e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 5696797 1250 5695547 5695619
    0x6120b0406020403060207060207060506040504021e0a08010e0303010608010b04030c0302040c030209040e01061406030f04030804030903080313030f03021207030b030f03160204050105030d020304060503070314070e030601 97
    0x20429921900c284000341c40d207500c9a8502c4140c3c1c0208100b128525004580c0740100060707402119880b403400d07030381008545442d800003444000c01c1c04803881c2c180e800c00c11441c03040d01d0b82d01000000c5d0400d80000c0c0007066884140d665a548244282c0300041c003e0f00c0003081e0f500801301258203c0b500491124912811a0200001094045112400d1681c00c00260110f0b8581d4040c0c4100c0800c1a4000180c00340303094444920915407000503881401c00f04200044101010403a40e000768051402010703039a90751038241c490f2012504003402d500b034088204080900a802d04208080c8651303901c1600491284040e01a8090251204001414a4009114248a54003002c00040010100c49a880e041d184080c110392040047c0d0b08203980d00005542581403030b028460043c0402c2c2c0060290b0308201c2c0000303440b40120300a00040040002c0800d01180c803e4101c2102d1241060701e500303540c2400f144c060320000014a00c64044c0c02140c0000868212180c8810300300340e0707500460032600800c08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 5698047 1250 5696797 5696813
    0x11b020a0b060409050a0f050606010306080a060506121005040c05060a02060a0506010909090602090a08030a0206040b090a02120604030807050406050d0f060306111c050402011e020c030f0d030f0612 87
    0x10b01d0250440c0d41c52455a01240d410040e00c1c6540c0e015035a00c0540703204a0034a40d00345a00148420306050801c401000030718000144501703020b400c01d0001883d5100d03000041c0030f50726844a075a05510410a2a00095095903c101c0c061232040d441641266500c0c41400418080c60218030096004500090119003c0d0340100b07610030014501000070903110308038202207032601c00d005c1c2c400a078081380459280c202050501c018160034801103003085890302c00213640d000018801488034402c1c0011549581040000b4516030b40c0c000d12020812040c3c40c845a629001140d050380003840d0003001c95800c902610448040c0c400ba42c2d190340c5072182c0e507810840506907001c0c000040326900c03a4008040b80c160300c00c0c01d40c0388604c00e040035941c150700e43c0141e00504540030960943e91408050100503a0000354503a402081081d5448000482c450140e0820440c090030302e400d8040c142d0f149445070f0010802256000325a00c04124007486166004110307007050085c1001701d94010461404503a040b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 5699297 1250 5698047 5698051
    0x402011715040c03020a02060a0603080901120e070303030203070f0801050306070c0f05030301060201020c070806010b0d1a100206060102010c020a0b040f0c1701060603050604090c0b030603070302040e0601030203011b020a0b 98
    0xa07070407000300801c41002c10201c030029400d050000340e0210364441d45960501080c0c1d001071000105010035030039619801050301c00c5034819414090391480c00d920901d01c2c0d0b0046055034281d031060f14805503881c203014010b90710131103400300020f01c0031a244c2026401004541c1c10794a000d00217150a030385906059031350340e200714001d481740b803c00c5d0040700006100700700135030183c40154000740e00d6075900600c1e1483d040043c3c020514540041c0018001500000b00703803041c200248a01140400c90b086460184071a52165140c2000b18a40d801c1030140d00003d0f83d501620086c0d00030040c892031000301702c1e00c0c0d03680c00d00000d003801044808100400e8901d4004402c0034010f03019415400d9442d1146c0c4401c904007660160350741d45031801081010340601c00c469201500381d809002c80b05907990b4480c52882d0b00d010b141d915400110218513030351810032071b54014560107007003044614030b035410a9940c0d02003440124400d42c01c0c58160362040c0003000a0711405407150300200601c0e552590b4004003400c2c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 5700547 1250 5699297 5699311
    0x3040b0a02030c07140a0b0609010b030c090103110c0a020a05040e06010308090414010806040303050c09010206040f030207050d0803060901060908060a05040302160b0a090503030f1b03090612150904020117 90
    0x1041c4841310119a00036202c80003400840d0080901181e83d14041481c8200145564841c110708030040080c8201e031b5040703076440a01a04c4050f595a501030040e0001c103400c080c01141c88001140c40e1418103000206a600302d0700807120007403e2a034510400095030b0007c0b403806038079044070004000140c1080040d05032a4070060002c14200c4085c1c0c070303408a050003640301a08a9024409100a0580601c112600190280145860201c00e900040d54600000c1e02c014042050103d000c802e042c400d000d1f203c007400006100000e2103c890800c3d00c0542c2054403201d1046035018000526240944194030844511902808459544242620080600a00543c158020395142103006500c5011000280c10b602700b80d00c0c2c49104640c80200040c410740c10090181d4000c00c00c40d01c9582d81d040581d40400003e1103540328042080c401070707086010b56203041c0e4010001203000c43c801180709266910410311201c140549034a4034040205038103041d00d0190100e503145d220000d43d041c03804000b41d03001300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 5701797 1250 5700547 5700571
    0x105030c0904090b0103031107050901030201051c021918050102070308070501060902120a050a0501030213020f0412050f1006030309030b090c030f010c020c0105070515060112090b0604060b03040b0a0203 89
    0x5404000304050b43c000c4002283c210103850014810107400541c0b00540d44003400040c0340941c10080800c0d0705410600029040c041c0201c1c410000c0e8209840740ea0801d010103e05548400d241c0c028401010f4040c821000801d0081d00752002031207103244003008591050f8000d2a90381c0c07840d1100202c551050409580c55500e403003001c240c8004a000420301c40400b092151010300d030490820301140c1016041814041c100001003001d40e980d03c0600441e11800200142c2d44c1400c1d80c05006940708683c06400b44010280e401d50900401091049042c845082a51100e900031045079044030002e020080215030340c030300b061000c11030710030007103500942c03c008075255980d542c40024506948031620b0348a6a4607000d00341c42d42035062080310116102803c025040a405640d580d4403008810001c40c10300b84120000345140c1e1107499410321005140c00100500640d904108603912001c5a02d00c0c0201d0138000c0000f444c6000a0480784542e410164802e4681c4403130920a0195101424400101c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 5703047 1250 5701797 5701807
    0x30c120714040303080a060b0306010206070f0302070c15090b160f0c08060a0506030c120a020409021503070309051c050a0f03020d1401030506012103080601020a06050117010b060406020c0105030c 86
    0x840404000c10156001c2d8603150755038a0280306c03c8040d5035880c0c10040414900340305009190360001013094002c3c803141407801c00ca40d00d8060440080c0104800030740b80d00d08420b400501a0601c40f40c4c940152215036a20780c07416200d01080980c2d209070381c4822100e00b1684612404a61000d2640e42081d2180011822040c0c0d1a82c0003850301c60191050140035507540c0c1480030314a0300300b04191883d441600d02c0c0f80c041405185198890070002c9000e40100d0f1a02ca00004540e0744070304000d5807800d120100c0d6180e0614103001001010510b10844103845100c4070040310310308041018044e000e607582c03024640195108112100203194030680f09068081c089240220300d94092001880c9541c680c40c1c1842d891814500d29118069000031074810740072000c2070784090008007103800141c05091900d0300e5228540100d24246007903402920307241c41c0034008200c501da403916200e001243c85009000303120460f0100400c5205034400c03c00981c2c00520000441d501030f00c0074680c0b01444510140c144 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 5704297 1250 5703047 5703077
    0x80904060e09030a031406010e01080a060308030c0c0d02060124090513140a020f030606070c05130504060e0c010f030b0307080d030209010f0302030c040302040203040203010902040603060b011202030c1207 90
    0x142c48682c03603500b0206200c60920303498400d0f14950003807415881c1c02410701c807002a0540d146032107038904200100000440310803981c0c109200031680101100c0d42e078038144120302c090744c105220090040c000c0d191408ca016200040c0c06043c0d85403410b0688101140c84400a40c41c480c101e0a501030240100c0300042940c0da403d0382000740340300d00801060524900c001c618142038001e015168070780c81805201140701b50f0b00c0669034010740c26240a075441e156810110817502e450340c85964840b061a444a1441c0c8254000c5400f580c4558030074400428100c00594891060058160000c0c11880e64039002510907086484030b004003805070ba00554580b11202d003010035588170400440d8000030343c2c000235640030701c104014a81d0740c58114258188a41c01c04120311462001034825600400400d040d50b134298041c3c214070360300030400c1040f60703543d02d01130025005000601c0d011030700d070980002c0c0100c200c3c002c0704d214110507401c1d540741030030300c1c19448403503540502510100f0580c0401c507141 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 5705547 1250 5704297 5704319
    0x2010c020d081e16020126070306030209011202010c060b010903080c03070b01060903110402090604120b01080706030902090610050906041806090207020102060412110706030906051006020a08090406 87
    0x194010302c150342e501c444000300008500440905207400940030000902c1d52041000f004900d82c0c2c0c2413a120310111100300d00702d0b0244031200300c403100240b940014003a66035055032000381200d200741d844a003160781e201c003c0601052903d00c043e000caa0203440c03000c00564544d0009030310400504101440f15101d40f0751840329044141e03550210380c00091000103001c1002c03241c41c0100308601d4045e907140d0942c1c0c0d03015203980300040d030f80340100d40118041203650b4488041c0c5000d401d05401001c00901c1904008050140c2880b4a8540c0d0161010110742d0394401c1c05459081ca8000d04812040c1e11110188030140d50514441340802006000c441c046540d03603801400180410310080c29890080b003c000f04845456205000c881d2042190300c0c0181d8000c01e125900a0b040b49002c21000d03000c40081d0b4070744075001c0050b2103a00900300003003002d58040d404a40054002d00040080780c1d02c0c0001901c80e04214002c0c04051380c0424081400101c03a20014180360101800104020790342d401a005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 5706797 1250 5705547 5705569
    0x60603070c051c03091505060a0303030504030201020912011406100e0d080405060304030c050601050303040609180e0f100513020d02090702100204060921030504050609030703150203100e15040902010c02 89
    0x800030740c55108007406c0c0186460ba02d8041001c20000300030301e060010010780409942d01c001011325450314001018503000303505407201000054000310302c40e4105c0010900802c20606c031030541c040c13200042007103030403c000400e244001c240c41d05445100d00c90100180c03400c4080044488000410000c1820f4481ea405140031358402d4a42003840d8809103441800c00f00141c0266020394030500c41006060390025002048444065007130001c000c0f906828005007200c0b461058051081905803503002000040103c001000c02404010076180c10110082c81104400041d5101c54001a0b0300d016190a0601d1030304050345004445810402000745000d0340c200c1d0b800500481c038092010842d02d009000910308a19482041880c0440955405003060059009090140c4070214124003a602c0800240014542110142c1c0c5c1d100c645d601c20b400658001c65041c0503020700290001901c101c0020300174010002c44180400100b004014800204203c1c40141c0c10000a4030301c200147c1c413801a800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 5708047 1250 5706797 5706853
    0x5010204060c0209070f020c090703090b04050d030f090203030d051021030809010902010c0b100302030102180114130501030b0a050603180d0c1e060905030d0b0406050603060603070c05 81
    0x95881d2002d40100031421034018004824825480c1c007664005030301285558040d80d04031500f4550791900749084004180d50103006284031030b104280810710000041d07201e03050405540c18081000d00441450030b492203040000d42581c01403000c10201c04640d0001c650121507030328643c44855403000801e150184d00ca490041818019040d001411747c03000c0354039401801180240594541c0e540001c4c180b41c0e1444010f00f6400401c00400c008d040f84607459802140c0040007551079017500f031100ea024841125603180469040300100d541c42ca440826030350724840440c007040003940341c078005502401c0300c5080f039070b40040403520120306070340e13400701541c083d4610296402c5940c0c00c2e121000d2518800400910500800d10303003500015a02c1624100e00110051941c1151009441c01c80302030040c04100803d240030101d80303646004001c0d131103100801070450b01840090703903c0050061500c0155030541e00031744100001280c0c54012403c02c140310344a4001c46010b07240054804040d08016183c01c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 5709297 1250 5708047 5708057
    0xe150403020103061a1803071703030108010510050303040b030907030c030501020d0b040e0a0222020307080f010609030c120203100e0a0b010e0108030901270e0702010e0c030303220501020406 84
    0x18401d550b498425200a006a54a41c4e07015210b140e031080c00714040c51309010400581403a01010b20b460501052000344001c6814210410500340559160b0308240103105941d803804000405070f140803c181c208130761029000e90716180c20b1030100103079079000400050061080c8076002002a4183e03a901e070082d4012400141c66441614240050355445013401e4469030911903441641c0d40086202e00390103134101c0e003c40c00501007541828860b02031040c030a031198408401c10040503003044210b4407482c08025040303074036070300c451041d5032055880c040601031240b06072040c840c1d0a54200c104001a0000b0304480c64400000001010b0365040415903446400811441040200c0500d03a18050f2295a020b50140d6051015096680c000c1c410440d04003c00071810b00d04a007407500d030b14071040c40008034100071240c41d50401c0c401e0b850181c0d00e102c0150f00c0c045901004901c04076400c199030b040180034601e940c5591411031400e11804c100501d4891503c071000c000a282440207100800382c0d81c541c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 5710547 1250 5709297 5709299
    0x5061012201207020109120e0a03020402070507060224130206090d0c080706051602010305220c030308070c0314030606040b030f010f05010504060207030b041106030403020f0715080c0a0e1504 84
    0x20100102c5000c0d06030b01c250381c180107a1000045c402a0b40c1150a4960301c2d040c50250144400195154115031001e90400c0c40000c0900c140034021a035070041c0c41c82c0303400321030440c080c00410280c0c00341402d125200004040c0c01056103511403215030089d20b8001003400c4d0030421404000754141c1d4038043c1c21100c40051410030089800140078080080040d81000d81c100f1460b20848500d0400c2403400070304140da20400180c0d64600692500c4601e1003950143c20f204900d45045900324003640415008210b80c0000240082c1c030078002511216815965140460244800143e840c0c102400b0705034811814400030400841403800356200c2c40030f03480ca1032030551404942c2c4c0035140664001c030b1304011040006010340c50700081d0341c6080b682d00840c500b210f6500ca0800f8072041e0341200c10310394448000014481419400290100d042030090191140c0355603445142c01550320030241d58000c2440360b07002488402940001e4070162440f802c003280003014800c00581c04900080c00d01805110120f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 5711797 1250 5710547 5710567
    0x204140a0506010f020706210912020a0303110304020609040903050f0a02010501180c020d050d0216050309040b120c0103050a0b120703060c0203040b0d0903030902030601090608010506040506101220 87
    0x1301881013081c0070300140190a0503c00010240070500008489182400b03082d40e00c03c403c00c0d0710882009401c00c0802c00301811342e1400a484804c00a000c0e80028244882d41200b80400c008403070207550700410b00c502c1c060b00707130040c00b0240c00c003404140c0038030105220600558402100070000490182e00000c0c40790b04005000c41c408141004c040d00052818194a9107142c00080c094014039142c20580d0303e40142141c400068428203a9140000042d0800c11040009c004050418050704840510601c0d8111042c04880300080a890100368003c85022211b54082d6121170380140071040040f8040c1010f1021448404200d4008100365210300070400a01072580306080303500815201561405151002403419406510b42c040c0420b0764520000003018003079803052201a0340601038034001c3d0303501d840610040040c0d2003466260f500b0040041d0442c42c1510450341b040000408d41c000d5101c440d0001c84160a44590501195649099a200ca900107444444003131614a071b400e5500c5c80604 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 5713047 1250 5711797 5711807
    0x20c0c010306120309030b040507050d0309050f031b0607030903050a0309060807020105091b0310060b030a1503050303010603020c0708060c03060a05030a0201080105091e01090e010c08040c03060203040204140a050601 95
    0x540030f0004800301d0a651000268089030b0701048a40100041c03420f5240c9082281c20320f0055405a58080349003401201059044450801110011501040002c031154207154460040040303400c0302c4401c01d00303c2c0301c1c24504480078280c0035019181c05500c150716a543e107031a10f02c83c903070705402040c80020204182548031a426501c9070841c8001c1c0500d0411040c15035541c01203801c5a03280e2a40286030941e103890802a544000001100034044155140900c480350b6005035103004042c1e0070328042c2c0b00000c602200d5079040303a50040046240d40c0c82d10108070029040340010303425500600a0002d1910342c100300c124001c070040012155242000401c00410302e000d94401c1d40030760001082000540c0e00036079094110b43e400e031421502540c8a042400d03054000c400c0e500c02100c180d03070003c18244019444007800c0c0c49680b0007041180000a41605d21407000ca500901001c492803007400050041c0c0c014540291010b040400c0c000324803041e00c0350600c1704582c000c850603030f55000c0069035039004e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 5714297 1250 5713047 5713049
    0x90206040803040905011e15050d02070f0b0106020102040311120f07030302070504051602100b010302040503070305070e090f0a03030216020402030109020d0b010504060c020f12030f04030c05090105011205040203010f020c0c010306 101
    0xa800d480d105805c11202c0311840214402d00c0c2000323a040051401e510b000700304584448940c1c050440d40c0d0f5807180741001504600c2182518039a101d5400800c100e4014401c07582603c1e008810018030000d8001000181c01c0518203070707405030081074003d0114600403c4400095880794014141c1603040109100854500034000e1440b100c0b6400f00240294010440343c200364031209010a5004000f00140d001c0d118a5008980504c60390800000348040480c041c0c0940d40081d030140804c0e10b032800c8030341c0c0c4e42061713412006154101d0141c05001901070b42c01400c1240000d90071203420b0700039070006002c0303070026800260456000625903003002e0130361003030941c2d070242401c0141c181410b01d4002848000c0c02107009004117426650031407142d41e6180d402e0005040c0004990703071240d824400b5007c0350400d20040b21480942c4802282ca07283c810541e5044c0c40040e50340e025080010110a8040d04016100780e0701b5541e1054004140301503800101510040d02c0003d00c500180100010211a06 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 5715547 1250 5714297 5714309
    0x1050708090d050a0e01050304020406080f0c030f0703020a1806090203010b09030f060f01090902040207060c0c02210c06030403110a0c06170105090c030709090203190501060206040b04120309020604080304090501 93
    0x41003041058050b01702c00801000e11082c40c2043d240d65891010400500e04d030b421606c0b041c444d0103031400c0014400a40065030b13100640548072000c1e1600e6955958541c9400000d511030405139043c424028004096800344c0507680004c5251640c61041c0c0080307a00a80245049003000120020035040402070700351109042c034010003071490501d03441c0801e04018001d40080702c3c2c65106e10b000395070b5160140d603100e07508500c0070400840c0c03410000d4440c94407280c080703011760803501c04000f40c9401c600f8240d807000c500c00b001d080b1183c82c2904106a51380024001c030240912141c4400003a10100b00c0414090310920418421904001c400f07402412910309801501d0700d481d00500013522141c0c42d098000740300d116071540303945039070206a90002c1030343c004400b064808000c020031121194200c01e80788504138004c112a989032076049840d458201e90146c00480e01001045c002811124003030b5021a0526000803180c10503800507a03164001d41c0a15010b62021505101906142c4601030051007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 5716797 1250 5715547 5715557
    0xd0c090503060708070e01050903010510050405010b03040b0412110f0604020a090204060212090307080a0b04060f050702030304151503030305040506011418130b0108030c0d020c010203040909050f01050708090d 92
    0x94910f00040c0507800007003410041141d81320b10711810b03034026015600c10707000c010b000b4442031a1004c1088100c201c24401c50f445141007000001c2d441070941c04890040c2c1e00540802d286948503250210600c8001d2081e0741042860072a04481c0c0200340310501c511240c403c09048039050500403c00c500310150003110314a44100000c10003190001054201d030001d031034016032662907800000e07003401c10030b81c068040750141115403020002c0c8a96907520592040d10104440c1c0100c1201c3d00c01c8075002c40714000540d0040000c03901007000040c0c1912404030458001c60103164148440d110680285d000304c011a4840c820b00042080500c0500c0c090030088407039110203400c00b4000744081840b40c42481041c0c0040020444078418480e25101032074000c0f10710503480d659180c8040d40c0307500803c1c2240c0640512075100005074404078460054500582c001d41c01c09003414003810003407041080444981c8a6260786d18190701c4280034691081150341c03034140e90f40c030307101003958103000c4c0c01060326003002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 5718047 1250 5716797 5716801
    0x40e010501060903170706020406090602010e01050106050912010e01110c010e0606030a021002070806101503050609011707050d030201050f010b07030801030b060310110405030c04110d090312020d0c09050306 91
    0x3d500007850011613400c100060700340200b10f072082c1c441e4418010060042c0c0e00004010800b160090305601c11101d255000300504040c40c0281c5080390b400307020310000a00d0410004130146030201b012035562020030000151100d40184850071609490310341c075411880402c10009024003813069004400d03210300075085074500400000d80b03444100400074425a401c10b15143c1c824400c1101d0005405950704807540c40c00c0507202c1240c2600305201e0841442401d00c8001e03059440785c05000e00444000e040345c40603908010718040c00c001090300caa01d0600c51014005060359509003401e407902d0090b000001d840c02c0c907040c0c038140d5000c140c105254490007005207000096014200604581e00081a003855842d5200000c0c1440d03100484500c041d03041c450121014201c0c03200520803070b0801c8045030000c001c2841484259020000440d21003d000e0003d114407107801d410000e1064441d1420602100c640c1104508980181c81d0381000c0590341e148500c0200d03003045040010341002c4000b48006c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 5719297 1250 5718047 5718059
    0x3050601110f030306010503040503070606080a06110909010302120a020405010306061d0112080a0905030a03020d0e03010b0303040504090f020604090e0c010e0f01030903020c060c15060105070506040803100b030109050402040e010501 102
    0xc1e00c4051701d101c0c10080c000000500b031000c18402d03203900c1035000009100d250f40d190344c50760b0380d080280000e0714054034240009140d91070103000c807001c0050250101d180c5a20350f40070050850b0765540070342407a008003010900140e50b1449028060b501c10701c0b0000b40f45040c008540c1c0d401c1c40720004150130041346c600502ca0440078203242420a0f50091031190390300303480e51049402d0540303030380120f0301441a00341e40010142c002c100000080015035868003141001820107081c0c50400d035209806030030401050041c3c1c100741d0440f041c0e1501174140e100300ac0780300f0f502254a80d805548100a016540c044c0000300d120140015440c0410905c1c03c1403078200384200040480b4200210b00c0e051503920088001018003d10181d00d5540c00140b141e515540011441340e00c9501c1226010854120714000580540c042c0781601c0d81d01d90800014076070303640c4540e21040b04c0d60001e0411810101c140c08009110b141c000001c1d4007811405402084d2810f0a10601042c0d401d445200601030341003070010301c45 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 5720547 1250 5719297 5719303
    0x60403080a0219120c09060c061a040c030504050606090114040e011503050f0106090c05040b0304030c05121b030403030804081305030703080c062503020706021201060215130c090c02190303050601110f 88
    0x1459000100010ae06200303501c1100070710f0848203810f400c6410442802240e5816500080c80b03140510181c80c101d41d9100104020b2a078240900722440f0054000d041850400f0341c03103031707400215040000a010614000070b100704109544122040d901600388505901c100f80261030080a1600e4240082c01940402030154061406042070200380400010300b418811311800820f2604a829510001140390310f1485943c004009440f0b900c201c0410303011050030000480301201d4141da50a80c1a0302c03555a41007a9500803085040d11002480c804101540c0a000d8440214401c0d0300c8241d0343c9412800e4582004e100400c030040403440c47d01c800800304800300340d201c0c50400c60301e00103075a0a103520b0a000203004552a403040f13481080004076586400003450703045084062081882c99440c42d0680080c42142cbc003000b0120000c40c0c00070000b0041a030841c10294100c0e0047e43c04291401c100808503100c01d14094002070703211401c0c8850707960800200201d01c01100043c6c03200000000c6203642d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 5721797 1250 5720547 5720567
    0x30307030f05070c030803010f0509060904020d030908030c0601090c02010b0a090b03120d05010e0f040c0905060604031b0603050108010606081609080f0c010806010c0302060403080a0219120c0906 86
    0x309102a081c05046524030907800ca840c499030000114004680340d04110070341c1c0d0030034019001c0c02c0180041c041101d2a200e09418070868005000003400e03a0b5035424403500c450b10007011802c1c408411030114040300b050018041e15101400107200643c507200c0c030300c401c1d42c4c81c491000c010359140880741da41a4554002c82c5042c0c440e9000b0204100c422800820701c0d024140b0015141a03d001c50040301d60305042d008075040340c402201c140f079181c0321054034404c024810303103000780038182c41c0b042001001c282d0781040d54404802024281015506d886441031100a03100c8207506000c0c1c0c90f000d100d05074051040c24090003007403000300f00c40c5083c004060980b00b00a4086441a8544c081c0300e40804d204111000107001c0c6035042d1003410644903007a80e950440a8503081c00300703a144002a1255100e560348000d020740590042c089074230b803900c050b10421400b41100628035000c100c01c000404640389200c41710341044e512651880e071901c2c0340204507010140300c1010484041c2c81040034070b034402c0405d2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 5723047 1250 5721797 5721803
    0x2030a11030d060b04031109070504030615030b04030c0210180608090f030a0f02010501060e0f010e0d02040c020a0302060603010203090c090703020c06040803060f1f120e0105010806061201050105030307 89
    0x4180180304811440c41c01011440c0b510300d82481004510181306001600460b0f2190025800c1c0c1c10300c6a04022400c002201c1c9100091801d0000f0004200503810171450085072041e030014460726526900040c031400c403000ea000c10781e000364090840c2848050000d16449a140c03896151010721600d1b481e6011900c6600c0401400340c000c41c01207407050000c0d5040903004412240c2c1c41c0c021000103410f05901a8880002d0352a080000601e80c0c0920202142800c0051000902ca444100196900c0314107483c001c0d04001001c03080ca0041e00d4070b2061038031640007600208500c2449250091a04600409283c003a034014404c1c0020800c0010b58a16961012a140d0003640d480120480007802100f0100303901e4810380742880300b4000240c00450007424165501c4000900701810700000d0b050349500e50001c1d848052056000310310951080e0340f1030300c1c03199000c2956500340c04400c1c2500c80a0f000005182c024105000803858031110200c260600c0e14000c0c0403540c074010000c2e482e40100c0700c0c05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 5724297 1250 5723047 5723057
    0xf0c090601030c020708030d050106020f0303040201050702040225050303013201030b010c050601141509130b0a03060e1b1008040209131202070312050702030303061207050d050d0801051002030a 85
    0x180e0b00f030500a11030346003e81401001c8079140c1f010640d0b007102802e003c0c40303000051300800001c48003001020040340d100716010386495190800b130341c0c24400250700c038901c6008442140c0ca4aa508003000c0d10742290b103079024000450300e0354101001d96400004417008541400c031603007541c2e081041317801c0d0741030110340e070900b400121007440100581e424001140010a14040c19002150b002c3d040b082e00040100c0695000301c4111101091a01a202e6840341da940300d4001500d01c004051141c00c10040040b000e0b02e90718a035560307903075008213807215030702881050381118680d2201600c1041003108242004c959210641a4515010f001240040e102a019154a600050b04840e200c070f406803002c3d9106070b50240d070b15942c420080d00c0354140d00084404078080c50910b80325500c9841079035030141c0c008002d585161100700030800b014041449903255800f036480d001a0340c0d510a010070005078041d0028252400946000828921050300031a218a481400185142d58004250f03045a4624142 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 5725547 1250 5724297 5724311
    0x708120721020a0206030c0301060201060f08100b03010b0d0507030614040c03030c0215031e06040203010b0d0518030a0203030f010503031306030216020918010f0b0904030c0c050d0b090f0c09060103 87
    0x220f0401d540a60060b401040000511520303c0061000718102da100d60300802a26072206034100c10903100d480f590301694865101c40c0d0701c01c905a80110342c88000140001298000ca001265204840d81c03426600e0fa01f00d08810000d01c1241c0c015044070b0104000d00112524203652040c001711b035107010240420692509034000c54580700800301008810301d820b16200e00c1e02201440c0180c2c1a40542c03076440400c100480d1683c03e20b230082c2cac2e060341c0346d003548981441c0c1c0303466408005103c010a801f100c07030b80e600d5007842e20020500050004142c0380c1d014540c1d03454080d030207a05041d01a80150700a80c42004185851412045d0800540301e1514001d0303641c0e242401d82007001000c195010307600403079100501c50340080700412440080c079024001c0c043d64828420030740c01c42d8100e4000c150014100340c00200081d2003039080d202050300c01c940c88a40503448802045410324224011503002d010b5109006041c84104990005d040c801401419030205960200c0c0100c0c0014080505144c0c0340c0d61 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 5726797 1250 5725547 5725613
    0x303050705030906031008010b01020a0c0501140d06090501060f0906120207030e0909010608010b060301120209060a03050708011517151308070f060b03070b03010b070305040504020a0207081207 85
    0x3c85200a200509880d26820002130001304400035101e04205503280c4840300b0030301c0d400464062107090308000400c03411898040151a003e5060500250306d00d0b003000008040308552064402502b036507840000c00d503040040c05401c5d40c1600d143d02080c0050100200241130303200c0307a94902a9402040035845140c0361070203403031180b685420039a000c002e440405c00c51a00550001c01200c80020090202019400501a16200c2801891103d20f8101c8120b07000d8203008030384503000840506402d4103242e80e512000e05100841c0c1042110b42d4658640101501000015001610750244203100c0d8046d80b9000d9640c8003045504014058185000184601c054009035402540c00c96034843c2d8941aa15003035400541d0098200d4443d894012090600e00707000809101355805110f0242c03459090440c4000b640d0420a4200d080041c00c21012074551514000b0b048141840c1d0020442241402441404c00c2031500740d04040b202c05000000c0421100c50104101c1035114014252103010b0070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 5728047 1250 5726797 5726803
    0xe031615020403080d05060301180206091e0a0306050708060a06050a030b01110f061008070303080a0905010209040c050901110606010504090e010605190806090106060c0201080601021c0c14030301030305040303050705 95
    0x2500107490302d4030100d12100f03040b5090304014401c7da8118000c220700c0000440c448401c18a102010350803c0040c084540c2e1070800424858034200302d90165000500b02c1000141c0c2040d06400840c6c107962614144a446500940f283d40c00c650b0448238900e0050a00000030614080c40030340d20109038803004c10203c40d0b4050074078003c0c0690303100161024071054010040d55030a0568600e4a1015215400510140c01040c01070903280d1698500480b915003ca00741c0140001d03d0042c0c074603540c01c1042c0c0642c2e07034907032241c54440e440c1501e4141c1c40b040c811002614076681141d031402207070801d8080001070b81c0e1210440e401d98802c0840000c60900000c40e0a0042103642c100da0f4001c0100321000c00a58007015843c42100da0200c1200c41c3ca5850394085800d88082c0e104110100f5121221080190300800d08658020018811500e4200003500368401040c07480e603002010410020301e420a00500c0d024011040036650011480d42d4550f035402401840345100c05800c006010030320f8400c0100c28 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 5729297 1250 5728047 5728049
    0xe0114090906210c03100603050303070503040c080d0801090c031a0d080705010204270902030601030201030f0f050c03150a03050a03140c03031009060816090209040e010504080405040e0316150204 86
    0x642200100a403043daa00c5030f0b104c0440e284a48603108001060414400c603000d06d42c1a03d91100145040d515410002e91f21303500040c1c4221140740302044013040c554410442c0008041d10340c0e0300c0c039081d5403528511204550761074003550201401c0c584401c1e40320710a5401c000000d20203840c125035400071803c0041039070050b4003000780607500000300000c0d984101c8030480c1c10882c006c400030803044918a0203c0c100c03026110002c3d0180c0200c401080998045e9100d010411400c042c00b0442c1144c10a103d012224122408040318a011080c808110203401155400210503520100325a055403125656202003200c018100030000880d0b021010085041c1d0351004c0805003201e8690a00c1c4508d82000c031020300030381d0310b441c1c0b030000000740100d000544086281d1030912511041402d1a0715440a0b600a2400710740160310383e9441c00b81d8150134400c180c803407070003400310035183e600741810002a41c9081304a0030305584240820f01540d009034120140080d4881041450082c0401d00007010b03011b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 5730547 1250 5729297 5729329
    0x60105090d020a09060617160507020d020402030703090c0801020f030f0907030b090304080607080c0a0e03010b10080603060606030c0f0a03060e090d180602070605180901030f030e0114090906 84
    0x3c0310390020b01d80031241c2011003521100d454a45a40e8100034104c0401d1400321801c4070f03290306562110b40c91034080c100400003580050005a0840055000f00b01613034410b40758000003917070710340ca06400d00c6a10740b4600041e107501002945080c04c4c0d500c90703400c540000f41925500b05103410205890090811503140116848040c0040528040300c130b013034a035045071250314894000c0340c0020303075502d11882d1964402d043c0c0b240e4160038112294021184c0351100070080b42c056589056007071540d9205542c900601c9040d646001c494501003050604146020300402d0040d10144140030581b030840341940c48044207207446035180d414cd00300403400b40c4925440014807145510034020300340c0010550100c120070585904842d0288401d8254041c003c81c455200140c10402040c0549441007004080791030308003801210b034005000010717114920030307401150809080b0015a08041c3c21800404440c502401d10080309800c2400c180c056202e8409a1403003140504001040e40c1d44081c48156040c42e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 5731797 1250 5730547 5730559
    0xc040306050103080a0e0303040e01060503060a0e09010b03010b100801030b0405010207060f05060f0901030201091a0f0c010204080d02030301210f0b0f10080601030c030605090703050a030206040204110c06060105090d02 96
    0x43c0d24140030b2801e511681d90440003a8008210760f240b81800000c80d0f089503014410303031426a1034164210b8490304041d003065030141003800009900d40080582d00d01550605000080102d00c0070109421a80841b200f60b0043c20b02c0000d401d8080e0f0480465811a0340000740001980e40314a8030034024459200c0003082c4074504142080c6040e204c0e0300a601c80c2c1d20550f69030044459450411040100c01d02c4000d0004a14200c248402c80e1654190f440842c8210b840071300346020518207440d00d401400c1c420205070350200701040012410040c207000000d10b400a9071131541450000c43e41004000c2d508c04202c000c900c548020000d06580800311a600a401c414081c186451000036403101510502d25050b07010030f01250454000c542c0354101c951008010050030b29540d283c0c00503240082c4404807500601d1000402b0030020311901440c648254082e0810380340520401c03040300d0a440759444070950900500782d400c81c0008989401c44400d081658540c401500000c180320610b15000b50030230 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 5733047 1250 5731797 5731799
    0x712081209190b060901081504020402180d08090406150909110f0a0e041505010507060b150f0703080a02030603030a0c0804050a080304090b01020102030910050705040b030f070206010f0f06080c0403060501 90
    0x40039070101c11340101802c0711300781c007181d90f100b00d566078603086400c03036404108050011600624148e802845284041c6550401000b241000100501c03070303210041d900e000d8000790070010b0385070511441014050b00030404040d0440128003c0c001d415500818000903a18591000c0003444881610001444480c0c40c0c0d82d54405805c0041c4000307a0f145000d40154200130455282e0340700c82056809039001070395642c1c2004003945465016212000e146500f00360301034103080100200380000e0011181d0703035171920340c1c81d25181b0f0000c01a04000b030000090302c0c814003d2141c555804400c541d0b481c00c0510381540c201c22142003403101481036074080d6901c0b9140b45000104d9a07004000380c03045a001c000300304000340b080001a801d038482120f444489030001e540154103461664000c0b9001406803804600700341c2c071f5818854a45d80184e8031142409007140403c0841c07039040145a016101808500e04031510340b0b41c440d01000c0d090f0242505004480700010f03268810352007590021500520180015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 5734297 1250 5733047 5733053
    0x60a29071e03030e060705121306090305030f0f0c07060e01060510030c0e030109020d020907090305060f090d0216090b01020102091306180e030f070609050a0b0108071208120919 78
    0x1e001000d01200824240119044030641c0803d5192040d0056200c01d803030328101c041103c80121000703044811151410141c3c80208002d44a16002c441c0711742c841c296079043c8109650f6400000401100705064690704000f1010002010ba0341d026502880120310401140a00d41c0074289030780206030010300c03403d003035944141d1540001980342903a880e880441c0032035406041c02c1e42c40100020f50400c0f000f554200060400d0855264800540e140c00c580141d2203603030341410b242c2c0540d481c0e001100010240400750406001c007440507846400140b405404804105507541100c0c0719031080d4030f50f143c480c880b940c0d00030340444000210050410300e0303111003c00124002d00760350003041c201580302038101d16468561310910b500e46009400540c18082041d13211f81c170300c0e0300849048070690780f00c90144001600410014094622a506640903581040b03201460849543e1054459004451502010408020072507100f00040740091140c0d9440304580e614024030300120b810802c981e91110014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 5735547 1250 5734297 5734343
    0x302030702091f06090b031302030a0c0621020c060f0a06050d0c150c030507020d030c0f0b010302040e010b0d02091b0703090501020105060d0b07030506040f0e0102070605060a2907 79
    0x1041994046007200b82c8071130044448003082d0140c0050084104041140400040104901244010200c3c2c80c441d01c20b681e20380007640c8039449035020490700b43c1012515090703041890000d02c5405021424002c11030003041e900c0741c0c090a90141160084c0209000107200d401c410003401d00500422060310451a08410130303503503442842c82000c0c41c0d84d1101c5805215003240300c0b801d40c056a5003030402815070200800c0303444004049080c0554440004005042c40540740a4a8029103049195624500500003500d4040d59503a90342d034035015440d000765940001141106070142c50121469440e0340d00101c000740329403154890b82c100841c0b20402c05500c2010241034403002ea00034040707501c4401c28018035490002e00207007810340f0b090002d49118030079440a80e004d04003c1000c20004035001c055011140455907006059400142a0702400b00900a0982000080c0c4110092a20f0b00340303000401c64640c01008892000b0400f540f0754285e48609032942e0755000f01d0110211021025480d40c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 5736797 1250 5735547 5735581
    0x6050a03050f06090d020a0305031018090209010602010203070903080315041e110708030a0f110a020c0108011d0402061c02030a090212070305070504020d020d02030a060303080109060308090d030203070209 90
    0x7181c0d03ca114001034000c103011070500c5d8070b144150010b2100540c1d581c0c09a680307800050003001000e2030030700009800c40365070030140e10075900d60b18005941c0350140140810314605030041403d5a0040050001c20741d4044007000449810140c030030703282c0d102c0b84503807006a40706e920707541c1e4040e0800b1071070ba100c50b01800c43c0045040391300008010411440c0d8985120340250800070f02520410720000304001841d0b00160800303400c0307817400039005d24100b40b51003968010200000050344400d26014007560021002409400d40c02c061015145080049200c80040140005e000c1c010102e0320000100c0018802503400304012015522841c080005500500c2441d0040e0b200741c0ba101d80e4a07841000204101041e29004805440564101818800a548151a07030413841c0e07070800c0810300d40074a41c4080c5010341c0e003081e8080b808500e1420000c04006041e000030f2281440c0000c10000a5400c40845076400d02c183c909003141691414181d0550186480103034200400d60f00304102014680da001c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 5738047 1250 5736797 5736823
    0x603040812090601050d06051f240309050706030b06071e03030c0507020a0509090a060501090b01030b010207080303040b13060c0306080d03060828050304060503151e040f06050a0305 80
    0x30001ea8402402e01d656440038482e50f50000d00c07000c01c010100d00141c00443e800710540c65a0019140d03031004044c03801c0091781c0245a209180c180000d0a00c00c2518000714000c49850f080c0041d0000781c94440d00e60341d15110300b900b41036a5400350000707078413488140e805c0c80ea042614080c02240005084030389002002d42100080e10b0301c0c0910040d0b038012010b41710884d4010b000303140d005050400b44170b442440504001124490800200001903140c00390314003070800764801207003038080c21001500b03640c64003400c030381550461717030f018480e010000084e030380d02540007007001e0200c3d141c2e61140304e28011511b501500c0c05041100c2d058410b170b010340005d01210140400c450b034051400c0300c210115203c0d402030341120380021b04035110407101072500e00100711303000c400c00c4c03c02800e542c1c1e85855640140d100c40d01182d0088100728004640751046212440305840154a805102d2008011100000f45940c8250754401415003004100c1d400580502406405006111386038200716030388032011034101c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 5739297 1250 5738047 5738077
    0x9030306150c0b0a0612020d05010605040e01020903010501080a020907030f0f0204060c12030608030d110c0f0703030215040b06040203040f02030102030a020d0b0f150c010209100905010206160f0507030c0206030408 94
    0x85199404144228021544506032006e01e440c800d03400c004255028140c141d80302e40d256000230400f590317644910400b1003daa0001a5110791260038142034560582c8012640c0d000303140e90f040076844030a0410b91000341440c00064508041042c0300061100d504102c01c0c2610205001c100d8941101c0f03d1044103005500d01c4038211210b100440a130344850003018400e420510092680c1d0f20250080720609010b20a80f07400d0044a540700c503c2c02c65080c0b40d40c5d50035800700104005058060191800c0f00d0701c04041c0c945240fa2648403483d15440150155004036070010001d41030098164079401c0c019402002035503281408840303003010303401c500c0c11021900d1a0040710343d250301d04400283d03100500504a04103803d90041c0c094021b0b08030f0503c1515075502049942c10661b02c81c0e800f0117585e0615168551400d007400c000915000c0020450140b8031042500102c80ca9089480d5008507017a51a2866039184145070840301c0c2e0155200003500280040144410080e222000d00b08240300340042d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 5740547 1250 5739297 5739301
    0x703030507061a01050d0209030a02060c030a09080303060102030a0c140a05010b0a05060702030601030f15090302010c11030307090509070302070501060f05040c020d050904020f09030604050619090b060409030306150c0b 96
    0x30044940b103000712184d001c24000c001000c0c001e01c10ba005024a8030005040d10441400c98002c43d5140c1d01690308a1400c0e0400030702c95100d290810500c1c0d001d04442c2e0000d5085241600010f5564800c05800c4014001d10a400e842041010f004079510380d9142829a90464800d02c0c285003c0c21500e007041c1c1c400e219030300c40800c15040038015525803a400600500e4942d18503111420140306891064882401d91a0300e408024114080d0b0801d50b1b01c40e40c0000381c008440741d0010070040c211091017886030800c1040c42141d40d0700100640503188120343c1c000172626005030640c000d10841c40c0c02440381d4208100010002000c40744181210400c1d2424080300703e010344103d07210007443c02130a0105d8004d1110200608196000e0300303041c402c0e080c0b01880d040041c40081c1c60300d003040350304031456848802000307404071442e220803e003a00c94010074001101c483c0d07107685003a1402862140515502d5410000340341c401d4100c03000034500442020350b808400e4030700510040005406866806040f00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 5741797 1250 5740547 5740571
    0x70f02040e15010306020c010207022205010b04030210030b1903050a020f0102070e010905040c090e030702041a1c020409060603120306060906090b09030a0c0f05031507020c0603090a05070303050706 87
    0x1d2a05050b04142d009018141c0c2507a030390800a40000407a009199400e000350801a11844040c281c204566050240207071100c5600da4241d03101600408695907061204000603154030055284c034134280d042c0454070f0120b0750007254a4400701d8030072181050941c6000018410301040d82580c0c18004d070750340340c091f100450069955600c10b1040159099800c401008518a9517015503009881a5030405c1403590702e200e00d5040e00c1c214410103e803034000141d003004620300303031050019009941200004a151324070001d5440c400003e0440315840c24481c2c40b40465486612901400d90b2003c030402102c0c1e200d061440404c041c0032050008203191080210b517050045403143c00b00c0c4c80a07915a1340c031505084011000d5002000304e20303054414180100000340003001914040c1c4160691240f02520340740415281468a1100c0100800c0d55401e111003140e0100d0a00c02101090b12243d903a926840c10f0b651516030141d001608500a000c004810103034032000600c84580030700d00034086481a54 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 5743047 1250 5741797 5741803
    0xe0402030906060111120415080604090b01050415030807030201060302030f010504020a0b0714071401030b090903070602032502010506010906030507020606010f020f07030f02041104060903080f0c03070f02040e 92
    0x2035400c015692207440003c000b50f12514031100f85004e010251095410000c112a05a030443d40040c1341c001e4400054145140d44649215403080d01100c041c0300e000200e480324070045006000d6a4042c1c0e4076580812103107a07090400000070340d8441c40041d980c51031401c00038000d01c01408100c2c0309008491100e0800c00c0140186070080750010029a0510b10348100300f10142e0226504443e89002d82c4d051041c115400d00444008080440c0d0031a00a84068001000c8800c607174906445810050240413900300d0000950784000c4d40000c005950b600e40410044560701400d01e0780d466a8841c401b030744481c2d5819000b030b50141d8402e88441e070499403141d006078140c42080310b20300c005a000800041056100740300100f400c503c6070065600e10ba0455481da4103010780c9810594250f4001d240400843c10540314844400c080d01001d1403c00d4201140209680c1d02444040d203100e4011800300003a8044500311400b243c1210708807903981c0d07110300d0708200059074031809900c114a407440b410002c42e004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 5744297 1250 5743047 5743051
    0x3090705091006030b040e01020a03050405060c0708180607080a02010b13090201080f060109050d08030412030c080c0703030227030705030102030105011403090a02060403030c0b01050d1106031b04090b010e040203 93
    0x1c101c981440c642030007401c030000c00d003845c402c0341c3c0a030b00c50320201640e5400380300512040104c0c2d03501080340c0ca8142001842e10360f001d060b0300350b0248100b01e03006c0420104011b80d2030b41c0000c00015040203184600055447c0030700b680140c22000001a0b0b10381480c1c0550100b5a21901a10010050148105603034215018540b0290100e0107010001c0d0201e424040b40c0c0758805414181906410307201e4020603000d182c10001207036000c40020a0006000d821404080e240340e042c9014418014541c000034810381c8080c240c61104180810400c08050098040d28105804010140901c103206555500c0d00301035460030702d0007400740c580003265606060084a060302d2068603110040d43c3c415051510a80c0002c00b194814000c88407501c00590314036000384002d43c001e07036900001c8021400d0072486040c0c10384c00f11b0302c5000e070b0702208400140c0c0c1078070040c03800310101c42284d103941d071369400440b00c5003540300c500c1c6140c180000d01042000961b132016004400aa07255030011b080710b000d203c100d100c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 5745547 1250 5744297 5744311
    0x70302010909020d0e010f0605030c0f0114070f060f05040327050f0406030f03110607080f040210020f0f0d020c04020405090103080702130903050904110a0f050307091a0309070509 79
    0x10000a01540b01d254006056000c6003e81c001032107440eaa080030b01b152585444120190380351041000549010000d00e0700418046030020020410400040c100c14142c1e43c04400304000400c2078024804200f092140f06034201001b4004039017050203803001880d0440b0708801156000c440101c0c0700703802000c20300800c1803c5000c4986507040008025a90611900c580d501c65102c1d039000c00002c401c03d08000c0c8851007619030500390003070282c0075400c10070000e050740c04000244080000e4030035183c844a400c6a01a50180c0300180a0401241008840110400303d40f10300d5021707941f000300004001082c07110941c01d6699107843c0c1c0b0200003e0788202e20a07103510907440001031000c03980ca1b070700425500d880180342c01d0710f07140041200400d4581c1040141d02084000c51001c0301402c160080540352035030046094030306044a44003034a03c240c0f8131442070030440040009882c0c0ca00500400000c2d2031024955006415105030501c1d0651044540d15614041c030100001c95007000d40080e409052 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 5746797 1250 5745547 5745557
    0x240806010809190501090b060d050604080f0d1407020105070306060c1209050904060b090709150f020f030f0c1002090105070303050a090803011502121606090804050301060608010f0807030201 84
    0x22020011207180c0030140c0194100c2c041e00c8400124030740e5103034410407080d210f40300200301112241882e50300c0e080b004000078000c14030400c00000103080415460b5006e40e0010300c2a8484600410a940c41d00621b21245ea406142000c080e0b41c00355048151032103140c03a580280590341e151030044064800078400c01c4081030001c0c2c03842c800105211020554045585444902c1c29550000600441c0065500b170354a80e99880c4101d00a00340100c0c1c00d81d021500d0309195615030b141c4648040d00008240d220403c00c540144200c1c00588240a03070760b0880d00b001d08aa464030030171500d40e8905c0c5d201664805192044e02180c0b16104524002d40b116800161202810131005032400e60250000a04076910641c2d15940140000d401402850281080e40000c0312205001007010307150180405d07840c6084081800000064403000010500d001e80c48100403400d1280d41c42d0441140c016608003070713410f500340100420744652246100d4100c0c0c440301c1d426086030b65100840d6454503900c0c04064001a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 5748047 1250 5746797 5746801
    0x1002030903070501050306060705031b070e010b0403030c0f0507080312010f06050909090f060106170709050f0607020102100504050a0b011406030a0b0f0301060303030209030706030b031905030f0705072408 90
    0x1341c040d001859204402030881c52902090781d68590441c1d102c1101039804032440b11840481000030020a80a006139042031a107a5040c04400b40450145100c0102000349242d620340c10800010040808554020300303c038041c503103030003586032250030000c8901c1690b42d0003000021b0548100c104901142e1850303e40c117140900e014144500742c4802403010f80c0f1343c450152040341d006420882d2714000c18480e680c8801c050080325001c802990040d14010400c0b0541105200d80c3d035078408040d071890b80444046545400074401070381801c01180c504810140303090304102c280180811030322840c511565040740d8030780e01c48030640040c1540d0ba10940c0c10140070300c001501b840c21688038802c502c1000380303000d00c118480800642540d04541086000a401207800301c07140c1401c100d1900074004a08080c0001a02c5a0100c0c4e65a144c03200546035404440344581c060240a0040791800f15000340c038240c0c0c030303003607400d00742d5460956108906907440d50302c40008043c081c400e540c1c00b58030110781c0c0d100215 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 5749297 1250 5748047 5748049
    0x612051b0705070305060f040c060807121d0307080705060106050403050a020402070204110712021006060c0209151503040201020c06070b04060507050c0d030b040e0d09090908090607030c0210020309030705 90
    0x1581040760111007610441c0e038080040b40b001c0003064410fa00e0307400980384501d018948484606040d074403582c244100001805196904501203001040443c080026601c06040b1800a020601d5440030304a006c000341030800e1201710b00c01000914069011504941d0341c6490480712b9125900c000f9060f9003288810200500d0305400070030607540010008503214000808980850380a03c008131000d5050740541425103405000c0705520b40040c06040194500d0b1000103800442c03280c070024814003411001903055040c11400400b094005005103441d0703854064500d0310740e072068800741d0243c0b0800f400b01000e440d00c1000c40702d0455100c4c1401c08140c817595511001351a01500c0202401414000822280000c0100c408800c0c1281c4d80070503c210300d0410b020072100c26084514140d000000441001d80c1c010704110202d170799200700020010b51604046410f4001c05151581c4040005810420f1540c8039003a181c545000322042440190340350820390344c07481016480c9400d604060010012 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 5750547 1250 5749297 5749351
    0xf0803070b0a11091e0301150506070204091b0807061103030c0711010207030506070302180303030705040312020102070204020a030b011205060f0d05010f060602010606020706080708010b031e07030501061205 91
    0x9000700030030301541041c0c0da8100190114941c80c0070601d0003090f00d19524010301d003d0055940040c20403d02c03440c1e2303a0034400031031303418464440302a01540c1c507844518100001036482c0740040015208032140c0b19103030602d144d240e0b2180d1181c503001030481d80491810300310201c1100e0040080800492500ca0305540b8040c5031074204580e281035004503100000070500a22101d880350800350340051750cd10f241121811160b91a0140d68002c1c0d005208002d50381f60800100d40c01d49400c0b8401e0b50b414000d800e0100c0c00fa00c24000c0c001c0d001350011480c2c8030760075003540016a401c43e090306d8090709804045204002c840007140c0079688560000c8071480c5030709000400c0200580110001b06900d407128000724151207007988800010b03907450f0010401c00385d041c001a00075041900d00030400d03040c2408010110101030288400700540000451550715048444540c0e4404400c041400e40c9481140500208000d00c120130104030b2241c1d025a9210252040d50310a41040d143d00369100e4850240040b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 5751797 1250 5750547 5750561
    0x2061504200d0c02070305060703021b0d05070c06020a0c03030f02070504060b03090606060c03040302011404120302010e0706020307080304120c080309030306040c0509010816050f0d060f0803070b0a 87
    0x6001a59401007099800000d909034000300401601d19070380790031081e50041194802c0840e08110f40013988107000045012406503000941e40c6005a00d4800ca021544424102c809100245114240d00725514640140107000c070207015010040c07001d41e550605a8a620310168020f1041c60f0b070000c1440042d02621800002d040c482c03046035252600c1b980030908540b1582c201134401c0c100442084550364081010035444001510b1680c140040c103011241c0c1c034041c07400000d052105c1400c0f680391000140d0117a9000b4518480750100454040c10f001c2d00130054458000d40c0381c0034006c004901140000b04035800316030f200d9021031459445403949850004030b01c03205820422180c0500011505610155000d06600c1b00510341d030b0304000040000b12030360005a0804d01c1428001c0307030450380e080410903521840010326281c2c100c0f401032080703845100707000100c00350a0012400c0b2000700c2c0a540a6401d660b045204d40d126152906000c41d80e90148000003028040103800060b91074040d900660 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 5753047 1250 5751797 5751799
    0x1020d0c05011508100b010f0c0f0f12030507090e06010906030f0b04060e0708060a052b080301080a020901080114070c0c0f0303050306010806041e11040905090304050306070302030601020615 84
    0x4215010a0f40f8008480e40b5502c2001c85a0210f240310180946622032490b844200f424130b02c1010a45c26405000b54604000c00380424a4100c608014480424000c0900d240d203e11120510008800060014001500d9040010b00c084401068101c030700311005000d6130051711100d000741d25101c0c0c00c030050103054030502009600c0700a1110540c40d9401000d0241481d040185414035040c4002480054000c002601c074004524040002d038075585024080c2018080304880a042a045030404001000d82d00500440c000000010328460124100d045503100f102e0844031642e135550007030300362810042c001d00740b05004070218039000e00451a5400ca54800e0300e00141d0195a4503014000741c1d142d82c81a4046100042000708669010105947c0402d00302d800300507034034456403071840e03036800360b024440b103181d85880764064010208160340c018060740905120b81d181480900340c1740d0300b00384650740c0070f44a1500482c030014001d0081d20b02c00d00045e40203103541da540041c0380340c070032080b02c08032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 5754297 1250 5753047 5753051
    0xc040c030b15030412050a09120302031201080609070806090c010f1704060501090c050a0206040201120204030206040b0403060e030301080c0d020607060507020601060908010b030c04090c0e04030c0213050601020d0c0501 96
    0x2480c0d20b6219190350b44402e8032100e640755181c3c907150920031080c408807000501000000c2000d21540c03a0420b004000761200b0070001600e00000c0e00c0c050345184501c01209810701122800080c205000150300c1d0311a1232180c09540002d59180b14844c1c0e2900280d8024503190044001107029500c0b030000c84500601c9890f15040c1c80d4401191040249c405071810b940441e150001484824032a0184842d00c1c466460070501e02500d0060081d03d400010304002d04001c00c2070703260580c80100340c05070307000346400a25840ea610303644c86aa10701540325100484807142070140f40000b0f074402106582c1280c103200094140704040c1001c0000d0001d000d54102e074030030011f100d4400411000d00c643c92150801d40c0041c0002c1d414400003600761440307948003140c1c581c103088601d10700b0b803804564440c0100083c1c801140f4680b10b850815503c0308150042c00074510342504000603d40c1c403981c1098000d000303941d009030540c040100701095641c203c54103030140c1c0c4401e0040103203038824444040214025000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 5755403 1106 5754297 5754311
    0x30c09041a0a02040f0605120c09060a0806030102071e0209010801060b0405150d020304030c170304020a030201051809010f08010501080309090c0c0a05010507050304060b010e01020c040c03 83
    0x915000003041d40e0106651480c583c0644015040400a85a90544694004000340c00c6511036011150082c00801c0c050400e21003110b50201000d0105440e1100e207410959050002404c0e1710303010b40d4200000c00104104449201d04040d810b00112685100d40c0100189000103030001ca005034074061042040c401c6500c02c84007203031010340340780007900e8100b001e8440318010020504a001d00020411003056030000c01400040c1c0b0840705001501e94400d145545030104681c000c0d000010100140059030240014010068200c0d1100c0e100c03165007804151414402e0b03000501002c3c0800083c4405102800340a002d4040500203609041034000099881640544200a6080000b45000941900744808652a600440240024144420f00900540c02204d0070b8500c1c51415501001c55807141c0c4000760300100590081039030580c0d9204100081115024900505994080d = true := by decide +kernel

theorem cover : BRFrame.Cov 5575547 5755403 := by
  have h0 := BRFrame.cov_init 5575547
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5575547 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 5575547 ≤ n) (h2 : n < 5755403) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
