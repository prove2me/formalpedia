-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5114
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:47:22.179638+00:00
-- url     : https://prove2.me/submissions/5f972d2b-4d31-4d61-8ab1-4f181a903cf6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 919604316 ≤ n < 919784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 919605566 1250 919604316 919604359
    0x120b04020a0911070b041106071a0a0221060a05180402030105010e060901060e0a05090103231603020d020a0506070807060c020c0a0501080402010309080d02040618050609120705 78
    0x1141a84181c501420104841e0441d10a942e14120701e9900715181010710380d9140021900200240c076500210b5101c000300b512540001c0042d40c0c42004103081c205165207042c20024009808050114818041c440810070f6101f0104c00d9150b8212110510f0395031a000030794480d009030000b580240642d00002448100201c1e210302070381c0700328020711003a0f0303d0314100345001c4400c8400da0740c008607190040020a015401504021201904845e04540c613a004118081c40070383c8100c07508907442c503160800c0300c803441d0030345c40400311003014082c0200c1c030103d01d0716511003030700010b8800c0840807640300446d07a5010041008040190446480708450b01b4500106e410155043e5490f500301014110310070300c0410108408036004086002160a1200441da2800010000ca050555030455600820b691601422035403d03115000b60360b039410a000181a40364086103114030304510032080c000345d40d5500130784000d0a0140c490382000d807101c65516140c02c0b003640c00140c1140074410610040074820 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 919606816 1250 919605566 919605571
    0xc0201050315060f090301050c030f0f041419030806030c0a090f0e120a09060513061b020306040c05130509122a070603050108062a0c060f0103032615010504120b 71
    0x80b4000c0200d075036210358203a203c0c0b004580060800f4903160015030084c445440c0143c0040c003e3b001001d0105190a00c82d290042c00d124903e83c012058140d00101035004c040954003180580103000b09600200c0410040307d4903001c0d105907180c03a405034040000003948900401440101100c0902d00407152004840d4010712543c00010980761001c0b40d21b502942c00c0311014424410003040082c42d00b00c0490740e0501c00c3c07840c034140c2c080f00c0f00c54002699041018074051401105102c800620300801c202c4070003080d20b6021003c5003000300300b00741c281c4045084d404600c01c0340306003540c0c2c050300d103013211001c00006c2030120a0b03450081002c50500c1c000480001b540c3d03042d14200b00c41d0340c9130700400d039032100b00b00c03020140e12407034a004415480c1c920388140d14a442c41d1180b1810000100345807400c04500300c0d500c0c417a00d18001c00400915a00c00d42c00500c0b042911461040c4040d00304008210541c02005048002c03c0801c2141c1c103039101d071044400074500703400c64008070417507403401141d026000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 919608066 1250 919606816 919606819
    0x60f070206061c0201051309021801020607030908091207030c080c1306270f021803190215090d0c08010203150f0d17090907022b0c0201050315060f09 66
    0xc1d41d0001d00d041c18014690b640c0d48601018030401c030001d590044409501080c040303209005031b070500040d100d942d030003d401c00e802910340c0f0285070f82400c0002464204024410401c042c1085404400b18101904071546080159180c8035a00711900c02d152401d07115900061180d100d58000103007410020a500c9a00e030000c0758801c09010b00b000720740d4241c0d0307c603004009072015a11540c01524143d528001c2000c00030a0010a80050404560040b80c00214641c0c00c0d0791511966041703c2e01d4203004041d0f90a003c0030f00451421920b4002c0b525401c000c4146a202e28000140c64090750f5490028400c22036002c4c0c550009561503002c0203010750070179101212442490003481d20180341c5950407081201c4081c2215501001684031400244040640992044801c000c1d000080c1c03105c5040310711035803054000303205003800b00b211229404044c3d040941c0c034140d541160b450b80ca900540c0c0d00d400307a40918006403691500108542c621850200f01c903841400018450300303801c42c450191030720070700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 919609316 1250 919608066 919608073
    0x30c0f01061203090e13060f02070510021e07060e011812030c0203400f1a030f15041a01090b1812070b0a0806041d0a030806030f060f0702 61
    0xd0ba40510100c0120940005021030500803090012a85a55000d030303100250803450f00111409895140172240020341a9680903000100078080c00b40810800072128010fa4085180940c018402c10658241042c0390021403400902502400840d03004482d116400400800080c0203502c030942190440800c00c90319505800e10091071a030207481581d45141c0e5903006589003410ac0382044007258101c0e8105603901d11414081c460300c0d01c035450a102084441d049500031b00b8105208031981c10a00d91040320115524200c07042c20508010a890300142d041d9000d0502e526108002d01c186035040f01000d070481e280543e00400303005120b0340e6500b000c4003a21384480880e03c07100c900c070f0300d07100e50800c10503482e06c0c203c051081d50400c0c014084d001403001d0162160603407203013076200d083c0d405107182d2000a841001849118178141c460f40b201c0340e60502031044051680304080d44c850002001c054240464178000921a0b1002c0c06100280440c0e041511400c0c41d00348242644442c040c0c410000621 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 919610566 1250 919609316 919609319
    0x9050f09070e061c0803010e1003120f090e0a05060111010b150a050c03030a061a120619050d14010509010c1407060f0501080109032a110301020c030c0f0106 69
    0x21a2106564003410101024012a07428056004202e04010b00b5658200c040382000c01c42c80d44400c410260054420b0765401e0360795240181100303100b00050403114001c042d50388100b001a0000b400c07a540c2c0d00c443d003445c01c52065001410341340b9205170f900155a4024003410007001d00c0349988910702c43d07071090b01c0f441c2c0201c03442c280c800c0c200c492880d030f101d0b00030b01e10400a14880403102c4c082e003d601d40303502d030003407400019070103243c110740090f40c0d440310440e2100c0082c08200140c6404100d0b038400b0720032540c100b0008000c46050024050036550150101249900040c5404010400508006010040021000d10380324010003020150009154680400b10780071000601400321481682d5503800551400040c013003c00b40d010040c12a40300c0e0392080b0140000740c0b40d0007140d0003008010000240340001d8103014100c8044080b11464412142c031841203100100c658075150607410110941061040c213021900a02c642d030040c400307910010606200c2034170005403440c0c0c0880010700078010076 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 919611816 1250 919610566 919610581
    0x10612080c1e0a0f14330c0423040204061d0301050c1905070c122108071103090a0308071506180527010e0d0908250b0c070905 56
    0x545124016500d4003c07281240118240c030b0008003080b801100c0703403c040c1e458822030344d203454441002044000034542e2041aa030303070241101414540c000c2820b07142450f0000713510030a480782e402041c4100c000f81030070000746d1040c8801e0030704076100034004640d181c0d00c801000e444103150080590790111260a01d01a40c207040c02410300401c140008141015502c454801c11400c840c490941042801e1004402043d00e002004009000740c01e80070310741c0c0c0d0072820480d0b440ca410712004610303031140c500b62540d80ca03800f011090303200045161404007078654460f030b036040d40309907803500d54040d40b804804420301c0a02030042c6141c52182401090b0b0b0000ca19000b400d68070284520006503583c0b80c1e00e1710280c14140c000070743c4840451440c9410000703a402d10403200441c03881c000c1c1e250395208001c0d544502d0400501c0e0000c0580d003404040345240090550b5141c10b5035030b24020411130303009065840c10050104901424100b8003880c2c5a03170040800a5450209104090380e01d0304103c04520306 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 919613066 1250 919611816 919611853
    0x1b07050a110a08070f0303140c0102040603021902030705060711010f020c07060318080301061409060703180636080a03170c03150d020102070503161403061303030e010612080c 77
    0x4645c0040e1000a0b901e1458409840a40100d0841760303094800700148000f03070f4800e1000300044c060680700140c84514000d154003200440440c40f8041d5403041140340045800054040c1e40b1402c14580310250545218000d07025000b115510708015001140d1214080404104075003a214030b40e9003002514800b68000300040c0e03180c480a02910030400041c803040e440b0381c00502200b41c9220100e0b2501d0741c0100031803203d82c484082900011070803c66600c007140d061021100400c3d452425051584c0030087c2500399441c90701e1707455a50a04c0c2d00514800380c80c1c86a050b40206020400d40711990901c1c2405440250500740c14030705540e10b035000403281d1042c14203490103003400c08920100e4405c1007040c080c0010b1004003d038154492540c0006480d50208248809c2a07603026804000a14000000d90b16000403a0128440c3d002402045404e0102d84480328200ba0141b03008200002c0b2046101d006020030303003000184242410f00b0700c06020b204d20003464901080003c07604504035a800138040e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 919614316 1250 919613066 919613069
    0x90c0c030a021f140f040203030702061c0b0a050a1202030c0406062102030f0105120106080717010e0d020303240d08190e0303090d03030204120f0c12020102061b07050a110a0807 78
    0x20240080000c200c0040e4105c041c41d0b403152000d001c880c0f03070005540004420307803c1203840d9a10106100c007149a502118003c03103034021015950320004504090014881071281d020706c0550038101c000c50000d540e410040da03114000082d004200c550f4a0324802405144c0d50030300d41c50b0102c1c1010f8290131a8980d0f208a91203408248501c43c40d90742440300b00b103421100c1441044040d900c3c0c18003c1441142440058002d00040c00c864180e085401005402c2d606031903003039a10342d008550751000d12a00401226401644004403840201956201e0031100c00d08250582e0402c10392003a900030040c0300c03401055150152400001c0001503454201c88100b110f00702c058041e0018172a800c42410704590103400103210b811701604103620303504005030103002c43d80203650644545458005100e0303c040b4401c060070302d5034200c0e0345928407900043d42d503c2002c0c0120000c250b01e002140c10b0504a40c003030b50a200e6002040e42d000010b07a040c80040d0749044c205084c450b0481c4400090540c2000a5060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 919615566 1250 919614316 919614341
    0x209120c010f120e070f0503010c08060d030c0515040b1509151516051c0216120c030b2a070c09020309240702010c03020c0606090c0c030a021f 63
    0x14a000090b030411500002c069200000c815165080101440780a2013900e004e00f41140303036020394a140004150075101018100d07000d02c044d010500c0065240d44807104203150301410540020b5034145009440d05655901d01c4070102c5d00082032108004a040c100d5026404140500c84510107100800019000540d04001c2068018426601d182880c40c480c2d80c18404000c1854200b00c070909120241c1e0f040054119204d07004900d2030100d0442600812040d5040c51004003402d030f9200598543c2d020300f90050700411039000000c0010001c442c0d400380099030b4066a8038209080c20401c1000600c3c580f6662640031103401180c0c2108003440060705c0420382c01001c01d40100d0700d0415080020740c006016450140195104004901d40c0410760100010700110503801c2c41c83c08a00003400c40f120802c20300105401003000c111303104d41c00561160440f1085030401016200c00c10040310b04d10541c80c074403046000104040c1c4078203030040303070b01d014500425021804040034511400d08449061050a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 919616816 1250 919615566 919615577
    0xc0304030c062912030301080a0f02031c0305040b060603130b15090c0406110303160e031f0906050a0b0105070b150a141c030f05160c090209120c01 65
    0x140200c0d00c5400025015802039600040100d40c80c05003c00d90014100303403000400100300503035040c1c01d2100c21040b10034006000346082d5410607180d1a110088103d001e8001002c0607280c000359a0103100c1118802c01701e0601078101080083c003d009018111400d03914041c0c803400103041c60a00804880c41500c40040c10300409082c2d0741c802400b594044d00f0803100044a4400180075120140b04038060760702408076540700c03403130680014240b444142a004580d0420710505c0343e000341419850780948414104501d0f003540020100e803809d04041c41e030481e107483c4a4884d100b10030702d03580040b140c540100c00512095860594500684001c0e820860005608010440c0031410f805100b94200e2070030070900d00c0707075003030600040d10043e51500940030b401500218540d540c50410700400500da140641842007210584014041002c101e2015043c003200140300340a1450800c8500c0ca05903118040c040a179031138062100003074009407100c600800418210003820080024200d41e4180e050b95070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 919618066 1250 919616816 919616821
    0x6080f0c01201204120b0109060509040f080c06010b09030c011706040b061b0c3f0a08070516171f0b180702070b21220f0b06090c03 58
    0x160b0101c525250b80e0340c001d006001c101c10032601c0c66030080c4010b2804c444034803901800c9040400003114103a119141c01403809004010f6502c41c2000990301603040003003442da124903410841e0081c4202a5024110b00460b40003040030401c0750080d000d0081c081d0b044428080031507005441080707004d0507c6014400146c00541c1529194100040030400035212500781041c00701c4085640b9a0002c00810640044240d9240c80c202031068a00045414100240c106400c02c40400c00465003030007800d1903060060000d920150811124103260341c400b40c00c655445081c2005c0d0340780d4080100350392010300174100c00199004480b2400710010381c0200a0000c45000f85080c0310380131a22412000c1003a11101c0b200c0282d5504903201e08807010307114040b01c00707141041000b800c040468000110f00601841030800182000c0b490060b20200341c040307440310303450306100f245080c40d0300ba805400b00c0c0720300b038003040403c4600d1074541000b03441614450034a4994404021009400700e41500414405200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 919619316 1250 919618066 919618097
    0x40e0d121b090b071406070305250e01080402040618090501113421020c1e1504091508010b010203180d020a090e0f15010e07180b03070306080f0c01 65
    0x44c0076140c410103110f07a0b5050f07010850b0782401811900703100466625000c002030ba24404102502c00e004502c1c00c0ca44111400c08090242c0c4031150141e410030840e40c0c0042c04540300c690010010704108480c0b501604100d00d800302c05000781c030104a505500300311004030070400e110709075104001c21240601144504910645440320300110481d1402985448a00480e1101002c1000e0018945850803040d01c1100043e1400d000c0c9a40103016800ca02030400d0784251003508090022421110120a10503074005030706103004079001668440c0c034240d003194100f8240900801259224002404900321280c01a40c403030041508910a600e2558642400e514250305100c01552008040c411095101c0b86901c044458081203110554003002d8040c420b0007042103a040c480c490800d14069a40c1000503080c0d10308401303000d0710f00b804910303005150b20320b1505270444050025100c0e829200d03e841c000080c0500818426010707180071740d213001e9903902c40102e00300d0b106e8075068440281e4000d0040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 919620566 1250 919619316 919619339
    0x1014010518041502031e060a0e0a0908091c03080903030103020d110607060c050307030b0a0308070f150509010510170c1302040b0c0304030614010602120306040e0d121b09 75
    0x240201e9400b541000d4120390140f8502c007441c01411511106420701060300c00b00741c0d84203806800c151096103c1c20040050340c5c024040d20394011111a004900b10201e03290116003402071040d0759a026101c1150980c04a05146100007d280203a1358182d058603044100c5131071b03100c2804040d421550601008000c40c21201c001d03080c4440c007600c1c1d2403900305503864400840b48008055000684c0c00814480f40716418011681c4c1c0f1082124040c120741d2855035060046d1050381e00003000000130f0300300d040c1407141c1a481903001940100b0188160b10303003001c3c820700a03d8226030112603011551404180020302003940701d4a24080c0000b801200d501004000490180e00e5005488540810020512030341d00303809010046022801161540d0845c9483c805a0b98198441007071080060300401a49070b00144140400000680c0c0310740d251941b401090141c017490050241c28420a0380b460000ca6210110048950448030b0401c100240613030b96150112010b070101c00010b4150b88103012a10000c1c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 919621816 1250 919620566 919620571
    0x51603050a08130b07050a0b0c0a1d0d08070c0608070305090a0f020307080307050303160c150504022706150a20013b0730020306091014010518 63
    0x2003d05126075a03008404441d501c940c0003142c460300b111080c0d20411042c1342e40550842c101982d81130503d0700d01e038001810106c140c5086c854407901801c0302c4449840704145080002d0304034242c1643e58509040c40f903035500c1c86114510000d0401030000702c640c2e2080c405d841c0140f0040340502a544000d80391039845951510b001d981c98011500700141c1d08004000404c14140310380c0103580c691505240c42201c2c0964100c1100c14003090022220000b08041e51400e01803800c280005088d072124000708401d4034000307401c4564580017a00142e02c50030b00c144d0740b91181c00d0031200200089050002c58075140950502200820f0300020324a00d0b8001c1e252280c0d603d8000300000003070103194040d88110f041c4082e156016416181c0290100c040c465168110042003000001d2961901d80307400c0240302e581030808181d01c00d81c0004038a040050710303480181721a0300101120500d0400011a43d141c04065041d00000d40c41d29800403541030f0b030080e903e8120f6900802c040c601043c5102d02e881c500303100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 919623066 1250 919621816 919621837
    0x30b010f06090308340c05120304030b07032003041b140609151605191a09010f1113080a020d020111210d05010603021c18021507051603050a08 63
    0xb0318406000103031400b01c5617000718081c03c008815505090520f0b01c140282074001038000d91100e20010300c003e2000080340c1c00c030381d032000325402c1c1075549001c210010440c0404c80c000b2084141016002c083c07a01000c0c6000e180194208040540c595090340c004510601c1482c00b864000402088989006006020001c0019214030403441c1c00c00c04a0315190300c41a2000e1a17108091406024000100501e490358a83c0d03c400c25503054042e122001e513141c515900031140c002c0000055400d640c00c2d003112000d49903002c4c041c0020982064502d84680000170b00c100d40c060a00b1000488500c000340506140d44c0240106070140c0f5247c0046074244041c0800208a1084801c02c1401034120a51042c0441000b030381e440c8c072002d6403032030001136800c1a40494205401841002072400310007003c07450400c1079000004030640f0030381d2540981103035054065401b1450855400c0759044450007400e2040c4110300350b84c00c0003818081101c000c850b50002900f00c3d88080c840c0c000049001005107642c210 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 919624316 1250 919623066 919623097
    0x3090f0209100b0d060602010c0c0503041e031a07030b270c071a011503050106021905070f06020601081c050a1b080c0f1b280803040609030b010f06090308 68
    0x100c4110f1003101da13029060503180399548400411881b60b0a1084002e000300a10302000c40001a84460f942d03801940251010340300042891046406c40d00c4100c4000c55001000380b03031064400501a604550413604480400e040c000201c0790f903d41001030300c1c3d410510038601c074100c01c041d91090150304001040c003c100402007041502040c4120000404440c8580e4022404d40c14000300040a002181c0074106160600d001400390030713000b0500c403003e8290502c40e458403034450700b811450050203900c10000541c4011010034000e40c0480d034030781a10417030001c032110b42100400019070810318840c1000058424000d00e10494400c0c800702e00800910300300128035039800c2c5c942e0a0181d01007103000030258040c00c42c000301e0131010300030303111807118540d00308109204080115091002960301450807031041105014035899a902c400060090b103011603071196113403030010b000c0190390300041c1e507801c54040000655050a9100c24103440103940c40e40380e02032461751840040d400c1540744c800ca045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 919625566 1250 919624316 919624319
    0x16050d05060a0f08060a20030a051b0d150b0a051209031306051c0c080106030e07090501120209160f050702030a151b05090d0b1b040602030a080703090f020910 70
    0x490507688a00907141e410050030380d6052071007020b0206c850540600b000244510313090f4007c3c444c1d802c1640e41c8440039103004645a40ca1102c68001c64545000d03c2c01c14250101d14a0510244c40e4080c0c4141e1464140d071502c007c0c3c0303480709011603000c2d21903202c002880c00c120300482c000862002a8001ca030740310403a801c050071040c0015241e152500120f00050700402e44202d100a411210180740300c80110400030308468800081c040e20b0140280002c0c151030f034a003081044001c100f15002032510180410141d6100c804008000a11150503889820b01201040c01e200036400d080004680c940c4805041480301c52042e80c454005140076a0705004100c14107000c18082075410a54403490b180024036a804898020070b0980d0a004200411005010218041c2c80b801c045c00342c01d036004400b000c5595200c10884e61080d0301d02c401c0f01d110510203e4001852500000544407540154070340c50025991000210101d841e8903101030034146258080d503016040c040080740c5c006000300c884c2801103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 919626816 1250 919625566 919625579
    0x5042001031406014406060a0f08060a030507080c1f0e21030d06080f0d1b02030304150f0906080906180f01060b0405090606120a0e010b130c030516050d05060a 70
    0x205481140c82e045e0124501d0000034840524565805042107801d50700303002581c00e00400e8140f007040b6003020300419501150b00c80e40c0e035117061002036501074211540d0a480303801140c1c5070260b02c04081c0c042c1c4580041000c0e000f508155822001005640b45090b10101c601001072406140d20521811000c0c502c00031107002003800100b80014601601084035490300841d6890807140d01030a02481e0014418200343c030380d1181c042d0003c083d01040500b030600981c00064194416039018a8900c80c0020420b401180c2040986c414051140c03544c1004642c2c030601030725503078002c80d0049400e80241d0300090490050070f0300ba030355120000c400c4801c3d9100e0760200c0c03404c40c1d15a0300070301005400441e0400c44ca140110f121503001e441038480c0790910340003003d42014580b01410b035000154990030b0390007400f002540014040c0c0b200400c41c0a10100d4908140021700602d00440000703820b0000042c0d90500b41003641080c0f400c2542c6a601d0032954a92200041c0000391101d41d100b44203d0b80060751 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 919628066 1250 919626816 919626887
    0xf06030225020d0b1512341d0117030f2709100e0c0a022805010f0f0c0f0e0f03010e030309010501061805030c0906060702040504200103140601 63
    0xc2c5c00781030a13210b12212420400030f11920303010700400b060b03011140c0400c03a0000c0500002499564694070201d48484403c05100c440e55078000a244c00c0c100e408110030100052041c1d4102d4010008090307401040c04080c4d83c980c81107941074507100390b01b0810300000c030a0b070f4815040411a40c44050105040440008520340310a8030050b41018480000307011901120403510742200164031014a05210440b01940310a41c40d0008907001e6640039000c01c8103516100049035040c2d000d80200000001682d43d90000c00010802504c81483c1800035610365000300780f056003260942c0c0710a954000ba8104001c0d02858407040b00d5055500d8046c2e07011b003400200003542c00ba104000002c038496042680040000002c08203a01e643d918139202080584c9001c12072520b900000e659250456480c031011460502c580071000750050314000410040c030a0142c41d003a11450080b00042c0b5804c07012004505441e01d200c04501890201e8000c21965800350300c211118030a10503421000d56007041c0390906 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 919629316 1250 919628066 919628071
    0x4030e0a08010b01030b04021312050304090e100b0609010e06090d060501030b070e0d080304232407021f0b010e030607030204050a0b12040303051807060302040f06030225020d0b 78
    0x74280e44a00d5040d02c2907806001d0881c40c403a003a034085041c0001680c560019024034443c141201e41c111307072904148807041c400c807005401c030190207000100d1009021681c1d28511145400ea481c43c05034100d00c103107868012901400416590b003c941801d81c0c0c10080c4036480001420b034045291140907002407550b000701402035000c2d45405500c1d24180300081c02540c4d9402026100740c0c3ca04006200041c0d280b402d607500710b604002c0b490008140c0b00440c08501c0308010700140c1c20301c141540c030342e61007408100600006c981e05e0001411522010001d0381e8802805200d658098103080d60400b04d00e0555003c0d600200e41454556210b000e600f011a091041c10344071080002d40001e0140020b0030003441f44002401b10f641001c0c6020042240c07106454000740004003019100d4020a1480300101c0c0c031194442040e1095401c0030395240303805802584148a8040d64414120300003031800e003e4800c0d64012225002c0501c0382d010307584440c44c2c90320142e8004a0307100f090382c00700c8070204240104061 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 919630566 1250 919629316 919629329
    0xc06041e1a090319080118050606030f04030c2a060e1e0a030b040f0b161407050c1f11011109011809110301080f0a030e01030903050d0905010203010618030206090904030e0a 76
    0x60700e075040407c5401c843c2c2e89441c41000b814108002e01019403602c404590307100414652039011615a440c04484020000700b020340341100030907503a40358000003804401c503a0642c8001d08042580e590059400040075000302d58401e040c510710f24031070840075610141c0418001d2040361910380340ea8515a40440a4030b007030350081905022a41002400090300d41c000c201442501004180404000c001030a2200e03074085030031010440b0ba0400108100e60000308000500040b207407400d45000e00c01d1403288404110014401504d0340d16003a02c18443c24030450080d0556500d400c0c000c000545901d034200586401c07094208070700140c09655449554907051580310706607660351400d034059191600c151700c540215007040120400180c0c001c0c0300350210080c00e080118840d1100d00f4141d0381801340022280c10603052800c07a2041110640c02941a03030066142c0e40c3c000c2448100007244003516000007504400304001c003505034034241c2d003000c0d4007a1083c44c180403001c903000041100250158030a6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 919631816 1250 919630566 919630577
    0xf150806091603020f1206120a050304052206061107090b060403060c05040b0301150e040c090918080f0309190314130302031906060b130302120a05030c06041e1a090319 74
    0x18103490500f040044c101c8c0d0301401440d2600d45522019228860bd200d018030880004000c2c2c80202c4c42e4401000c5604090b85c070402210350307117083c06000714500410b0601e0307902440358046440b9503240310f1342d52003407000ba00c8bc0c0d04003821580c5004c0204944c50180c1c003805005c0c08001010031600b00150b020700b0440c4000039002d03181c141c01610b01121030350454450740c11321710800750450307001e0704000c200e1300c03420004106501e0b180309100c010905031001900009d400501100c0c41041d0754000d6018510710000c070b0b00031482400841c466040c0026004002440c50100c680c02c004c40800035200c030400c0c9024194480303603241d00092810408410841007042c1c0c1d0107280007888014481c0800804484e0075051a1a0600e01070303020385480760000903c1440410250b002c00c401c204603038000141c2c000c044035518032003410195511007085504480320625042940c040785860011811126403004038080c1d124000c84500c800301c5001402110b0601c400d1205a055000c00120341c100c2600341c0e100c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 919633066 1250 919631816 919631821
    0x90a022a0111090904020d17040b0c332503141f03030311120f0124090501030e120409020a080604151203180f150806091603020f12 58
    0x180ca003074a0088054407169a4248120b4696450b641481644580d04484103c1003840501c0c0018210101009401c85c0d5040404c000c04c1901d000801000d400d0780100807101ca088158226980049a02c60503c0e840440d035109407a0813100d10f0348441c0c00c880062800002041d01e6404010030480b030104a40c00641c032004411182c03504601c080303402c002c14486d405a042c01c03078007000d00303903000320f200c01401c0568890b400c100520801043d141141000d2040040c01d0401f01d80080c00d0a00230b0040c480c486d0041d1180149004e400140f0f007440d10001c1e1076100e0310501d40401034004101c040e03100307005400b42c1640c0745480495440101b0180105807801600c80c681d0200052411500030440c0d4040e0385003c00a5500345401c1c2c440c0c40842d280c641081c40884140d1404491014403041040c185503008280883c540c0d03000901c810a960040300d56a2a040d00345904641130881034402039000444c8070b011480105244a03620180b9007142030140c5001310300a2690056440303d00002d01102200c006d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 919634316 1250 919633066 919633147
    0x20d15111809060121020904110406110114160e030609010e0f060903030103110102070b0a080601080c031b09270615030405120703030f0f0b040b060c0705090a02 71
    0x1d00e0001c4000540306203801c0c0c03800c0302c0081c001c40001c403090003400d580c6030f1259210020540482c0c55242002c0c000380b00021146425007411b4000703004a00100c1d058000507444030f08140315480d10302101c1400b000c4103850f007003002a40d06901c6030025003000404a40c510040e10200072060013050000c0000500c080c85201090520801e11056030054020034144202480e0010a0302e06480e04010500c100000000042c0e15003070071a804040c03403240100c4d524110344e810401d0b441c891042a00e0701509a40d884441031030714401120207818004e000381f080080c40c40c000c0083c1410300c00141044e0502011501c0b00c040320858102a071808101507010001a400c0401c4035021403a4074140b030314114105903407202d440f04690344200045200100d069028103120b0b810140030382c0003101041001c0e9050002d00c90240412160a034000ca02b80002c00001c1c1c01e15808a03942286550041c08030a03051600700003240d0fa0141a4128007038080c008100d66511026204a0005071107900303500d01400c400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 919635566 1250 919634316 919634347
    0x1b02040e06041a01090b011d011b12140306030a12030f020412140303040308130201120204061805010f0509010323070203030f0c030103030c020105090d060219030e01050103020d020d1511 82
    0x8000c44170351420035080d00040d0345c01c44c1ea5401c000c100c00302120501c0c1000c1d0300403141c0000e001003c0380c400500194003400d0001444441001e0b9016550340c8100075094070302170340244410b603089901580034044450105a11a00040380c00701c083c0303000710b100c0010000301e42c244e8105410101c011716582d4420301c104420300c002858665541c01c090b5080d0711301600c000e051120004c1107200c41481c01250101160f04c280d07003594150b00c84820031900d4a80303d210040039403061498504103d80d1044002c070b240d60050b07009610540e030507621036240484410045018051841101400c106100004140c8407055080103110741c4443c0d005584034a000407800303040f624040d02c40580703e00e04100600102c1c0d0300c001d07003c410a4080c00c10980c4d07a0220804a0804d252000c1c0103803809101080d186c4901d0401c54019501c2e00c816541800270b1440440c4290803030b4000e04c4004d5021070800034038801424222250b444d424012441081d59001c0c42e000d100a450b8100c0d0809080d40c0005559441c13845401d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 919636816 1250 919635566 919635569
    0x513150314150906060c10050415051003020637050316030203042319061b1d04090812090a0606090c0f0e04060f1e151b02040e06041a01 60
    0x3090780d00c03140e61002d000c6400d00c4000340074240500c40000391040001020042c030303641d000307414404212610303250078103e401c00400d104240ea40c50800d000725030b001240c0841c01c415250010402c1d0b1a0000308012104640260041d01129a640c0c100b0400c240d003102404101c1803410380c03292560f0340340c01c1c6850000d018016601700c05052061052001103480c517030804507a484000343c16204840030503041803a10b581040c80740c5c101100c4a0304002003010070b8120708a442607640c4410700120600b881550303055901c00d9440803080c02a4502c55807458281c20482c3c01500404034149060002d559110442c10200d071500081c0c5d0084813200200007280c480c8400400300c0e01410031960f5614480180a0503484049204003e03102010022a42c0e99900810040005509400c01e07603641d41504a803070401d54500d0134146111260020b140382c0075008100710b501a0750f458106100c11a03400c050118000e91050760000d0396801880c40140d402c0000c217014901607a411160201d54403609107500005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 919638066 1250 919636816 919636831
    0x1a040311030c030403060b010504051314090307030c0f172115060307030504020402041215050a180b0c12090c1e0f0607022b0c060e010f0513150314 65
    0x4008541c07901c2da011082e6401e0b43e92000021a41d00d2800b001225580525086a54000c020441800f983e0810b039100381c0c0000c00d900c00151569450142c135503124060501c01602062500110500040c000324503000020f1081c0066841045594450a0b55070813800c1c180440c1e0715015070460b00b5880140c0f000c0e41c04505e061003211012125404298207001c09462001455182d2011034110344d01c0350184d0f005003404001030344070003900d82461340d1070004290b034459640b4604408203500e840b403405000010f000b007204080c4c20b465196211510b00e8030040c41300d048208184031082c40b079080d40d40180e00504205000701080d44220080144072400d0b0f00c8481c2c9000d40305040030440741c594040a00c004802168030940307030f84980c00405d0364070319920350024042881c5002c40081001d0108a240a03c0c0945100005a51600300c01d40740c00740b800d2030b2a40492034510f03240102920030130082240d0369a8614bc001111b5560028082a024407810303500400d48403d0405002c561408045500401303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 919639316 1250 919638066 919638073
    0x10212010608060a150503100312020a0b25050706020903030712120e0c010e030a06020f1309020405011e031b02030a02010c08010515071e1b0803090312030604091a040311 75
    0x7600c28a9210085c6405030002444000b200058405070704001060065030421403c90580700c084a00a444050000c4229801090800402c1c1d2000407003103000d12100413025903980003201d1910644468200c200100c600399000c000366031540d00c042c00500b282510501d030b90400520045c030040c00a008040240b40c80906c0d141e03000300c200340001207048800c403081c240300c1883c0e0044000f02c3e052040700180544000d000052107800385115030f005000141c841420510459226400307001a441144161800103903c030322040100200380001508030b140b40d090020700c081399502d20900079a80d00e0808000b58201046c034020040d028024140050050b150284030381d030404c1c00141078445c114110183d46200407070301c001000301715002d540018020714160f44150f0302a1a101d14400001d0040e111460214040021603c80000950f02c860400401510701d4141001442141c2c0d00000d101d613034400c2d00c60f01d03da00404e5141080190103118258518468a803d04014103100e1380034008951651 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 919640566 1250 919639316 919639319
    0x902100e030c122b110d020c0402161202011d0106050d08030a090c0f030302150408161112011b090f03080d020d0203090f010c020118060e070305010212010608060a 72
    0x581c007144061401408982d0b112181101007407003490401054868004600310903407610000d607800d60180c0d80c02040e550f80401a800c580c45540d1240d43c0c05504c400540d12000d4910302e5450250081c00032200c86883d407030310911303141d105d081c17031030000c043c950025035034904229428140c0310301d1505e8a2031500c0700070b20440e031800e404a01c40d900b4610001e000424003102041301080a900070804040c0c01400c074240194983c0e040108000b424442203000d8410420b40c0c070800c086c0351881510840c1c202c10858200b40340b01074003a805011900701210040080d1803000035580e00d5005102e0010f1106000113500380072254a10604241050120180064160100b1100030b01c91950f8040e250b11646441c1c0340c001c0160410042c5c080c0c0ca08001c10f240c000320400c60411070001d000410b44c002e000003070000c1c840c01002a4229543c5a400320400a2501d00f01408640c0d15081070300c0d00b01c2c64904a90741580d407502c071300d07003240c0040001090414444004100c100d910400c0140c01480888061440300e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 919641816 1250 919640566 919640569
    0x30d0216110604150e06091207321e33030103050c120109050111191713030908010c0c1202030a120b0103090b010303021c051309020304240902100e 65
    0x10404d062594042006a0340341408940b100c0d8259000e8a1010340165215032a4120072034032030381e040c01550440d00e02c07050782604500c3c43d41481d0307450489002d4038082d000c00c0c44080c404030040307030444045811400b00d90074106031100340d00b4880005102041d880700c0e0310a040390a99000300e0b01c40c0b00d85140d00a100500204201040150a500c0200d90120045091882c80c601428811038040c2c03031546410807001c0c21f002c41f803008140d0b40381ea0042400005000500235198214489460f080314030f03000000494408a0303650300c41c1315500901b00070a00c1507694003540c0c2034a0a00841200103000482680104082c0d5810703115164220f002850404002c010010045102c540c01d0800302030311469004c1c50750b40661b00003c0c415070010340301500e541e100d0034081d54407022401c0b068250821100d1149980340f0400c1500c0039041c1034030031107007117600d04000e480c041e40000d0402d483c40300d20100740064451100b02d242241d030788a0140440c1c440954010803c403240b07940c082c2002c2c00200580148036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 919643066 1250 919641816 919641839
    0x6080c0d210c0807030e131506051623070e0f0402150403080c060702061302010801231e03010c0c0b0a090c090903030504050c0a060906080702030d0216110604 70
    0x500e140c200081900744107240c046500075403085000d08900d0000900c04180750f4000c06261180c082544c5244c1040b142c0d0000c1401c0b00d510084002065400c0e69052290701c3c80707200100f00c846164404808500e4180d201c027020540c038109120340a00ca802e0440c8002c0c18144203900050203002d03017030003d6141410f5010002503004000034466000d07410148042c259a130700355806140c2004049440300000140d0a51307540e402c1d00d040000d0b00c9203100141c43d07000180d0000c584c56a06030b562120907441d08503d45071451527501c82800c00382120394507844684a00600b950040b419407001507440c18204285800c4400940c4c02c1400c00511600700b1000c15081501342c0d4000341540e100284080441c10000c1070191690070000810341029007000074113502d500028019405603050340c034072000b40c42c100505070b103440c0304840c04141c69103003c00400303000d0341c3c0c40356020026005907860224540ba0100c1264005101c0e5102d10080005640078032a4580040d400b1039010b54543e8076160501050004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 919644316 1250 919643066 919643093
    0x50301020705070e090109150207020a0504060b0a05030402210303240d080a0e06030709080105090601060804030c0c0f06030203011701053102090405070302030d0f050322020a03050106080c0d 84
    0x100940c444e00030840c00402540601200342c0c0110050014400c00107500000e94450002a0700c1804801070206240ca8944074044c1180c4112011518100b0101da09503481e4000620a07a40721a0040300010b0180c3d00e40c802e60607000914010b15640e00d42041d418402800c91910a182c0900a624203109921140c1a00703001e5030308000b801d80c40b001301010848401d246040031503000302c1e000c801d10509d250002c2c03055064238500b400a02181e521859500d9482d5000d10441d80025546404036022070300035614080d005000e40321440c1d049403649000030178120b0607400600043e40c004010804444821400342d1100d105100911041c2407140c5104200c7c45152502c40c00040880e0302c1c401d152494920b0b0303114066000e41192140c0c034080c107003540c55008610059020b4002c2d08003061001d449442d1000e82c12510380c0f5418156200c900401002c00202000c0d585c28060030a40c80b40036981c0c0310002c000852140c400071900c00d0410010b1410701c1c5040c0d400a020b81c03210248440000c03a8400041c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 919645566 1250 919644316 919644329
    0x120b0901180219090f081207020603270d0e12070504020a03020c0105191107150b0105070209040b040203160f0e0a02190e01090501052a1612020a05030102070507 71
    0x7440341d41e0302031020001d01c104500d26a40f080f80d40031071103820740c0254415040303680701040c42c41c915580300360441d04c6140340410054141e00800942e0014a0460091908401032543e949650384060704d11400352600301140c10115445058661496540010b00146464094501c40300c0703075555400750703565807046000d1188120740129105940c14403d034140e4850080c0da0009001e01e05021141850410905000c4200c3c00e06156080c1d662680200480e00700580c0f0944855420000505540040001002d684c0c10018104011400360b50fa421003140241e01400782c101d06810144101490103562042d08000b070031601300104a40c81d80303005400b046600008402c5026a0740c0d201d54130003885000610402d40400e00c404001d240c3e40b1940e07085050f903080c0c0b50b0907105601d0707a005584c54001c11041c054604400007004a40b810000442d141804516003241c2d0503018071035034041444825045000c0380385600c0d4160083d490522032100003400c0540c000c6203490200d85919440d40e510b0301034007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 919646816 1250 919645566 919645589
    0x408032a18040b181b09030303010b0a030f050117060703061202040506040603051f0506010e0a050103020a090906090e060a0504050304030308090c030102120f10140d1103061006120b0901 82
    0xd901c03580307076a040081c0103000105440380b180601d00d80d00ca034041d025100d1401c17400d86903444081d981554070031500c2e44400200150700707503840d0030340011090380a4900c0204050b1110003003206040140200b602a0115117042c05034a003a48000354a8140300500410406040200c1004541e00b0106412500c94043e240440c00d5076544d0302042c05401994401003c52081000700060030300c4107110400768842e17042c000e10041c0c4a160044426419510060394803c060300c1c8204541d40c02640185290581801c0c020119692901c40e070044032125400342c800b040e16000c061002c1300b4140061980700e03013580300800040c200790700c40a41d20301035400020144000030002c42c1e45010200401800c60a0040080d991a030a60f1060306403c8001d030351100c1c0700881c0001203a0075401d0b03465070340d048c1c1b07801c141403510b003150207400c01c854404003440903607800300c000c0ca1003082d6071402e1045034842c04282c0341a000d06031510000400d1600c0c1541030520340d80c0b5161403600603654404619044400036480d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 919648066 1250 919646816 919646857
    0x23012a020607080a1701081c0c050118152f07210224061f030e0715080f0c070605041103011d06010510090b03090c090408032a 56
    0x440d1180c807030010b0240400790003040100d0807650024517046600c1502c0355400641e6038400700c450f86d5951340302280042104032480303050041c0c801c00140520a01a1001040c0310b200611440b0002049200913180c1020710036682c42c080a16001e01e0105131209a03207080a0290640d01c0c52243c16040c0c03102d04001000943c18050000d440110024030009410781009205190000303542e506a0315500c0200b200204252b500441071b442040d403186501504501c9802d00e120041110b0108600720f5006140da11581e00000b51010081c58025200c09440030125000a100c00382c4200c0d402041c6c8000d04036901c0c10011200f141c402078031030485e03010300040780f6916a85040180c800d16920a15019860160b1440d0505406500f0051018611054038a540d88034030a2040b400e05448850703007c00c10303000c0c00308285da03004001140d00040f04070680e0700d14030610000412040c010741d0142d41c01503021003801506149610301d000d002504008180441c02800560710250040c14916161103030700080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 919649316 1250 919648066 919648069
    0xe010807230703031103010e060a05040c05030610020118150b0a060c0609020a050612100b0a0516020303040f150305131a06010c0503030c220305060c03070201060f23012a02 76
    0x1105c0c6440010318400741d12980c640740c074424850b0b0101c0f5410301c0b0308181d51b4000307040d003483c3c882c020b1048541e5882074a1a9156002c4c04294455281902c00710740d82e6071a9800000c0f01c1e0591184180c5c8500e060ac0c4480402014000a5031900c4d03003210321481c1030640c10001c064014480d000c0056201030045000c01c554000076241074519480690400c0d40060280a40c000c218512841455808810b027460b5898002142985c0182c20308075000c0b941c10880d032026801d10564141e529440101103a1030603840b81808903c1e41402da01c199000501c000b9050b200c81e805015035035000c2e185854541c0c50221030386590040d68030000d00d07607222011200208ad501c1c0d2048420010300c0e9007101c12a0741d00d0420041071000d90344120084e204207142c0d0307002340110000d0b140d100303c00c03241c000c0014845500d034124181000d070300203403104d004d640d13950034000f8410388103040c01d10003068000070005095511201e512001001400814100001c6640855040b0200c8040c00b2501a03c0031507401021254030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 919650566 1250 919649316 919649321
    0x1503011502210a0f03050408041202030a0f030306051f0c03110a3905031203071e0c021305072f0303090106051203180f0f09070e01080723070303 64
    0x102d401c42c6440c2c1e841c0d14840081c1050041100100300c0d9158108114000070407002c4580565004208060800c010807000c0541e08902801c00d0009081c0c0300f00e00e0f0710750380b881c52038890301f4030440220b03454000812540ca8500480d1404c45482c5040e070b0040342515034010919190071400605012810400050510301002200d1a0550040d181e1100c01d481441504d405020040444003031410300b543d200d95819009822422070344082d0081180d051032032a10241034100911400402043c0030410225280d4840c0c0d6004c2074072140c4690002200c28018032402c83c4150102e100702905120510130101d07407060561103500b80c054015884510001b007540c1a00c0c0403400c2d4400184004000d01010b00c406500420465000300c910120042804500c035072640100403051070b030710712154925026420140071002846c48001c1043c8400c0c854240040d5500c3c1080d5410750000e48040d800e00300d29608640380a0f0801c3c07160420340c007400507445100d20451901113a200940801140050806000740c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 919651816 1250 919650566 919650583
    0xf0702150a05070306171c0203040617070311070c080c090405150c040506070b06031e0307032105040f05010c0206090703111306080d0224060405180f0a0209061503011502 75
    0x161401102500000e0596030042c0c448207118040065120b0101a8000012a402c5450b10b0f00c42040400c500c33010710818050042100c4145901c0c1c5201c5059800c880c1d000f408a148074680110030141881d5505140260304000c0600406201c8240800701303000080b01321012114810200a81e43c1c2c084c0000319a004690105400c0f190200f101d001f08103000b0b502501c05d001c02c0d012255140100041003260240c40038170200700d42c0003000750a001c02d10079007411051181d400345c043e0aa0103808040412100101c40507201e400d402e49110f01000002e005044100721144010616030810380c07030450725403006200003800040d85400741340e401d448080e00c044010450880c100843c03992a0f200540b90f1019102e59070040c001e01c94130500c02c440e402c00543c4180408440c2010715914101408001c1c0005042219002168008507666100c1000300d80107080c04c481c050000c4441c284103129240801404c1244a0100c801201c50800151070030780341145c03403900308101a803401000503420203042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 919653066 1250 919651816 919651829
    0x105091015030b010509090c09191506271802091e030606040f090204061409010902070b071215030503040603140c0706150e100303080114090a110409050f0f0702150a05070306 77
    0x14030202b0030400c45411119816205040341800541ca0b0715200b64542c0380240101700201b1a800c9405105001a25210920461540300d1401d5603403210f034031903103003254105401c0c0305540000c0c1480c82c1d4100b198103000104103a0402c03d8103214a60000703512190001c0c40c4a01581d62607400304182503241d00064041d03500078004129954441100d206100340b400b89590140580350f000141d880c1040c82160041d035000f110031040b42c2c540c16000c458022003148059406900c492151040300d0000c0d00520013188070700300840d0784030701d0081e0103415696203c030b09800c0b00c0e19003020044401540c200300d46000b540a0800200c01d4581c503403a5180c1d00142d0400c00c2140710101c10003440c0c0385d034403101d10280d81c000d071215086603032b0350000109000301d000e03019a0044601008a20094400e8101c0018811012401410107840d11080400c4513012200d0942481c803007014440380d01081201203810007040d00c0541b2000388060071800c0c0c400406010001c03402c1e030300c400103502540f181d80154041d122 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 919654316 1250 919653066 919653079
    0xc020609010c0812010f080a0c0e07050712080105190506042c01030503040915080c150d0c02011a010c0302070e0a091509053c0c030105091015030b010509090c 70
    0x740544e03807420b2510240900c0100c090b4030308000c07480500001d0320700e015a40c043c406466041c10320340700760b14841c006800c0ca014818103014180c0001c2180c48003002c1c0c030900d036440e800c141d0f1400f000c0000f80b850b082c60b0000d0707001007508148025181c00c000ca40030345040400b00c50001c241040c2c0340c0e440f0340010030303030f000071004402c004020000007000400032074031580d605000e004101c140141460704a8806d810103580700400214440c100002e42c4510841709141c13480c00e214000b0303100005d40c0c407014031080040c0d540d54114800c10140309000c1010000c03c0c078100c881a445942d0103903503144640103810b1134200410001e42c10408a4001d40c410551080300d01004001200034540604042901241e06010382c10440c800d000000c400030a11609805c40c881d04040c0009020256003403260b4201080c1c042c0079031540342c545003402098080c0000314018841030303445802c240202d864003030301c001046d00301c6034040000c104890341c0203064901c104e401b5201901c6080c04c04d490403a41508050b00080e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 919655566 1250 919654316 919654327
    0x60a050703031532030111041a1801030e120415020f030f0f1e1c1406011b0602041a0301180c050403030302180405040c151e0509150f07030912030c020609010c08 71
    0x947c01510499503084004140c001d0441141225401360030240081c00e900d04010550303d41c4179800010001c45424180c42100006240b000b590b80e019411503c1180f6200e00c0405401c0d0b8100540d00c0c2c420300d580e0141d42442e0045840381582e20840d030000380b203010089031018048221030201c0001104800b621680d030204401c00c14406076400c25106440c518001224031583e00301c083d003902c9810169500a2a41c1c0e10b10141a07003400625001c0d500c00d41d081c80003003006912049041044810040025103940c5032045c00003040380740380030500d202414565509101d54020054074141ca030b1609002d41c8800100c15041501808040c009a219041c003042c88213100702c10080c02c0030707122203114003902084881002d030b4443c0e10448400003040c1840d11284006d6202c0d001404a91030300425018241100c2e4041031140e40041282c88901400010484100368111041600a00102440c4014101151000380080e92460320190180038009228201170b80304240340c1c0011580f1010060b1a407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 919656816 1250 919655566 919655591
    0x2090a060e0102030c01091b14101d040203041104180b060906010302120a05010303120204060525020a08060601080f1512011d0c090106080408070f030905060a0507030315320301 78
    0x40000b82c60300301d901d034650b40001c01d2422440e40a030034409d82c0030f8061001035000c0b44044880591400000c150500081140c2c052075840380002c5002d00d0103008800401c8503218200b00c1110200b18007050701c0c1d440e5000290010726401c03c2a03501010031a0340742001d03503400c00140c1c0070388074040103240b103407400c01c1c10400c41c4001a4000c40c16079010b81c0d107000a83c0c146544000880c450780c040c01c404204203010075805205803850301c0498a5031800d020340403140035400b01c0c2e182d0182d500b280740a034021108020a03540c0c00b0303814580c0505074481948103030410500002050500b44601402452400c0c032a95080b44250031800401410700e18010030b444401e5805a1038010740b55426200360070b540300004110b40b00e6440c0b9805650450343d810b1a0000303680d500554095806000c40030700c984130000048594481c5c000d804c03040050b8541c150f0f202e1040c6401411204a0704481c0602101501d080c82440050010b10305104540098204040f64160b00602c6030a20952f4076a031560804070701c1e1612 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 919658066 1250 919656816 919656833
    0x90606170c06040b040e060a0306111806130302040207020f10020708150c09220504030822080a030e0109231c1403060609090103050610050402090a060e0102030c0109 73
    0x300184600762184001c0120802045108a103d00d200400040c80144152404540c0c1d43d17070014002882011a242e40340e40700001d40e5007942c3d004855100105002c06c001007080580c6c10403400448800345400a81344000d8000296030002038080caa001c2414021501c5686030701051500003013420800e8200c28030020766a0b01d05020b00011030181d04004410300700b10144840c040e501110340030303040060030320502446000840c2c1102d201c0250f58000324110302c1c20300c00c10740240c0c000c0c1c0e2500c21620f066080301c903800d07401042d2201103049041d00000403a100600b550411847c529001c00c000400d002494050101c400024050107008001d07211003120245c0c03d401e01981040035650100c01004864050384140d10300c01020030407a65404121164410003168003080013410075041c840180c0100781481d4098100312040d5210b08240813011003a510540c004200480e07040d0f161010007000314081d1040e5103d9030060041000541c65140c0c02031064541c0c90244000070045d112041c10b0605d032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 919659316 1250 919658066 919658099
    0xc010903030e220e0d0509030c0114041820130e0c04051e100206010b031911070c0306181e050109050d09030b0c0a05070b0601030e0f0c091005030601090906090606 72
    0x413a00c01c03855000380741e602940a988400380010003426000034108015211019020200740818604000105c3c4c0b40c0b000f081d041c0b9000302c41c1440050b01205034a1217030300c64600c4030207039008a5018400b03034038801e03594460035081d01c8242c0900300051b03d07000c0404400b8001d58002541c440403c000c0000e40d818900b10b1181543c1c000c880300030b203400440900340d8a0340828028140024402c000050b41180c003500d42c00040170502a001955040020805100307402500003150082118102041031001c00d0003a10001c0381007e0300c252120101d903451192602034600007038180918441d50074103102007940884c0000d50050305031404407052074001001901c96000446010f0702c204081040021310900f40d43d0740152a41b5418a024415100c1c0d055580d0001c2c520350415480d07031225000203400348850021391200b00f0003804068030b9441040481400105010341f8004406410011607800094981c1110b0b16045d0000740540f49052903c0904001d0b80d0141100d800c013480015034401ca40043e00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 919660566 1250 919659316 919659341
    0x1a1e150d0b0409020310111e090a060801260c0d0803041a150613030c0b0705011d0c0603040507050d0b06040b01030c0f0f0c02041515020c010903030e22 67
    0x2100c1c8800100800c40c1e042c008080e4050380002c000b194941060380c0480f00c11101e10001c0c6050200c00341103040070301014010090858004150600309040c0314080c82d02911103420501c10b9581095580516403c03180e121000540100546104904013408a00c1c10400e01030000305041009050a681551060b9400c0b1001d2000860309c05d5410103c01240340a0081311000390307000781c040c07070412000740c00c040c189030805500101d000001500e00003204000f807000750f04490b140d8401d0f091203406c5814048200c1c1071a8540c01011803d4840404c0d604046101102c81c0d548075211418003502c0c22083e600419001f10403554201c0500c5840a103c030b1040500711010710050000400441c140c071501400b0801156440d00d41d140d00c140102c04032921200c4514154070750f1000d5400103000d8a40c040f0b40502050540700301401004c046c2c0822102420342c0380002d00c480c0c83c001000801c120400e1102030100700030020240b500c3c1d45c60254802c02440c4c0c0041c80444286901c42c4000100001400e40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 919661816 1250 919660566 919660571
    0x2114060a20070b070e1f08070201060905040b070c031101020705010f06081906020f12040f0506060d0b010608060a091b0306050f06040306020d0e060a05040b010501031a1e150d 77
    0x594000180001c440c03606074000d104507041d44544130260784403092100c00640c0a10f0304894038400034a900d02008401c07409036115039003030a1000c802390841d201a000620000d08000421000c14280d241142d000011403504070304002490408940040350340340b45800c40d500000310135043c80350541100d1485000c1903020003c041c0d4404000350b031083c1e900456036105103010f500c000072075081d81c05001e2302c000000b180b601d40250080518003405040340c0c101d8440c0031005852040c131004102983e4045001c1e96118103005654544013040309051103544108520bd80004902303443c0d101507d0014018040203001b040100503000a00541c20400000020302c3d00c4400111807410242904480102900300e515050844d11400c2c042e41c40200c4114021761a81d1160200d880104140c40c880c0b92450000600d40c02c0c80d1401003d4404185c1c0054101405c004404d0089940100b1204403280110340700c1c00c01e1480422883c0d00c0a450291042c4d0000c405800710010b030b151300300184054000040c08 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 919663066 1250 919661816 919661861
    0x31207020a2103060b0909043507060b010504240c021503040b0a110f221d06030c01081303200d030f151e05150903010507092114060a 59
    0x21400b82d03002e40321b14941d03c10070043c04031303001c610701c0107610034082002814000410b0040b0010403c0342e00405c1c0340071002000041c00c00500800d131052001f44c102c01d1a106261501c0c102d41c44811148400003a240c88910030046100780e405052500c41c0c403580138141c103403800d0740130000c1000c0c0d820848050302c0c1c115500001441007110392103003403180c0700c0851001d81043e04986c01b05010350071084101414540c0007250a107070540492000008166000c00b80503000b07401c8020284030f42d0050003090080c8d201c1b04d518100c51b80c0164155900c600c10302c1d0300340000030705400d08030303207440400034041421848150718211812021480d00c203524020b407810701c0848500340c4610100c03000700f102c4207180c2419503800d00032000021152203144000100c1c1407503040d218000101031108103055000c0c100e200040c00e2440d401d0a0040503445019400d1441c11249440c1b650381100358070843d02322043c1c00310808141048070042100c01c80d000440300320707516850002c0021000303190741301c131140b90b48107010392 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 919664316 1250 919663066 919663079
    0x30b060403330f2703090902130f0b04080706031a040207021311210c03162604020f010516080a1808060108210d1a0303130603050612031207020a210306 67
    0x1800404d00ba45a510761000d43e1400c0b022070020b403c000d0b546501c2e8642554001219180741004502800c10040c05a5440b86450099498485194070000a141c2041652145007180c00c9917080211403e840c0541e84809902c0029516900704840030001c615000c102100075594401178008000c00100351059100040d4105118090440384040421410000150749070981d00091000081c0303410b102d000d4a1111807400c035a80d03101341d0590300742140d02c8100019407804210404501c0700c2070802624110641840024055150402522541001035043e083c1440341d040441c0d09440090790012040e120001140c4a440c00e10400705903201d8801859a4500d1044900f00c000c44102c20251034040c0c40d4003500050b080050804019460045603141d641d00d0034030080c12040f69582030f04240710f0030320501601304c84014003454040d07080343d4442c0110f40380000403201160007a0070030074526651340c48202d24021000c0b60041003010b041c000b0701c00d079912a00ca0401c19064a07201400269200c03407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 919665566 1250 919664316 919664381
    0x60b1c060b090c1606150515030a11030420010509060c060402090a3602040f0c090807060c0f020d06060b04140301020a1d130c020a03030b060403330f 66
    0x30f07201801e00c00b010f568000140f175690045421514411442e20441d90300c40004003c81109062400452000002c000c01c0d000c1034418011503143c3c075445141181402d03200e46c2441600a2442d024918503224030a0701c0f0f038003807002d80c1d0138158014860355603000b00900c02610740300203a030124001c107403a1000c11503441030341c0200b15040c454040031b00d07128032112000da00c00e00035130a0340041c00160304280c407025072614003032b98102074510740c0003046642e40c0c854005c2098006500c5122560000e500070301c03006038000c00c45110281c12281400d0042e0031400025981e00380304070b000300120b2a00c080014001d01e4240504125800200002d442c10400d4050500342d02c1841c0080b00040d504030040c0380d410608181c4c40e000030748045d05104070000c1c1040b90a084448007040880940d004c0c4d20440209a4517014007001d925059400c0c5040a10355030f01d1103022008203180c0c007410221603100080000349074004c082d2108260b0301c14030148a1006e0000020401c0045210302c6603000c002440807003000d40d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 919666816 1250 919665566 919665577
    0xf0a051216150906020708090108060f010f05090303044403070b090109060903020105150307030b0606031f2606070206010e090c03070806091c0c060b1c060b090c 71
    0x708072507415000d0540d02d8886082d25215000030065540a50034085901c610203041e01500c948585903407168080d0000d09031590080203e0b108444801400000fa6030100309540003800b41d081003038445c07108000180c02c500850704000c84095040c1c0341d0459032080314001c616401c00107102002408105549030f03c2201c0244030108944e0701c00c002d00320024544c080c2180d44084544000038030325003d6641c1a094a00106055005079100c0c1d083c088141d40b08035014031403e804a00a052007407856a454410450040001d880b58030040700043c03400305203c0342682207c050014613a0303020b80750380207040840902184076400c032842020000c080f980014026000708480c1d00100b41d26131800300703408039078400107101122500400344e0003856070f01c0800642e1301030842c03503015050501d0600c4019261840000d54821071014400d1f04008158021600c2180349030020340100307035859940c010440b040070b42040309105004544806044c080306600c12505110116080403481c0c42c0e00c80800803d0049 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 919668066 1250 919666816 919666837
    0x21222020f041e090c1d060904051e0312070c0302060f0a02270907050a0f050c0109080409050610030501050109050405060a050303030412020d090f15020106080f0a0512 74
    0x4880a020151900740c9064a00050091010504810300b0001e4200040101c41c0b007856142c407070070800e0030407110a030100003900c000c5190b400b507441c06881c4401c4c8040c02501080c0070b41b14030307008642444400d00800e802d40031a180160000b982d81c0302202c2c0e8079486030a00c01ea00c802c03560302040e5031510882807041c1083c0c241c1e0040c00507848841581d1784041010f40200c2c0b2855080008182e1243d0007441c800c4007080c584041626002c0d000c00f440132040c0020030f1001044020040b441d2100d030006101080d800441c90b000e500d40e0a0901c14a00400f2130010142600c06c001c140001e120110742c00040c400d001c00d840c41c18540036080400d80503520300b030007814040b99030104180300d00d05040d40516444400104041b950035941c40100c0d08603402600d081d2202d41b00100305112003501004901c80c00c80c40e500d481800546040241c01442005024403155001041c1e80b00703502178400d4001001516105081d00d0042944140d4183c0e102c80016003143d45000319145c030485241c06a040d5181c2c44071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 919669316 1250 919668066 919668121
    0x1a10080c090a180c1226041502011503120e010c11010509010e0d0326060604030f060207060c0f030608030c0703060b01110109030302041403060403020d120b130212 72
    0x6440e00030704080c040d41c100e10300101e0f5406001102240c180383d1a04010b0044d2805240d0103041814003980885072101035003a2403081c0c55201d10044106d80848048401030503004250034a0b8405c22070141030000030b4052220841074000c014020074030301d1901c10400c251140d601c0750600f40010740d69801c550700050503220300c4c00701d01c00d0b4550088005008410051500800143c00700c4006100700034113820a6000445084140e2803d440d48451081c000c04005e00044142c0780c000002842d0340f0480c04000c1a440c038850066081003180c3d0180d40155500c00014021040356400080c5510f014609000c00039041c4800002c08482c00b00889100141020250062a00f5510b98001810903508220304220321541686400e41c0203105840705a44255030150b0780d50302c0d00c84140f11030706603028140c0c4290405820f100019070000381032448101f160030901e00c1684a0418200180036400080b60040c10490411070600000c0c0d004020403c080d0300c070300400703803241241c06c588508200c604500194 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 919670566 1250 919669316 919669321
    0x409091e11040b1915181701050108030f030a090c0815070e0f09040807030c05030d05090d030b060a030915020a0e030f0604170f040b07030c0215160f08071a10080c09 73
    0x101c02001740030049560307003030000714000c10702c1c9405512241c6070311424400b80314028854080c2028001c1d680180344407002103041984401100b42144405801c0b540007a5a03421031608000d10f1900d00f000030204a800e40c0c8140c0d03100c0d611a030044504442a2002a24005142e190751600510700014142c02800420b01a5641d5982c038040380c0c0503081c250140403d061041c000907208100a0140d10507441001c1107030300b000e160f540d282004042d11841407504002c60712029840d40f0040d10340d401110720f80490718082c1e80c20b210400e640340060b040180c500018440003c10380114441100e0b100075002c6941002d1100d400743c0d1110025a80100b0400007101d85018121941010b050b4041c208143c6601c0e1a54682102c0c0044d40f01c441d04501086a4485010035850405c01485a01280f2003030304d40780910810728424413036042c1c40001c007803000a00e41503080c48801c038255031700a13501280c3c400c0c0c40a00d180d0004040c000440c5d103940a05000741010600c000045400c1d591040050b0040c034094 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 919671816 1250 919670566 919670579
    0x11a03040501020f070c030c2c0703061809020a15050f0a02030903070f03060c0906050d0f150e091e031603030b0d06020d0b03030306060409091e11040b19 68
    0x154805801500c80e903400784a0f00030048000d6004081c0207101c2d42503c03500600c1c510741254001e000d903205a441c2c1e090004034480701d8003d20181c080303100100c03600c8440c03585c0300d810981c0200610b0308007551a82400c40f11007901a440c0d0f00c4111662b0003110000f079248d03903902c0f0032098030707812030200300001e42c060088802040c40e210142c074210400e401501e0034402001c01003894984603903c0380c1c00e4004020400c2003845094410120034140524001d054141040c102602500c40c640c030b009911a0380b212052481c00340d541c03006130407259594078000f4403550b980c10103514010039144919a8003404080e030a201500b001c4881100c0002c8000d10f0400c1802142608210f051a60580078103031260400f8196507a68280781e000103100c0d590050b103a00e12110160110380004007014000c0c1e0041081c0300855851009840403207044138404110700c10039180640303a140340e800c1c06d0301160810b035012408100000e01840c054610070b548c100141401401081210141c1180051448000c1e60b01808403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 919673066 1250 919671816 919671869
    0x30409020912100507030e0613142a011106070c0305031504091b0f030f060c0e03030409020a1404050609040906020c0a0506060a0605030103170328091a01 68
    0xc0c1c100081c0312000c1c419a8611540c1042e0610054602d0741e56243c041000503501032103600d01440140300146510300d0f20243c0c41082c403510b072001038107801c614441211801c00400c18090001240c3d10381190000c20341d1b910180107407907140454041490030380e02900e452800103202d80301d16078655403100c104445031030940d4250300c0a0304604508821030030500607516207014030390754148144860185d03420000350444401d0069007201c02c0084110341e042000c203064466010a85800007000140c0034030701d01050f240c41e040a4115509408045800645054032b540580324a8102d91102c02500e8100000b42540f84198050b681c3e000509000e000e283e81083d51208030a9803260303000529000d240c8210300d150400d0020100c5441d4071450400413603003049036641008184e00e050403801e550455039404081c0300b03802d10440c000e800203c0002c4003509464014200010740e20140c210350000303111b09801400042209a5100d00e000c4101c052000c100c04066048540606100d00c8035100003004409 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 919674316 1250 919673066 919673077
    0x1611120f04090603050c1206070e06030a0204030b070c1a190b0312131406030c032406030c0304120f0912030314091c03150e0402030a05070b13090e03040902 69
    0x140c10000c0c000840c1c402002e12522010394010401064411340c014100701c4070000400c12003451380c1001c41440071540e04102e450759140d8040324507548990721803110500070701a0358005401d800695003400442a01719051038000d90064030440b68008024184040c1c07142d041c0d80c21001a860b0040c12040c58956a104c10007403407000301900c010280d130000d10071464114001804c05410180001c000100804c0018800c251003510745600b03614003441d512100d03000041001c110581410340c23204440c242c80039106803c0314000c19045e00d9042204590015802c22139013210401000d6542040703590090408034502c1e0540d58030079a105007813071030309007526030181003c0b8181501c0d00518a504808070903418401e018400c010b1051000d050002101d103960f001c500d40c10305180031881d0003481c0710b86608005442514440c0c00880e100d40c40402e10381801c01e4005411401800e03004540039404600a0200d01201c001148999444041c000c040f40d0400340724000f40c0d03204020400c903900b041c0d0007404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 919675566 1250 919674316 919674337
    0x60304051c05030114010e0303090f0d0605070e210d11100f02070b220b040311010203040303050603070b120103060b03210c0d08010e2a070506161112 66
    0x7101c00662030307808901c04a0840704000895030200c018816986040c0c07004034440b10034a0080000300094012070341340d02c19050740602403035030b40c284c1c50f0444c2c9850102100c12035015504004914080301c0c014460f03117003044e41520401001044074182d150806001c2140b03214100138020b04000c2190655520100d501840782ca0700502c030006030104018403030040e406030306250240c0da84141e031070801c0ca030150044c80070f601c0741d030741110800501103004800b20009a00104001180c2c4480c141542e03007600184000c1004d40c0000100400c05516070800c0d40a248150100c44032140c0b1080501d0660141c6031110250701c00182c01000810440d8010f03880f6500050140d90707018030050300c3c520890054501c00102c56100003014264150300704202c01154050b85000031042d4100305e060b1401080c00780c4110388201e8011000b101c0c0144076000c0900c40e031800c540b4555502e010703241090310f9001c00c407240210300742501c3d85491480e008800e451401c00308440900400e008118040e061030300b04c9080c18 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 919676816 1250 919675566 919675573
    0xf0302060306010c050120210f07120b09070c0b0105031f051f030308100608070e04022109010e1e0c010f11030417060a060510120b0a0605071a0f040206030405 70
    0x1680c07c802e1011544080d1a04480035558950b02d00020540d086c0211170460035401c030490402c0014400f640484d9040748080c50021840c2c298020203001900209401d268003000c24030038000c00503013020902061714032a0041500a82ea01c5041589816040f43e40551150301040d02c00b1a14107036034041c07548415a803c442242d00408054500511084d400403400304506800740b040e80c40d40000601d004020380c0c500071440c0d05d0016002882c102d0021001390240b030f00403036000920b958480744c82001c401c858802d07040500c0c00e19240e60281464040d90f11141c00b40702140e8003903018010314000a504000002c022020500004444100121620000304401040202c0f202da20a100400040074500118a034000c1c244810070b040450180c4203100c400c0c0b81c20410005a1110000030310445068140001011080300151000d4103410000ca6070150004101141d0a50000c01910074103000d4010000f54602044d24044400710070f58030002d8603800080020011300d00032004540c03141c4500140d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 919678066 1250 919676816 919676831
    0x2181b19110c0a14130c08040308090118061a030d050d0b0402070b1f09020c160501020a15021c11030115050708070809040b1819150e0c070f050a0303060f0302060306010c0501 77
    0x22030451b46883d20400006240c54140000d040d8829800c0d600103401f0710082007220703221414003481402210700102003d40f100303007480809192a000c4007814801030f0035038819601c000c1000340139503c40d00856111a140021920450038a032003516030700380e88041c04d038240e47c9400d414412070748400c1005580c9810107840c0482c2c100c501c1d001510080001e000240079030600051180103600c869000300c1d04544c015003095001c503042c162005013459429000507980c08199645154962340c922140c8195410001d00c051310000680086040342c0981c40301c0000c9148501084485215242014284c200b041c0f15440120300180d00800032004010400241104901c1c0441c0c07052140c101e00004242842e03041100c5019070081e2030008643c940320803c000c44034034a44500f15501130084106442c2c8010002d0444080382c011900c03040c0e00500710440003c46450100d0b41da100b0210124000b900344000000c078902d024020f8015240c1c005e181d5800e41e40c586d4011070b0035105115007981c680d900c4110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 919679316 1250 919678066 919678099
    0x40b0d08040609141002251706041101080403050f03092b120b010f4a0d0812100e2a040302181b19110c0a14 48
    0x1031004000c16190f81d00d2161400400e541034040c150445030040d25040304c04c2c0400c59002c24080000030200010003d801c3c1160660f00c0703a801280c0001420a0708034040c007038894030000320544500d1160300400c070551101001140c3d440744c140d800902103034060115007401880d0002443d4490030341e200b1105100c14540d40c0d0503402c041e002141a00320000a814840e49500c140f101c2c407001c3c2d801405110304c2e0000b1000a100d50782c400d03406400c0140c1c0c0c4014a41185880c604101e0400c0001a07000c580c60003500c0485107440b07044401480e800f80302135828078505080150aa90702d81060040f4180407541180400c0c804e0014030a240c9140e84039008129460f0501c942030240d030816015071024210b94000d00d280007400103051001c190140310404c010781d1020f6040702085007010141100f51140300c100707102000da54151035440c542c04a030328000792800c2d6209003521f08041e541d03c440c002c807806410740c645070042e1450341c00490400040c0242c503003050705c207546070714040c2030351014014882c1d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 919680566 1250 919679316 919679333
    0x109051c0807120e030a0e010f0212091c05060c1908010b03010303050d0b121b1806210102030a1e2309150906040204050f070c02150d14010305011a0d02040b0d 70
    0x1911b03001f1131101410412156480001086a000140020404050741c1d028800d03d03402103501c1c803031144d1540800c2803414410000030000d4182d10204880090070401c5206425800c40205007507507508411920302440d10441e4240d040700d46050001345164215181143c0c1c50340700981c004500c6803034410300721032a200c54485003d00190140070f8820020200344410030710b8000e0b10130903c00ca0081c165085020384c10515980c110604032454403100551280180584011681e503900030f501c08070070011242000e0f001194203107a04440509064041c1035030034120b654102c0c02d107030b0380c0c01300b000741a8140d48801c4003140c00014010482e215403c1504152841d0329040701c80e03009030f41264040c00110308050160725000aa030000d1042c00c0d04d171004006000350740e190360180c0301e04005010355032140c0301d1008442d80c48441c683c0078080381f1f2071071507500980c09003848220740710340c0380100e1002546c840580b2400e501100030109840452a502007101500000702005d52101c00113003050001130109 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 919681816 1250 919680566 919680577
    0x3030507031d090712050108010b0f1e120105060a061d090606271f02030a03050406090204060e0402130b011b021201180c09060302010806300109051c0807120e03 71
    0x6170741307001500140012020960300c041c3d00c026010380c1840c6100600d5030310202041c020b410305907003000b041c1400342c1892001ca611582034540100d01d68204000409040d00002c0c8206401da445000315940c070201120042c1c10514100c102400180c5003c900c0e1410030041178000c00e000308040e08046e804142025110004207920106074881e911700c85041c01d1900b6a01c107442c00c4aa00662050b0710b10344069228410748041174101907130380740003a040001c075903c41e034403164002d0b10800c8002d0b00c8650b010013218040e20141e01c00e0743d41007090b95100b5120f02038900d010300d06035244107145192003800f620340071035020102e07441521a814220400400d1180228248641749400d104440d241001070100295401c035040c40e40c00c1c0b0383e003400941d030800031301d0b80c02003020303110030580008014100f514550340718161400d4805000314041a03050540115161502031781c10f40f0021000703050035241805070005207501080719800000e4241d40140100c0c130303584c6402c00010500c940b4009450341180d22a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 919683066 1250 919681816 919681831
    0xf020d02041e0b240c030d060308072a12150509060601120c0516020612010e0105040b0a080c040c0c050a0b010f14150c030904090b0906070903030507031d09 69
    0x190b06207061002514050310300c0c1d5100c143e030b0002d140c000c849000720040c640b40324040d11000c1c002450583c08401041161400200d1010400c00c80c0c1c2c41e03141c41c50155001c0c1c3c10643c1d4040992004a0384d0203036000b06441c04a410540301d0314818074020202e05110b004210580340300c01801d120140000705409014850f000070400303041c15242040c00908100e13038101ca445042407030724000e181e9141d08401100d082c007141640e07940c9000e0091000071428401d02c459440e50f003444100002d885416060720328180d807400ca0742448900e4054060080c8500548590b90481c1e20400548007642001e80c40403074942d921b4508040507400b151209440e0681c440300448403a0003010041000360350342d04601c00034040300c100c0303c545140000700040c289034155aa00c0301c95040010000b820303640c204103c0310340c9200a0014480070740da505000c400140c4c12a01c1c4803e50003031130009042d2920504284094941c561a0f00713082181e075860450343c2f881c4036211441b18000404024203540c2d94074031001e114070f20b03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 919684316 1250 919683066 919683101
    0x8031303060b1827060c03130c05060a0f0e0114031306060302030313142706010324030606150903110a030c03060f0c0809070920030129090109030f020d0204 69
    0x1103e541404c4110405480c1466600407000384180b0720005411a5004074442004040d80300d10740c28108c48031b203941e03031140b079110200040f030302044d9801005000700034225840341d080181d100001036504810394900c0b032007140d40400026070000806002e4000c003901900c00056801e440340d01091842d4090a90440d9810120300100280c1107203600680503942c0940701c962072425411440200559139000703038070842c10820300252039a4801d90200440480282034051110301403040000c6021090100b501c030f160500801103411800110084011a0240d84658002e4a107032240c1010013090341415a1040410000002041c00c9020315070142d0b000300e000090741c0d6456400305088841d0b110384641031103d04020841c2d19940803440f0710480702050700204003500791011182c0341c1e5650000c64140400c01000100b43e0906c0d14450f562103842c142c1c400d1142d0403051404162034003440d8031103400501030050034400034945048062001d403026007045001d524640c00241941c101c010010402e25 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 919685566 1250 919684316 919684351
    0x61512030815060702090c0304020112061d2a0d06030606031a09010605090604110702280b04140d11031209031e0a0f05150a02120108031303060b18 65
    0x603120542c0c03402d40b40e42200c1d100d140211030740c041000c5010042c4203001c07aa83c040005010342e40518610382c44c0062030b807020080181c03a028284007032004c00307814444803210040015100340f01240c5014030540c801401000f0709005080b4040d140d4401c103c00c0d03205e26100c890000000740d103070240348040c6214528402e00c04080040d007052000700102620041d80c107142c405c1011751610300750590445402c1d900443c441242c50310b1300c0e005108801009421400f095891051030303008030300d070703220ac00b0900001034a41a0f803010400d020f800b65004580c0c1404035a035020010f490002d40f480354091040c00c1241100c0d2850000905150030080508800700c0c002500c09928641804225500300150000000c2d4908004d80c86594141d50314008111865840452041c002e080240d903030098032418429406117002c9510310041c0d04511000741401c0e1000c0700101c3d50813004016514800100e120b110b41c1286151142005004c80b1041560403a2500e1040c00e5031460f80c200d19441402088000500e80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 919686816 1250 919685566 919685581
    0xf030901290d0620071103060c18010e010309120207050f030a080409020c0f0a11040b0405010518150613030b0106030605060409020f0f07030c032a0615120308 70
    0x11a0902041e2850310000724110010b9507101d0110b10000c0d04103000150b10040e001d0020700300c1c0c0c1081001320358400041400020842e07070030100b8000305000e0301911340380c0d15072200c035118500034200581d01da081c170701b022591954460000591406014903001c41c0024160311000d01820714071590400681100800b0301260900c0e4501c011446425801001c0142c00c98070b41d0f00036409503005080c0742e01d4001511803803515042049486d8843d19005480d4070308002c1c9081c8200305000c0880d240075a00b4881455027a18045c4102c0d8103c489c0686100e200f0a0181000c0d8140c6800801e801c201c40f03032211240c5455204c4501030088919405251000c850540c05c10025244050f030043c001c02d400c2c40020310158562100b610100c4400a4001d40c42e58410074180006001703400d40f28148941c042545c0091550180245c8043c03030003a01e8141c0410400c06141003100030322003400d042d07808000b10402c006001d80d8401003050958445c0c0c0110740c0d4945880100c002401d0703105034009200c03001030040b00e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 919688066 1250 919686816 919686851
    0x9050309270f0c160602040504110403030806040501210606030b1306060e01080703080c0c040f0b330a0c0507030f0b0f040201090603020a0e0a03140706052106060f030901 75
    0x4125101c0c41003031034043c1582c035061080c1d0140185600d01d1895400801c030413601981d0140400500601210704492003109480d000380c403081e00095070710000310703466003002d11900e81a50300840d0080607030191686407503085400c580d411103240303664600c00400300f1404007540b400350520b4045551000349505184064544640150780000c040d50010000103100107901700031a64000b07422512081d00301e00160a0506808249400c503003400c0c281080e04496602940304050100d901d200811450f410400c003c540720003846e920304804081403c004c0c0c2c41c0c0000741c0307101a140e02d40424140360f140d41d858102a180e41c4202c0d440c03500c8012010420a58458881d0311030305c050f0482c02c080c90b2580000300000303200d10800c400c1c182e00280e8004040c0c07280d0340c0010384007005803079800315035600c0c6000c0d16064040c12040b102030051503008600c01c5e01c254115070841c510102e401c3c0f40c13031502005400240d43c000d000203511400800240c0e0300d0000e807902540c8144100000002c041e00c80c1001c0220 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 919689316 1250 919688066 919688071
    0x306030d02010e060114190b07021e0306180a060905010c020d080c0708070c0504020a0c110612191407230306010f03270b04110a0803030a0905030927 66
    0x6690508144a042c40c0f00003031020f0449a00d8105441d80344500030100385da0203002480001040f5080101082e03a42c5031000908026100340e4032103d00e010495800c0c9030b4028503180305581904800046a080005d084100300403120078030a403982d51140d43c0d90070007250130a40e411136143e51a80514082d0b66014000c0a03103404113820310880d1454a85c0e58200c003440f5124000b441c1c6000030403040280310903440650050500a0000c41d50b81040130b4000d1b01c58100e00c3d104655029600440000608000d0291a031002c2480c12200440d1545100350441e00011030964868507510f00b01039020421500c84180919040e03151810203038224020a103007400d42c0501401001800c10134001d40d641e104005042c502c03403510300016240b1548403592414030b0800607241c60883d0700c10300c003c18041d01d156004d00880c41070341d1112010510744244104101e0601c0f400c011a001400080c3c0c00d09001e4002880d6284140181c030b1601141d1000038403807030340c1e4403011141c1d01d10003203000c0390010303000c03403400d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 919690566 1250 919689316 919689343
    0x305100902091003020a02071a031006050406020709020906091008090c03010606080403050304030c05032205030a050d271d090a150905150c0903070b130b090d0507060302030603 78
    0x14a4a02c0c18004100010710200740c07030b401c0550028501108600c02e00500c0c0c00b80071201c0010003501c03615420450150000c3e07807101410700f40c5100024207103014004640449405401400303600d85094240c4000b03400c02205280c100c04200305144e502d0303985845030102d00b001911281d1050610001c4c1515000c00c0d9140d0714000da00d443c000340125500000015440380c1e01d8644150359a4482c5411980b411410300000c04038400403a81d0381d8110303601c003000d0350070b0020010112241c60740c0b10205a0b80e600705040280c00764102554012807140b10714455104202d22010030f0035140003420003400c802c88280d2085061454907910340c1e00c2032200325074543d08515040010007001c1d50585842e1301c103100c41040030411030307500c6800b80e0401005200c642404030aa128aa04501d041c507c40d40b404c1c0c0c0540e411038070038010b01001150a039005800d407818100b803141e01a003901d00700085c08595a0000d01d01750b50000460800030f0003c1d80c00c22104024144c1c9690250b12403c6c040d0916180c280c0e1440c100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 919691816 1250 919690566 919690571
    0xc2d1005041106070510060b092815050c0304080307170703171e101a0423010c021002012408190609210e0423070905060a03051009 58
    0x4008582d0b1401607541003802212000e640708030910303000e4617100c40c58003d000e0003801c20200050074200c2c10060031002c40c0985079075281307950b201480010a035200c50241c20624986c5400d1000c59550a11801d40341e80303500b003e0f80340c10311030003540c0e1840d0040c0d400034406610001d026020061403148414600310302e04112810608141d07006030070b0150b0401c0040b6a2141d440004003d50700c800c581c4005e00c011945040d485041c840700d804d0300c0f06214085d9a007900004d1160600302e0700314400300c0d01200c0040c1004014240214503400c07001209000c00e038100800282a030005d0b9680e100002c0c170385040b540002a41180030030b486200c840014900d20010040c14004001c3d15401048107291125041c13280b0b031803010300d4580341c1c0c01420b003a140580100400c00c14440c44014203450180f50000c180c1340e48103104144805c100556445d00c0e18200c4000c2125840f41c0d490300c0343d00340036800008030308150741241d8985c80411210b40100b6070000009480e00188403d17001c1a03c2e000c2c0c080e0906032402e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 919693066 1250 919691816 919691821
    0x2806030204050102061504150303081609050105070803130b07031406060301060e0405060303071b06271401140d0209040f27060204030210030b180105150c2d1005 71
    0x3079241c000081c0b07194801c00c00060711108903a1f880c0d0021065588040504072a980c0b00d040083c5403241c00c0301d1075a050f11800580556190061000000b00c44050b5511407800089617152102500050a10f184000022016000240d07040d10800d02c500250b035800100c1020180480b50040d0000c2c04660060000f04010700c12035038444c4403d0b1240c1c0065502003010745070000800c0c9540318040700941040700103a030186842064028030000c0756410396a039420904041d0400f100d092001072040b107244100002040444c1210000e002810300c141019a10004c001900c181941e001c00303000c4086d01e80c0001c0c200040d1805104007840c60034041000c10180000c0c1d000003036000080c44101c0c04108644004800300304068040754040d6a010781580681c0c00380e850060054400003440600c600302100c803024684c001c43c40d650341251401480c141104a0b000c0c4401c81d181c5c440c0d5501c96460184031341c4802640400450390040c050700500c8081d00003020681103003000342e83c4284900c49401e0005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 919694316 1250 919693066 919693069
    0x30c11030915130906050901090501050109030b070509041a010f08090d08091002040f061b0209010501030c0302091f020705011e0831151e110405280603020405 70
    0x1510041541514440c03424803420500306264010f0001200700000d521001060200c0e16411410031204140c031800d4a81c2d0302e804c4010242c1d4000d003c0d03e40011041302080001c40c21070a500c03a006203c0d428010b19020185020074190741070b1400c07800704484101511079155034030a03421100c0c02100d1030450001d0425145a54855109580c003008000c00d442c08102005800d00500a2901c5842c1045640e6a51443c00c041030341028031641010038042282c00000302d41550780f2403052640180380c000580c2c28240190020200c0f0b220a004066080c00446d182e900c2e40d0003003c15140d49165070b5030a480f20700070300030f24001154010b68100b05004c0000310030311200c0c4291000d07140e15030034014059600c2440500d09982491001c4050041c50704003140340082e550341f5201e806001d1084030142040d0100780000380c81c2c4111801c1d0f81012445250304402c5a1644403060b080d070609940d074945036446000a00c1a221800408804041240c4442e080d045000c42440100f02504040d42000e182c0030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 919695566 1250 919694316 919694323
    0x30c06240b0c1f0b0303040e0a0b01050f2706040306090204051b030414030702040f14060a0b07021e0909031c18030c020a03050607050418060e04030507062703030c11 73
    0x3407032400040e210710340d007030460b00d02d508004da404001408507a00d0310354442e10103014500550360004160704d01148002194411802c490303440b81d014508a1400c03c102141c00211401c10f80f03403099008141c1c2c58050182d950750000c0c0700950140c0f401080ca40e1003401040200e48015003000d14582080c0c420420a0342000c06596001c0c0d0806110709089051400390350941c0f00741d100c000c3d07001d881d088800c0e51410003580010840e200341081413280303a9450040c00040c10340d034003038808101418080344d0300605d040d40711680c0407a000d403000c6c0c40b04445040420403180c01951194106d4002007102c41c03801442100903910b80c3d20074801031007440500c8003c04949051890054208100021000f0541d12001070801c011a03021084030352500d0601002016038000d03004240c581d500c5c40c60302c214021035501403002625060001c3e2881c40e212039a0075542540101c100329021900c4040c0b002041401b00314891034915810340b01d01c22a0a20702c1c0040440d94245844024805100d440c13400b40305000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 919696816 1250 919695566 919695583
    0xc0906090f090c0d031710032409081605210901080a1508061b0415051b0d0f030e150103020618030601081c09140d030c06240b0c 57
    0x9040342000340c54080e02c09050607107180b41c0641107401041110b0030598403000c0945404045010b00c546074030340e11000c401d00d103c5440003600ba4261140e10010581c0300525550440030442e6002a0082095590796540d412449886005640059410003401400d00002102d01d0310020001500c0344064030856481c06031071561810051f80c1d40010b80341c895030368801c0080070f03030603240031180540e10340065075202400c990315140180c00ca03003a40b040c2c4274404260360681d504102441c1e045040d1150894481d040110001000001145240c10445007400b600c1ca1030501c035a1010480e001d25a00a000c2d01d5082d40003000580c0400c00803030b01c40e240d500d00c05055a504543c01036680340412400901c06840c004265450300680d40005594440000d102c40341507409520480c002c00c6940080d200340d0b0481c86006000a1904085c294034a070802c01660510f205c2e04084041190b01d0b15000226206c050111120031610b0703030714070100d4607084203030b1004002a8260130300e03101070403c2c03094403207100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 919698066 1250 919696816 919696831
    0x102070810021e030a0c020111090a1202060f070308010905010f15030c0e030129010c050a03050717030f090106091505040203060a0911120601170c070c090507030e0c090609 76
    0xc0740d00d5034078828910202c05000090719141d03407241001034000307008015403074406c0c001d91700e091444840406d1f004280d03a260440103141c405254a481840301d100b03288404101d80c031441c100f0a041e01b11025002030039485010703a60307402e405d60409491104890781a00041612003942c0c0741040311100e118040000141e4030310300814810b004050541e204110700b982d076075040d42019410132600c0d0008054031000343e010040001d564034110019203813a50400005801a0031140604020900602c001c01c91140f0540352035046a80d14100351415030016282c81182558500a0201c0c55070240140380140a5500040007048a50a90041d0412241c481d040c05a80c011000514540e01d1102850007464070304024031080c450450303402820340c070000c1c2d030034600c00100c0007048180d441180b50362580322801e0001b040d0741e201c030000005241c00031402110007010310702000c0745d1643c180c080e150080d0802d440100c0c4149000d0101070400c8015040d040c0100c00b075104229065540d280910b07040001d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 919699316 1250 919698066 919698071
    0x31314010e0406140112060b09060f0c01330e0a0c09081507120c020705011b061407030c110a2d0c030b09031206090901061205010c0e0102070810 64
    0x609401038901041140209501ca458510b001500d103c02e41641c0d0300c102c40998413040d001054548580480d4141d0082640100c814031081b0b00900b045002005140124002c031810032030004501804e44d0380d64082c440514445805e01c8614040389110341035035100c02c0b030107490221304007070300c880f02c1035801003401c607a564952004200b07160103004040082c200b5402030f9100609a10013186100b0800c1d181500000d001a00d002c81c803a149124902400d107c40d0f0281000ca45400c0045074031300b0040012030580a400c1c802103000412921510f0341d9000a500e00d002c1c9840c0540c0050308440c121554103040c400740017020030910340082011117000c3d03402a1103402150709640b111070b041c4c0103005100d820800a03003070301017401025400359045078400e003204501e40e940c40d1022622070107496418090b011810003c6030962500080031136004400400000705c85540300340b800e40c954101c0000751440e954461107c4d000c00e90115140c2c402e50801c0c00140580c40ca040040703030303840c102040000c4046a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 919700566 1250 919699316 919699349
    0x1050409050a110604120507170a0b070c11040e010b102d0309230c010314042307090935070c05090702030c010c03060f0e15090705030a050106020313 66
    0x10707107079021750300901407140220988148a2a086503075100f68000c0e0aa240e0030b00c0c0070b00c06d44440004a00b44100e6000c20110b0513902ca4890640320039100e1541200c1ca800f0207031500780141c03560710a1201c00980300c0c0000c038082d580e24040c00f5101504d00d105004002003034442c1010401500301c0703034549000d9981c00404558109008400808040500608210300031031554000341300c142c2d212054406440c250b840c01e808100040d0101e442d802907840010000c0e41c0006c011503030f2584201030003401d2070142e02c00541e0090300c41d8189101e507005400b9250f40c0d44600b400340041c0c400040b220a10011408200014030792818007050310242642000a0002038404100700040c41204004c2c440038140300312034100100081d4503a048103072800280d41c40c00e00304d000c20a101c1c1c0a90411102081440d106140c00c000e195103603114002c0180c80c0034109d484c074503102a120406000c0c4501d0655031480d8403410014100303000e944041e4844401c55005005210024605100743d07400c544140c040c00e042c01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 919701816 1250 919700566 919700569
    0x5090a06110d050306030a08070f0b1e01290a0306030b1501140a030b030a0f02032e0f02040e040f020907021c0e0f030a232802030a0807060c0801050409050a11 70
    0x214034003030010920234000c1500d030200020030201d038807d00c4c45000341144a03903444040c510f081d5201c440500c03107600150010850640c6c000e00c03200880b40c09481a02600c0411008504a54405480800060b503101c00401c00e0101c0221002d0704048131640956108807001c0000740090b0100352500c000c42c41c0081c0346040180240c2c0401400107025042d24601255420511504204100d06070f0013401980694004100c105c1400d040a40c40001320100841c4070f80032481c004d0010b420b0304803185508010102d04240b111600910481c03041e68681c00d034240c01d20500c035810380060070140c02d6510030114800140c0805500207121905458100c00740c4074501d001404200582c901e040d01402519004018440304080741c0004803100303401920704403030900c0c02990724005420740314000081842400d412600148919200a00040c2150107606460b100c0e0013a1341e00490007152100d5444035103c40003904103907220f0040c5030032241042412401c1c3c481c5a25501d04110003011540c1c2100d030803615 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 919703066 1250 919701816 919701823
    0x5030d0e0904080913320f040b1003170712081021020d0f0c1514070314161101030b0915040e01240b04081e0703020d0305090a06110d05030603 63
    0x4040006209006032641c5a1507500c0b03180112043d003103044200c041c1c06c0c0c1c11107200d4040c28052494498441e840b583c0300d451350b503400d42004d0804c100100340c038207000001c03030725000740d0741d400034213580015980c0c540f40c1c035254010b01100f03480481404129410070420300c140c81d003090700300ca0030440803030403072401c0c2c0440340e424030914500254000100e55a9006020141d0700046040d0702c1032281003400b9440742842c10082001160483c00600a400b114001c4616400074290180c03190804607202404070b0003000039504014807012125422048000610820112100c0402da007800d00300700180d01c071000f003074030410f008201c1034600d41d0310070700180c0944440d482081603240c4c000003041204183e20781004040490340c1191019500d898002c4bd40c143c1c44801c0f202101c0c01003004090f01d0610b003009040400b00040c0c1400c160080c0c034400030160f06c8001e0a8034415220740d4075107a44054020810081107800d4000d00d040000c0040c040e811048001030009805e007450900e103413650755440001e480d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 919704316 1250 919703066 919703089
    0x60b120c070c030b040308090313120807050706020f01051515071703070c050705040b0f100c1a01031203050108030a0e15040902071a0402010c14030c01050103050705030d0e09040809 80
    0x518000700b80c00001348042d00d00803a00861099a40c0751807902c92010031070741e034010701c20304500400542c002009480707002c0e000c51518511555246040c8032203512114200070300303a40050302580001180c1400018203201d07040e4004a00e100146030314503090b0108072064030203605040d103000300151220500084049024840c00d450103610341d41d290084006000ba600f43c07000302d42910031048082100d281900809240d00c0014000410b200c0400d42042140760030b0081220030300c01c2e40b080410100d680761400068114405880541c0d55245140190040d0b003c3c4851202b01468400140110440403086400d03148861500c040b1401d4140c1c00500c20300c1031412074071055807000400040c031144540240055034091181400c0c600300c03d20203034910b00ba040710000d00085442e2031803800a40c418908001319144101200d0601000803800303803c40d5001c4c0c2007690198000c001c200003070300d81081481048416864404001e03008213010526505001d40014030f091004605000240c03110142d042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 919705566 1250 919704316 919704323
    0x909141506013e15060d0206160c0b0a0809010c0210050919060b0102060606120613060302270c0405011202030a0b030a0b0603070e04231e1f060b120c07 67
    0xe01e180340d0903c4210460014001000440c0035036221681900c210700f40062007580c001e407000000c1e01281d400c1012680c08004805422000803030810042403030341d0a10001340114a1025a585414404c094450322000300140416810a2600c1035820b60205804850300504440420183c4682c0401420030060000c8142040f06c0811146d0034450307580c1100b0513842007038003582d17400c0d1115824001144225050f0300a041d0302180405d50a00f402c00c240405642d5010000506586079400a0b00c04104284012441d20f0076550140e1040140c0b13151503044000c04051034179007854140081c19a582c2038030ba41c40e02c603074040000358646c43e4581000c0c10f4400020280e070313032400c141d00d04412140401c1e24468040d04c10900c007c034405010000d02405a600f25806552114022260940a883c01d414204060180010840d168000d2004804450381c0f480c0141040080507119206509180f004844403542410010480d100d400c2003212401075900c1f0049501c0c1c3d0b00c1003150503032031081c0040113 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 919706816 1250 919705566 919705637
    0xf18040213091b0b030702120a020106090504080d06050a06020c0904020a030f140f12090d0f061d06091c0c03020309031006061d011202160b01090914150601 69
    0xc400f008641c007035010003a0010682c201c90b564a803891603d03580411034134900947e008002c0760f11300500550260060b022144008030b441394030b0f0768030841910402d8404403201d00c3c02140b000e89403002130190101820b41030300c0b00e58050740342c150003d595004811520f405403080c100810103648580d9444800341d41c0103405041481510300c2c2c582c1d0142840c11031407881d4000c800d106216004041140c14280100c0900c040c1000d02c4502081041148903100b100e0960018504200160f224051a24110059502103640c181c0007840b0a050181c002d10360341082c0c102404010b80445c1042d010b60030844036280541c2d6003c1c0c5850141d26522682e03460350b5040c407614101900c07010998000300140c80a5076075040345100c900041c22010491402114041a02c030001e8062104040c0d0140c55a80350811001c1c00c2c0400c0360319480f007404000c1c2c1059100310748a4100c0c0c014070030988440411410500d00518001e10b0714ac00b05861088007038248c9040002808502c800090b9558004180c1c407241e070b092 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 919708066 1250 919706816 919706831
    0x1b110615240f030603071e0b0a020c04110414031203130201050409320f040b0c0d1d0613080702010503060619090501080604090305160201050415090f050f18040213 72
    0x221031681040341e035075101b03111300e8401141c3d00071001d201000303484410440440143c1000c03d501c40c1a000406038030118410442d541400c0c2d5114000c800705043c0c2e07440c0f51960303941094105080c4000342d0390a1800303584540094070554002c0800c0b658044110b800f032003003508403480100c1e603a102e103500c02c01445082900d0342d24440d2082421011000004480345c0c030644001100f000c2c40d050403a0300301440c45030000001c000c2122041520391005a45a600d842d280301d06800c1345c01c42d640100c098819103410120846040c4040003203030741000c42c041c03034000e0549143c1e0364035a0344c2c458240003c0c10001c003c00414002d03152003041e80c02030070b01d41c00c212981405072400202315810b24414503000501e031801181b1581020300ca00854190540d4595150401495002c5d50010640104a040040400c000210100c03501c4a0803544003082d074406000910307058407080c2c007440300e8000d07911030030182d00300b50096603600d00ca02c020440015000c003850380e182c0c00000d11441e44c01001074000e9060144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 919709316 1250 919708066 919708087
    0x60c21060e010609030f0f030e03030f0712090510031107200108070e1e15041e0605160605180601090902011709070612020d1b11061524 60
    0x80064030703031502003881c5603039960b04101c484940743d2001030654020b40d60b2090104071140200410749029007800000707151031002003855a403010110200844000c030f0441c04001e0040b80320140d40403546422003d50741000c0005100c2c010744c0c04003009056948100d00250000001a19040c1e600b081e5070050030103c2034003508501c903030318003040d000070071800004044a00442e80c0301d40780003000d440b00702c01c0c06400b10301000140080b442d0310352111950340b41c11032000d4601c0080025022180d04030040e0300600c14456100c000c00d4224400703005051000042d0b021800340c0b01c0303840035084500031a480d02c460140340d0b0300115030101c00085005580c000304d50220b4541064403028800c0c0e07100d841e00380f20302d102840200d0060310a0522900300300800c004007803168150304000c540300900149808000f01c002c40c1100c0181c86c110903180c01d42e10300025031a0700b00d01301d02c0409101d10007520092600880e0081e071480b000b60300c00e2003184428203c84254480301c806d9030035400c0414155541d07400030f19 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 919710566 1250 919709316 919709321
    0x120c0f21100605040c211d06070215070509011d01120c020102031005090609060f011b030f1b0c090c05120f04021f141b010519050c16060c21 62
    0x2606019a04081074003110b144201805081021510700c06c0801088031004171000e050750040c0794054090601d5045041c08060004031300440720340e00107110200c044482034461407401414001408030034009491240d80140f40409100381d01d807501d00c030550a0200584074442c0c0100004442842c00c1c001c2070200390154001c42c00b40240040443d281540d034010032940741011101d607900b0003100e101007921030034a40501440d04105041140c0075013041e500309410129000c1c01600050700f0445e100d001da9070060603012100484055080c40c2c1d04841d141e40f000190648030b1142000d80d5003c903d00e80510880030b9a44075000e00340945890306143c4400c150052050701c09910804843d501c483e8082c079450481003a00c0c100f0340b0f0702c1210501260b60004c42d600114460149034204c010105021030003031086611440703e41c485c2c03e03040c000501028003203640042c08160200310400c2184000d0b01007542022680d03a20a07000300b041031401c1c0048405140c4140e8403074090103004421082c80701c154 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 919711816 1250 919710566 919710569
    0x60121060f1b02151315020c0c06070c06170705091207080d032a02070306152417090a0f060603080f07031b020f06090a03080a0509120c0f211006 64
    0x2684803907098a85d41090070307401c40c1c807040042c1000202c58140340e080526402900d01860060705882e62022050003150703059005c44011119441000f03001c0c801d20350400d00307c0595010040c9581c0440c503200d00003914a1150000c1d0a10602c4a0440100d122038100140d5000d007042c4415682c1610120b43c02078081c2086240809010a0404d900c0d521402c903031045c88001607069004040d1030780b46442e404000e00047c1021120300300c1c00752002c1841207102020712000e4111351040b42909400d05002411462842142c4800b54801c00038000d4022002a0000300c01d60810f804031844c0295150400042c4900d901c01400054040b07120020301c05002c000d80b40c0c90740252604000b0b200284014484030801d1207000354003ca54003010000d81c100302c80503005001010341110990f640381e460f4002e080d0040b1550034001391001030800203e007411080a1184001d01d03000340703200d004080c002a840c04240101e2801034151a040d5403c4130301611340881aa07005506886400c2a070510980103070155 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 919713066 1250 919711816 919711843
    0x902061c0b0f0102030f0d150e19151503090f030801081504120e0d150b12012702031e1507050316050c010e10020c060121060f1b02 58
    0x5064542415042c06429003004100c160b001c2e62130318604001041140d00302462040c1525600c40c070003010304540d03c40050103465442410507030340c901072500d4034400d404241d1400e025400c0c08400c0d00c00b40300810000f41525928442d079035000c680c2d4070040740189602c182c003802c161440310300e490a058100480505075a0000c013a14107c0700161070701d6000d40c80c1a1402040c0c8825000403036110f0303100d5091811040750003800401c20841a80ba03043c0b600608103c1111560707616040414589844166118050b2801c0000c0c001217a2071011030300d881c000701e142c4107074011207030512004668044c002c0307071800746500d002c0103028201da59000c0e6031072100c07420480d41c0d0084c0d000400d4031640600141d07031041c0c0190440c0c1000c01210b200844a03a001929181841c1d07490701030501e400c844c1400b116101c0b401e807000058507032031400c040b14900f100c1a884a00c14002868981401300c03d00c5000141c3c158118030085070503459108035400034080d81c4445015018030382d4420400e554003141d80c4401020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 919714316 1250 919713066 919713071
    0x170a11150f04141005030402041805030a1e0f080402040207080f0a080615040806040f050709110309010605100203030c0f130810060602010b10030f060e07021609091e02040902061c 79
    0xd03000f0034000f0154030103440e10040b070814030024005103866001010400d90b90880d04285201543d103441c80d5401141d011808219411800d410080340d4400d007405150301490a00600000004090111310300a0030280c001c0d500081e041090007a03420131030342803406c1406102c1da80c0055120040c0007040548800f803044180b805100d88600c0e4034030aa4003600c0d141c0001c1d256544031941d8007104007038803007402c072014091030200140f140502d01c24503111030fa002110550b00e00e01482010b0846941c1c0c1c02c090b200361441800d080e600c0b40d000050320b0744134a2220030580c0e03131421a40b002110b401108458071146c11411804112690042071101c1c911490314801c0c4101038032400c050f4244c40d0500c08280d0490740800f80c52084511a80081c07000ba4130034240041c3e43e40d1107801032401640c04071940400769000d18080541070342c24407032100003801204810043c02a80b50380e803405805840400c02884640e08154000795543c2d03500030007015038001c1c203060b62100600d0600030a04404c40b580343c600761 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 919715566 1250 919714316 919714349
    0x406030f092001170114090108070311150f0a120e0a080a0309060204030606060c140d050d11090301090c1706060f0d0521040e01170a11150f04 63
    0xc03690180000d1568408003034070080d60816607018066201104882c1004041465100c4000600300403074084e002e103281c1818036a843e070050102c40d9a0691154038030f50302030072003000424000906504421005c03104a0350840c0e115466100901808621854280d40090080421504064184130315680350341d0a1000e20700d0f07a00003a860382c29580300540345140401012550a10940c02164010b215440040c1010b07203d0301d0f10021184c945d0000350101d002849280c0522400902d4420100c1e070b40f500404014100d1617000b8a54000c1c4000c9164817034503450146051502c420580c1c001303140140080003102c100c0e081a40c00c00700039218000070303103e411129091039000440d030944a0380d0050700d800e00d052000c5e0306012646d00c00c402c082c0c4103801121304c0c8111200c40c5800008485400302d14035a100c50800222022641e010303481800c00c412001d1880556650110759500c8007904990724108618055000c42c1302e61450f1070b802880c10780300244501c900703440d02025000b40c8001c144100b4155 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 919716816 1250 919715566 919715591
    0x31d060717060d0b06090601090e090114060604030c030312020c031309060b0a020705090a020c0604060b010807030513031101020912101a090408070203030f1206030105220602130b040b040603 84
    0x1c2c8010f50010b000c056004000800b14180500203036040310040c0b401482c015a42c02a804038101d040c4c40008007a5111861a50b5407010031109582203e000c0782c4807841d1a25617680c000183c0841d100c0101804680c0800ea1080345284c0e040d6500171a071142600c1e9640300300c1c480a0f440895500500300d082d0714100c00411104050360640d00000259001025410b060504101581200611104c1c00a40802020403030440912601d4081d601c1180c0204410700c2000000d48005401810304041500c0c0004000c021707182644500b18650305420714800e0300101450a40c003a2294030380d450b030000c003c9004042c001000181070f50251710070300002c00c141c0c10b00286054840d610390401a602c20003040200c0c0c04a4080d0004140003071004040340d203441c40d0282c1d14010b61b00314540e0442c04410f04002c1014a003420f014042d40311501c45c5102149100b0b5060303068055400e02c0b0050206c640c003056582c07039251501010805443c0c2c03403909549482d80d41101201c240c0c001d000d6840043d04103280e03800c2c403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 919718066 1250 919716816 919716829
    0x60924020408070e0c070519111915110d050426030403021005040f0306020d1d1b0d080c010213060908070909030c02090906090f0a080a031d06071706 66
    0x1602d035100c026280c418034041c404a4042030152030130030810030400a4800146040000c40c4c1a6480407454680000c00ca040a444e030044450b0703070314010342c0d80481c03043c090465443c445050b62460900d000d45422a900d0450710b0714241056000356119600f905107110703820101610484607456190702640c03113040402400841800c3e0020034640c02440f041c801441c002105040b010058644681041d54511903000346105950003076070090741c0041c002038010443d0154401000418440c4145d85902540083e43ea45607000c0d201c4816500c020241010f80d030321181408003680160b61140c85031a1084903e000750710a001440440710f8030507000422074045d1842004481c1c107807014103480c46c58400700300013601031a4411002c12a89001c0c80005a0707030301c12103038052800100104018504040a00d240a108601c1c4030300641c0141009800540040304646904000d46400700d116020743e160942140c1e0303410341c0040c942c0074070030402406641c46038088000805141d80f14400351104000d00c031a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 919719316 1250 919718066 919718069
    0x60914010b030d23090607060606091410120506041104030b0f01081c0c0320010603030e031f0b0d0f030309060c050a0206040b071b05060402090a051315090609240204 73
    0x1115824500d1804d0044607610140041c0e04000d003225151441c03a03030b200c074102c0d195600300001040d041e0406001104030302c1103111340c24009554500803002c1030180a81081480b1a404030504e8032800061025201c6410204a0412200c10a0f854603100d145c05040c40700e0480c3c22480800800c000080c00000004d50f2881ca0b41e8240079007441c804030400e040710300f04856402a400e00202c0d030441e03220041200b02c00300c1800e50100c00092140d08601d070040603c4421a82d41e8400d034407501c042d13406007100c5046441c640a00740f00c0010703682c16030004030300c05074482c050241c000b00080d94140e080c035030582c1020040783c1c8180e43c10003c8401507403080e9164010a01e4200c01640b048000800003402d03494907503008241414417079900c19030f18119021000e9506411a1681c02030350070702c0118200600c0c1c407908500b030340500703100b107280c59590403180314810b62001e000e14000c24014801e8000c2603100c0000329400420a11142d2028101004d42849006c121900340b4204c1c1c0056030f8070300c658420b80c2d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 919720566 1250 919719316 919719347
    0xe12010b15041505030a1d0c0a060305161b02030102040f032906010f0e130e1509031603030f0f0b011d1003200406020106081e19060914010b030d 64
    0x304841c0b036903072013204c03030b030f00000c1008521550782c0440c89a20100a0a100305d08a0640c0081c114130001d1424401003540b10340c01002490f0428061002801f040141c2b0140e202e15850904003840b02c00f9a0200029000070000c0c0d05548002000300340c3d07c4450a040c1d09480c05000e0307003c481d441c07101100c0403071764001040844800700000882c10320341c424203154030340c0c80071468141e11f6900340e0b9002440d444800e006d084800303a690080c00e404c03d80f060190500e00411404040d4181c64542d8010f6100e2003141c07085121003c134242c0c1d003c00c15020350f004070340190b026a01000709141602140c0014070a60391010b000c10400e90652a007008031012003025400050143c26034011030749001c0d070181801c0c01c181d0b4001c0155018607003e040419000d00001c204542c0040380380380c81c0c9a603850802d002c20f001440401e14170030080a41d0800000e0b444d21081c502100c0c41850103003030910038010035040c14020680a20b42c4404540c0d00ea054002c000300c05400c0341920004030207400252a0400b2010070407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 919721816 1250 919720566 919720589
    0x4210207030605060607020a0b0a0e12060703020a090f06030207030905220c050906070804050a0b0703020304150903080c0d08011409130203160909051501030803160e12010b1504 78
    0x1800018115040f85030441ca019008504100d600d60000e0010000f03900008140c110114001000d00d03400341021005010940701c4486030494800c0300d80d00c5000051407001856000502041600d1043c1c4030a4000c20301e02545030300307864030f90384010b0107036209c0002a0005464450007181500e010031101d08114000c403141c0390b0a00d180002c0002400c140b03848402441028030a441140d1a26801080202e109032000c030340d968100420030841e140700340c0004070308000c24000100000e0300003044400755110b51000d200100c00d445002c13aa409c1039904018190b48020600206400b40041d003840741944503240c80841f0381e201c001c0284a0046800c80a9121100e03401103003891000321700c4883d149001400750707a02c0a00040c00b400c8a07110301d61001e04c084e55140d11480c01d0260920a203034104141c150a41240c3d495510340c0141808090f003001c100c441c1d0042c1010b207190145203044801c0d000645640c90684401400358001c10780100c01502a00340550140c1062103045c0448080d204015840d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 919723066 1250 919721816 919721819
    0x4030b0915071e0e0105090a1e0e0f0a2a030f061a0d092907090506090916120507020312130f150b041508011b1b022704210207 56
    0x22102150302404c558103002c81000300320140d4a95912074406081541c01040c2a0010003a03010078031466684602854109141440340c031030590341005400402501e008500340e24144440140d4078144054606901c0c0342d00900030303080782c240c0c220400c5689040002c01c0865600c9000d22010320035181581d0b5010400c100c00000482a0792002c12164061545500004070040d2910310705c0f288141060b0686416404118040758400b490130080c100035550141000c4045010490a09002d860b45414090943d5800c08440c416400c1038038400460304240305500b014a0040e440350310034610100700070500e00c00140c03030301001200700349115802608481e0310100ca0721106100e05500c4500542c0b00e465910030a020340c2d0b14010b40c0b0041000d4155040803529101403103085440e044001b280e0070905034031341c102094000b07991a040380c2e40d25450a030f0240161000a02301d180c1d1130710a4420000405a80355034038003c07a1650311840c495403401140d100781d80b40c0319206000d00006100140d220810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 919724316 1250 919723066 919723127
    0xb12010506130c050f040929130f1416030b0f030607050f04081006090b0d050606010324090518030705030405100c0b040609020a09020903031e04030b091507 69
    0x881c12030b0040c5803401c2428580b0425820304581d1255101c3c00c02c41c8d440d405180901c1c8110908216100318500301260011391110200c0d16010b0040c0300c3e05d009503500d80425070f8115154004d4060700714100313008141440c210414607000314001e034503100024034211440d605424002e04100d4a480c0060013403040d540c038880b04841d194816248444100c50038480041d10304003c105140004e1400c103004100316041c10400c1044442814505204a507103500501c0032030000308617130760045400c1c81d000c214a05000202c1b900c180d03403641002c1021500030400100c0e40002d60085006a01910400d040850a40c407015030301c2c09070714405801500208020420b42c0350010700303602010190708001d1a52071080d214140d0990048074241c0b03055460b54200341c11850100c1d008809008031940840c02c01c03c800020aa49000d001c01d0043c20484401500d21880b00030f4054078000c550040d8860762500d0000d8805840d0010440b040258080303000202d20524011002d041801d0703140707402c0000319200b210 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 919725566 1250 919724316 919724321
    0x8070302091c1406011a1b0c09180606010305040807060b060f040807050a08010c0815010207031401020307020d1812020d061121010e04240c09051c0308040201210f0b1201050613 78
    0x81c107aa07d144200302214602d03071181c100191007954a100512250990f50300380904007040200300d14101860300d01000300041c00001920030032030f00500b00107040d01c030040102d1814807a8a00b804804180070034002401000010b41c502510302c00c0d43c040051555803041d29080e1449107101c00c1c04103e003140000c4c01c084034410000c0c10140c0c1481210b00c15952504e512200382c0002c40e04800c0c0d07035000000c0240241c1c0410804420020310311788407031210700d00c04040c7c200606500812484407054040e19040d9a611010b0000e1103400000401c030b140c03103040c4041e0071a80103400e002c501009000c0c05203180180c0310081e038102e4180c45640e004942c1c0c2d9a41e806950041c8014130304d002258019a103081c1c01041c4503403403034225180c88444003181031002f001550340918000840b0580101c940354002a8820000b0390490340c282010695424151608840c0c0740c500383d003007105240b421065600400c0580c011501a041c00d665040019000620250030b9540c200c4200e03400c105070606096103002da9a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 919726816 1250 919725566 919725607
    0x51e090a060e120f070c150e010f08010503030315041b0305060310020f040302040203090a0b010609080f160905070908010e0601090501051905011209061a04110a08070302091c1406011a 81
    0x390f1b002e241e203a40303828000c82c0005180740341030001161989944000d5070001400d4240600d142071604603585000002903807444000d0104506166504040000c0d40302c94018511662104144030b03043c103018040140103100c2140d2031071080c46044403200c8a0480e034804c40d0380130350801001e01d107007a0454007440702030341c005080d01d03041d40724070854039001c9414500c030b49010f032956036601d0440600d4441090324000c0c031011003010a4020030040b00d44125a240c04404880d850800401c640d5240001503039056010791200c4215400c007281440741c403402099150503a1240c00d010441a40c9900900148400040440c002e103103032640207121a41c09805007003d2800d0200f004620040d456450405542100d880ca44403422018801455482c242c0221039840e0401c02040c1d04040740c007030300102034110150441b020b00d0303800900181503464450505030300441e01d000c0300208400d07030b03d0640e90744140055850442c0c041c4000201c1d91210881001116450500d40300d410541035660060780d08104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 919728066 1250 919726816 919726823
    0x31012210c2102061503070509040c0e0f09011802090f150a08031e030708040305031b0f0304150605010504090f0905010e0d0e09060112051e090a060e120f07 69
    0x1010200c6001a8081d040140d0918064120301c280c0082c41c20080e00d0110050100201038a00b0350349105142c40025443c0112001141c11103015102c0341400701c1c402003650441442e02c2c1000041184013070b141c540300d5008c0d848410080202c51142d110300d55040e091039800950101c5120003080b0120482c0030416089441452052011a850700009011003000d92200960b6000814510080b100941107400b0810080504a10b58a030420004150b010700400080078000084081000c21410aca40d0201080e5900b0070741d65158040c041241d000d0b041201d00f100c030404d1980241480300400d0103842c007150b0060b119581040c1c1001e2881d80508141d4503c144040e1340c507442c0c107021907402d00440901e18058406009680440c500080110078100385e6580150034400c240403040c0d90082184100d2034503443d00003080c0d29445400c0480700342940c91000440c4004092008000340421240640380c407031b010410821020b0301d40030b03856600703603400000961000d20505c041c0e126400f008210982c0b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 919729316 1250 919728066 919728077
    0xb0610090b180307080705180c040608041a040f14010e100b0303190c17040e01092310061d06090114040801090609061805060402120c030f0303101221 66
    0x102c200800d10b896100c1d0301a2140307601c0380e00e00300111300b00000e08441d039408190441c54503241400c09140984118440d4104022104000409020040600d00300c1c000c210b2070444150308150424031244564004240c0d005030001c4c503601500750701481401d04000c0c0080286c90a07a0a500c01c01c0e000749401c888036500b50004001540c00000410840691641c4a4940c1030030300189041c10f41c160b007001006009103200c1000188801413089203000d04503015641d010950411200390100000440012600c0400103602070025160803603103044140e0356143c0e02c41c1c412980c01c48242e01600d503900300e545d40100080156142c0e5510440190002c0c800c8218442d1a04c4e0b40c80210b43d00b100e109010a9a81c140c0d1420888100580c1e40107155000c068811140d056400b20344602c2d07203400e000f5000a04c1140036400000060105110350030341c425009081d50303502012100c4a503220760080790710340d101c4142c5d000081340170f9a00600c010240b0f500040c21202ea40800724503039a80e01c00341c0200005229 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 919730566 1250 919729316 919729357
    0x10090b0f0d320f0d091404020d27050622080307050c0d1107050609011b0512040308030907080109080a03020f090907050a030e031e070620070b0610090b 67
    0x1002038411003402140e0b10041407106030803014203003030142c60650032041002166040220a040861001426000319001a40c5000e9082c551008010030b07980c1440504501726500e03074600c0403012801240f070003001500c0b06e95640510415a411094092f107540c0c100840e4000d0100700b40d03401441e1300401a05120385000c2400070042d05e0030310480f4052000030012407861803015024400b040040100366403490400e12070100117403404800d016014581c0c00b015050342d00f480820008510512003c11000b50303030f00d4603802d140845d58021606980988582d03400080e003d441440340c1301d0240e410000d280e00300200c02c2012000380d48004d09200030302200f408406480e40ea00550749004160a40f40c0c0c030768500180c2d401600b07440d406e9640c48210b40081c05290380d024151010a039116408411455584210780703840002001d10114000c043c0d442c00141c151001500070007806514080c840f001055a00c0d0002c108080114059400000304100c204004065860300605014280100c000794400f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 919731816 1250 919730566 919730633
    0xa050c0c0304061b331109010e040605121e160302060313060c080a15050102120a0216031a090a030507140c1914030304030503190504090510090b0f0d 66
    0x24880b0146500190154540d045041d0a40800190342174646580500203004072844c680280d0052206940c14400c9189172005e20340d885074000400345c140102000c0e0034400d00358050b5070303400800c0000c01c0d54101144044c03a84600c00503050a2001c020300490120505680c2404a290409003071802200c0e4070710100000110640109400490345654480071403918030708602c227842054143c030741c0c00f1010b1601400f450742e0110324030b245031121882440d0740e2012044200d250086031035104003902e20009003c002c21606624080c884407060016031915110708010544030300c14040010080350341008000001203c40900d800f02941000965543c1c00c103e03c08140c254065440c0014490a0900244000000c840705020366100560045042a0075a61103940c1d900c205000540f8880034425100c00e800c1c8201c00f12005014018804d000341d04000301340030050503c0b40039145055061128488850420f801950043c1000611429070815151662149801c1c0d14080d01e609955581d04002030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 919733066 1250 919731816 919731833
    0x150e061201180f1b050f0c07120303141303031a040f0c120b03190611040f05040522020906012309121504030f020c1005030a050c0c0304061b 62
    0x2002c081c2107001c164040082c1030001ca49110381000c0340e81d40303840381c0708801c46a55141a8000390440c1015a0307078900c91600c0388000d000310066000648203d40c0080382d1a44990711403001184252014046600002c3c9450b07001541246c200e0100b105a100703000200303200e50032089404070784000744083e8441500c0400e040c1d0741b00c880700c0300d0300d1521a42c1d408661944002c6500c0003824020b010400c16050070002a1580c040383d425507610b60307c043c0441c003403003910b50010f90482241e50704103a407a41e4940c040840c01070b02d8400d85104a00c5c1c40f000072210300307189141d094400c84039940d00240c8c0c030782c1c0e50030821580c1c40600300c6410802207a140d030380321400e929484d000701d035101c50210f43c48002500412002e0b0b209001040f489800070700c3d0fa07803480c1c8081c10040c0d0b00036916040c43c5014002e0064102e00d00301302c0c0208158040c800c01c0e034140403170342c10100a50188180300428050790b551580300c0c800621500036190442c2e441040104866480b901d000d4030150380c41012000303000440e0f1030307100a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 919734316 1250 919733066 919733069
    0x120207080f0307081b13050d02130c110d08130210020a150e070f06050a05180d0f030201181509030e04090803070909050c0a0804140109030806010216150e061201 71
    0x800d042106001c0c900c0c10218205851240300c803117180c50b00d441c0415050703000c0703c0c0303100b41800b40080c200450219500d40084a1600264003c01c029201e01540c008100123483d03c02c1007118021a8500004544030b611f110f481410600880340c0f400b51960309000c43c00c1c0840e100b000071806a14201400149000744a14140b030035808003103803001a204900d42070164541c0400c00514511074204038158000c029200402124108a612191107240042041400da0039180d40b01d0305003401c078410025081d920384007882c0668000c00c52180b042000c00407031000440060106003514050504480480c1c001c150f0452081c174001400e0010803010406440590304126075850000c01000482607104031118020554204107204c00d040c0400442620700c1031818080800940d18005402d0005c98091040200d619070000c02c02c0941c0c1b0304000304010741c155507460040c0920541000303048940c01010041e1450300300540880c0b071410b14103032818068400e40030382041c020300041c554400d404070081d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 919735566 1250 919734316 919734331
    0x10821120901052e17120f12090a0c0b0a1403010810140103150506010e03030705302502030d050301050f01110c0108060f0618090f07120207080f03 65
    0x400c0d040c1345007441d4141c20881082003906a16902e83c207110b60b40c100000d41241c01c03010459002441e207100311030400c0c1007851041d45c031800c006141c40305e4012043c000c2c44601113142c811207840d10340380407a98446003c060040d00001d076102c0d05000c45e05c0000001e150380400380c1446000e0200050302e1484c9900241d11200c51504503101200307002c0041d0041c0d41d00c0c111a20b10201807907040d9900c1e9112400c034101111601030760b500009013142d01032025400043c000408580c0c86003e1841e0055030b030a44034241c1080c0e01e0003040b411104010100c2014030380510380340014103010310812060b50394021201240031161402583c60056103003031020909490195407025601d40c103001c01d010f1a600060982810006c0054101e44101004203c240710100d00b464102c906841c2c1d00002a807081a558010781c1c402000108c002904201c407403203103601241500c01c08919525811200c90040003290b6010104103c0c0c3c0001505206030ba0080924038800c4e00c110703040446140a42005800c03c40c0c000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 919736816 1250 919735566 919735571
    0x706080402030706050a0807050a14070b100b0f0d020705010b0d0c080d26090c0901080a03030f02070507170a0c0905220206041e0306050a02070209090105010821120901 74
    0x4103600b4280b040340302503d00c0d0304043d4601503d00800401c9054000d01100402c2000300c0ca42040d54868410040500a50840940c440c001d50400c20a031007015a65246500804080051001c070351009642e20b00789410f080d83d082800c50140c00019501100f001c940a569400035000941e80e406408184a80204e0301402214200580d032481d004a036480c990a000414030328001040c0700210820807148c20980e0241a0f4031040c0c2040d10f40005d10b0703504c95100480f240013140303881c030015072850034134000d03038081c80640d42c03c05c1c41c1012485204009041504403d90500800001c907210540b511030f840d00302c810f41d2440da100e0802d45000e640008c00c19070b032601d080c019203406841d00c011451030415580c109510700d07940012070f544214402c00b4840d800f10402e4252801c905c1401800868200e9828450391600140b804025400282c00728840d040030404030f1143c140502c142c038103a80e03a4031300801c400355120103022001d8508080e0051084410071224400c2c541c1300310346030f01511460001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 919738066 1250 919736816 919736821
    0x6010602061902041a1b0604050a120e04060612060e13060b01020a061b03061d1504020d09050f062d1503100608060c0705070504020a02071e03111002250503070608 72
    0x8114007011100008500d540300002340320100b5000300749002002c0c1d200c031803861840070610043c0c69000b503045603a54054039000340005d5003500301d200d4800030202050300300844d07503d4007807103c440003081e50482034040c0a50101800101640e00c441e4102d40c0500403a00d4000326580c440c0c044d0349035a6100f90407041c3c0b0740040c110040d058042c19028155a40791040b215200da200032510050090230a404801503103000c45403034486504039040540000428044803109050407a51107803112148085445010001240c004841044845d22511890309040010441400d50000c00300a40807280d07140b04020002e201d986c0811034500400c201b43c0d404101c2c6403401e1300250030300200410a0295450400c600303000610041421f801b07807001102d005860380d003040c800f2031800c002c42d000480c01d862080c4120704650204813064007100c0c0b084c0c100a6100d2258010b00c4a000a9084a100036070b002407240c0301600c80c0700e4400c0414881142000319066592400a45045010390000c00450f158506 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 919739316 1250 919738066 919738087
    0x70506071701090c0f0e040e0f07081902060403080c1009060e01050702030307020a0b040c05151e160605130506070f020c0604051507030513170c0306010602061902041a 74
    0x1c01d4018451000c040090860b803020281640c0004001c40d4100080d14240e418907603140e5001c4501201c440b400c0310f009010000d0000c1d82c83d0410f01940741c0c0340c8103603134070260900c0364041d00b100d0b031940c09407040742001e01d075640d1101c0315044411103a80c0e87c0248110000160094402c09418034010100442c46001551100b0300f1240d000c4c1840c401c5410070010004040d070000340d00c1b0a2144d000151908079903a90418202c8180107800403948510313a021f403100d50038014030250800e04c20701188034101706000e400445a40c4030346803124400303111103540040841c685901141e4840401814040500d400b5038450f424031400b00d84980c08078461491014403150b040040510030001518420f01d800c0c18000052542511081c41c0c00540d00000350020402d841001500d200342000295150382755250303000f110b5010255102034108d8031034115101054900058100e048644540192a1507201c07814041000b0000a0144071800d808003c001540380340a0b18894481602c18a6107031160740b020f4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 919740566 1250 919739316 919739357
    0x7060c080f04021c1502032a13140303071704090b09011d22050d170412030e030c340b0306130f1b030f0213031707050607 54
    0x3420314552181030802c000041c0c44084104485880c0c20041c0a02d1601c185408804441c5181c41ca410b414004002e02050140306004a800b2540c1185002c1c1007000308802101c85010301141c05105050072103007040056580b1040040318800035064a11341841c5480d0a0740b0207681d0480d40e001200b0014080040800f2407094500000c404c403000c0c101540361000d09a514091149241800c05004010bd44901c1c20566515500120345040104423070450401d95156050301c243c0b000490800c034100d000940ba031043d914803c036800f2640107103c00248104900408003500a040140310403c5401e8a0305d03002c101c6200c6442c5500403e0b05618041484003003080c402482402e04140101700074099441d4104c1580c3c1d101d00140e40f864800b003000c0d0180c0300588031080707040a0403403400c139008500e64212042010001c815031010b1003561a03900c030210482c880c1e030181c5a074138000d2000600000314050f03080200c0b000e449540706e0070044203850b49420160180c82e92804126a080b4424080a03000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 919741816 1250 919740566 919740571
    0x10602070807050105180105070c0f1404110703030b01090803121503010905070e060607060c0201050702010c09050d17120c0a120b1c0501290a050405041e031407060c08 74
    0x10005840b01929060010f040d60240e420b10a10100b8a06050107003644500705032200d090b0800c0c00e134140e0700d540da0b5069221520705c0c042d0b0120500c1c440315240c0c0a00b00390042440700c90102c1c890511303007a0151022001803041d4803109040115640700024034140c10000751841e400c040300000c0282c00d018051002d92105044040d029904124484002c1200801d402d012030380194100c2e081a030b69071002408512868900500c528a4400c882004980c154070580c42550503400800a90361402816181d444091040b40d900030710784150200080c0707404028a001c0c0f1225480c96040070344d444400c85840a08071900346804030003140c1141601d034411080328000e01c000c03104111041c00a0042001c0164601c1e00d9440100500e105000b0400250301819140031003811020900d8044002000864041c00c5941d01c58800460082001e141c41e20601d409245c0c461900300800220807160150322603140c1058050003858204011580814401002c0c01c0f8840c1000040c50074000001400781c9801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 919743066 1250 919741816 919741829
    0xf0906020d0b040e07030b01032612071d0f010507020d0605011205070e010803090607150510060327031116120b010605120408090604050307090506150a0e1e100801060207 75
    0x32000400110704040f0b403290649801002c070780702c00300c68002d071100c640111741c1c3c40d40f400010000f8bc1c20a5800e9031100c2074040c0502c1da0380c86008289086020340810405131040ba03004500d14400c81c02903006000170f002041c0701900d6031801c140300d91518811510300341e002d15120001160640b080280601c402c801900c03101314466541d5040c010340c6903484c056174215038001c80000804000388407112810140c00300308100103126038a0024414086041244607100110f820041d2805140801c0301800021043c000243c3c6c0010840da1401c1321409100790000340d160107009554000300d0030381000304c0050840c80c034200500c100c4910f401d00c58000160321110400c2002e019004000d1800da0030380303811542008095843d180288009800c0d03120341c0d40403641c1807003941800100300581c1d40120f4801d00080300d15003c60040c08507620329a208a03588000096140e420514940c42d080c0d88011000f04c82001c480b18030254500401c00c4182c203174a141c0c01043c0c0c0380004100c07a80e41005000c1c0a89030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 919744316 1250 919743066 919743073
    0x100e190b120303040f02060708030a06050f03010e210f0a0c050607171512010f0605030106050a03120810050a091d120a0c050c210c0105090f040f0906020d0b040e 71
    0x3214001d50b0710303400090002000a00d16400d102d096581d0441918980c54000140d80e030703030741409000e003030060904d841007034000d2418920b4103016250621408004481050103001880080c0d428032940c10010307103241130710150a0020128000340c0c50080d02d40064180c551b1000300525003442494140010308176410002d4244400d081640c81620f49030f081a60500d42c0e08a28001c400001c140c1c0d00e03e208142075540ca40400302c0286000c0750029000c48500790020032103583c984050100e052134a000140c003801200402c032034140e10035051307154031410000420444d0354588001071a84150f65020b20300c190388600b840390b0075070356a0503030300c106148060050603084051054200315000e84a544d10a00600b0103202041c40001e00129000f100c00601c5002034042c1d0b0311090f094200203031500540e61142e450701908550056044400d90704000f071021207a5940d01082101070322030b15505107841903c4609139000580c6600140842103a0701801080102c000010300003101c807610b281e450701d80e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 919745566 1250 919744316 919744339
    0x1090609051015110f0a020a0506070b0f130602161e11040b13060806090f010c09050409110d0b0618060d0201081003050a0503070b01151403100e190b 66
    0x540544140c0465594031819841184401e0080e00c40025101e00c0d0340060081914174440603c01142c8828100d20031031300194000e80341c4040c09550300484600414542e19540403581c004002c20368107034403000f01c5c1e103000e800709416070302e00041c0e03001005100740c46070441181c41c080000e0002d0410780e144103001280c0d5070b0000c5803a600b51200c003140030140905c0d9101c0e0400d0b500d40744c9200c2680001c0881c0d4051003001e0350f03419120790315502200c030348100e800350151284000b14103006001c900c1c2c59681d00c1e905610700349010040200100d06040b6030b162251401c803035258507414030a1640f0b40c01210b01e5009403070b0034400c1c40a81c4002d10350710200c051804040290a56421420109054080c41d082100b40d507500d070360103521185a000507055100e043c120a08101700040180a050320035290b10300641d03a5850030700c0d121107a51201101251403100c200100c0e41c2100e02959001151003894114142c0c0d6117040c21140000b03a81902d00102c0c0f550b010801c1c5401405503501d000c0d07090351481c2201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 919746816 1250 919745566 919745581
    0x1314010c050d0b1e04020d0f1e0b030d0905130615020f070f080601030807060e0a0803090c10020c100210110c010c021518070509180c010e1806061608030109060905 72
    0x113010851340354421a804034070310324242d0710f550050041c60084172081001051003075403201c0c4603030840b003280300c01802c141c955042da0a000c40c0e01ca00c03200030364442c5d19840741000b04200404002c80319400d135056552800107260415440e221002e400d8503006400035005406101d828014503404c1511184c0e0100ccc0c040200700000243d10341140e420024040c2c480096182c14400751603001061000361048000e203500f80b1250600450203542c04004440500c0c0c0300d00103000d48642034160312400b5801c81200d000e16814014110400b204480c81a44c054078010b6180342c048070207490300b4881d061004500002681c40c244500c1c56564034500090000701c3c640e0800307040019008010143c00080d0f410174008690040040703074084c0c07800500c3c8103441d02d4039452078030141a211110010500c9020021a465406030b00c0242e01c1d000c0180034000210218000484110006899036400040030002c10300d00110106144404e18840c81d88a907a9502d0102203070143c03017983c0c00c110086450403043c1b0052 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 919748066 1250 919746816 919746859
    0x7030911060a051e360301050609010e040c0905180f19020d05010b13022101060e010e01020a0b04080c0f070b190302090a090501170a05061314010c050d0b 68
    0x10804440c854490b461001022013030240518403000c506400f1040341203842c140028601c502440140c003003e80083c000380101403ea600555003075030000c0340c05006001000210340e1107a0b0203800b41c40d41d91044c65903034586608a840031950011810078240e00261500f2050025000c2c40c684c0320002e0452080c00542c540b4180c940d450300a00c941164000e18003040710030b40190080d180700400b00541c18404103141e40196002020404100000e101d23216118008184014142c1d80d460f5100c8001700c0701c2400649030042903002441c190b11411400d10002130034802c800c2e02c92132068015949802880034010b14042d1a11414045a080030000f400b0140f5030754152a0580b00c0031075020340c110341007041500207100e200987c43c1c02c40d40b0100c02084068580c0c028604803600a80e4003484640564071442c2c481c8102036008085405c00008608180852801c0400c2e02d03016005540c0c3c8002c85000e1642125592a01e0f00080b03800404e40b03418907207451191102ca0481903502c549100c100290001d103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 919749316 1250 919748066 919748077
    0x4060305184603081503010515060313151b020109120302030903090a1401020613080901081e1e060402041a0a03111b0705010903021011010b060c0a02090a111c0b060307030911060a05 80
    0x9032b64040005100f0440398213103042055003005020501d01540f601d240c0281c0015201a0074600c10b004012580c3c0388148140c04d00240c10403454001c2e40c0e5012000c40195002404000c01d40c07001340b00010450780c84020840c020300c62000034030810612207001a040c1b0100400c0c209220020340425008526a00d040701c03248c490910303100312180e1f980c1c103034802040031011a100d070404641c010001180604a07080d000101c2d031542d00200350340d540d010481079101d10b01402000a40e40b400381d074818111a40548640032142c140070484440300807265840390002642104240e9039516802070728082031100300c0107004d0a1030710700380081c01c680105150311101603105042001c003500c00300d1884001e43c01080b885000804c2c0907950038180d5905680c614000c07406901c600c2070035002c210900c110340308070103c0383c034200a190304085240d16150b011200c003c2000131880e03110107401401d0b903180d0004620401e80c60310005590049801c0c0710604004c000610342c001d090801607245419003103001d448 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 919750566 1250 919749316 919749319
    0x3040308060126040b1b091909050f100f03231609020a120501080a120c0219150c031209020109030804060305184603081503010515 58
    0xaa241d260301c00100c07070312040448121440c106034640d01c804100e01012460245001c3c4100c20240d84803a0050340c420b403020050b08802c44010880c0c44a1410101943c0d206040c08100f40f8615580c0c42c98144140c1d030049035064801d4800004100f42040c107920900e020305060070015081380d0465860740b0010300c10740b4102407401a800b800300f85100d800c1080050f149441d020900310307a680d80f4041d1010f50040614207000c594401d000c1e1490382641d02c41d403412607006400400760000c094480300050b01c0100c884204000f0b5030704030000540c65400d501d442000940001040f013924100e45a518145041000c1042000405540c000f19520a1000c07074404101c6100003401c01c042e1005846e41601a4002002072001082c005641074060f07001510414407c25661f0f294980001810384418070801c1100540300791101d0500311107044034800c11145140c00c0d00074210001a801d40b00b140002c4041100019002c000300666204100490b01c03503020243d00034000c90030400e14100d00170040c2e0403030070b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 919751816 1250 919750566 919750577
    0x209070311070228080c09040f0302071e0e0105042009010e03060411150708041824081905060606030a0b060c01090b1b0a081914040c08060903030403 66
    0x11038480703001e0003228507207603009116a0003a0a5018100c030401c102d40404002011000c20008580e000880d01171031041000b4580e5079035545e582c5e204030108035450380c00d904502c960385008c40c0641502031010803040442103c080214a04200364842280c140c0003280100c2c200f030341500111641d82d40e0300944c141a04011031f1102603501c0100d41004c400009140c0c944518020300c0140880c001c404400d1904c280c52a602180c5c81e1030151440b4407030b600004011050411081240c190384d0a8074810744400040085600203203074556007610420030304070383ca017040c110908000d128810447c2c00030000784c030300528581d140141c4445849910043c580d5005010001c00140741101c59400340d28840e60080c515500d0b04894901c150003004100000c580101507600403460312a10481d008841e0760f2291241481c00e0420f0f403080300c04c40d2000d03144403500700402c1c1004118022a001d110340c20101a81043d5051070242000d06880f041c980c044151500074605011300004003000b100c0c0e000b900750401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 919753066 1250 919751816 919751831
    0x60e040f020f0639060a091a0103050616032f0f0f041508040b061e030303091b060702030303040f03120510150809060711011413020a0b030402090703 66
    0x710321501450710750b2580c0f1510004110b98602c03095500011144c141e003003804a0700803042007555029907002c5802100368841000a400d41d82c0d19004200c0142c800c1304140f00b18071041440c800d128030203070811205500880e00308182c026110170048031440d02860144100b2490b00c10400055080c10200036550744142c48050380c0081c07c4003140c0652140c900d949980d40c00200419400d0380190090103001d05804d4405940c8601c10010980200c0e0014091103040d260321040004040c02c50a4440348440043ca50050540d020310166100b4102980030389020966040040c0320801a0320f07c091203202d0920121002da100041035941c000c5d032103214094115002e0409403025410014103823506030a10041100f48080288410111094011071410007820400d0556050034104d1303405004d50b0044000404442c411203941c80e1807426100002255159907512001d4440304480d003070300d400300c01c04c490011410000d4000f00100005002c441c218141980003c0002e40050880c40805440707041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 919754316 1250 919753066 919753069
    0x310090201210e120a0f0c08030a0b1c030801060e030f070902130902040f05090c190503060d0602030108070503060f10060f11030a121a01140d18050c090a060e040f02 73
    0x1112076055884030468a41200c400786805a0340c0c1703c440004c000030309140000c417006020f5000b80003000e9201503424203550356480c1c00c60082404501055110019681010054441c444201c400078002d60345c0c0c0912758140fa42c003802c171041c00b600450103079001e8000205c29400c04500c9500380d600c21100984d03540705c00300c02b40721880300d960450107070349100060000e6042a692000003c5420a0b01c0221041e41d881c0c2c61480c5030b0140d542410f01c002d12010600003801e104600442c4e00040003403400e1b0740f00c0201c2d01c809080340c00c240c0290074143e00c541c005000c00e00c1e0802c21150300100b8034003000b95074900304c041c0b0503d640c494424501442105082c014240d8042c802842ca0b51420030704481e1140303064072008015004032502c0540da645072031b41c4a14013540c011080321500e607040e194a403407550141c0381142c40f0360089045100e0290744076244c4095400c007910034a0f525001d10020614424071104200300100054002142d07540b9210041007006104840681d22980045141221026900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 919755566 1250 919754316 919754321
    0xe040f0c03080f030a060614071b091d0f0609030a0e063a020a020705060f130605030106020c03072607080106180b060a2f0a0602030402031009020121 66
    0x70002450b480c804515082101c02400c003851140c1c000190078010b96540343e400740c170b88501c00403c46c400c00c071042080780302054400d4800c65201c07040205080e803ca980e0440c1d1011241c280c00100380c107489602c004005c40000b00202c0380c0c5444100081e01041c18400791159883c41610085828000080a024100d03516042a6082c1c40c1c2924064440c81c1319030500465840c078444001d20b00b03445000e43c040c854215620a5403103608894004004060500040000c643c003c402c0000c0000310420090b1032860511a800e00101000d403200c80e203950400c1000b82c00c040031005418042ea001e00c03410080018041c0700240100130192600d1801c0b40c030a10164148402c58000012641c03d1510020700128452100c040c2c03ea1481c1c410021502c02c44200b02c01e911450031325000003201c0340500041002c81000d0380c40700d0510b00c2c2e00d0b0300078840c00001050400301203610960352254048200002d60500303106000e0b055195200030803400101e640080d1100a042580714803080f04164403448802107035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 919756816 1250 919755566 919755569
    0x9041509030e010305070903030f1d180906010909080706050612071403120310150c060608030405040e03120a05090102070215090109080616050d020706180b060a0e040f0c 75
    0x211060080464a003000707003480003250a0315000034501400039290510078030040040e6503041d503520f146d07941e5103141280c050000c0200400a00320303000a258299a80a0800c1e021055024040540b4a4000b40050400005901c805007681c1484000000100c540e000c6400c3c460f801200002c903a20b4200201c1c0c006100b80c002c0c800d041c481e444020420b0410707906e41081040044003100c0810b00003802c6900381e804143e56428111540100c148040e86200029a0010710300b4a40846c04592a4590700c055604a50208099400c0060b0900450400340281620444108015403405051031000d8480380001460800b200342d039000801d0304554290108c840710341d0001c0c0507120b01350101d91501c186512401c1014041191900300190b20207000c0b0710684034050501510f9078500b030681d000e58403540600d40d0705000ba40e00b000044005505d902c10405800d10807054132000581c0d61811400303035500942158480c01d10090100030310301188a00f607901c190f0040041101011601c0c04d0302c402000c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 919758066 1250 919756816 919756853
    0xa0609030b0703020f0d0b0f0f130c020a02100504050a09020403030c0b250306170a0f0f081c0207060e0111070312020d020304290c030123130b040b0f010503060904 72
    0x11b04000b00106076001441489011100310501500304400c010310034000c070a620380c00090728011603020038880d5012280c141c0300d0780103444243c651940020860042c0c0d4411030003190001c2000e10082c10450760381030140500090451901c0c0c00d50320701a0400c01c0103000107203d000240001750102803070f43e00c2d003601c01805196005807180b01702c0c0054081c00702d9000c2c003840450364485101c48200c0001d1900c420325003002c0c514040305540d40300d2101018420301c0c1a21071250410080f524944082802d482e9039001c03500042c0c42c0c110f0341c5000c5050328000140c0c0945070381032440140340541010304803000160301d410400d558103055103021011f4024400a074607000c0c408000c010a03c450100300c2002c0130200016802200103000300125014800d40708102031076020710061050404180232201130201284941800c03c14890014821002c80e2054221190b103642051090382024011090807140c02c68000780c0d54902040020541e01004045d0307445202c0183c0801c00b400198044224074411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 919759316 1250 919758066 919758097
    0x1d15030a080a020106140a1401110f030307080402010e030105091e01090c0602030406170c0d0b01020115030c050307140310090213090803040b06040207030e040b040e0f0f010b0a0609030b070302 85
    0xb229140a40281040c2c81554514441802038041501d092402101941d154051683d86409030b200115640748c0600500000c5118000c80130406020410256205104656990216290903c0010001407803504243d0090781800c0500c40d0001010a41c0b4000c2061101521001400c8800003809070111880240620450300d101141440d0301100810544440d0b1b00c0e4a20300002c5265807000201d0301701c407581074140d002c0c84648400d18031500f181038544014800810354100003181c141c29030403180d00454100800c1c2d0010451800c0910190009015510520141000380303004a034035404150341040e0b58543d10b4000404540e202c002210031320340322200c100014881850040700c036501c169410b4581c45c403ca400141c06207082d0003207402d4154155a19108581c00c02c05000103002050107850f40103443d0350200c540540204042c50b13640401c20001d03c1421881502603007100e101c0a4007500031a050041802401c2c2c0005054044035841200c0840980e0303001800c8000340a20500040110b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 919760566 1250 919759316 919759327
    0x2100c0611090906100903030818100c1206030f0f2f0a05060f0702191206051509090616021216020102010e0106050d240e0312011d15030a08 62
    0x81c0380c5015264425003624080007540341e6004201c1180d20344910b0000081d20700c20103000081c1311780310b0303da007080300c1c2d03039602c0c2030b410b81e2011150070320645400030780c1c14507515030021514a81c0300c1412200228083e00030040749040d40c4a4210022034103401401c4001c01c01e07040760070030240e10344001c5540d406903030441e07251030402d41c0884130144c0c0744040c6105ea0801100410a132409408940782e030700b03c0c0784000d2b2503c10140e0a110920741c0c401031846110410040c00100c10b030303a06000500c001d2040b44d00080c0340c508589020011003002c402c00c1e0103986082c041064958000404580260101a40b0b100d0605011401c914021204c3e0041c4042e01c404901c11050498140b6a80c4855100760020700c50b86000c1c00c1c3c658200d403054810154030648060700c0d040800d41c2c5400360341502c403d140159400c076040400300010756072404031000c0b056000081d031030324040b03042d451a800b5044105010b001c4800c0d008404205960141c540000603d02c015011072980d0704220100796580d221000c10f0b10303607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 919761816 1250 919760566 919760591
    0x90d0308010f081c11101b030e0303040c261204080d0201290a0806040308010302090f150603090a2a0504090510110d060801150602150402100c06 64
    0xa00c0b4107030b0780072007100000c40c42410100388203601d0201009140e50200307200d80c040f035240e030310519111154000d50043c80c00030f04040c000d100d421100c00000c0c201405104000500310740b080140300c002900184103000004900c1c0a43c80b0444454407040030761100d2000102c00401d107180346003129882042150000303069848041c00403904020306403852994000348c140c2c00e90307401c10140b8030780c259480100440f40c9062000c051009801621460040303466158044c9802d130147d80c10350201e075400c40100214500030003036a40c03107500e50300d0862040c10501040d4800b017080d0544944184408000a50081d0040281010007034200465603079044244c6c0c244000b201400d414100ea0070000b040104403814079004420b025a0f0040041c40c198844071241c1c0000c3c001082e40480e084410403903103640c1c01181c05003402400141c800040e4000c0c400c90084801e514952204007503422545a0014200c81f0700350059115405507a006003010b80b00e20b04030b6005c2c10100700101581d15000828196 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 919763066 1250 919761816 919761827
    0x15090204030b1501020606010804080a03060e190c0512010504271121070e04061b030b1e01051804020c03070c0f0b0304050304031509020d030e0108071e03020f090d03 73
    0x5166000f10200c010110100485c1c58210444090303010641850100e000a1464001003503084954600001c5460f11441d00c0d1002c1003003601d114551819104060004130154810416a0311860814a00e40349000412002c0000d052040c0c502c95070780c1d0300b00340e400320852484048010312182100150388074241740ad00c48500700e0700c1c0d1050040d102020404685403502c125110b00045080040908034640003420180c058020f0003102d03141c8d1203100940c18054000c0301c0c80a036058a84011605510100a200014601440c007c030380d274121100300d0301e42e07903040070072502c00500c0f5081c0b15603240044e4002c0340c00317031041009010007031000244410621806000c144c094031020714000442030780c3e0345203504a0380002d0341c003d407061f04104001c00001c2c07011030700b40e550400000fa0205510305290005112000350b4070040e0003081d002400d032550b5680c0002a1684100a401c045000510240000c3d940101e002c1d000828194001124000881480241c0701b000400800140c0c3e030703814a180081c807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 919764316 1250 919763066 919763071
    0x706051c020325030213051e150c0d02070e0f0105010816021c171b0a0809070b0313031205010b0913020412050304060f020f06060d030e2d1e010315090204030b 70
    0x56940b103a0011a4a21300219034124002d000c400c4880b4023214082082a545160f8004551b540010025044004030502035034101c000242c019108051410602003a0881d0045c01030f80f04508240044c02030b6078004080d01d0f00b00710f0008100380c6120700d5600a0741352940000c1d12042401c50200c0120180e40d01c5200c4880310080419081500e4880308003440070b0942200500f6050310040c0703c1304010500c200c005640c803581d10030480f6038160341c0d021000041e50040da21040104196140340c001c0c940c0080d0f5036103200d0402c500c00c200662404515603003d0284080c4144100b0b01440b000034010300320b4045c1c1f40609445040c08030f017000303645421f80e580da02501c1050081240c03100101c00450002c600c800c0004e0020000d070445503180b000300542c6880c01e600c2241440040d01e801c00c0c05450303851030a00104100c0c0000f00c20001c002c0d81410361484805801841854180720052001c88581080190710100782808520580c0ca0a001d10024007160031031000d040c0b011500009103e2130300281d50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 919765566 1250 919764316 919764337
    0x20d0b0712050c0a092111180702030a030e0c030709020f12012603040303170a0e1e0f1204091107140d0e040b0d030c020f0406060206090706051c0203250302 69
    0x10510343d07440445549060300c64078907031b01d0141440480000b00b051429480c01a1341c005103881c000c240144002d45075510155007160050b0b00125142d000c040d01361003207001035010840105031040c50900082d5850905008005a55401007507101c08103c00c042a210000400244c148882d07840d1031240602000e852622080c0191014403202a02000700c00c4406590701070799102c0c858000f503140e20404100140c02541e02d16076131040969441c0c0c09010111010200f03001d07a508513070014000f00d203084080b00780e9903515001011543c8201c0f158000f00c0f400c44101490100d0103071400172501d129401043c40162244c2012045d4242032000415220b40d40036160b155440561200d00034441160f0050712025041000030045070301207805000c1000a161004080901c2c611412020500b40c03180b680c04403002d03910030811301510060511540c4064446468505e007030a811541c448245114000b402c20141c0c0c3c00404500ca542c2403200701c51a00c49100000404005a400000c00a500a44021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 919766816 1250 919765566 919765577
    0x160c03030213290915160f0807020f0103020405010f0e0301111306080c03011809020a230307050f0315040507080a110916020d0518130b011b020d0b0712050c0a 70
    0x2c40f00100e440191118038001520b2288a2407030348984800607405440165500d940b40f1100500042c400760015200c0c9101e0441103880c1c035000e1040c40060604850501d040c140140300501031070764017201424500ba0203240000501d01c083e00800c0c0105166a171031800180b00084880700412885050380c02c590b0380da0340c3e016407039a42c072059035440e00081c000c0e18168024083c00d8504140c07290001c11899000410410b042980e940045a801078140350241c01d00d034600c490045545820f0000700d004090a030341220034580d030400060b0700c4881c800421080e0384660030214040c807104100c1036020780516000c1f034610702f0341810038028880701d02c10a944224198800110180c18040210400c550303160018541b10100035029640d9070401e22001c03151254800e0100e1880c0e8444035400d500c4c5100c024001001070200b40010408100c00d4240da0b003809401140c00d006840e10010309000a8100010f00070390b45904100301e80e4211960702e60546282840c09000c04071619000615000c003a036290b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 919768066 1250 919766816 919766879
    0xd06140109090b07090315020a0513061d03060c03010308070507090c1806170424090b0105010906080103050a080d0b040e2503031d01031103041101030f05160c03030213 74
    0x4590542c1175010080505201d00101400c124994000c0c00000813281015410458800d00049044c1c00b1944104000f0306840a0207240e1940c8070454100044107602411851030080e044890510041c44010a0310800003044014400309001c803a002c2c000900781401080c2040c00010700e00f076030000d903825500c190b01c5c0001980c0b81c040c440342150303224844401800c0d940d407a1140401685807400d82e08101d140185110540c010340d02c6007032200d07441100b40090340e5040500043c06291039401c0385050100100040c80800d0340000c100d0710841d440792000fa0340305012103054010f03041c0e81000c241c101c1c3c03c040072003901110205485403502c4200c1d1034000140195081070103000554807014010500701c0c00101d12586040001c80c44c220010304000c02c6a0406450203072aa9004480a86170b605000341840f01540e4140214400080130314000d11560500b40056800b120041d42d030017090004101c2c2003c1058000e40584030303a2151180d451511507a900006048954110411f115181e4400702 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 919769316 1250 919768066 919768081
    0x105010b0309062e060525240605090f070305150f0d050307020312030910090b010b090a030203010f060608130f17070b10090e010504030206060d06140109090b 70
    0x2030781c0c8200014001440103860710070704800f00503035115034146111030111007000a403540c480e2072001442150784582e90342000700009a002c501c01550002903e000d800e400000c21542c6603440300201c40000504c010840401841004201607403040b500082194100700d4100c50b0710700107038440c40d8035403800e100d50707074409452001f890820070041d944800c50644014450411014140407680b00d001240d1510201c0d400003803a0081910188500e030100008102802100b4460401078070700b50402482500d070749036507034040b81e4030501421000500c0450380c000b00f0b41d14041410b00542d000b400802ca05600f00d803011001d400a03020352800b2607500408210b98000320044600000d0b005001c200800c1c1003943c0341491118807140c11307440094107028a0020400c81003040b401240340392249910075140c0304d2200c080c0c031400e04120303003164507003410407007c69004500c0d2a44000112007444181440340792090045c1425400c0030035146400d40003044101459000301c40701030182124170042e81e900e07207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 919770566 1250 919769316 919769339
    0x5061b0c0a120201230a0c020c0909250302010804240e10140108030d0902010c150606080603240901020409020d0b0a0b1c020f09030a15061d13022b05010501 69
    0x17070407a1a0304484400643e09446507030000300c1c049080c0c4190750b60b8001c08000601d00050944800002d0303001000141500401c20140d940381d4600261012180c901e9900003a00c41c0400401c0034014202550300c0c9608984a5140000320340c0f104403003041a0071210010310764640b00485221042482c10640040b040507081c0e0650407152444d0085190030004140e1801030903240508a0600042c00425400070705079074920a98100c24a5002500500e854402000041c0c0500200c1c0a60807034041c802c0c5100d5640980c02c0030a0040709805030980f245d41c855402407103203901280100f44080703000080c070340b151b405c8064201002c0340c9000030b15842d00d02c1c0d40c41c248165100001300185168480301498981d03005482c0e580c060000c054103007041d11000c01d090645529044444840e02c0131403c0c1d41e0001c81c40740c98090029040082d50040d5500d409c81080580504104c4000c0c141000207021980d9107043d0f400e00c156010b9120089031b800d05000403040110805c2180ca035402c082c004110b151295 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 919771816 1250 919770566 919770611
    0x1b0306051b070809180c0901030605010c0201050702040e1227121f06030b070c0b070504080c0112020d140a0c0507080403030e040f020f07060e0a05061b0c0a120201 72
    0x1c6a18180711036850340c07115402020901d8120a000c42c8412203d4500c101040c40b90311038440741340d070300c41c001000101100c06030740020781404454040d81d00541d030700009540202c0e9041c0d600080f407400080c130891a100754030803035a84007180080c150000000c0c1038a41d0300c850f0700d014030681024079110b04100707140ca0000c9003031240b640301e081c401c0904140a03890758002101c141001983c142c580d00c0d0745240260495031000481c10b0380110104120520780220f90140880c5811349c10142040c014540350072070100c116040042040e0803031100d0141d941105c98000c0507078010421030702d10032105290840d044691041140ca451007030141d0f213020341c0455810b140d0101900f850b09055543c26581c011740c10b101139030440e0fa20341c003401a1003c17a100a00803840b0720881c00c1c0d150025480c2600590b4034808103803c20703411142c4c4840010b14001441504042c1c0c0143c3c640170624500c0d08807015000782034401c0320510405000c0710a1042400301248040016030007400903414408030f5244240c2031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 919773066 1250 919771816 919771861
    0x13060305150603061609080709050f070309080405060702010e0d060509070f181a0406030b1b0711060309030721121a0f01020109080d050f0115020a03030c0c1b030605 73
    0x40b91402c050105401c10300d81c0d03040c060042d1307455114151405208d9040503103502e90307902c1031000c0780080380b08044d4041018902404001c9041d51040d409006612803940964000704201e000c42e80030b003107070000580010307002030950710450400c43e0141006032891502405540f0b00804e00026519060b001c0d40c0303c050303031081400c1d22903107150010320407030725041340b882c000c070966a801e681d86009440044d402490040c0060414043c640c1007034140846540780414100250030000381c00f050805c01845045a03010740b01c1c0c1e94600000d083d4072960500500074001140000c8410a4001c1107900d240743d269194100310516102903005c850070070494810550000082402c5844d0440140d0721008040c170020a82500a6842c0415500100c101512040c3c442e01000705414402c4840b170b00502c4900f01b1030140d035203c00000b0391a04000303000a070801d6100e0711944425401400104c08940d84146184801c5044529411121049020442e0210308210108000c4504008034640c880103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 919774316 1250 919773066 919773073
    0x7111008010e0c071407081204030b0a051b04060203040e0a0501050915040204081f0c020607050d0b030309090a02030907050a0b0904090606080f07060905090408030c090f13060305150603 82
    0x2c1408030008004020510360603904200031850014034415001608400540000c00d1200c0c10b1904090401c3d00c03141001d0056002880b081002c111300c0c03501c0a42080f1726410004a64644416000c414900312280343d90309540010000b840c41d6001000708221009944030105e2074a4420003801034410a200703860f889458800418000e41446090107001e05000f40700603c1c05540b68045400e02c01051213007903280884a1440381d10304501d0054030b94030035051019000d80d181100c0c0150a0380103010b00c4410031030b61010400190344042040354440000100ba600340d9203003d0f01400c000c1e5100b103031860540d000c3c100b400a03150802003484000c1d50404403201d400e160140042c00024190160240c50b045d03101d40000551034410300c408031000100c0009400d100f41060400b42c0799901c0740d4800c0d4041c1c0718a03000c0001007103054003035076048080e101505565402c0d02c0c00040344d022040101a0b03104031403e820300d82802542d48054100c03440b61741642e01c644402c001c0e5401d42c0d002120031542540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 919775566 1250 919774316 919774319
    0x2060106092615090c01020606042705070b0403060f1a03070621061403060906010509010501120f1515140d0b031501291305060306040906050c0711100801 68
    0x24520b8030030800003054001101c1c22001440040410000d060340d8800c1541c01c01c3c0601c072119603050140541c020001c0d981400144150001001103090b01041030410042510b090001c2203001e20801000745243da1449803035580700e0070f000b0000e00d0300c40100a4043d02c1e2420100c0c01c0c0071284c0300001c41e154010090400680f50136800d0f070f040000c020401e04414140580c0b40c10074111840b80d00f01404680d0b02e5900c3c6444504140340c6440006015107072240c1c0303c1c400400050740c03550403450540b5800e2038001ca42039108071201c00542003034680ba81a807400c0180f08000074007440c00b02d404440080301402e02801d102101522034104580384d8054940c0c0421031220044001d401401c03542c18050100c0d5541652254603c0142c0d4081c0c00c00d115440000c5864900391046500704000e9440c40d2180b50315140e0700c4100c10060f926148070b110300400c00400090903d9585500105070143c00003814805032a22000e035a155502c00340c0200e8410841012480844c1402e1096800e03041107a111141d580c2d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 919776816 1250 919775566 919775609
    0xa050106030612050705090a09230c0105030f070c0819020a170f0403061d031801080f070509040e030d021c060e070917011107050c3f2401060206010609 67
    0x41c0d2004103040001510341d60309c500040c001403401502c4e5446032600340f1036200c031400c0c0c440c1025a035810040c1000824020301c602104000952900a0141e040036869070a9500e8806100e01581015400e17041408489040c0260080384061000303100740380c0c07460648545c421140446c0200c01e40c89a0b503020a000c140002480c50740280c1017a40c0606021481c000640c0c0568519806090b107140250000303103110140f560081c081540201c030681b548c3c100303071404001c020024011140c4103881640c07a8107815103a0f0b0800e0046604d41840800c042d987c030700300e040a82c01c2ca2042e05040c0414130b840c1010015482810380c0300b6a025440f00d49e01c0160b168640360f5507c0390081c1c8050840c801e9540c45010001c1070100b00c0003001e003984540c0103400003101190800003030b6132102043c90000105c020800c070007403610002402400380d51000202108200c0300031946841c5004268203284001c2030407481e4541c00805465040301c0d2603500b03da4241e0f0301e6940844000c2500d100b070f17000c400d02041d200040e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 919778066 1250 919776816 919776829
    0x1508070201020301081e0a05010606200a0f0f0204060312090501020709050f01060f1e20010935040e10080d1e0e1f021002030c03220b0a050106030612050705 69
    0x2861206c086400f002e546071a100c1c01c5400341da02c207901250041508400b03200c507c40c184030b14800c88801070a10079000c0d0301c488100040c0564018001c00c0160a01011035490380d01c01806160404207441d01c143c5055405019401c45005190141c852060009407400880c0030b124842d103a413003020400e5920b800c2c03095801ea004070b034165003400180040e00e42201b00344c0410101c5030480d1b503211868400d80d010051103001004800300c2d16a410300e501a004117810f800c1c030303c0a00d21594003003181e0080842c0000316034003900700c3c150700520b80050002418100210280d0060200345000380301c01717998248080e0b6a07200c00d41d4420204280c00b003482c88103410303201d04d4954070700c581c10030459a008413400100c6c8030000c5400c054610003809004000164100800c6090750440c140840c0b035403c150380c0c0a4070340e020040c005607000100130402d00c07051740107503254a151907100e4500ba000d400c0c218480f0340608030034002d0340300081c40e01740c1c00504440d160030700c00718203a0420042e180f101d0030903003030054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 919779316 1250 919778066 919778113
    0x1171b0d0c18020d0c1d06030907091a0118030c0303080a060b07030f1803081206030a050a060207110f010804030807090b0d0b030105060414010e040615150807020102030108 76
    0x329490300e1480081c20b642e00d0345000e40310300c2c014100180e89030010040241110b12a502403010001200c1400300040800e08408120761402c03210a41c480c0c0d2410a000c1c41c007103290300b008503e28240340300380306442a104080d020504003625901c0b00d0964280c0801000c1c1150310029190101a0328108003285c00346a4543c0c00c80070118010500c00c0d1904a604400c3e44507810440c0010403141031401560333440742c0e901f50304c000d032441082070703407480c50f1102c080700c0c014040e1200642540d403012803003e560411a18240a500c04180c03116486581040002900030392825607030a08030f69042241c5142001c900c0b08042816140c480c8191110b460894507420010840003d1128011001c1400243d0401a001d2200a032102240b50b40348102450b095403c00b9052034041c0c2c1c14020500c80a40004505505561906103100915904c1d13042c240c02809030031100b0500c0d111400c00100d070070b4000444004091001d0b0b1508a00d41d220312808078202d10091044801641201181c5006400314101c51031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 919780566 1250 919779316 919779323
    0xf080403020316050a03090603150303140403120c050c0609064f05060a170901090b04060b03210a0c030509060a020105160f0206040326040302010501171b0d 69
    0x28100394201141001d54581c3d15010344080d400804107000300356000078400081c001520f03060040e810352210303203c4c1d98406401300a09000000300f900c100d4581c0141520000c40e0030410080d05050b00100c0078200e442c5a540031340c2c0358021600000c080f420950111090520040d040500e0a4100390004412501c40d4a4007001c0c01d514089040403183c1c0702003c01441c034048118241c0c0711010900b030b00c0d0100c1075903101d070340101402e0213648900c58009402e80c001c4016100c1401c0e0513500e102505004102042008240400c0c60b000e010502066501003d45540c0a8040304c0782c6000c010501115800c264100e1400d404040107040e400c42c0c842d03c8050740c06071090a1a03814908a0760002c1c10b15003061565400603035540c000c00507203590740003000c400e005150800b400c908048601c02501c4034001000030301030103d4244804060841c5000c860f00c01c194400507140d90b03081c1454002c0c0039081c01c0c0f15401400596a043c02e1015401140c0099001403010709275a020f07880c2400e11a40200040003034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 919781816 1250 919780566 919780573
    0x150807030915060e160e090c07031205150a050906090a0b1311090f0603091002130503010e1006060e03060a18080301270207080d0e0304150503040605090d0f08040302 73
    0x20b0384520098003445010744120743c9110314030320300840c6504181888490807410003c103003000c000d00d030311a07000703403504003c0d240c1c03409076250703281e082c05e841c010304801c8009501c918240411101c0c0b040612030700510102111502c5209607148104603d502c030a0380d00960210368480402d00d2620a0390000c5040803000d810750041210510410049800b91000c125040400045114507450500103244100000311011821809d00d0544030f5514002c1051943c0d4541d030000700e180c11001d8141d00000200342c014020321030400304c2500d00e612001c03000c5c0c4224405042010114515000300c03032031f64030800c3c00b07002840295240d800c840c3c0030308100c029a12003819a0300c1303214085000c3d10025400780211302c2c00000341d100103890b40d0469a00190f444a20340d4818404040000d01940445542820306007000c108144c0518000c0d003144100d5009030034a00c0c4100c0d0a58005400c10080c52180b800382600304000d030707940800c81d52182000044040080c413550041c0d0003050148491640180c001e01c1207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 919783066 1250 919781816 919781843
    0xc17061e09100c27090b060406080a0c0c170a08010e01300209010806160503100314071e0f050f030a0206030a06120803090c0109080c130f060e101508070309 69
    0x10b0240c141e484081c3d80c200132101050095040303600074207050308402e86030640790500d0160014801031010305207885194440f80f0b403400c41d510648a0364102900729101000140441d40d11110580c495419040801d955800001c0c40a840b0075010b0304070b4507045104658070b00c82c92005207582c00d14003191380903c603046254002507164040142d019040320002808030b4184601000c90788072560004008120080080002a03491107214408a136886030340c500311810011806810010b0031b4101c84010342d000a0941c101c1090b040e141401c8600002501c200c05403940705000440030764102194266024559880c014105040155401580c0303600005045480e901c0001c18000b15803401c3e07681e401e0100501111440074002c9884511003400c1000080c2c0c030302564207403130303da0b0008910300c10341400a04180c0c6000603000b9030044e0401c11400c201c1203032988072400e0030410540c2c0039845100d04000110790042c1c0f98240168039a500d44030f0200715aa1602e040b0080d000c1c1000458422001e80741 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 919784172 1106 919783066 919783097
    0x130f03200a18020d0c050301090e0303010b0a05030903160c05010801060e0a06110f030d091202280c030b07080a0b060a17040c17061e09100c 62
    0x294118500b0503001e104000e029026552100c2414141e840d40350760361050045042e500c9100041100c088010340b40d42d41c0c1c0c0000d00444070040b1041081e131400c0d60040000d140c0c0141c0c00c0e070444e0301e0004401c08404640709401c00c06ca44107842c802083c4410741c0c000745514094181890000c0c00c0110000c0050b001200c80c0c4294810712001c10360545030a0070501a1201450083c011660754041d01d03080750000340586401900c003605143c4888111501c007180b1104207a41902507020303e118405a40c0304090b0005008480079800c1585c0000000c20080720780780300d074900f41c94410381c031b103080c2802600359096001078030701c520030810150103403a4020741000c10031640d82c5250926603031a440c0003590310070241c20003078190b8081003440030221000505a44140b03410315880c2c0801c0200169441048030a40d22041c1541001603503943c280f44551210107220b500c0c0c6401c4451415451 = true := by decide +kernel

theorem cover : BRFrame.Cov 919604316 919784172 := by
  have h0 := BRFrame.cov_init 919604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 919604316 ≤ n) (h2 : n < 919784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
