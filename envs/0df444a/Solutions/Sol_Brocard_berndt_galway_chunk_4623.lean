-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4623
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:12:51.016988+00:00
-- url     : https://prove2.me/submissions/551352d5-935c-4f5b-9a3c-be139bcfdaf3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 831294964 ≤ n < 831474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 831296214 1250 831294964 831294991
    0x1e10030c0318051606080108060a0c140c030d1d0c06090f0d030216090b0a05011d0303030c130e09190c0506030c031e041115090d050705010219050a0605 67
    0x154420110760701800c466100b240600004c00c062200c1211518081d409071303080040880040004c0580841c0c61604482c1c820004502000f030f8200c1565908021425807e100300002a03a6103484804009420982d07407004083c0510381c020f407411014800021003829550f005450100010314000c40100017030300020f061075584241c0e10700001c0300c0a120241c00d5015812620035a148489001221000340900034410030250401c070010035991030507130162030b05004818441c0a000d8030703040c0f14000320000c000c0440c0c4e0340789080d558016440c0c1040080088001c3c0000f00890040f0403407407101d00c121001002445601c1c600a01c080c80d44d620300b0b50948600407030207004101611854001c6114400c440005580c0703041075894080d5441103001466901801d000610001075015918400040b008480800e41458000704c3c0e110b16201e84c421007940b21900e10b1400081000100b46001101d801340c0a1740c6841e0248801c001c0a50f60500d0000e1140d00140704d003100080c026400190806810b1f08006c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 831297464 1250 831296214 831296231
    0x61003090b0711061003030f0c020613081e03041a0f071703060a09090c0e090c190302150406090911120f0a0e0705031513201e10030c03 60
    0x10740c001c0c1c15500540000c1c210b074541c4400c1d0508001141c1c20802c00041405011b19544006008003008220b2030100504001010b0179950b0350820f07600340e4100c0c036070072081c0c45075101000d59546200004101d122103019421031800303e0048140e40848074a0318000c0c1e02c085480b40e032600075a100c140741d602e00c08001d2100501241e91100039291f42d04e2581c160315900c0c10a0810040341803c158480d036011805c0c900b4401c0001d01290341d0b1000ca40342ca42d0550956191070240314188005509101d400152142039242198040071481c1e08490099440c0c0320152181741c0e03041242c2c8114040da002140400c0300c00c020314a401c3e03010064603c0301d407445605103000e14846680181c001d45184050f12076031b00900400010f5842911140d100340402406031038a40000300b03072189840a02c4291110110000901c40d03a1003406401e030340d0f0760000344140b484200004000b46440d07000c21250096010503040400804001030300e41c07014200402c0520000c04071301040300030b003450300004800c01d626032010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 831298714 1250 831297464 831297473
    0xf090f070b040e0c04051810170a2a03030c0203010603081b0d030c021906090f05160506180d060b1201230606031f030206030a050601020d021506100309 67
    0x5001500508100555942c0f40010003041500058503080300040108810025555098050301c8000f400b2413900005542e128442c414008050380902c0085040d18940c210188007ca0035041c000e125080c00b030031400400c1141039078038038203188079400c8400305002440032074040c03071940710940c1c402000072a1042e1256990101500700c60307800901c0c0420b5695042010805009047e0140b41c0c2d480c0c2044428000040203545006002e0041c0d035441c4005d1a140a00c00d02e50090103055401500b01403912203503142003035031403a01209002c0c103c0001c04021904d850101f04881c034807107603145101c880a0000c0c0800101000f401e60458403c2d03a14428000c9a49842001c0010a0400800001c0403000e40e0710211940300406c103c1c1c241d03007103003c080101c255035540c10345e504400c202c001c0411411a4104039102400640c0004c2c1d4041004410441890800c1e00060702c41d0400b03900360f441004030004240d03074841c030401c03504000101c110009815420300101c4148150f6941c500841c01680175141c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 831299964 1250 831298714 831298723
    0x804170f030402010f0e0918070b04080d0f08060f06030a0e060c0d230f040206161b0b0a02070612060902160314130905060f10030c0f03140f090f 64
    0x21000550080300700b005540c1c10461042e40f600d403d04196103c83c0c56803002800308200180080d0741074141c00c4004000b601c2c204420310141c8001908640c3d00c82c0c88002d07003951204003100700400a60b448000d429407511030b22005008080203841e003815001400100701964100901441e052941da0402400915041121600655041c8181c0d036842d0204810041502c8020110b455a59245009111030f99102c40d0800d500107061107440b01662180d10019015214010740402e1825101001c0b00c00d200c151462480d48220b46071800034410b546000300c0e0014042c1c01e40b107801507005001300b0840c180c0a07012078108000c060390005030841d240c042c00c400300d81140d01d440c05c044000307819550405421122031100c003d1006c041a0401a0002e0042c1d030510290007903902960302c1c3c402045180c0c880c281550001a0f00800440000012081c010b0081c042403014130006413200a150008034002d10403da1388043c0428040c40e2540e9100d0003548110020b800240d06200750402245400418030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 831301214 1250 831299964 831299977
    0x210b04030e09040f06051f030f050106050a18140403020c100e13050103050c06090d06020c030d02070515010515090d020607120f020708070f030308060f0432010302030c01080417 78
    0x80d13160b280840c10b041038000c44000801c0343d80c68000756111940c010750702c1e0026801310f84c1d0140d41000c034207004d85480350241c801c1e64042608031200039008501240d644440c501171201200040110f5248410000101300e02034a0180142e00f081040300c1c0c180c10304458100c8062098103000c048455000d0104207060071600c052141030f41d8890050003008014064000503000841e40d1909100605000815084041c44020900c90340028911308400c000c4c020f4941d06c1d66510400c5440307420504125480303001d802030340100c00300700d00008150313480c16a444000708104603030418207000004047c811401c034440005d90340804140040c46c0000c030485c41085401807242d841d00615000380d540039140c10400d400166498010341030a00c030702c8841d00c684c00c013242d4242c90007840b503480e450045104040c0382c0c0142c5400c0340c10904040c1c0f80d200f404006952403813460395941c0203203e07028503403c1d4000003070000a40c541c00074003801d480da41c456000680c0060081004800c01d40c041e40070180c06901c040d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 831302464 1250 831301214 831301223
    0x91f02010c02010b1504120510050c0c060604061a0d09020d050304031208040308043320030c0d0c11160311010c0b010b0c0f10020405040501210b04030e0904 69
    0x401d0044092079081c0105001c11105940b00050300b01c0e00c10646540b070286001d07040f13807111070b0080c2030180310f020040e580103402c500f5410000c604006070490640d500080035010300d482180c01003080b82c1054810001204c1e4000c036842d0007c2307003c903044101941b04071188440e83d500c900e000c46c013580c0c440052400651250008607034681c03541c54101d070681c4840c81a2001d0103000d404210220f500030104d682d0103a8080700000d10390110180980005001c4461420000c810b00706140b036019450380328140d600c50030042c41c04031082c0c02a1034426403004171b40e004440902444030801c2403010350898069003000c2d00342a10b01c5a5000c03105840d00d0526041a5515950b2000c200244003450140440e180000e1070940a03d005980310701080d80010700c621600b00d1400140c050a809040c040c4010f0030001c030041e01ca00300c4000170707110041d4116002c0c55105a2401e00002074601c01c84031040101000123004100000c090f440d42168440010000c2d818800e0440a0502c2651032030201d80c40346224 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 831303714 1250 831302464 831302471
    0x1d062106030f03032238010906030c0b0a090317070b01140603060d0503090a030308010513140f070e130e0f07061b1b080d0f0320091f0201 61
    0x44020180342c40070041c8a0011a0001c00c2841030031406100054a44000c040016400e03c6441c60034426503550343c0246c4081601811004524800074005102c034000380b8480080d946e601e070921981101c0b041c2c4002403c4041c110320400108503070001401182d4090f0400054059890303c4490041202c0840107640a00003e2030b20100031a02c0012805048204580c0c4d12840300308000c2110741c0b002400381032081c907040c04842c08000080003124440308004d05400d00045c0e985c940604800d4081c01254070034000d080220392001c4240c0315818030700d0031407202c8032640d40741c4448040900001604010030071036030b50a142c0b01ea803a020006c0700d46260000b800148190300400701401d01c0a414018409604410700401200707509c030034001c0020000d098002c071285140d1500d0040c08001e1200e40721070180e0160300003140c0d032003c2103218003d8030716200d0003655400414101c00320b403030140308034080b2000c0108032032981c0c1d081c0010b4a007009000e0109003e1615801e01d2024800c100d54420006030b45 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 831304964 1250 831303714 831303721
    0x209030d050d060906060c0b180f010c0e0303090105071b03061b020615060f090111061f0602030309120304060b0915011b0b04060e070f0e180d1d0621 66
    0x700f40716a800a00c0890b0040100743d003800c50090090032005400303030807001104082204071000e03900d10555034044000703e41e024000e545129001c0d02d40102c418011515501c4902c085040102c1200c840c644160b40d520f181c00e503240c0c0c0f00d44400c0408402c8018243d84001e000c80055614410071a64524001c211440d21280d590300910340000100b00343c2d2820340d90462580c16444103c01eaa00f1011181c0c003183c0c071f44801c2c1004a4a42003080081822803260409021a01080030840031203800e58004000981c0d0310356000382d030360b44800d0ba015080c035444810b500b8000c040c40009140c02a21416002c1401203110380021851207050321540406007480e074511780c40c2e40e008603c12110001c68001d00705210701130744603504d44540040018169a40b900c2400c0d0300c40b0001c0c408040500103480418070096121204e0401050301180c815402003226046140046030028404d10300e449241d0340c80303403100c00000040c0b109200501e40a030704401c060000461a080100107140e8110440c1c401d65250b28 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 831306214 1250 831304964 831304987
    0x8121e0f18030a020718020d0216032303070c030e1905011d0d02060d0b03150105010e0a0302030604020d14010e0619090506040f0807080c0a050d090b16060209030d05 73
    0x824070102a4000e42c400c00031000701d2070b0085042003c95140b20350f868010300303503a07102d600a44100302032088214400214018240700d59003540c22844d0007580c039130081c80394440c004041d6068000f40450a101c00f800060003841c41086440b001074440c0ca414060304040c0408659007803032030142866032609510051000d560300900ea88a1406c090581a4081c00c6150104001c01c0b0640006070256100141c0c0c0d0718805031782c0e000704040500140485500c002039480c4505041d00c01e001d9a4001031100c448901e11f407800041e001c0c1581d40050180200351110386c00c110310081424000c4441e0350002038203426520b000c2c4035224958002c1c2e000b403d45460440a481a07000403044040d02d000d2130030141001140c0d00003034141c0d01c944e101d41d00e40c0918800f401d0011a034025400020404d41000412842042c1e012070200344681c481c408451003014007401c00d4880081c036004500200000703101d0300d14a01102e116109505004010061400c610000840e04180d000d54070300021a60016640c81d410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 831307464 1250 831306214 831306241
    0x708090f06130b1602150a030b0d0b2d0a1d0d050a12020c01092d02100e04140c071709030304150203090d03230708121e0f 54
    0x304201c841034680b5003003420707010712a40d46004580b8800408101c1600c031500920640e200c2c0f42c1c00a020300000f59080040441c00d50001c1e400900003401c0c00c3c148041d0b4180715800040003940075800b042c03a96560003415403001c001039100c0d180d01c055a190b000b50030a41c400c00c3d900584000d00007044045007990b01002d1313800302c200c2e95081d80d88080d10243d0665400010f81d01d6001c42c502c4d040f41c88401c0000c09a000e4094a105010507503e007071544410000702c1c2004101030f8640121a0200c0b1440c0c000c0310205800d200c8010307401141000c61452454440d01101c0b41d00b0b0320003040003481c040034203107114000d44101e6006214078070002d0800144074000f0200410000a100e0345840d00140d1000b103600c80c051803041c80c4003001c2034112441c9140c024002d8840c2d10b2000740105000d4049410001d11410036054030f0b100d106d51903445001251500d8048903001604210000c6ca8074142802c1181c0c06000217000a04d2411580120f1400d4295075440c00e0240e40c43e02c2c80602182009130300c15400c13 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 831308714 1250 831307464 831307489
    0x509070510021f0507140f0a03050601020c1318050f0f0c120c061e03071805040903050414030106080303040b060102150114100315062d0903110a0b070809 68
    0x80d9888070310724080f14200046140741007000c14101241680b41c08038240d86542d00c6003645411030350041018108181144054010544560707000d00454980c070b001640c48500700a0865080601140101c40d840301e203400403032400020940f02d1740e02c1c00c25616002d0038509043c40138811900304082409145100f009211a0010111072000c0c030b02407044840d545c0c540a20b4046030180c90040740c03000180841810140b160320811941c3c5540c0d182c411b5000b0074009030100a004a5142e050011074541818072138040c03140c0d072540300c180ca020b060941d41c0e807810100030b006079455900c680e40842d0901c42440654000c52003000f180c074040c21b10800180c141000d0300d203035882c02042c12004020000d50020406414441690030714107101440c14110080e1043e15520a10031550010001d80258444850b0030184001610054458468034030118000c2002c0400000505004801d01c0851944004000d030751400030042002241c0d0340c1c0314071001c0c2d04030490640b680100401c5082c0e05081a1100020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 831309964 1250 831308714 831308717
    0x6080715030212070c050a06230718090222231504051e091302030f0f0303182a0906040509030313050c1504260a0b0a0f0509070510 58
    0xe010760302045040801c4014101c4c002c120002d003103042440030170300000711110303044101402004882d24944c140c0581c0c0b035040508401c9020300180c01203200c2c41c00c2d0780c0b100308150005c07100b107450004990b01075080702140c0100a40d01400005510404074150760007400b4170607200c441d800190600c007082d041d4125405006400c0b0f03054003c16001020308072401c0d00c20032110001d401c0c0002d0440240045e140d443d0a8102c00540c1c1480a0303455001c403e811410b00c2181214011700401c4102602e952880402c0c000b103a0040c008905010509140300d0030a4011008865145245d054092559040c85621071900d0110b40344088280c145029035580c8082c0607101480241040b8548950724400180142e0840849003c0c240821800780846680007a00424242c8200050420b508460303109104c1d040020f062050500001c03215107000b10941721510002d01030007840d0391121031005200070814504540d032015528060b02041c811107000d0010080180901e0b4200701c04e004888090b1111a030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 831311214 1250 831309964 831309967
    0x207061d0d02041d0f07090b06120106082d0106030c0503060915191d011203050f1b100b1002010b0d061104030206030a0207051507050d0519060807150302 68
    0xc2194855140c030011071a81554006440d850741081c4545003a020800c4c0f1003c1d000b002d4104000343c10000380f4400b85c900d203c40401854810000300030396407250b000400500080400104605401090102e0b4896400c0102c45521100d507100301001206203112208031016450043c00745507414801da0011302d4582c21301ca461800d00000260301254000c3c05611402c0035580d154400da11849008001d28885410705140603484200902e8102c012040081c2190a45030000610801c01e501c0844c68580644400b0715120307c01180f010103a0100da9460040220ba10072503503014410840800c0c094030401c00080c01103c6c800410162140f1100d040c81113a0401140001d2565681d40d00c0303842c035500030b4000401c06540104443e1501541e48083c0d80b04002204000e00c0600743d400800c04a8822001d0b1548031001c64443c0c1031180c1c06807500000210207000b405640307500b0350300140e080742c64003801c1b415014800380c40e20265001078002010513088040100035102e41840340d8091400c0c07508055 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 831312464 1250 831311214 831311267
    0xd08010b0a0e0409050309190302042301090905010b0d030e010210060602191b180b0402030c030c0c010624030605030d0c120e13020316080403091211040c020706 71
    0x20041c00389154514410340d40c51029104210042080300c40b0858068102340c80d1a00004202850300f40e14401a0301035400e14100c11810f81035904496101c50744402e08014590070001d80b030000340f4208404440940d81c0e800051029510400f078070386843c1c403940c3d136080400b50040009080c00407020070348440d681080c2040c0201c41e000300d00f50b205030710348200a20700e0005034141030628002c003841c450390440380b140c804900ca02006406d04944c5541900500001d00c07028240422480700f01e4502410080c1440820307103442c541d00091210980c2c4900110f00300d600c5425040002700c0040036540380c60307004060b4510381c0b50140100c0d07000b408118003604400c00030a0010741480c1d20180014110815060100b17202401003924075140c03d005099084040701405828009510a4649904601030308a41c00c6000f4450041c0620542d45691754803803840c900740b9110030822a10078221074900b0003841d07e1203503450781d01c200c0071102c0c800d60007000010715188010301041e8071074802d140d000b070701c041ca030703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 831313714 1250 831312464 831312467
    0x140f0904030e060d11030708011a0c15130c180c1103030f07050d05010b310e07020a14060618040302150a06210201080a06030f140f0f0d08010b0a 64
    0x49040c01e00341c40090765040c00e100315200402c2d03664030a0208170310210902104603404083d203416908001004480e400001c84010401d000d20340509071603920940c00484503410a81803160440000742c0701c640c240c00c260303441856204154201d001009401649801a10a98011440741802c682000041c1c004110509502c80c0b00040c4403034401090100860707001d40c420b00403601d0710001403804001d2940c40300d5607291303141e1200c5003007008084025440f14002820003141c00305041c00307908089201c0d103885901410214014120030030340c002c0864a134041150343c002c0e0f85800035070764082c042c1482c1c40c104101020b0710f0a4500c0e0620003080c410040000d0300060308007482490440c40d05611f41c1d448411101400c003c1d0042e561495a5003450701c9081d10303400c00c0c0302d0424400d032681c411030341c0c03903200300070499650344009051040001c1d07442c0003181c1040d0381550319141c6581620f01c04c0f42c42c104a58500002c4e8804150340790310044c510300310380e54808a0503014041042c042440d18448500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 831314964 1250 831313714 831313727
    0x70f170903060604090812040503090a09020307121109040204170d030c1209020a050d050a050d08160e030307020603130b0a0b01170622060f08011b0f18140f090403 72
    0xf540c0615561100181400300076002c1c6c400b454511301e04194180380c04d01d4116140c3e000701ca2244e001d0500582c0c0403d0044450003524030503802640c4106141201c9800c200180a03201035485074003400700000102600e03180000c002401c2481001c90110002114130752810400101e42001c05280180083d080c55200a1682030f6518000c80400c2c81180c6000013520600c05a02084c1c0c04075641c0750030820010041849a201030003001030b603030a41c1405038107a1f040c0c00100c03500700c00d01c12003415403607030140914072044041502070201c4c2e060900d00d0b4007040c00c030307403095a585918041d1151448100f000b80f200c550741c072003031a5401b07111804d0400006044d0120300342d5007680c1030b84031380e0010741c003a00c0b000d03115981b2600100301440c02d51403220404008018178060009400582000420000c1c414012011b003a8a82d5042c2d080c90100d10310102c601d02c40f06d100206c20003039a138030703c00d54000c0310b82d40a1000c0e083c0b503109044d010101104000140500095190140c00f0440c100302c042a003180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 831316214 1250 831314964 831314971
    0x70c081614041803210507030f050604050f01050d03121d2e09060e010c050a020d02070e0a0213030c140901050d02030604030f0507020d0b07084206070f17090306 71
    0x11702e80075407203400701842a46640c4895800308685410204039840c0e61581040780c003240700710380c100201d4a500702844151007007282c6d0380c0c48620081c00100010705010500381c0041d4040e26051003400c4190000905580a8030014000c0300c243c05041c6a00b26001d20141181000f41401c0c049030166020584800e500c0714020100c2140ea5074207440300703000b05604145d020b10241c038000c00c00500c41c90750180403500712803280c200621503a44002e40b8203000144407010b4803060743c1e0240d02d035030f10704c1080000396004030981d0ba0303448a461000000101d81100d240040c048009100c0d414003456424010415016408a44500d81d00c054080140e02c0115508d42c0064052a0a51014091581c01c2c0c501d0311034240d00a402c0100e5600c1c0f1801c0c41500e0301c04600925240d80c3c1c1035140d88a90128541d042844049640741d5108607000260b980c010900360542c851110800c039031246400c100003a16500409019680c0020604602040100d00c4c40740d400000740440038907007010801d5010a40d19803004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 831317464 1250 831316214 831316217
    0xe011401053a0c0c02060d0f090f03090806070903031b03091a0903100c0203040e0709092d151a120106050a030b09011208070c081614041803 62
    0x74070b255402c101c500d42c58070070b4180000c2c0c0c035040840c40314960040c412448051920185400d81e1080981d200c1d40b03046184ea50000c0c4018203020a81140c0001014104a04440030359181150000501d404148000c1c0074081c0c0c0b02d04003041d1400d0700d4541000c800a203280700308091807030288001390b0012180313a62540c901e01c600c601e0852900d002c0d00c0c154030581003510600d03c1c510418a00c1c001c030400808400c0030682c19500c1110104504505030703500720100c0c40240c0c10a0005101081d50024200d50042e068074107440701c07586c0d41d4903000840304481140143d040756500402008424000c4000103095419410010310740d1300c0103010340051280c0202002c01c002e0081200303584404c4070903106412800e0300d10481c156507809c000f40a17a0b00c070580355804a030070000009d41c00d15058418504807640c003084207481082a40e110b80e681e900030f210880700c10001c0500851422010050781c401c0d08035103c1009859410a894448400014014503200c1c40c2006884100c2c0000b0500010308070307a15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 831318714 1250 831317464 831317467
    0x206040905070e1201060618050f060a02031e1b06070f050c030f0c03090a0f0f0614070c081b041a090415020c01020403030e12060403050f22030b010e01140105 70
    0x94100c03c684951a041001d5403092101d6696a030740c06040d1312041c00c8a00075100e10340300d5554080f4072503d0621910036954030440c81c503521011405c00200804003a81d241c41903e20b08642c0d0044d10150009030200360000c1000490076102a007941010488171007000742c0100b00c00e140800f0000c1c41882951046020090040390080c02000200107440c16005040021500c0f2098030741350564a400001159200749500703500051082c001d001e81c0c1d01030340c05011a0402c070f1410100103541c10988000c0403003038050100804800700303481003040400ba100300c1010304030019100307080000d41c005103a0f4491085291414601002c0350034450720040301400c2e90303480007680d9941003038111b85c4820100b0107441d43c00020000036044040d4020000d40e803080e02c030b48001980e65001d000c400400c0808541a5a0000012a002c240910040d04d4041c8548078500d190000442088181d52546000c02c3c2205041140c240208031044070f55030f024008505090350340758034146040d5a24a851100c0e45d051000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 831319964 1250 831318714 831318721
    0x30c0b030f150118150801050114041203050f13090c021b120a02031c020714030a170c070603060314010203100b211501031a030c010302033705090a0206040905 70
    0x1080c0296002201003031005100799517804140000784c0c40c2c036010340024500c41c0041031960150402541e04005d2000c20307802c04d410301c0d24548420005041c02e800b40a41131000002000180000304085141001041442c2d842c10380c0100540307141c44d4252081d5044407120f01c0e010803044202000c41e110031940c50820384948150181041d43c01900650940119401120b43c070180744403500076211a607084445180c1d442d188a02200d00321a14168560810b10000c004540d030414140c00501c04440e0040c90100c02d511810b00d00000c5034042004070b5100d4004106000300704d2640c030300f0404004029880d52400e140c0e13505201c01540111201c030b240214141e1030fa00c1d440500110300001484410b407450500c0b800c010700c401074610b10035000a00b8804618909142d00110403607101010340140000320b4524011342c0039420052040d05140107010b546448403042c048041809510311103044400302200f00f221086c1d850003001490558040350818006072140800c0b50121103d525001840d601c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 831321214 1250 831319964 831319967
    0x602011a220c090e092a03010e0106090e0601050619230406091809080417191a0f19050a0b090108070501030608070b030606070c120309030c0b030f1501 67
    0x6041490301c00e1185401d000410160f004200c03001901d110701210440c551364000b4040d507034207029002140203180543c1a00344070b528010540a60780c8010000302d000340240701041e00b100c0385070f031185da0b8503502c83c0e0100c0e4580f0401d1006038050f000917a046458404840110b02041d000c8000180411002083d9458011810109400300d0240d445113207680e15562100103240702c00e0740c000c1400740342004440e606200c00a1040c0c1500b5584114444e050a241c540c0c08124440c0d0102152100d0241d1034461007900e810200c543c0e5107034850f00301c00000b8011802e100e03e42e1031008052080100200c801d028241d44c06401000e80c00c0340190021440760758110102003c0c10500f05c290780c001020000101e482c800114241040e14402c1c0e070200f054942d00e049850765140740d885100c45100040001c103d007410300000404139240541c041d08000c0740d030b542804000700317500c410642c00030708564001d1080061a4109400801d0010030720350950600300c0c4040f414000c01790000c81005480f2800b0b44603079 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 831322464 1250 831321214 831321259
    0x609080a120e3f0d0f14090301022101061b0209061f092c340207030317220c05030f1506030f120d0609110d060602011a 53
    0x303414480c90b00c06000060125109900f02d500800301103c007038907060440c80b1100162400f0380004569428044424090050301c2e031300c1c002407030180810300420201c051520240018404030740e566180d21034210600f18030400c1004103802c01ca01700509000d070301c5080f608205180d0f90090701140c844043c0d4507460f0000f043c0c000c0ea02034048202c0070700c40c0c02240d5550860b01401c100c840400e84c6c903100e1006981c04d00c40100341d040c1c1900c01000d0150105528081090414400e02c460322002e0701041e400c44030270041410203125200050f40050030134400c06a0082d1008003106d01110074000354140038004598450100000341c2c0510064404c01e82400805074003100144401f6080d40d00d409039174000551940000c3d0040e108611942c004030b0454100040d941401b40c001c60003030003480809101e483c0d42c03a072204204841c0e0985a0700c011803c5902d40c07007070340d00d0341c0c410344100c0399074a4035445c0310f006450300c9500c2403003907900d42103418026140082000c815030300e04859500306d10070386a905250785e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 831323714 1250 831322464 831322489
    0x90e0309180a111903050402030a020414010611010c0909020901020a060507120501150c02130b0414090d14030a020a090801060306021e0a0c031d03060405070609080a120e 75
    0x201c0c425003024003000a14402503070240050340c4092088400304030306450940300e1070075886030901600d882d8051451103948001d400500c0201610f442e407100350006001e448012280200d004a8840100866a0414400c480e40c0714810024080300c030300910085d000c3c507114802c0010080d000510700035140c2c4240814212117038064020086410300300801002c580d11504030003000c80c6028004140320140d844e80701403007020399a032200034040503424800c0328206010204001501c2d45008c1740540d03203038061408441e2420040e41814500055110301d800c28240764403081c0201000000c05801d140c0d02201c1d400340a201000d43d5904208100300c4d030075070891b40608160b529101d0301204000240e0014801f10742003008066145882103d0900340341b00c0c5088010105505041640000e070140ca09142c03404a000e0034810140603641c0403030f081031412a0122032940000d5020312420f9040003030a00034181c004010b114a407000d6880c41d44102c003940d141c1c400e00c6600d46c030501c1190381d194000141c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 831324964 1250 831323714 831323719
    0x912030d0501030503031803090f0114040308180f040b010e010509120601090917040e01030303150504050f0a0c1103030606070c0b0a0e0a050d0317100b071b1707090e0309 75
    0x420742e03413400e00c55101d80045d600b0700c0b0454024001e10140010000c19102030910017090101c01c05c21801c015a4410911010461010070a22002011666080c007424645103003103078a94130064000c0030841000e4006140500c961b2401541424a0768485d1250101c11020308020f83c0d034025540000c1c03450310b228030000466200b1030001192115141c0c000d03908cc24480c201103903c8001300e501c07583c018001d902070280714404690041000c46d1103034201d004500c000c05141c0d1400790b1604e02150079075030115800fa101e0324070042400825400c920808240c0301072443d090310400412500140c07a48030282c0a91300c1a00c0100f58442801180a6228002c3c03000040107503840707401000140c001b100d16407a40744201c3e05d04d9400141c6013040c14801c003189526560380802d0344510301505052302c2000d070a95030440c240300b20100308000000e009004160090801314640b02908081c0b640201294000f50000c2001070b1290020038000642c9006480102c078001c62660fa20090051960240213001036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 831326214 1250 831324964 831324971
    0x190c060e03040f0302030f011b1b0b04060b010809010506030d120e0d17161e020c030d05091e0f011101230103030e040603030518061b0309030f120912030d 68
    0x5010b0030040c003c82c102c0744240c0c140e900c8007501781c0c492401c0781e18200c550301214428100b07552656219501070443d40c00c1803504501d1400058076081d00c0150211001c842c8241d8031451180c1a61b04808441e500c00200390080c040e602e0800c0c082070310742e030480e22040c1c1171001d40d114030580c11195800507a40e4207800400c1b41c0340c50503a854000d02c000304050415485285400c04603421104d404110312950381c09440d843c404140401c6040346c03c8540404542c214003c41c0001002c6039024481c0759200c2c0110780e29540c84844203410040858100401100b260344000094a0ba80d180c400307800310000001d0819440840d03506400e180074050a0810744000f543c1c000c0c2c00841c20b08446807050503079000360307101808603070040b06100c22a001400080d0114409100540915801a0082d242c090001d050f803401d01051010045041c601b10910900700e070030200c2c0c0c511890404012070950303141928000c001d070712048000980584215070199004030415801000d184008104681220145c0a403c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 831327464 1250 831326214 831326219
    0x6040b0d05190209010f140c01050f010f05060c19050f030403150f141f090f09050d0219110d0b0a0e06070e0901140f121c0302190c060e0304 62
    0x1840180011a180070024000e18a21015001540f00703580b10310406840e80600003819a5094034420340401c1525075007101001046c40c059000c0c028940180c10180702d0780840d50400400840855058001d10b004d0705040c049107240000000304101b6822044100300280031843c1886414400c80400382c05080c072001400001304590030301452503800c00030808000d041c0740840318109840008034242d101c0d2001b03801294442c078441d4002e0001c181c00c40691038000d955540148155050f00800c4162540e80d140000207100c01031190b42c004c0d00c000d1001c1c01ca1440c008005650007000070601418290355410030380c0c2c03207440d50400101207a0704400c3c80d080501d071086490000e0035995144800fa4080d200201d02c5040c01141d802444443c01001120f15a08161030a14000035102d8003a40c0310550807404141502c13070b04100a41c00352510040c2c6903809003008000311403509501130208145c03040080c00300080c0d010300940c9901340c0500c1c1603007082c03690b82001c074058142482043c0040c007002600 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 831328714 1250 831327464 831327487
    0x90a15090e0c2b0209100804061b0c080c033a0e0c01110a020603070503010e01050114090d060f0e0c0123070f15020403030f110a2006040b 61
    0x950210303003103580c4160032540e459035041c08500030350310300b205078404414041003c1c2d545580c0300104401450001130402d80e00c04000f49102e03030020a40800300f00c81105000078002c0c903025607110b4075203900c0051030700240d089004001c003202c000050030605011800d810540800d008540c1710040d0307034032040400f900101e070b540280040281d50030a6400f00404d54580c3c0c0d50309004d142400da4a41d40600070000e4180010b40301c44c00c410358241e040b400350300c14001c0103030744100185001d071515587c0c103a141d60418911041450301a0810340c14000950b40c10030a035441c202c211402c80b0402d54a0080301c0f041860264080d142c0090b0110700c50b81803064408200d02c00040740c00903540d007640d4484452001404510088212051076007858504001030004280c042801c1c04580344140600c2d00e50096081920003280c00580040b00000c9074148900f510a52048840424078100310107000c03d480c0035640c0c031007202c0000c1c0380301c5415070f01c6140141e0300703944040640d0001d1a45880321507540b00034404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 831329964 1250 831328714 831328727
    0x50d0e010c050405270a0b03010209030307050123040507030204090503121f2702070201020f01050a02070c06080609180c120703020415030804050d020f030a0b18011e02090a15 77
    0xb1140a100f50721045c03280d60b015088901c2c605104160002250b0711180441c20203403081101158242d07408110703107001c1e07440130030040070004d010b6000014030808621851100d00c0d9400d18407000e505510b0148000f00f8008103000080301c0d07048a0009001441d850914294040c0c4051842034401140400c41b0f484980103940c10410560180400a42e0300c84610700ec0c55400380c4034000c0d4042c404540801008078581c0140110b50050040340c0120f107881c000706081d00d808032a4585c600303070040307110020842500c0850010300200d0400541d1840c1c050003290110070b008028403c15140c3ea1440007071484203000d030051079000944094503007410419816610001840220300640c070340b00c0c0c01c006000ba0031000109a9622071b0070301d0301c2c052512042010580c00707904c0999014032065505003580e6002c203c2815128812404644103280c101d80d4140c2000d00700504103c3c0341d050003900d02091404030f05003c071403410088016140c01c2190042141c450783d942021640c40000e80003800c110350010f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 831331214 1250 831329964 831329969
    0x11802091602100207030306150504031703060f2817120708070b0702010b04091a07050901200f01050117060a0218090402042711090610050d0e010c0504 67
    0x11100e004a840300c0060070200120400c0000042e0480c0001d00c100310b01c25001005040c0c0640f4001c281c480e1601c146240440390030311850085100001e0800404c1039481300300c18104a0807600038114500000800c03044500c1c2e4420510038000c0c06500e5409600c401c54002e4840350b10742c4071003003142c4c0720000c009a990100988004501c81c10103061120709081c8201ca0030f03140d0080715079007081030039510102c0400c0c002d49110301355520741c64104402e8640340308058003035000300000d624001c0c0c416040e01c083e0030007070480340c200107040080c13800c80e0741c000070061545c1e100702038040c8007010703001052420703c203052045a5080d42403400000c2c1c600400c02d03004401e0b04901781984d400b91120801c02c2c080303208401903421b035040b002c13581c409145880d44085d640180094008103038049119010480d45580c01481400306122000000078000300311205081e00405440605c0c09041c40000649880d034460301c8001088000540d085410344690024012084242c00910821200d50400b030b10395007050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 831332464 1250 831331214 831331219
    0x30d09031707050703050c030c0118020118060503130203070506070807290a0c020316030827070504110c070f2c01060f0504030f15050907060503160c05011802 70
    0x110145900e6040c0d400300ca4000c29140c0c030f50b649000c3d000e580a4a89801c21303000802c250005008039942c4010a001d021071107031001e4192030548540340b001500002651040e03004040c00c0c00014070000d5000001c6a03001294900542c403440024030002e4501a250f0b0001c503001900403513280100000c0b038016100c030034030420040070b03248004611000501d07250688007410810900c04905071f0000d42c1c1c414004d0680a00c1500d141c9040c00b08074044a142e011811000200742d1802c200318501c8180e40502001203000100e600030303c0840c4010f50b07504090140902c202c0d0b13180d014441c45c4d85054101c1c0c5110a1800540f01c0707080d6510013950703030040184a00b01180c100980300030304010994401405540d000c010450959007044402ca0b1041c10301c40c0d860041c0b000400000c8082058011450100e41c0b0903c0c4e013100524041c007050081c0d4030068030884d1650b001c10b10900c0603a8011064990200303094040301801a082002103a10285c3c000c4043c10551900a4004000100e591000c103003c1c003e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 831333714 1250 831332464 831332477
    0xd06020904051e0408070f0b070906140c0703120c02130501180902090f0601140414030d110a030804060b090106051206060405010f0806030a0812010311090c070807060905030d0903 79
    0x100c0c2c03400442400082803c401042c800d4001030000b8030100041c0070903e000310400031264003e03990342c1610400958101c3c0104203800c0d4101304a40d480185900704014009000741446419441c10380e90b2102404020808241c08202c00b410030310070f071520351420390018059000c0840b04220302c001045c081c09000baa03520904000450403002d4002c80c00f800d580600741c4052503841100031a4001f40107401c040c1000700707a82c00e208000040001410241100c5c98000000c01c080004240c03820f240d980b6000d0a0101c0010510300c415804900c11544507003508080442c0c0d83d961801c00018100f0a8056500c45441000460410b40c42030281c00040e144ca4101c840079101c0108004041c05280708290015030900042480355128040c407642202c2c01504641c10800f1958810700349230005c0540012118821004006010410942400c00d82054070440103500704820710748403034031404401400800c0c00007440020844182d1256004640000030f903602d4000035022040508007003002a00003542 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 831334964 1250 831333714 831333721
    0x91504061b081606060b03090f060919080a0309050109060204050415050907030c03090614160309111005090405041101090801060b0d09140d170a0506010905010e0f0d0602090405 78
    0x502401da80a49030800300c40390400314900c2c0c6014030400d000d2030440c0c40e20b486600001d4000c3c0b41c00d02450054250340e010388941118450361514003040141000444d5018201c0404600c920303101d03045c83d0a0704415001c1d61045c040d48160050105400c000f4180d6207400c00d210140103499000e402650022501400391000c0090040a083c4190140603400f10180c404035028901a5201407100f8802d410081084c0c43d542e00c078181203800c0010420114141d2100b00b10f66840d101c200040d051110741000c100c42c0301c02d07440d0f00b91005038441059000e03081102d441d18205000708241c0d400414000c0061055140c1841d02035520780f0414851800f0441e4907801046904041c084e680a80350399217181c9040c100300404d600c0145c800d05000340c65218035064a14a801d41c240441c644000c020384500d09032004646e5083c40c04031f0000d001078a00c038900801d00c21642c0e48102e07154125142468903004000c904400a8019849007046662000304520a2000c205040d000b500b11044104d50400c05030360b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 831336214 1250 831334964 831334997
    0xa0f05060f1909020c0604050118050a11130c0e090705040b120c070c06030c081e040210030f0f0e100b0105070314040e0408090a050f030307030c0809150406 69
    0x11000d4032415032202818401c1c6001d07081814400242c0d240c2c1d1941094400d640d030042e9400c82e40aa07410340800e03001a01000207100c424040c21480c46803881c6510401c800030b881d001e4403980d806c1401400b4a071282c031400350381e039109111403105a0341c0402c10003503140110710281c0504034034003c5a010f01100d400060301c8138081c80507102110b90200b1594502107204c02c03040003440e0002c220401e52481444a900803036003030307a0380c500a800300e5100005c903854070300300180506a00400c814000324541c1d48400304040070102c0c10b60803503810390b000100519002e80a801504024407190222480e1900500b0b00d078550360043c00c111aa09815684d0184030f07951850700760381070742e101d250204c0c0e0108000710000741708001d0300c80304200100341d80341080e03103551440b4018003040d03030295511100440c0030040d45c0303400320160004010496901e10040480f0011a840c0c1c024004041e091081100e80c0806200751a001c6031031900f0018840b0154100d02c80e69400190030074010400040c81480c40c0c0490719 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 831337464 1250 831336214 831336221
    0x201050f0118110f221212050a0201110c0c0a080304060915050705030a2a120e0102010603050601240518060706230115050414040525080a0f 62
    0x841039101d4040d9841a201ca038840a000c900f8001d00200c58200b2400540c0707040c0b50040c240c404203c3d248054409041103450308100000c0e0496160341c0b00c403125a200103200b40c1c03c002d0540841d41801c580710455040c007a0300404000c0030f100c4481100103000c40c00c2c07000c08106103034480000c6031410300460715058256500d010314040d040101d110b404041c0725000b69041d1030403d4950f0f5280c50351404101e580c0e41401c5800035002900462145040300c10302580c45101d0203a4048080c190b502c0b60030490311042340c041ca0100340d40040c441d9801458466901c02e40280c1c001c0e5422401326003c41d40d43c0c03406860b8550303401b542140b02520441145a40d280714208644a980c4842e510b80714190080d8104406a44a42401c9a86a60352850351410440340c0300440c40481c01a01100503940c980a992642c0c40c1d43c2840401c10000b0802c024003002c0c0542645c411510b01c20f1343c0000e8556903600c60340944c9084603a941008a42e07840a50403403c2c5c0c0001e0540c8605009481440b810400c3c00001c4180c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 831338714 1250 831337464 831337469
    0xe032502091f0314070e0723090d020406080f0d17010b161a041101050a1202071718031b030606040507120603082113150605060a0f0201050f01 63
    0x10809020035000341c0c0e06007000d15100940c01a405215030f42e5698091102e20f030b043c490351103410400f4100409038130500754581c0700b9120b0500c0c003885107440080c0040340c1150050046012000308040005480d40303e02c016049601500401002c2d403200100d680d00c071a5030358480e01912802c1400b05c1c981d8401c000003070300020707941e00701c1809908000180d0704a401481d16101484444100400441c10022003007004e210f42014003a6582402e00300503080c007650701c0305581440300800017509543d03405007941c034000000080060303d40b8494500400451074500a83d100e4040c003160342d1010310b024114144140e03208504543c0f14070390320203890011076680101c03258180c1169000415604090b044141c1c032680d90300e4003c3d101c400706a4036100b11202504150380340040450307010300920100c03a1941c034400c8021100d003207914104036400e400f402609c00061100d001100e241ca240111900010007900c1c000300340d00d8030b60601180040040007100711020041d802c10021841d41c1e5680b45805c2d05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 831339964 1250 831338714 831338719
    0x1b0b090901060e060f031503070f0f090b1c032d08010506090f0a06090303261b07060903030f0b040b0310020a0215010308070302060a05190b0f040e032502 68
    0x51a072a11406880100f401070140d900f00c1001c001d03150a48030844011442299500145900c03107102d8000d041c502106604096410301c807504040c0000c92040b042c01c400c0302c45040b801301342032008070045001c071109404002403c0c4c120826450405410240ca031001402010846c009540b030707a074a80c00c88404080f000e81c04286040018046800c0c51001080e035004c014000b030381200510000f0410800440e8400000102551014020158000d001a568105205907482140c0ca174001035521204080d0519545298200214282c861590b0580f0007850f044802013000310b4950a000c0c01500a4010039071041b80361590f43da4240c90710388a00101c24001030020420780c1c1175000071000079845010300300c007540b1540e0340c2c81c2c05010340240c040340079620030703582c0c0340d2074600038a8046c2c901075002e0301e58040d96040008100d904601860300703512500201d080802d00c0115400030a04c0c04850400302e80c3c010742030034401406000b000008001d201c100c000e4000c509080d01c000c0fa13a2074a1640760003907 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 831341214 1250 831339964 831339979
    0x1e280e1c02010c0f0f2304090e0604230f01050709090b0303030405070302130b0409140d140f030423011407050901050301030213060e0a09050d1e030e0106121b0b09 72
    0x102144515100c0c0002c00c0702d402d040740e46800c0041e140000a400078141c41440c0e00009040c000518103009030002c41a27101c005041d80d0906036034400603034902845480d0000e00c0450041c40490b030800000c9040c0034504020031560404800040000409010700c816890520079800164100001144d00c11908600503100d03403400d56081005c1440c0c51161002c10b80e48441500100340c5d22231103140c4407103126801c1000081c10103816142002825805c0c0700600501030503c1c8051414070046402c1007a031074403050ba43e43c0d9107182c2014804d400205800e0960501088801e4620055210a001a0000002ca249903071000000c498074894600c035203000400601c01000181481012810040d00c050004176105403500348004ca910350403070f58109480c1d200c544007018001d0600142c06400054600042020625001d9040754510520140c04040d55070002440e010400e522080283c00040031004281c0d5480c05c01a81000140001450903001d4050006094024200700c0311016009010700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 831342464 1250 831341214 831341237
    0x206180d03090302010204090c0503040c050a0303080f130c031b1a090d050708060c1e030106171506030a09060605040b03120717040f0801051e280e1c02010c 69
    0x4501500d00d010b021000c1d59024000030035014694000e0745043c001568030381d6100d280c00c1c1498003010903035a0045005079401882480801c1c1c0c0508a01d0703008003c4002d10b0441d4590030580c42005880c91009800d96102d0710380401001708a83c20030140b0302d0381c0040c0b0340e0b006c2e4031120034195140802c076900c550344204000042c107070300704071140100303440c001c209440984e070392048000c4c00d110044441580361280040c501d0203000100d03502080c02c000203401c05055605140001e401190703480d0b1403a80c6540140c000a0007001c400314070091950003d00140e03140c0c280110341002130300400d407040b40d5040c1000c20119031414584180407090800500808020340c41541c004125409484155980c0c3c100488944010a840c8010b100610210749a19034040c90701c2c07021401c40e00c01800103d0328031025807011403204107102c030507504188d580100e4030003d669201c0b8004062281084205624140307190300700842c002040d2100002048284001071013240c000c200d08840c005000c05010074489000c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 831343714 1250 831342464 831342467
    0x1b050a050f01110708060106020f0601080d2a152708030405030424080f040b1807050d0f02010e0d172a0c0a0f0b040b03070225060206180d 61
    0xd4a0801041c10458908081d0f0a40380307042520340e4104200c0c0d81d20030f5004000140c1d0401a070003000303942d0800b504207035043c81100d54540c51420404420000c20a5903501c9066018450301d442c0711035900d03034281048140c0381c130141c0100c02a413101e41542c9000d1265100210002d22500d0500f42c48003422880000c03642ea840041d0030140056a0b030344028030022504c10000c00200d040040810700f000800c1d03540e140d0081c0ba00d500101000700107100c2c241408005030040d000690084a00c0700c4030840d6240c0c02020b245800314a52040303034043d06100d0003c0078401141034452115000b07a98888041080005101d50340458080040002030340001400c2c20441c0c540c05007406502c40840e91018044c1100c07010842d04900c14201d4a035004503ea0750450f1500030703d03a0005080604100e0901071900030003001c18003651194000c0d50100000090400740b0030320001541d4004000d000003010305d0140100410310729409010007504c22107010030b080c406000d0300b0180500081c0300804100406940 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 831344964 1250 831343714 831343729
    0x120c020a021009121a152d030d030912110d030e070b07150b0a050a0b030c070803161d10030911060319050c122a040e01031b050a05 58
    0xd0b820304000500e0300c00314000881c02c9801980c18007070040320f80c44840e80e111114907072801805842c0025146a1000f0b02a1160340c0015284280c001654a1030075141c180d5036184001000600d5060040c440e1b28003071a501a4003c201e218002d24412075547c100a10070388295403055005a00e5901400100c001e59100e178000720090703120441a11a45682c80104000e0768000c101d00b2540030204c4002d42d000309025208003a00150101d60010903030f80b40c43d020803043c075464001c49640c0e017000000112488200d0040f00d0003540d0203008075a4a2601001244101aa00c06010b00180801a140a414481840004c0031500050031006030740c540c0340c401e5000b420103500403684811106008203d665a03507000e548165074516002600400301036465040f10002080c11a01d42824041c0c1c001150310780402a501c421600c800c1c000352038908803010035405070780055110034400040e002c82c00c3c4a600410340d040700c1c42284440c004104080120009000038010300750007482ea0202000035103003620 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 831346214 1250 831344964 831344989
    0x3020603061c05120c060a0c0503060409060225020a1e05040507020a0f1b0b07211103070317060603130b1e0a0606023d1d0607120c020a02 61
    0x125000d941484540d9104d0826004808980000c08085480462407106210b4144d210003881c408100300b900e0310002500500001e020940581d17524a4003004104540d8111514202801c1050490b804c0564480403035071030556040f8002c00d00c0c1c0000103080802e0f60a1040c03500c000e6505614140e0402050100510b00180340c2c4d0214030801b0111008180e40725528005035018020196007289040d0900d81030950710741c840c1030403d0040042501007100704e00c075580c09a2000941030a15031000c0400c4403035980c0d07034803a45402d01000034948100f6030070005800c070402c03088540c00219a81c150401c43c080c003044404109000707480d0103110000b10403000d525404480d8903407040d8003c1e1303e01041d0202d04401c80c4c4805030310782d80d01010700000b9010040b0000d99160787c0040f007140010b1030030404000e12a0a4003000c0c1c040f81003184040d086807900403c0080c2c0300c5101c240900300b81021250f55441c01510410040f51140204041c4c008040c01608600325070354005000782c1c0050781c01d110132401c410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 831347464 1250 831346214 831346249
    0x810060302091813020a1a0d0504030e0a08100537020d020d15090b100c030509060f030610020f030a1808010501030c0611031305060c011d010c021002040302060306 72
    0xf0074216081042d8014041e000c18080351000d40c6603881401003200303194201d2000c0c1c0340c40120080c2c4180e8041d080340d8030180052800724283e00c42d4581901c000c0c00306147ea65020184c01c2c0046004400041c6001011076490700620041d02d50184028441440640303a503c0700c0f40e5a0450010300a40e295000551100070070010b1030201c800c0c1e505c108076008035110000041e10b0398032a040e1400d03c0054200682885001001104440e0300040c3c0100d8096605a00f44030700c0304404c00906009105488040d10041d0070565030307195940d620300b260360007220101e101c0e041d5032840b40001440000c9003000303211400011b6251080800b02525800b0701e2002500c0d01c840c0d01d00c0c0104c0c000d20207008541c02148030b001c40440490805401030705045103403e171040607a1040c41140030742ca00128484040380d000ba5400395994040d4410940588100f48066682c003a040041342d600d1901540300080e00901603081da40111060100102644182d200c065405003091001c40d0b03442c9003178858030352140303445c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 831348714 1250 831347464 831347479
    0x1106031e010807030201080a0612170403151d060603030f130504020d02071a0c0d050402040e01090b010f05060304050c0108070c200a0e09070b1b0a050c010f081006030209 75
    0x40090028040c0c209070442060341c0c006090803c11960821002d540205000c80c09014250400c10b00d80009080b0303032006400d03185026003610f81084104111405150020700764031b4020128001403015080850622100035200c0c0e021411080001c0340310385c050740e4020003841c43c0016003142d4140d940c0215064110030b00f44014000390703503581d80c8018071070340d003940c5000750f252000c60404c142c00c8040c4015400b8440300d890108840341400204450354108480000038040d1100c0c008580113050020040da0f0079841c2200030014001160a064100c038094046010096242d5060112601090b40c00518551124092060303640c014041c50b0f030302a0007880c0c41d070200c614503265070960b2040441000541078501c0880d00d80e50a0000720741e0054244202d040d2041d051003116580d032441030f84550180048089080d96410071004000000003044000b00ea48007020703810084d0300c45140e517403241d000c00c442c40198040030f0301405086201b003214104180040740b4011040d4040e41c45a0201b907440042e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 831349964 1250 831348714 831348751
    0x1b050c0c06040f031112030702100512310b010312050909070801090c0306030203030703030506011e020f06090c01080f0a140a050711032b0b0306011212030504110603 73
    0x840c0e8002c1c00003808461900c1c1403091650030030300709100382140801e000303190410715420103107000002c68010380d6058031150701004800008885c1400340e2507650444c000f04100717008081042c0e44a011114011150b6021541c4500d142d01c180103200140003008540b1000040001c01c0e001e001410079000141000c1c2d140c169070200040030401d0444035040030030403400052100702d0041c0309840741c040013410304004290950300065982d0089490060425031035100041d000c2e4800c0b241d1045550048101d4600070a901c0c00c06500d03050350345070391820b078824540004c1c044080010801e05045040e120405603032980c400c060500c0d1001800c040d800c0f40c40d806510b0f40056541c202501c90f403090040040c0d0350516205c01082550030440a87e02c981c01841000c3c408440008890f0311782d140c0300750360800001402000c034050518065415454010032000085801180e002e06950300d00c5115a03881003031507560140c00702c0b1015140540207620003007e840d407504100009541081c01d58140c14400031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 831351214 1250 831349964 831349969
    0x601051e0c0304150903060506030c01090b0c012004180510062a060b0126070e03010b030304091e06030308060609120a14010608031806071b1214011b050c0c 69
    0xf5074034100c0c03d0001703812080030414030035684111500400c0480c06420801c2d0140002401807c0c140030307030f2407840d000091460001d48258003c030300301d680710309101406e0001c140c0189400c0e00148035803035140c2d04004120708000749512071039100d46082c81c5c00d88441c031709184040b61040000901c44502800380c0c0054050f200010781c00d000d00d903203d00b00c0440c0070307031a940c00184101038202c80c1c07001c600c10030703444081103072280004160300140030b1501801030801c1000090141c03814645080e0140000078000c9000b42613600443d036442c01b01d07447c0300c07425440d0910044c22a9224400500020031183c0403903010300c0c0210013001d00302d00082c8860110300b1020501c0d424000c0901c421100035116201003031064400380502d200405402005c3c5040a25548445440302080e03da000d1040800184400030030007018070300c5c060b2180c001c010340e01007900d80d039425600e0300b2400c0c0c0c1900c440d0b0003c4940b05160383c0c140124200452a201100c0d40c0058000040d54a41c00078080f9030b6845c0101201c044194 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 831352464 1250 831351214 831351239
    0xc020f0322090e0d0e030f151504090b072a020906010c05062404020703020a020f0303120903030423191514150d0b0c07030528080601051e0c0304 64
    0x140410f0020700041402107201910b82000038401c1c6000307400407041e01d030321000b01045140007a0a44004800542d5a220b80206419901004a07038014588580c0400340b228243d20980324880d82e846280036181d042c00e80343c19110a0366403194000c405180d4200060820b04c0b4083c0d0055410f05000c0038004890340c1d00d81c10220b00f120455904c034a500a40400b151070044010414803007920308520301a00c41c1c40080d211554140c1c040d006060142441429032000c208035102e84500e031040010905042a0081e100c2e8800c1c0c0c0d003954122410705040f40e40c803000d294100010b50000004013401480c0075208643c4110040069603141f5860880b030440000c1d900490a5083c0590050009860111420401c41802002a50140413400d81c841e0020f034440034030700e41119080c41144e441d440c8510b4211014070486030074070304610f540e02907445c3c03510345800380300c414100355120f4401070f0742c40307400446890095404401820391074110500c904c89074900240100b00010f4250303860291500e140300d180c17 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 831353714 1250 831352464 831352481
    0x1f060e010807260328270504020c160e09250e281409010e03030f040f1b05090a0e19172b0209030a14010e07090f0c020f032209 56
    0x3080a180001d00721943e22503012882c0d500b20780c2a180f5070510320b40c42d4540440c031b0346c05064003a40d400074001091031001c01600300f58600c071000c0070403201d84510b0081d03454030042d64061181d100d084668030b01038021a200c0c0700240c82c0b149a051105140484094072900c000c1c0030340e6032100d000e03450b840d60307040d10341d00e451490426100046624001e03040b2100100d0700052051059901d480958070004030080100c0b504100c0c07031210341c40513899604240300f10341120300f4020310020f03040b00d54910000d81042000101c54040303e0350030341c41ea00c0341c1c110003e9410841c4800055041441c00d00c241d030040c00c0d031090946028102c080203604560032040308580c8442201425aa500030381341620100c4800301410b00400000d06500700460407022940e07a00003080e004100411624144060183c254840300c4181d915404480c80349995001141c018080b240466140500304421480010700003c0d41000e19010f5500461906d07410304c0e407036420b444035503c40a9204029540c00100303a04a400b54062 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 831354964 1250 831353714 831353767
    0x109060209010f031107030e19080105180309010e06030a09080f031803040303020c0f0414070f0e010921030e0306040c080c04060303050d0e1f060e0108072603 70
    0x2940c081c000005400b06000902c8001018107010120150b102e0711030503039184503414140701c180032200070300142040c04c14442210320202032031f01c001040101508120300170a02100e85180034004e519032987c984c42503070709080c040b603d82c1d00302d00014108480156400102444000b91503a4140d0b100d191540c003018500358500008818406401c801811101c0e540100100039850145942d5000c1e4842c0c01d118003013885404401c50400c2c041d200d0b0b0304001601c07000700200c030b1210b10b001e15000d070028040400c030800049480700602425401109410181d44403000e4081c6105d0504150040301c08030001e08800f00300c2c544184e05041d48003005490301175841a0302031a149814441028900120324042a2049040c44070400102c0d4004007192485041c20002003051600203000c186030194412203555841c10992000000811a81c400419501e2076201c44c0d1059a03200d0015a4840c0d260003080400141785503228a0120351306171805010303034207070252410002080c0c03408400c011030007580039 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 831356214 1250 831354964 831354967
    0xe011e0309120801062a02040c080a1505150c100c020a05060f010608041209180b0906040203040b0c0c2b0f08270c060d0209120109110409030e0301090602 68
    0x104010091042c840c00328140e2030300110325031400800510007a1610310101a0b01c2c0d0001c0c0001810850070000f80032075401a0041c060507401060041c40f07001c080b60800c606524210401110074000304641040302c030010848002074410300041c2f502603000c10b10400c030b00c0c8a540302c400020781c2580a414211609600039043c850f4050078010b0a0043c003c000c403004001e04801440003903040441e080e005500240039954040a4180940d440341154000d041c000702c0250703426400c49a1900070400070001502c1501c101d0b104d10051200343d000a49008000382c040100040c40310340f803000a070002c0403d50b422036036400c4028224000c030a07051483c01000c40d20017424044c0b1643c2200c4108140340d01480c00c00041c0c6051044810110348443d541e903c03540700310454a03080402084545150003000340555540c0790582c0c6014000e6004c040c5c0180100040c0f06070b1402080103214070700350703660006082440e180d07942e01000002c2c00741306030840910400703400c040c1c01da4409209a0420b2489554010b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 831357464 1250 831356214 831356231
    0x209060424081e03160f031718010e0c0d020411270901381e040510090308040e06130e060a1805030f0c07081f0617030a0e011e03 57
    0x46051005010310480c0d50384c0300b00301c620501d041c0c00c1400741c1c00c5500980c03e03880b6500e00c0c0c54200c90201201818440c0c2c40b84010500c00c003100394030209290701950000800c9065100001140c0b5003501c08050350340101800e0094001d4100707900861900003080d008145418408070000a500c1c0024041070940300390100030507014100101c0041c0500490742180041aa90f00c80078075800c201c2120702001c403040d1030307442c80004805000ba10302180600c1e69040e4402621783d804002d80d00f0034800c0f0784c425000e55108000d854010314a0f803003605c0d00300311117519050a01580f04464000901402c0c0c0000c04503404002c4000548642e150340b400c0c05015002e40d0510802c00c10641d01b10442480000303140f44849400140000704649400001d506010345507500041124104a00e03907000f044240199020002c1c801e00640105502c0001c2440c10030003c5d454507441c03492010180b41c580b0343e5901c10841115010b020b41007850f4910014500314079a0141216003942e1580401402008070351904501c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 831358714 1250 831357464 831357493
    0x509100f0b070503070230160f0e070f050415030902100203031306050405010e0303010b031006030c0903020f0310020d0603030806030d022a190501030513020906042408 74
    0x3004000c02036024040e0820041c0e0321401e0f101e22440000900c521001d1100b0003401e80c0380d180f0020f42c0d40c04403030800c222649040445858000ea170100401e0f902e556580898455400b00700d401c127070b40e4004482512642d809c0019207101203504041018484184000141c911a0900c26260f510140e503001c07607c01c109105008000b00c61a01e484155003041c400c00a800381a80b40706d601681d04030030041010748075420000d00400e42201c8002c401d002c000004250421008000c0d40141400480e0309049580c030750342201240d40343c0401f140041c0c4c40394410400340c50103004403801204001d0517201c0040c4802c00002c100d9008050158a040d00c5070020018150021503d0b1761000d01a00542a140f1020600a407514081044110710004602150200400070303a220a4040000b42c040410030305010b800c1180240366100302400a4200310024179030140524800412507400381680c40640c45000800014010b21003894044403001c050f5000a0714034000c18000030f182417005442c065410011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 831359964 1250 831358714 831358739
    0x524030a020d150605161e080c070905010f050d030e0406260a021f1407150605060901020607030209010c0503070c09051008070b18032b1107090504030504050910 71
    0x100c48002d4a1101401c02c29030b60050f08564011800c19030070a18442285014280903c01f0104407062810350480e02c01000b0003140142080d808090461300c103a039454011406803802401100c8410b28007650030856030a2084005d14094801c0c1071240988a940e404034003110429030002c54000740c00c684490003600c81415402d0f62034169070140c2400282900410506401318003105150f1803074201c1c2c4252944280010402a42c01f68800c0d5543d081070f040c4281200680e448907501207152260000382071601c0b0048640010040e00a00000d95540c44164000e41080ca4800d05200d10440c4c42130000703400384001c041c02031140680c00b0343c8604083d41d0070101c81c0011300119441d00ca403002070045078000601c0c0c0c01200c0360101c44d0342d5110135004a00f0015500050300c0e0750188200c4a55984805003030003c7c2d1142e46190700365150228000d40115a040301031803051030f884d004031606015145040c1c02240e407003030003820700c0c501c3c2036540c4010594a010072584420701184250050041011801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 831361214 1250 831359964 831359981
    0x1e010801090b0f0d020f06180301060f0e04030e0a170a140f070e1306182a03030e030f031201140a0b090103020304111c110a08070524030a020d 63
    0x7201045500d8401000c50040c02c0554580c5124802103a19042190b8846012260030b030405004c060700e13140c05a08030004441c2000c0414861750070640c1c08180105140c1200085541c924003100705a01c42d0303102030310b00001240d03507280c00c1708522002288800c0d801c0450000d104503900200040c0390281002c01b0002c003404c4120385d681c2c00040121500640c0024000d0544003015403ca5494035500c6140e20025002c96008080c0c90030001400c3c1c0c90358083c0060700c48580030300d00c01d9004941400703061074505d41700d00c1c4148070009200411b002107031142e442da501440010342200c0b43c461040078010700e1a04014501d801c80030343c030001481503095800c0c480b1010b02040c1c1e40043c119042010441090040315100e504040e40840040c05000311749891170700807640940f070405818201c55a0100441c400441918086c0c4140502d4600d41051791018003181d0303801002c3c1071414140030800c600f0341180540d904d40001d28081c1001c42d04019001903015428020b401651101c0e0159282c05951088 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 831362464 1250 831361214 831361229
    0x70b060f0f01110f0607030209040506030a0c09090302030403051c0f08060303181f030e12030f010e0c12162c060309030412050105040c050a1401080403030207021e010801 75
    0x665054040781c80d80701e07501c01800e40900344007000c80c1100f16490b02d000c612040d03041840c4508018021007680660040402c144180c1d0f042c0100d0381c450303040c181c0c2c800100e6801410340741507507010484800319901800010307100f4410b491406d40c3c2c0b511403a240c403141002d410f046042d400150741815030820b2a0a02e5622070307003000c210303904e00100003c0d1a40689170785c0300400580c40119604a507544102c604141c1042c80c1e0141003c0d190100060080680c045040c120f8415400030a8055444106403849039038200b80c0005280e00f040009a041c41015103104181d200502481c00106040b501152144600784030006244100310002000c00e0002034400188030b5103030324200d803012042e0207428807040c0191102545e94540c0e107821451881154020010346a41001c49020448123400440c01103002c1c0c1c1844e88444d0b01c400c00c00800d0840340c0701d202404c00c0300200340c03842d95000c0c01249520500a0800506055943d000b00700400c080103510000841030048004456800c00881ca0140084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 831363714 1250 831362464 831362479
    0x308030a0b010f02060c0702210f06090c150903150a0e01050601030902011d1918150506040612153f0f06020409060b071403030f0105010c15050903070b06 68
    0xc1400207501c0c1c1d20013901c49090b00400241f6042551515210850f144c5524800510301d02000c16401c0c0d00d5190440150181c0e0040c5008a500b00c81e0000c0c1940340304100030040300300c102209040101950001c10070b5a003500401c01c851188002000055100d805040004242050b800b8440c0d4211140100828140341c40c02886001513684020851003050611a125090b902d421000a0101922002034403441c0c070050004103104c001602d281548210144052003d402286003142090806000702908420107000401c90184180d45003d00001c0804000590010541a00c0c011a0382c0f1b07040080341d003440880113600050504110b001150402070b60540c003d00d07030741c402c0850350151f02c8050000c200b090307490804c0c401c0e194110303801040400010480c6940d1104280002d400000f82503070160443c4c4190614500701004903842400303414403a4a45038204401951000c0f181b94040c0c50721502501683c1c0c901d43c00d40300d6280107640300c20081d61a041d1501c0c2c025030310040242042e004004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 831364964 1250 831363714 831363737
    0xc1a10080f0a2d02040203070309020a080d05190c08040f180504051905030c06101a030702030405040e0a060c210204152a1b060e0102070603020c0708070308030a0b01 73
    0x5a021058810040c0020b0941c01d9900c0c40f105840104900a00a50702c64400020720a070190158070a552061090b5085a85140d649800c1505c1d40051140100403c004020082c10300f201c6001d00e40f254001801c2455500c00070b900c034240c1d1178015400c0910356426221090006045072054070301600390b070720070501c11840c255945030b40f02d101d09a00d83c640290404500e0041100034016030300c00d943c5c0c20080341c40768070308615506c950301c0c0248104400364400c9004001d4951111040340d124401507001180303020b24003000d10004103a1600091228020400341c800052918015410a98625940c080e442940303401446800300721141c0138009103204000c100010b402d202a0440c07182c0d00c2d41803824011540414185d92a204080c0c102c20070011480b42c1c10410041c040f2001c85201c0409014039242e0302c0d44000d9641004a030840c07405640408403c20071184a50010300c02c0f402d01900388c3d00c1c40e41c0c0d252071441c5004083d410407510380c0c0c000310800c90405007030720a111400009181c41c0360b0204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 831366214 1250 831364964 831364973
    0x5010509190b01051c1a03060c03040b040807020306090d020607020106050a0302041d07061707030e061b0c0d0c0510020f03071803021f0e010e0f010c1a10080f0a 71
    0xa010000349070030989544544805030701910640b0b900c800c2040907650202a076908180007841d0403000c2c0d0700f540c060f18890f003005040c00a040c03407103046003806031441c41c1c40c3c80c1c860340c4c0e100d13030010030440d40702e041082004016242400541d01424101c0010542c0415000c0c000c1e0600d10000c0420303045a25004d010040740d9a40164242100e4069600050144a620300a9140f486010840000f4455203400007501d6500c40928004143c0001040c2d03080d45030114100c042e24480b0708070802d550301050108e40000c144101c200c1100824400051425032205100b6040c01e01c406481d03004030306003031256030510405000c503030341d1f58611003000c52138802d44030041440da010140c00c62040014080c01131190074580ba0b03018003e03640050001841070403001d18a04a100c02181c1200080d0390405220380f994000e011007111201c00401c0f410040c0400702c0110b6004100c3c14090f0740e4440142c82101540d0454689075000d4058880084846c90604030000d10744001703103021503030702da02a81d460008103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 831367464 1250 831366214 831366241
    0x120a03030f0204051005072d03030e0c041a1305010e011211041103061c05060a0f0b0a06080103030f08010609060309052122210c0f030501050a05010509 67
    0x55506003400039641030850305200c000d02031034104075003040d101c0003611021034110b03001d413101c14460305080c41c6a40b1900c44030706a105529a4403800d43c0d4000b0078500010303002c0c1e005118203030116021100003481c5803000030162107001010009010b00b48000c45454101644010211960b03000700f130089500d000012109284144200c0500240b0080c2a0b401c20941c4614095040350051062200380515441380741b0aa1041e50318030722500c0c0800e02544a603070380507480d1594681002c0640310baa030360079140b038015291919900032034507035803004541c003581c500104074003820701c3d48d0b175542c7c0700c0d0305500e40039000745840c802c02c009118080d030040041d0307580076126030140e444501d0045131101c2c451030198604040920b0101030542e000350103680c481042805031901c440076070107503001002c86030b0071800003032030b203004003002c00c0c50120444450100408140031010710840c000c0b40c181d0741d03e10045a581b0165081110303281d45030001c2c012209114007035640500411501c030746d210300304501800c10750b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 831368714 1250 831367464 831367483
    0x1615060603050c0a030b0303210105010806031c050906090d060903031104030c05150409140907060906200a0506040b070e01091206150b040303170109020418050c1b0c09010512 77
    0x4058072202031a01d21f4409005440d0b0864410240c6c14500048001c1c2c0a92041c09005e044e0009808a0004103685400900015074403039a0b015902e52800c40304049075503900c20325000d90042000c004440d043d0303d504109002507400754034009450303015440c1c02420341c2c640305c8070359032040028801480400e0ba012041d80c00c94004469000c1042d03425840740000340190390062681a18026a656500001040d40c038441c03d2900141c8018070307140c0744151403488140c0070b520b000405490b441c4031040a541040c2181030044011102e0342220780e9515460300408036004c523800842c0300e003881455608040c0849001c9403d00740001e9190034510030383e000202400003d8610754a40d698421841960380166010301120320b407550703455499040c040c2c4148500480342e0f907444c01010002803c01264800d840642d01d502c0000008501640305d10005001c1c003404100010b44104904140e0140c080c41302c2e07aa010040014210507070521041000d01d2034141d2099005401c005081c81c0c1c40c007800300d80f0001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 831369964 1250 831368714 831368717
    0x6270a150518060712090506040609140303130b070b06180f04030c12020304170c060f0d0f02031003050105160210020c1903090e01060f020d050f1615060603050c0a 72
    0x860b14000c4404240b404190380c0003642100d070018841044c09490003144003294070355150904040c0c2e580d0300b844103c0c4140e115501c00200e5041d81070044621000429101c0038000301141d05242c1da202d60bd103c00b040540c0000307408800021440108145407a05d90340c81041140c00607030f142da03036030200070b80c030b0a00612000324031441c00001810140111036108030b00b0781104c08000a9038496401941e690700c0350052400d01828008888250310f0005211a42000003800c2d25050100b2503100c124039070080b454a2102da0749900c035907105070015102441c0700e000308508015880d45107040c050708466018103401c0c180e94003540402d41141c0c00103240200d030704414600594074190081c0c1d05080210b00a544540d0f4400341e00c00000307244e070003a0a081500d4031124800e0503640d807400140c1e1280e41000344100542c00c1048050459400384002d025032032090a401890620360402c110b41c0040460001c494500d000b04074004660107902c41c00000d0201d40c1010459428003a24108403070054011580 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 831371214 1250 831369964 831369967
    0x306012615120d02030a0e0a0f1202010210050a0902150c060c0d0207020a0923150d0c050301091b06050414040903030b0d05030315220c02010b06270a1505 68
    0x9951500c0310440c0381c40c5104000d5410f0202c000030000c0d03c9500a180610008203a803c1514080c50289065000c8600a450380100e083ca0800700c03040c0c0350f941c000c050381580201c00c08042c000b1580d0040c144030b150304600009483d00e00c1c4c41004641c500981c03590700074002c184078400c481000050352035040703800a0104c035150940142418044e11582d00001d40000d03010300009003c1d0020380090741d100c0c086031f500610f000035400050054500448074008410501d40c005442c2c0e0a1805040603882d004400380c02245032200040ba00b5240c2d1034408842d002040d00b00d108512140c010444003921151800130300d0945440004035171440100551840345a61b1081e00b020140640d100303000d00138015015080341881801d200362203803c120b80c1c103001c250041420319900d00c1c04550800000407000b08c401403046507250864010309120b00f8080030f41d9a2a130f0041c07240da443d28040d01071404040c0c0504003d40d0303a542880c40181c82240850b000b40d071500341c188980304400d44011515161881c149c3e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 831372464 1250 831371214 831371251
    0x1b080a0c1106040306052203020d0309061b0c02040c0801050f04020d0e120d0506040b0105030f1f2c01120f0f0f06050603190b0117071a03060126 64
    0x1100391400c5110703160307002c800000d00100700226030b08540d1041046160b040d00ca1406001141a0885441401001600120651010b20f800782e440122200d0190400103664038210402d15040610b050744030010410703440004045150902882080a865151030141c5516100209401d05620701401c0e00c10364010a0201211505074400c204a242c1601100c0d41001d903160100080d600000d0024481d42c1003c00254150400b800360613203641c0c060355850b00e0766940400b680e48602000d080c0700c0101d2242c1203114614805078001d00d0241100c04281860710303400b01c200c0e0b40c0c80452480c01b18032103407640004001c09100b015102108980000700300700c4051f00b51400941c01106000c0092802d1020120007007400083d03403001d0b200d107006500b00c500300c020315241c0c0b60780a208208010b100100440044c0b11802990002d0130260001700115145191924229043d82100343c5d00d156090402004000c01580c0c000b0350b004500c60007040c0d1410114201c41c140d021031000908900f140001c00058 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 831373714 1250 831372464 831372473
    0x5010e100c0624060306032409020d110a0501090b03010323030408240f1503101404030f0810030b060105070609050a060b0a3b0411011b080a0c 63
    0x4140949a000c0000c200ca003e9004120100c10000c81410040c080c01900100390b00740a84554030690381c1080215076a0a4084080215451964501c4070301c0f0b5140d50071140182c548848003030b4202d03c50034085c20550700c41c000313102c1c0409043d403005040040d89101000810440741c1202d0540ea000309890f901e101c4803d83c04000405194813140c450321000500007001d0a0201e0205003080380788040800e80350503510240c09402066a001f00007000036000319007901c0e0440450520f07110081d06031100d4134400441300d021120307020300614440030310104000825a002205034203031041414181854240400020360f101400e000040c084600e620120701280c1c050816101c0250380100c2c18450788200c2d01d0100e884840f011400c030344030303420250080450320344211500251001c503210740e10001911059078407028558040601e10b1600000d811a0410180c56181d20660140554440100e030a0000400d00905102441c4400300003481d80000640100201c403e4034000d403928031040010340c00d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 831374964 1250 831373714 831373727
    0x912070602070c17070f140619091d0603100c0503040f020a0506031f060f020d080a0212042f01080f0403020c04052406090f060d02040906090902130605010e10 70
    0x41410130300341114080c0050400007404100b80c0d0101c3c0c4100030310540c3d0304041c5000c180e070f2416803035101c2c00a2192030001d01b007c19030007503042c420346442400d41c0c0d0703a8054000c200100d40b515148201d0000c04001081c1000c00c4840900c403940c0c8000c1040c400400380080003404054001001c03080e00307072a0f82d403e5607162250302c0080c00d001450a5030b20b06080110078024a410202c0204c49800f040002800c94040c12802c21039010341d4014220080318454100c5043d00020700c1c0d010f07019401d0100e0051000c0504001c1d1040c1c1c426450441c07140d24019242410810f1622000c40010700d050349034180380d078494500c1d6000902d16000d00f10300d84a07807500b0b9062600c112180b1f6003003841c10b010089140c01411040c2c5504090b540f402240c90f03078410a22010348603100c0081d41001c1151068540f505007880105002e05408800500f05501d034040b00c0240d440690101620640b100d000c003065103030260501c18101e071070150070440d00b803900002a04031494034000c188684030000c4c01203d118040e40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 831376214 1250 831374964 831374969
    0x203121503030d1a010822030908241b070206030717040c14120604111c05010b09060d1703090307021c0c0e0712020708040518040b0912070602070c 65
    0x60580b5101c200e80c2506000804c1800c40380401c45807864a20449035004005181c02082c03500c0c28003203040300d4900f06950800540200b102005201c05000403c103100340301c06202c2d400b6081c900d0340280c03284041102160000780c44048040c0340d5109403d002448030007110201681511301075107990741c600080e0341c0c0001c04c2d4803261743c40200301304010811240302d00075403d42c0e940b45003440304c0001386810b1088462031721681c2d010b550701c1b0718003050101c1c0b0000342541d42c851006007020500030411902c60800301780d03103c041384c2aa440e40d101d0300c414501544030903400442030303c004026643c5607c41c0c042c2c1d40350171000c4040083c2c000000c40d054100a0045821154001d89202001004034961498030031081a05450f80c00c103204000c035071103400000150041a45030b4413010f9840e42d11364210300a5100d22400c03201d0910820000405449041e405050300a401e01e101c64039241c84d080c052410b5a0017880001642c0151424002e101d00210a803152503400040060300c070602d9181540c1c0d1103c3c20f8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 831377464 1250 831376214 831376219
    0x915100821190306182c0106081c0f0e012c0a350703240f0510050a08370c180203041109090106031211010e03090102031215 55
    0x81c11110b085507015080300741141c05541d401e001c15640310082100322058151400003c00e4554500700811120200801034414090300000c0e5280d61004002d1824080c136060541d28044801508040e0343c0120302c5524901c034500348106101c0e082c100003440c030115242c001c100076008040e15901e03078a41d51a2522460301c00f500100034141c135400090054030f21480300c0a0316084204011b1442e08900030300007036201d0b9000050440d1429559141c2800c142c03840416590100300841c850030100c2c90041420900030888009060b05080d0300c49602d10041da003113a40980101d078010010094000340c0408000314400820b03010301c03451405a0000d010314003460046610300c0c60050284000e45007604101e400030035a5540c1c800c0d54010200990004a0300030380b02000421b03801e1b4182c01c1c11012503900910340000082c01c1071b201d5035540044030040b10f00e2400942140c2c1c4442c20318509100e681401b052107001903080c1801070000035920710801141c520300c114001c012807072000c41150303480200c0c02c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 831378714 1250 831377464 831377497
    0xf0b180706030e190f26070b04060507020a080301090b03070305010c020c010f03090c05040b01051b0115090e031e070606091415031b0d0b0915100821 66
    0x8401004003d0018540300240600440e06107510b0440060088003070030b50f102c40c40800c215215110402c9000700c514404a03840701900d280c0400080e62801414501c0c0301c2c000032441820281040f40840304000c0083e0155807061080c0f101003141c1d00240c03811102d0f800c9000c03814402c900086410300001d40d000900540c02c0808003200d05070089044071030a0400c1c3c3c0c3d10000c62000e00011001c0d6010f05901800709103000000341305c0c0342000d8100c00c05070360043c1840d914000146200c0344010051282c6540241d41d50080f68030310000c203071440030050401000c18056150300d00000303500c07481250340d918083c5d04103004000345a00000140c5110135040701c810001c1c6a514112000a04007041c182d8502c2c40800000403400c840e0480000c6018001030000e00380b1110200b03c9207444903140c80341b140d00c0b0340d003541c6080c001034200310014804c03103070741d0080d2407d041c1080d20300080f00b4000c1c0c540311a44036030a5041c04050400541420300100400c03400c00e21058044050741c041c802c00090300d403060803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 831379964 1250 831378714 831378719
    0xb122a03130b0705210604060b0c0d02010c02030a050d0b0d0503040b0c0712211209150c090e0424060801020a0e04050c070624060807030501120f0b1807 67
    0x11110104007602035890911580d841540840301403103500c0004c0038140c40208107400100740f4070041d1303038031120141c0002441603d0f503200c6a150b822131194660158440039980f0199542130169000390100f0780001e5041419214000e0b1850040c1074003d40d815a1701e030700009899890800d503105054015050701d96842c1c851342e6441d142da1000200d482c15101e2624001090109202c00d8020307240c1203103040d0721004210807100d4002070100962420000794000e008410407640c03003501c40d000d1180401e1440d00251807004010354030407500c0c5100b4003241c0601081300b05150b21030039034020f42c42a8140845804202c140c0d01c0d02250011580c0700074039000b8045201c200550040c082c010b0f0740d40700c0d4000017030311b001000300350350341100c1061041c0700600040d40004d455412641544141c035000300c400c0130942c101c0702d403480c10b03642c0080006069582030294054240c420745e405003205400c02c8620031203503180c14040a600b01700050426148100080100c82207400015903036201d0010750b400760342e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 831381214 1250 831379964 831379981
    0x304060b120d2a02092d0a05130818040603170703020111030114222c0d050a030b0f1e01080a05101403011d061006080105030a060e15040c09060b122a03 67
    0x300840e0700c87c031000d00d460003007a88104102a40340c0d5266118001758603180b031100440240a130407184031500f20380c4404010000450300e0b44440100320b075801c1c0d9070762500150b081c0242507580c6c0b1140160307264420001070245521902074079012013000d40b40e840381c004194078090219000280840d1441d072420101e0b0340c4d01204107852005000d40e513851004500c2c40c10b0a000c2d203031403400e413109020550802c00007121a009402181e051b8800802100c464101c40004c03a0403000034551709004c82210902901d42c568103d0340c19070304a010003000b0046c2d8a0030705541c5080d41c2c0d090190304418003061034845407582c2d00f50040409000b0000d03c56188440002000d036844605a41c5071758481242000480d0051103000114100c2c1c400074011f0070380c0d41d01ea0711800024100000e04210502510b0007403441c0d5880a41264003c40c811800d0b41c1c0103901d071018680c2282d4864000211007682005402c1c0041c152080144d04032038101400c2c84820003110b1483c1c2c0300c46a00001900c800404000c1003d0031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 831382464 1250 831381214 831381301
    0x13150b0f0a030c05180907120603060b10260c160609030f0203160224040b070309090b0303090909030c0d08150907090b0304060b120d2a0209 62
    0x101c0a0761000c0c800720881e10780035103190060500784079102401408000b070900d4124122a04519641050103110a050001d101903404681083c1c0708142c81c0c034000240c80c1032000140000144a242130304003078100c5240d0b583c034585c0c46240c0100d0004880c010031040728205040304c072450600e00602220b5491460602d010700038040055000c1804420030089460001c0112403500a0f40072840300070040c00d60800034101943c0500500f00c8404821550404250000800280c5034110141d40c4070320303140c5801081440c841e0003141034182004640607107603c1c00030603503c0c560011904140d0742ea94020403d0305e54090503201c5c00d6603104044107055016008a059406601c80c0d0301c41000000a54040c400e410702e00381c50201c0080c40145080080c020544051030b0002c0c8141e5011071007a500c0000602d028010311007042481d008080f1281107a42c010300c2d81c111010341362908900360b20000902c490310608204002c0e000f400c6107400646c0299100c03c5d110000c458009450102d18054840c1c4c2442 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 831383714 1250 831382464 831382477
    0xf070506060102100e030403200621010518070507050c090a06050112020f120702031210180510061409040603030305040203060903190302072402031e0613150b0f 71
    0xd4014071644003011912401030612281590001b03524181c65603481428140c2828000c2c401c40c6080c3d2201030f03183d6520801440d030b4030481107507000c0c0b0080c04040c00714811302c184d0155102d6401201800da2040f032038111944d02c13508504140d51901c0c41420824108910b0880c0c103035000480b04100021460300d0b92109007030354000e91700d000f011641c0510700301c0dc07841840448400d03108244500002881100d000661204241c4141c2c1d01b00001c0c0309103020441c4c416280551110100d420611040a68059200c0c0075442580c0501c00c130305182a411180c4046030140008114507040000d01002c1c040c02180c1684c3c3c400b82041120030340d24180240103241c1500d08921a001d00d10108007a0100001500d00c40d03901611135401003104480b040d8001d42c480e41040f41d5600501d807401103250b80c0720210f2425010200b80241c0e0381d1505401e01a50075680105400d4086829400d10240e600c428010301c0c603004441c0e0b00040d40303501001d110361200038160300c007801d415800a115540e50b003001e40508030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 831384964 1250 831383714 831383717
    0xf02010c020f10180f08030315120a030c060c05180f0103090506090604021903030801050103051009050702060906160c0b041a01090204050a05061c0f1d011410030201020304090c050f0705060601 85
    0x1141c0703d0545d4003a01100d803186601a900a1022603800c0e00060000700342900300410f1090a07a2150441c18186810070b00140d02052051794200b00f4045180a040e8603d4507d103011480c00c0c01c514039480315901d42d07450035030144821030340300340e0340d41d000ea0300c002c490607040380858200d440e0200300e80b07a0310181260128060079176600480140c17000040000c060b00c2c2c0c552540b9003240c0c2000011402032000800c0d05918103045000000c0001ca039206050081c442540a480c09240141609140190217050510318520602076000300383d5203d0407071208a40c0c400403000b9152900c3c2030120802e10141c03d440018680b0340000035955595074001d100f00c1c1d90580b00ca4816031b5484080080758000c00000034000d4440e4114424518040d610000c0d03003e005020010700521485040c0e0316146041d00c40c188203a656032401c55091909000c1681e100d8201c3e00c5006182d400e41c4c2c0004d40728015407282d8210661500306283c0c0850180059400281051803520740382d003450306200e565010160340060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 831386214 1250 831384964 831385007
    0xa05060f0a090518030f1c0b0409030215220209040f1b06110303060f0d020d0c0605120108011b121107242a02031c05010f09090f02010c020f10 63
    0x10805804415140031b80ca916009038200707807039480650800380b40e031010303060000c0eaa40496225607555108412a2500a034010302d84c04900320340701c1d000304034054004240d000c4201c0e00b0604103401c0307254209050358140d4408426403240d1406141400100b14010200f0001085e41e0202c521050f200310203d03405c0ba651052407140e85106280c50f403000380d9144c0e811001045007111503041ca00c91a1581c244060f15128401026481d90244160303036402007400100005580000705118010312809403401800812400d80c050b200d0b0500c0e0b6041e03541c030b00f06000c9005408059104994030900d01d02485070742c090b03601c0000b4030b014500d5115140200302034071400000421201114400c0e0030444488900403221000507100411403d00d90410302001c40c4000c000a90310310341c00703901030b541c5036680b41804038407541401e646d207095403080e070080214189010f000780e004c00e04400b000410282c0a0816040c0000c450000c68071448500b8246904641c50781200f000303130f1f41c0c400c1c4140c180000011548 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 831387464 1250 831386214 831386251
    0x180705030c0402090604083c150402120607050a1202090907030b0a0305010f140a05192d0b10020307080301090c03091a070f020703032003091c0c0506040e0a05060f0a0905 75
    0x2300002c00000c507510303001c4d03404104203024840c1c2c8240b525030000d000820b501e0307100d841107040c03500c0d000040b01c4440006901042d06180d85420091000c60110440000d500f003602c150040b41e041c00b03004240704205070b150144440a501d62644072409035804c03500034055041c0d520409400b0b40803903481c98061140c5880010b903180310601c5550301a100e03491a00c1c0205003401d6842019250004145184c041d4601e030440b0349040702e00010791022140080070a2a110401c100410880d00f04004801d54000300000b40c002140e140880e130544c1c604080005810800003403c42c020006004020011140c1e150801c232040d001c00000d5100760907507901c4c1034044006240072626000c040c40001d003c94001085015005900b01c5042c450046c4c102c112410140c0350310002d100103d02c000c41c8155071500044810902c041c102004010308010b440c5a441d041c541000445a40b4004040e1001035a80314081800c2d507441c01284100c400d401004039201d180c4641150300241826101d00403c40a50b1082 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 831388714 1250 831387464 831387553
    0x31003020a0b0a0e040510080a14010c0e09070c061b03050406050601021906051b030c03010303091e0b0706060e160801210b0c0c15180705030c040209060408 69
    0x48038032080c410382d544003918403844d0501015100c060004000500440f901141e001d01c1005040c0e021340c0149407400c210031440e910b0350700711844100b00104005002c04d141134a40c44031419250800c9003442e00c6960f866140c1054801030180381401208140f5104070104d2032035168003c0d07809903000c0e00040140b40c842d440107907034901444a000d5000201071698601194060f8040d5070b0021501810400440da05101c41e81d05d035104403011944614080014814035610520404c058000c035502030020039a030385d01200b0141c14034800c102a406001401742c01700710194101030010040d6845004003420055400c031203110102031403030002b0b100f42c00001402507500c40c80c040e0b040700c3c038150703017070a40510b48a21540385801800c80303680003420041c500b06910300b00580c5000b28a041148603080c103281350009100185140314041650061500740259a4007003010320002c07900300ca0050ba16561000415a44e0155a0240c40f0a0192001b02206c6002100c8910300415140d5400c0d00c9105d410400e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 831389964 1250 831388714 831388717
    0x81b0d032301080d030906020c0f0f1b06030103060903020c0a0f1503140a1503170304170702090c03100b0d270b0c090409080705010606020f1b06031803031003020a0b 73
    0x18228040d80103282004d1036a000b0f0b481b140c040c80c09800094548007442a00c00e06c4c160680203500c3c07044d4410b8a51344403040341840a64010f05107500c2e0700701d001c440b0700000380e401d001c10700000d40515034488582c004c05000700482d031440c03440a80b180a01079030328000c01141840f03501c0b03480003d42d580780d52401881c1c40783c403682021640d03c1c7d503011065100d00030801d0082c00043c00c0041c80300c065840c0400400c88610292044050000083d81d5911780362600003a48103001a4031075010b00c0a22119006079240568194480f039401e030341a490f0703943d0401884d50391b905a804134018a030006a1190540c00540000d800c0d0111101251031051459000e404400300354040030302515130160110b490046200020508500d0041010491500300d803a0aa215841050220354580d035447d8100001501400b42c070783c0843c00c88010b0010f1003036030031404091850041d441486414000002000880c60300522040d8002940440e0384910303019031010a0460580410380c807407014400c0001704400d5180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 831391214 1250 831389964 831389969
    0x405010902040b071122050a0f0b030604112106100b07020604030b070302041a2107050a03050916080708010506031c0c060e010c0e0f030712081b0d032301 68
    0x310f1070f03e4031030300b0f4407000c2003550b14800450b0311100c51010709000c0055800c01450106034070320000b41500f4091018412a00220070703070a070071405c00096005c41d6401241d01607009810119654409151400254808252504004a030000b1a01100c0155000100c2a04c0703420032001c03096540d074460411032a03a0003403007002584a0f030100700c14000142001c1000e60803900b035003005030605486200402c00d10083c0c0c140d61400000120740000000480a001143c11130301081d6000c0c0c80c1403000c1c00805034442c8006d410306050f2a8000700d003004400300802961a290264090742450326003510070b4540d41c1920402c1159802c0c0000b09030b242ca400700d00600544140a48074030741c001903100a68001c0100a000d851003070f960301070b10005002c2800340c0c0702c15818030781e1042c0480412070308005004410b518894025800001c1c20700040703060514100050340c10201c2c0d9078a9a5600e1440038041c208000781100307034090240450b94035600f64019194080814001300301e8008030403020b003142c86007403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 831392464 1250 831391214 831391229
    0xf020307022805070308180a060323010323191b0b0f03070e1f02010b01090608010803070b1306021201050a050306040b1603110403050c15040303021507050c011505040501090204 78
    0x490017040040c40010081050800769070300118012284000114060002d5018034042511940c85126101101190000004c0c5e29000c907003082d41136446031200d003003004814041d11001005d41001d490810489845003e0100d108c0d031201c0645454003070a04000c9014014107c038000001140c0c03c02d800c010b41d03541c140c1c000f28460130750782e81503c21607814030890503941d04241506890003009100c2c20b260100b0031401d80010416240c00e000041030300c6d80f9588140e040058035001445008008004c03201c80b07680140113a020b6403202e1854000d1300c0c1c000c5800400d150f20010380c40c0c20418108110f00d048032421907080600f9980c4d0014991280400c8074000c202000541c0020091445840403411560942c90001803c21042184181039070203074100392001c1c1e020704101c1d0100d1400208880904220300105030602e469035601942d1982c600300420b40c88440040040c0000c4d100d2000e0350b00e200c081100030b224203103400e4051340514140c0d004032070045090034004a20682d05000f01d42c01ca80b0305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 831393714 1250 831392464 831392473
    0x604080408012a0c060e03030f150f0a0314150901050106170c09090916060302040512070b03131a07050715180f05030d110415300f020307022805 64
    0x403c1c000321240030106404840d8150b07103142568000c1c4040015601c10b14075503d40040e5070500d41d01b007010704130302020517900c0341100d000d80100e80c1d2542d00651045a600007050307890049003012240c2001c4c80a40f1a0f441b15150a003040b003c0001504a039040380c2454485404441903011007507407106045440c0040c0d42801c0101d010503040912039103520810150665440c507000c100707055452803c80c1d220000003500410103214520309081c114200040000081010a1038100400c00c5400000d184000465031402c0c50b000740100140318403c010011200d445161410341d40c0134205400c04001030fa480c1c4146080c00c20780e02402c3c8604603000b10b211508128144d0f0b2595200c91003c1440f03c1100d5600042c41045010006c42c022402e18661003450360791954100030300319203052100105101001001c5180c2000050b201c0304a03140d007000d06440440c0c7c0c4106031245409000c40c02c501000070703840003080100b03040e408039400480300120041070f88c0c0010014a24050034100c440003a0844c2c20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 831394964 1250 831393714 831393791
    0x9030507031b02150a0e03030d0f060803030402010807140c030d0e2116020607060e0607020f1c03090809030604060b040b0a0b0f03101e05120d0f03110408060408040801 74
    0xc504003031715040310030b031520700000aa081d01082c19a008271113039602807501c8100c403195600c10b90180c5805490a0700003141940707881d40000700813800c040e10700c2040c440031800518001495008854034072801c4c100312551001245600e900600e003e029481084c099500c034000079500070006640d4010100c098141081411418086105040d01c0102e03448441080508001280b0340078446400e11110040c100c4d9262000c406410b1a41807560744c003c9030407404000300807000b82d070480b400015042c0340002e9031400c00d180c014428425042d4190303242c40303034100700710410155400811052101742e90510094200c1c205018002c003075402a60003070340042c099624985046400b85038003440b0030310707420046a507907020384468038001080300e00640c0c0300101c244524103000c8500404454410001e0005042c1d8920007840346581c101c8440402d0345540c03803c1c15440e40d040943d00a021807000f5030301c981c01d00e841c04520a0307100344503400703031075003030515145880c0800104c031700c3c0b400800b0054144c0c040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 831396214 1250 831394964 831394999
    0x2a050102031903050901140a2a0f0c140102070506090c0402040e01030609081608031e06011d0112020d0e0c061c0506040204030b0f040c08060108030a2109030507031b02 74
    0x1300070b0400351250350700da5081e190800c0708002070740180a40380c800154031900c0003c440c128101940801203c0e03a00102020b801584640559802c10062404941400e11490b010320000460b0120368595800410321405010700442e107076001d40c03800021101c101c0d101c40148006ea000340c2c0724034440a00f0700c000420204466802c00d0f00440d02c10409289480503500340040d58090340310007916480004400c20290154003c1248145480c0c01880380e002c0c0b0305030300000c208030300500c0e02c1d40806090f40309024460340600c0340c0725160130418405545a41c59650140018040802b492041e840388003403900d40c0d42403d10403a601c01c1c411101d11424025901b501d00082c05c000f515170b1b80c0040e0300700301c000080b90251280034010322940d00b015480e818641442d680c1055250030040c1a44c008600401558500008940c2c51308102d0400c21140c081200011a8402c80c0044101c8858105082d620805a1250090054920035103802240751000d0300d0600000284e0540250007000c0d607251200440b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 831397464 1250 831396214 831396221
    0xc020d0210020c190b07030501060305011202041d0118110d05060f13020a0e0609090601150f02210c0d2c030a0c06110c090919050a2a050102031903 65
    0x141600d0300b181c1410044070309000040c10040d134140e8003540054140040150325010343c0e4010580c520341804654105251708060b400c0c980740091040759111080d26020303410380300003012143c4000c001c01c1048162140100c841200c0442101c103402611904640d52805819000604d900302004000360b5641c00308140c010031010349240074800760540004010780c0c5880701400a0001000c0d1103440382484c40034002e500d14082c0c4559a1500608010700a07603aa14241060360709040c5084081c4440b41e140981c01d100035946c651485188032110b482c070000d004002060900094812290004400541201c1c8a402a51840100c2e12407007903000e50611564040030100c1c070020150307803459042d5594642200003d0344040d003c26542100c0d4842e019040c00101034001050703450100e2442d1120700180c40d480341e0002c5503041488076071000c06101041242c004030607030100c03e0307922540440200c500d08004504184010804070301c0c0100b51540301005032109640c01a50140c1c03800c4043c803094018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 831398714 1250 831397464 831397477
    0x221e0e010e06060103051e01030309050a06300b041107030806190506280804060b040212191803020a021e100305040809060412050c0103020a17060102010b060d0b01030c020d021002 79
    0x42000900b20300401c4009101f80c2402144285c0b02d480509241005002514100303174002000d01500d20f00d1004c0b44054031000ba083c001c244105041c0c0c0810840003003000b4020710f061241c02c41d150154402e002e081b110024060036001c1c0d15148010b61b50501001040928451804001c48800e8010086400c240c0083c080c00fa84086142c0c0c841e0406e40715080e407040c030b0307402c21030300007a1a10144000d2007818499038280203416203040d441c0106030501507650800150107010794813001e03001ca644a0401d588000100c0d20301e0b01c207220b403204c55802c0c001d5551860841c00d91013404100d56000340800e00c0c121025443d800a171407002d03030762643c250070b50092074003c20a1b5040b240c108501d0213182c0d030300d1300200040c0184005008a040150800d245820081c2c0c60350703414944104185030b080c0d034200c03040c0442400b19119902d0281d5907a00100d01405e021011140c01c20004104031009103240d4000c21080182a03a0030404101c0004003240d03030741200d10710711000d6007125031000f00c440a0b94004051 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 831399964 1250 831398714 831398731
    0x171b01061d090703320d1e1d040905240610080604020d0917121f03021201060b031005030d142a070915090504020609221e0e010e0606010305 62
    0x6840301e41c11074105000003080c1001c0f0750f008003440102080d000031f410104070003210740b26540d940321544050039440400c00b444601c0103004101089a5495420504456910030140c80c4d0500d44a2124032031902620f100d400002240e400140c542d00700300204035a2a6219502e2500307645400c41030200170340c08921441482034650443c40c0208840c40c1c038000404945811b10b40d1f0360035619004401c41600178100051140081030301c0101c1c2c100e0b201c0c0c900c05403601141d90304d8540f80c04604a078010503c036032207070541200c08010003060320b40c0250000e086420550544202d00700200048406c418440c0d144586940144000c0514071240074000d155406138401e000b84500c69080d009103010050f80c0614032103a1560b191034042031000081ca001002c0c244010300203820554001015030003201c41c1d5030b00465104131200c0c40352201c2001e0350240b0990303050400c52031441404000365094403401c501d0060342021682042d542c13051081c42445030a6202402d400c0d00d0341c2c1c0044014143c003609041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 831401214 1250 831399964 831400013
    0x1b030c030a020702190503010f09051507020709050f0a0b09041208100807090504021c12031a12010902010e060711040203090a0203031306080c0a0c171b01061d090703 73
    0x5031107a1172191046429155a504030600d40010142075030740301e0900841d194100540e24001841c000bd4042d4070703044110400030256500482240340c1031081d40040401410311041c00601009040010700a201240c4180b02e411a0b00040c0070468006940040c140340501c5440780000c1e11881c04a900880c8000c0b2a0300e81769a2444500d151001c2d980020f510540e85105010451030800c0f210400d040c4142e8200303911108544032503030703040d500101003c02e00d0317220b0302019202400114600e4140030000c1107112050890903186000304400f18040b40810701d0403a9102e034a203082426038815561055502610b0034400b401c0c00042d4001a0180d0342d80c0c03040d0244080141e4092014008070101c6440c02c5920500d445401015a44081d01800d084102080b40c00c8805501c00d114084454200c00c0c2c0e941d0921a03411090701c6803150040075084031003a039440b00031f11001034206c10210358610813151641c44040e064050030100554404e00700e58840d078820000124040b0408a14400740020b80c2d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 831402464 1250 831401214 831401227
    0x1806070525022404050a1a16060b100f02070b19050918040f11180403051e040609080106050f01090608090a0213230f01170304031202010e061b030c030a02 68
    0x11040075140035680302c03c00c4400b040511843c2071150081c0000c2c41c0003040c6180740b0103000204250740c400c60072101901040720142805115240d001080340c104060004201a6030744040101203400c42c1340e4035401406442800581404280103840303626520080441c14000c2c3c900040c0e609a0000400310780010002c5110800c0300d54018040d4403e80c000c20b00f10381611300074030b01103036489038204800d07114901425124010b4079404503016486030740340c00c041e0b0b5982c80c01440310303030b8801100f02e244000304000200424103940c0555141c0032106d44000a00100307888000300420349080c180110300080f5074500c00c100d420302c1032a015400548000030fa4105c84000d130042007146100d00559100a03441784074000c120411b051030929030002c54a4401640d0400302000100180b0601c11001d50700301802c074103c90468103004440085502000004103040d020902a000c6d0a8919941040b8000c40000407180e03610684c0c05d80c08a801100304514690704c00c0710070310043d08050141e000b0070b9403d1040c2e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 831403714 1250 831402464 831402499
    0xd03061a1b010e03041d07080a05041b150914090403180b0f09090601030903080f060a0801091416030c03060c0e06071419080702060a0c0506180607052502 68
    0x990018443c41d4002d9569641080c0820300060360100d90905081d500d1802c0040069110f104560400700409020409031200e0801000042d005583c844030b55080c044c00082803c840c40303146030b54810540b1554080e07236840c0030f5410191000c448982d08099242c0c0083c2c00a4400ca07003101c0d0ba1202907066540d140d0b103500440f0b0b80764202003070640120300001a0f00d1410316003201100e0b4440000d203030500c2072180540c0d00804030700c03000c0d08200f4218800c1c03000c03643d01c0c1d480402d4440503158080c02044a0543ca043c400c0d258211100403401e94001d460081ca4540d041d81024030a907a00030144039801c910b5991110001c20040c5551401c000450030706a049664110041107054040c0242008010a262180d400c200b5260101e0500c0c00d10080c10400090302941500c2146404072001c5031100301c00300d420b443c00190407a0041441c080e540806c08200360f182c0c03040d19006421030030cc0741d6035a10584252080e104100003000007113825089426542241c0440103140fa01c050f0808030540303c0c000c030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 831404964 1250 831403714 831403721
    0xe100b0d0f080f1b0f01110a020a15020f1305130504170a0e090103030c120e0a0603050a2003090d020307022b060501081e03090d0210140d0b01020d03061a1b01 70
    0x1822920b50450314400085c03050034041e03c4e80001c4004c800c2850041c01d883d02a54510301050000d00d01e40d1040342d5031411365425410f480d011100010007030b03521103011034844036021450266a1081340702401c000a58802445142c0c4200e6200a0010300405034000c0440203030401c82c10001001a1042c4280e0700307449100c10a8000d42c441d0b100c501d000d000914101c00c0415245100e102000304c03194295180382d4030785a54000300c0e013483c1800940d640300d19409402800d0711444503609140084100c4c1009160f2f0b000540c0320b604000306880d10407020b89822a1680b0642e0000303580134032070040085811503038442d902c1854100c0c075540b00c1440255a1800c003911800d0f031103402da5801002c603c00e41050000d417520710420000000e0f5107821001000240c0000d10010040e000e03a00b0184407941445c040c902d061070404403030b0141910b401044885201824059685a005002d002e642d54184d0f4083d0041006131000e5400c11001c420021052580c0e60300a01c031001e0300301951454800ca540420f00c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 831406214 1250 831404964 831405007
    0x1710030f080a110c0609040c030b04090302030c15010302010504170c041b0e030f03030403110328030b0f0924130504050d050f0301050d020103020705010e100b0d0f080f 74
    0x541c03251200031800024003182a05111000160400b144400103992500c0882c2c01800c1d003103c00042c81142c06204400070030b101d80240b60010b00e0850000285034000028040501c0e009048501c41e052014102d1150782c020320000307001c164184024000700500c07504100130240d10b9070885d010310f000d0740c002400342ca4900c49400d0101c1c0c40c00d19480c0130190320010002c0c90303450540080501000344c22100b0f91302e10008001404000d40c440c0040740e41c42051045855075403e0034180030080a4058007841804800c40590021a20f0104101e0440c28a2412a2500d0b140200718555903610504010541e086071700c45450140d040c01c0300341465540700580440280005100001c042c0340c04c3c50030900c0c04d090300303814405009040c0240310900d030a540440341511416680411030f03000300d10040e80a4098100001c4c50f0354201112440807810010b0ba80507000340d420410301c03e10b002201071000611506034050400f1200102201c0880c0e0128028680c125400c074009203000d0090b0407024a44540c43c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 831407464 1250 831406214 831406223
    0x1a0409091e03081801020a0816020a0b0a020322020607141002040902130801090203030712021905030a0e01030e030904020315191d010f050d020d06391710030f 70
    0x1d00601000c1ca1050340c00c11245104d44008510300b001025010708040b400a002d03a050800d00304120381c1007031003400011155644903949c01c1d598240301901801941049072024400c2400b400c80b40210440301c0c2210120796000340c0118941a441d485e07544505000301e42202591040403160302440741d092000b40010044c2c04401601d844801516890000d806e80c000c0001e61705140d202c07409a50b0100459040d035034420300002e41d51507010300581c2440501031683c5001070585a03d001441700201c0123000400c0d080d07440b405144c3d0ba590044d03044912032512100c16500520a254550800d940290703044401c40e88018843d003040c8002850050480d9246401501010700800c4842511a50342d114107000e940d040d1203960404011180201d41e41c40f0b0b00c0d10603c083e40307601040d9141c0112130038419811940034024160761118150303021081d01d204c040f0005c084a440414042a030401d0724195001d903981c4208400010008060484043c1c0b440f89545455100000003038213414402820700c0c0705 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 831408714 1250 831407464 831407477
    0xd080f1b03090115050415180905190515090706031a0a0f060f17040b041a041b0801020301150302090a0b07030215010e0610140c060c131a0409091e03 66
    0x2480100b400c024215405680607508080c020300780904103601e00347c01d565010342c0d00944050903220b1a8040c0c00f1140b40a400b60044941c61201a60004005500075000302c00300c0d1070706000b041d4080c2c14104100c0d200d400d0343e04503c10a010080c03203038000e640084080c3e5a149070200040d400101100d0f8140d201c8d20420070031710020090950070400c0c03984456074505020000e0800b081c0901c48900009000400841040b00000c040140a188541400d0644484044203242503e00160a80e5000c203460290035801200081c0103041402124140d6030720381e220a01103804840c00f50041c0d000390340c080d0340c030502e580c6002c80c0c4c0f6840c1c040030340b5038540030341d009012201c034010004031107a0060304603020803000d00742041038684491350400305249541c9003000402035444d074000702d607005d80d43c40792509000d04000d022a0504c0c002c09409114011303040c1c001619031314403844502c0c800c200440780340801c080c4030400c0b2182881c0d00140d00319000d00c8241c05106006102d00d02c9010401c10704a02080c103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 831409964 1250 831408714 831408731
    0x1060206091c0c0c03061a041b0e040c14070b22030813140f100c020715050a03150e0a0e0601050325050402030f16020d080f1b030901 59
    0x904224040d0401c41c0707000a002048804514000d02c510184148010310010600020802c0106030f4540700a42d00100c0c02c1100000b81351035040ca10907038821799031045090039840c01c44029410009108a041503c075a1001c01248007480040e10070100c0620038480303084041c0480044c010002c0050034401e640c0e40d041482d2900c1c542c8025042d0800120591000310300320701c00070b0f8001c1043d5402c12400010240341e52914130b46440c0380780c0c403074074004541c2c0144a242801d81500090340d813a809000074091041001c000342c22a542c2c2d00701d10920440d00440c0e420714582900800040403210300710716003c141101c450080c020484003c0d0300008101607030004100c0c00749040d00c22955024800b070050809545403800182c2d488c1d03d0b4620140c6082801011180c1c2404051074a00007800098010b64a9107800e001e80d80f15010125508170303d4454100c4480804e0b44082003403100600680c4580da0346413102481118080e50081032001d20350300c20400c0d96501004540554490114138001240300d5a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 831411214 1250 831409964 831409967
    0x30c0a03110f0303070f0e2103070b01050405150d03050d1b17090304092307030c09090204080303010311030f0f070503071703220e07030203151804060b0d1a0106 71
    0x202d4640544445400074001d0002a0340d024000b0910180c0c14a040c44440d4407080000b00240da12000703420200e0b685088041c1518404005001d2240c0500c0405902c0d81e80c0380140f0044d42c60440b441c0c00c4a102a0052100c03d16240008552b0f071802807808500303010072151000215190240c0c2442c80140d1824030b10307002c690020818510f42c000920990a5050140c200356503030040d4080e010a0302e840d25400c8541100014080e20401540c0d020265071f42804800903005141d261074031000a10124804103d0030713003500844e41103070140c41c019840c41e8655140c000c04010b90741600d0350f0602a00b030075500e0388034040000c44005000704001c0c1410138a0541054508881070307000e09205014000f18a8141c000401596101c0e10f0701810703080c6284000c02d42d41d64411140d080b00c0e080c03050b480203101d00658581c1c090b5100349507410400602d0301e56041008590364141071070f4580119894000307000200320b41c10204a900c07000c2e118001001c4540c1c0c641d007108035024003940080c81c2400040141d10b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 831412464 1250 831411214 831411223
    0xa150f2c0f01180b0a1401260702070f0803180a091e0f2a02240403020c0103110a0c021c0809040c080415090512040305010b040b09060a120203030c0a0311 68
    0x26008070410080b401c0c00e01195217016148034101c0c41500b0004900e42ea039020f42005c208001440b440c0320b005a600f4050807030b11403001d4400000522403280045082405d92291005985c20b1000a60400480c0950341d0045011002d01c5038000c00c1281c07000035815018000e1220302001c1c00c002c940740007100944581194aa540201c000c40d040c00113482020180005200303400c14965241c200f8210f403804103901d04001200e103a4542c482c1c003450b03c00c16600b01304200d40158401d50940b1809180600114152803110031844201c680411142460a000350074035041e00d840900543c445010b40070b10410a005003c0c02515180d800180701080303490640700c2c0390030280391820400c0c01800c10307880700e030003035000701409841c580e503039050010520130104049040d02a244280542e03458603460171501038584c04601c0ca00681c103006680c4440e14060701094441c0b030000e440e4500040c40c2c00c140c4030821001000590301400100441180b5140501c41407800502903100c075900c40e0084800706181 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 831413714 1250 831412464 831412499
    0x1403041203020129100e0f0a06081b040303050a0c032109061d030403021e04050c07060e0c010e0103020711060307080f0108010c08070e011709060a150f2c0f01 70
    0x5101007652008a0743d4001c01201c14000c107103804c02100003a030303007c10520003401810640c8003240000000d1011761004032a80300b80c0300f1200c0114950049984031041c6d0045000040101d401800b40d2038009101c2d40325010003a000345003044258040507603903d031014142210000b0161150f40e940c1c1845054003900e090764542241501005102c01e010796185c1c06a0700009205807014015540000d5600b80008105c5000410400003800c14140540040e4001c40b0111909414150040245a8080344903c5880010384a01c20004c0140c0e0045000b503003d00342c2203e06240c0d000741e0000756203940c0d01440c0305441c06d03101c01707038142448030840340c084d10305902101c01c5078140600c03103115590181078aa007052060070b00c10054007c6000603542001001c0710244200e0003c001c1100c81c140028010b4042c90000c031003045550902e62000d07101d400c50b8000e0202507500410104001380601c1048280410020007007018200306603205202d20400340e030802e804818841c0140484005c40c22144003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 831414964 1250 831413714 831413771
    0x50309010b03070f0302010309020111060c070b25120207150f1104030c0e061c06050613230a150b1305040605011d061c021206010903030c14030412030201 68
    0x102a02e0241130000c440d02c1c0e0700000341056240c002520071640903e086104101d4150203503411841c20010041c0c994000f54000d031071510200d03010518000c200150301a1102e4460402802c3e03030010002520784507d40385002686a03820485400401d81c291000c0c51b00b00e805c40800b1690700d403080c00741003e48000040034801c03507104010401c002181d2003021001c4450303075040010705035121000070380124143c2c07900802c1e0b16420891102040b81315486079101e05400c03150840d011016220301002c03210b5942006080c5802404a03c40711400c00c1c034041e90280280c400411300140c40112070110841c42d40c0806d510706008140301c680081c0c01041e20010f00000d46041044e0f61521000800c3c140398200d150302da0102000080303805803201d4040342c0c0d5034241c0d000420801342c0100c8586000b9400b501c0740d006580303c1880032403441c2d8440c50b62601143e4060759244100d00c0e451b00c0e121008480e02551507090301c41040b000501d41902032010541c14069000080c075200c1d010941030310410101a40311 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 831416214 1250 831414964 831414973
    0x230a0b070f1d0d06060602030a09090612020103091412030703141b0a021527010506010816090510090608070201090201090909021903110a0e040302150402130903050309010b03 77
    0x4502075002c410800e5620388821400640401c0c0c070040303018900720f100040d1032503080030004500540c00100070084116913503624a00741355204469400c4402500842d140e500058400401561207500f000d5515806005148403c0d00c08140355440d1507040800c1001003840842007110a070f8041c856503d1102d0040207002440c9841200150046030b40c80a00c0d42d03610b00400c2806400340b003001601d03a80345101d44209280d0924080e02c010340d01009020914030004019014284001801141e01940040c0c4610201e07450b202c00019516220564841c1004212100050380303503a00203d5404030000c03070304c83d00c4d80241481c00081c01d02c0c030b00820344401d41e81400720140041c0d9005c40e9220480c0c413009000120380b04948005200e442001200045400e1a00d402101f841070303e9159500c036032011102010f00c01e82c1d03a15518992042200d0141c056008220070140b40e0000c040500e5010b0f200801c6400c00040388400b000441d002c8100541c00528084208851401c00b48034128402c0400c40040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 831417464 1250 831416214 831416237
    0x80a1d0609060f0f090717011b05271e030f03040b0d0c0c05060610140403050d0801060f05091c050d0206040c0b04050310020c030c030c0d030c0c120c230a0b07 70
    0x5c07543e4440b07600c54032848906407a85a2003034982036001000d207071000e0b4004042c05000c20f00081c5942c000140603141c4240340c030f003000002801e82c03c804480000184c4076800d02d011800c41d5242040903048140e8050040ca41c200008001c10310040c000742c0f01103542d4503140d801020125040354020340040041c00001c14a010210750f00050140d8000c108407006504c0724160744040fa58000190780040c0c000102240110800c0000f18a03010190040c3d5915801d989e030350070046503120740400c44040400c80400281e00039007040c8801101c0d442c2e076400001c03144019952454580030380b901035400142c01c02d10034441004800900040203081c402005400c00781008000380d2140c80c0e80042a000a90004100c8070001040c02540c1c103a0754044156a1202450b0050a44401c440403c070130009142c58040d00607280904400760707100e41c00c014114901c0546200c1070750b581d04001d20549945044a0f640e045203040020440e821740d14080240807004041d1034a00b60007440580140107011016005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 831418714 1250 831417464 831417481
    0x70f0e1602100b0f0312071b05012a0f230c1003090f12051801020102030408040b03040201020703060f140906070503041b15210606080a1d0609060f0f 66
    0xd544201d10540c0300181c2441454001441c01100c0500c1039010700038111b0026404e15004045d040305030082401b00445101001100c1e11810300d80070340f0740803414004409003a100b140c084400c1407030580c8400071002a441c0c50300c6a0008006500b1a11103100400d1000512190740d02d106100b0140b600070141c0742d8810000030030741007a94542034100340d41c4016950901c00c070f0490381600141c00c1054002c40c5c8000c08030042059010000300343c020444d00d011b9904030751051003100d224641143d40141400e0508458000b59400034106a04600c162a000301c0070a4035481042d500512001e0700203005642030507020400180205038500070b8109400f0064226084800c8a034082d0b4841480c44002144468070b42400700365402c44490030507000390711078079140c01440c01003003102c0840c1c034000c0c040301141d034180540e0800c3c01150300243c4ca400c0403550300609130b0041020000300000107030400c2c0714890480c0ca00034080b60746010179030000c400c0c88020911105c84627040032941ca540906450211007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 831419964 1250 831418714 831418723
    0xe060f06120703060f020901090608010b0a0f02150106020f0f07031a1902070605010501270b0c0c1302040306060b12010303140702060c06060307080a0308011205070503070f0e1602 79
    0x220501619a00c2003016001e44148561009980e001104000484150f11000001d410600c141c1e40820f42c009804562113025401141c101c401c1c0d95405c40c541481c210048070401c006814190551041030490740d19440e22000d40c9000c0c1440364018400c0310004e41c845403a00012135070740410354001c003100f0b00110744001c402c1045000701d03140300359403a2103600d0031210414890b0f6240410f944080b80072400c002c426081181201e03400d90341c0c0c0031240c02c240d10606051f000c2c0500160f507a111400308200c0c041c00e020142401a88202c1900e16104074034002c9920b88141800b0044440d41c00141841003080c0341c881c000180040c1c0400350b0070940b0a07010a080d445040c0000703002e200050076400710003d42901199001a07001d410710392501da4001000c3d81c2c546040c2e40a0344240504200802c00b000c0001da140c505035019503d101d12a464884a00c502880b0b0b00c40503140c0303025038400800c450303c0c100301c4000100350400710030715441e1812510243c0312001809031100001c1000c8400e030400e50004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 831421214 1250 831419964 831419971
    0x5043b12041211010203131d0a050c07030f03060b0a050304060c03020a05070807020609040608010209150306182203080901150302060708130503010e030d140615030405120315040e060f 81
    0x43c50b819007140c030720006030702e503021304107000304c100e80c0b94503003c0f4010941208002d12101c01040c03000c41a21615018000e40d00225030b64804907005010740c0011a21500c0c8243e180d00b00c42c2000101c0d41d481e004242481e034458101071010a800205000070040144103070454070400c0d01c3c04508108045800509500c91000064240b0384085500f106550325002100c8144000400c2000a950b850031254080c0d0010b1113550302c82c10040d42454100280e42c41100d214240007424941d603405080381c15945c0b010082e15603a0380d11083c085800c0846080301c580660300d0f009880d0b91703119140c918425030a441c1c0c03901e50300340c120401c110b0400068489100352007901d94084002504d40070b003640308446003001c80d40640d03499030a18800c541ca82c0404002031131980d13081d003401d100c0080110482c01d03183c801652040e802c030202141000c103843c0440c0296070002c1c420026111140340c076100400184c0c2099419214507004013076802d000303242510907020170414420140207280b5007030406064032203008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 831422464 1250 831421214 831421223
    0x901090c02060402060c01020405060304060c020613030e101e030203100609030237171204050604060e1c050c09070c031205060d02040e070e09030c030405043b120412 73
    0x41120046c2c0d910a405039005068050010341d1203140c24185440036096840504015004031808101307028101ca407158803160709501d86c4a10401d1860500c1441580e100c800010040790a4404090240d4103103140381c045c032195000f580300d044c01d40761074402981a0b4429406c8c171148941c20001038403100752144450712416622802842e001700d00002c0590b1005103201c08140d02e81e8042947c480305000c191500000070121001124092040b0070184554016031354803403003c0c802000031034828203a511840c0030152000c10840d044078403002030401002c100310750079000180b0452460802144680d80505680b400a540d2050703034a01801d03010580f4400d4005980354000100292100320380200301c1c56018000700074007001540c0c5252100d025000740803440310504003086000c803001054900d5035403c0c07070207540707070910301802c11008141c8410701c5580b02c400408407441c0300110b2400f032030300c069003403480d03c4440800e002c5090a01c116000351403684541400700b80010b504041065000c1a40f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 831423714 1250 831422464 831422467
    0x15040c051f0507140a0c0e010503010207150515120105062b0609050f160f050301060e01090903091d0a4a0d02030c0d0807050307180b0301080c0901090c0206040206 72
    0x21424550400c200104c0388035803074855882c401c41081110483c40d001c07629240e10700080d03640c8600c105400e0348148a00540f07801200e111041e01c0f001642c1c4015042103205440c6440e49200c0c0b0301080f010b1044a050003c203075903540030800c83d42049018440320068000c10000b203405000c02c15000c1506403880500860781c0da517001c4080010402c0528422860441121148560061890038007010303030043c0a40004080400101410140038200c2617031a2201c4030a11a800c1825090048c190b808042d410454200070014a45c074403c0b0360b15100741002400c031021460420012011340340c407901c80d43c408a40100011000003484484d61601da4040d48201c4482402001c0000c18160700303040040c1c00b40588442100c4441d00000200782e0301006d60217803410504124003e440541e003c0b280c58020500410001c2c0a6074454581304842d0a240c0940201254407000344001c10b80090700310500c554045100030b60355252940308140148503203002403018006e030900094980102800c0280500b40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 831424964 1250 831423714 831423727
    0x40c0c03021b090c0c0a14030403020f180c0a021009141e0319021608010e060f07170a1407122703050a090e04110117090705130b0315040c051f05 64
    0xb4181b0a0f24402c540040d4071402144403488407035140d80c4284003c07845000710107000d404c5801c05202c8030001094101d282d4038076a40b98ad0305045a98082c1d588401180a013a2042290024503c5040307103c600803882800516101c41c071051400b0724540803850740710756440160344191000411501c400855030408a1840c8880c8000d0340742842c4c2d1000d1010200c041200481c3c04101544413484003400401100d045841d081c9026044c04801d65490001400c1540035803d40007401103080e4114076660350000c0c2840030a21141883c1f181602e07004000389840ca40000800000e0003080740108107140114001803001c2c0c4030b10b02081c40d20200609110006c40c3d19207880e401140d1070001041100020b0000c1e107032600d060721b280000500d5081c040740507d045c03588011449518203200300b440c50001d00b1298208010410b44038a0780f10500c0080351074100407907080d2014400c200314050450f0720b4210030704251030a41030350410364100900a40c0b5444c0400c0ca4038041646100b030000f030b2410700c2c3da551407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 831426214 1250 831424964 831424987
    0x15160c09021c0b061c05090616080609060f0d060b03070519180e06040303060509130308130222021b151f12051e19031d040c0c03021b090c 61
    0x10440103080e00a2942110786117840d031900401c0c4120700540590b2003a03a07071501a0f80c005804500c2c0000000c1c1e1290004007141440340001c0d80000000b84076410000c032040018020f8480000c04403140303034542176000b980c5e0808021910240004442403c0d002030b400c2e4031030b5515005442085403034003400d13050aa44004907800745280080d4082a41c0903403500c0d080190162405114840c015075180c800200c9a440c48580002c90a9166a4050881d12812a107010f801007940c01030368403562140000704c3e81b41012050002c0705054120141c1c032200600d80c2e07413465103884502c42d861034100100260494071007288040e4008001d4421040004101900b508005a0354101c004050808100c8209002001a01000c0b10034003001034250110003170b054944554010b01024041244410070b400028081c040e081d03100c421101c14607844410718070008050768495501000822a0708120009065050004900110070001c2201728409800c0c04030340c0c0d0380c0c4000c019406040c0041072950003103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 831427464 1250 831426214 831426217
    0xb0a05010c1e050111130b04050a0501050a1101061202030c03070b0f070f0602120402120a0c121b060903052b200607080a1d060f040215160c09021c0b06 67
    0x1c0c3e0890020851106214854601e903800200414980c0200720400160f046010003110142d81002d00724010162a120040d140c5400c04038511061100f025030029904409120745c1c0000d10348003a10480300740050042c0340c14108848260341c02a04a04c205105050120085984078212181416650b241e9828203928401070000000c100500024019080c021190070950103140210b030b002c420411419040d030341d00d6410030402422850106010003100951400400f1900e0144041206200407012058030a6280ea08450301099610784148140807040000380c4080354804907546013482c414420411b43c91711442060100015481a5642c0413181d122504460f00c880c0102d580c3c9044c14040601020b000b190615035403880c2449080c1990351012141030f6100d030b04000741481d40c40707407640640040c0000300283e8000b4404841c00f00e01d2611100200300d801002c17070418070140360368a010130086d401c40e8170038001d4900602001c400800d0540300f490321078902030780c001644000d0a0200f5410f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 831428714 1250 831427464 831427523
    0x1060f060809070611070f08060f060409020f1e0402040f06031104080a021012021303110d02090c0d060506070b092a121f0b0301060f0e0c09041d030d0b0a05010c 71
    0x50305071f40760004150800180c00b901138420b6540c00c001039596a81440100e50001602940c013550446001031507083c60a1a01540141130310425000031600c0003083c2664080c0c1d0103007008110780401002480c0c0d040c402c5044002c00440200d217094070300406980d8502200b40c02a2043d425483c0350028103003d60400500c00080d40002c1d51100e2503030450b100c400e0035a20007580da48500d408049007903d8140c02c1a40d00d203900a044503415181c80d2400b00b12500701110b5076400d10740ea0800400e5556a0300c01520420b44103203c2c070426440d0841c5182d040c19540c030004559044d1a41e841c0b03407001c550441311081c009041d0380c3c1000c04400038615a103400c4403100388000e0003600381410321301c403107445d0040410900154020700c002030f41d070480b50209040a10880c0d00040c01407012a11051000c0b00600c007002005001140c4c103640030625080c1c410780360240350865480091a1010441d15010f002100c0004543c900f04c4945024006040800c81c80740c001c00034617a62012200d11001611061031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 831429964 1250 831428714 831428729
    0xc0307270e0c0a08010b18101e050a031b05030a03050a1d092a0c0703030518060a05070b150306060402070609051507080f04080a03052701060f06080907061107 70
    0x1c03ca42d40b61125030003452200d051038003034102000b1105071400b41d90304050081d400d00400c075014510380702e8113400031182850f0034000d051b500817000a4a1f0346601090010314003030141c0030000f03007481c40d100300141d841d9032090303010740c021038400303030119810000ba116040ba9600b40381540c00c080044009540000760240b503401040780d4140441c0d20200c1207a400603881d01000b241120b10044800340710703070207040e650004a900414080c00044e1203034000d03006035101c1402100040304071000003001030300064112000100081014000c0c44600034070240c00c042ca10f642c41580c1000c40011030340f6420700608007800707107400003000c3d07007000b0080c1e010b40141600101910803090699400215481d82a20340d80000350085c004102004402c40485000e190f018110b0740c98914a0001a0003034071004140013031000a01d40040200c0466000080c80090000000a12182030070a00400b0324560b0304000f007005a01820058603950002c1c442098a0384c40c10904410120b2581e050306e4100190450385 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 831431214 1250 831429964 831429979
    0x120f05011401020c0d0203190305040e090109034d1e01050f09150c1204120305150121020405030f03070b15031507031d0c0307270e0c 59
    0x7a10400c02007110401e038000340e081e5039040e02d030703101003100054070017001a42c1500280d00481e242e1842203405041ca9100b4180b413030a103540c800c02e40758880400c6406071210b0b5100d00b002010181c0c01210641d01c1d042091002c113602074206a41c140440c050191032211103504969802c005008040c510355040e2480102c80840c051b10841c001c51180303070304c061201982000d0100700407562004000b44140030b0180280780d68891031500043c0f90300003a0082d010620200007040c07500c240702031841c1c4254000c10166801140022000382200d600130004941c00307a40e805c102e015a81d11503102c540180501441d03250b1804101020f500130f102d0703688113603031620070800100c40d120401720103450014012814252a90b0300e0031400460f0032010b5881642c1034001105518a00500d004002d800c40d4981c500000c0400c06602c1c0e41107454108813103500c1c01e40c401803c0c5d02c054901040310002801c60090a05400c0d004400c49400d4076481c00940a080c94442d105011140d5040154201e060401069203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 831432464 1250 831431214 831431219
    0x20f0a091403071505090f0409290106020c0f0a0506030f01230603061014031003210e06070515041406060d0b060d08070204090303021c1803120f0501 66
    0x240c0356201a209101040a025403100820300d03011030140b00b110409090304003c007804160882c0d15600541006511070041003820380b080e211881840c020600c10345480c001e2000c04104d65808180040c0b50075080504800148070880c0e0100398684070310010380d020643d1103405c4000648031031103a00225003008001c0100180301c002507401504903904e4840c0c02c04400d4250304046660030b10000d03c607400402c10008036219040c2120400e210380c83c90301d4003004049100e80070050541c01075800b5142c03466050001d006101d00d06550404062503002c00c1c51a04138105d1006d40480c0701749200750f1184101060010030302100340141804902c2214271400300345003a01c0d095008030071000500c0d00320b02c111000a03180303042400001c2203403508101400245d640340c40800092115060045504010a010b1240103859034001c440c2802e00c25200542c03184140d00020108640803c0d550350020309102800b2a03402c41444615511909441c1602c0881c801a00c1c01d4080c3c5501401d848070145041c000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 831433714 1250 831432464 831432467
    0x301111612020105360703030203090f01081909080415021f05151302042402010c0801180c0302270306011706060607020f03060a06140a14090a020f0a 66
    0x84480d40c600c9600010300c0d039945032000301c2c203d583c100c07034070000041c04000075042120034034103164400b0f82d03000c40c00894400c00c11101c0c0c1840100d5000b140903074030200300c5240c5407521504a40e03240500b0301c1e00030000d180c540c0c1c40d0341c1d00190560440c00c2090b6681004014031104004480181c02d0905440e00d151101c002c2c003c0d5602d40c4901034180c564289031004c01c2059150003894003e00100364100901e00c212402c20080b1040149052034031035081000140c00c0414620481c000e01004a8850702054950000390035a09001d1400e01081214001404691030304154021450720b840d50008183c00c1424081d00280308a0703c1d00103281c08944101c0003180d40c11320001c130341100140c042e1109a42d840d80d8031102c4040114828003036401ca980000d83c0341c20a4005404000e00042c4030314180d449400220b400c20400381c80707201c285a00c4000602012114090580c5019000c0c5ca41e0440780e031030070700540403100000a01d03c2c0304240b881c0c046031200034250140e40f40c080c042110b066503055060740 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 831434964 1250 831433714 831433747
    0x30609030a03060b0a020c01200a060e06010509040317280516031b030e030915040303080903072a1a120901140610090e13210914030111 60
    0x1c03040000d0601030046620740c81c01c401c0d2080200c0035002010380300c0c1800010f48081c1c40904030f40407540100404402e4a00040041c24001801140002a422206001c0d1030400605800141c02241c031a024000040d5115400c00b65101761080050401c2d100da80020a030014a003c000010b041d441d49d203884140322039840940581410709001c0030a07207811005038280c448159810401003d4000380c243c0040c06900184c041902000640e0300d410040b4002071440d030b0040050044401c0302103424030405030031140c00382e005000500214281003e41e81c500c10038241241c0c40c19560303585101001c407121803d042041c00f40600c600b0503070300712000610292068003d0952045191a0364020a9040c0c40610a4030000c0d5102004524a981e8940900101011441107902000004900011102c90000300e05000780340500072000d1014081c00c103804c10780c90005408104140201c2ea00e00d00541142150044550014003400e280200d600001d0061207200046914030781c0014031301209043c0007a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 831436214 1250 831434964 831434977
    0x10b04020a0518030a150e0118030c021201020f07020402070519050606150405150f0f0720010e030a14010221010501111b19080a0f020a12030909020f0903060903 71
    0x10283d800c10310700408065a400b809000504480300040ea0b460b41e01015410804c04200541b0010403081100c8200c01c10f0040307400780a0f0700194806000000b185484020010901c2e40d000c000d5003810840080701c0a944201c00e00248141d0707001454404000f4140101541d0202c401072000401c80ca60900300d4407120201c03a401d03c640c103016443c09c3c0f40b0141c072050740d0543d41c01070150114000740f100241d00c0f41c1e0020002c5580c2eaa0306111480728040c4130001890100d219008000e242607141d00115002c60090104e80d05120103207540d00705548000a00c90310858004822019510511030340900900c9100a44640080e4020501104607400d078503031412500300780c0c0e174448100d03295104540c0b070708000710000300307a80d1000c2c05922680c98034007044003541019402d00c2d0441030782d900446240c00540d00c42141c4440110380c0340d00940c078010f80207800403c551001c0382048152540c00425030084d60186071a0a80e0101c2d84000342c20209c015900611006011507806080000010f940c980002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 831437464 1250 831436214 831436237
    0x91b0e010801060b070f060915020d0b040b060a030504030e04020412020f180a050606040b070605070e01050a020a170c06010e1501030204050d0206030a1401090f1506020c060309010b04020a05 84
    0x1400005074048051081c0f100719904204001e0900843e5039480c00807403200502504c0c2c035a00d40c8007440c042105102da120b0314402d406030060741c80c2ca002410340b00380c0303d045200d03604c940d00e03148001c07070399451f003004448098500f8900050540d40310714059840c1c1c2c900c0070403560054408100443c0f128540c513002003100340203c078102070080c880e00c10014008080529018031414030320203d51400115000300e034000348000d0030702d0308184e1205d00c10816600f00d13030f40603586907031145c0a111002e900006150111142880d14524001714071401035610095844010100201607810101e018560307401e460410704804281c46855a542080140c1c0040036150424502d0080940f460198000e1088030100c40014200e00d1821203036400304401230300020107041c2c8507134071002030300000450702015602815400c00e00186000820305903000703c40c841c04896050440d074100a04c4415000034243c1d5826104030f8090342d480e9207244c0d095000d01030804a098200d400810819151608030700a020007001a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 831438714 1250 831437464 831437489
    0x10902181c080d0b09040606060305090f0d051305181009021e1809042a03110904030c0602210f24040603021207050a080f07050112091b 60
    0x40008001c210050821124100038644400800180400b00070703003070710544001c1c0028030500e110049442c80c003003103508940d003aa0f9850140040b03070b00b43c416583c2104204004101c0d0980b94116a907882c0000e030b019005000011070344146401d44031400d90701500c00039040e400065443c907000048500700362071031300301ca080014010501d94458400e13218041c0d000b00685d81e50400740030000640703920404041c2c55030150a03c8020303164486030078140c00381d80304040f098000301d4584c0003422510810f10400080d2800b2010800214110070000c0c072a460048444444a0701c0e41c1c9010303615505035600060241d400440c0b400d045200100e200c65128001842d000681c0c3d03150080508162421107440748085a540240b0802d16030860800150740c0700035000141c0726881e9000540d02c0b00d410204400a5846108103106030b04080690314020030180c0000c0180711b4803040c40340e031611058041c013810008110300d0001105900e030000100756400c60400d42100c2d0111850060300d03900f500504654000703 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 831439964 1250 831438714 831438757
    0x2033108100e2a0d0327050406120c03321b010507030c0b04020a050d060e1606200106030b011403070f0803070303020f12011e090c0903080a02070806010902 69
    0x4581d40101284904050340e10559030403c4200041e04600307030320a5040100c8900d0300380e2000c5a000c000e62019040002042c0070a00d000c0c10413040c0c400f42d807c0401c00c84041c0c01c5070000540c7c609480c10a80ea0b201500c408450100246081a440b400b080460389010344c1c0c1084041440102d5019200d41d000a1464480b603e8600151550303c01c2000080006042d1f0243d240401c03039403401180c1181c07009006520f002d5031800045c500701d141c0340c81075400d20fa49428131b00218404002070000d604103607559a512a140c460050520404103c60780703040351900881041d0341900b0742c07102024640c401c6140b45a940c488420324188200907060600a129402d00410781e800e290307203a0800c9801c1034004510b08109035404030040c1d007001c20035150540e0180071540010058400340c0b40646003800000841040d0380e041040e54a01030b6000c80030503445c2070a0043c450b82e000d0004000c4e0ba8014280c290380d100c0c1c0420807890100d40d5072040a80740100d0b80041006102900180098200390400050a54 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 831441214 1250 831439964 831439993
    0x5060c1201061718100e031c050114121c0306061704230f0a0f021311070303110705330606030105041508030d05010e0702033108100e 59
    0x704400080c242090050000350003c10380004c0701c042c0c0e81c1c041059801c594401d650070800d4031103240a11036170360804500c014110003000e00741c40c00640718030070034000c9525161204072194001c207809402840c02503050a010742c420801c0c1039180c80b01848004686150301d000500070281c5008440001e401f981c61884402e6600c1009806160064000e01c61024041c21491450030301d03c0d00c07444a8010f540c07205944500c10310502041a014031120107496031203204001e424011a00802d015500d4000f01402c111140b030161041039a02d400c000601c6070030385091441034018210b0040951007202640d42000d44466014000914000700c0c11411814104002070154809c561003a000001400100603131724050308801e83c24400c108428140580714103041313044d644104003024405444100420880d0001c600091740321186101650403c4120f81c1d0540801d4400c51387c00914209042400f00c090100c050008010186e44084071000030314100701002410200107010f4503805844450b04405 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 831442464 1250 831441214 831441227
    0x60e01051c05220f0b2d100b0d0b030c010f0504180605030d021015050f060d0e060c0a02070605070b060f0402090a03032a050601121b030f12020c0d0b09010905060c120106 75
    0x108405c3c4201101001040100e13401c81b000280070b001440036180000504075100310007080c25541481d80401d40e032010f0001d15162005800025040000c0041d105c0c40c0140c0c060241d40c145c030091007104444050362240e1002401c0f0755004550705018103001010480e400090032054901070301010f00c0440c2c0400303000302a1607414072030381790411000c44042c00940b410800902c3d0180100c14001000700c00031110300c3c9002411100a06c4016002820317200c0540c04010a5008000d80e1420321301c1c0117010b59842803103410140076140500c41d0280c200510340d40340d4040e078003451400b82c5000d2019035203050003056614460f84200d031165003181440040030030100c05014558000009141d541d10f00f22020499501b480740030707a40076040c4d10740c20580001d10381c1c003e4002c42c0182d00c0d040910711a402d068610071480660b91003558003088003151251140da40c00c40a1b1a00152a042c0b141c0e500300354a405030850170001001d9000b00c02c10491110950720203445401150084c0346803981c1c9a0701c0541e00d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 831443714 1250 831442464 831442501
    0x30c06090d022202130807080a1a06030a060f0212060a1a0d15030803010302090a0606020607030209011209030302040e0f01050f060706180c060e01051c05220f0b 71
    0xa07503451260015040501d0600501e49460310890844000d92818201300d070456008261800701d26041040f12020400101010b0700110300600b0740020580d4407610012181c011081605804000240c4503a030107010750002d16810031014411034000b0b0308020025404041c030384500001c0007000c1251401c060701c14400b80c07840d403d00011b101001190700f00300354100301909030120b030b110042c02040c500441403042c010751140102580340d50440c410070208020080c484406d0070300c0c0c03190030400964006000303504000d141c107006039690038620040302c12255841011044909000f5100c080541c198018011506400301880064035100e9010036585400c0c810350742d200000c4402c403410ba280c030500a1021920a00c000142c040c4003581892044201c0d8071306072641801c29800700451500140e20806900003403070041c0ca404018000c1d4142c0075680c440c041e6030b030340d501c00c0015600d002e1140c1590b0726065070401d000e10064140b800c00d5140c80306000465089515501140c915004034070140f48 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 831444964 1250 831443714 831443719
    0x7030e3a0c1106091306090b13020a2a0c0b040f0e01030804030b1e1501081e010306021b0307050d0311120a09050304180603211d030109081602030c0609 67
    0x20300c0c010b5101005080d03040003090701e51040300340c1d113103404621052007264010014014042a401d1102c2d0400086442c82484214003500402c032080d083c0368000601c2c1c402010500c80b0900b01d41500d15a0784064008180003440410740d0300020400c482034002800807200346464041400e0f4403681d03d0342092400b880000c120740301c284400e100280307016103a50380c41900003c070400900e000c501803044085099800305000340d05600e1f910100e5034003102c401d9028100c600884003c030303d03070040750f08401e4051001030006a4003088a000c400c0581c1d13160b9402404400c00c40b5100c2c006420300544901c0003001d0900400e20700341c3c00c0c2617036089140c1580c030b400005401e00d114560b240c005000140400c46c500702c1e0700c0d00003000089400501008510600c01d1000c0c0c000620318107602d080740123094548446900061230158440c01c441e0300c1000d540d81005004640000d100018001c24050005d24400401e41c07840818001c00b003291204641502c0c6008a08036500340004405100462280c1403410340c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 831446214 1250 831444964 831444983
    0x50612070e01090c1e0e12010b0f06090a1e0f0f0501082e06050c0f03040312230708030f070c05070902070f15020a02150f07030e3a0c 59
    0xc80c00d82c1903400300380d0001d685e0a10304020002440f16a4000844071016000301e640e1300e0003da610b083c50003c0c041268015002000354800c20380000d6114ae43d40d0a503140b050350300080b88034140d20780c0500c000007001d0010080c00805030101000c000c0201a0045801004e600d00001400701c010303250500841c1c2e0103071a10080d945031440303074045203040083c4030702d00c0804106080c44446510340701a0014002565001d0315541c1c60510241000780b4400300f0f1034154024171090020980c1000603d25100301e40c10964120030591102c01044910101603038840d180216111040c044400002c6128034010078407001c0555031030a00380d403c89043c800c00340c401e40c407203c428010b40302c0c903500900c6180d0140d9070007818410303569950890200b0303610302c000a5036004142560794a40401a5210004100c95841100c0c90301e0b910000100c0b1004080c41c040645802061400c200306001c2d00344140821558100c100380112089090080c412030141c203c1980030b011640d646108002c50000d07903902c4061003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 831447464 1250 831446214 831446219
    0x20d08030c071b060905012c12060406090b01080f0a060e031605010903020c0a121212141501170f0709050a080706081308090103050c0f0d050612070e01 67
    0x4015410007840303101004820062000451183d00d80d4800220103e66180c0281d42444401440700b000b960001d8180888410000c50f284040c03031400c01e00380480129003002e5404c140004d2103030400084460380b2806030340180001c0c460a50003d0500601800b001d00c01c40c0d03a569001a0b480322a540c41c035000c7d4003d80f41200001f1541c4d000442d1041c8580c0c201c1e810081e00303107280210102001030448891390b441440008040d0180101d41c2e001c0400c45040d942035140441004c1040801c0100411441c83c5a0708900428083d0342c1d080d9035040015820410a540c2c0412141d0007042640c00d4216141d455403e000c00d503224255000c110b0102d04201c1d0019250314103074a040b0040a44420103001c440b18002c00d00d40c0350401d0380c1d001085000c1c001c103501031502c10060890500500401c1c440416443d6102c0410001d0045a103024020300c0d0014540c0d031022800c8031603004661042c200940009400c45864031940c10141c0603a8044a641c288101d20030701503699140903110300b98551810030b004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 831448714 1250 831447464 831447473
    0x3172508090a060e120309030a12030f050a1a030606010203090f0d0b07020a0303060f030f141e0307050f3702060a050a02010c03270204021303050a03021009020d 71
    0x82082988103800081c1020980c40c0050421036094000c1c10010320081c5200c1560f00c0c0c04000e88280100c10340207589422060004251288540240907003d81c005801906600c0d110f80d00046500926100c2084541050a580382c09030884c0e9a4640000b6006c4100802e28a40802c03028064541600154174043e074510030b02403002e906241d42903000b44e01c0700614000c20b40100100c1d10038441076018150004152501a0488900d500545003407103000000b4800202c5044070344441340d0b0400d00510300300d5001e040442c580200c00b03280b11400841c0209443d0f16820000141c800c043c423500a41c1e00d0802c03000d4003241d443c800c162500320112a0101a0a41a001c61041040c4968904901c0c00c0a40c955004a6840c0d4000c403c0c04001034030002e002482076a080c401e000c00070b812482c0910450104138070f182240c0d80a50340b4140c12500804040e41150384d194100c03641c40108001d82c100090b80c6c0c0c14401c1d1103143c0d000d0142c0c05800362074800c0460768064070a1041c5aa0b005000107003000301902c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 831449964 1250 831448714 831448777
    0x3040804030629010e010f0e0a090c030b4e1c0e03060c040e06060705010c0c020418030909020a0315030b01050405010608040c03080a12050a0515030d0813020402070f05070317 77
    0x45503908242001008122b0a4041c021240308410360f0b1004200b5800798801d0004c14282261a2900f80001c500d0500d54000004500701e880a080f0449142200310700300c1d0002403c860948580320392003180303103001000e241e40713120506a80540c0c454103c4c100806080c55203403202112840f8140700304100900c8034078039a01c40c003a0000700c0609828140f104961310a070031070fa0440001130114449000c480c04515050092841d40400030440800d501202c4c0e9014100903c03d0099a1050343c02085200d2124803d40c04291040d40c020345200c8526520708160020310800c1c09520700803800c01c030011500d64029410b45014640c003110400c0c11030302d103032621100e5030004035100041104501005500c7c1d9051b004207406107280540c00500d600b40b07607440d81804150902c450780a074204144900003031b50400ca60580c0141a0429022508001d1002074002c0c4a1240000c1038109405403000a1241c0010504d0503a442190245000b001c80740c2010a0b0380031b0901c100942c56004005199007415068 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 831451214 1250 831449964 831449987
    0x2c01020a021e03090928090305070b07110703140705060901021b1c1202010e1c0c080c0a0b18163f29010b03040804030629010e010f 58
    0x1a03c4c14103c83c44c000803400300081c1c5664440c401580b90208040301e04500c00308001d961400e040142c2c8500f95000351960280c0c000290003284000005100240540002c13109860a0b0090f42c035000d0700c0340b80401c8400d845604264607071042d80d00205880c01d03c9000c03600503900c142c000b803a0680743c8a0a0000540465a41a400001c40040c8190342c0c65444451514103201e1100840c03d070358010300090071104000030f50b450541c403840400c071103030f0421207190200003400d140079071103481c003030911300214412840c803202c051050560040a10040f00c124501400d08000c0381046000300011303580c0e0701d140b040d0310900da0031114881001448552480da1003c0884000211416200c60b40c0d0b41008404002810380d94107442c144200070440c80d40c1d4192143d02030321000c00b0800c0c415480c0b007900d524050044225080001020906101c0400107940086500c4101031001090084004005414402240080000c0c84001139030350742c040c0c144546ca00ba01a507841091418241d001c454903001107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 831452464 1250 831451214 831451273
    0x60f030c0d050406061806210311030307020703051c140306030109020d050318060c070306020901271a030403080a0c03140c0301050f0603010e0103081c2c01020a02 72
    0x4108001e9014100e0290714030860107a60b002407154608610921b00400818100e0030310b614015081c0915400010312800103052034824440c19a4240303010784800e10000f07401d02140c40044100800560300017031190989100e80191409054803614007000030840340e8401d0003095944442e01c01307680d03000026541c840700060010078825225001b0541461011009a0b45900b0000701080c0000042010030030048003515058a01107140110544846042c003009202c1c50b0001400e8003d0781c0709825290f0081c10300e10001c240c001d00859482034510281c0703d1400b48840b442403041100c841101900d109541603207488003140d81e4200080000d1841600c01410705076103901c0440102741640c01da0348901d01c0841401c0c0c2e40d504250800c000042c07281555481391901b000107000c0c8040403020541142d90041d00c654560b8007000921200f141c030b4485241d83c203803a10310fa840c0003030100e03030601003801f41c10b20307000b404405003581403402e030310920b404840981e01a00d80c030f0090110003135080c1980c0c03001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 831453714 1250 831452464 831452467
    0x31006051c120e0d0f051b030a03020a150b090112060b0411070204151517130f06020a030908031509061c0308040f060203070206070f09060c020112090c081b030705060f030c 76
    0x10f17a01c101c0002c0a40b5030075101a40f0604803107a100381b8000030381185030002c40003408403408540c1c0081d0f4440e2280d00091810610408030f01510340c494018641ca1a401013100c2e44540e101e00d4209101d0411400c20765880d414403034210040d040500c034640c1c0c140d100c41061481c044068003403101400c00540485036502074600c000406402c5100b040c1324070625039a404840d0050140304040050020b400302c181c0c000901c86000c00114911007008185a10820150312034206080680040c1220440079003100d10002c00c0107282100c1c10071203003508a0840742d034086134450300240031421860000031581012420341103c080b0380101c034810b900a2052007036603c12000740e81c03401c050760429544000075901142c14010625085032045080d1007107454400d4810b458004010311800591788040d051000e05e07082402515201c1d0402c960b0150003c0482002503910708010341d4990291440d00c204501c0c0c4603042d09140707808a090003c8410040c009402d10020302c1d500380d011313480a40521600c0c0e40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 831454964 1250 831453714 831453739
    0x30a09050a140c090610021e030f130503010f0516140c01022a1b0103020c030c0a08030601301d0a080318061017010b031006051c120e 59
    0x20340005000d41c400c0b4041c05007840245041c1440580b03030001e02894411101c560490351500e60014801800c003462443e11400c0000c1d403481c05007184614842c51070103901c0000c041c1c440d1540c0748100c5048840540c002c10958905c03a4006045070000e8481004494513a0f681c041c10610403264540007034190f041c031b1854454400106400c85c2d02a00d080217440292800b80e00d16000000c0f040c249010900340600a96104d001c5421a000402c8102d41d050550115a401d0750403001c00589000304d0112080320401022428001d803150011a000c6000612000c441b41d03e43c1d513251002400c017103003101144114003d5221402c060003140c402c21106441141d02c014107184100300c42d440d05070080c1d81880e80c0742803035420302e0000d04080340850b0441d803201c070030b000030001c0036403c175404c035041810000c46240003103d442e4003401045074a65814810020503640340d00d0f09070b1140045031811a281c0c3e1000190b01d43e08083c1c4216400040c0140c0055680492654050100560244c40c000c0c4283c03214403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 831456214 1250 831454964 831454973
    0x90a02010815060d0507020706080f0f130b0403020708010608030c06160e0603070507030807050405030c010c3e010201090c1a0702181801052e1212080705040b030a09050a 75
    0x8104003285944c40d601c650a00000e40d40620145000d0107403403515820717510301070140000c4002c014050142c030a101c140080e24000343c080041d07002c150300600b00e611505150900954a100500640c5055460528002041c80001040700c00c89449800036004542d0752404040c01c009506010406000500c505030a4a42d20f140041d0300c10b0440307450f05070301c860807810000c280e0140180000f003402800c100c180110703500007901213031080003442c1c140c0d2081598517000300b0a2086003510003080d02914191828106658501c4041910a5841410f030302d45a030300481c00d0710342c04a0050310008210700c0a2100f0a840c001c0c41e9500140c03114010302d00640da80c0420b03460052800b0791003540502c1420b0110103070146510580b01e40d003420017404242044480e40601c840f1000d40207855198001c001c0750265a19407c500080001510007401707100b19042c5141c2c40c0f003810200400140b0b500c00058145801401070390141c9424140c40d9046907918001300f801000b1400e0162a14400e00c10440000f5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 831457464 1250 831456214 831456217
    0xb033312030403030311041d15090a1d01050f2e060503010302090a09170d15030503030105190b030103030e0d0b18071a090405101706070f0503090a0201081506 70
    0x3100180040d540c82d0314608005048131042803481c00301c0c1d05c0810003000119083c90350f1744c1d50306100e00041c45040d200c10480c85040d48a0200a9402140010401648000580c046070300e900e8071801e0b9510205801580030f08a8100f00e8201040d00b68240c0400c0440c14014004509001c0014540c00383d450040100800e00d20030790322010014400000510440c1014181940c11003581d10f41400084015038030240440300d80141a41d20074030114040041080d5a08100c801c050110080e000c00c07030700c134100f45449034824010301d8000c12400e1292541c0e001241c881c502140c441c1520301b41103901390f540440d0300045076245164406042209200410580c4159602a9464402252946144d01d0003103003000c0055020f01c4664400400601c00c0f41c43c0c0314120758120908481c0021140e80c1c00d521540980d42a41040b00b00f48400c40542800110028046000c1e0fa210345034044221110541241c41e03110071600240740c1d406c4880c0d42001540a4a100303904801001c01510340c0c2142c410115005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 831458714 1250 831457464 831457489
    0x32301090b060f03010b09042604090905060702211e1831020c03041a0a0206010504110a0c14030f04033c05101e060b0333 54
    0x7070540394024807406281c504150b118416060b0000c0c094a40c460340051031210000700040c04038445072801071700018249900e00e545541e80d205c407540b103503111501e000040044001c116001e110301c0d0007140b07225000150300400c0d500c0301040d1074191015a40ba0350f042ea04844400c400038081040391f4010700e040a809402c014410a00903614641e0481c10040c5d100100030b80940504000b41d80715405c86000317110320615981011015940c2e10300c02c10b8051544c45180c0c071400c90403541c061a81d040c3c001c402e0080815042c0c9500320b52103a620760003000200c031450000341b40d40302400c0019403072090044054242150080001c1e031280e011030014581198440c01030326810080003c1e0500800002101c3c18803c0300020344490030b4400d030303500c683c0f0041c1c41d142800002c22214105100801c4001c00180d114081c008a09000000031401c44032203260440c07640919960400c0760125881110700f0541f44512840c58100c20b1b81c03d46411440c40310034640c55070803002c440540c052005603d030038081119 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 831459964 1250 831458714 831458723
    0x42306010906360302031911040c090e060d050d0c0201180b0f0c030c15150d02031b01090305060423030a050d020a21050711150103230109 61
    0x14515040000400321401600700360103100745901400b4031451980b186008042c401c80c0000b80b81400d19048403180740700e582c40294144901040a0f2541581c0c02c0c3c0c5400d0b1780d03c541c100e1440c0340c00584c20402030307030b90026a0780f00048080c141000750402c101d0312b25801020103400321025500948a8505080d880c00b86240814103262100045580c03003112a14004005028240da503401d10040004600c130710341d0141803400380490355590400051040366025003890b0111900055500c5041c2940482114540c4a0207a01c1c00f9034510790030f20b07101240b501a40180640140102d40042c150408075003030341c0d64104040303c88007000103401040741c540118011442c210a00888a603641001c0700540c06010080d0010320514100316040020361b040814032500c05038541a040030308490101e2096182c5841d2044400c040b00d041015031301041c0185e901d6614018841c0048505071358801030343c4043c18001d2040401000031400e2030640840da425131202003d584c5640e040030742c0c00c0d00c803400d40554 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 831461214 1250 831459964 831460031
    0x9110d030801051903020a03230f0d0e0414040204110904050a091407080d080408090405040606090c180b0306041107111c03020a03030f0e1002120c0301030203030a050904 75
    0x88180780010007220b4284c2801140d038591401d560104500b018a44401012045104038070f074117011460901c2009103041e10201e071052050121007503920054070602002080f40b0745640503039801c003800b0b030703229101c403030280c040c1c43c0d40700c0e80e003803000918a01002c0958aa400d000d0f03604c0035501c90240d00c3c003403002d481c80821150300d0b600704003080c080504008031155001d400100320380c00020034a0742e081900c0c1c1c14882520342d518107103443c55101e405203150b4000e140400300404c02c81c1c00e40c0700e0b509030b440b01d103420042c040741c884003a00c6d401050400c458501048600412018800310000c690161006d4070203d03065a011b600641c2c981c001c584116044445490681828104401855900d00d039140d82010040e8032500c0c00794543c904084050201519060031f820311100075040805401c02d403004a90054400e101200c00a4019031000c2d0001c00580d008100c48120070400c4d0381c10f0743e40040156190400c1c080341951140d0015140076041502c813501680c030b40c00e4441d15202e11a10081c1101d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 831462464 1250 831461214 831461219
    0xb0f04090608010621031209050616092913240e0d0303020a0e19031509020f09040c0b1908072a0809030102030a060e090f1009110d030801 61
    0x150075122640c02c8008282e140c01001c1003002000848800c03961020030005107020400e007412a240c50480c1c8403e501c071400d00328060100000064000d1080c28150440134010109050850f00302845115050140c0c1d50710144000d080d00240c6010904910340c0203a170b150240d01d41c0d012400c0c0c8103030f82c0202c221416240b40008589942c032612000400e180c0313029544031080c4400900c80c03803900c0e5000313010541c3c00710340d50b01414003819200c01800350060009084801000e082401802c031800b04a440e201c0070050a52151094080c0c0448c05500418482c440e80528040c031251076001001611a10343c0782400140600072003000b03010070144103d540032603001c0c05501402898010301850f00300020b404503030f0507111943c0750130300c00300c00001c000d010400303100d003015180c40c094036020582c0f41d44008144001460b03a41c3c003490854540c003107005940d55443c031070540c444d90191480d07001a00121500c2200d0882d683c8101d1ba43c0c0d208000d030759015020100801d090107021071085001c1440480103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 831463714 1250 831462464 831462479
    0x9070519081b0a060519140c01050c0a02071a0403021216030302011a0906011706060d050c070309050d05071505070f03090302030615061c1d0606010e010309030f0e06040b0f04 77
    0x805481d80d424a2440d0110380e46540308011b03c076501c00410407030610301c400c0c5000c440d04115498080d12200030302c103038146407110004690000228101501c503142002902515122900c2c1070075100200c4141802c0c60b40d005e02c43c6044c40d00105906a000715100802240002e00c881c1d000b0f58029400001c4481564100c2082c00c9400100503104920900800480daa0f00289400d6140d20384261000d60b80c440c0000b094140c003540052902d076506003400c20200c0120000038081e918000c0d540d400000340c1e0750050054803201c6071005003d0360055034081c007103440220100035081d4020714045180103102c0e183c03204000e6034034504030000380038044200150f01e402c00c8510b400100f49040c80400f441381900281039031007034194984110300a0000c2c1c002c18500c80e40241e2000400035040c4d9844020650707800c2e21540c00f154090b01159640900307ca49510901ca120000c95042d00c418094640151083d108207109841c0c240c4d01442c204004501c035184034010f8508250324130110f40d21642403011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 831464964 1250 831463714 831463729
    0x3072d1508061009080d0c2105070506060904031d01020a15051605040605071113180b09120909130204061502190506010302090703060306110301080c0909070519081b 73
    0x3ca040209200d01400800e40c0030444004441080c14560300c1503510f8a0500660030b640c11103c0081c00d0701c08046105143c0100081ca5842c1c45075003aa031640c1d4820007001014103041c0c074082e000174245421401401c00030040000b400740140111010302c0d1f910b544070328a074000003020300c05c46a100c0081c03110719051030900010348607243c01c2c00b0341001c0c2010401000360140c1d02014000084c3e00e00410501c0d01c03144442c15410100300810301800f00343c4224520100743c010f50031030340c110300000041c01c100400710f203055154000742c800ca440d00b8500400c0080340701024003200610204103400c0401640c452242e0710045c0646105e004013504040c2000c0e0900c80c0b00306245811043c4100510300041000c40d070181507d90449013075641383c444150072001040c041d080282880e14114104566071842030142d4101d0381120216205000390340f06000600720300383d442e2041503001010a0025151425002905421440641d1501e41c0d90741c902600d0400445d40945e0003030701015010752141070541 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 831466214 1250 831464964 831464989
    0xc0d0809150d0c0f050307030903050c1212090307030905040c05120a0e0c0916050309070f0f032904060b0102010209064b0f04030206030415060503072d150806 70
    0x4e01000380411400c001c0c0052100400e02d40030156914450801c16014074240c450300e5400310121405030503110000c1c0026440140b250341e0040790720000903400c000c000107c3e071301540d256961002103454042400050003451a2550a2100902c80c4070803104042110620840d0f4002c80401c130518034040b10717418072201c812003a026a15130b00403c000000407a820b0f8030001c44610303003240c0d01d40d21802102c0c20142560030405c2407030300c2c0a00020f032030000c07841c4800135240900c1032034103c42000344294070b075a00080e595030702c1481c4090001c0c1c00f180445c8d110082202040c000589842a600e0010b4041c0c3d00110040c91100b031001c0720480310400e42d03104a40c1c0795014100e09215441e0b2030300c0d180840d20507108450404440000ea20303c0c1c44019006440c0195400751020b6200e040a05d80443e44020040d40703ca01c052905200040d00e02c0d0001301c2c50100c440410721031201d100e00030034404a80010034040400c1e5603000c440000d031400c0450300380d00b8820690303075100000d040a000308440c484100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 831467464 1250 831466214 831466217
    0xf02120a050604080922060918020f0415090204030b1009050606040e100306020403060b190f03082809080f011a01050d0603050706020a230c0d0809150d0c 68
    0x208100d00004400141e15074010760402580e5444e11040d0000030004038001082001040c4030341840890300c2d845400c0705003555070102082c00111002406040317050384140300039600407820140ca070010704066002c2048107117244000308081c0d880d000d28109903845540202ca00d00c000c0010041c2480300385100c440580b00d0082c092050382084000280c41e4040c030301038100c08400110105103110498038409000350343c4605c00b551241d940e820030400406a011000d13005082032200b52640030502c3c0e5100300cd0b279180303440d101c204508603180ea001603000a000307110310748403e011021035110b6410364420841001d580d0003c42a090105c52410010038654000c03450381000440e405072000c40f0080d034946c040130305e803140d00d481401140c0070203440942d101603d140034042d0046038055010a020a400b070007a190000a4500500d407503200040e9403509405c42e1700a8110400c4078544040c44d5140240034821180c1018803000c0020300da403054005070014000300041030020070015014501003041513 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 831468714 1250 831467464 831467473
    0x30601030c05150421020f030d140a0c02040f0c120204050604140d0221070503060103050705060310080f0618032a19050d02011116060c1101090f0212 66
    0x655841c40d000c40d005000709803280310314850110318102501c00b5140108040c1c21820903814200f00e40060303992001c102a4010140414080c0d558140014101c00040c0719039202404032031030314654900d07034005000319020010008000400340e9118020105001600080010001082c42016110b602214030f0440c070140103000400560741c42c05d054408444080400400f41000e440c001983c044044800075401034034903070700034600f101d0722900310040c0304501e0403a100e550329a0101079648030700b440000c20a03403003001c041c40182410005503400484400c0c00003110b507120820307a4103080c0b4a80c801c0315a54000030400801d8021880c01014001041000c1c0d8904901d0200004103d1401401c0a1554207083ca845620380410002180391200031007101c5002d400500d4100d80354403448580d28010360801c0d048451030701660301225420300342e400100701c0103501969103101a00c441b01020051080407002588105130a004403404a8841c100520304103d03144101709900340c07840c0030b1000c144e00c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 831469964 1250 831468714 831468719
    0x302180f24010305071205090c2b020d080f04080d021614010f120f0603021008160f03021b0a0c0602071503051003120c0c080c0603040807171c0b030601 67
    0x542603100641c0080c60089025a1500019505a0032482c1c1005a40d4030b00300070010840d84c0810100d0003228122001205600c00f04042d03141d10020307000741a42c3c1a1040b0340c000040ca003403044042030501c80e000790742c18460710850560b4070341c20603448500e40d900400c100740e41c803a5051003030b0560b0020f251000c81030a81851040c028240f0328915450602c10b000b4180710040c0e0146140340c0790f2024815080c48007a11420b90712001d4801440128024850702d07a01803007640c012194544a4400100881c43c007803100301c000c80c0e032188214148004c0c942e00b00322034400d00b4004259400300464000003445c450946181c0380d10002915400041103401c80c1c5000e010b82801d004aa602241f040e240201c0d81d0745035031302400c3d803c200a5000501c080002c0c114121500d4100c198202414001c84410160954071280e01da1a2100303480250750161080001400081014000d0580c5502860320311030000c0243c080d8000075480b00d88540480f05040101c003015135114050400d00480550282a0551 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 831471214 1250 831469964 831470011
    0x60d06032307061b2616020a301505040303050405100606080c071106031e15150304060b030109050627030702060912010f0204140d0506061003060302180f 68
    0x130f10b40304008103012a50702d0200c01c105200304807810500b400e6400a65200c0340e0b00711701d121040d04150104c1c06071229807000500d5020b4281d0886980410811900c0d0300110092580d11600010b01e0484090b40318800d91408201e8912405106521a0300e0000e020300740313414502d20300f001038500b204007a07052060a00010380e018000340d400c20401d4940c65145c5104e840c1c03080c10304442100c0d5542212011040103070b07820f14200d01003107000c80380007080042d440719990700304500306114085801000100e000040b1501402c01107034001d014850020b4203011000000b82034072090401a0360079072094051003c6440341021130107400075500c0c49210801c0d44081450384078001e0b403402920619010481042c20b4076803074614190820800c0082108248240c92440203411170b0040503404e40705000e018a1606014005040761030b0000020b000e00d070b42d48820026007141e002034440c1050780f074400c0007005844c1c40c0c20040500ca4110b040e0821484c0980349201304505c005c5c90354400104000300118000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 831472464 1250 831471214 831471257
    0xf05030118170d020711100f14030712090b0114032109060c060a0e150601121d03070803040204050f0c04090c0513080d080603011a060d0603230706 65
    0x42d030b01c403200c4840c641e081c0124810754002c0601030106a07000003110800c100e02c081a074040d4030800c9600c400910708408003101d41d0a00e0940000203d0718907440d15203004055005503902072003d1074400011007a110340001a112100390803240302002c2d000510829142ea040040d20400540080880842070106001c1110700e0f045025150503001070564584c1e15072004540740d00e042401209c4036820a45d014100030700c074016800c04107008000c0041030840c07103e40703040e001c1c590582d20860503100044c1c020b40109440c46144400c1c0303640c0604540704002c04e00c060440390303000754691900c80c03515005210980780010811515001c02408115090303991f07409480076123140140000e14103139105070544051140b800408044c1c101c40c0d81c001100d2100003110a072440b401d40c1c07002c009450300030905003030b03403c10075102140316908084403600b4202080038260201c140c41000c51040daaa4581c2900d441c072010031204a41141040420820810800c440040c038803842c02c4410114003044002c940c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 831473714 1250 831472464 831472511
    0x70f0302090f01052503020d120207121b020310021806040e0414160b040617010e0601030b01050d051e091b09042102030d0605011803030c0302071e0f050301 69
    0x140071300401c0500524070311a0901140f14480d0140071080d40540c240a96075104c000c848000040d1078001c600294040c42c020b55082c284d01c911005550001c04c0010703101d5a2000600c52885d8400b0b40d21000941c0d4208081d00000b04800001640caa601c81c0146000349040746100303005440404c01004a0800e5840140c0d201b5001004402c07044040c1c01e46a051041e41d00e9400d1074440b0b000da01060b580c000c2d0b0010805c4980540b00c0b81481c90312402c400d5102c400074031a00048049120000c1e078994000d03040140f207024140b5000c1d03c0e0000581c001021284141c540e9041d1900511031815409003c0340042c4d004000b4000819035084034901a01c01742880440d0b40e40100a100082002c100321041c909031000c0d0181c0a080320705417010700080d90307034011240441c40c0b142042c5000484e540143d841105a0704115111344009007075480550382d01000c0c0c40e0807030851098030000150030201000d07a030391038189001e10811051410001d50301051042d0410386c480c0c0d142648600c1410300964032140c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 831474820 1106 831473714 831473717
    0x6091113090c031104061a1b060c1e0c0102031e010f06020309090912070507180605180709090e0609160e040816080406020303070f0302090f01 63
    0x7034629008029000100c0300c241032000c9242c100d14010904d002034400310305180d4071420f1040d50240d0907514954880040740c2d680c00003002c640c000710341c0700d500801041e0500301042e003030180d44030303440c00012100d800000003811280d462040d82d0211260400841d128648454840c9554039841240c2c0da910002c440040f03110100c04608000f582e00560017142042d1072141070120b2000041e2400105220300c0000c00a04035850300107125143c880d401030000140f800700142c10080180c0010301002d820500c003400035859041d55801b144030444a428400c1e05d55441c140c40c0448540c2054440fa07003006114445410300095441c050700880d411210452028082c9204010013405000d141c0d202c24000314000c81d02c010f014108540c10700104030740c0d00006554604140d4800d44c040805a00301008202d8255027003002c040795519103050661030034000c0d00c001401004c3d000700190 = true := by decide +kernel

theorem cover : BRFrame.Cov 831294964 831474820 := by
  have h0 := BRFrame.cov_init 831294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 831294964 ≤ n) (h2 : n < 831474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
