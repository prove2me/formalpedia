-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4612
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:10:51.823799+00:00
-- url     : https://prove2.me/submissions/6a3f5b40-8100-4986-8525-1b51d68aabd4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 829316546 ≤ n < 829496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 829317796 1250 829316546 829316549
    0x71e050405090f0f06011404091b03120e09041a0405070b03040c0f050f09070f030915050103030e0901081c03141807151b0602091207051302091e0307 66
    0x200142080103014040c24000f600700c0d4010198016140c0e11025008460384410b400c0c40792030143c998800041c1010318140d4040c2500302d2290003050704100c0315941c4541d02104c941d000741c40961020f000c10740030320f8010341240300008040f12165070794946640e517104152108550641180300c0000002c04111041007480c015000e1180304684a01e03080c0740000002a141c003e8030040d07d04030030700140e5420700c0b10a0484543c801002d080ca1903413801400c56241010107040402c154441d80000c003c0b85c2601c18000001c1c0248002007104d60642c1005003a003803801c800701d03010340d400c40010400c2001c00b00302841e01341440d401401403a10083c1c03085024294080c0320754242000d400500c5a204030809081c0402e0000c182a03c01159503990700050040d000348008012070246131040e00030040409101d94424460100181042480c0d0003003141203000c1030103491a0340c0000c40500003481c2000d80c0c0301c6401ca0ae10415407400d84140d020440c000201d50b448030b0034268003102282e0564041c0111740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 829319046 1250 829317796 829317799
    0x1060f1809050703061a0414310c14060309190507180f05180714030a1202060f1302060706020307090306020d020d18050a1506081002091002010608071e05 68
    0xe0f0000d8030f0341070900041007840f2544079041c3ca03d80b8076042d9410f0902507090300581e40d113000030040c0d8030094040160700c40c030580300c21440d002e03c090741404a51002148181405038011070211070400340c0d03484203400c408010034415981407040090404c000180c940c0d8581494400c842100b1f00c6290852a0450540008103100410000c1c140d1030700103944071040444000409002c0342d06e6810340d02d1b80d030402c02005a19035400181042c490b10050b40c00c80c604480015044038040d9a007915031844e00c244015440c1c0c016003003201440081e10318121180e4005a5804181340b816086074001102c5e0711514030018000b980200018010750b00441c1c40c3d0b4021030b00950103650701c00d02925900029446400340c007001074500070841e200410040e021200c0d4540c010005c4c414081c1c2b136118004140c0440781605d50682e1940c03001b0840d00414003000010718402e03440541c4a44000c000c0010560707a8403642e0045a142c0030042202c080001400c0003140d0134031b002c02c940d402410380c2010011980341c000f40d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 829320296 1250 829319046 829319053
    0x1104320603040f1a39041e090911101103030703050a021308010b0a12080306150c0a120e01260606040f14010311070f1707060c17010801060f180905 65
    0x42403500c16403500d409408412440c0c01071700742210103c407a00032508501100c140103200621130908017803540900c00000703450342a05c06989000d5001590f9102800b12030781c82800040000c1030404203e0409210031504020f20848580b00505a403408010000010140c032107000c2449060694126100301681141030503c0035290007001d40030740b03000000700d80140800038000031070b0b580c0f041042c0b9003da03206600703c0c42e42d2110001c003c00d1401c0ea04050300c10500800091a01450030400940011312811181550b850b480f03c0152900082804290621040c145505002c050010260503007800301c0c11201c480d901c903140070903213a004a800c81541e101484c0c50201f84241a213003a440f440c5402d0342d0074490403000d40c10365207450041c500c009103d00c1440800c40000b50314a081c40340d900d0039060719a4244441a2280c42c2924400650b40d0041451500352a04048c0c0300003403140502041c400038010503103001256100e003803507071294240e2180085424a103280321b03038200c600036a8022044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 829321546 1250 829320296 829320301
    0x1030b0a0f1e0509060c0f091009320906060d1d01020708131215051f1403060702030a1409030115080d1d1c061104320603040f1a 57
    0x6803009110560b0f000f0141c1c42900d0002d4003c62088088030a444950107c0340d0a010360503043c0b0a1000c004030520003480302c40200468150684500200000c1c10503468240d1136101c514544c9109962458503070280d203c1d41c4c2081440d44a003c120741124410f20b0b03000444a16903400e5280d075620700041c0105a5000098003000d10009a0241140c2c8030003e4404195030f950390055208200301c2c12004041d5003265000c0502198a07a10040c0e002e11802c408560301180b4031811801c0f00c100b0b4010318101c0e1050302213541709007420080984e00c1003e0f80002c0d407612413810350250507084440c407800d20040c1c0000b000c0c2076a440a42119100e00c07201c06038040303004e0b01e801c10240c40303015885550001410704801104070714040741e01398400300d0003c0c000900d040180719555081241d40303e01a100c3c0c9841d0710311010031140850050009154091441081192003400c5a00070a03040904590804100c1100910341d0b4500782141d0b00b0a030301c0504c501c0d1810f100e2802d00000020550000d19104001d0304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 829322796 1250 829321546 829321601
    0x3050f150f0d05101415220e0a0305031e09030412050a06150e0f070e06070f12020705010e1f0818060c040521100c0e090a09050c0901030b0a0f 63
    0x410781540c2d09800f400d0496036550a5209010742071161401c2d4010501900d0541c01c2580100d003080320807c0d480301007210018401079620b0080720541c00c0340000c03c00000c0004122013901d4000035600440d4887d49107040500c0d545a581c0914050406d0004202c214001004402c101d588002544080f050006030b081c041341d50102c5645115905441c0c9952000940d14070100d20114810066511008090b150b139805020850704030910407910048040d100d04d0110780000302d0501030000a5000f400114144000140715910f518029400f40c44c4506070b06421400500381c03a00c440201e49042c21055446480707020b000c64158009040c9400356000341320310700c10240010004c0e0384066800c20f102c2c08100c2808182003c402002d00b60301d03081182a00c40f00c46a41d00581c1100b4001d240c616072980c038007800075840010658030b4000403592111520200304e0180701c2c1c0c400ba0002100e45d0b0140c0c0d8590b4a550000038001002c1000d85551249240340d0b498460f800400300d80509042d412020083d0301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 829324046 1250 829322796 829322801
    0x60b031519180c080601020f06070e0d240c02010e0a110114071214040e0f07030e2a1009180f09030804020102060a0c050a030504060b100c0303050f150f0d0510 70
    0x43e4400c001824060004825500026a0304800d096000041030385989115040365000b6056103400c0c0e2102010f220308000c541e00d403075035a58180059010840c044080c003440021a8403940c084400e59060014100d048040484c40c58496500000341c001204100070040710039020b107000164500c440820907100340020f04000100349000c5480f04980111509014203050040d4403901c00c2c42c204100028611000d0b10343c1154001c441401c0110b1214102c01043d41070044038500100000200032128807410b00b52224540c021000b5500710114811000004100b0500c0b0f00070300d80002d0450b0a410a080002c0d4444618000000c100b00201d00a9180083c101e034000e0b138007a80184641404540c5003401c0c0d202e0401d4002c19034442a240c400480c0c802e070040c0070000c009440003942c0d134120310541c3e01c45501100c0002c0c203581d0b5000c96100c00e440e01804440000d40400d40b1040c550042190100844140f10f00340c403c12034800b07419001e000002144a00344c524000c0450017192443d0003d10a140c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 829325296 1250 829324046 829324061
    0x60609060c0a0c050a050d06180203060a0c1b030917070905040b04061409100c05071a10060201060515071b0b0309100203060603070302160b041203060b03151918 71
    0x100d0380d54001640c1c1300d040001e02030f454081d99600010720000c440005605910402c1c19829130181c403100060359400290421000301c500603100c50b11341a0240c119640b091b00041607242030008030040a0301034a00801400e0039000c0e0000301001c201450950302030400403000182400d030710074441c034a01803601a06c410010f0324112449418800c0c1c0d0007049182c0b201981c80303400c901d001042802d880c4480070000e402c02c50543c400f40642045040c01140b8240d0b003059509a6815080c089801c0480301c1444c14491139002600f16450708405000654940080c1c484d010016880c1545940107400e000c00414040a8944001d042c003800004403900000080d600c104461700c1924000c410b603a290005910040300d80030b50104040001406c0b240c00ba5001d03104a07a042e0081c2e5025506903a100342c0314200664080c5c46258101c030031200740700e0f8540501405824001d00c03903410b6041c40c0010340c0c8004100c1900d40c1c401d644444002c08a147c42c8181c0c00028810b042040d0090003c08841c40000c0644 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 829326546 1250 829325296 829325303
    0x180b040320010c050607032409020a020c0307060c0b07051b010509010b0414010b031509010b0c010515130e1609090204051e0c03061804052b090e060609060c0a 70
    0x10900460190340c002c10f00070341039a8000340900405e56500704200c005010381103400e002158032101c0d03c03041e902c0101c00c00c1c014000c0b80e0001680c4a81d20b407000703840e00707140720700301031003588107003010f001c1d05600400c070f038154903132010701c0c801c45d0b890701c48040d00c0f540100710741d02c51480c0c00300101ea4503102c4150081402207400034020440d1030405000e10080c3c0b0b0007002c205107100076a000403c081c039030440045070701080446c01c800064141c0c02c00074610070020b910105a80c1070208019807000341c288146508143c0c9102c102e11050800c0002c140e02500402076414290381c2d4014000c04108240108c0003891000403e480155481303010300c000618203a0302c00d038041c526180004290302c1c0c54948910b05c05441403802402944c3e10b5060303581c00d5000609040e08400071804001e1140322041d0410701441c0b01d00c0103095855600003070403030400401c0d80840c600c21106c0e8100f03900d040c2c008c84140c3c00da855108034210565281300204240e03101e2035800c250000d80000d2072400c90a008070b101c5142920 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 829327796 1250 829326546 829326593
    0x3070506190507231f1518020d06080a030305060a030317060102151e0108070b030103120903171b0105280e03040815090f0304121109100906050d1101180b0403 70
    0x6a04a17904a4100415140d00c8100048090000c8030003100c5041418017a03050241c640b104904200040e01c5007540040760382c0c0c3c0259125004c143e0540035181c6e2003181600d80d00b45032440c40d1801440c218004010000480038400460840e0f442030101e800354040300c81c6040e0060500c95004a003401000f442160300c400d552001140b01e8001090700000c442c0e5000d41103045d642103490700601c2c512005511700601c070306000004001603080c0d042d90504640d4000c860b40742c0545a807c0b04200000708002c405c16490072041040e072020b401d510346000c0a620201c0d11401d1240c80b030100c001c00d0301c1c4c00c400c080c510002c5000200300b04000740501080342c0408a41c92992a10400c80d951114201f85482554209010603c40340003c20f050004860280c000700905602c107101040340c200c0141c0c1c18241ca120000c4060090346014066000205400d69500c045680182c642d60010031109040b18100510303030145e01386030f442c803642c04130141140304265503407035a880c40d091391030300c0d54141200001c04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 829329046 1250 829327796 829327843
    0x90414090d0f0305040c0303140714030706140f1b04080709050901060807060905060715180c05010536060c0606040612051c2c0307050619050723 64
    0x3c0c400d015590185501c9240c1000c120b00b95a0140c0b0f10002e24000d00c01c12500501c41c44020626040417012260101800345907221100c0c00c10380107a4800022861807580d042040c0b0002483c0e41c2d2801e80d1010f1803000701c4000340c001c131810704003d201e40c0d4842c800c10700c1144c10101d5030110962005024103502d00c020441c01307540c0e11140d0b031107050030312500000c50381e1064200041c0c00c000005210380d6103e2004405510060b90f0414200d40d812601d6034400c0c00b4600301082000082c0001602030315090030003d041c00f010038450081750708540c0d01000c94501c880040441c4c2c6001d20082000ca48004100b81d490704040c180310f0365116002c490540c070403800c1c800006144000c050070500d0840d000005041809a010002d81004a1700741c408810013503100c00e92414180c80c02c6030600390759143c4580d4002c801912080524000b0a90001d910074281000b9044036450044210030f0000640e0400c95203030341150526801a00c40512001c0c2c0003081251055191180881e01c0004198529662252607 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 829330296 1250 829329046 829329077
    0x150a0f0917070615031407080f0c060705030702042d060b070204020307020a0c15141602190315091202061005011110020a0503061509010f0302090414090d 68
    0x48802190107840e103201840c05121402440300202492806140e02150080c19884420300192460303109644610910804265092060102c0e100410281e4020f10481c00c03414500341d01e0f500d0703503d900f034420342001910904000d030900503100d40c030390020020008007500810010320400b1300c3d5800b00500400e400c00a0140190340b18803025150b4107404a4180360745a070900000f580302500c600207510500e0030306800946000604000b82c203038840005504000c010028102c40071203075a07007020340e400348240c10030031202001a00440b0b0b0111440c20350a44001c6c071080118000341c1010303041181c02000720040030360b10780000e000584508420034807005005000c0340c6070102600c80c1d4030505508041041a076118907107240483d1204c0c8162480a80360b07514040499000e81e07401ca01150011041044030300d4400c940e4800030000d0261185402c0c60400001c1503030461102c0442407583c0481c1030201612254440035490000741c2012105007480b1044c2e030354a034072101c1080e001514019054051 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 829331546 1250 829330296 829330301
    0x2120a0305090f04090507080c040f050f04030f0512070201021207030b0108060f03030903011b030b06040f0303120e0a06060302090619031403070f030c03080a05190c090503150a0f 79
    0xa150580d98080c1080c440000708918036480403c002c0d40680c95020810214105105540050074100020200d0150708814841a03803026861b140d03c60b4684800c01c02481400c80900d94060790520b09000071210155080d10a17018071011203101c0043d14080241480d0158010f0180da0a1000102803994521100310140c80d40701c01420700013034150010548508081d90b0240c880800241030f03a00b00205c0758042401c48640b074002d269034080c20f0800d4421107405102e6081904400d46131540b038942448034404007560684402030401c0082489208008415408450824170308403d4582800300740c20210050022070005920881406011952914202c1541802011907044a201451954540003440f0a6094040300140010041301000403401e42c10803420b144243c4622840c0d0034030341001005010000c156807101441d100074008002c0f40007030304880009800300041110f40c82d40c00b04a0b0303001104d520240e0548205844d014101d4155034040d44104090324040084400381e01c0203900713 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 829332796 1250 829331546 829331563
    0x2205010801090635030d1407020c0102060718031a0f1f03030c050a02041d0105011a160c0510050d110906040b031b04091d0c030c100315120212 63
    0x144415040c8800c1e100040c1d001d8461088030590b1a01c0c41821310b1010864110341c40342c0340e0244441c0c1d6541c2200c1440c0380300d01c05142c004142e440106002140e1800107581c8071005010718040c8511105080400c41e0315540001c06541d01c130307540d004860340200d43c0c8800c100c07003035802803550f4060700c3c00601642034820401c1101c500c0c0d68025500d640c13660320b00707443e44003241d20107807031500070441c014015071128042c00c8071031902c507d000744103110b0a0719207a084980c1a008031102c2c8442c0c82580d0442031074a4107840e520f41600c800c612407914903107000074040034541d00081e0000a09084140c415030840c0c0501050b03000b21100384064104483c88507458030031410026440310040c8414444800001d01441d0300102207041041100b10307040b20319100d41c00541c4001d5126844260004184100149440b011003a000c0108092200b40001944403010131000314026040c501c00700a0240c840e404c2510110044c1d41000d0360345440700c6090302c030300380d5929050f8081d104c0251100110300f400910750700b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 829334046 1250 829332796 829332809
    0x2161103011d070b0a050c0102131a0405060409020c1c03050106020d0203070215220906060e18040204050a02090402041707050a0e1303200105071803020a0e0c22050108010906 77
    0x2142138105510215141c10501384041081014805185428024401000c2213130f90706200401e1545800980741a03414826140024680b0510040041d82c490009840a40e08a25405a1252140140d035031410200308181da01c101d074400c11982a80d60143e12060680e00d0b10350070b5441e00c41c0ae184044c5c1c0c0c1c0707214680c402034120010051000700c019204000e8059840304000403440b20b04080c9080c000500039803c402051940e40030b082006a41181c0980a00c100030398a01c3d90038100a000310982d04002803010b070145480d40300041300602154106c4203d1030000f402151a141c503103a00a04075408808100080d108221011881d882c190b80540e00711340d51407400d01241d6841480c0e04100bc103244004400780070a202c00102424500500d50504804541c0001880e10707140d00000d00c10292220a84102500c1210600140c5ca560403081c1c00e894400310220550b80303d240703c90850780310700500440341c0080d1071a0106550b0250180d4070895200b60b03152161640c80c0d200038001c4a600b4804c0380c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 829335296 1250 829334046 829334053
    0x2a060112080c060a0b0f101b0c0506040e1f1805100b0d02090a06050726120c0a08060109080d0315031a0f1e0411010c12090302040e06061008090102161103011d 70
    0x10700d00c091080c1241888c58414200e849813541d07100042407807501701d80c000c0e0b00d100211a0810a0428540400c55400746030b039000261031a117032001c1070745015190103000e80d500d51a0000240c04001c07045c0e924004103481801150740711065030900000707400a1203141d200c0c0842c00000210340740b01d9400d641d4842c0d040060010040c1030b811003450b8461148880e600c0d40384d03040c0191160080030242140c400c0e252603841d035075a021685802000d281008103c203040c400d10903010f000382d80e00000e440141408500300014242011400c44180d02c030b042c0d00c01015002504035004071180c141021078015444940c0100054848004240c01b5444003002c0e14214031103c0e0004000ca010034046449007013040c1400c403141d905548440005078910203041e004942c5680d010401c42c1020b00c101040d080c0010050603490030418000380014803d04100020403010030041400400c2c00e41c101c60080203011030f200c105041e285000c0c412141c0e5a00003034031039413811710351011030b0128800c960030100412024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 829336546 1250 829335296 829335317
    0x30102040521070504020f0301170d021b0112060b090109092a0314010905090706030203040c09020703120203070806040e0109050601031212050103082a060112080c060a0b0f10 77
    0x416007042c14401068050b20401800180d652902d100804594103200c14480d0769604050b0304581007000c10b5081080d90b030254511800c4d030b50340858003105d00751105110b1129003500200403910003d00c40d904940a43c0351280c001803080e010402415414420388071400c0103590340c08501d00311496011181a9116005e419981d0301ca0700149042d8224001d0400203030350301c0d003856402e0340c2c0a800d8004032403041d5104180104540100311410092507031f45402d6140d0320341a6206c60340f0f882c00d4807d42ea41d4603004036098040500400c2c0322890780340d0301c4030119101d00d00060003c0c5244000e0354101c0c000e9240489201c101d201c18001c50f0b1a441d040801040d19134699510f484001280c00c107010200701442041c040e10413164054140214040c203c1586c035410b50311030201844400c90290302101c946100d1031214005c0200314681102c0a520390f070425100c0d10b08144200748520b00004646000d200c0c10040380c5c0215034000b007241441502d090f100c500b4800140072072812070b40815004110300002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 829337796 1250 829336546 829336579
    0x718120b0f0c040b0904060e09010c080a0b1e010903050d090e06060408030703080402060d141e01050d03050319020c012a09050f12010e1c020114181f0b040b0301020405 74
    0x2400219009080001c06a23950208581014015511130600765181c1680302681644802c156802940c50b55040140b4040e2900040c02d2204480151000c0151156243c440768040c0d120a0b00450b00308054420078013020100901c40d11103405120700c003448507404245c0b81c1c18030109071400d4881c2c4900031440c045150301c041d50301180040049034041c8042268101c0c20403107029102d040947d40d41020394506020f0304e1044031b910344100106441411000410081c0d07100304080750750a0305070411540e261070342c0450f111009000c044403d40c490000407d003605090561000e001007584641c100510b1005101a04c04200440070000014010f00d005100314502900021104080104504460503000215509450151041c0c29240c4c1048052050910f030340020100c14103130a100811009402902c2c5903007444000c0d14a400b100901080b040725500200100b541c4880706074150b1800d070801168050141140c01d40e01ca018034145441800242014025101a240020100140b0b80341001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 829339046 1250 829337796 829337819
    0xd1214040609031b0b0f0c0106171c020a080703091e08031b0c03063c0703023a0f110a030c020703122a0b06090718120b0f0c04 56
    0x4c540300340070610244c0011041307a203d0007440c00101d040c4005444600100807182154120b0313004a21194001d5165640c955001c1401d0000040d02031010800200f1984124540f004100c0020108200021043c0074550080103c2c4100d51801107031840c10f50208440f11000e0326240708030046640240710b5013101102020752121a107003500c040707070444561100060700d070031000d8640340030034410135042c00c0b400c0407450701d8003118880c2d188a41c42710000240505030301032002800d5208040e8041480001c0e01d00843c1c100403210f4040b20700040c60000c00307174401c2c044185204181a114903150680745070500c54042c4911036a05000c260b03080c0358460400380c010340a070030900021401000e9012000a070f1102000803146001e98034041040c2011858010b44030417100c9c7c0341c84502d180800c000000d02da1400035684150191807079600c60700e446509444400c0048902519031000220201e5240303144045030120034065080c01a894460a100001e00c0380140c8503c0e12240041000340305c41181903 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 829340296 1250 829339046 829339073
    0x812040210030c1d06160803010608130c0306110f030403020d080901180b0a0e030a08061306151101060503010908120a0606050412030909050c120a0b010504180b0d121404060903 78
    0x103409240f5101401810308210806c6a0b011215000f001c00103100c683d9101454981c00444811400c22203a030350b0300c172559248039612005228984500c50f004445e01d04500742c5404030200c0010503168141454040c0d1580c84040400300011305a200191010405026000382144e20450620207606691184a0001c1c001030102007100d407952800026010100000e100c40310443d0b640d540313035080840030040c0b0051400300410100e8201081805241000c1c0c0c840302c0c04000300d06080785140e8038091010b01424251303000c01e41c1035180125030303030a0004c0600107064480b40c886444100740c0d03d6003909030854080340980c1d80020824001805801215032210b00c0c0540241040545142d031070a40304180d607801c581c000c2e010301001c03411808503c440f03404e0903040504002d040c480b03403002c0400200180030302d100c1c0c500d041590300898826150a039114100807400540240007281d041d04007007080d9400c102ca50700015a038030b522640350000c290155403c0d0b4074907903550215180b45495100c645100d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 829341546 1250 829340296 829340299
    0x813020103020c19120e010f050d0b040603021002010902130509060c1303050d0c0b070305090c0f180c03091207110d0302010e07090c0e0613090c020a0812040210030c1d 74
    0x400000c407981c84c0068005900780c42c4660070070800050688002011a0b484001c003a0502c031602070401040c0f500300050b1041e0004e480d000003213948202c0000f4010780041d07030000e50485884031000c2001641900100e20742170003610020170503085a22040100d403003c6418007100d4005002248090000800405c201c0c5614104c503040310340c9039203501b0b00b01045081d46e40c0100b41d1005201040000a200142d030014481c00c0412141c50401ca440340c1743c03011151000e105204404e031030783d920b039100c841841420090014490b0070785004108001d466009a49440140c4100d07201100c21102590880304801e51003242407e600f000b0006028100c02c582ca001c90a6549031952134651020402162004240c101804200c1600da0701000d0400d07550160010300940e000c000c49881c00302d41034140c1007141c003980000140405100300807030410201c810014000700c4001030020800c0d00ca040340c540658001c03102d020844042c0d8500f5822960804001d4000c5a40149506071000c0281c8100080240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 829342796 1250 829341546 829341553
    0x17030705030a0c1a0a0902010f050c0604080a0c0c15030b03060c040618031e0c0609030b1305030405190315051521011104080c0627010504120515070813020103020c 72
    0x72228602c07145000205c3d0180101a9107401d01c4096681c440c241c030320304c81c580d4200980740c07a950b031001c5074540c10014809000d0141c00914029540d20800d0922507807a04429a00080e6803070f11021003502c40c4121440303002034104115011146408100b240c0076aa141e5102450030f45410416606941e031902e020790240580030000000c40c00c0002d2245401030030340c10890326140546002117406095401000030403100301400d10003e4541d11000360050300483c80155007403003520307040c1c3ca18896600580d401188000b10010080103284015041c4c034803801c02240d002c41da0804d09011a9411a040718000303080c4400c140c000e0402a107005d00718444580c3c00040100050012825102e04101400e1104000102045a2201488a010241c404a882c2d9103802034281c1ca0b4040096042511125822591056000d90380500308807002080c2c000c40e0902c45201e0b6041282e21680e1820014200c01510000528068485d9280c3c0c0d00c14040311241003c1910035400460094010f00a984058403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 829344046 1250 829342796 829342823
    0x60e0112020406020313150c030c0c120b0f0c12040206070f1e0c050f010203220f030605070f020705150f070b090102030118050c030109180609030917030705030a0c 72
    0x14550000b030000e0101ca40003150383d402d8150442c3c05c8000c00e030f40000d01d0a036642ca031070307611554805020a840ba0705440c02e1784030950a42860682e407001ca0740a405000d0001092000300242d0500c428407541280c0002a05540c076400d5601c1030b4400d100000c4419080c800c0050010b04e04100500403c034029201d00040345003959030b00c0548505070034640d0f405199020660b040081808912010b00415561002d0030400840043c0d030300d00410b5100030068044a0848044c1d913010000c500040513007003e609e101c4e642e60b04044008113420f030703000000500181200c64a99000041000c11100007400c40790560b201c014004092ba00041c180300700315001040b050011a2030f00b0030850040c000800010707901d51502000d10000880440045d00960800d020060303000101c00c15641154058600450031710b081050b002c944104084000708040c0c603110481c0b09040d0700410440545100c04920b070281107090844a540c0c0c0240400101154020091405007512500c0e2414100d4852100300340000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 829345296 1250 829344046 829344077
    0xd020a020d0212100509030c100612030c151e06051f03020a1116092d0f0e030d0b03010627020a031b0503040204050717070c02031e01091b060504060e01 67
    0x110826103286c120740c1c1c0041480744080304c090007468042c00c0d596104004641c41e00d0490501000d0910002e01801a90491031040c040c031560010b05001c5201010441002c3c440c010010315640c100c40c20803110b25201340481d003400c00e22001581c01000e249480e0400301c4540007200654045503a10042003500880c40c07111180800c117034051301c180903269440c2c00341803400000450304003101220781d48601031034000c0c0e00c00380801d8100b0b65a24015000c10b680001c0d01c140700261211160030b42092100040201e803800b1590b009089200c0300302d0080c0680780d03a07a441034007007024809003402408000700180c03058500583c0107154650071414042504090b45102072002c849140100c800304074000300300f20443c81c040c07049550207811410841880740520300c0e0798920080c01040300c024454001529810f65070300b0424000f6a42c05200b410600c1da18650200d40a415843c004441c1801030b00e50524404c603481c41c840064070311603a58141000d1801c0004c4800b080003081c80c2d41401004c02040341d41c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 829346546 1250 829345296 829345301
    0xf020909181e1e15011811030114030c01080c120417040305030a030f060b12090a060213080c040207022808032115090601030902120f0601080d020a020d021210 70
    0x10818580058641c9960b040c07059502000001001c1065801410007403e0301d0072401000c44c1580c5101140340c101c1e588044490005047e0b00c941d005029102000003c1d0710506050280000300e0241c040c1e072031140c400e00040d40d002d08266203542c4401400e1110f85115103110159662090088030090300080303640043e000641d010303030403d841c40e80000611000d079135018040c20503035240f00e0700c0401c8100d2030030905889030301030200d803105511880c00220b0742f00c0384100410000076410140840d915801c0030f800c100f040341c092107104990700a510b408552441c4c144250b0b0351494003d0700010508072214180d03514207021552040f0a6000700c8008200018204050b18446001d650042c0388103040c41900205a8001003150a800e064241c40709072548900351000d402c40e0f4207080c049242c501910005010b9078034108901043d104400b0084180a000120241200d008a00342e60f0302e810042d008036224070101d80080e4105640042220050816070340c030346410012241511213001d01c00105205 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 829347796 1250 829346546 829346593
    0xe0c2b06050a05180c0f01051b0f010204080c0312090609060409051e0916140a05130207030e120340030203160f05100e0307030303050a0f02090918 65
    0x2090b95503001005802000300040c0e40340c40400c0310041035001da409001070305641c0324041c4030f81000b40115407441d00d81103807040b01c040040030a0986030b12031f0b01c05000314002d400a00c6502950b02c60800744220f14200426034810744030f40220100c0c949503403042884403a41c00b050001e44c21050801000584a44a1003803501030107681003122101212007849040300d0101405c407141d9a00419035800309050110f00b035408a60700c6100901244110100041501c0005c2d0b200e10780003050603d8181032441036500070180a4841d84410703400204510a000040007504c686900741d030300c100109003610f4441c2040c00007000ba0791a0501e0202d000a8084100c1e021a8803503003450b952004003441140790030700c01c00b0b10349001c11000c0826980307400d1840d5a152003d00c0307094052180080c0c0b0901d41c0740300300c2c0e0400341040c1c0901114485a600d281c000d0041c442101c45800d828604003070182c84454074022103001c840024044909600d881440c0c041c00204c250810b00144215208008845d841d07003803403203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 829349046 1250 829347796 829347811
    0x30a0213090b06040606020d0c0215120a050708011d0a0b040e010b030708061e0402060403080714060a0902010503040809010908120405120106050d03180b0f0901030e0c2b0605 77
    0x8101019141c0540c1d00b41c00905954071450910405014050780025403500110851408030b98000707482c0049141ca01a011460556050000b41c001080092600803406449113400811860740c80000440b00c11000303002c4e020f00200c0708148058200403d4034202d400440c83e10000840e4000d04001404441804100c86507070303519140074124900e4180304d10302c000e0403038502804251500b115a160404900403241c0e10b2a001d000c007043c290b40700e0a0503503001d150300904003552070300350f07040607420441000340c0c0c0c030014414070000500f01466400703410314007603068448031f01750b441d5980c42500580200d9442c07410840c140900061450b81045a0b403503084d0400103140e41e07281030600b400f0080082003201c1c3c41d00d030306212040009440e12001c1c140c0040e01880c0c0100c0d0740f6002c00b45408600308a0788583c0c000360000c01ea4900401d018401003040e0799090301e0404c20b04d90020a600d0300d502c0c0c0b00101d280e000b84551030310005c1001c44d0b010b0000001001b401102109410707612541251000d03203141 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 829350296 1250 829349046 829349051
    0x30c1b0106180c0311092205040303060e070906020703200a090203061e060f030601050c0304060905010e0301050907060809070306050c1833070f0b061e01020a080702030a0213 77
    0xb15030b10900c2e1003050071030021841c041c000d1003d001040c40d500d118024a65004104012982e121070701f09001c6100103140c001d0083c04039007028100180a0007080c0501940d8504100102e02c00074042c00403041220455005043d0151440d1190400c14420483c1a20b69051a010402c80d0760742d480714042c0a0241f0040040c0c903810f202c0144010b1003078040001d508101804a04c981996400013945c80c0d000555424594a9650500407101c80c050f4500c6d4038841d12020038042915a003101e00360090324001c0c0d880040388440a410182a650140c80d0607903035402c815002e02c5918440e00c1801c0c2d1182c3c1c607008842c10a940d90765404c0850758119174a151034000814400f0b0a02c00b09000b40e03c105404403030540c91514141080031034110010480e600e1a20321502c0c1c20904d0340020160307420784d6007184800c0030f01c002e50b041844501c20112040341c0f1900d91207623599401da80c010707038032802d425040c0e00802d07090b0440d55900b002a403000c0700c02d0f6071510460141000603620644040c000c080a00b102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 829351546 1250 829350296 829350329
    0x9040b0f0903090112050618010306051b0906070201030b06040b0711030606150d150906061d01081303121104180612030e01051303050d030b0307080a08030c1b0106 72
    0xc0400c5400604880d4280d002000800f1050380d000c500443d0b2000e200c180000d860300c1e03800c000794082c0698440c600c9842d14a5000005110859024a110382039880d9900a1014040d0b516883c0b84a000e280d154884003c8c40044059486a808000715400c09404180f610b6110304486103190400c01d4100d8078041c02c2030684055040c24820250803241c290b4213108181c0c032410f042101801a00f215a04055544030005080039420034240002c002d640d01c00c0065a03100d0000070105564600b17044a4080d142046554551041c20814400c160b100702003103002032150303021a000b400c0112216151030716404000ca000c0300f00d0000704001c02500841e0480010700d01401c81c20b4500c240e1100c11408101511800842e0f0080160b03036042c0824031f4495074980e84003a620780c0c1c038560790300040d28034410822480121034040d031183c00b014004900300e4a4032595554030a030760b58094070009041c51400e1000c2030180b0000001f41602c025616692000b0880013036902d400c43d000760b84406841d845201c203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 829352796 1250 829351546 829351561
    0x160c051f0b0306040b010b0a050702040c050a1b1e030e09070e15280c0b01031515080a12050c06070206060907030203060d03050a090306140f07020f19060b09040b 71
    0x80c8800714903059014060a203002c0c0c1310200a03810501c0360b0b404011001a04100346031140b0100e42c02e40b0f50051007000601d1050400518075040000700c01c021948215940d81c11650801203250220f5000052010304050945943c004c42c0343d2400840c284a410003c000c900d03a01c20714543d10410f015503414296540d4102004000401c90701c00030762000341042580751200e1010015081c010060721910701c1c120005000b20ba0b1221440400b400710500d44c0004400c0090040c0d4400041e81002c905100030324078180210350a203c544a45101c0e984450141c0707002680d19001c0916010042c03d106080c80003412160307003441400c4440a0051f00120704105840c03070103d2400fa04000145811829858031802058100307981001c007905205e4041002c1d0407951041131540080d42c1d100e502840509031076078200401d014240c4039003a0070407000e000158400d00c00140b11035086030340740c0140031203041205800c46074000000181d4000f500c1e0500300c900c603141c043c2c0d114003462113015107000c3c0b80360003d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 829354046 1250 829352796 829352801
    0x40b151b0c0d03081317030f0f0105040b0d1106070506101a0324130f1b080c220b0a08040c1505040b0c011b180b040e160c051f 56
    0x20741544104000382e515004203501414581c0e018181101c1c0000c91016428038100d8a00d03415007400d0584400000c102c20000c43e056070a000d1300051461031f00d5644c0300d10070007003640d1400409640205c2810300c44030215111201803010354101400440c03500f440d640b10703942400d20441c0c8480d2840c072540000c1100324480340c42c5125241240e100c09042d0b040176640a01181e5076030a084a450b22155a901a5992800c00301b036540c1142d070b1001c014000c0c007007207424084e08d40ba024080d450081c400542d80d9180c0100e090034454031200021034500064541040c41d401c3d0410340000c00349040140c040341620b0230000601c4901e84a80701c1d041c0038070701842d0249003280d0316082140d1840007440d81d964056004415034055a40c4480034076103424500d00c405004080075551701c4d01a900403804010b06941100d0f107a500c00800c061892a071584881041d40d0503ca64481c60048140b2400001c0c0c01203049800c4403441151743c0f030203641d41c07840f685580d1300d40342901341001e010300081c1821354055030361403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 829355296 1250 829354046 829354063
    0x150d0f0c050a020c010c0f020609040f06080f07051e0111010b0409060902040f060b0405220612031403010b0a0c0807020a09021b0c09060405101d161d040b151b 70
    0x1d00e030032141b482c815030b00d019800d807200030002d004103408245401140c0d00c40d00030350403120200c071080001a5440103c15030380d50303240811030018001c010010425050050860700e030640211650040b11601034011600c1e00800d18500312a0b5607954420b03201c543c3c0b240100b42c0b005000c0d51002c500148103004010850390303c201d2505c4890700c1e00008201c02e00a10060301c0c1119030071554002240c88e00120491002e41170900056250f1519501103104142503d00f141070b140240d4030805035080c242480303800d6203c02e02a07008864014440900303101e1040d4a0000307098070440056091140315408200c40207502d4105481550b0007040c1a5024001d550307284c00081a408004d0000101107804200202c0700035003860300071a01c2d40300142c0c0fa0404001c000c0c0050503100c86056201a40c6401a44010001d03107070a07003c0e0b206010240309841c42107080201c041102000881c00c1090481003000400c100e4180304d402c400801a0000740d403000c0406803100590a90138607800e071140d61440d41c201a240e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 829356546 1250 829355296 829355299
    0x1060f170d0f120b09010b0304060c1b110d0506090a03020f0313050f031c0305040203150c09220e010204030b010b04062114090d03050114150d0f0c050a020c 69
    0x22900000580c404540d09042c4803e00309407000820402c1801d025040c04801c1d103800018000001420200c100300540c81580a0442086a9240352004031404015886201d0480c4040c102c1400410300344c1151226150300244000c0d40303d00140c0e01c203803c00804841003c940c0d003005481c0418507406100d074a04074000c0c0d101451600307505205400c051810343c0078490007607004a02c40a45d07600d0400820003120008075100d04103800000c0d00402401c021141280207000e00c0e8a000310b1031004da403d80b0b00880f0080e5140742000f1842d814099900c00b2110300c002c000d2202d4441d2042400c89108403175150b6400000560780c0d606500f4800051401a403043d943c00700100000c00c07030150f0104482d00c1542d440040008400904034080b400780c80b14043c01d580c42c3da010000c4c80724428001880d01401d90003500c05009503aa500146500c070110107241c035410444000400044000b514010001d060301c19100041d85400c0c001020121420a210080070807070001e0b0082496404000d600f41c5100c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 829357796 1250 829356546 829356553
    0x90316031112190e0d0804030b0103030e0d0804050405070903061806050f0c0403080d0f0617150c160c170f061f0b0319150510050f090d050f01060f17 66
    0x40c00300c01407003495410a4031040102d1044200300503a9880c17400c81e4880d40080200741c8468407420083d0420354207101c210301080c0c03c03142d80140c50810134040fa094940041c161801c0030f01d0039044c0405098010600340030090508000310007d4401c3c41400009800e080c2e005c00301c402145040411150040d12015040782c0b0441000a0424810201e9007681e42c00504103845d003803c2d06542002d401070300502000c0350704000c0301244100103540d200d421550180d040310400b415030700e01c415203040292080c0c07024200800094040165001030414154801c00143c0e6019070b54000f582071061191050700000c0e0819805035041000c00c0001541014240c110004280b501c15018041c1610501c00c10000c0e01c404400190b01912080020102c8040b20728103100a0080c0c102d2030354900380364050144500507454144582a11603c01c1c0c40081051071500317458001c0010400010100c151400caa4922501540074200c920a00a01c402401564a11740c84182410b0100c1c44040b1a6407444041e42d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 829359046 1250 829357796 829357807
    0x13020c0c0d050312070e0a05040c0c240911010809070608040209072a0308150901030209060d1a07020105130302061b09041503120504031a090316031112 67
    0x800224048140010845511500d10720070316000d415070148008100440d6080700070442c06941040002544040840d14014181d0302c8a040000300c2d642000c2040c0040e1214451400003240404003401c070040b03040030110591a500501c4095610fa018111544030071003016412558122010f0f640191402024286050400c00c00510b4034a0041010b0300c00c4001c100401e410600032241b40f250342032481100c0d0216000d00c14a880e6408000c1c008800050050340002c031040d0206079440c0c2000401054241c0c40e920396000c1102c6001c014201c564032801c00e0340b40d580000d802041503c0200169503680c83d0508d08018040d00315240102581c2c0240d02c42000000040d0b4003148560b071041c0c10800b0045048800768a031800c0340606d10901c1d811902c2cac111024580e203410307030610342101d100d64140c0c904000d030380200315124000e522000304055505c0e03003d28421004444c5443d444008181100e04280400c00d0511007030003c1a0180c010842c1c4685004c01f00ea0180880d40040082170b040780d1410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 829360296 1250 829359046 829359067
    0x130b09030316030e0405010e0f010e2206020c01060f1a0a0e040c0c0803010b0714070b090904050102070b04200414070c0f050a030324180b0607050d0801051302 70
    0x911400d000107000d020342c8401801014026480041c160202034800c002542e10346110070703000002039030102c120030414030001500704680038080e8480c9a1200e661407002c5c0c040710340c6001c00500d804c1d080341c034071740c00b03001d94071203034034244220740c001c041c200309800e40311b89440d4050b0f6242d282084201d100d400d0801004084942054100e102c00e0f04c2920001824100c90001700d5501c4138400c00104101d00c0000000f41300c1c1c020310702410484d030154814810200d1454061a84c44046102c1e6088407007050000c5209850f00007111903009000340000742c5010b40079034031140c20050848085030004c2d509010198101e002c4014041160400d44040041502c07145107040d0200c0014503d8042100750180481001111400c500c1d405074040304072182c035442482e002c0d010341001a42c400c0c02003c1580b2200810010f412214101ea07070122950341450500c070450070291500d079030000d070400400c104201c00a041000400c44840c4a5034a441895060004114115483d103805110b01ca0040c0000c1900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 829361546 1250 829360296 829360303
    0x30501051c03051206130518240c1309020c490e04090501060503062a030a0e0f0d0f0c081b0f0708011b0c0b0a0c03020d0c05130b0903 59
    0x14041c0c4000b00d1101399545c00006000100400020580d590030078080c00a10551400c3c071203001b0700081c2c141d071550316180078411581354403070000324203401e055000308001c05102c00c018600820b11040c074410064880041c0c1060342e201144101060340301030700b410848480c8036296260542c450301c0c2c001104031041d0780010608240c0e0a585607004801c0036001311640652403000f22400702420500c207890490038290300919061182e10301032700031703c80014080c1c10100056110510713000c0840e00210414a0207051503000107207001101c0ba80e41010b031918400801010080ca64201e0080104035020311000782104165003454050013000c010000010303034108203640741c4113131140721000c00c80c25000d03045260030708029914203e4000e0b4840812291019006802c06074480c004d0f0f03031282c091441d070440d84003401d010080c200c154840003180c1520b103260810380300c8443d18a0007500b0300714003001c18801c40e0000c5131054049400024007040140d00e010505005041c4010401c4c14507a800012a40703 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 829362796 1250 829361546 829361557
    0x12040f0b09011d0102011e0501050907080708041e020a09020307020705060c070b070512040f030b0f0f06100210060906090b0301110306011b0501020a050702040b040606020d0f020715030501051c0305 87
    0x403000e0f81000f000c3d149904c00d601000d40c0781c94036482c1011481c0000c004000501003802801d000d00d040342e000403d5640a6080d1a000d2001a90340720a00e55a40e10b40315030304000c0101d40b50b0600040c070314500241e0f42d02107059001d407090181c01652400c4c42e10003e032500d1607592069008440c107101c91031500701d022445804540c40c00e802d00b03507a18410300e0024100078220340000c0c440100071801081d545405032082c8260b0b41704060b02042500c446c5005500c6800c112007000c5011480b00000b403a5050a032020b107420305082c0105c4440201500d040801c0d40e18030f400c145180b03952100c080012500c03c0c025070341800c6050b40204004442c8114003030142c4801002d1030f06000903804680c0c281c0500c55101d1b03070f100380c01000864540c3d280c140014202d80c000700050344101d0400e80d24500a1400e48504800c80b40503800034481d0702c400d09425a80301650098002c254043d510000a000ca124000d1203401400341c0c0d0700240740d43c10700c81040041c07034501d012030321403e120712291000685c01c01c003203c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 829364046 1250 829362796 829362827
    0x12090f0d050c04270809152b02090915010f05030103080a030b01050c011506120219030e011e140f04110904210906090504140402060d09020312040f0b0901 68
    0x3c003444070700d80d013a103c5061071680c800070f010242c100005100d078460180a5000044482c0a55142e81001415881c01034100c00d4840c80b61401d9180f01110001300d46022034003c0b0080941886040400104e11120031256403000c058022280c0d441d540e0b101800f90003021042c00d000d8290350660300c4840090261075180303030a042ea180102c20450707014005a403540c1001c01c000b4000c0000701c1d203100b4900d029500c90040840c01420020001c8900360003a58040121120740200000903100f00b1400342402e20301d0a501c42d541c6841c9004142c030724011400c0d10f2921104081f890400b61821040c0c0b2100c01402001503100314024000020550a001241000304961001c5161500d00b0000c500182c00001541500441c81848010303d812119a8040300c9241e11908030050303403041400261745000c031002c000f031500440040c3c014585500030b840701c072035000340002d080c00069010a18000c500071440c0e081c840c0218003017198100210502c40501071a110132420070a1240001e0800341804c0d1604c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 829365296 1250 829364046 829364051
    0x6010518060c0a140a300c1118012c07030e1203071d040b01020c0d0609020307030803190615260106092d031b0812090f0d050c04 57
    0x10341d02c02810002652441d4000c1c007840700c08004800310650700c0c41412030889840c002202c0c8150b0320b0700206000c0940d1100da0304030050b60403081c1000c40e40004040c0c0102e62881200030b400c01d15440b88580c2888882124150784d1207541802d01950319110441ca04000354524045680003900c2c030041403d420a0b2282004184110921105414444030403001e04084001204004001d41e1001d081560981000d50300000d0442940600c01030f1003030040b00ca07000d680000c0c2500c4081c03c101c96000f0070103001d44030015415003241c0c002806c0c026545d0040d9203059000c8140000c400328a071810b0f074541c05030721041000f2032501c41d0000103d0003080d90384061158400382c10307110403880c041d0203060940b0380110b1a05581c40714070203007100703c3c14007440604c40c00100d0b05503103080f420041d0884031100340c0300c4024010325565401c00101420303150100f481389400c600280b916420000c9595a542c503d0b441500d9110300c00c28484215200d24149103e0b00c070000a000c0440c2c00805e800441000c240c601 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 829366546 1250 829365296 829365307
    0x50d0f02131803090302010807171512070f08060112151e150f08120909060303040b030106031a061e0a0c0f050a1b060509130615170601051806 63
    0x700340040404071000c0080c4000c0042c0c000803d540190300c40d041d24800d80b00c9140c3c90300c80301da04607a07800104041040f100182c50114242c001461050a1801c80082040c1c000140c010340c01400d1400d954003a44400020398020b200c400400d0110a01500c0c2040c2d0280e07000034580c4411030300c1d0740c3d1030098030302843d610342c0c1e0800351110740520891200703aa80b0040c002c600c8800580680307811940300311144030020303460100d01c03140040360039464018050380c041e0600403d0f20410842071005091503a00d0b100c100300c0001c0004205018500814040d20b00007401003a4580000d00b032150b080c0c28074030030001081051004c100f003160030504c05c80c0c41c02c001501c42940881c15200001c40000c003070868441c4010050800c000041c0f144500781c461030080c1440c54140310000c2e06041540600400703d40280814640c40c01c11120410f0384c0b9a22600c0481d03842d941d0107444610400740d8900000041c1080c1b0b804a4207003041d43c0250704034000f86081132a05007000d181182c210600380c48103100b01c400291 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 829367796 1250 829366546 829366579
    0xb07120c061d0607030612020d060506010903141c03020c0616050c19050f01090b0408030606120a02070c060914060d0212070c060606080103030e0d0501140705070c050d0f02 76
    0x1189140c50b08062800081840d604030355204001c4910320002401e00002003003540c840561504510ba002c1d09421008049980c0c940c00f4000040406040280d10040000030841410100c207c44244d00c015100d00c4081902c002200300e100700320b00040c035004210156a540c000a01c0700e0348516240c1c80c8a0410a52950403911445074850b1840c0500c65000c01d07103a090300050750030012500c60350031200f0381904004a182681c4c80c41c54058171403100200041c004ca4010001107a01c4000148114600103440c1c01c100280001034035000c540540c0800c040d4104001104403401809140c00d000700500e25000400d14110f00c00c030602d0307004640108491503000b4042e016281101d180300c0181c180c07450440c0008200c90301c83da009855440c01c0c81000611a402014564145c0340c00d59110360510340010180701a0740c201d503404560a659600302c100955030100c20003401104556a01613917840503003885c19100c00740d07270890780c4a01091014480010000c044241030b5070f5060ba4030b1141c040d081d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 829369046 1250 829367796 829367801
    0x905030c150a0221040509100807171603030e13060803030c0c01060906060203031f0305060417270102070602010501051c1b0306051e0403021213120605090105010b07120c06 76
    0x843d0101c400026000f004c608a0400a4000e40d001592010000d54411440c40345840da81e10400000741c005c5507017401131240e011502400500ea0204481b441201c0620520886005600a400080008000c09076525080c06440078001e5202000e02040f030401c140c0e15201d1002038090200c5800001e040402039000303401010040080b00402c000a9655050107512030f4070803102c6600c90711840946141e844414020385064a41040040030709a980d0340e01c044181680008000c3c22042c244150100003441041c41490220402d00500f440074100c400a4030b0300c0001c1e0800d1065904041c018055034582001e0107070201c1c224610750808410701d08241d6000a08a00d1550321070310154004020310040343c000c94051141503012242032841d0780403a40d8822000d503401070060700544400c81c1031400d15409444055840c400310400f15a031041404040c03604000116642901c800030850340840a1140c8c90042040d0500c80d480e041399a51303080c50005448000609012643c4030b044c0500c101035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 829370296 1250 829369046 829369063
    0xa0b0d0204140f0112110105070201050904180b090708061b04080303010801051014060a140c0a150c0c0302030a050a0e04050712112109010f1404030905030c150a02 72
    0x3074010095281c41d40150300d4030900c122044480c850120b03000040101441091482c595000b8180e03200901c0c6040045540e43c6c04924142e0410a05118908503580c07140704251b5100140010518110128507045401c080014081d100680201c04100f007007400c0440d00c2c0b58452620020642d910404508110b218000e50300941c0091101100110300a00154030590090710082a00704000384d07940e000b2107901d03039889905d41e0070100c140a0040540e010705c00c407500d40a40f5030340c1e143c1403189000310141b8000c0800d0090320034241c050104919040e4031f100c1d8101a00e041d1501200c9402144c4019650380720b4242c401c03007080400240aa001c0b0f100c0c0d2031108003140010018080c07130901d04001046081140075110340d10f0f1804030301d031804cc0c0c00442126034401c0c015403e8981e1003004c2a1a00b0340900c02040700e0b00c01c2d5260b0381007910300f00641c400d26901c01a1001115614206414001c25182907a080180a98045242240d00f6582c03450001c01c0384c00310301105070341c685000c4800c90510900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 829371546 1250 829370296 829370299
    0x4030308040236131101050d0e0f0d030f060e0105060304030504050405040804180e070512070305010606091a0715090203010b191406070f0609051e07030b06060306090a0b0d02 77
    0x141500f00c5044911003a00102e20040029292a1611010888803021061000003007004e0501961064194000d4018080800108000140c98103181045a0505250221001840d00034032410b0440c81d800d032003680d4550082c2c10040101a007407030700b070468004d010b00071144940004070029041500c114100c901412020304240500e00301071a14454540003030042900500103400fa0880c614894440c4c5c4056040c0f10b0004d2074042d00d000284400e10709052156404d0b030144280c04008900d090141a0007045c40da42c659100a10b0010b05026020541107000b500c19402c10141c4080b0710013031202d41c0c4689245200003007082961000a0050440d500550b0300804030811680c4004098031a540888130801c2621070703c1100310040184a10900070020401040c400440d800b20300c0301ea010510141c440c004903039198840c004031030080704e44558001d507154010700040c01040010084160025002d44105055040460000d115020014607a14145a403410214a10b036a00c1c030340e21101a80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 829372796 1250 829371546 829371589
    0x4381e06070606060e010305161709011119030c0c03080103080f0705010912020c0a1a1e040b0703021006180b130e150612030f1305060c0303061e06040303080402 71
    0x352920701a000440c2042106c0c0440c1c901400603001c0880d0180c00c43e40d0324440d039a9080d21030300c1d801405500f811b010f0710ba03800541d0f0f01c81c824500d0b409030b00003c7c8420500c880000543c050b5404000b81039407040000c060800c0000642031000940010425041d641d2015a183e154401c0d11154140b601500d81c0140c8a5802d000f00001800755080008881c05d074541c1c2601c400c52040d8090108401d40380c49816004080241d200000035070000c09031425507145407801700101d220600d1240d003030304690004030740c0940000301e42040580420102e80c68010300e88040c0211881c1145000718009c5090482d8801d684132102c0c0341c416a00c100100354001c18406003041000d5042403100d989144103004031190442e0940424800c0c0f400507460814110948021450003281861a2a00b504000068418640c41d05400b14441c0d603410060441c06a00e04000c507101d140040401500c42604c410fa485004070000c0030b5403068940c3e5040302e003545d0b00340c1096005030700c852002c5140342c40c0003c9090045ca0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 829374046 1250 829372796 829372799
    0x90a0c02101e0f1a0603070504060804080c15090f0c0a05010f030e1e1e12130e04031d0111190c0902040e2e0e1504381e06070606 57
    0x80703a1301c0200540d00010000340303042008030902880c1c0c4415108407000ca001440100070083c802d00c965a413052081c2020350400081080e902d103015036100c100c241403950202000380c1034600b00b00300103900d01000003c10340c407800b41011070b031285114003030141000402961078040d60f00a400011500240034200e54102c12000c1d100f030244507410030305016a00603c00844440103004403500022400d90b0040c004c60780d0328241451040c0d0142219040c20814108001000c04102d21060f12890184c1c07545010581c25030b0f905062030100604050600c013030809400c8801c0310000b00d6070b08d03080c02130b280c09a015180c0d082140d44e0048990181015600000e008141c08004024580c0600d140f500d24115106031100c0040511000032480c40c103e00405008001000549480b10b40218800c0b80861108030400e0202d01565540c0c0b03043c0c042180310111040c02c443d14010070034012440908103001b00c9111000003100b803d4002d4195000300c6403400c81280c2940c42204450005038014801c11080307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 829375296 1250 829374046 829374071
    0x403030912081504060515070219030305030f0115020a02130f090f05070e010e0f04021201021204110a0605030a0e0322030203010c030207050c09090c120c090a0c02101e 74
    0x100303c901002c40b0aa94010034004c0c103080c05018181c4200030081030007207e50a500c111203800110342681d02010011492161038580445040554020780e9080d5a0b46440303454052600e4041c0d01c001c800e0600c940030000c8450303020481420007581141d0031184650390b032035148060031240d10006802454238150b24200000e00c840c0060052144083d04d0047c6d903590500007207032000f407150500d54203180c8000307441e861507001d600c0d901c02d00c0141501c1100d0700b801030003402c98020003d0301520303542200620060050b6200e0940c00712400b00c520b8200281480c0008100f400040c06200c107984d10740641c480e46450a0050300c1541c2804140b441d1244c0c0c010000f0500f414282c0700c140d000f94640f02404840c10710a00031035100c242c000e4024070024801401340030310104000c1c2254228051142100403980c0c0381c01507226040c604000920100d20440c0c200603803940007802441c1d1461824240d6060a41c003c84d4554102603410000264142441400d500c4004120040a030861500d00500c229 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 829376546 1250 829375296 829375307
    0x2100f0b030114091c0c030e060d02030112020405060a060507030c05070503190c080607050702010f020c040510060215131e0c090509060a110d020a090e040b070809010606090501080403030912 84
    0x3c0c40800c82100c07107210b21780c003100d0369012101c0c014400098803070006c4d4011134042d00303401205c103001a00c09440c0c8034000e40543c0c00c03604280c128050202c100f100c981c0a5113824028036800000449811034210324088015013244a0b540c0000c09000140700c0034018084140100801008050142c82ca068140c4640b00e100070020501200d03012200301010401c041c00103111071046510ba1200d40c5072900680041d4bc1c45000d01d10b11b10114031401c005d0a407143c41e1030091a00400c005881d2001842c10500b02a0604145071082441c00d0000350800c01e01070455021030390002c1e0002c3c812401d40c01a54120322a4007407100300500202800380002441940c2540282c3c420f00b1000b094075983c1d1200b80d0110107031100c200b41422102424411424800084c1e4001c0c4200302440c01d080c0354055684ca101981d0010407182521815100742c108003101b900048201d03070003240071008029540c2000c9014110701c503a80540343c10418184000b50405009034045003000790001180e90380040440b100408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 829377796 1250 829376546 829376551
    0x30903030c010203060a1a040501030f020930030306130b2e030506090f010915050d0809040b121903260103031b030206130303090b01031a010f050102100f0b030114 72
    0x90b40c40402c0094818540d401c45980c00301f94141e0303146010314120046000e4684110380ba02155070070480605507698203030388181c0a052109503052080000384070f802601c2c2c040720600405400c00c00070440c2c190350b0050055032981205200042500f46140400c031001003810804150000d0341c803501c80119002e01c08841e410000f87d5041c0b12690f155014440c0d801001c0da4007004075501080103000c040130310b13000302c0e201448030b518001000390307200001421010840d1003641c1c1c1101c0002d140d803050810340201c01403000103840e070112035000074488135509d9525800c85030f06c080501c030043d000c1511651188280c0c4042c440860b0000d0811100403074400b200703110485c007041e2180d140c0007080d515a882c1c80060b43c4c041d0050303d241c0d070b0368604c210f40c000c002940c201d042541d07400d003450000d103a508080340614043c59851300354919205035541c100c18103070070603111819803200c1040280c2c0d00140440e1038100c2a000407030324902c0751841d60060aa80143c00750703d5401c0070304102c20840300e19141d61 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 829379046 1250 829377796 829377799
    0x905040c05010905061605010b101d0a062a080d02030601080a0e03040509153c0f10090306020408010902040f0c02060c0c0a120e01030b0a081e030903030c01020306 72
    0x294010760399401522107038841c1c802d65810480c1400b8005a401614040704000303401800042042e00c40300c4000b40011046086400210316040300c82410401c0450540303022901c10384180c980a81031400c003a00940c1440800c401d1591541503500c1a0106510811002540007410a80312240540404041d400480d803490008005900145158802e401001c07080c00c000f10243d4a000d0800040c00365048006100c0080300849804460180e111450400d4040503030358105140b02504204460301541c01c0d201d120107030300364002000341541c2c80401005203a07a0841d44a0f41140b0048020784a03082e0700e50010b0700b940c0c804580065000b4064000848551080754108120000100f40303400f00d0b00554000f40042c0e00120000d032146032031400405014101d00201c2e0010b1380e05a0359182030060f04141c51001030f920003041022540c143c002c080f02e541c1d0403906c40d41e0450514418954902e9400c0e00e01403442001c0503194040c0105000700c680f00038000d0700b5695945101c201c514040d600c1510003d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 829380296 1250 829379046 829379063
    0x3030608191515080604030207030b010f150302280504050f181b0f0a02010c1403041203051302120703140a0506070e0a0e04110103150f031b030c090504 67
    0x501c05102203055440603541d0019082103400018000708005180000122201081d0345101080c8a076081003003c1c0b1881c400c1d80140081c0307065203400302126006a0180c07042215940f000d001c0e0000e403c1d80086c10300143e150040c0c5510162141c03e841d110000300540142e0f0038444035040306503010380148140c4405841140c04001d0321000e00c03020018140141c84040505404607001691040240281c1c0c0c00c0001c405091a0b02c1d4160120a94003211480703003d80c0d0b64204900c0801e804c405c0c030003a13018a0010244c01c6181680315450390240f45d841c1d0400301030b0784000064040c00780018244904d5000703851710030032421203490550360303a00c180000d0320f000a04c00070003850064000742c00000e080c0c0c0310001d418940c54010f400e03030307005481c124440e40c8401403040105e02900003001e0548100d0288076040d403421039460024088031358515510207454501035040c0000c0000038508402c480e4050744102c10321004800b600183e081d00d41005001c401c0800c00003842d4401c0c0d40209006600840c0700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 829381546 1250 829380296 829380313
    0xf06050c0901020307060c090302060c0703060b0906030c04091407091d031c051e04031d040608071202060f04320919110d1a101407030203040801060303030608 70
    0x1520000d01400501c540143c2c0204614000212184c0107030426243ea0704102100940340e40c00a0b0300d6401c542c9241d001988040400c0080c2f15040c040c200d524403040d035119030141400d001080d1100c0c4098100c03030143e5216903c2404008100006010f881c0c0301e8070589600607182d0100030090600751661400000f8003182c0c40d13060090210440e144020000c000d40d1007403500449280190100920400c1d0f480040d10f840b180c1c180b045000b05108621a5503280e00c00104a0191001c0d0150004c07210f004601d020740038801d0a60029405003541c08a0b03071402403003e0f107480061010b03c9000104514420041400143e5245042a480c0c0700c421903045406d000000d4048800f040f8685901244e0103402d2001180014100d803c045048014180c40802c031240620000079540c0c5c003114209034459034405402d403d0009a01541a4003030048401c100460244003008126120742401c11855038000200c84040600810031100100751050083c007140e99641009401402c881c843c40f103090146604 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 829382796 1250 829381546 829381561
    0xb18070e0711011b05030708130609060c080a0605090711030f0c0106031502180103091a0c0a030f05010803090906180103051f020a082a130f08030301080c0621040f0605 74
    0x404c840c0b00d2000380c2e42d89045540e94441225000d00280000000e07501901076540410614060f060b400c41c01900042031941119400a02e4418010031000c0c4040c40c040041c0429a240c04001c0d0b0030808519000e55100d5209500e68103500c507421815042090024204542c082c06400410440e4040c140360307080c010541c0c20308016841095041001d02c0e15505c00c20016601940c814820a40200a940d180b0f1583c0c45c20348260748420b8a48601c4d040000c01c19485076a1b060051500364100e03000140b00a500d00740201d41e4a001d01000c00b4800c450a00c0010340366140c00c81c0380b6883d04442c0a85000550b507a080098481680c512400c10b07a031041c02005a070203401d03000301d0700c5200160391000b2043c1c0c3c544000c107402814108100441c40c3c2c03129003801a412600300a40302340c40301590001289441c00d4980d0000c03112603030204120f5042403004005082d004a500390340c0c5001614201c0c1c1d180103040c481629113440034100c12200000c034007404140241d40e103404030707424400c101c10419503d6210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 829384046 1250 829382796 829382831
    0xe070e100501081f0501030903050d020304150605040b061602010e0a09060302090c210a0f060b090310090b070c02031603080909010503061003020d050c120d0212070b18070e071101 79
    0xc0c0c21010141444410040c0d540b0072352102d40040e02904c0c0c5141441149100390003a80e00685040e0783e94004903280d155805200d11405c00285021201003102c0034405001c24200d0040304c80322103030b02d03a0ba18050025a401001000702440c07000b04844190703500d41100e00000d0805001c160b008924502c0041d11009004088880b441103030014a140c0f5482604e603d40c151000174460320310700b41c45100500c5412000d001d071501901c2105a5a603d4010850030b240c600b45001d0700144000341441c090308003207612442d14603000703521842d00844c1072502e400403a1400d500451403c0400c09074840010070300a40bc0040c0200c40c0003210000703840d99030307a01003680ea45026100060020800e440c00c00c0185000c03640100040e10030b00c2620407220307510340042c0900c07401040345007481d0000644640c88580c10f100080c0c040d40302035401800c00020382c4460485070001000c40581c4440c4141c1c0c1005c2090810000700100f036040c003030030300c0c0389056500146071881d260440481d96080c400858901c2c1001d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 829385296 1250 829384046 829384081
    0x20a2013020c010f02040f03050f1b090a1e05150f010e01030f0603061404051213170c030a03050417030301050d020d021804120f0216090e070e10050108 67
    0x420085403880d1600c014030007540280c0031600c1d159600e031107031107081c0403138005000204001c2d03110300d5005240d810903d0500c1d00300aaa072343d044d042845c1c01c08403c1c0034a0009041d04405503481c01481e6545000b49006201c06d01111400050460107040e8501c40390b007042e0711400b03143c03a1888140c0190030611541803031050645004c80d101e801c0b1001294803a80c818058610258004142c096494903030b501200c2e030b540521081d03a03009400700414440104844180781d01100c032003514100156410103c0c01456000d0a500c258030700c0409501746e1030030420080c0c1d00c0320007020740714940b020340b40290940c0e00612038074040c2c1c03021800f10b8155a4011054070304840c00039050f4070300780c4100d500b08103160051003000c1341d00540480c041c1103114090520035200c0c0c1e228051540c420007040c1c1c3d002d00b45041c04054581154000542040c48107007900000040b1391007404041a6417052541b207a06041300d03500b0411014405404000e001550005550100c80b42a01da80e9407a440c0e8019542170076044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 829386546 1250 829385296 829385299
    0x20f07060e030d29030a0c03020103021312050c0108070c0c030b06040207060c020106031407050303070b04060216050c09060d08070314090d081e03010f030b06042a0f0504050a03080313080a020a20 86
    0x1f801c10410155009030000c000e050016920004050388030520412070780362410f03007529543d000300c181c16400d50b00030024503017040d04c5041440c014603807640d41503d408020b0100402c020880e20206401da1104c0c1c05886032a41c0c07000c020f000849079840000d008142e140320035a40c54108052210769520f000c62140207540c2c000e0041d500e80003060721543c2c12843c01074021100c083e0f08021080210702003103410261944220050101c0800902c1000100d4002816451280500d50920000180c112b42110b40791541400d010f02c01d45001340019800340540050503400c6039203103000004106404006054000001c00d9000c014000e812104400b0300090155110041e2208824408102800000d9030303c200c0080010404d440c20030b010b80e44200302c84600300201d001c14001145044d401c2140d01307542c0140c9141503410720b803405001804c0d03c201484068101c00340080810000410190310701460364000403401e589000d02c58009658016a80c01950094404018241c0c1b1000407803400095010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 829387796 1250 829386546 829386563
    0xb0102250e0606040806070c06050c1201051e19030215040807051e0d0303090605062d03280c090c0906050c2104080709020f07060e030d29030a 63
    0x401881c589004405004507501c81401d000014024408125503482035040c2d560f001c003940d840b0325040043e510301800a80c1d11600c02d0107150b424951036811581100c00c00c036a02074140078074082040407884510034268005070507a40280c501600c490070642280c0c0700351540040d19940b8a65000e542c00b83c0d010b451400d0300850340401180c6031600001002150b4040301c0b06101403442c000400b9403032005011400700e52a4020501480b0301d9100e030340d0380302c1029141107102c1d9003d2881124400e05020107104aa044420070380c2d881c0e1000c00c8130240003404910512116201101a9841403582910868010a0807203001c5840c100500800034400015150022020b092100580d080e4011600040003881545046c0da0420030001819050b80d0058240a548a040c0380311181810307503941103403c04034010843c1d14410600348088801c5c49420010018050a140c0400340c01c42c0304132485080130f907041140305800c040b00344129411210803410380d00b83c00312041c0145600c68100d124007504008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 829389046 1250 829387796 829387799
    0x190e09010302270f0a0b0607020310020f12043012050a0b03010207120305060a060c1e1b0609060908100507121508070b0f04060509030c04050a0b010225 67
    0x1d00f4000d0701000700d80c0e110300400000026441c500b030b4000c00c851500c3d030104034034140101c00e04a8030030000c8111059a0030b500d8100e650300840d5540b41200c0403640d101e54001000c00c090000d100c191220b2400a01d100f04241c206428852015150400908000160b040300c10601d40c000039103892140d00242c8031100c00c4110400c00790700414004000340c000300e80f1030310710401e0b0350386c09c0c4000e108082c49840290044040040c0040c02c86a00601003030140304842814040d06411400407401e09038002d1030302074140f405500003000340444880050040c25408030740c000c038400907112a42034903410f54529281030743d02c0030704845000452055048603004041c00008005c866002164040ca840c00c01c0386040900b00003040c211610380e00700c14003940c11481c05024090013440081c0003052140340003418900e01501c4c9080d244144c0c82200702340500010043c2c2d003601d040c0602e10102000800c200103030b01d00554402c002d00892003541c1e005009601c825101c0100d01d038190008080300c0d40c44102703401d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 829390296 1250 829389046 829389049
    0x70c09020408250509010b2a03070807020a0f121e08070210110607020a0b0a0e12030a1401090504060b1807110703020910060206010812270312190e09010302 69
    0x2003101c0b40743d03103403001a480400f04403905c9034000b0320b0013440d0101107540d813590b40380214020080f8254170724580551030320001c200700c40000261645180c005c0d030034513a108014400510301081c4c0341d100d4580b031910982d0000d0614102e20020400c0d03801202c0f4200b40c000c201c051706100d1811400001c0c2044002d018580141c1044040d80c0c508804a02b0718401e0649207040c41482c0c018100d482400584c440c603010410400344407459a000340303001400340701111804100707585032450344060584081020000403421807545d0081c59850381100e84814940d6125040c18000d044103c40170380b656402d1101405050500716036041042d0a000040315003600c41d007104541403100c0088a0002c0c0c40740d500080003595039421aa40079444084240840c40c0c9402c1001c0c2c1485c6050f80301c4c98070b6804c540c5224040044c0442101c007908518481c00b00c903915070500c4100e151400c5034107039030944522014058003000010042c002d602e40c0054142c0210f01210382100c01c1100f15900c56001090a001000103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 829391546 1250 829390296 829390333
    0xb040605031e04080901090611070603050c16050c040506030a0b0a0506030106081c020d05040810050c0c0115031718040b060c160317030c12101a070c09020408 70
    0x1c5140c41e00c0e034084080c80b84541c0d0080800303640544100600103a802042c0d030b0400003032401000c007414003d00382e611039896543c0380c04640c0306040606403120300007800308401c14115900030b03000c0c400f40141a0594181180d90791417030b4000394001d501d410041042440c2c0094000c00b281e1740600303c5062581c84101c2007000e0701024013055055920f803100031450300c00c20721002c001c0e00001c50000d0440c1ca00170304020718140c0c4c40d80881c2d00744842000288403400c2d020903a0812546e140d640441c580c0c46400042c0414860800e941c2600d51a1803000c80144045688030011207014011282901003040c5864505100d00c40000b49006442101c410740f900f06070300522020030004103000e0420001c1c04115040016501c5506401da0f8030500a00402c03286090030042030440138012400c601d441c1421001c207100314020600465031810024125040c0065910040d00b0b03100b42580c8499a032006000c21a08410002c4a410300d96400202d00460300c2c0c42502c0498125078001e0946080300b0250808 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 829392796 1250 829391546 829391551
    0x2109090612010e0a200411070f1e060f0b040b012c04051f0803071a090708071d1501090620010c0c110d2604080d270b04060503 56
    0x1075403036030302801402500f440010303c82c600501420070380c20502c907607050140c400c8401082c03041c2e160010b507c001c0c0711f8490a403a002907000e424038907900c0240c10281e241390307880e4000703564801148108404000098208046050001000b0300200c00d04d20100016282c40384092400648182082d41300e4000000e542d4104102c030b400e4080c207851401000c03e040d907904403102c440f00d0703168542c0401040c20303400d9210002d00728040070310704110b4140c1d03821000380d040d4031109407905070802c0401e884060034408003005058400446240b0756032841045000e0500700800301040f003040c00000c0149070041c030648101d0205035030700b920032410003406840303518a044000d10840300900c07440303007a680c0c244580c4070300300095111030740749007000e20704520f95900d540b550a0040301c0100382da000003411500200c4940d4800060114640408440d103480c90045074850070303140c400e034584c4052081d000000841c400c0c0c08000301c800360100800409002100d01e100f2102c1c518000c000800096205001964 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 829394046 1250 829392796 829392829
    0x1501050d0609060b1e040e010b071e0302011a01080412051e07030306090f02091f0210060905070906090608010e10030605070909060f140f04091421090906 68
    0x1038002c0c1c842900300102c800301d0308200204c08000495070340c0d4407403031000303580a9600000c10030300c2d0909004072140710910602c2401c20340280840c040c002c0010303460007040200c0c01d240301c0701c16002c03007070034024040c1c152001520726a00300150588965440740444a00c500c0e0807451101038590520b9040300e4030350003030f034080c240d81c403840d00b0200804200303400620000780079540c081850f5050408080031204000182010103204000303810203078444510700f005020900c82c01d040d400d40441d500b41c2c00e24a410a04a18061410302c0200d004020707a80040e0040c1c000d0ba8441007200d880320350544a10049010300303c04101d0034030040000b480440c0c0300e9580480c6820f420303008a071f600c1da20a008e42d03606a8a0304041401d10340c2c00d010601441c482c4c44003c0c00c1031900590801e15205042c170110628050ba00e003c2d80c080c3c3d4500000b038541c0d0b088501016801501c2481d0510740d941c1041e200c2d0141e5040c0d20200c1e20101c007103072355880c542040d030b444424021300c0c12243d6255030040241c501001e0050381d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 829395296 1250 829394046 829394051
    0xd0510080d0e0f27070306060813021005040b04030c0f090203191119110d020c0112180203030316030b030606100c0515070306170703050a0b09210a12051501050d 71
    0x80e103000c0d900600e0021343c801001d5100300702d428050000b5054907500e4100404120070f01d4200b140c1c41100c040307200345254041c0d81100c1c100c0e4040100701c0d50f0b8403494200350150300b0009400000c000c0340c41c6240046a040100c2d014400d91a541000e051b488143e4141c04026016429812804c2071640444140c0da45450202e1400280c80d658404945c41484000c0104041054902c40707034800380142c034a100700740d1014001381e028030f000207801c0e1040306d1070100c00c003a5a030784072070010043d071401803241613001001c49071246807812016800e000c500070040002410444120a14140001c8581c001c00c00207000c41c000e64100f401c126003143d0104401e49851082c204400026260401000e008041555000c0340c041c0c105a52012240e0b0281e01000d01c6a000080c1000071a00c040b502070001544a070604000307071200d50440d440d0406520100e290184828071100c8010b0310040100454101501e800170714124296902c030403103008841c62403444009951a49182d84118001c0c0890014001c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 829396546 1250 829395296 829395319
    0x7052404080c0a120e180f012601140610090b0708090612011403070f030b1b0f0301080601050f03010912210e031225030c030902060d0510080d0e0f 65
    0xc40c0e2104a411820300045058100c450645e800c2491489a0341c3c08000c8600c40141016007030510755403414400c01c07a8031101c40341d014140c11140d282400d00006a08000d106001082440c9029098162103540c420b1569a0303100c0580c034005c00c2100c08a079100e1208038101340460f00c80c03110301c2d07105180044c1d00203410483d0704103c40c0c0b003180a9001c0c0c4800b080160000042c0d07824503180c03040e00e810020030044145401c00016103080b442c0e942c0050360702c00c08500c0c4c24842d80841824040c42d86045134600c40030001280482c0001442d038101c0c1d104a42d8050040054400c0c14206d80d40305902034443e650101e43d00c001c040c05003440460300d00408811514401107401c00c201281d14407484a0b442c1d40000816581c00100c1202c800d0708581c83d10602c0e07110f9540d44e0924004905100704000a1645031b486040350140268494960300c0c0e0098141ca5550309404c0c003840c01010100c0715441080201017000c0790f414400100c0849029051301c46800d418408810041120001c05101da4040c2c00d4031003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 829397796 1250 829396546 829396553
    0x1511190f0b04050609010b0d260405130e010524040504080417011a0f012703080a080a06090b0a0b130b0c0f151006080709081207052404080c0a 63
    0x1e00e84201d0141010303180034209421440d003941c0500074602d20a50030301c4c3c030320004a0420103544406440900c2c1486d0100500c107484000c0d8011071780b101d680071b111078680940d2030300b541e00300480000c0c03042c0003003046e9581e208091100e101303240214611101111520521410700c2da12868000340a030025a04095540100b0715040c011601c41e98400c1e512100c40881c82c1090041600d04c1c42070444d18001d04031100c100003020764004071404030405442218009410803070641100103980c000201c6a07071100d40a0001d01105416294844e80618102c000100c2800a1007107008400000702103459052038052440102c0d08104400c0c0a041900d65000a00394003241c020150341c0ea81300098801c0c80c02d4041000c0c200700c00e0000702c8001c0500c02e401c2100805040310600203807200c50501840b030707490b842c204071003600c1140c002402c0b503c41e07074400e0360854121001500f596886801144c0c0505014803d1055041c0d08661000702d0004040124000507071036409080b0041c1300030105e070806451501d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 829399046 1250 829397796 829397813
    0xc1c0b1002010603050c0d08070b1306090606030311060906061e10090612020901080106050a0c02030a0b1b1207030207030536030105090c101b0503041511190f 70
    0x100040d0150707654110410030814248203640410108031190600b550858490f0181403280d90401080380401000050881c1640880861210742000042000010364a0014010b18103804190040340c0043c200e11b80c40b030000a0618403403107451016280795190b060520151901e1070226000030054207030700c284607407104840c640d85000942d031032070030079854064060328510903035610a10850041003204144d0340c12040340e50454400c1c1c500b955940d0000e101c00c40e1505141d0000944c503004d05018501401340340c0105a024410403c4005a2a0301811400801d8854454090045000300c0300003226203020b07901605006000381005441d03c60308503160141c0e064014001d4846204040c5880c3c5480501240c41c201c040d0300360001c12441c1041c1c0304da44e40c1e46c5442c0c4625881040304002c1c01840c2071256041c8500011000c03546000200c0303e02d00035460350001d008103410860300080e81c100d001c0c400d00b02002002c0f26640980701c4040d409503801d0721141d544a058900541a005081c005003040c2d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 829400296 1250 829399046 829399069
    0x10819020d0203010f05060a0503221b0801180f0f05010e030a02010504030207061b020f13020403080714010b0a0e1b0309030a020c01050406200109050f030706050f0c1c0b 75
    0xa440060b503d40c141010328001480c146c1016002d20b106100d032011168101742103036000700c00480d01d221192005c507042c010030100c01c1d00042c865400d1a20881a0180600e010402e031084170000303100101100c0009159100030380340181080c0c02451104011420096020010a00a50000c0381c410301000d5010701e180d0000541c1c1006030366070401c000a0550501049028014038600b2140c078a480e081c0403031150343d600308040e1051303415501d1410a0359800404540b0038049200c155150380ea00e083c071000e40d0f0050501601c40d050b09203452100c8041c18884d005c0c00005c0100318004a07800c6c000360607500c0000801e2080036008880035080310b0307504403001c0c40c07241c1d880340000d5a6030301d03003004000d040042c2082e040c0d0610106000612800780c1004124446c58401780c003640001040700c0078103024010540c0c01038070360b0042010003401c00801000410006000350403e1080e52240019003a00302d0040394114107403d4140000710030014051500b180103d0155000b0840328040000a000e69854 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 829401546 1250 829400296 829400317
    0xf030103031106090d0905040e0c040e030a0e0d030c200411070203010c080702070b070c090507110d080702031b210c0c04060815090a06020403050d0801140f01081902 73
    0x1540400c182d8030800c0118a60200c21400500610802c00d4000380c0b400801c1e014162055460b1100b080319050b0030820040c9840e0010000c0c4070a1800c0d03e519901c2c1e9000c0a24080010098914036090341488a08405019130558512070241c21581b6104034503001d070510548002445180c41a0301e130f4890280102c500010401e6654a810500c10182110410741c4410305004080c0c0401c603603a90086060340c1200d03140c400265403641240b4142605401c00d41085010615003428490261b40c44134821058481440803181110080d05058807030b40f400f2214240182e00400581d45040b1180d400362140748401c50440b40160340100c0b1903003040f0505201002c1da0702000c02d04810070b440030480002c030904151802c1008509208966488500109882c8a00048500403600c841e204200d1f41120681103401191615102d1a000e0b03160344012801c40000750f9201c00204140304005842d2180101c020915a0500c802038010349071900c0040440d114000000880b040c0303480c25000800ba031b941d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 829402796 1250 829401546 829401557
    0x18010306020d0c020c0307031211030c0303070e121f0605030a11030607091a180603010602011b140313021f0905040c0f0c08030c0d020d090b01062f030f03010303 71
    0x80c892055011070b20010203d0301194403440304444280c43c086400e4050f0794100e500390a04140c1305400fa036032200f000b030a000d214400081d201443d00c1c0c010000d180611031503a40c80c5c60806003481000703400c000c02c414a03116034020718100c4292004209403040311203002034010440c1d0755100c00007420154035072000c1d038202003440352400d6a880c0501165a019030b041c1410340c040da0405620981c038100b0b9403c4035259001c001008461403421812403003500c06d0040420755250b071201c1c4000d001c0c6c070340c507481c0540c880818015003100da801000e00416034010300d01c0090440c0e0343d003060101d6800750248280c2c0c03c80082ea44030007600d42c0b90300c40f16104001945070802c40c646440309000481c0c4510703c005040015095407051040e034460b40342c1c0134a40c0c00480c425240d84900c3c100d880903100c0e070304440034a180300103040c0ca03403510300d6046215454094541102203030b0361740c40300b074817111000d040180002400d038581c41103e02c00180280c001c09101011a0300f050418484c1a00560080c1c0041d0089078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 829404046 1250 829402796 829402807
    0xa090308030a1a031603140c100207080d0e060306130f240803070b0705030405070b1204030f0315090f1503141218040903050c06040804150e1e1801030602 68
    0x22030303103c801510b0b08081d401011050341007080c036458514140802441620201c00d0380d044a0b0042210a404c03a1009007018451501c03603030041d54540f0940b003210120300074888038200d0f031402482d100003440d00c060510b0b40f0315664682088a000010030002500380c2e60b0b402603071000707202445840030303035400240304c0c1d05030f0186c07616010086c03c9a9800510194400c02c01302c00050a00202035030040f0310707400e18503101d0302c40d89402c1e0f003032031340c1a040402c04002c00300d4581c00c030130251122580618000e07224610300ca000ca88007201911f105840031000c1d41091042085100382560004240c40b034510310000381840600c40c600340c0744040d40e2003503451400c910f0325400b40400500880128034800c5810314134020b40000141400900110004c0c80380369540803502c00d050184003122041d501c808160b0324149003a18000c0b085030068020300b0500041c2900c0113003114080e12000b03091a0380201403164a288185c0c002d02041d4180150302d8220b1811070078414901781c0c1542d95400307540f14400258484 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 829405296 1250 829404046 829404071
    0xd1202010906052e0b0405090c120c03070306051903020108071403180118030c120c050d090801050619031106070203070905010e0a050105091306150e060f240a090308030a 75
    0x103511030225400c13024400604010304112402103c045550541e0104000d0303441440d40078003405080368030031000303045404000d610f40e1444015407003080c1c1a101008400d44800074040400d008203c001e40780080904280055805001d48a6010201c0c0c50205800070100211211a0f0425180003000b0401c3c408000c074121001e001d00d81c0314040404494054040a8400800310382c2c0c50040a8094140016291036042c481c120000b0030b150003008482840307c400d20000d002c41c0451040100c25480c010100e1007074a4145842c8025642d90540c0b80f540701c2c15034070703010f9117440e0440d000d42d84618200107807001a102800024001c01044070005642d615064040b08034110042c0121001403800005000075641d14690542220800700c10709072801291401d00c00605030401c5202c801710121000051444129008078481c88080e43c0d0810034442c8003050040d80c1c18815078980c0503000c05580603008014072070252000b5203c91802031541a943c2d2144084c41c0d000786c9a40601507221420355816 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 829406546 1250 829405296 829405351
    0x30d09111005210c031305030708040b120108061302010e031509100c0c021018170a02010e0301021201060c050304090f3e090d050601140319020d120201090605 70
    0x81400f080c200302d21890412010b41c45440024285504404544105410702c0010010b4461869101880c255a1512912903045a03004041064001810311002061001d404103000d0301070700d600c24501e07049202603401950300c40c26502039950548540f0007402007012074010690f01402051014040010107a91260f080d502c00c2e4074142c5c10b0000342d031007201c016101c02c042402c20f40690300d001c650000103100c2040249880b03034004082d00000c82d81c1c2413107444000c603251404c4c600c03d0b207a0b440750b444001c00745800e0b4052201c14603900039032000104440c901410028400307030f01c1041540d00e41343c0c40303c41910843e0034820f40d58180c06d40c1e0382d02100d4540b9154094091280d00d42c2d20401d5840c00000600d29240242059140b0f00c01c03010500d1080d6860b4a00c40b403c0700365209090b03a0140da16114081d660203a80068a8440d20905210310640010b0180388515290003514003600b401c61900c840051450120a041c110343d078621000012443d03d11401e030080c20203105000b404884003002c15107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 829407796 1250 829406546 829406587
    0x306020a1b1109071e11100504020d120210091a010b1309020903030915031b040e0705071a0f0403020c01030e0705091b0301080703061d030d09111005 66
    0x30001c200d020039801081c65400161031428044407514030320741c3c0300d13201240c0751011030020504840a0f182400e03a502e40201e6a2260314100030200c950000d8080745680580d01c0c10b07540a908803094071402c4010514041d504101503541e40112548808205484001c03513000d03d400342c500903840b500707056403000c10340380c0340d40140007001c405820014290312040c44e010b83c0f48565104280c0c000303412841514240190341403114014082840c14481c0000c01c07946500403100c416440810000ca080318014a2090360281c484d580ca01c1a1a6500c0420a07a8242c0c04840261000416a081100c02c0e01c1c400c0107a40c840e1504a031038042604040c0340c042d2070a281103200905246c10601c04210660340014444102d92044802003a00c0d143e501514800c50325240c01c1480c4010000b00100d000340b0009107640482c0d100f8002001009902c0441000c91543d0703062008858004200c601100f024940080001078056507000c2c5c083d0441000003040a02c09001043c00716101007030b1121203106a1103d0003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 829409046 1250 829407796 829407827
    0x40501140705030f040c15080f060105030c0706020304030203040f03050f011a2d040615110304060c02010f3b030712031422090b0a0503031b03130306020a 68
    0x4405050108000d041c83c00010185600540070070005424080184010401408009052030503014507560040128030200d81010322440c5160100f541944200d04a92169550600d000d00f441d0f082e59544c00654806407065007144800d00021075044415480e1100940c483c9004002400700800010700f9240c040709441007000000401400c2500c078206190280700081201c3d410072156038050e102c4000341d41c3c0c1c041d42c00514145012452310b8102c0d0301a10091402c1d19a4100c003188440440d43c0c9124500034203000625940c08000194010b019400c0c201031b0908020182401e050390040e10700d00700340d01007081143d800544010030414030500e01035910302030f401f9183d800e062034a01000108070b080020104503418028103615103008c400e46005070541e5156840d0301901d40782c03443d440341c2c89000e11204285002030021082c0780c12040c1804545020700514203044150300a81c110381d9107006902c801d03000c10000602c09221400b00080030f1803040800685a030030b25180100034007071440e44131 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 829410296 1250 829409046 829409081
    0x70501091e08033c0d0c05042616050310050c070f0b01330507020117010e010e01170d18031b0611030c100207020f041b020f070501080112020324040501 67
    0xb503645202c0503044a180c121700c4c607400702c1c142e500554101d900e4801c2c1e43c0044040110111003d4400e0741d01e411800b00070440c9000c580000200820340e0940c01102e10803542d165000035840e01e1160ba01341c00c810342c002800704c21141402c2944d2902401c4000c028070407901c50000100500c4000c00c10010801c0d8401c401c0100082100c014550320098201c01190b18103121001ca4040c04681c894030242d041c4000c5036240703459950b998560f6290020007801540381c0e1409001c00030401001407404002e044101c14000c2501c1203080c01c0644030341941000a0000007000407012001c102c9801280c80300d0303400c0b03c002d0385030b2178a0f00800500d2080120303100841130f04104190100c4020015036040075444000c80140c0d41c01c3c051002402545400d1200c64206090880c0c840f1081c0464510280310030181d0291524800e140c0051034403851903001361343c00318440b800180014045e80903100c916510240c202c4500c0d550350307102c1d0360f0039114411059060842c49410170003042003c0c050004050340d4030494 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 829411546 1250 829410296 829410397
    0xd0f0e060405060705010b12070302030d03091101111006080f1c0807081302040c03020c100203090a080318060c0a020f0a0206070b130209070c14070501091e0803 71
    0x40407480759202d41803003640003052030400c1c08420741c420119900001c0c50813452800d9031341c2140d21000203200c10780c424000d94020309100c0c0c0c06030223503004403540a4500e0307008450340001500c50b90540b070840c52051095410491803410107214040c0a40380303401c010840c41b001154864540a240c2c2c10075103400146e500001c000c4e507049603410b43c00c80c0d00307030078000700c25641c41c442c0e0031720f88032241d401962041c02c081640c0c148075095070051120350201015520050880c52500090b440143e41200490f40040502e90200c0e526102840e00500d40f0105c06c46000e80c610320003498900c0948000384a070100185004800740c04019410b0090742240c090500d42d8030f1070b00082c0c440d004035400589100e03000c100154560520907000c1e0881c55008010700c0031406e051000401d4020a54011248a04604e00721441984001280c004035001650703641c3c489810050191080d80000481103441503410350f010440c50300600190110180340100f00c04500840c514114102c04180000745906201400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 829412796 1250 829411546 829411549
    0x703060302095208090c0405060a050d0303020c0d0f0f08011511010f060b041d10031101021e0a0b011d01140a1805040204060e09030304020925020d0f0e 67
    0x1450108075840180c81c200a12444050f1403000202800f03201000f0f60201020340000c102802070070020111401441c03414181300032a0000c0d9a00c65010100c0d590402451400003a800c4130349129103005401c0040c2854518606600e545404c40896800019400d045a00c030504551401c0c003403805400a501d4451118280c85100c0e44117001c00076507868010000b03100350015044034035048010403049a0b00c072030641c1d49401c1400790440e0146006d11b18108545e030300501601030000410a1105a440c60341d400e407070301d41400e80c92819402b4103d03840083e071000381d90b60b660b02c8400c08050440091249003140c407490050300038440745802d0110340d02c4102901a0010306480b64400d0f01c1200c2c021900000e1b0400d10309500030310149600c1e802001d6150f110b0780045015500c207030340034022a40c48100c00c44595104a4205680741d0042c0002005841c1c044019500100704c03942c45108484146820602d462160b0280400340e8005210485040d621100d05414400c4500c3c0015040d45040c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 829414046 1250 829412796 829412851
    0x90601020d0c02240a02070f08010621030e03030301030b06040b01050c0a022404090618050f071b0b0112120e030c09220f110105090d020402030717070306030209 71
    0xc4042d0281000c2d40c0320b0125410f84881054030084c44000d444c0d143c4020b00e1009560309003500900e5411502a8400103016105000d0791069032622011032407400c151111044400d240c034801602000001c000c200001e84081c00114081d40c0182c21039103640c41d03c281800309840070908001c1c10484108506c0802610204002d0b41c40c550444074100c1c218246416400d401d80c1c1842c140c04140c00028001408020f250b00035001c9480c072a1a0744a031903848506201181c01c11141d81301d4460003040054a07040c41400b030000300c60724403080840015500e848030840e60a007600410441d2000003c0e20301800840c00001c24442000d152410b6640c95120100b41c4404106c80703c28080c601c41000b042c46a1103c458014880010004282c07400d13556052034240c50b05882ca003650100800d891044103944034004407102070300702900c000781950740d0744d0a200017980003c04102c20040c0d8503c035540c4000c1841e03c200c0c0039a0b05036501041050071801000316130740016042071440ca40e40c11003110340c40c2058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 829415296 1250 829414046 829414067
    0x40b0c011514060c0a020a080109050c0a1a03090a06060e19090809060f0d09050d09080105270a0c0b0301090f05061809070b1909060806180a090c090b090601020d 71
    0x50340e0054842c80d00f0341301280360541544c8025805292000041a2032a05502400c481801035040700d242c0340d401d10500080c0321440c001d44044082002a22045c104040d0003590400682000c80d045031045844480441d0f84d02c7e04884203941104050024954500c000d0f0400203201d0342081000c255140d03201c00e80d520a40740420b005220104000c103400c4100c00594226161031081403142400b140b4205071180040c072643c0e00418080a40480d480078140702e02c511a141c03000d03000207108000110702c208180d500c200c1880901c0f84e180f070303a00003600f641101c000030103015045a490707504000318a001c0d600300c0e0114030031907442c0c2009c1148a590300284541d00d020240100d000c15200e01d02d13000d04004c1e0325042020603800001d8a1043c00804044032002107180d59900c2600a49410701126200320070303544541d010030a0b8217482409030003a4100754000c001d4400c002006c4d02d00b039582e2500407240381d0009509550340c07014903410781800c3e1440ca0703120b14244091700094125807009441403054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 829416546 1250 829415296 829415299
    0xf080c090f060409390e01030809040227010e0f010507060911090717180d0f050405040e0c0a0b0304020901030605040807060f053c06060f040b0c011514 67
    0x8408102e0381c2e00d5650100280c40d0b081569041c04c603540051010440742c06034114100056940e040d802e240d0b080ba48400282c800003070206883d030340b841e02c8009480d0041c8402c0748d400780c2d0800c900b00d92141c162000d5001c11031107451070140c82110700009400324400c0c5402d00d003d0250746684c0800c0d60f80c03050450b100e5552140c070006205890341040f0040c200c116860729041010075090104098006140c4400001040c1c05800603503a0070712030040c0301e50404070f841d8056021015801421f03001d2004030805070140d01e0f0042c01c1aa50350002015286c0485076094581c008211030103807420889a82005482540c143e5850b50410b980403c0d400d400510019051990740c102140801c42c8542c02c40c0c0c01160000c90a0000004100c0408020030741a0fa401c8680c000401c600b82030007144511988400c40f805103064054400030304240000c1000528059000008101d400a038207404c0014101078110403c00e1503e030003150b0105401c41d411045070000e408070840d010021450040306a0740000030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 829417796 1250 829416546 829416571
    0xc090b0f0a0513030503040605031f121509050105011412060c040b0c010603051e0d09030206090616080c0a140c0d0807030c14011a120304030f0309090509070f080c09 73
    0x4a02c072030b04035031003c0e400060580c0400117001403c43c1d8010003850069030070f103841c0c0b020041241401c10494150340710b000100340c0447c1c1d001c40411381c5100c100103854212070700450034a00b20354807142126002d8000c40d440232941c540060050400348403c03010035032094003e02860030800100c1c1010300561086000001000a100070b24820a4200380d008550000442d484400c0340400040141250820b03030402d8402d900d040e110403882890300d60101c030f0f005000c4600d460003e1089c0981e039486920707030000e50944d02c01100000b4400350028094501c010014041141482c5045001462a440e00d030300c05078000c650304400e603510384d6120460345901041d040e40d039840794941540c50700d50501c40a4a40d8101d40030051043c1c0064029611681812400b0a20b0140b06420040180f41c4402c24290300d501c107100600000741140b030714029050081c1030000546a43c1c0c0c0d421020380c0c20840303a0240726000103404002d0400d040312640c001d880303008042e111010650002c202e250704014001c031032403072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 829419046 1250 829417796 829417807
    0xe01051f031a062b141b1507020307170606122e02070c031403040b09090703020408060c070c1d0a0506010509040221130f03030b130f0c090b0f0a05 65
    0xd030b54940891050840c1c0b400b10102c414a0007101e1000c000640041d1822409034600181020000c16202c441d1b590600c1c0e001070160461090140f0300b0496602d081a80c8400c00640d400742c3c1e81081030f03500074107114866041c0c011145626a0400c240036010038001c08a000c080c52400b00c0100c0c5520440f0442e0050b00002d08842e110183e0512504010400d09880010b40d1303010b020100c14950203990080100994042c803590340d20303640748900d1040610200341400f0000007032501c1c892003a000782c0700d442c003d07040a403a450350314100001a220710820301c00c0002c101d401c019540452000800e10360300d80700d1128206d030300400c0000c00700170481d40f0f03040d60ba003002445c960b009000b921203507070000e0000c5440e0002101007800c010b00300400d884840140000040e20a203240801d200e5082d0320005441107404641d400b90007a000ca40605603011201207194100f003076142c0f2400014103010140030400c00c0c005d84c40500a041541c0140c9914041005950304030381c412401c0314410082440d110b9030b2034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 829420296 1250 829419046 829419049
    0x5041b0804081204030f11030f072003062805010e070e030106170a03091e060f030f180b0f06100c030509030102030405031314011202030a020c010e01051f031a06 71
    0x1840307407a010704891101c143c244401c0c1544103c040f04584c041d41c80c0c900744140d00e210070039600c0c0511a079221442004100c59000110010403041510070f1111400c1c04400d2441c0019040200464030046021040400190b201c121f4618041a020182c0010841941088071442103204001c210350107008020362050f42540b403d41c40b647c0148100c0d8a41c00701c01014240b144d45a11449001390001250f0140c01315115a071210b0020f44848250000a2818a0600c0581e04210b00d01503031020300d90b594603a848403180900508600036036007200340b4800a082d01d4041004000617200d0000d01006e20104003540d1104824580c0c2c841e5241401d503400b03031003480c00315103034442c8009030f54065001000f80700c10844008041e000c6549a40d440c00070841d110364142440e50078500e00b0a0010300d040d0103001c07411013141d00454100421080c003601e0311410000850030740c0d1102c443c1043c40da55900c100070416240004c40c1d0b65100407003502c107800901d95102c01a003405240751003180f014103c808940903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 829421546 1250 829420296 829420313
    0xa0201031119080a0c0914090403120203040303021e161e0501020d0606090e0c030a18140a0309050604080309040e2a09070903051009291005041b0804 66
    0x2c660050080040703110404000b86209000d03951492500d0502032840036540c0203206500944990b81001041088500c041002500c0301410540034482c4618242101c41c0f0140010b40c4224001e450150392400800843d040b10501c5034030160a005062084d2000e00c031034040541c801710313007100880c503040c000f40c000407401400103d0010542d620004119141e01d1007031700400201c6509454041140b5a52201544c1180741110400030a580802c0000c600c840309500011038070460707040c40350030700d030301651044600c03841520600c003280e000501500805030720a0360100501010396032241403d00d0119010b5480c080c2541c0284142e44a07040d1900d01c00082009114400c40d42c1c0650030700494004600050361195850940222049170000d074102c0d01400c50003080b03d41c0a0000c00c044100c03060a8070060400c498125020361180c00c20f68181001040e901d0802d8245030a19011414040d20340c243e8243d0f07d90002d40030302c3c00c000c0128002d110a2946d490506900d0410000954a0749441581c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 829422796 1250 829421546 829421557
    0x90f1b0d060915020d0e01060e010b19020a0f03080a0f060b0703050f091c110d0206070b0405100203090c03060610050a0819020f0301030b0709141203120108160905090a02010311 78
    0x4100c4c0702080010442031706400a1021146020007000080c1e100d510803180c4d403009018a1030249401c0000c8a20311840c500c0300e01e004100c501c1034403032200f080d9540d2281192003050550001d100b01091005030b080510400c1c004111868003080030a1601c91941c10030b01840c10050700b071110106000c010001d440c0229450401c0c014281451201d0314a124280300b40700d03070f40585881158400e080101d007005190106281c0d00140650705040c95aa1134030640c1000800888040c064800004a40394041c009140180d5025000e0030102c0c0d4071109043c54039200512451013140c00e0220124869002812242c0040703844ca4841d001d80e4410b001c1003048050049130418003407001400429070b50751040038505891140340b5043c1d881c1c640d00c1c3c0485e0fa891050040442010458000c000e00d03141007a035100c1005448000c3d42d007001c00c4841d414984440992241849800c10f1501d0541d55045070791403c0940901740040206007003414520380d0b200070f070810090505a403942d400301039140d00c01c00d07104c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 829424046 1250 829422796 829422833
    0x6040b1c080c011b12020909240909060105010e0108160305060d0f060207020a0611120306030109150615050f0f070311060a090c080703170d14090f1b0d0609 69
    0x381000904c0d52840c4e00c4512209040022210f40d02c0c40d000745107038000ca0300104802460184603031030f80d90301442e070450500c1e44800714091041c441074480d103808405911411154014104a62402e4000343c04002201d92050400c4103910400000702104003048150003120301d0300060688d01c03880400d400521904000d080d1070905e000c030800f001038640041150718801c0d6401003005566000c1a200c0425941403a00d140d0885410095040303600009951f2040c0c0060000c1100072554907014480c1100f1401401d11303544032001030100340701b0041f60690801d0300b460460b02c6d01c400401c4c410580d0281c11000d008508001601e141407601c02c00d651307400024610107841080c10a1045a40200120841190100c10245001030700c580c0c0403035641d044a400c6609089a00541503080c10180d00c0446094a002c1c1d0342c0b980e4207903c0f140304080500c03a0424000400d03034944806061440e11001d102c040c01c9856003464090156110b46c1c100c50359407544244046101c402d941740c03000d103048440c480c51 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 829425296 1250 829424046 829424051
    0x1b0c0b03010306050108070b180f010210020c03031803030c25080a02010c1e051621210614060304060e01390804021203040503100902010806040b1c080c01 68
    0xb0082c025140e000b42d040702c40728011105003903616684608280580501510a415601918112401c02014100c080003051041d680100050800102207802c80100d001c0262b001000b00030030900101080c81c0c3c0d00d101000210b0440c508549a40c0b03403480f40f10074a04038402e1a4521808802ca0496032202040d401913001c0e455190b0000300a000f40311490036000003e010784000301500c3e01051400c9001901643e880b442d21428a200200300e49400d2012104103d00d500d200c07001c50001305e00301d03e010201e680c500341c41c68056110707a02001d0302c440c007205003286865001c11038003031541040891030718140c0e0f00071349039079850508100629900140d07058079400c01e807903080d250000070b442ca580066004400442d06113081403945200c2030300c0400b040460700c400d000c5409881c0c4a41608148007103201124074103600c03580443d00342090340d06d0840b0301c90b072142280d80c00c66030404000c035480740c4159400c02a94800e180000d0b5007907580103a40d401030070170300701050510602004540c00e0606501c003e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 829426546 1250 829425296 829425299
    0x3071112010e0616081006320a090f091b0804060b0a060e030d0809060604020702031c03020304060509010e0d0e0a030c080a020a082e090b1302030c0406061b0c0b0301 73
    0x309008499060f0130300005500c190015001004207141581a10714964514210002c040400c11224848001141c3e854052075140c440004440d4000c0403903d078076640743c1c0941450310020700061201c40d0868a02a0f0910080300740f485606a10021a40030a1800001c50f07181c3d0300b000710047c515101c0c140c1e044942c542020412980101014021160560464145012410007158503c0055a046195800c1040414100d18141c0c0152010b140001c094500035880890f0b0941000480c0000750086900401044140000c92003460740c0001018020704c00b064540d42410784500a8a40403030901a858180d01100d8075040c2543e80a140d001d50103544080d02c4a03d1540d9900c04034100328860300d550032002c60100030125500f8441d1010260071122045040c600c0309610f24108130911800b40d446603290041101d0b0005103000d49c1c905107190724030820f01c1c018103051003124030b203040c022400e1680400c409684002d800134850001012140c9403600740c580050042240e41c800201410b01000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 829427796 1250 829426546 829426561
    0x50a0e0d06090c170a021e090a0f0f022b060b070609110d0b010b090d0b0c0c10060f0308070c0b0c0607110c010804020d060b04050c091203071112010e06 67
    0x407203402c2d00d028803021000c09948040703595004000304090704032900108078032070050526518400c450000991441c10000142021a8010004a56211503142c50b005d400c1416012807003030b0300d4040b0031aa0290f15224a801c24134004a07080c4500c0d082000c100860b44900c030503030354002d41c0604102d6002a41e10404d0342459006090080006d403044050282c10300b403103160003440c0d042c01c6a800000c00a2a038680029814146c005003006a0000f000c140c200000691203440c6601c00e8105400b0141c8846d0094100b924089411000d00e1806140c1401400402880c081500440341d22203411640d0303004528220740510032640c49040c642101140c5000100c40104030203218006075903480c5000200844080c1c0e40e150702d41c0d441c41c0425180000f040150504050090a060182502042140c8440c1c041807ca410854180c10403441c0400d5026103407800607034001d80380440200a40c100640d60300c60510540490b00000e11a031900821650465000c2d0040302d0500040001c8d03852070301d030462 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 829429046 1250 829427796 829427801
    0x10e010e0708151501050d140f191e15030606080303011d0705070b04023d0203031b070201090e01180b1017150a080a0c080307080a050a0e0d06 63
    0x401031980650002540e100c3d086400641c89030020071104804004075000540e6590710001c0e44015582c0c8420090f90740d28400041c143c00780b60074410600d6039151006054842042d090201c4200e1307401c01105450090803100042c0b0f4001a06e04001980501d220f00308030080b0082c1d0000f090542410000105814088041d504035611076400303a01000d41c505861640b00c0f01250200701240c000c2c04500049880814201c0d4010710150440c100003c041d051135038880210388807000d40701101c0513103d9203120500c030a175000f030f13402d40000c604600386600c03210074030070249140c512507680204404065a1281402c0c10003080e040c80c5e400c02550712a2040600c0c598034000351c0310050704040c080112800c0c480e003220344030030b101e64a42c041034680708200404e80030701a00061241d154110185c0d25a0380da034480d0780082401500074800035100d4a041030814140340d02c40f021640003840004040799038201125544007052900b00e54171030019000350b41d101e00700c06d400d640216026002904204655 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 829430296 1250 829429046 829429049
    0xc11060a06081e0a030807030e0f0c011b0f1515080304050f0604150804020312120406150315020a120507020a030e0402040b090f042d0b0a05010f050309010e010e07 72
    0x2106031808400f10074100302d418810300c0d181ca1500e90007801d038900401d200d202ca054200f07030f1324900481c48a002e07480c0c0c58a0580711445452990308101c0841c6060760704002c0d00c41400003c554501c3c60f07490140c07254a03450300811000f1b050504100455401c1c078185503c0900440c4440c1401040145c032403000e65925000340c06003a0054800b0308c84500989008001d88048400081aa035041051000200da03108001b910490709441140100c46400000201130414a50740e03a407000b0700b6103081d00f0580281c81da5034a1980c1403040c042c1082c00410010340d01146160241500965900c000c0d04003201e02c0c807254108042110702d0b01d002d2048055001c150066828002e69490b400c2c80e1550702004100d106a20502114038400c100c28085030030103d115a0121074000d2001030340003118510141c0c0d1160b9283c01c20716142e021840c0781e060382018401c010320f900c02074556000075400d150011f0139154400b0250024060f01000048400c2c82c2500a000750320102c0c0001d10040907510249540d50303446 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 829431546 1250 829430296 829430309
    0x7050a0b0103030f08240102010b0406090f11040f051002030903061e240409020409050105040c0302030f150a0506120d0504080d0206060607030809121306030609150303030c11060a06 80
    0x4c195415034512076443d4501560300e0710140d41c410159101c82c201b4903d1042022419552610007142c525601e5100e0040100611074012504810120744442110810084065041405d002c241300002030041c4c0781e025954140c50261003501036007002d03460341c0285001107605100355000c02461000d4004a42281409842d6009681c0c507406252040f100b11075030700311524020240c8080c0c05103400d4000030101400684001480611a142e090941d142101c00340e4081c85a00c10400443c101040903011040e100b0703001e400c10081c0380840008440e0081c18030300c08039454002003046543c60010321840c0f40600f10490701060045100170707000b40c10500c02c0c90128018081d251300c1480c0085111481400c0007060036251290959003078030391132030140800311179210343c0f0320315a03920718050300a01020744000c0b400c58107149002790050a80d20160015844030341031041082100321982400001d8951609012920501247c011250308080101c0144148200e40500040c0080f540c80001070310341 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 829432796 1250 829431546 829431557
    0x10e1318231b0103141005030d021b041a12010f0612050c12070b0403210f17041106070b0f06030309060d240902030a060501081b0f07050a0b010303 65
    0x5264078081ca4002031504039580380e00510303034038040340180b042d89450941c41410000341d20003250a400c55a100221044c0c00c00350601542071205180030010032001032803510003407920700052040007542c1d210104486008517244c0b0034031402c508120000d103202d460040e04a040d81e42c45074110a010b00010b4000c91020382c41d0060100311000c0d100710520748290000002c0c2942004a030600270310104860407030909014402d00407034a803041e00010300003580074812810040742c40d08810080c00d040584000140b002d070030043c183c0035400000c21038480c21012072101c0160340324201241070803451090326610010020704181000750840703c03680142102c40302e40300c4c00e959500c00d25030b5a10807034840c0c0d60701c19018409848040029000301c0c0001c0400c0e40281801d185841c0c182100900903002100510780101c03c000c44008540700344801007409181c42c6d0310701d08000b000e0140c21300f04804030111540f000a0119090140c41080320f001c0c036480412240c4000130f900345034201d01420f0004030000b40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 829434046 1250 829432796 829432823
    0xf05040b031e0a111c0204050a0b040608010b0301060c02010f140a120501050607050c1002151017160909031803060603050f0307050709050402120718150e0105010e1318 74
    0x40f0501c200b058002e443d10302e06140c940002010040a00454183c003c072580801c00440c150700c0d956200e0004050001840d91602e0810b00041d0001e0700582001d120810140010040540d000d8028611140c0a00745070000701002e28040320202c9090701c0c907034940c10000941c01e81c01d40d842100000200291401042943d80388c03c100145881007110290241e4007082500c0c04078074240f143c1c402021814011140ca40640441c038000d904001c847d68658440c01c082d0030071000c0728004003800c0100c0180f02520031a1600c4088100c5107045000d00540c1c3d5980e8030840c02014000c0b0100808803e802403a10b0400d41c0d00c1c038180000e0301082c0022101c900545290050f504c00020540300c24540c810060400d00e828521401c000700340c01171090b644603003440c800e00c01c18041403192002400c4a400b6443d0324441c081da02c041546d01d2203824011150180c041000a8041640801e041d1542481c0502d80080c4000000c5d0300003d140000c851464a85a100a22010120198415a4031070001c100092 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 829435296 1250 829434046 829434061
    0x10314091b060f03011e09060b070b0603010507082a0c0304050a051009090209060d0e0d091401020312151c0c06030e0d030c0201020f0a030b090f10060f05040b031e 72
    0xd002d0014400444038090005001c00b07111440c00d101404d1019071b066013185e540e07104200c00d845180c1d10116403020300043d0b0f8024441c5110b10142d12480c290000d22036810040c80c0200010350091400c02448501d12414004224058114540ca08408080d0781c030303102c1d150748241d200c1d4402e21901c1d00c50102014005090f050010740341e86900007a81b2070b100b82e50716086030703100a0741c001a683d07a8450810099004620402d21802c00e40900318402804003446414014142024a800400d00000c81c054810401e86c1d00004545088000c81240000e540356000d002184203043c0100590154031503a0990341e680780c0b0301000e045107000320a911881c0e6641c0742c043d01191180d44400203160030410b568a6054003981100c54091024400180361618407603c82c9200d07045842c0c1c2070006521140300c11078900e031441c500d40d00012400d02c0342d24282408100e110751005584240c0c0140000841a12401406002a900145401800780d43e0700d10b0b083d285042182680c045560038001c50101042d80c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 829436546 1250 829435296 829435309
    0x3050705130501050919020d0914060601030e0c0112111603080f07050406050c100203010f091a06031609050402040308090405091522151d0c0d02090402010314091b 72
    0x1200c501030503041c090b80b1421341d012992910111400f484580030469692381085910400c2e074403e01030b00c141c0c43ca403004a0441404e048004e00000e0415003001820420608089042c04240c002400c0880003100303900301c604003500030440924224540403c040024815031500980007510a07500c0c03244540d600111034100d501e0540d140320025806101c1803041a0040f002400f0740b89c84141101c440c40b86c44c10600c400d9901c05d0f00003400100b100c44040001c0c10881c049c50700c555040b0380d032103184441600c020440c0c0780001084080f0301001d90400410031800741c10386801920b009041907655070780f0f0b030a15030000da0040d50424080d62400300080e401810209640306281e044401c21041703612001147c00c14003020300c03441d61340f040003030061400180780c46080d80c2d808200e020f408070303074150002107843d4040c0d0940000074458028201d0305803a991032031250300d0b54540c101d41c107190648550004a00030104c44034501e040151003021310101c40400900c40c0c03030043c00e0703400b00320300100f401e03052091 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 829437796 1250 829436546 829436549
    0x3040302030a090915030f0809030d021605040b060d05253606052203050a0611120a09110409050615030304180905010e03220b0f0904050c040f03050705130501 70
    0x50740c00c0045c00034000540382100d1f0994107805601781c00d003011500341c0080c2c00c02e101c0441550244e880075019454200c0c100c25620000c00b4219010420803001c007011859912840c80c032546401d07a0381d00005c039071100d9224105403015023004810030283e81c0c00c002803c8503031030140101007038040080036500e23040c2c0740584800c024418a18420020300e001026121070b0040c080c00341110550107060402c0c11002001c0c43c00031801000180b00d5074041e810300742d04940da17601140001e0712042020031003021502c800d4680014000707100094000c201c0c1001d440d240c0301c815515a000c5c3c01d000554040c0140050f01c2400380104003c079071240840c0500b0035550380b080e44075140c004400020075111341c000d2544800d404900841c00400d1000490580750b055601c101400108030400400c01d05101c400b8040403030161000040740c510b01442029865180d0241c0c2442c1ca03c60b684480c0028041c1e9254800e48004141c1200c60004080c1c0303131305d00b0a84030406809900d0280340e0541c000b0b0300010207070042e9070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 829439046 1250 829437796 829437821
    0x301142d072111070602041a0301050a0e10171b030f0c04180209040b0f0702010204050622080303070c0302011103060f0d050a0519020f01020c1e1503040302030a0909 73
    0x80341000000c1c00444504004100d880c4083e41e542e00c0034140c0103c0c1005060080c4981001692281816440d5180140c80d010f0007107130002c240010300c0251180580a000d80b0380c003000014050340e528010503401703034403030300003200c00c40c1c54242403d03008e080040e01c101c810000e09104218a0070320f400b410395425030301500c210185c6c0700e00001035460030309034040070f20001780e4484040f20171440e401140e0200c40c183c1d000c80302c080c0307050100a5220805460703550401d107184004c0d0302d01460500056080e02901d010f411001010305550300b104103403020018000c3c500103054035141e00d442c682c00b03018030404090680255080950703c4100c0202c09045034441d4400510482244030218180072044400309011a003a108040295020902c10004410800000e40c945100707568644103000b1a03603e600d5802c2d040d94800113000c2050341d25554144585030310000b8640ca10f02282c400108a201c41c210909138000c0c0010900081c0343d0302000400300804983c40d13022400740c0d0307401000b08980c0c0601004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 829440296 1250 829439046 829439057
    0xc08070309030e0609032b020f060906041403192c030d0f200c0109080d14090604090203010902030f16050301150c0501150e0901060501021b0301142d07 67
    0x444441c40d000c0c0c0603007050303030b0040c1c100c548402c5400d04c11068842d03a03c28800e00c1d85d0a80006d2002d07d60304120703020305884250041c15040c103241001c65901c62018000a00300b12000c101d04858103410000d40c0c5034510b441103a0369089410500141c201d010b0f101807c3c109080c44d4001e0b601d40b00c03119500000e00f0801400034034007000340c91000c030b8008610410403000c10030300500c04194100c01d024484030615446002e442503210383e10024050b400d040e0b1113200103400c1850602003981c2c000c614101c220402e05513a568030710017500002c0c41442a1381081c1000ad1001c8004035843d0810740c00b0b03520580036000324030610f840b00d14001c482c5060200b10301001030000c01c014441144003a45051042985003044404401640d88283c25107001e0054200150320441d01013082851600c4074075004400d040082000d6410400002e4a40c8400038000c01c421403182059182c81d2400d40c08016202142018400e250900c0b080444100c1030032007444001d142002c0e0703d102d480541d4904240580400d483c0c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 829441546 1250 829440296 829440317
    0x312a03120e06120702032b0b011b032708060f072a0c05130222150809120a050a0315050f0120010c0e1305060a0b03090705040204090c0807030903 64
    0x5010410000a00f4035085020502a5545c0c24925811f0091142e6140c0100350f81403a41c058030300d04540700c0c000380303504000d1406200999161000c0011500d550140f4044020040030f0b011341000000290042031302401c200c00c001150a408074a440c00f401210201c100c1c20344807010704a82d280d2900d01504848000964612102030444069404407480f0319140c0181c1c81d51600058142601050003c1c051a00004c065245402e021804641d00545254100b0b846041c81000262502620000b1040c0030400c80400c42103002044011034171454401600da0752001030b20003d002c0d401002d03e440209041601c0c0441030745070030b481281a0f400282204003400702e000011901e41004401200c0082a28140c0081c0e0100a020711540c5942d5612920004031100092101760150400d22400c2036260030280140c03a911a54032008490791070806980300c3d2651030041d41803010903802035074400c1c40001d000600000c9500644801e24440e00c1c0d003c0c15a031000001e405031020448000c0005d40c69440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 829442796 1250 829441546 829441567
    0x6010b070210110703020d2411031902091003090c06020f0c04050c13030b070e090108061807080f07030c17060406020a020304180212312a03120e06 65
    0x1002c801d80c0f581d400c03c440c050381d42c0340c012800e142c030101c6050342c00c56441c0019180b00c40c01c01c44540d8014040c164108139000014803035010500005c2d089003101000004000390300b4550390180c8000c0c11000341541400009034101500500400b0740450f5008242240000c4060021461403102c40105004e003000e400400200002000014035940701250180401c10a244c014046400030310720440014003070341007038800500740000101c1028401d0b02904018020f0038004a0360076000952031201014082002c9201802c0c980a0f40203403505100301442c09084c440c00060b45011030b401490f080b81000d8603039518a00b4140c0789245028581c2c8240007090000712540d00030011100c0500c1581d090a444000102c00c58400e10f212700c0c0015004201c10601202544c40310381c002c42072031840140c90700d6510500076000d210403c90b9030030130a2407100d031083c01918100880c00075001c0140713940200c0c0b00740c641c2512400501085e6074442c2d1185649801d14043d03402100c05030f10040c02c03682000000c6c0c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 829444046 1250 829442796 829442807
    0x10e0f090d0f1803060c0206010503060c0a02071e080d0f08070c02010e090402060d060b0c1002070c0603110f03040605091c0219081605030712080f060d02150c0d0206010b070210 78
    0x301aa01c00fa031400000100b130781e9205500d032154041c0e0141040354504001c061070218050100341c03185404001c0c020300c0daa00040d4900803107075800d1400c1050250036060b8442e80c002940500c2580c010003904054407584805400403d01d1192681d108945990324100c0d1205ca01c07a400a000c100504064041c0d0305c4e18000403988503100400842ca4200c8402051044d5406070f80042c0c003002c0007081c400d2482000348040d20180d0001d2200b1405d1500913101d40b594280e00748501c45c181946d50b02000b000c0c509000498000c3c0e8110f000d42583e80c20a8903100c001441c0032141c060301e5016120012011070f5450100142e038451a500505e190740303d62100d0708560310020801c56030300e0070410440c0306500400c6c0140e50034034010806035403909180d00b402d050055140a4a07410003038104200251182c2c050859900007000340c4030403101d0341c601c0c40402c40390850703407013855400351020521036030200002881c5090b5128942c2a60300b0340e680d40c00941200d01038203a0003540048006140d002151240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 829445296 1250 829444046 829444067
    0x20f0301050f120102210f0c0f0a05070b0103241104091d1902010f0807020a0602090d0c23090618340f08101401030212010e0f090d0f 59
    0xc0950040d00e0014005130308a0b0700c15074203903071b440200c08510f54039a0085000f9035400700901003100716134940f26235894010300c83c507031059203081004500c02a805100c0c070144c07400c141d8844454800fa503128200307104000a020070545c0340c861040000d90040500f03010344018103e030444250f040c5400c088624002d800c05035040610240d1141081007585d17410055a101f000c60f0004450000800b40001000580f00000f002c0038014001c0c18008442c0d4002103a500103500080010b86071180c020002d5414446080080e00b408000140454880305141d1519603194004800400ca602034005201180204880d19580604480b50000504e14118076540c5d03c207020802517100c0c0080c544030748500083d4030f1030500803542d65000240040d82c010035031103400c00160404000b1441d001030342d54000e4503180948003515100c00560744059000380c041da81e141c04004020949907864600c24481d0580407907507031072140300c0c03000403803540e42c00030406405044055880c100f484140d48820354144e03120 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 829446546 1250 829445296 829445299
    0x606091b090501140d050a0507030e060108060105010f1e0e210304030b040c050a060305040c09050f0711010f06030f050106062a02010c0204050405031b0303091e0f030415080a020f0301050f 83
    0x1000074010098452050b00d100e1421f90400046500705500c00404451141d000030b40550300100043c408800700044207030454509192440d400310000790100c4031022851840359006251607400c120003904101203882c900c0d4240d9102440703d2000c1e426142030a007400420f01260800c00040c03020424801c2030315402402020503890081e5100081094401b060780f115002a644900740010407010901517002058050802d00c52410f1444200038510000751402090100d07410700141c1c007041c00c0d08210220b000d145801c00c9019500d0800191502c1c1c001000c83c0d0030751800c034002c035206010750302481c00c4860402c03e120f00340003450990300c588000344070107906104d0000c403810016500c03030284500c04c0388101c3c0516202d1044071200c070f00407810340d80812216002401000280c0b900001c0c440328090340345121500d40b92060080508202200550030910b000c0040d000c1106140d00808044c0c0c040381d60344110740c1303503243c00d95601240100004516281c41c00c00040215240040c20620107440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 829447796 1250 829446546 829446587
    0x30d0e04020f09060307081909030504050906130e0d0210020c0a03110a0b0c072f13060f03050604170a140a021911010e090c041710090606091b090501 66
    0x9400060300f02d170001c8903c180000c0104040048005003008058042d03003009800307104030040d60307601030818013403401140d015a18000c002202965283c0c2c1c800b40914410f83c0c20000c000032101e0098907001c00900c601701512070b40c805110a100240300302d5044504d0003002e405503440654003201c20300509802030f00c5d144503d544040103c4d1038074600900544850700c1c6165101014a41079a000000c41d030080d1400201421040310001422045100c0c07040c2200c21500d5800020b00e0304004044540140b64001807021010080080008445004a0150f40d495040300380d60500c07880140305608105000541400c110b1a03c3d040704000703444020303c24010344440d0740c107001a548410308180e0050b20298241040381d02c86581200c0c1e0304801c17402c02c0d502602203140828212805100d203100d0109420130380c00508031701500510034100c0202e001d600600001d2810b0a001000c1d02c0302d8001c0c141400d10b008064040c0c2400d540a02e8290950781d103500218074602070041d102059401f000702a880c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 829449046 1250 829447796 829447807
    0x1060c0f051204060906030516080a0f050412031d03120a0e1c081b0f0702030703120e1807080414070b1201030b1503030d0b060d02120f06030d0e04020f 67
    0x41040c0b000b684081070205440340c54910b40000240ba1001075030003442414070341800d000030140c0454400c404405541030070030031516202e130100010072404001c0000f0510340310a0204100c3c16800803892420302d07a4050001007043e10000200e46007078180b91034503920412034414100030030901103600c0203c104000666000310384032103081075003040309400c603070841d007034403805598000c0011504111149241156107041040c0030500c0d2041e1502c1c0c0780b0110001c525201107540c200300b0840a168414031124211800076000391651542013840392198000100c841c9004001038041480348900e540c0d9030000340c849403140744404001c00840f540b0f500902c580425060f4040c0d0040030404208041c601d151345c51420141c0c90b1420181148402c100d60b10041c98150b90008156014050150400520b92802c400016a02c0c0f01706215458454000b03e1502ca01030001d04482c3d1117503400c0c444806e05503646004142d03d50040c1c0a858020418849900e409410503502810312044400d11052504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 829450296 1250 829449046 829449053
    0x305040f03030203070204050c0c0d0c020d050717070e0708040b07020c06040b0d050609090a12051e07060b03010504020a0614040b0403210302070b040807060906090b011508090601060c0f 82
    0x44603507030025805644005410300c11030401e803040c59440004914083d003000070002e500c6468084041030308040141c01148036007599170b1a80c406451950001c01c4039200e5907260300420680d04948040d6005e4050030b14000f0b000b042042241c0e105034000d6540c00c045a4a135614080480b802411643c11481100318a8030310b9115100240080c00720021a030361502d030007041890540b400248800c2c0039114120500c000c500c4005202d29002e81d12010204440549400c100d9242c011492041c146042100800c211304c40c4c484000c01003140140e405120391115401414242c440035600290084003501c010000300d44182124640e00c03c2d200585464240d4078451038110b0b800c01e0b0001d44807003e0000c0318803d445d0b403002d508a00702c0c0c150b040650900d011034403159070309480140050400f210001d1721030200203c5500c8000c4603a8400020401400c0b907081226540300c0901448000f44990001c0001c6640203403611031054040e0f41c000d000036070800c0c20884501d51403001c04c6600610045401000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 829451546 1250 829450296 829450319
    0x5150306010311042702042f0d05151e0105070204140a0b150d02030c040305010c0e0306070903051e010b1315060302040b030601141b07030b06040e0613030504 70
    0xc6000300340748070f02400310400300700480304001c421441d40d0950505d405c2d2492a101050803032260100c1c0c0019140000502c000c07180c510f4000f19140300b540181100044036444d90140c5100341e02100e007000303143e0b10320f41594168403000145030352159039020404129903295003d0300c00c0c00302c1890240c0c00c04605a022800f039500c4501302c141c003d210281005244d03c224402c03580c1d03400d0111f94025605840c002001518480d40c816042c05039000070006a4180840d82114025503100c0020400c28241b0903004004c03131041c80c0464400c1c001c1d80d010440c1c3d544a842610140d0340c01c00080c0c0080c1041c0c080e80003046800408001e1783c1d548035184160540d8070549002a014916807000c40c000c0c1911801e040c00240a4100b103050610511043c44020000030990303071312103800c0c2020b400d0304c29071210141003030045540b00c1c0040e8401048410b08000c01059a404507841408144000d0300c401d410030059a203014103000f065800600010a903c80400c0769400c41c80c0241041c03440c0a4403240b05005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 829452796 1250 829451546 829451549
    0x60a09020f0d0807021302071e21080702061803220b070b0108060901150501110703080a0f030501050328080909070f0e1906111c09051206090307060515030601 70
    0x42c3c240012803002c0070341c1803120b20840b00000840c0110719203001c1e551001040c20f8108918215291001034007400c010f15801d41d0f54980c0202c00c0d82d424006000900203048840803a10180140540d901203072121241d80040c03000e03071b564107014504040c14000419203c4d0040300d8001e2a001c46010b0020760040134038010185280180d2604d81c4a60420340d01c24900782003c0c10011040e0b140154240001420110300e109039002482c106891080030302c24507103030503103d810107028884005580e5841c55004503150000000c0c0340c41c01d0201d0781e80c9208164030b4410140700c0650201c48071030200d0704466400340034203206220750302c2c0508184c0e009020800e4114106c0d514804030361001c2c01c07050603c1c0c1041c003610810004a400050a800e00c0750200c2c82030300c0c0c62103800c041c8014000300c24084807083c420301000c44014101000301444180c8000d100250a1044e01e0007682e203211a40f1882d0408201c01d44610f201c20b0003117103404082daa0700703c02450003c3c804040e04134410000c20059906002613030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 829454046 1250 829452796 829452803
    0x70b030a0b0a270902010c0b1504141b22030c050a120c05060d180614060303030907350601091518111b03030108010f0e060a09020f0d 59
    0x2980e11103010038040c00507495004040c03850792141c445550f0320307542140751201c09090341001c140d5006a02c0140c80452204d58002e15800071401040780c54482e074503440b0001c5004072070a000b000501e00d65003003131200590310350410904291640c080310003580018000ca1107200e0f1610520340310506c030b0603018111380e007017180c19126410040101e407406500b1310b400350450f86506421954980e4036040b4078103842c8659402050081703444c2c0c4040031954011003030b0406140c90300c9200f0541d45041802042050b020300040842c0784c1c0414201d080001c1501d21920804c1d006000e41420b040c6074840c159a20503035980804900c81c007422240002e103011601407511940100400c0d410314451506580440c1d20780712480200080800c038108410007401240003481100081080366019403034040c3c424252840e28038100201105a82440000118120b40c1e01000800120007070700c0f0320308103452440701180c0c0341d68420300c01701c2c20000f116808041000c1c4014a981e407800680c0022403510092180140c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 829455296 1250 829454046 829454051
    0x1b07081c0306050a061b0309051201020304050601060c020108070e03030d09050d11010209010e04021305030706021e0d1d01020f01060801021b0102090603011205071a1b0703051e070b030a 82
    0x90359038241c000c00e80a4003046500040f01c50401000a1446140d086926900304a8103088400c1c1030080300500e01401f03010703110711600d04509140e2400b07540117903011140c07403244500000340c8501c1142034a081a0b4140e4902c0d081c0c0d19507600865030307051824000d66150004100c0703900401a00d02c00c80e41c4081c441d20103003140010703403d0041c000d036101070b00103615a40100b0541e02c2c6d030b0380d0000700071800724400c880041c0c582200c5224003484420f6500450b4042c40342440200b01070b900040c02504800840d0314500c0060805050341c2e480d0f164500120000c1007800141c2e9001494000d418601080c040c41100c0940701040e03011400d50744241d0054046960025030400d204044240c0d0030325032011940258688910070000c00c18601c8140300e1100010070441a6404111051042c10000d003200000794646081c600010380c0c8603400b6043e0310400c15201e411781c10254002080c0401200c1c0c001000d8455201d10402c259040071800510340028042d0003030100b02c2d1080311014602400b4680c200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 829456546 1250 829455296 829455343
    0x140106021915020a0e0303040e011a13030201110a0507060f0212070b01150c080c06061c0b060f03190c0e181b0406080d110d0c081b0708 60
    0x41d040c12100d40059851054100114010440320002042c2825034502c00690355503003001c0442d00b01240700d4801d03605000001d80000c1c1d85040304003183c10385203101100f20b00d44031010820722071889500c000d0528043c0c400342c20401766000f03150000e4005901021358220001030f60792a82000c1c201c0e0000000308211003021709006a0400079a5006555081c40c80d01d0100d1545401300c0f0f4240500c1100e18040c15007091801d4103116600d00c03c00194055403a649410802c050540c803404115030490042c41c101c426405c004e10619010640e4940041700d18105403a000207002c44003010801c025058810032200901950500e01000c2d0303080e001e5100c69a440e41000d00d10030111002030140c0c0403008a82d03042c08111100826017100800700845d000d203080540c20b002c940500210703400142e19010707080401c0845504061241e00e900c0d4000150746000324125000d85403948041c00207030a0380e1041c4124042c001500d05542e21401c20b8204a400036940c520034a0b00e41098104d10405892183d0310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 829457796 1250 829456546 829456559
    0x21504020a0914070f1803020f180a02120a09030c0605060402190c020301050703140f07140d20030106020703030806031e24070c0807030e0310020702011803020603060603191401 78
    0x1755a000da420500d8040303a503a921080c44200140c032400081d100b99107842080c075041d510000840b03151030039424810030929180700045c009401c260200207146860000007010700f01c140c400c130341c20a641078481491031501740c1c0303507100104802040190881d500704548421400303100e0814188000341e5480c40041030f10744c41854203441014004000341400c1552420f201180b00210310303405060b56441218950b034078201104e800040c0813600344103d00c00100c00c00711b00d404d500300900080d850503500865084844802c5124482449404011303041100240000b070700c148021500240020b044403d030200514a003e10f03110480d40d1700d440750b4082d040180c02703011020200890500280040e03035035464a0b0601428a80b00f2403c000c00308200012510100350140c001c0300d508580140450300c440d800326104100a5110040c140d01055514004102c64140110000244e0742c4c0501010b055803298000c6c45519040070348900b010188405402d1049132191145542c0d030364005801d802203502d45070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 829459046 1250 829457796 829457807
    0x19080d0e060708040303110309180114010809030a0309050c030706020a170a020c120a0c0b04090f06050d1211030a080103120c050d0f170f091606021504020a091407 72
    0x300d55004100600600700810814016242240d4140c00d004240b1280420442c1c10741c4140c182195100030741a0030304021000c0d08131900d05071840900c002d008036044500540e0501412100c1c40840d038010080411014420b0700407100035071140c5d045440500c1020300207420032800c1d40150005a101084150034082d00c081a0b20101c01d203655800c1c540110610000d4452940100d882c0c02000400c11010410804014009100c2d0b0010404041952154000c0803258800d104018000c0e007020304c82003405645101e0308003290f4004103006070007415581c13014120414070300000f0901654038590310580c034060008103403a003801e41c1c408080b98150300d080340c060702c2030b0000502000a181d950740c00040e400a0702c444a80740d18201180800c1095604680c2415010f080fa070900e40700341c05111804c040c0402d42400b80c1d03500029140d04103005070004001c081035200e40e0b00140c3c004110a01c5482008010540242c00580f400040c60346401100c41a070f050f170007604281040240030840f0950703008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 829460296 1250 829459046 829459067
    0xa0b0c0706050406120507050405040c08090609030a170907030803010e0402150a120906200c010605011103030a1e1d251e050324010b1207050919080d 66
    0x182406403c0c20700300200200018046100350700810360300c102040620340218240c50080500400c00e100946982400a11003013040c0da088605126440106420100c00710948100306001d0b610724840c04295103104140321005030110700e0340c1c042e4103008000308a07a50015030181018699410650805105002d0b14182100b06150540da041c00551002d0360300c405049441d00c613800340419440c25a00f0724500070092140c901c801d0306620303036403c0b004800130710181c03a01314016402041074a9443d0019034000e40e0001030b9407550b400800016000c491243e20841000340fa41c0b08c8408001040d041e500d0490703004d810920b1101c04081c4214071801c030708220310403540c08505070580c0816030307412a08460700a0750081014410440003052001031844010300c0041c6001811a210b408000310900c001070f40c0508683c0d0143d0351400003042e074208c842c04642c040c00c1580c102076510750f103002d42100d103504100c1c20744d58017584001b03840d05e22003013401044025108502c0a0100e4915400c0c001e03001e480712 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 829461546 1250 829460296 829460309
    0x2070e0601140d020309010b0a080c041a01093b160e0901140d0803040f020a1410030b030c030f24011508270303040303060806060328020a0b0c07 64
    0x940003280c03004110b000f5908a50030034100541c8a8459811207805011403040740d50700030b00b200c81c001800410005412500c900150b80c2041850101d820a551154001680c9404500300100c01c0000205001080740c1c020300d6182c1c0e141c20200303840207005511001011611001c4541e000307001e600b00701989191001030650410342614118003000c03501030101403282d050701d41c032510031500d516166502e0203a01c02d588140030f659289481d01d4107030316403a44000140c0c002d18680d0700204481d014042ca2040f00d02c1d00802003901c800c0020380c110041c10b9030340d02081e0140101e170306011058504024250145200e40c02418001450740042c8000641094960308290400c0c5c0c010000c000300301010040c040ea09107811845640c80c001180c901d44240c55002c040b484007108410751030600800a140254440d54050180e90750711004959242c10a80300b851b03142d04580210340008140e1803500c2c200c1e042030301074030208101030b800040c072625981c0c2c00040c1d140c0c030006c1c800208441c00d00101000d8080b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 829462796 1250 829461546 829461557
    0x30903090114161b080303090d0306080303041a0604090209040b0402040c140702062101060509030d09141002010b060f25080f0a0306120f061104080c150705060702070e0601 76
    0x510941c602d00c0c00c41c10402411041e404200c0301692416000e41307402402510084a643c0e05113507144d266101c950785180d0001a141400110b07940c580401140d001703540042c00326400013401c00d00302181000146c9055070142d9111100710050300e89104c243e2280d4003940d81e1800900d020700621060340c001510700002c0001003140031341e0414840069034a1190166040c5459450218045d80078151300d049066550004600015903c0c2e8854020b00c0703102415070554003480d000140c150381c2800a070140c40546040e01c0c61020360303401e0694510724290403a100110300782c9900c1020560301d904c1100921301c0300c00300044221955509a01d185026600c1080605140c6286d4641e0181401032400d081810b05002401360855031003a04103501a041c0c2c800030504205c6180751454901940d00011142107060540d0614229810700999040303e038034101400301f9014180400800c0701d654101c4a003409824400180410005c0000c28481d041c00d4005007001030400c1030341c000c140d00041401d4100030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 829464046 1250 829462796 829462807
    0x10c06140a0e07050307090203130f0803180d0509040c0e10090905061c1515090f0e160b0d020f040e04050f0102091f020309090a0507030b04112508030903090114 71
    0x1180000d2000c1180c460090045c9c03280c4641d09040c9a2858030b140c040c000074403410000041c80a841c1c001d60203103c8450758480b04080700c0243c1b0340c5a5944580540c0840d400380400318040c18207800c04510b0392024944010029081400164410311280300b000019034514424400c028051181c207402c940115810301c18110080740c090000c0c0030700b0000414209445d424100031050035000200701075524040b440581d83c07141c6598000300802c4800c1851182050107640b080280401c01202c20030444803104122428071141d402554090348051080d02d03030800c8201440341d01e00c40580081c14100d4500d45a40c281030130640c1c6000b48010b41c5c10203692040040051607980d0003c0c04032000610400043d0318154000242d0450291a40d2560000c10107001c014071105154040351054142c0e4400f003050401e26428802142c0c0240c0411800f0341040000c911210b0302c0b040b501c001294a441d04a000032020740c1e40c00100d42003910755040c9640040b03480201580c110505610284100050781c1c1000e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 829465296 1250 829464046 829464049
    0x80a290126011205030c0703121706090a050c0405090c070201020106050316090b1c0f0210090b040b2a030c010605060705100e0f0a030206090607090320010c06140a0e0705 75
    0x61084003c0483c81105280030000c2c21700c1512034400c40202a00d0401e540c03802d0540c64008001c0e121000640c450000e48181c01c007004541c1d00548024009022641d03178410400000e001c081c141101d10072043c80b00080c659926401944a41020101c0d1a11180746200190035150507030015031107508042442c000c0c441c0d0360007038881281c8a4180104041815070b010501c0580701090f00c4c0400c01030b520400d014040c5c0703080740808080c0b003a01c8941c481c60860900702c80000d0300c0d02501040c1c20b420002004a200450003601342401c0300e00c0480600c004100307064504006003226841e49410101c0c0c40c4c18020003c0c4260002030009581c024030340328050b07403100c0d00c4907000d2205280c0e6a0303132840051040c6200300030307000d1044c1400c0300f180d050049c5070a0181da80c0008560145907031040304001040e007880341d2950400c490b0b001c0383c01421046280103a403900e11210114904110b614039120000c43d9842c064141610030302800e07040242041e09010054451401c00b05000d64032a40c02080715 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 829466546 1250 829465296 829465367
    0x10b03040f02010e0607030c1112120d150e010f090911130906020d0902090115021e100c0e030607022e090b0403050301050315070f080a2901 62
    0x32580c00200c1124100203840161603074207981401d203401c40710101da030a0405412441c4181d4440c01000b103105005048410014102541140c5108a401020804106245100142c034000c0302a03880403030711860150143c00396101a80c0042c030300980c508010882c80207411221030103000020411310103c0d200340c035044a0b080100012a0051044400114a142070360b0301950215a00800035903544140d400c003400500742ca0318050380300b0b012080000408010900010b800349980d1713006004802c180e0201e09000e2049010200607078010344080f1103601c07045208042d20381149860b8620038070b80792014189402d20040880065501603480112050324840141c84ac2c8080b82e0040012a4960b401040c040c180201009101e60b50400910080682010147d0b050b0b030020380480e030b024001200031100d10740d002d0b5000d070082082005611006803103500380a6006c0c810341d03000b08070002c40b180f980381ea04050140c0c446200d04c401c50305060642e80700c403280d0020100079425400000041c0700f075000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 829467796 1250 829466546 829466551
    0x30301032406090f1116110a03060c020601032018130c0803030402010e0a0e221a0615072003120301060215010b030f040209040c090e030c15010b03 65
    0x50784403404100540321118440105004000260500c030440daa88038403000360054900d80b0030380605200c0d00090807041c4000342d94844078018540c1940540705d84038041c20300020210325820900e00350000c00800c0c80d0340929a10907900394000c141542c136500307015a05121450510088040c405400c1c0c0150380d402148038000e0821a1194201d6218860821030003007065400a0058100050001d1104800b00207107100714001c4c0c1f51214903003001e200b000315114007400368520102d03241c40864a0450300c40d1051611206880200c60036608507100d0502604110000c00c0c01a00141c0400c800f604080e6802c000122240f00b01030f09001013a9910311075040107020100c00340388200061062954108080c0912002004880340d0300d517141d0790000d46520b11115280c1c0c00c50504000001c02ca4145000c5034410001c0420f0020035840e16402c012000d4409002a210b4040d0420b0218030343d401072155840c2d815204005550350001820580c0c24800d1400d2041c92000f0312100411006915208403907 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 829469046 1250 829467796 829467803
    0x106180e15040510050d0606260a0303090213050a020c12180904020a09020c07090b0102150a200406090e090625051224090702121b010906021c090503030103 69
    0xa49a6800844c01c809600e56844158005d07030009a1000b40482036202c4000e80d074007403000307582000801d4100c1e841000e4001d451b03c0c940c0c2c0301c054042c0100e84030350320103680309200900c20b04281040c074004030240c0c1c40c02c3d524000302544c0098010b5140c1401c01c1b01d160280c03081500503080165000940100f0808110014043c00010f80010115520502154050894008119201e21465650175540e104a002d0803400526120b042d881541c0000765005104015500e103008070ba580c0c0c0d00340005040088918045481c0c243d07400445103c141010388003400295681515040c0307440e04454802d1006000561181c200009110740c801e6540a04800714070b5003031307001800110300e14044420b4800c01d003011000305070601c1800b070104410315030060740c2c009800d0749150074101882000648141a40e032100503034491400181000c210b90050614902100d20450340303602641041030a41c3c04031541102c51540c009800c44240c0701e902001c1080032840d00c001c02c92400035903115541c80c841800040d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 829470296 1250 829469046 829469051
    0x901090305190c08220f08121c0e1f1803110a1203050f07030c0e0f013005090d0e041109040905060609090d0c080c0f060106180e1504 59
    0xc0305041c0243d03444215158032000031070342da40d109841280c030464504040304440a900d040094440c44000381c400907544840c0162400514800c4281659404100701c0110640c00071110b01d108580c80c440c1140b50a0260f000e01a100d025481e048901600c5192122030540b40010315219200c000e440310203802d41c07600300303c450903031000c040d1071600c200d500b4000c0c040c101641d400c15440703515400c007034007071f80f5202c20090301c0307441e00d040a4013a1814031091034002a195022007615103800c2c01c0643c0c1064043c14100c1c14985c00d8103203880050f207007883c0e80d550075032284a01e06a24841d4880da690003200034024000302310700040c00130001c02100c0201c910890311351403d100300030501c10840740c2d10300c0300034002c101c0c03582b4030300c0c1c031940302c3e0030445120340b0481e020340018030700917408038007134031420348980e81d80c00400e01960b2981900d4101800300c0145100d104081e4041150411415000c0c10f91510b44843e8501520640c0d0280e42c0f244c1c10103000122050306004042400403ea82482003084402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 829471546 1250 829470296 829470337
    0xc030c080a1404030530031302011b081206040e03120406021207020c0f0402090f1c060c02070f090c052709010b070b09010e06012c0106090e0901090305 67
    0x8407240007091203000b0024500040000401c03000180f01d481142d50901c86452a9440745122010400d07000080d090100c01000000d940d245012600740761540b050500c1d003000e103400841c051000f0100b40003110260000911003807a0324990780c445522420844051080c08038003408a51030340200c01c0c3c0200d1800c0d0640c0410b040004a0f0103407030364084140c000408500d801c440c005e40d207100540d5801d01416410b40003401c1810640200c8100f45006051030000107a4501804400d0486908402640b688085210006000e85c05106261515079008015a0b420a25000348410450340b0462207a031404044400c034a4101042d02c80804d049012000c07401048100390440390032041c400c9a0081ca2a800031030040100800703405c910340500043d040e640e5170904154204c559010341d681d569070100f0700410050761840f000e04a050000ca203094a103daa4043e24440c0c45820303044480424030415062241c000003142260f480407906000b0f114174086a10064014407a60341554540c0808800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 829472796 1250 829471546 829471567
    0x200d020949050a0c2c180a08070b040201020601060908060c070312320f0417070b010f050907030216030e03150c0919030b06040b0f0904051c0c030c08 66
    0x34004441c50704a025101e00041e94600301121204500a101c040c0303960100590317400d840d142e50703c1540c1007580b21880d41619030306030b042009201402c08001902c01e11001e1070021342d09030003801000c0d05c6030751444c4003400c09100190602e10160032200421600580c1082034500010f03006410480b52440c080d80e581c2c07517007002c4595100e0300749030351582c1d424400315554800c00c01c2862200529420845070003601c080119000b000b4090702c00300c060884070b43c00700d80400c0c0000070321800400720702002450900180d5071620038500903800b01030400d0305c0381420000c6040600340f180d4840d09914045240c003801800c1044660f0340300d0300c09130410001080b1074016480420540300303a111041d0b06500b4904c1d0000b640c50035580300d04100d40c0150b2181000d0105000442405815280c0c080c65001e03a503038885062100806412000c030b584100b10003200003980e119040003034061030040d805402511414810180c84415000000040190b03452400012990120840b031481d035011000b96964559840e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 829474046 1250 829472796 829472929
    0x1308030903090a12060b0d05062403011e0c020a0f02100504170304030302060f130b0a020d020409090c0902160b06040207020d200919022215030e0c13200d0209 70
    0x5190f00d415621f011803030f02e14060a030400d9071381c20003102d803b0b104072020a20101d07181c078500c4800411480310070440710011710f04000703800f6649000d4a005070070b25a403458403400c201c800c0402c220035900006014000e16070f060124650000c200c403407030ba940341403070f072103001d10080c00740f101629458050b00071076440b800340c2d0103c4a40d00703071280080d0344440d15044440020021203400710340a41e495400000c0200079030090300c00708002c0080040c20880180c803a82404240103280641c0700d5070802c0100e0050b52200d0414030107a0049101d0043d90034410402086140e01203105445441c48008100036000a4406400b101030b21180150f22140c0d2260101c0913000401250354580032a14000b01c0c6640c000307556698008110713501480603087e01080d064031b4121030100f60b5006083e642080c040c425484c2c0020180404100d00c410011000204446440e00000059010a82c0001d0400c00c03c2ca003203a445075030145030b5600d0034011604c52081e5547c0801c0320382640ba084040b107400c43e80f0305400c017 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 829475296 1250 829474046 829474111
    0xb0306030f0106080f060a0e030a1209050604060c111513020409020d21050a05030c0711030a0318080f0d031d0d050d0509061308030903090a12060b0d0506 68
    0x700000d00a80c0d445421580d00c0b035a250640c0189441b0320300004249609500400220342800780c013071407a2000c0500110b03920380c100c90011650304e4444540d800001c800b00b0090b80704a0040e1030011b5030000f070760b070010130302c0240030030610305039010580800380b002d0310b41c1c00300307070811842945c0410000c0c1c43e10208000d0000b107180a50b00004100e100801d2181003079000003503070011015044001407807607065440d4011143d02400103042807001404101c04000100704007801584510500c1190000091400088003000c07400901c0c0e11400f41414650716481201030103000019069102c48603d5456455504a81200406480e0301c5140000c40812030000c1014401c0c00c1500e1110480305409051544040320440d54189404000b4412a03000302e511402040203131a804103154041d01c2d003441607000582442410300040152382d01565492076040001c29003103080030a400900d0408000312a90001c02074058070340d515482002032008201c0f658014807140c0f802003c40341c002030300031001840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 829476546 1250 829475296 829475323
    0x7090f060902160615080a020d080c101a030c09040605060d02060f0c0c0117041212090f02090903070b0a0908040e0901020903010509030a12020d020d06121b0f0b030603 74
    0x981c40d01402c01c0380c50456806401002e09105003c0401c60384003a00f01d80307101b81b40c065042070400000500d000c02c400300c81c9034001c020441c00c00c0040c1019506082007010703128025990f80f1851501c088036161024014a0700724050010060320b0700101e000013000a0000346040e40e1200001e00b140c1c0c0304010604080c0e005040740741c0380e003411011a682c0c1c1d0300603100e151a0b403250700070b0f0500030f41c842c0e0802c1c2120310340a500300b0202d8499135078540e241203000e00d00000307010f013401810000600c02d208060311170340100d65440080e00c460052001c1440b01422400603500104903420100b042103050540064050390002114042414003140314022600844c100e007a05206000d0941d905401500300300030110000c2080fa101e0300c10342640d1b4803c552007203012900e0b8070043e403c22500ca80c090180c208000e10050305c2c0044000040c011548140c106c0303d01110510403c0d0309011003500b420940b0420b01d40000704503810b00c0011b00c0d5002c22486500710340ea000000003101c40d1418000d00003030740403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 829477796 1250 829476546 829476551
    0x4050102162d0f02060912060c04030b0a05250504030206120603060a0b15072a06020d0e060d050705070209150102013603020a0f03030506090109020c07090f0609 71
    0x1040c034000c1c060500707040660000141850021040c0c6941c4501c010a82d03a010001c960166481da003171040c3c0750408050994010011441010094400e00c80b82d8407a14208958594690452034a18040b01000d080c20f00b9070307490b01007004401d1550308990040040400c1054208000c1110221010700c101d420080d04a2030108030450820b54810034240121012001e8589554458880c038080391140746280d03501c5040c50460801340e907004001401716500607a62607504004d0090005d072044c40643c181445011030309030405c00954140001c0201c00d080b890498007100c0348500140032400f40e000c0c3c030623905994000cc0740e8481d01079412103200720343c0906622018503159041c29041c001c0c03000114059420302c2080d01d62071646000140c0d03000422180c0c00d405560301486200d4000c1801021400d511482099030b000c40c80c034003d40040c0300d110381e0303010501d454980b050043c800c01c10780c481000c030750052050022030040810040305556100600048005042c081c0002a100661020071400e2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 829479046 1250 829477796 829477837
    0x90106111e0a110405070f0305150a081c0908030304082802012a08160e0904050307022103030f071e030f0c17070503040302011d0a030f0207060e060304050102 70
    0x1140490b601c1450760040c0310744040d41c00300f0fa051005a8500720b17075440000307444040c407040e07840c040c2c0e100030b030406a00366002d4031021076600410314130700494204009030340c0403c010f02007514040e1200a0951500c4c07805030304d01441d09040e41d40e28003015200500785000030034041190060001210321800c02030751024044c1c43c0118010b4002d200702802c01d0781d00c20fa1402c40080b14000c12460040e018510b0340c070b09110380e0b0b420700c1034841041c83c00d80700c000304800e2036003007202079640203141030042d801130000d15611340c07a5104104070029140c101312140e90345880d003040d03014000b2094903404412080c0c01041e580d5020703c121209208008e10070503581d0303400c002c40d40d44c5505908c29202d801034501e040102c100c0c1424161204070603030f02c4910080c04440300240b0224418009035401612074000491140c2940c400c0d2803415074004c0039090300d070780015041018194012100300c0c841d82c81e07002621840d07050000c01400c058180d01c000e0b0003284000081000c010b0700f5030443e010320020005900c10790 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 829480296 1250 829479046 829479103
    0x90203132901170703020d05030d020f190e100302180306100e09070b071506180209130504050303060d0201050912060702060c0412030e180a0c1404030209010611 71
    0x780406682000c41d440c2140049240c1c0707989005101c0002c880001011014955400c02c000035a06c800c0840c2c4601040c8103881d0015494000740000d00d1010010300d44581252108a5194074a02011020444c9403441c040c02c603101c5010a5502c40743c64680960b458071030010400c2c0281300c80102030f030940301c0c000c1088811000c0f00420f01c1503442c808d44054058845503440c0c3d54580090042c2865200b08014500c001402142024690140c0f0500804d0b020764a01c04404221a5480c00d080300742c3d00010706050a20308620032448284000400700300f1801c080e1105a070b1ba010080c131140c040c030481c0040c2c0c415680600f05a80560400030001d03008030b0282c8080f40d450f4102a685c0a000d40b055101003a030081700c103800d032030684d1080c0901403001002c07034a0488890310500c01725608108411104400301001114070381c40b07500816408100403a030341400802d0850100f82d030211516041c0420b00041e902c91113103078111034943c0b82244030030072100c01031420420801500c60341c41140344c0c1c18803040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 829481546 1250 829480296 829480343
    0x20d050301061116270605100f090b1306030b010219060f090510090c0506030906040303050a091e021003200c0f030a091503050c0d09030302040f1217090a09020313 72
    0x4e036641700c800d25952181e14001c601500c0483c05116444406180f6150080740300340e5020300000312514011a010740e40300c1c0241d00c5680301c80210301c1c402c50621020301403140c1501451511100a2000b050060841180e03413896020b0300200502e2292958201c22096080f074022503515a007280554020b490b0392280c03040181881003045030b50b43d21088001495203050740075248140061006000d280c3c0c0c480d0f50443c02407100a24040e052a0f0352103041d00840c00001519010540e02059003180c1e80d00d600400000b101480c81410406080020880d003840f0a103403224000380083c119039448a04d030500c81824070541d00e080503190301c00401c1d091942544500740070202c07100051504850040400203e054400c00c03108094251410403128214840c0381c1e2058160f24042d103801801e080e11082003e1311303000158401d002c150302404241050101001034144d101d2410610b41e450801440d02081821555100300c0d804035a000c00040ca07003031003510090250544c0700c42c05411403104044412030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 829482796 1250 829481546 829481579
    0x21f08070e0f0d0203070f260c061209071a120612030405090c072f0d02061213020310020a03110403050727020406050309010c02010902031b150a0801080d020d050301061116 76
    0xc0d8280418230300007108012800390216680905000c1c640100540c0789445100003816061281c85a1800020000510080b400c51185a1419039540d810018199459400090402803081212810301c6034446400000c0b54200d86040e00c81d5400d0ba03943c08602140343c0075000307018100480800030010340d030712008904644a0720080e0400322440d542c2c03051060304408400c00030b40105c2e003080300d205010314401e0019800042c25460400c100f946501090800030408182d001560700400c441c070350980c1600840c414000d240a2150030300d031640e200c180e86c4502d1845034081c102086254411016052040102c0c031404040042d90b40f25903440000b4926402103610320015460002901c24080c8103000b01070000d0f030014002d121604070708144c03103000d066444005074030100110991b4071000c0d110307020300381c0202c850f160526150315041c0c44900b410203580800c002c54102c112090302c0c0607044019281900c83c1031402c80c5201505001d8949030035a490410f050407440903a00049c6800302c00c07140030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 829484046 1250 829482796 829482839
    0x140a11090907090e0f0408030f0903071b0512060402100f14041409221121062a120613020715150303080a0203070c021f08070e0f0d0203070f 62
    0x60b0704d540c0f410b40c05100144182d4004206290400c007050484200003c095040720303c2d01c05032840c091580c0e40f0460720b410303001c605000080c0c0c038120400291070401680058100c00b54080c0149281c00c3d40004d80701c0b562101c91100317010305620b18100c1544a003000905090061840d5941c46490390a0b1011013803041042e40d04c500c3c0c0540005d8403802100016003887c0380c015490300c0042c1c0070381d580d40c94104407004000e0b40020341e041d410400d2094500302d0704280040e0740d010b0300d000d00700707001d242ea015100c4903241090314002441000c5544640c2d0100c40e04581d5414160700d5070b8035484009000c007070380044070340d4901e4008542041880281903551240741905c3e9804c111003007001c0b54a40c00a900c034440a4046054a40040c0e03075100d0640065621144d149445000f03074030303c2c1c0d0001d00c914403110004100c0354038400490130881e03080402160000f40078144a00f0003000c11780000c041807501018203000d906100020ba0454500308001405440e00e0a0385016241c2c4622442c0f5180e10501a0784 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 829485296 1250 829484046 829484069
    0xb0709170703061b021e01110714010507081e0403020a06060b0d0b040c0c0303021c02030907060201050f06100f030906050705090a050901030c0b0c071a09090a140a1109090709 77
    0x130024a02d44100e60410321540b5000340114030741d030411007280c04007288110740e02ca54840124855042190005203483d0748511245140294440b41c500e0843c0d20080802041c8840c0320203001e800e12031641d0b50008002030024106040da03940c0b40807410302218920040c8450301304080440c5a038111000f03040041000c00b010400703045108104001d440300031702e080000ca100012400c0100744039400624458496a524550014500300c1050483c0d00449035900280c115100c180000c50f42801460b0b040b070702504030308032a428900700051082104026020034040401c0c800501907000e42c00c0307104119000300b4104894a80510054241e5015588a0703100b10103040000c646450000d8400d030503a174209010540560812403c00406d502c030005640c542e2162030f2000a40c192100402030040d12900c201d00c8c0c9400344002808250030000c6c103014907107400d203504c40141c01800300c0e840c2d510410465001c41c2e200c02002d1031540034442da000301074002e8a22070801810b2504290301404944000410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 829486546 1250 829485296 829485311
    0x30c12020a0213110f1201260706050a170405010501060908010618021303060204060905091302010f03020322050c1008010b04180e030a030506090a180b070917070306 73
    0x326210071076550000d61001d003000102280b24650f61203072001d112044900362405042510b21189030b0802802580303da4003040050214180400c450342181400b0f42020050b811000d60346500c840190294404206021501c90ba0942c0704102c0148a49030504000c1100d040030704001c2d010b001d00740a2040841c0b1400b00c009401e0390144151411220a625842003840d001c0c80200003960204a0805040c14a00d50120210b100e1784002d00080c080740d26250000351401c000c1c081c201c20000d1a000c075001d41101d642c2d001d40d0700183d0441c8205814a001a03480d42c07080c0b072500744a0100040414040e481200c000300f00308000860680611040f02d4548c401d010790f0340212544402400f4240580a013800104440183d904150343c06140304880407401040c01c20340d16165030807441c6800c000036114001e104070381c10604041038228180301020720100e0382d0404150b0790302d466410020461149000011000c91092840c40080c021124103004800c8003001c03029540ca4107400261501c0c0e00c2d000f02d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 829487796 1250 829486546 829486583
    0x31003170a0203070f050319090602010b0d02010516020109080a150516090b030603120d02030417091027030803150d02090105040c0e100c0c0503060c2b09030c 70
    0x5554421100e9030046180002650b05d1030078244002c0ca044403a40b10920801e10340089204665181c0ea490381d039aaa56540380c964001d0039100080f2482d4040d10402d0086030150f41e0200131644001505581c011610740e040c030048131915500e5025110314011400c40c1420460400150907601d062010181b01544403502880c06140412812001080da506820070041c4103503006140d104030700030245c4650540e03c69512702c107070784031240d00c0d465694000100b01c1000500707c100b00320890034000d05403c26589402180c0b01c1071076010100148030400b00b20b01d0146503c254003c2d420101030400d100c8003503503880d2044e559001503801d80d0001884c01024069410a4446005d0701b03070300100508140d03482e100512008020700740c00c0070104004c04400881d2030b11a0f00d40c50916140321b0f038980c103c100e41d509242c4440c411507040301d4400e0300407005102c0c40408410540740800c00034a59052903e070810045800390314400078100c045030410304100141500050420005805400300425a902412 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 829489046 1250 829487796 829487843
    0x2010c091a070b0a0b0a03060501051914060714030f0306090f04170904020c120901030e030c1b01050c150f0901050412110c0d0c06030629130902031003 67
    0x4820034000c40042c00340402064002140640000d0b88540c00103490b14254003050090741c19400036107486845a0040240d8100041d140104440e540c5805191a042c181d00d00320100340541c0312407164001064038424452840b0f142c0e444426036800701c17a610b0192a002c0030031500102c4c1c0d2503204242c198000780e11104090500c0788115800980e841901e04128519100b80d0022211660003ea0900400a40752010804426944c2c490340707010b03849440c240001000d42c1d030038020780c81c010340051001040003900082c43d40040102450400d19200b108401290a030080d03d8074841c46204400c13420810740121020b0f01e0003071501070b4503100f442c3c0d03e80224a00f41e40c07082c0c038000d0a4440354628074416a200d9035118040c00485016140840c48202c0040d40d1500102800d40d02c1541081080000c3ca41600c5a030340140015101c00780da075801c0d40905a5802114041c4030045580000d014824007203603401c65010303202c2404e00710348a040845010020700350703c0c002128a2004456140341940010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 829490296 1250 829489046 829489079
    0x203210f0c16020105030414100603050c04060e010308032d040303061d0402041116032d1b03360f050a180b120f0d05030112030e01090504060602010c09 67
    0x402c410031640415401124107520041040d5100d0340a510a60014041888030801c0089280804200c0505500b4034604100c04580c140b131240d807400d401000f0b42206604503e0443e41c01994050300c03581d5510540c51050104200c406080942c19018004104100ca10601a500940e010082a0340b5a00380c41c03c3c0020080400015038500300002e030040c136040d04071150b80d03200d41303121a08000580002c49510042114210045a40a034060120111419620040f140181c58440e01100e1500000d029041d00c502c8140d00c0580043c20a802e00d402000d6001c0c00186208499210040030fa5880340000e034a800c203112210f00c180d02c00204880d9003a050019036030002c18a0580754a4030105070b440020000d40c800207143c5800441c1131b550345030542e502c410400e0002070329000c00541c2a05092086e541c20765000d0180500040c094070b2040c00d081459a541428480c17118007501d00142e03401000b5030b000c0d0713502c107061020101d01e503076041d0480e0340f0841090f110621280d840e480e1318400030714003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 829491546 1250 829490296 829490317
    0x110a0807092c0a060509012c0601050a080903040503061015110601060e0d060c1e020a033609021e090d020f1c08040e090607080402040c0203210f0c 65
    0x201650b602c41144640000c0e500114a1100003c0903a134510105030242000d13880b07030301c40900c190b60a410244031845034050006040781b0303a500901e000f07800600749004004c0207a007044100e90000303060200c10000c44002d0304008084030401c0ca8942540c070070341070b01c0b8010002c80718802004034181901072800c00c100400c03d10054625a8201402220a207900b00700c070560064103130011002044461090301c02c0402142e440c084004d021a030480c114515221003941154418141c0d2004a0381c400c052441141400021014040d03135000c4000c0c1c4410160a46440b00b1285200001d12440c1640148051741240a00341c04060070740d00c03071325242c0c0512208940c201002c802020300502c0d0103c54006907034401000c4400d1086500300c004100000301e4011503041030001018000714880b0203c580c1c0c0301d05100001c0c04989002d002c005d08110020708000e0040744c50703408800105000340140d549840b0500c102c40c0c038001421005082d86101501d5804a4804500c041210f000d050000c44510302c48 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 829492796 1250 829491546 829491599
    0x115051303080a0903080d09050c1903080304060207141606090f0e04050f34050d110f1309020f0109060507121202160615080c0f0301110a080709 64
    0x1542d110304031540c0c0206801410011803a41c04400500810086c000c510880000019804030a2800b680f512220429151142c443d80b262100041c500301000f8041e26400042c1a0302c1c0c0e19039281c94006809069002000880303800e0300114100e5000982e00030407000340d820000d0440e9511019113a0304143d000c0c08103400480001030003c0d01c640c00615030014850b404848408400a08c15070600e1002403c0c0c90500038094403888020398070302040c20600000e22200020f10b8907080002c0e084125411008000505070030250015603140448000d4410025000e200071054201d00300340144403d10f001c80c411001d5100a81e001c0d489010110180c590342d4552601d03051154561310305203240b0f40c0b04041004040042202000040d0019101d0742e444502d60344e505074800c1c50040306031440c0084074540c0c00401d80b410401c0500005000e03003580025070310072090b1109000840d014208603a0001080d5000207840c024030356020743c25030f2054140b40d5030000000d03244c00d170446a500304007061500646 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 829494046 1250 829492796 829492799
    0x90605130506030a050f0303040c08010c051917100314190308091903030f0b030a030e12070e131e020901050103051503010e1006060e03060c0a110a050601150513 71
    0x302903a0040d60401c400030101c580850340c0d540d40c2480c001e90024012400c0c2c102006000400c503005030075801400355900240644135a01c880180036020f5420545600c400c43d03080784540341d0051205484800d070f0320001d500d0501c0c0122103000c3c1c51180c1c0c03204071144c600c402e5411566040206030050a00e4036590800c0702000c0302d0700d0454010f00050074221660003104040f4580c1c00c11005419569031103628003203140361504001108903403c01c0240c0b4003e410841e580350019a1094180852032400c85141d0041440c100a140c9401629040000c2c01d15503d01030050b1110086144504907104c1c1e88600c9003032140d5540040d000b01c00c0b074002500040c41e040103000c3c40d80640c02440d400700b20625580e10020440002030f0944907400400f80381a04402002c000c04165405007074081e048904208850140c1140400d544000c000c0120352250000b01d209010140b16640540b81906840120741c0038900504041e13458400030f10500b1518107840d0001920240654162266403040f0101c0b1000039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 829495296 1250 829494046 829494079
    0x7090608060a0533010e1905010503091e1b03150a020a0e0d030806030d050c1e030906040b0a030605041e0b040e190b070207080d111903030b0109090605 67
    0x500c80501420071004001d1000341ca00110f40c41130400c20200710a400744d20314038040014102e0341101384d013580603001034059421100c40300d04d245401c0741e00030b1901581e0799841000c03050a2050b98a42c982d882e0880a51002d40004c002030008000c1030310141850034003510008040c0d9802d6600c01d0403030218000e4000a030703807480c0b541c0640358102da40d042030f004041e5003800040d9032851280003140400c00d00c8050001c1c40c00c0400c01c4480d40c610600b07000b443d004103004059501d104030219402d450540040740780c10400140192106508003410b02519070ba12040514059080f41001900092500303600184500d020b001d6806494082c0098a01c09000c44c5085005048003c0b9159009a11040b101015030410030a895040c00440020f40e032000c194600a010240d0252080e011584420030503c80712001181c0c1c40d4007410a414402c0740b090020b80a0380c10002c900e264050705059000c0f914003459019000219803680981c1c9031065240c07541e8281e002c40d40580669074100c11a01108200c0303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 829496402 1106 829495296 829495301
    0x90b0c0a081c062907061b02030a080c04140603041b0f0504180c0e0403141201090b15030c0f040e04060c140306030a0321051807090608060a 62
    0x80025810340380502c03221a0711300c002c0c10001691070304000660744018090020395031304040e40941804085d40743e42104800b140400c0c084000100d014070321204460070b40780c81c13003601d000e080417038014061540c0004104030f0385030442d540d011800f81c0845110600510200c0500082282807070140800d031158040d600c00000204803804001429404000c81603401c0a1540300d616990390504031070340b408041e40075180c40700018120340803041c841c500710305032041e8100a021201080c81484841c407481030b00d40360210000d1011419040c2e00f80018106d40c203c0c46500da06280c0c550102c0700f0390a800783c03822200c1e0303581e0740c40503040c0039003205486104e008140d091358103600d40240843c2e100e01d40100001c08109401c3d1601c46020786804c00032180d0a6003410400462034514000181141c56452245061060301400500f018a501070b00040d681d240e030142c10251035901c1400003 = true := by decide +kernel

theorem cover : BRFrame.Cov 829316546 829496402 := by
  have h0 := BRFrame.cov_init 829316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 829316546 ≤ n) (h2 : n < 829496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
