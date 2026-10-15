-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4336
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:17:41.630654+00:00
-- url     : https://prove2.me/submissions/0bcb6e8c-4599-4faa-97c4-2b78a93c0c3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 779676258 ≤ n < 779856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 779677508 1250 779676258 779676263
    0x130216080f03060f01140703030903170708100f08060a050a0b0d0506060a1202220f1a030607050306090a0b011b0818031b2701030c08060a0506150306040f0216 70
    0x3038044040c904c541c000e01d44942074101307610480381060601c0d0303800ea0003080fa115081d82031100c030303a46100128075200d507101c0c800c110540c1c82c140c7c2800d18006008040840f41c20140a1002c4507005018282000900b20751043c1d90200100d19031301d40c0c41c0c10800609400c0c40a54005450ba030032070050040c00220a40035200031754032680c1103650343d00380003074004034008020b600c88010f00c810a801c1050f4070001d1042e440c40300c03000401018016041d03049a484901190341c88410044581c80c078a0184a490b42c0011a410124554504130000540405004000720070495603000d0461460b441404404410290318103801011704581c20b0881d21904460f01900c664400500c48024a003004150860202c244001c41074000c0425800c0104002d0358901d01c2030320301440292210340c0000601c5507402180600601c2c030b0410b007481040c5080050060495010904040c03d0020984804090b000d560b01f100a40b542c0340d48541000402510013002c0c0d1301400d40c004100c0c9042448090440c82c031951 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 779678758 1250 779677508 779677519
    0x31618051009080d2d1701060908010e0601060c02090417030a020705010b03010615050f0f040e040b0f10051e043206060d05060d080d0b0a050609130216080f0306 71
    0x8820400480d1078403000b90701218144003841701a194850403000c0b0003004e007440d042a0a40c4132804017502e900b042d0907031024000842040d000c0100e00e0003841120741c00c03041c40c80600300e15070514001415411030100c2c000d004440080015007404140400c442d8800c503000030980c0d89080014000f800b9402801003580c155290444020491605103c1c900c101c1d1102002a00003050110b016212354111b4075401c143e41508120100305515503c0062000d08845018032400717007018100b5000041008040e55481040c41013445481121034441d41c040312400c8401040c524421040310b24031030281c0b10130716000b42c2804840e900c00d004100c48855080140122151016200c02c00c0142c044401c0c0d402640000c01000309540c681c0c0c4580040d079004401605c1d0707003591441c80da01c4e0192640980d520b150199525092001c0c140380c40d4003802d0050070b0450710075090512080018125180540c0340c180490b07400a00081074401c60f001c2c42d10f9072604000c1c46911107a202500c1030346548115000c601c200d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 779680008 1250 779678758 779678773
    0xc030403050d0f050711040b060d06121406010e0408070804031b030312140a18050328030603020906090411030d02011d0102040b0f0a020c060408010f0605030303161805100908 77
    0x8600c84c1c42682c0b4a940c00c15801258681d10100b4000100104000c00780c02a01c1000901300c04601c90003610010304a105c1e800d03080780b41900b00b050b201c1748071a1101c4902d070081c100401c1418002004035400681000606039503511030701c2c0440750791049030b20040c416102240c0c0010315501600c410b1045038001d44407000c10510456080e421924030b8903140c5030851070314003c10441c0c0641d034015a242880195050101d525a0b2141032940d044111030010008a01c010400007513414207100207208402e0400f40700c414155400a40b0310b080c01014180a40a00303030010b0b0034045010fa09000000b009400d03210624058603000740609080c80207030303c0d002d0004440085c0d000c030501c212011200d035103140d10f00341456203034292644c0d446885410110320a500c5200d000d13543e000000c0c0000c01064000042c0c40e00728280d0a010303158950302080c0309820600800c14039810140411001c581d1070302e401200c8041402113400d901a0a4000d15003140c1c210075070f1000550444404000d0750000300c11100c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 779681258 1250 779680008 779680037
    0x9090f022502033d060b0f0a091d010b0304050c060f070501140103020108070503150a0f060215010e060d050f100b030f1908030a021c06050103060b0910080c0c030403050d 75
    0x914540b000c103400d84c1611003007241c0b4200e842180c1140c42240700180414415910740500301c0320b03002950302409511b0300081403071401c1d402c103124100800e43c45181d000c10b04e6502c220040402c10500c02d608103142c00100141c10080240000c1d0f000f003c5c001d080d40c0d141c0041d00540c01d026045004200c4540d0310308a401d601e44920b602c0c0d12030482e0350580d14802c455445040c00c82d80d035040640145481d602c01d5202103040c1d035400304170700c01400f034000d130000708035103071550013842c2a944461285462001c1c0d4014481443c0701040c499000328140e8001c81c0c20541460014901b20703800c0320076842800b0705030010b00150100d40084c0d0005408804840f020881c0c106a552076542991700e079140712038040751000c0091490400741d64481140c02005082001c800d40e2006480c04000200111a903580000c0c0300646c2c15100c1d2030058000000b441c2e0800503003201041c184500302140506200e2035200040c0184103041c00c4507408074001040d0703030700c40740c1d01e00d80321355034032800050030300400e24142c0600d02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 779682508 1250 779681258 779681293
    0x1030c0617040c060e060d050403050909250509030f100f1b02151e04060c030e07051503090a02061c060902030f0604050709091a150a09090f02250203 66
    0x1458001044043c0549080c009980e8980078411403074002c070007070125a280010500c2424840e038025113849984500500421499401c0209200281d0030640c0c0300760680e0414082a0b03000c050203081c00c42c0d4035082003000a10780301308070901014501c01c010008a4400c041d8010100500d01c2a0051002000400100c1683c0b16030001010050b400b4101030781000040028042d00030075000345178496120b084c9030003561a401103500f654055192103a03815802d600d803041e91100c1201d0001340020a00b4003000030381c1103d2480d28500141c8021002ca40908400d00c0803000c0f82c1da004148566559000640d080410150300d08402440c1c40e0040c0024210018001c4078490b0700e8068040710240e4556041000400c80500700c48200301030450049003000b104d1240340010600c0c03090000882254004014880c00060040750340300c84103100381058607400c413281c1e00c16150350840120306908002e910100900603081c04602c1701e03c010032035a40c1640d201e00c3c14000c046c0264169800c40888820942 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 779683758 1250 779682508 779682511
    0x170c0402031e04060603060507020615270a0e0118110f060d090609080a05071e0f140a020303070f0302060f01050906150c010c02010617120a1209020901030c0617 71
    0x165000b101480c500e003003502c842507802403203038100081042d240d031504011682c08a0740c07100543e02c041e082c4018040328040fa010a4034bc2140e8101c0003420b034140b0380140e04201e50240703152035984808500c4409003504200c140444180003081161008040c03983c2d0003040040507a0050140c0d613284025090010340140f103650058021071402544500490041c40d021200f514119515101100019001e40c014046c030b2089640b255180c40700b9040071740d80d5203664003107420583c9031004c0d5500000d1030170025a0941d904860005100609903004906104a1400082d0b25020008403d41040a01c0800303c0fa2030b4029801c40d11655a4a40e90010b01e030b0087c0903160348a400c1d48000b51440c07070310807a91032075500d081000e5030904480c40030042c2501e40b40001100580d444d080f050022070071528009031000c00150050440100c12240d40c0c0242c4100c2c0940410000d01c00c4100d22200b201c1d80014042e95030280101c1059a52403d0107941240302d07004110016071041514403803105c91141d4076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 779685008 1250 779683758 779683771
    0x1c0f050a0c080d0f1a0f0f09040b09160b0301030c0509070c02270420062104031b0501050a0f0b030c100903150905010f0c081308040f170c040203 64
    0x559116142d01c0d03804080e04000b20340107a240d02d50b0940d40207030810340141486201c0600800381d445034000200414134210508075401510605051984c503940c0d10b0798180c0141d0800003c010684442181508042c807012030811105290341d40041c080d140c9000075030490780200c0403100c90703c0d115400c1000341f0005541c41303000944601b0a17500503290004000c0d016000d007102d108049800c0c0d0120040320441140e06868010f240b05c0050030039407003407031002ca425004490182c43c00c0480c0801001a0311000c08080aa000480009040502444190b10035020300b1112044810b924a02613010b00009c48a400c400381c2000c00d9030310080034a000303030384084900601401c21380c0e00c0d0505100c514910115180b04000742e1034000008503020340c800742415154600081840d00c03440c10030b10309440e041c2081030007503072808250105050348040c910b42c01402404035901e010480341456030f0a400796411144414400540000790780910100f020743c40c00c000380c00d03500005100c0041000328001141c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 779686258 1250 779685008 779685017
    0x1c050105010912150e0f0705030606040213090c0c17130803030106020a060506211014160503040302011407090e0c070b01050922200307140f0a03051c0f050a 69
    0x42d14001405113140c0b007903000001d02d00003a103d040d40c00a500c0c1501c1c1301c60101c41078101110a00582c00c0c00e100303083e40043c06603015480c191b2041c2c0c11001d01017040c41a01c4203295155000342c50244516140e260035a080440303010388601c0700079595030355404150320004020705400009050f00022054a040340d62613000f8001900d00c030345079900075000003013406a01018154a80ca001403400740c400c40f80250040013400c2002c00c198408048a0700c2da00b80c00c450000b014100608046116460000c4030f442d0326205881f40c8661809a015000300c62841240c29280001c0141c0954801e00e501c1c00c4940740c0391400c5150301d0b400089002803244d18005460f000000b40144141d040400c5001e81001000c5070640c0762014004091010a000d40d5007110748060341011101d40d03804683c00ea0380000c008a016141e154685213880042000c00c42c841406161000300040351a900e50300710030001d6422030150380c0c0d03600d200392000d0008101a158400030404442c41c0f4056584a00c0031340d0203204207600e6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 779687508 1250 779686258 779686289
    0x10b060d020706090b16170405101a0a0b0910111c020a05030c010c0305010b1201140103090203060a020a0305160e010c060f0e060a0605010507080f0318031c0501050109 74
    0x40202942c00140c00f551a90380303500c001e80000e40e840000e40e106181507100100d10b06400c3c00001e103560158510384141d407040c00f00340000324002181c4031a20b01d00d031040c001984100001009d405031038181000da4404040c00000401444a10041141c070300226110368001025440580320003081e01c1c0a0b280c11307401201300c103d1344508600c03c480041c0c0f00e40100c488140043e9a000d165501000c047c1c2c0c04d90f511800000175103505801518090300050507028107042c61a0380404480d64144a40400c1ea1003161098429900a82c0a941030707170b402400381d59032454034041c003501a43c0302801d0480001d05d418001028079200d2072204900e100e10780d40c0d645220000d200110342c0070075801c100b980c2e030b513603140c00007100340200c2e11951071403d0800010340f42524214511500f294440c0d8001410300c003003080708a00140c01f010485111078040780000e622502c60111210342e0070514501d0007501d1100141545d10f100034407441101c070711114001803045a880350011140f01d0380520031140384584040d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 779688758 1250 779687508 779687527
    0x30f040b09061b0a0302120c0d120f0204081c032a050d020403030c14011b081906031a0a0204230d17090315010f0302130f0603030e12010b06 62
    0x1003001d090014281d80c2003403100403054201c1d141141140d01d1550000500e001016014032010f8440318800d0262410010f80d58946521814400c00c40300c1004024003003204081020f81c0a0259401e5000045495a407140e42e0751f0f40c8d031000361800c10b019240c00104400100c3c0b003401010710413003414000c4248800e50700100c1070454070b07000c40e24060080c18020454913000078806040214001d80d2005404442428070505c400d00b40b1444405590410860884a004640300710b03035400550301d410352080da202c1440506030382c18006071040e540c3c01c0c180c1c00000d04c0340c1240d02101b0352803210340040460325030201407002c920031441041d86824400b1101c0c0301c0000203003590b07030351440064011601d0b02141d03604d0040d4000c010041400d040b801007640086130070100030a900c0195030301070340c00b180d5040ca000030700201c102e071000900c50324954030259141d02d010b420403015a140c0c501d003032244a80700c2c580584042040942070740512004500411140e03014060382074200000781c01d040c5404500c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 779690008 1250 779688758 779688779
    0xa0b1b01020d051e070e0913080f0a2d090302010302030a0f0c080712050603070b09060421021e0d15090c1503050f150108150d030c1103030f04 63
    0x844646255802e000c14611040030707002d003d01c0ba50320344400c074071103843c860b60316510340300e029121000300441031412454544401000d26085052810401d4540400b890154910721845c0f602c0b504170800414180d044e55040700c01c00340b120030315030002c1d0101c80135030708454070403880c500c1e20400141c003a002c01c1000d54000d90045802c02c408c000045094401009010140d403001101000050b48590030880410303840111842c207084034010074469400c0042c0001d541f20309500590b45841c40c0042c0c40700039642c401c411280105009480c16001602e01c68036040501d04903a404d80c0240304624410780c2d11410074200d040c0e4550020403050f4000020b44806004002c6240300c40c2c4d0b040d544400701c901090520310814020604180d152007040c224490003401c2c0d410207012841d40500704400d0060024034034400300354000e402c0c0ba110019070340300000360803402000c0403019080702c0e80940081c24182e008266501c0e03076004100c1402d05003202010b01d80c0c0c0340300e0001104640901404244071300c1d03516 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 779691258 1250 779690008 779690047
    0x901140a1d2d04063f021809192310060803030a06080a031209111e090115050f0714030307080406060e07050702040506030a05100606020c0a0b 63
    0xc0d1006030001c01144000001c0c6907036200014080242e0100010a4941401007802809665080c041d611481c1c2c0340c1c0e0142040540da101788a1540503481c8140159a50380c099015074000744400c5401000c22041d0511030001d480302e504a0003030060302c044544540f40901d00c403592000b5031a02c40d0b0800840600b44c0c50401400d94601e002c0c0e0402e9060204590007000701814110000e15583d007014229001129619030000186800101001c40030a1300010700760f8030340e8000100030074645081d1410f0011384901007145075100c081865072255a280714032480c10540f81c2520802516601c968038401031410b00f961050005000b00012010b024516028242c400d105142c1c041e0800384a0707002e0ba083d60403c0f103240300007681034400c10017488814043c510082044148102d514240b58000a00900c1401000f9000701d4443c008500e00e0344040156001054101c0c0c00c0c0e0f001d040d01c96036124084e29652261500610418685407481c1c44c0c00ca40f9901100c42e4240300e6850841118860380c4107814 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 779692508 1250 779691258 779691317
    0xc170316020d02120d1d04090c0501081801050a020703020d08040b1308070b0901020a1e050d0216050d05032d01090c091703040527150301090212030901140a 69
    0x60300d6441501d03e4000700060955420180c54984407104181c08802d03840e4818146c50384500e04041781140405d00c18106076042e54801c3c41d1103011503503103142c00b081912000c150f0340a10f610f41001c00195014950240103450b1003a42a6880301284070400c41d102101914090514440840414001204c441810406070706c203240044c1031040d19140c80108a20840d503206540c2d40015000303525a500c00d01c0b10703500180000e1030341180301c03120b07a00030094010301070301c030020550008040703c1640341c040c4a0341d48103910004540201001d1500100150820303100040d1115002c1c0882d05000505034004150380d142801c120282e031710b048a210041c0c5000302002085c0a18640081001d0b2801c0c601c0720980d4203118011955580b0b00001e2051092202c14000030910400b041e1140402542e48510b070040903180e01d4400b8480f4600009004000c140d02c0290b102c418202c09281052003c800303403d2f0107000b6210b0120021440c42e882440f8410502e1703003070000d011907020380c603901440741e18044180c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 779693758 1250 779692508 779692519
    0x1502010e0a051c1701140a0305010e0d08280b01051908040b0c0909130309120311010501141c05070e0a020d061707061115040c170316020d02 62
    0x1003500d06080807540d0300252442e4200307010f141c203000e002071060502500645860f034031040e01c4803079120782c0100c10f0140746640140450a4017990f6907072003e40c00915007000c000c22410003100441507072008081d03a400d0100e901d031800a103480d030110382949040d110340d18200c1c949c03a14880300c540040c450201d00505205040c07000005843d410244850340604035200e051450a240c1015020304074024518041d6203030030882d6903803d07202c1420403030700060400c3c01c00215040d189001d50f441a81c43c3c1180504421210050080c0750b03110311100080d840c254000c001990300d03030b0110344001d42500c00b00c0d07800a6010955000f0700003540c0c140040c59000b4010781d10600d49500078500c00045c2990a88103850b0081240307800511588503e100030511380d141d40400810001e841602c1d0103a61140005000785040740c0003000b01c05015241c0150a004031240301c80c60325251079a103625075030080c140c40c400e400350705400300c40001046030b11000001c20140c4601c5c007290708200342612005003c030b8204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 779695008 1250 779693758 779693771
    0x5150d02031b0c0f15060a26100c030b0d1703040f0c270501060f0c060222360209010e042c060f180703050f01050a14060a150201 57
    0x1107440b5000c1e1610702c0246000c0c100400c0303075078481850302c41c1407600007411030b000d08140131030b80e50750030801d030200c2d00544040da40f000800700d15818086400c7c982050140954101404402003070f0307000840014458504200040c01c01b0706200e914281203200034030b1142010740038580e10514901447e8803901c03c00c1c44c110600084c1d034440c07094200d036501208503009807a91240740000041030210220142070310401c15589410f0004181000c3c3c01000340500102032500070030301038507804880c040c854045903400400d04403604000f940451348250111200e180d0140301c846a042d0320305e140c0310309140c01c1c8000340c9540c140c022b034001c1d40b0072007519041c0410303904200703201e44850040381e01c43e010041062a01c1107072901c0212802c840304e40030506c19080b20040022008424102c00c0c0c100904ca101101c000d005814090b00d44101500050414807500341156025541500810704c10340c2d14031380070701141e883c0104c9049200e00644120350721084140091100da03609690424000300180b0010030b40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 779696258 1250 779695008 779695051
    0x604110c07120b090118020f060d0e03030412020d05030115050c2407020102070314030406060b03040f05070f0506121b0d0204031208060604230405070e0a05150d0203 73
    0x20007071541d005907800080c1d40404828020625a0240c0c81818103009000c50106100210418140840001c0c07054041720020220340d115401503900301c1d01881c40412480f0000c80025503690412034040341c0381ca55418040c0483c502c04030317030307110100400e03142c3c54103603401c060145040c910038604070810080c040c043d6010190702080a210340e118030104100d014418a82003550000000b0315043c2568010800707000044c0d0700178180030804849045840d141e0f19189072801c0070305483c1d400b0206100000c0140700610a980c1000343c055403080089800c075960302d0304c00005580182c81400c0c2d02860500c8507440309441070030410380c00752000401c0d00c0d00c942c0640d043d4149820024440c0760345503021070103200700b021800381e11142c581982440903643c40d080000600c02c0c441d0b07000d0942071065422410780326280300c02d00c80c0002c840040c0f05001702d02d02560010300d0160610b403c0362240081640000f09428000b0301d44800144413101185462405490100a940040c118003200400b0a0f45550b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 779697508 1250 779696258 779696263
    0xb03010b0d0f0510110c0c090903090d05010e0a0b10080a0c030219090c050a140301050a15050f03040605060103140f010b090a05100c0219080a031d03010f0b01260604110c 75
    0x6070b0248600040d1513000d403030ba0b241d00e000c1f00f02400c5406020b803401480141c1d0400020351721310005c00c41b081278442d0700c1d84c40d04501511100400d5411803040d0030344035040004030120740b8400c0c1c030408410380c00c7c82d60304e540142e0317a007110120180079114051014005414a6010802004c894401d020791681c0d484080c3e004031034601d0440c10004101113100220ac0354040714039a03503040d0600480707056504281c006043c060041c4501010342110b6499100c02c00c1c025400d40b5501c4103812100c42d124689820500050401110500d0000b442c00c009144903821080d54a03000f030347d00100b2140a0782c2002c40301c1407a6400011a9070303000e10111800591a0364510001036007d4443c0d80d14100b81c001c41c0f06103c081138991403000b00120520b8400e02050b00c00240c100404c54142c03074141e8010010b06ca0b042d2070600c81000c00c6415508002d8802c0381140280c100682800003a640c0350004115195200d07030241d00c0c00c2c840e0400003c00300c08a070052515800c0101d02e80880c1422616007070b55100b1480c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 779698758 1250 779697508 779697521
    0x604090209150406170316020310050705120915060105031e010909060c0924090e04050703030f03090803060405072f0c0a080613080408010603150b03010b0d0f0510 72
    0x1042c061644410b00901e041c1401120014140c803603215144c0d52a120056440740548500c008a61741c03c0e800610956030100804d008541c1810b404215074140312800134000c0c0e2084c2d05c04035038036000c1f102107030640c00001103c680b07000180d06030040341c0d20f40c03400450322a800544000003c01c181d1540b440c5c0380c003003544801c5c020410380a000520707000614111059505207001c000500c84400410000e00541d440c1e5028241a040019a200381d2800016164500113812960030002081c0c1000704100000030400c0549000381c0f11080001c100c01c0b0308500350380e010380005210100038004280c0c2c5052a42100390405c03a40d041c203805a680230080344240c40460050118403608001c440301040409200303400b00300e9001d9070030002090070008080c4d503030f19019018001c1c00c3ca80c030b50240140100c80f02500c000d0311b51507000348049556820034084545a008580070710700e141c03001c18051450140700b14001d90b10041d1020208801c291140740c0300da80d4901c0160b50501440340001443c41c00b034071814 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 779700008 1250 779698758 779698771
    0x609020d0e070f0e0712050717060406060e04271a092406030f0d03060509060d0f152301030b07090612020c0a0f030305041e020603040602030604090209 67
    0x68448110403112015289000358050041e00059400c0c01214204000305040e5032200300550559101c0b4002124a20411541209294038001c28420007035071081a40841129518400c8140d4543c42e04100465613103101e1710012039007054aa15042c10103821600300c012081040b51014183c8814681c10b00c0304001e42103950a6031050064000c950025845810200f907500524800d00c0703000038880d4040a4001039410200c810300001c416030360030402c01070100c2400081c0d40c12219070030400340281206005207032186480c42c0014003035051040110b12807681041007407001140503150800940c0f65800c105088580380c904a00946442070219120900d83c0c031805038003985581015001c0c0800a04044200418060b0400410b5804020040ea0b0150684010399075032011440320710340702d85400010001c0c5002d8185100707058060b40064819400b614031500700e00c0c0c1841800241c00b01100000b50701003024030100d00481c5665000e56803091014000086500c501d40010b00c0040b01210807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 779701258 1250 779700008 779700011
    0x70f081f030b1e07020604052a0a08060a24051909020f1809060307030b07090305010509030a03050c1201060c110904052a0d080306010c081210061e110f010609 70
    0x11280100c050f01c64590011003840640b4003420a0399400380c0b1000c00c7c260980000c0c101c45800b1301e03940c50440e00f00c1e0018000401403a00300d50742d2110a51200000c80b00c507007a41c0e02c0c114103114441d44113180c080b403c03101d400d52401068100004c00c403c41c072903000702d400c01d50040d0001140501c80780c402080222080d0b14070716100e042a40c4100d04d00b01c07000040b54003c1e201101409515100011a402030b280d001c1469506940c840704112120801540003514640c20b1000f40101c020022008180c14001c580e005e115565078108020400d201c0c00c1c0715610b0007810300740100300c8144030700034600c3c0c014442c0c0700a10a207032460001902b10b20050303805031115000034081016034260341c10149890b017540030449079510703008000142c882c6032441026010400c0000020071a82c4680034500c8000d500c40310154850441c006681d10456040701c2c61404541d40b0103010525a01030130401c0000d0080c40402840c400c5402c0307007100c550032100700d0b00b021885210743e400031041d002c1c002c0102401200c8030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 779702508 1250 779701258 779701291
    0x203090a05102a1e110c18161101020a030b03070e0702030d11040b0a0e04050f090304030f02030a0812070e06040b25080c010c17060108010b0a02070806070e09070f081f030b 76
    0x24883c21b1103a82c1c0501c1d4800c0c0d40d904103000c0c2e40f802e880c14003a40080e0388070524000140f8850f065a001c9588851340883e94400258840119010351003400c00b02c1042e0215050740d40c035640c1000c400c40083d01c54002507803040c814000d003400c89d0380040c54440f509085d0ba605013175940940d44640c0d0040440600880c0b4402c0300400642480d1182e41d03400420b030000c901c4d01d8101030020513140e1140b40406482c2c4000e0552400c150340302004a11038082d0700401aa64034000d280814140f40000d6500100050901d02000501d16241007a901928065410180390a02c034405100c90b040442e00404c8100e8071840e82180450301c0c0380d010740703510540c00001003441d40c0f040c09c004010700000d0401072030b01441e86040c0040f503640702440f0340c1581c0c04074513203076510b1f181414141d142280d95480340c2050303ca50410040c1141d840f41d14030400340002c2e03801d0b045a407601c941c246c070481c03c41c0384400d00007a0840300185403c035500c08000c90003e40350420000c9036841e80c403021380c3c400044980217502d420141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 779703758 1250 779702508 779702537
    0x5060c12220b01030602190306060e010c06020918010510020c01170619090c030b030318090402061608090405071d100c050609030301140d0807060b04020d0203090a05102a1e 76
    0x11101c0d40d107031f62400304841814004003400c0d030f00708036105030b04000086500f40c0401500d0303411104103038401450707540d1006643c0103580c501e10090040318024095240d14441c4140002004584401c058490012042448080c2012580d0013840c0076440a5604003142d810700e40715401da07020f00107401c1c002c80c0b80d21803a03502605031942c940c040c0b4041d500030801202c998030f10f49403c90910100b255200101c1e1102d0001507040e000d81c488200078900c03898000410005c100008011507241510705000c0c65541e00f5060b10b44c105851491f5982e280e050000c0719017450710016030484190a1304000c00038001981f9500c0c81c1400458080265920010052260350949406499034640845150000c1c907020b540d010094040c500c80144026154081140155500d406955210120385c80440d10b0749045007580e036440180442c2901d29002e8098a040c000c03520340200d140104074102400c45400c020081d800c000182018240c0820120382101d0300340540800c0700704994840c85c5c0c2c4a603002c01202d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 779705008 1250 779703758 779703787
    0x150503060106020c0114181504050f040501030f03110319031a0d080d0f1116030806060f0f0f160804061215060309060b061605060c12220b01030602 65
    0x1078210b0020356101c2c4075001c040d6030380034045009941482c0c40081c6c440d072265003225010110b06019075404240c4642c441e1111604d900544200e5108075106414040d41805100c00c462082c00080c3c25043d8030368540c808a8011061126a43c405008491a10200303c8480e00d074806441c00880000f030b210807a8508621003002c208050074401c407208070f044929540d0790007062203000b0308560311544840407280d1440c41c0e0b038815550101d009514036070320030400090310640c0321310002c1100451080d0010651905140d41071b140c44100c1034071941e01e00346100e90032900940080c202030f10022030410920668108000381c100003d807191105a4866040c4600540003413400b1a41e0404245440404410340d45042d440e4070494800741030001e8100d54a00344a07003e000402c000d95040400061018104008514134548240c01a029100107444540c040041803140701d540554801070b540201c2c5074100300c074803882c50301802c0b514008c0c2e04c04440e9a40e5860000c09a00546440b030740070901d000717044401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 779706258 1250 779705008 779705011
    0x1050603030c0c1519030608100908040603110403020a03060204150e09040803060d06110301080f0610060e03070806131a0601120c091a07020a0503060705160c030615050306 76
    0x3100514102a00790040b15a5822a090103d10030000d409014601d09058000c50300e840501d004102d505c0e0f50800700c080c010700454880c1c0b05d810300ca1110010020029403059410f200d42c0500090700d46494848100d0240900f01044038800c941048000010b90f036501c2c08000552103240d025803140d19124500c0ca0750349070780341d41c401441084404d0761a5070f80c84408050b4440d5202c02690f40b00e0b2181d4010447d00d000c280401011589082512805076400d04044c50480c0c44803000c03581040007101e4200c0e00d6071030649042100c009543d000744a03880c042c6480c0c10b00e04801a0407100d500343d80c0c0c00800c0c40d000068543c298518690040c9800b8000701c5414140b800300c001000701b0040c104503000a0032001e0840154000a0b500d600c0b80c00c085105250034002080030409450485282c400d0300ca0069010010407446400d040300002150f05010a02c50320500003621824200841140ca2a0890100340b504070b41d43c2906880100000301c00f80309c1e4544803806000084032940c101418945084030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 779707508 1250 779706258 779706271
    0x114130b062203121707030203151c0219030309050d170a03150e0f04150b030a05070e010f05100309051c0c05010c1e03021602090903031f0f06300e0105 67
    0x8000f04485c50040d00c1c1c5061a130003c6841c500165a99103001284200a46440176540d000040c11031919280034480e4041600500844200040d8102164000a410f98a1100034040791072020704002c030740703005885034003c180200085982e0400d0841400d429501c2100700c00042075850f24601513000140d10307018080d1034503250f201c4107030924514140300400020402400701e42000d0b2402d641002c0c940211416a00142c1164402c001c149489900c0305280c0c06500b100396903103000041e41c036200110500c11540d0140c41080402075044044000e0405a0015603082c41520042c180310740308405c0940d08900175594039141c4108501d05282595400b0080d40f041250600d08140b5210f114080c0e440749881c00d00300141d0314222009445000c00390070700c020354030807190000c00c041c0d9400440154801c000c101d4400100041245002c418040d1601884c000210407001c00c2c4503c2d8003902200c2c11050591404003c496070b80c0e4640e070b2600c10b07503500201c1481d844a101800d90202400361980025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 779708758 1250 779707508 779707517
    0x1208030a0b0a0b220306020301081e0106030f022724040c020709091506080d020706140d0509030d09080910021b2b12080114130b06220312 61
    0x5103070903003003540c074054059400d41020070721400e881044c2e106000c5100856219000755103d40e503405400d40c56164200001c0400503810088944284040c880c410503280e001020391420140b503004c0c029440c001000c00c1403800c00c240d120800c204001c3d20f00d85e200c1d031224440e00d10301c2001000c00140c0000d4400280e8080c41c200300d47e00344040d4011800105a8018050000b92036071582054036282c42c05101c98000315107048000301c0c0e180004100300548840360703001c071384030b2540e1450704454601103800c5004882c1000e00c82030a151071070307802c0127400060220880307090002c01c2044100b200c800c18001c607110000000c10f031400b801d10020070703202c901c15400988a941d00030b491003048950490081c5d440360003111130386464001c10300d500c02078100da42055070245004d1898041101482e140000012490b99000000c0066500180e0200e8000c0074004600c800d03010304035038026029154900b90f00500030301c5884001c01d0450350501103c0c0740c020040c100540f85007003884c1c050a41c00451000c10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 779710008 1250 779708758 779708779
    0x4905060f030f070e0603070b0319110705030301060302090402190c03090906051c020312120f01050a12020f01030617032505150a060504090501050f0c0309071208041208030a0b 77
    0x8400c042800801c84014130345601107542c500c03002074100b80182e00000900072003c024007164030f40c440915050b07917198442c200043c4854180604860081040007009075004000502085100e03802070120810050300141c18a0250860b80110301114a140c000140162070140c080c15880000c9600515401d4400c00c0000e043c60003240290b40e222a03241c140c1c4078500c0c03038607013152410800200c0c401c0000e40d0b00743d00e403006e00380302011503030040d14414840014000045a189003154550046500944400c0303000e01d80390f03003800744003494596070505241c1d4440d0009004240c07200d0800e452020072018646d903900884501c0c502001c0419440d90940e0412110000034000060b148038070313200f1403120002c503038403064000c01910950308203a410074203102c007190401030150080c502a40f503e00001d001903541069201040c007044898a481780d20400300cc0042d40c503016204240c0034000d8051a10342501d035160841c25554120049412650002c10866104440c0c4a004003e450807221200c18 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 779711258 1250 779710008 779710033
    0x5010b090f070c0b1b04061815081807050a06270803070b0a0b06040b0c0c0f010e060c0a080a090f0803030c03010608070c0501060905060f01054905060f03 68
    0x60070006008915040100f500105440c00c0782100e040e110702c00e1a5a0340d1603600003840800189592402c0c2c0134542c201040e949e901729807407182070300740380c2d00c074040d0345d44920480c3c00841c5001110002e6010300000880c0035220540040c2c00b81c000c0e600c0b1070301000c40c10080f50704074a120140b2803001421403281131042230004421240d80744d41010340c03503e541e116602204024556115400d07072282d0001800070b000034980001d02241717001002520b4850003070806024108601c1c2c0c1107213000a0200403c10410319100c0301500b035101a14044807403401e4165110802d0b9400401d803d0085840000c0800090500350142e00207000030502071410341c02c100c12605028001800382d141131141d0040020342036031088043c50100c5801c074009020b02562840000018082558070a002d044100384030702241d40140200d60007800000540803001c844490101480e05885c4e001c2c803864a5030b0050f100702c401944000c0c14244400600c000360300c1c1014406c01c80b4140f1000101c5009800050101c4035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 779712508 1250 779711258 779711267
    0xd0203060402101b0b010518090606132d050108030406120504060929010503031c0209040b0a0e0f01150516031214090c010504051309020d0c0305010b090f07 69
    0x4000794180d0b40c0700c203042d06030346040d65814142140341c41340c5a5100b9407a02813214400da103038100e402c207035241c200705240d82e64491551042150031004582c05200814a86d0038100c1103c4491a082000024509801180d141405840c0c5030040d0030081700302030303500e10100b49204d1140108155030056260901c2d00e000a0802d141105803154290b56500000c1c00313004a030342041a190f0340c82241107c0e12920f4020599000246609170861203075080008142030070700004680311120a00082003080540e0040078020754015080290401c3e00e904080c4110740b502c146000150007020462685d500e030400894641020590022018000c40181c0c100f0079030b0040100c8042d80061414511070425038181503d680444002c4440c88a181c54001d081072900c0e44c09032400307000044255250101c8031401195240624050310b90b1160701942c078a44107503055401840c1c85480981f20b80301000c42c6031950318020610f135200307980b165140c15024100e031800400041d4042c03c540d031800c0403810020320040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 779713758 1250 779712508 779712511
    0xc05010c1112090a0510021b090705040302091b160524010b090102010e160608060f150d200301090b0d0506130201030905160812040e131505040302011a0d020306 71
    0x840030380b0000f42909050320b43c801940301905d8050a004017110754204020340d1054506560a004210110301e5101c52800d030036581d0003065507580b000e043c40d0464080140d1842c0c083c000700400300c403040c00382030191003140c060b2034103620061074075050b030440303042590402e807001e80314000c90841c445804203003822400d140b41c10340d030b0007030001510380481c500141d00620034000b20032640d100d95106420003100c29408007040c2c2d54280c0e9003140b680c980e10140581c00c00c4039940c0e20b0740101d0a000c403a40c2c074500800a88000f0f0044d810105480b614030b084020310810000049540040000051010000d5030065001903442592030400b074000b10340346d16450f04070290800d0f0004074000007650a41e80300fa042204605d40007000d54254108515004095240c90b20820446000b400980558081c1c17900640303045401c0541491082c3d0b580c1d440009062162141c100e42c10043e4500403403840300ba82c45628842d0340710b6000055070541d80b2018080c20980100614881d0801c00650030068030b000c601103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 779715008 1250 779713758 779713783
    0x915030605060d0e0f060a0e010b0102010b0303161a0108060a06050f0d020103020903030409050a020c0105070c03020307020d08040e04060b090916091d060f01030201030f0504021c02010513060c05010c11 89
    0x103080c916641c02d150400c0c1d14000c010b003086c8580014001410015800303403010b42204002000501c001c080160b00344c03140801c600350325801c01e2007409010081800c02d00012131007002c121100c0350b0840203103007580c007080e008405564011410014000028820840074000480d2080c102405920000d01800100c040090405802281e001001e85040040d14050b210300c3e4018089443d0202d50f08000f504500d18152107503007044082030034513000b140200103064155020354a410615024000c0c020a0300c0e00460340741001f04000261b0002110042d4042c0e0320803c030215002e5049410007600a0000d008510b0907000030541410800100001c42d045a910040c042160300b80d00711040720600108540c10014010f8208004000c03000c400d049050328801d0b2004c0010300b0b22307000101e044685c100c1e8001d420039032174080000407540f4000b03220005441498903a1801c074018a64020700203070f5500c1907000c0742801a082e401c01c030083c01590320f001e020b031500003071854400400d25600c1c90000890b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 779716258 1250 779715008 779715011
    0x1b06040b0f0a0908161b0909060f0903080c09010c02041e0b10172208070c1d04030522120b09030708030612101517012d0b0d030915030605060d 63
    0x84100200c41c06d403241c0404803c2504d07404581d80f1740b000000740c0016001295070303602e004184060211207103e0b0100d00c030b400d90f55030b0310300d42d6842d00c0078041c540c80f8102ca94148810a2210401640e841c002c500140302000d07a141820b0f44018003400c04d4401c5c0268242c0301c0c0100200100795036610940840b000c0700f1810280781c0c580c179800101800c0d004003c509800b0b0307014000c0030109119030b134002020383c984518082d8485640e903003500d111350300c5e281a0a144810f14032000c00d0200c1c0c4a240600054803100900f8035120034800300402c400540c941c42400d692030840740480500c220698026031007000e50380a146082c0c0c10f40e596103840c0c48001c1c983d910401e034004100d2005003013003100e0544000801c60800142d42c031001308041c0c08071a480340341e03840c0c0040d1203201d6042c0c2043c0640581481480d09071100742d20384000c9091444940c01000d07403400c1d42d800c14040a48c1d2749503d000d906c50700a848480015013484244100c1580b8401a14281410108100f1094442004485c11685080c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 779717508 1250 779716258 779716297
    0xc03030b030f01020403050709060b0414031e0705030c030f100905190c050f04021206010e042c0606010207030308040f21121a03030706021b06040b0f0a0908 69
    0x1026001800210340d8603400d071003140154642080158003e00a99000d242124001035850720f008094916900540100640621041200c010f01c0541c03003405803001029580805c2c00d6085035035200621601d40c03c641d92010004100505040c80403a848107000d5018044c0321041c8120941e0301c04e050590107188680d00c6419006205040c0602e001305040f2811030100310040c0d040c40b200024090003103900c1844022180713840c0c0d1506100700c44140400e000b84500035500ea80c015220180210500c9804c2a107031900d0420820120043d08030700059540d109062080c42c0600743e1800c035005000341c0c1035511512050010980061040e54045d5101c034000c40030280e40d150422049100c030b050505240742260540141c186c100842c6243d10041040811118015020f0002911409401180c16400400000c008680142c004003c2502c0c2c804c2800f58100410381e50318a8034608680c180d910840b100203000c0044102c40c010703600300291070300038801840c258941c0f45491103814045500d810030201c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 779718758 1250 779717508 779717513
    0x20d0503041512050f0f0411041d0a0606170a08090118170607140406180f06090611071406071412040306150f0b070302010209151b15070c 61
    0x8100e40c05400e510302981d10060b14620050030740d4508007140c050440c1440700146501e034000b081c00781714a140940d040c1d207507107031601c131407500c6030b0301d22661340c1c005440c1c040ca071000405000042050b084104000e02c8035807a030f810001e007124555001169038560300e51340701802c0e1100041026039590000f44103903440752a40c0058401240d1450701d01c8176110800000108500d001134400d03c050ba002c0280c1c1e5107580c50704005c0b1001e40c500e01951003080b900340300c14852207205104c110809056032003040319083d124800d50103000159032003040058400202401050360080b0140c2e000b40690004080d0582800780240c104c81c1c0e441c000b80d006940c040340403414040c4089144141c03428200644a43c07510103080894254040d000942c0e0050620020480032003020300ea00d81110288542960420b04108460000d03510000c0c0903000c541d0240140300c0d5507554100c19050400401e10034a03520080d9003100410700340c4031404001d030303030f0000b05104861600701b16510b64410203030701e001c010b8a09a407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 779720008 1250 779718758 779718763
    0xa0813020d0602030604050a0b0918150f07140a140d0219031b09080c060705120a020307020a0806162312041a1317040509071e0504030807020d05 64
    0x2680040e5209441407000d40911aa03075000754020350042c0c40c148040d64403072031000d0540e1010800107801c819424009996443c0c0d50a00703802503c034080c2500d11a940410090300250001d0740d01c0b000c42c0c00b0031000c4c03000590308100e8030403800712040107407402e2000a51000e80440c0d404940c9101c4ca660000f10b2400a401d217a046424400303010850410124001000800030003901820b2020341d400317a208804080d000f00d8000048a0080004094040c05002801207940080324111041c0c07050340034000000c01902e018141c9102c10703600070354a82d403c41c01000100403e03640140e40541059040c00160034050000c055104c06d00c3c1401c0446030840a8450441c1c0c0c51500e0000d600030700428442c402c8030010094a000b5170040c21a030cc80301212820130300c0702590030750300388030310030b54008181000a074440c500040582d20b01d500207041903a100c01140000b00b041301c1000c005500015005011a0f4a09002d501f0025500e012820b19003180c2d1040c5c010321400300064860a6461114003c20604 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 779721258 1250 779720008 779720041
    0x81206121c200d03050a020f071e05070801150f180507020c04180614060102060103142a09011e1e080703081b0c090a0f06031b0e0c070201050a08 64
    0x10b03001003600c03180d000c1480e201c01a0320107441c0001d01305030208482c103800d40291802010300a50052400680d5514400c03d40014011290184103444103030300820380038000030004043d074000103d403100711000c002c0441c034801c0d046001400c103048401d2050092844540e481401c400b103000500e074403488010b0740b0700360b02d0100c025449800c00107001c0020082c52001c80d906841784100340305007402000100075507a004ca401c180141d01110042000c0380110350180c1030b5180d80000e45030600c002c240300b0004845500b03424100740a412200881d581845201d160050540812001181c0f40070400c0e1190740c0f400703105072604d810076152841d400400444e00b810041c2200c1d01202d000e95500d1402d10141e4011201c0c0340cbe14458010755424801c1b00100d1240182e00d401050b032000390765040101b03002000d082c500c1d4980b642d0b8400380440080c10503a010f001024021803c0c00100c0d20b000c0038448100c400404c0250707402024010500140d07000740603948d01d6041810294010355a91500c008c12110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 779722508 1250 779721258 779721287
    0x606030c0e0f0a03170d050105040603050d0804060605040c090305062520010e070503120310090e0102071208090d0e1302071e0309090b100c02091b07081206121c 71
    0xc05d000135107618020100140f0221030360403010700083ea0380358104411148203102c00340c1035802200301c01e506a4812990940e10600c280d200044503926900810100c441052409000c640850020310030700008000241c2d114495000384070a200071650a20b402242c2404540140040084406a101111184611480d0031440200428002c0b54031856848a651003602c0c024000c007142010048440e50440740716450803419210001d1402c00604024000071040c50402c1d5401c5c40440002000d0b01d65540340b0340d81e83d5448152500f0030381300c00340c207061054a0000a000d5400504886a1642c10025984048140c00140c540480341081c4802800c1c1c80009103d402594075000100340d000900c40b0152814188100f14807009d04081c0800342c8441303c0b14102243c145ca000100620740007601c19844031903055070503083c05c000746114007142c00c00380003240d6800c1d001c10322403c01144050000e0307010f4011202005c10922207aa134944412240780e8900842d511844030340601801039100400514 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 779723758 1250 779722508 779722523
    0x402090409050a170a0f0c021f0305060a08010b18060a1502032113260706091101080106080c0d060b0a050a0806010908031209101e0606030c0e0f0a03 66
    0x444a140c059120a109441103880a401103051040118418245e070481c00351522171070030480c103006c0140d071208a000f008903030084100c2e00b0440f941240b6009100c528802d92008038090412404218400100343c029900701d03072405446200654840c14400010121b5802d4481140c40e1880403a918440d02e4100b01c00c00c03526818a003211540c000002d144c2840c8407800300303444001c2c0c2003130b04400d034409035211007100b43c01c20100380201d40c0d022014551046a030b0798040810350040700ea0900c1e60030000081c1c0e00b9a6860400e03500b4411100460b90008200346060040c0390304048001d050000c0242000c0715660000c5941c210280c1e481d4400805001e40c5448983c5414600c04000d00365441040010002407041d00441e18950044210205982c1864065400c18a441000319444080103040d413080d84500c48022608440314440d20401c4004401a44040c85002a45c0c4041d01d83c194043d01c00c044c0b80c688040c07100c3e5803000790b03224406012980ea0500080c040f00017210300809420141031721 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 779725008 1250 779723758 779723771
    0x3090d021909230c0306010f080601021005180c030102030609040b0c07060f0209040b3c040608010b09130c030209061f05040807080703020918030c010e011e15050103020904020904 79
    0x2030420150f140543e0040309182200d50303544580b02e0032140000c2d1203040c0411840060380b001640126a000d502003010301c11203070b481c1d035180414410346106681640036001341854010f180e14092100384414401600254a035082400216071000d9000304050b11107160040465150300780141210440b5802c000240005031040b4252402580f0071200144a64640300750510241080308180e6010203c030841c01c004a8191038418400d104181e1100c00d403d1036043c0403c070655103d204110141ca40000002481030f0544140018008080e00101c00100c020340100000b6071515055419a903045d940220f90380c5030200805c15014000503c10400300d401e80c10031040b2a40500030b00101c40380d080031503a61079070341c41806448180ca0302020750480740b81c5000454140c4440301c03140315802c0d844112031402082d440480c0c2164131a00c0603403c0b07a51187c0c15141c00201d0021110031915904008000c00300c04034400905041451088a041c5500401c0c0c00816680ea68181c0700050380c040c2003480340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 779726258 1250 779725008 779725031
    0x30403050a050304050405060301050402010e010e01020307060509070602060711030304030c0309121a072109110604060203070c0b030910050a0b130b09130c0614270a0803090d021909 80
    0x43e6001801114007843c41c0900180e40c0c0d02d01409210301864040e103c20108804410045030407110004003181544410007403040011114895140f080030414050104242040c0c4001e041c40340c040c2c581020441182c0101d40050408011a60441e5060910b49040c080b20326003030754407001c60762040a01c034103111415414460802b583c0300140e41080c091445d240d0313503600243c41c41c0f00071003403901c0b100300a42d0b010001041b50b64008114203014002c400c900786188000a141a441900a407006070004902e40040042104c0c1c20005009a01c61700d500f1403038404415941d41d100c0d06180d1491710388034008120588056802910703040800b03131003084241c60818054001d045808243d0707001c3c0f40100e000680e070201108046000990000280743c1c046e16121303089491803003956451100c02020046454010708596413038038803245400c0310803103c50104040042d02070940c0d1000a02da041001205036a40e40c2245031b8620726411034600408089644c2035001c203013455000302041c3c91401c4043c407903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 779727508 1250 779726258 779726263
    0xc0307200d0909050c0f070f050106031b0504060e06010305152701140a031b050303070f030e03151609030204020a0302040f0f0506030c070624150908060c0309030403050a05 76
    0x3000e2207961540c0040e9a41c54640000b00ea03021a10b140300c40c007042c00400c1d1440651030040c520030b8007036024805210380c2522880e003110710f554000c40d02d02000d09400c0c104051005804401031504640030481c4030700e0007003c8280484003d2240303040541d102c0010356501c03c03045603050103500152064005181409503800c980940090310503203180c102d000055140310000c442c1d0788415001e05000c40c850320f10340d00c6072500d08101c2181d06441610210128198500f0400342003040c0c0911040340f039544041c2805080c807008180b2680c06a00410f00f42c0c541c07403041148541d00f05200e554444000790300100c0c100ea07509460b81000b981b050002401c4030585501d074020f80300b581c442072440070101d03a807002c1c0b4903921906445200e401110610010741d581c0c405601a0841a01500001c50202690910000340010a1001003113034003e6603070604c0286030a1b80441e141038502d013403240640e410030705403c0c4c0da03e0000304081210100040081e84001c0c082c4244c40096a000c0110740c1880700b14a041034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 779728758 1250 779727508 779727523
    0x105100501110313032910031a06010c02271806060319060b010c0219080f0d0206040f020d0b09030301060f0c02060a03050606091003051902120c030720 67
    0x41c0065441140c422020902004542030728400b8100203200c0c0c0c1c519a5131301c007a0307000da1800010601c0c0c04207600d0911506201498030030441c641c48500c24a043d4904a20003103032200c11035414004400c104100d69802c4016014500c2e0111042d0551040b01c40e00f80030313501541c40055088646c0f10f0244511002c202a0700440d481084003620b1440d610881810755548444001310312503c0203110800109038240e00c85106502c041c1340005d030040c0b0759004201e0100004c078400019901f21402003003040414804500d1700030a00010308045258180c00940da00380c00f40001e0180601000503d0455444110300404541e00406400d20b07450140481901c2c0e400c01d10441006c40c44010340c03007a01521a03141d00c50580e50041040d8201101d100b01100103200040c051a0420020003012485598141e012400410a46e034007240f14505a40605818a1040c0c00380509030700503c107002303152010001a0380c2c40741d07034100c500f80c0b84c5e500e0301d4003103404500c21848100000c41d00d071490322040c0030116608 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 779730008 1250 779728758 779728769
    0x3150603111203160b06031c0f080a1401080318010513090b030c03190c0b0306130506040f0e0d020115030b04030c0516033008010b0c0a080d050601090902070b010504020c0f010510 79
    0x8039881300c0300b42c1c41c420160b000c034002c070308c000750001c51304009103409030746a80d400010102d40081c0d0002c0c040500b0a046900781c0103020554000300d6102e55454042030180101c0b0400c1c41d00ca42407042042841a000e0103d019800c0304a40b81c1c01da109503a02c04001d00296410000c0c1220500c04c5200240c0500d0340c440c00e03007600c42c1c0404000110740141c044007160302414010b040160181d58072003503880103200240c00c941c0d1140d20350040040e800d425009411094403403d01a06845900c1c080107802c60300090180c586e0000c9c040d40070030110b00040445544203030581007443c0021031503c1d2087c14156404041480320b40c4c0c0100100c2486480748600415a41d40589a4815000d042c0c0145c04807454240320b00001d4004c1d8014032000b030550001d001450401c10844005405a03981c00308184c0010071a904401c0e507070b404102496030300c04055001412030a00462030718400d6124012190014001c00f8081c640000f400c1850220400468010742d000c94020011410040e160398070213142e03032043e03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 779731258 1250 779730008 779730013
    0xd1d060106020a0515071106040503180108010312030c0203130905151804031b02131b1403070c02010c02040e0105070206161b020a0b03010e0103150603111203160b0603 74
    0x101c0c00a00010702442159040030041c490020311074594410a10020002400c000d5103d6030032075141d500700030712400b65129401454880d21340300700313030a1103071100d00c2624100850500102b002c107919208a545c1a1098038011411103010901640b841c0f00d00751440141c1102c9940019a424139588110701400844041d40c10001d10035040100c107240030014030700458424000304002238054201144003018a10340501c00b07207110b0b00090504448102510700c1c2c25114403120805034401c074403408011030039050031031a4070400e04e100038050000400b10403d000010320580d081da030141e600040c0ca90b50050045c000f00c0040e0740801d0283c00c058032040098401c2d003002c11001f9106046401d01a01130307a4481041400780c024400142102b82010398101e040c0803800310b5900301c080000c1d80130b40f01c41543c2143e02e500d94508030465513480005010614648901840081c1445480d030014180c2254507100c80280d0103e0702e4114400c3e10044080f110780c0c05911070400040c0311f03200c0c0c811a0101c05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 779732508 1250 779731258 779731261
    0x504050c0a1d0112090b0603010c140d020a05040b0a1701240509060f12040c081f0b031e150108010603030503010b0f040e0c2d18060d1d06 61
    0x4031038059000314140300c004079004424154021503600941c105030300c0d051522550342d40300c1c000c0501c1203c40781c2078161342c0c0c500e0303000801189040901030a10810740ca494124200c054900314080c95000f003040d081d1040343c00256203c0014803840603036019000f445440e0b40d1300d04207014003034601c542041c3c0109010140200000301c0e00f24220b503110230389285000c950301c4403980c800c044400ba0300000c005039000c1d20a104581d001810040a8011402e016061070618240b43c00c195281c2c04650788088401d0303022810007168401c40d04911040111111000b10b4143c04100001e0b0034110900b401d81c050002901080111410004001a4596000c0098480f0782d8841500c43d00380c81075400041c0200b4801c1004001c403030400c100400405400800750b40c100740e01d40050700030440c4241d80c00082850046840c400700903040300310b000e8203c414202040010441240500140207000b00d0b14000c90742a40c119074182c13078150803034202a24401d4100103940e0340c01c48100031407800700040d40d00740c0718140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 779733758 1250 779732508 779732521
    0x16020604050c060f22030512090f0108042406051c050706050702060f04060f0305060607030c23030d15120c12020a030209070c02040e0c091b0f070c050405 68
    0x2891401103802801419002c20b003001444240d0b40036002c086080c1e04200440a0510182d407070888805a01d6a00025050310707604100b481c0c0110030144c0e52180c00100300304840c03541c500070880c00c41c02d002e0901681c00c0d036071428244070005603540705446140c03902601001d00c8034545d0000302515012217841044440ba540c1c581d01c41c124034040117141d0b902c4070a0500c443d0707000780041e000e200d1000b002c192900c000f09100c0d003d143c000754004804900d4529015580b16058000d1507403008050761420308100e42a107000304000000380018014042019010800d482c0c015003110707080c405a01125541c0c2010413009009151002450005225031a00802d00d00018100003030804e411a0046c8c004500380311a40518800c0307144120307445041200d001005803500500ca61140314640ca62104036501c500500c020740c1c41844140025130807041841c401030351010740c51038100889001da2a40c1e01d1600311040e5644c030803494140d104220100784941009442c0d0300e0f1100f034400950302130003191940c0c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 779735008 1250 779733758 779733763
    0x30603030f02070501090b0c0307080403050a1e02060d0b040e0d08040209090a030f080c19051e0408070308030603160f080106150f1d040c030e150402031c09080303010e1602 76
    0x240504c0740014200a4104030f80303c5030340d010f03002445480341685d00c4c0030b0240c0c0c3e803101035038090b620450f010340040c203c000c20300c060744c0c40c81000f0002e1a4180c1c403445c2c5240d80054218805c042000103d255510842c040c151903941c403565040d0504c104030f07906260f070018040d20f0725000303c8080744a0150500001c2c0c040201194152200f42d2540340c0181040781540c0540e9081d0b0005e00c080c900400c1488840300c14049901051195003a0b074660b56076400c3c804042002c852410b44004040400400c420429050000303190300c12203400c4045580c0b03a4562000190a01c0c4d80c101d482c0303102c04003411012540d0b905011341142110707100e4000b0001c0595400401c10401200181000411170040504614500030403070b000d41e07513540304250320100c40d4450005080b200f128501500007903541c00c204c034501c002006160003012881c0f0340c41026141c15070000b40e45d12000340144d04450702c42460101001d0141070308038050103225003501d0b100e40e1510500903102c03d00300c8500c0d100c005165082e10006001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 779736258 1250 779735008 779735023
    0x9010209060403030f0c02031509210f0d1503060e0d0f02070605030405010f060e06030d1b0809150a020109020a1e050402031801020403080702040c02030a09150519030603030f02 78
    0x68491410300f4590740b801d1341c004503e40d41050505c8504c1d5500030040c0d805004120650b0170902c503540c0c003410038204a03403614119203065801c0014040302c960a5081180682d1750f110200440c0c2030340c40f074480c41c60402a02021a0403014591548008400c0251039000108010014000c882804e00910805c5a035004152a080003603000814280904c5d8404d000a5030b03c180074100100b034007144035118504580da26840f800c62008080d0030312407946424801243c43e61050703e0141000c840205142c0082d031481c40008100450004480c50303640c840140c0000501803050704561100d02c131000203400b801460304102d1041d0840040421000c2c200c4d08418441c0340190b11066a8500300010b00c002940043c00216245074100d58411146c182400104051882a100716448a4142c41448281c90030281030b10155003080c49802d0b039007640b210840007252520685200e1150141c601039681d80b041550051545415645d0b4002454054102c1011a44266500300818be0103000172a240c1c1003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 779737508 1250 779736258 779736277
    0x11710050f0f06030a050402030c04200a021603050606010e040e060f0903090d051015121101091a1309050c1815070c0f0902040b0712170109020c06090102 68
    0x4249600344841d04010800c4244008040c222071605944030000482a810444408040c55101d9040004500301802900d40c4000c084e5814003011300088015000300e001c82260074080440031881c10400340c2b00700f204460300b000e1070480c880d03c0b80c0c40c0c0c1402c0340c0fa00300c2240c0541c081484c480c1040d02c0390510344078800010500c000589034135100c1200c009441d07000900590703268030080c000b000443d41e078046040049480340b001010202021204c40060354445010f80c5c0c06d80d600c441d41000704c101c8140045c000b0395808075400c041c1000580059072211155040a1416540600507400c40302040d4002c1c0041400303001000051a42d4441e4142a00c600b11003011038090244072003210110030301105607050034021711007004600c1003030501400d900980400d0311100c2d041a420098043d5546641e0040c0c00d10100540c542820088026100d1041d00001002004283c1c000d001c043c1c403890a4500460b04411022035550b075641e001c0020350010000f82880f4002d10001c628060300501c226821000b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 779738758 1250 779737508 779737531
    0x90f011d1906020d1416021908100b090f07120204150e2103090f03010f0509011b030c02070e070e03100b040b0612060d0206041e060807113c06060117 66
    0x1000c070b2040d8180c0d1b144458003240c2204542110690510010007070001402052005225100e25000b4540540d1000d8081e503014104e20380c1030000440f00d0112140c2d1282035810280c07456011042ea41e00284116440340340c1e01d060b804a01504140e01c1454491300d04400c46582c403141c2c58200d12400b03072041e107134a407070719542c0b00304013400e014100307a8088204d1103c01400041c40100c0280c21109803482125030b00a01d0b5591800b80710311200303a8007003901000f030514040004102841001e90359031b050380601d0b00700c01c0a031000514428440c007140b4440302d002505568840d00c0351581100a441c003608500d101e41d09080c030352202c0d41030807801d07241522448992813600c0e031151010700c040f201e4520f4084c7d0b0000803c000c0070501c040c1011000203800c00029022511601e000d400400003c4094000360030008036460300c484a41d4001036074140822042d80034017000c90645050002c4180f500d801441c06c0f405007003d0131200c500450200d114050a1702c800368450801840c102060000711000d89030300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 779740008 1250 779738758 779738767
    0x201091505190b01030204030203240c040b120a02041502151b03061002032a070506030105010f0e03070512150702160905071403040f060b030102090f011d1906020d14 73
    0x2d0440740c002141814041c1001407070180c49402003401e01200f0983c2c1c44010f5103042e2900c000c14a21003a503a8007041c0003a1460030203050081a90700d600c00c102001c2030381002c40020a1060310345038100c4004100101c40c440141455180c081c0d180e50f411185508010035500c0000c00743d81d0b4a4101c0d03c1841000010140f4540d103880401a1050490b14400c0440c4002e00400b0482d050030103100c0f0203510b164a00e01101c4d542c0400c800e1030702d002034100b5400b4076030503c010801a41c02c02c503440846001414003200c1407075401c0c0400c0c81c0150591010b58800c0a140003000d51038000300d00260801c011641c0031480b0f5480d80030590781d072505c0c494000d4214594840400030b0206550189411841901d040c54105441200317040c0725801c280c03000d43e52915603070b200c8010010b0074443c105244405800950414203803400188620b54042000e5061001080300303d00b6064592001c080c100e4001807103214005100052482e000c10280038280261142c1a9180b030740a000b1172010442c164247c0c0340e503140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 779741258 1250 779740008 779740051
    0xf150f0303230307050c0f0c010504031104110a0f1107050a150e031b040506010207180b060418090311030405130f0f0e031903140604090218070201091505 68
    0x2a800c280340b90940881010004014400c00c00c0150701401e159640e0035200c07402d0614140c10400c1804410b4000c0c4d04c00588822240d070418242c500f1271760401544040c0b1020903002c10003a0180c1d104d442c1203c0c0002036900b1089811581050b04526940c0c3e80f8030a100310070242c695151700c1e50142951040042c4800c11404120800003002c1e0301d01407030075000c99910500400e1a004030b14103240c00041c8040c0480307100d42004e11903594000000d10040c80080d00c2d00c14005191100b0400508240c0e40b505100101a02c1d00b000301c40040060802e800191540000014000d0145800450004095000d807101440000055409454004004900c0351070b940803000d0040c6070038003080381104d85400310360b0304100c614400d40c1d03450814400a1a5203650701c001a5580030a1740000609140c0b50001501c048480b49040b40c0d03000f9015074000590554a0001508202d46250002802c900071000c00075915810740240303031134910840050181441c104a100141e0740c0496065500104020340c0d01d08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 779742508 1250 779741258 779741267
    0xe010b070212100e0309090a020a0e210a0b0406141b2b090302061f03143301050f100e0f030a03231908060a09050a0f150f0303 56
    0x28444810302150f1042c4222074030ba00030794554581440040e040440c21001a040207038110380d20200365442185010944034005c1c1002c2c2c0070105950027074000311404c0d07021440c6881a80381510b9070b030b0115205040036181c0442c024000302c5003140c11a040c8681980072066041e400d40c0150300c8000c2c00040902d00100402072a042035124000296100c01c4407000c140d04e4200120014141580c04035a214550502a2900a010380380d40072040700105d400d000709c0d0b0520041e003303a80d44020b43c6c0901c0314003800060b01e80311103000070b641406816803403a214010541000302e003400c442a450140340c1e07640c504000f004e0481403605504031809450750480c85115010104c10302d44000c1c48030407010b100c0c2c0e000c28a0844044001c4000c500711400e01030850a01c890681403010b22034001500d08085800742e03c00c5084855500014890010042580da50300c0020343e0707002d88042c0208120500d0f010350110082d0601981556800e443c0c002c2ca9141c0a026070754140560300001124000d01e490740c6c0d403c59 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 779743758 1250 779742508 779742529
    0x6050f21030d0504080702100827070e0c0a0e01020c0a140a080f0709050f2a0702040c03051608060a060f0314010e01030512030919050a020312130e010b0702 69
    0x25103a01040104806820381c5200e9640264001c0c01038940b00d460390300c148a402c0056451034003c8c000c0f104200a40e1082d92109001030300742901c40b11066079900c45502d86000c0054101141c1c45222400700b00045030000050a14210196219034a03541104016a1210200410b0903000350031b1410902c15051064201e03100144080c1124400715600c6500d2400e280915810703a070990403034001040703010241d000742500040b410a02c0f00481c140b0100da540e2142811916a9042d00c24403d20003242308100c0036941e178150060400e11900d600080003c008180c129800329400d4450754400f600c0a01c11004241f0401000d8100380a641c10401d060360740070702501d031000c1050707255a620707202c2c45803081a540c0203113961542012954114544541011119075410000300c0d800d0003008038400300000c0480c0e103490011030400001806081181c180700c420074000e90140301d442c5149500035528801840c00e0500780c1d10800b441ea0f2641030010350504284224942c03000c003407120101603d001100c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 779745008 1250 779743758 779743819
    0x7140f10020309031020181009030c060c0308070e030a11060702060f0c0c030a150c090503010e0610080a0506042d11010810032310061806050f 63
    0x4a0420030100006445c00c0106030700c2031178007500c407028a84000c80c0072040c0c1400d821421151820511400c00c9803d08070380d08081c1500c10380104030485050790092000c800a960016101906151910303000303400e4010700c140450004050200044035a0b10071038100340c145800501a1021000a8031110101060400c003203500c40420003040f8016079440c0c0c002c21400b0b958a14541c1c07505c2c500c0b5005030500d400e628000d4083c1d0441a1204d0009038000d25402c0e00b410803c1e00001c41c1a01000d00310759550031504001d40540c80e240500c4004940001e81034030071842c00542c5428181c403020f406845200c135003001050b50784980c0100d40010024061054180541551200e10360072144060701c1000c1041e500340c030003009402543c1d541e035178416405640120745c409504003140ca0343da02c4022003034100c5100000b00c0e204036000c0c0306a0350140700481d184000098284400358480c2445c040050041c0140b001207450710000281c80d04100c42d074840000ca00074040c3c1d0103d020350138014045812094035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 779746258 1250 779745008 779745013
    0x709150c05010b0d0c0504240e090118060911031903270303050a02011a0906040504060906050703061806060905060d0f09030c03080a060b0405040f06090c02030c07140f1002 76
    0x42c80302d6071500e40e9131039600390140c2000b00701285880b051200310f0701441e04210b990f0f031010090b00a000941000070003242ca90890500326a034079003080c40d0051000842000318226260fa40c50b080c408140c202044d030324040c0c034803500e4480030300c01007642e20558148010b40e20b0640607090408070380500c110003040c152035035006c90440c074052840d035200d0f00c0542048003c240082405c000c0c04e0341c2441071195a040401101840103040c000080422100401c0c3c0c07442036840e4000a802c2104030340201d10005c4d4480424041800d0502c409000b03421320f40aa401804564110090125414042c8501319080e0b87c41b4514500c1c10a0141f00142c1d1004004199590301c1c0c00f8410100401840344100c1c2d2030290b81c8510210000717141c01000720b50040c1c400c8580078100003091191f5401042100c00b103030821a000503104602c00c405602074595540002241c6160030b003503584840d0084010700c06021400182c5522a171650000480301c1007001c0402c1e00080c010642c01c2e43c80c18000b0360b080c02190203004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 779747508 1250 779746258 779746271
    0x40903021c0503090601090c0e040b13050a020c0c0f09060405090f0d020304050907050c2a13050708090307050601060509010309081801030e070320150f0a080709150c0501 75
    0x40780c0c2240c6403452809000141d0000401480440038091140901002102840094000d1400078651918484003511030380e070742c0107242119a90a02054081c5604e84024800c038609001010000c3d08101d03401444c5009a0b1507040b114a0840140300d16814018815443c40d00d070342c03051000400c0c004002222510800f490101041410400246020610303401107a5031410003003401801540035007640280101800000070151011030106000c919a01440340c4003002001c01c5d00c50f54050f040c5403500401000240104c3c11443c0d0040743c0f00703410703a4882c002e494548031900d40d6030b0320a4110203842c6801003001800024800c400074040040c05140c040782160094860203803a43c00311520040c3c100c40c0000c0d007442075816001c1c0c0d0082c04422009010454038644801c02d050320301d100c1038000583c5138508110584d80c1c2c18008030601e03440341c841e140c503101450b040c06001c0e4440c420180104080800061415103d0354003d42560140450301c09160580d1405440e52003a24a0850b5155210013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 779748758 1250 779747508 779747533
    0xf0d1407060e1006050a05010c02100f05090604030303021e03041e1a011410020d0210021b0106060216080c010906320d0e12191211030618040b0604090302 68
    0x71070703d40381c1c0c00126400940e6511380070400401c0641d95101a0600118240c1480075a0740d444a4030310a00f01810b001341d0903444200b00f10f81c1c900c640398900b6400440420084245941b5901900d04004680c0175035250340c00701d86254840313000455000f0030400e49107104800c3d01140c0b50440032280d100b03101104042c84000b0a102c203c140980103010828a0010154002e20b0420800b0507484070301d0000d00680010b0040c025101c03903034421620f01568002810031295551070000c0c0e00c01c1c3c658000200001620781c03030300940b64140c1120142000d007550901084910b00441d940780401030507190034404615060341a20203e06982c20381f10092908500c0c0000c20000340c01c10011158005149999042d8004c4004219940c2074481a000da000c80301222004040d1421100307103482c0702c0818603241d180c40c50210307409406000200100c0d41043d8a4605581c0b914000d540100350440d29210100c2c0a001c00802d9038404440161a80c108100400c060341400d9020883d5103000744150303840c40304000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 779750008 1250 779748758 779748763
    0x1109210c061602031b0a05040e0f03030c030702060114090a11070f0303020901020d030e07050603091c09090c03020306090c0f120f0a060f1a0a110f0f0f0d1407060e 72
    0x2c00c285420008403054001c514081c0030758400c021042100400c1003001d000406c4030f6000f14015a4081d596642c0c50841c0003004000e0011004840c00c00c0300d0f56440c041200706840d4005981e00c1c4094410b5130004a59290202d000580104000c0c5c4100680d5980078015005011035200420a2500800001001c1340b404010034030205c1c082d4402681d1800310000082c903103008250000101071400d58080701a4001207034000840304100ea51540342d07161b00c001541003a4140044101010003244c4004111303400c040d018080b0f400308002005000c504100540991208650075a401490303000094070341c522a030090900c6801d03440daa1410221010401001c000d0103582104401050f0400c111050306140141c2c00503000150340b46488901c0c00802d295074164000300d00c1000100424085c440c248580449002885804102d41010884020791602c0d580704060390810380c003500d4032040d24104006a5030010503010f03601e4413220700d02540030141c0c61300140c208480d030944a55a044040b03204 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 779751258 1250 779750008 779750017
    0x30c04050d0f110411030103060902150a17060a060e190b0d06050f0402040e131a16170712181b0e1617060d02030d09091109210c06 58
    0x1c094608800d060b509040b690b0961100c0c615209500b04851a1085003849051340d0440303a10030004140c04105c0e2001501100c2091208140c005002c1740850040f50312001408000e41c980040c2c000588842d418460109100d00900010400c203200990031420600d554419010301002d09180840c0c40360f0750084554041c50743c00d40c0d89174445005104a141a110074000c07420101c03821032910385803070048483c034000240005401000d85000001b030003507402c140200341c004d40000040510707040c5480e9034694a030790000000158142c1003a107009011a0b0864029480c607110042c107060075071144800341001010301a002c40d00200d01c4000514182404110350403401c0341c2c00809810002d081c00540d070018035066001800c0e01c0140302c45034000c444480883d851403201e8215a0305c510202d00780c02d1240034025018403844801da01c0555000c0300c01401d80d020440107100900c0140076060003401518401e17644450403030303071a0486110404021001d0394041080c0c440403d8a0400644240c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 779752508 1250 779751258 779751263
    0xc0507090b0112090507180605090c03010305300901050f1815070b010506160f110102010c030b090c0703090e01091a19150311160302060c07030203070305030c04050d 73
    0x4980e0101ca11641e008402500140040b4204008109842e240e4030b079928180c0c0b140c100050354008101050b918503070020009410b0240000314a82030203840c0c1c2200754024807099421b806807840e00300702c10b01c0d04116042d48541079445a00303160455000e0503d03e9111001c80d5060060420100180290740c00180c1455020360614075003261014050200b04144004004400e078400c03c40c680c0001e01e01c884050650b90b09446598540300c000340c40300640c04080c20003900e1003460203152004c11451180740392a50a0a900a11000781d50441c00c1c0c084c2c0f151496060340c0003010a00080300c6100000203415071500915100c40c0c06079a41c40c02c1e0744520340c2030700a000c9035502d4803d8500040546403035400d605400b17850301b00b000006070036082343d400c03814021380d0001c499141000614030300c02e4020344840c101c4c101d011036407000a0300c03560007408907001e0300300d0160160f400014080841d51080e10011a0140c024525122540e46c084484c1d900007000041c4820042c8804186600c0d4203035114135061 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 779753758 1250 779752508 779752511
    0x4050406061707030309260102070c1a12150301090b09030403020a15050d0b060f0412060506040e060411030715200708071a0405040212010f1a04150c050709 69
    0x508102e2000c1d025000e2a44996995001c01001c02c0001d03802007401d411a044110018001d8683d102843c8149400085c90b40300c0798004900700342440103130781c1c545e402c0750aa25224502a10a514419403a01520305601701800c0d841001074000aa0054010000603005000181442607a40c40e907001e24020b03180040c05a0021605100718100155400003a01d281441500c0991490b00020b080f4400d01200d9a421510381c941c803240384d02c1d482c00303403032481c14400d0030741d41c5858858110910400044400b542e102d41400301040340d60030b182c8502031000781d80070041d054698a1741c03a202e50901121748000d40500c9801d0001842000801e502c40d884078456503003032201000025143c01c1d103074610039001d5071a001004200321152000075100c0032106c042c054003018001d01048401140a5030748a1500903000049070448040c02e040d900f8141c0710103c0b0036007a00703500c1d80f1b4046810b1080c10120041c07008104024031940d0848120701c8000b01d01d52410715000322103642c86030b0420303415074442e40186 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 779755008 1250 779753758 779753771
    0x51507051507030c021c12291c020a030314040506030106050a0e01020c01120c03110c010209090903041d04021c1b050102120d050907030503070302070303030f0218100e04050406 78
    0x1903141c01040701651062000b003100182114204500c620f9100c1b040741031202c210800b142d80f583c0740d0410032070101407080c41c44007070901d002100a0403ea45403c0d61054102d07004007542201d0408034250040c0d0040c2c9011141419a601a20705c242650a880018030041c44005290340e03a070030007580a8102c5a4480d1384848560794007511604c2d0300282c0b5810364000342101820340e644000b040003c001c4c45d050210340707d04500c0d8254000c1180000c507600c80c00000410403803112054005003403c200948a00b000c1e941c0701c01080d502c1e4082c034024800301050195500201005119400e9001030005024100300452074803030040b400c40a55003221a610500039202c503e01003001c90000910003800036000c1b104580e04210340c144100900c1c943d07a01e0780c41020450540302080301c00050340d8081c003240e80d90042810080d554840a03c000c500107030034100350000f407800500036900148580c0b02c0e00720700c12104070104100d50540314148020460030746c01001c240d54403401000d000340c1c001c41c1c000440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 779756258 1250 779755008 779755021
    0x16050312010b0d0605040c12112a0d140405040b042304060c0f050319140a0e010c0509010c03080402030111042403090305030f0c1c0e010c030b0a0515070515 69
    0x42e61140e62041c1d108601d0502030307e400c5600a0200c6580c40200d034000a4043c4100703500e80302900502ca0382007050710311380109601502e492401c0d42d03c400c12110490b050103000c1c2008452100c4401e40c1901e0040090100b04040c0c202070708550240f0788001e00114450364855104600240451401580b034080d0605100510100b403098100081d040e01d0004c810b582d070b080003e050361001620000c0c414410604083c0406071aa0021140b04076080000450782070801420327020704099000548075504c3e02000b40802809001243c2a1002c1a142d0503503500c2c0e2a242500c214000401c00c2c0d03055520745050048100e5094002c101030030310a022002044158964020a880741c041d150741894074205411010a410000303403644000603455040560380d030310003000118050346122110616620f545080d00740c9043e0001490301001070000c03c0b40400c0a04c0880c2565840d40000f50010070802081c405420b083c8902255441010000c82c50221145d40c1c880c905800c401154a14610480a2119 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 779757508 1250 779756258 779756261
    0xa120309231f0e0f03070305030a080f06091905100905010b0a1106061503042a050316180c030b1f1b12030209030a05060907181116050312010b0d 64
    0x1c540403400c6100d4102040c0300c402070310202a0f821514428800d600c8200000d94081000f00041c2d81e012043c0c98481001040141603400160780a0f40d408101500281c0c041c03d110390130314030400c19080c4a01064801704880d00c01800082c141d662000003022001c202a4544c1c0110f90082c501b028005135075001581009100164101d1030442640103070f01030041c159603602e20b4000b03021031100c040b581c94503245803a8034100741404071240c0444c6444c10311515240c10a282c4001c443d030503402c0e514100000309000f070a0050724052206580440d01480c203400200340e00284183c4914100050850070000c001030303070210f071506604450b000c10b580c0d0009959201c2d5102c2102d00300b032407004140201039130341e000360f84900d290301108065020800c0e54007130794100680060250031005561003410300903040c1e9111604c5002d02180700c41c0404003404900000d00c0348501800400b10141c1c108000245210b950f000f1120082c0c0d860700c414800c407140c1c0c2c1c0103126078600070310780034255594403480454100d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 779758758 1250 779757508 779757529
    0x5030f010509120a0c0c0b090f03150408030702011107060903090e011a21132f0f010504030b0a0b010305060d0f0b0406020c1f0b0f0a12030923 63
    0x140e41048203010810000054581d044508100865203441599504441201c000680500025040c2d40001081c030f40c008000d280b610003c0c0c41003c0c80481038400e041d5039038510f8400b4070f907241d050313400600400d030318202654110200b4400800d40e0746030000d2019098200480982d40d803507460411004160300240240d004180d40129006079600d0210321003110380c80310381d0b0f40d0300807100081d0310002d00501010201448000114400080c00c040d107000c030b421280410125080e0611541d11007402110030700c40da55000c551240c078080b11460740c003484101c1d82000b01d461305110041c80003000141c0f11601062044590110029410b20004001420f0720005008103001d203901003041004101d200c500c1c20f00341504003802e141e40340c4031380c0784c507100900c01c0607100c440701d0290421702c00c0076161500e03501c140941c40c60790034048903039010300f0071081d038074004e11080e0310440a180c01c0095104101c002c0014a010342030605446030342e21003864000c1c100100300303a0380c0e40c106500061245003601910313 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 779760008 1250 779758758 779758783
    0x1103060f010b07080d060f0914090c0a0b0c0f0a050a11090c0a0810030510020c1005010e0601080c0d05041208090a03023c150a200d02130b03010503 65
    0x211031652404980305841d100b405005810070900095005100455801c410010505035142c1d102050b61414120010500300b020a10b031140a440482c540c032800103180140c90390300503c94a81d180c50414000c180d03601080f40d144050003041541c55401c0d006106980001d401440030300b80c1c2c0101858084010079880c6034032171041041c6400d20040380c00c24010754a00c201281404051501c4201d10a0b04484090b400100f03507204401201c08880025005403418014102c100d98031040c82461050544001b40600000300c0b10020000ba510f622a1482d142c00100c0c10743d070329181c82c4085080398203603101120300f40d90164101c06403030f0246030b202c00381a40c05940700c1c0c050a84060544c0e0020341791050141100803080700b00b1105440b000400d0070b66540c2140c1141e42d03076903005c0a60496a21a210f11400d5003090454200156185115025010404035502070707030b0013044507404030012207070000d0151132409030f400c1c480c03403180200551405015000d0200074503125071510301050710b0901d103150310703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 779761258 1250 779760008 779760031
    0x80601091107080d14091608030c03120408040f091a0907090302010e010e030a1a06010203040f060c0317090105040b0a06030c031203110f0d0c0503040302030919050409110306 77
    0x1a01e030296031010542e18a640d0024440d50b40301c1c1a030720b400e00940324060030300d983d0086030001d019140000191004480c02444001190160317280c40c610340305d000d881181301c82e41e0002c000443c5c44081c807200b1564818803640b01103007401d03152480d000c1c0030740c070b0742e0040c07031080f070b038038080344808226800c40001040c00071103002029207019540145003c415200080c103110705007000540356805182041050f81014048403d000014202802901c100e241081c000314040300c003140c419403002c011101030ba04003030480030005150403001c6444115610f4107034200031181d400c02d9400110428110300440e100b10001c96141064149002400b0002d090001d00b1031401030300f0000075240070800c40403290000b10858149201100070340180500110f501800000002c561410844620281c114050460300800407486050000d940910050f100a805a4000e10a001d000d1400c1c0c42520040202c442c0340c403681540d02d50104c0c06880180c00e0444100403007142c441941e04040101c84e5004c040c0006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 779762508 1250 779761258 779761271
    0x1f060e03280f0c1a0403060c0507030504210210050d0b040b10120e0601120b131e1a090307031b0209070f03060e040b0115030608030405061c020307050408060109 71
    0x5030050424600078010300e94008145850140200c8403c802e000301590074000082100f032011004441d4018002241d0143c40d100c0000815071041c01903030002940343d1109842c160902c0f07c50034985015240341c0f0360b880c10340c0d01150016201c18080d50490506900c8140c1c41d100804044800d40781030b02c1007240200c1c40c2000030655640c1c2d10451101d00742003418a8008000013280344d00c0903040d000e81c0a1030511441300001080031a01c1e02c0c03213800c1c1d4000c0d03080b0390050303c601c01a040081308244000e400c4084d0020511400e01e072035484451414425120007600b1800000d800f0124101152803280f51780000c00da4009068009103e15140482e4240f42860207156a000130850103000d84418108a211061035901d64001d80c0100d014141c012500d156034580346c40e003602c200ca000d02803031200d00c10144403403001c240240200000c3e039844501079800e05007000c0134882e2030342140b10002d15822072412000b002803074a01c0214050301140d543c0503903550609120710300c2c183c81039210075140307450b000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 779763758 1250 779762508 779762563
    0x603051011040909020d02091314030a080103031b2307080708060c0f0c060c091c020108041106070b0108032a0c090a020c0f010b13060f0e1f060e03 65
    0x1030403242603c0c188600080c1d0b2400c2800440c0c070001c00a17100a4000000301c0c00d08c036410400c00850360401e0700c1307a604d03440c8200c9082d1009840c0e0051540000104000340014000240580700408900b110b03042d00011198003922500d8491203220304241c5030000f500740300420081c1c1400014080c0103940000c0c0071151a120690340ea03030b0402403400701d00c07680201d041034240030780c8001c40f901003030004200d5100e810020800070407544001c1e00d1a21940c149400c0d02c4600c2c0070b65500341080c580513120010103a0b1140c80d40d0240408644500f40c4c0a501086030000041442003018083e019200c02191980d540410640203c0790250892a04a104401781000140d00041c014038450303054402d8405030300d5030348011010340140401d6a5040c0a1040c07801c000d080158402450380008a400c0c800d900701115090301110400d028071761420b60b890209000c0c030709410400f03603008106000010307681c82c6240c8040900d42a5034000700c0c00568500c0d4081860300e001c20071034440242c072001d84030060100c41d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 779765008 1250 779763758 779763791
    0x912080301030816020d11010e0f100c050c030a1a010902190f0e090a1a0a06020a2d030206040308090c330d0b03010e03040b09013006030510 62
    0x5202c0146240d00014580c02141200300141190941c003600c40707850746400d032078003039842c8060b8103190303000903105050180c852078040049052008041c0c0f49005d0f05561a80445040300114400d8450303104450034138640e610200080c8080340d005900111580a0600122210751010b81c8101c05c00381c01848094400d4a036200b00c84441c90490900400c00480c07881c0036140c400c0100555030f40a0510010883d00d01042e07000189c848900c03080c6098184114410003200e800b05007c0c100041c0c2c4044c040e00d00040145052558407480300040500380240c41e5580070050190100072230058020100340810190010b010a03005204000580045541c038008030740500740d8840030310160035144c0402c0d0180346000b01900452043d101d60700b0b9980a10300d420386e002d85480240c1c6802903181034111070f00d2902c040140c5055070800e03d0304919052484004440c5840b00308982d40f900100b03c0c40c035140380c46005400803401044510003241141c070f581455800c00c000d10070408002810180c25540c006c100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 779766258 1250 779765008 779765011
    0x909090503040509100f0e150406060518120106120302191e080705070605040f060207030b1b0c0709090210081302121e01091e030903020f010c0506040c030309120803 73
    0x1070f07030744400d01e55417200c048068140980c400101c1e4100003d01003401c290700d0ba981441460104c440d10a910742c880103100440d81c030741c03060310005038040c414119007503178054151030b0f40000101420059503071010340780c1c00c586da1584100c51041504000380704068041c001f40059010066144180780025181d040204100700031001841d0b021040c40760400c080c1c5070540d056181c00c90104d030380300d6440d14000f038510741c814080d20000d560407003c0040d00c90310001d001000d6a5014a14410075185c0d802c3e030f2065017802c4e01d0303a0301d00c0007014802000d074041c04011a200070710100601190040c082d00500c1070035440c0c22031503820001400c0c100411010a020b048003030ba541a94106201440300c102c0ca0708150042140c085485002200150280c505400900000d0300402035421444000000f03034004a0300118002c0104107241410009490301d0f0284014045044c1400d05044a99555140c28540115400c84502e40c03840c40c24001d00d40d00c00c05450151990000da040880813503220262140070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 779767508 1250 779766258 779766269
    0x71203022802010c0602070807300207090b0a0302030604200d050a03110c0d0f02130e1c0512071e031a0f0406030212150a0504081b1509030a090909050304 68
    0x3514621303403c0010710b03412208956004101142c95190a15140400d80885013801c07440310606140d009802014090294159586800504c052482c1000c18800b40030400400390740300c0c2c0d00d003d0000c0540c5050140510503031003074030041c0c1291a0f842001e0964001824018002d901d103129040001e0030005915405036014100ba88840b09000083c0e0325100d40590041d0300814000c0e150810040510700304070a15108581c00700c45200800000300c21201e500c00c030f00b4450343c031031a0701d0a03116010102070f0200780270034545207192814461000703400300c400303450b8080012004180d0440188801200e520000860700e0148001201d0a0504101c41d51b0704405502c81c006554003d0341c680d6540c3e0080707004542c09098580c0000c3c0c042d40d070503240c100d41c0c880b5a100031940030014842e28004d2268034070440e8028401030410010303110440303405495948c20030403481021001180c4a40044250380303d41e0000000303507034845034004028140c25495002002c4541020410000210080180e03400d440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 779768758 1250 779767508 779767517
    0x10020418090c0504020a05071a091e030c031306260106180e01060e0a060c020907320d060801023a020f04060305060d030f030e0a020307120302280201 66
    0x20240c10682d03a075071500d6000342e60040c400200031035520b0f0030034042c0c203105000b00d0b00d649450301c0d110841c1841074001c0702c155031590040c04c4600700614402e0b6128103041900c40c1200d08101e080c880580c40d651002e4030900c01c140c483e0b40100714040c0c2c0301603049414074800b8003d02c110820898060a130f034106000d000240003000d41c25403070350b112181440005000900c01d0380c402d540e58050180821450400e124050101c1500205205020754003400c052f59020341101c055079102581100e204400c0198010707076205c28003120304c1d450b50103641c042c0307481c2c1c840c03041907a988104041c2101726100781d402182640d0060248a80c1e1800c40510212182c4241c0145046141010309103400f000e21100c40e440c1c07891011a50110084070301c030140c000e844013614100b04646850080281c2c0b240d1101d0014005071400e50003215803440b03500030351160700300107049505c0c0b054158002420204646c000306446c000490b04102810b0f41000740040e103100a40c000164241c8801d0500c151103c02034003c1d0520 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 779770008 1250 779768758 779768771
    0x901121203020a121e1404080301150306030b090f07061106150a05130e10020315010f09210b0a29060d1803080a1107020f03070f080d0210020418 64
    0x314001d401c0112444e01ca44400c0049074680882c12500d20b00904440d0541403400900303c140c01d450800300c601076a048403e90741980e10308845d00200d400810004000c140d202c0c90000005180c800740c00d4000c4461f803015010442980220903c1c10f15a40d00603410428400b4001412140118460f034204542e480c0000c6096041d50204d00c40310900d1780840d0700301078140d680801d1112558031448ca426000c0c030940750021a07501c40c0006a0006841280d4881c4040d11404055030044100c50f15240140c10000e000569502a215058a100e807202070161410107143d0200b219042100340c1c425071141080150228803800903403407201c040c0244522003503d2603144d0f1541d0b505401d5684540701240c040c440c4620300c4845c0d000340c4032100c200710085902d010104000280710700800203e0119250f17a1818500c0c5030f02041071240464401c550103000c2c01d20701140074200e03e400180508a003600404203101e900304001d18140c00701c0036105100d4410301050140c40c01900144076640700164022440c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 779771258 1250 779770008 779770027
    0x61f080a090b0c0a0e0603010b18040e010c12050105030604050a0803072706031a1516140109020109060905150d0f0606110d113301030b06090112120302 67
    0x1d020650018141ea026481086030200090000f465842c4481d521880201008003d00900303002c01c0c001c10b460760b54107002c0c0803a40501c3e4000d10405040052010600e101000f0b241e038210382c080c0550b40b0000c0c1c5414cd4420684009024045c0103080550041855180903181c2c15100c0d440c041c8000c001403400001300f41114490710000384000c000030768000c0b500c50003007100103034200c0034030680e00032909048002c82c15181c0a002e900044001030484880210101038800c91036002d114141c00c0c2c00748409082c07010400010101f00b024010800014800c0d0541c00050501c405650148040040d855410322450301e0b482040024a8000c09085031500ba507a0111000741c452941d4082040d46401800295981d001199140b08106003040d03c0340385a04843c11659248041d0203c070b11944504011b1407071024048600395641408081d194912444101ca940c203d002a0700c295016125807040c84080c1c68698a400c2c01040181244600405a5942d008060600700040700170b1660100ea0981d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 779772508 1250 779771258 779771261
    0xb011116060309050f011b030e030a09090e1014090f0307050c04020d2a03110901021b03070509241e010c1110051215011b030509040221061f080a 64
    0xb01c89005d00001e0010406042110700c58000d81541007000a06060300111106030110840361410303902e95a604569042c460b000002c0c18100c01502c4c20b9100d55030601c1100c542d0b500ca81e10305070300c212286404a0418221b583e00c3d0080c1c2001445094008102500024000152003016403505940160325500341c0c124400043c40d848109428510f00150151400c2504920b55018084e0300c0e1401c200400c4650804000d42c044c119150340036038821941c4d42e440d0320843c69440300c0364000800300d9103007540b20b00c081a08a0000c0d0b400c0d07800000d04e0b04e4180e080542c050192503041ea0251070b5104515010305014405450751440c45051090f60800ca0381800045041c0d6040038030081d0030b04003280c0c6c03402c200500a61000b000e02c03d04075602c2c0d001c90824600810180c07000c0740147e60318069000003054546100070362802c200c0601c50104640484c5440340e0000c1e1100300003100596408050a0100c0d901040c07000b44980d00c43c9003025000c1d602030451280088007800c09241c01440c40d62604400f20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 779773758 1250 779772508 779772523
    0xe071b060203040311060708060d02012012281409030a0602031501030b0a0b19050c01090b040204140103052a0a030c0f120b0609130f060b01111606030905 68
    0xd00103400001000180364208440f8940861000119041580e81c04402c9a00c0d003400d59955034401d90341c0c8546409984100c604950440d00700c1c11102055421454141c5013902000070604000f4003c50550b09116003c0c1d00da03035042c00341c102400d8016500c008001c1001d0325900725121940c002141c4004151410080803e029612410031035032418142c401c0f415440b107000000d0f0000741000d0310200303e810090440c0003283c000c1d40c0b806080c410400c6d001d04840e590105007408000080c400d180b140b80b030034025880304900401a007141c900f40b500500007540c1c25400440744a035100c000400006400040b0f6810014982c8010031000c0e1001c0d11a02049051022707043d03003c4c0c0034a0000c4140803d100c1540100d42001005041c4c25a440110715184050150040c00c0c5810307030000a00c443c107000d8202c2d030340302c0900d06800509011558030380007503100c980415034039155154000303505035822070310301e0704503841d000c0c01000320380c02403205186c030400a07008420030180c40360000c0301000300c108003d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 779775008 1250 779773758 779773763
    0xe0a0204230a050615190305090a08040308130905061509010203130e01062006040303090c05040c030b09180c1c1a0a0b040209030a02012f0f0c0a0e071b 67
    0x100aa0400c803000101808094078090b1145d242080714130303585811141120284090504001d8134000201d41c158010103006054a04e2800b41244000000d039061005001440c401e80805031a56184828051001c41c0d80d003116a45a01c1c00b800e00c000d96440441c2640c91824085001e507603001b00c1c80040381140a0051001c081040c103000103d44011401d45d00c6040e14141e68401c000c090b403a04600032000e07440c89280900b84c02400c08200400c0c840e4015180303481c014205403032201c1c2e42d00003113002c96400e803030500c00007595003e0442032032a0142d1401d03001022108843c0203800280307101603c07885006a40c0b0310075007070400107544005418080c01e04d0f09070130614521401c3c10795481c01200c8842260740d0b004440c80c0c1040072000c0d00e014400d0313540f607200250040040d15510b6006480d04443d580c0700f0909240d02e8010140b40800314412190340c03c02c3d0101030320414200c807100515204490340340900c45c0b0410f203400d005400c040f00e2443d500c020246450b803e03420000034410f00c00d01005101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 779776258 1250 779775008 779775071
    0x5070f0c05062a0102120408071118090607020d2001110714060c180405070e100c0b010905010b0f0a0e09010927081b0f0a1103060106030e0a0204 64
    0x40c07406a12040d83d4801103001104502081521440e09074202c0c458002c14164042c805400b08000c180700340302030f21a6510078200170043c002e0160000d00c83c129203150124081c42104d042204180041c050690404890300040c9910013200c1405492840c4402c204040c000c015980611f00d081e00350807000800c041418800d640b0142c40c2400c00b4114854060381b4071a21901000c40c020008110031100d02c9940f2031060320501c104801000044c1801816507000c014a0310281116640c6000f09010306a03910b403529401c010a80c542040f910a05030301904c480303460300c0300420814500341708441c9032021a070340c403a0b510041c00006a40c8080e108000d10340102454001081600d269840146241000d2461645c0040c2441418403207403418080101240c46c2406030081301c40540d5020300b081e41c0003805a8890b0110040c615241c0112110301355800480c020000c2c580d41804c0c400907025240c00d1800384141120b800d003880d41c03060030000003402155948101c00501304405544611021440032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 779777508 1250 779776258 779776267
    0x131b03050c010f020a0f0c230604060302030403200106080705090f010e040f0b0c0901030501140a15090801020d0b101704080d02040306021305010e0402040509010b07110901120506060a0605070f0c0506 88
    0x10880c0c0343c85194001c8040381c500c001001c0d036070a207550100740c5234880018008e038902400d15400310f0180d04060300444c00c2c4a0785040d0361070605c0b00d6200014002042c6000040c126141241840c40c02e92160b010f0341c0142060001c0c80f07114070085208505407081c10460003203d85a80c6020141e00b030990300c01400013a6140144911250908010021000300340d82c14020740c0d0b01e6100c45103c0341035000741c1c203034004070882c802c114566407201c0755400070110b4101a24599540e02000d826680180500f0032019602c011407009450b1180f0515601c12852a10a040c03503e05890003112100c044c1000e0b140c1031002c20181c2c1080103c1d0112409164040029901e52222001c01604602c15014850100d42d107141d00041904291082d5000c4800c010704041d41a4038011165500d0350001105032a603480c045020901c030384403200b0190003804c4460a8032250000350900c43d00340074018290b1031003103202020400803e940701b400e8503601c3d13400445030741c1c1564903403800e4040c0800380d50140b50400e40206 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 779778758 1250 779777508 779777513
    0x90308030c0c060117031902120f040305241305010b0a03050604050708280203010b120307060605101d0a150905122d0304050603131b03050c010f020a0f 67
    0x1411042c0c1d504002c407903007640c850310b00d40a5012802c0c0c5044e110b62050014103280d02e600c081c80030101c10240140c46a82c940501121071380d0b07200704221b011143c000913080080120400c01d00200c034107407403000d940000c00e140549400040240031100c0c110859008031003130210a5000c1000714000407c0e41345920b41d640349c8140c070341030125802c0e203150245200004d032010300401c00b8103100059603211b17401c186501552108940f6500000e907050343d80e0f42c0d034809098451101c5004082900c40007540c50361403514004040d0b1b51140c2016000b036134071103100181c641d00089907103030031410074451500100c1c000c00492441c02559100c0141e01300c682d5412010246c01454480a66134182e80c009402c03103d4003030b41660f9218201710031600c9000000360203010100c5c1007142e051013921400b0b5034070741170b940c0000604941099a0184a42128035586000c205e10a000d00302c0e8003180c284140103507071540e1919511030421880c29030510800e18011041702d442402031242d1241c1c44141c5140a815a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 779780008 1250 779778758 779778781
    0x509130b090f040b07021f0c1103223807051005090115050a03261306090501030b0d110402090603011701050612030a1409100314070309020f090709030803 68
    0x292000e4a80e01855800700e8101440803d4414400045861fa5140b0100007000f500081000a03441c8040001d1450030700340d40130040c0000c01d60a250940e400c079082e80380300080f41c0e50b80c8255000e1450304000039901c1042009280e40c61143c0b400f007180154030081c0361004080740b489034100052960044900500054500d07034421070003000c0d80402003003044040c0c40c028010b14001e02072140d1291445008100280c101040364500412114045c210b8480a066001613074103d444e1034078004c00d4003001440032a512040300300c0103240c246814002c0c0446140410845019000c02600444000808a100c3c0d11241c0440b58200005404542e40350f950f6046d001a4103000d02d4000300715401c00c0c001c49c40b00e01d0481240b0303804a9180c07024510304070b4a02e8080d110803c06050301351031601c2c2030203040c0c0e4680d940d042544525000b518040780d4486240314018031024014501402c2c58500b25100c400340c3c0f100d50106070204411380314012652a410400e451040d05540000d100d540000704100f68140e24 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 779781258 1250 779780008 779780011
    0xb090406030615030605070509061801140703020703030f14090405100503121c1e02030a060317030703060603050c070305210c180303090108060402130b0f0c0f0604030509130b090f 79
    0x5e0300d0400030368a5203102241e044c41303a8021143d00c0902807205100c0128810005c140c180e00504000b2242100711300e5261084e00491010350250304002800c10a254111164001c001580c0c941507424030b01c0704201c402d8600505110354002c2e075540c03000030900e13000e5a84000152900404507404240400e001c81480c0c2d01400021140404000000e40811258020710607941c1b41f1621040d100710001c48400002d400081c80d001105482d81000404208109202c2010f0411104e00c41e5803840c20340005401da40465001c0d03001c043c984020000702e0050401030f83d41d0305a0510384107554100d110100910380346003400d1030350715089003014810402d4400c002045140083c100d0041d5042030030b0200343e207034080e608400f80429101000100103242a034018100400d810194000e420344821415640790000f64112200741070010b0b0400c1441010426004643c0c0d145000304524a0150f50042450085000041c041d5400520400c54101c0b503410010441d000606104101d107013214822500080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 779782508 1250 779781258 779781263
    0xc0209010f061e05030c0a030603020603100503011d070b0a0201060b0d0501050a0807060c03080915040308060102010f0917310f0605120f07090e0408190f0206010b09040603061503 79
    0x3c0610071056000b0b00c3d19501034401e90f4481d5800c5690311002c200955221600140c10195200300207c0140e45600c0a58010f085212000301c1e00d03820402072500b1202c106844802da0301c4141c05802412074000354601c1035454807000c09454001c1d044003a809444207400441008101041d04010003010f0b0b4031440c101e88040350242100383d654089142c45050070700520000644520038040441d000b41417140d0400303912002c0352014000a401c0c1400d1a00c180c400700c00140705101440362a41e424001d080e800a480f01c03081000305d5550366014040b10290600744030305c50022075001c10995000104502c252810200742c0c0c41a00c0ba01e441c224a06038501428840000d11040407a10034450000e460402c80c20140d150300d039454a00c8080410000209418204040c00c1c0002c15510000380400c3d003d14414044141c542c01c035183d50920941c180b8202400b0815401c00d203c081d2035000510604640c62040003a55841290300414080c5c81c6581010b00400c0c10074001181204162022208990 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 779783758 1250 779782508 779782517
    0x1080c030705010c03122307020a02041505220e061f09020301080d120b0310060f0b030601080f130807080d0c0905030a150b090c04060f0305060904120c0209010f06 72
    0x192610019502d800c0c14490160020300303d01c540e400c11000c1ba43c401d8280319510340b412106c1900451000f090000d0031114100143c0203e1380d02000c500341805040e070626290450130030300c1c500304008180b400c46010700e0b8000e0728440d082e0b000300400711a4000b06001d520348042d58001d140480540c1049140c0c200d80c460402002c0c400014050b10901c2982d050715580c43c068200301116800480700e051a113400740031143d076034800d120017036034040202c201c000c01a5000880c0b514503299a900e0a880907900171007001d44c0400807c112aa400b0404980c05000501511400c1c0c44152828445100d801c40040c9041000201d50301400032001c0900b940c6000800e041c42045082c60044444600500c00c103601340e231140802030001a0601030705442e400001c4030000b604001a4001b40310b406040d1280c00c150080000c003880300c581e2040b2018045403c506003404541440c4c80880d12440c0700800280c1001c0500c6860807a50b4450b032180ea00480d0024103003400f550716452400b1510070540305080115 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 779785008 1250 779783758 779783773
    0x70f0c080d020a0c2d08010c020709020a090608091903030b1003111b0340030c050607060f0905060106021e0703120c06020a03050406060e190c051201080c03 69
    0x242c40040c6407031010b648035a2031030205240c41c1444840c0b10320401c068040e040c103590300d9800a1400007a48000f451540000321341c00c0303d9036602a0421019400c042d0344140100001001d007508000d044085070b116160000d00c660b603d0070003038148100407800425151908010006141c0d0580080032110f4085a0f010504079010400b5001c0307a0341009011959582406021010300c0b815047c11410902e44050340d10b0700960b5694070242c0043d0030b10004850700c4401007101021610301c0a248680f00340245010340e14159221155600864820b561040340001500b03001c211164202038050403e65400784048800c80c44d00503101c0c40309020f440010b2090002c03040208814140d04043c440d80000500312460840e1525074001071000d82c4402480a100da000000482903c010034442c0382e01d607400980c030704284c40c000301610300b668481c50300920814144211a1100210b040c0040c9105400081c0d0040400c82503400380502c5200c400740102c24000050028008111020640d20031410307203111 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 779786258 1250 779785008 779785033
    0x1505040506090f04030e04090c0e1b0a091802070204050709140d03050f0304031806110d080402180702100905070503010b0303030f150f040906021c180b0c070f0c08 72
    0xa24040f0b55644262880c40c01080c0424000c90400c404c0382c80c047c001042c103422607201c210109010381e0011841c1440c620070031032114900103448100c0140c84050b5407800044000003007a410b40e0303016106030450000c40350309028900742c1c11140c02d1940074001344030600c1c0044025040001905c640d0b121501c44600192141c6801361604915a078586c80e01c90401c000002c04d0119508002d00c11424007540c401c034a900203844500e0f0740005c16413666050480fa4000c0b000c03600b0101120080e0061148480070302c00141c4d52005000300040c2c4010101c95a80d480c00d90403440c141e0318460303010400c2d03d800315200c00d011780032400d20180d0704c080d0000e0042c0880c00d014540d07a8441128800714207034000300070a441c1981121100d1a0100007000000800401c00008041b14405401100c2c040c0d400030300d03114003440c2c500c00a04c100402020030000c0c101064038994041d822070740020103100c4007000240030020240f06a0720101e81001420759a409180b07440900c20010303015014483c802c2c0001c8454 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 779787508 1250 779786258 779786269
    0xf0f0b04020301062304091b0f0206160c050721021e0f1005072f1203040614190f09120f11040f0507020726190302030d1505040506 58
    0x100d55007070740c03103074a83d82044050b0b144034103c0d55800345105c0c04c00c000c002039164203070003844049182c940b1244010746a18401030f1098146800e03250654000c20704000020001c440200d40e6a4080d0402d00b40040f400e01e0700c0ca003850300d150000d03007039510124011000746040c030907a00c62585c0300b034070280c495414505030180d03a5140d40b480180d0080700c1d91401c0070703907040840fa85040c0e04c00504009040c20110b0744c070034688a0604040d40051800b101161100201000039400702102c01d481003a91084c80003c99500c9210714080d003014080144010841c5815407804c5810619440c0582040c0d81004840204a048044c5843c4001482100c022804a80e0902c001c26041e80c000020312070f0408594030f1103880824041c00d1a4000d9885201f50455186030103180e1141002d580038080103400c1c0402103004044c4000b02c0320700b00c03071900958081d0a0002420b000c07143c0143c50310000c0070185250492640c0b2031144100209405c00c08038540340f07009180a842600d40c219018407150743d9200c24085c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 779788758 1250 779787508 779787511
    0x5150309060402040e0a0b0424050601021b150318070f0807031502040e0907180903091a04050a080325030804022b0c090515030d050c0a060f0f0b040203 67
    0x44140d041075000c0b6006142c50340c451500e1002c0308056508100c10b5455030010032604a40503140060460710740c036041407003d011001a4403100b08104214200700700002d40e12005800c1c4010004400c1c0300c41c26440d0394072900c14030300c100200355283c3d607880d25444d14012035510a00741d8205107c3c420003c607003000d40c0300a035170a440d00c030300050000034516107590215007a4011741c004c10a034208404681000c0e40700d12184a192804014004645416a055122a0344103407032040d241ca007440039000660302024205c202c80d0000d96031202203540001184c0107110315070006030722070644480041c0c80e020104c0940070010740ca4814521841140c24207041e04e07100c8040c001c0000f032a11000500600d068680390a600841084110340c10407164007040450b5003000041c0c885003810f40e010000c02485010b4a58401c1c1844c0300700885540920110303581c0c5600d282c1c40c5090000129003200c4070403007042a0b008103038000d541444903044082e0044004c00c4c01d0708000c20020f04103602000281090b000b180e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 779790008 1250 779788758 779788771
    0x7060c11100510090216170405011b320705030a020a0603051504180507140f0d1a040c051804030f03020703110304030b010f0e060f090402010e030115051503 69
    0x3000c21154841c1404002c150042588000750941a0301003407a880700c0c800f4003003425164081440c4030080342001e150a48440039040c012aa08010501a48e64850280c111000080c0081941703032000d450b01074078490182c0054407014103400e0141d400d182041c280541950a440144c070055a1650180354489113415000b0390411080c00c000c1101511a46c0007540c407109405c10340b03818600d140d00260980c0d00720b40c1c6002e10315151002c4102400420701c0400010448541c40403001c03003a00002c42c4e071580c0c0c07060710184540108452001404002013041c000711402500d00c480f0b918151030b000d24420424060140030310180300300f02462946860a003801190541c03503002c2e228100500842c0a0b40c8074950441c10004042c504c100c01c0c0400b00007910285224000c518201d60409000c090b4400d682d80c0304000d904864010b0109548038840c0c0b015180030290f807a03074516500c031300050383c0c0120300104c003980542c03178010704000c036000b540300c4502521f00445a40450486030301085d0b0300780c001a030740d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 779791258 1250 779790008 779790013
    0x30c09130c020a022b03030c0f020a0f061116050a0312140105241309050903040e070810032108090724031407021c050a0804020906150f07060c11 64
    0x1a4001d460301c2d4400d0605c0d50744000f0310441019001c405140240d01c00c2e0803c501190702c460880d00c48a4010f859119040e605200800c1101c41946075004440c0c001c440241c0345a540301400d00a400106040f81d190411900401c10003150503d040c994807181c5210643c0020404503440e0207000b141e029042081d54682c01c020400d03400c080410011500035034600a000c160710b00134181d408940d4024042611441010882262a140f043c0044e294000e00000c12504100002e1101500454800e40c203c5650320305541c0a036240c0254100b12011900050540030b202d408040c2d108800010218903904a50794007000398443d00043c0383d90f041c076070240c641da104001c82045000f55038000c94032380c2d203445031038040341492550300321110000342656510f0058100c1e120000e03010804020504c810051490898038115241500030000c12001e80001c0c4112192000310f8241e07900c0c0c160b010080340091000b940e40b01d100c2d2040c564903521070041200c00c0341c20450380500941c054494070500d2600c6002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 779792508 1250 779791258 779791273
    0x30115060512060a05040e07030b1303050d020a0e13050403030b010e0307052b0b010806071e030c090315060e0a0c140d060e13020306240409060b06030c09130c02 71
    0x603550b84000700141000e8000410303071400120341d40d030b40c01440b050b01920030240400a083d8101500a0000207040c140c2401021b024100081d50100444065661200300140c60b40f01e0008100c0e1840080c024042c1e0055140035038880114003540300e280075921a44040015038042001568400c4117200c00b540d140d0491501007105040034010040416908036119240b60070142c21b090100b4600c030020b4500ca0801c40042c080c0440802889400850600b4030030000c0280003060110b0140340c41001c01010780780e044c2207045d02e000c2c1c0030900240d82d1001400c855820902c03601c9000389a103200707292001400500bc1201070715144221101e88650b80e5540c0c4a450141c907000b4007aa100c80c4901041540e24880021290141d40d030300c83c0500403c5120100303124a900405187c01d01c0a00700d82103002c0840003140f944405400e110b80c00040c1070310041100e40841c10114010804c02e0b08017134002000000f088a4001480d0090000b20012038074000d900300c0b901e40d44d0003110021140d6a0150f4030004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 779793758 1250 779792508 779792527
    0x1150f06020c2b111807021509030403170c2506140403231902090f090d0e010212040e0702010c0f051c022b05070e0102071a270301150605 61
    0x118102e054000c0003103902541404000c101003151790040d0002d4201301c0710504c90700d82d5041c80b007021402544005000704c0e04211410f82e0b100d116501c8003e26021030045150030048644d02564602c40200050711800e01c41a03d40000d0302910010007105182c1809020038603a00801406040003801e141d441d04045c00c1d07540360f115145d40e06116496000316080c480301400c01c10011040f91a07004000e001100900c2c0c810302103083d001801c034003c02030440c800c100b00c44400080c10741000380d1518088661540c8000141d041441c20f1005641520300010049103011800841c540900d4943d4000c10000700e9106044407100c00031001a00080c00412081144d00d03044011010300000302c0000514141e00400740c200020203c41940329600d0461034204411000352091607800546030500210040e0390100013074840038107014001d2442441a00c02e90760760b04407019986880f50035040220340142203e031b08102c11050b042010300c69800c00d0720540704548082c1140b002c8601e25190b0504140720503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 779795008 1250 779793758 779793829
    0x510090807140102010e0d021f050402060a2a03180503160b03060402091e01090906080d032301180f060e180a0803010b12160203071401150f06020c 65
    0x2110b0241c1190349825010004640034482e500b02090345030020300d107039002c94a001d8030307103030000400005003031a00d010440907840f4503080303400503502807420680c14101005441c940182c082c940001411045610707504264110310384405000038a032002c41020365400801d50344244680f525810321809050402640c81c01c8400740d608580c004001505014034200410603030700328403543d4060911000f83c0a402540c01aa410028201106042c0900c6003000340d43d5a403519081501070409d50f41305025408900c11300b401c0112a1150301c090350065969003007412100c0c0940600066040c504829841400b2803886024103d4840e010359165903518100c41002404850046044900070741d00203400044000c0000d60103080080442902e031844005400c0c02c00000800801c403401307124942c2c42b6901c1d000000d882181c0d5000440302441a00b00e0600c6000d8885400382c90940c5d8000000803600b52403209081c82900c4c0c85a007151002d559040c104a2044499450b400c5582100c43e400c0e036220055 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 779796258 1250 779795008 779795039
    0x90f04021c05100207080306090a1406010f050702040608010603050f0f0c150705100f0c020c060313081903020d050a0c0905091806040501020406020c0a1a07150f060510090807 77
    0xb41c0240c60711024448031142c107a0380641d8044a84400c000100a4580343c07000c81d4a400c185000410044612440001c01c0603000290144c0e051228460281c04414890303000c4448965001e44148000e6035a805c540307019040a0004403428000c51055084480340010006c0991007100c0c001e0003171011403030520001210401545154030070810000740030440801c1130740c408503211900010038400010311a0201d440e83ea250070215000407158009035a10b80056981140a00c1c01d030b1007504980341b804c805a0301ca0034400c078401210050325149001e4141e40500800d598144050195544800705203084424182c403d034042450404144468208003005942c84003d007a202c002000030001024542442202e0448070340e9000542030204940c140070380b644140b010380d1001031103400c000c0954014040c00140d0600407002107180000d0001d94840b1640300e030401c3c9810040c80b4072440001c00940424043c030b45c000d00c80800103035078030b43c4038600d9001103490482c0078120030750915880c280b01460 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 779797508 1250 779796258 779796263
    0x2503110c0105070903051e0c1e102613120513181409192423071403090f07180b010503010605070602030601020709050c09090f04021c 59
    0x140320310309120000340318a03400748015465140015141d0f00d0300c06e24080d0f0301c180e0401d0401c000b028000d211100022811516503044138081800c0d915a002062202c1c0480302ca25031000d284404a00c60301e400c60403e410745034107505080002d00150318005c04001301a1340e243d0320312404083c1390010582d4100b070144990500c0c5882807038001d0f0000452250b40c4990410020482c1c610b90652000402e8442c00e40c003000850000d0496181081c41c0b191103262803100ca070341207203681c030b04c000c20031a0000c40c4040804964007000384a00007024100001e200b80e60b82d0404c3d0140003120f0108210301c01007141c1c8030318216a40c241e80007078650000c1400d900050091036040c4a504510000c03640300740300343d00240500c03245048981c040007035240140d444222089060120410040c020658000216601c00e5044100540d0366200c80c00100d24000d180c0d441080703124941002e01404c01c0e140ca008207402c0300125014003c948405a9034009084c1c2030300c00075804080f11910449141c40c0c1107a40d1791450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 779798758 1250 779797508 779797541
    0xc07060608030c100b1e0907090b04090f140c031810060311010f0f02122a070807050915040c02070b07050d1407030c08090301020d140f2503 62
    0x140e41c1c401041c07030b6402c0a041d00016030480c0210f00c0700c1d04010710a100d4540403c640d0001c4804180e01c5004101c80303111580e900407210403000030f40150250002400800d84903011681e160756403400c1100130f01d10520460800e5007840c030345000020b40b40410701d000d10101c1e0400ea19545889100d817408401c0046440f403940162a008076541405210f88c00c01107000d4058503001d0050302000408140c40b00010b9000e00ca544900c42c0000c41d40002d0301d000c145940c0303003120360728050024500d078040c00c1c180c0c299000e807007103515034145204003140e80021544d00c0c41c02c503481b558860041001135a4200ca01070355002c403c0351030040c0382c41e003504500400070850041e15416070b1030b04005505548a01025525540b18000e81c1180c5603000e181d540e50550b0420505003402c41c80e5a00602140e000140644216008108861555001e60444145010300102000b0000c01e141581a8940303080741c001200b52a20400240b08001020030980c4420070041074110158101c00150010300a0798226420360 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 779800008 1250 779798758 779798771
    0x60806011211030a050108070e04020d140a140609030a0e0f040905100e060105040c0e0f0f030a051b06040303050703052514060108120421120513060906080c0706 71
    0x1c030304500c038449a98500541c49540c03031414481010a03103006a0000c2c0ca15404682c0401242c0001d08840742c000d50b040320380040d200610b041c42c4031541004201d803862070040c4000b0380c041009114800c0c03c8006490142c0b0080e950703850046449004107501e16012510b070701520034951515495005000c0b000800005034900503449291501e80d9009024508036910401054682030070042e050051030100c40a209804032100c3c0188100c840b4581640112603500c0070161956400440c691144006001c451001d40700d070501c03580e00c40e21164550303c94603142d4114000c03420003908071010b49406449103890040c282d0b904549903400070b03000c0d0780b03c245040ea094000c202c1c00b040a03950103006000040c40c0b1f098110407542040741c180d000403000e03030020001742540d2500c02d05407011980c00c40d944d0400b040280041410a04041030011b01c45500c0c500d180b02040d40010141000f590b29074072030745036182c50700400e43d0020b1841c05a01c0100d00400000b6100381c0301400184406c5105250200c0c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 779801258 1250 779800008 779800037
    0x325050a17030106090b03041112010f021c0609090803010e040c08011e18020a1503090b16021b1522030c05150f0f070201020f03030106030b010e0402070c06080601 72
    0x80002144440710809000004001075a400140071020f404005251807960600e940d5103003260f0b0064800d180664864541c3d80c00b21078080d400580c6141000009643c0e801d41c0110b00c80043d0140c1040165417480d04c48042800f107882c2c8101d5440917800000c0500d580d0805104c01e580000080c0201c42d04040d610340400e01507802c0c01030010500142d100030300943d65000320001034034003c5a00200c0e0b802402146000340c0e58502c80d01045802821608480195014003200a8200c41002520030b40ca0034052180403800c444044105019660a641c800d18039102a03090750140484115400590901c110501c102c44200500c103060f80b000f040050042e800a40d511181d200341d1042d034030319803c0801080f20781040c1c2100c04000d21091201454040b20724101e5140d4050568000c1006201141407000c590003000000510598801100e84075a51031400402510304141c0c200d001445000400c03c0c335003054000c0c1c6056580c40303401401d50b5403c01b501160041d40080c12941000302807204200d9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 779802508 1250 779801258 779801273
    0x81b072904032a1d013602070602040315140c0a0e01110f070810020427181103010b0d02010e040902130609020c07080c06031f0902030705070201030b030325050a 71
    0x512100c4c24240e40d8040101c500c02c507690050f40700e5001d1711182d50713a0100000b943c2d1120502c1c00070524902d10301801200161000340520702c0f004000c1e510020b13000c014000340303100c1c0c165403080e0040180500c1d144804040302000c0141da14a41301801030000300c0340d403030142105400008040c94a0f2802c05110140f8500c0c1c801c8070700202c21150070440c024080040280002c1115200d07150081d0704d0306140c2a00411000501c00d0240700742c40c2103a07101d03031003104d041c0c100112280b003000038002d00c0069403e02061a410502140e8400d41c600780801030346043c01c0a5400311a5016110901c0c9000b81806010182c40c608030126400030f2110800740e01251a481074030050446254016102d003200c080f07443c5400c0c09074100b0a0140c0c4003c068090554509085070380c0411404040c0b119105c1d030510345082003031507130001d0480d00d00200405c8100d60340300c0082c040b041d000366003e220b408101014503451788217012000c1404114400480034142c000c810303040c0f665101d601220b100110070f03241e255 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 779803758 1250 779802508 779802593
    0x209060403060515030c03030a0c052b08011e050d02010e1e0a050a03020a0b1e0409020d1503050d031a0916080a020a0912081b07290403 60
    0xc2e00315549000b40110700c681c0003010540d069058000b042034010f1100001d07520702400f2546000c2160b210410010401c040c0500c0c0720705060b8540c0c0300c1c249083d0340c010018035140d081610002400c190000038030000740e40200c1d000e0406040030f080c0303c2400c5c04c007405851800368006906020740f60840c00f5a0340c8ad0010005030481c0100582c0051a28800070000c0700104c950146108020f00c100034000740c0d85c3c403a610700888025a07042542e6190340d0b0200c60750178800c9028410109804140000d0022460700100094014101c0401120221500c4a503044825000141440d4840e014142e8154001c3d40200d04030303821469280e5020542d100011610001110700c440c41d07602e0110f103580c03030a42040003170350880d9688905604240d02c0b1203000340250514400d968084091355203030814480c00900311507442194200540500b00c41c445800d5503103001e0b00c03645603002c00662608000143c4020402c10000309481410725080c0386440e92030750600580825950700c842d604c620714000c0132500014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 779805008 1250 779803758 779803763
    0xe0f060729061314151908011a010c1214120a020406090e070f0e0109080a24090b0103060c050f040f030203010c050c0d20070e010f141e03010209060403 67
    0x44805160400500580c2c40e000d5810f144510b0502c0da910642c1e02c4d07003904071a403040310003043ca00050072120006550a40e000d5804203104400d0b1004149448190081600105c0d1a84000c401c80714a0f001100e1048a03400083c6c4070b51050140b6002d08c0b84604034000c0000415080b440c100b0550002041314908213a4015070a02d41c0042c04002180c0c1242c200002000c0d002c4110060f80380145010b050381000308018010840d95940d2408076a0046869030013a02c0d41c10104c4003010820703d000c03100c000400706800c2400c64040d0652100800d40e000d6200900d07480124908940d1941d510765000d8a800d138010030520200b440004001041c4c40e015000428481414141d0645140107042c2103803140d098441c100003041021505400c000211241c038021940b130030a16201d10f4809203c007030600404100c01500510000149142504100d50b043c1c54100000d485850755034180c0680d081034402d420341d0080b94866100030180c441c91550041c411002d800580f401e444040090342c0359019402c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 779806258 1250 779805008 779805083
    0x40f080f160519080301211203050609090f100e0c06070308191107150906050129040f170c040c030f0b0a08100b0f090f01060f0e0f0607 60
    0xc58061000400c0f03951012840c840070480c461016480b0032000d480b05018002403a0b1890b0070052110000328082d24541e500f00743c0544d4100b4080c10001c002e04010307030b03000d442602100702140062002061184c2203c1140340140701103800c0100b40e00181c51440116079150091601c40b5205864210042c40c41601c243d071801031b546002140c2c05c13401102404520315003071030702c15110300d180302c14402c4526954000b007109c0856501c0c80a000d016008031900100311600700b10000600710324600c02450209981400706003002c0b400000302d030b4240520701c10181040b4950380100140d00711261580200800708080c0c600200c0c1c0100030406980c6c1000007140002c0d900c04222035200217512485000300c50480e4032030203c624044102e50340d05810b180040255030703240b0b509909591034030321080c60207001801e00c40c0d1350700d403030001c40035055004d110b80b0000c80d10f9040c03a554203900c584001b1381c60300c0004180000c03940c080c606028842c0c01c0750408440aa03d60000010007440d56202d000c5080c201e541d6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 779807508 1250 779806258 779806297
    0x150e451507120203070f030207050102070c14010f0503060a032909100c0f021011070c030f060e060708040305030c041d010311031902062208060906070801030b040f080f 74
    0x41418900702c001e012020301c1401400400c0790300484504810006240260312103d060400303600a103d00d500003000b08501280001d03042e2211030015994000980700d0f0380c6043c607000780544080c8011200b66502c50b200f9002840011004030317100d12407044800c21102907040342c8540000d8004265540141d0343d2001910700301051560003402100d1107145480c941c000e1030000c002c1d41c5c540000404881e03442d160200902e059154500355034180340c001c03405c1004541d0300c0c00c10f030346e46c00b80c1803605548150514811542042c0001740650240100360b03908482650b0342d44084409802c0608001c6845108001c009503280d6045007244841c820003030800e1440d4518900350880100c460105402a0024074540c501c440c1900540740700c1c140c040d11298be58010700c654001c00340b29000714244140720902000300d11b21900180c12885184e81004590040d101d20700251003640c801d10005204c042c080d4001000191a420540f428501c01e0800c54201800c0719580e40720303034101d10280046e100850740e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 779808758 1250 779807508 779807521
    0x8030705011a06071a0a0b0402041d060a1203050a0512010815010e0702031b010209060301080a15050f01050f012a260703110709150e4515 61
    0x11021040b90089600e640350140c3ca41c0c81e140c0e000a903094041c0c0c0000c80c4000215118490b401154143c24000c0c0304540d941d4980201e11594107015030381000300102a80041c1e010300300300c00000180c0c0c00c8201143d84003800c0e560210345540c0b01103d01030800006000c4541041040c12801b400307007201c07901a250b503144401e07400c085000d05030701040c940001c54040c000419008070449044040c1a8040c1103039401e01d01809003e803141c50348141d0815800070000414000200b280c0508512421180b10003140c0400742e0000c1c2c4800b0344040d02c44600080040200e864405120003002c40103040140c01c21184a4141c06200381c1c0c0c400c0c00301c0002980001c01c00b0460783e00303400451484543c80c5521b0fa8000c0b1164a101409003aa0040920044500d521041a42044048014a04801c00344803010a6110800d50521030740310b0140c00d05a00303c049104c91001c200c1c1650001c1d2074417507910684070300036048050700d410012451508106800c0902011a05101c0d025a803c005e410038a0300d402d020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 779810008 1250 779808758 779808791
    0x7050606010804030f180302100e1504060509010f11100e24060d0201020f161d19020313020d0803070f0f0e09040309230f030d050d0203040303060803070501 69
    0x4001504204610b0300b0080002d8014000000403440c91404080e800d03051244070103050b003241c2001c0d6001c03500d540c40d1041140d10200504084106990307451510b08003103401c0702140a01d0003204003040042c09035022039440b031181507080300d00c0d0745856080b03c41d00c1d0401c1c0707007000c0d101d180d0701806c16100d80260740350840c1002241d418180d10103044180f80449904c5641051000d4041c0303104d1409007a860040d03a200304a0f42c070016a020068883c3d540d503102050704040403910821804090006211031801c4052401c18881c00d071101046030000003108842001f54801020801340c100f886400001503140c0c40000b450940c45040e5480d42da007040d80000d4541c07800140c2038004c02800c240046441e5501582c82640302000b60381e90340003030315a440c0954503101e068102c043e0308801c004c44011260038840d144a83c8060a44007150107044545c140740d1103503445010080400c074200000e034444501503000359441402840c00041442d15a00c415080d540100030580f0300740e450b8030071300480c80b105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 779811258 1250 779810008 779810011
    0x1422050a0b030117010b09010f150804051e03130e0105130e1002030a1413031409030703021e0306010f0e09010605090a0c0c0210020f010b0a3605010b070506 69
    0x115034a400e09440d1401d070040d98401401481c1c2100480c0c10030102c0110b00f504414080000140707036960759178403002c140c3c120190512408000120100714080941e00403141180200d030400044c0880400c0c024405030300564ec40d540e10840e00c010401030006003038495450001d090080d60150f00e9501d00000c100303034035038003994190865107803281804000c01c00003841c050030200c0b0720000d41c490355500300d00d034010045201030810b0423402c042000b0f0b80c0c8001c011080940380c82600c2c0d0311448200d42d03a40d41424004d40d1030a540640c807000041c0058901011f10a5000c60140080090003090102090800c4820f0703005001d0200390840030301000c01201c810980c40040d40008202542c582000075180340c402804a424036a80d807240c88207000e211350f0500c0d040c15006081d40c0e14022000e4002584c408281003402d006500e094400170080c54002441802c1340ca0100391500e1008c000281d80b01c074007007410344106505035100007254407250305004807402003900700300c0642c5458441c2450ba040810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 779812508 1250 779811258 779811269
    0x20f010b0d12050702130f180314130803130303020f010b03030702040908090301050f160201050108030d020a090906120303061e1a09040e0c150f191422 67
    0x1005400c0510352100e024000076550407004a40c21821189000c0c0e4241c403e051000e5001110300c6d0758041d0800d9640c1220102e01500f503810003108183d02520306042c0c4404000070000b03040046010480240c05000c0d01c01510403074441a11540e807090350b145103a10454003070b144040c0b014400c00c00d00d9010b10401d01050308880c000c0c4108190310000946900c50494001c4c4115a617003090410b12001c42d054917039200b00a0000c0109060290604c0c442d180226012138000050b034a0b1000d080740f06000305412102075200a40c1010403883c2c800019410080043d03082200311800040c3c050028011030009000d00c025201c418551428018143c407030700d801c440b801190741481c070280385171070512003411210000281000d80e000ca03140280c130b41c49007580265000d070900c207000000040100700c04141020451703030340e00120031700301000c510360185655154405e2000d01000da01a1280381c20f140b4905681c1c03403c0c3c03180030351595400e02c95412014280c6002103400d1101b290503003684e000e05000d0308 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 779813758 1250 779812508 779812511
    0xc18070f050c0c0d080702030a0c2103020a0f0503120103030f030f0b030607030f0608030f0c070e04030503070c0201020a0b071d040510050630070305070518090403090302030102030c0a020f01 84
    0x5000100035a80d0b042c14a40c940c080c1d0513030036201c428082c02c8016503002590040c261100c080040c01c040a903c4114010341a201000307284850050080100d100743c86079043e006444060142d880d6100c101d004c048040e10701d400104001c120726030f1230240050103184642c481c1ca100e010700c00d0000307045a01c0042d80c0300c042d40c60202c12407402e07580014926480102da10f004503012088c10198000303450298088003e41c4404211041c011544030f003c5c01414800324119842c882d030380c140d50400b0030300546010340840c1c000c00c080740002c0c0c402e410449580c1d0041c012904028000e54504840240481d81400000d895011091005030540e0341c0b4504501d0441e030501075414556035050b240901c40c440c8038070500c0000341e2203080c40d404583c0d884074002d0394480300003403198480000480321b40403991800060702d0174000885042c000d40545081360000001446001c3d54481030214015001c0c10a8050140200d400401660240011407040c0d02e4240d0154890014074000307458045138112680041c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 779815008 1250 779813758 779813767
    0x31f0617101a0406120b0a050f04200703030b0612010b070f202716021c03021b01060b070602070302031b030c0d02190b190213031a10090506030c18070f05 68
    0x1f581c030303c50828250f400448071450242503d000180c002c1050729048000c60b9110000324012510f85009401043e0280d00d061042d08600c908001d02da224040780e10007100203600040c0241250b41c0054a40d952041c4030326840f5a083d40c9845803800c0006d504030400c440e60200d000f8a6003810011030700d607415008107490703110f40107400b810380104004001c0b10301c9802140740c03440c0d468401c12501c0310900a40f046500c03080040b0300028083e6122040f8403000070620303030818152510503c960012a000300c0113083c100007044c0d641c00084d40c45400c0c160114031041c0100001d8986144441052810380b600843c2d48804540441d410f00344c0341d00903403066400091840382c659045a007003d0110383c0c040c0b0108855541d0301d48a80200a400804400349440030928090440441c0e440c0c02c20b82e8010400c0c3c007040c5140d511143d40a9208441445a0a015200401640000e504141d4211750010190b6a003220b403280454020502950214191045002408105038010740c01007100341c0c142c5495440d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 779816258 1250 779815008 779815031
    0x30b0717090a1104150810060e0c03160c02060d0b04060b0a0203030f090a0506010305030a0210020901170603071206050f07020d05041e0515031f0617101a040612 71
    0xb603001d103641c0a010000c098425103080d58456210081c0c590b000040410b580f07445102e4140d4420303840400315801460301e03001041c2c4601070000f2a2060510f041c840e440c1d699000b0035045901c0c1c000b05d004d024420900b800d01c0c0103036240d5006d080107141c4800001042d801d02d10821099403101d90240c03c0445c1c08020215020740d007c41103942c400b01c0500328040a45a2003080b524007401c5410284c01c0d03004981c004010400044000c150512141d800c5822107039001c09514103c1c0f041a8a42c1e0201d103241c08540c1c00041e800040c2ca6112000a06603003c195031001c89031003200b44114102c800b540e0b120200310780315078080d9420350049031620080c006400c4103500546684210b010302507609800410b900c5c2d00c0904694140041c00f404341082302800400d070908545034000360750034450b0340804540c9001900308a90740000704e03606981c820b601144022245220441c002d400c1c02c1c0d00711076403900401d55484200e0341c00b1041841d02e0416640b1864008000d103650003107444420303103904003d0400c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 779817508 1250 779816258 779816263
    0x10605040303050f1b100c0801121b15030c030f02040302060f0d0f090804170f060a020c0a0503070305040e070806240c07140f0d0b010b031e01030b071709 68
    0x1c1d65498100f803036480800310401a45400380c01204458000c241e0311a42c2c1c40000070881d50032032084010180a1410040340071350310780302d09004503150070b0f280400480c00b0991031071301491201d031018113402c04c00340c460340c3c3c1841102040c519200469200c4801080c040e605128012841110010441c140380c21030303000460381c5c81882200904010701190041100c5000d60021082c00c000b41e4082012012a14188031305070010b210b4224036645000529004c001c0100b00340f07501c00850400b03420b5581d03c10340c88000940141410356540d120300b01e501c600141c403c00041030aa4081d88400f5201e0789000007541d0320050042406c0100300c0d03400c1c10f010898686100ca080485058106100031407000350140f00d29004480034824584180400091603c240800301d001c000d03010b45400e148014072000b4400d82c4c43c102d0200509410460b0010850090840d024640200c0c1c40b1003041e6200c03d610f0b000e400c551400b03130402d440c0e0300341d200140002e40d40c010030940b044c03c0d0f510181650300c2c41c1184001c0d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 779818758 1250 779817508 779817517
    0xd141b0414010f1704030306031202010915051e0a020d1b0c06112511040c02060105120c150d18020d11151c0e060f04080706090b090303090c0603010605 67
    0x10b06200c142c0c00c6510115004004040e0410303001e1074820103614050030010090281c2e880306513616040b1013240304495206026046003130b600184e050401480a0800c0301c02800002e14403d401c00312001642050381ea440c0300303a07000f412000005a11242140801c1e4112507500303140030a51185c2c40205d082c00c80e000440e410714203400c00f40024007110032140c0f5003c0e0780304a002d034102c0d0000d40050101180850701c01c144146000b000741c52a4030002d0802d01085070314182031440540e0291004100034a04042001c28000f541002d454140c004080480c0e040c00c030f0340b00840c4540c00301084103401110544142070700c02e09888600720b10000650041034a040d500ca902070800d00324000d034154580c50700c200340d800c02070540140f55030301ca0705441200900386680d81961001c6017000400d210711480024101d0140f0004504c2e01d84a8485a40b01c2480f40c0c003010044601689038207850780032070000503e41c0c0c8030b024604040c584c0d0346088002a820704200c181e9a910805041c00148082680501901d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 779820008 1250 779818758 779818799
    0x6150b07060c08060315041a011e08060709051c050111220b04090c0c0507080c0f0f0f010f030e0105070c02010e0a03080901030b0307030b041a010b071e080d141b04 72
    0x402151142d013400c01d850b00c0c2230b0000c0141c1038021000010101b40a81511030a0031482036034441142c0c41c0c4281c940c960b88103841d0030740040d001030300074070007850010704400c946000e40c510b40310403000d50f55456080d40c0d0b81103591506400086168140d6034030309001000e400450750b480c00c407464200003401c02c0a00a40c040c0401d0316944122200001c1e0081c4491002c140d0030034202c40480c2c5c2d403011102d5940c07a00c2d04116024402441d0049228104620b407000f0b4100c005004002003150360b00111540c00034008038804041d20350703030002141c0b030080c407800e4040d1405940f0341c0b00550040c000504100180c42403d405480100d070200081681c68060b551880024038011540403d50380002c3e02c3c00d100d5400241c00c0042000a000400510700c001c80001d2000000202c81e503030340d41040c1491401400c0b405009610542800c40d04220480203046074244120261801d118500303910324201c4151104812108940c6024010200030f54407045540603d03c1c003226242c00c1c02c006195100c0c8a040fa2603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 779821258 1250 779820008 779820043
    0x1031403041a180d060c021203010f06051c090b06010314070903020f270105040b0111060112061e05180102040617060604080d0206060a0906150c06150b07060c080603 73
    0x2129007003400305200800310340003020443d01c50a18117102000349558607001002d84103200344100d50b03c403101c00751b9040790020f041d20202075103041c005442e43c0d40800b180c14074145400310110300b050180c0c841c100c0268050b00010f1250b1a0600000d82254580c600200c8469080c1080041c83c070b07400504030007a20360640d94400c0e603480d10f82c00704107200106070001c6584115100c0c86030841c204e280403a4101c4100312024004000b0313190040d11031894100e09044180c11000061240079000e003641c62855100c0c03040000d2007598000b500c500142c01c441c104042540350320502c02645581505500d903040e1083c0214507052034110701900d0b0600865851404802140026400da40c4007802e480c02059038000380c5644040c4420029220401114401e1144844400201c1d506905100320030660360901805800c02200302001d85030402d41020448100e0303121502d4404248009840034002c183d444085500c4140314034046040d078901d043c4040802050500300125542d00044100c440c3e00308452 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 779822508 1250 779821258 779821267
    0x6090b1c050f03120f0f0402060a0311041a0a03050f101a070501022a0d210b10030605120a230f01060f080f0c060a050903010605130501031403041a 65
    0xd2850401c09800c2800d0302c540404070b032400c070805190032883c0c0b0070322548200b4001981c4003c910900120103480203504100705002c50300d615402640b005a00d02400920641066030705c1003508242c0c0c1c0103c003415081400415468044c43d01402060740045410005120502c4c10142c003e40346c0c0c0c1c0501c82e2404a4411504003074154100d0000c81c0c481541040095548070085841002a0418620410240d407007400381112101e10124001084050954901160080c103400313180d0014140000c518505179035006542e8160f40f007089000c030580d47c940f000b0035403a181904000c1b41d503489a100700c00a8016484210016600e4000c121340308800c80500300c90510100141c9150030b070b01c0e02000300700c1d6203081404580c070048200001c044030f0114089840d0640c011b11080c0e1182c900c01c228540200c0b080c8203096072540070b00c014007000b0002500004100d0307550000a80701d410f1040d400c2803110b2f650401130050040c00115907084040c110020340c134040c90481107800c8400b60a140001e090f40118 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 779823758 1250 779822508 779822513
    0xe1303271e0e0f1515120c03040203121305090402010e0301050a0b01030f090209060d14101406030f0a110429010e06040b1e09030f0c0901050f03210903030304060c0306090b1c 77
    0x4080c0d41901007000c2d0041840d10302200450041d901c00c0c9c41c02d0344680b041d800000b00c80c600442c11601100078020110760028903041c10700886900140c8201d0500c400c8a6100f075454500f4031800344500c25801c03000c02c0305100c2100140860b070703c80c0e4044900600b4000c03c4005030f20740c1c820300c58008070280c03092880c5848505000c00014980d40ca2003004c4e0040c0e8064100b8074009030170003114594a00c035014440c0e243e4404051707079424441a840340700d8000b10b1103c404206540540303401441c002d803004c10035000561110031040170361210903010140d01101c00809503405641c0d145c5c016000d03110103140c9418005108003a004580e4481e01030b00d411050307482a200a8000da0b0714a08019044544140c10318081a807600c040d50f6045004103950000001c15281480885140c0a40500600f005e0705000d038028180741200c40c9080411341c010005200c8944040000b10701c650f025800c0043c400c4110000141524890740c8400341007410036a1340442030383c60b0001e0440d20b080307403040340f14214280d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 779825008 1250 779823758 779823799
    0x120a05041502030316050315040f1d010608070806010f150201061d06040509120d05060a081f0509060c03010504021c020f040e1303271e0e0f15 63
    0x2900841e00c0705400d048401c1c402034000001e14000c8480d101d034a102d105250f1401c03141c6000489020b8036241d1390f00f02c0034105040c19840380808610400740490000035000c2829011324901c0d681000603992128104080740c0300340446009411004003400f52545000d02d45500b01500b070141c0c1c00d041080d0000054214001d50011000786504095440d02d4400103002c401c035204200c503158096800d040000d03503c1d20f070200c0d045012005141c40503040c004007900381c1c80201070003411140c00c180541000f1600000401c0040414419203058520704c041a4011100340c1d000505030601590160083c040caa86254082e2810f484003a03500503102e00128411412240e00310310041443d510004241c100054944020011340b005118056a95129814000441e0441e500090001240301c5101403141c030b61712550060840c8200780c00350307031191503801941c1808425400d022404080945c00c02c0300c0984d20204503840303e10026542001e04e42090004102044000a24440c1144841400104514 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 779826258 1250 779825008 779825017
    0x70e060607140a0b04120807020f060112020a080613051207021806010c1a060f150706050618190c0f020a26030405010b0f190e060103060803070b0403140408120a05 72
    0xc813000c040c141828801c12a21288480200180304100020a00c600000f4000c030603101040040c81c840c1e1a04150403004828401c04aa0000c2c0f00e14001402031000c00c281ca0103a4811a44d03900e24030760380d107016460b048041c145103403040c02c00d00548000d070382d80c030003a0400009840c605590641d11100100c0d40c0700c0c40c443c801400032190000703914140200103030844c81902c06550390f40070004c105041200c00003000080b842501c00412180380010300c60b80151350010005040030b02c142845003200c0048c2803045440140205d5810651a10300700d6034010403414041303e003001c00c544a2240c00094903078402100190102e00c030b03451049400d00c0c00055405091004011072a201e00305480c04602801100d0640c610588003d14004030130b24203200d803e5280000c0700c082e06411850003050304203100c0e0081015042c0340c1d0b9041e001a103c1e0302400200380d102c0c4140c01e003059a1906127809040d611108203614110300040c8001e200340310000801e01400b000c20820961104101141110103125 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 779827508 1250 779826258 779826263
    0x140d1a0a0e0a0f032303010b07061b020a0c05090105030a110a0f030c050301380310020d0f0c08152b050303090c150405040203070c021207030203070e060607140a 71
    0xe8186010900109540f2180306074482d6550b08010101113030b0710203059001d1307803074008000010001007215805a8000300340c610701c0351802056030340482c819140d1803880d84100e107025070042c8045d070382003220000d08400036004c2190050082e5040001095403030920000091142e00001d020b40100d590b0040364a00504080d07100e0f206154991801900d01103441c07040b2400796007005100515640c0758400400c680b00c02c0c02c0c0c0590b0004903010040e5840d40c403400c0701c0d50540103d03041d400d4485814001041003101440000c40c100c181d50100008a5201904e4001001145000d1000000c6680e100030791415080b1259414806000000100e0081800440d40c040b8400041d06003003000c0440a1846a40d5184c143ca004001c3c0c00284a01c0d140d190b0b055903850281084140000d1500b81c0c05150091102d1130252409001540403600d40b00c000244004071350310407a800c008500d41084200054454244040018200140070402c28011550000e10b2107940104174100d002041004090300754 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 779828758 1250 779827508 779827513
    0xf1903271a040e09030a0f0f1e05180906030d031d010603030f0207090513060e0c030703030207080c0301140f040f0b07050706180201020a0303050603012004140d1a0a0e 74
    0x140c0c1c048886065015119a200350039903c000200764860200545080103c1515000d40561041c0c41c1200e481d48040e2058081c45000300f4200c91101d00c08142d82510027240d201c06586040001103405801d0340103803164030410b03e0104001d1b45072000702c0e88070312540d900c0c2000f07c0d00806a600071140c0c140004400e0040790b1801d0000401d041d4440a9001e1301c020507000d031500395444115000070345030101c0c0c81c4c00e05564400350350000500654010a2002000400d4502400f07030382c80064240300c800d40c400d0780103a21001c0c0034030041c2803d0015001d0600201c1c000c00401c7c04821001461580052020304004141000a07060100032240c0f580315542c803c0001c1c84a2a00f8000981240c1207044280c485600d0703c1c08600e01d0780c4c000c2e15070002d801e4058008003034085850390b0880103010014440c0b40c155485400743e00100c042d944028190248403240551202d0400d0b0300030004080305a01584680c1d038112140c0045150074a0f0401484950340700b003105540c4004100c1c000c6c00c2c00040707131055803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 779830008 1250 779828758 779828789
    0x5070818010e03011a130204081f0509030f0f0f040504150306050901150519080d0504030c050109140904051f050a0c0918050901110705030c070504050c160c0b0406020f190327 77
    0x582b02008100e95500c2c100000304034503103c0e2a84144d890203001c402c040b40d0340041129070400e030844000b0301484480141c4441c0f500e5180c1001c281038a07100800b12b41c0c1290380d5401801001300900031541c0c800b401900030009510150f4401c08800d049108050050340070002c102c40f0981e0400301400942000809c440300c51090722001811a030181c4404e03070f207400024001280c1584107625600c200c5a907056002d035000500030400c200094090000caa181c440c076601036000074100c8012142418018000141034600644608281c6542020181c20885143d10502406203840034540300e03404a410001503560b40d911889004090b00c100610b0358103000700b0340d1010843e002006010301c10403841920346c0c070b82d51503080c00103580e820344200e89414010300000d412440c2001e00a801c0780c0c0035000c0c64280d965901f0a00c01c580d4072540243c401030304650150001030317800f0040000c580510498424105400f81c400502c90400040c2c110921408480d803007607911004500e06014200c20381d29601c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 779831258 1250 779830008 779830033
    0x7110607091415030f011a04030b01030b09070f060512090703020d0b0a020d02040f090c03090816030912051e150103030815030d030506040b090103050c06090105070818010e03011a13020408 83
    0x1032140c01d1040300c00c60702c1030703000544400300c4e2a0242e2381101c1d404014420747d40d00756561680c90303c2005100707002920540a0004104492241c5800180780b651261655080c00848030310b160036000b0191001039114610810050300c070340d1b81d1b4034081ea40214550700c40e0b03106c8040c00e4001c0c0c45441504800b0718004240414245207411401040b00c84800b001c0116200100d015026202c516038060586041406400c40c403003503021000b120700e446454115203450300c401c03c83c030141581d01030540c0c140d84058442c203800040015a082e91030b0100c40140ba070341e00c00100801c171040e41404010200007000011811007040300c008a84150801000d0300c16032200e500703005009240485600b13225900340b0482481074180105042d0580780c001300a481c104140405003e07066001000060402204009502c0410302140150820303011171070031000d6802008000508030343d0b90103075451299150100000104050040400b20f0b8082070360941e03441c000c001030b0f1800038020b42c0e0040304030340541843d6420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 779832508 1250 779831258 779831281
    0x9191d070e012301140f0705030f0d060b161101092d050d020d060203040f0c080604030201140606121512010209040c030e0316020a090f050711060709141503 69
    0x58580210b0700c83d5078089803070010606001414040790106000210304200d0004200052000118850205107411a40e9a409286502c0381070365102c42a000300b0101645101c0740910070060170752130344041c00c00030507140c0c00200c00c045070300081c02d1540700400441c00340d002e1080702c1d0040c40300d5241042c0d00e000720402c030f0350250051038134007103550040030b404a118a0003491180b50325801428542c040030071940c901c0001d5002410641d2031070740c0c803291140043c2d2420510006401d072038000d8209070038140350190a50341ea280d541401d442c80881088256129a003d807907294450210702000c40e201c1e040b03504c040b2108011401d4021628801e4030188200540013881d00a6054404101e0712602081c2101202d4440c1403280d000d81041003942c102404680070924103030b000034544a8215079036400c42c81141c141340e40c2c0440d690385401c10081c003990811107121034180362801406942ca032525000b07029400e6805a40020a08554100c4503600c0e2001711884042d004568a6a20700b002540c03040d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 779833758 1250 779832508 779832511
    0x303091f0605060d410c040803130e160503040204150e09161409070f090503030d1a0405060a06110a12020c091806060d03050c0706051809191d070e 65
    0x22000340d1000d1401744501e0911300800c1c03412414031200ca2944c00440188680d5034000c0c240d84810001800003180303052043c401801c411101c0c4003900300c0e50b440c0c5480214865402000d04100e031401042650301d0640020407241d00c65070407540095002004907240150b44096080022600c0417582000616400040c4030301c98214450020442c1640c1c80341d20003204140b40c40020713040300021020441d228010104c02c1c405140c0c50411520142c1c41d000842d00e541c0000880e01140307510b4550203400b407405a4030042c03294009481c01e02c4603150807000304100108600c204810000c2c41c801410210905004506050307a010029800a04950400a50b00d2003e900c0b01441800f0000c00301d00035112010f407100e80c4070402000341001d40d07141d20801800d0014841b080c1d081c01070800c28152081d1007030100ea0003030080c6803a410b80380c0e0140112800c501d2720355070760140601401403d001d80810b2141031740810408404002c50101e009100902d4102d00701070010040780b00700c02d4089450b11a004240703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 779835008 1250 779833758 779833781
    0xe070507141b030c0d0206090103230c18240a140408030405030723040c050f0a02010f050a0c020a0b0a090b0906090d0504030308151516020a06020303091f0605060d 72
    0x160114021a410000305c2c4c1c40e1144000c1d03206c1403c002c103040d154001d0308000340f10308181030802e084002004060440348001c0301c082c20119000101030403245914070035910095011f8500b0b4603e84019440b4803082c028408034183d0240000c5007010801d403055107d001a030721a60f0300075488070b40c2c41c03000580c0c030780081c02694402c0c01010000708121807000b0b140c140c0c0000c1c4203032910801d11410103000052200c0111802007102c20800c1040341030340700d00104900541c6500000b9400b801e62818000c4450103003517141401c0c101a1f00015581e030000e8581d50141d00f02d00d095103ea01c03401c01010051108902c01030101d13605108210708034602140c0544100e40050540300000804042100c01d4851800001d000c500c140010403808116191200e00090015000352a00180c1000c240540e4101d82c0746003c030b9808940d4441c0860030312410307203401450240003c50940c00e00c0043c19440d030343c6541c0c03003000346513042803445034055440d008140102005804c00340d44105180721680500404502ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 779836258 1250 779835008 779835013
    0x210309060e0c0a030f02011b0f020f010219080f04030611040602060a0207080a03020306010e040e0a0c0807030b0f091c0e0f0d2f1002030a02070905010e070507141b03 73
    0x515a4201c0c010809404100000304944800c50030355941c0e03000b012082d0016030400c0024405040d2200b0b0040c80c08254030b0184020042040300f510400580302100c50b401130454000c416884d0021040c1503011202941c016030254440c0d84c2510014900e010b16840070309001e041c2150145501e826400030300a55074507a00740d821701e58890098405070b2156481c010000c10301000b040d65014400d034040c5410030014034002c441d10085030000750540d1030f03181c6c040790660080c070304401c01c215001900000a0030200058048140b45443e520b01d402c030010b00024006031342c207001135500a000d11a900c202103800c00030f00a5603503500001003403d1842c55015000790720514000d81145410204c1c1c9000c15484038200380c0040811034240303221f50611701c5e0164010081c440300c036903070b0341ca5400318401da1360f41d60f00a5440741d0b08110b000307182c0303a22039000082143c031745401440322180c5c000f000c03503000303141d8100542d848145143c45010441c0b5001c0440700d6000d000400c0a000b003a661141410b480c04904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 779837508 1250 779836258 779836271
    0xd060914190209040f06050f06010e1503010519120507090b010c2402040806040807030806060304410105070f020c01020613020a03080d090203061e070c21030906 71
    0x40281da0708100c58000d50519005900c40c40189881d4500a030712a200e0b0800412031042c5544100503540b0a488201910200d44c00300079555900c4443c8446a840440d0700300c2031100d922907800d80b244418028140960500ca007034080303280f4442d081c600100102044a01c08102c02c0c101b01e51107454901401030071608242480d1055031040c0850100190080317004502c0544900c0c65141c0b030b040700800d4a07045a000d203c00110340100b803241c14491070183c1d4609691306014a001480b15200414451203840e041c418000407442250b81200500c117114422410103a03c4e11110f1a0100c08400b080100d00658800c1c000c0c042e0113400807400303100c3c0d0744c40c1c0c2c0c442c2490801c0300366101c088808203240168000d40005242c045101d000748042400035001096880e2240c8801c1072640c0300140c1c1d5030003207031545410011414100305e1341c1e5001084100a042c3e000c00b094036000040c40c082d02b50000c02c000307401000c051209100b514400e1400c0d02901c0c29050040030710107070180c0614042504c2e05440c20300d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 779838758 1250 779837508 779837543
    0x150414060f03180705031002030402190b07150b060301060c0506060a080d050f0d2c0d0c0b18190b01150c12021504030e04050a0b1005180d0609 63
    0x40c2558081c0c0d921908407411541c5119407a40c01040c4041c07074605a1094840010781d0307450a02002d50f0325205404051b0386d9291900601089002e180c0ba0300001106004c8100011300700710040d207a2291703008002012404803012007101812041450300c2d80324074004000142d0582080c2144a502c5c070032802e40c1c0c3d165446a003004503100046c8942074850300030a40b250780035807081d0700900c2c1d41c5148d10f0100d405e001400c4401000c5070103c1009507443c03000100d000040d468040160400030b0b182100510081c200048020501448100f0080c9070000400104489010170300241c1f03094040042110f030540700801c1c481e203519010b541c0c141c03034560a40001046001c40e054842500d2707030741500c0e9803008100540e650f014074a4000c48001c218010815443e0641d584015401d00a40c007960702c07004640514802c10040700c00c013a00c03005a2514040c0b103420340380c403a0040c00c030100140c1e00708640c5480b94500f28030303424000500303600d1740700c90254504c800f00500e950008290b0b9000f0003080c2044460740c07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 779840008 1250 779838758 779838769
    0x6060206090610050d08040305100606081b040b18030f011b031a0d050723040c03020333060409020705150f010e0a0f05151903020f0d0f02150414 64
    0x140e4041c03451011800d0f0501c60350401601c0a0340c1a48581040d034038081c0c2c1c0b41c417207605010081400d284d6107078803035104000481c3d1100500d030700aa45011994104070903c002c00107107218a00c154603034500e0110f43c5583c00031041c00386003070203c0003030b050310099480510128001c00745071070108a0121144d00c18446180300b031203039000351407101d540e016202e00818100042c414030b0302e804071014410120040b50b80351844c010342e502c141c45404d075851400300c1c103001c20007a0740717070711900b40c04252041c0100503501c4200c0c01da900029004011901c100c1c10103080242d0220009032205400610002d0006240c0e0b2280e4002c000301ca00036415100b0030031159000340c054910540e8003d400403082c0d00148001c0b4103500406070400c002c0900019500f2117440344400362041120780800d0f1100d41c514800781ca0070b00008041002000f40348100d400d50550f8005021000ccc1c607294140243c5055080b4070401a00c022007002c01c6800514010f800c040154031182c0d1030b40b1a0140e140091654884140c250400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 779841258 1250 779840008 779840011
    0x2070603020f120411060d090b010510020615060f070312060b0702130203070302070f120207090b151819140102030405100318080a0207061409011b03030b060d060602060906 76
    0x1500e00207190400c1c20214442e102d20203007080d14444c0e81d02c0c0700043d42c1d0f9031b400001c2201800704440800e4050090426505814059121b64021a0a6210038030b5143c3e02094055200203190444182d402142c00820180d0242d03036514140038200103640300900d074105120200005041c0403e0201686545225400c3c1c014180020341182c1150034030090480345802861b40300150703180041c1044943d84410351405d0785030700c06803042c042d940b0b4440c12465050001d4405046501d105001d5241d0110200b03102c1c2250040041c144080413400070501c0810307080e01982054000e00c004400d4140b020844201801440b8034140c81140c9405001d265001000395001c98600034040000e41016990650107800c1d050012401c0741c8082040c0da0024040c00054030f9205da050b03000b803004605008000d00300d80d85030041c030441c9840074441d41c80d03d42c0c3c0c000302650316911521445882648a0f00d8260044c5c547d910401d030b4040c2000c0394244030220140d00070780484445508960b680e41f1740b400101e459110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 779842508 1250 779841258 779841277
    0x180307050303041410180603020c0c042a02031201170d020d050909060d020a08011e0b0a061808070306141608010302040b012a110a0b0d1e02070c05010207060302 71
    0xc1100010391380e80380a800358040b02d61142072250440c13402542c00f048042543c0c0207000400e5000c149450220803c101d141c09090342581c0030444081c0040450070303100e40c0c3c21820824103042c2180d41200078428000d407242c00384100e0f040140d95842e0b0040f45038030440290b20042c40d00c100e85a5841452001901906001c26921842e14062402003403141d6031900034112074000e000a844000181c844000810050490000008407015901403d0081d161a41200540141031200c0000ba6588000c2400704442543c01e1281d80500801c182c01c00440b82d9500c00c83c1d203401000310010500c00560401c0d06840c80210815420303a807100240821062048240000900c0c404010710050606502c090311a5105043c081381140b019400c4a038112132120004040012040c14441000401040401b800f2802c0b6403030014942064070840305030141c02c0c0a1000d0640700c0140591010010780d0716440607842c0c0c64107554811075130901e407010744514420140140300304080051240c1c03103442138814084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 779843758 1250 779842508 779842529
    0xf0c020d02070e1b0c03070507050411040b090405040c12030e0112141803040b07060b0a06051c051003080a0c030f05090102030912190b04061a0a06030c0e0618030705030304 76
    0x2241c00d06002991078844403800140f04c810444d00800ea54104043d1038224820340040501c03d092000384800d9170350b10300d8111010041800140104011442a1003c8460a4a0010b119030321400c102030360480c981e0103008000d440c01c10140a00d44d0080c40280c0c030b05001c1e290580b50000114603007003241d06075000c52982481040104941081c0c83c945050000c0c0c0840840782040e07210035801c91658002c003006c0b130341d440c2e480000794524108600390700003c01490808509042e1200b203407003076440800000200950b95030000a00901d000b031802c1024640010701d030350310707013103503000207051000401c9090340801c0c04800244107087c071420840c1e1050106038042c5080c01008800d000c0c811602c0b0a0f1041c2d24001c481d01c000007000800200284a4060317040350340d29040c107041142c00c403000c9584880b48400590800445900c0341c6504e00c045807001e00c0d00088150340704604075401e890041d807007980843d00203940590045440e0442c0703c009022019113492030341c0c0b00101341d030720300c42d0348512800e42d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 779845008 1250 779843758 779843761
    0x90601140f100f0c0606060207050307090203042a261e12180d0305091008040b0f0702030d0903020f0705030604120f11070e010612090b0a0b040e010f0c020d02070e 72
    0xc030311072110f0030032054a42c1044014000e00f0350b500d109481540d046440140d012440c200080e00d005c1084d60f004281d024801c503e50305160300c505045504044214800d8052158954a80d5500e0900d110040c0310908024841d54828098180a01180040ca49003480f0760502c0d21440c0040128410340d40b54058020100140c8000352900300342c00101c1510018443c0802d00c8155172904c00008004500c41d9480aa0310400402004a02c0b02e0b04c1505030304001c0740000308070001d41c41c07420035034010005040986181c0d852040807461752080340100014203082201d841c08158000459840c003000480c10390b060b1a840308141a0780346c40484002d0149a2404200c80129005082c0d6010310304141c9018031186d000d1907130003494048180d0043c2000d4198138010080c0030741c020029154054140018082c5a45039100e00b1070507100546104000382c2c1d121506911562250701540306a105540240800c0204c003000d09c005200300c0b107000e8050b018184c00d0f010407610101d042d0f402d8500c1c20300d01d00300d907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 779846258 1250 779845008 779845039
    0x902030a2a0f08060613182301060c11060a031506030c0e09060a0305060f0906070509220222080d0e010206010311060708070b1501090f03030c0f0b090601140f 70
    0x1d03000c000e030607036402503020046020490b029843c136202030030387c400e03540d045a51a42d00b0b900032243d42510750188015000d001321214180600994111161458110341c225440d007400000441400c90f01a8001d01c0000c6004c2901d8141d04210140c111340610f14481550307400054040d9405401070700005807039411080b02501d04400c441e074100ca400780801c00c140d1b45a94827545010307000c2d03602140b030210420821030b00c1074082100d20b6000d40340e481d050341400c07002c602140041050404805080d0719010554040c95170700d50540301421020551381026003410403000f0003901080c001d850b003602548644140f140d0182090f89403844040e401020399a1031504c50240451103186000d50143c801c10016001c80e0610019042c0c1d00e0080d0604003030350404081048610169841c0345041c441424801c100c0000446a001c00710b03170305070805c403e0240f0903140c00f94103400d40000051041c140742c01405501100020700c0382c1650701c5d06103220320507040042080b01035030a10030300d241e201c014018110707507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 779847508 1250 779846258 779846267
    0xb060414060c01020903070806040501240e04032c01080604090b060d06060503011b030b0a0e011a07080a0c03140313080f1614160f0501030b06040902030a2a0f 70
    0x8020381c0d620b00050801c0f014200003428052a81c1c000007076540080c2c00e000c1400401c0c86848074101e030b5681c160000707441c1c1d0255401c0400040c41030076100c2802d240081c050500030000ba1454520281c8d041484442d83d24061164a510320741c201c0c00100024001840c500b00343c4641c100da0b41c0c0119480302182e07180005c110205d508940b04580305600d0303400000c4c40751800d00030140848103441070b00910b2800500c000381141c03030a080d0184a4a9142020014108101412030554410600c3c1a440c0f0190f00e00a8480f0311440700300605034030001030000c440941c02020380751a18401e0355091403468900c03c44200500040c1c690000b1a6005c0c20040009a060310003004ea030000150040e0800e80240b805c40d0714072104400c02c5c4c07a9405516202040c0800c140913a801c0c6007202103008031a01c0c02d14181004407482402540c1c107140c0d403031181082e2642c44200780c600400e45c14005540d24500948c0d810090801201180200900c5141001c02009480c2000360105602c0d602c400d030501e070000341200e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 779848758 1250 779847508 779847517
    0x9071a030a110705010603060212060d021f09030b0a05010e07020a03090e040c030b0901050f061005090409030512040302030405031b0f130b0604170d0215070503061504080a0201030b06041406 84
    0x40c2c2e400c00802c40000010420f0040e10011405000700603100e81d10f04600711a044c40003010603200e000c00c61144001641c90303a180b2003521000003080c030b80c401c03446582641c1c00d0b0030540024200091603410400b00780341940003d03040c0c900090307158600b42c840711816603071901d4044d0001c0100c0d000344401c1c000b0300e19204207076a0250080310f4a2201d16640d0300c45e680e89030741c2500c01301d0003a51140b0403c09820b5080011541000007640d4554400841c24401000d07406816080b1f80709a869800e800149032013481030300e00e6403185408417442400d00d850023070741c1e941c000d110307441c001c4c024560044803005134420143d10150001d042845c04146c09001c0264854080b4240042a6500e0a01e40e42c680c031001e004c0d2018020b104024000d52088020f881e2030030688840c2c86046502007403850755252002c02e040c03a00301503a03080c155242c6e01c3d0302001418080311288919046040880d0000d42488006140340d0854003e890410250f00003405020744c510035406100300c411a203000f850242d007007a1b0002e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 779850008 1250 779848758 779848781
    0x60a08070b040b0a18062007052428110c090708090f030c0d140c070e0403120c0305070e0315070c1e0c0519060914130603030809071a030a 61
    0x1c45100e5503c0381d045aa45151b81288002504500c410041280285014282d0708000d40050a28a01d030100281c0d812103601340d0b12120311080200010409542d0064546155885000fa900380314100b01c000f84504c00c25661100003180507100205060020502e103900d500d0191151802c0d585100c3c054030401c102521003542440744100c90a1032240174000307018985000030290400600310351008000007074141c054641c0f040300300010300b501d850002e070201c00c44849181000b4280c5d19400d0030784115503a69402500389041c4040c4200007039056100c40c0c0720308401d0322381401c9180c1010074180d03a2510016841c80d50004035010a80ba18000c0010040c0f90f80704400000c414546d21618030302c07042024408403403d1440e9081407240349040c000c0300d0040c3d03045080800f80503107403050080210314203101c5c036040d0707084902003081c843e04c1740182c645104105560501c6180d40d00d14004011030002c86007102940120320022611040c298001c1071008901e4011608644841d4030340c100801429429 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 779851258 1250 779850008 779850017
    0x21804020a110703080a110c0607110604170a060c0219110f04020c0c10020a170a030b1c0209100e16031d010608010f09050a0308150d060203060a08070b040b0a 70
    0x102d40c1d5036000300b007100701031440b400c4580e46a1200b00006030111a03182c9031500c41e5000200c81d0015900e8900070780d000036401502c400056400034000c102e40b0b110700d800400341114043c180800030314000501182c10380c070540d070400c103d1500b0b100c100d860302844100d881401000782801004a41da160108000c440f0013081842e4410b640400103040ba44159800c03202608850300c0c1c804580b40c00440031203070122500140100d04c1031079481d1b03201869560300001041c0c801141c1c10401c6407003a4000710303c1000140641c040080c1c101c03540d03031000c010240d00300c0c400c0f0510000102d4401c0102c51480031250880c000d02801d449040381d4080400300002d1039420183d030780498034641d030704455403440d422070803100010300d036403e1107070304d50941e10704030171981b0746508181c40c0000041c00014203640c41ea80500d41312809849188503413039800b20244030103612400ca03003d1102800307143e40c011400344e601119015505903545000c0d64440350340384600c10043d1014401000803540100081120348402d292 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 779852508 1250 779851258 779851277
    0xb0f07020102041203030911010e010c06020c030403060609331a0c073803010e0703060b03090d030e0105282703030e010e0c01051c14040203070603021804020a 70
    0x7007103588444070080903170009484184010034841c804498443c2a0001c2c641005001d49000020341b08031100000240350350340c00074550380f900c00c0038001e94000d1684400b06101e03541d614001c500190805080e4a6080b0b0710740c8141e0351a40070048504d0800346103803078840c04400d2900c007800315111041030210342e03507840810820040e10010b02484001d05920003845620b20851401541400000c4882d10552646060707044400e03c807078000d481c110303070401452007070644d0ba800045001e080700e80e011142040d40482031200961000c1011103000c9110750b0704101007180c050b83c1500740c8070140d50452114500c042001c580010340046002490258070300440c92009a03100e041c400c1503d10311900d2007040c00200c48e41010341c540100340c0c40030500c4000380111911424855240c00c86113082078140100001c0903454501700d80c01c12840c0340e0b11a541004420181144842401011031b01248a805a8880420030324003901c03c0c0e40710540ca0310b4440c80000301d8402484020b51010410b0b5090002044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 779853758 1250 779852508 779852519
    0x51504020112150b120f130503042c07091e050f060a17040501020304030e060a0e1002070b0c010f0c0903050a020409080d0912020c1206041b0f08010c09120b0f0702010204 75
    0x10000c144445800803442014603146c03203866030344400940b400280350301c842c403883c0104d1800011356091320580310807000752000c510031040b024413002016100b4560134608204074940c01c0a5154100d812962500d942e80641d001042000701d068015030368000c0c2c41082c0c02d20700c0c0c10310202030507801c2002c0c00c28800e04480e640e0f850b00e14010895046506a4000003000f040603841a80c250350352005580541c1040040280a803180c1007403c011402200019042080341c0d10800240d00208610b8034000c0c1c0d5004580e240c0c501030401080c0b18554a82000440301403a031107841a60200c0c0d400038050403a0b0703902a82000080d1403402c0302901c403c641031110592000d82c91064601701481740300c582c058103ca10401070709109801454920a140155044101c0a00401e40c29801039000c50001e0902c540810105419240380d00145409103514002140c458015841510100b0203529444060755445030040d1005020010081961040d800851000c00b06602141e411902c2c1c2e0002500342602c65 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 779855008 1250 779853758 779853779
    0xf0d0204080f030a0207171c120f05100b03010e0c070c0e07180e010803040306050405150f0a060f120809030a0818130c0507030f030902060706060305150402011215 72
    0x91900c030070b0704002a8107881c4c40e01045440b00902032003002c0c07151918104459505e8000740ca0100490ba0004a420b41185114131914a007100308500e04100e004544440740c4010701b000c0301c80c052076842c0704070040b501518400c02d41e41202c0c1d07a9146146141e40c2d01301c5035211600301040803a41d40600c4940031a2011a0095652060640c0e0344d0300c145042800e401054600e0b0650f200070030081070003006000e490f50100c1142d05803900800701017041d0321176150840c5842c08044c4c00b1031800d45031009100351111320890290061106003410b20440d030b151032414954040c0e034418121414401c06489000410b0341c40078004000c4000c00b900c580904645414860794000b0118041c5160030300805109498801c1d66031070308282003076081140010208001e8024400c604000e401d1084400e20011002d21a4010350100c83c0e000c0e0403ea11540300c0d10380075000e02601d0008880034080c2044c40381003003182c10350045c41641c0580d14028484015050600100290005083c603140c10810102c0c208015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 779856115 1107 779855008 779855023
    0xa0b040b0612220f0b220c06141b060603060901050906060f010c050d230301080604031103040f140a060c0b01050931020103060b040b0418020408012a0e01050f0d020408 74
    0x90109180000e014040ac0c40b070341403441e007a03040031514010500500844041c0c00715027a0303868003e002c2b402d96404a4030040c05900220000d2080d00e449000024074144c1030525158100c8981c48080c11f00c08c09000c514003103407008000b02c0c00042c070405008400e9000e520002d0940d410f0080d9207440d800c001e08007808118034a403011055450a100f21802042880102e14a5590f50300c5050343d42c200c80d41c0f495101c0c00d4051390000c0c1c1e641c050205161410341c0a15001103584c200301c100880310801808422a00d840318000f085444a03a200002c80c3e044014150400c1c0c4038035100040036124150005d1190304070901c01004801001015501030707461b80281c00c500045407045c100024000c99026020325800d004d00c00c498081c01c010240d9042103514001305038259000c0e019150310040360409030004d0400c000d0b50424034250341c0039000482c03c40d0380142c80d2903a1600524501104c = true := by decide +kernel

theorem cover : BRFrame.Cov 779676258 779856115 := by
  have h0 := BRFrame.cov_init 779676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 779676258 ≤ n) (h2 : n < 779856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
