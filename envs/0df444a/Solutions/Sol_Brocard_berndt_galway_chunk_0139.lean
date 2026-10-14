-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0139
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:03:48.488002+00:00
-- url     : https://prove2.me/submissions/c7e9c9ba-b637-4a6c-810d-6ca2ec317d6a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 24820149 ≤ n < 25000006 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 24821399 1250 24820149 24820163
    0x5030901142809170a020a08130501170f011202061306171e040201030902030a17031512030307030b030f030c01020a11061314010b0d1103060609040503030604090804050904 76
    0x1c078a00840000303190b00800203107040e82404141c00204641a1940040402d00300e41c460f034807091004260710b428441c02d4010240080020462858800381201005541c000d07610407171038080004804140c0e80d0240c0d159540c601c0c81c04010000800ca11803401403540c4041d00c0d190074459070380881d214103045680500040359030350300d0201240c025001c1003948241d0100d056813420a0545154001c1e4000900090500d070750742c0350040540d50704201004006a100810600c065403401c410040c503003059418003010362062003040301070b1a0164090111407980001582103031748000d4110040e01ea01c1136526014082ca5401700c40c3c1640510061800100c490009a40c44d80d101d64000c010350b61610750300c076a03900030340140907401644019800c0c4ca16041703801e800051403186509801400800212544500549111010031000a8000e43d00c1a02207098400c142c2c0d8003000e006004a0440b8014020b4100700001903d41c60158455107a042c0949511401c017a1500040b44640c10240d5003a40c0d80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 24822649 1250 24821399 24821431
    0xf0f0501020105070c0308040b0c042105070603060311090604020403050f1506040c020c04050a0612031e03020f040e0a09120512011502031804090c060503011409010b09010503090114 80
    0x40d40c09000d80750b04403600d40317083c0402c81d005440c010a084005803000346a0904440403620210102e0182c4000e40307020b00d8403620708899500840c1c02c03050401000c503914050000002011030103445030300102c0390002c49184100381c1250801c100d5000040040d80d12a078288804408100b04011544680c011600100440440090707441ca042c00001c24061050303091000804155a001c43c04180c41c42d010703a4040b0301c1b0b40b85c6000c404040d042d9908502c42d0301842e8200c8106050b480743c8a11010f0310191b401c8000c80f801314508400341d1140d00701586045004000c10407003400b88801150788003086c207500040e100415520407c0c1c525030001044005440401c00b0044506114510340c0104151010780582845840d4080d4490142e4281d42d00c014048030301c22031702c42d2103d41000c48030a901410109025443f000c0260168100f03005814141701d00362100400d40c01c0503081241038480d0314030b010b41401c161900450b00c0341e2005000100b075540364020001d110b00003400103030069030012002000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 24823899 1250 24822649 24822659
    0x10608090319030b0112320601050913140a06051e0f010e041b020f0f03040308040306050a1d0c0117040b010303080907030c090c030506041a040f060f0f 67
    0x20a04090405034507604100700000039500d44408690018080e4180070a0403c11940140c1d002d490844840c00050300703020815600c03142503101c0d51196070201046080c144001007807030840d03c40843d09240811001c00950001d46048415030201318052203020410080b5005200280d6809440c1502802e444180038007107854901c01e2600401190601845009070002c00030350440031410200d814483c0303844014001c0d45481c1c105100d03100340c06a19210a01d23100000942c3d030408991402881e0044c1c0e80c0c80d45049a02000302c0b0103d0342c0001a00d07003400c0c21038442c1002084041c001c0041540ea03880f602c0c19048a0f0265119248070f01c2c800382c403040d800e0000141c04120071045100c025401c950030040002c01c00400641074a81600d0f011030b40c0d07620340d600e80d864581030b500080e081941084c0000f54002080d0400d0a40083c156401e2241e61106d50a002c181c0c0d1000f00810151f01c410f401868103400e250380b0038502034040400124110390350b03000605a4a4160704003294121443c141800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 24825149 1250 24823899 24823907
    0x10303030605090906010b16020307030b060f010903150c090504050a0903080108120d020702030a1b03050c060403080d0c0912080702100813060c0507150b03060a050106050a050c01090b0f0106 84
    0x8000c1c41c2c151444005442e21500c0d054445a050003500440e01001c16208101000c4006030100795501904840703200341c0303078208010040d1003114608e100c1c41050800c40c045501c0b0304020300413280c0c002c88035045245001ca90704081c06104080c44100400710000041d00d03600d500690b40078075007250000500d800305042c02080f9040581150040307603c43e0302035180340c4544034115407161951032070058030780712207100103400c0030300307414024000441507154503203d074548101a030200c910904c03c8400d440e500000b2300c80180174611000c0d101460901c01101e60708a55006280c41480341d160003458030b5103416408c2105801000241d59103200810042d04600f8420004540d46200d03040180c401c1c54104e4000d10b040c12080310090841d41c071003202c810340c02d0283c07081d1030540303920501e03142c000300e48450f0440040c6819104640308c0d100d00001706246080b184201c5058800a541c1c6518010b51000291820341c0309005c8005550750743c1d00d000010408000c0014044d1103240d04280c0a5450900000c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 24826399 1250 24825149 24825161
    0xc0c031101030c1b03050d06090519051b09010e1503271204030f050a06060905041a060105030601031d010608070f0911070b040201030b10020c0310090b01030b181501030303 76
    0x1606102e120551032111900c16000d0141c190b6043c0b501b50342e00c0c14403d5821000d05015030105103d0b41c140070900502100b451041c501030710a00504101c00d40d18500d12001c1c1030418604070b10110b030104040c2403554400e4450301c01580c000317414045050111036105060307a108562507408002036000203031140992403900c1c0f8020600400906061031340c1d200300e040e6031007681b0001f003d52070101140e10030050140948040150052010400316555480d0f440103030104a800b100c80c24420031644010440c02d52005020710b00694805003159220001540108504055525008070313100caa165641d10034003542c3d001e028640c01801400e89050b0390b852403d15a42c01100e034041c2070029560402d00354209442e159904614001d400b5101e40c00143c2c01495288680c540184001a10100058001904d002141c1d02503040345d01100d40b1042c403900b2540a6900101105440001040840e90100306280c10600d10300c000701e01c60b100b1042c0a407509804502c3c0d1032043c801a401042815010f202d05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 24827649 1250 24826399 24826421
    0x30c030b0307150804050f0d0f0906080712050603070909060204090b0111030d1a060a08010510090f050402071106070b100b040311040905030915120a060315020a0c0c03110103 77
    0x100038040c14641e11901110180c1e0000042000744e20005091282c100094181d0f03000c05400e0b9601d034050418028850440c044c501d10120313001a00c0000c4044c45484214070501c2c140d070751248601c003200f0b607407000341c4005400700764144169000465840000c0c402c03800741e0351007a0350040c0c1d82c1e483c0000b418140e4070800c40c0107050080e46c04c1c1c070710554000802194a0f11180480000c0c1095202250100301103940c40d4140d0004000f25012041c40e4000f11014140c03101210540c900101c400c008950b441407600030100e8446400310104154240781e0080e1407100e115420184e02c1c0743c0c090b030102d001d0b0380040409807800c10000d000d000064445140d03210140841e4901c0600d020700f1502d8500041c9080d0b038009010700d68480d13506013409001d10644105c01002000d0031041c0c4541031001d2020342208078281c40c245000d0012648024252280c43c00b202d52000045a003044030b0b03081940250040007694013801000d203003181c00503081c1c4407014081c1d886412200f4003085c01d5400101207032800381c54 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 24828899 1250 24827649 24827653
    0x300a030209030705010903021305060a030f0303020d1a15030c0403020603040807060b0f0105220b04080312060303090a03021302090406090212100503071802040305030c07060f020a0c0509060d050d030c030b03 91
    0xc11f00141c1c480e0500a440c4c60750f65980400c5030b454010114030340701140e038000781c071401d80c010f000c00415501d60001c0014120701e4405124161328401c18200380456905420361010800d44803942c030901010196520991102d500d500f001da1301c0c0c01241c501d610848007100c0300b200c0003900d14200a1284503a0826850596090030003002e1480064114420741c2ca0b0b01e4022084801400c80f400007660254001d41403100582d6140c82d81c0c0c0c14165942e0b00400c0400c1d940d04049000941141400002e0700c03200d480041c06410014519000d0104100030041000869602000f500e0440e031100d01552006144002006076984020000d14a58040c050070b6030001410134501001980e50006003001603550141d140001911800034090080c451644014003e0102040d02c00441d074001c2900030858031141c8400c050002412400c0b030b2505261140207083da0041d1406000d1410700d1551a540000090301034a00941c40d51a04d0b864852a031080c800003a4030341c568188401c5e40b60040c60f8501c101a80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 24830149 1250 24828899 24828917
    0x360204030609050f2a0d02100809010c05030402030a0b06150c060a0b0d0b07030209061c0c0e0118140409060504060b0a0b04140904030302040f030c0509010605030702300a03020903070501 82
    0x380c0303008401c1801240160b00800004580c00a071b440c4000310b805294000c2030400205640703034029151500480380074a49521700800d0341140c0d07000e1012a4800c40d030050181c104600c16940765a0b0314200034000d140c001d80036001820b0100f0012008101c1082230310001c240e540340401c2c07507909a41461080902800e40500840b0004900070045c903002a07aa081c056128248031001c12000c1c0a4014040320404802c46020300e04112940712840610103603482e0924201500b0055070800101e018241c2c1000d90018104241003900041c141c080d94002c0010a900c5a65100c95054031425502920a195555003001403460040e46a00092024070b50351400d02d07143c114180008007808102c0c1d0b000340c101100003800c05210340c0c1202d000e80000c2c58000d0783c403038581c00c010076000c055005240c000c01c1045d0002c1081c0340240c0513244545181d6000700072909101d030030395103081e841c024034100030005ea900e143c1e07000044102414150807991b9006071100d402c00c00f0949031071504d502150501c00405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 24831399 1250 24830149 24830173
    0x6040209130504020f0a030f0c0e1905090c0603090c0406050102210d09080a120b0616030c03020f060c07021801140108130c0308030402030c030601360204030609050f 73
    0x400700c403005244407800035259030b950010810500000d9242603200f10311038404000c10000d24907002031a03008103a12141c10340c0740c503c1c0c10001641034070440300c0ca00c20040010510042030b044990301a9036507080e20075100c100008a80f40303400603581c1d50080c0d04100c4034110141843d10400005003000d100410500b10405060000c0540c406c0001c10100c0380001e50384182c3d1505d030414400b45078012542070b0f039207010000003022030080d00c92a010083c1004003003021454108140d400ea42c908500310081c032440b5560036149010010011401e5005820445a400c08148090741c400e8100300d440369602c0203648100088450b40f841c852a0280700003005012881031080a41403106081c28884c0c42c80e119a520300a1220580344000c002540820021040041c268003450146100790210760030600740c10205a16800240213006007419100040000e1402440046584120000504000e055030b0f00321b000680c0d02540058400c203464000020030494200b148620003007101014281c502801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 24832649 1250 24831399 24831409
    0x2060609010611070f0308070b0c04270b09040c0807080f031608040e09070e0a0209090403050d0b0d0503090109080d0f0f090e07110c0109180e0a020d0501050f06040209 74
    0x40c0604010402030b26070f40112031404101a00140c00e44080105c0b020740d60b850400e440e6800480100d03051410b4802081490f50160144c07000d0791031203800341a013009151602c44050208440042d4140c3d21000d50400b01e880b030400c650300076130203040340c2d140e518100b50303800d4039202159110300684d902c140d4804520020110598039170500420200a00b845039081041090050f0b40101c48000114428003035031001c00594042180e005508486c00caa56000b2088200d00904c6070160f08840310380000b07400684200c0007060300400b003a03c001000c00f070b41c0b80031980c12180107004450307590000811080c55a00030103104003c20003040285200e1031064801070080f440c015500041c0100301d2402642039004007040009004140c482c003030686003000d001410b0403010b660244050003181d440c4401c80d44a01d00c0001941c20841482d4400c0e9120a810740041022503500c140c90f006400000005a80c2c0c8036100b18844d0058002040c18101103038441403900313001c3c1c407551155104000311000f5850b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 24833899 1250 24832649 24832651
    0x70e090c0105030105040b03030f0c0d08160804030c080d09030509031605011403090709020f0a0e040c0203040b09031603030f08010806040209041401060506041e050f01080c0f04030510050109050702060609 90
    0x4286d801007803440004010a145000d00c0c12101d07082c01000c02d84590a0340300007000490001d2940e00c98080da11807080341000d03691000352040025842000281c04070340148020803c0038131035920303146001380e40b5040c4022a807100f13004500050000880410398603080090315441c0100740e003505640361811340040e103003908400740a0504440400000c12520040c051040100040082503540c0c0c422480e82e8100b41e07000c0781c000300104158500300703d00c5060034850840100780503002036262904000c1a0300c49600480b42e400d030b25200b0059604141c2d0200e146090095110b80c90790010100c80900103400080160040c4403542c0c03081c0100f01c05170ba00e0700b17109600250495490204c100100c00014050000e07604000d030000800107001802d24226010425605102803150b10400d89650070400305041d00034440d8005030580011651050300040205101144145464a0030380c0d281e0b59241000c03c0000c1500d1000e070303200e0042101d00c881d4043c3d9684000f203880030709042c0c41c0c010300240c01c0e050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 24835149 1250 24833899 24833909
    0x7080106051e21030304030c2913050f0a05010603150203060303040b030601051909090e0c030319050706060b07021531080609030318160302041e0509070e090c01050301 74
    0x201c07030200325500c004003c103060048041c01c196966843c10707050141084840090444d0501c0e10440b89a038420160081046d01d01251216100c4030344072003035600840c0e0b050030b4058031540210a00c1041c444001c00202059501c120000b10703030246541000742d140e0360302c1c489110a8034010010401140d80100883d0181e46022a1041d102c2c0c5a5400417500360040107800c2c2d010314048119403c01035000100c1c24100c6990001c140204000c1c01d22480e203454100500582590040c003817a143c0d40c0340718202008007400307843d00609000f1a078031307018140c80d80342c0d204850a10002034040150b0620005806082502418081c54882100703083c02d590b030b0300001c0c0d010140a44444207500b0706200400c100040c9540e5040f500e407414225a996102e500a662410050204400d0404940004a020322043d400300c030343c04c01024619005e000160012038500c0b0700d0009862100000100144582c0d40110802001045400d05100510030800006449034000d6030210f1005a0640e900501300c2c0c2c1514 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 24836399 1250 24835149 24835159
    0x30807060c05040503030c060105120a0506010e040f050607030e0d03020301030503070f02040204080307050610050a0303050f0a2d03050901180206160602030c0a09060504151b06020c07080106051e 86
    0xe82991000c440d503000d42d13000380740e02d40400201c0241444001810b507058410898410300306a02a00005942e517010f00e20081540d000800100050040120b0702d50380701f401181d0700e1a04001c10781d1600d040280071290380c070103c0c0e41c800030f041d20b68904010503810609079050440c51035040da19080c2e9039024001005013003d1022920320b086485035010384004006880441ea11031030545800b903101d0b80d049810381d0b050700c0d140400141500e40600d01c981101c2c1c15480d224034140c51070581c17101c942c1c800382c0100d09002c2815490702d21703554400c0900e056501d0b45c00140f4170884080d000201070f181c0141118102ea0304000c00c207440728503c4a1000f1216034102c400c2940d80700b6520310010203410800014020038408001c00c01101183e2008286056250307070b9006800d6158942680d60703019600459038135102868481c0070160040c4c031360b00416541701c0c82409010074503603142c0040c1d9100040302c1d440c5801041040041e400c0900444010344003c41702004019200b403010f8621180c0e01159501c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 24837649 1250 24836399 24836411
    0x30f01030506090d080f040201030905030c010b0415050d230d0507030305100b03060d050f01060b03040b0c07030e04020c0a21020705030109022b0b010f051c120311090405090609061003080706 84
    0x58ac000c0e4000c0b400e0300d030b000301907a80300c642c105035582c020006151a81d010310704003010950100c0d4000034240a0f618010501214040310b40c6907480c48450011185400c4140d40c65100e0b602c010030003221100e03004031380c2c42c40d544120514005068580107045501c10803454035090251400400999601250540c3c100380d20000d2418218507142d00c0d070003072100952070b05c0c00225108600c2801188214092100c0d44a5500c821307001a446100c1c14034085e0015411540710001407400c0d8000700001d0040c80704460714217403c2d40f21030120002109050400740d03038080745800c0664061006c5802007204400801c100503403600071403415440000d100302c40f4202c1d851507103410328001c07412902c940d810610400e095038503070340c0345a0306400328050396100b00c10f0810145104004904501ca000d82d0007070b40076584800b445426805000c0d80001e05c11081004d0140300060744880c441c0a00c41c42c141e800400c240d040c0380c042d05040590107000220f58102c3c401050010850607022240c0c9241c1c400b100240c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 24838899 1250 24837649 24837653
    0xe06090f0111011509020310050303030108101109120105090601080c0303090d03020115080a0203060109020a1e050405031614100518010513030b0601030f021303020607080906030f01030506090d080f04 88
    0x4040c2c1c0048661201401300380443c2d00078250780910b2080c0980b4404e140515129001c050b50382c0000d200e02c01442d80700c884840c0456180380c201401207044207900505050501e0001014030000780358544090395507808020f2045002c10a290060104030040c0c0b400101202c0801e440340f20b4144868000c03092004c1c928101341c401d50001c1003020507126404003142d281c074150390300c034002018241e00c179106d13810002c64070305140d100710b070102c1510303031206648194500341301d0704601c00c500e8080081c00414400091692000d0007038110780108150921280d50500c564080b03102d0030b400015016010041e88038100c2078011080b510907000e2400705003107401031a001200e0314480e9581408008601031000801c1000c94081c26010301401d880a000c1d5103580300500c412406a03001c060340d0701041541c01c00c058100100241000c1e0302a82509140140f0000804d5040e40151031000b550300545004000703003c01440040d8110901d10040e150070106d04200411126000d000392014040d06404981 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 24840149 1250 24838899 24838901
    0x50d09020a05030d02030309011505090a090327050406080106030b0609040f0c0312021009020a14130603050606010207090b010906110c1e01030605010507021c02011107150e06090f011101 82
    0xb45002402c88004034890b02c002500d0740c00c2652000c0c103a40c00c100010301e45980000740780c0f081e1040900b144815565082d01c1c5400382240321816000d0203140ca035001c0304004450f8001d0603180412103000b00c000c0c900320030720088644580c040b00c600c0c0d15041040c00010540f440c4940c00910440301218252900d01f41150159410310000701200c0250500008000248160000c5c41c8901e400b41c40a403c82e50444100341c0b601924001e511840c0714405109418011000c05003442015040d44000e51022407000c045482e00d42080d01c0f42e03030001c01040361540e0704100c4540500001d0b0f40a00447c411071002030012400303401000d050100c2c01c4490b040b0741c0003c101c04008040300400e803a040c01c03546480d15006002c105501c41c000303414a81c3c04070303213035014800710350f103269018141c08104c141c0022501200030f03605204a040001040319110b03443d10800105004c0c0400c4020040043d0750400040c1c10301d11032410803400748009100b044916034403d031009140340c90038204102c00150300c4004038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 24841399 1250 24840149 24840169
    0x301080304171005041505060d020102120a050d060b0c0606190315180c0501020609030a140f0412030806010806040e15061906030501080705030304080601090b0118081f0b01050d0902 80
    0xf90181d2038a801c00c0300380600602204d404103140b0a08002c6a10342e90148807252100341c0c4c010340540d114810f80741880502c000100142152803801c0c9041000e800101d00070b0f075281d41e014ac0d21003800442e00c0b2140050502c00d803900720400b15402c109040748080505003a0040d480043c1c400c810007036403a88024032907040317041c0b506145ca16141d43c4038141e140503802801c1c94004c842c0140300344000200452000021628a640141c48195a4000c045515030080d031194044240000c030078480000c01d807200d03001d14184240310341c8a006070342c03030560001050700f14002c0c8110300c0f80e402d00c030413400c00f401d000c524242c2c150032428000c0855920032022540e004a2082c44596640c0c64510003c1c50070b525600140c16200782c441920b4895a660041660303030301440c0582041c1c0d401c0b00004205400c0300303501c01444a02d060610030100c1c0480329607100040d4141d80311189942180000128010510001d10484400c019041019144840000704580a40f83c80e02c110103540c0c002c024259500c2c03a2100b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 24842649 1250 24841399 24841423
    0x61e18070e0f040c0504050702030711040603080a020601140316210b09030d05010803030405070e090c0907090501030b010201150b070303061205010e150402010f12020d1104080706020102030108030417 88
    0x1d00300d800c1c540e1102003010402c83d41903900454220002c0359a290074062180110322541c006c6080400d01d440e0009428041a003d6501076510a400000a942d01c0c000e440340d00300c03e802421040d0325000f4041d404090446011380710350441c2c502016030a00034100c1c070b0f055800800302000104034407d20035080c0d0200b07940c081c1c4042e070341904100b1014400001040052002941801642d07640e85c0b0712652800300b902e005040d03800c084000d00c0b205010540995100900c00100d50460b4800310108a40d5203007510b082c400202041020300265801d1300503940307070102c207100030000f0089000020201011500411415406c0011805c1c103051103500700d400039180c55080300304030001d079140080c002e080c1520f8403a402e000e5403060350040014402c01620a0380c06031a552030342d4084400440e180c036103002c0f010407015401e12244d0041c1c05244a040d0142c1920307010340b42d81e2814480c1480c40c1c1040ca5000f00c1c1103a004000500002502000344c40886036842e6480b035a4458001c8a02d007080c551940c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 24843899 1250 24842649 24842669
    0x90515180106031209092702131a1c03080408030703060b040b0306010f1e0507140a03030e0c060708041a07050d030501090f06051c081b030408061e1807 67
    0x8030601c141c00564501301070480d00c88104240d40c502605082c1d0348400e40740701c65000d408400f00300310364117040c81090140c4028503088000d4051140042110b40b4215104507801c4504100c02490605000642000c90500c442c070400140d9540e0007040c44900910080ca0030300040049481345d4000d81240740034007881c0a10725102d80e1903a55400702071704116411400204044c40c1203030f0071401290400202c83c080100341d070b6103d02c02001502e441d440100100d4656820040004040006000107540c41d446507a002c00c1050b01d2041007450003d08d094001e204880802410340041c03000741c00c50b0215015098581390700d100100c0c000701c050040c101d01503e140100304440d010541c2c1540030b541030300c074055001c1080001080000046130030324040c16810910991800c0e16590b100d0140980103845200b005240100d14003e083c40c03201c1514201141c0d0303001060038001d0100c2848403a40c045c40b0f0900030300d00307550070380c2e00c1c10250880a09030700750355168030402d070004807428403031000a030400e008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 24845149 1250 24843899 24843911
    0x90201031503030c0501140103050312040305040b07050f0c09100302090c0c060717161403060a0504020d0605040e0a0f02010c1514091b01080c0f0412050f0706030905151801 76
    0xc000d0041003490004130f03255403a1000ba03a0307c1000f485401c90582e50807000440c14540d044444813155032020b001502032180901000076100f60040080212034850000303441c8d0807092040c0186441d90940440784920a1113041110749107100b0f02c02e008894040340e2088464407403011803c0e20b4070a0700d90421079801070008101e40190030000404420038000c10340011991611031054802c000e80d01d1030070000729501143c0880d0001c550140d904450010001120300340c0ea2400107081f41e000100034880583c031428108401e16061203400d03422080c0714050f0a1000080d41c41301c8000e02410402410f01c810160700d542407080400c0c80234003428004400300070b80038646c2802061040c01301d1b10103203035109240c0200903146080d1480c0941d1345040c3c4803140c0a44601e40c0e00da1241e0440d04001c1c491301014031001403451141d8406516040c060800f1b00400890000c08900304000b607004a014541030029074400114001591028040410800035042d00d0b180c00101041d075103445118034541c00d01c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 24846399 1250 24845149 24845153
    0xa0c03061d04050f0a0305071502091201050105180103020a0b0a020f030307020a230607030b0f0303030a050f010b04031505040206040302090403180918060c03060806040b010807050121090201031503 87
    0x1201c10b0050340104121a008000900229a101c03628840100040c906102c2d41c00002d03000c130500c003007c00f100345000d0f04210729580881c9505c1c2c4005140c0a00c0c1c1e448400400541c00e00c1d00d003002c908071040d04101d4596056402080d21381d1100c0c03260036141440022100c400d58030034070403120a119106c0540350303a41052503000350345078096001910400e42950782d94094460300500c00360700311102e0300940b00307690764144158010501130020039005003111401d02c44940d8184019842051180000252070800e008815080700058000643d043c40420083c03010480c2e03080c0b03601c440010300c440495584d5480c0b000c110503005d00d074002900801007101b40410075421400314003101c5090303215083c85c155520b4110098806006101e003040311004a26004035600d0303005500b06040d00d08003c14100c3c4d462105030310303100701102d0540340a6500d4006004120301070148100418092800890b00b00707003198081400d8039010f602440c41a40c615807041164080c1e0810340c195000c84481c8400640d0764 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 24847649 1250 24846399 24846449
    0x306040b2e030207020f210304030506100906050102030d02030c040308040303030231060c0203030705030301080607090b040302100c1419020f0306040f020d03030e012a0e090a0c0306 80
    0x2080088240322005400e80d1511a10035a01c040d80c00400f9000c81c400c0c000c05012147d9800a940500017042544c100f200c440104018001140700e907005203064500740000034001c1c5002d0700881c009904101c410000750381e0000030703103200f9803ca150041c0d5a84032502e41c004c071445581d10003480440007203400810b1542650203000c2c01c41a1030a18900f080d03c81d00c201c680300120303418241214080040c18441d0501c2a0480f4209a2020381100d1a240c1184c465070300e50f400c02d030b00c0709c0305542c40481006055a80510160003d0030a4420141483c1c03d540c0000c55140721402e20208004140d0b21090a10016103250181c0d0307070521058514004010408141e0700070f0140086c0e01441a1705090030301c81c00c002030380501c5503070400420402c7d0000c40d0708204a16117408015810540c503030480c00c0c248a02803054904c20b0f03000a81e400c00b5400b0004d0500341c01d1905800202c24003240c0c1b1103c0c02503440300080b00b60b0000d035010000680040c03980b02900241a55081480b0101040300c031520718241e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 24848899 1250 24847649 24847699
    0x40b0903070510230405060106030b030109061506110a120f1205040c0906050604080601060c051011042c010302150706090b04020406120f02040b2206061d030705060306040b 76
    0xf4411800420700c044042c003d049241610018401c7c0e20410042104030700c607500188030710400600200c4e03200381c0f42e218581502c1303000343c1820780d5550030322040241940180158104044800c040c084210243c1c42d49544a8818403607a010300004001c0c644001b807203084190740c0081481d2040100d41420700308004c02300014010419581e19001000ca141c0c50680b0540c0d044070b91000050520342c0c01e10a0440360004c2a03081100c0510590031340524100c0a4062a090664000c44044d00e40c0e1900d10040c22080104041d03020311019614103100c6039204058440c15290160744142d02c030070740b06070104594819504050841868140e0341020459404441c40c0240e0089600b404a42c1c0c49681102c00d040b009200206880e401c1a200d6005085ca90071281030848006c01340710364007440a8407004545403040e24520655551141844116008001406d024103004c61915944e080030003ca0b42c1d81c04140039044c80b602d0b010000460319600c90300507191491001d81403014945e03108d10b440c2c8210348 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 24850149 1250 24848899 24848921
    0x905060d0b030f070f05100513030f02090a140402090702071a130807180f06030602120915010501050405040f0b060c0312060402030408071509120207050103140906040b0903070510 79
    0x507140c0350400001c0028824044e40c5e400010543c2c0b1a1400e01000700c00c1010010384014054144203241050459014260003540039041c4800b01d9402c0b441080701144006011446481c9400412a42105042e100e5030740554151401e02850b10b51100582c54009280e120102113814040b0094078021444064007d648810080f12403603038481c8115611030555005448070490a00303c001c004100b1500581c00d4803864840004590b6107d88854060b07910000035070500804000074440640c00800500d044c00b00c1081c02c0e50341550414000030314030f00c01c41c40b995204907200c0070300b002c0031601c9a10030500d04100825036030b40c1d0307010880541c2d100c1c1c0001248100c01020000000c3e04c03810940200ca10545d80080703110302d00142c075654003071442104020340e44820b50750500b400c00698a45401401071015400600d0802d05c3e00e00010180d0344c0b08407c940064030341c0018080c2c03a510006e141600150301803200f41d083d50391200414913502840c000030380607218000c2c2440410030294480301440c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 24851399 1250 24850149 24850153
    0xc020109020319030f080c0915040e1308030a0b1306080a030f020d0504090c0c050a06020913060806040303021e0409020a030c020105060d1202070b0301030b0f0106080c030f0402010905060d0b03 85
    0x10709107000800c3c2810000080d01054804001214484c41803011641c05401d07001c2d84e90510505401184502d051001e42001410f800101404280894056240e20181d40b41c507010103d10316581d140c0403404043c0030445500c0d00c0c4c0258164a030b0b16549203121007918030700c007003041958440e25140da0344c49103401503000c104011990840c0710720215400740703031081e1a21200d280c245080c0d0740e6001806507240100402800103081d00c002002404007480c5c0b58040c0101580303400409003004248207600c1c070300c2c9a9592400c20100700e01c1c00003040307550307009c2e8250a00585030f0290095200036184129240281c4040020380802e10810b15800b514044215980820034080420000e03403c8440c00d40b1140d5010300400600c03000189011031480d0504401c1c4107851482c0e54448286071160001e0300f045900b07444960030003000c8800000400e004000ba8505544241800011701c40a0302c0f02034240007070480038400140c00d59000d85013440003400090b15540e911000030903004000c2ca12500c20520074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 24852649 1250 24851399 24851413
    0x608060a02181f0c0305072003010e0109110609040204050306010b0a02010501140f100513080a060c050909040807050a0f11010212091e040b03010c0206070e041107020609010e040c0201090203 84
    0x90030150150301000301c003c070440306008030b2207106440d814803c4904404104d81040310800084442c0c05155105040401c80c021180641081609507510004000160f038034040e04000450501082886e220030151019607868010360003040c041d1285800068051060b000001100d4102000401c0b0703c540c113900030000c990701c41d1a41606401c581d4081d40c4d00c40d0140c61040e18600c1c1c60f180e500ca0030280c5045c10780c070300a0440c01901c402207143e84509441d401c01c40000382840314030b000d100300300c503494074203a8940705c0c64400217010400090405030420001041e41c0c000c03c10100001540e1540040ca02d110041151900c2c5180304480341e9001c0c0140242c2e0850480c401022090f01e40d000001050520040b0004020b65081d80c202c0c00f20550064807410401c0381500c0a01c00c001c080c00079540034151515202170064040d80c426500c1c02d004910f004d50b049080074890342552a11581260002d40d2401c42c0d20040300d03d81c1035804055840751500d000c0340072070383d01580403905003442502513940e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 24853899 1250 24852649 24852697
    0x20a0308100308041401030f050702030409150503060c0d060e0f0405010b01030507020c0d0203070513020712090501140703120e1e0c09010302040c1211120117070504020d0608060a02 80
    0x121540e11000f07000c0441030000303014510404541401200341890000384d00903500745a0701c141d0740d003500c1c00d00c0960000502072000564502440021400c601a40000e6910b0880803d070b0f20340d4000c1480d80c10500100e45030b070f4041840e0700424020000c0701112542801c00b000c45030031801094404481e81d41c0b0f4850003a070700b54022f0058900c01c40164001d041c1e9150100c09010b84016041c0040741d141c0507042c0c000c982550381d01c0401d003001104540050300d420880c80d041e1540e5481381012002c1c0a00c4104c2002240c3e8800c001c04100050042c8468640d00e031407a0581b06492401c00341da0390309050555000d00f0708000030b01a00c4041400d0901000501080344058446241100694111840c4801400542040e80100c503807014030340791001d83e4520954501c8203c030810031072840029000501c1c507110b80000801075002d48108401c000c1c1e6041801c1c1416555402031081501658000c02c0c088000c159981c4218000d104e5171040c0c803040e15214004400075488000003071a40680c003020007030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 24855149 1250 24853899 24853921
    0x60604080f070609051e12030909130303050603070b04090207081b0a020406050409020d11011103160308010f0b0d050c09180603010609060b07110301020f0a030506030f03130e060f03010507020a0308 87
    0x1140d149522502008180706c5050140b0700042c0841c00c0b40c10b10041147d90003984803141e006200d420052807103c074503540d515004094032000f80c8094801e50108605009400c4d9140489045a260250050780c4003c9850405068001c032502d042c950141c0a98800c031110012858100c02d43c400c039004c00940d41c449040104840703030004040c1d049190108140006000108a429202c1050504003100000724603180e1855000380001c0c1c03000b00c140c40c0749800301508000481e024001c248031845280d418a03040000f10b00403400300306407050f164008200c0c0d00c00c40c81c0403218400d07006040580e0520b10410141c42038002550300ca0b00947c0b808800007500580c601c6a0300548824040306440c080303d82d220b004810a1400721103078155420070140310704000340170007409850300c02d48020555283c07107000c06040088001503e03070150030070800c85000418014800c01901c08000c0100050303225000400c008001c00034100f9015840c0c0340600802640000d40429003038460703607505e40780ba03603007611001d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 24856399 1250 24855149 24855169
    0x3060906011401030207060b030102071406010602011404060207170a03060f0801090302030702010503040303061206060302010809010c0e21060106080603070b130b03070c0b0103030e1206040c030308060604080f07060905 96
    0x4039001c45204098840e61003500240006d80c010703000820b244001000003407c9a21002d400c9980d4141c075102c004000c0821f01c17003503004143d140000c11030510001c00c24414008001d00027803280b0760018514003080500742d03d040c0850600c201c055107542c3c0391b80002c1c00401542c001c5076441c1044140c0020400014001d000d4417613415400303507040c801140c0c015526a00013620440c14180c40f0b181c0032800c4d116100340b085c809802041e010503c01e246000141440c02c4c050500400e503418074018809164005801d9807403041c0903522801d031500301c9441000c560f00d400051011a004481c0002216036000b244c2c03600801089007a41d8a007981c176001940a4864240c095140c500ca810040007111800030186034005000e05200809025954a162810b0b00c01d81045010901c800c449a100d0700b405a03074100500c2041000703041d0381c00e2680700e413032584605200040070080442c000400c3c90f02c40509880007000c007030f012541c3c45008000c1590b2650240e016813000070b40069400529803030b000c8084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 24857649 1250 24856399 24856409
    0x2150606040b0c07080a030309030e040c0c020f0a030203030c0714010903030206070503070c080a1d010504030503070204020903011d0106152f0c1003060906080109020a06030c0905040c020c0306090601 88
    0x2616240c0b0b4140321040d40d8100030b120032141d004a03580000d044005100039101c480c8203541c002000699440c02400011a030084e580c0182d182202152445800154040416804807a0b5080752050327180060300640705500001d4045c0804101030941c40000180203080d01e031207652401b1712884036401100c1030200b40c0310140060f849003001c903080d24024002150040028a17104007e10709944400c25258000d040ca03100155144414400d404071615417240c400c0320034a89107142c0362440c0c407403a40c2c0b40140e001c068400c903800107414200c0d40d402d51141000302c5102c40b43c0020f1414002c01a8000c048510881c0e405d1a00f140043c404030744a004400707221110415074103c00c0c500843c0081480700c0c401449881880365400c2450251741e0084504100d0407540e401242442c1014145029070b505980301c1c00d1181e051012b0040140e55499011041d61818a00040c600c1c0348101c0c1110b0b00c80e4541d00054100f40741041c5850919808034607909009802e50444d41280c0322900d119988031824414 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 24858899 1250 24857649 24857659
    0x3210207020108042d030f030b0111030f03130215040303020d02010506100c020a090f0209190803030103080310120818010c1716060c02010b030d030603030210090204020c0616021506 80
    0x1400055841c00300003405640c1d4162900540c1100c4040d00e0640c03541e08080c3c010031b201c85400703910302e07032316008000c0e03407100a00e02082c1181c0d0144100c2c1d0f490107000f90303e400000b0b01000090801b0310b06a040d444294005140401c808120002035101d0740c0180003c1d4010300030028511180b50050041c0c6001d090040c0203621044034030007089810000314142264010082c13040000e000c0200d00880b0f00c0c01d43c501000507522400c800c200300854440049000e03220840c00d404000702072021094074112900010000e660703984500d20750001d19040e0300311580a4840c0340c2000b080c00740c0440a03020007291801c0c1c0d90100e201305c10047d41c80c6000d83c90000e028100c9641c0f500c07080b0301c100c006043c00302c25070380e00c035080742070b0315501d0105403004210b50900603956803016050307601d01000b202c11080c0032400d08201090039510000d440303070445282410300325107034502e040c00c6441c1c1ea8100c4880034007031411350302c4a0030280083c00b40da68240d03501c6801840345d642d80000e0010303400501e600072500208 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 24860149 1250 24858899 24858901
    0x4060906030507050301090b04090203010e0c030706020703020915060d0905012c060c0c0102090918070605030f06010305150603130309050f01020307150204051905010201050f0105010c110f03030703210207020108 93
    0xc041f0090540401c038141c01c1900c50340c5a01c01610300740201104402c2c8075002d84981f498210502d031400980e9401301046501c070078010009600c428056540140c000c05602000c0740c0d050012400030710800c00e550519519041941c000d001c019031200c1c04545008102c01c0103520259240e01e04944500c900c580140c05c50408101c5500210b8018402406054009070400d1410000074144c0d600c111030501d0205040b803c207040356441070213411701030207881c1801411400c0030100c011000d10000d161a06155681d00800c00b002c0030111000c41101c001401c1564a00d031400715299a0000404120f0201da2012000b04039460000041c03106074406900031402c0506a89444640e0403840300b14003070283d403c01c804595601d03091030440c2442d014000007441d51f46801c00080c00c4800080401c0c0b4030075440e03030042c085a0713400202106020741000714291081e510030005400f91403003c6c0966414840090600100350f0010501c0781c500c1d081c0b000d0030f400d0000d0306031b8180c242d101d0920f0007070000b03600e10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 24861399 1250 24860149 24860159
    0x405101b0c0312140901050f070207120f0b040510050109020c0c0405040204090609081803011a06072109030c050301060503031b070b030c0318070602061602120a030204060906030507050301 83
    0x410684281c034040e14003016180c3e9955200c904484c0b40c00320b00c410010900040001c81702003409100c0d0412019254440c0502c0d022000070740b9101d16008040720807600d103000505002002c015814070a401c00b07180e0355182042e01d0101d568414178a114900301d4200340000903289024403c1e04d9030901c4c001d0103000341c04854000c210050800800481e400ba80d500540d1380418224071503450b880f84a000740c7c95503000e1b2002c0c540300405001130600d11a03070520503044200341c0c102c1501001c0c81426560103848408914021104201803006a1020000d45643c02440d961001d400e1f0110703402412518a0b9a86950906007601c55501807950141d04c2003080380d42020000b1820710744810008140c44c401b6840f500c2c500c88903841940c005a0303808022091014410a45900c0f02e20b00c450f480081c40070034542071003e0f407100c03c0100402d9541002016426400d4000d0002c0051000903003a403554500300000c0140003074000340944c4000800400c17020070700e80c0c0030340300ba180500d403a030b1900d03030440c2c0c42c00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 24862649 1250 24861399 24861407
    0x70206070e0928020d0b0112050115030207020429010f051305060702060c01090f0209060405090a0809040204090608060714120a0c1101051e1e060609030f06040b0405101b 75
    0xc0310718094518001580f501505940c0b01409103c0b104a601042c00c200e404001000d540d1b6440c0d0303200c100784c6000c0041104620010740b00003c0702702820003580315441800040c00a220809210440e08849543e24008440301c40c1c0d00e00b558002600c4203104031018240494581c05449121405098502014452460080c0280c50007520081070705240c00d00c44d03181c1509440045404a415818070303003a040c21803a0100d4a02c1e070009042e03c0c104050701d402c8010355036075020302d85c003d84101400180d03c412034035190112005000d6040c1c00340580c5603168000d80c0e0b81c01d0203c6e941e4001528840203030018030030b10000c1b1188800c018030409080c1d00d980e03102c50004c04c0010405c10a1001b009060300100e042030003401d2059400710360b180f000c0c8074004880030140700028084000f81e07040c4001070300080a03440049400074420b48085450b601c9000201e490b118a0100c0355a9a200c0d040c2003000b04008004182d200310b00c13036000d40380100d65480884042d1a113400c2100100480c914000500c9442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 24863899 1250 24862649 24862681
    0x3081b03061e0307080609060a0c02030a030b040209040c05090f060301031a0703020409050114030c09010803040905222f060405010305070e04051005011b02011e020f15070206070e09 80
    0x96a103250b4060942000040e00c0e00700309030300040740360f0450410004d20b000148205d6500a01600081c000f403501044002e413070f48544c81124041c1030b0b541d1201c4540b500c071903060303651a65016108000c03400d2008800341440d0400300c0c01c0761103002212256040c509180003964101e0b40d02049024103e180b480034a126400d0040c00c6104040d070034400050381282038021300f802000d6105103c01160784400031705080c02c140c03684690040e40703d680108100c0c48000101e400f141c18441c00043c06880e0700e44150303940c9601c0c80c001c61108410b804414140309170840036910301c1405000203079502d00030340004a01c41d5050804154070507002e20003048194000d1f0411944400e907881c011a148294100103000c913042651034a480d40c008500501003560400c2c1e69a0100d00c0c191000550000355a00003080b90301c44a114001414141d440014518002c000f81c40000d01c2da0390507110804a03002c03070030b980b001007280c4110040c42014082504103004560061100da805407a04049640700f68814102c03103c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 24865149 1250 24863899 24863929
    0x307170303011710090308012c160201090611040e09150103080313060504080d11030105030316080f040909020a090507020606041a190306060515070303050a0906020706050403081b0306 81
    0x340b034041030040c403401d20503103280b20300c20b4035000c000c6e506001c1c0e6038017a15849c40200c0d03a401100c5e8180d031800391946601e42ea03c91000303002d08082c055109000ca01400045d04010306840c20840b2220404000030058801d944803c02400c41c0d0f551881d400b1503864066000c110310301c01e54200180013058402009540c0a40080000c8159409030b40c2d440040340c0c011a02507400140114220b61300c0c1959024905d91500790329400c50640d41031130002034591164801038503818800c000310604001082007a01d5000d88100c2c501a2a1355031445038001a1801082c224400e44890ba804621039015120b85401904983d008158a0396402c085c4801028050b0b8000a000c22407850702e0100d0707841880c00b8a0034110080071082062441c5417a1069a403681c0110b0312a001140006034030400000545502d030f41c051502040f25251400c0c001c0042c040020f01400581c00001e041e018490b490300300c2806103200390761340c529681d190120b0740d6007a9107034844100c01c03c1d410400700315a0301d00000c0720340e1020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 24866399 1250 24865149 24865153
    0x51003030c020609010e12010b040b01020a0506010510110313080c060a170a02090a03050a050f01060e0f040c0509090a03020d08011a070203150f0912040509040602030a060b0a0504030203071703030117 88
    0x2843e0900014001c07030b607c244007000c0340e4490005601b02e00b07103402070140809081c0020440c84451366200703608d8010500810f8000d400d50741c0c81b03100952140d10030380c0d030520b088000d484ea1a00052180101c264041c010300c21b061050020303010080c2040006c4071414421559814600c0d003c1d2046c49400c4040a8802d0300e031345030284503503c01541c48001d4407008601c00c0004000428651034503500344132424a111880740d16001042043c1881c80301e00640c80407058400b00025a5107203461116511140c1200c0d81044c6100c007000b415800014003455801d02903000c0750082c0e0240300040341c04503800d000d03412034425110112805141c000002d040000e2006003580e290200ca0f5514102101c41101c0748810080e1800511003422018048201440001d0003824541400e00700841c0e1a04800b81000f49219800030006006006550080b0301400c15a41c0b0290340e13138002c6a0041c85a0014041039100c0d0080c0c000c000380d680190039050501251303010245007542e00c2d002d6556048004641c03884014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 24867649 1250 24866399 24866417
    0xb0901050318010608280308060d08040806010b04170105010501020c0d0822030c06030212041e050604080a1202160605071b05060403081f030615090204140103051003030c02060901 79
    0xb1110a004090181c1694401040384103d0303004420b420803d1004990f22a9507800e091001203903002c08890741c0190180d03103040500d907051520740c4492141c8d0340141c045001e000300225104503848020422100481040300c500c00841008508a60f000c1c030807140035038446110740e8540c0c10070290060307909001e0740109042450703c050104000520380303030000d242d420750001442000104a1040c0c040c202a140440c240141d50f190307010000c0c0b019001a203840c1d410891990520015400c8a0f8000d60003420f039066420a45000f02080d00040c1401e00440c1c03094440070280c42070740c42914084440c208210454420541783d0b24010a8007030403c0d010003540103444098043d1080e00303095070511a40040c1801d00d0241402004c951003d0600e032040a418072004000940f01c000b00410750b5086040010680261401031100310140d84c05900d0075400410000340300712500c61030a051707141c2a2801d12140e40d40c00c0030a05d1468903400000d01054145440c10050b042180280141d0701e8181054155 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 24868899 1250 24867649 24867691
    0x603010e10021b06040c0608040609150b0906040902061905160503040e010b09010507110102101112070509010207090203070912060203040303110903030904020c011104031a07090b09010503 83
    0x81a58420284200c6600000c0f000300c486155070281e1541d203244000381c00c05060540e10b0030120142481400b04115651003c101031150035403095602c2c50f881200701031161960308070032028000d04038240f031051185130002005420580602c9801c40c2c2d000300f94501c0d003419039202400c43c0009241e20f004004080c4200c12100103107814603908180207800440c1c0307c501d848480100304030160040e401c640c90600c0108002c1c2d8001c82030340d04056201d00800400d060340c80040b4540840b0800030314245051130120380c1c2c2d017591b041c0144509170300903030000b21640d900c0b4800d4800b442040e90741e600580c0451800c110040e4154061070300007a00d881d009000c181e4071880420b07000c6145800383c4400f40d00009010404d0381610840d804098034400c1c15043c10711000c00240c60303028210b0024000c81e0009040400740400f0742c40403030f071318101c50a1281c86685900b000d4031412004201ca100400150300890f1070180a8000d80c1c1c215680c100b00145002503c400441d91900064140d41200c0140c40030669 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 24870149 1250 24868899 24868903
    0x7080c1009030903050d020715030209030c0604091a030c1c0317070302030708091c030902060d02040b0405180c0703030903020a05010e0615010507080a210507050d1a0108040b0603010e 81
    0xa00e001c2d41d103140f201400d50810a0408801e01e0f900404d5502c6000100b0030b04000c2407180c55942c245040058859111002103420400c1081300c0c85ea000380002030206982ca110741c000d000c3c01c002541c07400740500b45a42855541c2ca0f6504120b60b0003003a868410424150582e0075114282c824584800d403001440b021030413122003500d01b1404260044204009941d02c03010841c6c0c007035905001009054907080250941c948800c400008254880e9040819919040100c1d03402c2c10b01100308540d525a26808052035030000d00520344910110081c00f821642c1503003010307000e2003000b20540d2400c03000da6420707001400c46450440950040c402c1c0c5030081142071203502c0c68240d22070081c00003032400e10140942561204901c6040c010284400d6000c02c089006603004411541014400c814100c000d0040c0200f910001520890800080050702c0e80e00c80c1c090130b0240114a010701480e210400d80101c0401d4a582d030500040010f070010740442d07080c18169401c0140a000003a5450000714114 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 24871399 1250 24870149 24870161
    0x20a09090507030f080702011d090403080c0c0604060218030601060e0d020427121b060c020309030f10050627060112020a0c0506060103060b0a0c0302070b0711010905040c0507080c10 80
    0x91079079174000c10300b01c0039540c0002030740681003418900740101222010009170040c80181000d070030040070600240520758420202e4440e080214204d80c6c01c2d00c0c05143c0a00a94003202c07140965003000700900d24142400140703e030503507000d51184038070400c0d42024494454070146050764030645940e00202c0706d285928100000034400154061985410f003040e600011409a4500801c04501c0c0304d41142c2200f026041c000c00c1c1e00ca039002c40d00c0b1042e180120b295004d02c02c0020b40c9401040c00310751100b180000c2041496074900d00a0006540301c07002c03c0150f822264000d600307803610050004a0b00c960040c200d0780f000d814140031440d805004140d0049800951914005c0307000e10b0311200901400f008015132020003440d041c0903035418103810b00d089014020001050000d20079030102014008d00404024140c03030121aa110045c1e17042c94400c031411034224034081031f03c55001141c0c908107401008480401a2a0240780c4100380d660040700340d028140040d103600801a1182408029000320303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 24872649 1250 24871399 24871403
    0x304030503090c150a030e15090303070e0405070e01030c03060f0801140606030601020c0904030504030209040b0a0c020a05030306100c02030303040506040b0a020406020615010c050601061d0607020a09090507030f 93
    0x1054a81c60b000d40d002d490700042110441c070448080794070100101003101258a50403040c94046046c4241d07812940c60011500504090044004100492144000080c42c400c504a03038840c0755100340541800100c0c1c406442d0000003400c000e01d802d485500a4204001510b510b02d400102980e0700d1220184240854000c2c1d03450340d4443c514060300c0c89039408100e4000a08481082c91410502c0020395202071710315416000d0301306400080c082c0f40c0281c0030b9074011038000d001d103640d905e002d26281d440d2580849881041a1800d81d1110b05507200141030080258032a0056166880e41c0c000c100c09880d1800400c81046a02010100182c4052020314011403141d0028815810203240000380c18000611040c1080c2c414082000000d030700252803500204000741c81c60000d901080106c481040070413018100f485004000507540358445200c3c2882c8280172840c1d5111501581041000e100d81d05001e54010b00c100c1040c400280f16a000c40f095510550031582401e07941d41d19400702d40180041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 24873899 1250 24872649 24872657
    0x3140309102f150103030e03011413020405040f05030703120615090902030901020417030d0c050c0a020f04090212070303091a03010b030a0213080a03091208030f0709080a05100e0102041203050f0d02030403 90
    0x2050004c8d0a09005120b841606020000c046161120450805000c0c00ca40644035549070310106081c0301c2e035008202c81580e004410b51341c1d140031314200901a1240d15500107100391404c00c0004600b80c944010300003054440c0d481507565440e040c0070501940000c0c0c0070748019582003000090759442c01000d030002c90124400355032500c0069184408a079004000d040500070100605045910003194842c0749a9044070001c643c01c2443d000329008000d00d00c4001d41000d0102512a81c1e210300003a841c045a00c60341d54451010340354415140781c0019500d6280c01004e0074001404400c84980285d9030124560400500b003031000c01c03810b030164031103500c40003160300315a54000506501032084405840649040c1d200c003001595240c005100040500e040c0c00b0410020a40f1284a07004030001005090300b02c40703001c031035810981e442d101c1c900d030b001c841c0a02d010b551075080300040c0241e50441d41e02c072840011048450b00d007620154003000d0442c1d40c50300100031134000f00160f480518060760107551 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 24875149 1250 24873899 24873917
    0x30905010c0503060612040f1707020a0503010b06121305060c0a0807030209060706020703090b0409020408060a0603030206060111030d020a0c02040b03010e0303011e03140309102f15010303 83
    0x1801821688820403070402c02c04104108204c2d600d0709011540300c07900c2c0c005146195a03950518412682c000c0f01c004006181100c0c4003040d9404a501416040d4022224001e240d6030790402c040c200e941c1031313111903042001403010b128921191002e841c8d224440050000700c054141d030b5001d0614004540c0b82e0020200801c054500a03407218001e0b6000e1214142145070990340d03000500c5a001d0401c00070025034001515804252203403100038018195015901c0c0c450b6114202000a5002800350b500c45109010000c0d07204101c40c003440e0303310b030b0701900500402e440380e10046880e0401c40c044200e00c1d04c020040000301c22000d20052012050741cad41ea030f0400560510401c015074000529280c866070500ca00740f464003201004807411144401569500000810b0825031480c07219440502004040090302101c510003000030070b08284202c80b4204102000c0805072201d0b07820712051955005001269100c50712100500b030b19080000088440e80030f403102d95007030340366001d0704200d000a0441d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 24876399 1250 24875149 24875153
    0x22270501020406140c03030a0f020913050114060708030703050601140406030501050a1509060f0207121505060d050d0507020103020d1a030d0302040509040f0c050a03060e0d030203040b060f0a150309 87
    0x81400203c508082c03904c11300d89a40d400f00300340c3d00e00000c8d144010180d99400c668041000c0755048814007080036100201c2156000805d000500b824420307803140b145200340500c0585003c0d011140881e0303110711204d045445500c1308500400000b8105c5052201009404012600b01e502410082510b581d0200b01581040203100c1c0c0c031603903a48080d2541c402802c40b07002c4284c0000c80310003540c083d841d103040c8403e00c42c203080703160001581c00b40c40803c03202080c0300f081c0f0032880d041c9010440145024455034591900f88040340040200240c0990450b101c0840703100d119100030403103540145070160401300081060f400b00c1c1c0c1c021282d6500c8000090013048181400c2c032141d400754401d13040450405140c4008144c5006e40104000d05d600d030385407960310401000030404000751001038100c04080382c4070700c4c03c00c2c020807004202c84014491803900045040c46802101c3c03140e90700c449480155101c820920507010410400c40394850750b800b0000c0f41c90740c4000261103099185640210f40c82000d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 24877649 1250 24876399 24876407
    0x903091f0201110903060406051512011b020c0904030e0a0302060a08040b1609030f020303040f06090f0b0405010c0209040f080a02151311010c140102040311030c22270501020406 78
    0x1080c4011030083d82841016142d55000c9040c0da03025820100c00b10340c0741c0c0c90411030342064141076081039120320142440c0340303603070015842043c031481d0081c043e48009031800f071700740c0e602c112482106034844801c4002070f00180c440e43c0703002042c84025089603030031904c0c0c1d40020901d4102054000004080008120a1100385c00c001e0b60800a81c00151262041d83c41006107405168003015100050f091020000c549040040385c006202c0c080403a804603443c1c4100400d03840340743c13080c0c200d904045c08001c294200c1c041d0454003200e105031100b9170060340326824060042d100400503580e500c40da980f03100114038104020641c01c07031a54060701c0700d9960380101c2038480b4000341a0451011181501c06d0002d450040b42401000003420030345040025450019903070f0303181ca51024065400814000100320030700415805038201181034940c1c4000710002e100c1104076100a070390441403d5204440142c000ea40049120b10142504420f1070404582c2080c4c01303007903224105ea141e98000760030007801f540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 24878899 1250 24877649 24877661
    0xb0a030b0a0308040b0f090303030901050105010908011b030c0201090b0702060a15030218060d0c1202011101020a020d0f02030405060310030c05031915090b0f040b060118030602030903091f0201 85
    0x3044034200c00503401d41c0c45905070740c041e5001351440160009246a9142c90035010344013400c0000341140c0d564642205000e020341030070300c50180440c400c2c00010a0b991410b010340484040901c820b09000d09444000310080c041421014044d035684103801000708200b41ca410344202c0143d0018201da04001d41504125030340d4007100360004e080742c04140b00503900c49490105450407a4182066500c5200010700c0713803014500024840207100d00005441d807028624864014002d80792200c044020341d681d2030a034481e41d00e2450050700700000403000d20780102c01c5e0114400152040b24285038880c0040b8909d07074020380b0003125044d500c840810400c1945881500605016405007915210b641c0180c0c0e07c40301034050007003003c5a1090320410080e800e9201101c0d06812402300c2016051000d482098501d09480c02d48135164803000140300365001c0c441c84034081c45080d080d05903140ca2350b181c2c0c00c0250000781c021070113404100800c009540d1020104038090500f000000c0017407000340d0000e406c41d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 24880149 1250 24878899 24878921
    0x90222060e0a0212010302040b011e08040314030f1816180e0102120705210a0504021002120423040207080c06070c020108180705130b01110703020d1212060b0a03 71
    0x300400c150446050403c04417030440341e041d81c001c501d040c0c4403030060320212040c0c21010490b14160350b400e02c00d41d51042c4854000c0d0700917102d1170300e081c40103130341c208552104803402d407000c8035a080401c0d2080301c2031840004400200e8251044151495600504000365a101c1c0c0503030700d64400340205000c0789204020250344100021403825451607880d025545000b810741c0140200800da41c01000c095402c490f20070b40094030a580309140800d840c20050500791070680c01503030001e8045a40c03500000d542c0b01401201030015082600d03045910b01944c240b10604098148000916a50b0740c4450000d13100b80b92080000940350707000594580c0c40c100c4005c1c0018104901c030761109000d41d130014070080e0001120781c00e4001051b4024001450407a032a40465002880030b0158400740142d642324035a5110260380d0000300c5c44c1000c2065545800c1800040e5015011004003c0040d050f044c0500100c075840c10304540303000442407240112026907000b100d8a603000100348500325418460405804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 24881399 1250 24880149 24880151
    0xf0e090a2f030123150d061a0405070206150406030506010e0105090a0c05070f060207050714100918051b0415080c07050703260c0d02060603190204090222060e0a 71
    0xa07080200c0e13a020141d5003080140e6440d004100d400440000d546040302001d0710480744080185030081c02041c0d4405500054039507210100154645800750038000d008503070083c0b600344c96940c0400396250814080300d501035074455000000941c1800441c0c001c0c084141080d01c20f6144c5001d0241c01d9030f00811100035103141c5400c403220142c000c0c0a0312450394000400b070b202c1e0005da141030300081c0715401001c0c0240c455808001a13107480410b1202003140281ca6404090076569070644020100c2d0044146509019407034a07100d4611b940415400b41c2c0c402c203182c001d030501102100740c5a00c140c22466190450a44401e0569040000030740c003c0c42d000b102c5490022551210358480e81c4c0e03408010002022941e0015000511040b0041d0042c0d50300c0040341d452044075101959000e46030b2210300940208c80002c2d22629000c62420030080c6a07109071a503400303e07036003000014500303190100e0b03000c801e5200070f404009014803c10385c0d850320060005030060418800b001c5000c0024521520383d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 24882649 1250 24881399 24881411
    0xa05090f06130303060b0313110d0b060609040605090c030402010f1403060d06020c010c0908070504020a1d030106090906090201080c0a09030303020c0c15040306060e010f0e090a2f0301 81
    0x65000a501584072080c1042200c46540514013100646070030b6000c104003083c04000d10440c0100760305042c01a0b88502502c0c40300000b094140703c0700040a03c0050700080103400002d4103410818010312000100500024080307464100003a2803c0301a210102c804501004220440d604104044c01b015424100b000300c60403511804d0040e03110051500e03000d1000d8079842c1e0208116a0191824a0715a00083c8012809140001c12485551194910521602c500050b003410503208441d0b60094956400f401490807480000820300d0098000b074056690300c4000035030440d184111240103201c2c0c00d01013500c96403030000420050002e025851034540403c880100c080d00b10384901c04591741401c0168071a00383e01d4a85051000c01803030b81ea002106110000118400c42006000b03491142400b045166161180100c055909008044040c030300380c4002e10204030411b240b07507440040743c001c60700d812601c0d03a15103803030f180805490314040341008915850201d0380311922224820a81c001c001c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 24883899 1250 24882649 24882673
    0x9060c0306010c0201030b1e011806021c09030b0c121501050d0e0a02090103060204081b03070504050c2a0c0102150402010305040510090302060f0c1309020a090f0803030a0509 77
    0x1880080c0040e414020300c000c603c400c40e402500060240348009019848064442c00400301034501d61031241d00040010402c04c2c09065540848d5003529031541c000c2115000740d007010300d402c00504a0300c030103221140f680040001c080486c058440c40c04048941d854400e40d100713050074400003420400c4903074088207841c015a6402025203032252076800c03003c680901f11180441c10007060b00c4001c0d400c0800c070000401441120380092040328000300c03c49901c6900429840f400364a07807034006a154000b11801c0140c0d1802d60003c98110564101c01460043d8000768442d40b2a0200c05000d079101c584c00041209072018008508608003c2c00607210b044050406501c0240340200000e0605940c3c00c0440c09001c000c01007000040981c0c07000b0403412515040181d0b0319002200c05500d00000e460000d00b030003a541064800e002e40a00002d80c030a8105503540d00a500040801000c0064810f030000d048005003403090005c103076010145560341480b00107481502e0000340b01c00310f20b501444415507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 24885149 1250 24883899 24883921
    0xf06130c0b030411040f090602031501020c0a08030304170405190f06022b03020c060f0405070611210f040f03020f0a03020303040b0c1005010305010506010206010519060309060e06070203120906 85
    0x10900c4012100002c00446da0313001c40008010160000e04560310100030004844001101481154026001c07603408100c0d4004000c50500c849c050510a5001400072a000580011301400d50f10110400c807406c00e511040441d0b000c450b2840c501842c4404a442044090711030a00b00001d00308030301c06000e5044019255486000448002440d420354808200c00402d01c280c0c191040002c801003a00c203981080d801f42d00f11813409440c113036032a006403500025100c1c080c552025025200700050590200c4c0b840100506035130001d440b10070076000304030a04d0701c0100d400c0200301610401039466201030640c018400300c42400c00380e4034002c601441e414000341e5000400c0d5002c40301d07940d4185960740355200300d10382820031042d180c0d4412800c110001c010480c064008a2041c0701c00e0b82102c04583e03171902001240d4a130030100341400c1c1580c0d8028420284a508180c100d0380c0030b09404107000030104055880c266080b158040140c00110700d41c0380342d9144031840307900200d11030010801814204030500d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 24886399 1250 24885149 24885173
    0x60305061c0203010b06070305030a050a061202060c010e0f0a05010605030706141606021803010b01020a03080601030c020f03122a09210a080901030b09010e16020f06130c0b0304 78
    0x42104241c00802107540942103000150005011152151103c1c913010b03007550030545034600b000d4100400250304003c039108030000c84400714107402c6440350907000d00681c0c1c1e01808400c0d00302e549400c9510042c1004016802c1205451030080401244a003011400c4490a41043d40f2075008140c04105e455406644a0f28008a08040a6072904801200c0d0700000d03142000412250020800d0046280b0020a45d00d190f80b06500a122920000004a841c2c1000d040020081280d800103e80694402e51290501c03c0316801250382c0b015024650300d1468100c0c0c3c00004884081c0010041000d1030301c03018a20f203480c0c1c0340a080c0100c8a524000013540500e6003c14000e1131a03031109408d07064242e035100c00040350001035031291640d90901241e80d50121800391301081c10003a150717a540c01d2025140e812950142c0d04040d0740c0d1640f10b501d103000340e4611a80c0742140305401c0f0620400c80306004250042d042842c4410099520b450000104416a40244014032043c0100008150402414 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 24887649 1250 24886399 24886429
    0x30c0402030711010c030f050108150a02030903040803070f1b12060203060a0302190509060d020f0405091507080103020901050411091002030c1002030117010b130f021b0c040606030506 81
    0x561682d503800800c4510079011807499560350308004110704501e0301640000080c1c0500355060150741e807540d0115507a00220230102e0f01a410410000303445031071540c09941c100c024442500c0c40c260ba25650140385402407002601d90406a040b07900400007900007541d2402d903060380300c00b03450f4a41311441e031018004503005408540c001000514a64501c01603601444e03004002000c5404904080420705040340607150041108030040345107403404c2c100003000264010005040301152405020103800d01500085071445800000414000d14132200e030f00c9050f8990f5210b40030b40c9540104602401c046c0d0003507002d24034103511622000c001d941101c2d070100d01a10289696034a61100b286540b040d00303414030721402244050070014915400950403a000c1380140c00041c000b5a86d05401c941810550380d5101060500c24502c1e107800d600304680245941070300500f05030520300c00e00005982d5502c241d034075400c101101541403034184500000781c9424541044140b5001d00455019a175000c08 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 24888899 1250 24887649 24887651
    0x2203051804060302061c0b09010f060c050c09162a03030504020a050a080d020c060c06070c06020903070303030605090f04050d1202130b1c09050d050c0f0111090307050f030c04 77
    0xe0034880307840307a800c00d100459002d418a56641240310319002c1c001441c2c519500740a05154101c0d1803480c150029034143c44803035914030002840c2c6481551041c0c0005000c41d02801030041e41c2c1615550740710b501d4441c9a9246498a200f003c10800414035070b800c42c1100142182c1d900d40c03c0c0307020225251a10802c0e81070800103440d890360700004030080c0e2254003440d4860056040416403480c0403e4001e9942e1a98080b654088440f00030000ca03405003501035074080d0700074000940072510880d800c01d03602c0e003e11401032034003003040042410225a604250f0100b601c80f00e042003181001800c00341c2c0022500300300001410a60340d05074035088480c2d400d60400c41048420000400c2903811610250305620b21031640c16035031041e0404a412000c0030341d1a68040084400026031240509407103a1b601c500508100d1480003015500e980040524113158800d0341c00307601da8901700f4402c5107180803800b1030103a216480340c0100761038014950440e80c0101c038054a007551903200003074001000ca000701e074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 24890149 1250 24888899 24888937
    0x30803090f0607030b0411040b0a030506060408010c030b3c010219051608030a12020703050408030703030504020a050406050603060405040f0b0705030402040615020303131502070b220305 82
    0x403940d86071a0700c03440049824010785041c0002c00790950b000003400e450a80c1c0c1400800381d003050520795400750348240c115180f4208000c0207014401d41c403031944250028803150070203484040d030300d00b100c08400c4914080b980d180f00c05026480c2c1110346c0164080900c1041c0c140413030506d024501400303c40041424102060194090b03680240f000c0310a0f00d180ca141c583c8840c5c6541025503650b00e803200c5144641d101c540c40461494808022628401125101c0c0d407000c0101c6000c01d0300a50008600b501000824040850403c1c018001004054001d940c003040a0405004100c071503034030350b400355201c0e0f07190070010812500c0d100241c0340d01600031200015075503200d080c260100c0b0200c0700018140440c1104000b5490b411001840c041c0c0d000b910304104603511100b16642c010450041e00015a0042c400100d180d2042c044010074140306001044400b9855504070007a44c01c0410100c0300c0500a50030403161180500e00c51204c1c4501c020180e0144540340c070081c010b88a060b445130103d04200c0e07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 24891399 1250 24890149 24890161
    0x60f07020108100515090a060206040309060806060909040305120a1e0504060f0c080109180b0105061317010903110102030606030705030405030f03011403100b03120c0111030a0605010f1404030803 86
    0x2c0100010403000e4081c0d408401e0b602c44c19802603214440d003a100d60f87c0504085020b61002602603c2154180c440062a60610744103544014004013156484881044111403640360001e03070b2401036109490f104e8403071507a41d003d04499000100092901071400e200a0002145400d5140c2072070f40da040f001841c0c3d201d40c1010343c040c042d01d00c000d550807030070054022003480c0d11511090490701d26070320801100d000001c1250400c6100788002d81460341000c0144624902480105142c050030440d00d840740d03656000d06101c8000304018880c0a965031b12034034017415001105082d007611103200852541c034000000807484d01000e4200810403001100050400c1420011a4014030555148945075a515180303004600a400314282c02406200c0200165903000d00403511452401400b9000f42003c140143e01a0340080c00c90704c6444d922540401e01041c0054006e5024040d80030740070420038245400905214808082441040720f4483c2543c490902d071810358059039032014800796203440354 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 24892649 1250 24891399 24891421
    0x3120c031112041203090f081602040608010c020c06250302071706011716050103020a0c0605010b04080607020d050403030c02010c02031603050c0d0203060a180b0414010506060f07020108 82
    0x80c0c0081c1a0000c80056540001000c80003814851485074122800f00700d00c003a011400d0b0307800508028190442c4080790400640000040c0824882000090300103c030341e50001016110f0300d07800300705141d5558030030751012681031003001c407808403c0d030b00d05161030707810310307591442e080f0307000003228400484500201011300c240240d000402c401e0100c80060480d460310795483d01d10a128080d600b41e050141e14558010100d1803000b03000007050504501072a120064002c2e60100b1649400c000088101100107542c2c0d2041a01074000d00304c003079032a5404c0c0411245071140280882c0155403141c0001c02210b0391020441d82074a0349807508418407a280d10041e2018000a5002580350050907001e40e0711100e540180c408481c025411111440c28a40500c10040c81c0074502a4045c0c100c08000390b90340f285034215411250b8140209100380340704c1e8643c3c1e4200c5109a03801c8812040a1511121214003401100e80082007182c2561400200c0c01c0d403510703503101d0084c00038144403a40c0c0020f0b003080c4d85 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 24893899 1250 24892649 24892661
    0x10c0204150e04111e0105070209070513080601090b1c170706020316090b090102191103030a021006090506180a06080f0309011404030b0f090c060f040608070c03120c03 74
    0x80b40d024464581000d2900008000d01d03081d05034050342051000500207000e101001c1040501a150360f031034090780c2e4081c8803602c080248801c05010b81080010014145032803440c00505180c005068154140181030080e078180b4a80c0f00d1190000001040340c102d9400c2c1c00200c02036110180003020145264021841d004055014103410302c04810420448902c103100c091040d074980d07510041039210440385540d03001e07d0200d01c0c0113170301000805201141540a40203a00c0c0141c1c4900c2404051400003031075540001000801a0060340151010007000c0c0550005000c440b0400d0240d842e000000c41c0d1a681d01054442c00c0083e11400304408510642c082c402070442c100075110b00b0210030b80c0c4143e80b50b000d0240d19000808884d0180740500070101680c05aa40c40b1800e42030035182c086044500c0b220240039000c0c1c1d030045802c000358940e5804000c0400c40740f4031040075111403808001a0160704001e091b481481814800700c00004d03804007003100d02401e00480000c1000800c04110b009000b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 24895149 1250 24893899 24893909
    0x60f15070f0f12020f01060b091005120408090109080f0604020105030408070c0602070612111b030409061e080f1c021504060603050d020a05030a0509040908160b0105010e010c020415 80
    0x10002c00b01070148640c2c000312003d100744903000c4450714421007000e142280c100d8410400c03e01820b0052249034601280f0106079100d1510300035051810141204281c2c00003650221072a400000b070810080d41c0000d6400000c20901000c1c1c502001c41c181110345420300200b00038108a0000000b40400003c1c60540d03151300e03040b01550004c07540300c0001968502450080001040404903e000c81c1e40c128001c3c8881014511025803c00c1d001c1114082c01c4480104104407501041c400032440040510501c00204801001d088562a00841001078000340c0c3d04001c1c3c240e00000741e2010003240c0024603010070000c15004941c01140954124240304201d51540d08003c2040c05120510050b03800050035603001e6415998011010304003a1703501c9a100300b00400c10340040c850b0701c2541e40280c000c0d02806c9030140c8081b807403494a0340d903140c4560040e00e115281c0881d20302240140408030b14041e001d047c0071f003060401c0e4444940013900343c50701890028803030764031030794500100c003d03441b00440204 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 24896399 1250 24895149 24895163
    0x605030403050d1409010f060302220e0f060106030b040b06030415020405060a080f0702010b0123090409060c0305090309060904090503041203050703110610030803071e0c020108060f15070f 83
    0x131004182c10702d8109403c2e00e040c904d81d82000b4200d13006800611840080b258010f05a811a0b00c064801d40625034401200c3c90303040da42c0b1000900c1d0070303000f80014054094054094507941d810401c0280403141d82001190040340340c80412002d9848180480f40c0042e00140010004e040258950000c7e1003107400c42c036000034020503041030860304140252300034011440048055607074401d01f00d00700e46400010b180040c8076040140140888174400001d1360920780c5c0c202e89482c100304003040c10b0303521000e0101c9210f55506035940b007483d41881040c1c0c0009124010303501d403c0e0300b4400035949019100b032030fa1140f80c1d103020400820204004031401410f03042810201c902490902400700d800001c0154007141c1107103501c031100d500100c0c442d8410106000e100391101d0454440883c1034000800f00000d01c0f422020f90300c40b0800380c462100032640e1660301c4040640051000503c1c1c80340245c645400740c00c10a0b0402d201e070391103143c89251319580700c441ea070301c030001d81c24240d086400b11413000d8a06 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 24897649 1250 24896399 24896411
    0x804080d08060d0c030308090f070609031b0e0106180503060a0b09010b04030f0303020706090c0e100b07050322090f020307091706041209030501021305030c010207030308010605030403050d 83
    0x20502280600d054502500d90488540c0c4203800e0210400501c10001c0c00c500045105000090040b0603054100128408a400c0305e07a90028881c503103051a00500041103601c7ea0030800c01403501611264855822602d8160fa440c21a02d10070f01d031018001c0400703002803c02c509a401082040000c01000028100d4100b410b2052804004010405002d405014aa4004100301000008a90450341e0004200c040c581c07075034400718029003001078116503054a60f00410041021440144041e0690940c80144ea0030180e0105c0c45044241d03120350294001808400c010400100070740f101aa1400843c654003442050103c84684042d084038070128502650024014401e034081d61003490503890380c0c0380d09030b1504042d030303083c000c40000700c0801d40c41400020005601e07124034072102121804e00452045c2c0381c4c2d40e5982079810045000038003107140b00c070804c01407408004491805c902800584070441c1076890051010005000703c0c424400c00101140816204004459070802604010015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 24898899 1250 24897649 24897659
    0x29010201020c03160201170c033103030e01050714070b070509060d06050301050601080121031e022103010e010303081315050402040518030915070c0602061602010204030c050904050a0804 82
    0x4c54810000d0340052940f48100b1450b24a00003914010301c2c82c00c80607411951007860304103c8042e49454661209442d00312007801d00a5a241036100504c81c1c0c07400720b010300580250508442d402014442044181c048042018242a0403615140e82080c22802d13641e0b504042036400d440340004d04d03504600d0020b4010700d158010b90011040d181d04400a0110307486581c01101c600d0020300503030140d4400008914086102802c4810006100307003420390340c003442c200c540503101c01200c0240d8056040205c907001042c180e81c80015014495002407829541030081a40c2d2240d81400300505020b2414040b644152004d52208522680088cc100d00e0144d420003881c0540b00554089004170b0409002c5a800030100c5550401c0c600c924008609002c10a0100040d040f0440090700020008101038404100c101001a0140020750010812402d210000c542c224070904000021a44140401d00c0012864141103040340c000302d85600d90303500e07541025420074910860080c404840084d0000e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 24900149 1250 24898899 24898927
    0xb0f0d030503100603150504090c0b03010f05092208031308030103061d0f030d0b040605090a050405060108030306180402010509130614060c0706030504080708031005120129010201020c03 82
    0x4031483c0907010703022500341e80d0700e001c1d401e6960b017194403284040a520280140d00b800da0005c1103040c0900c0c080c01c88039075201c80040035a0b0083c1c1100030041c2c0404018000713814881d071019002810700d04d013858211410030743c0001103403030340c03c00404048000001c140101e0507120860b0056030080529a565692880c00e0340c0140351040900310320428440d250341d800800400c180c0ca0440000025514105d0216070340c90050a086c80f00035031099035183c000c1a19124074090920403404000001058100303400c000d031400c0e8059003c00142d41c420010400603440b40c2030a880d05079100c9241090b640c2311480140c5103809414502a0041381c41c0440c03031440720316a040b81c0115445090004140c1c0c0b1100103001e454892243c030f000311035014002c10000c0c54800d40c06958410b0007401c100c0e080401c1035031203141c82c0d40142c2c5c032482012224042032049181400182a058810328001c000c608460091a078030b00c103841d404114090310382081c5940c40d90003901150681d0041e1000c2da03656003602c1084003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 24901399 1250 24900149 24900151
    0x311061c050705071101080f01060503091905030702011b0c05061b03070308070905010e09041403040302030709020409110c060403113301060302070302030f070f0605010b180609060702040b0f0d030503 88
    0x514001040c5d00700c0450f44d4082c080c13280c0101228001204180e007021801d0742c0d96440540942c0c91340c490a0f5061050f410412440c41c1040d203c0d8026503554900c5000040c2505500f1070a54800e10031402d68400054a2549050817188195035590707c48031803500042002c541d08044c0c00741ca00000902c80d040550000c003951080015841c0c030400e841d02d60004480019a005c02560072621b0b4001040c040743e21a42d0f60862042084206d91030a40c6030b0303001c00d051042691000c852a82c000c9001d05c07110505000300d245403100d1840c400e04003a21102c60680c0c0d590080c0000c3c051002c001131800002c0ca0501010340d510000a101c4a003071040803210006800c41450505681c000000012540b03501c24000c80e1003094040d4015070070110311a001902e56406400220380455210040328001110741c001c00b4000d080711074074184ca82c1803102c540116524208001c51003a841080600351940d5007809031404190103680004240c2c0321280417038860748814030150b84c8a201c1c0321000c010164000011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 24902649 1250 24901399 24901403
    0x606020601081f06030c0314160b0a08090a080412030e04050c0a0c06060306050114030106090c0c1403090d11120a2f03030309060712060f0621110301060e0a0311061c05070507 77
    0x7034070066580080704a03227446500441109000c100a460071052141d80442d41200542040d9912611103580d907890a5010391320881c0091103000300f0005160b006081c1403184c0d182a24207010500d07040e1103002071482100504418410210b05080501c469580404061580700030100301c1542c44001162896800c0c81d5400d00c40c0d030070300327001080f880c3d990b0060462001070b40d00c0301c2c200304078103a0340d402d040301820b075840c480c61100344140700c25599101c4244401c42d01910100c001440c4080901c11000980080c094540d40544038240015640003421009400040074154402010140e044c0420314180c851075858030012041c49440c21300401c030389001d0601d68035005044074004041401341c5483d4131030a28203200c4240c04100d403601640d07004000d540704812105110404020000813204202c0808650a00200c01488400e070445029045d60004413880c19206146540c1c4100d02040800340d180200008100c0205040000c03a4060144c8e9408909021320710700100c0060842d0010801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 24903899 1250 24902649 24902653
    0x30f04060e060a1b020a0c0b0f07050109080a1407050607050c01020904060b032a030a02070602070203032110030503040b07020f060c030a23070308040201050903010e060a0606020601081f06030c0314 87
    0x448107185d00008440c4c9038164003120080070343e4604000f101058208078001e0111b4038040100d600024000c0c41280c601d288103500440d29049140401024080d07180d1180b60b40c200100010fa021640000319242d21003014034100e690b80c0780c0c03240f426019004007034510360814180030b000300c0c003010042e01942c4180c250306000383c844040c1142110414046540345c2c51001d41c1000031a00c618625001001c0d1240203100251601c05c0f6a07002c0791541d84003030ba8045075403582201c2e00000c5c2d20310f15841d80e00b0031010b0a0315403210b400d42d11950b0701c0707205520403800c02040002c0c4040864944270310380c0c82d040d03000612650f01d03070000000d0262258868010000014520180788808556401000d580b111b0300c20240c030304200c81a0b40950300044007410607410b0180038484110070307950034002c1482c0c03a41604041e00150400189010940c1c445401400542d08010010300c280b079000143c590b5154000c07006c4282c0240640804030082025800103002405000000310a014400d01e24039421029081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 24905149 1250 24903899 24903941
    0x3040e06090403201501030b060103050a02031005121c1206050102010204030f0809040603060c050406120606020a0f0f0501020310053102130b070311060f0c030f04060e060a 76
    0x208100500400b20341c014046011004220340001005094000d04260320b0100c444081d5400914002998240d00450f00c0300205020400c11f940d2500805411081d0001c0950440c20500320004541ba020f0142c1340c06500301c000740e041c508004205c030300c410480403042400030000f60100217090f003120192251005007000c00002d00c6501c1403085034100ca41024020801040e90b90b600c03061644100c1d081d6a2141d02d5a602101040c418030070340500d22915240e15039100d151401c007402290314004010041860301d40100015a008035080091903802000319070121014030b072141c031840d142030002d80349610210800c014450904d03410f0080d100211018407140703248140400445200d241944c40034070940a10000080141d0040c0400700e210b1007840c0500383d1182e4031200e96400120083c1d0000c0c400303c00c0c0c0901b810081c882a50003001070744816296141c02c40d0410b0981c800a000e1300b842c41060300020f000c0c00660790012840d1551001982c00500700888105c011b040c01900448203d03011007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 24906399 1250 24905149 24905161
    0x90c08090609190303020c030d0c050a03110301080607260403170f0411060a030e01020d0f0513030e01080606040503010903090603060f06020604080f0903030a030504050c041e0902010905100203040e 87
    0x90503500f020b0110283c84984183c40c0c1e822400fa40000c0b105880d14403040c071013280c811141d40502003488619075659511744a41080007019601c0045003500440300420040c400c8810118825038418180d04010003900345540d000340d1100c00503208116285076a83c103100030994002ca05c50940e411400e400841074030740101e0800004001c1c3e0700140340580c2d28104090b01c0c14440003034410302d503e41c00c2c001803540c0788035074440c2a03038000700c00f8031042503440a058a1f079074070350311030150010b050310202c040111055802801301040441071606108e04400098210b6580200b02c801070103000d4000e0013007100e1803030041d1070080c0c240940404242020f0340481c03040c18074007250f02103440550040c0103d0f166611880250b03806007001d04c50070b00c0e00b04001001c5450802c000c1c086060170f5a8000354500c3c103420f090f410080032a68142c8100d080c01098104800c40c0c0d4840100350070300c180c001451115034401038500c04041d50000d40c001c40109006103400e600440540300300c03407000d0204911030f5216 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 24907649 1250 24906399 24906403
    0x80607110309102001140106020c010801120606030606080c0f04020910050714030307050406020d0206160e0d0b0c070b1503070315060506160510050c0306100207090c08090609 77
    0x449820200d80d401440100e9091030000e0950900100c64107040c4281254143c0c0c88683c811425415082a9141e00004403d04503400d1054014a102c0c40035201c0300c070411000030b1502e4010302c110140d40b0701c04400d0b9024070506a01c000c004562049040002580c0e6000d80c984501c3c1101440d441003c3d4450a10880d0900e4000c0790ba001c48001e00000c1d00000034802528140c0104900b501e074030054002d0260743c2c0700104000c0d80240b80c503464291300da51030680000d00d0448200110011908068203003c903058100720200ca5000060428064000113480441c5000c003508001400f0032121609000001c074400c001400100e0081140040179035038140514103003880c002041e600b40d4000c4000b04007046596042c2004480482c0000c85d080d40e0740c0740081d01f26044500c0f210400c031610035810342080401c00407589800b03c89902409140303403030070400520740070040040340a03101d02c28440c90750f02d10911040003d048404001c0000112100c0010001b0a04598041540c03090354040b461386040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 24908899 1250 24907649 24907667
    0x309010f1a01032405060708072019060914010507020406031112060906010603180c0b09040515010905040f06080a0b090706020a080a050901030e0307031206060908030403060506030c0901030c080607 87
    0x101c5005080c000d1405c4240100e90780911400d54510300c080c042c01000503401c40800c402d4001c00301e4030044a01060041040d842e521541000501e442d18804021098200d0f22440403280f1080c4e4103401400b480380103940f141f04050009510614040011040007400f03104825052416209400851042e508440c0d95030025200c480d650b500000042200d5486a04040408511020001d0700c440942d55201c00e0028a50408889000e011901210600f40792181c03e5228080c403500552000ea6840041c18118442c042d00c3d01883d101c84100840b41c00940007a002000007000310b4024401c1800c1200103940c0650b0100c00c980100003000503003510000b40340000170303042100d00749010050a002d0301c040c0d200c50700950500d500c2d054409184d000030300150080138000d07211079112440705003480044803075580050042c00000071003030044101c0003080e60183c981c80100081d1a86407100080d2034851051800390380300c04020004800c00401070000c0080744c8030802240c13682d864078807007a03c0680c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 24910149 1250 24908899 24908951
    0x140a0c0309050a0b0c0403050d030911040b0d1103011b090503010f0b0102060a0504020a051002010504050d0f140f0405030601060507060b030705131505030d110c09010e07050309010f1a0103 83
    0x2200d00741c0703c00421002201d10350801641002d80e807509030f4039a81c41c1e00f0070580c5090310021a03955183c500078401f28800607007948800311010089410100002034810034044000f0707160307044000713100c0c1d02520250f00c90102150a02c40558440b010b03001c0003841c034038940c0580b80c040d50801221030103990341409980802c140c1600500b1680c0d5801c1c0960300100340007401640c1c0950000781c0054280c030340807207403106490345600115081c81d041c18190f02d17045510940100300221802c072081d6403948038164991000c0d501845640d604070351014001c0b10301030b1790482a414002c481c00040c0c8590002e0003010001d1043c1da0511803208080f04068440e4141d01c80d60340c001c4150300081c80c4178000b130f52000307122440107161050496202c0020038940b800c50810400494404000c02882c50020044800208021208a4090345c10003c80c4c0c901054054125010300c107022000c544000c41c20b41000c8604c0100700343c10031501004c818520504003030207402c0f901003890818080140e0003205405001d0380 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 24911399 1250 24910149 24910153
    0x301050a09050c0d0803011e0506040e011d040b0606130306060b070506090c03060103060b011b0305181e010c050708030c070609051c02010809070e0109050402010f080702060412090306140a0c030905 87
    0x20b0300c3c0115010814031a86508d02440e260000049415916040504050b0415a00c0900c10f0740c14140303100c001c2e0800b0072082c00d0441d000810400029a4005840d501c0f200c107640103900c03400f108080800401c426000100a00c4c2040384c0410700754445000b504040c1c1c019003c030754031071701d900c600a5240e080325840c468043c2c103c1001840401c2e400c0e00014010751061500180c20881c61641088580c2c0850003100020301c0000c40c1243c03454045088000d484c1d0803900300d44020324060200040900c242c80031418041e0f840e801d0011300800b0710031030008000360400e40e03503115244a50103450710036501500c404100759107804200c5003402603a1207840181855402204502c0390010b44481400030300404140c41100c0c404140c480384001828020402c01c800070506007804e00c00507004214a071389031410062040100040c09500040b10b0390040d0700314410b2a6108185007080321f282c10642c001400700f90500d00e0040d00400102400f44c0310300c9030520304221408801500b1419201d0000d0302400903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 24912649 1250 24911399 24911401
    0x70201050c0c06060f150a08180c0604031e12030504030909050405060402010c1401230703181502070204020f07050f070501090303051303050f061501090b0307030203070309020301050a09050c0d0803 87
    0x1383c280035807801e0914800611000e00d00c140d00038102e803e94403034850140061034071424042422003941002e540b040c0040041c01d40c03a00b182004c01c035540582d2002600041140155200b010303244140201e0140d000144040c4002c150040a03020b000242e0741280016200d40703002a00c0991803007198040c0381c0c44409408a500c1b29001194441d42c0d01c81e040c0c41280c40120811032016091181c4400c65030001a680c4071500c3d142c408100c1c40e2801488030040c0750914140c40d21007140200200d01d01a80704003002040300070018050000d008021009420610025022a11100500140100f24410002c8500501ea4000c1c0692100194811180448d900c0c603020b00c0000c0c0200081c144c81f0394400c400c00c861a941341c89051800e0040404901240c00800c1800003100c01d4a8204040101c05e0802c50704191030b0a0900180748030080404081650200100f14071a00c07980088494940042c000e0095013010440c0000402480c4000c50701c030300c202103504281d814500c201c541e045070044025815 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 24913899 1250 24912649 24912661
    0x2090a0b0903100c0c3c0309080604030306032906010f0c0b0703091403040501020703060209210c010201140f040201080c0c07030804170c0307050618060c06070201050c0c06 76
    0x581c0140410396810f016050240440c0c034414481c2d07040c80d00c880d0303a91080588640c2003805460401120200c0d48080310842c00b207038083c070303507a0741506c0c401100030001d00c803106410120341c404840d4010004a0040fa01400300381540f580006054074000ca2680c0784020210a20111555994200841504030304001900541c0514038560503a003241c01c0034041c000c02e0390740340b1840c0b4030304499210219543d1014101441404061f0817202c82d03007440218035290a10300080e40d035031807910000741202c1d0002699110703602c1c0c1c05030742d100038001314015080048000d0980c503200c03180f01c0c0c100e40c0158602000100384e11801c3c0390040c020400131486e1022600e440c0c004480c4107078010201a040881001380f400000320803c05500114000c6951946807400d0070a40e20079044190310622055101c181042c0c0240e40120742034003111742c12075415581e48403003030030444089030700d102c80c03a801140071600081c09400420300610071401c0744d008019655400b010310b07845003e40380c40004558020710020340d07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 24915149 1250 24913899 24913919
    0x405040c03060b040b04090602210c0720131b14070f0611030a050403090608040206031618060309060f06030b0c030c0706020a0c0b010504020a020c012114040c050402090a 75
    0xb226250103000400c000c5c00d02800b1500740c8052a004541884d4006403000c420041d05006510007030b1075a42505180c1020720000d240d1f4010098058144400700049030180246109210b4241d840034013141e000d00c1c01d0030109001014940004403650702c55500c0c0c2208940f01705a030441c0d502040800904180040e2560000300d0004d00d01100d9242e520040040001140703c060b6221b01c8009030085a1340c0b4043c54002d0058400703500c8401440f0484003440016a504010f4990001c04101045034801801c0011118180354450a00000f8038000020981c550326804c03030341038940900340c140310350010880e8041c21504107201c040c0c00c5d6206c68001c11031440c41c40c0c0045800481d20b2036000d0400000303454900481c6e00c03220024010070150030740c00040025410b1458010300045070210300348800031f0302c041e40340e007040d480b100d0400030806480704072044148540b190002d801c0b002042038101c0981640c81200381540c2c00d5800c1c4040301e030005404c2c5098021074240520151030203100340d140c404508 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 24916399 1250 24915149 24915161
    0x40812070213180c0e04030c110102010b0604080a050114160807050702060f190c0b01060c02061606200403051009061b0203031503010b0d11060c06100f050405040c0306 74
    0x30b0748003440544200c80007400d80075100412410461010034842c0c545014054402c2035484504403410620411020035003010020222603001080e1034401e06c2c040004074010003400b20110340c0547c0225001c5240100002c1048419111308003c10080c1c5184140c1d0441c40800c98071044824030b0340e805489283d1103841e800d0303000a243d0501904001c140e0340000c006422800142101c1500813844640c40c08501e41143c26030466030420550101c055200c000744a801405441306001c1002c03d00402c40d1140003c440c881900400e46038a40951441c1140c0500170020340c5020f04110100004040040308048a080b40d912200a02412992480c000040d2420341d6040d60340740c0d594102c1560811094054200c103502540c0599900d1800c600c1d080c8401105d490040c2c002c1c0e02d00740700c21503541c40780762074520025008003c5d905c4c2c081340900040d00750320030555241158012207040c0010724200c1e804100540d075443d00010004c0b0348130010300c81103440850f00940b50b52640201000440c160b5032140c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 24917649 1250 24916399 24916403
    0x40501120204020c070905040807060c210c050c061006020d0f080f060d02030a050105010e010b090306060d0512070c080d0f080a0b01020c030a051506221e0c05030907080304081207 79
    0x24460303e0741d40d00c846c04219241102e05443c000c0c0c001905800704003041c070a0031089201c6080001e80c0c0082225444821407491096006940d920440c20104600a105950303000b0041c100f00c41c403524081016009416861040e00054413078545c0da55035260203110074440c180c08075a500040da83c0d401d20208110703900580f4058015680e580c90b0800740e1014065030741d04500402c00810700c4c0d49004a210003800e030503400400c03028428490807543c1d0b0b601043c8290010021980010203800506000c0c4c103101e07011009403d0340780d00203900004c00100d210b0070070440d070a8100b1b42d8404000d5030b0701903495407410010100000c03074a82c00180020f00c941c0c0480500d02c81807048601840185001c245050940303c01511681d11144a0000d04803003000031503403200c2c041c0c4003c294540c2c801e410701c022240e0f1f000c0c010301031601c03840c0c11900052030141d03030503441c03020500501c880b900890020703001c0d60003a16841844c2c094685c010a038401c002046408a0716401e0003000c61030003000594105030044482 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 24918899 1250 24917649 24917653
    0x70b04111c0503121f050d0501020906030f092104090903020c0a1403280f030c0b07080f070309170703030e0111250201020c0402030a09050703030e030c040501120204020c 75
    0x1c054811611400303419000d511a400650355080f10001d03400344018020600c000d40b800c100001400d4010740888107007194410790f440002407410745032060290140306d0740241c00020100800031103242d242d100600074103400d0296a410341740110200c440c5407807906806120b0100300001c00040a1a82c0a103c81c1401703441aa255400b50340300003141c12007240d00007000d8280d01007400d0020300d4244a030301e000441070340341600000d0441281c640d81e0121903c014202d000346000d2202898020628501c4140e0b000c0c0c0d02030018035015002402c01d40003509c0403070041555000107911117000744180e0410761340242200e081040a04940d11035940664401c404040d19000d80c144003040901843c800f8566428005407030f03e66200c6940920040c8070780e100c10784240c0501150140c2d8000c81c800a1100050383c02507603e035039001680340500780c034850080076481142c600006065000901101800c412420303075041910321030401064070400c0c0030303081d48081c607030750760f0001407616900400350294940c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 24920149 1250 24918899 24918919
    0x31306020903010c0504090c0806031209060c030f07060501063f1802190f060315050d05010c03050603011a09090a020901150f110d032403081b03070b0411 68
    0x101007801d41d02c0300c544840c0405d6010070188102c4003240074580540c0607c1ca0060101d203004400030381c4d02c1450a6020454040001d9080003030386801c01103524508940c0100c03642c0740d01030181c88441d80c0c88000c0681d005403030000003249591245000411902100414040d40c810040c0d40050381042905c005180416144000085000600a0030b134004603150611a0148290062120340c2004100d114500c050386201070181c403100141d00700c140c5926260001d2030100341913941505a829410079135200700e282007034404000b815084201218075903603062195031600d90506013030315004401101490a800c0650401c2d04080404a5000d011001141c01d0b02d00300d5008112421020717045036030b006a80b001d050316181d030803080421561074646841425003e101d1105601c0e0300c3d402c01d510081680f100b9101038503100141e071110103564880032101c040d82e2b8901d80090b440d441109026403000d82c3c0d1550351110b03940442075a0219421680d0b40381255590356032047c1410984200c00e601c0381c1009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 24921399 1250 24920149 24920167
    0x218070e0414060301060504020307020d0e010c0b040501050712060503030d0906020f0a08010608060105070f110307031b0f050904120503041a04030302120f07021009050304050907020c01090b090603130602 90
    0x2c01004001400c1c0081000282041030516007903e40941100d40268010814814a01d07400559000040007610b8082200c40c48000100c400c1c16842c08081c0800c45881c00380801e000040d4041c9000c1e5025460320840c0807409424801170350348034481c255241d0070600030441e42c1c6a403a00f10703507103840c0300f00d00041c5091a08041182070342c000340341708000680500300611000750000c0c51590440c60909005040910707658802d8414120302c0c2c8020584c1003814031201a81c0c4042040c1c40c055035119017420348040c410059090501240d120702d42042c01c51180028a030300380b910550f0301413500228070054000700301000b562a58400703402203603c0110085030201d007050740301c480c501880c03180c0e030b0269440700c400703058010045000d411060300301200402e01c0041500062542c0300c1450b03004003c1107202083c140f903030640c0555803055820443d04030800c20b2107a8042074014144038240c0351002141c2e05d81011080a010b603078800c9070090340c01c10128040581d42481a00042e22920000d403401c1081c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 24922649 1250 24921399 24921401
    0xf0c010603120503040b1e0106030c02030c01050703051e1e0615030702210c061611060108030d05010602060705040b0912010f0902040506040c050904050406060302090403021b0604030218070e04 85
    0x1024802c030001d180801444108100030f03031070300e4028124518003644901c1c804000c1900396010320840c0d080c51307550091034640c0c0d8000e0040e142d407400850000c001c5403816503000b401a0100722219502012503807054007142d40101e181600a03000703400c0403030304121030076940030b4841e4001c2e007400e600c9880c035581030340100c0611004602c10380455003c1d01071817080081000c035103d003080141000e1a0148001d002056001031aa5440401c00c040ca40460300d04104c00e480711001d511415016000d231100115000c44004003c0c0f0452039510010450740c1e82e201c20072600c8607025140e03240041c1d0204400c00118101001803c84e411008120303625516071690224210f0b02c0288030324070170603294181c2000394500b07803040d2035100400340c0b800d00101c809007100030b05900c0350440844c4210340c0c0f140801d080c440c4c1540f00101565002c0c000c0c0d0844c0c206402c010f50359800d10701500349108001000601d11b802d2403001d64085940c0038280384500c0f09a5030b102000a180101644108541036010318041d50391 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 24923899 1250 24922649 24922673
    0xa1d030a02010c02012909070504080102070b0405061015080402011214090f030306010c060504060f05130b15090a050406151202010201060e0103030905090c0d0c050a030506010804080f0c010603 85
    0x10381e00000790703401e00e1040c040c0c291440955098070030011311250300803240c6048070b003090504044841c3c01e0300c0e90f00c03100140d819009940014000e1b40c070100725207003000905204d00e800381e801001103944559078214802c000d0000e07401241c0310785420038000100c03c0d010300f050355005441410040320080990072031208882c0c101004000044500741480f8001780148003000341da8001c0000b41d031443c500b40b00040c00440d000350b0010300c80b03039a035800103040c404183e201e140072186400c000d1001c0d040240c2002c1440701811026a155150800821101109002003850030311010300a00000e5580f101c5a0700182401041518000c1d294030700800320040b00c4007424040c3c001e12503040e4481e811030000908503501c0d900301001490301d00c0014804603820907180403c56a00321000801340c0ea950741418014015600e10345025801c0080d00c1012642000140203c44550364003080140ea90000451b00020191000b410814003040075074034230640d000c010104e08690350000714407203507a5a40c010345000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 24925149 1250 24923899 24923917
    0xd21030912030c0905011101020c010c0801031403071a062e030c020102160210170a02190503040f030f09050312030703150f06180b03040507030b0c0a05030a1d03 71
    0x16981042904020210700d60001584091030204800c101a030000340202c10f40b405058140140301c1034005c145082501254a00083e0758000c2c09104a890310142c4800c400380422100000e50341c9007030740051000825504c0094124000310740b0b681c4c4403c401805854050450783d00110081000d000300c007540c03200c080d00e00c8810b809070303010340107040760007021034a4446a034270441e40100000011607035401110903890781c0485045860010440c3c0a640300c820130181d05425045860400c0a016696030180209001c2e185d50451190440764080b80d00d444202c2d070082031585804252008a4070400724004003081ca800c10078025511440084d103414100c0c020b0418035800002003240b4640cbc180100704c07080d159003513104011030805035210404202c038040c0400f008159040c41b141c05903030b0300c84200103200e034072500342c0d4034109820015103e070442d020a4070f07030b0000c55010030000301c0c0781400c943d41030942c6c3e65120300315140c0722045000b80c400303401c0440d440e5108c1c405180000c0c1c0c01f4401001481 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 24926399 1250 24925149 24925151
    0x1a030a050a062c15090a02010c0215040e01181508060f190204121a0405070308030a0f02030702100c080106120b030307020405070503011505090a0b0319020d090c0915050d2103 77
    0x501131050000c0c3c141c0c1e00030702460f884d4004154210040c1d8100e161080d03155412251018103400c00300680c0c00c9405980c0c0720418890110000081e05000713240f0580b0700b215540002c0c0300f1085c00d0105c1c6405654148158403082e400000000d0001c942c0b070038015002141c0d40c50b483c42c5000340c45602d9090b81c006400106c00c0000c98000c403401c004560f2108100d000c1646588482407902d91541030f00c82c0e94620003e0300303101d00040054004c1240d580481186501c0c2e610864aa0410101c000e599521424420b14501d10f4800500c040758000d0358030380d04072452942c803c2554907090210300e001d0485100d186400d0f10044c0b00c590016030b694041e00c0d01c2030203da41c43c00d440758540004580c0c92101c2d0b01521044c817004200075811038807280c0d041000c0c3c0311100d606e03030764035140d0051451a803522004105440d61001c1003106050100b9040414841d0280f00e1642c130064440360b00e041154140c1d10740900c102a010410045400c003880a0074180780202c0c1000000f0b038924140b01520f20607500000c00103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 24927649 1250 24926399 24926413
    0xa020a090503010c0503010608070302090306191410061101090204020304061b05070210050304021c0c0609060e0d0b0402060d06030606030312020304020f0909030403020a091a030a050a062c 83
    0x15940480c640c00145411070007800580c20a0308094086e2006010340300c100108680001d203140c0c002c1d01118000c0d01d01408480c11450100800c00d0b000850040b00001c1b0b5040084040008820080d098080c6000c1111081414034000055460034202c0c40303003040c15501ca05009000d80e40305e2001c4d41c426805410302042000b64103a11000030000308000001f07011040c006903002d40c4842c0e080040041c2c4500b0400d980c0c1e2102e0002032280c01d0b24141c900403c50201c9107910030002ca1a04540c101d507019115660102c3d1500d03001c1d2140140c840945400c0314444c41000c000c034a0007020b42d6080b40c0050b04032841c040c2e0100210040d03c5507a0003c0e21815141d840410406510680016640380d48400840c114201540007500902250220350700c14518400801c44201080c4129001594020083c0800030342d0382e58032401800840c11034082400ca0716580700c070b0b5800e010810200700c9a0002c0a0130801c50b660307586a00900310703050f4010400c07801ea844410300b0610128580d6405180700020005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 24928899 1250 24927649 24927667
    0x305010e0c0a06020a080301030206090a170c0a06020703032106120f1703130b040305040503030d0605040b09040206030a0c0201110a1107051518180f010806010602070b0406031d0102030a02 83
    0x1040020b43d008404561100060501149005081d071781500d130304850301c2e0751b100c07400301c0016400302d003641004854600301d43c0d9241c0300e000000f94013044224207458500c111940c2d00c40503626001203206c0500407544c4d90240d004081407200b000c2e040111312542c0026442d469040d909500703580000308071b8224007008200710521090b04152206a40b201a1461841c50001d02c50040d04400103401400c005a0101140405016005480c0601006002c60707884220079121400078082601c2503078011441c204a9080c58201a541d880c810f64001c0c110302d10b15200c0030510740041c4012100403045560765544440c05060280c01880340c5c6650741c1e20307441c00300a1340300b500b4103006d003d50081e0310031307105640c240e030b2443c0740c020694405a044540007078035040460007050462286010003009903d1040c04c00215060060042d4103803040641280c40503070725010701b43d0b55a8800d000f48048184180000c0004e90311a401c01805500c0f01c1900d0002d220741d500b00715003660001e90707102d020a500403d146034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 24930149 1250 24928899 24928909
    0x40203100606080a0f02130302010f02150c0909060303030105210a0b160201050a06050109090b03010914240c030a090305120a021e040e01060503180a030201020901030f05061e0102070305010e0c 85
    0x1951755040c1000c529003c0245003180307200c43c8600c0000c3c14456014240d4035000e0091182021050114400203482e180117280303e191a40100340b070500c1103100901241c81405d001060700d05898024100d80c00310701200c201101040251000100a445654014400682148e10503070245007251040d030b4000d104040040d00f591070084c0840401ca01c0c00104004503030f030002c4aa0110303031210100164013813501012a001d4040c200000e803110134544614000c1490000366035020034403a0b04107008031003010b41c1e80001c2b0f840070749440c1c0000c0418004641c4282c296840900301078801d0400038a00f800d0b030f00b90b80030b03017803000c07110b101d40254042080c04401001c4c040d082480110100014030b02030400ba0001d8541e80103020360300400c103021000070502050710340828100302d2030000301c80d403007a0390b494024040d40c1701c00e152a000900700149a4503806050069034010362001306000d12011500d9880c0e4040c06940e203a0504500c90301800202164082c03242c8000891460017810020f5a88400d020b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 24931399 1250 24930149 24930161
    0x2d09261b010b0a0b0d0209030303010b09181315020403020904060615020309091b0f040b0301030303060e0412030905011d0703120c1709060f0307020a0201090e150108040203100606080a 81
    0x319905105190741c440d511180ba480a588800c64015242d00c00c890110009001d9160842c0e01031200000100700480010050182a00101c500c01d15040c0304481c2c00341c20810a37182c00c44034402c5400d03e00000340e82e0f910207031140c1d13003e6000181483c1c0c1e2a00000e85043c0141d4080c2d070704695450050007107640560f1111000621030000718640f030f00c44804560b5070040104020b02c1c183d90400e01c03592092a5000715240c0704503110071561640c0e26149010090b50080c07208401003440c1807000540746070b41095403407056400c8180c40005480304403040e00505001007048840e55a11612108100106100c11410350f6141d0300400c0c4240c1549882081c1c1c40d42d036189030042c03000c40300003400002c7c11100d0300c60b03950850018a41d20b514a040209041e030140300c0c0c404600e000c011040007011a030008a0644843c001d0b070f103182c0b00ca9510207580003880c0d010784603001c110081101e1090194081d03d61036801a03c0a011100a2401d01c480c013421585190001000140e0940a201045429010368 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 24932649 1250 24931399 24931447
    0x40606030b010c030813080f03070201060602010c090b09010e0901080a0201030b060702030304170c0406171b03030d09080c060408030402091e0615120a0e012d0926 72
    0x1c106031044400007a001d0024600020104106400002c51001144203130810391640b0240d0700d80c450117481068251703900121404401580b030660001100340c414040d00540c8501c548803664a241840d00c1c10840d070340414034035814400103001c1c100c0c240c1c03212000d507030003007004801030030f0f074000c503840010140d03480c816542d482804c040c0b20f8900569004001c6408980000c0b84490a620000145900300302c032804c7c205a0161a0600c0040d00700102941d1026440505040e00c001100c1444c0c11290701e0042820b07a50954000e10110b032007400e4650052124074060a405810424103507070851505000300c03400c54803402c010040c0011801c08584190300103041c1800e040041299040800020030b009251034414481c0260040d1030480040840701d100140490031609841c103480004054101c882560300c1c15803a0010003852001024640314400c0034400e00c040400c9888420000541581203007a21508076481101440c4400900039044a000058800351501031200313180764071134280304103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 24933899 1250 24932649 24932651
    0x11160302010503090f1b0301200f1b0f060a110c0a0b10080709061a0304080315040207080a020d0909020c0601050402031b03040501090213060308030402010c061b020a02030120250204061404060603 86
    0x32501c4c08084503420782e041800350b40c43c3e403500c03401942c0bd65401c1c81d12a6840315414000d9039003a101c98000491114450314510509028911991101000500c074096041504d900010070210000c0c5800d031800750080004181c8198144e12480c400f0308080c0254420744585698086c20850202d110001d0380a400900190034254909a2944500c904c80249070f865451103003503051215aa440d815180380d90f4100d030955890311600e0034041d550b006020000c0020840032000080e0381145030003120402c14040010306110791900c028000a500040c240c0318050180751410480c04421101940c440c41c01900040703130079807607070042c0440d0175101100c0c2140e4506100e0180003081c184400c4a41180e420b10340715079103245500784100200b003403020f410444420710b01078182440c1d00103403200f51103000314003c00140c2c40c0c040c80c4c1740b07000d22414030260f4110010300c0a010010001d020704d88524034108480d60009c8415400241240c109812200c05960040a0030747c0c1e60816101c2e01019044a0030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 24935149 1250 24933899 24933941
    0x151d040516050102030a08061c05030a03060e060d0303180501020c0312060303040501050a0807140406090513090c030209042607050c040501030302120c100c02010b0111160302010503090f1b0301 85
    0x5c0d200d10a00c3d0350001489070040c040b400b00d403a8600c1c0ca50700188400741c448108111460400e0701d903032000d40c0c031800290501d20041101107040c40502e0003054024410020400340c0c1e036098015005021100f07000902c441d80b4000414000e000034000c81c042c2c24095507840c107c41912030b1200c0b00181c981c5000783c1c8248070138481039070408110354000da01401c04000540d507003002120f2140280810415134200400e0008146030407180c00c60070f4400c00c8491901b0014800c040b8002c80701900c1018045000740d00040016040c0f45030303032036006401011210703c1d003559802440382c6aa15000800c004102c00505507040c44018840e01c40720860460b000c0c0425491903c009503100410705d414000e501303000880315101401080310315407441c840341003800509190070340a4002c058032881d80b4081505c10440c80003400380800c42d800b4410200541e280807d065400440d8030303410061400640c0d01c6491100781014901304034064011050080c030344070014180b424127083d103810883c0c0300c040e000b0840c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 24936399 1250 24935149 24935159
    0x60c070b040308060f0a0902041a030402090c09031e0a150c021b0406050901080304061b03091503020405030109050c0a1a030a02090604050a1404150302010e0103151d040516 76
    0x4191140c10030b03094903200d0341640703440000401804540081701e0348a6182e031000503062101d03401a02c110b85a41c40e42420810516003e4450f510086034000d5000440c40b000800030005107014121046024049460800c803400d801280c51041060140c1c003580080051030800c8910702d10b400070110040350034013189aa00c00e001c2e503240c45072031000074056078210f5011825155036000400910303004240302c081e541e440c00e0003616544140036060000e489114960074190035080c0a4640c194940c1e5004071a900d00f01c18440c06141117160101019001c000004684e80d0034003800d2079890140d0042c04221070340c44200810210745034040c00000155884074094078020205480c0d002008160141e81c43c41600d000034502c0c41550044e90744001d014a02240c5d03100101d494440c0a00145c4040262201210041904056500c0000e000404103504020154401c1c0c1101c0c006c00003481141903002d8a070001c0c03a81550241140b107082403a05c40c00c010602500f088030ba504002c4080f440c40c8014185 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 24937649 1250 24936399 24936413
    0x180c051507330609020301090506030c100804060b13020d0c0201050717040c080d02100b0109031101050d150b0a0207050f09011a0409090303020a080709050915120a0b010305060c07 79
    0x1d02c24001d800022103004103850303003401c070300c0b091200c1021000308031040c1c407504400002e41003030184666851803c80001d00c141130001d600c041c1d0880040000c1703117404c0c0c00b000450707040c040200100c1c1e40c02d072501d40350f1040d0748034800240001180e200000d82c0b5820406001002c5550400060f000c5a0514040c0054507401a401c41410b00302c01c404c105103569281000c601001c0740358001e0305c142c440d607500040c03866070205600c003143d0f60b128418091907024a0044415244a00019040300181c8211544540c020f80090000740b030346c0d1101051080c6400803010408a941d0300150051070006003511001f903062000ca40a0241200c0d02440c44c2803560105201200501a144c0c800d080c01c12445206440038040d9401401c1d051401d00848881d803500402030b401040301000490301401c0400c0384180a8041c6d102a00c00c0600800768950380d102c1440050003000400c03d0300300d000c2c0070b4681ca03140410b001c450079980c05400359080551452a03c1464a82c1c0100741c2c002420040c00b1100000d418 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 24938899 1250 24937649 24937673
    0x7020f0406151b05030c011b020102040807090507360b040305060a0905160b070210030b03100b060f0301090501050f0303070b0411012601080609030c0a0605070201180c051507 77
    0x5589055441a860000d44007404511240040c00500c8007165400c1c0b99801500158106140d0482c01404100c282320142e00340e0045010fa103040b40c1001c036051103150700c40c0c0d01c07260b0b0144141c0703800f001d00003d01c0743c080c10310500d49c9035031800300c810300039030401c40c3c0d10701044170000b0500e44200a02c3c1c14034645a2503110840541800e06003a100e8116105111003004040f144258502e40080d4856a440d00d408250b4001c0404a014000c86680c0c840300c4c5020740300d44000700002502500703040f00e07014042c9000b13099803c0c031103602000601641c003021060001171400781000c403000080e994105402c0103c0c00c407860515610a9004200110000d08071101c20f6810684c0081a41c0340c0340010740058424803c0e400142001041400c00c0c0c54144c0d0700482010704032103103c4c1c1503c95130345809844035142c0c85103c01e40f0003d81d11019464002031a15407020303034002038920000a4052136491f03c2d8080200485040d030720080c4001090020380f40c50300014800316018502e1504d494850381d185041075907 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 24940149 1250 24938899 24938939
    0xc02190201090513140109060e070302030402011d060c030d0e010f0207050a030503060406030b090102030f010603060803090904080c06090a1202030909010521010c171005010206041502040302060f07020f0406 91
    0x1056413210b01c104002c5412002c8240100308800315690303116070448000341100d11a060340c100112020888540c080d00c00c81c0d02440e0184d440d665200121240c0a04c000c80154000c0d40010082020201c05041400a011483c480d14000304030040c8500c0c01d5800d60382c840d040984113070300c1000404000f840c0042c45d950384540c14241b0584a945020006004000640c070181105001c0010400c038854103500131841000441c481510f640d80b910700840444506004a03600b40c0d02c20020070006252003e11a80d01500c1408603615020f0300c0c03e41719041100545501e6910340c810b8855004201654400d41000c1c8007620045d400c080000d0b000510308001032003040d0140c0e00801d2a001d55805044540f400c10304803100a22940155000042900d040d43c099000e00d1581800407410314500840840c0403a18140d000f02115100e9480d0099414400f2028506070f0342c1c02c00001006031116406014103d2210103426122081c038014003080516003c0b91078811440e200091148000446801808003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 24941399 1250 24940149 24940159
    0x2120a1b05010605090c04051914010309020d140601050312090105090f1212040906060203030405060a0b0d0f0b010e0906040f080d1401090209040b01050c1506060f030a0c021902010905 81
    0x300301401c14a0040816820554200c10454100101c603865000203004a8405031000c0d0460031200e440300e00d0b2480e1601848031480110034000c000ba61185d0030000c00c190008120701d04613002980c642d802040000d45504185d000500100424a000e2107150381540002030058079010b58000004c10521483c2002445402c60b50120315058480b284501e14244910044552800b000c0800c250160094865000c0c11414103101050b0648040180d90169500c400140301584604100310050403904241a4000e00d1000041c001b08034144010f40c10070b40500e06003980d650400e404031100302c40062100304954491414400040c8422a00c0098207400c08041030300c03550388907481000323030090368041e0b10003924000005c00d12440981c000c0c9511202103e0401802070100f005444900414081001c5a080071200030a5143e454900640c41366000340082e15101f00050f00380860f0b0400d8a140198560303444000021a404226007006221f82400024800025a000a29011003400780600074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 24942649 1250 24941399 24941447
    0x9060111060c340c050a030b06060702191203030c0309050d031505190815010e0c0901090b0304030203070507080705061e040305150717130f02010c0b01090c02120a 72
    0x1003000b06400300842c150000030000f02e104500325000480820382000c3e034a65035140400a038a14118440504407030303000724507284a80d194400c020380c0f0382021000f0780c1c2044070800806082d00d90300380c20074007030701051404c00407440c185d0400030100c0796450102c9080c507260178041d030301003580015041c1104189140200d006144c10565440b05400e6900a50b00301c11072a012200001102660b107060340c0300c8000310f9291054500b816106c1c0b801c284260610040c0d02000708030103e00400c010001c7c043c0606126410329a9600300c0112079004480540058001099650810105010b03c50080c1402e40082c50740504110000300144507845501c41c800c2ca0740b000315030002c03100d2020784004581110a40700c082c68400c144640090b011580745000520300001c260340d20000d50452401022041d800010f8001d8507605c2514030703c40c0030020303414007242c2c0d0b0903100001c07820b00495018004064000c15445148400030b0f00d4065200a512034008003408000941c1e58440800c007450309114100005e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 24943899 1250 24942649 24942667
    0x3120604051806011203020f06010501140d0207051e010510030b1303030612051f0213050f0f040e031305010206220807060c0306140d030806010f030e070f0509060111060c 75
    0x10140340080c40b9102d80100c07800012241562650811154000d400f40d9090360111140740d91250824000d40c0d010540300c007031314081d66003003002400000c1e40f507900041c0b40100300c1d21000d1400301c0d00c90960f07403200310040c25010403a00070b006580c0c1110000e40481c009a0035a43c80b08036040c070003020680d59440c462041e4081c14420341011009020b25041d46000c2103803410001c3d2210f040380c20003510b443c000391241d0608801c1d8402c55010521070260100d94504000822880c0c0085554441d40146500704000c00f5940e50712410032491911002144d03074044100707001010b0082e581c0254191b4011400f040903403000b47c02c1d40000f100385010b05134001c0086141107001800396075400703407100b49842010307100f164040d030125081ea0300741350a8101302d9210200308580e00c019060000c0003d4030840101c1c0072075000d000ca080c034220913420046000e07a10385039601e2400080d580220301050310070300208041c0c10045507054101c0402e01e002c0c03030440f480481155455901410304d400164000544e110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 24945149 1250 24943899 24943921
    0x20d0e03070306090b0406051014040f060b0a020a0201030b0d030c020607050f03180108060d020d060b03010605060a0306030219030507030803041113050702060a06060905060708040906030b0a0501080312060405 92
    0x701542d0f00100400000c116828401c5d51450101c60807125a840c0c5000720314003035484104001201e8000c01d0301841420075800b444060403003c02d54041c591340303030103000c100044580040c000c1c6500ca540146440c41c001c1c0001829145e2040985004c1c000020195001c02e521105200c0941d40584516030750700c0310b40c50218a080c61a85005083d40408211000755408050803154005400d0362445400e4584808205c0000c1107540000c0d030008811103c40009415034200d911711500040c0009901d940d24030102e01d5035417107120080c000a642d90710900071490702e01d0b01c0845407150440200107550940d40c071a9550758640c000603000a1001c03001074208030000c0e02c28660300c0c03406058154141c40480070f1074080c25056a80801600030100040c803803047ca4443c40003110b03410b0b550030021919040a02500740c0c03140d0000d88518504000201d1910380c1e03401038000661107281c20305110701d090100301007181c1c2d040e04400525027040080601001c1d402202540003a001c8400103695240c4414800f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 24946399 1250 24945149 24945163
    0xa091b0302160501020a09080c030c06030604090501200a0305010f0308090d0c03150504140604080a0e120307110306070509030709110c0a03050d0b030f0d050702060f040801050103061a01020d0e03 86
    0x800541c0001000c400c0c00b03034400800d4040316840e04c110f601100c0250200368840be940040c031b0307400c1001480020760502d040e8001c2d0031414060700000807028158184172540340d00c1c0c14100b401004c00000e80d00c4041c0c0d89440703210700400c2c00c0d000101104c3e00b1995550000c2c0301d032a00c0b9034800c5d010f51182200b440b451002c2c030001140d003d2683c5202c50b000f0080e0034060300302210141c8120b1486010b4000c4944081403651059030b000c80300d60300e0440088029034400350505502500300e03030b80d06c040d2010807034108010010f09008414205211003501d0416241800007071001c0c0420406220003589c0e600c000442105681580a002c12080e6200c0700720349a5010341d00e6181414801c3c10201d01c181504040100f064100216051000d44c0408040c103503104800003c0c88030960085c4094020030340305401410300d9520051885240610a24101c203e03a000343e080b8017141d0750340760f00403c208002d5110300400300305d40210f1102d003c1600c0c070000c1c3d04c600130700006c0350074000000100034075039a00388031503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 24947649 1250 24946399 24946403
    0x30b040c0e0a06030c1409010b030711060408090a0609064401030c0b18041d0307030207050907090608060d0212030c01020304020a0b130b07030e09150a091b030216 72
    0x640300302d107851140900a0251403006440321109110040707580490400f016082c110083c1c0307003000b00d900e40600c4900b9035000801881c100a52122050390008041c030899000368041c0e0301054450b0300d0f040c10001b1a10241e486002401202141000380c0703034025028000072013070f80320f51640201454803001068468032415101950b2050103003c0b01401681c1014145c9001c0d00c00171003410b0700c800802c20036118100158952401e550580405450103401010603000c000c02039800d40e4140c01c11031461504141c80880150300302c04da00b0b00503400c003000c0c0c5a5120419152504840303190180213000b0660140c0214000e2055450481c01c1d03484414038044010602c004495032000c04246050007508155030407813151002040c0010240d9450303044c0c8004c0d00b26800322803e520319008060842e9880f07240120107219000d43e001c03030b5030383d42c02080b648202c10200c40095000440c0042022084c055089602e442d8a011000c082d00c01c94041d5200c540c05039411300590301d20401801c079906554074440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 24948899 1250 24947649 24947669
    0x305060d030f090f0e0907080d0c17040902040e0a1107150902010e090a02120105030c0a060503070e03010c030603060b0901030b06150c0706020d090e070c0303050606070b0103060203060127030b040c 87
    0x9824402c141c4178610507010070040d520303032a0f2a40440394603140516502c000080c0c0c211210b502081c9030030201d0706030100402401f0302d0141d903102c11600360f8000e07500c003c800032583c10404c50410024051411142e003039824491600307034555211189620350300132541c0701c1503540341d82201f10b9008042016180400418924403481c00543c410b0103544060200103070803400e00d0002805060018120f2075a950040038039500705e0600030201c51641000703140714200602c00b0441801600d080c42032981c4007000c1d6a0105000c5d00b18240031060303c000d00301c114040c0b402480100003040c504040c440d0050001c403a50196402e140801c00b455000d007845008003402149030000d84180c001650b052179080d01d88a040e03403d0358600105510b05811607070080447ca13841da00400207486a44003130790141c002005c1c00c2c285400c54a0f0354a00c100242c008940040d03000040c40541d68203c1c85c5045518113074110349002e1201c8016a00782d020381c9100c000d00c2c2e031040700080340411440c1e541d00c002030b24030408 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 24950149 1250 24948899 24948929
    0xf030b0121140c0d0b0604080607080c0708070c0e060f031203060303090303120411150d0c03062103090b041214033705040806061905030d030213060305060d030f09 72
    0x20b80f0480301c3e4090403c003080300385404c180e0125401d008054400300d4080c0005402c0315078503d0410340d4003c4c0c005004070340340e0504010460000714004007038085140070b40c000d240300070f00b070104080103c0300c0540081c5c03261046542004241d6800030340009242c000650303042d1030b82ca03108040b9145000d0f00c20402da1600000c54a520781038104d07401207100724041c5038aa606251594240042c004599032810342a20040051202d500e465400440503c20b10f13180000d14140d441c1c5014502c140d059244a1070384000321031000601da4804008806404500d105074581440c0c450784189800b4500030050819034a1300290030b62110078419540640748400456003160940384844203448078205096400c080104100e00d40c0c3c6201d801650300740d44c5040024410354603494200a03a640503071100400c45040c4c07036008140c580342070040c00b50580003914050b03290042c84440100c070580d00d811420800d0324041c100052584e46803035860a594050620440c124800340341180c1e4109941c101c102e000140760 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 24951399 1250 24950149 24950161
    0x102070f0320060f070f05100c020c01080108010204050609010320040305030c06070906080402130e0706021006091109010c050a051507020d020c0a060f110d030c0f030b012114 77
    0x880d4020b10110000302a9160000b58100800b90141c2100d1070b00303201d024000c850006800084050360a80960102c9020084000d25030f4151000009038100603000065140c540b075801140c540d01608584000303605150034070f0041011381c0600d0528504068881e07103803810b0245092b00f80404030320075802590b82c541e102d00b8110b80d0f82d031001405c500140314080002e1210743c0319074800c00680700150b03036400168885070200400241503901480c00c00b40e031030340b800780540810840740c001040190081c05002c09a10101d50032907000d54051061035040c00e0400b13201000c000120303040c4d160242841000c40103a801d100c0d1034922002030040262141c9820400740c0414104d60622440d010b5084500a20306818200e07190707201c043c9100d82210880c0418499a4082c240c40003401c40286484400030600e50701b140c0c030f494080c103d080042030b62907000700e106650000d025180101c3c01d090900c51110f048000921510f2900d10720090782c840c20764140040c040315003100c0074106071406070b510f00e0300300341c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 24952649 1250 24951399 24951413
    0xd020a030c0801090203010e040f140709150608090d03021303060c050d0501090207050a030e04020d090c0501020105090303090d05071e0c0806010801140f070e1507050706210b0102070f03 82
    0x100760341c03010075071410000502d0a41c0307000b00d90582d8005c8002c280183c40f182d442c01420f08920300109c4076100a05241800b05030100a07220091004050125480348400d8130030314400300540111081013210410003a144400103446100c0c1812898016030358018502c40918219054100611140c1405045600f403580980902100507210404001d10b907a542c00140c100e1050b50700040103078000c02514008280128402d850346440600b0251030700d007100740d5150442c1e1006000300c2c0c101c06140028011564240b081ea9440301240009503d14280000c0859907018000c0c80e89041140c0040d46000704000400c0c0030300c1c40c4070805a9080b0b00c60291034a5000c400c030600456a1610404000207010b80c01401400343c03103018111002c040c0e071100044d40b242c000004150380c003840800500e44213940c90b05039485000c0072840d02035a40340e05135442d046080c03094592180040003e000081c505090755606200304001400d0800980419884010307800c1c007405500442070441010000028000c031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 24953899 1250 24952649 24952661
    0x3160b0310090903120b01110a05011b020703020102060c03040302010f050f0405010b060a0e01050903010603020a031b0501080f010b0c0c03060c0403030206010b04030305040e0a0207050303100e060919020901050d020a03 96
    0xc0c04518000980b40c212102c02c80b510400d0140002d20951001c40c0b002c2c045503c05045840d041c0b404021b900e01030311a645c6041c002d10b03806c4850760365640304204490080b595244201072a8809044c6542c03840d00004c0d0707514000707400320600620000229007014001d61004e6144000c00509201606e004080c603000d1000449099442e54204085440c0c40d181c541d00300e801240d045e0300c860088180b090011111500442641901503603900c10200140e0f603100b42d00b400451048a02504c50451840d0580202c00780ea803080b410302c408a010b21402c0e5240100070380c150b034044030929407103c00890b4254980240011403c0c0c05007c0c0c0414481c007040e41d0b60042065034040e4003103842c666600c8442d04030500c1544000350010b1000c0c04240021a1406142c94000e1107003000941412030075110103040d9401a135150f2452030290808111411650181541c070040441303102286150214003445000c282d4010324403107a170300003002c0209178024001d0720400501034a0454850307465a0002c0e0040007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 24955149 1250 24953899 24953911
    0xc03020f010807080703110c01060f0302011205040203060105010804020301140108062a090402160b3c0601030b0102073b0403120c0306032109090c050403020d0203160b03 75
    0x2034148524019940036004090060741c403903461800701c2ea95000114000c1c107078002030720f850b00010094101303142c85c2400b424014144d00c031031141d072052561001400c0500e80316021100a82003008000150340c020803400d044034001e00b8041a2581c65200281c01441c203048600305602c20034002180c021300000f940c030f10030070b070b01d070b0003072034130001403101ca07044000008403483e054801003111480a08081d0080e01c6082c0a000c840c900d204055a20901050401c51700e00d0b00c1c84540080a440d009007443d030742041c80c16050f0207048910101d421039404034038020a8941815110308008840e40d108100c2d420040c204814201c8000400f035002007048184604414601d98412084106810703510041e40e001d15410f44030070401244000703040c03028000d4401c000c07042c196102d05c00004600c4075010f050070004050124604802101d078060001c1d03a0b250003141109140602a29020b508142182c059070b4044901c0c00d0010b82910020345000c0404007506505a260200022213076142030155001c0d01e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 24956399 1250 24955149 24955159
    0x301021206100504030c0b090307080d030903021005060306070e0a1203080f07020f03070609110409060914011503080304020402090d0f06060506130b09041506020d02070b0f0a110f01090c0302 84
    0xa9480b00308803200d0190303000240c21049003a204210301c444a80040014010140c1500d522aa5810444d401c000c2d21610280110340c03640c03102c05c105a41440502e60705864440c040119003410000f01e80e5584004000c0014810301c5c03c070114499444002080050450400c504c180341c405150080ca02075068460344000283c80004c030f42d403d4004a544591861068011824017a13942c81d110b02600d0000c206580802510192210036151809000d0005020f1403010601c1c0c00c2c185801d0030700c40014500b08886901d4980b441250f13171847e40102c002c40383c10024290701c0344c44500010f070003071080c074840c83d600841462040d400c02600d4140c40082501070361082181603500e8090010600c9808100c00a80c0c4400310203006003459140039103009440a48005146804401c000c0b502042c65001400503030300c15000703412201d9041003110007400c81d2044980c00c00c110000ca410003030089100f17a02c113011040300d548411800c10412603465040d014007c2c0301c04c000505101c00e006206020a83c015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 24957649 1250 24956399 24956419
    0x21905011206030206070b040309090c08040308071d060a03110a110709020309100903111e07060c0809010e0102031608070c05040903020a11060408070f08010e0d090302090705090301021206 83
    0x941c0c600c07070b100460760094021890905591f480110440c0000c02c114207006d209079001c80c10000e00c0c840d0a019400c540c49030071b911b00702400e014004d000c0081180c010030070009050104c0d00100d40b02204481002e42d00186c032503591440540140221032503030041c006000c5600114030390720415030050403100a0658000316120b0f8402403c0c1e2001300c4241038654845101980d41021a07408511a03501901d8079178560401c1e10101030034140c055424101010200e98040715a20003408148000c061609100001c0c42ca00e5a6414441c040c4411941c10300c0040c100d80c4806074002c1c821100800034140e440c3d00c0003401880e20118a4001a0b415140c040c000440450385040500c9400c401941540040052001c0c80d510b40e807111044c4c2000c0c641180c428400010f16020030092803014100c51810208401e0815030b82608413a4480d03141449079008004900310103070042141000e90360181c44522507640d420304161410f20460b942641c0540c40082c40303280300c210564161740501e004440200c08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 24958899 1250 24957649 24957677
    0xd0b0603010b0403020f0f03011404060f0603050a0605091c0314060108150d020f150405030105060109030b04120903080c060603160b180310090c2108120603070302190501 75
    0x9400240034104460b6000c010910151400c1c5080d41010030b4000d040351850011407010a003520304044c841c900800815040c0802c00c140c40c0603003500c409000d0310800c085451070b101e02e0303039030803d50a02810700d980e0703400404c1040c1c1e014800c0e42c4039060b454a0894070030040300d0008009200404100c00c242d841100481c2e050340c8264030480c000c60745403150f00e00003095541003217130f800113050040340c0c48030071300103d03c183ea00e9040c24607011108441e55240c8031072814080c1401e603000106810b0420044000900005048130f00c01e50b0825040420b0000079210444181d612441d035410142850501042c210050b00002400c0c6101b58010344c1030351406a005641150701000b80d0154224440050084e081c61404c4403c40410100d0700600701c4804811480110303007161840e000030b0b00c040066100510101d10140860044002e1401002040b0101521240b0550140e10b04000e05084c5030f80204150340da003084080055900145001c29078030040c00e81209150191203001e02041507203104081c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 24960149 1250 24958899 24958909
    0x3080109051005040e0c090a0603050c030102070803040b0a0b09010f06030c030e032d0408010603030207080309010f031d0d030209040b0415030605060a08030d060302150703020c01140f0f0d0b 84
    0x409940600280d08580e414401007001601109105d2042403160300e41950881d528201c14078003803141c00c5000604a421810118240842c0e0045a03000c1da00400c0359078001802a0300b16907102c0e8004105903426180c0c01d02d0107001d007040810300303640608003030008200e0002c03840395001111030703a403000c01440c3c2c0180c500360280e99923014003050f907810601003840494260744da080c680c00d040281c0304988080c50303401550160442c7e0802c0320b55a5446406208150f010017184002e484400011820401e01c2c000080030b204910380260308042e211440c00d08000010752514060704107003401d0f1362402d450b0b0721005000390800c00d00b440c486c0d400d22042d245141090303c01c410142241544a0708003e086da20384201030480030b000a03070014091200050301045c2800940107080c0c4104022132140e1844c0100511a010400006003070075040003c8800680c000800e021445028240745280b00b40302000711845000352044d44008003000100ca030642c2c1c1c4501c00030a076000300550108003481010302409 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 24961399 1250 24960149 24960151
    0x10509070801060818060103061d060c07020f040b040504050a03020105010501260c0403170705010605040e03091302130305060f070203040303020d0302090d02040614040501290702030c040c0c0308010905 89
    0x340c0803030100001841050310a02c0ca403a40a0b00c903110364441003c4006034030b860301401740c0c020344043e940c1d40311070038482c0d07001c400188141941d5402840705003401200f6110741d00c28840024807032004121144c0d000d4a40b50841400701c00300400420440ca03040c1810b581360b48200008400652070100085090360203468aa80c034008142e003d81c4151038000001d111a1801602d0300344502c600f0301c00080060200400800c28007a03481c2e115880f2000d41c41c000c0d00351111604914031075424481624111180041030718400c1c1ea08990162140c0c0e01040b25a00900ca041d1040485001e290b01c04424400000740c41c90003101c0c003403e903070a107546241041b61a070249000c01001600003485640c5242e2094000c0c0180740c0d001440344080402035400901100c816511545548558082e50009442d2500c150b90040070950f201d500040d40c101c0c250350b02680c10442300c1c440d2001c081341c2e01c410b5440400a401c8241409001008013000004014080414040341240018040400803403040b000780141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 24962649 1250 24961399 24961411
    0x10e01150318080406050a02010b030309180601200109052416020c10030b120a032307060515030609070609060809011b031b0206040b010303051e0304030215010509 72
    0x211140d925a0008801900c08020b10346142e841545030040030440c000d004000408441d200e1680e00c6440300302c042d003035071601c0300060311a81040c40030340100d44588188040204000c09008141e90701d040042c0c0d181d58015141031140034000c02010002d032030560000d000c0304c3c0584100d550701c44520260700030000400518046108c0044007080c051054844014104201070041d00c203044100c0010400d040c440c41603070000030b500c036984a0400e0603d003212681d0710103008098810342d6842d40340075148101c0032012010b420380c0d503a850130056203540140c40586030310000a00c614208506000d0f105d102e01a00303540700e4001c2d00b0200e6002c0b40000394100032283c0d10740700d101c500b0340b51110980700114010562010b654a032111804101e07a207403c0800004001c0e1000203080d00d84210360139008130b0356422017080d03611000034400420a4540070700e04407649807030015501c2080c590b1070380404030343c04000034082001001340720426802044d090000c018170031640c22140e03a40ca0030810454000d40c3e403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 24963899 1250 24962649 24962669
    0x804051804020a090b0a0902030a0c030e0c030616050702130b0405011d01060804030c021c030f1815020102040b04030f0b06060906120402040b030d0c020901080705030715031e050f010e01 82
    0xb08109414040c2c01548600c00b000b1b2140120300c1da0380c2c0e25401641c2c02160065015580c424100701d15a415100d880502102e16009180d504020800310707544500150404168030540007034450000d101e40308440010394040c0c085d030300782240c292000015020030b408161180741054000b0901c074001040c9440e5405000d40c00c080079900e045001c1d0351a003001740081c0d00304203124480c0c40c00750720781c5065540d011413454800c84030100117040042600d5640e005440410003d80414550b004c0180304a00a4031098103500c110b190309140c06074020700c1250b10040300300c10007240004c01d10400030508017440b8050140d800d05a40d540e030810100740707e043d11090340900207005a42803180c50880907030780184090400103131662a02e001a140541b40c4240c8000600450090000c40c104010391600410119004142442c01c10b80040d40321509070084960003a880c1101d40038983c880e40040040146448484080440c0c850805000e4101224240c1c400180b0303100000350b820581c403606040760303000701c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 24965149 1250 24963899 24963919
    0x108070507060b030a080c0c090105040c02031813110417010603080403080a0c140c01030e01050114060a050403060f020a1803080d020714010501060f11010b01050706020d0e010603080405180402 85
    0xc2c56200400c00002c440d0780500c03800c0c02100000d901d2600800081c2181d00041c01c21003103010410844c404160032850080f820078000241140e0000141c58071040b28120045a0b0302558010622524080d485050b155041001c4010104e0100e0018400e450441c2010b040c00000500340300e01381d503400d11000f42010800c10041001c21180006400000d15520302110000707455110b5005c18540c41ca045100e540000d01e8000896815100f058080400003001344220762400e107400c1412501914401c0c0101c41c000340c200389043c403c00c1101c001c2d65103d403003000355060a101c514001d400202801001c6101d500e081c040c21a9440091400c0725800400c1504c0c10903540d00503000303500448000c86030103103c50401d6a181400b03001c4c2c1d40c007034911036075240300c003c10b032210041c2880d1002d0714014499150904d02581030742d00c141210b8015801403000b5079100b90070b14246d030080a160550700303d25483c202001c0100021b20780200103d030790441c2c100795081c1c007171401c55161400c2070354002e42c0302c0403c42c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 24966399 1250 24965149 24965153
    0x90a05030a051b070e0105030d080105030606010804030216030b0601080603030304260403050307060b090f0408070201030209060904090f0b09030c0a110d080a03020c01110702030303060906121204140108070507 92
    0x400c0c003c0e0143e80700041066400c01000d15089007078000b0041030424400620441c1810015204c603c00d0600e00001c682d454071001c03030b4480d42e020b01850b04001415000505040c000c210150300f25070380c4191134510680d6810320705201c110035035003140000c1c09840460407901c0c00200707490243d030f0400303900c0311941e110513212600280040c1c5030481c065802d000001c0420703810b00180400324000c00010511130401010403d0702c10340109042c580d900f5010030301021400c0319040d51402982800d00583d2181d140700050143d010f800100c0f64407038142a00c00c2c0411400c2c0140d55802842403140c00e40d2511107441498032402a400321400c1584111100000700315075050240103410041c1c0800a02c58030354070764003140d40c0103c800c00040f81c6c00040282c01e41000348504644031010f00b0306036090995560000b80c40740300207010b40d44201d9044000c14a96a980440c000034801141c0449098280c25160b601064210340b00381c10124515445001c840d50084c56858443c4609a80316850b0408070303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 24967649 1250 24966399 24966407
    0x1308060613110a080402120f01020904050105030102040e010909020105070b240609010c0f060f05090619020909040204020304050c060c10050604110418020f0d0f0c0f2f16030308090a05030a 83
    0x45c01a43d001424001c0d20007200d03014003a840c0740c00a1500056902c400380e0f000d2009840f01079010500030380c8101b1040022440c2d0948480c151401c0790300101d640700b0f050004071030501944a000d4005400d88050003902090024224082c000100461083c03040810401440380565090b0764041885400040001072429125401540c400c00d8006019202d0300c88c48421904103d030b001d0314503403000042c0701c2c00d84501e0b25615904450350105526000c0380c000400c503400c0d00135200074062500800840c0800809101d0b101e94103501a0850380c94821401c0c040d50348010811440c10000e207840c001c2442414280944a10f80002e040407c3c902440c216001559008a0180c140c0980e8203005c000540d104280050610110100b408220074004030144422035080ca17500205021801c04a155038542000b4504e107900c8040800d500081c0c80d80304009581559400442107030701450300381d414541c500e04a00c4040d603020f40c0d0799034400d81d2048000390b070b2a00207642c06000b5a00a00c12985544d00c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 24968899 1250 24967649 24967651
    0x1404020102011d06061002030c190b01120809040207030507051015170712050a0c0e010504060b091f0903060908030406050c0f0f091203030a050403020c010c020a0e07051308060613110a08 82
    0x1031f01c1200d140c041c54001d4582894403108842461500700800c0c0014005c0707666819014080000301080051309540c0c5080852080514040c003d503004110203082c54024029a040b240d00174040d600c448401181e004010708040d04000030f82c01c5072440200390035001c2da5038a60b802400000610050b0b0401400003048120103030100d526202d240401000601c080c210000203007851803c0c6901275041001700000d80b8401d401c01e03031418a00b4000d91240e551012880c0c08280380005142c4101c0004000441d00c84140350000760805090800030010460204002c611031405100c0c10003003915102c3d1180701503c5005601020000240701c0118080c0906004112090008200c1800c07101440c81c424103541080395504a220390f9030007004149030301806103800350103007446c040b0b02c126410340c0003402c0343c1124012440c80007410f10004c1c0c00d1900400481311000400300070300c22955a0740f1086c507902c80713003101c06500070040c102c0c007a00c4801650013148034100503815001c1c2070100004080340e24200c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 24970149 1250 24968899 24968929
    0x20f0f100203100b0706020c060f1303080414030a050c0706020708210d05010303080402041b0c20040e0313050102030304080f07030905040e010c02010e0309030d08090109061404020102011d0606 85
    0x300f41800080d03000801e400401c07042d807082102603100c00204040b1801e106005018440564490381000303910380704410320079216039044c1440074007520740d0b0821284009040d50709045c680700004411402d07982240181c401d0395101011074001c140ca482c0100d855510903c50f28007140e0002110142010301c8045280c41c2a048000c080e00b41740c151079545094a20a91041d00418400000d00040d810f241c0550903c0394003010807984210290700000b03000044415000d007c690301c1c101d01081c2d0100d44003170203010040092060201a04104d4016284d90020280040106091000203a154000b005607031090743c0000c49941040611942d40c6000e600200b8114100600c50305c0100700382da0769204a130701240915000103000d420f40300010307084460040e0003020310790050003142c2e40c664002410015002561514002c0c90300c034109007602402d60080020f0103141071444401500c0d004003c9144668001d03070090210b40750a580710342481610b20389440783c90b00902e0000310182894022450750301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 24971399 1250 24970149 24970171
    0x9200a0e0907020f01051303080f01060806060903010f0911100201060609030809040902041e060e010b0706090203150a1e0203100510050403020a0f030b070503090a0303051008031801020f0f100203 86
    0x800308040280c211042214203280c0350b42401c44401c107240d13128881c1d6500ad45100030805095041c0b80c409819094010f00c05032242000003103410070364034203401c01030003101500c101307122002451070071130042a919400180203200f0154404000c0e0b10501a68080f21055114840e40c941145c80f000ca180c0d010707a80d020f400c15102d028103001611540301c1d6a01e0300681c11090303000034108440c01000d94140d640402140f4902d0b0005020365121401212a81ca0f444400050308166a1020a081901c0c0085101d010608070081048000e9150000d024000440340785200402c01e03c18184100d0006440c245056041410103000c2400c11040c442e48059990520740d0500b0b40c0c1e1741c001644240d15400c101107520325010308004114015030b541c0d4000176242421030651501104581c2d4512991070003900300f503114404110700c044201981000741041d0300c03c1d2991100201050b001000c1001115401441403d811103829100401d060141d003070002c014049407001c8000341d1010f9000605024070700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 24972649 1250 24971399 24971413
    0x3021c08040b0a0207200301060506040303080f0a090c0605070b06010305160807021c020318040b01080a020703090b031509090d020a030509040609060305060f010608010e010509130203010609200a0e090702 90
    0x1700e00c41e241e81d41b00e204003403025404410308810034503003541c64540c4105e0141c04140020310009030002d1860f82e000c508803840708081d5441e0b40500f00605101000903242c0011a0008240507600000501c0314034098888500551100001142115001c650031038250003150003010500d40300f41350b015040b90030791048420329410340101d5403400f2150b1610402681c000111110805004881c076504220125070421403006000b0001e481800014000045140d00049040405009040c14006084c0d001240c2b41c5a25100c000080c058152a07402c601c103030440780004246480002e51030aa008069015003280d45065505465941042842560003611000b011401c04414030500c401540100c00034481c50804400000c81d101040c0c00c00010016000700602c00c0c2c040240d44181103800684100c10740f5039805220031618030300d5410003941075082903000a0031041940008001c040b1401160000001006500300c6501c246807544000c0b486903000381c10340745000e420465000c0f01c035005850034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 24973899 1250 24972649 24972653
    0x20406050907170c0c032d070b0114030708030f0a03060e0709060f080601021c0201090f08030603010f051005010c15020c07140402070c0b090607051903021c08040b0a0207 75
    0x151410440b820b01c0060700d400c2c00a0a40c8a8101446030403450300b202c81e07842e0900c85140760351a48203000102030540800302c0c0091200c8810044a8087c40c00000f0943d00c4440f14600902d4075002845084c564010050707290740149004541d0101720340000d8011031504001d45003046c050f411080c0c2510a0580e14817000400c500407060240c070503281941e8038a0224201a0043c0ca880405142c030801c00020504200f5035980000d0192589c14a8071040b501840e0641e4040f070160441d038400500440c130080c140c03820040e82401450142200320024825600d15011718030403107904440404001c1c1540b00200415409131481030010760050051b024244103400c8901d081e680440e0041c417103680424001c202c0385145010380001c408040b0b905624045c1c544c0c541080550351801078a1002ca40012500c003d40d50f01030031500c4d02a4850243d0381c3c0d41c03640f400840030031401203105801501810b55080140c81d004960035402c1e42c03040d140c29a06490b162100001c000009107400550703075080241c040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 24975149 1250 24973899 24973909
    0x30b06060c0109120f09030c1214010c09030302010b010f1205090a08030c180609090a0c110f03030405010b01090509010909050102070b090a030e0103050c0a05030408041203020703110901060503040b0402040605 92
    0x500030b13010704d001c403882654a84000f44892407411600b020440c2224082c800106104948021144610f00400b0a4006410300b50344804001003c86000d618203001d182102e03401601c01e01c1240e009400821809409100544980c00384400010008403442103450390600e03c1d500c001c0d000500c12049421316051aa2031107210340c03007550800d01c507000101d0900e0122200c0410b00052031020ba802c141484030f010003089008a0140c04103683e47d07103c05180b010184141c040401c4c1802c8903003150703a07080407100c48a40329030003501c0c00e9840c1c0d42090038441495008007141c1048410280003050180e1814042c14010841d402d011980c55400f00016408281c0c52220b0078002c250440141841c0e010070326020b413403a082c01d000a4181400d0104002c0307880c10250944112807004e0510355501d50340c5290020440c8220380081c05000d545200e60000d159000896206a03445480a00b1540c100c0074104541004240f1810002450410000f0f00003011075507031641081c030160010411585a10000e1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 24976399 1250 24975149 24975161
    0x50105071115040305010f06182d02040602070b070309051002120d0204050f0102010b010503011406090306070201051f050306040206070812010e0703321e010602010c030b01050a09030b06060c01 85
    0x10b000a0b201203824428030500b842481d580d0040c41404011403441c080b081400d0190030101c1c030402d00e981d240d0401c001100f2540341540d1416620b400d010361030411160030000d40013802201c0040c822000d01003005006042200c910386d415482e80c07603860346810300f045200c0408103908070443c01030f00d00c6402640980300150010078070010000d030b00d42c0d082000340440380c1c035400d072103074116810038030200d00d00d0b6000011a41076800020140714400104008210f180c8160100766800d403083c4001c020100d9410751105000b2061007956010f03900b504010408403142d0382c000c00d94942c0050010600616140c03000f0440d03203100722886800c10071800c1d21011010006d80c08411100c842d01e08012402c0c1d80340c030900002080c03c44150551019983c2c01401000041c10b0081760100250013007401c00c2c4c0c545001190310310300303075040000540c0c440c00002e010302118075031303080868241680c000d429030156045d2008074410b5a0381d918010f1660301c513040031690240402c0d0f0083d41c00c10a21103010300c00e01440f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 24977649 1250 24976399 24976429
    0xc02070b09060f04080a030e042403060203070c081603030b01020d020304090b0a081608070504020f0d050603010e0d0c0512030103050606091b07030504051201140a09050304050409050d030606020303100501050711 93
    0x4464091948000d100598001c004416200c0c0451001100303a952002b1580055a07004440103072681c1d0b541c6400c5e0346040e40c80c80080c004010102d5403854103050011403a400d0351003a5410f0100e8841c400040e43c2c1e88040e0703080400940c00510062020314000c1e408107e180d08024021000c1c1135035001c0107410108001720300402c40300f044100f44044002080040c000340001e03913085181030020300941c0d205d402540c20315503041c1e48501c04111325a0b002d401000044c000f0b5020341c0d550312240c40d400307840442c000c0011200740c0606560b1014943c1d003007050b6812250844003403c0e05544010400410000c001c1c00d201d03040c051140c0e0745a070b000c02180640792440c800d07200e56650340c0c20041080983c0b0150022448560b050400c5021403410b4400c1050704007038141008542c110791442d10b68214011504030f15041441c102081013441030000c2c0c444006106502c0c01c014440d1500c00c00c9072a40300443c0e00114080840e0400c0040354804c2c0d0060424a0240c2c2d040303451507800d08000f845614103541c1e5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 24978899 1250 24977649 24977657
    0x30c0d1104090903080105090702030403060506060d06080304030c0603020a1b03090b0c0c09010906050303070201080403170c070308090c100e0102070e010803040305070608070e0906060d110d0c02070b09060f04080a03 95
    0x360004c01d40c1128503207000d420f044400742140d04c0e10100c020350301e101e20b010003031820303840b040440d6903601c031142910b0000307032000010b200c45601e9005961f541d402520050b10401c0488800145450117442101c424001725580c0e028140e00c00200c40001c15400d86084003084040440080e03a45108409051100c12400140456152910070000e6100341a040880508c0c0360080030070050f40c002086401d85982820800170075516801c054a07030414402c0940242d0070804208400740d40304e0802000c81c28881d4541001c1920f8417028907503900134021440d134204225a410f480c0b0340f03000e50700005034150140304580409072180e5006407007030002c0c2d2190b1107540c00450140700304941440943d0140105203000c00039850804001804401c9684000740110911800700d212515100211510884da40c203040c4040b4401590303062160703100c9000750003864500f01e80010124408140d0100703d84881703580030f042000038020042d9a51181a6031901c10a0400c00007a60300305c1802441c03c0140291a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 24980149 1250 24978899 24978911
    0x90c1002160e090a1b120501020405011218061e020c010902010206130c2601150e011a090609060909010b030a0c1b1103030c010204030b01080709020906030c0d110409 73
    0x400340d0704554254101803080d24440c0c1c100580a02c0c0042c600d80394030341202003810301c3c3c02c100398000c6000c1d03a9038000c08600c81c0458666810b124054000340220751081e6a0300c118020a200d00c3d034125004102504082d0000d803c142e404039105030403403031214544c0c121340219503101030000012a07001c284076a00d1651100e04180542d030701403003c0f1303911a9103180304040521055442810994550140c0b039907001291610b1390391010410940212204008000c222040d8400641d0644840d94803035a004290070328000304103044002c001c0544e255080c4089400e003400c2e141082142c0d00300c0c40b1102c1c0c00a00c140501d031855654081c1c0140201007200203682d9030f0810041d0710007aa0342c03441c0c9090a0140d003207182c1000d6190317000c0c0b401c0081e800c0b460700250600d100340000d0031071140001c0701743c0c69800800c0c04002d0124a86a140c100c03408582260070079a900c00030075040e40900d8403469801002407002501d0070b9003140042c00c085c03200b0507000030728104528414030a504203420081c04295500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 24981399 1250 24980149 24980173
    0x702011101061716050108040203060121080324010201020405060403200315010e1303080f06030f1605041a060909090102040b0d0f0b030f0607050d0b0603280501030206040e090c1002 80
    0x40c0a001c5d080a1030004a24038007600407aa4074003044c800e8140c514000b11154030500c140c003070001c507e243c2c001a404e41c1d0313040c00c03442c1d03032482000004801070440d00300c2c203c400250b005208503000c80310701070401824140b840e110304a90300414001d041c404a0000301c0260070f07550520011005106180342100c132541000e200c1c40802d48020070000d00c0d0800c0b1100c00001ca0b800001c01c60f40320301c1c10701c00c030901030f03941c000807034149400140d5a01c0244907681c101c039a1450090031078001d40f001510100100c02d0003a048a4206c1e5408000f5a0070075800c200ba25414286044101d50001c515400949002d03600c40301390b002c5a01803d07808422681d10191036840b01035074005c44034226001c5005000f61403043c07071f0f80d50b1100c1002e0182001e0000000d50410b001034290403d100e40e40c0024240384d22490400074582c5400c81c412800040510340e100c0311900c000700c512840e07060320b4002d840076041c5401c03d604101107100152160340d051090316848095940c6042d60381c2c418071079540c06040c1c0400c0301c0e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 24982649 1250 24981399 24981433
    0x2030406080109020c03030402130902030d020c1203040b03131406070306060e03060f0601030c03090f0c1d0903030601050703120f1506020f1c09050901060305240607020111010617 79
    0x40e0010003001e4010803081113a41e5000051f6074000383c040f90384004910441c040880149150807000703406001d880d41c04030019030003040e5113003018003c0c1d805d0720a4448468030701e41c07a03120300d0140003420307001440441c02020307903d540881c1151045207080005000c10a0403454070000310f41c41800291958401d008081e4030603883d031481807095000f00ba05080c40c0c10884a001c0c030083c5110304140da00c800545c1c1c2540300c0d03008410780703541180d00a184a00703d03040006030140d1a0086524036440e2000c1d8606a0058141c000d02c122200c10143d03003561240001102d940e48228810303000c22000350b0007820210702912408107407010301c040c002104104102210001c42e035650000041d90407003180720316600c074007190000a00c802c1001d500c1002d0b45100003540c50041640156400401d00c000200b003840d0143d000754050800c2d94101d01019030081c8096404944000c000c3d40c103c1c00034080440194019884071502038540d000200b03460ba1240701c00c181c1c0b055642048640341d44580c0c907403112907000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 24983899 1250 24982649 24982651
    0x1090510050f06090f0105040b070c090c05040f03030c0c090e0615060f0d020306030304030605010b0309010506030d12050a0e1b0a08060f04022103031003050610150327030203040608 80
    0x81914190040c1c1004000151113000302005107000344042d4540c08031a0f0b1042c030454000e0b1002d21500f944654060a06406c00302150003648601c6141500c1c0011583c0103105030b404a6205800003848241141d0b01220f003000580411200c80124000c0822a0b41c040e0151034841580c260081c00035140c0384e03901c029403017440d40003540030744020801c103c1160320f00701c11500f11001080d0301680d00c3d2252004a442d41c0f2403607001922a62910700089000900c0200440c080c1c1d5548000744181d0b1101010191251540702c28140400c6008007000c541703040a4204a601414041740020240d4030b25603407c1c00c1c41090000c0e044c1c03244600484107807624245202c00080c0414200030300b03171440c00600361409480085c0029204803011400b010b040d000081110304d0364804003081d81c1c1c403424400c2c0003005561907800708840c03500648000a81e80b54402140100301e641203140d41d0f50111940209900820981c18480b40c81074078030010108038985000003801c880e100f640103650700c5103001002071001c1b0b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 24985149 1250 24983899 24983909
    0xc01030507050405010c020109031205070b0a021303110105120903040f080c091f03050a110907020109051c0e0d0f0b09190b100909050703140a0b1302031501090510 72
    0x85004148a0942d501c0001e45055800031300b003d0b00717803455a000503211000e1583c4020f043d007001425090940307501501074210b20740701d0130b182255511085030000a90007030160080100d80081c40410205080c440e581401c15810b0420030314007401a00c4040c2d94941c211020810b603440081d04005804182e420381000300311100244c5000800d010004007035100140070035038100c000020140d03010340c4ac40c4000740103603400021981e10405501d0081302c0c3c0008a0a002d10810000c3c0001e0202c900600803140c80341c2d4004050450794002050340030764009500c0030741c800c01040011a1145484203485245507500400c843c8401050a14185d8060311000703140c101e20390098035008400070340442e0300f00810717a480002146640c1d198000e803410702545074816400d0300c1c1000c000e1818028040780c0d00e015280135060700703c12908120006036490300c0100b001041c0c024250006541c0f5542070400f500e040d8402402d81d0f01010810744002456174084c1c00001107641d0741e1083c0106241101c0800d00101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 24986399 1250 24985149 24985151
    0x310020c1f2c0d03090305070311010b0a12020405010906080a08030c090907050c1b010e090a0902060309060906070c0201120c020708190605060906090613090507060f020c0103 77
    0x240c0004015122000d6030400c50300880251461800d0070240d030064a02103491010040c1950701d841145002c11200044000841c05a0790104103014030034043d1111041c1c254071044c0c60060195412101c500e9442114403071556940100080b80d90340107200001030201103125000c3c01c205004220455206034404034030341d071525a080018013000b0aa1014a81e00415001d03120382c0c64640044580c440c1540a6912001d042c04000d007054012004d00104a01081203440008040700300880a10031032483c070f4081a00381e00d0a9507946080980e0750f502051326040402e103226942d01045190b081070b1000d0749550800720800080030410006ea9912140c01d252500740c00d5025000600580c91050748905080d80311503c0e80052402008100002c21032507003114920464141310720103030b0814000131110340741401c010900614000e0200350144000610405807a02c03100204600b20039a5000806455115004071020480600111000b0005900c54149114080034001d0500d0b14640866040c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 24987649 1250 24986399 24986407
    0x30e03030103170a0c02090f010602100b01050d02070c050d0305220b07030302180307060f0e03070b0d020309210a0305131a0606070b01080114060109062717070302031002 75
    0x119503c000119a40c01054041d103035500380c1070b0300c1244e031000b00e40d001a420400480074040d482c441e40b0401412101e0303ea0030783c0c825034040788055040e62802c41000303000030010b101000c00340c050303031780103021061060210341507881c0d130740020511030201030100384c02168000c00e0b07032000e1070b040c5200d000361508031620000c001418009011000d0066102c05401c155001c6003c140d842c015280c501204c01c4010125505a565210000c103101c11894000e000240d5081840c1120300380015003100b615480c5880c20708200092107040020340000300300b1281445940742c4204003000f10758000d40d15441500d5031a17520b07075040602400b42c401c080c00d1040c0080310b104646010955245815134050400844545151144c40014407180280744001d405840060000500d40c04154009030030b030340c0031154404160b1b64440054078040305511030a0049000030f100500c01104500c0407200000480248803483d40e19407401c0e607a504010604003520f5400b41c0800d00951504002000a51003101015850 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 24988899 1250 24987649 24987653
    0x110a02030409021303140f07140303030f0c0906070606050301050c041809020406091d01050c0309060a0b06040b07050f010b04051005060702040f02220501030525030f0204080a03030e03030103 84
    0x303a80704034800e111519034003040d8200e20020f020001c07030046800c85d001312013074040a03c50f07544641408460030360600c118080006c1d4601852200d0501c01c2004000d141544d51316064407601e544000c0081c400740c1806c02c40c10200e5510040540082400f400c4005810b6041006041c03c50b0006040e402c000071050004002050802d000d102c903d03400d5a0f4041030103800c0e8804200076201d682c2022070003a060940b0034851031125840c1c1c585402c01c0718001c3c8101c3e1580400665544416580c50500d41c0000303002980139041600401d12174240078105a03e881d0341d42c0c4041c28070350402002240c42d038001e10040552102c0c00d0090000c3e0007c02c82d0104100d0419281000607040a4450207001c0d610110b8040d00359601d650103007207580e408000540d60760070305207540e996a41da058a0b503842e00c40500000710711940b28bc410b0b24816014581c14004032a03041440d14a01b0211180c00800c060322141c501c0d03440d2140b800070300b00030010700008007003007a00343c03178080d056401540c04c60001c0d910a03c01000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 24990149 1250 24988899 24988903
    0xe0a1103041b09112101120318030c0e0a050702060c0a110709060311010f020c011227030201060f0803070b0a150305030309070510020f0d110109060509030706110a02 73
    0x1c1c0055006000a04103076604414030000303016944400d40c064a006040c1c0c80800d000e07801004c02d8205025540a500300c50729014004117400e0140e0f0410500c0c00807002c00103030288000d4003c1481c400c40d90030100d5501c0c1d441c254013604030340140d22089000e40038400701c403985000b05900962580080c14035803406821500c03443c06040c4203181003126101001c881e0f40340c107000013406031419010a0007525104c1c20301080d08203402c64080d0000d1460000724104500c0402c5403800b6000580d030300c0c410304442c221980050601c0018400081c440b00b60301100c4203d2142000c540f091203a000030941910b0284003c2c000740c25030f402408180c20030004040000d01d0b1020316540309560381340000e584507403080079411000403030b00020441e11001017800034010b00000c0d100e084540c104c0b8110740d40e59240780100e0302e550314201c00c00e1142d84001c81d91501c05010f0201001e032038810400004114442e610fa80c400d031003007034440000c20b4000082080c140103440c0030b526070503041040707881d181007002c00c0029 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 24991399 1250 24990149 24990151
    0xb1e030c10110604050a030801060503011409040311030d050103050f07050a090e0a05070b13061b030305070e03010c080105100f02070909080f0304030201140907051008060a0e010806010e0a1103 85
    0x607108948070508240e0160042900c144500c01590032101c4900e024500540d032038400c9134059000c40c5c1c6d070900000302103118000700c2c0d040e5019450446064592032081c864800005041101800500c2c03114520010f000c00c00745c0340d0a0694040464203515606125041c003030703010886407103a001908184401c0c0ca0b403081c0c60048840c030420000e8000d000041e81d0341041d5140b4001032580c01a03d00015000341e8040141c0450a840324007411559642e0314103442000c5600210710b0600200181d10340828080d1f400540c0c00700060419022084040000a0854074000c0303000d40417450610061003207007418148100c003c07003141043c2115210360380c0084d42d618214821400c01d691a1130b40d00c802c001e000010b8400c203006030f0340c41c2612420207140c00b90207001d02c990b22610716040c0b10300041c00d03801c001070403000312000a0200049580c83c458102da40703050081126402410140000800040d45151240200100c5000e0300e43c4e941080c00139100110054421040d90f400c20300c0901200c02c0b0b0341c0880e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 24992649 1250 24991399 24991423
    0x101a040c050306030a020d02040e120a0e010801030f02040e07030204020d230702150c04030f06020a0e0409020a1e050d05010c020d02030309070b071a0708010501020106060302030c0406050903070305060a0b1e03 92
    0x21001f00b03a4502c0090051300d901d43e4074210780d01441951620051008014010301d403080c1d19492812840c010044541110921014054a00b42d00e03640d405400c1c540d2040c0210307869070b029a428240c80350003240c140d906c151040c21005988004c0c0010300401181d88000145255a012009040c0400c0080d52510800d001c0c100c0761081c030001ca6844902d09086030020750340010020321000581c1041c6c0000e40200e40c00300e000c9001c1c9104400d04c0d180611661028a84c0108482035050600304c880d42e0701038003202078081d054407a000201d000c0d69008038200d0594454400810f4105010342e0003824045011410f005540c030500070702c500f440300481e0b650155001c1012250300c440407810200d20541c1440041807141c3e92650a1080f150f5111300541d041e2078080e0003e00c507050350b420080702248421903c015040c00280303c1800941c1c4544028040300c0700c0101142e40258507610352a003480d0040d00c2e070b640e00903590580480c2d2401c08032a0321200c0207101000100e480303005c101180c1c03280d1241c403807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 24993899 1250 24992649 24992659
    0x503101107021c06050901020306100804150203090c0303040e0103021005040f05060d02070b07030c080c0406091502070b0a0503060f0405010501080f1009151d010501140c101a040c050306030a02 85
    0x80c10f030b105241110440c07280c3d42c0106051000d82000c2d0401c6000b0740c400c0d120310b40107090714014080c0c0e40d401100818021503000d40c402c450090000002002504064640342d102d008101c56100c0700d603800c02c0584050489284450100d51551040000c0499211940821706c0703400e010400c000502e0058213000c03920f0079951556101481002036000380f0071880000c200104803814000c3c00c0303074075510000741c003a0310717440d480d032291205106050745001d20f00c20040054026007050100500500d00c02a15804a004903050107031105550401c03070300990010301c0081c0c4080b0400100c1d25090302498200c52081d034041000e9418030380000c00800c00105445a4000541d010400c10551403a142000304a6070504200070f1121904541d00b02e0300c03d226000d081410a9402042d603000c1c0c1c0c0c2040e04841058440d007101c00400306103e1001d82041030f6803040c501504003a090b800702c0501130341c8004d151507405d0041c2a6920380c10031088400a103444000c000701801003001300d417800039000c00e00d10307011a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 24995149 1250 24993899 24993919
    0x216080c0a0308030a020706061d061905040b0a1203020d0906090303080406090201140406030903031a090f07051306050309100e0d051b1005061002010c050a0507051015050310110702 80
    0x1760700c2c4080d00c18444000d012602c1c00d1000900e045001566492142401c001000c01ba180c2070200712140c2101c00d000366041c0301c8580100064039040e8412246800b0281c800a40242d641d101440510341820054001d40c00ca04094054584e02c014003101030310150a16804681c25610010908903000304003d00f0582c4d541a13010642e070141c06008802d4554402c000e075030300d450b030310000e002d0b0903035000480109090030500c00b11111b0280c80d4500440c40075020f0002c0d0750f2080742404a81034042c00d00020f1120030040f52524211b0307c0b80c10703405084151607041d900d0400543c40307480c203e0a00d8a041c8014a84108a842c40c0b0000c161503032810b803503184c0103445070700c4881414060910407000041d80c1c440d07240d08080304000c0703401c2036103e50700c00c5401007100840742d40c0903800e80707152020000000300100031040c81140a00c01910001d805001103038015002850a54101d070388070503e040000c0c41c00d0108201078a01040f1203841c200c6041400d002010f094940181d0a0041c948001e1192807410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 24996399 1250 24995149 24995161
    0x62004060f0305090a0204150602070b030103050a0b19020c0105271c05040b0c010504030908060f060418050a1b0b090607060902010e0a17010f230601030e0d0216080c0a030803 77
    0x861070354580060040003418801010000002316070700c5524091b015144001403084410b50949040769001400f80c90300d0740071541e8180c40d00e400280f60404c004100100b070086070240d4809000c4541280b400014030303082195a80012a02201850b503544491458021600301d02184241015070780500691800d00d441c42d041e10140615080421002c002145e540c2a840c4150400ca0143d4007039103c0e50541603c0c0d040098503907508441e400d074a1060000814640e0416500200100446200d60390502070b1036921030313050001901054030f10301c00601180800c0821121100000c0204080700c6141c01001d80c0410356502900c02d0180410b55544541402c1d64000c0751440c0c900040141050342c029215002558050079070328500340658a044100079021034030380302d8040c0081c05c03007103881c0c3c0d600c0214215550705000281451b0402d6100c1070904600c000400c0000c5c0700355103940142500c0e01240750490701c10303201607204001036032154003444141d4442e0003000003035030f4101d1143c507500d5840b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 24997649 1250 24996399 24996403
    0x9180c15090613090b040e12160606031a0f06010f050d0f0203010f0906060813080306040b040f0b01080a05070507020d03020115030312050a09020109050d02040608010207062004060f030509 83
    0x3141a07002200003c2c0120001d40c8100d1600039911040001c01945000400303010403152402800c2180d03030f001c0c41d120050752004001800340e4105503940b000382e4510300c0e5641c8080d01c810741d0084035100c0440c50000c01800d8800031280d4800080044110503160180000b028002215413410601c8400145450f955020380c00400001c1041c180a540c0c1e542c2d900c0c4c60801c02090751190102c51303850800c011800600c0b134402c13140504014903503144100541e49400e0850780c805450382d50f1040e9110b02d2042151124000d5002881e00948001a0800380c60009012030500425000340366103494104000b03540c002c4143e6400d40d8060724991030007840d17485c3c1070b4010841d5034600d403649486540c0000800d58030050001c208101282c081c010f80d02e58221070825968a00c000a000c1521038809000c1ca08002800c091100c2c00144042409642d4040e42401c80c1e105000903101e140d241d0b1400034051348511000ca01844288400303502e4035107046030040c02c440c1e503070035034000f0036850304003041008900b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 24998899 1250 24997649 24997657
    0x90501020d0809120f13030c030c1a090114120429040f0f08130807030309080f0604080a0201020906041d090706050a052b06081006030507051504210209180c15 70
    0x110b08221b1ba40c80c1d0410000114052008030b84028001074081100060811001c41c1c10405044a43c104948940159004c0d03d2881810345901c100380300d0401c1c0e01030b2044002d4041d900a00c46c0c0c1a441041400c0540f00c0d5401c81c084140c10210b50042c440050040050b0130802078105964001021007032400035114410b540380104100c0004001140d040000b05020040f01d00c00c3d121015059542c11341d00f526140300e0040600d558100c0c00018000c0703180d240042901d000e5500c00103282501c1140000d0740c0350065000400c2da0341c2000700c8071001142100744950401e00381002000c1051424200070100e10800e0b40301004c2210202c0c84040300f16980038024004544100019501e034103164400700145800c1c0305942c99403040e510ba540440310305221707100a4980003009400d006003400e050103080401c40303c008030b200d601000000350000394100c07900382e080340d07003940c03e070820040c0e0040141e4801c0141074003941a03d18003a500c40281c2c00a80450b00110a03201030111129a0900c4d0b426030103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 25000006 1107 24998899 24998917
    0x80114120c0d050102040f140f06030f0415020d06080312150105041211030105090d03050109021201181e0903030608070e0103030503090c0d03090501020d0809120f 72
    0x14140c20b0314107014010800503241550b507a40e203140c0f4440690101030380000c2e10000c3c200701d00d4900d203c0001500100e440710b013581400901d40035600000b2300000c0400102410150500c12940c0507901048030541f0300700311040d40e480307816440b54801c0340800042101c41d400030300307802008542c58140301c0045c1d56142c14a410310006081c500604e10040d038648203a00d18210084e42c0c24081d080c411000c550181c9001ca03a0a42c005d025204d0680154a4883c01808214241c2d4848400c241c1101d02c00d10024945c0321005c010392004004d030032003407110752541070f030036500580b015080780381c0683c800d542c01c120b001e5551505545902c0c560244d001c240030362400400c04a803143e4040d540041b07035003040e14005000300000454091044008802003040380c101002190f030180104450102e95040c60002868801c640d203465000c64442e1121404000c5400141d03c070b1501d0984034661 = true := by decide +kernel

theorem cover : BRFrame.Cov 24820149 25000006 := by
  have h0 := BRFrame.cov_init 24820149
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24820149 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 24820149 ≤ n) (h2 : n < 25000006) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
