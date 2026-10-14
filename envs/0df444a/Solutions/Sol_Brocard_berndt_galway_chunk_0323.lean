-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0323
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:12:16.446431+00:00
-- url     : https://prove2.me/submissions/004238d1-59e7-43a6-86aa-626c3cfe33c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 57913672 ≤ n < 58093528 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 57914922 1250 57913672 57913699
    0x6050409020f04260c03070617060a150221040e040204020306030f0102030901201201060f020a0b01060804030806040c020c06070302010905010c0810080601060c030e010203091513140907030b 84
    0x105600d1445045070b20300301d5021512203012905d005400e005090098216203410400f00b0f030002031200802a0020080e0180c4d56654000340c2c3d228400d400071702c086504500302c140540da000a40b04401a42da061840400d40f130341e958860b031401584100d00c03404c0c01c540002401400c0070f03009950800000380c11107250a4610700042e003a80c20896510085a5580781e900c1d510040981d9030400d020301901060b032810002184041c40800e05000b0002480062201ea003102c6100300320890095400202941c032558648400400014040d03405400051166011031450b1400b489850144001c5400500000b0030441c14030100340c001003800c0d810b5540e07824040020030028010001140451750721110300c0e25102181e1102072809402100e41a4004001400781c15009102d01d41d0594141c01c6c1030032441c0100004034954070555800c5500210010021b014801100d0003901480301d04280001100d61107189080300088400752440c0c1c4641a1000303c0c42807070180c4d00c0320345504405003013481000074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 57916172 1250 57914922 57914939
    0x18030303180209150a0b09060304020103050403170f07031a0a06081305010501090902040c0f02061506071208011401020102070c0e0907080f060603150105240c011e0e0706050409020f04 81
    0x404413422195043c040c10350522614260409a010300030b030440385800d00e108440801c0301408010300c0241810b0b0b84401003000d250003964007580c85849407054030307128038107540c103070036245c2040d2050004641080548a0a41c4400070340c401000400350000c0c21a0740740031422a00913078050200311004010b02460b802040082c080e50b400b80000320030204840300d032407041c48122440800317410100480c12100e40310440d0301048481d00080c41d45490094000903200084242c40b41280062150925000030032340c0d980c001c0940d0381251310100c1000d01c2020082d00590a034410080010511881540e052042d135580381c1a584e0885140012145081e40756058a46002180005054990f01c080300b000038a1504000c2989602d074034400701d51695140c400850b070a40c81c810200c0300000781800c6c00c101200402e40a0340d00c2900000c000b03000f040c900522060041c1106109010b4003820b005010b08038034000a00300045980999415141525141004001b03400c111080c41c41403604110004070941e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 57917422 1250 57916172 57916189
    0x50d2301060b03010807060804020901030f03030b040207051f0c120e070512031b0102130e0601120c050705010f0c051e0d06170c010207150e0a030b070915180303031802 74
    0xb80c06085607074a5041c444028500308066107c0e5003044454020400107854200080341101e510210051402c0b10500c0d0681c05031400021840d00144040b40020900a00164681800074001e141d400c04045800e01c600a5900400b0b120001c61340500200100c0405980114042402e520640d04010744030400102c07940314500c03040c06107a0010620310504180382400d050940c1800000310300e070502a101c034221202c3c05128640c1c144c00940d00051159010b0280c1c1c0b6191003c0407010010103100c804054595049180180c485600c0d242880410382d0301482020034a6a480c0c03541da05103c92140007154145200c140148502e100f400700082220080c007030000a4103088a21885004446d840c40c5c0c64400f4a03171072141154481d2004125400101c4546024030a8905d0090419845103002c954041920f51000303010440384410040c0b40d650100350902a1340d00b010300f044070840300140031280402010200c1101c040061801c000003030299129500e018150a6800003000c0d140d0009070786013 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 57918672 1250 57917422 57917429
    0x5040608010203190e0706120b040c0320070203060f070c0803090d030e030304200a08030d0b041416080403030e16030605090d05070b070c021017060a050d230106 71
    0x50b900801402454849410f8001c030a01402d2420402d5440c40c3c3d0341a42ea03041c070343c40340605222000003001e541e010b00b90400003000748007600901c03041e000311310020001d180c020306415107003503603a044404280c610030445e0320107130f0001d00a03c5162542d50b000c0140034000b030051000c2c4801e0b02640c000007802080a50710518100703024084200c0c44840c00b5003900c0c03031003d80044c640c000708100000207450012660b01c0d913044854090701140340324081000384500d074100049070321010601c8140a00303143c00c0f848458406850a10004198411508040105460800240842c1550364412512035445654490301070301e00442c005448040c007500f46904160788181103c48003800b4401d0003940d000f9160810340900c0101520060114014050300840308000d048000c403401040010340301d087c82d80c09268008012a10400452202500400c103d4500d0308103944440e0004995160400b00d100885101401399540c0d0302140d42c881150700b042c9211200d900c015416071401d801024030503840503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 57919922 1250 57918672 57918689
    0x1020c070f030201080a06081b010e0a120c050406030201080403030f1401060f02070b0a050919050603130606050109062a080c011a030a08040b03130615030b24010c020a050406 77
    0x141d600310300004201c0d01c2e005000494490408000b08403040d4001140c44061681035000044c003012000100c81e0801403d05559100c03e0101d1b01280341d054410030003008903c2803000810065490061006403080c0e4403010340030404081c00a80464040d4000b90400c807001c143c00205460302d0f00c1140c0b0024020303046000000c03511005105045e404005400280540c041494101440148000d08a00c1400810b500460800c020030391408880220a4043c080040aa68492406c0c540c104506035201105481050800400040c10b50091b031959043d04c00a47d82e03d51507040007034003003d0040010310950305441000c1201c602150540e0042c003a01d01090001103915511308000c0310058008070300c01c9210350072031a03950b40050f58120480d01101c04c5a065942c40b9910714040b45406c0301585c0c80900701d0b40c00c1502c00c0020700f914034009015a03105176860605c4e920707880d200d45a55100d819a0f15101c1d0035040361316880351302542c512071000703200415007061641c5840c0401e00f540e01c640d11480c103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 57921172 1250 57919922 57919949
    0x60403030203070f0315060c0c0803030a0b270105010503040503070b0103200f060301030f17040605090a06170c090607050f0703170a020604030311160302060a050a0608061801020c07 80
    0x1180d50014281080d0754040c80d0a000c9040421522140268144104802d1240404e1610204aa2740030380300002d227109001e0303a8072407500440c520003603d4041e1480344503922115107a420f20031140240e0128041d241c000c076030282e007031400550303050303001034030503031301480180000350010300448081c1e800303144905411948400c000f1201c4034003240b1680c0c0c80e4401d0400742d039419001e8550000740c1c0e04680d00b100f61042c103483c6c00d08264110720450307804125822000a00810707070030b8110000b010a00c1d415103554018507910001151504d0080d1280014141c1503001b03d4242d9000302d01404000000030301c070902d801e2190341d82d14034044407041100c61030342111408109101184154010101800200f585000d035211402515010002d10007024181d690610340040c80c040d40039103149202ca800000300201040c100a542d5a10032200f822103031f820300b0002081d0303c0d01c901540e0110740400e00200182d80307070351021031102a189950510290360038041c1c2c461600080110000500c8121b0b071041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 57922422 1250 57921172 57921181
    0x1207050d06210209060a0302030c090403171509010b0a050d0c090807061d0d051e070506030403080405010b0123030405030d150806090c060414031c020706031d0a03050d060503060403030203 83
    0x2005140080065115408401c2c6c02c101589000c142000c2a0340c040301c486185564614058a00b6002c0310148d5040072130744420000792100c0012200000f24084032401280c3c1ea07903c25481d01d80c030481601100091061010b110b000005400c03100441c0e01c43d0030b05490107034940d9851480c00d021984a00d0004000c142d1045070300402e0303580b1101c0d215068400f002c4842868403000c2e6150b00900905840d120b00600c0f4001c1c900d800e1001c0009044014116035890801c0c5c10014030000007038070262525482d00b01d085a4642c0a10000501c07180b60100104034000c090315440c00a810003003041c0e07168081040711841d035403c0f500c10a007042103180302c41a030480c1080c110900c1c0160051400003141d025a00d0001035686074815181100e901a080c107019114400100b814105142c5860240b4010003a1703443c031f007035004284107080ea4042c2ea020060203c1422000004200d144801d544a400a000c0200803d100f100100325420700030310041183d42d41c58011074a8004221815070000c3c0d03000c024003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 57923672 1250 57922422 57922429
    0x3105040e0c060a180f0303050715060e0c0f04090518060a020a120e0109050f01050702010c0c02090c030603070b070803041106031e060d02040203010909030908031207050d062102 78
    0x829a210045004120030440345001c9182c078841c190444007480180d100e00700c083c20080b510741000d0028900c5003802560f0f203140c054056085000226500301600320700e040001e0b6207204407011075850011103426a1075050714001d4503400300440c1c02e0340007010003011030700364981c4c00303a280510100c2e400346220002c2500b4281c200b01c1d000e8802c0b81494010070244000c40c1d484940c0e0300b0003802c80ca0000515846504090780180f83d4420010140d004000070600304000640c401032286240d90000d0004c2c075010349040302c2110b480b540c029485044040030416004200014680c0100041c0c101c5001903110b0882c0710250b001000c04903190350f4001300300020841c2c480e003007205500080e170f03d641c15030030040d466200c802d03880303200010280074010000f0800e40c0c07668000e0424a8010304110341d2541c4030510800903142c900000e50100d111000000366075800001211115203445070368910a032070b00b09048620b50700c039082c401d03241c9444140104450300e040d1000640030010144c04c1d4081c04052060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 57924922 1250 57923672 57923681
    0x130b030a290c1206061305040504030e190b07060207020a05030f0a03090b0301060e091b0417071d010608060303070c08061807060203041221021b040501120206310504 73
    0x292191a94180502c0c440e049043c04455002041201c92a4541b00d0402c8078000c18816a88a01e6000d07044c4020701040c550000b62803031160b1f6050768070388180c401c0c801e01c1c2d141c400c08520405c0d884a00800889001c134405601603c95a0b03c01080d10035070540c0c480c0000d1424682c0854046c071030308800d4141080603002482e48008007042040300c0e045600d0100044c1c140310101032100c0c01040e400c0006903501c3c01072505550411144154652560340703c1e00700c4d00c40e5001d00c50944045200c4d040012840041000c10201041c405540b040781c641c1c05d1120440c0c1510020b401c2e0342c1c040c441030245c01d001034854039508014140103c010b00c1d9070302d04a1207643d0300d50400c3c2071241d202d0300300d51070502203107034040201c405450b080401d4098070b4040c0d141003070301a102040094805581c113000104071f00d50204007021221060342c031000380480801c0c20002216400c0c85901c0030b080c90000d0150050a040d00580300c00242142030b8940040840403480f1039003580d141461051082641c00d00c411718041c800e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 57926172 1250 57924922 57924931
    0xa050610060810050402030415020f09040f02071115070206120f060f060406030e030403061103040c0e0603030d0b0105190906020706050f1614010905010c080108010209130b030a29 79
    0x3400340762802c1200004010b0300c0980071380c50203150000005824000706092200c004c03000c00404565645c041c809c90715464010390f00d0710f0b2140e81480c16012500c91140280c8080542020307000030454000c0040000080040792480608002481000d001d80e513100007400382c1c00a2280300405502d00b0240c0d03c003800200508683c8102c01045506855448080654040c1c80f003904000800c00001000e007843d40c041c81e8002000b0b24141415451400a5100a1130041d4804d80f03103404100c1c1c6801c8502e2013280100c941e1a0194414082610444813a40081d11107080605005150803801d00c41480300f4017070000d110003c149941c0b02003010590420141008050307a00d0210700f082d0b50100e01017030b0ba04c1904407a0f00c3d00c0d40d1004268080c4060030741488402c6a125000b082066440d1600380d01234503a00190901003550314000240e00c20060084800b00c0c100100340c43c0300c0c505000c98580c002c240c8500040d40610540c0c1609000941105004941c4840340c0e00c3d0700100d2000c001c80c00c074410030052 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 57927422 1250 57926172 57926177
    0x5090a0e060708130f0606030512040612050a06090504110108090a0b010302041a030a05011413050309010c1103010c03020c10020427200a020c01030b01050403110604080a05061006 79
    0x21511581000824030702d03000b250910b40032599846642420b10000c15005010300700908403004001000340903401007003140d100e0000c1e1749084000031404200c03801688200000300346068840150030700c0755400a60310500c100740c00140941ca80d0b02c3d40b011540212000c84440c0e41030214621150381041511790301c000c00f14020590034443d9900c1c10a580b41c1032200030700907500d80105030a4032080c00980450101c0280403662100d0441c18a00c1c060030b0b02d0020b0349100e001c0d003000b280b401d03030f558800500c86a070450001c0d4500b500041c011684804503040940d00740b110016040010343c0e080c01401001d508542d00075031a00a0b0400613401c04090740644c43d40a441000704211004940d41404814090b561800101381c0314803541c40d028207010780b40507508c090700c0d00c40e081c6400e0100c0702501c030b049141e500b155241d540c150015011144540190350104006110800004202500c9603c0304c16000d01a1400e0584c3e50f00550310741458002e04503416086103080050402440000c0c000504480c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 57928672 1250 57927422 57927431
    0xd02010b09100b0306040209090702070f050d2a030606140103060906031e0311060115110706080c0c010e0303070206010302120613020105090d020307060e121f0207020a0905040c05090a 81
    0x340ba90142c03050b40340c0318010200101000098180d0f40c2c0750b041d501e11080c050100015403904810082d00c0c3c220901a0030325202e6003080208071400c044410800d460340c00030420944401076407c11071000b01421000c1e0f5041d41ca10030203c001403036801244018081a4580030f105660040058161821500100c401915003541000070540a08054584028004609824143c00c0c1012680e80805c40f642034954800c560001030764082c522610118105203541d2404030030300015905e40c503082188105030005141c1e401182d91074801000400301e40034041e000080c0e100c20300c0d58407030075600b007181c0543c0941c00950040083d8144403007640c802402ca000900450b01d42540b001014904801c0040c0c1000400b04102c03006454004201a03403e0700141103c0f601c070340c2c0d540300400411080c03040c640103400c2040000d4070220001452004204104403003800c0d08019a240340080d042403100b0f03a03000408060008254403c4d2180f0350140d03000d001c1e45034103070b800c000500c41110006440d511015203071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 57929922 1250 57928672 57928681
    0x4050603150408130b070c080f071e09050c030708010b04060219020402040803271206130305040b0406050d060b190e0609131a030c03030a0f200d02010b09 68
    0x4680700744a828200340c0000c040d112801d1821103401000742c5009102500034020449600c0c580103010070b64460a54150f0054407040180c7e21403051480c0403401d68408401070000301540d00c0105086030302c0c0514914100c0d1355030452002e84100b5110303004280400018019115402003c090240681750000382c43d0525155009541d0300d20910283c1e640c0c102701d1981d404655031501200e000300060003c403515240d007901c00e4404410f00e520007040f000c40ca141204001d041860b010310001c002031028001d02d544524188120403a0441c2c210100002040041040e21410026001904140c1e5400d80c030b031050142d501e0125085074224000d03145050004000c2e0b0070345005058003460070f601e806c0d940d9046840203c0c005009820a003a80b1200d0324488240d0841181c1c00a00031240c4590300c0d040500007542403584442d0348403001c58140c0c00400180d002d85014206c0b100c8510303d01d10380090b40d9800c26a60b07960701c039040481c041c400c0d0042d074080c00c01254240243c07070a00f101290868104d082c07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 57931172 1250 57929922 57929929
    0x110706060509010e04031e050d0f0b010807300b0a0807080601080307080a030b01020f0d0c031805030706050a0c0b0f0603011a0604151404030b061002060106021b040e1e0705040506 79
    0xa40300c91900001c0400004030108030711030300581c1d0360021484014404d50341c04ac1a400e01030f091900d85240001c202c0c10028690510911100340d424404580145040031070300910000640100d0000000e41c2c1c4580d60440e0903210f2000c500c00504440b009852828202074401c0e00303001040c1c0c402801c0368000c2c000d68010821540844258030110f090005029007140c0c0180d0403e10340380d000745810b004150b00081003030b81058074030891902c60307590340070100180c051440c000d40c00c5001c0d064041d400f00c3d034280300190242001b421107105500703003070000d131145035210003680704202d07104080b40c04d640c014015581000d001b000c1c100b5000280c2514410400701c0030800f50700551150030700080c3c0aa403183c404c0c5025403070700d0074070400000070150380750b403a401c080c6003800050390024060707071050703c0c2c541c14180f02155440c16240f26038040d22031080105180c0c100d03030502103071b050342c00b607070710403081c2c594503410040440440000340394801e98030170724140f8500301600e560001d0302130303410181003125594 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 57932422 1250 57931172 57931187
    0x20405300105190e0f010e010b01020f19111801030302070509151f03090b0c0a0207050102030309030904050c0d020309010e07150c020907030213030602040e0109020a0509090703110706060509010e0403 88
    0x4600300f40c00a901d40d214102c080c40c04080288040302075182040b60040028103400c01840b0071001c0e008ca800401c0203859841c1e4401c40903403042c002d90780b03c010b00400240703014000c102500d0700030404007a125122075000b40245007a4011005640081c000b000941000da0070a540100301070800382c0310310b1902001c0741c2d01c5151040c0003044203081540b000301e640e00950026a060ba0070100000451521341d5000010b42d1100d085a009442014800940c1d90b01c00000c40e0301c503143c01d0000d5400c22003002c0c28030018201c060300b80b90207030b682800204c102e8a05480030390301c1032017a1000031580c0004c14031940e080400a401142c1d0101c0b107074005c2810b1681260403c1c2c1102d605031005a0103554241045000303001c3c80380300c6440e036840d0203400420301200c1d030013804c1525113501072200d07680d90741d58401c0d0403441080036001c08520240440401d40c50003103107c85e40000d09c3c0c00d000c00c4040e00d20b51080820360054030103c0c0c4550392103501344098140b954905002d00340d06420b00702c550500340c6020b000c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 57933672 1250 57932422 57932461
    0x190e0d0b04021c030e030f0102030106050409090321021b1b01050f0c0607020a060501090c081306090203030409090c29130e010e0406140114010f0201020405300105 72
    0xd9025001160071926030628050343ca01c00c03820b00949500b81481c00910141c2c14482403031180c0b0403070454503141031040c82140d0490324030b911140e140c00e24052461001e071219030426802d0020482d1a04a41e1020801900030111004801030b078501560740700c0006076000968140c100d9209807100346428a40b1254000c95040900f0b1035a20b0f035011004412240c841d484074000c090180405001d059600055a20221489500e00b84030b01ea884001500448181641650000e084038001c1544104039089001a2a000d020042100ca100d500480c0c50b40d84564802500c1a60700e0b01150107000e4007011250260641101c0c03d08894034829060f0f000d4605052000c2007480c001605120350500c1402c000c00038505002c3d40d490540c0d650000da940c140c0100c44c1074810504012070104c50080380d40145042e1211980d0422250101d880110303080540e12100380c0c00d5641c00c10003c2803030343c0c0300c802c0350424a2081c101c601400884160020b854507840e940380f0201d0381000300307003d43c2c28145504000b0307a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 57934922 1250 57933672 57933683
    0xc060301090b040f0207030201091217130813140f0306010509040803100312030c09090b010c230a05030c0d09120807060902060d050f0112050a06020f0f0a0302190e0d 73
    0x11110b80000c0040006002101815200107000c80401d5010741204e641180107030a01c1c00d2640340f1a0701590290b248510301d2151030410f800060601e6850152002554010310945013414003c4c005803824200d241c020318a511040c682c88400703898186800648600c05401900390340d450140442c1c15010b019100a01c401008800200440104c0a0340002035402055001201a0034030000c4d00900c003640480d03000031a000808588450309001c1c14088280c1a550008454201d4440c204c0000c42e408640c01d105420703040040400c1c40070001c0d00145070050f0041d5550301c03540000e2625003500862244240504241c081007003202e24551925055041104603503540605e18115004003021400203500c101c001c1a20a80d44c1d00c15441188180041c5142c2d030b103985d0f00c4d1806901c8001d501c0e100149903500101c2d03101c0000700c843d0003070600e00001c246001e05281a64190003066002040403134002980850030240d020703d11200c144080c103003401c10842d460300110100340e01c00c44820000d001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 57936172 1250 57934922 57934931
    0x8010e07020c090c040e0109020702090f0405011805032703060403120902180a05070813030302180a030b04030921080306010207090501181103100312021c030c110c06030109 76
    0x500390092200040d10340c4000d1000d10350346001c0104007140c1d0041d001e65480207007a5000403411003200d02c2128074840d0000c010992035601c030504441c41110040044506540b552040082c60f000201d40032105031260020b152a007502e00c2c2c5080b1218010450525031003182e8805202d071791804289036400035010b2404000210305c0c00c1d00d4402400e44040c2c001d400854030b8000615103103104007154007426a2940912040e1503404c8115818002500d40d041c056040c41e070808000380c001d50044c00c0440106181180c450b21613400502440402d90055454001540c20042010780c0102068041e043e103904681c218880080c055042c0c0042000042c114207001000c12000d0703000700180c1e0010102170b04240403d40c0c4843c40c003080c014508030410a16404d008032000c0b41209102070701e01c03410204501100c030501e1901c07030040c000c501d0310303401c0150300441c1603294100c2110b1b09114410003c1d17840c04610018088030042030f46400b50074840a980205041800e41c0d038520040742c0c11201c44c00c40116 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 57937422 1250 57936172 57936181
    0x180510030f022715030d0806060301140a03080d0903120c0203030a02220b0c07060e06090409030c0f08031501020d0804030503060102010b030304090917120a1a06030a090b06030102070308010e 84
    0x4000402410311001e48900e481040101003400b01c429035550310603411b6401b0350341ca02c001620780450a070f5030380b64020028001032102c164070090b0552540402803502e0304c07881e030769241c448042d403110040d0800030313455880d12014103812901510114129007400c103c0c1840b01c1c14005d44a000181038402c00325000600200034411368400c54000310425419030070720595a03128080c2c0b680c841c0090510501a2100011b16580035080b2030b400c2c2403014200d14681180401004010b01103800104c05020205d05c43c54041081c1400c2c0f210300a01c10500716039282440c880e03210142e81031040e124119400380d0040400d03d58020ba903e034200398141400d90b200d4035100010f07405805006512605480042000544107045070007505410380116028403580300711030042170851092104501c000d03a801008500b06610f20f03071100007849400c14408100301a6000003401c40e50041e1010f40300725031240c00c0324051082600885821602c00c500861412450343e4014000040c148505c042d00c44000e80000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 57938672 1250 57937422 57937459
    0x40507060c08070516090608010209060f070c0b0a0804020f120a030c0201260f060607030c080c1e010213050402161b0b03010b0c0f0106030317070e0901180510030f02 73
    0x590f0025401402e0703c902c0c40c0717108420000d00d00b03d4460000200c0c241703080001c40720b1040c82107031f203a008080c1074070b441c0140845031035a25500a130401c5a01d02610103000a0b00000c080190281c628180e4a842590600c1d004100200d05080f40c954400c00101d9015200301ca80002c44000d010b605040140c402d00060005031491609241012284041c0320400b2000812840040d48100006401203060342c42e00c8080c0805400381c40e030014082511f41c08001e0200b01c00700040c22070a010b4800711f42c99000104140400d40545d04058500d60790045610318615811102010243c00b00351021420442d034454901640d58811001504902c16000c01c118112003414294026044502d2006d0792569100d010541c075511160321003000c0e009140c03852010340010b0088408490301503550382281c120600f00c0705103686c1c0142208003401604040b012264880c91030307050003040b058506220703a109440b042d5050360170041c10b05004200c0690188002244402c00c45005601580e0124443c1200d0844 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 57939922 1250 57938672 57938677
    0x30f0f050d110601090605030a02131b0e01020d0212030a11070210021507050a090303080601020307240c08040206070305341401020304030f1404050604030501051e040507060c08 78
    0x140c4180521420700720401d40020655280c2180401100c800d40e03a28910300c0112031140c020103505401c904030b04d501526105241282d0744903444000103e4203a406081113180f0140d00d4420081032958980031480e43e014007440000d03032020b001500d003568000d01c41c0411440014111140c15540302000940110039034140d65038181c0c0645003051844640300003030341d00d10b4030400d00300d4071002d218006a4660720480036611011040d032150760170313113086503400c0c2c411210042c00103045110510121002c00c248215964180c0d00d281c82a0000c0c0811091b10800e45011410402c14010b07003006110041e00c40c00700301e561480d0580340c1544c407041e1b10440010b52103215800540c55071045004dd281c1200d081c1d10300784030f0358881c1c6902c00050101c425050b085c0d000c11075000e00400c98070805a01054019407a00c070070200b10003032642c6099180c0c1d00181c0542c00c181c1040d105c5a5460082281141054906100d402940c4400d54010300c1c081c2d8a0658640c202d008680801080504d61010460301009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 57941172 1250 57939922 57939953
    0x130504090c0302040612050d050304061410180209031207030207030c09050601080105040b06120c0c0a030504140f240417030a0f030605010215060d050303010e01090e010b0109030f 79
    0x82480140314034244030804038428042a441145040303030006086041200c1c6e03901d03096204015005062854800f6640d60300300178802e4070041d880d0443c0405284079514010301c140041510590040d090050240311845c41d03031000f80d00c0701d20400c454402135500080400d102e41c0740c0140700390758401604d41242428480d034001840419020004286501140c00151003042c1c01c1c1d0b9000a00d03a602c100b00710549132100d074a00d4000000f007103904200d07071090f41001e03440a480c0700c80d5841c1010905c280c42c9001400c41c800d5001500c0800e080c86481528610b1100b0b1003400c40d4410201c0d544140011822052003000707080d01000120090303032907e005810b840040c00ea803030030b0050302c007012050240c803a4001402078001038440000499020b000c0d00c1800280d80040e4002c180303408059100714114040980550303030103071032007451b0030001d0001c00c02940078180010008106500d08101181515a482114266a41000d5034034020740d0b031080c2e08108694112000c120083ca542c2484001c0d9031f81c140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 57942422 1250 57941172 57941179
    0x110607050312130b0109022d09010201060503070605040b0a02010b030d030605010f03051b0c03070f03030b0102100507080714071205030114030304030203100b0303280908150703021305 81
    0x6215014000044041d000c00514100100e006540310206650950054000103003a43d20000041c800350186501070400a2104100e10054695180740d030089400c410150710101000021492101c0d6820301841d4010f210a5004041950600e00d01500710b002d00e000c2c41061640100d40407032043c0c0b0035002104441406001d41d10301c1d4042090060281500b030007101d01280f100d55000703000034420301c5004d01c1251009140502d40040d82c2c071041c03d07139100c0000c01500b4070042c091705002ca0212806d0340900f502c02d84000507030f032914400282c10200d5181600100c1da28007010400000e0300052180d620410914000203100d80004c944a410f0040034000780017031400c00341160165801800940c1600d1325910b4407061810349104140d030760705c2507001c029016088240c071262440c00f903812010401600506690410982c8980241c84041003103e461002d405070b140c1c00e8401d0340000008000c0c200f000090580000844201d032209100035056000301079000800a203190b410240703810140a009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 57943672 1250 57942422 57942427
    0x403230403060b0d020f040e0102120a02030f091c08100801020c1006090204050310020315100309021509090f0603032203050f0307030c060506130f050a0b090105010203161106 77
    0x40012805400500044032a03601e0407400e900f4038642540407600603030f80103015040e800c2074601444003a02c444031105401d5034080c4451850403506d0f41265114600c003141c01a04da21300b03101c03400c2801502505201070340c1c10015045000744010002c3c81d600c2501400c2040c000d86500d044551211101c0d8480480d80d4400f0415004595010a01d002a855817440910001f43c840880c20101d2081d40700c9c460745940f189042c81190310840d00650307070242104400d501c000020f42d000c12008106d0300808070000e9a140881000c501d00100d44000482d843d800f4a801d00f000d020110368a4480641203c410444040000342150303070420848030710031002150a2100e40f5021184248011140802c64250059031181c990044000055070f00682c3c0580e07903d024217102752a140006e000240c20300c0e030401c0741000072007500e4161307002d40007851100a800040e640f60a540c043c0c2220500b116041c07094241c00010003081e03034000181c907111905012501e041000c0c9142284918684503201038110344003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 57944922 1250 57943672 57943727
    0x90326030f0601080124030f09050a051005010e0402061602150406210e070501050d060302030a032105070206010515070f030c1a01080715020102130f050a051503040204050403 77
    0x1401c901c035020b00c00a032035080b15a601e40e000c517943ca83c0c4031005459002160802d100b0b91038401e4025440c1c5400300d5070300040441d4140c0b12103042159110381520310703134803608144414482d02c0c82454010040405030400300e040650000f0342900c504a18095440404000c04042d5619581884205612384800341c0d0790303a603100c001400d0b0403a041c00c1c01090729840c0114a18120a034018240780303140c100702800d48075040500543d400c5d000f1a04d010a4142d58150120060310208040c01489010303840340e81c03504000c50072031600d0080c00c001403040b0318100010f0094181d00010302c01d054a0741155120f0300000e10a01c1000103004400c806014102021641800d241c0c00c030380b40808603070040042e1190807614071144d4042d090b0a100d8065507512003101004089030108448206260f80c0c80098500040e00d03410744800d00003500880280110690100308901c2c080c0700080003440705556040801440c20703405c0346503010040000c1d011700c0e100c6c0c0003e82014464040460040c0003000508039032179a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 57946172 1250 57944922 57944941
    0xe0705130f140303160b0c130e060406050f0904021c0503030406020c0c060310060f0c05030a030606020c2407080c120304111503040204151701140705070309032603 72
    0xa03184503080c0e141c07498008007000d0f428040210707400303984100e07000c078440ca50765070f9403249180004088130109041849041140c003900b01c418001044550760000c8a8200702c010001107032002d9212074440e1103659035512454640c8441940d1180c1c044804182e2401c050882900c0c0c040c2110005000e8000001004100241039000c0d094900145c3c0494000c003c0703103c14800c10f440280d5041074a03120281d000c00c426403098241014914076442d00c081407003880e0744c07034a107150048004a0013203511010b050140e80c0d810000c18150a2045403030880540308880e19206107009010408070000002910001740502c180844100300c03080c500300c42d04840c1100d00e0b58110307041998100c44c1071841d040e601c1710500d4900c503000341c400d02e44080649161074950810008280d941c030a04000d1100c6c031000203410170b03010300a05140b005031002140c208050303000e02030301c40c4000b00840140a810301000c2c01080d0721031142c0e02684d03030007114840403000d2807203140050079180040111610002003042008070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 57947422 1250 57946172 57946199
    0x30c100f21090302160501081b071106030405010506191404020c0102090604080a03030f020304031e090306150f0b0f0406051608040906030515060603130c03050613050601120302070e070513 83
    0x5c01c517580c1d0b4849842c0c0c0c0044810b80002d43c1c0d2002c00180900b4455064008080145000b511854141c0c000d510601e0129a0ba9081240d09862036552001089110f04112544804046141403001c0d01107040c8100440d02c1811006420302980d4085001114600d00b5411038442c060014007254413980e03200a031300c2e0b441c0c119a0003200002c1c101014201d0401041c003d07207001d03940c035490b01c0c5200b041060740c000a5007907118522041104100c000404118244103c2e0901d103240301c440c9262030b0410148440011080e0300040030941c00300411a140000c010940341601c80601d130242e9a0010315002007103011184401405c803560002d0300080242d80c50744028104da00c54000e8a140000d42c1c0700018450800301c2c0c0301c582103101080003d0701c60031444807a466080c072070103810034015100d0300c0c0c00380350034001c640e50100c1d5100884250b013030000030050603004008003024106080d20559009403115560300c01d1034002c218040100c0d11440c024004c0d6a4000030030703603074241c0040e682e10361980e500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 57948672 1250 57947422 57947443
    0x1e01301b06140d0b0d0f05010203090d08090c0111030c0601090b04110a0806090604091401020904060816150905030f0d0f05070804030206030403090b0a030b030c100f21090302 77
    0x10400d00000140c25000300d02d00942c07034031904100ca06240702e503d1900c010301603603203104d03a000a04e5260000000c02c6004910300884c002c500050b12841d10350301d40c0717140444240c5548207200c80f40b41000000040015081e451507001e01c1e103e0800c0c2c0416850a14601420190b0100380c0600d60001ca01c004282d03000350b012300404c44091001c1c180d002c2e40c1060f07520507080410002000500000c880e4244018803541021000d000000c01c907400751903140c19480811215000c99400084030005031a003070180401a040000141021001c40414071340351210b1441070b00d0300c40c1150202404414058144040148400713403daa075004640ca804945901c092038144010908460140e0400c522620660300001d907c400510710340307403c5400700107075038000134012410026524008100241884090315a0240350307240410f100f452441050b003056440b81045007e4544070110900c0c840c0e205c03202140c40d800e03600700000341180e44d03040e040e020341d209062440c074030b802e19407044101a030000750140c0c90b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 57949922 1250 57948672 57948713
    0xc06080712050412080411030109150b150d1a0a060809070e01050d02010c0203010f02070b040618020607030f030b030d090303020105090615090705041d0403081e0130 73
    0x1000701d0030038a0048810644010307081d0800441d80c802054040c00d401d03070f00580070300d103460130f002d071500000303420b4424001c8220b6a050704105a001038407072030300907008200c0040b82c00600c1c400302c081c880d079002d000d81c5481390301302c0d03407030f80504641d0780d15080184884010103000031903256283c02d0b001d0403e0005031807030040fa10401d40002007041400800038181e4100400d040803600c42a001100c1d01d0011503400da9042d540c42103059220b03003d0b84010302d0036604c6030221101515003401c040c0c0442d041d250b00070300d01201801001c001603070b07410225890340346d06080c82c0380c2181d45904100c00800140c014150584641407000440070b4000c581e88007181c0c1b080c2d00a0260b99100c400d510344500090ba020807001d03030800c2c80306507103140101d074440d03100c1c60714500035083c40c0c2c2d00c0d249898101c0810362a031008540c0070040c8030a1552084c035244d48880ba1030028540c0781d0b00403404a14120781482406000001e0b84070b10101c540b60f6005551050b00c09440d20389240c1c00ca41017981108609604504a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 57951172 1250 57949922 57949937
    0x708040b03010311011d220501171203060315180703080316020a0b010312021203070504031406150415090e0d260103080d0e0f0f0105060a050306010911070c060807 72
    0x21540c803944000004030030802e01001b41420280511a91442e203000c0030b000f00d42a031409841c040014031039503000b841e003e10005142c40c640895142400c018031045043e80c0703c100100702864900140d07240031100450710040040d50303001142050610114801002406220740003c1403000050145001c5c0b48803240d402c411052000c0141d0baa6070304451b00512510421004002085240e1606881012240140d0320b94003a54410706003698402c640300c9011a00c045010700501c806455080752103072501005100c1d40c1068130307401c0051502180914030840e1540381d4000003102c1004940000c2004034030a100c19220031580c65101c12922542e40009500c010110070b0601e800c80f003000741e041e5142c4840480d80d0840d103d10002d5070240c108000d40ca40c80e00e000508504081103103031000f00280001c0c25200107684000c5081d180c000d001c0603c40c00b141141400b803640c000c64820304640f80c500c40080c81c2a22600ca040142c091000f001e0184c800c06c0c1400a00349403c045010f200f890717666a0b080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 57952422 1250 57951172 57951203
    0xd140a1104090b060f04021303050f0105070302090108060f1903030504030b0609060112090c0e040305030a0606090803090f150c150703090305090f13020327070b120c0708040b030103 80
    0x701e034038400e0043c040102803404200c8034180380c44040c51648005c1e2000d0303e4507170b40c01d00d526100c000d5035004032103c0d8803242c0314a10800b005e215813034004405140961401440c0000201003000c0070b080305105602541e002d090507907a0064002c18150542c0b014542e03076076681000b03040c3c2c1d089031009690701c040040000303480b40390000009102d0941611a40c80e4902150500703401826850000c450040c071016001c1500c0d10b4484104e440780c1d100ba5180c9a50b840e18500c020301303403081d0b40c0c00300c020b011201806000580011040d6508081c1c103440c000b1340c1c01e0101001840d000d002515504404100003000e4100f40408a25081c0300402414200410340311007100f14129956034402900203101842642420314190001550f01c60009040da0341441c0c0ca400c5ca10202e0b80b0a9400702d0030001501c40b4801d03100c4032600d10600300001c0c1c00184c45054604056845248600750f010015613148100240584507110141c40b00b9540095116403596220806004550310070300040d540245400c40f540e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 57953672 1250 57952422 57952429
    0x2090310020903030f1605070e090f0c0901060c03030f050a060f060f050d0f0e010c02060105010314040f032a12090b07021f0224060a0806070e010503060d140a11 71
    0x1111109800f9004500e07080d45240c41c4403450b00a10301200218504280a4010030020410503010b0416a26000c81500700165090314001040210801681040003500c4407962000f841d5030440f042401d00d60222092032804030f0080c0410800c4180da145480180180c03007a4503070151068405e48003041344000e071200030a8500350000203465001400820030701401c042a030f04944a000b220b00c50208190451105071400c0d03c1c4d200b880180140c0c0300d0710040006607490b004c2d190010b5055080001c140c1401d8860201520300c11101400344001110074079840c0080a034403100c001c800d600412821680f5107059010100807601c031000003507a80d4004240005210708503034110354003c0a80d61079000c00c01040c1001e00f0365810300c50540c001c3e42c0309120309014807580d02074402c2000c4000c14140c80d15108014030480250040f10050b4000300400103060f1304017100340041c03e000d0a001d0f841e95102c2c40011800010304000410f00e0f00507256032840103800140040c409441400095600040300e0f051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 57954922 1250 57953672 57953677
    0x201030507230d0f02070b09010605060a020c10020a0b070507050c011b03180504110904060603020a050d0b03101d010501050f0a0e0406060812030a150311061c0507030209031002 78
    0x50490266410302c05100440844000b0700c0c40040c0d450021541c0d083c04003600080340c00144003600e035080314034100510f0000038414080a07000469040e424070001140017550340c0c44a0002500a080309003038061a20700802c00f01114941c008019241840d185100506a410100d8111500d00c10340c1042d02d0302d90300980c40080824810300d810001c40009490031558428080d00d0700349001e621010100c0e81e5200d41c0a15286c1c0c1c5002651241d40d01881000c0c00203d41ca1680410205403040c8141c00e02c01c0e500604850400014002c08941c0c0901c0d400003034145071400010300c1101e490000000e40a20098414601d4102250b00030841c9a0741c42c82402040600040015404210794000344154440e031455143c10500608000030a40d8640ca9164500110302c001100c03506004810448560000e0241c0c1a82d0441102420800c0389950741d400d91802002003c40d119002c08039121b040145500007056100c030340d5010501050405120180003540044c070114000c0c0118202d003030701401a0b008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 57956172 1250 57954922 57954947
    0x807020a12031a0907050703080f010623040b030f07180e01150302041e050a09140a020304060b09040b19051e060303040b040303170f0405151003020315040201030507 73
    0x41c0d100103840d960000c500a100c00b0f00141d5000b00c11100b2007000f038a550280500c80e0040340c8400d60b5802c41420301404200000784040000215080140b01c0386500c00c42140c3c0c118944002e0086080c03010719500c90900894100640302c90002c0108482081c41c01551801a0400e0702c0740003d0b60500200d0500c0d0000c0340c02880c00e421505c0380100021880c00d0514030713900c901ca00c0c005040070380b41d00c692a030307015403a0410100c1040b41d00c0140032624041c96540700800e0f8181e0200100400b52008001b01c07a8014600510300b0385c08400501400030700d8118444944c002080c0d0410b0785028941144040c0040d2140c9007095084040c609440096100d0305014285034a04848248100c0c0d11188007114001c0090b60035020500001951140d0200030b00042d6109445030500705d03422000710356941030000d02c2c401005623003c00b4000451004541d1110f1044842c00c40c2c42a5610310b0920450400a984000c0d054407078140301e044503c10515000380910302c02d83e824130003034942034000c44050b0403158 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 57957422 1250 57956172 57956183
    0x40303030e2401090b031b01050a02070503071511060714031b0309010501030b15010e100203070206120109050c0708090d02060c0a150506090103030801060c02010c06060e0601090f06090302010c06020405030f0d0807020a 96
    0x7d046039660003440601450905441299407454030303003010034140710890744140c000642c00c0010a190300d820010300e8064403480c0d40207000c01e240840b0f00074a08480038003044074079072001001c07030080c20388800041125600b130b11540d130b524100303c88a140242000d00c0165005108400030079075120501c1c000070300b10101650781c2004401e542040198034529940214250300c01003040a0050b107400000d0040280420030801039507242c0741c12802540c40c000c0501001450400961001820b4032043c1c9900b00c80070341c0c01000c4100148042800ea200e10b40418501d881401c2600003005403002200c11ba003410881c0504c150b807603803c180300050740d00703000080114400c0030041c400c0c64030500d2001c4040c4d00500d000145006c10351200011213195070031020701e0b0740c5c5000421046503044036002c0700410700030710701b03092003407411000605a90480c00000d0400244084090078459241c041d940604070003010780d00d00000d55821141c0d42d4a958550b0800310310100000b80405001203881e280380ea4000703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 57958672 1250 57957422 57957463
    0xa050a020622080d2d06080c01050d020d0905030d09020310050105030d1b0803181c02030d09020109030606080d080121030c05030705010c09090f0203010803040303030e2401090b03 79
    0x43c1c2c0c40c2c4105030400f450898040c0c2e617558414440491580075128080d264070602118004000601d80540b815030f0003846203503006125248087e40e000c411902803030b585180058a03082040c1301100901003489000e0040d01c00810f003030701c2c0e00c2c22035444a403940d072007202140c030349141300740303c410540345c0134440d05074035800c840a09010580100c2d0250101d40d01c47c190b0100e08240c503030740c01c51a07070410b88542d04c1c5400b0b007407000d468120301045840284006251580001103100700d000f13540e0b10031220703e081080c0e21000001c1c11a401020390001541c0d10034014003045481d0a503a0766a044c441c4c0040c00061910f8000042161107030004004400031560080c2d006426600c007a03600c1122820b04a61601c81001180040384080c442c00c4415401030352003c001a2030010340c2d4003940d42c020704032603440c0c1c410401004401e100100b00e400b2290706080200d032410011070f4407820041c40442c2045004031f42d5800740f046010001495060728010103003006004c40200615960340107d160380500030000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 57959922 1250 57958672 57958741
    0xb0306010b0708030705070807060204050108060919230c030601020c0a031e0804030b0f04021f08041106190c020a062609030904090302010e010b0108040b01061101060b0a050a0206 79
    0x901c0c1c000d6505c1003035420920710780850740c1e607111309a6008140c1a25015800b150506c8a90b0b84810380b9500040c00701d030140340ca4207201d6408442800440300712400607550b980360702c42c1c8568602d022007007014143d03040ca04600d400e409055485c0e20031110240140a07419501c22036107410180705045d80c0e0810001191a80d00d14040f20141414610036603203108180000000110440002d03842000c03600544111401c1a10520400301106811a08401003030010781030400e07803286125070f0154000e495102c42c040000c000c12000d1298540c0e00b42d500d022102c42c0e01e00c443c0c1102c0003000c0c2c01e01c01c1d5000d41c080c680c0e0b440c048440741080d01d01981d00d060710b207005200c4000d500380b129801180d8075003035070319161002c40000d0440b900c8070340442c05070f511404069141c14082c801c01c000200c1c2801e24440501d030a40d00c3d111f000b04140140e4043c030040440d1100032000c01d6010b00d024014920030199907021012014102e5001080c1c6807005100720300025444111100c01a451b81f411140841d406000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 57961172 1250 57959922 57959933
    0x1207020d020318010504092409050105061819032114030703090203070806090109020906090f0105060703030b0301050c19020f100209060903010204060302040312020c090f0403020a0209010b030a0b0306010b07 91
    0x150484068100f00040c4001f055080840c46001405511181d6406020222205074504211681d01c010081c0340380c00010031280d01c1300d40c101c869140c0f42e2441c002d086c5090400044224007015034441c00044405d0000c8100b0500200041c14580ca0100341a94000e079007008a502c1c0301318015010082c001803010030b0085010b40c10030342219100a09030fa42c502e46507030700d20b89410000c0350262602da44621002055040900100d90818020350310140c0c18a807500d0a04917004041c4600d50003800002628002c0c940b181e40640e02c1100014003d11242c1400c3c040a5001c0c0c1055813809141040024410000c40c00003032078565000c0580c02504645402d0f960580094001007281c9801c071400704100c9519903404e1001300080c1c0055140103803258110700303150700d00c8035214440d482554031120300803040d1780d1244015a4801d01116000b0380696032498101d05080040740c1c000d4104c202c00c0c0010a800350000c014500c16280c0c542c00b002406109410180d80304028400e0110807a01000708101055 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 57962422 1250 57961172 57961207
    0x20a090302100c021003020d0606050705030f090112050103050a060c02011a09060111030c06010f050108040506010e10050d120807020a03080a051e0c0703090905071209170d021207020d0203 83
    0x40043c00c00b010200030703940104080341403c5051500180d130000d80e054000400b442800054502c0c4e01d05542080c03034580c1e074640d0345e20410700c0c022008480803852000603881510004450403c5500511855940e4949640e4444105200b103c04034141090f81500300c0c4140704040303081514205c0404032a81d0101404080341002d0b2016040110800c0050301d0113504000070000c2902c0078000317001c25803401400d029041c0300380d00264100820201804003280001595038195443e8000d0b014050300c9000744c41011503d940d001c140c01170704018102080c45004130341805000f40d01c2e00e800d4581d42d202c08040b600c440394440c000b030224114102203010200e181c2c1c8019400100158034540c40e0119811407e8200c01c1102c00300440780000900d041015803003034000d4003c0c0840341040c030582c108450050682c48032140f0841c10140c0c1d618910044c8009504554009289039224990f0b94bc2c03a108620003079841218104814103803840890581880082d01c200c000d80f03a94069030420f13605101a071181c0e0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 57963672 1250 57962422 57962449
    0x1031e05150405010225020a0801061a09061603020109021807050a05030405070504110c010c08061e030a0206040f090e0307050303040813181b0905010e040207050102160b0415020a090302 82
    0x41d03500380400307034540034941059084164085a46d14400c0c8403131042181c922610340200302d1590602e03404100c00e00c808000e004041e52003091003a25003e011000c5001c1c0c0c0038010f52241201401a50b4000b4560198003200605000f6906254500c00c110f582484061080c1c03214400114204904140b140c416009160054815015904030b03d47c0d0388006009e650329185034482d2040000fa0b03481030040d0074846c40040b903125040c20207a0b0300d070010004407007001032a000110042c0d07050590325965800c0c0071402071703250300170b101c075494070b850300f941e401018490b0240c01d001c24940095025144400019101500c1d80540114030f580e41e40d5540505540124089410350300502c0400b0410b03440e070070714241c03141000d401c0008840b42500c0407400c40d94940094101444040d85060000d070768091301c246880c1e10280d0b130140c1e44140d2850020700910503000f681d6100c85281c008001044140c110103402140180f140750401070001681c04100d108401000c000b1a80d01c40080006040269611021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 57964922 1250 57963672 57963683
    0x30132100521010b1c060617040503071a10091a01030902150403051f0510090e030903060103060c090e191e02030a090308070f050f0f0c0703080301031e051504 70
    0x860941e0101044400003a040491052804504039080300030340c03120105480d017a810240310081c50060042c00c002031040c1001681d24000000500703000d01001100c03e1598440307030302458009020811802d2840544084c00407403403d4600040c000c10034090121040740805034104009007050054000f0850003008a0300041c0303101c03444800c1e60403d0302401c011070181e00500344004401491790416001000c03560003861803c0d092040c10803102141030705503618030000061060040300340c145107000e0401aa580351041c20004420004c451708280b982440989560300800d07101c0304100b99142c411110b4008141403505504180282508010b000d44030710102280e0412400307072110283d0b03000b110312070b2a41d6181d51241741010352204d5010f900c0081d91805101030450110001c1c064807828100c02106107001c110128419807000483c1d0340c0f040b0318401c0baa41196280b0301284203030802d03c400d07504200e4101861104d14941c1000313040a40d4072102500c1056400c1d9034a42000c10302520a41e030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 57966172 1250 57964922 57964957
    0x606020709090f0b15040b0603040f060f0204081617010b0102061513050c0c0d0f0c080310170601030507051504180b120c040605040e03070f11060301321005 69
    0x103c1d0380c003c013071405410907a411070545c480342e0040c0026a074600d07001d240a00e078200200301c003003220101c8010140d81e10508c003240100c80340c1c00c1c0b0f101901940e046810710f40074001a0400016059042c44102c46036802d0f07140310a440c16003803d08a41c88440240e0160b0072500c001101710496000303885590000501d1401d050341404000401c44000b180c0340d843c9000300240402c0c074404104010319500085140a41c802254020700910568184500804c00c80340071011031000c641c40b03110305020748000e45005042e042004111540c91400303220903952801440e5001c6003a007001050030051950380310145203042c1c504041c2c20701d0045d000010710403084c2d4900380d121440e900d1407a0b9404c0802c00000421145171030f2800c100840d03003540d01581c4902d15202e00358031540e4020095908180e0856a01452583d45061030700c10003074240030300c030360020000002250303a0300103d002c943c20310040800c4910302c0304988082580d1102c1011120b9224a1000c1da01030b00034850001490300310459443e481 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 57967422 1250 57966172 57966203
    0x30f0c10080a060902030c04030303181e0203100c05091813230f0c03010c17040b0414010c02010615020f10020c0109020406090204050316150f1b03030e0c04060602070909 75
    0x4a070829991800b811f00000380410606516004220000240030384d08400240640e0360100f640c15014449004010035000c154103542c0c0c00d200c4000b50300e030300d00030600ca41c0b0f000a500800903401800c078030b48607402e406980034202d00300c0704880780700d600c2144180f40b4000700d41d2505488110210701c002c4240168038504800c000d410310603104166007000091581c07070001c10803d0b0a480c0840c000720304000c4145141d40d494800c80d10034a070000e070892b0002c515911141010700200480500060056003030115444032160b055006e6011070f54100c0c5609070303458200100302e80b06c1100d5205003038103a021180f484000003807030340180901a0050000240702585601103026119540d1000e030742d241d07002c03400300454103080c443c012805901c0d03048100139900303010481c0350302032000e41603100b08507030f03c0c42c0c18201c1d90140b04d0108501c60b0803c03410002040a2400034083d0000c0e42c03565556025080320103d20b4200390140106a40680c0c0140103507905100c41c44006007002041a100d4100301c180d0707071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 57968672 1250 57967422 57967439
    0x813120c140f1606050901050f090f0315090c06030105180a0b031e0601060206040f1203150312030b0303090a090908040e0f07020c0d0b0103060203100503030f09030f0c10080a06 78
    0x6054042d000c01c05450048224084844403080030f40c41a014400208030312580da85c1d1010489200104000e841a01c1d07118050204031440034031000260540b14041015040c00a440c0c1c500b4456100c0380e040792000e010403018802c00b03010030312074507400110070000d0aa01403004008a40d000c90840400201c0010480010b45810f620340c6030440111901c03c544422042c080c00300602500050000300681e05081c0d4400c4600443c604000d825244565494900319119401c0038410049280310450030a03140c0c100609225001030410000c280340076120074003802d0110a44905410081000650300c0c648100f010141040160444450b00100800716449220035030b40c1e402031070f007030072141e9451a084001900d800456030b0030f81d1046011080980004002d8100a8190fa40c00304003d612034854510003140c82c8440e0b00140d5160002041a040111302d43e809001441070071000c94050f56003448100c1c0d140e201103403005070840b000d2042500d07118012600786801124400300083e50f10782e5041e09 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 57969922 1250 57968672 57968683
    0xa05030a030c080901050105030a0b0709080d0e090a05010302011b02030c03030f030f0c03090303190b0d060c0306140a090b060f040303080415020c0705040e010207050105010806070813120c14 84
    0x10001c40e5070740304180010b0360320a1015070b0043c5004c0c020489541010000303603903035162000c000c2c0014010b9002449603486110000f0040c0301c914115840b0032040b00000c1d1001d0b09459846000e10283d000054810016004840c100c03a01a12000c0d0010a00c041410030f034071074480e0590f0948560780301c085583c0c07001c00c000d0000101c0c2101140c0c50b410100c004125002000e408400610707424802c0c055040d07004030031a5004084294000508007030341d2551005030188501996202c442e0070781d207000b406160341080300323810280c1e582003004503105c404459002e040300c1c1d0400e40201c40c056043c8565081c542c041550700d540284420b0070034005082c88000d540c000d404c200c0c00500c080303061108005c0d0140c4024050495031400750306090082d104241e880300c0364814a44515102c0303407500c5490703400b941100c190540040082c441580c47c0c6003d01d0741c6403002e84084000900c40f1f0001100ba520b00b6038107100b450750011020311100302d030b403008542d540c0c00700c0f1007500e00011039809038003281020840c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 57971172 1250 57969922 57969937
    0x6030803010f031707050d03020307030b0607030903060b030f0703020f04020f0f0a030b0d150c11012d1506300b0405070525080403080307020709060605040b030a020306030a0503 78
    0x15110031560541c03a00d0340800e2011400004144014030070880015001f1801ca03007980c0561400686036078800d00210f003d030030003841c0326801400018488081c168040c4411b000c0e03e000c2c031005d0002d8100d100902d070f656480e0b9041540030b50001c96040c401440d14600d51003203544010009820020160300c510711682c0b1000c468844c540c2c0020343c120741c030394142c06480b03512003084480480c24145c40d10340d08131548004843c480c11656840401d04000d0092280c5d480075920f01e4000c2040701011085070380083d410034084000e26900c109103040400d038500826030840d51800d5400009807500c201950542c60764040c4484104410300b4481c0700b038003255517030111040a400080741c904041d40500041720000741c00c1c2000c011040041142e0100804c6032000703440204044010740c002141071071000e03801907410082400d180001400302c400d60015003541646c8542d88101300b2543e0b03580c801d8803e40320340c0c0b0030788188040610001c0c042074200da02444d40305c20040c050760768426840e42c86500b11740c003005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 57972422 1250 57971172 57971189
    0x31d030a0207080606060f0d02090a0806090106030b09070f03033f05060a151b050a061d0106030c090c02010209040f020a120b061902031204120f030227040603080301 73
    0x84040200c3d4004026158002c001620f0451a10240c2640315001e48507103441c092030b454001580030300750784801607440000d000d42020381701c040c2002c2c82405d01030042440281c6117194a5000f0802d45107011585104981d21000c0030390241c3c2c83c681d0151200c0d2028900003c81034142d40140d40041031412a2100080c070030b954880c028408c04401d40d003110006480310b8020f403030507441413200c0c10b000d20113010a0403880c00e04201c040004c208101c400c0c03c4a40c0c0c0241a805220b041004000498002101c81c25012440000d0480c01c0c03582d09080751400d2001070301c00407050504000e252415031180e0f180301d105100140c600100c1c500402e003504d101d02c0c40c101a42d64002a80001c650f84503064030004000954184050349030340300040d00502030640900c00d01010220700e8a000307070007003007201c180042e000002c0400d46828101844400410650300000c5441c030920980300c0740c440d20803252074a22001c43c80c1c0d10000d41c00c40a1111003544030500741c11039038400f800300105503540c01850003041c001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 57973672 1250 57972422 57972433
    0x30a0203040308130510020f040b070501020a020f0d08040f03090902070b090d030209010203030a0b04060e090c01031505090f0601031e0203160c05030f090a030b0c0c010c08100501031d030a02 84
    0x510340140707516402000300404d6a490351900c000281d01141042c402e50302e2210168480012001c160080d2049502400082400007a09010440107401412103140c1d540c00303a0321380155140500c0d443c0c50a03401044c00088c0b1500014000420b1100b407400705601a14000240c10b46800c03d401c00caa00c22181a206100201e04001d01e1030740c10844454150308915055007000701260010b0b42e00d000c040d142e0301c1c03003503220740c1124003a4860780d22081c01082c51b0040c0004505244401c0e54170354070960005800a030030610351010001136071441c5021101c014101040304e5407050441c5000c1d603006401a410144c0350783d0022048020181e6929102d041100016580e007801c004078001644105410703000d00060041c00b401044000c81600c0012150b80d00059441c00c9002c001980d400d81e0307030001840341a07094103000103920b07802e020f802e080c00504020013214404600c141c0e9030341d0303048800099900c40c10205000e1035109401c07024641c0300781031041005122404201c1d0441d0082e604000050780070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 57974922 1250 57973672 57973681
    0x30010212040b0f1f33050705010c0507022d041506020708070f06110f030d0c1b1707020a080706050712030e0303010311060712050c1006050906010804020a0308030a0203 74
    0x11441d4180c100c04080e1805001e00c0e1002d080a110501c44d00c40d20301d170350602c0d03503080301c0c40740c007034100301303014010a4052a0340389000040140c0107410200c0c081d40e0661078450919091030246040390401e9400904048803080004141d00742c1d009292808246240c0c40340041030380e52120b0058034034402c2207042e00040b490800c500249040c283d58031261069000e0401003142d10b1070903103442e003551220701c0c02c00383c00b82c50650194600310f19100142428400020000c04014081e401581460303440d55036a0065800c10014580c40307088100040c0c010303030300e4086448030f81c4ca030000280180d92014160b2a002039541d0009030514005500030004201c0009d440c3c40ac2060f111a9203500c89400c0c1800c02038964134000580c0c0d070f404140401010f42c8410404070034190340d007034140c5e1007c0d0b034040710000b201100c09900405a8001e2000018180702c0c00d03150350040740c0e46000700d2043e81c8014003c0031a80d5599801142c03e028060300980c3c01095030900400454591700045210740707000c0310003580d01e041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 57976172 1250 57974922 57974941
    0x20d0f0e01020405031203060901050d030c0c030c060807030905120a0e060c0304060f2d050408061303030b010309020d020405060a05060304110906120d1202090616050c30010212040b 80
    0x41c2c1b80400555401001080003580d0b91000702419910b090314810030348045441c0503103803c10f0355503028007074200611001003000000c3d440344042e01c0d1a40e55401440d21481026020b807041290000c045400c80d07034613101243c0035040034041850750740c54140f1000c150380000c500a90302c02010304600e0b40000400f40003581e0803007414000102c50f450140702c080d0700c41140e0b07800440755003402c0115001800c118134a15110b403042c0d4010308001e4068400e10300304850310720502d100040e401c03000320f805d10781181c0196000c2e02c1036600580e0041c000c440c2045066080000520000b0030096004807680c0021032030343c4886024601c5907118412200300c03010035208105070014000d010f64410003408148041100012030720b809040c10303600f00904000240340c1b02d1302c0a4010207003050b8001402107025001c07481e244a64400c040d0203002900d0300d0328501001d00140c0c41200c80c0608445006c180c0811825042c3e0b031701c1000c2c074410200018100640030700642102c1e502641d00342c2d0003190070428001c1320361 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 57977422 1250 57976172 57976183
    0x120f0f2a0e0f0c090418111804030e18090f0607180506160c08030a08010f0b09010813020301050c0d060902040509060607050304090507200a0209070c1b03061e060302060d020d0f0e0102040503 84
    0xf40c040300d107458862002c4903401740c42c0100409c0102080b040c00b5603154580c90341e40c0800e080d1510317210300708800c1c6086600565110004451003000b4030a8002040040303002e940d801240078041c03100148094142814050150312840d0b190710017401000c1180003103030800c0c003420007074a50341c406103a6503500304000802d0041c040c0c101c014020030b003030030420091200b030048444964081c00c0500c89035443c030300d50402c0342700d201501035059400d220411076003007a048028800da00e00382c0e00810400b511503c00508a01442c001c0c4c50304002800041811441c2003406480800c0c4110100c070715194556070080309581e010b80e290b401040b43c2400c2c1100340c03290504601d02d0503550724020544059140c00042006030040c2010080c0300b02c0c0e0b0482000c0c8007041c019081113803070303240f0800d6000d5680d103001c05c010002480104034050481625403203182071360140c0e2044a0f001801e490a08403c43c070b0040081d03000e000601c5000b9640c1050381c48010240c0107034111408491300043c1c1b81c1746800103150412 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 57978672 1250 57977422 57977453
    0x170304080d09060801061b0c0f150302181c061406100509010f03021e07080702010e090915180a0c09050a021201120f0f2a0e0f0c090418 60
    0x30003825001c1c0f11040c0d0002c845030444009151407080c4903885843c007198030744095005810141040008039480d00c4405042d0116410f00e138420420f8084284101d00700d00030745940201e000c2611802131000c0c40e10102000321030004509030081812159111411034034803040282c5001a9081040490b20304150326246540190900620388604070340001d003514480140a02131550100f0b00036451804103504049101100180071b540e00868280780100e5080b01400303c3c0024400c1c0008034240c00c02008d598000c440c0d00300205842d00d0700803948200544002e14405d010786805a0b0351740b0440b400c0082203c5503008003d00706078941401c40410599000801500196004100c22440c0c5a0001c8003a070444181031101d0408062502e48070004003003004c800303041055040190710610a0500c05801d4640f03070101b10a040141e1420322a02000749440340d0322031407000702d0004042210306089198030030280c0054070f00e800701040010342107030a0410740400301d404105a010130000c1039011560807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 57979922 1250 57978672 57978677
    0x3050604110405010e06040903050c0a050a23070b03042d05060f0105030c0d050304050d0804170d0c0807060924060e010305071703040b1c0f11030105040e0304170304080d 75
    0x100c0d81400e041c42483c900281102e0701562380e070501002814071880580e4101c0000c0030544200813441c1c140703140d4454a2480c242c416040041d40c0e00c0c080e40200e45151408920a006086060f1a01300130350f955400080054071508400c08111882e182c511410b403001ea90368003203d881c10361184c00c056207000c500824140341031088100600490398005010031081900b00c40700f00c08e4009a143c050300f1030189030b00403604454240b44d107a0030003c0c2e030b0029005079140c602c0c034140d400c44917500c44c1d0369641607404030002042041010401096960004007291406584081005443c03a65500988000c1200c0c01c8006914400d42e40840141ca008840081240721501b2890354107588400e5110080d43c400c65202c8003480c0c8076200550001d07c15039008100f03101c52140c80d00c1201143c00301d0380c24404025207040d4500f8080409008991041440b068640090a81917a0030001403000402a4901903001c40c071061100145140e2510500c0789010f018071b0203035494a160400380c1d0325292000411105 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 57981172 1250 57979922 57979931
    0x60e09061602062212020102030105010f050304020114160c080303070909090503090405071e03020a080112031403070201061a09180103150209150705010e070906031a06120304030506041104 83
    0x70154001040c2d50404589080c1180c030000f801c5413040c0c0040c2101004148030012006001c40d10380650144d0304a603001c0e240c12511b82d144080458440c0300880d0000c0c04181880381450150000001514000050081c1d400720851039460740041c034401d66029240580c0000100402c141e401000e000c010442c0c6c0c5010701c03000607159070b4141c07640107030200103003e9641d03080083e510520901c4000b0740342d10009060700c00221751f004020060340c000221b40d001b04500c0400080c1c0d0b6403602514410240d01961402481040c114841081341c3c8060031070700456480700b03c080345c60741840761050000440a48915a00c1602c5400d010820303069500b110300c50310310b040041022030030804d1551348484840d080107030384056490000b2094030325810020407050010500d481003140550245030b0410003030041b103651960792894241940e019000017044c280a00444c1085c00080700542d98000000030a00b14542d00403464880c51500190b005642980c0301c40e0600c82881000e00c188810070200351810300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 57982422 1250 57981172 57981211
    0x4060f1406310801050c0c030304030c03031506080609060904050a080c011b03020c010e0c1005030606090d0b22020907080402120f01020406090b1207050f090301060e0906 75
    0x80c202004210081e016600025040c0c0600101d01400940c0060550702c048a810440b000c442080d401401840070540c600f801050355101e00d6000d43e8152041000154507507a265607040310094003082d8100e05141d256010300c070017001c00a00500c041c00141c2e403400210718010003000b13101600074090600880012081c040400c40218101c4e064a80010910750b031200b09400307035401441102d5600d0812074920004140c0c2d1503241e001000480c01d448028041080040030840c2c94004480f0165032000c80c9460744242c42d80910083c6d83d11040007880b00d82003a8403200403900704c600e902c100304c6540303a401c01041400110300e000301c02c1e5680d03000b482002081403580401c0c1d5280700580b19506010f074540004e81195619401140300d11416030580d00c07100c8000562078040d40140c028540400c00c14100400c0400c28001604d409090207507004c9050703103410b10706a5086c1d1080d20f80143c3e42204100d0b80031a51000d006034002443c13100c04c1d02145148c0720441a04000c8090111510300d401805040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 57983672 1250 57982422 57982439
    0x12050304050d050c1c02180c0922090f03090602060c041211100503060a0e0c1801050706020414090c0c0a1707060e06090c010c03020303070e0109030203061504060f 72
    0x40d81603900981d001081e001d05414118036140c641920325500c683d07203e8105040814104070041d10900c280d9241902071003c20a4000500080b22207200543c014090740d02e07180361083c410000f1003060964801d40e69a0781d1a84416102c4104040e03e654010f100300c4c8003003507400080c00005110700c2c40070f050541800010104580310f18400c8140c18001030501f00140800519060781441c002800d604681c10500400383c800d4200304e80c150f100714610f410004411036050345262060006c0103100380f41181d503250584054002044090410400b03005441c00074207113100402c041c00061204643c1d0030003050401c00c5c0260024402c407840c0c0b100380a1880b051341c001440c40201c2e540701001418150b0114101007080c0078814010300710900700140070b40c140a022135414090f000d41e1040c0d030364104203807005541c03586502c040280140d204200050b5801d1103048811003da40c1403400b811950307906d0b000a49480c5003a1058071ba004201d0300071181e68a02481801c1c0204860f1b80705600d410b1406684 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 57984922 1250 57983672 57983677
    0x10b0a0c06020903010f05060909010608120c0c030a0609061a010c0f0206130e060f060901020a03030b0612090102090a090b060d09080903061e0c0306211f0f06120503 73
    0x850500955141030000c00c021038054449102001c0d00800100b0200424440900b00a50350940100d40480105010300818020302040e00c00032801084c0c175503000c2541442c2a8400102c0c52a14080c0440e00b582c4c40c0d07030510600300b8482c051039001c2400029420f024003103910344480c03d182007031207034200001790b6000f61b80c403a400d54116100c2847d603849800402d50a20030404a007a00041d05030001c280c282112111602840054815807802100300c02070100e0b51107011040d030b02503801051800006482038101010070040074000d141081c001d21142d002c00c010580c0c2003016070350046103012040c2090842e18008190420782882441b800700089031803840b5040b4105000d40e196041070060200440c100d80c45480c02078200d405a14148da4072201c01070130f80f545c245020b4100070102d100b881148003503e0041c84000c02a80c641c0503481d00300300b0754420800c0450600d005408500e042c8007607043e0b4003030451221103030200744887d44425404c2202c0582d0003201c00c4000e00c12000f808504c00009 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 57986172 1250 57984922 57984937
    0x1804020409170309030a020c0a0b03010509040312020f040816180e010b030307030903030f050304080d020901020c031b010905040e10091401050705040302120f1b04020702030f0f15010b 81
    0x80005000245041500351044242d0404100320400410721509a4000005000e20f40b459401d650100d0200c034104954240785200310b42c1000c80602c014482c40c60a0310f41290014071a041001011407a00480c105a0300702854041e4880800306007001900c206110b0710071011303030301d40000c1152401e1400e02640040100c4000404960f10300d030300740b84082c095000300c1e030b01c10008080325200d031524a0000c0040b1401e00080340001c0103c1900052a402442507a0245032321405190629025040a900a410000505045104030f000b031845c592800e200103503c41080c1d040c1d06000c0070b60000090f110200552003980103900c0d00c80021800c101c04140c10224079400c400200c0d001e0080d08141d0003400d552106d1620302d5180405022002d078201d001401164803d0726a0101c0f21003092070144c4603242d070f020300460b54101100d103001d8030035400304105a0440c0100014103040c01078001c00e18204103c10508203640c0f14007410420541c0070880700c2c60940315210103039119818141d0f51a120302450f003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 57987422 1250 57986172 57986179
    0x509100e0106181506021908130302060d15060203161101090f240c0230030403080d05100510080901090602030a0f0608010501080307080d0b090f04030e180402 70
    0x244140c0209000b07401180007810403c008110800d0901590302c01000c850255105410303508800084490012810040908241100c4801002d440e01c0c2c506080d03010903c600c581003607106010006903186030207080207404801c000188002c01c00d00e0040462016001039041d03502c00d0114000003800510031402032075100180310400d018000050310210026040200241c423010b0012600001b0307104586104200c80c0d03681600a20400e20680d5141101c10300a50001c0841200c111180c020070300030300340c070104040501980c03011400101e040d80c00c04d4104880030b18000916980c0240303030303025017a00005030303d01d0440203e00cac042c0000d220918204040060110290005920342800e40c0907100c2581c2040301595289800b500d010000c00661040301000e500d48031010948010501ca41c6061340c48c207a004601d015000d488010003500400340010a580d180c0348051103544070440e445001c2e0520710760280050405140241915141d84a441c0c05045200c1807a0030000d000d0120980050301503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 57988672 1250 57987422 57987431
    0x30606062a0a2108010b07150c02070803040b0703180b070308040f15060303122f070204020d06030308011202060415020a1b0f0807181d070603091104050910 69
    0x11920541010702c0c08001408580c0c0d400700c40d500c0340032500216050114030b50359043c6142e07202e40001c0201c0c000d291000d8180d081c0d21030440c1412070345601c0a4804400b90040300c11540e51040c060f881d542c0281c000021181010404d10105600700038031088100903c040101040d0400208041901a0006c050308000203d0081340038410078851074180b013500042054254441c2c41050310203420644800c0300007516900c0034000360511407103151445000c0c08072107100c1e5501031b000381c2940596900e520b440300c00e0402950f00180d80380d10041c04c00807150400403500600c1c40c18090103411059001400001480b010180165101c400715029114903145012401c00c0d5620202d01d40040c004000707003240601c2c1082855030810341c006604880014202c030080d5615013008a8860f415445024400c000c0121100c12648454015003641105502d41c1078140c0e241300d42d16881c00c0c00d646d02000101c3d595000000500811200712013101200351002d1000c1e0401c4104146d603008a942c440f0121541c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 57989922 1250 57988672 57988747
    0x20c030d020f041e060f0c020a030605060a080a12111203040f0c03020907090302090a0e0703080a140d05040201020111090108040f140106030602190e1003050a06170c03060606 77
    0x210b41903401030080010041402d00208181c0790f0314030181e0080744d0120b0601074158041500c40c0b11584911540a89000341b190f285541e210080d040c040c2895501c025000c5c00418030b0041001600700c01c46c0501d90568001510680162051001086c034008907040010031500101101d000c894110340e01c00c0189000d11840e040003801d0340d03282c0e0002584881e0540034803040541c0030040d0b105480c0201c503500803d49412012004031500000625441e0300019030402c0490b0710700d406041654054240101c89062801415965074400341d10311680c03031b58600520082d175074240f02c0d045400100c00e03c550b00d0b11200e40d0001c4c10b102801000100956502c448902c10001c1e800350310000260711200a01802e61607240100194101000c600720a0070b2404030007680c4c42c416580480f41c0000604800d0012499007012006420001c100c00b00250303c807200050b4007032803640e605079080020005084452802000c140c1001c001801d81c9220300e20a1200c5400885000070900e011081c00443e8180000c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 57991172 1250 57989922 57989947
    0x1e120b060301110c0a0c0603020313141e070e100b1c090501020a0518090f06090703060509010f06030c030501080706030f0e0102031003050709020a02100b19081e01020c030d02 77
    0x440802810740c507004c2800c00520000040c007a42c0305108a41821175280c603444110f04030f00080790700401c81c01d08441c809021500ca100c00c10b00010703142c0e0588003072041c0c0b00940b07407046130441c40001440d80315002c100a404e824480c1180c01c01407080380361803801d01c0c02c00c140b940c0703000e108801c102d9440c504441421500007030b803280c1040e41d4803400942d243c14030f954000d451a0401c187d00c0e110b4606a001e1848186048410548150012a80d682e01600d4075021320440000060490050650302c60000c038003561444016402810a00902000c041c00c2040c001c0c1501d900381c04c0e0700241400d0400603c0b07002c501180301010303603030310b071400059101c0141429009019480c100102e554400130070f00c11011800d010b00010340b800368040301c8150b82e480303a11f0300032407240765101401a0055920199074404a07000f0a0804800a214a0b0760029000921a1000d820307400600c0c0c5030300403d203001a03800541c0c140310218403904c0085041c20060206c03240c40340302d2500b144807140c0d800200c0802280 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 57992422 1250 57991172 57991181
    0xe010806060910050408250603090f0501020f0403030e030606010e10030f0f050a142208040e070309021207030f0b0426070b1605120702120c03041e120b060301 70
    0x1c0202004200020b040c3d01600710b600c24000c03589240562007000b900401505c086901818950104142e018a809070403001000780f8042100c002e8550711390100418004d00150100405820449030344516524002c8c040c0c0745680303009402074100c041003101503030300000d08a000d420250b070741c2d4500e148421812801000c20011403e0003a01d8003007544d0b0308000941c08113226030a240005c200c01503010181070784001c800c440201400f001072080e440d03400584695244c401d40b040001c9410551100c0f54642860800c80300343e40001c2da218038043c258a840f04204c800a009140604501811600c8a8003124454580a055400c0050218080001043c00d007000c012450b142e19079080341c1c03000540800d07402480e00343c1d003800c68013020404d400440c420940914642d91151440c044c13030030311810041040103001d042940200d51101d030540c110382d001003928440f48800f640d0b9a5007020040c00188100100355a403170000b0050034450040b60080c13201c052500440d2021070f0350b80d260000b90152 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 57993672 1250 57992422 57992437
    0x2090612101a09011a041202010903080c0102130b131a1912050703150302040b0409050111040f151709010605190602010f0e03040b0a1b120207150e01080606 69
    0x8519190000b007556980d004181c4122508032043c190703a0340c5c2e0760b0240d4058001707002e250040030b204000c1001002c4200c010002180e1041c14448400c9940340c030307070320710a0300700a803000f4580c0d40000d0000c0703004828032441c102401e401e24110b8108100b00380107520f25100343c05400a5450f048510b00c0f00c0d030b42c42c5810b40300003201c0d9004c03032040003020b190300030320040303841c0c0d5040c00007030034540400c085034080e01424001107650103c40c40446e242d5020440a01140214a50065907030105480032950030700a040c2e019502d6802c45a64615146e05a100b060b902d0b8820b0a000090225480d041a809038503015010b401120700c24403616424112801016a0b81c0031640c0f011184001e49146021402660202e888130b400800c03000300c4820954044e103008080034a90b64108202c2440110104400f41007403450614010b11108503082188814030640d01e02602c440b0611422110030076410406000580000703c081141c2c2c5960310750103800071160800c824140b04040300040c4e055101c15050300ea86 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 57994922 1250 57993672 57993703
    0x20d06080604050124050d020f0d0c0902030114060903120903030c0105090610060305100303080702010b060f0904050615070204050604141501020708070e0109050705040503070602030909010608010302090612 91
    0x541003614000d402403080c1200d40c01c46040d0081c010244954170180719041740c101404980d04020710b40e08102469a244000301d038441d140c80b490b003002c90306500780c44000d071100440050356541802e4010207a045076039138843c4032b11810400560345840111b581520030560031156900e6007140d038006400d5014110120140d50300e400200904e10b00000f600390f00030a0040d1000401c4c9071192000c406a41c022180740c00e41983c58803003000003074860b2080907440546480000350f107401803070000e8a50352040482c0e82c01041e020401d07a98500e45803203691f41107103023290f0000b07540f4002480302504bc05044800f0b40f0546c1e542c0005000f5840b140c100d440d5003031710380d400180c080c80c3c10341000c4100d000c540080c40c01446110350118080324009090700c00d503400c4c00365945940e8039102d91803019000060000080240900000445403000c2109002600c07a54028545400c101d5040c4240128140c5c00b81c010444031030010400b40e04c500d2079098100805131584481c100d03d40e1041c51415840f600d40540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 57996172 1250 57994922 57994933
    0x40905090c030a06290105070b0402033c06070f03020a0c0c030308040b09120f03060d080a02031c0603120309050a020a1502011112060108091203010303050309010c031b03020d0608 79
    0x401440350712443c40d40040e1906061410210f81841002005c49144075021070320400459010070081400719610038402030444031000310940480145a46aa0030b0546031014103413480c0c10b0346090f51801903c0d02c000001007a15180c950707001084030303016000c554241580010b254103040d01c40e030454041150007585980400d5620301d8001d0010030100c4041e50340080d4240400c0c03140c01c010507100003041d081d01d5010b0400d20202880728a075403010f4105a03100c0d400b0141c0b200040d04100c080c003840282a0003850301c5100c0341119003001030842c0c40040c0c41c00e00d03000090001908000000f0781d400024540003840341206c1c0752141c6811103480c2d010f035025980503000210401c00c9105030203ca00507a0083c02222414000e00443e40580749103c051000300100149165104460703003a40480311030101c41d10500180305054840c0c0c801e0f0020b5000510010030440c170800c0c2405120b036010000d2800300700030705140c40c0c1c81c40c084201d4900c1d9001c05400291030111449150040806040c84006036038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 57997422 1250 57996172 57996193
    0x414031c050a2a0515011404110c070311130504030f050706020c06190c0c0b13030c0b040507030c05010519050a0309020a090c020d0512070f0309141501150203040905090c03 76
    0x7061150381c1c0100c41301c0c41803944490b0f094003e0003d4504a138455480d210150a1490030017002d444003260b0050700030410b010151005074104802c40086001c1d0350780d1071204c01501c1c103004281314400b081c0d14410303040a0901c00069401000041c02011034a0001d459a00a180c208083c0c402c480c00b01201d441400188214031a0012012180f0400301c1e41c200441c0b49241030a81d0f103d0b81010005d4140c1003820001401d90a0f114100b51009100c0d1030102d10700e268690796031824940a54060701d40b6801a0b4041c0304100c0350108010190000342000da00b8110540c0c0b81d400501604d03c400810420701090b42100035000350041c5442c01e034001d1040c0d003110f85a682c0000200b604007500401845454502500c15014808070f0348070048588428007640d48943c42594010780c00c1d406a800c25a80b40c0340d65002c01c1510f20780d0450380c4801c0004d400342c13065502407542c0001041e0403680e40100c5072101750945603000401c58084942c400008241995803101150078111045540c541502501041c2c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 57998672 1250 57997422 57997487
    0x10150206010f0f060818030403051504020f0915120c060c0102120c03070c031116080d14160221010915050702031606050a09050d050414031c050a 64
    0xe6041c0c41000284041041d03031904010b1050210748195000301c0d00760004165105036280718040c400900d90203c2c0d02c2d182e600c0da1650303d003041c0310011900c96620f03607043c8011880c01e540d07a80000d040403030b0415000e0030442d00c001081036410600d24800d0301125074a08041c84180034580103c0c8000341030f1912480049c0c41c49020798080f600c006603d003d100001165401071200307481c0108550381c0ca0a09a0f00c50740e030250f5604048140c1040c2920a11966513600c01c9000c440c000a0300c11f03140900640300e03490002808143e07020800c50000c010034003405291a4240f210640401d070115841001d03500049402850845032194081c030725401c091401050100c40540b040d00303c007a0100030401551400c80c00c90720307401182441500301005150342c00c0030410a402c0981c00402c007031000640d5072146d5484610700301a001308c1c50045940494100800720b0608440301106009070058140704c800c0a40d12610550050200002d00c4004a05080108d200390b040c0c0000b400d03e044000c51500700d642e50b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 57999922 1250 57998672 57998683
    0x11b090909051f09020901080a0b0f1503060406020705010b03061504020901050405090702010b0102070e06030d0f050d0606030605040b061602060c0a12020a0b1f0905090c0d06050106080c0c030406030203101502 92
    0x40c6c0c0581803000000400c07130030000d1807048031900310340c1c201c1c07e588440348000d454040281c8003004003000146905083c0d6414010b40d030186108020069440d80d451401034203640312002914440c1c2c0000e810000c07401c00c1c486c01034001031000c503001030340c81c1208001a41d5600694005d550402109010081e03281d40550000d2643c407026000c80e03844c02d9480040d400e4020080f500e00340c05410003134a01300800e0080c0f880c001090703410700303201d41082021003540703044490550040001a84804041250341031511820002c2c44058031082d14004421700384558803590f80c44003d01a0340005040310142c6c100b0701c90000e41c594440310300e1006246650000f9a60951544103852882814002c1039144403620142c1000000c440c02c1c00c03440c070345041101030007028020110300060194014040280e684c0b0f200e0000c00d94492100000c4a5040035402841d5a60090200074981e2080000c80d410582c00815142100d400f440c016941b9921480003007001c06c0168014629454011040c0c6130306a00483e6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 58001172 1250 57999922 57999941
    0x1090504020a230d0e0a12182c010b210402030c130501090b010f023a02060a0e010b06070b062706030c06090d080304020414011205011b090909051f 65
    0x8040c0840385505e00c8103031711040b4614005000d50b001c0824100c40350300401d800403500c10200c40040d40c0558440001d02d111000000e0300096021200d1401c1c503420f0180030301400f404901103454200411500c0e40f03008012a0070404508180100c001411580c00300034621001c5405440c44880300300424001c030140c1001c0c0205402c1d14140000a800343d48644103070b408440c01d580c010103c0d450b541c01480c0c0040120000c03034a400700100340601c0c4103a203d0782d2080006c003a6500407d0a8900602050704030ba130705421010341a410700340f50240c2c9548000c00d032800746e9001450f09002e43c03668000500c01c181c01e00c0b2400c491009910030400030b031001034131640c41508150305580ba144584020054a0b04c00d01440c240d2080c4802503000c04580c102000e1a44144090400075900c02c880d031407504541000d070b03c8244481ca1400f41007040100078060702032002500c0466840c0c2102100014010384400d000300c4c040a07a6604808083c820100071b40c00040c446448206440d03031404406401800c401701 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 58002422 1250 58001172 58001197
    0x50a031d01080a1802040e03121302030d05030702100c08010602150408031902090315010812040303080105060306030c090408031e100312200a03030608010b01090504020a23 76
    0x880005a60180d500306098040d0140c0d40d1070519503078038141c07000400c80c2e50101d990079691038a0080041e1180e00c10180903044160007075464020603064904080300081103031440506c3e405580e801610001340759030044000e81880c0792a40c0e03400ca4103c0c540444080075080301e84c2880f07010802c00d80c2005003d810b84840e03070b00ba00c0340d00411040b03000780807405031001000309008200207260724405014200030386d03542e88005850800d007500000d1400e8816814600da00b04000700410110208000300fa592060b55024541400d2864501420741d1005108a0303008081c004002482590300344003501044170300412020103820f01d4200009550800c4640815615081a1100403010f04083c030718818a00c08019040050640d0b64904568050008003010f11400c2640018010303241d0f16103402e0b084401f0014405589a400c0040a5030501d50280729030340d251682c04909a6400ba10181c155002510056502e4480140407038101c0d210500c0301e00b5217400001c20a0701843e50000405039240c111 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 58003672 1250 58002422 58002437
    0x170720040203090d0e01090f0e070207170307020d080403061505100201061220060a03050405060c030106020a0201080601050d0e0c13140a0e010603020409030f080f01150503040c0909050a03 83
    0x120921089100581d50f1a0240d40080001d0038601e104007401c81005e0018580401e04036910321a515010509802c500c08841402c1c0c00c104440e80c5c10404a00206101c0c41e05001641791040710940720b01c10300d0710290249012258072410b107c0c00d00e0485006651115080040449248070195100418083d440c400d40c1400c01c03201550b44140110015600c070041b991094454a5031114000100501c4031000c91824800010065032040040c000340b07031058401007503a10b020300d080350401c54010b0079540c0b0b000701031005128079035001901e02c034000d41c2070038820460b403600401a550ba0045551400c03500e4141008050303054404a5596900d820680d40c002400d2402c2c10101c083c1c0c0c0f1521260401141d00381300280b4030340c4080d04041c00d00c10800000155a40d02c80e0080b038155000d059080d4080744240d080b003192658010801540540c1c0ca501200f2654106040c00c0544280c000e00101000b1002c4003040a005529031328038014100102c0800440b5400d2030516103450303030000c0940120310306 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 58004922 1250 58003672 58003733
    0x302090f10060206060a180e01090503030910060e06121e1b040c080609040c0e040b01032f0d0510051f060305070e0d05030d0c03050114010504050603060108041707 72
    0xd40e0741d00601000305690086d9040842101590b04400da420802d552181c81001c1c1d0700c1c00c203103c0c5084084c054006156280303401c2404d5440c1c817042c0e030300f14103505140140402074600d14040450300100121354980c5006c9601a91628042045800a240d002115201e44003050000b8074000c0a030304402c0c2039401c4802007401c200807100ca296084001c01c1c443c500080c0c00f4641801481c1e4410301c01e46400c0703170140c2c4410748460840d8084a048800c80b8a01c5c0040c01407110f841403080340120107503581040002c1316403c00409071840c1c55101c8c00b41422000d80c404018060081d800c0350040d50702c0c10450b515056800c0c820481240d00700c0c0d044407400f03103804641d25102e801082e101d640280c5441210a140000f40598070102c1c101c256850b002c04d20181c84013054901030f17066410700c82d94000c0349650400c40c00341300281c5210b002e02d0600c08100410446038035000c2c02d5a52001e424280842e50b44e56a04008041810400510561240005005040005000031110440000080c07082485030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 58006172 1250 58004922 58004927
    0x18010c02040f020307090501110703020909031612030f090f02091504090605010e06030d080705090a08030307080709080a0b150d0c0308070b060406121b050301020c07080d0f090b0706060302090f1006 87
    0xb0a1041d44040d02b11603003e03c0507080201403142c21140d510112840c000500b03008210440e2001c904403100b0010302010387c60f4940c1030252548103440720b00c040110010b90b5503902c50483d4007034402400703802907900290450071303140b000800001c0b01074028040501180b91a20040c5024043c0d500440c50070008140d00e41400240c40c84610607a803100103980d120100c0035030b9290004003070aa4000e04c081c80106118500740091405050107444d0300c090b5042030480609a14599040340310181c0c807061039900030960100c0c0311038010850b581007007403281c0c0c494003140b046000c40c2d2015080e400788000020410103d40020000d45001c0c041c40000c5032039500c10442035449038881d207065520117102c0700c4080f51908010700300314507261400c8149079a0320808203080e41c00c034000d0000260041c0004014a01e01401b014462031460314001da901d01402101a203002c00c0d0740107200c03600d800460480100200d59229034003464000b0140d025902e0080f0329003c4507802160114082c111103140001d8250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 58007422 1250 58006172 58006187
    0x3090418260d05040809100e0a0602030c03180301020903061906080105040206040501030b01020c0406060e030609010e120c010f02030a2903100c030908030a020a020f0c010518010c02040f020307090501 88
    0x1070400c000c861030100303040003803400b038200a4415920390404004120843c0d9940080a080c0900c3e1346070491f100500c03108101c40b40c0709640c81070080d074204200350300c11001c0200485a1901c3c602c2e144905515064020034021300504401c150507104540070b00c49204000c120240d101f030785221040c045151940116400c0c5c07030b025280213401075018803060000e90300a4005140089044c8115951074090300300040c1a00c2c0b40764070810100d104a13070350040c0f900b011f02c03007517902c600480000d005000700207660741c1d82e640702191042100300700401d0070040394070300790000100445074000941d140e081c2959082e000741100303004140300b034000025400708040c5140c1c541402d40c90003000b400c1e0310f100c4110100060120f4000d6001019079924681002500b5400610f0050715048c00046c0c5620446101902c0d002c0036460060561744234291030080740e030f0f2007400c64210b600c0d8a000000700600c400016a610207410b1002584a4200b0b656100035907200e0f030245d03204400d1507913190401c4d961007006450b0b03034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 58008672 1250 58007422 58007483
    0x6090203011502010218090a09021005030601030e0304050d080319020309070f050102011a0103020d0204081b0102010606021b10030b0d060f0b01030b01090510020a080c0601030b010509060907030e03090418 90
    0x110340c0307038089446d17904c3d00d8448954441c001e03220101c0d12080540c0000ca044450b0410040490004000d0001039649440748070b1207008110015460982480300080001080c41d0703006007440800400212400403428a8081c0c5c00c00c080c1041d910390501d4100c0548400090185002c0306200300d0000601c0d41c414040c1c082400420043d100b86000100c0045000e94010008500100e13020080014000020880c85040c0c007644401007102160b540002801d440895000c0c00442d8418060441c000f146045000c2d040a0100e44907064100244810b8000d4000c2d940300a6101e0440c0c4156000d020450f00082446550403c00f042020340b604015006c940300380b641580050590131003403000b410060031a4281c206980100c0e03a0713210150341d07052000c1d884801d0b181d0380b0b608040300400402488880003405400102c030310b0203441ca0108046500c480005010f14109600c0d4075510b0f03504038051040711047d000191017804200c2d003016080304d8103c842c041c04c5864000012000c0e030041800f01251105 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 58009922 1250 58008672 58008697
    0x40c030506100b0d0f021303060b04050603010507140319061403012a05130506030408040e010f0315020a0311040b070b0f04020a0e1902031008060a090804090903020c04060902030115020102 83
    0x43c40c20b2102a480109205c180280c00d15600300401011000c1c0d00d20141c0085108003c0403aa110503c400e20050b29400b50466000380e0400041c088115000301c00d40050701c13414020191640d40c3d00540320b4107181c070800817100e204c0c40c0c1a0081781d41c04505042da01c02c4101a402404160324900020aa00c07090b40ca56002d104815000681103030322402c0140350302e40d180032044441540340d0300001e1480d84103485c100c5600100050411412107512451801001f030104900581d80c5951695030b101800160180e80055000882e5a26240207500c0f1940f002aa11b101e0360300c6641302c00d11680181e0002d901540c445c6008400200c0285d075080710300303108585c00392481c1c41907450318440c5240e48201500c0300c42520904010505000001d1010b58445d01401d400404203030b02e0015224101100548255000c5040c0410040031424900880b800c030b500e041c1c1c000070901611b0500724103069458541d81d91007810244001110032064005e5810303a030a000900000303030000300701030307080703105002e01541e5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 58011172 1250 58009922 58009927
    0x9010b0a06020d110304080610150302180f040207050109140c030601080316030522030b07051810020102040819171603051c020d24030c0e041a040c030506100b 70
    0x184a0311030b140602408040c003041700c0c01d0a803160141401d021080701e1420603911414402c00c03200040501e4445c40c21014142145000d00c8880f103140f4000708111038030302410041240c000d09440700e904594134250040000c2080580520300384c25074014410094005116038400c1000301d15010038002e04850707500c00114500b500d004404000b0884104003038042c840c080c090040c1d50903581034520f00401c456185900c1082c118a0700201101d8081c15213020810280011074480840541032140f90400b01c0300b00c264150907000c01c80c0a4807840e000400a400342c004036406600b02c9401850480d07119405510844403000000d1a050241882040320012101051004640110f0081039400026403a1314820442541d03404140c0c0e0000f010002a41c1ea1040d03800394440c1c04594540c0c15101a012000c242d03840c648600c00c00d41003034080d43d40d84d00c400c0004101002001304c005801c420014100c800720740f4180c2404c21813480940710503035086c010b40700003c8a19258044000c2a9045104001d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 58012422 1250 58011172 58011193
    0x30e040e0615061c0c090e01030809180112020d060e1b0405090a020306040609020d0c081f020306060901081e010b040e0105030307020d0303090222020405041503020d030518100809010b0a0602 84
    0x244c0b61524981086c400c540201042042c400701c040760185000e403120644da10001c1d828010140b03003100100b529102820018400c0301d41940025040131780403500c0144580c01c2c1d04001c17008000c85662000ca5203c0c00100355403d0300b00005e40c4004035400c6a08002a40d10018201e440f484030300e0b0002d5058120100203000286968003c1d4001400130305044100e13813403a5034000006c51240c00030507103070303008107800307030001c28680d45000f0f40300d200c03aa0940c11400d190000c19100d008103600c0c14140698140002e001420071504c09460900d0301c0402078540d651440c052200b035000b801040c05c58180b800012501b41000811221099800380c14002600c900343c5084006101c000812030380049600d005041d00301c615881d40c034200d403070b07030800603a16885d000802c4120303a00080c4031000e1a40140341007015a80c3c1c600c180368059010b0400c0c9685d562208c215050013500340c1426a4004600400d044155512404151140c219071008008a4402004000c0d0441e407502c00c2c100143d000001740d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 58013672 1250 58012422 58012477
    0xc1403040b010501211107020310060f0b0705160611060c04030305030a09050f010f0f0b01080405070e0c040b130306060b070b0105060915070b042109060309030e040e061506 76
    0xc04004a046100c91905e840c9100351405441411500180f44d103000f0071560107502e02400307660b4915080d51010408949403030f80500002c106441581201e44010801105101040c8101070107001122418607140d07840d4180500403c0245c42c0d0390442d4890900040c06c1248c141c0100c80030790784c054495a0841d620803034400c0c06800700b180120740501071240c14280714442405004841e1012000220f000180704046004440003100b07031504200081092202081c0041030301410354120710004200c030380c0d800442050f9071240381c1c010111715100140790f00030055441108000d50748030342d4083c010650f80c1d215280e0346008146002c1c1000304a18010405840d01e00e000344510391025256002c1c661050800c000036800c4284281e40700c5100c0070401c020070048410741001003c04051030024120408402090500d050051000341aa01d82118042c18012580c0c4400b810008005001c1c541c20201d10a459500c1a281c0407801c02240050f2507192800b4010b40300e1210b003070356202c011803141c61041c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 58014922 1250 58013672 58013687
    0x204020d060302130603050c030a08180109030203120403050c0609100e030c06071506050102030a02060703200a0f03061502030904050406020708121605180f0310020a030c1403040b010501 82
    0x481003407a80e4080000040e10341610700324801020700c8001801c1c80ca1414864144942010520301c03039000160000006002081581c104441c01c8103c281c00310340000044c0c4c0c40c2412500040d5040c4148a0210303d120b0311080140196031044d070039954501710b1312060203101c0c015181c8169100d00a442c0c06400346200300e8480d8141d80e0300404403400650f08001046007540010415907054603500101045044a0f002d00801010b080c0b000b1440c10701c4404c0025159030300a0a00800c06890304039481d0030503001c2074124480303107a040c00c903543d4082451019002600750351010010a0500000052002c001c0c1051a04158650040c42c58410f1039001c210050000500031900b040d420300060b0007050340c0001030070b550101d9000e85d01c928185030034110407003011518410b0801008005c90301c0801c14641d80c15544510503036640c410204c0034000241000b415810541d0100e101068010030140d150308040500080d0b80c448000e0b00d03840000b014140c3c481154080c0c4440342c40700040216501c504027 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 58016172 1250 58014922 58014937
    0x7110a0c050103050915011701050f01050d170c01110306040c08011a0a03150b070b010e060d021519021b01081b131a030a0b04050906041e050a080415020706020a020402 74
    0xc1e06e00307070440001415080b00b13003a001481c40e040041a5600c0d20310003442080c6c0c02c603c0b0158100204e600d0500001d50388021810000c00ba50350900e005000c542c1e042054a000c0c85094000380110b64402032100b01507001110002d10079410201c501c23141c0c4e40207181c00382c10f88035000f03015044041c0030803820740954400740400701010b80c3c601c81c15001005500260014191819099503a2466410300c040e44400c1a000088241105000c0c043c6698441a08006043d0b0541e000c1901d00000081e0200d140a08465404440c142c581060b9019a0106822a001d280340080c3d40002c1c40000045030042c1c01102c070300912141102c0781d00c00d900a901c001c0c1500c1800f20158100c17040d01e0320203108040309001c0d140c004130072002c0140103504105006041c00500300f030310300304420302e4405811580c401000e0070252600c1162003030701607811052000c403210642c01104a5504ca08076240900d02030f4400e2140101000d100d05090090320300c080b030705000303e40d0300350300074045144942c007040001d520006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 58017422 1250 58016172 58016191
    0xb0f13030f081b031e0c13030201140f03090a0b1e0a0513050a03090e13030c020409020a0f0b0409050603070303090e191a0a06090605120a0f0608030307110a0c05010305 74
    0xe0f94040c80c250303220700940c400c90110801d1001c244a00800b44090f8001900120b461802030124402e55010f00030207004403070302481c00340e8203c1c4121181040340d1180d02d1004503055800020040c0c0710ba400514403205500c00c01003420941e4070100101140a410710f494611111080d011440800158001e15040100c03400107003403400040c0c2d0f07102e1800103812400c401051100c58208020110003140940c4082016022000000e0a03540100940840348000388107582d103885a000b0340d1203030a484406081440203a0b041a525104030781801d402a2003180380c640e0507c80002c00c9403c01190943c1101d50544600040e2400c0000303441519000402c07a50742100203050384100f240c514041e2110301416200b14041e514604000d0008004040d0400c100f0b0014070b800c200300042d402401c80c1c04880d41101c3c40e2089807180e81d00640509090b13100701101c0c0707041450214040502000550280345a6210080c8120500c40816215181c159018150000e400020403855000381c00c6a40e0250185 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 58018672 1250 58017422 58017451
    0x301020909040f0b10060507080a120e070f051507031b080a0305070e090108030f0706110c0c1e0901140103020c1f230a1d0105040b0f13030f08 63
    0x8808118118002c403415148580c0e480c50020901c4159134070b690b000600e25074030b0003880c0d05003017003c0e02c14420418014810800080c400c03800030300c01d41c210486815194814400d0214002d076091f41e4542c280110040c2070b0715036000007840e00e00f2040d155041c000c03031419036051400e0b90324259101942d0b04822501141d580c4602c0001850141c02030440541c00d483c000f685007444180102510b40f403110440c080e0b4000700051007906800015612104007030340c10035079100303034a2410360060084c0500380c150950000c10408400600440c038494614010b5035480045141711103114051481e01e4203241c1c20101c2d030b0005010181444401d4028500181005803810f11510300c62441c0001c004400307050f100d00680b0ba914091030710b004011216a0b0940a684078510b10344040c82103030303000751040c55507607a601c911a5009641e04510a40c600c0880000c020500d040d041000c081c120031500e8000c1030356a0400154140c402c85441608a0b40658440c00c003081d0200c0c040e1615070000d010781e244003450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 58019922 1250 58018672 58018687
    0x50108070c0c03051f09020d12090b03011403010c1404090b040b0306070809060901060302090c07020102070b04080102030a0f0507020303130c0f06030e01150602030f0307120612110102030405011706030102 90
    0x4621802c402140305400510f10f8407001c4880d103404411204c2100c3d0345a0400c2051710259607482903001e035450704104600076900d2030708001c0d50144025407000e62238038804400040e000d50900d1290315820004c0e0020f21100700020001c45050010503c103010407141808148550310305a400741c4038090001e0700c00a920741c400c0c0c000030f2a0100c100c1e440c0c000140358504010780c9030300920085405c0008040244042c1d411a0700141111000a1201d800500089100030079a0320800070000244110350070310384e440740c890134914083d510480d400490300d0704007100042040c005206241c4910980d501450964a90017000030101501ca8410340e6540c400d00d80105a0b4450110b8190003031210b07407030000343c0b024040d14035070030355180d4201d5072200c3c003032248100f08458011003140e50048507100c185a49644464050f52407050100104080b1444c201010908514041c03806098500440c0e59196024011004a0381c030311030380c002e0320700050206140041c0b00d0f01c5c0d00c0542da0042c000400240c00c2c0b065 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 58021172 1250 58019922 58019933
    0xc03090a030620130e0a0f150611071d071205130201080c090a0e0a090c0314010e12090d020f0d0303050117030c0309010c020433060309020a050108070c 67
    0x1019007007566290b03500c04080c00f2100b01c000d00f8601c0000e414018034100764068401554004a5129802c079200da02c10000f416000161700c050581817100c10100004040b0540d4109034179440d00410001c504121254084440002102401c45000300951420300300d10100110340141e005e4171003800d002c0003480c00c03140200c250041d548658010b5801590070800c030b00005100e0342c000f40c81700200800411208183d83c50b03034400ca906840c08419611019103440383c40900808000360060030304401840c0c08820808040300d03da03400341c9440000c0c424170500390000c81d113441ca03400c09040c0b2080c08100d110f03194100b6005401030207000034a00880180340c14003040c1e8040031540f085001a580d0b00c018881a1140c1013100c0c0f01440541c0218100f01d480c1c0c2000395a841805c076200c0c10f1120020050045660740e40010805c0c2d01060b090f40b0f90f040712a0f203801c0782c1c4200081c5002030000c0204000c02c5452080c4541482103400030700c9203111618140054441520280c038410402400c0c4e00035002155 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 58022422 1250 58021172 58021189
    0x1005011407060504051c0e060d020304030908060c0403171206010f020109050106080a050d0f0801090504020d05030d0b030105180703080d06050a030c05030d140d0510080f010504020319020105030c0c0309 89
    0x10301030b05c06450b81e41c0b928036a03103030000c05c080316480620000d2810241e25072104001d80b4400d0501403001030f502d031164101655540d580e5400740301544030700c00030010040c00110252084a05c6410014501741031135450b101103019038100c2c901c401290700002402e40d0300c2354516000c224140e0000090025140d240d05094034000d4210550310392080c0c90341d000b000380400045d0100405071400044240700b662000b8250310040c4a455841034071080810150b5444542c0c40000741c2c3c1c007600710780c0e6070a02c58204001401041c01520312a510303000c0001c441060210302c40d2610030040010385172490a40d5a400700a0300994407901c5055070f114004951511000d400c0d40c00b031401549902d54107890841058540245c4000c00000c0101c1c400c20012600814020b8811103008000045842e41e948400c411180001d540050150b10945d4005105518194002401603009406a9440403810600d48003511503c400c02030010780100f0020f00000c0905000e4100c0d060707071205803480d01c0c200900044000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 58023672 1250 58022422 58022431
    0x60603061315091b02010905100b0105040e010e04022e080a0f0903270b03160e030d05130803160210030b0a060809010b010903050c040c0e0a0e16020610050114070605 73
    0x540d80c4d20908641040d4400b03200710f0302d9003148004c2c00340550b0343c1d407900c0d185d148200300100659160760388488644e001e6000c1d103019100181c200c0a06680d5100b1130a07100009446c280d010304134010140c00d1008142c2d03a03515806455100c00208100780403c1122005401018280740c00d565080036522901c0c00d000c0c68221500941c2c68103c1e0782c0c0405c071010780449228940310403101041404204401c841c0042d250700c10081a510580312400d0b2005983d0044280c0c142e07a030501a035014451303c0c3d600000a44003400b062002400c0030340c0c0f184071641d900d00c0354584244050300708480000c018a401e02401000b08400d00c0c0c007044035014000495440101ca4000d82c010900c010108032007030000f4824290b1100c02480c1500416255840e900d4030b50b800490400d02454440705607503944c9008016041b032040014080c0c816669488070150026001a10000e141c0d0614410622a03d84001850740c00b54210380c0300640300b149031800544903c1c20000402c2559101840024080b401920031075128 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 58024922 1250 58023672 58023689
    0x40303020c09090c0a1502010905011407020c0102010b030309060f0c010f0209010e0d030906140f0301080d08010e0c030f04021f0c020a060f02211e040302010e09060603061315 77
    0x100c07020740d08000038140002c1c43d0a0581d4004201020a0355981c5c45900c1240d410103c2c090304210f2040003203000d003109482c0a80598205500d201420f180e201c170040c440c200b540c0c20b5401d421103402c0120309a40017a104a64140d02c04c0c0038030803ea20741070004240d01d00800200300e1a0042d804d000d18256940c0ca4200d5140c2940854403171517a51f04420031170424242103907950030343d9060355400741550983e030203554100850120b03010440c1d400d2404448094120220080e01c80d80c4d107940040e91000005d0010740050600000010055240030403507024050b02000c1c682182e603840b0800c440100e00a2082c0e0b806021602c807954000001806003201c0364980d0f40785001070a00740103100e2a40390f20751000d0700700940c001e01808440c0d408101000700303940c24004641c0d503007424840c0d084035000303c3c07004880c20009503c684181e0305202004200b12803007a01d521004183ca001040000502203407115004101000050010710f0480e0002c0300043e00f200002078940b222003005002c40a81e60840b000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 58026172 1250 58024922 58024933
    0x9070e100305060f06040605032e080606040c0201050c0706090302120f0306040e0714040b12032b0b0607060504050a060203090304062706140c011e0e0f0303011208040b04030302 78
    0x440781040700b05135101420903036000786020b180a80082c40b510008004a0706080d4058036074412207440b0242c404850382e80804509070a072074810154503844140c824902c91031504013801ca03c1c0340103010303807442102014005410003010361118009049041012021800750169141d0542c0c40c0d24060309209440c0d140c2280c59240403018001112050014565107501454013000020307a030090141080c0f405a501244001d0418042880d07900c4501500c0200c0c04045440e842a49121640d1406614848103600ca070042d00c15220044821600b065074100d0410071104011811640003250482d100c0c0c82124481c0080b81c030780200f2a08141c0340c5074a150400602041410f50000d500310300700d023150b90b110034101441c0c0c00c10320004005205801c240407000c0c8220440050a8007a0740c450042c080c024000c0340340700e2007007074691803801241c0b0759030034500b03440308500c40b00000391711880358280c03401145980d02386911000640704e01c0004450711b02c81084041407401c0a68017130b0000390310a070000c01e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 58027422 1250 58026172 58026181
    0x30203011401020c130e010207120c021f02030901050a0519050c0c01020c0d02040506010903050d03330603020c0705030106150906080f0708040f0f0308150303040608010509070e100305 81
    0x2848450345002411076000011442d103070f0707403000a0005c4403d6400d00005c0c0519450640901a01504101401c00640c002000000c140c0114022400d1403003226107041c0880c6ca01610044540072810600043c0d100344100109540508010011107249041c020b043c04e52038500e00c19134aa00703011040004e5000304407010013040c20408200c40c84400d0003d00041d0010070b0124002008a850282c8203a80301d10100e40d540c1d00500c1550003841c0c000742a40d4843ea5101d80c00b901030aa02a1441160207094420240702068603040c1000000c1008266150324600f40c0704602a401408840c1d07454052840000340941d400d11480c00140014211030f42c00007140c0750b0140c40d89030f80398001000d2000c19000c0207881003501500c140c4c41410390401c0512070b1034034180909808041d00d0000c1000301d41c99103090915400814240c0320304083c0700446050842c2005040d1a405141b05100110310044011310480c54448025640303d40f2514204007801e807200001100303055513126540209540f2014070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 58028672 1250 58027422 58027439
    0x801090c0509010f0612090c0509010e19021801030f0e0a0b042001020304030303020f0405120309030c03030c0c04091b030804170a0f0206030a0b1002071409150105161203020301 78
    0x20b500502000c183c0b403c0359440d0800191034658032086140000d5951f050520400890040d000d0150102802803605e66031100105891440103550b4004413900c00071482c00d2035444e03402102c00c07200c200c00158003500301110065001c1d040101160031559102e045c00746400000300141482240144480406410035080c0081d011145440d50b20240128081c40c84160b40c00008484c00c40b41d040c940103a440381c0c080e905640c24040d035081664030600e0a1681141e03603100001500c6118800c909039000381c0659001c15607244244400850030790003045802d0700700c1c600f9030301424045000301300581601040d1030b0304100c3c2010f00d800032180075902207014009112050304074444440c1c444000e0555810580340c240034401250b01c020b104100000004040e440315030441281498050b2580c9a0701e5203069001c4d4030b8528a000d100000c00c01c03149105010318140d088980280b4009020f05e0200c540340c0300454180e404142c81c1c0304088144071030100051100311400c0c0620005a80060303c81d414162403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 58029922 1250 58028672 58028689
    0x313030909050f19110403030504050f010c02010909090303020705030a05040e070e06191b0501051f03021f020312070215060301090b0f1003080705010609050c040f0302090a060801090c05 82
    0xd900c0703500e01000c1250704000c10f402e142d000b9164a8400c8000b1030034002d140080d0104a11a16007404041340000805070010060f00a6030f4007207070800d0000d01d080004407550000704501030b00040000320b0404c903d140650116091900901c3c02615102403501ca071413565000040c0c2c040040d10000b0b0070800c0c076029040c04c03504110f80b440d021080340c03c00c0340000d000380102d044200c65004280c100c1441a4010510b452408a40c40080300400203c0e0500500038202100d036070300300b21702ca000701e00100201003041c007041d60381c000d0085254510f4200c4118021106040d40404e51104201c80040110840304451180415500030070b6500b940782c1d542825820081c005500907814940000001041c0800710395214148541d0036a982c1c0c0d80345c2c06962071b000030b540094040c0100083c442c06001040d0401c0081c0c0d81c8010081c05251507040004160340714034816250f0021401c2d005000524141d1a882e4200240350300101d1a00d031a00585030171104032120460301c120954a04010342d0400400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 58031172 1250 58029922 58029929
    0x411040801060b0703021b1c05070806090f0a0b060a05090f0603010f0903050904271a060d020a030b0406060506030703050402040b060306010e010c0f1b060909090809010503060a090203130309 84
    0xb030f182098016507000e5a51689201071510303403207211007810b5071500ca041210303140160300114035086807001e08220f9100c3d0b015000350049405000300194000c800050900b281c0707240e54000301450b0500352910902d000000e009a039001280410000d0b25540f071401c0f40b4040d101c1015118000d0034080d04050844058078034040440d4108a81d0902007600401a10b020b07901c162404520050009003a00546e20507512000024500820342010310040e00340c050051600d41580484644901c020800711640e80c2c20025400286005d003400029104500e9a40092042001180440c0c8640c0020780781d4008490041c0081d80d1002044151b10f01760192030f609100507604d4500e182010303c0002c20180c60071401a042c003414640c1081000b900c4c060a0708583d4202d40103480302265034100340e0011100784142d90010341c15130380c04502d096461150a0155030310089807803400e450380006603040e801c02001c07160720483ea00400211744501e800110f201d1166440c08440d01500307883c000d0980e104e03980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 58032422 1250 58031172 58031189
    0x706020106050d0807020a080105090c010e0a080a150204050a1202040b01030506060327010501150f050c07060c030509030a03050901180e0103060b06070c08031201080d08070e0f041104080106 84
    0x1204002c25190100702d00849904013155598604450000c00c0d00a880356202090a41c03a00e0100320b546600410b1b0038042410990790609105e011000f00235000712140592400c58221120840c0001c48070440e159142d128141d001d400c080c0e4800018401c03000e9940031001600d0480641c00852070310740300c4c007081400c0909040065040003804500c450000522801d05610741100883d00f041340f07007204c0c9100001c11002803050750b840e508078254120324007014070301150360401c030710345594014000c0d00e0004d2a00d100510f0f4241c940101124900002c440540c1403040400c1a0320740f949040c010122100e010791113071991001e84034001484104800a8040c0e003015040080c080040f00d44030060440340c03c160301203850f030321060001c0e0703640c41070f000010324003d0361141c00204d208001c409854007481c0360b0105452680c5c0d602c2ca1039250b03500085e035100022880c00008400074003550794418031b0398024007045882c044c10300224027160f0b10000b4040c60300e10045400c002418003402200003070175504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 58033672 1250 58032422 58032431
    0x40f080d021506030a06051801140c03222a0f060e040207080c060403020a05010f05070f081008010216020415030b01060e0f04060902030906060a150c0501021204031107060201 77
    0x360000d44078208446000c01051001010400e6a07504010551406811030307400c1015050480c82020446c507510803e0a555080641200440c06000e1800b44240b000320440b51640e503034020100030080980b0072000040ca55000340c1804141058900c882801031981410341910b43d05202c07180c42c440d03641c4116818400607105220b440c1e441045014038100950780584c5031300c01d51820a8060203980708001031481500d08020070b0650005100903503d000300000c008484607500120280c4008070f81100105032400d400d030740030911a488240c1d100001044d1109441d4440588a0aaa00000f034800100703050b900c00c0400d41c6402e01c980100b04502c0c3d441d001000c0d2840e500c0036070b415030522800c01401102e490081c402e850346082149003420041c82001441d444031400c4000f074005903101780461080d40c0000c1c040d82410458034003910107651001004c00d06010003210090701c400030440ba9075409021a00d00d002180c16110f0044e031094a07030116989441d040103191005540c800c00031a03061 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 58034922 1250 58033672 58033693
    0x180515060a0f06030b06040b0a0801140103020310050609010c052d0d020c09040503090a09050a0f0b06030c0c011b020a0209070806090402120115060525021c05071a040f08 75
    0x75000340c0480d9050300300400d0645c41000050003602980d4810250b01c940018079668903940306802906880303a074040500e40300a07010046040740002c8900e100c288508000c180b200d883e2117409001a2041403503c401a120203944940c10000e004484441105009034886505250040d088450529000013001c01c142c0c4003000030b580d0800400d040780520080c102040070b2090500440e80540d1000d00141c0240c3e03581c0b4451401850200e65041d4120716000e004184544540a240c0f030f5141c3c020240c1d070461b2621100e040d96a84160f418240b0f96581e44420240619401c0f2225404401d43d0050b0110100f1401403292485c00145001e040129480402c41d40e555500d90143e042074040e0f81d004c014050820550f40100803422140c0e0351072440c6c1c000010000d81c0040240000c03290718564001000c0402410b082101d0607000c029441506000ca111042d0040801295403c2c041e02c01c441a06648000250f00e0080600c0340510403080020140601030901041c1e8006000d074030018190707a41c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 58036172 1250 58034922 58034939
    0xd05120105040902120a050706090909020a031104020702030a0f020405061906050a031d060a060506070c2102060a03020706150302010c02040c0201060f090f0606080403080408030703180515060a 85
    0x505014107485190796103c040d0554441e0305c0c820010844401c219000d00c4498181503659050303030703c0703080002000b5910100b0011070f01e0081681031540540072464060642d0f94440312803400c0300e03a098219a00f4803007403025a13410498a07a0003402170001000c500d10030b00502050342c0c0700401c0d813800f80d480c64072039021183c42c0100d4107080782d5051400640f14034803518120081c041c03d800c2e182e8581015410b1400342800884c003140120001c200030410b00c2e40c0e50050018038000e100016243d2402182c04000341c140c0020802c1c0d440359034800c80c403240c614075400200d843d0041d42405000075404117009040000a1082201c12018540000700c0285140d000138850700740c451000340101c5d101c40d04100035a001750001000f40c403450b1581800c0680314583d40c1c004040501d440c501881c20301c0d100040903070150f014603001e1a0940c2d1041407a660303648580c2d4903a40068464010142d80d14a0f80f082c0501100320255101e01c10005005c4140c01002071002643d0701401c054030498816504010450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 58037422 1250 58036172 58036207
    0xa031817100c1202030406140a06060203040b0d0f180605060405061e0f030105090a02011e020c1903020901180507030e191a010b0a08070201091707061d030301080d05 73
    0x4818032010600b240c001000302c07124024a114080d01d68008001d0008011300707130b0455a00d4000f080301d001101d59400320840140d806502c0b5106c0580c10400042c401c040c80000202a085140c00f00070a04a004c0349040c41107403203013038100c990078000e41030440420280d8080ca64100d081100e040c00340f4103000000502c0c504107807500c260891094800d1120071b4940f081d0325041030304020006c1005242007a40c0d2500c0380384c8075400724000780c60201000c0084040d02c26860029135160300500c3e0003100d040034800b4080081d20181b030000540d0708004016901c801960740a020402511900601d0316000e0700709481c0c3c06801201450f04081c40d4510764507002a040e0354840e010305000a0780701490800389880380400340d91741049a00b903000810700c44460300007032204019650f0f030001c061381c500c60102e08880d0184402000f00c02c400d0361100e11220910058020540114400940e220721540d02c49840da0301845084c00c2d40c0c0000c80100704249052100c2c48030414242441c501c1c1410180d640c00884 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 58038672 1250 58037422 58037443
    0x2011d0f120a170a0c020f190f0c08010216021002030a0804020f220207030818030901050f16050c0901050f0a030b18031b07050109150e0f030a031817 66
    0x2401054401d41107215031504241c035168030529a00c0350400d1305049003c0e200c060025000342c1720700140e10b10141e01c0007a844445c01d00301d0760140c400a000d0f81c1c4002c01e80440350341c29203d02e1143d85c808111a2820720040c07010501d180c0b8442132a080b0381c41030051109a01907824195001032140e42d1907a600124001e40c031941c100d034041e5042c06100d00191080740820103010711984006410b103010318040d4004d011240c002e8403031000381d99400c000f109224900e90040501504280911001940a08041c0c0306032401018298201100c1010300800740d83c04400659035540480501e01007810f2035406a03000d01002e50720340c0c03071508003d000324099030404d00c80244201e40c1a070004040140c980d1072001e0280b50070003901c0e03541410301c031000b80d480c0346081ca14105001d51040051590301541005086582074210441488941d0070190762010f051001e6541010100c1c180010641c1c0a00040c00540c4c0301ba118101e9400d0f00c0a1580220001742e00000c1003504041c65908807410000b5009840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 58039922 1250 58038672 58038703
    0x306010f060e0a150e130609050a0513030c030305040302010b09090a030807030e0d05090f0405070c060b180a1503021c06060e0903160602070c0b030109050a0506130b01020708070602011d0f 83
    0x44e000540110f1607145a41343d8a070f1115150050108c0d0300d0740715411040c017039481010148896101c0c042c1004031848a440d0040200c0e06100c41c04e400070740681c0103141e11070301034000010102000c40c00b0502c85001203603000e442e034000300c0c910803c02d42c1000405400080c549410004803841c2c4580781e64520b51075a1a0007440702c00700c0d2a043e29a00d41d006011414005842030200741440388000c0c0c589681c11600321903050800340340c0441410013104440c1e690194040c030209540383e00070708800500e0b854407181d540306070021003c80561291a0b003000304444c95a41401c1000e25810664100d400383c4c0c02159100e222324083c0403448100109507043c041000580110304401407500500a200d00400100b9207128040e000440c9102c2030043c0d0704030782c1500400d101aa81d0450810308843d81180d000f40d010001e1003100712029803a034441d03045a1010300484140589504002c1d1410806034060381c010703911026180040340c000d03e103410420300d6460040592420603072840361110705107503c0001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 58041172 1250 58039922 58039937
    0x603031d030709020c0105061503040209041e0501090803100807030803180f070b091f12020a0e0301050a0b03120a052d0a08040b0705040506090603040f020306010f060e0a15 76
    0x3155034240014002041c0b520310840d6241c000c040c040703000e080d0480340c49115500d1400e07590030041e501c20841b0301c0340303500070f11100741c6035100e945802c00c40d0b0710180d82d42000d8581e1031407400024024801c441007180200c24aa07203915141580170803842c2960070001d040d4001030300c10000100d5000c16250440c802c41c4070000d40781035401e0900d140c004008040181e600c654540046d00010b940003c14030b000c8107440d40228210390a0b0001c00f00105a800900080d030140f0340c0c0c04424426902401c040c88481c60134007201a60200040d0039a101039550713480541e40c814000071307a8a0100042914a10404105400c152666078050154010000b01d40c00303c181c94145080e680140d01c00486210000410103178030307030102440080040350226421900c9643e040080355400e07000c0c40640b0211100203041c42d107028814014800545c0004c0c1040704d0300c50303044419900581d8240401406440038109450300c0f0744c6400801050360b0b000100c42c074004c503807104092054001c1c00d0740da0800f850b013908051340c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 58042422 1250 58041172 58041227
    0x203040342060f060e0d05010b0d080903071208030a02090a120f06050903042111041b0e010f09090902030c0402030a060e010f060f080714130513060303 67
    0x284200d00606101803000940901e1030390359000c21441209822034802040280d4890700070200301089400352501080703d49010900a1401d03030401c00607a03100300001304503a00310b1004548052540b003021980850082281701c82c605003000300000405c0b08800d0f0f102200445c1c0c03650441031001602041d07600340c00040b80d407910b46403110110700406141841420b5100c0341c1c00c000104042815003140c1e03542c1448042039003d80c0000030b907425150203500001c2010700035042030318400142c0707900700c406c3c4181c08250242507407907201e55040f0700101c015107481c2801105c002440e00c00003054241c188504a040b403d080366202a607403060b82c0d0804000100c41c0e4150000a1030240c1202509a1042c000020040e02c900b070342d0010f03c210396039014402030b217980798400c60381c1c99a01400b0710030004406484d058000c80c8103500a44d0011101d0a18020b94114500078440c1035008080b001000c0c2031100c0100103034184025019a01c15814408118003815694000c0259554002d0030400103010202070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 58043672 1250 58042422 58042463
    0x8090109050a06020a080a060b030c070507080105010b07050f06010b0d11070609030e01030b031207110a08070803090906041b0302030714070b060306090f0c010302030703090813030605100602030403 87
    0x2122001d80060031901d07814543e02d03103c00a0342c002c0d0315000010b0243d6005c5a01e1400c2c0b40165025922201011411079813150442421600261801c6c0c03030900c900d15000601070340a12419020300040d030700b00c69881001b41403843c6013032094815070301640d000f4001003103400c40280603200f400f050314001003669030300400081ea40d8054541c010b00789900d01a5108101600410f59411490080e2018030401c2008810180c44044070f034040c1084800801103a07001400c14283e407900e050f070092504104544410045240c80c0e455049040f803940005031084813480c3c490b0609500c00e9044600b440b24907034408070b01d148103552560307990a1507008008a403c250040c10381c00c095034041110700e900c4641e0f504003e03800c020207458040c003070f00958000c500040320100e215102c03d46800014421381000708011402540300074420405c043d41c45401c0c400180c1c2800003489079040401d996103243d811030034a03008517103020382009030902074004108040c3e80c004c401c0e54222a0082c210701c403059040c20344c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 58044922 1250 58043672 58043681
    0x4120c0503030a060e0106090e0402040203220506042102150603010b1e090906040c140a03020d06020a0801080f0c040906020c030a0906030b03010b091801200a030e01021801080901 79
    0x308540804403c1003c07981e010b500030000c49210480c95510b0380d91382c01003550050120300811140010071400134025042c01d40041d03030014034101c440501c034081c00d8241110240003031800c481540000040c00180f000701a0360301c9200c030011800440b00040090003965a0102d214030400899070100054040d41e0700398407155180030080c0982c10400514540c0704030116a0100d110b104440080101c3c10b0300f100060440c1c4101d52001c03500860a08000c4054844c981d035100e01c2d64000380762070003c001a00c581c0000100148501e4000d40c60703140802c1c02400404c01608030900c00d038040c6260043c184d030005150702c078004050b540003403501114109203019201d070868030041481b000034022035141d80160180c00301c41656404103c0e031a1804201400d0703401414819a1190150010074000050a504541d1044c4920b000143d5092154450320704040b2048ac440c051004c081200880c1541500911054041050085240580c01e020350302030b41030301e0440342e030421050074001170200009511 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 58046172 1250 58044922 58044947
    0x705030f0702150c04081501050604030b090f120309012f09031204080325020907050306060903101d01020f180303040f0909060e0610060e0a0509010305060603010e03120412 76
    0x306000c8a00d000e0000840b1a03020348030b46052485441c901f180c014114550480c1649d0005103910310f0149180c480c210225005040c00c2018003030400d110240c1e00d41042540d14040028501540740d10381146d0300e50843c0ea14000300402e040040007400c4d400900b40c1e5024a00c420a064020303110203405d000f1900c1c2100420a00c3d804c46000280400d04100c000081c1003010903043c00c1c0e0606462144441c1d41210f01c41c80003c1d0002490780110f02154068405160300403006407886c1d0030b02c02001c000034507046130540c0364801075542e00040e003140014500c0201c00701d01d0080003545421904810741070103200381e140c0700a000c444618000c0b2a030740c3c18000c95004140e4031b280d803803049440e140000c00404030050201e401d6460000e00021040d004a6a80c7c03040b2900412054900d203810b005a07661034001541c2da0380000c1c01080407447e580c0e1440341c0f070b01031401540240389a1502e041810700b195203134018100b240d4000c1c0036540c1c40608920100d80d003d40c0c4500040070300c0c2021501a1245081b031136 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 58047422 1250 58046172 58046203
    0x9022d0306090601090608070303050d020711090412080c07030e0d02011404080102030906250e060d0f0b04050f0f150102070b03010b0717030907031707120804030f02060705030f0702 80
    0x40c2802400c0d0030000f201030594001181c10407409503124046070ba18280d03448000c2c082041840301509040c90765001e0200c20703024615412446041100084141c007045504440503002c5450540c41ca5602c40344040d0b0041c10b000083e841c0c8940303514040d0407180b01407180d13031050500003008011644900d21401c024104001002d4417903859588241c080c2d04102d070801110302c64400095000810050340d03448100b60801e071218031360a5141c04440c1904108000c4d41c02031010040003030780c1000340c07007018034810031141d001030030800c03003c2003006070740000d40310b04180ca004005001c1e01d050741d0001e00c4e030000c50aa00c9460300100100060b4103265a070b50040c90004404400041d100c102e440040601034425281880400000b103410303011800140c81103002540b11f944140001a03018100d10100c0c1005d0426904296540c3d9801d101d560030108108002900e04d01030008041d002407600f400c0c598036001501007460010001131990000030540d5840e106040041880e190007408040405030307441c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 58048672 1250 58047422 58047433
    0x702061902030a110705030414011707050d0914010b03100b0a050904030c020303070605010302090a09030807030b030a0204020a0f08090109020f130e0109080a170105060403061508030a030614030109022d03 90
    0x900301140c8a2300940308192180d9144298036040d0f62080f04901d552805140e28014640c9543d4001c4405400844e08001180d0356050500041402001210751445a40c0c002142211200090508112440c08004102ca003031089445255407051001e106486003541c4110265889003001c0b0780c000203e1034041d415000c0003400409004079034000074107803802a100c140c030b0380d1980c00341e81d004c039511004050001000000402c04652003a08403107212003005007154100303140390700040c0c201ea000008000c04a550507031070b03004241d0881074036070717020b08401c1c02001301c0e00c07468000c40c6c1e000000d80c00c2030f40320707004042c0b5040c811011644500040b00001d0002c00400b4841d1400f5007032548201500c0011903414040e010b160004144001e050f9070020740150306040c65591820b024100c45c00800407070101443d004a0411002c0014011107400f03581c011949500d481c0300c51000c1340c8018802400307641030042c5030015813142040c11407155042c506901141005841d407840e031100c6420459414020f4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 58049922 1250 58048672 58048687
    0x703081b2106010c020102060a11090307091a1905040c0504120f020102010e0a020102120f0c060a090c05060a08060112020f0a0c060b100c1205040f030302150702061902030a11 77
    0x7088005580140c01c5100300c016441d588010f442e04030215600900591252001a0000c08907811412115540200050521110b480007904007040c2e80c02003100d10369a0410507214106510012900d00c00980d03280188240b1042152100d909134000d8038020f0751a8442043c01c0c070301c01d02c02c48000300b40041e540074800001c2d103445000003500c11710a900542c2800d6082c03071400d0000c90401045513050f002400304c921a45c505080ca508100407015004800340f00124581c0e005001c0c0921071102030308002440100c40c41c0c60038032451580c1146005d22028003080c0c1440d90010b802c0790700500f003424000c07031016000941e8806032050b0180c088083ca40840d2038070740b0070381001179000c41500c1000f0500400d284541070003541507061318044009408a03040d800440e400040c0011203410030703c3c00924041e1180c0c44c8542c00c0665600440c0160300c0f50405030601c0141c084e13655001001c1c2d102801150a14495001d50384142d050841c12059000000c182c0009403903200c482c40c18910b60881e6281c6c042c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 58051172 1250 58049922 58049947
    0xf0f0702060c0c030705060c071205030702091f0602060115030b03070302040236010206040206070311191a010806160302090409080c1005130609110d0501020c120f0703081b 76
    0x540e501c603e40030b0310880340c02041c64546801075984056107040180b561500d000c90000c10b80001d03003002c0d11140010800800561280400584500f00250310702034140020380b4000c003078484547c01007003150440700040c01070910b015800580740901d494003103910300c40040001e0804405910007940648002501c0701f070448582004075400100f0100c4c1408401c4440109005801c09041d040c01a0406000500140307400c60141842c24044e2502c410000c0503501070310701d09a00300030001282c8810302140c1040180400e50040030030700c8800e074081075503d0191055070b900c002030600b060700309080341c050900c0c0d0300ca0f6050765007604005009000c0380c411410041a030b40e014207188000f6028440c00c0c0302120300f16028583c040c2c3d14402d5601529501c0da107824004080c050f10881e000c061441018101d42e45080300b01130064082e43c0010795580d4a80e810710700d0f1064904003100d03003030024045e0000700c145000c15a14410f4250900180541d6032880c0d85802144082e40e0365103400c0003044001c003100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 58052422 1250 58051172 58051183
    0x4080d0e060702010f0b09010605160b0703050411010203070b011a120c090a080d0914060c01020307120501050103060e0402040e0114010b130906030221010e0d0503040c060f02030f0f0702060c 84
    0x440b1038000f0000c0440600c4c0d62429038459414003904040c15a0040100510130001000c0d0650210881d18803005290760b128000c3c14180c901a00003510341d028082032084004440d4481d07007090000714903040351661008014503052080708182c5a5aa03c01c0c805848800c08540d101007081701c02041c1c0b464500480321054002454444c05008075550115400174000b614907070441441c1c40345100b452030424100c1030012400f51003500b0400900c60b00301764207002d0001d1802903040380c07501c2820061340c05128040300c00580c45030341010b0610a0401c111040c64840580181c5c060b139000c01d006c01c101004034054088120301a61080d40d1000000e02482440050500740c04c00d07413402c46129513502134480c190745c250300000e94030040c00201c6d10520a28410440c080d440080d00115041041000660410382062007800c0801c1000041004000c5c620050f40045e000074281304000c084505402035907030050514801e0580f000080b0350b450f2540c02415640e8840c2e0040c034040d980c543c01d091107034594 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 58053672 1250 58052422 58052431
    0xb04050c2d030105071706030a0b0a0f0506041b080405030c060103080d0e030405011b0302071505250b0c0313020307151b030509010e010306050a09020a080a022104080d0e06 76
    0x2901d50290700001c82c80d041c02605e002d00388560751001401d081c40304600d000b241c0942004ea05100e07103407109000078800351145108880d4000c0000d6440112800d1209442d00105107904c03a500c2c040b00c81d091005a56110345a412480c60304141a03615441c2c600e01e14401d070080410301e0b01c600d500000030005000010540884ca201090060003030803c4002c4c0c0d0390141d80111404148001e00012048241001c18040a40a84100c4940590740d04031a210960010400d40006400141c0d40701407021a0240350107880d200c6482007800400c64071a15040341d000b0b065007000001c00404910464814504910041d40003000d6404039075031100b4600504500c0250b02010643c00f00c5105d02c03142c084040c1e11031158250f152a4500005036004450003d4070407603460616649020100c4c40b611900304420140c81d40410040c2d42e00d1241c1c00242c4078500040c4182202070040080030100080c00c003180300040210b440f01410740c1c60f2460002020700404c0070b9000c6607460180c0b1100429000100303036015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 58054922 1250 58053672 58053739
    0x70503030402030d1b020603131a160903080f0705070306020307120b0108040302060f0703020408100c0e0907090302040903120e061506040509041e051b04050c07050a0b04050c 77
    0x40020b0b0f03080c117494400b03c0840c03032080350340c00711040e40260170804000c5600c18103200503600800c102d60340304104604900101e01d40c4610a41c100154020300e920200c004d0b4240d81000b0100925559074211036124203030031000c200340d0106144042080030040d810266911034005e54503490103920040413140c140e0000303400942000d0000303003554043c80701c8901964051b070240056507900c2d2814002440c025250404065007000700050500e001c1c001d80c2c99080b03040a001c40e0301d1203480802458002c15400d9070348180d8038002404011a00712203d5000c0340c1d41520b002c90091100d0600303442011540000b100d14504114122400d41000703c1c01d1803041e26440f413200d84050411080c00002c0c007860007203039000351524020070003040740302c020020004150b000602500f05a507490a0416151410300102c001c200d40c501c050f14542802004e0f4007055040700c142c00c00e000ca0315026543d000710440a4102c041c61000314041c44414082c05000c100081c0062a000d24800d1305d0003041080c03081100c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 58056172 1250 58054922 58054933
    0x20f040b0a080a020304080a0305041b0308070204050c1614010906050103150608030f07081b1504050c03060c040324020f04080705041107240606030605010201050a06230406030807050303040203 85
    0x1410141132003940c0c000d5401c500d001e0705002d1104426801040068016a00040054600351509004110745805540f00b0b0850640315003040c0705100c1942e40160042e21428000d0010350b40c10b1014504000189822810800080e01d480261500510014101808841c00c0c18000b20500c0308000070070716004405c00d800c0101c81c0c5e0311520907449000e4425040b0b4407500410100c070124094501500d8061100320440c000030096169041c50029642452040d5409850802007070000c02d1000c03101401080d4058140c03840d181868240c20f01c1180001410550640d42907103c0e0744025010801203044160210b6407100b500054a82d00c0d00540310701541d6201c1c06001045500301401104030441d60315500505100301c60f13691480007142c4505041d000514402d01d00034044660080d04000d007020740300040d042703091000081c00d4890041400c0040360804008010880107120f0f0103940348608100003101134039180002c0c024200c69400501007090104041d002e012011000f18001c0d0b100300c04690 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 58057422 1250 58056172 58056181
    0x31a01080c01090503030a0c0c080105090c0909010e0607030207080910120c0c08030402060306180f0402040e06100308030a0b030f0c03010c0c050601060804030c020d030e122e020f040b0a08 83
    0x5643d0b4100c0c2c004c0e02c2c1c164005100f20400c280c041c3c041c00380c8003449400e014001548401145007103a404079240140d03940684100506070034403200721604003024034000d00008418240c555951080a06800201540007a81005000155040d02c0b0140d800400c40802d8221049008000350f11099904140c079182c040085103860141044030380c1c16611280d15811a6a03513001c00a0342d42005001070b0304441c60242d2004504104110b00b0711a001d18000800a42000c0c010303c800c94021a10180b4203a125209000300070451480c0c10003180d5000411303583d00c0d0785121204c8040c0850b03685244d01480340ea00c070806840d5020030b1402c0e1180045d0020071481024000480b628641e642d0b010303044c2d402c21401844114400c900c40b0354007074000e007400b440c80d40856000c220001d00601c07051300025503068216403680350588011841926a600510601e5a60000c4034903442403281e0003900151800304428500940360103844c150344000c0f4000340ca456951070094080d600a4006500145050700043c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 58058672 1250 58057422 58057427
    0x50a06080a0f060e1e120a050d05150303040602010504110f01141806030f0a0b060a1209050a140601060909020a080103150f0608030a02010e030301080a0f0c031a01080c01 75
    0x9508403105000100100030031619509180d0700220700c2075503101e44440e0650202c0030f082000d01c0b00c581041000c078a503020003059843c100f0044100362500c0b50b00400090012079401003d403001038402140015107501c41c440040040d142040a0540500001c500061000d40650000344100c6c050502c035403a224820007040a010180c0c03004601146800400325010110600a401d040319458641c1d60501506030005140c4d40040740c5080041c1b1a000070800c1189103802250003000742507a105003054249540034041c080703244a4141125564461941403110070444024099000404070212440b00e40d040303515008240159400306a000034000341c012aa031007105c44007003080e9101e40f00c0340d0a65850020500d60203840b07608023074a48588091007800d5104020003010102c1c0116900d103c0d100300a400d403115015004804d40040c001000302c25008100341030b0b803952040c04480c10b03403e5407503c81000d00107600050400201e203800490106140078080c5d05883d03162080b240145c40c242c004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 58059922 1250 58058672 58058681
    0xb0a0303050a081b070c171b060f210106080c0306030d050906091f0201060609080c0f01020312150901082a040b030307051006120822052101050a 64
    0xe0015504025203000944908209904868072824030001011184e82000702034010076025140c140180604000001100ca06146280c107070f50090b042c403401c00312030300c01c140d5400c0813030b82e0284c100010410313581500f02c8126044d02061210114a0140200685986040c24000c0c2c0000c076040c5404201c1c0c000c24502964030911000f001010b6210030400100e03080d41004091039000300003403041075500d589903040d000c008542d41c0c1c86180c0c520b43c90000242136800980c0002d0030b1000c1d208050050340d80c08180f81d400d00c00240c4003031101808110040389184104003080d0510a040b03030910886400f0300358100303208007003291401507690321604403640702c2c0840203a900d050805000c00c4e417440c804420306074460280c000c10000f03241d000342c00401d0542c3c0c07140204a5040c2c00142c00c2c17182982482c480c410181c0700c4081c01c1400d09800d40d540005500c02d443d4030761300107248210740294030710f001000c20010b01800303005038001c0200b851402c0350003004162295103a50030000001c0d07108285214 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 58061172 1250 58059922 58059929
    0x9010513060c020c030105010902070b061c02040b01090b03130606090b060702041808130e0c2a120d0e0106080a02101d0409060902010f030c0c02060c1606020303010602070f03030905010305091507020c040b0a 91
    0x70842c42ced499154200301c024410510500d040c403000c040d0005000d240300e0040c52192105100041c0001c0b00d9160180494800c3c0d0403062005250a03100174850700c0c0c80f015034015550640d000200030002100d02c1d01c4912030404010721403400002c3d503076600b080e0f5190110885180d41080c0307080b525039152005060140c43d10001480c078207007088100050055000c01e90002078007050702d4050039086013044e0706038800c00051074201e4440c40e134880b11170400d20814001b4a0082d002c2c284c0c00d46a940041c08401c80e050040c01002185040c0b500b0412000b00c04140e017007030080040041c5400b07442c080c0e0161240110a0b03020410318400781440c913009000d90030001c8026558528002c049a0070004550807103030103011903115042485c0c04401c0e49240180290030190001c644035894040300901e841e00e00d4218500000101000300300103500405400700b55402400c001c2003c1c1e40d040030b040d14040c4a02606403050341041e0501c2842d40c5c02048020514a040d1801e000c00c030030500c2404050840c920 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 58062422 1250 58061172 58061209
    0x30c0c0f120b04060603080a030e16060c0b0a06090911040c0306030209160507060e0c190b04090903110d0807090e01080a06020903070e010b03060909010513060c020c030105010902070b06 82
    0x350640040c0103862241c0c1c3c4540310380e4000581545940b19078910303401000801d00800d6840c2520120a0303070400840c1141486280c00810482c00c10500410940715504020240c024041c08200011804c0c1c21070409040c3d0031904000840003414030b24032815010720075500036860450851001c80c0f181c055002560b80143c00001980c0300d200102d840c5404a400e26002c2040c00e2000c0c000080160256042d01d0100728010410f1900b0031013000072510035a07042d800c44034801c0364200041c0e00c000341078604540c80702e940000d0300740fa03d007420749402c801013079101058080c052031803060541040566000e0149a509c40c80d01070388135101c0b10341602c0c0030b00840070242e0100f084100001c1c0c0075002011070810240c15107141903030301c40001004400a800000785140702104118441c1402100c1ca40c2c0079203200000d000a003040300c180e01e088111580050311490710350418561160080003649000c89029000308180c3d039642c41d030f800003900f00d140c1c219195034100010a00c1d6181c01ca41d0407030307a480000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 58063672 1250 58062422 58062449
    0x40302030a091e1a09120105040303060503061306090c0b0d0606030f06080307060207080715020c060601030203070804110a0b18031006030203120d110313030806030f0703031206050904030c0c0f 85
    0x8100900d00131085950b040d40000400c0341e4003541e00da51641c0c900445d00c8000108043c2054500942540c0f03143e0044d502a6000004014102ca0b04500d4103041075040b090000e200700f014200300d00b4401458010130b02c07103440010000030b4154598000811541e0b80d903030130084541121080c1050325418480c4410a034005d111040215405500805906200c0c15501e0700d8007030507544080c3c4000d101c1311014025980450305144a01c002e020440d441202480c0441c13551600f0309001e840c45201403c0074150002d010b4a100203a22841d82020242c8003101c03046450f13500700040881e504072101c01d0f1900a01030124000800316003400740000b646d50003000b411040b140c40c118030070715421032034035003a0040c1c9414400350703401100c20086009030045481489015032070b04025001942c05004280a0790080000c00b0b4081c1e4003194440031b4030350502d04010344404e01c54030304002d405d4941000341d000545505200c00c16810008501320300d4407582d402114241c0d40c00401021014038842c0c1841403508 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 58064922 1250 58063672 58063679
    0x50604120203030601090b091306060f090603060b0a0807030b030f010e1006032307090501060e01030e06010501080a0b040b0901120203060a0c0914041b091805090a030804020315040302030a091e 85
    0x2040a0003100d04068484109e84003822504000c0e9001640714002007241407002480213540100820040c0c0000c0c01d0500442c0e2900101840c20700c100d178101c03420000e0000101c0d20700c600c01e40112039000c1d0000c0c00c4802801c189a00fa9000307004210300c02213580308998103203168024600609040f203802c030400700c0c0074802400c01c2d2041a07154203503414441c041c180c00841c09501e28801c3d280601003550b920241035003240c001500300e07010ba0640e10707030648c040300040109030f034000ea00641c000700c1c82e003002c2a520300e80008100980360304200c15a0082d021400494034111500302688401d000b03d0031148941c4608100708100c4e50848954800030305e0b40d54050007000d00e0692007018921000e4400a01010806a10300740305008059400c00120a403900b000105054401c085c0c7d02c1c0f001c07a10030001410224462650344a081c400202482801c00005055540920404024110f004074044581c6040d281c000d40f2130f4480300c501c4000c5064000082004c0b4041c0e40c20004198401c504181180c0c00d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 58066172 1250 58064922 58064939
    0x140105010e01111213120b04030e060708030f07030c08150616060f0510091806050a020408030a050d060608040302030d051b040f0e01090203190209130905060412020303060109 77
    0x1c2101094103100c0348520a512003101001050a03030030000a2403520749100003012003030503195902507154829014103040124480201158000d40d042c100801c50341840c4010607418001d1a0003d050f07404040f04100076039601c0000384d0300c2490aa40e0800601e10f50000948118005440742e81c0507609843c6d164203181418401000d440c041c2079011659058199680c1050700c89010518070b0751520340c001d01407540402505d2801500580d2002e0101452032034104203202d04821000e80301c992140003040c200c48075541114040c1c415901902d1f038400d050318010340580d01208408151510f0b210340050041c0c407850780c01c0d0050758150b02543c501740b10341c245a0b015100c007504546121070707042c0700030030b4010030340d80103000400c500f0342000a80341c580026400c078048164050340315640104100103560742c14a1038040741000a0500685822001011030038a102c1d84040c000a9840e00d02e0307402c02d12800080d0148200d01c42e00d007080c0030b2450100100d80f40e000c10b0350000c5c04078031442420b210084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 58067422 1250 58066172 58066187
    0xe04020a0b031b030c0f041706060321070f0209090d0e030d080705070302010617070e09010606091a090307031a0a090308220b0103030302071e0807030e01030f050108070503070914010501 82
    0x503a4a0745103828040c0588255003140e1040c8c0c03002c0b5181c0384840c1c14000c3d8440c1404580e40c804005c402038aa88200380b0071454181d08440c901111a1800041040070005205134001c01d00c0c0d005000d40c6014a44000181d42d20400540c03000046038520310000e02e14a0005101036241c90030351745621aa4442e82d6040d40d060300a0702088042d952a4080880d070300e1902031000c0c0320b50000e0320051078070900c1d1009811000782c000d0810740041c2d0500c01305101070303500070030800c04030b039a80214403141c00380d41c0c1d031401e103580945a00a54540903040c00042400303582002c8008510644942c2c10090300d402e41020211a90488000e000c0f40e01e52001460104070b6031640329100925448840300320760135545001c11010240c004034086907010070b14109101c1c1050180e02e4006440318030702c0c2ca2110070745940082e40180d140c001c00f001200c505100040e4031981019030004400c260030300565071034100f940d4444aa90060b10300912541c140050720007614050009040c50001c41e8101a90034a8011105d48 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 58068672 1250 58067422 58067431
    0x10e2505090609093c060d0302030c06070816021c11010b040906090c0f030b0606030a18060c180506030f0606070503160b010b0a0203120a150e04020a0b031b03 70
    0x848148000c00315500e80c1038034580b02e030742d14000c640e90350304036240100d601c115a05160300006880700408045c41d00c031440034039000003040303079521240141e6150491540c4a0f8808039100c9005120511544a811400d400c0c050954411010a10144c0341c0049a64014030205407840343c81084501000703c2c0114803640c110101180042049001c4a01180541d020440101d511990364060642804140c3e807208001d082411130004010b85140ca90b40003100300589410312a00001000c5859046194030002d029258607a0245c46d0070090b0502034014040ea03400400441c5c021095240360440c0b20801000340d406c01003080b42503480d01000302200040083c01640c115100304201c0001c0390040026040c040398800c811048140316160120000070103070f0114080e020240f2400003200e4000c020b40308603000050403003483e9607940c1c0c0c125021301401100ca0064052040c2e02040e80085060200e1082c2d0083d0382c856091646c0358000809440202c9456543c2400c11142e40b181d5440e0a0055030413 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 58069922 1250 58068672 58068679
    0x1c0b0102011107030c0c08060108030714070306060602030903010f020405010c03050702060c03030c03010911030106080f040c15170108060405071a090910090b04050c0405010f0903080a0206010e250509 88
    0x202d840701415041507002020a6010810144041d002c2081c424201005080443c001c1d000c2945407aa04958a00844600514030000e41d2804070740f40303408000100c01150000340a0024a9880c00060340b01c1e44400c059500079400c043c030398a2201400e000301c6045603010703500c640401641d9141110301e17402c01001268055404c1150b0440c48030104040d5004a4291300d955689502d420700b008100d55240c2c42200055000f400100503030b5800480540e8008000c002002c002c0da82d61510070301642850b00400c0c10000382503010950607a10009001d00300142000c2c072040c03a601e800c10269502c0f8200d0f0004d205510002044c410911000c035100c04400c001103406085c00280b01c005031071003404465800e020108a1010041a49140141249403006860401060510050400461140303010700780c180944650450301e56849003104900460b005010240c90b0340d0300000c000d494220a10400450642040106058541c401030511034145000c1ca03400d4081c9d640c10040e101c5800035190036030f1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 58071172 1250 58069922 58069931
    0x30f0d0e010f050721020708010603050a0807060b030f0102030604060806060a062106061211030402090402040b0f1503010311030601060206040b060f03011d0d14090409050109080a0206060f04021c0b010201 90
    0x1440c40c6205220030030b1500d005d000e00c00ba0301400246052603907800074102d0707030411400700046040171802c194040d030080e05195503079400c1d040c00c00203401d0030140c19402d0b202c1c001000741c7e01e5006601442c00303020308072400d000855495900c1581c032401991441c1d884151040c0400400e07000700b00480c64254030003040c0102c00c51029912080f150298080c0c03002c5160707407100001e91203076445103c09030704c40d00c0003660450130150003007011000001c1009000d01d80e80d250130241d83e622500b2021110740004c061601c400c4d2914182c0100b41c00c00e200c00c680da00900802c1480620b0041040c6046c0c49055004004c255501c0d2900c1c2c11006002e04259002804030480c04081e45080c02801c07a1600b081110a401e250320051003403800c88441d00510800c00414a07a04011810104884588504890114044038a400c0950041903950001006108000b0f0a8001c076034003c9070052003000c2c2121802c0c6415201e00c00c2c04103902c5000030840b131500a20603031024001b000d0380a2000d0000601c000034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 58072422 1250 58071172 58071187
    0x30207080706080603150f040f030207120f0b1008060403260c0a09050901180515060c060717040213150f08010b0a0803090d03080403111506030f0d0e010f05 69
    0x24201215600b2200c0040c100508200003030a080002240da400049200e054601e0069030b15403a0b0f080c0580000e00b014502000042030501c00c0040c00050310811902d01c41c1441c59240001185010903401c80350454210006503040340584044021141c440c0c0c040c140e0365441c0d540031110410181041003000011001009100c802c0f2a0924416000529440d03514580030401414201c070030707404540700d0400407006110705152611410030311845004041150744400b58001101c403010590250050004240c1c07205400001a4443c003404564035608106010740125000c10354049030003a40000e43d403c0e0b2103e03842c016030700c050440101c00c00014103c944400660409d48020780c4040001c1e0f4480c01910b20b0b40c41e00310090f5005001146c0114548000380c0041030600303050a40c0a018070007900300080526015030403504065858009036210b00c1400c4813616200c000a8030070a0091180e002d20400311f0000207411000f0088940703541e90144407200045130a640d0f44807402040000920465 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 58073672 1250 58072422 58072439
    0x206190f0207060b040b0a050f01110f03130302090a06030c030b04031e02010605030717100c0917332403010609050f070f05030f04020a08030c060a0609020c03030c07030207 76
    0x1446181d03c100c002044803c1124200001e4603d034007581e81c07107100342d54400c02456880c3c04070f8110080c820b00b420074000c011001040d051180b19649520b082c000004d540300110b003402d1000e01540e20859802d0401c3d00d4081e800000c45040d030000a080c0c03299020203001013016151900d5002c1c2c80781c0340c802410000c0b00352007501c10a02040c1c04015039102c0805120070726081c0006c50141240c65480c1c04200b6420591590794401e980c03c01d614656103a184004040c41030041c0340c080c1104041c800d2903031400c8030728a56500b05024607407945c071080014040c40c9444490922038075004c260304805d1151074601c20141900340c422402e002c02c00041d00800e05984080c007c0380020b00b112000040c03640f60982240c058101c0043c0700204000b0400010022160031009494208d81c0d9204103107031320b41d524804290404180c0c4c00c13840007440003244144c4a607030000fa9261141c4014102070204554a81220080e4003034030f40c0405590b0024800903500c2c00c009030140c00e800e4000e1044802c416541c1c3d00a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 58074922 1250 58073672 58073677
    0x8070303090c050d020102030f0c0a02100801030303050604020c0c1018030b0108060c0a080f0c0d05010806060f0616020402030613021b0c010f0f0c050a0c1401020c0406060206190f02 80
    0x11008a03446100d000203101c49002c00c1c10080c5401e07982c82c260008241d0000b51244203c0c0403812007400b0200b0381440a80080040313818003540a084698a1012030f003001d00480700174030007140080c1c01c2c00006541800e160090304c4100d0600030041c080301d0009002c02c9109088403845204019071118903003001d0710b17544603c200941c0100d113120225410000307540c3c00c1000092803514946810482d242c00c0e075030300c550420f078050a02c0c0d8100d212030720341c41c8990000d40710f9041c6000f000c1d07082400110b081d40011a40e580501e0b0101c2d452000701c4011000e015042c001c00303884000c2c45c4016045400542040d80065602140c001e00080d8241c0c82d0313540080132604a210603006c92a40259140048907081100f0224808242030529540d103003031078000c05104500d2401004c10050051180c00c204082000310ba01d81d610080c03041100e42c8074510350392002c502c40000c2d030040c4200091240941090310940064680e04e502500c074a60b01c20303104054400715400458503495440c229800b4180040c0301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 58076172 1250 58074922 58074937
    0x4060f060902071718060c010b03011d01050f01081b030f010f06030b0112050a03030f0902090a051e010308031b0c010c03050109050108010506031507050412110102070602070605042108 81
    0x100140c4408142c100b42c045004204e011401d4488104007104185036507040340c07040d49104580c0d09a540c00003030704180c094144c909005030550b0030701904034000044c800d6207501c44258032000700201e83e10340c0e1781c20302e4000e001e10172000315420008010a440800204103444900060211014130707541403155407c4a100e001a842d0b1030380c2e40c0409104109601e080341e80100740041d400c400c45400f07a1209900c442c16090000c080c95940c0300c100183d06160b40000241a40040c4043c820b45001000d00c806442c0444c1c114040000c2e18141074004c08514404034142d075000884282540d079611034444507140030122440348100113000258001409000c2c624101040c1d50b03001c00c4a502d42030101c000d40704107030000440d903410041000269180090f01e0741190950010303008003511241810313282c0344926002502208009000c2d4814041c0c0081c200780000400e901b201c824940d03646040f41c4445140c080d140015204100c01c1091040071806244242d640d680000e1144c5007540c0c955949500020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 58077422 1250 58076172 58076189
    0x1090f0906060e19210f051e0307030518060412030905010f17070f0e030a030309021c0c030f0c09050f0703061e05060d0e0d020a06060504060e010e04060f06 69
    0x140900c02680e200030a001107000c107541c400c503050042c0c0710007403100d0b6480c040d0198400311100d030000c84074120003001007806d4011107036a030f42801608103140c4440c42102114100020155501c22280b00001100c1c003050305580c80c40e0401e1552040381840b18403650384c542c0d0022003031002207660254215080b180522035142c1084c51850701001501c603004402e04041401080d2001d2450b0300e001182c6158000014500900e000001f0303441a030b01140c1c4004410340521a0384031080800d0340691080311494001c48003030ba2001114001e07010041000b003c002e0901d095800104002129010402d002c2c9108010280c00d680c2c80e81d901d0742c11100111000d00c0d01001c0c940034400e03070356058815100038080d4000103c038014104a28007102060a111302405440002404000070580e03500890700100d403001507580e450213641000b9a91054010305a030810b141c1203001070a45001d205000c21501c1c00400625181c1c41d21803c1441d0110003001502c0d00e030b8490074000c08640f454420b4101800000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 58078672 1250 58077422 58077431
    0x3070b040b16060c170f06010c03030b04090c06020f0106050904050a02060d020c03030f0105011701080d0c0201031d01140f06010905060c0a05120c0f010b130e1c030204050f0102030a0c02090601090f09 88
    0x1c1018011400b0242c901e006e03485c0d050b41030080e56640103000c520840e0301406c0105051740c510011900400030024050480100e40d04041991507000c2071450150189600178000c0c1600c0e1010040042400c2d03400030016403103044c0640040c03c10070041c2850700059a0018104210b400030141180c0c402c03035040e030703144901c840107004a42e0040440300d800458800107891940c18007510ba640c0310407512010051199583d924421603229070404500d140c1e10b0480d0740080e907500c0440030b01a00214903404001110b61300000c0d02034803201000c0340326020507560300f40c40a00d020248941d540c46804448000d0141c101c120b400300b40c08002c03110b000c0c541c20002c95592040e0516090800e503040324402800c1e4100344c40c2c4074090303031210752040c2d403441c0d0841d000444800b081e54091400881400c3c503d2001c0b440c88140b100190994042c000f1241c06540800d5805814401281c49101d1a900500810b940640b100050304200700c42940c4110306050000c640354035031041d0142c0c0180b99120b681c1c95900c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 58079922 1250 58078672 58078697
    0x2220218120d0206011406070c090507090527070504050303031005040e070302150f2215080f191d031803010603050712060f02030c0904050603070b040b16060c 70
    0x241e140c00c0512041d04025000607041410002d441d0941803017640d441c100c1c2c0710901c030040d0740e03903000711100c199110088218240e600c02c0c912002d054102d50850101e140314100040a08049406c02c0058681841c40d000915185203401c480c2c60b00581340c0310402c14180000710702901c1c1003000710300840030140002101850102000107480c002c01841c034032500007031070420060312110b002c0c040203510021440d0720341c500364034000310502500200248003004040b05440c854900b000b01401e560003583c484800c0543c410080d9000c2c00240c4005441c2c03118000041c51950083e4406c0d83c490103099400b00e85c050703481805007050b2205112040307254000155206070640003030300f02c040240080c4e00920580740755845072600e49801e88110300c01078984101c500b04021003035200c48811045288110740328202a09009030380d4008101c4540128a000081482440c0c000384c114100d40840798160326207400d00740c0b005a20707080bd200403140200000c510400044031405088800001d0780e6071806101d1a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 58081172 1250 58079922 58079929
    0x20316030e0411130b18031608060702010203150603130204020301060207090501090b0603010302011107241206050913050109050a06140703020403030e0108041b03030302130e1302220218 82
    0x5030441100c00c07030b41c0708014884c103400c01507200c0d104079451100d0300e5440318450780d4445c04442c001e4413050342c0341c00790301035a21303510000085407019507845100b207030001d80c1c94400036400c030710054541c001c0c22103000c4000815850004000d40c2d1104000e600503085002170303408601070383c06c02e804c21405604040f8080c003050391188190750052a1026050041041c0000421900e00c0107000c0030b41004005180c0c43c2d500c2030100030f80310003040281400c4d01031071202d0181c0c00105595030129400039140302403510300c3c400305014a4054590003800d00d49030f9100d01101440700d00d044032084440d9501e0301c6014020800902c050f00280d8016140414110001003020020010090040b030a0500c10f00c018070200343d02c0a02c1000141c0207003003820042e207450034a07100118000d44c46c075202c3c0c801200f02008041d07041c1c02402030000988aa401c0c40c1da100c083c100c43c078400c01c03510351486507511800c1501600c0c24095403002c2d1001880317807c844034911000d05099030711840c03174400303e0b05102000080c04e05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 58082422 1250 58081172 58081181
    0x50d030c0f030816020a0b0105060a05071e0201110312010e0a090813030303110703020d0503060d051f0f1e020318070311010206130b1803090414060312030c19020316030e04 76
    0x1c4c50307101806034110706588007620380d04180500c5016040c08201e214a990042d021141d015800c0044200030a50f019040345030f40b0040307041240040c0e41c2da18942d83d01c041c004103030f5401c80505020301314660308002d42c070625014001c02280300389403a2200480802d806138010b18a0b5425040c3c800940e50850030301a0550305210000c0030201010411413010990105981014002516200f030f62910f0b03da0020350341403a03882c00500702c0e000340507010b2400e800300aa4000d200320126002c0c800100070354880720440c2c621601c1001291900a40000b03e00f03030990042d0381c480c4944890007103089201520f6031a16450303070001c41c0c0e015414886c00700d46603010030003154008100c85241a61000a9444140340d54000d1300c2c04c40a50b038403004c0c1290f0301c44240150780b02000064800c0090364440b10b00101000c40079500c0078064000e8140325010420f000046910510100d80c00d070746840c0c04600c40030310301541c0b10003031011400203201c0d00005103580984102c405000c0d17500d01c22103642c0c0c0000c000469 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 58083672 1250 58082422 58082461
    0x30221030903030712110307171b0403020906040603060e0303190516030f0b0616140f06040201110f10051603090c0512070e01121a0601020601050d030c0f0308 70
    0x55424000c0040e101c4002080781e5102642d460005003145400b44090050301c0c07040d04054100034003008010040da408207441600c05c601e0321031145ca503140e4071640070840484007021802044108020300c098140340b00c0068111401600001c0c0c0741d59241c50b030004135034168042d00044c0c0c00000500c0031100e030303551400584002c485810080303410130072222546c1d8130761440f5020615031143c0341c8208415180e8008650740201030260b035613580792004001014031240c0001c0302c420882d00e003803d02d0f142000502280d000a654001c01c81130700e0f240c0066800c000b05816800300340c450004403185602060040c241002e84400d408122420540301300c0d048030360000d01c08802c03d841c212022020030500d0480740102d40b008c2d101e4911507610001003038100166500540c6032611558000128941d55100e03c0c016a030203090624140c0454034944244420306035402e0340140d228100600123031034040b1400b86202d01c00d041907411072815550b000d460204401c1c00b5400303d01c00e101040291048803000300c60702d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 58084922 1250 58083672 58083733
    0x909030809030306011b061e02090102151b070219080c01030b0d020901050103020309030904051e070c030903060b0105070b0403020d020d0c03120506040209030307050102070501060614190210090302 87
    0x1549840400205410100c03050304050001b02101d00b02407103200c0c0d00500a1708a6001c035001543c180c3c0c1c034901e010b940001c040034018410303079101c0340160340f00a0b8030500841200c0c2040c0440c0289505048150300400803d076401899001103001403400603a0480051058801500288010b1030014080f039160140f164000e484418102c401643e03810f41076415541d090800507165141c04908070701e54001c1d001055013207490b14062200260b00b442101c0c0141105900e00d10346903540f10740c12284285141c8005020662820007440050104d4025048407441072400d5410440c1d00d868001036000c040d40c0c2500035030003c40840c00030300c3d41440440b00024207402c046001740d00564004003412900007121424a560318045107566480e9012a42c94240c001c0489440365000e0400034000c3d030000004a644e5131a000f00011120b015401503103048404c2e00290707007407810300c0e980c0005561440f20400218041c0100c015002d0f61648500c0320524002d600802c5180200980701104c80304206070f1380131 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 58086172 1250 58084922 58084927
    0xe07060914060415030504050708160e07030b031b01030207060204061101060506041a07020301060302030a0b181f05130c0f0303030e0c2d0901060f0e0a1a071401020301090903080903 80
    0x810102d91810324143e00c4c291030b00140e40da48030704110b400e121894202018501420ba043d84121005007264130030744030031560090182d1a0510160116001c849030306415070040e00c1c40f42c00a8898106c402e54981043c10301614100c00c954440b000c03a07001743c000c0c0c0d001c074070940711500c04440300344210000340105079070b100c0c40e090030000c84514480d40c40d120180701400c0040c0380821034a082d045400190b6014003141c1200714203242034542c00c201141c0c55441c500c002c1c007440c403000d6400103d00d0120010501c14500520301700800700e0203810000d002150103503c0400400010b49040600801441170f18241100c2d5415850005d0548544030540102903220312120701c6a40d03074010130808100386468004046041010b95440d4110708100c4641d40000d01900000e1210b80003401d10100000e00d660700009040741c0c10420010800703034001c5807296102100c000d5011903100300109180d501aa2240d41030703000151116007664030076001007007800d032101551010190001c140f1504003088002850 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 58087422 1250 58086172 58086179
    0xf06050a090f110a0e130501050105070b07021c030b0f030102031506030601120212271507030204030f0c08010b010809030703030207291b07050712060e070609140604 73
    0x600c00d840502a808859680791800b20700e18441e6444580c0c003141558000c1c2e103982116102600f9091101c1009014500c00999181c03400d6007403043c103060301c030161a0f16007041d00c0e07500d916944c030f000140b200c000c3d4410545500d2520300074400d141d81014103543c01280c04002101406140b84884035080c1c081c1e0700500c20b01580d8221030f050380e40080402e95a40d03480b0351b81e400040743c203140380b00086d100340d03031000030101d0720507035510845446100140b00700f000038a8409032040c03200ea2031000c281c8090304100c2104803501180d1140b55040080c4d0726004d0709250322034603414200c024880b01160003400101c000c001003142030040ca69001e4007420000c0291510046040d00c81c42900c1e402000c255000408808101011001d21500040504000b285a8036a50034541102003503071024503000146c5400900d01e501c11040307903402540140502180391070140c5810000c02a031004882d030a0300d48010b440c24071000c02804d0f0082c486507a80300b144602d810108a11501e9104206025203000c02c41030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 58088672 1250 58087422 58087429
    0xc010f050a020606060705030702090f010806010b04140d03210213080105011203080717090a020111030901051b0304030b040302030a0f0201020a0507021314131b030309030314070b18010f0605 84
    0x81364810000d5590542e90006490300c01d00f0340c40b80e450025480038146003400f0b07110200008650580f1011401c81d50540d8a8085c44c2c03280307014034401d920070001490510880c4c0d040034040e000100d4441e09103035a02009030803d00780e1182000d0314100300c00d603010900d48209002d001c1400010198100200102c0d414a2001c03610054150405024000444080740180744180d1000d00c50316080e458590359400d004000c10303203c482d0103600345c0c0002d001c00343e0001901c4010045a500080c1616003500d8407414001e00c4120202c01010384e001c1c0d000922001002ca02e0b545031007845030340f19901031992144040c2c005029018581c0501d811680b0502c0300a1145802030200c42c1c1007a01154203030b6440d0725008403c00176100b13201c0c110600100560512800403030b50119044040d119006441480b0b0060203101003001180c400030700060078279041040440e0041150f030090441483c51242341404c1919182140e600544201c607206a0f00045800628000c1c800c1602c181d90103c01408040e1411000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 58089922 1250 58088672 58088683
    0x2030c250506060d050708070b07140c09150d0204020706020910020303040b042003120405010f08090d03051e0106090e0a0c020d12060906030b041713060315080604050c010f050a02 79
    0x209020b04c0e5201c0c0501c0c2848801c20443c80208604011201c0b20360f00c86e5000c0500744c1180302d04440881c2c9501c580041c611001c44c03000501c060107407104003140d41c2c3d00442d00c01d815603a01d015401c01001040c000c05070311240010007020f0b000c1d40c0c02581d00c0d806042400040d503640c00f080790864000b4001e02c030014014a180035000394010300003884201903040100f000355180c50305180d1500c80d0341d8800c0d0541039004060421294262150061508401c0d0299014801151008096045803440610759070180c2e0000d90840e20800400300104841c00c0504c8c414007081e040200801c040303410401103a100b562202e94015900081407204000c5220060b56400e00c03000c04a05000050105a10890b050341c400c03002402c14810a2012558030309101c0219402518141e0352401150380d1151302900c207034125020301035070182c7d440e00145020b07070880080807600c240920441402c200020184004c2085500540c040c0c0c01515488541c0c1002610800c25017040400340b090900c050114a60045003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 58091172 1250 58089922 58089931
    0x10510020604151b0c060507050424021207060f18020d11120a030e040c09031a04060603020a06080702150603070501050715020f07030e09060f01030f0b0402030c250506 74
    0x100c3e101c102e0682a5200140540c241086120031070b0354451140e003540018528200e90242004210030b171640c00d0203c6540c46a8010441900d000d0724070010650704e030841040039640e5620581e900d00c0e040c41e00a0300213600c00030080d2011a00e5620800c1c01305418030804009100c21141034007070701f1096012450b468001900070785640400c1c40b402c0400e454804001c0c040d01c51000940b00e0040c1249006848031290340b54032130007a860500c4507011240203402e0b1509680e080612081040c2c10420700c103068400041003224030603150a8000016200c0040075800761486480b920143d16100400070300d4405d5003002c00c80001346050031f00c60305480218140080d52002c0ca8900d9a400680c18200300c10300450350302c0010707903100241e00700940c19414041c2901e244a43c0e201d004010030001000307503004d015280103501c0701c0303601c01e0403c266000350b1050340707018422400030503100030000c001812a00215a94200342c2c0000401c00340203421308892780841c0d460f19070f5a5444035403c0d240d0f640e49039030050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 58092422 1250 58091172 58091183
    0x30307201e1e04050a020703080c070b0c0a1202070f0317040803060f0402190309021801080c040506030c040501060509120303011a070c030f15230c1e0409020909010510020604 77
    0xc1145050034041c072840b03802c00001610921035402e01c07940b650025030101106800280211011030b00b07a0b09464200c0300c51680200043c1d0305622240d40850b10350748003074204024022100212682480c05001034448503005041a401c05107481c18090288014100300000c60140c6004001c002041201500c0c2c2042080c3d400c1c16090280d070012400900c191141c0c00100c10406c0041c14030280d0540000403094800c0d1001c45040300c1900403002003210030b014500ca00c0c1c10407414403002d400c00f81d100f0355001d480201221805401800490700b1140f0a0708014002a0002020307119130904554460160491034001c41c555032501500c030b00c3c02c00c0c0800e801c4050344000100c000c01d00c10002035001c00346400900c4003245a4480c0f41124980c1c1d201901c0b040003904101e005010b19154401c0a00d500882090b2a0019039951061180c1680012000c03481100808020350105c1c0074040a800500b0072024016a50400082001400d000c16813109100d90144c0480c4d040b0b1941c00300c0c100d500150b020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 58093528 1106 58092422 58092439
    0x80c1e0307030206071404091416092114060f011a0405101101061707080c03010510030602070f0b0403080709060816080c0405030307201e 61
    0x21040640503812440c00190300074050f43d2a541c105401a550354905a290092361045400b5003075007180b00c0550504102660000c210618104011810004802c40c41e1811099060b0034200c600d100400210031480100a90301d40040241140030050794001e2410200c0c022400000f446503113218803402e500601c2400100c03040b10103851000d08548840c0130300c00c20035075020484503211001990303035900020722201c40281c2201c228100c1005400e9052074042118034000417121080d211703034900003c2c480c1e9500684800320803294005401340e110440c0b824011408560700304081c00078080301c2c0401c410950b2040c80c8900c03e0341c3c0b039201d00540c1354560a00300c5007510700306c42d00903582801038000c0c45d0950103503c0e0030303511079070302440036240c00d0700c0d000070034150380003408200c0368600c440d034440c0c00c002440700008600d110242c66520021922501c03600c0518008001c150264110 = true := by decide +kernel

theorem cover : BRFrame.Cov 57913672 58093528 := by
  have h0 := BRFrame.cov_init 57913672
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57913672 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 57913672 ≤ n) (h2 : n < 58093528) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
