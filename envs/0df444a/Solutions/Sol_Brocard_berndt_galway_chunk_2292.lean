-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2292
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:16:04.863476+00:00
-- url     : https://prove2.me/submissions/e7bf891a-9327-4478-badd-524eaa2d86df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 412050359 ≤ n < 412230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 412051609 1250 412050359 412050371
    0x608060d0204021209010c0516060915020a030917030f010b07060e1b040e061915050904030e030d0801050a050603071107140103062702031801111308030306090406 72
    0x155a2644a40d04895008006565400710712940304800d840c16101c644040d030030030300200758041c0510162008a00003075225000480d02da264600606a500000d55844001141001c0b614000e030008108a0800351408501d0780301a15100f01c15402c07950103100703815030034010b1110400303888010b1411102c15008440e00d410b05810b100f001048141c0d2040d01500c1003016581302d00c0c4510566202140c0212000c0281c00440400e054a991080b01d103005590507140d9040320303540c156480400c0300304000c0c0f464000c103615240401c400d42c400741d8040d03003ca005800b0b402920701e4100a40101440f80f441c0480c0d45514080104460407054015584035050120004201520a020760f902001404080300e07529540c0748010b0b0803042c4034908180c0000c2c01d040b00132444966001c071103540402d50000c0000e4003130103102c0c888000e4001520b0482d8031401c1c0c81a002219209001e074200300d01d8550142d590f1110440c40c0660143d465501c4200183c1061041096940c1d540c201240c4c0310360408004a4a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 412052859 1250 412051609 412051621
    0x307060225050c1305040b160219050c0901080d0c0609060e1912020c0619030209090709080c0a150c020103180c170a050d0c0507030602040b030f010605130608 70
    0x20918a0310180209540109942001d001001858403101d490540344c6181040d001d148010070741d4400c44025000c0c846540106081c24a2031040000c40b5849105841009000c4a4501044402c00200341c1c0d0740c2d444601101842d140c0501454014a4880700412101c848403c0203130000111000261620340d440e101c502c14055950410301903c03042e4004d40d5078000f84003440e5998a101060155140c0700d44001c1002175038000034041d056184000c3c60079003408602c407014180451100f00d200304258007441920526140c2e9503015000301c2a42d10780114203805c0c0081e0501d81f102c1e14581a01c5041001410003855048811404d4001240c1c680f901c1d92146d07500059002c2d1a804810905507010204581c05000982d00e802c2c05480c85801404d043e00c1d107074104103070788620580d000b4103150000681c01c50a6406000e40c684080c0c0300d9000e4508542c4d5a0312160101d0300709a105030510701c00041041520170074841110301412040c01d0260505003818096600e90701140100001c0c000f4800129507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 412054109 1250 412052859 412052887
    0x240108070f12020d02040903080a0f0614061c02160302120304080901201c0216080712060f05010b2808061306080a14330a020c0708010b1801050303070602 68
    0x1044c01e401802c00e01002d4028a00203020f42011a140300c4100d04c1d002c900161145070b80154011500c50540307064140109008010440c0d0060300c0d03c0d01e00401000320785800b01d0711400030b001ca441c0400314240c1c000e290ba0030080d0a000d04011007071504c2c401002080001001c800980711034140030b203030001303a0300006541031100888208000d1f00c588210070408074080c802ca640841801e020741e0030789001c00180c1440f0f8058806030700984000f900407141c1400b540c1e041400001038107008901c0810b00341410204801110801c0e00a41c601500020741c680f412001d03080b42013a4806e10800c40f418107206200010440307000030700114854040c40400914403542c540209002c0e260f800e05031048146035291202d4901d40700d05140200d402006020070110011040c040302081d050040c040240c0c4080c0074401f0102c4008100503000f582c24060301d11040300401120015010000c00007950802035410442c8420b2117440d1200280c9c2080d00611142c0c50100a444400750b02580240e111048420115 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 412055359 1250 412054109 412054129
    0xe01090c150e0303040e01050405071b03050901031a090121060f060806010e090a1e0b10030302011109060d0b040207170a0f0e0d020f0a08240108070f1202 68
    0xa0300c201540c190119504203150001c41d008001d64907404924240d00040c140c0701e0180e8801c00d02c590141d100100418206900181e50000c000e143c44000702070714000390359044403c4003003a00000d80c0403900036469605841039250004015031040c40001c18100091903a407014029030043d2030042040c284c00c03c0d180d290800c0c00381e6008030140310141310841c140000303140c80c3c4100c80d80b52140c00000280b004592103110300403005030300500804c41c050385507040800b0040d103240d05105c200c00b56a901080f0034070002801541c4c1c2c081c0035012245142002030954038840801300030401e040004003400d03a101d404a8000844131200031410520800005009024041c00502a1800c6001c20f50200c25040c1c0200040445c0b611510307140880e442e0100e9840f0f02e10320035580c109007840010409440c103902000814a401081c00940c0b80d201c031075090400301c260040c40030100015110040c40c06c501002140507244020080c04554038080060007004124462201d000a2010508080d034444003080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 412056609 1250 412055359 412055363
    0x80618030d060b09100f02060109052508060a0609050a030b0406060e1f06020106121e06110c010b06031b030a090203030711091320010201090b1512010606120e0109 72
    0x10000c0a6030f0341c040810702d40c03115801c64401c480700d008028055004920f5030381c044070140d005084c81d03800c1407c54070040c100602100e5810040701c00ca02008091680c41381d2202d41d00303594031140c0d41000c409101e1a0f07921a0400028000d17003602c04c2c4815121180322601f01e98018921480c1d50316582000700c01062039810924611141c001004170140c121042d003440d4102006800f14038603540c0c1d008a00b200c0d02d50240c81508000c9120f14800300381c141c0d0440c000d0161440160840900c1c1d50395613001c070b0f040800a0b031132400c070114000701816407c0c0f00340c1941060036903032680303103251141d07940b4200c0700c0e001d92440110700c0220100b6240c00d180e5200086d41d5501504803540c4150314105040801c001d07480301f45c840c0c0c1c59440010011307004034100a403815408600c040c0c00f1000f1555030138101021480681c110365959900f500481e841151240c00351260803100380004e24550107000084100074002e0615a0400c0780c10403c25030f0100b1840341c1c0d2948407800150340e589141190b40904110040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 412057859 1250 412056609 412056611
    0xf0a24030605030a08090a060f090620010f05010815271204080307060506040912050307050d0906090203010e0303040b040b1302100306051c0804090b0a15051c06080618030d 76
    0x208820041a6002040144407c41d41603440c296a2141194072500708405007000035084041001610300984200140e5554401c12003c140c1100304042c2c212003104400388102e5448100411a800c010301000d14009003007030100307403245064002d140b01c0801036050006400c0c9658403001d8071a8041c40640c40c64a2859030769661035540b0055207603290416402030714480d107009d0100f01249000d200e40010550711025412506035a1a829203554000400a9061080401036802c954000d03119101520303210780f000089111b03039801418211600700604c40c1c81076100f0000e00002c102e0400c5e80b1903200350711a5a003400ca81d920320a844404005500081d00801c031f0251107403115070150004801c4d200c081e15484088804081175003c802c440d1100580003074001c010600000360b040e00070403007541c0050404001c80daa01c4060720040340e41d10038884001030300420340c000081c001da0720000c090b4403150418400c840c14090601d4851a000d0b1000d40c840c4a40d0400c4041c8010a0007921040442d00c04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 412059109 1250 412057859 412057873
    0x190306020304061407020d0c0302010e0f030c10180605091009030c030e0a0b07060e010216080408010614090a020703030b0a0603150911030c0a020c0a060507020f0a2403060503 77
    0x2505101942054030115182410714055006880c810304415119481c50750040040700a165000e80d540c113540c2d40300342d0031035403a9100c110a0700d10402040a010080d00c0003550780f28064440300f801c0086032004410b81a0400c00f501000490000c0d8000340143c000400041c0d91b150300750300728079000201880070569030a20002d40f00f41508802c0c110b100074042c0d1540d00380f1440071760411200d80e0b401d02a8010110341440500c02007001e17980111020700e1010001403400c05216407507404107242020480d4100320000302407003600301c28080c10780142030491880400368100c10010720040001440b5003141c540c00315141e400d241c4213809c080c44450000d042c038480d850311414010041c1c941030402c0d048032026803000241c904601c0c0301c1c1c05903200880200130b08588903001d01d0100d07039001c82910011841054141c4070703d07582c0d2202c404010149520365660b558024414812118800e1402600c81c02a241c0304009090800000710036048000100480803502c142058000304015044030340c00d44103601e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 412060359 1250 412059109 412059113
    0x40305060a05041b05090a02130b0f13060f0e04020307050919050102010e060405070302100215070201020d05060d05070b1e0412020f06030103050d051606021201090c0c020d111903 79
    0x540080d00a50144d840701540d40280040340080c00582d10407981c05c08424030024020030b00d142d000e0080500b0008400f0341c83c81e80c51820b9080c07074010709600c41150100050800d040d607920141100240060b050a5440f0014260054074507140805800e0061f03800000044841c1c0c4141c00700c0711032010041201440402c0c80d6160500b00d8014051980550b10344002c0304218600016041d1045034400020404142950700b03101c81016418080401d61040003800c0b0000300c04401079034441d4485030f0005881d046500c49000c00e8a90280140340209420140100440d8001c038540c400e603155000a1980c411441c840d110141001e485c20440507200030401141002003102c0e59145540225155140f001c112803c00400d0300c402e21000341940e1009041c82540f501a10150204c003902c800703003036060070003500c036141031303074080b4000080a1043c0300040c40008030500c20307a0345101c510729010303501005075804203580ca000c245000c0c1803244810212a0180c0d20140450010045601c16007401c8e40d0381c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 412061609 1250 412060359 412060361
    0x4080405041b02190c05040902040b090406291008090c040906020924040e04020409080706050402010906031506030519110406110d0504050f030a0b09100e0d0206011a040305060a 78
    0x40d60b800d0005000e4140102050035541c2c1d9000010b03604a000c040310f01d4a443c0400c0700501503d0412600035031589070b059060365501021601c00d81c064100420f82003030382807203080c5104444040c2000955446d240c0d90443e03c0340209120242c0181c1001401500c1e0303001118a0b240e000080c4e294003c0c01c05020004000c103580103003051030410349020103401048085807103d11a504480d2072a01c101f48800c0001940c598021500140090000500780859480c2d42565a100c0b000940317603c0e480f4814403046503070001c00b03500101100c2c541080200d40d003d9a0a0011200e4400c000c01c158982c404104a00440b041c1a10491f00009040120481d0781c0c5048076079400c45c3c0b0514001c5280003244604101c0003050b50703203c02d0a995500c0e803402d0f0a18082043d582565480c0c40d800d481107403541e5001881c003190300c81c01920014018000501d03029a00070594902c0c40d0b820086800101c09410856000a54130703040d100c0111111942ca1600c10011540740030780d500262480c0b00d0300e0103018040101d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 412062859 1250 412061609 412061651
    0x902060c0d090e06031903120203010f0e1f05150c010e070f060504080601031203020702040f0e010c0201020702210307170a03060801051023030f15010806040512030408040504 77
    0x840d01c070981c92941c1d403141d0f0500301e2011951541c164005d581184000300c42ca54215551502c03904141d01110b00038080c1ca0100c1e00309070003542e01211241070a105040400782c0d899407000d1044042c410306812801e10490782000791184600810341c2403916103501c4081015a80c600030800c0003041031040c00c001c2c06503140c00900c0381d00d030000d0981c0d0010030b0749407103001290155081200140901d901c2c507520980742981d860381d00070030141c1c2440f0070f4005903110300a00302001d030440c60210341c40c1807801032642124a1114090709681c030402c8440d0050711451001401c0c06610721022074150342e070031030440c110b100b800002007980141c84410b541c42d95a080141074050403640c1c0820425891301ca105088a1081e1000010024501d00030003400c3d6202e5046d41c80d50650240781d1000c1d0382000302103032a22158890741c16050f04442d0402c50892051103840d401820558024191800c0a8440b240c40d00000e28403080d0031000040001c0501c100c4000b110000c0030081c0c400c03c5032904c2d4520010305006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 412064109 1250 412062859 412062883
    0x12050c0304020d1b270501170307110a09150f06180e070e0607031e03020c03090f031c170a141503011b02030a090f050105161401050718060201061406030403030902060c 74
    0xc641800801d604680120300192340e609880114a05140760312240d00790448500c4070b9a01c184203900c0851075404078064500e14a0f1810415154075003401500842c06100c2d412080402c12b1400d4002c1ca029043e2019100301c8801143c4c0b851951030b095000c070b41000181048581003000000d50b02c0800d51b00084070400e4030409000d641c0c0d400718241080341a0310030380c64100f181e6803051000a4003031412000084d1407480050442e8410260525034004d03009401500101103010340314481810411a40f540307038017103580002040041c03c01c0301d040d0902400a80b102e050064165080b000c103460961000c501e541c01d2a03182000d04403e810300a5803980a4000640001c40000700018040c82858030142a42c10503110741d4200344001ca0b01002d24545100269100282010306901307070002031045034040c03503142d540d401862040c1d039a0a00f0144031684010210780c941042040408841c2d414902d100c081101c00d955a501c450500300d000e000f02d90800381d03210308000ba0103080c0d00fa00080d5032030101c0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 412065359 1250 412064109 412064111
    0x1203020c0d03050904051305010c030b01080105030c01171b12091902221104151b0317130212240c0406111c12050c0304020d1b27 57
    0x115900d414441c0900c4103100040114000740503100842c603003600450345c0300301189800d140b40a400d03100e5070301351290001d603e4007196541124070b440303580c421075940c05001d01358000c2911081503800240308c0000440c0d403061a606000108000290044c2010030081028070129119030f0442c1d0b0501c0343d11000d5550030914450f01c8001400c202038020340103603a54005101140d140c200b14400c07480d03084030602010b03042d6a03a41040c00c1d011000009000540004400841c08400c607079000740084684660b91105d4400f0604d09100281d440038600320440006500d08959442d500d4080384034064444000752302450030b4203002103202001a15800d0010b154031803848000005c0c0920002000c2134900c100c0a02080009018050180d154240f4060708602200c41c2c0c180c06605003c2c15121600003000003075034020341d04034100d055000342d0760002d1941400c2032960500d82d0001c0ca8846914100601c410444000c203020b400e103042000300180001d0075500001c40303800511110b40710400407100315907 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 412066609 1250 412065359 412065373
    0x303120612160906050d150e010b120d0e030616050d110d090303050a020a02060a0b06070b01150917060a200a0c02040e01092019080d12180b04050a0c120302 69
    0x5403801305001503e80390000421f001b8005261940c201038031003403c58014640d20b07030760044442c0d100d00c4105c0140000d000c0180000c002e80c80c00040046215280007031081e4400c1c8107010010218640800c13003614035041c030035a20342d00d80b1140b60141c030181303604088802d40495005030195640d0401c100d110300c20365003004556a0a0346400407801050106001a808800024046c091070b500c00301503842c00411450808265a03100d145000c6c2c260072170b07002c2c0d038107001d04105d056402001c100c0241c41c0a25540903007907940103810b69141d80c02000c1e10352480c0c40748291041065030042c1142c403092a803114a0382c480303620202403c0c1541d001c00407801180b4005400e41000018842c1910450340f0180000e100c015501c110500c4240e20300c00d0a9100181e00344e44106035900c42c55100007048404090144040381c2000030b0701c8004460892240c10b400c0406680b0320f034403200c801000480c2e000304458141d4455050140c034107141c2407030003031402d401703404003041103405a210700300d2a6110f6421120710f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 412067859 1250 412066609 412066619
    0x507030f02040803040302060708041a0c28080d060e01080c031606080103020d0c051305040b1305060a0c0311030903040512071a07030c050a1518020303120612160906 73
    0x481c460b600c40c01d4401d4000307010503c0185818401405518001e01c03096013003036141e03907240c800c035030000c0149c912403a40000c02c119021014032100c0b0307850549080740c001e04000d0400300c1d041481c0d880002032481400158103120001d6580c00b49000d07000381d43e5040307801c0d80c603200115a2600c6c282d0300140300c0e208000603054580b03099103124007a0340c0035030b43d2806943d03e19402c3c407111080c070030720890b01200400030102d415141c44d0410f01e18906035540c0030543c0d090904041741100000390a200080b501940b05d0f102182c4c000901c00d40000c01c1001c0000d2012072018200d00600710b0600c46100c030080041402448a000405402030b6003003100c20b5103d458200f050140d5406540c49144201d40300203e0503100316105001803d407040c024100711075034070b005680b0343d0704041205030202d4400d03a01e80000070500710144a030b41075040c50544142541c0c03000381c000075620301501c2100d68114940c00f0018080d91200c00c03c40031804000402c80d040401c01c5040352880d900c5900480f10028500500010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 412069109 1250 412067859 412067861
    0x907050d05091e12040603050c1c1e090c060e0301021e0c011415040b060c150412020a1707030c02060705071802190e0120030301030209060d08031f0f08010507030f 72
    0x159a03c5414a400e142c90324101b81500904001070068580000074841c074440e90000d891804070200c00c180000a424281c055030210719403454103810f001c0c500d002001400110005980c0060341c5441c00c0a4007003104500000740079125514602c51400c5115841c8500c58522038064220400244000d0089001c0c194610060100444036861a801e1030080c1e00c807641001d07400b80c036080300e0280540e4540700c080f4620f2341ca8000080c0360390807007010140800c401e1101c007401704c41c2b0002561010b4660305c41d6a0f21080c0224003e08862000301e81b00150110030180039040e100e071001d9001d81600d03103036003150511680390711f181e109880e004041000f042c0040e010a20885400c40a00540d148034880c8030241200c060210600a40c103115501032503414041d40402050400c0400d0303001144e0700c0d81580f0500c0001c0301c0190002d0301455043c203103800010140720039641d2210501420f44100e80e214060040c1d490051f601c40e840c0c03004c01c0c58020551b400107400641c440c24141c1c50901584920305034400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 412070359 1250 412069109 412069123
    0x2e0f0203090d1713020604030611090f370f120309120206070303200d09152007030c0b0a09060e0a26070503180109060309020f0907050d05091e 63
    0xd60081a4200001d01c25504c0e90b4040032050300141c140b508003510b0b82c0d104d80480c0c41c41c3c40d164000b400c010900c03250920300703101d034405150001c3e50a83e82c9032028050040310a000005100710f9005030283d010030300a48052804002c1c540d039020004801d58070000a602521800360540008050070000305440611454a0b2810707540540190702d0f1a0550718102d0050148181e5190560b14440300c03040f01443d01c1f0090f240d021400d11000174680c0580c0b03041090b605800c0101507543c1d003031000d014107881c210007404400032800700419035641e19500d41211850503d50340100585540402d000100044e07138080c980b00e5200e410200103030340c0d8510718150b503120000401084081142c003940e0ba1101ea03d50721356980d1a400941c2801c0c0f00d010b81c0e425040d40c005005a008400070f5025040d000d41c0c3c4211660b00400300ca0a00301f146081c50b40100e84580500144240030f013034424040340343d25124900b1503c080682150070025410459903450315216031450046c50100c1e02e001c94101c9200c0420321f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 412071609 1250 412070359 412070387
    0xa0c022b0201030209060904090b0a140c0d0216080f191d0f0a030510150e07091e090509061006050a090302040b031e0705011806022e0f0203090d 64
    0x2200d40540d90046029501203420f40e078101c01c0900000702e036a240c40c0180c50000c2c0c070800341c1240501c0c003141035500300e4001010613000402010f0622444420440840b8410f41801001503542c1c2003500b001980106564070091170100002061030110514402608440304450a10403100d800c0b03810858810034201110100206070a90502c030303900c0c28440d800c2c0c0b03261018210842c40c550b651501401c2814800c24000b000341c940f054825100c1103445068040e00094409843c14106584014030640450282443c00c0c9540c00342440d241164000490040640700801c0c8268500040750036100c00082e01c002c2d00c44900f100700810384a014070103a58010b141c950b1030b101034501d9602008040c0401881041d01802a1440c01185c200d01b103880e40724448606004000b05494800010860804004c608a10100c60b6109020a90307000c2420091340c021510320401001d981200c0ba108030320300340c0c1e01601d01c5240ca0348007810344582d0b8015502c2800303540f042e00c09003282404143d4a240402c01d903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 412072859 1250 412071609 412071679
    0xf01050301031a10080307050f150f0403030e0115080109020906010305070c080f040305031207020606030c060406110f010f06060206150d0311120301090504051614010e030a020301020a0c02 83
    0x1050200d02040b110b002c2d40101303410a5810f81c1556891040c0c103590103400305440399002000c1c220418002041102c980c40c4c140f003010403540c40d003420f02d1420044050801000c00d0344540101900341000d4101550011002e45c03006030301550703034408a00801d21108120301960000f80000c00395030003442600d120b40e987e900d5068400015958602050744207184901e07d00346c05010101c0030a10800c040c081d4481090180b06590414a40281c40d04074000d20141c4280c1c071100480c6030b6604c4081c00d982c1200c202d410610800174143c0c5040d4208061940480b0203503107000404454a81140c11480c00c45080e40c0950303040c2c1d22240c5107000160580c0d030415410803003106910780040c0c0300700c00d815400051075007a940c0107120b4100412455100303030312401c0440d45034014801480824084940f80c20300e01d10310841202e01d40495800305c40345008142d070500c8a6060780c800d081c1c605208914150b81e00a00031075030b607090b811018241c008100303130030380c003a58029000103c232419a010b500509514010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 412074109 1250 412072859 412072883
    0x1050906010b0a02070803040b0c0712020f040b1f0201020a030f0b03150408070605040507090609020306011e020309060409140907030b0a0c03020403050d11060907050108011806081b0f0105030103 86
    0x640b2a5240e0018246004500c1003070300000b6a06414005803019041013000c0035a40d003442c2c08a203140081e95000f400c0c820142d0009100140d840e02080c140e000010390b030110300101c800d00000c00702411019006001d01404046401c0c0c1c0b503040d4000c0841c8904e07611300f0004450180d07001000c40c2da45a44064150307000140440c034440c3c03101e022590091050300b03014948025a40e03540140c400a49049032503601c890f00038030001d00e41c0d0192802800c1c00300c10441c11844e00c0800240340f07a0000d0410814100c00808000740c6900c2803003141c803451760151400d03540311341e60807403a4010085004090b01c2d0908600101c1c0c41d147c00810001c0032660041070056031a2640e6000d14000c0c400c071498002030541c208400030004030103101c1011198415243e8848010b00071821604010005101244942010b003092003140e8224521a064480092070020307500e5036a640d60b00100b0341a00300c004140f040010398007500ba00c0c0701032030f2000002510910703904e0401d20010b460500080c00000c11686000e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 412075359 1250 412074109 412074119
    0xd0c08030907050a1701060605030c1206010e100c1103070803030f221a060f03030421140a03181d042112060b07030f0804050309090f01170105090601 66
    0x8010356001151036041e90207040da540002002c0250990055580d6005024000c804007001e00c01c00004080504000b4594034103803060031028894480b00b03030b01d110343c0c11000c240282d01c1100042200e08001d42205406641070300080c0800b0704083c070494240d20820240b5403e03040201300c1a0840f90018003d60541d1130305030074a0001d1900034020340450038410344120840300016000440c8601600024014024120007407060340801004240241311501d00d881442d1000800c0f10221b417402043e0442c0d015280101709455100f038a0041c16107810041c0318142c400020407544c9080b03103c0d445842048441404490741c1d0b0381140706042004400e294141c401104140d141c0358024440c3c41c0340080d01200c11004104086070f15002d0001440790308608000c9030707443c400d0202611889174818100706c660343d001030405142e10030100c01c00c0752510112701000f0b41001544c0d601640104480d20700d1924072000b862040d004d2141c107040e5182110303c2001c008040c458103000d82e94200142c04039031300300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 412076609 1250 412075359 412075373
    0x20c01050c1213051f0c0e0d020a1203020106050d08091e1008040201112b020c030d030c0c08030708061008100611120f031506030108072310020c09090d0c 68
    0xc8001da50304d0041080000110490109088201a503684c00003403080c2d050000507c403107400000316000b81c08a0650501603a662013039201140c0b881010710007103900d680b904034003500c615404540c000ca64038401d001000a2000585807824027230360413505440c00c4c21038042030540d02403106500081d405103035002d503d1003221280e60050042c100319a11023507541d80c0030728000781c8001d919580000c8001500c00014441903010480c1540e100500d80c500c1c8001c0082d403503584032986170042c1585c031380c1c45210660043c2829268503410200c400d0316441d080340043c0500100301c540c54031928012081c1c084d01e47c01501e9003030103004400705440c02281008001d9031280860100c03008035220b5412050ba600f0110310003014207615080c0c00580f80d050480f51090910741c45081188500da090005000350300002424104441002c1a005070403195141100d03001503690300516080070351141040110758000032034441c02002682c410750143d43d1444030350380710005a94a200064030055500000c601a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 412077859 1250 412076609 412076641
    0xf09020d020f0705060702060115050301150e03030408060406051311040f0209040e0106050a0506070827040606020309090f1303110106090608070e0a02040e070c050c04020d020c01050c12 82
    0x1012100516144184000c1070b51900311010850399580b007501048102030b814441d09005242e1030030101d2280c10511005070907030005000b140c030a1500002480d0401e031044000403010300000d015a50341e2500c40c80d100391a0002210161401801c25022942800000d520f03560040d40001d119050791081e4001c00010b44010320120034016002e0000140c0c0356168403032001d1610500000054141c500b03002e001100001d5440540300755810721603840400e25007021603011116061904a0858182e034412034880940c00301c07a42c002d454100d012802c1500040146408101150800000e644054000054041c00c0300c203612581c4a2904040010780140c0c0b541040b04120300022031601d8403640301170100c030340a40c00008141e000310010055452410078130341c0c00074003507a015450b01c0d0810807a45201140030380701104000c0e001d00e42c6010311a06016410020300018025903803440f003e0b03000c10180d009032500301d80952821000c200c440d09208200c40c44004a810221600d85e28202c0300d4401c40340b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 412079109 1250 412077859 412077877
    0x307020109171b1c2a060b030c0a060f050702011710030b0a090c0302152106010207050a080c0103050903040e0f040b15030604120e03030d0b031203010f0902 69
    0x1d25010304100052100498003a1056403204240e2030301103441552004980102a0081c2504102c0040864200003040120240c01c142003030303441c4c20101142c0201c0d841014500103290800300c1d009804010b4150080c0c50040012001c45200110001c10000350b1852072040d440810300070b0421032a19030059010782907042c01410402c2824044a080100c1d24000300c824040d0400340074001c1c41001030340c042c4540c204104201c00c00c04032000f5500d43c80100781a010103881904580111014034021030202d40002c03008080ca01106480040c0d4080640070545650340135009090021465003400100a812941c411000f0039920242d000150020400030b024034030307640400c00c0040740c0c1200d814095401018640131406007031806040c1281505001b4200540029001f605500c9540c0d0001d580b50300250003c02d00c0c500030389440001c1c0c0d080194010034a030036010100e054510860160300032241e04805a09031100501c40031002e030701501c001d0062800442c21041c2c00d0100d550b8540c0a041d2007c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 412080359 1250 412079109 412079111
    0x1030b09063321011e030f081b07150c150f021e0a090929030106150c06060b0c030720090103150b01030e100504020a15020d1e0c0803070201 62
    0x7010780070700400740e0141c10103414507024443c5512021070900302c000d0040c181580c00304081c102142a0b2505103c09100141c01c2c2d040001c042c806004541e801c80f0341c5030341c1c9a2006032200a40860a40d1124220311542440b400c80250351100c4070701460800c011540d000300049004440107003400c0003000600410311240390300788900e881e01c7c0d0004e07115000d00d400b244147d54842d245840020701d0304031942c10045400d400c007c0411101000c140100c0130b41460740c51140c5400051002090041129500c0105040b695210141c000c41c3c0081210403000d01806007440420345071081900c0601c101c84104060b035008120210109400005040406480103c03004802ca80240001e5000310280c2099413856001410413006403000d2007201d1480c0703002e090038061002c00d009055217070806071395000f4110346c03a0701c00602196102c1100d90050304040c88210841c900c241c01c0259208280030008011580003131414800c10042c000358664001e0380d0f504d800d860149039841031110740002d48000159 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 412081609 1250 412080359 412080439
    0x50909040809030706090918020d031d040f0608011d0c1306150503060111060408032406030a0b01090e01030203060a020f1621091211010516050a0201030b0906 70
    0x95a81030000c2d20017400250380e0814010308000d07411003110520840c2c08807074440d480b13024006854061500001d1909410715504680a4040300000750344e45007200d9502600c1d154040e8441c03002540142d06030b56410008200c244075083ca41c071a04054001c0c0b83c8041e5004440304140c0d0b150405c0000400b800000c404a240d5607181c1c40d18011010381e0800e140403500c00300801071156409011041903000d00001880075017020789800c8407510010b00400b101d451100b4208a80014200200010b40700160400e42d89191846061b001000d5801c615070009010707010001c0c07c2d0386480d105605813a00200030f82010384504602c500203502c401e0b50008004410b02c0131a6503010302000100441c3d01035440e001c803200703c005401c4400303116004004180714020409000f41c06402c040684501d07400303510380c030021008400507500790007019819055006140380c40800c003e4041540401c1078400c2e00c060007803103885420007210310804c480094100035020321444051001700d40000043c40c0e498041101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 412082859 1250 412081609 412081627
    0x503060a032d0b0103032c27090318030a0b0c07021c050f010f0c08040f0212061003050d08041203050402190305070e2203030f060e0a0c0207090c0509090408 69
    0x2a2031290b540581c1c003540440e0040090541124100c0c22000004810541520144c403492580c2010040038502490281c500d4800000904d0010348207100a078402c4106403504124840d52603108407910b8103244102441203600d410001208101a580007900200750f0390f84072180305a90704155001c1c1da01c051041103900e044118812a1501c4d6800340b0007600d0a40a002c019909544180f0b0326941490310b001e000301030407540001101e8026030b019a035950410303407500000e66550340500450f0407500035182401041c21814984400709e07803080301913900c4d45d12580c0d006d40362000116005002044020040c00680740b080e40065030007403004142c00b0928107210030071602070040d338001b00c48a610800703051100500549459600c1001a11f107040d0070f4402000001c140064000010285920340006070304a01403031b0030100c044d05201400131030518041c4044400b030710703652060300c01602445078040307050801c9008400324140243c0b5802d00c1d004d142410b2100380d1800610964454106016200d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 412084109 1250 412082859 412082933
    0x17011b0309020f061c0c1e110a0b1003150603030801031b080d020a11040e0c0111070503161e0b160807051c020f0303040308010303110c0d06020a020d0503060a03 71
    0xa11800e030b103244110003218484a0303804442c3d0310540c04081c410b055081c3d964118107c00084040c680a14040d003000700340201c410702d0072001e03840c010302e501d02ca0010805102e40d6609002c00702c0303002d11080c11554110388019800c031a214000070f80012090001800404d200c0c020032603548d4003826200e410785540320040b0b42080c4c45031072840d005801c0780b0804000d2100700080030349580c4d0122010407445a22121890380c901e907480030b0f00d0602520b04103207649402c09110250080c64050b080d1003010305040540c269901503805140130785000c0d01004410300703a03007070b07001da054450328010380f481d118840240031194102d4800c210384c0c5000400804000510600001ca201b0600904040c004648020068244400f9200c4c15009600610800c40806d40c404809230450b60181442e80c121014507801ca810034220014070f41d0003982c0c03482407d0800c6202d900522261600380d095915030f000c04507089481d0300c0290381403603004400c1c440a0002c071300c05224000e05814070403e6620440c446941c141c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 412085359 1250 412084109 412084117
    0x403170a05120f0105120c061803070305010614040f0506010c170c101b0c0809012f0d0f030204081f1d010519020304120c05240117011b0309020f06 65
    0x110850b4044004011601b040c6168014003640ca001619008000303001003015802501e04035980f040c00c14aa04106440601070300001d503030040001d2111a0300c40c402c0d2800400c040d88141e000e245440e6100c01509198400c5602409050792003110308900b0b0384801500103001650b100ba5030a0411042d403826408014040201d010040082449400a880f104a1000085095050210800810001800b8030782103468001090900c0b20070f107500c404c002103d81440e03801c600340020442040d0501103900080c05045048285c0d03440f03a002e04e40305021010ba000301c4c030030400103901c030701000312502d8001c4406040c50724040b82c00082c990500141c1d40700680743c0c040806216550b5405021240e445581c1c1e10200f5480381c00150300d581010756800c0000045102c5850030096107801303117820442c0c02d04c80c1c540090740b5140c240d10155211003001100d1502031107507a208100e11200414051818000d00050300410310000c601080280720a6015201401c0103e07448030040c40799114540e84c80000d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 412086609 1250 412085359 412085371
    0x303020f121501030c090e090309040603060f060618090917130e0c12010b031003060f02121803030c0a020c0a09020d0b01080f010b0f090406170d03020403170a0512 72
    0xc40024240042940320750160b0106460415091000050074160402c0506080f10300c81d4511800c16556190920300354040c403048194080e041100c00030500003142c000d96042c1003002401c000700b80c0d850009a03521368031001505080e100b1800100b100450700d500c100c0b000c42c0120802081140d20040102681c0d101c8031082c0ca8000008405020003400e85400542c0a500e1043c83d41c54400e402d2103200791140144502c1444940000000d400f088101c0c0d98070300250744c860000d2005045003d4294041d402c07240d02d0b099440c2200d0700081d030220f072280981c0b60140c0b251006c0c61940c0c0341c1204400391a40040c0d6098207522034150800d00588680d040c0c1d07802080032050041e21104041d8421054680c00307071300c0b10304000d024801d01050f9054951064110b56000d403030240c1d80c0c0d560007261705543c05a0b030385c2c0c0d503400b5140c03036000135580d8010519102e020800030305480044206407000d904902690002401e4070341c4010084106000d070500402d5400e2443c200642081901808030040090444407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 412087859 1250 412086609 412086637
    0xe060f03210c010f240602010c080c07020303070203011a19030f02010f09080d031d06280902060f0703080108160306110c1f0b0102071d0604110c07031e030e0d0303020f 74
    0x45100d8035100802d00c082e061b144000e002c144c0290750300401e0150050a0b0001686001a0030380441d9002c10441d603115034090000e0050050307658200d0004001c9410141c0a140e224401440b03100c450072410382a03943c4201c4d03408603c90300340c00440f6040c1c401055002401089000419a90010058900c0013162540e0102d46000c5003180410310044040c0d40d00d05580c01031007404000340c1e1410000c0003940324941d00030145002d000c0400050720039004080d402400019803030304c035510614000c0100600949410815982e524002039a900c0504071007584a084000b0610004060350070801e960030b03602d09240c0c10010101c1b0641d0908042d40040183c400603209800c6102c0e0807030148440002090000c2c0000c5490140104180714401c0301c040541c420601c00124280d44a50002100050b1880b019490b0885000c215a44840c2c2d4007095510040b40081c007814144290214032946034581d481c141314803005e006002c00a55880c00843c141902409207202005054018011581071860 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 412089109 1250 412087859 412087901
    0x130503041214100b060d2007050f0d0c02010c0611040504110d0c0806061e071202031c02040b04150c050d200a210e0a0e060f03210c010f 60
    0x8011843c0c4440d070200c0c0702c045400d01003858441c4c0e403210255001c1d18008400480c0c042800b880c40c500074450a03541c14818203010403c101030060005103242d48061300701c221100c041100d44165400007503000000c0c00611012101000140135400c1038001c200d10400b41410252682c0010b4255242d96401042000d00400d04c0003002469020700c481186490600c1440790819a000c0f41c0148078003e000680d050003401d00303094100380f100407030783c440d50040a801c800e400350240083d2698007440101103550141d5003c5034800113244211012520f031041000e01d0f280c60012030903102c1c001408c20038280000448000c01086040c0080d082d05690f568a0400e65201c0c9005810b5030116420841c00310b501080900d80003810060b1003800b02000c0c0c01100c8140200681d04440440e03443d64000d402c0444568000ba50b00009888940100c4080380d402040705503820905039554030f880c090314011f4907052030211001800c04000d040041c3c003880040751241c611011a0155004ca0200d0809502546 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 412090359 1250 412089109 412089143
    0x2060d0e0c1815120a06050106080c1603030506030c040e03030106090b03090c120f010903230a0c02040203060d050703050f0d02061303050a2a06231305030412 70
    0x88403088140108071428070b051031181c510054070240050181d010f80c00b4041000070705540d0040400c100c10410402c0703851040161a107140035140c04c4c411503011401030070102d0070030140b001c11740f650240501c814000554403070f1000c03800b60001420641c2c05005403c0315081c03503255401016200d0a400c00219039a52500000034a104127079440429441018414443c0c800408100304a500030200c0751981d80c5040c2c420b10038240303c0c00c07090409143d803a01e0514820180c000c100400070450405161a102c5222215141d20344940e0b03074a00006070100e0050801490250701543c2c00ca0000b0b000c1c50301c0d40d00ba5942d41d500e081e400f0340003541c0d40d6004031038042c0100400c0204604103d00c074400360440317040001200288990745000201404408201654140d120f056204140300f00a07880c60540440c0c141281441c030100003065464078248528103400310082d070f08081d00304c8900c000158143e80c0b5011a03014417920030340210741c00d01003004002040c41016401c0b4016074050b07030034080f54a42d04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 412091609 1250 412090359 412090363
    0x50405091f080a1703070201110315040c0f020a14010605031f05060609030304060302160c0e09210d05040203010605060307090f050a141c17040305100b0303160501020702060d0e 78
    0x20b68402c1d801039000505010004d0384592041c0e0080000c00d040c9603c0b521122030607809012a9003c09210520200803c4200165000301d03841d05030099404001c0743c0b14030b04048602003003d94170351026a0180d20500e0005604000743c00140c0350075000001c07100e80328030020b42442003044480c41404049c041070b00600ca250310a880e0480003c4994525054100012a40303d014901c2070f10281a4081026010010f094410910a9038000b0381c10381d0868584401841020041d60311815a204102200010b01e00740c02e6034440b40140305049034186002c1091240241800520498042d503e80600080b661202030107940280600e031280302d070175802c00445501020150740118458911503108001440e2a1904141030351810740b02607030059400301c00c04240c0a00d48034001d0050020710355882440c44400046c100740c034030980a4402c6480d0444082d802ea40b031485446605800401807a81902110f00f42c21142609c0b4000250610300b090f00001e03034640141e40c000b0369264a0750101d602440d01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 412092859 1250 412091609 412091671
    0x601171017060103020a05060706090204090614072c0d0b07020106060809070b04090236040b09010f050f13060b0d230711010609061d011a1905040509 66
    0x401c0010511580355400080d00b00000303121340c5001d0440010000705000454005603200d680141c4144030f00742d4903280540c002c0c44c0d107214034807100280c0404280b00e1480b5503407110b22054a020422000098900d0300b05040600c03040d1281d0103c041112100055008507449101e0140c036000022641d29202000d080030800a086050070b030801d203810321030321342c4220a6805a4100240058491f901020f51040148401c00c3e082d60007070a90203107105400130341550345801c0301e069030b050001c40e14900501110230420f0083d9001903815200520803400c0c007641d07070500305000503e408101101e500d144421210f154011808004001800c21070703801c414000c0b8400c01402891816080c600a00c92050031500a4180c4040242140301c44040c81002d401c0030340600901e540810206070317100c4406038082c621000700301c108444880005580301000d080300002003070118a6500e4611010349003d01360002c1c400c0c0d40306102c02484041130781c4d182c0c0c00c2014410703809030403190501040b0381718500c0c0c4028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 412094109 1250 412092859 412092899
    0x51203070203010f0e012703030b0a0b0d05150d020603060409050c19140d03120c03020903070f0317030603060c031911120109110a0c02030109050d051c061d06011710 73
    0x20343c03400c001e00c014170102016800d11713816289c000303101080703135001916503825030f40030148000c0c02055a8200c0d0140d50320580c0035100e58918499068a8001400070702d810103030000c1d512940500c00121a4182034020031050f41c03144054402c51004c000021382e038003000c60000d0039070a0014005201c07414000010091420045901342d00000e03450384c004061514141d8020b0459854850340c910740d60183d01520842140202541c0a807521110403241640d00c0707101c1680c0c5e61100c9214038140802c080c00322070040d04c0c064013a015950b51204800c0141c1d0000c0d01d06000401040583c41240c915031240c404000c21102c0300c030f56543c0a003400c403040014181c00c2140c0c100c0c03030001c1d000e403001000300865403c8405030610840e000d040340000f034014103084401801a026051850305840d6110006207884030100407864610700745c034010036040f29254001d02e10504481c40c00d5404201c80d107031400d90300880c1407606140088611504105012040d503200c140d03090600703000c1c0007284c8042103c640c0d82d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 412095359 1250 412094109 412094141
    0x50a02090d06180203060106180f030809061b031602010216080c0f01170a0203041203020405030604060f0905071e06080c03013005070e06030610051203070203010f0e01 74
    0x40800400070314466201c290042c9255070b26140e40751003801c2c050004001c3d0780c000303054420540c1e4503800540302d81610a42d041100b020408049403800e50604d090080c0c03504184414140b0003902e0038071210b1391102c5003030002e0720300d28044030404138410002020454641108414058a1440060300e060307500140c851b01da4010f400300784120100019210200d200480b00700d103090f19450f005843c02d034074202041002d01c1c1c0d024100281019039800031809140f01d03415102c411496a441101203014234001c041c0c2c15081440402d01050280e00081102c10209000003841c0081e07a80d0245044415404146c0d1086482d0050300d100190f000407000614850824404515002c59400101d2005000300c4110f180c1c4002052070b03026040c0815401074041c0c881994540d103540c140b0705d550750840d20800040125010010b841403c0100e0030600030b03080d404604035a1802c1200300000171004d10003400107403200307224800c05a5403d0185102c02510b00e2400101c4840d80701c415820b541034aa601d800070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 412096609 1250 412095359 412095367
    0x17160501020d0f090b220c03120e15040527090706110c031e030705120c06070e06090d03051e120a020408030708090a0f08060a0515062506020309060703050a02 70
    0xb050010340c1c000d52088805102498070b03d6030002c11955561b002c031001c0c140703211004020003044034100c002c500d20989602c4a00303001d0a02c07402c0200c10602034140611841013800b080005040c080780171040c01803d403281c0780d0700c00d42e0030151503c0b030317441100c100070181d11581c4204081034214141520804210015040b10a121004640d0302d0107001100c0901c41401c0021420044040c808e46030303800e41c02000d0b0b506075511f640c3c020354140c0000c0d016074a0ba0041c0004a83c07050700880c8501d01000002d8842c90408201004000c000d95000380d040d030034020b0030480300754088003801001584042d00340d861a202d00c0007964460300680300030551100e0303d104000c28002e2204c00015690640c3e4408a11582c440060021230309422542d44042a800881040401c840d003000c0b400601c24404560b0030000d17a40c0d500740740020120403010b51b80e0825410841c0080c01c646811200c45c3e0200d40300e03541c48961110f940e925049034421550352501c1e07000b0300300b4043c081d0345c1030041e6500401144425414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 412097859 1250 412096609 412096613
    0x30203180c031222030c1409071d0a080d180905060109270513050f070627080607031b092111090405010507090509010b030417160501020d0f09 63
    0x25510b0144150904200c010031340a0540d82c01c940c8543d240210505007035641c640d0307460200314186030782c05201c0d605022500220880d0810138052442885d2541d220300c1003030000d004000c4450f540304100c60300160002e00201d0000380401115140c00c00955072025841c0c1006988040745005c1d81105000d14106414071405a03405402441583c024141281c507074041002c1004c86c041408a14811890a2504210704820f0302405061010f0241066170303e070461040420f900d4200c140544c00124004407541c44025195010366081c3d05941d094a94406454002c0b0038030b044412103c64001036210700b0340f00b90741440340b240214616441c3c1001821241004601620130198045040c0030a11507003054080c011940d8015500c00f5014103100c7c501d0500e400c1071406410100c1d45075012401c85200090350742440120305040740e40c00171001d81107131115640c9030780304443e0740b0301400700c80701c140629002e5012407146161113512403000140c0d2000c45406400a0f90a04005605103624282d81040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 412099109 1250 412097859 412097863
    0x708011a04030c060e18240f1318060912140a301a0f06121602071d0f0604050402130b0114040b0705100c09030605060105040302060703030203180c03 66
    0x60352114204154000c5d40d02001c0f0b4580840100000d512104200510880c00210300700f94034090000a050808410440c051140400301d100c0200e420544a02c40310389240000d50040d20380e0840200303192401103c0f0345618054803406403041d1032a1418001d4031503050740022020704400c4c2941142c504081014401400e1540c40018121000040c490380410302c40050402188250622808001321080c50501c0c50700500c410b038282d0701909908200e6441ca19001040c2c481c0100c14041008903542c0d010710102e41d0302e03641d910000542c0b2850001180c040c0709058481000100403481e80706a28003130f4500a51848060081c0d40514600340034000540c80b20764061500c04030001020030460034102c0101c2d00f00c1d5a001900070040c40c0490003040b02d10b10f800040c00010b00a07000c0b5030140344980c62000840e43d91106403000f0501c405000c00020702c0079040300354007560505020341410340d00c2d00443d2699101b540100c0010340e000040000301401550038015152100c00104007460341c00c00400c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 412100359 1250 412099109 412099133
    0x604180c030308131e05010e03040803161a090607030b04051302011110020301080a1713050918120c150106050a030f0905030a020a1a1017030702090708011a0403 71
    0x150030400f1640c0000d050105107400a200700303030320500b0030b01910142880d50140d050b100030200d48a5003018244100c405001055405840001c4091032800d070203449214080011392100b1a04003142c202e0100c403003103000b8040c0381f1444180c8050710356403403c200003e00f100c0c0c0380c06046200b80d00d0801031020943d0310303e211102460342070821991007129030b41e8080c9449000032001023601e00000000c0781090005c200c0d07810300792059040d0701c06c40c0ca81c20251186ca0040759116043c4071092002040186400fa401e242c01424581050940c44000805d49050202c20f1074120b0000000050300390401c20304006c8051078a4889141380000d50609030010110320544140500305504e5510204c10343c25142d02c020030695004041321399a800003400a92034000da05010386481d0b1a18140c1c240c11008a04458420705c01c180450a0301e500304540741c5407d284013001180180b00c144024001a111141a2405808140c5072032000750302d0842c848042c000c0c51145015881402e110420014645900c0c007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 412101609 1250 412100359 412100363
    0x80d12050a0b09040c090c05161b0e0124030b090c131706070f080c04030b070e1306030b0105030f03040905180a0c0501080c040303080412140a0203030604180c03 71
    0x4101619040758030400b510280004503441a076800902003040210a9844c0480701102c009121901030002c0503107860152803e4801d0700401e884403071002500e02422501c02c2c0100004240a4640307408140503800c0c0b00760442c00c18110301741c2d4040300512075465101048590b510342842101051400310b0002e19000c1c000f40707503000011505441000d0410019805030054020b820780c1071203c05960b035695502929184045142c00d452409401c2c42034003040c2c8130360a0840c0c1c10303150902e1031b41c03401d10740c0f08000d2684082102c5c1001d451441d40d20790800340c0c2c088030142c03c0420700e64114140100c034101c0c1a4001071180d4850700c0340000004020043c0c904546010314001040d03620440340b1034140b0702907522860f19004144080c01004000c61102c0c040d14001c0e0ba5525042e540d1008031801c91046002c06804a001c4a00040010700b010200f5030100c8050301d80313008650b0132202055240d8228005040142e00080204170b47e03070510748500003686c040d441c083d05140d481c0d525507220000882c080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 412102859 1250 412101609 412101611
    0x41b1202011d0402070b0f0f0402010f0807170108030c011410051903061d010e03071505100803040b041406030f040308040305070507030b040b180705010f0e030105010b03070801080d12 81
    0xc9901c240302c4034014480b4158000c1c00655a030451031915000d103000c12140c00040c1c018403008202102c4108078410b00c91a41a1a94602d8001d2a10181c0c0c68800041c8800208111401d018030f0088250421900034a10316000b9070700c0348503d04000b82503441407119209074901c440104803600c241e41d1000700849a041d560450500301034500d130056501c41740c00282c0ba560400850031403404c9195550170030645500000c20101059540c82c42e10780c41142009803020101e010542a4010150301076900483c141010000c1196a945411f0464000e07601211030540302103001c100a44000302200107005040300d503188ac52405000810340d00d90041d0020741003086113400139042502603400c441e01d0a03040401c8a0402e5a640741c45043d101084908071440c0c542c0a0224064840c10086810b2002400000c0c0c400c003400c01d40115049180d200c01d040c100700c41c1c4110420551428420940a4a0340c100c0c116941e1910700b5010300b00141c103034091a41c5502c241218402554071031141700c052035038000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 412104109 1250 412102859 412102877
    0x306070e15040e0108100501180203061c03050a1101290112090b18030a09030201030b2706040b030d0519120203070c050d1b020f030307080d05041b120201 68
    0x1001c03481980300c1000da0a8110800200825400543c1007401d040301c1c5040121003a440044495009403003003886147c1c0702d514100082d4002a44a0b0003030355000c98058522600303125480c0444e5004181c081003500455400218441d605900002d01c0f4203007200d4800901001c048a40a02c001642c038104c107080810100f6410300050b8842d001d444d6a001c0c400e00188801d181c141060581c030002543d0200800c00c1d40c40180041c4075020060391100b254684401c0e60b10b9195030019030180100c204000c3d40210b09980c0c400c9040711001103019644018140404180f5100d01031101710384040c103016200364885c000c1c820b5103940c0036044a03580310140424a50142d24086c05403500a8801500c1d400980044100988144d1200031401094010801c690414170644002e81305880e03079000340c000c1c0303200358400c0f40e01500300050340882d5414050201ca25003000e03521512274641080c5440400291100148000d001000004140b544500d9503904010b03031400d80300340d01d0104001d400a05020102c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 412105359 1250 412104109 412104137
    0x412032f0c012a020d030b010806120106150c0c0602160314010207080a030b09100b070f080f0703020f0705030127110a060906230a08090304050307030f021e030607 72
    0x24014500725070941c01024183c0344408150a0a031903c031a0346401486446040c5182922034040e5071200181a180e041450702c860043c4546924102140b400355902d0b20700c0040d50301c10303e2000c0c2d85860060b079104900204070740b50222011105501a0341158000803151090715801400001120380c00750401415810b60262503001e80103207900603001a07004203c46d004150103800240224600700c0b001081a5145502c5100c10940b074002c02c00d0004007171020100050b040e8502600030f40c040c510282c01c00305003507690003480c0e000703400c110b00581040e108540e46040030010304d0060b0004800910910502d007600e030002d001d00d00201d115841c24a081841070120500c1801407403003018000a651a0f19980c0181c0310344200d225800009000902a50181d950b00e41c4a00d0520ba012000c60710b00688142c0c1250100c00243c040314560008010002d1a60780401040000394401c50280701c0407440307030042000d10141c00101d82481d650610329a03c5a5030003154081d4040054107001500801301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 412106609 1250 412105359 412105361
    0xc060a020a12050c0613030905040b010c0602040305010b10050711100c0501051f0602150a0c210903030f09020a0b13081504020f0d08070204091a0412032f0c01 70
    0x510182c80d0b00d060103480d07208164080c1c0109042020780c012650192a0f40b0444d094840001b400a0000b0f494801d0a010754038107908030f840060b105140500084000c1d8491508aa216074403c95a50799510015246400c012911114541490801b00d00740080342e10781500413100d0815044c030070500129504081401610f00800d002d8100c00208510b01d0f040b440319010011422440716414008100002c4c240d03c0003403c8107490b4205d02c043c42076615031030742020140081e0103084c0c060190783d01030120b0b0015042c202240c00054480041420510760901070203c0b01d840104c03100711070805243e8000360715250200011250920320b9690b80310401002d003481d045030354000080b02c4c01403041040c8518070702050359020782e000b12005691036403c1001c0060200440c08000d290340401c0c0000b10252030154805900305009510181c600e100408a200b40581c04640840b40010f020023130300c805036818441c009a8803c2c0380411b0000c4424004501c640440d10078819403120000210180b03a0701e02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 412107859 1250 412106609 412106623
    0xb1b0703150203061c050708161d07020102070f0b010f0504051e090309040c080f0a02120a27060f0e03030601020a02040902130c080712060e1603091502070c120201020c060a02 77
    0x1200e1701c02120ba00302031034826281c003a00d00c03c0100070300c00c3c4c07c28424000c2950800300204e07190310000105001032020342d507030305100007048802955424021000400c0524030742c5040c062003203040d24140e60410802e882e940586130800740c029481d03d000c00c160120308030007003801c072a0540621542903072082c1c030306440e62040c0203074240c005041c01444600e03281c2068466024a20596000c2a0341d544c0e01c61000c100d002e1220498900060213001c2604000d140e0f106d00d201c880783d0340e00d030107003040002140000c02c00030310740c1164216512000000302e503040344103109150400401461a60601c076000035a505070101001e84115940c403110021076480504504480301c1080051151100c840800391642d2070480300a004520b80c680d10b80b00c4c0c0150f5200c0c03e01036808882013819280c0f02ca40644500c18050f1b19001e05150b80d0724002000300d40100040400110303840805a035a071014036043c03820070f4413944201580846c3c4408440141e8002c141d94091000c1601c50f541c0f941030781c1c907040b0b00c2c0600d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 412109109 1250 412107859 412107889
    0x70c021003090f0c080d0e030105040b06010c0503040302090124030b134d0c0622060501080313060201020909011a190f0912050a08030a0f0203010b1b070315020306 72
    0x105135500051028001c14217240128664445030100d0380032a051600ba10000c4800800c4c00407060001512980102586000300b8007410441707003440d03265070204101c0d40003a046042955059545255444141400b00780124450310b41404401e1140700826413000d0b003c1c0b503031a5410b03100c440400110395101070030b803104482141e1010400030000a01c41c0c96001000c1c0c80c03100c0d081031064501c0e0001840c8200c2c0d0b1541441801000c66580e086440d42000391120181448a88020000c2c400b240080c003e6138081c00f8400d000d0742d81c507072400924100c219002da2010095900502455003595504075010b0704440924150840717440c603800d15800700f07103d001403c2907807240c1d1440d0700481c0c40e848500d03901c4412254a42881058079800e08000354120b5203402029039001303807a940b0000c2c8515010f1604040c45100c045210301070481914241d0704260465a015403010030300e04031488580c00c42d4003426030b0000c081c00e0140e045490301004a6442030074019401e4000010660030f0f03c0350310b000b06200c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 412110359 1250 412109109 412109123
    0x20904061e11090a0f0f060807030e01020a080f060a1a090d05030f0307030510081b2d0301051b0304060209151c1a010e09100506030f040506070c021003090f 69
    0x2000b80a0081034100216840c0120340365840824003400c803d16400507030300b94210741c00c00380c0e00d041002c0f101c030b0302d009003280b080640700c50100650750002d0000d010500c034a03807505511890a00d07070143c2450b01c02070031188104c56801041000c02d24612041036282c000d0101250382da030780800498100c190450f001821071000042a49401c07690201650040c0c0c50f540d1305108039191124007006c0305410380180c600c16003044100c1c2924400102546100e0340010300580903100388203681c040540c090008a80c0780300e00f0a28041c10030314081c0319460f80281200b805045c203c1404407022450b000c021300c002d004917800150354100e60f40d108240c1090080ca11002c66440c048001210f443d41d0030240c190000d58100007070401701203e00c56001c100b0210617501c40e0003601c000c204002620b140544010003c2d035440c040441d07252110002113104a100140103070040c1040e280c03591420310000c264900700024003050000507078441e000c4207010b4495240100d01d10f071060420141c0c000200320010519 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 412111609 1250 412110359 412110371
    0x30203030a200703210e0a08010617030414060705030d1104080f0a0b0c070609080703080603100509060609090c04290103020315060c0a1a04021c020904061e 69
    0x100e07800110b0021003180c40c081c58441408400d0000d80d56001400003c010381c4803004150070000c50b620240c0c10b03c1004d40703000c100414060780454000c91841d0000a5aa51201e03400c0c480501d10390030108a90f1107050003545064a0510902000ca210a54040c0306d0b40c000104007080c00010002d0b5000300560305002c0044540c2e800e80c0301c3c40c0b6445444bc10300c144c00b4000100612401c0480c594090a41090514045aa5000c501c401d164088042160b8050341c8480f40000f189000001d807200703d22039120211681408070802d80f8020407400e00224050070030080103000100401d132150000f606441e500110340300c44548605164601c80400d41091a12100d259a02c01c500721914060400030089041083c006004606900c0202d0b2501002007141b401d103203640c01d040006000301d602800c03d4900004250303542001040d031300480e0720b002e003032440117110543c0740c00300f51388040200c0d8075488050803402d0b44c0454a0f80c070005101030603e59444a101c181c03600070308003050395191941010051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 412112859 1250 412111609 412111627
    0x15051b3d020c030c0f0a0312020c0c121905070f081c030f1b08040c0f24030905030d050a05070905030d08180f0a0c0f051f05070b01030501050a0507030c05070f0c03020303 75
    0x14074682e0720801e41c00100d0448d140c0011406274400ca40308440e100002d0300341e6481c101d0600c50115a92028000e0070311541040d68040381c0c20389003c03110184250003405c8860702d490113140e07082c0290307002646503810544c51444a10f03032186a84d011041603060100e81d42c11201a4040109000361005450f14000b210415601c0e500140191099218a0740b1060300354840e64040640300b1603020345000c1010421600004000361880758941070054600411000540d46e144c0381141c011840c1e41e080e498840f01401600b1889008080c1d224041d0310341012030390b00c2d01c00001c0e43d0300c0b40301d9003143c240724103007020846c0e404041101e02641032624048407500074020740c04036038411010b0380540388940c100c80d010039a180c55010385001c50b00003d013440c001c0400d01308081c06031314070100614103000e000c206450019084507240c900860044000103800d240203071a00c01034030030081801c020145040c1035245555001000e94000d1b6400444054000c90545448000e83c07100341c0011b9814403021921041d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 412114109 1250 412112859 412112863
    0x100f090206031e0c1314030304090e0a031b0b0a02090f060a020a0b1302090f0a0b10030c1706150703030e030c060601091202030715051b3d020c030c0f 66
    0x1c0650f04044500013507840700003048003030107030301224030324040c85a80c1003040d004503480c1102c3e8100010260f80c074080c2c1d2030050f8812900c08900c00c2c1c1c043d0704001000824581c01c401ca1012030541015a508003440b50781d20141c00707a400a10f030060740c6a0200c0d280200d6280c2d0b001003502964041c01c01030780e8003500c502c081e54543c03150104440006040340050481202064204089680501180324988805484010210008184050359130351490b6541c01584c41002c040840c5041e0b840005504101000082c5080c00300c2903412140c08031601441080d4484104903110704c2c1c19042550380b281150715086001e000000c402200600c008a00d981092a0104110740610340988541c5c076180d9513485090741c6010303010b401030740c160072420b020000d6110141c85180c41c00c84030b280091508411100560300b034541c20720625820350005003c0056030065084882202c2070700c8240c0614140d001201d03040b07141902100c84455a00896105440d0743d00304182d6010711040d900f980c2e091564503035159 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 412115359 1250 412114109 412114141
    0x203042d0305281a0402030f0a08040306110c0703110406050a03080c070f230d0b161d1507031b0b060a050d03020c040e0c03010603050309040f0608100f09020603 71
    0x2420008203804554520700e5600071030031a4980c4100c0800400001c4c071260345601d48014010382e014081d18a142c00d04440034011004170070300c12440c040d241d80c1103040c008211501c069402d10b0b01141082010640600018504c0450780d01c58000003d204200c40810060318a82d4855074101da440360000c410402d07107401609003000c4a404681c0d215603030b929410f8480407640304035500c03034190034071889400c4541d00403026080005070034451701e03038090f9a80c540040003c503111540c0622540350b2132501980309914245050b80c0e90700b0500d0300c03810a400034001c80d034155402e180024001403603604044c02a48000382c06110103c5801310020345007044030380c51608942d540d01c204000c42c4003054500c0c1c1429004100b42c0c00d40d00518130a01007009100040048801d5100c50f841030004190701a6000d000c0e1401461145004c0c64641c0c00c8142800183c80c070300b50003a00003a0400b2414400b08800054205101501031404901e000081903c1e000504010102941003c0300008028400741e0404410b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 412116609 1250 412115359 412115383
    0x30a090305010c02060609070c08070f05100509010b0120010e0f03041404050112020d051507050d0b090f161b03080105030606120304060e0609040507170c03070203042d0305 76
    0xf0700100703880c550201c1e15000c04407900f0f903100301d000d400714817594850800b5500484c0311301022407424600b031300c4c1c261300c503c00c094003200e42c2d5001c0c02ca00c00c0b82850302e0103102e41000088000344034a08148002908005074609048042c0c1c0320340c1d601c0c01d0003900075003144404d546843c044c0c2e08400d00e41c00e45c06032680d204e4000c045640600240002945c1842c1c400c60703040381c94001040c0d0380300380207500300003c100f990082a0341c94403c021200e0455042c021101c0e01442154a07035a80d26540b042a450070394084243c2e079480784422104211600c1491180c166001001007007510166404140c00d580041c0008070040d521035034035130310741c0070143c003c800181600c4048088885640c4e0b00740c204260841d4070181d03000345800031300c0208803407070003a032181c04021001400d5504107902d060101b41219001c42d80800068485200701c41180080b04110380c1014000808903d140303000c2c98080e5a80c400c0e48520740103030f513808032483d121515040544880e80100e0700401030081d940c1c01c105568811038504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 412117859 1250 412116609 412116611
    0x30305040e0f07080703230c03010920031518070513230105031b12041217011203110109060b030708030a090b090a050d030c0b070503011d0414030a09030501 69
    0x21400e48240b9441c458440c110594442609503981c0000301d0140c2041c1d0400c4403a071008407001c40001001e4180684a001208185a240e42c50600c03200190b9907201031810000c6024170030702c03020481c0c8004a0740d0240e0380320000301001d0318520101701c1000c0341e009104403060409003441a510b42c4800100420200e0000c510105034884041015194404400d41007500079265071084a50050010f076038410220b0358040c0e02d0300d50354a01140e6a51040311180d151810103401c2104114010340721113a65450361030126150100038150207902c0806019903143d0380c0c0e141c5030080801d031091941129503000c0f907009105600342031400c4806045156041c0d440b83c0210305021807682000801e4446082c400d41c1ea02040a261031082642c3d6400080884e80003408050080b07920384a1141e403005003440b81d52440901400ea08016110580c06020b03403040140410042140700c0028074409211110a20140340d16211440c041d442019141c050152600000c00c5c221032598104220100f10390140d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 412119109 1250 412117859 412117861
    0x4020919090e0106050a051305070203040f06180603020310030f05010902060706050a0b060310090f020d1d0c092401020138030a0c06050f070c180e06010308030c071506030305040e 79
    0x400a4141b0319002c1c240c0c120381c1c0705501c12404001a04502d030007010600640e803400342c448a41c00800340355a0032440101d04500c85400d420b01d107841c0900c0043c503d9203000c42c107600305080494007221541c0b0003e0480b500d4103031404240802984a9010598010301c217903611080307454181c0180074100c0d016103c1d1803500e010000d0034180042124850045082590140f0f402c012130304c0002c102d14070b128900140d0910003d0740c0482a8070600e0301ca061003078183d40d072a1036050a10b03403404880400c507901645145041c008029148150090381c0080341155130300f05182840101e0040102007281140144e450042c2c6070144181103100001080914048141401c4c1009240d940c0ca41018000c00c02400d514080040903c1000505010714213071182c00e2601990742c4483c0040a96900004010f42404180c61003e12140c420722503c00d0721348001d0000c962464842c000580801030104000d6180020000104644003070707a545400304100f0204075081e12070038014695006070141c12a0020148 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 412120359 1250 412119109 412119119
    0xc1e0b0a150303080a0f1506111b030718090204050f010602070e0903122d07090510020a1704030813084b061513140604020919090e0106 60
    0x100805503901034a40c0003045c0c4032286640001c0001091004449030b4400e50a60303600c0e4030702d4144c402404a550b52016a0110044407810301800e903c54006400340c41d501d000160b200880e50408854618aa078403480f815220034902801217580c1c000c0d800303480c04042210480b9030500590680b03445a003150011a2542416407100c1380a64240f280d40d8014000504004814620142d10003c0000314032662440d44401c0c00581118040d80610101c6503010061200e41c09054071005001c121104101440d10510180d01c480400d02e02401a020100c01e50303003589210422540195070003050030766507900c030810301d202c0d030566805410701314029000402d00c8680750003180402c010740c0300095400a0b42c00c82c80c3d14204002c092030340745081c407400d10707182400720705100385403240c00b402c01e12807004180c0030304000006c4500091050031500e0480098512000c0c2c0c0d043c940d2040c6c09590041c1c0c1c507100c0000103248841031862442182100945c0403808540c01d8010980c0517220f0301c000e0021380c0e150313 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 412121609 1250 412120359 412120391
    0x29101e03020421350703090e0c030105010201140c0315190b04031106070210050c010f140708010509070906030209030307050303041b09020306130f0e01060b0405090109020a0f0c1e0b0a 81
    0x118598031510001c40748040713281e100784002007882d503100e0f04000301d4007513a58400c8200004100c1d0b68262403a00807004015070350302030082c01c104980c01c02e4034260034030f00350040d01340c01e0001030544804907027480601c41d81911118074420302c8550040078a02800d80c0e44d416071071241c0c407501044400390414a0000c0c0342c0d040090965002607030091030002c40480400086505402940c80e2550369901c0700324101c0d44224501c15290103a041d0741a0200a18119170003034644841a4001c81c00388200004021940d9070007582d02094910a1401694409620001038954000c450b8050301c85e01000080c0420031190f1100ca02d4034040230b80000364040d81e01c44501040b4082100d4035a0042580f1482d80d41340c030491750094041402544000031100c4a0f130000034210742407508204101080010180914038084140500414016070b080d807411075407146c02001d4a6200e40380300c0510441c11181c104212080c4803010440c00342c00501d601608031420001503548003540e1260b60140303480705428041c090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 412122859 1250 412121609 412121663
    0x4020c1203042604050306060111190807141513170d0e1006090e030310030201081e0a0902010306050108040c0311030f0129101e03020421 61
    0x100000382800345011552031459900c0180100c1c0ca41c41400d90007040702d4410303040e0300c1c104194003d07501c0c0c84e5400c01090500d4401e0291003141407010310801c0c80b002c1180000d824007024039012511000c140c16140c950300500902000610701480307510204503210001882d1500306901c844010099103030b03c4010f00080c40d12500c0500700d01030043c00b14034811100b81c0104000c442e10140040c03174103280c442c243c1c20003603d0190000c0068035500d0401c170800c0b090043d4008103c40e00007031469410061401c200002d09444020705001810b00046c00c41d2101891448102001030f9944c1c20f18980301000d08014440c448d400c0780030a18180d00480c21394800e80d5040d1080d54004100c0d804c0c6400c40d101c500148803403040c025410b1081c0792443d40300040c00c0c0503940900d011502100c0070400700d19010004181c040c1c0350f10340a43c03801603082c800c09901c216440085030320181007480411400c002140030b88640e40200003803100e1101e4110303003009404c81480405020b0900c9000700301d01c41c41c1c00042540c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 412124109 1250 412122859 412122877
    0x50f061b03010b18040e0c030705120a020d0f020d05010e1203010605030f10080a03021b1210180218071e140904060510170c030105011d0114031003030207050402 71
    0x2200740010302001ea4440d0060829600400c1c4422441000c030380002c3c00d0f982e0281d165182e541041148140e54101000000b02510301150301458500102e500c103a60b0340c1000d50701a115203d00740e80300e800c0c0492448030340c1140381c018000d241400c0b240d0402c14041c02d003c40c11940c40b48a40c41802d8100e601990a0301d041c2c40c125a1840d14540718000441602680540308800004000d40b00083c81d0004000b005c020b14402e4003e840c034a0f840100c4682d40401c0391030024043c80c2814032188030a540460001858140400c1c0000c0c880c01988a24600e0011208005e400c0b07030000c1280e030074100e461401a0300c5403003da5a00310103032000c0103201c01c1502104c0f140e0408130700710300c52400300101c02802901502c5006400026034a55800003c0c0903102e03410199804a490b038610341003029103a10101e0f52003021222aa4a0b5515040000700059504440024840c4101603011681e0f0303c5011506002e0251252240e200e0a2000c0b0940c854505d51000328054031400c3c02c00203090405000750780c80700c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 412125359 1250 412124109 412124161
    0x20f030103030305060307051e01030b030d020601050618030a0803040506070f0f050705012007020a1e0b090d05010c031d0601030b0106080408120705121e01090c0c0807050f06 77
    0xc1d1031580c094001e4807004d01a41e0b4035024416012071540c44d4884840c0241050124400d0741101800000d001c440a5282640c000d1b0040305050b40717199000107119044500544280c3c0d80ca00100001080e501120044190b040c000c00840720140403998014500440c010000d40e041e58680d182c054500d10f88020803500442d000310360310003c09004501030503007580240000b00307046d560150300c584a0820007004201e6201d000c0f40110035410722540100140403000c0940300201581d04038540c800d40c4611912340304801c00034440c3ca894603003040e06025194450700920000c410701300c010f805044070804203500fa14044180541c03158001540504807034100c10001050b909114084a04200c000c0098402c030300c0c20003812041490100c1441d1140d401c0e0340c0da652b10380c0555200c80006020103055070400600c8400381e508880111034800e81101d1031010001800307510100d00703880040f0301090144c854040460b05000744140400c0e81800301b41c68400fa0790540d0740b01051200718040b190034602e01d031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 412126609 1250 412125359 412125361
    0x71101030b100806040f15061b1e0609290604021c020c070302090f0601080f072c03070303080a0b062703010605060309030711030c150d180c0e0a020f03 67
    0x2141c0078a9a641e00039102400c04500c6030410440002502d02c1e8900c01e0047c1c2e01216130030042039601c1318040c00d07403100c807032401000001503403251007804600080c410b001da440070820340104840c41d8008800b099100b810180c00320415031a043c03801403c00742d02c0d202000e09400054040c40e26100700d0711465640c6041000310b2252036001e0009400c500c00e0300f02c89124404010000d41d43c2d40720344900c40e0361342c084400428500080014591000a03085542000141050125040d00320f54402c0c010040d00c9641424402001030300a2031000c000120750f09401b8103031012050642c4003000038400c0c0305440e07040c00b400b840a0300b4868144114507403800111002c00c0480b010307610309040d29003225401400465001d45680000b5042d0740b003501e2148183e8000100c4404001b0135154035914090200d0103084a40c0d80a4007203554801c10b00c0302e00014000000d005c60050180b030b44001000303016140603880c0150140791807115040103002d948002d01b4007000190001805008954004090303145007421 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 412127859 1250 412126609 412126639
    0x503150a050d0f0f020603101805011409130611090f0f03151b0a0e12060c0d151a040314060103081219091b080f03071b09020c03071101030b 62
    0x8140e03e03010102c40407112259441c0240c0e0341c1c0c0b0081c41c02000c1607000504454605a0240d56a138164855141040d081800422a807400b4094200702b6007015140c5d0030760382c1e40b002c10040c1d8030500702da0010125864003503445000034507007020340b00d50305040e18a13400444185c020094026902c7c02e01035030541c800980c92105100503603500b6000708101c10303c11041000002d00c52500e0300701e130140c480054074428120b40c4030f142c03078189000000303034810103820b060400c640d245001d4401e0000690b0165200e40c40007086115250030100200450740e21100e40180f20081030203554040e11050703491300b0304283c00b0030104002080750340c12a1751218026143c21a50074081d000c00200800b00c0c4205d004031850220703040414003c025140788544000300150380c0380810001c8846407504034102d95403100e89a000c0c3d081c800011240070607004031941a0700e000303a880700c0040c0c030456007026444900114119021640000180c074006102e8000c1c82003130140d401c01181180c0311007100d140c2c44101c1c20242e0038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 412129109 1250 412127859 412127873
    0x303070b060d080d060e0f0609161103070606030503030115050c0601051e0d0320011802090901180602041404020901020d08070216030c1d0624190503150a050d 70
    0x10b0032a20030900d80341403200400000046507981e40c4110700140d09042040a0207401c200300b6503009200b21941c210300d04040c40000e810b10564440301c007d020542910350090201003058403451a8080003c0c0000c1e40c80340b60180e2650004e110303103c2a400004400340c000b074080d10a503410290a1001001a42e20b803000b008110028007000c1c045082420003d07050b29242c54205d81e6000b402500c1d81e40c010000078294103a540040014503010b6490021134a013000300905000461070340480d4089450b84840f08274034010503043c40107004101d8050b415504000e080d801800464610510801c070180740c88081c0000d0b4401d00501c41d0043c2c001522801009000c2c09003a60440c80a01c120b8543d608416001e290b588840e40081d900103140715400c109101d0f030ba002c4150790302e203440c2c4150b07100e007054004980c403004201d4003c80010300c8031814540401d030400c1912403040e407102e10740309202e02c00389011b400b0303a2082d525030380c40c030380c41d014088001c0c144001c200f011140064a1907071070422a40b1007403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 412130359 1250 412129109 412129129
    0x30d11072004021b01020a09050604210c050418110a050607081c05070c1401140c0705120a08070206060d0b070e010e0d0b070f03150504050702030d14150303070b06 72
    0x81d510943c00e0210441c0211030071000003000410743e000507558400e450010b40a4825944840e03c901000c0009100250010000700387d05400d2592951b51482e440c90400f40e40c61403a040075030031614100b0604a140c2d08050340c2e00005d40103841d840c0715010208107001c60800c0c0c80c02040c3d000101046001d00154218005002e0000803441d650f6140c0c48224810050301c0d009c1d02c0d1500001d0381140740c4410302560b18011b4998109010007003080340c0104441c410640002401c542514502041140230310a05100c98416000900d051030b96038055248064081e0300d0070349070f01c00103114550000c5c3713581c100039034100451500401c11482c55510310340125032517804500360074100040300d5601c2100e81c40b5904642d810754400c0002c000c5501e000600141401488000740c4201410400c01c6130b1003e002c1c9100c0f4080c2c0f001030b1004607160341e03008000c0e861407240045045503580361421072818030040e80400b1740140302c41c600c0c1000070007c5904260391b0340620310001c2d113440b000368007141e004d1910754580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 412131609 1250 412130359 412130423
    0x11d0103020d05030904051807060503092d0a0b0f07050903120c0a08040909050d08010303050403060c1403040b04020a0605090127170c0f010f020c040f1d030d1107 72
    0x90b89000441780200d4165801070300d42031126807050038810340400d003e2000c000904200d180407400c40c64039550169441400031070072000b0b6100c0074005189104007a903d5817282d64160221409030841c0d20303010309802e1080314100e009107405408542014420002c60b45c04801c028001c01c1e500c1d003203240a841c07641c03000c40c0319038152290b041a00001169003002c3c2c03008141346c2c1030008180c561400e00c607040002848000c002c0040040040c000240c0250554050326000840016442c1d03c804065410307a02034030340031103c09000710030002041419184a0b00c00d80c030951309196103d40c0c0c0d4006480034007401d443d450104100c008501c040840d05210035840000800c3c02480c410754a5101076481d08142010040ca504829100842402c0490075107540ca402842c02561590304820002c1d124240301c0e0007107100f151541180440f800c41a003007040c986000c8091034075100c043c51100d9641e070340826642a1083d04103540748082003c1c200c2550711894001ca2000444000c0c4244c00c6049280b40000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 412132859 1250 412131609 412131613
    0x6010509130204050301110c06100806040f06110415032904090809060a05070309060207030b0403081302120f01050a0203010305032d03010e0403181401030b0105120406090209011d0103020d05 84
    0x5241da809008043c001c50180b08110b54134001c0041c0c2e5409c00c040140086081c007e80d00f000c000f4000001881640190410380505607000c0b240381942c007402d10a40c3e92030030040080b81c04500300c080d0310b02058000e0000d4402b00074100705800b01c1c2c80400c51840c200305100030220000b142c0d50030640c1016091a00c03030a15645800000340004e021078110740d05041c00a20b0110380a0101074008490b84080c2c1035a00084c030405246130b417000c0311494014401410003100d040401c1010f848100e0b0b2a0710a80d00400009030b85101600c8507650701c081d25940c0c1003560a200125484101c54400c0303034141c1c2c2e006005985003500300140d820401010720920040710420b82440506440181c1c01780d0301800c0400080c07901810117003001895a60309008818175131034000c0382040001005105852410820308020900081750401a11a0700980d0704003840c0c0b4400c4410042040a50380c444281035108030348601c4682d0300c80d010b23071108942d041000c0c89072540000050016146c18450b403081a440b03401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 412134109 1250 412132859 412132867
    0x190501020705010f05040b0106050313230d02030d14091908040b1204030305091c0e0d20040e120304030c1713060305090a050705192601060e060105091302 68
    0x1032401c0c03c4a007041d0b02030013003560750002c2c0410007104610080c010861464491301398286000398580c000d40c91000100040105802200e030340d040c81e80c2c0c02c254243d62800b619950542048069184e500020a00420f1450107415140071b448408685002e1150b110041c62814841800300d0607004c0c88082c1901c3c081001d00c80042c030300c404c081c002c0440c111207200c1d9502508003490041c06940f8081d2400071150484440689e1309900394007a030a081c2075030310b0041c52024034100030524100f15041c026010f00c1111150030682e0052803601030303030418299401c000c3d0340450b00c60640c403411008441e0548960030400700c1d0121384a02c040110300c81c020001c9860040b09a034003004135600070102910700d441003d030300700300d4240c240c442d00b903000484802030044200035544190300d4001500485105410700322580442410f0762128070094001c80307002c0e80416465001016144044680c003801942c2481c1011540c4603a41410601400040c0c6880b81044201000c0200c4c0f84484102400080e500340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 412135359 1250 412134109 412134113
    0xe07150e09090f03070f020f041a0f040b0d06060e071407031d04020a08070f090b04122909210909040317010f062327030d080106030c030b031905010207 67
    0x220041500c80c0c030604c8990b01c001c031544103215488101078a40c0c2d11492506400c200f510080782b0303011940d01400c4420703140001c0d20b50700240041580544050b00240351452040800c10a035112a040d01c14101c0030301e805036075205040340c03090b41c000b540014620040c001c8400080c01074003240001c0200090043e541501000460100c0c2c100000200c0001e02440a21003880c0c1c004885101151580c9420b0a04a00b0003000c412148114030030f02c80444003074083c050078021501803038042c1c0141d400803400408005503104450300410b44884d0814050100f812a60f0b154102c18010100f0400e41c0590821680e0001c02411036001441a801e000010880804c02da0b2507a04860103000820a4581c020341020001032090040a420402c0c0718482c0864111314204c032416200c101c0c1c1c0d0101c296020608030440d40c0480f103590880c060b0148240214a1010b0b5000360b01d083c181c0b006650104448183c845044050300d020701c000340d4140d00103aa06c0509542c03198185800d0a005000151500c4039075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 412136609 1250 412135359 412135363
    0x30411060a0309110a03030905010c030311031512030a080a18050a080301080c030106180213080d02030702040506101d012105010501020c0105070305180d060f0e07150e09090f 77
    0x700c55a00080c0c0e03c0288008000321040b6040401c84150340c0100071170308581d0b000d040c5020380d00900341444003c411f400c1c1014825002071218601010040d5200c0c100a0079050522007060303541e0340704205152580d40c1c01400041a12500b0002c1d94804140d03442d142c075210f00500c18107160200b504030751160000840c40800c209a445c1e407203040d9081d6a58500603920303040c00203e100c1d01f0b00c40d9060107410400442041c02c81000b00002c82ca00603550088000e2410110f480c941c00f80601d4021519440314047d008805000302c0c5009540c10702103035480b08100000642c00011040107e05484240c0c198904941020b0380e0464040c1031020002541c400d08034220715100d81034468441e1200018040740d6410300c40070012040a007061810300010f0760703028020340204428841022034030704000281e0390b00d490346000d0312600540f04026401116a410340903208512075101c840c03248810021346600f404400105008855440391b0229012504114004101901044240c0701740d012800303c100d02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 412137859 1250 412136609 412136617
    0x80c09070822231207030804060f0b1216090902100c150204080105100b0f16030203071403032403070512101821080a0c2f0f120f03041106 61
    0x140b0f03c140124018000840ba1070002014480e0015400501280d800603030400c0c12140c00951080c004620462881c030030100070950008990391084403031030008085c2c400464800c454020703000310001c9098039803003060107590040d20300940182d540144c140d4414407503141030741813911030300d61240d040c2c0050f060b80050360016000910565510400c5c8110a1003c0394800c0003841031209003800c0c8015070000d0000c9014108074019007080110f811400c01d4400c1c401c40f01d003242d00075440e0741031038091045596290421944203256904030080702004480c0c81c40185440540200200355840c205800d001c01501e00c5001107545100b55080c5d29000d1031107001e18122041c5480700c0c450501b9a0741000110b00602d42030f800c040d494281e014804039a8400741c0960305c41d052620204011103028011034000c5c045613941d5055240000c0c0000d4134007505181d01c40d000d4008411501304c406d02d0315000380ca4003806131176040d0000003085141301d6900c541c00a140e105000e414814000800303100821802c1e80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 412139109 1250 412137859 412137893
    0x160503060321180d0201200307060207060605010216240903060203090f0615090c030603150c040f0902130509100f0306050f0f06180c1e04080c09070822 67
    0x109050700a803a1450f00380c2e080e0700301120760700c0c00d940c130a40001e004954501d04094500c940151543d100c5541001211901540706104554135501801d010780180843c1c09400d00501031a5455128031111902010583c1d240d48a0503040014028220200451100c1d0f604c0c00e00074400030000200f02c6070301c00385105904481c040d110f034107681c440c03890520700c00601c5400c0ca48203120741001962100004039620030420981e0316035984500d00000c0c50500c0104616010000401c200070707070030015801900885a105090b00515030721707030111009900494003401c1e04d0b0814888200194580046441d40101c001c4820040498944040c40007002d00c540082d5081034840c801e01410284107071010b94000a03c1003000d0040c1417510004502c1980404284000c0b07a8482c04500901242d80455001144900e401d100c041100342c940a103d81092140c2c81280c080d0304c00b0502541081d041c298421445030750707004c01e030343e40b20403243c007900c0c003045803071000c5402142103000002c02c4c10b504001524 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 412140359 1250 412139109 412139173
    0x801061d0315100605030c04030807390801060b09061803060f010e161b02011e080402090a05010f150315231c0206250f03020607081605030603 63
    0xf1034204140491424103500c1442086070030420041d00031100c00940f0300366644104416660b038000e081c04401e14141d10800c2e80246255500d841000302503400d042040680342810301e24807640d800c104d6080f076003a44200c1a032503408001d10013842ca000c0380100720b104641001c0a100c0100c500119280c49021121103c000c54060014445241503038195684500d030001449000e840c80c0c2c000400e5150085041869004080f00480031a8064010701741144000c4da41e22001c8404800b004019a0040d0303800c0c0e0240d101e550200e0300c2010b007809154140d6075207021040102d450070a4035408481594400401c0680e2280c0001070f248442040e44001d0002200d901c04101d1034030400c84ca44404104503e215840c01c69600f042d001e1103002c80754006404036181238442c800e2581c40c2c80f950740c0c41c980c40d0101524800b035020401200c100c1510b0028029402c90b003c5640340d00c8103942c0c80d002503900e6503c2c12007025581c03103100c1c8030340011030340008003030306441c1044020075400d400390048004080c411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 412141609 1250 412140359 412140361
    0x6070f020a090e0d0e030c01120207030306050913150603050a1e0c0902040512010b0a0614121e01060903030e130209030d020309030c010c0f0204110705060a09030e100801061d0315 79
    0x4640c2c050386903280726008501031f051074411480060b040540508801c42d003250081500410b041c006c0c0e00903401000f000c2e0281805240022002150b01039001c2c04440088031050741100d07409092050b0340c20b4a9000c0000d0203c500c054072200103402482e403101e95041801c1d072440c2d001030088054000280424a17000d81c03118100130420001e03c85a402145580e807500c55202e800b40d035051404d000301d4415040ca40c82c9000d101200808502c14403550350f40c941240010300c17058200140080d514004a0000000c05988400c0200d0b44a026403201800181d0500b04000305031400503001e10300345481c00401860300d02c0020101b8149040081982e01580000c0f1b40c6c0c40c0e0f1390600340100c0040c1d20003440c24090702007281c0d8404c0101c1003000b0019021315aa982c4c0400b5030500041100d0310250003000716545440d090003541c01178012507800302d001600c08140c10007503007407001c001901032213503071181c0185a08001d022980da4a102d141a40131210b2007a01036007980b028812200788190380f000010003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 412142859 1250 412141609 412141633
    0x61c0b01050f01050c1216060e100b0a031101030b0d1e0b070f0518030c0d150c0804150b360c0301150e01021e011a03060606070f020a090e 61
    0x2c1c60901030700c034a05109040040c01c4440340701280f6854981e91a18001d900ca0300c0d1003000003013248406200400c514a81400740210b40800500102c1c00c40f104c07135003803201e02c2c200b0040c0300039841d080c84010030440c1406d01c6031015601076044080d00140c080d03e01844d1494a84a4142c0700240074000080d001c90b4100c1a418003c03802845648500181040c030349608501200030f0481c4618150f042c0740c0b880d02c8400403160303681400152580b0717030018059809080c0c1414004441041c01401102c01850405286a000d01030495a032159070010220b4181c4a1746120180c06003068102e030f6030f841015120a070211240c1c00c0080614102d02001440e808500c203180c1e80c941400c05484003c00d41c809000400c1030401c0620340f02c0c402111498482c4551611038010b034a001d5115241d0b18005109104240301e8042c154810004050f10a0140514581c0740c01410b031200d40c11b4070625004102080242c01040c60038040500701031001d0304d5010300c0c07503507108218221040c1074a6100d5a8020a0300000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 412144109 1250 412142859 412142869
    0x1060c020909240603120c0f0c09060904061a0405010b0702040e12070f1104050414150103111005070501021603021b01050d0b030c030106060201020307020114090309010503061c0b0105 81
    0x544400c0c0e94004007822084020789103d89001200142c1c542403080c0c0c000b4950340c400788441c28020056207407250310340081e80351058446101e070180581c24803941e06417a000e454405189405228080c2186803a92120f489580c080c100b0659000324030b071142d0a080e100c5407518400c4a00034450251240d44039400703881040295114002001c61660015525017441c891100440d442c540d4840c112035694041d9260070b45403440e004414661003481e140402c401d2214032005015002c00c00c100b55030307c1090b0500321074400030b0280009401b0115006595072a810113022649800300c840c1001410181e0320b0340d83c103080e40d101c00c042d080c000e43c80400c1c51007016010441c2c0c1c000401600a60f0380000360b203900082041c007800c0c415000d103c1c0c88029815150710284105840400b0140080c0001921240068080c0d4001d0781c45034015840c200d542c00110302002c00680c0241c008002544c608100b2500440b0300b900090702c0700d603100b40e95810044404075010201c1e50f4091059005145562501e01089 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 412145359 1250 412144109 412144111
    0xf0b04050606011d030303010b03101205060601030609020a08070f030204050a030f0b071d04050a060506070c031b03050a0809220f0f0b0f100e0d080d05060a03050a080304030e0901060c0209 83
    0x4e20b07401c841c01084a40c0d808010340b419110050522a241e0352440d0f0052884889640184a03245000b4103180c20700c607010079134078407480e0281c030b0900c071090b540e10103203040344100f900c03440001d04158040341c02c60b0b02c120240380c00b4206614000d42441e48440001b0b41403107a90784212142854417900c1000c02559161080e0301408506103000c1400d151000d141110000b2001c0a03c00c03035581001071071858407075024102408008e810030b9200d00c15032410214551040c00165071000c031120039456000c920800d04001e0b070764458041c0249440d02e030382c1e04003580c009440d0f855114591608a04180b40c411100301c1d18101398207004520a00c2d145400c1d412541d100e46000c144074208000030074507840d0b40484420382c2c00d05580d51840204402e408540040e07101d00981e074032001c45043c050601540001606404044010400c0540c4800b0308100002015120040c82500862214004601d450010f95801806410300748100304e80b05c00041d00060090300301300c004c24890104802941003104030070f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 412146609 1250 412145359 412145387
    0x302100503070203030708040503070606260106080705130f0e1b01050a0806100c080d2306010c0b07050c100204080c0910180b06070b0618071b0f0b0405060601 70
    0x60351650030b003002c009449100082a606c2440030300310125080003810401c40348102e808c600b0030008036403103082031800c002da2a240003c50148111303400c1d0540da010302c1080110b84034200203040c0300345401c09204880c500340340d64020aa03600c240102604283c0d0150503217506508003d02025025030882088102054090f503040100130310140f000f164004401980108048410b801c40302d12600d822981800c0c42032008200e4013001c0b541d0384045555800500300f040340030b502c0d040344500c6403003079841c004000c8074010f0000300d8000425001c621501e0703095800020134907000345010450b01141d40703003000300d000001c02c1e0340c3d000404202054050104101c0b2620483e505002800e0a007201c0c140c1140ba0701503d0460903182004140c101240d9100c5444000082d103440e40f1401d290411510a2908a1f092400b5801c109400c1c1860b142c8458114454030300c58a86408182d80f03480c05424000c592181210441884000ca10100394010364030f501c62031107880140390034030302000010a4003400c2a08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 412147859 1250 412146609 412146617
    0x910020c01170613090f060c03020414011e0e011704030c060b09041211030403020a030b010510020303040c1a0d14010602160501020604021005070c0603090201021c081302031e010501030210 83
    0x501045641e07544140811400d100750210350601a421b20718050443d03880f004011a213445500c451319600b40d00540b040b40c0c1074904010800030482d0040d1020080d0106100b44d09200c0700c410f88007a03000e41642e81c1981410b14040c1100c410f89662000071100540e004c0c0d0105411151140070040715006d14220341d041a20b2a0606060a42e150f50b02e11312925014824000d0140c03143ea030400c002c1045c1c030011b5400801058480340d0341d0a018403600828016036010f0340b0b2500100031b105000208981c01070760b20041d510520391408002c000b00d010f4810042070080300800c038079004c0488900541680184103031642c07106514107030b80030b403070600c68054021b40b094080d01c040001e6a008100c01c1d50181d0140c45010300034480440485892180e1a401842e003041400041501503041d441140c446101b80c086503450001069075000403c00d08000c400050076410002e01e20304418800340564500c0501141c9600590302d00c103040901c12401e8690700c0381e6503a0010800e500d4071400c0c001c150300d040e0034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 412149109 1250 412147859 412147861
    0x7090806060d1401090812010b0f03191409010c0f1103040603020c0a060c020a0303050606040b0901121d01091a0106020c0607030c0213020406030515060a0f02030910020c0117 77
    0x60940d2200801428140300d40251074010051025403200c0020760412480200190003d0740b41c960320340e4200d190158404024080003140d06203580e4100e80c0f00c10080024142541c0d20003031004906440385091510301900c40849a000003204040b032401580040008170300f292880900400e01154a03c90034200300d04000f003e004440040700701d0381a0b410610713003d0b0f5140000300500345801800340c00103000340e00d00350070084195030220f81d55008520a40d020721041d240d1000304442030069000d000d140060030440002e00750b000d0140392500b04200c40022800c50110134841c2000750384008045000d94413588007008002044c001e0161290030005021007a50601a00a54503003210281c2030080340001056820300d40541401609954021700c001c843e00e05c080c001e000a50014822400801e040c1000720304c00750100200c0547d0104042c001c13a0800140b0081200d21508030307152041036010401c4410142d4407680b000e4032008280e9001088943d10210004009484024a40c400e000e0410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 412150359 1250 412149109 412149119
    0x1518030b01180b060904240308030106090e010609060c110405010b0405010e06070b2e080730230105091e0d020a15020d0218031209090c2115090709 65
    0x64848080342030702c0c0011400d9103989503e80b801e2414540c8481d100c7d00c00400406c004103c00118142d4081c0c0d44c805d16502d9070b0704203841c0755034028041ca001255030034009110291241c8040c0c2070b4203024a80a1300720f01402c0c4081070071070390207804c50482030700c00040900865802540207568944144e82007441c4c4215900e50f1850200702810b0a441036201529441c800f024584011154100304500840d0b4035070303581c010781d81d2948a44079540c25090590070f8280902c0c085018810441e98600140e40d801d00b8655072a013030540c206002203102d0401e150032601c1d56600348134903403046070a00c2c014020001401c245602d908808202c1c0c1d40c40317502891080061684c00700d8550340b490b40c880d010035100c101d1503c4d514040e0103400d03c004074481c40440c0e05141606402c81d82114038805400350780d08074952042c002042d2081c10041c0340c1085040004c96048002440184007291401c84070691914022480c20520328042d503001211100d45034180c4074034606041d01c550420818104402241c0c640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 412151609 1250 412150359 412150369
    0x1a100201060f0501050711130902060d020d051005100e031009030309170c07170109020d06050f09030a0f050f0705060c0d15060c03121407092c011518030b01180b 71
    0x141f49450244450341c05207029150703690000b215142c0e0061040b600c6102d0003107484000d4028500c01042d0600b81008500f01c10388a42d1102c06891019260780100307030946000390340c007800d02c1240036018456140307141b03030000d01e034854040d6135071082d0b03400302e250101400d00c08042c07140c0b0903055607d80c00810500d8004540000c5850131503822900104410009031070003801424480b42c040e40040504039404104101c542c4184e125104404207110a030b110603520950ba8060003015101060844d8810602507003e100a083e00c81418000706103014642d0f61003d08103101501c0362045501c0100b02c614009890b8010181e03040c0c20200f1001c4528600030008142c08807101001c0c06124131b0090710303801c0c2c82440d00401c1240c041c0f803002d01c0641c248843c0042c00d1300024400c0c01810081c84002c0f03a04200c4010a40c05036500074061100982d081c41d507a421556196401001480b400d0008504d10000c0c444c0e9180065010b4181c0450540c5011410b0035006c0d490903c1540e03803441c2c22a055495991 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 412152859 1250 412151609 412151633
    0x7091a040204450b030f0c010f110705100509010f03090308010e040807140d030f0203010e0711070e0106080a1812050903010902030f01050703060f060e041a100201060f05010507 78
    0x29540f50441c42280400103c0301440711800c05090082d100c000855080c2c501d6040143d0b44441a804c450324510700440b682c0c0c0341e4100c0c50305903001039400d0f4101d002c0244034070309004504201c41c050b11400355580000a8034000411032080100380d021a80c14810742e000911000408400e007824000c0080c99034000b00003610500419840d01e00000104040c4030842041c2c616440d44840050212540503441d1a0b440f045502c2301c0740002c1c1400d0a940c1d0f0800b2900070340c1d0498007129451906900c0d1038106a50000864011450500ca0a000041d00d0424001114028403094072085428104a0512001e5985904010510218902c2da09002920b0b07078600c0b4a9010041c40c00548074050722001902410003010003039458414680c400b4010041944943c1c0101030940341004240d940d1096021555590301c00c0340d003c01d181d450240c1c41400c041d0404a20054090000d03c0101d51905c00500e0190700e241a400c0180e544036030a0018004441d040005810242001e80c10038050b0369409652081c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 412154109 1250 412152859 412152899
    0x1e0e010e030403030215151018050d0209010e0c0f1801090e010305030a031109040905070e060d0308241c02150c0717010f11190e060f03040c0807091a040204 69
    0x1a10016201600440310042c24071802400c895591900301002041e40c0307003000040d80074400c9d0b080d001800d888c10081505545d94003070b210044aa2800c10f040440c854020080c0d100d88108110701155110b00c84010581d00e4280e012481c5032802040004012034841c2d0092859110f400006001207180042a502c1c5500c69181c0032620382c000c5903400300355000c0c061030540c20a0904140008114002c41c42c0416980f1000ca01341a940d501d10401049041c0c1c65001342c08201030780c0100d603148003c2c18030740c060940030f6120030040c3e418043c0411050304459404800301c0e4100310080c0110b1a0014a900320030ba42d68030064104103840c9941d503154841880b0318206407840200d401c0340c00c8020740004c9030404018904010074500f5100304845070b803000441d42c0c403040801c100c0c3c86207103004080001e41140c0c00f40605003010286000030015520141041c0d820140014002411000803c0300102402e0b2000f00032410f424010a850103501074000860b1050b4014082400740700899460400b01c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 412155359 1250 412154109 412154143
    0x3050403120c0e120f011104030b0f0406090506190506010c0b01050d0606030b010f0f0609060c03030b120d0f0f0c1a040c0807151704030e06030a1e0e010e0304030302 73
    0x4200303514107844410801041c00d41082c8262040081100041703100780050210400902206005411034443c5104d2400003c0c07142e030348640801c0790820021205680603100b5180000c04098540700c00740361850890745201141d40e5001010101f00b11806803030303009042820075040c15a0550303949920a1014000c460007098500c0c510380038082c0940145000351303000b02c40b0f030320b0650b141e16910791042c005000301700d0f5106d1a9000098024450f400000403150281e0f00c00403040307001e6804030094400003400590150954800d80c510300014441c0c801c880a4030f80300d4107000012400003a010742c03c0c4011a805000310342e19424003190000809050400c0030002c80055691070346402c4014110541100f0228440e5240104071020034440003c0c2415064407500d5000391034041c0100c2e8004101d400600083c0c500b40d4064950500c00059a040700100c50040354080494280c005220040402c544220741c941c01e004803002028418107400001e828040d603e06400c50300d000e0350714010242000c00d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 412156609 1250 412155359 412155371
    0x1080f010b030603100504060b102d03020705100b0a1e031209032001090e0c0d0906020d0f05010510080601080c07051e030703080a06211502071a070305040312 70
    0x4c1d502400312201e43c56804c0c030700304481e0130b1504200c2c000b40840e104180c01800610701090a160180344240c540d201541414201c00c00950107800012071018405000d0640910800e800a103050142410081d10040d0000320802404100200c5006c01e51182e03100281600c000d00d030240c0200c0018054940001d400b90f001c10222400f01e88461030b0307500203016000f03450701001920388801d0704907150410036a40c14468603181c2e1081d502d03244040d03032402001032082041e501400500d803c0840000c0c0070328401400d00c43c41c03107a210251000d00e183c0400499940d80140020716240e0080581860707245443d2043c0e141490001c0d04070100034146c900320b0301c00880c440781080030404c8000428140420070150308540b01010f2542c1e078000b46002c5001c90a0b200014003d145184122003c0318000011029462030500e102c42c040254258155000c4a074402d0b071081d9080140001c1c40954031a007140c04211640e410103540e0742c0009030541d4201410202480082940001c1e0360b019101d60a06c00100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 412157859 1250 412156609 412156621
    0x50114030a08070c0b040605030403081501080114130c0302040603060b0f0306150c010c08040303050721020703090e1302030d0e0109141c030203030702071202060a03020903031b061501080f010b03 86
    0x2480308117a000c018034460004020507400c0c1e001001d035000d68403e03102c00002c0e484800111034183c0311411104e002900d0180100100300c00e41d14402c607003510180000010800105060094480264119000c0380e00000c081101c6541403088500400b80d2180d02810700d000901c1f400842e210250204d44542c484013000311100e00008d08690f18501400d00030003401c02601d10140800d00100e8054020070300e40300008410902130031529524462003030800c107031058201c450380d0017900200d40136000c02c1002600800c4640041c00703d2801030396000c0c13859004109030b104140c41c184400d1945020001000d4404a21ba40c02c4101c4209072518480007504409080c00070500a0400c4c20042410307400a8000e00b06050300440114040c0100703509071603140d520b4400d8890541c2d81c84c100250011030030400482100d111344d0281c2071045008065a10f040c6807020320340c0041416010440c901d07007055090007401c0741c0721110500c6080d03082c2000122071802e0b01484072030150510810303a6140c00080002d603 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 412159109 1250 412157859 412157873
    0x10b0d0203180f01050a0e030a0206011a0702090c0d0c05041202010318050d0908010b010e0306041214030403050c0105010f0819020307050d241b0e0612040312050114030a0807 77
    0x140c151082c90445103007030303680c100e81c0c3c0c0a0a01910304a1243e450b24588200c1e84101104031515207400b40c0040c84142d2070034034140ea1090000544c1400280203003d103000590b0b612050760700030108180340c15158071400400108884451140308180001000204640000b07146103400b1280c09003400154512480190850400342c10030041c0b803409800118868172ba0488066011383e59800020014006840c00542c0e03181d8110141c1c80d4181c2c40710340001c00080e804814240ea41034607142070340e10601a8140751807a60416901240410b40115080d4002c003030074884c031401004603180390030400c1c6c0b40c1240591200b41d40319481c0000001000031100350b4030700300007110041c50041c000e2228820341d81005807401c008405007001007101e61140550070344c0c181c0945002d0502ca03e1751940d80488010040e01ca010145480540240d400d1003070710442c051101c51548038034042c0c2c03a00c440c0401249400360071510160031604a20803c3c402105407503e00154a81c0101d9205482c0e9594440d103040c108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 412160359 1250 412159109 412159141
    0x604120c120503070e0909070308160804031406100f17010e030a0e12071d04060b04050a0912020706050f0d02071509020a0b040810020a051308061b03010b0d0203 71
    0x15100315070400c514041c840d4440010f42c410100b66481145c021884001c0091460041ea0180950743c0001c1041c40400d020000030511116114804820044590b036031001e90b4001e54000c1d03e0940c5040e04236060000103014850b0710200050b001d60380e50742410300010803440340c3d008090034801c075a07100c40c074010002d601c8045420703091001c880c0c0b68a10804004c090415003a4154050400ca1607040340340d5000244450640706c800d441d4114440380c00b51802d404000041055a88544a150061098540e8800d00d40240412000890600028200904803009100c417074421035115040c10000c45501032709445640703101c1000c190741c0d0350044082c000680104180601802c41d0a200e40301d2031440760703219940c094402c1d2100c1d0101a50303058900d03c94006c900c200340c0d440d04000502c086240c21507005000b0200e03141009070610241219048460320030341c1201d8000e50209061004c100101030b1000b190210035103071a8990341c14522a10003a00600f104800096004004034054451212003d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 412161609 1250 412160359 412160363
    0x4030507141606120209060901052b02030103140307020d02040b0103090c081501050607080f03070306090f0506010806062106032515050414010c02060415020f06060f01020604120c 79
    0xa60342e00507440345440a40324648280808904045151100002c45000f43c1d051030078000c10840c140f9580078015200c5a2200340d0030070646415140c3c0c00c013140240007116101c16210f2000580b00e41c11440c2c102200d04e001310483c03603694010700c00000142e490104140401398192004201e00c1c40d0080140c002d0030120308001c10b00c844032100802d1901e000101c50500d010042c40e100100d0340d031082485124499041c024001000400595031520482c034000c541041040c9030005034265102c458900700d13017503189507194450302c48041c03000035a881050a134201c4800c4448524000d001a011440d210000806412104880300001c1c43c9a4080c0041420100403241d448221500070b40010011102806024a0b104a080081d2002441101950300755203003080c4140d070342c00c000b000642e02501d0403002280e01050400001c14141c0d040a10005032a00702e0b0000e00d036a99140c1c5120b401d10308000e018a004024403480103403282c2c1d000516907041b0360850a0081100c0c81644101d079511103081740 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 412162859 1250 412161609 412161613
    0xd090507120b190509030f130506071a010e01180b04020d050c070c0618090e010902060d1e090b040201050703030906090f030809150c25050601030c0803070305030403050714 76
    0x101c0000e02c002d0030310591260120381502000240039055010440382d0603a110380460f03005200e15039044141d50010428a00d00340a41c4941c140c3e1680010082d078804071048518841003404074604e481c06807200b9014080f801640351041d03060003c80c4c0e0700146074800e4800c1542d11140060b8464803180d045803003072561003c2c18000e40c6400806214241d001040c01c80e0071816090000601d28450361102402c0303a140c1c81c00549680c03502038072030003400c0c400c0c50091035550784000350310041c0d840d480201001c0340c0e54840451a09403070050f01c0f2000d05410400c600040c20a010100011800c242c01544603509090454039100207080c11030081200710001800b0615100c80c040a003c0c01010a28007148242c0d104600c513940d448040707464140300a900c14814039848041a46210f664020f080c00d02d9041c0b600360480110b41140755600e02203a48243c40c3c50708800b0060043c05075458410025100c4030004600d03061171030794020070f1071100920250400c070002c00c181041210303000c5000004192182 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 412164109 1250 412162859 412162889
    0x90804031b06050d09600506011806030c1808150c07080d0504122607020a06020418060602031801050a140319050709080606060d060b030c0406030b010c080d090507 72
    0x714035800b10340c0499590441c1c1d151441d40c1d604401044030300c0f901216004007020310101b070501e002c016110161042c0d0600084920321000d01500c0200300c8018865694049456042c2a201400420848401468110500d01c090044840011b8240644a0041c011528903034450050702c000f4007440c04001c2045200083c0c0200152868110b240a03900903140c1014030700c00010f082d900b145803012030301d810035840500403881c0782180c2c8000350310160a00503208640002e030390702d804981c45900301e000d1407041610040c00303008951041901500390740c0000d51515140c0c0d40d0b0301d521036504900040c1007103800999816005c0c424000c3c0d182e8055041c021079202d0034008407000c00004648241d405141ca4107000850746845410150101ca4003007024001e039440d96428080135522085400d52425124800003514002220040d480742c105400015102e90a01c03400400303a5010f148010304001d4101c141c1f6011441030f000f21408581d00b004c001800102c1458000d04004e83c5500c52039010f00601 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 412165359 1250 412164109 412164173
    0x110403230601090f05130b0402040b0103022a01180c0e060103021605030a02250302090c070b04140f06100e180d022410030b07050706090804031b06050d09 68
    0x28202051038100f104c0f05200950f929440201d130300090b441e004c4c103117001c1c8002143c00342c10258070202c071501062401501c4c03c60b00c2c0550036607407240034601240030340e608401014003103002e100b15401040d4031400090081484d8481409880d15030080700c03041307080340000c43c4040e8002e90403030300c094405a100700d86807081410480d850740c1241040401500480f01214a40b4030b0300182900d4502c140024012420300b0b513000d100d0780c43c0f4014261400d04a04000320f002003042c04900d01d11603031154986034040312308002100e0400204489000e0b4030360250f03081c0806c000c0031811803010f69007803000007a10340d95140c042052140602d002d03203815002e5081103071082980401d125058042000fa1022804c01452582444000c11151010310f103ca0440c1031001509041d01103400a030b03680b0744941040c170b494550500700c4010074021101c1d1103001408104100c044c0000c1c0c104620708881040035245842005000fa20400d54011295a40c43c02010100316001501480d00e058100660030660a40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 412166609 1250 412165359 412165361
    0x10110702130b150403031206060909020f04090e031b0606090438150307080c010e01090b12012309150d050f0703110303031005010c080d020309100f11040323060109 72
    0x71380421b400007140e21b0783d054000d6050740100800c50760f80d5500c6a5a0a14042d0b0303080003508150354a000d80e00003000002200c541c40c0c0202000900c10345c1c080c40d600e0300030002524114040e0401144160812404c100c0c03c1d80e80c1c5a441369026030002c600c014094090601542c0d64134144129820414100f0340340480d03511041429441104010f0b200d03122610b240b0100759603100207120b29540c1d90308c8504c5c0c180707083d40f26003510413403d07006040454403140c84031b041200581204044c4100d6080940c010412289a1844144448014001083d052900d6008103101d01c40051410003c08508280c281017921803403041c1c80082e80100c20780702c0d0303036440051507900c940d07042c4425070b80010100540c000d07901d004412203014040c1100e9042c005841c0030700544040c04d00750002d03914280c09201100843c01c1600083d4820307941c0502404020010310048001c4449000076a0905071611b04055160001c0804a501752600304c80e070a090f800016003603900810310b0189043c401d004002c0000f45104c81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 412167859 1250 412166609 412166617
    0x8010b03042019052b062a0e09060d050303151903050109050f063706060e040f0510050415080f031209030313030c0f2310110702130b15 60
    0x121034943d41440e6241c4903405070300c481803034049402403c58911002864580c0650302468140440d070482687c243d0030702c0c80b043d08080312107001c1003400e43c07500107030b191641190340d0100c2c0484030560100050784820703540b030000900ca6121100c0e006034103036980e65004201c1600c0d0401032032090416449140090181001d1007044620384600f0ba8081088040072a07500d12a81c4540b42c0390180c90310402d07541c0c445d055901074100200e1447c1d402c942ca82c0185004d0400500616100d035441c190350101400111074001030780517843c52411041c0008000152811011298111004950107034201110f45034000903601c800c15510420300014609007021002c1d00016a43e8051b042c9150b4130010f50640300c0c0b004581e541d064440c1c41c20450002405600c444445074012424004500e0880d035540c400c0800e088944200130307491501020909a0800000402003042d80b814000041e40d419520f5035400703001c0c0c0007485884001384c0080e0820541c0c0c8900c03c4004001c0c40700e44460700500707000c90070b940 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 412169109 1250 412167859 412167869
    0x301061a0d050a110a0f2609100b010905060d0e06010e06030f0106060e01050c010f1e18020a0324060605090906030604030c1b0b040801020408010c08010b03042019 72
    0x7041c10300050503851144502006000304030405440d0440130320086494480500900050007e8a8506003420824089445000101c802040c62600703081c01200c6c40c0101c5100340b4031600d03041c008940a03590b40041d07003004440054483c20303211480000410060200750380d868846100314000050303a00e41b012581806800103909584c1d516544020301400d07640c1601902000c40e041c1c011018182d442031340140054a035a200014000000f00c40000c1501d1140200c00d460510740002010f0052640c480c510f2070000385041420441d20319400702c5c20b91429480060103c0c141c124800318218483c500340702c8020741c0d2110410200381c9619000d00141c202481031342c000c2c1d405000040e40c9040c001540d501a50700f40d108c0307210707141031a5254944c10f00301c401c424980204421740007441144241c05007002c0d00c040070015031a1350800d0905821078082c1408003041140c000e00420120380c5210407607800541000c40e0250034124000324940542011461f944c0001306400400d545849114203642aa6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 412170359 1250 412169109 412169111
    0x1020c030a080609011202090403050c030a11240f18070b0301030b0c0a0512090309030f1509070612090303150b0c010e0d02030a0e040e1f0608070f05010302090301061a0d 75
    0x103141c0d8070a01c13401d48002d00442d608100800d8a0a01600e044c40303080e61311511914010340303002103812929045810450301100403824002000e200444140600c040c0503020303044080c00211003405d070b0304071032402800c8003601503034003030100e107008482d44403c3c2400303081d01045420040e03462034011001e034000d01c070503140902542c02180706040620101c2c0e001d90b100c0c0d0b036083d0502841000c800030345000600304803000d100c00c000380e841f070303403810700ca01c03c000c203903040140100c1580220001303c00b1400403c9202e0701d4001101c1480203503041121244003004540c00002c203440306140581c01014040d011004440b1140000200120818000c082c1200704500038000380c00d9848441c1d5030b548401005801603001488244552480740b02d4200490342c0040002c11461002642a03040111141050703800142c01d41c1030f18504041802040c00401500000303000c03103072800361078031204429802003e04140e00094011001e90742508040007402d620b5004594403201c882080ca01070348504103c4400d0303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 412171609 1250 412170359 412170361
    0x20d02010509150103080a0e040f090204051302030a1e06020d0b0f040908030714040906030302340902071401050a0227090a020c0a05010504030f0921030f0306030501020c030a08 78
    0x9500100704450304a5060000c4240c13a401c3d50384960064000c07281d0301d801c014039002c1340e1070141e80310300902d20580c08410002980019a00601094400c01402195840311400161005031400200955007581002d500c000711024030208200b5251500d00140903580045019500102c141d44040d100715011195080e17003000403014441a90315039030020302164024800102064047d0800c94852401200081c3c502602c0f00e10550488074140c00035001a88400d5206013214110b91854000b01c078505020340c2e01400f407568411024540c1e000385d06100382c0114142d000c00811000c0b401c2210580300081c01140b07450071084001350040005020512a40c510f15180c40004074035490f00100302a0104032030741c1c1c036202c1c0c00c0c0c06584401800500c07072182c00a404c02148080c8a1580036610a50fa1296140e4040c58011324803440d40d0401da0010559002801c075110031925400b594903414207010510700110242030b80288155440640154000241c04030003d401100805110344140c8a121305 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 412172859 1250 412171609 412171621
    0x3030d1a011719020a111209090906090604030e041404030c03030f0c0813080f0a05120c0408030a0c05340605070c030312020706180303060e070507030809070b0406020d020105 77
    0x5181c06580c00350070718000f0100e201c03080e0780d50780041042c484a803d102d803101204414041c9424411180ba002482010818001e68a0b00542d02600005940f0040015040030050300340c0340c0340080d1004041c4690788500f001c1c2c60f1290382150180b011102c0c6040c0b0341d8901418068030620303040f242240080e250a0110300e0400d15441854907801e00c95442d071780d4580d58810001c100c1000f5000603a420b0f0000c2c00303040c04802c1e0480041c0800e41c01592240c7d180c00d07085140101c03d00000e05003813138101c42803006100b1484000705075000105245407002490607203040440c18900c5c0303604045172181030000e4083c140842503d801c1000945000710203905a501c600c115018001d500e00109000c450300b6040011030720403082049a000c0400c03005181c603e09984100403602d040000c8030032444240c00075010b041c2c1500c03500000b060001c0c0108030519201130014a140301d0b800004051060010100b552240c007000f41801404410440658640d180d4101940d11400c0c41d0084005608040005003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 412174109 1250 412172859 412172897
    0x5010e1e07030209060315070f09050105030f0a090c0b0c031b010908040605071106031005040b011416030509040e010504020a0803130b0a030902041b180503150603030d1a01 76
    0x4810300e0400041d0010506550070001000c0000c1c00103a40751044062a03080a1b07150300340c0700d02170050760f1204050540d6408000e803111100e0791140381070080030701c100140c0d0740d507030f00c44258004000c070f000013010318032854400d626101d55041744e0580c0300c0c086060104c10702c000005040e045124000701000c0362540b50201c0c00e035000203800801240301800204206401100a0020140304085596801200c8004110942c1007224140e042e101f8540c410400350402e485407040e0b070b280a00e8040d190100411603031b0580e20848030704202207100c040603003041c144903100b590740c81000180280400e4004c0700c0c685d070281c84140d07801d900c2028088400100c4d00400400c44644c3d48018210201c4507180044c402c95a404c10640c840500d0f031900c0001d40107945900c203131847c0120003229114080c54940d4024000009401c040341d40d4060964244803542e40003500c12060401086490b00541e03480d0b001c01c0c00e6010b0300c5c00c130301d14a0341849130481020081d169a030ba00070a0a0340ea200c461007220000382 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 412175359 1250 412174109 412174153
    0x2031e061e041203020c07080d02060105040c08070c021504091d010c05040e0708280c030b0a060c11030a0f050f0c0103090f0b04020a080727090812070c08040305010e 73
    0x1010070145081c0007240f10b010340c016007081c075170b01c2d4140c40c010350361403044500f8600c0242030580141c02c81001805a032801d40305044800145240030040c40c900071202520000f00500085c1c468122240d500d5000c0007aa070840303020b001420001e00010b000124103400a203040d0a400080354201543c3c40d040754030403000d88049500c0e480d400129074840382400d582030f8030007400b440300c826000e10724100e40240300424070203070f48560302d0000750301c00b003a00b0b0090480d030201000d2481024000b0080010301d500044008000b90041c0342440c90941c6600003920f81182d042c001041d03554004610303003c2c080c010807848050320300c00c02912420076a541c0110111191014000d1402e00c4205416001c684404441a40035202504100d941074071943e00350301d080c000d6400702072130707200c1d1400d9018940c82101550800c51400038050019110136a01c018060242d401c0450056010900140f0081d00c107080e001c0e2841e8110800c565115120304029000e80070a22a10f1150300ca1001800c00c4a03944040071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 412176609 1250 412175359 412175363
    0x2010506010c060f0f020f0c0f0105060d2406180e060f16031d07050114030f07180306021207030c090b0f0a0203090402040806010e010b030702120702031e061e04 71
    0xe00846581e0300c041c02444003050040c126176441405a010034070b144000c185d046a212900c80d00e07000c0c4080340e240751050340c0f208580d00342d04110600c40161036180d508040340341e02020444814101410469080b100010480405402c000c4000b80d07100c1444038528841039060070900c20440c02c4165103691314016a450180080f07040b0000c1c00c1d2589203102d50b114041d071440c001c0b0f0072110305111020401c1d50108407200c00d800c0350030200115a009000c1141140c11040c2c168210324000d0702089047c0c8005100030203101116030000c09488400d08500069544050110f480351001d40e04250000700449400e030120340780105151303406000b00c4203007007180c0800c10010301e8054004a101074039084034880d0f500754032082c08003464503941c60016102404d40034009120039803400300d0319900b10070181e0002c1803885041061080056005c600741304844400d000f000d940c3c1ea4684042031502102c20040e03026a0240d00403088503190200d49240030b13030a100281d9144071312520010121010503a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 412177859 1250 412176609 412176617
    0xd0501050403092c3103081801060e130314030106081b03090703020402090112060e07091502070608040807140601170d02150612062a031524040e01150201050601 71
    0xe06884410150f5031429a80c1400341c03034980103061043d812040e4543c1c41200414400301c00c20141d50301e08448c0d404090084c000a01807585001d100201c0c840024040700c2e5842001011030b0181805101030400c1e4004a100443c1c1d44d42c8c1d03c2c03000034100041079480c13110f842524800391080c0001d55040c0d0340500f01c1c50020306400707403559082200a5101038030b49ca0500801c00342080704030b80f0a10602000f021820301c026000e180021005203a030125400c10706104056050bc1c240541e400904201035500d02d041203400c035111401c012038a170040c0301c4004c0200d66044255104400041506810ac1e50f46120005e54982240c00f80c680b26003405e01d211006038010001c107203d007400340e0030310340c1c010f0409003d2f00480490701e01d060f8100301007107404045000a42804070342d5070003503412520003942a2181c96055091080d81d0048186085d8446481400c0d002d07601e19120460124078049600034900843d61350343d4a0781d101a00364001d2151054840303a1028410b0818018022a0b00c03078041651 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 412179109 1250 412177859 412177861
    0x30d030b010806100f0807030e0a03091d01230d02041803030b06041818052a06040b1c0f02030907060219171608072406030c12020d0501050403092c 65
    0x40488540b10000c1800b000c064460303003040701c040d805102a410ac203000e65564001c1c107041000e0300c000781212040c4842c1c001c402400401080080514084032a0320001d54242028070040c0015002c0728800406540249000442924146100c141c1003085101c0c1e00e040c04002c6001003000fa41340070714401c0440192000809504240d000e41c03040d040c0d940c081c4c0103042c9050180d00c4843c1340440100340a85400106080f00020120301600250200303c203c2e0410b1034141800f486040500505168904100700d854480d0b05000e0640c100c203850200f00a400c644902d8041c1038141d88035414820600540922070342c12140320803811042e02102e820a210520b42c455913500a2410383c01b0b10344491030704008085200000301540d00408201c3c0c00380c40180000c0c10b07003002c4042d0b1822440d08200686241000401c001201c981c004d40440340031002c041d0340741c0400d0000c00d04040001d038005009504c1c0c4020001056040607002c2d040e1040c0300350460010700200340c44441d41007aa02d04c2c41179680480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 412180359 1250 412179109 412179137
    0x1111023070e0f0d03030e030309031b070302010903020907170c04090c0813030c0201050c0d020106090605040b03120306040b0a0306050a0b010206071409040f050a05090111130b090f030d030b01080610 88
    0x1050000841740f04c0d260014101e205070303213201c0c11130b0002d588404c51038000040000c0815004540540001c00070405040110f2450703001030124003142c40005d014681c0c80000030a424080e21106929246000b01003480b403601048000140c0c0c40350042c80d404901e01404408001d115000300c5114100254440c1ea40f007025403002d407544c142c034100490402070200540302404501344681d0424115580022075090308098210098540e01d41095008502c0c0c69411043e0b03503000201c035541c2c040c505202c507a41e80c6038000030170060321a050b1002e410a2200400001b00f12090748854480d00ca0b0300020030002c0210001240c6a44090f03400750300150034a400002c003441d00000504030080010000111a4002540e40056074800c540020700950341c3d4003042402032080c09034525140441d06002c0c6040820800e0441c00040d034020036022540201c0d10814a0301c54011107419290003d040310300e2140182001009402c00030000c90000740301a000c074450b4103280d8074101012140da02e0302c030700349502c03030b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 412181609 1250 412180359 412180369
    0x201110c0904140f03070f05060c0901080a0506060c03070c05040501091503030e0f0a08011505060a14030c0409110a090b040605030a050a1410080f0c0102060601111023070e0f 77
    0xe82511080b90245070010100c2c00300820041001c43c0c462040300c1c1f00c0c2d401a060545c140000104104030380c49040184144030780e44000010f5114070081c0d40000c05881304404500d55020751040b9203018071002500304240681180380204440f0304860521140c2e88407103244080c3c568030300342440040183d00781880000c1c011240680c1e40c20024000c0403c14070701800007207444603103502082690f5510280681010204018140905029281a403409481480040401239a84c007020041c0b13401101040500d03101e00c0032180200040c0400b0300180340c003920041c0f8075034041d0144178045004004001402e02020007560b040361210f8413254110340d91481404003900300200090303115507a6001181b90780180841107401807101d84849802142810310322498042201025034556010044980e076581c2d001415540c007000030310300b0701e4119003408141880c2440b058820005c09040100c19403d880b001d102081d0003071840c1506940710f0726281800c0c9c1e12441508603281d04150881d07001c90407030400d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 412182859 1250 412181609 412181633
    0xc090617031806210c030403270909030c050f010506011b020d0809060c011b0f17010512030415050a17090c040203090c060301090903230a080711010f090201110c0904 73
    0x164260310560301c0c0701d13801e00d40365040304803011000704034040240028954020030350b000d00102da418041e054003c83c098004242054481c0d05d0310603440b000b080081620a000c2c00c0141540502120070000e09210064003902d011141240000c030f24400c602945d4a100120041e1a80c01804495842050740c445103d560700c80349035150000340410048403002c40c00d01c1034402d11448084145500c10b054100240292510b03c02c10040088103e44510b070101664046130468804035640321141c00c003503080f9820360281d40e04c01c403031041d80c07043c00c0581650000e00905141c040d50380c40e62174902c1c80100c42e03240408240c0311303c1d00035400300001a006061542c019900003036410115004800c4080001c1c02030b41c02604070050480e26070111a04050308800070155040b03405146944541d118810710705240217110700801040b20b543c010600791401021001801c0600704004d2002d0070250260b540500840c201c200d00003281114090401c280100b20207a09134001000c4403819101e9454141109203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 412184109 1250 412182859 412182877
    0xe030d0f18030807060c0e0103060503070b09010c0c0603060305061b09150405040c02010f15030f08030403090f060c051e0a1502190c06200a05160c090617031806 71
    0x740340c03107010000c11000805440c2035031003260042010449a8001400c055100c03030404d040c176060a005100f65a00445d00b10240d920b41d079205501d900e018401280d00175444080540b5843d1841000f26515601d50410010f8a0050048030300580754107001c130343c0030b144040d0585026841800074442034a01203001503c04210101c110381400d440790005011540d00000d18000350399a0070b003040a01c54580101218181d071880203440c1c9501e99241c001c031804030318000919078880000058101070140b0308403c007a148000d0401090360719000061b003e010039110a6030740b449490030320590302d074180c1d070b03607140d17101ea584080c0c00400255130b11404103810080700d0103013158081c0008120024010401c044010550b65001c45030300403800c002e002c5440c1c640f00fa0402d03184841e140500d840b120000c8074840700b440c5c03401541e20389c0800d903401c0c001401c030140105006485e03400000d1a46064200c001034803500e80d803000c805000c0d03221482d50707446442d00300d03106180b0140e1203078514641900a0a4408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 412185359 1250 412184109 412184147
    0x1030210090f09061806031a07050c120d0506040b011b050a05120a0f020303041101080406180308060f090f041b12080418090201080610030b0603040809010e030d0f 72
    0x10b444454400010340c0c01e8218801076070340c0f02000c220f41d40c1d40b410514501d0b07403801800c0202c5421038981c0034000345102845a0b4918110b070100b213a2034812401c071100d401010303040da003494407a50751580740f52b805000f1544e5a1424800807549615182c4100d80d403011058541c0d18607002c0892071211030401520b01600c0a02480c81c81e800401c1d0140a5003001c04460040c6669403148ad040142010100d130b81003104540c010300800c00042c40b180d8100403801024200f8800319a9140340800144c401060440e001c80301140d0200100354125a0f554040c0b882210b01000800100e41400b00309002118800708144110001c1000b0811202220b4440520700001a107201e442e030041c1c1d01c5500d807000084641160010f4100111090149401c090b00c0308602c0038002d0036070940000300b0034400a0300c0c9912409a8010f0581c4c124060703446071841400280040b91645083c0c00d04468581182280030b000c9800c80e1420844c070b1602068072107090b007940d240c4095842c10164200c82c210300301040440c1c51 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 412186609 1250 412185359 412185377
    0xe1b01030b330403080a0e0402041e05311109030d05040e0f13021905030a0b040b01090203010308180307031401092003030a05070203030d02070b01080c030a03050301030210 76
    0x1521024154844061039680c8101401c10074565654501c0d0281486070201205000900010b01c0b17070821501702441ca440c00e03451018034040010001d100e03e034000311144500e551704c240000e0315840301e002140c0c030441d400f08502c5040c5109140d50001c1000c00303403650340c400004210141e038503403240d058505c503201040d04113058000407034544810b200101000c41c001080821a16428665803948050741d03441d08a500e040c40c41440c400541c500c82d001344541090032441156014401d00c1c40004c1030000c00b122055044d0b0305000030151800c1d901030f222402010000304490b50b45001b101d048907408044145481c4c05134a406a9412080c0303125a80341c0641030002021441142c28440c0b41043c902c00003401c000249030003140038075480000000781242910801090b5000b0043e518a0722260901700d542d8401440041c0c118480d40366030a030560b2000c82d454040c0301c00e12103418181d036040b0080301c810081c208100b40da10f1958000c0200084c070208010320040c100800583c200501c0f0342090b20075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 412187859 1250 412186609 412186631
    0x120b1519120606050a08030304112407020315010b0a1407031b060603020a0b030a051006051c060503011503051b2101090b07030e012a080c0c0d02010b040c030e1b0103 73
    0x1a9422940c03146c0c540b64000f2017400103200300c0c6c0003048001e40e000c95010f00c144490010115504028102854101402003030a0341503440034000e4030890802c201c0000119070719400f40000c03a400a042450001d1845600404050a80802c441c51550103441d0781e80c5400e071301d502d8810840c92a090480317409869030b00000041c1c90f8030032142c002d820704542d05616460080000c1040f9800105803021a001510040000c103802104440c040006404101d240080d40004000a405030380e02c448e426611b421403000314022080032200a480c42602603580c00300500e1680d6020140443c040380d8400c800d01c0a003c180e000ca0f00651000240100c0013058442c0941c40700e03030410360119050808a42c9407d11890030308028030400011202214001c207000383c2d40412080c0107910b50914030248426103000c143c50300c4e2081d0a42d40004540c40c00c40b41d14095404000303000e407a400303086500507400c000303400c0403040c02070140300e05500000b0024450607080e0880b02c0300019140b40d260303061590710490198 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 412189109 1250 412187859 412187869
    0x2060126100f0b1f12020d06030b1815160e151626220f06020f060a05011202010c02041104030803041101030b090a1104120b151912060605 61
    0x803121806100055140d188000e10109031481040d1440c030071480104100025002040c040440407030000058403244940020002008c1a81000e00b40c0c07040181080705a609032030240d4552900b00c0181d0f440c80e03402e40da91051103c0c050b1803100441c0981c1d1114500984581d9021001010082c040014440d01200140fa0f507030011034140e003038011882400c0300b4000c40207990004d1a07407090740b030002d81c40d0300000b050890040400c00d04c1c0c0070700018500740c4000c011004820140c00402c00c0f449540356030300030280d51814400b110944500850000072802c010034854141200c0a1000c00c0462107200d134011038604001480482c0d00c01c0e503514801042c001d4031800b4001952161914942e40d06040c02c0c07000142c409d100f045410141004490b10482c0c80303985885400c00c21034030011030b01e040100d548006a00179908038603103442b80c2440c00c40034044006c0ac40340c0a00c14040000a00315041000c0c081385081486808040e0420301c2800c010302442c121080035100c0c092000014840c0d00e50380012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 412190359 1250 412189109 412189121
    0x30312070804030e0111030f0f0d06060f03060816050613090606050c0622081c0510090506030d0f051c0f0b01080a14070e0f030106091b0206012610 65
    0x100107201d90081104158000c0c501000c2c190703003424092540402076002c2d40d52442000740441c2e0201c000b01740d6084d0182504182d6070030301e902c0705041c040c080e00c8440c014000281000407000203800c3c42400030780ca0740c0c04035080f0f190380c04100d03070fa81e401401c02c000c0c040a40d0060080030384d1108004000076054002c0d02c0b590025100790340d60144c2c0c0d1160750b10705911344017002c0d00ca860440b120400d0510318044070350802103004d40c8501c1442d207072422000d400b000d4800e003503038204100e402e0400304900c040903400c00d9010348500c04401c010a46074402459942c8410544810100d402c800c803100240b80104d0103040703402100c030044444510b01140403400e4445041c5001c0d011512800807452968100034410390190000c4030401001ca0440602e01411034080c10b0002840128141c0924a845840702c81c0110107014001340303d07542c0d441d4240002000d143c24100003c0030060140480c0b80d102081c200d040310103c01c915031a108207034413035503444100410b06403410702c030301c035804440c204240c0141 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 412191609 1250 412190359 412190371
    0x61e1801080f070b0318070f0f090c0c030c020609120a060f05090a0c03020d0305070209090a0c1401050304060506010e13050a0f0b03030a0806010e04020708041e081506030312 77
    0x42125490034488a01e0960070b10701100d40d07a048a4410300100c9013160540f60701034041c1103058034084822a210742000d4031608103060740540c172070f0046018111000a00103c031032176001005081d031040300c125030550140c0e600400082c2410340c0c1c4000f42c9070800141150000040022101d8910140028035211580074101d40d003549404c1680c4801e01c1c10b10610313910804200c0580072a021a540e662000c010a000003445258001924410f061068080e140c981e0b5004d840030f41c0b5400c1111381c89036990340702002181c60340744501000c0360103c4148a03a5402000c181c444030701b1602c50346e6603000030303080041025040103122103d49050b6584c1c5000b0300d030990000710000607242041d1860310140c031580000905d0b1f5904007956a0070b5501c0020031113800c0070062801c4400c0741c40f0140125021381a00b501039a0103400400e40d48240a04071004100f256406070418514050b20990362404081a09c034100c001c1e0402c4500810340d401e040c4080303030b0105005040e41d20f001c2c0211510010040c0580328 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 412192859 1250 412191609 412191649
    0xa0305211b15090c1003090512030c13080c131805061006080f040206030a0b0114180a0f030203070b0a020a050a060c0f0915110a05030f121b03061e 65
    0x260101c1c5100e04101d508041d43c2030190000e210074801240782007900e040e82c0c1c002c1554540c0b0b821f082c84801d000301c082c00c65009080942d01e08100c2c0b44055650070180e500d06040350303903220001c0c1d041d4000032002e01840014010003402c0503800860002018104d00301081c041c0310229000c0002c0041c01038612454001c031a40c0d0401b8103214000b440400010500300c00702180600b40005a603825096941c44107003404042801d4400b800100c1d40800c848095103500840400c45c0c8603000190010004005001c4d5100b022083d955000c2a4890b981e610001c0c5d01904441020300001c0c101034010f00380040507004946181000d6540c06261214641d01543c906a852002c0c081180d4000c2d183c40c00d0400c5803030450903007414a48018500101803c06905009948088410100c020301a40044ca40c000707040d6070300d03942400e0740601d01e94400d64841200c11304100003d034a030300801340020b100030140ca0305107042d5680d510500046181c401d4000c0c001e1501c400f040b5595a42e0f81d11001c900c504c1c4000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 412194109 1250 412192859 412192873
    0x503010903030e0d030b150a0c0203070303031d191b0b040906030b0609040210180506070804081c020a031209060518060907300804080c030c0a0305211b 67
    0x500c80c1d044c11440e0340035004040c2030044071281a680c0850b600d50b000703101803440e69101c054010642e40201d210600070f41500a4030400014160103078040303268800200712086034a0540c0160584800036001c111034155403200b0840080b50011045500349050360a5071508d9640310342d49180c103034006a0282c1440c41d107844040c41044020343c1101d81140069034100d485d4141540002c2c1d055074003001c940308003c104a5645420b00d02c91520b940141409000c0a0b5036505600b001d00c1d06601500a07070b111482030b90105907000c9022404403504011a9018140d01d61941d60202ca406041442942d1407a41f070b000008046010351080b2409295209614121243d40380d001604120000b0030541c5260070034001002420b400800048240141c0c1410207044528100650201e80b100440035100c4040490003083c1140c000031840503003e802c80c2207959800c0c0ba40200100c02e0300d14007000701950400f880000003101d0000203107110b41403a0301b180741401184110f0800d001803441c075180f005da00c81d034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 412195359 1250 412194109 412194131
    0x70b070c0905060607020411210105030c090f1b0f0a111203011202010e0301091e0312110a05160209070c031205010503070608040311190b09070e01140406050301090303 74
    0x4408000e0a05103028042c034900f90002070380ca030041281c0640101e4454510310b54180310308080f9000d95022010402032240d1307004000303041e00824040d136800ba109840c218141840e0000d0f0445c0308518601d0b040c4000d60741c580800030740d0b580c0c1c2c80d50035100100510603c25895803082c060251414642c0d00d02c0070003c045840503141150018000c10f0404c010401409510180c13070342d0700311a64081c00e010615005907008280184a02840a8203000d1a03000350550101c007644843c81c124001d50707480280c07040d20078030442122f00103000e2007004601000701c2200d02d4000c6018110502d0700040410600c045074022410340e400445035500003070003003801c103010181c01c40d40402502c03030302110411481d8181004a07960751441c2c040c49084c8003580000400700752044281028640c000c1d4165001074201c22944006120035080840b5011101800101c402d00b0010340e0380d088800b20404400b03140d207002d2084003030042941c0601c0c0c10545411010905480900400d60000d01c01d80d0001070741e2200d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 412196609 1250 412195359 412195373
    0x30a1e0318090e0c040608030a0c05031b0309030d020123040809121e01060e040b0c0f0412031209020f060a0c050106080c0f0a03081804020702090405010e0106060c0b190e070b07 78
    0x1100d41c0c4d92003140780580070300a440c0004180d4048030400e00340700c0d0050203941411072541c080c0c2a0303000500d42d06040c03019201c400c044041c0080300d00c280c1c105e5a40881e120810b900741c69141945014102d82002080d007104507186840750032034042d0715424a4600c00c0c0c808542a0200f800040c011540a600320320b001c01120411480c0004440001b00b005509180c02c0c509106e03009440a8050920100802c1030b10b4a900201c501e481c680030303100ba540716924408040643c101d80d02c1a00440c0b00d200e01c2c01f94005e118060b50b0011503009112134090181b800401070b503908003030990b404000700c001c0345a0009100740301e0b61014002d040300500010001e0b00c00c100700f8250140c00a4014003441ca0100f0000d105441903400020407008005640034414010800a0090340e4000e51b01c45480030520003400011f62009501c103c402000340a96038844100350b55005000800a06070304c080701c002803d0201010750382c850922644008520200244a803c0c40c00242e504030001e0700100140352002c00c105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 412197859 1250 412196609 412196623
    0x1806120304050603150303130824011203030908130f0f1502060a020306040207080301030f0213020406091208040f0e070206010617191e09060b030a1e0318090e 70
    0x2400852038141801e0128816000281090200c2480e820015005640900c10780316010841144503441540d20441103030356081c45034250b154800c0301c03812003480d0900342071841d040e6003846071143e4a03506141e50403002492000c4041e03c450703409002c10440c1c100e80d5101c00303009008600e142d6110741e04150380500b41c81c19a504c06210500010001180070b80c0210781194088884540180c49075030b42030214004c0d1042c40d9009000d90700000010007017203d0304010300d407014000c0d202c1154001809040000300e110394050340010910345c0030204084030b072100d8050300d1548601051030070140d0791406c01c0041813086d0081260a03141b2010440c1d003981c1004181e00504061610244c14070941840702203031100075280c0303071807041920003195540f503403070300401f044040768000c82068544195404000300014141201ca050910181a4180c40e000800c1400795070030004070f19003031b0001d013540302610303003180821002d0084440d1b42c0700c112a0014040c070010070010348081041c80100c4007190410300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 412199109 1250 412197859 412197889
    0x81608041401080c070f020918070312021b060d151503051f151b1a010801060b0301140409050f0109080304110d170a0e130219210c09051806 62
    0x4c0a20501d004505041c048a0603541c06442240c583d03200c0508105401c200c1108000d410b11440c1d00003c02c0020408400007200300e81c4e801c0e1000d40c2c054850500c00d11881c0c0510a6110a0602c600340000e0b03c65446101d028110b029110441e6070380b4503103031030264031821500c00440e90751000c00100c0c168270058000e8004004000c414403d00704a03c1d0403080b9210080441048440c002c0c09240d0050003003190600d40e00044d9401065030001a103010315034090040700521f500702880020f80440e0030054906a80042c0501036842213400309000c0180088041a00c0d688103aa11051241500780b0130003480742d01450300381d9601c2c50142061010400d2090b85980500c0c02500d1000100340c0215002c10803074a10110590360701404001280d19074440c0c401d944e0f10200000031003030601d01e01d5000b090b800e40152690f99050702c0d1a50203a40d40000359403c860302041420384500e10038107691042558070301a040030b4409a842d500070581c20000010801100038500c41403208900c1e10f0a0281e84005e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 412200359 1250 412199109 412199131
    0x8181b0d050a080409060e160e0d080c16060c0816031b29040b0403030e24160e090703150b1206090a0e150a0929060a0302010c08160804140108 63
    0xc01c000300110002c41c2186403208c1003052a94042a0319541c41e298141030070703001203429071265400b8281c603803100800c8201200828000e140094400e0298641c1c24440390042d1100d810903d10b0450044d03406003500086040202c0001401d98440f0794010104600740140c2c1c10142050420b2800350b03a0b08240441c0020001c0346208100016950794429075006905217408548142c290100c1440c2c40d800040000c0d9040100d4202d02e09a01000501881800c1c21000d490719042403413015a202084200303101c1d00700d1a007600180300740b030081e0801400d520181582d4002541e40e940207103c1074002c0f5000c1543e102030501800118681600700d51341224100d40308110400000511654800a403a50b0325807041c0714100041c0000800e40c8144040340c1c002912006214081e0581d40d15481c440000040764942074022480c41c0c203040401d00144c950607110301c14907003540d44502400e600b141d81460f014081c0440020b0005401501034401419030030743c0c3c62001014034001500d104c0c002011581c1c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 412201609 1250 412200359 412200361
    0x2040e07020613210e0603131a090a020616080d0c030f0b01080a0f061d0402010906031407030509010b15090f0301020304110d2303030708181b0d050a080409060e 71
    0x10840340002c8513031002c0000024008600084015100c0a000c9011194040710120030000c8075804000c12a030310038403c54500b030b04203400c03900c0707009040d40c00d8a11480071752025030300d076005003805c80080c030014903a40700311550030025641d1010342d0381c002184207900c10f440700c601d802000d03010300444500c02c102c01020b008580c1c510000800c80c060052014464945590030b01e80c120b00d0755441a000303404150b0880304241d0031070040301d50361442030340c0480c0056040d01002480c01e00c030f8401d102d040030072420026100e458848048000d01001b40c0000d003c0c0d540d98156075019616030002e030640c000f00d004860340300c081344d40800005045c21400140240d00400c200030000d000001d45d00d0b250042200c2d44c0e0205007650034401090740d4042d20035001c03880e80c100304c141310180c00400347d48a048039070385200c6107a54845d0f00302e1520041c80a80c03000c0e54090007080740b42800c061034481001d403002e001c03480d12424035141d092804500000603125900002014401c050960283d0001703030000840301402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 412202859 1250 412201609 412201613
    0x9050a0b01320f040e0106051f0c0803060103060e0721021e13080a030e0307050f1c1b180c030204120f030203091e01030e0f0d140d02040e07020613 65
    0x500c2030302e050955600d01c65030380c4905a91070b00c00c00b0040e402c016104102c281031003644180200900c1c00703080d2141540150020032400011080c000803882c03a42c0300c40101c802682c850485030800b0705964149a03c400307011071000d20440701c3c0c07440351a07660351701d081d0f50440001a40308045203401c6180168010800301002d100070305141030011410142c1544e813600031100c1c2805c6d05201d90005815401943d004a09255000d1148441c448049098802c1c06985800704a0392680c14006103401c182ca0381c0400d251003299040840300d4600620301c64001540d4030300c04945404058104000c06542045003420030781040c8070f4000300b1981401c1c114074050801075151081c008114008000307040c1d01c3e0b4880205482070007607134500c0f030010f414060754000072440b85444544000d5010b0002c0d10308585002400d100141401d0000d01d050083d02c84008061011500340001c100035004051080041307c2d0710703001e01d1008100a051810b820607441c204114002c2c00d11002401c4e20365246008221440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 412204109 1250 412202859 412202909
    0xc0206011d042102060103140a11010e03010608070b0d0b09040519080909010603021809150f040b061809130320010f0606020d021e0c101209050a0b01 66
    0x140200030703a01c80300ca6980e592520b2400d0782c2c040c1c00400041c001c110000c05125800081040c180ca10034230046101400c19210140d4402241d84094006016404201003a501501c411840361002500100f81e040c1c4071804180381003102da00c040c00d1954001201000d45001d441480c1c044801224070100714142a100d0070350f140d80b0f21102c081c550003070040403801c0003141000c980a410014044030700560703407528094000e401c00c0540780100615007081e524a4604900752512500980301086802c050050900c007480d80000815600203588013070b000304640d14072000c1c000700144981c005801c4045482030020048000d06a0800390903440c05480000e9080740070b246045001c0010f0110507255040c0c2c10b805400c00c188142c3c082c5142442c0864a503902041d0b10030500501d03000c0718010b82e40358490441a12854400044c5a00134040b91201481c0558a28000384403a103082e401c2c5400140301c040880d8010f100840d1164005c1c2c1003401089200d44100d4010300c9071307015640c00080400b034158 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 412205359 1250 412204109 412204139
    0x80319360605091c030b01080711010e060a092303030f071b03030903180513022101090c020607050a020d320903070503070b0a12110c0a060c020601 65
    0x10104038069418034540440004084442500960309000c94208988041d4a4041ca02c0038009801d08001400c002030b4003070700a80402540c1030b0b481e564a6900e1440c2154490320030a8140b28a5480d00c1c40081d075014100b01b00d80c01400b69074400684900c50303240c40741da86240d10301c4a040039512540d4098902d000030080d2980f100c101110302c0ca00e6541ca4a086808007015907000e95030250215610040c9941940001e544c50b00c40e403648420050321410f00c24115441e4490341380d103e400030216042210054000e80004050701c1c0ca05112120000c6402d00080000d80140c500c0c1696000e45600d0380e5030400c41c1c1e0b50000c0141c02d042d8900901890000d441e411030002641c01d0003081c5194540d50450320441c503200c107287da00340200341e00802c0c43c80d0038998000400301d48203115001020400d4500854140b0455810036042494640741920590300700a00320703800c900319555422882845c0f40d0754001406248000c001400d03401516103401c1e02100c180100240445d030100f00180040d0014030100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 412206609 1250 412205359 412205411
    0x50301030821070201050a050709050f04090602040e011e0e01061b030e041a03060f0f0103150f0f060315050412050c0c06040303111207111003020d0504080319 70
    0x4a554400d18001c036800200300d03180010b42c2807410310401500c0d0394194415401080e1003981805039444c1c8040c11142d00300c0f9401034990042d403000505000745081d901104c1e1662083d040036040c5a5109220903514500741d0000000c1c0081c00c2030441840d006412031005003450402840d107a50520034002d119254410b1400c1c20b00d43c4488540b010325000705112101d0200090050180c0301081091086000c01070b000036020384509000f059440c1070403140f440c81020f04800543e041d03860341d00d40145103112480b059a0720750313841d201c901d1440594010310004a1100402007a101c3c603500d411400043c041c02001c070302d9403605081c4000512144855010415245440c42d250303214500c00700d0074158441c007456072003000020008201a044550381c80c41c0003502d41590010200300303840d031641b0b114203e401451208031800d0407800e4908070480100a02d80c030310b40181000b09c0c280180c811118103407016290b1040220401c170300c1509244c0f0014030641148024080c0305401113044900984004403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 412207859 1250 412206609 412206623
    0x5040903261e0903180f04052403070302030a0f170a0f1e1d031204031406070203161e06050a061503021213110a060305150109081b04021902010608070503010b0105030103 75
    0x5c40f155621340034a07805060040c410003c40c10804c0c102c01d40d0180d98824260066805180c895031882c010510404480c4c018000e400a0002903665200b007201500702101c090109020b800b200c4110a40a04000116505d070480700e4000c02d40040c0401d41208401c949010394030342150042c1e0313488410699500f00510900b000d44448100103410003810b00c50000c403010300440e0000c24070980300941c0c1c4199451109551487e00c80c03002c101c0c0ca9208145a081c04070025110030000a810300380c042085501030040f00d1201600c80d992041030ba841562400700d625114282404203041c030000140000d41e89040440c60441204081c3c9a4000700400c3c20104400d11441c010910951001c0c0c41c01c6500001d1442c3d003065101d46002c0c1c0140020b5a075002c030610b4807003443c086940503414200a40700018010483c156200135000204004251600c1d0015000c1c089000107819541d03400780b02103101d80001c9001420319290b249054859800140300f03a040c02e80341c540d503903004400c50b070560350000c82d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 412209109 1250 412207859 412207897
    0x909050601270504021303021201290d06111201050102061608060303040306020c030301060f08040b060607150f0b1203030c040e0702011e0903110f030405040903261e0903 75
    0x807032586a402c5640b00c29002070000848012540c0c4428006050341e200300c07821715082640c00f642ca03080356840010490b41910111030140b00301c0040301110081e03080109032032181e032501da5603a0161000e00010344400d200100e01100d00b9040b0401c80340c05003000f032004103001d280c1403004054000c503d0b100c650600c00101d01180c481d4405000b114082e5030490000e660390740c0c3d2262240d60300e030b20900c11807000560840c003083d234807441410744c9400740d07401c685005590782b1018200500c603400b107041240d412140c3d80401032414150301841d80c032103e0701c45000a054038060207000810b44c15000040031600100100a040c3c1c81c404282d41c250f440d40031103001195500c210036401040b40341402c2002a0000000980399580c0da0030880d441c509c030755164403c540d15440c11543e00c0c070711184030071901e070410b11042c01301d42081d0744000c800c0c90003483c1020b0007a03401c2131180002c4c10003940c1e980040400c20100715400f141c00c83ca0409803015010390070703c00c4c9056030b040c0742c41f40508507070580c010407840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 412210359 1250 412209109 412209167
    0x1b03061306120807030906020d021231090c05070c0e1b0403081306170f0709090f2a081512010219020d030b03070e040609050f0303070909050601 64
    0x190152024003102c00301c0a2015101c2d050402c1c151300b050740101c00140c00c5020101e40c181c80412210440396031600105002c00c006803107101c2541000c4407a898400c07850400b0404000d0440e80d204000c8600b0111249c000d041802900c16110962403410a000d400c2200100280307a110844003112101d01010b00c20761180303070012440540e0780c0c10366444d899001c200030040c00031043c0248102001042481c00c0142c1e20764083c1c41d054200c40c40041c103210482c00103180c810004102d26402200c501d01041030b02d84555480c1c00711189005200e10041da165407040c905c0100c0c141d041000c152410142d810302019560060221800800207131000c5811154a000e5486000c25031103e41c502500a5440701c50404807a85010000c0404400611425025016040c081c0c41100500c0ca0060007a0030310a09100c1c0801920310080c10031103109a4840b81c01000c01c5091200c514840070800203035540381403c850007070000c00303ea00204546850081881480d81c1c014903403a800302a20114400412010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 412211609 1250 412210359 412210361
    0xe040b180403032408070f0305030a081503010c020c040b0d2d14010e06100f0905041401060806011715011203180b0901030e1c0c05010605041401030b1b030613 70
    0x1069043c50750000101c482c150141c207081d907030700a452045c4110703020f4558480c0c01d504074810501c005445038004005601841e1b20440e605d55006d00b00e111a51403001401d030110782101d0030341e070f014030050700008a1504a0310f86130041101d0301004a55015020340d00740c403074074800c1800d6504101c6000c8071500f2064440e00c42c0903a4441181c0003051104007514a40c80c6a0103010540c10051060040c14002503c603c0d401e503400c4140c0b426542148d41c44c80c1480d000301c00034100640b003524404001d0240048180090080320040c1101101800e4194034003500003810030a140302c1101250444848501c81c0301d05038540904450743c0e0441203000d407041341801c1d1060f08240d6180514007006c0a008140c00200790001c0001070402c0e64108017552044060a856600c10084030224240c0c4017507170000548106c44806030180160000240e42d541c3c2c60009045841c688001c00c9000c1d4050010024031440381e180c1ca80c0031450b0040103510350212005000030348401081d25218683c458410105040c603 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 412212859 1250 412211609 412211621
    0x7030b1306081b2812080d0507031a0f1503041b080309060a0c0206070b070207080c01081e0405030d0509010506130506090a0f090b0103060b0427122d0e040b18040303 73
    0x80c500400c180c0317200d040c00002588800500c035076042c20134000c5001c15220f8422a41c40c0e001940c3e20b102030868034410840c40410b94a406a0701c030b00312514120700c02c41e4071401180901e11031b0300b840345421107549030340f6040c01a0360711250158005110104d03007916040125105040a403400034100c042510011f07649006e032a0020706a141ea00041000d030341d800094002c00c3e180365604482009104000440e55107000f161842e07404044410080d20023255010002c1c1c00521130300a07207007486802c1c404001280c4046840d158140e4480c424040d40f414a05000024410f41ca00e0900443c94860040344511030054aa4804140e40750070842d5040700643c01580080d030302a03030016a40d42c0d0b81c24484081d0043c1c042c02441185804075280c070800001d400071140804221032506662081d07240c4000c800c00036000701003880080d43c01c0d0304140d020100c40721814241c0304a4080c030200c0c0071400800100c00b41e0056030041c0d10341701c4048001c1c0d58551922003508015481103065030703104d180031009805 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 412214109 1250 412212859 412212869
    0x131d0f060306040503040b0d2408011a13110c03160210090b030f100b07030206100b030402091609120819020c030c1c08070f061b05090907030b1306081b28 68
    0x1a8224064109e5213420b1141d8044406104c028080c490388444e00d00041c2088502c2103601000b82010039150119075000014200c0036840708500700242429200d0956010004800c005070001800100318a070030480c038030130401b052400c24040b609207a140001840b004c6c2c050341201c0d56030300016208440c000c0711a4042c0c24648242d607114405440d0280d5103d50980781038040000242c030220750210924280c922458005201c3c076000d44900c80c421034203008103031030f4004004901001065401d48940d940394883d01c9030341c0090303540c90050100c0c010003416001d04400c5400150880006603000200811462001c45842d41e0343c148040e030030904101c20301e2005000a4021403071005104240c4003001055001d81030078802030f443c488440507403c2e554844c0001054050101c54003d0922085281d4888224200001c04030b80f0200003c0e40442142c03d101c42040e1544001d0004070307c10300002c00c1001030814041d1004201070000351007580904c01555500d131060f02d120b541e80b5500c200840c0144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 412215359 1250 412214109 412214141
    0x70e01060228052d0f010b0f01050a030605030105040b061809120901050c06070807091401080703020c1e0309030c0f0f040c02101803082406131d0f060306040503040b0d 74
    0x32070812401156140313010794500714010300c1c201c3c00301901c041c000c0380d003500170080224a10306c04540c01501e4a400180790142010703581d0034082000d0300c09200b014041c50080d503130024903241420801ca0301035441d01c0890112050b6500340203031100000740c0c071400035285901d21902c0d888402d004950341c0c000e04c058016140f08000c03d11010380d401c035117030501504040e9031ba81c58003911411080360a0103010f50160000b0030304800980302510a6010f48500c40c1c401060383c81c02104000100b50001140e10090700d15040010041044d02d010024001300c05030544410720701229400008a48071440208140603580380c449880d8250b20a004000e10300e0301d031610400c801001200c45496a040b04902240400c402c6000300d96425035140c0410210100040d00400301e44502d414441150400d112030b4400b001d0b03606001c07e85100d4102c40240c0103c200c03401e000c1524201e603040d1102440986018000d8003c8418040414008011942601e0000801c25910802c03014080010012a82850680 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 412216609 1250 412215359 412215403
    0x1809050a0b060d0c090f031208102d0f0e130515010b0a030c050f07150204081f06050603040812060102070e07030e0d03111e07060e070e0106022805 65
    0x342c0344d110801c040d489130b07183e5010380d40796100081e00c100b50b070102a1103000400c1d005602c140c4900c4130391b584440311001e080c003881c3e502c1c07000d030050f105901480c6111201c1344140b280c20700004020301000b010b021603d0042c481c6400c0ca00c09101001500c1905900201c076041020b1010401074404000540b040e403045640c1d51344c1c04081143c00203420000000d0502012180540c82039041da1511049200f102e4070b0102e043d6070740e90100480340420341120f6001d0000066820303061010b089c081c0484881c0c550034050361486e03202103e1980e00400d00c169824020b21004c5245d620035a1900e60082035090300984590340103070301d40744840e8030240c60a0020820003c81c140d1507000442c02c0c0c0041021115030882045e803c2e03060742e15004609041e01014801c100d01c020800348404c007010080c5106a14100c56500c4c0c500c00d0b01c3e4038214001c01c035800100108101a124440c0790b00521041c4050f005034010300212220049941d40c2040c400001c64608209016041c80110348040d0034908080c80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 412217859 1250 412216609 412216627
    0x10506030d121a0d03090812040e01062102030106120b0a0f03021315031118040302030a05070311060403090e070f0c2306040c05151201170a0f060f06061809050a0b06 73
    0x143e4241c5021f071034418050341450f8170f04100b16006940c2030311103092011006a007440c40c2100d01c03000e44003140e4840b01e1030041e034500070000d620040d03020f000941d8a05c0d400c07006103181c3e00182d661f0740f4881400b4840507402000441101106041502d90480e0f10681c038101241c440da014004480d0b9540486d01000000001c0284545c1d04802804e03040e2605420200c0d102da49183d004c00c201d5019000d41c00401503094030b91b1041d00145172017482030170100b80c951142c0c6405031501008a8046012851012052107518801c20455600010a00e4100076000e01414000c00c20301506000801e010744120b0540c1080001c45551810b410890040390031518003810101054103851107402d02511012a641d45169000404c45422000c42c0700442d81d9a4a00101007007080c1104000181500030040440b00191040900c41c0b040c5006070004110407a03004051406c42c0d94650000061205a07030243c3ca03a000000700d2142165030b941000a482d9030303171700c01c030101510010740700e268401d03400280140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 412219109 1250 412217859 412217867
    0xa0f080a060b0f03150903070f140106080607020c04021b0604210521250804031b02010e0f060f070818060304030804060b030309061b010506030d121a0d03 68
    0x1400c0d4040c1900340011903001d01400402c0030410401c640580244150032421003100c41180c5c0c01421100440380b030102c6588412601c024941c00442e2000100018000c07031820074090300000c0d01140c0054001c0f4103206101a50765054107102c14000c035004103a0081514140300f82c1c00100419906954003403170709240040c200219540d40d41e000304c02d520308500700300d03106800b1764000180d001e041032000521111710a040c400b00030702e1110f5280500f05106250780710594883e00d48080307500d402c511402c05241c040c1c00412004c80740341032440c014a80602607a0300440d60580100c054a01c03c279501d02e0703c8082081ca21421460400b00710000404800704901c80c1c0041c0301c82011075407244a80c1e4100400c0000d0307840140c40280000c3ca1a0012402003407030b0f0752148200c0f1400a04403460100b00c00301155554020b1341c20202502c84040d403c0c000580c00f0b010360342c2d014034100d010f0412440c0001014110f0084041c8501882c3c0c1c0c0d60400300e000410321103031300e03052107001000411480306502e0010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 412220359 1250 412219109 412219123
    0x8040c090c0f112404111c03030606080402060f03090106080319030501090b0904080c0102070b10060f020a0203100e03040b0f071205030f060f0619081608010f05010e0a0f08 76
    0x10005074100700000d041480480c05139a00c0c90103034681450b002e04546004c90803a4050415218051007400e0050503654000c80c0190182c1e03021402c8040e01c15038280541180e125a02500a10201c00204401603440e10102c030060441c01030016180d807103d0a0301c41c01400a500010740c03a1000150b0002e099511103480d5107804113598080c40641e881d008107501b903414481d00940c00181d01c20100c2c0000d50080b02810010381240001030414000347c64580000d90250b4580d004a88585801d01c00c841e4400212100c109a0f030001707040440850303000c40e9440c0740301c182e40000700c3c0d554102c4212009043c030488004010362940162203041448101400e94000c04040720f01040700c0c40d121581a024405491080803040e142500c1039480f90288180715000410565011307808220900d08070a441350503018a03400355032103090500c2d00100c0300300e2000c1c04005050501a200004102203603544003580180c80c0c0a02c1d02d60001c90350440401d40c0403c07560480c02443c100c4030710200c1c0d00e240c000f03115 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 412221609 1250 412220359 412220387
    0x171605160c030510060b041202100210050a0614040e10021e0408010c090f0308041e03140f060703091515180b030c0f01080a0b1215240d0308040c090c 66
    0x8001c220346c0d804208445101b5880303400c04038810b140c100001741c075055030010b0610081e40140e4010443d40640380088400403a1180016680c544040c0a9517105031180b520b4a035040c0c1d82001800e6082c03c00d540d60764403003500201031507000213100c20000b807020380d160908007440c40d4482d1140c1d103400e0a140a400c0f00d00d04040010726002000400340071081541c022260411700305031500341021016100f8540707602402da8100c15465000000a03070710010826500551005002d01a260b1602c490400c0e070060512030825040c2030014000c0303880d0149100c82440120780004000d03810444d00c02c03800000d9849580c0146620076071000140300e80c0c2043d4113102d4110140c07228014958100b017850b0560700e0303203680016410800500304d040c00d039102000f907040090609a4200e549520b03585040d66a1000341d110451b400240700003e20020800420f2038807115848007018030800109445a120200180401007500c0c0400c0620004500107006859864000e0140e84500207014000f0b01e41030480b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 412222859 1250 412221609 412221611
    0xb1503010b0d14162d12080702010906090605121302061b06060105030c07030806011e0c0506060a03020d080a050c0d0e31020912010203070305010501171605160c030510 74
    0xb1420510300c03000b816181410305032140000d100c5c1c1e0003030a00360080740411403140c1d15240840c201802110030400103102d10101903449101e4400103080c881c1c50340c00f042c148240e101040c015540c01030240c40c4011601201b400840e50b40c4400706c5490342500101940000300001c590f8484281c654a0100f40b80070001280d840fa1200070044556101c1211013820300f47d41488204002031040b0070303d5411038014509070380c50f41440c0c01c014400144021240011a4281c81a44200042407107050743c00802103420b441141d10f5a00410424840361000500f414030000b052504280510b05440c0c10580d14000c986c054004510301038610b1846400d514441c420039049090b00846004c0030b0743c0d03201900d030080840c00041100c4c01d0042c0d00440f04655003d0f60050010b41d950382e09201941c0310f0302e07140e580402d095240c074002515440e1040d0804040c02072500c02c0000d070794030b2600c0d8443d424000349000b51317075485506c000c0009800407000003810800003810000c240100056900c00c42d6000d404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 412224109 1250 412222859 412222873
    0x5010509090c150703030b09160f03090c09110403080310090e010e0c041503021518011704020d030302070204051003060e030703200304031a0103050c06070b1503010b0d14 75
    0x954140c1e02c09a0303064055100b00406242d1040e044108003818085101c0d042c0440c0c10303002c03080010030b000811120744a40041c0900c0d140d185550000210000003200e040c2007080d025203403a695000390b02805007441058443d02d5803203401403400100e40086400c00105600e0342400c03130b0b5486001701c0360310444034414201444046100d1041c481d5943c0da107000760003400100740100520000d031041c0f400707102528009034000009a29401da82600c00201101d100d651090490040e010109190208074104903120003040f01590702c0480003604076804450740c13141010a8034007140a0311417001c0081d0424180f03820300490302c1e10040e61005891080c0024802c1c4002c01115541d24041c01d18082d000400141119907810b04080c6100c040300e0028007980e2400703450f502c4111650305188000280c06c030a2130b00400c140441401442095041201c0c0c4502d09603140d240e0080b07409010344030304e41c054480250f10b203465a095001000120010700104d003003880764104044124403183d800445805400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 412225359 1250 412224109 412224121
    0x1d0f01060e1b0702040504030e0613090c1121130902030402010225170109120c0b0703020f030601081807060917010b031e03040807030f050d030e07050d05010212070305010509 77
    0x1031101c5040b6031075810000d003407000580810010303040c050010303401d0210041000600d5256003000708000107003110106030403803412744004201c0d49a802084200118803008442c60640401c82041442d829440d00110041805a81d00700e846010404111b4148562000402c4581c0340c024500c201d000341c09940d0b5000840c0c045c1181c0345000416104401900e1909124403d13a21104608180c1c18000000f40d100392030b03980d03081c1d1000ba01520004a81c4041070182084030207002158096054542541840e0002d00321840711300007d03041c01d0601c040c0000240000b1151480704500300c84d01000c0b20350075942da4078081e1036900d0314020552075020f200d0103200604014002c0c001c1d080030181c0180340c0d8130741c0c1d90038404034180000800c408600003000300003910b82040000300051070240703003a41c0038030901c0e1405610300802e2140c1d00043c0341c144500704c00504170124601044420a4034850840045494401d00901c00c480d01c40e62068200c00610074001e80c1940b00b103051f00c0c003d441814680d200c170 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 412226609 1250 412225359 412225381
    0x6221d04031128050d09150c032a0203061305030904110c0601030804050a0602030c0601151103070614150d080f0403080f07060b09040f0305071106031302091e010302041d0f01060e 79
    0x82d02070310111f0700c0c0081407840c22501c900c0007900018083e140c103115134402e0205521020014545c000302041c0d8606d60801545024803a240d000240000e40d10400c412039030b221610717805080403651042d5a185d9020703614142c1101120415600c0e4000d07240c2541c4c507442c08172444c2d00107024250040080036400b00d0054000021214201850802000c4503803815504945451014100f803041000d009030322040d002c01080a800d82c0d3784100e0010036020341000e0310400c0034000034000d00030459084c000e20015142c408079a03000c40d07000351149540307804520010000c0d1040351320040c060301d800244508820994400340c00d406100b04402d014115521041103500034003902d01402c51000c6000e8200000e000760f00424003c0d03c105030303803c40078200303d0000361141c000b1114803e01c00030780440c21045190007200c43c0da102a0006c0b812220054000300800f20340e0f41408000d000e50b645980d00b1100d2100010080c0070001c1d8907080322250000c1d849940e001e0700d02c5214160800c481c5501140b41840382d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 412227859 1250 412226609 412226627
    0x60705040b0409050a0902060a050a181d06192409030308160c08040602010209180106050f130e16080705040501050a031a06221d04031128050d 63
    0x101c121502e00b0503042c1a441c50050001034402a04160b64130610001611400064546e00c0c8071900d03090745401c00882c0251948040e4000510101c01c0c41c2403d02c6004590500c4010f0f03038851007030b201d143d650b40c4008910038001400500039080011080060021000c40c124405401095025031540601c910140d60010881c00001c004c9100380d00015103000c60078285254075405494240c075034461903107901e1030990141c0c00c4080180d40000710003d181c201101000e4203079008154500c801d61402e03400511a001e480380c01000020001040c028240031403201e0000ba11500d100342410f41005404e403101c54050682c0c1001040c0280009103d80c0e01410549044401c1078403168580310410404034003d00c0701c40b8890014101840d00c28690b500c0b124040c000d03102c1c21610301082c074010303c9080c41c40844503510007011f68200303c1880742105820030390a60004d5050811000203200790307000b581049072035090941c40103501550385900154418960442030701038000e0320404602400d040342c06202c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 412229109 1250 412227859 412227869
    0x151302130803030f070c150203010b27060d091b14120102040617060d05010606080105030c04050c0f03060d1202011401080c09040b0c0c0601090902101706040906020705061806070504 80
    0x4c070002c00604241e00562000c076080f8415003440043c1034218640c04c0881e002a001104158000f00e2510b44181d000140c58105404001c1010400710a802c00901940728518101c403480c0d80b610140010400b914100e942c1c01c1b18400000760859803a8044d120740c516912102c0e07442540c00c0c0c4c0b12640031140610880e015a8659520f20000021b4110b058542c0240649101e8209140742c002c480801e02c00e1080c40c01a108a6507041500e500d401c08061034450300d04150341c452440c12050095201d466001c903241d8103841c2d60160340702d42e90f4100090081c40f0030080602075114488601e1081070741903116554441860410320350903602c407a6401d6403660f8050b00c41c0d1704a00e49902040224022500310303680004140062807130034998030701d0f0760300300350080c0c0c0523410701610341488000318604080ca00074010b200d031402110b10300780b0710301c6513803208005000c0e207004568415217002800425011036210b66048000c07180507051070b500e440f0400740390700070030300c420b004030780114546920410440341154 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 412230215 1106 412229109 412229131
    0x11180708010e09010606200c3a02030c0108150409030908010515030601090c0215040f11040513031206051c050d18090515130213080303 60
    0x30f02404140e0341000700511100f030348003440300383d4a0b504014a0458401c03c7c45414140740e0a042a950400c3c0801180b00f519540301d0132034800c4200e8003102c07108081400302d503030340400e8000200951540000c0403034226503119039101604148465030503000020190009000c541a003001180031400c101003c10101a0030304c9110303800302c01480303c4030b42d442c86a000281c0321f800500036003464a070343e0440c1c8120a44200030607002d02d503004907011118181400d021300f59014104040350141351751642c100c0c02d0308050082500501c1d813a10443e140a0a0390340548904400c0f0f4038010230a692213000051681e1410407202071581c0004030803c4012045c00c00c2400d280c1828081402d01250040c05220803100c00c02c100100d07031045134005140d0f01d900c0258400307c81c60a1140d0f912003440d103461040c0c000c0c0c03507000309240c01500c3d44000985694000e001c0d00ca000c12214000a2 = true := by decide +kernel

theorem cover : BRFrame.Cov 412050359 412230215 := by
  have h0 := BRFrame.cov_init 412050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 412050359 ≤ n) (h2 : n < 412230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
