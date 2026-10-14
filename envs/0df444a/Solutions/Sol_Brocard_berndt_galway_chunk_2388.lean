-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2388
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:33:49.780125+00:00
-- url     : https://prove2.me/submissions/1b882cc5-fbf8-4c9a-9a8a-cdccabfc6ff5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 429316546 ≤ n < 429496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 429317796 1250 429316546 429316549
    0x4050a0f060f18050903160803161806030510090e0f070618030f080d02030901060e0106050a1407170d02070b0109050c1c0b12060a0e060601050a050a0c0b010303110c03071d06 77
    0xf12990754a101d451f183c411900b03820490300940c03003a1303541d80080982400040046000e919601c60740003501521036809458080250042c02c001055a0340001d201180400d2103000c0d8859580780400000041c00034a0014a03224030b056016041401030000030780001ca03400d80e40304190002d90764403015103407440d0003d1800200ca8020000070740c40507030000c410000210030550010080740c2d801c641012060b40e072003034207940c05d101700380c0d00000003298544201b03204038140d0010410103101d000005102c022242e054401500444e410410a41e0000342e84428004024a01405400303102c1d4200704504041d80f0254440c49001c3c8818484410540540000131282d409102c8540c030103030a0314208209110303da80c0f0b6100440e6030052440c03604190903030054000030010301c41c3c403060b1965450000c0005054501d90451441d020801c40d80200c40030000d0400490140214800c1d1601c007580380301c28145074182945042c0040c040c1d40588010010710342d069178006002110043d019406489500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 429319046 1250 429317796 429317803
    0x181902190c08130b0a080105060a090303141204030908010b0a0609050f0f060c07030501240b0304060608070906080f0f030414030705030a1208090c010e12030904050a0f060f180509 79
    0x40d0f481c40b48145071140007400440d607034010300201d649683c81542e40c3c6e0700c620821816003d03040307603000001c114007414030011703000d1004000c0c0ca14a402c40541020362081483c88038000841d0308800090035800108107100302402008014401100e584c50110f00300640104080c0c01803040d44d11030103418040244035100c2c00d403507201034000900119561010110320035915804e0b1700c8100c072250f10b00b0050000c3c0c844002040314001d44000d90040380c1702c1c07501c490300b01c0305d4001400070703191150341e40400140a0030411000c0b00070b041115012503c14030300122581400c1c6035001d80815a003265103a410b4050b404030488003600c158810041d40f2402040c086443e01c00b2a810144e050311074125000c007030207020b52402c4c1e000396491380c880c10b40350f8841c201c49407100603005420340071039041d075050f000521f48100440340c482c0c500c1086a041104a00000341504c809071640c000507580c50400c2600714009011f0b240c050003228110300307545841c00c001c21038180321420454014560740c0c03011580941d41032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 429320296 1250 429319046 429319057
    0x7020d081801060e0106140304150903141908061807120f14270c040504151b02100e0a111c150f060506070609050c181902190c08 57
    0x8000c102d0f15880d10a1440a0902802001c02180000704422030f50320302e00007141e12860b40305800181c0c404c00d9162501c01781c040360304210244400442d1207800b085581c1c004d002011241e0082c8808501c80312409009000b000e0115809030340c40c125404070002110302c1a075000b50461400110b14003030b41b06e07803800400702c036059103142c4c60904001101c003100010b0201d00484140d41080183d0f80302d0403142d4000c00c2c2c0400c1a101b20b4120111081d4140b625a10895100d40684207009442510349048021a590400001c90104190301f0014440ea8104400911138000090411420118580d130710790711451210000d160300600841040e6a884201d40854141801410700d05c959625151162105a1103844001c1142c81c000c4c412100840301c1c00346604546020301000e04d0300c4103940303070342005d403481c050240c8080c801e003136400070036441d0041d8150320040e88901d403248508001c64042c046500f0001261002801480078151104040454281000c41d505241101c03003058a00f21030f41d4001d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 429321546 1250 429320296 429320341
    0x3040f030815040c050d110a09032a0608070806240f120106081501080402060d02031e01060e040518030a0f120c0e030c04061413020f0703021e030307020d08 69
    0x100301e502e1041c139801c040544400e00507044140035000001d40c03d5403131405220710b01400900c0c1d0043c00c0000c03d03448045200c1d0030704c68441d4404040325003c084541001c0d641d010000282c000d504001c1c5030340d8005485500b100c0d00b25044040c0e00100144122100315100314604410030025001c0d0144800e002290715100182d04d41d404c040d030f5503100140c100c0c4002ca40030070710b0038071106400e40c09600c1000c002e441a94010031203405c01d080d011211000350001840b9021039094603030f909914860941b40c540c02840c1545c1c481d80b2200000040c4003d40d14054405c000c48105100c180101b0400442070303d050f0405850440341c10030382d8200884071038040c0003521200710724003180541050742c030600401e5210b1040d01200d1180c1c04c0d41d0241b000312410703441303501d14403503c502440c6094508003d039014405503070400981002e010240c5400700c5e5110302402c80140c0d003c10b80007118100140b5440c60f0031884600914118541601c01a458a40c82c400000411502c0000129400364460085400352070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 429322796 1250 429321546 429321551
    0x10b0a050712021e01020c030d0209030c090a020d0e010908070303020a1b03090302010801140a030303020901020f01060902030105030106051005092b0b091c1d01090519061403040f03081504 83
    0xb16100043c2d2210380c402c078890303400603c007114003d1a8005000f00c44164284400941ca09196820b40c18001d400000074998140140c841c3c078581561401d441d0380c025085003200594440200149400b180c8102c400c02c0c519034140000500030801c1c0405036202150981000350351079001110440303d0030125480c940003400e0801c100002c1c150700c1140d140981e031007a00c0d852080c0e602e404110741e0784e9001078105a4000c4040c00c0c103000083c426009080c2022040c011902a101c0c85120603080d6045074004a1009501000400140c07500740503420041100f41c40070388040c8a02c0200034481e1044520950007030a41040303540400c0355510200110824081d1760554000c0d0318948494010b500b9103240d00b20303110344039600704014410a0422055003080e100e01100700c221040701180842141c01041c14407003500c8001859480f000910b1800d00c001d09807100f0210b08040f0080d0200c900c008064050b07090034410840040c1e810300c003c0070119090b083c4010541d483c1c1d03040c2c410b02000c1040d103d07082270 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 429324046 1250 429322796 429322823
    0x90b040602060108010b0a0305060723040b03100608010b16020f04020d0504031d030304030303150e0702030406030c0509010503040b090703050d0e0f12060f090a021f020114010e010b0a0507 83
    0x550101e00b25042c0d076414030081c8a41840c0c0010803c0440040c0130290850304003070017260f100350040e0161005040c7c0007220700c5001900d4944880380360426071060b181041c0c000200b0004940d507500c0c500c094030603410150342d194146410900c150081e407000e90b1801d42c0b10a040301c20741d5140c005a2994100082c021365071507000300ba1a0001c0d01c810b4a045002ca80b01d4401c801140340c4210f011140035030003500444c1003502e582c508130040c0140e0101365154841041000c1005500748207103c2c821f405c5034000715522880c1050090844291440d03900401106000440e62680e00c07508980e081600140200165150150001e040c00a5540014071a2141c85070304c05100b900542d0308100702d87c040703c60b264030741218801c1c00710011000040d40340700d420117400106205804044244c100588800b21008180e1550209003800c40b03980c0a0b10b020750380c8201c03c1803810360900450702060048075001d003465261464020380d031007040c080c1d5005a00c02181c1c40701643e1054058440841d0881101c20000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 429325296 1250 429324046 429324059
    0xf0c0a0e1501210f06091503030e040213030b16080106030e031e0c01240807030f14070e010f090c11070303050306030307020405010f0e0c0c0c09070903080309010c0e041a0d0201090b04 81
    0x40a179031189000940c1060003001c88012031040200850b50541c0b0361166504008003004025070040c0e42c40c0306484c0d03c003240440828914a0325910846042c81200c648164044018140f00d805a115004160401007620450324012080e11441c1c84a0300c2ca4840320308039821410528080e98903109a950318150454201689002c4801c090340a15921040c9a940b10241c4585a0a0a000c0609100444400d03c7c00082c10130b03c020b40300c2610380c0c3c15220341d140c8601104905210a0740041d0f107520a0303c07424060307204180300714020070384603040600c040300d1030609540c0c46d1f04151002409000d0048005a2251001c0c000c8982e02c641c010800c000c0d5603111065041180c0300ca0060140c6005030170b0000d0000b07603000040b180f440075410b0040000b43e006c60200030300420000c021070100400007600000140780a00514000c5040c0000410200410400100301d503018108030b40c4a01c1c00c0c5040e100300ea10b0001b6500d0311346081950302c840703442c18900048c1c800d0916079201400c42c050004000849 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 429326546 1250 429325296 429325301
    0x7080c030313030f030212011a07050a0f0506160c06050a15091407021f0c050d0e010b090603060601090b2217060a0506060406030203090a02030f0c0a0e1501210f 71
    0x2001d10985481076400c4c0c40940c21812401504800300d4008901d0005200007031442040141d000559206980351800e0ba5441e14100f1240c400e08989010400e205102002001d002d001c4c0c1c4000c02d85a107032601400054010882000a800130781341c0340c2d1300c60200300802516008030b0b0080703001c0340c41c80e00c940c0e80c1d80400c18000c0142d1000b170340400500d0300120300c100e0320108074000d5244500c800d603e0b03c02410141500140801d405541c1406000c210300d06403924140185c0c409a03418038000641c00081e0300c02e20034000780c010a014440e4100e6020080c2c6681c1190401c41507440b840901d54076140032680500e03000d00440904000004650400107001d10030210310540324280d0300c2514059200c14600b4000c0d1402612041e80c0a00c05002c140145882980510780c040480e40881d1900ca0b403680200e814140652104505600414a901c650741042e08128000301070844580364586021005151a00002c40c0414100715160800441d98603d2680210401000400821241c4400e9030700000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 429327796 1250 429326546 429326581
    0x403080a020715020d09150206041506080604060204050301140c1c0e0303180f03040518041b0305060a0c021b010311210703050106020a0308150109030501110c01150f0b07080c0303 79
    0x74a1b80200842d0091070500d40c0551407041d500209945c1d101c660f104e080003d4250301b500780340ca64901c4005480d8500300b041c140a607010380c40050707940d8145010b0509442c000e9000a46103030541c01444076201c1c450040b945100b00c480c401c1260b00d44a1040100070b806c00c04080c030041d200100500c02050760240c8081400306884013102d0025030300d41801030300c90049102d210b034020400d144503641c03003154814469026100d80200b2210498054804848040c280c00580d40340d03003c54208801c036403492007a0141c1c4443e07800100807022202107171843d03001880740030604050710781081400404c0b180040d1446c40c0c08983c4e48007d1101d0282409010400c111441c070000381c100000000d10702d00105020f01c12a416550344d0485503124800b04031290400009107040140c801d000001180d402c0c46601417201001c010654cc0c0c0801150312402e461031003420f8443c44040c8401000800e036a103106104484d0078045443d2642803909080c0e41c1805071296840481c0000070803c004c0d00c0c1128500320303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 429329046 1250 429327796 429327823
    0x5070c02130e120c0f0f070b0a2c030d0c0b04060b0612070305070e013e011104150e0a0e091903020f060a02040b09040f0b042f0a050403080a02071502 66
    0x4a0f1015040700665860740383c3c0c401354007242c0047d182800210f82500082c040d091003070034070110b2403e04424095003c3c24441c4c82d0402c01410b040780c02590325042c05000300301812807411600c1c1c01510f0b11280c545007005007000302416583c0c849643d064076800e042d100b094862008034a000c0c540b01c40301402626088581000281c203c10760348110391f004041c14500825050840705134155041c04007158080e8083c00c0d200b030324001c180108220070090007155002c440060207281c42c0c83c90301280d00c00007003840344c1d0700040c020890b64a05043d11075000c132000302d0390105141903458441c0c0c101b160a1103808490b403480c01d48c03815071803c28141c00140d14903862034840103d8034a591054060b100701c2c0a1030040280354041041096000d181035017011940005103100010318454950001d01200e442d10b024054030014480308401d1145a1100400d03081030f8140444c0c03905144c0100184244078601000303054400105d034080000f032003000058040e10b4900c02c1100f82030031401010755581403922022 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 429330296 1250 429329046 429329053
    0x9200f04030c060305010e04080309151e090c0315042405071214070f1101060f080d09080a0b0a0209030a080d11090a030f0807060c08040c0905070c02130e120c 70
    0xa0f20b5229205807030490b6044003550980d40c940e6610081b17958409400c5075070700d00c034140007060550002c00700703a8003500e0118680190405001101c54407160000c0c2050250b40041b0030013034076901e01003030681d034181e4454413540203599145801c12410211015945450b50542d25000c108407180c3d021318001e06c10750321455000c4d2901c9140000741d414804094140e41d007000c0224401c035008402044280069051595152042d407211074215103441d8049520911013000030443c0749820310441d00290040d103004d4011a0525105aa592a516030002e00c417000b80c1300010440189903043d2091410001c060300d000c084141440101d9401480c031f101e841034a02840344d482940c590301113134001036000d441319a400e859071f2101594103400c000b040c0d030402810010200091042d10410402c607409842c0c69a0324140381c1444212107021360041d000161900d801c0c04070058200b01180704040d81102e40e10701600ca0100380001600420340c1100940c40b0342400e90450f4034140340641000015502117 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 429331546 1250 429330296 429330299
    0x403110610091103100e10030525050303040b04180b130e01061d0a090305070b040c1404020726041d1509010506030103060f02130e0a05150a09200f04030c 68
    0x3c0301c0041c0b00542c2e40018001c00b054080059800069000e0303407000001d0400d0740c00ca80e49441c1e01d8204510180910008070890701741550001d18054514060700b401e500960034541840c08851040c413590050300c5c041c1d40e20105030000e4144070380103188001c6e40030705000baa0f081d1917150140906001c11440c0c03c80e50030000701140c001c8031104101e810305040041001952905810080144481d1000b9410824208a80310204001ca510540110b104000c200d002c80e07d04010310030f0740c03903410450b01d220f01d00410400c4041520122511803c2c55034142180d0740c20711400c01e900d820721683c1e02c81071141c100c0300d02100c0611401c620044c85607500c2882c001500040c08100a00e218090080e180e1140b4148010720224085920240204640f95001803400080d00003980d06d000050740005249403c03c42004102d165a019003030f0020b450741900d48209564200043c0071207414040c00070317000d50b201341c0ba0440d40c215980e0341d0750f043c083e60b01c42e60341c4446942e0324428640c05400150392a4200580 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 429332796 1250 429331546 429331571
    0x905060603010b011209060914030703030b06120f070c020a060e19121509060501090506011d1e03070e0c0703020f0a0201090b0904021c0b0f0a0b030a05040311061009 73
    0x1210a8010305a68003e41012921610f400606c1c0394502640c9666072004840006458400d154043c4da5040f8019a00c0e1005071a00406603000f020809004440c00e0100c010b080860a609582114044040c25041d685000c402c5441d40403045021354004103000d0005403150300000c821181d200183c400e01810700303c0e07415440d040200d42c418100f00481c0485e4101c0410300c1880c28011444e8100c8000c19100c5240c1c0b213090913a1400c1e088001001c0da200c091200c5980c01400020884031300f1007003201c140d20300000060070102c00002c0c1a20503640c10f101200a81d0b41841100083c181003444041203040c00b018030f08807500102d40c114094480c0122451140c2c80004d0065041a4141c1d113000c195030401000240c140c1081d2200d5800c07503001d0050300d001002c110744084840c0808000015160f9440c02001403154503103218038007071401718a040c0501c0c0b180c0000c0b01d41c0101107040214090304e0700d14044848004c2e420f48000c0318000c600a008030b043c40f0103442c000f110304000003440400a00b44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 429334046 1250 429332796 429332801
    0x90516080c1203041a04090c080609061c060b030c090405010914061b090f0d150f09020109170c09040305090109060801180c03020f070c090e0601050306220c0801090506060301 77
    0x50390012154814442017040380082c01107501843c1c8000c1c0400c0c141983c0d0945a8240c4040d210003201041c5034070100003841c10308200d5981d008504980f01e00300880400103801410b0304102002e4103964580441c1102c80d02e0411230b0602404010b081c00002d131821341821802804038034802c480300c6800507096200004006032190082071640034103000c01074503070030900403070740002503032030b080b810b040c8600b070b1641d4580bc9404a2180100381140c0700385103407450b000031075036860701010303100d03140c40d039a04090b0340d00850a000369040200100c007110030b1001c04070310741482182815401407042e02000101903111001d0711f245402a21400c4166840340e10685100f40240031300c2c000301c466060280d000d180990054180c01607039041c01460310f21003054070b08641d4000c0c20b040d54244900724003041403030303510301c981031408550b18081e240650400340000c0d181c0310090204480d400d440070803081650b0103404140161940701c40760094056071034001074040c042488003a2118040e15000070500d00741030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 429335296 1250 429334046 429334069
    0x601030903080109090c0b0d0219090f032a121a01120b040f05060106030b0f0609010206010611010b0a060c030816020c060d1404051623060a03090516080c 68
    0x5882d01c00c5980e091100704002080302e441c0599800480c1c0200056201c41e02d070040c040d01543c0e110140e03603648400301c1c40b010794043c030326100108001e140b000c200841100349040e090b079901c5030a1903030651765281c603500000c0c104400c3d40050120039100090f88850040c11290030741c03203194440a00758504000107840c090911807030130a40311701c2c0503420000f00702882091740240300701d03001240e8003a81c0d12078620b042002d801040100303540c0c1040003c1c525000b00518082181103038038516208105000079103846041c4660814081c0704152000d95040a4200102e034a8000c2c0c111104c1551742c1c40001c0c0200c940040c00c1e400b01d0141000306041c200d0f40100000d04400300e800410280314003c1c05c0c400039601240b0000c8100c5e54940314101400180d40c0c155025034040c00c020039104041d804054958040c3d540a40d80020700b0124418414001a04460381c0c10300848059490f0f410f1054103801600c41004c000300940a40b50340d2103070805060b41107000f80d544d0a0308845180d0029018000f002410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 429336546 1250 429335296 429335303
    0x10608011e0501140c07031112010204031a09033a18110a030501060e040b090601060e0f06090913050d110309210609010603110a031e03020102160b04020906010309 72
    0x1401e909108650082c60100151450070003420b03e08101c4911250812007036400407142003034000420581071401c00008003800c0c0c1d030f03a002140307001e00d5541e840014601400098103941401d000003007610406006459405036a4404980c1244c04010090110260326581064081c640702400c000311402d4400c000040c488040796032200307109071b200c80116041c113142c2c040d880090b6060100c0010740a0213140010041c0000c1c90805083c0780c40c1034082007000500500141e03114100404c241540100600508ea6080d2082c103a0f400e29000882c01e244034586520390440e1180051010360003100e0f5210480601441c01d03500c2c400b907080c4003200d1020000b40701d9400c40d070040c445440b07030f4038041805061f49010343c880404481c0da86280300b820500e08070b604034102d95503460304005000c843c5132586d04032034040302d13213000090a50303452100181d0b1a0000a4401c0c480100c44800c260003503040701d42c00e2401d2072001c4403400083c500307010b10400884040f8094071f1081c0220b0709550181c00344003030380c560 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 429337796 1250 429336546 429336599
    0x509191e092d240b25080a0c17130e070c0b01030f05030714030705010606030203010f06030f0f110a0e150f0c15011502010b0301150e090a080f0904140402131a04110301060801 77
    0x7c600c00100c910000502c4240c8402c0300c0d01c1611205205402e000740110b80303102c0450b0a0807483c01c1901641e07c14014810020300045030259000629102a9541035950200d0b184440400b6410105d20794000c904009145d81840490078507807900020281500c988610005c0c4081c43d00c8002c100c090380820310601c0d5040c1d0703407824184102402a0003110044148080015050300e4003c1403800340e49188004040c0d009001507000d6441e40d114a030b010081506840f4282180d0b6540d48012040c40784800ca49104500421003d900341424460a1190040e054085900756110301190094564013141c0501543c0b80400120341401c06020b550601e0300a010180c40d410b1401c030988190138001086845280111986240044c22280c045e042c1128040003841d2175210102c1400f0441d50740c3c20741c0321510040d0400308001a600c0498406440c050214041200843c1c0700400c11031600202c0701540c00b038288428440c80020b034002450489181d6a20f115060b42d940540ea480c0c4181d10307002d0828040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 429339046 1250 429337796 429337807
    0x20d1a0f0a14060c0a020303030132060f1605120319050903090d0201110607050306040614030604020402090d0b13061b0509191e092d240b2508 63
    0x2e80b02d009418288003070301c155a903d0200d1b41c001390450380260044440701a00c40086007444000c100151090000411120300c0d0501c01340001d401806164580000780d08005040c050900450790384048450340305045450041d030180da01c2403075401c1224921200f20f000006c06c4208181400744034045c40d1050040c5107030807480c0d01031080d44442140b00381d061044407204000c0074103040007000e204641075640d80e502c0381030040400040d144158400c0e203000701c23014060702c0c46641c04625203405c13940c1281c1c0181e0f1344d100c542c003149844084005c0644004584c0c010410a00d4103003101d0614244182d10410913a034441580502030000b003001c1200141040c001080381741080e04c4140e10003134025241100c40c1e5a43d803440000c80e050b031240004482c1864034200204012030042400780f480032403070109814001c1c00c1850480350202442001d441d00c481401c40c1e141e204400360000d032441c4655913031a454613101d007140198000186170295030402200f0000306038800b040a460b480d48200c0052505 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 429340296 1250 429339046 429339049
    0x5070f0b060111060702010506011e020d030f0e010c031d062a0910050c0d02011e020715090b01140901030b010303050c120c21210703020d1a0f0a14 65
    0x400e00402807414800345003003040b031800c000c000c0d480c81410260700110f194505000010f01700e1051486d905640510107030b40e001c040350040b03440105140145000200200c2e5005200050500045941019403030480b400780b10b290b06402081a2225804000184010400f02151b8a0f18201c03565251a000c0d018014503622505003070154a01d00c41c0411401d00700b83d44c00040005c8131001e5900003090300090109198507040c0001450300e9201d0008100c58200800340041c074500c5001c10a4005038000791801c104068114880d555900e400c40802c11969189803e540180003801441c6038120105000030701854688440c2c2c0c103a0354003c4204405901e940d40c2954540c001c500c00c20b0480c01103403c00b807100760104c80689814040312008140700d0500c01c034032042c5454000c5038440c1a2070100803004441904c20b00b040002146e0380080710390703603840c01030840c024020141c01d520303050b0600c15203501c00030350b0b0b4000e8060400111010b0200300180e0081280000311482044800c008003c01c6031081d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 429341546 1250 429340296 429340313
    0xb03070f080c041a0712090e06010c02130f02041d0603030a0807110d1805030f0304030f03020a0b091e011407270f0e09030a020c0d03030605030114090c0105070f 71
    0x7040100542401d44500d1000994480c1c0e145005004c01e02080645c01c0c4030742c3c40c6542e11251024108407402506040581a180c400204024180800b0313100581c21521200b84061806500d101e04008041403082ca14000e54001e215205512007818030800300c25800280c401d01802c4014004c40c5092850142540e4000340240800705000c50244203c040c0041404101c0240c5140e03034a0742d6402c030002441281840c041d82140740641d000100003000c1d071200000f140c090720340050038010743c42e80c3e1f454200d00c0c016540f003008041c1200b5409000e03280c140003940382ca1410240c8103a65034070843c8003504c0c2c222000f10007540f48010004001c90700b9540503100e400e00904580203001c0c280f02000403804000d0000c1c0c0e002a00780c0942c02001c01080b8280355800d90003030700e003c0113903103020801c04000395150001e01c0c03030610a80b400e10350841018080d52010700100000780c0284000d41c000d400701c1d600030401716060040f0b030154406030066584510200c3c6c00c0c0a03800f440f9207290f0203090311000803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 429342796 1250 429341546 429341551
    0x130218040b150d050613020a0305250804230706020f0105011203051602040b1203040f0b040e071206050409050d02252102090f0912070804121109150108010b03070f08 73
    0xb00410706000070304d00b0783c0d928002000d20381ca23162000b18039824054202d43d03000c0468001c8041d0308000050740e84074a6404144250402d401c03150f507845507141c2001c240015038101080703400c0d0748100703080018115004202c18000110082c02007081d681e0320f00c440d0611170502a402000500200640c840c829940d02c143e46443d070020b80001222141c0b000803c6002c006404601e81c103a0010508100307248a640025001c0c1000f042d040313003490b1500505400c060390203049501480107e00d445140500e056000c0303c014034000740280f01803101400c04580392080021070b2001800380095500031264540c00605c1c010a84000e18410750b45003083e4078050120105444186130306205c1100050f94a801e0102c0c00769500c4034074142c43d414031200007894101d400709030010844003031210b4000b04600c10140c0f0100c840d00380c000c218803403041c50500d11114a1180e0590301010003014000b890000410000d100c40f02a00e90030100d0740c80e03d0602007640412214080003480134004600f219101c1c40d5400e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 429344046 1250 429342796 429342799
    0xf081b0703020106030c0906080c0f030d26070f18050a170c04110306130b060301090c02031303030f02011116020f01110109030e041d1b130218040b150d0506 69
    0x100945c40399120f0360841703410307030024482603100c140c2807007062020302190460328411110b2000c909036130004a92078a07050340340c14041c00004482841d040c1461065210102d00c0340603540040c3c604002d01070149507240b01c1e04d4002815074000380c80440c0c0800c42520a07940001c01003d811840e2002c02003213000c1d0000c111a441c0aa0342d107500007a00c0e14010307140d407038403000049a04ca15002040c051012401140d0801c00c500740407980403951540d00860b81900e0600801244505030b42009030701e07501c03400041890b40c4860001c000b00b81075000c000c1d40a4401154002d00003180752140344145800b50f82c100850780c83c44800702000501d0198050368010006040c1614900125200e00c0c0c216400030f981070340411590f4001002e5860140301d0600103440e10140c400703400c00c005404a9503446c2d10107688481140380011803096540341a012522403003041419540c0d0320002d44030070500f419140600d402a410701c040c84605142441c2c68910280005000a05100b9a50494005008042d202d10f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 429345296 1250 429344046 429344051
    0x1a0901090519020403050309010f0819020706230601030c021501090e1c0306080610030b070c030e04020a21060b370c0b0f01051005030606040e01150f081b07030201 72
    0x28900c42e8006400210b004070301458543c4860b82c005001500030080f004200722a04042000908183d00032000e0003450800040e00e414640c80c002000303200610032603240e4401400044030545051491038802d03a000e0740d05124144000707806999a00d010140201c800122074018000e1040ca0350241051541c2c10b421260010300e032980c01e004102200004a0000c1d4440405104d045401c01003950052100a0700c0e04510b859611200d50085010b0311041c10040d6406400007071520a9501d0141041c00070000c41d83c500034113501504d0b000c80c0030303d5812004940b2441d00c1540215200e00c000700c034059500f09140c210302d4200b11121115031410034941c2d00e04e004403007480c00d0201c40b01103581c1c0d420f03441e260042d518a081041d14404000e100742c25800161006100c951204002c20150703541504001b500e980300d0000227000c90140350090302080c4500c070000174400081da0040071690301240c4694000d0740c0f1382c0307a0417207280c68103d81408a103401c0183c04104003415a005040c0d850291000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 429346546 1250 429345296 429345331
    0x9020f09010b07140c100810050d02010c0623011403100c05040e1305060118200a050d061805070f0201150620070e060f0604051516060906020d1a09010905 68
    0x1421503410388000000054a01080104103400c010480340a44070482b50004140070560000780139107a000c5d070060280780c41e2040070080c004402024105031011083d01121580c594804440240c0e0740031105100e8403807110b01111300740f4188203d110009840d0345241c5481d0400b10402e03440e00c0060480800c1c240c80201030360116605010045c06090b00700140d0516440d100440d005954581c4202d090038200342c42800c1903604136030221480d60105041041e10392000c000c00c50024a0940e11002c02124030400c1c0100703082c01603100b00d02c20403083c1c843e036046003010981282240d1041410b4488410040c40501901c3d0040002e03001c0c14114030300d98601e00441502050501c022036002d81c3c200d03101c00d42030050342d00d00540e0550398900141c45031030415217001c0000e4002d580900d2034107405040019181ca41c0628031b00a010310726003000e800d11180040e4900740c0000c0d0720034503800c0b19242c03402007203403403081c0d085d184005030710801041b441c50b590030644031900a1401a01034000384481101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 429347796 1250 429346546 429346549
    0xf070b040e2706040b01150e09040303051005060f0a0225030303090213020c0a0c120b06060d1d030d0f29010306080d09090606080f0a0e0c1309020f09010b07140c 71
    0xc040c1301e20700c103280300070341e5524022140d050041c000100d8801d101c11410582400d45402150380d038042e405250114945d02c440d8001c04091185400c2250840000549100c107810600004c260340d60003642260345070b600c0604940000c81601002c1109a109610200b0202e8032030303003083c0c11542c0010301c01c030705540650306014201e1303000002c64600c81c2c02082c54070081c01460038074000103002d44400c0406c80800b55850210a2500602491142201061110703d40d60a036000f032142c10008513040116624818005940750800c640486006080c03000c807983c05404c030300a40c5030007411600518080742418030062114194010494101503440c140000e44a40130400d910089069440360010716041c0003540007a10300350b40081c0d0a00c4400000c0c404640c01a41034185e000c030a8035000038404549203039180c20035054840d0542e1262102c290340b1800f1100341c3c801e0315482c5c4221184074180d901c24081c050122000d214030a40948184070310808614186482640c08140380306449030440c0100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 429349046 1250 429347796 429347803
    0x1203040c050603190b121009050309060a0908060106090509241509090610020a0f030203041a03090d090503071e0504050403030506090703050c03010b07230f070b040e27 74
    0x4c0e60300140c07100b01e0010750599849442500d140c0c00c4140e0f0114075010407240e035150b5944d0140718030f40c0c0c2c155a40e22507005028050041d614a900010400799843d2a90200206048400d0144520b140141800050a54040e12402c411079401a091040d80e9589240110490080c800e0901c8a00a6529200c0d00e540c3c1d212008800c103000b00700d600d500d030003083c01130003650350000703100a008511400e014407000350000f509000b16a80310b0220700581c0741618080341507001d01d03800b410540401002c9480582044d401640c80b52010804903103943d001100102e81803d8a44140c94154018a60500590400c400c00001400352602810342071540c0e48041022210300300e030181c0000e603855080c0482480c1c5040880c0d0000b000349000d111509003a001584907100c18410301e400c02800250042c10410b412241806480310414100c1d58600c039490007a0b290a00c113007144440f40a076440120344403103074605031001c0d00d044000301002561400c1528146c01d1200440e54041c2c1900c8840c218030f00002c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 429350296 1250 429349046 429349051
    0x3070c05010f020c100501050609040b150c0616021c0809150a050609011a04060e130911100906080a0b03030f03010b0904110304050319030e030a032a021203040c050603 74
    0xc0700e005036039503e0018958100416425004105d508100c0104038541c0d0300c1c8155284c3c0c150448000840a03042c0c00062945065002d10201191010400072200d43d00420041d202d030200c00c001080c2080c1d5060100d0300c0303010f5100300c0020010303010f21184050303100d000103941c44543c1c101101e020080032200300a084d841180c0c1d0382007548d103a0040021509003519524010810719294108d0021403204042c03580c0901c5c0100c0007003114203001c10660782e60f01c0880500c900c0703803030b041005030710340c40d0070150104280801e0085c01003400703041d001c0c4d010f8450b2140f00c0456107075584e40c040d075842d0b06800101403e0051041c590501c818050314581048020085008080c1d10308455543d808103803d0001796200c5042845581509004010218801008485e0280d041c14030503015040c1d4880140c0040803080c054000b1440003081910400f905039200918601845d07031702c042464244039010f0300c21a11080f24000507040080600c2c2401d040d80b000d540c000c0c0c402c502480c0c11039240e001060158004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 429351546 1250 429350296 429350321
    0x1206020904060501180b0a26040b090f0703020f0301020c1203150d110d02030f03040b0a1b020d0b0c09132304020a050d2a0602060f1b03070c0501 64
    0x280c168101d24080c81400d008100a09000700c1031070203464040c1090695100f024000817001a0903802d00d8811040c414450203158000c08500300083c00c1000403e80c2128100d030358900120114a00340d10000d05924035250440041061604541c00d100d6448164040c4070342540d004e020800201c0014003c110f000711410507800c0d140c0ca0110030014203926900303505806144d80a9202c0007040100003070161a24050314200d07003400300c900c003007880c0441e4910104014000810046403405410f4010300703184d90155900342205450303201d50014241040f80003580141c8158016001444e0510000ea104c4181138a5504044440c000b01d11440d034204800c44450380d03180d40d89072a0500e1000e030a44840802c02d1301c020310307141540c080780380346501c0c1c0103292041e030b410b0003074501704205075102141e409200c3c0030b04c8201040c0c200c0441c07542c804a00031180980030b44400140526011600035208a0300042c030046d0107403501801948079071002d05008100140341481c44046502401042c002034030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 429352796 1250 429351546 429351551
    0x30615050a020f0f0a0b0106030c080c0919030302161a03060108130605270102090d140a05160905071106040201031a091f060203040305071521051005090c180a1206 72
    0x5185886d051201050308030000f4585480c080395805607001c0c0d01d196100a0a49040344c0e00d001e10750000f1040600c90340b0b00100201084008001c0550118920903002ca02180b0f208549440d050f0210008103402c8420b24848000d0000484940c4180800c540100400a000c00450286e0f00c6100c152681242e20324804840c0c10001220710f548440260b1010890034001c6040c011150f001070003181e00c1503005042c141030241d078007020500a00040411690001c11615602e00400c1d80f0071502001d403240d0950686071400003000180a60b20040c018420540030307020301e59540e4010340c0100090082840c00303e40c1a1030030a880d440342220140146108408100c041c1603105083c08025500d03040355085410600c005c01c001540001c021060380d05c1c54110301c05900e540e04040300d031403803a00b400559010402000c01950842940b1850040741004440d5001c40e07101c42c1072104038101071b200012031800c10800ba0403204042102c000c1c100c5001020035090540d00d400603000d044060200761609507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 429354046 1250 429352796 429352813
    0x20a120c03031e081314010e0f010e0d090b0c070b070602070209010602010c0f030f0e01020304030504170a0f0209070e03011a1807170916061e030615050a020f0f 71
    0x6400c4412151110148015250f0b01d400000005001440c0501014568442c1165a80030402039680903044100030034004c220001110503078503681c0000e03407260f071580d5180038125000d03000c02090b9403408500d103441d20303000c00b4a07110610016910808514030940a00c0c900450780300d07058002842c00500070f56026840e8006401042034034001a4000360a580c54101d00014490b0400d08080326444da6040c00170304450b481c0500005080703804c4910303405506c0001044100354004010703000f5074000c1d100010417091002c0803d9030710401898080c00102207640f601005203010502c0a512031402d142500700844420042030070348498401d0403c1d40d1100c10f150402d142002a500704001078559840540303410551005844803402e10303102005001d00c500001c18041040242100c07420b065102206140c0c2c1e00c2d10000e28000d10b80300781d1040d0382c02c090100c42d2000d2090150400f0780711403021040c5251010481501d0990107501140d007580190000038000100030310110540c1002035014200b0321 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 429355296 1250 429354046 429354053
    0x1b06020a20070e060607110301110a08010f050d080702040e060f01090e030f0307030203090f060a050a06090c0f030218040203010902040602060106080403021b0d06090516141c020a120c03 82
    0xc1c40c55014070710055100d4203041183d94400922660030a40681c1e10698441560070400c22003c5141303d001e4140d070034011408099402c203001003014900541d02d006060362201070404030444244507a551100702c445020011038107650050910701c2c8000e00005100b0711261440f414001d0448007100300300024401000078084500031203242502e075001030751414109810f4211130b400060494410558007000155030030030304002e44c0103543c400c9000c480e194a02041000e01919046600c0240141040c0b0001030314071950140340c90060140e15405036000c4c10320b4048009401c003100c0018400e140c002e15408640759840214007038520041e0140c1e50b01d0030715101901d803410692000d0104001a010000442c1e40404c0310f540c2a51420341144071804a0000220142c684a201422143c83c103012403040000004843d00200c4441843d004032681c0e44540540c2ca01030410a10740190440c0a0641100010030f4020103440c8010428101551030300c0d0034840748000310070b048901c09500340d010b0051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 429356546 1250 429355296 429355337
    0x61906020a0209060a1e1707080307140f1915050403051918030501061401020c0112470a050114090d06140106030b091b0a031b02010c09050d030e011b06020a 69
    0x19404400415115280c08074072592b0348038804000e8002c0c100d501c0c0681c0700900900c50420302d201040c04a8410f20400327240264503510000b8119802c07910038000c0c02c4c400f110f03801020701c10390f059143c45042203400040c20080303e1944c03840c40b0801403440009443c82c8401d0380ca04000e14007400000440e5414421518180720300502018155881491110000c2c0c1c0e0143d00008000c01c0d043d00800c00091007000c042001d2a60441101340740d0034500f903524100404c0c100c0700303070700b00340002c201c0b49440000043c0b001102a6001d01400641c60b42200141459044001c1046500151a0364041c00ea241ca4030821589024082c103c00e9184000411500e43c1c1801840300c0a2400c8403100212b081c0391006d0700b00403690401c80c0c40424000309041c0100e038040e80c48041d804044100c00100e00e588850024024403508000902244800b000440c042c2444140f882840ea41500c42e110403003110401555000d001c40c150400e844610a51000000c503d030000d85081c203140e031500d910518004444581c07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 429357796 1250 429356546 429356579
    0x10902120c01141615020904060b120709080c120a020d0503040303021b1008130b0a0b1c051e1603050303070f0c0f0308190203010e061906020a0209060a1e 68
    0x202031009005030709072824a04100019117a12060b8818000d65410060380079021741c800f0280c0c85460403200042c005060f2000b407901a12582e29040709540e000300a0300c043ca450302130103c10754010b0801c1c22440c140784141203d082d0070300040758406807242d070003d150801e98000454254002003000c00803d60100421804880d07031441030101c02c0c0c044004940c21803450403000d4200310044020819031704051022894035900842070341c00b1441c0510001014000c8810031768040c442840c240c481142c0c201c0103010810b540312010300171a0708981c2280c200300d1f40d02c80308041913010703541120b13160b089030217101c0006500c160061516881c1841c0701400810008884409202943e00110001610501480b1456a050802c4001070b11703018220034208101d02c203425181d03440040042482c5018501c403c1c810740c001c0320a07088451011000110b4408588107040160780001d0701c80d001407600092050f807011000d4102c501071651803100140c06546168100340740c0030941001d01000ba1050750381e84 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 429359046 1250 429357796 429357827
    0xf150e0904030c03030906140a0b09010f03020a150e030d0e0103050606030903030a0c03020f1b0106170d050a030b090124020615150c12030a0b0a05010f0305040203010902120c01 78
    0x211074a01500c0240034149001030090415075101c1c5c045c000c0101d1580101143d60f1071000487c00c03440d02550980013090709120030f41c4180413a0700001105007a1500203410b5030b502800c240c001c0303850410703410724032604260303035000b8480603018600c0c01e610100004034180c00c86603610503401204000150031190064081805285e04104100104200008603504011418000200240c182d18214028040e023041710601e504002548660345401007d0764030300700a803000030008103540d5892080c0311081e05400000c0354104000d00d0100e40d0054000c2c2200200a00780484c080c00040001010580c00360031618414090205070002c564010902400c00401400240440d04100e010400004034121a40c0d2240344d01c011915004040d070780980c0c01480e444422a03220f1041c14050020642040f03454861061602c0040c5400f4600f50b0030400803070b0410307140c002041c0c90b03d003c120003a00000300107903003640d00c9503071480060711442d244940040c11100680901604d40b03000520b0680001c04a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 429360296 1250 429359046 429359059
    0x180b070504030f02010f09080f0f013903150b19140415090504111b0102281e05090f0f0907200102030903070c060201050403140903070f150e 62
    0x240300082c00780f002000310729024200400c442d0012002140c04000d02d81042c1c90902540700c0c60707c1094400a550300306018040000e0101c064454484014510401f80307001d004100040e01055040c180c0300110b0504429240c003107000c5000000d070a4011656521007403182070700003402892000e41665004040300580781c10b054400c0f000301e00124034000e40c012210000e0840d0590990701d03000350707400001400050b00502a103c2002d910040580112050f2561521901c4000001003010b10840e000d082c041039458a54a070b050240340a0000302e0b5078918144004104801a2015454846a00e01005685055a60495101348101d406c0e98100d024004d0000c010320080350b0703481c000c01550142c41803074070040305a121449032201c960940c0107556594800818000e103101c01000405000f0300440c4540802951054200d00b02c41e01140d002d0b001030030568074076400b02d1000005100c4028010200c0d0781007511800c4d0601002d026511a03046009080c80918656402803e10400154100c515 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 429361546 1250 429360296 429360299
    0xa0b030708060411091201021206030a1a0a020c03070c090b0d0515040f020a030c150518011d04060e10120201120b01090f03141e07060c02030f01180b070504 69
    0xd8491080a40100d00c43c039107441c440801c48401c40203481000c10010085096141c650105030b0003507014900407c0c0d544000e000280700c50900241d105007541c1e10402c81b1011a0070410881203200340900884207058003044035544034002000070304031300e03801590400074442c0b411004078111450002580d008207025062403020030004148180c84c050020410f02c03507541c03580ba00400c416582d440095200340d4000c004024408256100d6050b144895104900202c041c0425929070044041004030780a0540b03030f5801a5104400d0200741d10210340c590341c812082c44000405541141d000442180e6400d001c0250301000b5002550003000b20020503000d0201e2600000c00b884031044080c00c0140d160b151402d61a40320324601401442e1410048401c2600c0c0c1c80e00002840380203039601000d11503020719000802040c0c0f14509940890b600401c040c0c0d00e415010b540c0700d002c002c0c00366818020310760f84500c284821300560604522601721408004140d00c0c0400202ca0003500c000d040180070b020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 429362796 1250 429361546 429361561
    0xd050603010605011b080409020f030a050604151221020f010b060f090904081c0b030d0801050907120e07090501050111010209130b0303070609031110050402280816050a0b03 76
    0x32401c1c00c1200105c0c524010a003507060400003849a584a40405807000407082c004c411200080c41c001c030711484040c4082c0e125841000151031064041c1890078035441c2c2c003004200d4042d0320401a042c8138140701c1e000868100c81c1e03141d910486a80410240e08692020480c1000038487d0f11080281200c03418108070781a20700d03401d14040c103c14980104071a00205040c41003400503648220000c61103010004154500840a0030040e08043e000388039070220017128500031118641a508040e09051032507540b00d41c2103030f280700d1911401010560f6500240c640c181c080c42224064244140003081d00d5243c480014044610703140904440e902c140441e007101e56030309481e0b0b182090000d4010603210050000a8110322803210014200c91030900c1600c100340d00524171401c1c1c609500d0a655000c030380002c0590030380b882142e00079401245c0540349115154181810442100e0074082d4007034a41d00c0d800c550746880803504424480e41c455000800c6640f800c3c2c0003040c0981200700c6407a041d07003040c45 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 429364046 1250 429362796 429362807
    0x23040303061e0b180607081612110a02060a1710080d080f01050d060605030109031205060a06050304060203040602120c091906050d0e03192307050a060504020f0d06020d05060301060501 81
    0x5200001510038050b00070a950360780c0c04d54101a030403d038681c0c8d0f40c88030003400000d904180c074400c8a05129140d01c3c02c5140307000384454018031042d54080c00c1980f003103508210b85640603020007801e001c94141c1e295600c24410103081e10484002c0f048810041c2055500c91508110304002130800800d0010880402480e007420350440f0401c1d10000140080d918112001e02003581140703170151719080c0c100c02031517480751201d00fa00205003010000ca071155411f02024030014024000410070420220f000555036130300031948103015182c01424010020281c4144000a681c2c02d2441800442d101c0032030701d850b80022126904825a90f40441e10b060000b80280c000c039444c06d110035607148000300454000f4801c44091405185900c0b0072807120342800741005d0400309030262024105088840480469021502a06c0d001002401081c0c00d81d40c0d60400b90400420403a0040b8900104034015112000100c0485114200160b102d2010040300d404070b071002400d5034440d0303041c030104001c81c1e40c110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 429365296 1250 429364046 429364057
    0x110c0307060e0c040e100c0905030a0f08070f050708060c070f021903050124051017040825030809070e011e0e0108010605030d03021c23040303061e0b 66
    0x10800b0400300c0c8580391450821455406003600103042103403100041c02c0200781c0024044944804101c08000740004843d4072040d03010702605a880f407509040403580142c04190110702c00c002e41807400b21a0354038081700003041801100e0550060b0307014090200d003885850361044080d151103003850000d45031084800140140a1f025621241d411030405551920f05006141c2207002402044c1c3ca2500c11503521080c851100261031002c00c02150780e113040e46c1c1204850750309584481c1d004a6001e607008800001410480301c0b02000c2024280d0b20000341c2880c00d541c502401c010200d101142006407400e6070040203025180c0040e00b044c4101031400760590f064800042400551461460030407205582d1a01b002c25411001030000904c8481500103800ba10002d030213032210126880001e81c01e034007a281c02020b21080030030140d03c941c20369034044240c04a1007440305410f0303000c05840080c21903003a01c041c2c002070b8075100184014810740c030000c400004004001660035290481604507805074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 429366546 1250 429365296 429365303
    0x10903180e060d1112160f060203070c090b0105071407180b180703020c0604050703060e030f040b0d020706180521220302120a0b060909030702010c080d1503020301110c0307 76
    0x91301003190f513545a107410b8004003000d26040307460034034040c1d48900381500ca501c80c40008010203c80440c0d010301c04820345401c036900c00c0e0300e10076641c1442c50502c054004510041e0402c4018000040840e0b4050501300d130382200d140150819504141c09280343c1503400016080d403d0418280240a803200c3e0300000600c40c540000000319119201e044000c0d10605402450078401e8000b44424007001050310011071340720704410045084414451500c0b8015100150303002842030000304000c00740d8500034415119400740043c03400c0056170700e840441d40d400c460740d18910300108a01040000401c0b521025080b01d100f40030f07034101401c0201c2e03224810036107170f00342503060340d4002e01400c00d80da414030014560042c00303c0d043e031003120209075131100c3c00f01c2d040c0d9100000b00c01280c5141030141c811070040361070401540c07800351960010f680c1910701c0c0314206d0f030618040208070742601c0b03248580500f030095031700078450311031844c0101400d66100c00040300c0e102c1c80c10807013003160510000c2118202c650 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 429367796 1250 429366546 429366563
    0x50c01082205030301170d21060306020d2412020f060c0604080c070f0506030c070516060f020c0402090108061c15020301092307051605010903180e060d 67
    0x320941001000319601000c40401d0610300241c208210011000d0b6050b103110824012959a500143d256201e07060f04e084030208007005200b00b4080c0c0031a400d015844100c00000c80e000740c0c0d075520482240e000a0710003018035a00c0c2000082600c0f180800f01c00c0a884401a0285e1401c001ca0010440703000f650084c03041034032200401040c0c40782e00c159407007041c1d01d20030380c0e91500d42030601c4261640f25005501550062010100c0c80094984913141698805801941169107080c0c48190311f9102d6074082d10783c0d00c40e100b004c907000107a070b0a21002070700450ba9507100b06044200041d00d04001510300601c0ba0f40107000c5009541d900c0302d02c40d540200103c40342c1680c00d2002c100308103225040040604400b103801040110b00440383c0045048480706582000440e2040900380c080105176051712140b20b11090125050b944224040e0071411484c8c48015120352069403081d00311410980b0403408100c17030b151090340e00c0c605038488100070100c506008002d031a1180000e425820348440c020400c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 429369046 1250 429367796 429367801
    0x4020f09090d260109020a120603080912101505180f06060a05130603050f060301020304200102070506070b0103050d1e030531120c0309031719030501060f0903050c0108 74
    0x89100c546803078000051410383e68076507120150000130b903112001d04d07400b00e0010454602e00c84542d12540c41181d8101000d42d0a1200308000c0040c040302c1064010034a1040d0103042d40b4140d07003071080d030044405004040010514100a20183c0d40301c10007402c07200044681009886135000001c00c0e408081140e249945c0c0342035520555180c003038100c8021030301c00e108001007085a007581c4020702425045035882d81507a548000c15081c0d20040303800a10841c0032201508400180b040b102c5078000050050396030140d2218040f0f5080d0304202c2003550000801401041408018030103100d03140c00c0e52070400b168542d89005008a065030031281c0302050341d100d000600d900c052240300840c101c500d000c846410320044007102d80d0315820720025120700c0ca021880552190103030407048480c03039158645031081c81c5180c03140d2a0a01c3c05010200c84500b007017002401e0604c0c444003016502c51191400074113941440da0040c0b580802c16031003414041000820b00104c0c0340000c0c0c404400409103410440361307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 429370296 1250 429369046 429369077
    0x902180a09120c03200c130f09150615050301171005090a030801140d140703020603090a0302070f030812090703060f020702091b070f17030f04020f09090d 68
    0x1040004400750000da24403070312508540e070011101ea0f00c24000c2c0d480c3c003000501c08940445145580c07072210b40d96800030702500b40a00313203043e40c40d000d084100800141186040084001e40d80c00050460b03a12600c401c128860007440d00c030341c00107009500801402840445805425848103000f031040c5510010421042144100b20454031015403081c10f1046003058403245907580c2c407583c0100d001c180c81400100ea458020a0240340203030004180300c038400529100d08200183d4071203445658080e0020220241e15610011030049002c1d40050010b0001d03410000d042c03480c950031004010501c40b20402c081a03500c0140c1c1d112175019a000b15068440b00d03a030a20300320061788020303c0309003805034444c00e100440d03001d0706c503950094a6803c03080c1e44581500090320380720070300206032400070f10078031000c10020701d10885468800c04140c9a11003007400c02102c40d800440c4c0c902010b0158204020071401c02003e01e0580030400c0e03501e0f150700d09000142c3c544074414908000d040014152520759030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 429371546 1250 429370296 429370301
    0x30a0c0c030f0c18110904020a0306090212060a09050103050a0602030a090f06020418090515060604031b18020a020604031d0a08030c1c050316170709080f010902180a 73
    0x20741c0d2000c1c00d0b0280e00e15501d0094000072040c0300d00e0054070f01400c404a1011440d00a98001c040211449407403c2082d0707017000001d42140160004040c0c1da1030740846c1c2a03585200500418058901080061802ca0304000d0101c003680c010141190405d0010400030b01c00040109c0380a40c02840035803640d464080e0100205800d540c080c05861103000c611040c050740741c0c02841503a020100c5449100c0746105000300303a40f10b04400a00f01e611141c00103032030421100d005038200d08002c003010300d4541e43e911869080d80b145610328048000f1a2010082400007600b114005910600154108400d941c0080d4a03541c005002a00b8450500c0802c0f0f609010900c1c0c0c5601d0640044c460000d2684030500035586c2d400c9400011407610030389800c2a82210984009040d6981c42d0755061710310303591810b075928841201c10a16062041030948020310308181440288115502d658252483c0c2c5840e4540d031600140703220b0394180f64501600e41005d80c0319400111a10803507140503038020780342d50003c2d000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 429372796 1250 429371546 429371549
    0x2b030504240b090601141209031608041509061e020709090602030f010e0103050a0602090402160317100f1202030322060923010c0219120303110a02030a0c0c 69
    0x60701201c07840124140d150758042c124015040c1c0e0301107600d0741c40c0001074036040a00ea001c0b001404060145182d40b482001c1095402a080300076603082c030b051a02d0401c022502c4050845000b10041000c0c0710307555569288040b03001d01e501d40402c940c3d10b0440d01801d07103c08000150102c06640080040b000c1c02045000020400723000b041001001070704286000790420f4030002d821610f1800009400ca60404085040c0c903041000346c10b012810340d0390703540207512690006030095000d1091054801e09140360307030300e054026184e515001c5442d4200e920f910800400821035040c24000034454425801514819100b01c9280c3c142c002e41c00e030001910718080c0320b448800c0e50b070380aa844a03207035012402d240c1c11904a034881624044e1611803012190010712000c0d20504181d84a1a54a600c14203400c010f150018014450700042201030103900302c5245c200d000c08668041010041550610510544080480249041002040000351284502000d50042100003c081414440d68100301c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 429374046 1250 429372796 429372833
    0xa0f05030c0f0d06080717070b0702030c090406060806181009120509040f0905010603020907030e0606330415030e1b1305070c0b0604051302061308160302032b030504 73
    0x180782c1e66031400a0310001c83c4401f210055401100400154005404107030b80fa5a41e0040103007941c00642c07802e02150000046c001d64040c1d8441800086c145403e0200034007841c2a107841610107981441c85034034001915140b4a022442c1c50b2192021580c550700c0364100e01c03013501d041e60781c1c0c2c0e03050b10009000c0c1c03640050312101249412005810441c0c150b0002086a10946e11403c555035000c509070101c4100b0000070703440ba000407002541503e0b1031980c48100d0066850400c01d1001001c20268205094246c0d80094210000d420b0141c01c035440000030011489203400d000c0885020304664884408014186410f12207070b100c030040d5074548000c00c49103070401d04100614907240d00020b003020350701d02c41035841c0c07204000840c6580c01c00e401283c0c03140390f04140c0d503118901c0c00e50030700001d90300071440c4560b80385c000540031078803407001d1100b6030202001000c5003c000303080d40100360820740c1e60b41c070b5102e512101102c0e0345847c0c8a04449103203080014200080c1d26900d9040542a40d00e034a00100e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 429375296 1250 429374046 429374053
    0x1c050d061203030c020304060503010509040c03080a11120a1722030315050f030312060f1c0b0c04060909090312050406230c0f2107050a0f05030c0f0d0608 68
    0x3041c0c64800607a10154a07010380d0707051020084041c0b0a030b89910030b900038030000560420040c4082d080c40d005c00c07a0403d102c0c039266110580d80c0d4035105142c1c0c00401e40000000c0402c94030403040802005503291030591410700518040d502d1801030100c0c482c0c0300948003004400c00000d580901d100c8982e40480b07000308010003d0f036829240041c01014190f58509143c0c0d07000f42c01048506002442d024141000750086142603c0d1840d00c1095041c01442940e100442e0040c440c103546400c240d98014202941441c0c2045d15a0f00d04030080030401400b504801000b84010042203500484600032141c001000040c1c4e81e5850070308072010348131040b40f08213850800781400104081a03100700c1503030b150000c040c5148513513521003a00c020b0099038960020802403141925075541d0f440240311416840c8801da6070b02c3d450703c4841e2071008003264a000400c40100790702c0001c80c1c0018800c552650740780b40ca1850352400f03402c640750178010070700310412800001c9454100100142e001802a24884044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 429376546 1250 429375296 429375299
    0x4061d33160f0206010b0403030804020f130b0307050f0102030415050403050327040c1e090f0b0307020d08010f060809031b0c0111070b03010506031003060c0c120c051c050d06 77
    0x41d8255000000491000038500281031901d0314400f140a5060340c607408021840d0510b9910119440075010780140d9004080d881c1002181d07540710310b0406134808180c030204c1d1000448003054207041007030f0301ca00c2c094190a800e0f0007050303a02004441c1a54928000103112004070075048910b4000c03a0001801c40c807000802101421051b5503000c40c54081807584a91349442c0c074240b1050b291101c1c031070008501d8100e203082410701d282521410500aa10f000c0c0383c040e41d0b40210f00b0000d0303030340d9101d071409100c00028402000e0b0706214012514905040031410f651400440781c1f070303400192065004004000003c00c0100205004440514950303001300560102082c0f0b00c103448902c1c2880407408540b10f40084030704081301040417001c944042e42103505607881e00052010f04c4c0d000034406090081d6000004c00090b41c903115820742201640e5a8111159480c6040c016076990301c082807003448240c0181c0c01c002640090020504650010a160a165150020b8400d8090f1154401255040100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 429377796 1250 429376546 429376561
    0xc0e0a020306040e0d08010902030601050906040b09152b0e161e0e13030509090103050a0303050109110a111618050703050609041b03080a0804061d33 66
    0xd98002c01e0304803070810450030880340641c0c2d510110050100482e2222004100500c0b80c0e5028541c442d0040c10310a00c0c20740c00701c00080440d0b1050b0480803201502041d101c81c14188504100d01181501a206150114010107004c1e41c54140002544c001c1c51881d2107403c6070800d401825800079140220349212140b0001c641610034580201e90cd40b0b041c0341d04080c24a51154002c0301210000c1d080c0903030390b80b079110b200200c05420803070a40030710504000899058032404011402540258054242800c41d8680142521010790103004610308107041d40480e801c1034001c4034000d24103070030502c095040d50b03100c03281820405110000c407071540c0980010040c400850144048032888000c100d26a585607043c3c003243d4065400580000210740010b0003e6180d44030f0011082c50740241c03056450b41ca9468101551012050b0000507554030107206c10860140110b0f03c0d8449440c203042c0b074010440042c40d5a0307041450140d48103a403131001750b030700e00e01200f0018050028041c3c0c084c038040c50700c601c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 429379046 1250 429377796 429377801
    0xd0503030a14151219031112090a0909020a0315140901090b04021012020d0606021515041a03030403030c1b0b07120e130605040c03060e130c0e0a 64
    0x22408000e81d0708000804034403400c0920310038825590001015480c059140c03d00c0611444481c1200541c85940b400c0301c001401051503c80f00b510a03502c0020740130714041010f0a16011043d10207040d00b050007002216911400070005945c0c10a10000d181001400020140842d036807018100c14803840303d20b802c004890b00a0351600c95110721610b036030307215030400c18202c42d40184050f19035003014000c200146088a080345c03500c8003a181251424403000c1c1d641041303034400c50011001c0f541d140b80421925405006407090020754121001091501040120000011582803031040e5961f00e0b01014916030603034000d0140401404480d01e45445e0720b0050603400d480c1b4030507581da0300424205000103142c02418010750301d408180ca4206031180d40e69602400140071444240080407031400415107440400c04280f5001c0e220208082c2c1c5000305020403210801d540c80304042c108401800240c1c007940700c4682214681c2ca81e00201c40d810700705005011800c0d00140072004810050049000d4140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 429380296 1250 429379046 429379051
    0x4030c140a170301050a2301030209120303010807030b0a140f060102010213080105040b010b030411010302070c0e070c060c020318060d0b1503010305071502102a180506070201210b0d050303 83
    0x71b80d40c1c80c1d0a80c2e00d4411132441807000d000034035039024800142011951094000d0450b07040041e100d0b03e44200201a02411604260000c51103270340f2560b0300300144034428000e1900540d0019040046e101c0f00f0b882c51648410080080c1e00c09040e410105000340d1003541107803a1030b072003000140883d50300c40271042e000e0903090f20244c3d040d010482c00420901022012240a030b0b500440140304200a5001503000e500142e02c00e0b1910844498005008050002c90380c3c452121680c03154003848961802c5030440356507074101d004552050220b064504111000780c1c42d449400c68910380c6420901c41c0c00e00c003034103186006a0f003090340c01c0000c010240c1168007441c141d130f10420948224940314a4500e030b6407200c840c07403080140e1250000c841d0201c003650207000e03100300d10a95415465400b007480a01c0c0225000f90070000f0f1502c610198102a204403104094182140d030240b8010b45500002d107210044408074814a1468401142c00c90306e941c01600c2d5500c01801095007040c06080007031701c0383c004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 429381546 1250 429380296 429380299
    0x3080906161d18010303020c011404050109050f1f0f03110a0503011206140910050117121b060c04090e0106062a060e0102070c060804030c140a17030105 67
    0x2008003041c1a180c0d1210658040e440e241da0701003000000558214500d604020010f0b0081d80620809030003128082810380614000c1e0020800c52141c04001000510140a09614410140300600c00303a03078040a8501101e1084400d41c45020303405001914000007421962120680001d80e40d9043da00000441c5002403503807403c0007604601000e401451003188440000100100010b1004003801c4158806d44d5004503400584804c68035004000c041064807040040e03400216802c0b910079803800341a025112504d40c0e081500044008a81d07203000c00c80e46012410f0012484082900030b00310802c0d150f0401d40102c400314103001c030600c145e0354414054405000d0401d60b12001c1c461050080b242203c800355980355440352810800203410030203250700c004020603445060081489400f410b120001540001a910301c4a85801c64081d001035101b40c0c2405150810000425040394030200720b59000080140c8034200d119806060140c418001000343c0700c0283c00b4106004240040d41c180c940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 429382796 1250 429381546 429381553
    0x3030509060901020a050412050f0d030506040e070f0b0a1205040f14010203070903290a05010905090706020a0b06010306180c02190203120a0c0b131106030610030c1b030809 76
    0xc0e9060040d00345e05c0350010b09000303d501080200403c1c2808014052520b01400955911482c12503000c2c0c18601034480000000751220144420303450140704030502108040700400996281c1032008801400c1441003170421140850480c0c0058092031030481400411101080b1034038080c80c200d032003c82c000e003040d00c6032003100d81604030030319052007100d0141180c0c1e1640101d0619554031900d42c04071002403110b00030545080c80f40140768120b69140100040030000c2610340c100a80f110803140700600420b860f84c4401001c0040c4c58000c2080d00c401608020007800c6c0e40c1d00c01c0010303405032000d035008003d280d02c4004542120400c40e44908500c2c0081c1d0f007618409513a008202c0c1c005900401d0103980f6130418240031104445c01c0300186030b02c1000c0e080451450100b0b442d41513842e0022610051850010508141000141c0100445003881154460f0840c00e013040400c0c8180d080c500f000c4149641d81e813840a105000303040d60201000082c912202d140954540200042010340d007200c1c3c91721 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 429384046 1250 429382796 429382801
    0x30b0604020c0c2101021605010b06070f11041103180c010f02070e04170a090e060103091106090102010e030307261e101a030f100e010b180d0303050906 67
    0x1619008461142d150300c1d0050516125160410180c102d00c4c0d1a030301d484400c81020707003205903c2170020340b11030072400040309030010351801c1241c25144002c88252042100304601c8002a03151031407884120342180101d04045403200205000f0404d096419054160200410941400c0a602c09035003120700b000742c54a650700b0380015580f0b0a083d0702a540540c10030318050140c00d00d84220381d070740701d80a00755800c035070900c1980c80b804c0c0768800c0000d1b60001d0cc2000003403151441d1061055002442840c1c00c00035800701e6280c004d0940304d0310107454840c24000441d000e2030382c03013504400701202e4160103070303942c0b820142005803018010381030803000000355035182d030320140d0324954851180c408400443c0c0c050100044690b00421b00506403c1041340c1c60801080841000200c040b00b104203049003039680c2030510315010500d00c0201400a2a05042030511008a016001c9811209404c03222034a40300b50071085040c00c00c604480d00d400c001c1b03243c02402415450780045000e2441401230340c0c21034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 429385296 1250 429384046 429384049
    0x503010f020d0f2f07020d03020d0f0228030c05100506031203060d1211030a0302180d11130b0d0b100e0c03060904031101050f0109050903070c05041a03030a0306030b06 74
    0x22824505419690046110604101e4604c408004102c0d90881010f80c42c11095078009034640d00308180960050740701d80741c0080f00942204120329001c0003400202030b162540158600f1545d9200c03402103000c043d080c0c1d2401014041c08070f150300d40f070740107056501001000d0724032002450100c0700d06105e84241ca4100080c1e84d03038a01100d02420001e0000452804607407a5030038152103503c401c10410800b0858000100c1003840940484002071340d0140c1e903006d05d002c1221a49601c40c0d02c9500c10064000e40900081d07403a2280c500300c42c000e9440c00516000c40c2c080d40010000003103555040042007032080200082c88032000e20409410400303640460b210400603400203001c9880600501c02000421074918082c080c103540305100780b800b4000003115171300c00d07801d4030015038400e001c0321261001070080c000706004503644651007000660a02c0b10640b02c1c540369081ca4800c0c0740c00303165914441c58a4414070304584403c610054100c0307aa40c804980e009000307190910068620310580d90214405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 429386546 1250 429385296 429385301
    0x210c020d0905120606060f0f030403030504200d0b0c0f071104141014130e0d0e0f030304060e0d020a1e0b161203090c0f05090f010821040503010f020d0f 67
    0x10341d0a880c01003100d41e84417000c0c80595030011444000d41002400800c00482c51030000350703c124400d580200e1503040c0751400e02c4000b0301c0d01c0412100c240c4070302040a0340d6241c06e900a15501e821a4103003405c2d4648001907241031140030180804024001000c005101107030030b440300307148010303101008101c0d0309c0581311004110a031402d5a00301d411400400007050b402000c081c070200010811005120480320b44811221164582841600800070b202121034208030300d4168070800791048100c58500c000081c1d00c1e8812401106e090040040610507661101c00c010300a00c2c1d8080c00d00c0c030340140c0319514900c01140c982c59045a00310404070208000340c0c10800e0b80d28802e030b1104078081e030750b90941c0c4802154082091120404d0390340c5000a002c0352200d003105005140d013403941c00303506042c20700340300d4240b02c01081c0c40812010034004001d15000040d01e6101c1581d54205142c038034070400301803645031180e0b50003540d0540c00c0180c40e400744406a40107060b04060040c0c20410703020088044400d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 429387796 1250 429386546 429386569
    0x151201150e010f0908070e0405010f060e061306050303070308010e071404120201021515030f030c1015031406010504060504140106050a090b040e07110a050d210c020d0905 75
    0x601d0448841d2103a5000d40004104480c15080c0044c0881c1c031840f00c2c0d031411042da40101000840d4074180400c0c0300082c840c2c3ca0f60006103070014401c0508182d80e0108010003d043c450055034000890072444500c1d9100001130003000303059070b03522951810000c219030001c0c000d00102850b40c07400b0885581c002c0d211503410114080d1001c0c145883d10310b005030300f10980b45042e4103501404030300304066681400100e12071503142c003549007964002c0301410b00d0105600750019181c0c0c404c0109920344200060a0510b1090250b80801e410b011040410145851988018010b44580c4440115460040789440c180c56096804001c0c150740d8000700b0003a40c40d0040e841d101041d4090052051920401c0102480f207070906003040010390381d01081c2c5860b072056214034280079180c014420040d520007008494607104100604801e5410348815441d10024a844010b114484e1742c0c15404200c01c5803001d0b0b04110101d41080042040c4801a4450322405440070018070641808112403924441061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 429389046 1250 429387796 429387839
    0xa080601020a05151e1003050705180c0306180a0e16260111120405010b060421020f0901090b030d0503070504050105031f0f0315020301050d0b0411151201 68
    0xb0500002c0010402110010706035045c04180503224000c2a4031440e0001e000c0e00c0c030b4031580c3e80150f286003002810002980c03c000c0c407458848001c0c003288180c0515250304024031010140d03032074848000040410090001c182c9000c0c0c10502000649151580851700058104080d00e06622001c2408104000240584d504650b002e51381c0402001588031450060840700000040c41d6552a030071480d103801c03044074404131441c032004100030841d003809051b1504c0800da50140c01c0c9828400541c0701000c0b00d44103014a07620031510203080d59250160060030000192100240f940c40b42104805840d400c0905400781c410140c9040340644a60b0440e4858a1695691801c02d41031200468060b44082c08140d00542d240180d100220310003444c903c000c0c4060b1017201c1d40d40d0314628101f00030001524441034414414001000070341c540903c9003651030351022041d005030b6128038050354114220b40d40f1607000303091004000b0b942c2c0710000c000d0001e885585d045400c9a07076180c5003c4126050030080c2c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 429390296 1250 429389046 429389053
    0xb0d0513021302070309170a17030103052a130509010b0312030a0c0203090a090b030624010311131511010912050f073003091220010e01020a080601020a05 68
    0xb14614000c3c2c1e02500b14a4882c0c17412070141503aa4040085944110030070080d04e4000005001c100301d001d0314210311542c0074420007410356145440707107510741400404d2102860000021070ba100b42e0042e528055000004001010300c0ca01c00001100034a021110700c0e003070303610b13103201d0714140e103400100d54004181c0c41d40781c2880d6940303080780741d03020f85506840740c82584814424080e147e620342860401a11207080700140c441001c2c0101442c180c2c010f40b40c918006601c1022000d000c0c442c45216509500030f003000710310b110f43c482c009100c900c41c466003c0c2120315043c10204160079407510003840b088507070751402c800810f200021422200916002420782d07003110a040390301400348000c1c020341d001c41d0b031007a400c1c114a03855107910301081c1d1040205902494a100c401d10b0001b80800292800340d01d41001420200c0d55450b1050456101c40d0050011200c0c51343c4550740305840056034034818030001d01a40034069000e6001c0d4000416100100b50311200140c0c40d5440064070a0b1356503000b4004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 429391546 1250 429390296 429390319
    0x2120a02071404051b0d0b040219180e0103061104090213090f380d1b120b07030f0b041a180c03180a02091305060109051006050d14010b0d051302 64
    0x40c5126030b1080480c050303015124444500a0303988d030701c00b410325030b40380a00801204180c3c080c01003403050441082050110624810303c0b000c60101c41c0c480c192940200300040c0c200700000c5150786802030342d00c8800c900b030000a20004603154206100b04465851805110303080303c0010341410707180c1511040e010059440886c5503281044141c04528035a1403140181c1c0a5098020030248101042c040d07401c0b560303e0f80c8403000a101c41d411003008044001c0040d1001c0d84541e149150500c019000000301604e480035815800542d9109806403040104104501110019048038603082240c0507840744010103074a5104021140c60a84606492101c1c50700d0b5070350300031141454101034a88140144640340300a401a219446841d000305131100e81035068030401e01e41185010416003111100c20b04250a0118110846c0003010640314907041c103d0302c645d074070b100401c020010580e04e1301c102001d01c0b00004071403e0540c010001d005100390244050395072800000705031032183c00004d400207a007459 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 429392796 1250 429391546 429391591
    0xa060c020c0f0906040204030b100f0602010c050a0804032c130c2709020d0204180b0f0f0d0605010e04051506150f09040c020d02010c020708070506070302120a0207140405 75
    0x18030f2548168010401030070141ca82c0c81c0c007413408070225004080060041014000841803003007803001030031303288000e1044003c841c40081c014010340d80170b1014000503a000c40c08041c06600c9011501c890b242e40c07251010503121602c0211a18640150300401c84095030400030707003603401181d0003000316032a00980e4442c11540400025800148a11556a001000f040380d00c082d0008010382c4040d481c000d13071a07500380300ca08007260038a00d903000c10007403a001130b0300b95603215007810ba007410341c007103035865080c485900100348280107000000b0b110501d803030004680b4240b000c141e1806280150201d0300040b01d494200700740d82030141d034242d90000c4245080c002440448004004481c0340000142c01c0514503000309040d01d20b0964400050780110403000c00d03003070782413294170040e110a1001340603403460000501c0c1c8450361402814003038580040c40d07a0074076008101c4418000e02c44130303500c4d594030410305009480c0d07004c80c0900f8522941c3c1c1c0d40c08a00038038290003241d01809404900c070284002802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 429394046 1250 429392796 429392809
    0x6110c0306010b0c0f1501030201030501091b20011415010216090203040f0204020a0905090c160b060a15050409060b2a0f0a061e0e0303040b0901090b01080a060c020c0f 74
    0x14030200f0780740324101001762441800d11540703a9810784090180200c0d4150710026003901d20503004401c69600d045000c103c0d89180446c4000240c1c02810031400c5012582d060b585260201d0800880b40e6081461a2491140c818101403081c0c404203040490100c0c540012604d81c0074980c4900800100c800303051005030016401150020b00c1000242c1c4641c603d5408102030380c20406040e400f01c2e041d040b041000d030410403071090340000c250742e00343c1c0760201c65940d1500f41c4105c0c10000c4c000303000b4000081c400c1e8850100300310103030030510089071406048400c010040c0c0c2c800d020b000c1c4544c1c1000000241d8035030b40f2040e2105507004006401012098400d148100b9540a0118202c0e1158428201c2042d1060000c15035850050902103440604012060044500c90105001503071501d00d002d82010303170120951340c12942c0480741141940b285a0310901404c02000080e00030421640005080100000c81d03507030044c40303104140104000042d0903a10382c1e003060400c0d40c10041156112a9034070b03050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 429395296 1250 429394046 429394057
    0x90f090a120e090601030c0c06020702060403020a08100b0303030412050a02011416031401062f060a0e0118120f050d0203040c172811090f0106110c0306010b 69
    0x400854851a4858550300316031600c2404003000702c2d004000b0444541030540b8840e500140031b013028400d03040c00743c2008200c07119180c0003410031980805c0d003804541c1c481085400954004103004007164540d0310140c0c48094044401c0c1e00c42d0315007000c0810500340401600d20803034110f0780c0070012141c20541a1650392244c80104c085543e1030040603118a15070341014004c2401042050100c50603102c00303402c84e420f28011003580700400c001001019448213052413616803460070407a96618400c412440c40b4500700714403180b4000c0c04100b1036400c1040d4003580049201d00300900004040c8148040f10380014a0042c00301011070490b5050035004034240c074410001c0c0d16015140c0400076414404903002943d00f1504e640700c00350100210000008039409000700031000e0a5034011340c2246041070b001d0041c500c514014410f4100c014008100183d8000040190541c201c9191811501108010900400b40400c1c40e54983d403c998400048071158450003500414569080c001030a0464100c2d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 429396546 1250 429395296 429395311
    0x72303060105030c12040c08210405010f0203040902040617060d02030a1e0506040c1e0e15010504090903230a0c08180303040608100911070b15120a050714090f 70
    0x410000380b01c103003050384046c0308600030f1892184a0341080303e918205982401002c400c50081c40c0c00c5141d55894104440440d070342424203104805601405a05501456100c1d8408610225001a4490304608203025034409488084240d030740f0302003001203000d45600080e4059100005c200c0006260103402c00c03001e0600c511040c14008560746492900344110340880301c1c00c1140301e0800103450202d604408001d0000010302103603050103c204d40a00e0020140351044402003462070b626405030080310701508046070b05200719505030034082c03c2c01c0010358007100c086020300d00d000d66140d80c10003583d228140c40daa544c0480d5100c0d82b1240e040c0d8002c800500b108101003898064540d82c20001000140080d0715207080c40d240400d41c0100d0038010307500c40e413110707810901c03240283c400d640c0855401550000c0d51381d030745d03031500c03070441d1040c048802110760441151070b1000780a43c00050103003409031050b812913000c1078541a40c1001c010504408540294041c004160701102c48411180c0c0b091a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 429397796 1250 429396546 429396571
    0x40617070905031b09070804260409110a120203090312100b0301080d0305090a0b0604050703110a1205060303040e01031502070f03030203070f0c080324030f0607230306010503 77
    0x72280d0009041203c000e001d0030a41300000030080081c140000c0040d40502141048211403502d40c550800158440c80940c0112000c400c2480c0c24103580d1003a1000b9240b032190030410106400c1d8010319503480400040041032503194190301c01c07a41c40c02141c1c0b003120104091401d180304110f024401e040041e101c1d4801844d81c0c0400b2500340749141c081c60003020b07020000d1505c050070020150032980301904200d0b0581082da00c0101180c04d881c2070541200080d40d001a213551074490450050400c804d101c0301990002401d0f040c8117511003031101100481d8001000b094883d002095505c2c811846042800e1003030000400c0820f0508100c0e8825100c60800945000c1d400e64606207000270612040300480c6d408024407009035072040258104500c11b0a06a02125aa8450014030702008045421041e0740c04000080720000400c0c0c608400f001030204c031219840501d0494880c5421600c11001443c0c16100c000c02080264200d200501c000d50364a1031604e0350001100c5c21792009045800046 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 429399046 1250 429397796 429397799
    0xf12020a0b12241008070507020306010303050307030c110a060209060c0a1a16020606040b1504120b0f0c09040f0227100314060f01020a0506090f010c03020406170709 73
    0x40c40725004107600d1500503810300c000c0c540143d250350184114500050a45860b001524094607040b01018207001c903070070301a01c42d66402d50200c0f030921600340c0c025014011700340000105a0000041d5014000c01e840038403c518036400101e81d15914240f2a87c442d034806036442002c250240d00410311180b0141c059460720000700d011034a0110051000c0310310174500713151182c0d2515880d80003500300c295812940c0c0303141d0340514029030b22000904203034402d55481480080c155582000d2003035401500800d1900e66950780781d200050000d9800695102ca06a80041e200c0d003600002c051081a10007483d90a040300030b814040207113180030f00c0801340b44d0700b0410744040380f8510380e40005110256000d149030b0000f50f82070001c07080d080d0302c40c1020700d8201449461140e10180302c01764000d8040c0d441c0c0e550510035000407485c0402d0010301505a01803d410b0092004000c98124084520f500091207800c80d0301c1c0044080b40708a20403000003440990b02c0036070b01d1a0820a03660410001d1428100380c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 429400296 1250 429399046 429399059
    0x1f0b03070512090c030c0901080d0315210510060b070305030c1201081e0d0c08030603011b02070f1a07081c0f0e1207080f0c01090b040f020f0a0f12020a 67
    0x43e10010301c1da5004004810451a00b00702c104800c40c4107668040007035140407000750381e07446400709400074140c41d8843c0d419a1556407c81c0d10050028000e0303032042c0c40c9644068032801e402c04006845a010709051410800300c10b01032030342210340c04d40e507807440d10215440440b20340d0000340403100c0c20f4008000c001454034440c420640a020392070040c1072422400155684003180c40c94889400d5040b451600045981228882c10619040640f66580b0303501d03080041d0050040c81100f50300c0d40807003254482c145500180b044203845c00006101c1d5603588900600c0c62146111b240d90445401c100494030000c0c0c0244041c0c8002c402c0c1462009e20000003800750003d8850805000388244e60360340d07030b040641808009200400c61116000c900e0924a40c41e250b0a521400a04543d02e0b0000290ba4060039000d600400d0304a82040e00c21506040600d0030700e10321007401c10140e210300c1c0c80440740c01052806942c11001ca8455040620085107001c01c0080705c1607080a0070307030f4048003030314000440703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 429401546 1250 429400296 429400327
    0x402101101050c040602100b090a02070c050901030303060302090906060603041509021005130e04020a1205120c1c210506010c06141008070b271306030203061f0b030705 74
    0x260000c3d1610076110342c20000024030f03207215180d184003801d040c10030700203068460071041b0b80c2180070300b5009aa6124282801d0422005035032101d0b400c04c00f00000003092640c90380c040740640703108903540036250b200c0703485044d90b40c5002d5420380d50041d03003000401c0010720496014141150009808075041c0403e8000034202c401021046011400c005200000036120548081c0a00b02414501100d800e02c0e401050074081ca9000d6940211040c00101090006c100012160340c0510890165101e108116403034880d075280c48901c1c05005100300108802c0c0c011103405071020302d0b0106424221009540c054068031020f002c40e0305020a140702100442c1141c0501e06455098503400c141e282002c40603855000700c141d00040c4035801c0a8014840800c0180c01c03911880003038068401c0c0b4044006424000c113606c09a80c69000320080c4500c064034040b5044402107900803401e641c140e5032162901c20200d400408042c0101100d00c0003800500008406542c01000f2031621505000c88520342c004c0c3c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 429402796 1250 429401546 429401551
    0x110601151b021e0405070c050303011505090d03210504021309060e011406090708061e130f0b1e061b4608091c05190303050f040b040210110105 63
    0x5429071625407484041c1401e0017916081051403070700e03051100c3c09481d101d8481c0418010510f0b0b030125440f00400792480b940070f9410080c00200b000c042c10180d0320703028081201319030f11f5610304200ca8440120f14015031142038032454005d0000b01c602001c4003d464000e243c51b81040312200e0343d40000c2881420300b40b050a9a10601e0480400a801c0107000c00c0300416000705001c04004020003000041c0c1c43d801010310001410030701c0040300d240803000043c240c0301c0140a8002140c6030045070b12030b07074096402413101503409442c0d142d51201c0004211440782c203446010780d0041002c115090688440755051180e00100b4410ba90a542c846d40c0d00310f0100c4000394401c100d220004400c106018410b01000c00684101d050218580c15070343d41d4072400340a002c000c0d41c880c031600e0154005c580c05010b59140780707aa0000c05d5608584504200c00460300b0140d0040c2e002900d04800513128075005940c00380107980010500d111a40e65034200154812806401420403980084e88031041209004403070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 429404046 1250 429402796 429402829
    0x209150a030f0506030307030e01081005030a080a0f09030305180a0b0403080a110c0904140f060f100906030f0f080708040f030b0a0218120a05031306110601151b02 72
    0x91501d002c6030038101500e4026001d1031003600b082140c1000a40c200e0444030702d82c0030a08048900e5520f907642010b947c00360340e000035094050710b00d41c001044000310080540c203415803101005410300380030403507105146010040100b03100300608080302c149a40d500003a524001c00e08000107403070b4078988450760010b51088401c444003190710703039800d83c00c504051104807810008000300080000001da980101510150005900a400c242d2440f018001034108012640032114907040c102c001030544207007104c7c400ca04040c101004290021030707000c0d03d42240e030401840c11850300107440d6142d030340a107118103c41c40c41c0d0802408002603860b0020744020000c045901421a1850074050307413070000280742c1e5644c1441041340700b000842da07141e0310144410549048250101c1c404101d45018400740010301603200108040420310300000762601624074a5035602c02e100c02d01c2044a80d540300a01801003158840c0107181440c0b8422111266080301510382e000f0049055004030724000f001c607007480b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 429405296 1250 429404046 429404051
    0xe0411040803130623042310020a06151a0313120807080f040b04060e0c0a0f050a0603051b0c0c04050109090201110f19080706320c0703030209150a03 66
    0x4100c4a0f820800d061400103e00e05c2100342202809003500c424440c901841c0103103140e01407440b451180c402510780c2d1810f0b014280600300d5070042c6c001380d915813149500b216024108a032900000c0c01c407001410413103c034100d800310050303143d564002c0c0740d810042865034403043d140149030120340c100c0309801030b000c03003030300c0f001c07424106640b008000c5000240f020001005000030b0000241d044d0f001c81c1c0d070064202400142c07020100c00c14a08103422101c0c09a8400981c00000c100b00d42503001503000c07600100e5650910968940c0300382c050350401c8654203410021400d28003203800521008103090351b007410a980e0000700d0f00d400501201c40c20f803c54041030b40d85588280c215608289201914502c4200501d008003040703040580d142e480345a10480e424801c89541c0400001000ba03c64550f4084070510007940d0400d84030320003880008030051900202c0048070001189266101c0c02407040ea0799403854071180341c03403e5019500054a25400898401c0c071245141c082c0c030007800d11900303656000b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 429406546 1250 429405296 429405299
    0x20a08090f090f0708010b04030c030f062012010816030f0c0305010617010e0c03060105100c0b09030c2a12160b090a08010b1c080408011404031b030e041104080313 72
    0x920f41d045c160040c48035031078204001d2020640701d485c114100e951041e0b4984ca2900689850000b514143c0c2e0b0030103144843c1c10342c0f40004035030f0002800001420b4000d0107041c0ea82e03464219036440c0d0321002c1425440c461035040c40424001202e07581402d024000460156a0780d03a076903402c40b4065880304021940811141480613000c0c080ea0345801182c03001854503201400c00281c84000600c03445100d2421000b01c170841600440d8100002c40c0c101d03640049510b0540d42d003e40701d07404a81100418050001c1400140b540904003140e0b4241071004446440203040038041040306a07080c2110a12643c01990b1f028540d58442030003402c3d4107034029448480010a0116100b120382054255904060360008146c580c0069101e800b03501a2101e50041d41500340420244206d82083c07180c4c0d420724030f02d1500b084081c2a1140518860380c2c0310000e01100c4940c503409040040001400101c1100d9800820301c0c0c56004904040c42000c1c038a482d15a035101114a180e0203078400040074500c3c942d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 429407796 1250 429406546 429406561
    0x1050103110303130b0a020a05030711030c09010b030609360d030c020309040207021f0534060e1009030e03100606200102040b0a080412050406020a08090f090f 70
    0xd01e44000c40150011414244c402c00807001040b407a000c0c0b88040700f0046285400b00388208146007200d9040001d480ea149a80c0c00d203916940200340c2020b003e445800720001070760900c0b0407002d040340d01245401b030442d21074008100c0c50050180c1051030002c1440e042c20900c0d4840e5040c4920a8221500d1996400c3c58003201800d00951481a20a1500e4000d51b0b5000300d03008411519085c208440041e61580c7c6440000c0036a440d00d4a035014028810903810003107500800286201d00c406001200702070040e6500b99260045041901d0711f45a001d01100300146482d00301446518500c42900e000c0e50456443c081202c5104c01d040d0002440224404410305040c807503200a800d408000744282828002c0c00f401808090426200310f40e41c40a003400074810a43c1914040c01200c0e1003036607201210180200001d400352015140048001c01820909014604031001c03607441e0f070044c0540f40f84985403280541c008041140c0c07c49200340c9165040d07502c050740240301340d030003000c601c16501740490f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 429409046 1250 429407796 429407813
    0x16030f0536011407020d0512070b09011a0d080706062705060405010608130303060f090b13090b010506090a0810052401020717010b03060a0f0c090e0a0209150a0201050103 75
    0x1540107043c49165440d018a0074600000c07140fa894060300c400001d200e4603e0001c2c5030400d60316203034004003800b0a0110400c00c1c2031200d140114856070003070098494081c0c05071031645040400300d9200d0303090760744a400281448003600b0181e01415000802d01d40c0d03521414034403a00040c80a07407415410a07081e03541610380c0305958011106850030001981800d00140c0140800750024001c0b800e0143e29204051003504040040c040640c03051251a41e0b030106240079000401c0701c40e100c0c1c40c280255044002c03a501c640c90041da003002042031664600400e0003510390090f00e417960001414074001c14a40003c020054032166031750780006141c40e01442c202d03000705a6120700244000811340020701c6aa0000d410001c0e45c0c01c80c2d80241c901525050707550300514141007819014001e110402000c2c405a40c4490041c9030100300a010044032000d08980c0c201040c01404040e0340c94201181e8143d8032075000d8200410040c000340d103c0c065003181128113070064084100140e4440d4014000c001c01c58 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 429410296 1250 429409046 429409147
    0x3010e030408150603030306011b080a020105010e010b0c1b0d1a0f0c1806090609090711010c030c090b0d060503070e090c120c1212070606030b090316030f05 69
    0xf0b2a10082401c0c0000040d0b203a00c4040c19290412460000400310000044000010243d00c0b0041c02d9482140c038202038042e107400d11680d10404103c0c2c00002d00210400101e40350001d0f481c010300125500d40680c0c3e96000d0140315004e4001d4402d03203001c0000750140354076012a031440300e103444481c640101c4030a11924000c00c0c0c0c00c0582d0061101c1c041c884608000b01c0741490007203a0301d0303071100b8124003c80c00c14007584c1901c5500c0000d400500c41080e40106038401c8202529009204500c1c4443c01a41601cde034000020300000e41e464001c102c002d40d80c5002d1308000d00b20f03030404107046a64200092504003a03401032107a03d40288180b00d0115010007060741e110600b500c091003c04225902552030384000c0018a004240104401c407003180c052000d04800003000f46016215895030400d40300410050104848010031003000c100300c2000001070703d59495140307002c9912000107070740031500c011400808ac000e111052042014542804482e0486661108400c01c003480920351070a0040441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 429411546 1250 429410296 429410323
    0x9020c0705060a0c0b0a1b0f270e060a0f0e070e010c0c03060b030a150b040f140403110106050d08120a09020109091509020708091e01020d030e030903010e030408 71
    0x10000600f90507040f24030901c031580c1041c48100142e03150440c050207003001194403071082800180e041c0d02a60003043d2030340c0318045a95240e94051102ea418540b800002000c54070350402d8013010840d03020852003441d4048009068001c0e42665090003884010140d00407000c0201030104024102743c0c46501840d40140905c1c08008101064480d00420344107404003400c4c05864a40200c030a0714100904161030f90f11150741d11025255400b03507002403041c5045688240d05201020316140c07464000c050300c4041590151180391500c4c0d50540317400c44460f00350701c40c554942c500040c19035103802d048280785000d854525aa00c0c4144d4045c0f071010001801000a2450300c001d07600541d070700c0341049003034a0496000059203815500c16121082040e4021460540000303400020444118081c01c840c0c0d20a4403040c045440001000c0c58108052003285c1c010303803000d071404a85610a82181026041c0c0109807840c003014500468251758404010380041e600c0002c1c2000702030020031510815079078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 429412796 1250 429411546 429411559
    0x70f12020a08091c021003060906080f0309010f021005040c05040501091a011202040b030a0e01060e1311010c050f06070e0105090105041208090d0c08061311010809031309020c0705 79
    0x68030b03569101075005107006a40101541c0b000b910220301e002056000940d0020202c100f1b10249980090180c06e407401070720003240c1000310004c1d55075000101061034449581c041c0d41000720040c0111030b85421006001c04601c1003401307001601c0701900c01c0794000d501440e10079207a203003414188410b466060388450010fa10384442c07050705103808289404403800034600b1030001b400301c80c1d41d00080e0040c0e421605000c5400030a21106204a41c041d003c440c0160009220761552030821001508040302d83c03801c81c1c00d100810030001005035001ca02c5002050502c003200a003a40c4401c0c2c0740c004420310f040219444041480200c4d50031114004580809103009480d049206000800c3c501071407045510548800420804106240d025148083d034041c10b801003040040c1001e42c659566403058100d28004d1002142020403909420721003140c024560716407114808004503901c4400500b0311210740014016044c01e41191948503004148454026803a00c6410f203a05003004c0840d0b222621402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 429414046 1250 429412796 429412813
    0x2070803011d2d09071a03010f090c020607030b041803020c010801150c034a090f01050f0f030d110f0f0601061101020705030a09060e01080603060613020c03070f1202 73
    0x9800141e036010342c0800308010710680324003240903c1c0c4040d642280203c2e00d4180086052811386c20091412500c00c10318401d2455907520a04040700c403d5400040140c00c20000649114001c0d004400300c2c1c180680006004c54889615140301c4440700401ca0041c3c002841c84c1501c2d42c0d00082203809001004136107059040104000ba1000c44c80200041c10320840440c054050108080c2200c1143c1c1446071240204400701016441040c01020b2401080341a2810207110304200001c60f1086a0414000d01c25909160800244c05000c03c60a680441071004691183c0c4040c05003100d901c040c5e4840703020880300c1080036402c00295003144c0145070300071507004009110009084d8111201400d000c001003010010380d601a100301c10014065100c002084200c5961156126084580c0c564820145c003000c0401103411402c15034030f41d40c0c10340c0407202007034403490901021409031101c2e1000610744681c1c2c184103800c68111000170b89006101c60701940602005071340400700560a4400f600c41030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 429415296 1250 429414046 429414091
    0x30c081005010f030c030f061707080721050109020310021b061b0a11030406090e0112030207171608010f1b08070320071209080d09090f02070803011d 66
    0x82c003000304a1010981c0f6480c0d145210346c00380e40b28000031074888509024a40d1a000c100150034a085d81c020458401ea040008202030081110001c0c0c41e120010500400700740300d421100c1c558038030000d4400c0e5503510484c070b0060741d082000f81044003050f1005616400c101610701c0c1c5020100360420030580140041006408200d100c1034034200c42209415150f1451003000c8411210900a080561200003004565150009208002c6401c250b58100d02c0340e0b00e40980b4010803848030300040c0075a11519085c49003034034401d40c290b5080d0510044070301c40c01c0c5c100c6400340591515841603545941d074040400d00c000e99401070002c0c000808508003410390701c0041c001c140102c000d105000301544c4482241c1d4210b092140959440c444200c600d03260b6120341490070300345052481032008101103400000342080007040b0001644140e8454860703180c5060f020802408041d007135004030300c1e401c115580c0050080d202031806030240080007080304403051111103408501a050701c1d2608125000013190 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 429416546 1250 429415296 429415307
    0xc1501050a080d0206060d050102040509150f010f0f1d03010204060507060b09250302121e150d03120204030f030c06061e060302090d050d0f1223070c02040c030c08100501 75
    0x30540941321f191041c103140c209140280516080643e0002d0f802052129150105003400c11002040f184101c0403003d0100561389541c0000d90700e00810342034840000990f020b00741701512030400c8802905044000c3c2d0009003242d0003600000080341010520310b09018051003003022184096a480280d070070002403420781c0c280d10294030342502c11640070103000700c1e01c01e406032100051a00e038403185a040c0050180c404000d41300381c00000c44207400005011440c40d5030004a05030000e00410050610394a080320030105078042c4a0000e42c003004004001600710040d040e145001e0b540324811401c1c1850722070191105548072203120300040951030f02c0c004104505c001240c015080042c1c4e15028140803c208071010200645103015044003012040d4000c90032449800c46c955812545442c050544c030110313900c60a80352000c0600282c00e040c003240d20070804e034010a05080c014120700b441da0020b000e42e054103c142001030345503a0480c0006412030307503240d044a48070394094007042c203143c0000c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 429417796 1250 429416546 429416551
    0x50c010b09010803041e0608160504031e1a04020108061003140405061e01050a050603150a0b0c15090703020906031204081006050d03020c040203151c12090e06060f0c1501050a080d0206 81
    0x8060700c400c030389e0100c1e190195040701d00a6600c014100a851081c602002c51021882c40c11b030703001c2482c410788006061003000101d1045034140c50780c40d260340b01c034428000350350340b104514401d15039684031540a4030003910303100344514410401480316140011b202c0e01c850765407560b4850300712462001407101d035603210001c00036940207942040d00c9650b0b914031003c1c0080c802c644150047c0190341c01280320710510004104080e4050216020340708085e2b000082c5850440d82120700d40c0164000340014604251a140c1040c8010304850a030040c0100c010f540f80d1044d03101c19942d60188840c4141900b050003450014142125803107003c17040c40d00e001c3c0d11020301d004030030301c60f41d030010000d4020080b41e0030400401c2d501404104442e00810300741c0c00000c0d4000001e0b2a9002c40c50f0203012414400c2c4104410340303000f510314000c6502c2d01c00500095810540c410780282600b4402495901e00400950109030320680e406030340795240400744149480d06800880381601300401c030f608400c1d00010311a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 429419046 1250 429417796 429417811
    0xc180f04020915130b0f060414040b03010227031209030a0b0712021303050c0d0c090906020d020c010b01080703050c0901080c0d050108030715020403030906050c010b09010803041e0608 81
    0x2040b907642c030340a04076a082d000291a0301c00c1a07070008011039562540b00700051141a42c2140070501c006d000c10603680240c0c45044400c0b0102d055a203100c0c01e10780c22091113050302034005401c1103504404000c68064114034010100300d40703500e04500d450300b009041e011405d00c0c860305107080c00c0f01d0f0100b41c035400303031000140030f00088a0114503200c1c4101820310080d455150115200c22115007009103049051200351b650b849003860025a900c1c0019030001825448811000220700d000700d8500508030300d020940c0d00700e80c05d0201000d44a0701340010a003101441000140c1500c4880000d456144084c0c0030004051800080081c1051003208444580009003001e0030942c4e5070214100306071282c0c2541402080c101800000e8512001000d04442d52007145030114000c840140e00c1c1c100d01540c07101a0000702003103820014940982e004002403070b4044004902041c2002c0481c1408400ba408a51550700004040200040380384c6c00f0001e4848404081920314a00300c0c0c001c140d080b015003000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 429420296 1250 429419046 429419059
    0x32a0e0619051504030506010504020406053a09020405070c05030a0e03100c230c060f06060705060c180109050d0209101707050f1002150c0c0f0c180f0402 68
    0x85481c00e1001440001c0400a00c050100a07000c03100d111160001c0c03000311145e00c075060010813640341c5802a1420b403501691243c0c103051180150321410400c1001401d126911200d1121080c1c1e1841c50391032000e405203002064540d010301c180021a040144800200000d08840c00c00040d0048110384d03d550981c40c2c440c032440035110000b82490411035201003038502d05201d00d40190342123903c68040e038514841c855811310000c6071080d100d100d0074805071810340200d000034031201d0b0081c0400350884400b8004078200402a81e95a19015081d506402d545e1004a5522481c440d1480589a0420286084483d0a1800300031603d07807020158000d200340d14040c0014004a0510306110061181c00014804203240d02e0510380c8070a92409840e0280c0044419800a03003070046541840c1229a4004c0c070000031400103140072103101400030031841ea4104001c82c0d5100c810480c0311040b15914001e001d021b2280400c000001004040c0149440c48410801030800034440285900c00d030140e034007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 429421546 1250 429420296 429420319
    0x130b15070506040c0f0b0706180f0f05070626070c0c09200408100c030615080618090d0c150c051b0c2206030b01032a0e06 54
    0x58008121044810618001280325400d000740022071038040c601520803010441d0725522060310031040e42c01446035000e010460400024038a620103007503d00001c01010b884d0100f5500c10948800901c1c00752051540c0640c19002e100c01880480003c00c890b04044141c26001c00c0c00b400f082d030610100e95800703c180d02c0090301e22401821240c0b4816404800344064130303214144200142088210b24591201030b212441c07909440ca001c40e800d071000d0400600146070190a480c01618103045280201a142c140000d0301c104810b40040304000c840e10b82d0049440e00d00c0603c101c040c0c0c54140c0d220700100311000d0003600d40303020600048500d0b0628101c6034103001d5042928204942007801201107141026400340b05900c800607040f44201005ca114480002d9a500d50f038a01c4a0f140113130f03010003818000004013045100301140700001c1d000c0030917843d989850310700c05500241d0007600d02d00c034984094a962010221202184201c42000c8084181420f00b1403540074001004140902c500080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 429422796 1250 429421546 429421549
    0x9080c010c03081e0f0f01080303060105160c0b04090c1d0a060c0309080d05070515040210050d090b0c1e03010608010905040f050106080d090f0b120709090f0b100201050402130b 78
    0x740d401d502d06039500c0c0d2103500701086a01700340201224490201a200c000104811401200322401a80160b540c04d00f02203001002c4000b21820700342c00c458104104500003412a449400303000280400100000c1a000407034020f08020070745034414442e0b910000c100d6000da030b035103220003007910040d140c021003440d0646001c4d201079800d5041004544a0703031100c40403c0340e201c0001d1034514402d40c20741d411040c0d40c0c446440180f1050b038009500400b00c11020100c144180041c1035559855040800c41118580f107514600d0300a4844004035900016440c0081050b4055201d40c040d0304180d244c5907600d01000100100018050400d0b41c940b030314041014868804040303003c00750031800800c052907035504065905c04c0042c3d00e0901080c0700d07690000b281c41400300d01c4001ca840703200c0603602d0194104524070400400600b11005e1003094200400d5417203861082144151007220001404845081000000301919520404580c140b40c00c100060b101d41d000e0348078030700c2c261a003c10350300c85080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 429424046 1250 429422796 429422821
    0x131710020a120608010903141c020f090604030f05060c0301060e13020d02121504060f0306020c0123010321020c0409140a0f0b0f010302090c0703210c09080c010c0308 73
    0x1065110083d00700b050110784000194002c1042078840e460f07981c4400d00d4841e1a8880303000b0600e0780d0240f00001b90b031100d0034034040e400a20321040900045440e16000000140c01a00250021b84d010b521403599501081401c2112541080f41501480c0c1158906400100000310303400b041c0c6c0c014103200e61289840c0700326805407420300303c641009648503c14112808a40c0714101d0b00c155100c0c8800c0114245802e19200d40310a58482c0c2070801c2c0c80904603102c0310065403000605510a42d03840d00c8120007110102020251140700102c6600f80c3d514606002e02002144e0016100c3c549407103040c40000d58000400034074403081a078020400c4151814200407030000b105030a801c1d0300500c50714400300300d0942c03440d04840703200b180012075548980e402c2d0742000724240070081d0032a0001000c548800002c00150142501c6440c1c100d005280402a003011030b5000108420120749075081c40741c034607030403081d004080c018110003450a4001d0500007070691012100c00350a011480c00415a24203142c0d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 429425296 1250 429424046 429424067
    0x4020f03070c0c1205010212061e0d150903021b3f03030108160f14090a0b0402121608060f19050406030503120108070b040308090409020405040305131710020a 70
    0x8015004c06801c4504120b8041e40c0104120f02e149046c0400068451034a4803410102485000e03034040b0092844003440104100c0007802d59007221080180d000c00305542c0540c0050314803aa0281c111895030032074100000d0324aa000500c60b82d4011041510307a403460341441d820045c01c00012103203058015411340c0010942c282ca80c0240000000894850350005002c040140241805510203990b030103010b190020901806145048186c501c180a16161650300c0d04601d410400203070010019002400b00c1e48510540e03504001440b0400c41d140c007c062307408000001c42d082441c40d6151403c0041d00303184960201e14424800c1100f20b5802c02c3c000e140140240c03502500401220f602d81c1052a43c80d0466201480052a400c00108002c603011411004462600381214109419584c034088550800074085800650701c100d803801599882c000d150185020340c0711166180641100c0f40e0300c0700040d421100d141010856080301c1c24400003a40581600c0c11280140c070b40511031000c840030501c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 429426546 1250 429425296 429425309
    0x31e030e030a05210408060a0b0109080604060b04141501051303021512010f0f06140f0d0e010c0504030506060904030e09160e0d0f020114040504020d060503070504020f03070c0c 78
    0x42d40c207480d041003000100181507001024010544085100d2040b0715841207002d00900d54210742c020072a01d8415421007800190141045042c032a21140d001b45003840440d010f5850a07102c4694401303d0810b8800d040e1440d00800d150b00d40d0340f8102116001140c00f00039054104100003401e0480110f1018440014590040c6000503400011030130110319003007481004030704030f140000010400081486081260316501076030079802d2070102c055446d0140300d502109038410400c2205041076442005241c008d49003180043c454400040701802c45107010001c00501004020038404164000b03180350f48202d0894072440b00307a0b1f035440d049a000c0d000c5940c494008205030184014400b607010500400b0f0b803213030380f2030b40020a0f54081020483c5005030280c9100307001c00100025503c10f00f00c003008820b041c544d1600c0d00380d03540702040403680001821740d1403503035543e000d1045107000d0014100a00c0211025403d00034850764800e440e11020b09005c05011071a02150104201e014030f1174001c207070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 429427796 1250 429426546 429426553
    0x1104060f0e1c0602030a0b101d13020a08041104020309100e0f0f06091b01050f03090f06010f031406010f23060a0809060601021f0c0e040213031b031e030e03 69
    0x407945080b0f4080d41050740c0b0094a14184a0140094104881351262480b1507039218850b80e0303108940d2010f80320f810a0b819030800345c1e2000841030841c05000601144004e03642d04822460503041410305251400e104501c164010400d03c42e080c2000140d589045e80546000520a440301c0f54051411010860400c3d65014160129840c18000304000744902c01140030340d5640c80014031034890041c03100e01c009000c0b40c400d2102d00100c031061000b965004445404440e4a1090f140c011440c196090b44030588078090300c0b10034010410341c06000285080800003c1079254100340003031880c50030b10300501c0c103084030b0005107003180ca075090f45440756404090040c036541e0491000c002c21008048440c81d03030f28071404010812551000440295aa800101c0d034040196143c4070032001d0280d0780d110204001d0884c881d40816034591000f00021803140c07072490f0246d4a1494a82c000c0b80908412003400c07002c80c04208085080c8202c406141d18a404000460080b107103000d035407604c03062034069018030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 429429046 1250 429427796 429427849
    0x90b01031b02150a0509030304030c05030903070e1602070807051c060c0e09060102152d011e080613020105130e0906010e0109090305040e06030a050303040302101104060f0e 76
    0x307401103800c0c40c0280c910041504103594511301401a10b0b4203030390401055004000003400320340b089403c00c030001e02c544203072032400d0b01500021346032803142d401800302c0c4983e030300500484000c600b01c80074004030b00d80094601e16182418558940c40d01340715590060002400540c844035203444d510045540c0624100060296108014868034615132054080c000c07000205006600001e18040080c4144800d1b030707440d544004205e44540c051410444508021000c440f04100b00000901d0180c4a110715840c0b42c5e608140800c031f6610b031254400c280c0750304450b0900c009a6202c0e81114030042d020308015541e08040014407c40400c140d011b000348032002414064026004a6010b040b80d002c480b500000fa46c030f0b8028403007121125031004010030400c20081045c00180464142d02280041c1a144003c4581e2240d905540c01154210016000001d00100d42c8181d407040c0420160070260701410320f81450409441005440014810300c4050008100c0d16500c0304400c510034076407403030781034003a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 429430296 1250 429429046 429429101
    0xe15041d0c040c050c0a1106130b0c1507050403030302071e14010609021312260d050c0a0c140709020f072f150d0207030903050f010903050301090b0103 67
    0x802600d07150030310076030400c6034510320745104500759542e00c0200d2020708069022541c031118040350902005030414414000000442d84407140c0100034001368000355590b9610038055030400042852500e60200302c00c05200b1400e50260a9030247d80e411300300160b64030040d0400a81d0358440ca107000c215000c600c3e99140030003d20080a1244040c144020700909440350448030681c000c556941c41000d0407131000b004018002915039074400c2c0501040407650070800180031500001c20b50590140c1c9000804c52284592449800c1d440381c000a0168200316100c0801401900c10703501c0030b041032007910078100709072006101603401480c14110456484180011602543d00440780a660394030890f4001e000460b6103441c00d070b00c2c060194880100f00d604002c20171211007080342180804100601510074401c00c2480100700e1540070340c0f10001034901c1c500c4c0281c5840c03184102c3d00c109906020f00f010020f6000030599045d01d00036a4040780010000700101d000709400000302c61100d0010340e0354000c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 429431546 1250 429430296 429430303
    0x14040b06370801150608131e03030219030b031f0e0d110f030906040e0903071b1703070f0b13020901091a19030609030e040c02010f05060301060e15041d 67
    0x1200c050400902c61114081c2c09011842134902c960004581c1c0030001034003000e228254000780320300c600d0b0810220f04c80201d0141c44150b4036002100413079400150a1000b4070013406800e150200b515061000400f101c02180d00e60021034650800c4551a01a40c981d243c05500201100400032084520f100c042181c0240941e800f035100114a008101c070f01800c00101000b210500180500402e20301f030300c1e0158520796104000d14642c0b043c0014002a00091401c03030052210070804070580d0000f60401201e07040340c1514007420102c0d540200301910001d40303103a20b150445a00421030b4180c9070f85500b40d44d003101180da04000c0d1b02400e42c0c4004242a54194451031600340080c0d0001803100f001c0c018400d4400364143c02d00310b0000800c504100050b201e402200300584a40b030110001162940454181c460086064015075103032151241400ea1030300ca140c4d03002008074020701c0075918052444201040240c0740c010280d940500e2040680c486801843d41d54059018400320f02c144100d40c50746 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 429432796 1250 429431546 429431549
    0x2010e06030702070308030a1e1d0114010e0405010b030708030408010b0a0e0f0405030912150903040e04110d1205070b150f011101150f030b0a05070807030b19081014040b0637 77
    0x11942222b2402e0040c1c40148640c14043d181401c0321406a42080d420010348840180b0480d1150f40b41c07110030740e21b03031014400040100054401075031214107003404542960800d030581b80c06804054400c1052040d00041142c20062030224502d164940307040c0766055106681402d90400e540010f00d2141d010002101c050b52150004540115110241c0d042c0e2248180e202d247c60301c6491a01041c0800c1e03d1407440c1407507110041442c3c1d051141c40d40d0f80c00c0418001720303081020880101e031704021b208200701995408541605859122401540060123200040c154641045010211810041001d501081509180d249002030055694480c10381308201800100d80b40500b05010550a500300e014190141c6019141d003d8950f40340c00c0110700400500750100e80c000c880941c5032010500300990100540040341c09880424a440000e070166030700c0c0003603200244000c10411010800c0c09040b01d0700040300b203c0341140c0b82c2c120360b030444d010b5210780c0c0441d01c1003039110000d00d004400a10500c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 429434046 1250 429432796 429432821
    0x806040b01030f151a0403030e10020a15050702060702120a050a021f0207031103090105122d060a06020307020d060b0a0902030a02070b070815010f20030702010e06030702070308030a1e 81
    0x290500c0981002c1c0081c02140700090224428070045912880d104c0340c071001e0b2484520464133028140c0c0c8844e40b01980c40b0030041d005590314000c0c840400d03418000d155020109000a02004170036500814280c428469000308019010540c52045842801894240178103010900b4840f402901488029030290f402140032074407008450107842e8010040d211000016101c507401d0000f1a500038009000c0144010b024560b000b0f6041c0c2c0900300c0c81401c02003003481e2822821316185c000140311300d20b41c854011109550080c004c40c0010303901c41489100055020401046030903048002c02c42c1e0200c0781d00f1090b0780600110070080401c640f0790241c1546402900c0074103007600c4500098644480a039445035840c40421056121035020b080c0c800c0303c2d011285000722140660b20074103621816607010103401500009880703c04d41da440030350301102003400c886061541c1807410001e561510940720041c50b61402100003010300c03505901c205040344024104140200d100304680000740200300041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 429435296 1250 429434046 429434069
    0x15080601050d08030103060c050c0d12060b07080301210503040815180c1e1003060503070e1009091a0c030a110301060c020103020c0c1915030506010806040b01030f15 73
    0x3250700c2c007101100c02c11900700c6451481d50b401d54803100c0140c44800042000d0140c00c02c051940400100030b007a00304907039543d80071010f04442e201181651040e074442184ca0a0500244010030264812281150503505003251082c0c00c4031401c21038070450120103019404082000240c80002091014000308500d25140d0b8903071b0399030b084a20000d0b0001203032800703510070200d102d11401d00c43c01502101048101100501d03007040e0005840400495002d40042e484400420040c2030400038600507006203a0f03030b50754501c0c04244442d00e00401b441400241d90b29080d030002071001900c0014884449182c0a00744c40c60090340a140703035070043d6140c03031001e032401c000c000c500d030a45e10507281641c0c16951489a01c00302c0b900110040d401c8400c039480380e0b006d800319500c1141c1e5466032960040c4d46401381440c0c51850103c8140c4001c028900324000d050400c810440316a91080c80c15620000441d80041c00300700420040300200814014141d4852070503000c90b148204030b000c007204442c0081081d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 429436546 1250 429435296 429435299
    0xc0d050c100f0905030712030f18090c080603010c1e0c0206040306020c2509022506060e1005090f0c1918050303190809190605070f020105060a06050a030f15080601 72
    0x181540c8101d1071290703214010f08030291f100044c3c421481001c1c10a1a031034403030350092a030b503002008018958003641ca4246e99000c03a103861034101c3c003610752003c0c085000308104120901d0281003000500640002140d034584c0c88100d007400b580058100340d80180c03200c5d0704c6e1a101c1c50801c0003980308001854051003061340c01c2c0b00303c0400400c85032220040303520a800c0c0a1a1250302d00203504402e0b41c1d142d4102c041d0b5841d040d803a1039509800e526a005070070104031141f034035006246c0c3c0c540142c0024042d98a0700c030241f091f80c4070001101c0d0840c142040c8000c40d030b546e00e4003a40490040f42c110b0703d484207410400101c4d06903c101c0600269590b20f503400710340c03036441040594034820340050030000001320f104071105c2070050120b1588040400d082e00d0010030440140c40d184164550226810381d03403002404040c039403241480d880307500e050008000c0d40c101840040c00100ba030344218420080009115031001c0d119412050003803c3c1e698007488038104526060300d600919006401640c0310b00d500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 429437796 1250 429436546 429436549
    0x708060c03180a021302090607140a0c0b121b0702060307110609070305150604020412300206040f060e0f07050405090316170403020d0305091009080c0d050c100f0905 73
    0x142c0c081203d500a00c170100e9446090013403006500b203001c00c0f0768071040070700c50070380491840164030045030300d0503020380010b00315807500c842800204c1c0c000c619110014481c40b00314001000c1601e800c40d00c003400144201d1000001048680f003002c100075044080030080c880c00a820107000c198a02116042d25000c1da01c24405a0b5581e09920010700298488030321501640410341d5440d8000001410241c6041d4072204680c40312410010219011010b42d0125020742e00c284440c50718070003100c441050a0b00802030000d680d0380340030b0005000005552009070030405940d0149540246001c162010b018015042c07a445110500c2610f0007a82000c000941608004c0200c503294042c82c40e5017031a0382d50549408420341c8920940c240000820000400980d8072040318600140c0310380d84040c0d881011505110080c0d288402c04401d100c1040c074244060000840e904483e603009032000c24004078241426482d201d0b519000e0350b0440400740c03e207440142d104c0c043c01001e05168490250039a920f40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 429439046 1250 429437796 429437803
    0xc1b0c0108160c1b09020f04080105070302070c05190503011b11030316110f030d3804111209010506100804020a090504152d06120b090708060c0318 65
    0xa541c006a0000a550000f07010030750b40c940c1300c114910345a101951114019400c070307840a9032240c064000442e0030000302c0d03824015079a1294a9140950034035804e0750759410007186502820b8840c0114015144202280024080040c64028020f000e110441c55501340011415068007002400815180316017500003c03c50340151301c00f0751021441c0540c1c60f1704889203a4018007514080c00368452100300c240c42000600803010881000041410300c9035a4081c0c1e0074503508485007480490440c20300c0148554580308009002658042065070220700c026003a441207000e00842805d0751405e2100e07650341584854070881080d0f400c100d8500c2c84050540c2c440300100c400079400840d6140c04e2196070300c82d401c010b40280c0300d1100304004600d81000c01d03003330b518032054801039903d1001c410039651460365950080316081d00c000300030305403c080824205000700000602401e40c08004107203908010888000244040402d40d19241843c4441010f507900580301010007114a1980034507520000c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 429440296 1250 429439046 429439081
    0x10b060c15091c03060e06240903030d0609050f0f13032a030c06050c160f02010509150405030c010504050607060f0b06160605130f0b0c1b0c0108 64
    0x51007080011500100d003100d0041000e05240141c0c00310482101011215000d070580c1038501141490601441c80030481d0010007080c403c20041041d4080c0080b214a140c0018100161056441114034042842c600c07175451044101da213440740020300100c042d80030600a030121805108991034117183c4d500101c0c019104030610030300d01650000002c1c040c007174052492446890200e82001c02002c40341c0581100481500032800410300c0408201c0e4511070103912010f14501107003481c505000c6410390b044900c0000700420143d84000085d603002e00203481400f00f00a1107004656400d040ca84c14640180c80782134003d1064001201482d03000e10243e03019502c0183c0810305041840d1942005041e141000c05a455600c14010405403101401040c5c4034420f0340e440d0703610030301618100301141d0b0000c21200400300300510f200002400030030b516010b40e030003509101c9651503103054000e9070300c1042900b441c0c2c0e040140c08132420000124a11040703070001d0300c81405540d22051440d1560780074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 429441546 1250 429440296 429440317
    0x10602120f1b24061005190302031515090f030f0705010507020a03080f0d0608010c0804030c11041b080603012f09060403200102010b09160201020c03160519021e031006060e0102010b06 81
    0x614442e490307588230380d002e554820366103404041c24242c82c0022941c950b040c2c41c2c1c40c0c001e441001130005420b040001d084654090254000c100e103010301900c1c0341d240c00c2c15000e240d04001000903c0c800759520b405041001c0c40c2c010001555417906074000040310382c84141e40090751403d20000007181d85040c414074810390119100e0400660326690304580900082e03001301c51a00d540d0148010a071554400d40800d6415070002212039940c45c00050007010000381054800d83c10100c0c0940103424489001100180318402012100510106448203001d220200c0743c119030301040001c01d2004081031503d1105c26040e030300014401910049080e0742a01c4011600b0482c107001003000c1d0510504201901c0420340b00041c20006024859802d40d4031403a800031040510307044100c00d0207014080300a08030072114403559982d54941c0030801407021040801d82c5080303d000380c071030a0f840c140b00c609201d103024401004802e4580c4006042000581a00703401580382c041c60344428103102c02124080505d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 429442796 1250 429441546 429441577
    0x3040e0703020d0e07030309140d0f08090102190503030f0c09030c1908060109051608070f0503100e13060501060c020604030204110708070b010602120f1b24061005 72
    0xc85040950180d03100c1c02d00254016038414850288200c24030294001d0340c1300c0e60380c0c81501c520340900042c0421410814a102d0042c1d5581c0f0390000b945c0081c00c01000354030503031842c0c440c40800d00507070401801540d48403041c00300d0943e1404102d004401588500044005d500300f94880005070347c0d080c00351103a0b49130140d100d00303129140b43c9421900d40300009141d03178801d1107442d1242a0f450a00200fa40325401194807001840b041d0042d140c0b0384611a0180c0c9004681c51400000090680540610404c18448000017165807080c0028800c400703080300709050704290600234100b80240c0c103018810349406203000c0002ca07005204100440030190010895402c040c00c42d000c0000800c401d40c8042040401002500c0003c1d0000001e06005d50043c02e00f1302c481d41c0360500207402d0203005c05029a00e06010414600054440c40543e15031603107084085441841681d80140342c4003481d100c01c0000741008495140802c032800ea01e030b100300010b49010444c0e6030016015150750180c540d60392204ac0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 429444046 1250 429442796 429442801
    0x210609021003090b0a1b120609150305120c1906020f0304420f020c06180106080705150d0905120717030c0a050307021c0908010506010908071a0f0c16060203040e 71
    0x20310503118030390545c21145002848d56a5080030724212210051191001040f00104000b03010050042500805802540520300000410b00036110090b20100c078100c1c4407542c6058061260039030503201545980e60303005aa0341031505000191404072110040040c4000100c00b0001e40306903c1c444079907140f00382c0822688038103844100507040b050107046103298240110045010100300701c031b01a47d1000b80392560005101200c0e82500c80c550002808d580c41b50130100242e03141d02000156003a445214291a0242030a6100141c0404a00507140c0d119180810403c0c100d00c1d4010100c00348100310b8808065200d4032a101c00d4001140d625000302424041000720a000c2d8008507401035243c070698403211483d000080100400c009980005105280e080c000305000b44101030300920b00b400c110281516241c4450340d20369490081d400d00d940300034484a54140c0c0f1000351031344400103201d05070300d0303034441c2010320303503404003a03007503540d141c1040800054a5001008035010760700c442e044807840f503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 429445296 1250 429444046 429444101
    0x90218120f121b010501140a0b0a0e010e0d05070308040f05090103080a050a0c1e0b01080318011206030b090a0b1e06010e06040e07091a04210609021003090b0a 70
    0x5810055803d0040c0244000340c42040e8000c0c42000d010704051030603840002010014031424071600c2e04024142c080030403030b8040d965002043e400c889242440c01609803c51800450441c14030340038020700030701c50b1078400f200b0070034510080e00c01c3d19550003c2c02949a9620100100c81d9000c1c80301801302030b01003202e030380801e00c944020700d00d9010728181001b402100d80c1d6200c0740708104088402119000780c02285c10051070804403401000d03060000c500b080603103400c61900b119900c111070b040c440701c42542c80e42001c031a01301c03600035038020b016040a490300e01089520b41c400c15504035804c8400301c0c001000400c60407048022054200b130300c461144c1e25540107550303040e0300c0300416501c802c040c070001640c0d80c414038600d0f00c0750080340da49903c0d1510301554000a0b0088440204072401e050200f4804506180c0520310384070743e01064070009104070b043c40300041c0050000030750842042c1010006c4035826420002c1b00c07900c2152006103543da840741c041d0417501012404109401201c5809154 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 429446546 1250 429445296 429445333
    0x601110106030b01090504170f0a09050d02010e01121104030c1401031806020d020f030c0c010c0806010f1d190f0b04030b0612010e07090903090909110613090218120f 73
    0x5105610a0303c1c0c403400041100c43c1340d0010f2240550201e4000ad0b003011281c3c0c0800078200400c01075603074005804243c2c2c001b07000340004000060421142030202130000c00e8503000703a41611000c11103030340e50b03c2c0c890401100e00401e60292130603031040342a404110b5482445a07980c0140c5002c071000141c400b59a0b0700029500281440511035001d010100c0c00d40c420300025400740c0940210103544d5000c40c40002e003551500e010761010b100401040080c43e9811059404410200d4a80826030000c030b0884400d405260303d803065000041009154801c03001400350400f07031074071900b01007842595034002c1c1d4850312603400024584034075000450014201040310705810200440082041da403440c200600c1c1c45025481b000c0c2450321060b94a007455005080980034020444041c8081c0d40b054451034020741c2c05440482c01044005a00c15000313a1400d0010090100c010040d5510307010708941c840c0091900c94424411803894555070081c3c00006041502d0010102c0074101c110482200001c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 429447796 1250 429446546 429446551
    0x1140a09060f020a0510060e06010e03030d0c0207030b0703060617011d04030e15130e04050a14030f0408030301063b06040f030c061e0206011a1c050601110106030b010905 75
    0x198032450804c0d8000400521800c10b200c864007000041052070300d03004081c280f2015080d20306000340c9807060301460f1400b1088030007140342440042a1301e410410100c2c40c0401d59840035140c2105a010b00542503499080700f8221240b5542d14005c01d2065100000101420700c9200010114400803028104075491540e0b40940a0300308004c0c9602500c020880c200079010340105a1140003403100100b2401c01d09190141038411000400ba151994400340c0c3c3d0342c86088054040080703a90010001c6404100300da41c44664070082ca512707140e4415003c5e9803a0020300580010863f11030f40c603c098000e041c2d840110415045429001381e990030555003440c4804500c154029804000200e10100c510b000f0100075441856443c04a03481d041c0024000d04c040110301240c4516400c0d5001020703400982c0506603900400341c0100004861aa018240705065801500c1000b04070305012941041d030040303200d40e80170b803105070700e02091407452400c96006000092161192000621105c0120752009a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 429449046 1250 429447796 429447827
    0x1080919060f09050c0406090603080306090c04081e0618031803070b04081b010905090403030b010302250b010b040815060d0b040804090605030606151315020c01140a0906 75
    0xb40694400394807a041d1030442000340c916501c04c15040405e0304091080c0c000611081e00d0804c000e5056548111030b0348000b0306810320820010000c40c9003a00350300c04442c014041c00c412035032441800710300d03840c440900c041401312a000c3d00300003031508401c0340034400800100d20007442c0340450009064801d0400d5011454040c4608a8086071509926000340060080c1030f0083c444002d1007903040101403808035001b4100716020b0310805c080d4440c1c250305a041645030502264511064004138000e003e0441034241c1c04402c1840500708044032038134030f000180960000c100580e261456095144101e00c50044140e21542100540c0d0030314140c42504000c0c024100981c9038a0703500da441c1040c40075201542d10480001d01005116a90311465000b0801640581400c0c58103600003441c070034814907501403016002804000898400032024040d10020001c1c55105a08500c02035641803613501d4103010039503200e0340c40036010070041520f0000f089680e903a4030060411008aa41a100b01c5d070720b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 429450296 1250 429449046 429449051
    0xc0e0106050f0a0e09092d120315040f06090f090b060411070f1109090a170901030902041a030c0406030c0501050a020a1505060a0b03060127030507120201020105060108091906 77
    0x40040d651704200140610a04c800408022010201050303e407101100090304090301109419603015012174200c01d00d0b421588016100e0380e45451110070364011000890b4000e1900c0a2008020096800ba109960300d0a03c108440d407000504032040300d12100380603140055100028038240b5003500142c0f080000a0142410040b1640e02d000107010034950031603050202c0004002d0030304003514031030780c4500103038020095104951281208000e003040c01c486800c10001e2203aa06902070740007647c509034041d004021207501c65040c80c00a450240c1a85e01c61b0003031007208412494a800740800381e80d0020855190a0f1401c4019205a40018840c00c20b50003244668808120912a102004040c405020505250050030480082d4031074102c6611500180103005803130741d02100444041c5200740304036003040da25075808101d07048a0b5000600c648900f920100b0041e9001000c140120720030380081c400740d11000019103c048040b81c2011881e0f00c02c001403911183c607801e0480c001d60041900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 429451546 1250 429450296 429450317
    0x6050702070305032a030a0903060c1b050f0d0c02060415111902010219033c0207140901150c0206130605030402030f030a14180a0e040c0e0106050f0a 66
    0x103d03070850b0008010079141d05000d180c4800f00b80c0c2c042ea4442110f61095014604e06001040f01410381130060101800e00755072004e0002d01d05020703405c01995449241e00d5401012030b14a0001d07690030380080f1480c107500812540c0c00c0748600a20700c08440c40d500400c054241400e01072500c860508a412070420081c0c25a00c00610420510104841103222180c0707034441c80751030001928120341600d00001802c0c00300c030000082076102c4504101100c408510f181c10100e42110b0643c1800030640d14002e814804001e0384031242c000404c0006c85d0303110100051014051010082007030800d12505004403440301180101600c16120340120520050684c2e0400080c03903108146a10f098114a0200343c00009003c194981004400c40001c4400c0c02140740c08180a0000e1100500b2101c1d280034a1010801281d40115554240300c0064050a080707800d90342e40c1e1461911540940342606d5041c41c0a070b01140b00075064000c031f41a41d01c0c684032645030100a00035022113900c40e070190400c0200800f407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 429452796 1250 429451546 429451553
    0x1e061209020603090f071e031b032001030b0d05030306132403060e0105070f050c0102070602030906160801031101210c03050702010f1a040509070e071821060507020703 74
    0x240d8010342c0c0f01070045c0103042244580c07503c1c0c150907410020180c0c503480360045d202c0c10000c07000010b4940c8280700c00035020a80c11802c0600d10550001800c90300c2c13402440d03551401c01c01c0040b08403102649e0601071800403605104010300009400f13010760300100000b85450401480c1080c9000302c00b003000032104c00c840c44122040352604000c03442c881844a041050040ea402000090317560071000300070318280700c03030040c20748062401000b042c0440800e81c00041c006c207505030b400d280d410000039075803071601e012841d4660000310f6520405030814203071175100710311448130181601d5000030113030188820f220055402c00032254030b001c2c1c055496105000021a1805242000401c50310085000d0a1003440a0300355884880f600c04458604400030040d003100800142d181002618006480d480314a4024107250311504050f42645599050007120ce620044081c3c05203403403401d6a14040c2c0f00e0307181440000c5074240750f5214040d14014000410703203e91020380c0001d0700703004880c0342603900d5a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 429454046 1250 429452796 429452809
    0x90e131115070606030201030c1e0f020307060603060507080709060f052a0604060e1219020102070c12121d22110403050c0405040203062221091e06120902 68
    0x801200c00039204c000800c02c41d45c040c05548111101030030607040da6024000032803000031055180000700480348150781c44003402482111403003504203a05226003600c2e82051005004182c43c54000200b0100000b1055480b91013581e00b512016030301d0440d540b954040464568004100c0d002c180c0070440c5007a11a801c2c60524120b600380310341d019194529003820702404076004039120302d5494001c0c0d002e0448000c080400ca400c40300310707054502050010840c2c200d009003e0034070010495035041d000031541ca00540300403a070b11440344a80000000d0005000c4801d5800210003044401d1102041c00080c0381181c074075940403010580d900b215184404118056464685040c107402c180000d05109020090008441c84001620309002034201580800d41d903100041c49100d148090700d2250002c20841c04808590b180c200d224040c403800d00380b03541d0540d03400842001000c18040440003414400c451901790711001950508442c003460070324140c41e41140415040722035030b0394850210060f0781e2030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 429455296 1250 429454046 429454057
    0x40905010b01080a0b030c13020403060606050c1002130326182b03050c07030c03030e1009030305190e06030c070506090721020f1e01090e131115 64
    0x500001c201e409068001500701c6034040d0002103000d003041200701c1140c90002d60030410b00000c2d1800000c8022540f00c0c3d000070700980d04020b25040c2041c1c0009041030307014010f42a04c480c1f84040d80c1e655100154800101d10074000c41e8017080000d28000c2001c258174804003000750394594000c0c5409410310f4428005a485405001c44904000d10401218101010b5000720620510190030050507412180b921082825200074100301d4000f84007003030f606007400048000d40e8841c1300d08460700d80724503000d490740203210610381c001e2040c407548503505481080028200d0741c0548400d1300d030805140c03061843d00c0780b41140e03000b407080c1c0d05046c4995850307200086210726003006900ba2075083d130340343c01070a290300034000c20500e90000009201c1080303d83d603071803480140f10341941104030481c40858140c0802080319a80310a00c00c0c035110081e50702d0103244c9003000003607945032146030b1544040030070104180c8103049948809141e040c005004007551810f00361004044e00c1015003680f100f6156079010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 429456546 1250 429455296 429455303
    0xc0c0607021c080411091902070f06050915040b060f0d1104060f0b0910030b0402070b01030506060a030807060e0a1401060e0c090f0d03030605131b050a08040308060a050409 76
    0x40000b012440e80c00329a114000511450201c40c6420151078084900321440d1419214403829000704040d1b4010000c042910880c044045d52582c49504060100b9080b00400f643c06074140400104c0d040404184000718102c00c0b010080151195180e201c05400e00511030364000e2102003180000c4c0e515003c03041199407080741144107821418090106076112a8040a0100c0a81c0b00a2012600380c07016500081019185800e21041301d01e012405001c00040c40da4010307100092050602c0140700707801e03050301c0c000c40c03c030b03a183d031242d00a10109510034403014080710414400c0b03d0004140350400181c20504034200c900b0301160b0707101d000462103c4020041c0b6607656503001c206488021202c1503000b80302001c41e60400c80d920740130034003441041c3c1d0381512480da5113500108050080e80108047d04014064180a130051000d0400404d5840003000003151769810034030101d4420000c4501c1c00030195100c143c4c43e1600c0c0d4050b1610302e4040c1c0201e51003008020082940d07203403072180b008103a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 429457796 1250 429456546 429456553
    0x1407030c0317130e27060a0c0206150f210619090210320702010212040f180905120a1106010609180603201504030c0603050c0c060702 59
    0x20750310b04212540000d10254071080b00600290003068418a9000b08035030440c071341085603030f4035140d03200c0c5045e507080c400380812940812242e8000c400000d01728803420f80c12004004001d441e41c1c09980d0382c0f500720b940001d0303001d107900348000c00c0c28500703411401000040c2c81d641015400c5510007241c5600140702008940c804410000c00c85600740c12001c40240170402040641c00e0740d00821016a144c0c4949000d0010300c029010150182000391200a041518076101e4080c1060541c0c101c0c0d4000c0da010381c010310031040c0194201300030b202268110380404d1002c841503490312049010350792041b180304100da55100302c8400490800d0254075424246289125601c0d4800200608102c1c00030442883c3c4c0d038040e400500c1025009100780042d5100000240b1821f0180c0e80640e018005035000107101e8031503500c00f24489041d034881480b41000440384240381a04030a0411079038003540c4006440e800701d900080008602070740c8200d8105021032000303881e107407068804a26105041d15900c0c016030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 429459046 1250 429457796 429457799
    0x103060317131202060904110c0f0309010311120411130501060c0c171203090f0a0c030b22030311040509150109060302162009070504061d01080703091407030c 70
    0x1456a1840003410b48480846001c00883c0c0201d805c1d8002c192034140103c1d90742d00c150007254490300c20b07181300030b5040b01150181c0c081c0c424102d45941250307600740c0c0030906052072000041039140a0307850544c0c91581c01d6003a59515258010202c600740b41c9113400ca0025003170002c1022003809807078082c00c240d40300c0d08040d03102c40c50a501c5c0c20f07103030740d0100b0240401003407007218881c40420904981600d40f140c464a90b26a22701c42805c0c02c520841040e15889481304050030003814000300401c50b40100c80c5c0080c10f941d9040101916602e854848184082d6001c0d4030f80064001c1d070113040c0e03e455044145040a40306c41c0440d80f00002601c0c58043d88010340041111580d00c2503000b0054245460158244046003080b441c0f00600f209004001c802da4403082d81c43c4a00c13480314240d80741001000741c1c200c0d051821000e0926400340c060300000030003850b0108060081c5990b004a0300006a480b040e0694541c8030840003092120400c80f194810b144180310980300410580700658051501024800d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 429460296 1250 429459046 429459067
    0xb040e0603070614072d03020105100611032b0207030c200117040807020312030406060e0c03010b220b04050f041803050d090204050406060e060109031106090103060317 74
    0xb402562154081107840340c100e400d040d25840030b642110745c0c048502108a540ca10344004c0356a0405820b084880e66052240300b4550305400c85409006291000710025840c0c2c401180d400046003c07601a0398410001207a4010b0601d01d106c0c0c600b9000c000765417503904005c00800070303070740445019400140448104400e2181c181c12540d540c08060800c1050303503141400180194030b1080e050507510511a0015060002050846468940c0101036903940b840860042005400c2680c041d10424030b02500415551003043c445405800d0800f41141161320700400c0c1025a4400038a0400c000f0b420b00ca15020700008020480190010084507511282000240701900b403886607003920507810800d4840d42004d540012400c5c1035014903000b03540391151103501003e0a1034101c025003103440c0c18200414840c241d0702c51030a032040c0078011078098035482c004480041032400060142503101c00891024602038008019425040c10007143c12030341d0f41c440c2015500d41e4564420300c6c071030020304060395 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 429461546 1250 429460296 429460303
    0x30a0c0510050c0c0115180921081b0301060509120a210e06070c090905160b030415050609061903170904050105220213030803070201060503240609040201090b040e0603 74
    0x40910b20b4a4801501e24002d0052401900d000407d0a075940e41c4c0120000d0001147d1500320b181300014a4021005001d14020607941007129100091a107040c5248221110f00085034120b6085590f00350818003040100f010201c1c4d00d1030803062512402c000d03031002500403800d02d2851100560280311104090074058030800300b01c1c014903c906010444240000e00c210341a00580360902e03000545221585806454481e403048400e0300500c166500040c0100050001c600c0f4070700c20703045411040c0940807110161002a0b40c1994800c00641c0040c6260404180700602c640050080d40b6100d6a41d440d5a000f0511341c203144102d1030760020741202d450405028071801041e05803480c280d040751901500d00c6007130b41c0c2c043c1c0c0500c8a4001504004801c226280e80015540013002183e072403c00e101d002e4002e01403446190701a000f50008074041903080f04042c000540b04801c0b44016549010402420b5280200101d05014042c40042140720034403000e07001901c02007941410f1401e10a040618 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 429462796 1250 429461546 429461561
    0x204181a03011e020c0733030b0108040f05100e0709050105031606050a0504051003090302070b0310060c020d48060804021201020d1a0409020102030a0c0510050c0c01 73
    0x80c3c1c1014012803815110444420350141900001a1903c040003599820100164080c038044240c05087c0140d07010181401c1003044140c02c0101c43c0603480c9001074082c0c481c4000c0281c08a100b44c40018049241c00b00080c44451240c0180d074001c03030704650b441003141c21820042415070711458040c0510a0300780f06140c05000c0403002090040300d40c180685103070615004a00801c1000301d02d0201c458012820365010b00301c000d040f5210345054101c000d00400c520b110031383c01071066a0b800a000e10440048902400d07401c030401390380b01e04088080da0405440c200c120b81099448000501280c4580385406000c40c0e00e444078a152550500b8052911010048100c5803140d1034000c40d66a0700b03038103004403c0341c64604260102e0f907502e0001170030b1812622400140c0f5400002d2504050216920038031091410b20320100718400c00d48140800c48200007002809a0300070042c5058075409070300f14518081c49442207942000300855904159282502c075554550404195204228028000c00e039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 429464046 1250 429462796 429462799
    0x318150c260901110c03031b0c0405060a050607021305010e070809150114030c0a090b100302040b090402130b070303050403140909010512010e01152108120a0204181a 73
    0x14003500300c01d03501000030311a03a036190703043c480c4c000e82400511302c090101e20303501d81c0c1c01001e4984443d048a0a25802982e00410b0035981c000c095040d0782900d403d01c0b450f801000054080b60a007414001848500d9100003070903a4024001d5035417088a0415005450180480101ca400c007420000b501506186018000c20580d41000000e103881e650501e80142c1101c6160b541d0b00c90b24140040864148542503c1041d00300030600c00201d50b04c0c10540016140d80403d55403683c807040545400c60490040e802a2411800304100340020340c5000d4020300a06031203d010300b44000e13a140c5c7c02000d69404400103c0200b85c890b01000245500030403011030f03100950f074140f4608070304000095020403050203007610030710700b039920542e24000951000501940d001c00810604880307a58542017658540301c1e4130305030808090807003840070380340d4008509960700a031960b0900c4078141d000708071100018880b85000c0ea090100041d8080650138158914a410600181c001088250701d0180349100e590035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 429465296 1250 429464046 429464093
    0x102070e0106170604020d0c020106030b130201021b151204030e1c0b0703021306020c130e06010b0304110a060f0e03011a01050f1e0c10180318150c 65
    0x10042c0d41d82110044040310002d6940c0c808966801001400078044c0e8085584c0301c41c0f403d04800810382c0c05500420540c2d009581030348140d0303140c050420790808071400082c0160440404582c5519a06034182502c6500410500307032252060601c0c81550051030b17114400044100c140b205040e00070a0f051044181038502d801480480706003940c0107661510014190b9044100040d0038030304c258142c2d071030400e04280c2e50714029a9001c00030340e210307421441d49102d25031000c031000304e40e81d5601c10901118440005482c1d644c0c82c000311103049820040c01581c2d008120445400710707594003640e0340f010304020389a0300c3c8003c62944000b002d030138046400d940240e140c10010030020300061a0503d0010003464080c2d0380f04140c43c501e0180c0d000e01c00303402c0c02d01c8603561001410b401011019101d481c1d040412142d091250007d40001d40b01101c034445400310031081e005003c24400c1c10080f5681071265882802d00d03a81e800b081d1100d0304100e8103400015540d03041c450030055800c400039400402100380 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 429466546 1250 429465296 429465299
    0x518160801030807030e0a03060203010902040504270212070f1502060a27061107050601060f03090c06050304051f0c0e030705030709022a1e0a0f0803100f140102070e01 74
    0x407200e061113001406420f020503044000c6840d82c503445e80f1005190b01c00c00554403541d403810000c020703400c00d00503184a0390400711828144c5101e40d61500e004401203010714158100c0d50280581803c0f031000c000c2c11405990404500100b112000e0780060512800c40329402040450090a00d040a001001064200b07400040340790000c010341c0310f01c1e221403044250755003031030305c0c000c4020410b0641500c1e0440001c600e206c184000481d0043c121805074860056107003600c86e00310100c441000c0700410300c0d100510709001440c400c00c09036500900c02e10464400c00503400190020b40c0d2586e071865003490b12403140302201644041d20360100300040c0e0003045201e0424000075102c80c03032409001100385c1e01144540144450390408188900200615140c000030301a01545400e03040004505000020210041c0075100040848195400c5000d0807860000340d40c4940d9070350320280042e03585850213007010a6490780802450000c05000c583c07a000da0b103a03040064100504c69005084d51441d0400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 429467796 1250 429466546 429466553
    0x1030b012c010908100603031b05060703020307050702130e0d111b031e0c0a0b0304050303190e01060b030f0a05060108040602391e0d0810051816080103 67
    0x440107440c54030102181c1c4100014401220041010351200b0b03e0741c4660300404400041c1503010f001a02d009136600118841c80f0b9980d8480101000340007002036100340006880e01d0700c240d0255801c001c280c50014070708082e540000d40c400c1901720301014115690300c0319a480710400c00160064100d20b09000504406554140740c4a0b0311304070104450f000c100440780c035580e5042c0662807003100340f402c0e020075002d003001312599140d040d5030282c0e00850f10181c020841c2c81007102a00c1c8a554003000540c51b42d5289031407007201911203510720381c3c0d5603180c10301e80307005440a0103084003070402949800e4884c50301c0786010040307007006031400d00e86a14103807d100c81641c1c028542c0d503100e60070042c090780e01da40c8800810344681c0282c1070010385594004107a0458159080c5010545480c0c2c408c03512140f0300307000f408500b60144e9005100b1a0700410005800d02d0194030841c2c1c0c401d001c1100380c210701341d132800403485500701616001518007151042010881e40d014100c50600214545088250305555 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 429469046 1250 429467796 429467837
    0x4180203100e2d100608041106130e09011b0f0908030a020f0105101401050f1306211e0b0a03020a080c030709090c052206090e0c030102030c0f0306031014010501030b01 74
    0x11344420854030350b0004003448858244643c105101902e0275035100c214120444402404d03010384010000701d80003181d80d202c41401a00f140059001390a10032961741d0600340d030784458820840081c0905020002a08001030000d0310040c50791341c02824244040f48a0542121760091200c03240319207145040c800c42c4c0038030080340b541c080b0a013030071980d40c007003040400550b0248803440c06444402180101c2e1280c2e109082d90045141c4000c00303401081c40000b0401504d652225041940300c503280301c0c040c0b1000e41d41061303d02900207044004c21540b00d4012400c12201d1360010f500a500c503982d506101e050800c40c10000b804211010441000140d882c1c100c803076480d120700751140801c0b80048140042d05568048800c2c4a10300c200881561010500301502d03048203030103210300a0180d03100c02c0e81418003c0703a100c0c00220724020700c0c03c00900c02141d071941014082c16018030a80d4900c90315075200b0300c2141500b421016400c0425854a000101500d9403480003d0421002c1000151a0050f18 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 429470296 1250 429469046 429469049
    0x3030302031b0c330103030e010f020105090606010f030b04060f0f1208030a0b0f030f0601060908070605090d11130b0310020403020609010c02120a030512060604180203100e2d10 78
    0x18003500c5a421490420380784c400c0403440c03a0328100100340000010190440c40c170b48514002078035400205514040181c5c2220320484031000d660304540c1c00201198810348182d00922041c2c00e0000303a2443c220082400c0303c8a913004400c0f1204040000e121041b00b41244000500059010114084481d138415005000180903183c1d0103894110710101580d0b100c0340c003003000c20040c0460b00c40954241c0b416564210030300c102d901142c0c501e0804503d18001090817030550300781d62601c038509500002030200480394920f042e18219204e0020386041e540e9104003000c010000e00021136010344840c10541403070030100d09400340e10720400040005845d40b03400d540040809092800b0218880e001080c901d0300c4102c82c640039801926118010550003001606c0100b02c803248178140c40d580c2d0000d2203118400c90054641c1c0e454546091a008002030300195030205061000c1180580d85018469142c40301313440c40481580f41c0e44a200c0703216100072030a8000c0c0c0300440a180c990234400690006207466 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 429471546 1250 429470296 429470323
    0x102030403031407020904030503060103150f1725030c060f0813050f01020c0322081c02102d0b09060f04060803070b10080307050312130c03030302031b0c 68
    0x101c1c210003d56000c0f94295848103801030064803480c40e280c81c0c0104130360310446da403502007480d01d50034460b5004010a510182c8101d401c0e552002c40c14200341c40340a0000041011071841018100e45040703c191002c8084d0740003429442c0003c9042d481c103c0320110164002c0380401004041d000d14250f0301c1981c6603084820010030320f410038642e0034020705200072804400740d250300001c1d44500203680040245a412442c80c1070880314032004650b1021280c10380300340ca08580c0a003203441d513185111003540c403503120f141c01107490280500f030b03640098411405140300100519450300c031111010b548070307040c82c0540725400c0007120310705000181101c001500017030040d56000c1031143c2d00d8481d42e01000143c103503d822071b52602007900d400c0390224401c603010540a903680c5c900090b54040002580c000a030700c0705c042d500f4402e003507509103e0080010300f400b44c2200c6452100e4013098800710500d0255009640c051b85e40c0c5051250404c5909602c5007900d0881d004010318041000c020850190740e008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 429472796 1250 429471546 429471557
    0x30a02120a0e0a031b140a0902131a0318062517010b03010503010e061605090d0b0709030b060f0a0320061201211a0402120f061f0302010203040303 65
    0x402007044491003070041c640c80c0c201d5203410b404028080f03210240041d1071340e03c01540340c419494154818809406501540d0031684415040c0f1500110381c0103000030340d01020744031140580e80c082e03400100c2501c040f000800c410000030f00c0420810590f00320342c0300034164010f0819088c0305503001030003803090300c0740e803200b000010b043c0161521840a0314a68180c810b449001540c640d0903000d0790794420304c161807096180c43c0342040c07403a03400304540d031140001c0407044800c9014003205407102d50111703409035400181c82040c1703000142d68038061800b0351226625554a01d007146441110f411015054074030448080707002c0e2405598802a000075240d00800e1188201e0381100414400c07440c540680b54010382c0030403102d1100908065103412a400c0031100b19580e0300c0902011020014654050244caa2035106814a80b07909403149801c035102900b40e04146083c52401428280d288051f412070350050f6050101e40310040c0309404031210140d00c84144c16145034000b070740d01d200d9803200078213008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 429474046 1250 429472796 429472807
    0x311070321020408011e0c020a0201052514062a1c02040905010312030b010314010b0702150c0109051b2b0807030306060f08061c0f050f1e030a0212 65
    0x1407054050754000c01c4254024484c001d0f000451401041d4107010024500d8580f00b00b02d942c0c6407001690724034258041c5c490303030314100c451449144010318510342000984110799003100011a60110b50300689282005400d25081c080e4181e01c00c94030710ba2048003a5581c00c855210301c14209011070f03102300841c20009480c0300744049204c01a000d50b40c0300b031443c00d10f4200000140325020350b5040344064190740402410814000542c00c45091903030082001869100501140f03032a8001421001c0c001000564004122249016940d200002d110f105945501006003000340802c1064052502c410003d440e0780d800001146000400e016001c00415107551007812244d8160b0002c1402c03504042119aa0692800d0107000b80c6800d00c60480000c425243c40742d2000c2c46510030398054640240b0b036084600c0e00000100c0c19051039001a42e24100310b0701908000390701004400c0b42440010058028601e0360002c800d11004040c41c200203035001044402410342e80031032000140340e07080341c6454482 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 429475296 1250 429474046 429474107
    0x20f030610120218040b1605121914070905040c050c0a060203100807060f0912030207091a04020d090b010509040c1a0403060504030e1e0a051315060503060103110703 73
    0xd024071380812207908554030500c0240900e1005075449509001a8030b91040300c525805c4940c0e12a4a1304051440241404104061009244210040f11041c40410008140c2a14045c0ea10040d9421804509105010061414280286072000e43c060038420308001c0ca8100f880c0d03c500080800a100c039600100050200ba2040c4007a0064040c000c103c0d80255101d00d8081d000000c040b00d903001003001718100003140c110706038420080c607030b256029188061912a2000191101b10f801260020900940405a03104c1d84040e0075a500069004101103c00d070805c10010ac02c10b800842c05000d0000c1000082040d017101d0700c048528244880003000c4004034400c1c080c4c081ca810040000741440c05200034941d0021115003490350071240d104035030a021500382001007041c2d807070980180c1150005c0140c0e01e0b05440080881e100c8034408211000c0c80c645a42d000c1e003140d000180440d00100030b105455a05206d010740c044214541145002041d8034082c01c1c50380d040822004084109001e545e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 429476546 1250 429475296 429475309
    0x6050d0b06030f0304150201050a1107060515060c0a0b090607050304140312042f0a030b1008031603020105071b080304050c031014090d0509060a050403020a0f03020f0306101202 78
    0x6030043c0a0640380c4664544080da8a000301c1d400d14000150f0070107000c201c40611074800c6030014640036040500e400d0030340d503c0d04090035004042148626420701e01840300d403508001047c210640c00c0203801044914504114262405040000240d00120400121030340050840b504181c00c149452010248810550715520640340030410042500042c03104000480b00140b5800306100407603141c9440f01400014410700f0b0141007070303200406000810225041550141e0800c2c600c1050042d25610381c0b0800385980d1000d20032000c3d9031031046002d0185035080c49440e13080a69490940e10a9502201d41da07100300401c08080d21604c070000200d02004070400c02c0801280e005406e6400d15101d42c035000004240001d408a04a000d0f400059204036012542244042c0300341c035040e007007507080f02c10b120b16500004e0100c02030110820001c40940e0760f00f10000001d10454040312445420340c03040c030516255003180c01303000707602645c144418669196518025510a41040584040c044c000500c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 429477796 1250 429476546 429476563
    0x180501020309061e2b090b06041a150307021903050405060f070b011e080a05030a0309080f030916090c090911090a080d0e0105030103030215180f010606021006050d0b0603 75
    0x41c1d59134001242040c0b420161680700c804468244d031608412000303101281600e0011900504043c03100740021140e141960000b0442c2c42020140380111000601180000a00d008503c501ea00701000308400168100001f02c180210081a0105c80e00d096501411600650049c03030b104404c041203120040d0b02d81400c0d2140b407504190019420f50f0342c0c000100c10040035110a03000060003110100301d0f00c0c0001150210715501c0401146020541d03201100203040032141200c003804104807440e9081a0000038502440fa800c000e40b92a070410a204a14080d00307500a0b0040c900380b104c1805402e4100590504680b08054041000c0e004840408660310030440300170b61050031104c001ca41e402c3d00240b40d801e0300f82c55444441460f4004001503481d400240310080c0140e20a89507409130401c484e0469801090402401b00b079500480310641c20940c01d6100d03417159039034401040140701d40c1080700e006404100740042089505280100c2c02c07040c0c819602070a506000d03008982c53303850800030b400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 429479046 1250 429477796 429477847
    0xe0105131811150f0301050609030703050a0624051e061908040b06060c030304062c0a0507090c020304170304080a050a0b0a0203060604050f0103090204060f0618050102030906 77
    0x4112207080c5400080441e0000307280b8001c202c10f9190340d440e0529103040320640300c094600c02d4110382c40c010070000582c0c010030a540d09409000c00000008078200400d044032482039a001c035501c440429014081c40c111201c2c81c00e100c80703501b01082107071150b0705860508080446444031100c044000300b0032601c43c0541d00354040441190211a150340403c0203800f852052440d0740040e00d0b00c1c1c080185a004d14682d03c00560001c0010500240703283e400b64850507021000051084c1e0040143c1c0d01d40e0340111003150340c82e0020f410b1350080003c01d00c01c141c00351809104c200f01103451404025038901072802400c52000c58080340020811042040d00d00610b18182120420565807805a80b1713034001100455840c941000880c2c1c8140340c0d4002d0302d12408000c2d020318202807030101081b940380e442c0b412260606588104500141c2c0700d030b00070400a08141d2580ba454a4038015000305420800c901204000700704130401d00c420b0b0307404070455125204c111201a20341d000300a00b40150400c111114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 429480296 1250 429479046 429479081
    0x206150d1106030702030a0e040615051c1a0f011815140a030b1e01020307031d090103061b051806031f0801060611031201030308190218190e010513 65
    0x104d41182d002008022001c10b5944e880e041100c06414401910307442c3c010003a20758551407405070003600c15000380c8481c01ea40140b5502c5451246180c2c41100c1000c2813200307082a003800c810915080c01d4515036143c0d0320070b1030f080c4a60034040001818020365800f80c4400c085042d6001065984100b020000943c0407084e000c0e070360050540040c00a200c69581c0c40c0c02494200c0c403200005c011080d5100e0b1602c41038001d14680205680e08030b400c41000c010455102e003101c00c0042d640d48500d84c030a8043d62107201c00064528000c0c0c080240b22420341d00c1e0000708142044800d4030031594003a0401321a9099848644a449044154100d400b0342c0c501b10f901070507185000100c80805402c01c2088400c2e0382c440c4000c114160907125201e110b50500320702e01002090040000038400c5280f070345c0c071030111102103c0100000c00210246d0303101401c1004080b14841a003503680c54610592401002c0500c1c1c444085c6207842d0060250240500c00c003807250703544070741e42d03540c402c440e811000020340b290011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 429481546 1250 429480296 429480301
    0x30309030111030901050108030f040b09010903050319141305210607020a120309260c03121b0c100c0512130c080106080a02040905070305011d06070206150d110603 72
    0x920036160011a082074245d800c1000019800d4804006c48001051541040c1c0c60a41001c0e078140103039000d003114038100300c00401b000000c20000d10150003004000c03041c1e071256410440008100549501201141c22170402400b6094007583c40d240302152000d03030b0984c0202c103118001c490003200b654840d001e076000d4a010008000d81c0800d2072981c2c14421440107046220355401203046881c060802442d041c003921000001d03c00000c072a0349502820b006882c540603801319000d041d41c00c5136402c141c040d080b84c020300c49090420008144074600248010f418154006e08483c1e844105c000c02c2e1025942d1042c440c00b1030b40c17040d412a500111250384000d1141800481c42c840d8403c40c041c265081c01000d000414040c03010b00130b0500312251000200b0700f24070b464080100034002d0031000c9403180704489001000035000e00500850320681e560500c5c01c03425134034800b41010001081c1c0811500a4000c03c128980d4441984489000c15500c20011010a103007a14074008030640c91980134001104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 429482796 1250 429481546 429481571
    0x4050105071d04090516080d090803090922120f0801050402070308070c2a03031b03090512011407030b2403281406011808060408030405070b0c01020405100c030e09060303090301 78
    0x400c08c04500300340d5140d20189a4a0300311540724000d00d807065621941080202d942080030b1100005502c02080f0301900c1780580e40d0710f400001601b04403100c007103444208005101c80d04041240d00601c4203481c25454006160340c028171050740200740d041400b04414031700c0c1c18002d1362290401140d0460085080720811101e85041c0710310035100440003d0304001c00814030045070300c0016540c0d507040e01d0340d89001d805d11040ac00094940b0921481075940c0c0c929128080c0014003105011381c03902d071400a80b400c1000300b07200601607810040400e5201c3c0300007040000c00c1030b40440c0d07804810980384483c00d102e1641c060b4009200c01940d022118201806103181e0980405110300503e02620b038400c03401440125034490712494850a4400e410020009000c100744d50700035540305208400b40c43e041c0e91241080b003000c4d04001400082a035000ca418041424101220074950049041004140316269801071040a90301801c1d4020603605010441c0c070780741002565140500100284846c420680 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 429484046 1250 429482796 429482803
    0x80d02060a052202100302160620041a1605030c101b021b2b020411090616020319150c0c0320121204050105071d0409051608 55
    0x4664080d00e914000220b08110f01180450f0984141d2200e40b10720b038100d580070401015040c0207128181034081205030020140c0c5400c146400744100c5001550360113420705246151001c440c80c0e400d05100700070a01180001d201000d8001c04102d401e036a591003020502d02802482c00b400401c2840b0101c0c206c0d064070b001046908564021b00d0003009078100c000101178a01c80103080740005608070301c4004006001d0b120800e011000e019000c003a01000000502040d0301d00000e040618070301512090046140c240104170500c1e582c03a07101401c213a0004005010b8dc4108015860030200120703000c1c0c215101480b95102468030561240402c4455041170400555080d15121107a031802c20310059050242d44c810030207540503039581c402004418a2404801130202c4080068410340e1000562181460000c10045501c01301c81c40080c100313460201d09640c4068288400e02c0610081c5501c50390700b40d07902e100000e004403030104100c1000d050480c20160f2804801910b0000f01c0d902040c00310000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 429485296 1250 429484046 429484051
    0x2040c03141605040b0f07050d0f0305130c060804140118020a0b040e040b040c03020d03120b092a0d0203090c01020d21020a1b050705040c050310031704080d0206 71
    0x1405050001d55030204003189110701540c40001040c4148024410084003c0c050a02c0846c02c2c04100d143c10b03050380b40d20f0701d0101d1000701c540010300d074140714102c03c2d0f03814014950400416441408003034050b640d0405482c0040c0180d03010000900d00180501000d10442074038480b0200003040060124405100825140e9406034018824540000349a0f4041001c0314215a000d400b162107036103884d0b0b24500b02e04405001174400c070905070750200150b0707905805069094030a07100e000880c01a42d0584007a14002682c0900c03031404a0100709102e0b2503c9a404100c8040f1211403015143c11104e0704098003c040e16282031903c08410055002400550740c409108241c0880795401504801184c040a20b03104c00312241e41e102485c016040d2a54015015612003800c00d1601c4410042410354582d2210034150f035039610604041000b41428030a4406400452511520314030b40041d040198641500c0014010045912000a40d10090742610058036005050b94003d41d00c0c01c000950b1160207 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 429486546 1250 429485296 429485321
    0x1902010314010311010e0108040c0603020703050c0304080303070e0d21020717030301060207080d050702040903090905040b180c061804060f0807030c0909050d0e03210705060a110412030c02040c03 86
    0x1e40d00024087d41c001d480c2284100d070300c484901c104504100044010350000c40c012000c0c01001d10018050090500182001d4884038004548030715000e0b4000781054801c000e0203001e981d00008031030114903a100c80f0b0b181c104155038030980c40100034100f240303000ea903030340304d10b154042d00e5544c134094003400300046048440d15030844145c19250106c06868460202c0340d100852800c1100c5001400d10740c010000c01ea01030b042c6a00000c0d61001e0340020b6172002c84044406400d042c0800185102c001c0c000500b1f88440340041041c00300d242c000c501c1c0c0744100c410090419843c6205480166610741110020b1300200b2130a8515981e0b8003003043c5d4a14803800219543e400a642c0480c10900030b00c40d044c02070ba003020003041c141c00712041c1581d020261400c80c613014016038040c09070000d4a0011040e0000b62002056546d45203420298240040945200d1100b41001e5046940f80030780410340d003e5520003002c0605000c020310b026520080c0000000390014102448248069050751101504000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 429487796 1250 429486546 429486557
    0x120213090e06010819020103200703020f120a1211070b16170109020a120c09050a0b1303080f070b0f04050609210d0902040f060f0b0309190201031401031101 69
    0x14007a046403500310901402900e0b50150f550380392000008080010954018140007440300c03400308040c400090502c445aa01c04000900503003055170400040280b00c0d00e640282842c1c0c1c60415900300b1034455001e49004100a0a0700000b40e08040d901c03955000001a45950303171410329150201511000f140c1140d511007a05402442050050301c00c06088206c41840c0c07441c84c0c0c02c0a02030320081d04070300e49140412403c90700b03c110402c1203210303c524003502502c2d0301c3c40d614644000c103c0300c0d2035075411a0780c1d5004180b0030303c0140003010380c004080d00c0d448842c603922084ea031403040c41740707001e107001c094402c142d1501403180f00c071901d20120380214061810f0b10520342d1100c02807a07482c480700e034184030164031074420105510800005490000d05942e004603a82d403003500002c065840c84000c074a4015528407081088130307054081d641c018041540b6290440c5000c5043da5140d580c1c2c200111841042c4204e144116807182d80018582c0403548424400340d43c403814420714140c0c5c8508414007042 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 429489046 1250 429487796 429487811
    0x11070309050a0f05010801060804051e03030115030b0603040210050c070906090f05091e010b150a0807020d0c0f02181006020d2f0f03030108030322080702040b0112021309 75
    0x44404600f0b8058030300607190140c5c1a4a818811100c20100500560b0345003d241800300868071181030301c4400c107100c4001540c42e541040ca02000e1400348049180515142400c0821aa250003040c6c95209404858083ca00404490191014410400c281074980683e24000c1512440c0c0d0b070041c42a64240402000542550007040e01200d900392205040d562028906c120600d03404c80104403140154800490b1020901d0081943d10b00b140f0075005a070348001c50309005040d80072039180c0c3c1c0400c4520080050b0302102c08054a00b03c1c100c01d01801d140b04045441c010b64a074100320a880c2e00980010101a140824441080d180c060269100500882c2403100809100e0b1304880c149800842141c4a10340c44e080003084c4a0b4800303d045882401407a03c001c10f1600107002440c002c1c450800070390f950740713400c0e0145d40462010752082d0010103243c0180c06c01246c0d10740c1c15070359031960559001545c4245007005903441107488041103446800000d01c0102c0321060a20a411110440030500044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 429490296 1250 429489046 429489059
    0x3120109050919082215023316170a020703180501170a09170d050709180513061a040515060708220303030504030e030f06011811070309050a 62
    0x142201c2c0300c05400c118040c445c15000c1c02124840140e400301000340207030103556070078514070000c41c0400c045001d46c121070342c655840860342c10b0300b180504121012070440221104503540c501000b4003801401101c84221500c0180660003007000c2c030f6041004032400c0d00d00444c00402030b41c02480708400051890741140014001c000411040e078105844412042c2e102c9410050030f0040107100000254490182e01c0104040072200203480130b200141c242d40b55192980c0d182542d4014102000300400d12030200540c0000c40251035003990144004641601c40c440c01d000900e1031180c024080a242417400081040c501150580c075520681c0c1c00e00c115541c00c680c1800040030401d031709401280401c468800180d840c8003c10b400d1014408810711001009200a280c0985030005c4011a94401c240301c02e16070451074441c6081401c40040c030a44644417140340c0c59900600c64003640c140c601110701c007405030b40d402c10000400000d8100e0b03110041810b0052003910306102e1240248500316011546 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 429491546 1250 429490296 429490333
    0x17030403170d2f0a230702240a03090f1520040b070f02150f03150906030a060b0a3515040f020a080616031d0618031201090509 56
    0xe6007040080c0f034120030203101401c4281e41c441401c04007005901140c40200302c07040d002c01c859800382c410304942c0310800c0e403052020240c982407084045003038140d04001e0030b03111001180c0404000b884c0100709805149803942c180304203a400109040000c0074010b05200c640c3d40014505940c8407010700060095040d246814840d5001d004184e000030400580842e0b80b194079100764910141105c0c840070403020b84455107030001c40d0f00da1240c050002c18000c0d0006076440480d5008802c40e01203050f400c3c10800071ba0741c0c800f03120740240180d44400d00c0780c04a6071442000e03070041801481040d0200b02c08400b02c0d65845045041c4080401044100910450001440791142401c00000100e030b07111503e8021200b001d1083c1242d01c0002100301003101d240030300496000c0e001c403030303850041a0013011016064440c0f0302c0c0785400e000024141e00410300710003d0001e0700082945840c0403c802c164030060f0a500c1100e084401803581c41c000041d204c00a90312183c400c1d000c2e42c040d60000d00340358000450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 429492796 1250 429491546 429491591
    0x1080610170903040f0605181c11010509040c0302030a1406010507110d02150306040609150302010e1302031311031218040617010b0f030303010602060117030403170d 73
    0x280c48212540e0078441121642a080212501128103040d51085411142c1040b034100c0d0002980c040344600506c09514542048200c0c1106d482e5042c0604400c00e181050921001a010f90060504107807503900607003c480c0c0015024100780720140700800040c000e5403050f5011510380340391a1408045003a40c80301c042c01144140d42c0e503480c008050303d0304107101034604160356201156022000c0180d540e6003071610720b0484107690035141d00d0904c003003200b150b655900c107055280c10320001643d100b8030709003801d050340d50908180805a032010b010420700c48100e9800032100e8800824001411203240ca2051a80d103e81200640800640705042c0c5502031900c0070043c0e440c050200c1e80c030642d2494400c908160003d000007c4241e40c4070070408158255401105007030355a05070a41d00e80c1404030b440c45140b43c042d0015840c55151440003543c54005100f03078865050000030f4081c610f003080c0105c8004640040b14401c040c0540a0301e1021a0300a05c0240200c520b81f112258849540860005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 429494046 1250 429492796 429492829
    0x702060a080403090e0720070b0d0e010f0f090215070201120504030e0904080306030f150c030709080f0102120a090f03141201080c040b0a0b0301050114070609050a02010806 76
    0x24240042420281c0d2501c0c4050422814031801c040081810010040d0700391080d1096030b01c2c190380207250406403860b403400303c0146900744c120304c2d0300348000e007055800c0f03c944200201c000544100c43d098000d0040400d40090581141411030502c13a200c1c5039000155503600844e4410304041034030f20300c80b98521903400024040781082c5c544600e01c030600c0d4490713035016009003401c24900001d040000c103a5a401c980450325910044103101160508005801400c40b106000700280390020198504c988401864407921a01c00030003d040d0b6485585118010710f548003c44080c0019901d146000c2d400c00c6811000034500900081e01603051805000203080e00040317503d90064407500c0448100703207003240c55000c402040042e9490550410202c9001700116809040000e186c2420072058810f01000588105a510300900015128070f007101d04680342400c11421000a5000000d01401510406080c1034500780100c400d0103004900501e0641c400d0f600c0c0040d5540c0c810410a0022420ba10907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 429495296 1250 429494046 429494059
    0xd0608070824160e1207140a0602120a0309050f0601031505040f060c0e10020609070807150305070207030204020706091502040f142404061e050f0d0e030d200702 71
    0x55020000203c41907400e0010345071007001690400042484ca40000c1914049980814000c0004a0b030002101e5032480013100c512401c0d0f4a0310304002c2da0351b0f044403210f18110030001901c001a6002c1c2e80302c0059a50b120040d10800b020400c040780e02c2d10000d1005031500346030155149000e41ea9403003118402c6511004043d560825626658000c0c0041c2031013106000380b803514030000c1d58503107411843c4042d40e6030081c2090315001c0641030034450301740d0000209501159040c0140c85100141d01910041403030002001d0707450103422031030055035610181d001740c40001d14009000d036642003003004a0083c100000d0603120844854224402d52294003124040c80b02c0c03c0c40f03100c005800c0140c450070010080c2d9500064a0344c0840810b030742005401c1188000034082061580001784018021040b014104014403000c01c09031440c804d29042804140307001804070003542c070a0384a080c070807007400100c903150604292410014002000b2038107001c1101d400001ca8100000704603840e90b036014210 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 429496402 1106 429495296 429495301
    0xb0c100b031c08070c061401080d180506090103090c0b0301030b07030e0a020603090109061e15031a060a0e070201050a0c020c030a080f0d0608070824 66
    0x42074001e401901458840c1007810005820494450404169503510309a04461948842100904003403414441c41d09100c00c0841541c183c9400800301c8400011010307003611814161103140100700030045061165080000140054503010304010544c03044c00da42d01800c0c0c1c61581c01418201030040010003e00c20807002850700130050f8103042000e1017290050b50b44501003501c01130302030744000002c00c100c03034000d601c901c0d111500441e080081c6c000007034041e03849a40c4842c00e14043e50800c0210081110301d00845001c072648180c0b181c40c20440043c801c1c00011006016a03400b11000200003203c80304541d92a02c41d060582c0001031921b400d003001c0c0708403000000042c046600c0110030100c00d840c001040340425030001e416540f0349a41d030050b290144507424034950301504280c0001004000000d4220a40c0d690b0429201c000302000c01030390b06200c50101c0f0649003500e82c0301 = true := by decide +kernel

theorem cover : BRFrame.Cov 429316546 429496402 := by
  have h0 := BRFrame.cov_init 429316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 429316546 ≤ n) (h2 : n < 429496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
