-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5349
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:34:44.596183+00:00
-- url     : https://prove2.me/submissions/b13b58c4-d610-42e1-8750-fb3e696fe681

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 961870503 ≤ n < 962050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 961871753 1250 961870503 961870519
    0x120308010527040f140a061b0806130e0703111302040b0919050a0803030f0c160f020118080f0705010f270314160b070c0e180607210506 60
    0x140d2490320b08403004005496050201c3c140b2004561007112840d01800014007030100c0c91940c0c203203c07044d1640a00c0180c040c01040180185840e40080803d80080080301d40c406426090400e6801074481518070fa461405100400402c0104131040d03200703071400554010508002d0031103080c04900403171054070356521003004484083d1825034601c00c115004540031810140c1c13510701140d41c4506a030008001d0394400401c1c808d440f00c28580490307010a11b00358051030000c030302412841d01148804018103440a403981d8008580c000e06880d08100c5030158600912a6244400c555542c403503440420907004105021500d03500c51840082d001d100b6071100c240262011200d2090f144401d00c0c1e02c0ca507441811030210000702c101400314000c040c000d004010840c10340041d1500c02e4003990000740940340c10042040051560010740d070490b21318100c0001c0c03aa0750202060300d00c42191034900c0e01d901400c4100041a60003070390110a003000d80405505084080e46d440089680a441c00c4d0b0340702038a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 961873003 1250 961871753 961871809
    0x606092206080f0a150212041b150e0102010f060f03080304150507120c020a0c0b160501020708131d040b0606130308190e030601030b060118290304030e0f01021203011203080105 78
    0x270044030001034030707803807489281c8003542d602403001ea6442c1c407a4000700140d5600b07207241040d84c2c2400382000c0400d01d1041004080d14108040308400f14601c0700070804070b80440060203001880003814801d0000e000c040c001c602e4002001455100101d03d528a61440d007854510b000d480054264105540304601c045140d0809038412410f420100c20070450725140d40303446001400c28000751421038411100213842d840014100a4140d601d9003004180b406030b40c180500010004410b690050340062488180d5102c6102207102485062819901c405510350000700704204203004146940400c00344801c42d9000e5801141c0c00741154880592603804000180003040d0700c0f00d642900520141801140d2641040b58002015002c1d03100c8007400b04049400010700510400594180028214080c074600d01030358082c141c0c0c801c00b0b00450280c41a05a00072003a4020020000c410081c645415201c0d0313504d518001420341c9504048000859490000400e410310610741c0700d030160810400c0b0b0304000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 961874253 1250 961873003 961873013
    0x10807020c0a0324060b0c0f0f0d0f031d060a1b0c140705090408040906062d0504080307050f1605010206010e040809040504050a0302060606092206080f0a15021204 72
    0x13644c0081d020914007410940300d008003072403150400400e03891078001d441c0d01c9115041030a003460f450b9071040e1074025950386001c40b85d0100340f45041199a0038050a9031441c810300b20018001e800301d40c0c01c4100390341c0f040c00740000c000a074a40304000c0a20240008903c0000030307402c89541010f180085082c0c502c40000003124003441c401180a440308440d142955000080c0c104001610181c7d08aa0000b905101410702c5010b80c130080c214505040d05141001e8050040c05480c000c40c09605c2c043c10bd126151840c410400c0354020701c400000c8070b4070344000b07061041d1254400815004103110b00302c910001150105010412a00160068016a80307807480030500010002c2089400030b00030040301c0342d603035214815540903900900080007401d00501d40a890900c010705414030070602403009008554032302072600c1c004072078a03014001c40801380026501a00e0b880c2c01c5060303a400344440351480c10300005040d45e00c2600a5501c0c2100c00c40e0300721410101e10a0100340300e5110002400070707010078 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 961875503 1250 961874253 961874273
    0x606051b012732010e0c15030a090b0a150e010323070f0e01030b07030905030d0f0b1f0f0801030305091203130b0a091403030304061515020309010807020c0a03 70
    0xb80110f5403120701a0728000c41c03001e0036802c550340d0301c58000d070003400302c01403c424420340911108800c001c12040b25800700142c00004c110142400140d000030014031a070f4811f410141c1242d6000300815190308140d00301001801050050710303400c07920113000240580600400c14100c0340c003c4000c600802d440341442c1c020080c0032000d041d0707920941d0400107003c1c00319a054001005030030100340306541940790a15403508050000c034105814031381d2900202d0008002c0b248200b4405d20300240c003404d20503543c0301038010070030303001d41c015030a591050100c06c071030a40403440c404980d500780c02c40420050603140591f0a02004c5d000403028048800f09007484c101c0c2d54010400d82003124207000624074043d031280e070960401d00e001d090100311080e000ba04203a420018106064141c4030362500400030950781d001c001c0001d021540c1700d015454880a48100303042c094005003255096130528a01e000e962035001c200510f0016403814005441c40f4030100d410203a4100082007202075526580703072401e6131 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 961876753 1250 961875503 961875581
    0x14010c03090b040303021e0a170315180a182a1e090b0d0213111e0406021501060f1110060906032d0605040c05040606051b01 55
    0x4071550040100312a1201c1000d80000c0d0303c241d00070003c0c02090544282c1034014200158026402181a480050001c1c0d00702016103490000d01500c96644e11400031001160b03042881d04a100030000191605a90311002d00c00d00e0543c07018441031a040e546000340c5001d600c4054099503507150f402e00100b100201044420840308a41a842c60719071146a154205c1110305c80091200303071404011805050040200196086a24004804080d00811880d01c82c04002180300703591119410043c1170f48805481d540f4400e001529540c001090030300c0d00c940d010b40980c0003d0f110300001d005c10302c0c00c00ca9400d03040e00c031282d48480c22035111400c25191280b090402d00410f000d81c10004800c1c00c0184100384c02040c441d8008604680b0314240700741c403c0030000c000350645c26440d0100b01c5004041c0c0a03c01300c07139804880064565076074200004503003400e4000030362040c1404000540d441e484405801c40920085440007403a01400d4164201e0f100c081440c1c540c0d645194858042e161a070340181c000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 961878003 1250 961876753 961876757
    0xd0228020f04020a050d0606081627080a1104150303050d09021215090d0f0f02010608070e010e0f04020321040807081c020601050109050609010e0918010b0a14010c03 73
    0x801c0310030380700040aa8008110400c00580041400081440c02d4021342006108504041c812424000d24038040305010086400c00c0c4038240354050207214216508880b0300ba0300480c07020f440e0f40c564106503103d2102010a0b43c221070019106038031817905201c0c01303c00d62600c0035a03400c03840c80d60780d0031786080d0405910204d07120307a41c0b030f042ca0160300c560940c4042d006501c3e000e000205003030061100d610030701408964042c0c3c81a0f128000561b04891a000c00b42c015041c1200d224481c010200e014021039000306c000b5000d5040001801d51065958a050f50240c003016841c5545254194200c04022200a91325911203014030202519084110700314085a440c1c03e03203469110050a840c2480710740c444000c40c0d000c8074030344020310180503805003040a40d10180c42e19501d0030b800201003000b28003c840c454640041c107503038142c1c01203128010b009c902406620091400c039013074141e000d100f10100001c5509100f0302c20740301e261061058007034035520b0408000c0360200a004503003081c41050b0843c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 961879253 1250 961878003 961878019
    0x6020d050c0306040f050c1213060603052d120f070804080703030212040f051507051902010908010c0c060f0608070902030712140601140409110c0d022802 68
    0x4551402028800c034141411280d583c100782c0288000c0b2031440c828811180e00d003005100c103942001301142c01030f822400e40d0751480d072601c801403e0445001500144044d01d050b00c000200704021852464103120385102081c00e00d0180c44035140702d82e0100c422146a08090442e45010401300301610301007001d00c448504180e02a51461002e60140d00304440545c44980d0410805504001000d91041c0f21409503041616082c40703401c03080a18040e19205e98014213412144c4140c1d4001d40f0450f5400400f02c81c9070b002c235092144100c2450640036030000d0b00c180030200b1820014003802144008699800c5d001c00c40355201c0d0401803a40c0e9012180040d2510400680a1800c00c54803010b071081d1a00180d581c1040340f0054511010440100829420450303a0301d10306034201c0c0303501c1d4441d03402c1c244480100e06540f0104a14440e68104e403544503e48020106100240005045113003038070000c0328004420b001d000e90740d403900c2a5011540c0310015103c040c102c1120380566104134405400e281d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 961880503 1250 961879253 961879267
    0xb09010b040c02010203060a0b0405130b0607020406030f03090803040605040b070206091206070318121805100513140d02060a030e0303071e030501030b06191706010e010605040f120602 81
    0x10190b405070040b40005070b40100901c00f49140200c2841d0080c082c207a01d40e8581031820300803860201c02148203448155030b912080360541c031000d003265011035009000700429901e0f03141c9503110149091041d800501c01a03804100c00d1000402c580648019480d21070070700d441c00b0101d40c0c15030300401d0100d801038014064141680c55825003400500c1d601c03000303000c5600e07040c01300900300c44852a850207040750003080c40d808a1403138203c100c03400e40c2c0e91620318039040c820800c070b040039643c5502064000c03e48021414003250f00c000039200c0f2201c1030207100011660340c103201f024101c4100505601200c5603440000600d030000050031120b9071410080780e82e005005045055070800c89041c808a200c00055020880f0f407281010716030301d11070608010039411070311103200c0098001e128074000d1104081081d074040541d0619002004c10581d4101238401d0800190707140c070000e01c920304074483c102001242d81c50140003944c080c0c60039110090319052402580d2100c000030140280d400303d03420400300e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 961881753 1250 961880503 961880509
    0x112030e04050709240c020f011b030e031509060c070203070f06120c021f050a060305030c3f0a0e04020d1521061d060403090302030106060f020a0b09010b 68
    0x500c20f50568035116502444c044420301141038442145400c05800c070b0003603000d42d80103401200ca864054820580d8100d185005840200c801c0309900500407444510f2001c040d80f040030001800b00c10b60a6410041516000d009070300360580b031440442e0459800160059000000781006600090407a54510303034541c0f0b00500c420490b04100c0000b5003004005514080310b000f000d1500c4014801005008622300da00d250031011805501502d80c1c560011800c990000d80001d406107070040d06503952142c004500c80d55544c104490985012010010700e050281d03005030003000300640d034040380010307500d89034034003d00d60100303c40c0000d01143d2a000d080c0ca44941c0301422281c81141c01c0090a48444c0b0b00c422464100c50340a0b4002c500c043e000200c007103042c0301200000703680c00400490890380001d4000300c3e000105680c4089440340d40100030034144c0c001442c5040764000c3c5c008004040d01d5680482d500d1022070b00500159000060900004160024643e4425011000028040091000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 961883003 1250 961881753 961881761
    0xe1c03170103030827150907051207091103040206030f2505070201111b060d020403080a2109022d060a02030a08240909070e040609030320030112030e04 67
    0x6900140d845010044910800340054181051200d401c080e20107012522659a00b07a81c6d40d01d08550131000c0208400e0007080050768003504004100000d03000c2c6c0f840240b9612400341c0f00b02462070342481041b1510b80303958411240500d4014060030b24665a01a081d11800c3d805000403500f074414a8090509c600780c0d039803600605040d13985203551542d085c000105030702499018111f140d08005000d44841d00d00340004906000240c85581c0c130b800304528580b00034000c60340090100500068007541ca250301403803524089500900040f804151400031a04641719190020340000a800b208030089880b54610780c40b12604080010311205d02c2d40108100d5000301550b00b000d640301081300350103030b82c2007014075511180d107031100e01d4001491030301185088814140c150080202c0d4000c0b07039141000f4494200502180d00e6407070300e213080c140b80c41c4004000040c1c00f40e000a00e0500702100e007088a100e13200d00090305c4a82e45003581d080c0100101582c1071114100e06000e845601d510341a202e50203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 961884253 1250 961883003 961883009
    0x806010b0304021009081b0d0b01060302041e0b040306020d0b1005091002190609081e09100c030905040506030322051c0b01090b01200a0201020d0e1c031701 69
    0x4501c1d203a0900784180300c3d2414040c4124024081d003500207000b18100050300600f00c00c09040510380c040e01c0d503008183c2070600000c0c0a05101c80501c00400c20700c0e010380050048801141d1031a40080c000214103014280034000d0348003464003000108007085c0d0580150801c800d00c840b002440400c8980001c612195068042020540101300da074094541040d40503040d08035400a0401c4040480035080b0001c980c01006220070b603504140c00505c41d81c2002c3d190800380b0b508402004080d1850495107076004255280d10441000c4455042103115201504203198503481c0d80850500b41010000600b10003881c00f0f81520041c03215000100c2c100c1c0507203621501118103035030300b01c0c00c04003440102d005009181810883e030042c1100000e8440840c181100c032504c4d40001d00b0021134004803170003003c2c0c6401100b20341d02c0400711020024081a00c1c1000e5100340c0031601c3d04455580140d03181e0081c22001d9500107240891980b420804100002e90244039180101881845110610a901013a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 961885503 1250 961884253 961884269
    0x112b05010f050a270309080d17070509100c0203030f0f0702041a0904120201110d020a09090507020d14070b040f0b0c031014240c0111040825080601 65
    0x8145020741400511600740c0128003100140140301d0155031024101c050719806160007500c40242c041030601c80c0c480007002c0c0c80c0308015203a030400d0b031100003003686014181200d028070602012581550142080320f1001e6000b4004001001b030785241900c00d00300d03006099070140001c014004130683c07984000e003c2030700110b48140e140c044a005000c104c0d113a0100c0448400c142026075000b036582d500356030340d00651000040180420b005400c0b4050b20f070141c040b40c403d0001140220128a9540141180c04210f546095280d5921066141940c105450318009600040040500584034100440b010040f105040c2d00e81807455407007019644040301c00365030b00308a2904000412001400c15034108900501e12411410000c6076040d40c01c04d14803030104554424160700802c0c0d16101300201c9070350700c1451b840d00319080070144120154071000c210540d95180c4810201540104400d03641076a102c0b01c000c0c0280d008000d11b2002101d4507100487c3d00340d40720800017403071fa4000c10015001e42075407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 961886753 1250 961885503 961885511
    0x6031204060c150b0f0904140a060207060b040915020a0504150e0909030720010c170d0e150c090619020a0303141510110f0f0f0703112b0501 62
    0x103003032008550300070343d0110340303664148694405941e0b0b82d0940854500e008039a00601a115854032500c031002e071809418041c02048801c0717084c050144d0141590303030701500050000000402c20030040b694444001402190002d010400c6002c9941c098803140215050941c0b5041e2101e0501030f41102c04007400300014000e4040f02c5550810300c1e40c06030864000350007507007001043d42d03990001c400c3c54800038222030424001c428150b807151400c40b00582e04050702484002c803d801003069a40004900700200341003c141c0c1d440c1c00b10008103083c00240d20f80c00104e5585800302032042990010401a5010005015107c0e017030724107010900c2180e01c260010188a0b00e00c0c580641507c040f0703840d07501c0e01000d41003000000c1400e401c0404010508694200340c01a41117803e0b5000303c844040600548222140025000c80015403181100d013008203d03588032450506403655050a404002d00c01003010300710390140c0c01c00c0d000d00c107050442c0c01c04010058285c0303a4072041c840c90540d02038445c1c5e912 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 961888003 1250 961886753 961886777
    0x1201140d0b1618141509090a090209070e031018050d030203070215040f110316030605060a080a03090e060a091e0b04060605090603060a0321020c03010b010806090603120406 76
    0x3c1401140b8180c20300070703ca40b003840c05a0880c0780080316039004e40100d5444581c004d01190101c00c0303a0391200d00030205840750030700902c420000e100e01d8004030300a03030b2540c0114061034001ca0000c50514001001048500c550040d04406040540030500900e880e038088400083c03020b102076004041140d80058991510307580007841d003041c40e8508285200200240004502280100034115401c04214a8210a000f010914001e4405c51061025103403000110401400350807a034041c0d40c0890700c2aa00301e445401117a1030b203d5005004000c2030b1401c4042120081e0b03002c1351940000024260700001d56200468400c0d02d203103c0b02006001e41c0083d240b01003809921800c40d82200a4504200050914001500302d1249001c1d140c842c8030003000050300d07942c42101c0440030310351020042030a042d00314120b0900e40030041c0c544000d070040b42c0141c55107040511818440c084141e583c210740d51100c00600125035406401175815000304800c1d0300307200b8840402800100a6551007000d9044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 961889253 1250 961888003 961888007
    0x106031505010e0106120203040c170d0e0a24111f05160917030409090f02090a0b090f070e030f0714040e1b12070e06010e061201140d0b16 61
    0x240503000303092004a0f80c80180035041e84100000c08404010305c00507507036100c1d800c11100070304251784682090007804581d0b00c94020b000c903000a02e91000e444082c01c00b4100b0080001c4614907010b28030403080344540b060f08401e0300090010821003641840f00c14030780c00100c13103070a0241281c1626a01c10f098041406662182d00c100380c0c0c000c0e030401c01c41a0302d002520740103000c94070500c2a5140840d194a000144903418400c0710000e2046100400ca4100c80d0725010410b075a010b4000d038403c20070103000841030903040c002c0d40764100000b030201ca90f9603500000082082c10103807a10082200700d281041940e1020802001112001d0b002029410f12b404031008080c0e4141107418041c0b0700704500c40e221710000049455540e500c49030914442c030300100c0130503e0380d01a04640c94007441009800a69080142e41060241900380d90f16050b1104500500c0820702c125481400c01a5004004010360409800b0b0b41c10b9461000b80f02403507000250321500d10850098440d00040e900205071211055 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 961890503 1250 961889253 961889261
    0x51215100614250213151401021b01050a090e09010c08390912100b010e01080402240712140a0c0b060a050307060e0f03010c02072c09101113050d050f01060315 70
    0x7d80c0c24030080040242d00c0c0c1d010706003101b4604a1505001c00032031200b0784c00d40200d882101619042070f01607414502100304c1806070030382c81d1240000c2080e010200340780a003012450403d001c00100d540c51280041c1010f000a4429500305c500810424050a0301681e69000002c051400c0c081c02421680d0030600d480701142c2e84e03c4001c505015203064941816600702420326032258040700e004071034411342c10111002203104046941a07040c000343c14002c200720413a284145001982da01c4528548000d60394000b4450402c500c0d01113000c940740c010001d00c20446181e40180090043c107000c27640c0e0000300c2c1c9170042c16041000401d46540d200c0c082410100c030094100780d81240240007000b204400607448030b0081c0600310007014080c2ca8580d5921401034005042c000340100e000040c0340120926464810369205070181c141058047591440030590191100804100150301a5a160204001016104c0d400890384c50251201071460b03240d0071303c54940154000d08954000c20314001c0c880c0102c13 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 961891753 1250 961890503 961890539
    0x72604030c0c29030606070b2d0c04171f020a02010524060318100504052401050d0c0305011503031209080405121510061425021315 58
    0x1d076071145100c41903904002a0b58404030103c402c05039480d216400428000e10468001500800d900c8040c0802c481da800d54803412800c00422000c0c5d01c5140a080b03031140941074a24940074441400207124680800404099104c040000c0b24500c440c0090100400f800070030103002080c0c2c1c04640e600181e902070007041e07401b030a140040610914a07039102000b4641703a1800d580101804800100894002020892021031440c110741d441411005a4409400c041f1022911805041310344100111a1584030422003480088902140c1c05d1505210040702821003c1d038242e640701a000010400a200c1c4925820604500d12485401e6084c050020482c44454101e101d24005400001c640c021041d00c00392202241c04059110b2014001791034003003429000b6461005880c1070021140b11000e1001c2103506c0c94507011052016aa002411802900540a00c0f030001c1d002600280051800800701a4802040300b0100c102c00341d155002c45280d0090a100b001c030101042c01340c260711004204503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 961893003 1250 961891753 961891769
    0x206190e12031b0304080910170f07121416110303040618120906030f0204060206040f021f030e0114011220150711090f072604030c0c 59
    0x581021800065941c0a19012107101c5800071000c030708040b04a51614100107421501103440b41001c1c20644a146d0100782040d00c286510007034001980e000d0000d0100c600c8101c0c21007441e550782e01c601925029002004c60301004071301c032030380c180c50211842a03914038403006991100c1e500c1d10201a242083e0145c05641c141312036010300c58031f40710001084030381c03083d40500007151500303001070004243c1101c2c003002400074101c441d855500c0d680c8031015008440b5695070600c01e41082c625080308038441c5000310001600b00e14005804298020f40c01d8445620190146030a90300c0b540d00c900c555580300c1d0f01c050010380c407500d408009040900500641d245580144030007549003490782500c8040d5a04000c000500080b00c030030041c04200c3c200540d101c00507000100d0003c10700c10700e500d0340e804a01704403400c0070ba12540c0059824005401441080c00001500766070304d800c03a082d01c280c680d03844104c55000a10000101000f9100d8040d4041c52203601c0782c5242d00450318040150741010f03080ba0310307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 961894253 1250 961893003 961893011
    0x30c0603010521120408010903030f06261207051b030607050a180503100f143102030a140f0c0f0105070201030f09030503090706050a0c0b061f020619 66
    0x503552200c1001070903d1034804034454140620588608003e000f05000c00f2140f40401d00003558041900b0407a1007600c20ba90810ad8089040300300400c03222a0301420f884600100c1c000700c11750740c54103260001c104440c4100e6044003082401140c071356104500407505604428408500b0f030300d1a008030180301c41d040b00901010724015900400034020036401008010100035005886c00300050b00310080d02c130103410344030110041e0901d80003801d00d94120b1b80c40946010440c42d0f1300d482103010f40740101035022850031400c044071106502c0d0a038444081207035100c0f000c20107005035003c10400702c410340705000e02d10316484400c0070b171400c02103494202ca10b60342120740101401c1d0b0703c444100004070f0003420043d4460903140012401800c100000c3c01080b450240304000b85900480514803130210b620840303c009071a510103c5090050b035203500c010499150500c070020f803020321180c2c0c0c803002c0030340805512856294001c0b050451804150090b070403600038440d180042519090000880d24401e02c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 961895503 1250 961894253 961894259
    0x506090303070f0c02220509120903060c09060d060e0708060d0201141c0212010329010905061c0609020a1406090411091e0103150b091002070810020306030c060301 72
    0x5007801000d5654041005213100340c0c00110b40c4ca0380080c15503490303805079003030042400203039010040000340c034141a148550184908001c00380412240d10000107000303032200b900c440d41d542d5516009100401d500c40d030f003031020040004079489108018850f9051214403810a01c0c00508140809411107008600b040202005070740c111901c41c4070020300244459942200d040406004081008410803441c000980410681c110b1200141620301594400b0302050204e001e5855180340c04102c90076080d07100004016141c0503520060344150050b1885a0800900000c80946410320307a00300d511a80c0c2f448541c040d0704100c03000c0000b07002c481d040e507009035603d80c001401a014040f0030074440e948a400c20740d00071004200303549107104082c143e20130b68510801c440080015a80d4100c6c002441e14000800405a002e503040880c0c0800c2101882c0401344018031400001022440f019441104c00005011500b004060003401d2041c80040c2c5a007060010182003004580105100b02d10a20042c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 961896753 1250 961895503 961895507
    0x60606030e0a1203020d0212040c0801021e0f04270f06060e090a15030c0e071b08090d0213140603030f03190e0a0b0f0f040c05010e0604030b01030609050609030307 72
    0x112042070b40008070241c0868070f19030101c0103841020700007442c25001003003440709803059118090203544907001142d030460b240c120983c01c070301601d6201c0c80c010030715201051803c03140a00330b204803402c4c0308415203416285d04500c201c5403901164062030001e90545c9104112031071283d0401d1586c3c841042c001680b0b4000c00801821204c00c60f544240d80800100e00700c0803555002c070728904140700500740904c0d600c0c105190181454408c0c0c4d00b504030003070000303001d8610840003400e10740445141c031032100440d52904220b64100141e00c45d0843e641e00348100140c1d8800c070074000d90148a00000c02d8168084100000700200500901d0182e8800d10601b40d02c0000c0ea401e40b82c0c028400da110725070021200e1062000352414404c0385243e401202801c0c000d2100e040740d4148502c50710515001913407a44018484118800c40d0080c00000b4042814000c66100b00a10420340c0700040190b03052944075100d013880504207900840d540c0d83d852034a8001c0100510506a110300d807800036508502e400440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 961898003 1250 961896753 961896763
    0x111030601050a090e040309030201180f0608040602070b090105090d030b030709111209240f1f0506040803121003170f0f12010501110c01050712020721060606030e 72
    0x54180a00440c3d8100101c0c0714011281c001d0000301a80c0e0581d013010708000d410310420b800142e0000c3c9181100c01c1c2c0c0203c0a20703104040383d03c0198003021191800008984083d0017038812070ba03a540030000d07900801c0300f2902c1640101c80320340000a0508011001c0d600d4002c0c044a000300381800c00300c20090694000c24440d04448403c40c02280c0001d101c4446a42441624800344008900605004160f200001c2e07030403212a000030700180343d09084d00b0300034007140101c0b80000100307241c41c0002d80644005035061054a0080c0d1003403046605d400c00070b55203402940004105600120b002e40c00314040020700c0d41c01c200e4080c8040075060442c0ca920b403021012581e03144080b04c002442002001103032b400c6038120041c000241d17031100e00c410358028070307031a081c0328150005d802c2041c0400d0f4054041040e04c5150416100d4600c0c1142940d191002140803202d95000e602505e5000144540550340c440c1c1c0700030700c41100c4a00187d00703103070210490300260407074000c05151501049540300000b403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 961899253 1250 961898003 961898011
    0x3040905040203011d100b06030609240d0f0b1f06030e0309091305010506090c07020d0204140408030a05010e01030c030f1115040f0e220c15050a0f02011103 69
    0x18000c20306a480703002080c05003143c603c003400002140020314000f00408603210b503414040550500580d100c0b0020030445000c2503c44542c0246600040b964400103820042a030280400c0c20302e100d01c000303800080708a10f507040d0665245961f510700d0000c2065100d2100d07481171b2407040d4100c8151021745244041da00d01d01985d400d03d40c0d24010003003003540030000c3d02c00084000b020744c046441c00c1c484078024041c44050841d11582000d020a040345000304025104013400d41455007451f945808000d0114402607050341c01c11360301c0d106802c0c0c0002c80c0d090310340f2442c00703440d078150f40e828543c00c0c3c1d40441d401603004100c4c14005000500c00160141c0e41d1104482c1c1200c0000c000a200341003c032950110755000d517a00407140302011135095810000303802182e00101c3c03034494160342c8038540c98006004907440100c4400c03200d10903c0951160038051841401941004500d40c6c44404800e00b109401c90782d040410400706803c511680d00100010030300d44503200a200740300b4080b03102c42917404094 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 961900503 1250 961899253 961899269
    0x5090105220f060f0e0c220b060f03010308130e0405030d020322051e010603020906040905030c1207061a0a06120e3016020114122707080304 62
    0x288940c428042c0100c0080c44003600079604002d0f5000f00702080000344013012400c942c2d40aa604003070064038102d52600c080c01510552180d00c00405502140240070700703a001948004180030249500c040b11000e540614440c0709456540c1e030201d210044906143d6000c3c445038110b180400000920100513a40352484264002d6165203a86a04000d5205011022001180c040f80d50801780013000400c444400504044030f04611326103d0300c2d0f400d0701d10500020f5001041a008100241020b40c415140c99000e0400e490420b070000c4008d03070405000b17100c4103414401c0070441c1000d002c118416024000100c09500080c3c034400000b0560006540c0b04280502c50618850247c41404d40c105002c5240ca070825180d042c0156071540240c040d032460029a00444c540083c80c140e01e4520407074902c080c0d01c1c00c69090301410781d0700440d12091030b03140001c1003a4080c000a860980030520031400380c0e0600400c0d00c14070005003028030b4202d01110004d5401e602c604020000d201003c4210ce00380c403060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 961901753 1250 961900503 961900561
    0xc130914070e330f0409030903020909161e080601121101030203190b0307210c0f03170919030807141207031b0f080310090606050a0302091315060305090105 69
    0x81c4001340030404800310700e50700310f401d00059800305580842c1800c03e40c0d20888042950740c03500c0400c40e680d000d0210203202250384525082c440e030048651241c40800b15089518885501c85421078141042030b44130801c0102502d582e18100403a03014002e160300002c0c41c0450440c5080c82c140300d031300c05411841301c000f565076040314001c0c2d85060100c003000d00711003051041c00e0a5843c405890003000444c0603076828103021804583c02c5203d48a1000b01e030b07004142c41c00f020300315903c500000c5e805402820340c045050f9012801d501c0010340100d009600417040c1e6919079040c4e09000d24681c03032120380c0c01860303000060800104c02e1440305032000c0c82e03007501e041c4070341600560400996044240c006004421092204420003d0f44801103224a09511505200760360320343c20b03003060305d106025080101d0010300102040d03500c00c0e4054aa03402c4020015180c0020b0000400d00712003c80300030581020742c0a009001152f0980035040d0420a0040208020702c0e00d84118031544040454041c03c003004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 961903003 1250 961901753 961901851
    0x402010309050c040c0e03240609100f030f050606090c03150d0203060f011a1905180d21110a02010c170c0601170f0c130914070e 57
    0x8000e48080194060020041d9a00c1c0d5000905007006c0c3c0003801d0310170322500500c40580ca12182410803482031140c4984e0540c2c9400d0108007803d400284209841410319100243c0d540c113011500c80150b00958440010084c5414514100007000300701c0707400f0385000014480c071081d030341c1c0c11a5840018580100610100ca40028000d0501a640a54540301e840c040c041c5020840c1c0d402c50488950341c0c12004480c8e041d1001d40418095905419040b01000314000c0d02c550113440248500310500c504000c00c0a1030f00005a40042c80e000300391100c0c40702c3c404900c2d0513807108010030840580c130300b4640075540c06000011b130740e10b0794400024100100216144100700910a55101c000b00c0d4112564070b803a1144855561002c0034884c40014801d015551000b204000c5440346105030754401511070300c000182842003107581748201d041d0859481030400042410b40407152601622903020300b55091078540140206e440103080024600b4190351050315102c40c41c0c460705611030307a01c1c20a4160b404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 961904253 1250 961903003 961903013
    0x902090111010f0203060a06020601031a102706080f0a0f061107080a030b0409211101060e01050a14010210110d0216020909030a0212070c090c0513050d0305030402010309 75
    0x84032044800c641c02c20f10341d00507032041500614800c14059810302410343c0e0711042280d85c0c40c002e202c00f1303040503984066803180d101e00d9002c19a2062000e800070381c069654402003d1113100d1082902b040710b604440140d24414503000d0640100b44160003401c0104512410b1500c402d0b210030001d0088041001c3d08003000038580248100185003520300f074407030069003040b1146070300107903a400009140c0041d03c012442e142c81441c0b00190840031080601d10070f940c151514010709110301046c840080d01104000009002d5080541900e81040c0540d500d0300003409128070458004004400302d41207411070300d980c0050242101c02c0c5415012610284c0c40101d01054420010300e1058540001054031184050300c0001c50141c0c425507018460b030765181c42007030f12401100911001600207070024500d81d4000806418020f0140c03008400c3c1c55580c100c01360840d18160310311800320300045154003400c69190081c800400e13094480981007803696800800e98030000304028181551f8400360001d010f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 961905503 1250 961904253 961904267
    0x9050121140717101409060a0b0a03020d05010524031302031c0e0909060c30011509060e131d0c210709020f0d1a0a0905090709020901 59
    0x14008081c101094248800028144050041d48500ca03002c0300b4080703032403551420035460496511125480b500e00c41d4000700b00751600041d0030141c2c4400c29000c00308803071003400c00a080da00300644005980d1840307911407030242d03501688520711071605034070b04454003030481c03207c4400c1d4200094095036030f82e121081000b184454030406905842144880030448114040405d190040c540f11204a07039400410800210001c0310346262540288001c114001d000c407000d8403158000b00300601a030549030002a00188c641510f20500282d40401005501e54030690028140c00031b10341304a141742080c5024280600b004103a90103048230031050308542c1041d80c0554411401412081c0d00d01140300e403a00e0340c860b890001c0602c10406000d95040f80200709500c83c013562a0840648a014078201100c4000d400001e085c075401d903010066450b4450032807003101c0c0031000f50202071a018441d001441004540c68000300905032600c0180f0905d0180011200100d43c07440c0350140e80d03804490700494005d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 961906753 1250 961905503 961905521
    0xa0f050a0b041202270c07031209020d140a060203130215181903050604061d070807030f03030b13050103030305060405041e080d181203061a0d14010306051609050121 73
    0x11a821700511003080506c800514038503000b0703aa200c034050300c100f00c11400c941824100940c42240c0c44001000101c030b14000b462442c0c0c01c101500e8840ea01911281c088ea030044401d80312201c42000c450b0214035142280c074410144001405003882045441c45e203988101101c3c55120b010301020f00a408048440f0001c05968010190f84c8079052920300b1001a1491000202c003800b281c0020841d03091002918108480180000745405803a6840e4041001c100d102c05400b0551900d005840b10344a0607030810001d90356410000d8190316506004084a001400c164800c0b400d0605100c0070030801000707820415003910f5601071100c0c161a0a034014800c9820043c51581048480d00380c11100150005d08540218248030884000c014128205c4506008684d201802048081d00e100a5034010b4000441484000240701249412034540d50000343d2084440c20784500401525009240b400e640c2208641071120145081c0350010307040c1c0c0c0510000796070f200a1550480c0851600b50001c602c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 961908003 1250 961906753 961906819
    0xe090a0f03021014061e13020a0f090e060d020f0d0c082401030302150705070b010b0a1d03030a121508060f0702060f0a0e010b0a0f050a0b041202 64
    0x80c1119454080d40300e8500f5000542c2c0646405034010005600540143c800c4100a2070344119091403c542d40b042060014147c2c0c010310056000c41400300644001c00e0313061100d8894181c0c000050400401d040002e400c82c4843e032108805000301500c0c2d103210400c0d600d504541151003400c070040070545a0301d440034054114000f1040020b400368010030f07102111031a6045e200b00400d2039a285a1666900703110040050380700c11206181401c10041c0c5a401c4445841c0003450b014540d100e0300304230502a00242c4210000046509817142c200300505d803003250000805148100a00019849000e2a440c0900340950746070043c0c05803102d944048408040c00303a00500040c0c90798a1541e81e2441103840c805052480b4010405007400010094401c0c0a03017501c0044940d56000400058129001e940d40c956407200030030041980d45440c110040d004499980c65134a06e040200b04a45429612001105d6010041070102c0c0c10342188040903030780c05403900308010007017140001800040d03280070741c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 961909253 1250 961908003 961908023
    0x103020904150602010c0503040b0f0402032a0103060518010902030a0f0e1b060c1b0109030506070206150a18090203030f0406020c1314041b1e050a06020106050a0e090a 74
    0x301203280d618202c0c040d0f074050303402007010200654080ea0240300680303010301038001880000c1e860141c440d510562291000e4195880304818084807000700708511004a070407a9110503548955900d8420203008100440b150700070b0101d0003080e44180481806240395981e00000015400403050300000c90030b40c00450100401c40c0c0c030034040c544440c101460381100c1401c0070340301c0100e0b00e00201540e0505c03941c00d001e840000a00d0a51540c109030b40080141400b9a100000011810a10005100d2200d54001e88850b2521080c509204000c00c1c4405101d0420300b482440304d6071900000680c020b0002c1d000040848050000a141d8011452004015000064042006640850b103142c01000035282100515403500100d4195294400c0040c0101040300021f0701140c500c02d034141080e100102410030072070721036080140306105000501076548161104000b6030500c0d001a100810641c802008a80d003407100044104103030b441168002000346011030240712051100100603940864a21 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 961910503 1250 961909253 961909271
    0x10051b07060506360601080c030a090f0209090a172115030105070c03090e0c09010806180907030302070e0f011701020c0a0c0302122113080604031119050c0f0103020904 74
    0x4c40d44440010407a207810100000300e001c40d4000c0407140e024502c0440390908656801c800c55008000c01c15050320b50b0b4454084410141e225040400d0141c403110000c2c0196042c1402c0491291035a48030383e07004031074208001081c0805120700c0c0600c0303e83d900604401074941c50140c640100c20107820302d40c154640420b014140390000c000c00d202500c07035281c806910741c0c0c5802492503071400722a481041d00c0104107508242d03105100d030f20f034410002002c030380b00c08034a9281014980d50465100c030b10707507002d403a0910516404200c150010509240c1141d598504048d20802142d4180302d042e21103000d00940b403407149000c2d0103803610328880008032104081e20f41480f001c01c01300c0d4401603006540d00b03c1c0d14052500d01160101c21180035000088100e03010448040c920341c041d09034425078031807400c00403c2100c400d12078980290300a035620009046000c030001e040250003c1d07a130154a01a0042200003000030886282903c412140710740602e01caa8010780203441030f41d185580c0207250000d81 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 961911753 1250 961910503 961910569
    0x9180d031d010f060f27020d0f05070306180e0c06130b03090706090b1201171f0c020105070f090b070c05103609050c1b10051b07060506 60
    0x31504840541d01c50001a0350f9a0301407031a00c02030120194808044440740814011b01500104502144000e00180188105100d281214400c4d9040b038002501c4210401c03c05408102a242041412004010021140d031a50741e81e085003043c0c0740d014500c00b0070030307180846070310442d8402040304000340b80ea42c0c130303025007100e4480d0402c0c0100e8000c07882c8040d020440b40044400d0303e2500c980d01800100320f900f800d11280008502e1840d2449601c50100e8402d5035215043c406040103440e4400070a1201e500310019084d80c20080c18a42000040342c490640e9903404402d080480f4110705e83c05640c0c55407418200c800700500d03001207820620140803443c84603440000408184199807103000c101c03991542c0c040c0010f020050018116100301d1003440405141e9014940103a03855100c1c0303180003864850455134900011070072540c0d401c004001421480540a841c1d8060700c1006500342c1c110408070140c115008540d0040c1c0465a104000782c8143c54648e140000703800c0c0c4407000e0791145501d00e50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 961913003 1250 961911753 961911761
    0x4030303090516061b061803090e15030604060915060b03190b0a0317090d0b0117031204030309020f151e07050706050c031c060509180d031d010f 64
    0x211010710600c0880341c4a10f54030860103040e2a5640e89600804441d090405d0030394003040400d4036800d66900d00030032581c941c801d2909a80d480794480340c0045180030405644c859004055071043d001541c2a00e116907000f040d030f41d511640c021800500c0d01c80c141401540081c000200380e400929041000c660850403002461241c045203d204415003011204c0074183d85021005a4001b03515200a00000389408083c0064407900038000c0e06001c11400014404046020252a0006034000511640140c0111340600b03074801402076290001e59551061400e00c0100060304240d5990480c104566480305007600d01c2070010014045203011070303003105107903110220820b081c070b4440181041d02c0c01488251141d0075000b801400c0c2e0b1519212040d5880d03401070036010080d00040040c003810380328060030701920301a05800018070a040000344442110090706c4c1800e440001070514544103000a51502014142e10300070900074891100700c40c0610b0420340c820a59420000b01c603e400502c0c0d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 961914253 1250 961913003 961913021
    0x2190923150c1212070e2b0501050a06030c0621020d020702090108030a03240611070e0703090b091603080906090918010c081b13051c050c15070b0604090804030303 72
    0x7403d14045e8548650988800e503011704030300c2e000410340001d011290416038542410340c0c2c070740241c4014480ba69031394508403070741240c8102c0200c0c0d84403402c0c8207010f500707440d0101802207030401d41020641d88801b03040500c01a4107243d8136940004030324442c9919601a1050303140c0c090420070700c13940c4a0503050740b660400c000080000303141554082c450054201300d1094005e94140c03c210803814454201c540d48000c6409c08500e101d8007100103a01c80c40c0c05080d6108841a40c0c0002d40b489061505c5052441e02428020303040d8044188039080c407808811400450b60711455403507507134803140045102030140d500890f9004000c1c07001c1101000d0f001e00c1440c01c510020008100d2500166415036a280d8180c1d0404048031151210300c0707440c1c900790010009600061003c005031503452000039005526000025922204002c001c810000c04120804400d08115204107030412aa0f00c0010a4040c2005c0680400d40f04c40119020b0340b516400b0101c00c98100c0104d582d156268100075000e411500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 961915503 1250 961914253 961914277
    0x5120c040509010c0504030b072303011e060509040929090c010f0c0b071701030629010e09060406030204090807031b0c1203110102190923150c12 64
    0x1211410b06100340084c080c519204c09050a0940e01d440c4001e150041c0180d00303205202407000d043d00f61680c180151940c9940301c00da52981002c00000d0399040ca40380041d0b5900c24001d0501a00380c111042d900204c0044e1000a07180c904d904202d4818020003100d0100030301000303160114504028029031083c02e8210445000744504070044845203240c1c4400307400205030a04041c00280a02144c1d900041c080c6012200c3c0080c95040c240e1940082e4421078002da80c84140c1c000d800c10b10b8052801d8610b808069042c100f002c00006000e103480c0c0d41c0d2003840b0f0701c564400a005a0340700c1d80410051038001d0300400020a0516202985030300058050700456000e145071004040c40c50241c561403940725421250961610140740c88101ca1804102d0610400130300d2500f000c103003407014050402e91040e18000c3c050b010b010162405e80280c012040441c440c01d10b5001c80413156900980303d0006586400307144500352102d2045000b100c61001043c002c40703620140d80380c0c1d4100070782100c6400c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 961916753 1250 961915503 961915511
    0x41e0b090f010b0619050d140106080f07030b241b070f150c06020d09060c200a1a0613021204030e0612060402300708070203030408031f05120c04 64
    0x3103010003084e0301603038103100303d001c580c0008604007520540140042e0f6212603004a5a016079a052050490302604a45c1c0002d0352081041403006804070285e80207000c9081c1006440d182102042c0c1d403030562240201c0318282c14421002e1411028103c50b218183c24000c107002d82144c001c0c1640b1404580f00d20a568000c10314007042411030001c1d544451f00341c039241c565a0040a580ba000a0342002902d441000c0e92801c42c6808102c813400f6520592040d42d40e800c00310b0342c00c241c0f60800c120117640e0404d00750340040c0143c0b0015a095005081c4141d400860300d0207a0794083c00507507004220049511024004159036001c0700d00f4003c158000c0d071007525060400d00b00c43c400e00c00c00c3d004888446991100001c003140035410709a000f04940782c40ca06680008a0039601c100d105140b207240e5140c2e100841c4810060076981c0201c038543c2140701440038514505003501d6a042c00d0101418681c0e0f40d06410410310172004104404a000303020207852600b0416490340590380300d2401584d2a8015410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 961918003 1250 961916753 961916771
    0x61f030c0f0504060e07020c13110a081f03050604020f04380607051020121803030603030a032a053109020f0d06030c180b09041e0b090f01 61
    0x24072211703944594038590050424001e010100020f10150700340d0307800c60984e14803001001c1c2c056030b802407000701c800b91100391b120305241000702440f116807220b81c401d542020300148002040440c0c0d040c0c006c2d8040781d040643c4a071400004000340340340300312001c803800741c00c0740340920881071a84c401480142101002000e00200d0501000d40300d0200c000700789401c55115900c01864503400849400e1800800c0d0480c2c1b0380c1f484802c140340c0e10041030381001501080400001c1017400c2d01005071161003001550442c200400469a41d00a22040c40c041c5070319101d801c41c0348030f03000c11203184000407054009004050620081c01a81c01a04414021504501e003840e5070862800f83c0c80441c80700b0041410321520b02200c0500a42001b8039100e40418100848001c03524207001da00090b500032a4844402440c0c0801890001c00e41e94040b4842802e25100c840980c2d0f4840943e07a0050304a40311009110305180380d144140d183c0d01c0020108070710541403100484001441c2c955030580d12000b0008404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 961919253 1250 961918003 961918019
    0x2c18010e101b09170c0a080a2603340e01110703030225080709020c0601090501050618040209030604061d01020301350703060c080c0309061f030c0f050406 68
    0x101c980b0154041110607000f000910103041e804000c840d100015500c01c034041200140308210160b000007500d82c8400b600030144044605000000d0010801d4510350042c203014504990100820170a054003140140b03480c618920701d450175409060010100c00448440700c083d1074032683d004d106000030032001800e01407020000c1c0c0c54050301d8040d0014130700700c8400c5005506e101115101141441440719001510010410401d4040e015440c00035846041e203c1e5042c1c9041e1050b4031400302142040010040d0313490741c10440d0004440c0400e44c0d20700da0b4200c40420041d1281c072450075054410340c800c2105001066024580d20350074440014200380502d4805804c0c0e00082c0a40b4003c8980d0344281c0204103050302008664a401d0705c643c0b400d400b84034070301d903041c20480e60040d1026a03c51440d200810350289900b1f03800740d40d080301340303003181082c0c448140e4903000280010401d4445003584022280540c50a90003540d008075004000303a1100a481d001c540a0310409009030705110020910340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 961920503 1250 961919253 961919291
    0x90804090c0f02060a02090102120403060507031103070e0904060b1810050102030702061b120a0f0207240e010e04091505092b0513120c2c18010e10 65
    0x104043e4024500c0f500c40551500095004980d0b83e4103510a0703016035030301c1d900381d18041c2c0000c601840002402e4506070f0780240a85000c03181d8110f110741c08200b000101e035000750100c580814165028509a07030341d4038107a001080150071840c0d205100e80c070a015400240b4141c14400c4600e0001036080319a20b4005998074010070000a6002c40c0500183c0b5031680e0001b00a103004000000f1118030703981c10751480142d640a08002c20028000807840310740c02e5010030218009041195050f09c0b1640415034034170000e000191040108800b2401c0001c0983c442c42041e9a85007000b003007000b96501d5458a440d00e10180b560b055542030504002440d010b40219400611246201196110100183d45c54103440521800300003440700501524020b00410511200130f884402900901c480007818158400c540b2540440c094000d4000350211070014102e900320240e2040c885c2d84403e8841901032820072644940b141003562800301c00701c50302e450014409201b01c6941b801000740d1070a40080140308 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 961921753 1250 961920503 961920527
    0x1142d011a0906090d053417070803130602010b0406050907051e0316081303020705040c02120307052d1b0c0415053a03020709090804090c 61
    0x70400c1c10448000e40014400030102074000a107107600d022025800240a0039221405803900d038019119801c46803410a40d10a0142002c6a0446842c8503100090b046166034098160020f05900c8000702c682d00c1000b80b86c0140102e03109480e00d4240d10082e07641c0c415174a200b00701c01036003895402051403c0c90721802c1c040d40c0340544000803941d60102d055034035501100c1d000324400e141c03408051910129802035801150700c0e00c070902c8000c1030108002e001030740107415503150042e21140400025000101c080c100e0b00103550116004a00480c16403c202c001e18050700ea1507000810400103540c021b0050800c250004914640c200c1032001c00025104140200d00c803070f03881006444a11800c80d0f03850114148603c0480745402a9500494259440044001a0040b903000203105520f0302681919070b41d01c0300440a056010345507012450717160400d001245c1c82855440b400107044c4207000c000007501c280c801c03d100c549054980507200da400b84c420088920b1034135042c00d41c032602c80c81c0e4103904 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 961923003 1250 961921753 961921769
    0x10b030706051305061303020f0d0b04120809160e092b200303010603111603030504022b0f0303060b0a08060f1206041b180b03060109060b120901142d01 67
    0x1b41d081d60300f4440c450201c003907507580c004000320300c1e1000282c3d01c11040744078911540380082e000211081c0600a01000ba10025041d00b004440506659090460004031490720070703265a00c1d00e44009072410055081e98446114125028100c0c2c101002600c10180b40b1869550844443c0c0310b5030255400c200b2110300810301c0d04200010086603200303402000c100080f058540d4540b4403402400d51300460780b03a074200c020a4490b402c00040d031030304190030040084403885240012107100e003c59190700396440000c16a200480398402410701c2a80564054280d800d42c81d0354607003a1000151600c4401c44042d4400d85240840030110b06100e006168106d60807401420561260b0740e8244003407900e2807000e06002c4418000040450b44494000000c1c900d000c400524403140600341800c110307050b00002e00c41801c1210402c044090141110780c2000c25a0f256821034070341040e11382c054495402e0b180b401c40740b444e00b4410003ca1050b00188402c503009141c45080400d006403000301d00e0241300b9401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 961924253 1250 961923003 961923037
    0x10e060105030402130e0709020406030c090603020f0a200307033606030e15070504050a050d05070e0a061a1b0705090a0902010c02030a081309020f0f0c010b03070605130506 76
    0x100018540d0403c209460041050380c0f47d840d03c54480004036007180c1c2c40030f00041e07140c200e400d601c2ea81005412000e0012450103611b8113016000c3d00701c6030300c120700130f08040100598189054900c40460713004103510b54025655100b182e414010302e49100c10900d802c2ca4801e08101200707902500d45000300c40042114211003091900100303400900e1045200c43d20341c0210020075000785050418544038040b80e8407803d884600b00b9040c002c075002c850308254000c0e940c041d2510301041c00010710307101b00c41d0003512924103036607100701403c09440c0070345c4130440317078060480a01807080416014001038400441c82d0301320841c1c05800c2d02c1c1c0d66041481400d800c0b90030400071030154242a0012070343c1c81e0041c14136142c615990b5000c01d240c02c0601d003064400b00e0001c507800c40c56000c0000078900900c01d0134001e5040004144100b4101e124a03510948504d500081c0d01c0c00720042074004071a81400201503074507440d9500d901409551203103c03041390010342c5c2000403e1500e0804161452402c031400c2c80a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 961925503 1250 961924253 961924279
    0x604092d0504020f2b05010c020d0903050c0405070c080403060504120c11120304170313050a14090a0b0409050a11041a210f07090c1b1112010207030503010e060105030402 75
    0x101704034494081400000310844021800503200c0c03103e117140307100d0800051407401400c0f00030f0921090070354210402408100810100c0c1c00000c11f001c1d402c2c01102d002402d40c8841c4000e503885400f011000b0071a5801040010a214035640400c3c41036000e02d80b000200030241d002102c9c6148a0f02c0c0c002c050b9842086a5921410020303492803030545042c0489142c5521100e5190000c04000107406d1594000030765a01c4442e01151003078024a802d0302d4804040e802e002c41030180015264900380075074002e600080c02903816801c08034089001500410009000341007140c0c41d020140416605030301e10400d000e24071b0800344211903181c40c2820000b2410400c41d02007085002207440d41c0b001142101c0380301d28100f84103000d4002409000001400c0c0140381100a0082d41c407030701140000c1c44a404540d940f022201a1004070269002c1d513400316170405080010402003614440d0280c40d8400700f012030816400c040254140c5040807800c010544c2d55800450f1544001c0314000d4026110500b01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 961926753 1250 961925503 961925509
    0x30213090213020409090203150c0d0c051303150b03160504020f070b070206090106081204060e030a050613050708190206070c0b0703031e0c090b090604092d0504020f 73
    0x100c5166100404007a4044031403403010090f600581c0088130203030354811240085240400c02c9800d40c1d83c00d00020040ca140090702c01c10705020f8540c1034021540c90f10307042d43c180c0d4400c004440580e8158051245519181d0826103059803400381c0303480b0014a0580c40001c1468005203040b07454401b5451890b01c41c2c10305040c08042d41101040303144141c410703ca808000307809029103a10542d144e50041c01c552501d04405070966102d544296407d405c100e00b080045070844089030705465982c140b081c44800c0400119103004440d14024125028000c280000d40701c100401902440c0140d04a60075503840d98610ba888039291a80c0010001041110030b005042a0003d0071500380904100700c1e110703030b403426148801d5000c0c0104900095440002c040014480740c4c8900b03000038021030402111455420140c1103940341d000d04900c0c008081011030403550b6180403680a804080c4c01846400e0004081c1000b203607540c20b060b0014040300b5070310000c2d02e000d40306662140740c004000c0308a1032103610078 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 961928003 1250 961926753 961926761
    0xe0901060f0509120a0213020c0601171f0209031002190309080408030705100c0206091203150d060207060612080906030a061d06040606051611031f0b090a020301030213 74
    0x20761000d004003404060b02694814482000205406000d0038070b001c024810440362180025205206a20500c031a410020001510714150340344d42405801102404000c24038241006200c840981c4d00b480240000e0f80350350700905181d141c16411030b4070380c007020300920303040c0d00807502c1d0703a5022105024003040b440d120ba0080c2441c3c0c0c2c081d40380c0c0d030300c2c042e2500c05003403d40d80320f10000c3c1c900e94400e044501d00d405035407295600c16252440a0117107805c00001c1240c54031961a800300201c0d00203c040381c85005031000720098003000510f120307400c0100e80b5000010390441e41c0305a980c2403508400065234540ca08550120350b03130080740b0710f14180a8008000a5410182c90300100b039540b00000b03c1c0c40b40c42c00303003004074407054107400031000d141c2642080152800b54100000b0000140921302d9030303080d03202505820301e51000201e041020f941d00884d1804002d0119001c7c50820003191004034a102d9028500000064550100390340c0d4044001003030388021720000f50032000e1602099000034090740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 961929253 1250 961928003 961928027
    0xd0f080f0618040c0f0b12060d030e030a0b1e09061f030f08030a0b01031e02070611070b18030f0702090907030c09140108010b030a02010c0503130e15010e090106 71
    0x1002c40a02e0346807540c1c10402d4221000c651440c03a00707200f84000c0c1c2104400c80004c0035403020b03107407405014040b03289944101810107070003401020082800c141c061207040310843c202408a0301c071039105090640030702a054400880740351590000764054243c400140344a010b03c0801004e080d00e0300050404134a01e500c0341841d016060110100009a180c0154001280505012900c0707007041074010b0125211a405c1605044c40c00c6800a0901d0003400095180d145c01a001615042c0c1420a00054070904a41128502000440c2c80400c104021018000d10245142d401c224000c015400e03601c0c420031000304640e49045c0080401450034414095004c03100006545445540b0f5581c41d0342c401c02904130610007611018102050170744021128018440c6000134041a41d1034004240c945820703d10285c104510b460f03001081c80000c02c1260080006e080d03201d220565181610017032200c0c10746031003001c510034412040141d07100780d00c05041801e00404406559182c52407d13039814034100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 961930503 1250 961929253 961929259
    0x30d0c0311060c04170105060a09020c030c03040b0c06010e0c0405060714070b090102010e060c0322080d021b0f07060807020f0304090204030b18070501080703090203010c020705030d0f080f06 84
    0x9840c0055100c05110300c5000d03d041e603070400c2e111410b0542070b0515102920064880360b02d4402044500d0355115101801c44074a548016918110554203908611032465008650320000400107162180d1100038894141e6030401c0d02c6859881e2005486810001e031454950a0030901091040d860140000c01c0c0041c807500a10341d107100790501e030508041c038a40c8035035140c80c008601c109d000c0d60203000300e40521000350003400301c614208d203000841b4007000d407801c4042014111070346043c0201012074509140c0102540b80c4480b00001910080d40c4042d62030302901d418102d0a0740060b00001d00319140791040340140208d181481c1088070b07102801455402144070300441001ca1480500050002d006040000350b42c9504509004c12a844094028a0702c60549101d0340350456003c603a050a982091070070b90f541782c5610344120081c203152007004c0d41c554a0500c19401c295000100d11080392008e4098900001c2555002d980c2c8002c0161590040ba94010010306e8130402c1c500e1507036102d4001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 961931753 1250 961930503 961930517
    0x3030f120b1908060a1404060c0302040b13090606030204321c0b0702030a021b0406030b090105070305060603160c1e03181410030207022e081302030d0c03 68
    0x82001076041000358080000b011081107090291030000d210f02030340b1001656040c04517411500801c100840d00030300180074240c4d00d01c440a20319200360112401040445c181a07155121094145141500d5100c0c00c034520b4502440090160300a00a4800f03c81d03e8003000e07042120400f400d115011072000000c440c4440c620b094061a60341d0880d54280d25020078101100b0b243c1501e0050641e070809482c3d5170641d4014401080843d81c0001c00350486607840c2d01801416829201080c00f07490180c000800042c29201001110481540000c0c8200442d940a003c69180e1109001162100340c45510f5140c084141b0180540e0198407041c3c046440341050b41c00c07201c2202440340781e402d485c980450020b000d102c01140003020100c800c1000d004604c101072511600d210008540a40f88484502030580110781c04040d940c2c0e4412682100d103e850b003085081c0445204503a41e0f54840c40340c0c0004c5200b582c0440d042200e06c840d10071500e035000d80200150b00e4114001c0e145006481000c600f00122 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 961933003 1250 961931753 961931771
    0x4060b04020a0e042f0c150a14070306030804051903051203040c060503010e040b180106080f07060801151407120c03090b0705100b010207051509010809060103030f12 73
    0x3248010b01010001d6582c0346200344140c0104002e4403001241d001c510030172088900c5d141c070241c00c400503080c0c0c00380700d260783c3e620781c008000c07420500f0f51041c0309081130700d18040002c3c013030203900018000d4815840030366640c0ea8000c2c0c2130302194058000a80050070a020900c03c0b810110102c00d1014158449200541c1c0d60780d480c40d2402c030000900c114008404801c1c80b0811a00c030b101000a0b1100d41040d9040d50304102d8851020900100085c010b0f40341c81e030210343e88407102c071820b140541c0100001d221207034032000b2166440c1e04004043c8400e02c40c1c61070005440e0701c52060107040c0d60b00c20741c03000100c1c030340104e0807200708860341d5a03144103010421000000903c40302c1660244021a126240d0070415410b014005000d5540442441a03040245400140b40450611405003000a00091805c0c0d5040100e01d4104140c0005401c481d21b6921643c140d8a41000362003016030036a00eaa01580e208586991904020f22009011400703920108880c507014403e41d10310040824400505505 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 961934253 1250 961933003 961933009
    0x2901120213031b170c040f140907060206060f130902010302041d1006050c1e0c0a030b0f0603071a030606090d0f03080a06081b0a030501050718060f05030a0504060b 72
    0x3881d4811201e911030b84040d80f0300009400100d0000b00001d8088003201d142c3c4103041902d0f4102032a5041c0f01d5039440820aa9055040d8030035440b4101c1c0304046015482c2150203075a407141d03140162030151141c800090b8480c070b800c000da2103020101a000346083c401c0300d40800c0241c02510300880c18540c082c000410110030f040c0f501ca0f01e512010304482076504001c006440820391326003005041010400036180e444400142c4120700c00513460b2802414942c1003a00da0503d00381502e01641b00b401c040000040c083c4504c1c10034000d1480c0545244141c0300c003030405944400c00d00c503e284c04603440000c0e1001245084c05194000805402903107000c5000c1d0014031004150300084a00c50040f918007814194011402c5500110041041180e1410314191903600c0080c00502c2c420b0380180442d00340541c950705054401103510030000c2c0964204603401030b000a001d450070031a18020312000007002449003c4000100300d45032191443d50321440810b4001d840d00500030745010380c44803d0041c0c213803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 961935503 1250 961934253 961934287
    0x910050a02090d050706110c09060f03010e0f0703031d1012020403020312031914180a051606080f07140c010207020904052d0607081e0411010329011202 67
    0x64400c40181c8802d9080c14001f410f03405104015802c0c80c0e000b403d181d007581c1c8558125540144084807440700114404001901415050118802a00850301c903001384003c00100501074900c2501c6400300c032200401c042590700b00c0b4000143d4814012091a01c0c903a0180c03200c13110940304e140300945415120703008030380b07012082c000c0300310001000000c00c808240c00002c45a1004104a0180183d40c106c0040317440d2441c0190095150744903c1d0f0802d080c0301810010b0f1843c1c240d0000594011001081a031940d0b06a1403150794007040c032800009071500007050401d4842c003001d4070f03218284080300c1c44800781d68026104030340381c0e907608008200c00f590b152207505101703d108000a10036036004445182820f01c1309015000c0111840080e0107500030701281c0d59a2041062600031825500c01030614003c10000d0120302203211a9002d02007840049042a1990710f02a01c05210342002c0210360301078055212464a02d0052440241d8450342c4610340903c422240074030094240b10071000849189 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 961936753 1250 961935503 961935529
    0x1030908130609080732030f03070516091e0b0103021314090112030804320d1e02070b03060d020901090e1203091b150a0302040305070801141f1a0a170910050a0209 72
    0x10303030b10202000c1b01101c481c42e840c4016100c120401d013b4004801844900100d80f08040e8280544407000940c00d03034440e0341555069219400d01100d1266241a8081c103c0304004416000301d640800200702d202180c04070b8011903a140c2c2d00e40c040c56a46464500c4050b9080003104c1501200711118680700084081e80c0356000703401c1002d084440c928030700242c00c01078841c070551a040b0041da0600491500402caa5084031000964150740340c5c1d4100008030b001e4010707400207601c5103540b00040340008581e480264816245421200924140c2188401c035010444040600d580304100e00300e208000601c0b000700d59000a080090203904a0884003415004410080c0001c0e6000c0340410034031000b044418001e1042c1070007040000c3c090300c00d103c0141c030000c0461401c144540455040840c05181d2900181601c00d002c0700f4052000501c20329a6004500000006400e00c052407004000791507041e0080054400509c0581e601c0301e000e2029020090012021a50910200c540c2e6110030b0015944 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 961938003 1250 961936753 961936763
    0x306050c0306030c010f020a0813050a06050403050111120c07050a06240e1510090302040903080103150608030d0e15010609030b1503030901030908130609080732030f0307 75
    0x780d01e8070740d061500d0106054600c604006682c0c10661100d60007040031910035401c08812965140f400004c828000744a6000075009502030310000703183c0d603020340540207603485003000303000800207680404854080d158541c01400e240c100172406d264103c20060841b81e1080c801d44d0b8520500d074aa14003105c18101e1103c40003800c10607a1190101d2492050700a8004051083c1c018249150748048400399a100310380205228031203c1c82017030155800c076008607802001030080c00302030b00d0700800c1e1110a00c03088581d500114480130001610740030710000d0f5501840214100b00000403441702a00348a01d600d0694010003d004410306810301c00c19001c2c0c00d442e01d0b6006e00603d140f614509114009004416100e0006000c0082c2c0d03501008540d0003070303400d10300071400070014107100b085c91040ea480007079800d00400f000280150003030218801c4469100c2940e8900c2c1d40c8190081c0c100c030701c500ba05401d903100c02d1110416405041c1c50285004000360071203c074640d1507118140b445c1c1c020001035034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 961939253 1250 961938003 961938007
    0x51309052401060207090e0c0904050a0507080d2a02040b010c05190515010e010e272a030717010915090b0115021f0e0d0905030d030b06041205070306050c 68
    0x3c42250100415002880040b00821962002c1c90641c4c0d03d034541c0c100c00701d11584085002c202481020040080c0164201c4140d030740302c82e503802d595540c46207014452000b08101d450003045041012480c040c083c55460400709180505034200402003020340f101e030b4140498086148046602000810111020140c03402d800c504141421352610384500c0003501c04000d448010b004c0c0194114005044544150141e141c946456158a22041040c85c010084489018400300720110005000d4401c4821100c440758007000840130320748820b080300d2099003641c01060200400b1500754044444040c11400024154126586011841c07d46080f51103c0d25122034582052002240c0618010308025000115009070b51001940b00c415241140c12204800505a00c3d50b5145402510a0700c2542066a600160303800000d400750303450340038841c068071848981c00f41440c040e00c1188180390000303040301c0c182490409020401e06022a003243c86004000c030000002e1120300525000c1e414690680d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 961940503 1250 961939253 961939259
    0x18031a1b1201090f0908071e060903030c110f070b030c0702150319020403020d0b04051e03120a0b030309060c0f1b090601080403050d020a0e10210501051309052401 72
    0x4013520040b0003910203052401d40300c03100140e90030b000c8807041da502c107206070b60a03c086101e07690078400016000c0c00e85410094008200740d07150340110409941e0b0303203c003403002c05204940703a92044c0886480219521452003401804a440042c43c0d1004150046600d00262030b800b08400c0b130b1500c01145092000030080c000d0301142d0410300903401003168011824680b4640006042401940014118001c0c103c04941403000a10100710008032051020b103004250004040d40d0758030228480301c07420041e502286020340765001e07040800d14010001c60811118500b00078040c0e20200401c2200d01c9190410001d64400303020982129030310b80101c00341c2e24813400c244143c09200410741030402c4101801c0000003034000c82694805070840d9401600da09580a0aa854607240c10915a01c0030b00000d01c5900d841c7d02240702010700b81311a00403d002003420704c9400c11349900b8015180e000d105060302d0b041083c91640651815405074040700d400108007645150f4080302403c8850080130840014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 961941753 1250 961940503 961940519
    0xa03080a0806120d1403180601030309180e151f0f15020d020d050f070b0901230f0f07050910110c0a14120f1c18031a1b1201 55
    0x205060103c1c100c0501402d1101e208020a6203040c110380540800001c4003140c01c01450187c1940030780101400c99509503140c0c100074200c142e051040e41c1c254402805102c055140d01e000d8240b84507400c0004110a011009543d543e8441c01451120703c1c8292882442c40003404400c07000040002481c0c0c00381c80740c01c0c00148150840755041354815035001c1c020310b2603013950004140300b840001d4070300191103659103010001c50340b0610b50007504078210842448405841075000b002601035054020f000505070349200d1404550840703ea8074002c4852000492841c611000d40b64810500d00d405440c2407030400020350105088600e440c006002c200e144d495a800400110701964000c5554003150791810b404024003004403007040e40614415000a5081d41c030421180a102140e80191448200b041000030302e00d6800912034000698204c1a0001e50a162000b01c42501d40200d64006038000c0e1169102c0c81a00240401203074242401c60414070120900140c41465042c0c0283e0840354540b1000b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 961943003 1250 961941753 961941769
    0x210c1502070b0414090a0e01020f0909090607051215041122290f04121a0c030f091c09030615050a0e0703060f0f081e100b0a03080a0806 60
    0x1c065200b04010034404850a92052104541c00711034075511691280442d07000303040784480007400c543c000718400c868881440080c000c0c1c288203507941da14513642c489440ea5a68030903201140070400801401400c400c5e0b09603c9035001000c901a0740030710300450b0100b42102c1000000308031010020845034140500c858040c1c5010400c09000c6007140c0c140281c81c8903400a00c1c0e4850208443e4018110007015610281c0c2c981500310604951070700d80d00c1582e00c0807951020000c8543d122043d4188002c24441d4000500840d43c05040908582e90102e0000f007417480a000103500e88502040406003210a2040100500080d40c030781c1455480c618209041d204441c21a007401c2c10021010b00c070940b11060084102d0341c000c0251040c07901d0340d903002d40040a05412600800381000c0c00400c0e1540c0441c00c0d04c0890f542c640c1201c1c0c20461108040007090b00161100400e034001580f0f00081604e80c0d00020154040140050355007541c903510307070000b03600c03d41114010440703190030850280b4010007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 961944253 1250 961943003 961943009
    0xa03030605100f21110f0a0906170106140c0703053a0c1a01060c0b0a090b0402090604021b0d02060f040503192609010f0b0604210c150207 61
    0x2d04107000075200764050042c00c1c02c0b4500000040008166042541d0700b1780001010090941d80320703a5070010010071065a9020b035800d80041400010009911440384d040d10b20741041e4040c0c0d207000d40e409c2071800c48400c0c80750241400301000a01440c0c15001052100074015889507000f45810388980400d00d2104940401e8134803005030a00c1d080200c1101c0000030281c564052030204801c2805207040d0561491140c48034102030301400000c103069410601580d0b04500480244446a50b05400a403e8400300e1000400d45005c8201081c01130420101139a00b0040c01480907041c01d2011450318035070340c07800700da1281d00c1d4460550340f15260340500903281c0128544001c40c1103454140c5900e941d83c441d40c428003400b0402c6c201d000d00442c1c42243e82c844440f542108401c00b401d404004c01256040c240d500500d59441c2440100b40c640203441080c07803100e4040e1100b0306103490078082501c064008071003208108500d404190008082c0071f004c10242500e2004560b01d0300340074100030301e4078203260 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 961945503 1250 961944253 961944257
    0x40e15040605060901170919030e151611030304090f14130206161112010213050a0f0918020d08030f01050402090904320d0237080c0a0303060510 64
    0x890700c01d0346c0c031a1040101c3c00170b005403078070103440d001801031030420520b4040614007003048040381095445002d580413601c003150034682c04255001c00b043c0c90b118408024958214409118000071a628820f00f04905e000341503a0038265a08440010313140c170900d8000c9041e94584241c202203428004c02134106064000150785025641d0220300075210721495141b1917a07040c103199081240049a0401c4908040c045070070083d0741c281c81d0384c040d42101484019900d1041d4001c58141803d08174201150040c6409800507450910820000d101c1e01c1c002140100c000700030007016817207000308200094801e1264642e6403515001181c0c3c03681d01a00518421401000f08480540e1000c4055030090b4001e400700c1519580c90604040a40106041403964003100103601c00d603802c0490f19a103201c0c40364094804c64800851044540300d03444a080d460413000781c05209160080300c40d802d5075a031141030110310300f0b14440380301e52404808100840000c1d07150380003440b42c1c1c10228020000710fa524 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 961946753 1250 961945503 961945507
    0x12c1504050307021908010c0f0e01020a0c29040803090a06090302060d0f09050f010501060306080a0c210507180b1f08130b040605041b0f0b0708040e1504060506 71
    0xd03603201901ca100302c20003e4401d81d41d01d448006101c030f00c402e400004150410081040000060000c1e01c1010003900c001c003c036174418070080389540045442c1b2005036009010585032801c000d058020215410b400b40043d1112900c01e140246621000300007528503000210b44500c8404c080000b10415908880c0400c1251082080162a0081500c3c00c21490315008641c00da0341510000c020198490701601e0340c41135110b40c019040c810f52003070b4141c2d40b042da0140b1038030743c03148403855442d500410000c08507100d048081050700b8100d00e00a00c143c8502008000d42201c0b40c0b0384174a06070721a00400c4074603030b040b003600345100c4651240700c0d82da5034265558400e5000451007088540c0243c017140e41804022030000e002045028544040a5072054030b4100c2401e0904146000b04002c6400300d84200e0514010202d580e005a00c01045070f0482c802198100d06150004810f0780182ea0101e4083e20144800b19419036074800340d61182d40030464158003010700c0da0800c1705403029507012500421003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 961948003 1250 961946753 961946761
    0x30604061a031303210e1618020c19080d0501050d02031c051e0304050d030e25180506150903101a040c080a050702150f0603012c15 58
    0x586042c0c9034014500210a030000040d0304090384c0340340000c049496100802d609440342d1028079800000070044079000c55400b9848002c00701c0c21b104490103a450007031600001740d403c40315160028442c90b040f150995001ca03880110444040c40000d0b01101c82540c0450a58011103803882442d00600c0d046480a86401068001c01e072205c0b210a4040ea00c9400b001c009410540103208442500201c0141c406032903003e0944910540c100361002c464034002c0031421040d00344a80170384600005414050003100c03043c003031044000e0f044211001c80030800302000047d0707800c5d04a07202400101103480401d0914180d0100701041c4c5112490080c074400900000e94182c90005808510302c071110b10002d40955003d0500d20a10561180715a21034100680c2d440d40c1e650091440d0300801054405000d01e4076004001e80c6c441b06031302425030070302e000d50000500c007002c3d031580b040d00004c000c0d000180040c192002d01804100c80030340b012111840800c1502d41e4030003041181600300b5458003000840c14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 961949253 1250 961948003 961948049
    0x601051003090317070c03080f010501141803030d06030311060c0f0a020c040903030b01180308072a030302060105010f020307171b0d1205150d06020c0a0203011103060406 75
    0xc1000c040810560707a00311010825000340001c24510f0200130300c2549510f4021001020030400f180114001440310010408482410b441c1a060f240141c56155015402da1800c1d9425044040d0f1004004413200b00940e403910180020800b01e6507501d400b241090850a000d400200c582da1032410590281e010000c074038100c4801e44030b0300700d40443c803940d503651a04030407071501d4030031f00d551350380f00b40380c203c0400402d81c1583c80410b61000c20b13218400803040200000751072440070720025040c504100007410000c1c911004c194210030740240d6450000c0354440394414007800642049000d1f0780700c000103202c03c0d17800801c42d80070f41d9403c0c070055143c81d2403507880d420000c040060002d03629001181884844003090082031a00e0005000c0b00c000103a543e80040c4044802402407994501d032102040c800c10204200990303100f0040c2c041c0e4600d1010ba610703a8025400300c00c4003d182d009285800e401a9400e0040014047c103c8803482e442e410202c042004a605c01c0c1c3c00b90201444095403031001e01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 961950503 1250 961949253 961949269
    0x9160206060906010e060d48030908160201091e05040e0327040506041a01080c13030602030f0a140103120513080609150105060919050306041211060105 67
    0x4000b60703040701954031600e005a0701e8100c10326440ba40000d01046c5c50303548424503401000800b80005e03d030110040f40c00c2142c04c01d01c0c44580101c110804442c0035845100b03030b800060486c10000d00d40014030782c0f05a281c18950741c001d002d0010340021408400b0302590b900070a4a806441385a10b448091040c0900034031656950b0f101d454065516031a4100d9080c0703040c070942d046c190b00c440c03182542c0202500c8450210081c030040900c19403a0902141e82c60505102c3c510304064502003050b00100309800641c0c14820052000c040e00c10100404240101e120341c41034001c500c1031101584a0800711100c00700d05030001c1195100a280c0103003601180150b003010744c11a500a8030f20000c0350341514088840d0b208646e4011401001c641c0009a20b250000e841845168410155100200c24440120703c02c07400b0b00c82c0c141d00400501407901c85103080a6020098540f041c00e81e141c0c0340e80c440c0443e042c0441140c00b610079800d9541101e01031500100012040004080901800c0d070404000072852 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 961951753 1250 961950503 961950511
    0x80c030d1a0102071e090b030c0d150e030703080a1e0e0f120f070818060304120f0f02030405040b2209020901080c0d030e040e060108061006140406180f0f0509160206 73
    0x1407510f91f45410090745042c8110300804c0c0001d0300803c088022410001c400e004034004018a013450048054081c81c004415181d03000c0d40b5944a034000e8854490600140c24030850076035a070b085c0c82e540300c1304003180d0344603c04240c012003000d0968401e01050140c01d012801032201461101008041080c443d000115940c0c198010704464440c505e002d1461207071881c001445030404c000200b4001809451826060703540c1007550381c0c0c803400034885022101c07804188020000b517801400180214540f641005002a80103095141c4070903541030601e40b41801501440c10a5694050200942c04c00c2c1400d50f024041d544010b0030803422000201e00e4000704280f0250402007103001c014840e07035844d040f403030204003d50300302d86480d41c4901c40c59441c2c90055804210800b20130b040041e145000b0703140c0030b0b800030142d815242032038517105c01070f142d50950000b22204000b1868002c038911a10710580c81c00f030319408040d14080b90806003480b640c0200541900c00b1500b10307161040d0f207180c1c00120b003540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 961953003 1250 961951753 961951769
    0x1a030c0d020405090a060e0618010b2d1e010323130606030f110319230a0507060807030c2f0705030d1107051c080c030d1a0102071e 58
    0x11982e9001c00d285d00b403490a9000170846400d00080d911138550000e4814050109014000e20400d52280d040703080307581428486030882c040d54408c0341c034003030501e10030745481e00c0d9003204940000600300016805000d04000b1310b020b10020f0040d030003079607041c424002c5014420100070841d03010384985507804c50f40100b20011780646504c4c01c0c020070119400040086a014540c031040d0301041c60180b6501191302e10f858002d00c00c544900c61102d0710015641c2032640c1002d01c0803004100b0913003034020702900342031014180c81100c0e240700015804000000c0140b84954411740c2c00d0908142c014103640e00ca0f80d882003081036000ca082c480b44168440d02c43c02c42401416650000c0441000e1814440c0303d60009505010740700f00104501e410181d028800121344041d182c0061b201c500300300000c041060300d01c411a9401d03038001d00080210f4001e1004c038007824103c0e414a0358814411090b64a4003140144202c1d401581c200d09580401c0030034081c00c0710101c0c0ea0145007003000d4180340364285205482c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 961954253 1250 961953003 961953011
    0x31d03070b0c0a050715180b191b0c1a0916080a030e0d2402070c080d081602010209040c1e080c180406030203100501051c0201080a0903030e0d031a030c0d0204 70
    0x300c6106103920990500490440c1e01d00e4900d00760819080c10b000454450941802481c070301d880c1d209147c030481c40d5401c030030003002c412b60712078000031500c2000e1140300326036211a018144d07504408c6c3c07003003052041c0540001407c0050f0f01e00c0071000c405009900c0b00843e030b840403513007400190304406506545070059070342a21601c80340c14240c2c003e440c0401401c244034411909402d903e400f0760000c0583e240541040341c91581e4501c441a580c0080c0c90525001071803000c08501203a2401c1c030031b40c2020010344005800d00300e15400140494035185003c0f00030403091458040300c0e84100300c03642a24501810001c10504d05404030680901c15041e41c18011134081e01050004d5541d80d00081c044c1d0313000380803145c210400d07103c0d0000800ac2070044d0707841400c076007450111100401781c604a00c00d0b4182d440e000140c441c01c5801015003542c800c1103041c5a01d41403e0001c0c1d07002003099004002883d035020403146c036035141c0184889000b44401780281c11000080c1c5140d11442c2000f803c0030781c183e900007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 961955503 1250 961954253 961954283
    0x1a0609060f0117070216120809090403051308010c140a0f2001051503011103070c0611040b0a020d110a0c0524070813120f0b07031d03070b0c0a0507 65
    0x29900700100c407607040c1400340f41060010765580041d500c10290008280300b01740985030081311410042007100100000020400d044040c1800c0854907089482428080c1c01c00d940820954120003650b04404081e0f03548080b40855107900ca0030f04c02209120744905490284030b01d10050801c124149104140301208210311801070000c00c0d0010a0700900e8000c020605080420b09882d0301034002e810310a608001001c5481c1c141402200c0c060662501e8420303d1400c80d51324403001d0201d0301541d0700703001d03018800050600705480090442054683c0035000d806146035015040103004103a041c074560098028800184180c5900400d541d0210740050703141440518090101c1e0450003030882d2aa80070840404204004018090100d11030300104103542d1280004100c0403401c000241074400b0500c08503000c03514032000290440d002d03107804128600c40a2228061054094190075a948001201424080a10031450b040500d64030098504260600020424041c80740054150000d0840300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 961956753 1250 961955503 961955507
    0x913020f030f012a0206150102120a050307030f0b030a060b040e1f0e031303030f030b03060709081903050a08070219061a0a0807090b010203091306031a0609060f01 72
    0xc40e8104000301110411000036000901a000e90325004810780011288001200c4040e003100b81240080e40c0108a50b540c0e0740c00c8039030200c04441c030203419805811100c80b80407072044001d0541d1a100e8980680d281009440101242c10b54010207240500d4820028000d540208140c0901504044045002e4101d100010010b014404180105100740d038203c24500c030178083c10a00340750380040b0401c5540390405085031240700d81070440d031100039503940030703c0028090b20329103c91040f640381c0019607001c00d00110349051815076031100401c40095007040355103410030079408001c9030101c000c841c004c000e1742e0280c403a00918100c1814082d2050004050a00c00c005241510061140006c0c0074400c03420460028002d1b0f800000e012038986e5240e64041c146102190112040b1900410301a8540304007200100f400b003c1960440c00100011002d0f80d480d0103152a1a0441080006409103145000c4024002c1300d03410a40da02d0419042069951712800544e034004020313111019584804001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 961958003 1250 961956753 961956769
    0x501050f0d1d06070e010f321c1a06070203100c050702040b090603100c05120115180b1204110402160302010b2d060412150b0a05091302 60
    0x1c0d44950500d468a6850021002c0042249500d016419100785490381c0c0c8046500803640c00c900360200f681c24091841191003400c080c40e07158882c0c3e8a021881c0d0074204141d4602c062507041d54002c07140480d030144007100c1100b101285a00c0035004000000b41184109110111745041601c42c01000c02c20105548080c0036440060958000030005560f00040260664100100590259290544d840c1c40d07410803c00860080400400030900480c2500740b50f009058400001d000700102408800c0307108074801c0503d4064074040c1810108031001406c010a80204450088014441440c0403c180e0030076130300b11504503039400c40c0c1c031413940d030780d8202250001a011340d01c075001440040e80641d141080941c00400900c2075000340050031002041144c10a41e1401000c58000c0d920402020480e4000c51500542c10143c4690304240d541d180340c59506130503880c2922600015600c9507000280380c031404180320b1044482440c6c15050070301044100c00001c1810058010214800c403d40d44c070344030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 961959253 1250 961958003 961958017
    0x906030c09020f130803040e0c0702090a0902031c080901110a2703080d0b240f0c2811010503010b07140a14011d031206011b12030506010e040e070501050f 68
    0x5800030380d01d991710303000f075601e81c0140700e041d10090a01e000325032846401c904079454103400812006090306ca05d4481002444586012681449580b5000c01070041d02102001c0081c11502c07180e05910703250b46400d0940c0d441c226000020300341009008c0006400990740e64217030268040007800340441c0c01c291410050f858102800c2940041604036011f00540c0010301000003e6800076041c08070003003d1101e07200400c40350014120280008040c1d12200340240800310708110803030344c507402c07054203242590340c1d02c41074150042c280e2a6184240b004104810180903c207213486855580740c0306022a450040c01030003000c0f820719004030351002d501044030300710030b903000b01c4c1c01d0341d001d01f898821a0080c1214a030180c008004030307802d840e070035802005507010000442241d034080c3d904e000044400045019540096941c0400000040346411050459270041500c0004190170140009003044841c1401e00740301c0c40c01d1101d1102c0f20640440d40c8021920203082140d22121010356840c2680140c003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 961960503 1250 961959253 961959277
    0x50304060905010513060c0c02030309041a060a02011d07450606020d050708120c16060902010801140d06110c0f070510050f0f030601030902040f090209010906030c09020f 75
    0x40309004920100d184001c85d4544104004c201001158005542c001070000e40a54550004d02000d10a400d01703030800c0008074001e201100b580c10501c000181141c21112114005039502e090b011140c00002c68810b80750300707000000b401510325040400711349108482a0304044109802c003907201150311b00d409e1400020700070405150044911180c0010074082c804d1100510400240d000310b40e0203030045940c0d458000e4402c0d440e00010360340c80c02c400c90740500a80401141000107010400b00d51014004051203140c0218031031000e4000108a03402c180c2203a40d550120705038800c450b41c0c0b02d40481e44290f80c46400858001400020b10205004508101d150790042d2140302c0c540007030110b00c060a5520494014020382a40181159035004030709900c0170b03842041041e00e01e6682c4800103164000300514000c81c0700c0489074007007415030303074074880750762490b0b480d44d50803030452510304443c40c090503840404005051071a110400d11702c48510412505960000351103480806850486030000307008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 961961753 1250 961960503 961960511
    0xb0306060d0f05040f03081b07020d080c061509010b030c09010e011103040303090e0f0606040e1306090803070206070e0f041a0d0c0609050102160b0a20070e100e0705030406090501 79
    0x5800c0803e003014a040084000580f01f2000804d01c001241045513181c1d031440320035042005681c24408038415282054540860910580000140401c81144142992a01e5551580c102c0051003603c24042c2c104005d25101401040900450740059030b59250f824030340307210b403007440ca401a1244140c01c0c06020440c0000103000c014143c02040000440f03812620483c219038071102e1403141040d041e206294000420007040202c202c140d5001a0071141000310350080750311a030381d807008030741e448001211200c802108100c8019010f000307959004c0054181034854032402400542505201c0840350700c0f6503aa138133001d0243c410f007000d000c0c040c0701c0a04684441074140c20a074000c1c4825200d0580050307852302c804a007030351010580441d080f80d8a601c200c1107a040004070b540ca0b4100c9401d05041110f950307400a03240c41e40001d0114400840c1015100d002c0c184020300aa01d400103264108a0309448410040100c203040d03030a81c03120f582c2c40c086031a81c4440c9032040140c5140e03240a00f140d824 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 961963003 1250 961961753 961961761
    0x1d040b100f11011107030522031415040c050d080d0507051e0f180103090204110406030b0a14010503040f0b01061706040510060531030b010f0b0306060d0f05 69
    0x1681c00c44204058a0b12445401c03142400b074280c0d81e2040100301081020302418001900810107060012840f0703034905d1004c07182803003100d501d5001d613105540500c03030b9206101e1095024080c1007c46510b078006102036240680f19410803c07510711606002c2c0c00b01d09462403d00c141002076841d20194141d0038007071400c250704000c085800c402d1030380700e40d03001d04524600380350304500480d1030990f0707001056410501c50410110460000d0341109051544a0300d00000590b25445886800c90038807602d140c8803820074400500b292080e9140718045c072400c000601c070002c484040068090424a0803d0343e0b5562458200c4441d03e01900041013203201d00000714035580c00001481104800341c500c600d055540204010a8032400d541c5114806540b070b4060108a1152008280307540c03010401319110002c0049250f511090785085c4020600005030034410808600c58039401450b6801c0b644280909040d88200a40b001504291155000040000940c182c0c0c1e00418062041900304000c02d1030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 961964253 1250 961963003 961963007
    0xc30021b011104080c0d030311191803020a1e0b12091011071112030c0f010614060f0919030305070201020105070513060c06141602010605101d040b10 66
    0x15034500035034165003030808141034241180c080d64110340100c4000c2001d03c0004080c0149010350303e400740e04150311000b2000d240750040006111014240c11402104a4100340c002c128419840c140c0b01e003010ba241c070400c0582d0b41c032042d00c01502e0b000c101486114043c0781d131422103110070394400c8030600000700706184407082c40c0c1000c07031080c800b400940740d2040e1100d00980450b0b10301d1808226568080c0001c101251441c820046103480c058403400c00422104c400d1461074100e40e401c07041035071000018019001080c020340d8000e00b000001e504000b4081400510503025803d141243c1c001c1c041f900310000c1c0c0d0399400190309488070101c134401c29078407800c0040442d805504168099802d01c400300e181c040c45036003228070340d00e81c41030054000c508104044501070305000e810741e80e0649030140412a6060203040c50700840415a440d8100d42900c000a1700b51a1164041407040a003009416025a00030a266a0701180c0811803c0f1100c24080003031300410001d403407103410840d18445625955 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 961965503 1250 961964253 961964287
    0x203040317041a120907030c090b0325080c03060103020102120a09030609080c19080f070302011b030b0a0e0c03130201031b081e04111504170703150c3002 68
    0x5160801d03089032a948117940195200c03000e103c0189014690b00081043e100c0a074040002c4400c0101a101c0c06420420303810100b81d42e40d03402c0341f594582070004010207034042280401026054028240c3ca600d1a00003030745641c0411110b503401c0c0340c0021040041031040c5800c501455002c4001c0150a5103410512115000310394a081940301c3c550340807110b007030184910315103150300c05105841c24111881444254200c40421015992680300c020010700e0040c07130691001c56203550004004a032802007202c940c07003680c040f460b100000014003001e144103208481d03006180d81c03e01c4030f0000c0c0b180700480090242510003030107416949003420003580d001c0e84550040056500e405000c00c0d003d40540804401030b500109200c0d0020308400440c10404111038411403444012420250b031207180d15050801c10740400915045200e0a108100c1d511101c441c0c0d6881d40c1008001401c1c039000090404808200044860100401520199444401c8642c108070100754159103440b511100c03040c0722 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 961966753 1250 961965503 961965517
    0x4080306030a0c0305070e0601030b0a090b0d06090f03030c0813060c0e190e060109060c060f020702150301030203060f0112020904060e1b040b030a0b070804080d0c080702100c0203040317041a 84
    0x120011f102148196100e40a010100000100406805450016550014075010f80442d0300259050302c5107021421031302c1240c0710b40340140b0416040d000390f40b03801002c45a405040506210304501882180c41c41000020303480f80d80400300242d060701540d025145080e8500036a6070040c007012424801407501904001215800520811992610401075803260123b00440001440c11810100441c920782c02c9258800307000440140761000e00d40204401c02104695001d0300900000108210700b81000119403048000c0c1c042551941071608044814004450103072044200d20040360070710120341e22241c00054001c01b161a4444c00d600c4041d00562222200c1b803003035160500b0f00360f0508020840240b25a440048507803150782c0c5000986405070040c1c415568a20b003444013074960201c9103c1c110b13200e00d03907442e903455174642548004d19010940c81070b0008982041c1031941026000400c2d90244c81d80880c0c00382c1c4511603440568130078011903111400c2c0311100302d040808400200300500300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 961968003 1250 961966753 961966769
    0x3070309051c0f0516020a0803040623090f130e0706080a0c020706141c14160806040905030702091f09021c0209030f0109031805041404080306030a0c030507 69
    0x2e44000d00364162800d0700014860000326807444000d4016610581c000c003000b46030514425070f01c0f12144c0200724108940c0c0c000c5415907100080502c0141d401c070341500f00e403070020302c4502c100c10041042031680b4054000800d009100c0350703240c45195658a1300300e8080c007901d544100410081d840c84690380301c100c0d11446010481000200d84085501e000b051100c242d01e40081203100e14003038080b40c1508201205032038020b0b040c0301c00c8444900d04410040c0d00c1c3c01e07401022440126040044411000241071000800c051320722304001d151b0080a125846041101e001604612070f040c000d00b10b04c11024000d40c801c0003682000f0f1182a1290410a101da510002201864450321104102c0c8101c10904600500c03039a03d4903010b80c0140c006120003800501521440c011000d0010709640e0380f41e00882c0404c400c80c4000001600c5420600001c1c8000c89050060480d81007403101c0c0e441c00680060500c990000014400d510200306d01030000798401d19407000c4540c3c070700701240c0314882c900640031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 961969253 1250 961968003 961968013
    0x10c06090c091a0307031b0b1c18020d021903050105010b0a020c010809070b0d110a030b040b014103040302030d0c030905060f0a2d050c03040b0c0a0302040302060307030905 76
    0x100303480c003403854444810f0242c000d00900e030451700c0ea4190a00c95080c0003565084410700407070010f05801c0908070745490300ca941c0300c04c40e95042800b0700f40c5000842820890010070010b001688d2801407003c80b040e0142c40b141c2010b86801c0403000302e003541d5003000d0015800c0000000710b19405400030003c5840503400d440341c81710300500444904900f6500e014255105210900c035440016000380810910401d00140854140d40b224082d500055501e00200c1e03a00d20b0700d10740034101030294000c00442482d2158281008480c11a01c2540001c0c0c2d5820340c0501d100900c429101d905071406d4030644000003e516854203113402075803a808403c0d040e0301a0306014070980780b07501a0241c071490701c0e07000b0003818542e42ca69440e259010f50003029000100c0d201c61409252072040304002c41c1a065a01030b0342c140b01062548102030b254081d1403501028010420000414468107810390401d030813039801d5980e0120b1140c1280607010740c3c0c05c081e501941c000140103149805520500a240c41001072f54 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 961970503 1250 961969253 961969271
    0x90e0f0105010501050f0d0f0212090a260a0c060e0a081305040b060901083102010809060601020a0f050a08030109021206090f0601051308030406171b0711010c06090c09 74
    0x100c0034094100c4048204100f80075188284166400c2303d40d566050f14070041c04e21a81c606900345041d01564201501d40000c0703100414400004503603110703684500203072907240c040f551901c98a40300341d10102e000c0000c0703450345104001054020300030030900c031011514094068200624640d0104010100010901c000010281814010103130b136140000c0265040440040c0150303040c41f0002c14005002109147c0c0716078400b081c00019180407403004494800150510014002c04800341410700700e9808082040001ea078001005c1c0003403030348089581403600152070114035043e100340c0000d00100b008070010031281c200381d0192605452040a074036180d01d030201442280282541c5c580d1400b011000090f0040d4019401020319841810140030702c40e9a402089040d500203410400000355050340c16180d01c4d11004219030031180134490140e02c150703142c00410080c403544200500034003224a640226a002e00c1d183d182864112000340322161207440c0c1030b20090080c4c001c01c401d1915043c695 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 961971753 1250 961970503 961970507
    0x506030f07060e06090f0a090f0b040b09072006160f0f020c060f0f0304060906060816060f1205090a050601080c0604030b040c1205160b03091f06090e0f0105010501 72
    0x5041118120385902c0c0543c0c07040010700c4429401a070a050f004051400d030030180f521a81144002418078406c00505544045112025508241c0c842440341d4100818000d80d07a5480200940203045410500203001800801c1c0c0241c541200700240140200313410054541e909040d648c088111582d69100910312810040e1120500c0385001401640044a000450309007070300208020410726180e00c1c00e191250003840d034160310884046842944640c1084200006070243c400a09590b00141481070700c50241404c85940c948100800c0110104100203401d0107410300e81d07098817031071205000c2e616201592603035442c00074004030780501c00d0710000174031000e010032000c07803038400103085918051550b140c40f200c0c04c01c050300a031069187c0000c0010001e08100c3c10010b0148210007410202c85580103100000100d540940c903041810000c00402800100e02a258151800701c00c14100c00300b040b1020081c0107981080c4607180c507024658078141000500141d8220048000784907580c1c0756001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 961973003 1250 961971753 961971763
    0x111072c0f0a051015091406040b0331050d080c0405010903080903030c03030711061b030402060c01060305030a120f0902031509030d0f0c020f2b0909050103060506030f 74
    0x1100d00064102021442601141d00044d07009400603000c00d80e0a61580010104512100070342d0001c10000722081010012642d40e110b0700e80f070219181824145815080c0c90b8521004000e142c0c4c0f1a0000c0202c0701180000c0443c0f02104138100d0001d038020610b02e8076030750365580b03244001c4c0410020400502c680301c40c0f07011281961010303076584040a165a0707907108580c00041c1c40072382c140024400840c6488007000554407071aa0f03903680f0081030340704051031410944060322a640301d2481c81c00c001c007600d00d01c8003160b40050781541e51641c2c0300303545420507006107001c4d00014580e01000a0707500d02c3c5a8072110980354101401406c014610003000013108442040304000d4040e0402400700c001030251520150f03006894409a9240a144401103030880da610b14000e0301842d40c403500341910582c10810641101c1e81400140080c00469040c4123aa0103884041650400004101c48426118176240300040002640a0207196100c0c900030707000d480d0071a0b1082c00703446601010005c988001032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 961974253 1250 961973003 961973011
    0x110906030c01181a0a170c1c2901020c0909060402040e072705070f2c040f021206030304180513020d0b0108101103150111072c 56
    0x1d15003100e0304001555158040b100e105440035503984009085200c4008042e65009002c0c2415a90100b001c009400300761201000c1400410100410135482d46000c21144040355842d01c1701c2c10408107a80400181108950562019074096100708200c00c4803c810b541c0040300360203503481c06085006100c0075030300071243c0032465804040800c01608159014002406a50066031152911040c07a04c5038981c009070540d10021845090802640c9036110725604204a4a001c0707c20305070a42000b007107040c4901604180701c16001051034002601d00d1403032132070000a40288281c491000440703000b5001030181158203c00072000941610b000300480e41a500d020001c0001100d0300e56004d001404001c00240000360f031524444c000d661030520119803d4440d1031000425130500f0160f605202d020f070a1110000e040c800f01d98900310003c8190fa0f402501e41d8005900d032107c44c00100c1d051488003406501a005802c0045000c05880d07104042b581c044c005140072001030600e0350000084112 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 961975503 1250 961974253 961974259
    0x31107030516020409050d0c02090109060503100f180b0414010c080c0c0c1810060203091e0a050405010f0e070206040206070303090c030c08011a0301060302010f2003070807110906 79
    0x450500e5a1542c400c8941000d400903000080e540001d585031340c901640b15078914040b41e1110780c0c030421464072441450240c80740b10014844a4034020209a07258850300c8142003050700ca501c2035024100541c0000d03994403ea002d1032010300490b003880318410006440540e48184141d400b2580210140149108000e0a6942c04250391391b0f00841803841e0400c440e000414041c1c480d400040c1e903101551640a40c07245444510b80741489500710510540a6000000f590018030000c01a81c0d0b440000c60322600400611001212150340040e0041c000b94202a5000c0c3c034010012840041203040e020940e44044103040403030f1581070301641d0f105c00c1120300a5202c8010410030b00000d100b50008452a44181c0152494640742d960b2031a0000c620340203132180d0780d500d000207000300c8404c24014020001c240c008000d09030443e00000c0c2114054415042400912000141004801d5440c101800603100c1a02d40b038140c2450440d040c0e5101c41c109a0303154540d0007100783c05103017801d95280240c10007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 961976753 1250 961975503 961975507
    0x501151814010b0720060f19030c0e120f0105010b1e04140d02041d0d03062106020a05040b07030309030801090506090f07020f1603020a0f0e1b0f0c0d0311070305 71
    0x142d40b401d810000141c2545c04103844040d4800003502c5040281c551000c241010507107c0715529034010000c0b441800700010141030408003000e0503003040d0303148410a010303204207078000f017032014131460007200b001c1d0703c0c5566103802b00010308900c608014140c081a40c500e20107500c0d22030800a2960b0255004100308030744e03204002c0c4807500d014242a1042c9101410100e5081445440f100b003440a00c41d08200d10303008a0722070a5071550511501c00500341d80c01110401903560100480ba01200c64401026140c1c00150000114081c8098130004c09814060965569445c13030001c0240c400c0c0c0300c2c21000305484400101d40160700c0d02505106050103400c0c80c84a940341c41c102c503064000075007190103601651030f244120302c0042c414604403403040d04403011001d15500c180106041954400e180021401d0b400b40701654401885a0304690b01d8042401e02c298100c07450126441803a10516500c400041c0c40d8a011700013103806861003140351010031284000c444c1d00c081511410500030001142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 961978003 1250 961976753 961976767
    0x7080a4a03040e07030c031b08010905060102011e02070609080f0a0801090c1b0201200705030d1404090b13090b0702011b0e010c1406070206090f03090108130501151814010b 76
    0x120346d0194002c0c10040c90081001c0e0710014404900300d5020340030744005424280148a01130180c0292a0814030130310003049034405101ca02c0300590013000341d410712550001440014090306800c20b140715904011450355071a000d0f04048036907445451090b012a0781000000b45164072807040f19200300084c0c07202000c140d8560503e044071420540101d050050304804c003003007a500101c0d545030304a182c0c002400e0850910342010300c0c00080042c00802c0080e0b191010403400450002c0d60304507401400c01040501d080e0740003840016201202c41121032501b480f107020b0141c5601d466024104a07002001088000d1324100407800120100c80080b4100001101103944078124003080c0c2801002d001c080301602c500707117500307004096502900503805a4140200301d00140200a50303d042c0d4002145045510b0f0700181403105d000303110350040401e030821001440310039009850020303c40d0700c1107205c45031030300c4c0b00313001050414013060051807070264180680404100c1b003906840c48014420b00340a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 961979253 1250 961978003 961978007
    0x6011205060f4c050102010516052a120d051515090d020a0b03010f17100203090a020901030507080c150313030c1505010501120507080a4a03040e07 65
    0x514164800d9031000070703051001d4612101034070543d100c2c0d03800c04000f411501e401c00090a41d100a4407640d03020940a0080700c02e940c101007210000c000c03009041c401e081c4c01c0e084e04a48001030441c48103486c040e601b0200f503103441c0c034002414030911800d0104042d4503540031001c00203000b410655003020030011042c01d00e80b0302c2000382100d488002c100380b25401196021444001080d401440d64444c04001886540210420540034200c5252503000d1010200d681c0d540d80c2401c0852054801e90010103d800ca000034016000b201e500a8038103852541e40345095035032510303103100f424114002d8a00b14101c1d850305050801d0002c6c0700250450442e00d0b14862070030b80c1c14411030110140510300d40b04600007014008020765031840c603000044c15625140c00980038900414883e10302a1401c030400c80195000356003540c0003481e98070002541c038051010b241c03810038504020f0040b07003101400c9200d0114284218003400e08401d8181e141002c0e04007020b6501c1c0030701e010303031500d1079424000114814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 961980503 1250 961979253 961979311
    0x306010e0637020705060f040509102c22061a0d0c0501031b050a0305041b0306050405120a081503032107022a01030203040804030506011205060f 64
    0x500c05402030098044520b50342c1c120b2608401420032018600100d9981e0140c0511030500186802e45143e440c003402100140750741d10a0707018981c81551b10a0205e000c0c0303a60f21240e01c1c00b401c0ca900b98111500e003034081c510b100d81b040c01c9107500c101402c0400210f02c03422041c04c41c0e03501050186403040b0341140b81c0d619005881486441c0c14103200c005010384040d612044203100780c07030141c210301d4580e82c10480010251000d0046808841108002110955902c00211a5202c0051a0004041e180e62070440700f1030408164500100000d5030020041c060356500c0135014034400c6c2d0466400200c6581c030011039014007194040031903650300000d4840c4180c05080a04000c004007500d1802560090701075690b09461007000c0c0c03203610751b03041000c8180c04010100c6500742c0f030360300e03194240410300c06136000c0136180840320704054010020030108800c0708184c40145070700406542c601e40e164014200181850070040d281880307210045808680c40d41b103640e000784050301d81c0401ca0000c5040b00005a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 961981753 1250 961980503 961980517
    0x1006140d060e0a0803271c080604091212050f0903250206030a06060e03070b160204020702060309010903081b09010c11041104261009050f01020f19050306010e06 71
    0x3a0203001c02031000a0610030085100e4035a141406c80400e10382d0003100b95012840c00000780942c400c000036a908000c40d401120003020b6803811001a5890f0004100a0035920388001d1024441c00504018143c00081c400360041e85803c040140c0d42d00c4e201c9403102204141d4554500360410800888800c10300c1508024005145500032510012517000c25110b80c001c8424540040c1d0341c00083c00001e500205000350107070704a00406446040400d02c5045100f00000d8001c84801c0d60703088021516941c050f240d40c181c00500c0f69460b440d00d261400d01030410480201e00044090002400d03411001014030a81c180c1030041d1801c00d1212001034801350050142070f42c145000f0920400300d0342c2c440c06004102d404404105440e40d2420250364041d40746800010b644010303050b00c1c409852800500104001e4035120f010911846d0f9040031410f0980c0403507100740c4e03940001914041c81c404000105020680000600041d08400b8021540e0b80000d440041c0010ba01901c04005407030600d0140c528 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 961983003 1250 961981753 961981781
    0x5060907214103090a0603150e1302060304050705100c03080103020f0f03010f0f050a090b061314070504050f090903090d0804050303071109100302030a14070f081006140d06 76
    0x65001e0450251100c810342c409204964000141002c82d420500d007094001e10017801d00f0702c010641492031803d040c4c1d040c024036081c00410750006c1e081c288255992004150042c18260356800c0500f005626131001740682c0c1d002e5525203100410352445141c0e401c1c50340350540c0e9080301030390035903081080b8598080d10150340082c041c0c0d10201309980030700c1801101a60b18038000780c01120801c0340e009880004100d0240c02d0b142903c5c200102d21414080e90707205004944203001c1c1d5100f8480d46000b08800040410550b0b1400d0400c03107455001801002039481c05c80d05000a050507000b001140030044400348800d420a00c19104941407544e0815213082c4940c0c07580c1d081a4603080807074516000303e042918002c1c4609442605420646091900700c68240ca00300d200a0a540102e541c07011110b000820071040300e4500030303d880042c07244102400b800d0210016040c0c0d1019034a03079440a01c1d0cd9107030b0851801100150f0300464034100d4021000c00b4206144a03112a2a0140281050007076801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 961984253 1250 961983003 961983083
    0x90f1002100b031006060521060312070501091a0403180b0f070c15030213050603010f0b071505040b060907020c0f0f061c021309060806220506090721 66
    0x241000344d601071000984410341c0c906484000542c1d034810022078516984115900c2e4005111050300e002c1011340380300d801e44482c585d071038100e86085801070402d00b001611a07032403542c100382d000d0700310180540206d0203036440c81c6418015200081e4078140d540726103059810704120b13041c82c01d40590048d003110f83c0207400451129075a2060a01004440d410070800654000b403444010503450032241c1c00b03040280c4002d81198107040c0f004450142c903018021400d100418a44104003075000010240f080500c1d0500980c20301d40341c80703a8410000d49071244035010381c2d030024411600c0021904503606000f007010b120244010300b03100d600100415580d0704203030f0404c690030111a060101c070080139294040107a07109015801c8446507219a044112041e042413030030001d02000041c00e5400c84501058501e00402c0300700c10401d41c10b404d01e00141640501c10410495000110f855421120313081e60f000b01b45000c4408468a640c0a1007004142a80c0c0f86605100d405007042c410529400da003240803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 961985503 1250 961984253 961984273
    0x10c0f0c030c0c08030d060909080f0f040b160b060607210201020f0f0316020703080720030a141e0312041e060906270f02061905090f1002100b03 64
    0x42403c4483d4010103050751000030b045814032198800c00009048024080115244075600c0b80710611035008803000c7c014000c64021509040c0340d040341c00501b4aa4038a9aa032040480c0012600038401ca083e603050b1a241c0c00038003241040f80844808030703800311b80c500c95240c03c030646954001c80091a5070842d9400e0040c041c44500a20041800282d10308000f82c0f6840c0044000c1c01d102c8003802c5003070441d04100c0f000c00006640c0d2090360b4040382d01c0803540c43d811a04d00d652651072607107101710a41c5841044440c405021a20f16036018460b5880d080c2e6850040c00c03d40382c1c00e601349043d9248000d510800c005c0d00c11090b00d50800b03401c688907041500e8500e910280f07808060300e0f04513080d605955500c00e08801c000541c031a81801e80780b00324240c0005161940d01a450011400029018078440d02c1d54804542c4d0311811600c0814030415503046c0750048000082035904040c074144e0080d440320707005244614000071070a401a0856001740034a50203109110050100004000e8141c85440c40c42 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 961986753 1250 961985503 961985513
    0x20f040e030f04030c080d1806030906020d09030c06060b09030318030f01060308030a0e06060603180a12030e01060902030c271c060b0a152f0a03020f010c0f0c030c 72
    0x603c000c50041c03240135800b03810701442c3c5081c86c100c2d9031030b90280916040401d10a4000810043c05c46100d800c0004003040681040030282c0704c3c69000030407083c6007840c400c0c00c140d0000058a905800740700200000c5031070702d2840d2254481c0449055045d0b02c280300650044118800d140d41e09100079080c0c40c08501c01c0001103081d104141c108680840c03021040010542c402e00c21203031949245002000c0c1c0d81880d00204410b480050712000d80c0c000e40c58140f0385080da0030811820744c00d070b02c0005110600c00d214030040040403602c100f6100b41d420860001181c02181c020759005081d410b901d03900d407004d0b8403e020000484009500d001544004141d41950f4462084001c03403041042c00c04003002d914540070084540050f001c44c071a0f17007060810f010100011076900070f800850b081c1142c86002c005982ea001c46200144120000d003001c1d0403004a071404100a420503120b03408030b032602d42d46d0441c1a0b090b90000d12150b000a0240082c2c15549440b95060300001402410060b040c1c040139110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 961988003 1250 961986753 961986757
    0x12010e1f090b1f0c120905010c0f05031b07140609031b12030705010b0f10171f080a030809060403050304062711010f090501020717160806150607020f040e030f 70
    0x2000c3c0891040031052061204501c000b4400410b10310340510320300e040c10006008034a1440c030141503440b42c0c00c140c604111040085545134508040511a4905859441907507024140602c1d83d08000195400405081c46401d54164040040203489001144031000d1400d1800600f9a903011501c4c26002030400c10600092405038001c030000704801c4c110b1018071801c0000040490300403201c000c4c40742000c503805407005181d411031f4030440f01031f510703042300d1022010480c1c00c9641007004a00400169107000040d4030306420b00c25180c0c2221aa10800c00c3c81d1201d50486002e40407500820000300011403e0b403200c4829805c90b800106140003410001c100380d10050f50486142c00b05a419121541e000855511101840e181c801c404a0030080001e40340c5203584941a50390b5a5280c00d95400c03c0e040c4002c01107802241215007510350381d44070b150b80c1e43d00141c6010300c1410040fa00716059003440411140b07083e03009040311710424040010311005107165104103100d400144800b010b13040302100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 961989253 1250 961988003 961988059
    0x60f06170c12070f230304120504080319030906021204060f050c0703080a061d45070e010b0a020f1615021212010e1f090b 54
    0x14580c503034000110034100354210058103080300c1810611240c0340c16103003804526804095407808007980a640302060f502071804c61440501008000c04089500c2c1ca034a024510030f034015115888000da04020507903880c4690700074500c107a001040403206140c1001031086110350280381c005462030058403807604076009880c2c21440024980140804c5c82001c1c02116042c444021042089003032135015910103101d02d400040521200c40002010749a103a4041d070000c245e0081e1984109608030a00e00041004682519a01111207898200411b00300c407000c4103a078022000240c905040c0070303c0218850541d202d00c0c81449000d0002c01c1620400b401c0500901440c080c1c1900d500070250040e007050b51486139001e2541c815500744140c2c0800c464014121440c04910240e18500302d14200e0274000640709120140c0f40016201c500002044e014a040b01c0100d1042003450700d45100c00103984203003040114100c1c58243c0148501c403569030001414000c01804440399024032100c076041e00500203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 961990503 1250 961989253 961989257
    0x711012d0c110f0f01111002161407030f03050d0e0d1d0117040803190c05040501110607020615030a0204060b0a0905061201030b0a020c0102030906090d021b090a060f06 74
    0x1081c04120448400011022040340d102d001500d080000c502000c1120501320704210781485440c846010500034015500c2c0154801c4d540c0b4107010030349540300c840c00c8804885c1c40c114061160202071001c00c42000ba00d901c00b02142c824031b80345e10100c80c181c00c05250540c2036a5213645001c841901000b08048941c61502c81142c01417001c43d0305040002d10031105418021490740640c0303207001100d40242e1040c0e10483e4075032261291080c660b0301c001c020302ca410b82d151501c9440700f00140c2000241003150000d981d20380031a03042c0403c00340c4034003068880300c0142e404600401c8420280b0040d00042d11006030840c5d80b201c41580021f010740d465540102c0104400003102e170b188035440000303480506016a0361a240c03400400a655840c94140b01c050300c130f281c00001085251080d501280c18001c040c900035500d90138a07055582e115031003622410003900c00d2241c03850341140041009041140100e004110740d040749001d003c21000b00800b0101c680e80d5849010a109d0052204074002d45040e03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 961991753 1250 961990503 961990517
    0xf09090703170921070e010f0e0a0b060a08040219030303091209060903030f0309021810242106080d03111305010c0c08010f020702090c0711012d 64
    0x142400010540405680409010b0411461555885090344ea00654880841103140000e4880304541401125007140448000c00000002c411409810403810346101d0801ca40107a118038118000303e41003801c1480d08140c00748540d0385c0303250160300d10642c004d0011b0981807882d103c01c0031181c0c003d81c16400880c0400c2d0303900040d4007400a61a40c142412200341044d4015504002c400f8064120911005081140403003000c1c9015200c0e41000d50f003680d000d0561a001e1802010403608058112030840103242841d5000500200d10015800d0401111058944c00c5a0340041225000007000003807203510b6400c00554946285441102c0090240501a1082100501c401815201240000c20340c3c1c1506001d2060705070042c5040000b00d41017407c001406900c01c1c5410358440300f1a43c4900ca2a510781101000c510b42c6503002451450f101701d545004035a42c41d0345031030700c40c020b00d0b0001c1e01e8206409900b10b03580d405010840c042e51064000c0d0000710b030710070404510880c00c5003403a200252130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 961993003 1250 961991753 961991759
    0x1020f0c01180b060d03020f030301121a01050f0d020409020312040e0709051516050d11010b060301031505190c0306050a0501020f06150d080409141807060c020f090907 74
    0x10a2142c4510050038280200b0000c4140e1215031808030041d010070711400c2c03851014000c050007040000b8240050100703407a161343e950281e080d2241010746041d10711429001e0307828000121240a24103071000240750b01d002c04191018043d00300c20316501280c00ca030382c40b4a0b22016076401c210442c210702070110007554803170801400003841d980c00781100c41402200c40c418003840e95040c6001c10300a081c0c403c0e03d52940d0b003001d4622200103022202409030f004408ca0010610307403250b074900001750400028850b0085100c203100a51000b44005803102c0601121541103081c0d54001c00e401c09100c10103084204081c605520440341d0150f00c4002196480200300518103040030400020030090028003440c0181d8001552120402002c001000001ea00d11201e00d94690003490030707039600803002e80d40300c0d6140c850301c1d8000c0128000303c402d0005082c000800f1096104a00c0e00c3c007c00a5018010f05840c2c59410f50f00c80c07052000490b4048500703000615141c941d00e106c10700c242e118200500d0340902d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 961994253 1250 961993003 961993027
    0x1a0904050a0501141c0b10180f0e071a03060301111303050c010305060f04050403140a09080c041104060f03290405070905101b0c0e0711010209090a050a090501020f 72
    0x406403d04d4001c00c2d101c2858030350b404409080b8080c07190451016425507032000307001d0504622503000a040101172042d104ea1200c0b03181e1003a400c1d000110f80400c1007034a50075009550701040d22462000d008005003241d05402444043d503040080540003107802e00c0390fa00c40382810f404c0f05a10158456085130100b003800070400032016500c0d0282000c02c428140301c0003180b010040c001003280599180d901113020980b0610802e6800000511080d85036040c0480050011102d0710800f68035101c2c42008070703d10320f041e100d10f07450050b0864480d07103040e10740310058817828062030140c001e0581c1d0340e030890252860107402200c43c50440f031400e00d002e03000310200b00481c0c2002d801801042201c400c28030031512001d10042695a240c20303c450948100a00464010a90903000700121005400052003042c000040d41c0940c055844111000911742c40072400c0740508070806a02c03522a6003c600000b14951000d50041b110130400700e65174982c0e483d12070982e8880410719500325400507201c0c55003e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 961995503 1250 961994253 961994279
    0x40509121317031c0b060304062309370b0714070c0509070c050c220608010903020f16061d030106061812080414060c070605040302120607091a0904050a0501 69
    0x1c0d2040300405c9921181404540b403400020401021150b550342960b0036490303840c20701c20441003501030f220003030702c2c05511040e100c00341210002d41142c1c074106231010f40c1c2e10114800e0001036103a000c44040308080d0311011810600035203070805112070280c60310303020a6004018144c20740034640d0f40105034504400d02a030b20000422060420a5041d1060001100811a0090004120341c0e00e400c2a0522409465082407210b135602e08038038028000500d40810b401c060005406a001d0350f07019a185105240c54000304011040d54000c00c450a02c0300900915403405c0000080c0000e0003003003100d4020908540daa900407601040982001070410b44104800b01c0203003071208d0403601c9072030440d950201c1750301036409645000350462040c60b441c1d0f10f60b05d05541e005940442243c0c0815a14200541164441e000031b90007104600c1c2c000242030b43c005a06401010b05950f00e01e034007860b10130424048070301c000b1640c0c0f44100400074003d069580d4091140a080c41000c002040d51404200c01d50388 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 961996753 1250 961995503 961995547
    0x2130503010e070306021317060103030e01080f070f2c030f011a0f060c0715031a0d032d110c040e0a1403090d050f010b04050912131703 60
    0x9a051140c00c1c420070b440410340c001220f5118a016841705e08960340c4414035080c58001c04000002129034010b000b200051807070403a8002c1d100c0e8034041404000444241e20300311404c0e401c000b1103d02040c0c00c1841183c08510b180c034503151107000880184000503c02140040030404c0400701c0c19a041640303400e01604041c4856940200302d42042d80740c210740300391004541d003442200d843c030000c0f506031146802c0b142c2400045003581c400b10f884042824504440f00801c00c0082c4c901602c01400d41c0e114115002803a07401041c480080880d070790202c43c0e400507005542c040700002070041030300a551003540c0a4145d82a106c054a0000c1d00c10701c0e0346805602c954241c410f50803c90311607203a0030b0100e561070415401105100e41c008040c110b61b4610b02c12001341c6070308449c1e2003266600b484030202e0031112000151000b405240b44401c00c21003a140e054032818402d410944222129801040003000710744401400b504110344c3d17074081c501c41c030118044650991f40001603501208142071000880f4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 961998003 1250 961996753 961996759
    0x804080d110c03070c0605130e06030c03070602062d18011409010e0f0714100201140103081c0b0102033f092404081c0504030915090b070b040c03050f01021305 70
    0x40c0304024114500c1c1740c8c0544924a500e80e15100402c0c00f54500340505910184040d0480310380c640e071504025030f680400c0740c0407420b080d21058a003070618034504040c03408041c6404c444580b52100b16a030b240c880200d0b0b0311107400d99a60354540841f8400741c5d440c64415100c800002400070f01282c00ba40c1094281b4007001030503000780000f0b0140b03140c20408844501e0041e94012074000c007010007a070040c2a21a588014241d05c04000010000c5c031100600c0034210b40c509d0701c81c440c002c151400003030ba024140201d02580092001030351b01e50321f80c0311110301080e11400d00c20004490325000b40c071100720303105c441d104010400d080001e03404040140240c00c4210b0000b581c049030703411080040001d00500300034640100014030070420107410f540140342c50b02503402001103013450315020381160380603c03543c01901c08869114042e24014006441220501c01029240903003035600c003412688000c008652000902c1404004120304101c2e601600c0341c0000010b80d1883d1048403048a06850740c80030748 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 961999253 1250 961998003 961998007
    0xa0509010609140f041403030a15090209150d061805250e0f060723070510021002090301020c2527050c0d0f0218100804080d110c03070c0605 62
    0x441c0359003d6245582c48244044d0099aa440d00c0c079050450010004612445110103c20300c080642d580e0b0005c2d40c04201d0180014030740e40d8441000c2c05034000c0b842c0301ea900c004101080d110002c4944010035480f0329484001030000c0e2143c0c1d1402c90440d011450070405540d404c10000c0d9003800c140384000d40d48840c0030f81055100708030f800501c0d00b40d041c484a40100030b501e80040050700d0700803d40704c490741d014000a05403000e42c850b07150004403d540780d070703854821720400241e13a0400c1404110581003681c0941030a005012800e00030358400d41e00d442e05036500300b084d80388140041c4401c402155120070075030a02d1001101c90403d51503143c0018a00420001301880300560044c001c4505240303081c8007042690b102501e500c07403801000401280305090001011090000e5401059018010403541107082c001000740300090000900202c0811000030114021619040181c114501003070b4000c1494011000d0040040c1c0140c140da038041c0d0b2010500508010306095035402400c06458094 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 962000503 1250 961999253 961999271
    0x20114010e0f0c091c0f031211180607120f03150e0708070210150518130f0f05030f0702040f0e0d050a02070b0307080f0a0c020703030e0609090a0509010609 69
    0x20090701d4041c01200c00100300144060040d101c1050300c01c0c5c1c02203034151565082e981030901c0013120304002e004a0006518005840000c440b0344a4864080034022046082c030452482c0d0f01c1072200e200d41500da203c2010f01040d0009207004611000100190703540380d00070003030301c0000b4007034518550141000012004c0c09116401d442c1000e5940009180750100140e2200501a418111030840c881e030250b0810600384603090f008600c12080303c0b001c1d540800c14081c6405001802c25090f1103981514030000c1d4544045040e42c0120201140643c0247c2c0750102030765583c615540c03240c803098025040202c3e5000c2580740c40d101ea5140143d18070020312079280d40c00b040640f25a2071102100034440c003c24442c00e840d108021000103051300c0c0b04071550700d0400c03250290817003030225022803901030b00d01c000800b04c4800e80030340c007020704013034000709007250444d5015507610b00b5400c00c540e04414280950030842d0742c0d80d900349e8045d901d1241d000030b003410002840d900f036460b15000303400001c3c2085660 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 962001753 1250 962000503 962000521
    0x90a1208030a020f16030503150414070c0317010602060a11070f03080a11030114030c0d0b01050103021c020703030c020706210504020f09042a08030d0c110d020114010e 74
    0x741c1e484030351120010395484260403482105d000b103549004c5091004941c6008054111000b10b00440140c0f1a840c510f41012080105a40c5011100c0340403442a101160305c640c0907004120f28a42300c0d04091101480340c0c2025900800e00f64450b00050b4459010300140703403014852105c4004121443c94600030490b02d072240001015400103040100f01e2000a102c004664040321300ca082d908800e50740d0356510902d1404105c1c805104600c01c0c05400e5952505203441081c0c284069170000714012941e10b800e0054000b50407150741e01280c800741e1040443c03070f1030051000344145842610001482c105581009182028a80000c401c0c801103a007017164150b4041103280081915110108095540b440814041c851040c2d403960030052100620041020324854458500c10a0080d02c00e00d4400081a1248609a20a540d241c5e0000c104070040c0d1300003034000102c0c6ca1242c0c1045900b4902180001c0c0c504003d000311200140d550311416100c0244180086004004100d0981820b0518003a4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 962003003 1250 962001753 962001757
    0x170c120c1c0f1d040209030a0303020d05280504080403140f06010e0c0403080c03220314010506010e010309020d05060106120b031b09071812060b0909190f080c03090a1208 75
    0xf02940c8010034201e20003690791a01201c4407150301609031b40d643c1c0160301d0003130f002e5000b1540c1840720b982818005445088240150320515002030080d61b0400c451002d00001010054416145810304110110201c2e12182d2003401118821005000450301e40110908080068215883c1c1a034100107000d8004c884500792810360380c01050b580d94480300020118990f1107502c8024440409201d0b205501d0741106000b0800c80780242d9201141040e03a00c4068200c4004864280c042a94a1808001940f20b503000e1104c1d02d05c09409220400c4d240d80381c0b14a4640c0036030082002958800850624100501808807034031400c1c0c000f4001d4207940c68242c405598604420b0380905540d400103040580704d049030300c207000341c6155156605601c070f89103000b050094641c155140b50402c444155a410014445407140f41180d004e000a6070b041c0403280c00b41411764009440f00c0000e41d03906004103442d1001029131499003001036940300411014010342002036800003514001141c945808103c0c2441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 962004253 1250 962003003 962003027
    0x405041d0606060f070c0f0513050103051b03010b0a14030c0a0b030f1009050a0f060e07090b0d0617070303020c0d03020604080904091a0a05010b07170c120c1c0f 71
    0x8010781c03913100c14100e6110780d00030300f10003400d5210000070010b11000415050f00c2552029a91241458000c654600549100f80300c010f040d42e0282841c250107070100310b0001c100d000e000740080b90408000c1d00003411022542c00442c10910991004010351030204480d441c82c40742560f003080e8040c40c200b5801c1d442d010050054600d11051030000d00c0d00c400d07800e1b080c4090400940b04000c0e034142924204010f0040c1c07180209020724040707002c07449010742511180300d1862740c0d0f1060b680504000141c10f4030780000c00c003510b0705d91700c0d4030010400111301d0003140b16010480004080680c95828000d1400c01c081d084140a01860803a00d40802d0740452416030103a007103011299103181c11808034000341603004018240383c0e0705002d607a41c02d50001d2030480c000c034518501032090f81d0b291421100503224801e002002c5c050404460044000ca420241100c0300002c002d4a4070381520f441640c015600c6040790900c3c0ba000240b040d41622015000c4151507085886d00007000b0300074810203007100b12504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 962005503 1250 962004253 962004259
    0x10080126060f1519030501060e060f10120911090a05040503030a021305090109020315190e0a060e010f08120a050a18031b0f05041103010b0f1e0405041d0606 69
    0x10380024840140040b582d41c10b0000540541c410140011844c4090103207800111825401c0c8200054091140c3d40482c0c082c060041c820b11040e8031460811220301003820009092080c480d081c1d0f6003240441c8100b011107402807007046c031004124010004402001050880c1003480d0000748804140e001064947c0801c0c04079006079a80011810ba6213401d01991010341d0004000d400840c16007003035000707103003e01d080c200100760304e12864080010742001d040a001212003408000c004103040c0314206508510b8032000000d455031955104c98516000741c01c00d401200c03012004001c40c1c0740c1004080c9a40c00e0100c000703400e02d0701c1480002c0252056082d01000c01409030202e182c500c444540030002540d00107046903070400c0c4c1102440c0c44000600c00d081c0b01484075400010281414096411500064100703185103a00301410640d080e001503d401e01c0542050241e0a004041031007040c403100050a8840d880300c0c1b801c001c20080d190074900ba003141d24000c1c186103c100400041041e0421021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 962006753 1250 962005503 962005531
    0x30e0a0803010b0f191e08010b1e040503030f0417070509060904061404060606090f0f0902160f210e21030903060a06050a0503120a0e01030b1008012606 67
    0x1050802c04640204a50b201c17032103200c00b24003182943c0106000350600d0000c010326007020390071002600d000708240310704203103220b0400c03248401003010140c003448081500c6250307042507141c5000c28590b400008aa00c0c00324070000b800d003c8050f00549540950219200603c02d02e410600411900c82001e01488d0007000304001042c100a21a0081d400d10032810540805d14501404c00402800307c6200380d20110b89000004103c1441112a4005a40318460b2440b260351420380c154000390300c0300180c0720704140c803180840d0000b5141d440001d4014060200c1c2031041303107100100a90f00c1201003088081c4099001c681003591a0304400703104a07504c44d50000040c0c0c3c4442c5140e400c40c421121519418040c0d90100220204164821030a03984250b41e00c80301140c444041c03580c1c0d140c8014140c01128414000356001c14410120406e080c03038103140119180042401140c0346c085142c41c400d01003580200140400784d19102545c0544031540020f4040c1c4100010071390720303000c0203442c4282949207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 962008003 1250 962006753 962006767
    0x150f10121104051509010b09151b03030f07170601020d0e152d0304020a03120509060d052e06080c07050601030b0405010b0402090108060f0a17010c030e0a0803010b 72
    0x988001c5054568064024025480c2650151041c030030010b140e58840d0340301c0b00001c2030199052041e1200010b003c5c0c03945090422840041202c0e03040344003408500c50410310f4071b040c600c805001460103034840c24511013040c00c0070200a860b10244580720001003910404012890380e00058402850083c3c0c24000505400301020895080c081d0343ca038009013000240900034803044062aa500c106100c0342c0c00d4140550344020b0b9a80d110995020350711410100013400815600a02c603c1d6991060608500c2c22f40f60748040703807268200448a9007956691020030015058a81022810608840c21000900c400e1aa40462404a40140810040c00e0f50010325254402d0b8121407405410070111802580d5a15002600c408102d800305d60950a020f51070505061a00075680040016120000307280e07507100601080030490148190f014401c10350010740300d000480c11000440c01100080703003040845030042d0540703e00034456111a4000c80707440010400402c1545c1c1524941101c076551303512 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 962009253 1250 962008003 962008013
    0xf03030e010e240c07021f02010e011107060b030d050a120e100b0114031005010806011b201f030504150c12050109090203071a0c0f150f1012 62
    0x40301e154100c2180c8102a60b071946406040803428903481000b000c3e02140ea5035181c105203e0148110080d008500140b016042c29603803204440d025049200000c0d201458048a90945881d400d94102460300054600c06001003400303124072003601500144a001049500100180305188503901049000340740d06c425010aa000550030750b04d501c0407540c040300709403920303030040a00e00070300c43c041a1070009074800c00b142001900d200f100c5d4950f03075401035031628005481c0316100070600d03810003c460701ca800462000c4409211030601640181d1380006600026855501002d0056442501d022009038442040d240503040741c80d5641c42c020500d43c0b1103140c42401401c4405030320340d01c1401c10710711860180c1d100c0402c0404000009051140f80d0765410b04408640e403409010350550003061040c800400b0104500e00000d00c0c5030b65081c50b25103585402ca00308080a0b54010881e00704c00c1000182800e9000f5040d0008040b500c0e80007035040c0059640c0000d542ca10800001c080c41c1d4008034281300c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 962010503 1250 962009253 962009261
    0xe01171b2107080d030b01020f100c050702090a0606080a140a0e120a02010203100f0e04061a06041d160c260a0804020a0905090d11010b040207031205010501020a0f03030e01 76
    0x81d499004554010381c031072211a4030b03410181c0850340040e1500011006d9907100040c10a41030034910b002e027201e000da209424020300540020b01090000401812006031681c0b03910f180700e101030100001c1c109060034001400c41c41c014010710140c03424002c0107400e4040c91082d641c2c0040c078080c800100580c111415505100e0b081d4501e06100d0301c04548032034515011f400441c459251810b40030304950300c400e60b2881c42d140b6405603060002c21b40000900050455105500303409e2042c0b40f400905940000044255002d9007107021224100d0a40046005484172880c0d0029030039200c00810000746600101010413142d0003804050315800d25115118000c00c14214400e0b180140c0c9607190301240780505203542c00d98049006412003000022000c2d07892081c280070345002c1019026081c034083c02200d03001020b20005542d07558594020886660b00d10081104d1b81c42925000c1d80e024440f0100c000b1a6016844941903400007201900040c92002c001046140c2c035003800513103000ca5140d100d0042c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 962011753 1250 962010503 962010559
    0x105011e1719030801030b1f0b1b0304080f0615031504110a0f05010809010c0807120b180f090106181e1e0c1d041d070e01171b 56
    0x85a107014420a050344400c144d030580f4080c2200c0402500c0384100b1500303244203041c4201501449010501c9603171100d40c02090b070071112081201700c514100016a0465100d035004800560095810741c420706010b0040c1940002d6060840c1824540b501c0803945030703058803418403411140c1d400040c0030400829010605144090541500c050321484070183d040c0050190038041901c1c400005e41c11181405804081406640c41071816210703400d00b42c524078015030344260143d85900c056031311a250100c0080206400590864060074030300181d60313040002414507500d90741040010f1010305411070b61020000040400090842404500c0380e80c1c207030546803007010440c1001700c5080b0307801100030696524404224100b000c4400c1020903507803420701403210728980884614141e51752174a54044480d0b45034210707240c0d03140e011410b4282e08200e4140c00000300c50601000501000480300840002ca4240d44001c1000c411030292461200c00c410801520404140036100783e003904041116046c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 962013003 1250 962011753 962011783
    0xa02120712080d0b1e090907230f01110a030f1b0c0501030b0406030308040b0705040f0602030a172211120105090607020c13090c0f0303110105011e17 66
    0x4a0809403a180e5019030084000710405810a16100c01c0c91800240103e03d500d8844c4a640c0400c0f00c080030b01c0b034a00c0009001c00b65500800701e00040180c003101145110b0314275001401250070350003041000e10413400c2812410001ca038110242100c80001d1000c00013500b40c1001e81d8025025002220340c42d0764055160651316143e03881c4010801005c1c031240a072042620705100e1205064140000c40c1c442d848050700045004000c100440d0000e4261a049071003444e1142c682500ca08034007a00b40000c2d0310101c0180d2001a0750550154007055030803180345004e421480d9401c08041c02c0704810184045c1a90a0100000b0f0b04100864007807081710107a00504840c8903000701081040c020541103915554a0240e90300103440c0602c00700c0e000c64552001004070040c61070485102b4011310009100b12072400d901080801c0c00001941000020342c071941d200c42034590954500c1e0309581040e408040041c40e101d103000c412883c000304540c182c81e2080c01580d03020189402d050302d00b00026844680c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 962014253 1250 962013003 962013029
    0x3050a021306020c13110703031d0a05070609060c150c09091104031a0402090708070504050405040f12020111040501050f09060714060f061003021b06070f0f0305090a021207 76
    0x410301e030082404101030b90121605511200002c00540c00c4d51a4808021b100e03600422000c80000e019a02c6000c041402d01884224082c1242042e817401c01082000c0e20f10303a01c5914100300c07480c0c0c0140d10030094180c070b10700134a003400d0964428003408801c41203680f41a8540e143d003040d16128101030f50041143e51400d11400d000236003c0841c41c2d1240c041074841d5047c44013012414041ba000c5076008503030281040c0820754480d4400c85511901521a00070000100303c0003609a0b910700036207004500904004010102602d800b0f8950f0720415500815641030550b55007162036910141c600701d420030300700280e80780021450b4a40501c03134208000e80c80310700414124184180d0382d03807084103801800f0444190780c5907400c042152140888549034000c0c05140391201640c8a500500707040264110442c155030f140d0001c903801c0520844120002810101c200c1404aa12031010540520320741010481c5040c10111151504180140030340509004000c011504c101007000000404201c0134184d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 962015503 1250 962014253 962014259
    0x31103090a0b0d0c14250f0825020901060509040908030109020c01060b04180906020d0e010b0406060c020603010e070e0607031110180f060f0e28020a0603050a0213 72
    0x48103904842e0120a045140c03c0f40713422594062001090500d084c184140c0c00c000c10004407040c03140486000d014a14152000140007070b62040c59440801c1c400d9102c6074450319200401140301d0542c8881c0e0180744480a211000358480990300740c117551461800036902c1000c480840d011b86118035000300380d500000000154440d6030b6015180740c640c104005d020b096650314950490b80600c0c000c04860540e8000304600d0100e05901c0741766803610032080541400640b0710310382c04503280e4090351240d40e51216907544403846e061252802400e41806c0025041c94150081500c40c0014040c600c550104600840d0540d0b005018a901c0400001d011903541c0381e5910f4024540789069443c1901e0b40300c1e0103031030a0449080c5c0228200c1c3c0036801e40b86101051641c54071454440747c800250354469440c1a88845000e140c0500700f40100e20704010000524007159140000d0400c00b840c00c080c101d080d00540040e6103030403a10048491902d4041050788074846610001c0c81990000000e0b1400c1072400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 962016753 1250 962015503 962015519
    0x1f03050603030c07030c2607060305130204050a02031b03090a02041d010e030c0105070203030f060d0f082a010902090402060d151205010f090309062a060509120906030103031103090a 80
    0x607031b01759007000350254410b500e641c0e0303440348001c44060165515080204280038076031080d40000d501c452608014490605550082000c69009031401810940c0000401c0f900b00d166401802002c010b5001417891403410034015911440c01c114000c0c416512a00c0ea608490130801001a1310000e01d030007040f0404501501075038941c4852030300c000a50030803000030102c0c2c0c008800e40f0f02c40c0784a08c543c0d1705d4654600d002c1151501802c0002c4071a40180c84000001ca1009005480e1980c1e1516000700040800c44040240002c203100556460703040c5503d050060310f4000f04550400c0c2c1c140c984584846449022201928251080b000440b00074032001a0f0110318010049c4141d02410080051200d0300d0944d00c00d503102c84001401180d00a00f04000d4544140d20118691b88407000650850003030035410303004400110000e860480e214020b018a6000c1401061100d04030319040e18581074010022501e14041488098144204101c203459050418011160100001081c0c400e900d5296400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 962018003 1250 962016753 962016773
    0x6030c010e100c0c1215140105060a0c172502061605150f070e191e18060e070c030c060b0103020c010f050117030c1b030715020703030e1f03050603030c0703 69
    0xa9413500d84001c1c100d6915001031052601f102d2080d640b03216141e0038103080c00400ea0114540c8d2040003c0e481a46020440d4400888108130b01041000d61b6800c1041065601c002460841400f0100807200240181d880c902103c108400300d00000c034084540341409801e2900d03140070b0407a08107421040050b0010345120300d41c403c1c8902c0c0c8070800e941c042c034410b00920700785011140c3c40c044284d420510503e8454652802e02c040c003041341442c01e58480942d003a08881644110f0386158030303298103000b61100100c0c0243d000e409071811500324001d586004022825822000d0009544c1d0600c640007a4481c2d011220660a500000c1c01081d080348015030007440c09200f03158009a08924020080e0030110444400e00500c40040001d8003000481d425042074003543c0660512580b00700080029602d4000e809466843d0050100c0c14070350705000c1c041550300043c2900c98038400e28601c207640806804c9014400785481c001540b6901e007004030389144549000c0c8a01c07440f810400000300016a10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 962019253 1250 962018003 962018039
    0x408091003060e0c0406080609041b03141209091501020a0605010b03040b01050306061e0a03051203010305070e270a0c0b040614031e04030c0f0b070806030c010e100c0c 74
    0x10f040c19140d581e992429510b0040d8020840090000d1020428619208800390340040c020020901c4108510701094004240c80d802180e101ca68035041c40352680060050f4030b818124040a240742495040c0024241c0350001c1500c220010181d0903044c059108200c1c032451640c0c80032040200d56103941200800340c0003154102c464407004da0000c41c0c20304000c2049809941b018000c1042440d11281e58260700e04000070742c5400c0306103c0e2000001c241c007000721049241040010790360781d50450600e1801c100d000e80003003448000f100300340a80e80c4050048500701044244802c0c0140c2d401034400c5051142d040000381c0f9640110f280402d06080d060300400854140f5100d58203801040807502c0980d0104032880aa00400302d600c1606045000c0c000640c00392181c9030201c4611500d0740c54611b00107010a05461038040201080500c07904000003681003036007140207100d800c640000013030210707000740a1030b8010000307079544005a9015010004c16981e2040b002c2d0756070b9442d44c44a24140004807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 962020503 1250 962019253 962019269
    0x11090310142208041509092c010209031e0f0a020a0506030622050610170106211a09060603010f060c0320070303020d03020f12040809100306 62
    0x12044454206481112000c000e6071003070180075a10010a07407a180c100d02c1c0700803803604100030340d140052940700c01000030b484080c0c2d181491500c0410010700d2802d494012209103840c018450116071a980703400420100b007004001c82d01c40b61b00c82c1c16406030080324002c641520504000081c0a1140301c00c40742051061800c44a02030081c04000e0358940c1810f4002e074000110590611607424900025070b80a8400ba05600351384101d0350841074480203004003003100541c0c1c0c0b4103104262800000707000c9400202d20f009200c100e000c045c011040c48040c89908180120046680c5e0a540381c041108142c0c02501c2e4108800211419405420421807110074030810181e0b0000740180381c0001942d0507240240600d144481c1402c50580b8003c0340680150103002c8809204402d10303407142d100c0c0440221100185c01442d15626010b031500c006416070b0310501d40140024400c14403050b003610401240310b4131042940d01c40c0c3c18004840c0c0700c0e03400d2541d0041000900503504a03096000942155800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 962021753 1250 962020503 962020513
    0xc080d0c020907021b04020a141c0609062414040314150405030a080a06030803090a0b090303070e2205310f0f030e060d060303111c0f030906110903 65
    0x440f4101d885140e01c208603815049840380c01000b82c10035a010340390b01e0346182032403900e1000c2d506424450340c005258128a901e0505100b400d50080c0b80a40001021030010900501c1e003070200e0302021640c0032813400b508040c0889613804182c8036120821580c89003c0000d540c0d103480342008114a00e1661428089104280c44130300799010b12568644243d4019020314246010103408490741800a80350103501c646821000c404221140002d6022b2800c0303c000340101c1c1e803189170070341c0c84060003402901e654105000b000f00e019080303500b85184c400102e5200340807070718202054003852008894000058641010090301110001c2c804541d0406583c04004100c815901c080302d007411044000e00b00c000c400320240c000745d02450048c00170f51182c14604041190040443d4940c0c20550900f42841c1e00c1321410020f1540004070640c08007070002c05801400c0513030202c2084910300d021041d08011000c00201480c170b110354410340c21194030550501801c401805214000e8110300420791080c092 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 962023003 1250 962021753 962021761
    0xa0302280f0803040605070507080d0f0f0212030a0f021c1d070b0a05250c1d040c030f14240708070e09150306040501050109200909040c080d0c0209 65
    0x80030301241e04a400c2e0100540c40c1c60f08002c0304803150741018908891a12420300702003140c020602442852055591ba0307110095a0000c8c010700c440600d00c403039400d540020254030724440300002183c0c0e02000349070700400c00852514820780248289444007841500d00008658409111380048004003121428025004003842a55840d40c41cad034420360068407403c101c1070040a00907400b405d400c04480c82e10003140404010702d0b81c0b6059030410225000782031104184040c4011001c07024040d0300a10802085280c107540c0c0d1503c051072030002a008400541c1a0020050443c13941350b01111403206450300c52074000c00003000d0b0080c40101030640c100e0540013800d601c0c858031304c8600c190b01c01d640303580e226000c00060280c070880c09014902d074500e140d82c07500e295450400109006074400c200002e095803601810400700d600c01c6d02e100c0082e00701300840b481c08626143c180d84424008890400941d10381c2d18004d045040542e002e02100d01032244a202425013101c00340d100035000f5144010355646d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 962024253 1250 962023003 962023019
    0x50649060b121b01140c0708061026190b040b060904030c0b060a0f0f14031c030c0e0a0e070816020d0c06110f0c0111090109140a030228 60
    0x203864a508000c55110760f100112510181600d01c81041044c105144030255071520414164864002503078503501603241045810f03030802181354051644080002940d0904c03507800c4004845106614040205420056015105110202d58110050441e08030321740c603464084002441110306442d0b445100000616505003510150321036941542c0700024001180d9401703004890203000c0381d8001c92841c0021610100c5e08200c100505608441140c2092402400d07104804c0f071200709501035000703614401e416100010041d40b030000d15050114503550380020840714003510840080d4001c1c9896400286410300e204640e0117801c0503654072030310f559004001c0c0c0d401080e8440e0000140c2c800c20030f480d04548035020001400d8441c060100c2d0212410303030080400d80003048a908072010014800307000d84000d12444061301c65116040307090140c0c540c006402102c0500c03507084c1c0d4820b0098440312aa444601100207540d00a0251030309d10755940d030680c074143c80c100b40c80158118424020490070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 962025503 1250 962024253 962024269
    0x40507090f08160b070302010902040e1018080f0a050d0612050c1210090302030c0105041406070807050a0804022202030618010f050d030921030f03050649060b 70
    0x70a254480b1031203e440d0050b5160a0307406404280e045560b1081c1c03920040ea202d01030145107099040c0284800381c010800310781281c1b018608405603000340c03c1d912001075841d0064500d0740100b0307000282c841307003040c00139995885a0132000003880c4c81c000021030f0079002d110003104014014800c0303d44000a0100f400700310103454122004c558440059000d00c0026600020829840b1b4815242003000d0011802e081d42e81c10b550498105a080e50099181a420001c03d5800042442c215070a0b05240401401d01d106071700d59141048008000941503441d04a00402e610b0300d10010500d001c0754280e0400002d400943e00280b00700910313402454020318110307085050361003011048003040d00c0c040820800c0c4410803412021311000c0b490004442038102e40901c5207031070300d58440c194240c80e4a80280401e944007081d0041c1441c5c04180019501ca50301060100702450300d1a07460381881d60303008912003a20918141001059400c442d0072000603402030410184241014440c01a0314810401d180f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 962026753 1250 962025503 962025523
    0x120605040b01090e220c03031704080d1a030d030e0c030a080421020d0b0105090a0204080a030807031d010213060908120f07080a081e090a080c0309040507090f08 71
    0xc850240601c0b11240015443d5001707516007114a065024040712180c90030b9001e1819124031200ca8420010b25410007030b801c811801142c0d09000c5850550398403072481c0590520b045000383e0354030b10304151070400241d403440d6120040454401c032103400750050161801140d88040e60190350f4921204c2d08002030800c524030b9110240300c0c10b0908010000401c400751207980b002c03012424071000c0160b200c060501000c14001c5100700d03100c0d81060140102d001000e0100c1c0c0d0183c1c4100020401440c000c20300250342c40d03051502065546800368201e002d0440d41e00d02071051401c81c00e411401c0c5505500524840391418240c811841e500c1d2016252000035124000c000d4119100d40741c0140e98a03001441c40208002085081c188182c0368840e5a070000311004001c80e23a030100340f200c01c030968000c8141546054070084900d00d803034190603458480169008201c500c01284100076160709105031403440d007000c0c00400491524a0700101109041d00c28542580c1d44e9440c0031440042c04109101d42d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 962028003 1250 962026753 962026757
    0x705070b2d21060312121b090603040f020f04020a0c0308160818010e0a1203051501020309010c0f050d181a0a0e030f150105030d11100b120607120605040b01 69
    0x40100d501610500b4000e00624640d894062400e02d0403002c0009009800480c1310442c013000340385021003510480300100703028240855801c4c406d00300d0a989480c22217030f0096128101c0c480b10001c0e40b000c1050300c0c070b0304441280d01500204880441d1980030f680424224082d549071b8140d51141c806d00c0740503501c0150103500240911001441405110540e0002c2a4500000062040384a00c8003030804149010440e0111201065013414a43c180240c3d81c01c5114440e0b8081c03503081d0180046e6603031181c02c83e01c905000340ca045a9080c007a403140405140303034201003a10304c503800c1e401c001840b078020944004114000c0700b0001c1030032070440700d010001410a0350b415241101103601910404000c00901c0d6140c402d0403083e5200b1441840b8000032614101c0200d034082d4101000c040c1010355041640f0b0812244040c0310084400004841e20b5201c60503c2c00145682d800740421145182d00303107260520b119031000d01c200c1799405400d090584203040420881262074000f0041505c0c195294140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 962029253 1250 962028003 962028037
    0x8010e010b0409150c090b0712031a0307180b03190b07020a0c1809050f010603031d0306060d1412070b0f0105030d080c040f0f170a0b0a020705070b2d 66
    0x8144001d5030040d884c5d580e46041905109540324a1481280d01c500c130b08850394156002c04000c50754040c05180d031500400ba01c06d502d110088004282e64000ba4460441e1400c1d841010000b00c00d03443c2d000280c0400301600703540e0503444c200c01c22908100c81080c200d0b0844241000141c64510200d40603200036888004594980c0c42c1c500c1400c0c0650a41180ca0401c640d115181c0c00010800c000070081310381d2440001c201185181000352807000e070000b03212003411100e054094580e4000c15941e5010700111080700c0024918102102204540d0702c80140a01c86d51034040d0a1a00c00d0001c0d141117880341020718065036402078110007580c000c1c0307d03a541590203000310300700780c0e8000c80c845588002c6c41e811040c10103968040a2074004843d43c4640d06440a03c082408800079820480003024101c1004203c154483c0d615031140341e10080c407003c030301035021900c035082003401d20082e00149102c01060341c40c4c20520304110401240c6141d8592060303a150406a00c0c00c801c007080e81d20708030000203108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 962030503 1250 962029253 962029283
    0xe0118020f090405070c022e1202131806080d080412270914010f1e030c060801080c0406152d0503010f080a0c150e0a08010e010b0409 59
    0x40080c0d0024001c007404000e080c0b000340000d40b614400c0610400c5c4e82c2d56107030080390340350051151031005076829200c40d0f8030f5005243d00c0c001500312120801003007440d000a801801001400c000d0003141800814a2002800000c40744002845003e02a01038035041007180e54921081e0303603518801c00e0700c00105562100140100d8004500860343c00303845e0820000c40703c0803901e810400c03560003440c0100798011000900803014644650900c407842069612050b50400c450b815080c140c0348107114155000c04030060102c281c1c07d030000000c640c1b091b07204528580322038000d01501c40c24000c0300303160b200c0c082554007286000d01500741203d4042e1211891000074050888410044039042d0921141c00e80040c00340340e101c1030000c6102c081c0d6030365494581d41400c118800b10003040c1e1003566a5402010084085054902ca0900701cce4801c1d0074900c0b240c8100801502e04175030040f290b540c08400a040015004019000180340c101510020803880102c2030030041141d6a4140c040d0581a41172005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 962031753 1250 962030503 962030549
    0xf040e19020a2a061401090b06030103050703020d0c09180201030b01051c050c0421021002150c030714160201020f03210402032a010806010c02060715020c0d17010e01 73
    0x80749120600007140fa8800c9401d0711202d00b81e40158503121560700c4002c0c0100440d01c8644543c8160400860f801450341d451525815a940321b2400f0280c89a401a1880780401010048031001414a090705000040210540582c50015120180c3c00b00f800c142d03403101690b01ca6070031196903202108428104010041540c001004028950041d0312410000494640c000003603c1844c030790059010240101e06105000400c96585403075415035000c0c6055024003075110700c4480c1e211110200e2640c9903605d4400484540c6041c510b20034030030000080680704100341900d0003c405000380c00301d031030580c0c0080c0c225980384504814012007142a403800e099aa0b042d546144e001400142180c0c1d0340c210701c4c0e90304040da0030703548400035080d84041908071040d42c000008581c01a824204401e96039004e80200c0c0f0305110f445401090200040b464003000354880e410b441c4500d201500f00c54070450301324005003c90641c1405808050490300c00083c06c040072850060590740a001c0007008021001c1c40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 962033003 1250 962031753 962031797
    0x50a1409030a0f060b0907020703030509011205070221191b0803240406030b0c03060d080c070603060816050613030f0b24010e12030f040e19020a 64
    0x64010094200404140d5940400203001c0140c02841c24a0b80b0002c80c2c604002280c2500150f18041d198a80801004503004a109011241c040c10060ba4406110380100d031035520390400b0791002d47c608418072144941c0011410480d480c1106260010401d44104580c41d02509601032804078080210f110058862100e50001d00f0ba28440c141e40c00780c2a0760360740003a42080b02c1c04040c0002e00000f0300083c2c0d102c0090240780c20340a03030f010031840c0d0450f11404111000142012000076002000ca0403588501d0f5020300c206400c40040c61b2036010300f245260321807881d8401c0000082c00c1ca80040340001012643c2414064030301ca094507628075120070b000258010f403802404070030a01d880040482c41ea4003001c281a4459024500c0740c4ca8083c040c181038919443c611804041e00880400940e41c01185126031210b0407601d0a28994280c4400d91651040c0c00801d00c24200214002416039003141c5a2801380090440703020f0410300c03c59407142240034400348800004e82120707205582060b5998 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 962034253 1250 962033003 962033027
    0x905100207050f220e061e010608011205241e011d090f01060602070f2705061c0b0f2d10090e070e100f030206090105120f040201020c10050a 62
    0x8105030404c03510310301c820101c032030184040685030454010010040305626152071600034550456940d541808402040c0c1c22050140342c005c4400c0701005010b004c0100600281d00210303139118002c1c8e81911030000720014003907550200407401e40c038804400d240300d0a211810303650058903184e400340c070724002c000440101500003140f40c00b588502003001542801840042c00b0190001d08400e468151a94802030080e48030030308514102c240522400b8130b02c40380a0101c9000300001c141a1614400945003000e0904601c0c000e1144050510411018900c0300d485009035841404440d6151a404800c0340700d109000c8c10741000c3d02e00200150480102d200d40c020b11404c4c246040191a4800c7c81d00320343c1e110030f5458680d448a0340c10056461480b8a007680202141d40080000d4a070007144c002000d02d80c00b00901c11080812619200e0f4454003d0302c248180205900b001030070030403c240301c8a01c040c4d800780c0c014082c1c410391f400e003404c1503807076801600030541d54036142981c181021a0000c444078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 962035503 1250 962034253 962034289
    0xc0a0c1211191d1b0a1d040e0d080103051b0d201305090606030c0604050906030c0a1706060f010c0f050708071e050d020109031506080106060905100207050f 69
    0x840451060010401c8080e251415001403215040c40410b404021044440012002d04d08001c0c540f00d0070780c04a05d401031800788260030100d004820700041c0203000d10400b105c4241c810000c0501c0c1c00c55100491a040300e001d80169004104012407214500c03841c071040640250150742e030071300010800e2404880340d030301e03c052001070000080e0000742119800d4403200441901d44003404603070781d400d01c0070a800910803002080381d50080c0002c81ca46014910840d441084c504002400c5928180000804d05500a04c0100b403244c5558045480040101104505102c2e541c0056468103020104151286050b1182e026203001039403240155841c41108031054022200f0020b4002020800f034030141c080702801225900301e44014001c000e5251340110300c01c01d134003081100540d03000340400003920341280c080c2660015500072a00a05000e910600c80f542c42c102d0001400b1303901003031400c01d0f600201c44038031120b40045800c0380d0b900214014075a0019680014190518203a694010342083c41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 962036753 1250 962035503 962035549
    0xe100c02090a06080607080411010914010f02100203040c08100209060d110c01050c03240612100b0c0c09060103020c0601050402031e010f1d0c03070507080904020c0a0c1211 76
    0x2190030740d0170f05e84140c80c06e40c00310b103481c0305100421002540424944100703103000a280c41c9001004542d1903200004503040c04011491030302050303c24402e50300f454852040a5680e4106854034900d007520620400030350b40191040c200c00501c6500842d0a440c00040405040c07a500c802e83c3c40050102c3c00190390003400402c04803d422030301b07000b994414000d05100a441b4940740e58040c00c08510020032a00e640380f0288036807515a941001c1d9a4001034000101344070742d0740c5091803c54020a50441484c030b03100420500500d500c00a081c4110907400e40e0b2241d50b640700c000c0154281e000c1d00d010403100b83c00800040c40320742042e070701031540117131903080d40007480802c11181c0117103010a8014a0740c03091818400d201e4641801c01401c821106003204600f40c0c9810038130010503000283c0942c04003d00007ca1800b40418002502c03213040d0018000c540c0d8140210165139030300380c0c00d2407c4404400d42040007500c40441e0b203400000381d40144031a510034404608004803e1510b01840040c4041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 962038003 1250 962036753 962036759
    0x1409030415170f01080c0102030c0a14070e09060403020106050108041a2205030304020906032d0a060f14070306080a0813170f0f060105011704151503030e100c02090a06 74
    0x50110b40c2c041c5500b106004255414540700f1030900c42a2803015040d03601c01c0001d11090070002400e419040c0c1c11200241b110030003030b000075040c0100c6a01201061441505000418201180311402644281c0081280698450040d00e0380c2c0d0f4200c40140008040711a50f600d603400002d50b5541c4501c6c560409840c2c01c070307440d65100300012800c10556040d03001200b00800c508120000c1900400d08400600d07041c1d1040a040b075103240100d030074180c0c403880542c0710f1800f2201000090000c3d43c2c044420310140034044058001400030500c0910030303c600c4000704000d180244130b13072000c2e00ca001c00940850030447e1910526035001202c4054401d0711418001185440c01010203150960741c0064030300e0500141445103400040802d409198101000400c416a0080000306a85a9200d10040203903103500f019407485035410340128150b418480000d14910902d0400030940c2d100b900c54100c140311820070b00c40901b0000c958807000c2460903030751801518000d00c0c42907001d0301c0c03140c0100740962 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 962039253 1250 962038003 962038037
    0x304030e10050405011814060f0c010f2703051b03040f09140a1509050406290a0f080706030203061201020a050d0b030d0906080a091a0106031409030415 67
    0xc070107041c44000400104041c401503a0100c50811000c0c19641c1c0900c0c40350070001c3c0500c4254010711610301c039a400044080c1c00d40201010b4400000000d0020010b01440a0600b40507007070811000c1c264030f85180a26100000c0fa100700c410158141d51000c0c1030401d10030903400c401c1600e0004404a20003400006014a00310003880d010f05001440800e12444503c0521051172014103000056800c0601c1d00e6410701c185c0142d1000c4940b2171202180c240c07950300b07020000b40101d041035840840041784400e03150555a0860894110645050860960391079403241e082c241c0d4024902c0c1a00721030f604014a9200390050744e000580142420030090344180c849007240d110001910209e03201040890b80c020891107040c01d0f0140c2a00900b024145030b010045c0007022030300130f0b0010722a4000202c2c80246065011001503603108207104064810507440c01d90072a024850355000170304004406001100d030481e181d0041901000079410076040420300d1000079000d40d2607404110000340d1408084d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 962040503 1250 962039253 962039269
    0x5311703030f04110a0b0c1b010c11010f0c1a01170c01020a0210050405280906060219061107080904051503060103030e030a0b0109051b03010f0306110415050c0c0904080d020304030e 80
    0x147c510020925102c410903030018240181390701e1070501c9041e0f03921001103194002c09007515102403900c13659844175030340181c0c0c240030303a600081d10340b1040c2c0803050544459045160305036050805424103c8190041d4255520b02c9079400300d0058200501c541d0040c105418942110221400c00c603080544990208008051081780c1c0c007001900c01403140303800701884030480c029001240c818002242010700182d5601d00310018901d420709d60880c03802c1032011641c015460384159550003079642029080408480d04691446482140303400c02280380b01c984600d4083c142c00c80580900203a81c40c0d80c81c20741d0f00c0894207a000b030b050b0062000e514001011582d2090182c044514009480c0c20000a00d582c24060000414402c0b0802c00c018003c06030203044c80c404a82d4001e10103e00f51502c080712441500072640606004001c45100061954108000d0111b2380440011034145808841c01c001c1c0000c2d0560300a07000950401c0141407825090300110f42c414000e060400d0304400f0440440c042c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 962041753 1250 962040503 962040517
    0x90306070f1e141606020406030b010201060f0f05101202160b070c0c050f0310020d090b0a050408070209131212110f0a05311703030f04110a0b 63
    0x2070248140403003840c0d00002100d80c2c0820148182c10200e11512000c0c1010341c030700d486450744440110b098580303a40304800428216901400039074407956a40b0010b00985078a2200d50f000d5400c1290100d500200f0703044c031034102d80c18a10300e0740c02e403440c0030300344009541c6601683d4104014000881f0700210140001e101121750840000b20381d1843d03007464410104042e00c1130003001038000c4013a0125440b00040025501c040300c05403032081008000034603049248080d420700d03900118800190800c15840441d650340100c0504140c0d03a11030310040200d42045400410183c404e01ca144050b080c81e080c0c81d64442340341d201045240702261240c0c042c0340b4401080200188407464080290406070155900e0403290f4094103040200071050104280504600d030003c0100110b0302d61030400c01d01c52084a0444080740709103000c8100c01c071019141903180106118050079854900c8404000800c803849580300f045480c074070b51296074441e44e1f1031220510440d88040c024a011900310301c460000c1c102 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 962043003 1250 962041753 962041757
    0x7110d152d1e02040b03190212281e060f0605030a1e09120e010e012001060e07021614011d04020c0d2708060408070c0e1303020f160902030c09030607 66
    0xa0740340c104591580b1769690000c2c05081f074018032102485807018800260004039109070050511b105410064094111604010189040c1404849503101e194084101404100402d1054903124400c00221112620504000800030000100b40c000598444500c4440e81055019420f8900d03602800340d80200b13100f070720a04401c2641e100c04642105140103440c001382098070f441e0448800291601192016440090b1450315010302c107400300398811000341241d01c0b9500031508150324000d40d241b019a83d074202e503000d1140b01150749110621034800591059540701e5642141d00b4001071711082641040d13400540130300070f1030b11b544418000320901c011607684807044820040c0b070106003a0102c52546028041d100000e0101e50f502042c25607107d40c1101615665a116107018480082d0a07445070b11480018401d00450054401c5400710803402503003210045007681c2e0050303841d0016440003014002c101001086205140d07009560b02003024000b103800c1611a0700402e09000b01141d87c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 962044253 1250 962043003 962043007
    0xf0605041214190b40060f0603051605010507110105130f09020703080a0e120a09050a030305040810050105091303020f010204091401060c080304020607110d152d1e02040b 75
    0x1000350300140c401d04940d00b100c024003404444103802c9410f004100c1181030070900c08841034109101e06c9070044601e148105000b00200e030380d68184107481360400c2030101d1144003040c1c0005034170f611440079102e000790031030b0b5411240020b00d0700654060313000c2d0314000756003d45403c0001d00c4040d000b4940c80200700312080560303907c20340d1400030b0940a00400040016182c28401e0308484d40008403054062000c2da00d1a81c2c440000340c0079500c1140c0340e8011544075241050201c1010b50140140c811501050200e440050b05203035000c007034a000740245a000820100000c111258154180c51800e010780180c0b03204541c4400014260b038802c0e0004218035072201c1856030b055903002c0483d401050a490035424090386030765003152910001d0006807080744007040040502c107200c461003024990040c60b008400c1c00c6e81ca02458281540d04e0820781c080d160104003400c1c1c6500c60320308003a4800d1100c25119000903544140000e100d042502d04c2e07a000c1440d0349401c200c0f4103100400140211580041e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 962045503 1250 962044253 962044261
    0x3040807140f011d09090106050f01032f13080717010219080c0705060a0b210c0103051905040302011401050f0a050607110d06020403050c042304050f1203010f0605041214190b 77
    0x2c149002b0300c10901c1c1c1050b140c01c0018000400c10201c074401c0c15007881c3c92140b0f6031545250b403030300790140c040032900300100e44000080354100050394600f00c4822071038404082c07040340c1207103080380203a80c0000d51178801034090325007441c407d950440d40030300420350302c41c00c0014644880346070032012076100c0c2da5981d031407010b13190070719140b161641801202050400095850b218103516a0741010301c00b4107054442c030200302180d0701c4107445c61000e514614100403078034060030005e0113000410604d41020741c40c90004039090034846940b950000000e4190b4003400c0c541418070141781d00808013500e003618030030740c074403119515100c22002150081c0d4016071200c0c01c60810074140090180c456100300e01d403c00000101d10901d12840d000c62020b10041c0c4503544505019007091b0300303d0b04500240c000e400700140365107000c0000d58160f070703004650b891155449140940b145d10aa000d08420800d407552803000054100010855910340722080d5141601a0101c00c030038408a500c0880709010000200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 962046753 1250 962045503 962045509
    0xc090406150905090c030610090f020f0d0507090b2113063314010e01030b040f0f0f200c0106050604060f08060102070b09120a1403040807140f011d0909010605 70
    0x45c130300e4241c048001d40f0042c100f4000441211010303124842442d40c85400c800c2e40c0280301d81c140c40324000c7c921a12940c0b80050480c050003450121600c102040d0b0b4501c000c00c0b0544100140d82001001143c0c0c800602c10488103016490f40c010000b8840800481c4800300044490003480c2101e81101d10800081e240d0190120344407203003000009284403400c80c00c200c0c100302c030b02280200c00c000b82481c3c10707850203090040b07001d05a2580d003690040c2c1045c3c103c000380fa00e1a031201e9003903032038000c0030810306007964503540c1950441310444010718040d210b0407609a110310010440200c1c0f43c0000a9915030343d00200365a45c02513480780c0d001c40c485000102504e40c104500c56442030092001d00400c0c0d05040600c0c5c0180195124280184a40d0707610055407141001007500322078114032000514070041c1405036690340903015141040c066604000360500281d1074445441d0002084441c000c01c0c80801114a0424082c06081028941a81c440c00352500c5078801e00892004001141403030604d014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 962048003 1250 962046753 962046763
    0xa110334050a12050405071412010c0e0102010e0a0203060a0b1305090a0303061e170102040e041419030903060b0411070f1b0f0315020408120309061003050c09040615090509 76
    0xc0c0c00d4000b82044100000900d002c00c0c11000c0c8d030911204400342c415044085800300b110901040480d40c41c0c0419820640e0300822002d901101c00da00034011101141e514540b5840440700094140d8000404130341402d085800a051014004c4d0040040a920806c40000e6840a840c440801c0e0059000c0a060550500444028200c41e0080c0a40c1641120000749400c0c45485800744036242c0461400c52110701b901210000c01b01c0f0301c1000058201814070910a218205415080c1c0c480c42c02660702940680040c08800c0d03805440c0d1070740051564451134090440f203114561702c02d81e0383d20106005a0300c1d0003e0070ba03481c003030418071007801541d14008074640741e215030484803141803400c108039084514552405499020224000318010b007220180a40600d4003c135000d4012403895084201244000c0c0d4441d03240724085803040d072a0100e9103004000c0c140006040c50304034101801003418002c0030a508036100b884c000410407462b101e008410421900720030007c07910b513000e002d224001080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 962049253 1250 962048003 962048027
    0x50301031a37091a0a0e07030609020102240a0b060f07060917070b09160501120b240a030b180106140717030f0a110334050a 55
    0x5014000ea08180d88401c01256855500c80d60518030b00301d40040e6011081d00c0c10100c144040d80a101d1515645030000e00401c5055124014240c214002852801d20b0300804a0500868000e40501815901c42c5e902504802200768194418442c900c01c034400082c0f0440b140810403540211641090f03e00c60b001d49400081c41031040c90103101400d8615400340450b200340340d20900c0011102c0d09032070420f00610545000e07110345640442c5040c140290294802d21031200c0c24103480549140311444800d040070b5019007030024010a024488111055022a940000080c10070848014041d071108815590380201010301d0404035030041510b030103005021807840f0841729039158003101101d80a16900501c111001c004036445800038000d0604100c03024182c0101240c1488108403001c3c40d03080d4000e48070f4078800d402d031000045000e040e44c462220707811101004a440d50710385040784140b6001411214407506904507094200801008005460410645a01d91655130100c8045c24400c1840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 962050359 1106 962049253 962049293
    0x902130902030d0311120c0c0d030c03060e0c0f0a09170303040210020f10020a0e041a0f010804170d0906050a0e070618050d11090705030103 62
    0x34210580c00e50007078086038100c440506040301103074003c440408a403101480720060301c5681060742608504201001400d00700651000741c01c0409400c6a03601080d0f94021890300310780c05015100042100b01c500725124540f20420b003199200702d9a44c4108150001946810b041c0a0207040020f056005050a04908003c4000d030703407a88183c4040e4850314031074510070703282840040c04a1600501070040c04101241ca09447e010390800100d19040c4504903c0260841d1514030a00044040c411007603446071100d503046c080300c0c0d9104042c29041261100810001c144111054000401d8890205548600000621005118440000740010b0a000601980001640001c07040c803440d1020356450396942c01080d5031070301e046040202e2185a150341040381e45440904850303418050f041e848070047c17074180007803429201200c800f0049070000c00140107200440100e003100d00002 = true := by decide +kernel

theorem cover : BRFrame.Cov 961870503 962050359 := by
  have h0 := BRFrame.cov_init 961870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 961870503 ≤ n) (h2 : n < 962050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
