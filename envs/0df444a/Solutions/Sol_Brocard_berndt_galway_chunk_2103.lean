-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2103
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:25.388639+00:00
-- url     : https://prove2.me/submissions/0b5ea691-c7db-4709-9b6a-925a990d02a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 378057553 ≤ n < 378237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 378058803 1250 378057553 378057571
    0x50106090e0403120c0c0605040503030f09071401120225020a0b040506090d0c0e01090203090c01080402010509010305150312120703180303090203100203090c011d06070f110d0b 78
    0xc0c949480c5024054242070324041c0100340003295044401945401100551100740b400c0803262140e5583c00d010f45405540c21241c03608003104104100500c1c01c4000da014030148010014a49050345488118034000c46072410400076803482080141560106d6000e580c3c00500c01d031030007107120b444a5154000101c12072041c00e0340c100005040400409032801d80e01e00a001c1450940004204096001c01513000c5444894001e000145a40d000803031030f0082ca0800009a036900d00245001c0c03e1600d6090310324140500b080510015036844815184101e80a0900203102d40300d40f00c101c0c9480743c131000300340c0d85031040740102410000004040e00c4031280c0310403a00b401d0b44441c6400c1c4c054030b04030a8091030040d01e82d82c4500100c0d2080c0c2064041038000b9041da0000c008401000062340e00443c0c40e0808c603400841d0042081d6840007814000007061020382441c13150041c0015100d00c510a00076200e118900c04907828021050b2000c0040b0400600c1c8a041c45841d180038034906504803a1752074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 378060053 1250 378058803 378058817
    0x30e0a120b0a0c0305090d050903070f06210603080f16170a08101a0d06080601091a0d020915060903060708010e01080d091719080d06060c0c091d0a06050106 69
    0x205141c045c0c016140206003190103414440070039042200d0a811110781d1603414401d0580000320001c1660010025240c5641c0300e400180b0100c5110104c60300440d0b448070940c3c6800c604102181c0b21301e0a1b103c200848110203a515000c1c65032074580250000c102812030040c54841800000c03140c0001c001c40c0b10240c507906200e68881c0380c505440b1010b81300e101002d071885803c4803800000314000f0500807030030900000c2c509450745101450300000340c001c014095030f20601466031240c04045035010920483c1c030042c14000781d90103d001002c02030000c40388902d541948400d03c0e070780c000c242c8000010103822100d240c5800100204024022720440b480d07003203030310300104642401140240c0c1e5a61142c540c800b003c2d2030a045060035405840c880c3e00380380034040c01008503903032188220744018021140c10b6110600c440006e8211130455200d18140113a044c0c5401c0014a0a078884085442c07a8800080508800998000e02104414807941ca4002d2400e8142000b207103600c01c1c0c1c16a502c030364a4403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 378061303 1250 378060053 378060071
    0x305070f290d0527190f0804030b0708040605180c01261003020405103503130819050a110402070b0a14011a09090405070b04030b01090e01020f07030e0a120b0a 70
    0xa84410750180040b0744c40d4060b110800210782e511800c0441b441c403d0940900d030039902d444400380240240c420000150745a001e2000340000b074003c2c540c000000c51100a21128803028460703a171900346000505000c80030034111a1507036034040040c0c50f03a4215021843e40d140072107403031002c00302a00003240308610703000104400750b080c00740c00d0043c0ca4120452685442c6800d44c009410700400005955007c0300d102c0c4150007010900140140000b90005041e10504050142e4188010780e141c02c02d881c504000710801180d00060b02007819500036219100c2801110040340280c800c419014090050000030700080100c00c0d802448103620540c16040b003640c99400c000102943d24022202c2d000040c05035025a02d0032010003a00507211704100ca1860740e8a02d48070501c7d4110b03a10640303070000c0ea40d004108001040c00b50240003030b00380000b18546038251181d450103002d05003014040000d605515106070702d030004258041c16001008402c0d1501d645001c1c1440d203400c41e0f442c2c0e0140d050945d25 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 378062553 1250 378061303 378061381
    0x90402120f010e06041509020303040e0a060f080a11090c041a0d020703180e0105010c08032e09060e010308040315020d02040f090b040b03032512090305070f290d05 72
    0x347c4003da600401030b510b442c1c0703080b10301e80d0100b00150441c1c00302952030300300069400c81c2122010040c50307824058409840c1ca41810b103c054540c00120b4091080501023000038881d8038101ca040c0c1c1e012115100c0444240b0000e410213000da4088052643c4c400106a800d154000f00802007a20b018034401940341c1d00c030f071003030142d044081c4105404145c4015100e00010a4917001d1903005001da8805c0001441c080070319030b49451503040640d803c8040301e07002c0c41146030901512019101001e04207c0c1940342d65128a00c9201d0f9200c0a0441030310f000740d881481c26a60101d4080fa001585d041d515103031075251140081500d489010a50f915060080b5420309250044c4200010f00034003440c1403402c2e1030b10000e44582c01c51b00603460580c44811010016600000350107000300543e0f203415082d425490724502e1300503d5000036500c07085400003001070f900070424665061810046400c0002141c11000c44a4000c2ca080000c615007040c04001e0450030340c041c810020b101e910140700c065505038042c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 378063803 1250 378062553 378062561
    0x60901090c02070506090d020414010801110301140405040203070b030a06060e01020d090e0606070f0803040228060e0a090c0305090c0f01080a05151e010201050c0306090402120f010e060415 83
    0xc4000903800543c01001540303480409440d401402038454100b00089500150445410380c501090841c088001405138001c24131078050628461184e007031941d41019400195001005e2900d0b21031500c0e0b0b80000d085480501441c001031444528094880c00d01d000408040c01d028014003000070400300408002d9031002607008020660358030b880e1032190070201c900b445143c0c01000d42d50042010007500000400b9a0100c07020140079600407074a0b410184100702030444861180000032004076040d1010720025500c0008545c141d0501503c1e2541c0300022491508260b032000080c9031804520a070001c1c3c242d080701d840b43c1403c2c0161014801d000c4100300d421200b0400d120300181e0000c3c00a010740c015540b10381e4001080160003c0188821000140e10b500c0403001c101030868115084c138103a50f02409500c6c0c21104c1039000c20704600e0310300e012898410b0024406071081d202da0450b4280d50100b845110080300400c4020b00c020280d1058040e0750741410b580c1140c41440e0091225411482c4d441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 378065053 1250 378063803 378063821
    0x120f010c0314070f1110090c0501090b040902030a0b1305061809100b0d020d030c0c0e04080d090201110f0a050f0303010f0b07060f050f040b13020604170313080606090109 75
    0xa940d00182d250400101d0341021441104d10921201204606040780304001c00300210079440d4000c121080c0a103010440d0004503480301d41071000441c41401000855020f880a91f05040030041c1c9035a141060707400500864819903402c8459103910001c0442c258002c01d101d00010350358040900c0307441c10130701c400e50008c030f40c2103525412288041c1c0c1c20307207802d8100c1c5100b01c02c000e0026440b032100b60001080c200c0705140481c080f07403079058004104103c21949200400b505a640c0210b898585c560021a1203510000c410a55a51124a003168051607110091800240c100c0b2400b210f02e145e01940c980d61100b080d50300e0300c1030038501e9601240001c1146c3c16201c2242d6000c624914140c00c04580d40c2080c603080340c40c1030300c8156405102d661885082e10410008805079164201800d00d51045003015201400d00002e60b01200050f032900011642152829070300b002d80030364007004050440c0503001f800c5050030600500086c0400c400104107008080c1159600035a91b40c40e908001100c1c0091 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 378066303 1250 378065053 378065081
    0xc040603212a060905060c13060f0504030602031e0c090120190f050f1501050402070209061003060b04140907110d05131e06110c130e01060302120f010c03 68
    0x100c403002e103404180e10305401d00b501ca400040b840300415175903141000340454003c0c5e00c0c0c20340031815080c2c000b40c80f40700c9001041c8a00345990072001440c0300403d6885180000b41c032407900040410300d400f141aa001c051540350300d1410030103042c41840e0301c07800c0e80207021040c0082c0c0600111444544410311341002c0302c0c0e0800041c11900160910110910152402924031010010400c408104148000710a042d01c41002d032100d1041c402c2d4080b2007a0060b00002d00451042c0a000d0041e140c9554642e0003a1003110b000718001d98203102200500029040403841c0d00000ca40022503268642403141c00210885100c0c00603642c0c840d040303a40d04010000800c980e408040c1c4408040d001d0401401d8080000040000041d11074558450078150015441420045c03960708001d42c0e0f5211b10031000d000d0000d005441a481248001400044480d403952035003036803000c91403020b4400754045001540c0c080d107070070201004078020781e403200b80010345658203500305566450668803a100d80a95a0859 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 378067553 1250 378066303 378066347
    0x6370201051e041b0b070c060207060503090d1d0a0602031c0212070509040b0a06020606010801080d1403060a1d010303170606030103120c05010e070f0f05011e020c04060321 76
    0x503895120b8004c1c403944032144c10034501d0704040742021001008100190140315074180c3c561030000003d19005069225000b0450140f06000398500081402d4031030300d400e880c128000310866041d10f15000c01c0000303001d80c40399a213031780010403030b0700403001e00540407907d800d4460142209807090268480c6803404c2c1d0380032040a0000380140e0148029114901c8040c00006050748584040380110300507802c4000968003a4040005c00d40e44900800d02511114028015050a040000d8500386107480c81c5450340c003001c00010015210802400002c2a04060a0040c00e00d500c081c0c58034004e007800300342c000410081000070200d45131b81c0b8250041c64081c04031303441c50386941c41d585e5040c014101d18104210700702e80b842d4046502401210207181111001d4508649000140c0101030f282c0c0e40075252503485d02c84200056a0001c0c0100000300d280a00e008400007481012420000400c0340940e1080c0381120100520040711001d44500002c501c080d04000d40e24101910031010203c180742d6800e46d6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 378068803 1250 378067553 378067561
    0x50a090c1a04210210030902030304060f2120040501090b0a05071202010b180f070f020a060507120b0d02030703080d0e0f0a051c08010506370201051e 66
    0x14640640d81c0c644030056030509164903804520803d01c01001d660880d450030402102c10f51a00c0555103000c08070500b0108416078041e40440c0c0c59014038441c000034040d411034803100e80c034059011500800b0140140da84441e1045500d4001880c4401c0e20180310800c0c880742030801d21444d4100d82c1038950503110034003800d140101c89002640b00390120802c0060a01071840080c0e042d0801817582130990300041100c001382001d0044024900d28030300201114417090040c050300c58090b481c0c00a905241443d00000304407800e901d084d6555070300414003841d140800144036440304507042c100a0400c0f040c418400204104a80c2503c01c0c01d003c2c1d4190401c000410000f94079000402c5003500324400841c2e00244400203a09040500240d112142c101e00391040400509000548110710024440a4104041c0c0342c020302800050050301d025070400203c81e0b601002450f80f20100c40c0711321541180d919114080014200c07200d04400e00950308050206012840341400c0411032f403031402c00125140c0e6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 378070053 1250 378068803 378068819
    0x3050a0809060c030a030c0201050c181018030506040c050901031e0c1d150306010f0b0a0c120509040e061b1e030f040b0906010b07260319050a090c 65
    0x4054001c0079403208040000186144091014004401d21610005090201e81d02c0c040c0c2500c00051200a10003820131802d554440350402e0242c0da03000955081080e5401c40744140d5072881400b0b60300d1520a41036200004002c000a2200d11540c4130301c40703881c03005030b5a10610042000a0000502e001d40040a0900100c0d03881c52500210380a408007180d00c0e40d64a21551704100d04289100d0030360300031000c005000e460355171260b4415805070014481c642c074103500b25183c103d21380a80890508001801c0c0206403082c203507405107076081000c901c0f044610751000351481d4028440140558146040744502e00800710b91207204040b5003507501c640b0511034600710000d9012780312414520182520751003c81160780041c6204203000b852500482c142810301d00386070b440091030140c290740f20030010710250041c2d6065403011680104d402c0c07640d070341e41110038400d14184010540d4080b408010015081d264aa000c00083c858040810958485d181e0000540d9040d94000e807204101c080704101140d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 378071303 1250 378070053 378070057
    0x21c170601020c090c0c1207030504030312020c030a0c120807020c010f09090e0d18050d06051504050903090f0a26100515090603060f040b0a090204050c070512030103050a08 76
    0xc001441074840c03c1c4884000220703c10410348251200c080d01082038401a442000b0444020345054840c5060003a21790f40103160388514003005017040a4a1035051a800c0d030b5405031006040c21720292a11410490300003000e0107440602503e499004001041c5c6c024000c0c030780c0c5401740a041e0f0240c55907180b0f0f200191010740b5802204400c1040c10080041c440ca000d100300c910b1840420087c0030303208001040240214080300d01c01a07600c581490810150742d032490300c880219801040842c550341c840c2921151552034140c140e41140c00d0208100c41c1500100041c2652a4103e070301c2122400d164003072114403005401014030310070660102c41c0b080d004508205020b0100c4000702c1ba800080700c032122040d18415900701c8038445540c0d00728a501d05d03020700c8403a807201081c0c00410746464070304030020501d80040c101810300f100c0c00000c91461030282c1c0144203020f8001d4130600c07481c14040d04455807035110201c10380785030041041010315501054212412a07030401c0081000c01415203a0100903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 378072553 1250 378071303 378071311
    0x10b0103050c13053006340f0507080d05040c1d0402091003050f0d0f030e06040f05070b070b100803030601021b0d020a0b0a030507020f1e0102042103021c17 69
    0x110b40c480002c09400014064201e086040c0d1324007425050400300302008180d0441f1060548601c02c160620072007001107980180303840950b10b48000000d07440c0c1c00c00d6480303106001002e0030700718000508014007001c6e40c018500892044039980000c0b81d9901d407048865030040c03030303d658003104030011030301500d00741b20070981109102010080f021760b03a0317407002d142c070b1118070980742c50340c1000f80e1113200d00d0f4100d80c450940d40e40c0340c04d0074001c1c850a105004e480f190024801010704031040c1c0203c6c140035003004000040c01c02d048000341e80d41000c1c1041c00d010b450445500000900c0f80c080410070708008000e803401950706800030103064580d02982c2250250402d102ca0300055540310a2000d41d840c0041781d802480c0c0140780907561981c030345005040d00c0004002d242954840c0485441d4136900142c1c03401410901a0b02200c00d070908280035000e0712440e80181d0000042d0010401d0081000901240d0302e80f203502100c4002c0850300301400ea0040c10103280c404504542001c030440445112030641c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 378073803 1250 378072553 378072589
    0x6050a0303230301083a180806010807170109020319060f1b0305060102010b0112090c09020a090513090b010e04030e100e120a02300f010b0103050c1305 67
    0x5201c40380d03941c501c80c3c10980c81440242e12110207801c1c1100003800106070700c0c2041c641c4240c0c0000b00e4598140300c2e040b0301c00721004c118084500160211451807002c0141801034143c1e0b52a503500c40442c0d80d10302e13043c00fa05424807885a118a885601440b41400c4654050702400e01800140491407840d0f56200c8281d0b0481e4451403103c141511502c10020311041a86c40d40302c4000c03403d00001c086030002012507041da0714103c4890381f41d81e04001c803c404004c1500c40400c1d00030840c940002c2500482e0302002d9264004240c960640da0010f26040603540140c86005010400d0300150040d00c0c21400081c0c0181041d0005104803006074a1a03944075009003040c0c4494030403d4041100c5002c41d00400d40010f61500707a1050600e80712030209464440c0d40020100c0044540004501114030780d22800004151010023000c00b200006113a8038a080500351200f1040400c80240070700340503480ba41c00a40303002c1c002401c1d0080031040e11610307405603148540450904052124401c0c1c40482d00c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 378075053 1250 378073803 378073847
    0x20403110f06120c040f0b0309060f071112040302180c0306040903030603050a1518080d09021c1511041203033810020102120f100b031e06030106050a0303 68
    0x402d4410f0001a0302881508004585da035260402d00b80001d8095081000646410014442801d40020700359400c040c4102d40d440c0c0d039445010060b00d401c00e554030b071b20040e8000c00d03003d010041460009081124001c2e90703840140c04030002103030703945a401ca511002d0000144007040d000d0806600c60100644203040c001a0f881e05c1c0d85034030b443c0c90f0600304129000150007141400c00c0549020300320044030480d8003455102d926984080c4140905009140501d941d9035041040d5691209204100c0e14143d4041228000130305005086e150b44c00118041c40c0c1c10302d03650729181c4086c40c01320ad04651000d5040f0b00c0d030443c0d555080300a41a42e03050742150001c0564511240307242032400f0b0348030100c1c00c000710701201458410320070005400b85840e030640e4410300c03e29802d14205c100c030550080f84841030f520075540b5407004589129098001d040343d61008420418a880861391881c0710326144400c5000a41d1460700301802d03102c1c82d02426820414051040001900030100300c04444440c98080d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 378076303 1250 378075053 378075067
    0x32306060d0f0f0605010b0d1526010f0e060f061503010501030c030f0e03090909031e160615060816120e01020f0a0e130234021f020c04020403110f06 66
    0x442a90b42c2a0007180206030009003148c01032402e071040c001d004203180b80c00748806203401c1d210720070044883c1c041020040000c0e9506007a48080d03102c2d2800042003401008108500300c0000c3e51080121020f9120000741408200740340b800a41d43d00d01d500d941c001c61444c681c2841c00440150281044a005158032500405d030006c2c036600030444071640e240021502e52900004100607982c0141c041c20780303a00100b1100700104d5000c05041004001d01400a9950701941c030b21018101c0d240c50050141c42c54018000d4a640c400c03010102202c1e41691003450503150708200d0f40b03108500f030f9081004140d800801120803c9107800c201d09011050000505000c8141c0740c845403640320030100800200f64003507145152414100000012003061000c5090091100981d00b61030207906c5c020301c0c0b810f1220020900000c80b5000005842d502405809950000c0703200c031900701e601c0214510242c021a45081c04c50304143c402d940440341c0240000c0e2500040205001c8200c012a19960300081e0800240b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 378077553 1250 378076303 378076313
    0x1090c0201021908160908060a0209030a080a0503040c091404110a050d060219090f0506360913050307060c09030b070906120c020606011d0a032306060d0f0f 69
    0x1262540300c3ca84a0303518920f0440500e2004403000290300e014410911020b1090020014000b6440344d0780c100010b0340e800c0d00c03200191500100c403500500c410000280d00c4522076002c0051809144036400e210b115685801d016811780f00f0550b90704000040c41030001c2c0c0803038264038003601e503200301070b103500c58803903d41d07010030312510040a047c0d980540005007400c4400c1c1e00d1206c424030000d5841e005044900b003845600d0405500e01c501c038802c40c00800c151010282115042c098602c0075510314503110300070007110f250903500c0c510403032203400786d5000a90100700503502440503e52007006180303420b4017550350100605178004501c04000e05408003100150840030624000c00c2240c440381c40341440e1401c014100008405c02c0c014040c104034241e0029030700020b0f1560044001d0038804c040030448000c01200303808082085502820400700001886410646007000240ea844100010b40044003a07682d07030441507511a03000480001d540001c21802102d13455554859030480c1b8940a40391070b8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 378078803 1250 378077553 378077587
    0xf02040e0d0806100315031403120a0b0102060c0421110d03050706061d070f02012018040501081e030c0105070f020c01080709090b06070605040501200c0601090c020102 74
    0x410800300d00140148030040c9054034240c1301d00e4080b8a0140001c02c00540000c0b040300181c840209600c07100310500710420414010ba8800750710140c403030300151911000620181291160036800341c010722000c6144040017a0071602600d6584801c65102200c080b41d200255589100584402e00c0313070752003041e09031380d21115003070801c0c02555099150010340c1041b20403954154051442180f1500c4155900317000580c5141e8003070100c0c00c040a40e8416901d05901414010460410303d140c2a010350006510b140064681d210903040e660150040007010f1008855081c00740a88986c40039510f241c0c8d0302d041c2d4500401c6181190182c908100c2181d80290030b4490998800300030070064041070429a604104040b00303030809107011121030400754005001c003003e90082c00307022a01ca0081c2d040b203403142400c6404a41e0701c06000c000394030301070501034000c00c403c03003440e0f2540380a00d2584090324030241c1920f0041c489000907204c1646000001002000d08030203503002e554092014028961104407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 378080053 1250 378078803 378078823
    0x60a0e040c090509070503040f02062505030310050105070507031e06020c061603020304020a03060c050c0a0b0610170a0203070e0607060c030e01021201122d03020c01080f040f02040e 80
    0x720b1409460400c0100b10190b60020000010480d05000704070200f13407031051018200e0340546605940d0032540d50b64010741d80c54828070f001341d0005042c0b03280030040000000c1d031282d0f840401401e042c0e030300c660046902d071040b40300c0945958001c15060010850500444510100303010781c1c119000c91595600041e600040c2280c81c098000c142000036400502d040a840c02580385002c620b18502580003d5040c00e8900003d05115991300410200301d00400c05c44125040b5030045980711a0740b0300d0442c1607507104440c200e014200845412045d01e00892046008001c203003020481c4d5690500390500035040100f81030304000d02040d50b2021615000c00411f01c041c082c1c3c0c0b0114404104000c0a41a2031140300e8904090b1b00c10810740e0702c4d034004020650f05540c070031480b4102401c518204104800180b00e00d10340d0600c2143d440040d40390725010312618079403094090b120748844010064481c641c045941c1e2250550442c002400180d41700d1a21f0351081c4010000100a002d4645135890400101e03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 378081303 1250 378080053 378080057
    0xc170c0a060914150d0b2b0203160b041e090906020d0515100e0f09010f0612020a05030112020109080f10050906070c1502071a0106030c08060f060a0e040c 68
    0x100c000e0240e0080d41c800750311075100950700d038440a1321a02c407071007851080c052409011503442e24054034550340d00101d0b1081c05903513a803184003c0042100c815203880840c030300b20300c03e00c21007007440c040c640e1440c503030030465401160942c1403130b1621401c228450070308850315005c90541c902c0821041002d10443e19404d00441c00183c69580e1003000c441114009007244104442e550400001981e07800140804100540b40050740702005001140001400703990721940102030b0800458440b0300300c030411044801079618070250744201244081244074130100d440001d0402c01c01801916a40c40c45000039501c1813504400282d078640c4060b00380042018180d4030303600030415072100c113491401856040804d203000740082c0c1c1840d10001d420040342d810002c00d026002c980103d8400c1d2994145c0e400b26030888021440000b100da11800618002d000300000709103403080d102180c61041c2c058900c01d070400b4001d803000c01c18240801101ea00312807000d40c00c101c11102c0741c0300f5075112802802081c00081d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 378082553 1250 378081303 378081317
    0x414031b0d0f060605210d0c0804060f0221030906070302070819110d02010e07050a05102a050c011e0e120a0c09021809090c0603040c030515180a0c170c0a06 69
    0x8141c0d401d08198205040c03031704011880f212394012034115000c41d0110340883c2800b2a0300694203c1c1a4182611450b00c6000007007010401130600b220400210f10a81c0c440381580c46230f80d10180280c040f80142e010142c5205003d02a490503102002000285001f843c140100c0d8414074140340e0749010814201040142d444401c0c14891900070000e10b400307881c0489180c41486d0420001c2400e00031b08141141c01c10110360560901c2d60710030101001c441c01400d8407040910b080c2e007040c9643d0042c8100d00c0c1e0005020031081d80e042030002d90700801d10381d01c5580f1440c101c2c2d062801c010ba000d1030224050300c18000c03624114000f902d9102000c00800901d0000b68607a0000710381d040c040103402c040507005507004800c0004446000c41d0504d0b500c0d10846d600d0380c0380e403607038203020039050380907040105580319890b0880c90300c0d44138000c1305100c0d010f03400d880c180c01a5030b011881d4465502a0005250300d0b00f0800c2070180340d017045405001860f00c04111082c2400010010b0869a2250300040208085c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 378083803 1250 378082553 378082609
    0x309061812020c03120a09030c060807081005090720010212061801060504060c0c05120a060b0303090609040e1014010608091504030e1201020414031b0d0f060605 71
    0x40d8059441001c8503a0010301400756880307020070b8841c0c0b049a54440342c2c0c84009071a2803100e01030000603020b140c01c05000d14149841d0400500742100660303145010544800c0010004424005c1c0305007526400b60000000da11800402d131030040c0b81200700030f0307182d03c0700f41a0454803270709202070030b00310005c0114000300d800c00a007404800c100b4110411920003040300140086500041250206da62519002907140c0450a0040d4007281c10f402041d8861086a0620030000c2c002400c903110170b0041c4402c1114031070020406940e03204d010b41007170308402c041c01101e44078501584140707415002c01098134280c04090300418112508540309083c004241d0005109407a8460426035210340c00e00c001b0514400d58442c107a810800040004082003068081a0b03410f40340d143c4040241840350000f95150707071701c03950303d10b9a401036050074034042d100d40080809100103601e50007000d502c0103086905441d106403101e403405d074010360068034800d8907014001410749505455480c0e11240d00004424020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 378085053 1250 378083803 378083813
    0x20d060f1d030703050304140a0b011805060a060210150906030b0103030815031203060d0b010611150f040f020316080c010f080610051309020c0102071208040c1503090618 75
    0x420000c0e0501c103640188503000010b0b400c1740480e9000b540141c5000726000302c1d941007901d00015403038006d01e43e006040c000291038101060880454110003414405943c4460611442c484548110340040e40402415409800c0c907a201411669403815490b103060f844020761015540540d204454401c03000004006240e03020198582004585010b80116a90000041e039610000c82d440602d120001003c98006e03501c0f201009041c039402020f0441640c1e403901d02400d484641010314106001d850710200c41800c9075040340744a9100300031000c1050321141c0700e254080d064080203d80501c20b20300705c0d0300b054800c1401c000041052a004100e411048800140403840e107500500a1000e60428008181d80341040b0034110307142444c04a442309880d034507a481419290344440d0800d4800603c040c582c3c0c00640013496041e0154480c0e40030052540012140500211006082070380a03210503c0b03510100d41c2202400c410f43e140c042100059510380302d0491b403454180d800c8080b048204201046 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 378086303 1250 378085053 378085091
    0x5090301320c03070e06070510050402120102070b2a04090207060b060c1e03090d0b10080d0206160c1e060b040216020105070501110a050c0f07060e010309020d060f 72
    0x840490741222540c01c002c4824141400040c0c1040706000d41982008226251031042c0e0709030f00d400200710f8604501202071980100701c1500c060b405100e407100500c10103a0140212050a0b5000d4038082e11956000c5141842c07a0030504074213072154100e402e60840800f048007400103400344010050b56804207140000c12110400c00e954001c840c2800030071103006012074200d45201d165030008443e651102d0080c0e007180b00c1c1951080d0700c02e01300f4004170140102090080d104854860001c00740703070380310004690340e10000e0306854016440180000ea61161000003050b0300352403800e1103005010740c2d646451610762032400b500854051040c8010a000d840e000e100403a400907241141b03400c9052807801d500003807030b03507010341801400039110b002c01c0360960028406070034415a0030380b1105d03103000040980e0b000c2c11544155104118010b5000f00c00851004121780c07007926a540031404840054014190070076081c0c1e400b5141004c04401710b813450055495020700c0810004150b158040a40024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 378087553 1250 378086303 378086381
    0x11030f010e030d060f031a100902030106032003040c0b0f0f040b0901120608100e03040909080a09080c0102070303030c0512100906090501030b010e06030307050f06060a29090105090301 81
    0xb80120b0740c100f02040042c0300200c1e47c02d002d061044d003544d85680b4407491410b4207030310981c030b02e620002c00065a560f0650140c00410a03090328030440c0c5810504480f101c0c001568081d140c003c0e03600f030030858225010002d001141140c4200350038402c507161107400540041c0e0111603407000005a024066071301c4611050f08006d401c604201d42c500300141c5940e6501c03004c4495200641e5101405448582041510b00130300040350305106040691402e5002c1c1d4002100500102e0202640416040340216070100c2e04c1406034010a005403031620200c01810104103507100b403003800c0044c0e094914000003010301c510f42030580b91a6031803070403003a0011251151700040a40e440c20b4014000102e90302c0303070785044407401010f075a0191a580c2c00242503125280e8001e00500c2a1200010104000301e00c03148140310480b185401980d80e0000c500e010758040d00e0030080030065901e0f40403100c0d9040c0c094460702a040c0f511a00307041c900c102013030031101458241040100d80813900481d180c040e6006041e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 378088803 1250 378087553 378087569
    0x6070314041212030c020c04110903010f0605120307080d05040213051303110d020309061315030b0a140d0312110f030405010c0504030c0902070215031e010e0601020a11030f010e030d06 81
    0xc1c5c0040380000a4840b0700860205104030f4403401121131410603502583d45450008008025901c5007510702c800600161040f103004941044054404c0c1e400441500c1c100354000e4461880e015925414034001d00c00100b08070381c8540850910004020b0500c80d0501c0b03200304460b0700c1446440340c10040d01405105050040940c410801569803680c044240c502080c3c045e2510740c1ca0322422002a5001406900032401d0202d40003070201100b68141c11080708500140c030341031400c0e9190003011b0007840c0720701c803641c1d04211a6581300001901c03c002040f00001c900e1000590501d1f01c0c8414400d90344541103a400d10b0401000744010300c42c0078807802003148020708050789458075640c0e401e100c4140c0c82c803c05402c00d03400700b203900954850542e14098a0001030010350760307141c0f100c0b10344607188170003540714000380100380041508075045100780c0c01120160003c0081c40420350319440020603441a4a03014090100e6814201201f40180c00e070f8120080017854880414010304400c454043c0e01c6540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 378090053 1250 378088803 378088811
    0x180310050114060304020d0b09030a030c18180b0a080a031d0d0b0702120403140105070e0f060a0e04020a20061306050919050601181a0607031404121203 67
    0x11120b480d015800450980030749142e5100e40d0303280000f070101c5417400b0001e0000001c03042041165140400141801003276a2410072890720f803010101e0f01c0001b500141218645011418010408544042c81d070810b0113442c0411900c0a080100e03003801140d42c004210f541c4000404401c254006c402c203010f02200c1824400441800303400102c80302000c00025200e44c50442c04602d0051003401380000c0780c00c01e2407100d80c0d1b0380c0c0e43e880d040003070070b8198100810b5546171402148215200340300c0c0e070815010080c81118103003030100070031501d1b60005601005020b0044c903410080c0d115400030b403910000c6910740041d000050b10041041e0700140d441800f040d041182007107400103c21038101c0c600c07a00508002920740d41c080c1d401e031500300c0f05000901980b006030701c41c40810000042650503180100d80510ba10a03081c02c071032050312010b00da6070610131400c0c0c000341f80c01e0504c00c0c0070300121802403424110707024501500c41c0003540a0b400124003aa03940d10300906005a118000300140d0a5180c100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 378091303 1250 378090053 378090059
    0x9050f070c03110105041a0a0b0a18060905010b0309010c02030c0d03320403020d0c03020a0803040201031503050d091d06010e0f1017011208030f0c07081803100501 72
    0x10800020041240302031001000201c1c050522402d0b410600d000b07148001c019600389070400011401c60f038143d2a030b002d40c294000801c8800d4174020220b0740700000e84640c0b141c506005018803910501d40d51921016600c2c4d01c0010b0016050042074000c1c03c5c01d482295480c00c044419a007510001d841210555100300305081e40d6041c00104082000b0b854075001a1010801c444a01c82c0700c2e14046413441c0400c0045e070f4000e0182d2608040b4046ca00c40d1f021178500c504142001d070b58915440c017000c2c0140e0005a40900030400c500c0c000d41e4014414540000c01c001802c144002a8006802c11303250f641c03140c00382000e2290403014160250010a8502c803100e20340e04035603006204001d18160401c02003020101a07910380348110404030a00030804130101c160080020a41c0c0565400020000980000000e03040f100704001107a06070400d41c154610b60b51031001031600500640703558440350f01000004041141000500340381e400c920709100401040c0300070549040c011014120340a46020010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 378092553 1250 378091303 378091321
    0x6061c0515060a0c060f0207060e010e010e070b04060507050c040504120e010311032202090a0c0212070f1b030827120c10030f09240c020705011202070c0b090a0905 72
    0x4584c0320f034010030215a400c221070841d80640a01603006048505000e080202c6100640007400d9a0120000030400c0c8805000025079502180c4200c0a4180d0100024040b01e8412001045c01070301410032101780c54003c00103e0102c0750200e84c19101a049000d50401599211900243c29002464284114802c90480090506c130140c00000041100343d0115282d00d00000107100c1c3d00d8000b4500000340ca0807440d13082c05019004c441030018001c4012580b070760071403042a9903090380c0000c045170b40a4015a500341088012603080310fa010320b8207400000249000d40281803a0294803210084100040c420030324803648036400d184150030002c1500002040007916000030042103581220410003803406500805141c0700c40c001c00342c1000c0f010818424141d40c15404007a24282c5c003540d0104901800c012200880003d40050304180c40030481503104001c003031814100048010b142141e00c3c1e85101d410fa0440d84803000741400411044903600d4188000c40050040190a0000b40b8100c06c01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 378093803 1250 378092553 378092567
    0x11b17160203180111010507080115050c0d080403021c02070e060108060d150b09150f0102060903070204051009090c0504052406030a060803070606050f0d0201020a030806061c0515060a 81
    0x40203912801c1501c11800f03581c45050740001c03030b8032084001c01042c101014001c0c0b10000900906442600003401030640a1040301164004000c05000c5c00201103100002c880f81c810145c800c0e001c500c80d45c94411038150700001c0d62a1150541c0d00145049803900301c40001c0d1440040010b81803080a000f0440151202010b040c08203502000058a0b010041d5407840244441d02c00581c100c01c84804005905244501c0414094400c40d09c84128181681c0126600d05044950340c02031b420900c0002c0040c03d080c0c01c103030382090581006004598450420038100e95038400107441d40d08403001f0400c01c84c242841f0781034200341c80892003c000c2480303c44005c3c3c41c414202403140110000800030f00760b16080e500c020040d0420000756a510050303030401c8000b50a5600915201e90a4180504c4041c90983c0c03030304001540c180c0203456240a15241551402d00c000d0199400620400105881c80e2003120b04401c020b12646000070181885c1c140e41003410203852485000751000c00c0031580042e00001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 378095053 1250 378093803 378093817
    0x60315090f061c14010204030602120901050408040e060a030605070e01090e01051e0a0b0408070f0f0f15020114070f0206010e070e0d03030908120f090d05030117011b17160203 77
    0x8011240a078035100f54840306a846030403985d4030210b13001c402c010258005110004c0b03040e199495503111b050260742201c80980b001403441d0020001001101c08080581d54494402030580300e00e01d07901e4407040300b550002c90780107001440c00c0d42420306c25a086030301704029114190b200c1c1e0b013540c1064080b540008050400402050740510501c0d116070718554100c02400d40e00b5242d9480301d40c0c80d551159030f00510b00501d1340c02000c3c0e100201d842045d227000c403c11100c4414903800c5161078600ea60f21a000400720b40d000715500c501d620b02190b405141170b580a40d1044e9176034a940080140001e09295060f00a0040d1280500500104540c0110044041042110002c48294540ca030650007448001c90080c20740c5c8004c01d510503a5040550701074814040ba0101c40340a98a02e8646031701e82c0c0400c9054800b040c1e00b40010b109010b03850000e00c00e220020000020807c080040c3c1041d9540a8600b81000409010036841906030069040b5009142504407611000341090701035124040c0c40c3d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 378096303 1250 378095053 378095089
    0x80601050702220c021219030203070c201011060412020a050a0b0105040509010e060a0f0204030c0e07141215042703020c120703061109060315090f06 66
    0x71036801c003036686910140c183c01c4910442c040c042030340060b602d0040d04200d034414000d40141860000f0385c1d00c40301300700e40045118104c40200c0005a034020b500a400150540c000c000400f14110000b0b080c5000c2c40e0710341d030f500031104091400d642e82000141c074401c03644d100800c0405e2580e40c1c030446000480c2c0790410303440001c21094003480c1c042280383c41c100075000f800702d100b10a00c00e1709101c51088014140c4006550600503075442d03d0201e42681c0300b003084c43c1c0441d80035000094002c0955402045101d10302c440161509960380c644a0b080001c5403c24014440d4034418480701c15081840b40c0f01d4400100010b50038076005107021650344100070300c04141c01c441342c5100c0c092503440303078044208c00030750740404024401c41e540310034028136802c94110301601c60283c00309001d10300f900c0c5401c980801c4000419403142150ba0307210181900b1018400104000e000e4800c0341c0c0d443c03001551080c0e840b0f030b489406120040040164100e0058200a0a40f07038030014405140c03074030114503507000510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 378097553 1250 378096303 378096307
    0x120e09010b0d020c060a020717030c0706051015080f060405011d040512040312020d030e3003092b09090b0342010609060c08160312050907030308060105 67
    0x100b650080640300d20001d00840e4000d0b1402c00c42c141e038003a805421180d0041c14018510840b4285106a91000355108000000c06100c188005900340c0c010300e0780004800c9542c49115034540360071222030001703c0c40e0000700da001d400300b104881011150543c04003040f9018886545400c01c008003038a000c0c055005e4007a440000030f07052180401100031281c0c420866155103a5890904148a40782c1201150042c0240c000485065200c0e00a035200310600784003602400c040f41085401070130000019044605100340c0e04507540384000065886807007010003801d00c0311600c0c0340c289402d103500c0046100d2240481c0c0307034202d015401510b007015207040070f02c001001041003000a24020291100c0304400308012550b404100c1003003107038000055003207000d4655007015107449035128400d005040015505810400015115180401c5603034000d0300f80034030b002180100944900080070095021a1491800300829100b5200c5c195001800c000981490382c15036030000c0440c880681124104000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 378098803 1250 378097553 378097567
    0x40c140a0507020a03060618110313110306040507051507110108130b070f0f03050103200a091503030e011d2b050a030e0108010b0313030e060c0a120e09010b 69
    0x140c0200d414840c3c00801c0c003002d0f60382d07901c1d0a00c050041c1c0e00403241102000324039200c15120f1801880904102288a035040d5529006c4c80c06070702588110588507028201101c02e0f450318203011441c05240100090801c19061105000f400420b804248482c08801c00000001c240b100002e956918402d02e443c0403552a60516060004002180038107c0c4560303000340208585c12a0724000700c41c10710780718205441f240701e200341c2c1110424070010b0510407410f2107006000c0d00d1145000e0310058000c1464105580780c00104088502032120303040c0030000c1100a106250704608005000c54007441c02c140304903501c40c1000152500036030544d020342c00b40c82c0200002c1030003403807000760540c40701881c0300e07801164100725a60704102c050580124400707000380103095200703034000c605035600b0151051460315101140b0200081c402415001c00400d54510051640d508008140f00a070031001000a10310301c0c08d0500504003000c1000d400d0000c1c0b16040c002a8480802f000d0444040282032511801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 378100053 1250 378098803 378098807
    0xe09090d030507030608030d09020a06052b0e0d1106010506040b190212121e04050601170c0405010612051006120209030304120b01090b040902010e0f0a18090b06040c140a 75
    0x8070760001b448500000c521043e0091036580498401802111101c594035918102514140304071b004141000001071541c0d0320b4810f81d84407411a0002e415800181c0400010700f0038140061056400700140c0d9124042000e180200401e41c0904021945c0ca0b02d0240340600d034148501c141060310900f0f21604501e4194107001f80407a12540e0208826196661941c291543d11a0b03001c640c03804144c0d150311a05c0721912410821180702d20b0340701004100c0c0d41d0030308528113100d94940384082c8441c86a50307843c203480d440c0c90148a001b08400c3d00c0e800300c0851003600381001d56038001d2540318022245482007101680c4010007030004107070504010f030b81d021048040781c1140700b541c2014603403051504d10b00f0708003c10440011b04850b5200d008000811106003004265100c000001c0d0000e007980e0b1051003a80342c40d400310410b03280002c0144d08203e0369241e5088000802040d180026a901c032000c1041c0141c4815480d4486422242001389049c003140142111320810300411407400080348405c4064 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 378101303 1250 378100053 378100061
    0xc0504050c0306210124170a030516081b060f0403020d0c05070b0c0307050d0513060e1c15140108151f23010e010c02130b0d080702010e09090d03050703 67
    0x1100303040080c0802040ca014115061452240402c401b10302e581340040c0f0b48001e0070313614000e09080070140609910b6502c0c11506900b100c241d0035825402580d90341300165900004000c01200f1090342650032a031503e2950404074000c003807404800c0030310b007003200080d03001c0380301c00c5852003e00344596080003d0900c10b2a2124a801807500030b0400119500803940000181c40003a104d0001c807603041c40301010450b058003a0a0381d000014050100c01c0c0032071401a1003040c5010f034043c060550703904650000b20700c0202805010394805000d800c5950340103905009031304403640d02084407a541d500d0526683c0e0f50703900c0120303c0964400558042038002807103e038a130048040c0c44056600352501d45800b4915018104485031075254070001000b0b555002311042000251305031103041c002183c540034401501e20901c1040c2c41280e641404200990300ea4036504911409222003640311142440003400311654404480c0c82202200b0400252a40002d01c90407080380f2464081507949400c0e00a80c043c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 378102553 1250 378101303 378101359
    0x100e030a03050d09050f060f01080d09050d080c010507080a1a01080105040903031b05030907060f0203090d0606050301020a110f010612060b1816030c05030603031209070b030f040c0504050c0306 85
    0x80c001c036656810070060010391f00d802030200c0c400d8a4441e9980d0700e88640d8590b0701041031404580b507001c040100e894200664a183d030301480140c0d2800d96100070060031a002210300a0100c0e80d0401807210030003413807080c0f84501e80c0212140980441c0c10002034061541446003512858564900c0e4081501c2500042c0019050351034a080768810444045c1080d0403c581c00741d098070859400041c1184150901d91041b960b0781c02441c80e0508420621070003207a8000180c410548030300300081c998400744000c1211443d240c0d2044900941c980d41c03e030030002494140411b581c14404284010100040c850003001d078000b80005042e0300000202c0c407000b411000c5070344000d040d101003002d42504031440c00400b8010399801c100c40c960901095600740419140e254040e8410300c0800040d42c1e10100342da800410040845e2681942c8800215259004840807025000038100b070100304803840940602605040b501400f40c1d18210380101d000e4000109041d11400301280d14482e140c0e4010808000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 378103803 1250 378102553 378102563
    0x2a060f0e0a03110c0a050a0b0307020106080714040b030309010912110303121806010b031f080706050901021203152211040617090a0620070f02100e030a03050d09 71
    0x70403805040c0500600715001c01140180039408001d03009107814018801902d00040020304140e04190680d41160401007410041d136584001c04030398988100130150050100b4130811074610060410b00055a440d6030009009a005010359000390fa04031841d80c1c02e90780f983c9003200b4026042d0414600d00303a1000d82da81e800d80030000c0c111242c0040d10b180c040c404d41c3c45200c00c1d92054840c1c880e080d51140e0034400d402810905101044a1f441d240401000e14800d200b0010030054440030558103010032944694089980000c15803441e5030107012000610203401080d505614004018104032002c42c00100c2c40b9070301e007a0440c50b141483c2d50790b09024014400082049480409200900e58060f018010201d055441c0034401040130710030700b512802040002e00945107165035080d01821603606e441d000001039411000244082d031000d0404140030791524022107810f401030000901c00c5a05800c10402c41e01105022a00c0c0095000c1d440c03507040ca03285644130308000c811801407088240c0200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 378105053 1250 378103803 378103813
    0x717150705130806010603050108061618030b010f0f080303160e060c030d0614060702011d030111031003060c0801030218090102090d0f06110909010e150607122a060f0e 74
    0x41c60f001c00080680c1640c8640c2c904011590b2117001301640c4500c200d0fa05d5441542002a000595200c0c010f40380000031040281140039449039101007804000b604601e01082c07078204104400508007000340e0044c018080038601e9420400007000e4450b1891070321070305020b00b0310f224855a84581c012a200052244140c0ea00e4000782c11580d00545002d12907030305842070342c0360701e0015860305100711860b00f507050311407900c5903101041200081d5441d5101903810b55a50a070301302060400c200451160042c2c446602c0014118640102260003546180f0100102d000060005032140c841c4c1c042040020320036036209540c1d000e54507019203e01e01185400c600389080038001c01c0380340490b09a4084c4905001d1104a6107040c580c6030034001d0b116480d44c446540c0c801080480c0c000268281c1000944071507950322846003000c140580d20541c42200c0c80050385900c60042176114003c90b40c01d00248003103194410061800359607010034100050500c41d508c0f005401c0c03a50003603118a0789044020151741e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 378106303 1250 378105053 378105059
    0x703022d070c0603020a02160f030213060806090a0507060813020904050f07083415140319150b0406050a03090f05031c0207020d0807080c0106080609071715070513 72
    0x11301035001010402d000d8031966400d0750602100d0f0b22280c0c10b5882c0e407034022030141c2c5507030200081700d01c3e0b045400f00369035500c50000c1100ca10a00c800c03807040309054014034210312680ba015180c401c041d44480d00b085144010301070b1401c03001c01074580550301120130b0f00f482e480f5410024105100400d6207001d5104003c4001100240482d007078a0b4a4440141003001200c1500c0300550b0506040c01010080d08828042c024240c0b28080c1601003425450000e2542d1007041d01545982e10a0300c1c42d14226515001484a00301c1c94050200c07081036a040032840c4900d040003082e600e0080340910001d10401040d85c0745240d01c00c5d4003004480b900200d0303164254046003801c81c0c0700e038058040075464040c8003070035010294143c001c0780c01c4030b9409029410318051a8a0b0380d2401d07044520111941c038420090ba80c1c503040240610f4001d000703480b02904c3d05d03062181c032071071515205901180705460f0342c18040c0903090000c280d02154841c11501c0e01250769030b510045850f8803c00108101c006081c1d0404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 378107553 1250 378106303 378106307
    0x7030b06031c09061202030f0a020f0706020f1b0d020d20071706010e15010f170f06280509070917100c0c080d1d0f06060301050703022d070c06 63
    0x20049480a031a81103e200032085d61006070300c0200c030304440300854440801c6142540b0f80c000e11046d806980b8450505c180f0f6034034281640d1204843e00f009010104407020030040200d40352001d40e40243c000d103150100460041d40300c4540118040501808001d0f11249080302a550300702c10601c00c059654841d160404072262005109600d009441a50008110540c00c80c0c00a8010b2107104c4030400c50f0a590401141c011915400e84405c1150304c4030aa1840603d2908050280f0502110b1070030760f01d0001c05201c1c0c0016031300c900c614504010341030301e104030756924504400ea80e016503401c0510303a25981e064130718820684c0005038a01d6149200016228045050050760308442c80c24031980e00d00d8001100e580f100d00703c0140c0307845010001d24400c4c64050380010354101c1469120031102502c01d103510b05209866140030707000d030030010030018035113001e1056a03130040c0c03141011402c00c1c1051452001c0341c000c0e8500c0c1740c100c941c6134454501c1010a45d06460b0b101e54448007012034180c84441c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 378108803 1250 378107553 378107567
    0x50307030f060b030a05030f1e0c1e01060501050d050402030a05120703093201020703060c0908010b0402180d05010e010f0603021011210c010213180e07030b06031c 72
    0x1003550b115140c058000e07110714000c9800414180c0040c0118103090101c0e24414169102c2031070207009601c101248440d0411a0010380030582000003d01640246c603039160810341180c0c1003810040c2d24044050001d40c0e005400d45034141808280001d250383c3d10710119140c040c440b2005446445013015440d18a0740400082c62094030950740c806d07030b00e540d0300c0b03101d140003a0f0882c0d92814002805c5810b40d5441c003e80140690030b1052040703506c40ca40da41c5412003152120400d002c00036240140520649900740514803840800381e03800c514283d00340b60390f40440c0e20800796440c8a105071f107041300300b40000bd41000342404410402040b1421212103014002d00c0180301c12800346040407410151603008034a2044024095000380c012042c4210045004000701000c008445006110b44951306c0d50904c058841c00d26a80c1912080c203007050b041074a000601070001c00c0c00f60904140750400d0078041650011030354400c0108415403540030001b424070103a89003500d0442e04145030b0800603a0b215803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 378110053 1250 378108803 378108833
    0x60506030d0302041a09040b0909030c010e0705062b020d1d150403080907030803040803010509010f030f060b040905010f1d0705012106150206041704120f02060405030703 75
    0x1c41c0d0140c50000801d0341680114401d80d600500242d0b121511080400020448040d004100040000c0400000b90402c41c0a448c0030640364030100b02204010ba0920407460b510001000610a49192000180ca140318030403060504400b41c2809880c030749500d55801d009000c1da4581907441e07403032510644000b040c0c1c0080340548100c0244107034414480205200020386c81c00e1600c0411580d450728103960780003000e0407600c004e2180b101700102150034000994040d5119401203540d9504d028100842c00406800401c08881c503160b003040043c1c01c04e98150065903100750042380c171603130802c00a0000c015520000d800d650802850701c1003000b143d403200071078140141528407ca0914440156074825600407540440d0780500849500141e059401c03000501091700410340c10b8450050449a000e1b481410f40503900c2981400104009d01075000f10f041200f079200d500b018a08a402107080502490161003507401082001c1952650300460340034050140454200c1d0b80e072442d2a00a00d04200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 378111303 1250 378110053 378110059
    0x105130b100c03021506010c0b04032007030204050912030712020405040606120c0302090f0d020f040212010602250504020c010b0405100609050d12050d092909060c0f0711040603060506 81
    0xd8104101c000c107504c02c1c41c006c90301a0b40d030310f440341c0450303890181c1c1413800341c0150188a412000c0800a401603c40002034600340409484421300e03501c1030106840015140c2446c641050024900648448058950107802803500c00403a5080303241543c02440307213402c8640c0044c1440d0700803c1c415003101d0356a00180000360100000010742c40110104d008941d0b035240e0001c00c0c100541c0b000c0c40c02c0700459002c0d0340004c007103c0100900714001022a884010b41590901041d03004000042d0144010306401030390307500804840d050841055509103950107424421540424506d002c200250b02030690514040c0041000e800c2915141000e004e0070310940000520100c0c02180c5401c22360307040e00e4106d42c80617442d90b404190100a0720180c01841d01d030b40071a60f9a1009030046031220b66040b05007185051290480354440030398403041c440c001c00500b2168070540600010340000c0040319841480203050740e880e541c9603d88401000b074441d0290703500508160010083c054031b41c0c0003034041e940c22 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 378112553 1250 378111303 378111313
    0x60a0e06070b0f090c0102100c05091305010f06050703020d0c1121010b060c06060603071211041406030906060f03010608070e18060408070b0c0d0f0c02070501030b090105130b100c0302 81
    0x781d00b4517944a002c51649401a04a10758603a10f8401c10b811440f440310960600a0606c0385070350104011050180541c0c0c2c1130b41d2a4401046003202c20000080945200c0c90f10a19004050b20083e54034207901c0721450400107020204d9040c441d40300703100c0207a22801007041b40c0741010701a090801086001d00c48400d54070b00700600c03000c1c3c41c2610845070f240e110395024100c0d81d80c0b0b00c0100b100716003006008105000100c480c640c2161a0782c8503407202000d040220680340d80c103080042c4a13000c0000c0c0c199004500c204184041d07100b00003445079200c2d004550700d804140c410740c0403074058810755000324050312030f2076000304a100069030454840c03080651600c503121003810105070303208016500500103120030080c0e070000c2144c5004003035100c42000c0d4090714158031010b00a04485e103810700c81d2852070341c85844040c210350620184004040900c2c0920410030f514000075080d510600c1440d1041c10706001480582849801601c0c4000c4d0007080705054244401c80680f10030144ca404170700502039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 378113803 1250 378112553 378112561
    0x5010c0c0209060d0c140f120706030c0311092404030c0302030f071d06010903120c0b010504060b090f030c040509070315020301120321020f0405041415060a0e06070b0f 74
    0x903aa404413582c10000380e5905610b4100d80ca4140240c981d085904000107250350780f00e0b500d961715017804450701c0c0030041008514000b0000d0072070b00b1100440d0101030a14281401441c122403d0f41c10395802281d0750310031a5060055550000b401b1004408a00c00104001060040c44640601141e009406640541051512203600e030742941c01840b0081d50180e2408680100c221000755012006040c156501c81d120780b11018014440204000000e411001c071004100b140d141407801010140d5040c0200743c208608c62216004074284140240b03c81d10700c09003207681c1004802e1101c50064000c0246041c40e842c5192a10014003080d569184517002400e4860103900c200d80c100d07814544002075108507540c003101c060110590f40507a0414480395184640701d1440204221841e4084807542c0d14540b9043c8001d50704400b003080140f800540c2000b40c50307418952035009001c0110303804e0b03680d010049011303503d0007490081540c001201050842c00c10080e4040140034003802c02d10380e401c031ba031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 378115053 1250 378113803 378113809
    0x90512070e0f040c121e06021b010e030a03110f070302060601110d0c2414091207050309040e1e06070305061f050d0e010504110109050915061605010c0c020906 70
    0x400d0350f00401a14060360300304005055882c0c4601542d02c1602a0026600c0c1e060b40c17001100b101440680d1110350000f01d1704204d03042520b020101e940e222000f40701d8007004105040d01c034095071852000b071548403e911118400c610084030780c5070100c04e20694840d441810001d550704403c8031968042241e589402002510015a2029072130340c6a960300c00120141d607036400c0315001010f5900c07903180318000d0043c14984900460640240d19a408406482e06030503051425030415403e02d2014020030015001c1040802220f0004800382d4003c140501c501c41050f2400402c1000d0340790f2440c0107440b00344400070205096000b043d565038140504d071030b07030f80402045180780d9103040501014103000f041d10303e0040c2c0140002c040d03d59000500c170701c02da903440ea080d140210380444404100c03004a820941c0c00440c46006024143c415140710700c0c0c13000340f403003110001c03080ca02d21516010400005022030f110b111042c071a4000c000307120003100c07194090074a448100041748190711440c0000c030310b42 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 378116303 1250 378115053 378115081
    0x5010b0c0303160c05030d0b24040b0702310b120c13020c070f050a0e0601050322020a180606050309300301060c030e0306160f090512070e 61
    0x4403440001d14519142c200c03104849011003503088051020401200e40440e100380098245031014401c0860305140100c208445556070190704264000514180454840c005040d181600c941c2900c83d603550f1a0390001074030002403108403d0303102c0c00d0741c40c5443c042d240c000c22224030716451490501441061800b0418640c2001d01031091507030081551040c586040d8100081d42086000c00501c0c1400b444025810000300f50484070241da480f000c104624107000300003000911203988401a1420301000007049440041d10f8001c83c0c26044502d0000400482c1a0800c480e9005003644030751980d490210410b2902140480f14042c54043e0001c0c85a020b0b1048a2043c004100030b003800e140015424510311036951075100306506004c1c43c1c85c1c00b0f24002802140609007a44074040801034a00d0014490003002d14118045e401282c140704444420081c1800c0300951070601c54203039084003800301d8a0010f540c0c03140c7d5001d104660f6542840700c0208601c000d491440042400d00d80d20620081d00b05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 378117553 1250 378116303 378116317
    0x10801020a1202030403200102070314133f1e020603071b0206030c0c070f0f06050a0201180c1701090c03120908010203070201050a0c0c0302070303080606040314010f05010b 76
    0x10414108400ca1202d81941c011035010b0f10034140004641d001c00c00075050103407503440311111a9400a200001d1540000c2c4036801d01c0f010381045458249685a6000c3d098402c0c42004241d542044601c03500d00301807650700c92511410040c000d400c100c5901000720135046031f0000d448070418a52940304d20014071122000e010340182449165458460045a02802104041400b41000100500180e80b20b00040d800b890740c8840081d211b000c940402c1e810281c080d400b60000071f04141d020442c108100308214100e5055082582c0c031203a5615041c1d004d01000d035440f8030400302da044000304001c65a032a041c207035036100100c0040740d0503504d050380c221504040701500c00140c4601c00c0001458480da1030242c01c5c910300d012040c06565003410350980c1c100741c42860250f512070f4200650003480303208440b0002298a05140c4049041e203019455080f81d000160801c194200054500e07100c8004075001540d10150307009010201940a030700030015800c00241d0141020000603101805100390703003813 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 378118803 1250 378117553 378117557
    0x1090e0c0910050330030f04080f040915060f05040506040b09030c031516080705030f09010e031b06130312091112010b03010606021902040b150301080d0305010801020a 74
    0x6410315a104000c0c03021001403105100c1c036065000421503032414000640b07200380d010519032505c3c1d44018400f0030020480030342d46004d9801d100b048540019001000e410581224182d560340010f160014064402e44e040240f99504282c612560301c51b0071290b4000b1110710b81c2d034450031440c486104807070745c2c42140300b005d5000d88103000600c01282c00c100107060405005084440005101c0042424071481c00d280c0c41d1440c40a0040044610380d42c0c01c142507030282c5240c003034800c2ca464030000d440c50001514054202428400054000c0003d5004441c000f60071400c81c1e88943c0380c240b01145005030404c0300449030140b00c1c003060b4100c1459070000c0905d5410b03118004001000c41202009002c3c038142039a0ba030204620342151901d6201d00000c0183c104800801c00003c4d00c8241030a65015502000442d4041205213003081c1c025030f01900080c2c5c0c1100c010a4800c484030010301801c1d8902c01807040d48600200000760080300151020986596440c10b100503039907002c140f4200e000e07091000300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 378120053 1250 378118803 378118813
    0x30525141c0c030809010912090815040b040308040f0c08030a0201150e06090c09041109030c01020601050121091b05030706091d07020a15061a09060403060b011403130b01090e 77
    0x83c0c003800c4c1040d1320004090002608041c00d444031039602c001e5200200104015171414420205e00b40032048420340341e90002c1c174079030400b41c0e0b41c02d0004600810240070003030018042000c110101007545440c86d000b076103100f4050b4403140ca480e01c0354441d011060140d868141c0c202a00c4d49001e95120444401c0d01c0d10385110394800082c80251040145030000714041044481185d64443c8240e03009060000041c0f6100c0030448181880c0c8071080c0788030b5041d5405076004202582e0f00089800f262000e4514090b00340f0348a1000d040508490040100340c010521204083d0200d002d06200440ba000c40480e460180d0f500800d031190707041400780c0e104001c158000e040d812910b000d151500081c3c0c030300c12200e559000707446400394412800b1445003125250a0704105441c445940c1a8903286020401460041124001070b0b8034030592100500700d9840362000c0609038010130f80303e0801064118038a40e40c6c641407101c0107030845035020131a140810070001007010440c603c030b035000602c1c40b500280703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 378121303 1250 378120053 378120077
    0x1090e160302092404030209090606130b0604090908030609060a080a0f0c03050a06060e060a0807180209061303060f0905060f09070b0705030414010c02010203030103030525141c 78
    0x700a50320400300d0740c0e0040e1080414289103410309800c040c0b11500c1024090b00c82e4150b00c100000c80002074072000155001f00180541c6540b1a102e500f2460110f03880050b03014800b5002c250b080c0581d42c000251075103030407914414000820f000b940700d000304803042a05030362090200564403100c0e004004803948807500c0d16001900c440100625680183d00c0004030580e2030790b0b103510300001c0c0601101c585032507030790402000c40740b414410382000c421940101c020741812020344d0340350068450410041e000b03c811100b551502c0c1d04039800c0c0040a00360980d5008048031001500800c0d2004035040b41c64024120804811032146103231040d44480507003ea81c440c0e4100788030351100a42070948078014000000380406500c00100f401c80d105402a41d02c4030b00d010030003200b00c2040078407203041c0080e00008900507079000c01105d06603907145c186140c40b500d010714101c80d4403400503241240e030810048100b09110703042c51400c101100304030450720b000e4000c03618082842803a004007030126a500010b8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 378122553 1250 378121303 378121307
    0xc0905070818030d0501090e0105101d0a060801091b0f0e0c0702031f0c02070f0b25050a030905032512030c0803070c0b07091823070e01090e16 63
    0x40790b015680d11080302e041c13000c0c801d4680120f507403c2c0d00c0546190740d600d01c200b481070001c0c001c40d17038010042016000b01610f4042c121060420b40a002e80c107405800380040d8009450341c0c01040945103540007009000c04a15184241e0ac805080c017440114206100140d5940081c4081098682080c14004503858900d0a58000e800001e8102d0385030003455150300b52552866015200c00030301c01c1c004641800e13102c00280c28421f083e0000100703110010810700c008203c030411280102d074040565100046240c3e00c02040d02c8003400001c10380e0155010003014154007a00140c00e50f40201d0940f002d84a029049040d50300040135548401c10070305400300b2500d10f1590300e9050030b500a00b4125940300041e0342d8041240d00c2100c10b04042042001030000380840d0240140d4005914200b02e0502800d21030100640001c04071151440c68481c4108030920740303040c0071364034080140005001c13141420b0402801c2081390303004d190b000070011000007603000d080d0f408aa010f00b80403580e603644140a4402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 378123803 1250 378122553 378122581
    0x70f180c0201020c012d0603020306160918050a140601020d0f03140a0207060605090403080a0c0504050306070f110a080d020f091206090d03052e0902160c09050708 72
    0x5030040d55030034403a4024291082c02107000714000c041c10201c1c0c0c0c00c00340c24556200d01d111901a02280d05d4080d0038001030318009070310354000e48110784000500d082c0c1241142e4201045c0c03c0000f1003440e00115060a0020390401c40c0170346100c40003170208208117480e8003804481152844e00592000c00756016003409404085a0b1540a14012420140c030104c00c2c0403019040c0c42808005900103480014468941f050b940039110481e41160315092075280101440e102400c4211031070360311401d20b40c20501603000c440080901400ba9046440d000c54060308801d0517002400102d482e50740801c925070004035071108080e9010302d05608004c4c40114500007900312402041c0c50781d034104640e641941d01c00c103803500c40c9400600200404d19060381907030304200032207070503c4c00d050801003445080c0780da800f0f02145a41d003140300c40e03040c00b000381410f18503440e15600a50310144001612107100e6a840407501c0040e00400324004100d07a907500c02421510202e030010006000000485c0d592800300300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 378125053 1250 378123803 378123821
    0x3080403140c1507020321191d060f060109090216050a0b150d0b15360c0309120304050106030b01180e010c05090f0a09050c03040302070f18 62
    0x600340212568000801c0d80652202c5201420303039110001ca01d075024248141240d00c42c98503c05181001010320b07546031000100142c010451b030003600003070300a05441000c2d00455500d508103015104a2103010141c01c0c0c203490f0034110138012403001601011004084500481040e99000d03a4140f030015120025001000303c0d009120300461114045407040180c0314943e40681030304032040c20249450101d42d0106200380e40526404102c4034081654210460740c0904240002d04407002d41030700007020320060b11501d03400f084086010001c010071005500c00c403644581014281c60315910442e2032680005c03681180103034001141e901c5498072742e4010355049440341c000420700d207490742da580044010036080303040b45100c0c00c1c2d4030183c20981405125001c0080d50001c01c00c810380d034103000384a486516482802100980080000340d00c0341d416480060545400400282c1045d43c1701c80d4403903105075030640052040702d0010440000700d02840040365042d203590342400030751058034005450014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 378126303 1250 378125053 378125057
    0x91803082d090610080604031d040f0501080607271703070609060f0b0402070c0614070213090204110a2f03031005041107080405120c06040e06010f0e01050703080403 73
    0x1000880700c20019210324020340b0142d0180400e4a410014041c03926556842001d081c1d00071030900c40440c2d04411043d5805403014000c55140e1514004140035054001c4001016031901000040c10035001c0303449401402c1c0307a942c10b0140807a00c2c5101041c203905d1442c0e00152000f40c6001c0000d038a41070b044440c0380e480042a80d0a00e80d040e16080116116120f0070754445442d0144411039003190b104810450008071402c40c1030409584a001e01110103000303220910410394003140d21030b030300002075030320455000b40000c02e184c1c00020b00034013400b0702d6441280a141420300945001c030044d0140c42e40c9060170f64905013100d00380c010080385040c6446d400d0101d010000710300240308030140011071081c0c007a40761049510b442d00c0e0520045940810640e0a005818081d8500140e0440215001c81d0340c11100c42c25519600c801142c2042d0403649915802400010001901d1500d03000c29840b82d0003d0702d881300d402c02e1007a02900e40d0820b00700281e002842c20000f03800000c1c0500c1000e9007250282c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 378127553 1250 378126303 378126361
    0x3030b150f0309210901020c180a1e0c030605040b0906060a0f050f04060f12050c1819180b18010308071b0605041827050102130e0109180308 62
    0x2441920001204e0001210038440006143d042c01d58041149000c501c0082e02c03d0b201454a4400082011001500400c0ca0b01e80342c124810b6030110b185044000084070103003c100300c00c40383e48054028100780c0301d005c0c0603d003813030194805c602c0e160b28001d208050151a4626251400c50100c0c0c1c0e0400a000030000c0c0038041c840c161181d03c45c0b00c0640040c0a440e01e42840e00d500d00350003d4000044026a07036446803c180801110a11810076100c00166550b11401268610b1002503e4405030a0b0640301c803403400b100000c0c10340ea83e9042c0c81410300040d64200210f186c0788052181d00e940e190320000300405460300404c0080c81c28801040308034028400620012000d40050850400c01c0d40898001240480c090190b10940d50415180c07582402c800c110540f810f401101080107030300b0700020203c100030400c00621200390100ca00e680a4100c1039066a9200e0401085200b402e02803400007525054030f500712071084c1021807080d1601a01c1d0b0f034400b82c0d035a05082008880300c0d22032020804078 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 378128803 1250 378127553 378127573
    0x80307090b1204050c040b011d21010c0f0e030601030b04240606020c030304032d080f130b0a020709020903102a080709052e090303030b150f0309 64
    0x90407018000746a60100210014101410100e2400c000284c1e800d100341d10300102001d150303801c40181614a00c10303481c4400410703a200700280000f01c0e0076040c8548800e8035000d80c8042a01075001c2040b8143c0e03030b1204050015407210440f03554030390307540003601584107070b0040c80454141c8080941c4144100030116540c0314417040400c00701c0c05074140b81e00c401e445850a00c8030b59018010001030700c0d01900110b082c1440c50703d43c00302c900340503908aa200c850380c8200c8181c00800252014001d604880c49699440c102c08603a10b0f5544801c0781030300e40040d035040101d800b001031002c817000345109a009007600c5007000d2150000b0340c0314020060b414440d90b050110414131600a854a216040300c160ba0704d5503042400120f41d58000341003c0c00c0000500c1080911900800c2201c10740e802511010342c40c03400c10003103408844c06489818800d84010781140815a4094400c80a5a20965080c0184043e20050002e110400c240302502450103008080c4145680c070017440c0c4c807800c04811a00e07036a207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 378130053 1250 378128803 378128819
    0xb0301061d0303120403140906070f020d020904110901410429030601120f032a060e0303131106120705210c0a080702071e03050f0d02070308030709 65
    0x4000078901c0604c5201d42c04110a040d002010180008103c0c48070354a000e0861000034828441d68900605010b09841c8110640d111074101c1d126107076020303140310110304140c10810796915030f0601c1588503401d81030020400c0850449040515064140d100c03030840700c4683d6806070742d540903090354a00350403988050b0195860340a600000654101d40000c1d81160091101c1d5801051032841e01030303030014004009070a0b0111203e03401503001080660800e01d1850115402541d00c141e00c8061034031020084e600c1c80c189003400c10940d04c50041000343d044004c031004d07201d01007180da00402c81c50801c48000402e1100d240030001810040c0250315090104001e0b800f6081c050300c58000107040800c00b481e0141c4181080b41c5050113010000d4194502500c5001c1c6a01c1041c5262040028641c08662030038002c12480018142c141d00c41c92848200c3e0541c1e4001c6040c03440280e0307a51007642c01d40503040c903010603410303c5118181e010303000407821b54483c420035501c05060300302042259840000c5c2e040d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 378131303 1250 378130053 378130057
    0x1d01091a0d061e0c0e0108060604030b27010609020a08090f0c010f050f0c030702100c0210120b0307060f020d0e03070303050a120e0c010306061d1509030a0605040501060602070b0301061d0303 84
    0x1c00345c41d46a0005c000c0e10004091500040c01940076203010803040c00850480381c0c02691090b40c0964000e8986008211000d0094440301080000d6013440703001724800d10160045e0450303500c244d60300303004e80d910f001c61950b03035010012800410303030403800701055954800d00666051406500f00280f801200c003142c1d030702a03400142890659000420805c085185c110700d203d0750715000307280c07017080d411098001840342c0300811541000d000c80000b402c4401c040d42c3d001100b03201c40c001c1c01d5410b000d50b03444018040c15000100400180100c1c0ca054900034000d40b808011004007070b0080c5240c60079940d0585007903100090b00001c2c8a1030711100d11100312103002c0e1491401c500130103002c07480342031781c0003506650042e04180c0510204030005a04010b20407600100c21404580425921440f00c0c01d448a030320624407183d0701800358204e610180411504030314016840f5034020851130341ea81004913203801143c042d0b10342010040004000e8248640d00780f003000c050105540303607814003540c0040d01d0342d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 378132553 1250 378131303 378131321
    0x10203120129131202010c02030d081b041212030b030604030c02040614010e040b150a17010e04080304080a021e0a0605060102191b1d01091a0d061e 65
    0x145080142c004088240e0b81248100380071440b142506125030380b0b065008045140c0942c080781255040c2e5102503a2207440a654001d030041d06a8200801190001380290703070498072081e001302038a20a80008840001302c5080360000004c0c001640c42581c0d80240802c0d85070181e100301a12441140a0790390709001050280c1d11a882d03543d5440114414072003600c5156203c0ca8800c1c40c2903503050030380e98200021043c61071003143d0002d0000280b40005001204411500300d0742c2d80049010446507401c0845010146401c4421140681ea20300200c0114001194010224141070011600044104000d080800030a00584607202561051404450880c1070109126407090080e0030603c10b05103c4c0340d40000081c80038116842ca40c0529903401620007a00070700ca500fa1034220051306182d120000301801e01c80c5c03003640c8208141c1001203a001020b000e00c00d0315514040001c4d00d203030051030585a803071001034074181c0c11641645a80d002403843d8882030711110000604075000c034041344101d02031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 378133803 1250 378132553 378132569
    0x403240501180f140105090702010e06010f03200607141203040602070308070c12051b030409090308010801091104050439080604081e07140c040f1e0b0102031201 71
    0x1030100e40b240c007106030f403034280c8242540c510b02031204600c013000d0401141565000e541d500c81e59101c1a1040317004100999800c1102d00130030001003903a40c407940510044900500c0b00080c541401d04400c0041000b002040f5800301c420409000054000c1a203000c0206481c0c0642c1d0401104075a04101944122012900c0036800107010b402c05400c2089541c01c4000c510300740641402c43d584042074002040d248000f400004948440b03c0e60396560030f81c0d411076080099030744856903010003101620b45c80c13500702c021840f0030780080b4901d03a0511400c242150040c0010b400d64204000340001020090000d480c0208040e075010320019660080c480130b0303020396246040008a80781c500007009601c0c0c01020301c039004042031102080b41c0b0010740e41014501010b10301c0ca6078000c03500c8d0465205000c0300915140c20420210480c0d01c01085c80340c0204000c0e10140a42500c0c20144802c55825089041d0210700c801d044285008003903005400d1442c060044a251606904175201900f1099200d043c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 378135053 1250 378133803 378133829
    0x70314030a032f0f160506010501200303070509270603100e0606040c02010b090124141b0316111005071e21020f06010803040b0403240501 61
    0x4400c0d640752003002c1400c062118000002015800b901c043e400c8140c41c11440c1240124080d40d41454140454291001c113180300c8842c500715180c2592650700921480e808207940b8418080e6403a50242c42000310f582d50710246103503540b965410385182c1c03c81d18801c0c1e00b068450400c0c0d03600680d80017841d101c0c54600c000e94101351401c030040519058070008c0500c0810306061000200c00780c006035058110000300c07000304486d80d00c98801c07401016009007681c0d000c20098000900f071908020305400010404007540c3c06440070798003d0b0356040400300314031003402e000c10205802000700001c80b1040d0b5440300903a45000301c0001d05040302c80c400141074611080d40308985203180350110810b11100c886041190400782c0765110b6a8008440d131108022a0780a40001420040318001c2c180442007002c4007c070f42c00646200095448041c40d140c80018030810002003558030000042d41c080b24800d51015250504550300d0460100c0013055010654400c041d400500700024000c050181c04501800380b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 378136303 1250 378135053 378135067
    0x40e010612021b1b120304060503041b060807030c030c0c0807032706080f040812040804090c05030103050c03060f0a1a0409060b03060a06031e050a02030a0b1506031909020307031403 80
    0x308001d403040f07204030310400c25145d0b03041140342c000c41039400315509828800e8481d070b1181081c40c01d040070011030465001440e07001040464204d0030300344c0100740e580e4041205d8895007006070102e82402001074085248100c510000032911801008010b1182c60480640c2d109401049201602180d4080c0411040d600500c0900c3e4850000c2d60300c20380080c031a203d0f82c1426207c901d0a84201e200031441d0003000400903003401500004c5034010420001c0410946881410080039a0420b000844050080110b090100d14000a50300c2c00f503140400c1034010303a205e015000b402007600718800078440031740d40114042a40c6074826848000d0203404003243e01d6228804260400f240189041e280c107142a00a0000c0307499201e840c0355541d54894010b24800250404528200e00316400079414031496920b0420802041d4105029030a040648200c080ca400d0420241c0d000403241da03070709102c507100d41c115103284640003050220f001905448480751079454000d0040b8510160741403903070001500c1d07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 378137553 1250 378136303 378136333
    0x1c1a07030c0216120c030f030302091203031b1e040b0301060206090a03020d050306043201050102010c0519090f060302130609050f01030c1b030903020301050606040e010612021b 78
    0x20520454075101800c151003103410120b420340e40d14060000d0000c800000a410406580c1030b541c06160030032442c5203000d100b464010080c0d4440a01a0300a1440d00301244ca600300010540f8002c8032500e000e4a07011010442203506034025035046801e0340d0000e003030184038034103070001400900000200f45a8a6051060103481c0440181844085074001c1c03032a4408254041409110000c0d1032400035030340c0d1038100018015168101c204480078440302c41119504817207586036070001ea03400c1030090b680d03a0b80d0801607080703c1c000030464001c1841004a006041280141c0d590300c0003c0c1d003480b46119842e201c00700c10b14070b01d9803c020302090740019040f151400d818214401000b061411541280c240350200c0c403108108403a50b81031644810b81105094010100c0d441d4801c1502c524244181041c10f00401c80c41d00307444242d0085d481c00c0049055401e0450840d82550000d005050321a441c00204035112446080d01890495003402540c05411141b2503c250b002120001031101041403048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 378138803 1250 378137553 378137561
    0x90d06091115030c18041a1206060a050f0402070602120a0605031c110708010c020d09121112010207050a0c0e0612060601050d0905060106020d080a050408091c1a0703 73
    0x9064802c00c0007500d010381507441c5000322944056400300d100c0d103940790800c0d160300340c94802d18001c0d40581414142018400c03800e1500c0b135424402c0350095056400e0100a0f07031102800c0e2411604401a044140f180c1e04040f03500c44440c482c041c000520301815034403400100c0c0c2041c1d00501e00d541c09d020500401c55214002c20b4003421088010305402e900403101718070740203011346581c810302c00600f02d4042c008209000340d070000c0c00000028002c0039241340000b1b4a5500c031400c04030100303490003030100f00e1402c4106002407442c4d1141100010346020b00800c41a20207058560940e590204907040000341c062109607a658882d10420300d02904116060044610041c249400f6808014190403220790001e2401d070400f4080c24a0355462881e103600f200903200d2500040c01900c1640000214113030300180500f294811551000c1440d1500654041030711000d07500600301c0b50040c0046041c07868209407100488102800720100e21126544103490b4002d4113400111480c0a00e0410282607010f000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 378140053 1250 378138803 378138833
    0x1508070819030804020d020904060c0311031e220515070806011205070203040b04032303070c180f09030f030e0c1e030a08030114150405011d0303090d0609 68
    0x240505182400c4201da2511410340c0140070803903901d021030255203038881c6c080449a00608440300c07516150600c8405010b9801410300002d2410400c600c1071207020f41900d0142010880a100240040040e1640383c103003c0c00c054880c940b070160304403c071041c0c219440c44051041e00540b80c9051500f09041d0f101000422420600009000f00540d50b0b0303000d8008000c0c40c3c1c601c0000540d03611130210403031640c01a600041c4c1c280f44000790110501605e580d12042200b403070080303c03203c1842040b25603201d0040f06d90040800d5017081d070511580b01c0a9044142500e81004005144d0203c441204195803d00c00b0a41c00f0604106204038190381c036014851100d90487c0040503040300110100f5020015115405c000480e8150512480e41d01440b90b00082500104583d0304d9503192007581c814450420f141038854000705203600380d00502141038900300c4405071550540c0449251000300540c0c05902059854041003104441b0707595140d07152400b040c05040c00040780110f914141c115200d00030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 378141303 1250 378140053 378140069
    0x10c0210020304230709020d0207050d0e01050d05130f060507202806050f10081c180f0f060e03010e03090d050a02152d0306010c15150807 61
    0x4110200380e08442240204c582e032505100b44404441a00b400c1848641090084500009209a407021181c000c3c00d8628010b2013074495407900041c0548400c1c10303601d910f5000c02c005100100030b2100c030380d020585c460361180420140800c25a504205050305542c2240ca03140d542c020b00c8903080e80010849a21942120340200244a0381803641d610561040c41210f1455130385c2000340710f03080c1030240140f1103610080500680c2805c040e10304008070300b00e4407009400d0190350001000100020520a0320040780541040d040100074112550601d00e40301e500d960a841400061030116001a503004100e002d0300001d580e800c02c240244000210400355110ba0b06102c000c0f0f0700c0c0b2001008480c4c02032401c548012040c0c046250990401c903240030080e61211883c807903114852150801000d10b00c1c1d10301c0805005814154180302c0041c08001c000c1600c00081c00000d2455004101e0701c502d650140800c1040308440c0c18010307061301d0ba50710100015687e040300c02c014500007045a58003070070044c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 378142553 1250 378141303 378141307
    0x70c080a11250909020d1401021b01020703091511100203070e031b06071703010603092f120724020f0607020a06091e11091503120a02120408010c021002 67
    0x101c507038190a0302c5900511802a5403902101c3c115603030700d0380d4960f507558080a035441c2030b21103103484d5000b0b4000d15440310708500880c5030310782c80003010f1007120121949070b118072003042d080841002c0304100c410600c500303002c01c840c039901c9c0001003002003554000005d900580d8900c2c1140c1c00406035240710130124002d40c0092503c0102881c3c114070b07509000b81c1030700c4040e02c43c50281000c0020402480d000341d4a0400007001040c0d981c0d06420060300e40c0d0003125054403000c20001031321149500468000c00307441844c081030740b4a1800e814001e1307460b40c8076030445d8881c503111032580d0180c00c6502d001521441099121081c1550103200748a400049440a4800f9140c003140c0a500c404035008020480e03940d91200000700030a101c0c2c1b801c1800c9aa03031140d4420840c0d85040c05910b04403155040c451442d2340d001a01c6e681200020364000000a8094820b0740c400c0403840c5640c4d00300b030540030103501031040076100414507040031b4402000500008140d01c0d030001d4000e400c2c40300c0e56001598040c01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 378143803 1250 378142553 378142603
    0x1b09130507031113080c0604030203031204080904020406021c020d08070302090301090b0a050712110a030b1f050a03062306070311160503010501080f0a0308070c080a11 74
    0x49001451090452a60225881d55420070440082001007520201024045407a1407404142c01d0740c80140c40e002401c0300c056070756080412029000314400291706030700400640c051210b05400054015114461441c140b1440c1c0c4c0010f0242d8019402683c016404100241d81c0324025261031081c0611900240c000001a25001000781000401d40030070305400003407425050700d0942c49120b00e0781c5c00001800c42800c00102030b9001e80415102c590000c0d42c80306444e8130301012446141c0c8001e04c480340315490300f2859a0181d02404140e040c4c00d40c00300034280c02101c03445159040213441072176a50b54960381c1d9440d1002400300e900682212a50510080c400c0c0b8400025a454408241040360055124001403408503800300c141c010f01c045601aa20b030500b000c1a03100261401d451041300248696a01c6084242c3c0e1a000d500105d041c40d4050584413000c00d005603e8141c2048244c038205030013806c40d0b116140642d11041d0700b440002e2110120b5001d8020030b0082d1203004840c40c01c40120529 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 378145053 1250 378143803 378143809
    0x2120a02180c0304170d0609140709060e2206031a2a0f1c0b01030c02010e0c01051b01020331050606040e0c0307030507140603190218060c061b09 64
    0x1000200108180d80303401d582c000840046e60b05241d1b03110030600c0400c0e15100f0003030140024140604513620140d011514103809004001c00340e82c8155200b480c032460940800041e501d01520400c1c055038643e48454124009010f40d030040c1d80034400740c0140c540c024031160f9503920020005081d944400d91f03030100c0588400300608509500c14081c6449014182ea40602d40c481ca1084140700c9060004840e4603010036006469084802d03201044000350001e000ea083c0e07000020390606582100355800415800317540034041c070403503a41c2f090f944200111b9240b42240c0c404da5200300c02440d2541028441c400c00045002c0e03481c0103140086120f5480d0f5621030b0b0718500a001c05204584680e811321b003d25040068400610009003103541d040d581c0e00b00380b030315241240140b568030b00b01000320011a041c402c04490046072802c03031400010f03e50030b09000081d040791035140001407907806407814907550000035007004032846001c2d001d0360030b082107949154000d140c5910a2040706008448041d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 378146303 1250 378145053 378145057
    0x30c060711061b0105090d021903080105060c030f0a092903151c08040312020d08070c060b09070512150105090918070b04031b0b0d1802120a02180c 65
    0x3000035142c25444035010500d1032411482011102d601d5864101000000f04000601c0b0350018003c1e001c0e41d0350040100b03c918000d40d48404081c1c0400d00340001007089003081070041401b200908107890409807185002c50117a8070031001c001c0007a4032a0018480400c140100c6907151401c07005521814004e008000c8480c00020821003c039880c01800504584a2180e02d211003a6950040302c1d0b010b51a240482c0c154100f0300090701c8902c9a040d07800342d5107000084405d6603d40d10703184d518050b507910108803550040c4040c219421510350000f035a0a0310303404103040c06000c103a25000d84070165104a9010084024090751001c2400e10f10071041c2c0c0d03044030071a0412801514900c505650702101c1815420304d2003036542242c441c4600000c2d404030010060030681c0d00c01c11920485000204400640407400d015192040904014080018000c0e60100d020521859000746000b40d4540014610b0b0380008400c7d03440f034001c0c0050404515202000444008000b1300f13286103800c18001c80041c42c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 378147553 1250 378146303 378146333
    0xa0603030903110a0302030d0224010e04120507050607050304021e06041a09030d030c080901060b0a050c19120e090c040506030c0412060914060402030d0305062d030c0607 75
    0x80700c03410654149445403132000d80990740180444d20b050f06440c070002d603240b1031440c440c4001d82c2c4080766004a458400061412548104c480400d10386031a01e4a0032076803001a41c0b00b00b17001e010030080000650510800d84103540340e07241c2588034a028018000600b64626810686050b0214491701c2541c4080c142d409889140c90f22405075541d00b03108550f203102d005d0384c2980c9440b501c1e010700340a40e45a00031180c400070a40c0d0781c080785d89810001c60300707039599030054001440c0e0a10220311b02c02d104802506105458208a80c1d84000c100d0280d03001c0140004182c800e104040088507046030805003540305018203075045003c500d00f1524100d61801a400b03424403031300c00000840c2440d5050350a50b4060692600d51400d030107a0380c60540000d02c5440412160b00602982c0c0740c0840c800416614400c035000350250112510205084004010041440394000600443c0b103182030340c050b499241081c0781c03100c6140740720062801c251420800c2074082e80303d074408105420005282030010358030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 378148803 1250 378147553 378147563
    0xf030a12082208041406030411010302160209090f06180a11030c06040b03040c060c0f120311040602010617010203010602071719050303040b0105040e0309010c15050c0a080a0603030903 81
    0x42920307032060140140501041c0002d0181c240c2014038180441c0900400c03c0f03840c1003403041e005080761741c140704441c002161f014281c09c40200c44494654000d130010604617010f060740880c003c100f80c0c009440340e04152015565540a0b044441410034104100364100100310320848030442c55103a010740e20308070807400030900701c40204540310b00c0e102003004a40c10203000b031425480ea03854901160954200301d40a803144010b00e11b001450b140640301110216030001000d05540c0c4054441e803003018507601d480e80400d80c1d00c0c488100c103040781801502c003500b4142d0020a500e0700e031191501400758841004d0309a83d104000401030030307070002440b0003103800036403914800080c88002d0f81d081c60076429075001440d000101c007404201d000b2005600c503520071242402d0b44d0f600d507014003040311001021160660310403c2104010340c01502000c0a092040135540b481c4550300421809441c1c00b6924135510040c042200d560854103d0011503000c01301d841e0030864142345850042441c0c15510001d49 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 378150053 1250 378148803 378148817
    0x5043e030712080f132c07201608100f05010e01150e030106030303061715010909050a021c050d020c09040809030313080303060a0501031404080901021c02010501050f030a12 76
    0x70f0003108040a17504c403600ca221503840300c07950726007010300403840c41d030001191207407403031081d003040011074004500482c40d0350380d503240e03034030014420700041411190005105d101740103000640d00501244070b00644020400f401c2146112122503007620f040c0001ca41113a8201001804a508034a25640c111001900b4406224403c170400781c400f44040ca50781a015420602d011060503007540040e0100ca25803450354149140204003c1d4594245c5800075400540d920b0040000764000c2c0c01100250340900203907080e0360707400d50010703040da070341c012281c4c00c140000c0d88420300b4042c00f0300c44510068090f00113041a03000c8a8000b5080450040006144820100b4000a951030800c259a007007410342c4007100c40180c545031860b40d00d40048805a00c141000714011559511a010311100c07a0991111510980c42c0c59039101d1403034108805282c114402d4001d8011304101c2494550740c44030040d0000947c5504000c1440801c11808624502a602c02460080012450203070340d8030b504400d283c564 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 378151303 1250 378150053 378150067
    0x1050304020a081b1003021911100221061f0c030908030c100b0409080706270c050301060b030f0a050601051614061602060a05043e03071208 62
    0x40d0714500ca070f0008440c0d8804c1a4a050580103c0380c00c41d00407110441e000b02e095403045200720140e200304a14903c02120409103000b5007070054241078202c06d42481a030382c0e4044461400000c98200e010302c0c01032200313540103070329446500c00442c581142007980c088803540900540c3d441d5420b2616012030030406000f07420401d00d4031940507000580120800d50b6500c0c0315280100b6520400508010001e520b01940e190407481c26100e44030625a0005486042c2806600d43d90010f00ba00290122584800c5135a90060032880100d80300c80b81c803502000542034285800e250840710103421985089104105107c1005444181a64003101e10a0081219034410300100e030103028040c501d0483c1101c1401200412058405203410140300500700c44240e5240a09030440c1e092710201c207009030b0422400710f4004912904641d0b07000c4d018003401020070141d002c0c0800d1000c1d1a501c6080706102d070500c000c508008640340d80007400c60441c001d0210314100b4402c0b0459540a070b400800c01c038000241c4c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 378152553 1250 378151303 378151309
    0x90c18020f04141002010e0a0323030405030706110403020105090405060a03061104053d0c052e0614130e010c02210708090d050f01090507050a050307050306060105030402 75
    0x710a000704012019032202d5aa00f040c031144050224001d01c110300d0b081c80003001c144140b05610342500ca410041c41076209589060b240201c0303d6802d08001e82e40c1c5401c030030501c5000b40c01540101d01c42c900070340d90780007a81072180484030b4841e644445200c0411040001d42c1c0c0c0081a1000c0b501c080720001655200c5000081c0703000c41e6540020107107810b1140234950f04245801400482e01e05841c010301004800d1011801403c0000c034034014030f0311b4040b2000650780007500e000000126400c0c14403000c1070302c2c1c444d18039104201034110048a242142903100e444c40082d82447d00d40c0d0810700340030031400d1101100194540020700c50080e82e0703643c015507001e2181d8000d007030711440003002004a50000d01c4000d46072090108140303221000040340c0b00b6901907800844210a0304800c0e0281040155404c000e03207010001c0b400d44452081040c054460002071003088030f601e1054000b40007162618040c0481684580d200d680303e034106881c10480b588010541030760203802485d146941703541d10300c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 378153803 1250 378152553 378152557
    0x7030218030a080d06080601150f1103030901020301090615090515090d0b04020a050603040807030c03050708120106021006030302151e07020307021507050c09101d010302040609090c1802 82
    0x14641c1c1486100107550a000003100100707142c05400c3c2040c4a91034481003000d6982000b0300ca11a0303500302c5107244e599098480c01c0620071414040c0b07010810064241c40051541d001911104800d960000040220103c01d12a0344001c00c1d03002d02850010b40a60000f40c040c012601c60708d40184480548008075001410440c0ca25003002010244500c9a508003086420030032035040b402811a91350210b010718181003524455075011301e0b540e28000441c1c1d0120b51014a1402c2103041c01301c107012260009030110090030822a042e113050480390f243c03410081c40c110400a180954600c0c012080c00401d0740440c2d0341e806602200d2050110f601c42040d08240e5100e007915045c2d40040300010b2003079050b8044024000b081c0200d80e0804001340382c1040c400c8600c0740d1603000b00254041c081140e0f907420050b2031182c0c8030518141201b61642c3e10401c09166240030101c08541001100c010b00841c41d2074402c031005003007851400c2050868990351040403407013030b0142000c40c1d5200c51564081c2c0c03000d901 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 378155053 1250 378153803 378153847
    0x180209122e09231903020c0f0306060d110102011404060b04060605030601120b0a09151a0301120209061318020306010801090c05060309010207020a0b0909061813030905030a03022112070302 83
    0x303a8656580c01500b0001d440303001d401846846044051230003034140c940000c1060060000401c42043d0f500c560390390034417000c01d01e4401419552191272620344d0700a000035551280380100c00125215400c03400308821518650001300c11f00400303009000c401d0740e010b040c01c1d00100910200040b40350400001031880c248075801000030034140440c81070002c0300030381c24100703c0300b44000132200c84a000c0b00345070080c0424080c1d0007182101035008000340c600a204d031030b005800901000851a0340b86a2201581c404024540c050340030010780c4c03001c5042c10409580107002c070900070400546199248031048006201319481140044046849803000390f0407204520b41c024284401e042d5903c10480d456001120480c0c840e50000001892600300b00c608002e02c00d40340d03914884d055071040031550000d15500000d80400c441c0502c0402c050302d08000d01b10034103001b90000d00c56201c46140c5520414115024024000d4003070040c0001001804111500100c0c1c5003000740e140d60070100b030360044c020058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 378156303 1250 378155053 378155083
    0x302130b030c043312022205030f060c070b060a1d0109060b070312051e041103061320040f1b03060f180209122e0923 52
    0x90080203a4104000c000711444541e02401c41c140da03020003072502e606885503c1480420110501d076062280584d481071005d0703440010705120035401170036410329414100c07132265142c509007804186410411003c2c43d00300c1500818251a002c050113419000740b04006042c4079403000490410f99982a582c0b020b412120000c1da488123240c1ca9290811400380300da041c55a04d820f0340171030b01003481002c50b0003058240e01d500d000031900e8080a80180700060000795840caa901c001407503100d140f00020b0242e1b000e120a8244410703441c0c109403c0400c0508074034202540a0703a03c40025410320049140151901c15a84441c082d420100b40074202d0320061001d01c80c60300f480300103c0b0102c504024031011595408220040d21002114034185e01809a10000806204031060b4a2400d400900602c2406082c40410301032440d041840c01c00402c000da01d00700e034130300c50307030303080301c03802c079660356050100014140303d28050340c3c40d10311740b420312000094001c0e0100c1c80e6440071141c04004030380d1052180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 378157553 1250 378156303 378156307
    0x201090f050615010c02181b04031a0f01080a03050309031201080a03180617090a0c080a030e18010605072105070b250f0e030a030801030209060a0311010302130b 71
    0x1514006072100c2c401c4031032001c09100040010155446070700300c4042c2607405040c0f20420010512042040d20b00105a0300e0140740d05403411606901c0ca02c083c20042d07200d49103c2c038404205011080007a10024404404402000c00421020130000f03030680031035405080003503403621065059801c62060f550b441d10156525000040d15020000300e0713208503400303541d03594400e0710402010000c140082c0710b83d13000690144000005440810203d03a00001400c084481000e0755640c0e500c00b84045130301c10700f01900700020f04c405058020704040301b241760840c3d004500c844d103044144034189060040408000011410404111143c03141c5181030075400070341c8069007610072000702194030618003211034484641c04692040441c01e02840f11203149507502e07550500c2040c048852140c0040c10404010721403441c1c100e151000c0c410705004034080d030b4580310298114018407180d00800341113a40111400300c403c0020802240500b1030380202441c000da618034600c03040a80c091416000a801c040c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 378158803 1250 378157553 378157583
    0x3030f1309020412110102010509070501141e2701020a0f020117040803010513062409030606121406070806090c0c010f0903090e090a0303090816060b1201020f0712020109 75
    0x8100313080140140b2a014070040c0705031310801282614402c2e115191aa4800d100520003503000e61b6214607800001000107003092800703030600c4820b111240006c40c2c1c803030000843c032600c05202c410b650320000850b1140b4403440d03402d00c0001c0d55801c0c0000301038242074100410b0011684900300030080320f9882003004110f13052508000c00541d1083c412944220340300c41ca03442d080c03d9607004240460300407405018819844207890100001c151071080100003401001000003155845408080c00401109554041e042e14041800c000c0d50740c0f180a59a002000700200540e20040a540c00030090b21340a480307403105030710140030340242c000d11a000d500740f001920442d80340b54800ca41d1540250f5808803041e80e11100213900c12002e46200069400c4020300c41c010a000303030003a000b104d100314140f83c500300102c450103240d0255500c0407980d483e11a030300d4030040c1c6044100049a0201c010085180800c56505200580308440000348040744904486a00d68000e500ca542ca040e0407900240d48002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 378160053 1250 378158803 378158819
    0xa15080d03050a0b1203030105040209040b0910210b16090902120f180a06090c030f052a010f0e03160e090d03140c2d121503030f13090204 61
    0x6080350146a001d28020b114003080c6400d1013805d101003a0030000d50324590a00092002a41c23090a085030410340343c1100d0074658170b803140c89034072900c40c10515107020ba081101ca01d6018103402c81d400100b0301c410414401140340d6080c440c2d005111452040c412000d406800d44002c4c0c50750303000030f030390a1000c10743c0300d004990011498403407101c9215510603641d0310074401451055580c0c00460310b50204000a00050b25540586c0401d8007820700990202c0e80d9558011034000c5450701200e0b40d8000c03208181c00c0002452203400b1107a4140180080d04000800081c4a444030103001c1c81001009001084141c5040c8036212495040920592580d030b03d074290884204000d41c1c106d205031158620b66541c191003446030748a0003001002000c116116400b9100064101409002a42d6206150124038040003820f030010f02031205111601c80d01004003200b006140241090452407003402c84080580c0e01000711101d20500f050080c0e1a00141c000e0f1a400d4003040e0030400d220b510014010900750 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 378161303 1250 378160053 378160061
    0x1e09090c040e0f030a0c06090c060306060e010f020d05070204090b0a05060a0f060203120408090405040b060a050306041109190c1d040902010c080c0c04091a06010212030a15080d03 79
    0x121080d00c05204001910400da6501c0824900c0100306804c180401540e0a21520036610280c5c00307040c1c0405c5030181c6480385801d02010f036205e40003090b5281d00070401c041c1c001900086110003402d00c1201c40d14403001c0a501c40340004420404c100c0000b500400319a1982d11080364280c0111102e0541d1410002d4030f030007044c00780e0f2111301c00c403064000005c070300381044401c10507540e056021754140030040203541420f81e405442110303a13034818451000d60b5280d81c03181c0b601c103078040e06079400c0c0c50400009008200203181c00950080c3c11901c10000801c4401e0100ca11600d0191146180f695a2484054548003094070300c0c00c12a003880810020194030180070350300000b290114501030b200c1901040110f445001e0002c0c0495000250807002c14803010140406030041400e0b108034075000000203044412110044910f05400090608146003142909d64006028001004c12101c1d800442d01d09020081c170380a00303543c903408010030490110052000400201c1c04031100103204a02c060094 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 378162553 1250 378161303 378161323
    0x140f0402091006050405041802030a0b0403180803040b0a0302070209040f0b0c1c0f0b1309110102010203131e02060406020a03080601020c0a030f170304051606030504020a051e0909 79
    0x115070200200d84592031040861003290115103805182500d880c044c400a01039021180c00c3c90b0701c01c1100740e40035841c1440750035078280c401e500c0c8407000d1070140707006401c0070309a200514203090441403e1141207400021034040e0b40f1241c10054449103e0101200a807180c40c0c4000c0d0056403540501082060015256610394407410000c4015901d0041d000c0341030003004201c0e40c0074118000724100305180d40d0700107c50f6100d400c4010a1400800300801d10740c011178844090520303691941c2d0000d01040d40c001714980c0e10240700940c41e5003070085003814280418080a0000203c04003d103200c44410307041600f120754041d01a0340c60300d0341d804c0040d45078070507400c090780404e170103d0000c0c110307610205890011100082456008509640380c40d5107141100e5000c4030002c40a8410301d40f540303d0070b00034520451161006244078900394906104070030302ca90140c010715060905202c0180e032500f0070002134a50585c1d0825641e40c0300001515510010150b0580148030003045c810204c00100d210050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 378163803 1250 378162553 378162559
    0x905030a0801090b0603040f020108090f010e0c04150302090612071a1206040618150801110a090f061b0312050c04210b1503030c030c0d0305070c020f01050a03140f0402 74
    0x44d80380d0b03000c00d01006101c110390040885202e5140440150300483c0f929800c042c3c2001110b604850342c10800313085464550b414003081d841890742101e00e103403c0c06040740e10f081c140401e540342450b60340030603000100a0122840703000903100c000d1a18200b0032200d0700800d080b841c441c001d580564020120b640c0040c005045824011001420070b00b041d0013008100c80e0280083c4000c2c4003110890002001030310144281d03410344107400a100c5401f401074811a1400384e45040d40d0361141318002e410f4220560011803030134906003080003926001101c03014031002a4032a10356000c05413600321001c1d058940b504041c14a41024000341301d0545000e00141e604c44002c0150714130028441841740035007004000c050001c01000103282540c0d48030300f03400310b06001c1c2c1202d003000c0c284204682160040103181490364801045c4d00302045d49405815041001e600301107135056015000304442001901c103060500c1400100a44d03202e22aa10000c2c0c0c081d0603869001c181e0800c1c07400400d41d42c0050303405900c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 378165053 1250 378163803 378163811
    0x150c070201080a1e050c07061a0907090e1f030203060f04020a06050f0d15050d03120b060a05070308060102100216050601060f090e090a080a02010c020f1f09060905030a080109 77
    0x40d2042074032a066034028000004c0242d1400b1515140c040c007001000291040014021000000c030070380601060741c65541c0701d2620503010031051005000c1d0050806041015400d810060040d22084c4075401051000c048030040c042a50920702d081040d51000b50580700b0340082280d00034408410303500a510880c0c0c0541415510702c822149402080002002c02c01c040288071a0032480398401c203214190141da0310380c1d691343c0d00002410603040f200150f01007074940862004101c900d10038102c242c0c804403103850501c40e680704014510b002d40040203003030190b16408140680c0c020490510000003460003950b842960410b45040c038560901c1c00c94003031103901c001241d03460188100c0310009103259203100d5414640b1000c0034011002505c4c40e007190050811a202281c2d070b94006020544550700082031b100d0034488001e10709500c20218024a0b0050300d0a18807004040b0a918642180d00d40f000c80c0710049420210000c1450010041c5144400a08100029081590581280c01e1000200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 378166303 1250 378165053 378165061
    0x4060213090f0f15141809150109050f060603070e030d32030c1606150501021605011d01050c190c0f0305060610110d110f010212010512150c07020108 66
    0x81e2110030380f8865800c4c4030a24140400c110b41d51420702c40b210010100452210021514180c09100396000c0185130407107030f0b0351404490b10002050061050440404c601d2500c10f029100c009405030619104a00c000080340c5040d22683c8041d8501c103004082d00d15034001d00c90f01800700c0340040114601503034261940c003040110b0a00c0790100b4092100300754515520003006844075401140031204400d40c1e00c80040200d1018490011009281c004400e02c03036042c8000646010748210001d445001d520109129a990101601c0221047c0034511400101003600586560241040d040b8071072180040c1c40802c0d506000e0800079080c0503e05184d1503079180d050341c00703450705907000c068400c3e84100003113200c6040c011b030740000200e041e1070030307051601c0620019403e240743c0e510084000790b4201309a048406d01404000c1c030040e0304000861500041c4c6804045003d01403080310301c224465120400004018400010325180c49110b4115501e403181140b03001c1e070005401a070026001100107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 378167553 1250 378166303 378166331
    0x30601172403030d0f0b040b0306040f02010302130515071a10031e06020705070e090d1d01140a03020408060610050304020d0305090a090b030123010e04060213090f 72
    0xd40034115076001215500d200e2604039540300410300030035400d444200308841c040116882410000c0c1e140210104030030410104000c01e4807100c5041038400d80010003400700192040101c0c44201c0c0e82070a0150b1504150386039041541c02d164000c5800020040d070380350403075540200606c00644100407800e06454151400001c6034012108511450070321903052000c110742c2713100c840000343c0540c0d210003030303140c01e641d200181e0700443e02c00c035002e41c080070081c44090180f41525901020b00c0340180a1802e40300300081001c105481086800c40551b2009a00c0703912a0402108202d01d100003580e8400d10a40020002e500c140b14606003070083c58085841403426050120404070301c2c1c3c0c1c0e164250f444d0f40e000c0095040c0f80070380480500600300b1450005032904400d040040c01c40010018441d00b0000500d03003502c1c41c0d0700c0da201d60b4003a4040c4c81800008c2d8031202c04d05482040e01c151016990700d290001c024072074100316050a4456100009081403107800401391070b500e01b41d050116034801c500e2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 378168803 1250 378167553 378167597
    0x11011e090b07090303020a030809120c0f010b1c02040509070302091303180617060109050a3b04030503040311010501030c05010e0916030c0e06030f0714070201210e0111030601 77
    0xf00140c07c422200b80210303119113052a003180404041e114207040b0300070035106640c01311415803116003080c00c3d10058130000703114058050005961074500600520203441180c03070b03556070080c0704650710404140c88031020061a07001c2c41d40581003440504108851000702121403500710001020a5880c184a0f04078840f04011030320035844030408249004000241401e005007014100701301250002800d5480009800041032107040504454560a03000c0521100c0750b040c00424024200c0703161205042c50181d59030084d003600d0030036100d031070300e180c211404295078084621560a001c00030041c404400c042c03d04445003600c40940d114245424840380b503008940b43e8481880144000048500940010310311429524109030107030a640d0014074250401d80b249584415050200004d054000244204404c000b02c2c00c0d0303092600075030000340014154514001030340300b00101c030504d04026400050201c0440c80092010b6461000722400a0300304403003071400247ca541c80221240313981c0c15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 378170053 1250 378168803 378168809
    0xd031a04020f2a0d170408030a09051519050405120705150a0209010e01180306050612030c0706030b03030c0c13020c06070c11060c061305070e0a0c09060806090711011e090b0709 78
    0x170b07011520364441d10b90340c045030402013561010584403605d10002410600414045030b10031540b103501c506060088201d030b00400d5a10b003048902c0c10b018000440c00000d64480030f440c903001c05503640c07000362038105c0c00c055114411b40359000b1a801403040031586600a089000070a980e4550100710b40c0004580c0d810351004c074150900e08074502400420156000301c3d03030051014005900720110001610310f564004042a2610340240405006043d450302590007004000c800031810181410303000b80e00e61150641040c451504a5000041d254540d01612030340e85c42202900e13034601d07140b40040c0c80c08ea03600708201e50000e0f52940a042c41d14040382070361160700001001700340c2d0f030b41d50621400703003001a00e2042c3c4840c850803400103000c0b020300030b100d480380c682d000c80420002e03203030400640400d50a81001c814400810204103c685402032125400080791500788103486501540b1401043d480c05040caa4131040c40d0541c40d01140e81c3c00004801d80725402d8600c203943ea2403401c8980c810580 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 378171303 1250 378170053 378170087
    0xf040f05092433030a050108060c03160e060c0a06050c040b0d1a03010e1b01031407030207060917040314030703080609100801090b090d031a04020f2a0d 67
    0x380200c076040c104001c0c0ca20020120030f5101c050030f210100e12400035501c00310904000b1400100304511003203a405007a00401803a4014815400c092950080d0741c000107142100000d440120941d01501c02c0c50303000d24814000c0c0100f0350b0f03a040b500015840b201019010380300242000049410030f04448100d42c202c40d4825504c40c2000580300018016140d00f008a2a1105054000041c590f0302031050f80d600b001003400829100428440c0d401401e0100b02505040c1880e250140102c2c06401c9034460748840940380050b0741e100c0600c0c110000340034062001e06940303009190181014000307002481a2405032154030420908044210b6480c400c2280050000d00c0420204510381000c10945400c80e80107850003400740e440301421400c507510120256184e2560609010340c008092004d849100f14520701400104c001c220000d4540c266000624019503001515040c56094041078801d071600300107045140131001003d0003129101d05a2010050160402451200d8010288403d54030703511 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 378172553 1250 378171303 378171361
    0xb0c18030d0905040f150801060303110a020604120f06090506090f301905094e06190615090905060409120c061b0912080f040f0509 58
    0x104090102a10315103900d1740e10a9222010007409a140c0c0503408040d000c0d84000041413461401c00805a030b40702040301034207412070121400561109400c032420344092025192090b042d030b143c00b605211255201404640c50036001004100000c150140111144000c0341d100100060100362601140500ca11809800302544065034006461518210100d0740f0850308000c0122034044003005210480000240001200d546510341900030350400001c49042e045924968040c60108170080c0c42c211401c103039250390b46040020717240c03026910000c02800b5500741c1d040c44c151042c100300b4943d0240f0074041c1080000310303032003255501d1004034001513502ca54000746042d00c2c4000070200a4440d1750865250410800450414200b03d0f42030010342d03841d01046202405d1210440b12041c285804030b80076890b4400c440395100e00365609664a504008031002100e20708030392a0710500800d490440004500014600140034030b000c110381003a5244001075031208003004c60203184003504041c41c446 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 378173803 1250 378172553 378172559
    0xb07030207050a1a031503030708040305070503100501051c05010e101b020a0804060c030201110f070c050a0b0d0203100e09030307090806071202070f17040504060906030b060108070c0b0c18030d09 86
    0x400e50f0303903402c440c06c0a0252894010240c469009030740c02074200380c4051307200c0d010400c20303414100000c21411207103c0007081a0350400b00040c00654195200005144140b000c00d404d00c130007944041c100345a61b00848003840c14005485001d00750040c01010500000031041c21210700226800c2d0b251030384000341511701070800206442d40c141400040e03045641e40c4141100c4103003c0401026a4840d1a07095611128a03140074180e4101a4100c28004c410030002004803010301c0d81a16046a00702c6005a141e903500b5080c0240c42c12142d010904a40d558010300024550100c01907028440954602101a03111040e5590f19803003500d40d10300042484180c0303e851540c03503001c0e102040c17003038507003040c0034440352641414040c6e0b43d0310000c1c0c01000007604105071f140500c034400040034031000500c807042c030b0342c0c4962080d441d0043c000ca061080d080000b8805c0d03407081c803510411503840b003080c14080c10841030241030380d00a01e01034030140350f500392030305d005107000210313100e00d82d0381c0780e40340c0c03a00e142 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 378175053 1250 378173803 378173821
    0x19140a3809031c0203090a09060509060d02010207091a0402030c03061c030804020f13060b03090d0903050709110d0615122c0c0a030602070326040210090b07030207050a1a03 76
    0x41e03043c04081c21400300380084601035079440d1401004040303644010410700d00b0101007128a6401504079442406001c0c2c4071230040c1d0f004510181100c2c03014a00103240c6500046c00c0100004510059070300c588004200461904000d02035070140c236096070280c0d007201000c03c40c640041a00d090107804203019100240041c6420700750b001862801420840d2019401c1d24800c040d2040da400201c0c2030403010041100e88041004850b01e4285540340c0b01c0c80c0c003440d54403031903201c5001c1d0180020654a4101251269220b0402c465145010030343c100302e0305680f10bc441042c030803441c10410010355039814100500200c0d01880c84000199003400441c3c03e14080c07141c0c00508044035030146801a4080428180d4030141d542c8000d500507840560ba0314003d2030000c02c1181001c011400c01c01e030402ca2007000600c1c0900141d8000d40c1074803400b051000001c8281c4103070569900074200d00c800011034104059020441d0700c200c50080c0c0300b03004070355150b4270f00d40c840070300e449505c0362070362420310010390811 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 378176303 1250 378175053 378175093
    0x50c100b0607060207050a0b0903040f1a0f1c0b092203020c0d030504031a0f01090207080403241401051c0c0510091419140a380903 58
    0x410040890b850005565241c50503030b0003e801c1074601d500a51840f030300780f148451105a00125450103180303014184450a02c207004140604480c2140d252840503800c5201800c88521814030900c2588920201c09003a0030300301a1381d454403040341014442c003850b04000c0326440c09800b480c40d6150076025020440c0f0030460740080d09a00b188100d02c0c00f8110790b25141100c0c00e08501941c1d5132550340303040d070500c962024001503459841e820b1002c20400150315401000e41541d01070030016a0f280036904044c00305006076040034000907007445c2d64408100c07078201101c04143c8203170b0040c0b0500105007800d072400e14007441125003103158454002c90403990104e1030071545100718061389046480d0f00200341c0c01012a60341802003803000340e043c072084c880c030b4019081c601030454807059000e11081d0091040642880303194041ca1502408403d507650303401c0d480300036256001e0350134450300c0704101c007490004a01c214000c1c071814003041c0d03841004d1910b08540d0341c002c0180041003140844070f5996400c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 378177553 1250 378176303 378176321
    0xc0801060909030503060f130606020705091e071103120a0504120903121808070611061024210b010e060f1204030c060f0501050411090109090203070c0515040b0601050c10 75
    0x8d41881500d950440c0c140303c0c11000d0142d0364002c020040c01c1009209200d080a030564008030001c0440042224030030048952020f501e10f00700f01e184d1800e4412601e103014044400c404901360004002002e42e0f281c1c01240315070300581d00a007201e81d00d100c054038090454003010700705c58a80d4001c0040c441c0180d00c0b4118400c2644c207443c1e980343e80c5401a90422201c0d40044000036591103221404007010001140c2044030105c6002180c2e1038441d40c41081c2c410420380d035854174030310300e5601c400c0c0e1301882151a8104200c840f4540041e0080a141c0060604481031400301350481128011828802c0c1031b40c0b074104000e180e952130500000342544a01d44028012010400c0601c520300004841c2d002b00b40300b034001258007144950610b001c00c000c0c0e42c40c0300e5114410080c18031000e001c03aa406088101100ea01c1240142d03203480d801012504104e50f000007820030f20421032080ad081d40380d110b400b4800c0b0b0060b0002c4689489807801107950303101e62480041c40c0d070b01c03100c1900003021090340724901c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 378178803 1250 378177553 378177559
    0x7080a0b01120b151206010902130503031903050703020c011805060c041406090402130e01030b1605030a09141f060503031e0f070605010803030f060609030a0b09030909040c0801060909030503060f 86
    0x10340543d02407491b14120090f04001c070100d40100d050303500c00b20405035120181030100c000c1d41c20058440c280a0915480740140010140c44c1d401061240f8000d81c121118401104024007003c00d04d90700791a0011103c0e881200c00740709000006403441d0b000c0e404e440a44281c031040440003d0701204004150f0800015143d00030760030000e0313905850328100c140000342140601288a50f1450038480c40c000402407080501a07111100c070b09041d98414110b136030240381d00d9070000341d9498038241240b800c0d070040c4200342e403445089000904241d03010011005244021002d10450340c0758402d0603180d01a0b115211102c44002c046c0c03200320700c00c4102a095200c1c5040340765007481041e48a02c03003918820390003800c01d42c000200780000f0101c684541c0340d1000056500901c2d0120010102c0d80c2c2d041c10f41c101805c0020010042001c00c0303000c0c0b00711100b041001b40007080c0f80c1080d04045198035140e114000d00b41d131030901c2c0000c03002c003c0d0082c072400d40d4145d103a0509654590b402d205450182c0b10956078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 378180053 1250 378178803 378178819
    0xa02031605040f12230a0510020406050901050d140901140a20210c04060305100605270301020d0203060102060f09150a09020a0605040f0608060a0909031107080a0b01120b15 76
    0x1d07a01918201141e5042d00d0000280303403440e01ca040881c14088c00142000740d4a004000170b222064010046460f41402071800a9840c600c03c3c4c4650b00500840e40d00001400914050000b80303041500300c100c8049864605519544840180400315000703403241060f14030303040840249482003030020340441840c0d589210400d500100d952382502c4412076610246e8600854180051a45482034981c045240da04403001c06c0e0810320050800c0c02030b01c0660384800c080e00e4400040d00c861080a0b650700801400940d190071550081d00040c0d04101d03030184c010b1003070b000005c209150740344807140a8a00400500103807800c014150f140900b000701708003003590b2501a00c2005880712241c140082c0308541d0340540303c034280b030030140c010150307036005004011140b41440260740d18240b4600881d00b0040000920004500c0c3c15640d0422001c0c2d948054060100001001c10003c52502d0038284a03040b90b4400e07030303201e20038403100c0d484070000506440c2c2c0c080002103441c5c1102884884015000300444 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 378181303 1250 378180053 378180083
    0xb12010e0d030203091516030e0c0a03020613030b0a0203010509130b06090604090b040c030c0515180109170105270c0f0f030304030312050901060302090c0f0f030a02031605040f12 79
    0x14080c42d087d51401041210741c0901e8038810f6140c03140141e8020094040c18204240c1c000040f900c00d00e80c08081c2c40707543e00042d500843c01a2940b0440110f520291415407840c05d1300c00103000f90400d2044600840b041d10005034550f040025400059900440115158564000344031100e50000c020580042d580e26086000c150111201445140b060b01116499400c40c940804e400c601b5a021601900610f9901203812003600d068a4114041d40c1a40c1180d035000c00040300d070b120b0154440b4002480d8600510000c44040d0800d40c4540b402e030348c40b8007412050035205100c0c07005403041003240760001e2843c03800514241d04607103000400202400c21518040300082d042d54096402140800c62500c0301d02c04010080c040c59500848003002008818510340200e44911001030140d028103000007519251500c8410556550803d25524280c9a1800703403200b40095100790707a00d5001e4031708090554034103803280c0c007294165102600c000c01d940e803421400c80c50714000c0c424101c03840000541c0d10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 378182553 1250 378181303 378181333
    0xa0b0d0b040b0603010c0201110f1e0f0406270909020301060e0a020a11030301060903080f21061806220e030a030b09010603020a080106110a0b07030b12010e0d03020309 74
    0x5409140101c0c101a61403c1c031808150031550b404640405590620001521483c01401952020801c0d03c40c81d0341d80d0308010525100c004084500110401d40100710b052200c0746e07040282058403003e0b129104040041101510846440c00e400b1081c01e104890604c04278032103400442d4034510250000c95015110401d804007080103c4044007a075501082c51403a0380c0e0f00c1034013030b508c00741e0403406903180d035050042c003d044d5016408080c5c0208400034440c90700000c000100c50b01a12030b02e40300180413241a00da00710480c0150780d03807440390700e0480d660703401201c1c00d0740400d00845004220b05d09000f07490030300800354401c10410061080d5a50b0782d500000c030041c0018000c5000559000401d440854100070b11050183c00000400d44140518000107410200e058190399003800c0c40c051019150b540e003450910451801448000d0300410b00c51402e4041c1c025030003014040701e58449480e10051240e08030340361084821402c5d44200303111103005010368015034002e10500305036411a00241e100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 378183803 1250 378182553 378182573
    0xd0312050f090706031a04050711070305060717071d15040308030f010608100603090c0305031903050109090203060103200d0803040302060c0403111504090f0917120a0b0d 75
    0x4001502400c100300300b4075014410200504410b0400b080420b203000309400702d802c2e40003500e50049540e4408240c0b820301070407126001d492a0b10440d4955034491030101d445101c05c0d5201c030045100303030b0500e000003108004050b00c140500e41e580303540d600c1c1a00380040164601c400041c0c000030718454114034400765000800c003940c09191503540e2403c1020f0035080d4a90140d008004122080e014081d5202034441301c00f007103440f9481c01040e40a03c1b400c100415034010340c0010102d01c00000c981400349003402080705405404d8074204030507aa6010380390299032400320020b506070080710042c80043c020030a000800d40d0030081100c4480b0001c03010819100000f103060b260341201100300410142e041241517808a0968205030a00346560b440d400c1c40070712000306d42e10981641d90f903404198000b01c00d0360001d103070303203c024070911b01002461001462130700000e1b5483c00142c00714072402b00b401c03002c460031455640601c0b01c00d80d589040640c02452080001076021800541c004046000c500c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 378185053 1250 378183803 378183811
    0x130e1504050709091104080f06190207060b10020a020f011e2024010f0f03020f1207091e0204030b071404090903051b210702031c020d121a0d031205 65
    0x100c0586d103e0034410154544500d00084129591081d8100180d0301194070310710070044541c0b038001d80c50710310605e0030002070301301020480e07000301814800c043c0d607541c001251031503140241c98203000b034907030980112804c0c44910300b00440b2140a448421400307200c0d11202c400e070014900e140a07102c100c1c40016041c8441900d00220441081d038220700003500c0414a80d004100b440070420070580b0b0400f0300c08185d80c807803001920900951840201603191030f850021200016420356a8640e1500030b10f00c020161700c99a0003c2440002c0701256100b0a80700315002d99030000c5000740c0c241e40b21041190200d000c0760030100f10490910000510700d03011300400c1d81d040c1c46130b22000d41f58644800503a80e6207000601804860303100d01d45950309110404001c4c01c00307031310704003d036692a0f05d00e0011901e0691216560b01c540c0d400180b010b0f108982c0810101804011595000f1384007034494981d00036034001054016000c1c0303180502000c18500244524481ca01c80c4c105090f8003503103030038042d04440e0221 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 378186303 1250 378185053 378185081
    0x3030915151401021b0612090d0e180a050c04030b0a050f0705070c06080606040b0f0702100504060e0108072106052407060222030602130e150405070909 67
    0x1515404100180300e02410141030b1002000c1c044800c9a40001d5444200080d6030080c003601000580007901e800c801c0f9a126000340b5480142402d240c0181c41d03994042684500024842c01c249860524000301c0300c03804060f030211240354a41724440e4540c01864064100003600a08000000006400c0031180b4480d480c41080043c0c10301d080b80350030100c403074018214000c000d001c100d0b00c00002c84921140054500303034a00020b04c0d0303a03030002159140c0b1a54010b801c001d40d0204904010010341c00081001510036915103e03005604030044e1020300603070046c20b01007410741c07080058035440b07401403681c400c00b40d107802558103241103c1c00341c5d001d450082c90300c002901ea6800b804181000d01440807010540d00d038050301034424881c904403c2c01117400c020980d030b8000803480e000c402e89000c1a401c80200040441c83c5c20350368500300000b540005034214010b208140002100001c18a5652140402a1003481d5403030030389003040024a0000d100c402408181720011503d440c00b03102d6081070781101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 378187553 1250 378186303 378186311
    0x1c0c080301171e06160c260f04081f09150c02121b0c0604150e030309030f0304030b10060c060b01090e01060f020609011b1b17090909010908090d03030915 68
    0xc4008266403c3c2035003211000c6c801d03106081d60002d245e100c64011503100c4008446903221801c1d4001c00c1c1c500c42d00e603000710120000724006c660803d020035041d04150004100007034040c0541c080006907401c1d200041e001e05072082c0b0005440b60243c006111900c0701d40b064440083d44210b5040c050340200c00c250005018030503981003442010011030003003083c03c441150a1030b140c89a014071b40200a840c290400a03d14208060ba88040064603100c450040a40fa00a01014007065032504a80b0080c0c3d40780c0400b001144440500c1c50340301d82581d035556030380e25241a01c0c0e19a8405040b81910031070410441e0351002401030000141030b03028101a64179150384400f881c00091800300041c08001160b490603101d10b80a900c3d0a680106012060800d40c1c4000c0140314070107001c0325042d00190070a81c1c10001c00c100c07031100c00c0050850b24400c944840d180e0f00d503080b280b422500220401043e0f00010131200e070032403402e6010b07104a64820700d400b0a20501d55590003c90350100c405c1e0601d02c1b619 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 378188803 1250 378187553 378187561
    0xc060209040f14090111090d050a05121905070c051507060c02010b030d1806110312090129181f0b03040c06080f0a0c1704051c0c080301171e06 63
    0x1140c595150050444d034024401314143c90042041441040ba00c1c91140c8000401d84c01003200600c1600c100301d8218050318511a2120500382255100c4c40355540b240e507606c241c294000d40118203480003950840c0c42c2607820780c140b00612101d803a0030626a000d060044c0116800981c0a000b44080540ca41d800803d11440f54030030f040c6400007408445084c03003603100382c4001c2404d82000c85c00c1150018030301016203608181d10300e410b501c02d210300140d06d030001c107040100310700c4150400c40c180c0d5802d13a500382040000400311401c11210f04032042c0e0101e0002420210880411071503030f0412848074280485c110b42400c0c0580c41e04482c0d10400c462640402007005002458401c5802440c1c542420700440c540b14900451030403004081c41a02507545501501a91003460500e4005004600c298502d0801c3d042c0b1030760702c01d0000381100290f1a0343d1a01c0c081544200c1103695059484102c050450342098102405611144d44010481c422008420203050081c0c84540c1e8055046001d40102d0034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 378190053 1250 378188803 378188831
    0x40c0e0316030b0604020304230d02160602030d0f0b06180f0d08030f070e0a0e06040c020705151e070b1609120807140607030c0806100509010c060209040f 68
    0x20341c45540240c1c1580c4150100089403041000c2c6034001340807180107a50303507101c0c64981031070720800c03940304006140d02070550750b0301c10002500741d62580d59408807910700959201a41d4070304250300494005030010f001615401d102504907070f40461500c1004202c5a40c1280410015044940b8600846541401000f07080c10017892205040310f0944160a03e0a040d8a4104807480050042c0e0548141400000c800341e1140403100d07054903009041030b41d465522011441c80400030b0328602e104510f0100166015400001c004007158005050303d6110005021041c004e41c0100c0c42da09205880800002d034508010001080305030711503460001c1600740800c013109000751314418102403241c01c0e0000d20031803043c140d880c1c2e2603c4d800742a090b40d8851910f40050300c0300189a041c5818880d46045c0a203458154100220810443c0d44483c4159124000c0145601645460a011030002c0107072108652040d244a01d21500900008d440c110040700030900f10b5644103c144982d958850101150350 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 378191303 1250 378190053 378190063
    0x9090b10050f1309032c1c03080f0703090b010b0304060b030f120a0c06020f0a0908030301050f13020c0a110102011a0904020d03050c121308011509151715010503030406050406030515040c0e03 84
    0x9142100002051f00d041d41c01400b4031001074504111005200002544207100ea0003114250b0b600c001100301c1543e441c1c420021760380007500c04441041c24640005801d0400288038541c650b46100102a95072400d0b81c84802607101003001400c025903a40c80c400455864002421001c1054440940e40c03100100e0040252941d40c01c05003454004000401003542c2e40c203402c200c2002d0441d43c0948201131103013004024030949a0f1140c4500075040f00c4001c0c401114082100c06c01d0030b800911008420040040e080070596146503400600714022801500304034007a06c42080c13003805c0c0b05142c40d0250010b070745080300d4101e003160618000115018024030031412b490060111000910200403a10542c20b1294454007030b0502144d6070780c000029241c42c50ba04480200ba10400c10300c902d51400034150380750341d800118111301c802d42c00d000082c107080000403031301191829519581030030b090400c124007802026003c4150f0000d243da01510582e654852441300034000d031240341240b041001414182 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 378192553 1250 378191303 378191329
    0x40b04050c060307051804020403151a0a080a12110a05030c150705031305070b0706090611090d0305090a0b030a09110a0f0506030a0609090b10050f1309032c 69
    0xa00803d0060060094006041d5418100728001c205c009982a0001c01c2c005c0c0030740d41c0042c1c44054920081000000c456200a44800415034405c048030880b200f8403036840000d101e0441c0391751102c0e0f01440800c140814600c07004d0321615005402c0307281040398070b02d05140d080082c1d0f035540000682ca05038640401c0109401c840001c4480340c10302c0c009002801c140401094210300001000e8130804011061003100c000c0c1c0384401d480350f210b14150030441c00400440d18101d401c1442c106502824285a60070b0704d01214004003850781e11607656030119480e0b00410030198200c2004e020115903404c180d0080c500c55040c0a400190000160900300d803031f00120503529001c0c40d0180c0040c407030040c2c1070f20000d0a440f0f0607121980c0d01d468501030782004040903801030b04820702e403601c103104204070111020b00409040404580d02c0c2d86900400042500260b0407991003003005044550030400d41d081105858004d00301103c0d03074410781484100c09400300001060503240320320514101c0c80c041541c03001d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 378193803 1250 378192553 378192559
    0x80106120b01081906090c031a03011b120213140405060906011421150a091509090201020f120c15010302030307062706020d0b060316110c0405040b04050c 68
    0xd018551001900c000406013010030491119203980c413894040d90040340081c260014100300c0c4c0c41c0c2c103001c010010444d800000031009100c910001c0a40340502030090b800c4002c0c08008041d000102054a9220104119034441d54003032000d004c440802a003140010915080c40d4480c07561107900b04821528001c11291042c00b8000c14451141d03400807644c0b00c0040400400c6588151200380b40e40107103842c1442c2c4080e515a0400c0096115001c8650303000701805640c1c55205d5900c03540c012080d00c0708449090858240c0d11000c000080d0f440d0001c940307050041c01520440442c001d42e03103040c550000007031190170200144808408004102800103482c640b01122003a504660009849200b48040688032a03107644807000098921035406c120700181c080171072203e285500e80071020b034110f100c1c0101e8240c544140082c0ca400c10f401200d00c14a00d210004408460b01981a40e4444802a800e8418400c20700180640c0c0c590f03206540c055809082c14000601e0302e40381041c54401a4013074940 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 378195053 1250 378193803 378193811
    0xc0908010609090233090102210904060b1224040f0b0306070507020102030306090618010f030c0b090310050c130321020307030f030506221d1c0e0a080d08010612 71
    0x281445c544442c010f085121080155591001400102d14005803154201d1403c000150121040c0d038011009041503441602c06100541d91020000c031a4050f40301c030024002e03603c0e40011404890b132144940710040c40303861022210042d41c0850121442191407040756503541c03000c044146002c01030f50358401170714a0321618001c410b9000030b441f4000075280a000d20716800101d0700e04da1b1804035149000327210708610784440d03a582c000807942c42480c0c8820f8412441c40140456003001c000112200d85070003034000c00503400841200300040074014001c40b03034580117024500103440c20301c0e040310081d802603400885081d814142044450030203d640c0302903600c10490140040d400101824195806040000e0541d40b4500881d81c1001d0400c40020b00240c0b5040313806092216078803012590001d0001d8420362207540486950710092111001050030946100d0740d880380c441e40c41c0407403018004d4030620381c0f241d552034080d00e413090404194010031000030040c00800d6200e4112103140c000903400344 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 378196303 1250 378195053 378195109
    0xb030117012d09050c040905100608070302010507030c030e030f0a02040f050f0105101b0c0306180201200316030c15060506030a0e01020c0a05010501080d0903150c09080106090902 79
    0x50340300b001c2c06141a8400d07450b40c0300c080c140002404600d41114000d0410b00000c0c00d00c3c90400d89a0800f4950956442e181c01e101240d0709100248031f01c1620b0303043e10f8507803415043e03450a0b202043c56400031820803880100983c0c0988003403151941c001040d82c010180c44100f88100020b88201150080101e8500410000a5200c403c445170440308150b40c2d6101d0791490f03010803501030100b2465612004802101c140400c0010060b40c0c04a90141300100000200c52000ca03403085202a006030025010144030202d40c0d83d4400c0d15141d441400084a02d03004419420703159071010340006a001c070700c010b15801d00b442f13010114000c00d42c022100410600b42408006000c50101401c4030440c01e035907591100881c002541100c2c4458030450413541001c1813442c01d40d0280c80240034614103805017414624a0500841840042e25400091111103d0300400c81c070008111050031030b030420800d641d001034820800e200700c3c0041c1105074030109010b81980180701100e000c0210501846254280c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 378197553 1250 378196303 378196361
    0x6142b021c080a05070c0e0402031015031e0606120c0312050f03090a1202120d050402012106050a0510020a030c1b0f0510020c0d0314040b03011701 65
    0x554022541161040380c8941200c0720520252040c11000b090352100040c502e2901d50044d01803c00144a00d104840c0703681c07580c03079050240000355002509036102c0d0112000c01d040980100c10344c1c05035080030102d01580ca8403034000b826021318074825038440002200d020310519014403000780084940403428014540d4030322900701030038440500300200c480311924900344a40c0031990b41c2d001034a1626100e003007802540d92a42c2c0003003c1110318a004030049031000340045407200303481c41d0070a0002e0410308802c44100207848000c004a0400622007070070f050003a503030f10420464842e903a10015001d0b0800313060001803090b90300800e103e803503002d10034145076a0006d241070310550b00d881c003c00303a80780b940391441503c8007407030b46a0390044440724040f0741040d280b04410100d90040f00d4501945407030000503a05c031460424035a8004d1588104003020900500f40512099201e619007841e0655540000e0b140380c0082e00700e6503112080700288004407600f40150002000602e9032141c425180d0411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 378198803 1250 378197553 378197629
    0xe1009150b1309020d0209040501151407060e011506021207080415030e0316030e06041410211b021605040914010603030c02090112050604020909030d0614 68
    0x2000c0207100005620040640c0311040710300207050044041d0340b915a03802c4000d0194100104084c0694030f804000a2110ba01e01c1c0301098070541034a80001c04c82518043c03411a44c001e81c015919a030315039809200d0703130000348107a0f0200340d03400104281c1107003070540013428200c5001c81c3c4642c0c8101880904003180610040300c045071401401c5000b0040039543c2034001e440103607410304650201061500e1072421946805142030311a41e16a01203c420b038041007141e000314000c071920142c0000025016082402a4002941d071900340740c84001d12542e003101502000c48021400e154964013040180300300c1a20300f40c550751090024150354202004011101001d03886514825078591102006005900e240c00e556840c0c402c000740000c2d03850341405041602c0c406022070040074000c000040c94640765940742d07282c650007400303420710740c98940030004822009410300328940020070212802060503c110001844115a100010915002005081100c07141400360400d58403016001da80c2c02250 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 378200053 1250 378198803 378198809
    0x1150203160201030b0a082d0d1b0f0f02010815102102040f06140c0703020415080f011b020304050306040b09070e010608040606061b031103130e100915 67
    0x45080e0070346400101c0207000245a2a44c1000c2104004280e010000c5841901c0500800e101030a44107918945144004100c0075a101c40e000222010503842c400c8080f03150042d240401e42d9030145490b15601b0000c40304c988100c941c82d03414120b0204550700000241e41c02800d0110103061048008082010f0403080244441004000781480c000701c141200c400607292030b01e910464840d511111a1600b0324050301901000c2030f1102000c5586440d44001c4941080c14640a003011030310310307070a010240003005002e0f82c0703604601714045942c42040101c150701320403000c0041900009581c0001503054450b08100454004100500280d140068619003080d40080090403585e92484250b0a0155039001f00544007070316800042c4c0c00354009003e9006601a0904020480ea581c005032014103000c003820b41c80e001044100340100e40110f00c2100b440002905aa1600401103440341000000b5001000c25032b40c03580a21000d540318080c10703c00342c8400082041001b49000c1034100103010f502c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 378201303 1250 378200053 378200077
    0x5010603060302060313081605151003050319030f0c03020304030314090a0f08070209070906080606122a03090a0b1005010c1e0b040c03031205160e010201020c0303010609080601150203 81
    0x300d40141004551000c440315071103503041c0740742c23242d2640c079020791100511905503501c0352410740415000b010b80c0360014210383d40300e0f00451810801c1101c000450f1108134000d0145540c401c03414114890600406040800694005a8900c0c007841c010b01112710b2920407840204020f000c000e00000f001400aa0385900b141c3e5070712a044a178a80801c0724860f5520003908083e03a842840440f0707820940c2c203000d40300e0070740f40c181d52641d4613028040e0a025019040c40c11004040106403600115039071803003064030407241051183c2c8241c10200b59a44251016440c80d801410604148a101e10003540c0000241084003c3c0b54034101c0020700d50294040098418220041c1803a05213200021000d00d96601580c05d00d000d14060503c094229590f21041d004240d450751446074a0185204145c441d961a1403000741440220302c04030388000c50403802c00d042d90b50030045040080c8003080598020b0001d5035802e49050b06100c2201c1c2441010303440b6045001c00804020000c030740100c01e0702c920500030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 378202553 1250 378201303 378201331
    0xe06180a031b06081e070c05190b06040605040e0303010b16120806100206100b0903010f050f180303040803131a2e0302060d050403021c05040306050106030603020603 73
    0x60400a800301080380e200410400400501e0780e05076441c00410411a16182c03211402039842c030b850680b54020b4002c94016901e881400070b079140e4014031501048030301400440d030300303c070501d514000900b200403020380d120818181004003502e00f9000e20701c040c1c0000d40f02404040a190710195590106018403d68118003051004d2660100802a000d0b25000b0310b82490017050264050000b8000380d90a500440b20a03140816890000400a02074540760b18020309030b600c5c041111604c1c1e00010380259041d501c481c189070000c4070500806006526805800300340b424908407038500040c0501d81080700b038105000f0080420f8046003503e50000f0a100081806482031038032412007035410f00c1000004007004180202480c2d0304900002c0b680030300c6409100c2d90044182501e401c0d40c1d03840300a42c4002c040203086135803200398200e26006403083c0100d903c580700042c118003528070101c21100014601080c20030521402d800341a00401075070030100480390442d00414100d10006017091220040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 378203803 1250 378202553 378202597
    0x2041b080a02031b190f110a1212060f0e092b0e0406080c0a080613060b030307020307060f1413030609020d050d05120a020301120f1e080c0105070e06 66
    0x1041c0410201007000c0050190b55550405c04540348202d00440c0c140010800744d00c9806590064000340001d86402005000b262420790b82d0344040c20308610321501700003200c032514814000300c0c00b07800e002d00607483c0b1040549051901d102c5100708001c1525410380e0200f00c41040406071820348900e08000740c40340c20403034520400c007a606240e11407000d131340161801c11300280b1030700d0100300f11041400803688014165600d01c101c69813034005030381549054900d186c006d00019800d902c51405400b020f8281c1c0d00704044e60300040d0624029902c26004140000c6c50b0001150307000c01158a0544070302249405c007012a0942d2644540d1400010300301a40c4420b01c1c402e654880c5401c034000f53f40310781110949507806038014400e0b0490300001980740c910102080c2c0c0090f460082d00c0c16101000140c13000c0c40407640b600d121074049450203954901c20801c85074078443c800702c0360b11718140c0904160381e0754254292051b401c4810050040b003c0000207010941980e90702402c58020325943c0102e0321040d08 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 378205053 1250 378203803 378203821
    0x100b06030402061e0f0a0906020d0f020c01032c1f020406020d0f0201020c070602010204090c0c050318060705010e1c0309150e030c03030108011527020a03110a020a02041b080a0203 79
    0x1700d0441c0d4081c000c44086885407001da0302c031040c4401c1c0c440550135078045c12100d010641d400b905260794040986c02288140303034154801c1e0312100c5214507101140c026040a445800070f400340d29010300409400812605861103000055280c01503194281103140034a0000001d4981c244004820100b220740409802c50602c01d4056a0f000003031042a01d103455076545020b8001c0d0b11034816107004a0500003541c8200b80030315040c3c007102e500703e4040c51030a01c0500c1d603181d00c100d0f50302c00158009001d21003171001c40e10910601c5c02e5440c1e12001800201c02c1100b62800e0b030340080320014105410007400a000540c040c000c540424526100800c5032000b0241c2d480c01c60048400b910407d01c8044000141040150041008942a10300d80b03a100c641398001910400a002d030300f4004174040e480806e4030000658000e091a0a032032500007414940b80c16014a280d00941440d80164032000060065141074800d0ba030342c201007280250205006040c0c003070302c0100010555a450340e804400200881 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 378206303 1250 378205053 378205057
    0x105100819020d0602030a09020102060709141003090b040f11041b030e071a040f060e0604061214010311090708090a11030c0a230607030c0b1512100b06030402061e 72
    0x181e403140085d0749911740300c441c29000702064401a0300510541c00030802d42d5000361440d401b9076107080b5400c20b803c54500e0501544440c00c0341c501c0c04065544002034007150340d050450303009038400c1940c0c901c20242c60405959001c0c0c0300c059240300d5860b140d0000b012a8208000030068850350401045170360a800c101420503980394010b0340710044100c0c0204680024100070001d603500000c0315900d05841b01303812034500601a501d01d41040c010442031110318021002d44160b03001010001c00d0248440d214a12405000e920032208284503880004092500002c1280e0105032441c1c107003c685080e443d4665590180c81c00606101104a2040f006407014000361400790005850703100c007a5550840e542602030100c1c20071030b00c034034908440d10f29450080d08643c001074240d133340c0004c0101151075415114002825800183c03281400340c207001c0e140c0d60f046d21190236801d4040c014409407131240c03d003038030030b101c000e075109060130402c0000580d02d1400f03841070780c90104a10848007420854000280c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 378207553 1250 378206303 378206329
    0xd02122104032c04050c090a170106080102120a0f0c0e060c030909042904030f030e03120106090501030b2e09120c09060803120408161e05010510081902 67
    0x203121030601c00d0750401c20040a03c0600d20b059070200025621840080950b000b41c0040b580e10502c44241084000300ea0840510000180000041e411341c0d0351b00103500f245c0c8400030048400316042c1c100880903419201c1c400a000c0070307a105001500d0b2500008240c00702d03006096100b904045900103041c0e00030026035804480c00380c1501039504240c14a00e400c000700c110200008a107103000c000784000d98045040c0656856110140c40b0503550000f0b0713019001c2c1d204a007001d44428400c0e680200e10b06402c0364024140c9499030040c9070b09200004041d1004190480c1c068060141300300f00802140c920345c12458214080c3c2801c400c00c2c05c0080710120016849094040042c0061100348100e020300380080300d83c544c8040088a6032801401c0e00d9014004000e403a41c501c4a00050109405100801180d5003e00740002c40c585280c1e2500240c440c010444060303403041d0b001ca441081024416640c00881c1e6030b0580380c0c0d0610340421240d40c0d01a070035131071b0308400d0400c1e8a03004644525851101d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 378208803 1250 378207553 378207587
    0x20d0e091005280b210a0b1c0501050a06180e010209030307060f0f0b030d0e01030b10050c010c021f0e07170d02010c030b030d110c040203090d0212210403 68
    0x1101c91803200702080e11a0580105260880c030010002d13141c03111504070368024582d10000074400030080420864010024084a50b45854000c0c072206aa1a05240301101e642c8c015058030324411400d106084071310081440b5011803a0945c1840b13a00341c11071048406110705280803406005440109019004050049030584008130702441081520341003e124100000010400f0840415003141030744c0000c011150140c101200d503000440c4511036040e604001814086a03654500c80414001100103040e5400202c0c0880c0503507424500b8000c07400d01502600c000c140e031580785502c45c01c03032501480060541c60303600c0e50503d608503418050a0010010310810f121107084030b56a0702d032103035000302d904001546007814500140c2e001c0c0c41200480000a0300400c05400b9203542582c840300c0c00460a0070b00c1c4a881c4d082c500079642d50008504c100d900c00e024043c109400c00c000f03403900d41d0b1441c0710044c00e02c084c0b000c401d0b034500213100140c03242c40000100e40103031214102510030600035105208 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 378210053 1250 378208803 378208819
    0x90f06010b07110607030504030206070c0320030c03010c0509092503090b09060f0105040c020a06020a0224010803030406020a0c1704080d170c4006020d0e091005 71
    0x4081e507014000c0c1c48114012a040c2807403645440c200902880341800050202d5010b00050016081c910040d02c005407050303038180080e030303102e843d60201d00704024000c8800c0d5440054201e000e04003806a044035050a500a000c980b240ca20082d02034083c0c9800c00c1d004016120004040e64915965811548061940c111700c000c1e1142c0010040c1c100031100303641c5050001c0100ea03085200140c41c43c81080c100b881f0300001e908007820000904840c0c2d01034000c51040c11031440201b0018070003015100807039001411180c20020a49000d40c0c40c65100c0302c00a010a0300401145a0120403a81e100c2d41c0140c1c0166201540a82581d4486140d04080d0066001220602103282800700820940e121307201101c000a0700300314102d5500d82d840c0500c0c140c0171028030118080410220141414003100240304240c1401c581e0940000f80200c404182c030303400d50000981045400007266805010a8170192800e0301c10080041c2136007414800780b41c01602c1700720003e1110000c41d1002d80140500902010f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 378211303 1250 378210053 378210059
    0x60f031009120807050a020703080f2506060501020a0308070305060117040c03050709090816081e04051005090102210f04090e07080106050919110d020c0d020f070e090f0601 76
    0xb21070204485500e002c281c200f030101e41003030700800a48451201d550300070020a4119030b9189095000080042009682480081c143c00d4004105c145260400003901c1035400780e500380101511301561045065400045002c0040780d4041c1c0304035070140680c240800c0944a00c001214450090101402011444c40900c02088401020301d03003107a0150003242c1c0400c0e101c2070500304407001c0b104010000d0724104140e220980c040c8002c07c1d2441e016807001070410860000d50000480c210b801c1c208104000a814001c41c032749500d4500a00340da924143e4203180384000080c1d81c44500305405204048403001405007141030800b01d0b1181d07040c0c04281ca0b21150356840d0f80303000e420185142d60060164074004501050140b01c0c210485400401c012900c1d150311130b640c00909044d036035030034646443d100c401c1021001440107002e070904220005a071030104085042c240b84031601d00408540148816401006000580d482596078005441c0d0403611845003031403401300110341504003405288000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 378212553 1250 378211303 378211313
    0x20307030b120f07090f020d05040f12030504021503090c151305030a03020a4d0a0803030c0a02010e01050709150c0309170307051204050406050405040b060f031009 72
    0x4802400581c1c040c0c0700102d4001c1500e44800300320324041c03a0b03540084410060782c070003a0005010903504040062a0000305c800e03000070b0707420071075098034100100d06605003049090400d8612685082c6810401030400360f0010b41e210038460404a1b50072808808141d5000c000e00090400040003800d4892000c62116080016000f8407400d0346045c110210008032420007240c091103850b030580c041c06811b4455516030042c0b04403024011400090840c0e0404480011140300070071028660707540d038001c108819101c2040c10710014250107584400c034104018980042130701d8200a00052540c0c45003074041040380184a8152802d101d903003400c05011086030010030203000d0391940391088075008006039007554290800341c80100060110b41040107010340c02503115801011100a4a1518003141c81d81791800f440c0042080600034001410042d600e0644920302c0100002c0c0c806022510340f54032903507100740c402042d0300d000d0040301064040550b803d1280b42113101000004004207000c0c0c0c180303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 378213803 1250 378212553 378212561
    0xf2103010b071b29041202040e1c0201020d1802030a0213020904020d05160f020a0303320105010e12150601051e120f01050f0f01030f0c03021309050c07110a050402030703 75
    0x4066480c41c4c41074508400c04103e01c0c115401d83e006d250080320481000d0742403200500300f040280078a8000c2c11441c000d04004c0004070100c0d100c4039400580c031049030078480012074801c4240028260820741d10303040161400b05000440d40d8049640318520900c68500e00068492018540d50141c070000e511030040c07102d035004500032510140388100c00e6502c002d00740d500c000c0e0f944505026920000c0b440c00080d1094100b10103070643c0418500d45850120340b01d1802c400542450006882c02600500c80c1c0e5921108044418008a809000e0440000005a11079000321a50300b052030503200062202e9004034121042e8201e4411101e03941d00c055200e6586540003880458418040400401d0a03848003030b415038141c40e402403000804202c40020401da40d00400320301030525844415140c1171490311303c640c0407122a180c4002d0303903e500ca202090b1030b1480e90307040720301c0d01c616100501c00d08407408425242c2c0c00394043e000c0d0340c42c0320707003040010602203580e440b4980c0940000100403680b0340c5070708 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 378215053 1250 378213803 378213839
    0xc120408010b2205060105090d030c030201050916090218180708060d080307050d090b0a0605091812070503040803030c07060e0703050d0c030513080f2103010b071b 72
    0x8001980c00c0c0020000c195070050f0354003070841e50303031000c800341e820003a80460340021381414018500b1b0754100c040381c101c20301d903503042d03002c10001c4007072105054081c01065842070740712014086003007103226001007030707200c9001c4c11060981c0400e401302c0b40031380703110708100d00200200800405203d5a00401c1e611208550000002d050741000c038071581040003aa2550365440000c0b54159611088125601c0d00156100b51303100352215401004281c1088203107000700552000407408909010170302824100241150344051000c02a414183d440421280c0c0c49048450000da130340e0325030740ac040b8514041e64001c2642800f00109009582c20507030020440346120304000e100d4050880d440540f140f000703200c00350068010702c030203102c41c0f0b01c01c0c440e000140d4401d060640c02c09450410040c4080702a4024000325400080804910141040082c0b880907189032007200c18843c80110f180b142c00306100f44e992100d4041008420007030450150850b0841c0b41c5810018150b6510400c070080980007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 378216303 1250 378215053 378215069
    0x118050706020f0c03150411041b030b031609150305010e1c1107090c030e16050301050c04081b040603330c140705010204051002010510050406030b0403030f020c1204 73
    0x120304450301c0800b081c1c41300803503030040c00f901d407080d18417034128500c15006004035000b44442041e035001c0d5486204504030b60391010313409503620b03944000c050210740c00e0104141c131a522000101d40b81c050030003031600940361500008120b9441300c2111001ca00c2e0190002007140d42804943c2c2120040024070618400078081c422440c00d800384000c0d2020700d4002a01001074014140c18080c0d02e1136a00001303222041ea10b40013607004120b0040b2803c01d414030b00701c6520000d40400c00c2180d481c0034003403039821402c6c1043c2a49041d150030403065450108a41104072443d001d00c0d40103041d9260341c00240219000200c450140b40180710740c00c041299012400c4805440204401c00e802c524407807404010f0082d02ca00001818014030a0b9494005020440e5190b40800c00800c103512130b01100b51461109800200d400c0c10442c1c4000e07290326103900918041d901c0c1c41410800b08240391206604250982000101e4400060610000c0e210b9185003000705d201d02d0840c403812511080007081100c92075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 378217553 1250 378216303 378216313
    0x1a0c06090a06050c03040f120e04020403050c04050f0c07030c051e0105041208150103050903071208040605090a210216060c1b0803040527390a11011805070602 70
    0x300101c2c0e003845c00240c2d000351102c5141054000082c4410066415034185428200303800144000014140ea10036041220715411940c400da039103003458000d5503000b018003a514141c9280032900b880c000c0c01490005000c00c034040c03201d402405018040c801580105903001500d001402c00b2040c00b03003c0c184c900303d8481e8a01a24100f02c248111076144c010103864200003542d20b0707c140114080c100c00340c80079401c0d0004010110000302c0283c00103800c402541c0b03582e0514030f420b040850403544000c0112038503400002e00799000031480301094118030140111a0002500c0076012450480c0100b0b003008014000140030036559002540785c10003512545905a40300e51810300e000c4800c0e140e1180700750a83c024401800549803818400d07008500307014655100d800a0004600003400c26034804030344d8101140d0349960ba44140510b145848002d20300100303032284c1081a1400392049840c00c0080103000d400748442d800c003c1d003011a07407010510703800140c1c44050400c1134640219210740700c094410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 378218803 1250 378217553 378217561
    0xf0a021005150f01020c090f07110111070b0a180507180b091302060f120628090e010605030105160219030905100e0303070c0e13020a1a0c06090a0605 66
    0x690700855119102e01036042c40700a4581060100141114000e9415030281440401c240c0e00c0d0591810b1007070142841030401c5080c140c1d030140c40c0114920f00070b01c459041200040b01c889400044075185680030101ca611b55540c14404d1004226885544040c000408201000c0c00400188041503507503542c41c1d501c125959800b0b08080700c50300510f040c0c200e915500004c40c2001003041c0e146240340064401032511940c220716048552204103a21480382180003070014a0501c03012100c544800c0100c01c8003040d4180e50038544006540c030401551b03544459012144180139003020008100140090082d820003c0ba003046000242c000000140310b8080c50600701c80241c2007031348038141c250300c80d000940e00308400e2000a0513000c81c2c56003400301544d40000d968500304001d0000714060501c801d230403820403050700c1c00c202e00a8040814142c40700d5280000d695144000412155220f1070b403d221408104841c09501030300510704c1e0940100410450a20705c00b04500c14003a1040504104680e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 378220053 1250 378218803 378218833
    0xd1409070609030506040f06140403090f0e01240306050301020a05030a1109010c0b040f0c082a0325050402040605040e010602150705180306010909030318020d081e0f0a02 75
    0x299407001401550220011801242c41f071002131202c01c3c010307007002c2404072040c0342c40b600400c002d5030300720700245907040708016a4103083c200d440601050059034501d949440e01d00700c0d84400c102c5038424014040030450315142c0c02a444580100000350082d5180e100204014050342c10403140150351711b082007480c07460030880b801100c001d00016102c2c0600060703151190399420740010000c89985075051041d00c040b07507221401000030a00700000381030110420040140c1c105860850b00345010713114075060410350f070100b49440d40403607016501d00c07a445615244e44400c00d145c0e0002e504503100040c0807510507072020080042d035000240103100e07a642c44000300e82e50340c0d60314070080910011303034086040544078100502d002000c1e2141c0300a28807103240001d0800100781e1043c0c009907078800c605010980c050042101e480b10803e42c8510b0720405070080740b00c6202014005000c60340029201d9408105242203051404070031781e03407a4540404100000e200ea0090300000c02511540703100300c0c6403d07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 378221303 1250 378220053 378220067
    0x7060f08090c0d0b0c07050a110127140105040f0f0303020d0f050a050721080604180803011e0b1c0e0a0c0b03060418050c120d050f030c0d14090706 65
    0x41c1010f0a114900c0c041d07501c1e030005001024200d000c52150411922010030130403c401420240544060000c445419002414034680c00410708650701141d0034500440c02d0940400c01110910400070b90340c5e95200700100c03030600c519044841301c2d122015000c5180e10300c141e130020075280b0a400f140ca844a00400070f0316044d044c2241c40000440c00c004001989101c0d8018100061090f0030480d0034100200320f01c91040300c03071102c0d4000600d95000300045803a090281000412141d0450140c0c0182c64031003000f94030050042001110f80c0c807111442d141c05220840d8010107103074031016114080a0101a0344845000c90040c40d9400c00d02040e24020004c2100340f8000e60082001c001c2d0746c500802e100340ca82000b403219900554550386496140c01520392038010a2050004d41910418a02004070350310b91002c4a91899003c1d040c50034506401c1821549403a0240c061039803a07581c1c80603c00014400c8c800740c50301083c1411509402c004040500314001c61011090700c00d000c0e202d240441e641c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 378222553 1250 378221303 378221323
    0x20f070f030209071d0409060e0f06070306090b0303030a0c0e0915130b030d0c0602250203010507030203070804030507020f0a03051c11030405040509010212190506041a010305060f0307060f0809 85
    0x7100411719502451520340e1000c8075140c403c090204000920411250520b00444003402640e00900f080104550b45403103404041d044001007007040e01d0032000070070b40e80d000040008503142d944030080040f00c1d0041d21800c0305581d0091203580c1c64076200b0010b5580ca04038aa905010b01d80b95684054100a107001d074030b0110401400038182c0341c004482c05c86008601c0b2800f603810b02d07402c00c82c07103984084c503039415026032004000b0f6065940d101d2050500f1128024061000c00d4414410b01107056482502075400c81d4152034020345424a5000140b244010080d2184d806505020000f00300500417444081c002024010000303261a80031054600304c1c0054241c00c246d400402050040d0f281c1a802550850020b000040c01e003c0c15334018044943c0c10b4a03481c4c0320010200805614807100c4c0149548118151402d0160700740312406a000c0340305005005041c103488100007100c50311904082605010000c3c212046c4c29540c80000e406032101b58200c038001400c20780001c0c14564000340300d0801c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 378223803 1250 378222553 378222587
    0x4080f010b0108040f060f0f0915051e04170315010f030504030e120f030d020c1b010c060b0103021c0501060908210f19180e040f02040c020f070f03020907 68
    0x3c02e6440d5035032440110441070f0200c401c103603074500ea45035801b150302ca00e004160003c0e40024101c003107814006040c0c524102480315450600b41008409480c61509040d018a82c1c41c1d00fa140f42c4441c5004004000d401c441601c1a0502208020030200600840340900d9003e8032440e54081d8140d074110151501100d000e03010a00103c4146050f060110b07003441c000340000c041d140198040101c4a05680c4009100c0310b00c40d03004038076031922490a001005241041140c0d80390000c0d04540040e00039084003501511851f9280039010710369010741c0460300b031800708107425040704415442010003010203029150000b0400100410321400001e594800d45e440302c1c2e114040b0504811080205501001c40019030080500c601d00317135066400c0c4140c209129549940036502c051112040c1d19804641c40045140c4200c0d06202c007048030521a964420380603030300881c41140c00d220580c54080300c407140c1201c0d40300d105000201d0120501d03040c0c041c0c0c0d101702c030785503060345a14008607591044180c55100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 378225053 1250 378223803 378223817
    0x70b011a0c0705150d052e08060420090a05190911120a140304150c0f0201031a19050906010305090d0c0c030606171213091d0304030804080f010b01 65
    0x440d0f450000704d07102003001d0b804d004601e80f00801c0c0719031042c1e0b0019241c115085441c04071881c9900d80000c1900c50032040e0a4203400a6890209565a104c0002e04050000b501c80380c1e50b4492060018030200f07400c01d02811034056802c00306454002441708550b04c03000826031846500004200c1e0054640550300300d00d1000741c10080c0e000b000058003404200341854882c4c01d1500e4001490115440440103418000c0d45c1c48924100c42c83d0b04051002e0018010050400c2c1030b400098085c1c200600c400c0d40a00c0d002a0b0031a41c01801d01200c2c03c1d0390046a484000c45410300d031118038194900c03003070360b4059542c550316441d00001501070340c800769010001b41e005001050196840342045031042d50041c0e09103030b01603550392a148103e0f00a07421841c0200728104590031202c10801c14140c800206210310780c81c1220803000741d4602038440c003c844140d901c030100700d010780b94802201e0144907882c4054039681c5a50745010b04090780188121800ca01400508000e90a810700c03035524140c07410707101c0103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 378226303 1250 378225053 378225059
    0x10506030307080903070905010312180e37020a021006050a0519030210030504020906011e03020c1606020a05160b0a03230f10090504050d080c0f070b011a0c07 70
    0xa0f9680e00710500c0d041d014800c0e41000600a242400707000d00071030285459100f6104071080080001e00358407031031814002c540c5010448031560000d104e0b84440c882081c4807900d0070582c41801c0d0404492004550101c514209043d100e00da40e00800040380b40f9000ca07442c40b9000703c0300c0025aa482d12a1340e174080b03c000410005418090001d81c42403130782003d0042200c1e102e6000a0340d220380c0444450010343c2d260204000c50800e4803416030031540c01d0030700340c0410000304014003a1109410100003055004038041012810400c000f51071035140e01c100c95095070700c0d044000d560b507180c081e003551300b84070f01190b4104968002162000795244010714918000250a007a00034101041a500303403d54040c6078001c0f56664058001d01580500940050506110914000040c060b4100000c840e180c0801c0c440090000544240160031364189002e035565011058000703401090400812078400144000030080e07500511030503580b541d0703e040c146103d034800e1183c450041240582c2c05a018034028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 378227553 1250 378226303 378226313
    0x90f082212060e0a0b070504050a080a0f02040f090c080f01050c031b210f0105130b28030203060403050a030f060e04060b0604050a0602010614010807140304081b0c030f010506030307 80
    0x90b0403000c406500b16950802c44d0303944d009400004592a400080300420240302621707000030310000808a08004003030f0b090903519110381718492000000e00c540d03510f48240314450b1154000341d5003da00000301c0802c19076a075060350303141c3d0500f401c40d2070694079000002d480d101e0b002e015a8003c02e592015401d0703d1590f541d10200541c049491090051103500d80c800380c8501c0f5081152280340e07008440441035240c13400f4040100003c10400c0002030030320101640940f1034500509001d20071705032007100240c0980e4452801102d540000e50940203400410090507001030042100800580d4104038103510220700303000702c550300e0003005095003900c000f09010505e507401c025030f5914001c1c0340b42d182c165241300040d629405544a1005030351a07100412a500101040f0016000282040708081c030742a6001405840300c005914040c902c00300105081c4490b16042d03d003401d0894880c0719001c1c9105c45034540e2401c40380c400700e2203407184003180100804103014540c0aa100035000f103040203a60741e41c0e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 378228803 1250 378227553 378227561
    0x606030c0904080d0c0210180201020d0201051506090a1a1e0301050a06050d0b130c0806060f0307050c010f060608010e180c0d02030f0a06020301061403090a06050a090f08221206 78
    0xe00c4118030403a0888015000355104d003644208034000c80d907230a8940c03440068240303101082c28a0569251004201029000407004074540b9000c0b20541c0e078851803040000c0e40c0382d08540012490100c47c4900f4052050348800070202d40606100c2d201c02c001c10300c4d0525806200034000c4c103030020340c9040e042080c0b600500140130600c00b2100042003000215001c00c0c240f41c00c3d844100d525036110030360b11044540101031150888026a44503290aa01c3d0000210911001d003829082000c0000d907030035801030a40c050700440c000d007003007401500e580b03040013080000c01380a0103030700c8407c0001044d03c00416542143c1c0400540020340302d8001007000308880d40b5002213050340c05009000e18010014010700c44a0000c2c3e10582c8016100e5040ca00000c0ca440300045136411948410014400c890b0307400a20f41141315800080410360360349040c09200600b000c40c0c00206090a212074150401c218040684034100220540c000603284003400c0110200d1144503005019444070704203c04207141d031300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 378230053 1250 378228803 378228821
    0x2040302130507030902030d051b012f1c02090a090e1b0d0206220b0c03090409060b040f0606030506010203040e0621030c0c0102011d060a1d0d020606030c0904080d 72
    0x1300040d5025503900428104a002c0c1142c40011310006501c48035040800e486800d00010754000300006c541e21016203482107039400f104070900441c0c2c000000300c140c0c080d045903a40b9400b0203c1c8101e50104000c0400a50005024a40318407040380012844154500c43d0101d1f607507000006005056000501d40040d401031940d9941040e100404140541c540000030680210340048415040a18403403660b0b054110b03811548001108010041d1001c0b000030680c1c8801c00100d41c0003448072441c2c070784400104203814125030018208900b016150582d64803201c01c544440d07e090009503640303001242c5034442c3e801b9000c98220980701241e0719003403141d00c2c82007413660b030a0b40014058070000b1080c610741218181300c00c035a12400d00d180f074035682805410212521900c0d0f280e08908242d00c100d44411006080d00c21075503030b5518032246203d440b01c2800700c540d0745074151200b08099950080d100c91040340c1c028084e1082552041c0c850900c004001e100e140c01c2251903042100001c119006071448403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 378231303 1250 378230053 378230057
    0xc02040b1509090c040b0a0e1504030201090308030921180f1c020d060203010e090c04020a140d110307030b09090a0804030803040c150c02041a092802030a05041502040302130507 78
    0x400042070003c1080b0003403515143d1f9440300c6140720a2582048422641c07040391941d1000b0521007080140d030815500b80590754090005078890f40da0000c42031620041004241c1d000017a0b11821081c0241a402410720070b51450014800e030b000401072154180540000c0e94004020703601c2180e40c104220000841a4401444e00c1030580041c2c13640e6040e0381023038101c103020b10400410b00180c21401c00480301c0c0b249041d1383c25802d00000e90405445007001c5078044080c5500011086580c4a007540f01c04010801642da4580381d04000100400410403601514017524916011846540001403541580d0386d000300500d2900d81035642e0186950005041101c011000110219940d103401c403210f540340444e955151804112030040000f503c0e034024148014a80c1801848005d460701c1c41d8040d400300c0da403601869910500d070307681038503d01710080d107512241c40403083c00a40622030300001e0050380140320102008140b0b02ca04412881140300007540142c030f410300301003120f00603004281c1c088964 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 378232553 1250 378231303 378231307
    0x302120906091e0a0b04110a0e07091710061401020d020a110d02151c0b06030f0c2d04030311160e06040b030f0604030f03090b0604020304051c0c02040b1509090c 71
    0x130703561744410b03660296001c581041c0c1c40c481c0c04000d030a1821f00d09005011400c000d0049051800000c0e115403042d019610b11000d20035030790000c441e41080a40c90118281c141000055541c55080c1e41c11014200700e640180191112041c4191000403441081c41c0c05c00030080e82d0349803440c00c002030100c080740201e8015900a10891100107688080c0040b5070503094010100300c0019100c008a502150143c0d1040c041802031014603d120803070154031920902440741d071070004510202c2c01201c400c170182080340070325003c4581c0340e44100c041c100b20381c800e0300e8a5950100381e4408945039100c500c08103031845159041002041e400256071f680203000070f0800202d010240780881d060403944901e81213141c0c8072505200030961701c90020f5a0051040c6410403003008a5969880c1001014103094480c1e40c020001c02c1c1070280610018054a01c2c081659000101c0f51502400c1204482000c2c0d220f01d1900b11144514181705068201810104042500c0c01079240d0030040c0d0054040c000408010741 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 378233803 1250 378232553 378232573
    0x110f0c13020d1b020102070c060503010803121924050108090d0804060f02070f26070201030207080c0d022a0904060c090509070306090e0f03120a14070302120906091e 73
    0x451100d1403040007103038000750741e61f6007a0404800400c1c480d400f42d001c1100070801042500804004c1e62200d911382d001480960701e4005240703118200310010040414648901c1c5c0038459000a44500c40381800f120301841c2a40c0e0304015a0b60b24001c5490040c242c02c44900700b6100c910448031a0b900503c01c0000085101c083d20f004422078104102c00c440240b0040c401c0c10030b006840c005000c0107a20484820070100315490741c0001e038060524024141600490350400300700c80c07c0260344003040400704944400d040c05070000e680d030300d07002c5032090390301ca02d0000c06c0110074070b090b940703480f160002d4840d000c1174440c0c0d6580401803074129010010440c0b17025012410380d45a0803a580250300c0e550300800d4550804140008944409080503041e5100c042c0d10a0700708008000e80c1e2400c0080340c003003a581e6071001d00c00d002802d4031801d103c80010101041182e21074140e4081c11001a221007030040503a02e0203070490303031800190759454159005443d44150604000d904694181040081d80e00c0044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 378235053 1250 378233803 378233831
    0xb04050703050a03080106022512020a030b0f0711010b1f03021b030903100b031203041a040614070e0a0504020a180b0408010e03040f260607110f0c13020d 68
    0x43c200000c81c0000c0900740100070030359041100511a4030b60080c1502040c10030076101203030381d5991040ca46501d007000400000d640d41d81403a0002550000d2441915203400d0080c542d03124011246400480e544160480581c2c00501c03c00310114001791038840d8440e4070001c026900c244400c407140805400b04451b50340240e140307004402001b542001981c039079510004160821a21560400407a40350841500050360000b807140d6030b150400386070694035199400c14940300c04098103080380d1008000103001c100016540b18101e24810300030f072403803140c0b29840e049a400c8550010990311012100050140346400d0b4000c00005090b414061801c0010000c40c0140740c080741c0c0314141c3d2002c04901000540d40a00805401d0101000914038007410320162440e401007d0007000805450a0300042c105044540b03c06680200401102d00f5483c118100030004014462002c1441c0565810003148010001c0e4035005290b004100350000300d2a42000d500940007003602d990041d07251125452591 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 378236303 1250 378235053 378235063
    0x5180d050c0918060a090212030a08071d010e0f060d0c0801032109060c02030723031606020c010c1a0c1b0304050d0b09070f0f080f030c06040b0405070305 68
    0x26104001038403045003001c00b04001c80c0001021561010b000b0a0303c078101d1600482d1803903002c01c01100000d900c030f55600124004542144030015a0f03c0009140c941d0240c0005a407071140c0f6055645484000740816603a00c80b02c1c0c20314460740070482111383d1074378034500680b07102641100a0b107a14203265015000400b502c040e44010008190b084c1d00502c1804184100080748103c0b2118002c0b400d07011804c02001c0002d94803d0a00308001110110115070781480340f03d00074030302d0380c1c001c40360b170041510901c140c8625002c00a22038419414000c01035815046100b04469a0340c01810310645844010340b900b25801a0454404902070000100f164680c0b030780c28000c05640e041a615072140714081580045905c021400c80e910a000800c10396443c0c078110390540794071140030074503030326424405480d060301900a84442c0441150203d20760b6642840202102c0c5800c0455000c541c040750002e0f11383c0315207001210710350801e400050204440b4290190018440c50443c2e41a6580391207140c140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 378237410 1107 378236303 378236329
    0x2070323030301141c0302100e030f0a080433020d0e0601151706060706200a030c0f0f021506151303021c050c010518 52
    0x1901242500004a0429101265143c0d616100b5441280700c496000c81c0c06005801e40e52407802c0e841254031890243c0540207013890860300d14500001d84110002210184803c0204680180004000b4007014072140c0d60000c00f4142444d02117460703d4403000c41084281c0384e0350a0307284d4103a0800080c82c16100d5880c016582c040340d200e03000150808150b96a018042d080000400707040f04421040c0d4040301d42d940180c1545c2c100508202100c003a80c01c0c03500900c0130b10000000070385a50050b44203881065a036802c50141d20700744652988124001c1c400261180103242100780c002e42c03000500c03a01820210025003408900a588820524204910004140118220340c03079800701004102d0701000200c0e40c5a05503641d00c802c4584600c0100e00070325080d0340c2a191030a5003030503d500140d101d07011b0710704a19541c00450301c0750050b11342e1200c120790460b10109140d03a560ba6201003 = true := by decide +kernel

theorem cover : BRFrame.Cov 378057553 378237410 := by
  have h0 := BRFrame.cov_init 378057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 378057553 ≤ n) (h2 : n < 378237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
