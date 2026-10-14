-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2898
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:04:00.684142+00:00
-- url     : https://prove2.me/submissions/326f7ef7-91c2-4eae-89db-89740cc2113a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 521043165 ≤ n < 521223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 521044415 1250 521043165 521043181
    0x60415090c02010606021c03021303020d0b01030c0b0f03150a03060f02090a120804152706020d090303081504020c12070201140301080a0f02060c1f0b0f0a0e09030f07120305 76
    0x2e030f40c460250040754109069200100e129502030a02c2000848042b504256241c00142e99502e05034011307200b004040004008010362a04840b0003403008403481410b0002008141e5018080103000e0004c1071107034003d544840e51a20080c40140d9070024040102d03c0000400100941003008054040c280007400803075000c0422000a02070f581c407a040764501400d080c02c207032007210445242424059880355110b465213011148451510344c8441c241080da103803072802407409040031843c274280021a64144046907005540e50344c44000d0300313894020301000401140c000d200d561404192030003000c40b0280c9450317002004204660007640c40b4128052500e0700403455120a03c0743c40030640c8401d110f1000aa9010740c9580100d000a14072420720f8102042c3c1800d062088040c02482c0344080c0000ba01c0030400d01c05c1c0b109500040d98120710000084021a072a241030b13000e1a410100041c0004000740d00c204101c0300c01c1d150b4403410355143c40b05d51919640300100000d4241c00700f0f0400740069460 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 521045665 1250 521044415 521044423
    0x5070e01050405060703030e1903120b04090f060e16080f0f06070e01081815010f09140411030304051203030615030f0412030e0a0b0402030d0c030203070605060415090c0201060602 79
    0x203030308000c02135440e000c550b586c00d40007005520742c0100c0900900d41c2c0342d0030010f00200c80c55005030094880508645000c60007008035000111610b00ca149440c4d8000040703034110b0005841c0d61742c01030000682e5010801d42d107241000307508485101010041021030150400720f159a21f00a03554100c910003214601d0785030329104111852800208a00c1c9035910662040000c1508198240d040d5a515100040b43d5030804043e00354000c1131610b01300042202c07450100d605801481440300401c044000c0447c80a64444c008c0c0026190303100b80d800400c010f41e828022200203200062030071100303d54601c0202d45a80040781c2080c4103107a59128400300c07440f8002243d1040d00070414210840e80e4640e16400d05074540204c020030596507002820241d10100314a91805008002d015441d260a03c10940b4013a1013a80b4001007041004521000039000001d40d1030455110078081040ea5403000403a00401e981b45080480803a030b41c50000718141c40380d100200c034001c2c80c0e009002954035048107a9139 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 521046915 1250 521045665 521045669
    0x80a0e0a0f0b0d05010806130f17040303020c0108010b0c032a0102041205060c090d081b010203010807090e0f0606092a0307021c0905060c0f010204081e061b1b010f05070e010504 78
    0x4440583c0388c01400056041c00c1c604100da20070765480b203d8a4a00c03140302c071650420f42040300507078010500382d1465038020a1190060211104d008d10306284640255124016410003030310029803240510030740c3c5031040d0440742c480f0b0040d00031516070b40d8a0101c2800440100c20170340341802404040751411901004030341d00c5100150001d00040c95a82d503036603017a4801000543c17807240b504c82c1c1c044645e03028001140240b41000042401c42c1c1008003943c1150700c0101119040d0b0b101810f200000348010a40c507602c030600712050700243d81ca80c40040e240c1c40001165030340718408041c1d042d0030340902a001d140105110380c03c6034420304804987c2e103884130141d5030200100d403015404000d00e140034401403021042c1c01c0141c62084094080903801d90b005074010740129003040d402001a41c4040c070608450039061001456a42810301d4880203940d4003003144d020703040c1c0c002400210140303216195080300303090070000c00c20302034100344070b00040406030344810000f00e880440d00c15a41c072a8040e501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 521048165 1250 521046915 521046931
    0xa1206080304050d0201121a0109080304380a052502031f0608061e09030a0914040e2a01020a03020319031d06040b1003080a0e0a0f0b0d05010806 64
    0x318050425040062810084c00124100a0004000b101103600c41c020303041f000c00740c00b001026540c908400500f8031501500074a202c0d0b4070900c01002034100606d10090011241481d0480c56104d03110820000d06084000c10040800010301001e21680030300240705612031b07290810403040c8a10391100e0500103601c00a03615600000aa00c0c5036101c10310004c0100b209040c0015605551341070640c02c1c100110782510fa601801c1c001c002c1b200c005e81c41d4076580601010051483d04a45080c05000840140508418849040c403e04960b8582c1d40c0035001003225681207030280904075142e0340c03ea420a011a00341c1c3c0034201c0003a400c41d400000c040c06516810f4002d1400c0c08103400d1900e90320080c1d84000d80c201902d4201640318041a41c0151254040307410160080b4a4641004411024040e004103540310080d001000401c0008090b14030190091804c6440c031200c5000003210501160002080020380000015401482c48000d001e2012450804e00143ea42d403040640c42c0c10f01211406 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 521049415 1250 521048165 521048167
    0x6052508090618060a11040f060e03121213020312030a05041203021c150b0c0a0c0807061b0501060f080102090f0f0f060d09050616081501021e010f0f020a12060803 72
    0x41c9410240ea0420280c44a1b00014181000d03620a0640d000d0f6407280c3c00240400c040c05142e004600b0244403121000e04600256450302e9041281c20000c04030041040c628030303a80e0007034802191303002d204000344441501c0318070345c0700c0c20800512001800f080d101210220820701031008014000c1c002e403601e030f00344454042e00c40d200c500c1241014041780e004500840300000700c08503c4480c014054032102a08200800b15107015151214515400750414031191340f1810341084200d90050441100c41702c010542c9441d200c0d6454920f0150500f1381100d9420703407110801103003605056000d0040b40d282201d036201c8030580c41c024003840c1c007540d0107283d400900d41140c4203c00d05007200200034a190184000403258010345031541051020781d941d907500304005640c00b42c01a4131164440d044041c600c1444200114400040d45d60741204125019403003160444144000c400e5210001c460381e40c00c010b1005a154020480003940020142c402040710044540d0441e07c0c0341c49403e0035200310070011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 521050665 1250 521049415 521049421
    0xc242a011a060706110a200c0d030521011413051015050408060f04061406010e100215010b040f0f1224090b070e0d020a030605250809061806 62
    0x2026642e40b11600c04d4601c1c98840c071a07080740d452204000c0c00e10192958801080e9024a10101440604200428041e5000e040131009503a02d480c807031404980d050820503921003110150780000041c4141c0b1001020100c0c0c000510740320094601907060a04a84d0550071010619400003180d0094a4104190b110b5101c141b24000041c0d100c01607006040c01c1c10381c10942d0b5000f9042c9010740883d502c8580981d80000d0000700241c0d8041c02c001218000350a000c01e151800000b0a10448195094851160340a80850440c0203110040160400880889080d80c49004646040e0710a1040c0e00c8400c1a01c0000034541300140700c1c1c00c0540314204106209000e03da1640145030920f42e50140c880b84501c88034403250001ca206201c0b049100340f50440452030014000f07480f103c201c3c004580948055055100184c0e50340d6480e005413030348000001159281c80301079007403c0e54001c41c100061904001c1c280701098100b07107501d04c241160b004480490380c6203010f040701242c10001e441042e03031029001c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 521051915 1250 521050665 521050669
    0x807090f0e07090321020c040203040834111306060918020f071a0604020a0e09041103153103120b1003090302010513050c242a011a 58
    0x75142e000905480c1448a6548070b07229681d90340481115000074040001070050007640500c42c4504204c1708079402c608515041c4c0720710055100c0c00c802211081340101d0201c00396070001098010704001041401d03105011481c03d50828458180c81c0307403007448074a0856080345090700504054030302c550381d00a40e5a14015030f01403a0302c040c18032040b0b159001c4c0016098140c40d18058506c150160f0b031401e2100150506000b28a08040d106902480c0104807101c1d040d50001d0103c5820392064500700c4175540c1d241070026040e0a109491581402552901941c084900074440d0160112541c80c1d20502d40b203000348590300d8500d00c050031050065407552800f1901801007800030301ea40c0d40c80410901140c1d40020000c1d4000118a0007007950398001c039040c5642445415401100c1c0f0084840c400c2c0d50f034880d0b41c4d0710003038060f48911490f040c0308125021061040041c1204603440c00031074070340c43e102e0102112150101c0e04442c1c80308009198000e41a414069044020440d4010300003920b81041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 521053165 1250 521051915 521051939
    0x6072109061b0e0405130c05122803030f060f0b09060c060109020408060f040201020607270303020105090d052805041805010e070810090515030303040c0906061706130603120f0807090f 81
    0x12a011507402260ad003590f0030b20800c59004514843c101d0304d00b40006080c034001d0200d5040107803010495241c0101840154035044107182a502001405074480d05d0103400504a403003500030901c1c90b8000d050000928000d40e3300a007090b5452942624600e960750301c20082c548100325806401a48148041600c4074010442c0d1407101e135445513860064616174260490081c503a80c0105c0c0141e40d15000c01025010070b005040e0b04c190300340b0700306203044031020b00d150b4049901c082c48000c04402103e441d441c41e0040049030020444080102c00c01c045c403100fc000203100921903900c0322040540040e000610a1002501c00c0004140c15030500d4106007210f0002c190082ca15406001040d258136007580d0100013440c0300d14402c2c2c1088400234248040301c02542d1280d4003100c18015203a800094295003240c2c4507a1025054441125070b00e107141e902c501409966002404801100181e910300550102d0a00d11003000740e140ea1010303442c0c2060494005955114560b001031030281d082c04400d032404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 521054415 1250 521053165 521053189
    0x6080f030403110a0503010c1101150e01180615030f0605010f050304060902032a0a15020a0605191409010c0801120b0402060d0203130506072109061b0e0405130c05 72
    0x16150744c100503241c201107030071107204103d040c0106020b9070302c0c00b6031401c0c01d01800c4014030490f007540c0304041c038200c002c030030508040c0244540d2100319605441c26a20703640c0722078020050090102000c3c1110351b00a0000c142c1c0c0030085280f641072040201c1c46500504162540a0712544d8540c659922915401c00a180c2c041d0201c1e810302070180310106140c00d84290707648414200c2c00c0c480e40300100320201314030781c61030f5030250601c03240303820040c0c100c150040343c030954150b0040780205480e0750f440d080035440311404484c01003403842c003281c001c130b021080902c0c244103803800c4008100070500d001060b11140b109100b40c41a01c0740d0030420600013101c040005400c00e01c060195410000090303034034400e9070011180d03410442c9034900e10200b4000b04000150b0041227070300303285c041c080710201c409160302c0986d440f64411a480300500020828954004111060082d080a44002d83c0c064010480c0d170b0661526441141800086410301c44400d60174482982e010881500052400062110240b02c0c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 521055665 1250 521054415 521054419
    0x30c0d0807110928061401230a05091807022d070b0a030e0111040b2a0f070e06030304210b0106081005030f06060f010c1a010302090c1201170f01060e0a06080f03040311 74
    0x3010f0400c2c440602342000d00481d410584035251111185020700100c03003900038803501c400c030081d018400040c3d000708241c4a009440031884000b03003d0030003000c41d84030a4042040c1184184240002d41c164540007030516004107076028403240880c0b850306400d884042d0519054068100700420484004070011304242034580300104081e1100101054403810301488030505411071490141c403103c0a1000a01030303d00c4e41d003d1055405e00c81c00bc20ba40e401903024103841040b211b11003516001a40d0840f000300785c0d109108180ba580c440c24000c1c200ca41c2a550b2840b11128140c010805103030108002c2c1070082020700500c01e5689a004002c1841124507809040c81119600c0d800820400d466240c0340001c48082d040b029459481403040c4910001c241805402c000d000c5081c1d4050b4079046181107c10000e040440c0030b080d80800c2d4200b4041804c0101e6643c60403a000510803201031131188940703808881041020790700c0a40903190428030320368070a00d0700200f10a00000f180d1005800c2c180d000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 521056915 1250 521055665 521055707
    0x20907111006080a0b09060106050301090209150c0a05010b0303071518050706090e0a0501081902040b061201031403040e010603051905011d06030c0d0807110928061401 74
    0x8070311190402c88500390804006030f04a00c8000d01844840440d07290400d881000412256240100c0142075010600841c0062a00091a0a500d554625800d4140a00075802ca99562030352042c40e503440108407130444041d400e020409105250100a03540010f40101c00780002e07481000c0700034000d1610b060103a0346582d00503030840c04620100700150252685407503002c000760400d423040b1010070001b0304241d100c6007050b0061045a20104040001120600c81a80d04182900c0060043d048103104103030800400b2a00c0c190300c2c0708001c1d9a40c104c81c080d01c800500c19030880b06003500c034400d42c081c0c6001480f500c0010003142d4443d902c00d40e4000c800c181a0b04030060b9101407001621400e07030102031120505410420592608104180c210f007088005203844054100807610401e2a560060070008001c01c08205100c41c0a0349a40c444000134001d003024a001030b0750a1924013503a400078814001e0441901e020000c1d40315903020303154140e140f00da811a004004603400c0c51450b15000140d10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 521058165 1250 521056915 521056933
    0x20307020d1101092102120306130b030a080309010603030908031204020d0f02061803060601090e070318080705060912090a15110709020301080d05180108060a080a0b0f01060c02090711 81
    0x11680b100610700c0d002c038900c4807410f4071110083c980080e00250588100d020018000e5074ae80e11500d20303945a11007080810a43e010100090511404d00341c060800c0c3e20000802400745070662000c420f4038802d44602c40210f85030a03500780e580c090380c244000440020b1008c9005840e01e0046044a030340b251542010002c03456010034506d802c0b10001c117941244803564070100d85801c2c40802d40c0f00b030080c03810390141840c1a406a524180107000d030303800d040da1828085e103001c0c11901840b5510741c111550540c2d5101a14006682e03020484070411f003809502e464810024900c1d0444406600061608515a04200c00d080021218419040a00015007581045c0c014244510030040c10464001600c1e985030bd0900c13030600840b0a038410803c0b030200301c0c0048800100c3d00c1403900c442e081c64440440d2369040085100b1800c25000300c112031140070b41d00e004205d2040d500c1403107883c0701481c1c2e4607103036030b9030006440140c0090b60003540b00780003d0008045500c038007001c09540300e1800803581200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 521059415 1250 521058165 521058173
    0xf0216080a0f020a02132a080103021f090e130c03080d110c060c0306130e01050f013002150d0f140906130302010b100503040b15010c0303020a090e0f0a0c03020307020d110109 77
    0x910b1f14003d008a58980010402e62030010130900c9600040c00c0c059030000f0b03942d540103014040c103020302c1c1c0b940c64030080800c400b070400e24420070000781c0c44600c03d1140d98490928034200d4000c150300710445818803c561811704203200c180d5000d945030070020086d81c1c94000e640c03450740e040140305c0e5030400d04282c8143c03c80f9009016411183d42c07000000101d90802c0b1100d2030b503403e0141c1014a08042030342c1c41300c000104134140d9214911140420085200c0340c2e100295102121050348c00e051030703000c80c12503d00d0700580d1010340044280401004101d0100e10050a9000220303400c1245821103c0051844141c0c1c3c04000c2d10350f0301c640300000360b5000f5003001512168206015070000346022040204108200000d1a0403c1c0300309102d00326614550002070200440e48401420580c0118608410038002ca5122010302001402040d051500200440c18644116080b45c2024207014106080302c0c024401c03207001c0c2c4140c0d40a00390000443c81c080e12115030b8003035100c41039940d40b000e43c0041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 521060665 1250 521059415 521059481
    0x19021c0615090212010e060f0936011b050301060302030415060b0403020f03010905070b0a02031306110c041e0b06120412020607020d050703030f0216080a0f020a0213 73
    0x10b030090b41401078072104408405558554160401c214140026003032110640d10743c04031a9032000204c40100d429900d4000341884c200d40b414800d80c1e4070b40c0748503c508406004a14900b07102c090b00008001514010380744502d44000552540c000c1241000140030562094000b144d1050080c02c40000c081c401c41c040204640c071a60121500342d002180600461400520411182c10202c00078825854103443e04c6071a0741040c41080c1c070410b00002e41040c1c0c14028800d48041c041d043c1c05142c520303036032488060b04c008840d080f01c0d01c6034040d00d0042c8403103140500c104030400f5800d20b00200040d4003108070303a0040804140b25980300e0010300c03810000c02da000c4c004038030851098150070849c84004101900d000300261101044d500881c240218040e84907042c3d416454161401017116403500c0e006000030312900150701017110102d40305800b44024174000b84151460769803100c5141c506410100d0304d0340c4101c14025440034040808030008490348d0400c1c1518951928a03001d040c080c02007000034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 521061915 1250 521060665 521060669
    0xc0c0d0501050601090b040e070e0112050a0603031407120806010318150605030318060702040b030a1428060b010e060403110306010501080702250b0703090819021c0615 74
    0x2407a0344071010400c0550703016160038010300200543c20f09190400a8a01d10303074030010040020480d0301c40703120b0f446a00c035440d11000b005c2001010007081c105840e4180188c841c41c0415070110741c4540385003189070703200c40031210016041040340303006010f00314049a83d000003a200c241010b0b10b409480c2d2100c000b08a0802c005481840741001600200c0e14030030aa4080f0f0780120705c680c1050003181c0d0050b002504030506401c0c110b8840741d45480b00e00c002801050050390766601489040710b51403c0100104000404a03d8402110011000020014902084000d00100e131825249940340010065001400c040505044c000328003480176020403e940c00c683e10603104160000001c140506082c0f00142c0502001e1030042c409250501000e990381d906803900d2030003100b032091f13520944e23440c440c0c2d1807010300020f11049a43e28410f080041040403180a40e22483c040d81102943c2803000181541d04075038058149004401840b98a620002c800b090684080c2d89944440086003108040040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 521063165 1250 521061915 521061923
    0xc0c150c1e031506020f06010603090303020d02040b070605362e110703080403050702031204060203070606081b090a0f0204180b01020703080910030212100e070e010c06020c0c0d 78
    0x3e03400d0840300c000015881070b58030030703000c0d5003099518140c0c0580204a49040d500141000f0130308100c640760440080c0300b0b00c5810b0317001034400300700820211070750002020028080e0707105026545030700040c04124401d40030f5280c080c100c440e0001107010b0003035060412a8924805440a81005180d2400c9c01c0b519a0b9484460b00440020300c510300c8030358410403019212507100036041001c1030354060b00100001e44082c09001d00490030004555081100c01c10040c03500780c841c3c0e1070703c0d0b55030000b95503500041c008440840c2882d07408280c0c000d000407071030500310b0803015444003403241c0014070078410303400340c106038102c0d80740c04800246213264002000100381e50711000d22001d041709a00c40440c0c98921213281190480c030010004030f640da0341074624075103045907001096207000109400030310595811240099810f0100001c0d286110f1585086811007100d9142c1383d0703544a000c6605002c28810b0a000c1122201c6090100d44c503075018041703440d0488225405c400788240001e15004140302c08413 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 521064415 1250 521063165 521063171
    0x281106150f061912051504050a0209040f02030114030a05070605161a0609010b090906060d020702041805280609241b05070812090a020a180c0c150c1e03 67
    0x141c100384d403015500708004000b550400c218140403001c04600c04060041612032511900404c44c000c0c820381c102c5d821040f00910400a03200840028800717504240f05600c080141100416241c0c103003c500c25441551000140c86014103140b1300f501d60350420300704c42810141074841c01c000912200d10751824581c0b002c2d004042072130142c081000e0214160007102040c81c09101301401902e4010640c1d800c03c500307c4e0740720b490700c200022100c001d00030188017035400390410340e4080d07000001d82c500c06441409001565003060140c01140c01050113110188200011466900c1c0440d24a600240e2460322410074409441030002401c07000001810b221050107584280403250026111006c9406090504005040040e241c481034014050030040306a4004200005041e0b64014404459840d60046c140e1082c261103040080580a0340e03014210028940420311103424042c030283c480456001c61303501d41400e1003000001c05490568015410310035000c24254001111813544401881c1c182c1d400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 521065665 1250 521064415 521064457
    0x9021b0d080402090705040302010219171210050f0303071407050604150905041a1908011b02010b030111190c080a2610060f14281106150f06 62
    0x8030444101034072138406d0141c20001000140d801003541c07000001e030012851110f40c423a040080c0705a00c0c510040340840ca0010702809160090f6444901800000c614550295260001e2144912540d030341c03a0380c5a44107001c1d24000075800d10081d4001c00341002a20310070760740d80012aa6a8000e600403944010030200f0008001c6d078480e070b50b18001c0c04111018850000c0e240c0a4001600c17080c120349000721030030008800c441c1541e091500c01060410004c000000c40c0e40c02508000000112600c019400d2000e48505031505010f59641400b0b2005142c2c9440100c401e89016502c01c1101e003000d211141c0c04c288042940300380913101d01d00c0340da16a16113500b101e1700045001c1d004461180c60343ca10400510400c004030002e4075043d40c240e418584905c40c41d03c94240d0303035050340c01c0420180150011748070012059410111500780415205070b6011030680105854200f50b159490805600c0700001a4a094440e005000818000741145c2022958600425000c0c0e00000c9040000d98201e129 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 521066915 1250 521065665 521065669
    0x9060902040e0604090b0712090f030206071214060d02040920032a06031f0303121107030c0b060f18040507060206090a020d142e0209060409021b0d080402 68
    0x41e41d2201c804ca4040100f882d1642c0d85241455010304900c04209401c41740d0041600c541e48110182e54110010016160152400a40c0e52404841680004655840b0b0485d03160040c003900c203005880039542d154a6030350105025a1078070b100750a070ba1007038039a002c0c100810b0701c450010507854100701580c100022400c0c1410b00e40507480d00c4c0d81c02d943c00f8002d40346404a88041d0311031345d004000c8626030368a854910034030300640040b10300303031922881240001040540000300c90032490418507007400303182e1540f462040c00e4002c41101602269421500e10000303142c03203041a5001000a00380c0711070084000100e001e1101d044c1010040003000300c140024440104400401448544018840ba00e8081185a15038100010086c0902241070b41035041000c0c1c3c103030803910030f1907201c00c4a40300e10104900d5118011010ba014041d42e80e00d80c41c4122840441c002c130340c1854005000d42c0e181c20302e0160944020f500400b50303250002103581b01010158002d0020f0440d0301c03510755a0040e10704003401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 521068165 1250 521066915 521066939
    0xb03072a03020c0102030a020606040e0109120507020406060c260c0d0c1703011a07060b040c051206090c1804111201060306090501030b01050d050a1506061101020f041a040906090204 80
    0x4440f9042d94028060000c0b0160b0028020358000b00a6401080584d1401107050241112003c01003e004c28036141c0c212080c1e00070040c0c940f00f0b000b103400b4441c2d181c1d1041c05850303404191b44c001c2c2040c00300042210081e14610850387c03400444030285c52800d00d03601100c2d0704003600f0801c81f00004450440d01c00c1840040d0182c000c1d515004164940782d9494120040c520700085060300c698600c01050394400c0c01200c3c0d1018003a03140242c014441405001c000034816441103e02141c541600e002203007180c248800c0b054410301c001e0004900c1c00700c240d100140b40d0005d00007050340c456115403a04503000041d0000d130142c41315211107013403254100840502030714a41e421140c070991070f000040002c25980600941140c80940300540900860f0420600340490600702030818034280103045810011540441d0031200c80e6990700c4050510001c8803802e07441384403403809a104080c4424841c40c0c0450114032400004102413a00c0e0541c0d480d2088280d40903a8004101c590307012400700709045440c0c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 521069415 1250 521068165 521068183
    0xc0417010209010206190615050909090607270305030d090b01091104170c0a080f070b070b0615160804050405180a17040e090330010b03072a0302 64
    0x60001e508048440d00000c1d034840e001001030000c804d480480440103221580043c000e031030a000030242c80190608058941d50105031410700aa0310791000074121440800c0c034a0150f005a40d8968240c11108108020b04647c0c1a00d41680404a0000000a03104000510030802824400310b0744440c14203040c0c082100c142d2245114906202911034010916030448081d600c01c40c0301741d1800e8102c49081031034440c00510103600044841c00101e007620001494a9030261224211148151a0b84c0b021019000352003009020114030b00c0415024500080c1c265480700c4c100780e0144c00e20f54146440768140e00c0e5408252010f00e8001420f114070b06181c0a1583d120902280601c446a05196456030b1900308440103009000b115440707a40148101c0112802850500264401e504000c4d0115440b03030b000514103d807405084d2031240c0407003d20700c4523041940c944c1d59003150703a03071800040844a500c0100800d041110308008080c14022048021145003901ea54101e920703000341c50b010780741071008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 521070665 1250 521069415 521069459
    0x4050103050616020706080106050d020f03040507030b060a03021503070215070305011509120b0702010e03040b0c0c220e150f1009020f0412020f030102270402030103080304021c0b0c04 81
    0xb010051011700d4200c003000c0d0445005e4a403003a540c60a000c440802030140e4000b41c0114dc074000107020038040d0005003d41924050918244151120000c210a017000e51100035008034907040456040a1940081c50748580b150058441d5400048a5032180701800c03038400300130a0383c940060181c030114050358008403001d810b02540b0350782840e0307141418401801d4000e02d035040d100c0024a80d14400c0d00003100f0968140200c94559803a0010f041140d0000c0e882d40005100d4003185100c640b404000034030f40e18115059112034502e070002340300050120340e002d92682e1310441c014120810081840079104d5101000c4220850034000072800681007203502014500f4010f00c19010208034400403541110320780910f80c3c00c400c0f102e01c08110000c0002410741d40c5548003059142c102c062030703541c19100800044001e0242c0c012202044101d020a02002d00820000d000090040c14086206450ba08000c24a1409503210380e403040385642040f20000c0004401043c03c02803000792000400e103400c0c2c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 521071915 1250 521070665 521070673
    0x80703031205090601061205060103090b0106030e0609060705040e131e03020606010201110a0309021503010303170c0403030f03180b010902041a03012114070b090a0602060405100b0f0405010305061602 88
    0x160281c000c2c140004541030300e50307da640b0404038034268042c0e40100402540b01c8000306031983d42d50703006001000c0c3c0b4400d40b00e15002d0100003d080106c04a030040c442c1c460f9840340d5040900305111003101800040812070b03500c284001130004201d1404240f241405030344c0d14503221a1080c03400a0600f0005020345040d03a0510010450f8544804c0580712194a14034001840c1c203d540000b03984803544841100540c000080007200385580080f242407400b13070107014060b10b034541815002c8030f80324620000d000140c0116410400c240f1035040790240c802d42c0c011050844d41c3c662110840325030b00303034003240005038005001c00c41d0750442d0300000c003010b8182c2a9541550700d410f21181c0c00d5041c801d4035003082814000301104004600e000301141c11408001c44000326220b180341100c503440300d41c100384900715580001a4843c40000e82074032869103c000381800c40708001003180034000c0303140c2495200107841c89480f810f0700c49100d07150081d40283c1c000c000d641000d058404a45072065411411500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 521073165 1250 521071915 521071919
    0x8011a010905091003081c1503051615081305031902010515030a0f020111060f060f060a020c040c030f0213090e0309101b0f080c0f0c1509040204080703031205090601 73
    0x6144c21040b00300c0b500301c4c0502d6591840d070010794508000082c90800fa2902e81a03181800a405144030300c16248507508072410000c1005101062968604c554540411290000441144900141e41d00721800504000b030b42c4182da0340315421608103104401200d807500040031802507090084d103400201050500075844072680129440e00c2050304064001c9190b0541101164812040101c020f00703902d003510900d00f003000e44140c0c0443d00740d40940c8234080c800182002403815004071055282c8a1f002840c94a031444d0a0101030b00603d06000d0034903a58103103143c0543c010b40010600c0d050000e400143c002d042c581030300100c8142c00c0c00074440707034014031500b41c06844c0c00380c041503d9211818540180d8892000e0a40340d09801c410090691001c0003d6508100168001d4002c2100e4581600e0701b01003009440ba0b60381c041051503950007044a0580d100c0340401c100209044040907101601c0c2a4586450038a4412503130310817800608500e0008180d0003051040325000f4080c4400b0780b220354 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 521074415 1250 521073165 521073181
    0x3040506010501032c0316120f080f010e04051609020406140c0c150d0f06060e09061012060812041e0302030d1101020d050c0901021009020d080a0908011a01090509 72
    0x40c10549480d0340c170700302e404900c0103139600800540d032034890020484a018016403030074072a07403c20240c0c01c0c0040790301119180310050146940c68864245150300d902507038a0701c03070b02908040003c0c006844a000300314074421000304000d2950040c00313003a54096901c03803509000400d0002501a021601002408000d1007584046005502c00000710350b0301960031290790364840c00744150514450f040d842d1040790310072040c05070040c1049601070744403080d11404c0b000500c00510f200316050ba512507542c0c5143c451042c094001c40e441c0055030100007803243c0d12041701d945080d0115000803080c03d804101045400e0401c5a0114112000807403c9815455580425a500329030000340c0107018072a640312059400075815a000c2800404051156040c0242c0302042036010021079401801503c000c1c480d8000079006042c040c80d07018108110b940034903101c5d40c2007600318031300784001c100c81014001020700d0240074120f10040100d00500940c41c1030700014000c0c0701035070300c140e01641215003000520 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 521075665 1250 521074415 521074451
    0x6070f0b0c0c030721183005070f06050f03060603070c0812040204050105040e15070e03060708010f0e0112121b0c080610030b1303021606050304050601050103 70
    0x15030020240c1100e444002035a116030060030340c5018a444041503c0c8207000c0c0d8188080317641d00c0307448205003200c800b40c2c008940c031120a01107102c0441700804104021643d000e01c2d0480d0b400170100c403070b086101070408600300040c000380686d001c3e0722180042c84072100800c07204009160909040b8035240c082c028020060100600007403081d4408000560014022044c3c0d10606603c01c1d203041c0e603001002c43c000340c000c00c00c2d00c5c140c0c0298940070000c00e02c1c0c20035200380f40107102040000e0084a9490000d802c144400a01c21810401102404855a20200203071809240c840c2c0340c1300c8441d0b0410700d4140e0421782c0d651004200c000e807600100310b5801030170701710b4480640050b0000780209440800351401030258000600885048103504280201010204240d0701da9100b521004d8440100000300002c01e8040580b995818102280d50400d2140180d80c8481c800d0064401480141e401c24681c5035141d031003a00420350002c1000200314007031100501519003400c00b00844600120304940c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 521076915 1250 521075665 521075693
    0xf090308071812080c0708190f0c090606080115050306090708072307050f0a11011b05120d0b0a03051023010b0703020613030813060912030501060e0607 67
    0x107000310119141c92401800d016640038003890f008a40c030702181407400c805542d000d8208001c1a0144000100d4210008186503001c1440d2107071210f1224580d4542c0700e0792280680f41128590100c1c500000d400703059006900040106848140c4a58903250700c83d02a8490f070610708080150800030040155240c40c41c59403c180d05181c100c441e69221042503400506842c0c500d9410709420114041090f144402046d12078865400c2da00f00030300303039091035950b1047c81302c2c0244940d6072404c62445952140b191000003c140000141e001c0c0810740b50a82080d10385498004c00120001d4100030041050140640e484802e0f20026886842d686500b500c6003004040c2d0580c09484801390380c00501c000d0b40b01c846204000540844659484840c0211a408102d085025000302000941b00000348600c4110540e011388038070b1a00d0f0b441c03200d524141d0350f100d0f07022501c0e02e950b48000d102103800880c141c900c680b0903442c00105541802c001808440000c107482c0d210704001c0152000103441c000c0310780c2c6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 521078165 1250 521076915 521076917
    0x40c03080702060c0a0c170714010f0215070306090e0303100306180b0c04050108070908030304110406030b040b1012030c020d0501091b0e1003051c02030f040b030108010f09030807 79
    0x1d11400c0502c00555107100c0c000e8420018071481c8514030a01c5100318002c0d00700d8115103400035100710b0b100080e50701d40156101d1030791029000c1518031403550041c11441c0380043e42e8416035120780d03941a040d9110140903941e10b00040d6840c20240701e034440d43e1141c00c20a000c1000154114503010340ca04d140000c0d207000043c00c45444c2c2d0701e51003414000050b40e0030391561045110000740b074640d0200f545500107101c1c00d400103a480020480c02c45c040d01c0400251803402000e14910307915910b842026810303850415800581e00c120000110700d280341c1d402c2c002c0b48260300b411841e090410141100c8001900082404000503c1d15000250080d45480c002c941c1910b02840001d20390501c1c83c0103001c0311307401a058060512032000c081582e03d000303c081d0f170b54103e2038007800e40320340030300321180f03146804000c015511805a01080054a140c123800c1140d02d0310403a49801c50b01c9191841d5600160b00141090302c0100062008060a0080002074000c249040005421702e48009202c1203000c1c0a001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 521079415 1250 521078165 521078167
    0x9060b030411040b040207050c13060509041b0f090b10020f0d1116080f0d0c02012106210203100207030507120509180f13050d050906090406060e1305040c0308 70
    0x18220303032503c1c0c004d03100d41c01004104640300c54003410101d840d042444212485034501c680d0350740c00b1004a1003604140c440c0605641b0555456988605107041c0030a9a0b240018846100140303017040f0414480c040c102400d004215203c0c00710500130300e002542344540075500102144916800001080c48020625160004101250440309410b10100c000d041d03c2c811a51a0b0104030044005403040844c46c0c034100f120392a24049004440c10501e000c002030006000801011032036407203c0c100c0225086901e80016096079a038a0b01380d000c424600c0d0082005013100381c44042d03280a0020341c0c031000380010290710b400301e5694014664440e410000389101010000303000d24a21410694810382d801030b0a04840c9100b4110024104d10102c0d109044005503000040c019443e0420200c403917030b4000c00509070701c121603005490359040500e255410900902480b81d0654842c0140c0c80244141e4968808402000d0203008111004454480846040c00144400603406c5c0031000200d070342048002d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 521080665 1250 521079415 521079443
    0xb03060607020112050a060e13031b1b06020c152d04030b0112140a1502030a181a16051603050403140c010f0c050303060415180f0609060b0304 63
    0x182c428044561507003031464071706800c0100d80e04d0b0907032040342a1a9800b041074880c0d6100f051004018400800c0103000502d0120b40815124880303410b2070100707101c2c1807941c5023880c80c8010381200a040d0782c0480010380c040c1660b90003900700750600d1614850745241c1545042e940980b070304039413440c2115008084809080706400c910000041c0e40240d40d2001450400796074403220068038442c540c509654001440300d440821100008601c0c22140e400503407420080c0c600c55442009400080c0b04031140c03500d0320340d05502c107440100d1400c8840d00c10007400c2c6484c507488410140303901000304510101d07a4524030b0a0080c0340c20000343d600d0f04203104100072030046145002c0f21035000c0d07a8801090b03400d030702240e058106008502c0094496080c0e031004034065000c0801c0703c00310464400500f150300200003060f8281170230341221195095810303080e07201e95030310002001030005105490300740b0ba139603003c070301c22143c0c1c613000f050020013446505005c480d0500107109110f10010b800109031142c0c4102c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 521081915 1250 521080665 521080667
    0xa0815040215030c07030909050114090414010906090c1707032d030f03050c0405060f0904110712020f03070b01060e01021204091406121c17070c0506060a0b030606070201 75
    0x71201c401d601c1202a00e90030801640d013003941007802c2c1100400d101c1000481c2d221f0491007894102e4000315000000950b2690500c10140c10192050320138108a07003c80350090000d0040f07518241c0301d0040020006040c0c1400000c0740b55507040400c400940401b001020b10000502c502526040000c01701010005103205440107070292076546035101001d0f0a13018107801c01c58060130400303641c80038005076903940e03200d204c1403081d4080d0550004081c0040c0c03030040348000181401d0a406800003800f0300181d4042c0c400c5800c140c004076400c82c0c0d0080740e2105654148520805900c0100042d402c0074403036903c95810000501441041002c000c1d1801201c0c1c1c4200810403000340b0036500a070703a4503102c0031102c01502c80c00051508503460300c004941181047d0744041000106035014040d0751003080c0e4410512800da982c0031040190200424000e800b10481d114042c095a03101c00c584041e442c81c1003410400020180f511031407a001c41008071100310317030840381d0140c4112034031507443c0d40c00c0c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 521083165 1250 521081915 521081929
    0xb0409140606030c0d0608120a08180706030906020418020c10050f07050304050a0b07110c061306050903031308070906050d0c090e030d140105090603070308093114060a08150402 78
    0x405210300b841041404202c2d010008010410010195140ae4440d0740d01140d010007140c1c82c035040e42c1c4c0d41d402020100f000a01c01d42c000400e091103040050f00e0599119000d41da64080082c0701000306a000445a01114040160442440c2920400d010a1810b030301d8402d0f05500051515090200c00000a01000000d01c00d045409034442100c8040d41171000004115003151421500c20344035a21522100341b07006030654401c82d030148030140c1c115060400880c1c10f80c00c9101540d400d03100a010f00b250002140c0808000b0301000001024070a2034080186d0a8440700d42c0124050b24030240150007050010a58000790b5103c0c0d03001082d4181c0580c4803034558030411444880142c41c0948081010804400300e5048603070454445178551690b1082545800403484000c103504020052410681444d151000c81c08220040300003084c1103486100c1d0180f00341c000b151841658810210701001c00440f08070b608018150790352403416040c132410594038211000d810036030b6400b0000040865441c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 521084415 1250 521083165 521083169
    0x20607081c140709030c0504020f04080328030b180601020f0d020102031f0f030605072c01180b0f0304060213030c03120201090b060d050f06010b0409140606030c0d06 73
    0x140525540003288420300700030004680120b071220894400700300441d02c030b07400200980b5005002d044a031490701040000a6200d826040e944030300602c40000d441401303201412184124080c00c92980410002070725904a00079040b000b0300d858064000c0c0203454807032245009011500d0b44d41081d45a082c010f0303151180042214800c1e04c91048030540140e41034018601850822000540055005a62190340c3c180ca0040c070349e2640080e44100081101c40e0041d903080303007041c02d000e404000a1104080701c1e84800d070b9542000103515450103000e50707200c065200b107420281880b5110b40c1c01c01404407001e01c103901d03280c841c11201101003001d00600b40e04507024184040c101648481d641e00c0c150303900c6a0107100603554411035101e0420504e0040c05441e00030b550280071078010381d4070171080080307551000c1c0d82030315548101d44042d07082000c104200d60180101c4001292914a4000000190b07400100340b000c0406c14841032186503150a0300b6290401da03802401a281d50034030500400800541e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 521085665 1250 521084415 521084437
    0x60c0f0201270914090a0305070f0c03030c050c190b0c1014010e0c0304051005070c02100e040b1909021c0203040b040209090d0e0613080f0d020d021902060708 70
    0xc40001d200b6025110154021241e1a500c18000084c10800b4004018001c603000421a00320350310400000e0300c80c23001000c455204100c0108504e259444281541080340c000f01e000c120441c5120080c41010000c03004c0d401c40884001107482101050008016080c1c80741e140ca440380070170758200c4020140003d94050900c00001c100581c130a00d030000f0400e201b07107e43c00307118041d00081014040e250003264401c0780c200c002001071000100703003100108002807124041000400b07a50005a84a43d5800342005103955032040e40c0880d0302c00c0000700c40840b01c109120b11200c1c2c000200d05140d020f0b8940855000140041e1604001c0c00c0c5200750181649a10840f2840007040004004003580c080303000364025540402f8569030449055600d80d017207415500424006102c82c03020385845001824100d0050020107050350b40c6a0b00c0c1d03880c04c80003821000c5590020450100015070400c10111070b04807074401417203004c801070344052017103514140280c022400060140244200c00c2d040b51501510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 521086915 1250 521085665 521085707
    0x1110a050a080d0f0e15060a0b090d06021213030207060507200f0d080705010f0509100515030a061e060b0a050306011b0f0605090c01090603180203060709090f0501060c0f0201 77
    0x1036002c2560703d40030f0300b5801d00304e02c00c4010007058088c00e201b12550262881009481d16089121041011b80c14240c0021244941c0030800c200c0c1c3c074108600942d0180011000032842081e140c54043c0c00c003a0a0b070480010040188115400b1503540d882c01469082441481c11020910b040407454022405941c20742000051480340100071044009210f414041c0c0c0c020008403241d0000c2105940055810b040d00f40d010111400f0b860500740c1c040c58024403402c0580402003002e0300803030b05004401c2c0d819201213543d80307188450a4101686440c0707100d0795550403c403a50404540ca002030003900880070820001100041a9074003a4401482000700b00d11041d00800c45441c1c010080c11a0410440e042170409000c03413012540064018842d80303050711122019810074008400800580c0c44120005414440701000340c0c40600070103001d15050b079107850311103062084500c145e80385e40780641c019030b207482c00400c911644030002d10082e60f800a40601c0c24105800101c40384406a07140c441c0d0700e17107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 521088165 1250 521086915 521086931
    0x5091219050607021b13230903070b0609040c0608100506040906051c020603071d0603090307030215091c20010506040b0102070e180f06070206040201110a050a080d0f 73
    0x1030000d042d038402c10300c03542254401e8612118100c020b42440040366040a2906d03248900e0741c1e141d42200700d41d0204900b04958026801011070405d1400740c4040c140b0b03400c001400418090b000d80d0060388050181c070801658141540d400000102c107100700005c02a4020100e200000400060801403034000d00c21b98480351105401c130010b0881d441030078400c1c074000c0c10403a041d0320101c07000044075400134402c90442e640d95005448012041c2c0c41c0c814070400c1221102c0c4190f8844000e180141c0c100802141c55032200c1c50301030f20703107005551030082c2030110b10204805c800000410545c0c2100409407020a809000b00584000035800107804400410142c40c01125170154012480f4000856051241a1850005984070b1419000d100490350b0160001030020118407508600710001d141103a1700900c03d034180b01e050a206950107401a004036040c00190340e44244841c070f01c460001c02074018401260384543d56903003205001020407a010420061101d20b070740c4082404508400180a104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 521089415 1250 521088165 521088173
    0x30f0607050910020a150209030c1314061903031d06160c09021c020f09060c10050a02040b1603200f0f1501090b040605040c0305060406140105091219 66
    0xa080660401e00034510b03c10000c0400d072000814151a9801508201181d80c010f030380700000c0c0d80031030380032901032107004403524041d00c8440c0410f071604504140003c500c40e03000214606803c000e04010700c0754003405040d4290005448030300003101d0345410308100038510350245e1903074030b429a02e00d541d000c9404a580d8040c0d81001d80c0155110b84241c032a451000d0300c80c64200103c1c0910b40300084200801401c196511110303500070444000703043c0103070341083c1c0722400280c00f9034030a012446654002082d43c010845013401842d0304a11900802c0d03082a062442c0340002c0d0065464600c040c0804e003640400b41342c055a4001c550180041d9242d140c00c2e01a900140e0f10003800c2842c203802d00c07802c410303038000500105450902d0b40400da1801220b910b801510009400001035159000d540d40000203060340d100c4c0300b000c01140003502c000c12035180940400c01140c0080d4010010381d9400c22010059070303480030403290145021940800350301c00380541103140c00409500000440d140e0100c9400340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 521090665 1250 521089415 521089417
    0xb01110d1803020612070e060f18030c03030403210c02011e09030506090706080a0605010e0d05150a1b021b0d05010603060c02030c2104180e1c03061d1302030f060705 73
    0x101100c0d00c0d0b1072207010301d40041c440584229441091811400d128400d492042b41c2003009a0200040c11551122681c0c00002e08683c001e5004884001d560f4200d250614007a042c2600302c08040d0428100032002030700040c2982e141c4200082d50854201e90743e2a03101d000f0001318001c1c6800000b15681031902010061f919a410301541d80421004c40001e817004007140100d00685106966091021000c0d000340704c1d403c1040303c0d049951740611442c0261000312515002c0c07040444002c04512a013074815001e02c101b040c156440115003100c25003048584001205018030007064802d41c0d401c0005017003090042c80319410007050340d81040d00000c082c6a0000182100c54030030000d44001c20b03007000c030040e000702441c1601c581c0703100e06100802141682c422000090181428007240b440e1766030798150b00701030101400391050802c01c0302c2e00d00095414031907400548010400e40c40b440320446500d150000c8014450241449064013200440d2002d00401002c9581032049440314140b0950182c42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 521091915 1250 521090665 521090671
    0x6130c020f120403080403030f050d0c0804021804110609030102090622300303090f1a0c1219060305070914060105120406240e0a0b01110d1803020612 66
    0x31912680c820440381d0b0141c203048900310380e40704258078542881d540d0300381c078440000d4080506105060080596a8515008509104c81d141e982c11130241340a1042140c13240b911400d0035120f280c200b08110026032100e09400100030225441344d110149400081d019124a005003a00b001010511000800740483c4500c0b8105600c101884696210300c004c00580b24045000c6041040e5801120360741800802c007044868042e180105400d60161505451501c613021304888803c81c09560500c40c01c6181e80c02e58110040010070781c60300c1c80750131100000640141c0b080c1301d1031001c0340a6074081c0d111948007400841c1d010095130200740d41c0f02d00c000300400a5600746138107000180d0020b08990700c074038102e482548006031389401a40340c68590000624800c07540507816101c21340002e840e0441c100c8608000c0000380711004441c80d2001081040c0c50606c0d0345581404103801024103280001300d00c86606046518040000d5560303c00180380340000303a44041c5d0820800034180e4111266140d4541c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 521093165 1250 521091915 521091943
    0x5060d14250509070507050601210f0f0b09190b06060408150702010e070e040326091006050f0108071d040603030509090f010f120c090e0c0909120a0806130c02 70
    0x8040d601c0102c2a85c2921034080014000d4010030018044240e10038405480b0780e18003108a281c8501980e60300e02c080440ba40e041e112981c3c0300100038204007500d20401c0d4040240806490300f10ba03025820000511a0000100180c9006000030401d80300c0005540003420050210f4116602d400030340440b840301901c1100040d400c01581e24055440000d9003401c8940c107245240040d030b100e403400c0f9221900d81c03403898910b4150000c84840d480e10082c0304e07401000400c0161480300070080d800c2080342c440e50f100ba8015280351400c1d41c2c0580e007203d196544904541003000120140b016981050240100400d60103407a112020003450750010103009a02e0059540c4c40312501e0320b1200c1000301d40c09228840140c5400c050a0080318900141c0000c4503104600360070340c0980383d03180074080c0e43d0030141c1310400f94080070070144240f8001c0d0820760070600301400740c80c0811068004005600c42c0394003640c2400070b10030101d1034a8030740307405492451080100800c07840454120094a45c80d80c005810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 521094415 1250 521093165 521093179
    0x3020d06030321061a030c0d05070f1107120b070207080a23160612060504020d09060c170a05071b030201060603050105040216170f040f06021005060d142505 69
    0x188030000c1c901c103103403d54494840d05242c02d10f01400c0700a031780d4002800b0081108090040e030740a00d5450007501d02440f459141c1c0c11003820313004c02c010310300100400039085aa101c030030200074026034889450346098204035400d0303265a440c04240c1c82c0807119445545184160310802e0240840903920204004c9480d00d45808100c400a040f031352001c5208107403404a2810a08211049c0200c00201502580c0e14021a040780c2c2c0c2c10004040380c01001004000a032901c03405000c00140d840740da40e07181d18509000ca002030841c0d0800d011043c00600390030140e6a10000304800310300407042030b103503001d0500752004015581d1400074045c0030580308074400309003042c0001c00c05140030300944000f450740200100c900441c5031140007840c07803100003c11040004100070099030b10241c0c001c0c000341c80f070030705240341c07444c9462802840c1c0301c5201080300a013403a180c203210a550380c40d0700301c116075a08516088181c0300d01d404803e0800f201000d0100c2000006451050302c000e400ba081001ca880c00c503100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 521095665 1250 521094415 521094467
    0x105041502060610050c0d083d12030906030f1d1f0b01050a140928090b09010b130509191a2206030c0608191a06090103020d060303 58
    0x17611540038040d007142640c0c1151305c1e2004201c5c4100740241e03200c0c0710302d00358865907580351900703401f0040041c00300c550181a0400b180f50b00001070320030400410a08036007208070b841c80e44005180002c00c4c01a44201610f0305440c000722603e58212402c0300d000d012020301c00b084010801551880003001c100801412140a4000c1001c075204681082070103844039440c0c003c0e5441c040718091024280e801a41d90180045803694445000664030f001c22013006251404d4410403004807203080c0c2e48410082410814505178584445411504450810019548071104407104546031101c81e000135420040100820540040b001d5800e81415005d40302000301540c00441345541208010300a9040050038406400812004c1c00030500907010000000341540c9a5803480242142980808000f45103070062000c1d034841c075a80350740304081c01c2e4420001c0380000c10718a200445000076051042e400407030382c80290b90007130701190b0020b0350980c810420343c1d842e407501400780300400c1c0b06102d04a80d002c0c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 521096915 1250 521095665 521095667
    0x5191205070807092a021002311716090915090b0a060603271b0e010911030907050609031908030a1b050d0b120a050607020d0c080304020607020105041502060610 71
    0xa5a400c1c560f06e6001c2c6c6581402100110065800380c1c0c4840303145207400855407016495482c0700c0d0010010318643c111001d01e481041c0c80800000381341d414480d0010324a02118510915003202152141c2d50045207180b04d07410100101411080d5035003c642c10003410200300850401440e110781040c820401500b61a100110101c42060018006458422003400b100000020308441d96521408911070b4122a500d00b40c1d1180c140b40e480741785801c14020040c0054180c0e80150740d0080c130600204c0c0c0c114a40034181540c0e4140303034031980e0700a184c0006d001c289510309101c2d9111418251040035820a0315251005c1c1c01d0380102c400e40c0000740b921508043c4104000b4003081100940e565180c2490b0055401100919141245940c00305400b5901d045051301800901c4d0100d0090001d0300e810320f02010003034141232802c150300080010400105001030301c41801e49402039010b6482688501c15880140c801d03201d1074011100d00720201c0c803808042030303001a1880c8100750070345e4003605ca4407900300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 521098165 1250 521096915 521096981
    0x70f060f110102030a1d07050a032303070506150d0b0708040309270b0402090607110d0f0f020f01091a0f070c0b0a0f17040b0a1e0608070519120507080709 68
    0x140c0e527100d0140003080010482990001000c4201488003074210424010482e01e16404800102ca031608010100490001006003d041d144010f68151000c1d280b5540c070308001d58002404c4500348000e080204041c140303e400900041c00c0700214140d90f0440c056481d01c005210007001010b0203040052118003030900e40203031101d080c0050005401d01b00d059a94010300e100d40441190881b001c03200f804017282c8441554243e85001d540a0015251a801031110b0411109410360601601002c20400102d0324440003d041c491401581e44ae185c0c00c903900c102c00d01c2200801b901c0d10504c04004180c88060500034410503055444d034030b651803c8400c064481502c120300d5151560b502c00000b50100b103190b1145540034400342000944001060084c4d1260395025954260040d40c0d5907060203998002c010180103840212603071b518111070082c1c14032078803803030b80681c00861503508502d1003041010085d1030003400da00342c10780300e10648403800b480c000e280b01c0380348809440c094181c0c2078201e40d00312 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 521099415 1250 521098165 521098169
    0x2607050f1204050d0f05010f06091401050102060c0705120a2016030201051621090e060d021002192010090506161505060909070f060f110102030a1d07 66
    0x5084a402c1ca407400c0100800365800d12801d940070311310f4101c1a80002c0c0c00384103504160420300c1e0009481810075481000303d550100701641d51074a400c005019581e00000d0300c651058a81035400c0d520942464410f0500c110600010f060240106018484541102010a03107c2c1d030020004007200080c4541551400d40d6040200d508041581c1440175501c95401061048540c071141070030000581e87d0741c0b401e040048444280003100c3d14a00c5041503118a0782c000400c840c4d115138907641402c0000480c07440e41c0c80310003807060000b130320300703400441c020700000e407151101c6504140300324500d0030000170310b0501c08040e828009003250b181e14030785000752100d0070a0790241d40311010ba60406060016903400010740c01041c54031490005c0000b012408202001e1800200c04140c07400e001081c0451140043d00c0703030302141c22101080c040d00341c00b42c5849044400514100003401040345c5e0a40e054800740007822865400002040300c007140b103800100f500b00220a45070749043e01208416100c00c014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 521100665 1250 521099415 521099443
    0x20c0c150a0315080607110f0309011b03110f07030203070b03191e022110150c060b0a0e06030d0906140d021201030c031e0f0303092607050f 62
    0x244200c0c0c502911a500415401c0041c3e0900c481c1e081d242d50030945450f100301c4200000414080034a00b04034401c0c0300b610021101100214208014a03002804c2c1e10200011189918030703174101d1509052141c14039103001e007500742c184c5420110903a40d060b00d03030300c0c14002a8006e205240d00014018203041c2140d226103010008101c04030208030030301d0041c106d2074000c020003100a02001c03418694503c020304405110341062410754140aa80d040c006c03000600341540e01d6840c0004108520002203944003050303103484c0040d00c03940c49241c04401050540c010f039030801071310b03680420160f620b4403286001d03c10441c00c40e510304070444000c4610184030700810340000c00c800905500e101c0303c80003a11080c2900b060160a001d0042d84951182c0400d90058625540c0c0c0c1e1410001d20280705885008015100c424209180e5640c03565015240000e80007802c240ea1070034903d080c090600e04442c159a04030a8000c0340e0f030004c42011229800460f01a140390140c014141e44000c0001040c206501c2e80c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 521101915 1250 521100665 521100667
    0x50f0f090601120b1506040603090309080705010e2b140114040201050d090309031208190212060d240506130501080c01110703061b170601121a060706020c0c15 70
    0x880d03440e4030940c1c0e0054250007005d5680804000203075501800b40003d4403066800040078441800c004046090b13076440070400f81c004040500099a1200c0792051559007510300c081d03e00d9402e60040f2004c914849401100b944e400b13560001c01c142d00070f40204c4124030000a21048003078443c0440b00190a0b00d0081c0420020003009107142c1c8281c021034201d90107420400581d41d47c039241d54014440000c40d29001503050002c01c001d034640ca640d07003003200000d0441103041c451498882443c00780c000d05098030941180c4203c1042180c086d1110206904c0d60340002d600030321441065014010540301c0d00c0c0729003a030b403141c01c1603c0068400c0604075034484004080c40d940c41c6005551200507440160b400f03008011021021810030300600c2144183c0724080004c55060200003460503125880311511500d001003889010380c2d1011103403009004203d000502c07040d8440c05105028110482103030404400715440d028040542c0c09840600405801d4513402e14802c42004184a103803200040300720701c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 521103165 1250 521101915 521101949
    0x20307030b0702030c16060323061306120506070801060c05030d051008100e0615090402060f070b15031e0c101b03050318010509030a050a02240910060612090c09050f0f090601 77
    0x1a0a5200b10031008444d000061541d866100d40002070712070de502690720743e0002e0300340596598081c080d0b60041400d890210060380c0f0030f90760161640316180f94003120646410200d0f000008852201004100c0b0400300c514001e500306411001e003100d09858640c5010b030030f00041c110307103003c00c1c80101802c0040600d417035640da660800c1250742040e00b40031400d650500141000503004804203018130303000300100c4100d0148204241c030744950142d00c0720000b040507401d480c260000003005003071858104e0306c00d40702c2841194112405407510440c01b540001c5000d001040c1604400298040d442e99030500d50180025422642038810a4400346800d038400c0240b110118070a0018103001e40d41441580c5401c41d0f6501d805445084d0410f140c070140c1c00c0b810502c0840c0f281013080d1003000748583c0080c00a03501e88040a0100c04445030b0804002e0b484040050400011074a1900a8280039108200c103051141030341082200444114040701160000710b414200300154541c100c030807200500d01c0d149 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 521104415 1250 521103165 521103169
    0x4020901020a0f0f080310030b0a09080d05130507090b0f03070f1e03050a032109170a032c07060302040503030414030c12010e0c0d020307030b0702030c1606032306 72
    0x200d0284015903c1c600010240e00001e00c25a0040d030051f481000c4041c20305045003081903070700c4000f8180c1c608903454401030ae4001074001d425a440d40100c8280000e1756940c92001106000c084030004003240504c40000c02c40220350b52000c20080002e0b41e40c1e5009010200515941d40300c207005044c440642600c0410011414042c184207015604280c0c8102c00c1d07807503848074030740424541e0482c00b05600d0443d545901c9180401c8032a07a0419000034031a14403a5140d50a2400d06600c003585038050000701074032600d009401086100420820b092400881e40174941590f1810719035001d070f540194a80000c2d4248a40242d500744c81c4024041c503e0315141c0420003017041030010070141c041c003410351080f21599880904040503003000001041c242410340300103041129212000e2f00c00d2040c14414000740c4c41c00502d07041601d41c8440604842c0e100c5a100342d00e1400f43d00c01d80412032148140c0c6000100c07811031000b040312402e840900c10b001200d000c00100441c0260010104206c84000550b0740c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 521105665 1250 521104415 521104433
    0xe030a1101020703351806031b041509060804110f0409081815210a02091c060501061403070f21020405130506010203190917011a04020901020a 63
    0x1403101401107420640c0d41703680b1400c102210708142031440300d0810000d9003440d903a00c8400c54018075401d005180c543c800e0301d184c00d40e085000c2c0c418000d034800b200143c00c1700008100100202003a018075034507255103a032a41003404403c0031400019100348000074005004101c41400307281d005103013840040c040802d200c020800845220360181c0c03255404c00118004400030500180540d4042032082918424000184e0f030104901c080284200016001240d14030840c00441040c0c81a031190350302d0f03140303000001e402180700d01584940e00961000e03030480814121804148240700501a031380e80d0718003c2c1d90040e4010384906100e50104002200c0ca449040610010310305814150486500d030f502c0349284200c280307a401c1006a0000c0c0520452400741342c941d00741c0e824420140b1003468142c0000b03480f8000c1d00700e030000308107840100002e0180a154070001810602c03c04500d0303440511500d6018010000da42450b130706540c0e00c2c1c1003032030408e4001c59181420680051034508102e030317180840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 521106915 1250 521105665 521105693
    0x31303030b011e03050906091f0203060604091506020f01021e03090708100609141003021203070204050a050708060409020a060f022b0f021605060d0f050405030d0b010e030a 76
    0x4010f44112503140710702c02c050781c0d08040c045694001810346811001180381510191100345181d000c0780c88020100041004040c2d00b8101220150302c949070080030031954000c41d004604c00609104000180842586044003111029404c4540d1070007226403040c00c0b0302c9189000003d4058014000c031121099100842d007040500040369403682e40c641980d81814030110300003000341d807508003c008aa10300d0103803041d843c0079001011030b50b040c850300100c4000e04a1200031b014142c0c1e68900e100c00c200900c281c51000e074002d0001d0241c2d10b40074880c2001030004603000c002050b54540400c0c2d01d42010311545600590182045034018200082580c580c013082a104045219417000391450180b0750920b4164119610701b03c00c05802840400f1300702c1d03d0440190000c42d40161801c00d00c03d8a041e803040100c0754151a1a80d444201003c00c60140020345020000941014280820450000010100207400c08010005003c0d0100111088203610403490303410703804080c00d0004180700000cc115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 521108165 1250 521106915 521106917
    0x50705030d1410050111030412080415081e0f06060306040605030a050a17131a0c16050a080a02010206060f22060e01090216030315120f050111031303030b01 69
    0x410038a5803260a01a81d02c0e4411042840706124240180304030f9112400002d4842400d2081c01d4140349120943c2d240528030075440320025403161b07001400340035801c446c050030310541042d038100c00d0485e01901c00c580031b8a06400d048041410190042c0640741d43c035001d10380039044080b044c0c4480c001c000e01170b08003402050f03110340e0340c03070001846985c20404e01c100284101c2c00380c06006003604168001100303c1c01000c10350701c020055507244e00c21011440c1d05a41c0d002c884603450300406100308440340104054184240306580c042141084440c800c10211401280c1c4030f44656112880c0c40e84401030302c3e100034003507489031000c41d4039443c01050300d91a003500500b021080303501d100d050b280c0080c0c624020b480b0072a80ca801c203100c44540003108a02408440301c0551506d189040d0f4403440c0b0300340c51005020150b031520542c071002c0e01054080010403d02d11a00090307106401e00b2008003401c00b0049990398605000f201300d29428905480c450720b200c0005c9040c8c04c0e1176450503005401d1a010182c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 521109415 1250 521108165 521108167
    0x606130204080f0609010b091308070f060204170d0e010f0507060e12190e010c20040204060f02011a01091203050408060c030109051524040810051605040b040605070503 74
    0x124000d0b0b0200000b6928408441c010310040c03d10008031030844140c601c0c01d5028070940c00070030201d00646102c001c201395009692a079030b10010706081050103540c0b00010801400010b0024600c9028480c000007500100b0036142e5110450030151f441c1c0500905060105140340102c00310700c2d000320301414101d40a554007089500084201d01e042c1a034803800004134080c045034400320308289040000c450142d6041c070700e24104144001900c4004446401400084840d0300f40d03070221090001e1501420014200750744a503120480071780031641801001c4d005610303201001c6160500300c8010700107140c1c180c40f022105030401d42d02d018151101304e8141d082c00401c00001580c04420012684982050b20700c02d42c895050500200540e0400f61070000c41a2945620107100d5030b94040e4007440480b07810510a2604921481088500550344240618081d000310070072071080940245200d2070305194035152042c82a2030a43da1802a03006131100450244428084a1f02400c02000d840340200100c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 521110665 1250 521109415 521109419
    0x1101050d0b0409050105071e091202010509030609061b03100306150b1809060105030708070302160203060901021801050403030c2910090f0b0315060d1719030e0606130204 75
    0x46000c3d0340c050f0400710b800303a40d6a020040040d5002c8840c08800384481c8a9440400300048010801c110324040d841c00741c2510004081160b004804440b201030015003620064600240e146842e18000c8818070426070b46544900102a0307001c04403442940e421040c1c1c030700c40d800d41d25030500400040d204041e10440c401004038600d0fa03c80090321440081461140c141d078550000e0100d10a4040c24080c1480b00c14401e010340103030012085580040c0340d03d40161940d00c00043e41501001c03012000e07400d0b000705030520001d064103400030103000038080086600d48080000440c2d071031103540b0010b0b0024030603903041c0c0c00003005140740d921403011140f2000c680b401c850680c0916a031041c0ca07400c6038194010710801540f401401000444204840104116860340d804240c444244450000d400f400000026400d40e81780c00c00c41610607002000051800320011206c000d5a001c0901200d0b080341200000d440a44240900e90107900803002621960300c07111306109104013075a6040500350340a000c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 521111915 1250 521110665 521110669
    0x92c0705041109011b0623040c090209010c02040e0c270106090f0603050415020a050c120f0702041e090c0321120e120d06051503061503070e1f080f041101050d0b 71
    0x4811608040c0907c00084c02c16181c511558450b03944100d00c03140c010f00c00300c58940e82024510120940507031b400f1417001c096000060074501c56002c41c40d070050101c3d120800c00030082ca0a07240303155a03610220311903600e440c0140c0b41085031b8440e921503410722500521056100e500040e810038030a0940044090400f0303280c0060307820010740d560001d00c1c04181c15910310b500304011100d01c40b007650080d107410400703400480507205182c0040c0c0075640701e4103072461101e04074031515442c0c4010502013244840c04e00d40304040e101603220659404d00700c0351841c40301d00b0510742c00c0c0f202100d16840e035440000c100c01039440a002558410f51280c003c148804149058407002040d00681d01d42d80004c1d003d043c001000381c0e10400c40400d04080c0c00c14010000c142e1035588001e0202c08040200580360307038840c24210380044002906a8100015508085210f4142e0081d44118403058441803220b69601504d500c0b440401c440c040c0004a44400c1c0702015400340c0000c1c6410110700102144440780c02e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 521113165 1250 521111915 521111951
    0xb19020408120a0f080f06011b050601091b03060617060f10030222080c3c0a0803090f040b0d02031209010212070b01092c0705041109011b06 62
    0x402c0c2103114400003502880d85502158800340442c2d907051040180c2001100740c00c0e41c910051403107060014144440f4170007000ca001a5980980c0007085602070b60311030107020060300e80e41310f81115480706040800104d6000380907400c00c0d5030003562040e10340b0804120050314480e014046c1d540020f149880f40310162038124600948c1000398074007503a01d44c0ca21200000c0b0f20740c0c00c0c02104841c04071407814403c4078804a54a00c0c1020100c440198080009200c0b400400803c03015a41403042c10803002c1d1410207407010520098011641c041840303907520b000c3c17a26845540c0b480d0b98000c3c031566a40d032143c5859802141e07007100140040b0b8402116138040391818080780c0d4041748805012605030101d43c0d0420202c2e04400c0c0108500b81004800ea945078401001800764942c016103484c134405d40d140b001c20b16100600a0200d41d49201112090020380321011409100e0155080c489013400e0840360b10121200c80c94107035580c1c030300d058a000060303000d00500ea40403110309851b00300318004180c1c804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 521114415 1250 521113165 521113183
    0xc08010513050c151b1c02100b090708160509100201020d05090a02090703020d0b0406030303200309070509150d0b010e061e13271b030b19020408 64
    0x59024085005030030300914100890403954401c00280d40420315010802c81905c03400b071051000b10005c1c00c01c0ba420b03141028900740c00003003050a40d00c60380c03170320075400644501d8521a00804004000c204028004605400c40307545000c131300c245000c150031085030700000d034076110390785011030a2007990000142c810880d041c01c90b006039004102c3c40b0180380385106240d0000e068a0040001c0d181c182c4c081406030744000c00d04818142d001c42c1840c82403a00da00000308080d4024001c01405850380380c054000c0401d8220054160525812522a8a90f100c1107030f000380780c0c0704010a9078501d001d08108040d04010721004048098181d1903685855100032586920300c10782c4120903540c100150300300042c100505162049010760810b019412004a41c010301400984103103c000046004040251002d44108022000c810790303188100408814504e501d24803800039109041d00c0c1c0744004440032964040036005d11340c000b0201c4d00301641d40c001c100103031594080143c20550355941c510304124141c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 521115665 1250 521114415 521114431
    0x50a0b0d142e120803102c090c031e030d060e04120203130e040311060c0a02070f0b0f0912060a0b101b1202150a0c0e010219020d0c080105 61
    0x40082c411400d100302d01c0a02401450388201c040b80e80303008008050000b0980d800f43c4104c0000000c00c1c4d00c0c0c100761052801400c544910801c0c0b000b000425545040728070b4040e0102441000c011503040e80c408982440b1040c0002c0c0284215230514030700002d2200703c0341c1c0d0345c0e043d440100501103c154403405114020500d40803070410500c0d040c24400c02d260b058040741ca0464208000702c07a20408520f42030402d42d2240e9260500c03590711850142e51034080c0d0118007119210b200d080008904d4504010800502c2560a0312000c0e81c2e1224035441e4040b05000704078549109002200c1e9241041006d030210200c02080407240e401c1c000009400c0c0002540c40c41c552584a002802c0182040c00c100c43c80c1c010b0724507200040000000c0d103540303414210f600052144c91414007109501d8400c2010f85031403989605041c03181e090000c40c01e03000b04a41c40210003c03d0061554454541c0041900061590024400740d0444900e41c05c01c600c1a0076000112007010404a004c1608102407003858890011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 521116915 1250 521115665 521115691
    0xf09030f111609020903060c0403210c1b06020c030c01021f110c060604050c0c0a0308040201030b030102130f090225030c080d0b010306080c0102030f0304080403020d03081807050a0b0d14 82
    0x1000040c14203050000748030100c23042040108000117800b040320711070b03050107003c42c040a0701d07992081150310310485030016203401d43c800aa101c05138001d1404000301c0340c0c0d135000c44104413542c2080c142c42d41482d072001800b41c0c10405208409010004079091003c21201e030019a00460f50598222034204200c0c0086c01d038000300806c4030501300361003241e0f002503070821607a040445001e41030365140c1d40c00c0001400c002c000000b140c00c41e4001d030424600781000600964683c0040e210090b0b0311a4184107a0344c0b101e5060780000b401c0d4496200300c0c1c04450f12500c940c080304540d1302c00148640750040c411410019246449400304070010050105c00b481d2940100c2c046072000001070a0720110340280045070004050200303d0ba800004a0f082e00c110742c0349850310780d030300c0d0305280d42140141d61010707400c100898441c0e400c01d9070008029208248900500301071030100030881da40e07984103000d02074200b80c00b20000e0003843c0d0307548050181030340600000315040d00051030907051713454252444410707210 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 521118165 1250 521116915 521116927
    0x5073903050607020c0d0f06270c050f0105120c040504021b160612090204090f03030504170a0c11130e1c021b040e0f01060e07030f09030f11160902 65
    0x40c062082942040140c4001c0c079072410400002461040c50802c0200800d241e1f5030b102c8200511600105684031f80060150034030030410000301004054144201c400a2840b080410305140c90002d5041d40b0710107035902c0d03043c2018003480174103c040c040c100f1459071806220000f1555a103000038866000481c100e080304180c020120b618214050710641080c3d22070b18000d021040c0d101c003c000c4003e10004020800004a00110f402002c1c11800940240c0702d0700300520034076400d078010b68000c621603800074000490b6866464011701071503184000148000201c900400c09410008804900040c5041c0380385030b0b01d1001c00c0860f100c080d08501d13580c01c54440c030070340310002c2d036030700028449a070014200400281000c0e00d0f245003411241485150785040d81003120204015007101203401000030003580d0344440c043d0f45105012200f0500203402c1c1800c01c621004180a00013800b42e2689820101074245442900c02c40d0b654400c001c0315126105400d02e00e030745400712950080030200d2005903626 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 521119415 1250 521118165 521118173
    0x105210307200906030d080a090c0b03040c0b071509031b06092303030105040c02010209060a0306030c301511030105040e070b0a0c0609200a050a0605073903 69
    0x4204004152003400e01004004c841d03140400c102c440107840307182440e910380d20140070400510f4640f0000d0038003254088049a0444031130011070259004030717924001695240d400c02c4061042c907100a041c2180c0a00001d0f01e42402c2c4c200c103004601c42d0070441074040c1d24000d80c400030b00502d2415200d65403243c0c1c421080c000742c0f14100490051101050b025a0200015a5039a11040c42568091540c460800034100d00c01e42c15640000c0e0700928441d500c22820800270003070a61400113031081241d0080c00200c81070165001d014001001448083e00840312034007483c000e01602d001e841c1c4880c80752036030310342c50300c14400c0f1041c000481440c01e40f00e50600c8140300c2240c10b1860030040d10750100005000d20300713080040e00c0104d034030340ca801c800e400300b40d00e4a18068035122134010301c4408400400c0194041c40c0061b000904000d4480004460b42e4808109001201d8801c08000c15001c1080101048860140c80410018150056100c1114071410b40061484c1c040f003000f000c01300b0100340100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 521120665 1250 521119415 521119463
    0x616050a03080603061303140d090b0a1107120305101502070e13030c080a090308030c04140f0a1205010b0d060518011a2107090c0207060c0b0105210307 67
    0xe43c2a0018116407620446030a903500340c044000d01400300310381403c90b020850340125400106104800d00801e4520314094020740b80503504e2280c00c500b003003241b07010803440c242079640041c2c01c19414680c0302c0d05104180c0040c5405080880003410101c0302050840520700d4041c144001540140926880c1807068802540080c00a40c1da481d0004084004258009041070005800440a40c2d4455891405558a40159100514010000c4104180b074142d680c060b104580300072400c0e10300809181c0c108451a04509801644820b025070207001c0307030f00c2044148040505c1130000150910110780003e00045141c1401c9501e191280f0401003503a03000441600403242100c02403010394407061902c05600c03c20314486004803007a4090740964100d412000e03a08002010954020603201d2a451300501050383c001c0000d845032800c0000c4961140d05680b00d026000080200c85900340001c0000464010141040c4454171030786070522540c0900c000c01070300303129070078090460507558034850f10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 521121915 1250 521120665 521120671
    0xe0f0106051206010b0f070b090d270b03070c0510020a1b0309030b040201030f0513020306010b13050d0f08040e010806060a050108040b180d03020706060e04050a060b0616050a0308 79
    0xba25090318181000ca400158050555074a00d6003c0d884280c401102e40b0b00f0701650b103010f001c4080c100180040001c0c04114040072540603542c0c500720500c9500700341c09622000c80205a1204a1407080000d4001c507400f950f0030100c00d02d4407402e44c07405519110b2411190503680240194005800c80c0c40c5600054024001101c5920141030f003039040d100984504400c0c44043d0a0102c050001021684030340d00040108100306000c103c20f0034001c20b032500040814404a00a11034900085009051401a600826040c0c07503002d4665081900f409500c100340b200c00c80746401c401c2d40ca880025410f20203840580b001102c58251903145c4000546099030107021170b0700608a9a07800d00c580d03680008060340c400c0d0045c9544c4000c0d1038100350b0070464110300746005601c1c0620f45668050640c95001070030b2160160100b480050384440d103001d090f0f40c080e03a0003411a804806c030400083c125130059000440010840c41c00c00718025004016522010412111500008504400c1640105001c0c0d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 521123165 1250 521121915 521121919
    0x91302072102242a1c1803020a05010b030601141504090e030310060e100c0f0c09020a0801080d0504170c090c04080f1f0b1309030905031b180c09040e0f010605 70
    0x10440001c04113020031481026299402c000082c42c08135100b1049400031030300001c481c020503007008001d040003900d070111031400301c071203500341a99004185030000d001030599075143c140c0c88003000042c1c00c001e1941d840e035102c00b004107030034400042c802c0228801c0d820b41d001e074000510364030314050031280c4880d00309400880502405103500d07101522050101d45038048182048100d12450303082c45c42c40d001c1d602000402d44a00ea40300442c0c2c0e44400c3e00a00880d50480d2145000b0b640c035905070a44401c3c1c0c402000c00010800d010401003810315009101c001d008501c2520108141039001c540c052208441c007015602e00001c040101900802007003031101e5076203000d04020b10703184a6202c031800c02c0c7c00b11400740d40d846402c403202c1c983e2403088a450314000e01d0800c1102c121b15182c0548041d41c18800d081c407a004041d445050064101c01c0001d034150000c4c04848c0120160788041d1520780080d16581c02c4c280148007030621900c0d46d100d01810a094000200389901d03805010600707491042d00014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 521124415 1250 521123165 521123221
    0x1060f020102130605030c12090c040f0b1e0a0f0f0611010218040b060408100905060603120306090a0b061209190503070807170f09130207210224 64
    0x20452045000c00140c0d00b080c03802c40c0c0d407507d810032070084501071109111310400c8040140955500c0000e25803100305401d4070b0500854800c1d1000b1000c075803c0d00206500401595620020001a100011011a4014407800481d5150880081c42d00360a400800f4401e5050006001450300714024640d00c1003488003d5240440400101c02021800d1510500443e1508500002c03582c4200943d009401020708651f0303042d00d901c0c5000b024062040f0180c50501501000c00d003542800b00d101410481400141071440d01c944050103015000141000200da030b8560244503507584580c028616a06244107045031030a0121006040c0003440321206061300101c2d803590000341d804000d0741c07070964101241030b881d081c5504010b00800c0101c000034146a800040c00048040c100c1c0241c840984240c5000d010442e07540351850032880b4299020303012450086801ea01030340001441410514140305842e045561401040e4025091030b140618a82000e4100a031509200b01c44880c1110030070812 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 521125665 1250 521124415 521124427
    0x20406030b041b120608010f020403120318140a0f050a0b070806011718032a01090314090103110307090618060c2003100c081005060a0c0204150303030501060f020102 73
    0x300d56428450103c0d50203005803d804c1c021114081c0d800100200b80e940003d12001d09140d809400030f500c280412500d0000760091038540c144a40b0440b0524916000c000500c0a150340ba00c101140c001c12040d03500340305181c0710a001402d9100701c6812544120b0040036a41c85510303113040d102100070003180801052200b0002c181e03a1291103010703e040c48508004c0203460700d1441e0204241c41c07801201440c440094101c00080c40d01d9010907460802001d407250400c0c0c011689804c1e41d5508901400260320047c80000c0c2050b1200245078242c81410001035204100c804200caa4000319403000100d03840e5102045056000bc01d000ca400145604c000d100e03038240b14000c1e00060411601502146040b402a40c104a005000b041807040007022180d0282e80745001300090050790b0b1101c000904078501280780d40c480204400f0944500405941c1003600c0d40303600301e074000304815050340d00684440c0b1212590410b0340d01040030758000c2c0e40c003003095030604501500076404544050304582c810010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 521126915 1250 521125665 521125691
    0x4051003050621070b13091812090501021209010e100504081504080f0a02120304050a11010305091507050405060412210507110609131401050613150c080706020406030b04 75
    0x110810381700d0384180b043d290f42d400705a440d0201c2039038000d00303402c070f01d050f010404000950400d480003d10580c030650700b45251810817034410196115490241c0d00949103081316281100160003074590602d0942900d000c12000100d003484802101008500000b9040c0103816083c0450300303178514004040b04180c1030544e6014440d00c9050041c4011910200d000c1a20500c01d0009c0c00ca019a01c41816446c0e0900703040040d20760700000708c00c0380c040300d4a0f5038500580d406801907520601444011b000e4541d00b28507085034601004280404002c800c200c082201c0c1d585402800117064070301c5041019021074a44000d0f0880c0c0c00b900070300144c00c071203110300c5046c1c1c5c0601241e803456401005081a031280c10007181050281401c120b13441003a56405101e035441aa001e001039008042c3ca80807181d030f0307400522030b552182c1b000c1150f442c4803010050010718130101141350760310440c0c0340c48034030007915498017a91601300f040704a52031a0001000c20002c1d5141c081d020300d004081b40d00b006600d1807000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 521128165 1250 521126915 521126923
    0x302190c0b0c01151d10060203030f0c190c020301050a11220509090c091506040603110f07080c070515090d050f01020301060e1809070501080c04051003050621 70
    0x4140001103600042c51000d003007081d0004240d00c1c803d00c1e1260280354aa28010082c1d00d180301c1c11015035042c03d000580040d4050403480304507901c070b0f006545135807100070710707850788070001001c1c42c00412007045084401c10342c00314130001c80ba40e07a83d1080021542803041500350740024010240d02800c0280783c0281381d055104a03219103801014080e8001e4400d01c44840d00803c0d0340c0700e07590141d5440b0800c00101000b054500341d614040319140d005544407021100e40500743d240c41500403a0034003050250718020f40c005480d1113000038480d42007a11f07134503000307006032300c041d0040f00c0b684000300d00302080010420450014110480d140503078086903030000d2031140241032101d0b108115916020052017030502c04019000e00c0b800003596a0b40c4c6909010300190350f40a4014007540c0701070b500640341d05030708200074090282c0c01c020707140c0700303141c0310044a8208015000000c00c1d042080000b409540d00302c600b9100780400d460100b9940b030003d00300300c070f5007400d6000110b40b021319040c24007013204085 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 521129415 1250 521128165 521128169
    0x150f090312090e0a2c0109170417071a090103150f0e010b0a021005150a0f060908030c100504140106030b0a0b220c051b072c010b0a110105130302190c 66
    0x7010b035184820480d082e170b0301600a0400191030300061144815290280000030410b40f4020030030003054982c0b50b1140b5548811a104c0e401811144212140f48030300200001e10300020140f40c081001c82400800d13407031805d0343ea070008007030b000314810400030a01e060b0301c510b005103d11a03056050a000700c0c0065100c91200441540c0c01d6640da00080200c5900c0c10b860040403005820780e2205902d03090703080d140324206d0160201107848400001543d11000040f904140e0100003c1c2092102c0c60b11502d029140c0a00221980500c40d5802d44ca8030303500744130355401107003e100c2581c0142003c3d0542000c89252682c61401002c400d40e4004540a0035039003c00d0021026400260500103501c0484031400740c1d551512525000003100c0280c2c010000b448000c1c1d0b4440002c14002c1c03801d070005200c1e0240c55241d9140c60304d0401c001040511070640103031030709034240e08022038001c4a0008203801c43d9400c88000e201701411140d48401d040e410006149081c40350840c1e04c82c805079588908001110074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 521130665 1250 521129415 521129471
    0x9030807060507120e1f110702090402030106030f06050a110403081e0c030703110d03090506010605070602160323041a03130503070506070e0604150f090312090e0a 72
    0x2481c0481c10080c0b01da880400011280c01e410001724056902168882510081410340c41804c00003801050381c0354451141e00ba14801d04061030b103541e030b900340120824024007c2c0c1c1d00d035690b050000301051095401481f194400c00c0d000407185001d110034000c40b041c04040b04003042060000b0301c001403482c001c4a52401c100c0d080c0c0540c1aa108103034800d14802d1202d02401400701003101c9007010b410071003000c40d040110303090b62000f0000c0d2008800325003922001034200d80c0030a0041002a00a20003442003a002e02c0b07015240c210003001030150040c042508400054451090b01402c000c24a800d0341164100e100941c546403420a50340610911822414442c440010114448521014034584010303803007800e0781d03180c0f031250501c96240ca90403500c0b440030ee01842002c900030b15081d000c40781601c6031500085801d04a031030044888121a01c004020b0002c4a0000310100e007035101c107000b20341c100c1d41da0010100d0a202000c410140090485180181001c140001c0c2061034040c44c141903580e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 521131915 1250 521130665 521130671
    0xc100c06090c0810050109020f090112020f120f1312140403231b180a0b0a09020327120a020a0c0f17060402090a0b0a0b1206040501060903080706 64
    0x14a060003401010312807401000ca162a400018a420300860a0042d141070b040c004c212907030365420305505038803c641103142c0c480000c21003080198014800d00b01030203d10200141001c0d2180d07045d1010b0f40c01040b06800080c0b500c410041803040a00d12a9804910094900008805555590389580e44609188140800c020141c41a410400191801181c10000d040410507901507020039685501c0741c60072940c00344070707401560803000012007e1808400b50001c10410960400c03280111809040c2c0104c2686960149007d580d82410003c00350103105c600682e641481c80e1081001c0914044045602901500c240c0c215200480c01d9148150649030f996034900320102d0807820201d0000703000b8070b144c0710b104002c904032804143c102c040d1150003032103000480001004603a01c20017124004d62013650700e0000f520818a0f500300c10755100d005080000c1180c4ca8031041a03041e0000c0312642240312604c0c0400c1441e240c94042c0318010600341c1090040541540c03112405842201d00140034191 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 521133165 1250 521131915 521131937
    0x270c0a12210e04140702010e0303012409080114063607050903030c0718051630050406140c070305030606071e02010822022206030807060606020c10 65
    0x409000146080c2c0340c003c00c1041248003c1a2488031800c054900c1c10040d860103040c070551810010481c3c0c180d8580d10745500c3e0135003146804c1e186c0390003001050000c10a0040d400074030a1400d01407007034032101c01c10900d03010f454840c05000c0115201038080c21682d4904c074000901da0054018a840000c1840c84100b140e0b0300c20200361607a11540909079010310000581808071100895102c00b66036440000030318074441041418242c2e041a030302210918003440c40c1c440014040c018419040480031100310170f69144112086800103402443c00700c2c60b85800c02c0004200c0a48600aa0120403000c0d40b0010b0500e0003129005014020005052103400400720700c1c02d9440b5800d59013815132000001081207051841c260554601c001c003207011681440101e00d40d00700626184c06180c0c0c40076900c041c041c00e0b42c2c0130040002c1004240118030410351600040030301c0315000c0c02c0041d501a691080d580d0303105262040884026922950454014140b20006507a801100504d680020300d00144000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 521134415 1250 521133165 521133167
    0x1803010c0f11010902180108011103060a06180506030108010c03240618090903110d08010528030b09010b0310020405010504090e010f0507020c040f09050c0108270c0a1221 75
    0x340c541d901940c0034081e0100d0b0f003006c05100800301d0680d40114002d00c00c8207400700d0801c2407404169035865005550501c00e014052051802e02c0307040550310b03901e03807015039076201159065200303810404a994443c5a407240141d0140a500c00c0d03604800d00d14903100c00070080e8880703400010300503e020803160b990181c0420074042400e10181184803810821503030075140180c03505150145507030b240c1c058036160703031246030041038124100c0d1006030107291024880c4038040402034105407003d851083c80f5401002042d070150050348560440c1c400028100f032110f04041c90104a00003840101c0d00422041c000ca9920a064608413441e1060100c0c0d011900000140984119217500c4002480e00c0c040090720340d03001504640817a000d41e010490300030600c051206642404001800582c40302d14011900e521440c1b000d80d100c45000c03004c00c1900b00300a100020700c10301e54000c1400d0341c02012070161a1a09000c0c4100901584454090948060303036032841400c0c048e80d024880c98207001e101e10b421 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 521135665 1250 521134415 521134421
    0xb0109180c02030c031216051206040b0301020714010606090503031329160c050604061413050a060503161b060906060b040e0906130222140a021803010c0f1101 70
    0x1081550b025640c890143c042500e0346c0b52421a0444100184071035142d07090f5000b8021070303d215005004603592070b990030090102410441d00e149800d0746d4204100070214580c0c403640c2c0c5103140c064001290981c44c0100045c504851500518442e40040001803c1030f550024150120380889889030712a400300d0302801c00800320441e540600410028940a004045e02c1c11038824520403642e42400c0390311001489194051030198201160341e8094030340c19400c0301006840407190b040c50255101d0384a0005c03500d0041e840d4408000f141c00442403101c89100014801720700d682d030340303414241400c2e07103030444040c200c4240c0c010b00850342e550008000c1c040c40c0d4001d10042c141c0415120b56440e52080c111455580c11509070b4454013a041c00704240034140002003a016400074080d40f001d568609503544094000c00a4440740c1c1e54600713401c4008032107185400e1040b112034a00685620040030340351120445038071410b02c01d91400340301e0541990031180d190030404007403501c140003918000c882801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 521136915 1250 521135665 521135677
    0x20307030803012904150c230d0206060d0308060f0a0b2209020309030307050d1811100819020d02090319032606040209031911040b0109180c0203 64
    0x7500400000801e0900225510025420040e001d041249a1110260545028a002d020001d16a0b03c0c00c2d00405481039448048040c001c2c440c001c405c140c8030b213640003000c130602080c225a821454400716130070340501089610403030a65080200c0c0700207030b400500c0000c004012a10602d07040d07203420702036107901003500090401c820741699105280c04030744203164604640c51071f608011341c3c0042201c80d01e41c001d80c3d01411300d103402107007141c540140070349140d00046044600c503076449010b0200035200710b241c03c50b07403805004c07a260b00200c900d045c00b400111968030602031155803002d0000010310b112440024411220f030058641d400d8050740c0010788100080703298148607106180d2503049090000e007031914800d455038046000a00101441c600e054031a1841d404515400600142480c0e001000c040744014191142001420f8021542e16801c0800b52041030381d1082d400018146403042c814020030074200038210514000c0070003001400c0c0511251200c0d2507403542e1b4412030081040d104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 521138165 1250 521136915 521136923
    0x11030d09030206060f0d05070e1806010303180b03043206041101110714130f020304030c0605010512030702060918010602030a02070b04030201052b06030812061206040b0402030703 79
    0x414100c90400075550441980d480b031060b45a100300503410701d031a0403041b03605079101d0050006d152501e0030003400742c1e400600707040080c540152021034802050200700d01071072081d00d410341c0800c10300250030042e00d03640c0c00030707601050700308180808141301084103001c0300080c807541c000345560b203030305510b24203d01c01201207544592000d200400a6204100d800d0b040c081e41c48490b201404101199105040d11440d0000500c0040890302401c090041c152180c00c280808515840c40c2d4410b0002c0f6402254182c00050405188000300a00d074080d00c1c5c01070008446124074640410180c580328415040020300c100c5002138450740c56201d0500e6000b03840c0c99400d0142082d0303501c14029460780d20141c0f04c44014020140c02280480590050390166501a9540c03820060030b5161050b031003010180c815906a45074402c07142c0c0c01418050f232409144a030304d00c641c40d420840c80540964201624607441078100c600194902d86c0300040c401d6000c0d8112400c83c1d40c649941c004203041492542001e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 521139415 1250 521138165 521138171
    0x10819060b1c0e0129010203190c020f120c1311070f0303050f151018061106062e090915081e030f0d15060201060f0b09030d11030d 58
    0x2410103100b02d1401070034041c02c04428403e0300c080b000b440e07080390150f102c1964060b064455464922091124202041d001130040700d24182d00e100c410b201e001c050245090003d501c1130005800c5040c41c4003030300304000042d140c2c040803800443c00a0740310070601d140e0b24080ca500d41103001c0480300340d4200c00e4214014101341a0ba03085c07c5d080c000703010071005000707602007400c02c1d010407401591a40030f103100740c12920700354441980d21410040011a0700d0140e404000d440490501c00c0d50302890308100420781b685a03800510110740031582001401406c0604c540c0e20210f41241c0b25035607098000e40303802c003400e00e090001403600e4240c64030490b41e00016003803858200d03031314800c59210000c5c00c262002041150041c032205541c41c200c0c60748040242005800038040714100980450140c0781e000c40644002c10b240f02c401208090303103d1645d02010050791580000c0102102d10400d140180000c042003038506104240401c0d55070348a00d991000300075401040c0c1075140820700989007816881c420038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 521140665 1250 521139415 521139427
    0x41208070204050f0717060904080a0e04110301050a090b09040609080408030301060306030c2103111f05100b040305190609021c03020705030102130e100e0106030c0806040b010819060b 81
    0x4c054203041100c20001048032403600c81c100c0300045071614860f0700c000700790580d00c0c0e80d0303541c0f072a155412803001c08051140c5441d050905503168041c000307081c120000c0c0140c80b58035002c03c010010917541d00c400c2000389802e05079010313501d1b0701302e1080d4402d410070340215040001c1c0c41e21034154403859100113447d010100002c03504580c150402d500b160b00400034992805d0b2980710300b2440c004000c980403a4128800341d02e20000340104401d0030350051702c0003540d5100d4080e81503000d003007200640800d03440f035031207003008a60340c02c41030188003401034820f0aa0806080d80d40780c43d42c5003a20070040f0880c40c4424418401c002d82c940101011a9000d090015084002a400d40e001081a00201c0141c0607940005ca928101442600d0084005042040311149015a035010440025261081f0450506c0d000301e0982d84c0149028000c0c1025a40040c8d28a0940302c0201030000151001d482030303080c00c04840392030b03a100907800e403ca12070340801040700032103920110041070154050421000081a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 521141915 1250 521140665 521140681
    0x6010e061f02061518060f0a090c1e0206070203040b18040c2606060708030402030102280801061b14011d28020a03080f0c011406120703030504120807020405 69
    0x2609015100c501d00880360f1070080c00c01c000720000c0010039101c2c1407061800148035880c7c02a040c81160001612240031582ca40b50908262001110144041800e141140b206c1c5801440050140030982c4040c2c686401d102c0310003900c0344110300ca499801200072072081c01c0c01c0100454414030300c2c2e000300100311444800d80042c2c1110381d0a82c1c0310070701c0c0f011850f00d14480c1914190152140100030f222502e082507a5542d0303400303900060010398040d0b500388214803580b042da960941c101030517003101c943c0802c00f000c001410100305030411010840a500c84140c803050320444a54102e500480f501407141900c0183d5004103602298080040384500181110b01d4020070000840409001c4244c08a144140d1051703600141220003500a081214100040744c1c03141c02506480b051020000d02d04001c0c910310310300f594040303659116810715007803d001852604448003d110f0050801514100c3d01d1030310302504501640c85081c20a441000b210002c0001c10303004c540c84c640d40180100002c0c00c1640b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 521143165 1250 521141915 521141923
    0x9170115030f02101707050a020111040608011a0708070212012a1715060a21140108151b090d0b0a0e120a050f0403060c0f080a0207020306010e061f02 66
    0x8410b034000c10381c104481d103000d403042c2e02c88081702c82c40300700c440b03415203038220200d800760311a041803421550f944a80c1090386c4181d100400c0200555601d801255052018103100850381c08840d00e1401800c2002c0000100c10500b0b41d03400c1034040f2100c21071580340c0010a8054a400070610b031038422040c55000e1204070702c08480034268226507034011a8103100c0d40000e007406040d40e000007800c0b1010341101403840c1c4000100040d203407a01c2d180d00b100c4502d48406200f90035101400d01d0325a11100701d0036140400312440c5004282c400000d0500143c103440e40208040c011b8201c03484442044c6404408050300340271140640c00190084800104a05202904407425900880f4050801c3e60050444c2070016505009543c1d010140c0e240959140c070030f940b5030b40068101d10001406002c008080b814a10038040080f106490b0001d1940b042e003002814844010300c60f0708524818009100503850010380d5906440c42e2070071044d20380d1039110010b01047d950102d40e001d061451b800505201768041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 521144415 1250 521143165 521143193
    0x5090423010c050d09080405030303041103010f061d04050c0d11100509010801270c0c0506071d0904022b03090501140906070609080a030c0806040501060917011503 72
    0x3142240e24105011440381c01c0e1541981100b002503003e0002e4860102c1d40d40c0408031701482a140103280c82da40300082402d5420487d81901e00c10784100c00c40185040078040c400c1511800350040000509103015040410100c0070540900c07805600050f0810808000c4c030754030048000e182c51011079142c03070110102070110707041500030866180d09404480c010806c2e5000045c0503100d046c120ba00b0132080a00d040c400c0c905485207003e08452040c42900c00d4440d0658101c5551b036044815030042c10003d16220024001000300030511241038104416651350084440703040b0355510090b2124000142e030041c4400b07129112242071b112812001303060300f000003403840c443c3c3c58280c0c1a6a075003006503503042c8201c0c03000e0100c0904200c103500b24a003410042160354860b010000791244c080d100c002d20f642040c0c862002280d0303038030450320501e60000d0180703501c108100d078140007560503c10b004010f6138841c4509000003e400c83c002100e0310080d00841c10500200182001040d541c0c100074002604030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 521145665 1250 521144415 521144453
    0xc03060c07170a0c020603090712150506010c02150a0c0c0f0602070806040302060402040e0a05010614330a05070f150c02031920100b0301060f0f030206090604050904 73
    0x10b400325201c0c0d410b0010950310b10710b0481d110440c0100031502407005580c4002e107140098080e00d0000304880080d03001031911107001c3c0340003810703c5a94540c1c00d021540f000d04020f050018804510f801030380d880c800c1028560300904680d40340c4603d18420390703030000d00c524010072100c0306e0607011503e003051500482c01c072565582210701d956514182951a00800e03200600160080da002501504240e007106600d203403110101e51041c500c580310a400c6480030340103840e007590301142082e007074a025a18490380d4a240d44407d8000304201c00121005800c200d004101c05602003243c000c0c242c0224152806180c12004268001070685001c2c130150a81c95a4111050b1500d030001015510000503034080b0203105510914400710390303d060b0390440700308010030f00b2204141c80c5006200014030111083c1910b612000ca001c0707400000301800c2d25140c1c0c00110100980b084200040f40d01360b610081120740603100140d4943c10400803512501c90344d00a241c1102e000e10034081000581071940130b1070a01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 521146915 1250 521145665 521145683
    0x30a1b080303131704120605060607020916080615071106070f030c17030903070212011d0c03060f1e070e0a080a0201030b0a0f0303030e07050d05060703061d04140c03060c07 76
    0x802d0205000d6030141d526403020031031b00100014215400140c2184004102900704180381e800941d004c08200c940d007641d204100d07200491142c101c20f1160f0048421203540d460305c4007a00116a1714081d250340070701000084000701e0b1441e10b0380022103001c0c98003c0e04110360300206007406403180c02d4000086984840041407400b02040c107030156405680b0101c080c0d031500e0302035001c2110ba000712142c5000e80b5507903200768007248a1481c00829001040801a05000c1a0142090b0074100d0061280c8090514541081007440d000c40320501a003c482286807a55110320318202c40001c10050387c980c10051100003c030f82001c0001d541c15429100344c0e024032152206006112804050741300b15064210009010b02c0002c2c0a81c000000110b4103d04540406a886000500a090303032041a0f88a80151080c0300c8650f0b81801a20058242116a90000300400014070000c48005001400f0400107042e02d04940c0c9003171100c10080e120042c204e6680c1d0402481078002c99011490032648211 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 521148165 1250 521146915 521146943
    0xf0a08070206040812040c0e01080c0f0607031e0e0306041401181203020706022808090601050307062106080f0f010603080703140d1e0b03010506030a1b08030313 71
    0x4400140da5210f5644840c0982c140302c181111180d14601c042c0080314a001504004a00c1111002c403140c002c0078980e00610301014004244500d01c0e14181c2d5450051008100d9240070a070040d04103850300818240d0b0300c0031190383d400103d9011244504840c2d02d4001c030b00c00d00c024440c00c0d83c40c0700c09001b50080204040040d40e00c881414015420000304140c0510390100c00c114001d6025102090082c000940307018035500160242160641c00d100e2070041d022000004154414003c035449184ca01c01008103504290001c0d03520583c600c1084204085c40003c0c10071084c0c908080c1c030b40140408014030840d502c3d141c460303448070002d0120700c80621a840940d05106814010041102d03002035880340307018502d480c00ca82c0c0030202c540c400f10b089010030255400007070300d125682144045200c5000c000c40c262115405403a00b101415110344e040006111407503401140c0f003503406910049500541d00118081440b5032590340c055a0a80804010040a81b0031140350340c110510070166805540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 521149415 1250 521148165 521148167
    0x3150c080601050a0804420b011407060207021f030c0807030924150906140d0201080a0b01020f0106120204060e070206070507060618020d0f0b0609240f0a0807 70
    0x100400303204d8400103058402141c040f4a03200f81031300311250008460200c044044065802c0c682105003010101e00070f1018115401c1d000e407090b860101004d282002c1d501c0303c0c810708024103004455014100d2540002c004046668500e880105c41210880c0940d240380107032000740043c0012100800401d80101c0007a824038070a10801c060658068078100d400800545116000566040e5000c14503685102c05030758941107003c81d0009201c58600803507014280648001c10550140300f0b94005c0a00c556171000507132700701102c69402204550000341103c41e001c0101d00d0000d6101c0c1c12402d951914801040804900d161405014025103041c08030541c2d54121200c0140c041780e4010068100f00c01040090f8404c50041407180d00403c0e010400585480140c003800e0100641c8590541d40001c40500911450141d01000101d807481001070005c000003051007442001c4025100e5600d41640e1010712105407005120b00720401582511550a8601c1442c294002044403011590140c0007454032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 521150665 1250 521149415 521149417
    0x30306090106020f0d030e120c030d0605011e050d110a09211a0703020d05010e0103061406130902150c1e0604030e2b0302030d0b0603010509060d020a03150c08060105 73
    0x3d04c2c0198002c001140c408402180117103008607045845016002440040c0c803003900203403420850803809945c2d0707051501c0c0316804440841d40503505016030701e100d201402c002074940d040b2012041c203101e9510410200340d0001042d44100c04088108c02250b02e10740103600c05003000c15503a000120440c0c182411212911454801c04010100e4070003810040c20907150500f465044000703400c025040c0140d1110384000c0c0c440913000320000c94400e000410074030129000e0120103a03040303c0c4000b91428800f0101c0c0040c4407056035441c055407503006210840d00e88611002e07002a152000d1512458030f030b034505450300c44d604c003200c00000c6c580c0316010940310003241c600c1c0a035a141c2c4070300c402000c540080c040750410460842c440c0c500c1a081c060200818500c0032150b1034800d41c061540d4662400c0450304580000ba1030034010a41840140160f0319000c129030780110086910f000307116014400038544145a420041c0b04d40c0d403a01c101c0d00c014129801484607006a40c0b0317401119620b10380110b840e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 521151915 1250 521150665 521150683
    0x61107090f0b12010501090f1104050d02120f010b0108072c06040503030c01200c071a04030506100603201e0708180a0e0708040f030e19180204030c0e07050405090903030609010602 79
    0x80490400080000d84cc01d000308c1424030f1b01c080d0600710544038070000e80d8244900106802040d0351991521511517038403c0940394400494100305541e202c0c118001019050071050610f1300d0b900e8200f00d0300c5555904d5054500030400142101c4c1d4401100714400e01a042c8640705501c1d103000c59030b403400841d61440c1501c800310f08400c011f218040c80c1080104002020b40b007003600c50201000007002060040c040c6500c1a0380000e503440165142040050403643c3d400060400e843c02d641c0c10b1400c1c040780c20100c43d09401503220000a800d05c08603030002910500c0c02c0280900380c00150010725446120340303002404400c452050045a0300d502c1c036120400125403180000712030000190010384284d408078082402464580032040364180420042d43d01c250704142d030400420010004071200900c20b4a00c00b60340c241c198140784c596619000742c0201d601680360102100c0d400645e445104009070b80042000401c01106803e00142241c1c596006840580c0958289000440e07018000622410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 521153165 1250 521151915 521151941
    0x501050411070602030c1b060f0c210903190f0f0503010f06080405070302100324060507080d0f02030a060501170f011406090909010510061107090f0b12010501090f 72
    0x407900030943c0d900f80c001d40c0000c1150341158000c0c000503090318110f154400c40091060020046403c001d61811190391004144a101700c05c2048801c5a07210103a1084904a6100340c2c414020f40390303c1d060f98214040d03190944082c200d00e8204644d825800502000320b0242500d8402000720220130445280c40240103000500e062450b0421903e4440e1071081d9109018400703803510f032070b10b80d03001500da080d90311440c03c0001c5e03c504141b0046009907240c0d80700503091302e600098051070700a000d4807038010f609016107111008110101c15200382d070005603600405150456481c580301c560580244182c0c001e450024400d015001c64195140c030203180100103030391115400c0d030320707003107414101d004440c8070107070030120078828518242c0711440741d1402485140c001042d03d10707041d0b090103013080b8545d20107001c20051010796001d5040116285080c0d803146031000c20300d038075000c802030058504d45801395003140f406540403405c26010350155040e240402400c0c401000d450007120180e03800121098 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 521154415 1250 521153165 521153167
    0x51b0105211008060405070e15030a060b120115090506030a050d0c1a0613020a05070c0e09010c020318010e151308210f032214120a020a121e050d0501050411 69
    0x40000c019403c1c6149c0e0050b01102400004042240402c0c140f07400c0c40c0c01101c290341c481030102140d240c80920503030244103890003080a409201c088407124520b07446100c044a07178503400308256031010300a00ea44a500401154038541e01c42c2070092240d0350340d2000362442c48810400d5607030003603001d4140d409808014a0fa03002804551101780095011308403c4090000230041440016840e4002c1d0f0014031903010510140e10b030400c840781c00e64003020110003c5410070404004004c2c035070361981c1d4070040286040700b24980e032000481c2810f1400c11f004803034407e020480c134520040a088010555a240d4213551102c04045903480160070801203c280b011414070250400d901c030000503640c00354203000103240f42000762420300b070340500a180c00e4900000c0c1e0315501016038130400c403011031078902170354952a028174400029168940d039030000308a0503035402c0c011941407040c6998210a4070007203a070010071030180d20103007003a0300c4a03800b0040c090401000183c03074506842806402d10b640351143d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 521155665 1250 521154415 521154419
    0x3010311010e060c0f06010807060813080d09150207060b040e031e0904050108070906060525050c03030a020a03022b110a051b01030513051b010521100806040507 71
    0x566030a02040941604544107210300000c1603805c20140f03103608a544003400c020350529003401c6c20011540c0001c0d0500000b0f80c00d004002d034004d840300d444242c00010080e00c4c0c080d424062405040f00b00c80182040f42042d000e40c0902d54550300503e0510721803101040000c0884c403d21061f07a10f50031400040b604140078511100280042201c1350010342142285480007800004040300c03803c0e080f006071503000c404140b1603034440e03208000141c0080d051203030900c00540c42490750101c0c2090b0004414100000550030420300b00125010020020141d9841d03141c80d190081d943c1c01405001d030010b2113850315011040908041241d9021b52032804602c0c00b517101001030f103820300d44000408007442548010710200701c0510204a00e164007009003407601c40900e0005064801c090b004101442d1a0050716001550014034041550f5031020311020717005100e00160303001c0c094819091400000101c60018a0001c0c2501d41d00c90795020000600303403501e03250701c03d0751040c0881300101958020401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 521156915 1250 521155665 521155667
    0x14030a05070513141609090b060706180c090f0b1c0602071b0909140d0e04051003060204030501020301030204051b030406180614070807020109171602180a0506060301031101 76
    0x22001e51481e400c00b020402c4580f524149403134510440303148805c0403000449182060780120301800030583c85200340510326480c030004c1c0d085e2044403001000309580c0c4252400c02d818040b824a101078100385100d00c120313920350040000e1700c03510200a298514083c0711a400c1d1400125a5004820040c0342203824455991594001d6105a005070b518500e8641c08844520718410300390302a10350039402183e07011843c030305000903540d80c1100c60500d4210011035120250300c844c204c54500300440740072a09840300405420b50a850780c0002e00f485000280c00700a01005400960480c1e02c290f40c03c0129a6400340091094001c0c02d00c8221648010404038001c100c0e03981000807080c0c0140520124010103030f903a030040765000561820303841d14450401a0b103541080280380d020809000a00c0040c1696640909900840c204c910361141e0205407031031240001c1200860040e40644600c1c2303030158100b061a500303441211002c500a0800d0001407070b0f42460403c0d0703070481e523000710780d040c4014036000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 521158165 1250 521156915 521156929
    0xe01090c051c020303190e010c08030712020910200705150c120d0e0f070f030b100b071407050609090609090f010c090501090506030709150e0a030c14030a050705 71
    0x20181d95402c150600702000740c1d0307042c1300915060301c8240352090b004068540113004080001d8846050280011075840411858811682d101c00d1918041501e402825202402400384180064005076090006074449410482030340d46d90345002c1d214a540004002c0e020f03541d001c540520361304030b150b804115041c60069406045141164401d5401c0d07180d0420f104413152b00801f000d40c641075100c1b8256038010a080c080306401c0a502d03006000000d04022550014000c1c620004041812032000a0020390b840180080500072070a0125962641e03801c26240c00c078070340102d07016203020b0b800e00050945400c0040703803800340307000d0007540c46540e400c0d040014400c0c0062003070100f40a000541010080c00707106480d00c040c1182c65640d10303e41000001000c000003504024007400041040c0040550031071001d604980c11820113400c0c001d40d0590484080520380340d490b0b04004404004410412203248600568030021116041810030204241d030340c051451014180390011f001c2403003d410000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 521159415 1250 521158165 521158189
    0x3020715021911040c0c02091006021f1808030f090703020307060f020a230c0102010902060d090c09020c060106030b030123131b091506020d1809020c0601090e01090c05 74
    0x104211014883d2000c903007690882c400ca00002245001c1d1602103140105c1c0303207034002101c0540d01203101e043c2480a136444401e03444003854040302000482d1040325a07004820b002141c0b07010740c01101c3c0580f4018003290030640700030410294040008290b40400034102007141e03001402041d00c1c41c0b401c0b20640b251070380d0300740360011800703600d032500c000c203032020014800c9121880b04140c409001411081c1010707201045a411039060504980c0965100b000340c0b2290310001c6000108c0c00c2c014540160310002550100e01214004600d25403213903c04100503040746c00c60b4030140a026501000c15088494900300d042c401111303500152101c0c2e0084140c668440d0341c601c160304d42c0d500f1544683d640c048001a10402142c806035050060369450f0191418005000c0a00c1001c141880d401030b4964500c03030200010440e180000e2003003407800039420001805c1d980c50840d0340b00710b41014503880d01c00034040c1446642c1007420741c0303c03064414421180f44641202d80500d006041c81c0030050941048 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 521160665 1250 521159415 521159423
    0xd120c050c010e0f060c040609090f020c1504020306060d031e0e0301020d06030203160b04140105090901080c21030906030c07120f0806031914010f05010f03030207150219 75
    0x140480c5440309024443e44040350460802041c0c602d0707140010314a00740f0014030190803520f0600c020444c2c250483c20701000e90b0311006000c10902040800880207010703240c3c510300d070f61084041540c0205400d12a00707000da4003e905841c8903607500c4003440a9480402401070010318002ca006001400042800844550700d151081070310b80c201000a080e07070015007107003514036541d510410441c81c2c00c1044240b603000c0c0c2810901081c0ca0300c030281c42140200d10980c6084c4a20744a100c440383c1c403940464401c3d4400800e4400c80e940c49403002592484002003480c09880c880800b0f00040d150b22000400ba14403c0c0000c5151905040a005103604050004420b2a8040c8540000580701252981911051380e680c0c802e48520a0310041c442140900400c0c0680c006580c2c491132454035288182c2031a800c0f8a014242480d502e451600406c01c510304448103528010010a49030035240f621000c0324040d030b0895481a8640921035030702400480e114025901580301c0010b00b14202c0070302d01c1c0f000c0c06 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 521161915 1250 521160665 521160667
    0x317030a0e0708030a03150311010c050a0b010e04030f02010b0a0501030c0e090405030c0d0504080c100c050109080d0b01080f01031407031b05010f02010212010306110d0207060e07080d120c05 84
    0x2104107940ca00400b0360807094040e080400d03c0f00f281c0d58148501c0000b180340305a10381031280f8685603c9402ca100010590410681c00891f10600c0410030003000d0542d4032070551109981c0d1031000c6070740b05900751030850010b0f1001e41400d1006205001d040350040c002007507014200d16020065004000d0050703d10244100c250b4031503500d6a5880c1d665101c1d60180d0065541d078801c80840341c3c2403d806012140c2840340c140b0090100150004001d040c0342c0c1d042d60340c51890348495100751240c00c2a0300009105608141c122410481a200500025414820284145403481005449184080fa090b502c049540301c010070100344c02407043c040b8540c01c8001d0758040c0381c4a0710750a9045100d81010400c6a40d040303010401c3e564000301c079901e0079645100844c140700c00e030254104c0071601844007070300315511569120f0101403844220b88070b138540c40c00d00319941e46252901c0d0002c0c020b0081250030340c2c01740000008422a01180035864903e10755148440c42d000d910946000308903642543d420884 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 521163165 1250 521161915 521161931
    0x2010e0a30021002030a0b060a1d0d021f0324150306030b07230403150e030406080c031e0c090a06030b01021f0b0a0f080f070317030a 59
    0x220038018000d859006008032540510003002401c10301c07202481c90070306400da852105082950206024100c089241009641c0307485442008001d403262441c10b0f80e1020001036690f0a013500316140c030481000c00440d40c54104014410000c0500b2405c0010b9001030540c892040821105140c0600340b040d0750070b0002d03c80440301d52544d0541c60940088100e203204060030f00c00280074150120b06c00e425842c05111450440d541c2c6024100050701c02c409020501400310104a01d66401d034400e081c0031520142c403907079070b030a0848040302c02d090540030241c40c18250708200c060220403201503503890740b20200c0c00d07110315585902c50783c0000d106070340403101d00c0f104400b019801c580c0f56025003000440640c455031040100100040c06601020030b06140c05840e20301c91345c0109041c2088141e0703d000342c003200d82480107407000c5d044803c102580560800004a221040d0b6003c1c082910121402c50700074412060000b035685105000142c4000c0c0a600100240e00151b0001d5900c400085004a2112 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 521164415 1250 521163165 521163191
    0x30d0e03101d070506131e080f031312020d030c0609050a0b06030c042c010e0106121401060f03060509030705100b13090b0a051b07030f0f18150201 65
    0x160b8410181aa516104001c0a1001c0800c000601c05401c08460b203514008040e0001d040c805158460324080030050380b6014200d002a00801e401000901e003603a200418100000c0e48960040c7c4006100c1580b03c1c40c0032440d01000c00303100d008039601604080c011700140e2020754024504c840d040380e001d9240d02400c40042c1080c03005011a41c8900e4058040e41030201c01c043c01c003d0404200ca00851604012143c000c140d01100f28564140340300b1501e007207030289071a07405000d040086002c84d42c03c000c000112400b1509404039941e000b6140c0c2c8000b022000c80050130f072072040c411402000f08800090010402603400036401c690410212498a40c8940c4d07140d041c601380d4009141c010780d581a0108141c20041d0002559550852007080450015074074001c580102901d0b4500b081c0d030760400501284140242c0340d610a80d04a01c1a4541c9036518004202403050058800022901c0a4010081e030242405040f4410851400c0e4481800c200c2038001c0b4204030744001c0115034907030034a10095 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 521165665 1250 521164415 521164421
    0xd140a03180f1511031b0c010f09050601030209060904030f031d011803080a0212010e060a1e061205060d17090d08190e131a09131709030d0e0310 64
    0x840c070032034800620798107010038031044440c2100142c0135240c1c10000c21155103150300441c0015840146c40325210081e007455140100f00c0060140e01140c039080c2500706100d400900d0504803072080390314400d00d070b032088140000744000b601d005010419900d014040c0c0e0b4081c1d0028007141401c1c150712020b0f01800c00ca9a82074400068001e205400304840c5141803661103006030343e1260501c2d10a615000115164284148052040340103060b90200031030425640d840452004101e4400700030001c40c610615a03800c0c0403c0e12511020031214048244d040c049401002c2c45101e00624a100d4850340e6281c018103841e00044144410700100090011581c5000391203144d00d000d14640e039103c9000b10441044e140d411003400051129420100100307642c0d410040303460f880b4881000c50301041203003205130403010003400c240e48094900200010032000e0103155a0482c05001c81c0840e41040c9502800719100f10b51032240c040d04502c90396a04580207050303144228901030125403c1c420407821000031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 521166915 1250 521165665 521165693
    0x1030f0f0b1501110c0604050108190507050406080f04020d020f01121d0c301204381911030c010b03251802070210030501080d140a0318 60
    0x41401c88004100b02542d01415590307003580d00c08010510340e0b00da03800044042c0601d00ca01c0f4100180b407000070b940740700000340281095a0b8884207004070305140350040c0403604140103600001d203400c0001001124015483d500403500a401c02514006035024040e06940750620b0b541401400345510781e058499200d0f00c00a541d0305940c87c11000701440c169424629400002403084000b040e11104000040241c2c10051100c81880780d19015034003e440c0c10b0141c95080142903e001060000f110308078540342400498640151144000301401c072880c0f01444817042da4200701c024080051145800c014002d0043c03070342c0c00d124902500004a5901c1e40d0701c00070313801d140c59440d0384170748000f41010460035000303100490700500e0b4542d10740d00d010b1aa02c900c0c81340f0242c88a103d65681180c0d402c90b41203810702c9401410b03020802e481400c2c0035007d400c0a07c6410380901c21541003040c030a204107400e01c00c07504a0620b2500c2c140340e295046001d4488a405a15688044420740b4001440c080b44005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 521168165 1250 521166915 521166931
    0xc0f0c070e010501110102180d02031005130c0b071a09011413050f150c1c090309050a05030d05090f0307050d050a0501141905090c12060105090901021201030f0f0b 72
    0x1002c1d070400000404546044906070340c603038014044030f01449102c0c07000c8640008140c0e107071034000205000185c0342040030940301e000d880c60130041c4a04181e82202c10103401c0d0140c00d0040b511991220480040e104200c406400714040040e030307400c0700c1c10711480349400146410021440719a02c0d81c21b4885c144055443c480c2001614940c0410020f0074846500c8002c2c115020706554508410354440d03281004251013600d6100043c81a08503603c030301e020342020514103003045000d00e1460041c0c0010024091a48a031015081c0090a442d00250403245208c056542908107841c0c003043c80403280c419040254103008514002c9120380712021a00e070001e0003140200200096400c04a08540d40c1282c00c4058034000000c100c444110203c3d4460324030002800015641d40340c030348090800c202030104a0740880d510301e400022000c0010800d044c0c1d08200c90030412901d0f6150713064200c0c8506038080481c003d840d0010000710784003210090106c0c1c02240004000c00043c0c0d1240245041101c48034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 521169415 1250 521168165 521168189
    0x2a031611010c030915062904150e010e0603010b070206130b120f070806090105060a0905130903080c07020a031704030203060703020301030b090c091801180305040302010206070311030c0f0c07 84
    0xa000d2000c09500070f290b01700e003000200401402c00200c2480c40b1001420f000440341c5c241c0000041560a40480e8010f00d05030500080ea01c02c0d48000404003140301381001d0009803400651001341c58440704aa04a41906480e5450120540e0074401c460304102d0030361400b00b0581100181c51100c00380113280309152040a00c5007440c0c0090700003203025020b40710604104800d020083d483e1182d80300d042c1507810845400c3d031108c000d21011a085101344c1c20544e007144074007907c503105d54415009004070034440c2d200c08001e41d40351a0241030720700a80310061352240402e0010000306020104818280f01c3d108401c1e882d140c2c07a81c010038541403080d542900000d600000403c144001e04500380d400c24a441c000d0445400440b00242001c0c501800c02007000c8401c0407841e100d82402d5000e0100070300b820b4005048440641400f13842034105100c26405401040000380c11a88244a12000e0ba00c401c4030035070958980d00b110b0f8100303400c64440040c803170340c0400800c80354241c00c208000c000e00101e002c00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 521170665 1250 521169415 521169431
    0xb030f070914100506030411061306020706141812030c01050408090f030f0c01030f0902090109050f0c04060903080d020706050a0e330402190306052a031611010c03 72
    0x2500030480001c02c420040c0783c00c0344041c412540d842040782d40050300007001e03810300582c040006000d03105d00100d44000500d4800c00042c200e03000300c0e5200403034400d52948045001c80e11600061072040c000e06503c10a42220055110302e460300c03e025959402e40100c0c2d08121a901c0b565084500a035029685020040b03410901c6117040480900388440640c0074010a171081c02e00240d071a01965505410702d9200c0d01100030410301c9900148110360001d110706c40559541d0400001400c064903000020541000020201d0f60041700b02c0e4200c03055035681c600d8507451612110700a80104c9010502141c082040002049044c002c20780904445600060003000206590b0b1820040700c0c003034201c4000900c026000b10f441102c104080316000005000e2a40d203d200040004540e0000c1251000c074031400403007442401ea100030f105400003040748a4584458000900e500ca41c0b0201d50411241040050308c0c03080c2129401020718428241440480344880307629080d100b0b500c030369000003030b40c800710 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 521171915 1250 521170665 521170691
    0x140708010c03020a120f0e0714030d0201090f2a06050c060a05061507020a0e070c0605090a150b030c10122708160203150403020f1501090b030f0709 65
    0x5641c2101c80030307003011440c200303072041d025003a9141c02c1c900c072946658070300d20780141030310540040050300300e61402d4506181e2221101c03050f0660a04150b4064403c4800750590f5600511032254605e40006214415120640e14100070144103c1240740680f030b017200843d4815006902c060140040d40ca4040e190403100c50ba1925144004240c40041820081404100d4451040300c403d80200f2440450b562007180c00030a5080390140d101c481a00b20480410004941c0503620000181c03203410240065122541c0c000d07560f016040340984030103140d000d00702080005500903400004090103807882c0c0c0628100003542c00520740280808140303402c0400001c103005124000300c074821002410003000b5610020005824200300042100c0400074030340c0c61010000300741030807040e4000c0c101d03410700d100c017460f032814028107940840240c82a01a403582001e80440d041880a0f00040d00ca100703a8a06203442c0f0240c0681e100050b01030040d807040c026442c4081c40f120028106841021420781c1d80300360 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 521173165 1250 521171915 521171921
    0x9090709090f031706130207080405150903100903120221040b0106020d020319030e07210b010e25170109060f060507030804030c15021c1d060408130314070801 70
    0x1115544e080c80304020f513076035a4404243c40e2685401c00140c87d4404c2e81380ca0003482c4100c0d00f01950080c4030b814603843c0b1296140080c1100300c410f5041e5017582c10b01b01e208600307607592004000c0c04185940b5400f480342049902901100403603400150503074900c280e07540c0700c0d00c40956040c0c1d400c190060050000030b80421044440400340d00c025483c1801d0359078041c0111318519580010940c44107007640d41818100081c03c0900070a0070242000c00e007450090041081c0d050048400080c40d0000152540150070220b200d160420a1b81d00d90750710b15240c103d0714194034a0207000740300041c26001689821000094064a1101c00024040d070034805409100d801aa00403030811004100c5e070800658801c604c1508983d160030284803680881c50024000307800b0002c1011554404540d03030a803090a801c44441c2911b24070810030419902506406500118221500007940034801080c0040c0d80c0100810a00c04a403100400107505c0790740f0840000c4039517018444035070062409115600303083c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 521174415 1250 521173165 521173187
    0xa0b190906021203010312180b0403020411070f0219170a06050606040f0b0a0c06090605070807090b090906030c040203090f0c010306270603151e090f0209090709090f03 74
    0x400180400f11a904071007543d0320050100801c0d44146288174420346000340b0f1090105090706d49043c03007254036030040c0d00c0c081d040fa10050384224100b1559004881459040310700c1240c02c1480200c0344c180980901003000d040c1e1844058111190b0000900c102105c00d004140040079405000c0341c241c6800c04800356007001e05818400c02003003008100000d81d070f002e184211041c4e00c403207a0f212015013605480700080401c0140000e810810000200500b5130b0205104052548402010380c035640e00072540e00c41180130300c10516400b04030040281c50f0040346158000030007001c441402c0c0d80c02d00481d00380e800a48a107000b45d40440082c0d03405d03150a001d040c45083c802e00c2c0802c091031030301d0012803000100061901c0940c4250443d0807501e07049130020809590800d88d02e82c0582c0700304107044010102c2d0383c2950100040840e182071110420700911040a4200620800841c151f40800108140140501000c1c0c0325801d00042c04030a1409603151490155500d01e20f609600d06001e000480c20b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 521175665 1250 521174415 521174417
    0xb040506040506060702190f0321140409090f0206210708040309090c020313180c03060f031b15050403030f111f020f03010b090301060e0f060904020a0b190906 70
    0x201d400c0150f1030b00e480e81504c82c041d4044407000e010301d00241c18010020002c2c0c009164003000000c010061100c0c1e11090004541911440a03c8105040f411104183c0082c0d180104907420041004142c6c100e0b000100914080c1400708140300880e4005591644080d620b07800e1a8000c250041d06811680c42c030a41c81403d905020201c2d1074155002845084c40d400354040b040d603a01000302c0c2107442003040e00c0003655800080480d0a0322200e0f125890311842120340368440c10596030710441c078030a00400b8112400c11444424071380c155500d40740046140703068507125102440002444800501450b429a180b64a55595079801d5060040401c0300c603e6808007440560390351002e64140c0028112060024034482416200c50a00460040c0c411b40f0540c00e800d02c0d0120000c940b07c8446030060101c2c4504038000c02075651340e0754101c48103907c1245c28000030b4041500282c22420404400e0ba800380c4010f003e020760507203403105405250440c50703408400400079902c941000e600300307000c0009040320b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 521176915 1250 521175665 521175671
    0x60c0d060b130f082e09060c030e19050a080f1303061e0504020609100302092701060f050d0b01120609020d06080f030f130806090a2f0d0f150b04050604 67
    0x24044106080444a030005e201d4900c156243c0e0580d18081c0d030124808991002d8184100100300400501804203220f0140d0180100e03070030703000d007209125400e034800c0398404050242d640c1e00d500c4e126100d400143d0408462082003026517102d80c03a00300c011010714424000001e10034140100b00d44103143d070085034407100e490102440090f80e00d01c070070b60300100343c111000360007540d4482d4220083e0103102425500300e04140e01e00b0041d4076804440010600c01c500c0002402d07a07850381e0442c1c00c081c44000540108004100700304603400960000508420181844103030324880360001411a11182e20291900d81e000c2034107100903201e800350b180245440b07002013404480d80000705440784240c40003402110300014889504004000d080c10090080d04240c810303910745205040d403106425001160360401d0440309510f1208000001740860b4001c607200340781c444403203040c020250310104040d606020381c0d92400001596000150351a00a211000300340c0715098402e04c0240d0f05c010382500e01c1542 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 521178165 1250 521176915 521176933
    0x1003051005040c0306330e06040207031704080702210d0e03030d02130312020a02270408090117090f1e060703091509080310120203060c0d060b130f08 66
    0x5003294140306a80e0480000205040b00174541d2040744158000c44456107401c01b410340f407843c6403001580884441c500341d00700360382d240010802240f060300c10080c0403030802d9503162140110030080903032140c070520038686094515000a02590100e10710422200104074a06840c0f20b014452201e5603801400c06451b101b24000000f1344900442e030715810450b030f011800041d0f440e000c0784d0080c019900300825141d80039071140300030348411807490306034041c01031a0061600301c8074001c210101c561500f88148600d0b1a00e81d603010081e4003500c01141008403000360483c607580382c07080c4103014100c0c0000500030800c181140c2400d000344140c44050300341564229403034120000c07903040d40c442898900001d4407002c40ca40200c03141b2881c031a0b601c10703628001c42c80c0d00f007120748801140a110071140d1241d40c81d42d16043c1c0c04031019003a070025015080640031502044140c1c01402c0f4001c154500410101d40b40c0d07441d010300c1c0d0040941c1039090490340c8000c02001c400400103d01070300e102005428049 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 521179415 1250 521178165 521178173
    0x50306070c1401021c0c080106140301060c02060720191a030a1104080127150c0905040c120c0305070203180102150403180602030c1905010b09100305100504 69
    0x2580140002d4141d115080d005107020400307504550b41101c0c05582c0d0541c000400e070f161402010352800c0d05005c50050800414154020489810b2084108501e5843c60b07003400b00480701d03d9003402c004c9800c00c100303001d041e00203411081030034500c8a14801803214120304c2010455011170710750f81c110030116a41c60901c00140081184900c016240b0005039494881020b05001002040030b4501100008a00818685810741200381d16000303202c100d6141225032405080c03030710300360300b0b0042c28400c0b00319071070110740410b03040300310420100e0401440741c2d640c80b0041004c3c0c87d4002c0c2c0c44d800107080382c204c0d10304803540b51060a004240b03070300c0e007008a072600c4800a942d0744241d00e01c0c910401d420b14030340603c0340e10030405984101120f901e2044a4146440c0c00b4002d8004e50030340403030101c0700340da02060f020720010941e10f00072040001130044280d03003120542040e04401c01070315255281c40050403a43c5480040030700922650b400880c0851a6040450510390003800c854030345030401041c08045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 521180665 1250 521179415 521179427
    0x130f060501080c0a26070908100c080610030b060a0c02010809010203070e190911070210080601050307030e120708190201090201050f1c0e010c2a2909030a0905030607 73
    0x700f1000d00b003180d42682c0c05e507400071200400c0304400c6610301001c1c041001c0c00780e010046504035003100044518841c220810181902c05050300540043e5003540003c94501e020b98071603030249141c2c00c0000d002c10301c0f0000300305258484500c400c045645811b1000031540d008404a1340f0044410086007582850034000f481c1c1500003550794401d40300d61500390006454074a1142c002c110000041014020201c0d0510680d000309905070310546402480c0d036074135401035208038851041650380620b10b0b03981000a030001e01410810b51282d201386031207461900c4084009009042c000c0148070b4039101080007580d44085070080c2d100c116410100741d41c0051740c021041d1100c0300e280b2032005480e0700281010020303201c0050f854080207420200d00001ca990103621181480f1400d94515600000c1c0603115000343c6240d00260343c2451100b18013001042e0354201f048104400c1103021118803404452414416009030b0b039406450300001041200f007500210346400070702040d0b01070002131400c04405400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 521181915 1250 521180665 521180677
    0xc180806040609140a1b05030d090b0c0a14010501050a05031504030302090d06150503060703182a0f080606010306080c100306080f0102040f090506031b0301020405130f060501080c 79
    0x943c3d02c1d65108800c00540504200315102d09100f100c15004143c02e00b040001c0c444e021400001d000702e2408125410041040b05903c40c0700c1e251403054038500307581100180c0c09011a5030240c00b550031404006800031000040030100280042000d5051408124040c803c03984075034801d03449108240505080e01805550154041c100117850b81c0f0030038003040611403e040c00820680ca021001f0011505210354030b810350720709078101c921030380e00c04000380c0440b16481c1e40780d030082540f1400c0f070b0001541c3c0b217000c0444020084803441640c100014100c062202c540102c0405038007036509100d500c60800100340e2006003480c045c01701a103402c1d450b0fa11a10b8490506010b40b4800c5140c054150190f00448002c064050071a9018280002c659001350080d0003007180c0c0860b03016000642000c5030042d01e000301c80050191054045515059000908408010340c041d5020b200000700b50303443c6001c40e9460a44048040380d0103405a6100301100d083e50800e0307050000307000a00c80042c2d607440544403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 521183165 1250 521181915 521181923
    0x5010b0715110706050a0504030f08270f0d1e090509040f020a05060a05090108010911030f07170103030f0e040c08010b0f040504090827030a11040b130c18080604 71
    0x18110b044841d410310038030642901603d22824482401005002907115520960003540d5860290030007031022580d00d202070307070f00001050040340740031140108408038016901d116001c0361005450080042d042603842092640460800e002d00800f448100070411906c17001c030700c0e140000d1810322001501214014101500d003105a020362011519598103140c050500100050380b01c03160040d000b8180d43c4074444c51400070b20744000008282880c0c1c0141c02e098042992114110741c1e81c9802c00080d50350085c0140b0811000e0030480c1c0c20200300215540c040c5000c0d0b61410a8200040b034003030550f101200310700703004602d0700c0760150b2107591000d00b0f01c0c10360b103581a240741d9030340c00007088041500035904850b502501e4940f0500c200204600180a102c010286a400800b030350086400c01c41241070a03940c00d40c100000a000140c1a0754001c03040c8140140002405003c0300003040c0810103a00ca50a0340316034038940500500d030066606036422a0380c0503990030280c1451040340d260074010304020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 521184415 1250 521183165 521183171
    0x709030201022413060e16090b040212010905040c0e0108030d0e0309010c1511030c180a030512070f0f0308090c0d020f153610020a0f050304091a0405010b0715 70
    0x200f00055a0020b00c5910141400c4401c40c001d920401c1048107110b102d0400003502d0803941c0c0b031270f5003054001c0d00d2280c070714200660490381c0b07404409805044024002c4683c2000160003180f46010516154040c040315130080d03840303402940d0703e40c0484240000300c2106920502050038260fa111150a001a0788415000483e010b07d101070ba010f801100340c141180c020120070026036001c0c0030054111a600100401c04940050301880041c2d25140400360064101c0c15202e5000c0069000611009c0e00c55034203102c5d401965182c50b801e00c00c0400d4100e0009414909204a4210070004204980c004030740c403d96038407a0b41e0005130304507100d0901c02d0065454140d204d2800b94090305a8000442500c56016007070000c90100851222003201e01091000503611f441490902d21910307060000590000e00000701c898581c2a005459a9030803107107032200f0400403030000110b000f07851a01c0001c0402407a0742c0c1414007000199001608885010312061119202051007900303104d141c590042000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 521185665 1250 521184415 521184451
    0xa030f03021227120106060201050417030609072f01050405071a040302040e070915091104030308150f0312120609100303050c1015140109151b0b07090302010224 71
    0x41a850600c813060381c02a0752030030358006203907501034000d10701c90342c4188025040c0032101580e10b0440e0000341ca007a03410007510000182161302030800d030740c001d0b10300a01c4c0e501d140207210040100c0c221b003041c24101c140d440e0420b2004011040180c100680148205108003d0813040071801704d010700c4c4000b912558075042c200100520038030614000d8491784105100309102c16407060f0002411b40308440785d0500d01749201c64001c180d00c081e5000c1d2585036580c18240e480d025044910550071703150803a400138030440d13403a2196800300128255459000955620707030b002c1d040c2005240000820041c003442000040010128042c0c00c0700054962608126841d204496805490009040c3c03425a50501d4045401140e40203200400e040b503040019214081c0149001105c20080740e100c1c02a0212141c6400b40c18039001d12407403290f0000002c0349440300610f03500c46a42400043d41c10700041941c80c01c09101f59641031014841d031102080e003244000c081d680c640c44603441c0082000e52280c48101e03007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 521186915 1250 521185665 521185669
    0x3061503050c0d1109040b18121827180c211504060204090f0219050c211908100312090314010f1d0307200a030f03021227 54
    0x15400340744006048840b0b01d00e041d00d09100c10b070301d044d14809880d026400f0f1400c50f4800001d48005202c0c01030806608003211902d031000107140c0f4039529072f800441050740002c0b40c00844421480c040c604442c0f242c6509041209145a10485440300d80799001407903410790946410281409200303500428a200301581c1040504241802c00784166060f8501c06202c203000719a0091702c213580525a040201c0c5c03401000a60803407186516550191b595032160b0408a4003c1002c1c1441032a001e040d40c42041d6035092a080205524403d81c05040c1c000c120404010032401d840c18003034006040000c3c05081c0f61811a13070390107a6200060914006100c0d051256225817140380c0195804001d0118000c85601500d01915502c0c2c44100c1d5149022400840038800d500a8400c200c07120b0069072500e06c0c04d460b001a0902013100308425101c28031500c1c0840d4560800c0080210700510801c400881b091400a040100421032000c0d040c0080c440200310101e82400220810164030001005603c00c0300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 521188165 1250 521186915 521186933
    0x80d02070f0803092a1203130906030c0605040302060f030c04270c090b0f030a0b10020d02060a0501030206040e0a41010605190c02150403061503050c0d 67
    0x300140058040a4018104079241c1c000d180601069000d40c0c404a8407044030700c0d0003083c03000744819400049108406142841031404000c20b08034401c2c0c0e450304020070980c8000b00c80c01c1d4000011145d690074100144080840c101e00942810700d421458149580c0000c2c0072402031001031300c0c946e00d00002142c00e0545002c110b400801120b035104062000c4d40006034100c84142010710201d508013000303203664910603540002030310700c0302040a0078400c0a162a8000303130001064140001c1d0f507a040c1342342603030300c03c101030a540c83c2540c020411011101030080c03e200018214000c100d040200500060b40c480d015070781036a40e54856002d90380d0301c654550001d4031100944401104641e401c040418000d5243c4100e4030b01e24115007490040c030340c031529190300b20912805e40002c0c000d10500908090f40344000c0c0100200d841e101c6c0e041070381900080c070440d00310000c50079038060018040003004020f0041400100300303ca1140c1c3d800c0e140d5151607440d446040300d401d1140d142d0140303141c20080014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 521189415 1250 521188165 521188177
    0x106262809020405040614070e01021905010612050a1202030304030207150e1f020f0303061f050717030a0f140103060c0909050103061d161a27040605040c080103080d02 74
    0x107205100c50b0505c0c1c104200100b0180c0e00c0c00700c480c041240012045070003452054a66441030b8010520382ca004880c1c81441000308204072400c1d500d0340c40009602003040c050749103242c02030001e0800c4110501e00a040c10031141040019508107004000c042500841c0070760403251401d600040c2d541540c50100c682003845480540e02892a030800d1184200c010140502c12115400b164080d501a44c02503a50b80000c80c0c40592010301100d800c50080d0440c0700d484940041c0d81822400e00959039940582044803030381102c103035003000c42041500c5030a07026210004d1141601040340b01500c09000f80380520501001d45155110002444504c1c42400c9160050525400030466540c4919211004d4081d803849122060342c0f40d812424210700c00b11b40340c0b1440c0110341c4000403ca160155000e0034124030004191401002c2c08840004031080345101010303054060810f4441a02804010440d20a0b0708924080c9140000343c500007a00180c0b00350640780c1005074141c41d003140480c54030181c4605 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 521190665 1250 521189415 521189419
    0x108040606091b030606020a020d020d0501060b0c24090604171902010203150603060d030e0103020f0a0f200c04091b0803070311030306100521010626280902 69
    0x4156046503e4034400101c00140c9202d50741801090b544101c100d0781c483c40b541000e903005403240c142000504e005560205600d100b200007055035540c6003038002003504503294109032604115052244180d440920290300c0904004d43c2c0ca050070700311040d9544e107400a00041640040072407101c4040650320a030b0b814130040646000380340c20007400090203900240c1e002c080c43c01c5000c0d03101ca000c1c41c1690959102d131101428a141d40001501d0440d0014000502d090515508010f41c1c940a00d03184000d20740070103662281c100c8914941c0c1c00601c100544050070303070b420140f01d0100100d0740b0302140e2900c1c50002254017050000050819031100c000b10010180607501614002808010120180c010360340240c0310340c034000386031003907407601c81c0300858505030700000010b0302410550184000c1e000e0401c00031007800b1911110156401080d00c02e0300230f000440d01e401e080d00d09140c650007241080d000f010f006c402140c00c00a800d80b2002882508104006030398800c1c00c405c16006510050a031600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 521191915 1250 521190665 521190671
    0x1e11010503090c060c1b0604080d21060b0703080f060f19080105092119050304150e01020c160806012601050106031e0e06010b030a1509020307020115080309010804060609 75
    0x1840125552043c0c040d00d02044043e8501480b1b00c81d1600c0c41c01d890444441002829140c458030303608507100148409800000310800c2c500e0b00d000e00ba02e2141d0030240c03d540e42d0f540e6035560a0305014001550081c014030340340400600708a02034940d04c1c620403140b10192002d01007012821112010042207401c202682d601c0c2400300b0aa041d0001500080c802d1025220382062510007556800d0340b052401d561030402c1d04010001c07100d84541d008551140c006c1014035241c1c0000b000b16400d44400d0f20000f01641c3d00442d08544030002484286a0280304290360451140b82c102c01c180c440e5414401c02c541c4d181e000416052415640d02d01000c1348841d10000c000301c1da162070707000d00109103403c200e18030703c50440240501029107100d0007201a0000f00100301d00e80ca0301014105640c00100303c52840d07501d80c00080480d2100021102c003030078060f070008d0784038502043d009007111010b9010202607143d549041040d80c801108035425800700b86800c11141d030311401c020025014a61000d22100c1c9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 521193165 1250 521191915 521191927
    0x90109050f0604060b060a08010e060d080a0e030115031109041b0608090706170a0b01120606080a0e0c0904060908090a0e0709091e02090a03120c1e11010503090c06 72
    0x1801041051007180304240411150150348244030447c010480f000c00481c1c0c2134030040c00410400100c50360b2111009008884203071483e074032010a81c019414040c081404900e20100502c1c083c01800b01040c0055001511289591107188184080041c1580520078030000700d030a02080c00d190107201100e88095080280d5140c8005001e201c00722400041030140c00c0c00800c40d107100d008408910600c1c0b00b00c0c403c103603e0700b000c00b800800c80e030241c490621450b1004c41d01c25440e68001d16000b40a0b903110040a480e200f20680140c0d5003e500030b0442e074120f100544421364514071030580094200d01c0004504c1c44a141959042c4202c84000d980704c00010400104040312049440c40356040f95992400307942e54030204801e44a110f4000c94600c1e1000d40b0428200d14264040d0101d007000400c2c0200b407d03582e40351084123500b6103181c400014240b44882e0700303210201030b06101c191012204195506130070f03120140c5412140d076039a03040050000c0414682541040302c010318800041039a41e40d10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 521194415 1250 521193165 521193193
    0x60f07030201060915210606060e090a0207020102030a050a110625030504020319020307031e1a0f01090e0a0b0f06030d08010f0e1905070203310e09010905 68
    0x240050400324019030a01d0790203d04d03004a0b0040e6140920807020801d03000c4d04005562202c0031800c04811603100070210800c001c11080d000d000010012503c03110303140d2000005000c80b00714010220b1004500401403100103076400803c40b102c1c03441500c1d2142d151003c5000c111010302d40c0c58480a43c40c400c1009000900ca140d20300105402d0080d02c1200c4030340342d41b65081d0142c820480c0c0103541500400000090074100a032505a034901c014207841000780c5917504c0005c481c190541e07841021404491a1040040f00c10100c07140c3d4001104140440c070704882d40440f003a03014001c101419485000112078110300300310b140b0303880394000b84040301031a141c0c08102003000100d586500c24803031340e010140030500400d403442c10385001d9600c082407039043c40c405405203000949040c0740310846440500e15442c1d144074541c058200d0354051a82d40c84080c4000814521448011041c0912004116008001c0c04820412210690701d5030360f050f80c41044c0240103100c0907101038142d02450003040078034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 521195665 1250 521194415 521194417
    0xd0213080d0f0e182206020301090506030c120705040b2b031b021e030c09100509010e2e0b040306050901050903161e08041509050103050601121a060f 66
    0x496580c3d603844510f0400c1008000003803100344105120070014602241d003d1100003c45c44c0128501c404544140003941d035240101e03071090f4440e074082c0365100c0920080c1e103018414444807000450300c82d00003500211406854a04610034036104550700d0310460b4040d00c41e02025102c081c2c0141c8940e6001c0074810ba07248808140b45812400903a1030310350300c02040316404040390b10a4010b80808241d003a10300059109001030300d002a4903100e1000b030541c080e07503610038003446000c0400d4540e0160703203000300380040320406070002c2c070b941c240ca00c0070044a10012060b044400d440030f10307140d11242105442c414100c1ca640c002d12406100010301100b481441d400907406000d401c802000b4030f03516031030826264011843c0041c00301217004102400308100c0008052016044111100d200100d03a070b425029074090703489140940361080f40c000829420107403440c01800b00703080512003842c02c140000e10081d2582007a110b015a1000000c07084030402c58801003039000039000300e645840d40280d00f00d071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 521196915 1250 521195665 521195687
    0x10c081909050301060602070603020d182f18060a03050d090503120307020304030215040509070c031b030905060a051b07051201111206040216150e120d0213080d 71
    0x204500700e0000400d418144a440105e85003903000d000910f080107002c030040e500c189194068651107419000803007103500030444071103104916142030200e603002e261404010414410f400640351003480c81c0d9503280c1e414400948854400ca4001580d1444002901ca0f4115000a45144101540c4190880c0c00c85030f10001c0d102c00314101c07595500c102085d0b1900344000c481180040c0c20902c0f0410060500d0704d41e8050900901101034240760315200400c0d0301d01c40403a480c500242d0803081032005d140d0400d000c00350102c80d002c04620813040a40b005445000c00c0d1003100d008160000c2e5941480784504240d0781442e40700d003000b04540d480e02d11403030740e00c00300d03802031910a100c02d001d0000d562005109001b09624800c94160418007141b8002000d220300824190b00a0f0b0208840e800c01c0808001c08546a841080b960120324615070001d000c8540c220320750200d9a0084104902c0110402d00303940340c021000e80c01580e900c00c42c04000c40c40e00e86a40c0a114148110903000800300d8200c900006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 521198165 1250 521196915 521196917
    0x604152907050715050403050a0b0114040b01021e070905090604170c0c01030b1804061515051603090b1209010f050606070201080403020129040c02060405031206010c0819 75
    0x40a59452044464544241c200060495118200030010140061000441d08840b801d25604217076690300c07081e050607850707807084030a070000c80010700265003104020305000700103542c10024688003400207582c0e002039006410f40c0c5200010b0f60100b07640e00700800006445025800c2c815400c1c0380144540d502c0095038101d5003200c2c48540074003050789040941d0021848039009001c0221004019001061034914494100a80380c05440d04071200440c028010740c4240c134000782c401d2281e24500c1ca80d24075600b24281d4188088001c00302c495001e4141d480707201030340c1a101c8030809249030946400000340d1054004c12800329401961012030b5000ca0b20a03103d5100031700174001742c02000b004070351044501582c040c40030b00000d03001d5480740d645a0341c0f0500c00e0000181e03844150088012000c00f203150740000f820013a0000c102c82c185802030b50035040e0329000414840c14296142500d90040c0381c20352207460340e40070019101307a11603000340a034141c100c3c0076240e03550071071040d00401142e0700040c54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 521199415 1250 521198165 521198219
    0xa08090f040c0801060c0503040f080d1107300218070e04140a05270a020a0503120f07060207150603020306060a0e15010207090e060f0a050103050705010503060415 72
    0x114441c01c0900a01100d08841e6035654402d0382080002e50b5a91a00c1e1001d03105403209100c0891480403132030348800070308040c800521042d44031190050070f01c0f115211100e1180c111140405c503c102902000052105040c04e40c8508e0481c9016440070301c1c1039000103580404502c0b28a000003500001e2203009011035660100e001d003107102880306543c003460041c400c600b81741c00003032110b48942d886940c000b8003030314118200d161866090380104054a90104c0d2641004c901901145040c40c0d0180050400b54090b011085010700f50507054003942c90030461708100060880108103941e0304441d601544040d140240300c0b090f000d21001840540001c9001c3d2007180040b40261404490171421600740340950f402c580d580940e001406040021801d056109400000c12800450b01070100f200d030142000b888940360540c5c0c0e1642d8803101520094910b4070b400010702c00714401140c1801a0307542801d101d5900c2d00d8000205008084010300348100380b0703c501021444c56401040e840001058104034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 521200665 1250 521199415 521199439
    0x30105011103040503060a0b01051603180812070303090c0f09061505090f011d1503070f0503090307020405060a0b0c010b0a05120c100e180a1802010f0e040e0a0809 72
    0x280b5924801e0340202c2d54180d00c00000070b40001010b0b007110108030010f25119092000e90348144140d0801c1d45000c03004200c20009160507980703034001400061016200922031300083c0940c4904038841d0180c05000c240c1c8660b00c15060140002c207100003070a1720104000051703540c0241704010050b034050f955091108012034040548100140c4000800c0141103d410b04400700054031a4a0302000080d204106000f031080181d644000c00304541550320144c0d5520b182c880c0b0001d101c251f1300609001441803d00c11302a410740d001066070303c80d41e810342d000a403c0d2207e034009070700100503500001c40b03e0703400103500c600e0623010b4002c0c2852400503204481c0484c2c0301d0082042800201c14842c0032940500c0442000f4a0101c00c00350b454031840c10030b130400701c0008020640d03102125004214bc622081c0610826044a1055400161154840141d8003038143d0000300f01513005001071040101c0529544001e1380e0f1035100441c8038289804690a000091602401e5900b01958241c030400d4180e80d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 521201915 1250 521200665 521200697
    0x10f050415120608031b0c09070210090804050406271a0405040c030f0b04030e01090e04060209013011040e041205091017060102010621050a05011103010501 69
    0x640d02501c000c00ca503007a46002103001120700d42d5110103222907881e1103840000e1045014002000c3c030256140614180c040210350301d901e48100d100289002d040008104501030303501145980e58604200c80100b8211700ea401d0400c0344c0e000e0368100c990311034500080090300c24241e444031452082c60300b441c00140000d040c0103004642c0e154250896055458084400d1403501d80d110950140c0b00d41c04c4809c16035103940f200303043c4150b20403045460724109003e02050607040300b00094000d10034038014410324201136507200d041001a100600c0306401051211040e070007404c0d0101d60711080405920035402145c000a21080050f507075034089403400d030101c0a065800c0040742c0c03c2d500420701044254a40d5511002001c2242c0d465501300001400b00940300c4d0790301100390825809580d030b40c1a100070398810a00c1e1191300580342506580c07600348104180c403a0b0110064a22540e61001100c1501e10b09160342010041d40c4020269464100380d40c040c510307080003541c180c13038080c0e89401c401c2414401c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 521203165 1250 521201915 521201917
    0xd060b1b0105010b1606020d060605070c08030304110409030c02031005070f08010302370b340209060112020c0d091a0906030604020d090f06050a060f1701020c07060e010f05 76
    0x10724192110402000f20000b405c5c0d002c65014500c5000b00601c0c0a582800e84030448075250800e00c005030300040c440062000c0d154405c409001110040c519600380381d5607182ca007080c1005901e000c0c0b51905091010705002e0100c000200e5000342c241c40d800003104a008004141c2148d007400818600e00407100e020740300302d6085050300e41c0640300703c41c2d80741c034900083e06410750090308079541a054085007011041001609000b4480c100300c2c1074640e0a50320050705000016100210b000000b0f0704480b5100c1622101d440d070044d01510480c1c010b459810040f21450f0351054901145030000904094030000020b40b4010003031295640c40096407190952511303085800c0e8500450603080c0001d980d03500d403000080da000300d00140010700d4006240d0b540801e489004d40142d070b41340e082c42d0011041c4072203030107219804140c0303036000c12000f030400d079a0301a104c08070701031041e00c03410841100c485140254100c0b0361144800c800c44110a0b55280004d20319000c900d409400103058491345010540110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 521204415 1250 521203165 521203169
    0xf010203040806041b09020a3b1201200a17150f041803020c04050c0c030304080903070f120624090e0f0105041209060503250201060504061e08210c030d060b1b010501 73
    0x825a071074108a14200555849054801c412b203543e98442c0c4100694000e40850f841c14001e030440380c9800360140054024103804d62410020f482d03d200f0000f400c80b1140300522003000c1102c130701d208082c51101042c001c010842800c500210342100783e9050580000740380040e69000c450600290303a80c40c0c07540d00180520018120a640144089000940b100c4e0160050031300c00f40490b4a96541c40c101c1c4101d03690258807602004070510070352001d00c42540180c40d83d0001003446254034034000c1466452344880f510540010a6403482d0048901005000800390160b400f4004e20913400c0c0341c1081e1070144400300040b0701180606000148083c05002603a208910000c140701158240749a0032101101118503c0210355840c3c1001c91300c0e03952072080074082c1120084003400140e04160512106c05c20390404a500e9024054644049003202c1050091460902026403645414003030245540545102d0940740c500741003011404800036406003603100040c0380c5e1a0003252020410300c2c03c0744c07004c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 521205665 1250 521204415 521204507
    0x50303031305160302210a02030a081b0105090c13140405030a121a0d0816050c12010902090a020a120903050910080403080c0c07090501090207020f010203040806041b09020a 76
    0x8046c2d0940409006c1540c4007165580c26943d41e20a0f50380044d00388460200100c6040c030001c80c8a000b5001e1101c80300f041c480b01c0d100200a181070041c40e45a82c2c014840da410300c110355030b0140c0200c1052507041040c1a890399404031a050a107032402544030b030009100c03a4001501c0c0603d50b0b40c107031001e0241c00b0001302d81c1c840208411080200340034440003090402c7d21500002c0120303c40c0c588007140a081c0843c041c83c094a0901003800c2000110003d8121201c400d07818405030300096502c51a005030403a20740e0340c00581e11072134081c3c25212000c18608482c101860640b029040c5504030300100303c0340000312040d00c82407007040700a4501040640e07019001400100000d09009170002c000c000350040c2c032049905042d96224568250b820076040704100d5034012500c4e0045051180060321040802d0025600f01400d01c04907a5403400018030250040100300c1e00d0a1160030402da500f0050860180c0c01c6d9a44d00d005080a0418002e80c058041071030744084014454070300302d0500001100320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 521206915 1250 521205665 521205679
    0x108010f050c071106030a14130606050a0f15230c100e030306040b060904091103060709030302030a0c1718150405031b06040e0106020d020d1704021009050303031305160302 76
    0x1500203100b95508007c010042c40380c1e55006c1a0940920321a00e60b126641003400e000b02c907075852401c6415111603521090040d00f840900348411540149a03030256580a1104154444003800c203c62038501c1040c0d601d1000a98880381c8081100b680044c0030040e1640200e4045e008142400ca0482c2c4400c0c0f1894959041440441d0180c50960001208001b000784030038202100d400000e0111121200300325201c010b007481e0702065040038040340c6e03800726040c1008a0114a146c601030341300d10a00d660502080301c11400d0b9010004094407031256150040c5002d500c4100c2090100503240e008020588240d2600ea540c40c0c04900d10003c079010303101c001d03003d00040b10100e030082441000343c03000d1650100c0c05020126200c107041c0c1429000b071a00c2e500600d00304110314006414040c42d070800c42e0800c01c0c00002a40003101681d070480d086070b07040ea0340d45840c803e242001c441136030540d0043c991502000040c00403c42a1004c1003020350702800039604503590384001c8440d0050144802500105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 521208165 1250 521206915 521206943
    0x22025104031203141906080a0804121a0c040905130c151e050a0f030212041403070b0916050117010b07150f0c03050601020d021f0b090108010f050c07 66
    0x1c0d18040c1c1c6280059942004030348003c11300500740700c440d01141d101050380351032959000280c80380e02540004200d0407000e444a80850303151099103210301d0281844c0c2e55600002e01d8100b103001440301180803448911211641001035002c00a98024032454041e40c1c2407401050724009082410201135500030303843c0610b030f49880304d000c0041d020111a5001d2103010104a02c2c0082c511041050601c421394400c0d0b1744100075003014041003a4190034004040c418000c008035000451038160300242c01800d9801c441100700305051440c410000001c200031860024000c2d0104009200d554410b600c1a4007000b441d00d0780011140340704e00110700341c144c0445100420008000c100205032040c0181210740e40076502003d90b07015039001e0f0b2018414940c0d0703490300f501110ba25100e1160056400d1011f4070051000c007100030b658543c0803c610641003400c0c5000b42c000001a07000f51800d40018026096a44c0d41d00d017800c0c0203040c035103c605c45c7c0324106400240700700300442c21a43d40c07661220320114000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 521209415 1250 521208165 521208173
    0xf0e060d03080604061e05031603080904050606071b0e01060c080301140a0b0f03070305010b0702090f0a0605150d0e011103160c08041215052202510403 67
    0x22000b034943d580165507020080345012842400c07002e01c03400582201c2d1440c0c07a2009240c50708145580710b0028070703003108061000400403000c55612000c111000300d030b02d407181d6000840510401c1c00041c9500c0c40790411010900f5603a80481c12a81c1c480100155030b80d0b140740548001c2c40f0810020710891007023006004104000c45142c80d400c50140c0090032594441e42040758079840070032010302842c1d000c010841c200f6898099540909124400301d810130070b480d40840c84040f400382800001030b25000004d00103403031a90115000300700042c81c84088040d0a9001403050388101440d64695052620550481c001402052180c0101d0f01390b02d8a159038042040240313003000788400041258514004001c05c012202410182004559442c4501d00d140744c44078901103030085c0e040c17a040c10641003121025030034a640030465000207421250254a10001d1249507004032207809440044441d4030072840c40c100420181e43c9281c4c0344090001650b2000010444400641a01e003d01040184002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 521210665 1250 521209415 521209427
    0x30303050c0c1e0606420d09060b06030f01030206030903190509040e0105070f030b0316060309121805040905031e0c0d0c02060d0b01050c12040f0e060d03 68
    0x1181031070800a00300300da00d0b0341490a000c15040b800810005100010212407400e2100540040084030401610f0040100c01c280f800600b150112825480300c0b000f41042c02550074071207036205d000703488a0381e410f440d134001f00c02451080740503201c2d0303403070003000c2885410320314200c034022158031031003800980c44c640c00c0221603800203100c1d003070a00060144100c5034000d84002c0d0901481d50f01e42c0e070340b80c05030301c0144000c4549584101000740e04040502514680101b96000c540c0728900d004110320080031302080c50305082900c062a800303802c4500103000366066201c0700380703140f240a50321190031280b4030071540103030868502030140300712a0b4200114a0107500c055003c41c49403050b00e0501201030071082d26590001c0d84090304030340008805008010500071381d11660004d040000c1e40c600302d50040395860146e0840d08054030350700c0203100807a81c05241501e0a402d0310400321003034852010464100b42e00a881040003a00958074045022440c042049200e10300c098600c041180711500c01303c9403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 521211915 1250 521210665 521210671
    0x909022106061309060510021b010f020708100c09050a0f120606030209070804030f1103030c0c16060309060614010f032c0105190915090501060e190f0e0703030305 72
    0x40402d040124800c0c0340343d010000c400403c821440003440928040c240410031620182e1601103400040102800085082c02480700d03560a01e00200d9005d003012090740f800321690003071011442017440c050341480c0e0b1500407071400421a65501082c83d84c40003803000c3d100d403034098102c2e00000c0d803005125400d4201e1401000358016140411019541d8020880b115000c4e501040012031100070442803580060210307040b0040e500d4015030f03003001c0e0245140c42e804081e01e009004180040c10320300c80f403000c12040c24000700b124011104560307541000380081140e4102220420300b00400003907020613441d60b0444030101a100d0444485840178101d008000c0c030700c104c0800351111055001c200e00408001d8607010401c100009190400408824405241c2a854400366080c003860720001000b905150071242d0102d400860384040c14900030380904965000300107064000c104100c3d80002540080c04c19114400080080ea030a600c1090165148801920034070b40c8042402c00c0001c0c440c0e40319581c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 521213165 1250 521211915 521211919
    0x9071e212a21030206071d090408040b0a120f02090f040e0a06020a050d1b0507081b191103010c0e0f011707050307201c0c06110a0909022106 62
    0x10300a81c50356404034801c0341c00d018001010b107450294408040d01005070640109581c2000c4e421041c07074102682c13000407102010b0703001c5c50001010078200400b00040d600900072543c060358680203504e10040010b04100807218403035003401c900c00b0000d4914802c884140038060084c0300d00d01c02210138040944900300d180b44051164080540102d070b914030140a4400403035840b9980d800c1800c0c0e0304001e50f241d8090b00c441c4032280d0b05c0081e00c01c0350410200c500c0213900a032020b85401410191200b004829100940f80340928010080f05107840e91112450704e00c43c80c0b46140340c02000341414201c079489502540851a400380d503074607528050442d08070303440b4140b401e01c05036a880407201740c50100941c1c87c000801c4d000b0080c002c0e625002149102d166001c01500b005106130801400d660b105003403e05c100050180e001003040c1e6104028442d0f0043c0c1000003409400c1d480600b03091a680701c4104040000d020320008940410716000700c0d1501004494140303ca010754400314144030001801041d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 521214415 1250 521213165 521213243
    0xf1e120c0a0b0103060f0609230c190203070b0c1306030f1814280803180a03080a0c0207080c06250b012c07030509071e21 54
    0x30001030751940342c1c24040e51151070003052901e4122a1501514440c2d0802c0c0031260906010310b010b040700d050300c4480003a542c00d41c00d0064807981c0c00100c4a204624240c0540f680c807404c1080110380000050612904c10b040c0000a55900158000540613010303002c0300c0d62000000030000309120b508900500d0800c0000010310410003142001d501d105000304650a10080b840509845024006603060050f418519101703140c102c0e054030b08036000700100400f08080400030403020000d403520080c2e6060303a001158150041c904010303050741c030102c0300158400d092812080c0910300c08515601100c1015000344420342602e02009541c0c0c002000f034003940d541d86441c0c081c00c0b9400300da1418141e8040d59140d1303903650500450002e000780350000b0708480a19007245070159208505002e611050500c1d000605171240480310b400c2c2041d6030f210b21041d883c11103402d803101145403c0001101d041c81400704281076501804904c2d0348484001828210001c4030200e407e01c00f0005e450040d0310051110303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 521215665 1250 521214415 521214433
    0x180311090a0e011d0d0503040231050405010902100201150504090516060903140105040807120e0301150504060e04170a050915042903070e060705030c0f1e120c 70
    0x907421a43c00105a44030004e2080b9003040c400024401d00209400c80d280c120715514098021802d80804001d6104110507000391074113001d40c0004840303224103200c80301030106007400c1c24290f02034070350000c00368450900c40a01d46200e900520401c41b0040b030909414450701d240c041004000d00c2d49803c15205406900005400091400642401b51015071240c200d55400e40c00c0c003a4861040300301010a0360714080501010410300c00942e40044d030f10018005036005000c604440542c4c0fa030192540541c200740c00c140440007210b8104090f158107031010080c46640d5404018101c0c4150742c0a000b41c2240c510f550000349400e8000c00c2858040c0c01c16615020f02e4001250b10003d03505606c500c004400302c2c0c1802049103404403440100150104589000c3d22042a5a400c0c40050491814401208000074086c6c40e11402d036144681c014094a0b180c2c80d40c4a0515201e9590001484d2103004010f00c3d1031510403800c080e000c012411000504010510b0b144601c19544454601800b9105104030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 521216915 1250 521215665 521215691
    0x7030b0f06043b03090d1a150d08090103020c1b0f090408180120010f0f051015031d010b030f2b1704140105070c03021b010e06040803030601180311090a 67
    0x155800641c807c20014050340e81c1c0e9006051803c0001e092021501c1020303040440790f596076618040c6280d000b040c83e503940c100c1140160001d102e03d5860071002c1c0600d114460310128080c0b00f9540c91401510800e10b5a1810340400c0745101c011a801410481c0600404480c41c8660594120801060600240142ca0000134052880c840e0100189680d1030b19011405542e10340142030f0a241d80c02c0c0184607500b019202c29401e45c0050050341103803141d00c2d41043d41d9610981100040c00101c1c0e8010702d003e010358014030301801c40503885c240a44141902d41004110000b0341c2c14070810f401682003101c2c142c400d141d001c521486c5191000300640c0f85103600c030801048003030701c0c0254860101d1618080724014280e0a481c0d00a0203a014800500b0402020076000301d034400d01c03002e503580900703032018070100107841250f010320383c05810940109007c61040700020046004e51000d03240c41100c842400000b50441c10700340002000480100e221418030b00742201c001e81c200144860200c2c85010b6084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 521218165 1250 521216915 521216929
    0xe0f06060c0a0b250c060e1c1116120609060f02030f04050114010503070b0c1e03070c1a04092016020f0405010609050d0507030b0f06043b0309 63
    0x401510303c042c4031018014130600040041d5410134141e400003480c01c188040140c0f03885000c0c3d402400b22602d8440720505080d090000035901540850503640e00c0c50f68090003090350003440608805032007a40c0781d00c441c2d240c101c0000402c540d44c0780c0d00741d01d01341002e0766154043c003c40d060460301940c03100d100d00000304030360001d18494011507510700306a2905060181c03d44000305070a0129031310042c01840b07542ca02280400503500780e114000c0c3d88003140d07a41d1508d4200707480c2c081000581038941c0390505000100007002d2040c0240c0005030b000d91641c40104000440c1c40b081881c03400c041004100d5402d990300314041c000404951400340180d50080075003540d0000c25440c10340d00d0007440190440c0b4107071706070f800c1f40703a0141c40401266045c0b1b8000382440c00039015280c4075100d03003115002000007c02440c0091a840000d48046050494211b085210194ac8244c460360400501910000840d045100c0341030b001e02992114541c4280314030361160005da200106400104154400c03601c2d116 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 521219415 1250 521218165 521218183
    0x80a090305152a03060d0c0e10060f030203250e18060109080a02060d0e120a0f0e010c05070e0a02040801140402030f0a0b0f060d0b1005030d03060e0f06060c 69
    0xc2c6070015142242000841d04000c1140321072060642e41e802000003242019a98481c8042e17400031950462814209404080f81c5d10120ba01d80c4a8800c0002c003c10b031014001c211489074403100f118241140040e02640811070303450300d01120000104a07406401d501d148044111030520110707505015001c035103801c40c5400300d2444082000203100d141e5034441440d00c020b000650140128049a0340014158461100300c50140c0381c8602c0c0300304d03000f00c0c10301000716103818080400d0b980392117412000d8620100310504801040e031350f2800c88115401843e60740015035200740640030890030150311050700c00e4040c00e00d01015a007884003003800346c82441003d00c80300544007002c800345402d00c105490805001c0c880522a007002402000007000c804002d0b4110349501c1890701181d9a003000301341203116800000c1c180f583c1c0042031001e61340c0c42d041003200f60780060b010755800300709030030041c1c0c10384a0703500ca1700000880c4080003907048013030300019540211300109541d2500174824603141c81c0010306 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 521220665 1250 521219415 521219443
    0x907112b05040509040b061809010b0406050a05010807030c050c0109030e0901061707050304030e0a090504051e030f030c070804030c0f080703020a0501120905191a0c07080a090305 79
    0x400c10100000004848415140d452490064605402c15000c1031382100c0260004081400c4000403841940d20094151000840c03c1c1c031030107440c40d02d000c03028081d06036684014022450418041034504010344040261881a1220074032030b10303244012001000005240c07400c00c02d082c000029000ba0a0091800490007a078810440161240c20480c5120701a8051070030700100214240e1104e40501180746d000e0401d08003c2c1e00d0b50356606003a1410068070380f82c154406006c4502007140c9003075074042030113a4000d03411941d002500310044411400d2404c40b84209905c14481c07c841080100021640014140302b01800d00c9495600e20046c3e0b0415001180d100981060030301110b500151800020000c480007803c0441c07442e0040b80d010f919038005d2074100441241005d151501c250001d00c03e10758030004843e80b21800ba554440400c0701c0f10310407981d424883ca43c040703404aa1a104a0050694000e01803902041c1e5980d1426039100c1c100b54420300c00a4000000030070b400f445581c0c000c2c401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 521221915 1250 521220665 521220703
    0x18110307030c0f060206100617040f0b040c3f03050408100c020f120d09020f03330603120307110f0304061b0308041401020c010608030c1e0a02090711 66
    0x1040c2003e070800c02c00034105132a0003c888000c0040316800751271188102c072400c28102e11504e41c7d0902441c40302041c0703000b40000700028244010407205000081c100d40b201c00007a8803007000701c6440484040b8000d050404001c80c01c10418039101040140c440041c400d0034803620300382d034030103100c0d080c0050b5111004900d80d0750600c81c0341d0160180110941c07801e040d03000d00480e9200c2c03000e914072400f4a031a03000705030f6a43c540d002c00f1515030100914008000a0440e0b030142140940302050303c01c1c65a02401512403200700d00e90424000b600c5a0055038010003030f141d07030803452028880a810040081c8104468030314620014139040c80081070700341100c0091550f0394204000501044080c0c1c3d940030300c0e104481403100c046640710320340c103400c694030090352500b0750b80320b04203a03001e030040403801d024952070040b00041c01a400001080605150400da5102d4115400b02110140d11200c0441090300070022880061500d80c0700320360700c501c403030901c160341c0300c00c03507a1152400902191404007805 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 521223021 1106 521221915 521221919
    0x50c0714010c052a19050405040807140a05060106050403080a0c020a170a0b0a06060c030f17090d12020f090d050a081201090b030118110307030c0f 65
    0x340200480304078040d002d140305542c01e190304a4400381081c2e1213044059041c240c4c00369502254503605801014905400e01000e070600408c201c80318001002490002413144030414080d082c41d00040040d0340701f614110b86000300c185c12020910200b030200300002944441180ca000c03070680b4003600303101c10901c089284989036801c0341241c52601c1e021806801c10014500c01241e02a90221201d525100340310b0044800e10300501001650700c0202e031001c0303800f49000e180801c21f5450300d010030304190000d40c10200320a031120621a0450b0314001c0280341d002c06100760003004100c0071840c16403141541451440341c15000c40c09620f2084080081c460140040040107420400c2240d80e0b00990021942c0120240188402246016001030941c00c0c140f0034a50314054016070100c8250f0142c0396034501030b060001d21589441b8002010001070000c0300b994000f4075080718002c011034 = true := by decide +kernel

theorem cover : BRFrame.Cov 521043165 521223021 := by
  have h0 := BRFrame.cov_init 521043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 521043165 ≤ n) (h2 : n < 521223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
