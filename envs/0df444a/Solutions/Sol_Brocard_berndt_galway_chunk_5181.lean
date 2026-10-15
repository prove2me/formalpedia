-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5181
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:01:04.186925+00:00
-- url     : https://prove2.me/submissions/cdc2bca1-ed5f-4144-a7b1-4758223ea05d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 931654676 ≤ n < 931834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 931655926 1250 931654676 931654681
    0x12010b1b0c0904060e0c040f0e120403021f03060519080609010902100f170a021309020f04050906010c0b0a06140103020f0a202a010c2001051e07021206 67
    0x540c0d014000f42c1050b0428000180c00b0004005107080140c034102c031a4209041c8100310781101107075400864800c0400303066031240c1c080e048042015209610010358410b40c40030001184440482004012000c10300300040d00a0362140400c07a00009001c0100d01c141c2108010400040140045039100e42c1c0c400c02000006083d074001400506903005042c1084004842c1404240c06001c51b0200102410741c0814503140c6150150003951011140d150001b810f2100095034261034000d82c0c003a442041e07045800e09040070144007104070000c0600341007040202c0e10201140c2c2c6c114146004401c80000032030043d041038007134100c10361003000150415104100c0d011042c0c101205880c03261100d854542d00030800d540c20101c80391549964803420b40aa01000c001541660404103200c1800c030002c2903a07480e105005440140311400041d00401a03052070b04508065005000386100050400d00d05281c10000025054600385089172540b880006070310381076283ca1202c0e41c965040643c010449807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 931657176 1250 931655926 931655929
    0x14010c02070303051b1c0e01080f0a0903120e0a0201030b0f0105030103060b15190e0604030b0f04150911150703120e0709020a17090c0a0e0c12010b1b0c 67
    0x1c808a12003d02003100204107403400700c0c0c021500810088948003110300a0600320104181c02142c06148030110710b100c400f580c4503500560000c0d00c01ca00d62600c7c800641d640290000c080c1c81071000443c1001b180380c503005055103551041d171081340c01120003840001054030016046401100700381b4820700043c8180d200a03a849021607046d298407000c045007802100012501c140342ea0555030039003900100303c00c9644013412924501e8400c41c2d54400002c0d2400c0703030911500d482980400b23030100240c5400216690640814079401c81c1c440c400c2e41c00a031150003514030848150a40880715000c0150b04a425440c061024200030520031418034076140d69541d000d0541405050049a40c5864403881101c0d601d052240600900300032000f90754544554100500300641c80d0101f00303800d9055004540c9100000803841c12014000c0e0440b401c2e281403505608045000501003500300740100034911040501c42c1402d4004c04030200c4007a00d41e640002c00801d400d150303c000640c02c0e480804419101d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 931658426 1250 931657176 931657183
    0xc05010306080a26030f040c050105030c07060905250f0503151b0408060709050111120f0d0902060408070315020c060f09030714160608060a0605090a030501090b0414010c02 76
    0x40e40c1c40340041c1c03282d86240c409601400c00e080341e82c5141540c00f004010744034080500180c400c500c81c00c0758008e01c0d6164401515580400c0c1d411042124090102c50001030382d81d88240aa039004a0460750000a1b10410910a010344072030810752a10a02d410811262a40103100181000b10041d15910f0588035000c0c280d4440109643c041d0041d1340b0b09a81c21080180454000e003090350113540c0c10345480500500710004502c0380701d0004207480750200c1d005001213588a1240e09030b05c4c0c41032070071901c0484d04010750004886c003007040d0b0f5520b1060005a488000810003404c00002415441e4598109041c01d42d0030204c000d400c0e04e00404c1410400c80c000300e5443e40c483d010310700440b9151120340c1c035146580600140203021071000d1203225a036103800203c0c00c0584d1107101c150524152550011111840183e130390a03042003464500703000c118080c2d0302900c840307500908150710446c0d6a80f100d90a44800ea98280d80c2d540180080c0401c2c024006012801d01e000301009100074421218009d54 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 931659676 1250 931658426 931658443
    0x1020c10110306300601061d010c030e13061814010e0a09080c0f1e0307030921050601230402091c03091706061011030f070c0306060b070c0501030608 66
    0x1141007003043e40c8820700d00716816890f03000b0080a0003111324400200d20f84d5611070a00411020500003402d00c031813a054400d0628104d02d060b5102101d48445503001d40d800d00b0900c000341c1d804000980fa424200d041d0348a4000144401c400c6444082003010407041216080c3c0f41035442e0108039001403003242e40d451180ca8100380c0c0f40e0000a154031f07007800d0a45e02401810b0080489000d8170460500c05800010640101c0d400d00310140032107000e1401865580c441c09400601043e10613004102d50040102c0780080e80c840e156000606201c141d0310242042001d800c1044403c4480c440711600c9000710884049524060394114030b07002c400780000358905484400100841701d03001c100000c0600c918140001005c0424074520b6400315400d0b56a282d840c2180c070030340a12004401510b80b90b01c2002003507013145011001c5d46c6010345000020314a039120b900103442407101d401c1d0000005040e80315030700080a0000a140e200e2101d40b80c04500c681c0c80d503200034101410210305020424010444d00c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 931660926 1250 931659676 931659679
    0x10603062a05030402010302040b1801020f06060d02010315050607030f1805090f1f14010e030316080304060e0709020319150b13050409030519080108032b0c0201020c10110306 77
    0x7a10f03541c45100413806445240c01040710118080341030030301c050851007084c3e02d00800342c003610001c0c01802903060740c8080854130207520050352114100594000c0c0d00c8101c0340c2d0700d001e19480e42241c42c1c0740414200c1e44400300c00c0300081d0801d4418501150300861880120905803229051301707103000f001400594000c0d03d582c11150034a030101d040314080103002026250300085a495060742d42c40710034940c4907800da4403804619903001c00c030a280f40200c2221009080c100c3c80e00c7c0102019120105141c1005100b00c8807265181007415010701c04201a034000c00c1c580300007691f01d180502000800144840708100340342e08003081c41044121a25425054400311540e02c0e84852410b0543d0300c1002c902c0c2c0c80542c00c28948010b0f1002d06030700000820500c58401038030704210958950813110581c0901c039070030254105200c608603030b40340b0424903490354025900769000c07000911500300842d2026240f030b901503940011031305202503050010f41c0489031421010001902c401070076081d144001841203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 931662176 1250 931660926 931660937
    0xb0315160c1e1a01030312050c2703150105030a0809030f010f0515010305071e181d010b03040c062f0c090a1e0e030403050303040f15051e0720010603062a 68
    0xc0d10900009060710143c02c0c400c0d94030500d054040e00f81e021004061450507000780200d0700cc000700c550f40d026013181211000350040a44e0302c12074550740015042010015414000e03400f400c202080300340605c142154a180b0005410705202608134040304880d1802c40c14142000208007a10790014034402e516039101c0c10842035000c0c1424100d407148040e480b071440358a041e41c0d0105d400d5220b2041400c005220054101103662920134042c803900044030002c1038a0180d08042c400d003071203084082ca001104100060b04550500c2035003150361100d00c10f82074030390701400e40101c040c9418800b0603080303042108100217624041c9070040c545a80b0034aa42c00554541140c0050007034200216402950003500b5280c580c01c1a18000803038040103841074076600030380650f52080c09030342c1c412140070b1380d141c100314644903101d00c0d9000040880180024144042c0c01c1c820620580103041a82c009884040006141400c40c80c2c40012694800019100030200740804203001008000c003444a15903030429 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 931663426 1250 931662176 931662181
    0x180605031b090718050402040e06040501060e030604030f201b101d0a0911031005011e11100608010b0a0f030302070501050c0c04021605010b0315160c1e1a0103031205 73
    0x200007130706000d548282d401034400513000030070813500944a40a540110b03411320060341c0e02c003000c582c400d152019944e4550406401b00d00000d00984070700f1000815030400f08484074424800000d5130031840f607003090540005050040d118400091961200022210003502c1d400000000b0040f080c1d807180361408002005608406690380c004000003071000000034085900ca00307254181da03402c203a52002403403188500214956000e2502e00c0091018203002400c2c0c0c0842d10404c407119001d400003011180507101c101e007880d13811030060030b028180d40c00003c11840500300905c011078200307074480c1c08a00d08517101400003d601190450807102c0034a00b00b615a1850750300c45003041d40385040d03141c1c004e10004400000300071038140d041109000300001c100c4000c41b00285078032103000c01d200c202c403624050009104800c0d5110240c80c0d083d5546403000e415611651408840c001051685140081e409440803c2080d11103070082c500c40c12804030394565245a80290030444094000f100c8107486900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 931664676 1250 931663426 931663457
    0xa030e0a0203030304060b03071203080f0c0d0515011b0503040905071101140703050705090f060a020c0414180a0305030f04022701080c0301020a05180a180605031b0907 74
    0x61810440d4000b010390b5500e090038a400c038010070b144000c650090080400005e002c100140d000f002481e015120b17031103a540c60700741c072800040c1e00603e0b44850380030034040074a80650b0351180610484189a1411810b03440348009070517030124108503114400380312041d0340040c0c0c010041d5411564004004a015113440e80203664101d040d0b690a042c0e036290030024904d2850081d042d03405521107031010480e903141c90030101e82c4e80c4a2004504d804c007000c0c400d941501e040403801408a035640b4410744103e4000c6034005015211040c8550740103c240700c090084894080c3c41c00200c0103402c0004120941041d50007030705a0000500384109070b410440000c0a6450f010741c1021101c04d541901301c04090031014641e50120b0038005c084462081065282550030140300321400d000c81c43e241c1074103203801c260040030344059607030b441c5412900c00741c3c000070483d2441d0542094140c3c0b001003c10807900345018589020420300d5401c0d40c4080e00440031070300380c41f60030000d50841034a283c40c3c0c03907010b1041e2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 931665926 1250 931664676 931664683
    0xf1404060e190b012a05030d0612050f0f15040213050a1410050a03060e07150207090e012304020a0503060c0403060b0a030c060f030b0301020a090620030a030e 70
    0x502603a50160108104040c4040307801c41c5106003224a44100204111080119005c0e85480040b2004149154203681d40c1020081c1d21104035101e0000c40e4a0084c0541e44001541c85d03591000c0c80580102c0b001a08114003800f090800420440c0104824800c017090300b6681c03c04503543c0d490900031071000c1400e54a41d01c4d40705400000c41c4000740078504112460030001d09100008101c0c3d0708289000ca8102c1204c2c0700075004560000b882019000c1c1982c8034140240b0715490112078501c600440081c043c00c102c007140841c40d0203034029011481c5415210400e9403651580381c13030603900d012075405404d0300e04102c0a090050000f80c3d0318456940d440031036109541900081e905200d04410042e902402c4c00c001e0094920071030b000d2040c0c40d0b02c1d1050120081281c040141a0b070003c0c8030038801e0510628000b80031100324500490400b0a20010a089910003400310700000c820960500002e81c0003031502c80ea800781400341c10318213009420620303181d01030404c000e0100f6441c0d00d0030100600080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 931667176 1250 931665926 931665929
    0x20030316020f0616080a06062106030b0f061311030406180b041b05090103050c06071a0a142202010809031c020d05010e0906130c03150509070f0f140406 67
    0x142c0031141c45041c095120138480903682e0310000022411800030b00518044e0003590700f1240162180392024100c10201004035810301071405115039140000404140702d0f20709140294549502c1c0340950a21205100344602402403c82c14a41000744090000c41401e00700c951054000c0000a1148084001011a160307204809406040c034001800184101001c050316408a201100843c0c1ea035208180710b581003091001500c5600b120f10400514144000101022803080c1d03001206d139841c0c140b0082007080190354000006640d120070304000344044008940040e04100e1041c0400c2207040c4c40d01e13000301c2100d00281000400000f15490039070810595110308172104008042c24185248040290410701c083c644660403c400046c80c0d01c0000c1d11703140142c20010240c0295a00d6090800c00829201d004a400d261040c60002c0492894042140391000042c4046601e040c08200c0c00c1c035005480d0089a160700100004101c00604041d03d4003c42d04105c54a030303a13010060000800034000c1c0d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 931668426 1250 931667176 931667203
    0x62c0714190f030b03010e031206031c030c08060418140c0409141207020d0b04080d020c010b0901140a03230114100936021309032003031602 62
    0xc46070000d200d580c000c4a011040703900ca9404129401c00c8504150030f03034012214070f026a800801541d1900542024810340c0504054100d5000c8918a2003400041c4207003008400040d80c2c07000d4103000154003040c802e4004208440a110270102610014002001d01000400417540c401d041201030300107001c2c41d202500f004000b0400c1041c2e81c2000c00c808141c07040c0340307051130150200b018001c5140009a641c0c10f50054a00c010120326556003040010000c0c0c0140d4090500f400f616401d4079907800140002e064403c004520b0300c0e6804280300000c0c1041e001011004a480c1d803952282d21010249012a60402e003103151082c91844212140280480286925400c05445400342240743c09030714001c61209042c100413650700c41d02030085804001e4404241526041c03481c0e104003108954040a0500c1841c071b121440040e400140f600010340b03646443c09848106060074180c000004110030f030100c03450450912101c101403600d0f40702c01807841c8100c482c02e040404147c0c1c030822031107001e41321 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 931669676 1250 931668426 931668457
    0x114091509070f02070e010f0b07080d02030103060b2d01051e13060807030c0e0f01030b0a09051006140919030512031b130e13020d06062c0714 63
    0x1001000140800036298000000d446807a5002030a86c1c100c0540d68101d944103501c0d0050f1608010711000594040380095501140901800003500c056200850080d4490b0030001502820274061202c3e80390303180d00118404520044100c1c80c4000c845c1c203a00c00301c1c000d103030060341d420f28103081031049944080030500380c1c42c01095400741a40e00350304505c251405500ca151301a40c441c50300324107481042030700d000010440384190106007030510950241007814100407a10f51006004074a10b615079074040a0120b072175400344207811a1804102c0d006d4019850040e110307070301d1040305404520a030010759020f9503000c80c000b12094a1010700d50061944101a6208a68a24a0301c070094000741c0e42428008a6070b46080d4404451500704c840e0444071261042c040c0d40340c038072198900c03130001313200340e03441c80c080c002980050b540c003481401e20a1280748002401c1e03007044109400340300d0300d28005040241c1044441348908981c15000d0348401320340341640075141c4000d01c801c0f00303000303c40c0c85024464 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 931670926 1250 931669676 931669681
    0xf04020c101802041808160c0806071d040212060603090703020607140714090f0a0f1104031b0302030601290409051b03150402130305062701050114091509 68
    0x306502642a802d42c000c590030301c10030494481020034448043d2000b0280a000c004820008007056044901d1a009411103502c20b40d0b2000c2072800d041003150701600040e0590345056226048950610070600151011410a220306a00d10780a480c054400c900c00c900110016420403010004940503581c0030f0586601c8024a1400580149642d90f641405000701000811980c0c0c85030621104080d00502500c50782d01c078440b21440718030b40a03001000a9444480415055034103002c0c01c2d0100001078540350b07442c0c5c51400d03c08160509a0243e140212521600704003603980010720070b0641f502001e0312040c2d5209603e021503001c03c0b44071703403240310031000c00c001820003180d03440f0b20311840e0f011a120300c8903030b4401d4501041c2e11044808442e01030f4130008840003030a159015040e2444003c0b028000b441d100e03200c0d030703213032950031a0544104c1218440c60607661041808020b17000031000002e110950410307403201407581201c0c04c0ca901034508040080c02c01410340c4510712030002c000c0e15001950 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 931672176 1250 931670926 931670951
    0x914060712170f0f0a0b03210a020f0303010501020a120932090603191e0c05031c0207060f030b0d03020706110318061b01050a06050f030c0f04020c10 66
    0x714400c2140340b121010820000f611404075400b1a4442c000d10314400a40366140c14489006002d905019905482605520340d0080b00007502c0c200c06130844d644003a04c90030380ea403000f0718055002c980816550420b00042095980010b100246a5802074103054110b0552508442109180c0d00042a203101340480c80d0040c540d03014499000203402000700440b1180f40148021204103507000c540691291144026050a9008a112151043c421041d41074403483c030100c29440d0810050300e81c0b05400800300a130b842c1c10000c1c400703019040d072071070f030030260106d90041d4a4141c00e01c41e0340240b01c24802500c424a100c4d9224400d20503004004660030002400c000350707500b03194010703140400c480c85056000c00f80d0000641e01c603404003095001c10300c1180c50601095030009030b40c4e07048146640058060300301d428001c5074416000204e0010b011391620042080743c60503001068001d030448241c07004c03548c0b03800d411510b00d104262070142e0345100c0c103a81e5515003004020b138000302524115484415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 931673426 1250 931672176 931672187
    0x71d120705010c26040f06020a020f06031e0f16090f1401030f0207030207060e0607150c14030103111003050708130203070801022d0c071208130b070303060801020a0914060712 77
    0x75201013040d06c80c41c140d1192020307a690124008081d5210700d0341c64a030465840c03d5002558804002502d0303903000d1881710040d03401d240d0192003540441c0101404c1007041100391031840202031003403030080e020038030b04950103442e2400c42c02128042500740b180c2229590094002607000b0225100466503000e0300d060094a0312603d0080c40c001441c1c8089808081ca4110142c40105401c00301c0350504d41030b400c50b10001400c0700309910090003112420b030b00c0450541c10146000310b004002d0003c40c0e044200c00c119482c0300c244402000e26140c40140b00c240355011a0071640008070008409003281d003400042c1c9800010b90014005600010710010b82c841d842d1a0b5000300101100340d00030030884088110058017580401241660201d20100000c440320040340403404d000700030392403070709801d14440079400b003141e00b1460100c00006504810035905200e00001449131030002c500788208220b0040c281d03034a910691062101c6040e0400e4107584000031600c485520100009226075121005001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 931674676 1250 931673426 931673429
    0x307020a141c05090307090e0a0b07032702130609021b0106081908070c0902040311010201090b07230a032a02030304060207050a0b071d120705010c2604 67
    0x1034645a406141803032910024142c1c42c0507101d21140c201d404081c04084406411454006030b0500c10321b100011019201d00c21142000c01100c003814112505040445007000043c280030201813805e01406885041d4901c0b8400000080310410040c1080f800040d107030b42444c01140f00e0304c07071a10a00140d06c400035070080890000080c000038840001e0b1180b54200c90552160140c02c2e001024850920880c51180d0304c01c0074070800d81035041480039120390101c00c0841d0440b802c40350b800a002d1007400407000f01d607902080244020301c9018240d82d9008452000900750741c5c1803110015882e010b0300d0b00f41580c0d500070900d030100541c4a120702040100138205d403009100700c0c541c0e204001e02c030209503002c0380d820503034098000b5840c41c2c03030300c1c0d840400a40c0115000c1d01da60103040311600018402d1000c0501402c81c1c4d42e80c1c03440d0024500d103c0381c00c440047c0e031400c1c4a0180e04000c20402c400c041000801c0300d000342400000340009040c445c494010309011160600d00c81c3c0f40f1070301c4503c5460017400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 931675926 1250 931674676 931674683
    0x50a03060b090f0114061617040f141e0d081303030e04021305010f030e0f010c141e0702040b09040b0a0501120f0b0603030705070e09070b0406051902010b15030a0b03031c0b010309080307020a 84
    0x400036503581d00005820b1408580198101071528184d90509411881050cc0207002400d4001880c40c0d9403510940b64024680c0342000c100a040d08105060b84904149448070045034110700d40b1b0894000c2a480c421184507181c14840c01141d4461010300940c400071142d07200600f43c600c0700b007400341401c2c001c1c94805141004180c107581d110555120310b81c2902c0d145801c40c1140d60441030407402000c0c81c2c3e00001012a401030f00c8480d9a2a203848420b0b00781d0181d441032000d004181000841c090944005810034034886000e0241000440c5888400301ea410390402444551905ca54020a0a520039144050020321030311000290240024650600c80c50b0048160f40906803108040341451007a4400d000010744180840612100d82c40242500c481103800000344000ca80c1001c03a12803400d9541803101c00c41d02000700300400445000d020072a2400310051450000307411320200c2111115017580e0082903031004071462036402903011449141c3c20407501916460300b0b00000703603101a0440100c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 931677176 1250 931675926 931675949
    0x204030605160302030f0a0509030405060a02010c080c0c0c0607020a0b04080607020d0e0108061915180b070302060106081003170c010b040e0309040f06050a03060b090f011406161704 80
    0x2c0070140c0301c1e1007980d0041c1c61841103070315a40c490910050240c403001d000401c03503000400000807955134090080003c02030a0b0008121101e41281c050700040001f000800544c10400029000743d0020600741044501225203a2712610f43d4004140e207043d2542080740314103030025020800b04d500040c03080c070902e1150300f2211041c804c050121401c0c8600420709000c1417400c0d000c50302e00d1901001508400f03100001e50580b1a99072080101200d0b10900f4450100d00d101d00361000f0343d003864090001809420314600d1410310702c0e43d002540e6a40510501d03041028000100711b40702039881b001c0d8000d45c1c002c40320000075480088102101e81c003401c4c080c0220b620b014a0201130b814603002e80136a02d40840040d500303007540842400094011104ca040b5a00d41d44c000209060b550a001c85018600a200020384400004144529100e001e082c4443c00d642840042140514070620650112003e1b60526210164084494042084840001e1103240d05e0900d04803080d1003000030340110b03800132100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 931678426 1250 931677176 931677211
    0x925051b011a031216020108065509050709030c0b0a030b180f0702030c0f07050301270f0f06020307031e0e0a020909070314160e070c14010f0204030605 67
    0x1010304c0d48103031601c200500303404050304000b66002d512404d610150140800c00d1030f03003140302d440e1601c40c0d0003240030b219154420800501c8102545c00408002c4e050703801c2c60305000c10302504c103040e000e0038131542c41440c0c1c8a6001071080b911803c503201c0110740c8104a0b41c2c16540300c610b1414290010b0b0303403080029241c40002c1e00d61780740c4407100002c1003021070900111501d6404070600111002800b98080d84800c2154140340c1c0001c016400100d02d9040140407403500f050704042c2902c2c0081968445c1ca90200c0001c21440907031130801d01c0c540e80c00100244940c0840c900425503808900c00a0911440481000945c0c0d41603041508518080c80e5500d00c1105a041c0040450345079241c0c0341c15585c84a00d202005003080003501e40c0011101080b1006a035807952983d00c01602e1072a9a0020742001d8240c03900908030550390005400c144201c03415030702e861400108410b002c80d00240a020f140140240101d0f000c0d03115202e0302e0301c030f8030003550342d0358072818200301809080c0d85410b95600781010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 931679676 1250 931678426 931678453
    0x2e08100f0204050f1504051206010819030f180b0a0c03020d230c01110c0307060c0e1c110306090c01020c04050f011a0c0307110925051b011a03 63
    0x3100c2c00d444000380040342d401d80a4062100d001070034000501005001c0101040d1070b0384070f651843c400c10000008220641c103140065080411a158202c0c1d1301d4084504480040c0c0c10550700c440f800398520303080d031030061680144251001e81c0e6001c0907400300f001a04120303549d0300c0101e400015010b5001c49103011500002215620720800580025031151802056440c2011000305185202400046082c1c044002d41d48041ea0040414032050350000401c0d0040041c01e0061100210645c00c1025000319a00042591441800c0c113601c032490f01170b6915410052103205100ca02280078046602e18501403107a83c5e07403071000455060140c4100a201910351a06008a512609414290b014541d207000304405000c0307101c1c1804012030380103000c41600100200064003242d0b00406030070004000071000e00116802c0035004505080c184103100166040d1620b170540800003500d070072039444ca5025000c00d8900c0728043c0011240d404c00c00100c051840b04050440b00c42d404800303a900c01180d130710 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 931680926 1250 931679676 931679681
    0x80c09010605032a0a02061f0e011202031e0c030111090d02061c1802090f06030a1e022101060503161e0b031e060301090b2e08100f 58
    0x481d0030700251040000030000b10180d480304480b0508000c0212910300921110030302500117030f80d0766006030710050422000082c1610703200110110031a41c20030b182d052100414600b0300c140501020b100722801c2410171520200b02d03a40400c07c462100007400e1013441d40c000e448007007402e040c500c603608000203071082c504103400312a4605070061000001c1e545550900001c0c2d0054440c01c550328021501d400c148200e240121134260010540105012040384104a03c400f400350140300140035881c2000f009480000c2e44a00c195040349680203c2d1002402d148100203607180029040b2081e404c00240c510350341440120303400030040090000989413400c0c15a42c10881858913522000960704000d0b030103030090010300101801040e50b4046440b64203103202980140c4150f080c05420344105440800351081d51904960120000d00c5200f007903407154940c112010b091100071005848800f9103d0070318111031050341004102040b5801e907984075581d12019a220307036050070743c141102c1d0a6811070a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 931682176 1250 931680926 931680929
    0x130515010905031908040f0902030718080a020409060b10051209190b150a1203020105070f090b0322031706010804080414030c0a090603030e0406030b160311070b01080c0901 76
    0x1400400c16002010070040800e480e5081c2615059000c005c007087c0c440034400c00101415001101507a01c0c1441d040060000c07818140452854038900024880340030003142c4030100d00d404036404102d075046030034450000e100c6030b00c005602040524115060030b400c613025004c02412a40d12001a41d56002255252028042d03e49418200202c0f4007001510103440160402411490203415207024804a08000c105400402d1305130134203804030741056424011694040081d217449444e8002c0314102400c4180c0c980030303614080310b000c4002509030341d0308030503180d41c0101201248209401420040c010380034500d050441002d89a0000300a03501a8004500455025142610301440c010145000c48403903010701d941030041c5515416955107101d5100301a00c1078240000c1c8403481c610b0044c1600c410010703028010f50030502c0401c04100c48c3c40786954010300e000d1003a02c000c4140e001c114000c1000c803c21100302e040100d8004d0920401c004000c3c165400002100e0301d040c1c0e503108105911109 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 931683426 1250 931682176 931682179
    0x20f0717040504090b06040e0d080a0c032318010c080a1d1509161202060702030a0c12171303061802120d2c1509130515010905 56
    0x104000000a0301000c0d01524106049940c40e08164851001900783c8229000030b4500d00c00803024480280380901c2000c4009076104010100d0b1500307450007529400d0010071040c142c580c0e4150300b00c504d60280d00400c01c0002c180d45040c0c211282400c206048020a80b1107240781c2c089480c41da40d21920500c180315052600e1b40303450565a84054042c030191840c8044d0064040d4040341141030004200f10f20b40c0000070045000b0716602d040f42c845807030701c40f140792145000d452440c002c100c64100c050200c2d5030345030191401c958076141c034004a45006000a40180b2265003c40b001402080305094002c2a07071003032844142d000b0030482800f426004541c010080125081020000180d099002290100e080c11450380d020485d80c0000b0300b08600000340e00c0094000c4c04500b440c0ca03911003010907215208074402ea14810700c0190401035420103001da9030054007146c10425a624869042d5540280e000744406034840d50418901e01819094440100c644a903107003846040d8018540142034450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 931684676 1250 931683426 931683457
    0xf0303040821070804030e100504030f05070b0304080403060f050601051903110d0f1506170919030507030315050d11060c060106021608010c0905040207050c030313050a05030102 78
    0x3641d440e0080380e588140500b110781c001000312900700c1d070328555003144541100c1d01c51902d00d01c0c040c01c0280802c2e00d40c4400c248141101d006029165801600780c0d000d490f04000c40c55606105840e060740b42200c0c0da0007407a024000031041000b0050800003c2041d82d101c1c10f414410405024031a400744c0c2e10a4803c81d010500c1403184001c0146404074607504072000b4a00410141c1c0035008126265020108401f003c1d5140c242001103015107000d40402d00d083c900a4541e010b2a064004160030911800c0c0ca00e031070040000700d01036590802c0352254112038a02d00c076404548501d405005984080c404601080c2040c1c01c4c101030442c12110340046440140107500e186e001e55507046040d1130540300e200c0e80084203000c618050390f4100946406800d0319001411860003606601407004c3c119480206180c6c144100041080e6011001504840080d140541c83e88903600d001d44c20b2001c0098015054440410019050703402d00b40e03403104a500c02d81d0b0503c1d1690701c890030b040c241d01ca6681030492140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 931685926 1250 931684676 931684681
    0xc0902120a20042d152d030504031803031d0409060f05010815060a060822030320160b041e050303070305060f0a050f060403140610080f0303 62
    0x1285500050384909680c60000b020500c049403144040d0000d4001c4800d003641c226800c0041c0e0183c42034200c042003410101c80c002481c004210002010408138001000707500181000c401e18215030b9000d140d26210306482c0e00c0480b00758010020402110140e00040c0504a2102040803a1002c00b050700d81559402d10505100c9141e1001400c00c0c002d115085541c1e6543c14000c60000d21407404000c030041c0022403d07500d0960000c0c98211044092010380c0940700600c2130a40ea44555201101c0b014105842c00766540e00301d6460901c0703c95201c1503118519100c40041650590040005400e180b4041890b03400400724030605028274004140400e15608002c1d012803050241281d11501ca58190089a18110510008089000b2046800c1c1d440071050004190300b501800364000d50a544803404011140001000e0038110301c6504d0241c800600041034640b2030030304850280d40c2051051150400346500720356281011110384001281e48c10010600c030001103071200f1004000001942180c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 931687176 1250 931685926 931685941
    0x1020c06031509040f02040b060f090409060605090a05100b0f071709060408060912030f0a0f0f0c1e030e100506030a0c06020d090b0319090c0e040f0c090212 69
    0x1a400070300242010ba0725400c02620654071049070600c078601c9004142c0108020b44140005e41e03e0050301644504018000c04510403000000d480311740a00310b4010880d0b0445080c540300a024a03000303140c00a14000400410100079040306000703e85203da2203000542e142000c100f140503161600c8050350042000c003000caa2182202c0c4000004294070b1450b0000100000343c1c50f030b0140e0700c00305103070300180100003404a00740943d24602000000a9145140000100c03078440720091107803282903680d45011880303100a901450702514260001c100e01c140b0300c4d0f000303416541d0354400b0102c03020031844828030a521a00070002602c41c0d0740d005018101071441c10b14042d0100410494061040445d01000728050080c040f0090040790094400c885030102c0042504016420488400d5030400600140807100d959245000755030000c006810000707441c0c0002000526407040c2c107101d08200030300051204054141448030b1007040d41b00300c0942c0c1c0e040309805038000c81300b0ba040e20105820001e03842 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 931688426 1250 931687176 931687189
    0xa0b0a09051315061a21011203020105060105070f02090709030611180409050c090c1c022206090b16051c173c0f07020d020c3106030602032401020c 65
    0x2410844212007034101d030800203201011409032300c4030010f006510482018160288140d036040b0000303280c000d140040c00d85900e00c0162940030024000c08041c00050080340c4560f1500e00070b90752103078042c004031524424110f582c0d000709a18840044182040d0303203407850540b040c240c10651150140c0425020502009040c03000140910b0b8242002c0001e01031840e201010055060681c0c2d01c016100d0720350251200311510003244481051481c40c005100894200e0014021204880c0685540742040201d202c8044010b5000a00d0b5100b030f2000302001c042c0301409a14140c0d0b490380e45450942c1da6100401c0e5449e170544a641580c1b42c0c105076402e0801c0c4282024540301e00c0c80c40c1036004420050040c21200030b0440c0c00c01040405a018805101c0c0d05121540d014840381c0f008100a1002c040080c40b0003a00f0450384942c80c0400364000d0204041900c9036000c0e986104c0d0410209980b0f04004010303602c1114142c18801002080c88909041d030304400001c04c40690060040c0702041080c42107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 931689676 1250 931688426 931688437
    0x4212080a0917160e040302070e0c04031704030b06090103080f03150603070f0806220902011e030f180f030806060c072c010e0a0b0a09051315061a 64
    0x1001005640030030032690078480741d1200c6050b40010f04582e0b0114080c181c50780125000051090820028040840d80c0000d01501b0b81d5040582d142c10398540300d0b6804410301c943d500041600c1c1030106020402c40401000d0310442c0e01a110041080d5240000c100103010240401080741a090140c10400c24240c0c001c0d5030b0100c0ca00d070340404d400501100107515900110795050018180220101000b035101c440587c0090054400b0413081d40c0c440945035013072614484010080d5510001c05007560310402d917681d4002c5580d01c8a204000c0401d0700200504808140400d1250a240001142c0d40651841c60380c1c080c1c00c4041c2c810600da5541e000c40d8100e40c0945800c2d40b103c001d018120041e18240141c00c010610803070509020310540d0007441e5403507404901c85204407500c1c40100184d184032840a503014449800c0055541c0d545070020703100001682150038064034040030031090341e903550704007004140508181002c020240d8591415900c6900454001000e11000f80700c40c1402a4058007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 931690926 1250 931689676 931689697
    0x120307050d020106180504020a170f010b03160e13020a0f0806070c080a1b06020414091305061605210a200912010b06360d020d0303421208 61
    0x309c8503540302c446449100c0280d0345106a42c11400b070f9603500c24001d20612100d40e03810360107000b454018006c224840300252064580ea8940b1200050241c80e42c03540045895500030030342800192181240281016180140d8034240306017404140040d0080c803151242c103511140c0c4a2801d50b000744216051901e14981c16261010032804000007102da0010704003520035600ca481403080040c041060784000a01481195803008504002082c0042240c40d44003000a4030b4444a0b094014111110b1040e50916101500d07041c440e210b900360309030b040c140a0039485009005488201000b0040318218080200b1503000c1088100c14508281d09900c82d2071010038000505284204089421b039441414170607910015006840130500b5401c040c6009040c4150352910b1f0910a00c010884440f65820040d02c01e104d00c00302001050b20030703080080c2c4c1100d6250064808814110241c29032a10142e1022050144205410210440b5194402201d294104800320b45505440f1000164020034115 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 931692176 1250 931690926 931690939
    0x3011d211c0b0d06110a021015030803060303070b1005010e1012050711030d060501171902071e030c0501050c120c1e030c03010e0a020c0309100905120307050d02010618050402 77
    0x80482d01c144a002400b04810b01d0717041d0748816440380203003000020054080014a0600c0c0d5041d40c110400c010400d50341d000c6809640c0b521000c000901d940140c4038024142140b400030003d110044c6008071048507402c0e01da0b100e03080c0c10042002841070076540004005502c0d107504002401c0319401030343c0c0100850920b142d00600c1800e2036420341d80b01c0300540c280c0c0ca4072041c041006503440342144080c0285a000b040300d50400205e9110f900c030640310480704603900824807005002e1110804045034062038040c003082c5065140c081c1c604149181d095400d5460200000c5404c0444411190600c0030214427160550755202c41007503a4000d15407106c11804c010340340382c0e0300204190085005416020783c1c5916580340041058038148003d00e1030b0940d900504c40300c09080000000c6d500c0105046694104481c0384050466406a02d68489a8030403920b481106506401100500040d4003500035500e15800b818000d0303090392041c2c8510000080070702c50100e82d1304007941c0599005407004028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 931693426 1250 931692176 931692199
    0x1b050f19140a0e0306010b13031203061203030b0102010b0306090a020d0c0915080705060a050f28030c03060e010608070f0318030306092f070203011d211c0b 69
    0x741401d41102504501141002c080110a0b2504000c43d500409103010083c0c5840f1407494040034421107884001c0039170b0784074904030400602a070011000392800b0484030140d107009007030050261050b0b07a8a103000d540b8005010086080118841d0322031000c541c01070428030b20035424810b00c141000c1003550354038032a607404100ea80060207032403581c002503150301c1c078100d06108001d420f20007194400380c03081d24104055146d85404c94140c99410680a03542900c992500e0f100c0608600c202c003900983d0050a2001a0515010751082000c0c0120350703070410881e80c8401601594590a00403071002ca140c00f070000311194481c424600901d2100c5c5804565904404000c1d00079503c030480c124046622194180640740e1640728426031007402119020030708860700138200d91401c0306c0c4001e400c140070000c0c441d01507403025040f501c02c0d64142031503134050b01e048030382c281d40f281540741a4514400d1010902020007508000f82c9500114242201654412801c000c4006002c0500c000d50415040441d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 931694676 1250 931693426 931693457
    0x50903010e100e0d050703080105060d141f090e0309120a05060108060103151b1101141e0609150103090c05131b0201060305100f020f0d1b050f19 64
    0x2d01c200d19a602040462291611000e0314100181e0381c0d200b00420106209420129501086460444200351032807580d45100f2482800544880c2c9100152210384405101c100c840002d031548101060034000c03858552070b00200307801d685241910800c154407e1012212629110303641c001c400c0b040b5811105104903981d00d060404000f64040041c0d0780101004100b84000000c44800c3c010340da0000f000305a0400a41d0980e404201c8024010000020f900c2001c5240940c0480c1e010841e854a9120b54503040554400907441c2d0040c046445e2901c20114001d814400c01641c0150405410750f61003a0103280110003e001c4034a0075200c080c4521000a0542c803003e229014905000c180466003e0207005040c18003404a90a4401c682c9000780400c003180022403041040c0c41d04150200340c0c40c002000020290040c0089030128a2000a10090090072540401800c02c6201752608298046e01000e5a1781d000d0010403214117074080203c01025003d2038a031612450300e50402d0341070f5218010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 931695926 1250 931694676 931694683
    0x922020403050703121709152a1c0603050601090902040204050909060403020d02120a032316020706020a022808010e01060e1003120f091505031f050603010501050903010e 75
    0xf8405d40c0c2440150084805e101e5101002044000814807541440e080181d0082d5443c1e0400002141c0714084101141d5240860011418100b10b040314180e15450b241800b082950320004070840c9440441010088800c0380b40110f00c1101e4200c000350413541e00c3c290f120b10281590754401c907805642044003007000d60b1101a00c5000d8012030f80140080d180c07034600a803806a01c030711000b096501c010034044101310f80c602212400903040c600030134480140d01001c190030b07420301054110303500e0100400c108041003820488240c4540d5080320449a81e0b00c5c01661a124081d5010f5044040401808101984050504540302c00340c2c0752003007465aa81082401c6402c1074040a2803a51140c01c208650180d0050307694000a07188000602a0b04e5651282c19814400da0403a0902005419030170707c0d0390003800d641008006082d40c0990808145800401c03540c0116919070752146141240307203041c0e60001b4560165100030384007070719690030300e001903aa9400c00d00c4401d40c0341d1349a0740000c1080c07200b031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 931697176 1250 931695926 931695929
    0x7080706090b091203240d030c031427120703110a08060c07060c020a12090e0a020313020f0303220e09030309070504270b06041109220204030507 64
    0x2600300080482491802440400e070152400c03600f503100c0100303520100340340800c90f500074013a124024a02d921101c0240400c2101e0b0307050710361121f81c4000e0842415004030410304814441c2e42c40c00150a001101d40f0707503500a103d07020000c003140c40510740c4200000e045880072040014064022194441c05072441c125058204513440c0160380c0344180342d820032080e19400b030036410018001900c0c22103d00f00c81030242840c003506880d102d001070900b0f18020f1254890f215003150807151311140c07084010742003011b54070030125504004400220440324910076640120422401180b12103025020071000c1c904600700076034540010024040708413480000241d95029614150702c15515007400c02e002408002c0040384960400c100b04400c2c100c02143c0c88095901c220350010350820580d0840782d02c003107030000729041c3c24100f2084000344a070110845208101c212424400600560002e0b140c41c0100403600303402890000500380078203000c14503030002c0194280c005003865907a80781c0a00d066880d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 931698426 1250 931697176 931697183
    0xc03140c061f090204060516140a0807110409030203161110110c0405060916020102040e090f010b010f0f080a020f12040b01050103290f0a061107050d1a0903070807 72
    0x4003070061054141007400c880043c1440441141460f250a901420354412040f104028040e400d44840c20020240c207460718002454084400100c91391400800725030200c4815980c44440300f0400703181d41303002d00650240701d505034050760410502e0f8807041000d8a40c0f800843e5610341408800b0328944078511201418040b558407000c0500a151040e41008402c42110f4040c41c185403c00410f5268400c04540040f8401d804241d03a4100550480c02802241c001c40e03007011100c400c0c000e000b440011754449501e0844000c0002c21400d00041d241d07560900305240108003982074001901d0300468005902c00056074025150500644800300359511261074440400310030410722040c00341c41e5140d1400360600307003010000a50100c0380d614110a07520548202400e40721004041c1d52220909507444e2003000d420340c1c02c000e8880d00003178200c807402c1103121f00303512070300c5400507040c5420b01c00c01e000e19030409001d040c0e04000b0b54200c00907040082502d4001c0c40104034000000e200d0781d00030f1814900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 931699676 1250 931698426 931698451
    0x10e040507090302120c090105060f1909050f01080405060c071a0a05070f0507030c0204020d0b150c0c03030712030c230a0e0d0b0708150a0f0815070c03140c06 70
    0x1944104410516036110117030041c0d001601c141d000ba112940e44905407482101c0c0c0300d4607220740304021001c1d8401c043c0903400c1c0c41e10405d400383c481a0001610381c142c0b08100c400d2440d8640c00701c011110302408860103042640120b01041c82100c8800c010b00c110350090b0107c12424042503010000a0000d03205c881d1074658410412280359401070703c49520000c2172805900d008a1500c3c000c2c1214581e00d07010740324130341c0090082620181540718103500d080142c5640a40d40c90000000c0c415000000f1280d03d9025030200c1c048185004012145d0042c3c0c0041c0c140d9000552040440003005500da000d0f040c03002c20300741c840c0c038801004000d131102c0820340c107502e680d0303407070808014844032007003541500680000c400c1d0b8002900c10100f56500000ca4900b5580b139030740d07560031804c4403803511600740e0300010341c801e020a144080c100c00100b95610f010442e1001c07036409101c6001d14404641d00c00004030100b6032000040d1040540ea00302c014154101814a44400e056900380041a50388402555 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 931700926 1250 931699676 931699679
    0xb0d0203120c0607090305150c090405073915060305030d391103040b070b01051c1e15020a030c020709021e030a02160c0e0c130b09010e04050709 64
    0x150801009034404600d01d024141c146c070b180d880340c0d07980304118000c1d051520400000382c0c040c10094181c0300403c3c8001c10510150170035010142c55081000c000e814166100100c0f071203004080c20022071b1982c910040160890002e440d0043d031100121007800c82aa100c06001000c00d80c1000a040c40d01c007103220003e568029100e030825482d003402d8a841c901304083c1c1682400c100041a0030343c0e80c4815041c020300c1d03021020142421481140c1000c210504049004418040c61648042c1a41c0c41901c07940b85a031503c29a40b10000c1e03480800030b08009007105a01c2400020484000c0c01910906a0002098103c200c85050360410401000020303928556821099410081034004102c021406c6250a04814000d00803480c0030340603001003200040410940c0d1596412600c00f0982040107048000091030482081d081c20310070040c1e00d00225002c50907410781401101d012001030182e100bc072924008038280309800c12525207042c050320030b040100a40741c9010301ca1041d0210b68800729400e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 931702176 1250 931700926 931700947
    0x70e0d08123102130f0b030f03040608090a02061902120328050c03060f060f030a02042d150c060c0e041118121f0b12010b01120b0d020312 61
    0x1214103452600b149042040320340561102c070a9a40e03400900c080205403211341c007400101420050300c00c107803d0300c102807100341d64440200140054844503070fa0f4802549490b25900d64401941c803001e54040000c11824446180c403041d000c070800050300680300d0014260843c082c0781d410031a0b154903003003010380c8041401c20300c2901248680000c1705041209041101e904241d0740001044107010308110300c0404016a03d600c242c030070703141503418681e5891401300c0d10140a5001489010014505c0303030941142200c03071030501c003801a03600f0492402c542c501842e42400b141040c3d030b20010b10031500700765400b08070f042c050032212500071b88800811903480014841290401a04240c0030107042c8001d12100c80e030700121400b0310504841042200405500140c1000101503450740c081040c11120002d05907a50044003000700c04541d00844c04100e040c5080c00ea0b03500010081c001070024550b13080c000f1007540501e860407406407041001c400564082841c0c06005c007031907104000d0209082121 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 931703426 1250 931702176 931702231
    0xa03140c12071e0b030c1921050a0e0f01020a080c030118050606070206070b04030e0a0e0f04110a080d12020a0e01030905030f0403060222030201080f0919080a0f08070e0d0812 77
    0x16100b231400c03403a030642340340f203c600007451207442c510342c640c5030b80c01b060783d00c00e00c0e400c0300046084070000c1d5400c641c10021107900035070201c00d80d6400b0414140c0055603910410040c0c034100c0c0c900d050303058400010b004026005201c01013555500000510a0501580350030000d00034192003100c007d01c0d281000d00380502040980e50019200d40308816040c081c82e50a40d600e660420048026000c00d6141ca1a0915900d80b0902001d40c000040355070004026030000380b4068a9049031310b4281200f41d0002014090f40704440e80d440110306440d80d1514103502c04c1c2c0c40905e0030740c044e20669040920403110408541c4c007507031040c0c420940100b00e96581c0f4420320301c0b160780b0000060454400c2891940003030300140004020071100c148500000c2e8690f402805441e54003c40c0700210388400c011843e1104242d003200e079000300020224a4120704560042e40218001c000c0c9484420520022004005203094002401c4940f030304280480035070003150b400b5050003a680c150703140c10040012092140e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 931704676 1250 931703426 931703467
    0x90b040f060b10020d1206091107060c08060a05010c0f17120c131503020405190e070305061c0503070503120103120807050a0507020303090a03140c12071e0b030c 71
    0x110f02c1c4150850f214803900018403204071459800e041c2206c0110440e078400401c0103a1100c0041d41c2011700800c00500714800400045202d17100811001c50180c0b001c03560340d0b404a9070540c004402d032005100541c09042c9400e030700ca01c100f2a0100815140c4d40d00f4028007800e03c1400c08102c004100f10020303d01081d01c49030721001d50440b2a043c030710384208141d02c0452b80d10400c0401c00d91424040f00e82803190f0101e4003e84030283c051055820507050812050315584908207550360480d0200b40c0c1144613005041c001c1900520341c0854002440c3d14100c501000e0b88101e940d072008201d100c00042c8180058801c490314101c1c88130740d41d0701d9810f02030400210400365400b0400100108a0760a40040658901002e1807901e15118961840464554405c4075003180e48070000303070800001c110401e800c0c204020320030300a035454203080c00103000980c40f07021503074052904a000c041c8000071104249002c401c01900002e41c11540c3c56448a03440da00580306008200c00c006a281856a0000380d00360 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 931705926 1250 931704676 931704679
    0x903070f1110210b012003190806031c02010923070608091209011422051c0b06040b0d05060109110f1e131e050102030f07080706090b040f060b 63
    0xc90850b2601ea030004010b0040881c083c072281e40ba0400600c41c0d2141400303807203100e100312001c00c0100140d50b6541d41e0b0340100b1000485141c000d6005107516114045007070140307002400a100c4c401c0307004020b03252244c1c1d58030325104666980d0703441400304455144a83c1c05100d5035107801d2000410300c0360182082e080e070300004140714018090080e41e0310000345100c50004136000c01070f1140c20b0140102d805102c0e0528410030110701041d20525000b0903010710a008020010560f0125601c00c18017040f150800344004035524442c00c14004558030702071469004200030000242c646510780082d01c0803803594829a240d40c000401485a02034500c00d0880da2024018a14140700f610400f8818034403c1070300c5021030342c00c030711345140701840c07c88252100030090141d8a41c41546818003082c008465101152040002c1000012203500200454010500c04014a4601421a210358403903138485070040b141e0680e200750000211303004444084c020340c030032110300e06200c0705410300c0016140c042c031146 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 931707176 1250 931705926 931705937
    0x5010c0e011b0206090904050303070905010e0a0b030411121b03060610050a021609020c0705102f1002090f04110301050d060f150513020708030f0903070f1110 70
    0x9482680c101018003982c50480c0c00d00c92000710301d880810031500403491100e8100180405000c20001c2c04400745200d14100d81d10401110303514801100c0810082d1211030700415009014855086180300555000e8042e03035560006001c0d100104440140b80b81e400751903174001d10b0b95881d884510540412034920220300900e4a070400000040c030340b01018544809010b07000540c2d0440600a0140342d80030201c00101d560800d98601c40380740a503200482614050145102c04900c81c0341400d01c9100701203140d40c40005082070034208481e60028501c0300e0000c048005e0044040440401656549007604034016865001500070701c2603d0114400c00c134482e5003403132a1212501007280c280c0e8111b550882e030030504031364030b8100003006089130f10079103440302d04104400c0e0485c2e403218884030843c1c0c1d003654000c04a442001e58031040f40030700000146160310070004194401181b0100d103420000040c01d50f0318081e01652211600200f266080f1828064034850b03103020b04e420b000440e107907101420700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 931708426 1250 931707176 931707197
    0x7090603020c060f0a15240c3909020d0f05060306041127010611070e0a11040e040c2c0c0d0605090906040605160c03120b1c05010c 58
    0x2043d459140041c400c4540101c9030740080c60800060308995150301c0320050018100c1e803280300808012402800c148030380240d0780000e00043d4860284691b41e82d80002c80e4070103c0760300e0316845076280b5102a0500d000c583c285440e000301c0c100c541c01c0200500c1449401a541c3c007000c900142510760b0404244015407a01081151688012920503481070b07128a180303450190000020f03100c001034090005103a03940034001c5444621081942c2d043e00d41589440e03c10911240300315940714628011000c40010b000041741358031496801440c1c0c400d110810660405072945005040c004084400740c4035041800030402803000000c1e980f4150012500e001099044018488440481c0c003405c07211100000265000403c0d40c5d517030102c000b410008103e514282400b00c15261386a0098a040d94202d140c0404544038181d482a8144184183d40351107199180389d880c140c0701d941c000984d409003217851308401e240a55400084c18582c109106004600d030310141401400c640c0801c03041c106222882c2031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 931709676 1250 931708426 931708447
    0x50102060712060b0406030617010509070303110a06020c010b0f06030c04031415160f02150c03100f08030714060103080301030f11030303042f0a090e0f150709060302 73
    0x9080da48001c15040980125101c1c050240040503c1e501070040f102000ca8007103425503051700014200c895410300d122440d814020b03d07a080756816180d000c16644000d0381000064010900c24215001300c03c2901d40f130b0003650b118030342640e1017000380541c1a59141845ca40a02d084641c80b02240c009071041d038110302d40040200c4062117130703000c0903010954580081c0301406003040310910904c000b1048039202e04119074801c2c4000f4403d01c00c000480e608a1100c0900e5200051545561000c00900d94041c0c03668105442d59520207031603202054a002d00c040750725040c0d41b03c03a50040c042c1c40002e681e44d840c00d041812207040303140b000410742c1d01710100400101d500641500d0540e5006943c0704c06044c0725242c244545c0c6450520b154040c00044100300903c0701c03c8200044030300800003544d9104840000311407041400500103940301171441001e00a0200a61000700b513021058121584100d460b41b00c1c0349031884200381e1000c03440001041100d51a4003003015001000c250400754107100c0d02e00c0c3d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 931710926 1250 931709676 931709683
    0x11a120f25020717010e01060b1b01090c0501050708090405010e010602070f050d03031d0703200301020306100809010e0a0b1006020307050a0201030c05040e040b01150c020f04050c070206131806050102 88
    0xc1360030400150b61000011202083d4040c083c4401800002c0103203640d202c05650198103c0ca0380010010703001d10401e800c2c0c00701800348000301a40203900d000b416041200650300b58100d000242c8000101f404998070940b19845018007810031113412034950742c1760003802843d00c811a00205054555030340104aa0f032110425910358651500b03020543e0003060140d8625083c2c9092035a90b94400c02000000340455007015034181c2e082a00b0b004461440c00041c1400c8c3e00c4182c030441e401501c0a04803000052040f1100c030780050070741d0000b15400403404070b03107032030030302c030940282c41101ccc41d00103004038184101107070401080c0f140041c500340071490312060384869001c807001c2d0501d500c800f10000b5591044040340c3c06401030b1241045e241c10142440c03007002c0c81c2400389030824141a412070000340d0240f00103100711540240458103010b0390342c041c0405400701600301403503104140304540060f07903030001400b01e42c0c800300ca4003d9541d140040105c510400b003a0720708103003490240d040c0000e9a022 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 931712176 1250 931710926 931710929
    0x7030203160f05120f031207030606030615030515030a08031006020a05030f0708090a0602010903180f12110d2d0b010e070c08041d0c0c06011a120f250207 68
    0xc4600740030044c44800b010b400c003201e000328440306000004045200e007003184ca900e8080c0303666950801c0400c0c1c440e0010343c110b502e107008814110511500da142054403d4101d25486055200d115900c0145880402e28103414150b044070300600c04403c00c540300000056980041807948001c00c0040c41913124a031300d034490400955400c010024640040c4a44482120a0a40041d04401d1081d50b2010024001c0091400441c0000c1c200c1c0c03081030400d25000e1000c8196454000300600c501e01d0b0844682c1281200d8034120351400c0c0b00c2022580c25942c901c10b40e9a664002c040000f640e44102c00e611000c1c480800402d48114541203203200810019204641554000100d8030805d03103c3d004c1c25200e0b07801011006280000000e0085096107100c0507020841c00140018401ca4941c058030344014003c3d21071410030b581c003c800421080340c8220b0241380c1c1c2810560381e146050001407a601c03190904888026141c03d10a05000c1100350300c0704054440407441400305498801240300030b4481015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 931713426 1250 931712176 931712179
    0x130611340f0c121103060709060909020901020708071202030d080c0a03051e04031d010503090312100f0e01050a140915030709050a0e0d0507080403060c1101020304030207030203160f05 81
    0x1080c1e241d030708220604076542c01410140c11041c508010500c2d0449181c40c0c0f40114500138010580452041405007080d1026106030b511a035511500b8100c41c50000c0d008101041e045102d201d0000a4030001400f030403014100303100114681b0009401458580800320350400100600d050400c41d05031852402d86030603207958640491a2703201c400528904c40001401801f01c001701d04240406c054101d4103000f03440072101d6101d540ca10140c00155014001225480006c2c0c201700038210420441ca080c0c95809401b0301d58800803242c80e581410288101508a12a1403840400500039071400da11004010929800c05840300c0c00b1040125200c018040c20648441e039007650600d0a682e4103100d1100070306000b01e07041000d442c0c001c103c10302405109291008500a02d20f0741c044a510a0080f40c01c01904645124606880e69a074103000701407910940c0b003005401c01001c00101804e0000b18041c40c001d500800c20350f0f046004140c1800b8284020703909003000501300708041c000f01212071044510 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 931714676 1250 931713426 931713443
    0x60a050313080c0609010e0d2f2803030b100c110619031a030d09211a1506190e120304120302060105030a1a13061134 52
    0x4182c544000c0034010fa0b00707260040d004480800100050540c0164a00400c0d0022204529004101a03551792030554880300106511040c05807000c0c0d00200c85200d0400d031340704640f10b61b40342c400c03601c080b00c202201104a4a903171022502c1071651600464082d44401c85d6440ca1060108030080c00f1520742d024001d01903a00c0300244d8080355a42025203051120359070205004000c204801001040c0003a102903462042c0c800c031140c54200050211071010440c5c8030b100105061079283c0b01c11600101402c0322015418140a00082c014102c1c0503119404c03107081007041c04c185070b0f501c98607000138050b94040e032020701c00c5402c0c10b50b2083d1203405400c0103080240e24801050085805010454165507403480300040003e8090100072242982c14000d90039908140d0300d031002c1548400314550041c200080c3c54036144254816922807a41100301e502d107248400c44240e68001c00d440d40100801d01407100442d510550503030390140564140701c4440700390303280c0d039615240c4d02e40129804005440800d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 931715926 1250 931714676 931714711
    0x301050901031115160212030307020303130c0506120a0b040902031009050106050a0b0a140f03060f012115081504031b0609151a0a0b090d151a060a0503 67
    0x1150480b203107401446003090340d80e0310101c9228050798645001c800301e02a441047c80c03080000004410349004a80710350156265445184041e08007480601c026212088808030003d22a601c4400a01c0c03941c122018000140c0352880d1200101ca035008040c5009030f00b04110314006036004208a1144214000c000450794000c0c103006006040a0b0403254010146640c003081007901d10014080d80d03281075540002d045642e0040e41c0b078034080c051035040c00c00820b001050711884d0003500062042070614103810041c2d200c03101c0d0300d1a000c0ba55540103155640d001c0100004003003031042c80140202200400401130395614030218050020300140c10016008085d81c0c0810004500354820381c3c118100f4007440081e8102549218078080b0b64034070345850402c5104da404032141003500c0040d0010034418565280c606400200c1d402142059806000f400d8510005916400710309081000c6c5100081d4904030302a00b90585201825020312880c01032090148907a8818112a0f02c00c203c1e688221015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 931717176 1250 931715926 931715929
    0x618050904052e0509070503121303061815091707020a0b030a20270906040b041e140f010b0d0f060f031a0f10272a0503010509010311 59
    0x18007920348004180e605110500805d500c0004240c819a00201d0a883d00350756291540ca1300c1c2c2c46900c0c1d607240314030160308003000400e0040c4d011500c800c002c80e070441c08841071a034501c1010000d41c00810526a43c60391f60b2418000c0800200c0e13a24100c1512070380c54a00560001081c0755564400c6070400c040010010b101035500790000ca17040404a4010502c1e805081002d046035002640ca001c4201d4515940c086c1607000019501b99145010b4070841c4a61a00d8041c00050807000f035510380c1040c2c0300c1840d00300c1c2c0c3c45c41d0740040f4a104101c041c0081d070f01402c05050509000054480030210051100520280c40070f0000c682101407080300015145c1e002814081c0079026030b03409080b442c100c00c1c1c1d00000b84401d10f46090841900f000c03120389035030b9032408054607901060b11050303540030745148140260149500300204040500e04000c2d10317450103411500c140c4002c0c111800043c03001072101c103120748580c1c6040e00d00407500d0412034250747c180400320707e00810510018101c806140c9076818213 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 931718426 1250 931717176 931717243
    0x50301050315180a0807031701060903260301090f11090a1211030d11061f050d0c0906090e0d020c0d0209130b090102030108150c0307180807061805090405 68
    0x100c1e4100702c1950446203445c280200c072500840002d5001c10700614001c04905500c41c0c00d103050b5512626034551042c156120011500b03031030b002c030000001000303120001c0006c00c1d4018500800d0850404184001c50a03000415190b01840d0644164802d008508003980c0c1e800e510820b507002c05d01440e0f1800740a0510b12094070134242200d406004640c031b2010000e80c031400c00620050300ca011903050342c40c0c6031040a0240c1c1d440d0b1000c051004454400e11280c9810700720039808030300070100510000e8031a01c100301118102ea220684081d5160170421a0b90001e12003480310201c18005000355013070480c0071482110424a00034480c080303e00c0016440c003000f202c00200c0319000b014a40440c030700302040034000e500030700508200344600c202106030207014215052103a801425000c3c00d580300c00303c0647e00d501d502d410030442461101000303c4c40c004200115402400380fa030700c2c0c84e10610005a00101640c164100c00d024184000812010a50020f2a02d00c18845648201a08031686051114 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 931719676 1250 931718426 931718461
    0xe090709021801030b0f01140a030605031203040309170712060e1e0709020c21090613030b0c04030308070e0a09240e0f070c060603020402070b16050301050315 70
    0xc5201080c2c0542200c0300e05164501240280c81c2001260404810001c43c490304910807030005959028001e02e001206000c2c08603a517450070302062031500c40c00013a0500c449180012034105012040000345a40500c08034024901c00b5000016201c0c00c1100c03e481d00060700034001e034070380819440300c100310b00744c0d000c2ea03480c280d1041500c506010301d042c0030046540080010240d4810040003240c501da151080b80d4410307581400400300281d600810001212840d20413285a44080c0000c149030788031180148103441481882c2082d1340e007945090441200e020b0584420140148030910010750465003013034010300d02c0e041050705011444005008400f01c0e80020403403d003408889406040948004c003510118032419180a41c1c481d01d043c0440b050031646541c0124400d00411301040c028140751103154016840440c00c5034880d0007040c143da014010441d102c0c110201080001c40b0308000080086005c0d1901e5443c42d40b50400081c0d603413140c00520300244420310003003009001e01081406 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 931720926 1250 931719676 931719689
    0x101d060112020708030a0c020f032a01060312030c0314010501030911120c03190215030c040801060e0612060405061b04050334050a0303080414060406150f0308040e0907 74
    0x41d602c0c1803500c2d004c895600151078880c0e80f5414414045c0007540080799003191140340c00001d50625140302c1c0d14184001840784595424901d150850220100030701410740651b004411004100142e2403009084801c803e002004162811640b80c0e032070443d03208001c0c110b070b0013403801007002402d5003440e1100a5103110841d92022400c0f80700c0c1e01c01200401c001c80d04e41c4e41141a1480e818030000d210600e80e40b0080700961003c4203403481c2c0d4038401d88101660304002c9800e0350720308061301d41202c80e007100c001c0e8021900010300341c4100002c501c0d05c0a201c02418600740301800030340c00c056491540d240303030203442e649000410020b4030b034076085807805442c000c0c03100404840d8654610152100b117044028203460703042080c095131440318489a0003003000c13a100030702065590340c515201200c1115014104440300380c41c0f0281d5040d0a4000c020b003600841c00f4060002e40c2ea11400403812504443d41c0c0300c00a816043c140030404102210300307450880d072000880001d1640c40925039810880c1d0340d004034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 931722176 1250 931720926 931720931
    0xf020d0f0606023c0c040e0106090c1b080a18080c2e141c05181506090406060e043203070807020a0506030a0203040209070c02030d030b04150303021005101d060112 72
    0x703507e000150490740403104140c41c1080346d110354502c111a0002241810045501d001d80c0c043c00040c1d4607001040082c01520f440114140c1d200b1849001c0f1145601003070301548542c60028440c5400803614954540000c03195010b58161100708040740c0d26030844000344608800c0c004042a04d100c126081281107034440280805144c3c41000240001d0b10a5800e840411070580081100040d4802540030314403c0b01c901e03907403204200801030600800880d60140c03520800035a038245449154091752141000ca40140003800b04120020704d034000c2911401881c4c10b18118a00c1c001c0308a510903500305001c0c90350b80c0104c0c004a421544903901c03080d040400002009002e401e00e034003650090784200c03098005600d9050040b64602040c0b44003a605070015803130b001d00c0c0d40c003030380c80054155805800480c0c41550b000800d6170032840c1e0390064015130884d01b804c544a40840c8035043d8450b211819141c021401c2c070b490003d4103050f001d6070032400707903201004c41d910740e00590070030035982d407001010f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 931723426 1250 931722176 931722191
    0x9020109080f031b0a080f0a0e040c0c03170601140919080307140703230c0307060e180f1618151b0b0a0f020d0f0606023c0c04 56
    0x102d03075030780e44002d811141d09400c04140082100b00801e010700481e0b0800106810107044103e000c40641c00342c0300038000e02c0915603003524107444901840780c4506254461006152041c240603240400c259031040051070140108103491f83c01c8005d00351002112960b0313907224a1510040303001001c86a6001c03c5007586108000b80c6d1050002c02841281d00c51044d1105044c840c04903c0d60729803507400005e108105902c1c207032001c668840062088a1040402c4410703c03406540464202000d43e0007560025404a2106e8003c2c11b04071800301070301100282c025280e15245880d180001c50182841c2150030130002007075001880b94907520740d8144002c50f000c0006503100b5001c1040c0d50744060900c04035500005e8000038404042c8542d40e425000780c41c68203283e444103080700c02003428482c8010540d5003484031252039150341c071694109490301c110014440d0304180d800307494044080c04070490754810500c1c1500c40001280d001c6103030503005415100302e000c0100481c0c140451410915003180c1b4080c0e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 931724676 1250 931723426 931723453
    0xf02030a050105031005010605190c0204240b0708040504020903150108070303030f0e0601050f13021206030705060c0c0405251d0406240c0b01030506011a0702090a0902010908 77
    0x70450482c2c008408603151482607241d01d000390b5000348100004500203000181d441c400d1440ca8010f8a05140b5000e54940d40c194005411116a2064681108002e07160310207114100744131b400280c0103460348242404010350f1082628031650103800d00030743d004a003141e840e40741000456000c00c0c078801c0788807070307981c5544869545050620003500003a0629089001900300d40c426800b0070700d4400d01900c02070707007090f051141b203102158003a900441000400700440006102418645058030429207075810400201450001260044d80c031a10040000706d011282c0003d000b9a0b82c40300b07960114155035010403c08250100700c041121000d03040c0c2c0d1f61030680340d01c1010505c01c4030088206445562040083c0012914140120855102c0d04104001e002c011450085c2c0101c41929050040124540c5c900d10564802e0b44112907a5008030700601a504490007803000e00c3c044174803030a00b070202c10f4002590140010301041c403d030360f6030118402507900c6901900040c1030314a0848010140d184d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 931725926 1250 931724676 931724681
    0x221061306050c03010510300f0b030114040f0807020909152a0c0c03070f080d0e1302090d0219090e060601020a03080702071a031609150509040f02030a 67
    0x222550342c50b000c00185100d480c001568140d841c0a09002c03022241000c080e102117012070300004052210820021407105114009003800c200d80a01059500a0841500c1a20b40c60130b4800c1c401d9041030602000f40071103040080c0d2143e049214610700c4400c5007068400d52042900203500102c10710100256503c0c005503415620340742031115401c41e030725510220441000d03a2410301e100f80101c42181003000c00d050160042004000030b603200c1c4c0039007000091500c0419800040300301034020b010000c410b07060040529902c088c0c14101100700382074001038120190008452116903002c11001e1083d15503c803e008502c1c1d01805049002c01c418804d00d41c690600d1183c86202800c040050800c0d4078081101030040c08107800600f2001140e95081d95540001030440301107104540002580200400200942c840a403a9080c0e8906190702c000b8103040409040609000110100b041030211000802e1210f48591514686a03080d00c00024060412041180b160500205c103200b0b0710b8102e603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 931727176 1250 931725926 931725961
    0x50f03071701030c180c08070e0112050f0603061605031315050c09030c150d0225060c1101051b1608070804050f0306040f020108060628030f0e0604022106 68
    0x50551441740c842160048284d507103115110340001c650a0100e0141e80c01503c00e021660014108055902e851301d00380c0f021204201c0d034030302501d442d0f6001d0000a0406101c4d168009030250030b0520031050f0640050050310014086e40a0703031105410350703800e0013800f902c2003510340300c00c11081c4081c2c20702c40300744172540c0c0024810a100703020f440c40e20841845c0110107074981c076203100c10081c10944a4526800250001d00395109410700c1c03582400c20324081d03c001c150843d4407558002904140501d0014803509884400d0b00c2160b00d0001400616100007880c40e061115038800c05540315128030050504030342c0444010710200000c181c480c1040f244c0c1c405801910f200f6034070150b01203200400c15aa0300c1c0103450182200c0c400442c60030155110300d078041e5004001400191400441480c04490b031000601002c250304003080c010000d0039454080c1400c101c1344120f051119481d1040202e454640141000b82315000d0a164604181e414403201c111880c4924150b0b07200e89070048000c2e0380e440b5030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 931728426 1250 931727176 931727189
    0xc08010e1b0607020d06020904020c03030c0a031a180403051c0608010b0607032a15240b0d020c070f1706010b040e0105060a030e030a1815050f03071701030c 69
    0x90201c010982441002d840c40581c00804160b80300c190382d03c2d444001d5105111168206400300b202c00704c805001c0000b0340c0203611900d106a81c0700c160400080c00c99001e0741d180c99408408102e400b1a907071380d0811200340b440c4440d901d40c0c03c50312145419921441280700002034010090003403031600003640c0c006002c9030807400003840340c1100c1200700001c80c41403840050103c1d00c08044c0a186840c040050300d0408210756004605038115281d80b030100444000030100c0c03540311112080030341c10420000040c04d4203004582c3c5801e0400000201714000c000d80c48c0740041e800f00380141b40e40810481c60300180000380c031007061192546840744003403207034044c01e41d240d100e0100000b52a2490754111400c490f0702030342e140c0c2c141c0d0038402000410b40c0044152020591580d503504a40c0c2c405000a05440c0b4075a00c0b46442e040c0e41c01c41f0400085d4050303104101480100d514500899080350485890005101610b0b940383e49192040e0f501040000206002c0d1034100004810860040d5001054505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 931729676 1250 931728426 931728463
    0x2030f1516050a1407020406171e061f0506030c070b0f060d0303020d0213180c14040924081b190b0f120406020307110d09120c08010e 59
    0x2100d154244407a41103019a00000d2020403400c00e500b44aa100750a449107560500f41c03030070351950005001c0d121030b500316407201004100c050040c0f90007007280f404035400c04a42c0d6240b06002d00803441e181c0e20014040c4504811103400700031a002040980340181c007000f400070b0744904142007024002d030814001242e40344602d4021603400010100c4442c45000018010030120445a0b82200a500300c07000c0e9030403058090103451010b94040107910090a5101d655409140000172080c06448105080009010f40300c041c1e50342514018003101c09842e49844045060412031480c84201c95003ca242e100c503a2900901080c0554042100c030202d1103051701c0300e19130481c21010043c003214135000c03c3e8802505098100995014400a011442a4220024144400141890344071001140d0071915070b41c2c000b0821035031981107801010f003010768030020904030704501ca004d41103a0f05070107500da0802c40100e902e0100400154184040c00c01c02009015040440840955070001c04104942441c2c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 931730926 1250 931729676 931729681
    0x70503030130080d0207080c0a030c02092202040b0d0203060403090f3507080712020a12082d07050a031e1704060b0d0c210f0803070c02030f15 63
    0x1032002103510b40c440e401c505154a020b081d402e880d8000c1d0b02c0404102c4940748203001610500d1400e11000318014040e46440000842a00c10000c2c042002400580d5486110401442d6403034610600808103905a900003042c0c2c800c440000d20100c5900e500941c544128001c020415901c040c0060440700d0360356000440c652207402c45044040d491801078458060207a9003600c0c800030080c00c0f01c481e07105009a81c0d03400d84a030301c05420683c180e0841c000111780380c00340300704505040183d00018031a00101e0301070740711141c5c0d0b81d115601c503030700c0a40c03a00b408508078080381902e41e141801c0008000030b08190740710700929050391901000002503012402c02e0801081903501289502404000303a5541e8901c0301d65100a8500d211001d0020340c2c1171503460360900900d403121391489000078010038894001c54501a1a0842840706101c1145076420890655000030070b04407505110035842403900f5101e503140b00c801c45911001c403801075031612414030021083c90011807800b0b2150543c1e0115840d48c4e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 931732176 1250 931730926 931730999
    0x40f03060f020906310602030a0e03030406020c01262814160509030307030e090a0c12021b15011d041101050913060b0a1e020c060904020705030301 65
    0xb4000d010007144c0208003001422240f840c2075404052000c42070a450600800000c110005003019030445005071b0300016040c84410b800c00d26500c2848010ad00071880c240c02d1210094480022003030081c10701000407103549820941120800112a840408070210710b030a00b090031015009a00402c915107aa04180f100890140501101034018500c3d45070a40c942901c4034079500c2c20380100380100001407000342000e643c14002401d549010380d55a0f001054454200030007288050704d1150b900b490075101d03055031341c0c010540c441c003c0b102e210016101c1c1c1019039800954984151061017602807103545a001d4040304552906076280c0010f40303682c0c00c8500b800040e14a00c10b5601a1201071041c010b601150300c1031004050500018100768040003e504050040e11140d80114001d0800810a02c50042e484100210b00c0b80b4103a818024045800034069152070441c0c1e041c42c025140020303c09099100c80d0112070f0076a5000080742c2c3d4035a540e5844803c6503554261300101031140e14850b5900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 931733426 1250 931732176 931732181
    0xe130b09031e0c010906020c0105010f05061c0c052a011a130c0219030801080d080f0f0a02040f0807140a06170405010b100831110a0803040f03060f 65
    0x9082c00c1400141602160440414a4100c0d510003503403036403220b802c40001481070010300744000e5400c0c008110303541000022650050140c106030301400c2e06100c88500c10700a4100060409880940000e5543c0403a10885440c0f00703d070742c00003000b80b62995440300b8400c811755400085100700000c004165140c00d121150404081c44107a000318503040c0c0c60100d406a901c80c002d192000d00480e035001240070200c00007450b0480c0d041e408910000010440340c001881102c44015142c500010146083c0301e0080040c0005010301c00200401c60000e00215100d90403140900310540385023620b01d80d92075499a803a1128040d080545103207540941d81c2c0e0404603402e10545105403262001c140c00c0c16925544882c2c0284250381c03541d00c0301c00034200341c3c54412070b0705134143d05942c9091541c0341c220040c00c40e0440c4103032101d8407070171303a0061105404800300e040c19040341c0c80f10410015854100000340c842d0380d1604019010300000070005010074080075400c04a92045600340440480064034008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 931734676 1250 931733426 931733437
    0x280b04080315190902090d0f12020d0c0b180a02060d0209190803040515070204060905180705090112061e150b090d02040207060207050f030c07140303090d0302070e130b0903 76
    0x10141503c00040c4003604164014111944000e40100000f52568468650311240c03000251003118084195400740342e418008400b140c030044c1000c00111081d5034a10080c040300409610307120790780501444a08805006504d40c40c0e40080c602603d844050206500a600c80403580c0c3c480d03144081028140781c0a0321044049820603c007450038586404281303d28080340100d18440b51000f0450800145d8640c86448080d106d469400105d501e0041100c4c0460007000801c2c0c017066206540400140d981c003598281501d603165940013820b541d514255000d084010500c1400a2031070154051a4071150b102004044000701c42503070203a61045007109070f108040d203e1340c00107030303c000100260074203400810250b840f52000600c0d111060300e450b07040401840001005820005010348010010410000942954058082622604e01c00240d603441100041400350084c031905105041c020b00070040101580c4000742468a02031a52002c07010701384a0840b0050140000f00f00d29280000c192032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 931735926 1250 931734676 931734709
    0xc0307060e0d0605061207140103050708040f03050c1504050c0f0a140d021f1706151206060c0a0c05010212030108030a0c2405060f12280b04080315 65
    0x1480001c1902c030300300136000c003e284582051800d01d1810030440d003046076900403c1c1c10f540980c0d41341c0d07403500010705450020700200e0411000c0d80034000450101e4440340030303450f49400e00503540d506000899060000352000d80d00386e4904c1d401003005000b000f00d80003403240000c840340d0b9460807445040100355a0b00b40501c7c41c03c089817040120346030810b04800c840c02d0340010f010403914807050784610500080e40c0c1c01c0e01c001881e0310150954124004e2003a980155046800442d00d45008403100c80f940285010480c1200d404004103040e80c0b035030b604540c02c1200c001c1c141c1d92070b000709080c4060103028500c9140d0061044080960410b0444410749040c0c5500c00003440c94000c0c040c1d401c4851052a01098410203900000149000f11106e1124681c1c900414045032a151080400c6845c00350070320154003d07000c1407a47c012f00b460101d418899403e82214601c032500c40315464002d00f2001d590700a01070320300349007804240020303240503503c6030700d0100040380c41904900600606100d044140e2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 931737176 1250 931735926 931735939
    0x304031211070602030411030d110a060203040f0605012603090a05012001020a11071406030712060306020706050415090c05060d0f090f12020303010b04030b06061b0c0307060e 77
    0x4001030042508840069a403440106041c901c25486a034100c0c4c2c004d8804440409008a24091905083c07010401c10340d46810038542d92910000360584648980f440240480d50000005003004000c54800b00a02d4006500300041d60315640341501c007015800900f0b4410310342c448407104c81000041124070040d000342c0407a0680346441d005646800c400090f102509460f5081b81012040902c09860101d05a9844003005030102e82228104a800e4001d0000c0d225111041d10395500c4441c103c2e81c03c6070151521814a0840c40a0980100056000100010700004d940010300c54280c0141c1c0c0180e0041612190760880c040d0036130111140880c0043c140c0b5065481003000b460820050091420030000c0800e00088040e01c3c43c04450702800212110500e0003845010300005072020007000344140011465035041602030501805144030043c030620f0b000700001c810740c03992400d451002403180c6811418600040e030084e120320340001c607103001c1e1284d40c0c00010707064401d0900d180e81040c0503018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 931738426 1250 931737176 931737197
    0x2b1805100e040b0904050d0f140405151606020a1b0b0106080c0c12030912030c0f070c0302270709030b041b0b1207020705100512190609020d060605030403 68
    0x94804041034084182c0c4559a81203540c55503c5040040c0d1003148100040c050000c0c0180002d0301e1a010900500104488180950709072000d403070484054070022280300c06000d01d41c000003c414400e000ca441c1704a08108200d4080243d65009051000381e6900c0300c20300d204182d00e04010031131400802a084404090041103094010b00b034a541001c1e10f812800d10b081c80315840716181001c000301c0c00d080c2d4540042040b4000e4024488010b540540c0c1301d1103451424050f2905400e40a291215544282c000925000300700c80c802d4041d009583c06807802d054580c14001000b40e0204550400892113940340c0000c00031880340e030300501034983c4a0250913031070b16941c450b42a2440c1410708911a003c0340c54011480104880150404010a4030780030480d1601200090810700c2d00d9104078082c40d44015416800c070342010540c0c55100408140100b80c1d40e8041e500540e210a1108900019141003c0420400603603001400c00035001d5206001c4107503583c1045030380b84011200038000800b6840c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 931739676 1250 931738426 931738459
    0x70510020604112b021216060e0a1809140c01090b031506040e0403091514030a0f1a03070b0405181302100503040308090607050d0c022b1805 62
    0x402c3c00c07090402800e040381896424522100100c0302c00c95a0604140d104218011442e122180030341100514000d05030080c41900e04146d80d0740c881c0501030910030402d0f4400400d845984404c001000e07841c102e900d4080b004039040c0300030000150143c801e003805c07462441412000003080d20200d041070307540700002440c2040342d45560f040074012401040d0319840171805035032450007030805402e0f4289005d81a00781898042c4c0220765540c09082071030f841520031624250492040b0755048400d444c0c6540e2552141c640400400d1608000803040e40340c40c841324807090450b08440401001a0115043d00b511100000700030b000e28132825038803581400017108001d80c3e5540d19600040b2030b54400e18072500c0381d4005090264850403220000d003000c002c01c0241070b88600103a1b0410101c0003d490725080c4440c00404c0384c0b146421490000b521005500481c0d4420003a03403180c41c1d0050800e11582c079402003c4400c000050a10f4800101131803822070034141c15544840813a007004054100d004940300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 931740926 1250 931739676 931739693
    0xc0a1a04051908040923040b0106091a122a0301060f0503091c09030605040615050609010e010e0a031b03210203120403050418140a090b040209090c0a140102070510020604 75
    0x8a40d1070f0b20f800546c1c0c0540e45124940c4d407280607501c14a002001507041210007001c0000030f0380034070407030605243c1c1c4141d0100c2c038000310359074407501d422a4207942c0d55208441000820343c200c00c03007100400e0308010b06110400c00255058603d540e48090b54016200c4007111540001d1743c016585030088100210302e0403820240183c03111660400d4800d031030381d039221041100d0045800362b03129030b2200013554040c440002040045e00c4220f4120341810301d2500020210b0b002100e0b0207042c84512282030f05103076034801da48001594001c00410b0344008043d0348ce0810001403100319806c0540300e20507040c0c0c001800319000302c05a41d500031810304d100c54a040c10f0301c00c009082541404000c00010941e8044d045000724030580c00c68012400c01c039244014802e1440060400243e607103000d4184000419006029810a8045889011a40b5007010317050070aa10f41481c03c1c5d000c0c0b0007500014190410f00040c0c0d10240c030903000d5410b20b9136a4014002e108d18420b5020300180c020000140000f000e10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 931742176 1250 931740926 931740941
    0x1b010c0e0303180d1b060e18130f05120703020a05010c110a030f1403011d0601091404202d030f01031e02030f01060f09061a0c0a1a040519080409 64
    0x201811580c8000c43c2c06030081c0215150003880000720070403541c0a81d0304120071600d02241490180c052070327181c13800c820210100c413008010188042e408203078040c03080412941401140707490b40e40380d03144a245406955040c840104071829420318030300303500d11801400517400010301c807809040040a180d60481d4640315260b1010107108070078603200c08800c00c8c6405503000e0080711a00412001041c892141d0291000301000d04200d84903500b4410460007030001e0f9043d0105942c042550503200b1035220f1200b006202001440102242e00501010b04030702c51440d403121250030201002400e01d1400040c4401c403640c0c900c081d400030040000403200c03406e034015034820300e012103110f481e1075000070700b012409002c000d520381d114182032113100c0300118244001d26002004210162a00c4044480300d450320401c0e000c100004160044003040502001508a40c45603090b0241c91061a03014540381051f14243d989108000e052060080a0b81c10120721a401010b01402c0901d0098141f0240150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 931743426 1250 931742176 931742183
    0x1a0606091203040e01060c0521041e0305030a1701060c030203030f07020f060a02041502072115050a0218010203090d0212030d05010308040515161104021b010c0e0303180d 75
    0x1c02000442c8513801c032100c2d001c2c104564400941d6807690414625054900e5000c015002c040340c9045003c0d00400103e40c00c1b208142c1c00c442008440e010b0015040035542d0026055001c005200840192700034681811404a04049403d50340c0300d403802c07944644883e00080250b130080000c1962030401c0540c1c1c2e580300556204860481d134070010454200b21007030365220f025a4003c00d085c0544180080036104051851008008091800000309071260712440c405d646851030307460780820700660025020988411a106000c541421405040250b121408042650041a5002c00c42c0d610200440b851300e80002c040340d207400221b40070001c59039811a4040304511080010080540306402494020350094000544462604003800313a0102007000c0d820510a08224261494842202c121803141c1c00c05401300140b0442c0300401c2c000d01c18074003c4c6007e00252200e5034941001500001c5600000b070781c0302c5034681d10704030030306036280030309619021030012078401d03441c082c1408420010118013 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 931744676 1250 931743426 931743433
    0x30f020d02030a050a0c090b0604030b07030b121b04020f030a0f061707030b060d08030c0a020102070f08191b02150f13060e0625050703051204031a06060912 69
    0xe890340024503044028500329110b4106144010074003c0241e090703030003064440e100b8030400140000081051145000c000d109101a00202ea0a284680e12131109107202600a120412201c071110b1745d65201010008000d12482500000d2802c2a0003900d12540780f400315181182c9074010110090540200c0b010f03100c0746c0d1000d0014954026440f030801e090b465a0182c141c0c1421400c05d08441c0c00c0042c0707200e0107006020200c04c00a890300c8110796101410305811505c452107030300304901901c10007101401301000d03100360f00c090140314001000e0b08000821006081c00310001d00707844420343c0000c810000c02040b85040050300b04500040a2122030088152600d005880300030981d4100e0403c01070150070008041c4400303500701e100c03602512011542d0038100104070b8801d208400012040f151800c1200000d041004002c01113440519480340c20740e00c1030f424a0707640100a4001d80f005540100d940034081a20700d920314079640c012540070b0010761070b102480c41400060707624943d0168581c407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 931745926 1250 931744676 931744699
    0x9020a0c02060406090305010f1a09070221190903030e04110f0408060601020708012c030d0f05090717030403020f010c140c090711070e0621030307030e0a0c030f02 72
    0xb56100c0041001d450251580901c40707045042042c00c65080c088140c00c4d1615000c50725000c2051007030050803901084540c3e08055071442012810902410b515103001c0065855810414480c01c003d01324090707104003041c01024504008840c5e04031241700240110308070241c2090241015040b010100d207800d01e1581c03030708100500745102c6a000394007030f9070742d40c1103142800306940c0d05016100040090000a0083c016200c00701040682d6000f000b8907402d550391000a8601c0040c03050b44e07030004813080f0810038078a0181c1c404000d400106e6400c4068025098041548660034140301c960040382c10045080c0350446c1d090014401100500d036052094203040c00c0c0004407c8001c508256040318054844007400605020301c0341000f920700e600740000503040c0c140c8038200088001c100d511000f00640c058441c280816141c548500b0007000000c510700d204e1602a00020045000700d0496508014003503d68a003152038007410b00700200820140c0c2000c00210b5083d0351820b071140e00003400c050000c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 931747176 1250 931745926 931745929
    0xc05040e100306050f1506030402010e04090c0e0903040608150109030c0303020c010327060c05090303070605060a1719232506090e0901020909090303010306200409020a0c02 76
    0x40d011215440071401c003410a008101e120b01400303804c03100e10008101c403810b15070014503c0e510b44c801d003203001c0c1401000150640e8410703110100d5501018008101d40780326420103884a0040c1d0181201006038417010540d810b400208480891340c0c41c0c0d6504180e604c80c060740f072a040714040e2516041286460012000c03a05050841d4029403003500107240680c510000901615203c940041d01d400c10340e41080f151500c80441080c0301c0da40402e0000b0520209c940c26191030140c40740c03e540501c0301048250800480394007160050070704441d410821a07982e591040144124084907a8a41181c2c5400b60a00c2c2d13211200c1348240d101d81040684043c001c840d801c60610300a03504d600603441050705869011546845000048000112540c11820141c024000801d00d1140c813001510190000301020000e50603a083c0340802850100c69007002c03903089540390000e000550764689896441140e91a1125500c240140c40402d15400d045c6014104c80094020f079070a01c0c144896070400380c006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 931748426 1250 931747176 931747199
    0x16120b03030c071a130b0a090f1401020601080f191502191b0302070501050a09080703080408060c030103170c0a061401090b030f1e0328030b0915040c0504 68
    0x10100702e4004090f07a510302920000800b03d14200e84645070000c20120361924800000d132019240300600c1250794000310a011501300300320b603001074211a414800800d001ca03845d00c0900e228034007682242c0150741c07207202850b200e81d4141200b01440d4400c0c180810004008000910001c1c065002d8558102d114030740e1206907803040f0010240000107182100501c0d403c10001041000420801c08040403143d03070103960b906040c0a1941400400b14a013111188541c0d07160001d0062802512601980c0345011007481d00b080c085c01c90a4000c4e41d0000b050f0000c640d040c1c81c1203a40100c040e4081c242211803180c00359001090146a60055040d8030002c10110700555110b1200303018520410740c58024054200c81030322500c40c0c82500b202c10014070142001070b40d00d4040f54078520780c0c10843ea50144c0b0b40d24500c103c6813803a105201180c11203400e401c4e100d44c3d0485c0e0710102d8030103200100042d020468404002c851002000c812440c2c0c541e92414aa40b0602d121a03460400c0c030316081c8c42e034548458 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 931749676 1250 931748426 931748437
    0x50102030907050108011d0a0b061c2003040503040501050a0507020d03020a0b06060705031e09100305190207080315030f01090c29190306380316120b0303 68
    0x540c1e02c032203010069075074001d11040c01400c441c0215a011480d07090510241d14000c0d0171203613556103548507464165030749000c44808420009a030114800069440009000e400e09100d01d5108013200172901c0302d03c0c100499100b41d40c000042c52403d03041200644094011081000800406210440068a03112000d01d071641c0a60001c00e8040001e01d049091850001c0c4058043d40c81409072400007803000040d00c0c15204c0e1340c9440e420321642420700b4140f13801100341140d440010101c41c01000b03501540814010841d840d003900500000a1040041c0d00c02c0c0b40c2d0042078440c040000545d102c1082218000c41c183c01400d60707884c0c5000c084080c2c2500d0391480b0035a10444410300030824482000490140500c01e2103280029002c1c0209004043c02020201001c0c61000018a1030552107680440081c0001a8a00300310b50b1130b410200500e501c004e48020404140b0007040d03004201c01c07209407440b41c440031040c0b018660403488110341c61007074220010580f03901c81c0105022550240040c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 931750926 1250 931749676 931749691
    0x70804051203030a0e0d09061b05061602010c1409090403090f090209090a062603250201030b010309240b06160312091203021b1b0a050616020d080705010203 69
    0x1912424050103030313001c8541800000210703502501d24204034035041904941142e0050416254128a0104c510220256440010181c1c0202c0080010340410740c2603600000002d6030003000b40d11440d40c401d07500050351034900d00d141181400025050326003808640e5000d0f00c81d281104c102503640907045c00340c00c150303049811b0440d000306800106061119420381c2c480c60b5400c003407160354900354506035000c000e0641c0f104510044000d00d4000705081003140c100c1d41890400d0900000c900420302c5560840f000200d0000381450720506031903109014034689550407071981c9942801c0d032049242103032401250419003e44425200c039156a45a0140080031351400380000c4107900c4e45002400002844144c00006240ca038115020504c0d546091850711914140149d40d4608203029030072040c4084031540061152840014030304030300c244180c052000c290390b500e0300c1a4940d420403403540a41825080306a1280261001500d00700c084046101d0050b007c0e1860644683c031070b2802d9034011a80031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 931752176 1250 931750926 931750933
    0xe0f0c0901021c12180215160c1e090203150906010c02030105010909020405130f060c1b030e0111030c03030604021b030f040807060c020d02190b0c01060e010e0603070b0708040512 79
    0x4e00e0301140d240a4002c0c0c4c2d20460600f640808920350000c1e500d902102c0c0d4120b504800440c612016207042c000c01c0404039044260000e21507500e142c64100007608441005092181c02d4000440000500030b9a0184440c801c6425a030500a01840116a0000e00282c10030a1400f40740015032070a210308e0340078044902010602418a006000039a8000b0701680c3c4888242601d002c04101d01e4031408482545c04000814010101e6404407200d5501622624901b600c0080350010150443d500205030340b801e88951540310074a5032166164000c840044045400c1000040d1051400354010042030b00340513200081038801c540d0841c6960440c0c4118401c0840000d024840030700e0401801d4020400c0d458a2210003080f980414000303407290800a0050700002c1780d2400380b42c81c004031107024003600400c2c00e840b1541400014080c01c458400c46540540810010440b020220002c5110300c0000d0010807180b481c24142e5a1250301c072840a4588003014800400d86070f0b1021020640d5140400c000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 931753426 1250 931752176 931752197
    0x303050d0c02030406090303050304080d14060f0a052413081f020301120f0218090d11070302010f050d110a0e0f0102010c270314010c02070e0f0c0901021c 68
    0x504048441c003500e44401e541c4140020000285e20401580c252941071800b41c1d00c82c0c4451500003030318041d1355240002d0340d04110304a03c10511034114107100f11400c03190040190118800d1042c09810360213169007000000040d44c200d0282000e5080f00d089000c84080c1c03410360203142400d03c403072454000302180d40003001c42349690103889000528a05450310210f00d554500001011072040c1c01360000d100d40071101481c410355503070f0075240e1030880c2010b480004614000407141c0d1603141169503900400d0180264000ca8400018020180c9070f060711800e41d00a8520400e883c1c03900f01034000a03800c0c2c2c60301a49800d03001080b0152246440648400d01c8020038901044562111040d0f00c034116031401707500d111419481805031600854910741c0c1103c819184840302171203030094001504003144d1141c2d200d04000154004400340c2d0443d800d40340c006449440341402c0e0300c000d5030700240508540c0081100c80b1001001004010700c140129081002c5034400082c40d40c80340441c880c040703a0342410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 931754676 1250 931753426 931753447
    0x31b0904052d0f27100c200a02040b0a0812040e0c0306090712090b240117040b0a061203020a0605060409080d020c0a02090f01060201061a1918030305 66
    0x2040d070144406400d598041d072900400c2040c4041c40102942c1d443c0b40b0781880400c0e40d03c0a280159580c44240341959402c40b00341c0d0001001e402c10400d40b1002940e820410707c2075548615100ca20181003501406043d070854003004007900c07100c030495910030071007580054101c804002e0402c100700c010070119203551600c4030744e000d00701000782540340c071400070000c0003002c1d910220510b070302801d14186074803440d0420004400030804602c00500300f90f00c070410b0001003084c100c0e80d2040e008040503522205a021001107605c109140d260410006450002c03500003a1500201c0c6d6000140020025100755504410b803e100b01e01c3c2c4054015800c01e5403010140062070050710740c044d4083d1800d000c0020b103903507100c2c8948550040c5000559011545c200c44500510800c40c2e81d42e00184600304904007403031141d01c600005e1158002644c0b0302140010328103000c03c00c0642802c000a00c8a007466010900f16000284c140459000c1120551403009008034418070040954002d9668035210110f100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 931755926 1250 931754676 931754731
    0x4120302150a0501150c21050c010c03150603020306060d0603060c0201050108120417070b0c100c0f210e010e1015050a060f0504080a0f020112060308031b090405 71
    0x30038032107855080000605c91800f40d140b4801c4584203614251800b05120b0034401c0a940c1c5012000c0103001402e01b044000591040c09045003102080080000548102056045605944604050b14281c65082203040e0081d070180d44d20001c0070702510305c0d0003200a560001c076803481e00200d5040b543d80742456151642481114050000f00c0000c0444c0701d40440418514022407288103101d580e00c1c2501c0c00c108500740b0049000344090084caa1729140c1304038505859000c04a26811100e141c6011035040c1840344c00700001e521a9511800785820f00d48002402454007050780309180c546450910700d00300c5092207103400c5003505901a010780e1388444050020f07038a0391840c11070110305e0300c2c0b07044c012a034421202c0011280103090040c019050740340103881500607580202d40e140148040c08090112040381031140310700c01d0740c42c5c007800c0c0560000c00c0c00302d034400d000c0a0301c3c0400c1400000c0080741d0500c0104610b080c09d02c03900381003070140350006050745c0c002c650040c0f442d1900b6219444990403c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 931757176 1250 931755926 931755931
    0x302070b0f010602120d021201030c03170301060c0206090409050a20090609060409020109181b030203100303050c070314010926090f0a03060903020601060f02030a02060a0f020412030215 82
    0x141c2075000c65403400400039594002c14000d81c18840d000100907884003140d034100e400d001d4207490b1034080da41e0740303042c0380290443d2132005441e000c80f00d090004514007098122410b94610b0b0300e0302072001500d074013800113582185074929006541c0306c21850110340100652000648100c001200182007a11121b80040c00b25005a000d01104030500805680d00103c25600c440156000151345200b4001295030700c000740c2c00a4410f01d42d5141503003078100740340c1001c1c0d45400040b0842d80701c8800b0100c210200d01c03044503810110a681281480064814401061030180040407101044e07103e4940704000c0c04c0001109285a640700640400c000c003003000090580c0c48000790800141000c44000050700c682e80c5154407030120051003c07081c3e60781c052100c4c06150000c40401c40e00580c0d00d0003175a0303008280265808982b2022754502e041d0710010448030b000c041540580b409844401c060b802a04100c041d00705844e03024400814417201850b10102c026000e03a006015009070001c984074420300c007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 931758426 1250 931757176 931757191
    0x50c100f120f3b191106040924080604030c050c060a0315050103020702062203080a0203030402040e070b07061508121903050123011713030908150f0901060b07030302070b 75
    0x3211020201840b02050340c841618200c0004100c6905524002620b6040102d510758411800b19020814070030030f9009c0500039200c0c44c1c08013080303200c40c05005040382c01d52042c84e08a6100c200000c00003881b0744a40c941c600d208100700c0707a91652460011784d09400164442c80003e070350704481101e265001071010014a4207090031860b02040341c0218155100300c0507450300e90301c000e40303501e60382c2c3c1140d242d00c800440c3c00034009525811295030080d12540182e400380d12590a0800d034114120000c180b0f4000c4034004d14000b441d01c0041c0d900c1c00c014001c8a040010020903030712000504003020b001094285485071021690340c4032244603400365030541c5028008052a000042c0b05940402d0040300c0801442a00355610b400303003400498501d14180f00b6025580482428042c0400840c080c642502c0d100c0c2d160510740f103440c0da00065540d6811512143c80c00300e5100460b054441d940300c9603030170001c900004510f207030b01d46035450f0990340984401c0300001da00044c000300340408641d80d00d130001caa = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 931759676 1250 931758426 931758521
    0x210c0c01060f0f0b0f0c072c06010f0c06060503060c070b0c0f040317070c090c030e0109020904030837051509010e0a140c07050c100f120f 61
    0xf06050b036500503500380120f0641c14000180618100e04c2d860a0340c8145101c48121003609854100d04610049442c01c020031002c00e0745101603002c4104a0120b10802c010303524000a40c41d56001103482840b5210159041d0b680e80c170300403804d41c40501400d8801d00d8012078850342d4081b249810301658400400041100c902031002c9031055a065044a00b200e4211018904007035055807031104600c0380c250300510b4442182000075403806103030094014002182c808024039005000368a09981c41d0000c000e5020242000250020b80144500c54001d00c1e00b2100c402107a50f20342d00035244030200c007200030360008400346507a4410414007556500520f6424000c00c10080d80010860070881070081014118440001801d030740b0017035010529991500702816047e040c4240202c4259001180c02d5900b809140510b00860a1243d0f1401b80e210303d90755008022072256400300e910351405070910034403580703031620408402d205004109a4040300700c0c040308100360000b00c40c038480070710180342d010409 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 931760926 1250 931759676 931759679
    0xc10050702060610081603020c0604060c0f020309011733040c1115180111090a05090f0106030203190212100f0807170a0c0f0905130f030302210c0c01060f 68
    0x80d4004180303030b00118170b4070301b100d101000b00406030040d01882140640324401d000400c01440607030b800031840c0c0800da0700c403842c43c0d002c0800d00300d072030340b0076040c080d4003040d006541c0684100140c2d100702e50200d50034911202409950248015032551500326405d040b45c0e082c02c883c2e50707251034800c0c1c07004913016090000844070040e2616846401d540c4800100e1400440092803580503042300340b60135078061000b0070510f40f9400d0302510135003001009a004007040c410100e65400d01071541070091814641c0751403e60f1030104110080e500080521017002c503200450840448a40007500d529078021603004800e18006042c0201d0942c00ea120801003a81c3c1c502c00c0140f24000310301c070b006a030b800c409901d442c42d802d00f03102072510038804d000805000306c100001034828410100c01c003d0300c2000c00706101c42e1b161080c5032a00401c001c81e024001e810a5404100040c0c006c0c0e00800c0d00394859401d034520500380c003510006980302110300c00000e0b50006541c280c148028811100501005d048400b1050b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 931762176 1250 931760926 931760959
    0x1060303051b010b0f040c1815090909051e0a08040b120a050f06120a0503030106020d080108120306041a0d060507030c0206041707050a0b1009060501020c030a0b0c0c100507020606 79
    0x349175108038080d40d540e12195405030b00c01c1e40e090400260310001c0391134541daa0320050340342652140005000a19a44022038800654040c022007241c010008228014144501e10102c50042000042c5445180000c00002c4c0c148030180c8000d060b105030712502d070f000020a24414400080244984d04e25060030482d580031140c01560708010140c7c0d0f000540c0480007011403506140ca24054440d01c000b00001400aa0015450040c00055507a0064a903650b4400564030000c03011504442e105c01d00c0000e00908041c1d1203a5031040010180072150b84045004c1071005080c60000e44109494108002000d80c0502940212010b42d00c0144514075050311499802100c8001100e822500000c101041c0081041458000d5401c510249014200000d50040c4a60030740714001245007802c138002515070021a02d0021100003070080c0610a05560340c15210f280002c021015548040c400e42680080401c0a80d08401510100003203d00b4000e00185c5006402001070384650724000a00c02e56 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 931763426 1250 931762176 931762189
    0x5030c27011d0a090b060d09060911031609020901090b0d0501030b1b07060509030c070f0f1703030601030902060c0a0b0609010e040c1205010b10050702090c043501060303051b010b 79
    0x72100764500000385c89000c000052000d00c0784168206d42c083c1802800400c0c00b200d0790240a03c41e01c507058400780400c000c414581ca0700e50300c0ca84102172800b000c2c0c040144441d01c0e00100300c0f4a0051501942103a01c4144480340ca801912400800a549000600800803640512900900801841c01c41c9250103a140b01c8103100c0c0113001480f0f1604d03400032407440c0201f0410788400c50010015240110785602c00402c3d07030450307445040d200d904806030026440ca00d040c0c00711845a00b40001e035213196200001500500340070398007240c2103d01040007131455201400b0610455204144c83c240906180040251920060700000e0003102c0319824030000403407044e03a003400c03114000c0502070020301e076041c1140107080f0200740c0ca41090885050310031040d4440020030a9901c22200c500e042e0b115941602c070b0034041c0d8040ca480c2204d10403c5189142d8800781c02c00e00000584808006582d0a4103a080c03e60b041640100d0100740c2c00b04089110080c40303100041c141c0400402000380e1030f01c0301c000420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 931764676 1250 931763426 931763429
    0x60b090604090906090803240f06040501180302130c140c0c210303040c051206060915040e030c06250806120a0210110d03150605030c27011d0a 63
    0x4207699100550340420100d41c010311700c81074200000340c0c1c80745000c40c810354680b00030107400b03d1404070f035a80c660800d15000800c0303070003c50301a120508103401c100c0150382440a00c180b90600f01d1034110000016070700c44c194050080008840403c42c08000031000d07206030f46040d10740344483d100780035284044000003000c40d0308001c100e84c0c89440c84090540340940c0304c5034040f1400c150100108201c01c3c8034200903c1803c454082e140c2441031641e1040c904e440c0c02c000e680e410743c0301450708089128404404404800410002c10010f580d00e602c0312400c1c41c0d41d000c0384441485801c01000c00620334880d00c030500121488404500034010750340401801c0003001481640300c5c07482c0b00181d00c1101d5080000034001640134000e10508074003030074040c084584501040003e4490084459980c3d4881d004002d41200b0b000054403a040c100070342500c181c1c000030a912448130092054074030714950494800e4001e030724042034001c05140000010b180b0300d54003550065840d4081180d01d4a80c80747e40b00d100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 931765926 1250 931764676 931764689
    0x1d0108040825080c0a0c0909120809010212100e09070e1f121b090c0801030f080c0d111b010c1202012c0f1203340201020a03060b090604 60
    0x191040d02c110030b81090076004400381c941e6001007409940c600000452035881d80c003621015030003030f564880349001e942c03079074100600310b00385000c00404080c060317501c042d0415140302c005810035450340e800ba2142c95084903202d00c0c41c40344200802100007907400300d0b6001003003203014180d05420a408080d2980340078055614503000c10800d181905503046000c4083d000d407002400400c80e1790b0425841401d155085414510340c094030010310204c040c41907a1500c440d0f911408903680c81c41e05e0305074065280d180d06a0300c1140812420420700424009419081e80980312a20320040c015506413405d02c0140d29403400011030340d000780c031580e004241c1d40091584118141440342c0317503110481c0901300c1d8039480018400c0410031607400003602810411141d120000311298180200c402075031fa0301c41e0300c0e06c0d1001c0c100200085041c020510300d03010a54040d18184035803d480603034460f102c0d102034902d800f0060b5804595403102c00c0d4980148802040c00f00800c60428906070001100c40c4201d21508 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 931767176 1250 931765926 931765957
    0x106170304150f170403050702120c090c091023071a07020a02220f0507050c10050402090f1503030703110c010e090a02071e03090512120405130f05071d01080408 71
    0x5d082510807021070b83c8081c0d02904541d1f04600c2030b5802c80e030710200119814464200c000020310a4456003085e0b640c000b078001d0040100800d420350543c0c411908550040c82101d840e01405040d01410340201800e40c4140f0300740282d540c840c107540300b000c07401074026001c64200c8400403015075180320903000341c041c2400ca2101000d580e550428000e10300b14150707546142c180020080050b802030050303d40750a24a090341c0000d1268640e00301101e2003190003d41c454102001708091642d42490b2681c480385072400c01d003d1440540002c2d2031038108100031400a117049a124a5420007400401c0f460802824865075000800b8001440c9140040800007003690124900342032241d4034155214041241d0800d41c800c9955080043c0342c040326018103806054216400c0039200d4000804541d105410380c426402c3c207040c0070400064007440c441a241d403e0b210b90550804803034622501b40128640e031200b2100e110000f003095024410584914103001040003004086030320802124095000a01d44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 931768426 1250 931767176 931767181
    0x905070c02090702010b21060a0914070e040c08060603060a0c0315140102010c08012301050405060a081005011b0b1305070e040506010e040201200106170304150f17 72
    0x885610350040c0010750301140e010180039410750103501c12014014103942c03040c0340e40c803c1c100c3c1840d030303880b2164110302591102d070014030502104c2c1d20241540b0b1240d8021250102c42810991410f4840d4000c0d042403144030060004209a202c0c10100a00300d103805000f00389810700000c1c0d15160024403810203a40c13121190384a0600c20303448004112040300002d00a50303103030003242e00c00c0c007280e489090140d0320388207407040c0c3c04d4012604c81d412107942e2181d10200080000f0068000c910608100d414440184404200c5540358400780900c0038182d941d06910749428100351100f40640d620803814895010642c0c00b0144110310f4020041b42c000e543c0100c10f8032160307207244407000c486101034040e0041100c0403420302600c07100d55000b107000758200c500c1c0ea40c8070030b0038131600d60b42510028049284c01d0300d0410002c2e02d558682722030801d12400055004c0d80c50341420a003a82e502c2111220f50030018007030268a03a030f04103800c40031030b96241084d003410050303078094154074980071b015100d14240c800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 931769676 1250 931768426 931768441
    0x207030f051f0902181506120f15150d15080a1505090d1404080114041101080105010c03031a0a141c02010c02060f0717030708090c010210110403080a0c020a090e06010905 75
    0x320444600c40540420794030079444601c4071800301d0641c0c84903080c1401034080b03004054154014107032404000c2060103550039000c03041081e64400110310310038940b5401d0b8a030071190b40107040d80c01050307540058407107040700d450c00b403890840040051042c02e02d410107004080000158918069413641801103001ca1a082c007034500d4016507001c10341e95802d00d8410042010b83c10440d600551141c9002c070301e4040d50b10010b4640b0f58003401041d00084462104501183c441c0d0451140031130340845160103000303500040394400c3c05903081104013042c502d43c08941418424000c034203600000003201d80b480c1050340020b00c6000707401e04c0070344200030105a40101050034021240c0c0c0319480140c12a14000b20703c0c040303c803500201c1d901c3c404101141e0001d8000d00d00410345041c1513170141d000c2c04407035824461582c01445c4650882c00314401c00d000210010b5059030050030790010079241c0400040c001d10402c0f40d40748290b0040785c2130364103240e0004500140041e000303064801e080c070046025501c421 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 931770926 1250 931769676 931769701
    0x501110d0f05090109051302040302120a150207030c020306090d180b1b030d02040e190e060f1807120b13050a03080a0207061806060512030909070207030f051f090218 73
    0x1b044280d00200d29144003880c101650b00030000c992003500c41481503a9600045034a46c60a000064030405481801403c540c0d015401031404a21904011110549075000300c0d14104040790640500d03403202d0107507100c0360b0b00404410b09642288040450f03060134120303070300f2541c0580131420445006075407400c010b0050903c144e8207071a803404811500d07030b556802001c0d02d10000b5900725413181510320748292600e4190103915110f182c14402080141c841142508007550010280c042946003000d40240140040c0b240c1c4004009600c004004c895840c00e02c40140700002c4d0240e00c0c4092410100c4c4002540400c40814507501400c0402d66a600d59515502a12803580c00500080c94440300c0071081d800300c0c103203000d480d0041e001003011907110414400b1441c0001a08038042d84140400c441526040300f080b0b41c0524540705980f0640c4d41d07641c840b051600e01c0b050485058209414503001c003100700042034620703601d07404140800c0300642c0209070880440e10910740d007040088001043e40c8800d8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 931772176 1250 931770926 931770929
    0x1f09031704050a0317040e0903030105040606050f091203090301020d0f0c030b01080a020315130c020c0f181005040c08011e0b07201507050c0603101224060501110d0f05090109 77
    0x40b0100401c2c079080c0f023003d41fa03500074001c8600c610304d4580c2c0400c0c2e1a10501c03e0760045450076403240c0c5005103400401413190b04c05005031010344005c0080c41d050391028005083c3c11840780c0c130081419491a4402000d8555980b0180101464014a0304ad2aa84111402e810254140c00141e80e03482e042c0000c405003082e502e01c1904418018014482d228099101c010112102e0b4280c4042c01d20441c00c02c000c003000245060780c0410424080d640d218002c0c102160000041d1718002c400b50756440206d401d03a100140440042242c8400410a00b5040002407151030f0400c070001c0c1034242407030040d940901611601078a0b44641d402c0c5800b0740e5410b038440c0c1e426120014400d401114818101209551140804070740c01d0194411900b4039040c50b400b501c0c010307684054080039050410a03c00070300780b08074074161801a01800007810580705c0382e4010307045071741d0b0301d901181840c1820005480d180444401403d81d61040c4035019809600402403442900e80b40b80042d41c48602c1001215003900c0ca = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 931773426 1250 931772176 931772189
    0x1501170331031208090d0801180912210203010b070b06012d1808070509040318030c06090b0a1205060102030903070803090111030c0307020409021f09031704050a031704 74
    0x7440080140b00c1000c54a83c845440703641d6405107540c0b10070035240c80d0104400c03040c0109803001c0041c010030310b005001c00b020005035000000c1d44419510740035442c3c40803d1540002c60040d07500d00c0302c0c01c42900503a01e40c41407020740035403840d4500b9405844901c40e458018140b00c150f000400c40c1a8850700340301114140549101c40d0540c244580700200c01020000580400c032414140d2030b82c602c00840b0f01d402c4034224005070041b24544000e200542e94000d20440800681744040500c6c0350030811024003450041d01020180c0c1d060071006400d8643c5900205000b410074048491800e510055400d0b64001000c1c02103030603102c810040c0d00d94040d50109075070500400a0110318000000b01030021a802680c41580406680f400c0070784a100e040d00c94013a0703030001c02a03400981031581105280d10310180012806503105580c5540c000c03c10044403000440550080081c8035030131079080381400503427140f5890185403000280450100d44001090710b2005001d0280080d45a802e59009040c4c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 931774676 1250 931773426 931773517
    0x7140915040f0b0102010e120d110f0c15060d0809120c0d03050c120301030c030611090d120801051207060809031303120206011212110109060e15011703 67
    0x42d00e85030400340032003420f01c0740158608114003441c0381700040c055031050400e4400c54900607403a184000600602c4903034511702c160402c00b80400c0010580140703030090b4440050805103200281102c0c036008080c0c441031051201d45131b50400315051030225001200e00300d0306600f00d1100551400d041c207500e9864142e0140d0381200041c24150450000c010000d603c0d0b040e01e41c40380d00f03d00e14051500080c040030308030030856081403002400f99481140b940c0800314005017002c100c0000145400300e9284201e41422041e203004140c0c1c0d4018450501410080b103030201c0003162131722803559401061140c107041110b10b601040c1b0841090003281c014020650a10580e80d03100d0400c41e0401001d41c001c98018480c0c1000003446507801c110519049074000306800003440c80c41c008030340401e005000c0c5007907956120040c20000308240f040004c1106200007030204152010703400c112000b0145d108d0905078038070880c9501840c40100440303500702c003002100980702904c101030080580038104441888030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 931775926 1250 931774676 931774691
    0xd05010e03040b1b010207050c0904141903020c031f09021302031302031c0203160311070807061d0f04050705130b0304061811060a020f07090504140714091504 70
    0x30b10003c1044000503420311300b009950442e4a400c134414039901503c25001136144014a14000000720f41044c05100d80003260070480800504014082e02c03007000a0310000b03040010181c06001e49030b4064812805401c038940c2c1c0d2060398428a14055819503080c1c1d07510340c040c04543d544280120120070910f0119101d01d03001c0900c80b0401e41c103050680c441c1c4945e905040500340100301500f100074160780514200355581e04002c02c0d000707002408405000c0a45040302800c4404c00000000306120001044840e04d41040504075400550488401c0144401c50815948034211070422490b01958002010741e01c104045504d40101c420400080f201410006402c0c41020095400745000380d5080000e0341021821000c4544c8481e07004029400012500c03000e403030300401a04a01d6841c2c01a90000001100c2d698184407090b045000902d585000740710500203101040501d13200150010718031982451020b4000c0d1040f0401c20f0b10580e8000b0000364270b4030001165000311b880c0a0030500149 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 931777176 1250 931775926 931775939
    0xd0915150b1e0d0f1116020f060f030403031d03162a0303020d03050c09030a0210180e15030106080709050411271510110703050601080604030f0f0e0d05010e0304 71
    0x100984000f40b0011800c03c42d52148044505d41180c1000e0498210b034425901543d082c00201801000b00796489441440300b10b24038800140118461072280e5800569a030800d43c5101c01d1048031011403105078020f1006240500038050401c0340030b40c128260101c212429040782002c3c4072a50040d51f1411040e030000030805400240071460388016440034001a5504400d801450050328003450785a03200703050b0354003d405d0100901351460ba252038802c890750421007040d083c150013a8080202c0c100200f040103502050b403c5008154038080700240035130f6141030038075aa10206805130010565481d00400e00b000b60b000846150340501a100d03140c1c03548810322000d5000d44075114030101403100b400042d040c0b00c00c90031002c00401300414019409900d682c0480d080841c1107a640301d244180c110220100d103003007189600030044070000f4851492300d8a03005024800000c0700d88180403020034000011034010100c1c0c07002840544501001c0199410400d02400e0007041d4185280000900800c50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 931778426 1250 931777176 931777181
    0x52406090a0f17060609100e0411040203011e09090308040212030705070f0e1e130f0b090106180204030203060606030a0f2c0f28080d0915150b1e0d 65
    0x40f40248107a80031079403100140300300900c003144c40e45c01c091424034062121804090381c05030400e000b20060040032001c400424102c0e8002c0e000180002c0b656410030f2600d8010344040c40142042003000d0050743e410f0b42c0c015100c0705020b00003d10802407a04403200f503001c100142c600c0130303070004101d40702c2c1680d940c103001c1003084034050050300c3c00c100000242d01d440703800c0341d0074200c49902000c090309584031015565124954030049a68404900d1418041400340041500808292000040d140d02e403c00701c41403044201245040540148410400f50340e02040f09030f0302c14015195150f90350f5505202000400d001004c1d8040140780050b02c0b00c07100b54103aa070560354040c6183c7c0700820202000c510369242c40d03410f403102c0726600003000c20044804030f00b1503510440d01e24500e0b48000320300d40e45020043d08500304410b0b8050751210000d05020b40300d4901a104d104541c02044a040303a000310034824122800b031503800c58800036445208081003140107400c0700d60000c1450f02c44c014103141101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 931779676 1250 931778426 931778459
    0xd020d0903030e0303060904080c0f01020f0a020105010f0e04030f050c0f0a0201020606061e0906040302270a0203061008090c0a1d15030304090f061206090204052406090a0f 76
    0x291400c03c034103000000000480c1c6c014040142048000d81c0c42d582d03040715550061081c1e01050245811046011009001500c00e9149007a00e1907154210800000c0c2190300c140d02c003c01d6480300c088100310742c210020f00c5a400c00d8051912801c40850b06c101a2054800c0030003684080c030500c11f1320b4400301000700e917404800740b00340c1c241c1d10992142d90420140d401109c070390050a6003003441410124a00c8001028648c1c2c001c0d010341c0c1000c0e6290005518030b010038402000307803024112514519600c0f0280d469103d201072078110300b182031803404101d41d440c3c02c807d500c05200442020580340002000200d40d2036900814084800740c0356003004415030526180d1038088404840803444201c03240412000d60f500190085040c1450541a1006003658000e504c040a40d2140e0103c0d5282140c0e03845040c481c011400445d81c14805d01c1800700b02c1e8030003000e1110824803090098210102032280124421040714405e8940710702100103450000e5580c008c011014030900005142200c5c1c01c030211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 931780926 1250 931779676 931779683
    0xf070f020906040507020c0904020a0b0309101506090b030a0f06150201270f03111911040e0606041d01090b16090303050f0a0e0a08033a0e030d020d09 66
    0x1800d9182c003024802030301e10036101000581c014040b41c03030460601c102d038240d04c075000400039158581d5404611440398815107221205402c481000e081a20b46405010703000d04003021003106003440d0440082c03120000340141e0900c4100080490140c41d400d8000c48035038141160100301c03943d41c40b5410070004031024602009175003000401420400c06a504e101360b0000041542e100e11100d55072803010528002044003402860414100d24034410030418170243c0e0a09203101401000d82448000c8407017000c0706078480c174100302e0720035403840340801c04940202064070042940385801c48404400150a000c00c13400c0d6180240740000d110340c1700b0f400c5018180e062029201002d400c041125070382d00d9404041c003c940108a001d030400320000050041f50010303d0070900114070b10000942640d1164459055a80003051141a02d009101c00798400a032130070700c0f81000e507240c04070716803001000b583c1c0d50045650b480c0716030050001801182c02d074000c925011541d42001290302d900600380b160095 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 931782176 1250 931780926 931780939
    0x315060d061b140403050d0309031101150e0c03161b1b05090108030301030c140432241009030b01090614101b021903050a050f010c0f0e060f070f02 65
    0x43e02d9281000088801362500803000c3c000012242405801078034014008a0802460361140e06003440300788144529504500c2000c880315241420703842c4c60040c040c00741c180d0050200188402540402e005000e543c0715414030704183c42145050740810b824040000e050041c40504a8000d0b030802c000d01d40680d042110902816604c9007041980c1b8082400b0083c80c0800d1644140100020012a00b01d00240100b0209101142c100c40d611b400c501c08200c005c0410b40c441d10266028041d00a55921a10302c00f00fa40001c00c90000454840c04560a00b50103140c0c040207101029214004640c0916004030900301156982c0e045c610040c801c40c030800040c940500d0040a007841c01c1010301c0c1c00c0350b40300e580358201101d68013150307542c03283e070a481268041d0083c1400404c5103141c1503104011070240002d03000030010740c1021814001454080050359150040050700790b0f1b04485110074480c50380c5803084c40440d9210200d4185c1c890745050b0790700281701049080401072098400d8070041e00c00c2c0d519 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 931783426 1250 931782176 931782197
    0x804091a0a0b040602031e090a0b120f09121605010203090601090c030209060306041d1911120d0c03031808071103060c191b0606051203090315060d061b 67
    0x10b8090500542c00345000603041081031854003030f030808407240079094043c005071528001c032000518690b0301d40e009052200d00449d1448040911810b081c1d0302045228848102c2d2800c404c400d500d800e9141440b80c1d9003440860400c2d0380b510507071000714001d41e001d0001c565070b09040c03403905c0e51503c09200e101c501c1410400c0845c1c07503c0c070074000d94800000117003c00c0d0458840c0390410000e40158a0615120528000f00080c0703401e0410003080d212280044112011000307040004a907403004d1300b420f00500c03d442d040f02e40c2e010000b5a40380480c10a01d03052861030b4007440c003100503001050220b5029545c00c907111003482100d40082505a118400348e14080d034446082c15203e90040300c000003120360a21200d00d030081680201d0201d9a480c0c9429030903100c8101440302d01980c1c1050503070310107554413008d010900703185c1000041c00c03941e40001c500b04103640c1c000980e0307442401c1c41400f28030401008901552228200c180d80240d0010007405010710383d03803d4070684901160045c0006003036400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 931784676 1250 931783426 931783439
    0x604050d0519030e1906060512070b090105070c031416150807110a0b010f0f0609031e020f12010f050604060302010c1712160e0f06160804091a0a 64
    0x1202e0b14000c070b0445010501184078810b40060288a100b007005010300390360ba0710000544039111a00c00c0c801e03100043d1603800c000a1200120500340220043d5020300414014071a030300703041d540c80070740904c0c09554030b445d2498078114504683d0b00c0207250000380108403c041d03401240103044003001c042400c0d01d1310b54134182411910300e203402900c08203040d100070591061040f1814050a44450111040b51030030365030f8110000300c268044080e1490840050210700d07011407031a0000d000a01e041004035056460f840001480c024520f072000342207640000441d00c4a011030551000020141c51042000e9025580a04168401c0740300301c03807030600095040d150501ca08002d0b61340694460001d00b040d40e07900305d400c460404c006c1031402c1e028011000a4088402050703c51340f58420580859113011001503d4420701d42a0b03140b003040c90711001038250b10341605450458031050082e10880550b030070300804a100707541100e244a07044c440c00d85050710000a00071108034050350a504404ea031641d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 931785926 1250 931784676 931784687
    0x31d0603040b07270b1309060305100506150a02010902040605090702191a010803070302061012080a030e16031b1d100f06030c0e120601091e0207050604050d 69
    0x1a4020310035660b40c030100c1d8003140b003106410721020100e5802c034541083c0f0401c100002c40c25500000d42c00d10000361910740c1c0e03074a00100100401c0d85410512000707007903540d156195000400003809055980d0001809a500c0d40a60b0000c90001d2030907607582c848540c3c0c000e010701050780d001c1c0c6c0036034100301300041e0504100c40c4c880d103e910a0f60143c0faa40414010140d1102890641510b1110040c0e0554014107040750031203000b00048001135680703c880d0300d4042d00340903004bc024245010b040314100501100c5108074070800e0b034019100d581d11904560250010140c8026051507031180b82002c900c010b503c0e00001d41038a005401e40740b080c10000180400c1030800d0701074801401e5044868004800c000719201d900003c0c43c039080840c0c10f031906001090102c080d8031010020b80c0b2080300034681c0350400140f840502d425240e021101201194040e600c0c00103200300c2c10315a41d0b0b00b11880d002c1200d0038041902c0440881f06640d82da01904000d540d800d010741e000d4446018a50b03080c1d40c41d50107613 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 931787176 1250 931785926 931785931
    0x1206040e15070c0c081203160503010503100f140c0301090f0623011e03020a030501050d0f030e03120f04050109050618090402060c0604030f030609020906071e0f031d0603 75
    0xd600040725540d03200800c0395040001c0804880d80c82480c40c000c80c4d41807050115008442400618940b039103008440058404203036905403007442000c00c014051510080341c03800070f280104002107101100ca040c09030050030648088003040d402c9100303101802d208140214100ea40411061061020300002c450850300d261084000c000300c0ca82030205d444200300944002040705050403003600e140811018010004200c41030f00007513001a00703000840e0103101d010302501c02610801d00c20100d0b555080c00000000e8006403d020f4010000d8070707155800c105419500488811194030340340c40302d1942c10f0702e0f0840e006440c0400d09501c004111030401406031401c0c112400b111854122440302880040300001c0c4c0242c0c3c100c5c8003080070190000e82003120034012071080d030300c140075400c411030b005046401503000b08460038010000e544c4030765038540503241900c0c0c214000300c07280160300e81c0c0c007100703500a20401452000700c0c00e000428190040c0300002c9840384200c003036101c2d185850410490307101c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 931788426 1250 931787176 931787203
    0x109050f0f070509060f0d0302010b0405010911031f1e05030d020105100b09130c0806100f09170708150702070e010b0a0f110318010e0604140d06111206040e 69
    0x1104041003075241480c420b0381c202c0800340c1b014000c0c070508800308081c000411402d1f4090b0791280745114440c1040e20900340104001c100c10880c451940da400c4046100281c0400080e68510b0b00038030145210950020040a00303005041c88280c50304001d030742c41c2c00b00d0300c6910300c00d000e00b01c2c030130b03e0450040c0140b0b44104100b0140700000350814610184640007028580d030482d0b0400704156881205121709080c030318a5480b003071000d18220007005012150400d18400300503030b52100c5141d05030001803c8054505203000360402e0010044031500d40071080e80100340910425108c001703180412807141c1c2c0541c00036800d96000c103441e2164501324603802c1c410703045d58120030030048195a2103400754a4240a0b50b00e0080c40c80c083c00c12840b4070b10703004448201e101c0410141c00810302d40e0440f140c0c2c480e0840a6500d00c0c01c0a140c40c448039204004a00b000740115540360354001008800d42c040700c80301c01d080810503107800c201c2d18400300c4d180c411910769000718640500030007589400290407084924 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 931789676 1250 931788426 931788433
    0x1107081c141201150e0a0909050c030d050d09030201140703060f0b16020f0f0405180705010e0a0527040606170c0a14130207080c16080c100504170109050f0f 69
    0x113080c080c002d02e540031105010030000d10b10883da40c2d5940e9000383c80c008140e1030b8401f0580e40607a0820034105600c82c0a0107109500910207559800d80000644080729080c210014404119080590140c8207050300341d007102d0020300c100950725405511039425940360004245945450b22880c40540c80f92041e2240b400000c010000014688000d11f0640300e800505000c0504000d10013280c03da403c20b43d038407131000221044400085804200c5c41004103030034039044039034036115008513021001502884e4001c6800c83c180503451402d4035030040c0c0c450080020f45500e817a1509280004000d140502c1107241d0160280c500324034800100c030108060000c00d00741e80700b4600410f166204101012003500030203000c2c000b40c2d651001c5e10103401a1030003203101c19610107404c110356050402d1008080c820640c80c00f018004a4000100c0f00c00b103d0056860141006c4896420b44407405030354000c6820540391b440540e1201c106400100d4024441e200301c5600364043c910503629903840c00004140c0d9803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 931790926 1250 931789676 931789679
    0x1128080c0f03040309080109050706020f030901051903060302100503071d130b13020c06011508010b04031e230d03051504090206091512060603040c03031107081c141201 74
    0x20403500a64103d48030b418465401e594031001c040c2503c04500054440390401202003166076014402c8a1074403100501451a152040700041e1042c0a1601c414151104441d0f80e00c10050182d03010202442c3c00801c2d900006a890a0052036a032086480030001015806040048906ca9081c0007103840010402d01407401c0000c82c0400900060307080b50341c40703103d140d0f58007031200c1e203880140851102580605115070410300510384001c0036180341d400300034440303004101c68004c1030242e81c15294444855a01000d021010000d07401c104400030381500200d1815410300c040f0340704442e002c102e004007500e66020350000c0a07021501c00322141c21802680610f070044502e020341c04124502d100600250410701c2c14400b20300d0140035032001405500c0e0028003a58012031548003594030060846401c2d20314a42a030341e0a0001c001e82c40300805000e0044038440344100140007110182001c101211240082d800e004240c8021910740d01e008074080303620000030485400c00301d9030b11007181115030610742d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 931792176 1250 931790926 931790947
    0x18041b03080f0a090f1706090c0102070e09011e020d0c021c1103040e0a06170705130b063f041e0c0b1207030e0105090c01121128080c 59
    0x80d448801c200040044c48200490906422200c550241c180301c2800501c002025003103e00e0321501402001040e031200c40088a141e07170005215040e24000d058000c141e40702c040c20300c2d000d460070000c0500c00c140420041c91800300c0c0c036406041880303c40103042c0001c21141c0000ea84941c02001c4030b04a10002d24060b45110b400f50034010701040c0000106c1c0c2c0313001d6442d04020740007507042e62256180781e1100c4003000080c0381c00071035200c4c0c402503a01501d6018900b03000100100c03071112900d1161522070030140e40c183d03200d0040d0b600189941c0400d030100a0070040706200c00401c204411402c600754030303a4986444029102d0b80c412507121000c40d94403a1941d038050000c50b203400f41192031301725880b000b00b0104002006009441020303094000681840d08001c6c00356104100c1301d201c41da240c042000b40107100014001884c82d02030810500c24420380c6043d42c003910010404440c10f4100050f030b2010500e98100711001c02090f602e00c4d29010003810011a194070041e1450390003101e09110b00c1c1d160 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 931793426 1250 931792176 931792207
    0xf0c0806011b020f0d1b03050c01020607022d15060406090b0a05040e01020918160311090405100f06051201080a02030d1b0606120c210f1118041b0308 66
    0x1000001061256540b03a1552469805007203c2c0c515900b8206c0c1c458100100031041200c1d50700e01c5400d0018150610300208004d607a0003c1281e81103801d0038140d0350540e403116042200e11911251030a407a220010741101d100d041d8000e45041d402249054400200c650b80c42c41480314400c00240341400e500d1404003000050848000007000d5558200628000e940e5109075000c4001e2503038940da40e6502d080102c0005084010001c4410b160802089004010300320040b00c140000444000802d5240d81c8544820701101d504035800c0640009004201285c00c01c000d0b00c84e00410030307c4c20403141c2c4c0b100031254440e1481c0c40c0082d055032041003440d00c13080c0501c00845801e4071190740c41a00c0000d90304c030704080d510558003044c1e26108901001702032222414030302c40640740c100741c507441000d00b0695581090000d002d02a2040101c003101c071003000700c41088a060300d20700506007518181e410304400f9600c18151011144071940c403040110400460b86160304882d08548010f007032900e080c0000c820b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 931794676 1250 931793426 931793449
    0x1e230d03020c0705121e06040b0a05040803040605040c03020a090b12071a07111c061a012f010f0b120c0102060612210a09090e061303120f0c0806011b02 67
    0x446c05041610412080b151507500403103803008000381680d040c1401c2014001070b0240010040d68204020807010420604c216908a90300241c00945503441c1e00b07240311800e41c541c0000358001010340000442007215000280411012210030002e525680201c03503960000344101c030301200422407011040c0302040d0140c101180540f980b194080074000004d4900c1d48452203c11900799807080d18070038405907104514809441446644190703650000190185104040900e00301140c41da54400011240e110988141c511400900800401428503030180404400035409a601d081d06140381342800640500700c1841a00078019540320442070210318a500d240007500c80c421281ca000d07804101040114807c411f01c8032080c1c032190141c90060000800c0e5202800060034880800c030302060200e029900031034482c10607600d840142c0350a84a140000801c00c0d0704500d0304140071500d07034440d000300c00c2e007a03100da8801c03686a4580740152110a880c0c1c00400c003926130000c0e00740050a15410720003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 931795926 1250 931794676 931794709
    0xc090103060509030c0a0309060909092f1f0e031f0902150c0714030a0201020309130e0607080103051e03090d031404090f05070309050a1e230d03020c0705 68
    0x900c1c010040311103918206c0c0301c0d2421070000b80d10810810480b40d0001040001d045c02d09000d1190a50030389510b03201740c2a00709940580b1a1640710003c0e480070702d4041e031110400c05810300701c40c039015441c0c981e888050744070a14081585458100c14a1030089590096542441c41d034000030b1402d841c05100418261804a0b00070032000f103c0150180c00e8006400b41d5074071000241a82d0b82882035002250821007103880c080c1d4805c028540060780c002c02614000381042e80c40504440200340480c020340b4400500c4d0146015039010710030450307031150350719042c0d82c00f5404650801b80702c141e04440303030000c50101d0282c9400c00d005964041c6040d040c4076220318000e18124601c03995040d6403c2c03190380707da0b0040003110ba03640780c4bc0c41160580d02a0316880a0641801c0024600756201c550710742c05040c200800d040c200540f0310100b00044440301c4403891f00407103418544551000301444003006508690b03110321803d044140c84070720074021101c50310003460240c04010b1a20050148240102c462030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 931797176 1250 931795926 931795933
    0x8070e070923060c0102031f050a030803060a0506161b0608011202030106080303070c050f0c03060415140a0f0e16180b090c0a17060a120501021e0405120c090103060509 74
    0x10203d59a00015283d549890000140d8030305080082c502041039100f54241050f404120400c01c55849125100c01c0f0b0342c0002a035030b0780384e41e4040041d005070100c1c1c0160754091000b08044800107840300e040c03200380b40b140514a0100505014a0f54019050b10070500052066001481102224040c01800510150004c10000d807142209415034000301d51740c0000442ca60002028003804105460b0b48951581c06481502111400700303440c0d4600810180000c2d036643c5188200f2841540648010145c00d04031180905092900c100600a0751410304a080e0030500d80303c801c4074004c6464221034100040c944440c506d8449415418898100801d0681c0d6271004c0200094035007a05440c4500304c10a400c5641710f00c00b1801411584500d17140c0402054400308010082e10303060003040903103c80d440d24404c07000b81490304901a00c900b14080c0c01d2888200246d04518400e200a001034407411144402c0c1e203182c1040603590b6101d010811035001d007074040100003041d513903440700e070f0882c031464183d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 931798426 1250 931797176 931797239
    0x40f020d030e0306070f0f0503010f120c030b0412110c0d110d0204051005210c061b1605240912070e01120318060f110705041508070e0709 61
    0x4d00b004821200040820411030244c6801a80204010070f001128141681554104454102d09592130300552079040b41c450010b200340425405510000d41e07205680c05000d00d0a8580b51148442c410600004034084184980840304080740c0d1402481000d01640b00e5030009848841804502c10748140d00051010031202c00341e02c4902580d4491b40b02400d00480c0c5510f004180103171150001b032284000c0c0d42d6007429030886140132581680092046070829241c88183d0b03040c0202c0d4010191600ca5849003403c00c03a1404901c80c80d040c03c4900c21a0760035840440583c505425240403482460848000c00c200c280601d441c01d6464440c908c44021104142d85900c0c8004803082c086e001812010401c5203008100755214020402c80700c00b40c1e461003401860b1203000317402810007034280c0c0140000344c9140880c0040420459000b020024001d2011a03841003541c04c2c500309901a655140c06a0f4001248070706820a0103409039580d0795403900002e02d003c03d0b00c075150500313003401134415014150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 931799676 1250 931798426 931798429
    0x1031107030804051b0d030f2606040b03060108030901030222061e03090b06130f02190306080307110603070c051006081c051b0106030501090b0603070b03040f020d030e 74
    0x15012003442911400040c0c207083c146540f800007017859604445003003210108032a143c0c2e800c0100346a61504003c0c3d003079840f108080c1c3c4c0c0c1032145a81c2076181d5040888155908a05016150081703c0507134040101c00b09a0051646a070024000d00200758010400070380715510960040512041001195403504800c0b410800140039550140001503400310102e0810b2007450003040e040005070504006091144d6034a40700300c07a000700801d220340c190961038040c0703488a400000381a481c500d0304550716848040f410403d001c2041006000070700c3c0610105081c00c0020449440c5500708400344d00140d840300070804250300007003041c0d04001102c2c030b403179000460412071454030000008022035218280213000d850401c84511603900e4040d640e1480c0d1401e50007400710740602d44509a00486650741e004800d02400f82030303000404035860100c00c14140b205941180f03004e50800c038251030304140c1c0c5514080c410301040c1c070050400340d02c80882c100140780c80f0701c000b0001c074400d09007041c03a10031800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 931800926 1250 931799676 931799711
    0x605010806010620060f09100e0d020114090604021212040306021b0d0c0308060a0308031e0f070909052e033309050f0a060605040c050c06150103 64
    0xe01404056000c040140311654002411004807004211400c41c882d0b02c0229042da242006408155442d40700b0000c10300d001814880103003051003045062207800040842d0507511811200750000651a03c0f0b083d00f00359180e0130b415070107840c5071030062445484a408000c4150300b5080c842410307100300703060a01c591058170050401903000764070045e1900c0b01002c4e01002029440004509074001d0074a80d01a6500042c000301d00c2e640503e04000c1c1d5031744000100741140d801c1e41000c0d000b10804020802243d405601d0150a081a600c0e01022521103509025140100342d1310320b0041960301100f80040001c0354015035102140066a0b480c4110404076542c00c1545144980c1c40c26420142c18414004064042c03101000d0120f016a030f01028800701c00c5004940400d90042240c40300350100500908000b01103001a012040c0c0b14803002ca454204000c0000b0322889000d0ba04084822800f540590b0584601c910700e0009444ad9076110b0350015003112901401906059a8200200c82090b241 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 931802176 1250 931800926 931800929
    0x705060c01021b1011040302180c0c0a0624050a061d06030117010b0307120b0a06030204020f0a0201140402222405012a0b07211d01090309150507060501 67
    0xb80040d040a40900d50400d007a01c0c0720001441c101c4101b0001040141c076051440c218016411015208584481d50003400e10b21402032a02000e1240c80014410312078254480401080f0aa01500d1121300050440345508044c0c811a580903c1e0b881c82009100d004103c1106401051880b40810384d0300e04001407500c2c1c10030303080042040070340302000c1d01410302403280c11141d4204a0052040525000303000e1070402440d40300600078614040810641e103100c1c6c12a02c00785030300400c159200d805070819103e46401c01c2813044015030034000a1104107110b10030341e5003d0390b000351100507282002506603880a404280b4010085d0355043c098a90a1803030113040c0d038038003034180301108403458900014407c14101e040a00c141c012011041b01d0300c15030302c0e10307a1001a406050364900fa80d60034400d650001100108011200b00c000301184850340540c0442c0140300580800c0303000c0d542c20380381d082c01c0302c0fa21300d4000c001c1682c0b0301d0705000201c06101c01c580f0004591503d07d240106640d82c41050b50420b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 931803426 1250 931802176 931802227
    0x6010c290c07020111150c070201050904090609150b010e060729090f03182205090601090c0c050c0906031006090b030d1d151b0a02030d020f0705060c0102 68
    0x3081003021903a0100420002c05c42c40d100400001040c501078aa0405000c3c056150f944000204a01164028403d803180701070020300410016600e41001da0151052410403515012900c4030b40c200c624030340c072840d00b1118041c1e5441080000340c009000d000d03844444296904260a080212140381900d07082100c04464442c2196504141c603a440c60403500c0c00e551f08081c0c205101c07520040607260041900050105e8810403001c00e40221300c002e024003501415140d40c201405c121107000300254041c121100c0c1201042940e840c4041203441c0c1541c2d980c02400c1d80c012494023059840d00c41038007a000034000f41a500301c003403034109190440c1c00c03d60180c00125156041c40042d0714080c000681d507081d0038100042d000252607040540544114441442000c8101003103001d0484641a15a070b142c2401d1030100741450a0001582e407650b10000301e200f841142103c010451002c00c211000c0c011000040c000541810108083c071f4011100d800150b40d401d008030115802550104120001c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 931804676 1250 931803426 931803451
    0x1803060e0109060c0e130c20031c0b09040b040c080109030201051e1918060606051e2703160609060207050910060e010207030b0114010801050906010c29 67
    0x110f468060709650f80805400e0500003d010018103030b403140b8002c80b074011208800090481d00c90380050b15000b01458072181c4441c2c0341d40c4520703846100000208110040d0f240300504a50850301244c080c3c8800c0700d03120fa0004500004100068650b007d2103802c54812142c0c0703c8600e40711003605003155650241540180c0d1104140044080c041c5005207004a0f8541490b0803443c2c00d076401c1c42c0e07400c070390aa2110b00c10341e00c1c040001101c000c858040c188036800001442290343d01c0f0401003283c2c020010070075080340d40307251154107482804125a41c8803085150008078141c500c40b100c9031102c8504c12990540154407201c402401310b110084043d141c0390700c504810905182d4021720f00350b2070390040c40c010703490942070080100080c64011304990851404810713100708040101c0c00d11406920080200f0b00c000008608050b49601007101d5020a80e1099096a038403020000508810340303d190200e15080c200401040c20b0300750706a40002c280840084000724a00e01200c040c0341102c0d00070b401e01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 931805926 1250 931804676 931804691
    0x510062a080f070c150807050a02070b030717131106090406030c0b210c18010e090a1b031514060c0706050d0b0906030d08070306030501060f140607030f1803060e01 72
    0x30752840c6110181002603000d1443d000d17640b801500c2144051705190a00402103040060740713108000c1c0c8000341a40c203800c1610380c04d00d1000949842c4a4200170190740700070354001098090011202203020790000701c43d012100b50780051055541c00301a090350015160380380030011446d1814500e005000c8000234541d1111048803031310400382d200c514400054400300500c020a1000016603d00f21440000382286400d00c03001030b500106410940c07500b0082d60410411140003986c84900e4240340311584042d0508403a40440803103490005207520082c0f01c40051201403c81103501c484400c2c040c01e42d510780740110900703e10f0040c0036030051001500001e10714540503850300440880c82e10a4403080c8181c01d05100081d211700c0441c000b102080184000103040e24402c0e04203c00664000001308151a00c85943e030400200d80d010f0210251141036920220f800c00c10111000c013032300f550f42d022031406188012071380c1c0d0314085e542a0f0b01125403603012021819030302c02c00f40018904400000d101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 931807176 1250 931805926 931805933
    0x50a141513020406061b1101050d180506090a020916030e070305030a02070f150804060221040203190804170304030b09031b07081005130b16030510062a080f07 70
    0x984c10b0382c00500c20060142c0300411400c8040c541400c09641c01000b03c6024000000100c0d01c9020340244400c4041c14004000c07081c0201c4407417001c0f818019420b40d2925980c58607030691314441044000d401480c03d100040701406d640c3c504003a082000d2801050200031410316514182c83d80d0800d94964000040c61103160740c040107000c0c0180000500304025600e40800041c001c01001000400e0000b004001801c1105030390454000c080ca48036080d4140703011480d1001c0c01201100d0890291191502480850f64525024841217174000545882c0604210100301c504050702c08042051209000110000d044000400d1082d014403000b191160015440c80b851400b030601c0f000030540003903034280298080030444ec070800719081000b00f0540c6403800c5070795280146400103016030101c8070034820100403020760400202003942d002e103c05e40345c0c50202102c5c0c100301c0c4601d00101380c01098921100e0394000c041c46510384c3c0086038001d070003010345a043c450b5200c10070758404c50800080c8503080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 931808426 1250 931807176 931807181
    0xc060603080a08090f010b0d02010f030f110706060909020303072901170d1416170d020c0f061e0a1407050c0706050408060f27010506011209050a1415130204 69
    0x1d5055540087c400000354001080c6c0251605e138010b0f0400000c400308040b9a40650042100411404c80800c900391a41c503c0741c03902d40180c0011958181004030000f00041c1e18010940c80e282c0040c0030358074020300f50356a120590080302800d0030361880c80c01c4c8038041c03014003c4031900800ca480100228103d240e2822401d10040b031080e0414070a540040e20140ca1007402550051092001c45202c880745c6410407080c0303000030421a5a003038000060001300c26080d40c024108034411803040b20703c031500c10110380d0785030b00d011520f043c0380070b4260001581c808640004680c00105484002450641e0021501140703681190444081000010340c030070300c01d0b02003107108002d00081c54080d0038030742008201504d4440180c0007550b101c8094020800c920007a21402d40c81011b007802180700d04c0c01841e10b0a01809045503610302042c400002c05d0001c0c94140a07820039140c0c020f01a0800c561503075903039410050401e4402c2c2840c42403010f40840012041e0bc2c0d9406820b07550002c0e8810700d45803040009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 931809676 1250 931808426 931808443
    0x803370203070e031c3c022103070c2409050c060406091e050a03060b1509010e010f030b03011e110a050301031e0b040305031803040b09010c060603080a0809 69
    0xd610800039910001405050814503800030700d4101c00c06804d10420b4080b48180040ca00c3e280c4001610f1440e0601070400186000d0300c6c15001e441e00b50203100c0310504074011462115512800c104006008244a2088641d16078440c408044001800814401c11600707031601003070603035950744e101006010b01040b140b40c1e2600115006840c06040000040ca220001c0c42201c100b04100c10304410040b045c050320078023a220203400d40c16030707545e40e040c01c4c40070740321050ba402c1c05410b440364040141c205d04022a0300c10300703041e11401030180c0c03100011184891032003403c07400c0541d1424040c035989c0d420f016045d0084000d08582c02241c9400c0f180000b00c0705e03805030011311044100103807004141c2182c20340c1c0c11207400800c0baa40a0b0340300602c1134a90120b161005081444500070081096000f80c090744c02034040418a01c0c100781c01864040d607900c00c6000e5003022000520820181d58401c50101440c0ca228074000300e1003507940c1c1e8407a1000e070001d20818000c128603504200f04150b08200f0b015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 931810926 1250 931809676 931809679
    0x20301060e161b0f0b100602030405150307030615021b09070905010c21050406020c0a06050d1503021c030215040b071d0a060905010e030102070803370203070e 70
    0x240705040110400010814114854092001408402d5a4906000305454600e6041456803c0c82816032402c10300c0d40c581214000701c0e000791000042078462001007a141070303840c00303010401c1d145110b14040c0702903040104148101516100c1c0400c070b60380c1c42c00c501c408401a41e00100340d400c00707421244620400c030881da01c0c01445280c00b0403201652040c5284100d41c003e080400b558429400d00c2c4802e40702008200300400c0558606ca022298030200400c12500b0304c1d4243d64141c0030300300800130200c0440c400e800000d0001e0010700c84604040c0c2c000c034882c051407180c41680715030340c2d0301003840300080150702c411001080d0102001c0c03503010300003d6004080f451a16071305191954800b040ca5102a02030401c111000c86000b5441800300500307003d410000b4a107160596440c20010517040d0b19015040c0040d030010031a105504050090310300003a84828042d0545c0d441c002e140c201448016100c045c03003850800d031014581301c2c100441c465031941090150766490070b03e40c09481c1072030004015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 931812176 1250 931810926 931810949
    0x3062e0906030b0f0420030106170106050315130b0d0506010e0f130f15050f180d1209020105040b0f03041b080607121113031101140a0c0f080309060402030106 70
    0x9440d6941d01550540c04440817200000e58155120210b19203803d82421544c0748a800800460241d030400c1e0010500000d084040c19981e88a41c0704684600080d034144451001c41441c401c018a042e8491001016071010006000111400010304d54142490251000c3c0c0100c0014009450002400740d40454010003102c4681055541100340c100c2409000c0c03e10700500100800304100e030744528002c950594014856401e11240c1003030481c4040d0380c0100300015074400c0c0151402c0204000b0b618110646a0708200c0005030348580150810f540c040341080b404000c0030680218400c007400b455180300c0c005a84034503151034000d81030806c0c800305030f680e030102d074104004044000407038542c00700c02840e002400e1b014200200026001d420107519041c00301180c1d074180c0295048036141100d000da000c3d40b00440d1444010b4900805440c001440e20400b00b001e90a0035014449903845503101c2c0111920109140d150819550025140e5613a90381001d81071201b949400d001d100060b0141da000d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 931813426 1250 931812176 931812191
    0x11030d0c0e1c02090c36010806030f150c07060e06011d1003031d060c1005180706050703090e01030303020d0e070e13051009060209030d050f040b03062e090603 70
    0x136050b0b03100104161104000011404107003500c4808426012083c8400907420301104280c200e01143d07550304080c0024501400212145000030320400c1904e8a03001074803038030710080c81c40f030513800004204400210081040301c0c00104a407160007111400c090160940754104103a1450030030403c0003052801c0340400a100b2745451050101c4100c950600301420840d08291520003419203585440c1d0b40f01001248030781c0345a00100364401203525041c4104125516002003407200b0115039000179076988016400c2c002e440c0200000c01d4854020b04001000f1faa44d451040c6094000340c004900098020580b402625040d0184e2110041e0303860203009650b04000c8040203001000301003408480c0c03c907405100b030000601c6181042c040c410f038188052a160300701000a5441150b49034000d2151f2034801e10028481d0b81501d01840c07440c1c1c4030740e190030b15000b28048160000340590703a10043c1040041100007000c2059802d5500840c00000d502c8800705020740894201d034452418103040c83e00c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 931814676 1250 931813426 931813429
    0x10030c0807080d0c230c010e06031501030c170103081e1801050d06180902100206150d0618200409080f0304050c0a030605010f170d11030d0c0e1c02 65
    0x90003e80c00c40d941c0303010340700d11030242807005c4008061030317041481e540c481078640d003030440201708840407401c04c0c5c81d02c42c81840c96006001c52844100c4d10030060b00d001d0694148a90720941104002654925000c907287c42d2440880401c010300b80d104481c0c16800103400880381c207040c400d1861017041032180d58209176064100740100740c1d20f07007103d5042000010b44c0c0b5203c0c0c0030941c026400741003050326072140d030303081d02012030000c10700c00c1c000780e100340300010903030364003c0c4006043d038801c00110041290000800c0140601d02443c0c0d00212003080c1c03910002200e26111507007452505018916110101d101c2d419260411f610210303500307004130300f40824400440c402004890160901002d4640d0360f6556080030360410845a5965501c030303e00f40c0002003401400d41005058903900281c1c0c80311503a803401c80800206004040d510680c015810700b90075079001e06001c5900a1030304095034508a401e80000d021502c140031030001086100200c44021b050180c1103003014560070075a201110410b80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 931815926 1250 931814676 931814683
    0xf01080a0b0408040f06110c040506210a020d0b060108090f031614060c1309021e0a0905060a180b030405032505010212041208010b0322050610030c080708 68
    0x14800740546294001103000c0003060300c116001081d2411001600315240c8000602ca40c0001c40070078450300c94640c0c0384000d45814842e403401607800808181c0e910058000c017078103841840c9980306142c0609480c80c40946c81d8041c0ce10a510b1095203029a903281041c000b4003044c002a0095502e68003240c0f00c0b01d10680000300712145121001c58032102d0707542e03e25004114001e24030f0909100d00030355007484840700d56a00500103802c8a0075000a4180d190385080080f4041c0710000c500c1c4c0658650030b511850802001044000c42c07502e0244030a540701c60120b05285e11000340030300066810781850040c07014000b0901d01605003d200c075451428140c5602d646da002b4200d840000004000140d20011703800c158401c2c28035481381c0250f481c0c81d4080c0ca11040510115000da8041100400001446100d040e505060383c4240d9403580c00d517211000c4041081c1584c0072810b84001076450b400001c200308110641c841c2c0c0013171a82641d15801d43c030700081414140e0b40240c0060740068414402d488012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 931817176 1250 931815926 931815943
    0x308062106071d030a080714010b0d17121014030c0f0108070c0c032d03211508070f0b0a05090f0a0e041401061a1801140a0806090f0108 60
    0x28500300c90344912045842c0000d00c443e1100c50b0b0306219001005003004010340180c4a41400390014104507054009031909a1f040000803941c0051034021410000740c200501043c124924400c035030a01e50540000d40020206480000c495480ca600800076882d0300b411804095001f9000b41880c1c200d100302084100d82b0b50703031205050002c4800003400c0c0c11b10070924a1000d640004010100c1592810320b198494501c0c14402c440c501c0308450000c03c0c481101d08000117980c10350f241c02d40341c50282803001c24410309514014450f6100c2017480d050000e2600a1030140c50590040c00c1c40b01e01e00f80d10740c0c0031071002d03500011030240c0920406039626001004d03500042011b8481c0200c0e4440301c80000e4458400e0380000740c0c5804000b0500003409140c000351010080000d0080018079112001c410100b01caaa0500345466402c10421820402c82503524a080b00181000310803d651458418a650044111200054401c2040100b280b0780100540d4100700c08025a454550420b868207484610b02d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 931818426 1250 931817176 931817191
    0x5041b050a0b2104030f200a06090c0f080f1b01050d1e0507030b090702060c0706021e0c0318091303030203090a0510060303170c09010804110a030308062106 69
    0xb0a000351440d120b50f0200f0344424407103d4002080c03916180203005840c01008031000a040040004185103101c00c2080c0c507082480001c210325202a540c0001829203601c0446040c2c01e554800243c1d03407208400c1502a100c82409000c103002c192800c0342c034012400050340c2d501c81c0c6400f80045641d0308181207802a4103403c6020807514515071070701021511441008001c0c45c50441044040341d815407000c0c02403602210200700e0f68031000c8003280d540005070340500d8010320410540300040c120741e005004030124192607020124074403903003c01d540c0083c0d8100300c05400c0020003000d000001588062041021150010a81071100d858030440320649801428980c1c000701184d8103090400001d4041c85d884400c40b0b0840d0652241d00003e001d19200840c0850203d0406c5c0705050311400441c2c1c450344003214928100248403004540c0032001420540300700d00f070320100c507801da201d0090f508040d600a440d140b080b8101503041c007000307412203101c003460550702c00c51001a52a000c201160403d82 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 931819676 1250 931818426 931818449
    0xc04060905060c0a02090411040e060603060a02090a05090702060108070f0602070513141807170d080408041d1008010209090c0a0e0406120b1f1503020d050a05041b050a 74
    0x70741c000318504d07244190300d01070340c04a8220100070800070a454081c40b041030aa0342070007204075400e01c1036540c502c10b0b9641c0e507142d0014030000382031201540c054454210018109001a692600810f01c0b0341d005441c0d0380f0042c0c10040050143c00da0070006070b4010b040c00180000c559141c210000d40b500218000d9501c2103c0e000040d125a40b0660441000e118080b4964800d609020740c03482d0001c0c1400101e06054014140d0003e000204000c0b480420180c2501400008801910450340a18001c0048609400620010840c010000710040d4000d9804011526a0400c80c0411920400340c3d803141c4c041780c1c0100082519900c034140159042400010083d44404200c08152981c0d0b1031100c0e6503401c60300c0c02500041000f00301c17550950f01c3c0d0003550505070946034007a81c9000c0760001c0162091860044804000300d0420300c00c1540c9101591a005042007401100b140554000fa02c6461005440c0d0043c44144101201e24100902074001c0ba84069850b2030f000c100020f02c1442010040c0d030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 931820926 1250 931819676 931819687
    0x40807060f02190c0b0603030403030c06180b0f010e0c040522020f130513140705160b0a0903020d030c090513020d140103060b0a05010804060914010606090603050c0406090506 77
    0x80890b01070b103241c503022500c1400444000c00008020b03d910708000c0d2086081d40d0085016810040212426070b509540c9480f420315032502c8074809420348150103040203202e0321154001c1014022054050708080b8a000c02c95490074030500300010b0003400c10707121460100b004001e2941c81566000c1001c80a20365081d100f81d00c1c8003040020b0143c54402e200f18a00060124005801e0120442c2555000c4540c115000300201890044072214502d00c200041e900d00810341c1c8038004d030013410780600c4050f080041811300e50784801031214103440c608052510b5034640c60070540c051002510008a0303140400c1107070048100140340001900c6070f2030003014025200e01c0e280c082501211a2501981400d00c202c42d0115020301c3c0150f070074403003503401918180f07500d8620f00e41441907004503075050b5640c2d44e45032190748900780100720f1424121680c0051591800b0100f00c01e020f40e03801014107480d400d600f1860910090107403a002840c018a003001003201f442503d8001c0000c1068820a441c03c0b03407902c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 931822176 1250 931820926 931820951
    0x10e06030f04210504080609060105060a0c1b030c0518060a090903090e090607120b0d060c030e12271f050d020f040f1e050111120c030d05010e04080706 67
    0xe41d09034a00f4882d9519440900c0341150080020001c840000003114181d0341c601225640710306081c0640781d0300000070000302c0c68941c4140c2c0c001092038050345410500f12864a0071940c1c140c16540200e074190200364040280d840c01142c01100d1100c001522031091401c0800124841c3d190b0150047c0e650756601e00b03a080c50f11170900395010b4102e1800d4050b9604010303030550b03510501100d4100003da8182d400c00700d07151285c0a60000c00402034030b1140354131400d81e5a02c001c0d0182c507034107004040e03441142c981c0f18002009003100d80409000344550b540240242c1407908450f00700c83d8580b801111040044e030fa1240c00516841d1841c00c44c8400c4051010b42040f00c40d4072404d6035100701140003141d003e50044800001f071003107811480303000e00542c2c1d03650302c907101d01c851808000c40b050f10f0b00001040554002d1860203900c88611060f15035507100e5800080c01504110003000040e4000b14001904181da40b06080c0036000002e0351104a160a44c0c030700c9103034450590000d01c615118090068070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 931823426 1250 931822176 931822193
    0x8010b031e0c030906090304150e1c113a0614070816080103030f030c0323010509010f080d0e03011503081306030213030204020f07170304050606010e06030f04 70
    0x85211140c0d0881640c14003060700a00b0760001d071401d001a00890021481039040042110201c0c0c0c8080c0345802e4614030540242c8540c0d42d01c080650f04a030710180c221555602c11070803107600d188240c1401c50041c1c42c2e48188074850f00c2c12a803d004c40000d190000d600a490340c0f0403041240740390074201c10540c050780f80c800050409180d40001071408401030000c10340d00305021354420010030050a0040104240480f9010320030701c00503001c00c58440030b03511035070300c260850a4030040321f060101303240c1c880e542002c000f0645103100f5600790000c8401400985405229980141040010302d4003030f81c10128183e4860090a40c04002c0c0002003120002c661000c1d003113100da0086e498140214166a41405c42c0c1e40c0d8403c28844120001241002c50f0141c028030a460b0310204514001807181d08603428400290f1286003100300c4d000c000d00200c3c0010b5181d042c6460900348030b00b182a241e00701b0b0315000345000c0c0003800d411b040c010b11510020068556005a030380c41b504091105c0c038140c8860801c6d002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 931824676 1250 931823426 931823461
    0x10e0609031207081213110409050c060406050d2f0304030c0b0a090203100606080112020d0b01060905190503210d1a1009140d1e030903110f0108010b03 67
    0x140802c02040ca00203010ba2074001d0805101d0340c1d010713000c865407201511a10380120903c000c0090140ca461250f09080c19884503030391300d108004031380140961600044040d001507004000040c800600c0c491041002e01410542c00700c0b2140c035808040080991014030100700c1820110844003000041c20305204450b481074207504002801d41609202103580082c01d0b06040c00c4e0b01a01c46d09264400c050f4861040398100d84069856807496400d10680d4501580800c1045c0e80c480324108460340840c06c408001030090a0f1600d40040b150b00c0d00e014440c1004e50844898a5030868100c1007000f170301c0c0032440d0701d000305850350610048010000325007958002c549000400c2440d2140c0c00d10910344440070130383d0410044070394250b1398a40380b000b110344504030b02038008207181d107000524040c200247d8511200b48078a41c40e122000542100084101c5005402d400240ca0503804000748440f4038031a020442060f0b8940d107107014000d0010344012810312560441800000c0040d02c40e9a80700b8007441c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 931825926 1250 931824676 931824703
    0xf020a0c060807080718061d091005011407080405010305070306091b080a0b1c0203010b12070e0a111c02160606090501050a150e032b02011109010e060903 68
    0x42200e440700d400801011080320014040350f0902c003c00c2020740241e4610719500740001504010f00d0400d101100c4440c1059200c034413a501d803140c0a4010360b1070022284c8105d11a609440a20303103007800040a042014103040d200c04810800d41c000b081c0e0b500220b40580c5c4080c01e01207442d40f01c00c0000c40003403072242d1041c021140741c01038210301c1d1010480110340101c2d040d0b40d2500c01e0b4030741e01940000c6030031004a040d44a0820140c40741f03160480d003a41001503000800001d1120307001004030724500e0044810201c65000144140101d102c0d5040040d0001e01d40f9400b00303700c07080ba030183c05044c842c0959481000766484048080072103a6011a80e080fa200007441303580019518004018000324010360b050141010b0000c20242409840c940c120351917200c4840104001000c2510605141241607405000c0cac508000e4804e0340481c51910700c0810701c00102450300550b01c00a007104d40410b64004000410011000c2903a071040035290301c0f602c01c44071140da452324000000d140401115405 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 931827176 1250 931825926 931825943
    0x2010807230705060f010b0c07140607080304390303120f0e0a050c0409171617090f030a08030c0a03150303050c06010b0a0c060f0902040504080a090803030402030601060f020a 77
    0x25000c1000206100d4003601c580303038110502d0b98803990080480e000c6c220b2320300d0071980320050800400320040140c61146c0000f40c003452400050381c492050681c4110b8055800403131a034240c92414151400d0b110780d5800e05001d074002c2510250400784202c050b80f0002d401c2008011101610b10b40550004a100c141d280007048144081c03602903855241c0070034180d0f10b90284440e0300c0b055041500410b44816407048020250b4100070b107804101e03400c0402c050780c407042441c08000000317150581c3d41020050303020680303441d4600c442c1000303c00e801c5a00d429010350815000c2d800002c110005480c2c00004408201e5181c03955480c04800a02d043c01c0104003d048c161000002c1c90780250041491049005c19550640c1e21440c0310010f501c01c0d401003c00080d14000e400c800b0503000c0e03000c4400100c08c0000401c8102c0380d41c00040944406903416a458807000403880225034004c1d5441009040020280d819450140c00090716024144210402c0c440903030803d2006502c24401d5100d22540803154 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 931828426 1250 931827176 931827187
    0x717010b040905010615050c121e0f131202092e03110307061805060703111e0d0e01020a0204050a060e0109050109110f0703030c050d060801020909130201080723 71
    0x3c6406818284252a10003040d0b0f40f002940c60310403801c5800c003020090041c842c000034800c2012140d400340741d034118003945e8660046280402480200b004003101000603407100c444001c1c0c00d10043d11a03012a550700908034108006840300300391203621000b80b000f40c2c108103075200c4a55811042543c000741c0c0e0034500b8400842000400200c9000c1c5000c25022110031035204c0c0c0d016145214035050f0712140d5562420308100303d2138040f00502c650f51081c9824100381d00600220b80c50a1852044401800b20003100c001c8403010410030724481d48020310307028070b405040f400040c2d2985c10001c4040d0007582c607440000c2c0009250b40204c0010060a007451443e903a49196200c010603007030090f54000c0b401c1002c4651601a20b00a07070b007020854007000f900d000d01565041d001422880521014000d060001d1642c0c1166031246400030146000090385d511058010402c00c048010580342e904900762640c0400360341e120a145a2040850500020b0450480c82c03001007171400074080541120000345 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 931829676 1250 931828426 931828433
    0x51905130c1809140c040e13050a0b0a020705010c020615010e0f100f0f02150601050705011e0608070503010c0c140c09070f020c2409040207050106090905070e0402030717010b0409 79
    0x8180c40c03009001003000940e031119004504940321b5840303600181001d030703400300c1c2c807007490741049018180c41402200d80000c910f64420201140480c0c41480d400e90129044040c040207005035010440540f000c2c1c13010b45064960b8444150448100a0401910344403016072074a07840b80710350303c84500600c80c1101403402e120043c05170040580703010000d0011a50142858000204a078050f4042140051240d68503001122650050790f003d0b40d0647d22030502d1005078440c003a260b1080204035402040607400c2080031860200312380d0146000740c0c0341c4107600c0e0209510604000825034008950000e99294640140ca09000621960f41c000c0410302880540c940100001002c00300e02d4080c0c909103c01c0d1010004508940c0b051020b90880c04c0d146c00161104ca81e0003000c1d503040040c001400e182d040c0d150740742100d000e500116180f640c1c0780404014070004202d05001002c185090060b6442c155020a031100418418103104c0b222070981051200c500390030036410346401030410021f058aa06 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 931830926 1250 931829676 931829681
    0x80102030906060a141509060d09050309032103070c02130f0b0907030504030e12120304080310171f060e04060c0e2704050c0613051905130c1809 64
    0xd60b024030134959803000080e0b0300c203030445540f00040014180b2141c1000c8040ca036645920400c0300f240e00c0304007002094603c003c14460402c82500500040d5180c03146802414545131854161600e1181d03513480c00102c44180f00122076000d0380c64641100003981a1001c074040b8040c0420300c1851504162696482c020030341e104001501c01102e81c120280c40d90107081e0212401035402400051002c1000092810050f03456201404a41c00b1034505600c80400400340360016a021115031600200703202c1903a403200c0c01140a0308503003030100c40304507070886c41aa44052160000b0304121141c000500201508c4d8000001814030703050480403880c0628100001b00400007203e4082402c0840045841c20002c2007507103d028411410304c44030101d91007100e000d6074002d00407030700381c4030700c1d507405038240c40d4ae2000c3c1c00402d201c0c60005002500740401c01c504084200200c40c1c5110100300104280ea0f241c0b86800d1a44407001400685907810030002c484201c0400403101c082ca50310000016582c9055 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 931832176 1250 931830926 931830931
    0x307030207020310020c03070b040519050f070e07090e0411040914071e09021e072019030b06030c0a1404050c120403050f09090112122115080102030906 67
    0x701c06940d46100c01c0c0c0101303804c80c007401001603020341c8240040c50000e0b180c0381c03e168016006404403051048071080d071500901c0700013011241074012190103140c201c01048050042c0c0754015445000e0b261a4100810700c401910507149e002421002042c1444881072455000100160040c0715210342c9060081552560807006034052151030302c00204020300a03885800344038101881e020740c51814069a019403c501c00d0340041c01c1e1000c0e20020001040382c0181802031040c00700c60000720001d41c014420754504883d0034007600128081da00c070b900e051086602940c6d840398604141c0c1e2140c81c04240f0302291111042c1d00070401d61000f0460821000f010f0202c3c1808840500c115622005161043d004000603c04001c2c00070020a00080c0100068440c090485416070304008040000402041e020f90005000740001c207143d82c1406141040c01010502e2404e045c281000d000c01d110110b18524559455126901e40c0b14860000c1c100300781900070b10803074000395181c2c00d00991554941506 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 931833426 1250 931832176 931832179
    0x90909050606061309320105130b36010f0303050f0a020a0c060306080c0d120305090a0614070f030b030a060509030906030a1b110307030e01050412030c060b0301021206100c08030703020702 83
    0x1c6c400045080e443c4910543c107940c0c0241541100c01c000e854001d024084800d0096842008082d16407030b000b12003000702802440303d20041c064207070191840d129803001a049a641049030140030320202e41c00104882202e103810104613a030700c018160072420040031581c010301190400c130300092103030b605401c11400d90343d00c4c0b020369603644c000d4030412021a9918400400b085c86c41d01042607032600036840164000110000e40e15041c400d561844112900b200c0c2682280c915981400740c0c050780140c11889842480c00c082051428541c000395441c40101c2004107401d440b4800180d944000b402600c1d00e43e000600070f241c0b241030501d020740141014104401808000a10307407451588140301d2010710581700b0000e1481e160141d00c0844000082195a5041c44400c11001840b4280d0018111040380030781c2d6040744001480c0b07018800c0e661070340320031407081e03005000c4142c4114025240d941c100c8030445040d5a482101d031019100c2500300100540101ca02008214100c3e800d50002c0444520 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 931834532 1106 931833426 931833491
    0x30c03060e2706130c060311070f02010905030114160e0918070513020a0206010902091c0203100203090d080f01181a1c03090909050606061309 63
    0x209484c1d100c400c1c07820811503000e0001c0b1600b0200039120610b028410104001c0440c0b1881c02000c00c00341400720420146021a8010075451009210140003031008001c0403030300c07040728072048a207030300102690396031064203c0c45442804030440c4c3c0107200500e682c9507000140088042009286024411813001180a650ba004003c900400e0218096035481e040003000717040480c10b80c070940c500d6005000711101a03940c541241c8040c0150b45405120000c10300000b0b10b4031201241d504c0c0300c188000b0070701c16800c00c081001690075016403a07800c0720352101282800c10f02e5003441040c910420386101411500000c0c5c002c0b24025031840172074001001c01d007002402d01c104d1030089120941c0c2c180c240504143c1c11150500041250b608208074680160f141c041c0c580100401c000c1c0302d08070025030f9002e09410781500c80040c0c03160910030000c2e0100704d20038180c1701010752001c911484 = true := by decide +kernel

theorem cover : BRFrame.Cov 931654676 931834532 := by
  have h0 := BRFrame.cov_init 931654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 931654676 ≤ n) (h2 : n < 931834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
