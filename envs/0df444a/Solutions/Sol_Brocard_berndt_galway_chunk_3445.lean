-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3445
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:46.948329+00:00
-- url     : https://prove2.me/submissions/b59d6d96-cd40-4592-a28e-44e47a63a95a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 619424460 ≤ n < 619604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 619425710 1250 619424460 619424467
    0x2070606030b070302091503040f0506072705011e02030405061201030b150604090b24271003110f0a0807080f01050109050108130804080703050c0a0e01060804060207020303 76
    0x940000109001e00044400c0c05040010a4071203101e4821b4440c07140014000807401001000c4010b065080200200d8800d8901c0c1098400114280155402001540c441d501d4400390b0580e0040418070342e03034210b1160401c2003801c002580c0d01440d202c01178600070321558000099442c04034154030694008a8002d240003817920030005440018604980c020720090500c4d484c1c010700d407581c2e06000b554103544200244002e00024203240e00072101d82e1001004000d10114083d00c1c28030010414842004c60040031070810035084080000040d5040c1e1410800c28a202810001d500c068110b40c1075420560390ba040e9111048018045a80507424001d0301a02c079600000e00401c3d400b8210b0b4404002241000403d8900915101c03650603220142c413010343c150308180044074207100042c1420894000c400508001c01c082c0c41c002d00c007070882800908034071802d5003846487c080301d42c0b034090301820303a494042091806120019064407402d150030300e400e8803103040103c017a000743c2d20065810b01000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 619426960 1250 619425710 619425713
    0x709020a090501090905130209090f1c020606010e150a0306090f09021c0203100515120d090b070b06010c0309091e0e0c0108040305090402040306140708010b0c0703020d030903060207 80
    0x480c281c21954240c0c0d80010a0792130300710322001d81b07006880041a85052000d0b0000500d0039851443e4000340350001c90300c110f8160403159181c0318101c11a6400c10030a411444101c0b541401038990154003801c01c00d005040510201e24813900c10704d01040403000100b605c00f02c80c0d00c20f030445001460907610602105061003007240c010102601d08074413071014407030503c10102a800d850781c60280c004010b8070380507001c2190800540001041d886541c40c4200300c808103a910811100c813403c2584004204004c0b84075805451031185c0c0e00800810b51003486900d0000e01d0826145600980a1a03c03810300f00c210715041e10409050b0b0081d001c0107003000c2003150207007003401803442070080f403c41c140000a8910301003030704d40001c0010746001900300c2c4e0001d00400e000e2002400c0c50440a00014a07056a94403603800308c03503030351460002102211040c8101241d001040a01420300c5400139450902a031703212507526038680c4002800796000340204400d050080351014002d6400000540d0b55200c103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 619428210 1250 619426960 619426967
    0xf051809040c08070509130305070609021801080106080313090b2e080601171f09060801090501050c0c1c031e150906150e0a0503030703050309190f0609050709020a 72
    0x10b015080caa0302c44d6400004280c0b0304000c59034042d01c1c0c0c9034406692003801e80c908a80f658005c1c1710641e0381c580c46800c0140161141c0381c3c0c04a03000581c108422040d41800b156500b52075441c0d00c118120303481480255401041c04440a0440c1d500040020b04145030703401040030740002446100008516003800c5060000204050403c1401039940031041d9950070015202411b0004420341c14100080001e16074145200010303080d00030018074200d2290ba40c610030010303200c0da40c00c102d059946030800d440803c8001d01485130031400d10f5084500700011150010366030080308941805191803603428030656070081c0e0081c00181c88041a02d426440ca02a42e0380c080d240c691200c0c2d9a10a01071741c00107401030300d84100c0042d5626222001840301505008850001341c0b0069140c1c0206240e80000b11690300304010f122a5109803102a00c2c3e01d024000a4186683c100108a10080b00d4000c0720000e07407940c40440707041d54000c4c0002841c000038100f084c84c016240c2c201014061002134854942d942 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 619429460 1250 619428210 619428233
    0x1404020d060801182603010e0711031b1009122003041202010210050106021032040201080f0402010c02120c030d090f0f08030405040b2209120e010f05180904 69
    0x1004580040310010360305035035608082a061405c00414001841041c561030310b455042440d03803400e02401d005054045040d54007081e50900060114602c2100d1080306010100700c0368141c00c3c1c01c10030100c65032203041681110500c184100f1445020910302e0380d41e04892001201503100403a5243d90305d4903000c40d01c0c0300c080c2c0341c164050722604081700c6c030945142c003559040c1c411a5019185210325a8440d00107400c0103000f200b840000c0e2011220919a041071081501d0000c00080b560f50805000242c8100070140010501142140801000d81d0700009c039141e066605941180c01d03c4035107010305080c158042c00140c1c0c140210443e46d0700080e444141c80701541c2c901c003105c40d44540d0307a0f0341c01700008940344130b0f2a48541041c4070030405072410754000d0b44d41503000307086040d119407413810300746281112280d521a02c0340e68107490428002c1c0540c01803000050360a0100300d000520001078904102030b1300c0c1c2000c100c1c00050740da596040b0800b0126070104080c02c10643c3c2c2c109890314042d18036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 619430710 1250 619429460 619429463
    0x60f040e03041a040f14010906030b180f1803070f12090b16150207170a030212010b0c0114090303240a0b1207020a0f0602030a060e04081207091404020d06080118 71
    0xc0070b0700110b042190349091546e640c005840f001a038030b181c00b030190080d02400c40d52035031118603402204280003054518505c03c94048010038050b140c40c03c42420032003020103401d0002da02c280860301c0054400c1d80d40d800c3d41600001c000600294a4008803151440383d000b6981034080441ca0581502804c241011003500c01c800009002164544080480c0101d0402070500c0c429030301001e20301c264440003031044400c10300e400751905012681100f000c040c01c0e803006882030f030005001082000c0a1082244005c0713100e11040150030701000c01540c07400042c0104803011000b45111403441c06499801c0381c1540040c2c0030301c1141d40e03114003c1d90340b0f4110913a014103000540d000034003010720111b03a092003540d00201c1003041d0425a00e4a20082d00300406800d845a550500410051040e80203240b1403441380c092165141c040c68480000a84090080010b100c17212100b80149008030f002440e9940701500c0040e2104075656000001c8c0c1119071248000c0c3d403030041210a01d55070181c228880b103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 619431960 1250 619430710 619430729
    0xc030d06120605151806030f01060e01061b0305090907020f010c0507060b030706080412022506020d0e060904020d0603120806100e0303310b190206060f040e03041a04 73
    0x6035244c411004500380002c0341c0716442050000f08083d0440a1000300381c2110000d42100e9104000407180c0e03007142c080f90440f44032480840010480d20b60711640100341c0b042e4201000501d0100c0c1c1d64043c020b03000d126040791240b4440c0780020a1984200044143e100301c003002030204000b6a20054002d034060503040d6065030034141c11149505001844908485065507120803035503031727511002d4171301e21003c0e000c0c0c0c110b0151546602015244140012240901c10030444501c1d02c1c0c040040c0c6401014003141c0240700d00360040500b01d03030303468080c3c903040b03801a2350141e03407104d81032002402409990802804c10400e02804080a988407011610411054404030b0b181000790380b040d604012180c0c4010b52580c02005004051030013124050000c801c7e070400c001e00ea03440c2003030100c40c240050700100840003005c98020b01e44c401c01c000c1c03800003184900144c2050f003081c0c80810100da4104074407034011a21284004032000d001c200b01c0b00104a110042c85071103c503602e04042c107034014807034108036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 619433210 1250 619431960 619431971
    0x60a0b010e040209090a090f050f030a0e010309031d030a061505210a0213060b071407050f0913140d120c21090303020d0c11010518120c030d061206 65
    0x5a0401d84212801108014030505c03032581d821030360780e01a1903036910803545081d8200551001a10411103201d22082c24005903481e00300041d4002d2441a203480628101400c085a1801003a0441030001c00103521244a00040000501107890000da0a10040c8214640300343c50020324824070704041070b43c1080f607a41c4451040002e02d04040310407150307190100d0300800800d07030041c83c142400810752600c210001c62003aa44001c2da19003030300447c406603501c68295051034480e079000e01040d000717820121140d03400d5580b114003090640400401485444030300915440600a52041c844603041d0890304a80e08205042e1000301901d0607000d080903843d05000030600018094140240104458910074220103402000c0c48043d00c00340d0810740c00d06a00300502c165411141c09a00e5494405849141045286046c46402c42d0001000f401ca00242ca020302480ca038000300d122291107039040c0190b51107944941d0300303e003140700d0200d120032030a1130708800082628622011564960268204010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 619434460 1250 619433210 619433237
    0x10311180708040201120504110a09050c0403082206090905070806010e010f030b15091e0d081b150103050d0c03091e05090906060307090c0f0e0f03060a0b01 69
    0x19461018001401001203880007821180c4101d1025500c58014501608240c0b5164031000c1100c20a884c15581185031003070f003a605007002d1000100811034228100024540742e1498051030040e4003005100d07450000c0d4414880300d402c9003070418a035018422124895440700c014204903c00d100c0c0080003410080025000c6000c0d4007110310844060711002c441c2c80d038150044502202c3d81600e18189990b44105061684074641c04114102640341c219594075402c0c030401c10701440400e003500c4400c1c0d501c900b401c2c0340c2c3c5903d441e1500881d4020116900c1d00c05000c03507014000c121a5005106100d4124106114400b00c400c0034100d07030240302520304481e0441e8040350032003080a00607012880c12030041090107404070340002056800314251160540b90400100411011741c0c83c24003551101c1c0502c4035514060000500074088a10200003244907001c0207400c0301d4022440d0300a1201c40c02c038015550302c882008100a00700107040d20b03081e103400c2c42d40307400070001981218000b5074000c01600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 619435710 1250 619434460 619434469
    0xc1003180203070e0f1005031207030210060b0301061d1e0319050307110f0a060f0e0d1406100303081b040e04150b010e03060c0904020403081c15140f041107030305010311 75
    0x415540d028009d408000480790305400d5603400200120114400c50200f00b05050452045202800c2c4500a041c3d8951408600030a1070a19a110f03013050004192020460381d43c5a841d42c0c0041e0070810b84018400c40040043d0404002040600300d03068240d078a4001c024021000300440c0e8070074029002d0324800032007401008015080740340c0e0042c00004080c020036003e20240140c2440c94504032141504810104403088010001140c00040318030080c12241000d0086580c004921908190240d10b10344009203000d03006040003c00340701c0118a0b5000e2a1120100e4014081282c0c0b891094185442e01c647c840080d1421101c045151500c00a601e610030b000f816261003008000308442c0d224011004080d90082c400998082e90030000000000e0881010f4050004109481f022000e180241403040c5c03030000140705201881e1100c1840117401c000d241c1020110266085407020780b050010078000d00c4030462903100000e000c12200109603154100303d0690b0302c540c0c0300040d205469010310 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 619436960 1250 619435710 619435741
    0x181801060f080402190e01180219110c10050d0f1a190515030907060837020f04141f08040c03121d01020c1003180203070e0f 55
    0x2100020042004020070303901c508401500300c0c0c0014641d101d0751110450507040c41e4419844254500c550100410450310941c2c00e2224041500314154a05455101a206440c080a800c0c2007030002c2005845001c00041000c2100b807c4094001c01000b07180010180044e0408800b0940700d0342040e000d800354040900404480144c43c14508814404202c00c0141501d02400c144036030350380f0605d0001e00c03507413101d202c0111012100c5644c1e40d41c0c1040400e2609001e816048001440301c4002446141c02000091201445115201c0071164903603100008100f101542404651400400d014045c0c4150b400100211362480c2042050420f006050004000e01c115121400c2c54506200841c068050240245d0240c820040414030f5900c81d030711046002020f0700c3c1c00000079a0443d0107141184802c020a003029024002002c10102d00300c00202900c000803005010140c65102c080d210010010600350616401004d54809a4690709103011111040b1451500c1030a6403020515030a66020103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 619438210 1250 619436960 619436969
    0xa062c01060f1715070807200319050d0c090f09140a0509030d021c1a100e040609060308120c0f07020d110d11030709150509090f03181801 61
    0x40706880ca03d422070601c0550741c50701120030b26008202d0704900200c1c2d100c0c2098450682d58a80c00c000e41403080004107900704094226010241014807039201794000070544194000b40011040f42e07451100048515008034001044024181251308525680001104003036505450500b03141640d6070314610305540c1c03604100c1c0425824000031038080e504c2504402c0e031100c004400c0364070f04034920b000c0c00d00302c0c0d101003c0c02160741025101c642c5014124042c00c1c00348001c4404c84000301208000041281410021040c1030103e0004e20070495110382e00054001d10700051f0812066a0780c0c1003103000c0c0c0d800300c0c1c0c10301500c40d2560300140c10701c1c00c14400d0b242c0c41850301c0a0760f0b003003103450390911080120107441500c0140440051000303d0b91900a60000320b8270130401680650070f08001d252606000383c00c150542428400307800c04e0000004900310803118100ca0040c004d882e500001801c02003019040d007001e0100161250103a83c54000840c40528242d03084c441411044048034080d6500303005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 619439460 1250 619438210 619438229
    0x200a061b0c060b01020705181005040c0215040519030305090d050a0c0803060d060e0c0406051005180f0604031208010501091a1809100e090601050a0b0c0a062c0106 72
    0x80a201107141076202c3d01e0b00c2c2006004851400740c46000040c80200500710f540480ea05005c10007220141c00c18114000b00420354040c444405400b41c0030f5250994400114034503550080001c050100400030141545640550740c000081c00b030800a000d024100c44081c150304c00c000440c04420311400856005156507660f8010320716495440c0a01035202422a50780195100520004034a1500c10696a001141c005250b01c11440d4103100c2518000c0e4070161140e070706c50010f1128140c0100460340000b0341c8807014517000d102070300028450200d41d0491070704000c01040100400c0740092600e0110354450b11807045680ea40d6004660252040c01402314000144065139034a80c804000351a2a44540c0d507517021034121200820581d100032151845520207083c002c0004e070585900c455001107100c3c0c050410781d1304050105552048a211b05104d1000c0010240b100c62020321012214507030003c400e00551020144150140a540006d80800381050341000b04c0b1503c1442404211030f42c044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 619440710 1250 619439460 619439477
    0xa030801050909210403060b030a15020703140c070e10060c03120209190f0b16110d0602031509060619080604020903060405010c08061009090903200a061b 68
    0x1080c00396841d0090f0182030b082c861000c0302458441d100c110302ca00401d003002d001c4d407220300d142411408e0720f240d42d1307907103000350070070f9180030085a82d0354485170300101040700c0580e450725689000c5a04080b000041546d00b040414100d890301c40c0413403480c0c1110300300d192441194807034058021504a0a1103104085030010f0000000680907814548520040c140e005080c0700c001c101054061000070092042c0007202e071014414807103400110b10280402c130040c141010392616000e9504080008081c0c08003003154060821a40c42106104100d03071310840640d22803c0c20400c0e2a0700d143e120f002d203480380024400240e400c1c00d0280c1601c121240340216240701040442c0103442c000c8020b000950055000c02034111951010400c240c05903115070000205902d006100400090300542270310f200d01141c002c007100d100d41c07224a00d001d0700c24200b000203001000740341c16216100003109503404c2c0100e095904400c3d0002080400105014070800d0003440f005107540c03140c0400051850010031340c4c22 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 619441960 1250 619440710 619440719
    0xc2103090c100f2a06140c490207030801091103130309080a05031c0615120f0609021b070521010f06080f011802060d050406110d0902010e030a030801 66
    0x442c54a84913188010704155801c0c2d00312040d000c404a25181a594a42c0f10030341c0c00c0386c0c60003180c1e42d6503000d0400c003240380c10407150b0104c4c1e001c011541c190700b1020503d06c10800042021007651070384505100f441806801c1c6a40117850041d40100c0816400320f0000320000428000358050300301c6002030030020515580c2c40d118540d020f129162802e50801039402004600d902040106500d2540104001c5403155410006000c40785860741418901c60b0501b10b040090600f4035900744141406810904581041c070610300d00107224100d03030015000d007005400a0300c00c0840d80208101d4401c800c400c02c0e0040801081542c58031030b4801c0359000ba034018035240e00d0325400e00ca1811201c105800200310050242604010788081d42c1080d201d503004412114500c500034070070f80e0b0111807502c3c8100c8140c1c1244c0c001948034001c1d8203845c84155102c034000390801006500801c0d400070f44016458950041c2a80140280780c02c01040780421103860480c2c0052030002141400d01d54907a545040380c1c0e092 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 619443210 1250 619441960 619441967
    0xf031b090b0a030b030d12051b0a050f0c0111030115080402061803011503030801080712110103110c0d0801050406080109120302090604032406090e0a02060c2103090c100f 75
    0x707040382c109a500e00580e0300a54092141c400d64444981e2400740c1601042d20480480d03101401403c2c42945e18030155084c00e880780b054a1202c0b07210b0510f9520b500307481d0703007007000d910455030900940c2d46000e00e4610803c0164010f98180c94100001b442c80090300c01c0e003913610785400c0c5ca000c0d40c44482440010085000d0300c1c241e401c070380e4000d800440c1e03112040c0800c81c01c00c00290000c40c04141190014041220100180e03001022801040e08000d231854403030010b801d00203040c15040548a20b21021103000190859284050400031603540940210000b400c003070080c010700d403086082500c0000d18800501030701303032829044820450344105680c400d40c0254020041190850000e00c03000001c0b50380012015844941c0310282d00e0f14512110486007110320039004015180d1808880d20058100000d070030029030340c10b0b51000d503252820480a4074280c05214010030012200d0407007980b4200080240d40a1001c240403541c00c6405401044100d841c6e00d200200020351607101414020b10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 619444460 1250 619443210 619443217
    0x90615061305040501080105180d081f03020d11011803030e0f0d0f08030f0a020a0c022101021308010b0111030a0e041103090d020d02060105030703080304061b0f031b090b 75
    0x314429500d01555a0000c9010744e1400d0f4884e60459548404001204956012801d10001c40d4000b070005500c3c0010701520201e40940011184039122050201c03041d0390443c0b8502864001b000e4010a205900c0e1918401144800c0345002071803804810800318100207000040da035050b1205010078540308103000741044191981580040701e40d03841c001084c4591030300e601c81402828181c0e968944502c100e25003000c05444e04002620410100c01c0301c0750700c050401c2070b1036411a81054444100c1400403c03448031842841d00c594400030324000100183c0d050001103400002c000c0c07141c480020015907110700100502c00998004100b84000b047c4165403e400c0c0040040002807044002010169150000c0b00c1803199644081250280150100700c103c0050509100404140d814407003c00d40b580481e10004085910102c003040820800c2d4106508404c00014050a20561300400034a00e80c2c46803186e10100c0e160404581c21246c0d8001710703083c80640303030311008101841c14040980507031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 619445710 1250 619444460 619444477
    0x32312061908060a050c0909010608041109090c0f04021911030f1602011704171c1a1e01080105010e030c0a14100504080c0d050718020d0509061506 65
    0x2400542032614a59107140c005025007002c1005011914142900c0c008907500a071801c14680014070241c00b550b503e00640c13905403240c1d4605800d1a843d14503200a241e18068101c0781d00c41c14800401400420008540d010998100d8522034403151080c1800203d1003910f4201103140100710b801e120460188030035070210f0b0261003c90303180122041c100c1d40540c22610700040c4042c1a01440030542da441500300c00800703800544009241815a103000401c04140c140308080c000c04520312402c50786c24090190408038403e030904c11118900c0c0d4014100400220251161301d4250001400c1c80540f406134001f017906071a02101a4200300040d19044000c0091607850703c101d55440b06a62989001c8500030511110900900c0d8048020450322080510f01c2d402000742c01d00c0104414000040c00058601c015294680343d45028206181400c1070742d00280414900840c08204001441e4024010303058852400c0155450782140b450302c9030000d0300c050b845c0a100408403045403a04074000c20109 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 619446960 1250 619445710 619445719
    0xa0b0309031902120a1806031503060f0605060d2309060402090a06081603050c060705071205032104030813030c240e010207140606010912060b040e030703231206 71
    0x80c00b8440e07607045076803005d001c610000d26022084d0a0f800750703005040f8090101401d013804001240d5207403c5240d51248000340600751100160f0440c0d034150750005000e408058242e907a643c00b10010900980040035003000040301c100300c03500c11024a03002140c000e0700118050800fa85860302044030070039002d014414143d54681c40040c80ca40200905e41004071000060307031409280d030412500301322528070f940e4000d40c410818040090710125803401554040011034050030708908005240d401200c87e8140c0700a480000107045422040120307200d584a40d44a01e01d903520710414400000744600c008010602d030086060000301d80f03038689507103000d600125000e540c8a042010040d60f82c880749040550358000743c8403041c800d1105003d1664601e4900030041030070200d00081561189128801c02400ba5410707203002c002080d0054034511b403005000b4403050420310120703a12640100000c9000c00c005020000c01e140e03c07002c10030000c40c40307171071030f682810310001203000d4105d40180107d0b0310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 619448210 1250 619446960 619446973
    0x10e1612021210050306090c2202070803040c09091106030a090203061608091912030908030a14090604030f05180901080105070f030e0a03030e010b0d110a0b0309031902 74
    0x241400d00c042d000800080c581c0800500303290310751503a9000d95420040c0207411400410030340071000a0011401007058610850007844405183d00d50704010750b68200303440c000a01b403c05d110062010718081d5004440b0941e0150340c0c0e007030300b000303c400710f001c0105000d801683c000803c1c90081c1c051a403180c040500450f10722455030000e402c16100b1990700000004480c0d54240c482d500111069001f4450b40c000c00d00c4009003500050f1401c3c02407001049100b40a02c5000800e109801096485070320840031350700c80c00c250710745e0b1000c0d041103240d48811010140020b03034031040c00215240126055207444400f41c80d03400c0100c5d01c40d44809002e03868221143d42d2290191102c2d00402d000300044e0300009018103002400412201200d840b100c20542451090440d90381d0100e60204076550600300042d29000780c255190250a42585080d800040301e0402d0302404a11070058210001c200c4a001007162542000c111030702099030071006c0740d441488200d81c000b40d9841655203019450040b10380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 619449460 1250 619448210 619448237
    0x50904020d14070e011803080a050c1203011a090108040204050903070b0117010e1204091d0105041208090115050d080426070b0c06070e0a0b040609150305010e16 71
    0x240c5042d10292084074000300c08100d80c0d141e001e4003a1031445800d190030112260900b4070714050382c0c0b403030101a00302c103000601c0c1e02107a4000d00803078040072409000d80740b4038a820f03061220b0300d400c03d204880c80e650342959600c3c1403001c440c0c116540804140c5503e4490740301e0f80c09100090400070300380c00311803008010300c2c00803581c8285514000e24909200c03010ba848050b4030303142507401906a0041640c4000b007005030300840c0300705903030a0f500d1100002a181c580150400300d190301c01402d800482d440d220a000038450704003241c08888241d46c0b035001e01501c1e03070340e0301c10b00721000d580c00c200044403604070500440c5003128100c0a01c0340112010f0b41406d46410384a0854440d1030410620102c5807502c042c016041406030400419881b1b0b2068180428000ca140d01c07034600410507004c0103580380400d200c90740c9a5403400054001d030f03a083c070b4940d40c0300d50024103000d0981c091601c030300035060394010700756200c2c1c020a0b050f01c0c0903800084064585545212010308014402828841013018104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 619450710 1250 619449460 619449487
    0x30504051c020c060d1a040e28120f020f0f030706240f14061602010c05250614030402010c150f050a0c0f020d08070e06071b0614041505090402 63
    0x120354015804002031b410342c030030191043c01041070407043c00350741403004440c4a40d001051100360b1344101550000c00d18104840ca4441212540004221410300d100091207103a11a041c200000507503000c85800c02642d4040303035600c0d0079648a94404e07900400466001541d1608980540c800c1b02c1d00114114821030b9007404004034a40003510510f903019001c100240315140c05503002304090310345d0303850040340d40010356060804880180c180850070b030051042020400040f00701e40d0190100450281402e402190102e149100f058001928081032003084841442124096a41612189a0b65515550301c2100c8481c01600b50502c55a4828821002e60b15020f072601c00c8410003000104048000c801400023010845040c00b10b40c4680f545840250704849900e0700a441c904106020141c40ba00048592041e0007004082c18518020700c001521303284403aa041d1011a1141603600d42e1311038240d070180c000c61041c120040100c040d1028103600900c000c040b55100688003500d45603401a100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 619451960 1250 619450710 619450717
    0xf040c0b09010c1205030603070e13200d03030e0c1207032307080120070b061207081507030c2c010c050a0f0611090f0f061207020604050607030504051c020c06 70
    0x2c0021070717400820070449280602151014000e80c0740c4a100ca0300b015068804004c0200900400103105003c400d0f07448041700c5180900c0c010002c0ca081107455082c03030b008002c2e00034020304143c00d21900c0381c58480e51400c01582e2095011800050440c0d500d103071261058100011961244602c00d50100700015074180b00700c4001d00b20030340010441d6400285210a6144000d1b10240007802c03c1c002c120002d0240b11009400603405c9401c1c0405600c00000182001d4141e0711480c0c55200303a9590000d01d02c4458015886110716403410801c0d4511004107035061070448110241e41980d8107030a03851601c1c0a0089006801b061501d010003403146c0e030700c561500314804425105450001c64000801c410790180c4550112614a140c0c1441ccd01d11011a002d042c00420092048002464198064807504242c0d5204141c154490800d030401d40d502a482d10b9044c0c40c241e4180c01080300141e140c070300034014580a150300400901c0c4059a0a41c1d40030b181000003d00d508600482d0640c0c6107954400018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 619453210 1250 619451960 619451993
    0x60b0315010315020a0f0c02030c03012a050a0c0b070e0d0b15030d020c01030905150c04030b06180103030e01090b0309070501080114090403050a05070f0f0204050f040c0b09010c 78
    0x1048207541181041e0110010708000d0b945041d0041041c0d456480d07010510954030310513414018160905403000034204a41801d50a8041d86480341e03c451520030f0b29445800080c2c24071012104907082d01084802d440b801d804100400d10380d1200d0400205000740d107650280300c5250000f84070103002d000030402481b1040540b100d06020080c030002d200c84961490504208a0003440c80c03100c1ca0718081d403142034482e100c506059031005420103006003485643c5910020842d44007a40c40c1148044245800c18001036a4072201140050b04030300b420700402860710215922140e40c1e03843c50740c00310340002c00c80d054541000b07105100001c040c100c100107103008494003c090003100742860001484248144c1c81342c103e041e9210040f0700b0a0f210708141c140c011b074040c40d10956a003501c00003651144200d02d801010101412071000501c11000b151030380b580e2084034148640d854040b00281c1d4484141c40117080d82c80041c40c01c118046204005003044201810a0300d448001038903032220000000c0308 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 619454460 1250 619453210 619453243
    0x3060f0405010c030608061f05040207050106031401060f140310050411011103090d1e120819020c0c1c1a010501020c0d03140d02091c0308090a030813060b03 69
    0xe0104000c4280126001c662483c40c0410420b03140007210b035a9a20050183ca40c80500302d8200180000010aa84094200640306554071049460314600800c907511003650168401c0c2d040903c485018001c54040300c4065840d09036007420145e0030060380e031001406551510a00e941c0840b0701c12203000e15032280f07014100c05820782a1410002d44079203290000080780740c1007040b1002c1c10b50344044030744040f15000750882d40038540343c3c20340c4d041c00582c00318040c00c000040227502c40804d81c41880d00c3d108980d0940400c0f40c4035090790810045c1e01816498690542050303408a00c0c9003001500783c000742c04401c0e0b02d1000e260303041d158804804c50950b26860030020280041c0300958040112651044082e10348010484031a00c00503d20b0900603d1000c1c1c04000081d0001450b819405072482d000300101107500d0300c017022042545420940e541140445c0c0a84001410074201181d000308d125023544a4200c1d50f96402080417014145000031107403107545001000b01c43e1010054220300064404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 619455710 1250 619454460 619454491
    0x50904090f05280813030b0a0c090e06012016081b060306032802060309060a061502030a051c050103030c030e0303031b0702030a060f020d060e060a051306050306 71
    0x7805030070400d40d01c40f882a40303400c2850503405450028442d01c1010b0308003607501e0712100480b9055040c0740180d031002e00403021400034440142c0a640c0040c2c10510162a00d4507029602c010484c0b0750101141c8003804a110480c400404605440440062401240a542c940b95001140c0d0440d240f8070f400c111040c3e400900b80049038400b02080310040f40b4111034030f03419032601c4000030307540e00a40340200c81c201c0800d000e1405004151601c4100265005041d07a13200d04e00307520042c0c0e60b4001161900a00341c18050001404208100c1301c5840c00b003c2d5010b0b500e0849140016105903121b01900d030722541298502c9490100180305070350107144030b07030349070103000d00c03513050040400f20f5528180c0d200ba0402c10a0040400009901e20030002000070280e460700d0f00c40c00000d082c00c44086d0040e00c0c2604224425609507425402003a03010030301c030001c100300c648075906070324030440459844e600850500e00c00c1c0300310314003044c0068000307041314000300b003140e150f901103410800156174241e200031042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 619456960 1250 619455710 619455713
    0x50c040e070911090d0212030f030f04061419180c0311152805283005040213020f0403140a03080f070306080106030c0305071a0d0c050904090f 63
    0x6014501280f08103180460600c00490300141c2c0030807141c80700902c640c00c1da030f450808500081c03080d601e600b0b100c50003440d282c1c50881c4003503514540031542255060300e000c002c40740609000340054010101d40d036002d013015900d000303080300610802044204401500c5104000200c03100f180300e01441c41441080e000100b90403c4c0103c5066000c00a85502c00c140104844a0203282080445560b1058900f01c96846205c3c1074815200303580180445110f0104039011855015454884078079881c0d03540c0c004481c0e4400500e40c0645100044403003a0008040c20344004996000190024001081d80c0301c0f040b00341081c04121303800703480c801e031010b04085410814008100f4500c01c00710100c001903d000282990000c14001e0010400101102a10007043c80a4420781c480b1000d054550020041140c503400c001084016503c01203803c0d2041040220f00c50507e07141c002030305041c40d17407040d042c03442e004e0a03500035218142c0c0381c20030403006110701c0c186680d90b030294071034041c0229000c0c02d41800c0c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 619458210 1250 619456960 619456979
    0x1060f08030408030d023708010915051509030d020106180b22020c0723060a08010b160b0f0402040c020c06040603090f06290108061c050c040e07 64
    0x2035800308105800902042000304008422160540c40c03903800180c0c2c03042030081c03400104402c000103a8581c100301c01c442c2c020828160000418820a440d0140160f80c2c8003003600589090351594075110754005010002804c29001c14855440148041814104000040303032402911082c5180180e441e0345d81045409980140c0c1c50001c84542d60510100074038801040b0700c18004c1d240c50b800d41c3c1405040c00c2241c03030b40d5819201e02405803030540e0002607590201041d80c0382c030741030312200e03010092440321902d00d400343c12924510029100c1c94000da00e40410305030150410001c0340035020b41c00c09a000051001400c06104488424500134182803030700501c4111105134052070155400410a00025981c00b4159001c0342d00916012541c89610f280a02440d4003018000b000d5900b0084913008220440c01d14151046a803000318954410810046032280e4042d40d007190002100d0410f250000b420041d040b500600a000b280c5541903003401140444000e0008440d071904842010300080b01e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 619459460 1250 619458210 619458239
    0x20f0708190c0c0303270f0f05040b030a03081801090c1d09060c071502160b1302130903050c07030c2c0106050a1202030f040606050111060403030e0c030f0106 70
    0x518640700515a045550301c40c1d00f00c0c514000601030229546682c045440c0014169010100d14000c03108070326502d101c4400d003290303e0f02498200c00b070b00703540101d002c4c03c1070700c200d850590008006240344613030b079241600d0416015158500340b0b021859408032040090040d054041d1152124421080c9000300321403029084002241401068200f803004654000440540207034902d1101c0707680c0c95880c50112a2a01c0e20b2003410003160010402c1a01d0700c0b140803001100a0040c100f8989070303520301440e0035025039250300c006c1d0b000c100c0c1c00c3c0025003409190702200b0594420b052a91403d144182c115140500580c02105d40c0c5062400c14414512120b619a100c13404442d020040484101c445403401501401060100003010030480b125500c035204162001d03044490842d924100342e0040680058200c0741030300c3c040e05002d00010355501c0f03400743e00c00a000c9140580340b0703134171581d504901501414020140d50301c5004803d15180e60b041c00140e0b03400304650000140701d842d1040000f10400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 619460710 1250 619459460 619459507
    0x40507030507020d031a0307080c0a050a180c210e1b0d11151c0c0801080606010c240b0f030a05030409050a060e07200318060c01020f0708 61
    0x60038102440b681d03a0f000901001c1c001c106080216540850386040400e0309042c419142c2e040c4120f043c0010444400b117015200c004065402045058031103041c002c1c4200c844c4104401c8940d5030310744911221140c0d001c1c1c0004101c2d442d044005228140710090b60481c02c3c0c1d1300c0d0078281c3e600c104028550004200c4403070304030b460080c0c4100142c0401d000550820b02e854000e041d2440607403007400716980d422003412144021805581d22100d5084440c0302d80192211900c4106150541074060303e400799071514100e446203030091066964910044032842900c01c0c045607540002d40090308584000c0c43d0f61143e218000c6400200602c10808001c0301e901080c0c0c4c1340d80030f41c0081000350041900881114182c9503007150210f0980c4416401c40d009020503402032040d242907030140485541d05c101950300c00b0355090240d6440d035003d035030340640b60b1040d020002c03078a800c00201c0303500c6402e101000d880c80d0380f040c80c00107007426620304045800d6401070034101c0c0e0f000342c0040d06059003401c8618420220 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 619461960 1250 619460710 619460717
    0xf060b120f090c0103050c09030708151f060c021306150e12031b0a2405070e0901091a04050403051b0d080a0b0f0a080d02070e06060d0e0307080711040507 68
    0x10b042c01140b464450003c0503031181010b4a61001031102c0303440d502183d05c55940907007240d140c6550b8502090301d030481c4403030041500c908a008149100e58071401705800d0314070307484010002450724405885581c180d10341260001c80110303444442d08628883e10000b42168610341c2c0c416043d52800500350b54113581c1040c80b804480302c0120503000300000b520740c5499040c1d11900908012184507140032581d180061600402c1240e42005031a176031070343c0b0352400000c1403c1c0456100e40c0c905440290540d5403145d00b2035602c0b401004100c00c0c9401ca15a8960142024444050203001003020b0340c00c00c840a4022840c00254401287e815403040b41c88484d01101604906011000041c4242d43c0a440c80700b40684940c54464280c1c1c0e1040441d030030b02c2d0700424000640d81d88000140d16001e01d01104030150040e400b0000f175551003810801d102d0b000040503580341c14031841c2d40030020034002c500f84460b480180325000003e40071342d0051080902621003c664101395904100546200070244800c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 619463210 1250 619461960 619461991
    0x30b0a0b180c0a091203050403021e0f090a020d02180a12030c0204090606051002101b17150603180613150b0105160305040f15120f0f060b12 62
    0xc01d10140806a000500840141c1d030312030031142c0803140d40d45940c0001e000f241030320300c00b03008040d044802801200e10075154000c041e1185c02811710248a0040c9440e0000103801028a0722715080705600c1c1e0141c50a6801800c006000c402d29040342c00c002c05980806c860301d95078000626124204800410701203004280521032960000e02c00b054021009008940700c1d400304040000542121011f814094100302141100c82e6000b503445034a90b609685c81842c0c58001807880206030242010700c01141c942c000e44400c49035060000c3c2c640180541ca440803042c080b80880d50b5042d0046000b81007120706440ca0141c482c0752103041c034801800024a1040c640203040c002107108284180a040100700044e440b0140300058849120f0052803080343c0c6007a540032010190014080e02c1a00e0841c100b203194541c43d00e043e03c130130418200c5c2c1c1e04041902c01103113010028103030704200c46a80341340001040031001c078499081a2041900a101e00381400705030280d00f0010f200741d065010384104101c112 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 619464460 1250 619463210 619463239
    0xf0d05030a030f1407050a0908010b01020a11040612050331060f0e1003060e060306010501170a0e03040e0108060603060c0405040207030507140105180a050d0305040f0c030b0a0b 78
    0x80c0e0344030300d5450303000781900c40a4107142c884a580c40501d502030f440405490303900d0228001050f903400702c0700c6c41001c01d02040740032654150500c50ba0743c0c402c0701a002031015861136107405c82e80c3c0340030102c5107922945441003c140150f01c640090741b0244120002c5032204501d010061007032460003d0115101c04408074500d0740000d0032610300843d1041c0c1452200e01c0c41e00001200c41c610102120f54020328005480500350354542d01c06021903020011a9a02d500c0d07071820540c4450003845070b940001d20350310ba03000d0303e00300850503203400c1000381c00000f401c0709040d01481c0c21074103d644036001130103c00e0010400c111091080b80d030703c0b08080700136054600c2c026100e495076001c1c60103814022640820000209405481103035400c07504004c050b001b44c01400040b034060081101c0145000740c2c6100802c07002c2d1000202c801f805540200903010707000103030004a004050041054820103e07142c10840071401302e07420203018502802c1c4c121110715010f000e9030142c3e24980321450150840e01c0c940384 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 619465710 1250 619464460 619464463
    0x1060501110a03090e04030522050a090e060a022203050307151503030f0228050c01050307080604090606090c0c020111070503100c0c020307140405010504020c031903150807050f0d05 80
    0x705440d5201d0780564551146c1c10b0456042c02201780d0075041d83e10702070034680f00070206121441140c030115868007090b03440304a580291614850b00100661000c0081142d50402d60040c14a0304003a510800700c0c01380b6031042c08445a47442d40706640c02d810004100c401e200b104121203004200a4034140040600034407030403c00c3d402448003034200100c4035039010b0140c0c401c0c8082080d40340d0707801c42c5508511040d0396104900017103103011200c4d0b00c1214628080c5500070300c1035034841e42c010340b240480e03a0396103000c4c0002381500a03811250155112000b18541e4014030507000d10303405a54983c0c56403101c6100241402100c07840703440403035011820400c89564000354600000800e0540803400b8800100c0c10b030740b03080d92028025414001c140340400c1240021944042c806400c9405100603640c45090000301c0c42902c1100ba95604100314803440e0119a4080000d5225689030014804400c406003a030070449c5900100344940000c01d0811551629130760109200300212030902100c1d10a5480a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 619466960 1250 619465710 619465727
    0xf1713030c060213030b010e010602010c080115030f02040b2703250302030a0f0b0c03161d04020c010204060206010e070203032a04150813030516110a060201060501110a03 75
    0x600308407031810710500300822a015128a104041103c07004c490300ca00d080f01d00400d09000f040488500400000380c402d105000e911800c0d02d140c2c440620342d900f4641200070841d0401d0800092640b42d0500103080312440c030040000701074102d005501c0790a0b508400b0141003d40035090342c443c00042c0340fd0b8542c1d0300441c2008241218154044000035040802520804c1541c4040c0d414062000c010040c0080084402002441850240210b036902c000b0940300d07010070f580030304c2907850402100308403038081c58542820084007400c2100003038003000050141d902c440b0072144103940102c0d0800c1407540411585001d0140c0040d0004140f8046000035035034000100812009200c020b404001291029021140069440c010326540c54507502089c1c001c0b280c0c03076081c10010b0001000a032424111036010b443c0c1507072541d2020b140164058862050914140c000c0c2d95502500e2041482030740c0304030584008081c140c00100380c4d10300d4140090081c0301d141c40c002d40c2c60f07000810120300003a4000b50f031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 619468210 1250 619466960 619466963
    0x3030b1002060c0d1b02011b03140f0415050a1a0405011406030c0c01090501061d100905060f061207090509191e1d0d050f0409020c0a02030d0f1713 65
    0x1c545401111003a0409455000e40c07915118085c0800407011981c190889a104401c502e2009200c01c8200c90450880b02c6030707440504144204004140d10303201e51805107170410300600840c030042c0c507002c82c40012a03130203940c5c51a4440d580c0c000c003090b5410100000c2c007101821601085a03614044060740c1c68a515056584035140000004d8545080a4255200d12504000800502800349011402448203000b1341041c11707080381c82c000c14448454511445600040034066680f8030f80840200a400040e1442e80d008005009951a6840e080003030607140540160303813032560410a41c05804022190012800303141d0344400c01c101c0701c0307060fa0424615204030000140400006444c00003811071042603c501c14140240200100d035280d5611682c040e8070000d8501d00c810036101941d0b10300ca10341c1c4020013584144010002000745a01821410700030900360b841c41e42e910f07400282024041d01e111300200e900c0d00c2d0590000c60344078071030300044640185100044d04080d41001e45c00240c9100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 619469460 1250 619468210 619468231
    0xf060501090b07021906030504020f042703023301080604081605070302060301120312022d2803050907050a0302190e100302030c03070f06051e040b0703030b100206 72
    0x12241d0464407095054005e80d038407030b001000002d8507880010017030141070303d0a03481205c83d078204002c0c600e454440c140d140100e103808008802c0308812024142c40c49a242907096004403040082e950328104508002e001100c5040244c81e202c0034040f030841a4180c0040d24a0b83c009010040000c1b84442160300c403003403500c2000304006040c82c00d10b1070020039400094004502000004074034070442d00788070b0410701c60f448181c407490400350140100d0240f0382030b00c5880b103040040c074520a80e00318200b407003d080c64012980761018075501e1810032000c1c2c3c4044411b105aa4010101300da50511a40360000c2d616806800d0f4a03280c10006000000c4500001e40300d0700c80d682031004500c1040c07501d040100004801c055451910a000120b028514032080c0e0190141015682941c5400310f0f419041d1a601c0b00c8003440075003070100c2110540c100d121718680d004540c1d0384c81669003031004c000d80300070541d403a109543c0e00c1403440c0c02800e84180510460003192000007240d103068010406580c00b40e00903d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 619470710 1250 619469460 619469467
    0x1505010b03040209091006060e09070f0e1210020a270f1403190605091006030b0c0915042c040c090c200105180d02072c15040f060501090b 61
    0x3c5001b41030005180c841940c8130b14003507000504541001c514401e070713131044904480c00c0d0b0b5140d4090703c02c44881c5031004001810365003614450329095000000004440b0100c0b015003d5480602c07089900102101010a940054848007001c04401590700d4150b55240300a016140540038440f4440f51f0240030900002000c102c511900e0070444908040c101402c041c2c3d5800701801d0190091005458210950255480404201109005000403640d021100d640140d880900b542c2c50b0390041060654455084102c6441410b114405007019040c807090500d80039865083c0300000814844914200b15035050802c0003042e18544040300310380310310360003141070200b10800b1180ba07a40205210310405445a2000c001041544210f2064030f11001c60905040c00d580d41517600d24070101340c013005a1200381d081c000002000d0f642c0310201044120711803104005038000b001104221180315150f108804662a14503142c050a00e034084024010420281800d0000704042c905000340d014015001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 619471960 1250 619470710 619470721
    0x803070b0f060f060d1407030c1403070201090b09070509130308070309020a05061b07050d1509020a12050a060c0e010c08090d050d020f070b0f0901030510211505010b03040209 77
    0xe0340d0f003c0b0064005180690b2a0f007040042c10051018045001601c2072100002d45541c2c008d11600c11200d038640c40780c90030071850012400f9294130080a0504654841d60500002618000b08500030010b4201610003136050800b0b00840e100003c0180c0840c0100c1000c0703801281d08601c400c2c0d0040094600490842400d00102d040317028141e01941d0130074400a021102e160481c2d6419400c4410300d410380e0501030b038500c1001100d241894001c0e1903c04c9208800350b40301c860340d01c907550183c0701510042405036240c40241080c0303003101055449801c81c404010801c4031910a1f02a030341c00d1818544100c0c004035000a18840760180010000500041e01c040c0c2c541d00c0410809400340e11001302d031003c0000f00c4000b9100c103004d204d41c0055129425000c1220403488054030101440e2100c0d150400c1030200044004d42005420702004144210b404105000310940c3e181003800c4a208000d450b5071140340071016208000c8101c6070203841d01c001440340400780c0040b25040368045030068110340782c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 619473210 1250 619471960 619471969
    0xf0e010e0904020121230c033d031208090715020c030307050c0108181002181302180a050a031205120108060124080a1503080f0409060803070b0f06 65
    0x4401944000c5002041034170140603094026105810740e10400c8840c408803002201d00c5c1c00030507143d40c100d00c00244001400f00080803148804482c81c0005103a65284002ca62964040300c084600c3c0b043d82d000348240244001d0060b4204042c0f61032070000704078900382030a15110460740c012042032400600c2c021481074420408025000b83c02010740341d413040640391a03981c401c0b21801041c0450078500000345e051a040f441c2952541ca008054036070764000400802c029800003800c40003011040c00c2582039a194107241e1744111200301d000690b06c40000030b000e015480200d15461058805600510850302c0c0c10b2420341c12a50701048910301d24052440c01c0c2d405010790748a10002240c10700000603245130014500e8101c544402000e4140c42c101040490362402100c0e400001c140c191021504075080340e40004080c91001e2110040181c403a0b4446080e40d10000d00401100b0002c0340c184102001489200014860b40009524115040d560303c224150010481c29002e400200000c2e12030702d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 619474460 1250 619473210 619473227
    0x30702250905010608040c1418100501030506040c0c150216050714040209010e10050c121b0c18061504091a041509090606051f0f0e010e09040201 64
    0x450049844042410161405408203612034200103905003400068035a015a418600854102e503128802d2070900451103008180045c1081d009200f00d40000b502011007449603000e544a6050021968604000103044c0c540162601d4412807401244080b2280c01604042c403a0b41d03c0500311500380d01205640c0c000740511401c407514002072504000802401250110540d0468000080040844010301080b030041035a0b290100381c240d18031442a1031710107070941c4000320038a40245054030b451081410025101c911b06041080840c001e02e20540b50142d041c992302c90a070041c501a0343e4140081c0b451a510400340040c1320031034021540c3e40c0c41303100303001443e02c0080c05117030b9869a413802c00d400140fa05d000d01500841074029100c1d0a45001e001c2c81d030740b19048070308401900381800340000c014a0880c00c1200e101d50350b804c1c00034050f1210200780c0881e1440d05000d1091050f0390340c010b03140810303a82c821303803c01c107031050b25480b141e0700480c4103c4000000e54550b5180e075107910050750a0103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 619475710 1250 619474460 619474483
    0x7110312070309030510050103020a0501030b04150602010c020f06090d0f0903081201050f030f0d03021b120301050a06080709060e01030e121b070806060402160c06050406090806041205030702 84
    0x300c001482000707042c2c000200c001100c0c8a01d0450300151101403229007140d200780002903012181138400c22081d8400d070449243c080b40244005614201100a09030205e19580041d001d80d45901c1d41016445c0c050140c480e80400c07078009001c0e1840d040c0f140c030341c4503003400e9142d00501103e52242c0f040c16100e03016440141d0340c844801e0b50744105425002c114400240f003110700c9000305044e960194180405c1c6e400d000d2951400a1460b004012010340c00394000d00701850502c0080d44c80b00d241e00b6800c1040100c0d10304440249503680d41058184070508036960803020a0080b08800d000303203da80050454100d51607440c0c014043c12030000100c2c05040d040c84d00702d11911441d02141240e56488000b8449422402140301c00307070000d142d8075900c400c1948a4511142c1040000540310306154008200b1540c1102504802100c290388aa002d80e5460b00220b0002d40301140902090b508140b040c0d01600c803000003414285000d503505250000340c03809101c10030801001054019000304041003224 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 619476960 1250 619475710 619475743
    0x111005160201180f06121d0a35030a0b18042918070515040e10031e03090f03020607020112060f03060207020f0d170a0210050703051008030a05071103 66
    0x240c5d54007000b8440e040701407880c0d00e5140350030507908212241a20800c40c2030072003009071485140c951038143c040030414507403458030503100c0300004200142d441d6441c4074030710f1251030307a03228100a20024110341c00d904440b400740c4820b0707201c2c5d40140e46616655501c180d0220305005814a03a00d1038270700001c80c07200d022806603600c8040c07080001b410782d172102c0340503600c1d4112080255600e0402a070700b10710310380e0400c0b061002c002c20b120340e20351101700551080c050340c01d4191040c0c0c2c0741c3d20f080b02900415018068805101c02a070101503004202c00c0c001d00e00d99420500f5141980c00186075440b40c80d4000b03041c051001301d00708290f1119000040104880c4007291400d559900f004000781d031000500328070641054180860790300d8140340c3da4581c6500b05807096094802c0140c41d822640c0850207030425031040309038016614000d0f026040c400c100300e98010400b814080c0c01522001025041010b00390030900c100070b41c1d20340c4076058908007a04840405044803030000442d0401d40d0080040c00407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 619478210 1250 619476960 619476989
    0xc07150c020a1704060516060b180403121a0409020f040e0307021908031b10060b040311010207030809010509190b03070822110102100911100516020118 67
    0x10390300840c5004196018100f58a80018014054070881c4914014a0301184050110218401d2012945d03e0300c58481e55001400760910310000b0032038a00414000000540b090030081010350040c0040001c200e4072000380161411480844004491240c1c8907021b0380c0c3c0c4840e240190b5565260840c030301100134108100d400609018543c070b0303a200c100c06a002e08030b024a0010042403e03e01da5044501c0b00001c1d50801c00341000300311411020307580640840c42981e2030741307603508000d10948000300002501e480d52a899071600111041002c11b2240c1550032021081000c100d10500f181c107a0202464070799642c540c1e900006941d489102d0460071401000e00003c1030b620072160007180034035540d80380c11900b5a14113090740341c5000b429081e030803070070b24404d03071200011540c0900e003810050500582e1260288101c000342203d51440040e104044083d002d96140d0a04000005003410545490b510303080705a1494034006414203002410000145030124220f548840041d0181c0303020300d0301c40d98 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 619479460 1250 619478210 619478231
    0x14100f050322060c080702010c05030f1308190c0320070311040e030d0207051e070312050c0a031206050105091c0206160c081b18100b0706050115170c0715 68
    0x180c6070300f220006c025602c1c02842807105401130054074803520b00c2890705001607a41c003803420480710701407400701e03903190f000d12080c000842c40310b003000e042c00420740d00d0381810051401d0040c107003c220071078012001c60002d920451440041140700036a50003d41c40700720304102ea40810b0007003007001400b84050002003070302001354401c0e8005000c400d000343c044030310300108040004441403205214444562206100304001040c001918510540b40c2c10550b0400d50940203480c18040f041c030003140050b1300d01358030303c146417001c0c845c500207001c00b8a000d6041c0070019020607207481c9203445d00c200300c400c042d03c0e03c1c003195074800403240e405046c513036452394221a0307190031f0795119024080c542160040048141c10001ea1110030310701d9032802000000d449400124008002c1c101a10035007210800380808070740e0900300c6008184107441100001615890941d0320001c590400350b400d000c0000e4508150351048c241c41c440e641003c4510115551020603182010304460192180303610141010341d80031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 619480710 1250 619479460 619479467
    0x50313090203060a1a070f290a0609020f0f130305071e15080606220b041e0b1b19110906040e100c0e06030114100f050322060c 56
    0x5004034404d5805540007526020100781c3d20075511120580b2201c02e120480c04200c943c0b45980781e0f940039481c20000181241c80709200c1804c00b142000130143c00303200744114031000344624401420b26803821401d05541c81c50b10142d45c402e03414409a24400810000c043c2d81c4c90b40c2c603000065038172408507011075507610f0500302c490003c103640c3d0446802038103002402c1c09404052041007462030b60b4403c503655a82c82000b0315030f0000034148401c3d20595050076035442c0e01c80b0000300070b0000036041940b40c0f46083c406400a03083e00c2c0340da0007203018011082000303048520640700030307404540380780c41d9084080d80b1700d40c80c159215021442c4c03580c0c0743c884c803010b20055241050014000345c40e1903070700b41d035003005110276600381240c0038206610420300c205034005d9a901a800401145c0340030745107a480328000070881c2e042038220701241c82186008400c0d518103641660110260360030400b030541d10310500600f00c0d0000030031640308480002110740d24440d910350143c0120f81d01a41c10402c047c113041008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 619481960 1250 619480710 619480717
    0x2030109051b0306150304080c12130f0b03060607080d0f0c0906050703091a04050d050d08060315190603080c0604050c0402070c03080906190c02091b0904090503130902 74
    0x145100c2145031842210a25000c04807813290f800a401e01862400c038042403516588014001e0314402c40c140012080e140b014808100751151900e4142e4440e00314910229130038080e680b1880d40420396031802c0080703c003243c054a90141b03049940726201c04603810000c90511483e40c02507400c6150050145000c1c01c242c1c0000006162946c900c044151601410350b62481644006004920511b03001c0000360721200c0c20b0000050b1038640c240c28a42c0c0e880102c3c203115403080f000c0fa4607802004049e000d441e8030003541a4880c00c01c070b00800d849040104106c140c5600035211440c11821001c03041e5044107183c1007031004551000c20b855885550502c0342c0d803510b0098400b2503142c0180351581400c1d02c1e05009440313845412100b034600da5440e6a81d0908c10703620291605810050912048400c0c106910700c49200300b070306880d0098452490300c1000000070002342080c2001d0324000039400d90050f107030166814164140d40000c2c102d1000c1c01d1151860041c000c1c1405020004040400c40310130341d8015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 619483210 1250 619481960 619481971
    0xc0b0703030c050903031605010f0227010804030804030309053306091b0903010b061902010605091012050f1c0809010207031b080403050102031512010504020307060e01120203010905 80
    0x200181109010304607028800d29003505c1e410f50050000296081c124076201c45c80c50b1050b00002440c011000001003a60042c1c4161106000c4003211002030f0516010701c1c026012091130641100e1419982c00342105c1406031001e4105a600c0401da4200305c000c00c1303410300c0740a002c1440c0c42c21040d049000c00508080d180d4110040d4403260100d140e60412078005801449a0903040035001f1040914000710380002a43c11340c03564880001a0f0180c0318070009120722529040c51100701010040043c0c04d640c400d0f44054040c00101c020030440c050006403800960362070242409001c0d90030f084c01303443c0403000000e00304903015060340c590703041155605174000c4803000d8860680580d01d03403c80600300d004401c40600841d01417103a460b14481804031402090784510203c0e802c20391a5200d42e800c90304100e822980320304020400506901d410450700d42954482002407203540b4155020036140d036414880d1030240850444020901e82c000c5608004c00000384404648940e502da501d030000d44010b035803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 619484460 1250 619483210 619483217
    0x20403022803052b03060b0d0c02070b0409020903060f060d0b0402030a021807020f210913020d0f0f1e0b060c19120207060905210a030c0c12030e040906090c0b0703 72
    0x100301413602d0180c082c1000b19143d0110f224204021000b0450141c0071108080d001c5002c0c1e540040f40c643d8101010780050880524016100d020000905186c840701906e400c1481c40c10340300300022590346c00703040e0003415404041c2d5a1261520300c042858040706202c02580301ea4062042031100c0200f0b0301036841b824036a8200c80c0d080c116400701d1a11007003c80c005800c02506983da42d5503421010f002001103210241521004004804612040741c1240325880b2a190300c0c1c002112100d0130a016285584554080c01c1113120040808510b600c0d0600c2c0c0070720482901ca20607d0025601d0030700746c80c41c0c0000c50041d50b80c2c0c100260002c5a40f1204840e040b5420024000090201c40c8002200d00541c0e5851321810314081c103190410103280d40e508922401d403041004c2900c120407040c460018030300d00c1703500d0f004819262483c2c164012519600890381c2894154180c401083c1d020604441c0084140d9000a44010710700b054005801c2062020b040154540f1303000030140780310001005018040e54 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 619485710 1250 619484460 619484533
    0x60f0a0305040606170a0f020f03120310050f01021b0102010b0d0501020c100504030503041103070306110a0207051c0314070c0b0403200f0f030114070201060906080102040302280305 80
    0x2017800040c0e1141500c00000f82c0d11440010300041c000f17202c1c0450b16030004100408451100001038544000005414081e060200c2445580c80d403003c4d10358080c00c401c640d440814072003040002e40c0c1e00c2c0007010b015079030701000ba04952140d0003036000c0f800007e0302800071407074500f450034454040d42c40409035004070f00c5a06039440c419651880b0b0365000d1581582c86038030310f4032552103910403100c013a40882c4e403602820310300000081c1d81d8400d558036820010000c6403102e26422029060900c25480240a6610211600b00018030030101c8074810fa45400e1502c00000c0d000707210f44050151820051444460940c049032841901e0043d05c2140d1080c0d580d43c0c60001800b0813101c10401c83d41000390010781c4210a1019480c10a105650140000c1e000168407041c0085c025100c0c001034880c1e00240c0d54a0005202c80081070007040c3c094881c0b07100035441c0070301e580d011402c3c1490042c1082103c08030104030740400c142e26500b4034000d54020040700d01007c5544c85001c61903a90304600200b020000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 619486960 1250 619485710 619485719
    0x5031801290d0308130501020d051303080f010609170f03041d010f080601150512180c040e0d050a12050c04180e0d05090120060601021e030315060f0a0305040606 71
    0x2d40b01c0304109035060350365503907035154941c2020003200740c03640440c0c0554084c4900e84080d002480b501c3d10950316191614881d1005041c0604072900180195010280160050120703540241c40002100c9200010a245001c25030129040c00c4802c0c00c000300a0000290000d040b0010800442c2c00311910341c8203d5250743d840d000b4a811102d18840c42146400441c01004540001d2408090034001c0781070452509030581100c040100003102c488503078401407841e050f15080c0c2003180007050001a00c1c20000c4100c2c56001556402d10b01c0981010007a0000d0888007051003014018006071407a14140294101030300060300540260241114551110b120826841c0c198054080c40f2070358180a05446030441c0c10450742e60784840c0c01d060501c0070400012144078160024212610b0b401c201601041c10800002814600381407400342030404c458002142800e00801240d400000b0400130309170030034504001c18454011401e8000d500c032400725121200d540c243d000584158400c410030040c681c0c0341c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 619488210 1250 619486960 619486969
    0x270f0405010e071503020a0c0b04050f07050114040e07020712060f0c030603020f041a120708010e03130611010603080301061d0603100504050c07081b0c01030b100503180129 76
    0x350b200c1d002880300c1c400001130519003c0c1d8020403404c4191314108446d03016a403a04a801601030714103c80c0c6902840c5a0810f0f40424014080a00303401d00c3e10701e00524941000c0802c900503802012a2002400003003150b03a40200252002000d410f1000d02240009042c49802005099aa01030703141c14460080d229502c41e00c600da00b902e034028466640e0031040070520000b0b10748203050b25074410400000300c5840d501c052440200388423840052138801d007481e01c41401d4445040c0340c0c08403903100f8461840300d0050307401000255809860020043c00b50342e4140750150980d9800a41612000400450702d180e1003108090f40940140b01c51101d04000c2080c004103110031202101e1541c12080280708500e0207070050341d00117a401852a0529440d40c4461046d076002d0500722480550b1008511340c0c1c00403c1c0024010a4400d080070000c00e4000801304414403e400003a5040040c008005040085983c50240249040d4802041102d903014004000c0d111221441d0140380103410181d802c81c6003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 619489460 1250 619488210 619488223
    0x106050d030807030c0207051309030e0f06041a091c0b0906191d03030a06030201091e060c410303010f0501031116030c0b07030b0d02270f0405010e 65
    0x500d55540390b0366585261080707008001c1d4249400850264590001d100d40e203d02048400503100400054a49101c0c9001781840c0c03081d09101b4000d00c1381d1040c0c541c40e03940700030a907412280c2040c6440c42d500342504580844c0d1186420070707544002507404c0011141110440a12028400d001c401180d407120342800d50340718011510340e084605c4041612500d04201d0f0803552058800c0c2002c0f08045c1350314801181507410413034604100551304c480420075585e0024111000300052007801110000403060b4280145581c0909018010401c402c1000c12007000158440381d40c5250a0511501c00764481c1c403100c482c583c000420b5001e032041d070b41c9040d038008412a0704031040700515040c114913000054016102460505040300c1c000d01010700d03100417178004040010b11079545d13a5501c0c0202d160240400d60040c1141c1c0c2003515244035074095807511a0141c503000d80450752022000c440b500c00d4801012900c248844014150302403001c3e01c24a0703102903006a1103400240000581131001c00d94518 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 619490710 1250 619489460 619489463
    0x708040311120715021603111f0e090c07051b040e030424020a0c27060311043b010c0c05030a0f0509040c1205090304060c1104060512060106020106050d 67
    0xc00c0b1210800c9058181311a090401e0b40c1401615211984800130008440c2c1e198825078802110407911541d41c5030107180180c000081100001400d031006500500040030f00480e24064418140403921004880c1c0c140c412556002c000c441d43d0500c1030764001d007454000813403240102e00f401c0400840520201c1568140c4045500001031138111109650412020220140c2903020300c40c003681c0403803108441c150103050445070824011034150103101444003a0b02d42d450030f00780781c0103050000555208150310710745000c0f2008212990000c0700c60b04500d00d41e045100d0110408078601c0c1010300340301d10400e07590318a000200038a020300a4241e481c1024424000c20b682c004100d400043d602540c0c13030410080c001d103852400c0c00304850120b42150b018400000101c0d80d104080411440c0502941c0c5d400100310300a141843d00d4810080c00682e0004030050801044141d018020344840d80002d00030300307004210740c00d092400c0454586408080c0900e500550070140040313840e080100300700380040d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 619491960 1250 619490710 619490713
    0x180605180d050f070b01030f0c080a030f050d06090c0e0915010e01050315040606082e06050703030e010f02031f050d020616020904050d020c04090525030602070804031112 75
    0x81011490440b45544880d1064038030240070f0000c00c0c04502c1e8000c0d943d020354440c0f00d03c00d914212a05200c04224055401401d0039480009044000f0b82e105800134140700060030519120020300100002416203500050810f9240c9a480400b41e5808030741c190101405403507010803615040207087d44d5411075040140840c0d07a2240c4d09055510480007594048a255070200c400407440001600703171002940241c001560303500522118802c8011240780c030414442c5001109598110300340340080d41e91140109121001c1060700074180640c00c1440110802d01c0204060320624074010002d4000781c2e0a204084c1c05030001040c0c0300076404142c42a1340008101d0481d20603140d00300407076039010907103032003080701d014060b540140c48851999000351301c181e010b000c04080040c0000c2c07500d076a109035940700e5400c0c4490040480c6010418040010140c0080d90310f4110060000000c00740f541d0005000910001d000010b0080c00c80c040c10550344114050445000404d080028003041965404586d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 619493210 1250 619491960 619491973
    0x6050a03030e0d050d02060415020703080f100b28080103030e0d14032110031110110d0309020405060f061206010210020c030d0e0708100b0a0918060518 67
    0x120303001e042c42200441004190784403c20590ba02c450a12906409010159201000f400104142c1c1024140c407840c490308210305100480d2801000c000c4050200c801300590b040c00f04107440c043d403c440c0042c0c082245030607036032410005040009450720101d25454040300c01505121446001d401e4101c81d010b940300b00142e0f9840e02040000031050f0b100701c2d0b49082081e44c24501d841c0a1010300510207030440088055030003907015604a01006080b07044150440c40207000054030002e403030080704001d6450400464800c0002d13244862120701050041c4106030300c0d1222294150803080407039100355002c1c002030321510b081c05010504195a10303400007007440a01d00980c040702505511950510450b42a19201c0e49102c003241c1c4042c0b100b50f035503000000c0c090220030290140341e031041900380082400500d0500e129445400140d6085613071030f01e0f1100004544d0700d01c9140300c0500700c0d0200030051950007040c41c4503a44080c000480324242840e00161034800390702d007040115013002014000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 619494460 1250 619493210 619493213
    0x302030702250e010905040c09060501090b071a010f17060609160201061a04090b030c0904030c0c03020a15031802031b01090e0c0c0f0a021f02030903250906050a03 72
    0x8542d0b10b00741c400c020140148000034800c006500c4240c0200180d0a0010380d03401d0509004601070303010b401c28504907080c02c0c0c081000740d0b070050140301203171002d151305925404036250940d00c0324690020703212100514000031600d080261488001c071805484c040c07a008a20141454540724203c60305903001030b41c032000500440380c00300811811880c40c400010180d4031000b01c445142c1381c403146a404008003090034410445a07100707900406100f28010011103106030001155400c000384018200804c2d03209002c108500c291254010310381c018000400c068580f44003002200d504c1c124040001d00f00050a02c81d0030842d0760003104103030040e0140880c01c50304480740d55120030641031303141001040c1c05e0000d2802d07203040304c00340649091040140c1c0c5000c0314081c1ba15101c618102d640541e045451594016034500f41c07001c0201c00035441c03004d210012000203a00f9405031141d0503406015031072142014000030100b000440e20440481c0804503110b506090440700c46000b82508485804011f00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 619495710 1250 619494460 619494493
    0x3050c010f1e0305090d020304050a03060b1807020105330910090e011b0f0e0910030b070908061005060f0912030f450f030106061106070302030702 65
    0x44140391541440c4030b20710981c8455103400070740e00542a0001e07603030b1014020071000902801c1c04c0c1000a100450405e400c1400140780211248801440c1c02c0d501e00ea40d84940d256614009480300131407158003207034035144501901802c404c484807a0b049021040202c003252402c0c8041d8038807214040386d040509165414000304c903401070072141e560008414005040d401ca0300031030444010341000442c10706140f200b03d891104800712208180003600c8804240140d10144802c4121030071a403803d50307130700d55200080480d002c0d0380003c0c00520089013009003968202c041c42084070100c1003200ca081e80c4012001c0c441020f01d008540c0e10110030024002500001c201800c0b610000030280b803440000c101a251444c0d020040e940300003500810900101500d6102d00e881c5142d07449901010b8903080c160000c0d582c0d9004032160f10201060003419056202e0b40e0b10218001c401800822503030f511008003a0a181034640002d00c00e05c1440000b43c0c40b02d1090081e2030182c1c1264000304484004d01d140407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 619496960 1250 619495710 619495727
    0x9090e0a14010b0307030c0e0a0203090616030b13291305040611070b0106080a021306080a1104082a1c05030708030a0f0e01140c070303060f08010204080d020703050c01 74
    0x4580075900c500c01003c0a981c2071103810000c6101c0e8081004252810141c2c003c903260050180c0443d604c14410066180c00100c0c145034810400c4014040c80c008903603054008014002d01d09402803450307121105c45840a070f106000c1d003c1c10603440110b86600e5180c110359000300041c0642c0010291024200c20001a001207802c0b5214800100300c0b904440d2281106800c40e190941d091140000100b000c070750400c1c84140c0220784103c0035490202105201c2c144204984622010442000300143c000140c540c40850b60045c28400269039556a00401e6030b500400d61124550004481da01e4048141000038882c0461018101452070226441503000c075820011041c2c903032f40410090240007501d62001581700d02841c071000203030300441003000c80881e840c40d42c0b100640ea140101311901711560b20a00d83d0301160b050705865407101c041c41c084016122960008450015000d030216244806401910903181013004503000864040403caa030f0744102d100c06010f980120802c03a589501c0341500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 619498210 1250 619496960 619496993
    0x1b05190c030203030a020a020a09151a1303080a0e0108151504171c02060f0f07121a012303070e0d1218270b030f030703050301050109090e0a 62
    0x804415941d2600030a08641c05149110016040404000214502200c0d20406003c05042c10056880d80c01085a5502180d004007058407056034101041c2c10f285008984030741a00b400191650713690f03450034034225086040020301203101d140c00e12802e94401c40005200724000010010514041d005000b1407102d241004000482c04000100f4240d60f41100c640d1042e568800912406042c00c3e000102403040048540854010030203004c9502d4010301426080800900c5410154482032800c0d282072540f003810420b0b943c24259090300007951602d402809940070b89a0a03007448207541040c092101030442c42042c40001c2c000b08100c14424403482600a80140c941d40410320302c0d03101d00c80204e030802c01d0a000036041c51444070750415518900b500400d401c0308403810899480c14031003200c4415090100c1031a50700d054105499038100510600f103021001560f55031091410010302d154001d005a41c04111040d10001c6c1d4030710103100b540369140c10b00021344811810b95494200c0386940554 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 619499460 1250 619498210 619498223
    0x703030603020612092b081510020109060c110714040612060c120c0f210c05250c051309060e01141807050108090f01050f01061b0519 59
    0x4801a01c0b580c000b801484d070140640045842c2c54401d036841c00c40d08010080032091000441b440ca001400303150361b5100710600b40080c081ea984c1c04080e010702d01311055284d0241c029402140718035010b60207622924080c020611010182020a4032200300c0b6040714030856101c1030042200c40960b143d0004401e02c01000455a140d543c0c1d10880c003036902c0b240540fa0310b41e944846900b0030b40c000d60000000000c1e10310a01a16079080b20241a50268000490a10140440c0d41a09110000307541c4c03c04507603850100310052a03850002c00700e8003d00003103406a005002011081c216079001c1c101c06641c040c0c403003104541004184020010120155501036460303404410001d6400e000f10b00051248100000d10080480c940b034040640142208602d240e0710f81031103401c07900110b0802c003658001c0c20151602c3d1111084113240000040d900c1d8129441d200502c69210340c40c0c04c1350790480d503540c0c1d00c00000600086452040d000c1021004000340d01c80c95194640c0d00c1080100c401107400b411 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 619500710 1250 619499460 619499471
    0x40b011704211d0901051507060b09040c0305070803032401020a1a0601090603090b0c03041a040c1a0c1e010b04051f080f070303050906070204150614090d0602070303 73
    0xc0c1c110040b031015441c901c00700380144105012500e082c80099800b40c8115a0b41d4801c1d40350002041c1e05902000c06c043c4000b0001400c46c0c00d02c441600080c045a078080e005000714541400c0028400e030440c08119918019001c00090041d0000140c80c05032014090002a04089074034244000d64240345650641c0104001c000109010011604500c3e201802c001c2c550314010340014000382854028509052401c01e801d0049049600c2d900ea00ca40542031440d0380341c58508000c0020900201c11074811400403040008202d00d400221007121103840c0c101e204500c881940e01d50742c0c0601001201d8542c0900520816004190121640060b000d0000101882c8141c04235081d204211610705001e8814480030038072a001105080c02400c0600140280d078050040d05030b100da01c01e1001400700305000c1004290350303881008070750445074000c20070400b254880a1611400411b07124140100c1d400071810441c59603000300302c945040c0000d19034040080340741d079000300079040300e0300641c20903946a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 619501960 1250 619500710 619500743
    0x606011206051002010c080c0a17040c0f080a020405070302071a041502071b06170f04032a06050c03130201120608060c03160c03050901110c040507051305040b011704 73
    0x203e19200110107500108425185000292119401501c1120803038410019242e015034800c8a404919040314802d81268846090041c1d8019403a0003000e00c04400c00e50000b1078440c001170032841c1910075201800140c0d80d445c2c0c00d030300324029800701403c800a400466107511820f5101c16030700910444404a0440c0a10941d208903086102d0460308903200341c5071500e0080346218400003c0540b0b00d03140030700e10381c0d14101c0001c809028102e04658001e08000ca0b04140c0506c100403010700d0140001c2d0309031066458000c131107903030001c402d1360342c9460302001c00c1d1155a42c07422248078080455800307500b41c445500456040d0740b0100e41d05013960740c5140c0410046810300005003d17a04030f207185034407030070054520390f07004404d5041d1700188a129140b00d800280c202d400d03142c07690400d0a1914007140e07410324040c01c040748002e2480d801440d00d41040200e640150141000c052421600d0340c02030b844034103200031210552195404202c540d0750000941c20103609140e40b01e4403038020990790180c0c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 619503210 1250 619501960 619501969
    0x1050603040f06051f14101101091b0e1015050c160f1706070806060f07020d061a0307240c0606030b0f07020c0d080a0e180109110a02060601120605 65
    0x58036400e0b0388400d00c00310400c9003c0c505c80c040016040c00c034508945521043d001076011500840ca14040c000d252940c00d03100c00080d84030004050704002c940202d0490707080c4d007080981e01e03801514520003500001c11210080d9090020030380f80b171450b0101d0a264001420303603142c3c00190980b0300c24420039001040b0050790141d110002e264048010601600340000c010200c0c1222a003040b00740d00540c104400749070700c41e81c001d4000805845140d990074040c1c0282200b40300e0108040d41100c15079094004102c00b56002d600d007019a030301845001c801c00c400700f648072001840ba0810140c6400c5000304004101080340342500ca0b107040c00381d042061035490005842c189d80c4240c0748000381e0020408001c44041d015544a089480904805150030740000e44411490f880640540d03070101c0c045007514010404030306070100c010300c0c1100b0043c0c1d41000f030385000d0717090286900076802c0c031165602405080c002d0390352401407900600cc16560740001101e889041042003800592103140008154070f6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 619504460 1250 619503210 619503221
    0x30213090804090e0c03030304050a0314040902030f220803150105040f0807090b010f020a0b27010b0301180c21081c0c020609070501050d0b03010501150801060e0901050603040f06 79
    0x2075100c010400000c2403039218107008100c4445d5000350010810440000e4011480314006903050900d0101d40340301c00c0085032103000325000301d224036200100f444204041c800d0342502c650300980d4034550709100d02180503000c0180b00300080031001d060021a2924500c4110407980900c1803410b02e051944c0c47c0d89410a101e00f036402242c85030130614040c401851a03000b000e148201c00e00344911652840c1d00029510018140050310342801440400d50648254118201105548074900703031031100062410b00800503581c4d1213101390310348600050304035200c40e061401d140d085031903e413280e072410303811843d03400d104c804c1143c0030302c0304000e140001a403010203007100c02c00f4103014080c201403050300c18084410000200c1c0a43d07010303204006038040006901c03c1981c00a2826a4662100e8070b0f070350000c0c00d0b1001035180e2550a01d400441ca204020751524110036035035840e00c510740d90760301003a40d0703900c0010022600810104018040d509159005540080c854908042030040c151208404c451 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 619505710 1250 619504460 619504469
    0xf090d0611040f0b070b040204021e0d0b012606060c07080d030b01110106031e020a08060103080715020a1b11030706050d0b1518030f0303010b0d1b09030213090804 72
    0x49420b01020f941c0a40b0000500303450307100304c0d207804081d8941d1512600c000300028425030b000154100c5800501001a10040c01280c010341c9031500d400c10000546100307017180e8001000c0d21942c2c45000e414a8490800741c0c402d42c0c01440d81d484290a00c5499407040340301c42c3d00d0344240500003401c100104003458142c2900d540015000c442c0134001009400c4406034900351760704004041c400300320a003007140c00c0749040c03080d090403080d058408100601c10b154048036160040c1c0000100b80300c0e0640092407030500c0b6020b007078043c007502240e9200302e018014103000020045508000d200b00410b403401038603806107411b02d01030100b90000902d040b041e500698000703030b004944a142c0707000c0d46c064016484001c4691410350b50080000750981e002c1c4400442559a0072003a10140c0d03103040c8803083d1800e2110302643d54170f68440c082e420f420b40c00212181f590743d00d0301103444000c404c2e0038403402e40006255510069030b0318540070481001660704c1c805060590700e645580004404030003c10041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 619506960 1250 619505710 619505741
    0x50402150f0405040b19090c1b0b010e130317180d02070512071d130209010e070f0f052b020a0905041109060d022b0b0306090f030f090d06 61
    0x200e0604082c842a50324a065086c0580c0d00010f56510852950b0100c405030317860540002546406c07201c04952190f0783d14800c3d024a19114a10010b0050304400507043c1d41d4040a03c544948484408684001c074680001d4005038070140416070031020f060800c4c0e00620498040701e11503007003190044c10403100d80680c2c40943d10482e000c02080c141aa00030280080e00e001074411780346000c00e445650085c031091015030041100000e02440c840240c3c814440360041d00d0601d040d82c42d00c8515401d41015201078000c94182503901c000c5c144110741902c0380d2021a61840c3c140150150050b40d102481c50b10000c0d540501414250034441d180302502141e101c6650701c3d4142881c00c824402220890548100207840800900319a03448510071514203240740c1380c0c0146c0d142c5041201c1c120210a08010241049424564800e614600d82202c40c14003411015515070f0345a440b496607a270582c100c82c50007a500140462900500380201400750749901800600c1d244110381c2e03680d01190700120b9031070b0380d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 619508210 1250 619506960 619506967
    0x60204120212010c020309150d02030f0708060d0c030b040609051b09090613021908010c1e020c090a020d0b0a17060106050a050f03060d0b0a0b15031306050402150f 72
    0xd42c50641c2001e61050400c40c000c00458558443c029100e1041e50807040c0075080440b0711560304c019000c203d4514480d810300031900c0c1c3c1000840b8113043c280c02e070303000b000103034454000c51000c2c502000c0320a0006e034003411031130500340b450b40c40d189122001807042c1d40d07440d540e03030800000c50028426000c134820440c8440300b170801e000040003441100036100004552141b0100107802800d850300308500c0e50101d80c0640c074070300f038020411118051900400d000f9428800c08504a075004601702101d50700d01302840200010303d2800302e9460a1460318158480c02c02408103c500c0c0c1c2d640c0c02040183c01c1d41c440408d0020760038020455462807644a0b95030700c510006d03112408141070040502501d12460602c2c41d110110400074094002d4002d407841141e00000445c0303881c0c1d54018060300741c2d0b6005400b0505071401030790b031500908012114074000c2c1003009803c50000307502d5003102d04c1039a80003440640d40009441c3c0b00000d120092089810142c260703407007900302289030003800074510718020a036035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 619509460 1250 619508210 619508213
    0xe070e0a0923090c130902281a0d0c05030403080402060c0c0d08030f01080a030503071d1c020406050a050d120e0603150103140601120c020c0d0c050f1507030309080706020412 77
    0x21700c42c1c1d0000b026034a5450b0036010401aa41d0502400d100c9511521001c3c0901d1207203c24210201290301410340c9004006090949070b840c100506042c128000c41081420032408081c1c83c0361104460080000300c401d80054010325002d00608007914155084500543d0a6004a00707441c5012100760350703203c408020401c002d01c4000c007031400f400080000c1c1c17070f0200061360007418502000c1c05400030310181e400b200c01c501d00c2804825010303c10040c403501039080c41d18100994100cce0582c050780143e0038131401080342e050455400303040701d10140c031804002401d600c0354101c030511419101c0801c40c070741101030725507915038000d140100c10310354a0b440ca8184440016040300d039000240c00741e5014180403c045a80c20802c0745046c1140705101041402a00c08224189406241c81c950701110300c071302d0441400710a02c41c031419500107607510b08810585004110200c1c4180039603c0940e41e080001a001a209401020a480c4290b51160a05d110341c0d48200580e08190001ca01c3d50702a81200310 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 619510710 1250 619509460 619509469
    0xf0703030c0b010b0a050f030408160803060306070206010501020d120e1501290d0b0118060903030801090509072c01171005070504050f06070b09070e070e0a0923090c 73
    0xd0041c40c94039025480d29102020240c294010a5500c140e0410040001403c0c048400c00f120b81c5013100ae402c00045003060300ccc054034150011740c1d11074060b10800d800105018000109181a01d01c160010124002c10082c2114000010091111266107c84603015a4441000f00401d11241e1110b20243e82d81000d6040d4112010324079464032500310041910720404c0c45008590404a40003008507082031440f00581c1c80e00700040c002e40b4410920305000403c5580112220240e901ca60b0390440d05907694501041030b58801d90b02c0c0159500708541c02c000249900c10700c03100300420105445403290080c641203040d007030241d1000c1424000450300b10301981d820f1103001281c440954041000d418401002486070050b8000c142c0a81104880b4801da0ba80c0d0b14142e0b905603074000c0390507a85241c8405003540303400c110b1054207000d041400215624500810341c01000b00c1028000104081c0b40c007400382c000d0200810f420744807110411a40070113000690105219441043c02414103000300c10912 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 619511960 1250 619510710 619510733
    0x20d03052e170d021002070f080904180501020d0b0a03050706052109010f050703090f021302040b071209060519030218030d0c05071706040b06010e0303070605060a051210050403020f0703030c 84
    0x1500b9104102210010b095008d01c4085103421410f110b48a01c4400c012800170319105101500b51181c5000d05010024150000c05150300000001c0c02407441e64003d00c103030360354103000040c070a41001905000c03552046000d44980c0240b01034050382c4800c030240360100c5401c25100c40c001e0365140e1394540c0c000225400f609402000d03a00d4100031040041e10b8598008503440300007846942e4a100081520440d0b4050301c024010162100ea40c1e20f00a00c0e101e068801602c480201203040791030005400c0703005006965142c40d52401000b83c4248010b0700328000c0d400100d6400c001c810344455004591010080c00f12081b004c1c0d29001040221414018a00101a030102400c02002c182a6072010000305030340c0c2e00706902c1054190f0603100c00780140c1348940481c0c0c9050f05413002140748000e005007a00818040c000a54030200101d403502700740b040300945400032517069072110400800b440310661005a1183c0240306840013001d98200c03840c1003c201d94000d0f0001981e480380e0704103201421046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 619513210 1250 619511960 619511983
    0x1a090702030304060c090b090f030336030c0108040803102c01090608210915030109180c030318050915120102130509040606080607030c020d03052e170d02 68
    0x6c6d01903d0300d4103c9090180c8140c03552180500c1000086003110784041060b10085540e00480401107002c0404d4403402200c4480d80c6540454440c0810907030b4103002c14100c60f905c0040c3d44054650780c8503280c444e1141c1c001b409503c48104442d000060020a044c04106039100c0120700c1700d068424201484841c90341a0400c4840300d2500c007003000f00c0c00001404c1810b0482e180201880c0000d0072108000a0060080068100404020307100e0000480001907040c0c0310b04640c2040555038114143c542200004e2000300646c9a410040c80840c1c002d07a030102c08081c0d0300c0c6d0500201c586940114045186c183c800b00303d141e0f14000900742030f03d0003020b181001c40419008500f80742042c2a8902c07403c805108550280e00d07036a0110741800003a8108202404022084400034108010000c0c002c284458020005010b070104d1075885c28820301407a03009584060b1041259294004418040080c07030000c8492120000c50014078840d500c0a80110215180041e00c045102d006006c0d0a10044112 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 619514460 1250 619513210 619513217
    0xc13031a150a050d0501060e01030f0c060504120807051c0302090103060803030f0a0b0114070f060f09020f010e01111903081e1b1209070311040c0e041a090702030304060c 75
    0xc0ca00c29688030310b1805803c9400459007005101511709103207004002d590480c0101c40794040000c801d000c0d9844544000c18825984205400e40d6420115040e008034050240070782207201050340460603110180810a01440645d500144404c008014841c0d40f06030200c003290f00810a01c040750380501c40d0100409003076002c1c0d0b1451600a101700c99860000b444850342c40d50311071900e24641d00c1a40d1b100440d01e100c0340520b54074001c41c00d14545440300400100c620034103000c0d0010750030015000e25110320380d000d0103094031005a400150b500c500507010f44c504105044144c1c58440c00c0070801195840503020070102d201207641070040c12504000c01d0041c10b000a81f02c24052040c2465080f60701555503500d030700302186080300021300e622076030300380e40e02d0790752410140707ca0320101150440459109001203840343c0251030034030055500e00d04140300800c03044101959182026080410051600300341c1c410608100c1300080d000850507690400164800300c100810031640e8401c68003607000d6800e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 619515710 1250 619514460 619514491
    0x9030a03210c140a020c030a0308160c031b03440903041401020a0803070f09090e0a020f0a03080a050c0c0409020d0221030a020f01110a170c13031a 65
    0x40070b0030306140c00780e8003c0200c800045040c00d0a10a00c240701140078000c05072010040340d801c00410f40c0c40107841e00b462640c0a240f26500071809242c41d810740603415110f40315861004400080d8144801d40c06809110381c804121000310707151790941c2108411801c2c04100d0b0203002e903107801000301d28134402152a401106200c5101c03000030540d0308480707450301c00002c641c42c01d43c0100d041c9003148400400c290008018040829048a80400721480542c3c0c0c00701000d94854099041d00c0555903050b85030740103800a035001d814052581e01800202500300d140e1030350742c1e0b0703140f41c1942d02c500b840344002000401c03030140018050051b01803030b8034100d501f4004149a0780008142c240c0d4880000d114107007011520403a0b40d4641e0b540300d00d0516002c10313240c03076001e6610301a4891130b8040003401c0702c3d441d04940030301a48001d411760301c0c40201680d4019407940d00c501940e00d29480a084150f0701d020902a140c1100041c01030130015501c80c00412a046882a81070f040078a800b0705070a604c809a103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 619516960 1250 619515710 619515731
    0x30213051f110111040509090a0b041a090c0a090b040e0709020304120c05030a051602030709061511030301051011060702010f050a090b071d0d0b06030601082a0609030a0321 76
    0x364152020703103408543d501480c1d10f501035014605442705e50010041c048a0082000f48508260f81c4407066018007202c40040c0d80e5002c410b40ca402105490580c400400308003405104041d900c9988141d01c06040056910200204075113071482039400702c3e070705035000800c00081005151080a01c0d80031030400b10344501c20347c2d5680d900c0c1d0013143ea05104104020030340040c84d44884941e980c06540180a84800300c0d200c0c22841e0251441e03015044a50b19280780f007040062140000486203d008006181140d00300750812450f050034410010412100c0c10100d110041c05220032401030005030000120100c4410440d001d4400080c850786c8050700d021070140110b13084170701560380000989461540310203050120328005110b0301d012034203d20002055010000d68070020780c0910402c90450b005680d941005550381c096035000c40c20303c00c24800e9444450580c0001c40400303240010161810034511801007071401c901901e00390002803030301c40b44842c03000328007600c22149440000c0a0003901b110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 619518210 1250 619516960 619516991
    0x141006030b031614151b06060607020a030f03090515041a090d0f081902010b18070f0806030a1709040605031b0f1309050a060612030f030213051f1101 66
    0x548195556141013455a201c0d41d40d41c1c4000001d020b1808208030340b600b4020101c07404c008110b49807030768188101400702d00d41d450800151440f041e030051400c3e10b0141180d903041e241e401c02d40030450510000580c0410b1070b40d184940612600c0c3e15000a903200c0e0700d840315260266442d0754814408520070858a81113440d0540c05081c41c40d08002440342c10303134081c500303411030f88120100505e0f5469010004444c5030744c1900b0902da1703440700f03c2d812030340a890a036012510200030742d5030801103003000c1110368540d401609059800500181698620001600d070340e0040080c15000c001c8100c00041c22803010314180c803e442c0508020b400a04101c80401c08158408a407045018840c800d6120911007640d81c903038104100041002050189548a1130034950341c20034290102d0b03005081c4080420081c0c20145110089a050b42d01c4059101c154001607000354410352501320f01d1030410402044513121142800725004500c3c1110a51055480e03006144205040340e43c4040d13410309a040225601 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 619519460 1250 619518210 619518253
    0xb0a060c0605060d170a141305101103074b2a03020901090504050304030206090d0506100612020f04170a170306090606190f03141006030b03 62
    0x140000e0000c2c40d503d600c400100d0f85802e10030020700d0104032100e0444101d54203005400010010384422910140102c031504907401150f00f01303a042c00c0c0c090010403a07403401030101c080200380ea0038845403442d04180d480f0308543c401d80341907a0b84000c03500604159000300071a11070030f9610b40740c1800c49080d13001501030b040d10032081840002080e0100f000601c5030b034011765842001c0d101c10070341c5041c0110340c00c846040f001c1c0c0b200340c0c40341e0364040001404007514002caa1145901c1400786203400c4c155401c02050f0b0b040495401e410074407002c605d0000a904001407401444e1850000c108a4a408001005010303003001e03a0400318010712101481c0100c100580341610709141030381040c015401e1a2506d0800340c90009480058850b0340302100c050110001e5000300c0003502d42c9400b0b07640d420144135041c0304214031441401c0da082c1081300700e01e1140a058040d80d42510b4089030707500924108d41c0901c0420340320120050500c42040060941520441041000c168090840c0f90031225032544000c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 619520710 1250 619519460 619519463
    0x503030310060e19080705090c1305010503041707110405150307140415090902100306210503090d0305031501180e0415020c01020d15050d0206090409240b0a060c 71
    0x1980d41000c000c695550341d50104113880c000442010141d07500b4090340d950060344200388c000c02c1c803400841d0f48a01070318122101d807100740414220543c9000011200e680c00103105076107030a00d90724500040300540c001011098000c02c104100b259500c41000211107020b03044481c0d2058000c0349651640f804030f2643c0441b000c0001d0306000340f4804000c40c000d860781240f8900c041e0903030580455204016800711441c030b80280c03040b1040d13500d02c2c0da003030f01110300902418042d0a01c040e90102d10061681c0303030000b010300c10300580b03080c01400e4012070a1210b9504c0f00301d02052011003002515808682c0b034401812091801d038050058460041000007000c1c00b841a203124404001401e20500c0c0310020001401040d0071592484900200c3e8001d40021003e00d00e441d06003a0004d03001c031a055403441c03d0303500080c403c3c88401b8003a4200452540300081158200d6261301c5101c1c041190003580804403450607200c125001d05010913081128001e02c0c0b45d621400750381206000e000c1d802243c0700c129a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 619521960 1250 619520710 619520717
    0x30509070e190e0c040213080606010f0503150a08060a2003040b01030308040c050d08360f040e060c0705070f1a1b070801021305061c051308040915050303031006 71
    0x10283ca2009003001448000c20350031a0002541c2c246050b81c4400b004111401c0a040da8460384806004480100c02c4404100004400740049403004010000124a041004008200315541d034000c02d402c01070200c503105840c580d01e529030b0001c0c01c41c0060884110710701d0418103240d85044e5a84500140c41800301030200080c10002404000300c0c030043d14003501c80100241400070f89460506110390010325a9010041c041d10824207034001840740310031034003004000e903003400f00030014800040c0044021660154580c107100803800b40a2180d40e00034030b120301046035104814107142e4139040036640580000b500c0f04c58200507412000743d00c504030100da80c0d0311542d40d0f0700c04103000708400021103584101340030307448000550324030550003803a40071460544005420307038030401c01c05070340110111400034a207881520800c00c03040d85e10581c1e00c4400280000c190341042d403a0f0361104d400279005000d03002d6036280104c510051072446000140401c40045180d031030715521079140e0103007910480061 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 619523210 1250 619521960 619521971
    0x2060901110f121308120414010c02151009021801020d0f0203040b16050f0a02041805031207020106121b0e04030e040c1412010e06090c03150a1203030509070e19 71
    0x6604000c0c10415040c0c101417000d490345030039018044500001e40d4101c664202c0c07007403400b4a1542c1805000c0844045401428044010f404541002540100300c00454005e045001c11000381c00e2000c1e003825034020b2a200c03501d85103a0006442d02d4070030070940c1c0900049184040030140e0000403a000d54681c00011501d816110440c012400542d4000619501450140c0d04290000040030402d541c0226400d00c481d400b441102c204902c12004081c18a4204025262150118580003a008540c3e4400000c0640d45d9800101a41411210480740041187c680283d00b0300320205600240c5900100c0e5802414107680190282d2030061301c060042d601c0d601c520a0440c080e030808882c1f40c0806480a64030071003a608d12288100901a03103e5038200c41c03012945d01d003008090039105150001c107051464482d1441d081c4c40300d40740301905500c010814808184844004a04035180707101b5100840c581c01e164007218103082c559007003201c021a45004000c00711100701c504d1120440004400a07a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 619524460 1250 619523210 619523221
    0x9100e011509050607060906240e0c04080616020f0d0e011d04020a0c020406120803072327030c03030a050d11070b041e03080a05150a0602060901110f12 67
    0xb84195150300c42640704d04c02190080a104958200ca8603d92080c9010490700030289071401c034880094841402d4003800780f47c14401511607009482c1c000310003811060925664420851600e07100300c0714680c044102c81e064007440d40d0100004000e42c000030015020b82210702d00d00a00503903e9074100e60400c051802d140c4034507024009158401900540290354805041c0b0024100f020310100481c0624507003107000178440e40e503044680c4540c0c1c0c003e03c241d1554481c001c003114a900d803c00ca45ca414440c1c40b45e0302241c2c1c0000402000700080d1205048030095450032480d103001c2c0d1001c40719009800c08420013106c0c0d07801108403039021405003040e90321520540c0203100185007400c1045061180040c1003400d1154440c4020300c594410201d00c0016a4580b1141c8204803030094018007044a620204080c4040c6803c00c5500503508103c0c07800340b03450480003072080b00040e400000981c202c0010300c0b000c2e070021302075070034040c2603698030618241c41e118000200384178880504c2403101c18100800c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 619525710 1250 619524460 619524467
    0x61608040204020d0f051008010203040c090209062514011b0f020c0307080c0901150504030f06180c06182702040503030d0c1818050c0c0d020c09100e0115 68
    0x15a0403144e00c0b01002003003000d03a25a0010b00c0207480c150440380b0b100c2d00014001105000b102c3c440c42d07000e001031440c546805040c070065002046011f0b4411003c1c01546207a03a815500100700c100c00b40c42c0c144400c025400c0888181700c4003004154640d0601420444031852035002c0c007a00034040c540410f0b010502c15089080c50307040c2010035414003c1682c0040c0400c80090885042c5104039280d44499a0307070050080d11590780a40304003c188240010008034540010260702c26002d40d102150140c10340d42170f080030001050040b100d80d240352030103029565004400c504e490104140041c0c0341c1c0d00b03000da121116050503404480310304144120765000c0406805540c01810090200d030703100d41d19044044043c12090701c40a000030366140400c10b0040c080d0082c01c1c101c44103003084880403846c00c1c000c1c2014140040018400b4542000028881b040821203440038920700d41c0900b03000c09084c1e0070022210380240072801c110404100a1050020040e04541101c200414001402101c40000ea = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 619526960 1250 619525710 619525717
    0x10605090d02012c03160807030f0501110a05190504121119080d021204031e11091509010801090218090c04110d0b0307060e1020010e060906160804020402 68
    0x1150b101c0c09080004c07601c08284058960440411010748070690010345009541881501c07403624550700c107040c01c01c0440c003804805444903000d00d00201e0101403041c2c81403903940c44000300c1c01c001400004c503d440c03040c0c01c1d451485c0071030840ca820741c0703007500d041b0711001a40d0554070042d2400840034410700503940c07081d03060460031001c118056801076480402d1b0b52210810301402d000741c040e000c482044072441200b110181ca03804082d4212084050705030389156400000229100203c034140c0102543d150007240f40710f4410b83c181000c00d000f0103420700410070340603485595242c3c100040c0f1320069944c00c80c070240d94464000c4d038403240d544043c03482d4a8400f00300b0310960028500342d050200c030400b03100180b02c050071041090211000c41070a041c1da9a01382c7c8078440000f0004282c5004a140c141601116010140382c18028000541d80055024800e0802e10300280c3d51a09900d103240b2050000550104121010701400c0c0307000a03110f0f04215140c40702800b0040d1820000b030441d40c1c2c03503045c0d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 619528210 1250 619526960 619526987
    0xe0d11010e061e03070230250c09180c0b09011713021008040c140307090615021630080703030626030d021809040f0c05040203010605090d0201 63
    0x101c0da0f0501040c050521203500030740d218801030281038092003041c00c200d1415007001070b12001d01106815001c0c90550036421901800000640d0000591000503210002410181c0070740c141c2c4980e6440d00d41c0040885000e0840b100c1201070180030700000c00c2d078080140c000c541400168565030b101410049034601c07558482001c4621401007802070400410124880e11882550800e209402c0c5030020388901d0001c8170010410f810500c024000e600d241024003220010150881e030401e0340380d000240039a1040d4105000030f02c007035241d52001c10350400c801d042d43c0d1000e8a02e01c100c0d17070500808000b00d040740c8418034a85040381c04911942c261103503a88000c140c001307240c80c0c2c07541c17102e01d801006000d49203d003500040d604000c3d07606c0c1c15180c010070311561b4001c90096241100d41086040030350003180a05404400c5a9401c1540341c03070301d4084a12442c45a004480407400b1440d100303903040e0f400c1d0032142c0180d2042c0014404941c1003c11513160b02800c60b0561062104c0744012079076902d19485 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 619529460 1250 619528210 619528237
    0x8040215040e10080709140a09020a05221401050a0909170c1609020310030f05030c030a0f031b0f030504060902151803060603071a040e0f04030e0d11010e06 69
    0x100514a4a0758030b0000a07510090145c0f80d0807070341d0700c4098055800d5440c450307440031b11400c0414900d01d811760100030428406410212065980e0000840514000d41d0301d01c1894884000c8030385070480c504c00c040c140f45032248401e18950420300484c115800c81e0203050500c2e652207413160140a103d42c0302c0d5002d5000f460000d41c0d030700f0030031040eaa12860604136080392440490f1000c100102c0310300030349100759080c0300c007056a90728588410401203020003090700e060000704910039024000b032000741300c4e100841c2c407101000d4031416401411514014000281c2c000fa00d2003006105601140c5030100721030929000c0f076581c03a01e0402c100200842c4800942c841d404804080b06100c0103c0501030000d0040701c506410441c1c80145616040121003042d0705401607001440249800302000c45008000d02107541025100c07001140c141e201542c0c2e400740c0da40514200810140c0c0505400441201503070710b440040480e5441904651b0300b4410b5505000341503942c2c001719107401c010340e13054150808 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 619530710 1250 619529460 619529489
    0x106200115150e0f130b04020a021e07030308280903120f06240c1b03112e03020904051003030305060603160f030b180a060807060804021504 62
    0x501c2800600c511030304480240004605200038054074010860280161034281c0586445040109584180c0f80c2c094485a03500081c2030b030f54841e03101904104017181c0003000c2480f8281c12070504008089c03070328266503000702e60910000394042e1009800c51402c000010030a90302022441851643c04e900301c404600d0031410070300f4158041d03034502d0000c0e03410000308455161130b400346040d11011700600382648800805581c484064064038036000c7c0c9a883c120354000c21958804003140260400d000c035a1101d45014070070b0001d200c004000720b00040702c2940403000d007120040c02e41402000a241203003100c2410b00600c90003134049812806000b04104801e18051a122602d00c52500040d40040d24001c0000c6950500301c045a004804941600248061018080b6111040d5610850406498140010407502c411200d20720301c5c00042541c04c4d09203445e4140000b1100144d004032080d5000c1d48041102c69000103041350000e40555900c84407078030500d94561544519031103200510100c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 619531960 1250 619530710 619530731
    0x90103140403081b040807150c0213050405101e110d020c1b030102070302070b0f090a0920031308161205040306150e0609100803030a020c0610060801062001 69
    0x2000c81d0307120300380b1000001d005110800e00482d040c0128040c0e280d0310783c0511f0f02807010104000842c00c40c1d10705490103031050015640464514030444081e0611b0755185d509000c10040103020340907000c5250102042550300c0014079880024001c1d5440c40e11a0362540ca13403200170701503070484600600900d015943c0303403825207d0303965039120030b00c0700b95016030101c0b0410340354030b01070003150740310b07a056030007041100d003005202c20442c0d101d6011070b41c10032010441d4111944a0803440002803042030700015080e00002c821003e0242c21980030071000208000b00030741c206c4119140b8654513001031800d0345500031480c0c00b4040b101104030140c05e00800303007013032403100b60b0010003001a01e10404090200390705c0342e819049115028004c1c0300303950510600013081ca040100307815030b10440515920064a545902e2207096a0082e50f0011086030000b82910442d5410040d09421162110032281100c0c90031000501024042c0a20800c100078007500125209001701050b8064441e80f00800c00c50002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 619533210 1250 619531960 619531967
    0x170f0a020f04023402010809060705071e120309051618110919052d090402010302070209010305031b0312181c080402040c17070f030207060204090605090612030708090103140403 78
    0x3440005ca00140341d04d000034140c00c9010803030a01914036525041e041452035540e0303803101980b00608a20130620300c9010b60108034801c10034407801d010b03500c002031021a00d06040d818224404100782002d201c007201000703c080103200012002848140004400c0c40642c1c1d500418406d40d038840d640454601d0a6400700e01755541c4510880f8000c5546030a00c2d102410050b0000b5030b6603401e40044011401c4095443c01d00c00001a1312610500d00145003006070f038001a13407400d0a0708195940e9002041c0d113000d5000058080d002030303151100a6081625041e802508144010040c04c606210074521010083c402c00808a401c40a803142d450a040300e000010501c0c0c1049600307a10440c1080380240c0d06030f000e038100c5030b040c8814401c5520f040c0d403240429140d201240c070082040560811024003c00c0c024030250001e40310806000c900149850100078141e0700240800f0300c0781c4042c0b0400b403415007001040f502183d034000300660316002500c0060700102800c84202440c44020340c200000c0690 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 619534460 1250 619533210 619533307
    0x130c031e0b120f07030201080415020a031b05040503100b150408010203340e150d1b020607210b040603050c0102160b0a05070c05030304170f0a020f0402 67
    0xc042c1c640480c0054108681d503030b02c94003060b52524641020005002651242055903881400381d415009030031445d008480c01ca81c429400440020b68400d140011b070800d8040c164481640c03407a080f410603090000098075554001040710303a2990342c103070065040c4c03240c0804e0301d0607003941c280d01906d0750350340c02085010b0b500881d09840900c050016402034250018000000511110072100011903886419200e07203052144050340591504004000b10b140c0e0030040c04001c01c242000706002c0500040350440303000b80c018030015500004108843d282e403220880741040910780590601507083c0d2070b10002003011000c55074100741412004424043d001620b00b0b142d44084c0c0c21942c207481400d046000e011414007072014604406c100c403900d09407040002c0c003585402120001c606542e43c01c0041c0c50f580c40f0368092011081d1000c042d105c0c1200c02d0010408445402c1e0150486020170b60000740480681205103200307030350224585201c0302d00040c101d504081c003001e0900d20014000080040e808 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 619535710 1250 619534460 619534481
    0xf03070308041119050f0f090a0903020f030a1403070e04060608040b090c010503060d030315080c0a080303010608061c0515061507020607030318240c030b130c031e 72
    0x48003050b00d03241130828002d16101012010240e040550500c4204081442e200405c241c0c8080d88559150495840e01035050040034121800a030040382d40c90003a0a221206281d4642c03608103102c022242a0000200311601c0c42d640d150300d030b40760f840300320030780340c000c100c0060301d030410710300319020518a4010f107045000b14007840c0188125500c1c0c507202551400c0c0d890301e01c1d00080092002c03440030304100c0c61648000d44281400724000046030304042c00c5a141d64804203541d8007003024804c00b818100201005481e400020318a1503042180103440100054080707402501c6085041c0750b5005071440e4031b00e07040c0e80034091350358420070703107a946101500594041c1e00c10032841c0240140c0030000b074222174002d5030103002d050070304645072402e8005100500041701141c1c8049545030019020a40c01603115028080c00b52443d813900355079004440c0d1685418041c185041240b403802d964640e4210078100e031203840415410411030301103018001810340d100001d0b40298600b0022041c90b007046200d003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 619536960 1250 619535710 619535723
    0x308030c04051318080f040905101e0f14060c010e16050a060210110702060703020f07060309050307020d050115090603150b1f031803080f0108030a0914030f0307030804 74
    0x180c0092062022038013040c0307610300c400d4211021800090361240c05000036039062100141000c1d6900b0318007003640e10440d010700d00800f9459003401002d0107005a50b800f000481804030045040c00018502c2001354052461030b031030080103001e100e980b2803017161281c150040080c0240400c812011755603e000780740e280d1301080960404a80c1d402d1a5144404540051f0300510030840500c11b020024006174506000c92402000400e0144c1c461000800c00c40c0e01ca540204189151a0040350500316550000f8003011b0a007003a12002c100e00109840c400d42d01104c9015424045143c16401000b4074410b40940c1c040c911400140794115600c124100e80c022049540c1503030702d02a0640031214407514090740150010340e5160103003010080084c01d00c016040020700c1c0e9101240c003000080da035000440004503200d0411025200d071100385401017543c400118100882004050540000d500500f9011404040d4545c00c5503402c0020a180e0f516034029a0790751550b03420000e10801d8115030541d1355 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 619538210 1250 619536960 619536979
    0x1e030f0e19210501020703020703140c060403110301060e070513090e03030403050714010501170d0305070806010c030c02091f14010e0405041a0a0b01031107020a1e0308030c0405 78
    0xd410240454070008042501407501d080c2001c414100c04219048200c021000164200340060b60034401407070100d000e50024894140385103449940b40300480c0209080b90801c803c07031071031078480d0030544040d25404080501a6028080400d004140c10b43c891321041e501c100034440c40540110082104024800205080c00e0f110701715507055810410100403d503000b000000c011a11490161803818030806100c8581100c51002c0740c00d6131020b8101009011095007050a40c0008100707103265100d660602307111a1820080191164030300600700c5050001c08406407041520404005070f440c0d80c0100300d400300c0d08003180c030964141342c603640c2180c0d545803081010030459a1940d1504816005a50741d5000c2403010040c440a488080c100b15031654280701c5481d09840c1001d0428825501c4e8480003401d44c2d07041000500352030309204030381c9440608219000c0580c03110711407241a18500c4030400e4031841e03c081104640d03800ca0384040c0c28800007009218000c07000d00c0040080f03404c1140e2071403a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 619539460 1250 619538210 619538237
    0x1a1f030f090b16020f060106080115020c030a0303050901110c0a03020705120a0f060b060d0905120a170c210735100906030821040203070e041e030f 65
    0x201d0310601c80c040c0c80614241d0000307004411019440d6804180307481502c00c025004440035107000400e812940100b20070740010301000184051126264540d440144690603482c00400c2d191441664080c0c101034480c0300055940d00c0942000b005a481ca0360310540c0e5030b070022076417900c410b9511400c4005000324200001c1c245003804901c1c00c40c1400038040d1a03140c16558a00241c4070121400319006911a0308000c01035072000050301c0f0710600c1d200041740c0c0c0105890810f051038403003520b8801d0040b0601140364505e500c250b40006111001c000301c034550311000901c0300300b800b03032011520700d07400a20b415048080e40c0044c038a0080c1d0b065120051444003a40d491250703040c003291203241c0010700500c140b0902c0100111103800a00b1034500c040c07410f45a204a0054501a80042d100e020b000980d5408146030401405420300c101003074100c8a00741341c0e001980351803035485052100d0026901040600c00d46900111410103900c03801e48241019145c05070100c029034814001180385940310344e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 619540710 1250 619539460 619539491
    0xf0e0f100f09030503180a0209070c0303060e09030a03020c0c22060e011a16050d02150a0b280b16020306071e1115010807050a09020f0a031a1f03 64
    0x48007643e044d1107050540d0340b10403090011400b029000a10791088210b903401684465686500074851136841100f51450340c18042c05880ca07680c89940030025950070400007031301c00f100ba920701c110907184c0903030340f480722504051502d8032800b000745e03120f440d001805801400b419024044e45c5842e044c00c1c04010780d641403041850300c5c2441050210389403070101806080b820001000080c06500c403a00b1039080c00d0702c41c44d1412000c0440140076a104462488c40d0b0b107403d00040742c7c00a0f071004140441d118450201d40788040030076000c8200100044869007081c0c81415140c00f82c0720031074445032503050494642c0a4900b03141801d1703000780034000100c2c0c030161050035043c07405a1b100324507443c40e5890190840c4c050003040d40c180b86178015900240c40c0d14105100c03590017461000000c0521038100b508020100b903280c0d10607005184100300d20300c020541401940e40890b0b20f82000500d1180c801c0d000c249082c403001c440340e882079098400f006c43e62900425103d503040d0307607513041003025403032214403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 619541960 1250 619540710 619540721
    0xe061201061a0702060d14270a0206280905101d06030c0403060f060305192001091706103011030a050a12051c0f0e0f100f 54
    0x9030003003803105504041005002004000c210f2004d02814600843c0940d050b0840d5000340008840b0b0a0610a1294581060091000d40102c52023202e0000d03042007155696280824002801400b0100300108006980710301c01d828100ca11080c0100d030200104c00400010482c0610342c41080c020440340080b030b00c075101c3c507607560352400100c0d103008203040c042040b2500000c00c0c0034280482044080002540b038020810701342000480030405905501d40700d828510b02403000d000408004400d1800701d801254460340410780100300d40d40700b00000e00103c4100c56660084242c605100b164030008210016610b0700c220829508070040c40d490300f05070700302c0722802d40082d0075400c00e100c0300c8801012032000044265110b002c669a01000d0240820306207000d840d015034003a000800f50034103000d03640d02034141e441021700e41145040707041842042c2c0d0740300c001c40000c04c481d0340d00d0701400743c100c00d075111746501e030300f6102201d40c0210311548042e40c580d032079001b082d0850f040455144002803a4002c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 619543210 1250 619541960 619541969
    0xe012d05100c0c0b04030c0302030f06090303192309280602210f0106030b06030f0a0c021e0d110102041d0a0b0604090b010f090812070c080105010e06120106 69
    0x100d403800d41036890841d81007020290684004054543c00180d9195120040c802035100c0d8510040903491401090300b08451401a05903d8102004021003c0c0c004402c580e070044120b6030601c08a05620002c000521a440700042510b00d00d020010f905503008401d40c0c8508240c00c102c0b28992520321441c0494403046c856094254a038034140000103c59801a113000480c1c6840d03482040da441108410b0007006075010801f943c407880c0140001c950501401010300070585a03035117107040c010300e540305804008140e250043c1e070f9805000030a900c00d0102d900d94000d01403103202c200b40d42040240d02c0d4480c2c0c181d0180803510b0002c13600746414060080d64102c0f07070080d403401c00203070001c008070040d81e00040030400b40c199580607200703980e80d486025101809041000051458584002501c542004d82071402400f0f4410810440700d440020202d040560301500c60384c980c2481e241840b03d01307429420826a41d401c00d00041000790070710180c02c0c840c00c0d04139002e010130400594028201c410038080e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 619544460 1250 619543210 619543219
    0x240501120903030e0715020d02060f13050a02030105071e0905060a080702030409060b07020a051206010510020c040203010801150618061409060315091b090f01020102040e012d05 78
    0x2400d060341480e540701c800400d000c0e040c003249140082c2c0a950500070b81c2e0300143c00011442c00e60004c2550b04000704900841c1500081c1868107003034138900d24010000f4444c195803020032216600704403043c0449107190786e01400900481c14030340c030090b1001c1190304100300c0050000c104881d8980c403860f0b04804840010301101c2c031f81a0f80e84002c4407502ca0082101c803d5110802000500e0025407040c9402880d422052a4913a01c1c3c51040041c40d42a83c2e100c2c41c8144040040c0f9200d05130081038080c1120b90444c0c0f900070100c20040c0070382c10f01c0034000c0c00a0b4418070100001030035141c190010b240706850504010110364503604207541188014581d0b22081d043ca2005015440c05082d0401600085500481c20074004100140c80755000325491880c0c05060140050141050740c5000d420013000421a200d00c01d181e035495020340139401c540e40c0f04141402c001d0b1800d900139411034000d01600b003034821182d82c4440600c000d1a0203c40d8000501580010590070340400890606c1518030080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 619545710 1250 619544460 619544477
    0x8010513110d090f0b04030309120c0203031206130e0610081f05060109090c020102091207210219031410141305070906090606021605030304060c1401090303240501 72
    0x50b004001002e0300c1d40d0032210240c1107440c070804280400d00083c81580300f0744d0003048500c00d92400b07490f0120526002010b1100e105540780050307801000b40c54070282c84062101030b640d03850000407511150049840249868144451340b0700e400420710ba0300c03a650341d155030344619035180c012550302c20404640070000c000d00d503d1842c1c2c031145900440e40040d4140751201a040e00c5050101c120382145600e100582c0d40020b10352000d080c417540401e0401c034548007601c507443c81c05410301c503403044042c03500c0c9201004000c10b030304540e94290110204800c0c41201940e0a40b42d18000c1084241c40d034841d0321521410a00e1848402140902d0740741000c103c81c000308644a41500800103503010404580c1c80c040d029011511a0b000e00c115001883d1501000c0740039441c02c031000e828044070b20202d88203079103d241b0500440d1030000494048031903514002840c95401e09000c0340c000124950306445500780241082415413603040b61005520720f04510084d20b004150132980000c3d6442003a02103082c0301d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 619546960 1250 619545710 619545727
    0x91e0603070c1a060a1503060302040c030207020102010b0117070f020102070f030819020304020303090409151407090501020609120703090803030c09090105030c030714120f0f011118041109030a030801051311 91
    0x410011b05000e29904002c41c0c1691244e0000d400d4a070b880c900400040c0d40810244299a070900803c11074000078207022014074000060580c50307600c0102403130284440750007800d0707000d8801d40c125511745401a60246030310200e460001c5c40c402c0d09032075011540c0070324842000b0640881c42107a026943c001e004518080100d820700000e400484425101039106200c40308102d00c00340101d12400007c01d540e0b1040c1c0c40c0c0b0210107443e80d8215048641158000380420880010014000d1a40000403194940300c00d014036048a01c400c85411100e5580804400c1c404550842800352103c280202d8076500a0b03a00d1b40c1c1815036944075840b8440d4540d000350340800c04804280804c0c00c840754017410000c004c00003510b06902d880480e413460101c5038003400b42c84e1580321087c0b0580c4007540242062514005c1c40300700c488030705050720384202d10946c0e8034150303074078190703040c0040741c100c50b0f809025210824003508015203810f509108580c0113400940c03c0c120503090510916400043c2d105681e81010740c074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 619548210 1250 619546960 619546979
    0x60204320112060518180a02010c0204051b0705060702010c052125020c040c0806032107150b040b03070501050403111314070e090606091e0603070c1a060a 68
    0xc02c100840c2e0325554030f501090341d031a142081d8541204019428500f4100382c444244a2000038081c002607810503001c500060307900030482541c107074040313502040c41d072641940c4d0301c0140c4941c60414124800040e211080000116016101d0f07000c1d03400812544101e1a416510b611a01c910a1060700481c2c3c50000c484101d0312001e6000b0006a9100e13007218450f8601d0115007105420110141c0d010310a0714409140c140030b000300c00105840e290a550400b28080703690baa4032040000d1244c0c1440200c0348003581083d065602d4650000c02c801d002082d600e41d804020f089080b050341c0600d00300170085e1201e00b4000344c09070444a060b902c0303c1c981455512204100d460300341149921417080e02c0101000840c60203104440d40100784c80003103a0034021005044845040c400c0780c0a20b20220401c24103542d030505036000507000f9115844601101c002040d4540c2c0c01307101659018101206000100794072080c8418568464400c0e0342403840040c0d600c1441000c00c8614035400070410b801072014416 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 619549460 1250 619548210 619548227
    0x9031b15030c09090e0307060b04020708091e0307121505010b04140607080c0c0a08070e04150212090c12062205030708120a06060c0515150d0602043201 67
    0x1da180c2034041d191141d2018060b0b443c015844034881c6d0001c0350444c1405801e101e1002c04480840b401c600d0809103965100c0c82e80540c0071211310800400340080354484803000f11713015280000301640e0609031152980103106e080721105842214220f0758205500145100d664142c914540840b81400c0c940b440c2075110101c1000342c0340c0c0000c414080c0e040010103950281c030b54400d84401414020240c4014419100d44c80c0d4030819180d40165000c0081e042c103100000e80092b04010038406800c04104140040c1c490b10361008841e44550040000c40d81c004920042d03200800c49600b0b848074141c0e8036160380c1e45021f031044011103003603000000803420042c60341d9600c54812026a81020041d84691005401c1440715000345020309003009403d0040d4814031000d0802810800c19801d015150641c1d41c955024588a0300d40940000c9412030803561986012060010300c200075030102d03407070808040d4109200b0318215030140100588281022201c000c80d0354012003e1104000040004440809 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 619550710 1250 619549460 619549481
    0xb0a0c0207050411041e0509062b0816031707091a1324030b0603090d08180709090203070503060403050a0f09170f120a0905040902061909031b1503 65
    0x5130400c00001c0c2a1000110f010452106003203c81c8041d141005002c2074600007842e0030700c00d003949400d5000008174007629515011000c3d250700301c0541c1c0303460f1401451059265509201c09100e0300354081540c03005046942d0010b1540080664513402d0065074882c2050042d6440800f145a164a002c91f190024041c10703030280c0190080340e655000480d41d94007009600d603008120440e807082040c1c4d054042d02c400000c003070380c0c0c0910350702e400103080340c45079042820740080190600215080c550348000070942014001c0c00c0d5101596100c0907400100441a403c0f40030f030190400c005524600490700c148500e8240c0c9825103001381100003150048524000a02444800440803c403100701d09001d001090b600b0004000309200020381c0740c50180481003880c801e02e410070031a080c1542c000c04030401c6402c00e42d400304440c851440003464501407400c0440301140d204110000b040c2e032000c10002200c1c042c0e0305522009625294003804c035200c40c022051405420004061400c0c8260b01821444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 619551960 1250 619550710 619550741
    0x705101a0402160813080616140c0c0418110d02010509090a0204091a1e130e01091e1407081b0f181608060a0303030207020a18090b0a0c02070504 64
    0x40030941c0d4002480d008805c0782d0781800c900754410300100340c04000e160341004600003480342000c1e052030001c1c50788040b8243c0305290071020443c80300c0c0010811a610750700200820078002d40c1641c04003035134801ea408100759206d88400b40616281e0420f101d0703c942d00341d0182d6883d407801e1100021302c40400b20240007c82e600341e0070800000d5030000c600c070341107100d130411403840c2045200000300301d0f002c064504000340056408a40f91202d543d441c0026032400c161580200d6002140d243c201d0040507880c40c042c100c0c40301100411407441d026010f2010442c8108100c02d5200c20b07040e83c05940c0c0301d032800f82c03404030742c081388440c41490403c1000e8095441300401107902e02510340702007070312082005840a100c82c01441406101802241070aa40c610145440c01140c60400e00050703102000344009400d00da8000f40c03100c00d5417150103558020380b030030004035508000c1c070810103001030007455410b03203400c1a0074002c9001c084d0755025807410041c0c55401020b550f400d01003044014420b01d2100f5849 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 619553210 1250 619551960 619551997
    0x90109110c060408030406050a05101a0d0f0c020f070806040818101e030c02030d09080f07080d0501050103020403020609101b14190206030a0e010b150705101a0402 72
    0x10790030801c100d9110340d20400350980c90b424680381100075181d0103481000b44505100410404c0810010524100d920707241c60b112070002c46c518090b0151007000e42071460310741481c0c2c0305240c182803600710041d403400d03941c220303004c10010420b100d4440c0014004d03400140c03c901d01140225545001905130041c4888001c0c1c50b000104002071200c070000c1e042040031032060003240c15280c00c20000004001001c1c00d090188050f105030007034072449076403180110342d65244070032001d008a100c05d841141c04403c0c0c0207a0750718954280315029820645050950a04141c00482c01d035100c4c1c000c2c1c40132258060806410034600e032041003140c0070300c1d00c1c4141c1004142c030788890218070010002c40d841c1c0e0089000e40800c4960800742c901b00f0300e035065000c0200701c60084500041e15854112544804c410300d00084414030a4111400341c41000d6015610110140d0542c4172896008028030003a40315404880098515618804c00ea44182800e0031545490350859962030409400400d0a03017a246100810b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 619554460 1250 619553210 619553227
    0x109060503014b05120c13140708010e01080118030309050a0204020406051309273219051b1302030c070b0c09060910050c07150f0e09010911 62
    0x440c40c0122802c162110440c40251030005a0001003202820b42540d0b83d55000420300c5d522541c8680c410b0b403442c05a03040c0101d1400080e00c66118502e00c0c40d080004071403508203040c000f44840d10030f0085079400203c25000050301e40c81407141120f00401e401c41c0b1010400d5a0300c00341c0c003c003008803003a5481e000722480c4c0e83c0103903a86d00c0103201410301c4d070315569101c3c41850981a0f210070030340c000c2c084051820b18040c03264081100d0f0701c5d403d04050508111010640c2c60300d0400600202c00001c4101d00076044603807500703125070720210040c110208903130003e004d05d000000c004c11000300203045600300310800c0f507032a60500041022000b02a10303903240d000c24021100c0403a8000c0792140140c200128411080145601e0007a8203e10780403a211304060004000602c6446408a62442150a40c80c01c0e2601402002170724040030b0082c003540d540d1a55000e0000a0000c05120781002804a281c0c0d0710f0440c1c060703011800171480141c401c280617801c101c0c2400040110b000e100442c00005d101110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 619555710 1250 619554460 619554539
    0xc06020102040f09021c05060a030b041110020606010806090a0e0f0307060b060703050301140d0204090302010e0c0102070e16110f0d030c0306080309010c02060f040e01050a05010906050301 83
    0x104415800140d6891030700744044a14a2030750081c4580d540104070050300c40800ea9500fa1441c83d140d880020755854100006038240340307036400140030b1010082007101740b0032403901c5100d6030001036885410740340c4414070807030311040c0c00c0f50180d011580d107002041180c241117401c00d130300a0803080c00242008501c01d00703c4c60400750b0000b54429900004201c0100716250048e0306901e002903030031500b082c0080d50040c00d58007050185840140400780100d41c0d558412104404054000e0170400640000703050080c080c114003641c140742482000382e4a90a0752000030038204489104802100340c0d00c43d170100005030240c101c0c0d582c040100f16400070100010900203182c0c2040e2020003030958044070f40d005000d488204407410300741807030658108080038011003201c0384a0024641400e1340c1c1154400214540603407421024002400700300480e4000000c12043d0507140308a552030500c507900c000440d9103407418004d5800080052004010300c8030804442c40d02c0700c10b1f00e6180c16111181c0301c403d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 619556960 1250 619555710 619555733
    0x60a0c050c12060103021203041217090d0303140615070b130203070f1805070f05480604050a0b10050402030c090405070f1d06120115170403020712050307 68
    0x802c1c42d00a84010002c61401000060b0022035440c09541030900c0c01c480c5001700300d0b19090162190700412182c0070204800e900300c070f82a000040c0150300c650720a0a0040080203104940134070040d20320301080903031420311080d080c011100c1540034030b000c01940e64903500c0600500f100500333180344095800140da043c4034410162402c2c01d5502141d501d803460184030340400d0000503503541d1415050144840c1d00c4142c4d2000c80000f0b0408540c2d58244810310815065907505801102440102c240b030000b45030b261b207200d051000f00d0380301121031449500380c2d251304040d01e000b0a00c0d4464800c2200040390f0f8024075501004800e2010001d0750360301b0124050b030348211103034041418001100c0e0700d903103440e00c50280c020300e444c507010003c081e06020240405052420110030410b080d030340f001069540d0011110703852070010101c1c0d19940d403400d100d200d140300c282c1c5200104141902c180c592500900c5003601c00ca405078010300d06c03036103440846811070b40c0c005002e0b91140002c2148001141c000d40a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 619558210 1250 619556960 619556989
    0x1d06160215091e090c0f12090f101e1509020309010507092718050a06150b0f0f070809030a0b090c04020711130204030f03030507120506060a0c050c 65
    0x50b40c0c8898220030400280703201241c20550305800640d4940f242c884240c403540c00180d04e46280d9807400e556140e018507001e84040f1608600070076003003001402d80414103594010f8400b01302d03038001c40881c55410546040c0391040d0515503003100172180c074111907004015103c4014140c030418070741b80d0b03111400b40c0c3c1c41140d0004281c3c0d10344040c8503006600c03440140040c049201030000c030b1821800a84142c0d00d8501c608803a0985441c0302d2000c988071426140515503003c2c0840e00d5184103441c0050281050520505054141c004001f800d100307410211401802000c451070300d058192080c449a941041c20240c541d02c4091000c03029940b0200250504540540048079880c600740e01c0c0d503807800c1d0703144e49418002d41c014803e0348001102e206890408040890703040000440c190301880081c0580c3e4009000700a051005005068041e0b100c1405001c00340d0398840950500d840c00e17819100261913003074000c1401c000110104c1d201d50070b201d44542c412000d03184074507190000540c1c8402d41210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 619559460 1250 619558210 619558249
    0x316111207090e061b090d0201030b030d020f0105070903080706020f0d05040501020309100c0905010e1c03210902091f0f08030903010b030606091909051b040c1d061602 74
    0xd00315080c4040080c990301860746081754000c54000c50b0304103118001d40c008940070349001000361046a010b80c02140c111b80000d41102c0761100c104074000c2d03560500c0c01d00808654070b0040400ca615101f241e200c4290303038000d04020314084041c1d0310700000358000e11402d4014501402030304e403007051b180221030081c0e006200161312400d1429500781000b041e400040c0368bc0e8685244000f043c1c0d00806184110f500908160b00200003010100300703c8200101485e141900d85035001c02015001412006100441d010700c04040d610590721404461501402a600007125400584d148440010b20881c50740c2610204100f0746e66024401c5443e8410340008610ba0400b04a51046040900c1a2801c54604a0040515003000c00104101c00d80141c14044221a502d1001c0250006074000344607056000d411501c0f1107000310307140c80e02184503501c3c2078070440c1007440e03890f4410b106029409440001000768441015890104010756000c0d0507400249185006607002695509140c5940c0148504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 619560710 1250 619559460 619559471
    0x16080c0304030c080c0a0f14130507030203041202160b0a2106050f1f030e0f030d0516020a0b0609062d09060603010f0e040f0204090c030b09031611120709 68
    0x1903904d0305100d80190b00c01d001d40c16100003003005144c0351800c082280d02c0690704c0903800c4030080100711050300105a01c006142850305000c0e803254503038002c611641c0a50307881401413441c00d10881e00c4e01c5440700c01d2400140c0701c4030144106050b0900501442c501c1d4209804554101d1411200300d0b202900600505030343c40c10304003d41e0810b039080b80032014003212403c5405c91058180b000036100135000c402016074500c501d90704d00b8401c119003c9502200e200f1030380c8400c1003140c0803014000850701306441900c0c1c04d00c014441800000c2180d410f5a002400706d0b80c5580e44001e00c50150001080154007104a032006c120501c51091040300c0200b036001c072075000800d41c8060041d250000780503140180010801081a807080312521010380362090306000e0a51200d0034207098071041d8034006540180362014034000c11454050160807a031040256a4850360340790207003502c90241d04007280c404d607480016000024540f8210111070080203210400b0114130700340711490450907821010350240c0d40d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 619561960 1250 619560710 619560719
    0x316092601111c0903171906060f0f1d0a06030e060c07020a03030f0309060e0a0203010e030c0d0804061d210f0d020313050f0d2316080c0304030c 64
    0x280108160742c0da9803100c66103040e542248004401c0d408220305010780356100184810948102c1070305a150084980740794260030414a40c000407103040031803400c850720b48100055454010010b00d02c8074940740d210900d007180c410f041a15000e075483c400300d0001200320030104142d96201001805815103030b5002030b01000042d122840c0c243c003e40110401d510600950307005039070b20784003a81030303d1f41468603012255904505a001e0900c901c80140301908040341042888000620125054002c0380280b02200c2c90b8040b094036441505000403803500050200413041d4003c1407400c0d0440d00c6000d0020b007100714618905038008500c01d0300d0f46140c1143c82c01040034440d8190b11611190320600c1245486a510080c0403644121450b41c16040d0300400020050280710340760815407908407040d2503510080e411040d880c4d9035106086400725403a0514400e41c4031110300880d080855208226140404502aa05029101a0044500900030003510200445c00d101a000031480f655a180e01507081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 619563210 1250 619561960 619561963
    0x5100507051b060316020106081c12050f0601050a110604060b030d080705120601030e1606090b0414090402030a050109030f110609070326040e15010207030803160926 73
    0x200d00c81e640d909081c2e10002d07082c681c0c0d29000c50f0303003015000d6490101d00c200d06409902401095202c54224000da031508612a510440c00108a929603a82d0711030100321080c402085520a9510107100d156100c0010b00e42d50181000300003070b44903418011010a42d90040c50f2400e0000c0b80e08a801c0e03611201c66030b00d141003c0204060200503410300c00440e1070700410003821070048468800c4506500030128a850b4003d0740901024880c5805940c90b030700380e18003800740b00c0e201071156a002038100790340001c000c0000801d44041e503401c20300140e1145029801c10805a44c0608280c8c2d03d405000990380c0062003d106840a0394400d4460440b0a8283d00001c2d05114800030386502c207410a00400100305004210070069961000e0b01c802c2540202d40403030310b040302c400c110303801000002a011030101614940c1500c10040355070304400083e26140120380ba900030744401021580e09201140000d075002d0940301511400e4039000540316a0307003190180c0d200351103007540400751881000309501d080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 619564460 1250 619563210 619563223
    0xe03161b05030a030c0201180b030403080702121c0b0402040e090c040c08090a020d24020301030c050d030f051c0207030302091003112205030d120e0a1113060510050705 74
    0x14102c0103442d86921545018000e40315124000b410425401034045840c00c000000c40082c08050742682c2d02c80c64545400342a02d101079a0b200050300c11509455404c07402602120440000400900c010720790000d0036101074102075548651180c5c090202050400b000703401035101b100f4440091101d000d10b03005100c1150010380006c41048440c00400ca0342c840001151400298140c801c034140b02e002d420f003a48446a410249052994600342c40703a6166680d402a6040c3c0380994049402240e592041056032500c070700b0028007045900301142400d501603406403000120a60300080b2810844030350900300d900540c011404070f0350201d1110190b051801e0700c01130402c280d0600b00081c01004124170100d0048070519908400640c2c0b190a541404416000040c20080c049030740700d0804e050098070150035901800f015038a048601d9052907400510814000e82050817040000d14070418000b00c010201d0200c0842034a80c000018192914880310810050310340e6195114030140c40c01c10304186 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 619565710 1250 619564460 619564469
    0x10120b27040c14060f030403140315010801091a013203010e090705010504050d0c0504061214010b0f2e03020301052106060f0312071a010801020c0706030e03161b 71
    0x3c0c101e059444200846078000d05201d03601c0e8403507079503240885d0b040040c036501c81800380d404414030800140c17500c0d034040d000c182600c89070043c0e078807007036403a0858001500485811132098003004265005410349220f0080040000540b0b110601d0100e250040c41403051603450700000040140c45d081241d52030b0010807060181030864500350009003240164001c240c0304000702004003040003255261080181400b270424454540c0e01c0f01000801004500260342007110326036032058252040c4a803100c02c2400034444c3c1505080501030044032406039180840c401d0401c81c00140e00d21200c0c00010602c40180e0700582d40750f0611051001029445806600419600d1186540c40c0d001040303265010000707403900c0703c01007401c00019160002c0701c042050361410000e540c03c107109207010011a8540d90341c40c000d10316680c60818508074410303e10903503a103820502040c011b136480303174200800480b21172044030308048403485c2e03882c142110fa40040314a4400301203010740352600d0206d18001403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 619566960 1250 619565710 619565729
    0x90321030c02031201030818130501060e2d0402040306020c0a050c010c111219151503020306061504180b040509030405180402030a06020a081510120b27040c 69
    0x146852104c80002010302009100c4200480c2d031801c211314208054003498001021041d050081908940c020a000c0c00f9070800100890020300c810700303020b40343d1030301d8803406510400901c400d101e01a090881c0100410b5009408000c0000410b440e40083c2c801c2025040103810f4202d9140f607c145001450120300d414080c0c08d000b80b90100c2d41d0805500c80b0390030292030340d4505461412265003003040422003812100341a402110500420210480e00070b9000142080303c1407a030242001201d20b04d100c000e40c07581c0100005411400c06903592440014403002c074a0406481c0c9034600c0c0868030f2201c0c80b80100b95194412001d070701c1d00c0e00031130350045881400b661a1604000c0031a0300401d40741e81120700700d60303020040380440d20104440500c00b33401c988215150314001d60000c10b114000d5690300210760030b10410150902d0410703c4191003403100d44880b03041ca42010340c1c440c0a4025140700361740c85002e008101000703040e844d4243c1a90140354000064a103840c0c50190400c1000d0b402403c0207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 619568210 1250 619566960 619566967
    0x30b1515030c12072021030c0405030d020d0e090f070c030315060c05150106020d05070c0f0b0d0506121f0e030c0106030b0903031b0304020d170d06050117010603050601090321030c0203 81
    0x46c1c010340a01d680c02e078641c1c603c0f15a29074800c040d0300c4a621507030340042c2d0075106142481310480d42c040f4208240144998441c802e040312071003080481c3d4416218021a820420301158015028005180d0300d14031030b0030089003850103200907007402c045980c0002c000c039000700b100b9030400409020074040d00308074001e018025414284001e5a900c1915000001d110000800c50140005100c030100200b91621a00c2c6507036458411021154012700c0000700040e04203004540c440c07418041c440c000000d080000c0030f00340c00ba02e083c1079010b0002c2c02c80d0400c0030390383c100703800020400344003c00b11101050004240c0302d03c1d42c60140000d660003000c00a06800030710a1100314081d10080c401d80079810b11115440380c44600000320f01c5619031070010040026482451400395902000e1f1406590b243c400f04002c0e0f9858005599070700086034810b03404a400c4c401405000c1c0240d12090708150180741c2500025201d030354088030b00d030341481071000380500740d45540c1c03402d5410f0048030032010107403010350304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 619569460 1250 619568210 619568233
    0x1110a0c0e28021803031c18060e0c0306090703080a03050703020c010e1e03070c0302040e03091203040305010c0507050a060507020c0402070c030b1515030c120720 72
    0x81020907010710703a5800c1a407030100d00d482c40003032482c9940a0654150004007046581e10500075401000000350341c25019003601c8007441c2c08810b841007180c4040a441c1c940d401c80941c107000380306150182c02620008402c0b50046030030303440340c502c02800b940001c0220001c0d400c10540b50280c010a18292a40100c10a00028013441c0036a215a41e060501082c681c40b03414045c2e000e80100562952550b1809076141004a00010421640c08000340c48488030344404012a4892140c008082e09e0030b02d0304101000142001c4d8444c1c48025100d80c16241020703502d50020f544095001c3c1d00c07002382e910106040c8144030080c070900f8200c10560070158900b070b00d150344207a01c42406c1c03d800780200e955140084d84490090241c0300c81c0f007100500c11940c804071890810460816408240c07414405a00000c0b480d142540030110080c00040081000708074001c00248254002428001000f20521400c84000040c544150082090303484650800a4826090420105101c0c081c241c0d80d01002030f450 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 619570710 1250 619569460 619569473
    0xd05060a0303090b07020a17100c0201020a09030f051213090e190b0a1410030506010509010605040e130b0c03012111190b040815010911030c0304110409080901110a 72
    0x102241e9513100c0e1192248003900000700280080d50004010101100154008040100358070305454401407040100c4220350204a00300c3c095140284049082d1103414000301d0f428240b482c09543c800e40440b2840c101c0c49101e1012600040400c5188000f0007101f8801300d080da0040c10481c41070800100245079009804030000540340301c0c044c1c010b5034500046483c142094100742410708025014000c64100115011218200351005981c40d019640001c500d904c0c01120250480b045030703580500305428544032684101b030182100700c85034160f400140c005441c5041c05481a0040d0081948940c54401c8494255519440224022501502e440300042e140000d11945071b0060b80c550f03800405031135201121284540285110a80c0030500003647d110010b2030507030108400c0030100340b87e41d0740d01031002980c60020350300355614011300c00101c00c510301001442c0c1c031900840c0458007800e100408142142c00c0003006442c8914002104942540c22030700b10b104100800004100900641d100c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 619571960 1250 619570710 619570727
    0x60304080f07060618060e0c0304290702100605030c15090f091501021c0c1716030f0305011202030a0209040305120f04031e052a030f0d05060a0303 65
    0x105222404901941c40081000603214001d910910400245444841009103020f80303140002506081c0900440e0300b48a00c60410300030400035400c641541c8407039582003400d058140089d0768000541800c01d081d1401508180d00625694000d0000b5510340750100064408503040140603610242903001b45489080c0c0020803c40c03001c40141e1112107500c005a07a006c00d4020950784a09039200340100c6d0106413081c0c502d444401d8003240c8821100c5041500c81d03400c410701c0c00b070202d110010054042030018034408452003040360300e00e207001116506600480703400b0006a00060031403074000c0900340c240c441d4501510209040c03e0754201c035907000a5407021112340003170090540a010408160080d8291582d01d40d52106260701d502d80681101588801103e0035400900007460944e120300a4011502031088140c0c3c40314070300030f005040105401e090500d07003004425208441000200140301a000181700c2c0038400d80d88010441880054035030141105114041c0c07140c0810002c0c3c0c100400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 619573210 1250 619571960 619571963
    0x20f071b09051e28110c0d03060b0f0313230c0108062101090b0c0d050c0918040f02030f0309010305100806161103040603090302100e1b060d140412020c060304 70
    0x805010440b103103c1c002039011114134125858240a150782c49140d600024051a07860780084411800e4544012010b0329503a10030100e88580c20007190080d22600001141c1c081d00c40e800c0d0040c01041c07641c03428481d6000042145102401c0341e60803254100601c601d11020009282103855403c100d80020716108a00b0b0300d580e0962a6a40c00c850003405c01c0d004200302941145403081181780518891b6850b038007040d41a2030152800e000a2020000c0805580e040324000d0100880d142d40b440380d0000e0300340041d0080c1c41010044d0700200050340d00b0001d100d0300360002c0700170356251902580003405890b00a4000190041d2203c01481180e800158807540031442c070010410080d0f1441c82581d043c0c8040548800a0000040c0812907503003641080031694400d50072544404442c040c113608440400f884110180c010700d040415040c0070701070840b91807400900781880c0c050415410740032980c84241207210b10103030300100002d0103004950103076071604038000f401c101043e4900003112884001c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 619574460 1250 619573210 619573231
    0x140d081e07090b0c0106080f07080f01290102251401020307080d1808040b090f0409021e12160302090106080f011203030209040905150127020f071b09051e 68
    0x32030702c44e01c4400b504001d00610a4000341c680d4803000a03ea00d448038103c1c084c0d404c0398801c4405252a080d0305100e0031030f504000c041c100014115803219100110b103c201414114442c04110101404004040c11050b520f0400d803146c94a20303007410004d607001c8102c021815034006010ba003000c108858100c480c1e900c500003001914100040c25500400502030028000400c00318001c10300c4200e8600a00685a04480c42400740903100204400c0c4c5180d40e10094000d40c03424002903840342061112031050000410100d00080d0a4406610308908203071101c0044c0204e980410950030155611400b5101c46c1c5410002c070320b42151161802c1d501031065100c04000c02c03201c41c05251103981500da2211005105010b0a801400c1569890005103542c000300700d00c0c440000380031b01e031140504100c410501020019403504051100c029004640388110103401045030400041c103410000000080e2540402020360805c4500411074400070241842820502c1402c100038040c0009030341e10961500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 619575710 1250 619574460 619574467
    0xb0909070309050f06010810020304050c0103271a060105030c19020307021305161b080904060803160537051c02030d1503020a05010c140d081e07090b 66
    0x724010800000058494081c07100f0100b1000000300c1d44c1412181a042143e004880d030280305022807200b540e00905640c0150900c422a50081e04141701000128800d903050041a402c0e810380c1520385801110000c0d412542e450107074124101564000c5400e180003030079450000c00c0f000d0705100d020005061007141c0980200e1140c0f08000322151594058035161000500350340040c0500401d03914402040c0311401d41940051090981501000c5064810704001007a40c486130000ea02c012103151b0416201e4101180ca0078041000b04003007440c0c004242100d44d000c0c10700320304206002c88420020042c0403c0c0c030f03080c0f00680c121810940318484507403050390300914100b46040d040310307080459420380507503481205030048090002407529520501210303054070120841c100450100070341c042d40c0204141b210354801d0101f40e50f240e2160200140d6140c040680c585403210034820301c000142c0d07440420060031010304a0301c0010070300104600c1035040609014000107071a020700fa039540f4020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 619576960 1250 619575710 619575721
    0x4050d080f04080a0303020318060c030106050c101b021e030711130c08070e01020304150c050f060405030a030b18070e030705040618060e190b0a0e130c0f0b0909 71
    0x100102c81c000c10800d03040701c3d02102c45143c0075010350012201038040b6508503116024154000c03482910407508116514034503824080c0c159860b810151800c0e88c188540d01c91300802111600c01d41268800e820825454019482c0e0000d250040d0441c600350010864007218246080010076035043d00e40c8421219001400400492840404800000600c41c05d211940a80700e0300715105034052101c0342c2e1401619000c031801a652840f49225000c01198055007008066202d4401800e0f6a0b1180342a14044411104064034080c8141e41c107032026000000c041c00c040740c05201d110b040f20b10650f22001c1200e07500c1800d500943c4010102c10034051080c0c0d40c040c0981c1d051080201038103009004000309621030910f44460282060703080340d04c0e032400b00041044420b1a078054410a41c0071000b20441c035500c00b1580140140f408196049002403c000c51100c45e40462144030794107000c9010203002e1503040c007904190032588554402d50349000b080c8101040f00c800c48405d40402d9610180e551240c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 619578210 1250 619576960 619576987
    0x1c0e040203130b0415110a05220b04030305030f061816051c060302040b04270206071a04200303040302010e0307090603080a11070b0301090c170a0f0f0204050d08 71
    0xc444003c00e5900b14800300310411440505510780c02c4200340c010082120301040404803880380400c81c8010540c140305640380400340c4600b154060180407110f00b002680c83c2003560b90798000e60001c07008180c012080083c41489105007030344c05007007102c600d00e01756043e01d103070b148210010300b1103030030062204010a60a8025421a0484407016111055178010703011104000c0185000407841181049010783c910f203400d00900e806407007034811000c6080c2000341b0169100c1000c1e0301c200d0300080300b40000d9000c14074a5200c00c41caa810f0348079400d15441d1074513000820b4072032480b50007e0034045508915a64038000240c2d425a03a083c00c2004008020100085c50010143d0140210b54103214011080080c9a4050049034805441303a03680018200300d0319803070300e80034005c01461400c18401003010710407a4200d6085c1340110f0600206c0664150325010040e68100c038a0300105890704070094090915202e407040040c203110b4110f0502e0309104c001001c40c5585600903125120108008442d0b000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 619579460 1250 619578210 619578241
    0x30b04060807090f0b0d210309050a0605070e031b041107060c0f11030a050f031312111e031b03040e0f060a14150c120408010203091c0e040203 63
    0xd81d5040350503160350303034403410050146005450095410403404824504110b0481040558851003140d14248510703030340100b80381040110030030036440b003408502090301485011241c80c021400400c7e14036060b503001e0300401c03001d003409000e507102c61b43c0ba28260074400c02c03000c049901140c000c03405503034000034540c65001d50b80000c0e12091905494460854005040e40444816034807000d060044500301d0648038000c4482090105a0811a6000d030341d032008021030380f215242c2c40282580c030003a140c943d400320391540c120000c80c0601421407190181000910381020a07800108071107242d05003055281e02401c0741d030001d50781001c03450404449042c4241e13409021107003000601c514002102d28034203032003520a5402415221800b14604841206a1842880140c40c0040c90003280120005507404560401014025044602190f031500e5008000410f0700c03d00250302c4c2e0601d100c0e440d0502c0042c4154903d10039681e41d81d841c0c0320b0341164040410804c100e030010703101da84452904000c143c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 619580710 1250 619579460 619579469
    0x60d02090612030d02130506040b0403020108040314030901060513180b04030c1a060103060e0f0402090612010e01020c0c120d050307090509011707090203010b090616020301020c03031506041203030b0406 89
    0x202140c4c20002e03a10079400351040c2c10564416a900316600d00503c001c82c4a580a0b05407181c10405c0b0a10155009000141c1c12500c00d00d4469a80303040445424496001510100c8907070751107948c00c201529128088441c1c0d1018020200f1683ea00030f000c2c000c510f000d401000b000300403003a00041c2414007a410a40e012504482d00702c0203d080245002055403040762030070f001c00d10700742021941441c01c021441c0f10f4110403100c0c0445450b00d8080100c1003400511803644040b0f02c4c41c902c24407200030701500e4000407400c3c00268035402c603214014100401c100000c0d0040d10110390800c00300c200021034851451241c24520b94079101c1d000d040350120f4454100030380000600e0000500941c8031046c604c7c4018a000541f40059128085e44080c1c4c44281700b0108680c4091100010a24203040142103110300030010070301032280b0394040781c203a8200800e181401c1d0070100403c0a00313030603200b440154040440d0101d01d014200800c4900103401e945002c0d0800d555104044019252580814040c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 619581960 1250 619580710 619580713
    0xe060f030601030c0e1023030c0a0603020406030e010b090601080a200a021038030109260702030d0804051e010e0d02030910030213030c08010501140306060d02090612 73
    0xb503840e41060030b108403040c89080c0d5501e046000003444122003004000c00d41e00c80700003240d810321014210700c4070840380720324055142c02101e611424030740c0d43c0d010b40001410a91000350b260352400c580a0102c860510700803071181d0601a806090f0f94905204c0c80d4000c1342424148440d44550a02c4401808004004004000028241c1400d4010b2401074681e0800340e508452072081e04e25800d405442682141030151081c241040c3c4a00100860240c0d0150030441e0b144910450840001c3c02d4805040080d00c00c0d07100094001c00c40302c0154108210300c06a01d0b080707850b1004640c0429a1022010ba2103400c0041d101c01240820106101340c0903042110704024610055104013240203000c804450400d03480f40004071441d0a0011090381d512180c000c10b48802c0c03011019050f00658002940088808054100800041c0405103520003a008980c00081c0c1507041600020152008050305880b0b6070013a000c20005944401880840c80e40c1601c4400d65500d0722008221841e546001c0b07030815 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 619583210 1250 619581960 619581973
    0x18090f151b1b060a0b0609091504140c030403230301060813050a03170112020a050d080c0d0207050f013011120a1d060109020901050712050a02060a02130e060f03 71
    0x2c0364000341c034900070f0030308903400c01aa100d10410011144610804190496030040000701581b40c0c40202c038070421400f81000c40c0340d040c2000d4050000c001240d10607030201000c41444281a0710040c110440d008541c49e144010404403105005400148a01d50070403180500050b0020400c855018080341d11030700729080b1180314500904003030218403110a0411006000241c5060301e420500d0720315070017a00800c029410310040c014109200300055820040030800c1c07492541003004402d5600039564007611220b41494200f0038003201742941c03981003111125060b4650306984000041c403009520b611240f440f90001e10401610043c8900c0810b8200800d4207103200e114402598403900ca10300c42001075400c4441049004440300741c40400d25030080006010b907410a034010710b02101d05040031820401d480e0389007109186441072104c00114086507100440c1e40400240e03420103030b404030950610700c030100c40f892400d44178031070414040405030100305151914004600206c0001c1d007038500c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 619584460 1250 619583210 619583257
    0x210201020d060b120a0605060901030e0f0a05030408060a0204241202041e0806010e060d0c260c150910090506030907081e0c01030c050918090f151b 65
    0x81c0341d00812204004c0075049030008007000d50b0791241e1800e48200a055030304007004a00110020411a80170480620170b104008008410800c1081401342c403c400655950f81444100e90810708040d00d0b241da15801448103001c0c0489001600d05241360452292240e820310340c2d0100c54000046400105951000401041854980c102d007041c2c405010a12000c06695841e19643da100c00d2007500d02118002005c2403031854001b0304000c6960040d00880c40301e503111410341020301101c0700f4100801c0c405628a6045410520003c0f42c000c10455000b10183c2c140c2050980c90b104004d01c841c0b03d045a141e00400150056204202504000e41620349a2174103e04595a07800741d4001d00c200c030302c41c11401c5c640c00311030348003208204a00700c0301401d900c2c0c0035200150007509503440241d0600201b0302035020390340ca80c0d00b101005992a5603070b2003064103214801031300b418440c040c0400d1030b403c000c80c110600b004a91b10290086000c2005910b80c506118000d203441c0503106c40b480012500320400e64 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 619585710 1250 619584460 619584479
    0x13121b09020405010e0d020a03080714010e0313060c02100f02120c0307030e030a0c0b03070509100c0212030a050f0306190b0a080a051501081b040306060f09020403210201020d06 78
    0x425900b0a17220000c0c000d8280e02040002250642c00960001c0c41001c240002400342c006018124400d480e0100914807111131182510015a8030395001d40c40070820b014050640410440108464100808a03140f42d07008943d030001201420024854120160003000744200041c24280740d2860256448040340518940c40b5400032009400280f5406240c107001d04d0081030058170540c2c462840444a0f241803400c01282e00000d0184003880380900c1b50207a0740e1604580040c8640340c90b5940c1b0202a007510410101d0401c070100d0924503401400000691500300080b660040f20034000c058582c0c1d039840018021900c3e80602d103022100094000507664004c80c0a00b0b1803001d02d840d4104540d6903403048204030b400485180321040c070300d042c0c400480d5006040e00350700a110600054240a0007014602803a070041d03200b11801c03a56120304014000b02c00d041e440180c440000290315241c82c6445029100e038440c0f8503482c801c800140d0009995000350304541c02071450701e4080c40060f90324045403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 619586960 1250 619585710 619585717
    0xa09031b050c030d02070b0304060b01020703150212010e13030c050708120d05070212040509130615080105060402070506011719060606030c14040b0702011809050601110313121b0902 80
    0xb640a071140784440c074800750000c17a1035015611840391080c00c569a0f5198035014003482e80740c19055004010021001c516500071840005c1030030840560f540008402405c141c0d00141e10540c40740d4030800600200c072142c45d01400113140c0501d0518841402c81c02c0c440d05045c62a4022080f0348107080304031140b120000094881c1054800003002241d031059000da0b00c40300091030180801000700800c1c062031500c0f600160708041d03913003c20503038040c0c0340d034949040381c0d40350310341d50841c3c0104e6030100001e000074080c9941c440760555040d820700e00c903940c0d411365403035040c0503070b00864600c0c01e401c0f142c6a404000d507450248003440500d503003207034500b041d40c000c1105006041c0000d0408041d20380745070255002c28045170040d1482c601e810f01d0000960455048000104d0402c03d0540800a85100c8149901d0141103102000902e6061030070014000311080e02c0c01032800d80060200c566010b1000e110501150500c50491151000f54a07140d90301098600500800c8490302202146802466029 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 619588210 1250 619586960 619586983
    0x24030f05101503151d0304080f01090f11150d05040b060907210906020d0b03150c0403080d090203100e060901020c0c0f1f030c031b080a09031b05 64
    0x1601d00307a05603a040c100a0b151041c1c03800310410894601040000c684120940f035441d410400007940143d0312042408001076032841180692002c6011302070000180400c108822441008011110701c994510102c9108110050485691402411459110000071000d89401c900040343c2d98401c5200d00c20003041d09070790580e16586810002541800c0160015024164a071a03e0410b4240c5030072102c0c503001e00003541c4107603584070700703007140080d40307900207807010b641e80707150100e00032500000340b5203424501c200c58040b049401080c0020110070100b110181c80d000700c9101d644440b11216800600003e6000a400d4445e0400c071a031090740d10b500010100b082103060f02e02644450414074242d000c0c0c8408000a40c014207403400c0c49242c810046248000040c0c030420301c4810341c214685200c1c1e031100d0020082900d42551008481e41845000c40f4509074264400c007012103071400510300e020062488008a03500d85a0b07000349401509003400b500044c083c0024102c049250154440805002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 619589460 1250 619588210 619588213
    0x92a0706181b140f0d02010e03100228090b0c010612050a0203250603050415060602031e19030f0b060a110610060813030c0b070f270924030f05 63
    0x402250f1065180b02045107100000d2007880403c05138010446004500003040341800f540e080e0680042d2024404500c114490410046e151300c9405e81c0000010115103100030705d220110410f2001b150040450b07000e0300e85030b410454032409294255030042034550400c4021810b12544c0c10104140040e50b800d28600c00c2c0c00340c500c00500020000d0800d03005008010f2071001d914810310420307101e588090340c02030288010046407541240e82c3c00c11200190001001a0030006491200f088100715016440b04800240f40ca0001c0c00c0c01e4030204880e04c400008201511980c1c004001c07040c07500160882200100001d54231000f044014062008100c800d14040c00341c9800925052441400d07413040350030355260141c0d1603603260054844d21012070f50803802c0c04844c00480010a041c003410313501c55030850702c03025040441c504000d860b01c410342c003100240c080031003940d903200e680703030307080030b0101c031180b12010452044c40c44a1402d4811441c2c5800115581c8503000024801081070002d0007a02800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 619590710 1250 619589460 619589513
    0x602070614010b090d06111603020d0e0303030a0c0c0203301305010c020d060227060c0717030c06090a03090806090c0f0a090c0e092a070618 62
    0x1060300707089824407032001c01e20014896040542020500f0740e0719240306410009400c2d0f100d0901c0180e503000394192003807102007004120704042e0108010801603070340707003081c9c0245482e03000080d66030310000f803081c0400c2e92298440907401e4000c60b9400f00380d990050645504000c101205207181c03001420300c403d8160700c01c0f04402c0701c1500720129010310b803c9800020703646041000541c1c070a056000c04a80001224640700e0118103544082c01c44021401c0b0401c04041d4000c10b20758404403051040361050008005003840441c0001300c1a00312100594001d618072011800c40d030640c06a51001041c03402280c04001c541000802d00d02d1020303200c0d0f144c40d2030140e100d48005540e0361085400c240c1550000f6000c60092a04c1c48143c204e50388010b03d400c8038a40c890103000141c0310030364445404503030510640b9030300d40341010b030150703001a08010001c01d141c286c01c68920080c00503040ca02500000042040612600d81c000c0c61400e1420b896440c5a0b00c81440c00d0400c017811040842c2c0203801c0d05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 619591960 1250 619590710 619590731
    0x60d02011e080a1802030a06051509010e01240206072007030318090b0105071b03060c0c05010b012609071e060f05070b070e0a150507060f060b03010e101206020706 72
    0x1d1307a0803840e0090000e0040301c06035540d000081c040601017682c04001c1d9400c11110355900840540603065880ba14425545002c1541c0b030488000c001d01a0090200030502c0e040b15400140c1075400803c3d440c140c00d140d501000f88490210341401141c0786401404808800e25804c42e2a001d0300440760903030109101d03600c560324021600a110131500081c02044207a000c20246170460402c0b2884e0640000302a42d01c4d0b40300d10869200010400c045100418083c092003400e10990000c42c81c01c2c01c000d00000107590ba8400c40c070311501c800425820040020a804c80c40800c95000a800d162000080a81c114034200c42c112100c0c1c418900050340b20845d038000c4510902c190303291580c2c00343c4c01103174603180c412080d6140d84450b0496a040312042c3c000050140f20410b071500802d9681d2501d940d240b03018141201917404040d000c0442c2814582c040202c9510328040740e0440b01c031401511400e45441e2094003141c41950b2200300d40146450044050141d1540100b156a1003160100801e4000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 619593210 1250 619591960 619591991
    0x60f1d0c09150108011802090310090b070309020f01110a050d11060c07110d061803030f060f030b060f01121524080c1b0703060605090906040803060d02011e080a 71
    0x2c0058180065041c8004010092410728400c0d051001c10001508100902000c00e1601c11110903052a50fa210b52025003400002d00c00c06411a0307040c9814408003446401240e126450480214104003030000d840d040c0c100306010f01d11080354450260b03084000c9500d0004c0150170031060018030707405004080754001c804c981c1140c042c2940090303594603c10020040041c0d2444181003070f5581d68176440200004c8107a8401e40304114804c5d00e00251905440201100721141c582003800d015003541814000300304d10141d02d0750300c01e500b2902c00002d40c1c90440101c1e800e10300f0080106840741400e0140e40c02c18440845c0b00c0079500201a00c1e017000c1844100d001c180b5681070042c0c0041594000407441c414490300052180c07402140c6221000c51004003418503240850f4029903034141d48610038803503032408000b21900003a040c0014441418030380c45a05040c40301601e0648640608050141103900a19000f080c3d0900783c1100f90604000240c054003d640444401c050700d45400c41d1881080030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 619594460 1250 619593210 619593241
    0x3031d060609070905030307051c020c0310020a0c0503040e0103020f060301030210080601050c030d050114090c03150f040507050a0206070807050d150503060c0a02010c03020412060f1d0c09 83
    0x10444020034158450500380548041d001d400241000045100410310b07440c104024011541305400421602926003008078002941b840380c0011034111550079803640d900002d0b80320800444042c0180c0c1c4412a0b00c040d01c03001d1021000500700d00022034001520102519000c0c100c90080d00c2d00a903404514003000b10620007404000c1d0700043c144c0d0040c0d0320030320070400340e5807020301030520901c0e0051076066079156030000d400c04407000d6150b0300148010403100300f40d828281016100100702c2c1c141b01e07410a00c5800000d284413180000010208859501c62006400040002d0020005424443d034024190b900400d038200140c1701d1352001c500d02d5403042c0e880f10302c51812652014184045104401e02602038900c1690902c0700105011400d507505009050069803070002c02656503180010282c255520380b500c1c2005c1c907105100c208104080f0080300484103510450000e1006c2c0321648203030082c5101001c04071290703d4000b502c0007404000500e9541980121190045e80e661146220305010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 619595710 1250 619594460 619594511
    0x240a021002160803090f07080708250501050d090b0411040e07080705151201080d0215010509060d080d050c0306130b10030b011b05071d0601021b0a090204120303 71
    0x10702d050041c0049082c10010355042880710f002d449000211001c45031030708040d6000400c45401c100d1081140002c02c1102d124032000d69201070a500941c0528a0460501e5104250501100103401280043c40398040c140140d88448000030b0307410300e030609941d8071080c200014081d600c5c081c0c3d44200248009080d0003100c030700d240241245420081170100d0602543d41c078800781082400115444001c4c100c05138003800002008050604002078001d00d03202d130015070340c0e0825a410340140100d40360311145c05e034040d10564940c0344032041890060154030448011101092402003840721000d02d010045005000496a4a82e040c449003d02c2048611010700c2d203a001032007820440301c850194101c40384904050410001e044a050441110300c0420b0800310380c1900101002d00038080044a15844000e84005c0000c25203491000031396a0142d425000d12280005d044824403507640821542c00b03070144540c190349803036640c40d080401d4104c682c82140802d02b80100008640107401e140281003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 619596960 1250 619595710 619595737
    0x2030711011a190801020403050c090c0a0801060c14031b071e05090a1104140a09050103050c04050912040f0e070806090112030507140606040b22020306240a021002 72
    0x4400d02c03000c201d410b02100c0e80001610b0154040002c011500384040c00085005002910003502d20604000c0d42d0a0000d18814201c50203021f40155180e00445ca1341c19240e06062070071110074941045480000744c003280058504c000100b15408032544811440251489000c80754415110341140108200c84401505050b140317100420003032801030790054000e1a218070001e8000c441c00002c10300740d400b03500203076000300d1082c8150300203003000f580d000c00504030312004100c40c0d41940d880940354403100c1000340c42980c036100481d4400505001550034183e000e510146d807144e5941d1042c1001c40c151142c440344d101950300042e441c43c00385403c6842110b0052070056107030b00708100072020400d1200301742c04201c4103002102c00660400507492400495000600003407604070b04000c140c0300035002d1240211b100c040400a00c101d640e4001080c00d0401c100940c40f13a65101c04142907498295607040f0703508030700540344658102e0000901c1040841d40c290b5844c40030018007001603204448502e29203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 619598210 1250 619596960 619597001
    0x1206060c1b030a023f1f20070309050f090112020a0f080a05100c050406120e01020711041b0206191808040609091503030c020f120105010620030406080402010219060203071101 77
    0x506d20724414000c2d856071501e00080544000007088010f0446860403040c4000c0080c0d0b01e020b040c1c000700080300801046600c0384001d00d082001ca0303400d1006100300403084030020308040865440f0038901015200240c0f01c202d8483c0d6848245a940307050f4001524180640d0000c0c00c0b02d0009070140e00c00090b101e45902e450107182c10011603002d100c000340302d15215964101800c03c260280001c0003014000c80c00207840041c0082000220380002d80702262411440150498039600840c3c00c40c1d028498000b518100d0b1083d99842e00540760485a042c050184819101e0070080200041d00a807616503a23424859500c851049089890850705a090000e0b505c03001c000007840760440c03080c00c520281c1030081c2d842c000b40105441c00c001e41444c03078450b51a100140415544a540305890301c61500001108074803070b030845912403246008480400ca04ea1000030256400ac1002c5161142803480c0e060b4109603904003907000303400079500c12000458000114221400c1406107040c1300c05225200c090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 619599460 1250 619598210 619598233
    0xc0201121401300305130b040608041403070b0604021812031803070f03061505090403030606140a08060910170303060306280c02070801111206060c1b030a023f 70
    0x17aa5004101126581c1c1410980030850b07151240240006002c0e0b5142c10f50903003403500d020b690301800d144111005034800d01c0640e0104001000c0c0c15000403041c0c40c0180d40750009102d080c42d4803144d100b1960030200745e2038054906a0000000d040071084280454860000c40b010542c0300c0b1820721031400880c0c82d02c8024008100b0940c070042400040000c10300e00700c0e2341c41307005ca003108100312011b8011956072101049800d4019010742000000040f4032480d103051100058813081d00944581d01604040d400103445001e07441b03441d40500940c03400000d07802c03400c1c1c044d03641d240d1044903e140039001e0100480e10480108400c09050600c0d100000c10310346800900318007c00360b0484140461040030f10024084001b03129070010484908111075a524800000c10004d0b4800f07014a806060100b001c000c41c1030002c144e07612280c000944154804688000003403070002c0800b40030303520021001d92101c040300b102c0d19440a2148020ba50103200501540484a074150f950003c0e0306500242d01e40103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 619600710 1250 619599460 619599467
    0x150901060302012c0d050c0307141e0d050703290601080a020c01111b01060803070f120306031a06010f0305221e03020105010812070309060c02011214013003 69
    0x342c0742c4c0359040b000704000c0103900000e1213103025030029940d5400080d400305480c01c0a10503d8040c5c03045103030585d6481d803942e01082200040301c0281c1c241c1c8003a000b040daa2a52031002c20314607180c00ca01291503054490418210120a132000c80d24004101e13a0704904040d0340092203849100140c64000f1240d903031a410350042c0d4044d075640c0c09555610140c0840c580c9104014003000c000031030005d1920740140514600b1140d0607044841c480d03009000e81d20024003140303d07040b44243c0c8428400d0015020703002c25800303402a030708020040d001d001403c82c41e569002ca040c40c80b030760f8243c1c0c032013040784504403003a4201d035000c0c5c0702080e040036114801c1c069a0070034021010418864807200744040c9001565980050350141c0c2200103075101c1004000e00300e41044141500380c02b4820b030300d00e40001650090944062031151100f400182c1c19010103683c041c0030f4010051210360014000404100d031100c0c3c00c08800d002d88054040d41c503840c1d0340014013042400018401d04001d00b48209820784066 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 619601960 1250 619600710 619600757
    0x9060806040611070b0423010b0a0b21011806050445080405040c080108101a030a0b040204050106030608120309030c07030f1505070503060d111215090106030201 71
    0xf00d042c103c0801100d0005511880d000d845203000d070000c000200111064402904003004880803968145002e50b6402c0e500c1121480840306c1e500211030340c40b03c030112a13a000203090b82e91072020a014000009081207404076614050701c1c45036080146540f9842008102c0300b4440a0482948808204070070700c203c034a0380c1a00050103500030700601d00840e040080301044042048901c464081410052403c0c20301070410746100f941411512036040400ba1545c1d000c4a051501743e43d0303210701603018900b008102401540710003a080c1c0300d02100360704005c060542c003600c0481c000c52400c0e0000070240c4c0710b88510401d030fa154001504034004400107103c159040500340001c0d0703002c100f000e144180c0013081031030000e42c4220510310300c4407401c2c01c1c190303a00d50050058034602c0d400d0030100007040b40c2c8401107070b520401c00c940038000000241003d440159107102d4003500041c800c0101c116086000610300c0c90301c2072600c8480794aa440e0b420560980d942e512000740030030113000e0251007481d81100d06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 619603210 1250 619601960 619601981
    0x10302030d1b031422090e03190f140f0a12060605090609031e0d0f172208040609050301060504060b03010302150f0a030605090703050906060f0a030b10050307090608060406 76
    0x81900b13003810f685c0070b00a00d640f40b00e0301060b065204135042000341c42d540286500d62401c0c0b8040c5080076448500d540419400190420400000800c1e100e00f40303014604074800740108466290b02d50300104c003d289240c0c092013881000c502451548005015140035203401e81d500c1e40c0e140340c10328201c5014010f05070055002d10340d141c0544900c00b1400c01c001c1791024040c2d030314280100f454151a20028109942e01e01a803c200181142c03050340382101c00c00003d0b00700155050340030251003043d514901c242901032004145110001d0000740c030702e60200100043c0e81085000700501942c0340c0030402228101d11034120030000030300042006d85041c0c40365a004c0b108040d2032500d8100201e018030191b91001c00100042507940340f05002ca400d00561641d8400c096040400160424039000340e9500d1000300b410384241301e0b04110601a450b902c01d000c00442d40305140c81c080341000347c110b074022051070180302d000340720f03441c40028185400d005e140c0071100761002800a0780c40d03d840314009040500075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 619604316 1106 619603210 619603247
    0x9080a03080612010e0625020a021e010c0615260a060507051204050d0e06071e0204020f1314040b130b18010608010302030d1b03 57
    0x940d00060b0441e80740319042100c007040e80c090712a6216040031405403506010554185548102110390144a00410b802800b541281d0300c18440401039401042c0c02c5012003e502003000d408031200047c9801004c600c6076813118000d031180091010802c80c5040010020074454841441000200c6980c4100360300085821996965440300d000d071140b0760710004941603034000c10440710344105480321003c062034141030081e190002e42c0703601c0b8049000d0403000441d52800b841100c44541d407010007000540000002e448408000107000c0b078219600300085181c420400b400350900722103411113141e40b82c0c14800e81c04002441e400b84540214140907482046131790b2030304590b403211911000001ca4070900c500080c044030070a40c04c5500c01929038008100c20b5444031030036060f20300a400f04c5281d1042034104541150340100c4c4019100c9128003400c2c0003070f10401d12400301050110 = true := by decide +kernel

theorem cover : BRFrame.Cov 619424460 619604316 := by
  have h0 := BRFrame.cov_init 619424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 619424460 ≤ n) (h2 : n < 619604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
