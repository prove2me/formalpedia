-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1482
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:11:21.138444+00:00
-- url     : https://prove2.me/submissions/9d12ab1b-c657-46f9-921f-7d1d73692b30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 266366906 ≤ n < 266546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 266368156 1250 266366906 266366917
    0x303120e0c060a0e0112050411040b0904050a020415030611030916030503091c0206120708090d080f0727180507050703030b03070b0a02030d060504140403120b2112 72
    0x420610800c80f500710b892040032404c000340c3c0c0514000c200713050001510700544100741c4040e6008040d480e4000403610300b504c1071480e407078003d80b4100c0103840e164940320307140c03451990301900070ba4481120021680346ca9840101840d032094040201588040d0302e50342a800c211a2420300d84a50b010f0980122181002c0314200c0b9070004c005c6181410020034892200d000b044121818804c2d14425001a88c844001d814420b040560150b2035251041d4010241e8001810480741900300c890803e8210fa40100b940c3da01541940c03403601c1e2510360071000ca55a10209142d84203203500c0d4041c2e800010744003085078044a600800d2190b815459480301c0085403016203032040480c1c420440d020010307000f6040801600c5004054a81155031900c1c40d46465000b14508401031b040003e2902040040d4030030000a001c050382c0c10425821008070540200034094005014001003200d80d0387d5803056a0441a0714420151802500c041d1840e02d085009803500880001801400104039100750408241d46 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 266369406 1250 266368156 266368159
    0x18010b0a03020903071d04020f041e02160609050a03180b040e09010b090108010209121207080f0d0603121707020615040902043b12090f0a0303120e0c 66
    0x80c540301038200d094000703500020440d5058042c0c11800509a83d4404d0044a59010a14100c50394034080c4100b01f0201001801030384101d1908040c01d1144019010a44a079400c140005a981d55201c040b088071140020004040c54203003c0391500700907011680a003003510030340f40c07201c0162120064405d240c217640900034107014244001c109004c030074540a900001c6c0000009074052940c0e005c40d05680090300b003c0601da40005078002581440400305c4030040307000c0081e01001d80c49118040e264030407150003401100c03000c648290b803e20060700326400c0c50544207003000495900d2425040b500303000442d060100e0301c6000002a4040000e990714441e850035801303046a5a65507507601c48000e00c503580b6542041e6141d030150011307220341c4140180300820008010048030340031820b5400700003802281e15601d900034a107080d0f8040000d0502d64125030001c2c1c2685030220704000c5404140f02890701c540c44020103500106054205e1074010b0341d070840d41824003098484805007640d60001c10600c0303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 266370656 1250 266369406 266369429
    0xf0e09030a08160c02033f1e1b01230f0c0c07030c0e0103210e22050a0e06010503010612020d1e080a031415040507050c0d030501051801 60
    0x41c122410032410f5001c01e400d07418003110f00d03205600401e2900400d00d00c0781f403443c040e10081403c402c81400340d13401308125512041c0c042910b21400c00c007181c014618031440d0110402c803420580c502200c251400b1010785000910801c9441000c04c0c080c010745420381030b0000e42c1e45030758280e0200b2400894860b044800c2c240407261142100c00f42d0b02d50044242000c0ca0155910210000c4e8010102c040144891003600c0d0740e650441c04c109000000c8503007400100e1440e0300120030784540004c00301068031004c072065018a400500264244c00440b044a005585000e0400c60040080e0b4068401c01e400c1a080307c5090784c0b541c06240c2210b443d40900458807000904000c01841e010400f01543d80c0f103245032004250152a5034400c0740c0803c242114804004505110741e103a041c4100406482447ca0700303101414003620012001c1424244c481c080c5842d0400120041d005a0844602510310000c540d00242019401001000203014041c03050f1a41038802020364400c81c8654166410340d49030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 266371906 1250 266370656 266370661
    0xa200f0a140f150705060603150108070e04060b0a150e03030301051c2d050f0606010f03020c12041d01050609031e0106050d0807120c0804120f0c0f0e09030a08 70
    0x1086100c070740d42928280d0002080c1c9883e409007a40c0c102400042d8413520040105080074001c05013000c41c0f1aa12400f031303141a0004005060b000120070044620fa155003a4180c0c50391b0030040083c10b02e1510964204140c0340002602082a00d0468201084c0340e850045240d0910105520b910082c407440d0340c0f0000c003c1d00301c0e00d803080c680103a82c441441201608055240d00c055003094206040f11100c6001210900d1024058140580d0f4010b4403000040c0c49649450320010b80460300507203d4030100350b800315a1440c0c03040104074040c002c060008009440c0c96560009114803940325403000c0f11010920300000326824074100741c0b41d41c0c25008000c0c2c6181a001004031551601c1c5240c0d01210350348806c000540ca45030700303400322221400398147c20381d11103a9040800c40d0004072148c40303040254000c1c595002c20210300568059901224500342702d19031500305040900303400ba2001e04103c513003a10000d05550081c00310011581c0348010007460350b554020303280e100c3c0204072000020a01a000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 266373156 1250 266371906 266371909
    0x6020606040216020d2301021207050a0c05010f02030907080f0c120304180f0b030d0f080a0f0612060b030313090f0e01020a090501090f060507140a200f0a14 69
    0x7030b16040700d203003c00c030b00c62802640006100710505070096030441d00c103005108130b4107181280030110003800c0c03000f5441c2120241030071300f000b4001008441003210105016a406204100204040da00003000b8405201004050301c000e5006035941989840344010000d001311010441101e200c400f20003805000c1005800d0040c0c4488889404400340803c00010071502082d0704d105103a81d0ba031317040016100007450342100840d20540300b2a4869440b2100403002641e01c0f407a011f520103d00c1ca00044203482e10b00ca40009032100d0580b40400604003400440c0608246900c003030b400c1d005003030a0050200c03180a164492103042410380303240c8002d0701d09204420301030300240525181c0319800a03041401e60001c90898002e0100400043c40e5008108403a41e4041e10b45e4001d4148000500b10407403400f44003624602c074082d8000c0018401503000301c90329205100004050383c0000d841c0d4042240000034004030207000200b28444d401100e4a60924181001401c05843c1e00d2050030b03103071401e03410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 266374406 1250 266373156 266373161
    0xe1207061206180e03091005071106041511010b0d11090a02041a0c0a060906021201080d05250209040507031a070e0603040c031527050a0209180d11160602060604 71
    0xc0c141c95085c881004135001d55110318840e044c03145802e907a01d60f101d28180c90640500d0706042800d40c46000148000d011030404901c082c0301c00245420000d000c411840e2141e409800d030312001e203a1112113054038800b4008004603808c0b44100c100d0311440b19544807010304c0200c0c0298003840181c00058815200d1000804004010540f40d4408541800c000c0d40c1d0341d1429604022002c690183e008a0600751854070060501c0c058400341c000350410030004038005203140181d240e41c9041440045204260b00c00403550383e035809801a10328121480c0c40d00700b072540d8a405201c12982c2d11400018800c040c00400030280c000c0d4000d554030307048080b000d401c00480341c1000d0b10070f581f40400480300000141d03080340c240340c001c8403041012859810348090543c0e4603143d00700090301e10700d00050340b80000b5004101e000b01741d541203e140b0a581c403a80c01e080c00c20505c2600c102154410010140c9120790482c600112401b104400c8a80c407108043d20795441c0b41b541e100b06c1015911210109000e4070740340c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 266375656 1250 266374406 266374421
    0xa1707081e07210c0b04080115030506070c081603030b09180d05031503071e05180105060f04120f020a1413020d322206020304030e120706120618 64
    0xa5070440c0c28480c15240c12030160502e85c8250030342c2500007420440301d40c080c0590b1b200008403400100080c0d2035074070744544500005108504108002c840c0000b000101425158000181c0c882c0f1580c6030380c0d520f0050028040c65940f60300c40c100c1a40003e0f1154500f00c0ca80703800100b55806803000340424002035031290000360843ca1004420401c100321a10104080e1000b002e02c00f00c848541da034030540c20b4038140c503160031080c00380d110707020445c510442d010381050441c4c030182e03101580e8a025402ca400c05010f181c001c00741c0044102c03000810301c03c01408000c60310b4001c652030040c041e528690009029030088180750800306d0000e44102d108140da0140c49042c81d11000460741c004122104150f00d81720300403118072040c00381c3e007487e4039842400e803099001c0200e00c0415a400541d050201c11048422002848a9000400141050f115040406400307030040d280c40c07958641100010780316a5580a5000001c40044003050204070707501030312048540c3d030450322581c1502e4440c140302a0009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 266376906 1250 266375656 266375699
    0x4080a0803270a0b010f08071412030d0e1b01081305120f1206030d05120403090f03150e010203070c02121212011802040e010b090a1707081e07 63
    0x101000c1a4041d1105850a00c0ca4030540d4060607610f0000c0c90711044c03004060b00054106441c05405110150703000038440c05a0311800c5c544100800140700103488c0004410148000340800b06204041103502d421900b0003101000990701d41d2101c035924006c80700c02c00c0c0032450010702d8280c00300c1c14404503c00084206400741050f80c60090903d19104d4044d4066004005001c030000b80944e80b1036100c2c00516080384c81100603104695014800800c14010b03100d954403000030100104040502a049040040000800300060b0603601e042c10b40e5412903000c0c00d000f12900b40042d01948040c18800c80c1c0c41030b4443c0e11207003201000794092000c44158201c5102ca00c2c410040c00c4d03800707040008081d041c010a82c0d070101489604024007900d91012003481001350b540148810b0016903481c45941e41590f02003028551030320809000078100000940c4507208900c501c400200104c03802044610a450f43c030001c0b02c00c80342175001c0b0740081401aa1806605802c00c0c04140b03e00c0441140c0c0c0d01301c2000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 266378156 1250 266376906 266376931
    0x61213050106080d12050105090c2107110c09070518010201022718040b0109020f19031b080c030403050a020a1e142b030204090f0f050c04080a0803 65
    0x603035486086552540000c62030f507000f00980030500d644015070012501c00d4820a2210b035261401040d03070403102800700c00d070750500130410100301640054240740b000d540b1943c44070303181007264004e4140c06105502449a0051004041c1a402c08001c010300604150f0b0f182460800802208040c00c00c0a010682c1155003c020a4084a0311110380804403104001040200b408030300c1084456900d4000c424011200c500c10000810800070041d41140c501520150b942d14130f540ca80032241c4143c7e0140b500c0031440f810322240c4c00d549a40913072005041260b08483c0315050860030b0303884090842c0c151098402c10000940001d110b00003401100b00180121045c0d2011580c030488000c464070032918003010110219020320208110000e1071b60118800350104620f0002e07504281e4007042640700f07003580503440100c015482a81180c0003000385810400c442142200c1c0ca102821001e0210664181000042900160b245045034100c1319154010540c220706941d850b612600010411b003080035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 266379406 1250 266378156 266378191
    0x92f09041101140d05062e050304020109080f01051f050a0302060901031d0105060907110a0b19020409050604060816030b0a06030b0a0f0f022d1312050c0102010b0612 73
    0x7140400540a180a07100c1d0100c5c0d00c1c9421424405240504c401d64800341d100703101c0355070f001c000e01082d05002594a19003240d483d596800180c1e070810301c527801208180f1401d5203c80e40702c0019801140500807840100107a260031920082d000f0039240602030f030140b24002c08100526111005148004042c100401c0288918007207020b9400240040304499448004211080c6800c00c890b03940002d203820044c3c0e1002521601c6680e549000318024414407000340801e40c03900700d40a0001050b10020801d560752a1501b0100c3c010b070a0644105000340d0900b04045900703135000c2147c031800203030541402d070600d10710740703c004c800320340585000c0f040b0343e5a55000c0081080d0000981c4100c080180204101c82c450001004407214106000d42640c410b01580302048005046850264403000c3c5041c0d200c02030611200d802d11503140400b54143d1341c1c0740c0000300d00729000c0e0f109200030700410594490700e94440069003611140030b80140c2c0110200842d203c041e086224158001c95080f10070702121 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 266380656 1250 266379406 266379437
    0x61d0d030f03051003150905070b0309030a0201050105030a120503070507120503062d0d05010e0f06010f15051911060906010513020403081e0706092f09041101 70
    0x14000142980015841100c907000c1903003501449411030300e494071003a041c524644a244a5070782d4409a0b0017841c1e1a58002c80502c8810042d09010305a0a41030343e55034241800c445071759600c0801004e0255007450000100b0b8070b40840d0040c0380e15001407950789240002007044641e40e000612800134001e060010001068561328010f811800310344960781d5070306280041245451144454001c040701c80003913005d8003007800b180194007803c2a078481c0001a024540300b070140c602d064500120748642258207a001d400001c1c064120381003c880405220384034181036500009002052012843c00c2240b040809012074440c86030529a1900c14103111503d034071941032250589250280e1703884200144501d240242080c0d90040566608602c0d00c0d25590303e600e56030054401181190142024071003003034104500300c44036103600c00800c00401215261140342c1d9044100711501c9400318164010b050f201512104e020000000c0400c0300b00e0383c4558902130041d04031034480741000708045880420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 266381906 1250 266380656 266380669
    0x9010815130c0308210601120c0c02040203090604060506030f211209010501151701030213020405100203031f14090705041e150203030f010b0d0209060a0c1101020c0307061d 76
    0x2441c4071302c842e2642c2d20008510f02a080c25024003440b217400102080c00030a0f03801c007803d01560340429401040341c104510040e5071781c201488020b500140000300700040c0c050301040e1280300303511441c803c00003500d030324040c10750350b0b00c4181e60100c82d54020f030861094928259050f00722200210145840c00104102500b00d141055902400d035a45403001406605151820500c0c02c2c1d9440c036100b800003051070341d146042c60041c400130b0f004d03800b521540f92403c0b060303070110307009800c0c041c040070b8014245000c000d659a2040303c1c10b0b03510241076250f001a20040c8551002280d4000d40d10404010800d0104541010086c085005001040000081000e540385042c1800c3d248440b07515130a518004070080b81c00d40210501c402c5400030010010131002c1c070403d95040d1141620107d4807410481d40b40c60080c400c181480364000b03400f040a440d696400b40b0405400ba1050300c1614141600200581e0350f221245062545500416800e0292904c02d41000c803151210a4403500f019840070041400d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 266383156 1250 266381906 266381909
    0x4110a12050a03080630070f0e0f060f060702011d03070602010b0306010911030f0907050a03060606120b0105030601050702131103090d0203040f050d021212041409010815130c 77
    0xd00350003074084031003415003000c4c4840d4820750644152081062a43c1d12200c03900040c45014a400c0f054116150061010040f4001170000e502025002c1520317010408414001155207840a61036400014035600701a10681900340b8090403883c1040240d07401550071608488404401c8007840030f0304266981c04120032002007115400015142180106050401c48160401c406c03031820405039031040c00d010390490390301140504034201c550b00c40c1da2074a421f0140d240c0c4440e5022000110120a12000e54458001c444194440d44c0d00790455041c40c0c400d0390980d400740b42c003260042c800a020b95001704010241d0b140300501d25840e02002c80d0080d002ca80c0c131084c541d034001c03501004004c03180c0d07000c00100043c40301a00007103042074500350780c81078000410302815010700212589042191a501c0005200c1d0641000f550803118501c04510340380c1d005403241d001c60707030301c0c602c1c121603582000020300d810303102150090001d20440c00744007011900c019140d0b4110300d840810b84404030304145080d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 266384406 1250 266383156 266383163
    0xd030e0d03050411131a01081509130c0e0a0615020d120605120d0e06190509180910060b0406080c0c19030201020a02070603060e04030c05030c07030311060c1204110a12 74
    0x74000c0d018452603d1406c4005c2e405074180421030050040340301c0c1d101c00650703038807100f00e0700010703141d44a41000186a0141c28020410504000c011030103c00301d500d91481268440420468260f8601000854400c0c0950250141e0802c1c01d0300b2086c04d200d040f02032410380c004140490f40903580e10201d6290440e2042001c0c182d000030065030999540a0f43d82c03514910704450703213403c095002452403a400f400c003620303c092040c0001d0000460b200d080e4410114122840082018606031600a2705c2e210600110951285001c00c00300e10b0062820a5405440b42651180520742c0d481c0817900340c40e0b215000009407481004008030300041018104030443e4031030b60001da100c0d084007102a2503c9055081102030504042c001e00c45070080c44282d907849034142c5003608040b521424504e0451244942506050040c8940402403581000b1076207000142e02c0e00702d036042e07900c8d1828070307420f80507580769208200e540c4000300d0082503816075102e12118000340f40440b20b50350351402d010b204506480c00c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 266385656 1250 266384406 266384411
    0xb061909090c06030e0d0f0e0907020604050d0801080d110c04060b040905060f090a0c030b090709030506010b0f160305040e1302040c0c151d07060207080d030e0d0305041113 76
    0x940c108400c0c0382c00200240b1507030509200c20000b003491617440d82000102c0d00200b0150000c011100ca00c105051081e40303e000c1c2c09030246080c000c80003915228100e0301640c1912070f4481c0d4100086c81155001c0c100e40d0304101400b241405048111903400c541c0048400d188600c0601507203540c0c1d24405c09005202c1d045a140d5502d143c4602c800030750364020892803048c540701c05281c1d015107615400795403140c012240024903520850065000307045d428102504a4503ca08020a040c1c2241d282c000380e0740180c00712103060b0390f5552030181070311a820401a04d40390034810500c2201c0903480c0b10b4200d5109003030250030b01d80c0710222143c0e045030880302036070343c64075612004041d0308003032195080d1103110340303020741603030005458184502e00011050103849640b5023800c0390555618020242c4000300000351240e669503a10005c0d50365a2500071004d1500a201c3c212101c0da0182c410000b0003000c41019120038885400c0035401000000c000b95101071540d00c040e4060364644512894406081800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 266386906 1250 266385656 266385671
    0x5030d11040501020f0a0b0411210f1015050f01140d15060c020a05010503060406030213020909102403020c060403030c021204030803040f0203011103250e09040b061909 74
    0x28031341401c03c00c41c1ca61704c0d00003a0520340441c03640f051081e44580c002810780780c1389000e0404180e009000300058444041c1815a504203d100418000f480b0b14100302140d07a041c181e04020001c0b6030000040003c80100320b5020803160420900c0c092150005040542c80729010300c0714404d040d4411f64982d00c00d1603035808100800c030803000151005d000ba40c0ba1504184245c0c0e40429002011400780e903061100100c0000e042e82d0f43c540040300550b5010b04000c00005003480404044d400800e0307018425140343d4001840c0b9807614415004907080e074a2028000c0a04914030304004240d02e18502c10160200b2113003070802002c000386401103100b50303000200c0f0705030100f0003800c0484000142031f4241017007004201040d41c01003541d4219400c840802042400d6200003801400460008542d804000c801c00200c4115254800b007200241c203540d8120801180301110450000b100342540811132001083c041000320103203a40c000c00140c0303126040048501d801000c5c15055010b9006552038841 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 266388156 1250 266386906 266386909
    0x301030f030f170708150d0303050a050c070302120901020106030b072d02030d15050a0e100605030402090a0203040f1704030302150403050a08100b04030602040801140f06010c05030d110405 83
    0x1400ca02ca00c5451406408041c032402c1c01d9148240060012410043d011340418150300c00e50b940078804090040280030580d0aa00d000b802403c0c089038401c04291034080010ba1030091481107402041e0316a0107811a4184420030301321980042006a046658503100403001440300c100440c001c901580303d501f800056060354040e80d1607101311010814070035600ca06444c6400000791030105000341c0002c50b038000102401703980c00390039a01180d8090350780b17400001c00401411455009006010340341c8070b146d03180c07403094131507204c16200207400c543c1e0a8000f65900c1c4096002e550818454040311108205588408080709070000402c1558030001404108250301000070403c40c02c0307104400b04d15450161070150030f82c0100e078410002d000c042000110507009003a4642e016000841c841c40d15181c0302c1c1040740c000c0d042401161180d40c603020651883d0080542c9042c030030718000600d040c03140e480381c0c0110b46a02080c80110382501c4240710b0201c1032606030003003c0c031101d00c0003d400c0d200ca2800c0e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 266389406 1250 266388156 266388167
    0x2409121e020c03070b0706090b0a0207020a090e03030a05090a02090f060a0807080a02010809030c030d0f0609021c1a030316060518060403140d090609060506120304050d0302030c030301030f03 84
    0xd5400c01c0d98446640703503500d03803030106410080722818502d542d241c01d640e007801e40103410f2a00313008140ca0f001204106264120703a01a0005500030756401140c0d80c1c4400078641241c01c503041184c550750091001a2a00e4465000780d81c0c407210010584a0792416617021520000058402e1030003c08594104007550800ba51240018602ca900400d146440d28811940b40c0d919070102074108041c0340006080601c00f002110f901c908803108407a6112224110702c80207040144125002074204000081c00820900030758214014030417074200b050158800c0c1000429001052540546c28003800c104170b079505102600d1840100070141190545610b00103044820060000031181100c0c1121100c5000000e03015612661604045402548080f4046003a000e05440c0008650074089510100009904100300480c803401040c005500c0721401c001d4103c0380000305120130761080c8020801c0d40b600117030202d2074034003d0040c1c1785070070080b000e120f01b140c0c001d820581705001812055810198442c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 266390656 1250 266389406 266389457
    0x3020c0d0f032304061a09133c060b15191e050904110a1107090519050604060f0815010911070b1509090d140403240912 53
    0x2400f200400e0b00860203105502e85004d00b0161101e84d4504c6071a000c407a03607008060070924010106c003410700c2d0001d03402459141c0c1c3c8100311162034400c1c01c0d9500b0015841440c0700304100400011014110004d13030b5402c681d1441c1c0c0295149038603526956a1034440c410305450301c0c035100860701e40d120483c40d0480078186081c1c0103002001120b0142c0301c4511030300c1851007400300451500d2a500c80002c00024060400c030a44903940340d02c0011803003880d41e0811035041030400d81d2400d6480040e564045d12007140c0c4119640c0326441b00c0001c404694202c6039100361f50103000240006403003034590440f1996201d440c2c2001c18640c1c0143c440b00710b507a8074482481e0040542507801d00100d030612508000c1401030a500609905d209000300d0000050519010000a4082c0c220740f00ca26090000075603030207840411902040c1c00c4a540d68030b07482280115002c0e2900b08140c56403512700d46104040c8210410031020b40c065540308254000f54601d4007405811041e0703a10001c48101280e0011348190a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 266391906 1250 266390656 266390681
    0x3120c0215070809090a0e120702100f091203020708030406111203060d140a0609110103140c071b090e0703060b0603040b07031d1005010e060907050409050703020c0d0f03 75
    0x203200c040b00081004007280c00c040401c1d64648100d449904000340a0208048000828041c030112180e0b81c55500018000e0f91b03000715561200018044c105607500e1500c41e2045000810040f81801103d90990070310350748502c6841114001682c3e07420050441d08550410000a80c0f00d0b07492154240041050100e000c40454269296061a40010394112842d01c0010803c2d0004000b01c296040103210040d0301e1500901e0074020101540742240c880a8136602031408289042c1c0d41046c0c8500c0a010103100f00c1340100454070344a4642c0b1070043c007501002c00f8a0761070708085004200080c0ca4000d1010301c18128000b0580541145004400d5850712404035001e01d00134001c0001190550040c0d6800114506002421000384144d0a004002007544031155104822025103861030a0340310138102c510380c0021249585604c000c20400740c20a58404000410900040c082c50740f05034040c9420071854200180382c1251205264200103841da415408102084c400d5000303150940115020500c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 266393156 1250 266391906 266391949
    0x10806160806010e0d0609030c0506010603020a080f04170c0304030c0509070e041e060f08011406031506030a0b0a1a15070312150e0103050f010212010e0402040603120c02 75
    0x203458000034001000100483d042014000151009031140385840c000e254000c0000d00801d045414040d100d2200e0340b00031a818400d4500001e02a4403c3c82a103128544d04da031500d5030751b00c803801c0305901e032040608180d0b44815a2100c03007944082a600030014210300c50041c64407146503082c02c1000c0380340b42c1e001c203024010301d40c10001c03002d034803803036400316148101c50000350306000e4100500900d641c4003100000f04d16050303002c1401c1d1506103028088507040c40c001c0c01031440b80048540540c0c829100f803a00b5030302281c80c0c24540e81150322204c3e40f046010301280c0480c0a5519072140a03036040e02c80034281ea9449103040c003000d603a03120441c0701c11070503904805229403c0c080c12050323100390680502004000c580000c01889140c004007401070554201c030007a942c513aa07600007503850a1204503014828912844902035043c001e988501b039852842c181c01d40c0c60a401504103000c028000c9038003603034402001c00050010440080c0081c030701d5031414201e0034144140600241d00e880650341a48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 266394406 1250 266393156 266393191
    0x10e0a0f1103010b03070315060201200414090c0c060a091101020a151808070804061803020904141903030c1115180f03070b0a050a050f16110f06010806 67
    0x22801d0200c0b81114000c01e5025a20f542d0713200200c00406010704120a50a9003075800500d2590540041e407070450b40c1c401e00504009020315006281c42079100b014060301c1d00a402402c00e18180d01b0b0b02c0d40c415a2885001d141141c4411004c0c00d1210485004800940d00ca410009104014a5403074511030280024102c009048e01d403440300e091000400d080c0305480b4049404000d149003207102c1015030103040c5644030800d5103003502c21500b042c00744d0000039145854090070759558a0f40030007100e070013504800c00d40d259034035000b541481006ea42d503128410007107400030004586a540390054025500081d920361600001002c828282c10140d00a80c0816044143c003104c00000c690450840004414500e450202081c20401607900780100c50001141da03405202d0300c402294401c260741441048503a48004140c1c0803100182c0d942000074642034001860b21442c03400519115519051040a450344509254603051023805a447c042d080140100a00070003049140c2c1c00540d4503e0460310310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 266395656 1250 266394406 266394431
    0x201020909060439031118010e0109030b100302090105180115140c07050102010b0409050606010c0c08030432030a0807230a020a0608160302030c0c0105010e0a0f 71
    0x10721010745003512641e5240442d0008408031942803e1354003485000d01540e20b02c1c91500c20240c00e80c40c0020380482d040802911030603059500b101c0d6007418610030913006450020045030b0300070490159505001c850400440411001404541b00d5501e0654060006041d40f05002450906922160058045181c62901d414015203158195003004518102e120120a022103001c03512070601d0381c298000049420f09090045010002d5450a8009029140c040300134002100c83c3e61402401540000c000300e031183d8400c100c00310095000c1c031401c4400079142c0c0c2c00c1508540c41a070101812098944c2105417400101410b0002401002e400031800601d040100c5d803034581e0588000e0040000090400800204a1004004168030321120400c0c241c1e5035042a6108003440c010381c071410803c44001820f030b1043c500c0c948189211082c481502074010030a601a41000e418201504011321904811010074401e49000f001400300d0040b00b42043d080c16400c4800010a0804150802d800503509 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 266396906 1250 266395656 266395669
    0xc0706090b070f050a02060a0909060602072403110c0c040b060301030512030c120a0c020f0a030f0309060b0409050a0c0e010e1603090203011b14180409030203120c07110102010209 79
    0x101d4000f100d028000c0c032241303040b07403c010400300c0003503021002103920440c45900c803401c04142c41c92504100842c80e26090145d0341c440f914894200007100f100d0704081840841e2445942d400707858100841c8030344683c40240c102e5004410710780c2c225400451412a50301d018061024801e03025610703e071855046440d4036845800d2490b01c621031060010114021034000b0f0220ba624020482d88841c5504203001d0000241883c1c003c401e00600c101c0301c07646484900030850044995168031842200044600240e02910203080c040c0c0754180d0b2000e0325071494843e2b00030082010310980180c0100d02d51460000301d070300708075000b49224a820400600400d02d00325400c46d0002040d403520a058504000708a01038052020029010b5080130240807140000a00c052607800c1c5640303c0c9030300c4d00e14182075001a070140c210220b51155038801c40f071101d8200790340441e01440c02841500c2c0b50105c1c00d807104805410590f1541104200000d24905020880c0701d0742490070b400b440250300d41100e500c00100c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 266398156 1250 266396906 266396917
    0xa0c050c1f091e14010521040c05040203060a0501030e0309040f0f150602100b0f040906050a0b04091703040602223003080910110c0613080708030a14010801020c0706090b 75
    0x31281c4c0c60100e44041da0003001518440c1402c40400303440c1c0302000e813400d00200030940b0225145200e80401040e249828000c0d00d00c82e040140c00e2048583c503003001100600300d900000d940c507000030802240c030342d00d660140a44601c610203012070b1041e601c01800b030850308013102c40c0049448107081070204590101c0c1e9040c80300112800403039441c4080e000075440c0754100020613401854036441008001303881d04840c1c400c1401c1030741040003074215030600c810707250a448002c203440304c0029079601c1009108080c5401c42d0084000605012800b42c00b40d0303064071801d55801c5240480c070742c20060f2100130110f614075003846c02c0c042e0045404074044121000076005001341030000e0350000402410f4100021001003181c590240000403512215201d030303074400460003065000c1e4000185042000702c6910400d80d07880b0701030781d107840b006440d80009604041c0080c005140c42d03103d012001001c00c2065400ba120803800161360740b000c800c1c0309182c0340c1c103644260706220300b040b42004107080b000c05452 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 266399406 1250 266398156 266398169
    0x1020d0e01032c06072111070b1f0803070b0106030c0e1005090405010e0601020a200d121d0604090c0302070215031801020f0a0c050c1f091e 62
    0x1035418030404016809001400d40070452445000300701d03400c1e1261580406a080515010354072103440d000d4089500d058185441d070340c3d06101407600020028940d00c141650030303061032070300c0c00d280c0680e0b075403102e9203c1507a58485450a80301a000820b000320710a00007030111000440c503040d45d82e51010642c41e01403183c41d0a040e500d10180c001710703000d041c581c21512001880c0c0f1030f449150000c054a25008661030300e00540c40c200003c105601000c918602400058008003005001c9564000095008510b41262158440501c856688844c807003a001c451049002030850610410020140c6080c400303d580070381d4805210311603c0e25a00120390a540b00c09001050606450300150003030f00c64003400035004610f0035030711382c03250100d04040e41c01014009083c41440150b00c48582c280e000f51000c4c0402e401042102c0b004080c0205ccc42005414416000e640c450401c400019407070146400c1203420601202d120706076480d1340000c100340074000311134608642c90303440d26120700e03030408030f00652 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 266400656 1250 266399406 266399417
    0x10909110c010507092102130207020d06090302152203110708030f0901030b03030c070509100503010e010519060b0d0203090708030a050406030506040501051806060c0109061508070501020d 83
    0x4036880320255040358451000c040080c003440c00c10110003801c1c0c80e01031048031450070000c101580022112a4400c0d0891b030002c0545203042600342e4140000d502c1034500301d03440140c03d410030340020550b028080c00540607401038000c1e40d00010301ca24080d607005181c4036002e5188950b42850103007070052440042e0305850301040c42c5501c12403803440c10302e560704541076910020601660890322180141404030082c0da05001c00e00443d4289030b41c9004400040040d50040c003c148001e0409042643d40080d242c2d50312403040d907440340802d0842e04802c00710602a51034100304105950701c2c0c020600c440848400030019a07142c0043c0c0c000501032241c2c004c2c01942c002010503080c0c0e404004400103042000c0603a5038806c1031103000343c90ba5119101e803802090801c400588240740501c2524100c0d00f000c3c028443c0c0710201240c3c2a4501e4004190130f41c4020144654001c60800744140c00e00755103d40030001d02692050350001507500640e1041da1a07038400c4000344002c0e40d01240804000b006e50504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 266401906 1250 266400656 266400671
    0xc121920010f0b120d17060f09010e06011706010504050d050109020a06050a02060a02042411011d060f010303050a051e0703030507030507020d020705190b04090b090f06010909 77
    0x151400c03600c00c40244080d070070602c1010482c440b9510002e003a00c012113002d804114800402c0e900c0e06400544131022800742c09a112405080e000302544c450401440c190180c4071001c002004c6110a03002003800700050401c101d51541c000c90307048101564070b40e040605180800009005101d10701030f0794002c02ea003800358020000250002808a5030040200310701c40d03102c1a00070819000114060f0041c0f0990000c50040c008030b01c00c030340540341890a48401000c02a9904603e0b00609107003034100030300300340c203c0741d0800c0c20310504004a600210200e540d0701142501460144040c2444d0401c1144000400029400104031844ca54036403c0540d10348440031030781c0c0d04400c1d4120708111821400254107080542c036034055032265416850400040d260524101ea491801e6041c900c090792282c0c0e400e111501c0e065002200700028080f0050748191181410305081c0c00c55405031090640712f17159194145841150716034404040101c2100500d080000207150044910803003111b559a66034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 266403156 1250 266401906 266401937
    0x1501050904050a091b08060103080931140c070308040807150902040f05090c01050d1e0609061a040918050604050c0103110a05040e0a0b030706050c1219 67
    0x3035400d1003000801c01c105514001e4151005040483d004844240c43c0300a02410400318035441d50903a444a0001c0c01e40307a00359541c2d440641d01041485501081480580c0345901c80d030103e40d055030514610360207002c0c8800e400c2105880b00c0b203000500300940b000030030008850410a0b503c01e030750180341c44c40701130311942002d807079034070071a40042d2034070822144644501013a600210f1085200381c034100007900b440c407501e1044400c1500c9480c0d240d00001000c4c0100d41c45003000e400c854400250015600e040310000c41c0d00800c500c01c80c1030728030380c482d042049a041c992048000130207d8808a0700c400440110140942c131131405040f80c107941d1b8004034161950401c65400d003040d44041183c0090a003400d2090ba620741c102d21050009007030800c1c10601860000c2031340c174422895110301d0300b45400c0c00c1a44d1203141d4000c0c402031986130ba442888542d81d81c04c00c05000202619215255906c103110a90b9041c101045542235026100300403c09526002c900c44041001c1c9528140c4084000c424 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 266404406 1250 266403156 266403167
    0x718050c0f030109060303081503031204020418050a051005070c0f0c0e0f092802060702180c0a030b030c0d260f1c0903080708100b030f01080f07030203061501 70
    0x2141041c01003008070000c02d24910070b52103c4203480c0203449009241e6508418560110b0801d90741c0e43d05908203000817020460790101b9103070090f10041010071100c0c00344070f50f01070130400a90243e401d980034100c00d1007800028403001500503c0940c05020034602954007074004001110000d2010300702ca008242441034070b403110009094450048030140c02d101851800c02f640c2903074030400030302440c0c4041c400c0340079a0345640305003601c58550100c00030b0309030204040c1c0c1e0030041044e80c100c42040c000120f82015a1005481032400840d10340c2c642c04450310040c1151216614940258007414084029941d4110303040c00c03803030380000e4080c3d83c40c1403065000030091b1280050085c020020801c450707180100da000d4200001c032219080e5140321617005070020fa840031540034000c070300002c0100c0e0689100380c12442d48070b4a00c0d16080207882da41d40e0b150480303920450310382c0d0080400e040184590041880070610682108005082860840e00000c0d03d903100600307002e0002003421203030302d11030740900c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 266405656 1250 266404406 266404417
    0x8070501060f0312020601050307090f0b06030a0c02060f0603070512031c020a020c0a03200321030601031b09060806030c040f0608060601080c07061a1002010606020f0718050c 77
    0x1800030300180c0c0d501c403003845100001e40011140e942c84100000101407002501034101c0b8030060041c074000780361520141c028117460348101e120700d0f10b502d9120016216200150700440302c002d400185100480070003414620007a04000b909004030342404100d07030f00050240151201103d0610300c040d00c1c071120724958071590b041c091103001c004000501e503002d19800f03401441c0068090390940c40b007030000c00101c40e885000007001810600038000c541c05c400260000c03140310103401c8504803110281d02103141c0145001e851200540001007103a02e503814040d618480e20040601004210314150140903c00640503a00130032018800050081d40d0801c809006904058000c1190144500022010b45498020180d052140341c01003551540300e030b0003441c429880c4209060400c90540d45800190000d0019080c4280c05201950216a41c0c44c1040165401c1130b0000a0f209151150203410112000e03014011900108000c01c4642259007058103112095800003038660396141c03040440d8041c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 266406906 1250 266405656 266405663
    0x16051504080a0b0105040e030c1c0c0b04080301090c08040f12260906090705030304060c03230306090a0209130b0d05010504031701050f0a060c020d0506070906030e010207050d0c0807 80
    0xa030002041400143c0c402607040e5007094805100301ca440c01c040c5641c0780b051002403c01076006100300201070a00480b0a0050304803880c00c01841134440c0c403042e60202d0140d80503500c0250001c01004002c0700b612800000b44c0307050400950380e01c1c0945603111010002d03a00584400b2a040d120034071280b1410844800c0d9000c1000b2012140441d0702c0302c8100c000032a5109001d11030b8002141041400240d0300b000c41314014001c51401e4249102165080c805110032010b02292078030721414000c2450b20a41500440e810703181d2a440c0003010800c4511002e00074a2010f8030410a0301000d8445480c22070580540b02c034049079102c08a4045100011402d101030215440e01c0144802c05511007000084a0724031403011601e66221410003079030304100160158490070208042048601841c0d00c0c040e1540010035519400310651202800c1040c00c5030100005102e4502c203000340c54143c0f0400c821924820021400c01c0441e0ba1025a141d00c082c40420900c0b60180c5540100a1000d0443d20300b190f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 266408156 1250 266406906 266406913
    0x60302030411210f12040323030a0c02031501030201120c05070506070806180906160201020d060e010801110403020a05280e07120e060a0b0f0d0506181605150408 71
    0x45040f01c2403814208079206001d070340549802c10038403030000101c12150382e107000c01107440c003460355841951400700b0030800c9008003070040c2ca04400d000c051002e00781100311900c0d8002c50740640d1042506140030055188150040c1c00c0050000d40da01c1500c4000c80741114500040d0038080c01340580da68025540001c0c0640714000801208035880b0003803900846003520401000c011440d04c44400030790032034880d1030740da02c00c400042c08107404403c5141400901d00005181040c0380c0b0141080e12600d0b0481d601ca002800010041088240320711064003c400031180c1c2041e095134000b0308020054490035208000241d01d200480394101034444203c15136103c04c0e2052036650040060f1244111140b001041690800e10486c03a00c600030a504d60400c00060041c80e51110200c100800c0110030035900003100c0141002c90f0381340c54504035440d50080005088070b15155501c4005841601280392139600151011390041400c0e94910042d10000c0b034a007600b10143d0020403005000b940c1c0040714621 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 266409406 1250 266408156 266408179
    0x30e0106051903020a060206090a0609020f10080405061006051804110c0c1f080402010f020c03030d1d21030718090506100306060c08031305010509030d2004060302030411 75
    0x1042c80c54034080b240f099545c9080c07140d60754816a110001110140081e401902000b030010308a9400702c0e01040c130080c142c0201a5a550100340341800401c082c0c004620044140001d0020412a50b58800d00078440c1002081c10030500400da400307060480581400207695900c1c03156220f0b04031404003024a10319907125010919840d6564500c00c1120b40030b014100c540c1d00c45c517100d490700880081a00d440da400e464845500454061314002e0701c8a045020b203400202c40c0369000d100600c140c6c40c058034041030b07645c40004492001d00321800701d0503a907403003d00f07903d1140190300c10000c003008881841c50340784e581d21030040e40c00b0025103404528080440c038022840c9540c544c0700d01c1c05000c0564020b2099140c00c04144c00b02c418602412001c01c414071070810006008070011a4400011a860304080c282030b9030b482c0c2950000e0310851080c0d0404201c41c0019500f41c8100b411103030801d07c0e0410340104500d21010b80c0d00c142d00640041540000003c0e00f0f100c80c1c20303803a5005120242c100030002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 266410656 1250 266409406 266409439
    0x1e03070504180603030806120a0501020c07030606080705011e020a05012306180604021e031611031305010c21020d090f03020303041226070303050705120403030e010605 74
    0x1c0e44980600c014000c900050300000c14010300c40c207426294175440354141794903138204009017180d0020a00303540d03205034006c010021740213001401c4d103200301740300604142d421361030701c0415500e480e0403400e030341d50065008005a0f03a21081c00d034100c40301c0c20500011f0501000b000c07800c00d015480d016184e5030038000040c1a044105c11400a110344407000440d85485100400088142c50004801400c0d4010007040444c0b410354014001c0304000710740c007801c7c81040604c010881c0c10450f2003403091031103410f61808840e0801c1c0c000c1968003100015600d019043c0010220b8400c01e4014a410031a01103500e004000540307030307200400d10b030b200b20051069003a210000c0d9504103481c2c0144c00580510400100715407400881c805903a4000c010b58102070400329811030b690b01c0c0c490103071a008402480c000e40b00320403007120304419500800c181c3c4d445445d82030180940e14003900c001d007080303810801d01c84030078903010348240c210b035240c580414864048039456015182a80041c0d5010784110b0940006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 266411906 1250 266410656 266410667
    0x606032d0403140c0a030302030a0f0504110901082a0d080c0c0307090b010c060c0302070c060509040b090f041410151805040c060c020a15020102070c050f0a03081e0307 74
    0x1c5100b0b40c1c59060060140c03000c119940a203036840c8803660b20495410000902a401469002c20300c500005003440000300032000751141030340d066400020f1042072494a0030415038081c090044080106500414000641c103041c0040079240040381da055094040c60795801c501c001c119401c04003541c0c81d130a0100c040c07174982890b42c400034440d1013003800008003403e0381d00885103002416191070705400215100c81001c1c1c00510860020036a08101c000d000400510002c2c014041503521192902c1801e0240411542007484a6100f130402804101d040e4203001003c07540554846000903080002441d4203103004000e001e482030f00d0703090111640882100c142030004492031442400d8002e180765070f005080b28000d640c042c0c8a10b1020f41c0501c01e0b1030040e0442420607101411202c80c20b40d0b0341603c100824a004c001c200142d4000600314188130411044101800742102c2405414800000040d5107020350b00c070080c00c18a01041d901d140b8580c014290400d080022080c60b070368500110300800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 266413156 1250 266411906 266411911
    0x619030b041a0910080a0803131a0405010b04050c040506180603130203070504231b0a0c110307060207090f0b0409030504081c210f1e140f0606032d 65
    0x24003c101c0061803540300d204a40c1d0849160601401006d407458071140100c0c0d0008081c501c0c000d0b42c0c021a0b0001070030307003a0480400e030100d045429090034280742c01d07404c0d65907400b0054815800c00050026005e9194200c1e0f04540303088903107030380d981e410301040b40f420307450079035540d900c200c004c400c00c1303100c801300c007568140c551080342a01c54540e120800c00040300c50350464507419480c1c00258194040c58845210b800c003c1c2c1c1424400715038241d40c03a41146a101d800e03644001440c0e8a4200d0800080c1c4070400170700401107000d8001c0030b00f4603600a68400643c810a41e14988032a05c41420340050350003100c0390344024205204401642c2030141c0306500511501c00517202c0c03943e0042c0206500d0500b1940e1030b40e04c0c1d484200c4900000b04a82c1c005156404414045135503003081d81c9451702c0c82c454000d0451425101718003c81c0078441c10400c42e01c40e20b840d560040c0c451410041003003184241260301280031501185c8940b100080d802e1921004100050824885c100c0540c0010440c001a807 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 266414406 1250 266413156 266413159
    0xa09170306031905100b1309060f0b1e091009091101020f06040b0c3402040605030304051c05011104060201150f14090a18200603060619030b041a 64
    0x2080005030318642d540150010f00003810603080f01c1c00b4500f001e03030710f904440d106d400c00a190405204118440b501207441d4100101c8070351f0b5941e03001000c080e45038001d01260f00800c07511a850100140c2c0a049104c07580011148500400c20000d0010094948a00007418288908019140e41407420b9030440c1c0300741c9540c0703026200e81c8030321800407000018035030710996010b0020718054452840e44141a04104414804804030804003420301c40341c0c4160078190303004c10300c0340f00da40305050042c0710443d8820b4002501a4004220a02240d00c481c411030041c07010402020701104a5424518018400c0d554410309080340058001040b96054104494000d46600581e00c52641c07171948181241c075511601070b544c0c000d0a1110128600800c0c400c0d0302106c44031002c2900303080041107140100c3c01c0c410486403403034411940c1d8094400c0e0056910701000645009156082007000203445004200e82d5020045400c0181c4074528440d030894800a58043d00c1440400315410421040e4000703118000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 266415656 1250 266414406 266414413
    0x80301080c06030c07120c201f0f08040809060313060612030c0b100317070c0e061f0219031707030902010e01050a0c14150901050c0a080a0917030603 66
    0x71040d41c9000d0701101d019400e48a41d040c500640c030b540300c0b01020398101031202440280803820020501003400c0100c8608401980c00b9403803800400c0150b501c0154500308114031081c04103c2280340c01038140c030b540c11010700380078507151b030b851034a95042d20410360010f812050203c01d01000600c25840c04811a105030f00500032a5150b201020303200043c080060005030501c0008008a41083e10068001d100c114504a81c1c0392280c072031300314515400c590000320740b43c0003c9807414070694208010260124a0252509040c1000090440001601014690104200e4032032200f4002c002c40d514280014140524040c05070401400c04080d0303411803100c40600c02d0014032032910910030b80501603416111203c11220886c01110560000d1903001d080c020900c0c0703240081844015034100311080b040c020f100d10030022401068190b000b50440101c1c0e8140028000343c0000c00060b601e082e0820b182c0604a640c82100c071038040d00c1d11003005000c100e02400c800c51200c00c1d1200451103001c1c140c01300d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 266416906 1250 266415656 266415673
    0xa050c0f010e0a03050315090405030d272907091404020c0601090e0703050304031202070f0609060c081b010b0a060f0c02102001060503070b030f0a1d03040308030108 73
    0x50a0a80342e2144650401c1c0d044140741e000001d000d0806150060b20444001c01032850147c0468203100c0d06450030780b50743d40042421092100740f4098031070072075207810142c1c0012040c028059406502140001c5c41c2c0c03184c00d040c400c005010260107041e20100d4080c060b840c4e04068001620300011402840001c1903400502903c5003094003c84a42e13140310001042161b281945100040051000c01034041c028494000f01040042029002850103440501c000c9142640007902c3c2c14810f52100080da00b80383c2c01005600e820002d40c4040350b1203400e140d000c00c0020724152010f481208003030444a030100d080503154200540c4144109001035806c11602600c2d01c40c2a00c2e6030724a0a803140c0010822a0240c0041c103141840d0740c3c1c0e94405062445101d004000c2283e052903504400c1001342e0b55135001008686000c1040790010090100310314611b0502080d41002041c004012000086e15079100c50f00b1494016850960441d030f034030903a601e880d00c1c0d16100b6070552003072280790301038420b0914 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 266418156 1250 266416906 266416933
    0x604180623041e020a0b070302010209132007080d061e0b030c161401050103210305070804031b05030c01020d0b0301052505070204050f160e130902030a080a050c 71
    0x1e032a030050342c01421850801628008416074410300c041c2c226041090200002107200e8080302800c8618445d030005a100c0c0440401d200800c8800b04800303041f1800d218281012407402c0041c00d441003500c070561342e620310312400c008000d8440c7d011b00764940c500c2c141001420780c115410704180c8181200010060310b5030b401c00c891403400190b42110b90500108085000c2c45100e10079a00f515220f0240200c15105400107d804c65800340d000f23503403605803003034094624282803a029035585200d040c108110f0402e49802441e181005000400384190740c44204400c6501d01c5e545100258001d045a80c1d4840641e0224080d40282125a40c12800c1068200309841d06024082c4210b0010403011740c01e085000708444050300e115545410b000017040f405015848501809102d1501c03599544c0c00c034148008503125403102201c1d0241000111542c1d1003055455400c581400b11100f100840c4860150000a04000100c8030042c441c0000080d80f01079140c2150240210503850000d03120146c05152 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 266419406 1250 266418156 266418221
    0xf08210a050609070e04230603070801020408070905091903020c0118080307240609060e01091a0603180109060c0f14030714040b160512040513020306041806 69
    0x49882d9409441d0700c0005603024411402d40c981c0000040001c9685845a0b01c118150703c0e191401c07000c10000b02040000034242000744400a01c0c10304000c500e02440c0c00b400075215510380c0203800c0019150004038100610801c2504030a2400f529000c48080062038065a6841e50040490104001e841041041c48103100500c0c00c581c14100594501411903591070f400302c840455019000c0c0c929210002e5440c1503204540140c0b0904000241c0c4034207209800180e08070503842090200c0c00c2521401d100040940d031825075240c00d9651544a45511607a60580d6200413001a1340b0742c41c107184541480007a400003a4802080d0b2514400403074465070448800c80990306010710345004001140d40310344118241d000b1844c1615041b81842d4590345088a141d200d6040c40904c1c1c51201c50300028400280800072142114058052074140361138081040012407110864a555002c00010055140d075048194401203003490003120840d0b6141c8113008000708a480164000c0248504401030344a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 266420656 1250 266419406 266419411
    0x1501050f0913240f051504030b07020a020312090607060e010204080111041401090b190e10080403020c0306150d0507210317040c14150c030a0206060613050d0f08210a05 74
    0x395900c4c94114205824040c889902c1d000d020b0800c107080100001041c040320300c1c01d0103000142d014154103465401010300e0240b00d12808403825408104c840c0c9955540000c4481e41548001d011a130440019003c3d0300901450b4000d107459400c001480d43d0302081600148113844200031001c692504003801100d000245000f0504183c50420020600c1460b500c805c444c41c4243d854014004580d80700403035a4001c40003900008500c64800b4401090303018000400000015001070100c0d00e44041c0303801804a5a280c124007402c0032808000610909000307680140543e041d42504070102203135501b140f880000c10540c0059131107004ca0201e0968158510f01642d08591a08002424500260001c0c441d02402c02e80c0000f400d40fa00342c0801018029202c81101c2201568075100ca00c4c0020f420030031f008012921500041100c80f0401e46607020304820f684d801d44015900c03254038980fa08202c0c0380f07840e01410404020a11540d40e810040300b851300140e940c03080100503102d0304508030986606 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 266421906 1250 266420656 266420669
    0xe04020102030a0804050309060d0b030d0804050712060f06080a140303040209161b0b0a0b01020a08030703020307110115150c152301090b0a050303031501050f091324 73
    0x10440c00c034401c1c0c8a41d481580003801b607402e50b80342223566000100700c0c0d4010a0b00c021403980b40c115210180c51700380724a11105205e41420306c254942941c545850300558003c600702110785015400038003031290700000003c0d0201c00100300e52600c0c4e8240c81e40d038109010f0126004030042d17580c4440c0e01d0020055030300850b4042c00e80d016540f12156010504814580480708110514a10803100e00d40745540c0a001c500420380e1074001c1c24000022425105020080e905550003580c1d900009100841169070000312031400603141d4a031040110b5080d11300b18100c4403075609020340c2080c03940c040c0d84030000310751540b01e8460ba6800d09002c181c0311145645000341c44001000800b5080400700e03003000d1800720210381409452020b0181581c030441081e0001c540480d40d6000c030103045c0c11300c0b41c0b15201401080f0001e600314503100b5091441c83d21a218030904002020a510003021103040590309001c50040411641a00c11402d00009040808080e54030484c0441c41c440e1030b2280200c0b40056601 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 266423156 1250 266421906 266421913
    0x7170f06092505070f08131a0403080906091903060e010b040908090103110d0f0b10030203040503030703111b030a18140f06040305011d060a0c0c0308040201030f020a0e03070e04020102 81
    0x42c202d10035030311030300f0044080c0da49401c003480040003c1c2c0807100516440e10540040c03000c20341003503662807011141c002e1080c00b4920802c001d001189105041e6490048100e564564529408000c01d404181d9010819107503000800e02108002d002c0d004503000c548204002c20007100c0d180200816102c0c94840a40180400c000b070244a501c04c4c0c201d8003040c6090340d036107440e1032101c0580da42161b90305100d40c4c84e01d07a40e400da100524036184000007018055071805600b1030030a515071940702c2c407014150303c041c103a50344116020b519404047d18541807809009802c3c800501084640300d50205035000c002072941d40408080b2049c2c5554001a20b0030000150340d441d0741e04062080010791800a02c0c1c0c070101c1403100200146003401204c96240045450b1041156002d844602c1c000c0080d1000305410304021a00c80300d2a401302000c11a41e4240c60850090307181c500040e00148004c00c0441085400001c40c141110f8001801e001111403d8080b2509583d40706803040c030004003694005d00580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 266424406 1250 266423156 266423221
    0x4060b0405040f1b050603070203040303180321140d0209010f080c0a03021803030c01090210030b060f03040201030e0a0b0613110d0c1b11040f020c0d030507170f0609 73
    0x10502e1200e8a0703198135442c003c9103030715190800280b2980046a618005920024080c410140e00070204800700c0d08c2051003440940c216a5002d00e0485020030400340c0b41440c03407100688034440c00445000001100041e503444200085800103580310215582c00304540300e90450310607224100341840380c8042c078140e0741002d90748001200650303c004100e101d9003940c03105100710350740c0a200420b00102c245000248140e02072040c07007401e695500000c820b251a02c2c6403551507407182c0c411141030000401c0c0342952503075140700590051591180c5140c4034410001140100a0348020340c1380205000c0700d512091040e141448015201e42d6100800c91017000c0c480c5102d03001058004228605850405400814402c086000304c0d10f401102510b4a0f000d4041120480c1401c1c8500c501091031a0000e5103001c50145066035900303081c110500c01c0546e00c9001450181c0f050784220340240c0240d042080b10304241402203200b80302a076180d4490400b41c800b007600d6121207044070b580c0200d500061483e12 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 266425656 1250 266424406 266424413
    0x15170a020420030109050f070f02030d020a170f190b061207090b0309010c091a180105091804060b0303030f011e150c12021f0f0b09010e04060b0405040f 67
    0x280074070b032400045112400d0b0200204030034034001d14080c004c81400026a49400f520a2880100240168007072043e0184000c411643c080122000d22543c0701000d6900c40c9000f03000c603240e5000c4180e001303900d0103107428440030300a00c021090003949100704900020340c40b81114030840f04454000f43d805542000754013034104034410256400301c4141001d1031819601c02410005510841d60004581d540318800c03204160000808c101900b0100807400e50802d8440c1280c01610405e0007065840300c2c2e2002c46062a842a401c54109400180501402112002c956100f858041e01c080361200c0c00c02c056035050f4100001568810181c90011510303591030078507840344007040c080c2c910b01410046c50000c00c0340d8407070000420610402d6038503025801e02c2810300d0f05108100940710b001f103401c1520b5061407010b0340b07090108143c100420021b62640d241913940e004210b100303200364002c00c4450001500140051420344200d0207120207200d810f08101c101300840710200e800428808001402c10b010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 266426906 1250 266425656 266425661
    0x180d080912031c1d06070f080f1006120b0618030111030c0301032406030c080d020706050405040b031c0509130b0d060908090d1b0906050603061912030315170a0204 72
    0x45001042008001107801a0241c5c10060100c0c0c0380300c0800c40b000341e000d0020340d0001007e5401981031406844d030b030038101c04482034004c40d44640c00400040a14016601143d5842268011001010a0740d1074401000d03d100ca9140c94464a22952070114003124014092040780d104041c0c0a40403451030b82155039040707c5030000000000c8080c1c140200440f006602c2c411503010358000e00c0500591850306420310729050203d000401190408402044200e4014003901c0a81d03070101c5001c01c242110f103012070714140200101c00c2e641c051070700405202076004002090069000c4d1442d41e5161154001c50040d100c0c1c44140c65003148103151001c0104001e603200201d05849071446070320b0400b101c00010740841000c1401d445e440d0601030f251841e02204445d52006140c248001e0269900c9d001c0000e40c0d5000041010703000c1c401854811309014030390203802002e0701e00c2d8600d42502c25020300f001001400201146440d0344014a00801c0c10341d030070a040c4d01c0d04072610000300002401135017070101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 266428156 1250 266426906 266426921
    0x3030a051c0908030a06061b03030c141308010506061201030b040213050403020c21070e090703050d110721062d0504060606080403050a05180d080912031c 68
    0x395004910089034105150b40940c010729405409195164100888010101d903495400682031080342c228100c0c0c0100710003011035800341c05040004680e00c2100064416044030107270039101540010b01e08041400c82600101034401400080281c0d5680302c051010a2045628a1100b0300442004100082c034503010194002d00c098540c2e040c04820505100039250700b40c808030023581000e010702005040ca22401d030300e03152058260092003050b40141b1500c940f8980a142d0800d0301900018950f94400c002c11002164003000311062010b184100420150305004251450b001d24200001d0b03a00b00d10028078840104003282040c4410b850ba01c400082c480400c0340c80040c03c0b804a00001d00b0f1066681462109410f5001f04007480c142c98803034101d484c1504071a060104074800d100210360300c102592401e0320315040280d5101d030900148a1900e8000854683c000b4040107080d08214040010b040b9840042d40c1d460020703409804016100c0c003988600e0425003415a003d03031020011a000241d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 266429406 1250 266428156 266428177
    0x612010e0907030c08030910080118020f09120604050601050901061202090102211201080303010608060d0c030609030c060534110d030605130501060f0f020c0d150e0c03030a05 77
    0x100350541e2030b81c40e403921a805602c05c480c15040072422440c2410501074030520740319030b0318103c5055810400220a505584650810040c3c0d01240040b60b20080340202e620b51a0024911600d072440703c0e01983d60340d502150203c1c0d0501608000080034101400903905a400c01c3e100e0540280b036401100009410400040b41180b242051074444081d0b41c140302881004e0303801d10203585092604059120520607400f8115a5004200400c601d41c2d12030b9050780c103d44225440c022010860074000d542c0b248a07003020b80303420b1600dc071801c00c00d600b043c50400d00c144600c10601c200c0c0e460540007191035642e640000d100c091402100d4451251101b400102000c641c00d060795114503e040b82e5140c107401c101c000c0d0109a86007818071040c507000310849030150303180c4401e004a60401e00300400c030b815000c0c1010b0a11580700b081c81c1a290080c84041c001c5d410140101c05003150905007640500c42c000382c42c20702e5a14017000454228004284110307910300290041d0300d4080303041d5041703940ea48003918a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 266430656 1250 266429406 266429413
    0x3030506010c0210080603121801030504020604080321060f010f050f120c0304060b0901031a0402040207060e0c0f04061d09160807030201021902090a0e1c0513050612010e09 76
    0x1001a561401a03040c641c0040e61703292110f1602c241810b26141d0f28111981c0121410320414080c40c0c0d4104902e541500d0a18020495445034808280a0f0203241c12402641c003002c110310202c0c10060510103074154155034060310688070601803081032281c1d0070080740003903466055400c00034014001400354060100c4c42514014040d034549140b841e0546a40341214000001d01052043c1409a803103108412180e842255156503134070b0b0141c03100c21044442d0b2b040088001400d542d02c035415241e116421440620401d00c10004103500c8a0b00d003c0f2152041c0c000890200c1d80d0b08043c4100d10581e0101480c00348640080d440031f0100d100020191021403103400b0b403a000c00c0014892800c014403084008191181c29880060700b016050400d42140b6030b4007150381c102590324102402e410039105040051a074190034042403c0c002083d401c444800c0750215180c83c4681d202d0010000c2d00602803034100342507140e82c200318a030f10410b1158030034541c00400602c124035091b130000340c02c0603e503800c9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 266431906 1250 266430656 266430677
    0x10908032d07030903020a27090303020d110d0e01060f03080d2309070815040f030c02031b180c2703060112050105090c0a09360c0b13030303050601 65
    0x1120740d588142c6086000441c0540304104508055034904058160b1035000c07400c0204811703c442c020110201d4030008941c89181032018180694100c03185400c194009000d500500b001d802070301e5008407001d0000511340204414410418800e4009860f4480b50048106240d5120141181c00c12540e084c8840d68900c20100d010409918042000086060b00c1090340380060026080a980b0f501041054011810100321204405860b9901075070002e80c055081c3c41e14102103074800200c0000a402d4407a00700300c80c0c0300c2c10b4064030320285880100da44040500311030000f84500002698243d140d1030092040801441c5030089030704606500040303c0104001900000c0e151210a038802003c03459a551601c0900c4000c0c061310b50b04c450002e004100800f030000108401148501c02c0542c416511007140c0c0040450718400290b0b030064080c3c6440760160b0300314140e40c024454904944105035100b00042582c62001510014a10400d018030000d00d140c600b58080c1500402075810030804155 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 266433156 1250 266431906 266431987
    0x30b04020f0c011b02070302030c10051c0203062407030c0f05010207290405070306110405060c0c2d0f0406030b04050a0c05190317040b0a030e070501090803 69
    0x280001c0c10501c030000c10030030b10580c4c803541050380c01c0e1410011500003c40610150f10000f416900d542e00c00d480000c44922058003c4603140a68201086070b44540141d401c1c0108154020314055201101c840b245e1035039080c01c282480e1256058603031319a106101c0f10011034042c20b04043d4450089071000590b015036a14a400c9074071135501140c0744815041c0484404890708207a140e04010040e8130891428161a443e587c0c0323105100041100307440d00030510b80c620060090380c0c01007001402441c0c4a10308540c0c141e480f207520159842c001c0d009034840b5203101000d0203c0c1900c2028103007a444140f030f0040240302942c038080d55001c0d0070507290500000000d1004806034400c07400346e40500400065494070340480310059018074482c0880040c8030080c1c14449088000701c0f580229000c10b486502c008001050085034451505000c011a0250b5407a42541080901004907002d50b82da2503100e2006441883e80c03401581200e50060205030344402e207240154503210034000312000308184050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 266434406 1250 266433156 266433187
    0xc0c0305010f0524040903091a030f0a0506010903110102120f1206010509100302030a1b3603020418060218040509060708130311060708010519050f01030b0402 70
    0x1881140c15a540e5000c070b40782c1149500c07a441d0092001440320034061020628804e983d0300b6004860b125070740c5d40346203004040c040c8011200030320b409111440708803545940700301c040d0811125090301a40c1900080c00302c0107a03109203880b49505840e500d10240c1181c95422224202d4002030f819480f55243d0044225031502c0546a4815101800d41d40c5007422003500440b0800a030105050002c244908a1a5510455880d254094070b180060b00e0f03030384e80400da80203002030402440500724043c800e8101e031a409440d8580501c0040721081005205d446101982400d5400e185000c40b00c0039000d00051034140c006001c1c480341e10200040a108030b48546040f82c2c03019290348126000c120b4814030030f00b0030303003e8581d12080990280c104d9103072072800541a00b100910b004844c45030740810710304050140801c010601120300880700c66140c02040602800c4e0203008503072103006038080c1d0207485440c014400e402c0d12406444904d62101e0200154080d0143e1113049611580a1207451000c1c0f004a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 266435656 1250 266434406 266434409
    0x1e081605010f0c0c050d061803170f01030b0f0c0c1f06062d020f0f01020d050105101d040b040f060302010807080408090d1a090706112b0c0c 62
    0x8a510010600d800000b40c42c20a418820b40c040c0582414564080b0f40d1018519088540955507103082564500e455001000e03144420714441e14104211418540d01c200404050301c1000c9030640780707855442070300d45030000900c00240200941000182186080040c10b50090b020307168080c18000b003100c2150400780581f4000d81140440203441d0094001030040700c1c01400903050002000c811000140000c203180302420440074250303c0b1710899544200501c000e10810b8000307840200314052401400b0798415000c1e00695030034a400404c01c2d18241054164951042c0c4030b03031500f4101070340c601181003400e82038250b1040d5204065a4503481d02e00a1114041e0030303c90004015003144005041c0ca48040d2003c410840e11108000010b1140421555400350031a20310400c0c3d0400e01e41540c003007050015504000d40034109210a00000280c201c0c11307146540c031101101c9525501ca2503a60701e02400200801e4000041c20009111507002580f00180350302c1c1540204010741c03a107072000c4125 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 266436906 1250 266435656 266435683
    0x3041712041a0703140103110f0607030c120906050a080a0615020604050d0207081f09022d0603070504050118030609050607020d0f171005040c0c23071e08 68
    0x310000e0180d91820350080c030f68030071481e0804101a0390134080100103a501400004c003a00c000c00252009aa10500110007900b402000340780c0d14061441d001740140007407482250014460300c3d0328420345000c0c905400030b0311400e1703807050f0602c06640000c27101803501810b001e00941e81c0c0d10012480d00d4480c940c609040c0440c1d0000e003414201450f200d490105070240c0c00f011902320250900c20340303402150904264402c108246544810b0403144001004c801d207000754007107a55a03026006030300701001c80310301980024060047d01210014001540300c05c80c0c031400028400c020911066014002c10800348940c0c6146020041d01d940d940c50803038194513020395247d417020040102035603040207004544452880c050800d070500c20805081d900000310807500d20404078000030f44120114040d4401010024418028150810760260030140c4001e015115050754071000900501408485001e800e2090000c0000524103c1005500300340d002c516002d0058075040010307020810030440154400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 266438156 1250 266436906 266436923
    0x50f03190b120a2a1205070b0d1407020604020603011e050904060b030714060417010b0310051609080a030305130c0617010801050f1b1312020f03120304171204 70
    0x2003030b0402044008036907121a03004e070089801100c245104d101c0d9102115503801c00d0380000380203440c006041c003459810000d907811000c02c64480514054103d0035006086a001c071351f040d20344207400c0f80c80302d0f0210360183d00424100010011400d41e012040304a6942e019560104e41c1c44400191024105071415916180c0320600c00e48603290a00c801e00083c40140e10340c0010200b0701000c12441d001d68820f07504203c020b441c010510040a4000c03500c0e82e01c0080540d41302c0760020080c407000380000d0300e0b03148091452500804160b8003c28492041e40c485500070002c03002d00b41d504074003410004103c282c4004000c1c00c0c034000580c2860301e420280603e5159000c585112050390301000b203051303001b80754030703030410701401104030b1055107440d0000c00c081a00740f0201c0c41050301c802c0314440d4103c2c80001c55400d0f43c1c001149080691441d820a1088035100c0d12409a00101952040b400201010544e010004140001c243e019007503002e00251202d541444030030401044a200111400e8600342c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 266439406 1250 266438156 266438173
    0x170c031e0607050406021203060409080a1206121e0f02090f0615030411190b18040f020a0f0c0f08040b03070f03020c21040b190f050f03190b12 63
    0x820500081e42d0001981c68400c1c1800d140440c020340d680042c0608180d011000408103010b0781300c03030300400c212540003804569200c00c03c0e14001d1003102402604603549142103400310343c0c0c205e029074001c45150800514070141c68000ca680401d284c840a040310340c04807880311b1500680300c480006100d00c1c8000400303d8145856810700000c554001da140010420070420800014000c1e090b0545224003234a603d62a1919004081001800d0f9040f82800031004a60240a20406410744088110540d0140009661b945124069029451040010074204034090802c684548100380c0c501e801089095100c8070581c0b100380c1c0302c1c0c1c001d030441c090703491001041041c280e400c00720790781c00c441c1c1d9841c0440c07618440c8012162a6010a8201c1e10304003500c5c0d401d200301030105400d840c040d19404c101035640d5511007d513a03800a2481015401290008080c000c510f4014419548010340d4411114a1a5120403200404119552001b14855619040144641c4800c0076848010020500403c0000e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 266440656 1250 266439406 266439463
    0x109080414061c0519050a091704050607081c0c03061509030203100b0102030708040e070207060206010803030f070c12080a060f03020a12050f01150e0109050f01170c03 74
    0x79604040d001c1d008640801c150000848200c00389410381e80c412000240b035440d1980342283d00c1d1914400240000c0c10801400740440407903206000381c62245041c8154140b0130f81564942d401680305140d448a018040d4001042018006040e41240301e400300d1581c1c01c92048080403105880c2c60f100000382e0710300c8140b0a10031050116110b540310741c140204214a9580000d42d18411044440112130b2104444c52407a4000c01c195402c540d0300c03116894a030b6488400401d0741a0040341c002c40103104541000881d14004281036060f2880d543c0550b10b581c1d100c01407164a850050f00d102c00300010546148003003949140c2d120160b181c04c0e0707124038042c10407201210a0725225006040b5091080c007040005a4896815000b102c0280d030607400042c13840e091030b9090845140500701194200520001021001c00e40b41c42950a54000c03480e550741c840e80741200300c520490300720341c1080401005000900800841c1000000d20108462416a142000c00d003041c1030301203809400d460a004007100c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 266441906 1250 266440656 266440679
    0x18200706021c0216170f03091b0105131401050919090f02180d0602070209010b0a080c0702030a020108060301060f060804110117070c080d020703021b1e2101090804 72
    0x390081035800c2d070429282004419002d030a134040100182c0855201d800b00103d0001616107120545500646a05e000e40b881a11003002d08a01c4208180c90000d054066000300c095a6181d42c50500410549090010816910150554060510405005114a640c1c03100184c0d0400c1c444416801d00b110f00d03080d2403905440444900b03051260050021b442c002c104480c100003820000c80350107001e21500c0c10054028440c2c0c0c0d41c042d40010200e8004a1000d101000800b01c24945071344442c85a03651aa13071180314000c00703000952541024101101541c4181400ca0700294001c0000540a58404102a68030310711b501c184d000c0380b4804200400d2040411031407111810a091110701c5059810500307445542c000d200c4030030300200d8001c0300c2c144000740003940c400c0070403448115541c500b24100a540d5800ea0318440607031200e11401c50485081c00001d5122100c80300344000c084102040410150f8525107207484a01d0001d45809070f540c070800d0003a0380c0c0a60040d41c0e101d50711420810303020322 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 266443156 1250 266441906 266441947
    0x40203160f09052b050304030b100e13060903030e01020307111c020d1409190e130201050901030207050c03060412080c0a02060114030a06050703150801061820070602 73
    0x303002600300200404e40701c01102c039810900101443c1100038501c0500c0e4070300004030700b001e0076034403002c0740c044108002415800e010703280840d601480c1d01c2d5161086d0105001c01c0b100c1c1c0e40f08008d102c00034000107006070070a410081c030904010520413415081c40c2d0890f00201c41c048001140d00c1401c2c0e0024405016440014030f030390520180142c801708c0702a40e01c5601008003c101701c0c13016107000c1c0310710f8a401034600d02c4c2401070015400000b60980b4861030610b900400c40c1440110000c940030f90818203441d00c3c80c96040c2c54450038810910019030094100c2101500c0c14050105120980da03401c0c030405115902c21511500c90b40d0b6800001401401c0c002c1c41c4800d110420842080e4850300040c020781110112000c2d40f041006620100c2d05284c09140c00600003801c1c4018003020a030582c2080a40308503407030303007075450b140d54500041c2031702e0061040c1c20800e14564449104c2d00403c0d0070104061403039241c6080c1140f860315068030182c0c4005420b444086d4003081080c1200c218111210 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 266444406 1250 266443156 266443187
    0x515040b06090603150604080d020105070e01020a050a0201050906070b040501050405150f01051c1202060603010c05070c141c030c0308060a030b0a051801020d020903010b1c0f0203030904020316 85
    0x6082c03020450201c1c04a1101410034540d035810001300d041541e07030340d400b25009000d0850a8030b00492100002901a0000ba201030f00800d44580d00700d00036503c000341140c101501300004080c040307140d0b00107507415407050340e6080c0c00c080100401c8000c100103034209801580304500024032803420342412410040e4443c003601809131080c050185a24000c0b001c14151a01118001d214544010410510765941440200801075580c50314034520340114090344101410360082c406581d991000300d8041c8540b540040c4034a40d0040203222104041e4484232228901400004214504c003941c0c42110204500c00c40014140042c03940c10075600c01c0f0900e80150701950464011829503440b84405c00c0024000418140d5602c0003c40811804a107000c0a440305070085541301c2c078520041029511a51005004c1d40c20561001c005040200e90a2882c0c03505500200040c10290b50380c080e2600e40c1c40c8180c0e418402403004040d259518401107000f540045034085015003c032101034070003027451107244c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 266445656 1250 266444406 266444419
    0x111041e0b0301030b0901021b0d0807030213180207080313030306080327030703020a0f0f2301050a0c0602030c090f0909030a0f11030307022109030a06020a02100515040b 75
    0x820507241544160380c1501d03800100c0e0102c59448140032070090140c5000083d24001c400e941b0101240081010b02906100e070303887c10042e81e51324900740d050b4880d0b0b000700720a101448600701309008003503003542c0000140d054003615208582d1100c881c01d030802c0d00e107515204100b4070204105a0103100c3c0d0700050602c88061824810020544105042594414008007200b01022101583c0070300c039903005141d00900d0b00404507100c109400074086a0b01481644c0b00e003420004c28491000142a085120f011616801120606004558036081021040d0900c120800c0f0603000a1f03150000d148107601141a55807507443d184104000400c400410501a841d4141401444280402100e0102c80e041c00c03d04400d83d207641c07040b01c0d60b942240038a503290102001303000030a0b5001c200d1310242c2c92210320340e10200304030b400744250b0f600c00c401c80d01d941584000c02c040d00250390303178002d060818028015100c103501031701000380517124101d0b2a03a18174986039a01c0d2074549413a01c280c0d00b040e0130a13610f1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 266446906 1250 266445656 266445659
    0x1f030201051e090d0c080d020109020d030e0d14100f02031e0c04090e0c0a06020f03030714300705040308030606070f051603020907050a1215080111041e 67
    0x180103441441d9000a0320000c00d500e0003001c80b0380e10704640310302c8406008038813100218213141c0b02170400350284141500038440d00740d03419841400b034221100d80045c511114100907076010703956400008202038000224403202c83c081980218040034110f0220094696903200034050021078451118440c0d40d1403061051120090721008402c00002c00c0d0703100400c5c1501d5001134542c2c280140e500c850070b141d0810f03440210040011842c10792420003030b41d608940944550050303864a00050221100e54400e10000310501d10428040c0c14268580d20707c20b00d4030350b403410501410f821030710306461034407100704424200c0d07404c1c100c07002c0d0b00054a1400364100f50035a074035140948401b40c0a5403089502013800024421000000308019901c40212081142034a209200701c099920069215600c3c1d48001801c81e03000d841120451115903940c07803071409000311104000c19492000403044071038440f012a0410092060b403082e000400303c0b03e6107452410210010461100c521a005c501c4660710 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 266448156 1250 266446906 266446909
    0x207060804050619020c030f1c0b150a1211091008090703020402130e040c031a0f0c0313080406030f320a0921020c010e100318021201051f0302 63
    0xb1a142c0240c0101c02e040d5135501c0c2401c1010180c05010105203c500000401102c4900103a00402c90544010490000318054481210859104000740750708444082c5410740d4004601c0000e042c41c202c08d0030300d01c0b0f00118503108401260411500f0540c8840700084030070861910010610500c81d00b440e00340010320300300c81e20301c0e251100c501c0024040d075008151100c1404200c00041c1c041c140c01c40d0003000b180742504004211114038402075400785a8176030681c104540d1740007400d1081d505185100742c241c0740d44514500c0c030381c4028180c1c1d42050800b0b01c0c0034002030748038000b44010a980d5070042030b002c001d4147c0c43d04a43c402003a89034003040d016a0509402d00605c13440050003a416190405540e0700d030650030150502c203c00400c503084072110144404103610541c00e00c0c0c0000d50860b071640520703800549560000c1901039034840444081004043e200f500303c2450000809071000708045070f580442c1c4c4550348400046181d0351a2010005800a50414054154403101211400610b180c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 266449406 1250 266448156 266448163
    0x1030b090d02071725170601080c0904150509031305030609060412090b04090603060b010503071d010203121312081608060103020c03071505070c110607051912020706080405 76
    0xc90741103580c03044da1440402d41014400c2e1101a4001e091114400006589244035501503000d0f03106203c00540c0002d021600000700c103070590381048001c01e0215a1103041000141e00140102c81c040308603480742c20304400781c1c01124024403810300150b8890109080c061601403130760300154000e03840750040220481000400b290410303081064240080b456040881c0c60240c150080600312600082c00141110700341e01610803640650342c104a403110210044801d84826940e04000524644002070983c400c0344120f142c0c040d05004070780c504201041c00d4004003108543c299100f4034807040e2802400700c4030407602c0d0364a000e841d01140e1840c180c0003540b03501858001c40010806c1b107a0010310030380d0003503044500d0741a03018202c03038586135540340404402303408040340c1640c1030030300c404102c030300d800f69100000c09503001c0c03040480e0407580780c1482900d4110f514151614890715140011017070081c080c2a0a1070b0003000241c1c4a2820908060300c0c1c001980d000e50104040d20301000081000070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 266450656 1250 266449406 266449409
    0x3010b030c090c091206090d1716030609060f05091302030d05130e0408030702010608060c04030206031b0c0d0e030a150e0c0303031f1211010f03110304060501030b090d0207 76
    0x31503060400380c54000c0e54a603d0300076031008a8201400e61a409607001c00010003901c944032503030846200c040f00800407140070821703020592074032030100301254591080503d0403102d655070340740000751581e5500c1c25000391421944042e903c80900201406907041c40c0385200d90150340e00c0e50048845981d0750200e5550090f8410020811001203001d80020703d003020000014a442e04407082d0504040c10021100d074000c1d980d00001d9031034200002210340021078a54401c00004800c00e041c5407070360b02400307a60350000b8850381c0700110175500760b5042001c20014000e0982140001c14101c0300c209000741485e9041400d281c8250b00001c00140020151344079504071600c41000418440608022280340401e1002c44039490b000200400041100100b070340304036244590040d0404542e030300340c0f16012003040e18010700004050420300c0c590703500941c0042a6034406280000c1c80800702000e01840703400a8a044030346a40303e8004105102410328015001200381c0094008800030000c044e58500310b9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 266451906 1250 266450656 266450659
    0x501020a0b0a1407030b19080705010c14031605060a11090607020d0212030d151805060307090603060c0815030706030b0f1906081006090902090a2309010503010b030c 73
    0x51074006070041079a50807401c0c900041c02048a1541131084024014004552002d801030460360070889252030081d00010854010783d015103085e506043c0116110220340d0419211428034008820103980c1c104002c0c001d0384403880d034030034103004149081400c0c0f02001e4001001c0c2d43c1010f890040028500b011103110441c21600c0035074070182362021038070194803803034040d600a0116445c1051088040010074200c03100c0c96007004402c1408400c10061401402403081c03450300f181502030704026071780c8041d41100c0000d0845c8c07203140c1d441c8a04401d40368130350000c42d03240762101e440000039900a942d145d0482025045c4006012090000c240c1e0781d0483e00c114810503880e42801d1206895050420303482502c041d004682c194a90301030079910000d00d210b00b00000e40900d00107140c000e4445010401d5506981d66200c24a00c2c2c504c0b01d42c0a500501c0d41158041e4a20000203401840040307802082070070118010310403108501008100c49050340070341e0007a4100860300489560204411f11031040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 266453156 1250 266451906 266451923
    0x606080912090103060302061206091b031303091505190f27090f060e070201050603031b03090a29090d0b18030a0809010b01020c2b0503030a0f0b06040501020a 70
    0x80500104d001d050300d6400a0341003803000402e03050000c01d602c8280d12806083d40c2307420f03840d05c0740102c054904080600008554805001190014204013504603003a8000e241c861240307a100c0b51a83c0890148200310700c007040d00001c1c03800345d01c95a6040754030f1003507403410005d17114116440c1c00381c4520756000107500a195030415002041101d501814003800c2c0203a8108181d0b9000115400100305602030300c001001d070600000e44a9105001c2e407885403c001d0061070a040b1150b000c2c543c2c1120f120305080250205104030005030322818076650050400e401c419170122014220655031459003034540c8901c580420107440f40382c491944207800c032a0b100c42c800300259140041c0701000d1042e000b0b8041c1c14003002401d111002d03405158039014602880c0204048010075005990f5a41403d00582c1c204030f0640703103154484203903030a042c5141000714940340300910760360b1443d095034021650720014030b40e1401c40320804c1c5860300c2100c4038148196a041e10342420100040c3d961200ca4000800004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 266454406 1250 266453156 266453167
    0x307051c1e0f06170a030206011e050907020a0b070518010807050301060e0a0b04060e210a0f140105091b0a03051b0111060106020d0e0607032114010f06030606080912 73
    0x1c42d5580700b40d00400401c540158441840d10040d512a80f03018400e40c01403099900200e01402174480b1312481d0445000e20f0248149004103004202d00002c0110040d03000700307030440c00071505100c021440342140e03a031880d80e203040f1a580315900795900004a41000b10707050400200f240c016088905481460404605034410b10002510521480c1c01400f403e030000f08000a07020b4000301008442c1c0021594280b203585418060a220008441020160740c071490621021032226240b2642160048003103024007140c1290190030359500b07880e9000c02c2c0d03010890b010446440c1109180020400f100c5c2010002e2458039000d90328008620341c00e0000030b2250580a0583c0188181010000002e041e1205503a440d10702a46400ca070040d502c0124401c0284c50205141407c00c640d0303029403503143c0803644010808004042079180c51048140340ea622242c0030140b14001c4428000c0210107841b10240307042040080680c0c26650200040c0196041802058540810000c1640400c2102c0b03507100c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 266455656 1250 266454406 266454431
    0x21190f210f0e030115030c06200312070905041a030c010f1d0105120c0a0801090612030806060c0316020f0603011203052d070201031b021504020d02060307051c1e 71
    0x11700d41c60b01207030040311424200204100d0040600d104481c0152251860f1290004540c090030481c410403140c80d42082040300d2451010301e541642004551500124058035007000c60111030400b0031407519040c1840d0a209180340412205000a0003881d00041c0704041000181c0740b4040000344100c1044d07034502010070303030748101c00b03549a00e24132507240015410a84a402c0c01680080081e030005200ca13800411220058041c5404643c000700c0d030441003043f15101201d4511014006a0303118808100816403410100b01a00d200d00e510081d8a40031441403041042e448405140c0e10b010308018801007084500c0b0b480d6032044143c1506105960310b0790140b1010004001c2c00f207480d0b120103280760044d40c2c42c0d8920702030406030b0b100780c0f4100a5209a5200390800e4419034a0101c0180e10001303d0813000269045280d810610250140c0e002546507070003c1c40c05d030000c4a5940002ea0081105542c2590b107441207d014042c0500c200880e9480c51040d090f2982e4142000314400e4507441c113034524 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 266456906 1250 266455656 266455661
    0x101403040f02040c08100608160f030b1e240703050a11060f220804060c050a08070b1b07080304030813060c02071a040521190f210f0e0301 61
    0x1c0c1c9074014410850104002c1010b4007616042d10180504c0c44441c90105045000f40300703040c0645641c0650402c0d1141d01341d81111441400303a210000c058a54950314400d0b02c951684e200c0c40c00e20700d81082c444400001c103001c0569029010324110400081140081400300011614403d40501e480750790f0340c071000d509076074200500e40303005107a100d010200510b503050686d10b41e0003841c060503601110700310140c1d420940e01495402405000301004204103550048030400d0880d4425815500c1060b2070742c80380441500a00030940b0300e00c803140104044070481c40404103032554100d0049041401c1c5840d8a05640002440102441041c5011543c401c03e80681250041d602ca40f0600000d5100c0000039180c20040c8514050444a25000414803080800340c4094403c040c0c81004c150918034280d5003014020b02c110a01030080d001c01400c41c24a003039412000501581d10b5000c0034010f4a004032921010701010052960044162101280d00000020201507030f4a043e22001c950000060300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 266458156 1250 266456906 266456933
    0x17070c030f05030a0806010c0317090a0c0927030210020706060810060801110c190204150b1306050301050d0b220f0203010f0e070315110f0d060510140304 68
    0x880756405090008100c800001007500200c0da69940c01c90b84c417103400544a40240d600010081101c0c02c40940490140804146c1d00590b040100c640491107070701c50144192840c0c2000d4200c40c3c83d94450f18000c0150240703581c50840400c00e4031a80366443e2002501e40c0700c6911034010309034000a085c014414190030a0010304100c0080d07400291903034003a00c00070922841213a44950800d0100c210300040c2005507861070007000c4c05404000030355803030002c1114145104907801981ca40002041d00c4a0703207800000b030500c4603651655861004602c80d40007030079500c40b5040140c1000140490745170b4040340000d41e9030080c80b07080035403200d004900c4c00c2a0006410000081c0401041d018840041c0c0740642c0140290300030400841c600c80701d00c0a0780e14044c000c60700c40c2d0003c00c0800004000c003880c6200b4410b080800248280e440c14101c446501c05c152220441c00e01103603003100100e042c0706503c01407a044400080059402c140035105480e819119140417401100081c1400a01c4c4015070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 266459406 1250 266458156 266458163
    0x70c140121020910030b0406090e120d02130f03110907050d1508010e010209011404051f0203090d0c06030e06070905191e17010e0a0618050a05031b03040317070c03 72
    0x1125130308021001402060310030403603071041b410401e000a24810500c90410030708490409002e002d0184082540c19600400468100c59070801910b03806840303a130701e50009050408001070742d65241d8146051041002ea060600c03500c4901c081c484031640040403548204944100132801910040701440f60462550010019509010340c02c402c0c80810b500402d0070410980701c040c01d031a68005c0d00d039414015802901d820a504030398a5403034030504100c00b642d49141e8030480303180c02c140c000801c1c90394503600821249480f02d060148001130700b42c0140701c8000e0a140040040c2d10b0001802041c0003854823909001d81407441d01e0513010345e203d250700703c040d20703004042c4005a40c1c001b0340340030052021b104d4440c01c5404181e0036000503a060290500c0c801d01017008020321101d503117480000700b046510701c0021002d80d404440002c1d50074400e203c840c50081029683f620581c1048029008500003105401d8000300000c0c000100120150520f0101541c040d540720500340c51700f801d0624882d003014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 266460656 1250 266459406 266459419
    0xd0f050601060915050702061e0c03042903060f06090607061b09060807020a02040b0409050609010903030c030606090905150603040c03061424060d0c0203070c1401210209 75
    0x1080d240d811204841c100c568512a4003c04c16042e0022542d6000d41c83c00258808000c00c500e00448100c10b200101c0b00000001c01d900d0300c456803042c2890f40d4415801000c00000c040c245440ba640e015036501c080444e10200c65281d45049d0700014800e540b0351205900c6440301059552a9403110420b4950243d0b004000300040d1024980313203100c80b0056200f4200240383c9000108095101341421801450190024800c220300c81c1d0030030000d00740c00c0503d0ba4005695405050205500704181405094001e00006003404075080080c2a20640c002c41c00c1803604156040042c01c0d4080c004504030382e401e080004503600c5000b0944807240081c130f10a039000b0400b0040c4001d1007d0080034808903440740d0000c1042c040080213401c40b080c03044509002d01252079001c2000309241c0d0b071903144c207048020140747c60a242d0054040460f441a0718180050b03001042400800c8414001c20011b00612111101c10b886184002080c032141140605e038095180e007481d078003501407501683c09060005084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 266461906 1250 266460656 266460659
    0xc06190804051603140f03070b0a1808030a0c0306081c210c051207140304060e0a0510090c0e0919060b0a0b0c1603020102030901180f03110306240d0f050601 69
    0x1485c00e890440005010360042d200d03481d41c070700740010807118519801419400d4555408000f034004020515400d005548201c0344403000444a04c0114403d0300014000500c59001907401000c944040d003090748a40d2010700d03038200802d8031908200344c1500503c1c24a100110090808403401200d40084402c40d08015106201c5600300c0042c1c0882c0ea0131400002480d5280e00381203551b90105070348941d5680d4100040781c0441c10b40d40090620002070300c2214024149540d4180c541301216907030710034040d907d40e40c44041089206012005180020b00760705581441a18952107042c0a0460070030b56451000c01c0e8100030481e005112028070003003030006000e580d000a0005a0320408a61400707020b0b601e9559420b0840c040c00b001074a4069000b03504020010005441a004000b61068060541d40e80055400001d004c014051031195070021455002e110a251418001400140c000d10400021090241403d9110010b030a0101c47c1114081141c1c04c003450030150048000d4000d000c0c0c0c000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 266463156 1250 266461906 266461913
    0x40203010909050f0c100503060105070c2318071112071101030b0d03020a08030a151202090907060c0803062704020306010506280302041d07020c06190804051603 71
    0xc032050180c003070f405403039076030b49191031694072403061540f00d90340200003c20400f900d038840d00c003550784610103052031460f000988d00c03800c020409550040130003401601102044a05410704030320301040a031909004980031000b80880b11a000300900104940c0a43c14101d48008004500c0007054415005507561071034200402d0b81d104d00c45c000d90119041a051350740e541092100c00a0068055001d800c803c8011307503c3c40229030001d882c1c010502d40700e81d148004082e0303001281c00100408034851480322154410710075044002044402980c0107100104841d43e005101841e00a601401e442d6580c1e84090002d000d0360300251004e40c0c505803e001c03007210804c0c0001c541d4002c0340220200c4a560380c0e00c40400c01e83d44544001000c00d01c140703200c4401d070045810255821524541005402d15032100007000e5940044203407000b21100d0b503400c1c05810ba405024104040d9020717030300380d403800f02d14076110000c480c02122a0002c20007071304005004d001040c091110341120441882072159a80d06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 266464406 1250 266463156 266463161
    0xd030606021510031e031706031c090816090c050c0304060c050114040f02040b091302040203100503160f060837020309031b01090c0e04080c101410051e0f0402030109 73
    0x2c030201c0100341c3c07c40c4081c005000710400c1364400c0c0310040081c0b105120320103d08001c009403140110901007004000f08070030005120031207018070300c0485406100e241000950035500307240d00210a000c400c02c00040d042c0c0000c800c88058882038104001e24001038907109005080303030341e484840c005081003803204206007801401f1401e402101c0903c03100864004220001c3c1040c1c42c08003a060000290100505141e00a103a2194007d1801c3d480c05980c0e0000c00d003048030040e20480c41c01d407060014001d00320001c1801020340282d00d0415100e1030000024400041d1941c0e01e00e0b4030b42d01d650300e129282207243c112807226801e1500255145e04001c2c61442c0da80d00800120a440400c01503811202c080c14802d03110b01c1900411145101c80c82e000c111021000040c01c1a681e05100300903000c142d200811141106403051000041c400e218552510885000079200c0d1051400c0c40c0b100300200d6942c60008200b88002441d50110203171240005200202c13843c0da20ba030010300200002a080d0b940740d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 266465656 1250 266464406 266464463
    0x3080d06031a0903091e0a030305210702120c160f050a0617061c0611040e0603060f0f0601020a021305041a040b1303110102030f0105030d03060602151003 68
    0x10a080e90b0010700141c02031540e01e408590514a6a2080c0b00c58405850460352904611a1944c0071214120402c000b18039441c45c10b8006601003071002804400c1e200da5005220504000ca180002060525501c006e40703e5441c0d15008203481c9000c03e007000c0032102400014200c1d945070050b511129a0b81c466143d0760034091042501c18180d12000050160050f030110032003e00ca080b208203d43d03035130010080035001140e1125110203082804500050306482800c011011004109840c1d03480e040d050b4102d40002000180240c1201086c000700d0045030842940190b400000512166201340040303160100d5140d019600ca01099000c6007a040d640c1c2c4a103000f503003e1500c4bc490054811000800d141099400030682c0d14400000b40400030b00105d060b4045d4407034031388010100d86071545a401d981041d2050141602e406004010620b0304001035041e4444901b4140542480c001001c0d40710106180c40d0403036030220340b0010301000155809440516440b82c800340c5c2c056892071003000342c07211301e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 266466906 1250 266465656 266465663
    0x2031e04120c0f0f0803030c132c01050f09070804060e07060801080d0206040c0b03040321020a0201060504110912070e0405030d051e06042427021602010c050703080d0603 75
    0x40390100d01d01c10703403240513030a0b00e10700d0b00118034588401c40c13000744980c020701d80e0440c030a0140c080443d501101c0c00c1d4000613424040220f40c0305d5441c0c0801031010000680c0300d244a03d002c1150750a0310346a40201651003078040c24200b000340d50341c0c2008000b60041c50381628107801007030340201c2c090740c0203180d030350503218600206c8950341c0c4403c9044e41e55220940f8041c1c16030740c803d98104074500e4111f00030365200b482407501c60030701c01c591407898200061039a01d000c09a41c02003000b003502582442b503a00103083c125420311807922941079101180c49402000c03806a09406005900c800080200c0380090951107200642c1d45045d052258030f90704184641c808940c00e1001080e07104564200c948402e180d00032014006403204401c0200404036500c05107843d445240181d03002c0d18118052000030f10004084040c0d885440704031304220740301e480c0034801462046c40009003e168281902c045140c3c2070821710650344d183c0c2045480e0268131303840141204c1000408040d401056045001124031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 266468156 1250 266466906 266466929
    0x1401020a02160f080606120f0a080c011b09120f0b0a09051e07060f18030b0702070b0f1206061314090c180f01030e060c04210302031e04120c 62
    0x3c8603003507083d0614140c401c00c4140d82c0858042150b0340703000e0b0000700914100208403003103507980c0400c0c07500f04040e044051b00c00c25004510500700304020301030741c8209040da8144c1c6180b80c4200ca070103408421035016a00424034407603018000c10110111462500380c004035000d100c2d1800d000110040c0001c110201c130f15003c0c00d9181d1001c90040c1c0868205e480c01e02014001076800e0a80450b03190700940942c808200310304682c2040c286403240101c02950044e003009901c0e2425400192519403903610201202c901001040c070700e9480c0d14203807140203012a607580e41c035441c4d00b000a58140661088090b0882203c50f0005040307191406140380520284c50864495903030459901e1680200250a04880f48004c803010091419084840001038141000140e090300c0e400180c3c50b01e8005c641d164000703031000806120030304458a1802e60b101d00c035002070b8030400380c0e03076002034590003204d2600240c0d80d807601e1a11161100760007030390060200b02c0181c0b2982d22132802c104230014501d1240801c03084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 266469406 1250 266468156 266468159
    0xb2706040e150703050714070c091805100b030a0b0c031905090316150c2109030c11040915050610020606030d080907030b070c050c010e0901030305071401020a0216 72
    0x1002c20744400d040046000e4110380e642c0c510098000d41002490003080103007091814145034040b02c09820054051310748007400c0c60510062a08542c004400c4914055441034410b00051001805440c0302c103407040081660381410300401d10f0140800002000703083d1a00402040710080d1000d18418000c1c000c0500c2003000203001041240c105568220941c2c0040084d9a00110360031210302641d4401c4001000b00c0c4820034a400407140c0300c1c034042002881c14442d1110440c50b22007110030090640c2c20400005580340c0d00034102015800000f00072061210780c1071244c3d91030740d1000102580200808c02c40c20881d2060f9001442c0444846104103002040d400f240c5100082d40752140b900500101042c2e0340341f103001e880a1100414000e810311500e2070100000d0f042070000d43c0210390b503403160750300c8081c50701d0805d061419400d0070a04018510000071281c1d170305d12001a044a4160500c1660340341c1c54103000340680c0c0e802000e2441036000042c01c00304d4550015940d00700e208000b03400c99045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 266470656 1250 266469406 266469431
    0xa0501050f06092a0f0409061a121911040504051e0109021b0a0f0b070201090b0105040902040b0316061803020a03111c030f1707120b270604 62
    0x40d0a0791000d0308804400002081c01c810705140c0c600043c031029529200310052074004e2420340c40241604140c0001003000c1101c1035043c06414054803003084c00c14103034404100c0c008000c1c0141c42090800700603001c081102545074a020310300c5e00d40c4003c4244070030f205200039002c040e0710501c60340b070103185041c000640704501c40c800380601c2c1046082c0180182d1a146180010350088a07882c0854010843c4065800070f0400400c04003a202c1c11241207118407138102194140d01c01410b00b0156410000b03440c001a64407003105040d210225000115900781d1700120f402026564a1981c052007044409190760810083c10011a511592078000310000301107955034800040c84003d4001600203010f10000310950740350500d1030f1000c1e08401c0d80341200070381ca0003600101d11050380895020b03030405004691100c0f1344124024121655200b0341040d1030001c0a2443c8802d28698a641c1c4403107020456445030700c0441d074042c0001003001c41d6411078020f0032150005a8010f84124a0884040c074103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 266471906 1250 266470656 266470681
    0x80c061501050a02070506090f0405090105011d04080909180f0c03070b07030518040e0d0e03010c05180d03021c050c0c0102211305040603080307171b0c070e090a050105 74
    0x4059076000e0204a1b01c1c0105101c0c05400603003c03503034000b06166510b0090380351442010301c25030700440082550352400345114624802c030440c0e00c41910f010410080402e103c1402c403004801d040ea0707991401d95a10240c0300340c0311203540c03d8844e079000d548a42c0c032100a000514040880e0708038281e81c060f960b501c41ca4241442412802004504148a89200e100284810640050000c0c101051a00c403c004081c204091585e604010816181250400d42000d2040030461515414030502d0f004c1d04001842003030741c14021652107410400046810548240100300900b007204048a00122410101500640080c944002c0500c141e024441707403176100184203002d092700036036400c01c01341502040003000d5000c102500c50800e140100000e00307840e00d1281000840c00b40c40d009840c0e081c0b40800600600d204121801058141000e0140e10104003103110310700d0450700e800030b80ea013240f60107880c1072a171107900102070000090f08016041c10041803c1d92014807607070081080b90350740b210700c240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 266473156 1250 266471906 266471917
    0x80703050c032403010902190e0105041a1002011508010b0906040204030308061e0a0b0403150b0102070915090513030807050a0915020a0b0709080c12060705070c03080c06150105 78
    0xa0385020500c002100642108518215400900041418160768002c146000b21008054800281c0380c00208007a80e2701c00c10460141100b12414400a110310796580c5c010810f01c210544180072940f14010294002d51005080942e84e00b0b071055490384d5281e100e4000c081442c00607000d016903800140c014a044d2007240d050b2545600c0d08005030b110311003800366602010341c0240b034103502c00910072215555001160010309101d070000e50b5541c15840d100302c11407089242a15003a04005014500760780124440c02136400d166800a0b0540e000900613441c1030107503000032013840c640001d108079103811000d01c50b0214003d4851400b41d4442210880d41446803c0303100f000609411700910001103041040548514144111758810300c19446083c5066000d48031400422031100041081e640b052101d60007545003121000c2840e0454192281c0380c4034020481c00400c100000c00c1b40401074202c5c145409140c014000a403030750031000043e60345c0c680990350700c24280d00c246140c0c1030703540c4507208481 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 266474406 1250 266473156 266473171
    0x1090606051303142e0c0309030f1209021503041202071a0a090e1005030d0f0210022209090203060604050c071202030c01110d0e06100b0703140703080703050c03 71
    0x86005240d900d61208000132002110501d01400100c200c4c114107200d680300c800c1720702d0440c4100070007181c00140d007120011071035001403505040403403000c00e4000100762820240343c1014020100301101c00802484c4c0700c0700003940000342a0040c070a10a05a010318421441210301d4032800d40002d40a0742d98030001e1054003202909140600a200c244034090500341501d403c0c81c5895035110b0070f01c100e140714200d134640b20b4402051804c0086107410048104d1003c0282441d0141e440c1c2e0740d800940303407210b405402c00115000584600491100d88007080c2e402400c901c07036200940c84a86e03101c0a0000984240e109205a0300420703183c0c0b030079100c0c090203800c610710200e14011050fa550380b41f00844081c17050030750000380154404104280980c0d1511002d1f9000c042d9a03c0050754480100d80d41e0382a4829658000350401a1440f01c403410f040985072030a034503031380f10903040c5812682002c402c100358408420204c3c7d10020960030081c06405404161030507c05552000d100e06007a000456014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 266475656 1250 266474406 266474437
    0x403290a02091306060e0a170304050f0f031f052212230903070f051c0f020d0602090f030a02010e12072c0108010c020a08030a0f0f02030109060605 65
    0x5052905181d0040450580c050202d1480c110032559050441d800380c0d0000e404100481c0b03203036803646030060307200020307012594441e03483c0c01032040c01d2952800385006150044402d440941c001c2c0e1354000611064000c0103044548100004a90004205c040e0f226440381c181004045030742c03e0681e40c0d41c1c2c660b00d00c138181e280f1080c6c112030b10b6003060f00c2c0c40759440400b8403d450030400e50300300501c814003c42d185003000741d82c0d4642c048014540b80c1241d40d8030014040d00d0b1080b00340b2584e9110a1401201c1659600c0c0100800707040c100300c2e20781001130b90025400f40c400c8a100c8104500c60b009070181000456600d01840f240d00c00381a00e030b04926500a0014038040c80240a40c034183d40e208a00004e04030407580c04d6915482c0c4803101e068610707018211940c0c1d4094501816401d030880c140034007080c100901404400280195035840360071801400000044001074051b81d080c2c1c0603040104040d0014010329000300e0f81007009600a0186114080c01d010010074a28050001c03070b00040c0c9400d40c42d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 266476906 1250 266475656 266475661
    0x52509030f020d0204020d06030303020406020d0c0c06050304150e1f0b18090c031911010903080f07080c010f0f0c0212030f04080702090703020d1a030a1101120e0102040329 76
    0xf0000840c12180003280d01c282d0901041040000c00d10412010714441c0d04d00590700e504001d8042e10301111229004100301d010307504140003d0180d01c13010100c2d0301905200c1c0d200d880d17a141012078500320164064010746860100c402c150b60020b20340f42c440c0004241e440440182401c1c2c0c40503a0b1a1415039034000448402004130591281d904540c40398039031054692503004400002d0034a50312912600030311000c240c1030410b20509108020340d210b02400e281461780d02e035a5664006008460f0244070004001c20943e05025000080b101115103c2001300700d40c01c03505d00100000d140c0074a11811b0145400c407400b5405000141c1940041030b40b9907035a00319501c8203111004808002d00840d8100018004040180c031045a05401000d050324003586581d035070a50102200c20620081d042c20844000c2800303a51000f2481d0075810307800c004045401c01c0b9850040e2900075001020b0300942d490310a002e1580316040d80a007003034070320508200b00d07440c600c8403895290800d200c2045000d000848007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 266478156 1250 266476906 266476909
    0x60a0902042904080106030b100e0105010c03050a05120106170f07020c0f0307090216260703030e150709060909050603070e220b090c030a15091401052509030f02 71
    0x181a0071203511901058a000d403104d1003035080d1459a0700446000c407551041c070056645a80c4400090000380130303041120340c074000c002407a03511310b400040e042c0040041c04440c2284190120f8100100501902c2e080d9655000001c00c44d45407152003943e0034540070702081c4030703408890825000342001d034010154420000d04110841d84021b01c002d5051181100c00107034010070b030001d40b035002030350344000c4c200f00520300300564400c0d030159860341c1020310380d2500381a6034003a07810f0b1003010740c26160001c0c0d07015008803850724140d1440d500410310f04100c4100300c40300390300540c2c0f0001e03940c05030b5503080c40f5652034cc6840190781080ea00c0603403640204405004144020354616404000d50000201d403024050181180c8082401c055407009400401c1200290003008a58210441a4014030301c9100945070a000c42c070214203084d0429890b01e10302024450390540b00701030041040020030890400150074000c041680b40c080392038482c040454101180944012011aa08101402d0580344940d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 266479406 1250 266478156 266478209
    0x306080c0f060d06080d0219020a090f0f0f0e150606040306050709120515090c09010545010503030708040b031017070302011b020f060c0a1a060a090204 67
    0x38041c0d802800521000300d2806180c020100101001c0300540075641040c0c00003030801814620480c0d080c6a46c8a0110040e2104a810000c54085240000324200500c003151702901d16640c000e04520705000103500d4111895110005a07181c40301111411004180e42401d00ca400300c2e0043d62050f0180001c0000c075282d9000282e1181451422141085c3c56641203245102244400d8400d0303400b001d02d50401c1c40461810b2500b00702020010b103d20040680000e083e0380b8140200da001d000d08031080c04140c01c45440401c088030100d01005400e885083c8002e8002403508800e190b1004c3e040c00008441c10080100c4134150b0b003120b0721501e00340c00c0514644041e400034207103600c4d10483c0d00d00068101040246540509003043c041d15030f003895400010a404040405040c0c0718150b501c40100680d41c0b2490400c002c4000c0d40e400c0e413280c540402c01418400ba0b1301c005007017440e03450210030b5013401c06500303180300b10310494400411700c0d120170440c0224029401100f40074000c51030041244c1e41c016 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 266480656 1250 266479406 266479429
    0x10e150f22030b0103020310020424110106030f02031b010f08090c090108060901150b0a03050604064703040303051312121d03040519120b010311010306080c 69
    0x5642404284100901040714044254801d855407015280140304601d0240004480409165408c0d41898140650880300a01110f0000350100c4018000c645690099525404c0e0400d2403008004039030346c034180460782c1c00c45154124443d0080e1340d074662002184551044400b2010383d00d841e5200c0c01d040054504903c00b0341031013550b00c5038600110150f0344036420316003e0048200981090308000c0c00703160039102201c0d0711545c000392400301401841910400c5d02e54000d900d04c1d01080d5615848042401031003a500f2450045045000340a0308652080c2000070f82c0041c9004602070307502302140b8070400e4500c0d48020204007002c00224021a03c030381c0180e80c1200540d07410101c0c070740c05580c9074090000c940c500880411100d03240c00504212520510311580350005440c0b01030005060300341d40380d110f68081c0c5031103020440c0c040e690302084945c03400054030301c40a900f0000180c0b03042c007007a2034a0910040b990070401041c00c01e201d51190041e041112032017001058501c40036010401c80e070449 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 266481906 1250 266480656 266480677
    0x313081228050105060a031e05091609050105060313021314011e0b191e02031801030207020901030201050a031113050a050307150509060702060a0905010e150f 70
    0x28810600980c0448400a00665580740c201444401d2140d40100892001c01c01c81885880c20004200a80f20b0804072035903207010b49070014821011140808500c0300b11081a08031030301d80700802454900000d095443c010100300d040c3e510319580e091107000c3d523000340540364003c0000e1011403d0030071041c3d10790304100c1c07000702000245200c00f11000200e4407260000c181c042d600c40010841c500c41600072074141c8a0a960003080d01d0704015aa005500c600410f07006814449446140418800c42e4459800080051125802081762000951720742140840d0071010b20b400501d481a980640308a47e56141d011706400a140e10b950019550b9821a03c2190185500d0b00258404856801c0c010011442049411b1045a0411050062410654120750f001c5d0380194000d029515500d1820114400c43c0e24085a90301c81403004a4214040c2a50083d00090003291545a042e00014a40b080c3c40c0c0c2a680c1c1e9140f44151810009042441055180442810468a2110000c0a000701060f0380d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 266483156 1250 266481906 266481923
    0x90c0b0304060f0c090302030303040b0912030a022203030c140c1206010f05010e010c0b040f1202060609091606080a18081902072301030e06010801150506030c0313 72
    0x1518a18008264000c5908072410b9a5a5801c0c0000e1400d6201e59400c0040038a00411440d00f9680407036524440a80b0203003040c51200b0009042100401207902d10b01b90328590300d0b03182d040104124003c0e40201c500608060558048046e84405103103110302241d4041d074401000c003441d40c5600185117800070b82540c0d2800342e141d84034103588400c0282e041c40d04500c4000d00c4903614002c1000b040748a560055030403c2070a00341d000305680d021001d5140307640c202e103084030781d0b45503483c04034080740a144004200301680b6003114071154001c41c006105d1903003501c02402c40d645441c0c4258841c500c481c8182c1d0303205002141409400d00c030707401d42c99004440480c001148200066102420480400216080b074800a00228100303481c5120b0074622035180001c00c081030502c0c2c11074880c507030545055508210b240c4c2805641c0d84c425001092144148070a0300c1d101d50311041494007a0901511901000740c2ca410000344e5401c08104891148aa40300d9843c29500c948038a00d07603400c8a50002e544903203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 266484406 1250 266483156 266483159
    0x3050a0e09070c060b06070b01031704090c0f1b020a06050d020c010f05040c0608060306013c1a071509030203040312080a060806040302060105090619031a101404090c 73
    0x8644040e00e50003144240c541200c203486924040e015030362551022802046c081c44110001085090050f066a41c000a84c3c00e4001440318929658003459111500c500c1c2405003090303c2d00c4d00184040700000c19541c80c10b030a45c0502a120034081995400250040c03e104002c0110342d105a0240820000e05100985054121041c450a456191132880344da10303070b47c2061000700011072000500424a90400c000680391450020f42c07541c00c1440340171641a4400d02190240d80c4a41c43e5400707200700389140101d801c031107007a5180c10088501035000300e451160b80e00c5510700441e00036501c1055002100b585c01c06800c455120290100c11800c40c207502c07042c4400300015480c5140701d0120202942c50114070303c0c00c82400e4003584d28541c08417495820100c14800465804a070b10b605454066a50701c19548488010400003142c499601688501d0400c0201c01c00507001020080c500c650300b08100719842c0c0544030100520716118a0000d42c031198000d030147c4c1081e40202e05803e0060400c640000e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 266485656 1250 266484406 266484409
    0x60304150506240409060806100509040f0602160b070e03031e0f03090c0406210335150111211e1902010515060706060909080c100c090303050a0e 64
    0x603806111145243c01180138404083d180c07088000404406000b44001d050080c00c01400c0521401410700510070f130070003d02802400760200812a61001c8215590390b9102400c040e5208007120484000050101040d021407190448904110005020710725010f03042808164541c0001205020f420301480200c65002940d4003a5106065080c0580000134801b405c2104a07411070f048070701c102c0c0480000c1d81680d001003104094041d41814000e085030013000a61180140c1e503851645e8424004607101c2c001e5021103c1c440c0211019007069006814690064498289400703020390254403003ca00001c1ba454526184250001c1ca1303850362814180c00c000c0d828207605146010b0703804100281d480c204550010003918250114802000035040a41103e407203024042c690912440e40441c0c00b4050090f607a0004008142e40355040250048038501280b00713401211426a8a0040d6441d982104c0314501031070302d9812869561100042c1580e0b0250b0b00c0303800204d000c2c010040c41c07402d4600035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 266486906 1250 266485656 266485699
    0x6090909021c0c08011b0801140a0b04060201020418110a0503180703030c050d0206010303020303130201050903010e0a02090a060b09010c0302010e010c050d0c02030f07020f010c05060a1a060304150506 88
    0x10034080c0003902400f5051100c01401e540d105c4070002081d0003401c41e60390941c1d0b80305803014150341c408003003201600200c8000580400c030a4000800101c800100040c0c800e40540c02003040342c1ca620000600602d07200301f283c0c11505000e5242845200802220a1091148000307540c8200e21240100e245850001003034900401504100c1c0811890f00c059003d1040c00c0009030031004070703840104169815a6002900c9000140400300c0008044004408680c0a0b0056030007505018008100780100300c607400c2e6480c11010416806680301c0030100e902e12800d0300541e01664501c0c80442c2c689882440112008070088105070304656070351884441b05030080c0180f40c40c3c0045549c41b2912800c242c5c0e045c00864104800b84000e5600402640c03425400940540b004503804444000b203410002006030780c2e480051000070300d1030007004108182500142d008085c0209464105041e400b8400103104880c4000e50740a00880701c0022440b40581054020a620010203444c01203000ca4050390900d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 266488156 1250 266486906 266486959
    0x20307050d0216171303111816031b090605160605070c020306150d12030e060c0c011805100e0c030a08091305161101061a1c060609090902 61
    0xf1440d115015200038048a5215005100c04504c6581c2c6410542d26031982d1082c0644001400c034583c4ca1080d0300300d542c0e08070141100c1d020a681c80003a0b4a0500f02c1415083c1c0000d00e0500424605210780000d00e141c40c0c040d2814414640b140082c0c0f504049081c0d0703058204001d42060220b04c2c0304084c00081d203030b00406028000b41e4450554072143da104040c200140180450015551440030b5405607031207401c01c42600b03410480d100d004903102c801c100c01401c10b034110443c0b035115100a110440c0803203002400e102020500070802c071840da11901071492515000509242e0056074038025485083c1d210500b81c4040304200d035000740900340441d080c140e142400781c1d1030403c003007a0802c540c24200300d110350f180694001004240740c44401038103a8440c000440042142c1801e080c11500740035403001c00601842c41c41c0c02088046825552210343c800c01000215602211001c42d103004a0300a4106590fa41e031180b6460a04220582000381064101640d1181700003c950007200c7c0e42c1100c680 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 266489406 1250 266488156 266488177
    0x1401110d05240a03151503050d091e05061c05070f0806180f04062301061715010e03070308030a060e101206050a090b0a0e010e0a0804030303020307050d02 68
    0x28061070000c00900341c2c1801100c000784044040c6121030b42c190b440c00f1460781503991003c0c900890300d021010000041400290140301e0607040500072060290010b220f10302c02d000341d61040c8880e501c501215130000c1e8840302c1c80c1886d41c8140002d020505e802c80250010b01f0b070311500c20b0082014280320740140c6200761502400f28540c1e270304036284c859106e07004652000b02615095207a410005e0a0686108008c2445d1090612800070808110780d0350080c034904403001072031850300c10110000042c1d981c420310a2101041a104890a0b03080e141c50180c0d208a02000d4440098020540195000a01c8124240d4540240d90011000424030b2004e90b0050291040c006034160501c140124401c802030f011400b4800505000c0144070060185030502c60b5006401040d030b612031480b107102508c25910001c0c00c810720401084203002e01e0f039000f060b520410000038416101040c0c1c1c40c2e5280c0243c00e00190400f8020001400401e01031b4008503040700d5070b450068600300e101c644200498001c0c0c507424 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 266490656 1250 266489406 266489411
    0x30a06060911070506010302060703120504080406030507020c01080105060c0a0b010b0703090506040b0906130e2e05010903080307020f0d020f10051905040c170f0f03070804031401110d 81
    0x180100700c1a44640458003200c59070b0645401c141e500c41c0c9648800510000f0b1240d8070005001040621800c008101ea01c0071103000d006c0e40c140352600c00000c2c0c10901071100020319100000c0c07682d92001520014a28068407100400d9081c242448244e0340900b618440300d101d580d580d03030006940d1000c207500030122560303101e49400c0b00d03140c020071002c842da221901c01e403070600c014825011600116010100101d0704ea642d50b0800744098164860740c0c1e0701c000b11448207401007000c2c603005801c0070050702c8204c1015904916401502084010b9039000b0103002824901e800d000280403940155084042c41c0100c502c20182c900c00301e0325060401048a0060f00111000105004208610314180e04000d4051029152103212180003d00109141d04a65101c0000c50203000c80f24020718040c000183c100c0080e500c0e11403d035a560f0580d040241e00030301c03410b03030b05014012003c07003900c0210781e002d031180c0d02d01031458483c00c601c21110b40102c40035550f10b000010780c170006040285078100b20f1a002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 266491906 1250 266490656 266490659
    0x71106160c0f0803030903191b0f0320030406030906061e08012f09120706050c0f0a020f12010b09011805061002102d02030105090c070b060f0f030a0606 67
    0x40c00d4403072155030040f081c0364818000d2205410f404400c2e40e91090070302c40e0100098605000031601e180000c500100d10142559862080c02081d40b02c80380a58040d07180c1a210140d1050301e050558004004609250021310042c00400d129802c01c1040900501c804030f1001e803034400501044401c4040c20b1940c100110f420023070250280120015081c11800f20209600d8855805140340c00514100d0840c2d840024001c500f503550b49215040f030845d03d000c44100c0c40d2500070207462a40480ca00c1140d522611899003501900064041107056000e807002152948100c103120364418006910305107075407a00d20741026600da000b80d4500030007890040c20702c8000d80395a01d00455002500c1240105030501d03483c00f242d0340000c5c3c00200345101040001d80c9001c1008584c100c2d5030400240c1144c20314451402c00b0308100d0390065410307102c2c100d4090000351070b0606c1e41c1d6001c1c86403140c02848040d03640001809480d144026130f01c5064007500c0286200c4410001a092a840c900c08844c040d43e0f4500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 266493156 1250 266491906 266491919
    0x105070f030b090c030a0f05150a050a140f0a0b0a050a09050d0b070f1103030415060501020703031202090616051c02031e0a0504050312250206071106160c 68
    0x44425403000e40d090802c0740081040c08101d80c0b1100a103440b0710082c0c004003242039039246905ca141e00d6000c0310f0041140341080000240d034600600380c42c51040760100c8010800b86004d83c0b440341140d0944507110007002601003400b81007003030304810356400616104000b42905650004280d005015551103951b1790020101402200c9250880b80c0a5641c04001c180085c82d000b8038560000064144543c0030460728a045580102822407810b542c0030101c140010040d082c3d41c2c0100c240906001801110f0700d0b0401246d42d25500c0c030010b0f0000310529047c11103648140c0c002c1020000c0503000702e01d80800111515a02c55041e101212964010060683da0048032444496000c695101952801200b000c1d002500344140c100c0c0402003d0004402484c2c40c003400032507004207405001d41e014000b03050f0101d111070308a0807170396041040001444d00714620071446c00d500554004c180600704001c0f174072070500407142905510740194041003140044c0c1246504851100d00c02c40c041d40542e8100311 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 266494406 1250 266493156 266493167
    0x807020a0e0106050702120304052701060f1202071a01180f020412150b0a0b070c050103061d0a1d0106060908010b090112110a0306060e070e1c030e03030c010507 71
    0xa0080d158503481e4401400003550010894040341d030115050621000321040d92030a6101d00e80c042503101041485520b07280c06495180904000161701d5203a090b80d80f1003059400048100010001818000c50f5440560156000e00310160146071400300b20b01c3c06140000021300c00b0f800c08d00f10800380c81810200903c03240103462035060120303c10b5003010310b80403001c0303e803c803480002032140203401004040700a080d4800000400020070600e10107546444d90f141d1a80602c0042c2d401036000780000c00d065000e40604400c8400541c0420762118009094219042007c2c0c810683c0c9500c0e541000e000c05030703409506882000030400041d185283c844050880601d0b580040e8540c0d0404c0d165408c00e0351a42c500a04594414421041110803884c0103076400906510465000000c110007201b40480da90103101a00c99110403000d040d00d4001065402b0018032100a900110701100f100e0021040580c0d000182d06ca800e12400d80910040000c0c00e42e000380c2039640c1c80da036484042009030380e4080c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 266495656 1250 266494406 266494409
    0x50705010b0d0206030105010c0503210702330c0c07080c0a0603140f0912031005100516110112020409050405071a04030f151401050306011d06040506010c020d0807020a 74
    0x440d1888820b1480341c1c0814102d001c144a0f040c140b01c2c0c03140310f031000d2207000c0c4202c40c00d908102540b004180200300b0100c51070360040d10b40c2401841800f45501710700d0705e812210111030517071001c00410f4040704103200404200051802c0080c00090111581e0381e001041070b54098020340c3c02805840d030252090210344640341e441007041500b4a020481942c0d003249031580c00c09040030820405607103600a403860038400c2c2c00c01c036502150010810900d109501070b02c10a4481c111070340011080c4a42c401c4409000310014440b80340716408400c4002254540024603c0d20b041c10b00c0d41c031031036401880008070307003003a488a0303500760f1141c0401007004000c0c096000900100c007001000140c07031180c5000c142c0614007009010038a01004407050006480728200e16040e804000e01000081c01c46a001c0540d080c4a0180a8452000081514501c0c1d054100c82c401d030181042115594510411000d080c002c3e105c00d05100c0f03403104403405031702e03403036500018240a00005503498010744140040200d06 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 266496906 1250 266495656 266495659
    0x7030210090b030606130302101206060525020a05150d1103040510050c070606080a120e0303090d0f02040e030a0206060607080a0305060f130902040b030304060206041b0312050705010b 81
    0x401e0040c8503921650742942d030040c0041d17030361985542520040180c44c202c0360700082d500a003030210100340d096020210060390314594205000041d035912080d1240c0c0580014080f1440c04e80301d942c100100b10110300a0940e0005040c40369a41d964404200f2400c4880192200d9101c002030a4002403414080c0c0c04071006104442442c52405403101903c60103000710241000380c5607030200b41000404802d60310b03880c2d008001013054580e01c05a65680315207006046844005035030700e961030a801f465506009510290195142010800420400344000e1504403000500d03403000e0030150710346202d4251340c01d02030350080d692198850340183c54850020b003010310070343d4104070703402c0040c07031803400d8074540e100a040100e02512000300050502007140340c3c1a8225400510030740c50039000c2d0704000c800c18020f5804110b2002031400740758403803045000300030240c0e0002c008240000c01c4000b8007010a00700c500310200f01501c075500d0006007010070340e4000c0090740101d11070050000c00e00c900c8984100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 266498156 1250 266496906 266496917
    0x70906140405090a110904050c130b030c03150109090c15360b1b120d0b040209210a0b0403020604021f081602070e04080a09050a080a0809061b07030210 67
    0x3420745c0c41030902045080c01c580103034481804030f410080100300b19000700000920650441d0f0b028640c1c84c0040410b040d20310b110b44216034405825040200d0181c3c000c0c0590034560046030b09243d00e00c8041c21603440200ca414030003200002c0c001240402100a0b40280c2d59030b48803c10b405113046894401f0f8500008070490f401026032241c0d01c0ca05111021140c0d0070302056100d440004100e5611300082e40da80300c16004600702010529011001445000341c200e800b003069001084c1804200c0c001d64000580020300c104ea03900f02d00d506441e50103628203142d01100e18541080d03480000008007902c00301c0140e40300409110841c034250608500d014840040c00a19118101c0300506084015200b01c10305600a8071003c4d40034420b00000024044c070301c3c515a40c600305840c0000060780919090300c001150b650011030140f034811110021103801800904441c0c107142c60700111544200107055206100f004542d4504640341e559520058190700a400e01c14550b0050010b996080f0f503c1104100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 266499406 1250 266498156 266498173
    0x1014060c0307110a05210706050702030c04090602220905070e1f020c04020c030409061d0106030c210c030e010c0c08090a0e010b0a0f03020f07030e0307090614040509 73
    0xe4000058a211940001618907400b0039800807842e004811741110b90040c846081d40c5160700c42c004101010b15050b101101d6081da82c032002110507000c1c400000794140c00070080303c0305a10301508004140e90061400500c1c0c2002840300c1c038466540503501c1d2540544c1101c0400c00d10b80a4880c043c0d0084141c01d0603140840d40c0000100e96000751f07030800099a20182c040c00015200f08000160201d02801c00c564032001091400c0c1d59401c0340c8905089141801000706685a000040082c0c0381e0101603440183e03400c0c180c09602a04182c03021400300101c90b14981001103010100c1c051604c0d00d04130000d060300340104018203072020300340762a0f126810840c0c12060385500c49951000c8540000300c01c2e484240c9500015007034101e40c0c0c40800891040c000200301140c0b404001d0036181c903613849000c00d402e480d0105070140e0203030500c803880c85841408010046401030340351072411100182a106000d44900301042241c407140c1100c00380001103150500282498419141c0201b10310b8010500314 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 266500656 1250 266499406 266499427
    0x31b01450f141e03030a051206060a0504060818010606030506030615150a030905071e061409041112010b04051e090a180512030601031d0a030318060203101406 70
    0x1188650b040c1070007100301043c40010f40e1142601080500002400e5a6841c86100710043c40e58008007611041d20354102c010034018641102194649206510744608261914030141c41c604c0c0003c1541d110412200c035a01310f214428031580307000c0c0049840000752420044149440c20900820350406a051902c08160603910b64902503036101c180302e001d55a81242c0c00b42100600801d1303000400d00d03c290341021480180c0f00940009142400c620402e0096680908588011000c80c03a00842003007080030720302e02d00b000c0c1c0000072210390724508075103054002c460405a85000742c2c03044a1452022406001c1071904000c000d04412800b0740804024810200041701c001c0040c1c00060b080e6a0b03451503080c2264941d2008c11180d030881c0c242c480d2040d0a000c94038942e40f00320348090010340789c0308036160102c040c0201c160310143d0340c034014039284075983e40c154024049520515445490051260001072040c00114800c3c3d004580007402145410040b00c040701d07034160f01c0e0340f00f01f0041c0441443d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 266501906 1250 266500656 266500679
    0x2010b15130b0d050115020307030f230705010b010e03012307031e0504020103050a050103050607141e092103030f0a1523031b01450f 59
    0x152410a0403241d40c0320825003191001034082d40c03044220010124107440410410b52040d4100d80e10354440d200f8a4405440882e2248a0740d40018080703030540583d580094410347c504801210b07002504d8212202810340900243c0010b10104c0f00343e074480d641842103580c800034014a404055000f40004007182074541610720599a600140b01152000154217a10942042d151515850403070313998445070030700f040043c00b0100e4050b800b01f81000c02048000c0d2580c42080d040380d40107009041c01e92a003200446198008502030b0b54101400c3c006072104001a5030f4030650704041e039071800c1d6503c006005004c0e002c800d114090400c0c14108441421507100402141c2e4041e1250000c0c08031681c0c0d2540f01c2d0002c08500d103c8170b00c612141200403607402d8039001840101703100781c0c9001074100122410143e4031a04041144002d62501410010079402510a040364240c901c1c0000c17a00d420043c1d6100d440c40b0402401c881c034405424aa40310030a440002c0742c050100e03405000c400c14100060200c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 266503156 1250 266501906 266501929
    0x2280e0105030a06051b0f040e07050f0f07110907021501080604050c150c010c210504171308061f1e03030e0102030c060f150409021318050a0b07030c02010b 69
    0x83c243d1241700142c00001030031082e030000d2007010901900c54400e20340c410a1504a0701a9030341841c110301c0815100c601032010b81c0c100349020100d45141400b0b42520400c01c1d0000c2c0d800319110a440f56042569035600c100540c0300300101d5000f0320b210754100d800c0308818101039028a0785504040180004140701003126045003078190b501141207548070b96405841e102c1c0c41680c001079440c00d500c0c00f607050703402070701103141c240e00400711601611107003146c0c000c840003079900510010b60b140282c84641c080d80050b10620790048601241603540350720305800e00100f103484505481c0e0100c217100e240c0c0b100d403118201600f00400c48024402c5038881c0066a0b841e9400080c041c09104940c80c10581e200700111031001020030180d03465400d02898880070740d507043d02c140d242642e1184091075181000d108903d040c030380060038401084207500a25000f440c02000b0140906001042e01010800402c146013507180b0034928500d0b03902e00107200a0880d07a0042c1442c3c00c59051040c600c0099444a45288 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 266504406 1250 266503156 266503163
    0x20903031b07080303040501061401031e11040506030408040e0c03070813021f020d020d030b0f0d021c03050304060f0605061207090807060c020a050a18150302280e0105030a 76
    0x1d0a420309820300314035000380c0f584480303181e22001003080100801034201c4c1045840070000c2c010740569220064058810300c00c601482c1401c1c0f800c02c901030b2203150300403ea07280440400c0704c0c600b90311600400c00d19031044509542e00200010104607090007a27110340e40c00b0032490041415420042c0c1c1c001d00c044000340c00000f001003500d5001056680c0c4c10040c0c000d540e60400400361380081400d01944456840703100700054025007806a0409000e030184154208000b800b901c3d41e10933100800a00300c164910a036041010600d00e005100021071040310054029207540e5103034609890f10380f0035150682c2d0903001c19804c12a0801181d140c2c10141e880c10f40c041c01c8648450f58540100312021202984800307100c1c400c0d501c000600c1c9400180950005009a8481c0320301c41d161024000b465a1600c184000070654090301c010702000342d03209101c2d0340d0302600300c04403403075480d00002c1305010f500d002102d04030044d40340c0c940d0404079109003200400119401d01002c1d03150200190f1500020386025 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 266505656 1250 266504406 266504437
    0x9020f030f04150203070e1908150919050604060b030304060c060203070c051605010206010905010e01032006120604050711031b1609050108150907121b08030903010b010302090303 79
    0x1e0403c03802c490110358100701010110b45034500010300410300428030000c00d0068010310181d4441c20fa0500d01442640c0621004014004984210301c0200000418098045c0142103041c40300e0b58500c0441c4100301d018034014030b17480c1064180300c02101d10851030540b0130350007048200070041c0c10010081e2869044480181c0302d544446094441c90304000c00101a40124402240c403004119180410381d01c1c02c1c8c4c00c41c0c00980c1c0342c01440040381e0081c09042103203c40d01c801080045c600c0c0f800d51183c20358940d82e800480e1050004111503401050b080b580710f42c03203881003000c03a0619206040d4440342e145031407034140b448100304035140d01c110f0072400703503020f40501c00070402c03242007200e11141c0c00110300e03d000c03070350b607440200c00100310a000c0c016280c0a1f500980c071462860104607030141c03a45001405806107400950b98480070701c0102146c11081c030b28541e11030181d86606a600610170741c0082d5984408410805007116142c02c5010306241c418071505c100d41d00c00100b59401890f152805 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 266506906 1250 266505656 266505661
    0x21b07032d0b10081207020f0d1506080a140a120e15033105062701050405010c0305010626040305041206020702040b060f07030e06131d0109020f030f 66
    0x7010a21005480c2410002c14014689807501d80501102d90780c2c0261914400300c03092041051042410103580003d104140100c10301d03020800f0f036551445160017088190f9002d140000b610038a030301800d140d802c680410340c03e10015501d601d69036030725040503002c111750955880720031094181c0c01600300700c6000c01030302d442d444a001144602e01100c0c0e0031912850089248d003502455044507096241001024492900385c000748803030147c2d40039020340303040d650f0060392004410b01e626030300c00002104000102000402c3c4a0030b4015409680080f03004000250007900307641043e8401c008100d5660b45014030041d440b04483c40460154681c2e0215850390300b400c882a000c1c6401144030310400c50b08250400041c3e500600c040e0740709840c284809a15182000032a00070840171007201901003000340002482451030303905600004100a0910704400949040500c0030740008040c2035143d4013582405c8410302042d801400e0000d81035180c6a400074181c0c50b43d020141080c1e00b0390700034401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 266508156 1250 266506906 266506973
    0x515031c0f1e18120b040c050f031e10050c0a020f0606030a030c0f1205120106051603030b0a0f080304060219020607080c011119080906042a08010609021b0703 70
    0x200240103080d04c911034510034009040482d88608262000c448018140c000001c2c5030902c07648656011100a000e07000640382c541c0041407103140300205415030b0190100c02245440141b041c1c501507581074059a84461581d840a817601c0704429820099520001c10882d01d40d8000585644076070b45842c020a1300742d01ca10b42140001c3d0001d030020031000f600f00705d01c00c0440e40007004e0207000035011407000099a80d5002541d01e445510301c050512410600441e0100c2c1c0a0b81200c09000d4016000342c01c180e503101203050118015401640b21138100081c01c1000035030401c055254140e2010804078040c1059000070700354403408800a040000210b8030480c10350081d403220000b284800c8a2589c2d400025801d66410041c80110001003084400810b0381c2520019110344641c0d882005048440f690308001840500903000e1002d101510b51000310f1402020f000c1e010050025490258075681007000c2c565900303005803140c080036800320760208045100c410682c0d0703020b0402c2c0d0302460314070031104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 266509406 1250 266508156 266508197
    0x100e0402070506010e0601090e0c0904050916031b08011b080c040803180108070813061802060f040303082505090111030703020c0405070c150515031c0f1e 68
    0x30182c600e01810b0700006150f03890150080c45840b00341c0e50640705503110054003145010a4070b041405410506c1440700608080d804150081000d800701c5c0c842c0309100341c40d601e0686407504219280d02c110751500c1045d140000320640030f0a03120b00203106c030320307160200c8001c0c11142d103400d00200080480494010130b07183e0101c0e03015084c2c0304207a03550390440c04038004040c40e02c1c00103117000a100da40024901071040e170001d405080000e90994412040d5243d80010b40520903000d891410b02c1c401040060303540c0700007014040e000901d41511303549503040242a003c4000e040b40701070282080c102c0c2024061038441158520f041c10000d469602d032000480e140c5161480404051000103115030500d074000400210168084a0a100540c0c60b8a0100e4807054a140700030800c0740c002c1c0304001600c4058000e0f42d400301c17104000411040703120300082c2ca42089440b080c0300440703d040c02403075059801015821009490700304400385030404640e00303501500a8414104020102158061090448 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 266510656 1250 266509406 266509417
    0x60402071b1e090e0309100e1809070807050306040f0f020901290a02030405040902042a03060e100905060d0213020a08060301091a180703080a0e010e100e0402 70
    0x5411038581c140e40315540115400e2000340c07020312200143e520381070700612404a8030240070318108405201440400e80c000101e00c02800035a600110464880700e01014041030030f900c2c007103102e00305000b041d0f09202c241d4024640c40c5d0000030052046880c0080c2542d042a80405030300a0303902982000c40c500304404400940c020031100c00000e2a0300d40220102a0718a01c0c01e140480e400d40b0048082a03215502e41800982c0060004010514290b4001122180042c201150112540080c0720440c04a02c42407820f03140745a41ca083c0441d41442004040c0911140c809a941441002004894010310074249c0003912400042c1d0a5110b030304a084003940e01602a44d035036a084241340300690030040b800c10000e00b1542c0041c1b150310b0305004c3c41c45010382080e001080301e001d2012003003c0340001004505861003111200ca407000003041450000d6019000c03a5848580141c030013040b441040e88614104003082919510382d07511441c070144e400d500d03424149100c4a0320750200b03002c0c0c080c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 266511906 1250 266510656 266510693
    0x2221a121203130606090e150105210c04022b0204060e0402032e1e1d0c131d060904050706050306221b09081203041106030405010c09050409030806040207 68
    0x1041c0700015521107e420281d010701384103099541c13108400645489500e001d10500d544400f040401c08100358140c49110401c0c409079003502d600c48044030101301640d001c1000c003002c0c0c4642c07201490880310301f4454800010007001003946402e01e0900b0084c0280c0303905082d80c1c41258000003081c0c4030001d0151804030b100c500c801380c0410501d001e420340c0000d5114402c1260001001d0781040c005035159106109941c0300500540440d141546481d034100c8004140e9100c441e4104890315074a250f20240b0002001d03106d01c032144d00d40c241250300340032600103040c4034054030f151002e002c0000c10200707100041e10403500d0101e4076a40c0300c130006034002144052802003a4580c01c03000100c1c3e034050b0840c1c140108030b5a80f1030300144003001c04448003c0d0030300c1482201e4201000b8012000c140c4001140c10900850b946000382c01194000b07a1103030b0003558221416950751044a4501d42c1103e0007070020030080354200b1031899141c4019007180001481c080c41240d0001d4943e007000380c64400450729800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 266513156 1250 266511906 266511911
    0x1207050d0e100902030615061b07030209090106151b030c02030304050d08090301060b0c1b010239010f0c080f0c0303010314100911010c02221a1212031306 68
    0x800810b003000414621a003039010f4015500041c07a500d6a00c190860040d402400c654030701f12074070034540c0e00850504128003c90286400c00030160342d800c1880d40c0901466000010081d180c00d107041d005004008006090140d55021409076200a00600900d6a05030074584800002071000038258892500701d035a00031541d4404000f8400c03d00c01900c14400700350000c011503921b4401008460080380081e0190b54404004403401042d4000c0c10b901c03804060048891580d065068400e8090352802c1c1d1089101c3d000108078458414426001d0881000f0700700801048500a0000e081c52100074006d8a03900d0b00080000140641d801202c1400003290150303612540c40e0f01d044c03c034180380058426414410580d0200c52205180b040e50f84007039000c0c07000030039010200015a443c0031414020303a4070108100703c1d08502c00e1031200d034940c040000400000d1140b0b00c000315400e13020600d1400c80c000c1c21000310901c2d59440c0003400c6040b115400903826210d50700c048004942c80b000e00c000420300b60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 266514406 1250 266513156 266513173
    0x301020417010608030429040902030c07110a05030d0516120203070227061002100504051e0312060127082103040317150301090819051207050d0e 64
    0x2100180800d9001ca4080240212651110150354038003c9008058489480089442151241501902076031060400b40383c28281c0c0e5103040c0081381c01c1100c2a1080d1000099070104102602c1c44261500c00708403010b04050f03003000d012a42d41d0401d4100101031120025004070701c22030300d06000c81d03c56800080d5040003010094004c0d207075005960124000c00c41400d026440b40c043d803043c0124003507071182140c3c84da0b480d0300c100001d0f402d40c40b441c0b0707080d03000c1c501451903104400e001da1445103000300c00420f00d01a0175802d0322401d00004109810301d4100b030242d41000310004010581112007460640e46c10204010341200d10741050300520091b885101000500714004280990038603068003001d0140c04100b04032000754441114000d0004564040030351300c08a0700640c6540001140c0a00d16820502002003803c40701204000e80d5500004251090400707414080d081d03001410b0316080e400c2265900042404000c05044001031107008a4428181c4141d41d01400b248a0300340c08840058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 266515656 1250 266514406 266514419
    0x150705010207030f210207020117130b0606070c1703040f081c0905240f1201030b0603010c081b19120f062909030114090d0e01050301030210090503010204 68
    0x1e6001c0301044003c200380c03044d012100c90065201c0c908168100c52440b00030040720710400001e502c0400100d06004120303403000101c800c00c0180c1440380d804011403090b9032506040180032010000d000d03610907a4204105000103d020490700d0854580b001c1c60700e250350015240c10f003035000d41d07000305114041c0400d0006400000180c00c00c8482c0f940b01910300c01d00d01850f0110b1f0b1046050080340c0d04000300311000ea010086401500d90b140f2078610403a401d01c8140040c0280700d9019071882880c0c000b50400600506c045400c0c8507402c541d00b00c00811088600ba100501807074001004004184142500e1402c1030502c4422503c88003c0c87d94042d41c041d840920182451000c844055480c1d440c2136620300c1c43d22070714450007060300c01c80b80c48132000c0b07050082c00b00d105555140036414a800c041c8100e8019071001d0240c000106405403281c1c8082c030700020200c6c40d001c04c00030404c08214406030b4a00c82640c20408032815a07030103955209840004d0711080c1e0740307400c565112030382542c4009400942d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 266516906 1250 266515656 266515661
    0x903030f030a06210803060d0c080a02090a230a020702100c2609122b17010f030f03230c0114100504020a0c05060106120e0d0f080615070501 62
    0x2a09440c1080103d142c40380034000c0720501080c04030a4000389030484a01040d6007501030740e4040002000032850341003e40e40c075594800b103541301009176807045070304004600e0490281d680c00b80112a0811280304d40e40701014006205001120000d80b141c00400c46003081c42e0110382c801d64015203401104400c10500801d5503154440c02c0d03d94003001c284000d0380f0340030850041308a480c40046281482888405c012120b0005c842041702d52049a41034100504204030703410010240185000424030700800c040c09806600201444c0000a0030060040c101030040510990740c002900406145c064075090ba0040403051a80041c10940c50940c02c4008090000740709600400b0002d003e02c500091b041900c0381c0c81614114040c37010b5440511041c00c080d40230b403400b4100f81c9461111101c1d1038403003a040c02c800381c011000262a0921800c000420341c0103541080c40310400400c01c19000560042116034011005403c000316240031840035611070b1440303440d054050308040c1d41d40d481072810303500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 266518156 1250 266516906 266516911
    0x30c05010f02010b0f0906010c0501051603060b041211040b0301020c0d0f0e010206010b0d0207080c0f010b011d010305040203240609060a0e01060c0501020f030c12090c0d0b0c0903030f03 82
    0x20705166071600c8003071043c011200d5241010b0020b5101e080100108000f011009040c5c0d4100801c0e9207801c00414003d000f03050250800045944045003441301c018180c0346035811441706100304001c204a07d4400b0003c18013483d800550181003a04607600090140c15203203900d44d815030000c605031981d08804501d0300f583c881c80391560101c1c640d1103001960704600c1d00310762038096006080100581e5800c0c1c8006c20081021840040c60700070b080d07407440386541080e441202c603a8030492040701240024407031482841f00908028007030401e40e0b00fa0201801c445101c1d00e04150b01c8101050454900f042a403450140000308000740000a101d15000e9040440d0303c18031172541c15020a41c40e0503c0380c204400d560402e190042e00d6800e103181983c0c26000404101c030203640c00c0210b4039446140341c001c0c0d400740e00c41200c0e5903640c1504000d500702460000c3d1001000c0e8029890015095443c40d08500c00564030901071007459407122a190301c00c2c01a150016014040004d15040141d5401f00961 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 266519406 1250 266518156 266518159
    0xe010210110403150b03151b07230a060501090906050f010501090605030c070c0303080402130e07141201020301060810081207030503040f050f07090609181119030c05 73
    0x1840360050140300401d944409586200c0600100300620208084043e00e611020b0f0501c0301140c540700c0325010a15141c1c807105111a04201c1000740840e02e5401e0034082495060321542c1d908101d915103480c441200039040b034906a41e2940601d2510610030b221244555070014420855980c0da04440006080300c09030894a9a00e443c0000e07a10100d0014428140d0b2010381da05100039007421401c0e00c03264009032a9006444081c8010f0b40000c000c3c840c80400b4500c40d6603a45070320b0034207206101905040c40c515401940c180019030601c580005a8402100c50951508410f11030004c0860b6908141d4514451a54000000800c183d5007040c0c005006405249246140c156940d00090b102d05443da000001d05a0030002c0c9808130b071085000c0d5802038002c8101c4a0109102d548091600762503d4041030b060300400020031403068103224140051103101c03402d0002c4241a00c8503180c0c5500240d0041103c184c012210b84241c41c4c000c1504a0b007060310241031070880e2039003454451811a0b2050ba1b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 266520656 1250 266519406 266519413
    0x6090501110304050f0a0306050a0f05070206090a08090103020c030313121430070c0506130b0a05091c05091f0c0210020c13020c07060f090306051f03030e0102 70
    0x18595126242000210302031501560510342000304021041c0811440d203903200718481d0340400401c0441c45554040c1282003030024074008244821025030300010811000e6401010420415000c013281c044501e43d8808246640d940c103a0005900a002d840041412444080304214a0240ca4010005458044c0018440080050104940200e4860314030301e1008400c1c40aa400144404d10f020a40002d40d020450301c2c5001d132007013140d07040044501d00c00180c1d540c450314040c0301c3d040c01501c1d0049070114104c001e2a4068407405403004002d0680c10350780e0703512000600c001c482408803c805a41502d070224000500410080458201000440c0305041d60350510b0303401c80c1c0807403034149255000d0f16051204400c5800b00061000150b13003e0095000f40c202400d416540c04001e8080c4824103400140c540c1d000c0d41e01945000e2144d0042c00510240d41e503000c02068000c4070400440381d001d6404580d940d10750070502c0341c5c2c0c84070030810000020503031008410543c0084c800101c540d03007a401c0303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 266521906 1250 266520656 266520659
    0xb06011103092e1d0a0b0a050f0415020105100e010f0e060f0904030c0b010f0e130611030c0d18030e1014030408030f330402090603010b1b0a150b010c0b100609 70
    0x41005001c40c0341b140681c0910b0070008600840c1c0200c0181c207903060140c0d511810542d40b500201107000b0302c0e080910040c0d55503410402d961030341d8286038010f00b00b403092100c400e6041c0581d03071b8400d2181c0c0c0121021807051400098196481c00c002c4040108054a241c3e42400d05280c060421400d6040846017941c4400010695002e45948402140d0000b02c6605054640c00c01d00412000d0001081c3e410f04c0d140d04001000c0700c0000700450044040384e442e180d9601e203101c540001c076080c440a0241e501d070a651070740c0110354000c016100180c03040365100c4d149042c1c14400c1e102c10b0f009000040c9040004401c11060144120145200c0d010f070300401d0b4090703a600c8458290050070286502010816214502110140c200d0301d01c210301ea019000520344540304000440c0c0e50401d074055002e180001414564121483d45210000c5034241c0091000c641c00d0b5642d418200190201c00c41201d6031880140e54a80c8142082e0a007590006408010390501c44804005602e440c0905004540c05010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 266523156 1250 266521906 266521909
    0x203090609150c1612050405040b030705100503090a06060303050307081f17070e0117010b060f070206030c09090406050a0e120d020c01060807080105040b06011103092e1d 75
    0x1c860152608803401e410075543c64861041254111083c00b038004121514841d00290301090101748a200359103603241c4841c500010001505e01071203030140281c100309400c10860300c031441c0a0342c0040c00b80c1041c030b86a03030f034840e54103143c45c0800364050411814a103001040c19004030056028240943e0b03620502e40c0c0f50b071811b4185000b480d00940c8007003103050041020410b40707100d001201c0719140507134485540c1c40c0d105009514013a000f482c8115907139002e02020000c01d20420040d0f11050301c01d40c1c140401000c0c402194068000c0c0a4040c03100000010154290b44c002c40d41c40b9400180501100d080c907045c0710340107240440c0d51068151425100041e000303800101444d00c11400c4604030310b84000c02d01040701a40010410700d8607507403244d4011580c0203003806071002814410000003014074103400d0040944102030700da03e05001040c0850054041c0100444410309016220600740d4000b0502d58070000103044602c98600c060344030f00802c1d02d0b5004031912454440c0c2c1c086984414502e40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 266524406 1250 266523156 266523163
    0x901030c1d130204110903070f081c020303070c030c06090b0a0b06030606270603091b060f0a030e0703021905040f0203060109030210050c06070e0102010c030605010e061c0905010203090609 83
    0x580244140d20b003080c01c00700500d03040e002983c00d000c1d10b6a580d800d16160b04c001c00c1c0342c5644e5811000402d10491414408030004210702c07071510f002105003124070300f4021030280d100d2002505c0310f400c108250740180103050180c002c2c104200d9102500704041130490801960b20700040d00d02c10041410240e00121515050042e0380c0507134001085c444c946000e601c40701030541d90076006599810042031504003556240c60246100340740e044d029012248005a14070f0300a01c07450001c502c102414000b10a490f00e051040e600c910030103050001d210100d1007562841c00c0c0703107a44025840900744a81012904045031641c040320b20590702805034500300051a4282d0008680e10ba0008070751000030000742ca86500c6c0c480e07286455082062034056243d942d00d0816030100c44110204050341e1200d95a540e0900c901c804080300c502c1d04001c003904060000b8028204c003601c0601c56900410315178500349203590341020b00c1c00103000c1003024004c213181c0a8080d4008486c40302d0680114400541d101c4c0011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 266525656 1250 266524406 266524411
    0x10b0a020f010908030703020c010e0d050909071106040b1f03030e0406090605060304020d03170f060a05061303060203071115040c051e0103020d110313150608030f07050109020901030c1d 82
    0x251207170945d66115000c500035000345054814564840742070421405040c00b100440b80d009580e082d9450120b01e09200c284440500950108010f410000c0628400441c2c101e8020b544044964101d03190514604020001500201c40050982c01e00104150b001080055404016182844410b0f65075141c10211900c9128960300080308100150052418400e40c8040d54403c4c1850701620400c041e0001071808201e1380c684d02d409800003404140c1c0340044001e030040c0340495056190510700104036401250b031f44001172541e0f0f008030100e0030032030103003030712240f801c108004031415000f08800d50445d0060599069860004071003004c2071506005010000074003545030409110554100110025805220380708a46035550210b401082c0b808001140100c040846460808030581000751080341c20642071100e0b40d1400100300101e9601100740c0c0d180e6000842026100c0d00c035410403e002d4a00c03c10000d50240300b640002c010042404110300030303100703841076084070b05008103003240410a05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 266526906 1250 266525656 266525663
    0x8060a170a060b1f080a060e010312030905120a09030c240513050402040902030912190c1506080303010905090304271b0f1101020a09030212010212010b0a020f0109 72
    0x1060310901062071a0450305114801030848400300c4484100584500035502c2c04c4800500e11030240140d04216001c1c0700c0180680700c17050240c1f945141d1b9803105540c08252450281070712140031206001003400100700b0080c208608a80d2100602d10041000101d4001183c034041a8a404600c0d055000c4040b4040301f12442400b040c2e10320842c05485030341041d08017100f043c126140c0818151114005800240790b000009601c0c9d04003545200e003041c145c0b0b103540003550828041c0e803118016220b6240519503190406610400d01400e1294401c2d81400e40304540c582050400595850000001c1d4101e42c500340b010052500c410703c40540300c3c031461080e600403d00c001c145440c07420340071310420034800040c980000c045030015800329212403510030700390209482a86001103560081c0120144194400085180c1409050050408821400040c1c0201c1e81030100091030402581111540711503e90480143d41e955102403031940d21440000e0014003500391a140c0d074101c140580c44131503a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 266528156 1250 266526906 266526913
    0x2090a0c0c140718021908041104020c030904020c030415020601120b090a02030a03020d090b0405090c03040f140c12061e10030807060b01081305070302010309030c0203010c08060a17 80
    0x4094881d8400707841d2500c0d0b811410b006820300081d0303080000812401034a020013000da1688110f5469429440801000c0d07000e2009402c02c2100240c0c03079075905d44138a00121801070715541d030700480310314502812401980051000594100d00c1d04008007400441e442c1d00400390400c0031000b8101d072129000c0c0b007070200e0620340400a10006541401c043d90141240044176410b61042c1c002034a0698010b43c2a00507800c00c0d40001d00880d444414080504121a030591400d454480491b10b0b0301c60003008051000008404901001ba42c2c402401501e504051181082585003898640300d00048030304030311903262100040c02050b00400e603644103d24501d0074882c0900208640c1c456030780001c4c1712401041e007030400880050718150203400f0050040c3d20000f40003401e0400900784c803001074081e0610301c4401c0688000030380c00203101400d0382d50a103800f2810720100e2800f501e01c031148010080d41542404840036540f58040c0ea0144220800c4a1a00503190340f82001016030141d1161001b4540 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 266529406 1250 266528156 266528177
    0x14030607091d060d080d05040b1005061e0f0304150b010c0f0b10050a0b190e0306240603190506010908070b071407063f0e0a050303090a02090a0c 64
    0x2080b00709480d030000000d4000448154541c1c1c807410180e00001c0000b41c0d240c0d0302d07400d21051015404521b40c0c81850185808100340c01c0100103601402740d00d06070502c10303030f041d244903546a2909041e42c0e140241116650b4486c1402d00d4030b000d401400c8455901080c0c642000c80c0d41035803141c0058019550404004480c041b880d449003171411100600340829003400b001e00051031303143c00308504003e000d284442501ea07016100131300d00545420044408110703c40701c80584507034020400c59040580000e240340300a8580404410440d10803d084d40d01080c0401040001613586c1da000c03008005000040000d0740e03a400040d5148010340c011003203240e011420a000c0d01c2c45480042415500840400301000c089072607440c945202034110100081040c0c4808140c2130f019019050201d4403a441c1c0b500311107206030003a024619088050b00255102c1101e0703000c1200522400c003c0d43e4210b01a290740e80790034a1820741d120460f0b50101d0107131905200107200d8028074032840c003e400b1030b0395800d072602 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 266530656 1250 266529406 266529449
    0xb03060601080606070201030b1003020904051602030a0f0e10030c080708090d03090809060c16080a03080703020702040b03070b030601090801051006030903020304080607021e0c0a0302150f041403060709 89
    0x40d0844170b4202d061503607580c000e0b12207950b4041e650001c80403940d80541e850009405101c290b90b00504101284120400c0400707200350048151b50501c159454a04605195035004607640c0f07030103010340c42d0480590901c0c0000e896240c2c000c1d6452034001e454103600c540f1000011140e0b414103c0744628503405c41d4607507409070780c800d4001d014864080c04086003007545100024856900124010581e035020181d44d600c1020054a180000c0041c8005800d2814090b24043d040d070500030b00000030143d000074010119a22588103048114001d01203543e040d459000c14403031903005407807040c040340d0304000028000b4014002c5074800e03007085054241d0709250400541c05440280c6c2d046081d80418040810f00e60070030410715210748a2540105140f85c0100942501c07242c403244001001c0d045110390040f241c403a4814441203030303030549007040b0300d078060b841c8028107000d104001061407200140014070005100c6c079a02080c0c600f00d040d20815118403905a5240129105108003800c0d044182c03100f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 266531906 1250 266530656 266530669
    0x9010e0907050904060e04020109060f02030703031523090c09030a0f020d1202071511150720032101030c030f0f12052101080703080304080f0c0a060b030606010806 72
    0x902903080550a03e1101000981901d0081d009810220f0441c01040250340e0f10000e054000d00c0a420009140f4030750450081d00e0b807151203c040c0c00c2c9915048000000d100c075920000081ca410146235402e10041312100c00002ea0907000b091190040c0c2d4003065030b103050142154414800103008048103012a618100da042295400345d07400348040c00d91802041c480355980c110320741c0715405001d015080007034490741d00d000062038108004403071605d106190b00c0062190424003886c1803048050392600c9007296a40700301c0040c00d52480b1117441031910000008050000c40c003042c0200090308a10182042581109200240044200c42070400119105000103101c05005148080f100c400b241c0715000300c404612000c000080c0001078807070140f00031503995400b042e680142031324117515040d00c0641c1c40c1c21a0202401c100c4002012900704886d82044614810625080c6602c03003504400894880c90552020f58402d82402131040d003130301d404211140300c0d0805031102c82503030301e038801444075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 266533156 1250 266531906 266531911
    0x71d060d1a0907140a1211041205011113030201030e16080a150903051207020a0c030f061d1c020f0a1b0602010c140901020a061d0d02030c03030402090601170709150509010e09 77
    0x5407241e0303540811088800d094024005000303403440d20003401500e458000d0850380244113503590301009000c1e0120dc465011702440840341c0920b804140c09040004131400d01d010404040c608000d0424000b5091001280440e081802074608a41641c40b6409a1040d5901e20781c000703000550401c1800004042006d00e640c101c041c45c41203940c2c05005503a803000b64455604141c0b00c90300320301d0400c0e0402074240540703c00481d102003541d00c42102010700d02d80d500980b002d051030201040314100c02540c0300300407041410b0010400c8130801c290f0b40c244400058001002e2400d0040381d0040880e1b02030050003140c4c039544c0182d0301c04124020200c500034094100420003030450041100c3e14000c50118010f800036240203805000801c05900d031030a1a03e0103c83d24042990010b1144d400384032008003e807540540c040c6c541e05202d641d2a070041b070320144518148240d015141090142e480e511004003410b95400c1001d900c41c10820a800b950765020300041103001502041e054000350410311501034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 266534406 1250 266533156 266533187
    0x10f180f03050c0322090c08040605060d050709020304020916021c03020c0f16050a06080a0504020301020702060a03020a091211041d07140301050a05071d060d1a0907140a 75
    0x1030400a414012500b59445a2110090175610030b50400c00c1074500d0081c103006010054041100700b002c0700c0040c0c02d0b050f0040001e81000d560740001040358403182004010240e0200950328802c0e11015400020340043d2804d030300850404000030a1010300c1e100749100000590001d018079070798000301c500c11039100700d4154101a003d000a08411808004804070010b246d0b020b003003074420700840d46010b025030f980402c1c0301c1c40c490b060421510348c11610098020302481404a6955518004a80603120380301009420060000d0032040e025031507405400203500940d116401d0301c0d600c50388241c80031201c0c00c010b884d40c040d44141c00386519040d4049034450036010000c04004248004460500482d41d00110034180700440d9200307146400c0c854540d20071816402000309007058800204103503001c1d132502d4816880140c50345255170703c620070369041da9200030060000c0901b403811b410010300c0b503144050181e03c0d0030b408103d1440c0600c100d4039804446200550070210494811140503c0c51840c01c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 266535656 1250 266534406 266534417
    0x405030613060b0907030b030c0915060d140702070f1202150a0e28080304060206070c050a0c0b0c0c012a0c1a030f0a021312240c02010f180f03 63
    0x9011901d801c840c00303104003006d880001d000101c0e84181400c3c0700345500040c0c0716075000e07030030031400c1850040041815030041e1401525074507813000c107200078090f01c0c01e800c4011080300d0400552035400140201640d50080841300000e981c4c49404440f5120394200030741c00311820014200005411015040034400c0f854018450310225011480c9106901e2840c20900c0040003d0715020f00c1540d01c0703100900300e030001949450f162550094440c440503103014200252a0003203130a0040070865001d41039000284210000e03503d0f2074841159110b10b40c1c84105000d181e440c1441903019851003e4600c0c1d80b4410000bc12041000f01e516075860a2021981960209004141000c0a1040d6290b0403408680740c1da40e81004829040c1640d0b0040c441c0c2c252038010080382c5400c030340304000d9100300d174104003140b00300383c50500d80400b001d6034500050004c0c0d441800b00c421103e0040d0001c1c3d089004a40080024840401c02c040a640151000d05030f900e6040809100003464003403250f0440c0c0c02840e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 266536906 1250 266535656 266535671
    0x2161709120607110a0506040209090a140307020a061107030314120406020c0708070f050105030717070201200702090f0a06080609010507030c0905031b030f1009060c05040503061306 80
    0x6904500c81460500807580402c0410035016004100c24081402040040680e07104564400356254801032000b030007038030810045440070104124400036980e00074000c2d10100f0a4216880d5241c02014059114941d040400100540240c032601e0504072803101400205042d6102500c1d0306c1005035402210a408203c411000001142c41c14000c5108100140e07403001c800c51020f1402c000d0b038015030201c0e0000401005500510b2010340c007101c0c02803d010703807a5954400e00b91000a8003003008040c4021a504002000c1e0303041d442041404041c4060580d00c503144481004c107401007020003500414480c01080b100c003402c280140e88100c0b10040420510344401d03080341007200c01d6808140c00c0c0e4640f420700034036903010700800d101550b80d0700d05003111900d400e00007940c0d003070034207002240800035403003620454a00780070559481d007008d411503d82c00c01105000f03006201501090f150701d850a00840f42141c4544c0444040b240001d0041c4002d4482641d002902d06000908595481c0c2d102c41 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 266538156 1250 266536906 266536909
    0x70608040b061005160507140301021c0b1908060a061401050f1c060303090e0f0c1605070515070605160c1e1e03030515091b04030512190302161709 65
    0x1501740c1042c40742025100541c903048081c101c00c18070145c02d0388280d00511402040d070b444210030500078a0701b50f202040203050007001c038100000042c550701d94900d00d01c0c0301045941d80044c400b80500e0094004000640e40d501004150f0f10200040500160003000013a1280349114041c010300006911540f80420b08420301004440503980100c001c1031103c4410440c40012820301944001282c054001e00e03c0e00c1002e4240c28401c40c0381d040740241d0460046800e0000c2085035001400012740781e004501d44c138164440094124610460f5011304100000e100141003045e04032542c409074440d5611740c0740c1e030781d00c807000d1040b04580070140c00640c04020011490120140b0220002c070b00742600d5036030007410010f082e614001d01c0130002a022840504840c0c85854145078081441d00d846082000440c402503041c4c800e940c8085c00714451b882070340e07080400d4440100349060713142d43c03101d01855030302c80c081e0168020b0f0b00420611140c0021010041100032020b19002c0071262951807034500d00e0310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 266539406 1250 266538156 266538187
    0x303082703030f10090c05030c1b01091401150302030613031101020f0403020103060b03040b180f01090b07030e0a03050d0c030204210b0705091e010302091c05070608040b061005 78
    0x3c2c1c450400380322007414003400b280c6003100d5102404241d00305000e01250940b01403c82d01c0094444503128100090b61b140210810944a5081c61090001c0c0310740c02050902060444440f06048400e500e890100c2420301d07860721a04003100c0d03002d40a4036203a555100c40b41040e00f010401030301448201015298064001e1000300350820300d2554168941d819800010204c5241d504800742101c41002030202066106031800d0348001d0741514100058488100c540c140420307000404a290700346040307a02040046002103105454a65041052110106115a950701100c1010b07001c0b540811841200701c413580c01008080507581809031926594110ba110741d510a801011850900c45212501300288501d489070480003a2a1090408a20034001030070070103118a4001440058040c05807140d011350180c50a40000500708030f00740071084820484d8910025044405001d60000412554080c1c00101d001e00e0300502c0303145666035a0420f004142c00718000e240c1c00d0080511007404101c1f01c030b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 266540656 1250 266539406 266539411
    0xd020a0b030405010c0921020102190606180c1205060f0a06031406030d021b031204080303070807020a0b01060c0201091a130b04080606010c1403191701030308270303 73
    0x40041d98916150602c41d0071241101c01460070003040c0b400420010340c04a80ca203c910441030b0031804014550720050b4a07104900401c0301e45038003607842c084184495580960203c8552402c0307030040d000c1c507802503012500300e4002c0b00082000d2a0340000c03108040da0040d0383c00071026211500c210700560003e9081242c507408000040d454181075101030544404541d000402a8020710244030b0b2508065203a0b107a141742000c0f070210841c0310507030f10b42e020030640358000b041021607652591178210043e140c1c0d00c201c400c80d0200f0610400724502c0ca1001480301100c0f40c001540400903401c141c01203e4900340307804140e041220b02c43c000714909a07000014804480700d1f005550b81e5054441450240b011036500191320144d003400204010140426003aa10107824030385840c07102103d1502007118060211418580c1c0300200725817086074500218403c00c004242c4031041e00114072070118841150074000100028445030200b40642c8880e121044e52541c401e40b10340b8550f194114203072458104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 266541906 1250 266540656 266540669
    0x60711070320010e04060f060c150603060b09010605040b0708030a0b12010c020d050f12072105042a09020f09032a030f120904020912100b0f0d0605060d020a 69
    0x31642c00c000b66810010354040f0200688003030140c185000c03140c0121a030f1030302c6280b050115110040c010441000b196000c07002c00390000700407080c0c0307a02f0600010082d40c108540651f500c9800070405500034001d0300d04584402180c40d00d00695030b91014002e41014010000a94641800052666400c10701c022205050000080c0e0848240002480c180b04a03201806120b8200410301c4101003603402c88d40d6460407004010025228200304446440500400007a0615031202c0c890340c88a1681100d401203000e0299082d6004c0c00800000c49401e50000c1072003031422041c81045541d0094000c0d046081c8401c03030301e5060200705804241442009284403254416003003c41c0b000404014000b0060341c1e040e00280501c5911a42c04e40d52114525041c101608021881c0d8400d0342e1a60111400c403100030745030906200d5402d49484c0c1d03030966580c0701c1c014941030142440f110304105c55071380e0540c00010041d5080d00200d4071042c0c001c0202402e9503030868404d4034800e01507100d0143d500c00800c40f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 266543156 1250 266541906 266541953
    0x61a0d060b15070302060c07030e0907030c0206060604061d1909020405031b03340b030603060903190c0f0605130b0f0f3d060e0604080607110703 64
    0x8010200042e100038241d03180795000040c0040008641d00042171580326401841c0d2030b5542c101400e080e01c1c010f400405056110302c030f00341040101ca40c5a0092500340300c4035002c42c1c80b26142c04040040c1c1d80281e0180780000b84101c44500d16180304117600449221000d80b030b00d44982500c02c203008480c0880d03082140340700c4d0005800c104900b0100004218516401a034145882807400000d4541403c4071034204003400c0c041e1212100d46e030661484a010b00780a664510140d62103180440720740085035800c0c468000d42e800940c00c0c0d41c000c81114a2a142e900b1012460981c0380d0082e82c80d44035041041d210002c10460410014005210721030148810081e0019445154a8182d000c1d02d001065400800c07280414400759070b0005100c281c200d00090b0040704012a0303a1005504105040428401e8280e03c018440d0451600400f030403d50b00b5070b0b44c44000002151003070141e0342c441ca2245405030fa00640025181c903104041d005141c182c0042510f14042d501d03200c140c5075180743c440b01140c032130 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 266544406 1250 266543156 266543171
    0x10f0e030f150a150e0c0d02120603061605041509080f072102030a060504110d0b0601020f030f04062a0c05130b010806060a03090b2508010f03061a0d06 67
    0x5240e0030306254070030202c030f90511540d0401500484000580e101d02544a4111801300d41100d40710803c2d05c1e04804201000c5480e800c403084032a003080c0d010340b045030203070003558003142003040d002200802c866015102d140c640341c45d01a500080c82c080c5d44180041240b00c080c0803800903018001c3d5010f043c02c81c001440b034681001c0e0740c1ca20440c4a40e000001000b03048642d07200584002c03c010341c0c1170f5001031000515980e2410548031a0505011030342d800081101140200445084040d015072400e03400ca4410749149000595070b0700c0380c180000c031207540602040208501c80c0021a0302000c03801c1a9061420801c0000801201800c10444100015910503c150b062001c141102c0d0304154605124014410001819844024210034024040010740b0501540a0707040140c8060b800320b914a0345160650380c503500000071303d000c1d140100c8440007a4199030310a08142d4141d50700060715a49d9a032640e980c2c00010544200c0c1c84085000201c550b808030703a5840015244507004000124408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 266545656 1250 266544406 266544433
    0x30312090d0c031706060d051303031d0c040b030c0904060204050103050703021207200a050a050606091b030402130612120f230d020703020f0105010503060114010f0e030f 75
    0x1c85095a0411540c0340c0000c0c0400d0b44004041c6003422502d00d4510036446080204e500d078821581d68a03149030030b140c2031024541c404e044030b4546a0081da000c1180303119150800d000c641d4003196034600c030781c40f0040d440c19919090b0300200d03000c20020200c440710384407080801e050709400c54040d1003166000c1020066075815001c0d9035801102da00c0c00310720303215180f050044280c4014103030b0780030801d210f02030889001d003612701c041d0b820941d03800f220454140c91a000e0b41e50300e90b040040301ea6001e01c50116842c0c1c1020f0040c180140703080710304009401e9516000b413034140c00c014801e90b480798032101843d00e0b01c140391041902174015010090440744c102c4c04c100c41d00f8140301a0308010810401203102d4115800008100c01c4440d81510340304074241c0c0002c0413075901656030142c070b44920004002003090380003d001e1804a102100078000b0ba070741c0f102056103410091183d108a2055152007503010741c800d6414224480940c10031180080501d400300e86070240e2400c0d4211a0ba000a0100f60f01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 266546762 1106 266545656 266545663
    0xb060a090308031b0d2903033103030e01080702060c04050402130312021e06040804050d14060c03060102010608120f1605100f11070b040311070503031209 68
    0xd807401407200600521700030b4107500c02070f07628020764682006c01250340d89200720014051428440c0c840c000794008034081c510000700710100d50b060040d141c42025100c01460080e618030080c1c0c0c0043c80050959840508098213640c485020080d494504d0070031201542c00a80b03025803204540c08070b030f420501142e000141011415650641e100340d0020364107008461404154440c0d9082050464030b54000352005809c09904000034005420710540c82103030b80d0f10030304413003901c88502c0404a040c2070040e0b400303e00307001000091113415a824003409019003580c501501c3c2811600b2489862440344500951080c2808624007010035142011441206d4100080d0f800002d281421301005018145100004038070701b0094250514048003594003141d4804586001600c031030300c080d103840c509003801100314860010081050349017840640b0800340e030030385080006c0c00c000400c42c0c02e = true := by decide +kernel

theorem cover : BRFrame.Cov 266366906 266546762 := by
  have h0 := BRFrame.cov_init 266366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 266366906 ≤ n) (h2 : n < 266546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
