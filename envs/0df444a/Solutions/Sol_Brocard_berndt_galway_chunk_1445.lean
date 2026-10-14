-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1445
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:01:45.886184+00:00
-- url     : https://prove2.me/submissions/e6b45d74-7525-4888-a392-3b93785250c7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 259712230 ≤ n < 259892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 259713480 1250 259712230 259712261
    0x20906010306142e020607110102190c08090904030f090e0f070e19030506060103110c06060402340b2518170d0e061606020a030617010f 60
    0x6400c20700c20080307201000e01c445004902803001e11140f00390f802c5820070341140c400f50420391100b2030744d4000e40f124015211000800c6000b030a02d0700501043c000d44450100b080e0074400590b080b100125805030500303e007030712240010071202c2c071075480780ca040903c55806629510f401135503401c8000d0215001da80004c82c2e040400b800e106400741c2d09124160400024a040303011680e48100085001000f108100d00ea096031040001c00c21402080c2d9a200344803d803010000c1c0101841c02070080e11070340c00c03480c2c80347e000000001c40364035080c7d01800704100d04001810120016004034011034640c414410240d504450004c8100165100266031041d21500c0001001200c402000c2125080c0303007102c0240041c01c44c0103510901c034800c5001c000c21001082407251501860f0b00b52300c900c090f586c0e00c000a0035250288009050010031114007810100019510502c5038903000001e42080c03401004041d20380000040303130910209030034a400031580000402244103020141120038804ca0392000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 259714730 1250 259713480 259713491
    0x1060503061b04120206042c10081906020f0d0510080109030f121413050717030714070e07110d0c0308061e060f090111070b1902010e070905040209060103 68
    0x5000b009403401c6a841d42c00700d05610b4401c1c40000c0e058003458000c1544a4150404541d824030030a001200320031208800d00c0c0c09840d004121010099140520303015540044040c691801d0100c0074409424000c0d4030050802601c8903140740303641d01402d1079401d010b40b03d000307001d048900300c044c000092070224000c010400940d038026062101e000e040c075042c88030141d4000ca036188180c021590041c2185500992840c0039955030032042400101a40c0300e201d60780c00400c120781c110b64021340b1401c01100075410407010350b890003242d91075a260721f0254010204001060140382c94040d0040d40107403102014098440340c0107141600403107801003009540c12a98012071f4119007100d410400079111000034050794400b00c651080324001aa4020300c2c00100701800301e00c03500103407000345000d82c1d13103c4417481d0b0440352039580c0016015400c0740c0b5004005683c21101d00b00500040c01e041c07070001045280d030800c901070410100360700912140e611041040210700e0a224001d83c4540242020000f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 259715980 1250 259714730 259714771
    0x5061f05061222020d201203031b12010305060603061510050d150603020306031203160806010215040c0608011205151e1f0b0a0c060b120a050106050306 67
    0x140703038030090b2444802c82c51041c0a0481580f080000c0d602030303034020340021750040040ca0300704690400c0c8485000c5040c1c9110700b941e00ca00d00011091900410800218199120f0f02484001460010708000041a04004900800600c64001d600941c081d8010700700310715141c41418103145004180d5210034844140c00320096560051200c00c021491070250345075002d1400000040610005440d0410403a17540061456810b800652207210280d054030941c040c0d40f00b00c014a4001034908010502559145141c0e091081010a6001c43c1c148102c4150307040540e140305205006a4040d104044148028041170740c0002e0600d00610000000d12088803150312240e0b00e403190740d0680101d2001540102e2002c01c40d26100c4c100c08c00040c10711910034107082c013454009400c2948074803d240c01307090000a42030940800e071000745604d42c484110040680e0344001c01081070713018541c5c1c88481c0d2210141101010018951382910400c00020303001e00342020185001d60041c8000d00346420440c0740c08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 259717230 1250 259715980 259716007
    0x4020c0a2616030804060f0212041205040b0405190e040303090501140c0313050f0d0507060c03020703140a200a0209060f210109060c0918050423010905061f0506 71
    0x4140e0ba0301480c05852640f580d1802c0009401c904690a400710300200d00d07184600200c0380450b000310701c80c00061003600390184090328140118032550718034040c00e01c810002030a1081412001c6100980c1007441691103140c1341c9000102a41c080d0000383c1d4a0407407000300070b001d02c5000442c50300c0180c1544141380081408010b488001c040101e80c01091640504001042102c41ca00401003425510001c2d070040c2d004029802100042d035070a0300705490500c0384ad02030710031a10103030b81540c0c40706450340846002803420381c0041081010040c2e19411244018913400f2400805081c0341c018200a904600410408903c00360810384180000e500d4100c0554030080480e038071034105000b40c2c800c40340641c086401061009409401181031007040a14190302049c1071040d10842040704041e030403003a00ba60122001240c0043c0300c14840c84041909420b00c0000c00341985407000041103c408030b994a80c188103041ea0041000e10700d209248690765000b020142c040c01040d2092400c0003102507110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 259718480 1250 259717230 259717267
    0x12309060a03020d020102160602030a030f020c1207080405210c0108090d0c020d08030a061e030f060e010f0609051905090a0209070908070e060901051207060e04020c0a26 75
    0x340b05591300400b00045900a0000c21f0382c4034100b00c0b48521a0759141c1d0060746941c4141c00d007500280c5040c000340408a014800d072241003000800500d480007008420801701d900c9040c09889840301800002039aa5407402c007900918699000c0384607c075940040240b6101d400f84a05040c406110100482c680b0001000002080507160085200c2d1260012039500000c184c0041d2074207900004011802d041904158115819410301716900f940048400d0001461030000401400308442081d020403100e4000521642e55003000081d104001d414134011204c040d405000502d071943e0411400003000d200c409002e2025440c1803226103420031041e6201d65420b00300034460900c0f032022640c2c1350b114004074405007070b4050858202d1601c410002c03480c1c0c58102c840d540f0840c00100086201d0500038010080d50141000030110342e400c100d41915006024020030341c22031b40c24041142e01040810045181c14081c2c602242c01c030920081c246000c8501148180e00100204900440c158414086 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 259719730 1250 259718480 259718483
    0x90e0a0b04150e0307120f021b300705100306060903060504030507020904050c0a12080d0507020c03190204050a051314030d020703081e0106090b0c0a0803012309060a03 74
    0x503901042c507500c118024030500e201c0c2e507a1840003045c0c41042007000c60820034244c0702c58403514000079034071100b2070742c80c004045502030024421800d000c890605411118940d1400c2940740f140700004c04911035002d100070b107038008650003650104a1410b140b040004428407038501481290309001001d03240c40301520000f043c080d41e84000900303042c410320075034885c154014001d006504007402d00956884014040c14070402840400090143c0c9074034000c200b09a21180c5a030409400c0607044000708001001d0302c09600034030000e041960703001e004900510b008034880e0b60390950300d40140012070710000c4c40062a240b801e4144016007145030200c6a02c1903006070107081201d56480d105040d4080c200c01030764110300226864080581000096103e00000004d503401c00440c5d54111340d40810a100c0c040c040b0740194410b005050701c0b10010070f0421101170031224120269a00c001c0c681d8802d80c041c4002900c5141615100c8c2d045180b80a80d02004403055141424080000350310541c2c1440f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 259720980 1250 259719730 259719743
    0x512101104080d120f0207140f010b09060904030201110c030d050a05040c0b070620091c03080115050c030703110f010b180411131d0708061810020a09090e0a0b04 71
    0x41c16050442a604500001c092070007040d5224146480d12103001400d284283c601030040489c45035000105109018280f00b009040c642640c640301c051003880c620241c0180c0465482d50507510b42148405e00920310405268011680c5c0e02000c0f91080843c1c001038a8103a68900303020501c1702103180d90401406803050a031a09513140e00d1464010010400041d10214000c0245d40e24101da00c40782d4081d190090064901c90503070b0b100f2a10300b0f006483e050100401180700c000060081202070542c4800902036410418500340114000e180b841d0010703c03049001030300452440e40f509406201020744a8400e000a01100602e10b0008189000c08200345040a6986e00001c062151a40c0140003940c030162601c400b110090b81c8141c068034001614004201841525141c07048001031a1001c0742d0b80200980116160948501d0203500b5000d081e00d440d2095204030b2001c0b40851004150406058071450140391038080c000003952816403030342e10107400c140505000300c0d1240c0201c9510591048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 259722230 1250 259720980 259720997
    0xb01080124200a02010314130803090102070203100b0a060f0804080f0418061514091e060d0921120f0f0c02060f0a090f0b070201060512101104080d 65
    0x8085a0070b90040c2d1004560066801001104070780100705840c116000b81e8040c020360303a203000480d84400301a500304500c24051028a0003188c114409140c01c068a0710025207001110340009160401ca407050b4011607075101110300d40c0e450710720311000041c0303000d0410a841300340b40030019048140090002c2c00c0001c001595a03a403c103d50100d0300a4650001032003e5580c50103c070000408050003134441c841e450400e00c0030035030b004070b105090b500c20300c4080602d010070450a100402100308181c924680300c031110380d02203680d07100180140d044001c8000458002a06005070303401c20000444001403041c02101340000c0d440f4040b00d8000561200200e00490010034023001064942d510038179062424030a10105030307021680301e0245180c202000070580740c0c0c0100d181150189400142101340400d401c00000d030300184200c0c0e0200050000240e0b040d9168040340103c18820b4640d40c05400110429901050507c100e114040c521030500d807c060900e10802e507900443c464180600000c0f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 259723480 1250 259722230 259722299
    0x6030a08160f0b07080405100b0a0524030f07141810111b36070302040b04030b0919031407020a08030412141605210604150b010801 58
    0xc9000c0d07007001da103e030800950b40f4212800804981e000c0e03800311158000d0840d80c20f00d8240c00c0c000d00004190050036040f440345842e041001046180c3c50f18044036064019030081d0001c01c8020310b202d9801781045a81920b00b0b4007000b040200d0b245040d100b03804090101c4a5116a200200e283e8541c0c2a18400040b210721201640c1040d100e1040751901c4c440d104a10100344c400b10a0300442d46000e40d41d0380038540554403423200c407200310780e400f16084196400d0140c246080c800090b0304200c0c542801881d0035141d1112a02560107900f0550344020b110307080c01550b09003001407030210304030b003051401da4407000c1d5002001e6490080010000810110343d4209654481c0d2400e0014002141126070703d50b81e0340c0500030040e20030313401982d50b0090f0b80a210b01041e800b142005c1c1036048800340045043c1801c041020000560b0246900081e000703014884501003000418003072402400080c42d0155114100c5007581c0400c03148a04010145004111403014013110091142c4030484914a14120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 259724730 1250 259723480 259723493
    0xa06081507141b0a1b0b09030a0303110d090c0501120b0901050f031e0606010f0503040c0e07030f090b011703120a0c0507021012050c0301080a0204091502130e06030a0816 75
    0x203c003041c01d450040c40110000c00502240101500a6080b07a02092903550301700040140910580260903070030520304800000d100394844a214088540135500b00419403191101300c84064034115100710051009111660f0081c00d0000b80740c149041c240301c0c0c2c07520180424842441841038034010b61788204400882d0382e0500c001421604000f440b805081c20720038030700d59100c3c41514502d0108540d181c00c2580b071881903044a10440d00a905194402d240c000b003151310b41c41c010454400c1569076041c0216000c00c6008030004540640b07038044003035041c4030300d020310f401134510502c646920400c082d591500390780b00c410354084141080003c0800f00014107507654440c0c41c40c002e40c445c60302109050001d82248078040841c5900c0810006130382c2d170b0101000750384000e0140040d20b6100018450040c80c0c0b60304a100c0c27091140e20414422403200c0300c49000d80e008200502c10400f81c0d01c00901c0b100c03114004599101c20114014038101032191035400c0b80b482107159440c144c031851050305007030000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 259725980 1250 259724730 259724767
    0x311040908041a030117060405210d020d0c0e03070f0e0408040f080a0605070203161e0b012d0e0c03041a0403052703070612140a0608150714 62
    0x40e803e04020450481c06440e480c4c1c03007405030b94815040c2c035400d200800740011700b007441035500500402643d10400024452418094401d1211b0b0000b00a000f0207010107001804c0500c44070326000c08c40c0800085c004d40300311807819000740284c0c401303641040003803100c8d9440c20842e140400b40407860380f6907081141d854410781c0c1085075411101c10300010346010001e242c820203801420104042c0d1504401203882c0c0c440c0801c1c1d510f061548880388004240032698090b0f90340300302403031140300d1801f03583d0740451000264030407201319500c0e0040c0122a20b40c049074414907126036041303200150406a589605172401380014501e410081300042c10041111050a4400c145400352122854545001451580040002085800c00007002902082e54450025110800034003801c0e5150602c1022504040350300c18803120030b034843c00c0d0118400102e0407403a005480107080070030350509003884d191030100e40042800041c19038500304144564408040b090b00d68501910300da9503040d443d010941c105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 259727230 1250 259725980 259725989
    0x90305120f0910150302041802010f050408030405060d021b06100603151418090102040f09090b06040e01090204060b0a02150c2512031e2307020111030109020307020c0901031104090804 81
    0xf0300d0b00036030340e0a82c40e41040c0c03031042324404d903184e203052412400304a44a0051b032050155580c0148000d200c0713454144d000d806036000303840c0011709103400c1c0ac44600400411109030f41d010381095040c0b00b2240361070140c50380a4906070509118050f5166a180802607987c403415003001d40800149085640f01c40040c142220100c0c404015400c0c454a024004d500a01c42e111410b0701c105c000183c0030025000380442160000800c09003961080c0c00d00014142102000304955a183c0131400107175203511a51001c1d04040101079260403070103c02a00e4074103411400360014070039000b0000e08641e50300850704050203015010507615800e0a48500742d20320305c6002015015500ca00501480d4183c1c0421450250b41200340303952060600240111846a68030342c061303014680c1c119103c40003881e0442d82001461000040f5400401da010045800c2a00f022040640010070311010f6941080340300d2030030400f00d1320f0708241d501d903a5584202c1c45028581e240a03d4a481313a050504c00d1003002c1d1002030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 259728480 1250 259727230 259727239
    0x203071703010e06010306030503090f0f0303122d341e030209030a0807051603030f0908010b0d150e03180103110306010912080706090305120f0910150302 68
    0x280414580d10059810034090300d0300c1c6945860009500c2d62003402000c04072904140a985011220401d200303140c1c0c00a401140c005c0c0b00148401e031f080d241000200007064600c14a00e48500f0060450020010340108642486c00305203652010700801040e0300b90040b58404903500e1408501240800f2103080c00d2803121500c0e01e085400140c560048003011510740c3d0892090f04940303408200360200c0c02045400c0c0d425510100001e00080d038a600103003a441c2c011000c5982c5080c00000480d900d00c881d800840000d0781c49004520081e412071505006400050000e0022082140108850701100c01011308200340200106503120201e52004030804488400d036580d80c09803180d90f1034903201c2048100e0009245c0a0503110075100700080c0c0f401101c050355540c1020789000c08102c1182e000b01c0e0162030f90301e020000301c0000f440358403944111798840e840c2c1944034440b001c0344c2100300c40002c280c8244100b2190402086801c0402e0b060400b1940b9034000441d5003a04100d01c2031500c0c0c0d5040250030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 259729730 1250 259728480 259728503
    0x60c0a020a120c14070f0519050904030302120112021e0103020c06040b0910110405061b0a061a0d030c02010f09030f050319140a0c02040f1401031e21020307 69
    0xc2d5074800d024180c036502888000210f1203410100a954100d0f074404d080c07940c410400107002c2e43c503018844550008181c901c40d0901d984a40006810b54400e860403400700e0360000d8180231000101003006e004142e0344c02c0002894034681c000c0b90008001080c13201d651003034004061003580c020b505407440e207104030040b42c0c0c50340780c02c2c586195809415a80000355101d20300003000700726228000d1002d2030406403020340c1058500b2041c00030942000da44445440b403241524540440e04000c0072510b0b500410f40413a600304102e80b184140580f100009010701101c000d60004640c220340e803c003590340d083c6000c1c0000308004208903000062a04003c21441d410000c032414003800002038040044800d0040d0101d103025002a1807070340201840c50002d41e801e2001d42c299601803903000e41c00e01e001600214a6991b013910180440744ac1842000310101d41c0001841403013040c11502001c00d5400740741c0040511113456441a4500d144100760680881400e0303003c11a00c01c0c4159081141d000307105090 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 259730980 1250 259729730 259729763
    0x230114040e0f0405122b02040e09031809060607030e0f0a091406030f060712020904020307020307060b2403180307030504140102030316030203150a09090b01050909060c0a020a 77
    0xb4142016203007a0350b544141040c49101c000b500046517400a00150341d0b01d450580d0600848941504d0401c0c5c1e20000d60038040001d21071800e0040912074455100515602c00201d161903d6219070b00d4a0280520449420084151038910448018a402d400c064221030340c080b002401418a10990581040c0d00080004130500703c0e4000f800c00f662a04800b1806940303c400b4140d844801d442409560303400724000c035038820302502d4117101c40400350802518080308031005c05c0685c0d00c26182c2c000180e200103032802c05c0c040603106840c40500122811070029030400d13408400d030400c0901c4507e0141c0e0001c00b08101440c0c80c6c039500103c41e0a00240da86582c0203040250954016114554918216170900710066202001b240d01c10480607181c64144510010118000c2d040181165201300b050481042c047c0c0da40c0802c1c02c0181040c2c08080780c3c0f0303035551500c41e05588043e41302ca405480c41e41e060081e0f50b003020540560000d8000c0405c1e4850b141420120710705030f1a000058000c0b80852000003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 259732230 1250 259730980 259731001
    0x9020406031401140c07050d050c030c070b03090607020d05031501090e07030e070b120420030a08190201090c15120f0c0f0f0c0b070504031401060906230114040e 71
    0x14180090564082c80305c0c0d4030340810314003e2044600c0100f007508034461074181b190289000d0302450040000b16420003440c075a1807807400499420101d00110080104515031ba000c114451384070740b180c400f8041240894401422a00010303101d559403819000001030300d0307441458241d00a18424040d90004d0600040140092080b9403500039203010700d5a0218021003100110390407030144000c403541c984d84680741c030b008104010614030440d00c250f50032404940e408200c141c9031213000d0300d031003039444222001981040a1035940701d403c0d0b9060041c441c3c0880c15202011003140d602418145480043c400122041840b02c08441c2210b8501a000ca0000103c1d621201380400d45441c1c0e031801d000c00000030f41d2981c1c0c54100d81d400180300809210001880d103400950072600e64100302d0b00740740c1c580d52108a500a0300b900c904c90740e9901e007030800800b401c0340604001040c41c004115443d0384440c0f00285243c01810200c0d040c0000c0c501640d641c0a028411240100041c4036a203040d400d00d50040d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 259733480 1250 259732230 259732241
    0x2041d1203090a083004050c041805010f0c1b0201020703080a030e0607020a03020d1d130f0f0911090115110a021003020d05061c0b0c13030506090607091809020406031401 75
    0x405d56152005905804840c1401c0c0140100e80040c01024945420303c2040b01415103c80f07250070700166840c0c9040040d0b001d003d03001040c903c5200104103a040302070000c140ba10a022541c0b94403680055440142c4d0700818404203680c4c2040d042e075590780390503800f07034090100310a0b000510301ca6030b030070490140c1d4003045036400d451203a0300356a001880e054003242c00601047c4a030940340c901203456000d510f00310088064045800101007010015107100002316002000880413641d100c000a004204030000102c0c00303a101125501e5107541014055954061100d041000f4482d8040d52089001d00c104100080e2580c0200203007079a9600c803c000700607401070410000f0749030504010032010b14060600c41e40400d28a134070340f45588202d440340d40001d48041c02802c41800300700010003620300d480c4180006140184010807850600121061500c0c900034890010000074007401d01100c4100000380c045c85082520100f81c2c01d0b024000540109903a0744000d01c4c480301c500347d0000324181034214 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 259734730 1250 259733480 259733527
    0x230a080703080318060f060d06140709030c050a080a0210110304120303050603061b0a0e45070c050c0915010e0307050d060917030901020702041d1203090a08 69
    0x300303130440d901008003a5110301c02d9500c00401040d03a000030fa282c0c01c0441c000100c65000e41004100620ba100344513210342c800307031440700c0010b00d80c00c800d006110700322019100824003030300c4801029140c101400d4a89034100c030001c2c0300302110342d11704031407d01c1144070301a036203040400e0343c2c2c1d034603030b10315446200c0c45119400720042801d080004034603140104d0581d10400c4400742240390310310005104001381c0d0082c0400802d0016250804900d17480e40d100b024108014803140049134040a0307000c10085180b400402d074280402e2140585e2341080f40721881e01f200c5075080200781c68446141c801c0c1003e4140040a401452034810454500035a070710b80846054207880b1841001089002d06845141500499800075410700044000502903441075a106005007030414054504204811f000d0380142c031059031581d00801d000c001e41c41c103407080203a080c044000d001c85010788058a00d0300c2d1816400c00c4061680080005400080244441840c4960040c8a90303a5200d11550300c10066010100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 259735980 1250 259734730 259734751
    0x50c06040b0c3a0527100608030a1103040609090f020c030703181505031f03021207031e02090402040b01020c0301062d23040b10020307060b0307230a0807030803 71
    0x442d0710f40304803901c510303400340e1840308104400d04d003061203000b5103001000070310706036203d81da0307107111003485074403981c800703048190060759990340140402001420300120b292610b1704104400c01c2a6a0082c010000321303185c040c000710b280f410400c004030080c0aa240c0380c04083c0070001d141c004140c0e1141620403c0859030321810500c80e01d41500b005001000d042c000041001000415000100c00307600c910b174041c0c4104500c211607242d902140c0b400c0009248103800b60b2000000f80100710f04400c0320080310001d0107203109002074a0300014540203016001030300031036440c080030480ba4406c0c0004001c0704c1000e00240000c030380e502d068002034070030300158000000100070f0680900c0d48640c0064110b8001144460b203070052819502c0840c07407131050256100d5540d041500041d240c00116010401d4140c0141d61501080d0410006448620311914403a800c00321051081300345038640d40440803c0d02d00004a0710b5406004280c4140d103903040300c05c041c450a24000108182c950045200707414981 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 259737230 1250 259735980 259736077
    0x10031d01060522060506040e0406050105030303071215030b0c040503010f0b0102030405011812030522061b02040207050105040b060102120403021503090a0c0f0602010c050c06040b0c 80
    0x180018221009801101d6200180442e4805040e6440b400d60040082034000050781c0c5544400040956000354461904081c0c1d9504100c1072000d01c2c841c3c1070041105074061880c601d080d02d0b0003002d0806000aa8030030f2565401d070400c401e5440c0840c44e020315480901c807911070510b8003450025030450b1203014031075030038120b11407103415aa0103034140000d4107030021030a042c01c10b8010f451420985042d04c0080c100b4950003c0c2c072024200700e6a0ba61030290b100d0355642c0c0402d40c031080c0c2140618501d40300d01600c0902c01c200059028100031152807156003201c58915171440010082e12031110081c0c490360914080c88148490081c1d4203014000c240c003241c450510b80161140345010b244001ba41c86001c25112468400404000b180d00464210954400034459076419400c108950031400e0101656202845080d80910850700d51b074115042c601d09080c0c0449865135106401000141504c1d24040403803510407800301921031850684410000b184e4819810b400b0407641c4d92502240c420181 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 259738480 1250 259737230 259737281
    0x1401230406030f0b060607050a031d060a080c03100f03080301050103060608040b0c1c021216111b010509060301061706040606020307020909071a210c0406030b030c1003 74
    0x1d00c540000c0b2a80b061a140542c98903840e0300b03e450800503d4141c00c0842004503c0001d0003c0c840e092500b0311070b40380c000040c900b03916241040d8084140150081d4410456656000c0d007140c40d01d980a03048601d000e680b6034a8400300504034043d540070000e00c40c15144003000300f220240c0690305079002a0fa04012940d501d1204030f901d10000c0c1c9008d4120030491002c190700d50300007002049002005006102140c0c0c03800c588104981c0440c100710902401c550601a000354110040c0c01c40628521707141140100300e150351512010b148203451001030401c844c41c051640903006130f40d0020401091151690307540d0001800312405916a203040180c02400281c4500d0a4030800003940c940794001d41c2400c4080d4284802e120014007a101d443c070a801000501d480c0383c01e94a80481d0712143c8040d00c1c0c11040754968080c409082c48682240c1009040222503400141a03500305ca4881c50041820110800444e0903c1c420039221600151040f24010380d4a030143c000d0140c00741e44c01c419841441c0d04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 259739730 1250 259738480 259738489
    0x501140a03080703030207030e18070f05030c0d05060a0302060c100f060f06080a06030b16180302030d12061a07020f190b071407030b1806040206030402060c01140123 73
    0x39010040003481e080c05100f01091096001d0501c0078401c4c1810389851310170f90b0010b48441c1401d050a440400110200301e07d581e440440c400f0f0200079428aa8290f080c200e02940b281d00544150700d03281a611800100c5694900052100031030300640055038070205c07032100c035454a00c4400291510346c02e005c610040d03203110b44103500c1203c17140d90110301540d0070050111790040780609030140040d110040031000c43c1503115514012600c101010324200140c44000d82161048640c01e20400c44902041025840c0440c9002003401a890711050303421032407298400405560b00b101e10009050b0800d086171888540c01808074034021101000800402020001512466240074251004402041020b075618002421051f482078106001182c00140c2540c5000090f034000d0743c1e1000d6400c180500d1003540f8815892503101e140241500303141ca034000c10403511004e0402405240700240d050b0081e2420b50044041104c61106030000f0b59603011052000d002c221000b1f01c80104c86496991f65142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 259740980 1250 259739730 259739749
    0x10c0807020307020d080a02010b04150609050a1203080403140a171305070504020f0f1201050a080d020a0b0703240503070b0405150901050702091e061008040f0c0503030d050114 78
    0x280100100c513451206d5649440d030360008004841559220200703070034150340314011000824a02c3d40ea084d240ca14191004000c02841e5000a01800003100e007481032402c00e00c140110290581080340050300c4038501111881600160780740d004001096103d072a69000142a203254810444120151035449800c801d513080090028603a0b84030b03001c10045070815401034100348042c0000c09040004c800100881c0d50320507007104c4002e1740c82d107005201a00c0c04921030409046030b038004240788446020041d60f0b40c251240040d0003814644000385000740309820002e079400c031204540741899031303c0c2c81c02c00e100e03600d5010b52071190080200120300d450b034880c244da0403288018034141103914080d038804110761200b01058100f00c0200403010141c0c5030300e610140101d01d80050060080d81309240078181003005410340380b00300c080c40050781415070302010700c0d60410381081440c142c8510a2920907a010346683c04183c0500010404d07400c1d102da1036110904a0708804280f900007800c8004100100c80c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 259742230 1250 259740980 259740983
    0x9060106170c19020f0d020303090d02030f12060a0f080c030c0f24071e03090501050f0702061c0e01150f051f030f02130314060f0105151902010c0807020307 69
    0x10000d01089002c0310420a01c14040101401900c90f039030b0045c06000c1c1490300101541015034400414024403140400c1150103200a0380302460401c030b0300e03a07400041881101a001c200d10b10740303000b040c2030796aa402241d006060441d00100d034155148116078a5640007c541b51081c052510345290904112007003005030803000b82035414003006404020303a03811091a8002d6007440c144040c0c4002840760300300c00d40c40c14502242c0209400d00b4940100045c0c1c1d6a00000e041010078400202030710700c10310030381e5203480d811140070740c460316404d809409a41b484025201810700b0030201021001c81076001c1071201c04000865105070791907450003074050b10300b48102c5130484802c0302040f14441c600042c04d010303256545030126862065010b02d90a0360080d8041c070340040c42c00b81c1c0c00c00c10400d65101c01d00c140f444220160100780351401c8940e110b180705204007402070704031185610440a58100303c0305400d12a403aa6406d091803444000c1c001c1082181032800304040c0c0010503240d900020035103600030b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 259743480 1250 259742230 259742251
    0x110d030507020c1f03020f07080a02010501030b07091404020705030909041101030f1b050f070f111e010c080c070f030605090705030601031104150e0910050a020c0a1403120906010617 80
    0x507405004c0850080d8824440d032158400188002030014550303000401ca030210a500120b0b841d411801c1207c8290000351240c0180150800204552055400c0c074902150088030016140c415030700b003030350031072140c40d4450707a000e280c9104200400c009000103040b5494207907820070030f8403071112031041140c22641c003569a08041070030b101c0319544580d000340303031001902c0e500500349007a50351040c40700a02c51008035080b1403c089000094101460f006185d401c40d41c0744a521a02c060b00047c2c8505c111002c05401c03103200180039413039240300300950740083c16440a0300d80c06541d80d040c4400206026a5850000d000d4507900003a94070300041c00d1816a90041002e07181048003078200001003243c402e82c00c030320b40c0d0f10f8503000983c0c00f0481d8041d0b06c1104504051300c1d071781c0087d0100b2012540d0090451030100d00c144500350000078009002c0c2605035204129094916581c00546e01d103000b81e40ca040103040c4008200100d0007804580386048501e40d0315001c00b55842a0343d12941201c1c22105000740 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 259744730 1250 259743480 259743529
    0x105090d0e030304050d060911030a0b0a0b0a0509061003200d0e03120a15030f060c020705100905240a051b060c07060506210d08180715110d030507020c 67
    0x200e21545e004811503803084a00109c1540c00340c000c0f9080100d8520700f030f22081d51507002c0000d03440460040007484081244e000c208142460b000030360068020f0415809241000e014146c1603000381e0104020340000000c003505102002c501711b043ea0700a100f400406810704454800020002040e0b5000d519640c403400200d82d02c802450000f46881e695004141c04002d10000c04691050310300164603004507000b00310902122006441c0c80c0065002602616440f1700140002754005108415504120340b00684800d0441204061844001034000c4824001a00b0000789401c0310040010412000d01e800c20004070300300e400e07107802c8101c84201c0c100e04208081c100140e0254401c0c0d5101c0c0005011890045407040e510000810400201d0916800300704444d90450b000b502540c2e01c600c064080c0300d64042000034a644400c201c0c440e82101603000b641e0307405040d01400000e120008080200c4504a50580004001d4807041c2c4000000d8010601d000015003400c0751030075248a08400d00034a07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 259745980 1250 259744730 259744733
    0xc05010503041a0703021210030803070e03010902040c0509190e01030f02180c0913020f0a080907120f030f02010207030e0f04020702150a0806030604120c0f050105090d0e030304050d 80
    0x10603900041044412a000e040000481c143c8a0304460241c001550010b071900c0c003925007501d518001400e60002120354003010400150681e00704c0b03a100c084d40c03038681c01103141d910209000d441181c2009500608280c10604515401006804078510440e20200d06000f4040582c00c104c1c0c02c3c0c0110000e0038001130061000c902c03500c000003e8944003900500c0c0440c04442c4100c130045054801a084400009542c02c541c40c10f030f14040f0200e51925001c625194070313a841e003034961013002d24074011300c40c8420001d48042c200b4080b0030000c02d4a81c000d025104c82d107103080f01d42030248100c1200414900503010001ca4814402d540c0a2549078807002041561034040000c050390009030741d42d0050f0200f15110045c1ca510070400c0d80c0c6c80c0c080f04600e44a0200d00c4020b0718011005103d10b0180d400f0001300004a03030101104441e0000310708000303009840904200c2000e400210024080d50f00707140900006410000301440007580b40c0d03403486c601506800406803079101d075104086d400f680d0840c42c08d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 259747230 1250 259745980 259745987
    0x1b03070632040b370e1f0506030109050708010c081b09090c0c1006050906010f080a020c03041703090f010219230109030507030807090b030f0a1512110d0c0501 70
    0x107420044580c1e407038038100321013013402d141c0089541080c283c03062040714200d041e00c0300f03004224500c0b20b0b60000d0249200d4110b0a08181075401c040c0c4c102d0140c480c40841c080d85c03401e5009108a5401c0410ba48280c2c0c0c07100700d82c601800c016201240054542000541c20180030901c40c0f074800c0185084903d0500028100100700b81d015058003000c2c1380403c8000f50000042114594480c600131020407442d1800342080b550740c4000f01100d05008200301ca0842891703020b103c003a03110141090060b00c4100410541d0304d5401160086170a558071961b5990103440f001001d00021003040f80c2d41c1e1800004c06004984665050703518040203e5001000c100041d00040801001c88140d01c0303d280c0e01c80c41d40390307407030a40d105040190003040c0c002503e42c003450360003810281d001c0101e00f0803414003882e282003903041d48001803c0d40d82c070f4108503011a4001900390000b0005a60419189441a46900d0ba9000c1521403a4088030345440485a105031401c0010f00c0c0111260403490340c09900d49010b0064 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 259748480 1250 259747230 259747253
    0xf030303020a12061715092a03010c03062313020c0114010b070b0108030c0706110307020a081f05040816080c070e0601080705130504021b0307063204 66
    0x307400c0c030103c440d40801544580c420f400041c89882c4c0110019140c0c00d209504000f450a100e4002c42c22800410a11a02c0080c8117462113010b240d080e00c8101402030188410344401d03610a1740365082c8a0600c5080d80d0507003154081d10001c02161043d0f440c140c3c60100e0704111707d000c0a410450418410415180960182c0010442c09001040a18400e4846a404c600903041032a00f10400302d010f40038403544c0d00e1020301400040300118a17060202100f02d5035001d06100314030400140340440c14628405205561100c3d501404c0c1c120303a9074035803010f01d40b503881c900c000b00340d03c18103001c1011500080d070180900494111020900d80301001c1c0108441d0b000c42c0b131040d140d011017003000c0c0f00c23210010440b4900902c001c008201e1607003841c500040c01040c01074200010403a003800010074074206104000100da1040300c0040e510707201d007241c0b141482407030381d4101d40d540004960750042c0f0540b5007103003242e40d103a0080c605040052580d01c0c01c0560032055055000e030f5007000010000b0303582d060300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 259749730 1250 259748480 259748497
    0x4030e0906060d06180b090103030503040f140331050f06030603281106030c1c06051005040306390302070605271b0405060d06020309030310050405010f03030302 71
    0x240c6400c104040d01c0c41540c85540c000c845038089200100580405d80c1b05800e80c240c402c0310305441c25451502c005205000182000c0d042260007400e0904100c1164102d00426031400d060741d486000c00c80f003405013080f100511a1601d11840503460105c06041c2e414800d958005240e428100350040030b000454000400781c036054490103980100785041c1180080001000d048000c103481260702d03118810306009004540074207424024011210541c0007a030300d43c035100c1c0c640043c14540e03001005018040b036510180d00050b61101c00840540d0000c01802900e00410301800510510044000d0050101540182c10140c1308801502168486d60500c401d0207030f450054101b20240d103501085a90030384510520070a0108104041c6107000d5280da40401110041c01800e0f005d41003c00c2c0150414209520407a07640001404c0c0d559081039181c02103400c44411512460607452807640e139030043d200005607100d11680008c440c649030140c14141e40d070707010042845514543d0190083d4008480 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 259750980 1250 259749730 259749739
    0xc020c0310111e0d06060c020f0d020d2906030705010e1c02130f0b0405070206060d020102160303080136052205060105120f0604120c050318011704030e0906 69
    0x48000c3c40702826504a075560032800d445580d251011103980c02c4405c10340c007620611106010f01c00140e07446094912043c0c8044c1c42041c2100124800a4001403118100415840301c1803c148030543d102c0851030310701500750b4407550030758940408140d501d040c2031003424000344003000e00842a0810420a04011100594115400d403880c0c2c000394503412401150004e03140d0303d40190030386d000c4038098541505801d6604128606081900075160b0700e005000354010340c1d20502400442e4400c008105404c0c12025032414201e0300c92070010190f4400303118600600007818000c914441208580402400300080324981c40c3e0351074a00f4001030300d0020301c940390110480702c4c2e80c018000c95a00e06506a8401c402400c5158186010018000d050007108a600d40c045040e41c020a040042d90a410a8124040040d016951441160300f42000ca000400c2c0d0700012883d003224070324603240a502c1c110240c99800c2100c50a5002c0c1ca1030010441c1c01070006245071103611150305145481c940c004502a2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 259752230 1250 259750980 259750987
    0x904090507080703080a09050f0a090c0908100518031201140d0609060e2401050f150a03090201020c12060f06040b030a0b06040f02071a10270c020c031011 68
    0x702d01c1c1403102551003a1240da1000880303404075540196070700c3c003a0404480004ca800300f180c0c042080c0034554041c0c20034a0b50345240e204000390007000082e0080142c0000c80f4400340b4881e00502c05030100781c031426440e108800d4410b02044001c000e8404411100c41c44140581c03802c0c030f80030300000800b81c6c041e401081c92441c84010400a000b4004958042d15004c55040840000d0b6031412142c645014182c0d0a2514008000749101803400c0c1107503411200e042c01800f14a00055042950495003001c00400040038030304243c06403c4565128001d030241c4214071809824068110b606110260722500100005481ca0201406031604000094400601c80c402000440d24241380700703a0566000c90100100012442c060154a043c00c8408005604040d429500c5180101069191a9240c9004c01c006400b9400072140d0741300603d1810180310401c825100482d91040f003203c14080c2044c21700713040244290000445403c4074001034001c0480b1581d2407200b100500150204580c0d17101d041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 259753480 1250 259752230 259752239
    0x1107030e0a0e0103050105180c01170a020904022107050a0503010501030518070f230307030b04170706020306030f0d1409010908060a0509151509040f0b090d0207060e03030904090507 80
    0x2c08842d400303948a100001a2401d2a02c3c9040e50364414907429001507010700c8500d40c150743d00911500303002002c04282a040d85546142e54064000c0417503c5802a02c08500c80140744d800008228a0000080c20904a603c41c03071702c112602d110314011170003c24820001000954401c0e8020396001c0805010481c2a01400a4150030b1014070f500076011005a081c080c0300b0040010052658595034103042c06040d84401e0109072115107030311000c0e0003207001c00c0000c1c060050101e49140a5111492010b03034860389440c051000350020780780d81e8003074800c40460f911954000110f804400744562242080454010115005a48100c02060405c166100d000070304038020800c59019003d116004140c4d0b140a04d103051030010180d05216003029008103202c0c0d00905c40300d18101c3c0c4501030f50064066641c0c1d0411003240c8510101c002e05800059007003140030100819140381340906542910b0725190b5070b50044a120341290b00b1594103400c100840d174a03502e000d40c0021030617841282074070fa205945 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 259754730 1250 259753480 259753499
    0x80313210b0403110706080405120c0f070807151706040b04020705160e1605121b0a020a0b0109060b030a1a18010612180f0501110d021c1107030e0a 65
    0xd0310100d0101300c1004032050a080c00340120f03405000300d8030340340726585040d4894036a100c3d2040c1d0281404000025400c0038464140a0f50010a505004981c06030307554468241c4e4581d1184999034000028000e1500c85602c280703012408181c4640c1000d0340758490000708402014000e02e80d030352059003080040b0000300d081c002003210301840100d8450703413840e003403011010030801860102440d04248800da10380790020b080d120003c030008618840c1d0b9580200c402da007107082007048c00c0d441001084098806a00150301ca480c244580702148650740ea03614068251051801340e040381d01001d00004208031205c4d4401c088038070040c2c208070050702980d8040f805203a00c0d00104050030780018010300090340c02030580f42403550b00e024100209800103c140044542408006100036851208042480f1094000201e024550909940d071051088a00e4000b9446684941b6051603c040e00d080b00041601c184002c0c150b80c10100c1c1e290410580d0304807130411070039038003a80c0082c0354071000c03808122 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 259755980 1250 259754730 259754753
    0xf03050a022104020315060607030827030d060f05010c021e0909030414030303130201081801020f0901110f0d080a0609090f020f040e03190306080a031808031321 71
    0x441c2090b4034040c00c25005160801070240c103004c03c05400141404047d403140d0048608994140ca40030207107403a141200c500c4004000310031402d0f119820180c401c20600400146020444201d040242c940c0e14084e002d00402e4510410740401c1c099200c0d00003500386840000245c80e108062540a040f020001440641b8150341100140d0b20101d02404000d840b50410300c01900228011820341c5000c3c8100d0f00288414000203040040c258041102c082090a01445051118000303546414030151020b9003a00510910340c0000d11400054031050000300f0b4044500c043d10001d000711700301510094072000c0c0050403440d560759603010f001034041000d1040c0d8200f1407061070031066144a6004100600c0c031125a4148558940107060a88200c00011541c444030700343c1c0078401c81c28607075100383c00621141c1c2c070000940c0942902c030b00426034001448513040f82024000740441d0788456515543c0e000b16039140c074483c0b61100b4240321050f403d007900f00d80048042620014502e9694981c0704060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 259757230 1250 259755980 259756027
    0x60a0509130606030506010f031a120f011b020c1f0e18070305040c0b09030601140a08120408011103150105091203181309150f1503120905040c0f03050a02 68
    0xb943c80317041c8440356070312a07521034070036010740703018452902c0c2c003042d0003046510340301c40c0c84c441d0007940c101501d46442800721040b02c1880c20001c00500a110550b44440f50680b0810320060182c880e4051f041d1503c80c0c449210065030b402e42c0341c0d89210344082950140824190301c2da10880b0340e100c06400c2c1948180b050312802240d036001c6034a081519001100310641e40180b04042424050b0851a07180000c08030704452140c10050426030802002c01e6040030b4503085040e481c01021018160448004028030481d842c1c0c80007005900e602c052040340500054981c251028117060000d2960f40c40b40020740080300000b000041c2031401001c0003031450740840f564882664000c1140500341c503001009c240001d58400d4240101040d5035039075140b40300c5000c404112666a14000307030000d001c642c0052030301004a049568800d4507810080d1144410640b08800141d901c8008070351401c05000740d2001100c40e48490070400b80521013030340900300c01005503c0980d420b01c00400c440341542050802d15 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 259758480 1250 259757230 259757237
    0x4091a0904060c0306060302070201020a06240311130608120d02130602010c020f0c030a03140705060c030906100311010305280606031b0801030f0c03150506031605060a0509130606 79
    0x103c2266006010360b4665030000701414414000d07200540d802242e0781c3c54007580007400080792000041d040140f01c0602e140c07280c60f00100100031003000300c00361640c443d50004031005030b5007001101111b010758010b801031000607001000c0c005001d00360800503042806d0a080c003d810035803009008003255034203500440050f91100e0810207040e4040c0802c16050307040c80c0c0175119123a03003800403e6440800e45030040801c800311001e020400110000e80703543e15070000907079006040c80200109150002d9072403801c980285808a894100070054a40c100ca034809501118062401e00640041200a1043c01e00103404c0c1e40d0690340c56000b444420400c2581c280000d14903017000d800604650942664507010040a410007051640001003181140d90080c080003460301140303813209242600364402031003109000b0801c0003907216500151b01c070340f134140d00300d0300c5d003121480441405030464802c85400440c10443c200c0c130107100f400202100c92015207021040c8004945150031210140c2c0140c000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 259759730 1250 259758480 259758491
    0x120f0f0f0204050a0605190e070c030e06030c030103210206040f0303020904060e011703160f03020a0501050109050a05090318100c0b090115080304150f120219081b04091a090406 78
    0x6c03443d20180601d86404000003215181c0c0c08c045002c0d80f02030000e002c25007070010f0703184040101485011345100da0080500015117a0400f40d44080d00303504203000807120440814400320b600703801d282c81014042c989a00500e29500c480d19410805101c3c0a400d0b07040640800042400303840303d00601c070040100030030540e5558500f44180c088a2950b928801c2c1c180c00800481240000c3c6401c2280c4240c2c0108000000c142c642c85c00780e14001c030a0400074215402e000000841610702e50040348a500ca5110a010540d19001c807192a84164020f200030254001c102203054100000000850700081c10304a420128035141d03e50600c9044480c095160344075070801d509000300f908542e00030000c800c015401c00e030400324810620002c1e140004100070024609002032403244003990500d0406000865460b240030240c038000d558040726000104800c1008926005c4a108229030b65008103600c060500e4281404075000c0d00002a000d440c8403441c02d03080c4110b035500c00b43d0b03e00071032050100180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 259760980 1250 259759730 259759739
    0x607090e070504030203070302120102121303090b16110a330908070b0a17040f02090601090506090d0f02060c030a031401030308010e10091d07120f0f0f0204050a06 72
    0x1030034001000d00d801c01005110820050302d0009403102525070450310609500e04d002005030080c0a100e81340c40e103d111000c14403002d81c0340a400002002e00a07914155041c0e140d45e4a10014444c8000392080d12403103a55440c04100184118010840006c00000c03580c1d6956403010b09914280040c2d0081c0210103840310704402d4a4074910502c22003600b041310300b9515180c0d0301900e500c0944035041004c6400617400301060310a0804038401074403005a0080c90a00741400c13100740304d4841e8124010300726140450419170240b21321071b0481e40010710540c540700000c0140f010307059801c001140d903403070148165401039171014040c001c10103203000150346640a640340217055803000c0030500c4403000c880d0010f0011940c803511981c1947c034960044003c1d034803407402000c151a85036010140c620f18044001c80381251400e040d0200301909800c4078001d5403950000206da80c44200d008080d0004610f200c0b000810380c030048210301d0301641184038100a25004181680d034100d89510b03036a95203038030520 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 259762230 1250 259760980 259760999
    0x40f0501080901050106050a0c1103190201030e060c0a0c020102030408070605030f07030501150c0203150702031305030f070e190203130b011e0e06030703020301091203050601020307260c060709 85
    0xa07800b055810007400107500d00300c400b4050384078803030401c0308200340000c054050102c0554142d040d803001604540a00d0790340d0000c01d014070f52a042c201d0000342045200300308190005080c5028803100741e030030b85c6814102c800a41d0f004160300022410340c00244000130b29040280f25030300040c00b8507155150340349070140800300b2040b002816a001d0515040050000d0010b412007002810110b0902c4081409940002840c0c04807e132421388541d265502041030880d4088040d00c29204141119440b03c0c0d00c440170151120482c40307035841c1c0c075801103104001d91848401141e070020740d2440084a102c007890422400d03030b0b00484a0100b205884100c00080182c8401003d0060003006d10000d0040d0982641540e0503100d032140083c10451040416031913039091080500450b401402003000c1c06040c035003801085440508980482d03d4040000d100394000b20844049651008a418800207081c8500d0b9515405407a4050031003010300c058801e50404110681c05141ca684440e28140c1ca80003145 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 259763480 1250 259762230 259762247
    0x111f0905120a0c0f0809041802030d0c15020d140c0c0712020f040902031f090b06012322060302070c06030e03040504180203061602100908040e040f0503040f0501 71
    0x70440004010a4041690089090300c1050f0700c844092024035050511000034014141403d50003450034401e0030780314541d034490780041442902542c41500ba03801094420342d81c1080701820f144141c1034008102810380d4010040500541d40016001c000060806070114045401011000b000a405050240300b00809401440303481c25400d40ca0b0000d6020611581400c80b0700703030017030340c8a80b90241155000d124807070011208100400e80250724800c0d00014011039102652803401840219850b17501c66000200b170b4a02415900c0c074541a00101408268003420f01d00e0240144041c220900740101000722009120565000d61607905a080003207802c1541e500001c1414a80301160f01584008410748045510840c5d00107200d0581000107440c0c004038420095050043c0d01c2041102000c24000500c98212542290346071410040c410040729080180a00210414002003003016100c4540b40d074454452613205004101503a00e881c41c58209070826103103200349540034011540e20030404c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 259764730 1250 259763480 259763503
    0x30308060307150c171e1605060c070b060405010b16061b050301080c01090f090c05070c1706010806041a181e010b060715050c04080609030433111f0905 67
    0x25038640301e220304114006d80790449842180f6075000c101400480255900406456048425a1120b19000c1001c602c55808103c0c11580b004002c00402c40300d0800b80f0a00b416150300d41c0a452400090700722001d02c040340b0b42c0341111340c80c1c1c59040091400446803c0308a8440094540c0d54581d41012141c1d410b011080100b541040b54510040040c195640032a40481d2400c034800100d075228040c00315907510844001a0a0442600e800504a400420b90045030b285003803d80d00166281e4074040d84a910030355002d030001a41c0e012444500d0b407080b10fa580c0040f500b1255070b01701039505103214100400b41042031648942903003038420f508428090b00e1002c1808035421442c1840960350440c0c2d400109804240343c5a40c0d6001a03285400b0004a034050022001110420326040800c1c2d6643d5001d801043d003825541400400a80c800000385100104d5949030b54010a2006100321070a12020489c3c084910070410401034600040701d0300607044404200100e49002c4508001c1e04c0c00c05030400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 259765980 1250 259764730 259764773
    0xd0f05190218060a151202040f030303150e0a05100513060602190c0b03070207081e07050d2f1305061504030c09020315120303151009030308060307150c 67
    0x80003030580d140b08030300d8203594a010105e080d11500c400110b4020445111042d08940f00140108641156130400070840b4401e40d020300c40e1900700101c44101e040c43d485140521415030000c1001d01ca45038001592100002e071f0043c880350754460006501c00184d10020300400d0f65144140710195051040d5082c0440490102c108003110395240c0325010042e10510050780808008518010310911410005084841c00c0300c00010a4036240302c0c00b001c42d8105103400f0301c00d031701000699042c004800c0d500c60350088186182044001c4d000c0141c10300c801c108002c00c0f1418100f4401680c1c41d0580c0740e40070740091100040a00c0d204091080300c1120b0004050b9103c02400b0400c00205c02c40c02607000e8420f082d4025807031707032500d1f110301420a080c0300c002603004684083d8808030707103000006140310f00046050154500da000040c82042c0c0c5480d00340100040f500031043c030109010320103407900300801404545025980e103016000d07200940700f420000650181c401020b1040c103e4400030251054034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 259767230 1250 259765980 259766029
    0x50903010f1a060c010603022d030109110607060b040e0c01030f092105070501020a0f020d0e100e0a0306020f0405090c04050108040f0503130806012108090d0f051902 73
    0x1110300740d202c0d048080d40c440c80c400140302c0fa40d44000e412901c021503001e0446422001c28400007030340c0d10f445200c0040e29039000700c80d802161805001d040402600b000c0301c0258514601c007400700380e500650003900d000f40c4592000e01992203074443c041611b030990ac040e214030541400010256010000c0002100381000399840210300035044101618010317075200000b038404c846082c1d995014181c006070880d480400c00e03d07002d039000010034980d040151700b6158800609072007690316103c0e106086401c103c2020840380d005005044051a0441c02852111425529518041039034440007540310b944001060403c001e007803100c0d0050b00b0480086a46081a040c03600007401284002d1000e041c0c0c40c5240e2516042c042c060080700e40e81307103d481030042207039103824002d03954410030321417041000c0200000c0001817504400201000c1c0d8030411440c50413085000700a0041441f40c800c0d2007450071100e500780014030400440105038082c00100c80f9122003801041550075007100b02581c1d410480 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 259768480 1250 259767230 259767251
    0x415110708091908030c1605060309060103060c050403060f0f0b010801080a08030a020708070308010608010501030e030d0e1204140f04061203030e010209040c0203030910020a080a0b01140a050903010f 88
    0x520607101c0311541680d4404004000f03080700c0c50b03402c1c090740c808505400700060715480c1d24030108001400f540d1802c0b0f410001380e910018400300e071200311000d07d10340e00b1080c01800002c9403508042007810b80342c40e02c82d050035181d4907108102c444010800c03001a1341e81008a055004034000ca00211400f404c00c00300a40c50301c00e1160700c03034408204c0101001c4001000414406441d4182e4054a4128065070785540a034034016007445070030f0042c0e0000c588060000281d540c0b01c0e005004241205030302440c00c03d020407280a010741381101c9404a24000c03046c06882101000016000415850891a500720000c0c01400032514552030f92074000ca00b4407a0600100c01c221950303c249591601e000a1390038010182a4024003880ca801ca50190034041d91a10055002001e180100707400e000f6114420404009481248141403000e00822007500029100714030355031020300015410304000111a0803070800ca2210390012005401061000c01c40c0f034441e05091281407045014183c0410038188034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 259769730 1250 259768480 259768493
    0x30c0501021c0f02011103150102010506060f1e0712120e1606052107020c09130b040201050c010f050106080405010c0903170f190503060316120b04030e0904151107 72
    0x1c800b118000d001009603128100c84c0f00350300c01c012548440c42403e480b800c0840e01515000e40c1c2d1480340d8019030820b004036500b840c00c103040703d003414040c446480c60015001c1200d0b0301110703202c1e00f50412403424000540454048841e40d1901d0100d69a40300150004007020301c1260005a1700410395405200f210b80d6007020320580c6400d030380d114107100c1e841d80d00f007050f950b1455a180c11084e0305e000a80b001e01c1383c1ea0307400003029074412104507010041e039906d14806103401c40b19144090702c0b501001c800305025500500c001d1451220b01c0001017804003d05a8000c191142030f488600000d1245e800c020038000203214246200d0181c1c50104503161542e00e42ca098184445100101d040c000122120706071a01022aa0340007401900c00c0c44641c021400544590000ca4001d0302074040c1c19600b0640c1003580b4020001c0e42c8130b541240070fa000194403040d500c884010011018448514030160392661980000c03072081c0e118801c2d1900a0000500c1c10050327030360910328403003001018050400080e10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 259770980 1250 259769730 259769773
    0x90f220b0f06040209120d0201110721020f0703120f080f1f0305010609060f0503121c1d06040c0f0605071b0b040902040e0f04050c010f0e060c07030c050102 69
    0x2400020070340d101c03070000400a02c60002c2c010b610040d00c03038541c00b0303080007c2060f070b140c080d140e0001c000080a00a004e5050312072558000c00350b5040485005a030301c0044008100c400d00d031300c1250003200302c0c12042031525165030010341b131628281e0350000e002607112440003019151441e2012030350405440411400c40701030030702010021001144459502c1c5290114021500f24000340560ba58840841000341071a014405032032008440201da43e0400043c0061215810b10905251940000c0340d03056000c03005102060203601c1ea42f01801ea103c0680811031414442800740441c0c4c109440c002c03104040c7c2d40d000f205000c1c4004070801005421000341c5100e02d80000d540302c6160b000d940240020516074119074050180440c010505114550281050351070902c0035032101d843e0a0754410100c0000c82d8010b0a0394401210500305511415003007500100c0390500000002520b80010780036042001409060ba000402c104188180d120114000b48000c0c000341c40030590700314815050f802c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 259772230 1250 259770980 259770991
    0x30d050a02102a05090f040902130506010e0a0b0a020607081608180706050d2003070302390106120b060613080a11030d090f091802090f220b 62
    0x307580d6207805000350401c00400780e40024444648034000344000e0081d1145d0800400b40380110f61180703068a040c1020700c984012182c000341300d8891003040700781d1b04014140003001d4904110101104150b2a2a0fa07828617020b820104d04203034a0b40d8101900a00e0000014809010800300c0c00510140c0c42d00003504c0c0d407840c202840d15145980c2d4130002201a400050600c5010323100f8000002081e961200c082e00842c00045018083c4402a400046007008480c0c410f803034802082010820180c001d074000c1c4507012480b22050718278982603c18106d40f03c1c4190203d0008094500b40c0390130203100313200780c4010f890824011128803049071078654061000500983c01a000010340780f201d4000c200e01c0b038005152a030225202040145088031044d150365121a0003442000c3d0f001344142c2c0200315910035a03070408400d8950915004003003014148031081c00c0c8664022007070050250320350126452050000b8103202d4818100000780441c41c030300c04130711901c1c0303031860080f59000200740d00c100341e4000c23 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 259773480 1250 259772230 259772263
    0x16140a110f03130806130818010c0203011a040b03060f040303020306060706060308040603060b0307080403050a0507050a06090c05120c0105090103060806040c0e011202032112010311030d050a02 85
    0x11004050090714101d101c1d680038101d032102080041c00350f50502c0d0f0901c161922601515000d03100d0721400c40c0c82d0703c101080203003917050512400310801e408100840e00401e05243c1141d01d8191030300440c0c00c64404041004210420604072603141c1098041e05181d00810340007091207143c050380344a02135001800043c10544c0000101e44160383c0c4a040d07440241d00320a04011550396880c010300258010f04c10400881d00f42480090502c4181045d00e11400064441500b255a184e9003260a40e210007001c0f801e020040c0244008107004102d1158801d11036a070020350403805081840c07614a0b1544801e00c95000100544d410001c085140031150390700f0700b421600d5800740fa005070702904458002e41c0c0340d48111000c01060000b0000c1242c201e6003109a42511a6281d421160110104200c065090f5120395000c3c10001c5064140300044642da107130341800d0802685c4a900c6105003a40142c4190210030365202e8070b440c003444145041e049900f0010310700484180042e4440111a54603e0305 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 259774730 1250 259773480 259773497
    0x6060f0d020a09021b0d0c11010e090f0408131415030108070e0a111c0e070503070b030c09030a120e04060528031704091a01021f022116140a 62
    0x106440350317070a040d28030a030f901660942c00c0003960040c09448454816030301c411100282d14210750003131109204002d40984030841595840c851100c0c03404000c1d008171803592041228200c49034112440d02c001c0d1403060074a03007001c051901003001907851800d128100c1031003003004200e00b1000160080031180c00d890300c20f1455890200c184014440f4100c01c90f10004001041d1901e9040b403072544640020b18442084220320003545150f49040c1402041d41540c03202e641807203802805400703035134004032070281c0924040e0004003090802564140c125801154141071011058200c04201c9483d0710a0360b041001514020004125109010a00c43c0010740c3c64884460ad900c5005000b01458011030307141c04940781da0007019850f034050300c50b0301d4005142000682000c0000c01070ba44006105a00915071b28800740e04001c2000d0400b83d022500980c03c1000307820074048240d400c0e0343c4010802e0311411034944200b010502c140402054010040d4000f04045040f03401810baa0f1000858980400c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 259775980 1250 259774730 259774747
    0x8010503010203090c150c03120402041a0109091a031606081b0301060c060f1a1003091106031e0a06060f020a0507180209151e130e0601050d0e06060f0d020a0902 71
    0x51510810b010360705107001c001274040c490709100d2101e60156200751410008180e0f4040354034080f03588814400e00044d0310304001c00684845e07030402c500d1010240d50b400059040807000134617228408803480c99444070400200990750f0023503071407a40090401d003d0300c01c101707032038291a41034403050040d50107111014151000f0300c801c680c060180c0800b1424200072142c03800c4410185100c0c0992170500c00c807680150548030070f11a00805903031907441842c003004103103120100912908021300644415200c0c2030b010f07103003034600c82d0002e001e450018400a507450520000521820307040d0281c07030541d44561148000614001924401c0380c0e01c000850005400b22080500a0b2007000080b1b544883c100700f02004006141004010f14000c1c8000030400039000a840b600d94001c074100080194800201006080500503400754031000c14980249032030302c42000f05044805064030400780790302c80e5040141a00b4000305486c00c3c01c2c07040b51b42c254060000da000401500d03c0380123056109402050818 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 259777230 1250 259775980 259776019
    0x30f051b19021002010608070302060d140c0a090f0308071203020d09050106050301060501020c13150909080d0518030d110403080406110c0612180a02031c08010503010203090c 77
    0x4016201442560102080c030348038400304024148099109485003ca00300c2a507005104031821030303d00402400d03050745160200030325030300080005c0c280691144407401e200700107402c00511030790013948016100d20001000500c081e000d80c10a1a641d490503006002040c0d101058a02007903200c90021108814100120040d0159a11403c2034500f014a1441082010340011054440c194002c20415603101e004907581c1c00340341c068a8000c4017081d0000c072501d446401940241080e02e041d0441c0c140c0c0c0301442000c680752544140c681002c0410383c2101c04182d40140ca400506010b20b840b550364484085e207490303100e21650b52554a580b50079800a5036224001d4800840e0800041c0f600c0b16551200607191001c0480c00450600032020040094981582580c280180442c440f1000307668000306040810076000150990b4481e010380200160340c2081040d00082c02000c01c8a2484c2469102400a05042c2c001504c60303401441040410800080d0000c9024421100c5102d001004402003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 259778480 1250 259777230 259777267
    0x11a0a120513051c0822020d060b0306040602121015030c0318060e160f05090618091b120c0409020d06111c09050706120608070311100804030f05 64
    0x1001400750021300800d01260070384880e0006a81d803101101640c07400c03d00d003019080040311007922004007103400b0241c10004900603015115290010791b82508400003450400111000c4a495800158541c0300d030309402d540c0341d00711205550708146103007080c1d1b441142036a800c03042e8040641e07c800000c4805e10940100042d0200c10482c0042e40b400360800300c000d00b03110035050322a44919000c201c0514848a40b0b1012900b80c0c0c41006501810007041158000e0081c014a510102c011a44054100e00454660240380c4d0741c1c0060515007401310101c8031020101018608c142c0b0405d01120200e0404600c13100318880840e00042d82c14400c2c80050210b4484020140656260040c41c0d020b6060f044000c00401105800009100d000c10020b40240c6100d100003d0a40d0803100c02000040e0240d013141c1c3d005d03035500c8404504191614407551600b43c03e9030044e038010f002c1e00810fa8403802d00c0009600c0d84c01c92407070100d925251642340586aa0009041002000b1000480c0405030040c0c5c8041c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 259779730 1250 259778480 259778483
    0xf060a020a1106090d290403051c06080102190305010501020312060d03051b06060301050c04121101020708240105010527010c0606080d08091f0213031a011a0a120513 73
    0x802e94102e820304401c5803240f80c8055443d4540300d06c001d01440c1000741094800c42d85580c0e03580c5048a0700340c61084000846050101d015141c4502098060080c0054555444101202d0800d01d21414006080e40c006910881c1990800c1240b0701094810b495084d502050a036403401c2c040c4114501140e951041c207078044581c2000d818100640c68020400b14000c042c210020f106545440400380001d10481c4914114003031960080340018520061044040c030050040c4d030b007030658801c1e0302e0b410051000103400400300c001d490001c0709010041618090718082c40c005042100c40700102908100c49451001503240d006071207032981c0e01c1105000039056021106000207a607480142c0e545583c0765a50a0210f402900003410f540f03c00110070645d030500320b401c0343c1d00c0c020310041a4000d51203840300840c40f801030354021000c9002900b10540c68841c03034070007000661500c1c05030005c43c2c4400301c80c0d0303031a141c040184504c5240e0000380740c2480403a2050000f01c50700d50307042ca08001d00e030b0f1800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 259780980 1250 259779730 259779739
    0x2060304030504171216030e03030d020a090b04050109180f020f0301090b010e0f010f090e10050102190804090507230a0f030501080d181805060f060a020a110609 71
    0x420040651102c00342c41102e4200c0e410f0f50b480e06040e203049865101d0180b4410100405200071403100c400710800d0052a4028244080b520310345901007815030380034284c0a071489400180c1c07000e0031030f405071f8400c0040c0b04007041c41d401c1a0814000801d10401481104d41111b0880000382c010b441c50740c071007540141e414000311b58400f014100806550800d20808101ea45028215034041d4080d45101c0d100b010000c107070310640e00c0f1510041d00d000c0c0c0305030701d01010000079000204440040e04c071058010300f0030085079400c0600c4c040009141a6091072100e804001d01444d5130001405c100c152004e0354201803011405a40c2c020089a80620425614161172202c0520b14010740030f4200400e0107140581d01d0b800c0502c000902135091300e0081c81540c1a640c050301c680000e0521485000e85140c842e9032000c03080e00e07502da614514000c0c90307150b0102500c1d650790a01c0450316240c0004c8502c0b01d4141c803001d04000680740081d440c2c1000c4100a0310080300b24401c2c1c5c84950340c0320b0031111454001003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 259782230 1250 259780980 259780987
    0x11070302211c02150601050a09170f060408070c050d0b010b0a0311130e060103110f0a02010207021e030d0305040803180c0406082d0304140a031a04150e03090415030206 74
    0x4600940c1c3e100700c07201c0504504d04010108030700e540319404580c402c0b00140c03907000440345429155072140800c2401128075008050b4005000705081c001d42d8017650040101640750782803406c108000c2032944d4019403246658240a03000a0340708803109044074000740f80c01b030312205400b8003a805001101c445901c039920008160b4000c02a001a9005035130040c0b2684420b40e950100660440707035001090400c110080c0182241d0325004002000100c00c41e200150401c5466804102540c0114185445210803540600e2282c01c003044214010322461405016030300745174642c112148006004224000425034608140300c0d01000602c45440024000300a03131603540d4540c503201c0080d01e14000d1010408059074201e028080d04e0303001902d0603000514541407400d0000d10b0141d800311189500b2610b0040000003081e0030140c0d103c000c213098217060403149024a480e2000742d80c0c13050345001c16440c1c850211010f07c4008151002135109540003c0c6200c0703102504015400f541d0700095003d071002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 259783480 1250 259782230 259782283
    0x711011409060403031a011b1a010e0f090316060507091802041a090306130317070f120c08011502010e0d0306030213020301080303060f0d050109050d1107030221 71
    0x1070710b6446039011303541c00c110040f003040b4111081c000e81c141e1640040c0086003511308022003030400b1000d01d031140c02c2902414101152040b804d030b900368001c40035a0036100402c041101c428101e075501600040113180f4103070860108a074214900440079103540d541d880020300c50350107460a000549010b201e0785464420000031500698000c0c0104141c282e91a05840c20070318040003650800e51004014044568845070904c03004400c8201c29000c100b480041d07821203003640754805020720304503522807544408820f40500001d000f4800309040900c1c102940005680c0007413405c0c1075840716078001200c0d2002e00001c87c0500074225840f1028001d488114555a806030b200100711303032080e16403240d150070550044080340402d1058001c0c9401c00c00000e1050301c1c00b1a8054000c403001064604101d40c0c548640e03003110700d0124100c45507070103039183c20a0130307030400e00c6564254031503401407000f03506560108504000c0411120460114180c0c00c0140b00d40500011a060800106845800804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 259784730 1250 259783480 259783483
    0x7050a0602030a1409030d0c09030618020406050906090601031130010f1a070204020c0321010f120f03020c19050112060b18060d0218030601090e060711011409 70
    0x140d41d00ca803c10310f040c07003a20340001248000751043c1040c4e0040d40c03e05100c60040006082c52809100400c40d40401c08400280c0e5032268500000180c6104900b01c12644180404c5804540100c1d100342480740400000b0b81d2000c81c11036005600b031030007048014030754001600398050101009440c003189981c10840682854240785059140c00f00c07414940da03100d10000a0110b2802100101c41c042c0071010140368510300104107951000d80014a8021039612540c19600141071130321030b00e40748051040401917482d0361540502000000081c0ca2071514202c900d21003001000180124041d0340d140c0306243c001d0000007101d100260015011008403030303400d6034501c424040e0030f0206044000c5120b0b2140307280f0680d4241c0ea2072201007490401784040d1000e150000d003a105921410400240120b54400d0028185103000c5201882c192000842010708100c4143c12404035180343c00304285520000003111074000306542059031285403039000d2103014203107040300107095082090501004080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 259785980 1250 259784730 259784737
    0x40504050a03111e0c090604020708070b09030909010b1903060b090f06040b0705070e370603060c020703021c020d030503090102070206030f1e0106021f1401031a2d060607050a0602 79
    0x45c102d40c4a201691283e04210407401003c0c005000503005120050002c6d456007401c1d80c20094041c11642410203c0b00001c40d4048240c00c40d0270030050202e02d0b600c0d64403440c190008002403600701448803504284020704a400f5506003d80726800020b486041a00c0f901d0880d0041c3c540440c80c9990307085941001c5030b41d400070380700d40251110460b001801143e80c035001010100d101103d5410098078800c100c6103081c840d000c80c0c10466030b6070701000001600030310800300050700c01d40107458154598010451441e403503021310b030b2001840c3d03580507006907182015400841c0d418200141c40c1e80300c2808039802030084000083d0004800002e10030100c2c009044184500590072a09c51110b61020b0b014891410a124a0000d40e100c2c51006011107540c901a0800710101c000004100c104400d042c42003c00030b81c419180c03604000d44900701c40c2c0c81000d4075503000010400225400c02208003aa850079021102d0014150556001c00e81070340d15070040b10155138000003102c0c0c10364507a080c150001d61 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 259787230 1250 259785980 259786003
    0x10507080a0f12020906041a1605010501080c030111040e090f01060b0304150b0f0402030612070e0402120714061b0102030a0e0120070221031204060506040504050a03111e 75
    0x1400303920200c03d100701500171107a2500d000b40642e4189803424851480010041e001d454882c5402d0148905468242d00d81e0480140540300100741c42d49000440c0341810440c80c0d005020364103105035041e008900e41c04603022a4a189a5400035944968510b42003000284d07402609500348940081c943e21070030082c43c01540203102e9001280c1d0f000c0070310b030300301c1c0c115003c581d8001d400031000300402e242c2503000e940d01050291840c0e4101c2d6088d001e10341085810b4000d48520500312060205600b402e54000300442c200701c00500c881814040525802040044080d00c1090002081002601c045207c0703192200008001d640341e04100b104070015041c550f07203640c0343e0740c6040b140340c043c03241c00c42000040782040071a9910f08840d076000c1c49090600b4a021b10040300c0c0d8010f596289400810050920121079000400941003500d040c5007607801c09000940700d01d04080c01d00005c1180400c5440c0c2545c0c2c58244111403074050f0741d5090600700031601389000e030310941850450915011582e000c1c09e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 259788480 1250 259787230 259787237
    0x5090601090b091303050c03070b09120a140309010f021b010b0319080c160e07030b0a0303092705070201091401050c0301050d150c09140f1e010507080a0f 68
    0x140e032100207290440d000b001c01e855026000c80080341c1d9080060f010104898020302d000341c42d104841c40710070702e1940b201d48101d0b81500e901c420003030380e017009000c200210100c2500e95032a00461000051100440f001c0900c00d003100000801c4003203100b58046000c2068184055445120070142144904040c17030400200b075003441d2000919140120340b0200004c19941007101c9100ca9803105a000c1d04012641c441034401c010401c0020705003080c42d50020001c00b010b100c011314207860001d040c0c4201050302c50145031084401d000181e001301a03401690b0445c1040601c5105d00f0404035283c031020704800e2269032508040c8512a541900314a503518050000c1d441d160444142c05804c03188102e030003260442e8140300510170b926004404178a6503010b401c00c000b80c1c0d4040740d01e1000301d60340d40f00c0a00c0810f2401030b00b040080d5015004500d4018121034904580041001007850440b200e0310345029001920307001c072001d0f13004030295161990003c480c01e480da0b030f80c22400b4010500408810300407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 259789730 1250 259788480 259788493
    0x190c081801050702100911090f0711030301030807031b020a08073228090501030b070305090a021c050f0109050c1009150905040e01050a230123030d02010509 69
    0x502405000302d41c0103802c039034002c200b1601489070441c01490035078000c4947e0604c00c080c1e910f09a5030240498080c01e20b0001d04403150034101e50140029401c0400313410319030014401040811041025142c42603018100101040014100c1d03818a05180100a51191034100040382c90a0000b60718000c0d03c03807d4640c11000764030000c041c103207c40030581040e000c40701c404104045090254020341c1e4003004081200c0d0b03003501b02036513140c008060f80109144aa6440040003880003044440b600018103050410032814800c4009485d10000400079000b1104401841a00040166151501038100c0150303005250512079060180c5044502696948540c400100040c03411180800d40b0608688546484516141200d50700e01d82060700b99043c450a440d00007510340300c0c0d01031042c0400220f03000051600d8251004002c4461407410380000c4401c881b0203028079600c210000d8152440c000708500388854101c0700c203814420001d600303505802030490042c802501504601c0c000c400c900141d40c00e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 259790980 1250 259789730 259789771
    0x120f1f060206151c0605162f15090c0f01050f030403080c13080a0213050c0403031809020a1115070c2301090f03030e1501060305151903051002040506070b190c08 71
    0x1c074002303002240840300d400d001c0b0241103064815003580ba600030140a440003924040d800c24202041110b4802c20344c2c000c222a001603181400b40c8040007802403c015040c000f40c500d0f404011b010080c0010140f0201e81c01181250814900360b4403428841504011200e84036500540c03a0051544c040740100d810503210010036241c0d0003254403a10515521030700f03282c510740b4200d8200503510904810303030f040d080d0003150f20314403030005202c6141d4588400741112240405186028209003140340503245c0c12081c080d40607801010406c402da00700c05925480254168103890345c07550600f84101c2c0390318011140041021003415445128042c0c0c404008120711048100e40720b08996460000300600003006018030b601990113940c01c96121401e20300380e8040c0401040100b40680000d0002c0740303518000f00200030b010040c8070040d03540c2c40700960030700d480c007400305100303009600e4010b010390001000901502445040700070b150f4286003050185000c10b0342c01400c154015912980c01700c2101c9906617 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 259792230 1250 259790980 259790987
    0x8012c060402030624030d080708070e010206010b07080906030a0501262a150301081b1302091c06060303030e030304050a02010311120f1f060206151c060516 69
    0x521a64010b0007400690399a40e02d6505079030b0101540c82503021403080907005e01e0300c0403c070600d0700500c2034503140e0141c2405507020303019180c018040300802600c000441c10503640411818111000e01c042180c031040a454400c81030700a508110b07420000200400c006c0400c0354000314104c031950708840c81d003024107070f00c4103404a082c7c10342d4040503403148210030a00018401410000c012a2918621403040b040019500d00040180c5210541000c00140101641880752480030b072504500500501c0491000c1140b108001303401c140c100340d000c0768404007a00c80d02c02040d80244280c201072015032803490040010f1510340000d90009251040940c4025000403c0324050b1350080002c0c10003e243e42c0c0110050300380203c407141107103424440c84150200200649024811040b0802c6140c076048501417140005115520410851190204081038000c240c080d001003074801c44c80c40c9400c00d600410480c4080c02003510740300462026050a010107580800c2c0900380c85501216550880031048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 259793480 1250 259792230 259792243
    0xf0c011512030c03050904020405060a02060a06060207031a071707090312050909040b0c0418060e0c120a05090316060e0d2a060b090f011a0406050a050a02010608012c 73
    0x4000c1202e100d8903d003c24003c001174141e140f0010401b601e480d840740013045154000350340b00005a070210080c858241d0703c0780a1640682064801004a6451520f540300c3c01040d00c08199528a40c41c400725058510405594045052241e1012071906020b60003d00c0c01026120a0b074a010030340c03a8840000b4440c0b411134031007402c010044000c42cac0359515020360302d2401030a40c1e500f0748030420001801c0000340c64400800c46290780002802c528042035848041001000164806010490386201d014601022900048800e000103087d0b9074031003140b80396204d50480404d41e2540110381c503003001a1900601e054100440984908200008040e1224420000c203c0d03011003082c075555131095011049000010b000d10f00228440b040c2d040400e0b43c509043c1d035418080140003005001400703d80030000012200c40ca00f5a2919150050082807401110045d41c00c00000040c2003038107030b01c03d41040014241c0c041c0200103a5094108468803402550076990280021000c010001030020070b12 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 259794730 1250 259793480 259793483
    0x180f1207060f06080d03090c0e0f04082b020a0e0307051309020114030406090c0602121204030512070e03070503120910090b0406030b0906030606030a080d020f0c011512 74
    0x1150030840a5501e0601501c5503210b035450040d40c6420006099604021040b034600301906c00040b00025420a0441c9901c80e80100385041000c0091201d4101d0441d09642c0c07064100ba2515141c841c0b02d00f41c3c1c1011121403203640300f10215000004214205a4020f080156171501d460051381d10304410b140d2152003078468907170300592000c841c440d5059982c1000c0c034038520500d022290700490000400300780e0000c0d00d041d901d10390303100745101c10007200284900c084d10302c40c00109001c440c420207006a44c40b990302001e41c01c400c1440400d0406d800303201500d91104402d0000302d0b2901e0080002000948260002031080c4680c500000d144c1c140466640c0910869400349490135540703406004d004d41d5010f55031402c011b10340d41d0000d050400400070b000038084640c1e01040800d44801004a01e02c0040c1c1420300c02d030070882c01e002c0591750015050400303d90045060f9150b0f020900702200a0240b240000050180014101d8400d403040d8404041e00d000c400c0c680c04441c0c1c0315080352268a00c1c1031720 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 259795980 1250 259794730 259794763
    0x230114030c06130b071103070806010f141804030320070201050711010905100c062a0c06020f0c0c090f091203040f060603080702040f02270f0306180f 66
    0x504002410b1600c01040d0b030103075041e400301a4030340d0b5000c1c85a0540c4080425a04030811119412152605002080041500c1002801d080d41040c08040079180c1c240f081608061030241e044410751140400c3c03511401100304254007a00e841c3c20080c1c0900b900241d810b44c03210a01c56403242c0310140c0d000b69100c0071f03011b9441da420301c80c90f541c4203400407240b0082c0074103001d100c610011f070340c0d5180d01c40345280c154142d495054180c281d26141081e00e0030280705045c1010f200c41c0840e40c003c80010010040da805140c01c441308000c50401000903c18544050300d030324000500030740f54a00000d81c5803469542030b503040d0410781d00c0c0e4006500401003a1811b042c90780100c041c5810744c0d2082800395801034010100d501c89030107945e442d042201c1c403907882151524030202d908029403078603114400740da251901003580703420ba020141d08160140e04c9001e1803056a107054010958444040c007005000028088500034242001c20000d000349003c1007180340d101c0c0c6603401c1280d11000c680390f4070010a000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 259797230 1250 259795980 259795993
    0xb070914060c013804020901051c150b070512030403050306120304092d060b04051e060c0105010810091a07180e070f02070509270123011403 62
    0x1000c00c03240390b02c001c4021140350740383e49504031440700c104880706580e40c650803a8001c0f60600168068140d82d003800c154802c0744144102025a40c100048071114100d4944540c2e0046d0f90048480041801c01940103120051401c0444c181070158001e00c1001d000d00d0856038003411440b044620340c402101e00500081c01030000c2140c82c108600c40080c455038500a50f800c11343c0314048031088031680d5118041c80f0f0b140400d0200e41551056086110b00822803040c80594203041440400d840380c0d120f01e0380544402c1c601a221041c3d10002d03078a41a0005119680e608581c1c04005c0c0600000e0080e28502d006022603010640214410000a03560000302203919a85032580c902d0156030003030154090288501c180300c0d00340c0c0d5000b040302c05444c544005070198100321000400b805012144001958460902400b4641d240603010340d020880c8003400d8104007a40c40c2e10035030b42300c10312411001c640c00c110802050592116010002d00307481203500c105aa80c40041d07468500b4458010f5806405c2030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 259798480 1250 259797230 259797269
    0x15032406030f060e030712090e1501080708060f1c0303050f311202010903020c0411030109150302090703050601080f0f0402010e0102071a120f011a09030106050406120b0709 76
    0x9421004c43d42c0782400589051030343d1502c51003001208250361500203003213040c0a10080c24011001c17a0090882c0c80c8401e100e1910400181605002401e80701c20300c03281d800004c0541d5071f001c4240403403d074060b0100384480c02c002409040f140000300c04a01190070100051544e4421078500c9109200300d03e000c00310050301c040100c0c00202d21242d10b51116950600c00da0109603517001c0ca01803000c0075800000e00700384604009081106968046100310300b051425420041c0401c1903d054621440f8000356100d01c9103211281380c140d603070009401582603c03c00030b005800d40d01040c4a0b000a13200c0e001d29940e40b280c1200c2c84901120118509001d840110707000d54425521044510418012115100d03200c40e81070101e81d0f640001d20230094400a9a08404004003030402d800500d4003903039620950410914008007801c140414a10f41d102040031002c1d69030075085000141806003040000c140c03208510006001c06030400c1e40c1e808140e0003c512010311501c400d00c1281c208800548201029 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 259799730 1250 259798480 259798493
    0x60305041a0c040b2b29060409050f070207080c01080103030c030908010e03090102100501080703080703170109062103050d0e0a050106080c0109140906010f020115032406030f 77
    0x3030032041c08200b00384404504068118020401008000413400c40000342210301c600c459032028030701001c14103001c4e51001c4600c240d400300c500030081d1024440403042c0351000c0b44690050703500c0b40c288a401c041c144001034000e440d071070740a03080396402c0e600c00c5600c03069010380c1c41c42d0b00440c0d2400100e080c001040820f11401008424901c01d180014081c1d40d51201c190a480707401105030700c16000007407209041c0d81c040080e4182c0c4141c06005000d59072420400f42e03214403091102034400300c4d000a40c0c104042c0300382420803122130600e18008072541c540c072180d00104424002e0680e81e40b2421280b090901c0d01240ca0002c4981c10380e907c83c5030080c4807079480702400400b070b9802c003640304c1d14400000150080c0100d00140a81c1c60003800c000c0b030807100050000d8203035401080100c907452451f200e503481c3c440400d64401c900b070801c2d08030070358016130403801030902540e40c0e440380c03482c0ba00200070001c007641a0480d004107a4076032800c0c040e8003034800e0b04440355840001e0052074814180d0002810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 259800980 1250 259799730 259799783
    0x2010206160203190315032a030b2e0e010515130b0a030f0e030d180b130f0f030e100f0219060207080424090e07121b1806030504 57
    0x5525002c6014000c1041311002003403030b9002264602600c28003000c1200585901e44410f2307024000660b00c42e840e64450b5148050301804090307400f40c03070304803980900d0300d180e204a807200c444003036804030b041c0d03140078040c8801428080ca62203801614030401248042206076002c81c07a20042c00d050661806000e03100c1d41d40f00b40a15401d15444051000d0345031200d20a00700180050303406544d907a42e000d40c1c10360480c4d4866141c0351001411302440c5003c101400403843d4000504030300c0e084180c0c000d003040302c0104c1e14a040100b842e988981c560701015481410032103610300a030f810259441c8040b1003590000c0403144880c005a12040c280030a1006061b504000140203d8006180803a41e8482200941c060707040501018a20b11100300a201e41c0c1c005150701a1840c0b40c0240c15a0138982c0d9000b0840d00070f03044034104042d50154150900d010307842100c256001c0c20300640ca001d6101d0016042001c40c444080380c03aa020400002e00d140280159071140382e2000340d0480040c81c241c0840340c0d482 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 259802230 1250 259800980 259801027
    0x90303090d02190b0405040605060f0403030309030309120c03020c0603010518040606080102030c18030a0b06010c11090a0902040f06080601150216091a040c050405060d0b040f0902010206160203 85
    0x74526690510050030801c0c03540c01303450440c40e09544d4900301014001501c03c3c45d44070502603481000f24250039000442590300b038076814a00800e00c0601c40c2402c5003d0016000c0282c4103000c041d84144606410001590f40340c6d100c1d8098900708611130040141c207010074452030741c010101d003900c0300c042d003d0500d0b865131152150034006100c50712084401d08907041218034485400001032001001e851102c4040404201240108100c00013035840314583c3d540500118140032501400000300002082030843c0460040d107641c00528080000c40003802c1c5103001a402107240070034046a440c80e50040340280e94076000109100c2e46415203074003038512403440840c11801209040e079001d07000c1d800c00030001c1100140208020400e46c0d10040311250f0007038402e102c0d52603c43e1080c140f07a000016201100ca04a4684d9120040781d00000050030211940a5105103016401642120143d005c504114000c2e4200e4401c0da440911102e004152040c1d00c1c00560b10500c1328540b00f48400e0424403091 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 259803480 1250 259802230 259802239
    0x30b060f2110020a020706080f100603050402120f250302060a080c07050f1f142806090510050307240c0203060a0e0c0a0609050603040807080705030a02060705090303090d02 76
    0x389201841074080307810130030806005801c4504100400c0f070740301c402a40c019403240c40d03c141c6030614807480c4454030f15a104e0081810345440018040d03642d446c0191507111403002c10b4841074901c0382101503e81c01c914481c4918112042c0c1200f2014512510400c2034035800750105103002c0c5900c3c800c0d5140c00c8001c0450810755410070080c0d0000304148642400010f0324001480b081d61030314412009243d8210400200c1132821410381c9203810002400394100c0b444032004004d08040c0b032011021000c07110281c1110f00e04003640000c4105650b4440d0b4130a86a402c4941c00e01507c0b241096240c010600c121913020b0100d006822805201881c0075049240c24248803000111590109007080b208a4044c1e003c04c1c3c1d502e1229040d900300344450542050221500c2c1c845030309100c400303040707a4154001c3d0b07070082c41c01000003070400c140e4004444203142c00c001c03003584400301c034a4595540d600c8034002c100107001b502c0205030300f079000c0c0003a20098480200950700f000405800c2c00001115000c007070342c0c003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 259804730 1250 259803480 259803493
    0xf0f03060607050d0905100305061f0201061a041508040b07030b0d0f08130e060109030b1f031203060f0303170717070e040b030c010207031e020a0603020301030b060f21 74
    0x30700c10000d140c01c50b11252205c0c4201ca01d0001003051008422040509141c10401000020780d104207440c000048403520000744010015800c13401401542c100d803501201140401d510145100007810450310100d2028011078400c1404503900c200989000b480000c030b0340003007008680284c00c00c2c003501c10081c1002c0d2299420b9140ca985a185c411300580e401d01c80014030300403200c000c02c0800064a8400c050500c00c0c1003806c0000e1004040d407002410524840011415101c1c80d00b1158212403042c92042d1005500e82c05c120001403001d100d10400300303242c40000074400003071200c0a02183d1301a1154500266a500b860310312030310007440002001700c0343d2400108004410b5040e8000c400f20741d01c101102c06d0070818001158122406180300b5070014920440c0c03a81c3c00241c14040e42d42c48251450200c803860306031298504140402580301180c40c0000c135015503d43e01450403030307015a06a40e003a0300c40e6014044101545132459400c60b40001200c415201c99144521410009400300c1c0c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 259805980 1250 259804730 259804733
    0x30201091a010302090a060510031d1501050909010506030d0f030209130e0f070b16030c05030304050a06050c13050f010207050a140103050603061905060a170106060906050f0f03060607 81
    0x2440084030001c41d81101e503881c01071040d810704480072540284800307410000f0505010015148594a0b4546810561125014945070456000782d265240c10300c0101c41403d07566445c1c0d00c00b603010074042c03903010f645c42c1070024140070414007035180250b6018000d0600c0b0b10450a045a0b40300c005d0700382d10b051503002c000b400b00e2a2104a04280d1b13950140600084540c508001182130180c070086025140e84030727a809005c8803084204503040100c40c0d403a00c40b0102070301c1c68199000c0d18000400340c0700b8000401080140440810348070000d1f846035508205c50b0b5221483c0840c24054207510347c01500140f4410300080c28800b82d801032081c014011a030b035041c0d071640004d4011a09400078107a00034107211280855825002d041d410140072406020a440c03c0200300001010011103a083c00740c4590201d4500d84403941900003402c08483c4000c05241c0510290303000c0d20451003800700180030b4010018880d8840c42c01d580b5040f2801c03804500e004003602e030341e03101604040c00850f40400700300a01c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 259807230 1250 259805980 259805993
    0x30b010f09031e080c0c030706090e0c09190b070b01060c08090d060219020c0301050105062115040c030c0f0801080d110f19030f050708070609150501081e07060e0d03020109 76
    0x21001d00085c0248920b0705890141424500d890307015805201600070700380a484c3c1c084035a10380c001d0084050689070f0ba203820014441410901350514400780e000e02c04a02e81c0038283c0181041401411310009a03603039488100c40520b41c03104e0213481c004040c041d404c0c89240000008401e6402180f015040421a0007179070b4680010b00c01d180056800700b071a85019090030300404d401420101c9581c1c0c1410b120303103c01d50002c0080800d5407803031103010001400708003200409030207050020b001080b110070f000e800034005203240080200440d1080c19100511480f40404078140c50402020380750001c20f04109481c2080391030800e000d90f028503c40b40c800c0d0f8004014a00d51801c0d031600507884490309040c003415241d6804241c004001003000010041043c00040f61001c0340c3c424030000b1402c0303003418241c4890540c15a144c1c4c00314140000010401d00010b180c40c0740984100c1e00762001990a4205541d8000c184580c1c004a42107086031400b51609500c41c03100e09000c2d00001c540308026641c1c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 259808480 1250 259807230 259807237
    0x3010b0406052a0a05070b030c040513020c01090c08060901090816021c080a090605030103120f020c0916111c300213080109051b0105090a080706030b010f09031e08 72
    0xf41d00b561144808500784803040103941c0040030700e6104180307907080c054a01c4265100d103000b0240200c0f0301c1d040c803d1410300590b040b141d09102507002002402030901d0081c21400d070610965199124038008640d180f44103101d11842194012182d45c80c1070409004072000700d40c1e03080c00741d900c10701c0b00014190b1000000085200f03a4450f00d80c3c0e40d50784069a00250008285401460401c00b007030005200150320004400010000c4d401c100402003506281245001d00160840340c0180710401884095414680c2621040c0e40c1030310b454a0442215880d07955802c9140f00500340e40300300110204030781d4062000c03480307070000e241400054141481d2300c40300c1c0c51005568162680ea4001192400b1092686c1000080c10510000340b1a0101c1500c409955031301250302c1d0704041c1d10350981500c1c1a80990b04480140c0000b520304a1015514040c071a1100c8040c8942030103c3e081508500309513114050400381254151504c00d90b01c0d0950301d4031045904451181c4c5162084103a4030b801140880d03014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 259809730 1250 259808480 259808557
    0x4020309010209031606020c0402071e0f1518170705060c1801050f0d0c090f090906050a0b0d061a060d0e07050109180506040605280b03010b040605 65
    0x143c3c0d9807551106040c13500800100750b030040c11141030280003065000c01d80550013001140c0140c1c07107441d82d040c0010503c007094113200c078022107000a8400c0000240210071202d005604181503201c1c408800710039030b800f2100380c4443d13613102611940091240314180008040304003a4038103140c030340e99486142010580d54402c2c03841010941c940f004194901d00c3c80b004101380b8100c1e040c00441712a840b018000e6088401803a0349684400903198030440e4000c0c01003040e0150720241e150344d004440e004003070725081a65502c4c00c140005118503102d001d200c5d40c004010f084015000c0a54072580010324600480c00c0d5542800150304006948001c054945c1007a29070b03001a440f81c0300d041c3c00749464029170103141803188002e000c020300000401c1860342203680050203d600e40e10b060025000b4525900b0040e40081c000720002807020f2441004c00040341c12500c1440d299441d5501c2d0f04480c0000d115058005000b00400d100e41d0f480b0b030000d0440a10100c841a00020441c46440810001d1100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 259810980 1250 259809730 259809733
    0x80915090304261e010507020102040b090405150901060c030810050d12051303080903060703090507060c1b080102090a0f08060604110705010f05160e090c0304140d1e0201050f0a0b06070204020309 86
    0x1007084040c21b114968100c21640002c525145c07034900200300c3c0313020302c4401600c80d07560703140090035418000709089070407680204004010340e11080090314030030301c0c0c040950004880c4400030701314415041c00c0d042962070080589924540980d5039606182445201c4001c1000910061801901c02c42480003c0c41c803584c06151108030315401e261801d0401003012040504000005c40420000304240094504a1070100484419030901d030003040f01ea01d6040c00c5040310154001003008045d800f511741180300316071104030a07655610804150060740185003058104401055a91800764403450241011007132950418265454150071a4003180c8203501d103a41307038020404c0c011080c2c59003644440090409021200703a85d0042003441000800e01c500d45c510010214003489820f0086e11216001002100c111103c4460024502694000d602d490004103a0344003000a0040c0102c0744680e2500c140074450b80d441010b00c2004d410710201e13142e00201c2c2000603030301507100ca000039807181c07041a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 259812230 1250 259810980 259811023
    0x200a02011e1d0301090206190201050f0f011e09090c0906440f01090b010506040602100c03020f040803030f060409080307030207020109050d0308091509030426 70
    0x5044030350a0125441c0788a0031500103995190020680d80c480030b0840b015040d038100c2000403900608003864065403213a000f080c101c000743c4e036504004a0000b0950b00a010035215041900c245200560706200b0010f40300e00140b042e6052508503444800ba9a0402920a41e42c0c140c0ca100f2100301c1903090f01c0304000c600c024089645240601c03401031141b07000303500b00e0000c00d101102800c0c68a2060908010920300100c4040e2440d0195400102000007954034039000d82544074001d10170000c0441d400c07100d100000403180b5042050754125121a006420240c52001681cbc000704004842d03501419800d10103070029440c40405440a810014001e40d500e0620120340075541000400c0700e0301c52414818060300103900c0805a9404c11428240583c84e1082840142e44d070034101d800954200601908940a242d408040c0700c0c010650441130f0754496500c10b41d40400d0080407100d55415502c1048104807842c2d2243c444101e148460100c036580e821030407d42130a0002c10214000400c2228 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 259813480 1250 259812230 259812233
    0xb030403031b050414062b0b030c0a05121005011d10080309221b1701030506160c08041514040e0a050a0b0d030305071706030604080a200a 61
    0x61050110340203640c55266802265080b00074032a02c00c900070215040803c007a100442e40f0740500b0b81d005408012140a07207942540d02d090381c03900642c3ca030102400d0800c181c04540d0708020070302607006580a003a1034001070801d41840b0000040000c0e416561140010201c2c400070240b023981d000c1c0c250281c140700c03005416296290300c000d0103000e20015403061041003240180c0042252031006055075841416082018240d01030045000c80e5100359082a03070b4503194441040525180c03082544075440c0c1d0344d1003600d6030624000d090100401561103c00030907032010b090072001940384030a161100c2105855900c86005030003c0c2d0140b820b2a0100300301116481d004002c44107041e000071109030400b403a00161241c03c0e0b00251507100c0150b543c1000c82e42d4802e00c2d812100c0c880c20081c1518a11740ca103458018001e141c100c41c0c100014800c102e14104582c010003d29000e0300c8000d00a2216441d5030f140c500495001c00403801c10f03c4045103090700c20b11404000c420b01a00310340040e0051141c070303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 259814730 1250 259813480 259813487
    0x5040909031b081b071d090a0507030506010510030902090f060f060705010c091703030105010311071b230604030204020a03090c03030c0b07050301290c030d0501090e010e250b040b030403 82
    0x28101604c4e20f50000d1a09000310200342c042034006c40150748491030349486840303d031801e00f602d240000e00346005118010061140004000d4101c0f00c0503108000000c8441104070101d540d028002503020070620f01103885950074100b100c0e0010f070010030500300c24a05000154807684031820440d0709945694800c1109900000318000900040c0d06400919054122407500d034401400b0359030603d550f5203d51404510302e402a85c000030340c020400c046035003040c00002100759281c4114a41d60850362911146100e04882c02c1414504c094455424241550f00f0040030b50000b090341010541d45503a0403010628204101e401140203449030010031515040c901d03603440e030003426982404401c0004024100400503840e0356010303c489204018100300700c0104641c0b25240c452949403002007020300142519a102c61704076800c2540400c84404250b41c00c50a95100d07411031009600140c0d40030b84100130800c5400c0c02e4280000b0310506c0c8646400e065010368221b40c101c2c005142c000b100b0003080580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 259815980 1250 259814730 259814767
    0x90904031b150e34030b1e22030509060f0301270b0901050d020102011416320d0605060d05090105091507030908120c0c120a05040909031b08 62
    0x49040034101600c02c000003101c000121384130340241c00307901c51090454541c00c2500307580a5684030300c42c40c1c024100030494941181c1183d80c00390080d01040080b4014000705240300c5460b541207994100c00b00c96584040d60306402041d00d00307421000402084a01020820086000e000155488040c641d0589440400f428865040b04201841c180c40c1000740da40c4e540351a411110100c64964459031940b004074003409a400c2c880d0070f04141942803000151900ca800411110a0360711442c1400b101520715119920b4642c0e00f10400c15583c20024141203004000e100c020a8043c0c089503c81ea03031000b00304280e0164035080005e5507281e0034440c0842d000e0090b50340081244c401044100500c40304141c4513180503020070103040e40c40c010401040600026907450284044181c500f5203410140010a540440b03000c40d03080c000d01c000311604500c4441518424429a512242858104615140205150340080e014088c818180b4411802150311000b1007601c140d00b81e5458403a0f85d10360006906 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 259817230 1250 259815980 259816001
    0x70b0f010e040c0b0306120f0d1116090203060105070f0b070e06090109060503090a0c080c030d020d050313060e10140705040e13021906020609060609010308090904031b15 75
    0x601c050a120101d00011240b0701a00c40700a40341381c0c1ca0316004005a441605184146070501a007183c001e004580484c01d103124100503250b464451450241c40c40e11541100d01450307000010403002c1c04944aa640a1503001c50b060402d14542070036925061480f02091200f20b0344000c13528100510f89901807801858001c040d54030a05207510480041c000c071010340a43c00030494040005005100100f1901903000d400005a000c03a60701c07076900903143e09210b901140640302e02c4011010300d910000310005441100d6440d203045489442c0404c3c52120306503026500750f03841c0ca203c03203080d0105101098442c01110b400044115203001101510440105040d0030f00c00140000c00401c0c1e05400d07401e5003c0c1c10300d82000050403252000603880400301c52655507556005c1c001040c5141c0001da918001e1064000315103580c2d5501d0204440300a09010050141380144082051800c21034a40d5400502c81e003401d04020f001e1000320041d0084802056070005c1d012840451041200c0c4144034401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 259818480 1250 259817230 259817249
    0x18150c200f100c060504060b04020c0c040b01050a020703030c0302031c050402040c0e0a05060f120c070c0503190b07210c0912032003091512060a0e07140c03070b0f01 73
    0x9110007040940601040a00509881c3d190340002e030400a00c8c0c0e104440058006100715100c0103824915031f13441000504060141d0b107810b00014442d03010380d042c0c850030100c035401080c440b411740e942206d0039150042c08a0940c807060000d107807610000700150b0b60000c0301400c00985d5107404e0040000365030113a003121041c42040d8540c01c0341620381d00c2d0301c08103a98055403116552075203c1d83c1d04011b403040d840071185401c020400d011103652690700902d00c182c0520384480403192140c08150312000340700050102d159001c5603140000e0f04050402e64400c0541c14581035014405442c40761204000141c6482e5030b0b610f05200f000341d41c102c64600042d161603290b11355a100c003070342c0240c602204100c41e503a001a546002c401111020004c83e50344c1c49028107450b606810340c007084c4241d46c00c40320750041c1004407400001c6241c03c080c100442121083c4044074265250103400380c40d45100074020070703404070b002c212080f0300ca10200000c02d819445011641070714942035411400000042e040031101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 259819730 1250 259818480 259818499
    0x1d0103090c14010c0203030a02030301050108090c0d02040e010e06040309080f010b0a03061113030b0a050a05071d041103010f0306060506071a073005060118150c200f 73
    0x706940c02501029242034200448040d034003400181c3c2c8500390144002d50511000901748030b4079a0103c081e604954080e207800340561541010151150b0700900441d4000d000301c1d6401026203031076003108001030940000060011601000281171210072a02540441d1008a0810680c4810040861707400380b44e1000304060b0a0000016001c101e2510016010741e40b544011010500013504440c01000c100440014040e500c1c6040d03080307e10203e41c02e0b0030040c60040001c10510090107203512a24403542e40d407980c0a060741c0380d4103020015800d281e4005a44061115910305140e0055018105c901a01c2c0c40c11b41c80c5190901c2990740c00d403c00e034002c100501c00f032000290398034045090003c0f003403e8560151345140080310070340c1a020079480c004d9a9160343e40c80c0125040ea24003455040f00380284020f558481c01907440810303050030842c480022103401c01802900d11401c0c0b40380c10300c40c5002030390038100e82c540e0748000c01400881c40c40c40310320390029140c1d441c1a41100703000c0c07041583c24452 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 259820980 1250 259819730 259819733
    0x20c0307143304050718051609050d0f060e071202240d05040312020d0b1302040f0b07050703050a080310080a020619030608030f0d05010f1511010902030105071d010309 74
    0x1a80c024000c0321003003204894001c43c007000010300100000d0000149100ca21000812403a0b025241c1034803440c00e051a03062140c1c264034460ba090f5015204041c24a0000d4005680c81501c02d8401ca101650129507440145024910511180c001483c00709401403c0f0500c90040010742d01c20b0f42030501d0b00a102c0700e520700340703054000207451103554400070001e00d56440e0705064822594450201410510000340300c4040d9030554424624414161031180705010154080e4040b0702c0341d03001d1414540c03000f0504100721490400204011441007054a18482c3e99070b035901d03c1c041d10008121070500340802080109900003200d14000c1c60324200502c1010410340109055108403205d000758116222408288180a6080b800040c003265048030340e600340c082c54403034041d000312918460560070b040002611200d000701300303015107142c400710203409004400180c0f007441e080d159140c40d035501e8681c0d140240c1e400780300740c911135440f80d142c0e40c1030780e148083c8080e5004d207030710030003030515141100c481c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 259822230 1250 259820980 259821043
    0x906030d0207060c03020c0306010303170f07051c02041a070b07020604110f0d02100504090c092d1205010903030e0d0c12020f1024120201050904020c030714 69
    0x1007283c0640c10169004041420100d040c00c1d40c00fa05550103101d00e4000104140c1c4c04041c8000e601d00801981000341c540c910300b1000070b002a500d4400103002031004c2c0902030030f80107001c80c1407402600018a010f03039401590404500c1d050044151a00216062040c4070f0072418585e4854454800342101d440d1560751031031050b00302c103049030048800c120f802c1900d40340d0080c0d40c0f803140c0c1c006001d120741300342041d001000d80d8400d0084103803079400c0184000c4014020003601c03068a800c0d010006101044809c1c200350107180b01154000c002c1101e1000800710302e0320907804032450044001050034249402c0c0542a540c9124550495074469030f0301c440d05503401480c030b5140c664010b25886800d175190400300c0c0780c0254611040381e80e000c0c04003000ca81d50310503449a1050321721004103009883c10306030000b032038294038400da060190810039000015807140c002020308203002800142030048814001c3c0c030716080740c64225200115820f600d082c40c001004201010200818403e240c103043c1003103138 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 259823480 1250 259822230 259822243
    0xa0c080f0a06090c080102030a09060e0a02010e090c0415050408060c03060d0605090c1c051209010906050906190309051b0f0f030f1510060507081210150302090906030d02 75
    0x40d01860355a030040f030070040e102030b50000070220b1100940d22401c000001d003004145511040b50607625203021040010030106e112280c0b2501615101c03600039640c021f0114041c0c00801e9202106010800031880622840304107003804400d40c2e403241c0b85d82c240490b41e49420000fa14a2001c02e4040c03040004075030303502c002013161035806100854240c55a0030100c0c035040004203001da000110004e55a90b00c5815804984664081c904450a454440c990810b0502c2805262800200254014070801c1c1c022002400c041801602c0140361611030240302c1c2042c440141c03610006034507142b000b005e20804004001c001c03103260403c2d4000e06000c500150659071060b030514040e10104000159642e07041c00820315600c00e260950380501c17062074482d8050103044401c01c803110401600469100e100d131054540580d8411509464100e4140150f50040b400400c070707500d500c40b80c134400700300602968480000d0b07110355100540c031900c80c00204180e04900400c07960003039101e40940592139900046030b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 259824730 1250 259823480 259823483
    0x9140d1d060a0f02011407180b120c03090c132405330408060f2d1314060702010c0c17030403050c0706050306120a0f03080c0c0f0a0c080f0a 62
    0x91100c3d03242c0d0010690240c51a9100c4041c501c0f03280381003145468110450001540003400031242507500c0b007001ca0594007440060708502455180000c642011802c001c603008001d160031142c1d0303040f43d500000c421081072500e91401d540c403945200020002400560103207201d0818440503a1b040001003082c0203094a05600e0980008607001d02420f00340d4001d03000d00111200881d5180e03141c25410380d43c0c0c41c0a0f039078031044401640c0026291007a0001c0481d148034800e107804681d011f9050004d901ca0340142001d0511101225440001815103000f1103030f500d001d8000e40301c81c0ca02031030f000c2d007156a40d0041d40c003442100088440090500302050b40510b2400645580360746460401b1149400f4841d401c4066105012020400e00d070050042e61194070200c0718504901c4450318241c0c1c07900185000100440c0d160440240080d005081081c3c0c4000b0a0303415900304641600d00926014010120b41c1050b004203400710140003802440c10064440080240b01d03060f05c0c0c040e5a565402543d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 259825980 1250 259824730 259824737
    0x90f07140a03060b0318150f0f04031403090106210206120903090a030f0510140708060f0301090303090b0907030510112106010e040b0307030602030a09140d1d060a 72
    0x80000825000f540400082c0c140145220348074a040410451100c0001403144011300c10203000c22040c502902035a03101d007000d014044042d8542c950110344070503000c0e000320f00740044036440801032031002000d03620800b48000003207031b000c1c90300010410100c6c501825001c003d400400c9a40561142e0307044414800c401d5412074101c1e59000389203411801184211540a0000240041840b0100009803426400760341640c43c0c0008802c400c07401c6404409117200300000010000d40340c28001c03000300c0c0c0d0101000e04032402e4103848500107800c403405134000314086541c0708040018462500301c0c0582c400b070240010250181143c45065480d10040c00d5003441503114603000c00d448a1410a856404411030b58141d0407030320740c0390680300c405030840710300b0b000946081c20100240303010700a174041e1800c00b8003e04001d5045032200b03400382d4401088440d40d652140803180c0040d0114282c0d0a00b5050000985054010014020617100f074a0280d01305901085403107907100d07a12142290f418400505 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 259827230 1250 259825980 259825987
    0x6041a09130506011e12030f0f030b040e03120604140f071106040b061315050120030307020304170304061b0609050f0706030605030102030903040302010c021504090209090f0714 78
    0x5041c209150500d500500c50700903500005044148002c2481c8800105041d600d10f10351246079071006c2d111031080113000220381101c00501117000302c2c50140a8609c03031070041101a481000b00c4d040e00c65510b148107055100007003100400d001a601d9a80041c800c03038081c49004c00c0700b20b0501c40c14202a200213141c581050204969034052083c0d1071002d5001c5c3d040d00c000e8036017400c1c20141c2c024202c682c58094540001c0100c0c00046510900011000003000e09080d1400c0c500112815080111010342003004200340d07200030b58040019500c192095030085964074140080140c10201d1408005120b500500003840781503002052280105074501582a24100f41d0034100050000400050201c0c0200c064a946a0760b000c100d03071050361040d48051058547d034800349404c0b803100319092012500240424401584282c4882d00c81b680014105840c000d90b0b0b8904100350380c800e60120890301e1780000c1d24079403410032400ca10303441720910200150350f141000f0007811110901d4107401140d00d000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 259828480 1250 259827230 259827241
    0x50301060b030a052505040509070c020102060703020903070306021201050a050603090a06020702010c02100206100b040e010b180303030c07110a0303081b19090f0b030105010f2d0e0906041a09 84
    0x1180034030001031120803c41d0005c00403c05c054201d0348a401018080d4000400090040740604400b10000380d069000704611b41d0384140c22402500401441541401281e20010101d0840d001070540f1040230b04183d0751952404042104108690344081e000300001c0c410000102d1002c602036083c1c98020342d0250b60b43d003607840101c64015150700000c1d0701c440c2c0c2030f00d8400420350009029220740710070325130009680d032a42d1011202c0d005034810045820300800051084e0003030000640b250261a0a40307900c0d880c402c600180c11900121a06000c880c0085801c20500258040144904005036a101045400e43c0c03001849450010142043c4454168441c50a055100c088034002041410300d0080f809207044010b0400300c4900c90850440c507034400221b100d0656a0840e4101c58058440381d40464907a001990000301410074080815129800b03034031400340070309240d0240c07400703950f80c0c03843d02b8841c80403c000ca2901420f618095403401240d01165100e0031420342e0b41c042c08441c480c603140e981307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 259829730 1250 259828480 259828501
    0x703050f0414030601080f0a0f020a09020a050c010516080103120c050106180b03161a0408010c030b040c082a0702130903170906010b0d0219050d06050301060b030a05 73
    0x80300c2036400c00c000d00190019a0a607000984403001d001102a10202d990301c10355980d030364002c0250007445030000c16034080040c1e00110070240c943c0c0301030a600700d460740c0c5000c0c2c20200d801c10600100841c00006184584c80e00a104466004091400700c0c07003400d608440c001c189002c1404010800400e000000030f016029008a06403158440c009000303d03030326a5018610a00e00c003081441403400d03701e4081040c900443c40328101234000d1303407250060b45840c4c0c29880c1c0c5015a02c01c42d05c441c204100110781c0800c01e005800300040070792008901100403001b0300040b02e4000075910100909a800d0049010b40c003400502c03118080c0c2030311100c0c1d040601045407917100c0c0a0300258807040d95650002c0d105041d82086084600a80300ca014081c205080071070f01c4002103039800f0303054010500601c421200325001d8841500000300c01818044041e403140258078a0b51f219002042c004039202074112024021240900030a400070301c00640b41030b1035070040780005000c0208103911640001c01503400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 259830980 1250 259829730 259829737
    0xc030c09030109050708010c03060b0306010c0f14060414030315040e030d02272b0f0f1401061a030a09050a020a03300203070605100f06030e06070e0312070305 70
    0x107000300202d102a151465490540348a1842e641d400e0100b2041423501030b00c00d14085640c2c441c1d5007855650348400442d400c5990000403552058011898000700d4620142c0103c107100ca0f00040c289800c1908200d0894a01e44220b182d0940c010410069503072910180c01d485031307209581c00300b81014070810b03a60940c021810702c0031000d44040381c240007181014400f00f044c12118240c0c0c42d00850f034101881708800300040030041a0130000941180c6c03991486a6440700341c05070403004585103595454080c0440e030300303005a0314030003011200355035840300303100307290040c4444e1180000d10300b808004030009010007000155a56611041c900511000384523014005500524064800ea00c0b40740800d080001400300c50101d803411240c100510018401040e2500501c0e001941085c125580d5080a03107401090b0000c2c05000e41d500260300da4500134844c2c05481a61408100c04038904c003c0c51408000800103c10461100b0707441c95252408140c0c44450600e401941c1d0b9101914103066601c0d21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 259832230 1250 259830980 259830997
    0x15020403031d01020a14070b0c0601090606050901090b160f050c090604151202150a050403060f060506030112051515030105360c0307120b070201090803060d02010309120201050403021c080c030c 85
    0x400002d100360080d900440c0386413385002030410070410352038810455807409603140e01030100d140f4180c14480c95200744042c0410030345000c0c28030068056a0b6819030007482d491001c07101988407090041541c5441e045190703004409541c204a40201e201d48501101080d100303800c2c0d42d2680644401c259151400c7c2e00c980c6054000c2250381c0c03139581e6580204194070070300c0241c072054034008000d500200580200c1003280c4009250130709507402c0c1148920707054403106080b221445008218522080c100441c1c610694081245055540300c10051500307545004102850440220800d5945401c1205003108222250108180180c0b04d0b001424038003000c1550741070703051207200400505080c3c404602d903071072807107916503803640e413241c0100342e080e00c5c001c580080c400c0009000048203400c181d00007400e40c6005140200d40c1c50100c0d110011944145040080142d469104010a041c2c0401040e14500929603000400703c04203803008284240182c11104140000400305441030040020390300c401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 259833480 1250 259832230 259832249
    0x519080c0f0904090f0b0603060106050703020c1002010912090513051003060510080f07060f08070c11030c0604030609060e12070204020904110a0c030f050f1803070315020403031d01020a1407 84
    0x3091b0305120650070400c403205e510912401c0b00204545100e10f0640d10705541c55001000b0444000c1e0401140c1c00301458042e04540d6200c10000c0814484032003030300000d240d41c5540e240a4100b100348511f002c03001c041c40400c1410681884111192500c82c0400c6a400640c0002c280c1c5500321410f9041006134821140d600ca000c190740180343e000301d1054200e900d0b80c0c40f94500c1d104609820b9680c00004c881c64008101c1c8080500049500a0307203202030f10360014240c07030b00d1651410008059801540040d02d0241d0b43e54941000c1141d144540801d044105c40180810801c4940b52055031041090090080e03802080319940d0b03271125041a000540340c01907481e143d40c41010000c10040707488509400041200303a114845500400466a8291034101041d01d05541482300d00a0324441c0615142c042c4200c00c80040031881c1c403500b10700303030046a18000d42c0e50f5195003401072041070340b82d100103c3c5005440b244542d5a80005d100c0820740da20012a1110003044603904c0d040120641c45103020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 259834730 1250 259833480 259833503
    0x403170702060a0f06060f0c0c08010c080402030c0114220e0a0b04060608130314090303030108030d0605040b091906170a2306040b090a060c0519080c0f090409 70
    0x42030303008110302d481442c0d0b49408211071409581914140c55940c8107030341c00f00720742c0c1c014020780c1c40c400c2110710041800307a40140d00540c4d4402c051400c440855505000081540041c030003145402c0c017065855076003d00e0181c80d0000d00c1c10003c2c50603c100040d0310f2030000d10040c40c3c00110340b0401d00c01c00030031181c00000402c3c80c010f61080040d21101c2c1545115618012000c92541d00070b4619500070a01103181032030b080d40503038007503910b681c042d440d400d0101014455004180e400b007000751b01905919010f1600c4050200911095624039041b680c8175508005c5085110303294201e44376070122510f40f0007070304036a2240c40c007001440d160300806140786c1030200d10201c0c901d00190807280c06100341854402c0e00b06c40544041010301181c020042d80c0c0148003c2000300c0c40b0040e079a80c00044c8078003500c80a101d030b0750343d02d400c4031401922440031030b03000300e0b10344491958482942d00712006030809083c1032a01c042810610f02ca4200c1c250661100801d00c9034407600d865000300d60841d4065141901d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 259835980 1250 259834730 259834741
    0x130812090a020a1428050402070f0b1303090f180b0d051515040e06060609031507261009020a0903080c0618030a050a08040f0f060b092805040317 64
    0x202141100b4001d040c1c03000108000d50301c401c0c0205c0b0344602c1940d80481281010200310203540001000c3e9045401040f142011403219848280a51100e05010241c02118030740585413150681c40070300c502c03505075000c03c915008450340e003641007188031000800d1507111000603c00c0c4441d50b4098107911031001d510580500d408000c900071401d442c0c00740c1c1a10b480d4401c110035640840d501011070b40151010440b10b040110182c001c19078010151180c8020315210b02c3c804110440d124400203400c29031145241b26400d50942564550155030442490f01c1a0301400c2d0340c0700d038816440b0440c2d00040042003184035890300c10295901c00b42c00c0d5a14880941600e603240002c0d200700d0900d180e60641c40d800b500d00002125020805525001d003000c40303440c0d0550752894010802d4800d55005140100010b8454030300400c04e41c464000020008191001e010340c0b0745000b08002c2c072062020b10070a1040d40340c01100d41510100ca0f4020035503503200c0c41c084480c05000b481ca010150a024248071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 259837230 1250 259835980 259835999
    0xd150302040f0606021f020702030307050114130b041403040801110d0b1914061207030c0e060a020a140a0204020a080403180b040501030e0a050f0a0209130812090a020a 74
    0x142100e008407028401e03035018800b034074112041c1c0e10540b000360b4410110300c45901c0c0b40412201c4030f020400801810a503150300840d0541d4810101214540d540da00005002040f0b200056000056401d0070f10400d242075603034021030f841c090406446081c201090303241c012410011140034090800003801526500841c0b51490b030000c41c005c10229080800000d49030800040c01e06000c501142030340b034803910300040c03202e00741280a5095001383e0100890b03500212100380450140c070382076400140459180600030181c46c0d908090380e200744c50803ca40041150300241d140500c0f0740120f0003280c102d5609090340c0c41d290103500c009402500100787c1100498100740f1280c811f41c0251240070000380304007036080b0350203254060554040c800340024003d81d4441e074001c40f48002c86800700d90341504e280c3c496034502a00d0385100011a40507a000030210f0900d140b0350b40d00030043c0ba4441400c00021b503101c00c10f82c0a40c42d00070039604100400113255683c1000f0849441da0068851514151551041c0c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 259838480 1250 259837230 259837271
    0x8030405161d0a0c05031f0504090807110a05100f11070305150a02040b0f0f1c0c0e01020604020904030e010c1b090608150f0709090f1b050c0703030f050d 68
    0x11802d44a140700042c604040500030711916200c0c0380c1d91145999160b6070b190b5904524140150b22405440101041503100c610034990a1030145400c00d4580b1450700c1c3ca034101c160302d40070603806123414520400c50f5484a00d0785030442e00721030900c03c0d00241f0f1a9811a0701c0211082001400e00c92550300100b0301001203040012003040c2c018404a51303850707000c19002ea109911070326900080420035400402103280140c807a9216202c501883c00c50005c0101d80043d0070100d528044a6441d40c100c48041e4000c8845c1c04841428005005e461602d60001000500001c0014040c001c90000400190b8400c20b004602c1641c800140d091b101510080710711005043d0084803a00c5242030408151143c00141c0005841c0041c01055841c2e41c59064070204040060720720b4041c81120080840d0414182c01140c0d50f42004007030024906e203656184902c0182c400d8998402d01500300003844030349201094800c01d41e030309030800310300000145004a409226003920722520524041d03040b4884603030410070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 259839730 1250 259838480 259838519
    0x130e0a1406010e070804080a170709080115030803130c0e0702010501090506060910030f020d020d090209010f0f030602030c0904020301080a020a09021c090206041a1e07030c0803040516 81
    0x2112502ea03200c0040242100e0241c0700c4001252a40c3c00040008038900700400d900580303407518542d80c40b1152500d0b100c5240507a058404142448002e20030051700b48511501c080070301012840d014950b8031281907034440544071068000b08030032001c060040128854004104020400b5528604108000d00a110078001c014030942081d0110b403042c50204140c509c0040010301c4000d2048100100360010100c0103030000c1c860790288000b194011591000d0b0069102c0ba91012422000d17520400c901314130705030012100c2c800015414030a0048100c0d250041c2e85d8030950050b07480e190112040f8a601600d00d81130392050001002007078000700443c512144610a440c4c0a016a07107962024040e40114107612003540040e40302d141105001c1d8004509083c00680000d1070030f510307a400f082c0b0301e85074580da200c41c0c100000b51307aa0b076805040c590001d014510030055810b200c0d559600405d1240b14100c01b500c84a408004070701072001c28001111000003010a21000a80e01d0031807001c3d904a800780c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 259840980 1250 259839730 259839733
    0x305150108010c020c090f04060e0609210309070605160f1217091902010c0203010f020c12070507060c02040e01060807083f460806130e0a14 62
    0x12400821400002e01002d0a170004290310713070700d41e01c40080364400c41300203005035001038550403421a04401804100c0c000d01804016081d201141103c40c100f0b42c0360a1103000844d2030801c100030249602080c101d081e582c4a2900c560390b03000849050b446c10301009030180c06007500c0f010001c1000300c40d100c0500d01400503101c074010414034416000c1c3c085400c5840d0721590300898550030b4030003c07502d901c0f440140305043c80380c0040c034542c01190840f50711140403160341d82d0005a02d00b4070802040462081c01e1503909407072030075240383c0e903040c1c42c1c200c284941d000b40a659483c08085540d513411250381d481c1d24030000c126a507601c0314a556503010a2103000014010140f005045181e450f04030100e4101030030f03182d40f40007185082120306032910240c2c2481e00100388094100703074107040302e4251099110101240340c0100502e1102c18240710640b02658203120100220605800103c66580200100d51010010222158480103805100d59a40003800380395005401c022240d21103a42d2401280d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 259842230 1250 259840980 259840991
    0x40e250305040308040b1b030903182403070306080d02060601030b0103110f030705190e012c040b150409151a03150109270e01060b0405010e040204030515010801 71
    0x80054044803020340d0042c0004040c0c10001340803456852409400ca0303075800700d40c0380005c0c01101d490742e103401c180c3c0c0d4103030542c000140c1003405090b11140d2501041044544201854240c15040250360032483c5460980c4004000564443c0c007962004004044860a4903550000200700039264442180c080340030074036056103c100c17540700c1d11170060032007000f080c03007403a21030503408405213604010f050303500b00202040f07102c0b64a011040d400d1041e40c20f40e101e00c141803d203940094000c1110b1419190981c4280000410a1610010308080158143d400240800c911030200f42810f01d142501040890002800641514183e0001150489140209641640341d8191491105c23409540100310b8105201040c2c0782c1001070015017038001c05060038922a03960715591581400750311000c00c104c0b0a0180140c41c40c01d000d0044a07001d44019008006190810303501c440f0754000e5025903410480240340789112500d603a4129405190090125100950540d002c040801400d0013550025401d04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 259843480 1250 259842230 259842301
    0x30c08010b13031115070807050c030a0807030e0a050405070f03050901060302030a1716060509010e0a0309060e01170f090f010506060f0705031608090a06090f030b0c040e 75
    0x1ca060712001025180350900d1140b86803200407040740400307541e40d8408640400d052a084a0390000c2c600c00d41724500090300c8076410b0a00c5c80c00d00c80d503440c4541c02600f1005400000030780c0501101c441d217505090100500c041c0d2004108480d0103a004260468944814003803840d811480c01c0c918401190360621081d41c441d20428280d480a200007509580112684000140100300d0500c0892481e2000c9007401b6a0890f002c0e500a10501c5c01d82d0034594403c10300040301402c0c02496941c00d1118010074240a180e03030010704582e02481141d08120b2224032070400b9a11520b0170002c2e400302c410f55005103003444603c170103c074001601d4903e01446018071a8030b00a2060084600c50700000b003405060100042038520554800c40c0115603078007082126022000440f0740069691f409540850f82301c900ca04184807240da0035400c05000d0000c0003a0800c07112480082100580c0c0e8086262001c5841e1590b004c42c0e140079940051824610000130031400100c0101d11075068035000404480090a8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 259844730 1250 259843480 259843499
    0xe040f140d2c03070603110706020d02031e090606010503070c08030a1a12060f0414060f0f0915041104020403020307062f0a0f02061317010e031c0e0c10030c0801 71
    0x402c0364064254000800801006020b0340c001d0790105a84100310f4a007013903503913500d022603020701c0d1001c04050380031060000051081c9400300310120751000508090a02200c1c180e95202c00403c00c50401c0300002c00501c00b02e11490200348030030b81c0203400a840b403c02d01034400141990032040320031217042c68011029858099080c10444070058041e00d01505c443c40700100ac00340082c03064030783c0500c900c1403220040c01002003600c40c0307a112030100f08606120420f0781806001600c00039069020012540511a558542941140d44440c000718001503e00103d8041d006550010b035143c00384403000030314160420181c2561109048038022201c03d04400359010b000c50f09401005a408280c0c01400940706400710401c4500013072145081c081c030b1480350031201c48171750440c010001e00000040d0410fa024000c007942a02c801c809541020030040300c0701820010040c1c000314160700c3d091030348403540c814058060800d5025100c610381043c910f5002d0080c08650300c1c03030303400200c040d800041c40251 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 259845980 1250 259844730 259844807
    0x1e0403150228050928080111040501050d27060b030106121b030c0f0501090902040305030919090504030c02120705060919090e0a030f0203040e040f140d 67
    0x1a200c81c8240d0001515420302d40036050300c2c10950038000304100d0001c10303642d0040400d003006905c030481c0c00408040b600030038501d5000e9001000c180c0c103015502290205034029a0103503a000c0c41c0c826103800044c1c0040c005060419660301e01905019080341020f410720b81c080c03007110b025040a108000c02002032501300c5400317100700b03405100c030703002c400e0009508001e04100c403103010158000703120344a446507881d04d2001c1d40400d68003240c4007820003441d604000864000d003007441d81142002d140da100c0039140c0c410700541c5489070888085e0004000d14021000c03020f4201c50a00b08041c0c80c041c13034080c0c203003c100034041e44180c10071620010301130b030006900c1c026100043c2085080184e10000c0c42031000d0b03034081c45007000000950110701c068251042000780310011000749107200c01800d000d0200c2d0400b00603002150408c100c00e00101d01c000c8002a005580032500114002c0507080c140401145640000d086000780d204500000d98801076250b503c402c4c6000b40602022502070100b07800d203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 259847230 1250 259845980 259845997
    0x106080c07050a0611120f0108071d062103040b0a080105030f0d0305151203190216060507080f03070305060f0102010207020f040b0a03050d030e0d0c021c081e04031502 74
    0x9002d0307070300f030400100c0580011110400c0055030b2030911994140d0401c00c81304c2110620750905007980100509442000440c0040285100100c00d44c0280074a130500b000b0010106401742d00c0220742160215540390581c0d96451a00c42078a0700c4507150701c00d03403010760301c54a00305000030456030001c1001d02e80442d08032034980c90f000050042540ca04000d50290800030302e0041c815a0700c0c01d40d5070b16a21201c12044196003a94041c699400031031001a00c5401e8079082c81007154801003944044c8440010040280d03003240c02c155881e408181780814040c85901c0f18564404404028444036a805810450052074101c441c5000800e0341001207080b800780e0100a94080021005a8a41d06081e4814107140714041c2c0704c0003a05850352151494102001d82080010b81d884542c8418204c1c10f221259070744229242810a070882c6400040054920303028210801001d82105e00400a009003100e0301e881c1814910601e4040d020100d0700c00e500b00e03101c00e542c03c9401c482d03400c41d021241d100300c40401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 259848480 1250 259847230 259847233
    0xa0c03060f0e0402010309060b03030f0c0d1704030c0f06020c0309042d09020a03020409031d0a051305100e100509060d0201091502190809040b3c06040e0106080c0705 73
    0x583d516001100600141b040c10f58100c0c4e0b0740d4607808081e44044c0010300c10f400103c2c2100d5a10004072481c203161900881b400010054000600c03000d83c0da902d0702090300b20340c15103410444a20b103400c1400f0b80280d1450700414181c40003403076641d0f0802c0480644000f0b0011a0100141c030120700d81d55140198064000c14182d401003030050164803250f00c42d0300050300140480d075000752685e0105013213503038040041c2c0211b0005181200c52200200c0d5a1169400070b0722450140342c40c140105800310300701080780d00721036116400105c0300616688980c000b00500d40035407000c3d04021062911102c070600945005441c40303400551a07052118103000b4046d03042e034440c000185080208201510911546021802000d60081c5a41600503c64a5140c0640b02107a5a8a40c2c00100412510700b0441c0500664100f0046406c11000f4540140290b00c1c4000040744001d1905807110303189989002e0310307030200c00464042034038482c0c892054180c980d03075201c1d000780b07841d1200c082d25140507400005105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 259849730 1250 259848480 259848509
    0x40b0a020703090f0b07020a090e03031603020706051f1e1e0e0f0f090d021209121006091103040c120f140604030207060f020c0904020a030b0a0c03060f 67
    0x110485030300809010340603260520070a6124101c00030140a15800a00301d2800417408100394a0620315000081c00f2210082040f40c0c0e0b40401c203500ca000007800f40d000c0c0a4540a10b51846000350112420580e00040c201300340e18004c7d01c0300c806007441013509941418510b001003071100140c01a030000303038120f0044039101031400502e00030101404c901c00003588101e40c400039422000c03119584c003a028400d841d403694589280840303e41100142088050703031000d20004885600494603044018001c1d0303a0954400c84400862404012120501070a218400c0100607008850344540180c0d905404280400c2c08400740308000c500003910050315042c075818041141c0e00024485014452048410080100107a25000c4a001d82c08060300003d40154041104060303051007a0406024182800d66001c0503219009580741012030200f401303620410f010a066580b6161140000c641c842c04080c40351401004210190403901d8044000c0790038900007054980f2085161419109680c12680c070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 259850980 1250 259849730 259849741
    0x140f0a0c0308030c1e09010201150e0a09023609010c0f080702010f060909020102070602030f0414031c050d14280b1507170c0303011811160b0f040b 65
    0x1003507001074442182c40d1001c0102c210b40f5900a40414108200c5d110f400e621462008006820341d54881d2942c0b550040c1c4c03800074014411200c15a9401803041d810000708103d4610215016050082485580d501c0704c280e2004080034205420800c010b0014640e0307165115004414207840602003100085280340322405038640c0b1408100e81c0c41070b031610010801104c1d58500d2011203040b0b81103900d00c6900d440c417220640d44c04106c0300c0f0040c640da00c015440c10380700b11450002c80c0128040c0c603004400d0b0700c07149140d40d5010802441c00c451141283c00040420b8940039145900035901a44118104220f0039410800300c080c451158094003c00ca0200301200d80860241c902555905034045d0307580301440f200e40b03410840200c843d89941c115079481c8101d044c508142001c6004040c0c1401d010001070044031408020b80b811a860301a24250040010310404017404800c04040407820740440d000c00003100091710910280d00030b050300502038550b18105058a03808440142075a60114003049 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 259852230 1250 259850980 259850993
    0x30921090f1002030706060e06100801062003090406060302030906090304030302061603141006030f09201810090e2a01050405030a0b0106260a0902010306030203010504140f0a0c03 79
    0x86540b642441924900340ba95030b10401140c40c240c0081403145080c0c000c0011905064203100c0103140d603402c003843d1544c0740c180c0003071110700702140601e000000c00c8211040800100301f61010700d00014418004581c40380c9004009401c103ca1407000c41c4104404151411004801c480c140e0390154081d04a42e40d0b80c0c4100c0d60014581001442059941c6410b60180c00e140c0026500400b0040b0220306010310744000141038841001140340d130b0340d2030314071800c0006031200c4c100b0710025803048005c4105540c00300083c103002000d81e140c00ea425001c1d000c1015000a001c40202074605c0e40701d04000b9001402c41580c0d0f03454203252180d442034028010004542d0600c0880700c2d0f14001450300b14503103910707400403030b01f001c40d062022200401c0c1400148842d903081100c5e00d02d00e1075210100b50007404030740c1310200b0300c01c005070040403500c0d86c4101d460256440b0b50000000303150090001c2c0494105071900a8403088c110401c01800d0103072000c800039010003c1407400c0c1c06074021001961050560b1030b801c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 259853480 1250 259852230 259852249
    0xf0b090a0515091c080309060702060603070b090915090114031009150b030f0a0501060e070503060307140409060c120c051e0d0b1c0c0b0f0313050c0402030921090f 72
    0x1a1642004d00c0c05040008180c0e0000314411500f541c00752159040400010746032020142200e4030a410411081c4001d0407000d0070b80d440c1c000101e81d0070340c064507600c500c114034004040c406a0008540340001c141ba10003000d180a07072a00c143c04a5642c05e052041c03d104aa060740c00050100c4030b403042002424200f034220f2114502c00505035000400410249403808585210031601a510340d5800c00881d19000751456109001d0304001b85189050400241c444030180204043c01e808505160560344032540f1650070340f40c3c008002c1000000441c0080e0014100f501141d1101e41408150b004591103001030352126981d101000c1e4200b0340f28100c05460303070000c2c1e00e10300c04656140d0500030b00341d41c0c40c042c42e6a584480440c4e0103140c503043c18070000560280e049000e5000003003081c0112910400200c82d444140502d03824090b2038036141141c208000610040e034464000302c184042001c000c00d0004071130394144402c00e40040047c0c45a20b090040903021540000742031003045c017034105034007031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 259854730 1250 259853480 259853509
    0x6090609180109090203070b040b070201121820010c050706051c020f07030908190311190809011812060903090e040f2a0317040f0b090a051509 63
    0x500791100e14050364100024003644545643d5448500e2441541420701802019041555100740381c2402c0481010140c0714104000b8100a40c0340383c852174940443d4480d02c102014030500c80b5811500f8145840702c9110001034841303445c48100141030a6020b441c805007155408070203000058a88801501c0a0700040340005003000101d185a000392078520003440c00b04e07401c0d4000da450310b015040040c032200c82e83e00440501d0b40196600d50010606801c600760050341890302c0303179110042410840c00c01503050b80c4140903d843c5103880c400c00411340c0c05803801910a03a01c442c00b05054039071038428142c0d144103074200003035010700342c0c0045451038000c4c405150190030132007165540d03505c05445006d0111010b840c1c03072150400782004c00c43c0d50359080ca00c041018049003440700c28501120b800e00d0251000a00403911540f03c5540b1a99900641c0c008204142c540007055503944c444002e617070b008040f610300c680041d00002ca50391034000c0d8000c0f40550045402c60800250f80140403100206030035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 259855980 1250 259854730 259854739
    0x9070509090c060c0d030c05040e0408090a051f1e0507060c090503030c10060e06100c02031009030810050d05030f0f0d0f090c0b0f0708070f0f12081506090609 70
    0x151a0040d101c3d04000c102c07529a40c0300610315455a41030003012a0340c602c10401c10843c00b00020003104c6082c0e075030103411075005404150b480c07042e00c0000c0c81d5401e480e81300680052151005180502c0f152a0341c400d01c0c0f64a40750006060100030000c031f0006100721100f004500c06005c0440071800c254800944030070a410700c8a041034480740060b00d5900640414002c03684848000126500a40034503c0280400e40141c051030400c0301c0001e200e403040309440001c0281e090f0761442035580400c07019140601900c2d0400040300d4070309000301300d000304841c0980c003800c0c00c020000300c509001086010290700074000e0f6007001d21404000b0480e034061840c44941e82002e01003a026a8544d2043d24a5014401400501e414044c0b902c02003400075a480082d180b803092102c241c03000c50442c121659154005101d80d074518051400030300c000344040c009003030b4210011800b020049600302d80002d1a4140e101e840240c2d5559603020030280180b4581a000002405584040c0c10700070080c0151280050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 259857230 1250 259855980 259855993
    0x60f18050a03051015060f030b0a0f1211100f200102041d1302010206060103090606030b100812090f090603010f0c050904060b03040b0408070c09110706060e0907050909 74
    0x251204001e401c00e84103a040010b0b9130540c0d0103144141203202c0b100207115020b9900d0990f000c2e042180b010070031018107440741807200c0e003940c4201504c4007501d90307500746541458480200d485d40b00d80b00304040728030782e0003c04518424941254415000540d0356640c80702e010600fa8100c89040034010120704900003080c0740b0010000030300251020b02010900c1c55510300960031846041200600640c071150040152034000d44d0340410415806003003824046490300503490200001c01c95584050040ba620f9014403a004d000b07060f00c0b10849010b5412209503001d014140310a5120b0110590740c415080a0070001d03600300801450313800200200001144544200c426007076804210850300080c0001078815480c0c6820312401000c0d018040b41d0341d04501e456502c2644100000c2d00180c040c01c00481c48070704200e04c5190600280c02c45803014000100d880000c14510341103000211481400e083c00866803080744407860340b0400700540180340c041c0c03501c020301030311060240a45803c0d01400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 259858480 1250 259857230 259857239
    0x90a08060411010f1b0b1801060f050103060b0319051e04050a0b18070b0c120706060303170c0a11071707260a1b050405010b07020f010504060f18 64
    0x30310285100354010006414030064800005100d0001d00d907822040c008120140c0e002c00c0000d0712080002c50f4000036401450310380c1c5428180c0e40f60f81c00c01c0380c0110f600b00340d408145c489505034010110348080e201400000e80391010b00ca2140422564211703082c80c804016440014030350000e58004903076200c0d10484081d03601c030020084c8402c44060300d507036020409040421a410740d1480c0e2000c0d41071411714003a81d11010150f00c1c0c4100340706001501a0201e00365115800610403488681c585a004030b68504103440c080024003018070040e4007094a4141f0001710065031000e040c42800a82d41440c074100c1d500006441c030300080207088000d0300c02d0200200750700c4d41810081c1c06501003071005000c1d0a1804004a0346505481c8120146140c4c141400000003400248807034420f61101c00700003401c02c0745100c00c40d4039030326502c55540241032000000d00d240003900100140c5000b995480040c84a20005542c0b5203e1441540c000408100c05445441d200b100168184841102510b00180c0d46 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 259859730 1250 259858480 259858483
    0x14070201020a12090804030803040f03120221090705040903091e05010e011808030301090911040b0d0f0602280f0809030405010e0d02040e011d070503100c031401030501020c07060201050c03040602090a08 89
    0x403201250b8601c081c11656033810b41000c19004c0c84180705000350320f406507030032901001c1c00103505d86440d02104400850140342003846441c01a1102038001c01607200e40d4140100400b819100c0d000f260503501e503068800507074041011080d214180c50b0b80341104241ca00440b40482d14805030a104c140100b8040343c0140d040c0b00542c0203084121340400c4100746810101220344c0708210340361041d881d051074072440d9120340d5801e031841c1d17070420000c0d008100e107418410003034444c2c3c00c100c54036803a802500c8281d40300b010480041040c140d548102e030503c411841501d9800d02039070200c40307952081c0020003c96110b0500d28603825405043c54016195560108050352160f00e1021a1651101a0400c20b151380f88400301078045a003006241d581d2502c40807984448004001c410f246807940424916240290070044015046205c08030403586c0d6414507a000b50402c0000d50101c2c01400b000041d014814001d4501800c03801e4001032840c2c5480d035a4800079400300c0742d01c0e50044e01c0004c0c000303200e040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 259860980 1250 259859730 259859737
    0x90c081b0703090b1c090309140a0e0105091b0c0105041217010515041a03010501111603030c02040b030a030c0c090c0503060d02040e0304030b060411040e060f01020f03070614070201020a120908040308 88
    0x1c0b9858808c80d107070504415030f1001c00d1500025000e506d284504111920f52440c4031030445a05640c481e101d030302c1c0c100310103000c07000500c0f2200100e040040c40d00f10000d0154800b84c0304501031742e400e01075046040000c1b01c0040302c00712a006401403100062016240859600c840c1c2070301081d00a00e0a0fa8880003081a00d0b044030681c501c070900800104034550f00107800b04180429200904115248403030741c0b0302802d4860001a08200984444100710749565100b45880d030307002012200070821910b03004195801c1c0b01e2040f1b070280103602001560200b1400385400500542d01c1e03403400c40e41c0382c6040c020300070890401641d229490703240188035030101380002e102450052101c2001407070070074244000d851005d6003104a03950108010044c0101d000b0555401404c100d80018542e41c6c0b540040b4903101c09250b519019000001c2d507002000300e2903128441800d00c00020340707210342e42e0001c01d03806c034020400c080c404110968031a481c81a12903100207842840352405074242900c98032030300100d40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 259862230 1250 259860980 259860983
    0x108150a0605040e0702151303051303050c10021902060c03041a040314060c0406030504170c1b180c0a0201020f04090204080c03010c0912030504090c081b0703090b1c09 74
    0x142e00041c00e0080c2d522295900d54070041034002424400d083d030303415405c17010004080d8012010020140c2041601c200100c403c041d54100d8880340c0c00752a420215240c05c0c4000c411881145104411100c1d14008162010a1f802040b2901400c1c8541c0d02441600c0e4840b000c8100640000c200200303060813004014880079039001c11f500e86890441c60300d035041030521038003404954022020400c4529540c801c40b000d0740c1c0280b501280c1070301c4901d449a276100c089035041d59500800f003210002410002001903c0100401491480403601014011780050083c42c1d440000c06410015101c05107000c006c1c1415911480018032f003c42c1c041825120390010b40084200e1030300003c0c20414000100001c69031040e0490003000041060761014152100521400d400c2e064411842c90a05004106072001454108801e00c18001c81c808020034418081300c0503041e291000104030844503100c41a20506907040d02c48240c0241030280b0400e0f250030441800145000051100503101c480380940303800c55 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 259863480 1250 259862230 259862237
    0x1b1807080f01080a0b060d0212120a14190305040c0e071709030c061603110f040905160203030a0209040b030f01050f1b0d15050d050a051216020108150a06 68
    0x1420071441c400e03201c0300c040c0c0c8000e005034048070300c0c84003160150a01541028007201d011703d80f1509440810f00030800700049080303a0145544c81d05007140d01d440104412017a9540703116240e00b03811110410b60003410f036900c11340e190b91a022aa140c3c0654800c5401902442c100c0c07442955030394240c100030400b121010006181241100240e114200080780c004202e0005981081e114101540d5a140c1c024090000064000b100d00301950007030780001419480710700e54603a01c0c2c5000c070118416511920900d80240d2809001445125003406259080413139540a5891070300c0e05410312003e9003180a0710b60384142d45800e04006982c08000303141102d00340200203e01c42c0307041e0340c102d01454001480903e03c0f01c44260100480c01c01c0c04220b540300f2080810008101c4210b0b0020141100f2640082e0b030000307001240f0b01c040c0a000909002080d00c544100d0301e0200d00d0b40507010a5004060410204854034a50040150300603004540c0c840e150001c81c410b4480304100040c580361480d030213000403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 259864730 1250 259863480 259863497
    0x5090f0d120911121b090f06010c0c0f241812020f0d05100c0e0d061d03072d02010801090c120f0b030105010e060108041502070c06110d0305091b1807 66
    0x24900c64100c0d0a4005030202c4180d031907490654018040d2640080c0700b52704000550a4881c00c100f41c03684050f003e400c254000090994179045002442045141701d4003114003248496109140b02c2c0040e0704003880c04007400381c281031420350760081c078110040c0100c0c2d012511004603201500c40c0f01e4006001801800141215030076400004102c4030f61030f00403420400030551458241d116030300d40d080b0441d44a00c002074200311500b10560f182c2d46030941e607010b0740400103401043c04841071030864084450044ca00410b0041100c00c02c101100070802030100352088010001403c9586c4813280942407130824144800344030708407900711460254402c00b03055948004041c907040922849015283c44440c5c0c0f981e03820040e001802800c001030000745490588004640e11140c0d07601074a40b5aa805810600c0103074a400010701810010300c00d13207100d4482c940034200c12600c24040c10303001c2c4c0d4a6034040d05182030641000520000340044150b0041c201c80305400541041b2185140300b21082c0d078a481d074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 259865980 1250 259864730 259864753
    0x504020f03070807120f2a06110703030c02040209180a0c0212090405041703010b030703050a051302010807170f011406033102040507020105090f0d12091112 69
    0x491581500c4070702070b5100740001d120345140001e140701900c601d2151900403081c1880e20f03074521012204c000b031007492103030038041c4a088551000c00008102c0d01d001d81d09582c440c41e0440d1000e80b07081c09030b1800d070312a030010004a402620312900160008d40090b00d04400440400e103481d081460b900301c500008020000c019110b80f0440184440c1d601c0544040702120100c009a4010106071510950741c44000c902080b840502c48540e00702d01c020065181d41e91809054020b800455000010a091000003407804009210725072183c8810b0120b20040e810035001124040002084681408080c074100142e65a08001e0207100c5c1c461000c11504641c14507210100c2d104801403294007400c4d041c01848070045100c9803491005d4103141d4401c4803c584c080240825000c0e1803070182d04585044140b00340701e036040d000310f44580e50880450b0000034208a00d0359403040d0f4820f010f40001c900c510380142d500d00302c5c5c008500140c050070b1050b1407144504006030256421050000c0300f80d100209814 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 259867230 1250 259865980 259865989
    0x9091b0306080a030c02130b090403020d0f031419290301061a03011a19121a150c010b06040b0a08010603060e0703021605010c0f0206010e04080901080415020706050402 74
    0x10b00040300140000070080d58002d4507404109000900c00d03a09175800342d110b0000e0398480010b8000c001c100c00d03d41d00705414080d441d46400f1291400062001790180c13440f600030f0080e858a81c4030ba80c040e0100b41e869210460103c1040300c0b0f0410269180c803070920b0451114000003959600240010009240c03040c101400c481c500d60002d1034642d80c00070080301449201098a0444420700449107580c98030070098042446040c0300b400e504654611450301c01903100070852458070881034204049016114560343c0402207c00031607001a4901d6019455501c103409000d21a00c1c20001243c1e00c0d280c840000c61980203500140c9542c48007081c107002c0c441d4000b0103d4010a0700f410100b00c40303801d21214140301200141241d00b40754002a03030700c140d09100040350500c0c58104c802041070b203001d100c005200e0f8110340701020061081c1703030001c1075109510b0b20450241d9846181381e45040314a1006440c89500200140d070394220740780c0c81c0e88030523005000810485225020016240c9054810003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 259868480 1250 259867230 259867241
    0x20702010c062409051501110c060d0b03060703050103080a030e0a120507031b08180d02130203010f0b281701030303060501120b0312030c09040905070e0c030405070b0a09091b03 78
    0x20030f41341d05020901201049401020b04c2540080c42d1916840c0c80744c241c035920700600d00031003c0c2c002c0000076104000203c190b10454501c03c0841c16a0032603250b02c130048069810030300000d02109001c00072491518040d078842c50b00384804100352803c2c0010307511613595103141e10b1440d001003000001c00004041d0b0198a52440305614100403980d5251078036990340a000300d5010784054904641805030039641d00b510300002a0380104241902100a1510400fa42080c0b00b5120b0801020710f01103010b000c004213a0b018010b0751400b9510302500c19015100c541c0c0b84c0d103800d43c284178a40400d991690300301d50589010310b000c0c0e14041005032511000515040451800d5201140340603043c3d046581c0200b01d0900e260742d2801003d071a500c44590f03100e0544510781407140e10a24006110302009804039800c0c040358080e20051401d561410030700c074800e00c0210ba000300300b41c00c800c2e0180700d4407200d64003410089040340342a2544588440701c0c40100c0700d00ca0603000c0302114004a07465155498000d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 259869730 1250 259868480 259868489
    0x2210a020315011d01030c050408060a060303022109040213030b0a0204030309061103031602011508010902030106050402030603070905090309100806030f0304150815100801060e090609010306020702010c0624 91
    0x4e6408076040080300c100152084403454105903c5842100706c3c2807150094a01030705812041d2951420200c2556004010385d10044015000304211003c5030316007a4101e20090b2031301c240700c034a04088002080004d5200528024108250b0b44012022a00c11000140300e20520f003c01644c4900750f04001d0801500755000008020310180615503c800100030340c1d130081c90600350300c5880c105428041c3c0c0903000c040481903c8200280000405e0441500858000340c025002004120786810030701046e4401140c417990940d22211b070401c84110203501440c0e1080301d08050700e007404035034000503960170301070f0210b117002868140070720205250034040d0b0207070310802c034000314905880c0c29441c5011000c1281e054081c41520f40024111039108044401290402002c0329038005103588007601c2d19000780103403030000380c0c000c0a040d40780c1042540c440c028400100303d10016865560f0743c0d4040c0d03021307000030ae04010a0120310000103e1601038801c00100da10990b1000d810341e01641c80589555900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 259870980 1250 259869730 259869737
    0xc0e0105010e06070201020703080f0a120e030a0f0c0b0406050603010f0506090105040c0c0606270627090507030302100b0603012303030c15040c050d05060a02210a02031501 76
    0x10025603070410351044036902c007940e4007070f152481400140e0030b144190b8405054640e0014121200304ca0500c014040402e8170340f1102151100056080e003240d950b03034002d100f01e038400c1000e03900380c5010b003031094a288820720b00b582080e02203036a07110344d40390241c9040300c41680340e03400e01c00d051400307010b01da120a000280c01c00642c0380c440c0000d450400107200706030046541e00382c4904540c1c880c50301030b0146030b004030040c0846641c50803990242110807902c1041c01e10018004c2d5040e82c080e00a040803285181c1c0e003040800c00b003103040e07100c04050b40c0080030307426548e03154040040d0007400381c0c00046000b50050410111109001000d40d020a2035440c440c0e0030400050100d00c0450340900480034044980110140707503207021915511401c446039000340715003c1c80d0074a011400b600b20344500c0c880d80348031062030780d1001404007015412400500701d40114001522602807540035000000f01003100c12030b0401d0b186d40e1482803c8068520120f202d400004000c400e2070f001c40042100b180a00c1e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 259872230 1250 259870980 259871009
    0xf0b07020d02040518011805071a1e04080a12030507091a0c150109061a0304051509070b0705030d15030803041401060e01080d1215050d0602040b04120c 67
    0x18006625948001c0009104590b0b6a011441020406503220f801400c0c0d40020020f1400107031801020050702d150440b4184a1000042038810110b00d40c140030301411001e05003400075040600e1030944000411000d0b940741440f0006a6410800039a0545401007100c0803140c081120300800342e0b50005e203c00705010448208024140341c0c1c1da842d40e18100ca11f02115142e03a000d50640e41401800c040e110500007101001050344445580407804448244940f03888070b4000c1064031045020407180504290022034110250800743c0401941c0300160400b035a5001c2e0f00c8000360110350300041025a850360010905404000ca40d106030056504035941c0100283d16640da681104c0c40001c000501d904400300d05680e42d031313400b500100c0103880d56940c94011981c581c4a015a629900b10304407000031440c0703e501c81d55a90314442d80340c03000c0f0b0010955900d14100340902c1484040d11004881c0346908100014a6414090140000e000c0e1607604524400035420b10b001070a981e030b0040c815404020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 259873480 1250 259872230 259872233
    0x51203160315080a170d1d1011040608150316090f02090a1e0302090112060b0a08070b07081c2a08040212031e03090d02070b070323070c0f0b07 63
    0xd0344100040d84214040b4503402e5030800250580100302403206102d061081c020911044210138a80e00c880540488190002d00081d08040d549d10848494003404108010702001c0d01c1054516401030789480301c85003610004020914040042c1c0c00741010108004040c811004180507039214680e28103015800c01a054001030340c080d0300345c444c403040316441c1c003001c4148034500b454400086400030b20740e480d41d60750b03107011002416101c5c8048512900e0681121154a4100c1d0740740d080d00d0084005085c1242803800c01c1000b035000c0d000036200c1d24424014812106101c1c9211948000700a00120300540041a015850f2000e020607103d400d0765403082d500f0b80b80e44030901315070054040721001c45c01d411031503085007148100c200c8407115007401210088848580c0c0c000358024010101101e42c1d85074610701c12a1201040e0040c54480e04081040c6000700b8440d400c2450607100101c0c0081036440c0341d0000a0003036114003421540140180010421205001c007507000504140d0b00d20f5150200c40d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 259874730 1250 259873480 259873483
    0x50d0c090b0a080a05030702040c05160201030f0e072417070503060d080307030b01080603030a05040e31170a08060424140301050603010209030a03030905120316031508 74
    0x14021000d94503611005081d055a6011540d030061202c4010f440c0c126074a8180303540c8941c03106c0c005031301980c1803418844206100303404039a4582d072040c0c442c22032203600f640110302030040c40c03a41404035a1203c80003000e144061044000038070300301500034061051560388090f8484604000300c140031202c00e900650803070342813056901200307618000b65256203800004034101c030403180191440034044100150250198807158245200341c940c4034103a9103110416a0720311804030090001003042c4010004030196a01880d0060050303001d14000700c1060500400c0035210400e24070110ba111450b800c1403200005441030040540c80711076250005006000d0010b130405802d0314012592440383e10550b141d0b000004003079003108000070251540e200034843c00c1203004d94070300307110354a041c0c00701b80d40b0329052003221a030f501e020700600390f801c4084e1070960080000000580301070242c00c105c890b2250401e0029446101d1a410018007440600340003000c90702a0544a01e4080c96004140603500f070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 259875980 1250 259874730 259874753
    0x91d0d03051927030e0316060c030c060b190e06030a0b01030b06130e100608061b0c0304090c050a081501090b13090903020102070308070f050f03070c050f0313050d 72
    0x1118480860948a042c84042550440700c214032070f0900000c00c40000c1550142d031a480c444070440403541400200d0300e80d10b030700c0f6040c1c2c070542006c1111034503c1e00002740105e40b2010305a0050200142500c1d0b50b001082070000050f02c00495061400414841c410074103243ca034200e4000e40040524044940c1d903100c94000601000d0b200300402000a109075607100f000082c02504c291003840303c120006a40e80d9521520034009070014107200020400740f900042892080202500c0d100410000704086031280c0d0054202d492280001c11000c0b80c80b140902442d0394018403a581c075562041c0d0541c00034920b04e4040c0c40280706030030101000300700c1da9105501d0001d0b26501a0f10566900450034a800892029031140c0102410301080700103041d01035016150250203610340404a5503280c0c800c4501558454006d40456400d0041c010f1005440303000e55405551410442600d050039100c90b464040c15105061056000141c0b000010751000032903c0145030a0b5003004104020b0b036118010540c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 259877230 1250 259875980 259876021
    0x121b020108060402070615050f060310050103020a09030602120f090d0801090c1b0807030801080f1c0c06021c151d1e340e09060a091d0d0305 62
    0x1a0101003601583c0d0b40d41242c0b6030796070008040094880b5403a0581724545113215207481100c003e0041055070030500c08403031081c0c640c6400045020b041000540094100300050000c04c003840001000092040c8003d00c0b400702c0001c4001030b107140000c10b0b410841c10040903242160000c00d4090744035034110201d1419030300080300200300c4076036008049411409060307100210720749806a174004d10880600605c40700c3d01035910503c950303880f07042081d91004001d00740c05c0c40e507006030301803003400b00c0e407079507a4103810b20500e004041201d0ad03441d548182d810284070780e41ca08944440c48100d446661003070441402000d2400d00c5200d14282d2648041c12802044100c0c0c04140c400250b00c0070070121302c00c130390307003150281e524070034248800100e0511746111840300391f048268800b58402e2140e5419500c0b00c00b4545d81c0d856540007008107001040c4005400f56401107070301030000c18180100c2c003410300329454001d650204541d90030304d040e103040600c04912003407619101c10300004183c0401d03596070700b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 259878480 1250 259877230 259877237
    0xe0906010510080f06060f070803190501060906080615040b090406060905030a021201020c030307020d030e06100b0a1806020a110603041e0c082d0601180c02011d0703121b0201 77
    0x185c0c1d0704170109006218110007181030101c0069904200602c03440990700808995090034001000c0c02e03010f01c00c5510a0107100301041c0c04000401280f8400e1081c02e0307008101910145441c549212420a41e0f0010303009507101000c003003280000e0b42410710450340100070918141c0710300307417a00b0b0210b84c584041c00b201a0080c80c05040c1c2c020b1091003501129072400589084030741d80e01d4480002500c4020003000036002a0800403489060b42c5c0014405002c0d0038007085e1000c80c01c0c41c290b000b004ea40d2140015109010410030521600343c0072200c040010400e070b80141007180550310300030b920b00c0580101c0c1c0e485018140240800f00d544148103c6000900448100784190750b07040051a03208203a016503440e01c0780c5140340d604a070a100006072000c85036130300e40401202030945542c441d002401079001c88542c4020803c14a4295042401890701c51700000848106031b48150b403201c081005a04015030205d9410010000c1c110301c0c4040a07610707450800840c07458003030403040c10101010040d042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 259879730 1250 259878480 259878511
    0x4090c18020c060a05011a0703090b070510050711240105060a1403041a0606120412030915090c06050c0304050919090606090c030b010206010e0408090a0e090601051008 74
    0x3035000503030441c0c8541a00030300301d580760f19010940c10702400e0240250188421000c6903406000b1800c0c1c2900d140603415204c0e110098200b1070107c80c0760b0800c1708103440e00e2041c0b00452400703401c80e01c5594040c3c5460307980c40b40561074010100c0d00e8a07444403503458140c65400c03e01e0740c1c221100c400c1d1506403030303044070b43c1540e8a002c01e07401c84404101d540d8505010070004240010090035041d0032420b0595908000403d5491400304900d0380244030051842d840ea000000e03001842d0700607243d988000070709002a00d14580c0c2c4400c16108132544400200582d07414518080c0104030180200410b06031a0403072604072440c103003d40728080c910420f40910300031008100d0a00c8906845414441420810890b0f0003071810b1402c098040d0b07201c0c01d40110b04c1c0001c070300d001e03512901940d1013144041c1c000344100e910380000c140b035102d0002c0060307647c01010b00000e003c0e0741d902c07070b480002002d000350583d885080850056003010f01c10382c80a48100411541c00c0031aa40219245900c0000d070101d9484 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 259880980 1250 259879730 259879769
    0x609020f030a02031c030e06010e01060f0509060306011202040f0b0304061404080403150b060a0f0e030106060905130902060703020a30110a05010e0a0501060e0108030f0d1b080105010e04090c 84
    0x945924100148623000b203800204611031803200c483d04031982951000d85e510720940d02520b5600c11041142c2e04007201304000740b0954001c5180c0b40007174105000c014507069031103010580021a9070401e000000000081c0010301a09024094080302003140440311820301d503481024034030492200624200d04075444501c0410598851070040b1005802181d492140c104010081a24034280001051680b1081907080c14140308e0700b8140d840a4880881e91410441004043c030501e00d2440c8080791600c8900d401078031580c01810b00701c0d00c03d40051400c000546810b5041c0040c5401082180100345070b0450f0000e04450304c070442c02464240f071401c038400c201c58241090840503024003103600705041051950b000044041c10340780070708002c00070103855848200e4038880c00e2080b01c81540c400e00000f0300c08910407008081c0e038080340710002076141303070341800700c030a40700500c0300b00d000c110910700401117075800807a951000002200c0400002050359a100d10080381c43c000c3c0350100741c00a00191 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 259882230 1250 259880980 259880987
    0x503010513060f06050403060515030309041d01020729070203030703051509010803040f090216030f02150907050901090b0117100b04080c10090f151b0609020f030a02031c 75
    0x1c000d000c1907907140504a80f44c030406041580b0900c0308a03020782c80c05002808201c241c0e200c1070130a150090203589811003000400014050040002308425800e41500308404024401003d10b24420507034141d000d403001c0c540f8240c000e50b044c20440411186010070040a07804411a640003c4a00b000166615840c2c8040e0040040e411980c0d00300304084004601440f0010160049880441101001075180d18880003a40201e45400300404110409136000038094608034103144180d1044030301c90301610700841c003840415601c00c059900440410702250070203500ca9400340c0075100e0203000d1941200002003603900b61030084410122000701207041c90301000c09407401407407181d03203154445480d02001c2d41c4a9024450b1039103d042e09140c01081107000e2940c000440740e0070b0700e01e40a558070b45554690090440002c0604202c00607103403c040c944a000c2c402201405103400288a40582c81400013185070008120b01c00e510003004400183d40000d5842d265001c00b015454050740b1a00e000d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 259883480 1250 259882230 259882241
    0x80d05030c0f070203100906051b0304170c0703030f08060906011b060e150f1e010303140f0403060209130209100c0f0507060f140424020715030c1805010503010513 72
    0x82d030501502409001146c07864020304240c60090104205544481c1c090801e44021010440e286210620016000c00c1115801080c1c0e403c1c107800b00303403502c1010b12045003001e105400480100e5080c11010100e694010361040c1c0c801800d41c0c8007812410054006001802c0282d100c8a155152110341020040590401c0d2116610741e02103466106601056821510040711041000e00e0100c00040c10b011700ca01a40400580f10721559030180d09540302120400c8090180c50307115081080407843ca03c0720100148015400b80000503160b4a440040140e840341d81741c800c0050600500a00c0140e680311800e200d01039031142008810258030b80362261442c06102c07400351450041c0301d800078816400a0510720000403030f540f220f4550074041100d25441c0945e0040300c113003007511002c82c0391400820040c1e0514a0160048035036990703584036030900198074030b030384140002c0d01c491114185e950019280800c40e0320403a001810700e4100400201741d07002c14820f0510486107500060150241035000d03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 259884730 1250 259883480 259883483
    0x131b080a120807081b1e270a05010509011d060307050a021005070e06090a03290714030112050312090d020c0109051813151e0510060e0a08010f0605030106080d05030c0f07 75
    0x3a98070380845007c80007442c00403c2c5002d1200e96040d006180c0c601e000711103c0207840e0161900c41c1003180120044030503200100c0c000210750311a442c0020700d6550000034511503412940d61582e618420a002402c003c1004106c561150410061050f280e4020100c202d08000c10344105465281210010301e407004540c2c009007424590441110741c0d2000c5140c00000c02c15240504102600d9460044500c0704403150410102241400140220115106038402e99406101200d003060b0201510389400306042e201c040712a84292190314906030180180028041c1c00d00308400c06503d4280451440304200e0010ba481803810000503079081c0300000ca0b0010306401c460f044906100c40a5050001d0500f2410040030756104c440c4242d9001722402803610400c9414071040840345000000e4644c41285400300360b02602c2c0780c0c0701107900002440f810021802d00fa002007490fa10b01420715003120781079000b107902600045000d8101e140c12a08881c1c200c01c50410721035482d0003408007451140944c910 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 259885980 1250 259884730 259884787
    0xf070509090a0b040b03030a230f03090d110f120c030c0d0807170103051e01020d0207030207030c0501080403021f18030206100905131b080a120807081b 67
    0x14812850000d43c8008501c4400396010420201d00008041d602d020709009100002d04640c41958031480302c0f8420482d00301182c00f03d500302440c0191a0045400450f001e105076480501e14000c86540041e0701906050408003501c075a403c1c5050700740e12015058103410751000001180781038940700304203e40b4010788071400c0c0c0350000d1b41544000e01d808000d0b114640011302002c40380700382d105d224818030b0489071700c0741c002c182404241c1341c841c0d10140302041d00c14503554240460210001d2600080684a01c20341c003904a1600b94640b8008203c1a03400990401c80c03c81c0820000a40009003898103292444110101c80e40c04000b101c043c040500301c0c407421004280c0f08600701350300041d00e140a4079a20b4010500e540d106d5181000716402282c15411545c41103030700402190340f03090031413035841014004c03115641e00c070a03100d4680200c1b0b031421610f0914003e4651001030f4803010107a040601403806000034101440031865040e1242e002d0101d956002940035242180310841d4043c80082a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 259887230 1250 259885980 259885999
    0x1e04150807150809010b01091509030c140312070b06122d06060d240608060705121302090c030a021b0d230a050f0403140c0f0d0b0f070509 61
    0x120022042c2282c212070b1400b041c020004554006018000c1c190494010b0791440b501c64503040d00315012409170468030007440b0345030202001045581c0c0140024000b000113403000e07511484185450100c52844260700d0358418801440095011100e56410140c1111079000b8142e00c5c145040c02c00b2140d00b40001c04220003452007284c2e69000b08c04544034411101640c0541c2d0b144000c0c40304400d032242005000c1c80342110310510701105c500b40034070380300d44480b00015007685900342c091402c541550342c1d01c0400c101041281c42046044c40d9a9070090804580040400d401d07804034102d4000582690b6403000c0c04000103184091503415a090f040341c400110007040a0440d020ba1203030307014a8a100081e030b00060003013113159844900da030b060008550b603501e003d80e0201c00300d64980003c0700b00c0d1080c00b0100800008a00348242020701da0108001030500d03000b00d130041005d480d1081b0344440c050704c00d40c85102d01207402405810303484600700902c16169511083c04403820300c0f036620080d50205445 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 259888480 1250 259887230 259887239
    0x1140d0201111c0e27070306080f0109060b0a0305060c0319090f0b10030b13031809060609050405150f030c041103040c14030d032f07050105061e04150807 68
    0x804611040c3c06994485149082903407040c001700020b1a14011500818204c42222014102a280f41e00811500d00012215246c9e481c0a040c8000031715a500d07a0780d1503504080510045208404002e50229050400545555101510344500410001030f0000c080005074000d02c0d9000c000ba03d11038054010814080180341509c0e603030f1191101078407521500000110080e008903040c0003075a0300300402c151940d0b50106500060b00b5400d808404000b4880341c810400e01403200080090109008003181d03407410104000e280540c070b50f00c4070b442542082c060008003564140341821102c41900c03450385203103552021a160100200006801501c0c1c01100c0c80c604003004040c5005900c9503211208056440012002d260540791013903030300d0b8120b01d0b42e5080e098001d5000c150710700a00b4040c80c18051302000100c01c002050040034800306000103800007000002c0c410030364030076421142900920b412144455042c05200d0816004a9450301541700403229085224014030705441120000781d01c6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 259889730 1250 259888480 259888513
    0xf040f17040b07060e1e0a0f02060405120304060f0c0b060603060d15060e060d03020c010807110709050115110d1b020402032d01050906150d05092401140d020111 71
    0x3001c03481d05d80a00c108200401d050f02540c00e500001c050002d00032402203450b1102c0561807014126801074041100040381c3d207500c04860740d802c2003480619240c501d018070103891940580e03001010400c4261412000036030008040e40c2010050398015202d9131000c0104804110703d81000e0201120080c1503005032509411110a545034484040a20385402c000d101c010301c2d403e20010701582200e41100a954491500c4039885a01c0b4600141944888080d40d41031004039085580200d03118401130203a50700a6a4010140c84945011540004032403e020f4541d94180c03004070030484100d50036941d140c0d4000890840a8000700119503904000181900310b510381c9100b900e03420011051070780d42c4c1c2501c07408141200c20141440040350b50340c40400403c0344041040030086002400040489209803082034841c0519900030007461000b01c0003100e9580600c458101c034003007030000500142002071002005410305807030384104840c5071b100503503085603c1c0354140768a10440c111042d0b0320a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 259890980 1250 259889730 259889741
    0x90507031e0b0102121201030f020d080409090c05060c06010e06010e120a02010e03031801200d0c0510060f0302041d0a030504051503070f08040303150b03040b0f040f17040b0706 78
    0x10241c00702c5901d50b948170f0690146002e032001d00d11680d2041d02c01040411108140e42c1d11035072004240550140041d40c403043d4070f411603040410466a01c00a40c000c00c04407400d80c0d805808101c441c0307820200d41402450ba64a0305008041090240724041100e81c0d0080c131019110250080840446880d00b0b0078050307585690070b1090380001c40a030075030412420b0104c1120048005096941c0b1744044060042d560001c2c01031066400710010301101ca00c000d0240484c200d124001d5480708050041800c00d1480c050380c49c4011030360030780f5010003040b8001c0b8032500182141c0d8142d03404030f412080c7c081071850b51000c0c6131840440b4020020135404041c2e00c18000e0003500d00c2199105078401d0302c14009022404102c03025070220710740189003503c2a008581599101c0d119140204e00042d0200c501c40441d80d0b640d00503940c8050200034002040400300c40298800c038146444000741c41c00c0d03150083c80c0071a100016142c0e4480700d05502c0c4c64280b290455003d07084e54020310f5035550312850840c1c020702c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 259892086 1106 259890980 259891001
    0xd051215060f030712021801080c0c0a1b1508011703090f0d0606051e120a031710090207120e042d0f0f05011d04020604090507031e 58
    0x406000030040c1e0901d441c7c0d5104001810800540b51130303800352600003159014482004246030001b02d00000980105003030320b09158002d500c3d8040700083e00a00c151456508208828030340001840f4100c1d01c540d50003144100e543c4100036243c3c060780640035400100390300c0303400302031421035801d0f07262038082d044c000740b8665180005000718a07004110000300044403003048052400108196801400002915140c0303100e94000301442c1151440c8481d9051200c00b19441041c00000d1201408480c0801c564400c868180100301c1a801201840042d0101501c0f02c8182414007609074000d1003d13940905444c504040c0403d04a840c00c070002000e952640000325007095806120b035840b02e00c1c00005000d5040210f0310344031041f410b08418a040446d01400b0060711100201c1d0226400d4450000d1940c03038004044014024100c800b042e00a00c1c02c140701c140c2040ba50042040f403 = true := by decide +kernel

theorem cover : BRFrame.Cov 259712230 259892086 := by
  have h0 := BRFrame.cov_init 259712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 259712230 ≤ n) (h2 : n < 259892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
