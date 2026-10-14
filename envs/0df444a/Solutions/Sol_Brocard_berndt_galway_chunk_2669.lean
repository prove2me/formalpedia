-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2669
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:23:19.375994+00:00
-- url     : https://prove2.me/submissions/c68f0c4b-c90a-4005-89be-95018a3e79a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 479856115 ≤ n < 480035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 479857365 1250 479856115 479856119
    0x70509120604061406011e0e1c120206010819021c051b0103050c04090b0d23010e010203071b0804030f03051b011e150504050a0b100f0207120f0c060306 67
    0x14540c02135216000c00207068222520b0414006451466410000c4809400701c8000e480c4560182d60400451034004100160001c00d061040382e8007002c5101c221202e46400c640800540e00000c0c0e100d041e50002c0c0040d200c21091a0814105481c1303074401a40e2007681518911b200c00301c13a21094800f10701030f03000382c42280c15900180c0020003450b2300c002c2c1018500402c000c0340c054007505560541d5240600420801001c4001903400c1942d0040a841609a40c4411310581a5007400001141000c80248480044540c0041c00c030b000072107101c00802d4844c07a0540012108031285803003244102c10366030506869481d41004402d90500440c0803600002c1c03004e40101e82c16403e80c41c0180c0a5000388840001e842d89003c02c026901000301c2199211046007114000c420a000d000d424050000c1081c2c0c42d210b21074402420401441501a01009446228861103510b83d482e6000c0b06400803c0064500070b031a13900a50718090688000210200500000d00158408002004940d0703011400038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 479858615 1250 479857365 479857373
    0x51905011409060403140d02130b04081b0609090c0c0111070b091903050904020904021c060b190e120307030e10022103060102011103090a060b0d03080609070509120604 74
    0x1510103041c1221075404881004002075120a0440c031510041b52010386442456248401a0080c800d03280e00741c20104801040071782212000c3d004854070b0001f2641841d1000c4281402c6120400c4a543c210b20200462a5242800d045aa4004101100031031030003000d813604c50308481e62070b1500d25180c04001603000500001c48000b9070440968006809901c03c02c00072000c9a0f003210300b0040510001080e402019500d59050b0b8405040141c0103655034503203102030015010380e040c2603989180c030340360001c0f860042860590301d107401011490503100000c1481503401d00081191180c0c09000c83d441442030750414005010321502c01d488046914850724100b0201000e60142a000c640c000180c0341045803040802d010a070006002040d62610b680340102c3c050440c600d41c900404c0d50020900000b40700004604840b10b02400c0c2c1000310040941c10003854040622015000400320f00c080b4089240c00c0c03441c00e81003006802c06504d098050300c0803c00c1034140307004004c1c04e9040201000244 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 479859865 1250 479858615 479858651
    0x2070c09050c160c050d050a050d030b0109120f1a060306060f01050d0e030405030607021608030414010e04380609220608190201030c0801031e05190501 67
    0x9040100d409201a103010030912106010f0348440b0038076079544000c81800c4c0f281a440000151501400740040d00c440b80c1032450303070754121190442d01032160380c0d2162072452003841450030f240c40c165240c042c614a003901206100310b00140a90b08041d5221200c00041c61025007151303042e105c00c01c0b6554524000301010304294004003c0350084141e020b000c64aa07910900b03d50003035501800000303003018001c0c44075155001380d410294140c030904080c040581e8001645210000c0c3e240f021403601500d60b40b0341a00e03406207104800e00b0289141c0304000e158003421103a003c109000d00005442074080c2521840d03280c0b0100c550356100044051040c0300701d980020340c0c40001c800e031881c074a0204001d012a01034080d0f0412401210702c3d102c41c4003041130f9550061001011610100c03040103031205020110001c070410100c0c01f10b890b20b000d14000307031301404800e81203d402020341c0031a021104440b0240342c003412400c94550058410403048600e84401000c98140254000100800900c0d0f501e410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 479861115 1250 479859865 479859869
    0x327071203030b10051c06030b0907050a0b04050109090c0c050706091412031b0a06021207120e0c040b040902150d0b030f030a0c110d05160b040e060402090a0b04030602070c 76
    0x5008041c140d528942d80000880c1c1000c0b0746c0300343d200308000c99211038400030415900020b02408078181030140701d030b50020755982030b100100c9018422690f621200c00482c8075a21030180410b010001c20040018540d10186800c0b9aa040102c20402155642c1d401d00d803140d04040c004c03070500034061103a20060740c54144104400d559100c81e610040e040d0650b6406001d224000100b0740b501070703000d030500a01c491046694403010035900d400e240e00d210200948103c0389a00090000c41c180169403019005e1aa1261005c10103490400084000d01c40640a187c040ca60090b40f41d228420040e02d9850458150405a244540c0c440c905010307070f441550398621078a0302c0b80e4081409101c4a00001c42240d00e10304050410031108070452414150403161000040d61141929510905002000c0b642e2042081c0e4149000001e42d181c4444017002d01030f038056030216516100000e4a1404d0030781c000c00342204020101403000f50348180c0105190b00035041142c49a4002c80e940d0308000e084039403080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 479862365 1250 479861115 479861119
    0x5010203130308090613090c020606040c0e0f1c0b01090501290a030f0612050c10090303050306040914100b0103020a0c02011d03010219021c02030327071203030b 71
    0x2240200801203000c03065410b0001800c004000118010300e59280001c40e444540109a0746414a0340d41d103d02c40103005c030315004000340c014100000c1e5645081d01c20121565440d847e4440000c00c14011b000c00000caa403000c5810011000020b4030b03c3d100750003a840d50030303c02c54036400d066051100300000d0703a40603440620612120700d100c070481c01502e000030180c00201c2c0881511136403801d40441c007401c001c20704040c030b891410002044004024001200040c043c004440d0000c1d042818080a58031142103100091120300c070904c00280305000946e040f40c8001e101080c0c446c0303940c54401c803090900c0080d4040b0790180c540e510701c4034002c1c06038070034150f4242070460a200c115440a000c643c4c41d00300c000d041100c20064011848104410302e03002c0c07180600210f40720002c3c0705400468010b449079000161150501d0f1800e1207040c2c400c84038020705158083c1d411a241d07030f5a000814170321140d0351152005115985400d02c00100114001004c0c1c001c1a840c888505013805401c64550102c1c840c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 479863615 1250 479862365 479862367
    0x100302040e0a05030304030f030b0a12111f12151d071d060306030a0b0403030b130b06040504110409090c1a0307081603020c031206090c04060c021e030a0b0106020705010203 76
    0x54041a0040185c95119402d41400784140c206084c1c100c000b40182d590041c0e10050150707012650107210064110340620415104946091220400c5050100520310701242a070700464001100d110784c0c0c0d40d48108001210116200340c0c80e01c1200300c1011281c020400440c0c0c007007940c1da45405200101a04110607040c100412203101c104040c035204440081805800000f000c038249031801c11040742000d40040f1000c40a0a0a1600601400030822171a00c60300480141510300f0032a8840d0b02040e62000705540c1c9402e00d45401d11000d0109502030303030b500041c180b00c005080d07002406200051407082c5082800c26042c01c60014000100c1014400c1d01c500c148104201e10790840aa07942201f800c41c2c00a014080780780088010b44903041070400301d408007080036014202042501400340c20201c44031803480d2340300b42c40d40400307024501c641400901950a1307600076062203074591030040100440d03003040c1e2010001007450144c00d55002ca0341108440b004103e110744c103000a0020b0b0009201075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 479864865 1250 479863615 479863633
    0x20a0917030c120a0e0d0314071a01060203041202040b0406030c17240f09010e0115051521310201030e0d0e040e07050405070203070c0b030402010c0b0709090203100302040e 76
    0x1403117841c0c260304e018041c0001501c0c2109041c0107400901400ba5550a8140c2d10840d0346009001342c109603152850400c3c2c01400030a00c40c1c00032054a094880200801044034590340030407000c0c04015111a810079682c000200204450070349140227480c080e0080ac1400030907040d46480c160001c0c16282401c070f51496140c103483c6d0110541341d000a55580c0036075440d290419075a00601c4100c4884000e5880c00780c049401440034448070040721011109034003980e41d40c0e8155011131041c83c4e2078032401c14003509000d036110401c1c0c185d5a0450019201500303040c032002c9140502c034000d802210341082140c0302040031580c1c10701560350700c186ca2501401c02401007281c0a046030781001030080c8079644a030448442c20800300600390060000500601042c108500081d45a511408082d2440da0032203202140d02d1810751b084074056581a580d00b04000160b03100ca5403c040081c150508000c0516000200e24003503002441c09010018070000c2c80c0381c610320400003154860000c040c80ca420080c40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 479866115 1250 479864865 479864867
    0x10504091205071113140f0c0306060703170a060e130c061412070905010818060103110102100609022101030807121403010602010207170319020a0917030c120a 70
    0x205035101100d900700261914460310f0302c414029143d51390150052031300702c01e05160204a800035440b9115048036080b0540722094100c034024000c860804100d041040800c0c0981030920040034018028074204041d41d50000c501240307080c040d940e0a10703142d10b0790b1052003a01122480e403600003511103003510b810200d691f1102c2c032443c9207200d8030040c0700401809008040041c01202c0041c04050703107581d81460070030701c050706158041c0141070008125500140a041251902c4480d50012100514440c0c0c03865946000400803ea030365411805000004840d55683d0b0050740041c101401000d6195028168100c0385000b406117005c4c10380a01c00700400c0811100003c40359480d4000e4600c0103403a0351b840e420344a01c1074240040900850010001038aa6410f40c0500000d51007501c01000001003450800d4041c0000d8901e4008040035041c0e0b812204900d074014100d079a454100100c07440d50342c02241c00c080300040b0102d40150000104009496401d1205c1c003912542c2c085002c2c10081d510b07030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 479867365 1250 479866115 479866133
    0x9010905040b0f04051927080304031418011e050708070809090403030b040b2e020c040c0c14060403140c031204081b0f10021804022101050409 63
    0x466030340101e903101901c42070307511101010750030180043d00078841c0d0b05200b02c017070041207200901310010501e00740e204420b501d03110000d40e8070b02404403141e491102190f19190308551000d001141880300a00100b40c50680c000d0103003035030589103e800d107100800c150016280402a50340800c0141000165180458011080d100c02580001186e502c4855900d0080a00d103c0c50710710680c4160114200001c0503030541200c41031a100b80d40034032021030058244613101c80301100b0105960901040d806500c940c001400005e08100d2049950394001c81c00840c00f1941040900300c00500700d24048418009802481407070800c40302c00a00703552a1645009200103042c0ca00ca007900100082c2034803091004000f6281c50300c2244c00c0b0702510f42001c0c90910003d0f80402c807070b600d50039413490200c0e90071b060200749828000c0f4080040c02c040c0380b055600074029400b005844081c8140c0c00e06900c8a5100c51001d02041c401d005410011002441c0018a60b0174051f80982d2085040000d40000244410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 479868615 1250 479867365 479867369
    0x70501091a070501061205060a0e0a0b1302030c100e120c06030c18041107020f030a051009050741010c020609010e1315080f031608040803031f060302090109 69
    0x101c00e0545500040c900340340036103080da220030065458a17036407600b40500490024020074142c8010403043e0703081e0309a140c80d02040d000141c8021203000000e47ca450303845d40209244ca10050546080d1046040010000d0380344c118072000103044a82c0c0700400e401c2c040d081001d0101e00d24010310b034480c4240c0004149100091243c11007080c0481c106141c074180500180f04108010b00503c07440900d02e1950205402c040001da10400e841107015030349040c0480c540c002c9540201c0a80b4000200c400880058500190111414400c050000410710a4074440302d90000c11410200343e00c039603000100135214213a0800006560b000041e900c0ca581c1c0100d080b445e11541034078885d403a80e41020042e9003120303500c008550007a184240403502105d141d072182c8401c0e01008400c403081a103a44506d5524418080701c007925a008000301c0c0e400402180740e0b50030306440782c60300b07614080d1180650350035a08180c0385c801d8114007031119890703070120640829014200d40d00c1e0843c145011600020005070303841c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 479869865 1250 479868615 479868659
    0x3010807060c02030f1519090c0311191805060102060708010504051e090d1d060f161a0105030c121f240810060b070303020c240907050109 61
    0x1044902e085440034014984000580005c1d01d200c010070308500030940004848525050031240048042c1404e103105102d80719070028030000342c00d411a075845210144d20a0b81c56408440b00c41c40c417580101e40350404001d8809004180a50b00410074811305841003c0d11041c1950840c10030440025882000740e41140c0d4202d0300481d12f9102e03c1c03c003c10720b10b44200740042e48400312080200011001a00210088140da43e18141f07040c9030341401100c05403d200b1790391220081003d2591900054003420201040360300191202c400d07075554042070340300b41740420020705000004000c142350500040f07045d2501038411070701409507002656150088064031841c0300a11014109003520103501030a1112a403810140d01c854143c041c00084401030b00c50010f080c49008180120701c04035024140840d1151070303a41d4184202540c007a00690403141a02189101d0180f9500810b100040c0383e220a521410801c001350418081d05420071525810040c180072100904004009440251403a11945 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 479871115 1250 479869865 479869877
    0xa0b0901111c060f120309090b031b06090301020a09080f010209180406090b0a060e010902160308151801060201050a0905030415020708070b04051903080a03050604150f0503120301080706 82
    0x85401d20000a01c240d4008094811302d0302e03c0850340907070507501400f0150003612021a41c03a0744050f0303c020780c0c04291503030780c054208030081d410740f003c1c224980002540042c4103030304144203071000c40d08a0300200031000000d40030400c108000f00e8240328111181581e10002d5203002940004038203c44441d640e926406802c500001e810300000354400c4941590002c0d44600700d003010100030001d01940d001e0007044848000001810042500c00c0300c0f03400c80c01d03c2c002d080e00704068805a13406280103100c810305201143e1404610764440309007150b0074a03c100040e50550401100908640c0000d041d80301c0701d85414208004502c00009403000c50b6001001500c028200f044120704010282e44061100e00c80c0d43da0116030403c480010700b047c1d84080d180070102d0132001010001403c103511028160400800c038034818148a0f4000e15404030001d000410510020b41f07001403c070546900c10110904682001d02043ca014800b080c0000000b200060865062003911502d400c481e106000a1001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 479872365 1250 479871115 479871157
    0xc02060706140109020903010b0d05062a0a090f14150901200d021c0c080d060b07030e03070b1216020f16061418040c030204080f0a0b090111 62
    0x307070b41024541108020044000b075a5581800010350400c480141c425400c20803520100c2c00d10300151b50103030750028000d00f5191219110354401d070400e18000c0403500d40440701c0c07411010b070032402042c6d00e20f0aa5500c15003e413a02074142c454001e25040300410408040403070341d6075030b5201003032080413980700c3c40d1598400700d980050b81c440f0841001c903029285003050035500c28a000c81c440c4407a56154090b107041a0134003075064030081042c0c4d1110003040fa038401c0c003404621207001070465811701d01d03000540145c451103200880d402010303040b80095a900181c44650805020800090580003122401c1c120100f0300502c1c8200d000700300c4860700301d00000142d031161080051101e09441e280a84554800607541e94140d00f03440d01802010942c4134540107000542c2e44100c407001314954010b048074444007800c010150a82c098103108058080c000821684001d06c030b617202c0d000494004002412440c50814408440244a102a80d24002104440f080e04008407003d00601c0c41c144d022401c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 479873615 1250 479872365 479872373
    0x3090d081c1a040c26091b030d230415020c03030a050d0504050115260d08060103050411120124030302030a051324120605031c0c080a03150906060c020607 68
    0x400c403080401d1000045d40805103a0322070701503805005400355016541c01298a860120720401c4c40d0324042e03090f5020840c074092a900c686250701ca02c002182d01c810458104014481e1240c00a42001c03c0702c0207082c030394401082c1c041049061001080d03011354145004200d01078241c1c010001d1401c1c9075500d4400007010000203520031380c2c9a29503007613854446512000c0307982030f0641000050344509030520880b46248400580010a060582d442c076020703540741001100904809402141d030303000f20751351081d0241d0311070364248003140c2c0282c0001044409190b1074080c0e101e104907006d843c1c4540c8903050002c2903011044030039066090500c5039032001020000e0741d0301c485031340c04881c8000c0c902550501c041a89c86e00702203010305039a64810141c9207014500c0888840d8412261305500540c0c0f04017080c14040c4081035000c00303a040031442c02c4e1007500e6003a07040e80205500f90000b0340d13840c040c04d13910f10340203148005010b8603281048805d05081e0040d25100049801034812000460b00c80204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 479874865 1250 479873615 479873627
    0x503060a0f0b060708040509130b040f0510111e030c04030b100305030703020610060e0a0317071e0506091f05280b0405062e0203090d081c1a040c 64
    0x9690041c0c00b2a80c3d03134403242800364642d0414058280716500b0030f130210307684000c000340502070700d03800c80b0f901d03000c5888039038811000c0f044600b001c07a864016582480700d502818401d0503500346a404a640d602c0e9503001c2d0302400c881000f000411404401c0c000d1100c01da4010042d101681e41c480c0c856103007522071000c03450f0b44141c0f0341e00050941c440060034008165010505c2c500900d48805080e101548500040d1501c0d8200d512094000c0011002040811001445162400401d004d064601b09064543c1084110803004480d0503540b182070040802104001059001240d0341c05410b407684624840f030070016504001c0041540c484010806c24003c2800028a1060304040090440031050200c40601282141c5a128600d801c00040250820b41100360040c108844010700c2880d0b2030b00d40424401030420624114882801300f80082e440300e004080c0000d000e004042d81307422902c01d0200301d03e4584d45101c0702540c02c0103604081985c294400c2003040404440124040581c01422120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 479876115 1250 479874865 479874881
    0x8040b10080604080a0216060c060c050409090b1501081614040f062705010918090204020c1005070302120c0a120f09051506010f180e0708090f070503060a0f 69
    0x241c2c00303000240410424920002c01c0210180c0e0240c4401c0c0f00041c0f2880e01c040c080d8482c03c4042403841c0d00c41400201c540c1c0c0540c4217a011402c1c51420039898204c201c0440301d682c44222904030b541400e00c0000360b03c42c0140c0c11160000d18080c0624078000243d41a500900740d450710038046070403032180e1410b01c01300a45000d030080c0e9036415400756a0700c0004010b010300c40800200f5400300400780082407001030750300d000d980c8103071030b000051440c1c030308507204008421403202e07038143d07880315584010398440c0001d15440b00d0a07401001c04011034100441140e41c080e12134424907104001c1e5072000700030003a14940c40307442c41d60381503120b03442d421060301d500100c141ca9101080c03610805000c480380c03503488910064040d50480d0003110341241c249003614002c0d14034502003503e0702c0030540028482d9443c1240c2100b0506041e00d04c990b95100c0c4104c40701c096400d4404642d1b54010044151000c000440d0410350400042c900740b464600405e40721103000c2d04c0c0c81d4400f91103000440740310020383c01c4880 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 479877365 1250 479876115 479876129
    0x1020010f1103010918170a020f0f0303041209120201030b0f030105070201200304080d02070206070606030c1703071a0924070206090d0906030b0d060903120b0109030308040b10 77
    0x1610418814003980b507000f4040c00001602e0008080d030590401c10b00f2001059110032440c030030441203240e0132459001000300404510407444c50081120f000e1103281e00041507080250b4403401c0500e0300424030143c1c2d8459104215002c0d2003044032400c1c004204006980a007800034203101c005000c01c641030000c800e040c1d0107600307180034088119030550281c44a0150400d4001c8503014494030750945110949002d010240c0c140002d005005072980101511071000702494a040a07030355649040da05c085e803095070074442841d420000888040e510440480301300016620b04501c5561714030919110650343e6281980c4d400001e542a00f04110781405910800b004031110008d52050741a185002ca800c400140581408249038542c00544407a003140c1d6034555481daa42001812001050980b01482d8802c0714201c5280106025200d032003840c5020717030340d2400b1042d40e243c1020b096404d058100d83c101301c00210300f000400c1e8040c0250307412540c401c20030311307060b00c4030481440b28a00c6600819 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 479878615 1250 479877365 479877371
    0xd0602090d110103050601030e25030212030301051c0818010e03191e030c1b09020d0b01090602030c190c0308030c0705070f060909021e0a110c1020010f 67
    0x1405102c0e4000b5400101c14090b6018450f03507454000440a9407003142154615a1004c035a809074000c640d00d074000c0580d0503601c3e64040c5543c9800282c880f100b0151180c81e160400030062102e0b042841840f54040d552008280204401d6500d1202910450560101041901d4040741a6078498201c00c0011400102140d60025241c200d10b0546460b1a9003203c8101104111112045041e01c00394501501512180e903104d449440358525030305103c9400151400b08540030840c0c10692020303101412200d200081c481066000240c009a0582c001c0419540305011244c2d905600240c5010442d2400d022111055641e2030101089046508000d00303c02001c0708000403100e00b20041c00c0042c1c02003044510b0701e030380c0c3e0f101072404940a0041c0740004036499000d002c0d4400c5038000700003414245010328040120040000c20756040b140035280010303c0c003807000818500400000c900340c01c0031118076280b6181c0c004080c0a564040054254a1036000380e0700e41004400c0d400404002d81d40203041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 479879865 1250 479878615 479878639
    0x30a0f150b0a0806040b0303030609220605041b080613050c0a030b0609010b071109040213050c0309010c080c16020d06050c091002010b0d11040b0607060f0c0c110d060209 75
    0x703140e1581041030304000080001c2d000842900c0d10740948a41d40002078041d41c9581c803140e09111410800805a071002804011a141d62030307803101165900034019000003680e8201450019102d58032a054412049c458503820b100581c00414041d0700400b41480803140d801031498040d092a00e400701407940015650400400d11600400040c800d0784100c0391001e03d6a00c9801c0392005004142c00501010002407103034080c3d080c00e54016802c90300007004440201d02681d210015510211008081aa00441446406882401090368485007400d1036482c0d80b6000348401c446008040800b000d80c5041c03402c0700155250085000000c5410200c00d100514068404202c250312441031140600320a1490080e203c0c4184140380078003c0c000c240f20000c2500d41c1702e079440140d240043c15441591008100c01c240d6a09006202d0b00344070b4203020440e86101e482000468040b6820141400141c5400c02c001514032006814a06012100c407404400340b4200000240610441d4580141c0c586e402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 479881115 1250 479879865 479879879
    0x611070e070e033a0206070e040902040c030b0f0607110d0303061502030a0e0109320d110301050604050106090b0307090f060e03010507020106180207050f120403170f030a0f15 77
    0x40c200d1540041c022801409104250136002101c80070b4010f005070414008949007910071200344074000c000610110f440341c40b6070006030440d841e554088003c01e580d00d40c000d000e404c11642c080002c0c40210345041c105091600d03100302c55003980741d0142c8600003041d500b00401d4080c0c5c0c89000a002040070a051506039658040d58940c480d80d0f042c4082550190308080382e612a004200a40702c3c1c10000100c1028031000100c0c524001100158892200c10094a2981c0314404800d074280d01030040071803284842c40505003154005030105015070b04141c014044503070001001400c071184030790010343c0d0340d588000c100d8104800d900940a00090b131000064942e40c031403504805810114001c00c100c0e111484168202e480512460010300382a18410101c2c1301c0c0e81e4080c00840303014001f503c0740c0031405150036003400100010180754610100d030a2081c040c1c0085401c01c1c0240380380c0030600c1c0a184586424660100a052080407a298460368944032981c1d042501c142000e180001503a641300e401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 479882365 1250 479881115 479881153
    0x1080325050708061b1e0a020708120901031406030a030c030c0c031505090d140a140a0503090601120206121806090106060e0d0c0b21100603060611070e070e03 70
    0x40c44004030400043c0344031700914072170304407680b2030840c114800c07040c44070702900040c94001c405818203600644000082e420b405002d05c4801e640c01419096071030307009000141c121a811144101d0108400c810414540c4000031001482074040c10300c8000756020746812130b0343c19107008004100340c006d00b80000c200141c503010b1100f012561001030041d503450b1031500380c1d60103003a5140c00024603680b03401781000003100020b0626698520701018030765603207001c090255001d561000e001031000410445c08590502205014202c6055502c00508550300003c03010300540d901c3c1428400700401040c51441090041c900e1600304000f44c41c0c1614004000074000d0040d44641000710f82ca0940d407003200d20f00340d23215030740c11544910170048407030a08000c200c09800041d0a0205d00f9128101c402444000c00000c1d840380409603c1e1007405410000c00400303881a650014061000801d00c810241801040c060309803010500c9907079036035840c104c0459003c00703101d40301501030281740762046003241a00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 479883615 1250 479882365 479882371
    0x71509020613091413050d080907230a080a0b190f0903020d0801090c090e0406021b0c13060506031902040b1308010c0e01020601150e100210050f0108032505070806 72
    0x35803040c6075860320400e202241003200006c14035001417032599062801070300c256030000404401c0320103160b2241c50203008480706560500d1005041e500302085032920710400b501900e054406060b07600c04903600e1007424035000e8040786140c00303848006400c211a942c1b1041c0c440044d1070701800801d1b06418040e4a0301e003910b12503800590b0400c004205245580102d03056030846a07159029540b07802e401e50000e450141c01100d606408005d58000d61400c050102d58211610000d054030101a408100604c1036003040c0b423801c581003000030002076a403001602e9103d10f07181c82030441c10804d00c4014000f4442c1da00140d0300c01d007006c04d9000c20001e15010313845c00c4e1000c0500800c21486074010541c0c92141c0c000c0c0d40b038016402880180803111b2110348265044e00d0034280b410992444400003852400320784814030050303100881d0788866409502074503400c014103851103002035051a03101600e034440c041c400c60b408820b100c24101200548030a1040b6a81c1110582b040d6645980405840360f40035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 479884865 1250 479883615 479883641
    0x5010b100e040f05100b07020406080f0d03061505030c09030f100212010b1801050d0e03070305120f060109270501030809130c081519030809100507150902061309 71
    0x1114002c3c180070160711602d40205405038103c1441c1d0b1400000ca0580c2e40001c104980258a880300000c0820080010074482003100d40908034005104000030129002035000800d1262054911f82503203400c14102c0380c2001c034000c0380300c1da5405240086850708079a0001c50110780704115030101d4600380399014003095940e510b40b915aa03662007495032158016140f040c114000d14021203155980070700c0041416031098000810110b40054040b41149c201101c280d000c136100058007001180000c49840e03101c044003503207203454204040000c003540c0031405162600c0320000032040300410f00035146440340155030014031881d0f0310382c5003410180d007000b10701c20701500b0703540d0040360710003910b0080841e407403e01d5940d50442d81c0c0760a8040b06800c00240007a0b001210700e40c000c9525a10036090784003550040c4a0543c0d01c0c1254410b02002001c0d40381620200082400000c1c009041c0e100c036501404003000d004544c0ca04680001010ba201d4403510280588001c0c4001480b240c10742c0000d4460120 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 479886115 1250 479884865 479884871
    0x10b071407090506180c030c03060d0606060f091205060c0a200f0706020706140906070204050a09031103040b0d0b03031b060403020c06030112020d060b040e071401030e1905010b100e04 81
    0x1850400d41740c191001d40310642940f00500c0065046c901c130b807004c1e6621140c0140300c4c1c118603410780c40c2c400c215a0240c002c0e5000409207009100d001e40c103d00c4c8000107240c40d5131241e22040030740c0c40f1f03140c0341c0ba000351028a0748a00064059030307680c841c0c0c80032003500c0748100c4035502041107450303425aa4030803201d224000340030700100020564008550b05088039081c0d2501500406038418a4103290b10080c00107034803407024401d100160311188505031242008110019411805007406811000400c44040c20b0b03900400040c010900c00005466072000800400324030800c2482c0041d0460062071b40702c40405a1000c0601c00c038050014400e409a80640c080c3d5000e40100d0050146500c000d010b14243c140840c0c14138401412315040d0300380c085000e4200012030341940030000d41074521030780021095a101010600c08402c414901c503160b118242410004409818151500e410050f05001c100c901218081001d0000a41183e240080000d000181c5240488400350038585054003103800717146 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 479887365 1250 479886115 479886139
    0x301060807060207090902011205010b03040b150d030302070507051f0807050f0711130e010b010e030105040c0302011103070b01030605011809020f0d060902100f0f0203030f010b071407090506 84
    0x8404034520040d01d4443c3e01412906013014035110150015120403810050040801c00c1c40c80d040b4400e0381d010f0b1003415403142c0c2c0d908060a100f0410103000e40a52030720341e070310301110301e2613070310094160340080d0705040268807446182805408c0240c60780c4010707000107160300c00d0800801c02e50507001c030000c1c15031500b01c1aa2204507040300c8034001c410703203071103058002c010070004034000d2200d003556000e0042000085040b084080703010b460700c0d503a081009a45400b41d04055681064135800042d8055000304018505500c0d0a4144001880040d0521000240d00d104244040c0126422140c014011304040e5a603803030300f44003c0200344141d5402c5644030a080181e200709002d00c1d51544d03001004912041c10175401c010681c0c50120040f6035035540c42d8080e03c0140c03248400105243d10907207804015020081c0c01130101840010084119001002000002c80500b003115055034601e00c0d1081c0c82c1c000394034000c0018500c20150b44007900c19000b001440318000d4024902c601c8054400c048520307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 479888615 1250 479887365 479887379
    0x10815180432070504050c090a0b040801060b130b161e1a040302100b12070306021201120503070312110d27030e0402030402061303080d14010b090103050702010b040e0309030106 78
    0x10b220115040c4030381000804220f1860030340c0240d84c1101113024518503003500e0f11700155421600350321008103820013007420840c04a081c03040400610001030220318240ba200f410141280032030149524052020580c030050030ba1182024000b9640a03902c4580400d8070124200c1c40000303c0c40450340d00741016402401b03003500100c01406140e1540042c8004032469141c0c00141a54030b0099410040170000c21070049400c0052034001d40c000c0d0f8006a58404e080b010141070301058101d240c0929007488850005540001102e03c035a801d49001c030000340e606040f210142440e0395146001090129000c40744013917640c05009010303410b03440311003900b0303814801846001d28080e0143c0416000d0540780c00506040d00110343c410f02c0101124a84801019070b80d0400c0559002600c00c2100814054002d0100388100601c0c541d00e101c06d01c001d0741c507000700d6204a1040402940c1055168030104d00f409000350000113513400d0003003003801405032484c3e0455807074000c450003910a60a007a0b0010f019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 479889865 1250 479888615 479888693
    0xb09030d050a0813050f0a030507110a030c09020d0b040f05090d1e08040503040503010207080c010b18041e02062d0313020d0302070801050f071d0108151804 69
    0x82c069a46a4800030360360055519000151240e0680d094010080c1491455400344001004035100f500ca05480e44d83d2800d000742c42c00700c0d0800d064043d030303040c0000b840400c131005200e00880703044200140c1e03109043c400003005000b4032044982c01c1420028590380c1003001d60001441400c245046400c03416440f9000c030b03454052507030000c3c00e28014a52b1280d1891003070702e00c250b000c0d00400131240380c41d503604040703402caa0001e04103444940d00451040c010035800e0240c8107034042c0403204104c401003841c240c40d03004071020748001e0603080001e20350700e480c0107407016060142d90020206500d0306100d012a80c0141c880d00e064103454002c40074042d2040b24508150b034010380050700c141481881590900c4000d806c10b4500b9020361040340c100040403902401340c503100300700007110b60b405410301c580c0150410a865403290030b604074820410740e559071f100f03604550180710b01c03006200000d0311101181c20340380d1030214051844001c10810041c00020142f10481800807584400054003c00500040d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 479891115 1250 479889865 479889877
    0x30c040b0123090d030c23032a10061a031e04021c0c030c2c0a020f04030602461e0810211511040b09030d05 48
    0x4603000100802c2100751100704030408108500010f8a42010580014900c5104c00002c4001031485c42403441001908409014594000c0130740c070b4503004400511585038050304e40c40b4400818207600f03401c3c00580c2142c18481c418500c0c0240c64000405842400113482c0d00d0003040703070000868043d8440c0002510441c0c0c440c501505241c030702c2d044010300c2c60070174102c0503000b643d014030a807111660350030800000c0005e1502c951503d4199628610f4842e0b03019443da403080c0343da41c6d80001140d444500d08a000c4180105014602c8000da991038031043c02402001d20302c1c1c4955a010601008010055005084441c41d4000000c4c0041022000f01d2505c1e02c1011103c60000c454419090000c076141c5280d0b507299003034145200c0160101400440440e524845c2d2000211440c0034880145440c2c0ca920019212011340d01d00390068510401200c0e00c00c2c608020a0103082004508061603158000e002c100160884155143e60394540d251f16900904200da11070301910203143c601e580200c080b222 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 479892365 1250 479891115 479891117
    0x806070207032d021906030506041e0905030f0a031d010608030f0d06050607030201050f07050c0d21020415090b03010317070507182405300a11030c040b01 68
    0x500a080c03071407250b100c503c52030182c0036454410204100103035202009800a2040c1400703280d101442c20700c0040070384802074812800380340340c028030103100f803012681e00d101115004408944d01c08a40303011861f40c800d041c1441000c02000c01e004003113903410b8000c6032000013804c5a0425005001484070700b0ed0300b81e8403072000e507075104002500c1120303403800140045000080300003d40c0c80e9186c0109603103900c6280d0480c0140d42d42e000b000034100b00c107203d00350060b040d032402d0b9040c00d20314040180d64098078408802800020843d0100700342006032103022000803441d0564955030303107001e4016a0701201200d0408120b62070070108082c40c054040e00d04070707034106c100c01108800540080d54160300c0701c00d0070754880c000d240d0049900024401403811001e00c1450009101e10304038102214135030310020152600c031200b41c04000e10b52380c20109096042a6244070126140c0c11040400d12501e03060801b01c1d80c0c0280703032a038814042c0400c0040400748040c2e060720300d80d6001d0f00c204000c5819202c0340f68 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 479893615 1250 479892365 479892383
    0x9021e061207050408010f05010e07090f140d02180f0906250c060603030f0914030606040c1e05030103020a0605030f04080c12030f060f030d0813030e10020601080607020703 76
    0x4240362403854001904070b8000c0c10514602900c07010800d0a5805204040b61450b4039000104403054a1030300c0e90390f00c6282441d0092001d801c00072910045280d0b80300d009400708071994820656901c440e484001154020105403200c0300c9600041c403016412111122070b40807440000b001041c1c0840c80d144a0050031078410520000000c084000340c440840c07010401c21921154000039000d4403800c1c0146000e40c54051200744071402c0180018000d8003d13420300d820491640d842c2d610b0025203d50058002c45002c140b1840c90007040300c5040c0000c8910514500f202c0c5000c00c01307038100700154183d81c0243c2c1c0c0240340b580c81c1c84c0162010b100580d0f81c403a105880c04002400b2500e0300c000740005047e140141d81c5104411142c1240a800940320a200342d1809410b00081c2d192214404c030078030b4419030140010030610803001e07040c0c0348014800b0104410780b420003c2054030071701c0802c0743c0080040190b4861420441c00035981d80e000d0090203082d110358008684003500010300c040031240d10900071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 479894865 1250 479893615 479893627
    0x240501090914031c110904020a0306090605040b0105030a050c160804060e010309050a0335011d090d03020309031312020306010504110a21050115020c0103051509090a050d0309021e06 80
    0x210000d15480c005c002c980c06042c8907150a80d503560001f4410000d00c0c0d034010910b03604180d02c100031910079074881c41c82241f070f00b41c0000c0d40343d82013010351b51300c951003203000a40d40c1c0e40e00c1c144010602c104200510f80210102209080108540245c016a49540c1d18650310b40c880310010b40860316580005412a404080c035040000e1180c100d9603103145820740c050800400c800030444030316200392913510030440b2020052080d40c0e208100012064034072142d100c80e504051002d030381c40310b0188080e041050340000001d28490070810031034881201c03850410003056650307a04c4c90b501a8100c00224842d000d19000050245814010740502c0002c604699107416410b960544030300e580002a001d28444d0040444001d000303510645000300400d061400f80b109051030000d0400c102c03e5a0070b418140340c5024491004104d039002d10b007591040e01d0f1203031030b0b480b0525020300d04036010000400522070030403143c0c030043e41600949107603072081e10710350641c081020189541d0b0f1a41444103070444818801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 479896115 1250 479894865 479894917
    0x603021518030105070c051c0e011808030d0c200601180f050103050c0321030a240306060503010609110306010c0201110d0302070b090105060a0324050109091403 71
    0x1407101c840303001184490a00c01c100420b082d01c3d812500c60b030104441c1c1c1c0c0c105c0f0a022044c0407041d020114070b20002c80002841a001d41305200b10f141c420304211a4800c0d1021312040d520304800600304040c00c07030707131035256446504001e058007610100c0010480c2080303024004400d90200c0d0a9007105019009a81c03e0100300000c00e1410001c2030300c40c0341c42d6500081481701e140716290283d8000c1000d000c7c50040842414070f041c84400c0301d200c0c0e40460307440c03180364a2a030b882500d41110303030307c42d000c100780042490000c01d0b24440b81c4025030b44800e1039400420030143d98449012500c0c168000d000c410b503620348100c111040c00703030511503e583c10070001da40c540c0314203a05143c4d0362050400703500e03401c803c80316203240c200c20584110120341d00184000901804580b10342e80007415038003d100f0751034084c02050400c3e4061100402d00c04030312801b0b400112120103c00006440040100100d40c2d42d0440240540b220040036260021145040110309201008503030f003460340411001c84400740d11388 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 479897365 1250 479896115 479896117
    0x807061d01020706180e0f0103170a0e0d020a0915081b010e120a080a02030703180b0724020c0307060f05040b010b0d061706060a080613060b030a0218010f0906030215 73
    0x1184070010405c80b44003044500701409580c2c02600443c1c5041007a41c1145000c50b074980703c00d4802c80103000c060090044141e404442c80003281d100342c0c0c07020703070100d11440418800c220790b80020300260708060b081500800e000305030a0884004808560b03140c1420340c8450300c0302d4290380c0c05c01d0000751002805130703003401c01660140d008a000400c688850702e0541301c0031620b4121850380001a0000650b200078540e0006606d004e144088485014680ca0503203205c00500c00c20a00408608100403122500b00039000300c22006004240199650317101140710940b40ea0040908559080c03411202040070a0148240b81c07140d9800300d80406664200100305645410418040450b1910340ca000305101c1c002e580345030001c1c1031800041401c0d09281c0c08000e41210030341c1108503564064001c004002c10885000c004154210310300084640300100801c1c20302a1108020f034014102000d4003912040000520703040302c0704c4c8030b0444582c98a55460303201380d40c003512000c2e503c065107108401071049040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 479898615 1250 479897365 479897387
    0x70e012304061d0402120a050903090f01031a03120702042306191d0406200313050703020a06020f0d020a0f022704080405100c0f0b0c040f0807061d01020706 69
    0x5000d500c100aa680010241d1b8408080c0484405014080c00103000c44d5006142e0488008801f03542806102d8000c40d508280d440d0341541059201c082d00328002c45803000c46c20003041c0140540d44400f1643c0d249080a07440107004034000c51400b410558032101041070020000d29542441c0841d49880d4104007a80c04103c402680d020005c000000b41c0b0010314600300c904125030300c0201c44500c1c16042080846d400518a00d44080900700400100070100d000c4a901c41155100e0000760a01420203a241010701c3e0802500b0040004011400c0c81c0c00060070f00c500400c00017202e070041b4a40c4004c90300c405000d90700405080b061030884006190003400a20000c061400d1030010701461a540904035500b558140c0d4001c0000409100f941800401c0e4030156245091040464000d0b980f000c4110304044409424001d982c0045507004076920200c80050180b100704a00d03036511401c1041e103400407803090b84007046000391158640c4520052101c46044c050700502240e92402c0c034241e071010008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 479899865 1250 479898615 479898647
    0x16062607050f0d050115030c0c020102070501271707080d050306010c0305090409060903020c040b0618010c150b09150607030e0402041203080402150c0a111503070e01230406 76
    0x10310031520f0000380d1388039081c024601480006c03c120300c400c2e03029003200c505000c008100005454214050303600001d0b40d1045030b20a1a091102c5604100a401e40a41c07809000300440e43e4260009403090030705400e6001c0944441c162061507559560443c0d6400300b02c076034200070520601c00507020f580562401c2d01c569029080140c64002094000340485140d00e01c1296040da590b010700d010f055040007541e0314403400703540401000e0311031f00000700c06004a08002ca0a0702c0202d40000840c0d105c5d001c02003520354010619a0101e83d80c0d48010003030555062018002c0000c42c0003c1c060390114010458070b4200505040d00e00443c40e201142c0340c03085400050740041c4c0800c030005002917007460030700343e86000366200b524a040500c10850f03035024950384c250303668406100c0d800c1c007040c02080381d4000070b5100f1041d03490800d0305408610b8860110b00500000309011041100c00f5030403c0c0d00c0101d40109076101c0c012601d42200702403076005052580b4a50724000e010038030400d401650448241034072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 479901115 1250 479899865 479899867
    0x40f0b130f240311090d0501060819060b060702090a09260c160503030f03100f03080a020f3405060f04050a0909080a1b020316062607050f 61
    0x40d141448140348041d403140c00000c1c02c070500601030800341120001050801e15003408803c59003070710003549000318500700344509030038280340d02003100c25030211000f0b12001007030b1103c0d000c40110800d00e0404080041d1212802c0000d00183ca04d40b08003100c11659000f05074040036221012410014000c3c14030031510904224005811101c80690300c205081c5440c0c14103580b01d450541d040c1c20005203038075851203a041e40320140a0343d038011058841c1001021380d03050b00e07540c0b000d54040f1040045e078003100b03003264103950110500c4000b0005001d400c04a400325001d06400607410f59032002e4103624480300f4500c4206801c2018803050740300c560380c02c106904582c015183c80000e40554007403001c1518401d40020200404d0606a03020001058119030402100141d43c480074101e100e01001101003045c0301c83d0218000600c0450340400a0b0040c00b00c50800d4040554034215890780c2c003411011a035405544142d812200c072003604182d0000c0d550200c0341d110b240099400340c02c41c02c18001440b034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 479902365 1250 479901115 479901119
    0xb012d110d0c030f0206040201021f15230307080706230c03040608010e070c06180b0a050114091b0906040b07050a06052a0a020a0b090a02010807030603030215040602040b07030305150303040f0b13 86
    0x951000c540908013781c503c00d49004034400da03d00010306050414025003001404000200001c110081140c0079410042c0ca41000120048140400c841082d62000030100b0030281078500040a40b00365a00303903c4140d40da03600c031042c03601d00d028111556000141040b80300c030000340a80c0c1242082e20302c81d01c9032010070501135031840d8181c0b13021180303c2d0450b81d070380c4010400c0440755880d03080200004c1c0d840e90400d04117a441005441c0010841400312000024005a6602d80c0d0044030000e000000d070071a20384c007441c6009500d52038030720002c0d54481e0904000c078412000c01c1c041143c1d2506099038800050b4407103000d410442d003103c03482e0380560103203541d070402250803115020b02c5580c101c800750950700010f10000d0280003014100508040c81c1003800c0c00001d0b0002811028490294894903150b900c4c2d28249001e4030541e040070b007140c4404030300c4004140d0150009800f03442c0b90350128140080078028142d07240a44c3c8101d400c0380c1d6000d1010044c214250004189803086030440e154481d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 479903615 1250 479902365 479902391
    0x903030a240311041a01080f06030a0804080105040b1005030d112d06130305030a0e0a350909060d1401150501030b012d110d0c030f0206040201021f 65
    0x120150701c16100c0380350020300780c0403d04d0300e8451002c0c221104941e0102c00d0140c000000d018810051024181c640c148010507a1594104441120340e1360048409540310380301c01d81203000e440c054400700c070b2a080c080080f440072806132300c6942c2a0b036400745c01885403614030307802205d01740c54602c032142c12805000480c7d80541e020400c00c000307504000002680a690107000145030240042c200c0382c03603018071840180002d500004407500020380c8080410701d1103004142c1d5007480c0000360000c00842c5892600441498000080c0d5050380d074510304654a103c601010000c3d03807150600082d03004880900061907403512100c0c403d542ca014000001c90400c010745180c1c01c441020008588155460030200943d40c0e050040450000003840c1c15800146000c2c1c0101221054880504039080c64642c0c0030040e40c45074080818460703615089440d20084480090b084400d00b92058001810407403081103001c4c0000f81c0507004541c103a00808001c25502204100620800b4210001c075450b100b09003104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 479904865 1250 479903615 479903681
    0xb03060d0c120606050a060507080702220c110d0c0807080a0c060f020301090507030b09040803150a031103120703082d0a0b0a0f03020123041a031e0903030a 69
    0xc510800700000c5a50030310301042201b4402e41d201608001080081e5030000d00d421064500403603064407090f030380c0d8100310315440342c0c140a120000046031030300103100312060b03020301103100c0e42d9001e5041e0764080b00403c1c0e08507118901f040c4040c1c172558003000150002024840101402d00e01868404401100d6689100a580c0103030070360320042d500800103221349201c81c81002d800890a00f0100080d008140100c4c8881c40000d1015094003008400610100d1113003078903d41500e070091013184038540300e1903d903100c01c43d400b612601038803c05205400220a00303007194541134268842000300d80e29a13014415150503440461001c8811001031034a0001d5007080c40c0c0503065062001c5188030980301840825040c4d58028004460388040820140c2d0700b21000314410004480e500c1c1e1440403080f16500c1c14415039000c0c280d01800302000e0700a205101000d5405111181800c200c000704d070301400089000e0a41d881810342d04100702044110a030765014108400c0000320b040110b2404c85024601 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 479906115 1250 479904865 479904899
    0x301090c0807060f030b130c05091c15022104020a120501050603330a020f070b1f05010f1b0c06020d0207050d2d1e0218010b03060d0c 59
    0x210342c01a0010300c4416001503584040c88002d01d001c00c44d040320f0000080d081c016031020b0903010fa80c1d5150070b2100b94407840807165160b0018200b0500000c4003220318040120f08001515403100d02507221480f8089402158541c81459885017040d074001d5070140c1048001520407a80652a603000045600d22860304629050142000103180d01d007400500d0f080680880c00b044100d2028807443d020030f81d07015070900c19112850010440d5540b1106100000c2c440c04080c080c0d50040425104c0c10007055410141c82514080c80380148c001144000644031030040c001e0502180d801c8032102a20b1b0300ca090381c2200300d038001c460342800102d140c440201205081d0070440c010782280800d201080d404109034001000103607800d6103404519102c40703682c50700c10b002d000c1114a0411640104004030031484c40641e4020024088608500900304000f201c900d03c124012009002020103100100111504880002c42c03c07605d140d44641c00c2004e0291012000c9403543c0c01d0030004a00b010101906940d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 479907365 1250 479906115 479906129
    0x23070206040e0727051009030804170a05120a090f0e0a240e1602060c030a0e0307140a0311190b07030e152a0409020a0c0b040c090506120a08090301090c 67
    0x100142001d003880b0318241b601e0061010303c20032182c1040003442901c01c5404903003000c1c07140740d141d0b410104058200048888040c0c001d02c144001490070386440d0008200301c40542c1c03140490b56698006500c1686828892450380304140c00c0000c4600407507802000d1803600300e22034540d03030f2003004080d141051220b800041000043c03c00f040481e010020610260b03c1032800100050f240107800000c092000070310802c001c40e1600320f00801d10a041091312051a1301c02013044804442c262115900c0b110310800f0750020304000d08030041501c0200300d1000d242c42d036a90420b8000c02a480d0381e80c0c039810180c13148007016542c2a40701c0f03c003d02403204000c5207418001000c4503041c403080b00228407900c144100c840d52441803025421058002c1100c00700c0700940405602c07450602c1082d03078018001c41014004040b5402040b0401c046240e400e42035403c2c0d450f00704001c0d01da800c00d00c40300464002883c03c1650000c80400d003c41d084001404103458024000304400d01c46548902e401030003544007035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 479908615 1250 479907365 479907437
    0x1501030b0a03061a010206070c052a060f0c0c0609030a1112030a09030b1006080103030c0f080a030e07090b0a030318080f060f0a14070c0611030723070206040e07 71
    0x4600c5e61381480000c2c0c1042091500002c81c00e4551141d0380c0317884240c0c41c8110301d5a200c074042d11114050000f010300000e40205819101d48003851440c000380d001c41600181c500818148205500d031041c15a038102202500403c403143c400d5403a11100044004070b158001c0403480c0c5121400d40400c010101c1c0307000d13030351241441c42c03840c50315080307054020304010b50100b80840103200180c2d002c40e100d41100c0e00351602c004506100e082c000d009d0b091150740503040c10000210a24002d400d500311904a409201c00c82c1c40c010340c0c031401c0c2d200702c0700000d060961191710440d0402c0030a00c1200743d80708606140c0c5604041a035101030491a01c10700010100854110800f0020520380790110b4580c095030224041c40614110200c940046100508480c01d1003008402c4109120159012030741b1440443c4c0c205a0700c0c20002c1011b803180d0200b030700d2040001c094415201c032800042c0c0503122402d070b020b401b40b800c203401c00b0a100611035008090707004103e40700d801030301029160940390003070040d499110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 479909865 1250 479908615 479908661
    0xe01030b150a030c090e060a231b030103030c140d0914180106030915020403023f0726211c06182306030a08120a141501030b0a0306 58
    0x180e040001c010712100c2c2a62404407146100070320400443c150b5107002e603270340b00d29645144a108135002508013400c2407020100000c4105504031444981d001d0045880703030140d0030302c000d0450761000c10602020004141020400251400c041101d505020007032003190043c018010070002d0071400da00981c006916410030000384021083c4500181001d10010741c640750564010071310701d1400322140c1803040c181c0204140d142580320a1104400700102d8203003c00034a8515031707a90b55105005000070100c6c00e4042c0c14541c54040e542c2d07480c007074040001d002c1d03102c501400790801e02e4800901c06a10340081082c880382c0860301040f240c2d405508040040c0c400d0500c0c40c040c011403070b040c0174050864549070b440501230f02c001005280ca401c105ca40000c1c0c0e0382c0d426006c05c0c1451a0110300401014010070303821000040c0b145440e2080701c140d482003100c1070b04040d141e56248425a44044008241c1608990381d500c40d8015a00169020b41664031b4281d407543c4c0d4404072402e209410394140d024400c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 479911115 1250 479909865 479909891
    0x717060610090605040302090a1103040f1110090509041a07050403050c010507081b03091206060f0d020a0308070c27050603011a0904020f060318070e01030b150a030c09 74
    0x40d06980c1c01241c50054034250030880041c0c0300f4440c500001c1e115003591400900388140d650001c2c3d00320450a0103050b140e00341458040c0e1140300700031048864114080440856061044008038000c070542e0b1490700d03151528061000d4807002070002e80e143c8941c80c20300020f110386442c07151300890081d61055030329455814658104483d90140a04104c2c3c20081c0c040446c0402040c5c0d0032004041e009580380b130841d100500e00d5482041c40d031070340014a48106404071040807403098414174060301d41040e0302203c00200030000d120044004c0d071006841105001140e41000078006543c070540c68a8596a100d05008020303480b800e8145880398030300b10741064108918003800350007030402d4000f400400d0720030310640c520740f51171506d00d800388501c040000c05541d10605150464040944815a24100f01501114244001200d5229441015000203142032025030b01c03412203811001c0c202e801e48407804009600100c4140d043d40c0302610b050003001043c60001c800c401001f030741100103680707507610340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 479912365 1250 479911115 479911129
    0x506010807090c1e021005100513050702030406110309041b0210060e06220c030501051c02010f0c031718010609090203070b0306130501030501020d050a0c091707170606 74
    0x21090303000d0f0820115020303190b0480c0d103615a207001411401c990b6554450101e1410342c000078444040c5080c0024000a500c03868100300c25540155515000001c43c0380c09041034501c00d40381c01005038020002004040d10985020b01ca500f01001aa46040c030260001400c0c0d9160081d0081442140c034100054260100038480c00c4189440d810f22060303140034090080d070640205400c1c0684900030107086c18802c60060400079114250f0b040008601604000b0006c0009020303071800b8064a20f0b40340e1724082100700c8030071200e60594070001c02d441100004c03a034421400d641101440354242040c071441d030040c100035201d501701258045c0060113008020742074030419400026141c0c509014900580c4001c2001c00c00c2d1952808526541c3c1c0700d001c0460300d0403440c40d01500e04503203098000f20070000103400070418108106424021600e8162040f004c44481ca185000458502d40b0300300b1202c00d102039800341e4041c4540c07e440d10290359003c0ea0310321030460600d810550300701d0420482e444c0b411075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 479913615 1250 479912365 479912369
    0x40b030606100807120501170d090b0d020f04030803090a030915020a06020c030c070b0c010b0108012d08010207031806230c160303020a02040b2b020301090507030506010807 76
    0x50080545081c408003094480c0c0c0403018032010401e00c200040d051038001c6064a80180d100c500030811580d440d07402d60419044e400d921aa41d0140c031031044891032141d01ca05007544c42940c5141d181c1842c2d101d007a0005d500268070740031003680901001001c28050030195220303c15407000b400078500580350040c0388c01d40a03007007003051800400c03c0b401c0880c0d0008020794490f61000c0c00603581c00248072004e140d4000c0c142d0f41c024a2150090103e4410450030250600d101044002e02644082c2c10054070b0380c200900440c039010b40c040501c0c503001d41480700b20507503501c0d10020340c6080c152681d045500366408000160080790001000c88041c41c5540103200042041c0c0c50b09403d05403080c440207900860007a02c2c0031b011900031800e6640084144a01340002d11020702c0700100303d0303503868081c2d100d46240b003050344076a1915034014441d007040103440c01ca0004446046075200c41d8080c002c440384160040590301903588074400c40021380100704420181d03000b00c008090542c5001d02d6035161409036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 479914865 1250 479913615 479913619
    0x15150909020a020304050105070f02121509031c0c12020a18080d1715030a0b09100603020f190506030a050412020f0a140c040f05160519080c0d0f050105040b 69
    0x401102c04801e5010060718143c80342440e04c1c1c0da443c174450500c404280c0020030301950022460307a24004181000803001e04003d83c00c2148a80c0d696030081e441d4890248410143e80004007144c1a0883e64031640010013490340340c100070000b030125076204002c81e0080003a0348085000200d2003403925011070501340040100d440144011902d40800407c02118103054a91109001010801d0104048aa0f040d080c9010f421a680c0760b200c1e04101d61401d030107640101c0640505410485021118042d51003500e40103000e140c0395030b503028180100b91014000c0d40c1404000d046c0301094036580d4000450050300d07541c8001c6000c0c1014180403403d0182c43d5003060540d8081528801d00d481c0c003091420700700340c210340480750f6414050580c03030504140c10801a801032030402c2000301004280d105074022880c51102002030822128203580a01c61003854802410b4511400e0786064801d1250039070103205a601d0a060500c085070382020740302500d0541100342d442e40c00510050034644a51000c550382 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 479916115 1250 479914865 479914867
    0x1c120f05060a0905011827080a17040507052119030f0f08010315090803190c050405031c0201060b191d21011e1a0105070b010e0a1515090902 62
    0x14010702241e02c50f10314182c2c40c901c0d9844147c20000c101541d0200c1e0343c000007860175400c100c82e040c501110b065001e91194000324007125070a40d200140702c034000340f18590041c01808090300340030400c034070034007201e880303070003038405105281201d01060180c8141031520142040a00b102c40c070b8090010103e40c0d41c84070400655803495001c60340d1204060341126004040c0500c158044071841c005845500c81c0134001500c00400d00003040c400c6694620358690074181003084480440c001c40e07692041e48a001c3e4940d2002c14408061903c0e80511003074105103000000302d2603a05c168040007a08801d4a0240c0c036014178508485441c1c1050703407020300c0c000300d1031108a9041070f00d0014581c624402400001c0071142d0158180020003584851515480c0a8004080794207c0d1080005008050707044407202ca0702d4503c00c403455003e1400c0d0f0310a80c0d03010b482c2c00f02982c2001034805065000428800c102615644202800703080c50241001404000c00c201d50018000e5801501e80c080c654819181c1a00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 479917365 1250 479916115 479916119
    0xc2006060a1806030f0312060509060d03050d0b0a2301030204050109030b040302070b0c0a2303041a0706020f03010509070c0c090b120706050903120c1c120f05060a090501 75
    0x148035a04081600c4810b403201c165120109500700080000d80c0004000d0f83c2404010740c18590802109001c80d50300c00014084982c881052010041d0f0540310560070095850b0000c0000380100302810f00900030b40000504016180300040b5032814030f512011400c3e000381009410340307500031588545000c00307007015480c061404000030005003641c80040e00d10403100c800b04080500c2404000010b00244000e603132254104206aa21003844039000c550391440c1c4010007040c52244e40c00e20414403111400f95052a18090044007115404120100200c0d810003c69001500f10310284c01100760a440b020788a42c14042070160442d0040e10030400d100780100190009202b2510020075611031540c04605503a2000210b842c03102100140c0400d406440e05c08031307815912001401c1c14080c22012600c4c0d6000c100d01e0b126441c030402441d1403007a00000d0b6080300300300d030410640106401c1450512076038240300c15000201c500715950a10500e49034030a000281c981702030448068114a8000c0111354 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 479918615 1250 479917365 479917369
    0x2190b0706090501020904060308091912080c150c03100e0603060412110118020301230a09031e0f020601170615120f01090b0f010803071b0503010c200606 68
    0x40522200101459203410b45202009800c0d0151112070300c029005011440d16031511480340e40002c0090781c00b810411007000c16100d60002c0724012501c10100f0f5031a60f95503034444140640c0407149400440c481d882044440c0e01144c00224800c004802c0e03010789134100b41d0508055220194040c0c1010311820050150035a004902c2c290444c3e44242c9108080c0075241c020341d012035142045640c1d40d4a459014030040c02e40b0800440494800c40c001c0055810050600e1001050402ea040d00c0c80b0801001a49014650780700402950007400d10750305102906031601013021064801900140304c0144000f00a901008078602600c0e0900c4c0e61180c84503001c5007142d07514001042002c8140c401101d0304942d44910b144100a42c401d8419582d030100034903d494044d010090b401c542c0c0400f0600000c0a5014142c41c040c180c501e1900550301c0d02125840e1205080409040f49940580b0008001815a024440c81c401401d03d0303201d07600d42d0b4403d40e4110b2954080c0409001c03941d00b041003004a0340d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 479919865 1250 479918615 479918617
    0x14150406030b1e1e04110a020f01141012030e060408010903020d0206070e09040c05090907080f0d050904090c0905010602010902030c03010603030e1005070501152c071b0b01090902190b 81
    0x1c2001610901c60340101300c001800b41c01c0c4500c0115600500040241030b40c0d50100b2101c82080f2050004d202c2c407006c040040c010308504652040c01c0f49040d100034480035004c9003220000a0182c900503030304200c650005201c552013075000210580d907071051141050b0701800f5000450310300b40084e10403840d0885010301040042c03030900e0320511014000500300701c401040701c0082c280180900305540b5056101e10740d980014098051240301d904542c03040f03114000b0b144280b9034656601c0301d0410948506110107481f5031a4116912001484046941106442442e0003845258004075010321640145410500860720a60099042070400c0c40400d0b0414156840d9240030344440e520700d1f03201e400441c0e80d03001e41e4000911f20350801c0103001241c41c1e100710342030658441e2410b005001c0711a07030001d400700040100307a04013940c1c1140001c0149008801e012266440701042d018400c40a64888120140036041503076001c0da561000e009508160000a03464825611000b803000d0a10b0207118817 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 479921115 1250 479919865 479919889
    0x302090612031213031d1807020a0210030f0f050c030601050f0c0109120f05120c0f0405030307390902071a07120f0b010914150406030b1e 61
    0x2070409218140c03140d0004104803015004503000c540c0342030500c1c0d1100d40600203040000e60009825960310102080030350010543d41b400100610074a21040035240c01000c002820302065001300320440d00961281c00302d40d21000c209a8002540e811104920303001c40d0314403194001114031340070810091550403c02c6a0b00600242081c40c0c44600305044c821892140c040c403c0c035654204502c01301001115080700d441c529258881041d010071007401252180241d11043e02039030683c0d0b0214089a51000080084084e80484c6a28168451020074034650040f04115070001081e0b01200200401c1c00000340c2c5030104584c61a42030104409502644045001d03030700c1f9150b4001114400c209012500707a1140c5810034100c00c19240c40c210240900505e10b00d0740e19141e007445400c00303020100c0d101754034400105854030000d20341003108841c004050b1809041c0c0220104066080500004000d480200301e00e50323010824100542c240300d100c84483c5040b5140c86200ca41103200c960fa05044400707 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 479922365 1250 479921115 479921119
    0x90106050a1a1b010510051c02040504110a24090e04120309060f091101020303071b02060705030f0c19150f0609050114040e071202060304060e1009140703020906 71
    0x408800300354200307034582c8103c031944808043c4001c0309000c9600d040d040075100e8075042e5803040c01c1e241c1c0d8509101a41102580d4801140794241043d4010f103410390216822030301445110342c0074000c003c0400c50030b2006401c814a8022a0b258140302036030483d04c80c00d03603d0010301d080501036240c010140d4100c60050070050411020807284c00c0460310952224040c0b54010310180f0590002c460400000c101c8004141e804802c0c161080307199500000450340918010380c3c0300b40404a840c082c8207012050804200c3e070280741004040c2c08211b0400140045142e000c2c1d41c20741d66203013101424a0304108401041c01c164a030b441c0f4001058101405c1c501c4043c0c12100801d203108441c10718002010550004004980703498000700c0c0320740225100c2480542c081e5020090b102a0f222500d40d01da0081c4510110758803501903220045c14008051a001881801c0c04146001c1c540070150410000100f01c0712126552100c100600070221100c0c0d494407000009050741c14110303000704500c800000c090314 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 479923615 1250 479922365 479922389
    0x70812070c0902070c51120b040f020a180e150d050105040c050a080a0803010b030705160506060f06040b1b07030b090606012a080f071b050906010203270117070314090106050a 77
    0xa88047d035642c110701c045401c01481000700b1840707812030100940000884000081710899210040308810a1482c1074071410b5070300108590b90480c48005c0d902d103000c40140c00c01082c0b064070001078000d000c0c4902951040c0a02c03000282001e0500c5114030f21603000d84203d50007104220301044440342220b054801a200d031540c0e990360300205485c1441111106a5034902c42000030041c8040410f1044c080c4000720b5108841d09404800c0040d00e0196000b19440704104010214100542492810948054405541d03080d5501e460308207085200304e8140c4e141e5088001000301541c5c0c44070008901041d0701c00d0340400120142070000110a500c140208845000100b4145003480c01090701d100c03603807200400f0751080c1d122101c10700c803404d588102802480c0c2500850b10139030000c0b0a458500e103000c001645010a05403070b41c020350303118171015070510440100c880f05041440100030b101d11410384012440c201018207904184800921741e00903a49404818402542c1300c0070000b08403401a4049 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 479924865 1250 479923615 479923637
    0xf15020c09221707120f090303052508030c07120f0e0906060f22052202160f140d0e18040804080708070812070c0902070c51 55
    0x10382000f01103841440d10004003160741800c002c240c013462440800c899440c1000c1a651040c2580c80c2e907903500008000c120203120280d1600000f00d010034240310081284001b1000b40d88a00319654020786125001c54000107421061004400f0507185007909468244010100404010078a030b1480c1c900d135200e601038002080d1240c2ea04810344030781022001945640e02000c0e80e40600041c4008180c0418652002e000542c904d03045d00c0c220300414208215100360712203042203000070b5106200c502c00100500300c2d0100840c42000a9450300c034803914a6409501d00340c2641b03460100800087d00800201a11440305610f41c0044c4503070306da445058101450b20380e0300d4500001e000382d8200c3c2500e803090900006a544002500100300c8000005852544a07041440740d160300c11032170050500113140c1003c02c40100180d00a14860b0300484400031290388584207410020303000c034092484e11240044001c0031a000c024684170028840c1c40040d10200130b41c0f0442002d62a242601e0240844040b40c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 479926115 1250 479924865 479924873
    0xe090a020c01150603061e030b0c03090a0f08120a05101703120916060305160e030f010f0e010e010203091b1c0503030103060605030607020c060c070f15020c0922 71
    0xc14203c0c3d51a602e240505403104401002070000c2d11504c4010807883e10b110900100080080d4262900303c80001d116558113201640c0581c000b43c4604000d201d5810300c1c50108108108810305a0310a03807100380c3d1003a944019070030f540d10117040da00d034551414040c00034915503c3d44840032254a02151140e03a0690041365046000c1d554200c0b10a01c001e208211202c0e802180f403018020400201404868882c01c003182100c804440b06a00d06400001b81d40301c00380510810b003200c80004007210f501a0500e0f40303150035504842c421122507500ca1000c4800250203014023800183e0400c000c5046103009441c03580e1f1074401d001d0940c03069880095039416600c5032001d800c16120100641400d0140d68501580e80340e100b44411703108603140040106607468042445030042d201c0e54014180001044100300c0301e40d000f862500041d10807910001581803d00032000e00070640000540c003406074070318010f4180040081614440c004a008110b40d0070f4010b1400711031010688041c150505040c54 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 479927365 1250 479926115 479926121
    0x23060406030b011d1f12230f010b06130e040602070206040b070308010e0c0702012a03020102040509060301020313060c2c0414100303050c2b0305070e090a020c01 71
    0x42c0603201208004602e0b010903c8014000b1055069803059558170701e00c00008101c40301018a0440594500c204101103100c0e5030408a6405180390040328444454400400b01d464065600c1c580c100880100d500f42013840341c40c0e030404041c0c070343c03e00d00b00d0a4100d655922910340601803104c00c18070042400d01116074140c904241e400741a4a6485842d01300c40042e94000200c11030000d20020000309070b24202c1034032103000320504003140c0d0905006034015500414a401d945045c0c0e403c95a814484030081c0150300c0b0010300035000161749908002c02c3c443d415000400c8540242e004005100901c40c0c0001d84140441d042040040d0346091404119007a050440e143d1082030340d40951000040f00c500d40c0040c07a29000c2f5001c0000351034000c00301c030310a4012100b111126241d440d0030004079001c4e000500000c101203055403840181103600041140390000c00e10102002e20f00100b01190f010b00c00d164101c241400d0800a101800c0c001600d6507800074410102650007180c101c0e10604250 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 479928615 1250 479927365 479927369
    0xa030905070e09100b0409080711040e070b04061101060e06011107081204140a0b16030c0503070c03031202090d02060a0512010320091909080c15010603060923060406 73
    0x1180310b0710b59052003e80c41e941e82c820f800008000916011174820545824400e00501641c800d034214101442529108025041107284540080e2120240040204180702220140c213080150985590a10034010aa40b15101c0000f6040e0f24100082c0030300301400041c40e6214000740ba019400c1b01c440c801c66801d0142e1030f40540900d1003601100e0b105030100602034810345404584e001c01941200042002c4880e03281701d2102080703010400d490060650b1220f2188003130080c1441900c400c010340c1c4030f40c030f10b40c842d000c19602150700600c24000c03d41c1c00071074080c900522003001c1d07051441c880e000840e502c01c1c07090024410840090500c00c0c0710b00400983c2c040a1620140342500c0d070390390914108500301c103403e4101514203840c500e030b01454151b10b4036000e400000c10b03402001e03114031001c06c003c00c584041034400d01410711182d402e40c101081906102c8160f400c105805500d041005800d442c01c5401240d4454102884694480205400080c0980190441d440e140e2915404100248010313 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 479929865 1250 479928615 479928629
    0x60806060906150423030a20190e090d0f050d0c030b03190501110403170a0e0d03030f060e1608250201021309050108060c07030e120a02010906030c050a03090507 71
    0x46000540011250302001c41030000e02082c03000f845c2c0010406444201c1441d00804071a40e0501500380c0000e00c0480c0e0007425005000000c04010340707050040741d406140d11210700f0701101820000300c81c43c140402c0050700b01d1030801144040b0315403000790440c09100003d14074195503048030a0102d00c20f801c1a19242e1000c0c080d02c01a80050400c00c44a000030081590700d582000c4080544101040c101c40450b42c0089555000110401c40361364070790f02110f007070f40400180740110203890381c40109400d001407081d1000649001c85900300d005441095005c0101d9002c2d14082111450394480704410402940c5000c1d90030340e0300c80403062400078111051000024440c900f114003542c05600a000c072211074103d512105a45161480c217130782d824050811103800150200300380141100140c12628400e00b4904580c80c001000f280e403990700c0c0300e1601c0172984422100003e550300b2240b600050030184c8ad0520100304d080c50064661700c54600200c040580c1d60041e0014407105100000180c210 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 479931115 1250 479929865 479929867
    0x9070f020a3005090d230706260403051204050715090e061e01080a0b150405120d0e100c0c03080a02100207050c010309110a06051b0106080606090615 66
    0x2018a06074070941c0310b0320072000d40ca484010100c80c294000c4003030b580042c80041846800d144690384000c151001d6010422013164114a01030940200784055005808641e1b182072480d44010114511030041a248410b102908018000071030341c07040c101c8a401ca054160800b00e0385542c68802d15260150b40070500031a548102c101846a01106803401c03540552008007080c1c0343c0c1070800001601031512000b07a80001140c2c184d0550284144560003518410005000d902503c00b1840c0300070f040c2164083d49000103024091032412403410360349030725004000c040001c2c00d4007000d0800c02807820b141e0310071030001c61207490081c821004100700039401b030381c280c04290b580c0c5803112240c1c001c0c00800700540201c1c1c4420440500ca0300c207407100342d03800000400f0701c2014500190018505288142c0c1c61008011865640b030303d03a2065a4010602952203941e120b19582c01c0c030103c10b10082d14158142d0400900704801100040c0c2c082d003001c011202200d00d51143c200003480c51090340450b1680c940 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 479932365 1250 479931115 479931143
    0xf0204060602010510050a05030607030e070b2b140c03060a09021804230106120f0e071a090a0e0705070b1015030608030a0c05010f09050307170909070f020a 69
    0x41c0c190844d902640900d24008940c035183d10400110031220300849170164400000030700490710a80208200f130b1504010f48110940310031040c0c0990f84003203a00400b01c01c2c400411101582840217000d6809060f803002c005810404070014a66a0003402c0180f0540300070000c03407521f50301d01a0880040c41030040442d0b0780c59800007203183d8030482d07080d00c0d40300c2d0f8500303041d0105101c0a0300030320380d42c440d4600305003055030308095085e01e0440344021480c14413561080c1c4072a00001380e1042d02006a07458009001c030500e0b080c048411030640c100c40c44945c240034070003010780383c44e0541420196100c44480011a9492290442d8039000351140545240119014001c000c2010048003041d034122001000715070300400e90941c192403243c800d1115591003000080b42e014400c603e0360a09911400c004101419004800e90960314681c0091b03545400c006000350403c01031007180c00000c0403810780303541410f920a0002d07000c00e200804045c24081030700528102c151003408030150059220888240b01f207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 479933615 1250 479932365 479932367
    0x7020d20012904050610080a150306091209080d08060321131d1302030a0c06052d030c0d2c060a09021e13020c0606011b03080606070f02040606 63
    0x1c0d01c02d1141008a450490085980c182401640d100300c0340a000c1c1c0319602c840b900200c0d8036140082c06524020b50711049a0701141c5d1030f81215006500611000c03c0c01103240c1000c1c0c4124003040e035548140700001d44100180040403503980f030888540e00b010301071640d034038001c82d082111004c01d2042082d20310f204240009801c07400380001c2c4445e245074a000d11b0b295080c400300028003205c0303103030040ca40b280014801032001d0254060b042c40541a82c5c05a003203079a8100100c1d80b00d40144d408a6404218100045400c0c0002000211481c600d4090340b000f440c4840e2840c4009040303100001c800151005d01c0c0041600070200a001110345d210715440240d5000c0d15400051210650b02d00801001c80c00103982801100b20494000b4606120200c41c40031203003030301d01e80c208810782004400031044a01e003094400b919900300120302a016502e0b00800040001d8550402e14614402508855012a5020708901e502c4001074500fa6a83e405608020480001e0401d0007036000f81007000211301d407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 479934865 1250 479933615 479933651
    0x40b1602010e0a03050a020d0201060e010315020c0604111c0213050c0c030f04090501050d05070501050c12030f06100503011a0304022206060305010f0605030f071b0b010305060c0307020d2001 84
    0x2103040d9013074031004030f0b248d03108034207884d018401d5540700084075006002003408480c07140d41a28681000515215000c4016070804408075010795400c2e801802c52070a0382021081b001d0003903106144240d0050b1031341c2c0060242c0017441b0003141d903140c0d150b000510024500c0c0880e00900c02203006c0b243c0f0352a007196000207030307403050040140c02d6050400005440c201811007411a980c010040c0120b1030502d8011103103074204043c50a0b0a1082c4600851280d518400460080007010701d918100c0c5014020b000211591240320010004200700401000350402201030a00801c0100c1580ea42c50394000101c004202c4000000403031810320780d507040c0c001c40f81e01c50402c5441702d490900c0140c1c0e86651282c002100b030b2140301c0101e00c081001841d502c1c000b102c03c0b64480e600c3d08000410b44410403104c0c0a100c05d000045603058a268014002e01c0010001d1951203035502c4040c6140d441c0820000b5100c1c02c014000d042030003400005440240002804801182c221070f00030000329542094101103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 479936115 1250 479934865 479934877
    0xa0b0703060f060c110a1a09030705060f0d0e0c1503090c0f0d11062203060f06051f1205090d1101140f09070e1303020105060108040b1602010e0a0305 66
    0x11030710308200015841c100306454000c446507500c4210034000303161501c3d09280010125182d10036980da03401f01e6050110001d21010500004005072242d20000034146002e1040e000584a04010b10001c41e00c2c10107071080700c0072035501c40c0000c10b100c0f40c511209403410a40030b449592020b59444031612450808026500c6070001c041100c4004030007030f091004240403450715a801401491095004c6180e000f07107403203c294090119880c0c0038040750003082c1c50070f520900c0303091103a29038020400d00180b4013540f50002c003101c508011003440c0000040c0c07169200c01200100559856503078030340c9070081410b0788408121920a11161910b030030560303182c1c03404070584400304491150310030031036805200301c4a00c52080b00b40d03460b590300c544803c0300400b4001002209184110100401c00c82c54007484140220032a01074102c080201f4500030f42915001400d50341042004020031000c50004d40310701d0f80000721468007200d0f15281500c101c1c05004503d40c040c00d80d01c10400e15400f01540100103040e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 479937365 1250 479936115 479936117
    0x10020c030a0f1a0c270411030f0f06060403031d0907020d2309010e150a0c210e06090d0c0803090907080c18062b0e01060e040b070c02030a0b07 63
    0x1c1290000c0c5207158819109403500380903000306000705001c217000040600e0002c08000088130803408a50006001e480fa10300c8401050000407092010000316a042c8076046100f60300c1d01c9000d89001000f10307280c0c4c0118400501008640c0d40100758107002400081a0100081d10b804040d140c0514040d590306200794188002030303840140d41c8070a000f406c2c212402c15480041107460003031580011103003d0301c4484080d50200b210032100c1340b40c000b01d0004100076020703501e4901406180d814102040c2c0b01e98170043c1c2c1041d070350f4031080d03036070551207214062500c204070350203078448a641c004185201c0c80d245000300500003520703000c1484100040030b4003081204450500e0a561105021949040240d901c100d855006100401003050414101600c60794080c01040c28072034506030b00c502d121405100301c500304032003503403100c00100c0c1d40c0580c04620840b84020300841e440c3c00400800700000810107881d1481d500c01140460340f1809039081210703002002c0f1440c0c58480e0400550450064071504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 479938615 1250 479937365 479937383
    0xb03040f022b06050601020c03060106090e01050109080d030c050412050105010311040b030a12031e05091e19020a12050d091d04140f0f030702090f060d0210020c030a0f 74
    0x10058075080060000707080020b9062000840d020b9a400c0d002c0c0c000a04001e0643c0101d01e14450691001c001090003030085954480000b450000014290081a000702e0704004061000380700c0a000052034500c0c10b291171034006444500f08404840900841d0801d06250900600100c1401015003111741a40d004010b0200840850002c000c00c43c4e0228900ca42c1540020051401050b498131a0492000e414107020030f0300b106d0303a0031402207400f10250252006540300148020304c0b004002d500c04c4c1c04041406800d1620310b81c5120766031060b2508400d041101419a030404540f21601c054000f0f140359440141a04014500315464006035918800080c40c0c0769400903600880c84c861070605400b000c2026030079200c0d034403000c2d0f070440f5005049150788151111101041d90800201c100320600002440d1a45010310400c264404060300c102c00c1003114100341725580d624000c0c45041c0c04e504031440d0403080ca5031034042c1e003001c01d1381c40e0859040c0550304401b000e2002d1043d002e060184100e5640e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 479939865 1250 479938615 479938639
    0xa0906060206130c12031e0f02060a0c0806060702060f04080307140303010b030604050a0207050609030415020f0d050901110604061b0318060b0a0e25020604150906060b03040f02 78
    0x2e48480900e0f00020701490205442040b240d01100c03140d08240740a0b24000740c00c1802c11072000100b134444000a0700046a9181405216034140140f80d00035900b085d0910a091451400818401000c1c004c28482e0400050b910b0840d61403400322214040c00e2820f00351141c0d600c2c0c1e9000d032240c0040c072056501e5411008652081d882c00b10840e8181c81d18448101d045881300700c2480010003004054141c0f05900700040c0740800c800700030061140d01302500942d611424110703558512180301c1041025075202c182c622122080c046111408104186025515540c002004841c0c0d541e640440403107902581d020b200c10700415070007080741484d0040800089140c05d120031400c9640038241100d04014420310303600000c6554001a90303801c030040c02518125150415440315071800e5581580041c46003401d001a101d0210040071504268000f0f040240f616484542500c8400143c0e41003090742c82010b002004907950050000d410358418540d160710f018a8202040f00d501c1c18103030300c900307014019 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 479941115 1250 479939865 479939881
    0x11a1308010c0305011e0605030c090d050a060f020c1c170a0903020c060a0806012f0606030106050406050102031b120d0209010e0f011209021212030f061c0b060f0a0906060206 77
    0x11400c0001c0c1b4250140d880d190100403140c07134002410926080c0002c03c544000c40e03643d00701c82c40c001402400a8071051a540c944503040f00c2610070301c4540c66005201c61a05018041024517140d00b10000449084440400450b0980300c1d101c0e01e003120f16052410b1168107041075006078143c0d886a02201c1c2480c414004110281c0102100c2d180042c0d4a000080c407254170070440c81000901400308206401d0450840c2444a4150000c8200c01e901034010080c0d00e10742409030318010700c000c2d10104429070411b80002c0d2030b8411401c0c00560b061041071000349030a0200210300d103035185405000e0b103c41d01110940c1c0a075200124450004408003850000741c0340020950200d188142c40780400c221060b03580d20b001c0d00086405903481903101001071a5283e040c440c2448940c03652a410f66a850000341000002201408907801080341080c68808508080d41008031103810207030181059691400060214203404819a08442e03070010000390b072044c07030700041c050328031741e40a0700c0c1c0d41c0d81d034901 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 479942365 1250 479941115 479941139
    0x90a1104020f191106070509091005060a051b060106090603050f19180b010303031e020a1b050109231b060415120207111008040209011a1308010c030501 67
    0x303034a00d11207004105800c45030180e80c243c64003140e05400c10240d0300c403010000c1404d000c2c0407902da101081000030841c40301d19150401680c070603d010180e55409041a011910740d0041e80c0c820310501000141080001420003001d280d1111100c0480f845907845050061080c2044e2158902003420440415402115914281c2c810200a0001c08100e02180d141c0c4001c0d011074006020700c1c107040b42ca82c0b0081420408010702071802078902141c102c00d02c140f40100e80382c2003002c605c01c140c8140006c4d04142c0d40200c5040c0b00c0c1203501c0501031185450b051890041401100007803890404803d1800310014034084d00034401e00c5071044e030300d0070645801c0704200d651004403400d6004008120a10510340c09449041242d0355038603102c03440c285d400d18000203e90010300191800e0a480580c03098074541410303081d11510307642c40c0500140c102503004c03481566040c024408031882e5240c0d1b4150108801d81550940c001c2403c62043c15569400070301d000b019101c80b1070000906000000c96050311200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 479943615 1250 479942365 479942377
    0x30c09040c0806090402061b030c06010f0b0705031204060b120a21021213080d03150f05090f0702100212010e0f041a150a18060e060a0306091703090a110402 69
    0xd01012103a0740c1741c1c0e00b0000340c0c0d031024502c4020320b00d41907059444c054040010b0414090020010500c5505040000403240050341c000300d20b0113010018070000500101c2038405841c243c41e030440f0541c0f100d241c410041d181c00d1003c1d0307030818072462007003406450004015200c6809440070183c18101c41d555800840074640f60b2101590000300c014030f0f981c041c070300248605805504810341064950721901d0400300c0718074034000040c1e00c0c0d020b0302d0071400c503159401004000c2d0494918514dc43c00c00030641c140001042e2000752025040080c4410740240052001410401011581c2d00c0610300c1401d03604070207000c1c1c5c600381c50351403000551104a454019000365040411022050703020141618820001885142e00c000d811103103000b540c4035407407228090300641038407039642c0154000072400c44400d9070048114040900a20120b81ca032441003130140e9410010214420510341001a00d0f900d08400d81000784400104010003a1404900314080340c0c03107030809648210b00d0004004c10b9001e84 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 479944865 1250 479943615 479943619
    0x1503060a12021305070504060306090506010c140a06020a0513050904050a080a0e0a180f05070f0c020312030c03060907030912030b030f0d0503070e0301090c050114040902030c09040c0806 82
    0x4000144201c034001c01407001400d100070890049508410400320a0760410346021021400101d000e004850700350043c44085c02d04034204200610700000003c00d084c048001c05080344510862100d040c0c0400d00081c2c036084c1d004281950b8038000d489000742154800c0d80510480114150046564609106080e01580e004001400030007040c0c0c5070440343d6409107a0080510650b54040046c81d2140b00e41035000300700d881420f041d001011a442e10030b071a0080c0e90005000d140c4420840d000303400c20303280c404e0041507241c01c00d5200018400f192810506c4e4881c04a500c0340070082052008511b0f00451090800b90b0301c0350980d032211041a400c0d02c02c045401414091019608240e1a21a500076081d1280c003c2c120362000c1c40c5000c00b5404c01c1c55890112001070740010070041a5600014171142c8800281d008021028880e1103641c2104c02138002d01d8100205039101c000c09140f25000c0e10080e0a0050b0119500e04103c00c080c982c135400070342c441d8003650610683c019014081c181041c0b00d40c2c1c2c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 479946115 1250 479944865 479944879
    0x601030e12030c090604030512071e0210080702010f050a0603020315130b040206070f030207050405090304260304180504020f01080c0904090312061e0b280203041502030306150306 79
    0x18600b102c4541e8100600c0e00745c00100501c400008540c0030000c11030113860a1690365a0741815007403111f05960704600c25000086480c001c880161100d0f68032034402e4555282125040c0c842d003c1c200d014008034040000741e2410903003407014080306580480200c038400c40c211400782800504c2c00f0b01c0c40200300c032080c0e1540200d00c5000e001c610f410340415481880100883d14010740d658480c03001032101401a0016030000a09000c182007520810f030304030032614021802c0610b071000c000c0340c8004800401c20707841d000041a092143d0208142d6001d0a1900d000c82d040c41130a8912030000c03c03084030180c1c40380c0c00042c034010300341d405614524010303c5008011440c201086061001070251400128100106810700d650300384010310850b0003405404600510580068601e41c940c2c85044d0810700010700d0410420000c100b1519903a00c441c4121103402d00c81c4407440c80c050342035004950210ba00644a00401004591b000c4011403103408200c175118100e1032001180c1c00c150004440c10760300a15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 479947365 1250 479946115 479946121
    0x10b0102190201090f140a050144011e0b0406050909040507030605180705060a0e22020f04091d0705150c07030309030b0906072015010e0601030e1203 66
    0x1a08041d0421140181040c0d6561540c0d500c500c91403000300d601551112003691160440c030b01d049840300008140c2440c0c440703580007e11003c1c281e21424800440000a100c1ca04a030415400c02c503000c0d10540000c42c603140c0c41d81d64003000c0800402d15440304680543c1400c0120380b2842170000d0b1001d0719001c0d41d6150500a519003400180e0318064425140da210700030b80040011310794081c07544a400d80d5500c1500100f1107540c60b03403074442c85400c01c80c03290000317014101032598010100000d18404441000d050450900d031300007400520103110a041d0700000c0d0f550b00c0c0300d2240c0c2c000d00440d01400801c004041222a211311402103001100f030194004420401603480c140c1903076900d61403001281442d0003900c400180c607104290740704030046501c080c0c007003090294100100c0c1c1c0c8030a4540190119140c50100141135203400c07814442100c4c807071100b080300800c082108881c1c68004c41c410a041756118074020388120760031142e440c0000e040a2201398204c5003c5155044811100c1d602802e640f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 479948615 1250 479947365 479947393
    0x207060c050a031101140405030c0d050702130b060d1406011b170d020d0f0504050606090f0a0216050f0601140303040e01050402091c030509130c08072f0609060702010b0102 76
    0x30844c071000400c43d640b01e82019985000d50f07420180a14841e5009503999444000e90030b05014200c00c4440c1841810321030b40b400350311103070101103008040c0b91000401a8201000908500501d0070b0254400e01d410505204141003001042c0580c03000d898800030003000c40c0006110048a02c0003c003848c1c548180500d490100324041d12031403040f82d10240c106918501150100c07112a4080121a0b4442d424041407140c28890329802180590b603460040c6066003a0701c4170008050500702d01c0c503a000030140c28600c1d42500b02100181e01106032120020040134403641c40d43d082c0a801403600c0d031201c014a003442d00100715801c4070a03003103142201e6841c1508005c001e4109074040380c0c00107440c00c0b080c0107544c40c0c2c5480490161194840e00d484920380300c18803600d0706030340c02c80c0c8981d43d2414000300c040741d0300b010301c0c903903c11100e2410200350702440c11001c46c00d4509008038610f40c4520400c00c9032036440030403000c1c40b0b914001c04440305540c0d4510100e085c0d03000509010b001d41c10000140210b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 479949865 1250 479948615 479948627
    0x60d060506041806060f060c03090b0705010605040e0f01060902031603050c0426190b01030209071205010611010b0303030f04030f0207080304092f0f0c100f0c0207060c050a03 77
    0x444402080050028200c003d0051250450750301120520740d00d510a00c0a5040541480042c06184c43c2524a0401c40e42e0090200084c0380607200880c407021401e44100b03c003d400c1303600580006401403241c032640b2650b66a5441d00003018400c50350800501103070408442c0f0a0300d03c514511520b200c0a0541d070101a00100001307448401000340410000c107800b4580800000d0b44070354001c800036070407018106a4102581415258040e030898102c00010070743e16200ca605684d01104d0105040d1102308007520240345030220f001c038540c2400000512a81c10403007240903400020001d01c0498031140401d80c80303100444644500255480115010a1141c0d07442e10075101940100d9140e1a00c51200d103203140c119612000c0701135102c0d000300f00d0758072940704c2c15068403c00d000004110081c822401800e0701409001d9003888001040174110f2203400c00044410b40d40704201000070181041401d40a040b00049240140c455684009240c1c0e106001840d10650004050b1010181a40d012504 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 479951115 1250 479949865 479949871
    0x506030c010915020340030f030503131b0f30051015150206040b0612012a2604080d06050319050d05091f0203041a090315060d0605 58
    0x45210034001041007441c43c013403107003403150040c124a44600c4841e02c3c0c005180040d1100710f003206c16002c402c00008004100354540a82d00d418140d45a54601f18110781002900f200500840500b513502400e4030344074014038041c2d42500340d000d0320494803840c080c1c01804154100c410380d071f21346116105600b0190401100c901d80b086050ba201403401484541c240c0d0001700e02984500901d0800700200381011070303d600c00d60b0080c006000e151402c0e80721030700204401040180940643d0b8614100d0681c02e610001c2c0310346c05550800a8400d042c07240c0d80c0700125000802002c0703003040c01c0307100c0020661400e40780c28048800c013504142d542c541d1382200c290000c54446010940328080850f83d503030280801c90310155112081c0f1a5100d4034100036182c140768003a5403040c01420802d1150545511400c0c0c3c581410b5407680390a50501500202e14600c0740f644801400350000c60500a51384a40000301040344d8220b0480fa8040700030340c500b81e1000001d462895020080c0300c081400104140c10540d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 479952365 1250 479951115 479951117
    0xf040c0201090c09020406030606082a040504141816061b021201290a0515210403120c080a1503050105091e0706051b03160807060506030c010915 64
    0x1e0102a03d82d82d24140242c9604008003094001c1814422140c2c0340c030170540102180d213440b0125040030050710042075200201d803d040c0214110b8144026403000407140181406081007000311a4083e14800000b01070b41c2c0c035003003113980c0c0b50be540703405400280030094105848a4070b4131840c0741c41401da50b2040c0c42c03510100c1400f10f8078450030150f80ea02260400d1a4404000030071940ca400b40400b00c030003846102c2c008250102c003010801d03502c130704031003805480f4151143c02201c0e0820451840d00d0081c0d0320516030000030041081d04481001031010702442c425181d2480d1a2440c0c00d2200039a8841404103000034100700005051040c00c0d0864200e150130120b09101c0039880751910b0b401e45030202d403100c015030300651022005041107940013482194a10141c080d25080c500e00030050700c2528802a80e030b201101c0c00810405003030040b5180b031108a211040114503a243c9445290003050003907403858a000d0001d9454140403030500008a03050392604500d43c14100494407414101c24010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 479953615 1250 479952365 479952371
    0x111e0717070f03032106080c0114070804031a280915060902040f05060306300d0f11030903060109020a09080604081806040602121b03160308060303090f040c0201 71
    0x1640c924842c0c01c0b100514003a03a164400c1c3d05064944e05c0b48225441342d0080c80500e024020004180c001c07d1480101e9001d182c80d65022140d074000c100b45000d0b00d80060b0541c1c0002500000b0882c1581d900c06681c0010010802e0380e94590490710045141e8038003210900f80c001038a507484040380d504c0269464400d080c2c3c01e5660041c549604104d4446030042c0394415030014090200904034201600200b038100c4e405443e61402d240850001c090103400a6000240b03490342600240385191604064004401180c0790b0310b40801c2c00600300346407886d40c400407405400b03e0800440010003101c4d0b0f9007101400900140c0d00e0300380360701e0003035001d0300c910401c03c540b075a408200e01c8014041540982d01656070107403108051211840034000c5d0120561250008100800030103401042c51114298800034890b1120106920801d8013905054003084d40e000001e480000e5043c0100c0301060f00380a42c2e542140c179038900060564911031410300c1640034101c1000c143d40b0303180c240c10000b00920a84008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 479954865 1250 479953615 479953619
    0x10212090a0c21290907030c030204020f073306030b1611011401091b0f050315090106110f0606180406380102010b010e090406060510111e071707 64
    0x600b01d0f180b5140c46904054455014902d5600a6110301307500814618081e001c59441d5583c1d900020000d0702c0000c2c00b4680125020b800322058038142c0c2c5085800000c0c284004800420950b1031403050a030f54844a4012024904902d0301445444140c0342e12030b21400807515081c0d0300884409108241e8030403c184c0303019006a4040a000b0088402124a601c040d203505160b070100a980c02181100c0701082074103001120290b100200303007010300d09801c00c1c0b44e580c2c40d04150601c4400b500041207400600e0407000003542c59100c2c640500084011042c1c41d211180403080ca41c46188c16200f40d03502141c40da100c0e072405654119440d0300944180f600040c5c0f087e0805004a441000010000c254a1154000c041c0140050b07140c5103429030910080280d500d0550020300f15032804014980a8851074000400f0800c9503848071018240080015562640c0c0000081081116050098150240c814903104040d958401c010b0081032441c00341c80100d0910b0144032910401001c0d04901744614400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 479956115 1250 479954865 479954873
    0xa140f06270301021306050c0a0506010b032502030d150e090705120f0706120b0d060e0708010218040207020102120c03130503030c1c1808010212090a0c21 68
    0x8055981d500795241d01007400c400040340114800100071402640100251561074403880441d10650b085801c0c035035100c21100c40074501c3e00007200b900a00c10b104003400411001118005980f09140c2e1100c1120001c0e080b554403090404071221100159105201e00c01141d41346030884001c00c9909024071508681c0c507100b515420344141c40020300c54110840c14005810107100000c4a40300c1c11000300040c01440c200b2560f5440310b0b12484040045040300e149151569402c044883c0740700a18107216039a0b542400c10060448090b41c1c2864441c50000040007101802540c01c4c03054444005440070b80f5220500c0065800700e2401c90440c003444007001d4007618003601801001500e003000f1902c960b800100480601c0054201d03e00ca41e105010030780071040f0019004642e8001001c0300100b403014900b0a444000c20914000d054402c01c420100303100d60154041c1640d180c948030a86125110310a4041e1100320500000d4400e2900d2201070090741041d2040c1c500c1810b40403c141402105130711 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 479957365 1250 479956115 479956117
    0x1030503091e1302161506061103120c070602041e150e01020604060b031207110103060905090c1e04110d0f06030206070b06030a06090302030304030801140303071b080d020d020d08060a140f06 84
    0x451b204c10030b039851000340b02c01980282d4107a0400e82c95001585000c4074001c0d034110b000401003143e100071000140c80710400c40d0790b0301a80d009004800d4028803880310454540f00d81c0340c060282400c1983c5484101152510501148980c454103030003030081a204c0b61110300280c0641d800b1140c141c842c10111007040220100103001c1380340280c20544202850b54001003d84166511021005050500f81301c0c040102091001040d2130407190281c0c1802c984a240460300c10443c80030f9031180c94052240c002207200d600800800001100800015084094450031540c003804040e40140081c400000003400280784150000c500601f15010100c00d6600c117401e0303c04090342240148c10120500c0100b41d04520041e015101800150202440d1017000c00e9590150050280250700240900a0030b00f040c0c08515002d444814180c1d010103041820283d5180319201d005d000521070030590001d103d100d0092140140f00041c100c011051509010000d0b00e5003040c0702a038001b20f4000f4000b41a61040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 479958615 1250 479957365 479957393
    0x5030705070f14180a05060316080c0103060f0b040302100207080703030c02030f07140105070c0e0a020c150108030a080703021b060a060902070b042901030503091e130216 75
    0x501e07200c45060000009128008100f042c0c020144002d03044d001c40e07200c10529a1211250a0000300795451600086ca000c07021103038628180c240040204161a0104000050303802c02e880c14444c0d00c3e0ba40c0a20340304800e4511032058400300600c402c0c001898021b5200e180303040e00c1d00c1100ca080b41c5407840141403140c0340d4001c801240d2000e2800e07003182414807110282d00858006024020300d062107544512881d2707050103040282c00100709042109034548440603140340ba1100c034680c40c3c1458440000d6001403104c0c120f510074490200d600d0b9020700181810703039103130001650620314400c1080c3c500d807001403c210240f40e02840302403060060154a00a040502c1d4006c0190b414621040c00444610b1307048040a14010461500810215450a41c0080e8040c0710350017030400000c00e0502003084800d0802c04150554000001c1c000001302601c80e943d000c07034078425200c0c6048004405024020704e00e40c1c04c1103140900d40301807180382e0b000c3c0042208020400d40e070355566944006c0e0080c281 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 479959865 1250 479958615 479958629
    0x10f06030201030f0b22181a130c0b0a090e040f0b09031e0711090c03010602012d0b01120f020309190c0e04020103090204060e041401110a030203040503070507 70
    0x1020200195a894001c060001002400c100054101d590128840ca2810100140d902c2505118415814100c0d84050f41c81a021100501002594a0300c1000c0c100080070f00241d9200600100e1b80e182030303540c05284042d500c500000c2203546410710f50001038000c0c085c074005205009038006021200f0307054540c4a03d22411a11107141a40e00c0e00e0290340101a1090380c860b40140000301070700b5000388100b03c03403e00415a99840d48620300d000381000501c0580c03141c1042c20380090000065184025505a41680d002802504148141d2800003828031640c82e251410403a14950004056440b018a415040c13501d030700c0001c404811401a1142c2e8041204142e0f030001c1089000032060080d41c91102504204000300364498035500c0f1160b0041c01521101c41380c07100440c0c11a03009a000404c09503020b40240f01c0c16644150702d06561000b12419218000c158005007601d410621030707044d80b1040c60021509203d44024114020342009004480c54402048840d012650400c0090024414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 479961115 1250 479959865 479959871
    0x1140102070f0342020d1506051903110901083607050909030f030709030b010e010311090c390d09090e0d08130b07030b010e0f0d08090a0305010f 64
    0x103912078400d50f4040092035840540008018180c20f084c18504449481601100140e220801e003081c410007010171700e4030340c1c1c00038003042800510b05d9000006412070801808003a04001000642030307050b6406145c00700310805080100342850340c02040b45c5900000ca541c001524562104070300c29800e140305607421400e500d16100c001003440c00f001850080c0c030054512001609006410550300d01038006140c0d0000300200024482d00d1142d001c0800644c0c00c000d20f07120703959480d00082d901c1d010038002078480d548005c008503001e0138005d030218020f020380b44440b451b200c40014440496000140114031038a08440704030b011071111a594142599068040d100c07030340c40d60300040c1144425a00c4820990300f4071496036883d032004100807040c510103092134507a5968402030527001502d0340400800114140c018800000e40c10351040941d4030082c1c9580c3e2041c02c40301d0401806010250070154025070345940b210009440002420103000e0103000c821509450b580c4850030340711038114a004c4299 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 479962365 1250 479961115 479961143
    0x151905091f0f230103020d0813030804030209070309150e071d0a1d030d2a08010806010504060803041419090e0d092301120e01051b030601020601140102070f03 70
    0x7003c1c46003685110035110740714050b0140144000401105101c064402c1c084e000b012001d002c140340483e2005002c8100c260b0a241d16481c00458582042c0000d9008000e0301c1c001a00c00c0e40a8030400e8000b40c0c01c0458050040e050032224005000c0003003030f40c080ca0044a1b0b000524190325078450f03000c810407000c65040e0346013529000c0100e841003088100011079903040301007c0c2030040105ca401c1c4049070400b240c05400d5000c030500c1008100040d8010210281c0b2040c40300740d201503581d0598111000f518480d90b80d031000c01056411b1030046020a4008000401c560aa0415204803516000d07000f0b40c0d00c004000711038144001c06a20607880c640e10381c0385103d030301c070428801c0311400703800c5052004a042c04d11075290020040c2c50b01100301503010b09a4140c25a010354450144040c0703648050141c444004090350213880c2c00c1c1d40c071003035900d920300302d403120445600b00703a07803144c8410b0b13000382039682ca0300e54044085034610f8080d906600a80303201266110308a600b04001d140100c0071415001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 479963615 1250 479962365 479962391
    0x3050402090f0c030a05041704060302070c060f0909022101080a05060c070c150e04051f1202010c12031103310c060e190906030302151905091f 63
    0x1d00050a03480c18010301d01c100105014040203072a0442100080064143e9540c60840100c040521816008240210780001c9080d85900100b80d003500ca00580440e0b16681d44d07054603580b02011507031011880d4503409100740c0500740d01a1103401c00c40b07030440e0903440c0b002a007180c00200c281c020b103800f80c021a401d5800d0204c200241900300c50300302d0415140500c039845a020711292030085100d0503002e00c040c080c00f40d105e00030f0400da004000300104020f050640060034410050422050201070802c800283c03517440740c80c1c003036900b60180c60700013800380305607035905d03014040b65110b006242da6000742041ca86050b002a500c5250f10f00c2d41e2040001c50700078800032041c065804c505800c013007003080200017500540e1403411101903003803081200c201080020a204800188501e0080e4840c3d00001c44503803542002c6c0480e406902030340c2101e2003112011006013400c9420880c030819a164100307000540764000c0c0c1e4480055010b542d0390801c07175899a1580c02480f44820042a01c44a05e404e0103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 479964865 1250 479963615 479963629
    0x405060408010b03240c03060f040f0b01030b090c070b070c060912200c060a051b0d1806020d0e0607060212040c09140112032a03090b090102030919051003050402 71
    0x40c500748120810010034086441070304217008080042003040407000c12002d8030758803c6000e061000510a2111010804050000f84141802a40002c0c10007030904103a041034000c17103001d40c504030015450902d00d5210105c000070042c1620041006030b582c8500414681d10511025134417030310051f42040c3e00c2400050106000580b181c001a101d280048545140000c414642960a40712507403124114001556140034540c00c3c02c10b92118965034141007a00461658000807031521000700c030110404150180c44828010f00c00540d1004060400f40d902644a459101c2e1004044914200e01da83c0c4034001d90304102e0800c142d4000517000e000800c01010007010141208000410142281c1502c2613a44030b41031042e044c1c00c0748117102e100c061502c103942d080020100000c82c11030074055040c46114019041e4000c0c0c00040c5440c0000c62505a20000c503546443c0503402541845611020440d403520707449030344210406002000a90b0781c8030303540e0b1005948416100010300d07247c280140900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 479966115 1250 479964865 479964883
    0x30a1a04020f07020f03280606060c0305030406050606090a0314060901020a0507031202040e07020312060109050a060807120c090302030c090717151804060b10050a03020a050405060408010b03 84
    0x45140140030210311002c5000980c3c0c521a01255a0020540c004e008a402c10714440108100c190481845d40d403241800d00111001b03520a8400700700c9903503912001c550701a012100240050b0702080403d0108080e41c0001e9000034004008a00c3c007210a4001000000c00d40d1086565030302c2e0500303540b10002d0604c070f80c1f5400305c0c0300c000a5181c00715024005080c5d20a801c002014000071580b141e210f524aa415a8003500040e05002e001d400c000d00e019541350408034044a014020800150040d481900158200c40014042c00a501d0500005480f1688005d200c4800c01c07160414401a024441c0a4101405043e8441104107411801890b040c501c1842c030582c00380c0b60315418803010a40c401074003c0b00f40341e5090142004d0b12400400001002d00e20340c0281e00c0340b030309500c100d0210b03201d20020740110700c585820000203010400b80301e10881041d51708004280103000c00c10b03049000b9001800000460f01e0007500c3d00c3e13119000200745421503080175095079520256000141010403240d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 479967365 1250 479966115 479966119
    0x315040506100f1e031403120c071703040503070b180d080c030a0908070b0103060605120a03090902090301020904151509180902040b0424140913030212030a1a 70
    0xc0e0500f000710900c10068462007078031411180c943e00d030713841d12658a00080d603400458001d01c010130048156998200110b801620b00b140e00110340d920503044201c80e50294080310040a144903c0c0001c185608001d0080d00c450004000302000a801c04d50964840c88400c0100d80100c1c0d12024404e14001d1403140d010700b404041c4051040d2a544042a240d004c1028040481c01c00d8003443c00c9581400b802000030003401841001004021541d001341059440544984085240d07a5600c2070760340740502c90240100e2a0f5030800c1c080103803a5002010304c150041c00161074101400080390407100c00c14003850711070f010700d01c0a2040c9240700728440300903a903510308610402d0030292138a03006465000d41482c8940e43d000c01e40215107588d04004c04115004100300005c0304860782e50020110380c120740b1001c0f4181c03042e02140d071210404a600407140050088800d60ba00d84042b035118000e640d41c280c00758840c4100c00c0442854031401541304801d44034000c50207920f07044036500c508228142c0c081c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 479968615 1250 479967365 479967391
    0x40509101a010516030c1b05011202040605070f0215041403060601080f0127020409050a0e06010612200304080a0e03070501051c0e0f0a0c0e06060304080a09050315040506 75
    0x21140c0c3d0050a031009140080400308100e0818030702601d40e68000b1400801100d901031001c06140c0c000c5084004448003a200d007200e020141c48294201d1089028603008200240840000f007407000d07a100040780c2c4064540541040d0031444040d858010b03038444480c0c0b07800c601d444030780790900380301064002c0320a08002006040a03400500440c4050040c000e0859420140300010032015a0410312000303015001c554890300c4003250005004101c8440192600b0800f22401c54040019028102c86056980340042c050041094001c2d00d200c1701c1c074000c3d80c40154015a000540d441c02580228400c4400e1507a4011480c8042c2c4050403d1409070f00c0380d000382c034007000b035641c02c00121006614010024050702084103440030040202d010280214451450b44506200001480c40c2a160054821104040e031702d5103005540a0308581c5683c00450500c040340006001074054800300c000c905150007802c1c3c6620210385803001c00e0401d40942090340040c0803d0281c148607064004a0004942c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 479969865 1250 479968615 479968661
    0x15330303090f0e06130906020301030308040203061f0b1b03180a090c0e010f05120103030e031005060d02040b0d06020f0315121e010e12030108071e050103020901090504050910 77
    0x881e6004000e012030301502c0385c21a4210702c4201c5030b00414456030700400441d1256103c0c14028400e48040b20101e02038454280424014031084c0e403049916922000a10591400d00d50380030f0041d00154400e4103c6031f00d030b82c520003075144140054071101c460302003041d03040c4c00c281003000020090787d4820382900b460060101d40d42540200441050407003800c000c00002c0111004031054800c4440b100304100341400044100b642c06030a000032036900f01c00300c43c0503d200c203040c441110b0b01542c8103940558100440030040c07e25030441204035500804c441d5010106450310300a980c4401c90184502c1000002c21880c0c0a10004000e040300c01074445009880c1c078100c001d5640d030b400034a480d807482417950441c280c2a800b5004610055082c80594034000810102007a0540081c002c403010307400b60038000714140d2041c2e0201c1c0c55406503510640381c01803070300006400a40c40704035064108000e114000c11540c0361401171030b008281c01c0700204a03801600032040b00325420060704407490301200501c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 479971115 1250 479969865 479969879
    0x4050303070e0a080613021f0309030e180f0c120a021c02070f02040e0715260601020d030e01110a0c060c030c0903140f060712060602060415330303090f 67
    0xc591b602600898000d00c1002e01400010740e404440c5c0300f001001080d4190613010564984c004c0d0300010310076100c0c00d242044100801042010406000f290150340700005004900c0c00d100d13180e00304034040c01c0d440c588000d0b100c1c2d00c03105280882d02221015000600c1102c5801c981380d19401c0004410411414800c1070395984021000c40c5101910942c0c44440f03800400400703210fa5001000ba241c00500340c4a5011006080b040040451000c10699035500c51503046a044505124020503030140001d0840100b05400610740b11005505640d80c81c00403c0c40b103242d8800030b00b03903401d40b504c8030807031020149004030599030025064000c01d414405254081c41c1c0041d446800c0d207900c9007280d80c124020594071803820401e845021958030a200901ca65990460940c02001c4180d01c006c0c0052608d0b0340701640e1300ca038241c5000744240d9001d007000394004016801030502111071031480310030802040b810380000c005280c50b24003104900b4001c10806070480007810045c0308010004044500d8080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 479972365 1250 479971115 479971123
    0x203190c11150c0d09020102251e03171b0607111006050604290d05091006060203030c090f0d060204080c0118050108220c0509070804150b030705060304050303070e0a08 74
    0x840c4c0300040c0c0b80c0f481c6204582c000d008182441b001d035030f00303501d8513464a807050404250300c1c42841003409003c081d50700100548540300003940e03009841031000e01e030446070f000050b903c500c50ba03d1141010303101c04640701e94140015801411107a481740181c080d901d0740c00d814042d00090302c02d44d991070303c54100500c2e1a03032400d803403c0700e0382030384802d0b44e0b94085864500c3c120007410301a000c0203c009812402a400d5511080c0a80080300c1290483c14000410744100e49071405503801683c010300015500c00481c00042080c03c50103050b2440c083d4041012846690301a1011908190081418000c2c40410495001444824603014280040c0e211515541d80341c1030148a040245c1200043c910100515420112502c0c400b00003111130380314101081021964081d003031240000901003480c243c4107054050040e40c02a100012114006c07903004010110b4080064050064490000b00d0b03503034090107103100324001d40103959a442c08510040c8060b408d00c07491445551680001c2c401c54030001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 479973615 1250 479972365 479972377
    0x8040f0308070311040909050f060411040506040b0306150310060e1603020408070f080c0d030e0d15090c05040e0601081203091e0a0b0601051c0203190c11150c 70
    0x4180118540c5500008502134035a40740c070755088040000d0001007440705903000310041c03070241d002c5d110403610364061103071180740654004d0030b2031080804103290ba18069108076000f03200184009040c01c6070b9030100e03042000844030f41c00c84071001101c04200381800d01285411882030041044254240019000c2401e405007031520700200540c40b609000d40a903045402401d004811a508695560784000220038580540c1c41d42d802580d20111081c1001280b00a40c070344c1c95101d070002400c10b071040c0f02010540120540b0000030481c11510024818421104194024500c22101d1070034901440261100d0829510b800d6202c01d0042001e950007207507103080d203901210010745e40d44410a169180890118007a083c5049400c0802200d0300c0008108400074491003105e40b069543c240151014060303000356143e041c07000c0070340032007a12466000710350210088185207000d0460003c1d03001120800b810b01d6000c1150301d8200d00c0c281c801004035000041c00c01e1440d8960b8601410a603025005030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 479974865 1250 479973615 479973617
    0x503190b0910060b0307091a032206060f030b091b10210203220c120f2306090303060604090902120d09141212090109031209140108040f03 61
    0x32802007040418180008190909942c2c0240446529000140d103103901c00d40c1d81d03402003111a200003a403a008082094030b11107500382c5c12800c50742c41c80741460003840c210300c50b800c869117a500003500084070b81c416030018210b24581500c0c12400c1d46004e6080000c0580500865405421400d24015075042c11500b94141038419940f26440030f034040c0e400c445540c05010303c18080c2c40c05005410b6942c2c1c041c5100300c0002d20700e03808450780c00c14100f0120305040409400c280c00c501003881240c01d440c61054540d031141802c0c1d900b03000161a640454485000c810386080f444c072081b1080460108003144e04444030b4406180782d07041540015079075214521070b4112843d1210309107030940d0b56440d5030b0300c0380301e20f800291050350326800d1000340000c01c0ca00841101d040740240000b22410f0103840700d0f6400b03140100406084c6d07001d00d40d140103034025103072003410070602c540701000044d5100b04d0700340c03030b841c84e9203036140c103242000540d21028100c0a0154104030f001c2d41000046401c268500f07002c1609 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 479976115 1250 479974865 479974883
    0x306141014040b040b030f06011e0302030c0c0303010b45010302040504020a02010e0d0203090108011e0b0409090c0e061c020f04090b010311010f02060a0e030403020405041b050319 79
    0x140d450680c924010b65006141103a0301140c000f461702c52903002140b090101048201d21542e810005486003e654641650055407284e03410045900075401150404684410035080500c082c040c1891039009800c036410342d8101140c480151403171500c86030b003020074600c17108038030750000e4504c2c05214404011901c03000032102480e2045c1d0340268111005414003a00035980d50143c410041d000c1d140c81e0000d603030030340300b228020b0360040d1022040d17070380c0c2e0f040503540c0840e5a40782c8441c20382160780c3c40b070a290000707005100004d001030711b02d0018001003100c1c100c04101c243d03203800c041d8529485a44800001c122890030829070b50f85602c48141d5503004100068038105480c008503840d080c0c00e401c41c44e080f51401d911441481140032660f41200d1050817200d48212000004540c099100b2a00300c0150b4003000100d03003108440d41116100707021480840e4141540c940000e010707a00140c40070340306107076264580301c2541038900955010f400207400402d05c0d035080d080144000000c000c000f500ea804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 479977365 1250 479976115 479976137
    0xf07020a08090d120e1306140402131d1509070c021c15021e0a05030112140a060209010e0a0803041a1204110306090604050a0b131202010c03061410 65
    0x5209003005158580244142000801300d00002d010f420340d00c100d030b03480b80605040e000104185806200190b504824032802124040302c1403102030f422182c0521210305481380c010402140e40c19070322143d0909140600c0690038a0b5498078a82c005c01c9003079a010314803501c104041d058126411040b1140d050b10307194058001e240070300d0701c1d0800a4400030070110351441c1110718101e864002d015883d0701302c1aa00c0d005018207504450302d2144100190103e070091004009600c40580c1d15808180a078041501100f0b50084403410002d10000c110384543d40802c0484055a102607404c0e00d50708107440c100c44003030400a03c141ea0b4061031103603090000384490040a0202603006070391401120020b0030180741802d00e4000c0d02d80e00f41444031030003481100700240e45d80b440020300c907000301d03040006041c20711010f0301e130b000e1049030081c003180382c0220719249580010700700442051407545030343c000a0404404240103080d0340065011071b140140d190629006a80d420344409840d02031414140421700c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 479978615 1250 479977365 479977369
    0x2061e010e070c15051f0906120f050f03220522110405031221040803040b040f0210020106030309060c111c15020406030b0909030a081015020a0b0f07020a0809 70
    0x10403a4030b14901d4050420080c800201e1b108900c004c3c040000c0d100d444421350321011014100c401d140306460380154a80700c40c402203140d2400c103d41030f81c011800c0d60740800414089500c2d603400803407110401e14165104039400484802400702520003284c540c40102d40d454009031852025441c0742180da03640304410042c54001c0c0c0201c0700140303005021b503900012400c080c5a01c0e50446624580304ca006e8000b079040c80410600280d2059a01960f60b50a43d1540d8031003a0101c003008004681c05034083d0038600141c3d80384001ca00c0c0ca4456940003103030039030440c900100030602c198020000e0000814190b000140e84038400f1600302350603998000751140846400c02046405600a4034606040c17401204110340ea400030310903540d85840c2809541b0008007400f4905e9011204d00700c05030020f11490350a035118114044e00702c840c07211030f2501c1d0703602c85409489100ca12220790016030f024203120f400300a4034600003507100740c90002c061114a40303a60003948035131142c00002c2c0803030f030005440c2240d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 479979865 1250 479978615 479978633
    0xb0a0203090d2d020105090f0d020d0e040f06090911191e0b0301030305040f062a02010c060e0f060a020403051203040515010b070203011803050d0f02040503010c02061e010e070c 78
    0x1810314200f50a400a00c01c0038082c1c001e2000340ca180c02c40f03009410300102c0444000401e94201c1c85154000c00c3d1512845900f02d6440450f4007049902503282d44117400c0c80d07c0c0700d020301405001c106000140108452604400c108076030b0011034000c0c14008113a85c8440f00414141086a103920700c03081d81c0000b514010f0928002c036802c00780500074080b0000c07040c50303400f030050001e481d03090200350011901c800040d070f1201082e80d160501107804420301c03111901d034408061006441030500c1d0207150a180d503070301d00362a80300100ca05181c0c030954440e040c60030100400c68100b01048803c41c07030a415610b44a403038010a0007410148440000410100316040003200003561410b5640c0781d503540c545200c030031240d000f802d042e88203608160070301c011032640740c01c10010b15605440d4549013040c01045000500403185600907031980c2440006420f840c21300420311300290315800303000a850f01c001642001884403041d05440480319006000c8150700404084c0c000001c0c0c244a40c5e45031442c50000d0003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 479981115 1250 479979865 479979917
    0xf07082409091c0507020901090b04290a0603060b07020918012405060c0c01080a150b0406080c0708070f0804080114070207060f0816090e130b0a0203090d 68
    0x10807950380070804010340108650084110755a810070480503259821500ca01400c8400b943c0043e0a4004200350761b0650712140c002a03003d4000310b00746052800d41104000c0003101c03000020000200003606103015620350000d4501c5040422403581043c20003401d9008403840203019400c40342c0400e06d846800035110712300c0d824400090106940c000e03d0b6000203410051185134144038804c011485d0300d04041500e082d240410b00038a88144481e004403243d040c0070300741860080d6550300000d901140303d07407140050720082d118642d0302c6243c004014101d203401004000b2811051000c1000519050100c0705119041940302c908078289051031241ca00c1507a0010200b58a000303542c1c10307524009501d0300e204400ca5000d803400c0e60f03a1030901b925203031000101180018040400914014040007510b496602c00b0f1520191851312030084402100f03090b5028014581541c0d459420000602e44144d408000e0590540c1941881c00000b60790303482040c40138040c8280e00c04c20040c1600d1461007050703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 479982365 1250 479981115 479981119
    0x7030317060f0d0c050406090b241909050a0504090b0a09020406090203190b0406270212090f0705041116020414071814030a02100e04051501080f070824 67
    0x903c4008500d0021114041c600c10180142d080420006d40c1c94021f1003088a070b02c8c0b001e0110080417481007484001c14650400c500e2080c1403d0042c16800030000087e045105403584955080c20304010030050998031561129118a0a140c002800a10640402a00303c845114041b4281040340700080103010684c10903400c80d4404400c100781802000d80c280c01a1640007070401a42c1c500206000544a0034007400c00c10007401d0700400d600f0380350b802c4081003040e80000c5c0142441c40442c1031300404001510051042c2d8040522501522002d0007108002d007011030b4100001420300d00b1101d258000c440c00c1c1c1194008040c10181951666040301d0f000c21910054010140742145001d000d02666103590818851186c0000c540780750b035412000340d03100004004000d1003025600b00456400210208001c1000f074491200b260b8807640603083c040d040c1d910b02c90148000100004100c0303800108032540020a8800f4820301c140c0040742103400071050503103000016409201e00b44a00d5064181503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 479983615 1250 479982365 479982379
    0xa0804171f0605010818031602130c020a030f050a0909020f1b0106180b031207020612010b0918190e1609050603060f010b030c03060a0b0d09110307030317060f 70
    0x15200c0016403241083d6002600c41c0001910f51014400c0f003902180720004480e03104001802c0b200d14003240c6103440030b100a0540001c0b4603c20340903026103480100750800350344030a00c41010140c0110300c40b0a6071038545026800c00c8a4810000c2403034800b442101c40703d035070010b42c480000441004a462940314101143ea0074980910424001d00e040c2c40380c401c0000480ae080d46d11407250340240700310160001d00800c140348000c20500202d074045441260300aa080007140004a08215880d000309009001251030781c1d02c1c2e5090007a00c002018101007052004400c000e450f42007034000c000c21030900d0310300060003040c44000d5840c03c480c00808098440d044c002c001a15106034210b10320400c025400d861040d2500e120341c0b00ba400003030213942c803001e10034000103042074030070009142e000c0402840d900302240c1e00c4003104030551150340c0c1d181e520340d03d0305c00d028203004001503402e0b4082429401021814955100105142071041101d80103139040000715a0320344d0307aa00810840321005020b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 479984865 1250 479983615 479983663
    0x30120180613060f1205090705011e0801030816150506040f0c0804030f050c0114060f0405040f0807291509010614030a0e071203030b0603010e0c03060102120a09090e0a080417 77
    0x1f0594406191280c18006420710704034140400e4800006404000240c40d8101181d086640d200c8158101300311003401040385144100110b840043e40c0b0000007000b030310029035400c2c4842032206846148032444802400c142007100b4440e8003884140d802901803504504100319240100c03000e2203030030850001e070b40c00c1401810407403005034a400c0c0101802c40703044145101c2d150174402959800c4030050100d8003941c064001050240340105106071140140d140c8034a030140e8a00c000b9111000d203003110300c030035804110280000d151041900c00003103c40354150361404074000c001701c54103402c03100760302404400300b030722518640c0115050341d0405098a02d1151242c06059200c0100101a400241030030608403d42c2444000c582c1a0341c0350b100740f10b1440c3e542001001d8103900260a01c2d0442c424844400100e03c00c25001e00400e50f000c1e90f489040d640303018400f9003507039800b00404c80c581e00f1604040c0d0001d089001218100c1d48003002d003512011041100d2030030149020b0103061160034100c18 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 479986115 1250 479984865 479984881
    0x90c03030307020d020c0a0806010e04030309050d03020301140306011505280c030818030306011d0901090b04060e16111510090c0509030c040b030120180613060f1205 73
    0xa5484140d0341c85e82258520182d0108214135024188500c5081c0e400c00d0006202140503011490703442070103428049002d50085d56050320701b40071903041d10300003035000c0010310502240a0503040c5440046008003ea541404451550f146806643c6030038068005414801c641704200c41904031300d0902c18002200703282040107450000031481c01c80c005150000014000703000c14045c1003900c5d040c41c0007541542e440000540e103107105a1400b221100914000303230140d94504060300d000c0d0207070440c003007100030400e002e101c1a18920303000070004444620403c8108036a4900d08641070b041403401d0240c5648446c400c90801002c01c1e90171600c12a03100c200440e05484840450440364200d008100e002c400c403104503070b98081d0612070b9516400a51154032103107490341180380214002800020742030924404070080030607180a00702c80790400702e44914038000e45100407081401c1516928035000c0700103060070301307040140104800d210b0102c0d403090083c0c0c810a058401200707030320410801c505003040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 479987365 1250 479986115 479986123
    0x612200a05060c030a03140f010510050d18050c0103060302031f020702120d02190807020907020f0a11100207050108010e1302040905032206120506032509060609050a0608090c0303030702 82
    0x70b00000031a0034818250701042e2100302652007804a03c2c0ca1030300c09d03420a41041071108102c0801820040203100d600d80c0ba84840c03041003508844140d03802c0183d0000d24201c1d0401000c2c5243d1410f1510b010400c102585020445d40610740c0f550040d04114001e02d0904e80080c002d00300042c0d0442403a9440c4002442c000503020000102038003282c41c411209a14a640c0720790749100106425020702101d001410450a15030b00001680195800c886450340c206180508448090f9042c0f840f41c00100010300f020124420b070008240301901085040c400080d14802c8107110302c0c8200e0700080c00294520408402d8018408d90080c0188001149420483d960760000c0001d1044050140d0901c3c03c80c16a054030403048808a4440482148074520504010980188525090301880c10340c80e0803140240c880840d80710f03480d03484c0800c4074100030781d6404890954101e00e00b4803001000c113201555546006000311003445c80d06400c283c0c1c6500c2810b0419889107071f075503010300c0003105205015401007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 479988615 1250 479987365 479987377
    0x50d0e19050312060d0213090f050f0309090f060105030c07030306030821180c040f150308120114180415050903180306040c0323030403050304090612200a05060c03 72
    0xa890040313403140e100b040509940301c1c000070b50028020038102a404025000306103003d001e07414060b140c1c40c450712820b0078050001c0802c0c072940c2000500c02503510744011038581002d49011558920b252850000c1d041d840b0281184d218040007103120420580b080d0448405503900c40c00245d103442031400e00310142900011107041400000e00001c0c00280e01c1211110742a044034020034500e22a6800c0c080105000d00c840d02601c0d4882291481e61031680712144020351241c01e5240e503903004610102d0300658180c00038040104400b1452a0b02e0362901303032a001d4035004080702e80c6140c80e2440c03c00b9444641500304440d10303092030304024a4003004006000c3c2c0c01000321080407006681001c2503212001100e004250205451007400800c0c0c4400710803500c2000004500004083c0d5640207103141c009920440305540b0018060140000c54015600207140803104e4540150160746d82c80800c3c2c840107111201d03404400d150300d0306a50780e0340001c00105405032602e03a030b4002058050703440b03610603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 479989865 1250 479988615 479988637
    0xb1906081e0114041506050607080a03050f011d07050903010e0c03070f1802030a061212030b0616110105090a121704050a12051e011a060a050d0e190503 67
    0x71407181c2140352041c041c0740c21091000140ca030443d036a80d507401c540d200d0015000a402c1d07036100310102c0c541d182c0000030610140250201511629805401030917950020075881030300b0280f000400c10004840104d120342d60b184441315030340e65580c01c403c0302c0600800d50000d600d5800c00402c001080300c0442c0319040008107034240e440503916900128034414a0344941c01a5405501030980c9140b03555000d181c018050721404150103641720321a0803250340f005410b441481e1403000c0740300026010320550400420640320136090400705050868146200e000c0030740b40f64058103d051060388114202c03000d8400040080a0b0692134044120815072a0303042256415020100c6a050700d488400340c8084070030003011424824100320401074071880000048561f8418001e1200c41c0e01c50394081428441150307000054485020514483c0110300511824000c2108011740700703202e0351107011100318481c13504000c240c000104200f103150401100708001700e04404c070ba451003080004030060242d0118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 479991115 1250 479989865 479989903
    0x60b0d0204090f02120705010e04020c07052205090d1d12102306101209020607121e0f0e01050c01020316110706080f070e090106020c19120b190608 65
    0x31590030340e40e81e195a806158027040c4000c000c2181464160000c0042000e88415100340c1a512401326520b480c801241c0c3d4000108000042c40e46a2a44075403544a03005400514101c003c1500103803800c00007150596a02c4111208029107456030085030001120000844d9100803c1e802c9030f03001406140d00000d01d030072071030000c0f12250700f0740245680150300041c01030321404181c41c815120b0710040e45600d03201d01e8075502ca83c00503a0740d8034041d00e24503004180000c4810003104c8010032282140c144c0c400442502900481300642c8900070003002c4129042107100d594207840141d445010310340b4580019800002048450390320f0711159520841140c4a807821840254450354641c030300384c003d000004034180d000501d0b86400415140d041102414500a50000e94002c11141c0500f60001005a80550703c244014200b5208007d4000c5101c5d01c404805400d1128109000501c100050700c00340703501020810300284440c404030a0b0050001c00c0203410784d10301005072103082c409200c86092031303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 479992365 1250 479991115 479991139
    0xd14090f0f010b0a260a0501140a0213090f1e020712050a0507080a09030510090201021b0a050f0102010e0316020a050405041509030509100507060510060c060b0d0204090f02 76
    0x200500075070080020041031150068281400421003031182c2c6030714130795004c5c40d06243c1520501400740d0724506008800100e45654034054810042d1406800d0940c03e0748100181d40107819940204000e9030107143e000309010075140034500c06002552080c0c00c0d481000040c1d41003207a003a81c010b00c0d905100e0503292034401c3d50040150742901400d1801c2c0003144040040800041846005240c5111141401400300e601d98440514000c41d920b80801e4103592400040c05560f0100f10031920201d18188440c407200b800700c0400e4443d0340d18401c0302e0107450341406490150f8003c1d040340c081809581c0449444d241d1001c242010190300b90001da01503001d260340410b090401d4003404e4440e681002040d4035040d840c1c403420001b4a10900d042e0104441402840125502e600381071518446560768a5114001c0d8140602111405007250500881d401801c001b155007003584a229035800032130000b003800315000440c2e4031904109000398030522b0403164604024036160250b941c94001d03202011000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 479993615 1250 479992365 479992393
    0x1030c090c020a08030702190b1e130213230a0b030a0803040b18030d150b070b070507170708191d100c050102030c0a1409010c02060d14090f 62
    0x1c0e01c00c048940042c1c015001000102e510b880040d60400c041e48111104040140140c9a00780030700d10080383d03014600c03401e2003580c80170445d151170703010002143c1c14043d08044c50001044071210350024003415001c44407401d242078540c0903480c8002c49220300d2040760030307600c030b1030517098412a0315520302031500c00d210529040000b907030f110541e40162842d04d15121503c59900465009000301c0c4081d52035001c54640c0310b000e00c042c1041503e580070104604208e18007005180c0c174a601300642b181021301c0340f403011070440d1013072542102c1581851a41d400340350074001e1840e0300005060170941c000003446810003071028010725050148000540748298483c0c0119078050b44506100b04030041e20610100318608041c9026104600b4201000c02c882d060f5151401e82c4c008990031b124102000c605214407940240380000081da00d00e00051034107014000280c8680d0100c5c6019025060104941041c00c00e181d004503080c1c20010304109441c40c00c412403903610313010000d200103580240310400c5564 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 479994865 1250 479993615 479993621
    0x4090c02031e090a0b090d060c0822021e0a0306060b0a0e012105060d0b0f0f0c03070203030f100513060314070503060a050c1209072903190204180501030c09 69
    0xa0500400050200b45460003110068100820a5500001f503902203c0064100c0c450b500100048c0c0e100d5a04078a060000d40280840b00800700c11098966800d0800680d60306160000398407040d452101c16420349408248104446d40008107014038103000031410340c650320042c04600001303646002d10b10750b016004464201140c2e0502c1e03101e920031452021844a507400051744410042c000308168400b0340c030754030b00c41102a038200055080180900c41d03403840360400140c1c480c0002c44002c0c61070405035402507491100800020481f21204045a030704c07400c1d866034000030030b40140074542d00303810740c9030341030041c01e00d840101d4403602119001e035800704011440d10200c03000103016006640c6c030f061038000980401400f401c0402001c101040c1400b00e0607840e0343c0101ca074107000740600ca0500c2d24407462106220254405d03141040c044059030010001100d074485680a0354090b42e0b140103640b20041e000f55001000b443c5213034081c103c01c21071140d00241c100d0380603508141400755249100c07812 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 479996115 1250 479994865 479994877
    0x1201060e160f0c24020309070602030c0a03030504050312040303050f0a0e0c010507020a05060a02031c1503030c0c08030301090e01060905070c1e08070809100216050d0804090c02031e 80
    0x31595030001891101c0c0a5103106041500444c1241c0540c0a8003816209002d00d1820802d00c46a0200501c861948208400c0c801342c02c4500003580750280324058195184031040c0001e0405460300002002c014060080c3c5040d0940313803480d10350500303143c9000350161a04a80d881000007103000010301500741c50180856940389100901031002a1070300440720351380402c100741c3e00007840c0c2c00001020348900c0e00038603404c100c0d94007450700c3d081d4031000c20340080981c0d2001d0b0481401e2881b03145402441614820403664103043c051251100c0d880d04480c4d9000a90040708140404800020000c01c1074000d8000b100c03014008104098075080d01d00300715003055810400082d403d12901000450440c1c44025254007072103140400c58103651446841e03804100111240c0b40041a13440240c101186a1801e04150340007804d803190b1480340307449ca03c0340c0078410544500360050111003840721080854010705101c50060120343c107901d034080c1d0f580c0d00c208545800740742411030000900c8444015104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 479997365 1250 479996115 479996117
    0x1104050906101e0c0212011b03021207080403020c040507020706021e060105010c030c0f1212180605070c0f05060108070e010803040603090c090c120b0d0b0a0f0b1201060e16 76
    0x81c0590f842c58034600265080e619024003d284a000000d40c0e00c41948041d1002c0c0c1c0c40021414445401584100b0701d21408500e00b8980140305070440c49400d60350311940b21000d45000c81550341e03182022440c01070b00c806840c1e000b51420f018002e0580c1d0109208058070b403d5000c4070b2400d40304075140386044820a10300311641e003010300180415071050341084665400391800f101d0001d46030721444404e988559080321002c4401e40b500d501c454004075004d50f40154444100150271584410b03d00003440c107200184981e5550002030718084c05030318620340a5400001080741a009858100d54030350003030241112511a101001a0014000c40114142e80340000a1800e051804109901920f08142c0c211040002901c01150250b014401c08401c8855035076052800d0801c0c0200300c1c1241c0d1488d4401c1d008a006040386408191400b0744c0c02c0d0400100c002c00580484804003050040c00011112980320000640c0741b10070b81015000101602d06501034086caa498060016681c1400c485144c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 479998615 1250 479997365 479997377
    0x91602060702241e330d021018080601030b0a020928180207020a05061306050c0a021206090f0601064509050c0406050403080f0706110405090610 64
    0x90b8003a012801241d401100c0b0b102c0020f1000540402131944440840d540902100640341c040710659401d0400007250601c00008160b02e407010340807840480d00084003901500108007500c40c030302d10841c9030101c5c01300c0e5550406400c0e51240001900da6101303110540c1e40e002080049114100c1070b108980d0240002040c0c0040c0b05511000540041600c0c040380301121658440000d4420024204444640d03d002c00143d803048103204111090410750413450288400740300d040200b40790704a03c0c80030740c0c1080c101180c1b184a9070a80c903160180142c0c00035080307680e00d10200161480040e030b5902a015038025210031444403c803e079580c070000d200702c5000642c8851041c030060705410581d1408050002614044849031102c3d409510601d0101e1f500601080010407010700c1c18030840360404400b00b503440c941351400800924500990001402031030340000c03009129030225085a54440e84110240100f4102c011080c40c0358106204150150014000103006880c101c070f1002d4046003151140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 479999865 1250 479998615 479998663
    0x1d15040306201603050f07112d12011d06010f1d070f050c0d02031c14040303020a050717040e010501030212180a020a1707230f040b091602060702 64
    0x19152005404015024030008003c54202c1b001020004d00701d142c0034104041340001064103100328407400d8041090840441702d025000003200858601040104a540c402411003000d0541d00401008140994691041c5007010340240f0118480303040742d50b0403400d09206a5680f001c00868426070050f40e4001410800003512140501e082040e600f5144c600282404401540d40d890300c0d0810054502603403001c2002c0001e40e0a441203190b100151190601020b0091250f4112641010380000c05142e0041800c03940b043c8100142c0322030301d41029451300140200d00407000994042c0c081e010028400d000007048a50090003280d400c01d00c0030030580c2c09651224586141c00706007015581c110b0140c0400c0c0c0340540da84081913005084030420030070040301c4143c20076280540f0380d4403080c010004051528442e102252450b8a00081590300b80035640d1744200084c000c01c00098140c0c0c2c0000307a40188860080305a80f00e41450000d50200c03011521041000d981d50011400944481c542a40312 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 480001115 1250 479999865 479999887
    0x7030c031502040b0304061a010e0307330801031208090318030705100305090d0309030c0b04030215041a07020c0d0f0f080a0f021506010f1d1504030620 67
    0x401401d200c4540c0181002d4840300702c8005507006980076200e0a03114007042101590945d220403810409092100601500002194071010306228200c509038960741c01e5031003c3c0344200030b02a03004601c4200381c44003880150203010068213010030f072400710140b44c020385200d010300300541c00f91103000000d50070604c008880030b071b00e1410075020707030381500490b40700050a07214200c2006980580b6100400d5515003c00035600d0038202904076000c01d401c040c1c250000c02c0e08040360384039042c0c000b0b480109030340c0c407818142d1615610405048a01c2c140b80200414030603a04e4801900b50100d02e281080703500c41100403a070b5503000366115039121815618000c0090030003036064084a1154030703107441110081c4c8504801d85c102c00d408c0c0001c148801c003a0b01d00a0b5050101400300341c030711080301000d8203040000a0882c0f0308607100c8814400b0210070007410042450880716103010003082607180c240d0030000d410301c81d00642b0003203541c1d509106600e030424039040c0352600c034182021101c07401d00a01000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 480002365 1250 480001115 480001133
    0x271101210b030a020303040f060e0406060905010c11100c0303052a0c0f01020307030603050708010c0e131b02010f0b06071205070305120a0501212a053007030c03 71
    0x45000d0b03041c443d0b000300000584007071000d003008002c0c02e0b40d901e00180c501000540381000c0505c840307224a01c0d01c81c00388030194000c203448040c0c0f5000c0c80c100f001c90065150403100035601481103607110b004508610101039000301344600300c0c0d01c207a43c24401c0d520344444c064042c0e580c0c0c1540e10800200c03c25949103248a52010300742e04c4040b4001c40e11101c078600c610600321390058400200107034a802045c41403080c1001088000c4c900e0800030824580c841000a055602d56803002e8455a510004144508056001183d44000f5800c4065640e80c105101900a01951166900a0b0b0400c41001201d240442c1654811904900b02d4058038260340004c4030207034082e0340c040701440400d120000c03082e690070000b01d00c00d0038808400141d030f50401000f801043c0381004115540316030419010005203003130190b19089009102c10009070031811031031156590807608050703080b68842e0307115442c4003451100880260012540175a0f4004256a00ea0b181e000d540409001281078080400016141d60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 480003615 1250 480002365 480002381
    0x1707170c070b180a0518040602070f020301051e0108120708072303040e01090c120b010318150e0307080f0d060306020f09150421020427110121 63
    0x40a44108944450410745140c03c515204104420024110902c2e070034081d080c440a0f110454285018841ca03280c0445001c3c0700070801400242c0100e40c100c01c00544003c0c140c0b18aa00a0003445980382060780041550000a00e07a00303c86d030b6500001404420101c0c0c2c00125070600c0c000ca0386005e1580c0c5855200342d01c54a812a04030f80300d00309002440d01c44000050603410700d9000755a803286850b42e081c0b8031200603004840e1180c03500d1000c40c080d03600003442d1104490660404181c40c01000010b0340102001c41040035070182c1240c0c40820417003216204034410381000780400812107942d40143c1e503400b80c550000d042c0c14080242041070032008014103182003029101242c040c0c2c69943d810160b81104504014407a07001c0396011041ca080240180c07111031a070000b40c109894004a1180c10415541c860f000c2d95004520300150346468000c2c0701e045404044007540310210340c1c070200f041e00d1031000c20f5400d0086048040c201350702c00d42800340141028041003020200c103030004c6000700058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 480004865 1250 480003615 480003637
    0x120c0d020609090c0403030f050a0905010f092d0e010311060c0f0718050601030b01140d0906020c0d09090b0f101106010303080907080a0f1115040b07170717 69
    0x2030010100d6583c5080c0316600c503881307501d44640c40740d246d03250103045051a19000814460103000031044268040380f104201d902c02d02e07003000c4490541070b041d201e00a80750404030f460103c04007880d0a10903554035040130031002c8040614a6503607040303c0c0064030380030b0000804115000302203803014600500503040c9100301c582690889080e4074084c9103081c1d041d511941c0c040380190001d52145109104866100741c080c281030026405460008190304103030300125940c1c542c00301d0320041e4010650702c1044607560040d0210755920b44151515a2802400c8a940025620680115030045940100e104003030024188008481611040101c50700403001e0b80c9007042092600c4c10803d2a0400140b8021400780d100c6a00c6400d1100c2a18202404c6400c40c02480c0e001e031106400184859002c82056504034409244809a000018a0b01c0c511700303c0790f000744000802c020a02d14808402403001c5489002400b040c842d071440301d03421900503850040e06030701e02c90810003039200032000101420a16 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 480006115 1250 480004865 480004867
    0x3130608010b1e1201030501050406050702160611070806271f0506011205130b010501090f140f03030714010b0429040b100201050f0c030c1e07060f05070e120c0d0206 73
    0x4d400e1a48000c00c000342d0080d0b03066910352090101f4070085200d4a6003100e914030240010114206800c0041c03a440d02c210380810020450b1208030780400e000d05400781007080c040ea1080e082000c00002c1c0e80c0b0b02c102c07602d5009440761520001d051400113000302e8100400030880c040d040c00003028002808000d0078241403051032000440310303c19500c9218481c0c2c070201103080c040c00321070408800d00f09050b00b00781d051211440f010309c2036071880820303041112001282c150100b554013000c94168036803140d00940520011950304200040070044c41808a04240208403022200c001c1001343c0388400c1800c2d5000302000c041400010788101072407050355010b0004a6000340c00004038868906070b8002c0e2005035920000e0010b14009040c1d144d400010302003089095041c1075503d0859807050740701d07048424000d520f08900804501090707652441d00040100200744c001c03521140a00401c030391003800a081c0407151112403420009000719840010014011401080103004100445920607688010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 480007365 1250 480006115 480006127
    0x100308070206071a0a060b1c020309160b031b090f06030a09240b060304021c030e03030406030533150f0a031b020a0203062205060903130608010b1e 65
    0x2001213440079a0300c071500740900d032a103642c2000485e44d9a030448a88030302c04020088080f5480d2070302641e030000f40c8000682e640c85090405180948031400e07050103012404002407685d061601452042584840040c0e9405c400806c491107403041c0e941c50760380403100303001140700ca00340341c03020b9640240035400002d0380c0700390358640c000d0101c00501c0a0520203500407290380e140342180074000711428140c03031060960030158001007080342c0300c003402030780c0c22048411403040c1440780702100303001074000e01583c0e600d9440301c000a020381412078180c20340845501d850001d00c04a00020184441250007130054a807012041050b0110b0b618442451b60030180600b90380201d1141c0203100042540d20700040c040710200740700340500380380b564260641d0031890b1000b016840101e1082e501c015050400c094140c03150403140c4103003582a4020700644982d0040201c8028000000c2c0b10810b1101d410701900c0790307100e404036840c09090040b80442a4280840310f0315150141580c1c24404100f0b11541c1850 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 480008615 1250 480007365 480007373
    0x9100f050f1c05091c08190506130c020d0f0c02010c0b07091805010509070804050c090c07060507030b150c0316031b11040f090f030c020a08010603030509150310030807020607 77
    0x3c01c01c0d6000150b942080f200349a0044540000202441c40ca0a00800501c0c3c5581e9102c0c02c403581d80c40c80d0000c103450340d0006000b030750380126038181e622540300b003008818050b010003907858500c030a040001c20818004202c200340a11903a03414030ba41691900c0240340b4550303a4240c40100a05007900b805240300e004150f0300d000715400340140354030040c0090340d5807604040144c401400361085080c049118140400b00f9404114840443c4094a1105890302c5031401b040c10b40c4587c19002e07040e00d2528041c0061681e05412142d2590800c03a9061644091614014a140f1481c03007070650700c4c1e20800440307040300a902c10221703046001e4101180b030240740c0b47c031407460340c080365104880034003881100750341c5468280b041101403003105c00d00300410a8a66207204103400c2e03100c1c0143c01d002c1c8511004086541d103400300e8002e004000700a004a594070301c1c0242035500a216180d06c01d036001c01102415a00341825a44144200f11600b10403c2c51901d51040b961b1000070143d130840030400c0060046 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 480009865 1250 480008615 480008621
    0xa1a0a0602011505040e1b0604030b01080604020a0503030313230123010605040605090f040b121e030304020d0201050d020d11030403030b09040b07030f0204080109060209100f050f1c 80
    0xc1005400105010105a5080c2080915600414801d510703201800501c4200000c0a400640910081103800e0390100700041a41c05680c1c801801d903240c9000100710403c000c6003203070180c2d01c2500c0c1d5041c060344a2b03082503103900085602c2510584142d540002023505485c104c15118802211948071070103d465072801c0d580510024110780b141082d40a5440702c024011900504041c64081e0a0900788140107010303100c1c03208001e2003181051820b01c102d40c1c40782c0c0b001c072220310010301d8440c900d03c0002c071031034031003c5414080306a06112048400310410200880788200d5000342100180415a4015113550b0811300722014260744c01d00185500214078801c0d1810142c151466946134a0549001403e0700c4244d50410300a12a03203052000184621141582120a0b401c000c00c260340e000013043d00a0103140d214049540c2003942100034440d02d0b0340100710f050307810b450249501e504100d003a02c48810040100b40001c200f0003019000c5038484c0003a0110b400404110380c0c2e01c82c8101949429 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 480011115 1250 480009865 480009869
    0x1909050604050a0b01080a020303030a110c010609200304021f050d0e070509090a2f0306011e050a083c06160f020a0f0c030206031008010507170a1a0a 66
    0x90f07000a03500c00c140000740300d10342c1c0108107003c01000b0101640d40800c0c0c4a000c0902900a44d40d00c440303405208080c04da0581d20007040307000c020005241e4a0349100058117405c04203000800d6422806000c5556070001c491140d40c0140c58070440c2c1002c002030165401140340103c0c1002418080b2241d04503440c014959040c9222004151042c14502003002c444c402400041540d03002c41070b80b400040c60b4a030005c1c4806107401c4042e1002002a6007240d214a0480d0f920b0f80c1130044d1000440c54441c11003072107290400800345000210740343e005204180d282c90154821581c06100c030083c4521200c00c0b0029a0380081201a500440b201c58828070240d84200002d056000441008613000a8060a030710b003110724a000003680403842c0003e03441d60f80e441400341030506810307241405d0040d800f880307000966010f002c203035803454201440c14800610f8014403000c0d5080c41c021032100340c824044516454080307940025652150120080102000c2100c21044074001607581800d2b5201c401e4900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 480012365 1250 480011115 480011123
    0x1e0305220f081501050907021506010e03010603060f0e030c06012c0c09010e0406050a170703231510050d0510060902120f04081c02040f170d0e091909050604 69
    0x1040e041ca21803c500d0303689050f04514000c2d441c02c030070020b020b40c0c0029003109260a412482c0d01d95250440103d40d202d100101554042d0300b4041c001040207140d0740001c95581110800f0050351a680204540306e10404445000039880351005200c1d0703860900c004a403c0910b6500320142c01e000606c400b030001412174a038400c40c40b02040b0380702e10b0f50b0012008560008201c404100050801001131940d98850259102100c20001802a035280c00c000e01405180c029480c0701c0c01c04100002826407071040c122000072800744001c403425908000c01d1641c001e089080500340002d04002c10b01c408501b0700c2906603414421090007154007e014403e000103030004000140ea02c008984520f40c1500000d061180c40700645070410011a03000026162002101c540c1c514200c00084d000c003020b40120b03045010345514003507000681115410120741040345100585051146c1c984054031922100038440c0c0c2c102c091000050071074408a00070401c5c0b22140b801c0000c202d04180c0fa0a8500740007118201d07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 480013615 1250 480012365 480012373
    0x2130c02060a150b09010e0d0c0f1502120904090b0109050a0b060c0601120c0915030303050f07121508060c0408161203030203040f08030906041e0305220f08 69
    0x400455041c01800d902c042d02078414000c2c61000300c80e03103280c3ca11900c510303c6201300100724000350340e00c10010801200c600500e038034404044e5082130032a62083d44141e551200100c48002903402d00c90b400d4016401d4250060031111924106100c8503070b120045d000d0784030b50344280c0d001c001400020164060440c2110004103840c14200031006c44545d00781c481c0c8544003d0080202150f40001c4041c15a10071040a01c0048941d240400364502c0d540c100716801c6041050745e0b850802c2c2c01d048003080b207000f81c1c1c042c003403519410a0380f4100c103010784107030002580b000010014415160064074401c1e010b1860b110880765680400c81c1032590554410242420000301081481020410000528010046100107038503142220340a1002218001e007855000f0000070f0611000317904401c1c3c1d036a0000d00c080e50781c0c5010301c41581c40d03410407541222010603012100c140c005201400d44030941d4161921880c10602d01e06416110030241c503103030300800a0305004604021f84442b90401808600010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 480014865 1250 480013615 480013631
    0x30b0411030106090b060301050d0201090312020105041205160f02120706020723010801120614070f0305010f053003131d15130b040c05070c050a15110a0213 69
    0x542903c00b9580940c8825007030107200c19030350ba60201100d0450341c04580b0220030800074801030f68800459440a40701c414145203000c000394064000360f218501c02c05402c051603403114401c0c1c03030b030f402000720b003001002446d100313900000c10f00324080c0f14103400148040300c0401c500d003400f441e01d000354001c0d00041e008803404104400d06100e80010b400110214840a4015000001c0c240101449020b03403488448400405000040c4d000001d000744101e500c980390710f00342402602c2d542d40d208116000174074203400000c0218201013024161040106602d0f00b501801d40f0810a40850300c032907866251809044008070003003080181140c6000840140055207031941026800d10a034141580c406440300404c004090084c10340d0b20741d810212950100c0f8004281120000c100e81d4419941103032402c203400b1b000c103400c14050a40f091080030503410468488051000c4004a1310404c04c41c0200d0000341d1141a000352007030f07003002005400300da04818944c0c00043d140c2d0300b03040b07048480030390303604079 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 480016115 1250 480014865 480014869
    0x60b0a0f05091e0c130305240901050910110d0c0e1512010302060d0f060308180d050303060603180a030503071205070c03051c090501140115020304060810030b0411 72
    0x1042e903101c650758100d98039807040c1c0c80c0c1610340790600070140142400c0006852560100381c0c1100f20103107400000300c0e042d5540c03d806428901200000c1611400801000100d4680303050190520411002003c1c100c9140c001c28040b010b04151454915800c60034000150302c0c908a200d5500e8154859a44010390b406620a001502c0e140c80341401803200100700e008006007501c1752450460380c1c1500e50300d9a88501c0c41032403000f0031901c6c0340340c48080c0c100031000041c022803502030051144942021503c5013558810040803240e60305004115400a10001d03daa1528a0145d84d02185080c1013800100501880c24100b08565a040300494004824402e8055005c50a41c0d099078035681d082000c1c0c2031852000d805510103042c01820040005404281d00785448e01c9021040d00c1d080e0148007407407091034103c1c0a00001312210003010703130341d0000181008240300568220b1000c5c0d00514a46030034240704541c2180000d2019414141400c1c0c00000a988502c525110341d0280b1011132020001d40c003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 480017365 1250 480016115 480016129
    0x40305030d1a030601081506130203090d030b0a0e01030615030203120c0c010e09040f05191103010c02031c02210406020a090611030d050907120b040606210609060b0a0f05 75
    0x50b4843c0a58860b10052004801c005414001c80c854180148541d0b03880e100040e20b041d0b02800045402400441030058000d00041c1c0d610f0951182d840900114482e2014070000d500380d803240c00740030040200108046103039980070800e4406c28101103e00f00780c0f240c0110385414186082d41c0d100880016062070180020300980343e0109003480d01c80b08031400900001e40c402c80241c4040d02c0001d82505850400c13808019500c1d4400c1e140c1560096000300b0305001114014295049010b0b50070042075281c10361011003250440404084a2a22052480001c400941100513548500704401e0142ea0641c0c01e041c91451166200380b60143e5101010070f801840b100c42d07940301905000c0d40800a00710300c0304c0401910130b0702a4450000a441d41ca6006c0d2a103080705540c00408440c50140300c1205102600160b0740c42140114400d00125035100d00401d012010f001041c0480c00d84090502c0001c0d000e42c010a0510f40100d0000c40d2440050000070301c4c1101c540e000b103440c1c1844483c20841b50500f02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 480018615 1250 480017365 480017411
    0x3040f0b0703080711010e060106090603050c030106020304150309171801020c09190b1008040c0e190504050102130e070e010c0221150108010f1b0f050f040305030d 72
    0x3404242031000981c1d02078240c00000d4080401e000d55041d502c1c1e00c0038400d50103c43c040148408031900c950703480201900760300c0d042c025000003a08100000d1030010034501120b04880d0785a00840c0381a1411000583e61240b1030258401c06880700800320100b00214228940c1030701c20303055070759038501c0a1700c0801c07070104480c40f1a042d90405000581a6960107070324650000c1423000103c07000210b01440c0c0014000c0a40483d801440201c0b09a803076039000305038a11a503ca10301d034041140c1c03500100342010a0860b101c6000e01880406902c07a220341f5004035411034417480000d41012400d0070380064110003a0401000f4802c0001002001644a04d018280710300c2801c00700c0c001150303a00401d021190044041030050b000070351040025504001d0001103801d802a4034000d940c54802c11800780c40750303610701440b480c10005409014200c0c01400c2e224a0041c0d110b601a10b400304a0603140ca40120b43c6883e03562006200000208000380018036243c0f802081c0054901d41451200302803001035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 480019865 1250 480018615 480018629
    0x203060a06020d08040b0c0c010204080d0e03060112030c030912060e1014060409021804080c240a0e0123010306050c0c150a0213031a010530070302030a0503040f 71
    0x720b100c3c0103459410108041c0c00603040301900c0031659841e100324a2a00c614407035a2495880003400041c25071000c58044150305096540713540a10f184000c040e6248420701500e2140a0b109211000180c0a00d01e42ca500d6413180c10240640c81c2d8444604103d80c540d81403d998507501c0701417076407000f00c1c10301070b04c040e0143d01c020030401108200d580d1040d00200810040c05141c0e41c03c1810150b6441d03500114000703000c0c0c0700d0010149400d1602081c41c0c2c0014203222001d22440070714032051010700441c0030b040c41720204da07e20740c0d503100c0d8580300c080e1080800c0060603550f540e04000001c1105c24800300e094009640c10115545549084030454000520b41501c8081c14000da202d0340341c01080043c04403000d15642c1074551612600000244136140c45210209503021001040042001c0308913000d16040e450303200da0b030b80c2e2401842807251203410400c0714108541c07403c4000180441c00c02c00f07000040012100c45035107940c040303854201615020b44d40e540c4003003000c2150b00301000f21040a0812 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 480021115 1250 480019865 480019873
    0xb0703050c0a270305060106050409050702070e070c0201030902060310061106061c0c0b030a0902040f050702191b030b09330711010906050603100e150403110706030203060a0602 78
    0x144001040340c5103014045020201c0100b1040c40445800d140002854000c5c0035a6440c1d60b4440026040307a0092142490560070130001481e8913001013007440c201c030751005130b4a20795900c1060449610301c1c070000032818550744800c600c0160301c50101940c070034030184521000c224104440545000e0000c0034410311580301c4802c0254a880390b088140130078140f8800c18071440010301c3c110500c030102d274200d079010342000300401c00900d43c00d400c070ba2840350007070700d041204880c08a121403c0d51400c48800000d68420550000404200182c400105000301e00901c4440300c014561003404030b1591040c1d0b511528034090145503071040c451000c56001c1623500303803042e80350304940041603e0306a9404011203000c200280c1007a024000100c00d80c0321420080000c0d450030b20b4044000c1c0343c2550b0b040d0091140300c0a042c0055418421800320086900041a020752100c00c4003016281c0208100c0c20000400341205040c00c003046110082d010310b0b1405600d0307160103001d01030150001d522034811540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 480022365 1250 480021115 480021127
    0xf030705030307020d1401050403090f120b1602030c0f0105010801050c1207051e0d051014030a020f010c08040923010608240a0602070f0b0304080f0d0f090b0703050c 73
    0x780000443e0b011035070554003600003c0300360904844d20f80e8480380b10758141d4240380c00c2204156010309030038190307002e00409080464440306c4650400e001c16000a004482d00004140b074101c243c02130880f04c02082c41100d281180782c0c0440d03820024030110307240c00ca0f91102d005000201c028020a036100c1544890242072000120905c842404040c4c41c0f034085c00000100800003220f4682d0803001412203040d21941c1e000e58880c014002c246c03c40394035072209410180860000440031040c0c5990348000c0060181c980319400300408075100d4504d50741804030703912541c40080d500c0c0c80500003c04003032400141e85149105200c0408441010340c1c84520701c400c00600c80c00d42c10920303058100f000440b004150340c20b01e1160103012210700c0c100700da10070b00c240c100040c0f480d80003c642c0d01340d401005141e101e895803503a2104240c0016070380105800e905220441907645a01c0103441c0701006c1545c00b00d4041400d815242c1112001d0300300b1303184060703207e08102c07845405000d10782d005070350006002c0c03800c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 480023615 1250 480022365 480022369
    0x1706040201200c060c0a050105071d060f0d090b09120a0c030804051608010c180b04062a060504050609070e13021810060f050705030403020f04150803090f030705 71
    0x1100c844510320702c49101c41e5251108400300a10200c140c4013504c545d50fa14400c10600340c0d00c01d44d11104a800750f08100002d2030b213074801c100d600186070210100d00000910441049100e40082c0580d8810041c10303c503000614200d405160f13110381c09419800ba050621404641c10708104650350b01c80d2000c10080aa01907a10450004113a07805280008107038450703103003c0f42072101075103124184030142c81000c14900c2042d03001e18118541626015151411045100c40b852443e2149900c2c01e10b05000800445000e0743d80c950703000d440c24002c8440e01c0c82120a4203201c0200800c15207a696490081000308070041001a420814400081c440b0b0b5103403030030080051000074a4204070200c60380001003103481c1c140c08064014100c60841000741b414085544a5460501c5228000f910000850300094040c400302c601f4250887d01170344c541030941c1c00340b01da02040301e4542ca4006a5940c0c40034206410507480c00003810418014590342c29180c0108921110900c0e1214403d40046c0d40402841d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 480024865 1250 480023615 480023627
    0x71202070f0b1905071a1008070b0409023f0c0304050601050f03010e06040b041106181e0409030216080114150d02031501050301060b0c0303070309050709090305041706040201 77
    0x1510f00c0b50054506000b0155040ba0700d80500f500007001c103800340005c041e1812a994100348507100c01047c55003107564a002240d030310441441400d03030201c0c1c10407041c45100d13195002056112081c80d10705040e41621840d018484001c445080e2004401c4040481f80103001c2608503040b00c544000c080c21804c0c980c5596440c2c803030600c1103e11070352191001d549292800c0d0804104090b8004c252101403500d41004040702d902100c003100d010f001810940740a140850507109000f040b007130200380884540091000210084070400032103501e090003080f5903526406440c00061084e4042c1480042460b6034505003100c40e00056140e9040c805011001300c08541241e0740b146083c240300c48036800300d00105000e00342c0b4000180d00760088c0d6085803d0040f8a1200c1d030304941e0705034002c02456a94500c45049030140c616900ca2a400400c08690540c0c420340150b000b207130056080d40c0c80c0944ea118228100c40d0050b4084001c03880100e41000003500401c1e0b241070b0b40052001626091a16a00081607 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 480026115 1250 480024865 480024877
    0x203030912120f030f09190b10030215120a06050f041104030215030f0a060e06191520010c020703021504181b1d01030c0212071202070f0b 61
    0x1801d107070210303102581c4204820b451482150b40c8043e9100c941d80110942d80d031085445016000d0f112010844035080010001e0846040d00e248100b242520b981b4018545c0700a000d4950300305d40070341c007c80981c0e10745601d003c980248450680e52103121005801d4101c80042061130064030f000070401541d03c60508850701c0701000c40340080c0d04c0d60704904d4800580259000170790031011006005d618130410b84029030140ca1000d00850342d50380e40c2440754099450a0060000783c40b00c12011a0250405860034005c44480b11201400180c0380c61003203010704101459240050740d006201640001c2100c000441e03088104002c2c000d411130742d40003a540c0c2d103182c4002030083c0003858110000d100c9400c2982c000c1c1c4404880082c01d8044c280c105401740484216035065400d881401400140c010b05c54408900d10381c66084001c01901c4005500900c03c0704400c0c000d41c010344405160300000c0d80d00400e4601c2c4038500120340c4080c0b20790002c1c9031030b120342c100c14a18540040c044c00848500c80550322 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 480027365 1250 480026115 480026119
    0x1e0614030606060f1c1b080c090a030f031b0c06140403050d050c1c0302070c0905040b0403050306040603140a0c06020f0a3003060306200d0e0115080601060e0402040302030309 77
    0x40d40d07901146000800040407641c1180040c90288900c0c180c411600d016182c0140d642d1f502513260300c0350749100c00c0521800c81c03000e600c800c10980400000742c1040f11a04003d001e800c05944150b40c580c4a048548901c044c00c440380e2000c0c0c20705012207070700040010082c0c080d030b5000c64205421659001ea40e01d04400c9840d06101e004200300d90f0514081004040f2003001e5142c0502c140d8207014090041d401500048400301c661542c041008681c91240512903078001d01c3d00000d1340c9594030181d80a60000c1c010540050700d4807404000704a00442c807a040d0007020006041c0302100d03040c00c0c140c88210b40c01800454100d40c1c24100d40e01000100300281a41201102c84240e04007100e00007440e005101800c0f0002c5960245080c1c10b80650004044901500c000d001d102540d01c2d0700c030042c800ca80c00740b40394500140b0181e00c007015258071800e441c0302c407074000082514007001207104650103584100400d90240d40140490756008210841000e4140c4040d0304090450340000c1c0c03280103810401d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 480028615 1250 480027365 480027367
    0x507091b1b140307120e0103140a0902040f020c030301030b0711120a0504091415060c0a031d09180c090606030103030f02150106110601080d140a02011e0614030606060f 74
    0x42c06100742c21154104180c80859035240860300d481e6040402000030341000c2141104840c0031035010313015030501c110004a40303040c940d490300d20900c0140f0040106981003a59004c102c1c0701900c0724801404403410340310007151607614520700604c0c0124000e103680c040020525480030342910000d400300c6140620006503454900c040c00442e4140140d41c8201c0c2545c1c01c10350f40821008003005200d0281030340d243c0442c8940a01c03810300a5921640c42000c0c0240c1c000d8404030007003481110400c5440300811b000d80302103120000040c6d148401950310040954503900c03c1c2682000c2000381655440c0251102980c41c941440002d0b0240414440a000c0c0401481c4881080380300b400000298582c0c220b10740b0880d41c450100420745030064901c0402446050000f14004100013a4070034900c00c1d6a803210301e03480d0702010704c5c0500e0300602044402d541d05e542000c4503506107511420401240c032040002d465140c200b51071865214589010300079000042403041a403901000c0320a0020b00c0120b031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 480029865 1250 480028615 480028667
    0x60301030b0a09020901060903050d090b0a0f02160e010608010f1427010821090303040302040e0703080703030516030c0f0e030c060c01050a05010807060c060b01050d02070507091b 79
    0x441c01903c00d02c2c4000358041558000031480681040c0035400366130042c01103e03021310004900b565014003e0003015003810050055050b01c40c8640d00e0640e40402d1841a50780810312408010a01d1106401090701d81740008018040180d02c003403420300400060031443c42c241d2070071000400c80d103008480c043c020385400c90302070311000101003c0448510805104d0300c9079a96a51b0b80307611103a40103082c100f440c0e580841200c900307001209030391080d44000c020714070340751442e03003000014103144280f04100e02842c0d50000104086070050400b040c000d48002c100c6241c018400b115031b0900320302c1c50041c50329103180003400551024411800b400b043c1012070b801104200003a00e0708540c0c1c4180c0b40c0c80200002c031109000010740009000703040300d0b0300a20050741c981e08420344604850041800080800d654280411072a0300203c5d005181810700358900a05c044104069a0280a0549481c1d22085041080c14018400c0b40c0403820034001c081d00e684d600c004000d003076550b8450040d1020001200d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 480031115 1250 480029865 480029881
    0x50705070206070c0303032301050906030f0d0302070c050d0f02010804050f0a060b0f09070f03021c050c120105100c2d0c170d0807031508120c1902060301030b 70
    0x22901020780041074151910f01d2440c2400104401e80001c6001078106144950310043c1804d0034820f00d540307058566900e80c00c01090005d1600c0080c041c2e9071600c50034a11802400c014000b8142d501d00d02e80e00035944240c141002103040e2580d0313100d0b1740110400c0000b0f40109410614058010781d091800f061036440c1e0b070509603c3c21220803c03000c82801400c8142c01007110030360112003100b00956500780100b10b00001c118883c0c60031541180804c03542c00b00f07002e0003071107940186400040660741034005e031480b880c913070219803048910f03002c600b0000843c002e070380d0f00f011b5440380140350803980d4805100e206500140f40c802c00410082c0700800100260024864103136016a00f034000c3c60303d80c524132701142000d44280d045481070300f007034076040d13000510310325404101240150390b15142c00c601c580b1101412001005c483d403c4481064001401103050307941400192240d40d40b02c0000740d01c455a03140c40c1824500e01d402000d000417012050130340182c40e07103400da90449400c40c012081558400c2c0c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 480032365 1250 480031115 480031117
    0x1e05040f0b0318030c030a0915020c151303081c06051c0602070206161403030708040807260309281106040e2503050f2a0408030415090b0d050705 64
    0x4000d12944c000892082d04000000000d070460103d6540d035000708035070362514040d0040c0407041c4000142c00c80d803490b0083d41040143c080b4520340c07003090749141542d000c024104901c0550001c41d4101c2d000282c001d4039481d41da889080b60f00700220208a03035407400000440700d802c50144551240140d000110a10500b58160740865401401c00c1d6614401605490550b03218500101c070181445195180610030002c15a8842c4d40d964640c070700e0644464659000941001100f2290319070034040050400300b030043d01c1040d11142030000e84d22400d15400003402c01080811800c1464034080300500600e00341002c19420f1500f0001030b40e682c0c4031030000b01c0c0170f91103242c100c402d03080040010310002c10706140050442003d83d42190040740d0407031a0803003c1d03540641d0b5485600e2040000314501c0342070341c400500200703000001044a8010690320064940184d400003843c1e4001041c2000720480e898601690038110740341502d04541000200050341c01814500280d10b41d880d4001a44640590 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 480033615 1250 480032365 480032401
    0x306090a0308071215150503071704150c21090503040e09120c070806070306140f03030405180411061606050604060b0711100905030705010507020301110a1e05040f0b03 74
    0x44d1003400414040300484003c0d450318400d080c0501d42e1030788403c6405100e501681d0044142d030b95030341c040c081c420b0496406c044c00980b041e6007038802e900c02e008130501c651240308130900c0c807a00c46401800780310030135022884290b5100c3c0c106c58200440d90f0009080801101c003031700c442c196200c1c508d440d04080309241c020700e549121607d01c0000341c2c901a0f4000007901d181140c141200f00c1d80c2c95a10b04d00c0403826211184990040e1546114508200e46000310641d01d40c407a020b0110303030526503160300150040c155241c403410600080c000380310074801842c00740f5407041416919145042140c40342d6810310700ca9407001800460391903000c1a602d58550300b10758000d00410245a031544190704000310a014078000203485000044c440b02c2c03400340200369401c1101c4006001d07050703940c0390a00540d8660b00c0b0610882c1d15540e20381264a401c0300050240000740c84550f10240c440b80c003039170301d104900304125828090000500c41001202c0b911044241508d015401081d186e4480d1040f421750030000b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 480034865 1250 480033615 480033647
    0x807090e0f0106030f050714091311030304060c050601051206040b10050904030f020c03061501031a09040506160c12110a15050603071406040b0a050f0a0215060306090a030807 77
    0x1ca030000612038840b0354010020f0144041d038507c0c43c0d507014042030b118010280280c1241d203200c001034100010340684001a4040c03655010035413681c00c0000d05550041c1c0040001c2a20a00304005018041110130b02420041e2001c4008104049026030350300d0740100300405044005002614000388014000c005100c083c00c10440c0707040c1407801078003060403951a1801441403c10b507034000c0c40e0018441d4003ca50100c609040d0f40c01150045020381800a01c078440c3e0044207e070b50f5040d454080e22244034a00580c050101800c050401d1821006040d02034010840340c2e42c8800b0100d4841c43c02c014811560341810083d081000c861a42021082400500800f5905540a140821581041d0b00c1108100c0540e0002501c40380c1190100c0d400c40e1199401410a100c1401b5a2100c0d0b8018070710100b0702e0801904094144c2200c0105900c68641710340140c0102c100c81d2600c4150300308080c1c00c240114043c00c0540b5084c85580c0e0f41e8000107201408008008011400c1c21b802400041d200c1000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 480035971 1106 480034865 480034871
    0x4060224060112050a020f03010b0d06050a032f09040515060d20010e1302040504060e1603200d0e240f090c040e01050a0f060807090e0f01 61
    0x80140740c0c5845caa0308100c2e00d00f0895480300910300a019245030070303036200381700c5058000b5100b0070360249009810048052000401000b00c004213451002c101001c80003080c0f00d0b07403141940400d94103401c8801c020920003407140114404441040c1c6800a0380b0a17181c8030144070220500c500d0242009000c2903400e2201903440c60b482c1c00c102c0341454100b127901000e8001402d200000c00240850a50002e01003215080a014220003842c001c254101c551500701a680900f6401012450030190343e1622160b207031003030440700c8c1e0700b940c01c14500a880b4100114604010805408256154803035620080d0540b0040c8055200050341c000d015002034840500e540d0304800083d1162000b4000d02000b51001d0319070388100c40143c9044030010409040c200c40c004221501e405001c02842c0c240300c2c0c1840700d00800201ca504031f600000d0300040340000c411a150074112003141c1c2c1020780d42 = true := by decide +kernel

theorem cover : BRFrame.Cov 479856115 480035971 := by
  have h0 := BRFrame.cov_init 479856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 479856115 ≤ n) (h2 : n < 480035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
