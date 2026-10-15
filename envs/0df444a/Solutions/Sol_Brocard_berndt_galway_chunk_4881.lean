-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4881
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:02:16.776983+00:00
-- url     : https://prove2.me/submissions/fa9dfa6d-1419-4c2a-83ec-86de3d129524

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 877697841 ≤ n < 877877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 877699091 1250 877697841 877697857
    0xf0b0a1d0903040e07020717061b0d060e01080307020901090c081b0c0d0f110105040b0c0705010f2a0c0c0e06120d21060f0b030705070f11090105010c110105 69
    0x4607420291511400c5007884000d0702c0342c0000da07000450030050381404000c00112230840c40040d124510f4140040311001c0700c0140d500d800302d480002c40004900c240da1102c4040c2a110728001ca5a42c0c58103007059880d80911000d92003400000000a0005124080c840b02c8050342d584080311512940c4c80c520758129021034440300e040381408040c100000800c461042c3d10216a680d2110012070b18014082408810b0301e0740745a41030600300004070300c13190100b40e00010b50041031607849903513040060040c481107004528150406007009252003200204c030605951046225480c8040b500d801d0721440700c000c000a1004212010410a04501d000001d9200c4000390044c07100410180340c02d400e02e420700003110041130b000b034a000c0756120396040944140300c4030034040040c0c50a0610903040c1a1681c130411401d400c0000005010911034070659000507845181944410b855107400040001b01002441c02259a80000186980b04083c00000e1079000010640d10400700c5c0300441d01580030710301c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 877700341 1250 877699091 877699093
    0x50403090305151006020c1e0a0e0c090a0501021902010518060304050a05010f0c0e0d03031107110102010b06032e1203020303011e150806040f0504060f0b0a1d09 71
    0x8002010a42c10700c0052081801d180050320303245031102c60100d820265411801c00c5500c880340c05181034075292425020401d001d120b0005105007400042c0104803150000250b10001000b40001114807101130007510070112580c030161030315031004907079031340c43d05074506035020b00d00d4400809035029200412490f0035200101c140a1440d4000c030302d4541c016201202c50354090a541421b00800b8880d1010031032090b40c0c2484400101d1800401780e6660b103c0d840d1207505071201d00e80801d07011340d00800c9041c01c0d010b007a0f0f40300d106604200e03c4d0036100000721405035080c9070000400d4a030503400c507881150448000c206000d95800030000342e001d25040d80d900150b141801184c032078440103400300a244294011340e500d40c1011503c0c0034418940c01c8100e8190711000c01401607a00180d2038100d11201464110042c0d650540050007a2840c04a0030b600381d40b0b41024001800855009401e07045013003e4140010411041802010a00c07403081c4015080424075503001040503071340480e04400c82034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 877701591 1250 877700341 877700357
    0x706080c0d09120e010306061403092506030e06060a0b0702010c0803130614091c0504090c090801050601090f1205010b0307080114070504081c030e150a141603050403 73
    0x10308000c44090100550f1a00380c1803001071842c1c0c1d4070032445141101c0c2841c090150350b19107030001d840e00492007a00c1c0400c0d000400010341d00241041090b600001c11512050344051420304030000c20040c0c06024002070400300d125502590026019010320350182c0551185454103029103007a41245100300d041040080d8200003081c100b5010b0b50150051040b541402406464080221208034030140e041e481c4400030003104650100b405034561183e10803603c0d030603400d420121001e21454200000203031030700341c95550360b039130042d40074040e169604c0081040345ca0b007000541d101c0925110b1918804c0c2a80340a0185806017903800c9103092150001151001e03056000038280f001a07000a40c00e43e41d15807000b0702200034040c0380ca81140c554107201e407034141041c01c950f8490b20135104420500300c1d0351990004541c8240d00c800c074100204825103205500407000b071800707650155607002c143c03070805400307401c0418112000c80c060742d046c285118070300400ca081900900740050041d41030002d12 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 877702841 1250 877701591 877701607
    0xe0120030403020f0f0a060518010e030c010503060a0305100501030c0608060307090e030d06090509010b010f0f1416030210240e041406010b0a08070309320f0307060b010507050706080c 81
    0x401b10301000750007543c403815101d80ca50a0740744d1580142d150340da8100f04907122081c0882d02c1c04566000001d0f0b00303203401640c81d0707184c40c080303080c00089074001020b503c5440c0203050581069030000d4103881c410758894000300d0703455900f1115181c0503528183e05410005042001d01125402100e10103004c1c011b607800d00c0c401c0028181240e00581c484040d5a0b200d00800000720300038495080000e0007400c24041d04503050000030240001a141e050900840b807a20481005410098503030750301d0264451300e40c008803403074000d482d0000034001040c10b9081c10496802d140e004001d100d040c200a4070801135007483d1030140303e8003400c058415a0443c2d000c507d00c1540c80401d1100a000c2c080584140d41d807800142d80c02030085a0050100d81010b1a000c80e41c0d000600c480d184e90340b1100b0003104600100303840086090120101d0100801c0c520400d070100d031b0000800302c0074124242c043c401c10440d1344a0f10300107642c0c034030070000000c01ca908440c0c424007506000d0303582c1507082898600d01c1410f00b82c403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 877704091 1250 877702841 877702849
    0x1a130c020118050c03010c021501150314040305071a190b0a17061608060a030f1515050a0503071505070303020904020f070b061f030b06070f030e0120030403020f0f 72
    0x788400f0740d496040000700043c1c80c142400b441401100c244010501c004841000d000e02d00818000c0d0012034007420b0280088a100b80c100302c402441d0a40d014140c2c1c100b500d0064400c0d840307250100ea052601c42d4940b060701400a410a102d148103401044140148046403401480d1007039000741d20070110f6a000c07a683c601001001000c1611f0002402141450001c081a07810040c480504111200c0204011525414020700031668401c1d2400031500d12450108400880300a162102c4d40c6000043c0044180080441d4112a41607540002c0240c80b0410700d51250450300800f9191108a42540c407068405d42c000c040450103890b005080030464030005003030381e219180c0e8501c1034402181c28800e01400718030003600b011041390003005080c002485c084404000440020616583d0386500c1a00d4451404442005522046014980d591841c0280401041804040c00940d12060b030101546071540703071945c018208802541814515401c2000c16402c0b071320016000000780c8101d038840c2d11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 877705341 1250 877704091 877704131
    0x902030f070201140a2d05091213050d15050c0310060c05060f04080d020f03070801080118021311030c040321170c071a06010e01030603020f0f120607030e011a130c0201 74
    0x1080446c0402c039424200c80c0e040c503000340c8030100ba4908908100f0b1010120045c040402114030959140540c1c644600301480351103001e600d40183c0500b00390800038000e002c00010b41c400c1020550980702d1a4485108840d003130401c42004243c0e034011004a140000752002c003a500a12400c3c10514120f88240311a007a40c2001440b0300b0015408401d10140d10f4002c1c02e80b0f070140501030002c0068903d001559025589072290117801510b4a49100c080ca01c842e402c0000001c0158482950740c0c03c01600e96400c03540248002d44500400e812051304410b00001042044152540d070402042c10311007012a00c0c000107007060140d044200138038400204080380c450ba01d8103900800502d2480c1510014100861585a0300d041624165040c80180c0e20b0011440051206030b07001059071840b00007007510719000c2e540801051052400304000746605411031842130781200028080105610300b484c603400e41c46501035034000d25403034582d084145198841005802948008920450782c2c0a500300c9600c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 877706591 1250 877705341 877705421
    0x172d16050303010603050c0901120506060f18040f1103012106090303051905010b0a1215031b1a030c0c2b1409031903020a0c0902030f070201140a 64
    0x78101100420007039402d8403513203501114801c03015241812903030000308558081126040d000c1d50710400b0848644840d425039040f5819940060b0b40c038100420042d136803020b030b040c0c42c2d8072031400d003001e0001464080c081d020b4000320034072060b421039092a014080302c414002007464103142c2424180c1c04101e4500503619120700a8800203214102241d00c064207c6c081c800141000e800c2000400c801e1001504407071800006280601a40041011b074802a00302048110720b45160300341c0c04001c4c0909000000007100704210000c00840e0b07602c0945881c18400b09203024001024000103030f10441300002000c5005440080d120700d49203030f480280451200d442e44410301c0d0304110400b036242e030300090545050010240180e0134628100000399a8205071180502d00076001031558080500810004815540c0000c10700c01468595407194003d4104541019204104802290780d00c0e0062040b050b042c0c0c0952a4441c0c55528120554040c20540c103141c0100811b00c40954040011640040f06403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 877707841 1250 877706591 877706593
    0xf1c0515041a0a0b0112090807080a0206010e15060d022b051e130f08041809020a0b030603060408091206010e1f0b030403030911040f09172d1605 64
    0xa00103542c0c040800b100c0003014201924a08030683c0040c1e0703003140f880340c110030740e201002c5080402850002064080d0410003000c4c1c1d800881c44460860300412403505880610a10002c541c0d20319002116410480c00400d800c81d001300320160004909800820071200c02c2c80030390800803220003004128410700800481159580c0c1f05000140601154a00a80e66802d0b10703480d0b241444541410313495039102005040c2200c581d10a400c12030f02c0710a0302c00501196044555600b01c2c12002006085081400c9203e002c01c0d01c0080703800d07100c8205490007000043c0044c0300541e2580d58203141da50205000f6507006c5103113018028245803c100d154068020a001c424850810500d9040d040d80d6102c940c031202403c0e080c003801090201800d40380d1007a018640415048420700701307210448081d0f00190b07005414030310040500c8a441c1c01200c0c00a200382841c10107100742d000f120340c02c0d0241d0031001c9170b240c083c0e648409007035880c1e5824800c11040d500c442c43c80d2005400d0041c8803840b903c0412922 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 877709091 1250 877707841 877707863
    0x100303200d020f0712110609040b060703030603030215010b03130c050618090a0504210314040b040210050f0403080f1201301211150c0d06050f1c051504 67
    0x480f01e0030b101c424000e11741040070070417070090b9564603200c0080c0b01c00300a002e00e00c0072030600596940c0c0c0c0c2180300d100d0b001519031540c8018070704004014004a0005070302500c58400c9080000340644e02650490300c05042d503d0440e281c0408451140450500540c1c440020400106903551404c004140400003c0b40041e05071106109000b803030a001081425150b18240c2003002003203002040c141081d150b85160a10185510340c1900200b00b641100100c00a140003003108000401100c14020350007203902100d540200308080741d587c4030303081c0c00c038a42c000c040c0010000201260050310008842e21940340c1403005d1600c0c80d803100d841c00d070b101140840c080b042c40b5101941c0b150b001d4131928041405420740440a0f110b017402100d980d01e01004001c44602c414041550500c038640309041e030b042001d006030405e200000440e400400404820b0351500400088074640a44400b003202801f502c442c0340843c01d82076002144e0600c00c42544e6078010030010700e807125207640076184100d04c40c0521110b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 877710341 1250 877709091 877709113
    0x20a030c090e010e01060e010e0c040e0103032d0e01210507080106090911181305090f070602071202091f0b300a0c110a0503190503100303200d02 64
    0x20944455500740c07130007649468424070120030501442819640400f01c00c0c1030f20f4130740074a143d916120356800f00d00d051204000100c101036000300c0018544100c01603499810100490a6402840560003140030400c400b80400d0f00354040c041d06805410f03400c02200080c3c420442c00c80076503c2c200e940d040003c205c1401400241d0b08240b0900c00b508031800204030075240c452441a030b510480d40c405007011140c1c58039042d07551350b003044110b01c6040c40c0b00038007039400c0c40c206550751100114440c0c0468001d0150104005100144900c101c91045003040c6107049035409011409034007400c14605402d081c0c01e46110701340c0021f101e90082140c20501540d6240890481200c0021a045840c12019410070203088148160304036421024000340010160308061065038001101d12003204130b401064100d03801d0001c040040e01e089540304011521240b0b5140b002c6416120450354002c00510826050000c04c0c4141410140b484400e0007122507203040da04076a180c01c00320141640140d002019030b030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 877711591 1250 877710341 877710343
    0x30b0a0302150c01151712030f06040b03010e1005061002121623011d0a11270103020a05030109030c03030207020118030f05070e090c04050c070c0305030c1c0503060d020a030c090e 79
    0x31091b1a8101c041c2400f42550900e0801d144000350006500100c4107012851680d80d40d84203e03042480100204071505200d243c2d1500c0f9000d004000b6000b84c90140013840d07a0034000503500f220301e82a03003e4440e4041c1e0300c01240e0590000d1040205181503c494040000d00d9044461000d0707008507095840c981032000f4043c20b440034807001c294203501c800405104504c0002d9829071807540700c0f20303203206095043c008c80c00d0003100c0c1c03940f8001c40c1840c4200d0719414140c08240350680c1c0c02994102603541d01c0d10181400e0300c1501c43c004000409211003030700864800c7e4040e119080c4140b5003140200f50290798400b5514058105640c420039691030101000000c000f01e4000300303000c0c1110600d81c0340018960b40c551070743c0c03025613000e0f42c1c40b0b800291044030040c080b1680d8551144403030340078544a081c8280e4981112134451610320076617211422400042441c8186901d143d03a03100e24640c0c2d100c0a2240800146008a800c5032a004011001810410070400076100c0c01d03c0c00250000100103103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 877712841 1250 877711591 877711619
    0x16020603090303011e030b160c0606060302341e060c0f030e010b0105190504080a0c0314031c020a050d0e1c09080703060b030708010e0102070b07030b0a0302150c0115 73
    0x48005d44440c54100000f480d04814507034000880d000e1004200f0070401d080d2103400800781c000b00024138143c3c01207000d07500755003d0400c2c0401c149018200a41040c9030402c8445030f403451a02081102d10f410300080e95842020410700c00e1811004080b42c215900c01056513040650311000c07800c04c858010106034180300b080608003050000380061207520b80040c00c588101021810640a2481a0081c45005900711401804020225140301d581424043c2c80500c060100326054420b0b01c03354640d443c000001c1e00c494002d80b12240e501c040c0c400003c10020341c490710000080c40000e000c91403401d95144a03483c440301d20140031f440b20002502c1240905180c5070201070510000601c2880468000a12241070303c1e0f006100041007103040000030b2506240342d104010300c1d030a12130407200c0b140b019005001d110344074200404550301c0300c820a40a4074a44a4400e400017040d0208102520304030303200a4105500e20501c40c078103071354100e0080c00d6070142076070703102209814a404c10115500b8452 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 877714091 1250 877712841 877712879
    0x5010308210f04020906012a0b0108060c181206070c05160e150301110301080a0308060f060a03240e010e060d02100309030e060c1b01030618021602060309030301 71
    0x1c0038503901d401c0018600082020740064014000345c00021010390041001940d035211214508030034407000043c0b601c62442d010000c0306c4c0c085000c0000102c3c0c0c03000040041c000c940d000629030030083c981119039441100b403040e031544140309258203100c0e1030f01401141e0080c5003682c0d80895081460074401d01d00b01c0c0c1c0100300010400c0120341003290740c0d6100c41d400d410048101006540c0ca52040010340581829a01e030506202c00100010b1a5207002507030220342e40c40f0b43c503202150f9942a040040e401c4000c1baa482c8c10030790811580c4d4116100b6441030007003603961038003800c2100380c0f02d98003804401660050000c4508082c018090200c612488943c880400c4541d0300e209e0080341d02180c0c1c007682c01c1842100341030b02c07010303270b07400300360045004001403134010b020503413607440c2070707028503030360800c0c000d015400005454602030254820700a034030907901d6544040da00b281c03a056024000758400c5c50030680e0840c0c0303003580e840103941e8040150301405903040150741365410010380014000360300c90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 877715341 1250 877714091 877714147
    0x2030301120f050307020301420605130f0b0a0206011e03082b0911092505040902070308060910082116120f021f050c0d05010308 57
    0x10040041420106007445180e51280e550a50210180790451031030040950003545542000c4d00d15a86890002e0500c561082041d10740414502104030101121427401d0601c10304030b000c440a020207030242d0001c3c28602c6418610304480b0340d483d40301c1443d02002d17130003800c1b0004000803a1a00da940c10031031103015003191103100c0707845060001d100e02c10172410300c401483c404000c62a180175a01c990390396034441009400c0790b01d01c5070042070404020041c001040740c2092425102a0007414400d0095100c3d0030501e2003001450b4103200c0329801d00c0da200c860702d420000c2c200004948812180094100148603440301c039440d003002803c12860150080c1180441250604200b01303940000908600c102c61aa10010b207108000040d1461441509450707141c1c48101c0c03041c1d8040040d080a0790302c0000c0c0030781e11503d29002100040786c407000983c201600f0302c010820540d581d04c1e40740d44a80d80002441036035a00e01074200c40d80740c0907204241d001381c4101801045c0208603840896034900d4034030000b8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 877716591 1250 877715341 877715347
    0x20a0f1a04050604060e0112050a2702220b060c0d020d0c031e0302040e100609090209090a0c0c0f0b06010e0f0d0b04022b02270408070807080d050a0c0203 68
    0x50b010414030700a034443c1c20b040008500c04040940d0080c1d41d1840a9404542d090000345400b0315140058544802c494035424140030740d16818070141c10040b15043e500414a11140d81c40294048285820110900c0c1d6155900d41c0412141c0da0a0006c028030316403a80640f00c08032460601904040e0000000c0c401c1c071800100d03900000b580301c0082030f0b00707140c041c0482d031050541c5d9901702c9c0240601d4100070000070300300062210104004010004603912551000b41c0071b40ca0b190f4440503806800784407a080008803000c12020845030b0020300c2c0d0740186140427440d01d2441e407030742c80440350842000c2c0c904000000501c0b03146d59010a881201540a8444e850804000004145091f030b10746800b40501d500400420b04650328400c81c40f074461000b400c0c51404032504507104080c40764441080340301c0c20b55406030607540c1007050070382d00380c070004004c4c405201e030307680d4407844242e030b018070403c035200e007000c01c001c1d00012031000140110300d01c510400a540c0c035210700044101c40080c82d6240c150340c801c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 877717841 1250 877716591 877716599
    0x816050c03150f070c1211030f0d02070219050f0d021309080304111801061b0c09020408010f0e0c060708070204050a0501060825111002030405151303050403021507020a0f1a04 77
    0x21b00b44421400d940e1030a142d011840c50350300350441c058118491214039000a1030340000c030315038000d00001070089030308614005400c100401401018820701c1d8009040c080b90702058074090f0070360300c0134500140400030540000320070b000485e03e506004441c03440380401800b0a0052141080c00842c205481000c079022880c00800110841482088104088550101c0c075091040c000803036015031100000c2e40050b102c1c85110040c0d0441d000c1c1001039840d18000c8800c2001c1400f411030129030345000340a0500440f810b101450b40049000e540040041003500016269845218422044007400290035410b08000400d88040a482c6030300d99240c0c480100400d00302508442e8540c60710b4207040c9030701c941610080d810007100c0070240070500e00c080200414804042080000104080c1402c1401e54504180380e003407172004400a000136a0602c0140010f0030a03584800d40420b01d41030391410954a98001030308240e540d08054441a84204100305824440584180c80001c141c002c03400c003030070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 877719091 1250 877717841 877717853
    0x4030c03260913025e03060b0a0b07061401050306090c0906011202131703040806040b0709080a0c031709090c1b190515040816050c03150f070c 63
    0x2003c075000f000c1e25400140401c1c541c03481c00075607461641410590400f8040c5148281ca10343d074025840740c0800c6101c070407031068403082882c0d01000103603045c8664018119191500204444000950444000c0300041070342c0781c08c3ca02a1005034032031000407d88d03000304a0310faa10b519041c6d0001d03000e0b6000c0c00c2400100310707010031103154040c8241c0300082c1710354a40e0700407504541c0a0002d4400b5034030014507005c0c80e01c959441282a5040c404446015112000c41c0b03554030320591042c460381e604141f0200700003412015030b241d04000036142052150341c440000301d04080e0641742c101c601e02811001003040060049920202e0000316014a080550040125010318401840e5400c1d05000140d00758030741c136910b02084030b40031030741044494070208112142c9071011200001e80d41407180070840c0008003c0c0070300741d43c81241d000148500b000c102408880c10340f42412001c40d128011140e500c3d25540701003103201084108115250b003d820015080041c41401500301c4040101007400b110125407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 877720341 1250 877719091 877719109
    0xe071106011e17011103040f05160311040c0203040911030f180703202e0521041403191b1e0c08030a210507090b0f0c1608010e060114010c0804030c032609 68
    0x900dd0f14081607114200008a0039440749c0d821045101c0d01e00140317a5214100c0d4006944513400d24103101c52981c90b864801081041e10356600e1480f40e108000910014062010300310000c1c3c100340399515058401c0001440b0140803001d610604040300e00408101c000000020904a166041107407814078250781e9200324001101e5807241740c200400c046820011108550b600c00b81488050380d4031142e035050704403c021500d6055900080403a1100805002c03901002025940d000076134001c02035840180c0c42c0e903042c50f220180c7c0c44e40f0784000000390012041c002071025101641e180e02074600210070444000036060807041d615454103080082164110074070900740c1d00e024141035200e41d840e01c0c40d8001440b6122881071503000300d00d0300c82c803448141c1070014240c40d0300100070700001081c100f482d40daa01091003461072003490b15408c103101e5400b5451020140d030103040d11514240e03ca440f0a0301001c01684100d48040716640c0d20400041c500108040651030043e03203030300d85200a000544089 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 877721591 1250 877720341 877720373
    0x80d0c0e030304151b0b061002422703070c0902030c040816030308090d08070e13110304050c06040617060a0e071106011e17011103040f051603 63
    0xb0030f00d182d803180703441e02400c96540400e8030100d407141c0c10102e900d4175140c4070401f0b8600c24000c0700448090760020340007140400c7d00c052030380b0400c05d41c100600450100c02502410b03401d43c03071304084484900301c4030b6107184a103d0f80b140d48000644004c5c80c0c6081d0040b402d19100148184c10a00071140010510070f004030850300070740e40240e225165940c512400d0b22556100509502c90b4160703141070040d8a412207000c880c003030346a00589503180c03060b140e03c4502c2d111020b0300052924001410950147c00724150212000d46003840e0011040718032402c841542c81000c1980e2004000c000400c507041000200e11241940c2c0c483c20180303080d9010700350b940040980039100402c840021001d80300e80180c50018544020107800d80c0c200414060200144050b500b5030b540107600001c100011298000c1161401e10300c1102402450a000245c00584010107a50071303541750808102a210303048042d601480c0140f9851114110b285080c03071921000e0900c0046c44812007a042002ca891500d40114603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 877722841 1250 877721591 877721609
    0xf05011a0a082a03010b0a03110a0e06220e0d020609060a0c081b1606020a1101060503070909020301060522230415111b0c04090b0c160b04080d0c0e030304 68
    0x4080d0f4900002e024084c44600c6070740125040d00e000040c800241c1c44124a200d00b600e10220a54640401e400c1300340c011160b56412514030b200300200340030000c4d00c0c0e400b08110100c001418040f8420894146114814010010381c084810b100c24030383e051020b66007003032140310308100701000301e01f000d0031f111801042c03030441000c168207606504d1406000c581c00c200e4101e0740500500f40074500b040c02500000c0c000000108003170308404610f401445420280c4000600030326101d450060f10b01d014000b00b8000b26095501c5290000d25601c458514809440b000025000081154010301d4100c5100c81c442802a0b040b01461f500b0300e119144846801035000301101d04411100c0500502404e5540400310700e51100150a0b1402001a01d8000e245040c540984910b0440002000203503a114000901246410300c041201102c2072001080c100042111700450074070b40f5240d074411402d0484043c1c03001100091079002440240c458900b0151050422059840b602c0d00481e50340d0081d070050b104a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 877724091 1250 877722841 877722913
    0x150b070c05190b04030606080d0908121602060708041a130311270603071406090d021f02010506090901050712110906040b0405010e030619090f05011a0a08 68
    0x1900e0b00e401c01c01d201401d0800366255482d42d41c2e15140000340701510031702030079026090340034030440e1103a820700044850f05401802410b0307039900b1040031a40141e000030007148807101408016201d0340c2c0901600c03800f035a1003e40f6949031460340d082032003140102603040d420030820418400c81404150060b65009200c4410b1001080b012a00304245694401c040c440d4081101502c10580305041d4420a410b8064481c81030355680d24080703001d03140b01e076181e2103070302480781000c02d003007981c50741e40303024001031485942400030f05254952203c403100c1e80006075129002c01149003080705005030001c41010080000d860092001014030000c3e003401900c8949880c2400c60711503610050301c81064000706107641e03a80e0b03151100f040303642c06480348902040d201c3c4108601d503d004217010b0f2244808035082140c81071210002d40080c171500104444a4400ca10008041402440b5a203180040f002203090755110b02d8041180d815015440303040c042e48030b400c246a01c01132044000711102c400f8801d51034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 877725341 1250 877724091 877724119
    0x50c0a17090603100303090512030412020a15082710050702011b0206011719080a021c0c0204050109020c0a030e0315040b040308070302030412080907090e01150b070c05 74
    0x18070311803414081d50044011082c09241e051100003a012248651910040c160390b41d01880303031912554075013241c0c58009200400441038401080c486403403004103030b8124103440704035424024079810510300c00200242e0820800711135207003000e00c90740c1001400200a040c9020010340da08041c19080c0001c0d41c8880c08110614000d40013060425100340b03248002c40c090b42002543c1d0030b402d214148d252110101c2d400d0f611000440c40d04d140d80c0c94084041d54841d4180c641d00f00300e60108440004511594824030100c100582040c804080ca0355211040318115004001c290b40707060b041001d805104003c0300b80740000000e81c001c0200d0740b41c1031003440d003441e0b000040c0c04c0982c0c003055024012040003c020400c0120340d80348e0f20551194960308801c0e10796400490480c00b0440c0c0c0203240b0b80d411805ca14030140194480340e4094602000c846d04991540e07000000d03070340c240c5087c1503140c0d1680280300c4a15100c2403490041e00c41b10b000740c3d0400400e40c0b0b0744100709116110346402290a61002d0b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 877726591 1250 877725341 877725383
    0x3032d13030c0c17120304020d02010c0c0905013c120503040503060a051e0705070204110d09080a0210090b1b1e04140603060120010b0a0f050a06050c0a 67
    0x201d50390780240c0394100c1a83d0340c0e0b804e11140704503043c407000540610300c014030b2103032413402c1600c1c0120b07005402c4c9801c01e503a0b41e0041d2000c0d140480240c0341e0081d07080001540740b101c1c1c0076050180402415002c10900e030180e840031003040001116000320200e20603190000c121140074404c0f20300b09225260380072141e007001d070708521841d081a43c00d030040713508100700d1a43c039802c0b09005031102040c1148403015102e02840200b015921400007920401000c0c0140c0381c0740e042002040c0350312079007a00d06103454007100100c03541003404032040500031424101c00d94052044160701e240c030120501040b001581c484c1300c44030000f0004a1540103165054145c4c50552054403404400032001c180b5411f414040e9200642052040b00820f10f00710b12080308a003001d0055034080c0c00180c603100d0714120208035900f58500c451021061a40d030305e8801e9445a0b817401c0303c00000f400d00d11440307001c0c6d506110900240b000203030804c00c1401070802460180c1d6000203084074400e82c01404030307082c01d000708581c0307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 877727841 1250 877726591 877726607
    0x111010c0e090615130f050a030f06020a092606241e0324070e030615030f0304173a020a0b0f07030623040b18010803032d1303 56
    0x86449011410400342c402d28142401a6455441c0c6d05020716500c070200302840c030650000402c2440c0341c0c06000d0000c0c6854001e01000030b50340c2015134250362103e07454a4510102c0c00001400034020b2641c150b200b8042c068290001d5a502014050031800d0399811000b01030051441d00030414400d0502050700e0054440160700c01c020140d4031001040f05514694148120000e1000094007021070505e60140c0d03102e450000028015008907551080c041400c0030134002e0164060080c000d9180d085182400240003500700c0c1c03034401c030001d204142414a0201180050881109903137900344025945290512640601c1807480550101c0301208a080c46c13040900101240b042000b848141250001503511403811942e0401243c0d0355000c1c981000310301542d1b044840d040d103141030405800c06400c0582c1030000070702201002c248954440382401070990002c40350740c102000f80040801c015070604000e903800303200b0a0030101030007040c80c03025402401070f602c004c256891013020940a0051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 877729091 1250 877727841 877727869
    0x1b08130506090a0302010e060f060d0510051f05190b2101260a0309090c050f0703020706110d0f120f0906050106170c250c140111010c0e0906 62
    0x2620080e0510140c480e03610143d5020440265007000010070401900281c41c5201d034410241d4904a61520005d0000c0700040c00c1065625000d689071010856440c0d00480380296001c5003146ea03a01c103a42cac040d0141200d680c009511070016542805c400e61030240303514007500c0c40070304504c0d6039040580c220003140000c081c1982e2071141d00000000d81050124150040e400750465a5074100780c82c0009076112003041d0f4000380880c0c044074051110309007583c1302c0210302416061043c035121030a10031a0302904603000890040e40180c00500201364032503c00e1307105000e940000e0203501c0203104080c1045074a07442c04030412a07200c1e20003609040c41d0304801c014048103101000703000d515050450117401e00f40a82c03804a0030300e40d403c0d01c400381801400ca00c16968001d405042c1403849800707288220004441001810140c072050010403042c805110007408440c66240240f16640000741004d54035000c101c400b6458026801d00d03080d003100b204450800c3c02c480c603454550341e403400100840d4040d95 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 877730341 1250 877729091 877729093
    0xa0902090d0506040f060c0f0918020c01110306040c08011a03070c291803180d02090c130b0f07260c15010b07080409020d0920040b041b081305 63
    0x401d0100380904100400701e81d5004401c1800000309080041c1c3d00614000741103000550800c2701003003150181e8036264a0398020a03005850421074800690a40303c0942c0250400680081070201c145030034810f203141d04000c0e003400c4000d50324141c4442c069000700b091100000b0f80000004135034521900b0b03500c81c0300750b22042030352021401f8014071352144141c160380b1071000381400108510b80c481301e9103402c1d0030220f500254640309000030211410150303030801580101c107046d202001a607545000a1180c0703641c0c041d46444010405400d00a582140e1266801030020480d202043e1440b074121900d20340c0000f41c0520228511000c056005007588004030280004a03c080d9203800203d01c5802c0d20007131103d043c0f801c0e626604003060a12601400501d481c0d4100806c009420058000d488500104440001c0106554980c401c20404174500140b0f0f5400f030880304105480d042c401e8624491082d03c00704490100407060320030400d1400c10348014041c080700002c02c0206450001c04415134031038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 877731591 1250 877730341 877730353
    0x60f02271005070f0515011d0601030605130e0c04020f0a02160321020f160f080c0105033114150c030a0b060c030c010b010801090c0e0f0d12020d090f050a0902090d05 73
    0x415802d044e52300d070010400d418507034408200250301ca400745800b9900f008000c2e105403140e110b01500108888407800380c09024a400b083c002d5525807000d000c1544a000141d50340c0d0101d1350000f410485405251244100000e83c00d01c00f103034a81c400d0421801380701c002c00740c2c00707501481c00760314145c40f0070804000342c1304d9a21a001040904400310003101c426840c8400d80545888070b071600c400c90154036500003002800002d49000750f0401d20660500110503250461a05417a07500d40220a40000c0d42c48080aa000008004c001c01c1201041d502080001d2010700f04120703801050302c000b038104400305440d20348020003030ba2210100d4600c80c41d142d080703030342d504904035005000c1c02204000502260241c00002984c49481c00780c56030143c2150b44040140414804005548950b0b40c40542c114608052280003c1d0f1342c8000c82c80c0812403a0010403501d5600d04c0b00600d01c000c203801c494a5090b40d45000c110a0b200d254045081d15442c5c900903850350300302e8021a200b841581c3c0050090300c900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 877732841 1250 877731591 877731599
    0x1e01090c06051908091b0a0e040605040b06030c0a15021018121b030f0509032a01020705030a08030a020712051c06050913060f02271005070f051501 65
    0x640140f0055a580f0b0030b0030444821458291603450b0202c0d6400e00b42e40000070444c1103071000c148090300445004252070441c131740b40c0d907e8900380381089500b191840d60b0742c828003041c406084c1c6060f03480704040340281b4880c000d100104000100301c6c81480e144c1c078032662840101e13170300900803d4001081c44408004030700041c501180360501542c0159920804032083c1c511071407182c02c020450441803180d5540c4d0f074900f039404840c01d01401043d54204001841101c115075010b000c50603000404d622010140303000140f6480c1c581d03038200880d07415907200704d1040010342c401107408040142c200c11011740b296200004800a8031440c83c1c000c0003103101c100902c00090300803020344000000d8108290444600480b51021980c40340140790744102c2e124000350b40c150780b41807a900124462000030802c01f5400d05640c0c10382c4c10003041c500c16507413040304580020310310458407110704d07001303c2e031013800f91480c000090f143d8800c0800180c03d41201a9001086c020100152140800004040d440941c2c0d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 877734091 1250 877732841 877732847
    0x18250c0b0903040e040b041502030903130e091015030516030302010b010305040b0a090215191803030e010507080c120a03050a11180a0521070906081e01090c06 70
    0x90010219080d1018001040c0071040010035541900c5007184c41d0603242d100c0d0307111540a60002401180c03032582c40502e0343c0d410034581c0095401040b40340011900d50040c810511082e0005801030f1088940d10010401e04000c001803143c110a0240350000d0b00500011441e032601d1025000944284200c4d488226046000d40c0201c013141e0003a0300030003182c400701c001101500c20607240900700341c4040020440d070030420340c848200180300500f1210300c0500e0301503145164009503100003850280d08002d484568001e5030007da80700d0b031401c48906050842d83c014000112900c900ca04108001c01d40c01c04000504044070305107820042104c9010701141c0b0f0704103c5038450500340000038208000b1a16004042c052650707654940c16016003408610002090301d0b00104940c42e500405141001030035440f07449074084030315030000006010362030325003030680b51540c240e100303a0340503141640400c0340540c0441d2944140c61038034040e501441070700005501401100502030032600c02210000365840d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 877735341 1250 877734091 877734107
    0x721050d022a0d090915060e01021614040c03020903060a0902190803180315063309180f0403050a03060b130503190809060304050f060a0b0a141825 65
    0xd41d55810500546880150b070540301410504850b805407240b087c01001d000310520303d101401841114030005001c2071404440000b0341c00700b0703904070f141a101155810f060007010380c509800e040a6240007040404607039106001041d069540b950389141c8021540c5004503c254035070008145d145058441c440c507500ca500015090500300d503e00483c402da402c0c003080400050320018444055952070109100071540e41c2c038900f200080003501012110f0f044a144483e8001c200a01e02d51625000014410000f000c40ca420308803580d100108a070b9450034a00300c0b64490b41c50300c1e0081e00c8050f854402c0d0003600c041d40003503028a030041651b0b04400c0c0484080d40480d00100c084590000040440c0600041e0ba03000181003000208211101400d16a0085802510850484002c2000e10143c2030400c00c065440d90707801601c40b00028020b00e0a11000c00c040c09100c0000c01100b00326000007441d14282c030310a80d030140b1f00280010305c4050321200031404190f0084c40110a4400ea0200400380d41c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 877736591 1250 877735341 877735363
    0x111e0f0d0506100c0812060102010e10060315020306060403120512131109071706030a020303071b0e0c16050c03010e030405040621150207170721050d022a 68
    0xa09040007060f0f9210f14410650300340c200380c40707034035000b07410811502010000703100c1410342d17407a00e1564144000400407a10080c032010030008001d819450b18510741060003242008460041c814480c881d030b19041240d0440e40e0011840168035807000060f5010301030005402d900c1c4100e4000c00c06c00c030516040b0451194815818421610411401c00c809101c043c0d60038800a01001c00e42c03008502608030789508102c0040c01c0341c180401c1e90b40040d140d54800c6804654202100010364140c5030300403504405803c41000c081094504811211100d018585d00044075031b00402007a828442c0522540032240d05c003800034015415401314030b541d2523105204460155160035000036071200943e45d0800c043c2c0390241130704244032030764491114100f200c0409100f42c1e90700b00444ca001411500480020714800f03011551641101d0500d1807403110780c504903401c41d501c040c0c805c0007025030250483d0f00c184041c0b0f000603165005000e88bc668403284000030b030f0b21070180d620860b083c1c000018081140c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 877737841 1250 877736591 877736599
    0x3010308120708040302030301120c08030705010b010f11100b0103020c0d0e1302030907052116061d0f09101d060a0f0305030a140f0d0603030801060201111e0f0d0506 73
    0x3580702d9000c01c031000001110b001d03006800c244014000d011500720038070001e034040d00c0800c44480d00d4110b91403c41e0301000c4211102da540c2c0e900360f8601d5030440040080d40303201e400c040500851070500c8075200d0000300c444842c41d643d02c2040c0301031a07010f541540c0c2d41003080c1e0100e81d46c0c00100700e400380c030014070f4902d04ca00c2044505102801c1c5412402182c1c8140b00460141620394942000c3c0b103424031080d00c00e044480d070030b42c9505290460070800710140c40d001580b052107040c90035030042c0c070308413040006108801820301100c030540c46401c240243c01d84140c0340349016a032145642048110355030030038014203d5070b1100d14070304206c000300b9600038841190b40304025503a800d1001c498290610006105800038071110f00300034010f0074042200400c08007864a002041c2c0c4902c105940451a660700040d13880c0001d20615a01000190240c03c540c002040481e21881d6501858003460209940e00079501075002044080042a928a28202420940c0b00c0300f0002303040000c0c0804843c3d103402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 877739091 1250 877737841 877737877
    0xa12091103072106050402010203071208101502030a180518041106030403020a060f0b040e0303090601080c0a1a070b0112150614120a020a08012018120c0603010308 72
    0x10740c401c0504509000f070f031015000c002c06a074560701c24010b000020400d0b41540402d05c0f42c840402c8800c0d42c04000c0707007210384d1000510328002d08120312191158102d4524041e0180042d60b0321500003088640548003814008500c80b048800f100c0f4042da0b03500000d800031038281540c170990040481c114011480b4480540e50701c9150b03014480c07980400c91f000740060344220110000f1508a074003640020041e104082030780c03140304004c54281ca540d4580c0d22040e45c800010011543c0060010f24094407a8401034045416210001512000107001e46038400052840b40804445444122015264019225006507030f4400c04141034001c442c10036545028142d00d4030b1026034044c4100c40c143c981c00c00c0c0c2080071a04c403005120080c02a1800d04c102c9104110075840541e503203d140f500100111000411480023402d1051400111441140700b840028800c0e00700c4101d02055450b280c52003503c01003140b182c020b06551404a0542075503400c06800000172040c00301c6540104802030603800c02110b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 877740341 1250 877739091 877739099
    0x503010e0f0f03090a0501080a0b2707090e01051009180b18010f09180506160e18010902130e010b07060b010e0d06021308010e01050a23010303050a1209110307 70
    0x2d103038414103041341d6100003a0041803080e98054003003243c10091454000039841070300804501e00c0c1d1001c2100d03d084100c56294450050104908180c3c003811074900030305c0c204e24004200d148400c1c18002c0c20700c02d20361344042442440c800d001c044000c16000d120388841d0140c100307905000b0074024940d14020700006011490046200c03103682d0427100c0c2a40030b00700700d42c45c0c035100384000c01c0d0744103c4641c1c0041c0c414058001c81e0040080c0d40c0680700c003070000b051a0455040140000c1101141c0501034000c540d80390054505080361941116038903180036a850100344010410745695030071045404203400c00110f00381d040c181c060602c440c0308070000c000381d08031000155420a0190780c0c140d403102c1c00342812000903402d07801500540602140d084d51141d00c0d561b4403804e4514021640c201071307658200b007050510084c019100744030140500f90050050b1900720346c0720350304140030250501c01c00054055110b0303c2801c80b054908803046c400c1124114a14100110380c596001f03c03486803042217001b107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 877741591 1250 877740341 877740343
    0x301150e0c0c10050604020d020c011e06030201021c0c0c0312020d110303060d0311010609050a15031203020307090b0307020f0606060a0c030e420a09050103150503010e0f0f 76
    0x965490b502c4005000e403c10100e01c0e140036000041c034a6420940a0006003039100d4540054078203030704824004140c0c1b55030b41d000c5401201400c1551030403542130503000c1026036008034550545803081d60701c0345400240304000341c54070055984010501390071100000f0074020300d2403143c0b036455215070a98000e2204081c085903111020058000d583e001000071074014030b452080760001c07600c80d0170060441540100d4990071500250b0114841c41d4444c0200480d026162103111034564801d03941c45812810f54035030010501221014009256001022030016402545150018030f8000300456a03441d28060080d00c0d50360460074002188511408100d1504d40308040d50134810f61643c2d54880f0b0740d4103441c11141d000e1100c00468001860201050014204590304003084014201108500c20300502d05401410300186005015000380031b852446503005103c242200c5003481e001c02d815807a4503c3c002c0d0304000b42c0c407240e4150b1034801c0b0405c7c2800c021614041c0303206000c080c0d44a0700c0304480c1c02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 877742841 1250 877741591 877741597
    0x110303090f010f030e060c09010e06030f010501180f270c05090d1a15031908040b030c0d0f05070f02031315020709020f2a0705060d0b0301150e0c 64
    0x16950100c0014405051544070750880400340546150201d0382034250310021b801c10a050311100b451450004240d150355030018807240703501c5030a445044c81d40c07400d4402500700700e40601441c2d040040c03000881c1411310b41269040080c200d17401100594941d01d00002c0304c04c3c210490782001c400d070b80c801c50300244401480b1b05080c0e00b103141c507441d2600320204c04000c5800440f03081262807003910383d450560814240022071140da0300b1000e01c0740c0d002110702010705c1d02503000c01042046007030703008640026165509540491700c2808126449031502e66a80155001c0c00030f158510b5454500800c58a0205400050140c4290b84440c40d0700088080104c3c0c03648075404100c682e40040410800c0030071101e03459410098a1072055854042d10303540468281e034459185014411004145c006884204440c00f00100000340302e00703100300c0945442c2980750a02481100d00c038000218181d90f0070611504002105403004008104900741c0045094418410b40110701000c07180701d0000b60011011011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 877744091 1250 877742841 877742857
    0xf01170c0312090102250f0e10210f0606030615080615030106030b01080d0f260603010b062206030207020901031b03020d06020c0d050f070f140703030c110303 70
    0x7800300040d0308140d07440c50707900030207920f8111b202c0c0c0702c407104070f8000380510706800e5401a90911202c910700928080540300d56008514441c1a100900240345c00c180e2941080701c40c2c2c05402c0d48904420080321884054a0308090300f407580f034100500421266901c03c0c07094900c01c000070000c000101c00c0282c1615a14002c14100e640080d01094000d1000050075240107001000070400c50344035070350100816000c1c5c0c0720415540c0004521260300c2d03000600001c40d141d2030324100040010250003540382000007200d00300795030303580d1021540c84d440c04e402200102e1005400d440c0e0380e440c22043c142d85c0c0514440d240000d51603844022686d03e2107402121007494009000d0800b90742561102411103951510303103620320503107100c0003005032514000c0700f81c050702518006880d1503c0740002d41c14840300310321700b50400400708a115180c01010040c0c80b40c03140c0154030100c4042403450070328200c8001c25a0060f00e03102da642c00004042d0b00001c8900704032b108020300d0704011000402d0503940e001d400c4c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 877745341 1250 877744091 877744093
    0x60d0b070f20030901050304141e580e03010509060c07080d0609050f09010e07060207140f0a0801090c140a060f1e020717030708030a0e0f01050f01170c03 68
    0xb8502151b04c107402840d005400351089890001c041e60314039141100300852440241000040e0300920b01084c04980f50580010092a4042100704403020151004420340c03016881141451140300c0c844180310390011002440945031606854006042e01c1c204590203803103582041c00280c0c803000700bc40e02c64050b030718448025041c180c45607249581c50300116001072015075600c000080c2e00ca568000d66001701501c21400000e4100301d81407900b5648500c0340c1e14007a80c000b000402005a000428408a800c54180b00c11071010343c0c40000d010065240e031696000c0403001022907108411751142075800c0c132945028804139502c1e008000022200c00e54a98001c154581c200042d50285e4080c10b20114140f0b0034404091001542c50b003103090b20b407e0000180d000d40010b200d00643d0070b80c80018110039400440c03d0182c80d50300c205052100600c030350700103038540300d4180d04103404100d4a5804036019000740400d2424902c00c040a2009200e04403440c001001a601c08410200e04481480c038050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 877746591 1250 877745341 877745347
    0x2609060711060d1814030a0f0e01020a050a05061f030c0e061c0506040203010507020a0c030609030e09070f0e040618053c07030c0801030b060d0b070f2003 68
    0xe101c1c100c40303071001036640360411400c0083d00c0c1c00c8803d03449890008003050385060250392160800e090b981180c62900705441e0b004000b00c18801d40c2100b034a05903140c062034072444420034040100d003031041d03d013002000351154803038407000c2280c042000c5d44140aa041000d201c1d200000c00c41c1c24a440d2840058130f26003000006000003402c0c266099400360000e0301c0d0202269041c000e040d142c20002d5001d49180d040301c000d2001f14942030007416041a81e03803004190740d00b501c0e21072001e0303040c152100801c459030f00d222501c10140074221904007104024080d004c00e103840d0300050700e0348c038000e59a40b002900945000e01580307490720620701034480340c03211181c90040c454000001008054001c0f11011070351428909206010485101051041c1c2d51030880d400c1e0b65100c1080c040360140c650130625081403001e10383e060f44100a60304590700a0351406882c0c4401021484e441300300100a01541c1210701005806a000085000804220354030504d20f00303c6195000f480642508a02040d82c00c20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 877747841 1250 877746591 877746593
    0x70507080a0306050d0602090906151c0905190c0b120118240801060906140105070305070f060b010e01020d0914011404081609021201090905030c060426090607 70
    0x42001d0003001419040005159072070380000b0f072019001001c1250529000100000300381005100c5d140c000b030046d642000c804502104801484c000d00403079101c2c5082d420104401c00c4511b400c802c02094020040d0b0fa0010f800c0b0700240010f644140c000d5481d000e0f182e00c0000c1e55003d160031164010301c584034600c180e900300701074401c0e411144801000219100d1160b1800c0c40c0c1b0b03012901000600c0c5204001c5000d1400c0046400c0d5142e0342c0c0000310311858038604100c0e10f64141000b02d081482480c1c01543c8400724039064800340189103000c1c0004000320419010007244e0740c8480071410098840890b8211100012640e07441c6208104000030f8207004100909152900010000441410150344100c80c5604920498216038044000e90f0b01c4448a15905000340000d0b601415141005504d08951000001d80c284010701c01ca8000ca5550316112040c8413051094a2940c11540103646482c00e140c2440020b0010729205500440c00702a640702d039820b82e56040f24900c2d44054129401e249207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 877749091 1250 877747841 877747853
    0x106090311040b0d0507171908120712090b1005061908060a03020411040f06020f2a120607030f09030801030807030302040f1203030b0604140d052a030c09070507 71
    0x303c0c5000c079801407800c3d005840025824050040a4403002070f06e8031843c0060040c182c41c040900c50001d080703170036004168011071100000c580f185907404e0946e03601922401c5c0f08460207501c404207009507d2078203180d24100411011110300610b0686000a0301ca40c0f10002c2050901c140c29401d074034000c001150800c032600403400554801001440c5c200001e650303801041c19110600e401c00c152980001e4188100c006140c4001c0181040d071005022000c15901f0b00d40c0d881c1941040008103a05d10041c052074031440c030b1510078680300064124618000c001e03410300c0ea99517090318403002203820b12454036440c00b4a03110b00c8a08982590392607060740d183d0b4840c281c45503c0004c0036020160200f00205002851403e07250040107600d14541c80040e09050050803200e85802c401e11410b403c00003081010150660042c6075507044811420491080c40d105181c0a0b01e6980c400d10100301921034541da15421800ca02c048800340c0640f00395050b080104000d0503412104c078000b0810500c00d44010900c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 877750341 1250 877749091 877749101
    0xa020a0c0f1115030108071e0e100906080a02010e2d1302030126030a08010905060d060614010311030f13050a05011814010605060a050d090803100509010609031104 72
    0x401485080e040c1c2c815503000c01d4142040301e82c0c032214000000300400c4284c02c100900790080c50120110150101d6411020329400b039248904d4214a40d501d0104118060726240b00c8000c29102c0b204011156171110b042c4c0d2203014102040c2d000c41e88000c04540c49040c000c02e9800e0040d40b44000303010000c5000301c1070040c0040082000d402c555070800300d61481c2c505100540c0a02800c1c1c480782c90401b08100e4078060817464203104c0445030401e22a50903a2600550228107486550602003000d0340c2d00d0012840081da400d001402050a101c00002c4121100c00d120b04081400c0c1c0c1c05001d8802220705500c0b851106a814001d100136850014540c40341102001c0c0042c0e1003072054562010030382d2100303070a60b00b05030441100c0b0b58000c4c0b10542044a003d40302c80c182c0c0c00b0f0500030300617580381a001a40c04d015410700c0f601401400520341507000c10310341c08042d4203503000c059546c030b078103103800b800580b0441405124090312444002082140c01200d0403021698000d0002079910004024000642 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 877751591 1250 877750341 877750343
    0x100c03060b070c03050f01020c06061507020307090c0e0604140d030c080f0414010f0f081e1303030b0a030f020d08040b03090c09161725020a02090a020a0c0f 69
    0x5999410040740106058009014042c000c80440c0c1d4058110f0810038249040c0d694000700300c0c2c1c4108400c40c040d8030301084071b40c0e01c50402c81d02c18403525400301c28800c2d54421a00000d505000d00303035003c14041c3d41e96101c2c8410800070754405a02c50240d000340211885a80915a444049111800b041d4070303180c0070030440d00e8420301d032041e26004180d6980314640c00c140c2080b021003001050034481d100209180300300007002407a110f0269050f5a5000d0442e4503c1c071110001c0001c10b40000300c5504140214a500e1200d000178070442e8980b60460503030b80c101030182100046d091420004942c81c02c4210034013541c0d0046011000c8550715070804c17120007040c03101199541418400040c100c96101d0240d0b105e281c603080034117940c8082d941000ba900c900204081015003407c5030000400ea80199120b140c000400e590850f142c031604420002e20b103c60070b0441c00e0170f03208415072440c60342c04120f950303595100742e41c450800d032644a40d04042c2d0040072084000904c01c681c0c0200400c003491603001c1c1207 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 877752841 1250 877751591 877751597
    0x1050904050a05270a1e1a09010c05040e071103190c0c0501030c0207060e041103010602060a0b0a0803160807171209060f160c050723030106080a0807060e0d270305100c 74
    0x140b0b1b1907075075080c204940c0101c803030700a0418508104003208280644942c0c3c48543c50294641814a228001400000f401c2d2400704004810141c2d0069401c00403075180007441403044100a070f41541c01480410038003821107080c07044e0724001481354042d00840540b00400d070040c007145800c094040b2050166000819407141d01ca20140d032844041c0801503000c0d201582c0030309584d01d400d0326031000780c910181e401030107008401001c101d00b00c0084141c0b800c3c501c80e41e280d820f03080c00905100d00745011380d20020301881c180c803031030070007084054000340261000c1280d411400d44d03c0303803c1281c40d50360844082c18140456000241d01e40160200040703c41c4140c00c2000714458141c07511482d0480303e0300b0a0300c40f0440a0f5410f47c00340d6140c0902c10440000710024401182009182602c4114040d070003000300c140443c240d000c0043d03075040030000162400480344a500c070f650700100703034540f80c20707a265008014003020844104581c0d030000990350030030010801000207400080062144980c92020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 877754091 1250 877752841 877752893
    0x40c02060f040c05130c1b080307050711100e1003090309050f03010f0c02101109180402060d05090a1a0708010510020106050a081b0121050601050904050a05270a 71
    0x403654030036562141401740e010b000100c091a030b510242420900840d01c030360700c0e1042c0c254100016108011290300002c945000c03078848845181000b8010701e101a2a9400700301c6e05002c00c1c9180e808025111000c804235440c000c04c0641441c29030486040c960f010307002881030310043c082818007011200103d08040d0000590340ca01401e00005ca800c0000040010380081e00150200a9140640b02c4000003030440c1501c1c0a01d03610000c2e00304202c1c0d08040026500c2c55000806540c0c64500351031390600110350502c803a02e04444038580700c00921804a400d040518031038014501d442c1c0c1000d1141030191141c0c0c09503404e20040041d840300419400d000c541d20342e400420b07544c41c0c02e0b030410010b0051400902c0201d075000c00004403c04280d000034104130341584d84669a2400285201003829100360000f000e0301c80c0720049800c1d00c1889a0f5a4102c3c3c10300d010f200101c03100d613000a11408855058803c2c0c40460080030b01c4c8a0034180c0048400e9110314107010102e41e000b0075000d6407088201103444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 877755341 1250 877754091 877754099
    0x80c190c0f111306060e040f02040e010f0315050103262205090c03060a0b090a26071a090910080d05031b210910110901020c040c02060f040c 62
    0x304140ea0444112030a20b49078068002d24100340c05110444a02d41505104003400c142c402410380c080d25144611454550141886604207035044801500d030b040008a03030340d0385401d40e103070292880344000c882500504030607020b070040c10b101c1c6a0690303501600d105400d0303910ac2c140c1203d04046c0c448200300107004021a5000300c22008007544001100100142081d10f450100104103000805090300c071841001005402e98805034228251140c1001c03060300c03020150041180c01c445901302c0b20b25880c00022818041d8243d82c41e4400c8103411170b04540c0e0301c1e6160344c4001101e948040405085003418027040f00c84d85004001c2c1580034045100b5000d0140d40e4801c841d10309110240301401142000040c003a4400700c19840b401c03540041c004c620300d0082c0c0d895017104020842201101d60000207c081280b140007440300400c0580c4e005000d0251035210040707100d0316440400c4841c00b600c52141e83e220942420b0042c0b00f1100745540107051542d0301c000c100d1108150091040390141803080b004a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 877756591 1250 877755341 877755353
    0x10806180a091e02010e09130602030a0b120a050709110705030304081207170726093706021b1c1407051c02011d0f060106080c190c 58
    0xa4401c000452020448207001e08000441d544000c2c94150503400c051a10005170340c00030300800502c1425241070b2078a6903408000c40c2c9038802c8800091001d800003084c0000000150060340400c0c07030031200d00050b00301c2521615640c24020000520a0f000044108483d07410703680065140000005190f150014a40e2520b04552040301c00710386042000c10f9004900a014441030381c06216418642020088d0519401940c64020b00035030400907002905580c0b000d4800283c0d98110070084550141d0900b8100140c944100540315280140201a45201e000041e4501d00178065202c000680410494440402075400300d1250345c0b058160313039000501864100034241c4403c18411102c10014403150009190304140d100d0210400805d0100c0000705601143c14501885803500b641c00413a01c0c1036003640500035414801c505000801640506020040741c0b802c000c1c6241400d4541c16078890300d09403404202a90120f9910350f042c4140310382c80c1d051012171400300741d20b420030002c48080740d654a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 877757841 1250 877756591 877756639
    0x30606040f0308181002030706090f0f21020d09121703040305071a15240a0306080601050307080a06020a03021224040c0e0904211d010903030503010302010806 70
    0x22503504030f00065120141d48074002241240c0800c850441620a822100a40d03e01070088058001a80c408103601001100f00c1c00b0001c0540c08031200c00c068107030742401c032400b000b86458920b0b00e41a000700c2c003c26504c045840c4043c0c103c10f4885d01030b11410034841c0300f03c07400c03500c40071503504c1c1d8800c40514800e2a004042c42c800d501c2a80c9955581d4a1450545020003028131008610000142408401d803280c0034242082d220503074000302d03071205000c0d401c5040300c070880e5a095400c50008444800a030f0540020090b202c4482c00c403240c47c0d0341c4606041e81c414051144030641e0b08034030302c1e010000350709800a140185040c80d0250800542090407501d40c1d00a480d500e1840c9900040c45140070050311541c030400d1021a410009004803c801805002000c115180b04414000c00281042031000c442d060449402900085202c000600035017122480707229010400180410420f0941c826404031064940c5543c07150300396460f41c0e0041d50661406000e00343d002008403000c400440e01200c43d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 877759091 1250 877757841 877757843
    0x6070810051e0406080304150905040605130504110622080c060f0a0504080105070e0f010305041713030807060b09100b07140109140304060306050103022104050a0506130b060414060402030606040f03 87
    0x2000023011540c070090051480f0f0ba002da40240e040180400a82da5042031059081c01601008669940e0300d2520001d125401c10070680c1c001c0300496186070309800f405012003e0004044030030141c41c2c6810086e0b5076200340440c42a40050301700580500110800081c001c40044d6040c028282505c40049a0a540b01290107800280a99000600b10f02d4903d8840030a000217080400241c00d154440d1079070039140061541002500082e5040c24030544000311000b503030810480d40d00d0300c01034900600038240070440c0ca4400c51310034000c11030700c00c00200f988084800714594107140040c1c07903886800081d0507403107400042d581c5c1c90b480030104458600c3d03141040c04810203141e03203904009010303049419075000541014070512441e003903540b542003903012000450880d02c40075661445c100d40740c4034038190011300702e0156a0030b002c2140000341100345068440d016440c0c3ca40d481c00c090004035010746440001d600c0010001c141c2c0d9003095401141c01080c003030f12403841c2a44500c0c00910510310340d40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 877760341 1250 877759091 877759109
    0x1050c07030c18050f090c010f18090f050601090b0306010e0a05220c02071406161505041505090a06090510020f0c06060d03050d0f0b04090506070810051e0406080304 73
    0x2a01d146030340c01c03403060325400f00120303034409106d040c0100595650485008080c0c1400200c8075004860303802207400300ca100074030041035980d0759240d560860190003820360111000b03082c2408a42d0960150204000340e800400d5002d086076194401110b96146046805030404660000426582c949115034440d10654854180502d200010144100c403071702c00a49045410603803080c030040810340410340301c03a0021207160f07881c1d108082c3c400340b030300c0d0201c04001d1030780c1c20950582494244a13005180700c0c5000e00071400340c2011424005060352000c072003076400c9800c11003655001400d0f90b0b220003031b00c0d4000c4044a07000d030407a210200480c0d01c5403282e518010303404101004120b40c1000710a600005c00c1d140c500c2901c0f060360740900b241c000d410304a50110348900600c4488440b0781d10502c50003c00910522481080381045911007000362a03050009091034002012001115010740803a01301500d80d12944180c2402c00c00100624812564010789a030310000d00340004002500217011480303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 877761591 1250 877760341 877760369
    0x2101080327102105010b2a01180b0121060e0a0506070c0b092d0c0315071805060a0e0415030b0603070e01030b180102120f0a060b090a0501050c07030c 66
    0x20003c2d01e01d080701100d03500039042c2800c005015410380c2c0000d4a26417045140452110f01040d490440b00c080424030004040d860b0500b400c0da00c581c8200c102031103900070404001c1690300d6040002c8184122200307040b9100c808070803580056159800002044000340590348100016600c150405409860007000103115540140c1882094404607411030390603402040d261987c95210044070581c80103559007841001f100d5000c00409100c2d80e0140c90005050b00d0110039110240b40020609036046000184a10310703550f442a21034103040156800101003e0415403281b03422a01840c40540d229042a160140401004442d5000030007441c42a1402404c3e844c10700e081c145011450352100010703400768030041021509100815410988288103c1d0540c1c13a98074426002e4810f558900d900c01d040b13001007240d030220b040e419030301910100209000c05d960340c2014915a0182c0e84000c1e61107508000300300050b40c007560040c0000310300b02e4141c54503603940f91124071100c8041e034003000c0c07180210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 877762841 1250 877761591 877761617
    0x3160801060e0f07050c160303050a032d0203100b0304050105090f06160c1406160207080c09190603020d061e05160c150e03210108032710 61
    0xc1c06014050081544a0101803615200e528006200075005000340a80000d000801c6401446407000140001c0381800350150380381f0b001456030f44551300c090b001038030b04030700d00c40040780310085418098210075504282c15100442c0000070760010b40880941c4100b2200080c1e0000403902451095008400000f45c500e0600d40c0c060400e00441900c02d041c2c1c0003c0c04000304000c02c1d06d40880c24428502d003c0421020a10b052000007183d9401c6001507c500d0302044900d01e21703001480b00f100c1d8681e003660300d242e40c0c0c0c40791a07581c0e030b0200c0030f020b501029810008040c0c01550500300352005040c500420296940c2d00030594609480030165010b5032141c1610221261001700d11242c2c01c24036001300001c1c035080500008003078400c06400708209411000c102400910b03070303192021048188040258844100c0c50f13036603e500c400e8800441c0440c0142c424202c1c0c1e00c50070302c50f04a9201382d0107103240c021000b1145015240c3e04822411500020b5918102505c0d90103449890301d1042e20340505000e01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 877764091 1250 877762841 877762843
    0x8092a0919060320030d050f030a06091d1612111c0b150d0f020f150a0c1707080306090c0403080a0504060e040b010219020301060e070503161e0507050c031608 70
    0x58011358040c0c0c0c06000c0006070700f607001d0304856000b17401200c042e4880e02c850f080c14001d040a135000841c0703a130034071103114249164485081c0b4903843c1c02c0b00300c600c0c1172000c004448410220b4490a503a07101d070700140601103010a01c440340c00d8000140b41c1e007054480140f00e0001c9844442098849070119000c110048520001c405d10b4404116000440b03103006c0d6540044900c420350000f40210347c824500c0f04d9944602c40725501c03009070312907601d455100d0761800400388203905009030390086c0300d00b07039007a010030105040b655000d03000810719280d542c644052106000e005802008028420040080401c5c0f8040240111842c036a075460303601d5250400003094400915440c91007a40307049000324542e038000843d4851005144c50313000104040c0c1c000a4014155544071038107108203942000180303544080190704c2074041907031142100d090008202d0300c02c0000d106240203e503020064031085406680a011076910650032107554045003004241041c0001c16810001c0018150500c03003031030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 877765341 1250 877764091 877764143
    0xc180e010f0b09060d110702091501021207022107080105011511010c0f030b0d08030414010e030c1b0a091406120309010c02090c040e040308092a09190603 68
    0x20110505042c82c00c0c0320002440340c41401e01712100c0c9585ca00c80c4010040040c8190748445c1d800800550080c500038a00f8910f4605e0b40b03000070b005018101d040d40c80000900160741c181900a4041d8041070600c0f03045030450400108403007140d10a020000481c1102400340c0da010b000c1807003111040d010707100c1010340841002d003d0482c0344d074100f83d10103401035400500c0d690500114600864468021404104120512840a0300f9944008204400d002d0a400304895800000d0020070000d080c0205041e01d038020841c0701600798000840503242e5983ea1040c07480c5107080209a0181a69100d5401c801c4030907101015110381c07140c00400542d45007803060315000403403d00c0070b5032401036544002007200d505001c009125203002c0003c2101540440155030250030003a00c410064101401c0217002003908035641c1c016485a8514407003440856805c0e100d804c410b13500711900d550101810400740b00001401c4125005800101401000d854060078000f9809044080c5070030000800000c0544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 877766591 1250 877765341 877765349
    0x7050403061a030a0314090607030806030d09051507050c0604170f03042126180307150c0501091b050108010b040e04020d08090607151a01120c180e010f 67
    0x700140c20b1101c4036100860402d4000b9854940f2140000140c2d144172460b00490300c51036045800445c4c02c008058011118034051103080f0212018000c240404440c40380240c0500b9802104141d068442c0c841858040c005c0a80b0440541d0b000740380c8040410407a400c00c0e0b002ca0203107100c604a80000c3d0b0424003001100001980140d49400d08128841c0460052860084803000000c000d00040c0209013203541000380801c4840349094489115203c3d9503001008020103503a40c40b0100c406510f000580d50048030008408842c2c2501b8000d401d4803011403103842545e00d5501c59200c00c00050b13208a05014051120603a01405400d080005240b000140c00914000d02d041000b030006d0108800b010740d00c140d044940d0250790003640790231070150041500d0690004401300ea58410401c00075001300d812010280100002c0f00d09451041e21b082226040c640440c0380301115082581a517001546940705904008405243c4110b0f000c031b0a0280d0341c0550080928400140441e05403448400014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 877767841 1250 877766591 877766621
    0x20f070804051e0109260f01051b12070e1201060b030a0b01262a030a140f0703200313030e0a030309091d03130602060907121101170705040306 63
    0x1402c03e810020f002c0103118010f42e042c00603040740c00b034100b11001c1c9176116107054040540b146880703c5081280a0a000e036042001e046c0c281d00f001420350380720401e40b503461400070341021140d202c0030780075100b540311502e94641040c5036800c924801c00c800d000e82c5c0700400d4030010b6a5542d10344070000d01c007102c4090900c03904000500e0003003c41050b03600706e14005101c0d482e00718074860300c4000c0350b14000d1501400c4040010821000010a054038002451085e480820203000c9443d0502080180c004212101e0146620f0940400c407141e00c00d1384203100c040b000232001542c100d6415162402e5801c00c0b07030f0035981c003200d1300240740401d54031403848080000c0c261051a0003034211750300070303011042c140186c10480ea9a1071994141d403d9903140035030081d0354042503d43d54003485801000c3c0e1280c070f014240c058892040465443c1c40300081a00886012185440582c50503907207071030b40200c6e8562480c0c100981c40c00c260b07903d803116807800790090501e03444960391745203940b40490079280c80895213215 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 877769091 1250 877767841 877767889
    0x3030a2106080a11040b04062304150602010510050d051504081b0a060e010207080a08040503090d08450415180c030902060d1d10060e010e040222020f07080405 70
    0x3000049c91000440150311030034030303424001c040c00440c00034a100d00c0345400d141da01803000119244c0651110f4000c0315401c1010949940b1a070621006100f160801041940003002c05a54103911148180d08036110f050381c1071070004400c0100d40c03c20014644024103410020301c1c8000c00c2143c4c8200355a240e80c0e00001e50402210b07446200a5000740d110403420b00c011136000408104007072084030702d05000109405404a568108400c55400c603440308003500b40c00c0c8110780c410303002080c0d40c00d099989106000d4002000a074913031850540b84004682c0242d00c400180150f0b46e80704400c04081c201256000c1c4611806140700c3c1300b51040c00c049501070501d82107064015031a44011580e82407840d02c00031030b2241104241a00c0a0042440d460080c090b0f11780041001c40c4a80111046640c101c49030f140d03590b00c0d0700b002c0342e400a05950082d40302c0303c00007502c4030584214940242083c2900c0c0300504003015000c0c0b840c40c2e0380c000748013203a48280020b8184654506809002d01070b40200d00c0c0c10f60 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 877770341 1250 877769091 877769099
    0x5090133050d0c030b0406020301081009020901140109080f0309011b030801060c0f020406061d1215280b0114130e0a201803030a2106080a11040b0406 66
    0x1030440440d026250060812110a40910404084400045501958a480350b140500700071000350002e009044a40c002c804200392585d2050181c5c8034066001450807003941d20f0700319001003c0d0484c107942414480e003600e0020f5856400c3c003003140c0c101090720103140d079001040c000420924a45d02818404440300382124007280d401030003181510f4181c03c007210000300a0422550b18425010005c0d0300505010b808958a5480074580c550403624803d40101da4040d201040300b000d80486a00c1500d9205480341c42001c0e440122054000001c10702c1d083c8603600c103080400e00940340345800d80e14191991081102545c1c00001c81c03550880c0c1e00080350a01c14802c289a1614506104200030080e94802203900c00c0000d61003000700c1e1495800300300001c000344040038180d410080000d094440c07625800e1b9000c1c20301008980c410302165a0f5040300c07174550007003540d80d0120341110341101a501c150100d0742031000c02442d140640200aa00c402c101c0d00010402030f5450201070501943c202f2038108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 877771591 1250 877770341 877770431
    0x9150301180c031a100504020f04152705030a0602030402040209030a03090501120b0904030e040b0a030c1508090319020c10120e010b010c03050c12030f040311010b0604050121050901 80
    0x18040e100201c60249c0c0d5142c403078440c00c2c000e020301d401044058103141d070350703842c280e4000b13032070b15540410301d000010740f4000c0320302c080d641805500c90642c2680014040c040062200d0740110380c00b81c4000c02c018145804400400c0c90000790503811004122000e0702400700d507801215031070b00d50b001104280b2280e00703a500800e00d44480544020302f8840300300806c030315583c0ea6401c00050b0141c0500300e542156900d043c907000c4016240310b23118640d0380c01050316449a01ca0700f0400d00c03400074407009604d402c030b102248800d0702d1240d46801c0114087c5403600d10083c0d65079004001c42041c00d0307403068201c03044a803c5a046454452141c5130581c075208008500d641c20607484601c8917003605006855001c0e0a094508200221090f10b517915000000c201d03c0ea41e05506c0180240c0c040c3e40d80d25489180d15010368202c88811031225408403091000b000b1561081c0c1c11100d400481c40150042107108904500560314182d079040c0150351950368041c014a40d406d404213488164486014a1011800e508 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 877772841 1250 877771591 877771621
    0x610050f0603060109090510030c0f03050601030f0507050a0b030f0906070e041a031c110307170307030e060c0c0c222d061503020909150301180c031a 66
    0x480d02a40d00800002c1d5107a010f17482c4103006103d00e6006000c41e00d802c03899030800c4041070204451500c11050041141d800750a6001d06896000c2d0081ca1306074215102c0305021216000100d4032841040e00101c1c0d1a00d4044a000080c44031105542c0c0b01d082c10550001010401001c0b01040d52120041200c0b1a901400d0300e80c0d080341c182d4001641d04040c00c0034060381380040411680521410100c031039083e41808400a094001d0707500e43c091800c80c01d542e0340e164030030400c000e48201042203415401d589401c009640050fa1804d00085011111118600340b0750115113201381518045440d0119043c00d0101407001001181c40f0001c040303900200c0304a001045440000701c13a9528045040340341c46981040b415545421288034110200312a0304c09041c4038000c100c00300780c884c0e0700789a885009009484c045800140507040b540c0d41d58101910380012090290f51540d21080c03000b00e0011001c0e11a040b090181d10380c101c1541c194181180e829403070111508400c6820300401103200889054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 877774091 1250 877772841 877772869
    0x207050d1d090f181902310f020c161e050108190e0604050d1202031e090c0d06140f060108040b13170a022a0d080705070803040602061005 61
    0x1100d615903e40c0300740030b041381e0007500b40c07103e02e445030a965910308103604100300e20b00740c402c9440038010600116108103050750f000403000c10080000c01d400440b11160000c1314000038601e4014140081583d03010701c1d10415603044003413040d0403481809040105003558640c410048000080f0500c0e200000700903050082c112211603130f050100313603401d00b500e400003c90a0188800c540d502d040900f0515100c1d0254440b4402064094003100141c403000d0007568030400c00d103028032003007400005804068040080c810600c0d801b070003000c0000d543d910551507543c54013507400000d200001100988119a000d040c9442980c804800c100c0c40e607034456611940260300451000f030948480100e0319800c0b450712001404401003d80e103c40d401c0d155000b80c5040e403d00d03400c0b540c50190007034440641c40402d075045c1001180201000c015420181001c0d1403441c0720f9010f55140000b151951130814469030003800b41c68200240800c0f285504011094026191070030702a10302e841e1600207100c040800304 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 877775341 1250 877774091 877774111
    0x905040212010606050a0e01020c1c0501110f0d0e0c241c0203041a060105030703110906040f08150f010504050601170709051003110301051504090207050d1d09 70
    0x9800c54480c080100200c11004000b030040544400300501070b03400c583c00c2c1c1e00005000482c0303049103600c00a60140e50351005007004845202c19010301008030062541524950348030303800007100d4001600108200e121014070540ca0f003003000000402c0d120346003004009544903254812a0b641c48200302201401560055251469055848500d501964410062010b00c00c400b2200414098004522880c445d0200c001e98070140741342c0401d880403e0b645103000450900014007518000e510011a1031b8602451034281180300002a9190344940c20903191088240d10401401d10200510f000107010702e00e50b0002d81c6025007078a000b85a051048901c00c50311500828901d0f40103045042c5080c003012021101031a1071030000d001240d81d40701c6c4a0161206c1402c00044074407a20810700d0004110100c0e41c5564a858100300e0300e414940caa0440c0c4000401c00054070204620080000c144210040d02481400480140c0442f524444807000f4506074408400d065072001c4800da400181c1e95 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 877776591 1250 877775341 877775351
    0x8011e0b16150515042d1d161e2304091505180f06011203141c230610210603170a08160c0804141003110409 48
    0x1040c640b204000180c6584026840c01c1d0a1206841c1d0f484001d44a45605440600c80b4580c031108090004216041403200c03030b6180c0710780d052641c405803c1444074248240c184c000031004448824101070040f110300e0f950108081c82009400e020400720440f000c010148251190301d0314500d00c0a0314414100b8100d00124000062242d5a4640c0100041070b0056911346600e0b030039840c110000d000c240c034044092010044031411705c00000074650300500140000c3c0000341d107400704c0e9040c10040b13101d0442c280203c0c21029410b44103540b020700304050519454007240042a01c1c82c4086900c01d1300e80003484501c075454924001c0414286c141c1200c42600d200c2803482c0300e0703482141d9468400c00c40f4480040b102d05840006007803a0003d06c01c0d03c0c05070841c14240051541e40002c1032240700304180c0031850600019491440c03003401030742852828182007904401960710900e13168407a030000e403030f40c2100001c65625424208800921640c140c14208082c096041d0060424000c0c3c2c0302e001c802039292 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 877777841 1250 877776591 877776593
    0x20d080706020f041403100204060c060f0216030f0f1701030320030412020f040501120308040f0b01090c0f0206041e050717010b180c160602070209040308011e0b16 72
    0x155040b2002d81c0c3d085000c40c1c0d200d0751180d228001101419000d14801e110314002000812114400ca5084600030b88400e0100b65880d540c0a0140151a103e610059800c3c088202031314000c0c003070802100e10940c4c0d89070120442e140d001c1d0a01c146100c0c40b13020003c1c0792103282207005c3c120b01868103480e01403d10b4842c40b103210301c8170710f81c04924200b92280f07804040740009040305420710102481d8800c40e0b10940c26141c802c02d020461780c00344210085000c0300420340021900840e102c603009070194001c511080400e0310340408039542a40600500c6507034803228000198081d0440300802c000340302170229824903495000d000401c5400840022000f003120f40b040100400105000305030145841c0e0b2500c0d41ea07110309000300016941c050084010101d045000b11043c884948655520002c490418180032140c1001c050401c004464840c0e080200b080560745121106205a10a40e114540e170360401140c004c04402c1062503140061940c1001d01c1944c4103002502c00e44002c4500d041107909031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 877779091 1250 877777841 877777853
    0x7022a030c0a090c0f230a090f03150e010b0a051509031507080c0a121a03030c0f1606140304030221090f0114030f060a050a0810050a09020d0807 64
    0x585551000001c000041c031103d454020510124041c4c407222042407041005079100c40d0403074989110a8101c00b6585040c0b101000580f1071107803140303801c540c46900c0d880401c50849082c3c0041d05c040c0100c1801001160b0306005141090314808024480c2000510100c1c40c4901c050203614031035181804801403040901003036504050004007140c600076103580038003c0e191415103060000495100010302008021030442d1070000441e0707900703000580c54840031401400e03210482c514890301792001c4071059900300040c2c602d05c8941c1c1c01a151030034030312620234075050040100d28401701068100300300094024800c992140f03421580182c1c3c03a521483c00728204201144028561808415240703a8218008082c00300d012050307401c2e1410310307010001519003c010003809640d0341402c100040b990882d840ea5580c110201a20803444203854000158006d16542c20040706580401c400d4141558a4096590440480001046a1070041c0c001c80c8030700d08203000c0902040e01c00a511020040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 877780341 1250 877779091 877779103
    0x100c021e19080f030a0f050c161d01051f0e060c0304081b010504230f22110c060402010809071d0103020108100e160306030501020d1407022a03 63
    0x40000d01d800340326545039074000244071490250200a00c18a4407402040200004950f144203141c0c681a041040301d101c11541340e400282098210b00440c905d2018107104603d20a000d014410015499030303c0c600d40c540c089000c142d1103148035a0407040b85603e148481c2040b560000130314900900c891580c14041426445207070050042884006400100b412010413000746c040080100d401d8500b0601d001152640554040c41383c0712100c40c012041001101c4c0c007038882046014281500c1e85401b10000380146001806a41074020581007401c20000c041c411032207108103030740d04031f070408118581c0782d5612080144024180003030720020941d40c14082242000800da110160001c10401060340440c07080280f104034045a50000410048a83c0403926016200301325044140d43c2c0d07840c0c1440080361f00c0900c00409040c0d84005c04004250280001c01c1943c05605010a106002c1030304000511002858201150400058020024490184444402c042140c19090039803603100283c1006 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 877781591 1250 877780341 877780399
    0x40902030312010b041508060102030d051f030c05010e190e0c0f03042d11090a02040e0f0618090a06020d0605060307210e0c10020111040602010905010b100c02 70
    0x40200b000050032880100c01081590141c500700f044e0803500348025184104155003007130242e001030105400e03192965001c0c030f41c0301c0900c81d440c403200350440381e0b205000e00f184c2d0002e43d128080c2500602c0f50f9600301c40e400f200841d0603900881060884600521169103174000c00c1341d040c000d6030101e060391000c00c054500000c1c11b480701641c5e80c105840d0040d00c0300d40c05004110103040c0c44818060304940d00c0c2d06403030078503000a040700e6003c890b1410420100703030080260350083d5092101199541a071404644100d05131026452107003055400c0007441010b0008074901c10300224100300241701c0208066048079802407000d0303200d102c0048480c02600303d81c0c012079042503022040010f141d910500315034001c40492840b0361915252101c05003542ea00620000c0740d684810341c004624242003c51b110100001e00c0001202e01d19021181003da210750302050040c2c1d142e03514801400700c20304c600c106003401140d031052110040034006d0b10030307194280041d100e2040c0700319042601301e250448144032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 877782841 1250 877781591 877781617
    0x304060b030d14040b031807142b2d0506041509050316030509130906050f070509060318062a090a090b01030e120c010e06011202092a19020a110409020303 68
    0x201e4071924500d41d00d849904008ac82904a0703880c00340e0010400309a80740e200e0b50780c01c0013200c41d250340d11400c00c0a10521042e4211441c40b01381e00b040604401c5546074042d2081c4060003050070903051400c0c150401000b805403030b5140609500020720000304a07003a01d4418005102c0704440c901381a5401d010314071525803c10174209103c5100c0b03030701d5400030000d50321840c010480b5494a11081600100880c0c01001007881081001514039009e030141d0350010341c070344200c210400700025080c10b000c0241c0d201d0030440d58404c44080c0001c810071900d83d880d81c15110f01e9043c0643d000000f030035607406200700c030429590b42502c082264441d800042c0c018540760b04031030b02c0303150f1b00501c0e000d26070107200c1441c055440c00c4c000f217038454408a80300b4100c840c83c00c0e1000d042e040da5000c02050202c0074146103820754424a20f881c92464802c200705030034040c0319a0715200d04200c0758900b0021000c8049030215041281e604c0d0008150101c10300c07115100f90f0300001c0d034007420310109185110f07014030113001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 877784091 1250 877782841 877782853
    0x110a0503040b1e0a020a031a0306220203070602011d0f0c0d03120e160e0f0705130815040309080a0f201f1803030e0f01140304060b030d14040b0318 65
    0x8051420717002041507400c1780d40c0c1002510300c89003103e1002217544002c41d506412900216000f0440030300c4074075040301c296104007580d218990000c2d1a00001d94030980260b51110700001080c9504841c06e003d14a80d00c1c0907080000300c88030301944900b04500068410a2224140028580300e00114418000c40c4241000441034514040e641e0303c21354a01a0003060480b01e010a500842502d102d00034540d0251500403078941d84010748440c0c0003414404100c0381c51000000d21420100301c0b49010080b048903050702c0b402c0c1801c0050140c51a41c2010701c456214148010020301c40b03030f90642105401400f103408140d60070704180b02000c102307100c1581c842404c0e0482020368611004a03c00d030306450320b4403012007031008800040c1d00e0480c4000b40100d4031016140c1d905040003101625041414584a080b1210f08070800d1216002914107a61003503035029101110300701013003119800d0b045030800707151095a00281c082288154010410b11134404004951224550020345091a00403c16112 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 877785341 1250 877784091 877784101
    0x302041127270109020304050a0203070306021215032104090c1205090f030703030f02070614060a06090b0a051605150906010f0b0706180605010f09110a0503040b1e 72
    0x3104048020751620442242241c02e40000922580070410b0511070039400b610307803820b03501c1d00003508000d20a4450b40100d401303200040c1d0b8148401e0000d10300c0344800585030400198503030b01d190401011b080c907035184481c4030062694000380c3c1e4110700c1143e42c4023100c006521454a602401940d1002044034145006414100d4110380319040c0018140c0d800c01c61a85c601d042540d468510004468185e00304101100200c0d1183c3c11412803101c0386a000b61410889580702800ca40b8000c4003d0707a0104080c1c1400700b14135002103000020080c502c1c100c1002d07400d110300001a8464010414103000c000038011034000c410401c07800b803081e00f040680f001d0040003e030b51501c2c1c00088882031140c2c0070b41000070170840007010300ea0080d00c0f17481090a080c80c1c540c2e51940300070001c0400b014101e058442c543c0e8002006405000e010302080c400322500c00b4507001c801c43c00e8900c0384d4502e003400a000d0280781e25182d408007c2e603920a80091410000e0307100c1e0034000c0400b81c0d81b0102d8100c00a0540e08002e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 877786591 1250 877785341 877785397
    0x109050d1103120901030b0f090105010c0303290117310506180706110601150215040303020c0d09050f06210a050f0705120a02031906031101090f030c03020411 70
    0x4013a4400c1e2414045024658208402e10000603116548030078484018003165204e40d8008641c144203007400140740744000b180c800c1708200f44111040c81c005240000e4540d503840844044881c1002c0c80c1400d5504090000303000815056144a5200c0060100b02d0144c40c06c00400d0f0346210303001010b40f01c00d401d0041400c41011551a2000e000d441640400910584070300d09940740070049030b002d071220341d0802c0c170341804007013a800310b0318218442c2a00e111102c681301d03402240030306d11a03107005a0320708400340f0b0281040010b68408042c8400603808020503190300d603c0444032032084030141e0b42ca00048800000301c0c00b242c1c0b4998500d510540c100080191750758030981c041e03916040c4100071550f03800c20443e42c0384541c4024003000d0403032101140400304160040e41d045104c2901c0d00207011000013484080341c840d03500a40f05070350740010f075034038550300404400040c3c5071103141c81000c00c2c21501c401000c2c17909440001e0207141d40c0c85e5980c0c082450b00e0706a4588022001c8001d0320140440448 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 877787841 1250 877786591 877786597
    0xc05040c02120d05011e0806040b07110f0d0210060f090f1107110f041a1e0607150c02010612030804050a150903030b030c1e0f10020601060306090204050109050d110312 74
    0x100002a20030340c204003110841b40c1540e000c0f0b464038401812284c0d900e9540c02c500c808050f082c80f0074007031444a104006841403100c89901c83c01080204819025030744000c1c6010700c910302981196280034001d0020140a6903100e00b5184840e00120f00c55010b21450350080691020341c0700d0404011a08400700400000b958179818401c1b00c0c0d030001c5900e504100011145a4182e440042541c11703082c0358036081030f10700c0d00640502c000941d442c80c40c2800c01724149600c028070403215030380c00c3e00d03412540d1341c26032040300451b21140c4002c110181c20501d00c1407040c3c2e05590040c0074003c0a01c00241004020007410809a6100016901300b540640042c000761452100841c0441d08161071540241000240e0f10007003007000304107404010404d0040d80303691250108194221004e120302d540b10307403901e03130455030522110343c01003c3c15854400e0040458040c1c1d0444980c00b8010441001580e903c00390079401d039841140d41c01c580e510765251107291410740382190b5070103001c2c0c070941021100a40713003d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 877789091 1250 877787841 877787849
    0xd141606170c040303030504020a03050102040801090201081b03130c0510050408431208091e0a0b0906070c030b1f0807060e0105160506041e0c05040c02120d0501 71
    0x3591403041c1910149992040d003215280a950310a00080010038865003005170031038006402c0c1804141c03292030352800d90f4440d402a4260b030b07444048800031940d01c041a07551001c600780c11400440c5000b080c04225100250615542c3c40501c0411400d0141d0314881d03400404000b000c2e06510f0410b03c1016203290854859105140919140444260202078106500c2c0c9440300558220244103500142e8840c0d048020002c8480903c03404512100300c44a51903c0500400d80f094450744890200300304689055800c0c045d45030240052101c42e180c1e04602800e448481d2503c82c0c50f44170110100d40c0310300a107840680034034028500001480f0501d00228040c40e00911841d040d640f1301040080411110301c2003845c46d511624080003541d105800c1c1c002070500500d84985040e40e800141000ea09a41d00140c89980180301440308011a414148071b2200c41c000704070743e0141c19034035141540080c1d881141d001d151542c075090400c070720a00496402082d55049551560b542d02040d100401003405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 877790341 1250 877789091 877789097
    0x1905090111192f010f03020706050f100611030d020a2d020f01021c0b062703060601030c0c0308041b030309050306060402040b04091e02040b0d0b0603090a020d141606 73
    0x95061190030f10f24143c2c408020740e0004030036051076400011561548220f00c40b4040540c244507150008407a400741038080e11034a0303603014207410981c0c01000b0320038407580040b01b804a042c0341515450310100580d145980002d400503205c0c88222000c1e0340711180c1305201000001208078440707920180e5494a001b0320b055070700315102e101a401c8294200c0c420103220042c959419034107050051241d0b0040d100c4480044c0000742000b000040c109500005000c000001c035440c0c01c44480c8504003001100d510060074a4140b000310103d060180189550100103410841c80800003028043c4200c146145800b03805101803806580f4100140b500c000e600920b407081c000c08010441c1461f05000383c40548504d0700420346400e260007091001070644a0455944003407941002d41c0381e03506880a000201513105d03c40c0e0b581c6400d10340e0310044614036100c0b40d200d118144180141303e240080c04a401580c16100c00040180908089006d10b4070460b5003406442026032041c0c00c85010303910281180d840391 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 877791591 1250 877790341 877790363
    0x513021201090506241302040902041512150312020f300403031e2102030105010216032609121608011b1d03010603051e03190509011119 60
    0x10340c0440c1025001c2d111244105100c61005e0107494003203d00c1d0340c48403e5041c010300e0155614650300c03da820681c05a42c3c843c140740d094250141d048030b804105d1000d560000c00c424988903142e4030b061022030002404011007241268011030080100c400b100700031000303c5115080f0154600c0c0b0241018600c141440f01d0050a201030510710400e44068a9060310751400e000700840f03401c10780c48855140d81040103c02e01160080e080c101c008895017005401d40560f5035812b110000e445c05156250782c42e00310410280c2040403890084007008685002580d2404036070007103020981034050340201980c491024040c030990003034000382c0000540a5a03048141c0e465a54a045080f603c074146840080c110038810b0ba01050312406800e0b2840280c080f02612850016010900311603c0c0e400440b029030000c003c90014403400e280d10464860a44011351921a50200380e01065803907005020600c080803840c001c45a01415100d801c03850001c040b54040080035074201c141d110b8202041e0340c058122 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 877792841 1250 877791591 877791601
    0x30b040b181017060601050c15010905010e0105061812010f0204091b02033a0c02150a0204080312040204021606050f071b023a050c1002060a0513021201090506 70
    0x20200f403c03e407903520005018541d4a05005481c1580103a150702e11134042c4203a8401c07480d41c84480940a4400b2942c0000e466042841c4101e84640603007100f0b126120071b10501d1030110701800300d0000b07060203a8640ca0b48071008241180540000c0394402071203400820003040a8600f540801301c01400e01904840c1c0c2c20900a060780c50740300303048040071150a2121681e80c0d480c410403041003102880d130a8581c1c0003483e0070400e0100d40018032840010703040241c0001c18004080d1107160080c1e6508030461903c1d180c400e5041ea00c0c85600c1d54824000003c00000303084d9580ca5054829121401600c0c00282c000b038503007500142021100c20080e0f42207900800c940321b10031442c441e0903101c1c07448195040402c94013045480c80c0202c030101d07040d1a0503c903040c8021090789810038002c5c80041c28a00705621482c2c400e0911795083c80203409601c1c00d401102d0455400656180c02c152080000105a00c90f01308690300380075501c10103500080d1014119000b000705500c1015464080c0007030355250b07155 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 877794091 1250 877792841 877792859
    0x1203020403212a060e06010f180f020703080108071e030b0a110d0b090a0213060813021e011b020109170312010b031902030115030b040b1810 62
    0x6903020240904640100b004001000905550410340d068241180070b440400a02c000b200b001c1c54201c900404410302c54000c01c20b65004102e5045803803406002c240d03040c0110888122002e00c10710007141c85001021110150b5070b40440c1305411401d4040d5520042c0381406005200c081c8540505441902e078001550810380140100703000103007001c520328600d143c859020707042029101c47d5040d80c1c0d50800540341c5121200404000340c1c025800300f6081102c200b00225000018543d11210f801040301e00701c2c01c0c1d010460041a0b585078107083d50715485000046420003000c0e94029000300380c640c075500300026013000582000c2d40982e6544525030000659107910301c08100000d0114962080c20b011304600090024401e02d41082100d042a40d103245107904140c2c2a4495000b465000040c04100754451000031044100b0362010340ca1549002d1070500d490103101991703001c1540e1140d004000750348581151030004070041a008261084200600807040b09a40880910b40c00c01400580b40314 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 877795341 1250 877794091 877794097
    0x2030406020d08060105070809010201020d0e0105090c0d020904020415030503130906120b01060518090c0c060609010f121a0702010c0905010c0201020729030f0402031603020f1e030109050109120302 87
    0x1134180e4401c0c2c20282d03a5035510130150400c0a005040d03540911807100000000d00c60b072074500c80c038040045554100070751040c1c10040402802da010b191010007020268588500c3d094001d981520700103000c44400401d01e41c161159000148240000108184403820190f00001643c440c04010000c06070b8480007007100803078002e002041c250175880100b21280c016800380c00d02a03805407108200b500c400c00003810080e0100d43c60043c00c1d2011039504400300081080a03030285055412038001e506180310540c3c0c90610348151400744199800100402403400744403815035071842181404c1d0304010030013030701910a584001c0d000400440d00007401c3d6114002807001ca51b0180c020b03054940c200a00040ca074040380503c2c506001d6500c0240802074001801035110303080707a5480c402c540c1003620400d824401c0c03924222030351007104e000070700146c0d90701440c034076030214115120301108040b40c1f201c2e500c180786506241d504d94603015526050202c103400c01078086118102100c100704a00d5000d43c200c1c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 877796591 1250 877795341 877795351
    0x11070308010509010608072712031d010528020109080d240b0a050903120a050a030b030d120216020901060c29060618060a03020408060a06080d1206030f0302030406020d08 75
    0x2e9000c007249100300c0380300302e01207480c0d42d00e29088d910034070703200d001401007102201f0040303000415240900744001c28400d0a20522030003460510700c0d010171049925801c000c0c04080301545004a80341c40c071000d000f580024403443c1e2005449407a1601c0600400007440030075010940380046082201d40288800d8003001942c0340d40181c24100314a4840480303164002d080c030f007909886500300c00000010110090170080c0000d0303641659030b100002004090f1007079130203094026400b2030f40d885401c44c0c000804440c040c084520040e11171402d4000c0200c3e500d007000d4042d400007140400817950710341c040c0e44104070034010340c0d0854200301501000d0001044141c5071540b09017200c004a40c8c1440c01e0001020717500b509a05000002c01d20300d0004010784c1c440803002000c60380c006001c02031280c082c00724561050b0f00820400406240c8080291151040fa60100c2003041801c56602000303030071382c000d1000e50380110060750000010310303001e50f84c0d900038064640544108000da80c4400e101c0c0c480f9612070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 877797841 1250 877796591 877796597
    0x4060e04050f121b0a05010203010b0a12020a0c030c020f04050126071d060102030d020f0d06080307020f01111603060212180304030f111009030b0108010903080c0d1107030801050901060807 83
    0x40312184c520403201000f03030b01c0d0000c41405200710b101d000c514240080d501910362414101c0d0b481011020140500c81801a0780802c0e03801808440c101e503030408500c079460764160030b10325000205440021803103a002c000451f4401d151100100781800403079003c0142240c00881d00d000009e00a40240d170b07407000fa00c6a01c2030451101140310300b240508100d1500020113004507410701000808107401d980045890150310b03440880c01d4071003031142d409503800509030b04028524140060b004184441d01d2000084d060000d45031130704248003010030100300107010320344844d00c5503500c91800d08040d500202c201a040c1c154100810300d0a03203054481d200310481040214a843c2c03030b698a49031000c0748580c00341e50000225454030b520f6240d40d101e03c1a044160343d500300b003240c11458121041a41030300320302241e0b850a1411710009411485140c0c2124001c0d1905840725048001000581440d003107601101c6408120300d010980c00c00003290582d0001c542c01801680ca82c0d90842d40c56908031095800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 877799091 1250 877797841 877797847
    0x50a0507091a0d0e0d0e03070608010e180c040f0510050f0901090e0c09010b0c0106290d06031e05060a020307050f03070309140a0309050307030309170c04060e04050f12 74
    0x761502d000d00409500790351420118088060080081c10203a100e00d6410120715001d603c4c80d85480c080c0261005481305050032607981d414481501001c0c10014080e54644100c804032102e5024100041011038100601c2071048080d9454010054034003660078122580140e4030102e0076180c10340200300d40540161800500380e10b000c08103409800314030510420b81c02400403183d0309484071340d44a4003920310109d46c60743d41e040c3c09000c2407c4616030b5100404020000c0c2003618504090802c0103d4103100c602d64945421800354920014440ea038001800c00180b03241c10004c00301c000c1600c0700054045c85c10f41d01c550380d40000d810240d01c021a10304001a400700320100d0034000c001301030342e0042c13030514000568424540c0d03180004c40041940100c5548a5001c0c40c0030160b102090201078401980600b0309689966006091000507000e00c0c20502e016201d20707076440f0810803c10181e2000140705000c440e50310342c02840c11a80940707055402d400b80c1500c03e071710b03c440010524146440210f070171b0b103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 877800341 1250 877799091 877799129
    0x10b0105090907050f0412050d0801050109050d241b08061c150f1a040605062a0102070c03020f0405040317131b0e101a03101503050a050709 62
    0x420b00014020800e01c2420f100480e00c48980c440900301902d401d0100c0000d049890030150f14200b1607842d84401c200b0b900f00180620b90384020f0300c01c01c8a40c241c07064400104a40342c0412010220320110603800c2241000d806001a0740c0c2142c480800015500c11809004c620304a490380b20443d0300980028000743c00c00c00400380134000c0f191450180341c1a0280f0000c0f0690601595490201c095200781c0b1b603102d001c01c0d00c0314254404040f41c0203c60030400350380781002040480c01109003881d024421400400d03107940344140079100390000b00c4021565480503181c000c2000466000903401110b00791440180d074106403048601543d09501e585140081c1c80c40450422200101032a0039040215056000504000001d4406011050028655a00b44100c0e014001b100405415900d42040d808004d0000c40c1d284003e05205041d079119070305e80d0b0f00f0303e200040038919070041c2e40f844085003500301025499030115000d40c501c07500034001a110803000700c41100c0c84d406002040804a000d0740 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 877801591 1250 877800341 877800349
    0x3070806011e030f2006041805040609240c03050c091021090b06040225051f02180a050f060c010902061903050c210403022a12010b010509 61
    0x18124a48100028622500c0760f60f202c289180442c803c17200408400b0300500c120742e0714000d2080d1101c081d2402410a45801e03816800c1101d01844003902650310301c0414241318503a0410001e080c1c0100081c1c441034000580c1c625020187e2219140c0680f42c5240b400b0308512901441d0b0007004084011410201080200604603080f05200d00c10311982c845146056210a40400f10380200000e00143e86401410959070244004101c0c034841d0303204004040d41c601e041105159901a40c40380601d40c01d5092a009141410b0840c00100305484480003020842480c1c0060070900014180d9028041340c58091010442107806076680c04801e03101c1c5101d0380d0409202400c0440d00901c00410a110503401040c0e2039070001449090690411404d00d8800c5d41501816400c480e000d030300181f170103a44281c40041c041000100820740d10002c3d010900303040c400c201c085101400075100c08000c06142d04507541541021481314091040c6110b1000001010703c141004040180c58280c50030403810200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 877802841 1250 877801591 877801619
    0x20d1b0b04210801140102010216110a27061508011e0905180d030507120911090a0605150f07020f01020a1401020a0311040b2203120e090f40060504110307080601 71
    0x7858000c1844cc03000680c07407420301203201c00c40d0b1403c461585440710404c40b00095a480740c02c6000c40002e00b18480c9020359003d0003050460316014405511202221004c042040e0654061000582401d00344080d80c1c140b10844000550800b0843c1c4075000101001e07015031701c00b195950f001c5100080c0300c00e100040c82e00302003032861240180342c54520442c0009410301105035100c000f40fa036140000d20903800c2440065003c1d520440740e99080030030307414040c03009200c0c4a038002d01421341603403203007003690080140142e41a80b00c140c540540d510505114001c0d013181c010400024141110300c0d440b40c40381c404540c01d4540d0550040d151044036602d092191440c00b2418809030341d020b900202150039403540c0d00030f1604664501c04012404400c002803020050422141001180d090002d1841408030007841d90103407050390f8072900004041d641a00c991003006640003034411000b034007002182d5000f64407840c03007043c4038a4203000c0d46044c036690302801d018400482e4404401070021015803802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 877804091 1250 877802841 877802873
    0x70c030311040519260c0d030309050109060531060b150712020c0a180c0201110c0303040b0a180b15100302030601020d1b0b04210801140102010216 65
    0x15003460190303541c011030980e49003082d00d070919161149050040c8107258002178194100c0458984074034441442c495102d5003800f4085205422020002040602940110744420781250081000c032525003440009443c0860324150505901d01c1509080041c80402070740308042e40d2010000010780c0c0d5508001085400030140c0d01c0b0079800d880044060341c510081c54401c2c4518030401582c5007403072002e0315064061404510604641c0030a000d6a400c04059100705261004003048103030003514141d0040035405551242c18400280040d02c01d00004000c40c01039103c0c07221924107540390142c9208803410080311400246940d4400800310340446400c0b40c0000c80060b02c06880139400d8002405245944280400300341c0200070000c00d581c05004c195041c1c002d81c144131010249910000b090381c2c201c01c80080400c0c1e40180070030207200b070720b0900c0300c407030602c052503e000110300c1c1c2e20142c4031882c00d120b98140000c607201c10990300c0d4418000d03241c4501c042501001448104c0e0359041043d900e08070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 877805341 1250 877804091 877804121
    0x180a0f23060708190f02070308030c071b0f03261207022a040b030606031c050918040c060309050c0907030e01150f06080c0f09010c050a12080609070c0303 68
    0x80200403e48110040486403131601c4408604403100c28080c05502d100d08408096402440c801c101103100c0340226035104524461a81c0c1c4c90b2014603080000745041c0c0d0070040700b003500c2103010980069092000742504e01424815910201002d480c10360006503420010705200140600c0003102c440d0f002031600100c050041c0c800d0741600042e1003140340d4600b040c03004100d03400401c250b8581003074032990034024402e8020300310300c0c50a207012a50b2107a01842151191180c2480101128420015283c1a0000178000c115140d015000c004610fa0183c0e416103440550420010382d440c00ba02c00c4850a83d03200c80501f440da01c903030041241c40c000050642c414551075044c0214010000e210701c042201c0e04500384d00406080c2001c0c0038054800c2d0300701d0304c1400420414401600b01d010180d800b454901510540c0e00e11074040101c842411742d00b40103200e807082c0034650301044808a90400400407903510700b0b443e940c410040000c2d210040c0e07106004214018210030200e486a0407030110001615 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 877806591 1250 877805341 877805347
    0x5010c0203030d110306040b010c020f010521010e071419050a090e0f070e010c03051204050313030818060a0f080c090604080303061908070b03040c0b180a0f2306 71
    0x3d41c0c810340d08207064000f100d0400204006031490f051007485400007003840c02d071150380c5840c1d0105034500882c00c3d1160600c0404140d100706440301c1c4125251081c03c203885024156907940c810b266004040c1d8050012442c000c3c0061400c4400c0c07003c0d14000c40f03000010203c141e0720050165450b9201602007410400e40100118030907031202512030192281680481300c40c03809000041c5070400c1c01040604010034078601c000480d502c8810b4810700c24061311820b0f410744451602c80c1c0340d88180341d2002d1106840d90310000c14000340c1d10190500320031400011075403802940801c07607140303d8884080085401e00e000420424407860784946d0081040140e24a05030880c40001c0d0a5003060303001c001650b00003c200501820112810113070505100b0810046074117100d40e81d510740281c1d0062030440f40020000400303214404210f0401000014081d0390307256500180c02c9407041d01a05942e004003203031000000c1c0c5140c001054011a0608242030030801c4c04161030407906403c00480503400a024 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 877807841 1250 877806591 877806607
    0x409240308071109011d1e04030206010f0b0306010c0b0a0e01111c05011215020f040609260c0d03170c0301030b0906040c09021c0c0801180e0705010c020303 69
    0x94061809180146481c0b529080546410440c0407030061085008050389001000340000e401d81c86509101c80700001c0c0083d0307864010100b030034140071906100403030031003042c03105258010a0050680320300b1680410320f0f039250040d1002511055a0081c00120381c5840c0780b001c02e42040700300340c00c070400b42070100d000282000141e007903841000c49448403507400202802e4034210044800510698401c00b1701044d85003052400c0c500404180162501e400c0c4a00b03125001802c2d0b0440d564003c03000302ca191116140c880c0204512058002c9a0680004842440000d144c00503008581c0103d10020035040c102038090204485503a5412410702c2484682d0f5001075524070303c0b0600c61903c41c000c00b030b205e41c554142044603602c0640400c100b600070500b80300c0496060a1800d05130381d00c5110260f40c03100034141c3c4828496502d920f6a50a52034052048140e651100c3c0041c1260740d240001640254092510300440c0d4142c194610941e11040082015500074031111000340d00040a4034204011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 877809091 1250 877807841 877807901
    0x10b03070602010e010f0908090d021311031e060f100903080301080c03010c0c030c03140d020c1e0102280c08030a0608010c03060e06040902040e0d021507020c060409 73
    0x319008003001d0303510707200071204c4040b00748201c800d81e40d81c2c18403e0152003032a8071a224130f4895420800c3c003889400c1043c01c290b4442e060040f44060a03003c081102c01d1a4403810350160f0025503008072242d041012041d1801b2031701d030710305010b00c1c2c004251301c00d410075141c00c105000c05010510424001c19001c000049403400c0090360081c002c03a80030f890b40a201504040c04c440f40c403400c15060101d08000e20f8003090340500081c070300a44c50f041c0500a10b0071078000102c0e9000b50503404510034000946000f14403001326040b8000342d00c00288188669a82c40b1560a0340510b02d00710000440300180c0052507180c0c8000d0f0341076417110382000b00503144162200c99041d881103a81c1116203442c0c00003080f0140382446140d141024910b02002028200000403c4403003003d021117105a840d088400255501ca0740010031754004d00084803802106010040d4035040f030260142500e02c2e0810001d06d43d42e0000c20000d84441c401081e2a02e0b0a0805400f8001440340300745103500d440d00640f01400c0995 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 877810341 1250 877809091 877809103
    0x606080a0303051e0912090303040f1410050c120f21090609011406040b13022115010c0201180302040911031b01050301090e010b06130512030703020c12010b03 70
    0xc00707694046600d141190f0100b46104000700310900902609080100d2003002003201c080c032401d403000840d541c01c0081c0000303240d80246c1d085424000001c18000400300e200c50b01d00c1c002543e050fa00107100303602e8503106803450301640c1000155a0021a01800740304014401400001d07000c080403410501080000c4154200720b500c180040d400000a02070031040400c04268003e002c42c0003400300c583c65211745014104050142800707142c446800354070540d103d001e120001c1001ca4004c41d111410340810b060810300721340b0030703024070501c500c0402c02524a10030100300881e0103842c0c0400d40983c0b0341c011202030980c0d540200b4a441072a03008401a5140d008a0802034061416801290010800c060034800c4802c140c41d090445101c1a0400d42d800109581c111842c0c02000580550300020311380c05032105e546495071004001401104030060300c1c0408055034019900204207000c0403008960303070712540b00094003507417000c0003414540c40c0140d40846c002d6140030010404645401c04203103401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 877811591 1250 877810341 877810343
    0x7170a0f0602040305061f03170c0610090b0102010e1504290604050610020c0603090a0b0a0c030c0f0903060209060405030307030807030b0f010806040905120703050901030506041e090606080a 84
    0x1c0d000a0100b0600c0000c202098100c841c6150f0b90b480c41d1804600e00707c0c034a200d80300003042605002c502c500d400c090b03401600d540c0d5001d10103503401403812001040d2030004c00e010b10a401442c1c241c8c00c0100d0351051150140c640a0400140711310a8100ca070610400c01c001c1c8212041c0c030945541b18010410b02986c85401d02d400d0b6110207003810903c04200503520018403150140082c05030012000d80c1c0080c1c0440f44200030388000d9641e84a0013803181c100f4901d0240a042c8803074a10500c54410304a82c021a1080040c0c0d80400c2070500c0161308031812145940a01c0021b02192700034000706110341c0c0100015600201028a03066841c808a411500840b2066021804407070802100300d030103000305031107550126000440b40070709200103800c25101070b040a01403076680f001f0704100002084044241c8000036426529202c0030700c1d000304203601c8203903014002070030300000c11110f003054040c030008142d80081c0c28020540000c0b20b0001400850780035103581d61115070005070401d003806009a41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 877812841 1250 877811591 877811603
    0x706110705030d060e0f0f0711010f02180907052d04030b07020109020a0e161d0a2402280f080d02130e27070e0a060311040b0307170a0f 60
    0x80c0740c45da031101924001003551111880c98810407004000d1120b120b0785c04146070906201c08410450000c1c01850317001c94504c801480081c101c50548280d2044400040c011104100c0642ea89002164070703004510310b50b4003040d41e0800311604800c40c000840c039501c540c002c400b4140b0303960b0b848580180d403040d100c0b06c0140c0d568058802c294100305d9249006090302c403483c1d59050500c05640c00c44807489043c04010407240320b02e02d00a03181848000c5019070801418a0002c0c0c0d11f07031080311180444482112040c41904007144082d40c0003203418400c403c2261a1191920350012141d03103602d081c40002c4882c010440034400004103090050891604020701c0141c81c5c104801543d031001101e90020903003001c40c0c204004c3c1040b1125115030b40c200d07100c403a00c07640418400185107400e189400c9800e0b9200750070200415400c0035800707502240d002d00940729030362020b40d00303020031214240d85c01a0150481d0340c080c45251281615914407103d52401c03549042d0042c0c440340c0302070040e054101d4507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 877814091 1250 877812841 877812851
    0x2090c040501110d0905040f15030501020c1009030f05091207080102030615030c0706090804091803031b080103140f19021801140d1e21140706110705030d 68
    0x755a2210a00100503151402496040103050000e440b9007454804e0310b105a0310f07403240ba041c0e00481c2d08801e540003039810108a0b03241c4c072450b006021b504502200002441035080e0807031140400d0081c8180107070503031106844403400e04c6040792a07900284211350040c419480d20190f80400b0020000184500000143c681c24490100040461481c01e00300c20010140140721400c90413070201d4001e9035110030006504001e501d8200b0140c01650700c000721052800355201c0301040224079100c5800e00c0f90b5000c0008000e40d090121b40304c048062030b000084d0700b0000510009103520182c0102d408210704840c90000c195502610385804802c4070303e400c04000c0e80038011820300000e50b6013150004000d50902d5030510904071640c00c00501254861408284440d0034040d03040031283d4228466400c040780b10406e414200206003020000f44912140703013620240f090301c115000900c040000c00e00301c1c502561501d038100501030780400403240071010444440042c100f0401800341d02410749011038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 877815341 1250 877814091 877814099
    0x120204020c0d0c030806123022050901031a07020c0d030c12020d02060a090314030f10091b120e0706080a0c020109080405300c09150117090a02090c04 66
    0x90745d9009010180600001c05200081c9080464110f01a01030304001036443c50000380d481001b459030600d00704030401c0001e00184201c6030542ca0042811000080254840d0340340240300301c2d96024400585201d0a2003074950401e01113807905600715100780f04540c00b03140040700241030021a29001c401003900500000b04000f01014008400e100c280050954039141410203502c4030402030400c9101c0c0d540351028000c140c002c030380d41141100f6404c440ca850b0300c0c02080d000355a031000d4802e2598080304440004100c0854000c6071007489400180148a105424040c1c034100f0002e4540010b0035101c0030400107000342040240d005252598884c03a050034103000c403204a5403042580c1c421a4181010580400c80d80c50071182218403d49400241c4503880180c011681c0c0030f42150480f48840a10000100100081840464004550024103a11100c0201001c0c0102381841404074000ca140f4003c101c5140c0c84943d0700c413a04800351446030601e5030000301940400c6818001c14580440c00344 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 877816591 1250 877815341 877815347
    0x100f0b040e0f07020d080903040b0307050d1a0f01230d0507080a0507051614250503074b031109131410090b0a05130804120204020c0d0c03 61
    0x1030b8105019072981c400500700320b40001c2d1102d8840f00f260041c4054940480e001c0c030010400c807402000c00c042015124142018001d21a901c0342c140f112405050030703809140ca090300340405421842c020200c148000a1000545003444c515a0401a500ca60f15074000304803003060040c24003c41640c800902480d1420000e04107981c080c0c030103540c07186010100014150481c040b2048121400240c5101400b00e19144800600e221442c20719030043c16100708481c2d0700780c2c00c650340000d08071508035003d40e11203040c1584c0720070342d103d0381a10361180d4140001e1240b0301c1130440384445c02492800701c81002c40400300c4450100c0d201c103849007180d00308100180081c2d650185108481141d40800c1c90504010004801440007005455280c1d56000b00d04580000c001030b019103e45000140030312111070038841054182141c04255172810b050010b01c100800ca4501d00d542c030303400756a05040c503051640c02c005c229140c8000b00c0c1c0140e400c015040c1c2c03c800c10400d910812150f59101529500c85150003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 877817841 1250 877816591 877816619
    0xe040b0f011802030a091a091b01050403020f030304033305040803072a0c17010c1205041106030118060503011a1215010807060e01020d1403100f0b04 66
    0x3422840c4858001403110702102c6950400c2001c91602c0540c0342d40307550003d00000c10300301a008000400044448103040b010303207440342c41095030303c00f551210b03403002d4410b04041c055020341c03074000788040100744010b140c610112038801e400642128201038607030782d52150084207488440302905040c411a0191058107000741c51802401c9024040c60038190368859480c0009490700e000c2c01019000200b40c0e440c1f00d4901c01a02a850401e0150000581415495884070703000b41804003126610324a80200140529000d541c02035560850303211040068000504006d8021100d56042c00760320041680c8a101070360186c0602c06800006a030741c001d25030100c030f1083d401035010b41d04280c44c1c4244150005500d480b10801a20040784003100e100e240c5040c00c3c0c07108011000403140c2800031482c018002000c90907130703a031034a0300e880088043c001680e075100da500d02d0000144049117204106900341f00956040350f4580c00c4002c1140c0c442b50640c1145040b5003010b40c40d030398085400c1210500d01052 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 877819091 1250 877817841 877817851
    0x20c07090f0917161e11180f0c090303073503150310020d0c090803130902090d12110d03022802030f04120209370f05010e040b 56
    0x70030403200425a99800800750a020000000740d008030300c018103603c420003001200b550040714a080c6070790a0091060b1400d01c01016a200c411000d02c2d101a4204540600100c0000007802a103603620720400304051540200001e5900b0010300c10100191000c00142c41024410b40c0e140c503208900d8084e5102c040042c0d0400d44000044e01c01c01c101001c0c090040780c2d0403078a03000d0f41c50b030201039980100c0d00e4a409298410646407002400745206140350f4030041c41c7c503000c0d5403811810b03a5202d04056803070185c1c2c4480c900d9010f410380100100080c81d8001d203800000680b00450700240d64880026109000d00d61801141740b0003826241c2e810107000e8401c40031411304085080041c0808030903007aa03003294512518280e02d9400d100058000c00580e8030052070320010b10303560b03922100b001e059060345410403401000800c0100b0b600c0c0344c034a00028500d2150042d41c0001041c0b1022445203c0010240841216a030f000816141201ea010382030290064504441140c1810710b010711001000800e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 877820341 1250 877819091 877819121
    0xa060816210506041a09010b0a0b0a020304120f020405100b12060d050604060507110703050a0f06090f140106090b01021c0e060a1d040e03040e0a060b0a080f090d0e130609020c0709 79
    0x7280230b065448100d90302c01d0b105500ea82c6a2504141103090345140320701d42201c06d4504507000e8803001c1000040e44114100d200703990900950300c405030710751420728090040002c4041c2c1400700e540d00d48140061181e10a400400301311103c00582c56903800c0c40019502594403e448108004609030001d01c1890113009101c014803601c1d08d1030311071588600590713070700030048500310400720180042503700d9066182c0008140e120602580340c409c520100c901c82240c2154200000001d021155100300c50780603806070050302d11282c4184ca0300c03006882050200c401e1024011403200180c070b8150280014600a40740d40800d811a1450203400391080d00200d4466420800344404a41010059404440303811a2600c101e85812800f08040c283d550001c8807400b00210394200c0640c1d000012500441d1040d180f40c0d110b803940444961502d4001c0781d0040452180300b150500341c2401d603c0d81114032a100c5c0c000a00e2901c516548069a2240c940200217500101e000d202e20b90051080e0240000120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 877821591 1250 877820341 877820351
    0x70510090b041a06280b0c0703050601060813110111010f0207031701060c080307030603050a030c061d0c1005070204180210020d0806041812080a060816210506041a0901 74
    0x6000601c035130085901c1c0c40c45d038903a0680c0c500c586400d951480b90140803050724141c0c0b140c1d0034224499072000b6a200035196071142000016186025103445806088a1003403261120740a03220801c07005010032549041020701500b001070084203118405114452910150355030500e4200100162940c0040c402d04500440c010840c1e40c2e005024180c2030b80c2c0c0b20800310b45070b544845c41070300180116400503080d8020768541c04109644113a0110780d203031083c041002400480360208d0240300311281c51004950180e0301e000300501e40030030003031000441854086c0c90481160301213400d40c4c07400908a42d4200184c50303814210320b07003a0201112030034584000c110700e5501c3d001c000d24402010344190300441c1c0c0d8140c880421840748500d0013002b80c000c410094004034030b001c010490b1008503038402e40140742010100e00da04011400c481d06900c403070000a003e0f0b0801415909042006007803944a20000c0c141a000400a0218500c102e0040c560200070100c01c801800c2003040041818000d64501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 877822841 1250 877821591 877821601
    0x512010b030a0f0219030b04031202030403020c040f0f1404060b1e150c01090c050102010c110309040b0f09010308040305101b11010e071410140f070510090b041a 71
    0x110b0224881d044001e02c6280085400482c3c610500000082400680e5440c04010300108848103801b80303100b583c40c2e01c9035440500008089000a40d0000e0068006c050801d50f589050f400000c3d5801c0303284400140d45902c0c1c51785101303c0741c03004d03005400c480b0003030108814404c0c14400c582c40c0750f0013604c40c0103003410400100c10303c3e00082c8009920584030b288408060100410540f60010354030740082081c2d07405800d00445030303191ba00c13030f840c015800d000504420611510101415203c0c101c01981400040801c100180030b2042020390440d84541d142c10b00b0740e903103100300c41c025800780c4460b0b9695411810404d0404030544210040103050042c00b0a241305c0940e40703c40c2d20030a1786484040d0b000002e0f002d41c050410a00c4010076841000742c0840c4d0703141c442928101444049401c0c1c02c40e150f1015064903034104994032236404500c20702001248101072402400d10504c1030040d680740050b66074140b01124503184098410036180c004003c100100e0000042000b5880c14802c0b40510f82 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 877824091 1250 877822841 877822843
    0x2802040b04150b1c0c020a0525090209150f0d06050103060b030601030c0e030d02010c17070e12010f020a0804150b060d020901030f060602030a090605030613090503090405040c0512010b03 82
    0x41c610a0041c020300020300c0502c030b00c800d406400112000c501090114441760b1500030b58030741100314242c419008081404d00280222000380c10121780044128000a10302041180250442c104032600000078201d480328000494000744498540700180944404103036005c1c20480e20710780c10450502d86000c01c144030307036440700d0190381d80002c0900e8049805e8041c103c08541e000e1150038940d402d0312402101c20001ca1b019040b503480030003141d8800080090100003c1c0c40220305a4980003c03400c550320034400381c05c204800700d0041d01581e0010809075600400038080764450490000052200c01c28401001410f44220b161164142014441640c602000868174890000c00d200c4e21a800a460852a4000c4d04401901e00366110700b080071a40d12040603440f5800760103050300080e995007000c0344560046056078051600600f88090800020804400400c0c02c0327481503505120a010055035582d5a02549224510480c2c45420300c1d8540010f00891070800a0b0740c8034140d062400c400242c2d00c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 877825341 1250 877824091 877824131
    0x10b03040f02130f0f0203180a0c03030309051203011805010803090901060f0c080f031f1d060d1b050a0b0a2c0306070c050d09080307020405092802040b04 68
    0x1d0110751414030051a1101c2000030100c0c03404d130005003800d141c0550b0035840b581c2c2c0070f18821700e440c844860251100c5400b0540b600d00e004001045245494801d00100e032081d805011507911840c1100e04c160000c9502000d00e81099000e0483d0a400380d8a01c2c2442d2043d0280340c1c010444078004600b400d1465002450f0308a050040074104422841c0e2440c0b00303807040a00301121a00001400e9840c02c01441c8080103510445030903c60320b2480034041009511600040c0441c1d00c0d000c00b015001c038a8080201c410840a0b00c1c0701d41c01009542d08001141c159002c2c0302c00c1c0400209002c0256281100b4000f0000060740051203051052017426030390340c3c0054040c2482c003a0030803840c07508001c1807205000c102021401075090310540040000c80c82c0c2008050f82c0482c0110101c0707031000e000c40385c00c0b14803008038081c01c45d0780c1c1c1080c0300c4940103040c250040c03504480d805003514510150303c9100d00b02c980ca20101c0c2190329000d6031505055051520070200d800300c081d18140310b000b142d03280800f8180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 877826591 1250 877825341 877825343
    0x30c0702031b062b150f300615090504260409021309020f0403030e0301020f16030201060320090108011503081c05181c1d0d05190308010b03040f 64
    0x201c0410500405443c1c4c40411150070b15490b007040000444c4040c0c202c40300d0717034103001e0a26018202400401c0103010001241c902c0c16544e90500c401541c406400f48a161300038004458103925160460301a4800c00c0340d0300060020318800190034034041c01e040340321103281c1c0c080202c02e02c26030f4003003c101d02418003100c00752448050050313070b20f1004482c0c465102426900030b81e2414800304804018004000080040324040e0341d913040e100c0102c4081500300d110b00c001e190b00c0b9a00c00c1054040c1a910000c80f800080d029000001c0d0003a500e8960b402a040050070a510000380c90850340d1541c41c0c0340c00045d01520f8500020004e201c60070b4000b514070040c0d40405044042c4c0030600012403001100f4905120030400310a00081c02c00c000b049050b0103d003103059000c3e01902e0314180700c1c00d525001038094000d4039074480c0008916440c054001d11003d90030340b900401e18080c400049141080001c6461000c10004c0200d5071490030010724a001c10703000002849020230074003022441841c41c0101b21 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 877827841 1250 877826591 877826617
    0x50a0903081501080601030e0a061505120d0915110a06051e0f1b0d060b04030c2727050d0201050702060106020705010815031911040c0915090803030c0702031b06 71
    0x20b08e034800c450134a44a00d03c00020006e505220041403400f141a003903504851090742c603c1c602c03529800c001c5440b2544454070070001030a401c4104841d40e07500c1816104d05d02a401c008a183e140903032098108040c0310030907101c01d521441480011140c000340c481e519108040c4100303150410341c001d0680314502401d101003104400d442c2d003405250200494044c1040400c08100b0140d071072801e91090303042807000340c4031004c102d00d0002d50a48a40c150708002c0c1e44200401d03007040850840f09006044203150740105001c00c1504100c0760b20403241c0503850070b0089000381110006800001e080d81c1d0014005c400f1508100010090990009480c80940d2030900380002a580c0e02000e000580c215944003550501c0f5040004511606220b034a1601c00c0c068500d840100700b507041440190f40c9400c0072100089c00c0c1000421654000c110b00707980300c100b07620340345281a13600c004161654105440c0780710b42c80c0d4006104000c51070104100600d1000c0e00c225140110507800c0040c41e01c0c0104007810900c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 877829091 1250 877827841 877827851
    0x11e030609140f01140c121b0408030a05032a0d0b0f10170705040609032d0b19110703050c0f030d0c0318080405120c04050a090308150108060103 64
    0x80015600c52a00c80c0400c82d02100d032088580c0b00d0b12406009440540d4403c2d03070a8001141b40080c0c01c1085403800041440c05954070303110201c000701310a02c08450900e00ca00d0a00001c100340a0501c018184806299150740d100e0603d10300e405c581c1d581d071641d00400402c41804d00c0a89100c16004c0da940d18140c40700010301e441c00303540400e904892026a15030f10085000ba000d0083c2c2e000462030b42d010704540344150700c668a0410964462145008110101d080d844c0204005021407000521090303d075540c04500c1c414481d000002c86101d81c5040710f040c03140300c0810100e00046204034038810894a0180200c0e803d400c8040e8480c85603070809401c100e0009804031180500300039410504184c1c50442c0d0b03031441014a10002031045081843c0000c1c03c109030841c20780b1541c1c04c5100045d40140c80545001e01d01800c1001c181c504051843d941d0091182240c906d503214450300d80310b080024004a6400c0c00c52074000c0c4006001081d883c1d00761241e81d03c074007459a020007400da01080c03c1c02c1c0019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 877830341 1250 877829091 877829093
    0xa0b0a03150306060602100507140a0203040f2706060e06030606070218070e01031e0e1e0d090e1e060d14010c030506090103080a0e06190c0209011e030609 68
    0x50001d41107104402424400c000040220b154890340494484d0340c291035500c00b00d40001002d80e141035030b11744005003642c07400b01c44105005c002060b00601900440e80341c41d40d5507108100e040c480d58841501d400c800200035214070400c602030224424480803c00009040ca08050407110b088001e07079005260200000341c0d20b0b00d0301000c5503103840e00100381a40d1569080880c5504070340071540b15000549401485c08594028015501c5050504045882140700760b0703207810003480307954088074032403180b103100c241c0010070884c8241c0007200c280094504031501140160401c06203038003001418020710204184606816a44280119040c0100e1034607120240068807580c410b80703015020840b5442154000c000560001c01c002607c2d40b001d11242c0c0c0e80c0810020340600900c0f000e084410100b007100c26140c494070b040704122000400e244e06003a0815504043c07041c003405c0311000b2402001d03c4109524204000364014400da60050220042805091032146c0c0703c1d2000074100d03601c0790784d888 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 877831591 1250 877830341 877830347
    0x30a051009091101030f0902010e091012050a05010c09081f0608010c0914030601061d01090f0b03040605181005150603042319020d03090e0c0c0f0102090a0b0a 70
    0x10041c6800e0318248100d8816050a00700d8506110650740400c1c5802da1743c0740f658006006100015805841d07100ca042c84407428400c00c450014a050306005080501280c0002100d1499901a0180000345a280300d2460002d0031100340c11901e0052000240b420807101d44005407445880c0e803d0040c411031801c4004284000c0e10039034000f4080365081c014146102c3e580f0000410444000700d01a40703070700c6103100034581c032240280944c400140209060311400a80f0008540d9409811b00d40360b0840360351707400c84420b100300c1d43e00300c0b4880e42c0c0000184001d100c098003450380c22404100740c074640c0030500c001880c0d580c0c400340b807a0342040ea2120700042e41c42c0d8508484003c0c00324007030301d8150340c0d2038645020200c072503510712045044c1ea49449810b41c5000c000600301120803040e0840046000242c00704042d1040d540c01c102d080180c05039002c41d00d2841e0000f070034020350701c2c002303a540c0302c9442c4214641000500720300e440c01603105100d00c807004d070340d00c41c2104116000a505aaa0f621300ac1c1422 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 877832841 1250 877831591 877831621
    0x7020109080609010e0c0a0605030f04050c06042303010507050313030905030115051c0201051c0b031005150d0f0b130c0308040608060f0f0105090301020c010e06040201090812030a05 80
    0x241d21900407407040211154064201e00113140f45901038a404e8464101000b2031050540a05000504280001509901081d503029046402503003200c0040040d17000280c00caa0140d000b1289076a0b20b0040385410208900724000c51045c110024031461420120060050000506200c014803a0450400606000794254070103407a0190091102d000b034400c0b50b0403c4101446914021504041c0d041454031490010480e0340c3d5050355100c0c90009818040e11400c80800e203030214156441d40c00c1072095404126078940c804412a0100d8507191100540c0d0402030410b00da24040e00358110701100191044049855440e03000714521015181c690310021100c00700400106100e21411020082c81901c101400803900c42e030b83e604070b00307541e59824060921480007209400207005800403402d980580064180200c01400050400e01e40d54442e0342540c104054207a4a90001d0040c0000e42d40e0003010344016017580401040d4080d046200741c515840000d1544c5017840ea10804100100031409035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 877834091 1250 877832841 877832849
    0x108101d060a080d120908090301050f06030d0203280207050d0803090c040204060c0f020f0a0902040512030309031b2b030e0c0a051509030a0503120a020301030c0b07020109 76
    0x12480c521500d844120392048010348040d44206100341c00025034260018a22030050302c960f071505101c0c1c440c0e181500c0a030044840c02c459242e018400d440c03003510242310b064410540c2c6000e40c162414600c0c2030509012441d030320b40085400410111103280408201d000001d07504500706500e4000030340040341041141c8d00b2499001540e0515007003480000000b139401080c1600546803a1078400007080200c0c420342c400c09011030300d00460303280801e12110a0410707150000d42289c0e40f101e5844009100540306400070302a250f80030030117001c0340c100041200c21130f48061004500d942000000e440e070340d02401c40300f0002003009491000c2151018000600d6000811320141955800746103000422003800c07440d00001303803802d01d0007a03811900284141c0c0e00d640145c5411143c42c149803d00c443c103d43c1d40f6104020040400601005031020442450300342c0c001e1001c2c0d9150390039000112100c200150840901ca8010b0005001045058244104480601020a50761001e41c03005982c0d0209580c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 877835341 1250 877834091 877834109
    0x70e0a0f060c060603170d0609050411060c0c0a06030c0e0303031b070f060207210c02095a01030c23030a060b0f040504051207080408030a050406030f09030806010810 73
    0xd404031b0445100009420b00c01070b5040288030306034840400c0000c51708101c80107840b0300310a03404817a050521070700a001e00202d51080d6140740e424800490842159588800002655402c18000d49039101d0710502211030101c01540c51824000d080082d240340c03111104181690000d03803c0108850b03600f0311a40587d1115056441da09103052041d0b440c0410554261903200000590601c0c600c00c01540c049664000c290301002c1e120042c0c50034810001032803001c0c4038086035940f0f001e00100300300800c88a00d003151190b155510031001c0392030070382400c0e040031420300721700c1e401840020144040700b003c0c2c9020104000508440c40c41e0001080901038200d505400340c15415410b012007a040b001c010300f41030300c10108440018003800200c450440700940150000580c803c94401103800514910380100050b905058450768201c0c00c0d0f42c0092405c00101c0c0002808200032a098010000c04106c42c0070200102d1545403000b41a50702c00803c40c50401949000046051541c0c46403030000d0a4801c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 877836591 1250 877835341 877835363
    0x60703030b0126040b0109091a1e090307060c020d050a03020d06030f0b1b0906040510110d050c0106170c091f0f03170a0f0806031f05070e0a0f060c060603 68
    0x102850700785200c26101594611100c000118000f04107024814400d40d1050702252100d18600200301c1192018141d40b00303042c400c00007032b080d0b0700d1140f00d03290140700258082c2d5910f84043c9001d504551241c0c003410203640040365a030414940082c2920b03a02c29041c02c0240c0c1d20034144040900400c442d03080102100820303484101440502c40b1030324480d4104603d20314151040c4030140c041400341c3e840c21640050208400d0005041c10a02529645800e0400c5050300400b00000c078104501c150504002a001041014601c01c1c240103c03401402c54006031801410742c40c4100d07450b00c0c19903003c14000e00e416000325004a1800800c5200c400d4100e541401d190303102c000d11a0800c1062109032100040607500c40441038005c4111040710805440b080c5002280480542e43e0f000028405a81805025520341011000084202000765407030b20006961510860261000d4024200a8052003060f541800003041d00007081d000d9502d2810b02508608007803800340c000d070040d508000c1c5010000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 877837841 1250 877836591 877836647
    0x2030d0504230303060a21050a030c03020c060702010801270f0e1e0312090a0203011803120c080714040803120f0a0e0a030e030a05060709080706020c060703030b01 72
    0x1801c000d9181c2ea4200c0d0008044101a240c0c83d941c1d01058444544c40010500704000c503403000c0b03800900958010489401c48034241e1121410400702c2d4a0640100d049586620201a0305102e0704841281c21100d06040c0308103a0002058240140610f00c1c4250480700841c440c4800f48250400c00d0100110520185e01600382c1a0040c0110f484440504c0c070a1400c40002d018514050003110381c201002103040112071603126801c0c500140111001e0b00130b4090250150b1400e016400095500d2401080041164600180b1030891030032424116417512039003202140d40020015001409450042e61359603840401960394400c036400103900780300016135106003d42003114944500764062800343c0a80c0d42c031032440107480198022000d01c2d0401660100060b0050195000841000e01128040341c4140e5a5a107003500540b1190042841b0543c100281841004240c0c094507892001d81216180719010030958014510024180764407113101d0552039118a072180c3d41d281460800105081c64 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 877839091 1250 877837841 877837853
    0x7093803041b061d060414061c1a010e01051204060c11070807060810210602040e0901060311060a080c030703150603090507090605031f0b12010f05060a032102030d0504 74
    0x40040040c91610104c440d030b800314174005003a05c00f12105442038404c003081500401809a0080000402c4e0342813500741c28100d001c0078490b520701c503d5000000000b01900c100050302600310800c00d18108401002056100c1e05508002900130354040000304504649040c02d4488003c0445004510700c0303484130010780c82800081480895096403580ea0050320344004190f40f014481c040c8042d002440c491500f40498015111000345005000c01424561280480000540705a80d01c8105a449003411710922030326190075913800f0422910306203840c400150240210000420301501e003031000c000100100d0080d006214120060f209500806440c0c07440640100003410060320305100f160310204402110703100f52415103400400803c00111440480c00d0702c1c450345004140c80c192264405513164803050b0300408041044d03c0042407518019403550100c820041145114015040341040450801d0210740700c0d110f48014100f000d0b060130130f0240d196105800c0001210f0389400b0401044c401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 877840341 1250 877839091 877839107
    0x8040e010e040809101e0215060f061c110703020f161206020c010e0609070f0e07090b130512070303140901051909120807020405160e040c02120307093803041b06 71
    0xc0843d0300c0c000c035803546418041145003ca22b4241c11000822000c5080d8594062a42c1492001c00340802c82c03007200d07030740c411541c0c010744004c1b030140e03000c80f42e541e00036a001d01ca2101403900702202c3d07029062402020b0a03541d8400200a4170b0f4a40c0011800100c40e001c0d040201d0026090003116400d0804616a90380d42601e84140800e0002d241030200340d035800142e205005905030790340c07030f1181d5080c0910010395a11060440015907851000040c80d521029038001f1604c002d080640001c2e80f942c1005849541c81554507660600100036054050fa04081070340d07085e48401c001d10301c220428060a40b035492068001424021300038019800f006003683c02403070350520a5a050000e5102d0100b101d10f055191489540858000200100141001d07031201c410009948111040034400000c075480c036500a4680c2d07400a65003079000d00c0b0300d14422a500640d00d040180b103115000e0b20f240521003602c20fa01250905410001c00310b0203104008442c10703002c810000342c91440e90394a40000e00042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 877841591 1250 877840341 877840363
    0x8390f060705071112031902032502030601060c03110601030b0403030c0309170d02040f1203140f0a1d220507020d020303040204240308040e010e040809101e02 70
    0x40305180c002400244990b05aa40b501e03880201c0011628022041104824038000040300f6448180aa00c42c1c49000c552480107002d0903030041c65640e00c2c101040d00c20b05a00d154600e0303401940418070f0006880001d2858116034880c80d0030700e9418503a10b0119980c1104903003802a07442030703000110900204001e41c80c0a0ba210351001c20040ca21020f040c1c040d100c0d624800740c0350110000079401c050384084018964261301d61401440c1640703401007441c21031107941000f500004003d41c80c0c002c1541000200200c1104440ca6a0521845400c6412240324201c2c3d500100409141c000060002ca80044044410000c100807405130020540c0403400b51001022074603d402d14010030300c001e001284041040c54154051441c654076034091001400c41590741c90007550002c141702c84a041810b003001c0141d031240065940d0f0724a000c070021202c01c8180c02040c4185290014000001c01c107a00700c4940724800d0340d0008800c01894000e4681c04101e0103400747c062804c850f0f200700254003242d035481c04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 877842841 1250 877841591 877841593
    0x905060111071715040f03030522200306102d030807020a171b060706050403020708100b01050a180b040906030204052412011803030212090a08390f 65
    0x85504c41d11984040c000556020b0714003c15124800d0110b4400d4101c030750f22040e0750454803c100b1180c0e1400160543e102030607544502110507440e4107039442d500416003218210001e146070304040c2410f1120340140e11034820140030490b440c0f039070307508004142d41c00d6076604003001ea03d141c1d4a003003400c01c581c0310020480c800c000c2c0420124100c10305a4006554089070300c000c1800e4100f0f203040c568042c245282d25036000300b040c2b249100140072401428802e91190b03014242c1181380098051900111140702503141e0701340b40240c4080e17640001550502c4515243c40d2000c00410b003070100000308240c1040c0310803100041c01290302d811581040381244c3c401d0b5000c01840e5a5442590b200314000d0810100d00080a01800064030309984000c2c1120440c170300000b040d00a83c46500300c0e11355047d900b04d0201c1d80200307074000b501c91048905035000c400c110180200c0c10066841c02e059106120b0400c81200c1d28080b540e000700e190001103040543e1520700d0a00444461000c156102054100709600e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 877844091 1250 877842841 877842853
    0x71103180916050306040b0a030b090109050d020601060e09040f1505060f060c0307080327010b040b010e03060714130f0e071403010509061c110907110709050601110717 74
    0x5032407460688440100015a01e084c1182c851004103c0982010f102150b4010301231600480404c981514a83c0540c11035800006c200c5441c3c503241d402c02000c0c4081c40c05540000004001c00b50700f1050700c80400e0300440b86001c1030780d03ca10300003040000ba000007074907188020303407180707510078aa0348194012b9000300ca180c81c0e00030703d01c02048164415400c1d0f0100a400c24001e000c00950500f003e5600500c4480402c0c0d0740d0001c1e02c0003c1008241031000c403120303030345800e05c449440c20240700345511400b080c642011015130240200796110006402c0304108080002c818103000d201c003040d45d2142e410729103020300c40e43e512203803051501e090f8000e2821a0316480086504076000383d504a501c403100304a090700750784c0780108001003005d00405242d000000f08070350a0000040c0044c2c461154031410f25100100b008000744a0b1901000b8811070a124800d00c1c440d602c41720004401e011185155008950b41d41c401004907180740751010000000d11075036801050075003c81a01c600d502c0c510100f1694 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 877845341 1250 877844091 877844101
    0x709050910180c030902130b0a0f0605120c190206090d180312230d060503010c2c150c010c030908091c170d05060d05150711031809 58
    0x640e1840d0702c252500002c0502034000440c0c280d4101c060310200070b04001034242142d80108403099615268245030031703078802200090785001d208800181c466036010303240c80d07828039402070b2240c45507040c65100c202d01c0d02c0c00198210b25100c111000015200d00e003000040502c10045c4d640c040950701312410f400b520f242c001341d0320310031b4100241700030240520250413450f54442d00c0b10300c0d51103895a000c010446c0b1101c07880c08000c1e050b814a04800708140c90f940c00134101500c044407444e4201c13910a07418058a20010390344044040c801c117054000041442c0c2c2211880100303010b1089815800151212120705004c1c10034010381000e2400c04024007201c0c40511046007207074040b0000401e44401440986840e040c03031110241c010100031607181247c8602d0b100c1002c000011510075041a0000508850502d040e00905d41c224000303450b00c54903109141d43d4140c403810a1201281c613031101c01e0006107803074030410800c9850a030850950b6511540303c0007180b2180303100c2e8006d0740140b00a0002c54 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 877846591 1250 877845341 877845361
    0x2040909030201180519140610091a090601121e0506190608010e0406020d110405011b1a060102100e010b0907020c10110307080c0309031e030304110d080307090509 72
    0x504159214002d0415201b0b020240d0120781c1d400380d820759400300204044c1115150800020340604018480708a070981383c41401d80c107590011000c409165031142503000d80d91110258903402c04001d08041c2c00203490703107640c440203000d00050004c24204540351480e040d010ba6105130700544040d50b401094030b00d4010030034003480c1d2911036500001d03050b030010805156269405034000b4440c030300c05890b140801286405444481c2c400c45220783c0c000130304004640c0c01142610442d219045580c420b4046525005c40d40002d90540d01c805411050028085038401d0010705402007060008100815403070b281c0c01e009000c0401e0250042114a0108907100d000080c0030300b039850b0040010682459901044860790104080c3c00305600c070500c00e220000355a10003401d10810290015512800c160041601d020010541010301d44039100e241e01c000d41c000310450341d105801c000145115070902c80400e201c04a902c10103090014040180441c0300e6101407044222042107480d1056903c601b00c0030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 877847841 1250 877846591 877846631
    0x1030b01060306150503060105074d0105040506070309030206030a02070b15030c0118080a0302060a060e0613050705040f0803120f1e180601060f020601080114070e120102040909030201 81
    0x81010170b4081c000107055601c200000c25549206401d0a0040071022030041d0690b003c50381040039001103a40030704143e0390405000709031980081202e2031140381c0c150001e0042d110f01d001c3c20340101800110802498000c0c012040259030191546650b0b241c5900700c4002500b1515084501644020105688000910150070842c034000c01400300a0b9400c401540d40b4094400d8078030f1483c1064200042080091000305c80b00c030300a401030041403234400e0014040356282e070001503e2600c20b074144180e41e02d40180029008800000001d065180d02d8420394050081fa404606055108140402c00b4030010010f0300c03050310b400d40c1803001c6480340d04020400c5041110050412084c42c5414969580340f4241d40f9003086c060000c004030700c00403030141428010241c00031004100380720850510103504000603401080403d008000c8801c10341e03550040407001078580000c024512800d503105982c0e40407031100301403242c4000c42d6656921200080a802120426400355180500d020019130303400b000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 877849091 1250 877847841 877847879
    0x1b04060518060910120e07060e03070e041e0804051017070e060306040207020a0b0a0806100906050f0a1b050c190302060d0518070e16170f1e01030b01060306 69
    0x80612144001c0c681285d1050a0203110304074652100304a18070840d0034400c0c4009000d45558041410903980c0c245880d10352213912560303580e2900010040451403610744002d00d1900c0c48018509a0400c5c00c142c082030055400455200f45130b180882c1803075400218030004a8800d0505046a0340c6500c4c3c10740e0074001c400420303a00600c08000080c01850594020000b0344d1008201c0340d05251103481c0b46100d500310510780300200d881001031000350300c0e2076030054000024524000d4145c5080c41c00040060003046101d4030750400108980c6d440900a000d445100d510740402900f60322002d0038131a0703581d24408a000c0c050800c4115911500d0b0100f1440b80030b494001c1c1c078440c503004140050300001d040c020034660200c00f901d0402500500305000c071000400e07040d503142e21903003065184a003400c00701000b41018010300090b0803008000000716941e0058400c00901620350b03890b000b41801c149a000003400c2d10206c1c0d00048101320b80701c1043c50603140e860b0b0342089000c0d01d50194405050704005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 877850341 1250 877849091 877849099
    0x60901060509010908100b040e03040810150803030907030615081203070203071a040203061608070c020102160608090708010e0a0f081c0c110d171b040605180609 71
    0x4014801580110010841c900061401c5a007555507502d5880c103100c1c0395440001c08a4543c403600b030052400d40614541c5103500c0010b140f9041c94a41d92560340d4a603905007094050f11040c0c0c141001d100528100d00400340d1b00e081d00c1ea00e1518178815920f9408501040b1002458501d0400f4843d11110304607040d40d9030400188440314201e03821000740e402c018048021480100040000106072a002100b005c0071030341c3c01d03a02e41c1440d10415080910041000a4820221300b050242d554404540b5030410384e68188039109038400d00040f401d040f00c1880c08240211840c400240117903029803c1d500c03894603541a42c12107900e620b02c1a00b61550700421140c1980000c04800100300c0d507107a444540c078440c0b0800351038445c0301980d9031400b01c21101b100c4019692090a061030700d8120a848503c2d20903603000d0701881c0441000641011840000070b82e035a048000010540c00203064200079481140140742e440300d54425009103183d0040e02d9001c2040b9422083c1120307820100c00361204468014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 877851591 1250 877850341 877850359
    0xe060315270f030a090303170f22141e070303142b0c0e010c0b01061202120a0606020d02010e070902071b1e0506030f0a020901050c07060c03140306 65
    0x1540104070360200301400040c0c010b011080503003100c108002c2c02000e100c1d80354082814518200a0704125642d0450111740c00000100640b00c1e004003000d60784100100a008110030b1a950365140e03001540c40014101043c0c03681e01080c0da01c00052001d480841400c041c15500349140d101070f101c41c0f10303100c0200802c101c2044c0d00526202d6901500d0242003410320b0020800025690641204d0303010040c031700c2c840d030b01c0c40805080c56014403a14105002801d003100307441203a41d01d17690112014411001000203296600d51070344503940484646d0366480d4548a0300e03050040741c00000b04124803c1c1c1d07015108a98520354824010300800c100c8a10342000344c001a8a081c607414044e602c26202110807400180c2041c40c01800d0741082e10240c4007600300001c882c010b5941740014428650070a03481544140200710445a0590800d50f0000e40200090303118030055006858600035001007103a01d0190f1707035000c12180c7d407251030306a54a010b9500c104150310000c00300b000511040d110316400c20112 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 877852841 1250 877851591 877851631
    0x504141507030302210a0203220f080c0106120c05090115050307080601090e150f0a0530031b281b0f06031b1701030b1902040e060315 59
    0x36030261110307004181c03605c5544201d0340310300d8840050484132186019030201c10701860090035941024901c4204448040302400f58a41c4030224800f82c100602005002451942c045420742044005040c01027201c500d08245240004034940035000303150103071a074000002a2040d0325200d61418400d03d8896a16588403003000f00d4001c1d030018002c0303040c404451000030302180c42010481c0306e405500c00c03e003101003060f407c01542e03410040046104080030380701071016070388540c00503451426a40c0081c2140c03041800c80b1031120100307078100c60f65010104004010007000340d40b0042c8200507400b9100c3c041808030b48000f58100d030281c403c207030400a40e824000a4601c030342c0484c04213100c031400301000d591079070910303c0c00540d50005400a40c94040314403214400c0202443e2710105400c05460a62050107104c0d8511014032001e40300034405408285000341200100b034075040c42c844d065654945a0410421100058814a0182c131491180462111008058901504050a00070008446 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 877854091 1250 877852841 877852847
    0x60e151e06040509091605010e060d0203090a021f090902030c0f030717070207050f09090c01120905071d060307030309060c02030c030703032304060e060a020a0c06050414150703 78
    0x641041d4101c40200701c049110703500c160b1082e1184890900400c0b260030424003032054800315074081030500c0441200c5101e503239a1041601c0c008440041d0040c0c490380c60014041c80d080ba1180060742150b581c44d4020441444040144460340150321a170b43c6207a500e003202e4080740320803103c065034503200344080c480070f0070910700564200c4513502e000091540303440406040c0403400c3c1c070840c0150303000240c00c00c12424010500106407a0413101c41c0041d1800c6180c2c41d4480c0300400c881030400c040020355180d010159841a4041c60300982140d007400d44444546000101070700b00041d00c0f2002c03400003051850000740410540e81c1c195a0044410b241400549e80548904000c1380d25004903066420941c904020381c00c0118004ea035880c408803402c00c04c10007a080d106141c01c0480740d0400040c4081600700441c02d41d52001034440e107035030303140540c412414986180b6004050f0b4900c135000241c1954441d000e4015141c00c28600b20117240340358100005c0400000c0c0d0030721001000d000003008240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 877855341 1250 877854091 877854139
    0x1205130b030601095301090c091d0a03080f13020f041503060203100306050705030f01030f1505070c03110312041401020c0f011a1203070215040801020a03060e15 71
    0x12000e6180386010010f02e203124504d1464007a85c281d0720190444c0c441c40d900032420b41030480490a40200955019038440019000c928058200d00b2500c80081054065841c803e00c00342c1104042030307134959031035460002c143c2c0c8016600384c41c0e20360071031000c02c0c0b0508074084020720f0940d00a15540700c100500081c040604040c50b6140501a0882c0c2d0000c0442c0752400118440c411500c032004c0070070305600d0060111100900007004001041c0100408146d050640d941902e4100b072225128541a01c0e08a007500c042070822a504c60425081c008507581112112100c81d10035100c0135070300c10103101c82507624000c0a940e60300c03241c00d20000c02d01064140a0340403981c1c0403800091f03d40507914101070314206808140c0c04481c0c0d074654402801d0100f104543e03528903400c480c08000c0c0400c2ca101207640c5d004250020307100c0d200686002810b500d5144c100d030014104807000395202d41400c007018000380014460401c60b2001100002d01420300203040506400700181420315140e00c0344071160800e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 877856591 1250 877855341 877855379
    0x60f030b061c06050423041e02121c03021305040b030f0a0506071b08070813050301152402120a0207050a030809210303070c030c1205130b03060109 65
    0x107102088100c41d0002c405a4410200d00c08100220b042450301043c08211401444403070705003084d90843e1070300c04268a8a0541250300240440c3e02d124040030301c01001030345900003d48c0030704600c00340905001b0200301d010080480c50700c04144102d80000c00d40580c41900800d40801e14110801d201c6441c19500030f40c04860043e003168000700250401b5464076103d480700780e401c0d600401c100301440307a121084440351803003110000c00c950381e5a41c0c2d014031400740c6140104842d0000c200c040701d00304c400280d54000c10f0014000c0c40420303c0c607000e000141042d400f4181c4445002045664002810760781400b07072004550040030100b0b0428058145a081408150308602818a0028081d036456044101450181498503540c40340d0600300a490880462441800e44010100140e01070010055030b90144031030520b900344245524046402106101005040801c2543c02c0d045296004018020700507426944120b20340d100c210840b09801708071a5903000a1016030107200722085041002c00c0c0b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 877857841 1250 877856591 877856599
    0x11707031a030703030315060201061d04030e130614090f0c030612030f04140103090c03061a090c03060405100e0a020a031e0e100902210f0d05030f10060f030b 70
    0x603841c50001e403c0c08216070040c2c000903291054041586c1505002c0d10007030403203000070007040e443d0600d043c260a0045104607804c0744200000703000d141c010811814500d10040042c040c4007035034070f007136001440b881c02540a40328400c0c40e101c00d00d04088110601450407070f108112035558188404120f0f40c40145223581003150000c1e00c4031441000c10241c4001585034010a8446041201460303001c0520407501d810036040074100c00100d883c4020f481d0a1f250050b20108a4101d000030500f1404d0540c0011900a01c03484100030840250501850144104132030520980c1c40700c510340c42c2d80c0a0a03008034580b001d030003804507040b030305194020704d4808000d081c041102c501c2018900c0c0388454460401d1016500c50102030360b02142800303070b094101c0f4480400c00111156802141e02c0140300d240842d022128042011502d030001c105401c0c2c040fa0140890f084a005084010b12541080c0c0e1000750400d00b150100c0e96000141000760142d0f0041e03500ea0408003010203045015040c25280c142e00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 877859091 1250 877857841 877857881
    0x21210c02031c082404050615360102060a1512030f020f031903090c0e2a030c0d1a09010b0408060f07020c090919060c030b01170703 58
    0x1a10180048040c0d00078060b22006074044400b00034200e500e009001c10320040314070003880c54016442d03503501d10000c82a00c00041c2da941e0301d0042140120904905c400710b450104554000c03c0702c1c031840c0f515440340e581498100030408080c0704606140d12101d24007581044001440c10403140c0d0203a5101d185d0945403000b81591004100340381c60200400380c0004810901c40d00000350108842c11208907000015880c142610a240c2d9081100d100654101519203114100348034941403c0000b501c40c5605450042c2000320301c040c080160440d41200d42108000240c0c42011000141d0b8415060380c01c409142c05044000100101000e440420315080984065502a103a000480380600343d42031011340c0c0c030350030540d1141c03900e03200074002d0101070460002c11654580c081507404a01d08140c4d8085066198040454201000c0c5010341e20b086007100404018130005402005080b0f00c55103080040041300d41c0112602141220002e0060108502081040e4800d600c000d000c044081c8000c4a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 877860341 1250 877859091 877859093
    0x3190804030b07030f090c030204050f0702211213021005040509010927050609010605330f07110a082b02010b030f0c030105010e0106090e07030609140121210c 70
    0x12a12100350031f50b1039401c3c07000c05000710704052240641025021090501901d0060f1000350780d01903d04521144280e51901411404070007030a4030b4814410501d00c903d01d180c51505d0700203400c0541b80a034410441440404d98060195003207a040e2100645000d071603a0a0a12010141c00d0140c008004910782180e0703c80c0c000300506841003031511500180c40c0c0f90801d01c403100d0968510303401071807041da08a001010320f034044400443d0440351041b0f180840d040c0f8000301c064a40a80e01714403072221400074029041080c0c81201c1c1c40744078400c940040105071079199160b80da00b415409100c440f4542c81040030603c8482c80356040ca21810f1001240d14480d1102103070034120f01c0000499241d01561f0501d580703103020300801d400740042407900003840d85410001420040305220351000350440f28040380305140f0a42000002d403e0044040c00031003541e01000070401001d1060325480c0400440c1c141d503400e0030341c0b10000306541103500c05048110440d0703c80d0b501e5500700c640700d00740300319410b10030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 877861591 1250 877860341 877860371
    0x3150d031704060501050a080705031009020303090306130b1b0a030e190c0311010201020a120218060f03040308071d060c150f0403084002190503190804030b0703 71
    0x244030303038400c3c4000b0840d9490101800700d10401500038041d2a00400300070f00c401c0c2ca00151b94100c05d8007481d008140d003106400400d00318445c1c0042c2d140c040c0103880410501c1030f5400703200d528091107800d0f004150b95451119021195100c035907a44c180c00100b200d1400c0c240710b41c200300c080c184011300b40c603068002001143c8111400100c21a128030240c9410030034000b2400c41d030140346100780000d40c82c0035800240145480400c4280d50b0b8a5a03010030702052040c0248510400f80001618080da51999050080720300d810854080303000802200001c0c5502d4030075140704100300340a05031402c031101c243c010000c45030000d00e0181c0c031511604d0340c10f00d189402da0005a00503019042d402c4840d080c1418000c080305001012001607140303900c0c559504139281110055a0100034405030b02038140842542420480241c000c4c0d80b0200700944103a414413032003484011210110100d82c1d61814285940320303110340c200000380801d207091100700049075080d0750f49603005004d0b01e000541c03911050458 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 877862841 1250 877861591 877861637
    0x12080a0201062301120902062d0708030a05090c01090b07060e01020d151505161401050c03060301060602060603030a0e0a0b04080c011418151c0903020c0603150d03 72
    0x5070040c081c3c0070790070340320b0b41d43c01660080c00750904500910401400c0e40100d0414801d0100002d08424229200c1d42c591411094041010144039491036460790103007054062900f00740c580c0f060403440c220214540345070000d014020150b068450809281c40e007100016550001103080d1006902c86a5a0380c88450a00c028041e24002c560700040d440c0840c0c6640c4070b5841c80740c002590780c1001703254203070b0802e80140076610341c01e403030f90840c290011080c07a252240c0100355100103469800c1c6000d101145001c0701c05144580026002007002c15600c490880c1d42d80f80030b40d2001d030150010086401994407d8040554030780b000b4195003400d6588840f501e1041d80140d22580d003541101e154440d10750307400a20481c6040f4454a10390500e400303c0e454010058030a1101485014200c0d5041400e00540c0b003519030540d204420812207080030b00142d00070748100c1c030045005002d12142d2141900e4210152806400e4840900b40601502000e0020041c100c070415400d00552001080184130f444e952 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 877864091 1250 877862841 877862879
    0x6050705091f021c080115112a03210c070503070e01030615080309040b040b12011406040e030403030f0c080417070510050706020d0b040c260112080a020106 69
    0x10030038044100c0310300203040c908001a0340134000d500c006003c00403580200d0460540300e4449090519050006040c0c0320501d110f030f188034041c0294000311000302032103613090403480740c40c010780600c91f2040810961940031505141c10f2102182400c0030418045070302600c1a80400c03412610220b864000080c642513150340111000703000c1c10014010840203005199410090400c0b500000341010315098403400380b00c20560259984101c5400c0e0f941d110380144007a220040d10041c601040480005e0292004610b001e10940720304020560500300b40c0f00d808401d80084000e141030a04641c1e00701c030414084003411017040450040707007004c00c05030401003008098040340003e00003843c220700390814006078086841280198070181c01160030804481c101507225100581d14030071031003820000c00d5141d10a0750001c1c038200154000702d402070102c6024050707030701101c90980c1180c03544c03440000d03003401000e0010503402c2c3c1540020398580081c020b407910740e000100318a41c864001c0550b10080341d03d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 877865341 1250 877864091 877864129
    0x1021902010b010801052d040c05180312030c13030b070518030609031c1d010c021911040b0105092e08040c0501081807030b01031e0507030605070509 66
    0xa410400a4092051155409081c2041c0d62550b2400d0b0000d15007003a46108401e0148001c50380c1242410918100d0036020360043c0204010521040010002d412030303a902d40d82136a500000580300c0c6000100e000c2c2b40300030000d001d491542c510316014001e40002901c41a00c020501e00400050100c0d1000342c0302d061150303a510380320400076042c0e611f14180361141d0350094106178248100d00202008079400020030440010340324441301e61400041c004260078070a0b0001034101e0002118064010f503040410550841d01c807102021440c003659404004010705295a00c0b80500040c14160030203040070310141855402c100200300440d2002107202081080c600011714507014040420400440e410158075100c00103190607510090000410301401341440b0080c80000d00b82503001c2040149401400f05550f07a0725540c3c58001051075080c04102e03801c5818290342c403030724941c040c890044a501301008040c424950f40394a4020300c0c01601000410008120340c00345916000318030045c0e072012107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 877866591 1250 877865341 877865377
    0x30703050d0b0607030c060b012304152c1c15060618051c0f0c060e010e030c0114040515030a18170c010915051503030423060c0102 58
    0x1510103000c4032002c4104510401042c0010800701e94007021288580e54444400141001141c0c01039400c001246940391410f030456813100031401804001d4401c4a623004140040c0340311485c0c098401002018161072000034100c41c1851526444d038100f220f005014040540482250045491409441c40103540302c030311a664a9003020100e205040081000b8034146640c6040b01081c00c03040c0d1114842e5a120b02c0c502e220900f840c7d401101d070030541c964000c20100000c0c545280c2004100c102d84201804100002030141c1103502a854252101c00014003405181c1c1c0d0150040d02c0d18841c101e1000004a8284000710b03007511403114000c0e005101d4689903860b440c1c1429140103490f011480100000528210080004c0c0c0d19040300c0c10700040703003140ca070312018058092401000c1101014003400c10000700b144440c4516032003a405500c00300c004000e4600d40c0301c240340d90380c4101e01c10800b100203503500f5000201310360000040c4454000745014980046c00d6211400d82e0850850100a02000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 877867841 1250 877866591 877866607
    0x507020109030807091202090a020c010e100608031603051e0c010b03060c040b0f0f0705060112020306070206040512070c0902040f050916020a080c1c0809070609050d080906040803070305 82
    0x24041580c803004514202c160142042500d07501c000e841b0100901405041c800301d500c0b01529010768014101400c020030030b0130000f14599a0711801c0d02d200c002201d10f48800460900310200468002d4a04030780c91303005520b500c0d90202c2e6181d110540c4219402c41c0d0b01a05076601e210600208081c0071104000b041300e0b1200c078105400d0090242c0f02038103030941000200160750030013013680d403901050303007085848802110650100d4070070103d004140e40580c00011900000c0520b134010850b00a90469007242d44911099a4969090320060310691010869071408210707000100562482024006003413592a125032060ba001500540c10611190b28203000313505000c0c45031035108a81c08840400d007081d545003e9107070000140040c1050700b0004695449c1c000c100018040308403003030320302d411908581600501c02001030721850070600a5520028035075102d0f00e06842556001401c031210f603a4150345d081c6055004903502a0401028000010f40d0038060000d4602c40d40651a007680d96030749 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 877869091 1250 877867841 877867847
    0x210a0b040606090c03051303141201080a060b0d050627061501030e2808070f060e010b03032b140703090c0b030408070b060f0303070317060906030a24050702010903 72
    0x119071311540401d480d00082103215075800d441030900c0c64041c1070410340c482014141000714428070307692404101c51032000081d400301c0052001c04060058804100c449051001c0050f44603048001818030b81c020804240702d18040603140e1003011303a0b00400b240280c0c150351001e0401c003003203c01d00d21b4003c0206a180d455600b500548003040070020107860504180081407010092007810b13820103040b459012003c000880007141c3c940390300030310407648a111500d07000d4081c0c02c412070704025650902003034044078180042038030700403041100c0350390001082d41c01da400e61202c84000d0800960325465034000361f0110103905030240107955004150407a26043c40041c070341507503220440d0300d1010400c01010a140c601581c60040d0722100c40040c540b54040010381114402c000103906000005e403c00406811608400500e00010080070341c90361088200081143c049a030503426411a4809000041d1540c5a2040c4082481e00c50b1b07180d144154040c0040701c0c5c1c101e42c50005070b992103000c0320034107070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 877870341 1250 877869091 877869101
    0x1a0705070e0402060409020306130f050402040c05090d06090f14070819030806011b020a120c050303040e061302040f0b0405030f0f070b0c0c190f0b030105210a0b04060609 75
    0x4072070000a05041c1d001c00c1c0540702d98490000602d5011000c554590b03540d895481401003140310074400d01065191007001000c0c20b440481c03140d0b10300a401c0e60461b0049041c0c980c0c0180040800c480207281d51a0400545a0140202d850f201040c8812001600b204039880d620a40c2d200201090780c180000700d480e00c00d000740c242107880c02070102034000030780c1b150607207038011420f103040c07446010034101c0c100341c003501110002d5100b454510089020007221003440c07081c0d80079a210411641d5038070141074603445280613900804488100184aa060100200c11046604c0700014509a0303228110007072002e054211010000d0000b40400107460b0401c0480f088018079400760504422850f0300640d221854070625010410100ea907900d40142800704240c0c0324000707004042d0031000d078480d4408400a90081000801c80580040303600b40c4c0c0d243c25641a01c0b00605140c5025003064001d9200003054480c0c2e2001e071059070321900c0041c00140e8618040d82c81910045603c40c00c0240003800e4070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 877871591 1250 877870341 877870349
    0xb01030312180f031115060a12050703030507150e061e061f0201020c030d050619060c060902062115030d0203030109111308030a020c040207150f061a070507 69
    0x6003415498842c540142c0d00740100319074004103090181d241d034601aa852000c4019240590040000c155850130715698a035200300c000b00c0e8142a0207031034a03c0541000d203811005000b40e07100580a200081c000c20050116900841000f0000d2402c0d0081c0030566000d06d0041000b500280d040c0800c246080d620f01914030038905031300f185450100042441e03a802010101e04030801040d92104d910300031741c1100d040340c16020551744e481c203580c01a20091300064603220300a0314007110081441046100300e409032003640d500c10041c130005484820140254600c04da1b48404200301e962080c4074085440d280c44011800f0398089450701c2d2454498120781c40b0000c0e40a9040030481c4086a0b40c080202d0303040d12032450b000200d00c040e4020700300d0a805554410343c4004070842c004100fa810000c0540012080d545c06c0b11041d0a0180c140300a902840500502c1462841c40c032480c2032070f86412840201462140004040c0d541d00000c20442292090719a10a030002035040244007003806040050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 877872841 1250 877871591 877871627
    0x130902030c0f0a0c050d031109011d040e06161e0e03100203421201201201060203091e040b10030b1201060e070503040c050d0605070201051819110402070b010303 71
    0x81d00164462231901d20a808108c4c0c100007003c403020100b00f000da1304000c00751070080d00c1000700855800310140e4a42058a0007658214983c4140000340d100c1d13080c2840d020f121080020100400c070701c00352031962600a0055050082c0203000f41d1810780f51000d14072400741d10450748240080d844650304100301c0580f188040203140c56000900d001c4541c0010b030a800c050783d0b04a821881040711030300410001d404008944079032540c500f0b447c40f002e0003078004828400030340042a41d0302c110581e40c911521640640005250781098000c0b03020030f400d080707400f101400c00304501161310300050000624015003c00700c0d5552603444003604118a2103914104810001c01206003040b0803c9501e1030010400c1c0100000000003608121a42d84140020000680003010000c602c0c6040405803000301d40c000019840d010000307240391352810228102c404000c02602911782c5503560311280b14007008045e65000c06a12080b800303a11030380f005100582c000d042c0c83e0740c20b5055185c001c0c0f41c101086104001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 877874091 1250 877872841 877872851
    0x302190504050412110d0914190b0a02160e19020d05010902031006051201030209042609130c080c0309010b030f030c010b01090e061c0803190c05130902030c0f0a0c050d03 75
    0x3031904000741d5016039a510f002d00110400741c40008402c0c80d40304a866070049052270000400c41540c80c09004003054907000d40300101018051008600e51501c03801202107400c0e004680c90100401080f110b01031f20050140c070b0150031100303210035150280e01c4118255800800c100030701c95030805c1c0001810851400c0351402c1c100100d120410681030001911443d400000f08081000381c14141301c160511058545000d14041c00c40805500b03c0d402c294018032000e40d4441404115104005225403d91038240460319801909142508000c220826541d42da201540d00c1d5035080003882103070341300c0000455546052014450a5a00c03552000e814400d03980c105111074201e41c5103043c5e04c003100781c8440380e0005400c03202d44400e1164100c01b070003008001040c031402c10740f00103001800d110300d5030061010300c02e042001c49481c85100c0c008107408001c02018011101300e0b8000b103420084414059007082141c00e003481c1d240d40240058404104c40304601e01c1000003e11000609a00500781001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 877875341 1250 877874091 877874113
    0x60905060c15060105130326090612040507050312130b030f011413090b0420010c0f050715020619050118020a20010b030f060709030219050405041211 66
    0x541c2e452040c6240c0d294011100002d860f90748610140c03103140c0c040c140b0042841c0e0340c03400d050f541110503000a091a1030604072810f10308003480229982a0320142029207800c021004071805100041c1c82180d56000d038080015a95408100c010400c001100e911a80c0d150304000c1440b0385c100d00c1d446180038040c00d00400001c803082d40c05503411143e80c420421041942400090450f010804170340d02c00031f1416180e00207010f2000e190911072172042e1000441e0381d410300880c19046407441c0a403070000f010004468009004c81030704090301e5100708200d0f10300300c0d107070340d100c800468442002c0030060740801c04205221b10101c5501c1408170f9201000c01241d410301001400301d400c10702500d042a0740000307844020a00c1140650038084202c0020b070401d80b080c054040c080d109011803140f280c400e12800b00c1c2c6051021401c07601a014585450b08000d24503800e1003464444d4000c29516400c0108000516465502400d8452441b590491032041d0007050b0262018408003852030b0315510003001c0e14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 877876591 1250 877875341 877875343
    0x110604020f06070f0c0b07020319390308070b0a0b0109050103020f0d0e0708011104050603012117030a0e1501030b09032b0617070312030b0306070207060905060c 71
    0x10564071420349840395103240074200f16010496000000b407803958100c00009001e6000000351426a1003182038922501e040500394501601d80359000e4180340e4001c0525030b8030412103201c10041070031402c840078a070341d0050340c65540408a500940b24204001859401c02510012240c0c1c0708803c1c09081140c0034816000034035020450107a00d052550000e101c0080c008003d0a892071465220b00c24440b14048a5183d074072040305105428403517080070030004000340100203842c04d80304098004c1d800c680c40c00b443c0340003010000b0608580f0364082031891000c2041c070386166039a041001d00c103541d2820a03c192000701d60b00780083c1100754001006c1080d03000d1312410203a0440750005d1840066407928502c40d411885421414220008640c181c4c11100352005109448203a040070b08005041e034820243c1c5400c405000390802c160000c1006100048000c003440481408501d000690300c501d04001ca80303055400d40d003010240e030102074100304250707011404101603c1c0c10354900d400c00889400d25 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 877877697 1106 877876591 877876609
    0x2a050d29040c1d0f0607050d080402090709260106050607050a0c090b01120e0c040504060516030c05270306010605030f06010306030b01030b1003061b11060402 70
    0x503244980a10b00c0030f00540720b4008108595100c0e003040080c4901a0b5011940c040024001d510100e1f8080003521104001c071344030302145082c180100104154010480000c1140c1d1480501201c8048208050751f00300301d1342080007030b442181d903040c00f419154003e190000004281041400000110100e5160207001480d00058030340b0100320980314008000c0e80030a8105441c289a00c01943c80f50280c02003010035610039203500c0d8002000d44800380c405584031034840041c424000c1c401c0701074a04445103801d081012050300d40014080313009c0c80303011640206011110b0326500109100c111200000141602c86660711500054140d800507141417011102d0a4005605540280719400560b9044000b08010341c1c81e6507980683c0c40c8c4020421420109102da0000001e1928003400c3c2841c21003854201c240d10340c1d6400182082d25020581507507510070003d01002d13860f65106 = true := by decide +kernel

theorem cover : BRFrame.Cov 877697841 877877697 := by
  have h0 := BRFrame.cov_init 877697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 877697841 ≤ n) (h2 : n < 877877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
