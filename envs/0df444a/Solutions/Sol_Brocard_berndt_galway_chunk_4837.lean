-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4837
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:53:54.289625+00:00
-- url     : https://prove2.me/submissions/af2cd7df-35af-4e8a-a805-89e63b2bd7b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 869784172 ≤ n < 869964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 869785422 1250 869784172 869784187
    0x818100b030132090c10080408090a0e1b1e1305040c0207030510051b090a0315021e03040c0b0310030b01030b150114190201150602010b2d15 62
    0x242c3d02d680d4054110610b000c40601c404800d150041c0c2250310100c22405040318440400000c0c2e0700b0203104070380400713000313440e004101070184540590710000000f9120780052519601540702c0100c0490386210030003a4041d25000040f06103058528248549040500050101e003121140760442844100c0780600340b0000182139179940101680e4001c1e90300603003505820350400a05100700c001c04503d59900345030500c01e00120322001100240f419510540d2a0b0690340c00003031082909510141c1609110564540c21a10603801005c2c004001710850710810039905480000e800101c0b1301500b4030020700340c1000040c0658005542c464241100020110b03140d98034a9581c21007070708140c6210300e0000401c07200201202c2800000c0809083c44500e4090840a004a0703105000c03014010038080c1e01591010741c000d410003514240c001422820742510341000a008220240d2030718425418403501c19103c00c54401c02040340440c2c6018015400b81c4481030140e18010b03061003510a00c010130201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 869786672 1250 869785422 869785451
    0xd200703080d0f23100e040c0302060901171f060c08090d0f1703010302130b030d050a03091403131505030103170403050a0f052e0504020a03080307030c0818100b0301 73
    0xd02c41e038440da044c5541281454290039440720313115001810300042900511001c20813810000c01240c0d81120300c155904440c00040702da00c01d02003c08161507000c6010300a20418582124811841074214104d900d5076450080743c0c1d4000045010700b1302c000c00c03c600c0801e4240f10030160b03856400781c0580899003034940d0740d5410039148144004103608020005000310300d4011040b2052100d80301c405e0001030755040000703442d0030021a0602c2031110000311105058040e410110380e481c0c201d00c99400d1006d0404606840740e00c4041a0410000e402401003041c80380d10701090110080b13a551141160b09680e6074a6104034500301c00c03c039581e0207100001c0003c00411495005520503504c0704001961882c00d10324082403802402885007294030f04504020800364904914082c0e05004030360740c0c5503030020070580c590761f030005450200b00008008419804d80c011160440782560b0f600d00c0c0e5621149001170310303009028080c901e60000103105810385c00ca13400103008600010000100303002c2c040d551 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 869787922 1250 869786672 869786711
    0x209070c120f09050f100f031b0c0b070513061b060c02030a200a3002030c06060a120b0a0b09011404110301060503010e0702030c0d200703080d0f 64
    0x40310001180075140201855003c041c0d03000a010940f104140c403004040082c4603601c43c00340b0082002020480d80105911a800185003043c505482407107402010750b00600381032550400366114001040400e035140d12030380850303085070110030340701d0300c0039041c81422104008404205900038510351046c4d00442c519102c1c1241e1225950000c0d50340c0d003007102c005440141d40c5100c00411180041204001e240041038282030540d000c151000e00c80c0200f440c81e005c2114460301003048411644604d01d4464000004101782035000c0700300d51440d84c030780040090010003400350210301001c803d240800146100689034100030700800124111155101150078400301360b1042e1b4161540b9008100f8070b05051188881c0c1c4030740c1403101c510b5581880300142c031074401841804105280c1500144404c2d2080c400d5603000859a0181c480140c000c54000700040e01d13486240001d5024002c440022a0340040c507403040301c2c2d11090003414180c080300c42c44010a41d08844501203a01c1e4088203100b94000303580c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 869789172 1250 869787922 869787953
    0x90e25030b130515032e020d020d05070801081924050708010611062e09020d022104170a1815020d09030f0b0c07080c0f0d0c0804030209070c 62
    0x20b000800d0719184080704c0010036a10a03d6010f60081740100b910704039205101079041c400c0a410040004810620000901c039020807086200e10204120b407000c00741e0b0b003089004d07038155912502141d07240c00c0702940710440a0300d840c24880e031101034080041c400758041000c0c003112401180c603405d4000f6050098a40c1101c1410000c0c6170080180001034002001124290100004100a01d0300488080400020031311420f01d11103e10085018101c2d950060800b0309034201c1c09541f10982e0641110181d000610390b81d01003081c0c81450128940300f22031007407259800000050440981c40e55004699100320480c60800c101c007810f0301c41c40062021b0300d034000c00d1012075402d0602d1001600908241800c0002c04c10070031001c10400100d6090400541220b40146100c40961034044440c0d52030310401c11300802d02180032070154121000440c3c65000d00260301d041c1d4681c2e001d04038007200c90030340c0c004004142a50078007050002d42850f241d016405061803c09030070f0a4000d0b00d8000c50801d8008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 869790422 1250 869789172 869789209
    0xe0f0105030d0e1e0a1a03010302100e0310151502060a0b0d020d141e0d0801050604050d080f040506030408040f08060c0d1a130606090e25030b 63
    0x10010403050408010b08408100035140800c0f10b8840500010036003650394141e00c1048072074000014040c0d4428030b6100080c03400b182c5464124001d103260340034070b0f042448207034402e00031141100219405103800c40b5014500070007800010405c1000b0200509481e44401c00c4e160101101145040d0b0000290f150a84650020b041d6450040589800d441540c0f03009030055002d06030000c0117071210b00744048010f9100c428803c40f003010381070f582d00e0b0007503400c24503c03408540740f0144400c1a0200750045005213a030707102502130381c8440c1032181a10071132003282d070040c00083e00f91010661802c0540004a6005045d074907042c0c1c1c50300000d80c65007050b90706860340a0002030400144403511100e40040c0102005400140713071280f01e14546008000200700015115000d004074150f0505a103000760100802ca88805100400000d00030481c0d40207020110304514000b1030003c148260061080c000740d10500189103009080030121a180d17850501032580707500701c2803c91781d620080d5450702013040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 869791672 1250 869790422 869790451
    0xb12130602030703090b1e0f070221030403080a15050f0402041a0c060f040515060d0b0a0e1006120807020102070e0903090a12030206010302150f030a0209040c05130e0703060e 77
    0x2402c01044010002d0f101e01c022508443e00b02c0032042821f185c056000c0c400c485001d4065a503144264100200ca05911940d91030801107040070054620186000303a00a540700c41c4296902030925048984031150300c0c25640da541000c10003850044458400c94602610260900b035407030a007913600400000034860010004101d0290790401040340c144d2100306841850700d0360a15450780c50312103d9030122032450340d40340170001b09640c8031108000004d550000b4003404501d429a40c0354014131800184a4240c0241e5280003102e0307200d4002c40041d106421111000c01d080d0795152842d980c020302d0224194041d0300c400007107041c1c0c0f82c4069449000e13080c000c2c40c1d0380c00c03600c3d0800650a030300d6001640140e44412a40c0c0100c3c0c0e00042190560f41c1c10f9aa00780329101103d040b040b54080d0070651070300d400d000410031602000f03070303000345c43c1304001270b1030911141e90034250641722800f0702e202c0c0402901510a04104888142040c590032030703207604000504036102c100040d54202d04231000004031994 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 869792922 1250 869791672 869791691
    0x509120f0f0c0625140d0b180405010506010309051507090b030103031107051e3015100501080408090604050a060f0e060c070603050402130903020a0314040b12130602030703 76
    0x1135604500072140c10156140161103054405815030440a17000d020440c000704107024400201e0348101400340008000c50048aa5400340480d19107040741c0803a155403d00b400300352030354040d024145a140d400409006000d8480b500020742601c010104c3c0c041081840700007400f01b00c9500150302950083d55103e4440380c440b0076013460420b6592001c2d0241724081060343c1e50182c0e15107035a40b210802c80328003418401c8858036403a203620301c5003403030500b8141189450040f1000528107c0082400c450b050306995010055a000149403045c03a000c101460001400500a540203180c050f0300103110508242d10307040400c801d81d040d50400d02c0070404042211000350382040ca01c01d00310a007150b0301c525004403444015110190ba2207100181a110804101107540e01d01c002c035400b80564804001a005600b0300a68446400c0001d0300400c254100020b80c8156680840f02a9007a44441c241340000c038240b14545245c00510002644484c2c0064400041c01800254001c502565000c02e0300c840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 869794172 1250 869792922 869792941
    0x4090c030c1a1e0d090b0c091306050f011b150204170c0a0611150903040e070c02030304050f180f010f1403120307050415030606030b0102010509120f0f0c06 69
    0x1040d103401c42e04082881141d44540036074508040c000508804951034000014508000d408090001052007001b5401c0006004800c030180ca405641182c2c101c0d480a12040110b0480701240503407a0019182c45c20b4100b25400341d90310180210003060a5903000d0003d032111501401151480500780381c0020302003180c44000400d905180c440c00703010f040d4821341800001d0340c0d0301c12881030350203100c49401c0e44803c000050002500c82c1010b0040e0a0180c42c006e41066203ea0040c010910070b140c1d110086179181d40b00710a4941c0b0564064007c51425041c17200700031192000d8182c40f03070700c001030360b0043c008001020726407401512030086d001000e50500100b01d603c000d998010102000d088007607254641d60000d414500b103642c1c19a09941d907111201d040f28544a660004640302c1001c2d0034001340c299040d48204110f07200c40e613003000380070203001c0120300f60395081d9070460182c1d20078902c801001040d58010304a14900c89a03403440d00200014110440c3c000441ca00450380084013003204160 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 869795422 1250 869794172 869794199
    0x2060f070b070507020907021902121f06062a11060c24070e180606040503031c06050d0203030315040e07080c0a06170c1e0c030a1403060a03060b04090c030c 69
    0x147c14006400c40216002d00300c1c42d50040c00340c001c0d104503004082c4044141e0309021b03128501c1c3c2036200341101000c085140d00301410b043d00c40d03800040c00d100c00d040f04a04c81d0400c0101884030f40749401e502e0b00ca807600c8240d80d1040300e0031101d0740301004100600c2910402c21030381c8495000681000c0c0450903003400c402d144c6a0051614090008041d85000701e60303110300c0c07070302c0306d48490100e510111b440d20f201046260040350405c0d501840006120501c45030b0a103285040181c81e02c0c001e00519844900380814002c0d000c400030342550052021554003540c10101c100e007088040d03c00143c0d0305141c11024a01066640b0044241d080b0603100c4600e070520950f4000030f019141001c80f01d0780000d14030082c00d0712009002011480d008031340500c4124285038084c3c08d020000b103003580c550b44e0402d4226104c4d44004480e8011a01d500441d210501020b41684e02c5001c0041c140c581c120300d542c40f000080c2c0840003505500a507101c40c0200004d56080c0d0b000061030081c000c007068682040c8003440d100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 869796672 1250 869795422 869795431
    0x2105130204050a110f0309070806010e04060b0f1509040908130302040f0b210319050d0513120f030b040f02030916121112010c08060a0603140402060f070b0705070209 73
    0x22402d003200c104c0500d100e8000c44103044940030b4260341e6950b500810b03e0400e412a0000c1840b405028000070b140042c01840b1400750380601010400081190100081c0709901d440b000d400c419607000004e040456003000d4445200007600c01f040108032503030750902039880074541e00c070403030b840308024400e600b05032180d108416542c010400c500400180001c1003448800f0200304002c5010a4445400c0c00510940e1404a94510301064038900f000d00a095600034090020a03d494240040c02a2143c0101e050300030790006511800c00342841070403a100180b000500003130544400826169840c3c610031098a810790000050b104d081a000c0503003022803044142501040400090040e01681940700f000d2903030215114070740502060106030030160320542070241d9460440000d00054010b282e40d8270aa008a0b040c140c0140c072000c05408403412300c0070759990396001e03100003001402e003d4020041c40811445081c00c002881d61007500c00c02040b03942400003040410500704505000f15aa07400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 869797922 1250 869796672 869796691
    0xd110a061d0402070c05040b06430213110c0f03040501230a0e0f0301050a09020906030120070303091b0306050a0501050d030c02010915200c0907210513020405 70
    0x804801d03444000705c0405501641e0b00c643e40c3d40300030000641c3d84c40d0485a900d01d003492403100014001c220904507100b060031802450450180d0804112403020f4492002c40d8003c206c1c001c500400d411035001010300e034240080b54401001003405503c802c00c501d130400c80c0780400555503942440700040140440860114070700309800c149140c0c1e008000705448503c0701c14a0620314030301541f80003490484040c0700c0a50154030f02428000406c6440e00090141130094981e0881074642c403080c94201c4010035060020f4008461800d0000c28030b017801056000d010740b42c04102400c850302c81d84602c952051324043c80740205201081088514002c0680c0a401c03903800308540e614003401300d0350301d291000d0000d040200000340002103a000d4000c09001c1e114402d80301035400801c080182070880c42942180c140728905044075210b6800107000200c101003d0010041e5459541081c0c649044070070030702441d52481e80100504005500c26070f442a145142e841e800303074140307005110460b40c025000212 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 869799172 1250 869797922 869797927
    0xa0507080d03021306030e0c18090c03030a05071b1e09050901090305090123040f030b0a0515090a0204081207060c09151b08041403190506060d110a061d0402 69
    0x30b01360b01c8400b008540d03150801261200c00d80324020301300001080391983c006001c04d40c1148000c03202d2002032150310080c1c204e0712034a00c0d402c101356403800b82013440300006000300403200008101c1d000002e842c0c00380302d41800016858036002d1001ca6003000c0307000d201d00045070082010200030300580b50040804c1008000032005070310018094454080e405062140003c07600d0840d00c0c918401d1021000f00410715915a41c41d00941c1102c200c1c50b10040c0d9000d240e0f68045921070844d4810117000d0410103184001c030003c8a014801c203220000c09403040c041d4240000203404500707203c21440c107040704c4070083d81c50205180840c100c0d60703020030300300405c1034a074810300445820480004400314903040418400c11013002100c4502900c950042c80d814002c078000503459a1000310701242e42d0114282d41c800f00c800740e14020004207200b80503101b1b0b0f120401241590a213143c9000e1024062881e05210030700702c0e40490604011035018a0025405580d44051201c1208262561030710132103040d803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 869800422 1250 869799172 869799187
    0x7060c0210030b010507050703200a1203080705220f1d0601030b04290406150c060b130c0206012610020a050c06040b0402090c040e040b0402010e030a0507080d0302 72
    0x5041e9040c00908105140d070351510102c19030b02a105a51070280c4c0001111682c03a202e10b801c2082142d030a10742c2940d44416821401c0f58907040d00000241d030100241205a000251003c42d08080701070311003410321804020308030072221100411466015007000c03a95016140c0f00110321010300c1f9034010100c045018103003101c0e1458828040350003801c01d10f000b003007000403030002500030070704044480721034400200414911000b02034450440b00d401c58041280030354981c4003a144401407422080000c013a02c1c8030300c001a005511100707034240d002e045001040d0140e02080300b01e4802000d10005a07002500402c06400c402c04064080030a02c180104480c00140300190b41c0c11076072000302c10050b004101c0f400510300c03a2060b14403001d003003011202142450704040d1000d000c195010b84c013034010600099096460b00044904a036084908000aa900c507150520300e040702400481c108080c1d04140c561503503007009241020b2b0701030400b4092052500e004540f0300401010103400381401440000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 869801672 1250 869800422 869800429
    0x90509031222060e16030206030115170426040f06080406020c122508030c030402130e0c0f0406271b03020705060f22020f0402030906040507060c02 65
    0x5030944405400d180c0402c0d1110b03807100b002c010701c00340c0d489280485002c01c50203110b016005404044086000d8800f002d40e4441075042685c0580400f0390040c0c41000104466030f00500c50702c50040b080d182031074000c0d01d0180f0f902c14405098034140c5000c1a08441c150b9840c1710f0b05030794103503103840d009a07900c0d003454402c00017004251071040d903060100010009007400600c2e0103c420001d0032100b500c00d4482d20440e013410640000070800d4a4140901c0c5180c0c0346540d0410019103281c1054085041d42d881c04803880b0280e00c0108100e8014030002070000542409001d03403410260b00710040c02d8290b10755030520420029008459103c1d0342811810007014421250080694019281b5414288401c0000c81d0123003070301c01c1c0d00e424501412030044200319032650191548602c00c0381551941d44400c0ca803a288101c0c00d40e028400d014850700c0c030741301100d2454807090350b40f807021340440209030150000504076081143c8849054205108120800005005200c003800b094100103032003214a8011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 869802922 1250 869801672 869801677
    0xc0303030f050103021e032b08012709030e181b030c07030309081207050405010801080d0206062101021215120c010e01030912120501060f050702060d1d030a0909050903 74
    0x30039160703100786d00103241d5843c10302502d48a450508128000d10801c0b0088445810b9002c58000001d00800004601d0240c00f1a00a21281040d0100006861121b00c4c030001404058001c8090101c24490702240e80c4881b0074904c4102051100f4200c01c0c984180501070310510b8200c6200400c00801c1081000780070350060b510311541614000800b41490b2504006034402e0300743c0414800c0018081103080c0c0da000004006903182a0b88414190340e8400045039507004851030200513030801e0000800f141025080341c400c4014003240c10404400541c00c0302d089a106407140c3d010074001104008600c101c0104040d40e8103001d8441c0401c2c0d111400708103864100703110b2024100400c44036503403c61384c800e4011141183d04125080010500103502400b004060400c05500754280740000030107074060030312183c403004070b41c603098904135156080144a03481103a28086099841e8504164010b41083c540307081e0060000450340c0e9000840e0162800540e50300c6840641d043c072003000403c171404410b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 869804172 1250 869802922 869802949
    0x10b030a03080f060f030a05071a0301050306041106040b1c0e0601050105071e14011521080705070806011d06060306010e0f0112020c01020d060f030201020a0311011104030c0303030f05010302 84
    0x15070f01026180c0d0000556142c401002c0b855161084e140700c0828460041504000c0381e1071480300306840700740e070a0184ca25001c244200c2e0361640000c8002004540c8941507100c0c036680081030f082c90b060704c511a0002540040c2e182c411000c015000103030b05004030703100d11007480401e0f80051a8561400700000d081d0f00c80c00c1001008000c40c0c0a81800905103190125180ca502c8840d800740302c054120071314020000d10425002043c10000005a03c003004401c10400300340e0403490380c40d0b0042ca0b440d0803d2303540c8001411101c4e4400c0c104000b4000000b030101c5406041c810761500e0803008004141e54204402801042c8210420000d01c1000d2b80c010641c10920001900c0c501000000003006840010420b918070010900006003c3c9048406600424101c00b060b1000c00129455105d14600030340b507800001c6c00345c2c0c052480300011078020440e2580035001900003003000c010040060380c160700310f07510071542d10a0301d49050040603003500940e03501f11019036040005600d182c0006000010b1841c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 869805422 1250 869804172 869804191
    0x4120c0f0f1a1303020c0d1103060c0703200c13020d0507110d021b01180b0f0a0305070c050d140702040203190513081e0705100e010b030a0308 63
    0x84048100484080440000c68108105110301600c5042c50401100102c2d0120a1210004000741842a01c1c608040b09070b80c05078000c0150301c00c01c0091002c4c0010904058452808034203203280e040e1b4040003800c1c0304501006406480380c1241c075000d84660640207250382c04104050603032000000004828049030b204490400020304540703070f94070003480781030304d0104030b142044104032010790007140ea46185d511040c00c1b50000007142108036104da4004012183c1a215082c0200c0300c0c0d8841d9010004030b2180d112500303003080d5120701a850320f91200b540e03191901004582003d0058240c03140951040c117070b09000b4101c8c00c0c903589007510740c80880414414880d0a2108001d0200c2690079202070315409030086584e030406e084440142c000d98142d4480a500340703000144e000d01d070060b0303600d03e96a021004a04003079604140d000c0e440320b15480e60344580801e004281c003040d420000815400b8a10b0000281c1892080006082d94031444206000e44d0241074a00002684440d0583d402704258 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 869806672 1250 869805422 869805437
    0xe01050a03110c06060109080c01050304021504050a0311100305010b030a0c09080708150610090909211205101a160609080301180902100e150d060812030412 69
    0x10a0140d0042c11602c020644840300814812584000024084c0c051031090320354020003039035680c4c3c440d41c402e59407074442d00098050000c0b80041c1041d0518414007140070031494102034540700401d41c900201da1060320b006d140d82039a841e040c01e02f03015104ca41c003480d14080c4000e44c145112285c0f1480094074050420340d541300742c6285a4407600344100503007022000d4513101c641c0c030441c00d9510800754481c4200b80040704e01040c1c4524001484401100c4161908500c06242c0f02010307006041501d030594000ca0001ca4041e6071554003424140c07052101d03258100d80c0b81810440904583d001401420140c2011000f4800d00000b811619180414051000e0341c0d102006680e5140280c000f0005003c5030518405074200b258640145060301c52a4810103024a050b04158041d9160581d001e50800043d480b0705c540c0034800c9050080b00d0901600308603503070070b0515042100b5030040b001e070017404e5a00ca40c14800804103000c8880c40f081800c5074182581041d84400c0900d4100a400310b052140c035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 869807922 1250 869806672 869806687
    0x6031b0801051009030204050910060e0702060402010f0e09041406180303150a080604080406080f240d0f05010b150702090112020a0b030403050a0801150c060510080a050c0103050f070e0105 83
    0x15244c40c8003566002d042400b050a1100c80d2565680a88211050300c500300345011031070442c05003845125a120358018480340e00c0310740041d0703182107005590000b0000882000c0303445858511140380641c1c442d000d003801154a000c80c640c14001c010b03207044101e012030240d902c00c1400020039250069084035807612a4a00e080c005142c0c3c010035070288145000c1d00d010401840200409042121001d4546103481d0350740112000310910100c3e11980c0402c004190b011525001010030b0415820107800406030703550350b4882a0002ca54610110713034a0303440b14450000da043c10080f901070001414402c0e03050903125400200302c007005000703584810412450000941d0750b0804610010a51a4481c6690741000d040080c840d50010784c075130000ca00000000191100040c00c005882200b43e5a20130303540d11590b540c9005000b01070a01c1090a00b4440003150400043c0003010000c0e00c07480050002d201c0260014040c1d0344010005281900c5000800420607089141d60340b40450920700996078006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 869809172 1250 869807922 869807927
    0x601081b091e0a0e0601030501050a050f040506010303050d0b062b090206180103140a02070201200a11060c01020a1e03060810380f0a06050d0905010207081306031b08010510 76
    0x603a0301007003294452100004140001076110ad03003d01e035581d03003d0006035148801b9921500091750b00170801da201c400100301113440746002c0c04810721070705400700c1c8510385035001890366000980302e2400b01040b01d43c0e80761241141c4c40841940c220080c01400700804940000b4858008c442c80141301840350381d07009a85a02c2944564440c01031003441e14014200150790030025005080220b0110302d4a03121006c0d0a40c07113440c440000325120004040c15030141c2e4420901007031920b07036107402c030000307100740c10960f107080c0054103889a080d55562070303282c2c2c0e19070301644007007480c0c00c4c600a04d440c1440a01041d0404900301d24034408004021603200e810030a4503100c141403090010441c076070700e8000a24003d090740d00000851080f2110489a0000780400403902580d00c0349802003081000440c4101c141c6400401805010300001810458581c4452006a011100308114100c6030001802029098400c0c01b0f00340001c043c880c220607030440703005841c4807018001c50744104552041c4601851 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 869810422 1250 869809172 869809181
    0x40302011206081905010608030414010c0201022e0b0d020a15260406050601030c081611100e0f0d02030406030506040f0f0f0b04181101020f0601081b091e0a 69
    0x2008412246409050021342400c0e809900040f50326509003240040c16071400000e68060351034060160311201d01c032100548419060203012415130041411407441500902d03001141503202851b00c1c508480348001031411907403018a002d1068542c03090301800358641220202c1a212807904402c50032600c4031040c1d805070b2a0b40c1000c1c1c00c401d03500c201c1401d00c0e2040340c80a070040d0304c5000706001c2510303040019000c0c0d4400c42c40140011340a840000c0c020300700121102a803032420b080c4034034025602941d09060240c1c1901070a40386443c0d01155411400c20486c1181c05d0307c0c4400900030300124000025202e00c114480c01082640300d001192140d40c0c1c0760701c5005140d2503100100a4071403010000405801c0c0c1d102103030307070543c0b07451408501d9003083e0037150340001010203540100781b0f55503a010f030800c40030182c040c114401d103244c000c200501000260b000e00b150740300400032003000601d01010a200b040581c0d01400310042405440f803107101701000e802040210f560000c0d591020000c0040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 869811672 1250 869810422 869810429
    0x2040221090102180f0915010c051203090d02070602032a0a0b0907050105041a07030512131127042109050f03060c0f220b1207080903040302011206 65
    0x1030100c0000e001507410154010000c101c80c02d40241c503429940700401c82e541c940120460340003c1c1000004000c040d158140c45d4841005050180d0b10010507101c092809118880075010782e1400000d01c64040e40400c241e04104c0024030080c003a890030220000c2d143c6c0a000d1180e498030f500c048241d01d0b0400112403400520400d581265000e00060602c0241c80d28144c94049613801400360205440d48100708560942e041982d2086104c55003580b966010750100a040e010040144005041343d8000c040d828000c107494410a40a0011420082c40c480c0c03207240b00601c80d0600c4101030803a0381054140c451115503103a0304281c03030b5585040c082000a0a06041c0c0302c400c41032032141c03059907002054a82620380c192841c001e03090001c02452390301c4200b40c0b00740400f504244954510f80301c1e070000030242c20307895190045003409082c1d03510000c403031aa000612002408221032901c036144041300c0d50703c40b001385030040b04d5040a6030180d8a0303100c4c80c00080d0400407401840c80406242c2c1d08900001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 869812922 1250 869811672 869811727
    0x1003080a020d18060509060304021c1a071706010c0311160e13350a030b0418030e061e040b0406090803090102030301090207050133090513020402 64
    0x3035240440c0000e4541c842a1907200c003154107080140c1d9a458540d4010060750307100c1c0c541c9850304142a003040342503000104103da101168551520041d00c1d4038400e00180381c49032841d82405008600a05802007000300035400f0403d69840f110301010035024100d8119038282401c203d41181410f0458440c040a1402261449000290303540040350014240455014000405164844100e0b440100040c00005015002d5009010505040300000040102c030214122a000900b0b00c0b0000410340182201ca008030faa00c0c4c1030135149050074002d06095185814180c91400101d5601a00e05240c040340c85001d400082034030340c01c4000f01e40f50f8190b802c1d100d00186403180d54800002c5610340c803602654002130502800014480400030584088080503000303541560309201401c0003c0d00000400c0e1600d6481c0d0200c4600c40d1184152200b0950249800820000c44044505804c0c0e0713190f84080c1a562804042010020b04080340e07003003640c1d0480d00580d0340c43c185e4101c0307250052200c0c6199032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 869814172 1250 869812922 869812927
    0xc0b0103080a0c0b04140d050c150702190308060a060503060d0303180507030b0603150f0106080408070f201903350307080c0405060901030f021306080108010501050a0b070308100308 80
    0x180721001e020306d803281c1d1405080b1002d44054100844240c0248041d6010a622420100300c144490b4218503501030702900c1120707140a21050b0a14903915150300950200320301c43c051107010300f8101c1491010b0b24450401074958181400490050200210041c00701f43d81d401c0c1303a9009220f006820044582c0140403070384210313124100720003111303000d8460307600c03038802c0c1c11400302424078011603244075502c0c1030395900241c8c1c070b492010303030b030301c0b03400a000711403c0303030200310620001b8442019200340758018011154015a00c0c030514251100d20940e980c4030f000c06141c03c00ca043c104601540940707a004081085410804002c200928641000c0f054402018003454100341e0040002c2c610496859130360540b2a00c0d041c1d54031130b40c0d2140740106600110200210503580d4041d400c40319618010103801480c01c4414600740001d0070845d0403e00000c0c503000700410099009004450140c40300711091a010352a2421a03134a07841140001414003120300002049030b0000100000215009240d00b036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 869815422 1250 869814172 869814181
    0x617040515040512120f011d0a0b03071a0a030e01061505091206180606040b0109060e0112020a0309060e0118200307060c02011d03070b0f041e0608070c0b0103080a0c0b 74
    0x34a0745c0303c200c0350703244c030350350100c0000071038404001000481001e521120452500c41c04120009400000001074141c813402d08005070f00c00c00c4201c044080001d006031341d03468030f100040080542c1ca1310803c0e080b03142e040210030f120054030511106580300c52401d12540c0c5282d028082090003c9614280849003e4041089a4800182d940c22281e02d65002a62441e5580e04100030803a00808140742c00940c551340103205150140c201110400014100421840040b902d16400d07030b805001c1e2400044e44035400c0340f040000c203004200d0324003035103002406013244c240142c10144d20209030180000018111200c000740210700101d0900d40043d0a0314107040c0c4031200134041e0791904074100d0015090401e003401072105d40e000d81181c10b0009014121091411411100d00e81042c1c288031040a400c000002d099a0303e10b04207143c1451072200c45900e1440c014014080117002001c0d42c050205e50140b040008a94254903811349921103440c07900c0b0401c1000850b04d080d000070000302403501250920 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 869816672 1250 869815422 869815447
    0x220603060c2a050307031101150801150f14040b06040305070e010e0a051b0306010207090914070f241202070b0405070503070b030c0304060908070c0617040515040512 73
    0x200d141502c0e0384400161081c0c03180c2d0b00741201403551000380180d01300740b00388000039102c0c520000310030240c40c001007100c4459101e90000070010350f0025030a43e668003580d2100c00c108220274070090050155401c243c070314052240d45480e10555400c1e118642c1e410b40000c05603140001c0c1c0b00519008000c82d40701e50f4032500200341d581002e0054411062210000541c60001801820700c04d065400001c03e01c0303400003a640c8050340002d030886056000341c420110b64003041d0300c1488800e902a060b0102540031903455a03007400202d0b0400c250103421010113012200084003400c041015002030400b260142c4442140c04069411074114054000129030091011006600c0e004034086c40c2075504030341e40d41c01059a6952681b03d40d0410070700510004083d00b00a1024540c05409103602148049940e6180506d5502481003140d4504c0c0c02c050a00103180e00c02204c0000302c9020803c2501410140c07111039070b542221040750341244194000800300002171104058440c1d00c0c071001c41d01c95a0a5002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 869817922 1250 869816672 869816687
    0x50601090321020616170a1e4d040e190e03090f13020c060f0406060e040305033d06030b0303070b0402090705070b07050c0f0705220603060c 62
    0x8010040c401c100c04519105031703001c00841140345c580c41d01000c5564003244204642c6006284901c510303a01c43c904400708003066402048156414000503548202050b52001c15070134860340d103614903840c2d901308425901d82610784c01220b040b218043d1402e240e20300700300440c0708039004290600d9005060101c1608600d41c080307404980501c0620030701203900041582c901130590f0700c0b03510041111448030f03241041c60182102d044096005490b018500b40b420303180c16000e8500d01d646900c4201007000748142d900c60782c4090303e2100d1125035a070030f00c0d0310001e00600000d010500604444100ea003080004250310003014005c1004800288a010a06002c850a14402c0002203400c14002403001c0ca004000c561000d07502c1904000c3c02d45840d024043d040c0c2c8002c1001003408020800000480c41a440c40b9100d100d0f55650346940c0d0710410300381c40c01c22202454002e840e0b4003412050150b90f494089803090307170110a10301e14a90004009402c041c0c441944098289071500f1840c0907660b510054 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 869819172 1250 869817922 869817983
    0x18030706031a01170105010513030c030b0403080a0603030c0803150409080915040b041401140d051e0f04062031140f210c01030b040e060a0506010903 66
    0x102d40240d5004500544a02800815225106041c03038014411356014102078900d000c605c184107200e82d0b46a130340314481401c094000717945034641e050030401050380c0030040940c8a502c034036040c400a4655500075150313454519006100c80c40110000d043e641da01903021305e0a09005006003c3c03010f260030902c0c0540c0c05540304c64000c5a5403004020711320050300c111022145c0a40901d4906850104e07000c90300c01c1099000e0341040302400700c00800750407000180c904d0548404000845040403280111208042c5030010640b034054020040c0d84040c055400764080d400100c0031444840c0403c2e813242e00c188441810343c42000200300d042c82c1020300c1c03900d0a0302c00d100d4440740100c44e000c4442d018007100300e8407400352003002d2006140005e090084285072000b601800c21401d040b220508026005895400707040594440031a088440d81d05000d503125502c402d95040041849001d4901c2c0c840c18003d002c40380103615100894030b01d03445070003400c00a54208160710070704101c038090600700184440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 869820422 1250 869819172 869819201
    0x1005091809010b06091e0d0813090b0411030601200106260c0d0f110402040b090307050402030105060d05130b07050c1c0804030e120106170129061803070603 69
    0x3d072500260921504450841100400e0b0101c620050b0300c02c90741c890244c6213800d0300a031545100c0b90009038248060310b01c511340302500440f114204038501c0c08940000301c542d88501c1c2421442d1803500000301c1200d4000d4028170b003c8042290944600380c6291411143d84959880d1040000e82401203122011101c00307030601501c07082d00d21014480d03840c04070b000140c2e400f25911403004002001d50400d80c03189031040074060b1884000900050498009501c000002600010a50b041d0f10b0248854030240c201201c007142154100000b090940c01100d50311032503540d903100440d0064090745809450281e0011000ca25850120341c010b10a801104c40b1054134403804d10400344d040304503908500801015542e068041e80c2c4d50300d00f100d00307011015081b070b040820401008400c081c00c2c010074001d008002201c0301d136402008400750031103043c00b105008015008461000e0750b5002152101c103290100d504070344420819200380c0e485c0b000300e9841607051113121000601a50150400104020040c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 869821672 1250 869820422 869820431
    0x71103010608120c0c030a030f031407080105040c14030403090e01090203070f03230c04150c110d03050d0e0d0306090902130c140c1b030f060402100509180901 70
    0x4018542624001d0081ca00150840050020025a02d00181030071a085138101d0301c1800900340842d0802c000d0f404c09a000038125500c00c10156094010300c5202802800b9404441ca0718032030088c04e0a40c1030107001c0c82a0303144c842400856100d43c43c03010307001c092410200c1e038900301031034003421540300351003210484010000002410107451007541d1003042d080c0c407840c02d64080d0903005c0300204480c1c02c0d283c02c081d40d801403211501d20040c41c4988909c90f403110b00342d82c0d00e05240d00441038029414204040011980c840300000340205c1000b02c90304420786c2c0b80a2400e8441c5000d5030fa034054003008403540d500d40021081e0803a40060b50680c10f0044d40c0f001c02201d51545008000d0720083c102c00b94201d103881008440b4042d80341e010202c84525440c1c00c031141109400c034080b85a20001c1000780b5580725a080e004107135510b00043c124004214028548400d01d846e0340ca445500c01400070f4410f80381b42a031501e501d40940219010a1030007041c125070381105500f1042c0f001000d4038031394559841d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 869822922 1250 869821672 869821703
    0x103140a1a0a0b09102702070308180f0c1302090d030203090a051008060904020a05030f030918060907050903100f0509060105060405130905030d092003011e020307140a0507 76
    0x59914580a40c42c59041700401904000300c00d40c1d4400c50411043c150400a50310034115030070f610142004c244a5a5401c1407810300004100b07505a2a15070030901c0d0300000301c100c2d104c0a002600088403441511010600071801210100a004021080d900134a031640c810342010b074044004c0560382c104503840c40c06951914248600000f0160302d00020410030808110540f030000007096210b84002c0c100d92069464101080c20520542902c3c041580701090048092411080045010400b09869100e5241000010f02071110150024041c404000b6604400391400d002d40c0880c545161400d1110010064000c401044200c54140e542e0203424004030705071030404101c8045400080032000d4a001858654004040b1440c046602d84400c0040d840a4512401030710b08441c0613007103c002e0402c10310b041c9104040c1e00907115100ba4904074a00c0744030138a2a251420030384c8401c800607125920140c042d141001c0c40e43e2540e51442303010680540b0141c0c0240240303c5030744581c501c503402822 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 869824172 1250 869822922 869822929
    0xc170c03010e0109090212100905010509150c03040c0b070b0702210f0c010906051524030f040f0b2a040e010504020f04030c06030c260103140a1a0a0b 66
    0x3082c022410012200030041091500c0d9811201ca2280001d00f03e2200c070400d150a545044000c01282d1030b456120740340003080c89000c0c40350f10360204100003c1c00c1c14079150302c680030b60203030010180401d8030f001002040c01d01c00c020350803070040c001a5041a0b601c039081e044ca00c4103240b040340c01100500c6808500368074030350030001d2945200180175449040c44118440d01d2120782050110701c59a65a134031000e40400c4c118000c45004d580c0b800001031045042c0428440200c0c14529890991001401e806031103140b00d0048079071042c000214418240c40ea407800f03070180d401600b0007400641c1171703a05004100e403500416603040250303240c130303001d08941311030790801180100e1191181041c0c40100400041c10190028082c40303220310705892421361680c0e039040011382e254000000080d543c000b0300030300c19001942c540417210032240e0382d002512642807140300c80704140001440c19010010080040804000d0060b40950001541301d4113030034800309030341c04202101c103c86400d06116200c6010f04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 869825422 1250 869824172 869824177
    0x250b04030b2a07050a02091509010312020124030b06010203031b0a090b1b011a060403080307020a020a0b0901030b0d1e03211b080403020d05030601020a120528050421060c170c 77
    0x84049c05000c0b00e68030b1510b8845a0054942d2154195500c54861010045045042600c518050348803241c0b15400e504005608900044c2030505640c410024010901e91802c190346413aa03120817196501d229000c2c0440d51007807a07078441e4030544004148102448480084d99001c4203259000f044001c00e260780c0b6000381c1c801c200c41590406401c0006101051101e001543d00505600450362650100ea000c82c0690f000c030f03841880040c1b400700b07070324403a5079140c045c02d8510541100d041c196094282c4624512529076002541181030030100c131b6003018003c2c8044000c0c0f030501e0701000810a0804401c4000d41182c02600880c24010010715a41c0350250501a01440c0c25600403c0000c00001c0240c07400da00c0600000d040d0312815003208005034009255628584240c0d0720380780c88810014698108041083c2e1645d030407a074800f0030701101540001039a04172141c4201d0101075104080b0700c0500c00c0c241d020007920450800000101700760f041180c2c01c444c560341400c80880c996405100c2074103030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 869826672 1250 869825422 869825461
    0xe0c09040e07051c11090903030415020304080414040b04020409091e2f19090b03010911010e120712150209210f250b04030b2a07050a0209 61
    0x31035041c4658684980c2c00c01c103104c2038480d40d00c03d44003114000014000c2201103a200d041e0358400000c2208005014040c0111961008002c3d030440c2880c1c0c0d00c51000d4002c9000710082c11400e52810145540c032038100701c40801005d0421035132151a60440c00c0640751140064075501e840340c208204140103104800c089907084904c0d903140054a40c00c401c1d5900701400360807030301035108007a090315580b018560030351207014103602203500e860b06611005403004201c1e03951181e45043c480e1004a03419006420201c1024a0010841180c020029198180c48103192510788103600c07010628840c40401900d10314051440000701581102c0054107a214840220340c01050f880c4074040000760b10001c141a80c0c1041050703801c0c100171028241d1030000c2500950f55000c004541c510030244110b030010020380141440c00e4036003421a1a440c0103000017034602002c03000c140308000d070000711140100300c4040100c0e5600c1c0d51049103050503551140c40000692046003010046541400300a00c6241c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 869827922 1250 869826672 869826679
    0x5101e0608120f1308030d09060b1c03030e0703210e0910052709070302150f091306030c060e0109050d0201021b060c0a08070c062c0303040e0c09040e0705 68
    0xc103400414040d443d500840d6012421880c0da00c0d021428140500203052401041d017000144d000c114180941038414422415005042020100003008240b018041c5442d405040201304150b04802240c50084550700240c000d5103000100d104513a64102c80000612107540c0e031300680404601001012134007901c01191040720000200b1a6050040040798030165401c0c40312411845a210201c0904040728001001e810052060045140400849100c0400d030005942812408600f42120340310344504144601c1c401c40c0d540119000c1d40d040400030319400040880c0c0c0d00d94406000d4420010760001501090081d200460581081035602e420990141d0081c0b1700f291600c014400341c810500400c0d90003600821455843c0341081120007000d41c850b040c5540d035240c06042620030b860f02a0002c100b001200e0107035a1030014200601c05040c60907804909003100c66600280c07070b500c00d9a00040b900c964500c2001070204401c2c0107400c03690400e643c01d110380f00c40313030a10039114034460089692 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 869829172 1250 869827922 869827927
    0xa060203070b0901060b0f070210030b0609091009020f0408060615030f04020d0c060f03230103020127091b020a150218130e0f070503100905101e060812 67
    0x1290b100c00c80c82c0e4100703c2c80c100004072291210310301c00881e0f10003150307003204d02c000050040440c141898070401c081020310b81045003400e10000500c141c450032032a24400c202002c08103055159245000008042c01c50045503941c2d090900007140ea003081c8610201c41c0549000910581042100310596100d0050302518554a07030807049400e07032000c1c0040c0e030480001c1072008002107100e69032001a140310740321161241c4c00b008004090310141c2c040d2580c501c0c0b550042c49140001007a110341541d80c24204111040d8145209446502c0705001d21034403c074005400081d0482c82d90311128403004180466103d00300403136002e82c1d440031441001001840c041c402030b8401e140c1c82d8080c2c0b88004844a140003c104210001184010803441c6d40e228184c0c0c41e150341049000030401080c1c0d03000d00340c0280c04a98500703400a80c5611060103410708103912040c0180c200207040c0f00d1074410090020303041081c000000350342c40c05486a180160300091074000c010500c501c00180382200a1442140e0a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 869830422 1250 869829172 869829187
    0x1060302030c1905091c08030f04050a0b010e060f010f120f061206020306010e18010b07030e09090c010206070e2b17091003020a050d0e0f07061d0a060203 68
    0x24020340c001020501c9120b018030040310701c00e808034405038103042140c1c1d910780c6905046041040c43c451103080c1e401864600c08000c0001035005081e42d42c403100841660609a840c2c1c00d0041c00e000d40c2c2000248000803c03000481e0400003020054001c25003035070650343c4011404010746080c80d402d19040042006005c0e40440000c050b040482000c40307008011030700075510182a110b0641246085070543d03004400c000c8256072288814000d000121a0501c5030001441200c40b115010f00030007000b90000a6a401454007400c8045503414029140240d0f134a800d081c41910303a504086010300500444000c2030f00684148044c00c01d035400200090201440000042e1091050292441005010b8404007012a1f2401c407103040518428454584d83c032410030402c90601c1003155000c0a01d841404040881a400801d45150207000e181c00100500713030703c004078505402c0710f2201111303100c0d5030400300e0581c1c1c1c400e10b900c600d600594486081d4005090802045d98114003c800050f070081c807644 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 869831672 1250 869830422 869830427
    0x2041d1e180f01050a051f0e070912230607090e0414120c0d0c0f11130501140a0f030302120f190e1807211113030b15090106 55
    0x55007003821180d610107902500d031541420302059004000d51a5034a60410400640070300645600140c151684050510fa5280c510b201c1d0501e801820301c84200b1500140c00c1c20300443d050b002800d10304403e4400c40d032041c07519020888041504d101415149000d03804100030000d140c1e8000c0c892501c401a42e28240704c0822102c00b402041500d004110150600e0044000d020450b030b549851200e15545500e6a03840a00c0e1a15243c2801704014241241e0380c040f5811140752001030b980700c02a10260b00c60709000403603040e00d10a030b1040301c900d0007000141c041008034641d0000002980d94121050355040000c010145038440580580c0101c0944844058040020255003561210a600701150f02509110804007020540d0108101c101200340340d14000726040d19200c2c442100002c1481c01410040001804403030f107150804505090071000700b1140c000c00d0243c50607100340780e1075004400301022106441d21050322450505ca010400490201c4410a11140058050401a480d01c0e404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 869832922 1250 869831672 869831731
    0xc0307151409063c0403022b0f05070215040f1a0315010203070501050c0409060e19020a0207030503031009050f0705030402090406111306140405030c040911060d02041d 74
    0x9910401c0441e40c2c1d107400700640c80d0784013220500c01c45040564a490b103006850582c201303060004d0041004421442980381c40944903c404444ca03050181102c40d202c180e6140c0a045030082d400100804142c6010300c142c405001292010700c0c19018940c0d48800b42c6030800f40311000540c01c21400c100180924469411481c031448041c810dc034a010440c2e11458211042600c4440501100060801c4108814061030300501140601c005160500690501d020b02c00c02c0105003110f07402007080a05d69000307001c00c0c3c0c011070f040310a0320741d40c0c034005464460590103800b400f0324113445d140224a07840c51200c102841042503031142482c42d03c640e020420403810090040ba40c1586406902c0f405062490281011040b03421070764440a05120b00030b1710000c0341180796541c24509010030426640c0010b60500b140d40c0071303980040c51480314103191300503a04000c41c2c1ca8201c140055085c0c2c501c2c100d54020030444260000901003036509040001c440c040c240c50708410344010454525a18100a00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 869834172 1250 869832922 869832961
    0x31110090c030b060a030c0f080606040c271a0904110a0f080901060b0a020c01080603281707050d03060506091818190c0e0705031b0c030715140906 65
    0x40c4901d0702d9034035a561f09128030240c019800c84003180c6003c0003081002c001d11034101d14100c1c0e090211800c0180004d00320140c0501e208003e0b070403200500107101a1400780000341504075101c10401c40c80d40d600030403d900c8401d189000e1403030405407025100a000550f120046507981d81040f01d10440c2d03049503000000b03803440c0102e569030600000c01c02041801450141600d40180000307084140000d04004001409140a03170050000c40c65242d040d00003110441e42000039030b0009400a0801500074089101d40740c44049002503181c0c14864001b5048845640c140e80c10f00c4280d403100302f4000c40c0e001d080045904202040340301c0801d150000d0205a000210a01c541110303000d6176601460306e80c16242807c0c00640c810b09100134854600620727000380811415241003814440d8006050f80303c010300c5d00001c03c851312200d403a88501c1d00121507602c0e0030302e4200c039280c86103414400003450300c001c0c3c010611171601000c1d440c241c4101000500c140000da002c1c1240d50742d050500c500c842001d40303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 869835422 1250 869834172 869834179
    0x60703051c020c010204031529130f0c020f06010b09090a020703020102191107051212091804150b120a0303110417010509060903121b16031110090c030b06 68
    0xf040c01103118003440a03000850080b6102c0040440b0f05a03954112000140f071200304082c055080c3e160442c82c4650b00390f901500303652840ea030318940d01d004801450109030b5614200d0509100721400c13130340012031140c001c0003201902c416990759a1044141d10540401903044900c050008103c8141d60380a801c4a034000d000152a155016a0b410b040d0680b0313008800200b1010000121070300010800e19014100c25111054001341c648452580d40c0016007212920680c00200784200d030701c0c1d113030118150070100044118141410315000030740600c3c080151800e03901d0034200fa195840c20b450030034442c0c0700c4800501551040c41d241140a0000c0648480e107121301007000290104185180003402c10300240001024108610104c4c2840c50240000e1410350041c4511189950980e08141c1c004c1c030355503080b503c400042d0407142610700031417640700c0c0142080383c40c040c02d15800c804504000c180750000c0c1d480c4d5040e40c1005400f00c5050080c00740842d461100c0900000f43d528407125000100103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 869836672 1250 869835422 869835427
    0x627100f14070b090703140d1409120f0307110a1409090319090305011109150702011205040f0b0f0c0a03020c0c0d051c21020702010e03100c0e060703051c02 69
    0x20f440c0d00507480d20684005030300754002e9000304107201300c84040803803e052a4002c3d05034203861020044c401c980340150444482c8002410200c10f46e1a420344c00350441d8a0b070140d0f010071301030001044c5c9070b4001c0039094802544c580364101c1e442c900a000341c0280c0704540042000a42c00d0360a1105080c0000e01c0d1000b1403208000c0e140242d00180d9401c1c1601c0420f03a10035160340d046103042c0c0d00307480d8004916602c219007440291825601c0da100c2a1307410010f226800d481d0512800100e8101c4414000d60400d140b6003801d000030700c01519214801c03a03008852050a03601d4800b00304001850450304100807080600901551034403940051456004190840c0da064034144002408909405030844055018503004400150803030100c083d403c4490608402100f48000c60700d40d04200003220701c0740190f00143c5c12046a000c0c02c02c1703440ca0800541240c03134103043c0f144020024185008039101203046d19a075010341c0d1415104030303280d00784d0681e0b0301d42c28415460441480600c0344500d80340b2f215000e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 869837922 1250 869836672 869836687
    0x23100909150806011403070806060121090b04061b080f06011107080f0d0f050f12070c0f24020715090f050607020102030106110f06060118050627100f14 67
    0x10443e4034040c0000e4034403604001c40c00710030149000c0702544041400e401400811406a07001114515071114810101c01c1c0c00190301d803c4801400c91782401458054150305004c1800b440d54004a014072031190f24103907208401c20285c07032448044615001076004030340043e80302d510400808990000034812607440984a0300c081e401e0106da03211101041e4084c3d0708940c021640000500c0c0e0680d5182072945c940302001208000071311414035020001000c0d41f02280304c040c03080a00c185182c2e00f204000c0b4040949142107480080044450700b06a140600d034019400081d100b25503017581e02040c004d0350581d8030071050000e49405003007940c5008441d001c1070082081802101d101e0369a42c3d0006980b5810908068400c0341800303000d48450f400001100c0180d5000140140c000e4000d0801c8402c0050310250204980c010350442d64000390040341c450000185d03030201400015a00c01084034404040040c010f65000841400002803007201000b4861030007440b2414484064032121460140d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 869839172 1250 869837922 869837939
    0xb031005040e1f0212180715090909140d05040f14011e020604021903030c03230403050109110613060807120c0809100c0e010302030a02132310090915 66
    0x86601c05465020740028588510201080c0c05d03962001d81d24081503200139582c0141680c031205405000c28047c400c000148416000b914540010956581c0070b02c8104414034040746c0301400d031116002c143c42185150f058250107070041c0c40c00c1c1d80c50100ea4980c164a001c648139100005006040e06008006250501440da020b140c9100b00c03039250024011810688144142c41e00108407659111036441400e1000a0f8010385e561103140d00751801c142c504240a0b003003c18994000f1111040806c0080c0c00010090107402100d0010b00944145198000f01010b001c083d00c00c546000910b000a00018041c0c5405108415000021032a09003402c00d03020b03280804a274a00c00b50030000c19040010880c4182d41001018a000803400003484110b01c03240e80034007407800e141000e905040d00800064a40e951a0741906c0e1624098074a50100c1b641c1c65000b05802c0248040907240760020440f4400e0b10304105030610070714206a5a01000d00b441c00b80d03001c008186440c189d131b1101300300c401c00089024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 869840422 1250 869839172 869839213
    0x6060815210a03170601050405060904051f080703060e0c0303071e080310090c0c0804060c170703030204081b0901060e0f0904150c090e040f080c070612060b031005040e 74
    0x41c420b4580e00010744d0500c1c40218200801004207041040070030043c00790f42ca40030152466202e081d40c01040a032111605103241041c4004d4000141005010006031200700042c0d49048a000c3d1108128a2242c00131064491440010f4640c043d40200b05280001345605080d000b4101881e4409840c20115035510f0b40690041d91006a9640348080c00c0c00280140e110311031905005007007000400e451544d900d5a1801144900007d001174940d4041c10300007600562841100c000002e03542e60101d030700d000342c020b4015020350400e40c81500d01c2c49900040070b90054202180040c01002140e10345101214100d151a00643d00321000c070014000d01c0d101c0c025041e00442c132600b12010f20b104c018038044210381071a0551820012240420000070b21002c1e520360300103800c8070000309a038049082c040f0f518072130910005214491010b0024116900410b6090944148082404500d41c8c80c3e111800e02d001c04c3e00d42c1207800c01c1c2e64174200054905640068040e40000003500c280d60440004c400c07046 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 869841672 1250 869840422 869840443
    0x1e0412050703020a05041a13060e090a050d020f1c03180b0105040507030b130c0c0b15011202030f18070503030a0302070b090a0503030406050a1b02030a030606081521 73
    0x40e40074490502c1140303130046481014100903102000401e543d030768410444001511041d00840f00c1d01d0382c0c03040d9000581c10200182104142802d16820405681039a44a03482e0080d21035020781c0c451425101c0c0701196847c8180c18000040200c565038168807004000c0450039002815070f00c403024410504480451041c82d4080d624480d00c96240105100603a000148403004052828401c5429660341c040c2c0340414003952080096009010081500c0450022001801c2650228204113083c0d2801120f282d00d10820380c0e4940c0e030001d10010354001c0e40003d58840b03c0000715030000800e103440030002900340b40d14203070881d0350181d0380e040400d06692284001c800001e400140300d40601c80d2109447d074000303500e00c00414960800341c4a0646a00014000810858444001c9811042c07280c002142d9811450022403640b811080d000c0d560ba0300102c441c101090070705000103400e5008808183c41105115a0384039203141500400c1240c0809072120b40031a46902d0191030320300c904010f40c122a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 869842922 1250 869841672 869841683
    0xc06050907150c050607230c0307171b0c010903060c140a18080a0c0b030712050f0f13031e1202040e01050a08030703021504021309030305070e0906061e0412 69
    0x800c1414031509005d0000c0c00301083c840d030860120400040340d0030301e08490380b50302c0c520340c0c0b00c03001e024600c2e00318403941c0005000740e41004106440011100c00805860840d038403401502945503842e9074550080d010420b02051900d40304002040482d004034500da2418903004031070080c5541591071580200603510002450f028469019088060320364000e0b103007041c010040e090642e62001604003c40c0258401c005021003c00e50850246201f8980103812890038821071609461010300304404442e8203d288910030007141c20440640108084d0980558a0521081d41d8100d0200f01000104403403041043c224000c500b42c00d00d0b84007600142412200c4d10f003803540b40c1010418004c4881e042040fa540040140c0d0740065000a541840e17160000300a00240c1d0740c074000036106000c0f0400740c0c9009420402c0040405038964081440307842c1035281c0c8058010607205100300d01c001103030700c21381202003003014a044408510420b0404400450213519050310342c2d2280707a02c4109401d0840f00d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 869844172 1250 869842922 869842937
    0x90c190e041d06070f0c0611072d0201050315030a05010b0a0b12070c02040b030f0a060f0605090105040b0d0f03080f07050c030304020409150603110f030d0c0605090715 74
    0x8040c40c0c240034030810b20141a030711144048501038499181d0801803d51810b100c030b20720240901c980030320418401c040e0091000c11840100401d10411a8042d88081320341d400d54885204d21040240d0458410031006070041510341c1d02c0f94015991944041d105000c000a1216048400d6400b000300f091198030500000c248061910709006c0c0c40a00740d00b02a621071024007060000e160a080100e912003c5850070001d60f955600200c1d000304011840720b505409540504140c800700000c00e901503078400c44c02049106203000d05841103502600a0b142d0001e42d0200401492070f26070802c40340d109000340341a81c02141550340c03c905451103070741140450313000d0381004840407d11001c140d201c0707600d0516074a010310301400c2e65120301c00200004d1049503038080d1001031101c208440040104070420800070140c1303c0c20800b5a0f07140110034103100b00c620b655494824207000c140ca06410703206449810444070b244e5102d01c09400010013880551181020005032010f2100044c0e42c0c0c84217580700e000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 869845422 1250 869844172 869844197
    0x71701060314010c080a1e020d0b0a050316061202040b04080d1b0f03050c1c09050f100f1209060c08180f0706050a0329120105060d02090c19 62
    0x2038030b0b100d1a6003164002d0b45031400310031001c1c0e0401c10303007035110360800d00019600b1207a120082c62090b950003211845403004c115610b21800c25030050b0064101100c9110800d5502c0c0c0800d941c07443e8800c4801d0198488450400a03207004111052212212110141c24541c0b192094095500a43c0c0424a15071026051000c1560426000c12040324002c8201d82003030416110006810303c90a00102002400030310651b06c110b06120350141c0900c031382c40d9003030b602e1542d4038018455480c0d40141071007481345002020303a07071505c200b075030448081540343c4e031401281c849016640301c01411401a02a603e600c002800110240b00341104d0000e5519001c2003400d040504041700100d9044409060748a0030020000d4080007074441d0444400d850030a45d81d085400d0210080d02e1040440c60342c6002d10b00542591078101c504049140c80d0a80710581012050740c007e07030a0350300949107690409614a14034000d4109005096031150254503101d01d00074010740d55980c41c00081d02035400141c582c20420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 869846672 1250 869845422 869845433
    0x309010801090e0a081b0a11031e1203130f03051209010c1409060c06010f0e1f09091e030e090105030109170309160e0f071412090717010603 62
    0x118090405008100252018188031130741e00e0f00c0800b00540b02260105207100101901d01001c00002e2203201910803e01443c0b40c580e245400c90120240309000b0360501194130603010200f109401203501c005e003603040c84400c10070429030026000041c0c2101d028400004546281030401c2094483d5079400d81d0b070000c108a1054007a03015200c450242d0406000e00c0314281d10002808401110505a9680e0075101001810501c50051032881a02038100001001c00400c10349a040740e94070682c82c20f0a90b601451070b2010341c08005100720401d0307401010b016048065204081a9204401c0da0110b0807910850351ba00c41c0d1045000c80014070020040d00d03850400581d0b55005000a8001f4403c981e1035035140a9000c0d1850030350784401001000240ca0301000b040300c1c0c0166450741c4a0b071000544c65900748002d001007142c294503519014000b29048078403850104007080500308403542003a402030721105980d200a050382d04148140200401c00b5180440b0070065240c8242c0000b850300e2079442e14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 869847922 1250 869846672 869846687
    0x21c11101d01090506031941090d0c060603060515040605041b050d0f02030c071e0b040f15020406170a0203040b0105100306150509031e0d050a0c05030c030901 70
    0x41e541000300c90780040015849620580e0b8100e005280702403c0005504c21080050900d0142d04c4040d080b0207890156040f10b000f101529900319402c54103000d16070303010308020800c05540c1d0209035404a01c0d0048414031900b2159840c510803200803030b1582e9031741c0380c1c0415500f00303031044942800b000b001c0807024070307041c8250f0000f40020b031410b21884180300501b043c8840c010b07980c1424040b000447c41e00c1c42030254442804001d2610085450781040304805805400604007210b00c0c0c0c00500000f405400300200540b01c4540c0004450125600c940c1c7d000a500548401220600da50301e59030214030700c0da070025201403e41c940d03400700d540010213885228104042c0ca0110907902c108140008960b840d030301c050540b03005072102c2e407440039681c400700c00a007991f9111480c0c90000030b0f144400e032607100009003080d0754210700720f0b5060781b0f0051000c0f5055007429050003135a8090344820003c02d00642c040d0842018604001041c0c802680b0303405d0030741d4840485a00a500300180079049982c0040d0f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 869849172 1250 869847922 869847977
    0xe06011106090304170a050609070302090a140408070812010816090e030d0209060f0a0c12030e060610090f03052b050702041104051f020613021c1110 66
    0x50026080902e0440d07228810382c014070606811624a0141c401800c00c200401c880d4040e044400514140d41c4564a403040c070701080b8401c0c0589400316150320098080c805d07030143e4251484800e6100c0d41e660b03140a030f015803012541e1680500015221000d0114220300a01044016208606161100c0603c2840607048003400700e01d4031401c01c11010002003901d0158008100050780c8110a4001500d64010003c0d10000c2590001d5160756141d41710342150000c82c403441c498800700c410340109805440354502c03000900da01002c000f400910700344060400305400381c1001c03110180c60301070504002d641e03030300306440c0780d8000e03180080340030030124030201e01d1100081d031a50002c40981c2c00030090b04c6001c030301911454032824000c020746130b040115001000d00418541e160310328401ea689002070109508800360083c400003e49840070706070b0b040c8100c0e5000b0030901d43c6d00020036841c46181d01e11901640c052401e03c40314181c944881401c2d0198000c203403141c01944400003144903502c87c0390b21 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 869850422 1250 869849172 869849207
    0x909030309030e010201140f0a060b0a0201060801060e39040306140a091e031b0609021009050607020607050309030610150507240e030d020a02010b040b0d030f03150e0601 75
    0x2c7c82648200703c0d89003440e0050703084940d01c012510346c401c2c1203001c0e045a4000c007c1d512800641c1000c0d1580544c071175001c807513032400288007003551100380f04400755040310030301a110684000c21642c0c028014207052800700420b050000291000780310500c80e0000d42049920395a0f03541425801c90b10407502d5a80980114400d0000302915960201c24a01c030a10981800c044525000c003054002d07010030540e40400c3c030441c405111181000000740113a40001c0e8007807000c880041007424460800141a10005449e6070b1800405609106980d84501019102c5000600c26800240c1e8240955406503410752a1900300b203043c181c0d02c85401043c0d0342c04109000080016800144081c03401140400030802c2911050b804111404050244d009140a450000188000046120f40d020300400c0e08035078000c1024801c007809010480e01000280c0e82c0c000715141e5030500080c4189500c1e00485400e190101e4000c6c803030341607043c01ca0004d03000311650b200798200704949542d01100c4002c400d00400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 869851672 1250 869850422 869850431
    0x1e0b18070906181527060203160f051b15030405120a0c050a03050301091103190213090203010308040923011502030705060c0a081f050103150909030309030e010201 72
    0x8031805808140a0311982d020b20000f201e507501046482e554690003001e106011828030b048100c00108148141100690000c981016202d02d4060b6003030000103580352a00103500d8601c0e0f140a0982804440008441c50300079142d00c4400210244502c080100340b003829603600c41f80740c10802890240f440150340c022030090007040b004c108005042d040e0100804605a505c1c1c044020403640c4080452000d01144965115401003652050096048418a05040020100080480c400da20003540d4642c520300b00d40001d9501d0787d010350700a0001c40c841184003176040c1e59a80f106000d03a0070907031007512900000700f007c208007180d0340034407142d118010303d00901911500d1400444100d040c0600d58a55071012244501c2900800c2220400c640200071540300c0e1401598001c80b607400030301070500084840021a1140c600c0f0112a00c84084003245060300c2418400110000c2030b0300210179442200e403200004000c3d4140c4640740340b42c1c0c00307a500030801e00b170701c0c0c00c0150006940204107411680b52 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 869852922 1250 869851672 869851681
    0x150411030a0f02010c0c151d0a06020604082d04050405060402032404021c06170f0a030e010201020708121e10060503150315100e041104090302011e0b18 67
    0xb902600e144107a0b09080020034400a4280194102001d4000200083d200800020600d80210703840000141c2c00941c001007030344420622180d211039201c1c42e405030307000c01c2c045000510008040c004c440c642010003400c0880031501c0e04512140280b2060095000003000e0260341030602400e0f80c032840030b460562131410801c68002c002c0c80300c1d40f15600d1a401500c0f204145644603011500c0340e00303c1302d50080d080002456100300405031441a400c035000c43c400740380038201340070070805484e120a20180c4240c01d242c4d1010703034112110b90b0300c103411035508010302d900098540300600703c2d00c81d41c09103190300c1c0d16040b1009800d40c050028031034600f030f49100802c00c11402c06c1c8034500560f080c40c9000351312a103c089491030314614a402c2c160307140c0506c190850319561602da266115200c1c0e138001100b49951049900003e1605036400391a00d100c400c00d0388c4013400c00313400100040d8031910000910025402c105800c1c002503040c0c4070301513034440c040f100c1d01d4035140d030200d900004016441451404d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 869854172 1250 869852922 869852933
    0x15050607060b042c0105010906081203091c030905010e2a03120301030605040302120a09121a040602190203091c081c0f1109010c140a05150411030a 65
    0x289440040c8041d4440c0c0300720b142074641c0e81007007608258080540a030380b04020746240070030040309a4010b081d0b1034040000f860b101140203050880f001c09010300034418010134413003203590004114950b1440b640b162000307102c0316042c2c1008102e001d503900050b08501c0340303089401c2d00d0700802c1d07800c3c0f250f000003500c250020810454030610075085141c0f048a040510100b4208058920600114900440000b080c01526009188200c4c8258203a075050f01c0e000300d01e00c2e4940120308101000408a00741400f5141181d1580f04c1000d010390200102241c8004240f0101035084070f040300c01e0f54001c030b15480c1d00c05d01d904020704005510b002840c00e2041050100d0b8103080600c00c120700b00825004108180210b1900b244c0009403103000d81c40c03041150003082c9014100010b0341e9000c05207042d15008000b40d040042e10000c21050351f07101d41c1d01c1c9280d16010450007108440b20340c0c6000d46400d030000100c04101e2a817174208140c280304402d14141c14007030304408441008500030b0300700300c0d41440041da = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 869855422 1250 869854172 869854177
    0x230a080d0b011e08070908120a0f08012d03050109060e12040e040b0a0204260c0103020913090302030f070c050f1023041a1c021303060207020f031e01150506 69
    0x140c0504c0d249000740d607945411103103258143d100400500400038800c564a01000c010000140a0f8541e40c0602020600884615200340b041940ba01c036904001c41c8440b41040100d503080d01e65100c1500c4107601c070780b22282115401041103401643d00c00700c4881610041c001d603580443d0942c40e00d8102071420803641c90b403410080006040f2541400020399400c62a4180d40150042c08040304050030000c0e4501112082102203030400d10401440b44c001d580f0034022220351070009801c512004403084100380281c91104c0c1e040301540800d000d001850180500580321890062545080380c41c50712381803041802280880c2030140304102c0f060030601e40c202d40150700341c84008a070340350b8450800400190b240103039082000f00290a09214107030f410080d015000c1e651042040c83c00f0710752020080e000320302c034100580d24100480c010400114210368090801c3c1c6001502c416000044200064208040d8508100748015601071080b0b01700c80c244124400c400000082c000c0c400d0808001420304d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 869856672 1250 869855422 869855477
    0x6060e07082514161202030c0127030f21060306061e061110090317070c2a03020a03050105040b0709060903080f0d050a1d1207230a080d0b01 62
    0x8070300040d01300105094074440340101500a01c400c9130480070b00400039141d034002e800d140d40301e43c2810340f450407905c0340000f00040c14445000c031040c400384959041c0c070400c801040d1941440200110318801c245400d80700c0d1055003400000055040c1145025012070340150070003460740d0044901e0a111420121075401555014245083c0001c0e20000320781c0303401080d207034200c440c90a2058000400d030b080440e140c843c40410045000302c1e9246a0b0403a0344460320400902010500c1c0d6048082c0540e251804001da050000c1c15610b054403900801e1490f07949901c2198140c1d5035104000910100301c82c669002070180c0780903640a0f1422400908610250102902d400e4001a40c034203000c01c803808481c104540808280028982007103a000200340207044008a81035200510540c80740100b107651940701020005410b045158640114201d800c0d4000380060030041032803811940d0800c450f00120f442072400507610b0141200d400b05564801c7c108a05200d054014005005d03a00354100400f13 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 869857922 1250 869856672 869856707
    0x301503081803031b060f0c0307080f15060c0d1808030f18030604110307060f09090b1c0b011d070e040c030b37050d080706060e070825 59
    0x1c4054060000381103114054a5003904007450640e844094030209940d486030405801c1110b0704d9071450901101c0c0e01c8100d0300b4200103001d100010706000c007445503064001e0a04c0e00e01c84181802100410f40541c054860f20f01c595018400c0829041d51121032512480000b03511400c125290a040940d40e0203006944202401e0102c1c008074200e05200c0c007440e40c26001421100c0d20304050406104203491621200d020b030117a08000310304103016850300e0107045165660018401d1400307400c42d00401c010a040340d070040504030b115143c1c040b0b2035084a0b43e50b00034501c4603d6540740a14078078410a4805030004503103e00d0041000060700100c60400c42c1100340c1d0046a02e40185c4012001000c0381980280c2c0840404e01d041030641c0c801c8804000c5840000390002080245031166203450561710480b0b900044104070900010211b102900200c1d108600c04222192201c00c03008160303100700e0315040020200c104103c610117020300c2c0084e580b0b240d503080308070501859200501c101f130886032030380b803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 869859172 1250 869857922 869857957
    0x240102030f1602220606030e0c040b060702060a0503010e1303051213050102040920090306010510180b0703021b030303010909170f03040311060c09010f30150308 71
    0x2d0790100800b410181c3d90080c54844109039a100029441d03401000c0c03248444c0ca0200007180d401c0c00303071140a554412200041200d6038800c0d081101074420041c0c80754211205000801c010b880e0304002c3e040540c415103030340b520b940c14542d0648202c900101555041c044900c517050209801c1012101e03006801c00090380303550b5030301044020f03039122083c0007403066100060000d142903c580c0041034410301c07110304c4096682c01151140c418061b001c402270b03160b040400100a1031410341181c03c0e00000300e080c0005c19000c80d03030488281502030b90100150075000190035040640c144034410420107a80004c0041c00c3c01c040c00310340d03203000500504003040e0790384203520244607403000a0001c0104191802c1c1c0e40e202c1e15450700a042d08191421000700d85801d400b5045010003181c80c6115032000f50a56040602040045480105110301c141c14010030442000c0c0b2540700b4600f50a18005007504821342031800440c1da030850b01d0000078444040d800381d02c24800601c824044540c9060303107100c140b8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 869860422 1250 869859172 869859187
    0x60509120a05181f05030915040c30050d0e040212010e07050706020f0406030b0306040b0a09020a0819230c0f040b0607060509011112070332240102030f 67
    0x440d40140114824411080b82d40c90240c059844401148100704100a4134901c1c408000d4039465414149e0f0001d1407401210405e1000441403940c100c86a94800d094200110f961800305201080003175003035800707421111400c009a60090144c26086c03009035004c6180c40c0030010741e1a09450180103500d0781d0400c00007c03a0105e441101079038a0302c1e820403030440d0b0b00d5014440041e025441482035601003030420400f11103910380404c3c030502c1503410035060441c507900c030743d030f04001004506000c0340c2c030020311a80070840080802001410940b50b0700804441001401d250b0080c04801030326038184050040d410801010102e40d2013040b000036504401d0211083d00060041c0051902042d044240031030b40600b80580b5400c003a014506150081019468801900d1814800e080800100c95000c03800b01d441c0074401d51050080c081d0015003010110f055440b08048110b0300b450f5941740882030414012099146c1d003418003520318240b0705000c440e65200020351a8010b14401c03403c000c5021aa61 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 869861672 1250 869860422 869860429
    0x1804120909061e0f06021b0a0f080a230d0e030a240e01112508030c09010806040506090403051e031006020c030d050306040c0903020409060509120a0518 67
    0x1403000d4074820905224098030303800c00451054044072158401e0040c200d0000707002040380c4c90b400070b5500c01e0b0302408a40e021117000340021443d000034983c01400d0480300048107800310100c40003608491025082c2100141800400c2d5091400c001d44804003103100c040103204005501503090715141480519006410002803c100f0000d2014003404c45500156214880e80400384204d8608110204a0070301e1700303c40c1500302d41200c08407030f2a20700100000c039054900e440200c03070301100690b00c081c01e08009030307107110440c0c005580d4411100c1010580340c4c029a005443e640d84404159010021303490030000080c140304024101405110b000250514403581c0d0010401002050281066983c20945d02c1c03503840360080d00c6160b0050181080a1a107032901059648510040d9620641580c45101c100002070400641318028840c00020000041e00d443c007880c4461400b07080f0010707072454800c1030182001140c18054038207020420408184540120582e81d210030400e04010b107400d0f211020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 869862922 1250 869861672 869861687
    0xb0f040f02160c03051510061d0a080303061e10030903090f0305060f0903130510350c070b0a0f090503070b0a0c05071e111206060906180412 62
    0x4001440800e02d1140341400303c0c1e214071a00f00c030b100d1011101c9000c10300d0000e015a010640740b1071502c501494040148521400320302c03c1d43c50008007511100030f0243c000a00c01c0300d01d2ba0054286801c00b004101c200d00c4d000744002140100b140b00c41004840f0000002c0750290383c1c0103d40c0600d0340d618100802e0503c2140c50381d015111301d0001e20441902c030300f0429501c403411110801c070f21030b405001a1000b40c02000382c486290f18965814540d03824401080000e0100c1204542007003d001c042003880040302203180d0510100c0d1041b10940e0403d01e40030401004000d001c000b448100300300c0070000074012203a072030348248400e0b400140c50344d00407150000740c14a0740d0003601e01d04c40490300c101400b043d290901e00505081000304108120140f041d2520700030840007600c0c0400c2d00c040b0f0750b84a420b808911500380e11070350b441c040084800f40001d004880703007400340005911a008110542c02c15601e4140c2100382210706219440498001c130001d00e800400040110072401a0b400409008008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 869864172 1250 869862922 869862937
    0x30d0507090302031623030d080714040f090b01050304020109090506030102090a2c0106140304050f0a0f0b1e041b03120c061b0206011a0904150602010f0b0f040f02 72
    0x5641c840c00305407070851201e90003405000c01d020758946c4000e02d846484064051491800303805807040207151401501d40c0e0f40700401c070701e090004ca1200344080d070021100410180030a416038041c82130511005c10112281420460f061050410901c000f50b070f0420328150858604140200c0c03986c0e1000c0200e806030044860b9240c01c009444c0c0301040c0c00d201d940c040c40c0300d03540704042c9507000700c586507402e22080028401c4101003a20b8000910300350111900555004cc01103044804940d6141d1000b4071384640308800361203040c0c089080004000c92003891540210314815024241c40b940300d04d000c01da0f4400307800240350b900840d40c1d0008001041e000c41c4000c64000b1a10150f10031030300005082c000f1401002c5482c0c0d482d15030000d81217041c88100d01e802c00d400b98018851a82498058079010045810501e80349900b800035100650351409255110380544a100c000a458800080d0039500f00d040703103a18041c20009506038644648105181109080300c020627045040308407074009208194 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 869865422 1250 869864172 869864179
    0x3060103120315060e040b03160803030f0c0406140c0a0b0a021c0203010311120f060a0c080601030902031c0504031b030309170706080c09030d021b1002030d0507090302 74
    0x1000009100d49051441140e00c01502c0c1480700a860884043c420b0006025540210b03c08400039200380c201907001c0c800742280035040f9103801c1440d20900060b04151351065807644c4c400403c00151003080c03143c0d41c0e0000452030304d450400f41001c80140002e10ba4613240c00303a03107a01041c00401100104480b20640b0340114210741d990500d00b0701e01001e9402070041d0b0400c2e000640b08108441f04038821031b4101d0b6085441e40144c11041020000740c0f0b076411100200521804030743d9243e03aa800d0010501800250303500040c0d8010400c03000d044070800504840c10315140c6018040075840c041200071190084185604406100801c00c0e900c0b80941d400c040d0601400b1400803850801103503418050364001d4883c5080d0a0390303803103100c00202c05551205402d4002c20401c11070140252065a000400c0301022400e025640004c640b51104440510380164852020755496024904c0c1410f803030300f0281c1701864000c1a84101075034171711500d030300d040780c0d141c1c0c900005441c0303440340040d00060b543c001c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 869866672 1250 869865422 869865433
    0x61b050301060914220c031a01021b0a0e0106020a0c050907050313080c07030507050414040f08030402040f0e0c011107050105041e030515090610050d02060306010c47130f0203 77
    0x44030000c000c28031008081b010902d4000381d203003414804002031144c9a4141c0c01061483c0c0c0f1070b0315120820b4001d0036401e80101c12074901090080415009502a10460340200350030345003402d0060070207403a58003441c0551030150611059941c8a41229880718a030300401010004034504840544925590a0740902540f0b4010003001404640003007200c1003250103112503121801d600e000140141c0f0020a018803080240300000c41c2e05d0301465005c2e00007000040c1030050315000d0800d41d01017178000c42e156000000e2030511903070015a120044240072000305011414040003174454402ca00a140c915503203455840070842440345030b0800340d944207003520008640b421030090410f4041d03515064a0081e0310002d0942c4014030114070407100000c0890040d6038040e0244600c1c1d6001420301410041040c0b0724601040c030b4820304000c0800f0032400030240452680d504d0780d00030154600822521020403441d0303001c498036802190007901c0c01d1002d00c4601e03600d20744041c134142050381c0290035010783d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 869867922 1250 869866672 869866729
    0x60f0310080f070807140102030301030f060f02040b07210516050c060d02030708010e070f120f0603233c150f0c0c06070509120703061b050301060914 66
    0xf0480208498812040341e00e031507103480f4900d9690480313501c914010380c02400100040303003030620b0401003140501000200b008010421105981c0190441418040002000f10401012070441101a8000204030f1303040e043d95000180544141242059542040717140e00d01400030500c080d021858000f000aa0345000f030700501d04c060342007241c1a0011941c2c1c00300000c0c2d610454160076214118903a1100b0b010728039030409a0340358801210101c0030b1581c030040700c66008401d115680c0918061588203010003d0313030000d80c442c42181081103c0680202c844c1c3d50b503c020113144001040d0520210108681828801d0000b01c942d9000904180c8294241c4420808000a0040c0185241006041d00360340308803000e0841d205600080806910400005029500c10310140203141001450700003032251840c0700f180b400205400035114030742d40e00c002e8a41540c00302c89003070b00b100090034100c1c21585403801c05484046a4441ca90411951003800c030a2643d5104494500c07807d6280300b030154014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 869869172 1250 869867922 869867953
    0x6090103061a1c060c080103030e041a09040f0c0906140f0111030d02040f060f020307030e0a09020c030301080106060305100e0408090d03020a0209010801051006110a0f05101505060f031008 83
    0x788081504c030340303141041050f6424402d020060582c0c0d01502c0d0300f1000f4140d20144801069008168040410b030700c0b200000396560707003842a0183e0700901010340d040c0924104140c0300e907959400b6944091801d00c01704501c0444403248098941c08131204407020900c400140c0c2d50304c40c0030305000700754040003600111842c174540c0548240e0b016100070741c0c02c1a4644500342c41d10801c010f585405030388140040c000191042e00080300700c9030043c10420000e5035600e1700303000b85d030444495989035030004401804039000911034080141807614060250f4200001c003141014210f000307861018030600c0000d424003140e201220078000340034208042580881c20002c2d290760315200304034810044200001011070050003054019480f40c2401c40c00c03503141c050203583d0120401d500b80745074042d172121140800c056221406d4030307a02950141803441904076a0104540c0c0142000200c502985401d00480d2610029640c100c0b0001d502d0b00d03030b01e07220032060b007030311910a5010300402d01c20602181114134 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 869870422 1250 869869172 869869219
    0xf1b0103091b0f15050702062217010c11011a1201150306060312110c0409020a0504050103080c06010909030504141908011b03020c0d0e0a080303011e0e06090103061a 73
    0x640c04804c6400d5000c0a2004850900c03c009020f54001c005115185800000b0050b60201c21250803d030351001c0ea41d05290705811911070704014090b50758a43d0301807400d421000b0b508000140d04020007070002400400244d007211081070a000740c5072480880040c5600358003060046840182c0c804010340e4070701e8a0006000d260000300c5816070811b030b18a204901030582c4040040b45103000c0c182c8038000780e003404010a02100b090307034403503424940020241c4961151130b02071401955500c1d91400c4811481e860007006070b114111947c501110040030a5021056409a0708210320445003001000300180801d00f51404090015040c00030005600c08154050380768040202500c0142e200b000e02c0a50803070142200e00d00150f00060300008840e4407400c1350700155003005051454a07a1910300350741c0303160026000f03103a5031110ba107143c2072a410b16021075401044a11000d010900d070580c0800c910f01410b103c018901c035120f08501c2401c1032070310700b507a903c180003500525001e800c0001004846 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 869871672 1250 869870422 869870429
    0x150903160813080613060f14150913150203060409060218010e010c050c090c0f0a170c21090c060706020702040b0a0e04080c1c02030c0f1b0103091b0f 66
    0xd10402c03000060403a00070851511501c05603007580600c40aa854020103814001a1446c038555100490b1101c4410914294050f00e08111210500794a28007841042000a46096810400c01c005000010000701c1c0304207201801c110b015840e6110003000c02c02805180308010030881c00822020038510100c207070100d4004090340e075042403c56102c019070f00d90100000c00b40003074006000d14400ba0801c1d1481035085001c00750310f5498920100c051001a4004030100d2001428905d1070100c20000040615040449000f501b464680154001c0ca16440d480c0303c142c41000096002450600040c49280003290018000302d83e035802d00d18203440250301540040f485941341201c03610710750612860000a4400c1e0302c032607007044d484a4807440302d01d4000c038440802c0c41c454241200c0034280f00d00c0c4c409080180b20340086032555030fa401c49509050b10f142d40401d40b40c1c00803041440c1d51520550b400d0000701c0c28200000e15903180d08000c0070324044c1000d40e1090b50003107500040d06030140da1404084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 869872922 1250 869871672 869871697
    0xd03020a0c0b040b1204020f1c12030c080604150906060909150308070314070f110f0d030e15040e13030f0804050703020f03031207110d09081509031608 67
    0x2040e1242c0c40c03480940558025003892003400e2004a1481628018603a0003600040050541e02083c60004098500d002d40120843d81503011680800c0285200c61201050b00d040500c0010880710000341840c0f0010030039841252140c00c2c40340c0000c01c0558010280000c02002e20200c1e4a40c100604440058800c1c185554070b040c1390100c540070175507000e1007600c0e446203c00346828413545023141c50b00504803c414618404014510000300400c0d0107559041c441e5058000107044081003000000d1031042141c020524200c1d240b00080d8460380d900840c001c112080e60520310f00c019000c04a0080d600507003119030a520030f02513518a040d9a804500d8030170380e2034040040da2494100d6030220240c40003485a40441c1040c07005280401c40030190b20805401c0f641055290040803c44450540301c182c0466030b14107440303142c5481440b1f192045c02c1c86050004a003840c0c1040b95a4501c50b0210003520030302e5003c0441c1101d0014021101d49002c1140290080d1007141058440c5038004d00c0000c89 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 869874172 1250 869872922 869872943
    0x204081204030b01090c12060801320106111f0b030706020a0b0105010e01031b0c02010809191b080a03020709051b03060f120102040905010f120f030c05010b0d03020a 73
    0x6404008003141d0035a0303400800e5808a91900700751300090a103074603101b400d0002c0c9400c0c1d013642400714802d41000f070581c5000400c0b100d151a4609000c914202900d852221100a15055208200710614111a140d1800f42c001c01c8402401c9810550084c1155409403060b030081d18075485190400707601c4603c202c0564017800e55504060784c3c1c4a00042008080b4410303540100102d47c02210540c0b0f0060b0181004542450100300180d5070000080c11307800410f403210050000c0d942d00c59030a60380405040000d0603000303000004180c02c00d4000c00e0040a07500e00c4911100c0c0042000125402042e400703040324040842890082d45941c03450241240292400000841d265050255030b014101c40c2d0070103500d5901c0b5201408243c500426502c0d82200540142d5600b03200248028801040d058070300140c02c0d4113000c00700407005a11341c420341049554031344480100f61030328104880540c0c941450652103805107481805058119181c95000c00d0b4070411070185500480c03c0303c0600c3c0300e0b030b10454 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 869875422 1250 869874172 869874193
    0x24041811031005041a0405070902271203070611070807050f150f040b090a0503160c0e063003030403030504030e1806010c050c040f0903111203040b0a1e020408 70
    0x82103603c00c0320f015103000b021084181510900c035400c260064020070035102203949030814101660310458103181000700007103c2490f0b04c00000080c02c4124401c0f100d45038003082e540c00455407402400d80261546944880e211100c82d40d000803680903d0303005200544070411030400c0c1ea203480708440b54424030301039002d501100038140d0340140c0c800c4000b016010425155078583c64541034000340352000920071040040e01003003041000d4a28081c800c0400b00d0302d5540c2d842c09900d100040d40c0180c40408d400d0007844100c7e40c52804408281c0d401c051403c1b02d021450003240f0b41035424003100c04aa00000044c070060580c0340c0c02c194400d44c040d0300d610056151140910505034800f00407043c14a1109011920b0b540c82503013401c1100e03005170111091840d44000007400c0302c200414031400c00390b50b420220105078104c003032602880b4101c0080d042075100115800450304c00100010186a00c80c40080d800038019031020710f602008a103112411001203100f100254070500991102d84501715408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 869876672 1250 869875422 869875453
    0x209030102070c0b270d080a0e090906182b0c0c08010f06120203100507030921080f0c07030c020a09150e180c040e0a05061f0605032404181103 63
    0xe0f25260301030070806059440c0c0d2174808032508a41c2020041100c0d109d502011961030f18403c0340614143c00c050155820605202032201441018040c1c940e0000c0d8500717000c69180341c0c03007821141030f42c030350702000c041c6001c07812500a00302240081600030050f00100d03540c2c030154411040000181d00400ca600d8464400c58102541d4400095041d4040300320300320400c24541140d500076040d030401144120450350740061440181c440710382c110031202c0c81070701111703800313003940360003140005000030641400142c401940c4200140079040c0300c4150288800c5459a111150003071100d8282006290003102004007001010312075024100c1010012403d01005083c5500e0007a650400078507030b00d050f003010700003c4c005404c090f02d10fa0041d03100c100b000c15018013015100718020025142081305d000b54441d12104140c02250400c81c1c24000c00655803200004444507048003089206c2d2080c1d8500004c000c0e18401000c4001459038500130400c200d00e00340401c004250440a0303412400c00762565 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 869877922 1250 869876672 869876737
    0x1051506090d03030b150d14160c0f0b0a0c020f070f06030f1b1205090106032310020a0e090114011b0309050303120f0615030a0209030102070c0b 64
    0x81560004007004246000d00e0503070b800d0700c00d01c1d22a04003c1044400d66000904050288054501030b8078002000142e982c2c05104031429008000901c030080d0511050301e40400c680c440182090080c40d440200500c030143d4600c0701e03500d0b88100c03031100030b1034403954070070290002e004d080c2e000d80301d0205920091880032030b2a1003035a04950741008000d01c1c00c07004a002d082e2807404484080d6030b807035010000980070400040318603125114021000d031042201c41c120b8400030400c0aa40c2d1603d8018000519170300901e000d082c1651412030109060340c0b050500f000f400781c20340d502c1c0c01d20003d15070900d40d4110094406030901299406020380e80c80c4041d900f0551040c4001c3c2c000707100180034a0003800c1c4180d40c940f40602a00d4642d03040c1d0745910200b495a44409898896a12198104032040741c07040f00803503104205441e02d02d800c2020910052043c00b01070032403c41141c0105040d42d0513142503055a034525000407005007038994400100080c1d9002c03040d01c0704e4a4405041c030110083e4010b51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 869879172 1250 869877922 869877961
    0x1b0906021c050d11160501020a0822030e040e011d101503060903110303100906080138090a0510050d03020304030201080403170a2901120e0f0313080105 67
    0x44076443c02000808200c0144003450007112001c0080c0030500307502d200002c240204c680300f44001647c03103521440241c10810000d118a0301810220b1000c000070030300d036960210903981400c01160071090540054003425451f0041d091a40c80d008040c45111781c140b1055040c030008400b03550419944035105000d40c0d0440305101c42c4041d0b5400208005251079211048041c0070f481e0103840c0c1c0d880e0602407800d5500c1500d41c51a40f4000f0310049c02a010548201c5008141c00c0b1b0017004019200c405100440c0720410f6500c0510f0f820103107181c2c002849500e9008c0058000342610441e20381110039034000e000581e402c80074440e010700041081c0c00c00d21a2920b005e600740d0001d50501d0700e9603004480410004104904000400c01441400c0304402d0341c1ca07003d1440d42c0004100090760840c0b90450311000e150018400064281c0040c8590f0050300c1034640070301981c0e0103d080c99443d0a40791500d1280c1100010030701c8000b8500300c0704180301d0410f0007034406240c003d01079030700e522102c441c0e9481d8051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 869880422 1250 869879172 869879177
    0x8060906060403031710030b010e010503070608070c02010e120d080f0a05100b03040c050604090c0f021209060d061d0a0c0f20010f020f0919120f05011b0906021c 71
    0x706580641784480900c07607201580402200405031290388000c40300c8403c2c3d04c003d0003810b1142c0140b05516040c0304004c0500fa45290200040c50300381c100a1079034840b40c00280c144460802540b14548420042d41e01e610012001c8440ba03590b07000008101c0c0300111140d400003c1d94401085504d20240a9913001d00400340e03a0402d07007401c003070000215a1020300202c4981c030707002e400007038240c80b5000500000c154101c00011190248c000282424100216140840d04454802003000703001c001565506901036413065100e80c103042012008002e6500f140c040c03000820707408005510845001e80c406c081411060084504103001912151140b1310704d8008240c081075007142c040004140d8039601090100041661b01c8880020402ca9201100084607404001820422400d0507500d401d102d400001c81d048000c0d2411350f110300407a45060008016115040200701030050940205811080c01038203880710a81d80100500014098410700703016005545012110002c100d042d12996125078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 869881672 1250 869880422 869880437
    0x60a03031202070209130b0a1e02090a05031b030d14030f060d0c030b07030e061b031b1908150d11010203040306020d050906090d0c03030f090807030806090606040303 73
    0x190340903614034585039003010384207500f403003800301582e14040703c0341c011aa070f02c580d20101480ca04044459503402010503514504125148542e02440a850021451202e0005858448507000114908059440142c3c580b08604608a04041901c040c6019000031000c903201c950060505071272010b50b00381440c9058000f403001078206140501c40c01c0d4454402040c4490080303c42e520310128998a81055945001c4e103400c01000e250944283e0700c259040030024080b500e08100860004442d0a029000060001c8045010a40003e1080040c000180340140d2148940c103013044903803c2404144002410b00030118122886a003021010200090490b20098034a030721805d02e403264540b1854110301c010400080401c0192020304424a00c500021445042c0b400d2020314044010744151840c1d0480200c81c100d26070044a154980e0382d2504000c00d04032043c1803e4001400d40756400380610b4000a0203008061380030200c90300c10501100c0c4280e040d00c0c4c1307505003c564001c5000003404180f01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 869882922 1250 869881672 869881679
    0x308040611040305030d09030f03060806160504080a050a05060f062409040906020705070602060f07031113080c01030f0209150f071a1b1e030405010e01061202041103060a 75
    0xd64200e4510200ea0324500351605a8981d19a440c69105142504200c2e680f141403a04142e800409c005218689140610140f4200800c0b940c45503009082080c180340e01b034201034099401a030a40c0c0003029040c05640c0b1061190074400e813035020380c0e14102e98900a000005985944400c4050b00400000d050b026004941081c4407030480118800007581d50000c1c03066100b9075459005481c5214454500940c603034140e4505240b40410b00c2e005801036401010420080c14646605113600c41e005240114140c030b90b1403104400d503c10150601c0c071110103841c0110391a00c1c0010020200781080e40c040003010b11040040040f406005001030384500340790b408580040c88980600464243d00b024035180102c2540e1b041f0400e034404a1044445031000c08000142d48030440400c5140224603100d89032244e084400c81c80f00d043c512001d040c4c0007010001c203017400025070141142295207402041140e8a50702c092080c509800022072155040150294400382500140e9004a0f0064940f4011908 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 869884172 1250 869882922 869882933
    0x17011506030c090e1008010b0402040e0606030a1b030204061d0a060c03030f020403060b0a080105090c0d1104050f1b1c02031f120b0f0f0f06011103040906061803030804 74
    0x11401c040380100701d03541d4004900c0d0803050b0060b6014901c0000ca40028524080340c0c6400d523642c054a5510680c0305000030488040c807a07440d140c1c0550304842c11a640d6951084150082160f5103040781c460030b0f03600011102c650154010030035921580c55081e190722031784003014402807036000e620741c020311001c508000f0701c0c1c021103030900e4503403103402c0110750ad15003400d076031b0100e82255000b6200c96403101010807181c00d1800c0e18601400c0804024480da00d0b040564654481c3d90b07809040c06041c0ca00928018040ca003d100c250741e103002001404503027080414004800c40c19901c4100101c5488605805022461b040340c81701d0b0441100f03480c81c0620810403000a4000900c02c4400c0a0fa103080e140c910102010004054800c010b03424100075014102140c003040010320005080003440b0034441180750a07000107601c40054451130500d541d40d03100485118029103102c6400b848007080200c2d00c2c140c41c0d0059000e5940d56070b1079107110340c0b40c584081031590907440b02402254840011401023038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 869885422 1250 869884172 869884181
    0xc3301120c0e0c0d29010c030801050f041805070329180f190303390509030f0c0f0a0b0a0e0303040320040f021e0309010e15011701150603 61
    0x19083c502c5a013060901c5a020041c4c8a074005401c00c000c011104062107102900650240a0360a1a00d4090700c071a943d8054011070042c011103110b0030050b1304150a699070f5400c07140d103000040d1803110700c035042850306581c0e5241a000c1220031010496030401c1c0c1d446e50034089d90000002d00f0b0046010b4503141050321803884c400c905070f6000c0c0110101c840080d80100000c0300341e582c1c5030b454004e00c01d0041c14000c0c00c8070903d2014180e8105c110500c20703204c914503280c82c1e010070500d040c0a2401c191504055419101e400015501800f81e85200e88010b03001280c000801c030829150110040015810490605064012948688002d2007100340d4640314102c0038400d02030240c11079240c180c807a20b410081c0108022090203080c2040000d04041c1410b000c0e18034030b0320071280194103107017185000070304648900d68009260400071002551110003504110b010002c0e40013919004050b0169080300b0200900414500c110340d4101480c082605100d46100114148401c00109080c101c1c11005003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 869886672 1250 869885422 869885431
    0x1a090a030e151207080609060d0303020d1401090c0909050c220503120a0f030b060f09210304050108070906020d0804031709010f0c05090d080c3301120c0e 68
    0x401e007280c2c0061444144000d044140d030103040c4460034940128000c180c114002c1205002c1c0001d0014041c00d1345415403404204d60b8507090158449102102c0e07900204980140c00e01c402d0001e900001d20f002060340201e4100c40183d40e40c00605841d04e81e0041544d0341a20904c160a500308110044008403901c081010040d94400c0e00e103859941001034034102d550600e900b8201c5000074805050340e040103217803036001c045040070b1080c0c400301c44c006602801b8410740074541d001d0000781e07145a503803044010403da5100c0c121864090b540600032641e00e40050242d640440c1c48a804601894051200c100489a5950041000060110b4120345480d400b5000b1402e02c0740c401c448900b241c010742503091144040d1000018001204a40f0205881c0c1014940007880f90400c4011184e0b11280510a180c6030404111651060070020700c5207002d05550361007240e0003500300c07000c01355074040c9a0150002803104003080c0903600c2e060a41d00c1c95126240040c0031500e1000100042c402000c1e400307600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 869887922 1250 869886672 869886679
    0xa06090b01140306040e240f01050f010804060b06090622060504081002070f050f2d0601050f120715030b09010e0a050c090a0e061809100917161a090a030e 68
    0x3c941594800600b911f48800b082800c4090603003081000301c035001d8007500621003240c0100d40049400b00181c000040504054411902da4000302c909403658030880e1903181d4003605055035001c00a4140301c0300e02c030710503544036404240d140014080e4804c8082d035080e6681c11020308992990840e140f0300942c0200303030444050b6401030704440030403010320205814000d0100508013620b1701d01600e190300c40507a90480c81c0c0b00386030b1001c0011654006a041c2c1550800c1d01c020380c914a501c4000380da44401c0c8040c2c103115200303440300840d908403c000b05840c840c50680b030a02040c01e8410420140070024010030354001c03804400107500085a8000641020789103168500e050103410120309043e015800c00e4800003e0b0005012480c02c29452401510943d40c8000c441400c050148a0300c4602807141d40d062180c46260740c07400e12100d003c844c0c0303181164181e04e40d41c60030580342c14007043c011510180e07803540403494200543c1d01c517102c40300e11508000c3c001e800c000320355917015500c060311141007941 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 869889172 1250 869887922 869887933
    0xd030b0310110307030f050903071419080d151d0a0f06080c0319110607051614100216060c08090a0602031c06050a2304050a06090b01140306040e 64
    0x109000305125a08212010040741a584d01d8624000b90583d65841072800300545000c0401220030004400c0d2034407141d002d64004004d292032100302d450304000ba00e0020240030442003100c10080080010803c8900282c8140101c01c0048542d03101c000482c4200303030b90846000100c1d07071b01a030301850103a8468404800001e0101c4813181000c115800d64101c94450361180071180e02c01d1400704038800303440a06042c07116042032244e0714080c5040c90382a085004032004501401040010700503032481510f0034010202c05035803a00da0b8824008210120360082080d400c0028003544040341ca40c0c03c0b105406003540105281c050304844c41c1050140c00e42c9e28080c1400030303005640d540405480101142da0045803200001d462511950110a101c14082807620000700010384620134030400f111000000030907984800315142c5800d58800c14442e48c001d20306401c00680c0e901d07a41c00038040c6c0c0c00e0160300300100e4100000550300031520080c40c1d101c2007005d0000444034509031f0400b103140381c10001500d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 869890422 1250 869889172 869889193
    0x3160f170f0a0c050312030c0f03071103132103080105010f020a02060d05040b060d1a0406091202101a130c090b0a0c020306280b030111040303110106080a03020d030b03 74
    0xe06000701480211003c840e1002c040015103800c008251003908001640c034a10300301030134169020301c56007010064941000c0b000884a0380107142414140a51301c007980d0b81d03000c021304205000c40c2c0e14020711704210340c0a024022006d0001c451001c840d64103894002e15a4204401941d0300c1d500701d40240214440e10040c0d00050322484064040300010080c0030420782024600980850001885180a04c04031124480488c000034050320b00450080c42c510129107450501a02a110148014007100f800d13545605006500040940388106580d004010900c84001200e01d100d0fa00401c2c50fa014040c3c082c80344484c503169014881d12550750070401c42c1280d407030300c10802c3c503048000b0f5a000305500d8100c0f5410b41c1402d2000310ba20451840740780d48000a02a030b00c500140c6020b071443d582c50340d140c850040588007507102e140000040c2662580b555540d03d0000e0204016500401d40b650a0820000b40d846001400d0040d1591540107032810511509080b0010b0242044965051250100c02e8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 869891672 1250 869890422 869890453
    0x50c030307210c020313080d09092307050a0206060f100503060d1e17070b010b090406050a09020a030e0a02030a08251203050916150e1002070503160f17 67
    0x40c0b007403d00c2900916158421816500b1907001d05510440407a00a103541c2d40d0074581c40700d01c410954540580000d80544401906841b185003d04840d43c0354006c041400b950302d8000c8094600d0004590890781d00e541c0781c0007400078803980c540d00f8940001c0880d20002c80ca5014502960748490007410543c408510380c0c80e6031800b01414401440034900b00034404040c0001d50907145062082041541d107410560382d140500100c052280300781d04a404100c82c840c0381c1e907a400840c002c002c020603641e0742d9521a5050002944144d40c03404c00310f45810480c401b00240480c4c000300c0030750000d0180113040398680f241d40b0554450704c001c04030b01c0300c560019100342e980f001d49411114040c0d5000c003650112600b0103030441e0000340c0000c066911014007a0320705081610f041d8242d0f000c0391201d00c0e5403030074590191012003404d0300707460740a0b074601440400179030700040d500202c9408030207c41091441d00c02d1168402541d00503608a41030804062101290301d000b201c03003c1e80004101c1d8035040c0e112220 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 869892922 1250 869891672 869891681
    0xb043c0b090114010f0c080d180b10140406140108040503130803190219030f030e0a0f020306011a0906090111030c060411040606050409230c0c0607050c03030721 71
    0x1c803e48481000e100d075255603011004020810007401e12620081480d1224040c038040d407058403642ca919041c0d8408510030a0303100c0b50143da07008101c0b4405040403401800000004d000c0c01549810b4400d61202a2509000300e1040f50548282420146101c000445149000030301c00c0c1c071a8441041078016628040d043c05005021030409142c4600c0030304044e10382007201c0d907031584c11903020700150003c0513041c062442219515040c80c0c5007946030240260040e14070b108044606002d204400c00510640b4031040386083e2086081c2c82d1319a80b61501062009942d040848041e2810300032070085060880083c08403a80504090050013202000b0910b10f600441c02c0307a10a4000609000420030301d0b003050400c01c60112000d010081c28107900a2181c01188501c00045403182100002e81d803603040b902c07480b45035080e2800b05600d440410b03510550f024410007005841880006003115201e841614400302205d00a54135684517124200e464181079025450441c08041100d00682414800c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 869894172 1250 869892922 869892929
    0x40c03020d080a0f03023a0204170106090c02120f04050909102a05070c0911040f0e070e121c0c06060509090717010902030a060b043c0b0901 62
    0x1079a0380d20680410010401c0504c404080185030042c420031f072200c4a10110071502c0003000d00380d5000401034180b0000340100b01c420070032601c0d10019000c00e98504824002c0302c5a03010704004d000d19543d0359094421202080d0004006800c41c030114440e0824a000410381c2403500d0842c6800c003511240046c003200002c1e06d1002031580314025500d908085030003040d03107000e080c060781c0582c9402c0e918522191112542c02d8002c020000540108000340000701034060480d002e003c104034215011000d889030320600412201710101c3c0750019610003650702551103101e280d1340300c0c502a00e901c030600a10381401c1c0808449805103195151f46070301c0c10080381144050f0360b5039003032a040c05400c003a0225490f84e081240030710400003c01c840041c00054140803501512614054501003111440c010510100c4c000d5040c081c140950041c070805400c03005c2c8a0034215002c0004640818501004050701820152440400070090072403d0490b0000324515207009400708050200e0800034100398002d80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 869895422 1250 869894172 869894183
    0x27041410050f060a061209080d060f0f090b01021209130903030218120a0f0c0f06030207060b010503070c120207050901080106080f060f060f0f032b1412040c03020d 72
    0x404002c03a00003030a15080d007041c1c040d0360f801880c606000c030041210700031200002805455250100800c00c115003100d100c005402001c00c81030742c860b001800c003c202840f444000280c08400401d00d400c0e01e10030000200c3d416002400342825490360204550007030301030ba55100200558440b028000b50180c2c0c0000c2d8840e544c01a603078400350b00c0c6036150070340340f250084c0100765520900041110004171000d5441e0020116110042549010500360340d090f002400b000b40c405a0000c1c40541503005420b90318410b000a10547e040c110045421340012641200090800740007d4082010404d130800c160b14a4415114003c0d10b070004610313030030030070ba03c03444a80c0e6560208000f1510140002e112200d001c2018103040c0c14100d401c91041c02010300540d200d140c01c44400b1410751703102284400c850030301a0540b180030310a80100340000940d01d0341400452514103a55022504c075400003130700d1002186e00c0750709100740d00458a18094005004803a500501d0f036010001d03940d421000c80c0e40c10301c5403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 869896672 1250 869895422 869895431
    0x1504020d14011b141204061e05060102071a070f0804120f05070503061b03060109051e0103050c04270b12030304030e15120403020c210c27041410 64
    0x40c00301c55400030040d0b0f10004000780141341c03910103000301e81240d200301050b1030300045a803a6818a08010407091503421400386055001c5181d040054000511400f0240c00f915861039035000c8a1030540783d50a0a500e01100c2040300e08002401c040149407002e00810a150400780c42c1c94000041c0d00c029a011f940c083c0c1450304507000c20000300700f00740190405501520903801e0102c1d0700403a50844031203c9062450101c0003d9042c0d1040d00c400005140c01046811007080d001300c0110030020580107103000a040c4000034600314008401c4030f040310b003071160070420216600000c000c104605d0343c95480c5c00d0340302e03160700c041c0e40da81c5807202040c003000d038002d15982d0500d45409031060700004041d034091580c1031020940e00304510155884440702585c40e0311190785a280c02c9080807603100c407041e80802c0200850314082e040034040c0c143c114074001120403600140741000780c002210000c0b6084210f131280e007070500c0d00c56a0030301a0400e12810300c8034038540410401e5400c040c841614412526902c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 869897922 1250 869896672 869896691
    0x815030105181c0e1023090f0904030e010f0915210506031209030a0f11011b05030306040e0a060501060810051206060103150308070f0615081504020d1401 68
    0x140010180d4120b2084980107561210300042e024050100b41d00b881017110404a5400700d02408807030303240c10911070b00c0241c810280a402400c580102c0200307400f58a4098403048981042c0800e240115010b407504a000d030341c503030011990085a4a40101005841e0740c0010700a010040c240700702a04a0300c6004510740380c20103800169075070278400c024040c20002400b0564a02083da0144000e2000506d691400c031140032920b0450320080003086031040090580074004c05c01c1e845440701c139090362105a618000c4004010719825038a014266420410200354036203044e50284030008224020388010b54001c0d2581070440b0b000360f0028010620340f40800404101840050014140c1100c203491303920b4041111582d103075401040c040c10b242c2e844040b032241c0650010080000c42d071128400790394503120b00c2e11890f074801c4004100c40150a10b004504075a008840140a80340d40d0001003004070810201c10010303800142059810072040d040c9200030070290224105003140790301c0040340e070241 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 869899172 1250 869897922 869897971
    0x61109030d080c071209052d01020a021305040203071a0a0806010c0819051b01061d060d0f060f0501030b091213141507150e03030c0301060815030105 66
    0x36246804204800748042008400880781540c02c4645c100c3c14100a8180c080d00944581070990844ea610050f8036031110074030f00321044042e0031b1310001c4407084407144403103005a9540e403000100a5000c0c040c1d100c011207403138090f0702042c1d105000a01711041280c0c0d420307041041640410341ca4644103c006400b000240c1c1140c60990002401c1c42c0a00f8019850344458501d40294190403026801c6085102050ba200b4410364596100c1c110420300c4042d80898800e0083c03000c0e1081d0103842c400380c81000891010714072280c1c400c640c050130350005a827071503981d0040c0119903001215007507651040c2d18040f1007280b01e082d001c1c42c80381048803824204042c03014688010380381c0c80d10115a00f00305100f003114044005d07900b210038405100422141c1200050000c111014030b06116282c041410020f2200048084003001c1102d802000702240c0110388503242e00c41107400700380d1400d00b000100042c503c15100c081d409542500166090045140085d0a5034000c0d05d403003540725520b81403480b8406 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 869900422 1250 869899172 869899183
    0xc120102070b04210203031501181503060e0603010b06040b0c070f0311130b010e040b01020a0501110325020c0d021201090804080c0901050a030201050a02100e010501060e040218060c010906110903 86
    0x804d18001141189040310341c075500400030344c42c100c2c10041c3e05002c055003069130341500409001e4074008001d582a96080c0100101030030b01c9101c40200314100031808505041c8110312698201400881c903150a10442035540e41c001d80d64044c0c02c2c03180400000e0901e182c801c1035005103105480b003d40c2040780701d04000200702d1400c09040e041d0703c0c01117440c00d141c0e0442c1e0544480d0b40281d4002c20701034406030050f0300306624400050140d50804680e0b80030701c1d00d448000c3d440760702440c6600800030b004506031811245d142c80722401507417006254030a01c5c41d2024040224500c000c0000e00103003207035240242920088c803421245038201040034030de9030740b09018040da0004180d401304000d40c982400140d0f40b2542d440040e05002c0c00003226034056101b40004542c0c220400400d000c4803015440701402072009100e0400060004182000f5510705802192007043d9440743d01000320400c003042107003650100403140e80e80d41d41d5496000c00200613018003003002c8007040c0e60b1615400d0030000d060504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 869901672 1250 869900422 869900483
    0x51512041209080c010c0b0603010b030a0803060a06020601061706060705010c09030203070b340b0403020c090c2a16030605190e0304030809030106030c0806070306170c120102070b04 80
    0x16007103100c0d802d1651b40d01c000c1032400d141e0800706c1c221182d11007801190040c99990340043c0c15020304405001440400d04c021805294165164010559904e004980705c040c00e015040020310305424140281c1403000760150010703802041580703000d405940d03260844032070042c480003041d1501d40030015850280a242c0007001c403191803900d80f10302c50440a10505d4049412480d18003804505042d2080c41084e0700751890b40006900c1c0141894107000c1e5507801284801403290700c1080014a83c500f103d0103661240c0b083c0c00d010703441e09940b540ca5080c18407003004a018a4442e010b4142c2c0801010740700900103502580b00040e25061042040b00c280252034401d840c1e59061061070740f04458008100c41c02c82c0d40044200e40c03a00082d2001a02401040d0b01c0078007000036014000c62544004030b01c0300d00514050b20f0802900344e46140200031020006401103036500074500e5600141400114440b155a80030001450003005903503502d0011010f807410703140004041c0307410000c01c9214031810030f00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 869902922 1250 869901672 869901689
    0x6181406090c1507050a1704090608030a080103060507020c030607120b0411070206180409060c0e010c030e01180911070302190c05120c0424060c0507051512041209 72
    0x507000060b0201d0801c600202102e24403400020303030303a07041c0301c000c1c0b00d80d5500e0fa502c204003181540d000582d401e17450b0841d005514640c0d00c0d169000802010000c200c50b028801a200e0a60a80c610f4840304e0042c00028801030640c02450011b0016a4040c805c10703200780c070243c4404017484000e0590710115903200125501803482d0030030004490803000261400c041d41110041d43d21508008003810318207400300030315000750074100001d0400580e038002440c05c1c8400d030fa0f4a808501f51500440c2c07401c1c1188406030219000e1301e0214119481410a00c60700040c0100d01c0840f644d42e030741d01c40100d8048900c2c2481d012400b0402804251f41840524010010800d108100e1101520b48400e58400c80c407900d4469030742030340c5c0d40c0c19440c010b010704402d6034002042040035028958402c1c0d071191205085a02d004a06074000c01c5e4280a00120b03509030b504500101421400e05040c025032031101e0b5980f0b80080002e10403442440c40348255188950f1150a550380c11a0034511b015010030311a8100f40c90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 869904172 1250 869902922 869902933
    0x21207090b0d0804030615080d02010b010f05030402130c03020c0f25061b170310061e080f060f030a0807060f110a0e19140a0509220618140609 63
    0x3c01e0581d82900d05403a00100c1c00110300051409084512420390700400c1c06018440384440c1c519019032003202d00c90000e0702c2e201d01440e03a00d5411103940c070040b03800030b521000c1540c80e0311000440f40d0215000600b5401c006140c903407201c0c10030f031400050015095580c4d010300c0c002070f021320001e1000d924083c0501901400a410400050703c10340d44a00214400c2440303840010a110110078801d40c0d101850202d55640e05026800030904c803030034005c101c08200314609521a204003442480d81a01c0b0342d580d007400b540c5684201c41c41c2004d006c1c00442d444546201800784981d803e0100d6900c1911601a16aa8400e50702d0840243c039980c11016401c02d21b08083c42809009980440d1009640351815100e0680580001000c0460401c05c50300c9a64502001107401540741d00c0507401d04100b01c0d40e50001c03e542e04204242420111010200010700d405105500304014000c10101480b40c100030442e1461225511081107032542c00b99100c030f095102030f08900b1014440b40c0d8200e036101e405004d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 869905422 1250 869904172 869904199
    0x3090209070311090a0618080f0a0f14070608041401090b04020907090e010801060503101b140c01051501030e070e06010c0c0f081e0601121707021207090b 68
    0x4840c0340c00108400c081c03685a000c2401c2900140003290f0100c00002c2201c0c80441c1c98000041c08280c030310308555224151000c02141603140010f156940307806c01c000500e4001c075a42e0325181102146541103480540ca40b00000307000c503090180e007000d0a4290390b400d8042c5440d00300852508a1110040302e1a4074000922001c54504208564070a8050b14914140d0b20b0340d40080f159441030794426800d001c0303161b00100e41400c064010b10b088600440482d00782240d4121070004a1304a40102e03182c01010100e12078805004940d4600c0007501500e0107814158101c0d507050944108031001c030031a1303041c50401c08466815204180070420044010980c00b0308025010130b20703200c0545900c2c140507242030f960082125031032250025004c0d45280410181c0d0f10017400d80c3c0e81d413500140300040000e1a80011f610400011581c2c12282940203c80c0b510040351100012081d0b0303d502e19151010800c019409600c540030b0b000031003c0c5950040c8541e5251031a0300003291224154503100c0c552410800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 869906672 1250 869905422 869905429
    0x206010e0f01031e0c06020d17010b04090b0a0b0c010b01030513030206010603021c090803040302010e03270f09040b040b0129090d12050a0206101d0402040617011a01030902 76
    0x242e0540741d0040000c0013441d04413044000c4820b502c40d006114001e00140800c240c2e034040341426000710140c65054412040c58104410190240180344036600c003840200f04030305194000c0f880c0c2c4e40d009492050559111455000039a000401403143c50703465a1908401d940e2611031160301010822500d80307500105d40d1f0080d1148818403400f410190007140714040300041003481d80c82130b907648e242009030100b98a0b040065400855007900075510301040c040a080002c0300311200b90b45038108448000c0b070562810215034030400d03031103500011201c014000540700c22800a00450048900003c2031415140082c5000c0058205000d0004a5107418549120aa40c2c40d0381000b92500c1003522002ca25001c501c02c80801e070000360001c40600000700308290084014645c1e604107909403042551035595910b020811489440403081610080d651060200071120780c0141c070042c4007044650361845000c20281c0b8410715800207945d070354811800c415117442511003500081c02c1c140400304198000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 869907922 1250 869906672 869906701
    0x11418031603030204080d020a11010e030703030f031b030f0b030c210c0603040f060501090b0901260303070216080d0c0b130609030801060e120d050a030e010603060b010206010e 78
    0x9103000c100850981c0c1c1014001d80544000d84510b200315050a100101c00039900c02d03403030f402a0740e100304000f001400d40d4807038805040f420300098000c002c81c030f29580e030464004101540b900101a035038413010703500c0e111441e803080e04103495540106141c1c200300c0d001000c84200f00d00031803080d4840030400819443c0e4008030881d9419901c0aa4518072801c1246401d103045403415079401031001040004010032845106801c50050344100983da803519030070030865130050b80f210b9014520100400c400d401c49001d0b03410203400500c0a603280541e0140042c50741e04281c0e104405a0800e121a9552840d0044800c0040a6030702c0148500441d2050140905180c020050203141015001441c00c40c01c800300e1103034107940315004001c05246401c00900000b0280543d04c00100380c401d000da050b260090600030207a0320440588400c805141045d240d586c050010310b802d041c0c50701020900440b0a1003200011800780c074002c03e016104000081c107250b016000312580400440c14440c6c2241200741 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 869909172 1250 869907922 869907937
    0x30201260a0f021e1e0a1e1106162d05070302120307120f14060613030c1502070f0f1503020d05091005070e13111b01141803 55
    0x4000401e1040c0c0c541d1200070744108134043d200b4440d001500d601404d0710300c00400700c081215050942c90030000b150084e441c03140c0c050b075000080e0b10300b1100148900d00c940c20042081c03035050042005500c40491030905a04940c50800c030711095003064061740d0000072482d4110000c6203400b0b0440000c60942d205e540341e0b018400c0c2000300c0404c8120400d0b000300118079001c25030b91119901e138a05140300624803100d181c420075249060450040506429024040302d22000c9400c0000380d9490b00f05101803a044000c508140f640050000000b01da8900901c1001d4180020b1600ea1100c001d03d004c0d00d03100203984019919055800e00f0400d04041e481d040045e0760b5914052030a0040000049005c1d000301c080070100c60340b5144c10300c01c1c042c9001a428962840ca45e034140401d969140040d2281e5400c11241b40d0022111500c1404021a85c1d1100e0f80300c0210a101e2170802108803040e840d61944c0c000038000c2d60399074410322240f064000c4000c69000d214151081c082c48014111030b40c40b03008912 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 869910422 1250 869909172 869909191
    0x405010e07121103031b010506150a080a051b0a1106010e010e0106050a120204090207060c2c0d1415060a0f03141f021806040e06060d1e0603020126 65
    0x81401c2c01554040c01100c11088440b4004805d01d040007002070700a04094410620134080d501800e40c8ae4810b21060740c0d4400c5050300c2e40c1d6141d5070b40c001001c0103400006c10490300c2000782c4180e41c01180c05003000e0540440c00b030341d038200c42000c904034080c42d140c03041c0c20908401c28058010000240306580003030645003940361140e141c020962059511602c884515a01c440c00800c0c0843c80d4008fe9015244482c0282c0042c440761b40c1c02d03502603c0d00d500c03042c0c0c1c241102000444050048002c041c41000146001c0e02420f42100c851302c402e04035421409000c40c1c1500101710b46201c00c2608502039800c09400c44001d0f04840c030b0032440140010f1544230040003000506100000071106100780e980101c2c0302d01c0081c0c00d02440c0d400e060001e500030741e582c1c4804001c0114410541c2407420030303039041d034206076103400b42525807104001094012558014800b51509040701040391840700004009040110120b102411071001610a17140c514040c05204040b101c0709405243c507100c02e682220f03807003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 869911672 1250 869910422 869910443
    0x50607020d03111501150f031a04150b030c0304050d050a0e0d030c050a0b012607050f0a03060f021305010206070c1115040e0f070212030a05071b06050405010e0712 72
    0x201e07500d04001d00300c40a004101130080001442e06010310354422502c1c800d0384d5205000d003200200f81e0807900744074011125120040035085480c1000da0040e01d294920101c010790440c0d07241d889403450f90040f00e0700700071034401000780401c1000410100c1c1260305c890800030b04100c81860700600101401258901c504021028081818016001006010780001c00d0358440c4844e410074409000c402e101e107007440005140c01c12445072048100490000000018041c4c0d18034020401198120329115198801b105242c00800100c00c0c0c841c04000304051280940c848901120200940c4010380c040b5055400040802040651280500e403c0301e80c07007620f05001d400140003080004c000c680d800350840360005000b00b45000020086482604903106545413a505c400b030490b20b58851500312524070000b0700200f03104408075080b69074400c096141c407440d0b5002503084402440e0903a10143c0c1c0b000d5441080c4001d1081c05e0007900c507070400c804020240c4511300000404072865204000c0d1011041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 869912922 1250 869911672 869911697
    0x1b05040812030a0e1c0801060c050303181203090106031214031801110a030e010507020a0309061b1a06040c031a0f0d0515090f1b270c070309050607020d03 68
    0x450748492120f025050417a43c420000c03041329500141e00640700c1001c29010000051b9080c8105120981d46502c00080c3d821512350419604400c06002411003d074050103072a02c6a040500e8003a51089102c00d001151881c69400d14481c500601d203a40f90402a01c503000741c6a40c1c0a030801c0700c0e0060512030804500001220320203004001d080809115203a00003209104560b041e007000e0b1040e041e10008000d50340324000c050380c0e0748c182482d0060100307120010800c03d15000300c0c03403409245841091015580019550007650040c0c0c0c0c100c400803124820305110590a00e40704610707544c881c0d03040810469107903424078030441e00d0f400c0446104010358420454513488201d03d00400580c0b100858a000d101e0049031040c41c40e044602201a108003806008400400a12140038111400b07040034000c20f41e0b000d01c01211205403004d0244502d515040e00c44803a01c904040c46020300b40306050b100c44291900812441e5164403562048100b4820080942d5841644080e4103916050001c1d40f0300c43e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 869914172 1250 869912922 869912941
    0x509010b22060305010c0c021305060d0b15061209010510030201020705100203091804290703050c130b0c07050406080606061b010501090609050903160b09030f0d1b0504081203 77
    0x40d43c00003030095090004031102c0c560001c51480d54544215110525601d120088108480c0300f107540d69400402202c80d80041010302546a410000404512032180f02c001c1c003180040d4080d1595103031340c0d0080c03000c0008845003841041d41010492500840040c03075600001d6560001c0d00455100307011b00300404c0f514500800c04c1340c0e260107002d009a400700401c1201c60306101402c803429108240c001200ca200070f00420303d401841e6002028000b546d072240001140142002000880d50910400c10480d001c001640140010680c4201190f652144410700604151103503200a000301d04280c01407040040104c4c02e260302901c280c82850710307403107014170345560030110001e1408203528150000c00c40c1100e83e040701054920b044810700c080c2d103880c6810f5a680c0704244071000c210510207506000030f0301c1c030074680741c000c2084011a400c0c01c1381803002e0f00843d8018840803100c0740d600c03040030004011181c9411852002c600b4061700b002d01d0446041c3e1151b82d40380d0020700a203800000100c040c1c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 869915422 1250 869914172 869914181
    0xc261005120a030315061409060714070317040e0a0c03090821060901050306070305060f041d0c0402070b070e0316090b0a0801020301050105040303110715080106030509010b22 77
    0x80082100e2403490090391440c0e100c000448060f00040d013402161481030f9003001c1400221038065903409052400d620700c1e0045908400301e000c2c0c1c04141045014042104a141e21040f80100400b40843c40c1c139503e04985c4000e005505d004015200b40400c12603001c1c460a0301d54003000c1200041040907403910214000c2a0300e00006140785400b01d8561400b90205098402081c080d104e840c4d4136072030742010081e02007801d22a00d40c0c1a480140010102031007a0401c0d40c0002c4040d214078520b50300c1034001030940f00416541c1c000320002348040c0d80d140d40c0801207501c05520a960851a008003601c8806507000014903060610440b182e20f40443c0c4c0b0f0412650060105104811513000d4844c00700d100035001c010602403041d00260340203e540354040c8200d0b41201c07030503103559280030b145079819114000484080442d5001d500400074a520340c1046802003e151a40e4100466050440140c210340d406800b0a8083e032505031070030b101ea210f240200820f61100741c103020803190001c10650182 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 869916672 1250 869915422 869915429
    0x7020d06060b0408061909150b131b0e04180b0915010f05041b05190c02090a1b020303040b0105010e03010e0d03020a0f0c052d060114040c2610 63
    0x80c2d000240014400c01d0101d03040b8013460180d828502210601030285054990010300642610141b055240d203500d01588012441d00c40945111504c6205600400482e070182e099400382c080e000c40d1001c02d55500c11070881e5a1081141e00300921725130881031025804241100805007655000421004401000041c513242c441541842d01581c4450500604514900c2042e0050341061100007a420070001801c01c43c0c01c0c103a1344d0a04025001d00da034071505100c5031810040c48007882c0d5010145c0c03100714030544900c40200c0c011401010301d08215010b94908110041150014418000017403001e075502d0381141c0b0300b4601585c2002c80040024010b15007006494054400d010f285150145c01da00074080240182d1926030700b8180700c030710684071a100041c00a1a54010700c0c203912041e074000001f00000d070b10603102c82d04a25480c00347c551400c0001e0300080d00c101c400303003010306d094500b5006a06c0044a94a44103800c451200301e00c2d415a60844d007080b00d088180c000080d091b101080009008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 869917922 1250 869916672 869916689
    0x3240d0506091c11120a0e030a0b070206060105181509040c020a0b060a080c1512040f060609020702060d0f0209030d051201060201020301300c03080306100806030307020d0606 77
    0x26080c82c1c19219507840341280d0600d056180020a68500c0f40240d1060040314403607005000d0080300b904400d5260780c4042662024031002108203000c1d611700300a56940e10344180c0c10b0554600388403c0191400744002c04040c1000030400400306004d186c0b02c000c0a0908081d501d803011328101e410501e03083d000b40005036400c00d11300f00c2190b004950000780d501d500c40c01001007000c0340d1902002e1101d004403030f01902c020b80d8040544c10000b4104039014610040e9041c43d0942007250121300d01c81d8015095905032800c11358461000c040c46000d20810000f07021401045203000002d60104006005194410030210ba44144c00286d42045070100c680c00c402c01000d591200e9168200680103130407001c030007081810840c001140707072030051080741d061704c3c481d04407054004041c0700d01d0000e11408035180c00002c68130b180100000340f0100f60500145104400d0951070b8a0040244156004003407074120401420900740121350320b01004036010150150748800b08031905040c00c00143c0351743d521014a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 869919172 1250 869917922 869917933
    0xd0b01031d1e030c0c190b0403080309010c0306030f0305090d02030709020d2301030f0503040e010b040305151009090507170a020907030e07180b03010509030a0306080303240d05 78
    0x41101002c2108000040326011035801d200000c2d031496600e003d044490300040d44401c4600d68a071802c001c5100605c42d404240c80181138803019455030725003150f441161030705408410310030204d00a005160044119140400004d840c5071128039078a015294007a050250003da1000a522580d82c5235110f01e4015084070070300e6aa4846030350096026603a0011044d04c0e207d59943e4002054007416101280010700d0000d503400d40c1c940601080302c94404480340c0c441000000ba80034001004075008140d00e0003459151455410041d06141800d0424000340c5020000c01c1391071000b40b8110000e0316820000000c000e4094a029464044030350040003420b5403c242c0510355401c001200380080c2e109a5407800b4036240c040c019401c0c2c03600300410301a29045201c0622404488a0710648018131207000031440c0a8034a000c03078212074094400c2c0046400010302010100c4d010b010b818010044200110725514200341001d90301080700d000154140707a43c002410b041d50381d40a01c0440140c20606584 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 869920422 1250 869919172 869919221
    0x412052505030c10090f08030903270a0501110d200118031e14160b040b1014010e19360506010203070f141203090709020f0d0b0103 58
    0x10350b65001001d01070100d200c0d40c900d0210403455070140c004c03900d900002c295031070112035072454883d0700000d115030400d10051001c40f001d1944c0e6101102c00850210a004030607803c90107100104e4910b401c0103041c40107100c0d5021240100148c509181451481e15003050112050070910b03000000704036010300d40c02d0010403030154010010012030b8a01c00d442d400b144002c1103003038205c610010070110001c120000c41d02900b40d010040204146104040b000144e10020382d1041d085403030036101600c1d02403007282013001d176810b01200340020b40170ba40c010000340c0400000003803001c0c1883d030800340560b1041c03000b0320a00c5e00250b1450054015000079401c001c00a0394651684034140d0f0600c5082ca01140450b5074041540c4a44e502907a410381c041d40c03a180517501c0d0400c0d00840414115999030400c00e01d04074180082c010300c03109010001255a40e803c140c900d0307e1400c0d01c0c6400251301c0d030344100720212102c11041d0882d803c040960902080f006030703880c0140c0080420b65401d20208035400c8484 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 869921672 1250 869920422 869920433
    0x20309040c0210060501031401140612040b0414030310060e0d0b070c03120204050109060e1302040b09011d09040b04030e062a01090b13020619030605100804120525 72
    0x262007001c3e07030410400603030b40d95000460640720a261910800c0301603d0041c8101c8030740c000c8403848981c0241c95185000302c140105003101900b21000d0340e203207403071000f030208102c0a00b05a126103c6485d00442c01c600b0260030307880c1100c686209090622018503006021602c8981c07040107100d4000102244c00e180c59240074100c005840d0040300000e02489003981d1801042c4240d50a441040c1d640c03403050f600f022015101c4071001501c1a5100ca1085c0060200d0741c2540000e00140c1155204980c03226403d00014000a40c00502101140440c0c804004251100440719034802e42290586005881d1414180e44501c052414160003550014804d07207a003e00c034280004840b40e69410184190101c0d540c0c81c22240c0300500140342c21300c0341011402da0900f201c5080c102d2400141000c1c90035082c0c907034019441c20400d13088130110303423103210400403842c09409000318089141041c64492405684912428284c502850107000f00440c1181080151a880c0b94891208185e1350042201c00e0914 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 869922922 1250 869921672 869921683
    0xa02041d0613030212071b0906050a081c03020a0c140c0a0b03070c0210030605031501050f06070f150605271b070b07030b190302150f030610020309040c02 68
    0x104050351040c80082250056501d0000c550b040d0142d001d80800305c03010011843ca54029101580c12100c0c203888007800c4d140f510003110041071032032000180580f801040c410380e200142e00010f1039802842c25019184a406c403008440030b0103140042c0e44000104041d200e091101d07001510240308440540041980010128011401142c00d601040e90700c010b14480d1b44822212940007800c0c8001400040c10406d40b1200150726a0a0105646807121301007894442080d109440c00744030744004012504000a0140c070400c1c040e5011441c00380607440c1c83c403012040850003040e003050852140c09003c110350180c405031100420303c41c600d40c0601280064400300039400c60f950600000440c0700e88c40c130b54005080d1002180421814668a600c8103102da48000b4896411316445002c0120159555070768407c41c0c0110f250a500c13518103500510007078540710116188203050400103094010301010a5a5001c082101c0b0340c456400c40110482c19401044070264009080a2a00b0307101138002c2003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 869924172 1250 869922922 869922971
    0x81b070503100c0f1107080d02071806120b040f060c020d0f020d02120c07170f070f12110f030313090b06070834140d0e061b0a0204 58
    0x102c403a14110114000b0860314619800404981e0032445180000d0054001181c80756101c01541c178155030300c1140790f041103461401000141c1000e2814412900d10700030202e5040d0b4252401c01c041800d1907045524010100d8010b4600c4500c0e50000d002c00049031010b820345980403005021403a9200c0b0007940d80e82c940940400400c1401c0c6c24138070160310024211141d81070f568020000c5c0e6846c941c981441d81d2010030b010348a801003000c081070b0040d0182d000071241003103600504413508003080407410007455030000124200c144504000e91040c034201c0d030060340d401100180c515000c280c00540303847c0300303181c40f0303034250001040110400d61414101001c90322940828800c0c4284841006468807a6010052103080c050003016020707043c0f44c0380c0b0413820400711407000e1034014820141d01c4e600d0440c0400c50b42c942100d4201e0010309018000c1c8038117102c03241840114490100002804c2d402501400e5100401804203a0401c203001c00420441d00e0f0081c008100040c0302c0c046502e5500003040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 869925422 1250 869924172 869924179
    0x80313030b330402070209070504030201022517030702090406062603031317041509050103020327030d0e0a290f0408072916090b07081b0705 62
    0x340014224801c0c400d0703810401c00054024410059000072480b814804448825001982402560016120008240d0007203100b5111551910714603c002440c0c0f40081c01c000c5e50072110818000002181c000c07140d03050740d200c0d860304a02841003090302c1d851802141c02c043c2d1710000300028802401825409601500e0310f1380c90505050458040d4000d0800c16241b060643c0c1e801000094072a8203200306080305244503e820070782c400c20b00039501207660030980003070000d0440e110108200d5034103d041c100040200382015410b41c5001b60308180e40f044824202d0131320190b64000440006401c2c1b0031580f124400d000300700080f6980141c0150b690240c204216103050b081c1c0c500c04039203070048031303c4a20f05009410b2002c2542d14034205100e200303809841258a0741040c010400040d1602412083c00310303911510070880c0d003452600680780000641001d075990514001c1d00501680440c005053f5040b40c403e00356078010350710f400c01c1d0610441d8131003040c61008041c40c25500c00046284402c0b110300f04d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 869926672 1250 869925422 869925443
    0x6020315040e0708030708180604030506060a090501082a03010e0a1e08031b070b040b040b160c240e06040b0a06151d03101d06012d08031303 62
    0x304030355910440b6004e1102658006d20001c00000d804c03a0040110000d14a04c1c007000c180080003260baa82c02c1600304581503000001000482d0920b90801002000394140922503549803500d455126401982100c000c00c100c60a1050503060782070074034904400240c001c1100c00281c4007025142d160059046440b0305082ca1080140310610011301003094101c2112451500c1d2209820040c240d40c00102003068014041c1d500408e60340014107210354001c05454585141c1032406001c2024000c04030307039280175801d9000351060741c0216594030040c0c0c0550803800e1102c16460a1907088000340700b40c1d002d98180295101a00720200340d0034001c0384a00c0400310070380c0325803100105a90b5a402030a1b001d140321041e011041f4030a560840000000b204c0d0b441314880342e8004203040c0b6182c000c0b090345840d15100e026004401884c00c0010b42c8180c50060507007541003101004010b10b0b00040c0c40000106400c0c1d00022810707a908001c0109950000c4035910f25481c02404c52800091000303840207141d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 869927922 1250 869926672 869926691
    0x1f15031419050c040506030c0703020a0c030f12080106080606090d050604060c020d020303072a02130203070207121511040902070b060109090b090406110705011406210601060f05070602031504 84
    0xb01c01070b40c0031744000411481c01c50750340c1c0c28202015085402e0a07021446024020004180b01c8004200510f015083d00d10480425003840309060030b810090404000d402c500401030315521456158000600700d48042d603130301d901000500c04054018015007140a5142400100102a40250504055070302551007904d0400420781e1a400200d6189010583c903540003c0b04480c00c0c021a01c1030f56104551070b40d0a0002e801040111484604210071158000144039040740c04012240051641820342000b03801c6941d45d000f802c86150158444054903000c10040031032a45041c2d501501205004544a41e43c07405e0060006005445a0340422513140d0045064102401403412200c4017400455440d200ca42d200b00040c02404140340090100348141d00000b1400e001320b20f0f0a40c840004000b00341080e1041051071422099064002c280521543c40b9030f8102040d25411141070341890104000031810035942841003074001495181700000304841506022060750301020141d40c104442c1c0300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 869929172 1250 869927922 869927941
    0x10e040b2d031506131404110109080307080706020a11030a03020a0e06030609160e0604060e1c051e0a06090f0b16050906030405070806010e010e1f1503141905 70
    0x4460145040110325002903850b06207402500c0001711568800218070020f18285054a10140c40c00c40311110020000900341d86e11640e01c070050700c140800380d4502042b03560380984a20070b042d001080c241d008145581d100d030198240040154140003560342d6002e6802b8020001d40c00300c5e000c0c0700803c1d13a80d42e032011103040640581e44100000b8003c04030320345825a01c000004d03c010220410440c055264400b0380e100c0b40d0150000708000d40310400e10201c040100044280e5031100c03017103003032006161310004c00e00000303010304024a6240028110904e0401c410308001e544a400b514460030b00c2440c00c10440b0b0380f0400014140035a05c1101142c9403144580c40c10b24090140d41c00049044c00300c0e4030140b414000031074000e8401c1d403c4511142c2d03500c61540c2080f1003640610403044083c0c1c010041504003440d00c96100410340c4242848045080034120188850f02484000c41050b500420070f040c0039502514600c0403400d0740c0200b510303026011070003c001d1034001e000401c0c2000017040300b014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 869930422 1250 869929172 869929183
    0x70618090b0f0d11060a020f19050a02130f050112021011100b0604090905010c0f0207030209011a13080d0e0d1101050915280804050c010e040b2d03 65
    0xc0010407504040c10540b040120990b0f0b000c505940c503610a44007100e1907a5600018805a60281c0241c1a50b9004440c4c250402240000305401d11055902a40005030041080d007000d503070440d4020742000030180103c0c02018502c00900c0e54901c0c200011840020544800000a02c02c80b8078030802c2103128001c0302d201140e80f8412440b50f000c1d981c0d80b449888103401400c1103038030140c40c0e6030505540701404030a23140f111006a4041e50750b6900148000e62062205501c2c07000c0b800100707100d40c910340c007290070301105100f0749981c903a07a00030360008a0391007011146495207005103007003400c0e1144030701d91300c0c0c00d0362005040100c0c0c217403001e2920b203003442e07602c1f44d42c0071b60040070000b00b202c0014019035040e4000c6001e0b55004420390011149540c6001c0900307803034408114403603425014005003000c02d08001e0440d5050100d000c0c20800005c10004000c0c1d403402003840c0041c14080c06001050190440d81d42440e48602034100e03c14070329200e0b03540701c3c2d003540d08090300c428014181400c0c1070301da1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 869931672 1250 869930422 869930441
    0xc09090623060d230a0b1008010e0703060b0c07260304141f0207030506100305061b04360905070306024006020d0f0309080c07061809 59
    0x1558428030800614000b0040d0a11841516001c0343d031210a00c00d100c59400318400000744408808148050296180b08011040c4000c0d01d8095031440b40f010003410840052065a0949510300005004a8420f400482c01050700c90f048645a00110b4403d584604150040030010502c4285280f0b020381911208020200d4140185103000e00340a51141c40c0c205038140c1d250821085003c08d00c004048000841000800d0b9002d01016070a615180d814a240a00341c070240d8200c0c05024408070b000899429001041078249009061802c0d43c0e580c4c190107950f100100c82c07800d407002d4030140800c110200400841d00c5820305280e64103c503201c0111440c145002d851a4811030041c000148140d000b80540900800c01c868107140445d0583e0303991b551040c00802d182040521082085030010003040a0a09800542900010400c0c0108190100070205040545400c610310074022a0b508480c980024401a01d5840b9110722001c0c10f90303900e02042a0540501c11000554100c5c0c511500300724 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 869932922 1250 869931672 869931719
    0x405010b160c0b0415081f060f0c060e1b032e060b0a0c03030b01020d0f050d091a100b13060e0609040528060f0501031e0c090906 57
    0x2800c00344a080802690103000c00c581c0030104002c0800d4001e481400360004216182d034504102840050041082d0380242c500c0c100002d06070010349000c81311003001411740b000b500c2c280c4c8003500c01c0941213852045055000e44551b2404003044201d4401050f18540401c3c214150141f12081c0d6040c1545c5d00043c900c80c000e41152018201880c00301c45051805030383c2c00309004600d1940b20640d00c5a254856401c190110750304002910401d6014003640004440900242c22541c041110262040300e8102200f0100b040c0051a00c245840c55840742c0295600044494100c034140201c0601104060744e03031000200c1b00300000204168020210b17054070b40720a00c0c8807055441e14038240c480440310006c00342c1c0306a0078040c840042e142d622485100ea400c0c020001c0c0078031030440b0003003101c02c0b050300141c1c0500d003012810302c040311000245070b085030804e180004074002c10740f208100340c1c030010880d02c80c05401c1416280e078060348900d00743d00f520703010b000420581b5654040f0f00303c6c584082c0562680c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 869934172 1250 869932922 869932927
    0x19020a0b010e070c06060603020d060b130b0c010e0303011403061b1c06080a03020a020a050402040f0b0304020d0209090606190513090804081f0b03010203040503030f06030c060c0a060b0405010b 85
    0x150b03600105029003003039440c20300400800c0d00390788000035074040d50006000603501203070042c7d00045500660005022100c1c03c0e521f0040000c580748031000160040011000001424058130341c0300350f100640d846141d81c150380e1203503150032038034000880c1100c480340300340304140100e80c59203500108003c08009454041b0702d00a001015040324001814265140303e94401000500c54400e105150010388a0b03805040b0041d00d5104000b80c40c0c040e178000c540218811b00080c03004041c418908802d592000651130b0301c907615840041e03002410040000d400990801c24000340000000d0414014241180c0042948991903880c20400701d4031310810364010981108041d130f104a6038800c4079803e018150342c40c90540c44041c0b55292a040d4450f446886c500c58103c448815024441c01040050171802907185041c07035219641e0300c0c080900822110360700c0001084c2181c0d8100080c00d5a010003501f4292aa0712003034885450340701c864010340303000741400004821458a4803230203068541d07196a050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 869935422 1250 869934172 869934179
    0x605040e030f16050c0907020309010f0e010c06020904020f040e040b0928230c0f090f060918011d10050c040923132604031101051b0319020a0b01 64
    0x1000f1001c54105071010f006000c2000190340ba501d464030311600b0650000c40c0c0d107282c18000101365018180340c0804024660b0012141e0f60303440506c4600d001d03080813000d0b84511010b40001c000744140c0d070032080d11540c001800680d13585811100c9204d280204544182d0b80d5507600019101e00910b640c0c8030040b9000000300c105002e10301040d070300c018000c12007500d448404044001e26009401078080e07040d44010440c841c05c1c948000d0410326840d09860020060070402120b031a0410080c02c0140f085032041300203441808045810000d0801c480004d10204118030198100b0450200b41490302d80200c144445440c4041d010b91030150303070081191450a403421179060000c014a0303080b10941001ca200041155140c0c060340e03806004102440c80c13540c44e0034034048000303015410010903c844c04d00c0a196401201900b0b650440350400c0d0038030314112425004890a200c0c981d00c555250886192160000c0d000002034001c50100c3c402858a842500c9800c1c0c2c2d03a00c02101004040d03040c0f02c0011b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 869936672 1250 869935422 869935447
    0x170309030d0c020c09010e010f17060a18080d0c120e0601050906040207050a290907050f01210e2811030f0d02060a0c0e0609101803060605040e030f 65
    0x42d2180c0e01841529040000704d800550740e00d030281c4c060b0b04102c00c071400601640f1031180e440c138010040c0895070705084241d40065502e172040201601c10007a5540361050065400f14214102e16074400903840c3c0d07444101f07581c1002080e1003015000044d0b0242c840c098044a248121705103e032104000388896880c1c80100070030020000d08080d082602404558006541040514500c5115101001c04110341c012844121581001c4011844900d6410712407003880100e48101030b180d0564201d104040b8041c0181c4110540030510081100200769411110b1010340c411040d518400b003c0d2500b40c400380324070030600e642405403d005000c00c80d90300c0c1c00149002841a182401c040d05441400c0480c0d00c00354103080000a81e00d0150300030390100849031040303106111840c2404d0510505407071041d0003096180c0505803c1e01d0080540207a00010b0714010344202d41c1107070710f030885c5a940f25102d203421400740c205441100c2c0110f080500c1801c22000100644001964035942c0b24140041c50300704 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 869937922 1250 869936672 869936681
    0x108040b070513030c03050607030b0108011a04181a0906010906050d110403050f25060522180506030106030b060925080601110c01050406200d0804170309030d 70
    0x50410b2080070081e403e08440040d02a0000310b001c0d10805246030701d18206981880b400800e80010903143c9402640c60781c3e0020180f80c1035455040100a12482140f600100c9110350780200700109106451107030014201d41100140d1407104207800b11481c18603050148800064801d9408a82854028001c06203c5c501400c800b2041d803202003010113004107170003020f40c459002524144c11500384102401320400c100c105100403a40700c2d804400302c0341d010182c000e405001d0741e410070000041c0c16009031382c8582c2100d24000c4203036945040b1565010b0340749801d415840c2c0180d04500b0030700002c4407454184554403c40350003c003610029034820081004400c0010308401d01011403040340c000414a00100d90144aa96107a40b042d03400c000002402000141c829810980d1043d040c2a001d03981c002c0a55040300e4040c104200c2089007a50442850849103054107074a00c1400c1400d41075903489500c00340500d0242d090320100c01c7c00c6900700c02c403500c01184c189880c2d40c4100007801c024000c6501 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 869939172 1250 869937922 869937931
    0xc091512010f150303091a04050d0201032d060b1312021507060501051804021005131e06140301030309030318090e010b0103050c070507030f1e05061f050108040b 71
    0x182ca80546800c40b4122402c055082c0941c0c201d00a040c0100341c0c00000c80e4000d03100729480c0c1d90011022003001c0020b4440c0303000d07040c000d00e40c2c080003500b1a40a0307040f0301d180354100c00d5201140c004c5120310305001d40540c1180032449085c00300004910203134404451a043c80c400540d15110704002c00c4c00c0104c2d0b480d9070100e800c401007000c982e00c0c80b4103200150200c0d500c19072000c5010351410041006981c00152407207441c0100405200040c3d580d031901e1f161283c69070502e240c8400403008001d800b080c05601255400215100b010458803007028880240c907101d0701c508055281000c2c0c4001d50b0b0000740401000300c0d82c680010300100c0c0c00350441030594448008580e01803500c4943c3e50307094641d00140040303580e44689942002d907030580545580b0080300b0001c281040116107502d82c3d101c0c86403001501700c0450b08491001d000200d1642140308515404034440d07481c091808540e1460b04a8100480505031050151512040a881c2d411100e05a42310171085d1515260b0329440c110241 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 869940422 1250 869939172 869939209
    0x30f160903032a1709040c0503091902030c150d0507030603020109170309040221060108150f1c050703061107020607082802010204080c09091f1404140c0915 69
    0x407081000030524940400b0b0080303050b01468603085c4090030b00058590170101b4000744102407041110304803001a121309070102400f00c221071800b031400400d040400d1a1681e50b002085000c00c0c0b1310703c1506c0c100500150000700001c00007540d54000c114203c039401d00001b8009003100d1020044202d160551010009602064038134085003a000182203901c10b4403001800d09050004c42c98000300c5c0c50205da8040002e0812006c1e80c83e100319010300e0140f5100455100341e01000d1314044c2511100340c402c40001c000140524800c0d03d81c106140c0e10b0080744401c07100507007031240c0c010950168000341c981c0310303502800721824015680d9500402d0b03000329800c0744400d5203524038501014525448000e045195030001681d0f2070610082504060440c101c00380500081402c0c08892070b000269a1050000a5041c03a080c01c2940c002c6c00107045581f003941c403c60800024403041c012095442e510660050013282c001d01801400d0080050003110040054030200807440d04a040005042c0c17a00590a07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 869941672 1250 869940422 869940497
    0xf180b041703210a0f1406031b01080126061f080c0609010302030915010306020c011404050a2405010308030f011508041202070f03080d050106180920030f16090303 72
    0x743c154104403600740e401b082c404102001804403034182808410040c4400c074540c0302c00c04000000281820206208400750200c1d00076100d0000c074074025000002d18919420f81e140d50508940b1250001d519485090300d2805002d400500164001502d080409001d0706050030460039000540017500010a918680d0165002040046642c8000356020754810040141c0301c52941e41130500b120f0342d50000c1440001042d05000204800141841030f0b1507000d032800210400e0001c0049001110080b2241d9041c100341c00401000000700c0a50721861040d229403d45030390340c41c901c402075480d614101021422103004540410b80342c006c1c0d2200d809540c0101c844c415524060344a121400d60b02c180c40c0a0320108a05c822003805016542c014007a518144100c08141284000314200c54031a00210700d0399000760030008145112040880103c1e0b42d2001e40303d01d0000c00181c003a81c4100c030751040200800c03400e401201c0c002c2e00c0103820b0b40c0c3c05680391404900c1c8032601150783d04116014540c11000d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 869942922 1250 869941672 869941691
    0x2040605060703030c0e0409170a05090307090b090c030408190e150304020f0f030d120b1216051f080c090a0324090809010f180b041703210a 62
    0x80000602c58180b003944c00181541e200c01c0001d00c00321242c00214800c1e41411030040c0441c0c80ca1046140c2052444d42a41d5100f00281c01602c462040a540c10f82500034001c00242c01600f82c3d00c681d941800c291440412a92080c05181075444111402040c0303c009000e001c16160226440c00e40032091414a07100300b2201c40c00081c0c0030310709040b1401d11407100108100c2113062102140c002c001c02604c0315401d1000c2c0100103902c4040210035081040700d0300a00000e80303c081e40000d040f42c1009040d4034503000a04406603200c48156015014010402c600000c060a1010030102c90703104000c1d601c9902e100300c682c2154030031009030008032111b03018402c141c3e86544250100c401036103e40780003414000d400e01c4107584002d549029105070761a0140700030124116404485150300f00b440e0284003d640648190b400b11441c5030014460042c6e58004110049960020015500110080c1c298000245401eaa50348500c0310481904122007020206403900c2c3c00105412041090010400c0c205 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 869944172 1250 869942922 869942929
    0x6050a1e030b03031b010f0504050309090907030c030b09160503190822170c0105070210110d030e0f0102090618130f05220b0c0a0302220915180902040605 68
    0x10900c40800d00e409034170140042c45009100d52100500c903040180036030314064a0b00741d04c9002e02c82440f07019012340c01c0003545143c3c003401084065907025003580c0d01e0b00e0b16418100c2111380c04403006c0c4405d104100d21080f50110484051045800086c002c12844600f110042501d0f51840c1d0b04803819401482003c4140040c103e2036070081052102c500e83c000d140401442c11400d00d103160310116007180d004e80e409030360321008480c003507501501c54207041208030400311083e03122040c401070a401480030360024194190804941000c41500300c0d45015a904803290807072040c0890035078018420803a07007481c0782c50001b40491040d4001d001440700c0001c2e00340301d8140c80030b0700f5880198650b0307030342041615045080713610307841d00900010390070885090303075400c081080241c00482c4002020a43c0c40e00640309404507007000c2c1d0504e00352514007080d6500c0c05445003c50240031400790400c802000d0300840000741004441101100344d10780000b080c070b110300034100c03540e090341c0103a101d21001ca034584 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 869945422 1250 869944172 869944177
    0xc0c090103060c0f0c080f091513140f0901090b19031101200307150b10090312031103012d1d0f0108030f1c1b0906050a1e030b0303 58
    0x6019590205104400340e000801d0340c44080c0761300051110a4011300d0200302c1420580d54180303880384446541b00a2900040c040501900c1080c0d00310800040c00406800c400c9171481c110381100e02c603003900304c40c04000c0160240e100b0406540114410004121816664210110001001e0700b030344034400705450718680c01912500155100f41707090b10082c81d2035901010701200307010082801c0468107001c50003641ca0b8455101c000c0d24a10311403e80c8003c401d041d0740421a00c4074010a06001c600d0150009030007800c1da4030003660b859204005d0b424159000c2d01403c42d040e40210403061031030b828100d0103905041a200c0483d202d6a08098850096805003150b07000340c20070385085180340503000302c4002030410081603180500d01200c010084800004199841c02c4a0302d1105a1102c0144d40300001c0b20fa100b40d050300c05203041c0403250060008460034444603911650b40c4030403050700d45070282d803603229880e880d00c0020646401011107020f00c1010860390b20700d500d40816000440c1000038610f4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 869946672 1250 869945422 869945429
    0x20a03050d0513080328170901151d06150c0102030a020423010210020d0b030a060b01021b0901062619061e0b22230409170c0c0901 58
    0x980009100c1c0090001040c200e801410f420008524101000b030600c0313501341001701800441e031b41000b0700c0d0740007a00a000500045898102c0c0b044140f4203c500c3c80e01074130004840001803d035582021920850300e0901c0101103010112010141e02c81c1028403e1000d00165036551500c404e1084030050402030005500500300701c00050b8032141004801264020100c654810b0b40d02800700c0002c141e43c02088865070f00e1503003000103071280c41241c0070602401e6062543c3d9803600a4030380c10420000183d005040c080800e03070850f5000360449090303090b50f504081296522003461001001028802c0001103071501d40303070340c400e80071103042145411100c80540d00209001d40484260000340c41c14842c1c40300038040034918000700c01c80360101c00e1000b80903000340c40c10200001400c660b011944614918038003d174048040645946017905c80c50310300360283d024002d129148aaa4440c035050080300a4507810610141c440e5401036580300c0170317500410000500340983c10b44440b10f6130752185000c1c000d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 869947922 1250 869946672 869946677
    0x180e0613050702010b010e030a031403070e04020408070312091404050a0e030304031e170c0306041e02070c0b070b06010c03030615050c070e0f011202010210021803060c0c0a0807020a03050d 83
    0xb05c000001c005080342d955981364074000d0b8000c6007014003086d4000b086160340e612440019940ba241e54608561440c6078030f90f9260007600005d4001130301d002c0003402c141141e001e070010300d0081410141c00c40f845031a5200d05c0d40d5401ca40034002e0454541540815005a06100300151420130851440d0458100f19000d40221380302000c0c68124240000c48a8904c07049807900d1004001090007100d8400b20140c00502c4004010002500030b40b219440303030b9500030703420511428a01d280d58900b0060350005804403180181c0c0040090032003580b6041d1070359107a01c54000d190541e201d60044445c0318040703030140c04141d00d50034002020525003c044585030803d59075965034034201c2224603c0e0440b5507101000040c1090200062049000c04c198191084483c3c1c2c8200d2060342e0004030701d030000000c1c411008a20008018104144601c4030501c0e107501581590980d555441d5148043d00400b078407401190080c4d0303070590020b86918010300e0404d200500d035510207074032030b10340c0c5191001c909001c801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 869949172 1250 869947922 869947931
    0xe0f01030201050a03051f09090b0105041b08131403180607022206050603010f05040b030c0f1201020c0601090204051806030d0e06161a0f1e0403020f0a0606090606180e061305070201 80
    0x12b000b401c0c042180900000e403003d101c800703800e00c1d00007130140f68a1014410002a000400d2005001908042c401608070703480c02c5c14401448a842d450354840b00d070307143c903180490441e80b0b9681401d100303554960703030014022901754858102c0304001510030a84030703034010ba60b11001704041da01e190245020341a507143c0300c80e1680c104014031080b40c4c91443c4030b034032139406602c506c00c0175603441200d01d28801c810b45000c4001c1c0003c60702540a80a00d1011000d94002d400000c1404512507001c0c1048442c01c03201c0c0d446004019501040003442036400503016000034984503495409440c11085e0400c014100310300c0c04100580d1002441d80b000800c0380c0b5544003201c0c0315060f5140450568000f1107000503c0a10306000c02984420715070b00205880a0f0b003640005814103000307205c0c20059912110a6440c2a13540b880d2420081c0300e24012000c0c40c0c0c0c41d00001040079842268490b60b52004070400d8040309003410b465814101000300215405058503290703a004c030f60140655802801d09800101e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 869950422 1250 869949172 869949191
    0x60e01020d06050d0c06232244150a140702030702090c27091f1404150b0c0d0507020d0b2505040e0f01030201050a03051f09 55
    0x20b42c2d40ca0b920080c80703555110503200100f074034500c01d6000c60344036052282c11203c22010141407a000303080b4500b03030040b0101c1d028440c181c00e00f00e610440d260094240d81c40f1a15074540c0362204503d844201d4141000445070900525522600c41d40d26400c02e810002c2c4c0105005118a0030300001d82030300c806d282c010140000d00c14203005601100d4a6a4000d501c24175040b84000e50f28003984202a01c00d2154002041d682882401213034644100d840001c21060a603141d482800003e080c90107004910b504005540250382185012600d40804011100c140c90035101528450030300d0b002d05d500640d6145603090852010702407000400107000c1c29920b50403400040c5050208001c00d500c1400b108020039001039582000c1590340c203502c20301c122030b1b64513a814002e20001d0741c901c95254000100305001c2080e07070400043c0c021522528219403596403500c0d000700f5044028031000340416410b2001c40e000602a070012a4032500d281c8442c8100c07a2060440b00c280340c1d00e54802d03d0301c80e60b18511030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 869951672 1250 869950422 869950447
    0x6061e041e1503030c0f170711031006080c090612061614030c3916050409111002030f070809040b0904241103070f1e050a08070c060e0102 61
    0x400c2e12040704914108110b01e10345016007928051a0010209108200d00c441080406007800402040c03145031a611002580340440320486558201e82c401c0c0f1480d002c682c00b80c4007c2c0100c4054518420161002401103010b0004045c0003500d8541e000340d44a02d83d544a5030304200c598410201003000c00762103280d007074002e40200c4c64415454800c1c00100100100840039808a604a920042241d9840d2401c02e039803250071070660115148020085d000c82c94a4000000c441e0b07a268040345142c80e449564504000403501d55079801071050440b004003000da4135104841540c5450a401030f0380c5070100c9000c070a04540c1c8040021500541e01103220400d9013041e10808100e1501500c5101c840d0410340c441e40c1082085821000801c0320031000320402c201d01c1d40012a140700c880d6812510303828103480281892504a0026000a00d518101002009d580c2c0712003003400741d1600c55a2a01c08050000c0310342d0304000740400c3c07d0100c00440003001600c40c3c440c0c08074101003240010380710340b041d0412 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 869952922 1250 869951672 869951681
    0x180602070c0303080f070e090a09050a111207080d030b010c0c06022424030705040501090f050c122208030a06150201060605180f0909100b090906061e041e 68
    0x411940e00303131707180802c01055009240c2c2440c85404503209106540c800049901504250754024024000d02c0600000c1003000c0b070f81506155812174685201c02d0303241c0340d0300da070b503845500c200c005541c000300a42050300d019a00c4080800d8040c5040c00c2403469544620610008640c071400c0140e100715a0101c551242001c19070185a0b40c0f0891709103400d00d01e003104e02907000e0000c405008010b492070546207940400004009100141091081c2e40c0c0d03440303410005010b1141c5016095080200040503c20a402100e9034580300318454041ca46424000c030341504010500c03030501e030018007070000105210f00041e40c03203031048a0012840c1030030612100044246855401c0540e818004103000054010050b110702e00200d80302000d542890b44005500da05000043e680c1107250281031206200c80442d038120400f00a40003481042480c00c107008a60701d003181c00c00600d401c0907000c2011071810b040078050b40392850000c260000e1404000070200d44040c05c2c408100c91240c0f44a08094a0a000d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 869954172 1250 869952922 869952931
    0x91503160f0c02031b0105040914090f0307150f0902090103060b040e0106061704053c030306061204020d060515091008030703180b0708090319020a09180602070c030308 74
    0x186080e071061150f02084d03075003440301300340c6031080c0007008144103d0b48607038151001003600a0703040c0500d400039070311400454411740c0d03c81000e005191a004003a0000002ca03604180c0c00b0460700c505408691064008120071050142020340725120740015075503c1c05264040e60084100003102a0800100012a405d111a011450f41010400c00c68242c000406414040d200c4a120b12559950302d032060504103060071a1250f0801c0c440340c00050b010ba288200615508042e0102d4455224074500c0d9890004454107a03101c1c00c1002200a44030b40e0f44600c40e0014400b41400d540843d117640c0e48000d5410441700342038803030304000440002d803030042e52268000042150001049003401103641e224800e01d02d01401b031103545080003100c0203003c8003c3c5c0c002d090344248980c4840446ca08410f0503408054840c0c800c2c416004468900d25040800c585416401400080709034a03110b26a8080c081c41e40015070003c0f061281400814464001400014420741040d1206402d5140c007400d21070003e403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 869955422 1250 869954172 869954177
    0x32f0f0703090503101e05011503151a0910050c03070201110109200301061d06040b0109170706030b09060f130b0a0b0706060602391801060806040c05030a02091503160f 74
    0x40100100c0c0c4654503003401400e111b19022030408124403080e2f01140c4254442121192a80c4e1901c04115404d030240c40c58400031140001d00c0090501c04442a00503603100d44101d810810030400190300075403100c07042490600010070f09003050313260b032039804c46900034280aa00c190594000c0303e260a20032300c0c001d0309181686410902c1e00d0351140303000e110010310141c060355481d0440509a03009004800007840851740740c1c004040400000c58460425112720004a4200807000f440752034601c941c00d1103043c024240c042c80c071260408005d5100541c007110201c81c0e5658010017810748510100c140900982c42c8080c1d9190070b07514208041321717840e9008408540109001b180c40050384c2d10410f860b80d171000d8000400781d59403095800300a05403030089a1010080c0400c07441041d60300c003620704a4481d0b844560107940c0d03400610084d41c245885040024004000003901039003e940540403062010708600c06000307255030720240e164800e076041a0f4007201251805800c0d0781c018000d410030000761 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 869956672 1250 869955422 869955431
    0xb1b12040806060d06140705090102060a1a130209040c020a050c091e0601091214120901020a2a0f18060b03070509130c032f0f0703090503101e 63
    0x4075609031240c001030072140c42002849512014015190002d4000c1d246581508000b418080c00c043c1084c0e10605035680540545800a050782d0300c01e2186400094107401a2081400200708104424041018803008642e09100b96a43d03600c2d18812858228803a030000c21080c10309061551070b0115540503140b04a001e031702041b803100008600b0a04002031030000b00750f151202001600d2610f4290444501c10300803014180c24460700d030f00c100c1d801280b401c0940f11100c280c81d0340510700e4464101407d000d40e1000034a480014400d0200f04401c00c035145010610000345d103c01013102d001580320f80302d000501c0c1e1040c00095194150a12a62003a100801a10b40f03008000c0405020041036241402408110040c69854201c1c03591a03c0f440e014080050000d4070102400401c6180c1c0c2c6800880c1680c401c00a6035407542d1152000d0640902840b420480143c10312070306075100c80b50403810440ca280c00007441c4d440400c2a068000300c0180c4c08140c4080020005641540942d01024020300300b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 869957922 1250 869956672 869956679
    0x905010605040b0d090204050c0322120f030b0d0803090610030f02010c0302030d0e0f0d0e031e07080303070e091302010c0b280f1103100e07090b1b1204 67
    0x3008035803c441e0203090309502d501c000d035030b04001408411000b9420174101f604016040750351100551150603185200b106144004401001c020100030006108000310080705003460701512000e000c1d1842d504d004181a164040401c4134030043c020101ca8040b03020081c00319000003440080d0307000300165500d00103140366803114040b0910761a400703410311030401203400501d44244229900c540c3c00070390912581c0d0032111100d41c0d51101c2491400c05004a40c8142e4030342e4403a00c01300c0000c0d40010010114101d581043e01501501002c240d121840780f61000201c0f00720030f10142d44903a0310b603240d00d100b050421703013400500500140b51a00d411035032001c480050386c01160111100b90400380060560fa110003845241e0750071084150602e0852094101e40450380e070704810140d443e044800d01000c80240da003008940800d941184101c041c81c902400003602a0300c070f1a902200b140303001c4801d6607481c050000940c5c030000b0f40560b0754240011001c108030007005000d0350440b04040c1d80780391514 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 869959172 1250 869957922 869957927
    0x615270627040210050f16110103020406050306060c0a170901031a09242115090a0602070f02041a0a0e010605040b0c010f020a090608060d0b280e0a020a09050106 71
    0x1c0c0001c0c444c403280409481074500c05d8003a5000032514204c0150342d0b48a00c0d00c0e0040c112038005048425044a200c0c041c50755120380241c43c01c5507055101c079801c5031200400c200c2c0750b801410800003684180b02d1024041204040d40000300607113402c20640c1c40c0b420100040070383e0303035600540d40940c0e204107080001c2c2d01c0e8010880c0d44900032060700301c44400040e0300c020601c859210040d0740070114a500b81c1e890014004102e0480070703000112a508640814202008481141c2c040d116400082221000c101c19030014840148100056103031a031050340040c084507540710f00060304503c035400e8607850703090040e0008064940046116200c0d2b150900041c0148a103004480d0600004500501b01600c250012040c040f80ca070419074403440b5184000f089000148259400034034801b010804a080801c0c034464040d402c05840c040940e1841d518101c003403242102c250340341019045410290340a40b003804030101c810b102901700f4444500402210074299040b924165290070010000c082c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 869960422 1250 869959172 869959249
    0x1e02060702011115010807140a080a14010902090a02181e04110403050114250203071101050d0509071a04050a0515040f080c011e0206152706 62
    0x941c2468445519108071140500f4008005a1140002688000451203560201e8a0015a04541035954420a01008000552880c0e110311707452500310b81640701c081002e6200d0029039090580001c920140316178042290f060080b40c0f40c010702903007c13400301c2e0301900108641b0341c0900301b00c4a001120344a07070048020360810700c00442c403556131480c1211002d10007406480c000d5070003200802ca402d1070b0300501c0340c85034003c82d205004450f000c034999180885003445110008070315402981451015682d01071043e1888403054140700c1c0c01c2c80601c00300142d900959115000c0e000280054901e0080150140640790003034540c0010140414881d0f03455a0100c07000300c0d90112500d031040840d240f00101e50f0710880d00554100060010041072070071340003400ca4aa082c080c2e88850b0300606524000008060030780e00f0a0041c0c01403004940c2d10705001081c040070000040001c2058510b219401024149c0c076880401c43c013030a01c0400085281c0b03a0203a507042c001e840c00004c02000c41460014210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 869961672 1250 869960422 869960437
    0x50f2805070201121d061306050105030613110d02060a0906080601030902241603020106031b0b0307030b0102030f0703020106031104020901021011090a06080f09010b0d03030218100c1e0206 83
    0x213a03583e040b00c043c508007221100d02007000b003005442d0203090207020011904c000032030940c4c10070b0404000103840e0500150300e9215880780040e610200c4020750f50700316610903c02d075083d032001040c8524005030b580d81c0028270141d403e680302c0b4261030785800e001610041004207001e061520740180103026841d902d130b084001c005c2400c40402140c03914500108140240d0205094400e0001d90841c1016015884001030b00d0240c0d400040e83c4650700c0000c40e00300003074010809418414408640c0303040c00ba4121075400e5105006983c05d0117084240244603401c001e4054006079185c100c1001401017019814001c01015102035241c81074010001c0d503100100b07001c0e0307001e0527510403050780700b02440000e55040ba200281b5086003240c1d98000146064010348100a800c0340c9880841c1007820141302d4208a00d0015204000600700303510150029000010a171000e040140300075607441c1d645400725174001d030b1251202e48803c0c9017030501180100807035040149400801400c40c015079205015500c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 869962922 1250 869961672 869961707
    0x10218090c1303080307171608060a0902031513020702181015050d050f0403360915060f050d05130f03020102031602150105060a050f2805070201 64
    0x103a10341009076800e501c82e0364a000881c0280100200030018000000d5021b400c059a480074035450086120718040d400b521074003600069464501070701406a51060751103440201011038656443e04814203aa10481d80b149091030422452852382c40d1881d14843c04425010301103041000d9030b4080340c400b10b003401010a034917114000060744080c90040b0080030b003100c2420454141300c070060190140e04914241100e05080034009030001c0e02c80702001d84141c1d05580c40820211541181c5c10141901c075040400041415072192000740010b00d00c14020b00c070280d4001100703000d000a5004c020b13480c1d0404070821900e008649042c0d0f900c8026a05400b0200c440003840380ca880c0100e074a581300c018001800017410411000c14150107501a61050044840e00c210003c031440c012601c0343c1101031a07508001d050001445242040c50241000302c0e400d0401c0d610705a03110840b1450b81c1c0200f4a00a034020103140c0c0d01180c401603600100030b88a043c01e146082000035400608030260b0204038645 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 869964028 1106 869962922 869962939
    0x40b040b0a0603020a030f1803080903280e09070206010e0c091e01202112070c02130c11010b0109030302060f09120f07060b03010218 59
    0x2080d1008000c061103a090240590094001c42d12030b008059032100784040c404d42c540300f031541268241c45440c50a1510b440c1c010190b4600424200417504103000c01861091103488414070301e003001d5074400100c1d421542c04c40c0c01049a10f0140e6200c0340440030700204a1300400c110703050302c00d0310341c2240e200d5660a50082a078803550b20341c0d94110003282007142d034562641810040008052400030003000010301c0b84201d03481124031244064102140100400800ca41c0d403003a2038510601c242e0510008810a41d141400188030900780314656103454219a6145400040b18228034002c000c10049070500070070b5840c2041c4c505a1030b44c649441c0c0312240d8050038061084075810b9005060b1a03480c0000201550400303003041c030f5a4402d29400344028514100540b003145c542400303040e119526400c0c41000e541d903100c0e82a00a9104100300801e80301c1c040500303018001c05450942d0b = true := by decide +kernel

theorem cover : BRFrame.Cov 869784172 869964028 := by
  have h0 := BRFrame.cov_init 869784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 869784172 ≤ n) (h2 : n < 869964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
