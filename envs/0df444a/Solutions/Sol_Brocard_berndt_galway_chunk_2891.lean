-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2891
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:03:00.876392+00:00
-- url     : https://prove2.me/submissions/51c59d29-9623-4ca2-a3fd-001907578648

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 519784172 ≤ n < 519964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 519785422 1250 519784172 519784189
    0x102030406030207020f06361f120203070306180509030306220903050705010b0406051c05070807080d020f070b0414041d100c2127060501090c030506 66
    0x3841d034a00580d690a143c030105503510a064681c030b400c500c000c103410140d42514a0748200c00301e941411400c41c40403d50241004410314014550010f5208000480c1d0003038010ba107454103155800c01003043c0c00b420f000e40040341e004840401c0001d41d5824103024550041254105459050b4030601c0a420028011500c80c4005020284102103a0700900750003c011007102506420040d0100281010b0341000742a41e030020301d007162507510703007130081e081e520349841140c044d180040d00e042031744190a01940541c0c1c2c8504416a114414a0b4000801c002c041151002500e0b001002d0a001d0f1f138001c84c080d2a040d42e1215854007900585002c0c40003030082400c0c1c804032440fa1424600d00f46104002c41c00501c0c2c0711210300700303241d04840301640780380380020503c110721241501007085a0030700714100c0d00050030700300c2062440c0d0094002c4214000f1900705040d5a040304600d99981d00c84040d180d5001c00110004666041e2910700400220f03400784648841140c0301e090500c001d2801000061145 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 519786672 1250 519785422 519785429
    0x110f03031009051e0a050708010806040302060a11070203060c040501030e12070303020f09060a03090b181203090c0a03030f03060b18011202040504230106020f1005071707110c0402040501020304 85
    0x43e0f914000150148000c0c1c00c0c544080c420001c0d028298103044843c14054041128a00b02240070030740001809240010110300c181c2c3c05034050b04180c0c446240d000080c0007030500100d05c0d41c0c0103000c66400360340c091290501822111500f0340da92440d00f00050141d82c0704420004050b00600c0850546a85d2502200d10841d8035242c01656856810030180007405a0041c0325000f001c045180190301c0e402d80c2c0f100c02018091214542141d80f4110550720b400444140800980c010412040010a08202035030b00900000252038481720b50b90041003945011780d20590000b06100540718501d90140304410142144140141c9020031001c43c0c11122108004160f040068040f03c03980003442c075a050324080c0038001c00500c5178003540342400604001d4003d0703102e01221210000668640000350460008100b94003900c0c6c45082822290000c2c40c004000000707102c61a240c64011218901000e0302c0790300d40d600ca28540c1c800d0b81320854500340681c4c51140c080e9104010a014607a000030590307048 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 519787922 1250 519786672 519786689
    0x2031002090a0b0d061a030406060801020f1c11030f04031b1e03030605090114040b030705091b0405031c020d0c02062208010f0b13060b030c0904090c06110f030310 72
    0x200c1030302049130401425554440d402e1034070100c0e02140101d069100444c007440c05944240000d0381c56503026402c0f8072943d00c02000b407803030030041c0c60114034103401a4400040121000203404c17444071400c000c2a0f100300d842011118240c401c02c0304058015171040101041450740000314485940d41312208401040a201003526115800b8201486038000700c002e40405011500296900d0120411145044401318415070400c0e000d540d00c1d0400086000440320000c0c000103154680314a00800541c54121542d6082d1040001140a4808200c29009444542c0c0f400501c20540c00c0020708010114448504201031604a00c01613a01c08007500c904540c188618050902c030840c0d074500c0c0034202d510800c00d6508000c0083d0b1100061b0388500c104800c00d484a0080100300c041800c1100d45602409180e10b03001d0010400d8146107001030301b42017401401c00200e603c8992280c150608455000a0000d4034440390301d9080c400900c04102414002c1008500710300b0522403642400c445070054144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 519789172 1250 519787922 519787927
    0x30606110d1b020d050d09090c020c090c091c240c0804081b06010b030f060d0528020d050c040c0e031504030207050d12020d050403390605030402031002090a0b 70
    0x750b50b04c60103c294400c2d170003400c84e2408505284040d00419041c400c074000c0600e001e000003031140c008604516007010042100e185940c0d40700d1070310b0180c2c02413510325820004a9025410348000a4582842107006810440d51030b00240b4206100e66011080001d40c14104004400f54680003c40035800c030f80d1000c0660f03110780c0706000e40f40f0114942d18500d1141d1040700000035009049000550288a0030154800d1540e01d990a200804a603004000c1040c0e1100c1c440c0c2c0d528000046181544119030002c00707803807040780e80016040c020740c16802d40d03840d00f08107880d505a1070948610880803805040028140d0b215800194441050341c2425400d104401c0005040510a0101c880138000c0200340c103134580e403e42410b114a060700740c502c80240c030403100c010303c6080c004c00568045a510041d10a000f000704082500a61840c0040301c0c0c0c0308829610450160791a0301640d0090581a51150344900e824010907180c20310b40c000a00c1002e00c10080044d80303466041141c420f950008480d00d9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 519790422 1250 519789172 519789227
    0x414011202090d03051803010e0304030303050c04150e030f06060d0b06040f050c0c07050105030408190e030106090e01060b0414060f0c06131406010e070c02030a050d030606110d 78
    0x18082e21400c461a0740c07103c003110b42e500405402030054045018503a16524030032080e07006050894460030018040b6500912081001034401e80004c0da02903030044250381015034511102a0310840c40b1000c0012130000002c0c0d0780241800c1100c007a0705420f12004020f68182000402d4020000c48006001c615151000a8243c1c17165045000301030001d845c10449072520b40201c244503000980c0c40051802007007800550b0707601c21401c2d280110b82040c205403400f042d10911008002081c01d101c0c2c248400c0a442e010195002c3c0f0850009100ca424003003003400c0000c06e181c1c00c5403c00e0300010703000c641c244030a00500d8071802889460b0380c42650202e03a5010940a00d155038019040b00740018822041005403c515000444450a1152203169440000300c3c0c2c046880301400d014400c1501c055100090249114483c01308032140080d0035106442c00c00d84803103080803c10403100020984034201008410760140d004e100380e05000015000402c1d4030130006110807007001402884080701007901 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 519791672 1250 519790422 519790457
    0x24021c0801050d020103141e010f08030d09020f0d05031c09170f1209031804181211030309010204060809030f04090911040f0e0d02010903090513021209060105100302041401 76
    0x21051103074203003500c511884c0081000e003501d2300c51180b009608968000014004000c416240141e030b40541c080c50500529101c2c1200500d1160410703a4803901201410466487d0510100c2c0414010b6010755501c6115511504c0c0c210340150702c1c07860307161425080c0c101142c11544101010a482c5001a035102101555a8030341d0003403101040130200b14a0030b00000700000001801200184400174103801500700800048a401142010b0100c00c0203a00200251b40880d40e03c9a920060520000d0078032400c0300030745590400c45800c04960b500241c10301c4406e41004c5850340c0202001c00451a1018890a80030307980500d11800044d0b80c5c0351941c11040010034000b40c414264080c2007004156850080031001d00049403240c1c000c5c0c02a41d00c83c43c0900d2041c011104d4035030b016114400900d00d80424090040500ac01c1117005550a10a2018086001e20514001d16100006080301d50409080201c40f41c20044c008041c1481003004005400002000c0b1050036402d0070007004098245002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 519792922 1250 519791672 519791681
    0x801050d0303200a030b01030227030304080114041109100e0c04030f0614060406121e0f0b0103030813150e0a020411071a071407050724021c0801050d020103 69
    0x242c00c502c1c84a0440b124206082102401c80c4843d135130380520000c4c02003c0158224841c01481243e090307070042e82c10010303039a519101201d08030003404491a10f42da50070314600f142e4007910594140c52100d001d02061125280400c01000c00032580c0c1403030343c104002c407010703d0030070ba200c0e0f12207804418000a00910050040e90000e60f0030070240c0040c0e1001b464400001c0c01d040a20004400f0382030041000ea003010310442c4141e8291983e00700d3301914503128070540c52400900c2c000341da2402d040c2480001c031004034080c40b040c03240b100071a40c3e50540ca806000030310300601c1310810246050840300469107200d2440c10807400d640c40015109400da00a03030174054607041c0a5042070601d031113030b1a20074041c00202100c134003074400c1c0f104111242d80c0182f41c5030402e50b18140061039940342c1c0c4030103450b00d40042000358403900842d0117003a541c4001e00c48007110b90411441c144210114203c12030380500c0001d0040c403001c203141c0c490740d0070208040c101d40c2040c05802d000304a10300c085011a4000e511 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 519794172 1250 519792922 519792941
    0x906180a0210050a02010e1c03090602041208040f0b1204031b0f0b0610020327120106121e12050f040f0902040f0501020303010303090b0f070b04030f021c0801050d0303 74
    0xb207215041a5500701070a80d0b400120884015840e1001c100c510100200702c41c0d9030186400c0c000041000720450490203082c44080c1a1170b481e508000c000b821220203a06031840e91b2141e00b4440e01c0360320300200050403980503072158451b00340805c02282c2c200000c14001754401da0508000c0c1032107442d00125200f403011141d00034200281591034800740400102c84600c92403003210b10b1103914a03060003c80e203a010300c00c1a11040d10040424a208500004194914120282c46c4210304c0c3c038006002400d5514580c049814000000d4095007440350221824110900c80c5100d810a2000c0355524041c0d98a80b10781c0c402000b20204824008800d1042100d00074550ba1240c60b203940e840d010900700a601074031a569a00a4606000a540d40007005490489806450702043d203403400360a241d4a41c0486501c070600c642c00c2001d0400560041501d03400795010341d0720600142c0e0103440c081d140100d12a19040e255120803058411f0507480101c041c10b64100381e4030580d5901c8103240581c0600104c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 519795422 1250 519794172 519794179
    0xd0507030519031d1e070302090136050906100b09040506120f0f070512120d060e1f0812070201031d010e160b0a08072303100801060503060906180a02 66
    0x4089054540340003910705544003e07000d9184d4011702e81a14959640d405210083d00409201c0040110708003501c101d01400c440030354826000400c2646011641400d00b007064141d50f41d0b0f4084c050035240c2001602e03480b12034041c250a0700380c200400d6507102c0c000c454026200384d4580001942c65122403000c10141003058084502d4850104412511116400454402803003012800222484c0c034900c0d010b031100b040310151810b03100d01c0c0070001007913112300150b40e950381d02c42d080010079401c141c0070b42c1d210f402c40100300246500883c91110001d0002c0d4440d5195610001c801c3d141020400c084030003a941c2400c0005842c010345070f1441e00508000700d0349005510304041c8000d0110003043d030300c000024020381160019180c462000d0796004002060740024400350000340818042c56a201c07002c4050f0f001a50312407aa43d507801c170301d42d0040707900f1200300043d60310401c80d80600b406142d01412040340a002c03186040201d080d0381d040001c0180036141302c60805404070300303030911400c25a075401a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 519796672 1250 519795422 519795461
    0x7020d0b04030c08030c0702150708070b0c1c0203010503010507020d0e0f01090f06090e07031512021f0207050411070b0403200106030f020a15090303080a020d06090e0d050703051903 80
    0x1206c0304410303400001e4164015408426003100d961b9070320040320b0a40d5481028141008030340d803954071000400030048409010200f00e802c200c01c0d0100f000c84208101c41c2405640c030340c108800c0c50f00703450000e4009420b6501c130854400003942c1084a0b41d098140680d40239100c8000035004a5103804183d001585054202e6004200d143d8001c00c010b054911100d0340791156212140b00b01c040f01c007600919040d24174007030302c1400301000614050f22090f0005100310000503074024250329522100500c500543d0100c2c004014508007401481400d0340080d40150408410340c40e50131807903000400003400c20005a85403038900781600b80c2d000481072108020811030761245001102e103c40c100050b44103411810000400c9240410f500a1020381a07903040b441601d95602610600c0004d0320310580180c00b8000511000660f118003c0141402072021640d0a1310885150810141a04403010041c00704000004690014129000040c3c00d0b5407040c1000c1c008001207005208201d042040748100303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 519797922 1250 519796672 519796681
    0x20d08040615210c0506031015050c060f22081c020c03030112061109100806040b10020601030b0108030f030426041202100e030d03050a110a0801081207020d0b04030c0803 75
    0x1c00a0a040703d074803603160818078903181c1003000010f010880e0300b683e03d28100503041c02224596903c1030502c004900b48103061170f1031a07207030505005003140d24034050a900001c0144250070034050080420b03010042c512070103666280e00341d10b44228202045540c81039000c7d159048056030440e6501c0ea21142074039107070350711040c1c4005001001038065034070b142001141d6240144420071a04501c1005211803500082c0c1401a81d64610050a02d58803d9550383c2500c2c04c1d48410401e00441c50f071540c0a804290304620b403c4900100680105085a00c2880040003011240b012207801941002d000785d402e038004102d80005050130183e0750188000400d0005483c0035540041984c1803080300d40b0b44010340302c6031044030504a4007180c2941039000d5150007080c14000d900c4560030a0312003001054001c50000381e02c50641c46201400b00203407000004101695042c070241d0281d41200303040c2450017600307800017401c9510f040c5020b40410003181c0807400b05401441c0448103d684902c8060b2203260 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 519799172 1250 519797922 519797969
    0xd081e0315010318030309060b06040801020a1107080c011206240f0c0c050f040902090403081602060702210912030a0908031c050c1209010603030f020d08040615 71
    0x1007a9a807461480007a6409041e640c041e00a807158120841c060030084049a20114094850110203540c8140c0e0b80c0c81042241c1c5440700100701500030003001503581c0e042c1c514028080f0ba038410100b001c03a000b0b0102070001200100f406124110246408c8080e507040c1c48503580200925400281500c0c0c02a1441910750041c00c0c40c80942171664641c1050301e058030728251800100c0c0c0780300070403210341c003082841540f42180c1c3d400100040070307000080d17410300ca5000c600c4110007038800380d0129103204208265446115020300440311248080e03c1d03d0708024130040c1d941c9017103112004981c1811100004128032400a55500003c0185880f4621005881681d00d95010103038040018071000b9020503181d500004031402011105a058008104002c51100814024140c0300e8299070030072045071140c5c048014540101c012200000301d00740386150150002e501c8144410a540010711b0888810340c2005565a000f6004103001c40e1018803046419401441d90b04010000e10032045500722481 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 519800422 1250 519799172 519799177
    0x71401020f100501060e010c0b0712090204020f120124210c1106010b250218010306020316033e0a050403050d030e030d0b0105040b0304062c0c0d081e 66
    0x8650741c58000001b410a001183c4009140390040d010340c01c41d0000c030b8180e0388141703407940b080c40c41100009543c0364503a00003005e0340c1c4243d0000340307041008117031480c151551440e164014800042082d00800e0b661401d4148200624180400d03c034980c00045a8840003400e10f00d800700381c400c0104902c48940b0009410000749110a03101da1240a00100710140310300c0c215605100000000c400c0821040d0160580c2d6001c10003c9800c003640244013900d0b02950400c40e400b95101c1c40c0c0c00340e2030740385c4010f5650140074074450078410103061203807010460011058a001d80074050031450410102030100d404010b420280c002d4542c4070020302b05047c15801400ba10559104000b95044240c075070358101c0554130130500a2041d034008000180b80104030745c1c41520310b014181801400e1541c2c60041002d05d4201704c078103440250701c41070303040540d0400704044064404000714805844c074501102641d125174bc043c00d103028500b400b0340c4800b401015005c0d42e91510940d0100d00035405043c03400006034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 519801672 1250 519800422 519800429
    0x6040b030f1501090515070506070f0e030615010e0d0b0702010c200c010f030b030109140f0607051804060b030403090819020915060d0920010c0203071401020f100501 73
    0x41141c00007080c4101c1c1ca88140c0000244160f48818400b41004100107031042c0250040b19064400c01803900051028480d0318400c01907a201c01d039903440160005003843c0005601148207820030340c01c028176040c00561500d900d40c42032909c1c0d80344184201c04141e10301d60071640540300800b000304012409605400419508041c0c2d555100080c1c045100500707081010000d5035104d81003404074400651290315451007103000ca03d00424601e40c0c201c0881c1c2100d290b14415242c5400700c3c150f41c85491000c000e81040142040300030714291070802401011801840b803002c0008001481142e00760341c0340c0d04000094070030854040c1d92400c16140c05085103100744070b02e500c140a500b0310340703000b04000c080300d40180c0c0e0040c000c0e03d00c5a84610350420202d907040e000a0380b11805002c1a0800c030501c0c850300325010f21850070302c030382a1000c501d820401c00500079041d04202140c10b1100050300c0110b507440445140017120704c004e4442c0b20050741003645e910000305240c032075400c456021440355001a4100e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 519802922 1250 519801672 519801691
    0x40507080f09070f1527060e0a0b1b030d06030510050f1003020f060d050f1006050a1b06061d0a0b040603050c060d0914030405180606030601140d060803090310061a0a0e06040b03 78
    0x549a039103080c0070303c10019100d0b800e0200d030188602c1c04031301e00714640ca0354004c00c14be00341c03460506a00c00c0c05040350250303081514250f110300a15200742000e441100c0e044030040ca100d040c14601041c00f000941860300000380102c1c3c2d008508101e80d02d0315000da030700b244413060090100f8031300b062010030000d008640076240412440c90000ea5640108102c070b10040183c0d6a0101354484c822000c0301082a4460440d407075582c80da4001400e402c0342d1611040307010412284402810109041400d03113000902291185152500c10000210001520f4810242c20b460075a225140300345094014048440060181c00c80400e043e207010340044010010744104940381c0a0b214070103103030402909001c582c641d80001080000c900558000d90008110340010704c1042d107003141c50420070341500c0c401e6200030066400822202c615140c240050885013100160810519182900c182040702c0149482840e9410001e1480d0b1014810450b00c801400f0261407150f441d80d039100c40c01d9003a84101d81288a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 519804172 1250 519802922 519802937
    0x304020307050d120e13050a0b010801150f1d0a08030408190f020d020d0510020403050625050f090a0b0d0506040b131802040507080f09070f152706 65
    0x4a80c0707403000c030f003001c141e030032000134480080920300a13030700d10394802409580b1041c11070f440d40200c2c026000b12482400c0e4000b021035098507080000d0f00d00c610680000319004906400700c07140e542c2c8840035140348074051501d9005603454810144203001e8002111f41c110700120004900994004003c004403120320080300e0511a00b5400c0c00307203c0b41d84510041441800204080c09440d008a16024190000704070940f004041c0e6595071a00d402c00c00800c0001e82c002c02d00300107020043c000c031640b2101000803030705440b04142840070b0700c2d018081c50806003c00442c0086519101500780d8400c994050b0201c502c0d5912030003d001d154100303070031824840b4200000100241070500440101440180c14000d221108002c0e010281c41031401360460900041543c402595031401180d01031160b6458181550034140c1166800d03001c0200030b00125030041070204649142c00c210401150301611540c81c1642e80340000b201e5045502c2c01d4403106154000032403688241d019500303c125110740d140c40a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 519805422 1250 519804172 519804179
    0x181908121b0a0b011d010b030c070305390c0306060103090f080c06180118120e06120109050601110c040504020105040e04120306060f02030d0902220b1309120c0501110f0304020307 79
    0x4088004d01910341800e1040c00411041142c900140c842b13907209003070043c200320f060500829010340400011029900103400c6958806c100d464240804030880c010344101413801000c29500c540142146040540d152015000c5c000c8952043c0d10b2258000b1180da03842c01e01804a07940d0702001c0d108890910002070180100703074014420182c40900c80380c801850041c55850b1101700c4022070040c0428031680030710090407030755031100402c905501f1071051748655040c004158100c510040419041c44030b4640c40a00e55407001401c000754980807900855956160f100495050040340e001d0304444240e5024841000559074980c841d01e07400c4c0e64100100b690b1140211004000f0108a101580040050001c0740182e5002070722aa4009001e06003c902208462800c19081d00c15010003180d64400080d231740d1820765820340081c210a0418880404907840310480ca5411640e81811700a014903444100842034020041c80002429000d4680001e0005005103a2017140e00301c0c8240907518020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 519806672 1250 519805422 519805469
    0xb0102010c0c020907030e01020d0c031e090201080414010912080906060f06071e02060c061006031a011b02040509010b19060509060a0302040803181908121b0a0b01 72
    0x442d542900100800c005459a0384207400400072412109280d5408120184e8a80c1807401400c540319025500010580b0340d007609829814600c60350305440e03074140b540100150303070f00c500400d40058003c03002101c0b01206803601c500506894000518070340c1d81400004080e500b02032004d01c50030196061312019511001044200740448a0081d8010030034851b403800300b0181c000c642510081400101c9403810150002202500210041c081030342c006010810302d00c00324080040200142c0c181440303141c542c41414030000300401c000718100030704200c0c4c015110091040e404035183e0040d2080085041882d00e50340600360a0100c54000c082c0c0076203641d58154045c00c08000c940480d600c450510a006040260070340c080b0480404258080c04003061a41060000340584a040600f00c0d503461034107000d100325440380110418040c42c0420f01003200840c042100022403a0031017500342d5800e0720160006148003108a1540d040c41045590b8081250011a1a05035404181415400f40c1c82c00e01c203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 519807922 1250 519806672 519806687
    0x40b270a030c082b0e040b0604120519050d0503070e040501090b01200c010c051f0507030509011509020a0908100c02010b190308070309080d0e010e040603030203040b070807080c010b0102010c 84
    0x5131070380e10104c807928010092142c00c110220751001080483c81c40344810000f40d44d0380003034102c6c40200003000b00310420050100b110b1001d0300d40600c2070408030f19560321401d49811400c000d40e002d022000001400a5114160b248030040000f0801c0015584411414005104000751180810109110707a4540791003a5146c0403000b03030410090680483c400011152012208001c4442c2c4c410200610580c50b40d1a081100d0700310200700014a0346080100101610030280480c011649402d03a1040104d07000b0080c80152160319002603921041c180382210903c201d1707400082caa0060540410000c006c94020000c0c000643d03009108101420003000b004e107030390007040740c04114521002c00015002c2300250409030300905080316440d80d83c0340118140444000c1c070308001825050092460740c1c00c01d101c891010001d0303408200d1141544d501a580e84624021740d0842c04c0080b82c40340821030207000310303003c4944c1300b60321075126a44c40c20501c4c06040c12007101c0c0c2c0035509004109440900c030ba00d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 519809172 1250 519807922 519807973
    0x31101060618091a060705030a1d18090f01091a0a022d210711010203090717070305030c1e01020310060c15110a0305010b040b270a030c08 61
    0x55a4103480c0f0704071101c4000d01014503100341e4543c808440c8003080e0341d81c10180034014050805950b840540b00c100030100c0e80e050305502d030f045260f0407003064a5192280e6004100e14018425441d6803a0038501038504106594035031401c0d82040c01ca441002000d1110380b42071275400424000e0303900d0303040c00c080503805541c12030410749a0343c01a000040b0340540071019040031306d0300403d290620301c0c80c4100c490f007075511405e0001d9564005000c3c10b958404044085248014001c5085080c0803050316118241840303040c0c0308000e124040d0340941400d00c00c0e030f80115800710032a5911860002125103070f030041900144c0100c48108070200104042c02124410b07480d030303640d02c0c002b02c0c02e104040c5c5030440c808038241c0b100c00502d0740c1000f109509116001c6400c603161803140d241c800c9400c0c01030540b00141c210408545e418002000100603140540b248a04c282050f420801e202c00400840e09410280046c0c0c0081001400001c0c401040e0758001a0303480601a1a00310101e0600d00158005204 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 519810422 1250 519809172 519809207
    0x80c0901021f0207020d0b06100c0206090f0303040e0906061002010605010f05210106090504150f03030e0d1b15030e0714031006080c010810060e06180603040311010606 74
    0x4000c810b800103085801252030903190040c200542a00800c18411004c242215611342000a01490b8502140d0030508a000e5162083d00c1d00340a034041040c90160313111150060461840c400c000340d6007401039801400c05082d40e08014540b144040781d88a0003918002d00640100e103003601c15900c1805204c00342d820603101e240003010200401c98140d8400d0740801100c2a99070a120304807000309504034000c0074035980c0d404485003440708110840c3c1d000025060390000440042143e549030b5407880089a4160901599410072440420422080b2100c02810a01d01184000859400900b0313441502d0407201c01481ca0034940c0b40a42c00c0341e45154280100b03900140c0c0c1005035078086002c0352540f40b0041c0540c3c00c1d6540c50f0030144c00341c8825401150b00e03900088490b0406580c41062158090014000c01c504e007450704601038807a0380301c03c00c103500901000840503051040c17140204242030f4003520507540c928041c14000c005100081d905407441d42030800004106c8c3c443d540c04a004580130 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 519811672 1250 519810422 519810433
    0x70203071b05030d182306070303091505011e08030d0c050408070b09091f0e090109020a120302160b04381201050301060b0720090c0a080c090102 64
    0x151514114011040064000c0c1c1e15445408641500c050181e006142901d0b11012030030303041d0010201da080002d811810408107481810140058400c903803501c03400090701e0450360381485080490281c0510700e400340966020346407516240d10542e100a040f1081c082110607801544607500c010000d262090500640c81445000000e101e01c0d071100c08a5215810f1180c035041d41c0b11891030406a03d0390008521700c0c00492000d8860a05107115070784100091608000f9400d16010080503040070701422a00080b60700002e8411038095201904140d0002c0c02e002c0f0980d0786a50000001c40d2100c4224014042c080d6414000344000c04410150b030442d00489040c2824007100c041d0031000101403500c40d94407070341d07030034404186009080e540da040e0311510f43d0380b49100c850085a0f0708041c1d0000d400303a0324210082082105d01c1040e1030b20560700c07542038403442884280c1e9029000001d075546501807112014401000460401081c18006544030076001c0d40e544610101213005800411b80540c000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 519812922 1250 519811672 519811687
    0x9050102030f03041112010c050a1b0206031b04030c0e0a1a240706060b2709060d060f050703051603060b030f180a081323060901050d0509010209090105030303070203 73
    0x107002d4035031040703d40903007803c646c0b0003481d04042c207440d86403078540c000c100700198494000f80e10501601100350040030b260440055030b0301140c1c3c00e100040565110800240401e84405900e40403a00110340041c1c40320300c2c2680781c000c81c594a080c01e40e01042d00518250a6860100a5901aa0903800c00500c4103c1c94102e079a82c0180c603900c4a01000480d038030400100c00001c00e0b41c07007480301418070f03180040e0301c6540843d011441e60b00d480b40308100c0f000721103942c00c10941d140415a07920140a1300c0c0c10060301a20715012003e040403d6848085a091804014005602d6481b071445030f28150800b1240e000000d070180e04440d450f015101d5161820000203410407640050b040c3c02250100b44000c1c3c131811400e00b0ba003005103410085030f2400f4002200d0341d0409142640c5400740040701c5414014241c0f203015000140d8060304e0302130103424045100807041e0302820540b54510514003051180349403241c4012b00035440020f515100303c030004000310b02414000280c0e032180d6801d400452070842c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 519814172 1250 519812922 519812933
    0x1170c010302090f0a0923011a0706090803070305040b06040204080703020f010513060c0506070906020d0e0102012c06101a1e0705010c110f0a14010605091609050102030f0304 77
    0x10b03c41050300404141c494141d1038540d481090b0092450800024000080068001003c40134000c00f01c040072206006001c080e0302c1101c43c5414682022500e60b031070351546841000f60800341d00c00f0b88a5040407080180c0c0c00d4040c0c00052166200c1c2005104075620710342000101c0c081c1e80103015085d80003040034001410300e42c0c00c0e103001c1d2b40c05040140c1880000c8000c03003007031034540c1c2007440050266140c3c0d1003046030400c802a041451828040307172940c10100c0096503290341e04180410030103840c0280c1c1d010f9000f9032041c242100d080e500400c6820410310b100c422a42c101180101e14401c040019070050301130320641050f9000010344401601108031142030b01d800000d5030b590800020b0110390f4030b04c650b50b801004d2444c803d00020403110032181e8054030989420302e4400654201004502e450303180454281019a40120008400f03100c2620841c010304568112540200c201d10074451111000c011580c00900b4990f030b0b8400b035a8a031401280c80703018282544010b101c050000c10300060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 519815422 1250 519814172 519814177
    0x209070536190806180d0201020a1e2a05100209060403140106180c020615030709110c061503070f06080415090516091812180f0602030306040501170c010302 69
    0x10380c01d600004005450350480f90a200c41690070303611542c0707a4094010349290500595821403000d000850a0200004014001e0f074154243d02e079840306d01c81503001c04035000d0611090b80520070a4451001454552200c0d480c41d01080c066a9030711481010041140041c000c40301c142074040c080c0350516144d603540684200c403030040040c2a540700c50000c0b07a1582215100c16228801860224081c400210068281070024069a015031810301c1c5403079240d200010084120340b100c400c00144000401ca0b00c070901d000e015002d0600380200c030107209030b41094070400141e0040c1241954041ca0391742a0586840d0154030a1101255031440010007140c0d541d02e0030242035011030404500036240303548050070500e100e000f035800000e03204024040142c240c403400b4a45039541c20300900c026601d848044100000e08189000c002e04580c10a28850340100c1c00801040300c0c101c0a414282c5604000e91603800842d0503901944ca01b00c000030724103150f4602020390740a00d03070140c0b22042c0035800460107903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 519816672 1250 519815422 519815449
    0xe06041b240c0c1715060603040506010b090f03071503060806150d080403020d150b0f01170402030a08030c071b03030c031103040b1201080d030908250209070536 71
    0x1c0328000380010704c0300c020011a00d0042c11000180003c40e281c180c1c0c921090401410440c0134242c28020480000c2c1c0000e001815640540d8080d5150140d00c4002f81c00c0000415940d0340501031000002120000340303090b004004550b031414020302d9200e6080a603201001c440900721042c0111b102e59113802d054101100d094010906145415101d40100c0c801c800300c400300310f40c2500c440c07104500180c00351184030080300b0100d82e90310382a20b010000806d00602d02c42910115070b000000b24046540400c40603001a1340690503d0300ea04d014800e5200740d400441042d10400c03010b0703100d600780021500c1c1c031030306803903240d00d600f0680c3e00c041d1000c550a60170045a85680c0c80200700c0030403081d100001400700303440d189020310030300c0d0305240ca0130b420078640d01c0003070b403e1504201010000420b40400d945001c08129500d41e0303d04040608441a09008603000e50041310031018400e450303510030014104d111145000d0400c0010004500ca050b8480660000100014110900c0245003105180054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 519817922 1250 519816672 519816683
    0x21206030a031b0501061d090c01020d0c0201050903031201030305070510150b3402040f060e161403070f021c090603020a020c1009052407060e010e06041b240c 70
    0x6e540314a81c100400b404022091a12907520341044640041017100d030410b8282840074200120580c80c0182c000d07542c0c11402418030002241401040d04c0400a4508a4104903041c403075550756401d02a04a078090f100075075442c094a0040612042503024030014034001c0c21101c3c00d500e190074101e11441c0c205c1c0354000e0524900715905114030b8000002c0420540111888600c41c0c50148100b000321110740c401c043d040b80c148041040b40755020018541d01c400c050f0101650f83c0c5025804844100e800119058209400b00600001c250706c94001d1515900503001c541044180f080b50400c1810f0300d49400000407208802031001c2d80c0310f42c000d00481d07040d80c01103c00c86c00050307000a080c5028802d81400050000310100034528000044c030030800005105590100f540015082051107400f80c050078054984240c941c19080940c0b02c03141c0080d1500c1540c54a0419240c8052000c60b07040a00c606907001c405c002c10240c001e150f24003c64a80141c0030320345660041030581e100f0910b102c05485 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 519819172 1250 519817922 519817931
    0x906030b030c09090610061d010e01051207050415020102190518031c020106050907050702010e010e090a05010521030904050408040e04030f1808060621010e01021206030a031b0501 79
    0x2c42d01d5100c0703580e00032030350708000d0540b03441e117200c00c000d98214540c4600d04011004045040500c0903030100341e0032900a01c0d144084201c5640169894442c242c80000c00103d01404c0140300c982c04406441031300c60103415103011211a0400301e00340c1c040c1ca103103c201c40110201100b209406000100002d0040380110f24540040400290901808034a12201a125203070508a25075080c0314013406480219201c030f200e81007040c4014518014103c0090500c40402103895a1303a029a00107400d00200501003020303881c014030700c0700151400b8441d89011f03071501058048801135030010b4506140179000110300302004181040080c0c08007400944070031a0401008c601c0c2c4121500e158410342c020f4a07441c2800480c203000420080d050001d0903181074045005100c0030074041079668010200f110f102240310360310302c0c145208071039218900040d5864041050024001900a0913200034442d207004183d83e80d002c1410b84030450140020b00250400d03000000582d07424404490b594011000084c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 519820422 1250 519819172 519819193
    0x60a150506041805010609030b0f10050402180f010906141b160f0b040e0115120c170f0c0316120525090b0d1a030709021e0405010906030b03 62
    0x101954020340040d20b0081c08024802d880f40594042c542c0189428030344440c92510796162840420801303001d00e050705007090086030090081a03a000701030000140300319071b1880049040d0400301d45840c40c2ca4020984000c03202050f60088a0324002c442c6183c0b54802481c0040d6881e00180e44100b0040214000c0c0200f01540729104128101003d200502424500c1d42801c0d010482c107400c907231050517098002c00c0300303000340110030782c01a04580c2c0c90460031181c025000c80980d50380505c40010200e003441d20748642800366020400c001d2000c40d001d0050b040b5140c4202440200c036088510680314072081001c1001482903a84c9004c4900e014502804152502c3e60b00e44180c4405489a054120b07100c80e84010090584050b0714800196003011401503140001c1c85000b8000e440385898480da8a4072100c1254030581c2e0726001c2c505004043d102000e8482e0040d070001d4005154140c00c1e1408401c0c1c6041c0011407004480903510161110300841d403030140101c000d826180d91240d0107000750300014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 519821672 1250 519820422 519820429
    0xe10050706060902040314060606070303052805070e01030203090a0b09071a1b19031d0a0b0415051606022a060f0a0c0c0b0601140414030106050f03060a1505 69
    0x40b01400103004090303503603440c6040003480384035051040c41b036030f400100c01c0c010b080d6140c03411110226407509002c034486d550840d0003d0300007813811968424400704082248907098544c40184100b8450300d46074281d0100301c0044003240012104017030154800c0340840c020540404140e988500c0140c00c8404031625a13200f0440314400c8a40c512410070045100e031200c855050241d59800d15010051042d8001d402d015034072301e00c2c1000e000d001d1000700c0e107400c020250405001e2201c0d003009055080c4065071410000c4160303000e0b02c911a0a24640c3c103001e034203c1e102c3c60441e045600d0883c400c2c00302c08040e0700c0343c1e070003580119035841d8040c0511228040a0107103030071580d4a44890740140136240751690310a5500c076001440040340c0d52030141c590800701d4000309608146034220b05090603564843c1c3c01a14096101e006d2a120000c0100340000ea48508100308441c0590940003800541d0b500c805009441604514040d415009100014080f400a40c44100c541c08081416000c032035541011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 519822922 1250 519821672 519821681
    0x5060d0b06040807030c060302030403121505120708010507080603100e03190e01030506240f07020d05060405070915180605090106260403020d0503100905160f0801060e10050706 78
    0x21150f0b9009180100140601c06001e8030060020307040c00e41c0382d0310701a54010445200d69201400301c555400d400c408107130401e103620000c2c100107807502802d01c40d50000d00d681c1e40c0c1c1c14803c0e00c0c0d040d1b00b07110006080d58440e0382e0050141e0702c05402440340c150b5842c0d0400c050518189a9070840c4010711500c1e02050340340018240f0b0000544032040405102400107065620003405a4040c074040c5442d0710070b2804500c1c0060125502e0248281c4a00268145865508c40d940c07010f91300807014074041c000c0c002c012801ca0f0045110700f045440c0c3ca5603c5000702c0640d0120f0b1143d42d69081200030070400402c8055403142c141c07070f10369800904c0c00d458030000307600300704d003a000140003644846405ca100d00c451060740503d500703030001d441114a402c4d94025510009808001c08000f00030000c0740c41140c0d007229031009400260024403042c50884030700c0d402c42c0340000a610001d41131581505002c0e0160f0800c3e4140c440582ea5510480703100c0051001803080d8040f0082004400c100103030101d08035110703 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 519824172 1250 519822922 519822929
    0x10e0601060c05010f061a1608040806010e240d150906020309070b1201030f0314030403030b100e0f120a06020301330e0d020612130606060e0a05060d0b0604 69
    0x50b400201401828000e003181c500c1911851070525099007880403007500c0f4031044907440742e1240a603540c1103003072111803989200c40d80248140000310300426110000310342e082c180c2c3c889020048080d0388130002e80e4821641240080e00006401c040b034200d0381022050032403003e002c0c0d1b8600d07440ba40c40d07101a9044075216101a11115070100a001980b8414400500140b001060750340c240311000c001c690842c84184801050340c0f500c0c21802003010b00a00c81150300d811004802c45e202d20341400c02078090803001080510803204440284282400750000d51207c41c409041696450344400612030f5001069000b60343e10302c1400844000941140021406820600340440d600d203840d04a0216a00c403401c2010442c1d01c455103648511a40306e2400d40d01030340100d03011424003a040c00419841d1142080c2010150041c0d001c11085150b08903000c04014410042040400e680d008115050312001001d103a03c400c0041c030400ca1880c0c6503020f00410035200c2c000055060b4002c2c00104164016803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 519825422 1250 519824172 519824177
    0x7120f060b070b0403021b03120a02010b180106022103070f02030d0c0201060f1a030c180d06091a0c070f1a090a030201050702070f0306021c0f150503070312080405010e060106 77
    0x1000c01007099418014000e40b035480103503031910104d060000030780350715840c009c007584101c0108101c4030452003500b1060f001030020304240028140d0070b42030940001e0134003070740c000f520400081d90302e05100c0e1045a442c0744443c007203940c01c2d5201d5090803210081409030310b03000c501c02032040c52081c2103148140c201c080842d400004841d4a000e101041d074a0f8294440310344447c6905030700032142c080d8401c0300d6100450140407940c420220050184060740a001c03c2d070003080700404101006142c1d48010329a0f800b52411201e040004a8245881d1008844a0000c3c05042c0000c00c0051111004010b12622503200820308000c80e1030300e0100b24074120b4140956a00001103142415020710415402c49124805030074400d040203030003580f0001500c0020001640003c080c06610501044c945591400c40800c2c4100b14518240001074280c4222610a000010100040c0da18000810000300c07544642d030000407001c417020640d182d440060040d5419500c0d50450001c51000303200c01c0307000e042540c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 519826672 1250 519825422 519825443
    0x1314120d020a11190f03021006090606111204051905030f0a0b07020a110f180c0a0201060f0513020f070c0306140106170606030702100501090603050f0607120f060b07 73
    0x700d4010f0441d90141d800c42410b4000780b0f9894450300d207120100b051030ba0090350000280700a0300d0100c1c60000c403604101200f0380b400700301150b442c0d080e401075000c0f100c05540300302c1d4a0350140000b64a60580c400200741c4108200820030090410380144628481c10549100c103050351880424105000303190301915540240c096007081000000315203400828910040c13540d01c080381e4421001c44503002201d440f40603d407010f03041d156507803d43d00c8004520f5000354001d50900746141c06d61034020703000741c9015500705040803a240c2d4640c40f201084881c003d183d11107a45050200d03000940c00504408503c1e0020890000802c11070030b0799600941c80fa0100180030041408040c01442e0183c01403001c10000e0400d15441d040e08800e40b5400c03904c00c840c45540c0f41c580c050103a1403c1100710380300103aa4101030000070410040d034840d80440b4020810340303042c030b00058034182e01d9500486001001c02c55110019165200551000c10035901c0c0707500c00501d150312002c0000c4180c00c40e010864508041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 519827922 1250 519826672 519826687
    0xe0102030f04082409030d111b1c05120f040201030603140c040612021e0a08010e0303040c0602120d1503061e0e0601061205040512030c03070f05031314120d02 70
    0x20007051003c2e804c24021440c4107042801440380c030307440703034032400e0081d50b49036460203aa802d0804121a02008032a403c1034140304400407981d103450300a0301094451800e01c01c10404903001784101c90703410b06404507581807540c070305001e0202c842c0301078030990415655401c048000380c9150700c04610b15861500034440071020b1400c010940c0c24541101004c2e440b00c1740084010f850700d80c0c10042c8200000442c2002d0b52071140480e101b8a2540d110740c21541c244024022002030101c0154001c0d0300030f4258290858582d80140e075110702c590503400071843e003007100802c0e603030040d801818441081c0c000890036960301d80303410003512400d682c04450305185008210743c0c0c010303501c076401c1d080792144040e0034103602d0031802510107003154401c4402552500001001c009080c4542c0c0810700d0384000e01034803420040e2440c1215007007203c3c4c500109502c60100704c1042d000f581906e103d01b03842d10200c5000045681c0b01e000030b103403110118207584524a19010990a44000f90118000c0b0b00030041c1c94440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 519829172 1250 519827922 519827953
    0xa06021b01052a0d0b0604090902120303060a03020112140c0a03140705030114030304030804030b040308010e0f01030204020a1814010311090a050d051c0e15090108070e0102030f0408 80
    0xa0050002c94000303140c560041207807207a0504180f12009002e03034481d448a40c240c000b82030194103d9a200da40003c011600c088280d004a07803190003170792000d403020840c1c80c410341d4900c01a602594000c0c400001003005622400440140c04030400740850060480700310201c1450781035403c20f02e1220045400200c030755051140364105008801d019086007003c0b00090114070060249496802c00305101d02c000e518100119401564020102070b034a40e900d041c00300200d00c003550224001051140001180401c806078280030f170522403d00c8559910716400c00009500c03200100c014014420340e84950305041d01030700d9004000c01c81d10040400d50f1280010212000750b072201007500c809005240590f1241043c00042c0c400980d00d0302d20341e036101e0070080c0c5001c03010607804c8081d00544032003120aaa2010414010407015244441480c0c0c5841408451f0f00030318101c240081d100783d00003070240b84142071019000c2c2c5c040c010f072494022071307400340c80c4550300a4004030030b40d90024004000d0b803030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 519830422 1250 519829172 519829181
    0x1a0106020616051801050d140a09021207080c010f0e031608101416020c0d060f050a14040f0201110a03030204140f13020306191203080606031501110a06021b01 70
    0x989070f251040c0b030059108420903465943c16a01c40c10000041100d9800c0d0040d40c1c024445188603114403619450100340c010040c3c440c89108070301a800c0708440392003030381000800d00c043d030f40c1c0c0101400d0001c101c5001101d1011060203080b01b0841940204000d58a061100300e0000f61300035821a0310300d0608800b14a006c0d0a10050161585011280c4e014125000400c0e41c100a024005c0801d903500180308919006043d24240c4d80311288188400400c042644001c4030000c460906009940d1020901d004846c030300e4264914448501d40058001044519403076070130762050500c11002c04051050614052180c0c0b011000f00380d00040912200c4031420064414034001c80740322a0005204c0041070381e40c503012100c00c0c0c0550700403008c15013075520f901c08240a1000d0443c0d030034a05035110703911100c206840703e00743e0220302d100002c502617013007450459100f41120260300c0f05290790f0a00440d20220303405d141c503c0c940114080703100015014001800011854111840d40140c9134441c9030031074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 519831672 1250 519830422 519830461
    0x12010b010f050c0c0616141609050408120a09080408010e0c120705130e010504030e040c03090305091e04090b040302060f040b150f0a03050d0210090804121a01060206 73
    0x840180030f044200d800000f0b03c003420701340c250f5031030f0344074580145040040c6074003407002030a028414a100b0340d480c40000300c40c403908611424080709150b0743ca500504840041e24042e200d040c4c10007a00300c025101c0782440f60425040d40c00090410f0081c2c440d030f51681c20036041000d06075101d4000c900302050801c000500040e007140c41d094240106200d5560300c070098415580605001c600400542c0d4a90f07010150880d51040248001c0c607203441d0040c005030680c4c416a114a1500c590400c1f960f11074407442c150701d0f0341511000d141428080c1000443d0300780c40c81c1c2c590700415001c200c941585407070182d0446584690080328880c01c0501d0b0103030910b00e000b44100f410480300701c1000040f444004210f50411154070f6141c0e22000290301040001d00000421904181c101b000042080b0340000e070424803c0c0560300740c035002c0c4054400c91050310240b15001d4078500091009000c0c03070f4801c03c14220340fa0b1142080c0d0309000e03540146810380c814264080d02c0982c2044c42045a0403020701c1081420 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 519832922 1250 519831672 519831677
    0xa200d1808011a040504020a03170310170703061509111207020607172509090b1903060c09031b0603050a05091903050d060308091306030302030d150512010b010f 71
    0x301070f8640c1c2c001040c5003100c29124461921200840c2c1551078490094001d103030454520303040c025203120720301d00d5540281d400ba01c40b214144c500140402241d4814100800c120300a010540c1c55500c0d00700c090400040072004001c0b62180c0010790381068440c1c6081b100003249000d8940c02d201c2400b500c2d100c0001c0c41102036400400c20081060351100c105500c0e01c5203401c110066448031861065000c0308901902450349a0010342c0d0021a040211182146e5a202c01406006001000d01122800781e080c0325450380f448050610010301141c1102e1920181c502e000b0444c66500d484002990006050514040481000130310203140c1c54000e041d0300044552007402f050400b43d038100d070740d50107240b075030040406d542c40d01504142c45803048601c14a0b00c000280032950301d03030a01006540c4107801491242c800c060710a003030a5501d001d420200c0b90150051400c210441d24124054225102070400c1e1108111010550b507980d1010900311048050001484118000000d041e00f1843c1810505 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 519834172 1250 519832922 519832931
    0x60304030816031127120618010603080c0307060501091a1314010b191b08130305010519050f01080d11010603020301090f0b060d0209010b0f0d02030a0c1707050a200d180801 76
    0x11b1304140055915000001004202074280510400c1030050805400040c03840c080080e5500c40380310000083e0050b9400b4071010401c99aa8040420455035481e41420740b204000071050103d14102c004c04049000d00f40c804181c05000d6050105501c1090b08042840080440d00d030a00d0320006615030030700b00580c10035103a0303032945050682c1400d081c0f010003007600728000fa4017941c0c0314507944004000c5600100900c1507050003600d000421038002e0520700540d03d0603000992440c03c101a5504a841d104040c107507402e00c08104454001c40f441d20b81c4010764130b80c000000161000d116151805001e400c1011841542d447e0401d54014003402051044030400c03042d00160707540880311411108121031560362110341c0b580780d4001e8040c02d06441195840441080203041c0590840301104070641d44070313584110702c001690709526003550104c0020f101400800e100e54054035101c80b40c15003aa050311065000d12400c18900107040401c0400180030344824009140f402c510765020341b110100070300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 519835422 1250 519834172 519834199
    0xa15020f030a0e120102071a090f0111091903050a2001180b0c0c090a05090705060a051204020d1202070503011a010e100311040303030515060304030816031127 70
    0x4000407803c1002e0b900c602034140c0c1c5403401c0745003581201c2c056a0b11000403c1020002e41d4074100c240c4040b268a003a0340900c0c1a2840307a207106200341603005c1c0c00021841d003828100d006014212564203c55179400b83c6024000c0082002040104000b5101c0e020121031202d19002054890341c0ca0b0001c0e90510180394503a1008004011001c401e8400c82c80106890300003081c54581751502e8080300301e400c150781c001440340c51032094001500c26614030084910a07a590b206004803071244085260004805000098042048080c0542c02a00062813034403a0040e949409000070281c0080c907026900040003002182420301894040d000c0d6446449607460350300300081c04410b0040580d520842c0100078914900d806984540c04900403003250945454903460302600401081d50001d40c01203480c18008054a0080300712885aa45961008481d4888070800c1c942c00703603100c4041051680f112203421454004001501d4550859503800b10030f094090f01c6800490031900d60700b8000c441248225 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 519836672 1250 519835422 519835427
    0xb13022109060703090503040f0303020703020301051e0103060209030709020d0f0e030a200f0a0b04061404021c03111b15040b1605030c010c0804060f0c0e0409110a15020f030a 77
    0x1035003d0010300f0701040b0341e140c51902c40d00b10701c00d54010075142c4007040d2020082c50f030300040313500540340300f503000700050703150350440c0068450300c130700d900c020464150010b10024280c5d40140400040190840c1d035000d445103041e10a0383c0100c0c0007804180e07601e41d11070b83d815140d07014451210107a00c01442c03034144c540034000c00d0607005071100415005081d0380080740b48010013011030300a08000030347c1d18a154038942810380c40b900f65010343d201801c04500e8046420303140449405181d0043c841e03142e845200c1c11080c05244041d2050b03007406840c0e014140344c0c12003840042080002811000f0b0a00001010003841d1040d030341ca00070000e4420b00c010300c1000d11480c2280c3c000c500c01c42794401455203500c1d00524601c0b5062a8030040d5003010804081c040d000703451070740110301c08c0d00203110b10881411800d084802c116003100008007208a0354506081951104885074040c003ca1010b107110358010594041c1c150303202d410503d50040d14440381a905100d00340601103904091441e160340e10000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 519837922 1250 519836672 519836683
    0x1005040809041802131e0509191a15041404020d030e0310090b0a0c0528090806100321020a030e0406181a010509031209040b13022109 59
    0x11507000b00ea07180401d12241522081c40282a40e000b00b40069505010b842c0001030049900102d0070404070305001d0074600c0c01400380038402d489003802001c1f10318482c558884410142038090714078030b03100c4501240516034000d09030f20540200340503805001c0280180021900390101400c04210401c0a100043e5991007900000300d80600c3d0200784c42080c03c0000341040c044625602d149480e0462070020010b2242c1e140e441810003903020407403c40026070070746042c0700c2c0341040c94a0343c01d1b00c00800d04007076200702900000051840c01518554075880740c940742000580b425400d644031950304100304000e01c030008800c4c1c20800140340801e0410440623603582c4440ba8010b00b4441c103166034250a864580c01240140244100c81800c640d085083e44018082a60200072640d40000395003e254062400c940164002400610282c48a003400300590b40250300c0059000762607074007202940d6283c01e064002c40303100020059a40d80350020601c082103501c121550602c5008081140c0080e02040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 519839172 1250 519837922 519837937
    0x60905100204181d151b040e040605090304120b010f0b120a02160f03030902010207060f02100b04020c030a050319090308070c060608120d0515030c120f011a0310050408 74
    0x2041005540c42e403440d42c19006203c40c0518400c8100a1010301080e405d000d0080e5840700c500b008009500303480100a02c507500418054488031008034000850a0340a40d41c48468103003540d0074951142e030100c101d03100354201030300e0120b1510014071198840b0074204006182149905240090140c1e0003590b480c0d0040020100b04e50202e521610202c40c441c02c8041a5402108103204011502d4040c000300704202d001d0b401031050302008144903000d0540c030100c0002d60340041100701407100c4042c000d8211a051b140d009a003d0064000b03c000401c0a0400c0603003035207403561a890b001c0304070064050b00080d411851410014014040780d081012203420001c0d52406c48500c0c00f0606004c00031f0141503000300e00c2e83c401c0e854801040c100008c00b412081901042c240b15646442802040f00c0a01810b52036141e0042c0e003003a85c40e850029000c6450a52a400342ca40c80c212040405007100d500c1c512503136186101009852440c40c1c1408004455056440d04014906007501c136103910303010b500c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 519840422 1250 519839172 519839219
    0x20307030b07050403023c0a14030313033f1b0b0403080a0e0601051521100906060c0b01180213120c080601060503070c0305090d060905100204 63
    0xc010442c0305200c0e000311005150050300085503075094000d14040f40d032000340c544100110344406060240c0400709403481030b1200a240c94a5142015501c1801c4a4108081030341480100301e0419409254080080198000c40410071440a0413060102081e50f08a410706000c4103501e10700c00c482c08160203180240c40501e070210b804000069986401d21280c00044c0c41c51089104100425078022080c500c1100080030500840c540e42665136a00c00c0300b0700800da403090701202d01c03c0c0705501100c003408080c1450003402c0b9442d803001c904007100c48070640c0c1c100215480c5007003c0c07180c4081c41c01920000d003821b20b010301403107402c1e0316a84414001806200312800f04800140170701c0f492501616455002082820b030500d6403000d0051056041d940c1c1190110160200020100c002048a074121902c58071114075590340e0801c1111151000d13a022030a002d428000b1142544800c81d4810392640305900002e13d0a0aa0409a2400810100084800c0e004110038003402d115040159044040007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 519841672 1250 519840422 519840443
    0x708011508060411040b03150a0b01050403020a03121e0e03190302030909070e03070e0a140f040803040501140c2812021c111206010c0b1815090d03060503070302030703 74
    0x130300007400b4213084242181c0c140310f507a10702842c210702c800e2003a00900300d40400300607403802c040c015220b40c007580c8006944000100c2d41000071a0b00b0305501020074490b450700350603c005542004950014103c00700e0001000350401001c241010441161055079081d070000d0740307038501ea034000d5a0f841a01d144501441c1c4820118030398078080c1102080c0b89000409071000c1d5071300c1703010b040c2280404480d5001a9030a01c0648428201880110390207044460f00c10304866559407a0316515030b101a0003190300d9980e40c0c0c4040c5100e0400150540900c1c10170000f80d694034910f81e5058003080034a0341d0815481081c141c0a42c940f40c00440001c4811641580540c5038412254542c10310702c0303e054242a06810405015010316040004204102c001d480082d4151542001117900d4a9000c1d001000015140c000c126103201d500b4210340141c40307440807150309210740c1820511840301070707804c0d02d820707448003028641c0990580242d04c0036110a9000301180361039600025a500b0f120711000d802041003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 519842922 1250 519841672 519841703
    0x40e0d12090c032a080f0601051c0305070c030c03080702040c0206151c06140412050c1e0f0a030f110f070306020c1c09031e030c02102007080115080604 67
    0x240c808124800c0c0031010382004c1c00d613a100d0b91902d5008080c0019080d006102c0046158078080101074070f06151300d41d283d800b44101e55019149a88105130035205011021000000030b4030030004013001c1c622601d115503c038041441807105a172001002007040d90091030810000a801e20200075a40404451110703440401c1e500f4030340304455404000d400c86061041c500440d098503185140564499000d283c0c800c03080710341c215001e000e071241820950b00103101210b03081c051144281d102d06002c900761480100c0c01c840d098a04402c1e1903040b804503011010460015030804d9600b0203082c101d6001e006a8a030000c0515210404c602000345004d034045104003045e0010800c003100042400030090381007010304c0024002c500e0620080326a8a446158101040044814803924a5042c0c03904000071104d50700300680143d10064000400c4a440642403000035003800340b0345200c00140141001030b0071b003102c00382501c00f031119101c40000c2c82c2d60104502080026103641c015080711580d4141282c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 519844172 1250 519842922 519842963
    0x170a021206040f0e0604140601050303030907060c0201110609010b190605030103080d020c0a0f020a0b0a02101a030709050a1817030703060509090f16050a050402090f040e0d12090c03 80
    0x81004c5001040d1140c8020002001100f440d0300010254440845000e0385ea0f40003019549c2c801200c06a010b5000780c0820044203000b07a0043c0102881410800c0b0400f0100d00041d16005040f5076065240c0e45550340255a070901801d84a16060f03d2008094400d050060281075444180720040c510342c000124048082150b5045e0341118107084255400f941e00e5040500d00084400d4080e4070807800050300186110f005400c03103003968030a402034045400c1c5090a00c00070041d0510301c1e103208a12651311002907a0500c044000340001803070004440c140703400171508403031109601554179142c0010744400b1504082c40340150000181090741d80350350f80300c401c0700a084076a204640040003201840302000000c41c071a80c65219090031200e4801500c610914641e0051141640106102d1002c0c026070815400401c2101d1029101241c41207114010030100c50380a0342004903a0000a2000c0b0351982c40082d16003030042c242803d0040101c4c2e48c850300d25100081c031000b40b0810701510b4400c2c2030710 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 519845422 1250 519844172 519844181
    0x40b0d0e01060e0f0c0307140703090b1b070e0405030313110607060b12280c12210f1b02030f0a08031b040e01030602160c06170a021206040f 62
    0x5180024030442d607450403e030b1a021003e40e6440740700101413001602c00444442668451020395603064064203540014083d1a400700c0f0703050b41080030409001c103130301c4241c40007000d824601c48014403001e04640071050901c03007070382c0041c074402407003200f44800306d5000425290003049040c0c0384041292946060718a062242d0b0f03070b103500400003142c00301c03d0081680c40183d00034400e0b10010703000218a030603107484401c41c5c00c2d560b50000c0030a44581c191882100807469452103840300007a9940c480d03140c0285402c0f40201103904440b10a288940018100d0321a9008020b07810105503807450010090803041008006240140d00c0350410010341d40c0801c840102d03e00404c05035801d107441400c01300d244e98401c69a02d00a215000d04043e404524501250200d07110400c1910090742150385400c06580407260364141c0b2500d144012010688030306440c0c00421640d1202020980c4000000700000d1005210010303043c0305000d500902c000c02501c0d150704c40320484000440c50302c2d0001010080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 519846672 1250 519845422 519845441
    0x5034306030b010305090d12050a0225031725092105010e0f0307080d090b01060203120112050a02040b062a0c0904031d0105070b1509011505040b0d 65
    0x4065905000030100c0e0581d101a0b00304100303a80610407070341c41480b03003582e0303500b4030502070b00045814950f50300c042203941c0301d560807821444015280c0309d030000c03400d10301c0e0490308484600d901d4000102020950880d5051b014841c030441d1108440c685944203041404d03d118180d100c03404190f20074440c0030310440004002e008120300d00b00c0610002c0001210b403a1030b00c8422240d44d86452268156948006a610003940301e0078015442e10455596000c000d27003000d50203c403240e845090410002e20004501d83c06440158001d40d290a05d2a0300c8484040c0182d0100404128620001c00070500c040f030464012a0150703404101d1084650114401d0712500c400154500d804c0d20910a26940202031001e82143c0b16041b2081c9000140c2041a004810b031401004501c0790310342210b0750400040e12503215441410014200700c607584032500d525504031006103041d007082e0681c01103450203101907070151481c14500c3d600d5554004020300940300342c0c09100d1001d20080391480581d00d00d900090b919 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 519847922 1250 519846672 519846793
    0x1b0307030804120309050901081905011b050307030b0108060d020108041103030408010f1406010504150302040b130e13020114090307050a060509090c190c29010501090503 75
    0xc0b15541d4203091072140c00c0d500304500259620400040626103d0402c6040e00c0541c8090004280320007007400a01142400c100e031030355220440c1c501c5014138451420080c085c00d03100e10341d89140440d8000c0403117130780c0c3ca03030241440307201c1061102c0f0380c54607010075043c5c42c0e0a082c4001161201d0901c0d0300c6400704852001e505200000d00424a0101034201000042241e002803007215181d120894070840100c1c0d5050000724244001c07c81d50218900003514002c05081c0103281c551114103582690388600c000101b10313140120104040c0a00305419540b000312040322821000841d40024202049070144100107038011421000c4caa41c1409030704020000107140e840c600d42c0e1640058000d41180d030500d031161b2805070004841041c0c08044851404800080d06406510010b0a54041e15a113100341d035004002d043c44802e803003a10b45140324507403842c071030100b4961501d40014800f500b00e800282c000d8100d50080003021501300022908c0d88604141c221198031100402080d031b40e0712082c0c601340c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 519849172 1250 519847922 519847927
    0x70e0406090f15060608060f0d17040f0f0617040b070212071a01050a08070e040317090604060e03070b0105091803070b06030106060912020f0114040e01050405181b03070308 76
    0x42010304800039241c81180e0b00b050089595900d421b45042800700c600235049100d10400300d01c1c52424441104a81d03204400003042c20a60740203024060300250071622004040d00010300010145080701402031016160619002c8640c1a00c2c9805c0d9074040d0000345407025030800718408500a01000c151070000100958564403103007001c0b0b040300c0d50100340c0340c00d0402c8080042002d09042c900d041c141c421030301c003c100c0c0c5460804211403802d4010001e404000044403524040b08540b0109805040c011004040508181c2040c9003101c8207003021b01c615902c1005040d000505e6489500e04462048a060003240c0d148048400c10b59021800440303607000c000707551300402002d0b2080c2401080203030000c000503910390400356000c9074039000e40c8010005400300c0100500d05282403003075820040c900300d81807005e0b0000c3c42801303800c5500418418880700c00144810704143c842c641e8440c40c41d44403038020200140c0e00544441d40d5014103400074001540d801096101008084011640030f0709003135 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 519850422 1250 519849172 519849203
    0x5010b07030c05030c1209120604020114030411090103080a0201060902041a030a0219180e0c03040b1512070518040b1308120a0605090a0c050414010306090203100323070e040609 78
    0xc46c164031204819100305003111075003040c104001440b91155906031900f80c5540d02405003c0c44581000740100c401810194840c000707a11501100d07030003103100d81c540940700c210060b4068203480494200a1010707105000401c00701c0e5501404d031903d01c441d00491070340e17611a083d4031006446003950907802240144c4c0c19030025644115808030000340084018805a15084550300e1004140c030f010407c001c090012401260300030b02a182c0112881800c25102da02c0790002c2910b0020b8200301c20b009810a150401c500e0034000303880c400b500044140150700380390541c0c807220200c6001d00001401d040300d540078410071500f141195101089511180d420345400395220028245900800b0b0084201d000415401c900301d02030b08003139070404c2d00c600e41003a0400ca00f18800d5042c03114030a040644407000010304501c240300850054020494a40c08030381236040040030407281ca80c40c0303002128400041100f03500b000c40c403401030b20002030008116441e1420a00c02800e810070001d00141d03509907494 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 519851672 1250 519850422 519850453
    0x1a0d15020721080402130209040b1315060203190e060d050c0406030c0e0a1719050c121614220902010f020c090c090a030b0705130905010b07030c05030c 67
    0x100142803001c0400100d1042c90003003200e00d540240d800941000a0350000c03a40700b00590090802e00c08094000254101140002512034550080c4400d003203540750b42c0f6032804141105000003a000500065240c00091a022107a1405008078241005141d44101860755034100454080000807a814002424202034900141e8018403031100801d15140d02d4408490182c800302104101c0200754018280c074141040300040c0070265142c07800e00811f00d0388810059030007400d000c8240240000c02c521400070040c00b005113010405110b05600135a2114500d800700f00350700d000e41d070b12501445180304081e40843e10000c00c00f0218801d9030190224100d4520302c582c40002068000d0303807204400d4600307403002c3e0780354a0503800440c1c020000c540041d80e10003c0b4801000200805804504002da0302e031210031188500741d40e0013001880020341501e40791030155508010300f24500b000c1142c0d51400200480f42e2154000080c24404142c04501c240315052007911424180070040c5d41000c075480c2d41c503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 519852922 1250 519851672 519851693
    0xc18070201110d2f09210109030305040c050a0e01210c0e16090b1b0c030f0d09080102040e0a05060f03060c040f0e01080607050c0a060617101a0d150207 67
    0xc19138080d418518101c034200302c040080008000900201d45031480007028025541d26080d4421034a03510401041c000980c02d00c90708147c0e60082e0380c0098581418903218416a5190340320904c1025400c034203010380360000406c5411100d407030300795500441034400d090503005070183d000b0f8040608000000340e1220080c1520b84110600e40740c0c6034003000d250750107450000310f5000c1d007421001c00b40072003010025000c500320000b02c11541101e22940300100040d00e440e1942c0450030309a00194070320340c5610f40204415003d00200340003981840e0070103648140081c0f00404814046803034601081047d04c4e0900080d01124002c9c0070f40d42107140807603421407154407e20404c0308012950b1030010708054602c10a905881680b00600460f03111441c3c121400d030854941030a00b80143c026410010b9024031502000389004000100c035510b194040d18200b0810703141c038bc800d2500304241c82e462038104118110801c20116150b89407a4071908141030302000c1e5002c2042d00c00c3c400180e100074450321504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 519854172 1250 519852922 519852941
    0x24130603050d02010509070b070317010b13060e010f080c09120309121204140a0b070f060b01112805150105040e030a080a020d02190c03020606030c18070201110d 71
    0x116070540220110882c01c0390030840d5601c1c0c4075001740300c1c24014249190009c10050b4082e01d000c0c49408041c44889059581c2a844040c6651001480a041c00c0c40882058000c1c805410148001344000c0000303030400c51020f1142c000c1210175400650410111000e482c2d0680c0054010541503c140ea42903070b403a40030800c0c0c98410024044c1644502100248451103e40062005428180762170943d001f0111300f10300141d0701c80301c0c883c004550003282c4c1c0050000c060043e0002c150743c42c00b908100c0103e03144d100c03a0078108124a16030000804000500100843e511907003c072118200070b48140708000d616030020300364050f0000042e02c60f9031140710300c0d043c4d4404032400c104044500b4829a92446903107050000f1a0200300003804075409030b4068500244086030240c94805120401281044020b601c8408208888006028113070304201841e404201500103014507010f41000078146100081c203418200041c60014081c90300c00e4206003100826070003080e40740c041100514020700762070751 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 519855422 1250 519854172 519854183
    0xb01080f0c010215151206040309050a05061e0d0606020a0c08070f17031b0d17190e0a0203010504050a060c090605030103030c050c03030a030f0b04020304080324130603 74
    0xc40012040e5004940d400d81098140c00a000f500d0b11140d81075031018005240d103041c2c003040031404070203413185841481c03800b102a001d40074502d05440d010344064260307040a801450790120074409501c403103088070080281c040c3c0a51166501440d1082d0b03c1c401e03214001521420038000080b007907000111401c007103110350000a22282c407200c045907548207610540242640041081100f0003105600c03c6403c0240400d49103407031002041c2034070a51030b846e0301d80260750052040d9001164042141140028586241d00355410200c130a05520060400410f03c219614030ba4403a2014041045008240c3e001d0000d1000d0300d0142041c0d40ca03001e004900761100d034240081e0007100e5116a840b6029a2402d44078142185d0854404450b00d0707031000b03000c80e070300c2c41000340c1d800e511f5800b04050034078440140ea020881c00c040700744500507034140a03510b070700641c014030600001030703400002c0e00d9101c403000c3c4002405c03110074180c4445852410098940240800b40d1348400b021044d04100103581c05003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 519856672 1250 519855422 519855433
    0x100f0209090604022a1c0914040c08061003020c16052803030c03020307170a0f05070b04030503100306060e0708010e060901091104090f1a090f0a020d02070501090b0108 74
    0x300c00f840241e1058405403004ca0000b405070b003019541c204000407101c42c5200031128840c40505007200698a800c49a0020600c100c100704106811192001403044041c1e80070b100c2c1c01030740303a405420094040c1c039a0344a8149803c490307980501c641d0541e000f41e0840c01c12581c80300d80018201d02c8510702c9000351070040d0f4031000407070442c02c06000a000096802c2e0040c4207010b00d9070710100c80c0001c10381f60440440c082003000c000441c80801c01902d40141022740580d4401d09001c002c0c0c1000f0030320821100703009092000c0c0000c43c0c110b22000b84d05c5905820140d44ea961006000e04490005400040140c0c2c80c18801190390041c03031424501c100c0c2d6a0700c408410340d0702c84003006d2051100b210750550000141c4010720060f1590f400800d00d80711200300d4203040907110341c1c1c01000e650260117012185ca544041c02c1792440150051b4807248031090364030900c2810000d01c0540e02c2e11b001081c4d20800e6400003070350788800b01254110f030741e11038000d4001c1001108914102900480a00c243c190502c502d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 519857922 1250 519856672 519856681
    0x41122060c1115070f06060f05101707030b03060f1023040b0103021902061e01060f050c0a0807030804050115120615030210020d02010e121b100f020909 67
    0x110004000950400e032400010351840d400c01ca00703c159480c030550768001c140a020300058170f0245603c1c2c0e040c45070700c000c41c40e40d04002c140181d00040f58001441040c000ca0a00c202c60741044000c846526080d002070515500d02000b0b40140c600454503503058403c142c1000491680c501c0c00c0d501078814400960551a943c001400c90003417100c45422029a18030249a082d1a1582c450400c408040c140035040469443c3c4501c804040c080007200960800c100704a4541061340042100c095181d01c41c1c0441d50410300000e04d1017104080312024000300050f071291000e0f003001034000301540070a90a40c1d03054a4078005004150a582c12291507091038000411540001d07404410303160292060700403d0800c1d00ca01c00030300121407074440d44944c20039000c0007507210311038003211001e115001014000c4500c2c10003400c540003a08046d006810180740c00c00580591011542d131102c001c06c6910814018108640c20724030b1007052501c03c540303051500a80d204541d0082d00340f452080f9095181a501e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 519859172 1250 519857922 519857927
    0x80415140a1b1e03020f0a0f0f03050d2c0a030e190b041706010905040305040e09010236060f030a0203220c1401260604112206 56
    0x245960010440c405109030300e46180b0a01e00340d6241140c054000392510125160403407402003400b48080a551000c00c10400c0c1901040801c880c1c007442d800400000000b91544003510200c3c5000400d8002018107100c1414496001d680040041f400100184a00003081e000141046c4542d203250400c030300c1507024002c1003c2850008160151282400001000200013950324600e486001ca00c82c0f10714080b9240144002500c09820600e44a424110141e85628540380c0143d00840c04141000700b0000042d520105032070486046d160b4960301a15410144d60181c040d0040903d245801a1115003100c00584140505103048013801210340d9044424132010f4070500800392002001000450050b5403103500030340e4003003201d001c0340002081500034035150800004051321544000c100c2880004102c41c101003540600b424040d0003041141c5c4d402042e1185004504440482c09002504544954011210701d1401c0d4604507540c41e03110091000301c01c05801410180840e40401207080e90 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 519860422 1250 519859172 519859187
    0x7030e0d1a0708360a17030f1006090509070903120e090a0e07140a0b040902070b180c010c02010306050d03080a0e0115180b0901090c080a050618060f0904080415 71
    0x1c00e10194410782266076032041d403101e404002401102d01c034403004000400d504c01000f0030380c11b100506d415903a041c640c3c030303003603848102800e00b140c440d41280c3c003004030720b40000001c000c13503030250b40e9200c1540d00c664080c2c50741e800340c0d1710140000240f4103045d031a50b607010b40d41105100040360703a651790703449000c54581103940403100c1c01c034658400f100c1031101ea112600c88008040c0300800540805032102c9d840140d07030308241e220ba00f03210f40101c1d12600700710010040c5ea610414140a91000c102c01d41d0489030b40340341e01c56806041c064100303003a10559100790815000b0741400380c4045e0409a503407030001e00405080f02c620f01d001d4942106015424018040e15485076041c440000c211810104a4001120840488030343d00366202000740e16915142c00783c60092943c07100004058a20f400003800e0924001c000c3c400d00c0e41f511003005080c1d541c820341a000d681002400d007106580d6907011035000d05443e488141c3c80a500e104010070401c800c0001d2003910f907030096078500f2030f0002109941c400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 519861672 1250 519860422 519860461
    0x14011b09060507060207050d08090c04020906180a0510170907080309060f040e0408040905090721050109060905010e0f0312012114030a0216030807030e0d1a0708 71
    0x1408030402007000c00e106001800b42c0728056070f001850445140d8540d40f50030a102d049401080f4107108001004500380a0460001000d94065140200c0030000400c64452030000030000762981034150300c55124200040081d02020b0500c0d040b00200800250540e20000d641c3d05480641c5000124000c201056031011111980e0046080c001c01c0d00030005150010010b6080390310090100007005030410b0384143c051406041d40c83d940d1420440b2200981d81d004002544a500c034800c1000340000c000c0b00c480740c0b92444e024030172014104d4070781580900714070b050140c2401d04200c50002800b1040d804031122220318030031206030208184050b5100d00805191222780d0804e900104400241c0c80b03080c10350b8403920104030b41a0002c0e80e4480f42c0c900a0500300d070055900c0801c0c0214019010405030700701440324810300148628654403d4210320a0703130401010411194600c140135190803100c02c00441c0c1c40b0340301113030080015200c2c100403181240d0240000d5407000c046110710070300c1135401c0c140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 519862922 1250 519861672 519861677
    0x602180a1d04030c320616211109030d11030d0506010e06210105040209060d020d090b0c0d050109050c0a03050c0f0a02030c16080607030f0204050a0314011b 69
    0x1030541800c44034581d0300020401c0c0c003445083d640d1000007a141000b003815018020400200301d079560b0800181490344d10a456419074042ca0620040405c0400b24000303041c02d5141c6000703c08962042007182580c6840800001820b0195501402024034060109103500b40d0032583e204a0b501d8007250161000c0002805d45d800070004012001056000654403d80c1810b012110065003404244950301503d00300c0e1030140190320700d0134000c4c0000007003401004101c4065003403409410018920380701e0204641c5180d94001030141846044da004115600c1d080721941e01c452901b10200d107281d038000b07410b40c2d072220315000c004170341541240b2907a4040d890491089042420007801a00100805061402011802e00c001492020480024800c00c0c056a020f07540743c203010088607141040498001b101c190040b40b090040c41c000140c83c0303a01c035030145004210322401600300c800a00c60b0f904010703007155a4040c04002e01c240440360300c4100b000c1400821513035542140321040d2213100000c4000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 519864172 1250 519862922 519862949
    0x504150e0f0907140906040f06080601110d051b33130c0902090102010e01020d0606021c080403050d110f04150c08030703090201020f150f0106020a050304050607150501030602180a 79
    0x55016184050101805e02a1440b4505601e90034140b021491913889a00060503150800849591050a5089444101006108020a02c00c001e411801400246c120b03009100c1000b9592001c200301445031805209806084854002d1aa1008011640042110103000303008180005801c1c400850b00c0e41d003110703401c80b40504000c50280a54825016181199228240084c48020a200801200034800d0000403080d141141c081c1c144400700201101c0500c0081e0100042034000b8900381e0320590500d001079940b10b0110102c401808044004000b410011031400310340c0714001c00903c01d403500998840036010424400704c4070b11203014001080c80798140085050302d4041e81001c201d040c41401a550265070708401c0500c2e1001007240b0540d0480c100d01400105004000640d001d0b0213184060601200c1a4954980e64801d070322403280650400182c0b9000e024900561150b0348000e020305000c596524100b810213174201103006d00030a0400b4000b80c01914090b600982280c41e6601c4480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 519865422 1250 519864172 519864197
    0x5040503121c050114030d020c130b010903050709050f0f0402211002071211190b15030f06071d090103060209010302070f030228020108040b070504150e0f0907 70
    0x300c0301d0700329402c8804141d50002986030500306601805010b04403814030083c007007034070000b01443c00d4410b00700002950013001c5160300d1a180d1500e01060107149030b10101e4840c003200d00485400c1c1e0150b20280c41030080700404191200f0a411181c015001180003803900e4568128a10f0f030020142c800a52125041d460412030448100207810800c4c80c00e01034800e48416110500266484503400b2252030000707440d6801d03034641001c100007000d0180001081c019050644000d032498010001508130104000011303214100c00540c5000ca0030064240c0300d00e00044200c186c0c1d101c106603600000b107111030003c042c2003007910031129044031009040d116282d2860302d804000790311510704c0c0f44c10941c007045414041401c04480d04030440c840e6000748602004100000c5910b06080c1c0c0c0d4024070743e070344141d0f000540ea010803480e4100d0342290045400d03031691841551640f00301ea1088401003d8024103900c2e4076001060b400110b002a9144400c0f16001e030200600240201c1d850030100d81045540c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 519866672 1250 519865422 519865453
    0x9031b030613060e07120506010e010f090b0607020d0b070e1207090e07081c0807090b0909130c1d06090129090411070303140403092c0408031605040503 67
    0x50b0549005034400070f007600809441d14103120355508401c4500454244110400c8003c2100500520140081c0b611550410400c000035410354891200d030543c54204054855803a031040f913180c1035000380f580c02c0c10800703882c18220454013191044046100e540c0c001c000c0342040c00401c43c0c1d812200000c0d101c40c07818410704000500580380104024401c8000100e14010300704007510361410749242580180320400e900030444040184060100f0050490401414511000340c480e0700104950100b80c1c1e5541101425058034009400790a409284100103283c80d019004c1e084081c003d0b810010003036440109110a10600303206002041104070058240c0c0b20400703038008a0600c2c400502440c04025200280542c0e03038141c0340090740c0c6400120310042542601c1482d2487c00302101e00e064078542601d010b02407803002d1050566045403562850720a414400350507004900c40c107170749491414241003048603500111070210b240c620ba509051141801030b01680d08903013008001f0140d841c0340a900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 519867922 1250 519866672 519866701
    0x311210a05010312230706020319020c03040b070809041b0e01020a0503121b0301030506060901150c030f030609020c0601050108060a242c040b0103060612020c0f0a060209031b0306 79
    0x107600a60031401603607003210803c60086c170740c19000f00c00150312428058542c50480089412030154141304006209070b0110201c103980131120301940c15600d5035007034101420b0910640f0340c021341c0245001c81400c408404009040144c581940d6000f9546135001f006a0340c17856881c0000c1c003254800c0c0101800d0500140314103520003000002001a80807840340380c88180c000f0780085070039804c00402c0045505109400500528404910050702c030420200544981140b20000c0c1c02c11107041f00030b0141d90b00a401c06c4004142d1200110340c0c0d500c0e400d0706191581801c0c0140c40c00501404c01164039031800d0a013040a40740046440c0301449802100464501184c0b04802c06200d480700b02a500c100c107506011011103800d14600b0310000c8001c0801044406622145051614000b41484015486502c901c41005440b0b4016521401103900b68940480382413603072017502c101a10b8004000054015080300f007400c0e021100144026130b0200186070442203001c0e0103a00010010348440c550860 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 519869172 1250 519867922 519867947
    0x60506030a12021c050f19030605032e14071214091501050103021305010c02040906020a1709031611040b0a1d0903040501020a020d030311210a05010312 67
    0x21a00040c41c5981c54000e154064105400560030000100c0c207480d244403624122011030749841407503c0c903280700034105070280c0e41c201882c0380000c80002c1911406684444090200281141c5003040d01c5c0c0343c41c0482803200d0351101d404d2505d0f40045647d0320b09600038184610410604602e240ea100101241c40e0508074031882ca0b100e40780c01001c0703c2c419000325182e00510001016205189408146260408069100c2c604044c810041185a100c148415000b5a46d007440d0003951300185000050280c00007074005000b041c80007400e908502e03004100203504441004243c212a0f0b103048400fa140d006018041540004801c00380d00050001c2c04001882000200009001c04084012503140e0b01550482042c4942040145405211b94004990f201c03070004011407074942803200007922418403110003402034003495081020140079801000c01001c1805e0304a444604070714041e40041811034400b51122207490200d45d090350310f03000d018140d0381c00011400094402c03072000c0340d070600e0421 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 519870422 1250 519869172 519869179
    0x30103120f051e0a1b03051b0a121e0309020303030103020f1201050907050f0301230c0d02030f160c1a100801090f110a121209170706120603080304060506 68
    0x1110320641054840d05500e03044501261074005103a0043d00c1170314400420418071300b0301801c080004e6801000c80704645c0b03074010345403c20414425245e00d402d0309048020003c425081075020300c030b90720020b00c44403d0481000000308001021082e001c60301a50406074040c2c104000502c09802c01d05804151800042c081411a40400c0710042c2101d5066074003c40c20727049040104032501e00161001c0ea00f107401c6008110b125000c046040d03048961500050003100008001001144100c0035910005c51800055550340390844030494243c20482e0301640d00d20700d110040e00c2c00d6101c1c11030700c0421a030040c100c1c3c6551040c209004138200000708650b0030350300f42c2d40010903604401c0c0602e900b00c0c2d1050007008040032107440d044603165402c902481c02009e4800040016401500902681d16005000d01d029403c00306021551000700341c2280f4802e04d06922a66120680000c50710226081580c0c1d5484241c11700006005030313581c9220203050f4060034000315010131401c0e4402900918000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 519871672 1250 519870422 519870427
    0x10b18151512010504060b09130908090a090506010207060503040305090f210304090e01090b010909050717030a03060801062d08070b03151f03020c1609061a030103120f05 75
    0x25207418500380e0240c800741c0d821603401c0c4010012410640102d202406040a44a08243c4400003192a0071403103100301540d0380d1545052410300400ca401c17078448401c06002000010b813104040d4018120580700140148100c010008104d07205100b035a0041d036042e541c481c50032110004000801140420303417640004501c50204100140101c841d00182480000d19111803820044e5412100d910b0408262641850900c00010b40002000f5041d10030750200001c9640f241e08285141c03a2203600700078629101c00300c012038014800030103402030b801540c2e0f040c45100d44540c0c240342a40c4643c81400365881c5040c0e910007032251440c001c56070040040c0794110841b6642e00b003051501626600c210f243c2c0300000240a030703180141c1d003800806031040d0740c03445542c0c0000c041100c24040f41d200a904142d404203143d100c0c0c50707042c04154908002814080c0c0071035102e0907000024181c520407080303a180031f001c85030389038652101a24100d075000305c100244071010900c00d450b8070390002512000c00104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 519872922 1250 519871672 519871699
    0x50a091e0503010f1a030106060203030103021c0b1003060c0903020913260c0f0106081e0f0d0e12150106050a090918110102010207020d06021309050f0603010b1815 72
    0x2442800b00310b07aa6080b005c58138080d610030440301090103100081c066410080c048c081c00360000103c0303045907416107042100402140840d41c501002c0400100301d69021001d0084201820064000342c034080c0c0420010b400ca44e07a03054074100d035a40301c001e4200512000240c1e0800000000e518254041c00700c038414007418078848541c4a08480080350306000200e02244410f1040100091411003000200290b90410811641c0c1b0152001708150120050710010070800c0140480c1d40c19404030360440308450500c070005072400180002d224000e190400340c03800c41c05000158194120240041c5d0742c15642442c0044910794000b10107901400384441c40014071150b01e03c1001c40204880c01120603084032031400c81c81d15034060f443d00c1c1c1103a00501419025a64809100320401c1d4040c00041c2d691040101100d4141040d0340b1a6103030500c0c1c00200500c0107856100c1c02c0c0714920460081007151a4a800c10090420480207401000303500300c00103511106280000d6140c00c0001c120452440c0c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 519874172 1250 519872922 519872929
    0x8100e0a0e03070501060e011208041806150e090901060308070219030f050a030f032703030e01060e0a0b0103020304030f11070e090d080603060c070303020304062003040c06050a091e05 81
    0x40349004450785d80d5202e00c00c114480001d80581c0c09002501760100503900320351130b2160140a00e000f0b280784601020700300a0f01c1007440d0b200c00014002c1e90741c0030101141381c070300142030601300801d07180c001c01003180042c00c07201041c03044600303503a07010300ca483c20059190288107084000d1014500c8540c01c039030b401720108001c0c0c1d44040c90035215000800303480f042494010213030034040e20703220241030400c50404456510708008107034458150004860001543c1000c50182c80c2a0340c4680055203861008520111191000c038415154080240400c080c00c10046049200072100900040ca0190a9103601c0b40300c0c810003c2c60b4140402288c501c1d03074035003d400304403004c140c0d03024010381c1c0035001c020310440d0040000307a40080b0440103843e5514140c2c41100309880340030700060815500000003802c00c42503034480c900c0cc00b40da5884a0019034503000d0388285034026603040d10f0a0504800c00503280e4410011104540000d40c2d8001c5075501c0c00348107140300e081429009001852000c00410180c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 519875422 1250 519874172 519874177
    0x30d02070c09090c061404050109030803040501091b0311031c08180114190504120c03020f070902040509090a02150c0129190503030301171c02010204051008100e0a0e03 74
    0xa000312480e21549145c024058580e001102c103c1c110004c05101c10091aa000844c00c0c04881d00721585956955030307032070150300400005c0d40041056020400c444903503c1140c481000307403031050f040080000c010700109a0354486482c50341448002c204404036100d4030884529400c08120316440c85245815170348d0780d0940e00040080000340c5031110400008201c000f040b4070018014801c1000b030703404c107511200c44980c600e030074400c14025441c03601e02c1010300c2041603108203443d4206070f0b048140c4440f8140082d500510502c0d02c80c0c42503101081d41907402041160a540d8010400240150031441a12b1507402c60703130a034440c6550b1007665091140d12424400c1d40c10110108442e10003e0308010085800041590b4460055500c0014080d90310000210713030540d40c4001218800380411841d032031500302480c0c02100460304180d8501c401c503805401910a8402c102d41d000c100034018281201d45903011203031045c2d50804010100002125003071000d03005400201d0100d4050190030516213543e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 519876672 1250 519875422 519875441
    0xc05070806090a0b0a0b0a0603020a26070809030f03060f130c110601090905100905010608030d0c02060f061c2d021804050307030e0f041109150c030d02070c09 70
    0x15006903281030100510201310540c80310342150100300c0142d01c8000300783c0043c900e000e8001415030014840b508d0300d006480c4402c150210481d00c8100d1b0101590f202a5038805441c568049a48800802c03112240441a41d440c40e41220106040d0390b034503030030010140340388005150070000c3c2000d0f110070070441c1d010b82c01c1c0859080d15018071620003c500f8038544a4140e0107800391078944075265001900c00304401c00188482c250100b5100d0309401c0c2980105038591010544d40300c00642081e0380400741d00040c4444140d6003e0702e40f280d640100300e481231903088844d99072000500e0954a00c03491580503078034016006000e1118071480c3c40480c190700e002c80c003107040c5000b940c6540f110210302d40302c1100d0740004440b0b6801023260800d661840d640303000f460b4004041c012400040400c0c5d0701c601e08450b1740094001c0c81840b950209600b121481d6201c1c24425018501c400c0c0061001c1204c0700172202280010707001503281c0f480c00c0c01010000d400080048400c5031503804c00107207a1002e400740300002d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 519877922 1250 519876672 519876691
    0xa05100f0c140307050706030b1008100e130c0608010b07081b010507051c0b3a0303050702010b0306330a03060203010807170d0302031e07080105030c0603010b0a0c05070806 76
    0x2104d4840c00e00c180b4003600d079031000d01014142141c6600c03503280c01c3d404403a00362050030b00d48140e884550342644804071540042c1c1056002504021410900e501c0000480d401a12076910554803820304640c0f88109000394402400308118140010b1030b004c00803c00700912441c04c10128000c0f81549080d54801c0c0c5d00ca5000036000301d00781c0b40442e01c6110b50600000e040b00c1c10001404200b020406c901a035136002c03d292070790b12400500302d980c5000100c4040c08049440103001d80d29240140081c50191144001503180400840706404c000500300d0052401403051204254400303400340400c0c60a680550324501344143e145100e40f1520000c0002d14858a009603c030b6042c003a041c1d290246951001c0c0250000043c0c14442c4480030681180180c010320b00507940e40d6454039442c0e00b041d1256081107008810004012071036600410460503a94202d0070703644445d44060401106000c28000c0303d00c1208208030b90781005002d00031524003944148160781c160383c0d0300e0000d2410084100e647c00036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 519879172 1250 519877922 519877927
    0x6040b0106030f02090310230c1b0c0915030c0a0f03030e06031909020f19090609020a020316051606210c020307021504050a0b07020405060a05100f0c1403 68
    0x1d103036058001c1c0c00380544801d8086041200940000b680e5a03603042d0828101c60b0390304554801c107034228043d1a00c810300d015500c119410000340e02c003980d51104507040d0001c0c0688100b600b40340c4c4007084141038903800074554512600c8500f1a185441062130740315038140310b04500450b03240c50300030b82c0c0d01c0240b0481c04c4050045d03144d801c0c00752070b40080d280203c3c40f400d401c03c01c02040d9540058034000b41d4524010008051070f0901c00318021a00006d002e66100103064402420b01e032460b03260b501680e5a50384180032041d40d445101050303005149003070002d83c00511000d410a50409244210b0600450450311400c80e006048910070001d90000000281c40131420122070300358078000348400200e50b40800c20f034024060000d46a00442000038030809510048580c1c00d8001c0007a100a440c00821000900d56501004816540318110807809141020000744e0306141402c106400c450001c0d2a66062140c00d00d41121004c10410909060024550368100840e09082504a036242800d00540d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 519880422 1250 519879172 519879179
    0xf06090105010504061805070e060414180613090204062c010501020307020108071808121305060414120102190309030806033403080703080403110307080301030f060207020306040b01 80
    0x40c295801600210300803414840104201140c3d041000d0280d00f4500b40025591911041140c0800315880d403140e215030041804985200d09420b01200141c080b608860030103070000c829010300404464a661056202e071800e0074407034082d0480000144020000600c0c1a2946600840c0300707194208078400c9107440986000d282107060249000d080240015030502c0a1640000d00220b401480303842008641d48405900d800340c2c4000d40c0160250034180c5504020100307060546401c10a102c1d07800070301040b4005418140101200c0541307a0114030301d000039405000b8840034130a0030101012565080240056960710000ca01d020444241c0d000b1a8518060600a09110014141603c641c02c0710b0740d03c80e801c1300c503282e00c640e50064101d00407168500c5103000420040c03041c0d2024003030020000c1e1010030175500101c1e8603c6903101c0e8441240c1e00b410303505055900c2c040e0210081480b0801c01c014800b18030b040ca07003c232a1f1403142401500d050056801b00381841421396045035491131060052 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 519881672 1250 519880422 519880441
    0x2030c090306070504121e120203130515070b06010c0b0a06051e0f011d030f07150212390c031b0319021809070302011202030903030601030f0204080f06 67
    0xe800009502e8554101070800071b910f80d02c054001070051006008a800c1c0594070f5503c00d0890388150003100b601880d60741c03400041e489621400040100c01464032001c2980d1074440302110700e0010103501d00d818111955640126030300702400250501000c400d002002500030a9a948103908030340000c20554504410f000e200c103000041c0500740c2100520b13000042c0c030b40e80003840b0341940910703000c0951003c071032108110606440407a81c060160700750f608050303240054004211707582c0d075501c6030304034450342c0d0103e031158041e544400c110002080389613440d41802c2c0c800007001031088a00124140c490105041c02045071303d062110b40c010707040c10045850107001c0312103808140804c46164a80c2c0500082d10fa8042400741a001c5403a0a0340b00c044d0344074085141e8150b954404440890305100002c5d03680c80413a84001c90015000c20580d210b0a0014020340b401000328000450650321240c0054002d03080841c0c0690009071b00b40710018000c4810850089604403e8025104900300315800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 519882922 1250 519881672 519881683
    0xc0a1d1609080f100b0105030708041203021c0e060705030417030a020f040312030c05030114130905010c02070315090b01090f0e0313330f11070f08060709050907050906040902030c0903 81
    0x145d9050200902c104170503e0f42007041c59074444d80c420881403040400102c141c00900901761207884110071620004055080741d88000c0c04000c40e0070803903440b60745080040b04e082c0700455000309281c11600c1100010340020025640146956034050f06000b10b6100b04230241d00164025141c50340e240802401258040c0b264140d10b000b240303003032440c56042801388a211042500c00074007565406041d11794290841d480398400c1e5500100171f00640900d41d80081d92051940400c3d40c0000040e08a1034280c0c0c00751090303000c040ea00c9a08502580c0c641100e0300300511b0000400c010660b225004603c1114041c0b0081c9520102600c210b903a041c1020450001c4841034050020b80c06800d5044c082c100f000910f000401c112035252512030411003d80440300b54294140440b110320600c030001c02c1c0703080c04d50710302416580b50300c0c11110141e450540c02c642d02c6910f8410990040001d00110b1354441c401d90040c01204400380c01903182c203546031003000c100c0e841140c0110031040041107451580c0740c01d102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 519884172 1250 519882922 519882941
    0x1110050115080103021c0f0b010b0a020f0f06040f020612040b1b040f050607021f02030a03050c0711090a09080c07050120100902041d0c0a1d1609080f10 67
    0x50000882d070555001c01e50012a030140480e222080721b4480c000c1181c1000c0f8030985036401010340486595608002c0c465800c18001c00c070140c0074080c04a124031100003407050303650b01c030540281815192070b01e035141d072040c0d904410381e0003001c20044030910303050f4440100d000302c0c0308041880342450480341ca01500010f201e17080348810010481009030420860504064030b00031600d45948900f14030001e00b62041210000c2e014600000121000c2a004805010074000f81e48050203d41e403000000d0100e8402c2400013410100241442865400d20804003640001c1003007000541c02415241c55031503400030b00030f24007654043c1c00180859648a401021301802a008a18034a40a00005500c58900700380340400ca44c1e94a01c054150740d11508201c0c1004a08501c0400100c0c0e68140703140c40d040100c01d0280500c01d28800092401119181026020844416a64251520710002403041074010705082008200310003c2141c41e000c3c00450700012090b030040000e5051641d184003524080d44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 519885422 1250 519884172 519884177
    0x30903110d2604030f06090203010b0f03150603010e0a06091103150a0c050f0708310306021c0c0f0906030203510310051b03071110050115 61
    0x12080000c0d411800038508144642400c107240c003000b40041542c0c082c1d544040e141020040101c400d011580c0e201e03101d580d0080e4024001c200c00c04081c400b2001e0a44111601036004841022001d80c140c3e001680022004002282010321441468500000c400742610f40c2c079500d002c2d01c41007003021111064450400d030080c1c0f00d0301003886464a826a0020018222591076484c3c182c5c11030302c034800f1641412158051261034030124181601d080e0044101011401c5141041d201c1840740c10400088018101c15000609401c50783c1d120080d40041b00c030400b01d80312100348039001d204036000d00300b060589a03481080a14402000400b10300d540c0d03100c01c0616104000740240b14083c45101e0400302d04c0301d8841d43ca00010a01c000c40300350110a46101c1c000791400a600780460842170100c01c408040307040311405014610b10b40125103060b640702e100000c05552a04032103101c10060743c1d0103400713400c10405814041c44410f080040c0c100d1101da01e650f0320401030104407090101007c5c01c20091 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 519886672 1250 519885422 519885439
    0x807081b0a120c12060e0f0c030319030902090a02030717010303021e030c0607030c201509030c10050402041b08060402180604080c042f0906041203090311 68
    0xd0011518200490090a141015190520040c06a052001d600901d103000320200403003890300380100104484090b0b07100c0c90180301c291010000e000143c007004500e000300030b149805c0f041e686002804260140741802d1548800704100940c0d184101648900c080741c2c40580d5a1404031801881a24a01c480b81c2c181010600140082540081c03201600f000d1902004c1c00003110700f49092842c0070b40e181d85a02881031070b0800c802d41c0e505800064144400b030300e40080305020000b101c0004e15030010042180d03817010351341d07100321290098400c1e00b11906005891600300c00344815404c04941c3c8001e0001c450320b03502484214100381c031895620400800750703803510f41c40321440100724920290105214a402099181c3c0b940c0c0c50b51a65070444c50001c003140d6035980d8805030107449541980045106038900084c641c1060700084694910b4082c9501010407600d40ea100301300d19810540c1c4040e042101803001059041051000c8100c550082e1102010f0a2a52800c0364a00c0c151241032070254020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 519887922 1250 519886672 519886723
    0xf050309032d0c0a140109030519030e1603020a0e0f0411010e0a121b0b030103060e0309060d020d0615020c1215070c05010c0c020a0504020313020a080708 68
    0x1005445100180881180c240d2416a098800001d1140e00e600d0215200003030b40c200440c00050030131042c2d440780c0460002c000400c0032040c00c07609000382c0600403841c2084103030207004511000c1d01030050b19060004940701c03510030b00f0340b03441344103141880d0600411000b03000303501d00501d06000400c1c81c00349440c0300d0b241c8031600c41c031940701c050f0004101844a0284e00c060b603020ba013a00b59501c4004e80301c0d043d520f03030780c4030911401070000005032490f46d400341d0a402c21500401e0310f041511200c400e624076591841d500e09005011a407000c2425000138051900103549180003000542d0500310056110412020754400311000d9030b21072420410018400001c4903008503954031030b0802111545152400e4545a0742401c2d80925140010504041040600c58000d80340544139405580200001d00c501c1d2001d5503d0742c645580a548000680340400052030190001c6900c080f0802c112703ca00405503020402e902141d07001000e00350071050050220100402c1185105a007010300020352908 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 519889172 1250 519887922 519887941
    0xe01090e16050d020f03010c0221070f140106150503150a0503070603020c0a210219080921070807090b0f090a050720070e070509280b0403120f0503 65
    0x80c2e2140710300500102c0e00c500e040d9655000d0100303050700c0180003400002c2c0c0030607009407070b0b0480c81d015480d0a242d00078040010704440c0250383d9056404120000d0315078507a12003080c0d074520041c4250942d920b42d000450b1003481d920350050420750035182d1644038108400440d48101401000c2d03802070501400400c16a603000035440d04030303681c07400e0044c0d643c0620402d0380d08007409800068019413000c4040c2c0c0d08404000807403528242c41d0303070994040d0b6080e110954600c150221019018071014800c41764103140c041805400041540440890785240c000400e0410600d5848020590000f03141008114118000c0394031490381258a00006800c60001560442010b03000c81c0380d080d40c1e1800690450f00444404012103c1c1d2080b10303440d032200c0f01440d559002c0f42d0244140301e80045000c220741e03070302400a4a084090040220b13828002c0440201c0e40b40c04420407045894100010005202c80302200510186000780099510700303609210180500e1194152803003000420810005402c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 519890422 1250 519889172 519889213
    0xf03031801080702030f07050c011103040815070e1c0c1a0706091a0a0203040c090c02030a08060f0a0306020c011d07060e13240902030606040501030b030f01060e01090e 74
    0x3900b402c00720b40c02e441d1820120300c0c0d400303807012443c2e2a03440003e0f10803d2000014160f004d894090f61600d990706104100144c4074092481168059030083c20034500d507081d0480c1b025031041c0700346071410864103050006440c5065a90742d02a0507070010304902c0521910144050282a0841c4400205d00112217180403e220310350b005020941d45140a4080104602c40d02003014103444020340a4140490600d009500c1070341c0444407000602c60005004401d8050314a81d000c580d0051401d00441c003609940d50400180040e522169400030030cc0b1a80d9040c0e040c40166018200043c0c80c0c201108242d0308545622414050950b482a00450340c45030018030071007514007600d014a042101d5070f012440c044848080264414100383c50000c645440c0754621070358a4081c0c101074200703a590002e9004a11094a090f90000c07410001440b2030750091700004603404010382101c09160704d4140c124211542c035003111414000c000b004001504082c0905500329541a01a1107200d22040c940b00c6d104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 519891672 1250 519890422 519890467
    0x2120928030e130e030315090f0a0504061104080d02010e0609031606061a0903010510051c05070306050a090201110304060906140904150f0608090a0b06210c0f0303 72
    0x104441001071181e4a43c241c80011041203800c050200a49a1840755101c0d0000c440001e080b5442c2d040c581d4003440d258041074001c40c402828102641c4a194024003d000e00820a5500703030344420100c511103418100400003841090045c0155a1007075000a0a5490768880108650b101b41d0500252090200031034100c00c00c1d0240300483e12a091924070042c1c001d40c0d0240c0c040c000000403044c00003214000070030b6116002c030000c00913541c3d2a2500c6814013403500a540c1c1040d00030382000f02d80c0700c0034046021442d0107a000c9410040d626940c400a03a80c08544040c007480e200d462030000c55821a4a5613044104140a0340c141801c0400c000c000c0c4520f40310340d40400054901c1c2d05542400f081c00c90701c06003005001804022019107101c0d4603510075105002d586a6800d800245442c898a10b0314001c1701c105010300740c813140c5511483c00401020f0403d5a1081529010100c840a000301c01102c40100e04054107800a050b410004d400a4800003640250030802c01440646e00c2e0510305000d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 519892922 1250 519891672 519891677
    0x209060402070318120204060e10030201030c020a050a08091801030b0406050406141008062208091513061209350a03051b040506030a1a040212092803 66
    0x482420f81412100030000080e0310140c400d0040001c00e1504c0001805640a8000c0d0390030700007550741d007402c5951000202d4900342c0c41c101001c41840150701c40d40101d00c003c20f040c41168000c4249071145814a00c001204035200c06000803104214101f40e0704441c0c543d010344251b0745c20382d851916005925640108020701d8543d44800040400a25070301c4081d90288543c140402440e142e07025551580840c0101801d40c410b074400510b46281c0b54014810130000c52049448604565642e1401600000c40c040e0344048101104079210507a180641010b03039030404812002c910304080a0b0111201402c3d50324142e04141d01607020951000b969549035401d4030000e0036944910340745420500003001d20354521680020052040c56140d000386019036042c00320b480d801c04154400302c1542c42103206041d0400014030028184401c0c60340626840343d00300044004500f00c00001500702c0e80b1012680785000307490814807491072410040810120500c00c100c0ca0400050700500d0100c8808a00c000d04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 519894172 1250 519892922 519892927
    0x30c12080a030f090f050c030f16060503270a03030501151b0309051002010f110307080f07021c03240f09020912030d0501170304150507030507020a0806011e030209060402 75
    0xa4085500c138030807580d000407080401600c1c6103003041e180c8100520492113849400007400ea892000310b111365010400001520703145282c440700360340a803c01803201d45034125881d1001c4005034050620982c83e12540058400039000e45005011698180c101262698102c08400d54803904104802c4981c40800414114000c19280c200c4002495030015500009a044139041b4160150020310f0401018481449250250003009505000440320b12000616010114600404452059810a1042c81502c10003840d400600d14182403071000c00002940d1040850140b8008108941801d0003e4803030a40a624003006c042082c101c900034030f0946540016060f00554642d40b000c4c0e45040001c040d2900c0b0210140d2090040000b44601d05042c00703200000300d00e080b0048100e40030355070b2843c07134020444c54583d0101e030380303800c06207084081c00300c200b0600300580ea500e045200100002e100174038140d81001100040160084000300d45601034440074801640c400410030380c028420340740180c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 519895422 1250 519894172 519894191
    0x51014040e0a080306040e010504050c0906010207030f0f030801050105211017010203092e0c05040902070b06120114060d08070f050a02040b0913030c050f010f06030c12080a03 77
    0x8005064071560407456101e140302807010030503c20080c510608088900308540282100d265080e50341c02c490081181d0810404001280f0b416000d40fa0496030620455101607182c2d0307148a5071252061003960107603074511112080650011289000d00028a052410b103000581c0c0070120009903030715030031682040c10001d00182039840030000100100000040408900c040d694001d52060700c8215082c044c2d040c00b08916400d465108071382d555003140c1c01d0403031900c2141440007000101000000c01604000004800070b1500282c400b00d4019180c03201d003402c2110412240d9030034031494a2159040480b4512103007840b01803154021402e40d42c54910082d24030b40841948a208401015009205814400d0041c00584018000c0c400d907010800344c580b0904106021208403090103c40c42c02400b60800a8424422034580b02d20920840e40500240d9044d5802d55030b140740304806d1203130b5400080042c4440c05102400500008480815540c01030b203c0e00010710481944006242d210382d070300e5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 519896672 1250 519895422 519895429
    0x30619060210050405250e010f05090109020310170303070f02070609142403150a05100e0429090a0c05040e100b030103061a1f030e150106021f051014 66
    0x102140420303500858110902c0f981101e406c1414044d40c400c4a50140011480d901001028000e03140002c0828440307078601100350340030b0352006104001d402101100010243d505241c410813419080020b1603ca25013450002c00c5c4080f80004407086521030300b4200b1074203401215000659071302004e640030000c9500702181d032107806480c4404605007052003a044c04180dc4001e580a91842c415032545c0407110010840500c0240c000c4130740c13141055080f001d4250003690b1920b498203002d400402ea01100200d24408a0f0154007401c0040150070f2101880b484c00407180ad82c1b01c04000802c11201d06030460041c03240c0660701450a0f1007003a0300100e41c01e10203035403080c0c009014240c2490b5480d030f100d01d04003018060f183c210003c8902c40c882d100b44945400b02405540e03110031101c6a131f07026400380049000c0d02000c2407083d0503000d0021010109031003440c02030302034401c54000700085a080845448108100c00302c05190314907003414081c0c07005c840307004034040700c0260584444000c12203000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 519897922 1250 519896672 519896683
    0x6090705090301060e010e041208061c0302010f110301170f03040e0702160603020d0e0d0c030f050f07050606031905060708181c02190213020705030c12030619060210050405 76
    0x156024160405c000a090800003c40511030392040612a06030200c2110649032040d09071101980443d09840e10520140c0410000d14a2802071002294007120019048110f9070199040e0f035a600c400001400380803d400c20506c29180d0040013003445c1c205078101c103034690056006000b12411580b01160580384200031090400021a52220000d5038a40c00a00290f0240e800e0075211420601400d00c500004603030000c1088184c3c40320444d40740d040d50100c43c0c0b440d140c8810390901030b05104a130880d64180014000803403140d0020481030410800f010320b4105840114440141c3c02011400001d10114000790824020f0900c4e00668540400b188246010721054584500c544008030b491003d0343c2003401c4581009030242c900003060007400c181001041319001e508012500707040ca540116942c02015007038081c1094a041c00c01000c281401c1ca00103610ba210000303030110501c102c524110007003181e60942c803001d500703c4500d03002d03004e912400820591b2500969890001c0c0602205109 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 519899172 1250 519897922 519897929
    0x250306090f02060c010501050f010504080d0f1b080903060c040f030b04110904030206060a090203090c090c07060e0d09080c100807030b03011b1409030616030b1c1a0609070509030106 80
    0x41c49413604010301c1004c2c0200300900c6140d200c0d826880590505502075012202522003120240c124440c0f0a84141c840b25901104c02080048000d8162500c044080c607000e40a8402c006841e40d8101103820945003a1010703184030712001e001c020800414107249013180440354031000c0d0729090341d500d041034080e034500c504c2c2060300705034503108000c10140d000c01d1091080004580300c41c40152508030020480c003040741c040140394020341c003610183c50140012a031242039950128076110807980c6d001f060f14a145080304603503105000341e800043c1c20900c00f0016003a91001050004003a81c001415030140b083c0c5c4005200a59000c01d007510311a800001201710003030000e000d03131309c0601881c49000d488440c0710300005010b441e0000c40c40101d20704071901c0301d000400401c0c0c0c03512907400198001c021000e266060540c2c91031082120b0303d0f1261030300c26602da5600110b045018a0608020145850129240e60851078082003440d6607100840ca4120b0424a007036500c602c42c0d100800d00400340c0340c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 519900422 1250 519899172 519899179
    0x1006050a0f14040b030f0f070e0d080c0a0b070816080403030c110a0c080c0306010e07051c0c03050411061c02130b031501030b010c0f020103110d1d250306090f02 71
    0x14002c254403d80d200114086c0100220310349655488040f8a0306149054440000040c1d00030718101a40c60003140c120100c03801846003a01c0c04400da80324034034002035410100c1d201601c1c0300800240703d40010314103602c95001204140f000f01a10344c005d00341580148010149031f928054054554400c600d09002d1104550486e605606182801c0004441e02d103c0c0880e94410043d82460b21304000c60300a040f00c1e074500700e5910039203c2070800d0301e050704408100c000c44129000042400125406000c8402c0361a8400144c58140b60409802224800b00990300400c2d0401064581d614078100d00003072541d00000c0141c85040c05d54014041030255407115000c020003000f03100950100030544100290240c038100400603402006603107007a0f007004085c041d0400809190050b5001e50049200403004000c180d1a00002a90440880d801c000b0005036101c0c2c0c4000b100200d10041180306c2e0707058200e51079081c04103071250b2040c001c0255404000c02050700c0742c2c0d25404000c00541ca9102c0070307a00a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 519901672 1250 519900422 519900427
    0x30325090305120a1b0f061808090d05010b0901061805060304052e0c1d0411040b070c09180c0b040807031401090803011806050f011e020c1c06051006050a0f14 70
    0x60905121b00b05074400d059408514108402e041003451054943d8402d911146050520710038004102c2002d8410a0a07203055481700c1800f07500d903540014041c06010152500c04c0035140309840c003280f035030040e0407030303809094100140300105000142410a981044000e05111f0102c1c4882c8241d2403032010700d00c01e109080128580100390030140040302c0c120303601d0441040d40392220400050302c43e0030000300100b000420050100d105504020101d45019125004109541e540c0450031039000f158401400c440d07180c016803c00c5141c1000100800d48003800501b060b080c4003d0f40e0f1102d00da840001d00501c80300b00c44000a0001b9044203a5040e0000491900c940e5107540087c04c0071038450000c03110a01e4000007041600c1c05000501344804181c0d181d0211030a480a800300e075003419071a0205500c1405e1100c5026075030759448592403101503201c4801c86855240950654078007074100528070b0b003c5941803090301d43c0881070b103204095030314050002c0f4bc460340341940c1c0300d000e10158442c000c000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 519902922 1250 519901672 519901727
    0x111b0a0b070e0910051c1b0902040e060109050109180603061b0f050a0c0b04151e0f0911040504170a020a0317060f0909010e030325090305120a 63
    0x8107200302c0000070203030303040d00d040e0f0b654001c5480000c01c180078840d0700c0180000000604200221425100c2d846400b14942111700002c10040e0100340c0c1d0f1081c10001d4000500740010407118000703640200d0207017480c4036954200307070028244e0b8815020300e81a2f204080c10707884892100c5d800042c000e5800070f03410490803904000707081c040351482001d640814600d52404002d00d106c0c8044420580d202d540d800b0a048482e5520b6002170805402981c0058640900084600c0c60348140d4502040394850303c4c02c0341d41d41c480028151048910170781e80252420080340085803107590b45000300300c0225800202031303540c0e14004a50520060b09000600d03400310780c4180854001882c00c003260700070b45a080100303801118108070341e4404c40e034564002c0c144403000300241c00e0252845400507042c1e000858561140250185140c004454405401600300c01c042000451200e0590102c041481c10003c018150780310f480d6211400f80021400d00350000c2e040210300d1052003008010b00c816400c03513115020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 519904172 1250 519902922 519902927
    0x9011428080c010f17040804090510140607031b030216271b0c060605130506130203070c1b0312020a05010507020309030d08060a0f0b03100801111b0a0b07 68
    0x16a024070500c0c0e1141d0300d8085015800b5a08810030240b240e035460f071a14401610b00e1014a00150080320141c50500c0701140440550042d94400c1c1c11580713008208500d401c3c261222603401c1500c49004090800c00400401c0c1e100b0b1013041e405800e5108120800d48a2030106d15258036402c681184a10004010a04103000c41c0d6004440c0780d44182e22604400036400070f42221600030f541038040b140c120410749800c0c041c0c0001272155004440025156540754080340c19410040c50401070103545908020183c44c200200f1070705441d50344403c509600c0d1070400a051396401350405805010600035442034903481c1c960200155074000055682042803402c065070741d00381e0309000c45c3e25500304800148598130004c00e42d088054010010004e6481c4500151014517014054541085e0034000c04250034481a03c840001c2c01c02414550b03891800e081035440841d80f58009100a904003040600c81050300e40a03592041c200030300405210613030541e007034a842d00c0014000c11825003201040071054 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 519905422 1250 519904172 519904249
    0x1a33070c0608040b2d100816090e010902010e21030a0507032003041e0909032003040b030105040203060103140a0b030c09090d0807020a080c0c010e0f090114 69
    0x24403070421044140c54050707140350702a8110008504141d100340d14a82140d40c076801094012060a00806e205910f807090f49042468441d03244404a5648034100260442841100e802c1c185d104003c0180c04000c1c0d000070701076041100010701c035200204449480b50901100020703202007403002c0760380d5401c0c1140302925a811800d030030707004211030040190003925070020700203650440710b0103945082d0410800c9403101c0703413110700e01070002407000c03001c00c181d40c440c411002228000d8985030203006140704000c0b0006054001038103150014002044000d030240103590549400b100d01588030b6031010012030041c136003065540d104a0b0414284407180f01b042c0d1019510710802c3d420345d1454002442800030f85c00064480c00e8a07035011800c2c10307011a11440d4600d0b008a100d205072000c0034034035121824144c120010a1980d80c000fa0400d2459613080f8044041d403c2007610400040364070080002c0b00c2c0001403280780452504501006825954513514450308401010140d201c0d5404400800c0300c01c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 519906672 1250 519905422 519905431
    0x303030c12020a020606040f020c07030c0f0f140409080906120103060f0c05090607051f02030702010c11030a0c0611161419110f0d061a33070c0608 65
    0x41c1c0c07811051811075418001c071004982950000e00709a1506420f10004000310700641c02c90907030a0180111502c000c1c411a00114020343c44c045909040901d085808a0240c1c0440c41c2006004e2081044c240412400c8290705c2c42198009110122814010254480c444400d90b008c000042c00d10412000454013074181d0f07004178800c02044450b92005000c0304d18410b00000483d0382884a0310443c5801e800508005100320b040da00079001c28002100004481007480410702d401004228180c0d030b09106100d0b00071218980282000d0108060316285d01c2201e03a04810040d02002d030509118094020800850b00d00d26034035510614108602104034010030100c51244100c11007480c1c030b120000d84101e8110361010408120b840c15611004008100342000d60031191105038101150381e0400c0b181c088030b000ba900490525088000c0e04281130000c901c1da1303c10000002c0910010305180c4c0d62848140d078200c40b4164039403004400d917170280103c1d036000300540703201740001c55420350142916008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 519907922 1250 519906672 519906677
    0x1110a08040c0e1009020c070902070f050118020a0519150906020f0d090e04030311120105011b150f0b04020c421f03060c0f080f0606030613060303030c 67
    0x82e01c1d03c48928403d070030016030b4004c03110b203214041800f0f1014158010048074413582c1c1101e51581d594400c05d403c4e44c000c0a8142c40c040310804c0c00000b07106c070a0144411034220031207005158180c0d640010440c16403809824000d206a0388407a84910b58525403001412002000c0c0d1035401d0440402001805940140e03401030150400862194100203105d5403001483d40380c4203001400c04580c030040901c007c00540801d84c4078940b42444070003a400078072a041502022400c20b41c1003400242040c501980400406a403218100340490b81c0409401e501451000010514442c201c0c0030701e01400780c551140794006e100041d201210760000507e04003040741050205030a4007202803403d000900858101c010100c00c07800030307072000080d2150650195404810303000303064600100107402030241e0030458207a540c85d0f41c8480c09607040607100d2505041868404144e20380030128a00c07580c2c01501e010300901e0040007041c2d0700d42da0110901c906e640740100c1041160343d82d050040140840c016400702 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 519909172 1250 519907922 519907943
    0xf150f0516020d110706050a0c08070804090c0c03200f060901050a06050613033c110d05150403020316050304050a090b0306060f010e0d061a030f060f0901110a0804 72
    0x41c00e070040c500d01c081000c13000007926070a840d180d03054440ea4410070048040040e52410302c4000b03041c03a00070b0005c15000b164103540741c45c28092000200d4028418000c140700100030300c1c10002e6031100b1414007042020021051050300d07100e040c0e01d0030084020341e6405004110420483d400d0541c0701c2c82c411b44038440203010303e9503240c050091900c682d0310807010800c500082400070031154103100560414660400000d08001000c00046500788018100c9007000f400c44041800f09445640740380000407908403000321055520f841e0f842025000034802242100000307000c0c03500a00a85103243d1120151a00510a52078426200c0e400380c0292886584c680d10040380045044c89120b4030190003400412054540700b0070004010044607080b810002c90a0669560380c036540d030201d2045102e0100482d070117100030403c801d04a9943c000c54041d5000d61035035504801c0004050790041a4546443e40513100e103210b07036000d0030144a00305603591002516004155001c01403e1045001c2c441c0c041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 519910422 1250 519909172 519909193
    0x3020a1a1b1f021809330d030f03240e0c0c03070f030f020604020603150a18060306050105120d050a0210020307080906090607020718090b09061906030f150f051602 72
    0x2c0880b82c00c0d9215a811071b4610421386000303000d000315480c24200c04c05982d0001a2002c0001c1050303402030011400900800550b81e03c5c2d0b07805010b13440701d0704104540003000001195040780100428415400c1d00703414035011074500c218038412282e032040b414007540c0e40e441003420031144003e4415012000140e0008107090000d2003c61198000d540c01060b49103507803204180c90012141ca000115400011540002001240480300002c10300001e140030804c03502d982000740448005074000c50051900e90819800345034003107400e9030000d403941081902e9514404089142c140b0910742d02072024030010038400c0003a04681c40701d00c103403400c0c01141c895030746010100740c4844003070790801e0140e8048102840480c0922080c1280c00d60041e90000d60280d9507100c2512009065483c01944e4100b0310610820303507500c40c4910a542d54900b014403040b4990b03900c00380800d00000b00500020b01000000052080940005200c002074100a0095040018181084084030040c5402610540a414 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 519911672 1250 519910422 519910429
    0x15040e0903030c0a120e061009060611070e07050d02031e090a02100e0613180b12060f0a02072108090c010e0d06091b03020a1a1b1f0218 60
    0x100d00c520b42040ba2981404404c1c401511201000c0c00b101c1d0a072500d401000810030010071500e4858805c40e106500c2c2245440301e81c038101d82164220100700007001401a544140006410085504034007e244581d40c031040200c681f40207054001c007400d8000414001c541203034a00c1c1807101c0100d500718800c0c030340790701c40304503139641c08041300a4009200c151103020f587d000e03032210317829400e000c3c12603032030980c0c84103414100c242e5541004c800481c21442d81480351006214004114000b92851107030103510441076a9520001040d0000f010110400500780d0309543d0166003900341d02c880c8c1c0c0504088808900406881904100700000d0328480000f00d115100043c840540141070716100d4001c030f15101403000003001182c007501d400c0e80b201c4d01e810010f10240f480c80b1a03800d50b19000d011850651041100840c0c8940c41032190350b0341c410181d81900b03c1c1808445410003440d43c0701c40100790307600c112410103040c40310a00c0e12444c1d07a208860a0711442e0024030109019041c8241f501ca24502003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 519912922 1250 519911672 519911677
    0x106020f0606011d0f060c0d02100b010206071e0e040c0f080a0203061014070f051c020d0509060c0c06040f0e06090f071d0409110907090e0a180215040e0903 69
    0x511804c25900328100c40c180c1001e00341241081d5020300342d103240030f0b00144141e24000000c414400140d002e071200300004181481904080355091000e8001c81c2844035000700183c40f1580c101c884080250038007a045801400000d03042d110242090001d20340e459809010640300130b010101064407000000c1c4039256074401c90b8800c1c00c0c020103281d0b402259103802c48802041096a00d5811307410030400c800f048440e45001c8031a881540207040c62104048901004003240850409541c8281038402c0382c160000d0948610090598515444081128801d45030803048205103400c050000f4010805545425440c010740e4640c43c010700e050b80b1100240318100d40d0407100400c00a0911000c00d0100744281a8404100049108008282c030172100003812112540390441d00c011040b11030035024100204090b0b0301080340c0c01c213560014900b815110180f4001000520580c0d56050060280000030855800f01a005040004c900003c4803804005070f215000d1544c1640340710740001c0050800004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 519914172 1250 519912922 519912947
    0x3030f0c08010b0f0f040f03050f1002030f1b0d050c03010f080f0d030b0d080c030306090a05070c17070b15280b090a0302040509100c0306081c020f03030106020f060601 74
    0x1680790920742c1c07400110340c0c0c20401c1703000c0000344104000201021700034500d001442c040c0d0f000d00103002c400403200385840c0000f0482c7d400180103100b08040190300380ca000d0342c0102182c01c0584807403082541060329200e0340c01c032004850700d400c080c044010007041c003650507104282c000046503070702c4100300d0b9524140489020f11641c4610559111648250801c0d1031281c0007504103921007181d0360768012540c02010055509500c044100411450440d00e408c0c1c020720a83c0041109040525000f400a010040050304840c0007070412000c110841f8100c070383c1180c10901c0e4682e541403071131400548642034041544116008400340c1c0c103442c0c41c04040020280704d6018030190303500d081c14a82858005205243d4000c48074130b00000075860314007925103c0ca1010300a40059509a1400021688800d503802c080515186041c8140303500015001d203001d191060441088028070b4049103001c005e070480403070501002c00006012900010151131100c0414141e421580c0c40c000119600980e015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 519915422 1250 519914172 519914189
    0x4051612020310150f0305030a031401180b120a0605090705041104120302010204030c0b1c021611040b041b14090a120203010908040b070c150e011b0c0303030f0c0801 73
    0xc00e40c1d50840c40d0341d841100000401c0700c0285650756030b4240041e4071700f2280d0081d00c2d240c200040d590030741981403041d0a0940d904010060440d41003202d0f44514245841d03031050705940c2d4110303030003843e42d894070380c6415861550100c0b98128260b2400b000a0181039505000301c0c40798200115280c0703428013030b0114101d0301000702c6042078541884002144c990b1102542955800c21000c40400e602608090203802c00d441034640d2072580307007410b800b6240c800c445408018418840c06443c640702c0854407403181d4014100405015482c0001030040481c082210f5100d03141500c0c1c0d406881c400700f503946c03201d0304548a114640300100500d81940c8501c038096640081c1c201c9050000030400142010f031940040d000141081a0343d403603035459031160300000d45185000c200d46080262907031246000c0e04081c0305000c000c030701c00e00d000380c0044150000345041c03100004404020f0b209881c0da010515402c0506030000b143c0c0d9080c017500400c1c5030341a94000038100f0304200411030142c01070f00e04907070900b03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 519916672 1250 519915422 519915433
    0x1a160306081c08150411180114030c090402041706010302102f03130806090c0f030a111c060506010f0c171804020c0304170a0b131406040516120203 65
    0x3844200d0fa4510010400c0c1d20281d10300358101000d486520034075180c0c6105000e1259140004194440c041400c0c204840c100407468800c0140740c0700003001e5135080b0405502003038881c01545c1c0003030b0280c080c035000030305101c55015404014550000e4400e0499000b81ca00e102480341d452800c5840328594030810369070311500600c6042e803220101411003001c0c540c80a69052881c086181901c00b46998010301c06980a01c040c040c103c10240145881164100c5114003110303600c1010075104c42c01d081011340080b14110320300415440346026420688508142c0c400301040b1454500010070003230700d500b40000c001c000c0f1400003500035180d04030629000503500c4c03100303003441c04052800e070b2007024070070032041c1c0d1816088044d84903400a0f0070743d641064080c5441398104809184c0c4040801003407195540441002d2012421500f8150b80040743c08503803d50550302400c008802014601645015200781d0040009020000c241c400c591414030310324404041d40c844109400c2102c07120301a5154000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 519917922 1250 519916672 519916723
    0x30b1c0210030906020a09030516080c0d020a030b0106020601090b06070305071103070510021e030406050a0f031407030b361015180b03221a16030608 66
    0x9251460300541d091501007103000c0c0079075811081c0c0c0c01c03140000c00422202c0c0410300c00c20105000c0c007044c00000c10203020700280b50040469440b20031410b0340307008500141c00d00003503446520680001e142c2045884089580d200d00095403100244900710741186088d010380000d28202044810150309503441d9230402c12140c984201c3c854011842552510823404001501e441c0c681085070040e8103034014102103444850712460011100c004110207410402003441981d41020940c0d81c001c106140042060000c04c20540041c400010100085c0c0d0f080130812801542c1504a10480ba4090314031002c01143e040f91148510a5050303a0030910800580c8110107119180c0219407041c1180c10140c9a11365800303610f0582800c1c1c245070700014024412044112041c00c8455000346510f0901c03034503500c4c0c0b265418008040710200e4100d8841c1e02071100c002d104100b5811521000001807020040c00c213522400d0010144500e404007280c18480c001480070000724507018114450000d03003080360071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 519919172 1250 519917922 519917929
    0x8070209070c15021c06081903020f0709020702190b04061101110301031a090c09040b091005280207150902061c0603020909161701020903120703030b1c02 68
    0x40c01840c0604020300701d07101d0000304031074010019181050140c0166520000042c040d440c50f00c0d941000407603404c0100800c004c2d600084e00c0311070f21880f000c80b0140d0f402c45103412030078007000e2504854030384154900030401c40381b6940101074082c0b00715214041448031505942d20f8056a200e0f40582c204180b004204003409240d00c02040030100380002080050000a5181d0b9002038006481c05a0001d441c41410a400b594298020300c0900080410b120784600050101c1d000400080190a40300d006c03400c0b21004001c200b40038401d1140600a510b4580c90504d04409290302c032a46501180c650040b10308014401c07144c2003074000704c0102c50710304000d00e0000034110300607089030014820800300c4808082c00c15100c0003000d14041c0800d07664075600400480c540007600c000c100360030016034100c03039403a071f2a003c2080302c403d64418510b020002e64414028099901025090f001d401a04405074400000510741144240c03010030001020304203215201c4401e41c0b0303036000074000344c00c40b201519 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 519920422 1250 519919172 519919189
    0x2c0c0a1203080a15030b01030b0703060e0103110f0d05010e0d090b1c021308030313060f02030603190c080312100902091003090602090414070806012a0c0b1306030513080702 76
    0xb014604c00380641ea1340e49010240ea0709034021358124001c036050040c61513160090000515000e10411410b505584a89040b030036262030007841924020700d40166034413500908216030750400020050940303504902c3d502ca035292001031b40000d030b82c103001107824900c00040d01c0b5020f41c0d98250301e48090310303188440029800703440ca41e0b003420014000001c3c6000708000561180ca44140c20f180240b08501c0d000c41603503508a941c4078614010300c10090140c40004925408209400c01462100c0c12801c00c7e48640b040c9410600850200203170008280c290351680034000c4e0506510080166542c003c014124050404110303400f8048800d215606482500800e02403401348500500c0c02d24001e001070201c41c0016051001c0b640c4050401c007815410810f0150f10580c2800c2a481d4030121a2552028030305401c0425482c800d142e03280810b01c004031441e02d0141604181055079180800325900042c801841340c82c00003800c00c4005031103861000c0c0c003851400e0303101070704506081c100d034200401d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 519921672 1250 519920422 519920441
    0x414090c0108130618030201110f09010e040e0709091a01030f02060309030c0105040f050f1f1509020a0203030f091c030507020a060c081504050105030307062c0c0a1203080a 76
    0x43c041080400072802d180301d510840c9040c01079150f42c4001e41e150181c00d45071200d6190026040500940418510b0501141c0e1441d00034a0110100c110000006000f032880340000005031084038030200b401c0d106640000100380c0954204c140041c0c1c8100f103001601c000f404028410450310040d0001030621318040d46d004540002a00d09100b6030050306400c586c0119025070322190140400c0c070038007a0a00c0300e06c1d4801484030142043d0200c04208000700789101540c041983d43d46d182000e041c02400f56408040d11102d0019036451021040080d600c2d00291507807050100040c000c1441c280c0300084180a070000c65040d5405040701e20790540062000401d214294040c0d841440c0000c2c0680c860003030b10340e40a845994407800c10112466602d03014415541c0298980703001400650340010641304c210360f100b180032401480365580c1184501100f16542d200141d1004030301d4082d08042404601d041d0145c411041c00c5655484020354200040c102402141c0e400c00070410080c0f05401c010001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 519922922 1250 519921672 519921691
    0x409020f0d0c090c081e0f01140406050607083601080604060b030a0614010302210703090f1a160e010f2609010506010507080f070309150305060414090c0108 69
    0xb499aa00c46400070b4030054401c03403001035655130400c211003201c1095040042d41042d80d00b001403610a50b4401c8200c0e040c0640b00400c400840d41007000c1e541d64101002034840903024a031525402e1414000a400801c0010b80150707807031410b090180f040d0301c0745051161542c043c980d8101c0d064401502e606070702526641c4c100703490744404a0000303521030095020b00c002c882d00060b07643c90300300003022142602c5100750406004000c55084103107980ca102d502c25404c2070810200d44c0700c000c0d007a0f0082901d940c00074208542c0501c480280036031841e02e60f00a035542c2942c810b8543c3c07084080114800d0070b00302800030940314214118554404c6030112030048040c18045d25040303401c5a01c2a05d52207000c98a42c1e020310000401080c0c0d0401e004040d0040c03c207003003050505144d07944101c2c20740a9500306130150200440c01e441494031440c410002824405c05c504405c45a000b0000c010b0002154454021810202d03c00c40b021800103006101e1440e50024001c03075500c0c0401102c072104080d248108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 519924172 1250 519922922 519922943
    0x90a080c01200c01060603051519151707080c120702070503060a0b03070e01060503010312091d042609011407050319090603111204031101110d0b0409020f0d 69
    0x40880c080311102d0800d000025807151500401a012802e450064106130304050400c41480503014080042c102206422207503103412100140b04008150207946c0507640305002122400882038021036004041041a000a040e958601c0b10a81d00104203596048006508101070300391b070074038100c1440e00b040c1d07075206640945555600091400c8411380f10000d95a40d5000000030614041202c00000d101c000384c940001c3d89400c3c800307005030105100180c0560000d18608050ba481480040003400002c201c060301c600c01140440714410b02210210b6400d0396032106520103902d0000d109151070034003288103203024640401140c2407804122070101c0000d05010720300002e50203002420780115981c03500d0000f0044800c1c0100108480d5001100f41488e041d5030820481c0c4040464821041e40300c0c80304401c5d15140b40072900e030300103108841d02035480e00301000c1e201d44901d402401d2020009809004102111041000711003075a0002544607030080c01000711410000c001043d07a9015511540c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 519925422 1250 519924172 519924191
    0x70210180942180b090114240a1d040219030209012003070b01120302070e070507020d03080106020c04060501080a05060a030b160305130f1b080114090d08090a080c01 73
    0x46039002d90040040c88108001400b500c40880c46441c050340c00440c0c1010a40d45414a0b07849541101d4400e0f50084140900c0c014a40a044aa4040d10010200c1d06650780d040840010080103039032071440344901c0a9a11040305150074001c2c2c2c4c0b0b11400504840000350030b0b94806400a50000d104035052180c2c1490040d0060302c13200314411401482d6003c3c1d48c0d58810340c0361001c18941e058220602a030b8224240340c02003940018000c0130b9801c50240b000d00c503114180309840328041da0000035070043d081101e9004140d4840c405030304030764158080b10f40151090040009580c0f00c0d0042500042c6e0200028200d18095042260401e0018108100840c0c80340c03528460319800302c1d4403002c0a480707007081c1108030380c1c1840b40070b5010000f0360304004400e245591311704140d082c11001a08603264030001c0031061805000c41001400a0301c020003030804c000c0c0d0042e03100380080300c00c0d0449010b034400654055002e00680d511650000016040d511a41d036101c4003d60400313015854550b60320070015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 519926672 1250 519925422 519925541
    0x10801061b230309100306030b041103070317120c0a050706050a09050a050a0b0703020f04180b0303040f03020a05061213050102040503100603022e030906020702101809 74
    0xc400e0642c801001c1c0d507903050013105200b0303040700c081079a0013010301c1c00350208049003103e0005500300c0d50010350751016580303000000b844c2900603040a042000d000382000d13006900800100707130480f07250a41d89400c1d990f0f200e00c101503010314211800843e030204407010000f0f05a600140c5e00018001000510364025102c0b01c3c60310041d06012905548250001400e10184074100c0368000482d18043d450064085401c000c2c6004a106018608102c085030702c0c41280a0b4002d4079170030b003001d0210f0742c90f00c0d43d0308401420340702140300681c012500c2407004900790400c2000c031401c1c0c68440340b00c1089920b50a9200c0e0f140004088291800d560902000c143e0b6a4284001d0303040d030103507660109130641140100100c606240c0c8545d03090010b0400b0602c1342d080a0070440c08801010f040000d400d640c03074101070740607203e085d00081d4440100e4240701e00d101d80110482500d40200812010800e48403070041e400c540503964107508401c641e9500014908081519944845e45207490240401036003010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 519927922 1250 519926672 519926723
    0xc0a0c0803070903150504051b03100e0102090f0411041202010207080a0b0f010909031e210e0d02071a21090c01020f010b01081f24020c010801061b 65
    0x2c000001c02da02d204005212152440c00341c00c1e02e003403208001c1c0f400c0070b560702d5507201441c55001c0340c00c201c46c0802c44050f507403e100818048940581c103000104070604c600c0c2c001c0d800f444215114a07070862403882642014825841c680301400c4155241c10b00300301001c00303056003100089046200380d00001c1103151051240c1da090078402c9002c440241082800380f00c28140c141c01100c40149410345420200c0da0019410043e0f1b203c0410420240076603030011034a10070ba51000c519030000b0000e000040c0215940300080d0101c0a40548178290f40c43c40c0e00b2601c0d50101e115010741c0c4031281c610210070030f85400003420403030740b036000c3c21810300c8441543d0105c85800b00c92a080c240c11251200b4090f503014882d240d00140c030303140208644901d000010780b0000010b000400c51707031400b0b690b40d0028100020414050031100703c2018002c60782c0d1a4851614018015080050140070020240c65010300349690603904945c0f40d0b150101c00fa9000e1001030310404000b582c4c004001d00700c40c101407021500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 519929172 1250 519927922 519927931
    0x1505040e07051f17190b01050904020708031005060324031507030519110a030f060b0c240106080c0a120c091a040f031e1709100c0b0c0a0c0803 63
    0x41d8080956102c40018102c6204c0c2e00c9a10f50b00d84825007001080003861140320703c1e8850b002c1e00045e02c641c0b15801200c0c24041d0f44001e903005440006d200c0280301e81140a5845402582d03a1000416150401d100386800b090315040c141c0c04010820b0780094108c0c0c480c2c1044080c014041303c1800092030700411061100b170340d00c1400b0070350350414804251081c0070203c19110020700180071118803400144814468a0301d0342d07007016940e400714580b440054204c00010400c420342152285601c0070219110700004950816810620a00303404841c210b40010f412902151140c0059540d0f02d04c50380c000c0e0307010403164010005000317240d00003400d50f84a034a445403415900c41080504140c2071200c017080400e403c400f400d40512041050100c0300c681c2c2e10a403940441e100b0b00703040305a811101050700d44e000c010aa84042c00e403400c6840440005421400c1085070550756100c0e4091003030b03841d07203011007000d00509240310018100b400034a004011a030198a8022494181a19541d0807600103170f6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 519930422 1250 519929172 519929209
    0x515090402030114010f0c03120c0e0a1508070f0c081b07230901050d0f020102030c030a03150501030e12030c070c080d02010c090b0715181506091505040e0705 70
    0x3690030130703503409454141c0c1071129061103283c602980d140903141e07038020300c0180c01c5d242d100d4401c0318005d4070030b800104d80c0c0e990140c04450640d4031090005c50081e0107000c0c0c0070018034070200041d00144540155a01d4030700c00d46484152807255100e000180e4403c8994106d8802c03000e220007107443c01004400010104070004146505102c00028541c0190380c03403032032041c09002c005200315500c0d10240140c0f15404000794000c0c03003032880180c2c03d6000c2d8200040c0305020209903900a01d401d604010000c46980c101452420380720401502224802d9015805944c0110324810050038500010340d08824405c21060410308155555091120160070414080e00008454122103809002d01c048901c0301e4148000541c4c2400d440c0700d49402119030151450001100701100301019602016611840a100b06038a807441c0c100fa0404214401303684d140e0500d4a0f200180642070340c443c0e002d0011040300d02d08202858001000050007501c061030380c0c00d000e0082c00044e65964090218811035003003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 519931672 1250 519930422 519930449
    0x2a020c01030b0d05102313050601090905210d0c121103090d0311040f0b0309060903180d060605101701080604020d060507033e04030c05150904020301 66
    0x400004040e0380d40d82c200940210092200100003680c04121804a109044800280c400a1603040c088418403400310b00c60142c019024881049840280c2c10b480c41e0180003143c90700d0b43e0700c0d20400210366a060f40940300d600301e02c81010300038450b14402e049000e20b00066034100000d042c0444100d45207041100040b803c11003000ca15460386001e506090340d0103602d6903043d03150181640c0e407105595400303101096a02e40d0048540441201540d000e011941380d0a240c0d10b4803100804001d038016114008030b440350b0400140340300000008c68590422110030503104020820602080d800c03868011035010382c8038180440d064884071a0740c2c20250103a950320044a80c11340c0e0903080a481a04401400d8018008100241e200e05420300c80441d13200b540010181e440880480042001c6c118075100541030500e2801100a82c445c1031441e481e001c0c0101d80348074147c01a60326540b0481c40014240d0410040c02c102070700d40f0034260107201d070100328264500320b59000001e007240d100f60044101e40420 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 519932922 1250 519931672 519931693
    0x60a030618051f1805120706090b0709090b03060714131503061a0309060103110301150b0d0e0c0f04052502030a090905101a0c0604080304020306060910092a02 70
    0xa01030101d00210825403e04001c1340c0303860301e5860307150100001c04000070014881c81001100c0e440034a00c01e82003c0300d40110308201c000144000d81c1403054032a51420000203c18a15021440301d024a4070b6440f02c03c01e00c844183d407041690031594801d12100383c103000c000380004000c1203044e0150a0b581e070002d2250b09050300050b040c40043c19240131034034103008016400c00000b92a90660b41c20044010607076035040c0000e030150444840d07520000d040b01c8d80019180f0f45c250003515011031204028403006d03108035200340d034a080907103499a002c1102c0c99054100c0c10650302c50340c1c00080c20280c1c089000400906c3c864000d2400b1100310050380300040b4511055030104004014205280051149081648000c030b4020114014211004d0070000c00242440002084032607250300e032025215a0b180c10b0408080039001102e061f4040c0c042e010000d001840c00c01c092a100310b4420b5082d03600c80707082541800050403403040c00d524105c200040d84d0000745d81c2d84128002c8042e540e00400341c8282 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 519934172 1250 519932922 519932983
    0x1401150b0708030601031a0d0b060f031209120325061b1e050d1103100b160b1302060d0e0f0313090203130803090703030314060a03061805 61
    0x2000e030310055052406001060001d40c014040301d0b081a002d02e004140785110030280d030081a081024036a100718940c98100230801c42c1100741e88511402c0701c0000e2280d041d0b40034103032144000340d03e0403c0c848003040020640c3c035100502180940201e4200c81c1440805042884640350f650101e09118441c40114030030008240540d00c005003000c7c2840d6100d000c6000080d1410310750388942150061300c50400700c1d15030320500680c0c8140d401c0307850900c2402c2c0c03c04050101c40e441500c40c1000100c098501140009201c0210703000c82040b540740002409040e251035030440780140080138009640c40c28203001d0b075519000741c50384d0020f240c4001000d00d4080c005900e080440c00300550907800034080031ba01040c0b860b0745c60342140c0c03c0003400350303595407000350203100b43e006400020302020000c4103102c1c40000000b00070341682d1094a0800865156590700890703000c00300c40d0f03282d000341c1024003030001030840d40100d00d2940c3c9c2220752041c00001c940e145401c0007000d0174013848510915130307134202002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 519935422 1250 519934172 519934211
    0x120c0705120a0918090c0b040602070f06050717040308030a02030f060316121104090503090a1211271f0609030b04140a06020a020a060605040b0f09070c1401 69
    0x12926090700c0e2401001e9030002d02883d81c54455420741e0503030b000200303007016020b400214089602890080707030161600080c0503517401038090400140329148010402111030100e020650301c81d0f4681d41e0401c3d02a42e130f0003400f82d5204080600520742440000001103201d80a10702482c00a48050b807640741c0b04403641c0040400400c113501c83c2e40076082030701600f000c4204002c20b8400740c08a16100b41c0a90a103156909004a01150401d02e09111101407050200c00351800c024201c403004141607442b160501100d00e011000b0300b540c1240c6048000915051424100401211320036045034000b41f0020035501101300c400e50585540500c06400c0c503118580305402402c001c0c101942000d003507445003040c0020081c4001c10b045804090a40420400c20210f034441c3e0f8003007001d42da61074402d64001e4840314a860225940f03401c2071400701d464070f050f01404001d201d000d0542c0790000314013800c1150591018007030780c003071100100c40038012404419038001008160800484c0740079141c1340501080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 519936672 1250 519935422 519935443
    0x21303020111030310030b0907050306130501140c030604090c0801091b150210020a03110406030609060b0403021806150403110a050418060b2d040501091e11120c0705 73
    0x10780080040001c0074050010385002d0326040034030080d8a5a070102d100346880c0254001551501c1402c007000580a100dc038601011031180e0000e201c22424101c0301490588140d42c920400c50042c0002501401c0c5079029214441c01410746503030460751809036500b1242d00328007d403601e41a0402a01c07041507007404001c0101403640d440c4080702d007030110080d203503130f8031400c5041150b07000180010000d110350040c20903a40b0360203520b650741d07544e2007015000300003511542c60300e50300b4080c0002c1e503030f08000155070403641c0180c80103500501d1b0f822048052200102500d500c5002031101c02e1600b090800544081c2d0711401c4000d6842a803401003281413001a8040c0d441030303040c0b42c40c1c2948050901c4c01d401c51560700c0320012440c030101a00080d00f26440d039140680340d00384940401421098a006c05804000640302004180d80b601407001c1030341d100390100320001000c401e000b000702860781d00c10241e0803095040305003070090340d11260f1030448055480583c405400f0421702d003031100602442840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 519937922 1250 519936672 519936707
    0xd0b010509031002030406110a110c0d02010f0c03180803120c030114060a090506180f122e0e0123040f0210020c090727030812190213030201 62
    0x208112240003a680d001c0340300c5441003c5030040041000c02c401508000840c4500c4040c140c0c41d0801201c004104002130380c041e00141c401d5030940095410801e0740001c000b50181d40b4680403a015150070303501100446003c030708016a812182c08003400c48280c6c80003038001c000241d0fa840c5048a1000e610f007a01401001e08010101f0040101d1448880382c4400a80107442268590b1245ca2003035a03021801e5110750341040000030114155100c0d481141d002500c1241c640f00e4406120b0240050441c1000280782c181d070180050340d0b242c10744848203d441030324103545900c0011745100106d00303079035841c901011326a4444c035040b50b45514071542e4840b4019042040e900b036190a4039991a008004030000e40100710654403560281d200784170081204201604401c0a030034003030300042c80c1403801000300f020a481c005c0200859105494003204403500003030020b00303010491115511190015110161000040d240050300710b6450002d010401400ca0110003000d2550001408003440200e11455 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 519939172 1250 519937922 519937927
    0x71b0806070f18051903051902100201290d0c080615031609020a03020f03151f080103021903020307030602130b0c0d0c140a210e0108070507051c050d0b0105 69
    0x15100a0410f002c0c08492049909614221305d42002030b022021940001d0010b001e003495220622694002541c20580300b9100690241c2c0d80200803400c0b01d07401d280d00680c0016800c4021524000c03c4c00e081740c0b4807001001c0c9180c52031180e0741c0340ca8100060380808079030380003034040018041c804401c090301036005401504003084402d45a8034040034038040c075031580303a003c240501042d10941c1a103001e6410010401d50b00d00304400e503a05408401030080384543e5440641d2042e0045c00100f150500002d620b446d07406900316800c00c220010715600c1c00013107000d03238100000035a80c2007040100a5004490059650408801c402001986500285141d2074100040410750f80001081c0320124024500403210035118034000b080e400501003401520300c2103001100a1200110200c54404958504030b00e0409034080243c80c410b100d0318450340800c90840014031142d01510050888074480e4007580d40a22203030016a66482045119a0002c0d0010a0080d10b141036441480000c2000342081070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 519940422 1250 519939172 519939197
    0x1006030b010b0706060905010605091023071106071505130c06110703150e1e0a0305030c0f0a030b0f1e010509060c070e0f0109051506071b0806070f 65
    0x521032018855440b40a074001407101c10f11003668041d0f4090802c3e00820701080d40e503807000030714a4000406071845405030421b0303e0344150040156402404210002025071254070344842c1d0540c00140e0300303407070041e80d03004502a030766519001040074910550000c4613441c01a401071040381c0c0c004200e80c4001f04810440c2e0041040036013450103c4166140030500d020080389014127103d500d41c401044000c00038480c8100c010542c10041d02c0402070700844800e040180013209080000c604c0071450b40c0c01c12441940030034410f03802541e010403400003051801ca0401e00c080725991010303040f00e00182d6202030007020752826540ca10b121803c00c440010704084510203c4044a020142c8503052240c0020140e400d91141010742c2c0071090060190f0700c007070b80d590350411001e40045800441c0c54070075074008100030132148160350040484481c4050480011814000c0c5c90b031040c541650702d0322040c480c00c0c0d4501c40043c003e00280009001815150411a0000d000b0742c03d450040024401c1604980 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 519941672 1250 519940422 519940433
    0x9060815071e0309020d06020d320601090e130204111309051005030604120305180d0f050408010203091b030c01020c0f0a0e09031305270414011a03100603 68
    0x1a0300350791000e4542c198044600800754010300202c01c000b90031601c889201c80600c281d6502401509078843c07014030041d4041600072065654000e142d44003020144010680e4070401c20f800c90b803107441030409503081c544943d41d0a40e41030088038a0f007404482d0011083c01c5090a0090641203110b4080c004d0920350781d0100000e074441036005800c1c1860f990701c00510340284a07803641005000140507200e40e4146820110340c40b0060020180100b4182408500c441c3d0310b0701301d2000742000c01e2010b09240c075141c04080381d04030407203840041008400e100100b1020001e200940c010340c040c400400c48002c03c2032041d0f900642000d4910300c29040200e0386491641c01054012040608031240b11142203510009000c1c0074590300141140080c800800041c018004000c210840814801c004d115036604200281d81d0002c1c130365181404c0300e0f40c294400712080301d40000d1b041803003170840003a9205000921821518441c2050b09074001d031746e00c2c58070541403e2019100c50081c049040c020b041c21a19079 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 519942922 1250 519941672 519941687
    0x7030507061421060102030d11070b10062c1c11011409060702131d120414011110110909100509010e0705070c030b0610030e07090e0f070906081507 65
    0x400340c03c20000300003d4096803003402160f42041d9059020030020380800c12012941d00128000c445106814010482d4900c80d000c448085034202c1e030303564542c502902e00d000580e41c034010f40104c0c8610030b0004401c1c123035554462103940400b04030700301ca101c01450904500f40501064071a050001c100c00d80804584608100c5400c1c9000b03454a0b5600c04d00d51000c201010001038481c114249003c50300c14003001e0b08110307048245485005c5070340c05a00b18000704600d02c298030a0781801c2000d41c2e00b0604a5009503000c0c0a0705c225103043c2c03100d0141c40301001040d15a580660008070100046c445003d00e80780142c6a001464003481d141d0b540e04000124290f20018002c40042d007a000001030b4001d48108204c40390700b030f48840005211607417442e05000d02581503071201d00c0364840307190107c200c074460301c45d40c0800c0e0000e600505980d031812900340010030550614003254022040024000081045840010a203610780003441900c1c040f00e0909140e10035031900b00c1001c0f071805020072a94480754 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 519944172 1250 519942922 519942967
    0xf220201120e070b0f03010e07020616031a090103082d03151207090903030b030102070c03080c030d050f0405010b0616110406271503020a090c050c070305070614 71
    0x100050341d0b1007104516207401580d6016400340c201c001018800018400055412102c03260103001668071803c6041c1d0b02c0b801d040307490080c81c1207030000c3c0c15041880381c2c10284100b0300450026001c00c01880c0406c8000c2400d80081d140c4000c0064169140983c1482d41000821034100130b85c100c1c5074004008a0ba07220181c0701e07000e2500c00300c0444005581e0307078041940c420000f800711540389940c3c0d81c1410103403c41502c207402081c035207968030069003018000c0310310156004184106d0745045569600d0241c005040d0712100b03210070300291f13844000602c10346004000c1020301803002d26262809030b01b540c01103215039014110a021060714040f0900e0100300741da62220b030640c141445080030500400c8554449014110b00d40c1411103039000c102401f2200c2490360f0340a02090b20b031480045507200131440000d42080da1000c042009034102d5224201d22011441c0c030714908140c00716010303e1320b60300f0b8000741d03141e81208004000b903e0f000300d8521065a02802e0075414a103010f89100038401c420403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 519945422 1250 519944172 519944207
    0x120302120c120732030712020c10110c01020f2107080409020a031401050604060c0501061a04170d0804080c0703060f0603020a05060403050c060c12030f220201 70
    0x19558140704001c1c02070007411000c040046464055a060000f5000402c510f440e50030081c00040c050080c1050841e80707100c0240030002c501d0310300e96603500034003c0c001285210441c014214110381c20f41d01c150100707080d0100782e03035968241251140c4040c20304130010010b40c1950b11685941401c031002044004601c3e03908510759012001000d10048980319500300146601400100072071100e00550150076003142980d801c10030078421098007019100203000b80da900560500c81041081d00c5100b441520b0b5200c3c5001046c0e0300d550f800b15054a0407030300011080d1b0b0101140a2100c0d482090b0044001c110000007020704140c3c8074000b50102c600600064042c880001302c260140c1000c00c6418010341c4c2c0310740200400540641a08028a240d00040b4400c6c100e4200c0007070185043ca080d5025650050098107041b00d007581008095449a12152854001c3c0380d00900203800840107184111080a030800c2a031a103441c24400c02e0260003020524420500700c2c03c00503036800540c00e4211003014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 519946672 1250 519945422 519945427
    0x5070b190f0c0206030f15150306150702060a02010e0609032107021e01020306182e030b0a0b1017011a131508130f0f0804031208010f12030212 63
    0x111007150b4440103884041d400400010500c200c418400b0f84407132250902e1141804446e489008100041e01c0c0354240ca1007a10040c004200f2502d010b0b0413034003a820111640b00e1270080107502040441c0c1100c0c42030300c090b035510042d010203208140b0040e13a010600b000918a440108000c415504c6152100300c280c81c4ea000d80020692070080240100307002030306c8000c00b40800004540c034040d41c070480d08a03009204035111566006950502680034040b05034212026882e0802e585000701d00c608641803c1055421000010490100d56903008800c031690100e4000b150806000100e5056191241000b04450b03160b952560b030100d074130781594000a0b0040d5a900d01009a0003140103904000041c8203810000080c41c4002030b40300c403072084827512005070558400c100303151303000403c1c58050030041d41da9030301d9000291446800160144640c0700d040c01c05440791110008c88403003401e90004134140030014071881601200c0f5200800050000c2007002015603030080d241d1404901c90034a00350b02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 519947922 1250 519946672 519946697
    0x4180b0a1e0b0729010305070906030b010e04021c0c052403060d0804081f23040602070204060e1801050a0c1704050106120c140604060e102a05070b19 66
    0x2050600000200e00c02e010300c1c142c2000c0100e54000d0b00c0030f100031521403003641c60000b00c9e880a405071000b1641c002204c40c129038070740a40c60040142c0104201d070301c43c400c0407400454460b103206404103280200c1651183c0ac0c20305c42407207400200c00700c1341003c00e8014041520341c0e00020003181c0e84400203035183c6808803100e03e0041541d0041e40c111081c9030140040f0001d44828000680d2084628198103101110701d0030300030b400141150400e070a19010400018010135100d0b0010001d0520203440098015599580e030742217482d040c0c8034895003805422000055030024021503411415072381081104180d9154054101d206030500b2800d05a201c0700000c061050a510200040c1a000031074881c103c201e00c0c00840030551400707120008054030f2020381e4181030000035a0103841107904e4000001450500f00004041030070400000c20140001c84600b0310611342034404410a800e01d42c0c5113107070a42c64645d04044184d00710110500c010701016801050102441610251500342129101e06 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 519949172 1250 519947922 519947933
    0x1805040b040f180510020304020d0f0f06050109020c0f0c0303160507050402070602070302070801060807050405150d050106050109090209060f071e050304091b021b01020304180b0a1e0b07 82
    0x80b04048050040c988050011400c0354614006440c070b2085064603280a00c2c0640c420490109035000b942103018000110000f84141002d00d401c81c0c0108040101001d031980e034442a5002600b0012a858010841c0d5400810130000d4a000e4001100039048031040704001c40e680c2e0046c0800c03c0b04842c2c0b120413510620034180405400340102410642d520041030524030060360000c04110014454000001141013040c4900003e4420f00800780540314503000c104400f425000e050600c15241500030f40301940c2d030f82070000301d20314852000443c03079525100000d0103200c2c0d1540700c0c0500703e0040240f240642e0302c4000326405035043e00202a100d420f603080014550703040150101808084850b40002c0c00700c000051700803034028240c28040060382041e4220540007000b251009a8855141c0c0080b000518460004a40041c411a41030a69840003003807814840072580b000c99658405403600e505003200701c00040c0104407070369001512900b0307009240319624803801e8000c00010840f4410440b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 519950422 1250 519949172 519949181
    0x30c0616110a150b040f020403080702210a0201030b060d090506060103151202040c0302090307060e0907051602012d0306150f0f030b0307030b0c030906091b0f0a03050105090304151805040b04 84
    0x105806c3c800c640700c03a103900c0e1045540e17110000036031146122102500f1955000c01c500f54141001e100540081c803601c1e4015409480014543c542c8140c0031301188543c01058402e240145000c4c0c0c0c0100503500701a0300140880b02a0001548080303409103042c005d0042c62110700c000c05a040d0380005009640792412402409064952541030186c0c10000038803541c407181d901541541101c05130b00a4482d0f900c2990b40b441025100c00c21491000020000341d802414001142005051b0f5008040c404e0a42584060a043c02d180c0200c0d5807004184041030050010150152007400c5c40310005204003805000c1030300e80307030400e420103855801c01022510180542c4004582c0501842c4860510101682042c2c0040b1550b1809218041c00144200310005071611090527018800e94032000f0f44040c000c0b2803204d4034249400c480d0a0f0b200100050091003140e01c10318091014540f9103040044485000740000003020801040c180d130b03d03403a441341a000500b01c1d50101e030300140340343d0708a0114007c0c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 519951672 1250 519950422 519950441
    0x6032104030615090e0703020a0504021c05010b0a030f050c040e0c160f030f0801031104020a050405030f0f160e011401020109020d050c0a090515040509030c0616110a150b04 76
    0x182080380c0024490302248450054130342c1c0314400d0040742c0c04650f9141c0d0b224500d00c406036201e501c0c588100300501f0b0550003084004100140e0703140e481c003060b00d0101076070f0003030344204002032000a070040c110354148078a510390102d540090100b400c2c00c9402c040c080c0103501800c92404003071130205440d008405c044070701612030740c004a084030f03001d401c20070780141c0c2c2800141c0101d901d00d402003040380d03c6010382034143d981c4003001480ca41061400c7c40000c0d08a002401c0900c04200f00c082007580d4100304058140b00b5a5004241c0d1444a0318002e040072145100c4510303045050909200e001921141c95054234010201c1d0308245950000403400750072091006034200c030701e403980c441c14010007080300da000240036215001e00980d64a007142c02c45a040760b00500c6205a50074025441c546a0000764100e256002140d0034414900d1803107080c40c5003520b040030f05d00c050400058403e6000f411028010394001d010b010411039648501541c0906c180c5100d1403e9078500945045e80c6e81c45e0312401e4034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 519952922 1250 519951672 519951683
    0x1804032001150e06010c060903021c11120d090203010609060302040b01050a0e1c0222051305490f0c020303032e06030f1518020d09080f0703080f0603210403 69
    0x2504280c09e01a490b1011080194031980300340403900c80c81c600542002c11301188601c002c001d000c0942c507110a180e00090001c0c01f06940b940d1480c805a07800740a2000a0420018001155455481000304840d51180024188101031000414a542048a500488809585c4482e20609000070b80b24220401540254402140500c40c2000c442000c1c0c0543c0782451014200026144c00e19034507046204482c005201c3d9100100c54050200d00c1628448a15084009a898015844500707415007001f148004080d900e001c10700103001c1d82c0100c669001056504080141542c940c022075202d01c00103001814190103801004400d041c2040900f40410110203042c4401d40c4801005026045039106141e9260908411310107001c00e0508600481e82c0302503034158203940d665960001380d003051010b0380b00181e40301154008030380c0d26001402c0ba610b4040c5015a50700781c924000e401e480300600342c20b1030b012195040003090346000406641c2c40340343c1e042d003808030907040c0502940f6101c2e0780c000500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 519954172 1250 519952922 519952931
    0x1e08070206030c0d0501091808071103030c15070503060f041817091807171306090605070201051003050304140d060c0201090b090a03021002091804032001150e06010c06 74
    0x840003000107840c030b40038135031814042a41c0c0d40e1448015100d4528642100c1241c0701902000600580003d1020500c250041c6010300140303030000703003160041000040c441d041051301244410b0b03282c51441e404401410f0090841c14a50049100b941415110a0003207503030704850140c5104002e21110b03120382c07000b01460521803640d800c0c0c00e19000300c0c00641c002d01e0b88208890b01e21003c1c9421134403403150b0b99640101d40301c13003200012044001901e41d60100e07000e030440c10046076040c0900310a96015080110700f90800c07010082c00c441c00100b128812001e0004140005000401100c1c00c03242c0c041641c148041048001a02140001c0802032000c0e141080c0c3d00d5025406402c02e117081030080c003a080d09507070b8030300c074540e15440d070700304000d006820a2402c2850322005038003904a0800c003403c000303130401d404028140750042c01d890a41c04564190603640140c440300c0503025208152070004d1100d940c100100c0c001c9850540039100007109560000350082c1d202c0c00d054a25280c01000510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 519955422 1250 519954172 519954181
    0x903010606050c010606050309060703091a09060103150c0903120509120d02071512051e09010e0d021614011e110c060933130503010c0c1e0807020603 66
    0x400303d0303001c07140c000f55550a040340060120b018a09407403058120401602a6a940d1201140200380440742203405860104038901d04081d0580030038810650760780285015411400c08610b52915088201e0626051082060304180c5c4160a101100d521048024001142050503915409100310890b00700c1d00314004440101400a204200400c1e550203036050951605480c019140c0c0111400c40420705450079002908600d5018aa10034070703500d4100c5050720040d45200000000b9640b11845a4554103c545014001d10403a8a102144e0006151088665905c02e0928030544240544100c406c4008d02d00303a40600d50606604c0940c9034903400680d8011001385c4080142c0d03014080038440d0032b60001142c14080201c41d007026000b000381e07001102c00c04c01c0405071071504480035240c0710300c01c0c4070300180f194040103001d002140c501c01d2030426003010141801c650307140500108004201c40c8200208002c0c3c5a107469607d00860040b1100a103410a04070034400c1100080d0045d00000400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 519956672 1250 519955422 519955427
    0x10050d0302010f0c02032a01060e04030507110913060b03030c010e0a050c0103020301210212030414090a050f010e09150c030411120304150c06050f060a0801060602030901140903010606 81
    0x8102c0119607050412131024040c008a82d04e0040022020056582c003803030744510071140515913080c00c44100007041c0a5160b40c10300118103801e440031004a01c01217000d4041003860300203200c0704c507802d4a4041c0c035440c008498841540c84d882c8003a200943d07440c20504551002c0c0116203c491b9104028403907401681516a515076003a80f003511076014020445160b036100303000300c9040b6551348010000828800100d00190b00034200c04a0340100c20b2030110810303500034400342c0b005000c60756a010f03c513007400c41400701c403800050410005a19200c2000341480c20403422506495070400e040d4034581c1c842e0000c524000154620320007001012041100b95084031000790f10551090340e40980c000a00818000030420161400b68103800910040c000d22840c403900c081e000b5018070300912210580d85602c400c542040c2c9501203810860000c021050824803901401800a01d008200d444d01d0141c000703450b0301540036070301c1c104035001c48100c2075400c41d0800d45075000001002000480e0390341402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 519957922 1250 519956672 519956681
    0x18010f14180d050a050d081608060303090a090e0c2b051002180f03030a080403050901031401030c05030625081305100c1b0b040605101802120f040203100510050d030201 74
    0x489442c4182200900c0e06c501c00d03020680036400030a41c10000c0c0c0d400480075509514001e000580520040c04444c4282e65074002b02c1c001445804000a2800c80200c90700d03041c01090088980a00d03086a00c080f01820010103061b845401600c0205a6685c80d240060800c0c00c0c1c0b4250120090010440e0003030322404c116000c44c00720003290b901b220b10003000c0a043d264001d00e00c4e1030010802020014012902950040800714030500d40000c0070341105448007803d40086e04240d4140125260601a606081004c9074106d042d01c00c080d20b070a0b640d442d40e00c075205221140c0100700a11600860300c6141c103d030500000c10391040588070100d021b0503449000744031200032003000415a150b10200480c0411700b1070105600001e18081e00d584540760031015000c0600b54031400c5c8200c100005140003161501c4030465040c690140e9103c00540071600d0940015040e400658201000d02006a50004100c19100c0c00c400c03000c0360640d2040c1c0e161080b240d03582e00c62604803010354585010180e06500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 519959172 1250 519957922 519957943
    0x120c04050307060801030b07030f0b0607050604020a09060302153f0c030c3108150c120403120b1e040e070f1701020d020f18010f14180d05 61
    0x2118000c80c0d0f00c0c0c900b1100341400b031101400c0208004085444284682c00103c081030000d500410310800403004550350754001101034409400001c00c0c0001c41c90040b0790381c0b004245c6910180203690643d0001081e0146d044820a00f0304400182c0951109031411648805084400034944904200040521183c4c407811382c00c10725017548000850b83c2a11b5403d4a000f104d00c3c0109500700144100310b921481008c1c04850903615031070085007014484512400042e01803107020300700203543c0039400c4807a00400b030007100303961406011201e103051b101c12402d5445501850b00103080d007c114601030081800891b60f542050407280543c900d901c1100001502460903141048902d522010f41500c940040c000c800e44170001110803c40203803c2c000048058104400061920f0b6500c1261030881c0e22030101d00304001c80c0400d500400c505101d82a1a1944007800c0000d030002c10710400400f9010b851310f054211103800308220020300c510307280b5407a4110000d0005206003140341070040d03a07846a0b14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 519960422 1250 519959172 519959179
    0x10151a0a0c17091014040512030d1109090112030c02280602010c0e040e07050906060c03040909020a060819020318060108061f06020a150f020d0c08090a03120b0105120c0405 76
    0x10072440c1d0b0920810041d094140b1140701740e802c3c2401c0c58204030507040c82a81c190110b20080c00391007050302003031140408901103000450341ea900c2e01024800d540c003051384804440b02c141441c0a01080e001401c2da0310301039045960303d62105e050000a102290303403042c5507020310300d4010080380c01c94055001740e2600c2040c0d154191110341c904104000c0c0ea00d40200300c08a500101c0c4104454100b4420307060f005080140007071700700301051407a5455900141c0c02a0880c58985441405504101a641024007003d14040071180351684180076442c00d2400b041c69000e42c000001180340b03020400c503000f0040f041080ea00613503950a2116070b280703425074010404051010940b2600540000c6210484515801a00540c0b0381d40d215501c203a400e0780e000d2120b0a40f2504001024441840180000e0641c0400011001040480104031500c018000325032503122010400100703401154181c02e4442e051004101d003c801c03801241e0f03034010204a040c5100888081c081c040e040d03500078000741e80058 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 519961672 1250 519960422 519960439
    0x15080c04060518070311030a0c0e04020a0e01080405070b04030602090f06070c03080a0201020d090f030212130902180301050f01031b1d04020a0b0c10151a0a0c1709 72
    0x54100411075150703100781640400700e03001400c685100b18081c0c503403200d1103080c00542096091014015603000302c80c40791200c2d47d103203180d00e8165044819414445001d0303c0850910950420151019086080f624140840d55000a00b0404100071034005440400689034440d6030700e02d44003000c3c4d0840700c840c5100c0c5103d140000c20b5414420240d42e00c40b504080014102451512121b4241e40b140125104554007000f004020131030b00c1c062481003900c07415003041c242103a82002420504126400c4110b03e40070001c581d03034407412109001c1507480000300103a40b51540045018070340d072182d9036aa095402c150401010300380c60003a06041300e000e00c84546100702c20210707042c40054140203030184e00c40100c00c99640013018070300c001e1740188050700099105490b0350306143c1980000103168440d6010b8420a000100c5600506100c00c0b03900c4e0080301122b04024440c6440032090140408414010460030744051140c400038080503003004031165501382c10141600e480d44030449036801001c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 519962922 1250 519961672 519961693
    0xc01020d05150913080c0105010e07031b2001090b0c07030f0e0108041e0b285106030606050306010e1c080c030403062301030b0a0f1508 60
    0xe1120b030000d03480c002c00014003a66580071030310010040030400d540640d418800580307007030000d02c1064045c10201c0c00e1782d50185040702004040e20031703003c400042c08080c00c0322902d07025044030740441e50384014211401c03e004c40840c1903006000480c0e010b081201c04100b80140c50004400803c2c2e824040e5550882c8a47c140783d040d580c0c21003682c030550003c1c0480000070080344400c000075040218144640851520320349130b03022807900580c4c05640e105040c070380484800d01c0e6040480024071003240180105c4030a40403880034543c020341c902d20f10f200400e03020001000c50300080c0038281c089076000000700700c241203a0b80700b001e250f000b0300c004680740079030110f1094090700950f171188405075070383c610742050103040c80400860b40c1548901c24018001d405c000407200d101500c001850840210f071624a54200241035a518004110800c1c4100d19514103200140708401e054030b8008803204034a40316a94540c0c0100505d01e641e188c00703880c00c5240d0302d4900c440c072803c07000c8809030011554404007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 519964028 1106 519962922 519962941
    0x327150c02103506040203041a0106080402041524050d11070b0a0b1c1707030c230703020d020604050409050d020106080a0804030b1b0c01020d05 64
    0x1075428001d0041080350300340f042e241038901c484985022601c09050741c84015102030700540d00040002c0a2040198074004030081c81e04036510039694540b0028101242964228403582c2858007900d401c0b500450080141c40d0261400c80144030030b19a007820780c0641408207801e22a00b07000e0317054140d10340d01c29548548a0030300550f40d42d21070352808070417416000b01070300201481c008580c900740e22590600ca40c000b160180221142a0500b0401d210081c9039404d00b150510004422080581c081c00c00d40009120300e8050b03200e200e46800000c40201c0128242c0310a0380500400c00c094680359010094541c009040c080c40e0035280c0c8081025145400c20640e01c69200d43e040d15009942489841e005090b0100640130200031561130f058184030300c0c4000b41026a244001c0340f14000070f02c001c6902c4012007a41203030381c0ca5150040703a0117904141c002c051258505400903c0105 = true := by decide +kernel

theorem cover : BRFrame.Cov 519784172 519964028 := by
  have h0 := BRFrame.cov_init 519784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 519784172 ≤ n) (h2 : n < 519964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
