-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2470
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:48:44.866545+00:00
-- url     : https://prove2.me/submissions/4e2e1523-55b9-43a7-9405-f730bb23366e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 444064748 ≤ n < 444244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 444065998 1250 444064748 444064757
    0x303060f061e0306290c010e0a050c0a03120c060b0604180f0b0d120306080105042108010b041205281e050601150201020d09060c090605030105060405060703020a080c0a0201 76
    0x402560450580384c0f0390192071207020401083e06200c0011002242c1c5403842c0c415810309180d92a0115030039940d85007845160f0f5070220054070305101040c84040031980b001c40d801804245546c0d607501514800071442d03010f10090030385000c1441826040380c0203180703005124a80d2076888560740880f0031040005618414900201425807015a00c1050308080b00206440307030682d0165940350122402000d55410591500740c00241d0100c2400350b01c0c040c5100381c000ca400034020016040d4001c0c4a030b1995070803c10411300401c030030300c04681290f05070b80400948a6820149080c6140703800c100c01c217401408034000400ba80840d107484144041d803803080070b07504003250f04082c00e02c1d04030a0001c07001e000364111600401003288810b2076440c040003203000150078201c02c03d00d00811506801d40c00d480458032811341000095100c0c4942c4082c04440c00c0c031600390b50420001c038859028500500340100c00016148040c98000c02c001e08100d070703002070310071b90322003a02f00f6164944c9076110f012404035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 444067248 1250 444065998 444066047
    0xe1e030d080106110111030f04050a0c0f1505031308090307030b040b0109060617060904020d0b180c1203180301111c0506010e0d020d03050c0d03020c07091e090303060f06 75
    0x200c041c09940e4000400301b500500f1a1918050a41c8104002d041152184a25400380001030300c0c1d140b0500080c0601080070409610b070981204840486007110010414100100140c1902e01d44140a4181d040b1b0076441d00c074580c060110740b6020650700060300001d15103040108000111441ca4161681e45905110940d503c5e20252815403a9222015000481c1c0340011418204030b0321aaa0290004140c5030b0316401e1622540358495040d99001049241c1d1404240541410407283d90004410350307070511001003143d10642c803402040001c0d071601c602c41320500801c2d0b45c25086450224010034015030b0352500c03910800c400d2550198100c280600707080001d1180d60085041d981c2c0004007512004803480c9690030040e0100e0b0004088081c040248070118491100308180030791822140c03801030707540c02a920607078900801c95201451803420b00741c5042c07600901c0000081c0402c0b4103403010030740c01e00d107180030f80c0070300020342240c40f03280c00c03c00d80010011f0b40401c2d0001d140c5074171045c24206 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 444068498 1250 444067248 444067277
    0xe0321091804020303120402040f050708040c051e09100510090f1d060409031202030709060905100c12021906140703090c06140f131e060e1e030d080106 67
    0x1070041c225400303981a0018807194544105d4010482d6000b4801400011140c0e040103200080759010744080b130000340a5020402007140b5000c003030026160442d001d1080300ca0030600c1031807031591011280c0c05884240080f40429000990b2403029101c020030300c0108801020008001c03800c00d205065505000365000a111410900325982860810368104034517038504060202400000e1821000c1003101c062100d802e0003a440598015186503590b11410b9107000c0000707155144541002c0e12800000c082c1203201500020b50b8100340c4e038820b80d018800b25980d40181d0604a6640350142b04541450340e0900f0083c0c140d204d01203a0540910807021a140d28100728106c5079414001003001c1c2d041d0006008aa00841031401480c0501e0f0089160a1030800d180c910f58003d4118281410082001445401b4040844046400d400907080c252a8030f0f003200204000c40040a40740960201d4006120700c2c1c01803542c00c03c201c86c0260841d80005802e5000410400091145000141c0040c604160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 444069748 1250 444068498 444068539
    0x1d100501050f1c2d050c0d0504020d0b04080307080708070e090903040504060f1511210d0912021c09031b0f0608010e0a09020108070e032109 62
    0x156041a56032034100701900d040c2001e50780c0f00c406034200703039242001d28081400060050740e075001e110903a460000400c4090541d12150000c01d60f900041c100410070810003204401d03113841110300d41d030115481d00c60b400410707510a4040707406021000031004002c2401807810086001c2c40c0305564540300d0b03680c1d0000c11941c060059035040c0c000f950f1030369403860324034002c29041d4000d403807102501d141965800005007290302c29400210304441400b030400c40b04038551800c41280181e4180040c1c00840c0c152020b464041c60101100011140414000801440c506071010720b06110810401c5200b2030a2003004200c4240c1d1901c01441750750700c1025103901e88028004843e03499200d2000541c00c0d5a203140b1400010710703005c95264851040010140001c0e01003070000c5c500e9850320211941828076880040c00005d01d0850118200004100103076405144281c0c0400c0c9442c00d10289486032000905103400e130004080307800050751203410041a40b40c002c0881210865000e00c018031100600007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 444070998 1250 444069748 444069781
    0x7080f28020d140304030309060609150311010203040b0f070302190503070c0506160305031305030a080a201206010e04021324020c1302120a09060506030609070902090d0209011d 78
    0x20f6084038148041400207019820106506220b03034004901103450703075050012100219450010070b200304004205100c46a1b41a507080c01080c0701552805003044184c0c0010311400c1c3c102400181c001503040d040c14030030300800e813140340c81041c00e296600e04c0d030404540c1c80c2c2202100351100d000390400015603282c41412103260503d5107640d60300b00740b0306482c00d4030305401c000c1c9550040201c107481c0c200040c5050008240e9084951a106c5650825040280444c1e5201d940b143c142404450801d4042400d0b50031790720012100c05c01c1810355556100101ca0070045403803540c0d00240040f91a0380b40e099040c2e490340a80f41c01c180740b84040d4141040d0303480030382403440c08c540140e0071010100440741881d5894051a4220010151078040749502c0314540c81301c2103980041d900c0d50b500a400400a40d40207454222108800030305850400d490a00d455000e60710551428a40c0020f19101940740c06024540750741c0c00800025042d0b9607500b240750b034040103a01421031b4110040000b190303003907503c40741c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 444072248 1250 444070998 444071027
    0xa020d051311010c060b030f0f07080601050307030809040b0405010e06240706090c0b030114040b030f06010605130902070b1f080a110127050f010302090607080f28020d 74
    0x30b0140b07844800040d280d900c1d049805580080c0c480203140e174a9102003044d207005000500c0140f00452034101c10a00b410314642060300c19800c140c00401a60342c0004916041d070307400c41580e0f07a94860007400a80107107503e04240d50810304002c00014148000c00006204e01404e85000ba8080e02003d03100d000402040c0c49001c510b0b00a0108102246550b40700e091518070990f2183c41c41c54840e011041d868000340d01810304000341106014540c1040e016030030342c9810540090840d0582d520320140c60b11414050482040004541d4020a41080700d41200401507400e0441da1351115040001400e6002c4801c06070a000c01503900780c401d0b200140280c00c891f2040c0142c00119501d42e41d106d0302c8000e500c0464100506401e0a0b06c020b0002c0030115400d001d100301621b1403130300d401c0511000d82803203807a07075050500c10300c0f802035241c85110072148100c0d8003480c41551142540c445c00424011640b00c00301c40311072031403070044140c0d00300c0c80c4501d4a200e5408462600c02200801ca40d13000c9203e120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 444073498 1250 444072248 444072263
    0x1140c1608090f03100903090e011d07050d1a04061e0e040f0c090506090f0c1b07030b0f0f09010618180b28060608070f03020903060a020d0513 63
    0x15040440c903108042e003469036000f0b00e12075150f00308000080c600000c1c40071a038499580e078000d00c3e00b0181c228901100800c030b40000c141240d89001240e41d6803c1d82442801c40d41030051001541491040d811540040d141920800180002c1d96074001c18115031822140128503003003020500b441e1032003000300e03031484c400030390002d6a050214140940700081c00032900490480015000078000f00461000341000d600001400d141c80c608001c10240054105480844c40308244002405400129443d0070740d007072403028a0140c4512003902e4661298406443c8405100a110004005094181c0907070441525640c0c241c03103040d28542260075510855400d5191070411041400c5590008070700c1480550802c11006482c2d151048000d604489003c02000c040d40c01c007184245051000c0e03030744010444100001402c00601030a003180140c801020b0002c5c218510746414031980440c1c441d041c0c05010707901c40d410036000c03803030103074000708002d0031000d06140004a410020081c032414607600801c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 444074748 1250 444073498 444073537
    0x90609061401050c0705041b02010f05060906010c030c170307180b181207030311120301080d051e1c06060806030703170f1204030207080a0309030602130801050901140c 74
    0x640309a8444c0c40c0c1e41a4074014090002015500c61150352020000e41410300d0a80360040002401c450070369101411072440c12080c4150b942303a0501c401e0748264282003550102c0840e00301030722041074002c3c0080807035191b044d2009a40012001840c010031154460740b4042d224001d00080318813990051020342401409034050521b00d08016a3301c0200c06064004101400d003841070500405400075000b00c2c040f007c110441c4001003100d43c80c0030848524803410340d410f0804090303c4148003601c000c01c1041c00300e44400a0a10b8264a0903184042e4501550303030740c0303c00c6c0e44500d8458201c0b242405540340c5480010020b000307034442031140304002c0180000074103582c0c40000c0c0c0040d2100c0c0a1302e0807410b21403111401101001000840d80d08811000c031807406181c02403030640c3d5a04050f685030822540f000000c0d07045074440c4180c13513220201603201c026500e000e06071540c00e80e11011140d0b007410b05001203ca0b065100301c2800c100803040143d5951007115905242c130900180402d041d40000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 444075998 1250 444074748 444074789
    0xa200307081b0d030e06130f12050f0c0f100c020303070c051608160803130311180f0925050d06060305011e141501050c0703021909060906 61
    0x380201042014030341018441020030484920b0003c41002d200d010a139a07240e071a01c5440200001c40e07000b40c1c107004c035503258400e66560907034101b40d510303004104422280c00a00341d40d008800341c030011000d5048940d1201032101d0740b02d135500f203122103490843c02910179002c0d24100a000c2c4c1001150142c00851454940b4a802c0f0b13414906048160740074000c0c01e03c5240780c510010450801059010b0041080b01c07908840000b054025074080080b41c2c0c0100494489019503442001c103c94001c01c5101e05d4000e10008584d403d40b03022070062040642508101d03100d481ca40660740100001d0044449004c020800700318500040b6030500116000141c003042103150107802c1d2812240f0610300440d1995803076071000c1c01d4502e186044412001d03e1409036030210a00d100781100514400c0c8003076028200381070014a203012844207641080380003c0d5a005070740003044000000d50b40901131500303040a14040054004860192661281c282040061280708500500d005e5400c1d80816513403108940 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 444077248 1250 444075998 444076013
    0x302030402060412050c0a09020a0e0d05070506030a09020406060f110a20040207080c010b030d020102040303090603050c070b18010b031612051006030c0302100f0819020c0a0501020a200307 83
    0x105001c545c00d00c03502840c0034060b1941d8242d07130000c1c018000d015845200c160b03406082c03099070b0640d4601603c102d007a40804a1130000700078003121416100320781e49032242d072010b20142c80742000c0650010304108000504036030105070702c1d428000e56a10500300340d10440e2025281c4181c40c1c005003009c03044090741d810161442d0b51104407030400400051606015135100750f41078110b0401441300e65511a1000e02a05003400342120220f0148021460123042d550f000d850a10765005810801d550b4000140d207500b411412260101d4102580c511645002c501d114407034001c610300c041143d4204100c451046c200012007418a40e01031501401040c1403c0040000303c010700d8042e40c60384a40000c801040780f842c854031026601940f1400700c0ea900398011700c504c0440c90101d010410a441c880790790140d03031094000341c000e0300c15800810580e482c4200c0308081c2c041d0303c103100c440e40200d44c030041c10000d0550040600c24600c0d15400002c890103000c20f200744041e0f00b01d075104d5170001c00080001402d43d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 444078498 1250 444077248 444077279
    0x201120b090610020a050106080a0b0108070602030313020103020c160f0504090521041e0504060e010b1e09130b031c0f0e220c11060603070b03040f0b0f07030c03020304020604 77
    0x107502c111003508140d910386034203581449d80004800d82244040c1000d201030409042c3c003400081c0002d1003d00c2ca0064001d503644001413a002d200e60710030a004007168803071b0301200d02c1010704100b114101c2d00a4a10440510424030500c4c0d0001041480010681401e0003951041038201024100c00c00d41c82c0180e0a80003040c040c0d205100300d040202080614524482e02427003030300815640700150601e01840f04642464114031a0200808010010700604208644000d40c004070821861490b40102c40c0c40342c05012a401d5201c000704004000c0381080c1e0340007044a01c001c82c00c036070503030940c0c0c200c030f010341c981d81c0c0312900004007955141c19072140620220b4402c10300c040c0c200c111108064213100d0a05104010013040180c4a14100d501c06038000e09040c1c07850300e400007401150600c0030000f551409584a1124103107000b100042c21702200429040304250031200010b03543c0b402d0800102895012920390340424a0610b813800d080d8802d10a607031040e5070241040d4a0036003003c094004800e034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 444079748 1250 444078498 444078529
    0x16210204051e0108030c15040c05011206180b0f090601140c0a15050f0f070203041e050301050c070506091501030204090807050a0302010608010624030203310201120b0906 75
    0x1e10038a681c2d400124200d040b4024140d26014580354840f8640b8582410004155000003403042c205100c0402c0c0410384800481d60f0900f001d49000000c0041c0001070440c1c4c2d4000340302c0d140400f0030140640c105402030481170f00111005010f16110004225581c181902c1c2140080c184046c0f92982604030001414400c3c5070034120307001300d801e81c2d0384c0007100707601300002c0100941c54405118812011040e0950480c0070440410854a06010002d58a0041d8443d40304041c04810100401004000e4050701074030000e002030005182000c24810194012041101c45100702c00002e0300c5c0368008268158040c0100c61214066441c42d02080080c294550040c0c58101041040100141042194070019842600041045894088a1341c00c442c4998011407282c9cbe400c604182c1010301f0040300a1000c00b00341001602d0f80c8480050381d070f0007c0d0180c40c3c00c07038000318540141101c000d882c44600241340700360b8444000905e4040c0b001e003907403543c005085d0000c8a50010030400d180480102101302c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 444080998 1250 444079748 444079771
    0x1502031309020a0806031f05061801030b010312110606060913021c0e031c0f0b0303072103020a0509120c0d240510030b040219081621020405 62
    0x445514108405080e622880c041d6900040c540e000c15041070690b640164110b024144c00700e003000170840640340c0000502c421b26600c03000281656902c0d0a0a0003c0c1e4591140c4c096540c2c603807502d00c0080c0400c3c0000d07201c08880750544a141c5102d88192880800d41c20b000e44200d0311a8401c1c09000d80080e42166408038060181030a14031117031014200d0000360588030f0503440795040c040411520600106145600108241174250a1803150181084880c00c0e0002e64407050f501440300030800c0300502541404005006801d001907040e00542400080b4124900c10420741800d60880c861850302d03201058052010800c146007801d055019085c28800b03585a810b00300000030b1a90300340200032542203122202c0d0703051441480140c0c006100c049141001541010415805d940240b844010842001d4500160464032a000c8003519007000c002c8001149840310141c1c0e450303d4401d240681a401c006000066001480340c05240361a0309840b212a00b102c29000d100c080c0c80e00418400811 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 444082248 1250 444080998 444081007
    0x4110d1415032b051b0c0406060e0315040501020408060c22050109120c0801020d0903170c091212070602030103060e0a0b150a120f0b07030e06070516050a0606080f16150203 76
    0x40a0707241c0705c41d80045420000e0282c020440c42000121440da8101d01e00b00a40d0914000c1c0c90744001540b1741001035030316640c07191a80c5a00e0007901a12a0360003c103071078010001400042081c80e00076102d204138140a003600886407146401c003c00e402c0c8146030000b04007039010041400c11035180340116000b507200d03402d451b88407100746099078860320310340700d03120356480111042c95403021245506605040e813550140c10003c19032aa00e001d0f42001e1031041c04074000010070501c003082511110300030a0300c0551620081d08004000790030900c4155141030404910204454011a110740340f80c1e407000307803149244c4a00341c00c0001d1082c81251907800c24041d038404110b1204c44070b00f0001c214410321220004e080281b410490014025211034249824030741800720740b0b40d01180c01c0c1c0e4400300d649482c03920358440d9180323401140071290000d4124007805142e10148405600a01c00391003caa084401004d80010415aa10901c12000038000c03c00d001c203020103c1200c0581c3c0d03529640d0710480381030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 444083498 1250 444082248 444082267
    0x7051e03160516060212040b090316030308010509130213021e030c0c0c0603010807150c02130c030c020d090311030703020306070314010902090f04110d1415032b05 72
    0x81e4458000580c0c40381d00c5001e82c41c440042c80500e000103040e140c405081480c1a0b9000060b4500072800b8000c0400401b02e8404070b191810420000307001c0b041074008400300d603642005800f098003801100e0140388400009860580841000300c82d60350b000c0c1c0814440c1214800c50402900082008440c4501c14088428010000070240d4000d503141c041c0d00d592060103038001807400d8507107181c9074010b00043c0b004101c1c100021030000d044945468060380d800440c5801100c68807001080254480c4000703049000070802d0303510000f11507809441c10010100000020790341c81c41001c00d0b1000180f92440180000340103c0540c80740c1d0600581119049920303940000d0505600b1103980c00001d80d40c1c504404401000a0380c80e0041c25940d10851904a881c0040750419210382076440c011b07502c441002c41c42d800c2d8642120044c021183c010000b05907140c00401c01103d00380c0c0d12580d1506d0740d0120060600c2c001c01c0b0464400380c004000c8022000c00000f50784d0407811456140c09000050244000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 444084748 1250 444083498 444083527
    0x21090501020f2106010206060603070c060b0616060605091014030f12070605130b0c030714040f180213060c030c08040905061003060308031305190b06130207051e03 72
    0x25070008500381e000040500b030454044020f4000c140904660140d0244075254840400300c90f04290340d498507191030420344c1450405449100c450030741120700055500c01c070f03410302035802c42d0080c0301e850103206007a41c41042117003a40d8140e45408000c00031174820002508841805045040c3c09002e907216030b9440d0144a0034140c92411540ca1614005803d5041002501c201c55001340050b40c4800075000c19215110788020042a01084120000128000740e000d1014506c403101206010b03581d070b41d1103a4581d50003508912404085801d0f1041c0712400b107116000fa64100e001c14030940d90840c1c50030b0412506d4140841007542804482ca02c1100030820b00e500500144c4803141020446044c503000380021030403907600001c10540b0340030051000581c07250449400440d800b0390140d04040780c0c180b0320f00b0702d4041300c0c04030305a206024281d0200f258005074980325203000c48103640800007161000041c5e104498000340950010b803882c2202c1e9242c00c4180da0004030f02c00807242418090b200400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 444085998 1250 444084748 444084757
    0xe0c220e0d0c15020307080c0a0c14030c100b03190804090e07060813020f041d03120106031503030c0204090f06050a06090c0905090c030702010e1b030d21090501020f 73
    0x7000649080315501c1482009a40c412001045640461075440e25690090950350081e0201010b10000256900030501c1000016601178109020243d07580c01700075815078a9101d0722860b001da0249504890310743e040e0380b0824005180280113070980e681012a02c0c640c000c001c40041743c501c00d041c400820010300602c00c0851070360700d410042101d582028405040001c0c010020f000c44141c2415074401038854a43ca43e00300354007640c0c08074003019000a41640c1080007070f2030301d0a40c84080b030f04006408004101904a80a41c0c8080040c080561449040d80303800340005808130704d406800f440181807544c07003c402c0318040c429030000079045507a14404d41c0d00a4901c0c030300140d2036540c24000402c031032081d480c07202a54100300d4482450a00403c00d200002040745a01d808040001100d650003074112955408005043d103801000c466901d42078441d0700751201e4001d00c140c104060446000e00880401090219240e001071081840c007140a00040c0d10111003c2d502844440d815580b25405407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 444087248 1250 444085998 444086023
    0x315051012050a02040f05040201200705100c060608030403030206040305030703110a020303090c0108011406091f18090c1d0102010f050114040f110906030709030c03080901030e0c220e 81
    0xc103100320310f41c010042518411000484110b29000600005070303085817400710300c00d9000b030003c4039010800000600b0300c0c00c2640711540086201c0303801d151265000160082291003550700f000030a4480641e240d49000314040107001d07a1052002c6408640108041c550110082c60302150000004100456903048141d118016034008400d001d01580b0074420009103010038684031480b90300d00740590b00342030b5030347d10818096040014610256194059440741d61040e40700b410f0206003102500401d05900484c4040800005a1000c101001c842c055514100c032107940701420740d4400c24000c2d803010b2410ba84241550b58425110505003540d0150074000c010410b4100309841801c01030100b030701c03080620a02c032035207046005500e049104094030102d5406483e142d80300c3d55407000944800e540342d000a04040d01560000003000740303020003458031810030f03a8240140e40030595413030f582d401501d4401c0e030301090764010710110b02600c1d101d22420403010000030800c6040c0130070300e1303003040b503080682e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 444088498 1250 444087248 444087253
    0x40b040f0f1202150709140117090610062d0e090114030c01050f0a0c08040b0c06180609060f0703110c07060306080d0e0d0606051018050109031505101205 68
    0x64888070f030148080442446041100e00b41458041e00051422009010308a541c21101c4c810344c800d43d1260800a2181c05000066465814950780b2940c4e1940c0c01c84010703101245912001c40c0d07540c840d0110f0800031002d21010481c20015a44a18101140d4900e000401c03120301550391042c0c0d140b001440c020480862842030302c80c51b800605040042d00d121450520008000034600e041c03100d4110303200a14580392035001c3c64081d240c4241d41d40301d507902c404204440031605080e952004243d041c01100807180e0041c1c0f141d02c824400d521008110b40c0039030785402c035400064143c584d0403661940540545000190903004401113a00741d0400a001140f84e8428903040c02070540501c030b64801350a41e90300910800480d440002d0901d0307500070720f260103128940085000c0118580244016100040020001c0e04101900801000301010144100b41503940c00040315409045c01506a9030080340a40300c001007150301501515000c1c1054030b4511500c4000901c0d401c90301c200b00a80d5208001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 444089748 1250 444088498 444088523
    0x9061407140d030b1c0506010b0f0405130606020d0e09190b040c1e210905011401030f02151e1605071d070e0901031122090209010b0c06040b040f0f 65
    0x181314a400c1c104280500754083c05d030091001c214006021411141e40450b0681e0b50000910f6481d06c5001d16484140c111301c000340100400c0c8125000181031741c05503030860340120000c1a007110881c003558012500407005d8404940d2030230b00200c4101c0024202140401c81402c184007040c03c03107d0f6414210f002600d1004040940d1403a80301d0900c25164525101030714084120050810000d00300341c000016a0b81d845002c108070342034100ca494070f007014804440640c3e590030a00036500c90071400328071901c070300c0068020201c00c040035070f5003424080001aa00d07003204c0e030090586030b024500c864216240301d203500d03000450400100c1c02928101189014103e80b40c0358100174038001910341024032481c5ca41c4100d242e201e0b5400c0c1411260841100d030f2929000e107000c80c02c08844451800c1a2250319002409034a0300340e0000c401483c4242c4418034241c0e81c610a4103200d0080e029442e070075810140114010030420800c06402c640070b44401c0b24456001d0b41c480e50180d0fa4030004840c000d85404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 444090998 1250 444089748 444089771
    0x61701060905060d05030318100f05011e06050a031a090a021213030206061302220602070503070807050f061605150f0702060f0c0d02040f09050709061407140d03 71
    0x505034110f81d083c0c1d281d910041d41580e40d141c803800001c041003100702d00060f0025414504004c00050458524010004e8441c0054982c0280409000fa6030140d410f40d1341c404100e014034101c4808882041c1e80e10f0303080c035201c01002c030054801001a1400340c0c1c10914050f00a5403251840d034020004810016507540382d407490741211513002030218440c0050030210401094002c00d009502c418100c407600d032403024501c18140203004841d4205c40788004c260034418032600000c0d86800ba41c1564081352950341d44c4808041c3d48001a0049514a17040620200880e00b00070b0501070403c00e0081c90541044405003a481e00b080340b508003034843c1e60010202e00071218900190036009800080e15828600c3d0802019541d02c00240c4030700c0058406c80700041d08a04071100340c8001d8540700d00299612070740d408001c5012130003030140c104071034906404a015140038030403079004c4070034a8603940c00100c0030b00442210b07500000b01c01d480c1c2c0a505802c4d1039250406001c242108ac0701d546000405007481e9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 444092248 1250 444090998 444091001
    0x102161a010e070c0807200307050a0b0415030603080c07030c0e130b0402040b0406060e03070902040f03140715032c10020306040e030301060807080907050d020d060617010609 77
    0x411000014480c0d400c018458a00303a6000158004418208441025030500c1c0c80b4240d4454100c02801c01040050f07441200b0718047c00d038000c000421821a004161940d0410110105d9032085031192402000704000d042c6d118200074070307418005d003000036100ba680d40714941142c0c4103500c0c46845400c0b40c0800e00c100440015030101411130b6138042e0109161060038182041c8550f5809010200c04c80e0020341150307110342002800e040e000c1c000b4000c00d56102d0300500681108c0150b80e101c2d000c0c1d00d00c00b00d038800003442031f0760480c1c04018440a51614540318510025210000c5078000c0c0202040441e00030188145015100c001d580e000a8407060800c40b510200c40003c1c04041031f480e036820361244181e00180504d400f8450f140010703501c1d10b65030000f0f401880700d49201d070385602010000181c0aa00290420700c1412152100200c1c2d41e11074103082e4490296029142d4020a00110030015040c050302c1025004d100303000005e5003544844288000d841c0010800c0d51a03911228107110040d0700707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 444093498 1250 444092248 444092273
    0x1012020f0d0b010929131b1106090f0705150c01020414030c100206060613050d081914030c07080c012d093305090a03031112040b0711010216 62
    0x1402e00c4503001e040303641982d01c3c1e4642e02444140310710426504a42c0140f0f0b16880001c021941f0f85544800c40124000542007020010294826004440010766940c0d804181c106201d00440f0142003418101020410828250561084251000e014041c07801009100400c09890f00000301184003240a080516061502c000c9074040c940c101b40400006400064840d0401401c441081d2508000030b800191902d095000a0340507506840e51000d101000700181088140c0300d14007041d1004a0101b0b5803c5040d918164002041c208001001d6031080c1c4040c040c0248256071540c41e01c14035140342c0c2e0030360b10340c108c81d059004414508109400c00305801520f00c04000301e801e0010300f2268859a261454018a4100402184541105582802d0080245418189030802460a103402800d41e00c00d9541011001b203440e101c00380b046501d010040da05000d0580d000341c50155039941e1070519910010f0210340500c48154500b04036600280090010203407408a41214808036052001c2020103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 444094748 1250 444093498 444093521
    0xd05010302130c121a0409060203070e0d030203030c0f0c0f0606040c02010606020703060f02040308070305091e2248021b01020a0c0b07020f04051012020f0d0b0109 72
    0x81c04501c010390039003184e0301c001600040000010340940301038219030900e008001140c3d1151802e030780641000302ca9409103008594541e0740f035031503004140030b10007591264400a80036a100744002140c910300100240354071010010a03a08103927941c86207d140004040d16181d081d004442001f490b0308043c8074003102040244028030100d4900a4080e44070313a89400003038029500c5245d1011401200c2c1c0442e03000f154081000c0f5030310010741c10000d02d60340011030041c2c42a40505a005612817039450a0b101d001c3c0028051002888011481c00710540b6600390b400440c2e0320350540481503103114911000c040e1031128a1b14a50004591b805800c124458222252015007003010610703641c002000c000c04401702d58010250312290300141d01c6c10b840d99000038000f5403200c0d00450800f403480c0203003403054070035a4901041d140344400c000517240b048406011501c5111020000c404010f0000f941c62030000d03000414100b00e8038007180e01501c0a00050710100b4200c4010403150207988504d0f0340242 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 444095998 1250 444094748 444094751
    0x12170a0201020307030506092406280201140c0a2d020c0a0806091c02120307120b010e061c11181207030507061119060f0b0607020907030c02030f0d0501030213 70
    0x2e03101c0b145051850040151150003082c02c610780029407503040c115080f20b44000c1c10b158100c2f40c1601c0701c00c9117420281c2c0d002c005500f058440822128009032160180c010a03044505001c0b01100865010005070402c05503100500b0300c0d200d00503d84c28006828004680c0600845604a018050303552007a038464682940460100080d4000c04a25400242c4041e102c44030b0780e07003481404a103440e50304a042800042d0001c24403203040c1e0881a0300305038003440c0005000507404040103560000c1898402a044442004110340050020040d0124030340300c00c000040c16030b03031102d6002c0f89412052042442c00312101c01c6500f185046c2131440caa06084400901c1071350f082d9500c05444070002c0c031400c0140201400c0803c04000280102608010903114000601d052414913602410131030000c594990700d0b10b6800741e03050501da0211544560013a00084068554160850041004442c14011070000744008802d07030705041c1c000d1148902c009000b050950441c01081807103001c104811f482c05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 444097248 1250 444095998 444096001
    0x1b04030503031810060f0e010602030a0f051c05010b0d06050d03050f0304021503160912020f090c040509040c030203060c07030f0e010e0a0f090e010902090112170a020102030703050609 81
    0xda001003101d902c5201440014450f07482e0322103191612640101025899007410800f203001500f0116007011a00a4074500382c0310390780d980080c3d07107a100f640072200008400075400082070f80a00000c2c05901c080c1000d144e201141c0141202c201d0b2400e0304620036145000424485000d40c6024090103410101e8400008030896038000d84a403148441d503100d041c00102c001400c0d0342e00c0c00384440d5480c804244240e641e1414074600001115680320f40c1011489800c004030f441c4823900d00781d503542e0740c0c0a00300111440c003031400c00046040051071503040040c20000030134281c64143d0f449010364840c4086120725400c5104160514200500b030004101c02840400c0c003080c0d20400c0180d1001160174160034600c10100100c2c0d41e080541016500040b20003070010f2407181280002c02152840b0500b006801c590000d06802c1c1c84a15402944c400d10580051002c08184c50b0904203091040918559441c4440c10b841d00d60f810a401c0000583d60100420030220382500078103900580464005656 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 444098498 1250 444097248 444097253
    0x203011a010215060d06021209010e01183f02060105190504020306010c02091305011802310612061802060406050a03020c03071b170d05030613060b031b0403 69
    0xa690243e0001455502020f000c11041e480310b040b0328a0083d0011000d650396000e00c0c8051001c0308085d105100349600e0b00c2c010014251041c03160642c0b013092002a10107492540d2114142500400004c82000784001605c074010a5000d0b007005c0c107a0407800f80140c114042d2903000e410031405a000c40d0141266101c3c0d5214274440150281c2070707810031039006840c2d842e200012100c4020032030000350404400400e2020386444290a00d028900c80c0d0000c2c081511117400c00007244d020400000c0d006008203443c282030300140843d084c1c0d88031420354203040342c0c2c0083c3c440400743e5131954041039008440b04055020f100c2103002d00c41c3c1040ba14891610b4055050b03010810b41c0c42140304090421030045442010544290119007c5403601c20403681c50755400e00b0640555a4840007502104012500006034201e031049002c0c0c9500d607a1000d400d84680d1120309440380d50008080340d5000705140c00710190066644618805000c1c2c0c844039989900d860b0a01d00100c0c039204000100006042c0000c200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 444099748 1250 444098498 444098503
    0x106060206060d060b1518150909061c030503100b03090705010509030102070606030c1412150c0f0a08070f0e03100f02071e050c0109120308061302160203011a0102 72
    0xc010b2015100c40300620001e00f010750091507600030035544800c2c031460030b01046251401616050038000d58101a850707803141000070400d0070300c04d00e01d0107010a015226003450040c10b0964800401340405144444c0c0540c0a45402d0784038030f0880c003181000c0180320420203000c2004001d8222a01c0c03280c44c4d4100301aa00765101c800b8403440b8100070740002ca032452501c2c00e406954407075074005414080c158891500c10240340c12402010810110b100c024030341c130700c0d12601030a4480499806052903014105000104920040038185103c804002c60009907001d040200101d05c5a59140c202301c0c1000c00b001803d50500b14288000c2107402c4212005a68012602050300d0140100001e601e403070f0241e041019003da550081c005541c00a0380d010744684030f402020300d1520400c151041648910010350703924a260044a107001640700c20400001d02814000c0c1d006070f002000100320041008852040c1c0c1e00c40100b001c81d040000c0f02180c00c40c142405813150b51202c881e107110740b080a4100003903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 444100998 1250 444099748 444099751
    0x90315160915021c020f0f030d0b040507090308070503040b03040b07091520011b020a05060601050319091a01140f060717160b070c1407030b1311090124020106060206 73
    0x30313000400352100c0700e4600030410413005000304d6064440420400b490300d0784940144038018100d42c100b031080943da160901c00c1c0d9106510b2034450488071030564072008110340008804860340e02c030410001c201c180c892400b6500c114400c00c00704203103140652004000b000c41d41d00008403948108034038006a03412191003030340f1005482c0380740b02d030b00041d913a29405480790a11401030721034940f00307402e00241e010481d1640d03540140200c488503280c3c040111034030302c000ca030080000284a2405402a1401d4105161ba0b90241d50002180e000340c101200c200d01d800c0c0e01c4401c9c500d007001c082c0e9103e400c10090340090310300d0440b046420819561240750512200b9000149140e00002d80808021403003a40031207010342160b11101c0e2032a24007005806007424040546986035844400b8a9015000600320180c96010b102c0208a44880c00d10422050900b41c045403904084c0a410f180c545405c40b03114000c08044000100701d40005242440080c0d160750140116410700b01305100356500028810b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 444102248 1250 444100998 444101023
    0x80d14041509051903030c020f0f0c0f0f040f0507021b060703030b0607050102041503110a022a0405130201030b0102152d09160f03020307030809031516091502 70
    0x2c10002d03514909241011001e010008110342d400c0c0309002031541c158007003032000600d81c00711031705158803000707090ba50b40c501045000507601c2046010140d0905001c0c0e5529110044c0c00c030080410854009001d882841040d0103085a90b0020405c40070360402005170000c0e28649000541d18140c404500d0910461b20003605042c2c0310440c145c002e0321040304450045030400001c40d11282c0310b006c4403510744525054180007034200003502c00d0541c1c801040ba4148007040e0000c0055141811446601c03920007107495880d0003950000402ca0789540c01030620544480004260701c00103840094200d84640000e1030442d8021000d41014041521885400040741d50010712000610b00e0840046c035094501c24960011490a102032000d00041d41e002d03d800d0401c45029550712030880400d03100c0e4520010b036065010140030004100508010403004002a0560b000c0c9901031400011205080da50320b2009628003403010710350b9030302500f002c016280b179100001c070301d1f602014000d6440b82e801007032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 444103498 1250 444102248 444102251
    0x181306030b04080307091206020409050f0606180a0b0d050a0510031a040203010207120c2f06070f02040603080703171e06030703021c060f020313120c050a080d140415 73
    0x11817501405841c4201c01030100d2580c403c8240454684040070350080d2245081284c14000030644000c50050b40070b200f800007515640c10f04c26081803800703450b9103ca80640c0c1080f0300100105514080344010010000031010100c0c50b801c00e04c2c030110403210014040500071400c2d54081c00000c42440b011440800c8403820b8148540703d80c00003900a109448004050341c03035400c01c80408a800c403041c0100540100e1515040c201c0541e02c5414900e05405078a07003903201408140c9561030590068049107001e08100581040954045800c5031901d8106854803000469501d080650190000702850038603002c600903800c0c400994040d40501c1d845091000141c40c0000700703035071000c100d03503401542c00a0074400c803d40800c0d02106070b2000480143c60030f070f042942101c0c900c40f1500880c0c0c050662200700280c00f0200c2e85485840603038940c0d0b41410062104502c0c404903600304040e20240d4003a00c0c007666200c1c0004040c904881d0171001d030780c044841c640c04201c0890203c43c002d2003281c544000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 444104748 1250 444103498 444103501
    0x2505010e06031b030a06030201080601030509030a0311070b010902091513051005090d08090114040f03030f020f060108100c110703150209031c11060405030313030302090402181306030b040803 84
    0x20b025022880c1d110070f1041c0407070080b040200a10003a004002124001c0e00c500b045c43d15980b0044095a408807181340041d842048000c2e0090701c00d0f4003201c08a4001d22150341000141e03541c40000400a90081c000542c010800084a01d040e8039181d50f4a0b800c4500c0d1441c0101000070b20551040034401c003807084204088400e0f545000742d0496041400c01080360642500a00e881000d035040040c0740c81c0020f0365004961002e014032030848054800b20500b00c28210706c1c41e5411194950285000011800b8005904102038020425203010344002001742513000d101000c0d50089455615101041104820140c4446c0380c0104a030f0302500e81221003045282c0b5003c001c080a88103560344550148240a5140e50396031644c81c0c0c00d404036070300ba071710220311201c1504da180d99a1f809960241054000704082003113401c4441c060300301c042c440e04001d8100040900050f00f00d8120028904258648028181407464107210303060310258001020043c5a0a64448200000e4000e0000300388480000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 444105998 1250 444104748 444104761
    0x40f030f0309021306090606030204030507030b062214280c031d030304020f031218130e06060a0602010c0e0613031e0b0601140d05040614092505010e0603 68
    0x4009004094001e8100c07040e44da0a50180d000410403445011402458203501081440c428007c45080345d0f000802482c1250440e110601040c2010300300075800703501a10903504c0094440440103080a20300c000142c00e1801800c00440454020000344010728800d4100d0708641340031800505120344400001500001441c0039001002011001002185580618070301e1100c00401944101d200303864800a10300944145a6030709140200313044000e40610019082d2074040540c8805000010700040450341c08588800480f900d205c41c460842c0c005204002032400c090141c0c80040003544002c005200310020300401180002c0c80c0c3c04d214080000e192500e01d48070352800d1000c0c5800c0320b84002181c2c505190003408003860f40c8100c900f1907030300d000a10030350301848030000b01c072100d884120300d40100552408020034004000b202c05a542c0c400c40e42158280001c1907100700f6400008040f0300601c440a46201090003905100070700c2c01e64402d110503640080c00301e18071081601d2040d20b903207031034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 444107248 1250 444105998 444106001
    0x6050a050a030513020303270307030314030c0f131403060f010501110a06050703050403090801021303151409010f0b0f0303070215041203120b01020d140d0618061d040f030f03 77
    0x8413001c0d601d40310206000d00d810786d1202d035015403c2a080e035407043d403844c000241526a0483d00c4050f01290b450480103042c100a00011740d84404201a150700c1e20166000440707040c2c011034641001c01202c2d110a01c1449102505c0c06464002100140071500e0134a1401c2a2580140a441e04200c81c5890301102882c0400c001109168010001d00242c54a14030007001420115806d4001070b501c01030003c3c10070010702c2101d071800c41e11259021498250746500304080e0083c10b11000c00c3d903a910f203c0400d120b4060095001c1c0d50041c2c00400d001d850780047e10142d840c0958060310a810803407001c8002d0394004100c23a5130590503540c0051041e030b9000303c60081c0c000e60f41301d400c0c90916002882d081560240503804d148160380410000781c0f51031001240e5910b944480000481d4000008170440200440a0700c1c4400c2e00d0400841c140d074032507003c102e056640c0c000081d9110740f251800d1042015148562251200d120441e0045280944804108502c0c0400280900040581c11203805100c4d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 444108498 1250 444107248 444107281
    0x105062d01051c050a0b01140a120506180a0605130c0c0f03020708120c0d0504180902030c0315010e012411160e0a14011202090a02071a09010606050a050a0305 70
    0x1000c2c4100900d183c03075451740d0080c10031440c80350300040304002c2a003840780412050b00c085143c00c0c0e8440300c014000c1d00080c0020b0201401c01c95101f01042010f00f0101480ca0040303125810b105000b15910703203042d041c00041c07100400360440c06170030551200c641a03440120220030710340040300b10f01d01103d1420140e04001c0a600070f8000c0e400395409441031040c1031030007070101d01030b00d000301e03201c86000d40b4044403d405140694a09421b005102141c070800d203030403000b0100d00040566002d132843c040064540550b00d046140e030070b07040c40010401003400c0401c00c0d00500c40c143d05000e82e10381c4201c082e1094403040d60950180006003c0b00407042204014035400341e0285070010b440c0315241d08000b041420200c888020351781c01d041101043c0391800301d60904907004088554280d5405500b082180880101480f850a50920042020903601d121448001407500180151410700408035401e449403504224103100c820085044074544c00801c82d00c00048030301d40083ca0752144448510000c15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 444109748 1250 444108498 444108547
    0xd03032c0a0b060607122006070c03090506160308100e0a052215020c0c03100204030b010b0f1206030a020d03030219080103170306061b0105062d0105 66
    0x18104030320920600001180360500d80100304101d100c0d90ba032000c01c0043e10403014000c02d203c00c501d0b0107043da50b0064110082d01c0c01d501c180d00d442c2070109070803103141c008100e9042c0c0004504010307800034960450000c0e07014007402e8074040c1c5424100c0c001c0c601008607482c0000c041007808000143c000b4483d03000140644002103001c1c03032505019000001600040e42d403124900b800c00c010040e505e00d022045d405207a80064000510040c042c1079000a4202c040012791502801c0030080d040d680601207000c4d1406001340041c1c455003107041500c03030902c1c141c02c43d0901e140204801e000701c0e01058162100c0303420038041e4003455601c4034003103070901d542e0b202c000350071440d002004000c00d0b400da00136121045da4003110240625980380212214038003848090080a41b1403e001c505004c0007000b1680b00d0005484286001500310900a03114030466040362941d540d001840b546107400c2e001246000300c44c0301100300c0c40305c0302c2141e4151001514052814000e00107108a10950b21084c900354010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 444110998 1250 444109748 444109811
    0x70f0f05031519090f0c0306150e040203100503070e07141204060903030b1804020f040c0e0409030201091b06081308090d02040609020d02040e01060305090a06050702030412060c0905010203090d0303 87
    0x850081c00c85c0150904520800110b0b080c0140400c103080d122014400420203591210440710501040c00000c0d80080d080d89100b403140907011480c1d88041141c2c1004210001d04500c145c5480300004003401031540400e50302c16010821030340103d1440d845250019007121000986800d6860240d0080010521050700900800c00096141c0d01140c42c10740302d1030003562583c0c070080300042044212000b8400c4c002c08a005858406100e040c1944542c840358400e00000802200ca40c860170160680d20780b501c04071140414050101641c001d40c00380c1c0000c070542005003034108030b03951010703180a0101854090003c001c0b4500c195a15074000c0c070000c1941035402c664034561414101d020794000c0c081e14411260820000075850702c40c2c412140720350000303006065420b103503548131409004060000c0045110503c4041502c41e07090822040c154851080005c85419080010348551801e0b8031480c159042403290307024a80703c0074080d0701069494900000d00741e032030702e0024440c00d1900501e0701d5150b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 444112248 1250 444110998 444111011
    0x10507061802040b040b150705010221040311011103010b031e01062012270415090506090906150303040b0c0102030108070f080c0108130506070f0f0503151909 70
    0x11030075858407405007030090350103100321540f000901081e61030b180341e8607422443c2003c1109051a0207409807100c54850340000d07141c050300c2030ba04006800c03030280c102d12041091090004050300b2600101d581250040203200315003482c901100a401305214560304a0f2000001540300d40940386151000700d444580c0c003c0035610344800030003442100f07900c00368001c4006407024a90400280328818817259070b01c01d80c40c1c2000440d01501030202c5036007503005248041e003c400140c0d600c0c000c03041c3e0f080d80311840c01d2a41d0f191259100039100007402c254050100c03507050020f00100410b040da03001800e10b00100001709c0c030401080c1f451045034443c0c034002a000c0743e0090f0490040d002181224110400c6030300d1240c690980b003401c0840e500c80c1c25155030040340e802d4035030b500640304e10354001c06924124401c0180b98071a40e0810740100c40610001d8254949050841e81040080d80800b2540c6400c0341146080c0840c05401401420414031400c40e80300c1c0460040003148414000d030802103010b0090 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 444113498 1250 444112248 444112271
    0xc0a1502031e1e0c0303011202010903120819090201020c0f0102150a02031506181509090a0902010906050703090e090f0307031d04110a080a0225060b0102070f031101050706 76
    0x5a8102d40c900c488090340102031580e03206285810b5a40003039990b0055846d591900340d00003442140b8000032814460081400000701d95a095a92801c5019444d0718040d131510021100c28035001004004103645001d080a0261343d00003244d103041c4000382c44040101c0d07038480050f49881c0d4190a40c02580404004001c44290710380c01940c02007070300c07010745810411002d042024a0040180b0303c20b5030000040000740c0ca01e0210581c550501d0f400d400ca0b2b19008135040482c0c401c580486a0055260705c4414900c11540e101070100e008008500d031150a26810740c0c0c0c010f102c000e0911541e080c00c6180f00100780320810034800c16015150390804c41b55600482e2a000e400c450314034900800f001260360840342c00c0d082502814202680c51240203240020201e4195002c5c000a40b09a103115402d2210704842a0104074540d1240c1000b03034041c81d480b4691a01d0000d50340b00442c054119004840108050001c142c0200c064075805181a10805807a2700100c8071030042c101c01a100a0410030a10030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 444114748 1250 444113498 444113557
    0x206060108041b0b09031608060a020a030f0f090c050a21080c2d0705150307020705190504110903120c0f060a090302100c02071e0302040207110108090c0a150203 71
    0x170144400d4090341c0340c0180900084446444138030649003207400a0000881c0b440140e070041491950b5070400180254400301400308540c0f005900a640c0c50380c0d0025a410301c034207070704464010328044070107070a01818040448400344038041c50080ea0b0030045406820054150281c6a000e032a40c0704889103030a0b0202519100e10708034030124500c1582d10040e08807a080031401006941018040e0113480841103d405d40303036400141028114001c5103c0843c003036890182d5003035031070b0703c400e00c4040007401c00003040b0894601ca0010900a0001c00114000c0d480120f60400e0020405c01000c1d100c90103090030300e090200d0507401c03d0060142c030042084030b40131a404503071128002c2e400c4440c0c005030501c4d10403c440c200c0c429807026a10182c02008500540a48220881d01c0000d00c045503560301d81c0464141d0f0007001c02101e8510802140c0c90303403943e0001000750312403ca100200b1500c401c160200b191482240203074600103821b80000d82c10030b8020000c90700810050034068003180b41d4100b6642 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 444115998 1250 444114748 444114757
    0x1503021e03100906030f02010516050d030e010b010206191e05100f1e0e060102030705031201080607020d1e17191b08060f12030a0315060f0206060108041b0b 69
    0x40a160b42c544001c02c0c0354503070744103e00540c1d034440c0310071800c0d80f07850b0015566900034034000c090114128403c000000d5041c0260350020100e0748020030368201c46510142500c588400f2903045520880030802d00c000d07a031607480f511000030000092101403400b208446e40b03445943da03000450070001400104021390419000725442c40700c07003010154981d843d0341501a450b00d40f858540c65840c60034031410721a24005034000c0790500442e882d11002e07a0b00c050071b5030072407a050b503000e9076220f0040210032824070005602000030703c05803407030a2245001410b10880041c806020384060b06118104501642e41e00b250f590252041d0303403030752a14030011494034111130b20303004034503007420a9070750300c10700d1412401c001e011151550320b01a45c070b100500c05506da0113400395074060ba003202e05004140c001e0000389801c1c04c06e40e0700420400d001744612450161654010800c0101ca001ca0003201d540c0447c03541c0d0061000d1805502c15183c60400c50390002e400300d048020808070150000740000420010b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 444117248 1250 444115998 444116011
    0x20423040f0902060712020c030a0c2303060f0601030605120a03020d1b080f070b0430050d0e0c040f020414031615050c060f0103060f05101503021e03 66
    0x90104120241c0504140c44200e00000c2d00f12100744114000038180800c0d420f503020040c4111855500700b01d001074039140300d807a02030341c442c0820710042c803c4c4031101d24100912039030704003010080c0c0300d0303840031950f0750304004c14036503068481c040801c4440c1c1c401e070002e0005040082c1a40c013030f000c000701e601d038441c1c680d20011405889061000b6080354040c80950200d01c071410700d1b020032407489480e1407160313a2007802e05000700c0c10100f00200000e070591060500950064219030048041603840721562941052406c0c264510303050a500e845030f2250032182c1c03138806c0003c0462440000031245140050301018a980241800182000840c955008e0400c90342c01403a0941e440070740340c007031540b5010703040198610750130401028040c0000300480301c0c1c62444949015403401603006402814180d055468011408001d40100b040c07140300c0c050607402c041d00340313402c12250502c0b220129403000b07284248501600c1904406070f04c0c5009034142ca0088803200c68405040c002c900000851f5071044406 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 444118498 1250 444117248 444117251
    0x3010e0a05010602190507090504050a0b1b040302100c0c150306051210090f0602031e0f070f0f021e0606010323010b0f192a0309120602042304 63
    0x540501107030194604030b45154024180460041c03200313403412411803030140d455105051001886140714400e0380c0c45035000398003501c90108540b038002042113015066030000c040450982102c0240f207012141100c1d812280d04001000c4844282d8011100f03060150811215100024007030122402e00070001c01315690130803005c2d86030307010401441c004a01080c2954051070f00c40000a10a81c0024092400340002c031a025400d0343d1400c081e60700c105c0700605500714512114400551811400741c218290590324501458000700040c01150380d500702000b004001141d49100d20300a10501100d583c1d0000051a00c3c05c11550b400d0741e4182c1aa185030000307291688a001c003116840350700c04007440803214104603034a0401c4540a940001300300d81c205800400001005042d065800c0070a990700c0d0700c1d42e060f0a560303007105029409100480f000061146a01113002aa20600040c10384a8440c940b440d4040350f820904001d0003950010803003421100d42800d2100130390206040080c1c400c950 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 444119748 1250 444118498 444118501
    0xf2701080105011a1e091c0c0b2511040932030414180405060403030f02040605040611030c12220b040b0702011701090f0b040c0e060307020a0f0803010e 67
    0x4440711000c4524066581d41d000340014100201c0350101c0a100401081540c1d0410140800088510030510340042c2070610107980c40741003001803699a001051020030150070204174512109a400b081442b0725070704828806281e0402104040903460000d0140081001486918011540c0041c8588007002c0c2e007026060180c8800b110072981c807442250b1f6005e1403d0a1070500051020388280b01015032120072001c4c0440d0722402004840e1045005200400003400c043c20b0150072500ba50300e40d5000355004003c2400351a802c00c08440440d421440c060035481c100981142c1103014490f060348060281190246030080007401030140c907600380340100940c0780b20300754071214000c1501c92019908000d0004003c50071760340000c0d109042c01070602d285a03812100c3e084900c00c409801c10042d6030354420014003100480c3c412800150f200b9074040011040ca5070024291485490700355200f40800800101c00b24824041d154075550b02c141114003a021910305580c1e00e81090003103403803c022000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 444120998 1250 444119748 444119759
    0x30c0819091e121104050406020904050a09080406140702090c090315061804020315090f010b0301020913180501090602071103160302060c070e04060b0306071d0f270108010501 77
    0x8005a402d4000410080c03002d2801106809040075050203540640c0030141c4007000380c45034003420340300b6486a2801a5101c1849042100720340d40070b01407804240ca000300c0c0500043c1c05030111801d4480a007042c01e4041022510a02e151040c0d4100a402c80c08160602c04c4a80038000a4803000c6000c40c1600c440c02d41482c0e1680c4921012602c0941c40400345070318a001c2084c408209070407500160075107034030081600030000401d200b51040f0100d13a00680820340e4400017031044040d50801140207618252036540095645035005001d00b41903552070000c00841d441280503001d0542c0e120300280001381c06424100700a420103102942e802e1103802d0821b600340780100c2c9040c9407100b02d2070140d2044d400c54003072201030f070400c001c01c1f0358501c02c081000c80e4100d103104906110ba8801c00020860b81c0f500004d15042a0015110205020141500e203038000c8220f810358511031800d0315481c890300c02c410300240710000c452a241e02542140405080b00e6001184641c0c161950074000f0310103a40e951 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 444122248 1250 444120998 444121019
    0x5030912070b01051809031204060f0914070b0408071e030203070902090103050105090403080f1906030b010521030307271409010803190302130f120303060b03010b070609030c081909 80
    0x45681405135082041002100894008d5003904207000f818002a41551a09948200d460484040c1d0304040c012510a59244040000d4070207440c0141c0e01e0b07824146440f101c25580d45283c018060b000c2d00424034810300e122461110b05c01150003c040304c042503a10360b48180203600001c45140001d0420001080b80e080418549001d5075055580c00700795600c0309491031b141d0401426420341091810a400c2005000c1d02840014600035842090254501000c003e220501400d068200140c11280000720a0012041d40e5000155007000980040001d9216407070b01008001d201a07000310400104031500000c0048050030760a450f00403590740c940040b40e0b503a00400003201c0c21010750550040440e031203500501005510000344604141d01c030041020805000e80020b016060304041d803000f40343d814000c4000600058015a14550401403031403018032030204007802403602d0303503007503001c0610406000184642120581e612011012111010461045940f100003003c880c070118440340039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 444123498 1250 444122248 444122251
    0x50f070806010f300c02070503010b04060f051203070c09050a0c1106070513050901080a031b1214090a060201020d0b0414060919020d060f061b0305030912070b010518 73
    0x1910390150360503400e140c9001d11440785031000c0070101d0381034442080003420b000d1740c5030580c0160003400b019030600003414211410b4040052180b414001d042001c0d18110710b0403415204192010000d240c074440711585544100ca10041c81c030f18500c0c20015800b060396008a004e41341d0b0000a22070028115401c4440b1620440c10001a4109001080005005500130a107604170aa0100b40690351040005c038040000d0b1300503201c5802140ca000200b42c0c1c171044480c004407543c81d080c0d041b80d03416110b580d489000500c4d074000f441000401e4981000c5040142d030640400200f00c0b1481c10744420000f0f010303401035110b02c460242081c850170780f1482c20f8011402501d0f6511018422179813030600b081002c14000d003180403d14518049031503040d0990006090482d403126001c0b5515280c56001c95201d1540d9001c4820008814440060000c5600c000d100e8241c02d4a0304940700d0b00d403028a01d09100380003415213003550001403450104061113100c1d81c12501e082303802415481f12440c85d24581c000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 444124748 1250 444123498 444123527
    0x11060406091a1b0a110303161803030903030c0f0f030903030f02120d0b0f09070c0b060a0503030d2004060305010e011202060418150905180d020d0c020310050f07080601 74
    0xb01411845010b14000042c0c520800207280840c0c215617000c5019083d03038001e5469425503600c606e42d681440c2e0300312040200009101d5841c546203851610300801ca500b007030000030100207010f815a01401001307602401c0c02a00b01030b400525615503c0c028200018500c000c6000c900380c03d0b003010070517001051241d03100003031541c214500302204021100400b50806107991258100413815060b8803258911071249081c0e8407003540a43c45402c15046281c0000c00082c8100e8003154207100359100802661007410101c3c1c404940048207074000d001c54940d07613441055846003c18005159030349900b107a81250a90090100c659132240c48283c3ca0740c0c1c0c1c40c50081e401c103108000401c0b10704000180601c0380d01d14802c00081d4624222540c213800c074030a50011400303544420a004055aa242d451043c00c11502c00400031500c1d0810041e4544c0c00900456050028000c01503080d03407070900110200720702c1060f0802907032501c01c41c0500b0300002510000d0015900400150b81940641d40050b000701c0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 444125998 1250 444124748 444124771
    0x606031506030703080715021c110f0a03150503030f0901090f08030f2b0902030139030204030203030c031b0336030a080d0b2b0311060406091a 63
    0x14210f480710310a90f84806802c50b414120751101601c0da5110744003421a444886d41d2002c00c4108621800c0150b2b0962506088001e4003005002e101c1041c04040312070a04860070007203003034000c94010300381000541d0302c6990903001c0060586038200c00c4034010205400c013602d4580744540c46580f1002940c0b020f0207071001a41c000c1000720650240070003c1c0c00340c0d08503500c0f0140c0308440c0d6001c46410304c1c21100018803160f1100f80090841c0f50a00400c5000c0d004040303c0400902040c3e6000081580e0442d040c00303203030b21a002e0350400e41c442c4e01210040c1d9006002c580d40c40740c040f00341596a80c03002151440c1e214146540300c60b00031000c0120341000003c0d4458141820402d049440d4001812a45140c0d03446491001c4190780c41c18080e00c41500c4c01a0421078a4001d101030103020740304041c01803441090014a112111050400ea14180803030240c9042010103151030b0554818000b1000c12000e480b0f214100010809a5000705a07040d10034200107842c122004c640806414059584a0311035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 444127248 1250 444125998 444126013
    0xc0928050103110603061c12110c03060705090d050703140c09010e1f031a0a0e16031e0f08030106230a1121090a290d060314060603150603 61
    0x2d01e00100550741011004080080c0c40324202c00440704c0c1f0300e080c542180c400300800b00075160396070030215800001d400c0301c0140220461490029841341c03c010412418080089450302403074803200d24001c1800da0013002c440b00c15443c2d0400801950300b59803c410f00744126403a00b0300e81d00f0984003031030488603003400041594a850075884020342c5422142c440c4591031000003c042041c40d841340d6104441000f40c143d8604248040300103582031958081d9442d8011190300c032140d88000c01d0403088a030800c2c001000b1811441007046500242100540041404030642091100c4003000318126040c83d2a40701c00140903180c04229034502d0803110400d40f03024020b80c41140d0240c2c144844c8401c002d030540d6140d45a07002d000c12844905010361010b850003151181c0541411f40c2c659000c2c2120f4519010320040e1100103842c400c1c212410315641407004103907000d0030ba01681000c005140e200034244440110b5000441c0c1e078040403540c0e54030030311640400321007080070001c4580c02540f0203400341840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 444128498 1250 444127248 444127283
    0x90f0609230321090a232106100905010501021501050913050f0a0501110f19031104060e031b1c02013c1403060d03020c0928050103 58
    0x5044900e014107425004181459488200c4802c0390b118400032003c0107901c03800000d0074403114802c0380e003080412024202c400aaa445180580030f10010200c4558040a03441d80c0707a0f00000d0312030b600d410024441e20301802101c1d46581c9903c010780d410807100700101c3c0c0e42e4200490341c2e0720443c9000302e070b1140414018045030519120721580100b003900101c0b206055980c546142001c12036a100705c4d0f03080101c2c07890420030700380240304444802400140c01e2101862103401c42d0701c50700c41c0074101000160316000c07059009420540040c4910014a600c56684410150202e1a007000c954401d00940340380002d140d0455801b0400b42e1000b030700520030341281034101c04401094031000da050024030076860300e122842c6569a80c6c1c000d0144040010810482c0801900000e61420034081c00705c41ea100b030b8912054002a03a82c0400125044044120300d07090507420240301141035030300b1002c00d104211403802e8903120410400c3e400300304002041c201262040071104280401001050203100801c40b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 444129748 1250 444128498 444128549
    0xc01050a0e0303070507030309140306093007081c0507140307050f0304081b0303040b06091302060d050907060509090c03060f12100c08070f080414030a090f0609 71
    0x1c00e1080982140d02c1c004803516118a0880c19500881c002894210148500080302d14400c01100c2c00350010402810100740c0d5544402c800a00b41001032440d40c3c01c065074100c4040c005d030003801c0d002910355640f840c505210415074000c10920340550516588030030401040c0c80740754480c000302e550300850a089403034080060381c40a012401040f4090051145d070018500055010b1480b030f14401740d44052051401040d96004860010190400c2c000c1002140c0501e00341548410120b9000b5481d950358408a03020481c03420019400030b0000c9400c064030003459000601486000c0308507100c4a030b42d498102ca10b4402d0300c0d20300d0f82101020b404900e02140d180c0195800040043ca03038201e64040b07802203000c5440c141644c803581d0f4400d01c10034001c21054400d9900b040d500e450460500d181a860141c01d0011460701030003000381210016050040080700d0402250800041d00c2e40c60000c1d040003001002140250034032066611030008070580260340c02c4080328082c000d414421030400c4400d12 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 444130998 1250 444129748 444129767
    0x201b06060d260f04090204030c050a05060f0309010f09050303070e03061605160822090603021c020d051603151a060c070801150905060a05010207090b06090a0303080601020607020c01050a 82
    0xa101680a2200420f4080700c14040c001410906800503122445c5061101451350503074040d81c0540c25805042c000c588236142140c2088243c1c03400d503603480d2902c00c042401465038001411000c0d280100c0e00c020840c0c0400210b0284841d60b417203c02e21400d10301010b49443c801e840b4401c0860340c4100309503000740248003808100b41c803000d0710520820f10703441d200915800782c00f50100b4001d0f240642a40424440700b45805040c423120208a01c40c2594041814019403010b480e0207141481304160031991120404d402c81c941c410203542c41100c0381807040455014a0004880c4007803000c0c1c12510415051040b450700c84100300952404010120038405a9488080030702c00f140039200700400d40c00401d01a1004012a9401513300107150803400d00890344080c007458801c40070803004018a130b900203810b80075207041c2c0d0700c009503500e1170388000f561a00c101ca4041c1e80100c0b00310000000e1540001d4900c0c4900c90a800b0f9892030340e00c440003203846070420101c05d4003180c014054502a00e00c110941e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 444132248 1250 444130998 444131063
    0x14010f050c161a040f03081303050a05030901200306040612080d0903020a061b030605030109020108190207150c1119030806120303090705040b0a05030709201b06060d 73
    0x10f0b409996003107085401840d0803034055801c0c0c0b00c074442c0e00d010107500004040d4489850403215130300c80450f5800810741d104400700142005800701c04940d0f00b8400703500c40b202c580300da480004122150044000c03002e800c00c940ca43d102c3c900e0000009641400c0d080d20101040d40100d15a00c0c1c02440c42d0a14010100300c10290114400d9a4154000692074841c00141c02079a0450800041d1900c0f03000301a2051038001d2800ba90420f684400140d8102509075009000141072840440d016002d4200a003ea91405400c444040206000d5280d03194003280c07902e95141d070790611214043c80c2c8079648200c41c02d65207c0e4410000c005102081c414500b2a4001100520a000080c07825a0451541d08150354114094022030300c100030928140c411138080300c00a88080d5001441d04000a40b100c005100310000c060300c6101d0084805080d090420852510405240d2200001080e88045804181d44600a4424880402d082e072821080c02030189502044644084203651040502c0c010082e001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 444133498 1250 444132248 444132263
    0x6140c0120030108010b011b0b1824011703030a0908090a031b05190909060b0405010e0703051b071202010f0c02032a0c2b14010f050c16 60
    0x500d140c11480d0240050701d01102040e00d490b54100441e241c2103881d1928000d040c8003403402c001c14080321501c0c0d802c5060b500038885440139500c030340c82c1c1141d90003240c440100324044e00b60680e039810f6169400b10880e41d011140703a01c0d540e0322410102844403002c60002142d600600000c2c5842c0c0f580d03003099400c244690301c1e00c1e080242010100da907086285c0c0003201c4411039003816000c4444005034010042604849540d2400e81981107000210090f0048504845e120f00c03001c41030012580001c803149001601c01c02140d0f03076401640480c0b90041c2c4503940000d08150110f14070240038101084800c1c5132582a5140c007245940d074040c000d0041a490003955254804000f1580652090302c1050400340c000e10b681e2200c07544030b40d0031a254009104802c1c1014101070000010004104144d05000d0b2854105041c04d5586a4030b168440a903c0240e207002408a104000f0307150600e107240d00c54132000344010041407198509548048854200f607040a000b4407045001c429503420a090190f0750 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 444134748 1250 444133498 444133511
    0x30e030724180f06120c0801061107030206030406150b0f090105210f07030e0304451d1c0305100504060902090108070f0527102706140c01 61
    0x82d8100303800d4440d4410105111402420048070707400680d9000415000241041008581c140c081e20015043c081d0b41e04102d010050209140741c02c1200101440d0014001522843d0516007207014001045000624074020302000a0b0050070000380e5100400b040340e502e0820b40700100440b010780013011a00c2c41c0103184031500190515a0030454051a44401d1040d600c1c6481100a4159003480145080d0340c1e00420040200402401c10b00c034000300510003a1952090345040c22903451242c074440795042184101e49003183c4810b45c0660440b90010741400c08084140ac040c0d81c0302c0040050540c042d200710185a901d00d4400d07800f5541c001054001c1303170043c949400106040340e070150003116403540d00250b030100660f0040245644210607160240d00b4582d444c2004100b80604201081c011480030080400c0d040010400280394001419044000d0350a010040c03410241030f21084a000700b002e11140e40075003160341c1c0002d8601d00d48031034010055485002007254800e03101100d07030313540c0c580 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 444135998 1250 444134748 444134777
    0xc030605190312110303060d0515090601081606120903020102040f0e0402040609090f080f0904051e0106030203010602280f030903050c0d0f020112110a0309030e030724 74
    0xd886200c55802040c8a001400c510f4180340501841d039165081c00741e014111400c1d04030000c12039a00000a40d00050300c401d01b840c01611300610b0710b044003145100e440030000620350018400e03048030b04907401c940328180301d4150f8903044080d601038040016541c0c403034144481c0c1540c010042d194420700c00185003e030f80c0c041110000119800014440751078001348815450580101000303402200010490b48009599180c2e00e800141c0c0e00a00300d00c004a03c9800405403401959441840500180124688000394504e100408508c1c1d14075000400300210b421842482507a050b00e1280e0010401d000c011150700700107030401450741108429002d115000140c280ca0a000b000b4400e84402e00d91608600c1c00e28140400081800e00800004440401080b180d14404a201d5020b09000703104982c210040c1c1c018004081040b082a2000110f4101c1543d056010104030340c0250b41d041d02a80e4041c080684440541c484c0c44940c922841c0200521170f0b51054a1421490314140110341d0b46208 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 444137248 1250 444135998 444136009
    0x9110405070302041a0a0c02190b03040f03021b0919020d0c08071b02060d090510050403081e0c0901270626131509020409080a030c0f02060a0c030605 66
    0x1c8070072000194010404210345540f103000400e0b403000d83c032191400c1000004000b4a030b8194510081d1184d901e14002d403052354002d141da40050020034002c2503580c641402d05051080c49100220b00501c112801200703505004146e23004100c0c0300410f01030103510b0b44080c901d090f205080b04107041e15030802c81c0c8603082c00c1c10701c2890f1810489446402e00c0d4a03180c440038000c24031381c604548111044d14146001607650074101c50118051010000390007000741800d6280107080605803205525000c20f000034550860515403040b040c41c45210243d030380030a1603090ba080c0640e8010110401030003100c0b03296028407482c68101a00d110001038490150501c603405007500c0d4021800706508008200e003007980740342558851000721300c2402c11810001c1e4400f4450302d10b00c6000e041c01c29145031104c00003040e600a6900035400510602c000080360400c0d0b40351303600ca043c80002103072404502c9000d16020b02895088015245c002d41220760f03034030750b004028201d40001d40040542d03c80c00803c0e1795965 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 444138498 1250 444137248 444137251
    0xa030f0207050706090e011a030406060b03041112030c060f040303022a120315150f0a09080d080702100b010e09070f020709020906161104060305030a02151909110405 73
    0x8100503d00c440c43c005000d0103050f80ba800000051403601d0042c0702d0116070020101d034207143e001309545e4a07516410442c0c001c01c1140c1000790000c000006020034003081484600d00303180100c6040464499481e9819528030070802481050703001413002420031845032041c981e116002c0e040141c9480402e501d40003410201d00820201d451441800d00003c51f0704000485841c41e00084061a5080488190a8590031404040d10505010420302d500206c1207051703c80d01d403140701189481d0005000c000c0d000407194095541280304041002d505944030740d0f503160142440d5009401903001c03204211028040c0845070a051000242d524480c503260040320b01c0c4120181d80d40c60350202e03042d560090030100c10b50701000b03044d03005001d06061541d811088403010030b000c6a40103400303402850004100b400c0e1701501544980350a1000040c802c0100040c03a04000d00e5083c1d9080008101c02841500d106039041c0d0a00d40d41c0078003040303802d0800da2180e0802d6000301c034070410329801d0714001010b4a40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 444139748 1250 444138498 444138503
    0x31509010e0f06030118020609130c051b0307121d101d0301050403020c210f0d11030a08040f1401050a02041e0e0403140409112109120a030f0207 64
    0x80071410800d8400d80c10a1058100100710000d200c000c5507445007542d681c10300b400180c8210000100c0682a5542940301d070303a0030a040c0001d12100c5170303030180589142c0000c49917000b6a505580200b61000000c4201d0b60401e6001040310b1003014007910490301801140c03605235201191512086060780c80410b04000b50b0840c1c1e82d61510383e42c601c0c03424002c0b4201044424000d0b81002c1c2800006074000ca55039040440586030405032100c010001918604100c0b44013940c0e004003c40800c1c05e01c03012404d4900d40401e9203a40811540c06503206650380310301c8c00240001085800032400041038050002441401102150704507041101c00600310740065034065000c80c0c0c009010420b0503000c02008003001c4004000e5006c4500d40480082d0120000b0002030402a54081891480c182c2c4400d4a02070724811504001d0000c1d20085601d840d40144207140c1441d219000d0705130354030f040b03001c1980704100f5240509515810b80c16000310540000f0600c001f03264031541a010510540c0c40a80b14450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 444140998 1250 444139748 444139769
    0x3030408011814030a0e010e061e030603061038120f01080705060d020c120309010603031e120f290a0603141609050a060e0307060e0307030803150901 66
    0x200d10385031040c400c5200c80c00f03090041e0000c0c0680740d51650002003108080c0420b003082c46108501d800056034074800d241d5004652114a1070022000d00c0e02c0000e1481400c1c207604894464a030707101290031000840c4075000450304541407440701012980800b120a03800701011a048089120544080b0381111000c04c04075002d00041050301042500024018000540a403820030b00f09008a04244620081d10081c11303000508250b45034000c1000d4800311031050203140e00c0f03041106044e8003030b110510054001038800030200c0700001400c0d5500d044107081d07880b035080c05140b0080303035009401520380c2d1841c0986e40300f80301520030100e442e40ca9a08d10b0300810644801010408000816801d5080141010301d0607410240c107003a040030080e00b0a1a000800c0181994058201c4040c030300354200541040042000080094109203565030042048099540c11520b03044102c801d880100e41566050340484410000710343c1444c029030f0030803000441c1e44000c11056000c50103800e000e034000320010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 444142248 1250 444140998 444141041
    0xe19171602010e09012d050a1e1401090603330602060a020901230f07030503090c120d030b010302090402120106090e060d030302091f0e01020709090b150303040801 72
    0x560b40402c903c02100740450741c082c019410a100c2c1154046801034205050140d1030302541130f003005440d2000200b1004180c40c000940781c2404201002da65a03014100b041c010740701041002c88640407100b071580603512901c00d2031410104501401c070700700425004c10b154030b00d108071300c03001e031292101c5020200d002291044d00c0c0c000020324000004040107280792060008842d283c6c2c0c01100321a00c1c51500010744032030f4452540c005a80e109281480d06c1d2444001445000c01d904003001d075208074689010344071200d0326002801240d1000d804458a0754114070103088415010341c1c4082000c240c1850010304014640d4040344c1280d0068070340700c00c0010413600400415610001c280050103c1c41c41c09891400d0a201041c01410800320090a05801280e014a582c0f5100f042031300100e4044038800141c0030901010703001c1354100810a0050191400200303031210203001c0c081d58242d00003070310034080c3d503114900c1602d1030f400c0380301d141d15010030080001d4140d002d01a8404003034840e0001c4602 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 444143498 1250 444142248 444142253
    0x2070f0305131e1e180b120607320d05090d0203040605041503020906160b0601110309040903140c1b010e030d0f0905180109050601030e191716 63
    0x480829031055482d030f0b200c0c508040001041c40e000104a03010b44521940400300001007014803c03554001014107002c0c0b408000c2c03c0c603043d41104429120582c0e4891342102443d0240d5100d12040f0740e400d01052101c445c14610b2020705800694600c0c0304009903480d10500c80d44009640d02010208441940f10414020720500c2400710324202911800214685483e02c00080c00900543c07007010b042c03d40c4159040502400303901220307a40040141019940d03103110103d0141d070014104203480640d00d01c400a019075018058940f26460068015400c000540c000c0202400140c80120100f10300344100b038103501c884401510780904140080e000301600604100c1841066000003070412500220b0382aa50314041001c405402c201d1601802e020084801601c10074900d07032240380c02019941103e0040700d01c51070345a0681e0950074050080d40c540500441c10703110f0001040510740c1107800e494022032483c01020b020030380302e000000c2e0300c45445080d10086070407003842d481d500001440d40508 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 444144748 1250 444143498 444143527
    0x50f10110c1011010605181305031c090c0b040f05040b03071205071505030105061c09020a180b040b030607110a0507030b0915190b03010b12010b09100506030a0b0402070f0305 77
    0x1030036060b02c0307c5181e000d00c4481a014168084c148002c5048800c501c0c0d828000c041c0112860340d803c0914000404480031100401040e103000103039080034400e000450340b8140382c0c2c00c8400725104034001030780b17242c1450200002412851800c42e0700d8450010001210310b16081d000304014041c02c060240103182281143c01c2d50010070320081009410070042c00159501d800752192650900c011490140b2400300c24001000a900041d50042e058172001a2810038201d142c050080c0342c50080c0700c048080e0702408152642c210000c0da26070040c2c2d00045140b072203801040c0e0f504660f50212848040039403116414038030240c01c1a200c0c07480050400800a10803c0b030b4100d00c0c00e0740d040c4001c0d2482e02801d1114821071603044010354036140c0c409105070343d909410007440c1c51001070440901030681c90600307000381480c441940c010410000080c000c10140455202180e0003e080300b89903a4414075141c005000241026601c26030134803504022900d80d40c6040703c211301c00d0b12615500d030040e07050303e034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 444145998 1250 444144748 444144761
    0x81005031b0d3005121302040b0312040f0603090c290f0909011d0103030e0613090c0201050c0f0301030b0402060d0504141204120209041403030a02070c050f10110c101101 75
    0x9003440005c00c141c00700a180c0c0a851944030444400500006c8168400035000c4c0480f944d030690305104004042000102d6880204115221803074041e403a540d942c1d005030305031600c00034040e0038052004010085038040b004d842c0c04000c840b60708150420380e1600188201d4101c3d003025883c0f050040784130307107413810262445409000c0c40c0038101160310501c1d01041a40754140401030402c5a0032000116079200ca0055401c034800204000400079183c500000c014020301121500540c20000401c50400101c82221440d10220040a140da0b0031501c0c2c415000c040648102c0c1c112400b0030a1680b06800c6d0b00c1043e011703620078049000c4a8107202016032a0004c50078003403606203c100000c014840020f042e142081d5811f4990f65115561400e01c60003c122102c0341c040c0d80d0000004103d5582101c1d801062480d1285405080841c0c0380d0042c020115400b100854200891200710803d0a005025080c1003488900844121010710302c085001515040c0146000c10b06d04ac0131056544000c1c003518 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 444147248 1250 444145998 444146093
    0xc020405010e060607110105190e030d050405010c0b10050a03030206040c2c041406040506090706140a121121180c01050c0109060615081005031b0d 65
    0x319400d20703c002412500c600040140010103191a107802c0e0b9002d081524610b0f03003001c000700d04041c010800a4400103100e00054440c1c0a11403403038a40500610544058600c186d4840508022a9480710a41c1801902d40d90300582450000100d581c0c4601142d80518800d07405000326042034502710310201c103076030003e40d12000654200c0c9a04400d01c400b5080407011805840283d0302c941c1060074402c121032044c0f030458002d00701000140000010814090072010f0b046421f41940d4441c100d489a2020728044012902040b4124402d03214460030301c24070340e00800001d00c80080020f41407003640110101c180c00c41c05008008174490109940c46d92100c103a1050584035000c0d400f046440f504005900350500c0800f00c0d01c408200000d41c04aa9181d911103401c0015035110b1038204603201d03070282c0301d40010305144002201c41b81c07041010030031144054002d088409462020541c20016612855000030b04042010040703a80c00a5201c4600c49400c407c0b682215500d95444088041a014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 444148498 1250 444147248 444147269
    0x13031b05011b02060702060408010b1201020a0e040509190320120403080a05070c0303050306040e03070507060e06120c03010501020c01090e0c0d090b040506090d020a0b04080c0c0604060c02040501 86
    0x4121903600301ca02100403a1460310b500b03202c0181440014200d00464a02940261001c540880ca110055114510400c070490300c0e8101c003c495241c15003030b4414030341c0706d00003e035007954003906034185900840e030050800004d0b01c100e040f83c0202a10905d08122307043c4d00148800e80d603010450742b40056504c02c400c241002d0f080c0e50b040411454001c0c422480020070700400000c9803844c040c850010303551059481003e6541c210b03580c1c20010181e4100f51103041c4110720b030800c454562800007084442e0b065001020b042348915040095805d121144030140c0c010f00704008180c0d908403000c811510607100ca08800f501d80d414a4002460004802d05240c103000da034407014031074031031000410f580c088020114580d46200086a000c06004804030050401a9143c148800c0060120300301d44189003680454805040700c0300c0890b99030354080c1c0c02816001240d070114006c511042d00900250524030111400d40355068003042c115805a8003c500003600040d1500441c07426001e01801492505070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 444149748 1250 444148498 444148553
    0x2071719110f1b0109080d08010f050607050604170918010812070c0e07051e120a0506010c03050f04120c060807020c01050d020a17070e040609180308040c0b1303 71
    0x800c0e50f640d22100c0301c650b0003030000f08104801e0383c49051020007502c005426030703181d49200341003e00302100a00a045901084660109c1c00d828010700391109943c000380202680d807119141c10082d03100307505500c0301e010010050800980c4130b09aa04071074503d010154582d0b58900080d040c1442401e00b20242107480030890b1601007121484007030191f81288080c0302d819200c82800303990610581c410143c40c0b0103d01180d04820204130043d00620a000990741895920900c0b40812200200d88003800702d15980f0204010a200d074024042c0310061720000c918181d100d074461710102022030002c8600001d8a0818061503070320084c01c130340000c0700e80000d100740f4915a0028100f03001e810740e4903560f9580410010103403031056010340c5400c040341081c180181003110000b0456001c0c00710311400b460420750001241070091080c84000100743c041581e03501030f25a0225331428001e0000e552419100304041000c0145000404030141c0c1c01074003a20b0240f0b50b02d07194118040740440009500d0900e003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 444150998 1250 444149748 444149773
    0x206091c081f0608090c0a0602070b070206120c0a0f020712020906010309060507020c040b0a030206090f060d0204180608150a02031b040803090405160c060207171911 73
    0x80c5408008240c509100019503103228041050703000385400201590209070001444580120403640182c00080c1510042d002d03038818450f01102e103100d0080182c1c4040300410942782c1050150080c50320007420640750078034203004e1200a400c00d441d1805c03000c00000d018118140c22203482e0468030a0b50018290161600740c006000f01d40040e4040d02802c0340d040052182da11a600402035544e02440801207800c2c00c02d4001d5841c452404050f000b54036202c4028064a44810104200d81d4002d091914068041007030000c0503000660541e0032403418400b02e600894a030024001604441c00c8040c0c2d02000c0d20707040c0c4144c0f6244d031b1002c3e002d40c0085420152443c1c3c2001c4665001c01d850f4030250b0742c0e071101c00340000b1406841d2820305078941c002c1b902041e5501d000c03008128508080303500f07100f1600c031101c42c480114008600040490b44c0e003800d0f03c0005110b40c020b0541540101411742440503880760755131895014007031045a0344030301d0340c041c81401e0300300c085e11440e480850000c00c4200040c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 444152248 1250 444150998 444151033
    0x604180812070c1203091707050c0f031b1201150e06090105150a082a03040506180a1101170a0902040e010c020a0f060b121005070c03120c0909020316020609 69
    0x11840c02c01056203640c01030060000f102681f2000d00c8000c10a2640c0e070400d801d0540d20b400d08402d030b030340c0300d100700c6c408a130700911f0300244202c0e190300b00c8003c0030308240c480010040c0c02d14503026161615500c660310500d40c450074251505c02071902d4202107001d80307001c0c8104015100140c024a202e40100f44550401d003207900c00740c50340740102e4203100b0180c0d1a00f40005480000849a04c02e080c1207401004040504540203140030714416170480e552034076150601100114000c101c1c1445034021419280411448100c41e03030407500604100d4030100440560700c51800e02150080a200e85881c41074003141803030b103d03000c0705440c00802003100c4c81070294029102e10424401818070705107000040103000301c0b940000c110340c80051801d00b40c100f0098040d51109503001604610341c0c03403e0300291007903000e032410400d00365050755907050300f404543c1084e0090a040c0301c40740800000480100c0d004074113100541c096241c0303005090b21071444040003880d1001c001c117030103503581002e144901501c101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 444153498 1250 444152248 444152273
    0x90806060a1410141c0b0d02030c21060a0603120309110d0212031210081209120114180106140d080903030f0a0e010906020307020a0e0604180812070c 66
    0x1121442140101c3c040101c0b0f030b10481540100c81d52000088218418030101410310542c11032010a02580d015902000f82610700d1040c0070b9015044810003910503d000402c14000700c1441a5070160310000d86009483d03c1c4041b980140c555a40388418824007008054090180c1c60b80d14040c4041c0d451691070912440508403d0380c055000c000c0716900715912030340d50750100c40240b400c43c0e0702d03500303c086001c140200a644010100051030000700707503a080441d8036a807620008845603e010303051800d00c00310540000e15580c403950781e140c1c0c013600c00550a245601811040000481210300d56510360b0031161658010742c0504050402d01c200780e101c40054100c200d400085003034484503001c020904510400c640e00c58070400010f010a500b030380144003088010402e0386d40c51007031500e0748800d03a45c91140e00030107540810704000c00c12241c0e0740040c0ad550f00c0540a071000c11010306a45002100d5910480100c03003859000c61501c9030703484114809548111180303041c9118034803d40740c4a122418 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 444154748 1250 444153498 444153539
    0xf0203120a1713150b04061206020414120a0b150d11040c05040e15030a05060118050c0a0507021003060b040b0316080613020a090506030f09010c1115090f01060303090806060a 77
    0x4548417610216904c0c0da0140000305800a00d103150401580f40400003035109008212066062007401c64450400071500d984000d01c20300100b42c0c03c06c003130715203d2421500034480c19125075030741840d00c100d498220010020034031a8000407517620840d0100006d07908a80003d0080140c10b00007045101400c181c0d0a4000c501c0c0c0d90450f014a411a02007414007008440203019403003500c000041034000c442c080c1d0300481a018042180b0f48030702c180003041d0b00c02d107401100020f406104003005841e00b880400c075280c03c50b042c000b0b60345549100c07400301034000c1c1d48100395001d004402c0295031074410003003090030b01103498009100c4c54030703c00040301d098800c00e00c07500b8207070302043c0c00c40311a001315415005008002d24081d241e2400ca101710b140380300d00b110a552a54200200419041d002e40070314020a2500030241000300321000400311800002400c1c12807522a0303a103030807040c00080c070495003c1d40c040d50f43c5042c075504000300d2a00d00000034004601480b90714504101d82010b1f001d1003103507400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 444155998 1250 444154748 444154751
    0x10e10170a02070c0b07060b0307030807061505090a0e1b09070c05160b0c0f060c030606090301090f030801030b012909060910020705010311070c030f0203120a171315 73
    0xc54408584000b400f60742e200411890795284007080d649519000352416a11890003030014450340c07014035895000f070344401410180b0034412040081d149402401c0114102da80c40012990348ea400208555011f50340754030400c3d62403024542c40310060280c9403800ba00c010351005601143c00c04240414002030110003042803402e07444d000c00c10b00380850012250700440f0240102e85031100d9451981c050b803100c0c074541c07083c0d22004040d03010209201e4403030841003403000e04590729802405550307409031000d036074507550707030000540010024090440000d0190303940228540c158540349110800682092200a00e000c400c210788001d40080a1a0b20700c0c2030a01c55250b902d070201040003400307400c044542c0071040401d20317808280d000441c01c04584003680d0601c156000d0003060003c0348280c62019106a4910a041c07021036000d50303101200900c00741c1100d1000e20107000710800c0c4d4102503680d00000c0c0b0b40e000d20940854100e55082c1d000501000c1c901007510842d43c40c00301d151411110000c845 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 444157248 1250 444155998 444156001
    0x30f060f040305130602070501120b030d11030f0d0501141e0d0f0b090a050c06040308040e06030a1407050102070b090325050a0b1308010204080a200a060806010e1017 73
    0x40c454020707250700e511384203106403c1c04c1d151403000e52918414003c0c6800904443c05560840c004d500440d902e8490280c00390000e03072507001080700d4a5907940d0111409200402c04000800800b0b0000c0101403481e00c13000845504202d00e11141e000000b44841c49a401c0c1c04051080101003d0517505075142201c82c110a06040d280c950188141c041001e40b11004e26070400c2038008005c243d41907540d00c80d10a550f910300c0110200300c04c034081c80c0405404d0000510003880030989913002c96800c0784000f011a1782910407650354044200d01d050461405412880c000c101950701042b0b030320050000d4980641c24001300c4c1e00070030707510030700038180110640751401c0b42d29400c10084250300c040c2c03d002e080804420b44a40c038030702c800d40c04000c1012150000001c0001d00c100188252410b40e194400580058441522600250088208480860040407a01340c03466544c5913090402400c180d2580b008924041001411007560314160034001c00b0b5401d45440c00e103134088900b2409602c0d5212881c40d9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 444158498 1250 444157248 444157253
    0x905090a0e010b1f080105010306061709010609020c031210060e0d0204060b0d060f05061912240501020d030b1f020a0206040303020f061320060d05070815030f060f04 73
    0x90302c441200a6004040158030b1807800521380d41074544003641d0f0300c40032032590781d40004504403504c6115040020f8100075080042c0c0591030b00c103a4020b04814008a2000e4803403002030102c1e800100f14010320762000540207814040718280c141c1c0b044441e2051a8100d00c0e080f40580a00d10583c2020320502d403000d0400119500c035072045018143d8000020780b0340040708a114000c003890300841c0c5c03858402176400070b145e00d000703012240080b04d98060510241c1404400f6103001c1c41011040141d0b07501d89805592180c440c030b0301c96810052040041c880b89103480006400c0c24100d04840d0201418904401d8a607199501048030340c1d2207442c038004141600c80801c80c1001800c400003503001e680000e0001c02e2660001b08031080011400030380e003c42c0c0b10094283c0c200d006e58080104403060028001d03240d40c658a60408080c000a003c0518043c0d8044005044400403603503800420110024044039010129281e0200a0150020a0095007040c8203e646460003010a071400c080c80000a04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 444159748 1250 444158498 444158501
    0x605130f020705070609080c1c082b020711100c081e070b091e070635310f030e15030703270f21080405010b010905090a0e01 55
    0x1c0250020280c0e41415103a500003424020903100c0d20347c151142e03505036440f03841c03e200d41001482c003040c0c003c2d40200340d0f5550560303903401440d5000c9041201620102c480856402c0202c14501c07407000050b55615189411001480b040350380c5402460081c202d00301103a00561072080792030708200f0782d0b0b886200d40c92000710842140c0c05403c3e00b403c0c0210b4000f01300308000e0301c000e000c0c112420076034441000844451804550880700c0100c00d6203c03c01c1040550b011300c50384c40418012008042c1c280207901c44050883c3d480d0810342004c0004c507010400284440360414178125600d0382c030324103007e40f20900c0d101000100300028001103d0148158105402080d00c42c5e00b210000e08110b286117402e240c6903145070030407180d900c0820f0500070310816034205c00d95204203882c6002120740c00c00c0c3d00340d120213a0741414400c04441d24044042160207180c140c400184110301d032662072240c3c900c0c0901c1c085095980c0417000d1810700c00341c07035000e00452781d40500d640d51004480f58006901c0228114031030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 444160998 1250 444159748 444159757
    0xc0409110d0606031e0206030a0e0304030209070203090a050a0b07140102300105090c030c07050f010f0e0c0603042402070807030f03150f0b0c03070b090307030801090605130f02 78
    0x59004400440705010480e10b60400c0003264000c4043d86540184525510300704058118002d520034810000a8122400350344440031184a050440741005e89907404584078600984042e4056480030449281c2860039080b94409008140d590100107850452814518003800000401030412128231401e002e0302541518a84660590080119441c03540200d84541410204105ca0700f01c1c04c00109280c01c180242500035424609000d03c0d5650b64086071007a500000e4045407140189098540034034000d00680341c0303400c0c4a060020320852000c0040d440d00411410310ba000b00403d10030400402c0302a21a010750340c0a12280f244039507030341c409080007403040040c010b00e09107022400c0d205040d40002c002c00d42240d5900c0401c41040381c20072a403620740084c45500441141f43c1814801c0c060240040d05540c0d000d0300c01c0781e0401d006070341c0d01e03d2a0501158007925661000c00c9240c00d159001d0807032401040b2012003088000d040401180710280b4030211030340c040352a02a1b02e100c0801660495 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 444162248 1250 444160998 444161033
    0x32c16030c06020f010c0c0b0c0d0f0507020d02010b1813050a0c0608090a02030607030b0d02090a05091903020c0d08040b121014010206010e04020a03050d031b0806030c0409 76
    0x15111140c403490034034501c81c2a07020724030051094440b184031503501445601e00c04442600d9240725010b8503680d0f07051105c8020540d4080f07403070902060a41119074011041078000d402c00104442c5002c05009262820ba468014111fa04180344001d80e9200e43e442114544038601a10505540d01d40c2c40007089058010005d10314420709503200141310070000da94041d1942a50b0f0640789072101e183c565900c40d003070400a94943c0283c0003050f5198081e0f4445041002c000d0142c607400d040f1900051101182111460352a0341c40b20208403601c001407100030020b8020798200c4010894070303103000356243c07000c05919001e980781c0c40c14441031040c8402900e00510110440316030b280002444081c0c00307541690b6031030310b0600741c801c08034481c94841d009840c101010382c0100180d070710b490a141d03070180000e401070340c00441c3c0c91004400300b0302c14407078280d500c190350f03d0120301c48220801005401d440588072404002a807400d200e1141d034003080b03501043c5011070380440d40d60002d041c00203203d0740310b5021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 444163498 1250 444162248 444162283
    0xa110405040323130e071d1207030606030b1308040b16060504121206230612042a120b0717071115060f19030204111207032c 55
    0x40301698048200624544c02c140030f101c072503035a5411101242c031034180d504101082000b144100c848541c1704c1d45942d56000100703c0784101c3c202d0402e1a003804007a030403d48103540c032034005009201d40844640c0d08460b6500a001039441c00d6102c6c400e550040d4065107400c280002140381010201c1102c410495400400400960a184c5041d001d0518100c5105001c0750fa51846010500c030140b01d00422a001e44050150303002c80c050740c1c029400100c2c252568440f1050100842d00d808030b80e10a48038911640814000750001041d00c90660308403100303944402c6898405019211054000c3c071982580920050156210b010b420b603840400103540d031079013119100070421020303807240740c025119542c0400d0b241550040445964610421283d4640001c1c15031001100c034240943d12000d0407481d0408800145d450f40d000400b80d40030014910508800032075012884c402a1b140241c1003102404c1c200994800300b00803420400c401020852416020b05001c5c1c044c1c2e0041c0000000201c003002d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 444164748 1250 444163498 444163547
    0x90f1909140c043227060f0a140d05010e03131203050d2c07050f03061e0405100e0601090b01030c2a0803010b1206010c0b0a111b100e0a1104050403 65
    0x6045c110b01c03800d00380076040e0914017011031085d003000840007610100140101d0317000350070400b5100d51310001050301a0050852440203010820030b200321520003d442e07001c1c6541e41e1090740d1468203c2d2494002c12010840c00748044006908141100c4201e14120008140142100c10200002c0340b5902401c0230202d0304488102000c00100301d00b0107850085512101180880041c90b40e204021a210b440901c1a03c11034842c0b40d120030302e5694880e1064040358141041c149811003a038402c466020081d6121344010302801c0d0040c014105200c0c820b203420001012040d900a20b08281c800001c1000c04485d40c0a40c1c4401c2d10f0880c400007980c0226000b81d4959544482c20820b5000b20b02810703a00c81c7c0310f40810465071084640c20703009070704030b41d100340640c170390440603002809000c0102ca00341504104102411480c09144846080824090140815100b00301d0703054030103243e8500405d0300071a005000181a5020200c1184d00507140068582d80c1c0d13103030542c2c11819892541070700319020355 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 444165998 1250 444164748 444164779
    0xa050c01030507050c0c0f0f0a0f031a09100e030d0908040e010503010603030818010f0e03090a080606030a060f0902041422020105090f1909140c0432 66
    0x404114080003030380d04010300c1e03a410380100c401c1d0140700c41c02000c2d9040441071001c40c0c50044200e034401c8400415291342c41400c6800100c2c00411640042c1040d040c640080041c031200c201d80d00700d045881d6000601038601420810303180c2003038800c80f4032816030f540088942d4040401c240e5034419444034081107120000c3c1484485a002485080b200680ea40000300382c81c241170040004495154039607041c03a84031506484a8030f40c0c40140340020350740c1c40b07480103180c0045000740f640545214025642c2c1d48008014015045441d8220000c3c80d4080f0061001540b400140310100c1341d00b00500040d00c030040e620010141180840196129007000e82c200300c42c00c4d0704015a070040c0000340700c19441031800f402c0a1030f04409644082c0c040b68081c0a08401814180c1c001e1a89103c000d14441040d010707440781c5001a10550860701c3d41e80d960712030841240440f0b08074180c0046c441203485091510701094110400820025403503e405240c40340110030340408015000c0e04070042480c5215030302c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 444167248 1250 444165998 444166003
    0x3020c1203092b030503070507080a0c060b0118060c05011b0206100e04030909091401090602030930070c09050702030d050f0f0103110d14070501030e07270902030a05 73
    0x41c41e20384111040f40c110300740b480002140c44114181e4915411a08a05031800d50f81d03500010496400d1060410039440028002c0e0f0060449030341035261800c080540c0d0902c041203502244a5071705001000301c10301a0701070348000b1881200c0081c034020b054607006140c02409000307509484026001c10300358200300c4a401103aa0b6103e1103480541e0b000180e90765100f0030103000c3c107a40180100e10740210a000150710b039000076010303a00408031040c0380410b14080d1401c489a488007902c03116808424000300201c10f11217001c400d134421000c020200c07454000c0a0031b035007a1a881546026002a00e0010003004806103401030659480c00c210f50310b4000700194581d44802c1400240c640380400048000701d0301804280180c00f50107040704681e00395614100600c566a2080b81c0c0407100100100001d13000f1201e04210408680107821240d140000140640c1c1c82d042000301c0b5508004018080cac07024858030505003600001c0c80c4000b000220404d00014410054082d401d030140172954418020300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 444168498 1250 444167248 444167257
    0x40c05030d08040b0105091506210c07051506012003090a09060b0a20070b0d05060301060509151503010b07121418060f1201030b061c020d03020c1203 66
    0x65054804103410718008035400b2008070340c028a03000d15000144440e080a8080941c004a90801c1c0400444400d00098903504908030b076070f01c3c0320041010400030000c21049250032a025542c51030600d24103541e003a840700400d003c400d00d1042c01e003000840603882180700d5428050b1840b00500ca004640310303695200c0e845600c1c40c1c0c1c05400d030790400203440c1d60740341b02c1c002c125601d401c00e00d41070458040040712a0703005006440700f030701d24070310020745050000d00c05140101018202c0c903540c0c2d41090242c0c4241e58005005074840d902d0100d04210a49030412066440400210201d0001121000094003602070000145440b88040000308030651504014440d4038010515101900d111a00071281c04c1c04920442008220074064102d162016910900318001d0003045203060203110180910030341c010328401c2200140c0c080c0100b09114801501540040d416500720840200800c041407000d600900028003030350060307001c5000c8c14400d100b100b2240070001c00d01d21040d03862045040d62a0403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 444169748 1250 444168498 444168509
    0x200603130611030105011409130c0507020a080a0507033003090b130c0b1305040e01060f080a0206071104090f050309030f0c09071119031205010506090d02100512040c 73
    0x81c0008290b600d40700d141c00d032030484505075207070420b003010403030011030b80e80015040503007091580c0d00200005401c2e0043c006501602e644060b2103c0d005e0040200142860780800a1a08083e18000c0841d0700420880d06030394001d01e003489070449914056050003a83c50a50f035508800c51052801d5991542005103d203007d03440d01c1d2410303150410030034a040d411b0b0500929110b802501040842c44000c0603011001040a409007940d582c0c0011a080c0c86c400c040e040816559008140640c5041c0d1030108081c200141c010098200c059011400a10515401418410410458000c070703903983d4100e410311513800314800200410914103a40e40e40c00048003540b10b401021010f00803500000b80e10072100740c00500c000040d4030340305400d4401d0142460b84540b14000c4100001460b0502c1440c5441c152013640c075074400920414040044942c1030b0000f07446100d00300251801e907602c9881c042e0300907404450002c220003015100b907919218000c0c0788900050b11008003c240041103241204540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 444170998 1250 444169748 444169751
    0x10f0e090607080703050c09030a0507030605010b03100501140c100e010c021f021e0714060c0a020d083105010b030102070c0e10090608010f0c0f020a2006031306 71
    0x4846500107910340c0360031201c920003d26a00000381c8858866001203400c517400390030462034481140d002c00d08040000034192039507031101104208225182c40b46a0051901580140c03c508046030009041c1015104140c100029001c46d0400b840c007034811110003c07041400c5403040d403000e05200000e0410b20b00500b030b0039440c00e00213211039030000c05c0c1e008141280c0400c20407903c0d00c100350300009400418424805110441c2000c941941c80001421030034010300d0791642680902e10002d250601c010310505036100103009100200d43c00088001e00202642842c03000f0303544e86035201d02e0103200e1420001445000c542528800030300041c98104060295009000c00000c440c02d0609034401e5a200400c1e0042c2807e0412070100c81c4004030350041d002c42601050183e40d01015802e9070800d40010b08103941d6150000a5142180b00d800000000c50502d0341c0d6007541c1e150044d48a41812101500103541c80102c186070085540f020340218000414290310390a01124000c0811001c1da4202d070b116 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 444172248 1250 444170998 444171001
    0x5010611010b1909180b0f160906090b030a0e030d09060e0106050a051c08031519030201020607050c01020f0c0307120302030c07020f03010b0301050f191a0f01120203010f0e 76
    0xd080c2a0784100622069180303c07000945030409400041034503112001e0b5503a84e41241d140064141541c15000340080c21103c556814800034900200504400040c00d1203050b40040110540101034a0129150242c00710340342d55507040303d1805000f41c2440c81945000c000350072409181030758000c8400900644082141c09085841e040c2281e00318000c0561040148038200003030b14142d014072400d040d5001610818500300c1e500d00200350001d9032000040c00e0410500003041c180441040529070b04c070010b11101e43c5c91500042d48501000d401401088400241140c2c0420250100c3d030f420f042c40346c8400d40d901640c0c0f8400d23031a904044411034502a54168040d000c030f100c0d00960f40580340d1403800030700c0d009031582000061480c80705210b03015522144049030541d420321616211324141c4184082620b4800c20b2081d4200e00745000c1001140707400d03041400c601d40da50074903d9000e0192401d69803103010800503110030100c8520040901d00010000c1191f010900780f020450700705041d4890035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 444173498 1250 444172248 444172271
    0x8010b0d0f1a0108160e0603121b0714130c0c03050310080703120f08150103022b0b010806010c03050d0b0d02090c190f2f0706030515030c1c0507090501061101 70
    0x502400f070f83c1d41603059210303104c00003050b049c01c00149581440c2d00003541400b4640280300e81404016807241c402c0020142007694141031544413100c5c41020b0b150100803020300c031040688a48404e5502074204100440040c000144000a11000d0aa80030450f200703ea500c2c5000030050105e0080000042c0650000c280c0c1a40510412401100080e0f003240700f14000304011002504a03103603442c0111020782c040542d401844015411201e10f0120203e07000020b64005041240003900140c1008140348086011079031180640380c040021403004540111044000785072141c0032980698003d03411014008820100802007400100f1820040440e10b0501c3d0705544407070900d194200820b94038520001100c07820141c440980d0740164600841e00404000c040c540314094000c50086070740c910610240a42440581c09202e07401c83c0208681001c43d800b20b121300d100d849003041c207030701c20081000410406011140c042c04c40900304011560391082c004000144d0400d0402c001c0d464410340703890 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 444174748 1250 444173498 444173519
    0x105120c090a3209010b2208251d0a0b0603090a051501030b0a0b120f030c0120040b070503190941030c09100f08010b0d0f1a010816 58
    0x54403005000051983ca44581c0032050f1340007a841015991f02240041c0d414403035064480094103030b06000300440c6140ca107807680c44001c1d540310740016043c1e00f074081103400c01c071010144207248100250f81e8161507500b0f1039400f400c115400a0f500040100c00c0268a000000310588064011012a050a81082a401d1076401c00f8000506852400070024085100f160000340400402030f140d030b15401180d1910300c0c00c004100350f6a0605420002d03030000c00b84070900885071540084003810800c8a040380b001c40302441284117002141501040d40700920805109445454004803a803248050440d4001041c040140c000c041020030b0401800c2800d60744451403a45a403103e00d115a44040811100341c4070600300d80d003499252107284d0072400d05e6100c07039445a0042c10000708005a40e41000d0b900000b107150b9400002d00e681c500000c0c03c0da00c1e030305c080c0d440134440d80000301c5c0d00d0864202c2c14210b003801d1076188600d20300c8020000002c1c01090005a8582c64a2080382c07040c4503d44807a43c008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 444175998 1250 444174748 444174839
    0xe030c100b1f0c020405070c020316140103020405100c02031e0601090617060f06130e030d0e12041206090f0b01170c0f1003020c1509010f09020105120c090a 69
    0x400a000c540d020001411700794815900542c941c01c040410001c04d81c0002d18044440d460030031000f00d949010440810008420030f9160001d00f0150b082070306000204032001d01401c0f5180c02c0012303007421901551024481e04654800c0c402da414100d0a50000751503881e04203201e900d03422850b0201c0010303c0d485101c1100070220a80025125580700d40c100140b56082c0a01503d500c10304440c0f40040c50800b40c07143c0c000d041c0703410002c1c60303c400500c40c41104403040300c01040c0780d0303410010449401601040864040e00c40c006020140644641000c600800307040c5030080c20020003600707003c14010003a006604903080c40b42450381c04031356881c0060311000b5144045400155041f80003039240f0b010072000d08100920b00d001410011a000d8061904042042040c00c4103070304418881c002d1400e0007145d80c004401d450900001d00ca80d40001c110f842000001c1c0765622060011622501c180800c40d039051170300034950841e0944419808042040d40e0b503400103425091007460200751010725003807 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 444177248 1250 444175998 444176059
    0x509070f0c0b06040e030d0b0a0e040203060a02030c0d06030605060f1914040921020705030102030f0106180302191d010f0608040f0609080903011d0601090e030c100b 73
    0x5104203041d0b0b50700301000005050b903903100d07484240300203001d4001c0001c2e04540d0074000010480d10408820b0004903c200d4001080341000c0c0401c000160b1000503070150044891240183c0d0796440c155040070314040c0c802e81b00b030960b04104000040c4015500640d000f80383c100d034501201c2d0882410041c031681f080004c03515035603402204009640d14008010700c12000600f011a0030b0600399500002000b500b21044107003043e90281d0801d20341c0c10001d500c0540400d030000c501d107040003a24040718400510030a42005014005810ba80b502c881c042c000465026064130312121003d0703a09404254907001d40491a0603800c1a10b0081d0305a41d0070904075840358800607009820014222510280140103941140c410403000c8001500ba1090004640c00b4000140d21442000f04050955940001215110045030948840e8000c04201241100d602c0f59000801035094424281580240007688696002d0a0310300e442070200342d00408400c0310211040040c1d15140d90580095601c480d00d034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 444178498 1250 444177248 444177257
    0x1510080c040c0e010c030215041a0708153601090f180609170a03020a1b170903010618021305010f05070b040206271c05060406090c0b040f0509070f 65
    0x1483c03038075402008110101c50092055903004404409603046500e001e460407100441c8141505a809023800d86441d00010146803003031603401d0480040001e20b0111840900c00d80908039083e00022000011103560443c50640d070f0349400c0c51a00c4414000000d100700710f8601e080601050500b155403058185040d41551043c10082994458000802565900f203d03004100c40c032070040054010060072860401e983c0c0960760f012424001004100311050717003070004000d82041e40c00078003401c1507170040b41d90700d180a030b481d402c41000181c0503140c41c0c0d0090460f0496070004951280540d0014580c800240c91481c0c82c1544d29801118500320302041c000020b032050041000281406183c2070b0801d00040010b810800700313280090070544000c0200380d422406803100c80305070521001c0d03020714039800c201e40403900840e07407200c40c0c880400034030007043d440e680c9065030100007444d07100340040e0400408103a10303141c4500c058403050300e107401520311441c01d100000b00c3e524400c8405448854440e41c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 444179748 1250 444178498 444178517
    0x605130b0a03020714030c0c0108130b190204030309150f05120403030b100206060a09110f0313480306021e030c041707080d08091510080c040c 63
    0x400d200c03034200000010406400f00100008240e070490700b4064059050f014544c2c42146102091508040d41d0b10705050220f12800c2040d40a40c2034514481d02d41c120098a03401c0d9540d042e0710740c006c0715124444643c98404140802030503400301460080d82c010540503140c031501140b09642100d400100300d80091800c01c805081405829443c0307070414402c0c14081070001c503200014201801c10ae001100503440441040040c2c9404143c3d480104000e00d401c00000740185450503451044c88032446040000101007080160010501e80001b5000a1144003401088000c0524114619a8203500740526030314046800c0805492048060701c404500034035500d96a1504042d41000f41c0d0060400355400340c0003105108080118451000080815942c5003003441c1c50425110031200289030b60300550092100c03c0000881e02008420380c02e005c203a0ba640e03022050300c2c209154560001080d24001401500404000c0b0b50307066070046000e0380e510421110521040754208007101c0300180008030f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 444180998 1250 444179748 444179759
    0x1506060306090b0f28030b070e0f0307060c031803030c1a010518040602070c0e011a16061d0106030609030e0d0302060103121715100c08030105042a03050103060501060513 75
    0x100040d00c45c0181800d180800040202e401c2c80c5030403590041d05c0400c1d0000c00c2050943d4400d00c040f0300000c0446015403501c0403803000c42e50b2002c80d030042006120415590f10b0a060040c1a0044000812600042e00a8580c9001805803640344d004446000440312847c4910a003102c3d00c40c16100060700034050046056038400c00c0c0343c000390041d41e00e0b44e420042580171501c10300c00e180140203001c0e81d076205549031180b201c0d9801ca94051807144900207001508100306010446400150040d102284660842c14803d510880c2607614600a40c079001000042000507044144184c2c02512a81c54a8000c0011f1120401801c0c00082c0182c00c03400042c000906902c0c98002c060400789004904000300c0c6401485181054a8603000900c42d010040c06074544000ca40f45402000d1134a444071004036a51300d800c5020600546201f5610307840c0c43c1500745000107400101030545107010070f07600035480d8003500070802804151002d6081030000f186a82c000e00c03c035043d280c60152038801991810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 444182248 1250 444180998 444181009
    0xe0c03070302070b16121416030e07090605180103111203091519020106050105031b070b04060509010510050d111c0804080105070f0909020a0c1506060306090b0f 71
    0x405a0040c55400d0143c030300451440010f051141c520600c100001041c07456000e4441c91400104110190818079028403c100005000390810720b0303140c1c54184000c5801d42503000d0190048000c10a1103854000030321064150801c84c1120006c0c0c1e189203070726210080407800300c1e0003408041c20310300034448003100ae400d11195070701c2e1244440094906000321440080c600c55402440940d04030008a0300c004170a16009082c0c6010000d070001700941440c00e0000b03801070100174469401306010b28088224079080c44101c8069035030240c0c0c008814a03141ca094070041805031640440c2d58a06000204268041306010042d0340c0001c240d140044156510800d4004410508c1d035004200b04e91110314600341148400203980c420442c282e1240d0810407214211840184128100201001655010368001d1f000300142c40d445e120241e55010154010f0391040d0204000414004810404c0e210940e21750780300c00c05450140e40d00f402a5a5110014800e550080d4811944000e140140b01649e00c1e10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 444183498 1250 444182248 444182251
    0x100e0619030804080a140106060807050a030f05130516030201052a030a032301050a0501200a080a14070206040506213c15040609020f0706150e0c03 65
    0x10311101030000c03500c0342d807082080d070426071122266602801c03510040004502d82c84c105d00703c1410080015916060b0010068207000e400041404000644140352503c81e401c5031200440e0440103001500b4030004888074044044400e80b00c50240c0031204034051641c130508130840c0d4050b900c66040c4101c00e54103801c41d040c811988100030182100c1780d186a2424005405000b0282d01d00113280001c0d0b1301c2c00c4c3c4820340c0c1411609804e926501c0144007a55500703d020068800a1030041c500883d00362040b407407030310505407055851042060540420281c0c500130030b02c04406560f10043d40001d03041030b42e0180074490b002544043c0500c03043c003290401c000501b501c0040c200803001040400e18100102d1881907032800785c0100810305540f02029030551501e603400c0d0040c505404203511880381901c0c0203000e0b000c904080106800094a82d0311354208401401c00c400c411507036801480d20804040e40b04010850302039003841400d100016503101080300316051036829003001d40c3d45402101c071982c0b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 444184748 1250 444183498 444183529
    0xd030c020718090209010e041212020d140402150c190804051504030c0609030506071d030d0210050f01050d03080a090c030f030305010b0c1e0f01150608100e06 70
    0x16614002600c040390000314507518002d40380007690741d419005200745018140c000e8003080300f4800600000400c002442003840203e8903000c1040031440200c00c02a214030360402880505203c2140c0c400c0869440c039a000300d2089a550700e80c0403603003020031840c0c0070300e14203422a074000c034140d0100c814040711440c00181c0f017650060f20b0f1903100c0c0005144441d220b10b1070181180003250034420011110403060182800382003000385145141c0d01c142e0346d03000041604007007201130386170b00c22500d5006c100300401740c200800352400802021402507542c0707070948030882c3d10750400000c00e004401c5129014180d61001c2d00030400403071191426105c0070805010940015902c1c41c240001c618030051000140d0710801034651081014100107043c0ea00c1a0030480c0c0000e0704201c11403207030340c0c002340d04083d1a0342503440840605520303c101d4200a4015401c000329401d0041a003c49200003072150300f52402c44d10381c0049501d444011b00918101405141c0c1c0f04100035020a0642c5410015100c0044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 444185998 1250 444184748 444184753
    0xf0206070c0b130c151205010f0504020c0f010c0c030909060503060708070203120115080a060f050f01050408010c08040b010e0609010e130f05031e0c06060409230c130e0d030c02 78
    0x2076840c4d48040454405a00900d0200701420014942070f902810248000e00c01034018086035050000c2d44c0c490702c44a1048520541c0d0009074010020014000c41c0e0400540c00e0082003111a034030f20280c4140d0503e00c080740003811091020580c24800c1c4252419600003800909143d41c502c0403d44052001618000c154031060100e00402022000d1043c040c104036400b550070816000d070040d00e004c1c009401c4030340203030501d1750074400c1f60300050241080310021640080300707a1001d00140c801c0d00ca190404105542000300141a541d001080c0d54040c500ca000c000402da0398403a01c020705071405650320380d4001441d0004101c95042040000d4002900550800c2c20140f03555648100c88004070007201d45e6040812151b141c0e0380415500040e00200744203862400030802011900c0d484007c01f200c0c403980d511441ca0080c0041c01d5146e950511a030644501900d080083e42961707001c0540b0340c2ca01c91012005100f034248114060130740b10143d150010281048011401d501a10045e905a803c61 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 444187248 1250 444185998 444186031
    0x90105040306111c0509120d090204020313050f0304080a120912060e0f0a02150a03020702090c09040605010e03032b1d0d0306050102030a0c1703070503070f0206070c0b 74
    0x356a51081e18101c66200b58520b5489104c0003003481300070b41c60150107079241d140008002901074046011841a484031503016513842c4508201070041141420194026102108220340380084286860000c0c1c001c0044030136400e45442084e07600c0c4200e0040510310f0700449030f060000340d1a01c144441401031801e00b0f90329a501d90309000c04c110348590041d0b580503107404440541c3d071070501800340c582c5c10710030107045920990340118400d0002e6a01e08a1212000100420124800c1c0c1c10754004a40c0100009060b050801071003209400910116201c1c41ca800703000100e540c01421401d41c1900050060350420001c07a807100c2c605000502101c03082180c00d803011480d022284280c640c00c100390021b0380c03290701001c035030b207440d0103195000b001c01d25180040500c5160307000000d4440000d0740e4030f04054220f0107441c0210a0b0840d0660300d40003a040841030154041c2c002001e148101281d0781c0f4080041c001050407a81d802040d40d44802040c0d807019800701282101c801300d940030000c000c0041d00b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 444188498 1250 444187248 444187253
    0x213020705010b0d030203071203050c0f03042a08150609010e150301020f0d0e030a0c12110a060204090b19050d080f03010602010b0a0f0605120403021009230303010e0c0901050403 79
    0x74030f42084c0840050700000750318070401c980a07115420414803842c080000d440c141d980007802e4820313034001c0321441e48080002001c20020402d1000341601e0859103240c142c0070a6103040c04021280102000c9003d00f4003010602030f008a4802d01c40c900040040e15564078011034804400c902500500200d1094045891591000d000400031000c0d100708069840116119002c00c441019640300540d40003000488102a40900700251203074004000c21803c101c00c0780e0030344100c14841d90000140c003910400c203052000503809001110b20052003841100c0054042051a80a01c0408418189600814021410500600d580540c89071801e5840c00101904a500540090344000c0050f9115143c1000310300304120f07840024440ca03407064801508002c1c0c09002d43c015442000c0d2038220041c0018107041c0700f002007a01c14840d400003002004410b0800000b00740318100d038260340c100d492803d1a0409000012a4100c1e14034403204070150300d0341c035403880e331540c03001349e42c5810046c0a01001c4003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 444189748 1250 444188498 444188509
    0xb120601050a0e04060605190302040518060d0b0f01030c050d21030b09040524070f140405220c0e130f020405060d02030415020406021e07170f0f03070213020705010b 73
    0x2a03c1c1b00e0b1540c1c0c1d15032000d00a48848058401c8402d0201401800304005948440325401100c41c0c0c6c52075184001d42e80c0a01080e242d00c43c82801420a480c0803044c007910011910020341030300d01900344c80c040140c5801c18040701324480c1000904540300c5001c40c4142000b0114504003181ca1464003086082c9100000303040c40310107503800e442d40e4124400300c6500002c0c0486600300c0030291015903046113040c290143c6524024400c6100b4403000b08a0482d000040c1c200b203901a050050154010001d01070203181703181d40710100b066543c3e2520202c83c149034024514000b540c0e10081680b500c2d800d078001300002a14030000001000c80e024040032a42e50b44a1005e0032480100303800060b00c070710740341c20400e07003011f1100340d5403500300d104010a000540d40030800300c0c0e2003070081001183c03e44400301e810345404419401400e0703841c80b100c02940d003c0c4001c90075200011a00086a2854040005040d140e101d280002507000d60743c0381203404488034680240c005a40160300004903280300c2c0000c5030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 444190998 1250 444189748 444189761
    0x3140904090303060504140403090902250303020a080708160e03010b0a03050322050d12110f1b12030418090b01060521100512010608071e0b120601050a0e04 69
    0x8000c03030b4407132006203e070b8141842110001c20b1003585565560a01e1344028207802e1a0780104d20f101da8001618404404d50300d5400c00000901d00da1a10402e8524240180290003010070398001401c40d1000c40d1120740704441440c0286c605d000584003513803080109803215042c2d88140fa40654075403001b170344c2c9942c8104c2400015401400a0b41d17071524481e4031860121040205441e081007499824010303a21080d1403d0142603000c840300041d81c48000c0c3c01e0303c02c0c410081d0400700300e1180412114510402240512030200c00c010201c10300124502045a001d4011007400d0b00c6174418002080064000c0304421035045010000240d10140c0352a2004540800d0f000940400e03c0000d50306807401682d055840500080520070b40141040d05c00583c02702d0392881001d03c138032403032214403a8600d400e5000390002c01095003100d131840d507618045000710b03503203000d03141040342c240d900041e4410320031088403140d081000c100c0d0300d42d070744040c01902c01d50003400d156001c0062164089165449070b11494 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 444192248 1250 444190998 444191003
    0x5070b0a0f090909050a0303050910061511010e03031f030b0a1d0f06061018090504022d30070306270f020d0b0f150411070314090409 59
    0x1000c00700c26200c000d401e528495215248641c80c3c481c000c4042807011858200e4540d0600e400f01c2d584c2c541040c3e10380b40c03c154018a540305458001c0000ea00040e82c00125100d624a40724000040041031115080b51101110803001d6001000002c0324000180200c0340a40740ca596003003407040d200d80f01d45118600c103c0391070010f01e0755412040c0c466081c1d0303100c00490500180040c80001d58054441c1d0b02d6140140403c1c1c043d60718880350044603401080a120f5085180700c459a00380d075a0f80c0014041c140540d820390140203804c1192844040980c0c440c005c101c07442c0600c0e5032080341c400c1480700c0554042024048004010380101000d1909201c8001c4060054001c0020b1800c50514600302c0ba0f02c070040041040c2c101040252090045902c06403064204e400e0329000400c9002150440884c104000c080c1030904041104500c10310014600690510603c1c2000e19041001d00003100c40e09240740c0c4410b82c003802a00d0000703104000c5004d1804005480b079003801642404101514403c8108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 444193498 1250 444192248 444192257
    0xe0a060905011431090303050a140f01180207080d09031403070f0c060204030803010803030703060503010b1c030903050118060e010507080105190503060c07050f07030b060d05070b0a 80
    0x4001080441c01058007610500101071440000d070030005044042551a6440000450034070000c1400d800c180d0701c2005aa002080c4018001494024000c00040f20000c0100c1c0c50210039803400d6010b00c18440c41050711401c8110740b0303400c100c40741c640d00c500c4250340c09405400300062000107907030001501040282010200302d9001c10301e00034180401041074000c0002060003041210795010328100e12040d82d50800c041e031a645814408041d10880d040030b05110000000020b240c000007005511901166604008a5440324101802ea81c4010409580040fa60103284c20680010030300c1d5940c944a81050468181e50380c1d90345007560300d035480c4034132181c1100c00d101e802e00c0703014003d0300c040e0346210380200214074146c44060007921041c083e99000300ea8262039166140110904180541380003422264249040c99811a181e402640f08850a01a2403540600e4040004400060303c1e8080d81d0b00c000f030350716581442401181c2d0310381911a44510000082d068440070002c0007443c100d90354 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 444194748 1250 444193498 444193511
    0x50124080f0a0809040e0304050303040305160906060909181a01080d0c0b04030e06070c080c120307020f040213090e06060307050316090504030e04020a17060a0b0d020309070e0a 78
    0x318a0810000708a00386554000800c0000080c80c00d81c111a4554003c0310000303021942c49403940c0c50740c01907403c41074152100050100c00e00c035000a816224200c00c900c00e0440b5a2104605016240c0a00c100c101245000c501800141d50300d41002742c01c0302c01c6201c034030100c07101c43d00c407144d0b0000040301e642c580c50885001070120200c1448455007140d0f45003045400031045030741d144a44103009101400b000b03101e402c0038031255980c4044031740f4a500000703098011078448a555855041b60080e00384a01c0e139641c5510001400801900d0542d0340081c159085c3da40840c06000c0a0b521100c64070784240003169010032610701c140300d0300b0038018181e402400a468805c003814506003298100d140720740d03c008009615461621500e4040da0081c500100da19265880d0a41d8500c10f100041503000d03001141425001d9880400f05c024030100d00d8942e5182d407540c0040c00304000b07107409165400902001540e406c032103250000d40c0c1125007070003203c04040c2e0301d070074040307040c0f07400e4600d0b0381d603a5250030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 444195998 1250 444194748 444194759
    0x130603050a020705031e0c030d05090c040e06061905040c031401080613080a0203070222050c0f07080c0f01060e0f0106030501052808030a0201061a03010302011407050124 75
    0x100391544428940c00840c6840515150207680b0700888444012182e41c544009004074560426030350411542001c80751109030b524110009020210b48510781403140910780f40140c03829010300f03c8100e01060150044c0d85a01d81070003418542016404500203219000144a032598441c2c8101440c0030707900040c103440804450740101c0c02c103a1101031658406014400e01001a07500d000800e980801300903a80d038103c090990850245100103503100b07921000447e41007032600302039915034504003000c01c260b56600c1c00c0d51615000b100d440c400444405c3c4000f00024143e14010006c107203066040301d80092001e00d0803801e440c480d400c41482d5041c038000740320f0940325907016507014200d1800e05002c19810903001c034040f00907980098019a015030070130094a012001a54003030551401981c3d9101e00c84c4001a001c0c001034481c007a01108405450b10383c400e158401c0d02d041e250305943d403a884d02e0f0010310304e405a0f00461000d8640e550b8600800901c03d00821550060303840701005440304501d0b10b03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 444197248 1250 444195998 444196001
    0xc14060a14010b09010f0516020409230109030e060705010608100b01020d0302070b060d061404120215010e0703050405120301030c050a090c120f020405090405070f05031204031106090402130603 85
    0x1a400918041010b1003413403281d07038028120120b5219103107040398a4162000e22498117180600c0060341240c6483d2103141808101100501c1c00300c003c80c0c0c42d001d45082c25011030300b20b8220400160018443d07081c001c00d549044002042c0c154003410000c28003680781c0c121281011a60303145c4102d51995441a0702030b55030188024107040100b402d04505000705500c5101c01400c00804041c440c4400700352038000c10901e548125804410901040020f00e003524091203005152021000584155101500311340d2040c450f0794169200281844000e440d029819070190a014004580c01c0c007034611413600300e0f004040514001c40c041d580039903c9a00d031405010301c0c400190480c040d114204242c801d00d9a8110600007400380b0106000210b415170003620f040240130700d03000340c2c0d40034a01c0000c3c0814020b00107007d50540c0c000c803a40034140d60340c4104056642e02c210070500c104042c01d12040000c1446c10362104043c40340030300030510702142c04002030102ea0205036004100b01000c4014407031140d05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 444198498 1250 444197248 444197251
    0x30106120c1706070c0320010b01080a0911040908070f030c0b0a020a020a1b18050109050a06060f030f0b0612040308090321060a09020c030c0f010c0503070c14060a14 73
    0x200000409142e080b42052601d4003001401c94080c07041c8803462408151013031300e120b485028219084101445100300881c060854030b540c10380000c240301301040500040c1d118140c00300d98450641d8100b550b2601c180700161248450a81d4804414002003012031040c0c1d50310b0107898881e95600f054901c6a290071a0205c00203090240b01510500c2003403070241c0c0000d56110629004508110392601201c103204a40240f5040303c428018640407100080c001d5400031810380e07039802c60510071940c1e07010041c0212034540c42440005151003c1100185010341d22841e07407540104000304400060070041003443c0d00499001603060070207400c010505d68401000d07908422090041e620748a8400307081160b010032044c1a03c0ba40c2154000301c2d04c030fa40c4910700280109103820095488140d50540b8980700e80120036076440728042c0350850b4046017018820a000340c012034503581e0450311041000c07503500d5107100b41120f841e103950841c140103400070400700d4811800700c50007040ea10080b41c4c00f80400c020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 444199748 1250 444198498 444198509
    0x40e0907030b070c02040e01020a03020a0e090903071b0302041a010e1f1202091c050d0504260a022e210c0219080703090b0c0d030209010e030106120c 66
    0xc580c805100264900c5030903070300300495140001420210380005030042520034607656041d0320010700b4445007a0103401411030024140c5540b103401c0c038807206222004000b282c0f0100c0c6900304100d80400509000000640410201841c2c54481e40300d501040403288030b050250070f070a02d62111494a903a02c02010030441d6000c0c0c5230043e095281400d50040c0000c220807030f00910440c900d10034149446541a540c035010000c066107001c00a1600c54001c2c011120380580e03540c021203080a80e518007030000c03a02120754900c00c00d05030000000030301101c08001c89000502c0e020b80b405020141c0e0350098050202c1c0c0071400c03a040034000105031a85030b01c4d01c00079100240b00507034010b821038181c900c84c81d61651000010100707401d10041400c03800c017400b080700d43d96984196450242405480406840000c6c8a52a54140d2039140c2102035003e01402c4206000d550194088150107446070b000741a4018040c18030111818070341c00080c0c00d4a5054001c0c07186440e90003104001c1c0000400303248014503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 444200998 1250 444199748 444199753
    0x3110412050303040b090d0206061e031906060b040e062b030e03071d0408160c060f020706090b1602210a060c080c040603050903214c030c0803040e09 66
    0x12861f501030344032032009000030321604128668130001808140d0352036540074000d0992300001120303c9106120340300c644080c0d4460749840170114080b260001143c09a4022002c42842952000e0804c05070a045050b02c0c030074960b645091035408102100c85062591007a1100f0003284000028145000350540c4410b80c001c54151034020100702d03428426400c80e8105244c16a02d00f050450090f854144440007422071210090000d1a81e0b4440b0610b0a154259429200501c0d510f40049501050902824440c0503003000070100c2804103190030480c644c40545024148110004c03d15001000303401032400d2a04401004000c102e160300c115160104107013455081c904006511000b81e00070b0b400341d031061540e00c10100f08200e90800555081d00b10b50394884c08180044200e1420305001034951100090034001035010a48600700c845010100c011106d81c900000b00d113165648107900c40452440544403e004030110328949152400b52501c40000c541c1e9929108001141707010082c80f42c000340c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 444202248 1250 444200998 444201013
    0x90b0f07020d0e010c020402030a2003070f1d040518010c050a08010803120f0919060605030d140f18031605130b0a05060705010f050106031b030212010603110412050303040b09 77
    0x140e03041000e0b1901650141c7e0016140e139610079608004011060300ea0501510040d1034950304030540b80107501c03400d225600d110301c0110000f800d82f1030340902510034a1000ba14031000c0350303c0c2030907403049a00040050261040c07010080703d0500b12040d001c00200000c100180508486070000040350050801c10001c40c0703403005540320005941b1010300301400b040f803c40041840180100248500000700c0840c194a21002d072404000134840340c4036260103030190403881c4910900452440c4003815440104525004820b144c09086900a18a64a030301e8101d03a542c0200340c60820116200500c034459a000007400c01c0f04011180414895202e040707030511641003025180c4c107160300304072041960307016119011031400c0c50142003910b56840b007080c80d2100010710141d1607000300d900c00d040210512054950150700300c0c180e1291425022810a030203004002e914072940c046e901940c0c88210707050816855031089a001c020300784003030794158404014001404a00c503c0c8903003000380840284000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 444203498 1250 444202248 444202277
    0x120c0414060d020d03170a02040302040b030a031d0a030b010920030705041809060509010b090a0b240903030a0906081005011706010e0a0e041106090d0f0501090b0f07020d 75
    0xb9a129048028041c44400c40448205800f402900220313485460440c1c4243c0b41c00d03000b43c0021b40040c802684200d04082c201d00d25402e000c030750a04099059910021280c1c80000c2415100601500091300084081800800300d051000320038003038501c41001180d0483c03000558407290300c4411800201c040100240300b160f68201e011642152200700e80f1111000245008400a00c00003401901035402d00b030070001d00050651000d0340c0220708640c80340907501c50700d040d80d08407080c0d15801c9030030480722890b6020b44c204d0340000c040402c8004940c0351034240c81d071000c2411a005040c041003c1010500305010550300070082c4c1c4e500c031007100e1907480c0043c80d20000070010808002510f130030840c0399000c82c131540d114082803414020050002c51181d5a1100c0200c3d0340e0300115416568200e410f210f60711180b4102d0126820000006c00903e000071340364a80c0c078a00b02e04601c040302c4030341d0303217800c03841c0002d82038140d16129410011040c515454258006820184210a0f0004000da0024134040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 444204748 1250 444203498 444203509
    0x9100b0d0e0f011407032d020a08070219060e190302160b0a0503180c031b03070e010e040b19090605040218070503130c0f03111507050c010c060b120c041406 69
    0x140107a840c54082030300f6002201e6000701100b0143d410748030b280440707c00c0f0110110f03600100760a0205554010403603403002012602d40c41609081c542d250404059140401c09030b4001408805140d8140c0725800148441c41c2c4045001c480200c2c09070700100035000b00c00300d041203050000d10201c0b030b103240340c02d400281c01041d501c0700400c0c02030000b000c2100b0380c03042032007003141c49822000681160740c003842440030f14054560000d4090321a1040e0349d07000c2041401c1405807030480342d040b802020179841d82c1d030f43d50b2085007000b41201c4210090281e00e2003201003500501b1201030040f80002114141401032119005118131101712402c52201440b540c180d0060443e5400028408404003c41142c071b02940d2040c00c9030b01034441d5243c406404014040300c800160f001c110221050185540e10380043c2c01d01c0e008581c0d001e032980e0000c410071010355010b0001080c05900c1031100046800d0103100040340d0015200310354450340c2c040104007086003402d208140181c25615060405840e20500040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 444205998 1250 444204748 444204751
    0x1103070605040303091205041a070c0e040203030f0409060905090303040b070e031534080105010e04110c01050106030c03181713060302340209100b0d0e0f0114 70
    0x508041c0d6880004040c144a90300801603d41e011031110320344140c1040c0140343d40c000d40625848000600c10000c046100002202c3c40550b1002c40001e45901e46520701c2c1c540310000340b00f6a00f60008004401034280000014005061101400664a03081046560844100070403281c203036801001404040380d80c3d00c00e0341d5031090341d500d0516087ca0b0800e02083c00c0400e1140b00031031314100c074424030400300b1039003003080300d8140303a100d2021611540106070610382c02064050710100b000640140050b5106d505060301e00d0401410120b8a10f114104003003803030344502442001a5034400060000b1036150041c403800920a2406003c42070070407000c0d010f004601c0c180200942c00390108000244015030503540301064050350301551555828002c1c0181d44120141141d6440403e161205020440282d19a00340c98603805c6004120035800d002241e500130300900e01c4119007080010f82c900342c500041004604980001c1080c1000c0d001291401181c1480b41c1c0303080c1d04150342116010140d01c0100d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 444207248 1250 444205998 444206003
    0x40602011b0e0907050c16030b07050a050f030702120d0903170105030d050c0f01060e04050609120a0809010b04020d09020f060c0606011b1b08060f07020d111515030706110307 77
    0x82c035454640c1d880c2030300c1798400c00d01002c1090180b15501607031010100580310450b406510a04800d540c2c0120464541c440c0e10b2051002c2a42404a510249494406103a000100d40112240242081c080b880c0c2030f00101440d600403501d0b03c0a1504059000c405444040c00c000002030707455042c8400291554200b4924908010020900c501022000c004429400c4400781c0200010b0362201130500e0903010888080d10705105090218074181c1000520a500c2203d1030038071420200100707801ca60042015201181541d02c8001a5030280e840317200804c4030941e4048001802c1d0458414030015110300c0081c00d108640034000c810a141002c61b1190b4402004d1a10400d141721000c2030400110400501401c0410703204140b00c03482008840c00b00170343d11a40c0882e042551076200d5004001001c03aa1900140c01000c9107455603805200c0010351804420b058800c928040b440704100030000300d41c00714a50000005580c181d04083c0011800b4200c20b1900752600b0001c10195540c0e48103c1000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 444208498 1250 444207248 444207259
    0x10311040e07090501030b0f070e03060a110d0e1e0a05030a0305060d050d030f1a031510031a07180b030403120b120d0206070e010c060f060e0103030302040602011b0e 73
    0x6600541c0c4062110901a101642d020041561a400c03c40c010b91021180e6680134075542e80414000c030b000b03102c42002090014001d251170398403541403501901e07859401c00c0c00c00d1030620003101c00020600642503050215802011413050788007088404041c4100c40c101e031500f115016502050380803003142d007000c400c0d060128075911108045082d0585000c80507082d0300038021185035a50f4190482c01d15980e007002e09129070140c8000580145440005032a17041e40580300000070291a851300b40d901030511030003104603559a454400c0041000d841c48a06440b03490104089940c00155090003032030049003001c082c50034480307030451910000c0c001400303003e1038041ca1b01200002c0d8004030505a805020f081c4a00c5e0f020b441aa41d440b19800048094000c0b100010701052041c2c02a05810005039a203405070103182e15610014050030300900080c54541c4c001103984042404118000e511035130300140c0e00d6140503402402c4a001c4420922104500410030041031360190f42d841c1d41d601e04552 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 444209748 1250 444208498 444208511
    0x10903110307080a0303051e090607032004090b1f09090207060f060b0904060509070f080408090307030c08060c0f310f0513020406170907261501031104 67
    0xa407034031a0943c0f0283d858425682c80e2010154540c200341c0c0180c107500caa01c41014503d503400f8180b45422502444164803e8001940052081e0402206401e0540011000d040025035413046030b0b000d40c21860b0401d0f01c481201c01c43d805d090b04c251305005c1084172011090340104500400012445c4501c21000740c021400d001400301d02e42c07040610108070001044131990711184183c41da04042a0f0521443c54210300003080e0a02440385403041c00c059031500508410442d06a03106040684203880c90394051011045646007080680041d5001d911000d07100361030030404914216004000d45d007400b1040c801300381505203041c1035807090000003821011240c0b03554407100c10001d0f1911b20450410500b18009100120369164030251181590780c003c090392903412580580c880c91003007100098003800804107146810a910b03810242d03c50503107180d960389580080142003044504d140c0c4400025040f201d168040120385a20300820856095540c074649540504508040007e4010f644403038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 444210998 1250 444209748 444209783
    0xb0a150e0d0309091b020309150d020c0303091c08040f240b010f05030c030403050c0f030a030c030b090609010e0901020c0105090a0b07090b0301030f0201030b030a200f010903 77
    0x115908032040d01074034444100d4080d040c0204041c08a00c44c8020702c81c509105070503c0c1311031034446000d4038070980040d0718100ba0642484a0030302601500d03e5440307814850340d007003004c1b58001007644143d080c00854803403e01070075450070704040d0148901c1c004042c0c40342e480308642207800c440c2d02a03044402400342c201103007480401c1d041b07040300c082e9030030703425a81d8401c40c0841584075460402080c1e071080c071000803071441900c85210549070318401c80720270710000380040e2080009080800042c402e136840d003001403024524503005a011200429140e55014903038507854480c40360071b40d4080711034142c14205500454002801801030301241860700c80002c03502c580c03d40403152003100e035200800891400d2034180d40c0700c046e024421581c0d8030605020401036407140c0400001e580703090070064078691869498440118181404078107042e150262810980d034140503014109008203000700d06000c41d64030700c526035040822018810509076032681d400d6607210200700140c07580074274540304070710441 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 444212248 1250 444210998 444211007
    0x212010b03061e04030521040302010903020f010204030812040f08040e1909020d060c02010e0a030503181f0209032833020d150815090118081804050a0905100b0a15 72
    0x160301f03401d0079813002020f110801d42d0550001004074002d9081c0c0f201501e0346090a4240e110314070010b080c962040c0100f243c0035150b012025000340c400c01d404c007440c640d1036a502c4040e4025500c1085a1200b85041007221401c1ca00b20004007074102c1c208003d454165030000d065100b030440080c06840e914001005001d000f5400858680358002c203d4050f01c4240c9001051a4400c95181c50a900910108040380381d0010340c2d450603031000e2000071184040d00503004000d4000013200c075894400c88019a0b01c11681e48a801401c0c0a0003c6a82400140b410200111089841c0403c4035180030a038007000c4c210a0b065010724000c10820259540c0d4044460300080c0c0a002408040c24004c0600050701c190001911600d807001c80d455864240d031001600c40c200c8290801e90300e50601c0614085000803411801840d020b42d48000041d101040280800e045a40071120068000d40e184100824400c04200c10707007c40840e420b040c000e181c5143c0128402042c03500c18080d129441c1c03208032111074002d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 444213498 1250 444212248 444212287
    0x307090819200901080c010201110c070605071b06080405010b0f0f010507020a050402030c030601020d0e0a0b03040302210c0111071a0402211006050306040321090212010b03061e040305 81
    0x20400c0140d96118178800b9226142d00c0f5680b070140d0f00c0c2c003240624508001050300d060103500c0000e0400e6900c0c10500759610303480824229460141c98014004070006000c0440103000c1c0d56560000700d2800340b4045084504000419128102028580e0181d58604025400d101000e01c0e00380d8550000d48049a0a10036039000a030b03002e40003004101d40f040a48000d10b100310005da003128902903032484103850544070190071540004138030324144101d030031550055401034842e1040756034000101c604403041c1003031b020301800181c4000070043c01e000802d000390f0040c2c98480e0f002a1038140c00741d581318000158078010440c14140880060195034440c105140c9241103106800d19180c0398000322911400100c8107071110794036080000ca268240007445034851981512031030041151a950a03400047c01480c420416440f160300788016145e42e558600e90501c04070003c81c208104030201818104024080c0d0524103000d140c8820348030714040c2ca260000d8050602c0c583d1034800c2c0d001690540e45 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 444214748 1250 444213498 444213563
    0x60904060308041d011710020711031c020d02033610090f0909030806040509120705060114030d05071203060b0408060907060e010f0809030412080307090819 69
    0x3000700e800140326104413040c0c1c4541444800320241a0f072502100b03060510700e80d104010b1640b0480001034415100e40c02031101c00d024040520019000200281c9800c94030040003401e04e000d4070b81641c41035010070941270f031041e55002850411a4083c844c91800e0400d00e41000c0085440481d420031403640c0400c10590400a00b401d601008000005401c00007248200d81110b2440c40000410289510901340100d60542c1d92442d281c0b44d0404010261001920820b0680100403800038144810001072820500c10400f8208030740c9004200d15141144c02c1c0710074025004248544e4040c1c0d071000450381c5032940061107200d01000700000714001d2145411a10242c080000c002c1a49031000481a2140c0b040400711258140c4545003211159a10404980410540301c014600640904c0210382c1c00501842104d05160b0340306d0081c1120760290505a4164100000388641c1c26807101e54040500040c80043c000c840501c210490340c50003548000c1c1581c016041e00d040f82d0070340c4003071180d00342c0c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 444215998 1250 444214748 444214763
    0xf1501060f0e060c0f1f0603110405271e0604050a1403130f090c0201090213020d02120403171e150f1306230310020a050f280206040b01050609040603 66
    0x6400403a5071b65240c01c600064141c00d01e0481211414110a01480c2c0650345d118200d0b118106425081c4409400301602c0458050030f01c030b8155150220101c04810104d8900c0020104038602021126034603218242c0ca0405800005c1044040303035002031040c845682c001c054201c3d03e08008050f0342940555201000740f0340502c0c10000e5071250946200044c0da120740010007100490003802d0342250140b201c0207402c0700c5094001003c400e01980a0024401c3d2110b000d80f802070080070600c8010702c01c4030308070041009100400d80c0c9030003544116038030007002020003600494140419201c098002c102c00040721b8004901c0d0b1450319850f820000010001e44404149118801001b0141080303018090b030740c0c40d0b54005a500c1c000e24100c94030040d00058060320212990078002d4001c1d42c056064407041c00003c100d370b1038404040400a003c030380d41a0703500140500d0340c081003403848125241c00707808540c072007014030000c118111129811103a0481d180307a075642c4841e002c640034003d0785e48041e0245 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 444217248 1250 444215998 444216013
    0x206041401200709060915090c050f0301030c080706110a06180206070b0901050a0c051c091505060a05010302190c03020c04060b040e0601020a0c29040303020f1501060f0e060c 77
    0x100c00000301c1000344c07100040f083c021140c80355081812220040340030b11701d011111200300504155544441c040441d02e2411914005a5040b00d0440303600a070310441d040068003c00f0007901c001400307000040c040c07501d00240340c080380381c0c15141e6504c01c0743c001500080d9035150741c4e9048000c2f4078006000c6c0c0c1e40942400c2e1a2092030510391149201296404040c1d400c0c24001145a40f4900c82c1003000d0806446040c00c001e84050701029401d400c040b941046c50b51540084007140b4a0400c2614002100d40085490702d041010b00825100682c0458141030042c881d03000d8041e241500800c0c0c00e05503181c501420328441c01c080740390880354039090b5080341c901880422040c0c40c2d2801081640c20908001281d82c54074401240c4d80c4e609002d01138088400c560b000d0001421345a400040a1242c4603482c4c0310031348008403080c20b41d016900840c0980d000c0003484c44200414041c0c800d4800c0c10144007078496140c401c01602094200d502102080284108900c00b0b545010546220070000011901d07072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 444218498 1250 444217248 444217307
    0x336012a0c030311010c11070e22120e06030601080a0c030609110703020708031219020403170903060a09020f060708120a0504021212180102100e0d09120206041401 72
    0x4c1c107422115000b0550908400c115280d004148100c8203812000040081c1c0d4a8508103010f0308002402c1d03240c40c0304c031415290085510100c0e08841a9000340c1e010110315512803c05042d00c0d502c42c105034040c6d5014000c008541e0b800003603c07640003000304004214440303002000c40040129800444440385040b400d80d203940036010142500500ca83c00315003040751504e240d1a6207029510403001100b1110700003c0b0184480c055014507c11029400342c101030f207aa4590b81031842e80c06001c1c00c56080811a28482c2c503080040c540c12801449041101e4441600400d00518003000b001d406064001051170030003280302c040300c2c0140e015070308054040c1003002d407600241c0003d82d01a80f06894000202c41284004140c0c0c4140ca07403103c0005150040c241e400101d91400c8984c01c0c3c0c1580920705009464000902403d81e4000042002e446540c2006801400b840d007907411801040e111081c001006031180011a0305a400d400c40b0252907040c000d00480e80380d85008040103400718200d060415 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 444219748 1250 444218498 444218507
    0x715050a2708010608030306060307030e0715051321020609011b050706081806061e042c03070215161509050d030504031d040e0336012a0c0303 63
    0x1d0302c108000a21000d130b0f48101c0195640010744426900c04800c00101e409207020380c3c03150303200fa2078000949117001d03928501c21401c44c0114001b03d000c01d00014100c101c88051490003005007020303031003103d030707055081c1580c00a500400e640203000d01000104000a68000d070b142c41c6540e404808080442210740ca0107079100c40d00c5100700c4001c5101180440c0b0140340300d40f10100451a0781c0300610704d41d603c80e001c0101c59001c0540c0c8240036000c0c0b8000f03d800380c0f03450080d1405200c44c02d840401c04603c0c04032007240101c4030035007490b540e0801e2104400581d10230310741040c2a07021662103510b8600441401800000d071610042c0b24900400c5401d5a2002c0d5400031a0a60300900c262070003400941c03c19401e82d48101d900030009a050010305d6000c03032060f40040450301c4007400004c1d620a00c01c400c9450755000000b180e100d4010b007a00184d15601c03400b0442d454003450300d0100d0520440d2000640100b81c0d85440c50203106003880c20480c0240c89850415035941c11407419580503549040292 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 444220998 1250 444219748 444219827
    0xc0c021005040519170145080c06060609060f030a0209030f150f011d1b030a06030c08010e061305010905060c040e0604060506161401050c03180715050a 67
    0x5600074030701c11545e01c841071240903c800d4500803d81410741900c044004000405008026040342809001a06111031204a1121481351314956a00d07050424641d00d4450018050f910882c0c040024817242d490700b1080d907003d40703600d0b6000c03622602d9010b90760001e40100721a0a07010f20464400c01c40c480300009507288001e84000e00c102d081e85a41005581a0900b400742440c404811000d68282e16401c41d6401d5205410351640194100301003000e50b19584140e51000d903050b1904010300511003100008401016100000c008003c8110411a100c0000800c484120544800e1000500c0700030f40090014a5100c0300341c8100d071400b03840d445400e411070300034464140e810600041090070144910000d507070000b4641814182c0c8190262101d001c00d660450b00b41103041915000306500f4005e250143c401c14034415204d04d40201010645100004141b08a91104d03004111340003003d840c154911205240681d40c84105180c281c0359000d12808041c45040c0610040307101c00c800a034800d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 444222248 1250 444220998 444221009
    0x9011e08040b070914130f050c09030d0201023415020d0506031603080d06050303030406050103021504030b010b07170a0804060605040e06190e0604051f0c0c021005040519 75
    0x50000340c403040b00490b1800014010403074440208504007000e403074551030102d0780d200e09200107e14501c41041c603c05503081940c0c621200c801c0851411150700c0c0c10b210702d8007400001d10085003400003603601c0e0403c40007080d011014030040c040c0c40b051304428000d00070f00c055401041080d00c08940a411400030b42c8480707840d03001207151002140981c500418172019101299001e00c10305c50550702d0340d040fa07902000380303e42150b99803138000455440c103002942c481c601841d400141907240d030040c0419140a40c0300e50500070000c01c070601c0007424106405054810300344809844481514081c803928142c1c0046070107008011a0301210140e0054100e0f214510403942800701c1c994803420310058a0100341071741d4640e0041d80c0010100d00004030312400c442c00c0074078082800200c4010302d90400c03009030717401d80c1c170364000441c1c01c40b5a6514410007001e41c0c000b07000400c011101ca00703000300250f00a000003842125007004503c284d52065003a1800350100074550842c9d4603030f900c450b241441d86071280c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 444223498 1250 444222248 444222263
    0x240606090315010540180b0402090a090c030803040302010b18100f0602030a11030405100c06051315020904150605070308150105042105060106051c060503100209011e0804 75
    0x10b600006070b00058103a24100c25084402c1c149841d01c166207400e034141715901c5000c1c1d41c0c94408000c0c80119031424014035014442802c0c490515006000c0807010052070702c120b450410301048002303043c207501601141d400c17030006903d035141d6140032030141c010b540d0016071014501202082c0e400810300c2041c003c824154079180c0040d515180c805030120035224000150304180080071045000e51880c4103c100890190b900e801c0e01c0d03c00040100d05003d00000010701018404820801c0d1442036540000c0d03c1c466007050000c556481e0511034043c110b01c10002a000b05100c00c01c0d0311203801183e076034040c3c4601c5060603900e9000090035a040000c041d400143c8500110312070080425544400f594103070750b220714150410400040d80c02d001c511082203140e8001140e0089030080c8283c0f40030309904d5039840e40d40c001d40002001e2107814039244602240c5041c0d010401c0b583c1c001600301c2500b0000d080543c440031540010390b04200443c0b4040d40302c882c00c407c0d980d405644079001a1103140f24202c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 444224748 1250 444223498 444223519
    0x10110d0e011109040c0203070b0a02120901110403060b040207050114090c0a080a02010e061e09011103030915090c0307080c012c010c061b1806022406060903150105 72
    0xc050307098070420300902500310401c005545541c180354008900210444c012a0300c1c03c0010f903107000111200300d0b10040a241d0100b2103600d080782036443c45030800c4000c0000e000c074000703003550611140305601c8000c11103940c0d1000700710705407115015030f61203e411034001c111034420094040d03403a8a0482c0d50040078090b40d0303902200d500e40082600240d80c0b80800402500d00503600643c0c03504504420603034009401d02040e40610071b9170303240c602c002c441200d01c551a44032801c001b510040c0e410003032031090340082c020045007141c00240164602c4251180203026140c1402040c10402d0350a416a0140035100700407400b0040000d008803030b01802e82c1e5004a200014001d4000041403109018016500b448505103541c0320f00300100c600b44c0218400501e9614613405814406441d040d00e41c003080601c1840040301030780110000c020500c90021f481200003150145201400156000c24240c207110013148454650200741c60120b40c010b02122560030480c0119680310074244200e83c841d141625 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 444225998 1250 444224748 444224771
    0x150510090317030c0c0f0c03120403050c0f0f06070b060a090506010f0507051614010201050f0105131a03010903120c0e06090d1110170a18031110110d 66
    0x5404a0032203411070042404164000c1106030b0300e5001034003591505009000d4038400040c2440b03c4080a0808001010407110b100241130030070f90000c000e450803000c01c1c00100040341011440b905445002c44030828a85c00220010303142c450748038885c1e908141c02141600c108118411344901504085030758919455541000b01c0079a00200c407860b0000f4000d85032090322901405c064000c103846001560302c0d808501d03200740135014156102e4490988a5548101a560280308407500442280781c03c40441d03042c07101141800c01d56002d5008120755404416502c071100980d04103440344018024010105103041c020190001c40c000c1810f09803034516424205400390809418064014040c00d050100070380230003000042c00441aa8054650401001580d40380041e502c0c101d112a00c0300715030070609402d012010b05004010984091405030f070044540242c000b5800095403502c2d05410711000c12107940e0900000e0102c54a81d41c2c10a4000a01d0220704000345c02c4490080e4000c204880303850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 444227248 1250 444225998 444226007
    0x20c0d030e06130b03042306071e020a0c0f03020114031005061c090302011a0a030b010504020c100603050d030b0303030714031308030a0504030e060f0d050712150510 73
    0x2000280030032214400050315050190161070600d5441403042c0c4000da035140308201503030040380c4c12a265220500510759050641901c0000c03030343d0141c010003181ca4070700f0000d00f0030450082d404c044a504121354000482c420410350310525440020318440b82e503121501c1d0aa0b5100303020480c08500d04080402c3c0307040c801d0301602e200350249543c0d03812441c07800307083c8981ca88c422001e41a08404c54a1a16400030b21070203052092442036000050380c0710301030140541c40340b03020150b034440d0344c211a0400204819480742415a1021140182d83e1081701ea003407454142807956456606080820010900801141c424002450b07038030107002e55848001015140d200c1107903070001040b200a08500740502400186512011000120101220301d4442032282d0f002101c403043c10548420400c801c041e0703c42c2a4800865050f10142d0034041c6242031415140516120081d40303d90368000200090f211b550028200d24081c0c40411003a100f0444181840455000f0b01d4010103042c100c9040f114400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 444228498 1250 444227248 444227269
    0x1a010608071e03020c0a0b15060405091f0819050105070305012303010e030d0b0406060309080a050d060e040f1b081527070e07030b010f0806010c06050a0c020c 70
    0x701d41e60100d14905001c000d00c04a026000300314101a800d00c450420104108641c00d5034074001c041c2c2c40003528001d588400c0c8042451700007401024240810001c44e1034600d846600046c140c86440c2c03602801a002500303414155000400b103105445116284040c980c01444650380074000034000350751214010750550b9028400c4035400c20398201642102154040404400280240042000402c100703644d840c540044024205155030b40b80b001074546030034480c41d001000e16050034406124144c5030040755019480a0200f880380001e01082140341951150001d02000317142000181000d04200c0135004081004890748182001d10b03440d40c001c040300305001c0301e40300380043c0803a488556a003014140050020078014122000c0391012031a0800f100721902d241e80700030100b0170315040c1d40400c0c0d02805044c0100b4145420030600843c1d0f07010050700c00780c011904115006480d0f4100495a02c843e03c440035100518100074050313000703880d03084203180c018560708031840491850104071000e400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 444229748 1250 444228498 444228511
    0x100f030c0c12050a030e010204061d15030408073e040b060f0a031e0e121809061c1b062d050705031620090106110c0a031a010608 57
    0x1c109162202c000d21600040001d18801d00c0c021440000f400005820390b0050340001c3c0109000580141e5200f1107010003205101e000c90b650004074052034280c009071301c00035101034540880007a40f6024800400b06800c0c06c0f6a2040034890914071400c00030b880d111b01d00d8228180c51400128082d90740c40e09015940d50000f000300a64076001804409000c1d950100070381c1e4042c10f0711380115500c80200d10440324240303a03000002107545050030b499641000c000c05032441c4400e1041c42100c50450801080007070340340d429514020303541c0b02e20000603000c0880c280032074240c400da2100c033304c10460581491070380058041079000750f0a07106d12003943c00d01c1040d6035100b59105800301c105003c40107600694412201424818a040c203140c8443d0700710352101125803000049406080200032034017051a40c0e2508620040c404882c0500c009810100d041c416242000024962505410010b2204000c587c20090020561070f50741d1400c00004440005055419100c60000281c01d074010100b6138800c24 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 444230998 1250 444229748 444229763
    0x1212090307080c1b06311d01030212190210050d02030a0911010507030c0609020d05070e24010c030c4205040c12033507030e07030807020f100f030c0c 66
    0x721215a44d41c440d032a102c50080380d000302000008641c036028081f00901d040c45600100158114014007200c40c1903001c03080f0315030b0300c01c2c500c100e8101000e1841221465044615500810381c5500855060040100009241f44000140844002240e21540d40c0e280700c0d042c0386400c94844d00c01990140155280030340420440011000000c006500c40081e143c8002d04401400c0301c5900d846140400a41080d0f0ba40c2d1112800c3c07118141e0076442c115072030b01c4004032803110142e25070700080111812610013024010903c1d80c501c10400301240c0704c03c00c3c42d850b030703c1080003401548580010381e403094054000142134259402100001c0d001f524441d60300020b004c60301034601400044084a030395015001c0042100284080052902030260400003505800648a0a40300d50f0070411901418540c107241c40c2006a039019007010581008607601320501945403005070010540146d002d48800f9448510700981604850b00554002c11600300c51b0340800c420102c02c0c0054561004e119005401c41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 444232248 1250 444230998 444231037
    0xa090603150905040c1214060a05150d050f060a0c1805150a05040506030708040b0708010e0714090301020f03040c0911070602031e07020f0c031212090307080c1b06 72
    0x30b4001e03042940c11a104602c01c10f5070564500360004c020b82101401c840541e11800c142009940811009400081080c010002070030003484d04180b2640e540c400c3c40c055583d012000c414094148a028040390316101540c1080c07404645034001007040b0380001300419101007404294541c45080708094840207054811503c075203800e0114250010460101042004c000202c4c40b41c07154000741d805040d0546445025052915260004590041c40e01d01000035050042140520300400c107a0412514108190742500e10f100c2c0c07486922880608542541c000600c510012020f840214403841c003d4030800c487c161910a8002651038180c00074402c0d500c1404400040fa456600940d00009041c180c0074280d80c0071a5008030341441280c102c0050780001d0900c4460007820321068240d11412405400c9403144c1e860303194098012610780f00e0718810301c030740000c0c000c1c042001240d0740c03e0b41046442d612820001c00c0079035a4001620343c0c414030020704000104034204142602d0070191340c0310050600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 444233498 1250 444232248 444232259
    0x1806090a151203051201140d02060901020f12040e0112050705040b010909090c08011d1e030708030415061d0609060f1011060603210d091401020a09060315 68
    0x1500c41440c00e120701107107149000a07042140b03020351011502c282c603030075118510160082c040100c140e00a41008046298140b8150740d00100070f507a103541102c1c0541c0f18020040102c1ca0440c0c400c1c4140c0d01c034410b1440419403039030044003610446000c0749808520b40c2e00c681ca00d900c1c00c0c1e142c2c1c03001030659000d000d043c88185801c0e00a076881c0b980601d0300d03540172599508000c1c26a04c001c8000e071140344800314203120f134540070701451981342550801602140d1441581c07641d560301d504807c4016200400200302e2003001801100c2060f504070b4a125120b0410307003001102c5186000045501350720704a0001a2206103030040004401035030304074102a91080140310740c0c0341c4010f007250380c02030144c100032005a840802640090055503a00451209003070441880c080340980102c0c03081e4040c000c400309801c40d2500b801484050f0154482d1074818104418020345402d45008020f03002a11952416260540c06044841841d0380c1c0d80840c25504c1d68150201c40458041c1c2d000f07805940c0d000d112 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 444234748 1250 444233498 444233501
    0xa02100c020705060a0807022d07270906020f03040804061107050105040603020a020c030f0706020c0a080d2304060c020315040309090c1413050a090621050312010e01051806090a 78
    0x40c072940500686001160440d03080c1c411271080704609410071070b9900307202c200031409c001280240082800d0100c08603481c40c007080c2250300142912960984400b44d0320f0810010760103803400060780006142d202d007032030300e00245e06410600030600081c20f4103040d4041603000203005000c88406844040c9401d040a400b02c0103917001e6030407031055208506c840307180e030b0303c08000366038082151a000c0c03c0e40d2030503c80c0c000d04080790140c40c14230070780988409000b02c504c007203114400c0100c5401c1c60700921202c0002558031076130394111001c10103000b040000d440703500034015040c154400c400b559032111180040c41d0766010142c8001d000140000130a1040c000715910100c031180315818582243c8030b0029100c0b5084e813082d80b070751605004c44041041036047c164009406080f048000f4480203062200907056000b460b0302c040305503441c1102201c14880d040c030807907908082004865440d0741c1c40340c074070041b80c6500b031080b180200500d51007200e1400c1c1e80d002860080100070204c0e4103980fa42c41440c130 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 444235998 1250 444234748 444234751
    0xb090405070c17040f09020c0d030e070b031f050d0b07141b07091805030703050715020a02070e100e0f04020a1706100b04051819020a02100c020705060a08 68
    0x300744a5880c1503440440c04100054180d06000c041041d913460405d0310142860040707070f001c100310300c1c01441604029940429003510002885c83d0014070003548056881c581104e80d40310f0b02d0840e4000080c01b503148507240540c2007d658000320105d41c0ca9071070051003a00c00c0344400c0501008106008201254411600c0500c40c3c801c4402c0c2070308001003c4200b0131001070030b14003800c09510110080241400c580180015488020700180e15103016072500da4036403080c520700804200002510700100001c10884040c5502543c00843d2254100340c0040d503915024060003480039500380014940742c3d0300c80388201c10742c0c48a001c040001d46400701000342100c0c028000700e82c000400d9401044001000100c1c03981148064010040c81c202400da07030040c406141c02c82e801d00030003000f0900444d00e5040710780d045070150100700901c55131440c00a5007200311096694490074000100c0c410080d0740041e11152030b9203809010440000480b0f82643d68028a2082c15007002c41131009407461070180b00e005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 444237248 1250 444235998 444236011
    0x1302030309040f060e061c06020904061802030a050c040803040302041e020310060809070b12061201180605011e0506030a14040803241c02030c0307090b090703060b090405 75
    0x40703040002050029056407403401c1074078035159a51500300f140303250070300380c1540000064464104840710001c0c0500c444004041c0a0000790f00011120032a444661106000f840d05141515031891416280f001940c070985900a8260600d40440c001e0505141110112000d100003185880d00d55030a10001d403003015081e199840002c9440000d48d00310f4002144183c030031031640102c060030544050448200a411260250300001c2c0c18014424400c080300c100d440040240c111961ba0341d4002441c81a4442c40d0b811203500340344050481081c20010601c07401e03c68181030003640e80341c010807400b1354102440b00305040d00035a010885800c080c0700840e000041000d000c1000328403810142480101914110b0700c0300c42c000304000070b5000c016481507852140f0041d905c8290b02010000d41002c1840380001b84440d0321911200855408004002c0800e2016080e107910030340c2d401041c001048500c282034000e80c40380c0c00064944c0e200c6c0c8254803c1c0c0d00c0400c1c94078200701c0000d003440300601c0005d000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 444238498 1250 444237248 444237253
    0x40b0f040204090b1002060f180a05161401030908030105010e12010911040e0105061807020f12030106020d020a030206040609080c0124050301060501172206020403020126130203 78
    0x4205058aa40c00100098000400d022031804c0f03c44050240c400100d42990085400034018041034050128140f80c200071000007600c0c0701003100103014144688014002c2061254500085010460510f00c404541c41800510b00d6410b4210040d002d03160080c40c01401a0001c000510156001e000d1a07106403c000c4c00c180111010b0070044d500f11409510300740c2d06954842d5120015240501408180c0c00c40400280000d081c210041603100d4045c1810001c2000c1c2c0800107805140300300524802d26440c0700444482e915400365080c3c441d4028007500005006243d08050024000a0f94102e000c1e81035000b41020358494036000f0051034144800c0b1044541000701521851090007964400902c4002141c1030146c0c00c82d036203c981081d0391209000e641044402c2220741c2c4c00c0000070307500100300c0b0503000c0300b641c5e843c0388500c0240300c800d140380104081003007120a2101560141c002ea900c00e80702e5030581100300503014094002020114904110355000070103820041001c4c050f102c0c4090704 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 444239748 1250 444238498 444238519
    0x2031303150b03030f0c070504020f0d0902010311040e04020a0602150c160212031809090d0c0f06091b0b041223011e050604020a0e101b0f12110c040b 66
    0x203819903000b500000321726400422040b80d0f0460a1125000a040480d0708519002c00c0f0a0680c03418001c50f08080c2129070303901c1c00c0070103590194110b03168418981908558070340c1c4900d00360301a50001e55050b80240000b81d400300e0650b00024440c0c0480d401b01d45180256510300080c000294460480088a01001051403005031140d8092842c4481607002070745c3c5407003181c4081c9580b000e08015140c4103589035028000080d0300031a0304030207042c09185c801080450742c01d0141e4030b107460000003041e4910340402d0710144106200d07044450002c1c50386a0007910b540c2c0c000c0b0f4000380500c0c010102010700c60120500095092032540003841180f42c0c3e0664a0000d101c3c0407800c540c1200c500140c882030300b40b1480c1c10080288542540420120340840c241200741c2e0b0024845c0100071401da001f004c0c071800c1d001e101405818030040403040b281007601402035901d0a00100f580030502100c50f1111152881a1140100c1203500903504100c018002524080c04010180005952a5421540000c2c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 444240998 1250 444239748 444239771
    0x509100801020a0e0415030b1f050d11010f03090b060913060c0203220e0a051312051209010513020108100504092009071b08090607150c0203130315 65
    0x1a007810f890390b0f25580c210030340d0001408240c1d0f06031080365100050410b01880040c10036412550081000d140c110501c2200b1480020340e07504940084e917100001414890400c04202000710540600380d807941c90345030b03942c003094099600341d48000703010071091130015085007480701c11207902a07800700e0b1880d42d03501281c6891007120184201200181c00005510102200003211a4101c51403041c00540207450012498020748014114000580d2210042407000902c4a82102ea0300e0b04a002e404114031001405002d950100f10516101640c4c880001c0100e8810311440f0700c0760444000e8002e996009600469050200400701e0142c007241100208083e1140d1190f442200d00c680021101a886240c0040803a40000d41d5540706801c04030800447c0c41d44408111900860400b41000c080e0192410310034500402028a411107004920b00d030902607480c400d10101006504c080007803035402c55080345c40744a07003e40d120000c02401801c20000f80c0900c58501034802483d4001004110078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 444242248 1250 444240998 444241001
    0x160309150b01020613110609010306080d0903060b0a0608040b040204180b09120c0703110a051c06050a0204150c110d030c03020705030c3102030916090908040509100801 74
    0x44084054041c1d981d602a442940c0421103190840c482e6900600348101e80d5a0707450311000034030039450003250040350091050f4040c0c5c0021000c1e00d011401d580c600803501c10010505009031005803a07040c1000c8203900070b420820056400e6454540e6110306540c1d03141c40391031040384041e104a8102d1f68805001200403221805451b0042c410106a5100d0614161552502c11200310441184604020103070b41d4800000f140d80c00c072640700007411002c001d410002580c4d0020b551205410075403071096041800ad00d80005450148a03110411139912100e04100803405103016154407000f803030703201c1c1034907a010307a07004002c41e40700302c1c41c04150341942004100700541a510881c04580410f054808140c0c0500221000d418103034000d0440c003600e500005c283c00443d40b070301003841d04c005800d401d006445488116400d6401c0f103065680e0309100d044161350750b0382c0711613000c08140c0090b000b08159860740542c92199811003040c40c01c140c189403c2010001000d42181c1c19030b0382c1c0341000950b88100303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 444243498 1250 444242248 444242273
    0x9180b0a06062a0f0c090c0e100807020c130605040204080f0709150603050c0c010507020d0f05091e180a1b080601120b0402090616050c06030f160309 66
    0x404008641c0d940391090141908003450b41c49507489510794100c000b02902d000b603000595800c201c04944000d45070604c94a004440d4000e040f049061500c1d0203226134004110f10b00010707040c0c6494a10400c00d480444444d038040d1604801a0000b8401c00c52910b80210010303205132000780c0024069590b20006022a407140e03210300019004090b45403070307200b4203000c0f0a004042d14801440342c900214124522000c1c40e002d000c05240e55200492003800024043d58003030f042c0d5400800107400d004001946e00c803481c403415000240080140319405100c3c10036900313410405003441362007105440151540001e00511940c2143c10381c04a1040c00f10107000003409030450060000700788182c200c03803014281154041c041032000d00000e1020590b40a4007402c0c022165440004421101c00000307000b903c030b280504c0740c2c040d501044070416800510b031128110341c842c074104c82c003c29216050000300d01040301e69013882410783c000128250102c170b083e805080b40a141c0010140429a200b00700c043c0c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 444244604 1106 444243498 444243511
    0x100b041503050c04030519020306070f0801050d020f03060c0711040506130f0b1314010807180e030f07050a0201080108010b030a020103110405120313060504050a09180b 74
    0x1920021381d0003944d444415906d07403000845d0391401d40b802845084e4443e01418010808550042c0700d00d0b81e48910580b1132034010780c0703803004010504441880981e008860400d01c00d10b141d40a11100d8801c540c201803017500c1e042181800811201402d040328025460f0105103e019922002049030301d0303007a070030302281d20002650302c1006003c0480b891034000d00400100e541300c61140d0490002c460203401102d055a99030244981d40d440701c0d209884c444d04079007c62080c504202e411110910580c07004030b80c60a0b10024044a00c0e0b88100015103d50300002c810a086680c440040350052a50070028080c103042d600010f42c9070a16000024141607031420b83da921440e1940540b002400010203201c960b418401c500d546070f9000d220011300d449035480c00803d0040c00341080d103094410213010f244909007070960103401480b0b0b40c20171066509900000c200000c01c43d0421920445 = true := by decide +kernel

theorem cover : BRFrame.Cov 444064748 444244604 := by
  have h0 := BRFrame.cov_init 444064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 444064748 ≤ n) (h2 : n < 444244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
