-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3597
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:07:33.376703+00:00
-- url     : https://prove2.me/submissions/3aa2bfd6-8eb3-47d4-becd-4cbbaf48db78

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 646762589 ≤ n < 646942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 646763839 1250 646762589 646762609
    0xa050d0b030705030a020d050a380c190c060e0714401406030c0d020a0b160209040317100320011e08070e040615202a 52
    0x1340c068000501041c0941003020492a240d44100300f180c80c881260384942040d1a10f114401858101011034617481080e140a0a031078102d00c0c0e00c900145041504081d102c80c440c501580c54001070a44400e00098054580b680c002a044001440a104440c66158480c0d584c0e001d138442010007040c0309149401c18010003900740300c401204800303402c031007001c1c00f80103014868809424a25501030011004407401400e0140b2540101d20311642005030426082072219000c8c680260520889040981d980c80044421a43d101d9261f540e5458030100b0802445a000720107900b04035000240701c1056480307207047c00400e042003030b03446403600e07a0100110078a8082c80049c0c04017200620172021801c001480441c140f5050400380501043c06000c0e4451030403540c100404515804108010701e80c1001d503128180b14201c50400c0500e00304480203880030000344002d02003107414112907003940c800c104807290106151003140c2c155807424103140c500e02c8407158840000080303c0c10104060030015011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 646765089 1250 646763839 646763849
    0x3091e1207030221030403060f052508070305070e03031908012313021b070e0601260c070503030a0b013e03041a09031b130c0302040b0a050d0b0307 65
    0x758910515a80b4031520313290703204140b00024001088000f001540a106400110b41d0070072010403a40b52100074822001507090b044c2d43e00003440044800282da0010000342c0c0b00d409810001503684a16000300c1d4100b0a100300d250300741c0b000140c5c0c00d07000d5242c1041036204000d955600c031803680e00e904d402046540103202c2031500700181c40301031645203454200e56103004c003200703001420480d80021549400d47d4114a8010a40013900240a98146010111342c4a40d082c2092602c20ba4007041040104141105069500c525880812000b03c251000c9401d0305411a0032070361a41000c1d08194010a00b401c00603000c04d10809038111015182c1040c0003502c44c0d100c0407286005812035856005c000d051400410600040002103034003905070342c80f15180b0118100fa542c8030703010202414500f000c3c0000d180c1e49007503030941c40541c3d0707541c418050100d080c0144021410f80110002500607020710b4100416880e03020810301100390340203001e400b05440076481880070b00010414981c03180360714019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 646766339 1250 646765089 646765099
    0x908070f03020a0306020d0b0a1d0a0c12090f0804172820040c020c04050a021206061b0d030203090d0c0b010918060e0d020618190503091e12070302 65
    0x2013040030a0352075000d00320071004070601280ea5030b13002002441095082e0017008644454403030b0181c1c40f81e07241d40311766400142101c0070044000944809425584080302c402e0310191a45140300030000343c030b804e040e595a4001c411b02d03152a111440002104a01200f814580c8039001c20b0703250181d05074101018000c81d0078500c0a42c5207858031204a0b1102c2196104800441c0c890f403861991164420102000d2041c1e018100603000b0b1001c1000359030b00607150212850050002c0c1c2c06000c0507441c0380c0d421610880d009a501e038406403c03114084031034a42c000c0c00b40620388001007269015001144030764a00c1c0c0688122619950040c0c54405403000040c0c04105140b0040c800102c5592240c0015286102d1908030018181d5450f41038850000414010344c01091488150640400100f50001c0c4240007504544000742002a5111030540000c4001900740300444148103060081f60152880a0402e00d0142d80705907900c0741c1e0100c205801400385540c8405102a90310100c2d0135000d5aa00a00d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 646767589 1250 646766339 646766359
    0xe120f0a0e010e0a140301140103020f010f1202040806010512030a080f0c07060905070306060b0a050d0515040e0601061d030c0609040605100c020f010507030804020103050a060f03030908070f0302 86
    0x40c220750104140080c01d0600003041005001a5207022401c0b00906200c000603024a070901c1c140b5081d05c000051181c0b0109180c001440141d46021500d03000800a00c0c040001309510744040340d0203140c41c200c02c98079510000300030076003081c0482e100d03050b80c0f41501c490604a02a601e01d5030359201c0c102040002036680000300c0c4144695841058002c40042c54840c244803803611404e04071280c030103003120540e100c0c43d804c0042007040d0003050000c022103400d55040a00d554006050751159020948180b44d480c0002101440c1c071707022a80d180b6402030001c0000106481d40581d40350f0081c06071101041d0440100710a000d960407a030001c4040190140540038071960500120b604541c8199500c6a250000411580c07a03201200c441441503a4590360b00030758500620507401c164400860400ca820881c680c0400d07040624190007503420319000900313a035281d54050050000b80c00c02d00d68640c0e810000001c0c554844480801e984110741038865240d0b4640340305440440c3c503c00250460351000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 646768839 1250 646767589 646767607
    0x6031e0c090429011809020c0303160c030503070e0a030c1811090a12170a0801060e0301090c03030c17180f0405090712110a0f2120010203090d060e120f 67
    0x5140b148010030220700c40017003e0f403500641c5007aa0040c0e00c10350059440032003003000c01c03142d20308803080e00515801c0000403445076840c000c0c01480000d00c203c0070302000d0142d0103900d0f103c0c0070007580250f4100c80c0c20b200c0e6581300c0688605880345030070280300c80b50922040c17590540340d96041ba441d10b00b0040a151420745042c4003a0440d44406905940c10010b560348000c07040a16802004d800d007459844400d55818900f010305104c0311102c19a000340c2c544480100003070310f00c940c550240c81c0c25060458bc224041c0ca403a444200b924442101844004500c1d08031040c014440c0790041d13601122110f80d000382c03000501080328412906c00c1203580c01a0800c12040481032007072000da0380200c0b1701080010540000c1500b00440b94851903101140610800c00518044045003030b451640c9122103412040c1c0c0c0f80c4480b2409156403e10000001c001aa0218ac3c000c00855665000244c902041c0c2c82c0c06007020802092003558120b29409140303079050720007108800320341d507000074202075038284840300f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 646770089 1250 646768839 646768847
    0xb031e07061b05010204060305101208030a02181e15070c050402130906080d09060518191d160f02100203280e0f011a06031e0c09042901 60
    0x54990b41c0c2d100c203020400308081402070000f0006450b03551400300307060403c18101522400030340c1c014020000c0154444000585110031030780c0004004c0005601c0d41c0d000716004100c0b080c1010059881100113205070220540c29004440000085805203071184c44610b4217540d13449003c0c40204881882c94082c0708d545065405402c1c00070700c5400408005880b09418411070704145c001200f258000102460001e40c01401e030300c00b912140c60600c3c10580800d0403613078440c0c6101c0242e40b154210f1640114414400070b1484014980c0d91107030144240c01c0c0c05503002e070030012f0f141d501d00741c1c50521880c10034074015061428802203650081c4421400340300e00400a410141c0b581842040286064000c1d1032146020744d144540700000040000710603500e50b00c6c0003044004030b42142d0500c09001443d001d900800e02c3c1c60482900c2e07066507503580c041c0c9410020003080e206148580250203000031040004042c00e0400300658007001005103011703100e41e468a2800c5001c040c880e08104000082d442 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 646771339 1250 646770089 646770107
    0x2011e0c05040b0d02040f030b0a151d0a020d020f19021c120209040905010b03010f05010b1219020a020304030b07080c041e03140d02011a1518060d0b031e0706 70
    0x810380050802c1e481c0c49460340d5540140d0300275a0200341c4101030180d014001e216281090700b0600141c0e08440c034004910013091030084d907600720305403a031001480b80c005030f80441d41040304c0040c00319940c040c2800748400b603410902a03007003040c0c40401d15030419030001540d440031903480c9500e0421508407103012945c031041042000d0b0358030b1302486600c140e40c076280528807000f03104000124040030343c5010705084502d2200c3d400300d002e02302401000b400300e00300c0413100a80342c3c42219a186a0301c0d007115001c0010003038101c5000602c00141c00100c20360120142c402d0380c0c41240d82c602c403074a62140c11107140d10140c644a08421040200300071911040c808011010040000f010b80b45a0300d440d65101c1c0c05000e803c3c4106500880141c0100550a11aa0715800d8001c1113100308403c08001246074100c140924200700100014110707a80c002d040d04034403d0361700c02029140d4821840c044440544a0301c80702c0c2d03029200f2042d030040041000c5400306009421300c002880c00c0b5203004021518a44 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 646772589 1250 646771339 646771357
    0xb06161104020301082521021c0b130203010e0f071502010c02030a0309030e280501030e100b030f03030910060e04050a020603100306060b0702030606090906071409030a0302011e0c05040b 82
    0x1030300600008103d42606c0c7c06008407034241454821a18580c0184441034a01902c0c4518005103858440e000990344280c17603800254405540e50091071070f2000c03070300500301e60483e100320b4818002c50321002c60002810303000340c03a0038955500348006400d0b016403d03901c0c0010300d0300240e00f0a102900c0c1c00703071003544a8401c80d03000380b5100344080d5110022440b04060140706451044c2081e16070b1000c1088603101b8002800c0a1800300080c040e680340c8140c8540b503421100d00a5a203501d884000e9640401c0407410790700c011401c1d6503890030b01002c115035400d92110b40e0303150f050170a800013a01c20008801c9900c82c5420001a152122a035800c10070980d00003082c0620302c0444400102c045000d61042102400d01d06240d190f944490b0f00401d460544003c0800380700360b40038800c002c60b04c0d40102d900d9400291034100700388070b4201c0c030000624070b0003010785498142c4200704120b010300d80d0541184a055070b080040106401d440c1c0042400c0da043c8401010201c0c01c1000100001c2c2e03000c00c01414828 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 646773839 1250 646772589 646772653
    0xf04140312070e150a0306080123180102040803030f0f07030e06040f03091809021e0114070201030207021f080c1e03090705030a0b1603090209190b0616110402030108 73
    0x1c80e803082040070b038000c05481000170b5a2214103103c0390001348600c102c14007088003490303c01070072b2164149400100070290110021600c00781c0c00d0070102501600d02804545042c0c03912454610b400d110102003c41d86071801c25409000b28407524007034440c0110304050301c0042d2001e69282d8440c0c46240103460790460070484a6500044c07030491a90b9980c203007002847c000b00c1c030030245004014488500f4000c241101d4100c454128482c0e1704419032070004050000c4054030f0320340c54001a4001e004100001e07411001d05c0c40ca0034220f001f4104003200810383c0f80c6450450f0344070380d00140303158000d8162840c0140c155109010b0b18895a001441d842078659085501c501e0312030002c2402c0c030140e02003c60f00c1030b8882c810b010340289905007c1c0000e01551030200176009607a000907445010142c05802d40300b1900410543c0c0984a8020284c13205024094030f5569034102428501d800d8064400e50b084441c81044070014608bd0080702d04851041c001004280c0d51099501c0d64202c021540011300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 646775089 1250 646773839 646773859
    0x9120a0b1506030c0919060c03140306060406120905010906050105180c0a0e04110f030405060f040f08070f0c030803012c041e0c0b030105040c03020a170712050f04140312070e 77
    0x80c568006c04070090a090394070782c48035621924001d804180302407081c404400d07042c000c000854a603841500d084410506e489020301901042c080010105420b0250507542000c9040060200942099040300c03000c0e101000101c2400071002c80c543c03400e5030030ba100e07503c04101c1d407074845101c0c40c61115403400041001032850107002d240d010b1507004000407440803e021080105001c014440d171a80070807000c1e400321151806685509220040d0940101003d10101c0c01c0700a0268a4034403004031035000b0444250261070f0300f011009500244a062528014402081c40928400350850540890f103041e00000d41ca890b925404079180044c0070409886805c514900494403c0905800400c44045855560b50400040c001610a400040406d0500412074000b20603808400d060f035081c42201140c0300c3d6250145d084031f20407050b036661a1068109000d20241c103075131015203800b692007162052015101c0c440e14980b24018107060308503d2000100061117a07000311104119200000d1071800e0b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 646776339 1250 646775089 646775119
    0xa05030a24180b060a081c03020a36051e0409032601051017041101020313080102040f050406080303010311061c050405100204080c120309120a0b1506030c09 69
    0x1840c04082c8080d0b031000d41c220180102c40c00c2c415014005000d81074050001c0304405006a403805805841c000105907000440a00040c802d0041403540c1c5504030b03500241c9402a14040b4907040d040160740101500044005250702c0c22444d44025269142454030201e1000340c01c000c000c1c0f8003c08240d0038000829100f14080340b01c00380c0c0e442c808091b801a00d40365410503060041c0280c01161500c20b2045c0340d0280901041d00940480e070003944207054401e11018100101e00350300840c503c0c00c20002181c140843c0f240e1041d009031007911381d58000c00682e203640b101040143c1e0f80f28801e421298008000500100b82c806450140c403030301c0649100e1600c50a0000c1c0103031805000c6040c070015590f441070004002041c0040441d4000307881c0d081d0300b09814554080d4032042800c952600c0350382011400040f0413000d206480308184010704940c0c1003202100c48a4860303194400c1120400800d90014503002c10420020161103009009079066507620150104a80d00552505034000454400650 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 646777589 1250 646776339 646776371
    0x8060601030501152c04150e060301090201080f04020a0315140c04060f0503070203070f2f0f0409050712051c050f07080307031811010f02011a06030414010e010b0a05030a24 76
    0x40c1c7c41604550326007014900710001e220010301030407c5200f641070203003640150703a01802c2d5503001003003500c03400d17595200d9100192120350305074030060220003d4a4500302281050f80300456100c8a004071804030340c2c480f64070b121241300302e015403804280407085081c4102d11504c00341d58020039500403a480c0091075100e219414000309006c490703803852400b1000c000300740902d50b0044040200303414440a00f440000922126070601898051651182120103126040204200400b8203003066501d031003a6041c40c688450a100e0210741c1c000c1c624100d0700d1943d210b041100d00342806004441c0c240a40ca82d07a011403540050190000c140c3c80c3d11894a07000040f100300e00460348178801003100340091400242c00b0794502081d54007564940184c0000d800c117205502407000408840e42f59880c0e559140c150281d07100d003801091590f1a1080d04040c610055026001012040301d0001c403899440040659800c200b81c802040603070714031212280d02d420101c000d130310906a090041138403000182400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 646778839 1250 646777589 646777601
    0x5070f03120e1c0605090118050a02030606090c0d020310030614010306050601051c020a2105010f0b07030f080403120903031e06030c170a0c08060601030501152c04 72
    0x10303074120401000a881c8941144001c9910001981c00404a81c1d40c08042d1041d4205400c0240c05252100c0000344803501c20b500c05803c0c5a2004808031100780d81d13080842d981d40300b0340781c12406845a030006c2081460310303001651240340c90101c1c0340d28100e15080390201139000030780b04440203624200c0c08800145207008100b00c012105108204540c5035082c0b900640b580603240c18180b00c02001602c1000c0ca0011760480b07640c10040b4096038562011004680b51807803401206840307410301415003000d400e1034000c01d04840843c03000000447e150488080c00c1d10a107070004021424000805070f6040c0182100c640c003501a04000702e503811040007000644800725070880029944204680d000000c64a0030750a09409960404c1411700f10790320000c42c40d0881c040ca41d00701540404d60045000200141c103041c1c3c1c2d005420600c070030f60321204140e0302c0a055601e180401d00388000440e02014804130342c0d00320051656150070b520040c1c4125020701c2c4c0061012000c3c40d02100340300d40300b0780302e9010b50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 646780089 1250 646778839 646778843
    0x3040b18150708070e0f0a092c100608121209100606200a030e0d060f06030c051002060610050a0c0501060f03170408060f0a14071d03062205070f03 65
    0x141000e1074126001040058100c65141c4601b5194554805c1ca13100c00240d4400e4400c0c1e4100040c00392001915844c03403c039040d100604070402040e15142c40180070a20305442c1c015228140003081c1c6450345c040e100c04010790364071100c00c004c0c45a80004400c60b0b580139040385101c030680d100c1c149001254810f95000da0030510108034600b442d526200074410000c01504600c4015100601c0e07103a40c02800d044041d2105440b40048082080602c901944044c41025000c24100b00303481e03507450850074103c518030580340300b40914186856440d001040709481148014071a1010b0b071081c10782503405410820600c81003000e00740107000000c06c240b04032006807a160000443c2e5916626100c8466440041c0c03155100505200802c02858002026500f001001039500040d0369440703041002001515003a240300c00c80b6000b881302c2c494001a039601d05201c0c283d03c00101080b1501850343c1c804058442400031081ca043c1060507050700c1111110640c441c2041c4d030442941d616215022450941007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 646781339 1250 646780089 646780097
    0x1a1504050a2310080f070b0f0c1632090a0b0d0b040b07092306070f03090303120c0504140d0507061206060f020a0201200d080f010b03040b181507 64
    0x180300500d20400881c100804c0d41d140105030b4014000c540d1500d41c101807040d540f04260105111520800b10010780390311011000843c0d07610000d0794005143c44d00188200c03e100301030b09079000401905803504107010010201c654080031060410701900d03000c014400b69545603103180c0c418090745c89902c002c00080c0160607041440c201801c00d04140403015007900103004588504104101c140000b402001c020b6400140d0168181e0011414606c24014007c0888903000307035040030590080c1c41542a0b90090f030f15581100240e6148200703c80030f160503540401c00500041046d5007001c1914510320307002908145980080750381d990b203843e03d6a080403010911481561103111680c2c4145401000c00f4500501485507501021f92035504202000c0d041002030f00314032096046440c0c07010045003000e0100c807004100d050f4010070b0070b0003d944000031a4454000025416a404280ca0040d43c0000501050b51580c0c03078145210789580c4541e150078014446405484056481160300c07411035512 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 646782589 1250 646781339 646781341
    0x27070b0c0604021e090112020109030f15050c130b180a03050d0e03030304030f11070308030114040f0903140309070b07060b1206010f090207050f010204080a1a1504050a23 75
    0x4100030141130070300c44800c02070101c501c480d08117584040c581411108411000d0702d40030702600040b20504040d4002a00020003070040b9001c000f1480c1e0507200c00c05400d681000191114a944081c61058000650f448407480100b4440201e07048000c00c074985910200100072000c0d140456181c100c203501c10703900c0d50800b5000024464003d0f414219202c4220f002d149149041c0d41c000e400305d0075071107241d010804040d50030751400d2010800c0002039074100003d152290303236824482081500f0300d244a80640e08020306100108554000d101006615482e090f000759054000080f1a400060244450344141c80000488045810040c4402c07805008082402145641070010703c02d200001042c3e0740d80300c58010001d4024a41d40304055401a041c00350352030a80d41001d81c5445000c03500d0035a20b500c009400298198005914440984504c03031070b00d0148152400d4600c1c8080c100c0b40300800058076482040c20703162950045610500c401c0001030840c00c585c40c880a0b42c0c05042210ba24065a14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 646783839 1250 646782589 646782593
    0x130203010501180506250c090e07080a0503030c0306150304030302180d02011e0201060e0f091507050313030903080d05010e090a030c020607020301140a0501030c060827070b0c0604 79
    0x10b040388242c00c2c19000a0b04070f00780741c2808610648264100d0f00c1500c0e03440c120070f40c06000a00b045c000c40e1500300201c59180c90322034035654010300c2c450b1b046107134070b202d48980095200700105502690316040302c040c5040d42d950f0620006954030041921358070210070a00500358401d90005540038500a0f40d00685030318180c1c2e0010a5800d0040600c0d118030100030410005030713070191400c010000341c881c502c01034413800001070f40904095009034612425050400000e40780f943c1c11688281c0d42c1004540416030146540c4455034030603103003003000540820000341d5a90885014000750b901c03925220f081295a92a451282e403c91038561420030f441e40010011195030f4142c40c1d8000c07031400060080701c8403568020345201615100207001d000c003c00c0440a41d0780070b40c042c01506940900d105070764a05100650001c00013400200c80d8088109000b00f412885542c1e51882104c03004282070721020f07101018a081c403040e1103010b07914407480002017452070240002e05800c1070080d000b0001801c0034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 646785089 1250 646783839 646783847
    0x170301030507050a1d190209031912090f0e04020a0e0c0c0c09010b160501021201030812162001111603080603060708061309230610051f030605130203010501 69
    0x80c0d022802000d03541c28044030808080266540007401060060000c2400c5c9011001070b000300408d0320750501070211841400b00510384001d480e94802c611620b00714442400c1a00d60380740704e010304c0c0103541000300c05101d940510361907a90058002024414419610200d91400e0441110b00010000e000f10720050f10440c10803800802e0350b0100c84a2000390704251109a05000c0d11100342080b0943d400014103020081d4100c1c0d0ba00b800c0c048441e501581c403403c1c0314165501c100b5100d0070b07203401d010000341495104a000e46c0d900344a0b5458040c0481403001883c8100c20748507544105560b078465054002d0310140c020302400d0640840340b40004880c0c10042c3c08803800501aa020340c205c0703000c2000050b172000016610942c21a00c5c241d4008146051000505014000805080300c0c2c261780d01c149076040308030074a03141107181122080d0365142e0030700c00340150603c00c01e03070405d60382c011081283e07610300c42100040c0c0491500140456484000a50300b0b0103512032601e0741d9a0010051090b546c0c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 646786339 1250 646785089 646785109
    0x904050a121218110a03110d060b0301020a03050f10080706030f141f06030615030c050708030109050103020405060607022d0303070b0f06190302040c090b07110406170c0d17030103050705 82
    0x10881c5e40039042461525111031a07050040f0181c4201400c41c03450301003001641c8807001d0303010f01070001c40d00c45002c0440540207190944a1070042206140000c6200310410004403e607000c181c050000e041c80d10105a024102c210300742801e6070303100d10420190b208400300c014450840426055400c441c3c10b01410503040c11500000c0405083c80c40a100501c0080020519200c0e2843c00043d40390150311f045a603402122001442064000000680d44a080c0c0000b4141ca000300c0d400c000940703440041040a00c51100c000f03412a520381040881441c0001c0103c00d0703120f8800007070307144a180c000000e08590002104444045a610902030303404248600d0940c0410255a00425602c00e18160a200581745c80024402d98075018140b004520980e030a000514000800755103840807803038082940028400054000da180c40e80c00a0f503228030b000440c1c002d180404c003030503071b0b80004000d1001d0b44035080c609640e9029030341e001070a000c82c0000194021400381025005003400e1400304071076404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 646787589 1250 646786339 646786373
    0x1204031b03031b032721020f1b01211b02010f050a09033618110405060d020f160305071a0c0f18031b0405060904050a121218 55
    0x45440c0710344025034407424000e40039468510301d190001070a0301d4502a102e121041b244e82000c6040c11400380c103a00050b19800c1030741c0300000d0b500180350040620411400b1030949600041c80e05007a0780e0b000c60407082100300301d4600301c1d02082c20318401c45c102e405540e4128401c40140e42d9200742550f440050b00c40c06802414201f070602c1742100c242c8000381070342195900b034480c0441140c800056204401c16515000d604419262106560ba20025900881c0d40050340162400d020140c5201c4405400702c13030a039407000380384e50306010b0b0308080000250031140c0c113201000300030803580910000c140d5a1118591081d60f641e5030f110751038a040114000560120708284407000c0038840206d10441c20758110048480c50f194443d1190460b04140c024000344268142c002e01c42c07515a04c8454040c2d418400c03074162024030254076040706002c040c03903048801071f101e0741054401c0c1c0001142c00310422502132003890b10b4802d08a10391140e508907410480170489009100703843d58200005000350a06481c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 646788839 1250 646787589 646787591
    0x5070911091203034003050714060712021b030409090203070f0e150315090102031e01051810031707030905011b140a05030c030301060e0a0b1204031b03031b03 70
    0x410300f401000c08080645c400b01991810128651900380070798a00807610110f4040c00d911000814100508240e00800e03043d680a4050f2001140541c1d0000b2a64095140c5a54000200e0f150803d050029003060324229552522007070803800700c0000b00040e0002d13020503c1c0010711400648105842c0680c0b66000000703101c01c1c00400c010400c40800c046601528908241070070440c4140000d05102c0070784001000000300f5002d0003440401540034610600418a41710101280d552102e18800e009100300380d8040c02c86004a1195203107141081c1d04420200c00854009803650741d04800d628955408070146c4001154040030b04d513210305400002e10080c00c180e409000707200c50072018603000c2000070f4005403400703245203441101000f61706c0c21590801c0c01da0791a440501a001d4480c0c0c000c0c810080055155203403a2810300d00814100c1c115032003070759568901030541c0c03100c83d40943c00800590031300040560310500c0d041ca50301c0365110f0784e100e03640004107880c81070a4524500f044010404c101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 646790089 1250 646788839 646788841
    0x3071d0112020f1b0d120b121507030e010b091303050f0c030c010f050112060911030115051e03060a05061c030201051608090a0201050d0b18010303080615040506070507091109120303 80
    0x80e0b5004030074401044442840840c0d487c200d0300114150b4000110380000900c0342140150400d610081c00901805559030705219560095001d182601c40c49507186500c8025040820003a501044e1448070306482170030302d1420300604044840d5960402c1d00d0300074185e000000d9104070303000281308800500c4841c26041141d54140012100326609101004000036540c0e0003c000f072080700350f004600218000c00904c10440404842d00398405140700e0305029100310000d071820b00044040e40a44118003500400180e980d1000a50243c00041c0c105500030814403d0054078207181000c85050600030340002c500c0e800d001041d030f83e0f5000c040d00d0384030400112406112074007501091010150750246489a11010030304051802010303083c03070030750b8015000c400c1c2d0503c80f030950046904807402a19600495a00c60b818000d0000148010585a800c208030510551034003034050000035015004498007152603520103002c80300510320420152001140684e8a8640a01c0c41c008117070f240e801460075 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 646791339 1250 646790089 646790113
    0x6010e10061b03050a110601060c02090c03040809130b1f1107050a0501120b0607060903021c080a0c0e1302030a060b0403210c081309050a0203071d0112020f1b 70
    0xa51000b00d500101040030008448402c540710303001c1200e00e06c01c0c20040d07580950707559202a00448511900300c1c0a00440000071b800f01c3c1021007960f10580c0c0140d015850114070000300301840d03d5403030070000200c0c0d0710003828801c0d48030341c481659a40080c0b03107030902501800340c1c0038001d00d00b0504064002d43c4560300070700c010b4450100300822200300f800d1000c2d04044100da00c04c040c0c520140340039000389010071400c080c002c8603004041c0d0b81d8042e409481300441805017461040c413401100d0804a442d59000c603043c032103954040c84100016140240e03072521190005105022000064400180c002c0180140c480c000e101d0301c401052500041071030325240d913a50440c1c2009105119485513202c0c1c1400301c0c0340d405001c044042661144030030703a80d8003400854111441013801a00e182ca441c000000f80042400c2c82101c1c000d92007500c850044038404e4004d45942003c1c07034130b440c0c100040d0140207041c400c1a400039100c0b072030b28a62060389a018894100845600505028241d1b9001a0540c85 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 646792589 1250 646791339 646791377
    0x10b0d080d02070f0f0f0213051306050903040e041a01120c0e0c0c0f070f0503070e0a020a050408030a0302041503022d0903190b060312032202130231050f1206010e1006 74
    0x2003066210710040b0b4cc0f0742d6030904640c11406140d200d0385001107020100010040002241c0350304034041c0c0e007080241e07600e41105040100c01d10100a1048500c548140074034030800b001c0d540d01440c0316811610b840c4000500c1418241000200b04240d406820284a20030710b01003040041c0038154010104030b0702d0038883c04290000508840300203a40000c4c1002d0300d0740700d50201d401038003c1030100c2c0e58a240400e0018001e6205115440326041c1000c180e0b40003074400c1c021100d5a03050340c00c008200948404201341080300c0300380112020442000464050344092101d90f0b02e180c0c850440d041328402c9400d010101e008014005442900134030100540c603c00c0c032003038a8121160880f1008554040780c440d0000020110f0b0195003d0015100120300c0802500240290500c00030744098000255209c41035000f00c0d06071a008101140030188180c0c10000312102c0c407501c0040c4690701014a10200070300b40182a0000903d42a2a5040241d801f0602c50000c000300386910302074082c0450700740854 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 646793839 1250 646792589 646792621
    0x10501020d0203071b0e1009050f0403050901031e180606050d0309061404122f0a05041503060207080901080c1215030f0d08060102010b0d080d02070f0f0f021305 71
    0x501c070b100c19408a40c12150170240210140c03040c013010b20b81a08004104040070340c028400c3c80350050400000801b0802c17000041409103501d91500c0d030800d0700e000010350180c00340055041c3c44a0320310f6a04520040580112500f101a40c010200c020801e4104402035030742c10b800050154540300010342c0081e60002544040700d003507140c44420084075000c041910b00c200d51041c2c11043d507403c17681d4180f01d440340c1903c0c1744010042520308511940140440d0b071040034060580d000ca1621010001400d082d04601031201008007000035590716a520481240c02010094615200101d010000c40d45c204080940100800d840e45003071a030308184070140200d0040403203006155001c603ca0b031031340b01001410f003040c1d410010380e08907003199a802040c10f00c003294283d00541c01d10f0964221070038110150042036401c4060300f490141c40a180c20083d6100680803183e0711641801c1130042118555a021141d1150748a0034003505070340104200c5e001b4204003015a641f40100780511207410030454 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 646795089 1250 646793839 646793843
    0xb0d111c0c030b0c0706020307050a0813050a120c02041a030d1d0103020702040e06070e0a120506013f06140906040f03111617012007060207060212040b010501020d020307 75
    0x8030a082c4d46030000b4030802d000e201c10052000d80040140f00ca041d07008000760103001465039595510742d40303451003a640c0049810002e0301513000720b006080820111010420380807542e0820b140d0940407580130078100c90098080803040d02c03c120a103007480c5020700c41010b00080c00d24040b25090382d081e09040c16540413249681c10f0641c00a051021900e403500320b4001e4400b41400d03600c1d40d14008d1005410040d440e911540b00d90f407100700226011400107030480c881030304000146000d07820452194681107405007907511101003860411a00c0500302c2e4402040d2012845e101c503003c0380c51a200054a001480e1910001c814808004405000180381c65006400110040c0c4c2d5103a5400d040e55045140c40030407825010f00403004945030b908244039400c0ba0744541451012840e0085503500701c03030284183e40744900d458000c071a0400a07880181201501600c0c00524146007a079805049901c85541e00c981d81c9800070801080c043d42c408040c1c011706080c00900141c0c600400b009440303100799440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 646796339 1250 646795089 646795103
    0xc1009030c06050c030d090f170d0b0405220809030a140622020409030e09010b041403010b0904030f030f022811060c0f0c0a081909030f020402030a0b0d111c0c03 71
    0x344405102903200104001070300050031541c801d00c00038409c00158403c9001040b42030604804c44c41034100313489075500c60a04042c0c9031408211601c040c01c00c10003052003e656070341091000841c3d80c1d07414080060b17100e00c507507035454070041a0b128003814034500070060170110101c0101c0d8003201800782c28a042c8140d04681c00030381c0c08520318054400030301200d02c01e03802546000012640880c40c40080c07040d0740c0301585101160300034208040c01d0f80c21400780640c00c005190042400a0302403031041405518500f800304481b995000340e03104a030440d0300c8900707002d100300300d200d842458010448000c8000a14104015660380c41c0443c1c2d0322000a445002d014400184150400c00100151080c42150340c00b52403404c1081e04001100e42c0144485180b8400e00307850f40c407a5207005600000849034050300c24070f88180503030200002504020400f01c4602d458a65214190342d5614003d800f0f184103044103001c1e00d400c1002d104807444908201c214071f00683c0c030070300c0200320300030748107000c0300d40c4403070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 646797589 1250 646796339 646796351
    0xf041a160f0216030803060a141c080c011b121515210c030501081c030c030b040c020d08070203090616050c0306040305071a1303030902030c1009030c06050c030d 71
    0x4001c924100d8a901c04801c01c903c0c1200100c100030183c00214001c900859007203038429251451a10010115101d80341c0c0311600c605010584414019204d420344e006440280c01c20144c04201d0f130030340d1212001101c020708800c0020900980000404106d002480002c104c0c54845100c14007500c100c1380500150309070071030342c6900a54440c001b25060344034080b2980310340c1c0400c03160700000741480c4504103011904250012455203030014041024407003000c40c0021003120054150300401c9100508070030143c60700102e030b035141c80710f0240d0803000348140d008000784000043c00400080d03001c0d001d8011034101708036841c0300c0ea6409007681d41111003075950404841007460315502c0c212100241c039030140942d030100800c0c16003000281c4000c1e409a01031181f21034440c1c02c840c50004044a10401451141d00c40b540072034802c0e801125598806021a88055500c1c0000b440c2c204400d02c440c0c0014500c600103000300103c000001005003481e04000d07003041032807500d00d6181e0080210503d05a43c0e200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 646798839 1250 646797589 646797617
    0x50d0f051603210f0b040b0105090a060327050327010f0806031c1206060e15090a080f010c0306080c090c07150903030e060702060f160e03060f041a16 66
    0x71420b030710080203004080040101142c412405440c1009004d07104901e0101f83d610310b54010412200c0c0e1b40d0005200182080c01d0900980003081402906020603240400b20040d02c01690340404000e03004400560b2030b42501240080207104104000c119140c1d040640d4100f80d80240280044280300d041201091b61110042880d1007000504912804c000c0340c041e884440d00450910408181d103003041c0039040d19800241c80e401300c003090980d0018000704034a070a019807040502034601c4014406481d059a415455261517521044c00b00c659640e0280400c3c403030781600c2601d0042070420040d04110000c80e00182568000404010140704005050420841e4800c100c0001e04200c8408110300400c60400078024801840a1085031103020003103031405000085c0d41d44642c0c210f8604540c02d596802c0c8002c0c4080490843c0740c14009a425565100c0e035083c00911b00c00c1d02424450340403441d050404075521304500c9041d1400e01007400611040e034640e22202c1002d000e40d400c0c01001d4032140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 646800089 1250 646798839 646798877
    0x7060309120e06190c1a010602060106021f0f091208010501030e060402032104231011120f120406140f01060c020915030a0b070f03060f0905060d020a03050d0f051603 73
    0x8210010702210b080101d06c10403812024025050322215402c4452681e2100000ea0b940c0c4c4030034081103600c408100c0d07203883c01c20242d0005600e00169640c04285001c0a58816046a04601c1d4600206020f0001030105503030500c03038403c012524000030141070030141c0200f0f841703c0c00c8103008080c6075100c018002107d901070702140c3c010300b00c82c6011150808401000c40f94040c1c0b64140501c0f540200f02e41032000303441203008045d5000c84502400b0311015400444072075900003000708041d4117091001c0d04441540c40c100030301c030f18000c20000c141182c1511000c00380300c0005140d45204076210005001543c3c1c03002d401d0f04d02c1541600d0107601612021110021600340030702d1250f061203031425050421407072808184c010082500d07002c0780381c07507410001d03010786049015480c1e80024441080000400b207800041d0040009009035405080301c1d004541800c150f42c10988a80d07100c254038606003907004c030039042c000c841c511f40785041400c4041a442e2414058101074108015081c50068a0a43d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 646801339 1250 646800089 646800107
    0x1b150a1d0a05060408010504020411040305060f0712060b250b0712022502010e01140d0f02040806071106060312160204060b03150411030907030b1807060309120e0619 73
    0x426494884c0d40e604411030180c14100e404074080c41c1000f035039040b1031001e001a50141e0303600a020700459968074110f0b40d420240145001c04010310085000407001007445004050241003c0495549255079101104c0c0884c08210741c007080c00022001c00403c60203220141c10003901e1030a4601c031601200075201a001c1c80f800e040a0b1000c0b1100302c1180812110356100e124400c0c0c80d54a010404d82c030041d9140d0400e207030035108035001007104d200b1004c42d9600a10020a08440050400d500d42502919080080300c0c520003042c0d100700700c0030841d0000c0003c182c0c00f10045001b4100315050703884150050041164600300018007034902c20840d901c980181002d231003220350342510b03440c048031b02c0d6120302000b824450140d868416a025000070200890b40304850b141c004003c80d07861031341d80120741e40c00107006c2107200700e1000811502680900259000b000c0c6035801064050f40e904020307003140d03002c280080034015000c0c000141a1187c4059922461640d142e02010036901c083c1500e01c203203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 646802589 1250 646801339 646801349
    0x10b1203131e05190905181027110102120c1c2102130815040807261e16030e030c0a0e1008061012141b150a1d0a 50
    0x20391115291001c0f0b8614a440111909042d0a11007501e800d8600b01d482c0302c3c0781f103480980b60070125103d424803105820407001190f21050b0450410100b240e60070310401250703800c40e0014030401d801440c943e4104808400b6400742c11520703107440904814150b651540032582c000c0c1250804034605082d000e040980c030709002c074640e8801084900040000290b0055611090240d40003002081505002440701944040c0780210240c3d07485588480034650801e00c812100e04184402c0080c20301c4c40007201610000440c61100d8a4040c0c4080300b0352407100f0340c114403c00b800203100c8000342980189200c06074a8150a0084c282240b01011a00b4800303c407401c1c64001d050740c00700045521040c5c012501c24417071341544a124035114480c01c1d1b29020241c4000d007200c11001c209001481e081c8608160a62041c80038000b02d03030f00c43c1d000d20300b01159a43c00d140042c0c082c0d440ca58460400c1202510610034484103d0718042e10035101070703d020000400b07942480301c51060240641c1382c031410301c000340c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 646803839 1250 646802589 646802599
    0x1507080a06080d030902031b060706050c1c050603071205060403210c0c020a0602010603080d0b0a090903080603011d0d120e01020c030c120711010f020a14010b1203131e05 75
    0x203e00b5400303000b038285090300f00e000340305480c0c480301045148601c00c040f281d0020262071070101540c6a000c0030b448040e112140c6010100840e20300f4158411031803c0c4507298000c00300341407500c1e00805040041e0340c0c1c0403056440d034192180000900c08190107502c1689402c00030b07040582c2d00c40400ce100e10b07151400019910b080043c09903113401c0907520800c913202712071580312182c555100304c1c00c0c0d07002840000c0c09594180000303405d070660350300843d04200010f05030244160340c4000f240140d4494a0007a0301094200d4144034003800e080c0600c0c801c1d01417002241000040c0301c0d84c416517603500c10448408006011040a08940b42500142c000d85501c90081d0b4640381e05201c0c0a07204d6004c2c2507006000c0c40740102040031034001100341c46c94a030f000b018500300b9030742c001e0041d03e141503018142d01c218010601030100103022860300003802441700e0000100c2c120110b0074440484546d0058501030750007403252280c0300392100508010344242e04881055080c2002c82040c0c0507965800440d40700c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 646805089 1250 646803839 646803853
    0x1080105060307111b040515010e1005070501050a0b0316050f01120902060c25150806031005010305012f0702011b0b0a0c0e010f020d080705070510050105030105091507080a0608 78
    0x2032a841e41c0c10f01780c040c0858040019444105040a50040c01c8081c240030403000e0b11045014038080f84040303282d5100341071292400c45150384172802c441c8200c81c24860940c1d50b0107440f04e241001c0112080c2c407150301440440044c00c1c100040d003442d403408900c504200c50f4a0300b80b010300d025034024070b4a169003d0030b000e0300d0748901780503079448840c66a0615801d048140300b40320741c3d0000b1a100c20490359881002ca50802907414115010300c00101110740500c9400740d81031081590307204440c000d40c000c200001d02d644641401020441c030300e510a03444034415401d0605c5c003107a940b00700c0b0440b0b0350900300410032594000c0d64100400c88480c0c050565010141044580c01003a0009032080d1316a40e034082c180c482c81c0005546120b025001c50340180d1012050050f00b038000d01c0b4460b001182030401d03609081d8655680c1d480c0080c01c4210301075641e04c0380c004202908090045030b41140d80030016200c0c61004007511213240034000d15031001c004510001c2203141c442940860041c2034608161440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 646806339 1250 646805089 646805113
    0x3050717011803050405040203101205011a010329030c060d0606020607110a1103030c07140f0a0e070f1e18051002150a110c06071407020108010506030711 68
    0x1040c021100300340803039401c049480b40a45000700c0c0c0d41081503071503150b403410581081c00b840001d40000341000030154001c0d101003440f081d051092a5400c0c462400855400403442e0b441d46503551080425050500340546003140410f00b40040281c2500082516044c1d50f1990000c1d150940c0e104059400803000642c402c2d04a03095001442034581d141c08603480ca40f00c1400845101111020039a6207400c00b43c05c000001c6c5928000303250308600182244d040003007440709107080050366800310030502e0101c0f01404640c100108100b0302208101c1e081041603141c0b0408080c0303003400411400400c8a00505983e0322801040351541c584482c000f60100806801009000c0c030264002048803501c092760001002c0c600303a0100f86401c1041d03805040c60040034841c1d61407001016186005035a103a0f02039040702d60307604010f014804030b0341c001001c0c40e041030000908a1040a411510100f50401a12000d43d80140185044900507600580d59644030300c011240c04804041100c10f5000f0315200c007070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 646807589 1250 646806339 646806359
    0x30206030403050c0c010815060901020c21060c030709210b15130506060d090c05300c010c120315032001020c03070e0603100e01061a12041407030507 66
    0x10920262030131250a051140c0040d680700307c007141d0010321004281d80360902400d0603c00b5040c0c02006004540411075440009010034079255401c0d00034021100c00034000b020100000c0d90416181c3c0403051850034810002001240580148001d58581101c61303001982800100440e941e00081c82c03041c1410440c961110071110049400e114070040b401049032590f0034440c1d14080c0100800c3d00749000c10010f05040035007201001030710540c40141001445458954000710030303a100d8201070542440c41d07612403640100c00b4107441d13a00e9100c480030300360990b001101d040180e0740080e4080b03a902c4540030101c0180170314043c14000b17910315010004c10007000c03421344000041c10040e05899500580012a501d02003081c00546c142d020071340420024810304c0c01290091405810744d0703040d01622101209a4103070645c0200300340e5442108015050021241b401800710354140d05d85032010805002c8050600504060702221800301c0740b51080f08100688001181e110b800e461403159681240c41c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 646808839 1250 646807589 646807597
    0x60309070f06180b0a0801030b0601020a0506090a0b070f141e0a030609060902070c0e0411030a0f0b06040207110103110405031501050f090f04030e0103061d0a06170a060f0603020603040305 83
    0x2102c421403c400200784000e20405507880c0304419980e640f102e80ca191600d030030b000c01c00f51449055000704442d000c04910140130310781c420100c50000b00003110582c5082058044e0040041d01003140074100715204a0384008c00e9550300302500006503c0e0103181c88041990000d01905060642000600e480d0f5542c154014904690704060100001d0350baa8001b007080e8450380400a2207980030341400d00040c5000310381150024040c0c050818a0f4000c00007291900114240c10303140d04a60390800d000304000c041c1d240d50301031820b45040d81464038be550b0b500204d114107006541070548070684d8600c09130040d0266401030030001d0844039101c0d1050110710141100380901d034040e40341c01c16500340c0fa0805e5075050307010760f0340645404015951502c046440c01420341d101c504141d110f00002030510003c00000c210030030f00c10101c121600344652440112204d9034041074141080b0181d0341c0b100075020429100300f903080f58010540c402c0c103540070f50051035a40c000961124022090000385030f803000241c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 646810089 1250 646808839 646808867
    0x120203060f331c09114f05040311010f02040504180803010302011214070915020d0f12020f04080a0201090e09030a0507050c1503061c050309060309070f06 68
    0xd08442504403a801100b48504684807078040c51400d501211000c480d40400340090045c800b0713141055030300000401008151803059059030780a9200c40c0c1c55801d0941e440b07544d41a80f1b5100d40107076040c00c1440c4800d514040c44c1c078403a030b5645c8001b500741400344060010340b00061000308080e880c0084074034029041070007000e004070300c2c0021410961891064981c0411307001030b8034505681c40c580c01160541c3c00040da05a045480342412105800000c400a014030b40d940c684500540c140804040503c452000480440d48540103001400e5000909a50035440910345103411080b2010f109029219800c03941403154000100051001004118110880c2c801d988040c09e0554500c0070842c240820b460312141500708211100310340e4041d80061060b0752144060b9158250120b0008010946241e030030380203036800004110040c50b022541140e001c0c01000000c20981c266194180d880c0500342c0741c0c03400f8000c000041410400304100100003071120b020380001340760311014014a400ca0150742 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 646811339 1250 646810089 646810159
    0x1050906090c121513240b040203060a0b1e030109090c06090e13031724100503011403070806040c060906030c0f18090614030705010807120203060f 65
    0x140249481d00c0c12030718040b4003d5000030025007241640482684501400e600360200f070b401c90303ca00103408441000b41d9002c5069201c0c1804000e400701005403600c000220748924410420080c00e6034458081c00242d907020550161104c4000c2c5c0c2038043d441d040c3d202400054408070002031440941d4000000c900c0c4900b4100c00c2082c0d40764000d40d124401800303200600c0c4031050014150b0120304c40d0107841d01c1d0191600780e810000440c544083c1000907522404050f040b405c28404011088801780140c1c0c40070b40e848000503603001c20082086c04180a003072424405c010104a040e6030400c0581c010308010310654607a0304003840c012041413210b10071000401c00000300014001d01a100fa0302c441d05580c0c0300c40f0f0500d141124101c07408004482c2c1300c220481d14540c04505c8008501c42c08000e000c0038042c0801813491081014944182640600d0402c280c440420803031a81c401d11245e0520501a4050307100d440764000100d40303085940600d41c100e80640c0c0d10148075403514450450302003204032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 646812589 1250 646811339 646811353
    0x603100603110f0d0203030307031104150e03010e03040506090918032a0105060a0e1f06030b031b030705120f0316060c0906050f070303021209030712080709180209030105090609 78
    0x5120f5803400131100a9455081031000800c058000d400c080e844545003c41c46107400e49070210010205110848e07100010b41c45c040b2100305003424865031001d04640e100079800e0914060000d0030314462412250b01030b5100402240200c008420903003c0c1e24441d2003560707140c0c141740c2452922015884001070040084200305c0403000780601c9081d01079a00944420f07503950602d40350100c44403010740070080d02405107080040201c0c0c60400b400184c9400c0d5004070300201010308052a00c041c010b44100032039000022418659800070714407044580a94003e00556081f0329914141a007141e290b0500e804002103004115401d0403c41c0d002d14030900040014510a20080328206a10301421001c11010880241503c0740800540340b0343d80309103405071a01c20b540c3c02d0101c203900d0070740c2c3d41d0100e0f900120b9020100b2503c0407003a060000c00d450f00c0031042c60103010080055103188140d40140e2082242c4480351a6590101da00810f0090024420b41c10001e15543d5240c004580c0400c3c6401543d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 646813839 1250 646812589 646812619
    0x3010609020307140c0604110303070b0f19020f030a0c110d2a030903031404030c0e01260a0f17120105150a020c0603100e07020a0c060f17060310060311 67
    0x42a5005c40c03040700010700c01651103507510408440e100000a070f041c4000d0005c10f00144202800d42e1090441035003960180c180405098251290000c82480450040c00030043e02e0f484a8180c0c1e9000800d1400425840e5600000b5034000300c88010040712030103001800c0207550380001401c2440585401d84a01810303550402d144c81d82d0900c1c1004001400400e820008a44540107043d1071024401c851450302c0c0c0d480e698400300d0f000c194044403461030703d1001002402c009400760000340d400c0d082c1c000e440e4540e2241e42d0b070326885000c1008103100042014134090051443c1c8081248039130a6070700b43c1c1c4000f418020001000c0034400e0310300c5080b02d01408495148240f0a50b04c080246800400c420340c1030204200301074100400031040f1891034400000c0d0b0400c0c02c00198042d200d190082c0000040d2402c0103849615290005014000018000c0d450a984154409241a0340c0c24114202c0d455006c000783c20802e180c111400c005043c10008014042000314400c000881240c079449008504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 646815089 1250 646813839 646813877
    0x501060e10050105090d03050417070e070c030c0326070e040f1e021c1b0207050108010b0a0f1e02150915010506030c0702030a140c1207170c03010609020307 69
    0x20b4010b00e80019014001400141048118924400d1007410b00c1400d2035207460f8501034240d400040120240c6c4004410099400070408081c0c00510302c0c907003219500b260741c074081d0244000356030080400501820600303030400d04020b0164a141041c441d4512420100d0000b01040b0301d01007640d104626060441e00907450902c5131240d036003012070a400c4d4203040d81444000a40050364903403a80c140040450604100e544640b9104803000c1800d90300c0b035169020024506850b41c1c100724184590b1031300510041d10828180d584400e03061601510054000c05c040b616000010b0b031584040e0301998024440607008240041c0c0325003200c01004e0180c3d41d0b00c10041d0f444207100b02d80c52590a40100510150420390000e5510020805006180040c10b0b80843c2ca8880c1c49801520450038104551040c1d00041c800314801c9402103810401203003046502d01e0726903005109910402c000284024400c0b0400d10001e000098006e008000890362041420040e42c011550600000c400d411030546114807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 646816339 1250 646815089 646815121
    0xc081006060e010e0f0303030406090b011e0302130b1008090d03050f060d020102070e010905180d0210050a0b060705030403031404081504080d02270d050a110109050303070501060e 79
    0x3a03640d400b4181801000566550700c8580806800c132417035007900c040b186c400b0401140181d20400f00010703800800e081c185100c01c010f81050050285900f2034401d02201041074200fa01c1d01200c6040a01d40b00c22400340003000c42c640740380d400c0821030203504000c41c0c01c1441c0342c1c49012290203444440821130320840485004988032a8030310203540101d0784505110105444040c818012250590340398011404000400d1340940701c99a2102e04000c0c8020350350f10b503118200303900b0000301038076404001e000e516100c4804407655840e550320002505c100168000481c6500c0c081c0056607038894500701241c0721380c40742c0030640200742070309911050205a481102c1c2200c8003000501291440a42e41c20004c4401400031b60305a00306118030388660005100405c8104018010346910030b00e42e0000401034444441851721640d405255803001ca80040350600010380d000049446011045c401178900d031129412094041c0310110b14a010480154409c1c0c060b0341d50940154030f641e440e03040c1d80742044a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 646817589 1250 646816339 646816349
    0x60e04020705071205120c0a0314190305150604061115040807141006080d030c020106061202131502030307080c0a200c1314100e0408030c07050304030c081006 70
    0x1c0220300403c140c50313120b01090b5800c0c0c0b0910a490811001e006c01c0710454020b41c1900440340c011403007120805401c0440a0084034020650138100419011705e45038512001b100c107000c1c19101c80000c0d4400c810850040070103c5c00400742a240e684800d0010056081501150020f02c80c0301c11035103040034250700551203a0390111001e49131101e0386d030b07a855030051200c0000540e4841c1c040e0060810000b40903000140440340000c011500741c4080040503140030f4030311141564502001480410303803114811810860806000d44d88503d11201c0f400c0e2100b0395031059201e142000c20000e40726901000a50007480310f66200b55240e103500780d031900b1300e20510100501280000a92119405080b11a0820241c2a01c299450a254a4041030040c0500020317601d489980e4016040e5840700001c180f5009004428401c4000d41441408071403550302070300c05007082c04048000307840302550401b12101c0e0b55108066a40b80c56480c940070304025010700542c0c855014420b503e290741c0c095072182c101154 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 646818839 1250 646817589 646817593
    0x1a1c140a0f1502040f030b0402010f0306060203030105041d030d02190302030f0a0504050a0b090706120b0303040306180c240f090608060a050d11090916140105070209040c060e04020705 81
    0x19401c1d0740ca550340d900c801c0b609401e84079028000000c903c0740d10b04411000314000c010311116403030640700061100c440c00c2031342814180ba12405002141e4004240c2e4191002903800194540e01b00c0003128a0100901c0d110070244000116850200030b10b40141c0418041206091096000684142e040e800201e40c1100203d00b04000103942c8944c43d080241c100d03000300e059519421080e1540316015504039803407081c2e580702000400480344d1000016601c41c10b816000c210407041100000e48038802d61001030810b41d1105090b030142000000985121580400d59881103070381c17070307189003090405100131030310710454141d242420500940000d0004066035980c103a5a508010007681c0c800c10140c030280c1c004810240c042140e880e54240051441c0c0248989240717010000100410160300030040d4116401403030310514222401150341054811106040c54034024500048a1a000e0444060340c840d03219400d0109004000c4600026559141c2d02c0892403441101032106921404600400d03603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 646820089 1250 646818839 646818863
    0x110408030706050c042606090c0f15190e0a0530121201050a08030f0403030e270402180613051e010806070f0801060e041a1c140a 57
    0xd0351a6210a9001c032007105624203003529881488101340710f00040e02c5141c61ba44503280d01c0108104071036940241640010059010000c0200300d060281500b0b0500410314150505e214010790819600c102224a0010460f6440d14400402d01c0c190380c1c00301ca00a050044001c02c50f0700300a0024034109400611803444800b40115880034401003040e520802c4c0920320344007041002c0c9a00401c505d8840c00520402541410300700b10350401c8542c001c0f41658000c0180303441001404080c2c0d000c0301e4150403c0e618101071340340031809802d200d40407102c0400c0144609203001c040070a50a00a03030094031541c600c0c1c5004003010003c44070945140b54030040c031140307850141c40240c00c0302c0c0c2e012115a251090680031001d8202d0610402c1c3c2290701907411400030401895445200b6038041125840c002c61075501d01400640602142c40d5846c0c0101d13101ca03440c1d03049242500d04001620f2024000d00c00c000c19a0310040c1500103400400c945c055460583c00000c1e0f240092144100c0740c00030562888 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 646821339 1250 646820089 646820093
    0x2120408090433120f0201050c0c0603040609060b242a0a020321190509031e190b01060309140f03040e09150417120108070302041104080307 62
    0x864008000059209849145544040c28070034182642d001c2c0050180742d20106103c541035a1412a8200c02c202c2c000304013403c008200b071103500d03054a40e020f080c240d030380f49001c403100e509106a500d1840c1d00310500205000c20060203602c04015540200d00c20040484100304001c080c0b807602c8019103003050200710b240711115080300107049004140300c0b0078068850750413201c0e110f01d450301d00e01245608a50b4a80003541400d004402c040840765003180e800740c60030040c000440c01101447c1c20024404087c024030140680101d65030464000c04031790340c45560381030301c11a185240740c01303200c180a4210354011100011458500081e07111905200c1d5a00b003076000c800510000d4400e5455480c40013400304c12900c280804844610300724007840d5680c2c10075041909104006d0241031f110b0344003030a09010318079000c41c07154016500182d0082d165485c5030181189000d10400326030b10400041c00040c85c4540041d404d41200e100303580030f0007400c00200e2108481d0003240b0172002d8941042143c000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 646822589 1250 646821339 646821353
    0x1205090c1e09040521070b0a050709030602190e0f06031501020106051027050915042306031009150e1002040923010503030a050f09030d08041401021204 67
    0x889102805401410307000d0040000d600e103001601d094506811003220b6003070304002c448507000044041e20406107440c0d080d544004054030001c03d110a125070740c2c40840d221030302c03480103e4011130308540c0640d242c2020041880c4168810038002e0085601c0d07a00503411410808c04c2d40880c1c08000305442d04650780c0d2140c01c03403a0403440700c1050440d5658500406e02d0381e5103060122001c282c0c2d5444e580464448030904201040c400c2017000c4007048040c0c10816a45c800c480690301680450107040c1e95a408404140604510506140c4c204d20b081d6440826010061031548140400c400702e4001c2d000300c00482c0c0880c0c04080001c0e040908820011142c840035410500390300009104954010541d40c1b80179040b070304590013005a00780c8075180441050000091108503e002c604600c686501d45400699a071051208020900801054071402800d4440545007103110250a89030000c2811400402050007150100d80c3c2001031060200d000078140b0075501203600cad1102e1654144c5480e11031070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 646823839 1250 646822589 646822609
    0x30f090f03090424060c111c02040209042007030806100203031b07050d080f180d0e0105090415050915010206070e0d050708030a020706170408030408040306050c07031205090c 77
    0x2c9101c01c820004101c130221a8182400140041e5840c12034001031481d0120503491054001440703407011a176030703054001c801c100e6100320650403a40182e4a0b1072000229014210210502180c180c1140c10038580b4115840108400d41c400c0d03680c003205542e200700f0414480b04d95811b1000680c02400000c42d21040c452100210005040d031140c189146a61024a040e1034001040000f805c00400c0c402c0d040040c1c007656030021510069100e42d041901c0c0281e9540203030503e5902001003200450f80ca0b0f0340100100c5010b0701010f48203100318a03603c085808442294401c240c0100030110000780000340008104500d070790140c0c040c100e030b511680001c640c680c0746441c807560b00c2046044401c0c0002c40070003150307008142c194059a15044c01040180c03d048480d4000380501a0301038055170a000030380700c02c80c4d201e0350201c00d8940300e40700e5040c2004180150780004106a03d850103011001d0aa58003a0000358402d540d0120035284000c4084150790090b181d0710516404a012402c15282a100784 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 646825089 1250 646823839 646823861
    0x1701050f0f13050303160306080309014103070206010e10060e0f06030f010321201f020403020406230d080c070b0403020415060917150408030f090f030904 68
    0x50300c2540b03a0348600c4d0441c0d0085d2000c0600c1006070304200b007566050b015080060544002442c01c203060040080d045c0c8810740d51a0b10b085503480f19030800e119413015400d451800c5a5206a1117420303200c0b64409961041d9180c50252103460000103510b560760b0240e920030450f0240341c0c1191403030100d0030355202803041c1503540c4c08000c04003041c1c4143ca0300d00186108102c0801040706c2c2c0e500d581810984800b08081088100b8080400a030b03205400010074a000c002025114001d441c181c841c60f410102070110b14802c403180039114840b98001c5402500540b402140c0400c0039a48d1180f01011030160345000190303500720118869611318040c00e140b0744150050014501e0702d20b420400c0c0b401c114058101c0b5003210030210b0300b0302c1981000d110b03401851036a1079805088034203105000d480b81e0340d10700c42c0040e5403850403102074400100f0b0096081c0508050a803040c0ca0400f80b071b00c203e441c1c00c11500d6000e10b01a0300d001911a40b000241503100840c50320145150200074020300001d80411440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 646826339 1250 646825089 646825111
    0x30103020a14150f0304020f0423041e05031201080c0f090a06090f020a030e01050702071e150c03030e06040b070c11180601021902061621091701050f0f 67
    0x72052480c0144010a80113401c0100c140e130340d24052041200b0500c400300c3c4d040c003491a00f6840201c100210822035507400300400141529565403505441a022021441000d22280700c010410000300001804940e154240401541c0c1e03215400c0903503840510040c1d0b075216140107918580c80c2410550075070040385049011964035229000700b01500d204260140e04031743e0000d0a00c0c0220350500c80c14408500c40e00081c0306d40e04000100075542d5845008d9142c00a00c684850715800c48030402e801c00601c84210b003028021011200946888480300098010034100340c03240521540101d803042c030a592080c0104120381700c1210031100900e6800c000c9902c1d54482c91500c1e519a074081c10411103201d1014084564a0030030300090a180035902d541040c010072654910050ba620010703128201c4000c0d001c41c4012920303041c8801c42c404020b080041c503441048850294651000e03030001520101459015041d0044211038220b031422241c130148880d604002c070300f15429200e0031580012207042 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 646827589 1250 646826339 646826359
    0x611070c0f15053f01080a1e030f2001050a1a100c0605040201120e100614090a020f070507060e130c0206040b0403030e0f0303090111030103020a14 65
    0x15512219004036041600c80702800c0c0c80c00c0002202001e5100d10034006494810304003408011607510b40e42c420007003059284c00c0a45640c014428003140340810b200342030605500e55070340e10b040340d40318050031000740d403d0b103180400015100c0141c0d5002c0c50150b41550b4442c2c1c07200094008941c00388070141c0d003900e0300108000e1503a40020900941d4058580c40d04002002001c01e1402c4030b003803c010742004e0103051307a4124204070a801140c1c074030209412090125250382c5034801204c03111855180051140d20b440c400241900c0d000400c85800d400c080000c001240d1035640740c8824004000c00c1550010003080014811031054011f03210f28890007004c00c1c10110313140d0741c2d6070130281c82d81c11a00002d001e00e0b00f526003d10b003130300c05400301c20054142000304200c20b0000a4952070b0060014006114020204d0304040c4a540f100707440356644000e80b1607010f0003c80e4a80c4a61050759424565820302d21101d858036034680441c0e04881e801400c0282e086e140806204034122410081a40070780c0c101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 646828839 1250 646827589 646827593
    0x506030309280503071203080c0f04090b0f040e1e0102070c06111501030c030b190c1d090f0610030e030f21040803130203100f02091c0b04061107 64
    0x4000c0310114403102c4441d20740e402518012401151055028034425401010100030441d03e89498540c02130b010b140c040f403107a480b004250300d2803141c03030400050f80f103000800040c101555401030484040071154980e91070072850406c4241d030041c00411007145c016081c0b050504900e100c058104400403800907003060120b895050000c64141c1c4180c0200c0c01d070407407100c101c181c10700c001e6024002068a1200320750660f103a011800700540001400302d042d48000c00c8035140d540054560724040d44030148030405090340010102d00404406028442c20307084902c44d145400c44a0702e04c90608c0c51002030341c7e03986000400160a0b204036542040c541d070f0310381c0f450100c0018030040084410b00e80380700781d50b0902e107110010030f1070035540904514070030b4405010024029008407900418640e81c050070480640c00000d00744901c1d401c2c14036025103469030011040c0c5594001e40703a2513004031021190402c4041c03070440c0307a07481c1c640b00401c071242000011340090816800551944d64038410f444c01d0003496 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 646830089 1250 646828839 646828849
    0x2011415120a050109060519050106140a0c0b07050d110415082d06011103030610030e010212010e0412050708031f05060a0825021b032e0c030902060d0506030309 71
    0x14185c1a07407a191200100310020384542c02c0665440c1304010304102a6141420007440b2600c21541040c400307200082400041d8802c40015050540181e400501414170750790152540e0f1043c40d414040350308061050360030191000598080300c1a01240343c140600740401142d200400030040e02905801c411202031080b5082d14dc0103c50202065180c803d0070150005000c0d20b141250b061002d52041007000010f031210072701401210410704000c6404444401110f0290090314180040440040300004040520401c01400745001e074070101d40c01400440c0031984da2190f210090084801000402c070640354506543c0104103070b01600362442c03600c1c5c40018080390301601c1800002103001e8140035030551a042d540c0c030495036803500d94502400540c0c0280d141d00d00103c070583c08245c4007000320382030340302030000b4001d038000d10004060015124846ca10500e107507540c0074042c2803401c0b24090215010b0311429040300d030010980d6040441040104c0040c00c00201040e400d40420b0040c00303929261 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 646831339 1250 646830089 646830101
    0xe03070317070c0810051906260f0d02060402040e030c0a0b06030c060a0c210e04110d051003050c0108060a0e100306020d02120606090a031209031b0602011415120a0501 74
    0x2c2105c04074913410b050301703200c0e01c00c842d0740c00c081d075614a007000821040c84040052014003065100001010382c142d1130243c100406001a01c80d02c0c01a40294004158045281c0c0d2181c0e10071102045110140703050250380f4042c0b00041c044075841501d00d440496180303807100750f1040c40101150340c0c44004901042c1c854014072059404070f2050903040c1e00f00100150750941e80d14002c100da0b03400313140f0301c0402844800c100c440c42e4040d90b9221605480388820104031904200c003e81d0071b110340d04201c80041100c0042d40300503151f034011004580707030962051081c0c500445c40204901002400c101540782003103006000c4091035082000c0020020303c440c005809010951400141c0354502074103070711483c0c08010702c07092040d50204030040b9940c2e05c038811001542c0d0032214150424000003001e851800f40c94101408100340c1e00045945022148a450240d40241d4000c0c4a00b2104601f540318080003a14910440c102c003d402150600b00204a062200142c0c0e04962116a45403106400c41712 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 646832589 1250 646831339 646831363
    0x140615090c0c0a06051e0405061b0408060907060207090c021c020a0f030905040f09080a080403091d15040207020d082a0c090f04030e10050904020a0f0e03070317070c08 74
    0x9215410891401b500c1c04500d004140840c10881161034681d803680e80f110030040102c9028041c030a640b56120301480c040e100508040c5c802c4980c41e00b481c1a20ba981c071411842600010700c1460000308504481c1c0c01442c11703804850b0004c00510001c242d510100300f041080c4201188245a100000300340d41d02495142d5501035121110306a0620082c801610240724440b9004c0e802c0039403050008003500101d40c5032106900d09412191140d260850300035400741d101012146010030829224011003000901030318032584003040d1902c1240900c010790080500107076120300d0300389501c404282c80e480100000300301d010400c954448081030700c2d0f02052045540c00c4a582c0b02d00d10428560402c6d5241a80000d411855410145070680d4018410b9150300b14040c059208007030480c0850b030040b8141d0b120300d44024030964994041c1207000341008920502600052100398200f515400c0219a080541e60000398810381c6140d401c41c0b041c001d5021540442d4245000c10002560640c2030082102c00d00f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 646833839 1250 646832589 646832591
    0x30b2d010501020d0c02060412021903060c02061503100f18030509030f0c060d090f0f0308060907050f2d131802090a05010c110301060909140615090c0c0a06 69
    0x150400000a2405141c1c600040070300061707619400c0941d0f505c0003520200c1e0002d4106a0b0106c60f24800700b00e80140c40031803440c21901030b0001208110a0340c200c1030192500c3d07400c44400d40e40c0c8035000fa05003082550855090340090201105801d50f903040000c4c0d40014490100300340001407000d5514642c00340044e0b00085010031030006038502800301c2411440d031500100681c518610001d1070611422030720001d0300396181000410010a40c0c0c04c000c0880e0414040d40c2c48004505004c0c0402c0d0003261072911500000b400181d201d17004030251249603807081d84440c20a10100701242c2c1503495a10410300e0007da401ca10303002c00544034028030f000744514002c034810600c0d01304252441ca107664811001e0318010b1004620545a07414070104540c02460310035020000c40c246030f0626045000b2094165083c0314000c9450031791380c0c0200152600c1198042402a802401c40340c1707400040d40c144900540812400d40c441c50500c0c0c0d01908201d0402c1403a203006140b5201074680145600201c03459 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 646835089 1250 646833839 646833841
    0x5070f0513060b0a0f02011113031109010b03070f090f062606010f21050408090a0605090303092e020d0f0f0e04110702040f0605030105100f030b2d 65
    0x1800d21401c2512803910044060041c142000d256000902851031400100b00c92019031100c45c51003500a8071005120720011561025036424001d40c211190106444030f00110900c07034142d05140c48142d040358445040305055858800045410382c52401c022810410710810100b0f5402042c0000c000504241d120700c8095100131a0403242c06030044800e8840498403001c10806907044441c84110070418548030f40e5070038a1a44060120102050301c240240c5010108002c02c14904020040064111003c0e0149a03650000b00d801e8818143d041d6096041400341001e41d00f0007100200c086a40780d801351038000399550069148003a041405401a0700c5424440801c90b0440395141841c0c03e40d152441101c510b81c04094151718804141c01e0045584908541c050f810f01d009441c00c140c6c1c000d03c00c0c0175004d032440c03d8074081c1c03200c4d00036a4440e51030130001c02c40c881440801d060440328980c414041d4145113440b102400c1c0c02c020304118141503039280060391042c0341c1c4188815034103207840425007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 646836339 1250 646835089 646835099
    0x90603090a050c0307142202221e0e0c07080c0102090103050f01053d02010501030b0a0921020328020f1b0f040b100504030b0603060613051305070f 65
    0x1a066010714824005d4000820030706c061044003161020b003100035030300c00c118103a10314040300c03031620841202540c07644089442e50304802c5608801c00b6980d45c4a850000702920703001ea481018514804403540341c20612003c0000c00c0c903c0c50a103a02c00c0b131540d800d904100064464503803c0d484441c66500c96503000580d031100d0341e014800e151308101d003100300100d07541c1404003107068900885c011200030841c030080b1008050032500f1300290303003c0440441a40110b9118040e010380000c1c00304a940c82008070015101807400c1c49911180b40d0080c06072000c030408c15600c111521850f40314981140020054000048030410304403c01e00640300034054400000c04000b4101400901d4503a50340e00174001b41c41c242d8054218040d44184101d81a599010880001500408417801c41c5c0b81c101c1c14001400402c00d4004000c2c1c0101c4e80201e411a0f00c2da940c45041644400e0121411584420130352840100c10b0010381c806684100441d0031007920713002940b00c40e80350024a90110300364020098040c85 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 646837589 1250 646836339 646836343
    0xb04061215120303021e0406030606090b090102070302060a030902041a030d02010e0601150c1b060f030605060307030203130203011a03010e07030f0807081c0507110c150d02090603090a05 82
    0x1164803051841007004030309000803282d92441e1000050100f5070042107203c0039904108101c10310017280b4071201c1c1c1c1c6941e80c1602a01400141c401c0c034011592024001807004120070440d1b051800580c0941800c034119400c001c195005145548105130b40d4401181c0180c40c2c0c0e01c140020715881c15050320286080000309072806805056040459040200020f5009400030b403041c195240d100c0c02c20310740b03102c4110032181c0900480c0c001d0a035402c07072229480ca55840d0200a000e0720a03e9948804002d84403805800b91a0940f182d90781228041000803509442540a15001020210295038080d41500080e00303440c403207002c401c3d0071803215002226038075091188401142d4000c01902190f45140c4840c01c104090030406000c2500001d204010007801388101d5965406c20450840c49008800d0074030000c0c041101c0c481d0200d4070b2000082e40c800c40009400d80303c010000c12000c2500811803614405821044091540c517409214014507580c40c01e01444c45908a140280200101c1d820694 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 646838839 1250 646837589 646837601
    0x3230709021b15060906030c03061003030e030303010609060509011202130f09060f030816231002121305121c06090b0102061612051302010917030403031103040b040612 74
    0x101c07550f000e0310714a11020a00307081c2c5a0302602c100e030041000c1d51540003190030042d0220481f0380c1400703110100030704107104402c3d20003a00e0283e62980c82408800e4103055076031000303018000200d4881d04080200340d02c070341d008144d00d94040c90082c881204045444042c0e03040320915848aa55588041c00b042c100641c100d030080c905a4001c3c48041e243c40241c0200e0350f55400007030140c0c24009411841d07000346da0b1660340c90603030209420301c03000b04180300d01c40518610071042c0c8143c000d26481c22900c0d2250300a58000e00003206d405441b68981d01900c40c12646080e000700d505000b00d1707001c00c10102c0c003040038211504800f9814000440702c0308845e000c86089401c280129840c1c000b00e1003050764002450341d407007038144202210b42d004202094441c004c2582c00465003c0c2070030208a100e10f07d4400c0811218400c0c0c8070b40ca0707481c2e06c440041c0c4590481c612811040d43c403d06c0200082480f403626001074201c0902900c2c50300361034100c441e03102c0d03210750415000706140c0d03030040540800c0f030321841c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 646840089 1250 646838839 646838887
    0x1090b090d122d0209090c0403030e0904021807020a060c02250e060d0c050904030905090601110d0c031e0206190509120c010b0a060305060f040501030c0323070902 72
    0xc200f002400b0800c1500d60000c00024203a02000040006a41400784c4c12942d20810041041c02d440c0340042036001c295205000840006009030b45903030180c14110403d03030041d58020640080c2040c00d40d41a030307521f00c0040c981400c5125180560004c510280716620110300c2c91ba000c1c1ca28070a00401e4801c1101001000394a1517506050410600000340b458a810840855048a0052407400c0501e6400c2c910741016610010782d00038002059000310800c400ca80094401000030790b1860015940c0c0d5900b1025100250070000741b06c40c0b01031045a498040d03510a0030403c03540728a540030000950b01814400c409a405807051017520746140c203060708011281c00003030000340341507002c258440080340c0b8001d0180c1e2010a8100701c644c42074001020320078020b42607410440c1d44000080c040c2c4030a80d607a070301407022420a074a4500f0240205816642c01c4232028020600d50741d50602010717583d904010f101c2901c4005190325402c207000b80030060206030005038031a4803c00304a20a411340c1040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 646841339 1250 646840089 646840091
    0x2114150718291e0f03040204270204020901050f1b07172e0f0b0a050a0b1204080403020d2402030601021915090c030b010b04060813030201090b090d12 66
    0x1500c40b106802916031484034001039843e40714640d441c0c142607032101001c4281280007020441c2d54280070071102842c0308600841e8148466001c84080101100131001c000000800d14a00d22015090580040c45c0319201858401d2801d079141c81400042d4000d8511203140419000c412100700342c0810164014258030421400c13070303041d001d407041d40e160745140415150f84200342d084c001c070382c0303003403224480c0000f06d00000c0c01040000b2041030010500314001c03a1240b8449100825242030644094007610809504c081c0340001c112040103002000420445050340c00300700110041e15403003c00d01985108003000c0800c100355074012040781d02c3d52890241c600e8410f000304409a83e0000d03100341100d03404144030041d681c0e241815400e030400181e2001c8070a0600070b880f000c00508032421401c40c1d0061002556598035440d407084144964450000001c4030038001c25410f005903500c0c088a5880f074000010742c1c540c90b0b59806c0c90700710101c0d000170807034208007070000100350407480d801440b46070000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 646842589 1250 646841339 646841369
    0x1080c060a090e28020a03240b0f07120206010923061011030a0f030b0405040b0c03090c0306040305030f0a0501050a0911040e04080a092114150718 65
    0x14040d0b00d0034070540407a0700b0f06001140301c00d90f0300c0c00d600b0565075414a0002c40444000340c0c08001c2d50001e00c5c01000280351488a80c10340883c0300c8181e070052590701020034190f24081300c0542c25007120000c400b202c1c2c02040f0007000510f11011a8291301d6494001c0c101c00d6241480c1f40301215081281c0da4420b0020011040c003108401c0c40480e07201c3d1007210a2420790340035140c00c85049c01c01d8202261644400240003600c190031041c08106a001640d080c889400c0307940c14041925001c0d5001890030440e030021507000c401d040003540d4012170a4044070503400801c40024600003080c1d81c1500803600000600260b43c002c1c9229503405145107205206070751512000c10903070700c42c0d4400da9041c0780c0d50381403140406850700c080714003c10160082808905260402d2041035020060403408102c01800000e40304002c01c480b00c83c2000c202c040c2c005001c02a8a8114400d0001c0c8031441d034a0160329000c0c1502800a01985d000c0c5100350349012000f031030a120f110300c195140d08011a8014a10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 646843839 1250 646842589 646842607
    0x20c1905060909131b140d05060703020a050d0c0c0308060613061b020d231f0209060702130e0618030d09020a0302030a0615050d1e03140d020301080c06 67
    0x44100c6181c01c405076030600c01e69036509135005503d031011500030960740403401c00d003002500101c000c905903619146425076400764041001001d1004450050864110500089844e40640d003d061508041c0c1000c41c035050412a400080f5668076145501003101c60102d0802e160340078402d2544100240e0711245800410461480d000f501c42c41494200a8001c2800c0e030800280b96806200540c00303440c13017040c0045443e0981c1c03421891400c40c1c101c00404500c0320204100021112003c039030022500004095241e4880b01039440b00d6009a0004401c00c0080f0050b143c6880703801081160010000d24201d5200d206401d00300050600b00c8003040b202e16a010f904400b10440e618401d6411000604c40000e101160f10720340f01b40c0c401b0b9411300940720848140600780d040b2040d0781030600b0084643d9511103040103c200d1100f20081c060b5039030030601c03540c0102012001d8401502038280038803110311000f10748a03668442c0c4011302202d500800100812076007040f484407107001c21121103040c11040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 646845089 1250 646843839 646843849
    0x9100513270b0a1d0304080a02102604021f02060402100504060512041401062c0c0a051e0f1210120f0311060408040303180f2d06020c1905 61
    0x30f0204902c3c0faa6a20b40340088018480300064140e4141d03003a0380d15103584600301034448201c8071040c3c2c0941d6419000a5541e44140000c09141b407250542d00c407100f010403a02c00203100c0040040341c011822a0300360400107010281c3e03c0c0c0300323002c0340d008190500e801d2040c0440c0f4a180c06019040c0681804244485500b041c16614003210510780c0800580d40d9050400c0c0d0446100e502d410a0352130901d010541414400405d2489828145240110414404c3c00d2010303000484550f9010030b01800441c0c1c4892107640100740450300c030380226026000303195454815a101000c483e04e10f50002134241a500d1071309221325444806055800701d2140340440c03071902d510b00c04000410680d00030014608040c000c100030420301c101601200d17400d144c00c0c42c00c0344041e03200e408298003045a07047e18140180c0340310758001c140c940d581d81c0750aa59140056111150380640c200040189102c1400d900500c07000007000d00400903503000b84000c0c0103031014881050014151010b60b148200e400344480d4840c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 646846339 1250 646845089 646845091
    0x12041a0a270c14060d02070b060a080604020609091f0b030a0c0e090115021204030605060a1514090d02130c0e030601060221090d0b04060c1d09100513270b 68
    0x100fa002c0d20382d0010140d0002c1c0161040c5520140602c0c0301248101c02c5c00002000c25101c0d0340b05840c82c240054860055554030181100c000b507014004100240750341c200500583e802522400c140c0102c401c030011014030318500c0c0d030050700392581c0200402c0700c607602a00501d00b8001e00b03070518500d5407803044082100300e5014060344c101060040b84045955100700100d40051503d0099940c503030742c691078000d014110a9441b01d20a511541010450030312500000c20602e00c5a06c4006028200032800c0704240c100c50b508942c4440790b0341e042009230b151280003600034141440d000854030500c0e040a4507034800e1031401c9010b43c3c07003500140540d6400145445038134201010040d10b030407420b00e00c5011442a5901542c02c44505146541003040411510340914801d80040c8016140b02100319051142180e409548040501c0c04030240d0416212041d0444900f150203810151280003048a614100b0001440345d540e4040062046403440140c045400b4080e40702181c00d0071586900a0901c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 646847589 1250 646846339 646846349
    0x1090501023c010203090c103908120108010f14040201080408130b070605010911070303020d0617100f0b0d0b0a111b06090604080304080325020d0207090b030312041a0a270c 76
    0x11240c0c001000408209e00c0c40300b682d5102641c1503803030240d00d1003410029820300c038041c00340d070900d82d04510922460144041c1710450340002d038603035580c0781c0044444010152050b541807100704918980e40b181d40705010058482d940c52641c1e95141e52410310304480d4140d000d020102d01d40701b114200c003081d590840e2031243d014540940c0b1000b5004c00d0b1f000400d801d03440f0014006111034014141074010451420011905078104181640045240152110b501841d035020b0038100042000582d41d0041c41c0d00184441e03c00640460b01885000550788418012904007e09281740646c1490030401194070a4000d0040c1100b420642d842c00c02e5404003420040001e84080300240940010601400003451450000744441075005006500c890205400000501507a800450b200b041801025003901d0080d0041d850304080c001400844d0b04040c200301c070004181c4109035a16130b010001c1901070740c11110000350a04503210002e808007100210390203100d0751808000c0108260032091411a1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 646848839 1250 646847589 646847657
    0x109090327051215010e0703051b09060d020c0115031b05060906070f0506010303050c250302011115100905090a0506180c0d080901090501023c010203090c10 69
    0x500c03000e01c41410b004401341c94100c1110241d00028a4a46211985008980a031401c1000b83c803100c4105036090340c4504404450101041401020b0800b0002803d210040000050070710650408040c01d4414079190b0001454000380c003030007030100309201c43c580c0005680b0b00d0b03407207075143c2800f0440703d000f402462031240101003201d1040c024401443c0104640c04015500d00e90303120b240141841d007252040c0440c0f84a19202114410382c03030701103540030b803914640070b0303003003501c0c0d54011912440e0300c81e0307403034054018a20212621601d03108160300424144611082d040c1c02c18012004845000341030400d241e20201182d80810000b04d002c40e0001040d45006140300703070340c0c92440d00c2c0107100c0300e2013038100c0741900051050000040250101c1b103426039400c58403d580700f00485e96403589281a04550400c004858000003580303650560504503c43e145c0c461403030340030708103003243c00c00c4409001c15086100c020045160660803106014014100001c55040e4180278a80001c010054a00c81c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 646850089 1250 646848839 646848859
    0x70f0501211505030307030f0210090c05190b0706020d0506091e090325170301030b010605090102240f0a1e050c1b1501060521100302030105010909032705 68
    0x342c62022000780644000f6040b65595107103483c0040900b0806501b99005016044090049a903039005060b115074204494030f10050500003007040c4055280c1302c0711002a40d00c2d000266560800340030300301c0346000e81c40060302c400c001d40900040e00d0001f005180700d0700b501410070a46607622181c2c01002c2903041c10031070042d901c00f00c9162031441103145401c001591121100d50134015076180c440c20512031504901c00040c0c00400c0b8403980000c0c000117208410180c018480f89124401508c0812014411140400315005514100804c0640141380340b040e45c0c130030441e102172084c21007a0445441641048040c1c00c2600c0403490440c103a901424968076040860b10a4039240181c840b030800c1d0080c0501d5141c21183c0d071580d00d04604c2c00070f050400c101e03000019402e01900945a0403c01c030421560744494015242540440040c1502800c07101c10f200840076071001d01c40c0c18082c044500c40041d240d80d481c00c0c050640c100c01037031584501e1000241c544113200c0c0d10588021150300381ea806842d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 646851339 1250 646850089 646850111
    0x50709051b1308030f0c0c0301020403170309120301230907050a0507080715020a08010b030403020c0f0118091d03040f061817011407030213260f070f050121 69
    0x7405160b114103018400442c2203501d61040c40d00031b20340151240101c40520382440c0515090740030f5488040d199035000704211181e900b00b00d0086600c510b980d002d60b8440d0300000b5010209400a8020803240c3d2860404801c00908031120b40c0c01c20a800c442c2c110030b52400dc24014100e201c0d8030300e840704000300400d01038208110803040d5072203a0750240c0540c2d000180e0207444002034000107410f00c005001e040000403141c00c0e640c102c03805542c055001c2d05404a04a00f03103d41796560290316410004140c080846c1032001c145048094000410b0204049280c61202184404117081d40411504108000c00212250407500e1045070b0160030000030910900c01c1003140800158000b010300d0005800411b04103030103504c0074102c000d2000a840791034075040001c4040340541406000d10700c040c501d003444004480c01c1801c40040b0404000c0c0c03c000d503180001820105011070b403c9155100c4002803200740f080c4003400d0302900f001e103005c0f0603003c4040044034500e41c0f96004140303416618008801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 646852589 1250 646851339 646851367
    0x311040504051303080c0412061a1306060f0207050102071502011805060f070c12032a0c150905030d0f060504020301080c2b02060904090b01080604050709051b 70
    0x8010040104208014a00b5245004400d540420200c0c0082c82030740005102c001904281e4054812034603440d641200d25588400042201510101002186007900c0c00342e40c0d10090032107402000108003141c0c42e0314041d009840c0c02031030029401550802c51003441240d0340080c0910449200401181a1480c1d058042c0e0040c962604850b4428030780000900912000003996802803000032038842680c0c7d00c0020407550080b0b003550003804501c002c07408003a000d200c0d410040c1c15051140c28100c0d10800702c03e90324901e03078140d5402e1004c510100104000e100caa0400221000050042408074150a6a41c2501c03840360717039080c0d046140c4c1c56032702c00c91084e815441a03010f090041d02c11941e80d40c54080c00713661101e02d9000548288600030000818010882ca1841040300b540940180e030085942084000d80141c60780b2074000703a84182c0c90001c9a03001040c18000c0c15980041e1140d030401d410303d64100300090300082d403654140750078403202100010b1000e14805503040840c0e124606000700300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 646853839 1250 646852589 646852597
    0x10507060b030304030c0f09020307120207051608070602010605040b01080103030c170f03010e060f2202120106090312050a09261e0708120a03051f08100c020109120311 74
    0x50b800d44000300d404802c2008802c0f40c4010740e10201c0008111075580c200400c01d901c022120140001c501058035920352005401800400e40702e8002d072030341c5000b503007515000200d4a034803000b01580041810000d064080c030944006d07040689050218803141d40021f480300344113100050800c00381c1c81c135010a001e0741c0c0342001c02400c8122506550b1f26442d0141d50410382080c000c06000c045d014002c2802460031072001d20b0442c030040d1201e01884d003041d19841080701c104200108860302000340000d5070082d291894003900403500d504002c6030640c01c11035102d072126040101401001c201c0c05e14400d4000102c0022a880801e000043e4150300d00320071400c40d0010800141c034451002c0e4244040500380c50300e018132022104940325155901c942c83e5803400940c3c004000c01c68200b08a01e400e40c40303904082d030300402d00703144042c1c03000070800134140d0200c182e0711040958101170440b070420300c00750040400e103400510090000050343d48480e001c40007980711039002d00d50345401403042c0042e004243c13 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 646855089 1250 646853839 646853861
    0x1709030a05030a031a122d0f01051b03090606060a12090b06030c1e04090f02090f010501090504090803061225090507050a050301090b0301390203090f01050706 70
    0x565102c6040c0704014015002011180203001050b804483d146d04002d01060710307501200e1300520007500200444501d19001d024102d07280d0300360f80c00780c51000e0b004104038081d4040003000001c5a192074103031650280c810001400c0c14010410074003560343c04c0000e6035a04030000700c4415a80d0000315030155100424580340e50115402c1c60314100a120b14032800c644244816003d5038000100310040001c948405c00521041011940c4460554145540410105445000c0070000c44883d0340001d411604116130107068000c801005020550744080e2034001040c058800f032002100b41ea5400b4024080240314a00668a101035000e141c58100328506e040040f00300b62002d5030144803120071941c281c0b40070b882c801905200204141a200e0800c560001203d9a1281c0c10f5901344140d0401820110096584c10340d29004030308c3ca103030406000e07100014118000c1d03030206089614045607035401c01450310b0540d041400000e219850340e038100742c1041403d00c1c10503554201450003800820b084100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 646856339 1250 646855089 646855093
    0x10052d040605041d07081c080c070506090d12020a0c0305070c03020a090b1e0a050105030c0f04090501031a1b090411161e0f0b090c0d0302070504181709030a05 70
    0x2032400340310381300c0302c80395240c2c0d040403d0351a056100d0b15150355681e40c030030b0350018111426000b901154030030192a50061054140186072503115204c03146001e42c2941e043d0915002034410311007844e044240e043d0007505400086d0705040d070400001e0281e080190010b010f000f000035000c0d01300002c0305908d9010716401800d1601c000c0d206d0703022000501014000c40e0049281a410b5101c0581c21a03904a00c0c1000420018220342003c0044a4981016000181d80074050008a00c0501090040c02c06400d22036000141585542030007a0031143c2200f4000011007080144003412480b1011350381019545820140d540c2200b402140007805c0381803821002840200d0200e070304c0e600340004603a00601880c0c80d80d4100e0132001020085000410004009490a01800300050210065250310140e48030513101c9600c0d1000200c0c0400d181700c00100c0040e001080248014542440385074400880d031021803002c1000c5640301c24414500c28800300d4002004a100d15242d9020407010340c0721a80201 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 646857589 1250 646856339 646856351
    0x7080a0b061912110c0309040914030301080c09060103050906010e2e0603140709030201080406020405032b020d120f02130603051509040b271510052d04060504 70
    0x200500c2204800c3c4050115800c242c040206007000c4010365290180c0d61001d1442c104403802044010001c16000315118a50b035400b1102500b070034006503000303241c800c0107030500c0b280c000300b0000c03440170007031105040c10324142c00c7c40011038002405c00d054030f03030b600742c000d0680d160b0b443c0b101c22070640e0041c26200c03141485210b440741c542040a600c100c60683d18240700d10b922210481c071041c802214150006109100100095841039140581142c0030340f2006103401e0300c8101080c107081c404d40510310092040030a502c0c2c49005412411003845044c4080c0520340340c0c020000f00003d03803909600125030340380c5581c2c4a904a0560443d81d00c422100c043c0054a50740b008084c0c054441220901404400480b00340801c3c10200c0700381d80b007940c0c09029403506a580c0200400c0640525103410410ba1a10186065101c4100500e4500103c8007000c6170080c90924188035424a143e004503024410807050b002c4062080030b014401048651601075008a504011030010700c9580c0c09143d000b400e0103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 646858839 1250 646857589 646857637
    0x409020d020c0d090b0a08041b060302094608010203090d1e140309280605010f450605100807120b0310020a052107080a0b06 55
    0x150082c15422403400580b02410700300e9100380c502c02c0d028410008110420405864a244070300020350f4001e1050003c1505020742004045c20401c80303801000202c0d17800900c24410b46000100c400e42600b201035029950310300c411660301512a0702c0660002c01c000300c414505403034402c0c11100e000d04100c0c0300031500ea251105105941d808220060070100755409541400d03000d0290080c0d01000f03da031108103d20b50003095083d096030000b481d601700360041c01180c00c55405100141107102441c00040c46580b0210304040c0f04076001a0312254030500c115070104020000c03d0003203600442c4a8030100c903809101003c42040c040b0703840b0042c207002c000060200006a255011106845041d035010810417420581540d003c0070984041d0003107000707500c1c5800000400c0d0012604850701806440c0b20004000c8120280e800040004010440114441e084238401c41c2c54280c46e0f03040341001140d5400d0824001d868860080d0803007104685454891070f983c0c46038000c83c0c0c4100d10302e140041c0448a06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 646860089 1250 646858839 646858841
    0x1050105090c03010e06060d022b06090e0a020f1315170c0112020f070c0e010801050714091933030c0e06130f0f03060f050702030306040507050409020d 67
    0x9004141c418000310000c2425071010605032070594011814400711a15420304101c401c4d080b213042003103d0b035002c1002c0d10000f00c81d082000b54440341070400c0d0a0103030703810640d00f09a85031500082e60103860250004407a940014180c0201d64059846000b5005d04801040c06014100003412006040002c0824294400940241101c03030b001c0403905400b03000c0b2a0640c94402e48081e8900242e071074550900004c20a40c0100041c4465042c00c5141c100d035680c5504400e910348e8421000b00c03c2d40784c01000603400038011140c0c000c1d49840e100441529110441b0b2240c0254642d043c02555900000100e960041c004240036098841c0c00c03504031103050b0013403c8140c101481e0141440429810410b80501030f004100112a10781c451000b0303070184d0414410581c025500700603403500700460010b01556841d0522020340080201c0b1442d481c20b50400f041540e030300d007040361001ca1504c0c0411511031790100c252034002008540108050301c950030119402c4c01180c100700815840040d60b000c1c0200c1c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 646861339 1250 646860089 646860091
    0x90d0c081519020a02150601050d0f0b1207080a060506030a06020f190f0212131203021005090d0e06090a0305120417070302010507151503030e28090b1201020c0105 72
    0x20300d1821070840b40c401400001680103d82509000d82d00031405140200e000d1182d480e032100040c580035092020301c16112040c0c4041207072040301c8036900d89104090307082003000c1c031020b1402100105652882c004c9030b196a200a400040c050a035130314040b4207259004d0054008203600800c0540d110390501034001c20b42c0d40260860490b021203443d1120860f402802d6100400d200c0b5005060071245600070683d081d800300d2201d180450521801003031514003c0f01510b070641c001c6d4010241604500e410303508940c03001c1c00c0301c030f020750166001c1e101c2e4582c03040034074400341c0050f40d6950300ca50141e40450782c10091034000401c1406004042d8402240740c00143c01114a0004681d1084c54040d4070903403900090300010740021400c21105021628800229100814060000500e05e58508140902280f5500210005006c0200043e80b07880d06160001d0498078a15034501100100401d10780c1c01e485501c00c0184140d1078403031224141e40c2e24814003441040000003550b5981e01050b03d5402040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 646862589 1250 646861339 646861351
    0x50a0614040c021e1005181209220e1e0706080606030438180606211002070804081509061f030f0506060f04090206090d0c0815 56
    0x425492000c080e480c0c140100c100000c62500600201c8841040c440915000308401503014440d80c204061031314071510400e4401e81641d061042e03003c903510b082c0b40c01d02e82c696059200120041c0310608240da160002d00302550902c4146450030a0140414030141c5514141d41000c0c4c000d90f85c807642c2c24115038a1051142c144c04d000d44002039110070301070300c20400a440103900081b080c40050b0020388880e884a10040c501c240b09075001700c0442401819115900c0d000d040c02c0794500c203028080c0c000c401c0031000031143d10b019141e545000e01c0843c5581d00c80d1550a046040720848090001d0014002d0323aa00c1c0c0b004007030640d03a078000742c10505103940c854414410513200711401160480b4420404602a6003d00c02420032a180c84a40d800750304900c0701e1a80911b4410040040014848141e13203d6a520910242010703241080810140451154070140194146040b0740c006036250300031280070001c200c0f84604140740701c1c140511418501d42044200b8840c03403000e21032001d03e00c010309100344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 646863839 1250 646862589 646862609
    0x10305010b010203040f0e040f0c0602010e0c0a14090718060518010207030b040b0411040504110306060609060406080a02071a0103110f0a05040f11030a0606170106080c070503070501050a06 83
    0x7681001280d6a210758845c1d0041c0010300b04062101100c903c840a030014040e00c0c0d20b020b07050300c54660301903015540d0709c030300c0140c2e548542413907501c1020b018104010b03800315022140f05140100700000300c0704102025129403c40b000041d0f11501420014102c0f60915180d03001c1192103540151450b030004c4003a0b01060109980c669040d8400a04042901d070301c881c101281c1d840c0c5580e07503c1c1d031000290048a04200800002c00c4a07110741c030a041c82580143c401b283c042c034400c002d2504200340030700481d0280004109006254031520200c50440b851854400c41c0c0d5076982c1c00150090080c0000104000c48624550758101400c0d842e1320706890181a20420b808000d008201840b80307241416070700701c141030004000070720301948107403903801049102148001000210030301662013100c4006106507608004d10841da80007040c003003080005d00826030a541000006001d580008103a921409400500c400400c181441503d51942e0720400900540c00c0c41d98410700a400140124401c107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 646865089 1250 646863839 646863851
    0x1031d030403020a14060703050d09060f0203221e020f180708090a0213050901090b0a150803091309080c100f050601031a01031a0310060e0619060c06111201030501 72
    0x18000070481007171084018403140c5440c8031a80d040c1e643d0b4020422190200f81c1c4c400106012442e907018440000f0011500181e907132800003031040319107100300c0c145003800c0c50b20900180014070200b2072200d6008541c00c0854582030901c0010030800703903520300d039170418240303404026081c4c0403001c80d5004484ca0344421566035105140c49036100301c1c81c100a544468400ea0315100b00181d03520550304144a40004141000c0d1a182d0901514040d203d46114036134541c0d12034942400741440002030507111001c1e51502021030000360310368043d1104414441c0c0d039003480d0800c2040660844400101c01000e030396403058203481000c010010301103c01c070460300704400038401e580300b4400d4400c442e040000c40070039002c142004400900781c048104540703409052502500390b80401900c1c003055094440400c640341000c0c810214207201504145c019945003584010380a20303009154290b91152a1a6080312580d04204000d00f40c0420b00e030220090009111041c0510210180e050b41c2c0100003c1c401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 646866339 1250 646865089 646865099
    0x90108070c050a0f08040806100807051915030912050301080d17070e040e0712020f060301080601230901120201180b1e09120a0312020307051801031d030403020a 71
    0x28034807801c034001c04503044036101d04000f61041e00000c01e018022104030341040d4454824a2908100340c98200e401070307801d20200100f49040000c00050710301a074000720001801380f004052000340c0c0c0180b44030a034070b01c0005103c162213a840000010380010403081d50206c074090142181d4820301500c0e840380a000c0201c02881d010f0103000420341d250038040c0c010742e600c0c1c0d0803c07a05100310340314035640306407100f40c0701942030400c00a00c030186c520880c21541c01c1c035041c81004001059400000e0040000b400100508000800c14a046a1301c0c1c00140d00000d6001070850841d42d5a81245984544030000100d2159000e83d02049070030704c02e0301c074aa4240d020489031020519144148900044200302482d20304032030400c0e40003e04270352129607040c0600f000000b241c071701a00d0f6a540d0b0a0b4802d0101034103140e40280410140f03645d4010461560070860001040707441110003e511b2008012202c81e07190344030340c1c003120006500d413241c2030303400028110701a180d40c05841305130300c114000040450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 646867589 1250 646866339 646866347
    0xc030f2203020f010f03110301090e070519122a0815040804090c02030d0c08250e090705120109020309010e060919170d0501050a150807050c0f030f09010807 69
    0x241c940040190004181d094011114080400b00780030405807a0b080c102e05c0b1100b9540614060496110040386a40c1c42a42503490308040e980860300c951046506554070075071015a800603515050140024181c140c00e120301e0052460030100102400d205003c05000e801d000b8841c16600c1c95000e0701c01c00640e000c0700e1501d00100b91360281001100f00320800c024407003907004803017000803401a203040440c55032010044a000d001c96502207200b41041058448a421041100303000030340e0000706c03403540b804009000e42c400c00c3d810390150400501240c401405042170390014202d5190030b550540c1c48541d81d0001e03403c1500e0300105e542c285203040140040200b01c562181041000a00d07102050608034030200301009030a85006410043d4403190200c0d5400401d4141211440454194506010b0040c0d034281d42d0300c140c00c0c01c03d4082c1c2807041590f019080d280c000221349440750302d564500c1c0c40c0c582003290014401d503c0344000201039441604a0010b04501c1001340c17165025603503903841c00e407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 646868839 1250 646867589 646867657
    0x10b070312020306030109150507080f010612020d09053708030a1d0a030c020319120f03020f07030903020a0b0301081203041b030b0a0e031e0f0c030f 66
    0xa000ca00310354100304400780d16601469005400034000b08180c54035442c3c1d102025401c80da803a5446840d0401c00540c01e8002c90314640080c802c10b02105558546000244042003a01c540c0404c960009406c40b111542a0094243c4541100c265502101d8502c443c140c0082000001d105094041101c1c240ba42c0d8015080302e0910b0b00418a03503e1951051182402400740395491200103140349a164858042044400c0700c0340d101e038540d204040c8a50041504e42a03000300c280d19001e946650700b00005146000c62044c641c07135410710310407042c510350040c0d002e8000d081b00c005800401080c100189684590030070308481c000e481808a02c1e40341e050701c00f02440f090080c503031107a100408944092441100546d071003030186076107041c3e8040100203011045665813043c0d45040b41d0b5024440341703080c644600243c0c1c521041c0110300c1c01c011007000c0d05c81da410000d008541e10b000400d074045440c0141003100c900440c840240c0e56500403400740c9542c0c41d000807940e00000b07001d200d4006100483c03071501c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 646870089 1250 646868839 646868843
    0x706110c0405060307030c0b040e06100e0103050601090513020d0b18071b05030d06090f0603020a15023a020a0f08030a200901020d021c03090812041109010b07 70
    0x150448010250034440038100243c41560075104510340040400c1e01d06400030003414210800d542c1c2c4a14120300c4841c00f08026003580d101d01020303c05a0703803440d00300180c049107060078240400c403130ba50103005884000d402e5002942040300001c9030410a080c80e801440080c01d00f0030100b00d000155010300000501c42007079a46a0000358020035840d5000301c12820402d00000b000807814402036849a00359044004004103541c0c445200780900b03942405100e100f2441c008080000307600d5900000c1048450f8850701d2000d00c020402e51542910a005c0c00742c051041c06041d00007883e10410407144208002c001c0103001401c20450702c001072002c2181002d16412504407c08410a0b40f1581403540c00a002488100d40e510f00000d04d000450285039580140c61100580314200500007a0800c40118050021034102ca0402c4c40c1a185005042c01c412209140000f12804140f9080c0d43c144a404610480c21942504000030000001013003c80e03e402aa46140036903600d55401c2100c0c0184400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 646871339 1250 646870089 646870093
    0x271a030c030f06060408072304020910050c03160c0510090305150a0f0e150912070803220c06180e0a3204020405070c03170a2a02070611 60
    0x482c1e80e020a0700c14a9402a41c002e00492034144d44074099032074076943e90b11500310241d60050440d0120003040c2c03130380c05201e000c0d1015841c002040c00020b06415151a040061060214900341001e0003041640e01c3c114082c0f492100c00185814040884841d41c443c1d03910401205000d1880c852059411000f146e07130000007051800b2500c08140c2502800825000300c040c0c1c0c590001c0c03e460350302d0007490300702c19580014040524041040d42c0300d01a0041c0389000e5640310100041034400e1b0328013119102608a000c41c1d8594990305842074414007501080d5031143e00c000c988005110081001208407013041e199489088024030302185075205d203104d4441c2a0203030b0000613220400d507803c0b40c503502145440030282c1d03c50b2108600561550300f16000004070042c0100710450400d8840d241d08a0b07402c0c144100c040803980e50081030303c410f405c82800303042010030200318a2510390300300802c42c0140342040c46046141318041c003100c1b50440604001885801c00000d21140104400454580300c400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 646872589 1250 646871339 646871341
    0xd1b030f1101031413030e1f080601110a0f14010501182301060f030905070b04140402030609010512120d14060a030c090903120c090806161707271a030c03 68
    0x3860501d1030401990a6081c0003002d0361207c1c00380e54008030510b03940301c0f0780540c1c00856440d2000524440c80104805c1c140200c8006285804400140d0181e0965010441100b091000d15141c4a81d030380240904009608040020031380c05419000da00c502d9078500300c1002591246100c00003049540740c0d0441000c01c0314401803020502c51904c01003d1001404c0106a8000d540e03205031a00609a20842a001c00414148010b40d40001c001c008124125002c0d400c509041002501088041c402c4912a210a000190a05005101412078100c850204d941c595104268050180a40c1c0704003c0c544001d4100003103241c64001c4c04401620b80003080388045a0030010501c0c010013141000350180b0a021044114582d040d0144d0003840c1123032f6640f1101c0c10702d0644c2407844c01c0805085440c0c810900d40251546a45c40385240740b21300d24030801da20381d68a900d6002e07039108041c42d42003030f0710349162162044100000e1000900f01c0301d101c0d00704154610001580c108602040d18001e010320340401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 646873839 1250 646872589 646872601
    0x160617100e0a0207020d0b070f02070906030b011512050a1a040e070b0a090f0308040305011b050d15090f140a1404020f030111070609050610060e0d1b030f11010314 72
    0x43d0107072031003601c05411805001a69251180001702c2200c1100001305207900003004c003a170500c10007000706041d02c018809581507550360b240c4070905000750781c01c211240e00b6001c2c2403482156000924143c1c00020001c80c104285108050b2980500400c10240f681d0708442c504d080912230401548182030103400082d00b0200100d006500c42001142040080040030039078452440000c4000c40c1301d150f410750368529618045003034030303458050708842070540940c0c0d45165030400700b01c0b000d041000c1800102c8000a14181e9500d07141a017050424500d4101484128100390b807040f0408840e2106810590b52a080880240c8041c0002e0b840aa90711030702242c014106450000c444000040010416142c94080601c40380c200000646040b900c0c0d0365540d0034490144070b400d400110080e134600700d01c4c0c24108054040c0b00e014402d540103060301c0700454113014090701c0381c01c0c6100800030301c1003c46580b8203051045c0528540103480c585c50308441c860503503000b403007000c01b500c80142e0751501a80c2c40c1c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 646875089 1250 646873839 646873841
    0xf14011d01050f04080f012703450e010501051e0d02070308101d06011128060b0a060804080a140f0706150b1b160617100e0a 55
    0xe445800e050020a0100c1000e071030946014002818884008140807480e14445030300b075495200c110366880d20a40d0120001c06e07075461101e0165034040c22315208540050800d0107000004040c44183d0040c1da00d040c00700700c0d030307401403003070040c140c4500c4a4851074132400d01f100301d91803c3c822540860810071101e4041c0c40711604d0860301d0140501e440741840b00504903202130345d01c020b800310002000307101005494440c0f11552800303407003405002c449400e403260038001c40800c0602440d05000c455590081d46070002c00c000000c0d042410702c99945496007420707440900041180c1110301c2c0c0e0070503203a00044e0404a41c98811a085070f51990101d4486449a07100c0d130b8400e4001c8030030046400510508010000c0044c041054a144225561042030622804403140d22082e07d2240c418400704101e00004101912040607810390300c0ca90b045c00101d0020328120412030703504c1828500c0c0301d000400b1904408401040395807010742c030f0007a07686c907410b4502c80e580300d001c2c03240e080341c0304004104080c0b49 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 646876339 1250 646875089 646875137
    0x1b03060c180609090b0d02040f060611150106120b03010c050d1d0c121510140102150402100c0510050108010e2a0d0b240d0b060f010903140102040f1401 67
    0x3c01b90010060f0042a004138041d100341d411060580f80d25080200416680100310712250100c40014007444c14001c0f86100d090081842003038104903a106100b000e5011640c00301c000c1c9030004000708810b00400b400a020b07908080c401c0e040843c80d10504524003840340302c9446d20b02640002078103441d84000300b00b05010b10210800c800520550030b14032a0107469034007050250b0f000080303000810345040c80900341300c005585c216045400050301405012410080c80d40c00c0369041394550000d9505d080125241c044814018006200311403100c0344640207580410f050b504610000c1c0b168096003004e56a90f481d0b60000109181401034400e10818400b01110702112401000d014040e082500c440100c0c007000d455503068a590030b403420341d4001200300512240f607030a9904501c0c1c1141c1d600c51961001008140e43c1c010182022090342c0341c0c3c07160b40480003031030b403280d07456546c1501540164001d4105020344c0181f03000c03906020401e110706c0070300c2004841c4165900404c0340040e41c003043d2008030f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 646877589 1250 646876339 646876361
    0x210b0c0a083409090b060a050922110309010507030e060c030a150603020a0801060305063114010f0501090b0d0e0f0709022106100c1b03060c18060909 66
    0x400d082c400c9001c2a54035590304085000c99441243d01418620000101d403802c0c0ba4a42c0700d100100440e4100c1034000055515888007216a800c90701e0303015450700056844400c0c14040715203007500c3c001401000308050750180e11404020021691822000c0e021900d00340103d005903840100040c1504e0076000003180d0040c8801c00204140743c1c404014415200d0700d40081010a4004c02c82450080d44030710b82600522280c501071026081c050081802d83d08603141c81032007103040540420404203040c01034110259030407020040341c0c00107100703021424801c1c064001c4550103d88001002e6105944460940300c01c00c51140c035001104e9039000060038408603002160043c98540504100c0900c01c1c8001004001c03405680d40a40b131503036141e03100b01030075919501451402402081d489140d624602540c0034101608500c034582040d100c020345610400c08610f66014010041001503041004174900c1c9840c0d5405034136801801c00c01000042c050840024800a41007140319019006000756103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 646878839 1250 646877589 646877641
    0xc040302030a0803040804090507050c0607140f09010323042001050306010e041416090501090b0d02031b07050c010f051620180732030c04210b0c0a08 66
    0x241e580c1108c0b8196001102c8610200340003041e0095100d03028046503501040d0391400503078000c210240f10a2900070900401c03081030000c1040da840364001ea01c01c28842880d944c0c401c6810425030a9010b140c001150210b0b5018801c0d15110310110031b591581070445016103d1030b00b142d40e400011110f80071500e04155000d5241c43c1d07030784501d00c15400e00c0d0f40102291034108144034040c4c0006403036181d290788010304001c2100c1d405c00c0a612040c0c01c1d00c206503800c50001d6230340d4580e50342c1c580505402402c00c0c0d0301400f00044202c1007050018681003410070a03250301c1d00f001402841178605000d04282d100582c16034000c2e010006886c03010340c0d205025050901c21081402e000807034126500d5203000841a0700c150140700d402d5401c400355081d28408403580000c0d04416805591407548195140240c45201001007464080c0b42815a4040c00900005d03d0060580301003441501514940030741c2c010103048003083c3e0080074401210a00b04041e11020010b441c1c6a6540c07402c2d0264000010803c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 646880089 1250 646878839 646878847
    0xf020d06091a04060e0703020303030402130b0307120501060902070b190e01020f0c1501080a110d17030a06090e0a02060903120c0a1106130905090c03010509070e0c040302030a08030408 81
    0x15940c49038a42c0855242444030784034a068689503049903c2e004090070154000755041006990000c04c5070341c03140c1d041c2c8122604850710401c58000d0300f907a003205589406a86008240d001c0a485082d07002d40c0128000d1000b195501c40c14401c81c8a4030b0303400b85c944803103900000c01e12022140711a940102c0c0080024172900c03045034860898014030401440b07884005403c81200e00300704803003c1401d1115079031410035490b05207a2691008904001401200c848120546566500c1d25041c5400c1d041400404043c41083c03041c100c9034000c44202035000e20300030700420031844a204210a800c0020000d151981040d0208101e07a0043c240499051003201c1100040640000c042d12401070f8800040c481c00000e8544075510a46014982d4098407041c094038040302c14160420046841c3d186e0002a1034455403001800e0100c1c414825030190f0906092000440d000501d500c101d561803400c1130400c2c1c07507690920205106920010390300d5071004812001180c0800e00960700180b207401a07a03e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 646881339 1250 646880089 646880093
    0x50c04060605091206090604031b020d03080106021618090c09020408030901080718141206071d1801210f050106030b0f1006120f060b0408010c08040f020d0609 70
    0xe480d041d8201200250001c01d01590a080040c0c0b84072030018050040c000c0c5140012080365070f08001003001d0b0810007180f1081c40304410f05600c100e402d82d00500305403030540313443c14040c1060b5428031175000140329004c518000000342600945c140d40781040150000616a5144400781044000507103104550a40006910409100600c01000b50501039901d5021b10390015007140c2000b4502c500f48000100700c4000d005441c0900780a0780d0441075444c1c8804502c0340030800c402d0034032595005c98030400301400203141e001004107041e0798907441314090242841003880043d601501c02010403045a100502c085180100c04203c2c008034072884061001041e10f0f04a03142006a07401d80f22a50742e20004c2c000c1c403078000110356200c0d080d41c0042c240d03401d1070400c3c00d001141c184148070420642c1923aa021b68015500821180104100203002c41c64403420791000c250b1107849200b40035032801c0701500c14240102c03061446a84c00402e8a450540d941e028841c0444e41780004941c0f01d5914180c40c2c1c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 646882589 1250 646881339 646881341
    0x1060e03150a06050310150f180518010c03090b06010e060301091d0d08090d080c2b0212091c140c030409020301060309020108060a080703170c06040302030720010c02010309050c04 79
    0x491b4900c603050204800e800c40c0e000da031021130301d03801450441070703104018404d1000d030094280e030720780048800148650382c1029035102101031126034181d80d401c0600f4403220980c550001031416003c0e40600055444410040d10409400d81001d41c210b03c040c07004000d8104264810750000042c00238491500d404020400c2c1840c4924244c400410b1f10700b014010003039401c0141a25450690170110310070300b0540210a114010741c900ea00000000490302042d0310ba210410881922550105540358a03031039441c1d001110382100c20621900c01c914489480b400300250b1145910341d540c0f1582604e00440c885030b07810390710000302c0c01c00c948030130440040d110915100442c0244801d60380003681612910005003410b4019100340e100d22030b111400c3c4400500410914100c1381d00126512141802d4034215006014180c0340d03400e00e000d18001c110526401000411046d07108079402d900b18000d00051100c4c0c1c400d4030084900003030140b5030407001540603a2101c01501d000e041110516000900010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 646883839 1250 646882589 646882603
    0x51021020d0512131e0515070f020405270c0f100c0b0c032203020d1b0803040309031b14090a09150b100c1e0222020a0801060e03150a060503 62
    0x1c40031440313038404100510001e46a00c0c40c11449419410705c192600307001074041c03184020000013031200040d40c0001c0040400322560a29070242044c09180750803400c100d1480c544860741168614280380702c06498501094005044400034041c07404c1e1040359003400040304c9403140100500c40c1c5a0110400720f408560410b00ca1800c20400c00d03500c3c5001400c40c003010aa02010602e0f000d10720599400182e00072070764445007601e910300389103998606088815020001c43c0081c181d0f101c0001030200b17065000b140501034901525a03001c3c030740e02444600c3e000c54264030400340d101c0a0030741440140d01d4010001350300404003142c082514941c98940417803e8803c02e51400200d581d40c440044135060208085214059500f01550003000a03250b0761515841402041c4003801042c100c02d0441d0740f140e012450005c07100f807a0054041030b030400f000003540200f042e080458012000015490710684a5040415019000e4148c40030a00c07010309444101a100c04007036074880f4404139007510100184 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 646885089 1250 646883839 646883857
    0x216081204022b030f0909110403030219051b010c0b0a0b0f04020a050405040b1c060204051c030e121c2006070c030c081903051021020d0512 62
    0x6103001d0070300d0720420056580146844081951507800c3d100454100c50300800c03141d806007801c1c0181d020303c00084030481c0c00b9402208030a46424800700d80c0081312009001924400e408540308042900c0c051410300b0b42c1c0600080082d80301c0f001202003407100c205a5040e4103418100f00c141050203903101ca0003001d04072001d107071413940d030025102c0500e00301451500f040002c0c0e6045142030b10300d110041051007280200341c0110f0300c0c0e200e15a8181c8400348dc158080c420584096040f100364a40076010758485d02c9014403680e113404403076183d51189020650100d52503103070f13518107400d20014803000200d07142041450b401800880c1013078a8842c0754180801d2030f280c0d1040c10403d208101c0c0d0002060402103a2156489003041158050b088002c080b409900742c14a803862a0182c0b0740284588503004144000d000610310048580e80c061300080d00403054070360400c00c0641c4030000c101c4030003c001e100304103044c1c1601448016040c5440e0860440c0c0c020000d8a00c01e0311303a0a40442d040c1e11040c40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 646886339 1250 646885089 646885117
    0x20d050901061a0d050c0c030708121b040e04020f21010e07080607050304051204230f01020601090e070f0303080f09010b010c080d1b0e10051c021608 66
    0x10094020400c0c072038035000e040400d1680800f00071107030044955002e04d10040507102d81e5000800c075030241440079520078092850440b0340d100490300d08221079412101380380a00c04441404510280f0341d510700104421221640f00341440e00d80f400c040481c120281050341c00111010040b940e94454005003000003402c4241c0020400400c1d02c00b40c00c5910000034030010b070300404001c1c04010350100c0c0c820380003591440d100d42c0b02d4566091107414400f10000860304810b00140000b0303802c0c650992440c403110f080e802400d00314018828840752001c02c4d049940142c01c40c03001406030030590760141c8420803090f01101d01c90781e100c2c05000c04007003d0343c000f580820948001c01c107041d00c0d00e040d402d0380407403501e0003400100050000600f503d10740d504000d00001000c1540e42685505500401070800c2c41120654101c119803005400e00c03400342d200d05c0c0210200c0c000c1c0b202c1d01c0e0081b0200c1d038040005200b014a801018414403000b90810505c400c56903840d1b003102800b00e03501001400c21448a1382c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 646887589 1250 646886339 646886341
    0x5060f09030f0d0e160503101107020105030712091212023103020307080a1b0609150302090d111e090a0c0201240906210f050f030c160e1014040f020d05 67
    0x4105481c00300664000e23100c141c04c000141100204120550b40c500354203003011526510780c1441a1040701c100c0040b030a1341e42c82c2c0007450341032140d4200c1c81014541c0c00e0b01da41c0a06414540202e0507407103081034490700242c10b01355018900c071094109032180d8005181c803c1040d0303101d42c002410000e491340840c03c980c1c4184032a20038418081085410b500c03d143c134414115203006406030440d00300f03100f040102c6c0381020000c1040390194040b1030641c2c000800700300e5101240d240c44110f411034200800e004d01e0103a829001200181821041c485100a01400542d9204400740f03001d01105c868890441d503c64200e407655000d981480845c08000c010b5031100340782002222400c440041d8082440c081e0082664012003980c0c401c42c1c412160405402036584006061161074280301c0da81c240e03020b201c00a44d61550110106000321841c040101301220140d17161030b484900c03a010350300c820b042208070b801000b00903a1700081c860450070141010501406070b090740c004a8100c0d040e40c0d808281c40714 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 646888839 1250 646887589 646887599
    0x90c05040507050403031d190605030f1f0302090402040f020a0c050c0301020a05090111210d150e18010f05040c050f0a0303050d0e030c03031305060f09030f0d0e16 72
    0x4040c41d41d015400d890202e04262440d280200003040208035100032240b42030000c405078440e19145595000e62000d01c004d826502c00e401009984111014000c454540c1e011400e4004003428488060425030414203440d1308503020000091130190041340c1c01795940b0303c0340c40401120b0000d40300c8009140c8440e1740d454502d00f401070410179072003400342c801d91040208500c1550807509030748040301e0a1074070403582030407800c440d031030060544e4102c0b8680701044810081e158813880107100b445041c440511150110b0314500803204182c3c054018000d42d250002140840031001304900010120000300741646a07c09100890b07005880564607907004000a02203030401741d1140c0c00c146801e458200005145880091590044144000313100e074071049407020b0b0035820000d60b00300202c4101030b40d130f8038104407002410080b22140304070340c01c0c01a08005815403d0000405220320302c000040d43c90504a419030b00398030b03409044e1520340c3c240d41e0802e21300701c0c0200300030041c1d203e0004800a000c40b4241 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 646890089 1250 646888839 646888841
    0x9150b12030306010f1b0c06091502072303120315040504200127030b0106021c0e03100203151f020319031d0708060108010908040905060d1704061403040206070b0408040504090c0504 80
    0xd400c020f2b00c02c04900400c0003810740c00251001150032913a01c0b00d02d0317240c20410003802007041c5218180d142c810202640c2004088000039070040c0540001001101300741014002600c0d030803140031302504104480360520010a0580c0b2815000500d003c2d141c6105491048440c401180b039034111070415180140100130010110501500c240d00041000e4908182c003418a04110701c0c05c1380402c40c1510104c5101e072820040241c280c640c1c42c034150348a00d084900c48142c059103c001500c603495500042d0b200b40c0a482d146200d041705a8042c51500d540f0303100304602c010300710300c1800c1015500d400d01050b103a8540c1c0450004c401c040081e06a4510782100d2924110044c0c0000c10664074103543c4000240000044400301c03407107550086900c1e56070500280080c298400045c14038402d80e19160b00380c5000c2c0f0b000b4005c4d64525214211100340030307000b410b014002218020741001d01003144e0b030b021504080403594420700c1001d0305841c164882c0046020b45580700c204856256504000f80994901 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 646891339 1250 646890089 646890107
    0x40b01180501080a1401020d0614041104030807061a04090302010b1e060909150904030f0915090b09040b1207050301060e0c0a180909150b12030306010f1b0c06 70
    0x101403420700180d41001c01c00f036114485190300500c20004040010614070081d015070b42c808044410410861780d44201040c04400d100451900c0385150024104404036580c0540e01540d82101c05581028201c0c3c0d1408010b24240c4050124420104c298114a1b51180110385400d40b080c2d0020a04540350310a000601c020107981008510618030583c050b6240d00042d80c250a10031030701401a40c0364036080300011007080c1d1800f500045440100f000741500440e071482c89251a42e100303402290756443c903409226910340d808000540d42d010422840030107002406e11068020130003d200316041c00000c03044003040002a0b07854001ca0300401c8546000e100300002401d00d0141030314189001210001544103800020b003e11442d1241c81100400440301c030406088000b100300f00c0002c69061445003001d246008560042c03c103011400c4a003003042e907601c2d0a01c40d4200560541e15118019600d01c00101c1d18a01005070300c2c80840b0501c050f12140004450140445020240c14600c008140450b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 646892589 1250 646891339 646891379
    0xb010303030c08160e0d020a05190503071403070302120c030a060e1b0f040504030c0c0e15030d090b0a0c0f1104140f071b02180a060501020f1c0314040b01 68
    0x207044901d00e003094010008207001c8000700c0d02d01c200c96176148002340c20780070706800c59170300800144d050484442854004000761201201143c3c0e1310703a5902c0009810800e00a8565015000001d080005003800c0344030003903004042c0b05441201c10500046840c0c00031102064500c243c036240301054001013400410712801c1c1d01c4116042640043d8041048041e0400316070b401f4942d60b40008051620607154003aa07240d10980340f1000d141e0b2004031740c0e43c018050b203d604140c1c01c4400c2c2c281451030009110854811207031140d5030041c4c9030400480c0150401c00c1c9440c2885078280400c00000c00d0381e41e08520700340c85144001980d011039014081100c02d01c024601d010141c0406004000c0c041c0700c80076601c211141b0f84280320303141d8001501c41100d086240250040344543c000039007850014240d81c0f00c0c00d20440c0c01c000180d030f41c1004913521080c012204049410942e080c03d803107242c103003400340007109500b00441c184000046904240101300c4042d166401d5160041c44800303109096080380301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 646893839 1250 646892589 646892611
    0x1b13020c030a021c0504080c1e3625050405040e1b0303030606031f0b0d020304021e060a050906091908060a1401180e0609071809080a1b0b010303030c08 67
    0x908000401c1c1d9180e8500c01e009100d40300e0802d04c00304003e011034564009d040080c2c00c0140d0740c204054000c4602c4050035070443e001040a8030014441140f10301c40f84a060166410500d6000c103a44403d18080f6588030f400810000700800310365500c4600038005040107140080000c1c88904106c1d40d14100351402c5680319800c03c206000040ea60f51081d6504107080030501045401d1880360090b4000055101d0418040085601009112543d01170761042d8003d4405000b04c0d12101d501a0b0f08040300007030076030310030001c2c07007841d106c203200340e02a00a42e10007401092809412000145031641191001500e401036440b0a112100782800b9068000d9481d000c180040c1c41c0040601100550500541001d01c402420845000425070041c600402c1140d055601905003803051a03101c1c00e20340500d5405207119004190360308080d200e8000100d0b000100d41c1c1c1403105042c0c0c22140e0314440c100702d0b010440d0101c04007010400308540c1b02d000718403984002540c001c500a025100544c000d0014100d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 646895089 1250 646893839 646893847
    0x702120705150403260702060a050c01060e04050f010b0310020a030e033006030312070309020d0605013308190e0105070305011202010c080f0f070b090c031b13020c030a021c05 77
    0x815186405c0d1b4580c194110340c100d440e84030b14101101c4a00404407032407420340c2001d80004000c842c0c1c0c24003a00460144080d150b004d0a44a0b62509a1b184000080e800d030b03000d58000e0017443c09aa001c0d0107501420701e00031503020518408103186070000d65400360140d907201c7d03005021142242c0d11800a00680d50b9100840c540000000d80720b002d0406440d002c1c0f5401c100046507648641d001094540c1d00610a203020760141c200030005002c00d002c0d5401003c0c0310074001c0c00c40e08000290045038014280a072104404441d0104da80c550003800e0304242d4041c48140c0c40c1c00607034600903507052680c41800003420307107081c0c10010103403001a8802c0d80d2000d01f100740300c405030341d100b641240c5040c1c00c00c501565942040d107003080103102d40750200151400110340c09080114031100305000b079460808540740c0c003141404240d240c69200b4120000740c3e00c40c520700e040f54246880258081d10001c2c100500b8a0b41d80104030741558080b03c50040142c201e450b0301122100c030001c0600b11070350a881c1050134 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 646896339 1250 646895089 646895153
    0xe040615080d08071805060d0b040b0604120f0204020f07050a02010f0903050a060e1f09112205060d06020c0a050d020f030906090a0f030305070b09030f0702120705150403 75
    0x502e0390141c09441040300045c0b00140106280c95840b0007480b01809150b0b6074100c1c2e20003a0010150f07960007602c038601b4492512840d00d003140c181e8098850000380000140155a00d41461030071905c812a0415028800f51340e180300740501a10960740108060000c0c4107542c800103084c0b55203001c1c03a4091000112013800031510004502c5041c0f58007000c001444c59000c90f03650b29200d80401c00001e4160a01040484040c280c0c01036404980309010700070b8503000c0c210800c5503100780d440710420b1015042c401000340202c00d4100940090005d8014880d65030241c0701c41090344c0c810209100503170710000e40746003006420009040c4114091001e0084800c0520001d0745034410443c11511401011811420641e51005940c1c0200141ea5070030703a29580e42d00d400307801a0070080c800d441010b6500005014000c02004031100310141c01051841c0091a60801171301c280ca9048280c1c4378401c1080114454581c40e80809021b030501450b280c80314a18940307408000000e0b0103020712070301c00c0c0e118008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 646897589 1250 646896339 646896347
    0x60501080705030a1805031b060a0b01020a02100e1e01080a05040c06031a04020307081603060308070201030504060e100b0f0609030c01080903072004060b0a14130e040615080d 77
    0x5013003842a100440c084402007010700c0c0212084102500601000640b0145101c8051600110382c130b10209480715980c900d41c802044070307007206800340941c008500d0200180780030304885500755114103018044c41e0101e404200c1c5462035543c02150503410b0710582c81d8075030b0441c0d0a1540420f00020510651900e969034800b9401c2900c500c8040c1130b156036908110b00c0140b10440040f442c050021034482c03030712a6000300560000c1e941100c0c000b40c69008801943e00c0390040c001920b030006581031909c02c050340110000c0c88020b10965845583d801c03403003180070091141000d0683d60361400b1402030940c0741001900c0c00c0e801c004511840302000b448500d0348001c6130368501d00000b400c00d4503480d9149004035083d841207400007407003e01140420703943c10445c2a0400000791043d1030810640343c55401000c9988118142a000303d400c000b03440c8420656030000380f0006030440c03081c0080a40d10340180038031803c265000c4440c19220784000e28403082ea4541d000040c01100c1c001d02888900b542c02038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 646898839 1250 646897589 646897591
    0x30b0301150b250c0f08030a080f0c07081204120e0a03022403070801080d050a08060d02120d020c040f0b09011502070527010806061507020d022206050108070503 71
    0x2c0e0201c800450310541200d410011503c00341c2204040f070404405500d8600a41c4d5468080c400500d00c21200110b40070300c1c004255800c03592a074480350220344850b9604c002150004059014140003000000005a502c901422140a02d1000c0140e1818645850718010250103000407c1020b20101d1030380070b0396440e69980071a0740503900b0140c011045510b882d800038a030340c0480c940e00000024040501d9211551604030741141064901c25400d241040f156442951540c02c0040c4c140b1021680d1464010b8504610900c010708083c003c2254250a07410b00300c46450302c0700560802c120440301803e25018081508110b103004002c040c0c00700e0002840040180923205032201841c46001c0030500810000e00600700080428144003198109480f40c001302c040a6101c1140c2c3c800002036001000483c90302524008200c1c03004007982030035000c03043d00010801d07a4000000300b0031310096110300b8480e6580441d400c801c59141c4607a07804403000d403152940203904104002c8204255260b00105503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 646900089 1250 646898839 646898849
    0x304030f05011d06010e070f122d020d0f0605030a03050706061a07030e1e2710080708060103030504030f06020904060e0a150f030b070210150303030b030115 69
    0x41a82006414002e005003004040d42148010303d030115040b50000140c0541203651000e20b1200c241d591120450b1585485918100414104030140030203510b55044504124400d900c0003820229006070290080c042d503a0050b40c0310740c0003e0000c8410450b02800c020600c2c20401808040d240002203652059244005010480041000d0003044540c1e08078800401011a40900e191054000d40956600c444400c03004900e040a8103d85030502c0c100e8180c4580750100c0380803418031007800b845a04a51041c1d400340c54554503510030000740644179518040d4051090070390340f15041c01f00307d610b0040307190021280c0d03078083ca0041000981c02000c42d81500c0d84001644062541440d100300030f03029200d00681e2050602202040c0c1710210104039120b0303280c105081c08885406540a85c040000e4010342d41100082c0c941400410410a01c441d000020340c4100c59010b14444200030440303900c180c10340d0040704800b00400505078180034061903158100e00800410105d141e2411000b0260312034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 646901339 1250 646900089 646900103
    0xe1807031802090a0b012d0e0904170d15140319120e0105040b0c06042102120c030403170717030f19230906090f0d0809070b0a0302130e09030403 64
    0xe15600c0d912440c003c0f24001034000c016520071441c1f594800c1180c1030b03004590002500d00080540364036001c0211402990080c40d0700385091109400a03c180c3d0107906040701c981d4403400d00702080d400c10000c0d58000c0c180e240c501c0e8029155001058141004007458184000411382142e001c0352251154600310300b02030401c0c502400740030006075514000c903444075128035400300c4c0e80740c0340c0d90300460040c0c80740348280c5180c0c040600c00c040000000c0307503036540e00d00180c0c40400400c8400e2850b1700146100030140003141d04280e520b54444204000200c405007240d0340c04101c00e4100b0100381a04240690031401003821131034200180208240010101e500e89070500d8525003180b0300381d82c0701010790030300d40501c440ca106004200300b0040d0415260010503202d03150010342200800f180d10348040c4e00321405170403511010b20049400e088060b014503528003d0100000e88031920100500c0c00c1c040c0381e107003d40c881c25070f4800315004035a56800f0f1142c550701700c0c0c10081405d00101c202e60035250300405e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 646902589 1250 646901339 646901351
    0xf08100506090f071d090106051c021c091104020a0504080d030603030f0e04060902030127090b0f090f070612051e01090e03160804050306070c080f07030e1807031802090a 75
    0x1420740390105c1121142c0e007001401001207140b961050041103141602018543d603c120542508120f10034845c185103003035080b00c03800e4010300322500b1030b020483c082c4240315028400280007900300d9011224050100b0000601002025000e102e0792070000f1071820b041150900d0360b14003400c543c04c0e4810b200d0821410603c90105980c3d01c3d403011000e003c03000411901c80da15101c48083c041c01d2020352106a0b140700c404442c0100a03801592002ea40c0000005601e848440c4d1140307000c08050689260350040007000e210040042000500420895680e038001803268075441046520203007001803143d031401509000d102c120242d56044481d501000a8400581d004445c00e50080002c402c885800d48400e040501030355602070010358030220280d03029600c410400761031241702075400070008442031020f08104803001028000d80740c02410458084070a040001d02d4059500313130b104224142c8407051007103075580740c40303411040c00d80742c204c0c0071110000343c0004020040090009846030380300e40c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 646903839 1250 646902589 646902617
    0x30406090f050601060e1513090203060a030b1501090e07020c01050a09031b03060e1c0f0e0306240d030e10020a08040305070303030f05040f15060f08100506090f07 72
    0x2031070049060341c00400340c0341956141c0d10003d1600603001c0007907200c0e0060303402c44120381c901d4a00311541051202c1d41c0f10811840c01c5050340194100502c10342c0c5c8807040c04800004030b0250001e4522400c0c182c04600002c681090000d011140c0d190030140d000c180d85020800c8079500041d60703001d03182090070f14980b50091100201d5420741d058100400d55405940c802120200c0360000c4400d40340704910600c990740841f0402a41c1e0402c03140d00a080324600304160076414040c0c3d11044400c44140f51540c450642030b00864903044081d29013200410740c81d15421032100ca140c0110b058140c0484090f4541c0d18141c5004014112003030b02c031842080d00d1580903131094001c03c025001190b120480d02c2e101ca5036401c00c542c80c1ca64510099000c2030034103203000b0b07084505204907441030b60300c8403103400c034040b5540720503401e44060b02c4100801d0369684800300700c0d160600f0500000300940c90091022156a40c6c020043d202c0c050000d50140c1d0b0124180050101c07007988596214020389070040c0002404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 646905089 1250 646903839 646903853
    0x70503070f0c05030d2604020d1b0306060810061e050910051507150605100f02070503010e0d1101090c030222020f0a030b0a0303081902070203010212040b0a050c03040609 75
    0xe03070f00040d07140c45014031600381150092050281080c070032030384e05e07082002e040e05d01d151001c0441d0000c2d4030052200380074000501400ba00201c0c0510307103401c11a840d0712641c507001100c10710f0b0001c02040c2c0c040b9404034030461040c0204000780042800b0307a01c002880c1192078254882d1401a58855081c480000708090611040100200002008a03200c1c072745512200c8a02da01004c000c2d02d004280910150300c0340c2d02c0340191021603070040c0010301390000008080340c807250300c407001740214043c0302f40c0000c666409001d02020400748a0207010140d80840028118444030010421241d0601155030007040f5049455801c0360b40548444ca100c00b01b9050001496101e028501503c510110b89604050501009080c0d0707800349440400c140c4081d0000c010003d40799220040010740150001204000907031104000c0c10381960025050840340d44c0001c0c02e90704000d488219560581c1c04000501590744045500311300d04110401ca203060180303050b06940300c020300c050841601d84031b1101c200115 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 646906339 1250 646905089 646905113
    0x20a030f020a08040218090a0f0f061401170f06181c030b040606021506120a0b010e1f06050a0509180414010b041104150e030303010311040c05070503070f 68
    0x1180d00455a07000700c44006848024241d0341a03025020a03120004180340441003d40144c0c0150004c0095000580c0c4801c00e410001d082103a080904000392000150303180101c035207543d000715407203400350704000d50078000506c10481c2c0707640c5900100c04400340c43e2020400a40100d61031090106550003074508a1400c7e01440702140e078542c1c08656581c1301a41030b070080c070050038121400c1c007513659a104200e0b5501004200c685200401c900803a45501c2d0403409460b01c202c89006940000f0503179200c1100d0030500b640a50410a032410030099200d84d890a191608006c030b2032104031840c104113000b029405240040000c0c000f000174804010307990f000800c44201f04e4100d11a0591400d46400b1000410251000d000c0d503003080252a4140713001d0107016528119681e40342d0a042c0703004d541e6402c2d5940c400c0010240580c070544010f0b20348041c00214043e60150600c1284404000244421503500384113000400c07000348500000a240481110001a002040e05074141040d0825040c0040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 646907589 1250 646906339 646906361
    0x132103020708030c0403111e0f130603290115050c070f12050706021f020d020c010207260301050a0314010b190305060619050904050a0204090605041b18020a03 70
    0x1400703c00c00c54030a0400d001042039920a26000f5080071010090040c0700003c03c080000406000c50100b566080885480302d00c41001005070340516107000000084600c81d81060720680300010400e8506900000c0c5081c0380303040340c5a10505985072400b221850005c440b101c1007001000220301c1e40001040050101601e14050000a62a56240c4000034845c4030402100d4601502800140440c0003081c08128000e13040700c1103c0300c02131400c50400a5010588040b5a142c0c203012030703048030000348050b01e0207074881e0b080d00c26500c00c801001c01e5a5101e103c2ea90b9111202000140465140e9840c81d1086075441090307400c603149100c08107805850210382464106100b0a5400c0700e004444004000b20f80c01075043c3c0310103480b10700a00c0800004501818042c1480c81c03420009410f0a0b043c0c10f0b03000e4000c03401d03900705243c00c0d40000c040d21044401a0b503429241d0007484280f06650b600200d90400040203030b0b11452510009424130b01d410544403440c25404925032040030f00a402c22520b002c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 646908839 1250 646907589 646907603
    0x90102041a040e07020c0a0b0705150f0919020d0210030b0d200d0210050705191a060904030e0103051503030708120c0a0504030204020f04030209070908061321030207 73
    0x10070301d069001504180314080c5003220090201c1c10450010844010805c03000c0c1c5040105418441210960b5100302c20480701481441d015402c0d40b00b001031124020200030009d100c1500304451281d28190305107105640a00382111100c2c0140c1d2500e0550b40580e40c10340394100d54240412051f001850880c01c12600140c0c1140c65100b0428885805a503504626142d410440c03501e200340020040315290003904502d45170440e040b11405280506407440c0702e0303421184541c44074008442c03021400507080300c40c0b0007119441c1001d040d2401500d40c0c000d1042c0c5a001c010310b01034500034003001c00748881d181416644c001041003075a04510001910030061700700d907518509483c02107219842401c900310321200d40030201e00c4070503d002c211406d080c401c4c2c0d981d03400c0030309540030407009501a80c1d0218520204010005c0181c6030700481d14032503001516146185481c1201c41401d04030002d04004600055140c030900182e040320311003810b48250860b44074450403813a4143c00910843e10054610 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 646910089 1250 646908839 646908869
    0x1d04020c0303150118030b0408130f090c0327060c050c010c080105030105071403071803170c01050a2c01020c06010e180109110d0c0e0901150b070c0e09010204 70
    0x1029400c0c0c1c030402c0c01c1085ea01c4101c4540b2210001c110300e005800000c1500070b8590108000c9482100585041c0000d901e42500300d075502c0380c041d45850b40582c00710404c0c035116460712002c1c5826200340c0500c0e03000c0c840303c950030598512070b81050307034180c503030091201d680d13440050f403820300c29400c0c0c4443c088880c000f0003000340c040d000504400741c01d109041c800d6003080e0000d1b103007900c240000000c104030006c51500310b403525070b000e88100c4e52618800c1c030040b90741200040400c2d40c982d0b1005803100230748103199454001360680c50940d04001e0418401c607062800300302c0c55039040c1000d00003648000308490704500d1802ea0860180c031400d0b4420045116080000c83c50300f96005a00340958441c3c01c0020004611081950a965281c1301c09080305580403048003c5003081543c0306100351044c649a0080b030b841303007284151010162129203c6039940e443c40c0e4006038603440e44d400589503070b0080c5d50801516555080c1661400e02910340442d00d00700124546e81000d40555018004030b12014440c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 646911339 1250 646910089 646910101
    0x15080403211d0709110306091e070504150c120320070c06020f01050c04030f02011704050708010e030c0303061017010303260709052202030a05040201030c09061d04020c0303 76
    0x55501d2500b80080a805411400074a1041c244031740200c070b041e0b1126440c11680c2c4c1d94108a0340440040c1030088202015840460039036941c02d4682c801c04584c1c46460701d07541014011008000c003448904140040240e03c1d10106480750040d400f0350038980ba0200303060581c524032080044031384031280c0032041c001c20010b0401202c3e8075008190b440c950f00300d4603501102c07050395098a4040d900400c1800c1c08110038408a9402e24103000107a006041c580c40c82404a00390403081e100480b03050b00e254010a4050050030301c00c0c0100a0002c60250043d0304043c2c402405980b01d00c00500307607500c25a0201095a4003d0007809003020345600410482203960756814054116a68070602001c0084441182c442091100c3c3d00c03607011755000c1c0c0d51411103606060030f0060b8010025001e001d80d852460580044d5009800198032034240c1030b00204150030188005425200401c5410003480300780ca00c14041c050307000050030801c0b501045000a110400d0001c14002c0c401c84a01d192180000410002d0f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 646912589 1250 646911339 646911371
    0xb0a0215090c090f010609050d020a17070510050406270f12020901091a210a05010921140703090e091b0301051e04080c01150e011508040321 62
    0x400c0700c0c1560070045a503214400304514513401d0040700c0114000c0e0300184181e0030718102131a0918400b4083c032440ca0784442040341c1c01501680c00c40c00d158048a010300c040d09102e01000404250f50a00d141001c2c10490054500c0110f805500c000c15102c02200960300115012038000f010800b00480140351100000740c8007080802c41607002d84940b500000300c016480c4a408200103c039104001d09a009a04100c10045d000c20700a51241c8401c1101c1c5144105001001ea40d42c0310300000030b4503445030310f000c40b42158450209200d100103080e446002c00d80180000011030b06a290081d039582c080c0c42c050714207107050703080382c2d5070301162004003c1010800103030b421540c8000d030090032118141d141050b0a0302c208a0760300489071410f405003000314003000720b0103400522a4107194100150b00c0a41c0d421602c003151041d1a80300140810031200c0b01d00820540905011101d129039910f03001c2001d04503900141005041064019040380d00b00200410300f91100811003044c02384074481c22040d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 646913839 1250 646912589 646912603
    0x8030405010c050460020601031104020c0c190810090206190203210702060a1b0e010e0301050f0613050610210e030a110102130920040308070b060f03070b0a021509 72
    0x10035a81c1a14002e017014000920141242d500c80e004104040800081c000030307410000119070340c4d1090020f48105a5104910f031a445001800c002000901d4610050714000c0c81d801c81e624840d141880d002c0c0583c8507481181c00d0a40540d42008002c01c0c1c018003203141d413040c24900104d0021400061303c608030442d10682c06802e00d030f0b0880d01d0588912a01a0480d056030741d24118030401822205212402a02c110b020305005040c4402001d544101117829103400701c5189201c0e000c1202002207903c1e03c51032101d040c102c3d80b4070802041c80c01a020a444400014001052061680000360703071420340083c411031809091420311070306c5020b1000035900d80041c0700103404900061840e0200400501c03e94041c1880ca10030320040d0b0703142009000040c00000b01c000c01c0d12450741100d040d8540c2c100010801984540c0c1260b50b00c000c0b80c1000441510042c1c0420301c02e03c500d00a450310b9940000d9104240c5004201d110707600c2c03640b0a010b80c6010707031b04446078038146440001c120300c0c20b002040702 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 646915089 1250 646913839 646913999
    0x612280c0503031c2d050405060f100e04110301090501050103030e060f0d0b031e030a030f050112061a12060f01090209060a0c02031908030405010c0504 67
    0xc194181c4070402c05850380a42c524000c4400324204241c03203800c02d80d4000350841c01c0840c410202d016034683e0041164111100803503402d503220b406210820204000080d4096908005645a41440788080200315134078440d50580c1c0030040c001c98203120501c1c1b06010400c4004000304201040b5142c42d5010780800d00c4142e001c6407024503540000d003031910440d2400d44600e2642d46c41c20001a20a00081c90101c2c5081e0701849145500c084021480000c5030028040100658540740650340040640f03405a0342d00034610b007040010040b6824241800c000f0551110001c02d4108103040c0c154000c00c5260007090780100032541da008200703800300e407007409540a500c00c40320985e2a5004d14060b40f00d0034410070b0300a10700f00544c000b010310400c0480c0c4414401020303140848035010000342c441d448918240c03101c42d070004c2030104000003441101849211070521a082500e4200d0a00d02807002c81d0103141c4a44101d80c00c00c60080402c40180d0010305140005640e0802c00d54502280c0200b104007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 646916339 1250 646915089 646915103
    0x18110102190b0906180d0c0c0306020c030c01060f050603040f1403040b0405041404051c1103040905060f011701050402090d05010c0c0203100902030309060a030f1e23061228 76
    0xc41c0d20390300b071040001a141d905c13500a10390308800001c1203801200803402500d55030701c0748002000040590008001d5944140c0c002d50321100301241d12805c458643c0e0010400d6266038404010688811099907401600441c1c11807859803a0700f4a01001c0c5180165280d081c040010080740d00d92400c0d01400507900c06490811454004042e40319482d101550f0250050388101c6007140245c088025181c0c210b03056181094290804a01081c559000741d0000c5030350340d80b510200052401c2c1841c8040c0451030910b040d541802035869013086000c410b002c1d5a0080d60002010040741c1c561040070480640c0c0301c402008820200078008016400c42c0c3ca04074800d0082400032025100f8038011407040b2074000300918038269070300080040a0340000c0c01041070684074044081e141459102e010a15003946034480b110703840c3c6a20800c101c0e00b00c00650040c1c82c684281d4103135004101d41250ba80500191003510002c980303018510325000c403418000441380640076002c01b5090654040f032003803a00c9090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 646917589 1250 646916339 646916341
    0x10b03071d0d331107140f0d080601081f06051b0a0507050a150f030209010c05010e070f060201060f03020d020109230405060409122708150a18110102190b0906 70
    0x9803d00b40c5140e03100c4030007207000a002c01d40100d05030104201906a00404945482824011640c1040c1e0300c1c620748000300b01300f1001c020ba2035800083c2540c0c41281c01208207056107800c90a801c1c21071940c01a00100103022907080d02408041e96502040c2c103242003292207130078407403400da0360701d0070103002d5903001d030714281c200203123049000c0c4091705607a04940300c505408000460481c001d4101076412170400840e1041e510210310284110b41600c60030740007a003802d50504030384120320903d0364014404c580c5048010030004040ca410901602c2d070445450080c20010b000485280e00c55030085240301440c68080000d0070513064124019a105460074000341d0b40754003c002c1110841302001d00100750041e060125544030300c146c4080c1070146240707a140d01b85c0d5240020070303809840e00310b003c01da4130400c407003109500b0800e5041e81c840540d44051001d0300c0c142c10704014000c565440142083c00800c0d219429a0091100c0c0307802d0000c5201c09412081941000c191200e0261500f000c4c80c06288 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 646918839 1250 646917589 646917683
    0x4081b01020d210e07301b031502030403080601082403070803040611010b0102060f070e0409150e01060512120d020d05151009050901170a2009010b03071d0d 69
    0x1b2208088450025800714280400303038880c0550b00c4408004807020306404032001c00012039044a2160301c10198100603100e02d4580b4010b0408003001d0001814445500100101030100410880701003103120040da1901c40380101007403904c005900213404600000c100400d106a000025000200d0040003d100441d6118010780e1140d800b42e5405400349415070000d0f1506000d01505941c5800241c40081c406c00755441d104002014556081c10310b6840e0f41030301c6200c000074094034010b0001118110040703113040070181e681d551500d1141080280204e8808100c00007941500c54949031003100b84151b10301519075508407803403e0500c5110b6240301009015a1740310703150030000e440000c0c1a108040e42080c2d82001c80c90f02c2000011030718031403e00c4032000a0004419490816016111484000003243c10405084c00c16041003203410418801c0001c0d456008903080a110600341c04a18000960000300f5103160004602070325901c0705682d012641c800103412640d03071081c200b1142024800074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 646920089 1250 646918839 646918889
    0x2060d0c0219231c05040f0503070b0d0c261e090604031101020d02210f07050a0e2106070f0212180103021e04081b01020d210e07 57
    0xd40c0c0902540564514074100f03200494503000c1d03900c1c3c440d04031800381c02d5028a100c4200000310000c400a04045002c04c400c3c2452840074015120450280050504050000446000b88021040d440ea100c43d18008658020107114800c0a25000042e0440c04460546020f00505807a4440c135219980d07000320000c0040b425840c011444117014200030344032514120303103440710440c0c44849954204852003500300644000c140c4105006250840c07010040307540d1410000080c000c03020900d13401d003004002a4000704440f40f0114608180030000f000c403002c90f0070003004043e03c0021031314145a444600c03100050451041206580e4040c2c1a0f50b0424200e841d041d4161000007500401e00c0340000550181d00742440c5032906160040c104400800d03c80034000c0410300500c0d01c1c04001038180300e01001404039008514041c03829982d5201d0b1400000d56940a10610500b00048183c540700141490490b4a040f403203410801e1081503250003681e501d923012071081d40402d031203600803c4a00441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 646921339 1250 646920089 646920133
    0x50c09033c0a020120150103060b0904080d110d020708070605010f14040906020d050c040806010b1e0703110d02010c02010e06040c060516050115030b060904020901050f040902060d0c02 81
    0x60806000c1c110840c2d40150350020340040c2240c040340c011004400600790810145286c00f900c0f18041003294950f041007000c88264158031405060785a04000120f0600803c840c22855050000102030004d445a00b281c0c0c0039044c0c4c0001490300000d045402d02c030408000d001040d02849080120383d995043c0d008038641c1034400d070103100c0c101510070729151405910215420340a203001614150b60592400c0840b403044810326844c0313202040030b0081407002c000281c050b00303600c50490724098010f46016580b00344003001c10480c900006041c01011f1203032803408040d44a01040700c0e002d48266038040d000e03010340c02c1d00d600198a8000d425001407000601a4010f581108981074120301f4200300300e07000d034032009080c0c0c105030449814400081091158190a00b82001d00b0038904d4154a0049c89003540900070a00c070b000840c00b0f00004d81d41d0005401c0c1120780c22221044115003540106018040c0c00d18060341c08000425007801e00140e603007002c0b101d0651a03090340c0c00307020079801c800611b0309 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 646922589 1250 646921339 646921453
    0x2307050307060507030513031424040809010e2d040501030b0408070203070b030f0106030606020a02030c190315050603010c050c060a050402010e040f140a0618050c0903 74
    0x30080301e0400c40a030280d40108159402807030810715001d4041c40d814464401a07008450390f46580d200c8208800c3d0501c00c00d5545109807000703c0105c000081881204500a40041e14915000510260a80c010307840c4109865016184600ea001c185c2c65400721000100313001d00d5041c02036606580d20785800d1040c039041c6c1e54000181a900c0e241c41d00ca40d4069042448100e070503128055010804208581c091485001d103c0744139401ca604002005003994840c0c1d1004003550300200072500103982c0411000d0000100340d640120228403086160307044d62182e80080e0800b03042841028203584144c020320b02c650f9040e03009100310035000c001114248900082c2c4e07922900424042100c1206640002d03030401d00502d05050084000000a0112800540300201e103507a190304207107036a00c02841c4903a00603100c43d000c104040ca05070144014003449402340100b1517035100025500d502e0710081da44550b1020702100c520700d11941000c413040c1c24250300d10752660003020a00700e90583c20112008401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 646923839 1250 646922589 646922593
    0x10507060906021605161a03041209180209031506130e011b05310315020708121b040518091c02010c0806060708120a06050d23070503 59
    0x85898a51200401c0d01c80d404494107602001103407400001c0e0100000054059006450004039011500341c1c0001646e000d000c0300d602c40b09403c1e0780a5a96025030f68403507008002c0e2010003070004002c5444a9a50304803400716001c182505c1200d01483d4040c107842d03001a011100d581100041c0b03484000c0040301c01c0d6a100380e40b22a10240075419070015000300092030b0020900030306122583c0c580c0c0e003040203680c00040c8003141c8003035801002d0720010001d05121018400440b14646002d0908145010103010101e201c039901c001d44815604403008150020b28464036441840060640000142e5024281d403072141451540766116030222007c9980050820031018100103c0f0801d10200508518940c02005109851812a20441c000c0c0300816800000e1402e00d03407d0140519a010301000e00840d07080c440d13000001c414904856805e00044403182035540c1c0e910840002d8003c6400194015683c98044001c121546060101ca0300403d100c0d0320510380d10002055540c135040c41246d41c1a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 646925089 1250 646923839 646923847
    0x3050715050108100501210f08040f030f02130c12020702180a020a0207150f0c05012d0606020616030e031c05180c0a050f0f1509091e0412171003031d0105 68
    0x44c1c0b240d55640350540702e49d05031410681c1d50b91900c0d494814940c0151034003420707000d03480110300d80080464500e003e0884100950741d000c80c1c0045c42119000c2d0704503259980000c4103030a56840c000405c840240c40490743d031440c0b42200c030a1020717400c41240d450240c8222040030840c440c0c0748021070744d4281e0540d9041400d03800d0030f4046524800005043d2295580c1c1c07600d4024600d01d0520581e0002903440c3c5c04600e1792040c4140e21704690f00c80c0c2c00042150000e4060101c0074802407400c0d10061000c2c0342c00328074950384d503014a040d8455905001d5114080c1c0c60600041c07003840e000184240f00000b011044d0101d81c18500d07448100350005181e01074450038080c8054034056810032502e01000d002124048000343c041141c003441c503450881d040c4800f01e82c004240c0341500c0717100e41c40040d40740c8842000c2d0a00c0014002e400300900010003214091201d2000c03107201c0c1320f84401442c048001000a400d0a540d502c46544560100351300083c56001803200136404400e0b00c402c0f018040c0d448510b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 646926339 1250 646925089 646925093
    0x40b210c03040f03140c0f10060e010510091508010f0e010303021509010e030721090e011a07120f0e01020d050a0c020a0e04080d0f050f01030305071505010810050121 73
    0x10302815520b0443c01c5c0034504409584982d03940703010746008580f40c0000e00c90310245070070f500d2415000c4048444401d04260044c048420ba80491a0450b02c0684080411802d0070006039420804c0707410946110403c48060004150b2206407a4100c0e1042448440361076181e0140380410802404040c0240c2d12180942c107080f81403188861344589040f00016041292054950542d8840d4100f5610840a011001a00d01c0c25030a00382c00f050060a288a4540c80c0c280840c1c40034105106000c1005604603c0340f26246514049030035141e40400091603007404584060020014070400c10005400303d040502c05500025181103500c00545406080c0b0b056000101d8800c0b0321004100c1c0c0140a6010025840c6005451640181d11400384140c5415035042c045040362815512100c065080c80d0900c50b04c40854403e050540c0d4241c50030650750700b2507080c1040030500000c452180785160100025810001080100601601400034030090f40d980080740901440c03070f48150200348505000f480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 646927589 1250 646926339 646926353
    0x1a120606270d02121f0504030c0215041a070b0601182903010902030f070201090314180d030206011d090606010c03090e090610080d020c09090c0402040b210c0304 71
    0x1100c00c0042c00409070b040c040e40800c071400c8040503040303601d9101d07010f02181070f450516604110085100104054a801c0d1402010b4a06009000c0d004203480c404042901507070404640c00380900404072000e0301c8180440f6225035020b010b0680c0c0f07402c1040c003ca585907124181d2460786810414580c411139003815500003031610101144074000442e10007001101102b6809540200100e00c030050300da1501c03560084001070002d04d01e60031a45041910400a83c0003000740001c0d94504505a40300d851034880e20200c00c4190400907441110456400105a40090801d050341c0e180590442002c140401c44500614141c841010079000300c80003581c075501c104903401383e9034000c1c50100c0c101603542c1d17410082c103170041e41c0c0e05196030859000c0220034080300368980c005040800051081c000b041000a4507854907181d418441c030003200c0030075010b844c00c2003511443c0100034400c550b12559180401ea84c1c0e4080030703010f201c000e111440d1803441c20550006520400000d0b50031403850791190b480030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 646928839 1250 646927589 646927657
    0x20304020f04020a0c1e02090c13180914010903270506030714040f0503070b0406121a060d1a09040b0406090503070605011202040525030e071a120606 66
    0xe402c00005c40c41680c003240c0082c0c41d03c104001410076004000e55240188940440e0081c000950030808200700d17502d191039190003d00302c903031102501034113010310342c00c98024090380040603168407900c020041c81131106500200700c0c01c2c843d44032801c40c0c5010140310100030302e601255840c024030b0a0010000c500b440401594800664a0310743c0c28030101001641d5960829085400400090803041c041800c04002010151050740c0c401c900740b130704d02400245400343e00d64000c000140c440036000100300744401c54504a80c4000c14a54070349541d042824010000444101032100780072290740038900305669030b90300594000303202000a40c3c407600ea000107480b804a040b241e51104101348070102e0890311886021701294450380d039280010b801000203540300600f80b03a1041c0102c1d141000c403250100c0416800046508011465507031904545080c0303c1e140c0d00a02c8094440d0702d070041d9081200d0000c10440b50b1102200c40c2903103824040c02854021403201e603241d01c510b501c060421800600e004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 646930089 1250 646928839 646928857
    0x14010609060f260903070c0605070b04060902010c050111091509010219030c020a180e011415030f0f01020301231e03030c0f010f0e0a0c0510170c040612020304020f0402 74
    0x40d203200c2d80085107040f404100b1100d42d9501d410108015080140e0301c20454018580b619049081c40465281c6040020001d08014102556601403c00f164003842402030100d4004000f0414194480720b994180d0b4440c000007445080402105010000c43c9001e840503507006038000e00da440e0f50006031480401412a06809004607070f03040c00c0c0160703620115140a400002c44908a81c18143d1a5005452404068041036410040c04502d841a803d41c003a45c0405201014a23a2910703c0010a050046540710003e06000b02510314541c8441500254100c40811a01115004405141000c5060010801580000d101311240f00d08440c0062000090f40000e0540745040c102102031450001c11103c2001e0a9450721a01244d5900c41d1244030100e60004002e410b012642d9595800312640901034107120700645030b002440c3c1403280d01405095003203007900750000e04210a0041d2681c20501c174007400500540703601c681496990003902c0c00740c0c1e4003804a04112042804010284d003141d541 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 646931339 1250 646930089 646930127
    0x61e09090f19120503190e0706201203071b050105061507030203040e0a061502071a0a02070e0c040f030b040b011a0a031a0612190e0a0b1e0a14010609060f 68
    0x482006c0c403215100716511281090000d040c031034501000640300301401c0781117000c401c038a40030790050290007107161117461440858080c2d4951360004180d0b10682c6c4914413011042103450514100201580014000e900484403400043e80c0444c1580c118490248020016041408100b0a0780324030284242c201e40f4034800450070759144e003038142c8803640160f01000140d2129008004200ca00035244a50907401c8480c5072070b01688080c0070b5520308540c49a00c080b1400c203400200314012441c203441c0500300a040340742240d0b0b500c1c00d014980c4241540c0a8544450200001544011182400e0044070b10003031a02e041104240d400d40007403444908208021510303d020703240c9961540006c2c602201130001d048041c2c246003075541000070088043d81c10182c90039403441c4030100001200d10744e440c0d00c1722100c0d916540d1281401c82c5000e00190b0004800b080200b4444a403a8a03000550500104800f240880eaa03805046800180c03610407400810036004464035200d1040c9104080094070f910 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 646932589 1250 646931339 646931371
    0x9120806032a010929030402120d05070b07030209150c0703050d1d0d0320190602220b0d090606050901080a0512070209061e09090f19120503 62
    0xd000220009005034071100812800d4220803250b030404d00319805840c00d80304510320780c0210850391110864180350b00c0401d050101c001800c41d610078201081038580c8800356420b030011084042c056400102084619540001c00030781c10303602c244240c0e0700400006240002d40a44000c4415080e4400612103031103015040c40440440c03010004541032443c01d60303801898803540031541448041101401d442009800b041e5400300c2e620001504e40540d8110203080035840100b01c480c0382801a1034540e60f10100c0c42d00580a00c043ca9014210800c1c1c005000700003409000e014146403e180d00403844802c200b80041e0600300a19404004258840e860001e255511000010265442640000015408140000104802071100803241345041d041d003800c01940c1d0340016900325004007203d02aa41d03050005141002880fa03418101001030540c480c103041c040f5026440e03112428031800d69110710030a01c42a4407040c015102c5003500a441c01c0100030900300e00711555171000d0164140b041c4404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 646933839 1250 646932589 646932613
    0x60103021302190206071b050d2001050a0c03061508010b091c110118081f110304031d0d020f060a03060f09050412050c0c0d02040f0608011e0912080603 67
    0x15058004140300c3c1e400911032840d1500000304041460b51a01e4004110200e141c00000c0002031094000603279410b25111060360885241e0381d4598401504040b50300381801c0c00708400c031690000780b414030701707540c10b000858403041c0c100c030800c1607800130070b000405500c01044564000400740c1040d610091045034400c2d40c5c039012200c84000000140c1e032408240c00c4614040d1b13080403655035050030841803043c410340f501c4600b5407074508008440303d01291003c601902804640e201e1802d83e01c0e84540b030b82e280d080c90704000b04800c10b049150030382406244844685031030500d003038814141d802480302d01048411428405c864101500d8281032544901c00030401604c203036204005000310590000380d900e807508108000d03d06c2f44000d101400010409038214070b8000c19050f041d64810303030782101070701c040c0e2010a00510740d100340c010800f441d050000c5031410064101000d000350030382c0310500e540720030b5508408803a50101c00034801d0326a031700d13207510450143c2081381d8801c40c01170644413840306003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 646935089 1250 646933839 646933867
    0xc0206130303030f180c150c12030917040f05061803340f03031805060a0c03091a040e0709090504032c031b0307090c0c050d0809060103021302 63
    0xd07002140800d0b01c50321035405001c81c40c440c01030b030f504c2c0100e40d42c080302a03d5211503803070b0803540c0901d1400c0d00c01506080042402800041d21b44d680c8000c2040c01d401d0307001401001000b00c0582114940154494815824032242c00d46058801c4005034207819882d080c1008010740c00300415000c0000c0d2545040c0c0155400d000d241408000608000d00103035605801880c1003200320400f00f020b6907000400c2c01004422280d1600741c030b50500740712669103d00700e1170003070320400d0341e2006601c148001a80020664006060712030790f403194441f4401240c80f5001100f1034400d008010581034801c1c00f040005e10640074403282c0001a0b810f110011645070080a82940e100316010f9001c100e0912540c502c0c418020343e856000081d0000380001e00b1035813800241c40d684e4144260300f0401303000e5080c001d5a501070240000801d8135030740401110f03c200038003600030240c559050322540070b9400700c0c44903280a464620310510003070000d411241e0842e800c000f0b19076a0740460071540d6034280b001c0301940c098 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 646936339 1250 646935089 646935127
    0xd020d050d05070c0e0910050604021909170105060603150d0501060906051509010f031d0313060f022b09050613091b1e0509100f02010501061d010c0206 67
    0x10b9a03403955a81040c00c050036044080d41c0a10802ca5484080200844012451803040302840f41c021400b03440340d50018020780034442d641429005202c900d10b01440c0c224500204848604418004484002c00118201c60084070f259400c40d00c1040060071a1b01803980707103142e200004044403010303000d6031207560845e003094104240181e6200350903c594682510307892841c1449039000ca1602d03601c040000c2100c548504800309040d1601c040345456110381d4044580c001201c011252034180503070a0004407240d0784103c8000c80c0ca940514941940b0114a941c00f200c4000031b000001e242510641c1e1460204c002000c040001550b0045483e5580303400405400c010004034241190400340c0709000c982c8100181641005a41d0303503116980d801c6903403d00404041011541814501001900c05200c1c1c000010b6100314044001010707290040200d07103085149500030807840e0b0300c8000c240c40042c1c821a240041078020150740200b0361081c00c003003401c140701601d6103041001d605400051000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 646937589 1250 646936339 646936363
    0x308030f010f0902031603090203070801020d021309050105061606110a0e100216030b060a0b0304050607030606090f0b031503070807030501230f131a06010f08150d020d05 75
    0xe08240104100401804400003400f40d1002c114a542400400b544441d04208181814580c50343e1560045d50b9090103040c3c02401c1c0300d4003c1d5076a00071004100300035400051034030b0405000c1140850f00b0380441c411641030344d4014041c02d217402803188800341a070100170000c403240f580b03d104040c0001c43c03c10260402c040951260380c1c604915608200014030060300b510111341c00741e4024944840a00700c4101100d4001103c003042c1d488120203e015514107400c5100b2101c030000c1400100140006e40710b100d41c1e030341d0307804000103074984600325410000391040c904011440305007801440380000045411041c5600b04024160308040482d041406690050309290064241042403100030301603603011900702885a0340d502c0c08108110351441d0050180d080b096030000c001488503131f160403030351501a0416200f2601c1c00b1580010f10a001007207505e40c0c00900c01d942140c10f0300b4000c8518a004016010740b01940c041d406042c80102492a41d09907800303c514001c41000c00c0042c8403100e0559 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 646938839 1250 646937589 646937611
    0x30c0901120e161d07080604020f12130b151e0f18090106050a0f0618031a04110103090b0403140f071101080c131a0403080c0106050111010b0a03020609030106030803 73
    0xc0d04d07103103450b92034075110380c0c1e0300f14010045400c0051196000d85550b500003c00c071001602c680f004020301441c3e0003500c0800394981000002c0c040c1903181603400a0207144180281c49040e40c03130320000c042140320310711983d801405429007064144c4101400f00c090140c080c0040b402d1803400307000600360040701003000002040030420303c152100203004540c0134003410741c1d1005a491602d500904102100e2160004205890381e00e1344c5102e14031180b5400850700925118112800b6035003010302d4403002d940803905241505a0040a540240100225580c01c01c61040003640c542c0ca040c0c504440c0d291104009100812000b61074815003005040854040c0b60045003c48032840058604034014009106023401803107103040d10382d8000c19110903550200c1c010203184809a484400d54000c80c0c10040960102103515080d0a90551080085810903699a022415000750550803150385182003904203440082c00d00c05424814000e06940e6006130000580a0340da454042860300140c0b1084081c1d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 646940089 1250 646938839 646938883
    0x30d11490305010518040f030e0907020d0e01030915090302030c0a0b01050f030a05030304150b130b180105030a0303020f070807141002031e04030306090f02120a02030c0901120e 78
    0x24507414851980940010b60381d90980d544842a20394180d00000c000420012486100e03800301032007854640020b41c0d025204007210304040d20003a403581740c421042c000082d200010070801f50720038020b4581036170704a521003069141c64044a00640341d00c0c1030030b60941c070041148940138842040407081d598090b01c43c1c800e5550410302080001504442800e1207a0720000059011540200889810660042200c848004803810f124080c11070310403140d62141042d55202e2404072550050306180b003007201d1805a115920013504022030080c09400c1d0164401d04084c0c0010780241c0c010030150ba800c580180c100801c41e656038a040e1720400080b62116601050300c03500000401a15402c1c60042d80c0641c10341c680319000300c810541d610f21201207403102d000400c0134140650300c01800f421410400f8000045103990bc10302a50200e0180c0c808130080000040031058a4400d990295440c041254500b4000c90011503140c584130302120502c50f84c49800001c03440381000303103042500450798034201c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 646941339 1250 646940089 646940233
    0x180822060c11040603023303010b0304060513050c15070f14070b03040201050930010e0f0a080d091a0108010902010e04020a1e0c061505030d11 63
    0x2e49030b0500c20540601d003004401e1005a1b201190080301c03003c1c8015030414540304002450b42c464010090100081d40000003050070000c003001144103a001d00028042a207a104074009981d24100024003143c120306c0605c40d0500e081000030303401e40104114241401116150499100d201010890307103424540b9010007002c800340b0404008182100c805800c5141c07039000602140f14450400d0710507646c408401c09100183c15260f400d40780c54401083e01318130924006802000707141c0c2e0700d1200348149225071540907800242d142d8425403000700740d410030500c01c0c0840043c05071103404440440201c80869040c071120101c0c07500038140f0304004100e6031901d0001500e46042304017400e000c0c0d80100400c007035050f040b01e00c00e481e542d030b001c0d050503c100700c01074110703000444280018501410b00b003990800c0c1c180c032840c0700d056441c00ca00303807440002c280b501955404901d164200c00ea410154124040741c08140c0342c000317101c5010343c00504500b801080c80c50f04049004d403451290202c400214a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 646942446 1107 646941339 646941353
    0x50f0c0405060901052217190b27010501062303071223090f060f01120302070f030818030f0712060b0d0b0a0c03180822060c 55
    0x24520100580b1a45086c100d40300f0030248003500001c0041d40d00700807034500d802c010b01c0c1c0d9251244d00d4255540312940c031401070080503940b1928545030841000b084841009640d45000000d0079810204080d1000b81c01c0e00348644820088001c081b08100120116504850301d4100502400382d100c1905010784850240c6080c1404603a0340d000a4510308100c0a0141103030a00303644414451510503903448104441c090392032650f80e801013285006140c0552200e038003d1040d03a16081d240c044609045850390310890342c61f000040d83d07698116903514003c4007010114007514030304c2c21b680b03000d40d900c4206010711311f20202114440f50401c40503034424110854042c01d0790151301854184214aa00c2c11504c1a002508014900305954801d119503c2d0034a819820100755144035220003405820908840007202d92030b8054078403150380802401d0043c815070b5075001c0c21545603c2c00c0340b = true := by decide +kernel

theorem cover : BRFrame.Cov 646762589 646942446 := by
  have h0 := BRFrame.cov_init 646762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 646762589 ≤ n) (h2 : n < 646942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
