-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5525
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:09:03.505986+00:00
-- url     : https://prove2.me/submissions/06fdce9d-f434-4ac8-b505-c9c92479569c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 993525179 ≤ n < 993705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 993526429 1250 993525179 993525209
    0x6061605070e0f0702071a0c030904050a05070e040e0613020d050f0703030f0203030f04060b0112051f1a0706051b0c101a060d11040e0411011403090a020910 69
    0x4102601141d082e603e00310301d41c040e03030001070b401400005d014080c0c8064500000c45002c0100394540c0300c0c0d02c00a07000b44140801d01201c2e41c6a1258011180512260340020a1510300420000c00c039503000c41030180305504251240c6e0107210041101a0864004094003500d01c0450001c01c41035448201d0041c11803142145030b6951003004201d2000785c92183c0d44850700318000900480e524042a241c1208910150010800040e0b0356407200300f114a060502010181800d004001140e004491a04a602ca1400c14125008850130460087c4c6025000002e00d52000101d0710201d02400c80d00400143e6124040744103500241c7d4180081d0640309005660341d45250840e80c1c40301501021821058202940090134240d80b030b0b11040704200103080c01c1d081144000d501d60240282395000000345004004c0414a1500101c10a01c00c5000b4203007035607295a004001400040f102c01c107209a56000e00a0050700040881d9000c501d075011110b42d03d994a84c035000c03003c48615640f144400c014004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 993527679 1250 993526429 993526439
    0x2c01031b0302032d0601180b0f040f050a0303020a030c020d0c32031906112101091a04090c18060503010b0a03020120030d1a13140606160507 62
    0x60011881180c81c000c4610b003a03000c2a10440d040e08070021801d0079a00300000055044d40304003c8080c10101f4008141d8040e0781e1000e500380703150701c4248030114001c400074060220311074860085000b0041611a8547c0314516203000b92900d005070b00003020801841c00d070380195965069080e40d400e8001c0a240340c100e42e01c0702c41c8014a0070065854038691030280a4012054a03140b00c140c040a010300500f052a6243d529414400c1503d6000c5590715552000d07420740c000184054005140c05504600c00988a61035246204005034804003925080c4968042c00c10a4040050b011041c199401f140084081c0b07000328400c1c06a40001e09000c04072001e8440100182d040307a81152000e034001c1020400c0c02d400e2110f621940e0001901003181601151071030358603102456065030307620080d20f0030120076001000a842d104030a541c511106024940c220b89441c01010030f60602c81c00c410000552841e840e41020714008000d40d20901d00403564803510714132444442001d0346d110707042e00d254540f11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 993528929 1250 993527679 993527681
    0x1060905040b1008071511010504050a02120309030a12053903090f0907140d09060f09031d030304090501080f011d0c1e090a0e06072c01031b03 63
    0x4031030980d44900980c02203401d52043d25080d000f80d8011a01418089007000b04a6100796072601c821000c010143c490868508000c3c0b1540b40514440c0e4080c4c0100c92080c01000324130801c5209090380340c0c00410103c2060780d00040d51200f800e9005281c811241c10180703041c0c0d25409240d40040c070003a092641021000c3c02a4900440d1a88010b00c41290b07604032074402d43d0301d00400900c56002030b080c010740c884610b8a03070041035102c4028984182e80481908420000d03400c220341d8010013644859102c030401034a4056903004407510750f0200000319554400a144114544010032080170541d80c5a001e61002c2c811200076080f00e40d41800035580d6410456903808024030003002c0c5500c0c02003d047e00a050b50419111a4064030003444020500c0042008640300600c0f85020307540311888013006522140c204901c00c0c0303280d0070001159151110040e0908600500080420000c4000d4001c808100c030b050781d10750b1085944026200c0c0102005900401c0c500d880400c000d0454003003403c0b10303541 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 993530179 1250 993528929 993528931
    0x50709031e080306090c070c080a0303051303050d0c02010e0f070906090c08150f04050c09040605150403110307080109050f010c03180b06030c10020c090c03040512130801060905 78
    0x108141c0c1442a111900300c080281d045194000d0080d03000300045540d900d01100440d03081003e0040043c5400300554621100c80c040f940000c50f503410030208001455017500c62250f00203c12403462036a01440c2da8010a5480b80320340501074190341e01c180d0f803809171007540902e07507204040d412105c000f0445410196a421603106428225081403c04654080e05001e034041d46106034a42c8070482c1c81d000c01c3c1407440001c1c40202d54101d601004811910b90740d9015150240403064015a5101410020312080c0e42040d00070320302401c090010040c058180104a8044035002885030320b100508500107410702c045a40070b11500e60910450009026011401c0b011015902008000441b40e070482a8103550100d000b042c5070380ca04080043c0410a410011680644014251000003c0f241c1c001b50100c010b03001c40720016808400f5210103400e20700402a00021035030b804d282035290680d0f4550783c038051007414417089040841d078441e2030284508218050282000280032540c4c0310180c200007484 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 993531429 1250 993530179 993530183
    0x10b09120715052a030405010f020a0501020d060311010e0f010315030b040311060f0c07060f0f0f05180a051b0307090501060509010306120c03080906090a08011a0303031005091905070903 82
    0x400241c800d209481c1c55100d08030705586a0085e605107850030f401590111b100254410039401422400400030380c0070701c010040b0070701043d00000e0340c5040d410001c0054074121801818441c10055446065030b6101d41c80815450900c0c021030b00b07810901c13103880000d2165000070a64008101840205904a44c035000d46081050880e030070781e601c80901c40a100e500351540901c6100411414010810f030360042a0040e2800001180320542e4140c1041150082c0300b458003019030b503100780b05203050504407401c4805c41160042800918035210691560048484840c04503842a0409203d4030203010020080c51429420000d969564001174600d43c440912180040e2400d240400d107065404406040517400c103501040480c01c42d40e6058541d4800e00110703901510030b01100c0c0d070039a02d020b800c002610200d40089140c1c005a25840881003d410445120b81c10078010490b5801001c00360340211038003228480c0c2e580d00e808000500081d2580140d000541c240310800c11403e41140c00041228 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 993532679 1250 993531429 993531457
    0x30e03093f0d0e09040c030f11060d0c080109110d1a030a1b154e0f060b19030f0e0f06090d1205041e05060f0a05010b0912071505 57
    0x5550b18100500b101c005c0358020b08014a0400500101c0d45031a10f009520744144134801c4c0c903140580000d49035800a5030041c0300c00e45c441050000f0640d101d413400c2d005002c40d581c03c1c42000b8441803d50628020600401d007030550729070640040581d4401e84030000c2c0c3c0b020b8107550400741705042c000440000d19050f642c030f81c9400301c0300040c000031600c0e0078014141c1e26034900c06480d104801036000036441500c205010a10b088040202c2c00070724161a500b94000654049110200848581030f43e40c400110b02003a49030400420070500b461040b1040c5c0c00c010501e0f90500d00e00028150300804c0c0e0000400d609034030b0050034500704030001339503c800d0b411100031180103940340c03c00c1c3d079a9104c00760301180c0052070131103802064111941059800a104140d2803440040124120a0f140203086050740c0707580c081d005010307e00d481c00e2003240c1c000c2958a418006581466241c041070710500e5801402000c0e03039000441c40322028000000074003c400d011080700b5449100040150300502e41402c048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 993533929 1250 993532679 993532697
    0xd0807230409020f180a051503090705120706090e09120706090b0a020a0314043206160f0e220914030306030c0d110d03050c1c030e03093f0d 62
    0xe20300b4005000c1183d600600c0c0d0342c0c2d060400d41c03980c823160b00042c2c0b60076550b110f0b0301c40209030303681c1c0c1031900e071041130015008010943ca07015000701104915840790700141c3c411030501041c40d1012410b1110300700301504181d6180b2031403401d140103160a40f00078050a00010134044601d1540d0000e0401c1e0072580d4041c0640b036100b44070801c81250503600100301040465404e880c411505107a00216103000040700404601c5040d49400e04408a8079085c00103011a01e034000709801c0744421011051358900900c0300c000c010040b900340c1c111021003081e110103050f155044a01950014401c9a0344508280604403141415655940003690041e10a0243c22070181490a18100020206401c02c040800220100c01403042030303020240c2c11f4040200c04c2000803405041001250a003111b102c9807825007a49040006085920f45101141703180c00c00c0101100c10741e182000801d0b003034401242d8018021380c108034074030106500c18095011406682610050754004604c5081048081c0c0300e210310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 993535179 1250 993533929 993533977
    0x1401061e0312180b041a093f0705090702030403050a0b1003080a0c050606040e03090d061506021b01050f0910020c03100f050109020a0207030803062b03020d0807230409020f 76
    0x324024105043d070040d04410030038602c202c001e400030710130101c036100c040102d0000c84e0f82c07903601c070f01000720080185d48075427130400c800d0400412850f40300c0d18501c0650b04160455690301d40300c0c90790241c081c20800700368001c00e40801d00034040130011507100b546259520901c0308081c1104038809006d031114001c400005a0170b080ca40110288405000b014524040d0007104201044184140642d038007a62a031910310b0030103456924001400380341d002042e12030b58480340340940e40b002034000750400205009a840690f006401d48003000400c1300d00686c2ca170341d1144102e01c0c014400c0b01d00c5a040c4555199051001095400aa0030545c0b103038090005a8880518070207a1080c003c00340d0041c0d0100c1c008001180b070120145801c09402003103298865401c0000110300144a520090341c0040404960304040d01000b44042201c05418420078a20701107401800400304c503072030f0401c2c08030700100c5c21215030300d0031089502600c04c3c0325046481301840440911641c000ca01c56924120800201f50030b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 993536429 1250 993535179 993535229
    0x623070c060e0c0a0603091e0c0911070b06040c12051602010b06042103050d050a0b0301140103030e100c0b0a050601090801050402090a0209030f07031401061e0312180b04 75
    0x8007400004e406104440d1070300303d04900801c108038058a45140046000312690400c1000d160a54011071011003e5030a146503034045170703070340780821490540412400e40000c0710089250f0348150103d800081c03509105805951004040d000b900d5450320348030400c000141c954034107819004095008018a800910a12440f071141e80100c2e910041c0c1140039060160440d40d02c00e0f0300310306c2845c01ca41050342540000341a1803080e1010004c282d00c1e05806150780c02c00b44240000741c00c1d400c110360019491600d000e00741c1201c00c0c901c0c0d4010003150401142c0b03d8062003017004002d601c000c0d50441c9103800780f4824003e0000b51413080c00244e11080010350380b8014001c56008035001440c8413800d0701c0b0401004001c1d400034034002e806015013954a040c680b0284020030046d4060540414a4644070304002d00315182030f0002e4a02203050815240d02801040c182019a0b40c01445a0050746407101e0a0355508002001c20704002f901c07240c0801d107803076114090421242d0520340003000c8030304801000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 993537679 1250 993536429 993536443
    0x3010905062e090c1101150302130203060a0b030a110403050c03070e010303120203061210050f0606120408090415060908070902030123061c1e14040623070c060e 71
    0x141101c110b401040c042030156520004529003d414030307010844403000e0300f03400e6400090000e041001303100703070030015414010201000c030000380780c0452562920800240c610043c1e40600b100707149010000650100300b65002c6541103803801b00440d02c5594928100342e50700405c61105001b07009265000030740d443d030f216109059a5058452002c040e64109100c0000e4000405407a803040b14035a000501060500020040305814003010566113000c42d005a10011b0260006005140820441040301c0311032502d6504190301413020303607590405100240140083c2c14800640c00711758940001c2d19500084500120346454096070500341d0307164854000c0b07002c01d100d104000000c4201c510041d6030380303084490700403100804242c2048030031501c2c0c04000803140d0306104a0f0b41d440b010305141080342c45103d0243c0304110b02c1400380700d441301c20805010202800080840740c643d0240d01080b14003200c8644420005035070ba07043ca16042400510104000900741c89140c90f1a9250588000102c0d290b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 993538929 1250 993537679 993537751
    0x1081002270a0e0c090306070905010f0c06060f0f061e0e09100806010b0711030d0e130b0d060f0b1503160504120503040e0f01060915020a020301090506 67
    0x20240110540220450075040325410300e81c480041d1a02103162504401094028046404019120482070042c149070000c0500f14805020705610100070a80c5e106001034550310f402d16100e842802d007440c08034090f141d2038100b100054001400466003580c00145001280d07590f0752520343c10010102280044504071510358001032904860700118241000308581245840c1a4205c100e551804820b051440c20f81011040e0303c00000c840c000c0c400c1d030f02800200e88904802400c604004101d0280101c0c1240c0740392400348581c43c1460040d0307000f0b6800000210b90141c030344545d1034000e1034804010100d00300180f20803490001865001d08040081c05040c10b085c1c401c0a03e540c451001c44c1e00c0c05141c05000c14104a001c01c804a8039131340c00400c158485118400550f1554100a41002c030054010003600404072001f00412a484c7e005008000300c9041e42003a2450b40702c3c481d0104d0030800c41c040041d400d582041100801c005001070560700c01c5031102d401c040c810200072041d0443c5240b00d110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 993540179 1250 993538929 993538957
    0xc0902091309020d060501030507080d03111207111c090e0f0117071a190810141206040312110a020616020a0c0806040c0b07022116090501081002 64
    0x12a01401d0142c2c000781016000620148404846545110688200740c104407101e07006448104800740c0d042003151000c28241c10240040103607003140f0002805854441d481c0055031a0201d01224091451072a172030000d40c0a5074410354000691030903210450b1011800142c006c2800141e400100c64020f0150718520400d19103646407011503103410b4072115460f201c5009806000031200c113107091072400c0c2e60b5090492501c942c054012950140c40b5800d120090005180810150403104030201094a81d0a680c408100b40301501251601c040b01c49104200d10541c0c051106140d000286260300001200c020302c221810084041d03501d008404840b405a031140c0042041007989102d0324142500b144119400d14500c1e0f12840c1054000364081c0380f8175008001030005000103025294054407500130018030388607080d8042104030440846021005d144a0894803041e00d0500c480110100d00c1d80688115949404214001740428860110b440c40384141144440307a150098640d81610624 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 993541429 1250 993540179 993540199
    0x11130e0d03023123030d0302030f040b0a09080408010e0f0c1003050a020706020316080106142d0324090106082a0a050a27090c050d180c090209 63
    0x8500240c3c050f4500010250894041c40800c800e03180501c2e01d2650000008813490b00d15946041c03609211000c42c2102c00c1600420030044d166a2219a5030380140d4408501001680c60f1444000203100480d4000c0c010b130000200019007407015002440c0d144c6200e8107880c10001000c0c8400c0c0d80c1c1c0400f00e040ea40281d084500c0c41c107918025070009601c0f01c20340c60003503d04801c0703940300c100726441110040e0b203500c480540c4003c6140c0c440e586602420060810f07002c06194044007140f54000ca8040e04540015000d00c0c0c001c2a02e048102144034801500c807031307182c0c14100400c030200b4420f401070541700804550030780502c2c50b002c10014106c0381540c07a1000991659041955255514421400d0503050380396451440c01c48000202002c80c0290740304c41d00c3c1c1002c10310003001011121801c000301e003003010b2a851003455007005c00e001c40e0543c6800207407401414405680e85e00070541d541490a00c0c051061981002c40c9c2180048984102d0301c1546c03da13222004507040b070150703841550700308103415 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 993542679 1250 993541429 993541477
    0x906031c050a18290703090509060f030d1e05041a0906130e01090b03031c0b010c081b060708070c120c061a130b030c0d11130e0d0302 59
    0x6002c080d04920b0408803043c0804005040711031154003480c1c5a800d152840b8440300718003190910b0442004290a02e04182030300c1c000c260082501800c0e01c41c003209808100b0569540c0005680a0005030594210041903100078080448100004110040c41860005014412000c80d4242c0f00e4000380e140e452120380e14001c180360003107441260842010011080c68844a54509000308189200c0504942c100f583c1c00081c3c5400000c850301039842840070000100c00700f403001e40303083c0070072100041c4980d50000407250042c081710042c1c090100061700612008103002480100300210701100c81c0c0d0b8840220403100b4070000c07918500042c501e224188002060000071881c025840d1405034101c4030302d0b4603210103e030301030716000c0ca048051207840002c0d0b0402c60740411004070f001208000d03600d040008a0744031182184110710403418545200b0400401c40c0d400c0c490548090315805100d440742c4000c2d40100700c8036420f0302c5680310385484031350781a1003402150160701ca5030400005046d014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 993543929 1250 993542679 993542687
    0x1090209010e06061c0519020711040e011e020c06010501090605070312020f0a020c090c1305090a140c0a140901050703030e0c1203041d010f0501050d090c090b0906031c 74
    0x2e0807040d4080d42c100403200e41a44081078150900d00200e0700041d060034580007010801c5012100c1500a42c0180309e014085030680742400d40f20b0710140c03004113910001e1012503004148102c120000082401c008203181001ca50151494508080c21140242d1b00c2d03a0056503410300612901001030b60401c0035100080c0700d5441132144544220025041030320a901c0544290811a100001a230052030a20501e182007502984c10507c610b924914140965070105030491080c0111400350034481c2c042146034049500c140a0b440c90075212404500388091b0340900c580c0548440000660304130b482e01203001e1040c045401800b0140c403001d01e4a0100c0d039040c0d020301384045d101c0a1a0045480b180003944071602c580e807a0040000140d0341c0c03141024400110324180524581c82240b10340c00602c4031001d2080c0e0b44065070000d080c0903440d00b004a1020f801b5103041c003001096415076000001b54425140c201c80c0114908681d8441a9950364081c15600c9901c0040f03000c0d64554100b540c0742c45401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 993545179 1250 993543929 993543931
    0xa0b13050705060d02090a2705010509060d0c08010203150307060908190f0b07110106090501030c050103112104020a060509011e0e1e0a0b0c03070201030c0e090f070f0201090209010e 80
    0x11804c00b5050800c1000017901e2004190302c4010303100000a0021004080000b001008082140c81005503505001c04640d500c0e200401e8180039514182c1c45005200b840a54a0010021800250350780d00d01140110040310b552070b00070b0300902c83c492000c145c56000703891210075150300c10001c0105182c0d4109034010300b2450001520700010070012200460721000b20369110f4031194907080407400c04442c0881c00c42e00300368060203429281c103005100194842c4200400c60302c0910b80442c4060035080c03200040e1240f00c5851081c0d12540c81840340c900100e01e402440341c4c0c000c40303040001995400095034940701c0c0407800c500188070000c0151182c42c0002030701011071780900d071001c007104180022070400c80c0450800b4400b1000c044e044001880c2040740c00000c0c28000c038030981080700d038040490303036401420340c020b05264440030006201c1d03118503880750542400810751001410010b80343d50780d040e001d480c0c040c00521081a030440860050047c40307450b41e406021802541c2c40c0400c644181c0340 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 993546429 1250 993545179 993545197
    0x12d03051207060e0a110f190e0c04050a090906050f070e12100e010e0105130203070605030a021c0c0306050a15030e0f010e0d0f0305010315090212010e0a0b1305070506 74
    0x44d039501e00d0700d50b01a00304100c2c0c41c0c0b24071844040b00714040d15010040203080341800c0c6445401241845802082030100000c04c036400407401041e2038a038100f8194807800795410040d0001d5079201c0c00128500c2c1508801001c600070725080055844186071240300743e00442e944004203200045600150411050343d495205900307080c0c43c03c0103284000e14040c1d8444182100580e91911a40070f40c655081c811542c0043c04014080e2065240b1b5020039162001c43c480d41050002c040001810310400390119112980b000032468034000700401050001d1081c0030003180002d2030300101150758101014401c0c20307143c2a42c90483d055103e0740b000c8026110703102204525014554080c0d0006400740900070710083c0b10005081121400c540061501220b007428404040c1000010404150b606045140d0f1460080c8082409101400411030440f0038900740c00755586090380784000d20202168442456101d003608030826100d20b01d50841c0c0541083c4090300c1500034402c10411480c040c4000c02e1000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 993547679 1250 993546429 993546431
    0xd03030e060a060f08010203010509060d0501140c191107050d0609020d0f150c0f080411030706080a0c030902030d050901121b111b0f031005012d0305120706 69
    0x80802007801e080c0240c8400c0d00e02c40d00d8510600c20243c10a042d40c0140c06008002c600b5503152400040030a440500120300414102d0661800e1103020b4020178100c40450403a611a1705280d4002c06c001e512084d02500c03505203441034110f503980310307150b0b048101801074020404070b402c00c0204103640e002c0d00001c07a417866980c1da0050060700c49009007610b4074050035100841e0003282c107042d207980b1040c00050364039518120034418016002003140d92a80c69500d44005107a42c2e0380340041003420004000750741885801000201d40340c0c4203010a12030a40342a041c00404c1001d10b081d802d4a862540003541038220150a003c0c591188000c1d03d5505014134100c2d0080d01c0c042c0c000c0d0101ca500c8400080d40142c0f00741043e08454000b049403203141c0003400103140500c091600e68030b08624100315a4402d0030840742da00081d507010040b1100d2080c0700d03001008256503030059400d80d480560b141b440d50041c0100d405101c0582c9452860881e42c0010103409000014550b82d2100d62000038221252 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 993548929 1250 993547679 993547691
    0xc0e120c031b09160c080a0c0204020c010b121636050403081509060405070e10031e0e031b010212040b152403060f0409290f060d0303 59
    0x2698108407004208140c400b0300d20000b940101070140e680d4005250810044150010340720341d540c05811070910a0300070030500e44035040008102c2d00320311903542c0654090b002040000c40300f04194040110484100c840c405086d896900d1651030300b11004120800410402c0d040200341003003800310303d105004a41310240ca406604184651030a503c0001401c03d640d0b4042200b0560070944403074226005c0c0b03200c150141048000100300c1c00e0f000700054025a03d4001103001c0382c0c003031001e54207040ba00610751b030402c03c441c400050040404a54102503155016600e000c0d8074a5031162102d07946030341003d145800544d1380d00c40440741d242c0200030155075080021142c2810184401d07401644a0000950581421510030070213103961032000740306940c0c40741890105860504040002948141c40d15165030710440008c070b0395504803194640290521900d2020884440200b0031a004002d420380301000200c0341000781440100d80070b480700f410300008101603160000c2c001d0700652082c5800b18036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 993550179 1250 993548929 993548953
    0x8030d0b030f0d0903110a0f0302060c011418120307080103121845090201120c0801030b0f1b0306130608300d0b152b0c0e12 55
    0x78100444614000003604d56200313004000c103040d946280b4240c221200d18820303040040d42c900102041c44000d1150400181c010310390781c001c0d00200c4202200342c0e403240c1140380030b1204078070b190a80b5080845900904016425a00c403036001c2d80d005d1110395030f40820326807d507598042c0c11040c5003451400d0045c00f080f5040244104140c2801400b2044240401da41045900044100d00600200003200d4880300c4400703218030081e010102036881c44e070003060080c2180016603045000d600c4e415280c0303042140d01d404954121001c18105d07807282807004800c0c1c1c0e6070b00741d80034080380a8544003c5c1c00c240c402034010001000000d140c00c030341c0c0103101958440f01c400303100b011101c2552001030700d82c20038001450040d842400d81000c8074200400050b03240d66070200b0310221702c545601902404e9640141825031b4940d080003102210358068401e42d60010301583d8101a6000390b0700032504010071844211000031401601300314040ca48078540c5130b0b0980c400b0411709030301520416030b040c403c01c891458 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 993551429 1250 993550179 993550183
    0xe010326070803100303030506120d0f0e0a0e0718030b0403080703110c071404090503030f0405070e01061701050a0b07060b0301022502041b1d190e0a051008030d0b030f 74
    0x2c020310200b0350a135881459494040e051b514010b1880348103551500803284502008035011580c0440c0d45046000d40b1a07c0b981502e070b014004601c140c019422000c0801c02d50f044a403000d01800c2582c0350038204d6648500c0415425038903004c0105202c01c42004940024010b9000d15084000340c14041298856106814030359000300b1070310a4030b640207003004c106459115404685940e400e40307081c002400e040c0c0383d15580b440050728015900409100040c14803005000a1010b003010848030703045d44d40c4d5400000e146190002c40c1015099000000180518000b4100c80485520034551410800182c0707500c00100044003181d50103540070050700c042948000c1e20744514401203c0c40040515060060004607020f601e0030080032110361800340203440d000020380002903501d40f80d80001000c00740214124140c401c03a0180b48842c800f00101d40e0340140002a4855100032508022503521410440024041d510418940e90800c1040503840507560300321b0102275030003904031510070b4520403c00e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 993552679 1250 993551429 993551431
    0x3070215040609031d0a141809100605011e031517150f0601090b0d060b0d0b011206140d020d02030d0804030909050f0601030504051c090501090e010326070803 70
    0x1101c0964a445103020503401605d400e44100b41c240d14042c0d545030380c4010804d1103046000320a07500032500e4000019558003c800c070858231404400c00000c0c1840048261350301e00e640d00d500f030f55600b0a4002304555118072201d0030031141e0307000403400350480203409a00402600c202c24020700d6201038045a0b0030489000740c1c1c141d101c2c19000b482e05c0c60794111b0342c40c00c501d000350018000c401c1510601800c1c0e0303800145102070390000f800b40391b0b40388035554541c0c0007000141e2041c044c00c14042a80c072900c0401d40e201d0100390b03000780c070741150702d030780f07081c0384000f00c0b1303c580140f000881c07405150545904010160070403862002d040c1224cc8189500040d00c2c00324100d600c003000800003005c00040645c000b903100010809080103001c1c2c4e08103400c0202030002c00601c0c0904250790358001030203000003008074591001d080b800d00403030078001c0c410050110301c0c01c1c040c40f8003083d21400c0000d80342d0141e12520341200d400029080c40c2101c010b1240350401c0d0004850300814030140040b40100e0442c00080d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 993553929 1250 993552679 993552683
    0x1908041802070611131a0901030506121914060f070503070e1305010303410720270115090f0b0309010510150c0c0f18051003020a0306020307021504 65
    0xd40317424812034504211122904504a500a007a03500b000341ca490f82e0560780900e200b401c000c47c0603603580001c01c0801000e00090099442410b9100b0703403040c500302555200c0350040104d5a12160851071240c2d0b9200281c40c01106610b103440024400d5203d2005948c0085840ca8000d505061500000360507103111a04a8590b90340e410040081507013214000d1410b103c0c0030040110f1980201c440004c90959108a214400380100908181100c0c07808842039154428040c4480c00c0f040b0307100c41803a1440351074490064540c1040107414950704003103e41c04400860016441d6800e00c400a0110756201d015032003445100d00c0701041d20145c0d8a0b152020b0308803004c4080c0c9130702d000c280071400c0d900082c00c0c142c10443c800100348001591348100c001030030a142840fa0b038172805403411030840065070f44a01c01c0d261018401017080c01c0300700303020800c0e03070320760030040c42152100d800355204030400d0f1000a51000d5144010000a10b003500a103501208074016a200250b143c04080e013014001c03102 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 993555179 1250 993553929 993553961
    0x190509120c040e0d050a03150e090a061103061c02041d030d0c08010b0306011115070e01030f050c09101107030c0509100501140c240105010219080418020706 69
    0x31a9402d04003071160603910241c1e03500600015040203c040d01c140f0078103220b502010b440d00748031141a080150b101c002880c260f1211701e00e900c4c000c0301f8036440340c095450480e10a41030070849a8072049110517240102c4e03008228034146c5005407448000d020b610b4004a0700161100750700c0701d485205003040051902582c6c05159103502950316001180e2240b9103500c28040b018005104003901e020940c1d0b071040081c286030711000d4409145501e04421002842d0700c850440c0e041081181e446080802c500e402a2818031007032401c00c038080160307242200c00001c081014400c00a041c42c0148d1003003a10a07882c10a003000f04000139900e804c000c40c42d0402e607894112003004110508107800300d00e85c001c84c25582f02c0c0c00c0a0078200002d104e07244400d01d0361480580840c501944000500880e00f00003100c91004400201c800c0421380e02d150b007403180d02d01502480e00012800000c0d00e4000400b150f01140180c90709007040c0b0300404868075841070342d82c82682884110006140d500c82d955110004441c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 993556429 1250 993555179 993555193
    0x90c0c0c060a0e15070302102c1e0a150b121203010312030b01300501090b1503161b0503160c0f0305100504060902150405040c1419050912 61
    0x140000e0794048046034955004c100180e00100c2d9022420318802844044007161101501d9070030312400c41c1c60303884039514040501c50700741000800144101805400141407210003981c01600b5240c2e110607030068010180382412021102040e4001c03060b004005142d000d400c402d00006500e003016020641807074040020050042c0040c402c2200981003451400f440b58400e03c90009012501103c601400414500e0340514511814680d145110080240400482d80d640941d10050028194100e000c4c01c07070b2804041c00c2101c1481244c0c891940c030f040c400c40116290004403240401102c5910b000a039290380e500015205000030401a000018000c1007841c041c1400b080c5442107501000d0f410103c4582040003c40105181d070360003044141c0050f13035940c0c604004002e0441d1200080d408070740c035100183d113001c4c94000381081c1c0d88103803001c110383c08404405444220604100c0c0f50000c0080c07120364010784d081c21055002d648076140690a058403000803c4003003450701038454040c3c00180c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 993557679 1250 993556429 993556457
    0x14060114030f061c2f10121b05130b0a02030f0d06090c0f08160e0d26040f050f01140702040626011401120314070f0602030a1406090c0c0c060a 63
    0x31342181c0e03402c005c0e104c80108481011001548500d00c00ca06076042c0001c400c0100040c01f9164007602c0e0090a19860a01a03070801c0d0009003960b1020300742d107074030003000c05002c038103503484c0d0041da07075030350181d030029450040310580c409600d0b008895602c0409807030349000b140d4849a4040d443c00b5005c1601ca2074a44146808054103110300102403d200d440d450000c0f0070340c6a4032805050b03522006458001c0030b41010309015900302c0b5a4035030304c1c01004201c8101c1a881c1d003000b000380201d8111001c10000d281e2200c04000518040203042400907440c2081c0b802600d2045c0001c01c000341c070090000540e281d8845050181088103040a05008048101c1441d854000c0c0101d114103020412403500701c0d8180a95074440103031044014081008c4c0103480c80c0008031038400c448810f90003080d200300d140e4141c40c15202a5000312881101c1500301200f40105044a5007010701a19009041c00e0190b92007060768071858118401c441114840c00886201d1a00d83c2801441407500d1640c175070300000407103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 993558929 1250 993557679 993557723
    0x304060e1504020f1e01050a020709060f181e020903150103060203010f0509010b071e1707120e030c01030b0d020d060501060e03061905040804031514060114030f061c 73
    0x105903518040c043c41701581c40102c00295801764405024242503407180b110000803841d054441d00305058a03840c04101041d50210719440c071040b20440614218007910408842081da040d2a02d0400303243c14105041c008409550080c000055018040b140305414040391a00828001c0c3d0041e51819400401802284043e051440140c2000e80c0c00810035490549004454840c402010b420010450a11803544000030510102c00750825055080641001c1c0c00c04001e5200401c12240b611400700c40c24242c500030080d25140e039030010098110300382c0c028015400380c0b000c000a554004807450004006a0300e41080740b1585000d1000001c0c29030400c08003078a05c00da001030340c0e032095001d9002c01c010780500050344000300c0445c02c000715003501c440c44c11907454010f80d000100038640d4175040318115842e0740d100841e04003018140d04200d464490042d15484079002c4a00c82c440020000514540261045550005d00284c8258a45610351061365408260082c080b181303402d2500f0800c0204046d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 993560179 1250 993558929 993558949
    0xe030f0109150b06070803090c01030606170a050702030409060801090b0109060f120201140a020a05150115050f0702030a03111216020f19080a0308010b0a090b0304060e150402 77
    0x11900081001d00c030151550500c440c01029482e0100d610307514020400c1c0c5402003a182115440a5610388a00b0011411a00d80d0085400c09000034070340740b800105e5030310510f40c104903031414002140f903035203e0381d8004000d018024038440c00d600c0300f04000149000607200750b070300901c04980000b503400013601c0c00c1808028107074012410582400014001e000000e188002220030b42445902d1800c014030050b1000410102004140c0030049905468540c010400d00720341e51055080d40c140d0303c820017290403019800e01807601407400d03c10304080d2440c011001804d41121547c82507080826075400030b840c00740031501c101d0001c0d03440022490804001c1041c01d01c00c010002c0e61509201000c04014150703000d910780a40304101d41c5450056503114a2810417881000d1084000301a032a12110f5a03903111030703c002c800045101c400019120309200a8400c91812603135001489494988100b00680001e0000c0e00d04a41e12554003581800030800401314294000341100d5603e4180100010025 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 993561429 1250 993560179 993560203
    0xf04152403051806181903082a090d05010b0303042411100507030f110a110f060103121b030801052704021e04021201090b24070206070506070e03 64
    0x542015800511803001c07448585c0b140d0488011800803046090721481c1014024040c0500820210150700b4580e000d618a4400c28001d08240c416101c11304181c00141180101c0d12a42c22003440301101703900e40007025240607806a030002c20409034810019082da4003581c00440d4100302c06041c12800c00f242c0840a10f11106424802021024421003946076280c00c012006030594800024020b60300981c00791503401c44201080000e40d2102546001e50b5201c0602000482c2d8000c1c6021010b5400294210a00322440064140c1e40d1846d030f6403032020013030803c52109000e002e03c1c54408003200c501c042e283e5580a80d84050065140c5802c0c030902800104252003441c80901032412000c41008480d07800c03541c1034030f05001608064140f44c90079556140d03580c0c0d016000041e0720266410080740d55040c1c4120803000c00a4071000020001c0c0e248210b682c0c00d140e0000d542500214140000c00382c452540007070510351824071a50b54084c03c0203001c48034bd001080c252000010142001c00000d21500303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 993562679 1250 993561429 993561451
    0x40b0909060c0703050417010e07080d0918020f0a08040b010506030105060a080a020412050a1703060a0314100204060c12080907090b130908040314010203060f0415240305 75
    0x410080c06407a140c00009200c03080300d4a0000300c5108052140003114010f014060000210f1604500c045011f80000da030840e41d1417051301d40c081900000803e100c074460000c2c0d114039181504d84070103081d03040c0c81c848100100650a204c01c02c0842e984c1c01c001e00660105940c1c40b90141b80070700e0700300a0982c0607000b440c010b050520050003507440351001c031198086a0b041c8078502e42e640305140030191145400c100c00c02c1031085010805c00c0400281407588a00c00c41c207440000d0007406003c40540012144583d109140074001c20101d007001c00c601100400701d800340c2d0402d114140c50302c42a6401030f8000300c0019100302d032500920036a0316104c100a0306034a0080910b0900f240d400740d503001140541d40b0300fa0b46c0c401100020350340360a4042404100b016051041855070b04015526821030312055030024220700c0b030041c0c0d898062003200c0c07003071100506000901c1c5424081c08018aa2082d0a00380e4408804001c1810f9000c0040c100c070b10101000c00e01440040c1300c0c03000702940c20290440c1421 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 993563929 1250 993562679 993562681
    0xf0906060e01110c0a2606042a050603040c030308060d1211030c121b011e0519050114150304020d0311032b1a0306071b021c02040b09 59
    0x15030311180303201c4110000d2034685020f0703022294103130a2208042e400e50340180d60a03c0002c040c4e4445050b40c118190120000e01e0340700700401e0700c40c0c6486003260700a03c850007118070301e01f460055800c3c0d1181d03c03d041c6014004141c861020850590040c0c0d01138995542c214010402c06a010030720301d9201d80d09485000c1c00c090b241d90340c134074a034210600d60410710a080221840103403003081640e9140304000111002c1c407040f81c2100c0035036407002c40085100d007514245403500c18014000c03449415141684910349000c3c0c01580d000625001e4105c5100c80b00c2052000244001d90007401d000c0c00c0000d851524401c9074204002c03490401d002c4a11650348248104405603842c101c04d4a88142c050620904401c68100c03517905521803403c55001464901404176020790450701000e0070700703565500402164140f0715040e0803941c1c280000c0c035815408400041c0100e803054120205258045402400c4440305500141c0c105840f40009a926081c00c1668002d51800c4e0240f400003803800c1d240030240d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 993565179 1250 993563929 993563939
    0x6060203120c090d05030d0204050103060806010e04060b0a0b0d06050a12020315090a05030a0c03230a0c0303020408011103151c110f0904050303250e0103090521040f0906 75
    0x881d03031009026250042001c5000c080d152100c2d0003040069512005507562507001c20126030081d0810700400f80003e00d0000c0c0401e10600000c2c00714141c0744080d4015105684540e13036a40a40a2081e1450b00829990000910110100c0160030720b107101c4800420407500300030034090303203141c1544140f4490400d03204d001c0250f01c0200300c080815114446c0c1d2540c5070b50300d000541c50000203960041491100140f407207649a0b200d8816141c1900c40e60715641c680021142c0468510020b121000f000c60702009901c0080d4000d0040c10030180c42410090b09041d500c135100d40c00c5450b51084021000400001c10920558106454030301e4802241e0000d121681002070381400d06a40380024014003203021418503e540b002e09042080d08010600390452400340741007030700da40050320f900001941e00c40084603880007018040c41074454076502c03282001003030310046001d4030145005840501032500d421900b4100003142502c0f4484c45074240b035a40745800a0101c3c40044c590101c0251403800f542800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 993566429 1250 993565179 993565207
    0x30c060c040b1204060b06220506090109090c0e060310060210062103090302033a08060607081216110111030c37020d110a032102160606060203 63
    0x285001042c40f4141040e682d0303180c001c000346100400c0c81d600010110f200d03074a14030324002d0740791440144912440301039911028002c85008001802d40840c401041c240f1101e1100e81c01951080c40a01e005e260002454000c5210b80d4002d48041f00c12460041045c840355404014044036030f40b0703110f020002c0303900d4406840003d40c1c40625850400040f01c3c6d149050601c14901c45c0040d50b002404c1e80c2241c10440d11710b0000c2c48080c2e800812290482140038654540d00c0025034141210761645100303691a9000c100240d440f240080713848507010301c01a0b12400ea07050380240310390209120000088803140700980400d60002030251070307a04003480648620320034400e8a0b0480076411003141c0b00c03002486d41c0c5145002243c892401040e00c00742c0500c000c204c2c500c1007040008a502641c21500d12101d044400300b21110418460740c5c020394079040020701c41d4841c2d0b07017050b07800a450420071289600c1e0f4010383e030220050f003a112245049980c00c0c041c6038400c800081026000a5140480080e0207030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 993567679 1250 993566429 993566437
    0x622020a03062a030605010f0819020f0c070f1e06020705220c080718050906061b0f25050d020d0c081e060a050601080c090f0d0302030c060c040b 64
    0x344600d0f2034500d0010311440c0c503d401c14182071030403c101401403035810004c0c000c0c140d901c552030006a02c4a08004034501800a13a8024070440208a1442c02031449020203544203008000191204120300c2c5542d035014045a8040d00f20803080052880c5040882c0089903400f6003440441c01c0c035018204030445d000500303042200c1c1d0540d01015500c2640c0030035240706142c0f010318032400f42082d170381d0f14400d035218980c507104200b00d0305c901d00c50072000751051400e41103500a4503005540340c2c000c0341c9070f840d00390007425418001030081401c44440c0601b040c00d2a009a0400c8030580c0b009459075840a0381c0c0c0724401c5008680f12030007207400e28010000e602003400306400b1b030281401c0c10074401070103a200d510f280608405c00465540e0702d0341c0701800c1906880100d500d012030017030074049031080d403141c01440d001c0d1a0582d500c42103501d40e510003a0a95203c031200507401814000e0107507003511030b095020b00a40c0240c01454403160f01503130050074048014040d5001540c10442070092131001d030309035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 993568929 1250 993567679 993567683
    0x1050105031e090a2003060901110d0506120a050d02010f1503030c0303060e090a020a0b090d0201080a020c011e0f06080d1d0405100f0b0a120506030a060e0622020a03 73
    0x4031103991100d400f600d0a004103040098400b20281c110404522000310f540c0d10b44820a07400c0f5001030303541840c10ba00f03ca0902400321a0104100700707100303964145400c52134020a000327090034110120350340040e14102c0800d008a03640e4103c06500e4001c1c98086c424990404441c41d410b1091809201d2112100c0e00980002010700040f0088d603800c1c540305c1c0d8020009000d42c146d5031103860801152481e549c40001004910440e090607011501c150800c0035100356800c040c214101ea80c88960056a14100040061f070241c0d5007404001d0409409028815a1308205040b1520324541001c1d40c40c02d07a001c03d819012080d0400ca800c0041c0c032000100c00200258600c0c2c040303100b000c0390403c41c80340b02d49079070540c3c4e0040c100700a000003443c44c0d0a062045800b010801c41c6540d59496500f0300c81e00802d07004401141005904400710320f081e401440d4004002015206100401d170f8401c0225032480c03c40c3d800d2940303c4c10410403610801680700001c0d105681e048003141e58640d0005100310414040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 993570179 1250 993568929 993568981
    0x905031009080f0a051204031e090f0627030308040606050306041106030a09020307152c060703030b1801080606040e0616030e031c05070c050309240f0d050105010503 73
    0x1302050081c803540c01d580040f0340038840f4140764203140c00d00815115035100b501c11200c00c005003480341d541c00b0384006000c840214190f610b0341440c4c1542901d020810031500a08003004071340c0034140300e01200000b40910f101b900c890078030342050f0030240c0440e82c8176009180a40d010809000c082404001041011b4504403125903880d6220a001805018501c000039011301c02d600300464003200f896501d100c40342c5030307959402d00008400c16428103d40905892402c425410142e48a2030500400038110709000341404074804202101084518041106d10780c080c000040040c840000c050150300d4002208981c2402544801c12241e511418051300192080e02c1d00303860301c0160380c025000540990001c2040d40e441c1c1d0390a518101220000c0c810440e40a031a01001642160140b540c1c00040c035007001c015803d09200c0014070190070201440715045030380c01080c13500309007110380060210480c0101000c1d1600c2000c25440103541d0107030082c90510800707000700b002e560842d441000c0400082c141d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 993571429 1250 993570179 993570187
    0x60405130902061b01020903010b0a0501080103030e01020a200406080d050d0e0a0209010e160815040509010f050c0705061b030c0a0909020703080402030f06090706050c011107030905031009080f 85
    0x40060b00c113104001c1c20115400c00b0010050b100d18040d0301501c202ea03000d03002441802d5215040090041090140c01d000c5079102c4010b1000c00d206461003098140180120b94105030a51251401288110902e4041d0040c20f49071008a050a0103a08014401d0384028060080125005092030003a030301c20228983c0d40b85100c0d800e00308104001943d244d0081c00b03015965071640480d120080040b0b5000342d0600303031498691142485500a0752142071404040b02d4070407030381800c1201801024141e920650740b500e070102c0b5030040390320407107001e50740c0f003455151348031400d140c40740c00c180c0000c1c400c24492101c1c80851512400f0b07181166072148022140a994000c0480156035000d10350f004110072503c041030800415400c4400d0b540950700840884a90090302e010499a0304412202d1390302c0341d00510020000703180918040c0c00355403484000458601c080c1c1c0345a200d41d0304080c9041d00010b00320340c070400c81400c0c18070810041c0c0c1800d980510511721143c6075104248907500a000304070034005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 993572679 1250 993571429 993571433
    0x1c0e010c050316030e1807090e01030519030302120c1308120708210a0209040608010b01140c010902060d0f0c1119030521090f1f110c070b040807050604051309 70
    0x1d0240380b040e2000074925081203175102c06031b101e900b078110b0f407040100e07840c0d40002c200703000c02010030760489510000505407900034000e0020845466071040b0180354023031185078031103035404201324850741043c0003003604c403c0d440803640c034840829030241b010340c3c0100220300480f140100441c0c100319085003003955902e0000920301c20024000c0f0b4652402a925010302c03181c5007803a0028415844110740c1400700350b0b01e40100508071038001a10034003056080c110b41c482c501c10320000e80541d950240c00003c048840e500882d659601c000301058000d50b40d031614070209d0580b4881e0b1b03c030390002403401111a01d00c4512031b50b5035050444000d14110111449041054030030400c441d04c4091a4080419a98818484540f883c50a03a80c808041c0a080c40000140e100080c18031b80304030020b0303250080d946515512200070a20403145098500d810000b000d03048000300174000051440c0d4004903940c03031070580c00741c0c100340e0160000340c0b040200b00300c1000780da507a044042021710201c8070700084141c2e0f14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 993573929 1250 993572679 993572687
    0x2150c0a0c1715070e0f0307180b031b030334050c0307060813020d0215030f0403030b0303030609010e07020c03070807050f0406050d12030207051c0e010c05031603 72
    0x8940c0003040040640004669440c8103804104000314450407641c01e0300c190312003000c40c2c03041118018000b859180c0c0e1000140b0b00f42c6070700c040107000901036411064880304844400364030540d940c003030180c81e010018443d0604006c000030410510400c0f403e4030000a0000b0b44038490741d4150904081000500c11180341080400f03200d000942010010810303040c602591917049281e00d192085c041c1d003200003034650191580502c5426464a071b0407130100c0542c00c100440114031001d076044105940e942201d4494000194011405e03080e50002616061400405035030810340c81d82e010341c0091042c051151152001c06064030110140b400b5a5514614101e10740840080e68540c1803003105000140788202143c0102a0366080d24400c151603510414003040e182d030b5100300c0350018180140c03c5c01107660307000c1c0846180072525000d4a03082d10354031254a000305003008021078000e1092007107502500003d41d8107800380207080100714040951507180e2240204518101c542825041030410584030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 993575179 1250 993573929 993573943
    0xf010f12140f0106110c030c011b080307080609010b040b0a0507260301140423100f08031c05040c0e150603010927080901120612030e030d0c02150c 65
    0x1032289200319150407007540030b0040b0284110004140d02d488060860076000c00d642c2e03618580503004000d80f0003400c0c011108180455010780d84410034900d01800107460100460141e0302d1079641c1c06903401c2c4181002010703201a4480700752800700b000304000740441c19080c0c544030041404d1064135000f040c14840580360481c0d012070003410718500001203100544001e141030f9526030400c03410003070001043c001190a40c041030a50300f0a6a29103041043d28010540d030b1205407480c070140c499550f1031a0702c809074a150801903058101140e00501d41040c1d04108142c0d07071045000b4400c40c20152a984518101401030810540031240040e64540e002003500d16405405410150743e03607035642c070600040007110350130a404070b50500d8007060080b00c01d2546502c6600200c0c2c0c54074215440006543d4200c59031401c00c40961141d1001411055400400c010309001e51507071120146000d04160614551200703243c24042908808000f6880710b60b9a00550200d0450703140e5541c003d82c1c0c04d240341a0b4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 993576429 1250 993575179 993575201
    0x7020604050405040f03031d1f0b1309060c080f130606080f0a0b1003020604090b030a0f110a0632070b0405070608070f170604380f010f12 61
    0x30410080c0001c002101c010400172a0082da0100b251800503034144400d103040e4881c4c003556501250b01800004800d40c121007500300b2144000176600e42e10000f14170800c08801d05004070310b643c0c0751002d0511400d40140d0401d5219490005582c1c68510180459020050700165685800d40f11907010800e1561241c2c02400e415000c0b500b050085a5410b940d54900000031a010701c842e0010610303034400d0390342090580340e009001608040c00d0039000f4000f414002034440d858400e2500782804144840040c006203400f890381504845031850038405078100315400001080600316492002204003024400303c2004102203603c80001040760910070b000355140a44034181c0d41c014001040303800039181c021a815521400b446075610780043c1d455082000d4024082901e1b02c4640701c2484202c0c0000758000c40040000400c1e503101c141c0d50380320b5604168040440d03000711401801c2d41041d140d8404d844482141e08002c0020481c0000b01148003008894051010a902e2140381c03000a42041a140c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 993577679 1250 993576429 993576431
    0xe1914010902180a0e040b0a0b150c1b010e040e01020d1d06010b030f063f280b040c0e04030f1205070917030c06090a02030c0a1505070206040504 64
    0x940c40d008890020f50112880307041e068a000c2811401303003450b0018804a030360440340341005a0302da44071744205200041203025440c0e03480c00c01d9140b41c0e8500048003840b0410a0400d912642096649441c1103d6001403007200b136285550890b01e82c0c0d000b55544101c480c10f0710007050701e444c1802c56501a010784049100c0e450300300104030300000d80102c01903c2c030441c031714229000e59a81d404840c0f0588810740f816002c1104c0940010f40134100025100380e01e000d80301015014414607010000501103040c0c10b65102c1901e0644504081ea0410100040040d00c0366a040101401c5068201a40300080020000c062071000981404144580c8200501d001c5c80c00180a00c0c01f482c000785012420303040800440e04601c0001d8804200c0e22889120b10349a85400342d15504026102c0342c1001d0441c61701e000b03031204111480c17074000c0511040740074040700340051015140c40c2c8100f500307010b82c01000740e000700c940250410100281011052a0803440e0a0043e17a5410328008a0400c1c4541d03040701d900a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 993578929 1250 993577679 993577681
    0x61109130912080c0922150320130506060f0408250b03040f0204020904020c0105090705010c030203190e0a140f04020301120314070605010f0303080108070e1914 71
    0x42440d68004481c010310030300c20000740602031001550228416030704440c820ba0240544092418912a81c1c8181003525600d1384185c000706000d8800c0d118480b86480001e04450020802c10a03200c00d9a443c44884414245400d540070000c03c040001d244034080c0b4880e1180701140c07041d240d410031180303c3c01692890603580e6480e440429990f1540c0d0024040030080d841b042c05120b40111103450a4074800003480d4a981c545880d081001c514050060742e01950802c52000260340b68401000c08030310b440000f003017501c0e0080016043c4a103503840715051041509290001a601100b00c908200942000f844401d050b110119600d04131304000c1500b10302c0012002c15048000d91480c0c0e041c060440701d0a031500c003c42c090000740c3c0270070b204101602c43d00306082c00c0000d00078805200322011081c2e0040c1841015102c40381520b8081c4e00500c210840c5000520903d0380c44541203024200090051012030f2500f08000c4801c0d600a104403900c03941102012254120b58118041c040d40045001c030355 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 993580179 1250 993578929 993578959
    0xc050a0312110307080f07060b0a093207180e1905060a060912110306040f05060a0603120516120909060e010f090905150103061b020105090703061109 66
    0x1d400d07a109803040850382c03a80300d00501d40b500000b22030304c05500140e018200300c00c402c0300000c00d40040c402203c99507165248a0703603940310240e413440140010100071510300440b00300e209040141c0c1d122280c400b1510b910b044001642c04001d01d4005441e854985070420b44210804644a241c2e00305481c800a8201404010459800112400404681c0410043d1207810812440300803a1140c3e50205281403001c02140400c084140540c60041301801000b400000009090500c1150110707044191504400c0a1140800c2580e921011500301001800e0035915810040c050041800003082030001c0c138040248822010b400160390302c204601000803032030300d001d4200384250003841c4c50b02e031400000041450990f032101c0d048440551041301442e05003000b134800b80c00c0ea9003041d0346c01d04c10305039400d9560088081301c900850003130301c002507034000ba03601d00c05000104011301c108580c10f000520803c0c040108004044aa229130006400c034400b031149202030103a201000d6000300b2030301c2c2c0101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 993581429 1250 993580179 993580193
    0xa1202060103020a15142a03070b060d051005070e03010e060105100914041508060114011233350304240302041a09030d031e090c050a03 60
    0x4142d80c400c9424410302da407201281c8043d210b10041c1540000c46280718807884400c0400100b0300c4070080402641c11055806c0074500c410690b020301e08840d0300014400b010700c6130380c0710704c41e03009242110888440b039003649546549500c1d90300c0e1314a1296956000c04e503030f0350140d00e8a1940920207030080c802110003102480d15800240304080c0100303a03c3d1080d0080e0392050700c040701038603411602030881c041250148030040a40e0b004a010002c1c4a43c4085190b000030004a4000e00301202c2c2800c7c0348140b24001002e00e901c50b21003101c014105402c483d00b081030031494182c1d000440c00a0000d84d40c03c0d00b0f441c50100800e50085011014007403240800448680e400d18921400801021000c10f10140749079070380c0b04511400000d0b07640c1814230705610005a440403c980e850307250250030241c0f14615600c10942c1100340c441e420a0000c1c003031940d4113061010100400650408000b0341d41d4516600c00607000442c050003006070b464002030100004111250080c4c0805010f044440342c03030b454221 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 993582679 1250 993581429 993581431
    0x501050f130b100323100e0307030c020a050612180109120f0e120304030611130b160602040906090f0506060a0507021c08070c230607030e041145030a120206 69
    0x904038001e0b10383d01c00980040d401007a20001f6040c1c011850100d40c0d0324221520304074603c080ba030015800c2c50026a030713950880600b10b10440d00060b1350381c0f820010b200d210541401407800c422a4148109a40800c2807520045444600c03428245081120f2400171545948008002c0f9486408184030701100c1c00300001800c20340344107403020014000c603400300794410301416508034044810130a09100c140c00d050080c0c02e250104900710155118107076070700340584e00280c00030155550fa52070b0400010f00d01e4000c1801450541c80100540c0c10000e02191041c4107a03800407062100000724141152281d40e41d818100501303002d02040c07007450b860001410f42c4191400e4540140e544000302d00c0820300409911903d000c8240e5290050b425002c1c0074150704900c0d0281c050144032030846149440e80c3c02070b50400d40e04021880e641d40300760302038611041c00e540028103096203400d640f204126101c0503540d02c148a468082100001d54800007460800340d860000d140182d0507111017601900000c1032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 993583929 1250 993582679 993582743
    0x20d1409240c07060914010c050a0605010e2d060118030606080a0b09070806070c0c090e0f2a150c160e0c1206040c090807080304030501050f130b1003 66
    0xc0d0b43c68a6075843c0c1110624018010111a1540d070b643c0400591700030311005c07100900c1401903850b81034140c0c80d0a400c0310400d034001c0030b0302038044003040314509240c0e000c41d1804509048078000c25a2003002e01c2c00054000701600d050194014100043c0c0c1406801c150003158015400d114450716a548152120707101c3c0300448040c070000000c90396119021074060243e0304c0c0b003030080c449a44e8000c0c1c21901e01c503502d9401d44148071501c6001c00c0800803400b6020784c01c140c0340000e10b010b000c0040120324004040c80c900164000c004600c22201c0c480d00008503074140101d898456911901c13908000030b01c02c00c03452005c81d10444521005803080580603808035a092204042c4c544e60780042001701d0300c45d06140300b0708409034000096861901c0d40c8103820b01a4a071800c0c0f402d40d0388030b80308245081442c3d00841c107071b0352002c2030401c02c100d0309009541e808540e4800325161414402000c00362006d0310b5500070b04030f1100d2800140c01d2195070302601c00558004002c84901c286503000049250401c0c269 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 993585179 1250 993583929 993583933
    0x4050a020909330702120f070c091a13021303020f130516110a08040e040c030c1d010510052a010504060f0e010507090b070606030212060610020d1409240c 68
    0x4d64040c00450b42101a480460599190001606940c0d0107540030000440720102c020310007050034200e902c604010008510407282014200f0420090002c1e2540700f50f42c2e60320f0040054002c3c466070355201d041200d0b41583d00500980323281000400c071108144400140f2031400e010082c480c03d0000d40c04c505625283c0381c810079000d84c0c840e010f0701d8903040d65020b0b014210401c070801500c0682d041d03480d8003a0150404000450b100d07982d0241a40140c1d20020704c400b80b0f18050403020f200130390803500418044807240014440b4940140072401030441504010b180911084400064121010340c044101002000382c0e14152030800001c007056201c0310f181c10b01e8010040340d514414413500c0d000d241180c4440720420b18241000d9059403080c4800c40d40280c480000100588600302e010340806030042c054001c0340741410a1104600000c1d8000c030856100c02c816040481c0c00c002003600c0540309640441d641c108050100780703541c000e06d4500c40d94003003610580c0c0b005024000604011129030301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 993586429 1250 993585179 993585181
    0x421020c1906080c030c040b0711030601080705040e01020702032812120c020309010207050f01030f060b0c0c030a111c05030706050a0b0618060c0c180115050304050a02090933 77
    0x44840c4c4280000c03280584020070030001030095408450240903c144551078141f20500c0c001c022034103014080c0d01c902d00691004078244628680350040b00c0200070180001c5050612540009540c0c000d0001d2001c00c0e4101c90b4103100c4500680e1011520341504a100b4061005050a00900c0340b000c03900310005007883c08000c3c00c8401e1002c41156000d440c140c0c01056414100020002d0240501681d10b0600d139540e040d4003013148103405040c000341000c403050b07901c130b0003504115801c010a05c0e8107680300f60041e40b0203d0008503251803040001c034040e6034031100d101318507042c2c00082c1c03591000076115200c081101c0d802c114864100d00d2043c650341720705101c000035800500c0101d0003200c0c200c449110070b0841c078004600b030480207404060b800c002202e42480501c0d020940c507485030400e5480c850010001841400919003041100e4041850b0245c42c502e02601c1c0c16440e043d2600303009102e104034202042400c0c104025402d55851745040803c130490b01c1c0c1c0e5030350324260101f45c4007401c6507120340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 993587679 1250 993586429 993586441
    0x6050d0f060501210617060105100c17180d0f031106060607031d0402070c1403070b09041d12041d01030c0e07050c0d050405180421020c190608 63
    0x10040004454060315042600134281801291070a59010820708180c1d0350640050120001c1b04024000842540a8061541000240044d00040c1c07490242441151b07101500000ea4803481203d10018211403103407940ca0181000400141e966141a03019822441c0c442c01d020390031080b0078800d1311a8076100707a100039008589480d20700413150359501640901801e00072030300070544500450102e80c040c11400141a000a0803600304104c02c0c0c0784045442030902549040074800401c0d050100c008014035407034512011424441c00400c03a000703989034208424042c0d409981d0768000001c0f50103685d00380ca88507180d049190014403800180074800c450758007401e0340d2010220b050740c0d044056024558203182e515120404080d161501308071040106507181a01400040c01d4400076598040c0c0c0d5510381010000b0844500013078103080d01d001c505101c005110101c5a000c03e074061601d900030503c11600582c20300e16501422604030703004001c03400800a902034820161070094075550407a803102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 993588929 1250 993587679 993587681
    0x10020706050f250509030f072702130306020903031306030509010b0d020907030e070b03011d01090e0c04111b06010824060f062101060807050f091c02030706050d0f 72
    0x12204030490f51240520340f0140301c0c4500700400c900c0d08040c2c121800320041075001c5140c0001c03603000074500d0707400c41040b551101d102100b20200060381c010a6040400030b0b8220140c03020541f200810705540001c40d4841528140296104005007244080c0529030741c44018020340001c54281e05603510700003880d0060714048013800a0650003030900005695550b1b802e5004062810013080c0900c0350300c8000500c408298002c5000e041c07500b1340175108045802c0703400714480041c1c20001e482c5042141071402c4a400140b90031300e032a021140860b2280004038032600c0c038850b64840721031051400201020ba000c001a17424100c44414080741c20b001e0243c510310f908118000c0307800410402d041c02061052801c0b508401600314010562443c02c451111140c1940401101c146050464000100100c9030031440541e8050964240a450400b601400d040e041c0320b64400b25101c0d8107620008011946000301203181103901070110350110380ca416020b80140c00c80301025210b141480c0008001d9046 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 993590179 1250 993588929 993588961
    0x60301060902210a02090a03030c020f01030506060304030810050d0309080c0312030c071e061a01020d0504032012030c0c1e010305130524010e04030503010e0910020706050f 76
    0xc0d0140c11540300c441e610200fa2001c10292420342c0440d020300c44020555108811200254400d484240c21112a07205105444032190b443ca41810320700010045582c0b6180c0899600540c94601007a09070b81d1103c070311a0155241e000715403c1100344028100300750b000f450210640701080211410340040707808050703407002505030380000b00e04144007013419102220050320401d03116410450b64421900c001c841d41e002d90600c10b4606039165581200c58102d2807140700404002880682052008080050183e1095100085c45c0610a0a030324402d00d01250660b44201c10080c0051095401d411041c0d03a030350050002c044081c007584030540c09914000840501c001e1500d583c401e40e052200c0010f44c000d2400800c195a4441d00300040030004400340644103d414410b00e00901070601841c4884070304c101600002d00808440040c04081780c0c01c0f03400e99044462410443c90542d0380c100059060a440e00e0071180c0c05400030a03840c04001c0140c05c040e104150740c6111001e82e90310444007c0b00952 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 993591429 1250 993590179 993590197
    0xc0513080706020a200303030703090b1803250b070f1d0a0509041a010816090905210408030309010209011b020d03030b010921031404140d0c090212060301060902 71
    0x4010704001000403070400c40300e0018405d5981383c040e20301c031100c0880d09584c82107600c00000780d6a8881201000154150241c03c100341d0411311444112440f92035540e442905002e07140c83d00c240da56604c0300041040b252019a0780704600f882d090800d28400340400c4001c90164021624001603c0c003090000e070115120002e004121010030317440c08090080489003c1e1095840483d0220300e40d01040c000c1e50540d008081140050508a50058120f04a911503400c4a02c589060108000c003140b40051802c4024060400d031075605560300d41140078a104503481402d05002c0481000300c40e041c1035020f050780c90000c6c1c03108250800c500701c0c60824460356142c001e50115a00002d800880c0c0b09911010f9040010f06040c41215100d1180300042c07411000010006041100107004041d0b009849000d0000f80d44103950030035061600101030800000005402a241c1401c41014841c1c0c00d980c0d84010880b00d4000c5595030030240c210f808600e021990b0601035800d0400010b4075007168400c42d03d00c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 993592679 1250 993591429 993591433
    0x30d08060d051b1c121d030f0d14120a0213050d030c030e01082802040506040e1611030d0209030109080409051015050405090901020c06090303040b13080301060f0c060c051308070602 80
    0x1d881c1700090790400711000c00e201103519126800c01164400300b01580342e2440e80f100030a010f02ca4844000c20040400280c10b128081c20701081c2031620602c00140e8102011070005a02c0f00460415920310548640c0025400350100d90302105064200c1c00c4150301c0f80c00781e50b5114282400c4d500640d20f112046d0340001b15210b40342e0039010101000301c0103040c91072902c0e50142c0703001d55074030001700650000e812181030380414005111507554698a101c010141900308428120b0940c982c0d075441e0b01440700c0408207283c0025124980d0b903003c1d031212125590004501d42c482e40c48080642c02003c1c120f42065400c5a04107000c5901200309100076142d1191f5518180b400c3d042c8400e1100c0420701420345540c0d59000e011402c8ca001d414440240304024200003103489152a042565502c00007070160b40307022503005903102c08200a202200d0540d00541000c004400502c0d108540015024070042c004da031812020400995004000b0080a8101c0399104000307034a40c3c4165444540b14400d400240e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 993593929 1250 993592679 993592703
    0x130b040f020406030206030718050a080d08130209040f05150f161e08160f021513050106152a1b0b0d06060f0509030d08060d051b1c 58
    0x440100e60040494406000450b0043c0c0d6903010542d96001912000701041c1850040e40044d6146030101c002410100c8421019900e0f00ca5602d031501d4502070b200c1c003004540000a80181400c0004082140d8064009070f40c80ca0b190828040307140401104407114040c0c0148880c0307090a0034071540c01280c64142c5521161103120700f080c5e404c14149001024021071000c4a1120070200750003060400d1640c540c80f40c00e02e0310040c000c60b07003014250b41001b4400143c000c10081c2d540019161064120701030750800984415001c032120a80114000380158281180816202c2400d0400f681324001030b04d920000300710808000302164802d400c02802c40103071040800201700007800ca08401440d001417000359644540900809034882c00569900341e446074000c101480c2d003d00150903014140c9041420110000006030729406507920140401c5200740124100b95140c0750711070300d140d40c81000c0300e0181c0504042010351039141802c1c0c5211341c1100c0340f0101c00d002200d001c0d482d21382d400b01a141003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 993595179 1250 993593929 993593933
    0x112020906013905060907090e0706050415140c0c13020c0c040b010309050706020a051006060f0f05040f03031809050c0a081f08030d150b0a0e030a060203130506130b04 74
    0x140f0f01507a030011004501910081c03000c2002404040d004d1110000030b40241c608041000095a812031090419640042000c05c545a0311106a5003076400d0040f0511074118041c0d030072107066403981d0505010080c0011035043d59070300050854598038043d50000d10300c0d018489140104c5c0030311b01d92002e9580111081d021a45007640c0040080b0310305040005101c1d42d9510703820b14100d401e80141c1c0159010203403c070140b05c42080040840c690b2010140703d528101500203295402603031a0006010a20401048840c00f600a6802600f4010190f070a02660b904000300146484070002c0c1e03041300d8403a000315202003240691441a002c18400c180b80403004401291315240080c0301400b104400516282d120100d40880c0006040440c0115110391940ca02c00007101e1500c00c400b840d48082500800c640100c0009883c0d8016003802c128481e900c450002c40d04042078920028a403510020402c104c2c051441041032096001d10111055a80c030030540b10440300b114007025203284084000900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 993596429 1250 993595179 993595247
    0x7090e0712020c0111031003141612030c060e070e130b0f0c13120201020c03010c02071202041e090302160501080402090606120c030915040b1b12011202090601 70
    0x2484007003d10000803141c00009030040359800544d84110703c1c40741c9040070414041c0382407060800c0844070001c0e0122006c52000e48102d01240d128102c0034509018184e0705150060158880480e0001d8040c04400900e646650b20b4000318010903c1c14100000422041c0c00d000310030748609680220140710303d1304c0712000300304940030051540c0d100c0c0c80b0410441500507514070560004002c0c0c3c1301320411154080c80064104400340e080180280e01d4600403803252035000400100700d03000c1c200d04e5060042c080c0081401340c0a25528482036000016a0300030401c400c2c5e00c007503040b5010f9400c0d500025811510b0203007011552080c0e41c00a01e8031030114001d4076225124a400080042c101d80c60b1072003900d042450a101114140780904001c410400642c0091203104240c00340d104e103001c1a460140c0d51819240805410b0004031081c21031000c112142060840e14010045480d40c4025a507400c000528407038244803c80c040c003140c0c402b0030410f5004240c00f5142e20b40380c40300d2413000d01c08064000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 993597679 1250 993596429 993596437
    0x20303010b07081309060b1801031b030c14162f0907030f0e0d030e0102040501021c09032109090c0f110c060403060b0406080604150218060a0807090e071202 69
    0x700c1011000100185c04801440740b64024400d20b06e20603180d074410740e241d00100d0341c0354410364103050030038051446804c3c07110f418241c46030007401d00140b1010083e808481a1000e080c81041c821000201d00e003040e0303030b4440c1d86401d60b8851030510780711010601035081c00320180d81e200c1c0071101c2c4001915642d460084c01442d80f0080d10314000074000302081e00b02c030035600741070710789901034100c410314403032583d4140225410860a880250701d030602d0000001c2d91082c070301e403e00c0d0320204006c502d610795601c40c0e19480002e41d0000c0c070344c03280840140c0070b0b2a03800c1031036004a40415020003000501c000907021380081c0b60f2246d116030080081c200d0094500000e03054180e007150140182885095a440010304081c40c050315000844900d45014441103c0c0e090700074590702d5000c84d00308800901007200a503011881e02001603180c0001040391565440700b83c0c0a04e07070140740070500b01951503105440030311640060b50b41c01c0311385541e000c1c000c202d4101611140c0000b0400d201069003424590018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 993598929 1250 993597679 993597697
    0x180e030a081e04030503060306011e12020a050402030108150a23090111160302010e07080303010b0711130506030d0804020109051215040f201f03091401060f06020303010b0708 77
    0x202e802a07002068441120307422542140401c001000740111414204002c602521041401700e602d02211895100403843c1131003154801e031074101d610411926280c1c00d40d0010480070340203640381d5860b2001e658490b041492a2640704000c1e0001130b1422803207004480e00b002c110301501d00001603c001d480010000200141c40315926100505148103101000b401119511414040c500d0000d140c000e01390f070320507035541d490b603408228203000c0d0180200c202c0e8110782c2034844003592f915242ca030200411801504d0641c1c0008006541c02c0d00d14101d421042c400e030b004034261601900180e20665284c181924003034005145564213003e50706120196104251140f41110019051701d1040d4a1074802114101c516080c00d007441d2003081006500d407508035000040c2c0f42c000002d3305010402035020191030030050242c8100200e40380d0301a03841055074642100401c0601400702584501910461090400300a0702c1080010542d01c0402544e050b5400c01e98041e14160f01c2e0b49070320303032079401101030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 993600179 1250 993598929 993598951
    0x310060c08130602070f062a02010c06020706020306040b062b020c0f0f1216030f0c0b180c0109060206190605090103060f060906121401150906180e030a08 68
    0x8100600800320410081240e13900808902c1d041c002e200720060041c0e401681488600c070b1100f8407130351940c090b6032180c90941c031901031412414001240ca07100c80c00c0c40905098400034482c400e200d55600218800c1d001540d0070302020704e1180c140300c510710442d40c45252038641e042c8001c80844040b12a07003200c500e54407007d41400450f246580c02c0480d01440311285912203004031400c080240070540d200007041890b00c1c04e114503d42007542d0414903210090030000035005100300c2c41c0c00f81911040950304000890030790720704606c403c010308480c20141e255521510549080d13a61182c03140006403400d0785c0c054070654840c80d040600c40d410320007203030400603103c1b072000c40c0d692154443c1301e00840c041c000c04248000152240300403100250000c00d500340c1041c0d400d000c09440b0b1000907039019030203d251005004c00b40c10060042010442100703500c000584001b58010f040d81050301990010305200c010319010000c1c2d041100c0c00c8044100d4141c10500c1841c000500666550740d00c4103070a25 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 993601429 1250 993600179 993600187
    0x2030d05040309080318090c0c1c050d0c020303190203101809051212060910051e04180209060306070c1b0506030f1e040503030114030f01060f03170310060c08 70
    0x10070790a40e0804000c040691040030294200c81c60003004940c2c100001c1d10003a45071001c00041141c0382c0d1082c0c503200d100902c050344ac00104512800c04c9541c58a0400c004000f0919150b000944a50096072902d408001050f1014188131541c42100d004800c0b5003404441c09160459185540c011262000d94041e50303070403004049030f001d00200324494490b82816540303511642c0d0741c810800700500424054440030040091054071901010241d48080300d00c401c07607041c606010403035203811b01042601700e800c00410050903a4004002e0301c50500c01c0720900300e507a607481d003030554802048480f60009800340d03040c00003107030148000c1302d42011070804501d1019243c1000c100c00f680f00361005070307800e00000700304810a48120717070341c0c04054604064071010303003032649915a51380018000d61134201c4854000c9022503904200111400c1c039074000038019036a507030042000d207003517034801076409030031742258800c8a007944400c40e44554285102110440c0c1488000c4400c1c0f103070004200c6031000f00b00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 993602679 1250 993601429 993601439
    0x30a110705010e030a1806120b19060816050c070b09030304030609110a0611150a0e060f0406240e060a05040e0f0f03120f2703030a1b02030d05040309 66
    0x3c01801c1d658405080116550f8084000080180e48500304064002c42514002d20005138051210600d02280840c0030802d8000c81000076070440305e4108000140d104400300003145031f0480c01061187c0000c0c034041c11008070f4a1029116485090030a50554010000c1849140d4219019041101020742124205a200e9035481c007164400401550920000c2c04111000d1400e4120800505654604086079900d5402e07035981e650300007103480c10041c19050010343c0203d0355512204280e58188111221810000046000040143c4003900e6003070601c00721403074118914511000c2c021000812081c0e0368605015041d0084019080c158407034507458002459656501801c81540314120183c078400d4146440646040030741c50306e40c00705400074030000402c2c0320b00700703002da60060911103d5150f96940340c20701c0300120300040c011f80308060b01241d45264500c00002540c402e5210a1003001406810486d44982a040550040c01a03104000b00c2649030401c0e00a19003140c400e05040e0121030311a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 993603929 1250 993602679 993602681
    0xb04050708030f04050a121214091309060b03061b0d110c03090a08061302090a0216030f030501321318031403010509010b070f08180f0a0b030a11070501 67
    0x8500e00f07200c84a0041002e011741d107000350031078008200d03c8406031450318803595154074010307840c0d031010140900100025000d41214040700c841401c010f103184c04480100181c00000c101100c0c1c00c0d03c24602d0640001d245050000f0040e0190884148015441e00421003212a541c840d022400340c040d120340048446c0d801d00405440c00c4244540a1500c4061010511141b85180d5101ca0055884003003481202401d1b0185812150380540c0c0c450381650303400b150341000e403040501b0400101d0355010784105155101c4020030b01d0340302c2982c043c41640da94054001030f90046041100d02c540045210552081d854100c42e4040000541b541c022a52540722210464415480101c0140c100f086d84c40201503006081c3d019a419800500d810765041001098111405000c0d0301d400800c000f40000c14084c16840061003e80c0c05204182d55084004120900c902d041c2e0030180034a5007110801194074040d9480d80a0711a421505400c1d81e59104104020f0f201c4000b2841300c01c181040002c2c0805d4007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 993605179 1250 993603929 993603937
    0x90c07050703121701050f0d06060b0d05160203090114071113020d0f020708180a1205010b010e041e0b0a09060f0f0b0f03130201030b1309030f0c0f0b0405070803 71
    0xe03036070024509070003020113010380000b4903040c1d6020302d05100500195645590036052448165081d8041810915000009006540101c4890f400c0030a441d140003440c0c0e040345120380c3c0ba011040f595202c0042013aaa28010308803042d02062920020009112055020b40130441c0604075113074400076400c01040a6040c560b0400300c80540015042d44211006d000d66039a807001518110301e044400e40760b1100314081d03100745000140281c40001c6036640c4030006140940410b000060340741140c1c1c03030300c14002c09034030302081e01190202c80f01c1200d91800344a412076086100e0202c990880c0a065800010488414555401302244a01140008a9105400140c80380800e801d000b28200f02080024601e6030744050f0040c0d02c2003080544801150085d03d80280b40743c09013028058191005a0141800780c0c01e0315004a42d1914841c0081c01c2c0742c0000d80e11901070385030b6444000107000c084402100e1030b03d0240a00d650143c5140c00607030f0f80450306a01c140560140c80f0216240c00549080d940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 993606429 1250 993605179 993605183
    0x1b050a030302072f0913030206060603070215090c030c09040f120504090f050a1a150a02030f0715050f061507050a080a020a030e061806090409050f0709150302010806090c07050703 79
    0xd11400b022903506080a90303a8104891b0455010740c000b140d03800950303450780284500e00461022000c1030101e402000b058965021880310098580b038824107007541c070902e180c9441c5c801e128400b4904c0c010f003000c0614502950304444c904d281c2d07040070f44400440004503e450000c00c10100f0000400c221300e40b041400001c1024030106407814603c0c1c40302d090b0b170540d122034114140035840b0440155509221070300030112301500541ca510701135105030300f54061000031810400000807500c1c10040062044140000500c001300f0150325040f2400849071005c5504c2500684400f0007401c215401030060b00140c1d1298084402018140d42c0b640c8460b000500301c030740035a0084c20101c04042d04194482c4200320151861400d000d03200402260b07082c600078020380125000545200551104d400141005800104a440d40d50000e84d20380d986882034825502c100303141c070802d503600e00f000b228810209c0c3d030140e40c2c0e40da680e11030104014040074081c110020030780c0104005800a1028050b0000440c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 993607679 1250 993606429 993606503
    0x604140f100e03010f23070c020603010b0712030b150903030d2f091311090d0321110409180f0b06010305060904050d11030c07090501061b050a03030207 67
    0x201100e00341401d48081c54100f6005ca81841c040040c000061032010301c1c2c9500380c000e00c000d02d0703d49000554001079541c01c065082038000001050b172001000081400c9880b54401c22090340000c0811021180d003407402e40c0d0b0003d100174401461100001c050818001e0060070b49103024038018001e002c54038000241814800c801280300101302100c01600651031000f178689190400c0040010700c203101144c0300c01400c554a50709804140a6001500d0601c070340500144094485420040d01103000b004000b41881000740c40010b004a6901948400e1044008001e050508041426001e000004c0440310841d4030030020b9004070703c030b1100942042c1c1c0034000508a5044c20b10004060b24001030445008614004c184000180000b4885a03d0811482c1c540190524864124114400d034941c00d0365502c2907140108801c00704c0c3c1d001d0341c101e5400d42c40d052801c561030ba103122601d50380d4000c042c0c480d402020ba44004603010b40c00078106544280c40c040c00b0182d24840b000401d00341c00c0410705000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 993608929 1250 993607679 993607697
    0xb090c0a120e0c0a060804110d1e0c090b0d080304080a050705240f0402091605131d0604050907150917010c080108070b0f070203010e01060b13140604140f10 69
    0x21305050003800043c5c80e280c80d04051a20b01500c42c07050396a50720850303e0040226001b02e4003440f902044c94960319038040320002680c40b180c00c0101d1011450300502c214a803a02c00011840e00d4074445054180d94841806811541d490300c40101c1504884650400d0101c1002040c2c00a1024460b5404d800000c030f069072114685e800b1443e0700000c00510b02c0d41c04504003014400543e564441207a80185070f007003103a43c26a110002214a8040e13031a44014201c1030314404a0700c03c4540b0550f4a8811000c410120140c4e1003000300000e03180e068410030741c81e41065109000c07201d00c0c2c9880301c11035001c908202c0c1550f5603d0b50146204d607121071051721541d5440fa512032000d80c0c01050140100041e6005000507400d141482d52030740700d1070400e880d901d01e002480d0000c64070203400041c03110a604000b00482503803031624203015400002840007000c600307d008141c1300d000c400600d11072a00031301402d0900703040c019058003112182d0b29580d44117903c0501526507540c1e6a0031800c52500682d18117042e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 993610179 1250 993608929 993608953
    0x20d0c150203030c1b010b0a08070e090d0c14070f0b0a02160b0301060302090103110403142401030f0609060c11100509060c2107051308010b090c0a120e 67
    0x220410810500c1190000c00c04d006408418009440126011143c002170b01040d01c81420b00518010710030b942c114003401c038002640d060205030300c02141d011000d000d019a4512441c0c0c1d4545441740e40d0703540800c04c150384290118031841e08083d64101803104452101e91192403d40c1d00c2ca23226030195801c1d440c00200b1075803d41d41405600109140152910345440c18071886d21083d0105028010425034041421000d0b07a2003600540131070100020ba45540c2d40e00c90601800b029189404449507110320f603906200c00c000c10038940c40a0001030f10750320a80e402c0d43c0d40d6402080d1004001e841054461740e41e800030a51501c64150f000d920368551140465060580c18204204070120100c00741c0303000b003004180400854003a5000c0760b00071029648009403a186400c560014149a90001d180420003540c0d60304440105540b01d4140c01034081ca5540d010041d00b41c407a500b214941240956022403200040c49014003114401d909115403099001d030310090842d0901d1742c00800c0c1c5c0c0d00c02001000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 993611429 1250 993610179 993610199
    0x20903120f0a1709100203060303071e120c0c1503140703150f060e060a0512090325120e031c0804020414070813020303131e06021b0108040c03020d0c 66
    0xf50320001c2a00c00b2815240000d00151540c2031075244c030342d48680000004403903a50900c1220303403042d4004e585801e001c90a800305000e5000c44107003103035580100c0d44580318040c002c281078209207600c890705008035070070107440c17410004040521005141d12203034a404c0301180d009407035108405d1640c1c005a00210880001201c20b203e50107114034090110741802640d40c0000b94440700607055903002e948001601e0100d4580c03040b540c40c07080103000f4500384024035002000a1034140441800004c803600342c030403210030310410000000e142c1581680c114072385501400c000e80c21208020305441e00c8104a81100b46220302c52035461000403006c00800c400c602d410310411300003007179808a181c110302d0711010140c0ba15002500840105190452040c11550304004440400c0d000701c0340051210b65800760000d0b0354400c1000000703e205402d60104d44140300092519013000d40001001500e04010300664110001801c162a2440800000b0026803551401828294414a1000e0006140070385100d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 993612679 1250 993611429 993611447
    0xe1305150603070c0b1b070b01080f030a0816110706091d04030c02060d0204081f0c0f08130c0f120309090e0303060108071209050d0e0901030f06020903120f0a 70
    0x94850001030007400700050780242c503011129800184444261900c41c10010315074180340c01b0a480c0c02e40000c03107401b004641c00c580c90490345004100c0e0303228400e01c4d40e5107840340102c25050300001c1111002910b400c03285c0100c0b503a4136109007400c0383c039403d07604000c0d41001025000000802c1e240d079810005010345a007490011460403c4402071400d2a580040c181c202c060300192240c4401b1480c0c00a41c00a94102d800800b26141214034504105100300c003c9a4140450542c442c500800740c10168090b03403c0c4012003081f95601202541c503079191542003e044041501c100710b090b140480d405922a1003c3c014005c8280010041c1d02b0b186402000d0490607000028040c2c1041c415001c41c68000080d6600030400b42001c0d15680d0340c603a02140e00d941c40c0100014034600b0b0050610500a011a0400310381c40640e40b1114100350f00414480074203401e00c001800802c81030005004910298080e0520000040990310010250203060180740c0203c0c2c0001070360f410009141c440103811500503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 993613929 1250 993612679 993612721
    0x62a030e0d030e0a02101e02070311013b06030a0b04060b0a05040b0d090605040c050a170a02040e07030f0b06100305040503090d020111070305061609050d0809010e1305 74
    0x51060390359800030346464070380d034004c000c0c01054020303104a403c0c1d000b040c031200c40b03031401c4910082c5003800300070003541d0344103610090302c1d103a001c0083c1e841c80754494400c880c04200501c10743c4015040140029050f0301068140e4041c0049442078001e40d5541e81c402107000b846c0c080b8010525001c8001004200c8826a01c007115490080000e030340d540fa0480709641c1100c4010391400c1d00e4600d034010b030740c014050000c8020301d881d1a1600b003004210a0072140000e0b65415a43c00c0701390f90b107404c03825101ca0103000b0426003561040c9891001843e0a40112281048403400c0c3d070003640c1d480d0b880b9001c440c2484003c48040c1030100030006642000c224650703103883d041ca414400c5e4107003500c4843e1a8410706440500810a4450070019640107012402d44914000c04440d1423564a007000b0b07455440035500054001104224010010300c1489440b0541d1401004003030350101543e1040490b5100b6105035051094007100303c8081e039140130b0034000c12584108041100e00d401891509058804030030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 993615179 1250 993613929 993613931
    0x110402130e0c04120f060f020706020d1401050a030813030b1003030f03021201051e060316030506090903090d1716020405090a240b03030c03090307120807062a030e0d03 74
    0x108405110b00c00c40b004e07140c0e0031201003081c0c0340c5141091005400c00e5425466150f0000607544204601540100405000400200513412540c0b005440c5420284242d6503c021420010320111390800c00078912900ccc00307602c1b054419980d6031602111902140c0350208824110004c005058101802401c0d440d45e1f480e0851400314a01c0010724171850601401d801480d01c0259004c004044040002d10030340d001304510b031070340303030004000654501c101242d000207170400000c00c5050030304090190180840f08091410160403405015603c00440c405403020701c405240d060703070b1600c1d9074010084c00000340300c0015045031500610066a00243c0300c0c507000c1e07201803c80d60100301ca40620403c1650f582150f08810601682c501c406800320710360b41503042c0400100d07050399410020040103084415070540b180c4542c0c417a00400c44103880d15020700912010800328001804c2c65009031500d00d110101c101d84503035030010f11114030744c40314030b81c20210f0780d42c10920b0347c400d01c02c2094103032140840c50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 993616429 1250 993615179 993615187
    0xc05240903040e0106120b130209040e0c061204021314010312050c0c011b020a0b07060c020f10020901030e1c110106030c1509170102040609050111030a0c110402130e0c 74
    0x3c02030180a0144034000c10480040354103172a103100ca821004084000a0066505081401f0b00500030361101400c1d51045180c00d02c01d80c8612804510038403500e000810103401c1100c00180b07040c000c000200201d0780958004110b416110303072407040e0004c01c4400003030400c5560461902035040da10030362290303083c85014480c218042c0c0000503d581817070303000e19211460100c8884030440e0b146003014000d500c021300440204001810388043c000040c020306040c441c00c40081c50a0b07031911140b103400881c44d00501158030070001c00c0d070000c2c1f0808606160001d48130702c9241000381407280710f0b41c03035124400805444c1000f255010b51a1041400349500030000c8ca841c5907204c00e01ca0002c0e204144603405100740c0440f20500611151004200c06510440101c0380c04404a0007540715005031404208561404a100e500c80d41000450301012001545801240c210940304c4a05104044514409031001c1e0f41141e02c5500180c0518010101211000d60414241e0101c114008010800185040c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 993617679 1250 993616429 993616439
    0x2011a06161502040b1602041b051227030c0606090108030703080a02040b0c0a051009020f0405090a05030c0f071d181213090c210c0c0524090304 64
    0x1080d5548107640c40381c00040302245001d141d4001e030080da4484c190320100806d0042103400a1104402d00740e04c2101c040010360b01d07500c0c1440d14007200e203000c60005001444000720908405556581044070180c030701e0307503545021002054000c00c90510b5016030b000402c040d0002c03241001030a0700801d04540d0170b00c031581072220f11540c038010304c00c0140c1041369a1020601c10219581124050100119a15030b40d80c0d0310002a603036000c514404460703520401d9008c0c008955540315200c22f15500400164110040c081084007519010b401c2114501480c5c4100d400140708000520030440d500b0094038680f00c03900d541c2400d001c0e90b40e0004050703481a101103512980c400310340700c1c3d1203200c0002001c44c80701c42c0b4410318504540e82c0c88281074007500041110005c1e40090784202140c92441013803058040325081101e1501070b5807241c090716802c041005918541503001000504410300c0c20001c6818240c030b07928036110940445074803000082540b11440189102c125500c8001d20300114507051030b00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 993618929 1250 993617679 993617707
    0x307090c030f2d0209100512070206010e04080904141503011518090302070b0412150c23090402040f0305060606031006140903150a0518370302011a06 66
    0x100e482c20302242c00c03030015000c10700c444d0306480c4105406460341c480110681c40260066011005503101e441c82940050009480001d076a030580c0c900c0c001029180c2c4440e60740410300d8000c0751005600640b00c0c610303141c4070117031050a140b10780342c500030310f00c180c0c43c0b05011b042c21550f9240c811102086000401d01190b0040118601100440c403400101d800d20381c1012814801a034000b5002448002000995180d072100350040381070041c0020240403c41103408002c07584405a0640804d07082c141c0980c88108101c60305040c84181801d80d860805120300040490740541c11242030048800014014007070200321550f030050090b200e0503d541042c0280b003148003e607204880420200d00084e50450b0140d5041d5540d018002c3c00722050b010010307440e154544021607500d05540c1c60306c4001111406290304403404041194050312021405003044071905800a40701c6d406030380c201441201d0304031880640003066000f540002001c001a02e1001b081040d0301d119035108180500040c1000d59403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 993620179 1250 993618929 993618971
    0xf0b040f0207031403180a060203070801090e0c090a0f02070f0b010b04180510030b0f06010f36030c0602300307030209130608010c1206030503091e0307090c030f 71
    0x82890380f15241e82c2c0f50040c0802c01040c0d20718400160142100c001e0230052103801940c042c11080e16559040c2e80c030383d2240001c80e408903203480f400754024260b82c101802c00170501900038a000c800891204507401912060380d00102d000c40b2158a00f00001c01407040e03115031940905108940385150030300c7c06401905890011480c0c1d44c416503148045030a81e084c610540c4000e44e403140210380e10380360411510007816001c686e124049035040c80502e507214480d441c950440502d14002020459035103180e02d01c481d440c02c681592041d00d11001001190509a420006042c00d0b4010450840c007000c2c541c20030041c4000d040da85111440c0c1c00c000c07042a26098076400318980c0b40041e21008040000b4140001c0758803082d90b61840d06101207905a81074010100021803920744800741c0e0701c01071003202152481d10019080d80c1041c020b0143d1407030200d0381c9a2003907640d40c503004042c00305100028201042e0340d000c03282c040d5484001d20000b68040c040c240781e0b4694410700f0030500c11308211500c09001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 993621429 1250 993620179 993620207
    0x705040518070206061e0d081809060907050a020f0a080a020d0f05041202010c0f0b1803030f0103170d150e01050f090f220b0711070311061b010f0b040f020703 70
    0x6c12906032400203620102c0340748a00c54010001c40311400641401009a4000c103100240d20ba0030010544241c208286c01e28050103000e80030441c20707030319954212000c0d004600100114020a0f0900103010307020001c20b05160301070710403640d80d0010204040d2a009004204105003d14998441c00f000d4100b000c0d9003c03112580030b8925054064801240c0e44280b641009018220340d078090307410301140e810030305c0c880d90107103240d9820324500000e519502d00046640150702c02d1418018030004e401341c081034603030000e200082400e140c00801c00c82c0c01d44190a1002c0344041c10300c0000c0000b00ca00700c3e03020307004040540e0000411b80924001c00c40004009000f00340c04500034010800301410070384203813100210000d03840c0748088035240000c081d80382039070000000b46200c8030b81015510041a0791048a07800688600da02003c030b0144034940d00181c40488050560005445040200303015590f0300200340000090510410020001201e04403190040f0780c5105100e01c60000f50004d1520320000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 993622679 1250 993621429 993621439
    0x40b3f010b0a090b0a031406040902092a0708030a1427030d090f0b010b130e0714120f092a030307080a2303060609060a1106070504051807020606 64
    0x6180c1140076a8000f02c00e0f030080d142d00783c00284145078554194099003200124480d000c00304d84600041006580a00a002e0f602c030045102141500320b01150f000042d60340c05810018550462207090240e802003001901c03072000000400c0703121289880368040611507285050050b041410040541c0c0c0070301c1e02407080c0145c0d1010100c07000c1e8420001c0e1000600502c1091158840d98036107103082445500d0110341000ea0341c8008520740400b0410750b121918454030102600749000c10610030581301804072400d1102085180c0d1500b113103100101b0042c10407140202d264103001d151501241401080020709030484000c0942c2d803035046940c2c000e090000700c3c81ca90060501c800280c01c40c800c0000003400001c00003244071601d07070000e160702d07141c6070511030000c08070562030740c202c249100444401e90b010904105d4180c461805501074420b01c400351906203030480e074040b940c40c80e1060640342c4002085000c50b08020b070f440c24450a114100d0100d0210496080c04134004c1d64030100034000505c20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 993623929 1250 993622679 993622687
    0x5070305090f03031c1d031905040521060f0f060f1c060507081513050414011a12031207140f030f041709010212030a02040b3f010b 58
    0x265681c80c004070742c940001010b8a60714009040e18508040780c00d10441394450801e003c2d6038060003c1d181c1d00090707007030341c101651614040180445030355050030045010301c0f809020100310b0f5102e000b01515a014034994042c3d441d28801540ca181c514020301190307046034002e041240746090000501c0c0c020001341d034150040c1032101c1c000b5481d0062001170080c85008081e0030400e211460708803a0007440070b522800c4c02034441000c803c078114030030138400d074000c6d54207003802840103101e0307000c07903449401211125820020402990309403109448040d059012510f811030315407800d0b03030340110305521070300c01580742031000000b850452000400303d0003404185607450200c445420110380e601d1072041c8840b40c1d03d28100c81884c500001c1030320b0a5800804040360881c1c00c05080c8119120070340140c000380309440e6010a0002190700040541382101c0d002d100c0000d840e141c01d409070100342c1c18044900d01c29442c0c0812800d0310050b882009504000364094402c0044d1401c11340d5040d142d48400d05643e03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 993625179 1250 993623929 993623947
    0x610091817091201021801030c020f070e220303050703050a06030b0f040f0c0f0e060603091c020f100b120d1407050705090403021e0f070b160507030305030906070c0305070305 77
    0x41c8509043c6a80304039400022a010440c1c440c44120036110f909803400c12441015400c200d030b507120340328108481503008442c203001c00020300b00c105501028500c0340000b10450411200d070380e039034030860071008a520b0382c003170051050f0140166540600355800402c5402c1c0f65403a5100c00c0b40010b0103038408002403001050a02120008191900d074010800041a540d01c075981f0401a156125100e10102d402c030200e00103181603001c990c00384121000800030709a0320340454951148540890080d4860905110742040c0c00340040b10f15921000000074014645000f4007403000308501300c1601c590001003039440a9a041a48100e105003100c166586407420342c90300a2400c1101d412690b4040320a8040004242e40011010007400710480c03200070311b941c403900c6c0d05e0750745603018445401c0790170512080c80b459038850007906070564864002954041d0644855040040c03540040c0c0000d20000104407205200f00310180d008211807400104110640c0c5005059009902004041007030000301008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 993626429 1250 993625179 993625189
    0x60f170c0904150509040c031a070c11121e06010801060501050a080c0f070f050c010804051902031606050a2007090203090109050601090b030705031f1508061009181709 74
    0x8040d04015017240e043d0306260801e1052812a8442100c290240344090a421046401756a0080c20742ea02c55811078161595207d0348e105020341d94981004402e80d413401607920810120000c8010090380c50381c0307551010301c42401c0c808141c100d4509a8189801000360340d03800021101d40c01b50901c1c04ea0059210458900103134400c203803079484140004240e44d42031110050700d8148881c0b01c3c0c02101d50f038003e45070054458000850300904541c1113410071b90182000700c0210300641d0710040985124251441580100d00410782080000950200340d60700030640100242d081070359022007078444900c91481190350396807140a00c0e070760160003002041d117040c025045941c00b154041c003640e080c1d43e110800b0400400700c007001503229204144000800e070401048042c424546404642a42480c50364800050107201c1602c030303415030303038600c000580304814402d40740600d900c801800d401520f880114030660b00710100341706040c00d08508100000d0001d408501031030a00700c0c102900e0b0140b40b40058 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 993627679 1250 993626429 993626471
    0x2030705040306060801051005040b0f010806040908040e0f0606030f070311040503032113020102032502030a050303041208070c0204090816140120250804060f170c0904 74
    0xd0203d41050008110450190851781c42903d01401000c4940e6a402c204402d6810040e0317000e41048c02d81040d0f4507207511800f501c66011102800100d4500e5403a600c0c46c41903070141e8400100c85c00810181f0105940d41c912461f0070280c1110300a0440c01c00711110b030071040c4007800c00c5041c150382e000c0321540106804150340080c030f801416651110030400c070758085407544245440419000740e0012b1596000003103a00c5e100c94069000718200110a5448854805c03265034840310708808001a50040c0e07410010a02018424030155859081ca4a80b8040a041201e00203091001c078008102d02e45500820903589150111070100c0e602c9502d09100c42c1ea4803a01040d00700880c14280e00e10300384089540c82d09240c50701a0b008211b4880c00c288200048124400d16203103441041001d200101701c07803003c0c01c074110704120254155920541e55199103501a910900100d00408100c0b20400d400c680301d80403094400103600400d1802207151b203420b00c560200503201d16070b12500030040e04038036132400b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 993628929 1250 993627679 993627683
    0x20102031207230d05010b1e071104020a090e070203040302150a12021b16060504050607051204090905061303080610050c010c02150c090604030b1915090c0e13020307050403 76
    0x100403040c40940c0700306500c60341018100a0810000084074040c01049a40080808c0848580b648805800291543c041034003950781000c001d0070703440e080c0e98a1000b001142955150f80669a2a1250301d90b55800020600c40954009010800260301c03044065002054180b80284e624415a0810365416584042c01c0c0680361000c181602469125031a2055002c048400c4030f1400806410300c00d00b020440c02041c0000d8000c1c442001941402c02c040c00315640b241d401c1c2c42e18803a01d584d42d100e581d00300b5404062141d40790344019090200038808950814108110300c449130441e900c024007440b4000d840c0a015801c4100d003801150311541c107480a8442e008020b001c840d02d0700000035550031198100020080014000c01c1010070038030300301c03184500050589410207283d0f440701d0241850060030501d0701d8074034240a80c007030036951082e215909440c05003800d410341010b1400084909a100c040180714400901001c40d41c0e0b03042c400c80c0c29407448000540e4030382d03e00004503030a000d03540c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 993630179 1250 993628929 993628967
    0x406090503070f0317211807051509090c0f0309150f090d0f23070c15020a2306100906080309180402221406101215350a020102031207 59
    0xe114140359004219150700171f003401120002c0f40c0310001c1024442c0d114520506091041200c90303070038140b05039041d0b80091a040e8040c1031050001d0006615402124031414582044240d10400f4124090365504034055900e0b0b8041c91404c084940d03512910200c1d10382c00c0c80700744150600d10a224401c0e858110a0801180b048011850304400d404c4d04411011100e12444034008906040f1501c50035032650401d9000b082664115207500402e0242e14a90100c40d030703008070010b0440b1104105850080001c41c00b203840e42031070039030030800b1a02e00d0b400c4108140c200300300c1034600343e0b990f04414040c1440107034409225122403002030350001364000d41010403485c034102d140f03085505520114100031032156600407543c50341c0c200b05074960b811070314502240c04007848000c1000036900a406481d4901c1040c04029182d107130142007520141c0810044801180d000c4029407204284008041300070f10007811041c2080e40041c1d200d00501c1d046e155003088600c0015820fa200752a0f000c2d203494001c0c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 993631429 1250 993630179 993630181
    0x81302130e1b01030b1008100306052401020106140906040e0624010e06040b0c0f100617060f060928090302010c0c05121602060406090503070f031721 66
    0x4040e80b920341c108141c1400300045140d00d449540240211710311200010b00c1000719100ca000180c03079060340500000c3c98840d54460100000e009441041e000c0c1040126034040f61401468503555081170314046811a41046010042660b0400204894240c110b4401415a81e00c00201d40101900c2c01181424403407082171102c51800c121a20444c4580240b0760f034041c043c0000151540d602107507901c0c0d00100100410030034440c440d0701a06545010750240c03210181c003407803800e1604050349200b8a80342d641b90001c2150000b00d451141026084001034441c40c901100c41c489950401040c0c94000d656038000500c1d400300b070200c81c03081100074040280707011042e03100c02001807002d0801207001d90321305410080c469005013220385105034042c00070f1007802c43c1a1a15011600980c507803c08608400c1d0f400e800583d034110107400504995602c9507220351400d401c25113440da81d6845680c2212080009201080c1c0055118040030a554102c55030350842c0d40090b42d0080b40381c9148101943c0c0c6c2c2c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 993632679 1250 993631429 993631451
    0xf010306060815040902131e110a1b0501090c1716030f05030415050909010b0702030a080a110a06020d05011a0a0c0804031b060f1107050904050f1b0102010507030c08130213 76
    0x15103e06100c0c038902503144410326120103003c044400010949e040c1c040140130805400f880740f2804142a00052420200c108840e91241e0035140c024900700d4241040384000c2c058240c0c400c601b0347c1c820700000d00500d0030b11100403403030718034000c0c40c040a0940155010190180003040045070010030a103044460b030001c1000005003550071005441e4442d0342039000000303041141000788c0349100d400070003500b000f50150751044180e9001003a4002030051240807007407452000e01c0010040ca000c0c400140e545d5115021040443d1016001385440900c10034144042d07403100016160750f0032983c101003802c29510f0500b1002d45c01140e00062000c0800c404810010050b03190000442c2c01c80c0d11424000711500d28180d0700702081c010080b24a604c03a50041100345410001c5c0c0e03420900540503180000650b013422410501507180e006100d0030745544140107943d0900c10b680d444250380c6000c00070f4641d403e1000303051060152101c1e0343d03110011102c00c19503031485546061070f010050200450740c240 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 993633929 1250 993632679 993632681
    0x7020a05092e08010c0305010b090d1407180c0c0f0303091a13020a0e1b1602120312010b09130e120c0a0309090b0a03020d030c0609110f01030606081504090213 70
    0x103400f0f00c5845500b49410100514041e0080c94141c0d260340c040b050501424009000703000d242d40006581c01d40c50030981c0081c2d50001d1010001030b02295500c03641401c02c10b10507400b81c0d018401c041003084406081c2c000890007451800d61101c4d4185000325990005040a0080314441030f40901050002428000007a400604520102e4400c2e1031600c8403642ea841d065a64060807503000f1941c111030340d803c1c4100c4041800030401031401c442c46141c40c0b103503a004a8148510b4915030200307076200203803140781040c022a1203401800c0340710000e460300d0501c0780400d620729940c4414480c2241c0350390031040301030021b01102d601c41038200035031070f00c030949005520f54945800300c0a5002c01c503220000f00381d40e5818080c482807540080e0820501916607400e0010612040304142d04018111101c00002001402040302960050303d421041801d41c50800000e07c1c620707660107050525081c170070070400313801000e0305600507200d00c00d803a00c080301c5c1e5022401501c03050390025841850000d48003191101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 993635179 1250 993633929 993634021
    0x90120010513150b101115042d11060c0a0f0b07090f0b18031005091501120201120507021002130801061a040e150303120a0e0307020a0509 61
    0x14003880703006010040e189500b1592074010319074100c904000d21404250040381e0809511705100101c920300f0034410780c003107174014048c4d90480700d80500402207030400d2803040c0400c454042c00c040c01d1080645503078911404030740400d91180a1100815650b001d200c00b4090115500c2d00003a41007010441c1c2e180590300100b00312244400700380040c002144000030304032008141c5001000c02c83c0b4061017844400002c454864500d6414828458002030500b034600929000c0c4082c0d40040040454004c2c0c00340c401caa058100300d540416545081e00586c2c1c0c41110801d80050703c1354006403d4961190072414240e48040d140110742c0001021004030780340b00c0302081126090f000030001c264644002030b07120796a807082c88000e2072083c003040c4034046001c00381d160490b501d031415200803420760300401d04641012901d0002089034008200c00e100d040c0c0a1003030004902c00c05940b4060349a40003550b0300d02d03c1e009030350280c54200c2c002030040d04042050300c61641d0940c940361242c018a10a0101113034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 993636429 1250 993635179 993635183
    0x18070e01120b03070b0c01020405060403030905011202030c16080f0f03090607090b04090c2105040506151e030a06050115170411040b01090306020d0606140f090120010513 75
    0x64120320095500124801c0d00a102c034000c014000d024508400014207801c401c1c20034100c3d560802c4001000d50742c42001f000150f100b0344510000e180703400c0001d0000c00c104010000106d0040040050141c0030f5022038041168040f0040d0380c0210a05080701940039112032144e0744400026803968018808000d14401d0380c4807021101a40d03941c0303004403401a868415a090750324144403d200c08040382e04101e1194030036140400d00b1608010103145490b00c04051501520794400a000610905006407540040c102085030807650a04010600d84003009002501c001d0841c1f82245040d80c2c02d001082000350010024810395071509540d024084840c5d4030240400c04c5501c0103211005244411445160065810b11401d80390105200103054001e080a0404c00001004400105c107031019180d41d0503003210000e002d505180014044424004104540203005e0040080840502c401c840e0840020300e0004c110840d105c0c900c0411017800164068036500380001c01411044500448070380314 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 993637679 1250 993636429 993636437
    0x131506051b071a1b0d0c030216140112140c04150309030c030806012d0f0518042408060f0a05160f170a020301050312250218070e01 58
    0x501c003140700d5075028980f01d291022060626090444408078001c0c001d1414200c2c3c0c0351992010b103800142c10408080d0084011030108116030041c50b50411121950840d030407030031301c0a035040419440e0014041030314541004100c5800c3c00d250206034026803000011030056150904210380c00e140645c0060240c4140f0401e0040c038080ca840c0302e07004103a141500f5880c0e842d16401d06880c200c520341001441e450500070203580b00003560360003860358400c42ea00000b101468000b000001403081d10700301c07524402c00c0418002c64012703800d000d41c8034002c40000c88000803405040031040358000b1055000d0900852141c40020740488040f680354030880c068010200c1d5983d82612200459000750303a0b02c82c841030841c0c043e0705d9a81c003e2000305081c01080c00d144074001030309211510300c00d50840754007100c19000b000401c8241010080381c1217603036004003440d090010707191110340354031840c0d00015010a48070383c001c401d54442011804006d500030382d0a01d19407800100150121030940c040c14001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 993638929 1250 993637679 993637717
    0x261c05061e06031e090c1e03031c1d07030b07030603080912030f070515010603060e1302040902090103060504260702040b06300903031513150605 64
    0x20745003041c50000c1d050307003003912030032400803190902201d030300001d01a103032607402504515038054424035142c5c80b6031060001060410840c0c410f00c0a000170303c0252a28489420148200d07a03a00403054980d00c0d20144540070300e28061208181c0074104010180042803064810200020300108015096a0289225002d980c0340c03408110100d07400e0b0b02c0013805060f404d024400303580c54110000e114001c0c01500710f900700020b4207403182c03070b50340b25004c04c40741c5078440c03d07419640c00d88602c20603006004500b81044958a007080480c1039650090000b0a85d8a5070800c40c421907496500c20307042039030080c2210100e580c42e0300d81800103000a8400383c17004007403000984034042000f00140891000200000d00f095180d0742800060400010103551020040c0021040b1101c0321507221510b130940310080440c9034042008040c1c01c2c0002d402100d907600100100a802c4610004500c5020b00075501c0c0220590000d0003080101081a02c000d09901501800241c40d50302c02c02620b407148064914005c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 993640179 1250 993638929 993638941
    0xa060f150320120f0705090a14150408010209010206091204030f03110a061d010b130b06040515070219050d080d020c07140a05010516020603061305071821261c05 71
    0x19000c0d0181d4540d11400423841480301c2d4452482000481b14050500e04442d070860750100f01c0c98000350400003081e940407407081090369041040b43d80002600c1d0242c003d00c40300348000b105510440c00068000241600b1000405110300510b00a80c0d08501c2510842400707464a100907002d000032481010000004c0081996010f2190f40400a070041141031080ca1380d00100300500ae05140e4640c0c04034080c4000079243c1c40c3c0c3c0588582900200c042c256480c00c0501c1003201d8654451031003581041c00380b0702803000c1c0d200c1940070400282c0143d00503031030f0414541048040c0c410b0700b00c035509501400000043c50008007942d8028840125405d40c0095156001110b060091042c1c007021808040c070f00710301609208000307581103030010300480c030b2503400d0700509001d41c1e20940740a00000c448d01c001d4506490700148000c060311500d50128151042c0c0e0b83c41440b2050311100182c65000c400000e940346d10701e41d540708038030702d002d5094107606c0d948180420149211165808400f0a04040000e10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 993641429 1250 993640179 993640187
    0x30c09080d09060e0a080a050607080f0103050a080706020d0c0801170a030813080702030d2c0d0201030f060f0b04230102060408070c0f0e0a060f150320120f07 70
    0x1400c030710a42e896011a901d881c00841d0307480642c1c40070035084070760f007107000c68842c2d0280050000e05d40100c00400b118200150010409880204241c05500706640140700140020861585080d004404e20761210818103010000b84030744001e1880039490003281301481030f0400865412500d0003411361981501000501e0346a50306500028001110440001c1c14100b01c042c1d0581464001d18049003480385039800b0914040f029075190011074840301035603000c028400c1c450382c3e050b8040001d42c40066110000b2903d02d030b0820343c000341410303112844160000c8656100d40010480503172005180c513035400389600c0396449400f40d14180f00000703110310101c40b02118194081c95046e4020413141e0307215154940c0c541c01a610490f0074660440001650915040780e5402900700d80c82c102e1117038207014005204480c0207521002e000c900460003001050b401402d2050b50001c1c40c1000301c1c04107a1070005500010b203176264031910081c089403180018445508072481108a55041086903c440e1402d0f6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 993642679 1250 993641429 993641443
    0x5040303680c2805011b06090f0611091c050c09100b0a0305090c0102010605031209120609010903080702010501030b0a020c031e1e0304020a05090711010903030c0908 73
    0x50020145051100203a155168500500703040301541d034500d0360003000035800540080c0444050410403040c8199440d2103440100030a0700742003d003d02071801c0e403001d01003806681c1c09401c50380c1e142c0400080c07000e12504400c1d020382c04401004095589644542560002d000040c01503c11001c01d80c038030341201401c0c440ca207030494000e250030401c00703040104034000100181c42c1126000000079082082c07102504030307800e850302c0c04200703480c10030b01d6545032400600c030700303070440e81803a00070041e6440c0841e100b94006075032a00c003551144586c021034159114451266083d10501040000041043d40407a540500c00d6896184640f5510004c90a8540a0001410098076070000c14045095a0700401d401034560043d2403c215400c3c0c001a2a864852100e01c0300c03200028100304032209001d50910410701d041c85035411410646c005c03130a0080360b4000c0c0ca0140070400e0115101d14003803021241204400c0000740b200c1042890000c0180180044110100303100c0e03803000c6a10301c0042410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 993643929 1250 993642679 993642821
    0x1e080304090903051209010605090618070503130c1203080f0c0d022109300706021e03100f0506030c072013060312090302100305040303 60
    0x150308007400d10321990010300b4441c1040382030120400107400d1920103100800e105040841c00025860316003000d02c04034003c000c282d50311070b50008410580e0441d5a00d0300c00d40054883c0703846a200d46e640340500b010403642d4103000e00340311842100040c0703e00b480c1004211030f600c280d803003149a840b01541c0582c500f80c00e440e8900c0300783e400e0140401d0145268040c054001486010706100c0d4000c1c0b00c2000c02c810156400041c54200061603985111500340151801d0030114100369001484503044605000c1c5000050580350005114150f02d40186403034040e0704691299950b4a061044180c0c12103c1d1510030a07030741e450762030000585450000152842001d42036030107840d001c0990b5480044a8517511000b900b00000c0302d20940d40d4a802503610394041e007125000810701d0441c200500e0501c0e44501140400600050070300c01a00c580124810402c03842c10089100c2d2200c3c50260040c08902001c10000c41001030711044400044640c0c401c001c00291100c42c8238005180c4540c0c0d5102d0341000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 993645179 1250 993643929 993643933
    0x10809060a0c022e0615050a081f03051516020c0909071706090106090510031529191a0703141c051e060f010207080a06270f0305091f03061e08 63
    0x34a004042c0142e6040303501942b20424042150710030744254034154450341080d9010350000c110403210305001b820280c0c10401c0c4420442c040e4050b42c90082d6140110440d07140120050300100b4000c07242004a00060480c8003044c0741c480b048055040d03a1180d04031082e140075820705c800011800c80034410140100c03028071128a21604549038000304050000001c01b0740c0b41c2e19a00303580101141c0055000c149444905040402220803c1180700444a40d01910b05918032104000811401340546030760b10701c001c41c2940f220050300f001c0d540280080e4607050f00590000c1d0421071125103d1412240d032814203000c00283e150610105c0340e0445410410321901000b401180d1145040400c0f07070300350380d014170448600702c3e1901103060a00020102c2102c0300e44e01e407081c0d6001d280280e00101510101003040c0d01030008681c980c800c25006441c0041c00307110000480380c000707484412988145c025550080c0c02d00c0f201e16a00200242010b1103149942803007140410001d03964490100f04031040640 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 993646429 1250 993645179 993645187
    0x10504050d080108100b0d06051501030f0623010c060e030715020309100e071d060f010c0b0403030f180f0b0c0403030207090c02030714030301060e010809060a0c022e061505 76
    0x174079400401756080701700c0d40000e4034901c000c0020703554002c40384901041004c20744400c612800140a413100717062007202c441d085c08018088000c0c0d162020a05401442046900003280320040c2c074101072150b0040c00305404c100880200500000050030040e00c0f80550701002c11504a01c5000c900060712102c0440e00102d146121b01344280d08588034003104402510400c641d207a00001700004944606c4440901e40402c2060a1030310501815040d4800c1c00c021700014041c2e030314803130002d10051005060564502c04005550125804100703200c03212130309081c1001450511145e28616210115013101c03084000407500c072880c0c0305030340440b640741d0001c0001e2810000f00300003800703100914004500c8140b00e0100850a08100d60215004400c05140c1e00d505200d801000c40c503244120a06010018081c4004a400001c9540e400780402000240a11400800301c1c1000c4e0200300440b03809883c011400403610822032003580780070404000b084141e60b00e28141c428520124801400310310180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 993647679 1250 993646429 993646453
    0x509180d110102043305030601080f0a0f0f02091e10120b03250506120426130f05031c0f18030804031211030a0c02010e060309010504050d080108 64
    0x50388144240d01c00000d820710b92640d0541d00c00407100c02c46884240015114514619a040c005041004a9117070041c90b41c5000030001e05409005400504200710000c001504090700b80c3c0308540c002c1c6841810301000701103039070900103900000072080c815440d00e0809042c0074440b011142c801d00000d0484800c641c02081c056504103410010041811b8440c2e10854441e034050160300e6401126180c101d403119010009c612400095400c0240690001c01800030804d01c00700169074800c0d0311400c40000c0703100032041500807901c405c41181c44507401140c9a420310450900000643d0350300c4e0308100710999904205952400840401c8a500d4000c3c11000841380c451580707601000f606d03080040d04201040034001106030168400d0300e6200000c10140208000103080780d400b0b04081c64507010200204807041e0300d0b440790014400620244000c08821640642c820440300c0c0801010070f80c413458241207480c042e240c111422a55400703440c40013000c1d1070040d10000e0680b00e50500810f0f04820300303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 993648929 1250 993647679 993647687
    0x612050f010b0702060c0d021f14040f02130c030608190b0c091c0503070c05041a1003110304080d0c170609070504080f0f0d0302040b09090a1d06010509180d 69
    0xf0726000d03030304041d04001102c1654401c0004040042080e03004158190103201180800d613007610300c110303410382030041045080070020b920381d4025810080c0721140c445c0d1440040c2d004000030b0082ca001500b0006584041501640142d041710074040641e441e45020b0105100d00180f40040200509000c9000c201c030010b1b044040c14500c04050903580843c038030424410b000040b80d4208464540c000140c035410407803070703840741002482c0950b01400315001c01c03071003141d00000380e100b6240558100d10000903036601c00d4000802080d484101c05980303007000c6c240b00c0c00c2c40e400490310440d020f0401d00c0400c0c256206064040846000343e440741d11503150407003003000c0d0b283d010340104200309040c0008192036000703002030581014120024400d41501031012400e150300074208400340752041c88100021480c4100300c58282008a880500c04e84d5804081c6005040b900000c8990500d40e6803030450b1100c001030f00c00e0580f00100d6030412140e60b0410700d44901c84406241d00c4a94003c0a4201c210a001d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 993650179 1250 993648929 993648937
    0x3020406081212091207060506041b120507210b040e0c06180609060a121104440304081501050a0306050603120c01061a040324090c06090612050f010b 66
    0x10481c25505d000340c81c18412446900303c000c0540d5000c0d516020f201b0b1034505441001c0200c60b800d00c1c24400ca1b0758030faa0281502801401400b58652500c00160301e403842a60051844108422405201803040180c800286a14070260f8001d91410100746042c5d000002d01c20f2003000300404492074a60040b22940102a840b12843e810010903c10005240e8409020b0311a00c641c40d512140c003012098051001ea55110701c18641c0404100410702c034040301c00e6143e413000816185051158640c81d004108042614840b241005050501c548508100480200102c440030383c01c8a142e26006203a0750b440d40c100b03118840e0700071842c940c10000101660070455101500400365181c0b84200140d2880c26803040c10380c4a282d9545420510101070040061086240c1213081d0038103040c01c55884d940f50040c5402681408a04000c84200071301054200080c17156203e003a541c0b046541d00c1000c1c10344ca12900030580401c80c055002d03019159513218043c41000485840c80041e4680b60010272030b43d01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 993651429 1250 993650179 993650191
    0x11409100f0504050607062304050c01110a020619110705030307030c050316110112050c091903050d0203120105060c0d12022502013b04140f0103020406081212 70
    0x2c014400021503503100409045014092000401c10800b0071280718105003002d507115a600d181c1d04148000700d0310000c0c02c96885070083c20904050700e641c4108510b410040700340258007010000c1e500d540b0a140c55959154a030b00c60300c0c1c0d03000b44040000c0c441e485c0c1426018668240c4e00500c18980428802ca20400041d801141601d2800e100d02d50a441206018041501e00403035150842019591007a0010f402080c10101005582000302d03070030310644030301c10403607108004058240240c1450098102d00860b404011501c40d01e0340b411010b5280d400115450b21024500c5000240c2403c01c40221100008190090000c40c42d841c00143c8050304c016400114555082c8001c000d0070000701c0c200003841c140d21a4026060446100040c107403c14030700b002d04101c50348040c55810068a1404c05180c109581c00c0803011402e00001c03074001d0450a1340300f00815403140901c540d403501c440c40341c0c0c1070301d00903202800b62689034807640780c0e03c2a070071042c4410118200440c0780c814203881c1c800381e0090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 993652679 1250 993651429 993651437
    0x9010801052e050f03100e130803040f08250605010f15030e01021c0f0c050f0304080702011e030c020d111203060f092806050a090203040c050a080c011409100f 70
    0x80c6034140c0c1c410035081220101b801e000362207428881410340020080d400046000000c0c078511595440c1d22040c00003410041203501c02040c3c080401214030203a59203454904143d01c20ba907090b1402c9481d0b41c039107142c1a56002e2a04001140000c610f1440b041501d443c8080300d00c0005c62400d0440c01040304222098555500b03000b0340204400340600c3d00b00c178241006c004036a00449210b8001180c40a003030000621004100d112a00b514140649a00c1038002401540368140d82c001a111500060503ca40e01c44403c40180401501036100c0d003101c5070550708490610810800aa0700d1102c0c00d03030424642c0c1d0003001842844c000420007140e02c504090701940c00751001c079021807800c3c041503507000c0030344049076000c001e0085003003052901019a44014456103140c480441c00315192070145040031034000000409008151003103074014100600b0103107050359102d140790745500503044a41d0008002c1581800d0000c58070f025075403081c1000f84449089145001c0c1510325034114240c0c10240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 993653929 1250 993652679 993652687
    0x90607050d080f06030316080a020c03070f230a050d110607080c06070c03080112050307060204271401090902040b12070614180f0307080d0e040c180902180d060209010801052e05 78
    0x1640f41401850001c113844d563b501001400d00d0405900c04213243d2205100202c10301468a95139161070b03850045900a4601d100c02000505124807007982400300036400c01c400140d1202008410f034002c2c0651301c2d40000391004e07602c0b2008121480485a04080c000501c8800144803448404001c9200a0b1280c0308480c680322080d0b072a0030a9812030740c1710490651155100c0204e01402d0304504030b03caa1403103c10004000c01450502c6814018001c101c0100d070f0703c0e01010115195641700004049004008044101221807a9a59095280107450008400c400d0401c41201070f0380690b0100c900c1c3c81c941e00400b1030242c0520280301d405101d45c5625100c1e0000c0041c015500344080c415582c09561481201072221041c803040d9603d91102104010001d14050b41800040503400b003502c000d4140580d4900001d48d000300360340c7d9450103c550001d905036002c0b04001880d402480c40325003e8075920382982c0d90f503081000d20686040b014032001e400310700d070b0344880440303107031818095520b424841d0030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 993655179 1250 993653929 993653953
    0x1e08010b22060320030f0a080d05150d240207050601090c0509270606124b0a051b07020402040e130c091b05090607050d080f06030316080a02 62
    0x342004c0010740e6000360302444141141810300b070020400210031a401801d00310a141d0701d00800744218001c4121a03030340e660200b180407514201c40c4408810040c0740f104071586a0804243c064000700080100300e8144903a98401d40c894000d44580b41c2e0001c01401c00c1c2d0707107001044000b41c00c4003080c50342000410814005181d61304100c003850f1089643d6254418001980d44102c020000340c001d031b1084005018103100f00041c500803030f600600c4c001c0e661040100309005c0c42142d00b4a000013079600030b40c104c04115030350005080d41401c604d034401880103c2c0c0324810b50608540c0706542080030074001007405410790902200521005201a03c014907241e5140b0b0600350004099030100000101005031405115050400340081d0039803080c00c02203190383c10041c28070f81d000031503840188900813030380310001e5888100f80d030842c64100c0c05171140c815006400810b189821104041c01e06200004034900782800000d0300c8105540101e050703880d0403641c64050703994105180032021803145c2525160 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 993656429 1250 993655179 993655193
    0x6040905090a1b0806010504090f060b18070f020601140f060f0f030124080106020c2106010b0301080d020a03021930020d020c060f07030512011e08010b220603 70
    0x2450114121143c6030440c1400c441e81c0c14860180c2c400d40c4500c0c00d080c41c00740816071290007044031690044000590a111001080510381a151b0907030040503140c0402c945075800c07804040411051f50f00355855680c03a4240728401404920105400c03456074148005135040035401000c030034a50342d039060b0828102c0d41c0481015402600300400703c030102940a140c030440c24000c0c8101e00f0150a00031406c1d818400002c1d41d80c0c0092281d103208004203000382103d00786110040000c400a0401d0f6000b640c0c4440414030580e0080c0b04820080c8910751421003060310200780c001040303a0603030180c040d40b070f1410f448145c51020440d003902d0018501809120300307640701111100109580c8401c40c3ca007020a00c000e410198440e5800b011b40d00628000034840ea1030720102d03541245047c0000d6155480c0d820211154028034030800c2c40c0ea0803003000854504801c40d4004440300c640f2480780116178880024a09a81c1052400354001d95035480090728501451001c5600812007100002d00a0f52a140e0b02c13 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 993657679 1250 993656429 993656453
    0x2d03020c07030f0606060306050d020d08030c12040f0201020f06011409040c0b0a080708010b12160c0b0f0615091309140d080f0c030f0a0c21020a020c010e06040905090a 74
    0x844c42561540200a0241c00d8060706000741400c45246224440d2a0017040702c2400341440202680700000015103883c00010a840c0110798a441c00c05071403a0518084011404016081c0e000d48070b031555000c03055500183c0e560681c4c82c0d4100400c42e0841c0c0b6400d00070740c0708028108940b0450150b10205422440074050300039100c8aaa5201312030408050141904006800199070104204a08400038818040d681d070400c3c1d0440f0500e100304100c10007121346042c000c07402840e4002c41c005104a2442e1420410301800c0c04803227521480004e0b01e4400250310030380c3d02d5941c0000c050f82c0300c0c0f001d480840d4084400d4900950500d2405541c8464450404c60014440d0022038002c800784034180c14142d0f0311581c89683c000c041032450400030040c0300b01403070041041005984400d007003000326204c0c3c4030f05980d0046454020480350341c0442048043c1d08440040801482202d101405962103501ca440c41e00f04007800051030242000c182c2c20240078010a10301030740c800c01e002d050000303c480e003030300c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 993658929 1250 993657679 993657683
    0x90c2c0402181e15070602040b0703021c08012102030106270b030a0201020c13090204020f1c050106051902150c040302030d0507111017090d2d03020c07030f 69
    0x40c500201590100184030000c1d1081407100c6504483c1501c1c90f4544822020501042913680d544460f12440c2280c00b038400e03604014103115000c90200c1c101500007400b01650030307040e80394039400301343e580048440000c244203d205103104d43d030b01212905800c0c2e8404800500280c004a45c07140ca4502c10060031350341c8032601d83e02556244170581a00070500c91421540707012405002d2a09654000031b507115603848641e03100e100701c0c0e0307001c01058030140c1c4041e8680f41e01800a540305c104622005107aa04520080b241c0c60301c80e012140000d0401f885194180c60079500c0b80e80c2059025107001c42500b103800d1070802503100e600240c4001c5200544402d1041c141216078a543d241540f0606061801c204548402d0250a10540700022a10b500845000340150744c2008a040e5a90003154a6184030504010442d00031080c80000d2401040703030003009455845450492403000c200480c8014800450040110b07030844151180e4444d40003407030f110705484201c908503501da484200d0840000704003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 993660179 1250 993658929 993658957
    0x1e010902091c122c04051905013005060a051008011b180e01060c062720060d200a021f05040302030a0806130f0b0307090c2c0402 57
    0xc0508030a0748440500b00c4094000c0c9440e00c24201c900e04c0f60700b03145201192911590f2181d00003910518030b1011a007094440000c140007a5946203c03c100c0708150900c2555400c0303040011310300c01c000d1554050451688107000b084255a0f035144a001004090207810000d0b40d4040c00180401090107140050303564039440c000d03d08010000507141d68000c644c8071024541c5240100501050760310114111141d5041c140a4030070a882c10500a02c540c908110080d036000c11154428100c00001051192151000c0012020310b8000c0e80b0098002140d40d0303500c08410490341c0300049075500b0000454400100e01c0586510201440803560843c0c1d0204006030702220001d1803a40c0804400d004200e01400104024103098400039105c0c0b00d2083c0f42020300000070007050080c0ca40c0ca0140031a003400d00e5080101c206181c070400054007207588010710038440d00801240d001e00f02d11a90707204c00226100d039602010014800280c005405411250000440381c84214507190750005012114441203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 993661429 1250 993660179 993660203
    0xb011404080c19050121140f07021225060f0203010e0f010537091e060e0721090f0b0136020c0a140708061e010902091c 53
    0x83c05050700800c4202079485020050402c5280d8108180204600d0790442c1080652101410320010b0001c010240490700c000404000250f0940c1c90f010b40074040a900703030717280000c04590200c02c501440781013010042604162a5200030076014110005210702004a401c078442e6003400201e8009900034104200c40b0000c202080d0401c40302280036003012100b828a075402d081c12022401c0203010b003441640da00c000c4030701d10300072495543d01c0100042c010034898000400f101010340d024845407840410f04064003c04d01c01505c00c503461259055917292007030713002c80781103010340d1040d20000f117140f00307030b4401c03800700420010320150409078001d80110030340707526000c2c0f141404070181c0030412003e2a141c074043e5245030151000c070007412054002584a04004580b91708040288000800c408880940000e13600302c007080705030881d00c02d1804e4844aa45143d80d20250411807019143c891010310010310921441d40e01800004401500d040c0c1c1016480742c0f07100340120300400c01d40704500c4902d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 993662679 1250 993661429 993661453
    0xa05070312020f0f070305092808010506030c010302070f1b030c053f03070606170718020f0409050901090b150a15020309131b140d0b01140408 63
    0x103080349001080720740841c680510301d14a070215018406464011480014421003814491015261080b0004040c03c113462a41d203400442480c540c56481c94103211503100045038031303061045e14030130840074000d496980d04c078600440096000d1700c401c90700c40200d4160040481c0703021400c0a45601507021900a1a0650402580905650340014031441d01010501c00c46c128100c9040300040c0301101100301d41c00d943e0b03002009000031540300b400340c0c0300120b10041800b0958200c0822100003032b900d0264031898411007510b0301c08a0040400340090b121510540d035409074000c2000d44011103150b070916448003003403070a0320019110f1818584d103414140c4140301c3c1041080703400071032031460382c10782103001c1c404240c0c6e8000da44644030103601982c0507041183c0c000e1040311440b82c0c00800c0720945140307400210000300080012004480c81802540b08181d0207071882c44907289104036000e0409a07489c01013009040a00040707030400c80c143c400a0400c511081c09840078001e550060582a03c00e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 993663929 1250 993662679 993662687
    0x20d120921030f20010906050a0509011b0c060f0515042405040b06122508040b150a0521012004170c031c080f010f060f02010603080a050703 62
    0x101103030000c01d1020102200040e4200840380c1c074000d91800c02c0d60803540388541c50001d401c0300c01e507402d00c5075080400c02001c0181951080744070315071489042020b40c031040b161500301d54804e400340a1681c0c5001c00501320a006900d0040018454003020984d10481c820190940c0c00031b6500c00140c10f11003910140c2403a29003d0081e8400581303c00e00c01351604822108200e44440c490740740100c0d039407030503048151106011142030005660003020b440c10070b41c26007824010480382c0d100d12418683c01c0300d414144108000381c05250000c81801d15070726503a0f59400340c004454a855030110310340c0f40c0058191107058403001e0050100d4090603030300312032140150a45148085529950400c3d1040c2440000c12900391010f03141c914074865100420b69115900d001c4000608039850300c69520147c03d00c4110150400c00e40c0c00560314000705403500b0300341c03e071103030800e0142400c4c0810380b040038840d0a2003025080600360083c4008100659640c640e1800c952000c03e02000099000408030181908 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 993665179 1250 993663929 993663959
    0xa090f0b0f07031a10020a08130e092a010e0d06050a11071a041712070905010c05070303030c021207060b0108090a03020a020114190206010806090a1707020d1209 71
    0x76074141406042070250304100d280d03003c9a13049200f0600185000c3c942882004080d0400398420320b0296508403040c2540c028651900c1a06400c640301d0300010030104010881d0084403035040d100c01c8103e4249010720340044070080280c1d040001003040a2039956900c1204003145000b201d0010719410801301001c00d0b580c2e10141a51046002c00066002944c825088480e80c10060603840c041d49661500c8000c501131055030012645011420100c0d1380c0d130071101c440c01594161950031010307907904e0041d00c61110f92200a410341e0080501000864042e0b040124001024815554550700381e107114050780e040720b00d056841a41c0d44090004a5802080da00d8100d43c840d802080034000542e0002e42e24403c1c600003e04005440c0341262401c2908c0302a81e5a500c002e5100e102034600d07500000b9a111713800d2003003c000c0d05c00d800c00329203000c2e8003007440160756400c40070030410266550340104890380000310490b0452040041d00010560b00c0361944180e20850f81c410500c94075002c181001d00407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 993666429 1250 993665179 993665191
    0xb1807261f1406030408030a0b09041406010e04030c0f02040b0d1110080928021002061b04050f04180f0f140607051606140903041e0e0106080a090f0b0f 67
    0x308030980c00100e80d0b42405485d800355008643c0c658035a41d02d007021020b8140c5610050304000420184010085403004407000a030450089035010fa0ba51210904040305c03e03100a808182c5c26103400d03000c81c95031040c0c0740f1240d001501c08201540000040b038140d050f00007042ea40e060a0450041c00740c90701c1030880745900001e1030010754504250810708e403641e1500b42002108401e03d140c881591403000740208403d50000d010340c0c0380f0700d802e070006504d0791800ca505480f0051181d0944210100b20b109a40a844007d0310703c1c600402c0460900004103641d2042c600582d140305103580010b503609190117943c51288100c032482a415180440fa100300074554159240c020700204000c030707607208064402910041c0a4840100404d082810080c4240003420003600da4603c10040102c00010013807003100c811407034042d01c0140008201e84011035a000f54802d604203100100111031203171101c160000311080001a034464550713119402600561400c80f181e007980c4bc1080140000c29000d140c0c055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 993667679 1250 993666429 993666449
    0x1c0209060d0206090120100f0506010309080f07021c0c0501080a0e0303241306060e04020702030d030b130c02010c080a0c02060412200601030203010b1807261f 70
    0x24070703640e000407071900814400c9810000311843c91030740b00e01441c100300300358080b003025184861089440e04014014401041c100a418200800d000f544a44205140301d80c10901d040e00b8a40100c00b40800c079801000260b902070b001c001800c0038000d4540c080100c01c7e208440d65100d4a2501c4c0024280c110018094003240c0e1800040288843d80402200e40c486144a01100314104425041326002e40c10f000c5540c0200c004040d400d6a821942e014074242d65441c4c580d00c6000d41114204020780c49010300007901500885131107400c0c0b60180d0071410290384000c08051190000350b06545c00c8a800743c5091005039100c20000341540d030802407440c1c0214442d00c0c24445084402c40103550f0708400303000141b81c2188030f40030781192841100c682109001034494403140c204004070140c0d0760341d401e0100364465443e14103407100031700d0303d603121400382c00c042d1034181c540c0d0344c40c84025a01c0c91819102e000c0c8616506c010303150700320300709140e042c8034a950a448610038408064112442c011a8204400b4030b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 993668929 1250 993667679 993667699
    0x30f02061003020f0103090807060f0b0a030213020a0509150703090f05030a17300604050403091202010516030302030f0901021c020d0e0f0a0b1f0302010f030b1c020906 74
    0xc004604a01010742e50107a44544114001e903004130000c0410440142c1040004030350101006107a410000754000266800e1080b4207008040140c0d06041c1e10000750f010340b04440c0705008003841d4000e44074902041c24502c2c18540d004020440c840c0551807042650000081c1540c101900320130400c01400c2203181c4410154202030219654203651003001e0126006040c50000e504601021079207926035250207a1240601e468040c290190854803210000810034001141b40c186442414400c0b80c040e680d190000c1d00d40440d114031071500e01d1050b07041280030040d00d120b50710724600074040c05210ba5001652413408003007a080000024180301c030240d00401804160b1b0554604030006116407403401070750ba69101d09140000c000551041c07005005189030340ca00703042c000c00d100302202d020300a002c03600c0c0e0700c0d0808800c401040180380061200f0141042c00554403034100440034801c02d050000b0288004c1e0300051104403000d10aa040030300040f00142103007460a50250001415a920422 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 993670179 1250 993668929 993668941
    0x60a030b01030f05070603180b13060617061312180e0f060111010c0e10090806040302010914030c060f0705070b090606010215060306041103100905010207032604080c1018030f0206 79
    0x1520b0008c00700501300c074031800007180020b000481040403040c0e018804002947c0d581c8000581c1035045e4210b0143c034001c5400140004e030401c4810700e9019070044202a241034103442c266030384011a440c0c080001c40118021820342c900100480c0104484001c40700c0030b2404038001428a20386440c900860303418a8440c9001c0c6070404521810b441040780d416a510301b20580480d9640344540c85429184104000c1c001419019440440300d14020044005003120160780b0903624807488140e1402079000c7d100140c650744803440d60b19008071291500341c0c40d01109454660f9103506c240c030484081d400605c01e002066070104044a00741d14461400005450b000000a841d494010005040c00c03019040007032a42d41e0500c00102c8040f40808200f144075000d0805c00d0003500425011130204881c01541c042c03207001300d151901d0ba1191000b0364201c640d5155618041c940001c603c03054140b05541c4404441c40003400303445041c222a440440080407103040003000202d0700a64a400d6400000030302c16 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 993671429 1250 993670179 993670211
    0x30f0c0703120c110102041d010e0f040b1305030c1617070918171c0504120311040f0b03100605090307060302090607290609070e09060a030b01030f05070603 69
    0x208540d61030341e001800300b1090304103450351141601c524442d5440080d0200307620000441040c80c582e28003c000d4540d80c1c9900b681c0b2b681030001c1d24003179440f0034200005400a005104100da0100b00313070111101d11003890713841910719006a1405516504060b4014500c00070030103030013004040300ca10100d082a5a03181e120345503801e90048000c066220f0b0348080f5100e401007010700701581d1040c00e00c180792a9055400110750402850f1954460802894843c9240705003e564003441d0840c40380105105464011380060031401c6074080750440900001400d40b20200c3c5200051a907103071860750343c0c90000c3c0c02506100340380d0083d80504c00e06010700c0407a5200010b4100a590060030016510602d042c0052618081c20300010301c044031042900102c0000407440400b07012142c800389240b42c45107010440251403c685e1180000d8540c1c0348a400c0346040000950002e10140034108402d0712a2110222000b02360019502002e455203500100032082003c0c40003440140b50030440d200ea604802c01c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 993672679 1250 993671429 993671447
    0x4030b061810030303180b07050a0905010201020702060a0f0e030616080c030f04080a02012c0d030c05031504020405031b12010b0a0603020705010b031f110f120c1e030f0c0703 77
    0x3030200b5655641c000024492282c0d080074030703034109420030700230300e0040740007000b80d031008180c01c0c0001d12852001600754014025113203a41e40c014801c60a014800c80d049038101b0490090900b081072114014400c0e8a060104ca40518201c000345011112903090140c41c0b84d601500c070003050300c0c042041020b41c0c014141400d40041d0b01030b0700103035540c0c10201c0480c0980501400c000d5038442000d62441608070340d01d0340725501e00d4401c06440d2100c0c080075040e000c0703c030407041d440082201040003440f100c1e40c0b0f114186898000a1005003040d440310f010a01c0c0025800d81e582140e00506400b407414a06403c47e00c80d00001080244003984105012911204043c402c0f18140b6402151117010404290440c041400001e0103c81c1310b07c40440c480c080e103259041c520348485242001440182913010300702c40b400c0211816140c44c0000a0f03d81e01c108041c000d01c2101c1003081070054040c074070030040d4010a0aa02d0721007441d180e0415042d208a0f42d0409020504009401c100304000a500812aa = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 993673929 1250 993672679 993672683
    0x60e150a03050a02060c0f160e06010c051f060f09050a150803121302030f0c010306090c021c1e03020903070501030b013213090b030303130807080403060204030b06181003 75
    0x1c244c4031b0702100005d03440c140d03601d14550080d0107200840d80740203841c29448402c0310000182c054040d203130103005483e6840b11100c00b9181c0d8110303440b04000100d40c1c881c19001d40850020004400759100c0d49102c10140340d4000d000f80c682c503002403110308282d500502200501c0901c1420a40b464103245a550340b00d0441f80d860105d0305180001c3c00805201c05c8040d2594001d015103060b000c1d5158000c0d280c00088440601082c54002c000c07e0fa4101441040d6010a2a0700102a200120a0080e1003900803a1408041114000300d145812a00c0c0f007203c914229981c8001d620740c0c8030707d0109414460250407540c101032801812140d030b6a80b00d100c8000025003665102e50300f05000548003c810b0030007022003032000b00021006200c0c81d181040c01d003258540d200c100f00341503505d0101a2284401c9e98042800219040264003180505005041c10b500c140c0718640b400390f99544000c26a005a802500c07404820b10030030209060120f10b078011310a4040c046a00f034030708050401d000c140345000c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 993675179 1250 993673929 993673939
    0x1f1a0402040524040906030f0201080c040819020303210a0e030a0807030f15080d08010f030c171501060c02100e090a020f070f1103070f15051c060e150a03050a02 71
    0x302d603102100c203e00300c5010704541d080500c100c90b141e04245442d0038000c04128002040f80c4002110401d411040c2c40680b403580d0301520364520030103118466610b28410031390307050004002d00080300010ba1401c482c00100348070b00000900e00b0f2440c800403580f20850000742d03900104910340002e5440414160301c119141000182c02c43e00c102000c00804003603040c003815074110b036400f003014030f00024006541d0307119640704417082e031300d60001900001003844000c12001c900301080c00a0540840c92111825014040341c09030307140810300c2d002c185820790105002c501d06110302001e41c249028103282012840c22b11100c1d81200401003900307040c0c02400740c800180c1c04030321681440361148c11140032580240d040501d440b01820684c103400c4901041c1c5100c0d1080321000200e03803000c0c449040c200c4945944c01e0301500d9000805850b1544400e0120300303150722600f074003c0c0c290b40501c40d45020b00035601140040d1b2402c04081c41801d004030607180d00c1000741c00e004100040c1c0000c1c03480d041c41c0c1d054031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 993676429 1250 993675179 993675229
    0x501140c120a21050114060f0d020a11120a120203131203060503060f09210a230c011506030b060d0c0c0c03060504150b01050702010c02031f1a04020405 67
    0x101251050750030301458441500443c0c5074180c45490781c001c9810703541c1d140307403a400c070758510310400c0094858000300300c6984601380078000461195a01603c028422410013410341d5a915062500342032141d48480194000800d0854156a0003056211945174804045155003005c040e411841c0b40b003604010401103a5500c0078981521a030856070003404040c0495a150402c1040d5904010040301d00800070322844001c0e01d10160520070703000501c3d01d01780a03035141500140040720180400c07620001105030501823078a00032940710042098001030740002070150210780130046244139a900c240105410030b600700c8020703520b041c00c580803171051a200180e50156070301e007a6a6070601ea01c0117008800b240000005010301500640d00c40d40c4210032071251859820600c0d401c85503027941326070000341d00b40404001940943c901c282d010f80010f04480e54005d01d40700c10034035541005003e50300e1030b03141e40320310026a5809038103289010080301d0960429040a01007814038030400814103410841e01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 993677679 1250 993676429 993676447
    0xc02090702160807080d08040803070e040b06040b130f05030c01050705071205160b12010b07020307080303090c03061b1c0902150a1205151e0a0f0501140c12 69
    0x40b14018180c01c00070040718403541c903098942c036030285215000f9180101d14480c81000d2051440034440c0740c3c801802421a19080320803218144100070a5402c2644c54601640700d0342d520014100a0000c280c0c01c650310341140d040403c00070105d500c0180900808501407001d9a00030884811242080c41c1c11030311001682800d83ca001d0342948000b880005c183c07008001e1290200785e00e56214850441114920368a20f00c0c40320520501c4181000c0a41d014014080e03c4a120002d00801c1c0c0010f007241e004d1910740084500310390058a022145500c014407100003070405000940d030000501c1c000b404800b2050711524440e10a41034110701840d69541c0803050b11241c0d62006034003c1c0c024204c06520300520034081960390003c2604404103580c0d440e49590074401e4081c540c4aa07141e2440c0030604a81103050041c500031509061464214141c6c44124030385500701d1040c01007041e42d02c1c010780307945030000140940074075607007140b01081c2c20001405045000198100ca0400d504405940c1c0d0100c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 993678929 1250 993677679 993677683
    0x22090206070f0b04170a0c02131b050408010c08190c11030408010203071e0f0806010201091b090507050307020604030f0c0f060b090a0b0a0504110f040305010501080d090302010c02090702 82
    0x11079070003400b48155400b82c00c180030102a2052050b0721a5000c0c40803080130040600340780c015420140009540d4047ca9001807d0000d0307590a0305030b091350013203880784842484a1054031100b441c0800940c1c08a000c2000c0c00c001d0098400c0428075052501362802c2640d0700c0c2d000c5203004500000c480e03860f070503c03a504920809000440005442c1500e8071140c64135089800b07580241e03031302800155110200c071107c009810001c5190800b40c4c4404100c08030754241501d040000500f11415556640340792004580d00e8000040c40b02014440d00c2d45441c202032108084800241c802400c00200b4004c1003074181d000980c49030899014100360520510501040f203204820480041030030044065480802006070080700c0c150100700d40e202c026643d034040000440720061701040d40014100340800040c1020b5004001020b50794421528004d80d000780308415501950040301e940c1c1d500c0e401001102c3d0b082c40040d00b8a41c1518000c1805855130700000d28802c0102c4c3d002c0e12400f840008945205d0003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 993680179 1250 993678929 993678937
    0x19050304080a0305090f01111c0909090c0e0112082515020703080106180e13060c021006090902090c031302030d0e0109050301150611152422090206 65
    0x10a80c00c641c0103402078a002442600685c030814010544c0c4030f0469810760284a602c1407a6500d503009107001500324540e6184aa4081c0324a020700520003404604c17490303240a505152400740d03c0b05203d0502e0b0200711005404c0590041c40100d1041c00c6e64400154282c0c1140d1481404a140343d080c3d24519501000d0040a40c0d4000c00c1d040741344072911248100da40180210030b009455403040c0e030b82c1e85c510540f603241a4071071600b10b00d100c0c04c2d0b05028155404880540041081050340b86580041c2c2d2844112800f0070b2010015034011405141940428044d070805802200801e0041c140d4660203c0c0e004038000d000395464201c0800011031110f1201d4a18080c207070010100c815406c43c140b00502041c04410a80d4000743ca4010003140608050190000d4442e90030400100c481c0b0b0644102e03201030402d4024142c07801102048040c0c6101036210030300910704091401e89442d400e590300074900c2c00e911080350150311002c80c140c46400d0840d0740c0000401040a01041480c064400660207200e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 993681429 1250 993680179 993680189
    0x9011d090d02030a210c110f010e030316021203101509030317040618080315010c0807020f031903121a0306040206090a0b03040f060b033d0c0c020307090b0319050304 73
    0x200c6d00d00b104141c10f60008008244500560a540c0001104d1089034241d400050041506900800101d004812018403030070340c1c602d080c41915440403065484641541c02a2211800440301000500c003056601480390ba00300c3d190300b070038140507145503000b4107650515045500361284210000342030003450b400200c5610301400f100114440b42e460304030b0316500300755900c0d4407001c0608a80c40300c0354028444804a503030000411030810301e5135800c12414241020001d50135015030b501c1801c024100c044080e4100b88241c4a02040c43e60700d07240c030412030307455005942056a60360921005070302d01051140c0c0180d0141c6055a4940450010412240041e407084065007400420003092125030401891060b20440301400100c811100b01a0b42d0b0b160507000d42e8074030300c2c01d6290f03082c90080b000e00c039490542c10804182010203002d050310201c60080281c48080381c41000400218a4240403001c0940b1150f4400c004e5651f50802082c0d441e076803141c05481c1121050380000030301000300f081d01e00400d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 993682679 1250 993681429 993681431
    0x3316050d2c061308090d0c0302100302030603162d1502070905010f210203100f15080129040b0402070309091503031202031509011d090d02030a21 64
    0x2800300515030309860700307a409281ca24001c0c0c1c400314451501c1d01100d8801550404021402e10185004111622a0304003088901e0480300c00001b0060321a940302c0b850020075500e0058907450850249030900c120391110450714181c1c003505008590200205404140e980041d01d043d8008202c1c8806100e0100e0f045400d503482021110b0403c070b540000d0400585920420a0255998030104a02c919080d8002c240042c50040e80e0707a80040040307030000000b20f00040445480191109043c000c60702d88842c0c2d0a03010b07032564059402480140b901c0c400800444000f0021443c84005c00200600c403510143c00b40c0c14141203400b500d60303903034010041e80e4400074800c559078111403901034030051051046001309410222804a9101c0d0850141d08494158072000008062001d24100035031005000c00000f49003404087c1650b100d5000c0c0d036028000501101c450140200a00d085400f0000c1c94403d150340b10040a84480b5808401d5804403009402c09449071090144140d42500a4900011003d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 993683929 1250 993682679 993682721
    0x1051801031508012003010f05010503040303060e0c0301090506010f1b240209090c0405010504090914120301060216051e030f0610140d0507050906030c033316050d 72
    0x15074190302c0301035224007054500e081891790401030840d0340400d10406a00d07244540c020840c0354040c1c2c000750742c4103100e40781c00995541c44d11081c0318101c1d000e0300d407040c0160b4040014456000c143c41215009242401c2c40e0802d111b03441030081005045040071700e40500c940214078104444410309030a68803000a0b125500c4461040040080d00000c1016129140d0740c0007203648102d0070f00854041d1007041c4c0d149440e041c205911503001d4511224202c80d81501d4505000c0020414010868034901440e04c8030341d607500d4004000d150110040020900100d82d41040100ea83c903286110201d96806246549101c4c0140c0000d0900150800b0112103014101c04c002c05150381c022040207441c0780303085019003c4280e000b0f00c40080f03044030300100300d43d0050350103100b54909240c10700d42c8000018100d400c14099440800d0901d001070350850044101603220068142c1142c0d41c0480d41a080c95408a039450406000305c11410207654040c24041d00007892102801719400110305101840e80402c68 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 993685179 1250 993683929 993683939
    0x1170117070e0f0702120406090308130b0a08070305010506090a05040b01030e0706031515080f09030c160504050604270203031b0c13020406020a14010609091b0503010209010518010315 81
    0x83c1c650860358900140544410000000b07804825281640c525550700c60007141541e544000c2980040b040d184805926040021411807410040c1040e4000340d0701ea001a017012a005010382d60103130400c40c486d10040c05018984d031101c403142c034122101102c0c0801c954100341e006900804400c640282079000c0c0320804a16203405400017048041c045c2050107066641b00700804442c1d000709002000110410080b4074603103036990003140c0000e0060203403494120340c0348400f40340a64512034001c1c0f03251295010800c3c1d24140c46443d0340854140e6007880500c42d64030342800c2c64520602940030480c5030410000954904005a5203e08114158409941030a4400ca80d0320b00d0114041c41c81180b8807486020901100d000356011103101e42c00502016400b90784c0c6c0083c8103d4213620003015940d4104c00141050305020301c03120035003e015030704110020824840036000341500814001e03801040890b420342d9215045411920003018440007041200d001240034191102000d02070b603107650000301d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 993686429 1250 993685179 993685201
    0xc0a150212091b010f08070c170415082512090503040902091c02030c01200615010f0c0510050405100905030a021b0f0103021b0a0807060b01170117070e 67
    0x801e0600a15080f1510001e01004490803400483c201001492000c00b29140390300940036009040d1094a00041c5040c0e0400c0c20701a940042d40300e52840d400b4180c0ca100442d03003014004d41c00450818040f60b4140f0b2489680c21241402c0121204226404c80005e409030020b40c850340f000d907800f80c1602e0765969502980d2000c0d401ca4010241321709200442281400c04030040903540c1980900a03000c0e8004890040d42d40200d5101840014948525840d01c003a50520000740315401c0d0305012082c00010030001030607c0e111803031170070500140010b5400420000130710020b0941c1c1512000c651680c880c50002c1c1000c1c0d002ca0070036500b900302004d2070f0400c04084090f10000c5120303401c940c000903c203801c001d02503030341014281c0c100c20000f01d500f40355403017600100422024811010107071192052458074002980c2d07400d56180701c0102e8080c041211314080c010b80000b00b40f070000a0041c10398490003080c8018880d18401070751041c0000d0803030000b8030040000b00389054400d80340b07107000700d2800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 993687679 1250 993686429 993686443
    0x2222303070f1202090604020c070e071716020f0a080f0a0309120f14070b0a020306240910092102041e140a020a0206040f03020a0f030f090503030c0a15021209 70
    0x2417083ca00d4500142d8242098429585070040080050100078a0043c1500e070144015021300100140612288118043c40f03013180d0013640c0d4001c6000c4100c100c5640241001c0382502903400300e80101d184040400d86c841e06485d178030703c42da141142d501e09812906500602648a00400c40a084009031040c40d030002c40c8008041ca06071038201d518030070350707503101c44901c2072450060888045c4d0001c100d00380d007070703a000c2c580c0041c0207010000c1c451100c15404015003100c155404450000082e0891f040c144006c45048100641c105040c0090a000c0b8200c20b42c40c404ca2641340004203012000d0a41d07030f403900076088800880000b980c08008000e1000302411028200c4082044080c011400f11a1035100b100e0000c0c090794007816107603d4940d80c1a00727030001070300c3c19021441110642008100281c0150116038443c1e103442c014000103080c040e00d04030159006a20039041807005e006402d00200c1d0038007216500811032a80040d01c144114024003400019275903036604c6000b00721408400041d48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 993688929 1250 993687679 993687683
    0x1505030a0e07060215271e010504030c1128050415030512031003081b10111b0f01060602150a0213090b060c0f0102222303070f12 57
    0x1400500341c010081a620001c030710401006a000001c0550309401c0061070741e0f000104100c1c488482d210802190008591b84140d015060300000000d01101c2d03003003030b0124401d10303602e0000e11481c40c0645014004079008903000d0501d0198a4410f02c40350ba9411b080c071002c0701280030101415000b4840705074100d04a018103401946030181c00030b103049801c03a07404212607000300144840c031422038800a1a4202903c03c00e00c00c429560040001810000644603800300013820600a548000103946404041aa0b0400300c5181c520038a603000355410848010744505500240c4c41c2c1d4240c01c41d1442c044e645181908194a0000e0110f082a40810410712a2104108280c0d154071406018000c0348108000103110241c00041000604065041480040d00c001c0034142070464908505050880080c0b41501c2d40c0d500240500700b481d61080380c417101c00e03d18095000450308209210014130f0b4040d0740e4031548241600e48482070b5030304029880103461041d00007031549035100200e46510000400c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 993690179 1250 993688929 993688931
    0x30318060507090906030c0b0703090806090c15090127080618010e06090319050d020a111b0310020309011509050a06060e0d2418020a120b0f101505030a 67
    0x80010584c02901500c02925042102000e140c0d16110540c01154001c0e032045050108004002486030010300400744501058005003c0682191040000d81c0d041d241500a502c5002c3c440310030113076800700c01c1d421040385010082444070a042c40390303482c0100c242c0c0001c0152184404118601c0c0e2210102981d644614000b401000f0305c159505858500c102e60409980d481404101d62000d4004d000e00c030440500e040403440c0004000325003080c0d9015040040100c0c060044883c030200041103064120f1404020f0390001005100c00a510b0384180d60740c0409041e004004280701c503d003980208040000b0400801145079144a0788001c1d180840f506018207241460004003140140a16882c1030001040901000c5007603540c2042c40914204104024000d070302d68800e20785951042880740b64080449208607036241c410864809201e4000c070400c204070300c141c500007401c4100c4043c2c10424403640219960740d03c00c80354038500025800281c5008000c000c0e88015908980118064079038218 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 993691429 1250 993690179 993690197
    0x51201021b0102031b0d15080a11010239041d010b040c0806040915020c030d05010902070f02131e050105010e15031803370c02100c030318060507 64
    0x2280c0b4200d00086420341c03903040c040a5103504400f80305008107030b1502004c400040038140b607030440303811a00a402500c010340c0710318403400600c03194144010300c0c04801d100901482280d032207008840c400710003079505208841103c07840c5900160040d0040c14901402c20444400c080f03562074507000e4103e21030b41680d440c2014407215030405026200c1d030040142c4503141d6580f01c800c01d000051500407c280c600300e40000d009081ca0324140010a01c000841c001141c450070440c0926044032810303031100c080b03184100b00300f0b00000d031360604c03503010190121046a808030909404602802518200d441300c1c400c0c1e4454403d980c103071071b402141a60801c0c3c0c0d9803031048080000344680c05002c401d504011040a2002811208010810030762500d6001d0a981c100071007030352910f00611000c0c2c01d1030f1005030000c00c00070310540b0a0b03c0f603100131500d0b0320707080200000c02c0d008150384080c00300c42402001041c5070000c0515019800058036010615580d241c44c5d41e49050090090906070342800008285030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 993692679 1250 993691429 993691477
    0xd14010e0403090b0912070308040f170703030c0c0e01030b01140d053003010b0a02010c0c0c05091e0a06030b16080a05100308030a0e06070c0308160905120102 70
    0x54442032103242d150721101c0c1194244002d0750080d8001c0c5003e42c0e4005510420301088010501040000307600c602c0f000c646441c20a80403403200c540e0798106d000a5034611200c80780310680040c101084035050308142c0380e00ea000d800c00c42100d00b040d4100c19085c6010380e0000040007070119060b412100b035661211080c102c4441009132081551002a00d9680300d407a81085244a2145141390003c18111455071804082e10104507900b090b444a4111000400c419411640a01400030440b100b480c0c2142ca91040e540c45214907042030142074010b08000000415400022840c1d03d41c1a0000d042c0c2007080c03600d80140c001510960100316141c80d43e083c042120726140c141c00003081e54090b115502c295a80700410f034000c0000400741c0d21840400c000c004045030050740218021300420742c010803803001c0c00c0e010524105001d00a1010803c00c0482080440d50004039550020308162140d11000c00d107080841c5ca16189810071075109403c4424695140d034154003c000d400e205c6200d00035442014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 993693929 1250 993692679 993692699
    0x917061b0f072010030902040c0e060a050d060b0f0d0c090b070f110607050610140109060f0e03010f020a02071205120a030e01060609170a11060a02120d1401 69
    0x3034481141c05800500c9001c00050402042420501d0800d0780c400c00070310140c0004004100300100807010903501c9241c0010340c205401080d00403102d608017200140c01c0b01010178098032456000408110740400c101613094034a4000300c000b0917011000b182c4550406103001000d9221194a09400b880c05404200741805010310004403840f445000341464541d0b11960100b000e4094211686412242c01c400030b0b540354409003c50500500091a0b141391a0002070902c14541e00301c600164034100a6141a0b0380c408a240262582d0345000d0034002e83c5078106413074104060344060b0f40b5500741004900294683e0303015000300607942d400c0b60107081c0d81d041c449040680014001d08260002d9440744460440130340100b0314241c061030f0004181311000f4609003100e40c1d54101c41c00151140f0003c022110004660400c00e0006802500c1604200c3e80c462049007400c00a00d03002d00780116001c04002c0c000e001714806210000809980c079481000a071000700005040e1800381601c020002c1080070903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 993695179 1250 993693929 993693937
    0xa0f12050102132403050c090d14030414090f01030803220f03020d030605060f070813120f120302031e0c07060e0d0201060f061209020d060f0606080601170103120917061b 75
    0x32071f06c0d01c610303202c02c070024400740c444d8550701555050300140422401c04020002400145903000001c005220000c08101d007924004e442c2a080c44258030042c00442e5900e07007100d811403251510b100002c802e005989810540f911800750542007c5204003083c50780220b00401500341d141d40810076161284108aa14024000c1204000c0c800713100c10b000080007800208152020700c1407040b05641e0311940100f8080400c01c0445250142004c1401044001100c1c94090344250400f5815860510040052100c0c40112213103648501c0010a100038604011510715640100050104010685801e5560182413620900541c60010000341d10a840d41070740b803d4840c2c5554001010b0445030380103001c0d04000c4000d0b0380c499243d11004001130454810300c481c0707000e9108041905441c040010300586d90003400d250521854a0094040000341801d4506495004c0c2100e441c51122030021036112540360004000340c0271003c11007409403000211203120f4010606501030303090000030000310701d0103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 993696429 1250 993695179 993695191
    0x250504020711362203020304030c0b040b1905091302030105180c0301090203071209050d1205100909050a020a081b040204030c091d01060b09010e0a0f1205010213240305 74
    0x80481c55003d44244001c42c040c0c00c00740c0fa00c000c000c1d0010340d4104144103101300c4800c5015900000d0200100160700000400509068407d03a05091904810040f544035040c50040c2c0e200c0c030741c0c032404c4030360b0702403c281c440c0c41202810311642c200e00040000002d61080c02450b11500c180344003600702106400700640304400d003240d2a800c592038125220042d4101070a10418401ca0a11950550001d071003100c4800c2e0185000748560b40118101411701b2607800100c07401c460410041041d26002c614100c0c0c110b03841002c00246080107424440e04101c4446402580400c800100090454002849041c0000a4201e040c0030100d00800c1008922943c8001040f824039210100507150040e07015824004c44100032841c0d96105040781421583c0d50f40280301d06140c007081d00c805a5a105200f07204906060b10b00c0701700070303040c040816000320040c1300d80b03e0031011201414080240a4050310602160a540041125201ca000301d0740020201c3c203040402201a55a10f100c034424020140104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 993697679 1250 993696429 993696499
    0x307020c120708030a08040605091c0e0f0d0b01080730111918020405180403090803070f031409010e0603060109081204060f0c05250504020711 63
    0x103540038007403102100d4a014000668007036042c0009640500384010080c01d900b81c0e8a004d624541440c180040300d03406880341c5110f6103c009005041c40240e0900b80e044a03c60406881038440310740014140c03002011400d0700010451681800c0100c00c0c2c2c2914141c94032002614405500c1d842d41c0b045148089001800040c24a1091840700d8101004402601d014000352140707010194045030b0412014488403e41c1c10f40d04c03501704540c401e00c108034990304c00c12440543c80e03d841c01f400aa0310340c902d08800c181c41e40580303001c54101405195407070f000307000700c0301a00d0322410785051881c11340c0200344054002c01c012100c100c2c9001210000c0360b1074040161110501030050320305200c1650401070615041c48240740c000300b0742110401840c440b1400340076026540c0c500f862001480310030900304803810310a65039069000107401007a000c405214242d0510300382c070130810f12040c4601407603000c69001071000800c24184600c41f1031420b03400e00c0549222004030700075000d0480881494242001c05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 993698929 1250 993697679 993697693
    0x130e10090c0c0f0b10050604030507090f0615020f070e0105031515120c0f0307081b010504030602030405030318062205070302030708060a0501080309150903010e03030a0b15030702 79
    0xd212650300040e081000c0e450010405a034a0307442c190002c6034a41c081c2c6000c00e5540800800c6074221001ca4040d06042d202d031030030103255584096481c540740c041d120401b512800b007807143d191107500280050403100000e201404002c003000e901c03040c01c088400e0207400340007000b050041109004071b040320310241c002c0c400c5181d18504a020802d0103001505c4400507000012000d50303401020210946420004d014840e81c40810450110344240d0154007a030803041302000428400700e941600b00c10b2403444216001510801252503203e140c0000300183d2000c0103201c140000000518400d070a20341000040d107001245040c1d4801d022115141c03107035010650640041a04000c4000c1e451140701256025510395002074104103141d0401803083e80500c0c1009181080d0f070280ea40100701d054055458105150040b030109041240541e48003403000800d40000e440940c442c0005258620650303440f42440c1c410100540b1807560740b54824072003030200d00301d200c03007030011a401000070750001c00c01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 993700179 1250 993698929 993698939
    0x80106080a33090e010204300b0415050117011a0a1a0d1d06071d0d051f0c0e0f091810050703091202010c02070b0d020c01090602130e10 60
    0x240c040c0e4081802c5210100e000403d00e0f201e00a8509031403403500056100c40c10840341d0700001121401c0c0c3c40140710581007107155076100a2982000e1500300d00501003d07651420b00e03c0d9446100101c8644e042e03e0440000b451212144500d604c00240c40024041820b080d210000c83c480313000600e59116200f0f010810100c2011500d400010342441c40310780c08d0008207021a411107004030018400000700d048002c01201080c020598060210700301a903d0340c5040300807030029000140b0481c01080f000e9180e909209042101941800b00d0000c4202c901468900d030302c014100041229002c190101120900c51808480a194000c4083d0080f50541e80c0c102c82112a0410b01102211a002c1c2e1003d10a01400d14040e2900c1034155480108e180d00444c5042e06410700328440c1442164500061842182c3d4046200707070458003444074040d155070729003500e44001e00c5403101003011903103400030716000c001050700902418000520403a4035070341e80b401e00070b2a501c0e08a9041d50542c01405040c09 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 993701429 1250 993700179 993700241
    0x4261812100209120a06230f0604020d09020402130609060f0e0907030207080c0c0108101d0702010b042c0118030c11060d0504060516020a30080106080a 67
    0x1240401c010103056000c240d113084541840b800c0f403000d44542c0e4071510002201e40480c1500c0202d442891041e0840b45081c607040e2003420f8010708840c3c8a20f80001c0c100344403140c40d4124021258000300304540c0d4040c101d00071190b44416114650204038070b6000006d520703000e803034030042510003900c1c0c919082104400b0000e020b500100000281a1300303102201c04030f0349040207030001e500780100403d21f081e0018009854120300901c00c0d0441451200d06211041e4003204400302e0b03a410282401407611038000c141c0c01f603e12246a40d0b0000d160603460f034002a82004d40620305103c5000c50585038030010325050a80c0d5652003040400151607088000003840384a400382024090341c1c03031604030070003c1c0018040d40d00010700760601640b00c2c01132100b1b0000f02e100c1d5640065181249410005500c1e0001e9140d031003450b0003800381503000782030b06600c2414001901141201c00904103100e10814400307031011001380179410000c1d9040000503c40b02140c81422035401855101c80c0340d000982c0340400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 993702679 1250 993701429 993701437
    0xc0103110403080f31060806010903120504050f090411060a020109060f020a11060702060106120b1203031608010303120c0e0301090c1715010e042618121002 69
    0x1041580d04010000200311003c0c00703011032089012925030303a80c2c03800c42910312540407068070700100805025071000300c040d82d0000404607180341c00c0c021400e0740e4400042e100e0805070b920180618003001030000600398860018400c1c0c8000712102401c0044540c113100140c5c108460092a210b4001c0464040389012005050215030030320000c22100110b90700c850036620007440d4100c0054002c2580c95040d90012100744a00036440e0007000b0514000200039031390a070610611040c031128440802c1d020006410000b01800003406007454240c42c200f0726566640102c0350a101d001d0751411411000344140d240034100d94041d9503900d0010000724000009000e41415002030001110441d22070792005e0060180f050f002d0300c07101141c03d16007a82c074079950001e40d06010345500544a0301c481004605170700d505595007021035a0040c1c2c0d0318a864141281c50360360500d1486110307007020b180000c698006140c501c814880881104416100380007a04000211000ca250050b50004020b0815036000d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 993703929 1250 993702679 993702701
    0x603061d09060a050c161109010905270f01050906010e0117070918050a0302060703050108070509010b09030106030c0e0613110a0315050a0803190806101202120c07031409030c0103 79
    0x41c038644003408a5601c40c1b104903c0c4100d55200c3c0e04440880c240c6002000c1c9401009041e006001501d80380e5003450604010705c0e100e49000b826964044c0c0622020040c12070b0301e29005000700b00c00d051051040b655082d091096000010a034070000c41c01442d00b00c0076a0460b951304009003802c40c107001011025040303019440e41c01d0a0504030001c0400c0e420480402c00b5801703500a001d031802e1840000781179640582041900d980101c60800c00d0b03481d6280c0e0b05045034141040181c60319100c17070020f40903040d030750b0003d01541000e07140818602480c00c00140203502c11680d10b0041e907003014a00040e1044002c4c1210f00c404207000110840e400303038100d070480c14041c1040760486d80e1104005034402d0304580106641e40d0001c105003e4040c40a1921440c4105038240809640342040c0001c0020302500e5101040240070244140e0501c1c2a070107a590003140841c0040144c0340c111610005504042000d80c00034101c07030002e0400505a60460344803180c00340c00342400e01780d08001500a08404051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 993705035 1106 993703929 993703951
    0xa231e0105011704051002270904170d0e03041502010f0b0f0d03021216150b060d021b011b110708030712030b0a0603061d09060a05 58
    0x70b00072500307002a42600d03a0b6844d46441c40c1404807060395070308154004120001c0200d401910010403d6010140c40e03441c400180800083c0c1c00151000361116104012a000c43d0742d017107004100400f03180b079010130283c082100e90303071a50303011b80d0295611402100804441d9070b8280100200c600080c00b0520040e1790020028100446e2001c80301c0c411104000d820701054004d101540c4000e1242c0e001640300c80208028080c92005914102c0b085521801c001c8503114a038415006003160140021742484038192a0314004d50001c000f50405c089098620000b07003a0074080c54110250b600140b170b0100c0d0300d6000182142648600000d650b40000b2002c0c01050340000c1030b150b01a0b007020500c042c4001009094000703165403100c9940000e04c0d000301082c03054040e085441110340c90781005882c4a110715214014500640c0d21a09580108001c04c5522010307030807032504a1141c4074 = true := by decide +kernel

theorem cover : BRFrame.Cov 993525179 993705035 := by
  have h0 := BRFrame.cov_init 993525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 993525179 ≤ n) (h2 : n < 993705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
