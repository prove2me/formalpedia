-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2501
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:53:48.129779+00:00
-- url     : https://prove2.me/submissions/6d60beeb-3160-4fbf-bafa-e5a96033593d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 449640287 ≤ n < 449820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 449641537 1250 449640287 449640329
    0xc110301020325050307050f09031603060615020f0a0318121b050f031b0621070e0604061b1109240423070c0803010b040609090204081b0a 61
    0x200240010f0110f00f0140d2890034100f8904c5501074038400c0580d030705c81c24a02031020300b840c0f030141c101c1034185500d44108961a143d540400e820070b00118401c0f94040384076130800010b15883c41380d12010200b10360202540000c600c0340000c1c42e030300c0b00d5014205003000c400b00441c0c0e040c4000aa03004017072454042d20094007000340a80d000b1480c080c02000300b0711003a48030b0342044400c8002c4481c4d01d505030f000c05240320031109100059802d410004215038a043c210725a54120703202d684050b030304940c00c024204080540c2120000d14406401c4402c1c0d0724103030501c0d070081c146407400f8403900d07410b03a0424170311010440245501d10070200000c1080d52603280103100c6252400610742d0310320280c22403500c6550a401d01d4011404000800c3e000307210f40c000c2c015041400528001c06403000c225465035420042203050004601030440c00d00310b26508ca04000c0058407483d016401464540e05c104410014200c0c04150440c1c00c1040c00005103010000310002201c1c801030303801c1451540f40318900b03a481 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 449642787 1250 449641537 449641561
    0x20910020c0910051e1c0f05151009050c1303110a06090b070201030e0c1f0e0922060b090108010f18020d08030c1e04061205070f0c1103010203 63
    0x110111828000d9036510f510b407801981080c4502a044449040404800d181c0d40205482429000d081e25126090040407640c038212180c8007603990a814081c0d2006000c03003130000800407001228008a1070801417040f8000410394499840c4460303480f000304400000102c201c2e08250b41543c0308521260302c0341403480000b80707068581d40c400d50704040c000030098040c440100482d408850402c2c1010742640040d4068881c0d80e0003640280114044880c2d41c0d03072000c0e030a5045000d41c0d021501c46404890018000c501400c11040c400c0e000035080103115807183e4109a0218450344100400c14020300c0d00401070030904070010740c060b4540002180c5024158000a00e860804078180100c1050100700440103520a40113500141030446210108400d50000c0d41c112100040140c603010030001901c20b03900392142d080c2e50841c4002020425598440e211a40303c1554940402c420b0901000181c901c41941e9409002c0c494135503900b0043c0041c0d003a6140ea02a0f000c2c0095549107494a05666 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 449644037 1250 449642787 449642803
    0x103060609150803040b090102210304030212180103090203190b0907060c08161505190c031803110f03041401030e0d0e010804020604030218070207090c05041802091002 74
    0x82460b00d001d826a01c4400140400012a190140650b1506062003c404116401040b00e1030542c81034010b901044d001d042080c5941400740d840a94482c1010324000f13041106074800c00d80b09070003d101c1c24640c8006000780e40b514040909002406000c05c1c80840e04007409403045074207012403c00000b00f8805569009441602140d095807001c039101c8205075030a000300c00e8003030015034092202001c0940c000c08103100035402508507004442c04084c6000c240e42c010ac0d8000b0380096224054480488640907074a64911982814841410003840505102c3c42411001d000c010311440c12145280081c8103032500c4080040c15039950780d0311164401070307110f0f004a03202d00007032420041a0f001c41c00410320340201c3c00340e41d6030501020902001103c2c81d420107402645d1104c1c0c2000b0001c0140e07610000d2442541075050a62a41c4c600302101905100c080d5104200480c00d1807030003002580c3c084210b90580e00c44130070110b032072440a100fa2009005800c00c80341c11000fa00c810b0030b0440d40000300a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 449645287 1250 449644037 449644049
    0x609010e16030c0e0a02070c1701060e011512110406020106080717030f0304020310020d0902010806040501120213090b04050f0714220b040c1701080105010503120d1401030606 77
    0x1401030103000314500e22a01d85200c003500d19040d60005105601050348000c1e00800c8200001d41050081d4581d04040815030b440940c5003140035608588024007030041a0040c582c48c010035075a0340c0350101d82000c2c05003401c01c0408002c45035082500310300c3c05a03c0300c034801c01000034042d00d0315210385002c0d0003001c680c010424a803007560000107c1d61000d1140c4e024000000d800b543c14540d400400306c2103904094000c90303240c0182d4058408911103031000d4203444c4038001c2c2c0032076000d81d0350001529904014040900031402c00005212551010380c0082c06c0c594140c9400c11040c0840c0a090000c0850440c018121171080d000c3c0000e00000280d0480008075080507240e00690380e8002c800c0d4085201100703908000c00301c40840c220f46020061004940841c40049682088540060100c6181c20910000b03e440e060f05c69000050803038840d405408032100030040340d4104800685c2e5113040c0806002595000920690b43d0306494004c260341c0c00d07107580c0720355803542c5a2400030701901c40c9000344 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 449646537 1250 449645287 449645293
    0x20102070801090305090904030e090403030b040b0a030c050d081c0c08131101110f0f0d02100e0a0b190501080d1e08062b060204080d0513091d0609010e 67
    0x11406000c18410fa1683c140d040d11a986000c5e1940c062003890780000340250140050381440c4402500c52101c940c0c4558441e503070007c1d0308105941000704496034450a90b0080e0200c4030240000313001d00d10360b0703411b40d00d040329411a18221840d0400300c5100d52420b030043c8001a00c0fa60b40308444603003118940700c1c07580c2c4070340e403480c5d47d50940c2e50a02200303000e000e40704040d03151040c40300c0d5000300c180c8803420f01e214040d500e030b40000010051801310025203107089540100c1202c0000384d41070007500052841d0107030a02a40006401e0f0a6031110125005841e40024001050110b65400340300001016406018080c40da5102015034803000c55064a50100ba100854281e0644503801d0010340721507a62030703980b1030340c841500740804204c0c4c01d50000c810b00101c120180c10a1841d1000f080e01c0c0744102d2000d41e51714101800c80f41040352440300002440001d0000c0400340000e0003000058804183c400607544030324034035145511841c0c10503c48a802040140000c141c41034120342000c868100803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 449647787 1250 449646537 449646539
    0x270b060103060509040b070c081213030905030109080d240e1b03190b0609121608070f1a0d060303110c010e0d030804050f030a02060f06030d0903080c0120040302010207 74
    0x248102d04e007044400810100c02000083e800707034007921100e00b40a00802d8450705050009403906004182502c0d903550014480d0029003c0650102c00400600416002409000c40f6640c40c00098011100c07036003812501c030f0701800d04407640410018060882e4000240b001a660a500951640d0070380e10f03800f01c2d0a140c00010312044e003907011603015181c01110440d5000d200486140200f0420f0000c80d1302c07440400020f040d65403802c102c8c441003601c2c00080d04ca1240300c07414074070211030181e00089842e0807203501007100604200f940d00c1110b0800b0100031014061011071801c9100e0103050056552802d140407003455884860300c0004031040c41124205035402006448846180c606540d001001588042c00244a400b03219003003031107101280c02400c1038081c180e0440d005802c1107801603110404000e800c10414a50303541044003034019148051180301c004052650f6800042c1c01e0f10000510403000480940c40643c0d08500d031120405150f072258448072050b030007803105a0062043c808 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 449649037 1250 449647787 449647789
    0x31808030906030a020a1107060504060215010e010e070908010507120c08040803010506091f021501090c08011523090f061623060411040608060712270b0601030605 72
    0xc1201c6082000400b40d0741143d68040d800b40282d480302462800b00001c0324030001500400b0011240070f08a10340307500d41c865042c117400910780424003902c1e203040003c50b001040544c90048006040d200c0000190440742d5a080d019201c503841c1e580212030541ca003070b042104c0b541d030100c04400c0000c40c1190500c05070220120407280c44000340c60213000038a0420041200e4600203000389500c4001a064000701d5110000e955842032100c511074001d41c01180045081140343c0305084d0142c8170300c01080000c0c200d414070040c0010b034140035044403c80030350000e1031032074084c85141040040058071841c034103c03018035244081c0c00541c100c9014038004002800549848001d03145072070b601c60701c00da02410580d12032a981c1d0218151507048030301c2042a00032081014000948918051030703246808103481e0082c003045484940c09411642c1000c03052028882c0d000c05130100c9118040d50110342c402d0072940701755076040400717000107903040c10120300341c20801d901490f54403034242600e04000d40c0380e07200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 449650287 1250 449649037 449649043
    0x15030c0d0908130905340302180a030c050405010b0f0a030510051e011d010c0602221e23010e1516300302130302040e010b131104140f0d031808 63
    0x1b502c0000390340c0707080d00c103020052007035010340500138010341d42c1c1c2d071400111400300d60287c0141c1c000752801f04000905011504140c01090b00511071183c000d031800c0e03160485540c2902030280314404060b2200c022800402803690400c0c0607200c010030143e40002d80f400081c0c0d00610790207600d8041441c5404200c8c56888514030b2984a4806846d5201714503507a0352490022361003e0701190080f080c40c3c001070140540038071184041d00000c03207a8400082d9400050320342a855a2240d10010b001c1c2051084242c4c40b010707011046042030806101d2905c5003000a40000645c140c0d1658050000c21420f5168507940f114004141c0114071004c0a80e0003070360b4010910f500c1e03540340f420b428000c0f2100000c40e4440c1d40103001420140200a6185407240d00040c1a1041c840305020aa912a04442e98a04d03216034034096080000301d08000b50407400c074850b81e940c0564440c0030307203244680310803c4054846442854480100030106400c809081c50054900d2b0107002c4111500c509114003c06c81d11000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 449651537 1250 449650287 449650351
    0x5120d1e09050120011e1a01120f0905060903070b010512060726010603020c060901050420040908161a09060a0b030102130801060515030c0d0908130905 67
    0x81ea10440924140401941ca0044071144803000b00c4052210041e2000284205c84100d65040b0081c00999420204141616503504410101d2898158a185283e03004074000b200d10742c1800780420400c02c100d1685008100c44c0d50302600c2801441d0800c0410380021009251091144040c2d05d120f0342c03190f0900950b890003a03281209a84644089952a8011030f0080d00d583c01c2514408000c079007044840032400b00a90102001c2900807640c2d01c07031854180f202c01d51210303040380200128500394a5450084a040f5904c032644640da83c0146400d85598100100752900203890035501d0441c1c000010f01e6200e212020f0300c031180400c802c51551441e4136441801140f00307800a12550302c40362140002016a80a0344e13500d503500b08181410196898003600c02007084100029206140000b40100103009190213004483c08104100006219409855070a214940c0000710f0309620718000401e032045208030003d1441001c0b000031401d01c2c40c1c000324841c0c07003052a191100c00b0502182143c1000c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 449652787 1250 449651537 449651597
    0x3031605210f0406181703030a05150108070e0307120b09060709030f11040603051e06151c0302030f040b03010801060b0a020a03081b0a08100512100b01050405120d 72
    0x403c10080290f20b20650a10340512070208403159910754a04c0300f0500600e403000d00350440d070804010008030002a02c0303074541c0f10b580035003c2c0058001d59000201803250081600c1c051011a44141c0d403a034808110044c0034004100c075010a9218130301703045001040c00c9402651510403a000100c05034440c100060403203600624851a0b00c016036504031440a00078040c540190780c0390000004504100305052624210300318080800d0343c10322001c3e0800c2c800602c898011610321003203d265407901c4e64100c000a40926410003201818130f022404e61203600300c110701c0b02d40085000700b040b4244c2402141213651690080160325580e601e5010b05000b1a900b01001da048400880301080c0582d960317503800100e801168501c8560b0203042105600549290300002d0074100c10032646200c11a90503010300b008039000a0700c0144082c0c10b590f00d4240c0c0006c03042c0c036500d40900580c130380d00a80544002d400c0c01821000000000b00031950745038440e4541c8400100901c1800b410039440582c05800400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 449654037 1250 449652787 449652817
    0x8011b0918090206090a120b0f06060909090c040c21060b0412061e061403030c0a03110a0515041e0b060d02010e04020a0207030318080312060303160521 67
    0x8494880c040040c541c00c2c00070703030b0003007002c10068a95545040d9030b0006890824200280c00c0b50310300380036440102c0248030040380b0741c0200038001281e503450140d41210308201c5180500303030341e0441c0aa040010a24410350054105188054000d400032030210111051001103c071103d0107010340400d40301584202540100f0812003808003018080220032001c0c01108003180e00d11186c0d8a0001c0d00d111217a4180360300d070b6076800500c6a000031aa03070000d00041100110304001c5c18031705190b202c401c0450000c2c1070104034164001800c00c140441d10310642c201040d14603807800010302c1e500381c01e000c5408540694190f6000d80c003240e45400308007691500280d40000660f14441402032580d161b00003a41403100e80c48070140c080e620740c002000c0403405a07003d0b10080c1d140d850b0107000180206100861210288800d10803110300000b65207880b148444100075070f490b0038000ca401c501c2503040c03801c1a40341c0400c2201c1440030000303088401100410b0f0511050101000344006801410707a03082e9920 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 449655287 1250 449654037 449654069
    0xd0c03140310030f0809090103080c0c030a020609040c09081203070801080102071112070b130e0f040b0406090f080307032004060c0f020105120708150f030d0f05040f08011b09 77
    0x180024400b404e0f024400c42005107010705070400201c03556403d0f403040303400d00c0c4006480b401103034092001881040b8250001d120301c9030300c4d50000d1090300585070954056982da07451501c0e10340c0f05404510080c003080040ea0003e02190020030300d582d10031250030300403454100000510302014801c84086580200f962810381180004003c682c0d03002d00c4003202303180b1545202054041c4844000c2c0542d8540809160740d46140c200307402c2103400010038006030081450100303c042030091011940c41640078100180e00400b51030f00c0003c0200980001d0301c070700320200810900c0358041d03021042e80c0e010240d03940141d9140021400c041e20450107590006482030a036600000e0113821a9a039641c4141421418a03900c98440812560304075904400641030f27205000c81c080b40c01c0b80b070100d6450140d03040b00c8070030650310109548188a110540030800c00009182d1198812030588010742244190002c00130354940e03c05019111011b1840c2c40e55440d8140d50000e540202402d40407118039803e046425 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 449656537 1250 449655287 449655293
    0x32d1a06010f022508070b040302031b21031603030c112d011b05031603061a0c0a0510060503060a090c15090513020d1415100c050d0c0314031003 64
    0x814401c0070303e0401e408004c080400d09103070611040f0050240d40342d690b511949140100361914092034400c101d210103a031102c84044c0c0741e451012980c000c09c1c0310100100c80030041807600d9441003021003120304c0902842c0c1740405a01da0851700c1b000046594030200b10003500318003034590701d1707100c10040170440c00020400f14560001c3c0c0200c3d442000b40000500040b0515000700c00d025800150000810010070010400002c0b4000003d040f0b80749000c0101a04000070100c440c2d2420b0a002c8000502044090386180d041100c151140d40c4801501d0003211804c14240c0a4855030052901c24007a004c00103100d107045210b908202070300301c011365100a14152912602e140c1e8a0391800802c8020900420141c442400b0780000b424014001a0740ba01c00c96501c00031154a0320001880550342d1041c041c00c1212041c074a8000c200443c0d410400070492542078030007041103880100316010340508108090740045c89408030310700070384070340f0140c020002105049100480b14100c40c000d84170414404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 449657787 1250 449656537 449656573
    0x14010e100f1e06170303010605040e150a0801050105032503020f060403052b050a170c0d0501090509010c0c05060c030c1c0c11010213032d1a06010f02 66
    0x2014820100250001c10010308560b841e1402903a81da22503100e100c20403148055150991104a5840180d419541040c074002d10910551203a00700c01c10f5080d0110b00b000e94001c03024200141d0040c101c0928030350382c2c05418060700b02442100e04c03e009511103900450300100a6190040391440c000180505580c204440f409002200d1504201d05103c00b00028404002c207510a0002400d19140c00100f001c0d0800007a901441ca00b0401609110307512010b600a105890b100c00009400000d0355143e1042058900840d4141c050560030040000341910050780075030b0150080704020700414856603801c1d01d0b40751009000034982d43c084000101c01e810b002c00550f07008400340040c946024072040c504c08183c0c83ca200c601039410b0340d50406030340042c0c0220740c1c03075100a4004002c0d0305021400074445503080403484043e05841e0308007044000709600e840c194540c0345a044140004001c9801e082000d042d65003030b01d06e06909242c000c00e6080d8011840004020080e40c010880e04000360708100c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 449659037 1250 449657787 449657801
    0x80316030b030607050304210c06050a0e0304030c050f01231602090103210207150e040f0e0601031b120204150f0803070512040503061f0e0703060314010e10 69
    0xc056464081c1a5199410f00200740681040c0ea40d060f140c6c1414103202e0b44508994510007207889040020020258016101d182103541001000800c0d56504030768001a20002090524500001402200f0402070041c2007040c1c40f02611a1800c030006d40005450340f04d4034100c10f01a60301c2c03010f02c2c000011801c03801000319050381c4000c007205406503400306000300401e8104070341d4146a85581c0c01d120114510030710341000d4910090800d18030b031a4007c004480e0981314402000100440c61205444640044040c80b40d6144100300d60150f1112442d00c441081c00201d52020b0b620641c2d441204a0405040540d6100300303034082c4d260040d908100c0101a690486401f00c100700d1800030300d11a030700f103501d0010852580519541e0352146081801c01e4100a00382c0ca0015051109200f292030005080340d026200c82040c0d141e01c4182c82110340710038156800305003552990810032a09940c9504500e00b03c07403140f141c2c01651800182c0440c281e64808244622036840740300039600140090308465 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 449660287 1250 449659037 449659081
    0xb100b0f070503090414060306133903030503061002030405010206011418010902030a0b06070b0c0a02150705040f0905090c1323100f0f1e121101090f030803 69
    0x3c2d180101d56400300b41920064030348200006040020005141001d00406a205a401d0707081343c0c0800450b5540c4a8000c0d0000001240208103901046c1d845800e0403e00d01c21180302d0622510181c7e00d1400400550045803241d020314a407604031141e0a000005580580e00140c01818690b800c200b40c0c012a801d20310003465001d003101000b103828420fa248900c1c064100c00001507660300c0c01c90550415103103105655401031008010003001708008954440e00b00d007080c6c486580d2041036520481c900510160303008000e520000078000d04030340142c020012104160780407030205d95103034480e800300c8004490401d09504030208440e15854841c4054101c103040310300010f0100c01654883c24004a0542e03020b0b00109048180805042d003948440d00800900840464007401e0400040001c6149d105040754610044214546aaa40080680039041c1c600c40c080c2142024240302151808001d001400b24140b81340128070654194000300950740c110300ca080c9181c48001e480540030042225103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 449661537 1250 449660287 449660293
    0x40c15030b040207060b190302030c060c03070506070201140a0204150c03020106080d12060e0717060303070b040f021e01020c0607020301110307050316050405010e040f090b01060504030b100b0f0705 87
    0xc030480d6a144013602540d0b0040c038002411000032414000c1e0842044000c0c540b4501d608410001a0340010341031040c00815121140c0b1142ca003100c4601d540250a0010294000c40c01000700c119815030004240c0d41800011650948075891b100040f8480c9004000010000c07102850b0300e14013481168180c03c1c80b0f4800040d04540c0c4021050030061500780c501c00042d6220616240300b0f101d40103080191040d4500c050f52410300b1440070704003841c0c1d482100030300c188010010301e680d49e051003aa094660001800c03106c81c6080e01c0d00c130b40c0150112900700c0c0310388a2030364040c020b0710002c2848814024180c0003415142090000c0020540291404070303895900e42030001c120864a8002e14003400c40354407053348a0802c5e40c002070210703003181c050004200c0140b20400c00e82ea0300c072018070705002082d280081e220459414441c00f5004001010341100550000010010b0b4880c00900480380106020500c0341c40350200700e0011200f42c810f212031a5018080600c00c100e8100090102078410422 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 449662787 1250 449661537 449661551
    0x60a050108070e03070605090111010b0904020d110319020301150f141504060201020418020901020d0c0f021008070201060602010b030a03051b061e09061b0a05041802041409040c1503 80
    0x20303250007060341000c3c0000d480840c6259065802a04000c0708a0ae80c40090042c1502d00010501102c4001d1002e403003412018882400d000c000004010711030401307400d0380c00c94140d5402c903e215100030513040380650300e0100c0c0440055041c10900055810b4088152452807400d40d40c600d58204648450b03a02600000d08001154070300d000510060145800150300c50f407600700380825100c083e99150000c9401000b407190b00380c0c3d0101d145011519a0b007000c19a200b124100f000011288402c000d4100c11038401ca1650b4980040c2c0301403144038a90300a00410f915044201c0c00c0e9038420440d10342542c800384046002a001c2d43c050000011001030300c680f1306920310820b91600c0c0003602c240d00b18800128116160040d081845540318420b040140031031304000001508103140c4152100640c0f4003c51400075031480380046070000d1500021254000303848c5c0a000c0d0003507015106005030411103100355001030030114000d504c5607800c010701406103880c00b40014074a03031902c2010000c269807200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 449664037 1250 449662787 449662789
    0x30601050922060b120706050f031305030a090e0901020703050d0b030c03061501020d080708131502040906091b02100f061d0916050a061214040515010b03060a050108070e 75
    0x80414024000c0e0782c0490704104d1070741801110300c0302c071200b038004d41c000100078080a034000d421a50130364101b590030b5a4170780c0d0b07184039101d107440f00680080460000050500b03010703038400347c04015214080a104980d44810001500300c0c41001801008500180030048004255234032800304c0c003401500741c54140c0d0811002a0400e0b03000c5820503921a00580140d0341c55a04110914600e48203007408421402c004801401c10307240107084030500c0505c010401c08200d503906400d4071408650b4019911a1b48429800d005800c05001c0c01480c41e20300001e0b51500d942e80800d90200545035000741c80200c4001801c04041c100400c1c0501c03400d903ca500014007004240b11200210385610120046c9090400c0090709105001e100f2000c0038040ea5400c2c0129aa000001e80440b211070804a2140110307a42e5a000f80019001c8105000884003c02080c0040469007669001c1c90880040c400d0703803a041e022070f041c0401d070762a40c2c01402040d010b0286500550046400c590300b400c010844110ba04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 449665287 1250 449664037 449664091
    0x1b2003010b2209080406020d030b0d0c0e0402010207080d02030d140f070809030408070603020705010e010509060c07030e0d11010215040c030b060402280906080135070b190c020306010509 82
    0x94001b10050b84500415a2801e40c5445080f2003408100d50b1941282d03c0c0d601d0700c000c0961603014100031a07484038040703802c42e8000c10036a0004c00d032140940745400b00310030740603449800100180b40c000c1c0c01c00307640311402c1202d994120720036170081d60b003d801500c5681003210700380720003081c4100a2004210220301c83c0f40410682c0003c4c4003d540142e540da2982c0340c00b41c00d548140103868203ea041c041440200c0802107034055100c420350000c5a2201d0960030100c98400d26860840c3c1c211528040c1c510900c2103462452611500c01e80803076802c20f065145071300c411902140c0103030406450079400d00018803e03950817600001d00800150030250050b040c4840070609003504070003041209811721000390001030420040c00c99040545403580b4000c080d1001c8500305031418001000c000b030800015440c500e003803401c0c060142c21541c840d604c2d104c102c022356200031600c0c903503506104401c100c01071041c030131040d00981c0a4081e1416074070700b00078041101307009811010070007124422040a170041d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 449666537 1250 449665287 449665289
    0x506030a0b0108480415030c05091b071e0803071d0301112d0c06040c09090809010c0c2c06040207050307121b2003010b22090804 57
    0x30300080c00c241d0704800400c0824480b04043c4400b001c406a100013400c810300c1c498a0342c03960114018103c444050800100244038a6071175103501c102070080070042c031424082c1e540a490781902c1c00400b0f901c0b0344081c4020b11441184168801c1c03001c105d80000100002e452030074400251884240484d00c9654101403904206c1c1d0031400600da004003007402d50480c49490300d016100360000c100300c1501c082c8100c00c6105078426a9904078014007100441c001d115240340d005c03061143c015494000081c030b5151910300c291400e8810034808680454851202d200341c8003074990208075280350184440c015034041d04401d400b80c07001181c440000609400c05480760b08884407450801d0328050f00204505250000030b040a80241d2041c4520400200000200c807101601b102011011168030107084031585018210681c086003060400b130f04104c80c1404100f0403004110803142100740b040145400c030350305460865409a40c0803030000454540d0108981070704802200882c01404686840f406a401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 449667787 1250 449666537 449666549
    0x2210702031f05041b05030d050c2d010f0b0901060305040318151b0305030c07051f020307020c1014090d2306010b04050604030602031305160f050a180506030a0b01 72
    0x243c1c000c03c401c000b014101c01c04882c80241c080d419081c00d140c003080d40d65240d00d0603e000d10800007000303070300381c0002c100d140740c8407050120069013100301e01e540d10104030350101e0510066080100c040c0f00549580164506a54003070a120041c2c0c2c030b0500110094100039100754244004146840908c80385501150050412050441c01c1e280c0c0003040148030340c43c080b0342810140b100414420000b0781c81402c89410649444410307490b08a1410311a080c0060392038424000d2000391f1480c1c0707640c04c5940145225090503029926448050018881010b4205410340c00041e030b895071100781d499044000d8031541c0006000c401c5507111030703a41d41400b0544080c002014108080328004141e05c10800c29001d010281e080134105440e2402055060086000050080c2d8020000600400416130340040c00e0340c200044038460548403c00101040d041d005002411a24420206150410030100d40c111a080d00c5003c1403a0021864000200303005000c00c0c0d80760145003010340104035442c1e0524003a00d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 449669037 1250 449667787 449667791
    0x90a030807051e19020312011707090501181112061e060708040e06120a080706020d02070c050103050c090108010306110417010b030106170a020906060d18050d02210702031f 76
    0x21a00c03080100401e810051300440d0701c00c002c200c5035021071a8a407411121028600701d2881c12031710603582003035426002658100e1601000041614444c00104d20b6215954810405d62104505000f00ba214014024213495440c0740840e082d400e04210000040402901700000807605000103000c60b401410107844154001c00e0501c04e29103403410700e6402c002d048540380500c034600f01050b5150308078130303001030050403000c42c0c3c5c2c0051214640444403042d2142d242103507200c22614054407603946600070709000030b20300400034500c0c1d1803004c202c500500f0140c40e00321150386180d640801502407220030400046e01440009003030a101d4001d418005417078000414680f140c001030508686030b030760055100040417840c001e81082c02141c0641503940503540c44030195503000200354588544584060900d2070314030020fa2451020003c058100c0c03142f01913504900d41550708980d605014081c003140c8421869445040c0c50103000109421480501541d80c4e005081c00c44903170310780c1036000e20700030703c0c0e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 449670287 1250 449669037 449669047
    0x90d230f06060901060801030309030b070203040b04030312050109110708030a020702150a081003020d0b090a023a0c0e07032304021002010c021c02030708160b0906090a030807051e 79
    0x1c54403841c094050219864201c3c46da40c950f807001803200c2c0081c4005841480c05202140010f4401d100300c4001d003002110040ea01e560ba032800508207040d200003081d24074030b0403001141500c2140104040703100307000c0d0791a05141c0c01c0e40b1441a69030014180b036041d59800c0000c1320040e101e10148030440c054031441161122155040500403441c002c10102104490050600060f900d1160881589400050021890391601c2c0407515000070030728060b42c020302c08154180700d41c01c1e05c0f000d07415103903001c000300303030411840550049040c0c039200c00200380b0b0441241c24400c042c003004005074002c495250102d000709042c1c03450280340d0303420341d0305812422041003017005506052040b8980c6800f14030081201389803584009484d040c0d4000c0f09a81d81901685c81480944200300f070360780c4503803c900000c0c3e41e500340c04000d01100c0400e1404850302c401c10800901001000304007548100a00c0b00544030483e040e0f40d084031590f00c001c01c040e05114051101035814104c1c3c25a03864441002c2904507524 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 449671537 1250 449670287 449670289
    0x5010603050f0f0601020d050304031b08040f0b041811130b030109110702090105120a0203010e01050702060c18010e011b0b010e060d0c1802121317090d230f0606 71
    0x8428000c0c80d40d0f00000e415828840c599030300080b03256491400f07160142d06c9848515044507210809001c0c00c80440c510500c0000b4040b0728001030040303039202c0ca441d000c1e00d503481520070b6280c0541d11514110303401c030301c8019540203003030f41145c02d408104280d02c5142a2800b04540c40014054000454184010005010001c581e2040e0381c0c025003203180950030700b2016400a00e5100d014040c241c084d4115400b651159101000b00c1842164010300910140314650501070080c2400c882d2100188900c001113504171010800f190a09145001c024113040c9e850401901c2c0301d1020640f16040020b500300e252041c940400794001241c0c071410390500254501000c0000240001e00500e02c43c500c003c0030400010b100200c20f00469039985102401c1c84403078400709000303018907240080ba6482d44420401e00c04182440014401c3c414000c0946090714003240030103502410101e0390304440c070006413001180003090340c0344041480d504511120340c0d80740c408608100d08442c0140096124000780401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 449672787 1250 449671537 449671561
    0x807030f1b0e16030e030c010515060a051b071d0703060e010b0d05090c12163f170706051503061305030403050a030e0102060a05070e04020a030f0501060305 69
    0xc41100311040980242040e101c0d075000350000d0811000300300c80e4030300f08003981d0103074102c110400d40090540c0c4d154000c3d0502c00e4081c140c02c84200504405851400304249464010f840c0084032954440b81031a0211207502a0f0200d4010100c0891060000005440c8031a0700041b6004c000440c0809050a03c0000501907900d01c0e00300001c020510b800500820b0301e0f50094443c1c1c10103d407000300e4251a0f0840340d500708150120807a800c09040d44120340804400030b42a484404a0840e840c680740d5a01c4c03d014126041c001c1c0742051610000000940c03005003c13607034550701c03031003c8000c0f84283d9030381d543c5072610700070082180701201c04a20700003400038a110712603010300c100320600c150145e4440007945660005001441001541d02c004040c06010011b4030051a40102203e45075101c2e81005042448900c4040b80140f0400c400244d82c8600d5005181c05040d060f1a0340b940c480c000350410002c4c1d04943c4500d0205073b034514207001c0e404400c1c06464000c1c403180c1c5000542c0d0508900d1001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 449674037 1250 449672787 449672813
    0x901060c03020d1e180b0d0209130504081e0d060f080705041b0503250201290d032601090902030f0601080a0206030c0706091b0f0506030109090c0807030f 68
    0xa001c00c01c03214601661031384a04901c00003452411100c4082c100704203a40c45240340c0c018840708140403504240400072a80144900c001c200d405582c1010184641030686000301d400525461007800f000c9151684184c0c05d001b020300e080d20060411694030028000c0300d06950202c482c01c44240410048032805000076400360009032800d00010841d2249140301411840c0c40f1010484e00200203494a01c000303004c5408a8501d603400c1c1c1e550354503104000d028184071114110080000881803a200d0200940c24810304c070301078a02d015190554070b0a564880320104920742e07404d090440245442881d0840303601070100c51300300050000d41c5006040ca00f407000c14103803180340d00c00c00041c401044001207240e080c990440b14140c0d42d84d44c1c101d000103280601030004001c5420011544104642401150710405481c0005003900355141071541e003610062040d030390019030030801406540780c2d0390000c240320ba00610071510302a6036115514605039403540f09644d203c0344048140704000e45102c20744 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 449675287 1250 449674037 449674063
    0x109060203091503070507051212010605073f180b0304170703030207060e06040311070513110403050f0d180b0313051c05040504110307020a031b020901060c0302 71
    0x250034200400081521252480400f52496201000044499110b0011140d186901c00c0503140c003918501400c9071260441810038042607119000441c90394070840940d1441904017500c03200070041d250122030f03401c07000004544410042c0008540d079940d01850f03400d09200c50795070021001a00300d0b0300a130100c0507030020700f0400030800900001c252441c03150741c8a170f12128540382d034a403402e2a00f90000d2007043c00007000113061a6040610003004110a803290340283c540d007092880404100ba1207d0050058503400704800c91451002d8000b43c1c040003021444c030b42c80034502034484c1c541700c3c0b816400490f142031544c4102c030802c801e10341c0502400d0510301410200c00300d81c1d05061440c526070200510f0340002d0200da4480c1c1042c0310301040b8405400303146110540d41c0b943c0d0050001d18030340c8203029032402039040901c400d0391000004101c1e4883c140319409801c6400240d5822070b10b1590707029044031501c1007065607001588d40c0580301402402c140d141d000c000d5100c0c0c40c0c040d0518910002da4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 449676537 1250 449675287 449675293
    0x100e060310030312020316082e0e1522060b0d0b1509100f0c061e110f0a0c0c03050607020a020a0518010902130e0c07111c0b0c0408060703060501090602 67
    0x80b0803103001a602d08020180a41000d030f1450b9209810070404003270815590100c00b20b01c10358000c0b8007080400c0e400554040840141d00b560f40c64091054480c0c154403c00d0300410741003003841100307001071203540c500e110304400850140d40c5ca9141001e560000b20750f80c401569a81e03444240d5140c04803407003416501e0251002d0030308201760005039015a0b001d0a00f01400804001c400e126441181d441c0e15540d0b114104102400100f02c510226480b041d40c00c0812600d816441c01240300b02c0fa080e29611107000000c10710700200594115000c000920080722001c04c4004080006142440081d105500d260300a0082104d01e00400281c031500cad510060003031307503134280c0442c21045088070b4030f040d2003039950050382c3d0b4400c01842100140485d406400b4804020702484000560f501c01000072038040e48244202400c40340410100c3d9800e2190902d000030f0051420340019107940c000c652140756203140604040e9180907150070702604440050000e99904010710440d078102ca41d074800303401c0d90f01c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 449677787 1250 449676537 449676541
    0x806060d0b0705090414130318240203040b040608042102030a030b19030b0103150c050301060f09030f1a0702031e071112030a11011109100e0603100303120203 70
    0x30318010000041c1000b81000800901c410b8180c540d5000328015900c40888010744e8a0603000144604074002c00840020b084800e2000154000082d08029178007021484881307220004103041c1c00020a0b0545004d601007408000385d121204806403005003400e13203844182d85814500700120030f03840f2241815041440a004032459800010b480d03100000d81800140c02400c440003c40400681c3e00d1111208e06089000c010018003a48081c101c2c0e1144c0302c42042c3c2a04110400e06440c1041c070070100007101880100300080c89000c08106501c0c0a04140481549076104c89002010f101c10660381c1e01c002a50281c01c0c5411000c1c070a81c03164039440558100040d060041040079240306810024903004074000c1c007071100003420400104801032011594240079104a40c50380c102411100200e6460500700d000b00300180610709103442540101450098040108803014280e807450408000091490440070f403110b800640c01070b22400c2c0c0040040340b0710b14005002285d0008103900c0c00b401401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 449679037 1250 449677787 449677793
    0x19090603020a050301090507110d02010b0103050906130b04060e0d09050118060203091909091a01080606030606010c0303140a150503010902060714030c0d0504050a0b0c1e10060f0806060d 82
    0x5a90546580d1b640c0171a0035140c2403001c0b2114039880d1031100050041818070044540c05502412800c00700781c905003d0f642d03d807689a0744600b801c403546040116440b03482400a40e1110a06a004d4403d0b200060384203d41c6051610b40114400d40300c01240c0034103814082ea680001030a0318642c0c80e410080822401e0203c020740301c2c0075005005005886030804d80d501015040f4400004c2c00315683e04002030611410b2400c11144045088000d00d55441300100c0c0103e008034680b842440050001d00e000e46400004490b140485101a400c00d60749500105042c54401c1e01c041c05106012408140c8214003484000b510344198001442689420091801611840c00362491181c1201d04411003110000a0a042d88501e029210950180f00c00181010360040003420940d41c058a1041d502e513240c41e01d54070640310354105411658040c40034412150780641443c0c1c0c100d580142501c11b0207031a60f208205445054004400e085a400360078040003d041080300c0e0300ca90708442d20351007a101e81c1c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 449680287 1250 449679037 449679047
    0xa1a04050c090712020711150a022107021909151206020c0c060409061a04211712180a020a030b130206030a0905070e060307060e130219090603020a 65
    0x10321503601507041c04001036401c3e4050b803650072034a84c50303910a40d5620790724503288186504441030300e8440c11041c4040c0080006110503250440c00b16001070200409010110006025200c20402051800c0000d40c006845040d41c0907034100d0f05440100845040a0900c01600c1d84600b02c916000b441035001c100846001e808410303901d822110040e030f01d20042c1e41c4542031503c010301c21a00080d0000d00000c0700503035544103078102c030064050000e00240d1000c080c49030f44264030920b00310b4201d03081200c40d0701e070006a070401080e100d04040100032001c402c080130241c1203a0b81c104e110710082d0080140d4260241c141c1d1403503141c1c0601500e480d09060b8000f8880c41110702001c2c200250440000344145e030350f10114801e0a4000304a540c032842e06108441c003804c0e94060840d4140540100010000c0070380b5030b824040e00004000c0c1003e10b040c42411640d40ca25408401c0d8043e054103a01d54035160a4802003601c0f030801289103494008492000d044aa102d0340040101351040003001a00c660007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 449681537 1250 449680287 449680303
    0xe060f07030203160c0f170c0c060702010903110301090c060c030e030d050f0f0d18031707050301051c0218040c0e01260a02120d03140103020f0d051507020a1a0405 72
    0x2400c01c680c0000841c20701b840581e002803c02404a83c03403c0c102e0320101840000340c03145008802c229002c0714820703414000c46008400000740400c80403101400005c25560381c20185502c0500009016001c5881d04d41700d640c415400300e00811400f5291500b89a800950002d075800190001e21184080780c00c000c104d8030039020b0354032207500042040c0e8908800762085a09010319424148034a0003105101d00356400501d00c128042903800320031040201190000da032180c9180d07119641160310b031000b803015499055041c50b1103031810282020040c0c0d5840b420541e00d045885e103041131440c0c10f00c0d10600c0740b1400e03000112130a00700001041545c000c0d81c0d541c80102c802c2c00c1c000c0a071400024003513103004648070000750f001107045d0035a03081d020005100c41b00b120f080e540a125002c0c4851001e800d0030801c2c0800b0b504131035410b00b507560324144240459006442803040307884504211008100140003500c804005800c4031075400f09004105224100a281081001d0658181a41c13459969030381 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 449682787 1250 449681537 449681581
    0x6050907030b03030c0607020c0109060e01090b130506040f210b07120b060a081603020408150405071206020310061d090402030c060c010608061303080703020f04090e060f07030203 79
    0x31014010415142071007524822a5000704441d00750514002c065201c0d8414102700e80010207040303000601074440c200c0554942c80684400320804d00b04030f000103030780e8031141c0c205c5500c0240250000f0760391208801003006019601ca00741c429818400003c40d0042408060074440c0f00602118000c101c903050560b4001190f4100703401c140c8400044207028107844004103512100204d941031a06402c4481c66115904021344c0e031945002602080c0d040b80a44d02441070554044038040c1402280d6900580d013181c040d808407954680d5035000284482c8080f48104d404580210510035280e80d04e0001d01c1c06407045d800c000c03942d240d2185040c400c100c444200e007440f404000000c10299102401a03000c0d40340e01400181e615008202850b01034441b0303201da118039110f07100c001603a00c01134001542d010795140d6500c03038440d11425030840c042e40106400b0106010200320000300c00741144294441c0c0038850020380350328602041d528001c41c030001c0050040c580104200168440d41840324211004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 449684037 1250 449682787 449682791
    0xc0a0602010b090f04150218030c090702102301062007030b190e030a0203040602150906042301090c031a04150f020f1b060106091d0a0207050d050d0f0605090703 71
    0x160324149117000da04500000c00d01b091000490019000d42d040c07081101d80010b030212005c260082c1d0902242c00800c692110041e0001407082080c18041d0300320102e21200c4075111148092a4440c90148a00a0340102c4c00300d449100d074492080381491501550000c828090100917203903407184120701c20000c001641c6c400800c03121022045496209400c084507010449032505420301c0c0c0a03549a2142c0a07400240c41919208945a0321241681d03105880e180301400c165200c0c0e40e0742c020544444802c030300909591441c0006ca0200034070406003182e00031201054174601d182042c12150300146203522200111908201c081203070141c406244001100001540b441100042c0000740544054141401800a070508481070303d01c0a5203440d01c64142500d0941c0d036922810b440c1100d980c8900e10f014609e886a00b03403045940046a54040503040000d031411000d59030703190130300f0800031005020481c04515600340c0c408038451000b2105162030204071440c00c01300002e08031100184803404042d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 449685287 1250 449684037 449684041
    0x10e0112020f0d150b030c0a080c09090f0d080a050c18010503060a050d080703020c0105130501030c09030f05010c09060e0d0b060103020c06131205071e080f04080c0a0602010b090f 79
    0x82c81c2d00c022030990941050070b412071361102d020440040e00201020078400e01c5842d40365203039840d14944071000c81d01801c0c02000003101300d000340070000700018001000c5001c2e1009420060109000035640c0103002d603109151442d0003518003044a034007a2078071403400d10611440180c03541d080c590009207071307090818035120354481000410407001ca8002c0d07508810381e910f6a0003002031540240101e144607809540403891060011502802007201d20100d4882c510420000c65000e40d00102d044421440c0c4000d120385c80c2e031500e81c00204004002c42d1542c1d90364404034092070340b00d174561010340a18a04610050000740000e0100c0741150005090b4141c58400706400d68080c0d07049410586564017500c11a140481c41150f5000401c201514184240c41c104491540300380201c616060740600c4200c0e02e204107600c00081d2081c000300444445800300608a01418040d004e0402014084020031a101450080c01901c20031584910156810f00014420960b1042c090741e50200c40400101d03015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 449686537 1250 449685287 449685289
    0xc0a0215090a140106090f09050c01020102091c0609020402070f060b1903150603120206100909021302160602030a09020a05150f0c1203041a060a061407060e01060f030b010e0112020f 80
    0x146050350011b0b4089103820300390350010420b90004442c4174010016214040c5520700160b083c0d205544103a0750180d82c803c0383e880c030324645601e03101c2c1690103030200040d41202540410100d910114051303a859420201038001c03c01603000c0c00e64120300542c1d1444042021580400509880c0d0100a05440c1440c1e0703030605042240d0301100065401404020014110120194603210262401c00350381ca01c00001080c041101c1c011081d0080d40035001601110040361140d00079080301c407a031414504402c00c1c540202d0400d0015500070000103000050f03c05280c0304005218085500a40c000c88005000d422181800d42c03e8515100b00c6000d103030780d18500c1140d51410030700d25100b0000300d03c401100b800300380040c0080362a00b1104404925215440381002c201c0e540e601c506c1840002490f441e0b54407221a14803015184440c8140000301d15442d66a5819094401d60b401c00705004140c22020402c3c407000001c1240107110000d545e82036035050100721400c603203840703c0280c050a140381c4c041d100307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 449687787 1250 449686537 449686541
    0x2010c02031002030f0108120403020130020c0705030109020d0605041a10061101021914090307080309011e140304020607060509060601031b0801030f0203150c0a0215090a1401 77
    0x445034001c041d01c030032104403040540250426220408191655000406c0050340090b0400b0200c26411246003044d1540c1d00441d0361703251880c150042440e0186090812000001440c64031a611580160f190030a00320258075201c803940c0b106200f41c2c1400009405a01d07111058020b250300b101012543da9214140b031940ca00d41c14540010810658007040f05152000c2052070569030719594102c1114110030441d4280d0090b94038110289991030041d55241c1c1c020007400041400c10801242800c0c204000642040480e9101c00196007002417611090f42c0d010541002c8031005459110010b00303100c4009010042c28940124040380000104065664a6007600c0d0f40030b43c08841400545080000c10f52502c0b0180c0d10b45000c44e09140080111244090384090282c1c10f0340c0c0c40d40103903840c40c0c646040d564042902179070140980320251200080c0000c21920507a0200f08080e540c51043e076009152041c90a018490348803180144001c440780400d0682c90242c1141540d42038008024500340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 449689037 1250 449687787 449687807
    0x60304060e0303040614060d080d0509010b030a0f050c180103030305190504121806020c27070c030e0402070b0a020c010608010e0d1206050f060d060807090204051c080d02070201 78
    0xc10384000f00c100820045950800c20381e101c500c0480fa010b6480306d00078883c1c40e01c0400740042030001d050060b505c00008a82c0b041d64407003a07900002c1040c1109801003418180f0b510b4040e14225a1a200078042c003d01b0070590490480507a80c400d51981c521070b4000903054180001010544c845006c0703000240e881e80000c608408060702003000f03043c02d00e4000d66110184048a0110714050850358081d0b20920b0402c081f17803181d030050925038030f501d41000b11f0722102c0c81015034188565015040c50401401c151485103080361a01c0d40300c0451801c0140070b8041c10703640103204600400a9800240c2071314412a00003560744c9002d40c035080300e40d4919014028603040800e0039861310528490001000544894918061700ca13646501d00200c1150150303030381401707141d420842c2c4910101041c2010b070014506100102d0380040d0701130311840e1086c20201580d00640405e500440d05004504d0050001002c505a804184a001001e95150581c82c042d00e0b02d00400c10b5404500c0500f56400307040c03003131 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 449690287 1250 449689037 449689061
    0x603031106150d1a0c030412170a0c171008060a09020a2303060a020a030f0e1207031709070609120c0e0901020906070b09010b01080411060f0c0a0c090b0604050f06030406 75
    0xb04e03d00342d11785031000d410440d800d540051200703584004407401602e09214401c40d0b45250801070b505d401100000d0201a2001c0040101d08072810b040310034140c929030700070100c522a5100f181d181403d8546029400f80c00c603081c1501d800031780070041c4c2d20f258602085810018280540c100803041404084112076141d94050150204002c1c03030001e6513000301001e00391038038204052540320f0000b00803a4204440c540450f44620a90410a00c4402c090003401b4440d203414209a40036050703042c82d00700d0945100038590300c018414000c65400055200c042c0240031150360026400791100741c1013900034443c505481030300d0008590f682100703404072080d0b6a0080c01040d0b50311315900d0b201c080180b044480c0e800d594a880350365441588124042401645c106a1400c00400c0d160200803240d440000d00c0740040604128140d1150400e12540055038082d02d904030700399151007031407002e58400c1d4920b20301c1034604000501c41036407100c040012000099500f0754403580c46107456001464030850320 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 449691537 1250 449690287 449690333
    0x7031806050a1d04090c030b13050a1707050a060c090b030c03190608010e0c0a08010b0112020901030f0603030e0312040501090605160503070b010305070905010b070230010603031106150d 82
    0x10705d040c0716460240c0002c0342e07c20310420003256074003000740824449034000113000741c100d01c4001000c900110314644412400c00119485d1104c42d540d00c602d450345081c001c071903035900d8410300e40319550488488401003003140c2c01a403440c43d040400c040103100040c01050111040c01d10b84a480c0169844103000c2c0401d07170000c0040b505600c084035910000304500500c900141100414062818003500300d1405060315003164a0300c03001c1c01782020750000813001d4105a911136440004020078081c032002140252207062000d419901414141030300c000d102c010420013088104003d0760300c101e01d1000c6444525009860720607882c00c0354418910060050001d200100f900350600410781c0c04581242d106204482e0b002e545d42e46a802070703e01c00d2055001c50368081c00040054108584510a81c40a0041e0320b070a0f1002d07100e80b02c2102211442c500003e0f0b43d00c2106200b0190440601480c0000e1000100b0440ca0203244075500d588031019030b6402001401c440000700550185103480b07005034100c071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 449692787 1250 449691537 449691551
    0xc050901090204140609010206040f0f081303302706080121080301230d050d2006070c1a0106030c12020a081b0705010203040807031806050a1d04 64
    0x181c031010b074105005102c141c030035002e0015003526100c0f049400c001070607005411240e844d13440e00802900300c1d06003511801c00a0866400281300d0100400044400042e00c111041c00c41c14020040e051180c0c2908400c501c0180081d02e064010141c08030018841c500030180c0200c2240158507101c6c400547d60a102e40889d02068076504107400c2410f94013900700c42c0480400090b00c2d4200d075102440050410320b0100018000c964280c00c1500c1010000000200d500000c0004140c0710050058240e83c0c50300505c0d00c95004991107012a10a0343c0056401102d01c649043d41c1c03501c9600c094007034018480c00c540060300300004003005461002c04600420f0300b5695a0401030f0142c116810b481c00050008142c0c5200031045100351109400140c4c1e50340502d135514480c034031400ea040c08520f80d200c5000d102d410f00081e1300340011442944140007a1b51506803604e1701401d0004514036070082c83c40380040900c611079025080d1148130700680341444101758542c105400228000301040d402c1420410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 449694037 1250 449692787 449692799
    0x1140112020f010503040804060c0201050403080307080421020303190605090f0a0c1e0f1e090503010e0d02030703030c180e090c040e0c040f15030f050f030f040e040c050901 76
    0x108410045009542d10100d04071a5001101c1600c402c440040012009004c1400700c0751080740302c0aa441e1041c18411b25213902c035140c2c1c0b08150801c44103c40000c03081e904000070046400c0600c0d21701e90901e21007841c0b94a80e03000c040d40b40c0c003000b0024518502c0311064003c403884030303402900c0108000392507520542440b44030b0768162a41195010070940c20101048881840f507113594440e0041c3c003c3c011108902164200c6070045031844440c10030140641020b882004149200002c2d1925140c03c41d2891a01050500303694035954150b80b640c00000a070302c1548d8001c0b0450303180c0c0c0d5040c5000030341844075603400d49210b22149081d861107801c2c2600460541842d1405a02402102d411104141c02d188204010382e20141164111900003d4512010f0300f01508040e00740545d144000c00c200620000c600001441941305440340001c8200c1c0b41d01740141400008488040c14001d14605244219038120921840c440c1010319107241e0006410300c00080194005840000c00d41d1b03926582d241 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 449695287 1250 449694037 449694059
    0x120306190b0301060215011508070c1e0606050a27090606090b030f0c150a021f021b0c06040b0708120c0d0c05040807090c0216081605060309100e011401 67
    0x406690090302c54402c0c14090506c100060301c1c1240d4007040c06031040f1180d084125000300c4050901e00070310008010a5002a41551281c44001d904a0809500842c1420000e0580748180d02060058024100034001c07440c002d0143c041540889070b4940b0b5021040c040c0a008003480303100a0030b80d0745002408699400603400107502040304500f101c144412802d02c50b5250b036094000258418001c5403211142c1400030040c112400e09030050790022040104a1412901d04144d031f000020340c0015060042e0060f210b840c0311040784d00004003d96645100820350911481c0a80750040002141042c10484d40d4002c4074514048220f1140c4142403070707044402c15410088503c890399040106401e81c02d407050381aa0121101c160080a4240c5803116000060074521a40000c50180020880136840c8904114004141003030007400a81440c0c0d282080c0d030704094005521a8000f001072018200c0c0000e441e103032414441100180c1c0701800c01d401401002c190240038060342c005000003805020203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 449696537 1250 449695287 449695289
    0x50d0c02040536150c03040b160806150f1c05060301140612070803070b0114101d060d0e030301362f0d0b01030e120306190b0301 57
    0x25a0144110b4950b1a500000899003c050500c04022242e2051108405a040030202010101902c1072944820229204e1000032107a03035510940010501081000179082d2541c00b01080307440d49540b001010008113000c6014141c14802c0071714503290710300c2198038011600310303c0602c0c507041d985480c4003034151040d07041f011003880c0d02f620b04000034842e4241801140000c9100495005655030745c80100402d215030580c10000c80d200d601404262408104000c01c5401d00465141521350314114014444095131b40606000d080444511101c25030000c04400080d000219010b0380f9100d1503001c201c04c1d00130305280c2c01c0c0041c181030f101c0055520203c002d505039401200002e00f040920b8108a140c4080b241d401c092030802d2440d8180065100d9202c125010708480e0310041c90344040040407800885088801400c1c0030004a0715130211281c4038014001c02c0a00341401060101c51640da290110110070340e2424070004001180c66407403a4440817600b180350074030001c09888a26002c7c1c0c80e042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 449697787 1250 449696537 449696539
    0x131203020f0d05070f0c0306050f15010c0b07271e0f030f020907090b071101020f060124020307050106080d02120306060d0221010602010b0a0e160503070c050d0c02 72
    0x64204108001d040840d0050328a60780343c4a8a18041c07640d66090a02540c1140030384443c00c007048040001501401b616015064040e0110030034141a000301c400e03100d803101d07103505103c081e156050001d85020000e80d44001e0346d0500c6881003042c0d00210103a15402c00c008640c11503201400300d101e0481400852200b59620f210500c22610741e16203005011040c0405803002d030342c2c0050300005180c000700c80c40d440022032800541c4503590f501000f800390010316046036100380d0211410003030350741000021556003600c40201400e501d0249140303422502c40000c25010200043d42c085a030b8020402c68400d1a0311000800200382c2d07a008175500d81c910f034086440180100c88020711100c4199080c0ea0007420010001442c08036040c020300020340c0454001e0392608800ca0a03d4004c00d02194294000c00741500007041c2c1c8580b447c1000030780b0506804c11800d2440f04024003083c40413007c44500082c505041c81039490301d0b8000f0030340c0c0d0814480001480c0e80b003080d03446060310350311441c400200d0384 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 449699037 1250 449697787 449697793
    0x2011b0212070611030c03190c1a060907020d0e040e0c0d061b0503010311010e0f060304050d03050c0a080f1509070e0f01090503061b041e031208040215070813120302 73
    0x108481c00f6a240d1150044240b06c40d030041c80350904010a4070341d030110012880c1070440d0105003990310154048091210188614084820413425041854441d0ba001d811407018210002c4880700c060403201c4102e58140c0201d5581540c175050131400c000c1a002c4910040800150711920b26060f0058a4220306200403101d1b01c0c1d2030102010300541c00e90381030741c2d4005840c20755540200011145004140082948418507110000391b98481e1402180100d005030007800b000851002c01130b082d5080074100301134000e010010b410780e13140d014040d1600018103103103254450720740b20043c0007501c5095455942c040810420b001c4a1908840031040c0c107131050b0350086540c03412800545a1404a00c513950300f5411020002d42008008003180880000300c030640d9040c0754480701600c0b4508680f035012006242000000c0c42130001014440d045038406242c041d201d0300d4180c1c04a500798600090007000301002081d039008006002e801d640c0980c456601624080345d4410749040b80040c00301050300940 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 449700287 1250 449699037 449699057
    0xe0f0a111c0f150c031d0303130609020307050301050708040b010e0f16110118020a091a010f020f01090609020f15090f19152a02011b02120706 63
    0x30801001c11140d0702076145200721640c01988600301c1c004000442120340048101e002d00c00003c10344103010392000282d40005d0104291540451003110b584a094580d41c424010011005031920320210455880031000c650060766101280c0f808500d504040d03855400d1a081119083d805020540f00354041c0d100481c00340d0361407003581c1c9144810781c2d8051041e00740100090342160704210014640a032494070410408201c0d240d9401c50700d03620000b030b45110b43c00703010304190320b4140c030f00102614001008012503070007200703a0403500c031003480da00e818400710b1008025418001e100703406414401100030f00c076084c4149003980080c5101102288104a9400110150b0074820f0101c88048230703001d056031422054408128030840c00d440e181c0d03400403550300c0410740c42e1941020700005203c2d0034400404210800703c050010b0302150002e800b00000c58492403140d00000b038410402580a007040c050500c81ca40d1201d00c058070850010303421080500006211074000210141110803590f201301c00740c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 449701537 1250 449700287 449700289
    0x904060207050d0c1a070e090405071505040503030d151e18050603060a0b12070905010e0c070804051c060e0a020102011505030c060a170c070c06031806090203010e0f0a11 75
    0xb800802d50050200b24500e40780143e14080c5d0352103a0380040d45c90410345114441c00001401101c01280d0869640e0051300301004800d030142e400b0844001d01b030411600f407034103001c0070a0b960f00951414014940d03d4050040903180c0c0d800804020349510989803809859141400102c50a90310427000300c00d0105110487c036002e0f038424240070b190010040d201c80e45800800320058860500566400744640c42c1445c0301ca54100310840003080c1c0b40e030300885c5035850144030508052004003241c8803004104808070000382c4d1041141e06a4408603003419000900c1140070400c441c1c0d9401c024245442c0080c031006c1d0140014101d0740e418800d074024040c805541c014000e1501c01442520b400d5030215242c0342003460003e001e82000c440354941031000170341801c2c680e9003ca4003911104500640018088240704010121401520722030505104103501004208481d8164150150403036540b05407010031941c0039007001284911140c2281d000a144841d0180c0300c0703503e10402c84006e170381e41042d060303d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 449702787 1250 449701537 449701547
    0x30a210c0b040209040809060a08060a2403050a020f0a031b1806030906020d0603200d0c06030e07051f11010513080a030b0a0b030f070305010503190804050904060207050d 75
    0x101d5008038207500584441e424404c4005020304101d407000000e11201805886900190000301213035a1030000c1e5003851005d1000162280c0c200200444151401e44820144e0002c00341c4102503501d00041c0035910001040000d0140c01d29a80c10450001066442c0300d41c5604900c0e01d03580d00e801441241601c1700d07002d42c3e001c00d81796010007000c04110010800240a6400220128000da40142ca0040c4402d0028116501038204a8440000051074007a401f488260911200c1003945c0d044214042921a0b1485400c0e038030034442055229200c400021409001400c028000500045003451510f0428002c0e00c810f00014000654001102034203100140921402524040d40301c42c8203c107035417907240341ca5110f00544024162600310111164851691101c028150507031015103d0500c0c2c8004510017002901c0c5104060820006103c903940105994500568401082041c1074180c644000c150103140c2c0001d1344241c0890812060025680017403103518410003e84680c00f030054800c3e56 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 449704037 1250 449702787 449702807
    0x80f060310090201030213030f140a03120b19060807030b06090607060c18060906031107170d140c0a111b010831050607020708030d1a030a21 62
    0x5403590280c680520010342941c0b1490340c850040c0360242c540008954000007415040c2d008480701004a5410010b0114104c0046c480408403c044c04100c86540c07002403040b20f02e12030703081640b5074400c0152184d650701c810a00c0b649400c0c5810010f00c940c0c0d04000b6050030380c103c98540201c1d0620400c90603618204040722180704000700118180b110340d444070f1000b0a2160b4540d41840106c01c00f0700c0324442400741c01c000400c40303503443c080190300f8400001c064510034040c4100070601170101c03100080f00c640c01001450200c4964a07103c01060105c48060000d405249800168070401d01c4140c060301001044102c0940d2508007118180d090764640c1c41c00124180c8690485032089445250300c00c1841c1078104008241c982c900c04052082c079100007214101c24403400038000f0940040000034000154001c44500280981b20700d0401c0c829128410900c100340300a68540c110171024501590070800f001c40501110a42d03e0b60f403804001c14051103030403012a0040d907506601c51885100303101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 449705287 1250 449704037 449704039
    0x10e1b011814040e03070f02011b020619050f0705070e0f160503270604020406090b0d02010c020d060507020d080c03060d12020109060203191a092a0703030606080f06 73
    0x14809450b011801c2d500b4411018000e610030788a0250041ca42d00030406407448601038414141c441c0710302d02c0094510031040c0004221164643c81c41d02c0960303118425221950100300b814500005070030011541e074031031a040304444160210720b03130051140004000040e141c01c0304076014141c0700c40001c0c400e500d5040fa02c82000845169080e6855071040001e10780000d20880d268403001c411402c0f1040743e001011841c2c0940e801003003000b0030b601c0d09000702c100401100d0020004500c2003804918400c5001c4006410b00c0500d2038454215112005c1000c0c280c0d811500421550078a00c000030340742d407100d107800000a0940004200160007503002c0328000c1c08014074210700c0141d00d55a1003c040200c00d0b0040941d5603503040800071510600095200f2072003425030302c1e01d441d45d05600d001214041141070201d0200e407401c0120540340c02c4400c2d42c000e04a1082c070004201c4018075a2800381c100e0494444032070001c1464010990183c00000c1554116210030035140e40d0000c0700d101c6034100311a15 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 449706537 1250 449705287 449705327
    0x405150d050c0a031a0604060506042d030309032f1201231806090706110a0804080606040b0405072c0402040803041a03040b0f0a090203010e1b01 64
    0x802451600c0c200003410305200340203603807803540b00304000b5240002981c0191600c41110300030070180d40d600401d0741d9004038101c0d010001c4500740408a00240903900442114aa00100485541c1c50780b00c4a0400e140001d40c0740b880040d12441d004020800520007210a00c103280100075960307440e201145816035154071855041c040c0340080000ba43e000780300c80c1045558540d50200390b20802401903a183c10031807501001414070785c101c2054045102000945604610280074540344049001d070204e42e81d0b0701c0d005035410020b03100d140c20220754000003448480d0000e00050850804907401d03103e180103c03400c001001c2c140e8280300550300129000000121a450301c01094408004202100d1003100400503a101303404010800321b07400354100b071410354030126040080581a40d04041295101d02c8104d05505080d42d404401c41800b625601a650115000643c241350315482a030032690005d0090205140902501e500c1c0c2189400380c0362a04005802c0110b076500406841d1b0503600d600d010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 449707787 1250 449706537 449706571
    0xf0503010b03130317090106081204080615010201020906030a060e250f09050406061707030c09030f05120711030f03180904050c150a11070b120405070504060f030b060405 75
    0x125049540982c80880c24445c96190070340781080c040c04801e11410b103843c0005003050030900c0c594601020702c135540000e52010002402000804140c56070000f003203008102c1c02d00a4980142d01a020724a80c1c0c54201c940030003085034164a5401060840b1907080f94082151552038015a410700030301d40d07110b0b110064000902280348a0a0320b0b41c804045403600310806a19040010281c81c000d80c440e400103040601d51b40002c942501c1025040b00b00ca04082041d0340c0f11503400340c8a4002c520014081818805154040c443c00340324100007041203c40300c90303807034003540750403c074440740c00d8038480c024850030f0b8401103910300c000221380c0b656080e0207510100c010b6083c10401d86038001042107a00f8000c00041486a44032040078691040b00c805080e074480f14001801041c50042004a800c00d41c014903080003030340246804c0702c000c8500f28160081c03540d22030a240703262aa4940c000c9410a282c00d1000588082180c0200207883c070690000b54035448200801c025030300c040c0c03100b03903c0e5501d0480c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 449709037 1250 449707787 449707801
    0x90e0d05120a110f0711090106080606160b0a0f0e12030a0e01061d06030d0806090612151906050301090c050433090605011e080c07020303070f030f0503010b03 70
    0x152071603000605000100d110b0300e5215081100390088600e00c0b640c03071400b1525500300007060203810410b0740d05441c034580b80d40c50440e004004103400340c1800d02a039000904144181401d0b411b01c032495401c49014049814424051802401c99a41e0961914948804202488404281c0d60b801507450889613066032513010303c0d080241003045e220000c565039440d0000e8603004024101d070020030160310f50001c074640441414100710300c2d00301a008001c202400c025240e0307150109581c01c01d00549503882c0e81001501100e00d4085554001d02d00500b5050030401c030302c0302c9850105180141e07050309120b415a06da0500d401c0c1d40820900400e900160a014072017030601d80d00004582251010481c1e542c000e180f80b0480011000201c048140c080ca6000d01c1034004500800000302403c0c60051900f142030074190741d840d110f600302d00040122000105c1d2000b2075410a8840041e00201503d907511030340d10301200354103001001200840e41140706c50f4241401102a03274100c3c0c084645581c40c40e51421 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 449710287 1250 449709037 449709067
    0xd0612021203131a090a030c2c0f07090e04140d02030903031c110f0403051b030309091f0609030b011517061c050a020a0b09011706060408010e07090e0d05 68
    0x40c04c0e00d2540001801810f0b1035a5071051124019400b403c0103580c01410200034181a0a104c04070306440c0380c0000895846200081c0d200398070104000b580700c02c9403940b0000300d0782c0d00141e50001c4502e9001c00c041c44140141141e003109414070100460700607074040c035803d90b2240074111507640d06d60024040da0800c03180000c0c0c0c80300228090700001035401d0500075224104c0e00030b0b0410f0581c0a501180600801c0000c2114401c20950680001606054130001907500d2040f51780c03150140c1c51450101d401414008550b00721203104012840d1407039103611000707041d00a13621003514040d0421000150410710300800500c40c0740255105c125002c1420300724584000d024000d40c0d0040389111034000d03140301c0306003200c001c030303110b4000340c105940c444c01046098070641c0c0048128210800a07103070103a800181807100b0b03880013027034558075903a140c00140040c062036000e10032a50130300081101718500842c04009071201103108000d000119080e456861206080300008218100300510181c1403803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 449711537 1250 449710287 449710319
    0x30a020f04020c06090d140f0702130605030d030209031605010c0f05030f190e010f0801090c02070806040f120804390f0602070e0f0f0c0d061202120313 67
    0x251015183c8820b21186501d0010701716001d924540114940e0611994040072032010340000041090520200700045a49417084182c020300c1581c0d00d0350504491600382d0441030040800070252414003028200140180d80481c8805200e03000c0d00d80001c2d80c01e01441c180800b65103040e591300004d440325a40e404680340340c0701c4080c1d030b462100f44150804842140002c0c003084183e00380c441904c58103010050045400b003010281401900007002030308550024180781100c24003100442d440702500000d9041c1081c0f50814020390003464100000c0c0910b00400300c145030302c5011050000c2c1d15141e01180c00074004d543c01010010040f040144507181004003064906100d042612030403051600302401c40300d0356010342400c16103444100003464061040200615040e00e400d03801d0320703014450ba400d01d24014114020340d641e20000c07800c40354188099421f000b003550410014552034401001e0301001d56071040b40b01e010311001291b600301d40841581d048140702c2c43c0c1402c9035818010504005059 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 449712787 1250 449711537 449711539
    0x1e0103050a1712150112020a14090a091d1203010b030406050403032a111219020a2901090e0d030b13020f0301090e0106030b01060c080904051e090606030a020f 70
    0x28419103c020803104100781c015400d540300a00801500f030001361026081840b031308402d83c41408014121038001203a05000701c2c0c121070281e61161410006804046941c00401c2c105180ca200040396405012406010003e6030f400c9072003030300c040c3c1c9101c11907210034010750300e40c20400e10110300013491640200380c001e8030070704000c01c40e0b517912480300708841001802065560800080c900481c0e80005165044140c1c1c00042c103881c611245007540103104200940d1341005000010b1a0001e02c2400340e9801e55070b00c4a00240400c050034020790f1a2828206080101445200001080d548921844070000714201c0604101981000c06030014040c00c00c0c000d4111080c10038151414501c1c0c40140714110014200680301d5040c0248202118618000482580c4c07408506201041c5040300b1141100d41c075150600401d00c107890410240d00480c804150050b0507c81403025181c9039202c6034029a040f100e181c095950348108443e5158800d60b413a9070150401a40180541000078000010782d130 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 449714037 1250 449712787 449712833
    0x180506030603281208040201090e011202010c330b010f0806062a0102180306012904090213090f1b030c17010603060608070201090809010c0212010e061e0103050a 71
    0x5202c2c2c4034242044000e132000720000349031200308421580c006e289207015100044034000b0560400b80c00000d200c08501c80603041c1300a09014070708200305c03a41300040f80411401e90041000c1e002180c0c2c14203150314440103e50b541400704034955075225aa80e192030390090707614070105455030401c0c4001a030000890320300c0c10408030120400c00d071032200101a40c248030030006035613444503411074400c28644058a0702c1b1f078000c8001040600642c070740240f100e140104108504e002100701c01c400c2c9125503401407403c103001140462404400707440000c11108009821300030b0a006002d0081114201044228441d10006007103404500c66484440e0406040c04d2058507200c1032400701461010907400400004d40350032040c0121035001201d0790700061307240000d12a185459540307130403501601400c1780c1004100f00071042559140b101072000c1d800e0282c000c20840d000300d01010703140e080445502ea01d84011030481340190140c48603d604032034120000e050000d883e503480640c00320310072004000280c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 449715287 1250 449714037 449714113
    0x15050c040b0f090415090c0201020711010807110a06020304060c18061404030c09091101180e1003080a0305060907020f06150a03020618090c03090c010f0201020f0406180506030603 79
    0x51140d1003201c0034050200301418201b468950740100780c8141d07030082c1d011a4014130019001607000d0344e150191010034200151940c3e03c600341140c1501d91280540802d120301c400700c4003402003550065010f580205414042c408a0110603105400e80c091810420010a581048894030400d02c20034489030ba010300341d140a5981c1c43c1ca20004056421000480741e5516128081082182d00709001c10420b09203201c2c01a6020094611540184501c074501200040042c090304000c04006001c0c603844100c041e283c0e01e40c800024028013044600138003030021304010404076400059034901c00303446540284419520707882c0700022058a0600a80c0088080c000030006990340d0f80a23040101d01c0c040803a411083d03102c10408054405094500210f078100117011062001042002c0780a1084c00c002c102c04dc0c0c80380080313009125651503145106808607001c6400c03540f0800c4100d240411044009a0645820401c1140d2005451041d0300d64000c03400042c1c802010721100482040c0010032a01704 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 449716537 1250 449715287 449715289
    0x7020d0906211b051801140409020a0302120403050a020f03090303071b0f0b030f0106051602061b160612140112050304030c030c0e0a05060609130e0a0506010315050c040b0f09 77
    0x1071048220004a01c01061100c40003085c0d1280c4d150b40300e82442c0108282c0089800c0010501ca03500549600c181c002450142107070194040f500300a126010051040c03510303040080c45500034400c8080103020300358003013100c223000100b66903017403100401940c03524a0560360f5011040e2540c1000015441d80840001d20b07410071207142c0010041c03c0d035055a42e21f000c4425401c1400b050b040441442420701000c88141e40e400f81c81c2101c2a8140d074003c2d6191000281c1c040442400c032203040c0d2a20900112003500ca03402003600003143c50700c0e1600c81c009040401c40c5401d9580000c00c4c1069429410010840d461040b0140d124080c010000c1d04d1070300d030300d075150210903a11079001960b1001d903014042040c801401a903a9106600c1c05041029040c0305000403154070600425510a41c4950480140c05010323921a59805640004482c800380280c079180d5110402440b040d00d1000362049015400a518002d0b50301c0303145140101468603051003031101e0030750003520441a884505004407841 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 449717787 1250 449716537 449716571
    0x2003070507030f0801060c02010f0c0b0108030904060504021908040f06060303020705330a0e0909010506010f05070c0b16060c08040c0803071a0c130e07020d090621 72
    0x92006a50380c541d00c2210b400d01030480b2000c010380004020058004000f0305510070781c0c1140582c1d091030603030b100b04003400c8200c44480f42404060400088100000b034210b10000043c0a05401902c0038808e465640d0100401ca0080d400451074072007007460a101c05511070350b5081c0c2d000d4401c8803540c4400d150358884004a0302d80c3c2d0400c401592140c0c0d0144060f00d00603000e039500100300300c080c410045100903c0994419100440c01e400c980215020501900942c41880b00308406841540113281803098980030b050140e9074a40828413941e143d000d050712860882d142e003500a214030600710301e04044851164030040c04512042241c0c081040014010f005500700d4041035910001c0a04250621252241e403582c0709803241c0d4001c005c11000500e52080c03030b440302202c040c1c801500c0c4d07442d151004124428144001c5099488601c0410783c60402c441c46070080e05203070300301c030f41c803000704413042e1600388190244001040b441c52a40c5517400d24405022a000c0e20382c41c0120342d0382d07860301e419a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 449719037 1250 449717787 449717791
    0x8030a020301050406140102030d0f020d231302220902120c03060a0203090705040213050402030c070308010f180c0e1c060e01020f0406050d06050a0f0e0601021f2003 73
    0x5806800000401c942d141a00a850241800b02840c035240c001c6c040010350340e03118029800300700743e4031f0301c610810005a960603200e000402420900180d21580003d01520b01801c0b0b01c0c80710740141304003090a1000c00c0c028581c5042d406409419403900b40c9118903020701303042d4804040d568483c8100030042c1c9175988014418090318000300f00741a440c400701828014024198503c11f40b05000704041c0200014110003107420940d001a91240041d0303c0903807141c0b054100b80d800c83d0001090004442a01b8001c040740d41c042d5650465591b02c2da440351030714801c00d11500000406940004c0d001c1003036503011288101580c2091401101c41030003092000f04031141c1c0c8a0101c039003065a43c140503d40c0280f0701d11100d030303100851030440c01c20b010303807400d000c0c5010302401c200011078010750088484d031005000d000020050b50001c0d1741c0b00c0050002d42014083c07040345904180101e4030719400010000003c0c030458207141082100917107010001d00c140c07000c400048039003c1e046444e400e9580001c0d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 449720287 1250 449719037 449719051
    0x9051504091104230108011202030f030403050c0901060f0e06030c120f01090c110a1113020d050403090803070b04020402090f090f04030f08191505030607020708120702060f03060102010204030803 86
    0x5440da440e02580340da03113180c2007400307080080a4289500e2180e1344007003c11f040d104502038800406000e8004a45045070030101012103120009011080c442d00003541498140125000d12150380c079031004441d40005995520301007821910741c0651842c1280181da8485000141c20342801c4a240000d54950003d403145203141d80e01c01d005110511180c000c1c200d098580e0b0412040c0101c034004525035440c103042c40540108144101203801d41d03181090030303001c03142804003551203a01c48200980140402c0c0c0301103020485688002401e0940070064034801500700041d1040c80c0e9680c0c003444081c1d0303c1100c56990091070740204251170b40e2070014860007811030040050051a080c03030094805418280701006108844080203910030700098283c46012104d000407a1012400b041c2900700c42464002a916020f054100845180c2c00030703030b030742c100c0d100c0d60704498181b40c0a00688841703210301c620103034101c1000c105034030b5800401030045400c00320600c0010b01d49980ca885040d0140c009595079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 449721537 1250 449720287 449720321
    0x120f0a050f1803060109150311030f070e221211011506030b04050a09020603040f061803050307080106230702061303031e0203040e18010908030703020c120a0905150409 74
    0x42050b5003003c004007805068002000c01070b81950406804000c02c171131100074280005d000b22141952000d0080b0004088034000326000141c48914686582400702c0d4203000011130381401d030000348000e0b5a002015030f00509410031240c60703a81c003200c1c500f1408209020a40d29010301788403480f070b914a40001030000345d4001514686490400c025141e02030500d032012130810000d0f0025035603140403640c006074043c440d200740e0344043c946031000d00310307007003018050038154818ae071300b8950024021803042c503003591800116a21401d0a60310b0302c2c0d160544482030380300c804161b980201488002c0c0325550009000d6800c11400303030b01a22003088590822000a1200d40c000c2c50101c9a1612140e00d6540c0b5002640c10103007401c0100000b240010240e24000c44411403c0c43c088100303620a450300c5801181c02d13681c9250040740500654020801d000051150030f0300d011200701a0000d40b142440d050340c3e80000c2a10700001c001034450840c90303100310f00d0f1b000c00c03002400c80390610541481d04013103864 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 449722787 1250 449721537 449721577
    0xc03022b030501090b060a0f031107060b011b0c050d06090602220b030411040f090203010c08060a0602071410110a1109060315040b0714120f09120f0a050f 68
    0x10040950b80c041c0e00200003d410300c070001c1400e41d0b074501541c0f4048014a02100c40a0407200c0460141c00080e0f90342020004c0060030b001406019040488401000e0702c07602040010307400c5204444c041540c021301a030b05c00500c00e000514206040c1d82c240c5002e120003007070005170743d01c03080200e90021414280c041c080a00c455290402c03003c10400a000c4010350381d05514290300c400804001280100b442190361b0300701900e440c801c41d070002c042281c010b802000344110f00c040180001300d0076120944503440c0b6400008210340b0000e4039a0984022800c001c140c40506d10502407a031030400a24000d10103c14503000024108000c513034180750040d4400300e1200304c244144080c0c203001070036090003608229180c582110340b006800d5082a4488881d0403160369480b0121004032144905072040b00c00001c0e080802440800c9031406001c50a4251500b607c1d40340d001903540350103440c40359611905000c0c11800028000c054480007442e41080e07407038801028007810940d44030304203e240d903984c5420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 449724037 1250 449722787 449722873
    0xa15020706061e1e0b031b0a030b0909010e10052e030b0a0216020f1906111203090604031211071203050702030a17060406090e06012d05010c0302 64
    0x400c1e0010101c400c40701c400c03440078113005105900e641c0140403002c3d10001c0132172203c181e0441203a0b07642144040e119110014210010060022110041e20541c0800702080d1320002c184140c44d0103100240080030100301c1010950701600000b00541c10819507102c1a50344284055840c01d04201d040403601c090608514003107002480144c140c03800c1c3c0d0700c1408504800a2948408002a0b404440950424001d00c00003440c55040a2103600c052200c04400544503410001280d00d02c9180780580d20010b81c00780f8080b01c1c6001c00c84200410340d10800105021078090010240040840000030694405801100c206a4028101102c81c005684945500d8680c076200b4107401011314405145003860440b40240840e00041e0345024442e40c81000c5503603035646074003210041440c0542403240d043c4c40515544c5402c0244904c40a80cad082252808028811102c0b41d01c48900341c0d1962890103003008011902c40715a584110107510a040700189060b003081801e15100460302880015080600c4c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 449725287 1250 449724037 449724089
    0x21333080912090d020118030606151103030903040308031509011203030c020604050706051b100207170a090b03040203010e010e0c01022b03050907150503041208090a1502070606 78
    0x101586085440500441d16a55504c03444102041d40904e0090313642c03020351803030140110071a031000b8071840c6891000500c4e8490756442d8402c0c400c007616812810100800c580351207102c1103d40c0d40d07071500308010030b00024030407070065600b0500000202d1541181c410210b151003000380c00a840080743c2c0355440c0d0400d0b0b0f26002d925a20045440684003500300360b030750b05c0da5401d120b028500078000c020605004504610707400c0b002400c4d8940480d841d507403500078158001d6000b45800e6440031300c0c10308240c600c6180c05d002c4640c01002d55458040003403606170140040d0b040031700100da042d522081e80d40e804000c00d029401400c4004806000940742c00c50029141c40c0401c120028080038800160124020b08045031410418504000c9600d59a1419503410030580b60003000c2e03817400002480001c00c2d40080a18843c5102ea070048840c1190000c0603900441c5c104c50000c0190b205461500001d00340704001c1240b85000c490150500e40c0b2a5034101c1500c602e0307007040702010f85000345a030000383d84c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 449726537 1250 449725287 449725303
    0x80a020a080a0201141602041104030b01080304062a08070b0118110d0c180b07051501081b0604090e0c041d0a110a090203010603020a09090213330809 66
    0x441c0140305403521a400030b0103e04400041c0754505001040601d21a9541080c200d00c070742d40104100304000603841e9000c9980c215000076540001e40b0300011844110010841c3d05642c0036031944268400c068401c90714136440032410020f686070183c491000238690801418403244070b01102d50107581031a0700b050038a00b458080003040f40c24400381070324501441d011540402414400072030b0b034500d00c041c155a030f5990b06001411004181e480001c03005295005800d02510032020348801c600100c604151011080c003c40a25030004490800c8440100d14018041e0f1001b03001c2a0800d035454900c0e0044038440b260003102900005082c807102e251a10440c004d4040d01c1900020308054030ba4810740c0c40e000741400901801c2e1500c1c0221003031b6102207044001f0000b03000d09564070340c0c4540000300031350012029000410b45845e8040b40c801d01c280261003448841041141526203404030031068030700c48010080c4050344c1d1200c0b48080340c4080da064130481d007498a030b05615040c070712040b171726050704 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 449727787 1250 449726537 449726549
    0x10b0103150902070206280201051b0306040f0f0c05120603060403050f0d0b030307030306091a090c0a09030828050c1b1f030518070b09041805010501080a020a 70
    0x14090005622201c01c10101e001d840c5102c0b001a00c034500b030300c0810480e03c55040074009469040c03003090b42a9140490030040b080d40e43d8000e22103900c44c490016144220309801c003414070ba050000920030b0402d94482c0d51012061280414000c1c100760071481140c4408103042d0000e6030001d200e0218032a0326180c107402000640c000c007203d14143d24014410300070780b88240e146240008601124200c140c000001c1c00000405032692401e883c6005001440e0794850118803504100003145001c0b0340000c5090312940140414601d9504d6400d4030303071607170300041c4001c0c180081e044010022880b000c0241c01c01c0041e10303d40c1d980c0c4103002c030105021403a502240600b0010100441141c5030400300d001000c000c0c518401c0c0640001010000300c00b050081c098a0007016039160342c1c0d04166240e04a140207591010007100701d0744c0040030300e0303448001178000d202c589981049003c1850034503a00c48c000c402e02043d0001d4603000303182e4504d0f01390b036002c0c6d100d145142e00680a820540c94106000801000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 449729037 1250 449727787 449727791
    0x3120309060e0705241603180609090b030606011e0c1a09120c0a02010518040905060105100f0806090903070818130216060504080d06090614030303010f030f08040f0611010b0103 78
    0x21402d10150030740c0c45481541c46d0303030007082244c8a08040c000c80c601707014070a0140b05100301c56180c51004003018614815001c4840c14240c0d03054460402089542c001d0406039501c207100000c0c031818482006c0078041090802020104c03403004550030000c09410001501480d500901741035580710b2900c84400320b417880344402000012711185000039031018550342800c00c10344404a040c6405224580440340a401a00b002c40540c1004000b14032541a140d01316130800040300503e00c103c440d81110403500c40843d444101044032803401100b0310354819281c0040f603103450b405030b82d0300391306804c0094003e400b00500e070002d030300c1803030001c9040b03070031f03078503d080450401d01071003034000031041c69a00203006103545602180c140000b00d0300300e61404140f800c0a00402d641c5520503c020301031445102d00c05803040840b03a00360b24003c0120b074100c55401f08004103c50650f121400301c40c41c40c00040b03604070002c010000e6000030030340c08003004202c0c9803141c0000300301d440c0c072150940f007024002c10b04240c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 449730287 1250 449729037 449729089
    0x90a060f021906020f04060c0201120203010b090409060207141605030c1e0109090e15060904020d02010f0e1008090f011104150c06020d0203010512010203010b0403120309060e0705 79
    0x554001482c400c5034001205100d025030050504070002c0c400c0b0380012445050016022942c5c0c1d403c5855841c5940c0300ba60b441c0030320090a060713042280020b01860040d00000c100d401007a14080d000306501a004100061a10110b582c80200c00c842514000c4c20540080f40c10b0314503c80c40703004080007000b081c1c01a00c51425480c0c002151456600c0404044080c090a8103803d40d1050f0b00d814007421300c107002042160342811080380c0d2290710020201c04820240009200741c1428440640542d9000e082420300d05519401036a11480c45000300040000452511030650b0712100444e507982c1c0c17161141c4840303052054806041c024000f101b0181c5a0414034200c400c034012a0881c0c2c100c2e41d06029541c01c004400704101c58400e03a1000140a090010035178000d01e00301a8000d50413648115038003081c100c1c503005464281d0100748941c0074005400e01003040414602c000100c800300c00351900103802441e40e0349500840301800b2507826568030801c400d020380d08207481c03c19400d01100300060410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 449731537 1250 449730287 449730317
    0x2030f0d0c03111509071703090d02010c170f0301030308070f02151801060f0608090a0803010501210905060406050c04030b0112020301060e070509180720070f030602090a06 76
    0x1100da40500508100f030704521208610320620104d032407404c0a0440c44000d042586099035a1000d5028140c00c0c0300410340d240704a118000100c139240744001d00840c902c250b5940054070001603031042a95003a0048a110140d0b483c00310003003285009005030b142d246d50440c02c00401c0a00d0081c40202801089602201420307000154030311607a03541480e00080d50380b0b001202011014007a00c001044d803c01c00049010b12584c10031109950340c940e00c0c0010380d65030320b40d0142d44000002d4041c1c5040f01c2040144555441003c00c0c444030f0a0720301d550b8040c11000e01c0d00710100c40d1090029a010b070880001e0000b001130600a803a00801840145402d1070700750b45825108000620441c030542181e541482c086440a401c040001d02088102460034a40164003615640c00704501d90b10466900c0d240e46105203a40e0460380c025219a40c488000c1c4029901508081c0c1000b5200308844c498031400181601d80d00140c000590b100321409603d401111051003030361441c640082d01440020301c480240303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 449732787 1250 449731537 449731547
    0x601050a230109081209150a05040b09011e0305040b07180b1605031201210305090907030f0c02160e01121709031207020909060105100309050c0d0303050402030f0d 72
    0x1079904112154220091200060b1801d480d180e020f8146030049041030441d40c0c80b508007415032101c041da481201c01d001d101c4088114401d180300100032410030310007804018003c44c081c10620006051628480404a21400e02d02c8800d0841d60f0000c0e444008200800c1581d018084c0c2105090400c00080c18030544401c00c508041d0182c03660302e00b00441e14011003d00c050716034a04035000303400d03655110100703041c0800ca074209000e0b0450200302003d0f654140021448003600b120380650340c003824104a01d0412100c00c80142600082580b0303071b9600c2c0e103d841a40701d60850160b4540050810100d0317039207a409402e150b81e021100310fa0000004200c100440c40100d14a954086c54180e0701203000c41c810455401500403a0303801d032003030503503019181031260024080540211151034095640072486036490704240502500684030218580340f2a0194002d84607082c800d50540d0b4003401c400b4040ba4454240407415000217440b00103000550406008900c034038035018014003800400e201000d84 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 449734037 1250 449732787 449732819
    0x270608030f16020607060b09010b03150d24020307230909040c030c030f0209160f05030703090b0a020714070609062006161b0c09090501020909100303020601050a 71
    0x400450004030071401842c0901e20004030b035401812a91503811a040c240010b00803203211501684090002081c00310152050701d100310b804903110880f940790350041c8903c8180c0a441100c010300c00d02b1070b0501c0120b1100c1c0c07002c8084269180181c8a10b0240c100425181c0004048641881018a903c4001400074110382e40307040107035180143c80e200c2c0c4c50402d48030f1600d03502c0948141e00480000c81041a0246094411802210b0481198444081541000341400488008181420468403950f07000b4800b81d9440700d0b09003000141c1e8901c0380c583c11030a91080340c030000c1581d4005031880030171040f4002c0c200300c0e44480d002000030f02d08121014014401c0e901842d42800041815180180300c1d807803103481c03140c6402e404c0c0e54135800d001c1902090100070f100300300007048405245030200304000c0001c03052250000eaa0860480c584124a00101144c1d03000742e8a5540803c0004100d8903104810f5010718402c01d04100c0042c0795040c005d080c0401038119510604070701d44d0806c00c0c111903c20441c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 449735287 1250 449734037 449734057
    0x10e10270b0601050910020106050103060609080606120c0d210314070e0a050406031104110f070803090a05010e030a091e0506090a0e01120203010501140d03110c03060127060803 78
    0x401681c03907440041c0c4d21406802c4143e503000b02007104041040b5810b40202040315070070b0300d0074414592a44820380b200c01c12401103d9503580a1030004890740303041181080c0003950f1078159000d410301d00d0045070304000b0044d000c0d00c0e460a5680c0c0703d525003140d41209084c003e80f91800300300d5040c040d075441ca080d500240141080003c500003840d03c4d0340e2001850002004c0043c0b0030008130b980e17441c158a601d100072403018802c9290030709108020701000212503021403903048092510ac031035903492700c0c10382020308401d078240710b180c2c45800011402d205a1441501903170041d0384900c002c0740c000700304041c2c0750445030031071403e03010040240044810365803e0300d00032101940c035520300e0800700d061030040342c0c0040100e108080001900150301c03030481d40c0c014000c0d0001e20240c0c1c1c0307608020341c0c100d103090802038004078807441680100f0f100b11014a00d40d00040c00340c510301203c400c0001e00c0c2000a070040030000d041c0c545a12040c0d10601800517010101d00800c0c02024900110b00743c49005d540b41e00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 449736537 1250 449735287 449735303
    0x5070c0509013c0501232b06030c0933030209090102040e01030b0718090c0f020307050a170c0706052a0d03110408010204031209080a150902060c010e1027 68
    0x390740001d04140060359101c010072215501d602c1c0014105540ba91f150b00691240c1358510450f1200312118000c40701507030f40190030300121500c1e16010f0401841303440301150301d2480300d03080c1e042205c0b5900c0761b9608018104043c1c1c01d0341815070040110b0f01002030800c100326807042101300280d1400c2d003805030450780c0140451740d5903980e641065600c140c0242a01110100c0c481c0082030400140c0d120420810460303070f0b05850307100719240a0703075030344141000035106a00030540c0d0300020f9010b80040b113001080a201c05d09154500c4940d07072805a203030304082c0c041030010801c000c1c00d80c4064448209080c10414101003460902c08183c0c8501e1150b007007900b016103038420070060790403a40455000f0f1180200855645640f070620403040c072031805007400020040307100000d40b0341c000100406c0c5941c00c241280321105001d035550000b0000f00c60102d0300a1401e2001759015030081c8900c44041c1000c901600030103070680d11850890340f06002505d9501d500c0c1800030b03400c1c1042416030f061903500c41d4030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 449737787 1250 449736537 449736557
    0xe060d03030e1005090d030608150405120409200f090d020402090a08060108010c11030406051c050403080405010e0303070203070233040e06030d0c020105070c0509013c0501 76
    0x30803805400a402ca200040c41001501e41140c800380d4000c07403240e1106800d49502007990382003202502d20901c9800c1403540820300080003d0582040c00e90414429011038100000303502c001c0440c1d1b046640080000c3c3d0f5140d04000c0c499039810044c1e081d023043c44800c00d01c0c288900c20110480d014084080c1c1c040c1481d1a0340d801103417155411103950900003802070072510f0391110306955416003402000d0300f95090000c10075007d8044c0600e000b0405610340a542001d05112007101d09401503044204021110018044030042d140f14541c0154001d56a26040d0301e0241007250030b4841140c103281a5601c104104149240d0200907542d43c50340c1190711810b07543c81d005082862b0722107295911421035500707000141c40b2440c0c1e801070040301c01c5001d4090b580d907181d80405850315508050302c004100c10075401da00540c0f0074001010a0784c03041408240840d210004610969003d802c68180c1c90200105007400e207141e00301d09080b5000101d04081c2600d00400f42c1c2c000601180301e00340c10300c0305281c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 449739037 1250 449737787 449737793
    0x515151207021507031a03030d0c0e030d09120609063215060708040f080c12060f01031502273d02030706020a0903030801050f2b050304090f050606040e060d 69
    0x202d5500031b090003400ca0742c0f180322a544c518003d10300321132402d01107540d28290110034200800c88d0022281c00d41c403081040c900d0640407801c096010300f41140c915658841820014003a84200c0c03008428260030064281509808400501d00e52060084040c41d00810082c02c5c0c03454900d4846000401e0381c029444641c1c078070748055103000b40d4105403a0f445201e00c02090001c0000350f22124500101c0351980842c00d1041025200c00c02951118102a1060f0060011811310a01d10101c070210384001032a1440c014486001c468081e8180202406440c915001b280380c00d440e0410005000f4207061400d0440c02500e0002842242021000b1043c8030003c3c0755060003842582c6482c2d800007020740d9541070701100280380d2038050004602107800c041c00800d40e0b00301041c91055034200070780241841300c80680340fa5605500c04c03130054550204a440301c000a03a06102400041c030302c140020038107460310003070316040c0d0301c0041a25000d0007061008220001d0020b50098000100352030101105410f41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 449740287 1250 449739037 449739071
    0xc010905061c0c050408031c050c030f0a0902062b05090f0705040b030f07030c0503100b100806030c120a05010e0309100c03030b060301141f12051515120702150703 72
    0x40e101b594540000320300212039119464024403480020482000f441c0d0344c42500c008580400d0fa0307078201c0c1840d1600000d00340d405961040c0c0320140020082c5007850702500841442c2c45080400d88450560b901c0c030071080c40e8182c0642c42d0407980c3e80b005403603045000031501b5602c103800d1044601c0b4944a100e0401706031010b1010920314200e00302621038850700ea0400705101d100c984201c50103442410f00e480710b424a00d10407402421002010703a4004292258200d81c0c014001d860759a240c0240b083e1030f02e01e6640d20f00e00c041c0c01203403400602030440700f90400508680210605841c40e400070800d146172075407052182e5410100c0750a004400000d81e0908900801041481c20b40008001001003078841c0140c12007202c804084510001010f8200311025420360307564030082c0851141ca0304000c10410940102e9404801d80041200b09404040098890620381107807602190f4006440c101480403e14040d40c0303c000350005281030f40c010000200100c0d001004001019070b1520482560550a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 449741537 1250 449740287 449740289
    0x30c1416110906180a0219020303091516051305030132010f15030f1a0906030a110f0105120a06170309090106050d090609030e04060501140702010305040f0b090c010905061c0c0504 79
    0x1c7c07155002c4c0140f0140c06592540141c4901c074043c0f1403407280396a1140d00e00d003080d03c0392038416025981031030000320960301900204448201c0c0840340710080b5950f1003d11500c0740d6285840b408080c8449000400008102c00c2d0901020b01d00700d000042c008070703080c409200e0446992800c21800100c604a04400814803420b518103120704243c0c0300f0010000c1035100300d44818040398440350070b8035800c04143d0b9803050742c20000d00d1000890440602460004011140460103040035454561084008204041c045904078001d6035a4402884600d06c2c4048441c03d007004400110300d0310345401c00081c01c0190521405041110008096060540319006016295403001c403d00c84001303185400340c138100740042035a018510b0060002a03d40c400c140f40b9104c0031498451502d44407050b00114054032004000381c9400c55402040c200095005003000d2251007001c0142c031510180100041c68655194001403050900b440300072190000a0005428071450750400500000d0302d02050b1401c1c011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 449742787 1250 449741537 449741557
    0x14040b060f070c15021e030a08070f0c02030115030c0803070f061a100f030e0118020405060d020904050705040f050c0909090712030e09090a080a030c1416110906180a02 74
    0x3541c0c1300495810380000c0c40052054401751030404010300006801d17a42d000f1402100c0c0003a02c1d54021410407401600c0640c41c01400d8904401c9903411754000c64203480850000040c000c4070035000300140000310501e00040d02d4490041c6103420000d48604044a000440c007401165907003090f0300000c4690168102180005485076088541c2ea43c4090001c254450407107020a06058000d40c0e510010310a084510140080c503203003508041d02400024080102503e82000c0e01c101c42901680d02c2e141d20742d100320721440040007207905210500003580e20410011a55600349020700060248480030350781c02c0102556007000e103030b80d20380c1ca240c5070102c940d10100b4501140500c08003030550203004543c1c00356040d10070309040d864081c54190b8908007400c02070042003051200c1002d03035119810140701c840980c0703082c0c00d5262036190f00400a510202140d6490b0815034903c03c00c001c1007115007441941300b01e480250500d02134004c00c00c1e0382d01c2c0b10401d0000e0410340340087e104280301d60640307044080c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 449744037 1250 449742787 449742809
    0x5090709061d010509070f03020c01020d180302191e02030a080d060e01050a150f0306210201030c11070b0a14070b010602070801050702030417210414040b060f070c 72
    0x75490300c01c1c0d0b0a200d200ca058a0348500a040040b4060034003051450007000540d0301c004500070300e030100b14002c2d00000544602e03950204100700e0711028500070007031844dc5801081404c00702507e8064600303030b03034641540280e000c0002d141c0302045c420360061981d1050212a20103482440c400642840350004005000d481c0c0840e134600c290103194420410b40d480844510310f680d0326101000b219800304d2190020b05010715a20034006071090260400c20710007402d0200303070b068407000c2035a0010b02030407105401d9582207600100b9580e041c010140b07117003e9404c24a0b50250059405030310340d4040d004000004c1e000064005240e441845003240d99002c102d02c035900c0350f003a8a000c02c0109000e03c01d10005100380c010105e08904184241402130015400542c6410715000c0540c0d022030020a0300f9445005201740d03000c16104840c454505c0360241d07440c080e580c50905141515451010114602482c50708001901340e895445c00c88805000e000101038494005181c040b01621254100101300a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 449745287 1250 449744037 449744039
    0x3020f010512040c0f05150703030e070e01061e050309120c0a1b061e050403030c0309050607060c0216050102190f02030d020703020102010b090f070c03030e0d050c0d080603060a0509070906 83
    0x60910b103010b0944101c0941c1030030540c0e0711000c02401e003a01f40880710010800b0007800303001070700907406042084c44220a40708032030707540c641e040c405207030990045021441120108a80314a040c0c8030440340f00150030240c0c103605005009c00e81d20f4040c040e500d0042040002c140c0c10010003000301c08107203507021580240d4150000402c00c200000f070712820011a1a002e445800d00205a01445481000b0350f00d84d4101450b54404039a6190284416024024168008902078803510020911240211340102e501405901d00a241804880c40780001710442c0c40d00740803580e0301046480808014034884030000302c0d5070810102c151f001c2e00b0000d501d80720706120700c4811900480c01104882c000d800800c260300c072a0081c0110300400b1030f481040c500600000030341140c043c400b0340d04c0150081c0b4000490b01c060001c42468001c407c42c00c140410320100380c0130b000e00c00130020505800c450303240c9100a82040e10104c0e40e94240a030400d2111519200000d46044081040000501000c0307810310882e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 449746537 1250 449745287 449745293
    0x4060f0b15070b070c150f02090411090909030415081f0326040f03150e030d090b0603030c0706081e010b0a03051014010507020604030b010b04050108010602010c0903020f01051204 79
    0x158030280040f01c0d9100454001098640158212111300c0e4004d14001c000c605400c000c5002040703e0340b00c504195500380442c0d442c0d47c8803403044410412121002550f5210464100b01444500503c00f000c181d00c2007106100d2940107004000040003141072500341511162003142c08075a00b65205d01d0072610001e0700000b845009001c030300f0f047c410800500004110b086030b10314144914040c11001d030b2942142000000d8030b45840034a2001145000140800541c2d515411a409080c6001215443e42c3c2070000340f0042200d03407900018114020f601d072200e055800794031084548240c0041c0112a40041d1070818450014807078a01c0c0d03031540b51890340c1c4a9008240b40c0c1c02000a90000915010004006a4031100202c09807070701d030901c880501018070011074244e0710070b00040b41c0200050100100040078082482c4c041d1003403100c0310741c40714140f500042c01d204059010004680c1802040001207030072605500079a40c042c0d601550b1a0107034401a9640c3c403c284141044c08500000c07c014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 449747787 1250 449746537 449746579
    0xe030304121d011b030e1201020901030b041a040c11060c0a14070302060a1107081204121d0d060207200f061e0304140613060c03050f04060f0b 63
    0x52030301d40d294031000c00003261122410840c2940001d0100d041580800d146003140074040d01060b01c00e19050108504150116844c07824405004400341e40225200d085980c1500540c807440c0001e036402c00c4006190840d201d400c1b84980d910343c0c001ca949030041000b07070740b14103154008082c0c40411a040d500780211101c6c0c0d030b0b40c0f000c0c03540000120180d41e90b0150f402440119607819030560b0081c60340c0c0e2030f250518401080e5203008280081020440310000450300301c003900c0d5818800031050582c1c40c250914004485601c00080c04106c003407e924a824200c80714910420501912070405000c00791410318003c1c800c00300701030714200400c00149800e00a00c0e0b50741144034000d481c44c0b40c01810201c24443d0034000d844405103040074000b00d240d0000100b80103507502901909a1020001d000d44000782465010748214007000c80d03400d0804180032080c01203505024403440e0070485441c003405030303620000c0064402050f20351100750703101018581380c000c1d168841000b48a210b55402070040320507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 449749037 1250 449747787 449747813
    0x3060b3a080711030d0e03100b22140711100b030a062a031e05090a020402030903120f040209010506160b070c03020111090a031e05010f0609141b0d0e030304 69
    0x4840e1244d4000b081d5040c6c0b08015032600140054000c0503100d42c1c2c1000c803030203880f0044003a074010140c9103141c3c02a03120a008019000800e0300000b40c0c442c039411200c01001001050441841022513103840680800140130004046640001502403181030001c0e0400c0807240010780300c60b05040c0c0b80c0b0f940303c00502d1008a0b00c05da403a446002412142020780590b00c10459040049200e40c030304c000d4030742503070b040982d003c008103041d201c0d02e4504da40014101e0700252031180940c5d102065600550306030707070044c0c0d420140c50040907880e8641580010812207050103000e0164001051201e5861606507041d41940c0d1301882c000c1d140e107440d0000800d1445107a00942c0158205880c02200700c110314110340003440080c1401c1c1d041410764a440d5a80001c1d0320380a00140d89000018011600c28400c00311944082c400100c0c02a10b400031030010f44403901d201006031542c000500c86000c040c1036500c13421100030901183c84000e100419001000b0901101c07401d40000010841007000e0044903607 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 449750287 1250 449749037 449749039
    0x1090608010f0c021b01020f0106030606180218100e0307030302010c1d030c1507080301120c080c10081f0b0706050f01350a0c03060b3a080711 63
    0x8005400e240d4000700f5640390761442005030300680300c58002856014001d000c03030318041c0115080070010451290071242941e006441c3c1d55500d200c18041c0c0b0350959200c0c14000000380e015418500031100c0d503180750a00c40003140c4100104106000e8030350094003c10303a00c51006083e10001941ca00b8064040d010307551203500003400228586240540d100a0072001220140c0200100d0011034140000d011882e01500002c01c8248101d6001901050045018100c240000ca05198091030200f0b02c0c401160840c2d0703030a800c4070a5928540d2510450305449600618228906407a418800c660398400a5520100407901110210708010018000e0004c40d12038442003006030f43c0c0c1004000046400c1c0a1503d00fa10324a412076052030048060740c0700b900318450045d2403035102d949079070b02c0c0580c00300c4116031900c00d803070b410010b0008611442030310b040c0c2512040324018902c004801001301c4618101174404200000580d40484030802001c802e83c02210150f440d101420704103201d103240c03502a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 449751537 1250 449750287 449750291
    0xd0b010602011d030415030e07030309210308190204050d0b0f090304050a060c02040f0501080607140c030a14090904030c0605090109120804031103041e0b0a0f0c0501090b0109060801 80
    0x100d440f1402c44102c441040c80300c04041d40c241414008203410b8808203010751020161030b00940001c0c04c0d014030a040c000c502c03c0d19128441d038030384901d100e01c4c000c0301600903c440340c24186600209402c5000c00b0307800700c210008219005030385c11445000b40100e4001d660042c040030415020411640c90403030140c00c00d9440a025955007c124a50700e04c11401b82603000340c54200d041101034041c038003400b00c5510003032004c0380ea06c0d046507103001220400d0344a88200c0c0d00c454180018540c201070028410b8101104545c60401c455446030703a00c2c4541400c0000b0400c0107090a0701d041d0f03030303d01680c2c80400c000700500c07100c0c01e090800400000014805076100341c42d001c04141c0e5500c0c144520a030060f4003d40c40100c200c600002940d031041c004005400340072503044c041a030380c401480180b0107000e10248481c070644450440064211054001c1016244104140360180340c0204040c491014a8607010581c030b0041e107045800740c10282c0005044906800010404d0315103030b044182030300e26003802 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 449752787 1250 449751537 449751551
    0xb0a1406030c010f0c06090605070804030e040605010e1306080f030c101401090203090a06060e1501033b030403150c021515010c080f07120507030203190e0d0b01060201 74
    0x405445000d56051240856204d8040303c4c9518092409003040c203004490000703400e6200c1c2c907a80f0980d46d0813500c2100040c119020003081540182c2c9a113110b80c402c3c0c1301000070070f04240021b420000d4607040d80348a5250580b1141d040403032a084400070f0030001042d1054042c0c414440e42d0b0300e4120300500610750042c030b87c2070410b6052500c6080c1c04101801d54071840341e4a0b041d9220025400a02160954000c90f18100045842c0d40142401821165107a050798502403280e200040f0a01d0f02d003a04041c00d1030b0358030889032140b1500100b000c9601c5811001a100c0c20310403005000004241d01c1b440c0000304000050090400e0301103c40941404103210800285404070f8507041e0040003100f0442071030707000c5203600c0034980f03041c1e00b00d1606060205400503241c079812465000f00c0000c040304000061081c0030403003c0c03008071140b2245401c0540c10054a41e4019469002d0860384501c1100d40c00132042c85648a030a1410b801c000240c0400f01d5200241032040c0e050302c0900601001d50b0030045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 449754037 1250 449752787 449752789
    0x13240f0e0115050f031803030405060601030b06160803060103020909250e0d11030118060209030705031c110c0901030b090c0616080310270c080c0a03090309030b0a1406 74
    0x6000b02d40902c0c1c80e03031000c0c0f401508011929040d000500b0b90502e50a40e41032020b0200401c10003140075500070001800c00d45000000142500c180001a9010b450203201151000b051907410030401640204804d0720707561340500480084c0112100c041d80000c1c1c00701071242048202c6104c1d400382c0c40c002c030305000340d460f000404c0e5440301da0918443d400514540d01d02c03010034959102c55903200c0c801800442d45404034050700d04503124244041e64101e50010312544070303140400c011802004160007a141c0c2c920503201c03522981c0740d21849001408070031501c07140304a44c1230210042d070081c002c10040595850b0700b070500b0043c8080355002418824490034400038070303202040d180c00b01302903c2110340e20307181d60b5100e030350b6600094141e943c00c0b405a0404181380703070740010031010b2040383c0810038450001c0c0d40c9447c080d643d15004840900a103201440f0a5040701c4007200e00b00000d5042c040b403090003e20b030072035a607039441d40003400200350750382400304508464100141c5001c2d0f0a4101d11281c5480e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 449755287 1250 449754037 449754059
    0x1050604090201090528080705011b020108010b0d140c0d3b01020c06010801090c09021204060207050f12030108210a081308130612020913240f0e01 65
    0x440030380842c40c1560704000f42e2a010400d103200d81051104001401e581d039606990841b0326400481c0e44d6005410180007a50740100e202681c00000a292900c0300f141c0e80020381910b806004070003001c640024900741520040d000f50225800322124420b4902d000b025003001c5402414240e03000c581000c1c0f50608289131541080e441700311000c02d010344124484803021802c0003280c110b1845540038480c420035808140070320f42c02407090b0000840c15110618001846c98480c3c2c001c000c2c114418841000c681051500342c139031041d40454010391300c07034003428201c3c80c002c01903011703031481c0c030a18074092051300114002d14120303403d807000c0701c0c4840301c00702000201c82ca0914100710032540a00c402407415104600b12504100808041005068a500d0703c859075440003804202c20411564200700300c40e4803025800c0003080010045043c0001c1200090441800d00e40007203010741c0340c00d280380d00c003610540c4281194010b6440d07050701303a5488204440140081c4205007401c00d2090001074841c0c400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 449756537 1250 449755287 449755301
    0xf0c15080a0e0a020312040801051b040504020f160c05090703020711130e03040902130f06021009080409021b061302060417030d050a0f15080318040f0504030c0501050604 75
    0x140caa9244550303903450000000c00750325000111920602c520301001d80c80c1844281001072010070031541c0c5500b420006801d40d40c02910f1000d0f01c0e9511344c0f03071409001b160b00690b000d403441160090383d41d00003200780400f50f0041c0092410f10710340000b81c010411a0416a103002c490059444000d0740e9038040c020740032406006005042e054076205030000c03524200000041035942c02c00c00060060034000c00600e56009078001d2070301950300042170740d180211420b50300010601042c1440c1c2d41400e0500007511104036802c0c0911381a210b6a420082001e28029100a049507100441d1203504c00e00144100c01c044142003411400703070502155a024203020460300c2140c028020a00e032904d4140c0c038644440b001c83d075044241c04240241c91500c11540238071802114180340c0483c0079a869030190044568070558005102841501004010320200580b28148020700c480c2040c2c2e140800071801905080000703189591810301080100f503080315441503030500820082100d65145e03402d0000312150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 449757787 1250 449756537 449756579
    0x108030d0b03011401230f0d0803070e19031502030705041e030b040f02040b01090510050c011d010606020d050c190f060608060702120304170c07030c030f0c 69
    0x41048000305024840e04007661406000c0d00001d030103e05040c9500d00001c00780c203c03843c881c248002d04100c07079001c0c10780b843c800c0300201c0b400038540c80c0c200c00144442c00012002040f18502200003401c0600441001075400000341c1020b00c0c00f514150161800170303950004454452007035000300b901c04001c1c0700340d9103c3c0c0340d40c7e01c07150726150500340710400a0b0078841c85240d03180c0640f01c002c80000d01c0401d041307005610032108024004d45034810081035850300c111031350404c401c032542004180e40351581840a080141000795582d0b11400c04c40340540481e0707038056440422480c64460750401544080c0c100e80140e4203485c109104410101c0f0184a006c1d00826075920004c1d071900d000b10241d098140c0b451041e041403800c030b00d6968a00c81990451703880840d481d04480c003003000c215018030041301c008078021300b0a40343d803420380d039002da0480458010003007a03100031640b00714030441080603101031500840c050f040c4965030302c0c0c1010314040c5d5140c102c540130709003040055640c0900c84000c00c0303c50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 449759037 1250 449757787 449757793
    0x3100f0b0306190803180f010c0302100b0109050d1202010605100905060a0c0209040c0314010e030304060504050c0d11040c030e060610051902071409010609170a08030a02091302030108 81
    0x1104030411059100401d03043e02ea000a99000161000742000103111028684400c1e00c45038501b2000c01100110b116007450501030b440305190300280e07000c103c15040c03101640c030010300040e0440040340c41e04d45d503030029508448100700000901680204130f60507400d1550081c0022911a014041c800862280c0000442c02c03000080c00580703400405024044c0740791416400d40d040c99000103045000a03075042c1e82000c0004401d1040c454801c1c0100c02006043c002401000c400c89401556407100600142000e55035002090402c00300b0301808826080080440e11503110320f007400340d1403c68030520035208525050b040c080507806406031152004d01200907001540c0c50000781700101035000a0103041010070001e20040038250409a030355640c45900804c0954140721643d0000900d4581592040d822940100b1150394410400c03400ea03110300d04080300c2181039003107062901b110940018524540401005107841d5107602a01000100704c4034901d10f403840041c0031049100a0043e190030390 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 449760287 1250 449759037 449759041
    0x30b04050a09020d1403130b090a150504030609150e060702010e1501090f0f021309060b0403350a0809190305031b1b060402090a05060105030103030c03120903020303100f0b03 77
    0x10340c0c0080417a22044c1c07100c0c00e41345090481e07001c403809554580c00030b60340208049000e90300d9051140d6200d01510540160860032105100f002e0001d0046200051000f0388030b0017070004115074859140310709420984284090785118501d540c480c901160071600661900e08203644240c00000d85452505400c501320764203900706000100075000503840042110303101ea89000702e04a0502c0189102d19025014003d0a07043c4035251050f111507512142800c501407105201013170452000940c02c1c2424895802041040c1c440c540c2e03065104007054102d0170b00401e130740140903005581a8803c0505400751407044441c82c666044c80c0d005044045c000070820720015240024505240f00308011000003241030180c03100034000d8448c01c031400d04482e504080d050100310308091202c0354211180b800f00b80700324500540001e1a07400144005010400d0021f2594140340c00380c5076104010802d14424005402c9909003c2d41d280e005842c1060020088540040c040c00c01442c844151406451078600e10303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 449761537 1250 449760287 449760293
    0x16080d08061c022e0905010903120806130905010b100807170601020708030c0106260d0807120c1d120a020904060e06090604021503010608060d06110a030b04050a09020d 74
    0x112124200c1281c00010f00d25803400381c102c100404c4501940a0701100c048100342c55002402110154015414040880c070300340300080c1c03004000082500c1030701c0c04082c542d444c0c3d000a10014542121881603510b0640c40c0c00034004190064040a0f8094445d814015100c0794101e41040d0210b603440c0000314801c0f1216500c04403140c1486d00100148110303850243c60702503031401c6070300601c4280850380d9581c1082000301c60030102d0302d91239123800300380543d250700d015807080d201c00049a8590803c1009800130b51174500901e024001401094000c02c44071717030305a01c007a00c9a00018526091072481303607a42507280c41c1880e01c4c071209240c060054840c101da031303600f8454403480c0944221029a26030748214901c03601040940c2c41b41c01910018011030625005016203401004d801800e102020401405001d0300110090b411210541d040502c50080f410b00b40001c100040c1e00400140c1d0000b1140c00e80c0d40d050f00403188100c011130b003c12580d00e078943d4600460f00b1400c0001d4200744145001808 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 449762787 1250 449761537 449761579
    0xb0f1309050120030a060b0f0708130306020c01090512041d060619090303090605041526010803070b0105060414150915040e0f0105061c090516080d0806 67
    0x38480c40303200045004038610140b59914000b04600003058000842042103d55450140a0003802c8959050b450542c500d511440c4504c50408064842c4900017a01c56900007242e01c984010f5420000864442d0040201796002e09854013040e02c40e441840700d040390b6840c00c1c13412a011181003910001008284d0381c0c0380c0309003140040000758403190078888400700103d2a50100f081e802d059a8040303e043c110302d0042c10700c1502d030308190304021080c8011b025600c3c042001e0880b844aa0511f01d540c420109a00032459000c0e5950440c003075109000014848000805403403490311819280e800c40e80c880b41030113014002c07440f0710055401000502074640c00d111088011421302108143e241c908c820011070403480465103401c220900c0003408004000d00580041d8000d0007180c103070a29945000c1c000b4a0a000d0461503861445184c41251029113541e48034100c0164840b0548600c0c3c0300a82c00144040a544a48503560280040d1011a24407860b4080c0c41940c00034410764000c0c605040043c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 449764037 1250 449762787 449762801
    0x21060306010602100b010221040501080a09030c020103091104140709090e10050402060c150a180b1f09050f01050a120c060827280201020a021302040b070501060302040b0f13 76
    0xc154001c8c840d8014920400300c61a55892204290460f5140d15150004204040051540c8049450420070100013503100700304010081c1c09282c040380c949042d0815980301c0080d4107038180d00c01d2400b02c50811080181202c14400c00369500d40c400d6043d81d0300408070a0380c9a2207040480d580040464003100d0340300f6400503800c140040c1c09a410501259a11442d108c0c07012131140c01c800e800030410159aa190107a4905882c15411900740860185d0b03641c4c04282028000807003400c0d4804803690301180c0d0030607000040003812003e01140c01c02204001d4800c03c00e004241c000d51400703070041204140320418507002581705007406041da15007581213410843c05071000ca03960a16075984904010343e100d019030116000e00c0a064071211145145000d00c00e01034100c030f00794440304840e070b0150ba000f04001207000d80541c0d5400160042c104103c0003403159801c031651000e404510b000c00d0100c15808a01604c0c404d950070000c1006003002c01139030158000003140d0000310b0a641696100c0b1941040c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 449765287 1250 449764037 449764039
    0x90803030c181c110a120210140a080402091b03010b0a0c0204091220120304081b06010306061a041e050301110c010f050402030a020d051221060306010602100b 70
    0x501c0b01200d1000451400c0c100c48115200d0321600400f005010020315550b5841c001100c000c0407041c074044003038400f00c8400310064031402d41d02c003c03a031400c1d02880000000d20b84412046507280f50101014000840c00d580c144c2c06100d044c00054166040320403200c0c80400b00c0301a0a003103031719141069000c0c0d0b100040440070031030b01c0c0b804800143c0351030044020161260240b0840c0c3c42850758010614101c0306002c01540b15111002d012560011580740c00c81c01c00c50f40d455a0383d9985050100f164814901c000e07a071841554075400280720040390301d6041e41d11480c401d0060030f64820409401070200d42042c001042e0800080000b44290320318000104e40303220044089035542c03000079084590b0f070380c400c54a84200046081407100d0a21428402c5600c0b00e400300304c58100b81e00400d95800301a0300090086266604030810b001c800c0001c40c0c0d5680c1a103641b036a03100044007400c041c5241d803002034000da0b28a1400f103066842d001c07a819040e03909550090140b5404040004007801000e548a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 449766537 1250 449765287 449765317
    0x1e090911131a04170c0607210f050306061615140f06100e010c06140612031c0207080c0a03020c0a050111060a1a1513150c021e062206090803030c 64
    0x403001584540d000341c0701c050301a0449464501d440c1130790968003c00c1444400403c5030b40d807172707040c0119006070689410220644904d621000600382d0011050b54042c40544074445010415071065659042030b03d84151684000d50191a04003811a0403072098070310b151700100202e2000e4402d0b00c90003440c007102d030701450040d0003000e198407510b00300ca0400c08001032899154080000c1803c003402818424810b8900851034903501e04d28202c086814406229035040e00000c108062002180580b9411046c40c001d65105d1455480e0182d80c034181d40c84594016900450700242c0c0c6c3d80542c140d4407051005030054405582c03400301e80001400f54a65465805804462000854481620000d4001c2c190090244d40381e00840c000c100820256111200c8000b2050400c1441680300c4e5096890170784c103448120000c10113080b000d82d4641e149003502d400000100d43e00040d980080401c9410917400d00f1140c01315526288101c803940180d0043d80e83c03a034401c001284e50801c640c80203210102c8031181d6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 449767787 1250 449766537 449766553
    0xc0b0f0d1406010906051c020a1806080601080a05010e040201030902040e01060b09120d02030a0f0e2e09230a0521010612031e090911131a0417 63
    0x24000c84080010002200c500d010400c269941c011a081380588110f0074103600f406002c0820301c00c001c0149112000072600802d111034014001e0a101031015903001100d4002c1c0d4550a008028070f900300c50150001301b04c600882c0081c42c1c44c0c410795040e116104100b0318160790729001500940710001c4103e0308555130b00b400c03240c0000284941400303000340392070f000d81d5400800d0800c810f0071805103079801e40d80c0014540003017040d0000111021a8034a00b00359001c000204810b030741640304004016040540d00c0d480e5410749a40ca088040c0100e2090300668030305900c020304852444140c01418518030200c02009869090045507440c940300003041811140d4803400415802c0201d004581985c0764030076030240c1404000c0c0034105c003a0400c0c0541401d0700d45030f40c4004061940044041c0007941041440d03441c03052160490300e000d40304003a018440340b151008a208c0c1580050003502881c0a00000031559070110803d00b210020241c5000703082a00f820101e40808540d03100404052258000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 449769037 1250 449767787 449767807
    0x60418030509150301230405280f0203010b1908040c090902040617010e0d0e0a0e071b0c060e04020f07170c0d0e040e060906010311043e03040c0b0f 65
    0xc02140a0442c0100c3d0002ea0014050107008052007a264107204900b0720b4104900000300c40c85003802c070278140200c2d0003142480c0e21048001c007818150204214000000400c0d01e41d41080200305c44201050040520600c0c2d4900301d861400c1517800401006c480382c000c002e0742e00765030001c040c2c460008000162a0f07031f0390303402c0480450f020040ca045903512990300701c202034030078483ea504000d60340c2008040c1028200025840300303003502802c0c45403000400840c0b030044c0304003c41980c0d0394403003002c48200302c2d40e81099143e10000348100303000103451607080d1a242c04d1500030789102c440c01008550400001f0b81d40c5034104183d0004030045080c0a1060510b071034010089606040d00b81c3c1c980708810301024081c041a82c90b5100780c00016841441401030500d800100340b41120b412400c0c0c40c0d84503403484005006410071603460904160510b1050031202d40303044440242d642c0e40c0300d9400348500340000030003060008880181c8030b07407040c0070304204000d0714400425030f40070340c481d1880c40c00e0710501c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 449770287 1250 449769037 449769079
    0xa0b01350a02010e09090705040f0b0405250318080f0909070504090c0c120807030b13140603010c021f0204031e050d030e0705011b02060c060906060418030509 70
    0x20a0038030159100695110655030050030b50085004142c41d06200c0346042504590359540c284242d5000b96500d00c00f0b40700007440c2d988964207125009000340190706158054003101d15800400d240303a03c4070039040141c030038001d02c5010001e91070050718001c07440c07281d11001e025801801c40721145c45000c0203007000968501091502c2612a501c40c10780751404c1000510460b04120882d000b8402c8004074200420707460740841016803001c3c5000319251780c0b001e0701100a045580c00c11904004020208441038101d500502c1101c40b000b103001c911070b901e0300105400d80f0040401340f0702607000f00b51460000d0340707030072034200900d049a00058a015943d07910304220020741d0198100000106603c9020010144040d100909547c903041c4024501c2d020300700e4680032580300e014180084412460305003003030701d840316403082d0300285041d44940d002691fa58681c2ca089840c890140100e400240480c5020322400540c01502500301102c2502554141c6055100c0d20750564442814052607031022442 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 449771537 1250 449770287 449770379
    0x6100509300d0f020c0306040201050f130b0a110c0319230604230c0619030617010504231005091609020c210307030b1c0b0f01080a0b01 60
    0xa03940d0381400f084407182c001c1c00e01550980440c800c1e0480300901016130380c0070055400112600481d1a0b0325199507152201040c09a1711488500101003280681143c008500b04103440f002c0c0151900e48542400300b41e2100e181891085600000350b808202191041c0841410042c8651940c01c031400601445031400b141201c04507a0307032041d24074492061062080c9200f80b441c25100074200f03e4807007800183d49004006d400c070329510a600300b1004607440390300030300300500c0c41a42620000c0d00c02d060043c0a803108880598141c170000d074100d4403550015180c1426041140701402d442c0041d05180c0000d481c001c0c004900612410010120400c9241c1741100141340524005035111100a07250b0b00300102c030031005100c12031a02c00451044040801c0b00e0f840107480c03500080e60080390b40010f45141100d800c030115410131881b5141044105450640118080381c080c189607a6142c3c0055030315107400d0402400f810000c1c004000550001030205040d2500a40d00014401030700e591020011304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 449772787 1250 449771537 449771563
    0x4050c0f070515250e2101090204110d0e1f0b0f1f030b040b030312060123070b01093812100e19080708040b120610050930 54
    0x2802074880c40070451040501c0207841420851100817038038000548100d41c078101141510510569185010b10a60009050310790007001008130301d03000354507044960444980d550145203800c912032844c13800026071071000580400c1642000c0000109031000d4441c41d440340e90031003c0f2900781c6465580d000d1815094204003810811a101500402026030f003042ea8000c1c00360b454a080c2c40b1039524080100c80494802e11000805911280e0040b40c19646890484866010482c2c000c42d243c09100b0040c05c0b132900951403c0a00c1e40c9664110040312010f0710b2034025038101400c201c0c2c03014001707038400c2c003610030480c80c0781404c11103840400c60402140c070341c000341c54001010140030455036204480c005408140108000409000d10303841c0301071804006046250b01081100c01c201140c0d0407a80942041174000e07071102008001050725000a0300c643e44a610b00110200407284604107580e03600100800c1c0b800c074400740c41c4650040c1006036008410040c14003007040c0c0c3d0b49070100982d1003e220 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 449774037 1250 449772787 449772811
    0x90604030807150606050403140304171608073605151c0f1704120803060102011410050d0204090501020703020a0c08070305101e0501061d04050c0f070515 68
    0x41403504220010f00d071001c0904441c80d1032030074000c0c1e980c00300c25101a01d501c940e2220b696007080c0740300c525602655000482c9808445441031040704003164556500640700300030325610791100030300b40e1903002034090403100381c072101702e10211511540c00b801390312544200c12003021080300d60040c060312002c403120700550301c6040300f0405d9420f04006803080143c114800d9508481c055441c005100d905841c060800900c5200c010320282403001101d008200440945404901070728081c00315400440e2100c3c099482c0007041300200c11100306040c81040032286038640e8505110812030f07002900601603801583d140c501d03000081d000d1004141d414003e40040c1080e008c0e03850151170040c201d8200d1300c0d0640240c0300810000340c1c0000c0c2d41805007415000403c0b40c40c0000403100101c0b13002c8001c0540c641c113007800011501c0d0405044858001c03c00b0341c03205219001800e01041c0d03941525071a03c0140104140b108400b00030002e000d455124006952a03030f030008440c00c04500c81680c01c070060340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 449775287 1250 449774037 449774047
    0x10e06030303161107170c09040209130215160b0a0203040201090306050c1303050609011d10110910180803070b04081305060a020106052704030c0c091d0c0402031315020906040308 79
    0x162080090043c0c070721007207a0110451801c2e41c0881cbc540700014101030885000b482c0802c0071075591030281c00c004c24100b0f41c151b031039891500d0082c40f007400c5c04400b6100f1b903d1903004240c4280c0b860084911a68060711003a542c140b48d560b03240d000b03140040c480e01010505110468140303a0b004a0760005600a9005119500707090003464211404c2c000302c8868010a102402e0551001160600c0c012040c648001002c0303503003402681c02031141483d890b61009051591100c4503402c400c05922140c1ca4811203c01e0945a903c2207550748513102d4090720750101c050001300041ca02c440104040000c820214000c25035540118590360003131802000540d458040602c96410184058600809c06e0040044851641d04225610050142000e0100491f0240e90401e00055954440007004860010820aa51072480041900348110000d2070780c041c10010b5447ca103094026603020b10101ca020714822100c40c0c0c1ca03225894000ca42215a0395002c3c03280385d82541e02c56007e04015400b4020007a80c0e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 449776537 1250 449775287 449775329
    0x909070e1903050f1f050a11070308090d050426071a0406030507030513061a120f0c030105070915032007150618180605040f0506010e06030303161107 66
    0x1411940070038903580400c0c42e000041c00321754241d0403605003540c0d000a036521401e1646018001d01d10f103000312840c0001c0c1c64801c03d640140391610400341c0e003060341d41050210401329200d116a01c0b0750500800c070101c8000b203510341015402d07040d0719501c04950380c4a83e81c91480c0e001e00b003244445405214007241c104a0f464040c01583d9109c00306113410450f9140024410384107078843d84000d40103d9445208004200076500840100075008001408291121500703d6403005040782c1407403107003d410b202901c50b003814014540600d0b440d40300c10b201103081ca00802e082d02d910142e54400c140c0c60742c401140142940d044181081c08a500351944d80c0801d0601da100c0102809108036000e15002081088890842803200b002144d1a000309155502c9951000001d0075110003500682c542010b20007008030804c1c4a40f0031a214038182c80580c0c0e641c005050826504544098040e00b0400000310302c440d100e003402594031000c0c1000140348142008040c07800300e9039040000da803200d840e40c40d604 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 449777787 1250 449776537 449776543
    0x30607021c0801180203060612150f030c06180a03060207080310080a1703070c0803090318060304030f08070306091b18081216020907050a0816050909070e190305 71
    0x20905810090b01652600c0014079001c5401046404025800300110b03200303580c2c00c0122045840d03000051406428501a9140b0544800030b0b85072060195500c0c0e580d2606011910a80f03040b0010a4030b42040c403071000e00c41455a40c11a482d9021462420201c0050340c9480075100041c0150081d940340c1c03600034030745030064100d900b001d086607020b00304100c0000d0300a141c0203001c45601480035207079103070040e064983c41424840100321041c0402003144081000019121380460145400500c0c070340c00c0140251031000761000b800040107107180e001214096090b40d03400580303d25000079140d94800660303013190089160304120610703e4014681461b0b01a50107012444d41e250540b400f5440c0c5206150384407002071600c82040c0e00402e00680030112800e0f403000b0b1603000b81130383d205440c040a00a00702e602c054600808103081c20301041182c4c00b49411109840c007680c6070b007450240e0110800010100c001d0074102008092240d85600b80c40b01144124000d4a000c80044007038258609a41 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 449779037 1250 449777787 449777833
    0x30315090708090d0e01031508010e010c050c030d0b01050702090103120206060301020301180b0303041a130f1206020d09050106060e01020105013305070f150e210a090503060702 78
    0x100b004620014030440800104000c40090001e081070000b80049000607400340525a1001441e02103014000900c0c00064100b244004d00b100003c11044000b10000e40d414084c00d01103440741da0040c401211104526400101ca1000504200e400c1126581c00a0030183d000d0300201da5010b000d03800340328215010040c0c0343c2c100303004400a50a660402d1320103905000e4902c55034840035205c0000d589551000d0089a01911400b1510131021246140e10507503913002581d03410001600640006100800410f1601175481d0100b075907225041946554001c0d400516400d51403540d9500d1700000103000b4070400004000c5034407400c0040b42044006804c6a605130b010001da060200204408901040c00301e0a8200c2c0c0304e6150950400f011700704481c00c0c012008024009803143c04c0000038002d2503000002c101a84070360038482c4240c8040b681d615040c0321002c2c4811100412001d01c1060a183c1c0071305981e100790b14182d40c00c55a0740300003d14054003502c1200242e0454600303010140038194900c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 449780287 1250 449779037 449779051
    0x91212190305060d0206091504030b091c0f05030f07200609150103020f2713060b01030b0901061d030316050c1002030316090b071406011409040213090503031509 71
    0x1d50104e4064000c0b404038403131040440d21605481c032001c0a03000400d020389010303580090310300d2031a02d84003000f1a0386541c4142040e03c007003951148141145d115a8101249a10b6a07442034150389858216009081e800703000704081c01601d504040640c0842c9981c1203140b0b08400050419040c01c40d0403a00300504c8040c41500050080018005601e0b40294990107010a607180e0358002010b01480d10189102c80c0d0404086030b00e0011300180d80740e002004090b1a0103510100071000310703003005400325040d0000281e004400b81004000441c081c5c1965001c01104540321082486044002410340e48412814401d6406440d42a014050200b0020b0700b030700b50603500c100412030f80d00c001951b24000100503003440803030340200c40c02c6030744030b5040c072002002c1d084041d985400081c5401a62100d41002c2c11425100300d900000350603500000e9084034080103030100000780c8403502842024141800f55180c0191030b905200e0026904200440c4030b121401c6000d40c1c400340303103801c0188001c0058500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 449781537 1250 449780287 449780299
    0x10c17061e09070203070b240d0b150310060308130b070320030d09030f08070806010f050c03040e011e05060415030b0109170304091b0509121219030506 67
    0x140451200c092024450711011070b0414010794401900701c0c0385200b1450f005282140140600c2404005030b0545d4031100c2c008030011503d01106024002c88801e0501d0181440310000041020300720100b244002090000d01038500e130070811900700058501d103130f000311684000000d0300c2c080920f090300400003038000c22002c946080280d45008004840c040030f860440500f0b164101c580880c10000c403406003d031404148400e142c075050142145c075190048001085410307000648082c8a0855030748500300c161520210300708549003c90f5650030054200c00a171008100c08034034108601002402410308540e4884012400316141c00a03007202c0c0c1c0064002c032010f00c01400f551032440980361041740280340c0000c040168000481d004442644440034034181303840140340400d030100007401a00c1c4220424082e05140c110b0340b001d1908206000d60001c1d01c140500789940c50f0458042000c1010305049622403030301d541044605070f000e1882802e10100c140101001d282d018010709500540482d01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 449782787 1250 449781537 449781559
    0x16080a0b060a0518040501060f030b0a05012703050708071d071d04090b0403030c020d0801030503090d08130906090c0206061305220c090b06040b0d0b0f03010c1706 72
    0x4076409000310410391080c007001203804900744800c440700b10113031000100107001d00e5139100c4c0007418241c500020800040d0901500558604000314a0170031280d069690400201d207a0000c44120301d000300b201d0440101d03081001001c80e00400c0704034040c1c81840d001e04241e13841d010b240c1049a84400d80b00a41e00050010403220070b4101d001d11515041e152940d00707442d9810300006000f05440f100041000c80b4090900080c542c0c540e01809540d8865003c4076800c4100d0f030400d0f01c4d403400910006245034420004890a814080d82000c505449020103900300800d032642c80c55405015000101015564a02004010b0f464026040d1241c1c1d030b030020340458140390010510070010f84030b840d9000c54441c800728816010140c400f55000c0107555002d02d0003e000e2601c82d410724440e1080d011001c1c10300c1c868514900c1c1500c00c81742152410340c0100e00e0a410028080d024240c040c02070b03a8044000d00c0c0d1840341da1003c1c0600300d12210321741d40f5500305401c6c0b0910070344440c1000e001c0394000c1b802025 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 449784037 1250 449782787 449782789
    0x609060907060203091e133201120204061d040309060905030d0c050c0402180909060112120e120a030906030203060102032706041d0106020318120a02060316080a0b 72
    0x1040f17654030304054500024038602e01c07404081074032a4040701c0d41c0000d035131628a40107001c02c0e40f22600c5005072000c58041c2605220109212030301982082403070160303281c0100002c0e1144c5c3c21145410b8030240c4003060a90b034030740100840c01151514450700040b42c0f81080109036103c06180081e005600b0f001480d14103000200780d840300070154000501c01f00d1410310781401010020309200c003900030810740d587c0c441d209a28008d183c00c1c400c454020310074000421500b420200b0000d0507a65803180c01c0410f418a41c480180b0844070f081e02c04280709c02c00200151644031103034001050110000201f0b0400280d00d0010520f251a510002c1098070500c02d03c403503a85d000c0110b130030912800d01c060105007000c0c01c4010240c01e00540080d4480d000140019056045d000c0d4801d0301140e0700c1c40344019a907104426a1030384511421840d55442c4c40844840c580303405900150301e550400308440420445902244050340255040c2d40c40c1c01080c00c03d203014551081c0d50b9944080c03034000c20720010041d20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 449785287 1250 449784037 449784043
    0x13020a0308070b0f150f0a0f08030c010e190314040504060e0405100b010f0507060b1903140d172d060a0503070f091e0c0504030c090207020904080f0f040806090609070602 75
    0x1040c2c03035124214291003a0721b540c0e10002180050050240056101a0b55080050b42c0368484a00c14203a542041c0d20a844404d01180d40c040d4001000c26500c0c03900303901e1b41c00701c480600003004070084480070f000104080d01c903481058040c18034103070440400d0409007801441d00403801c40340d50300350342013441100440c0da0005c1043e5411109081098803403000d4070b0200c01402ca0b01c458203801c641290803062500e2406501c0c58200ca00403440c620321105040303261a00d40450680c18404251501c0700b19444004500782c480c2e02050f000c03407881c40e40705a040304030040b14082d11b0f11101d198140013800000d26002c800c0344001c140031401000a82d1038104140c4140265115002d1442c0d614404041801c00e4541c40e41d1400d51420000c01003100f1908000e895a00507000980311052211404551001c0034800c88000c0c0740c0003004401d00d42e0b40d540c0c070044107621038044081d42103003d0244c412600710510250002d000440d01a00a92600c04d07440c0340340200003441407006a02006003040510b0b004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 449786537 1250 449785287 449785321
    0x100b071104050a0207170910090f060e04110304141204060813020f0a0915061d0409110604170c0f180601050f0a0503070927020313020a0308070b0f 65
    0x2a03902080c00c1d03a48443c1d007030090140030340203051158060840c4840c00f00c908000c0400410480f00000d4210346208100c4210200d4022041004546001880300e14090480040b0002004101207819204101840c44640090b1000c440d908000941c090202d0380a00001840064100c8000d09152820500810805c07001c1e0621941c607410b403004034250346407001903100f2044060720400380c160740c4102c490000d2048200c081500e00c1070b010b0120b41c2621131854458030303007642c00902c405c00e1110002c11004182c4101d0859041c40c020a00220340e407134040280009000d44c10b0003840c414070034206a4203102c0441e178041d10034030514626110680c0da0482c030a00c100300002031010300c2e43d104401a0342d24415140d00c01810300c1d0102c0d01844081e442001148102d5259850040c4503a0301c2c03910f0145e031004080d00c11106c01d11035403d110040030650181d03a108001c40b1302c00342c0100741a004208842c0b5145c0080d44c003240001441001e002c000c2448035004100702a86075102c1c03620f0000600100e0344 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 449787787 1250 449786537 449786539
    0xc070303050c0102040306060e070f08010303090e1e0c0a030501090504030504180b0402070b0103031e0f120912050901140712120f050a060f0f14040e1f05100b0711 72
    0x482c6014500109506603000b8543c40002001a41e4498030501e800c180c0c1203500c1c0002410741001560080d00c20310145040f40c0d815120504041d0620780e6070451001d0085c10b0307021074070120f00030b202101e6081035480e02400100e040d81d540d0340242000103040c0c440513000019420304103018400080e501c002103a0444800e051001441648410001c025101541942d580540046402c3d801e02c81458091812248203440f400e0070070000c8144401024840740e140c901041141241710b100c24013940002246464500340000c0340b81c080d503200b6452044411107503000540c04030303140300e0950304a0300601e410340303210980311b02303014650f41c0359541038100c5099201040a90008028003e6003604110140340c1d01c1982841140351050700040200f40503c94588000d005800c005602d0b803440d41010260740d59500c0c00e800541320507052001078201c44000a4942c40b03210744481a4804072480d01c408034003242000300d09824158414100b03013101d50001c5410100800044c000102e418492802070a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 449789037 1250 449787787 449787797
    0x4031e110703110105070b33010807030203090f030d14061509190e0a050402040f0b01020a0605042f0103050c0a0c030e150f07150606020a080705120f18060c070303 72
    0x1030000105c400780201070005100d2400102405250190005100c0010000301c0d00c809078070b501d1400c5003030542d000240280c04101d401001c204d000d8441c0e0011640983c4070700c00c83e43d06d00c140701155451036100c018403220f10b80e52203680c45034000e0500d02c419042003044400032044e0301001ca00848334810769683ca4418503a0118441d16a82c0b0400540020400000081814a0010204000740c907003150100c1c440c0b440e19402d10350b800018480d140071104180e00400f0a41c240d41e8810340201b40c0136000380d031400052541c001554000d21501e00844080c1414841c4030440e503070014042d00d5003d0298503030903106100552159a10610174010f139600b5161049901c1f9a940105504500108214082841c0041c0c03020a14000b68010000039100d0403001c600c44914001c1c0300b003200d449018000058214600d2040450316690281c044036010303500f550341403003500071503010b50340c800364115030305041c0420700d400003240ba00c1c007001e4403800c2541c0ca01d203006010180140c6511441c040101400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 449790287 1250 449789037 449789063
    0x5060c03030402212e0e1605030105071704020d170703090f050d1b151805090c1b0102090a0603060503191101030207060f06143d1704031e110703 64
    0xb44200070710100b08803105d108100100080c000315858491400e02c0c0c2c1481c03612001c0025031400c0501c030301c070700c10845561032920090f04a03c0c20f9150a82c09801664000490305501c004034a01c40340b824400b480040f0920703940c58140c80c0180c1803103803c0c0d00400422141400410041d00c0f200704461956070300c000ba0b0360751141c40c26803104903060306400a51002c400c45140801d100c0c0c0100d5040421801c6440982d049580d48041003c250400c0b00c503000081c005001c2e55209011196010769003506003000075007000381c0d80d40800c0c0801e001d648544002604c48204011504040c040c0b020309600010710913803c203010303450b401143da1901444504050b80042c0b044140075455000384888915504240300240d0b9a0070264200307031600408600c03a140d6000075210340b09010703019248105494100a82c61000300d9071100340e4080c403c400506000480c03600c12181070410507030521440c0b284c0c40d5868807142d410008560b68500903016810701c070270010780d44248100010007200312a13010005d49902 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 449791537 1250 449790287 449790343
    0x904030309051509100b060306030a080702060f030f0117010212070f090b0c0132060402030403030e1e1903170c07120f0f0302090607030c02040605060c0303040221 72
    0x2c502c65000040c0c00c6260383c070612050400120340301d401d00c825200140109400700d400c11005200030307a51035034140d100340c02c8000001c6006000d00210340c0011708250601244d01468079156104982d1080c01d80084070052040858256408100c40e4440d002103040c03955003000ca40700f6450190903d000d21600000c3c542d0142c0c402c4d003220002c1c152100d101c6485480009241d0302800b6202c1900046404009003488034046030a4060981100b803640402aa04d4007800e01c00258405801a01095150021410760003000c010ba00305001b80120342445400c40402c2d0b05085c100011200241e400d0070900800c0800c0c0c1c2b04160076020b210014400000b0380b10420400300d14451a1802040d004000b101c0c800c01c1c3d50460314003603c1544a840394070300d00c4c1d81050704900f244640d24400d94098020301015011a1103030b488005c1880c806800080c17034036242d03c00203045802c2602c400843c1d80c400000c210440c1401e0307208401c0d05501092403080191415840b60b140c1030820144203848015607005903c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 449792787 1250 449791537 449791543
    0x20412140705060a020303040c0506090d06022503052d04051e0301090b0106080c0403120804020d20040e0303040b0f100906030c060305070e0a050103020a0c081204050615090403030905 81
    0x1804000c0526544c0c01107800c01a480c7d8204a0b000d840b140d00c103c13000600b9081a004036801c2c0d0344002d0117151080e0701940c4410094108082030341840c0c045101c0002c21b0748031700780103641003030007600c51300d0b2038142c0080c44008200000e00c2003c7e004580c45d6218240312298025a000d03140103d812503003422500b810000074035415402e00340d041d0308228403401842421200203042e90120740d2500c07080d0b40c1d45102490301d0300c40c510008241c25800c4c2012250075101e0994690402d100038807070001c1500e00c0c3c9a001d4216080d4202c4000018400118456481c140c458010050350440165007940350640311000c140310003e06442c50141500300050301c41d03802c654160f010381020401004080e80b2814080301c070382c111b8007980020a01c0d00d40440d1682c0e002c0d11a0000513a00106001130036410400110b010f900700d507000b075041c4002c90200000050440000d010021807c2070074070007078902800c101c0d21341107024100d0414131401da4020a150303200d000301281e0160301030a01003000901d51411601d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 449794037 1250 449792787 449792789
    0xf030c330905031e070201110c030d0c1109070306060201200d0c12020a03020a08060306390417010b0909060103170c060f0411040b0303041e0e040f12030204121407 72
    0x4400c13485140206a4030060001070700895000380da6039602c0a60044d0f5441d0f48999170f450b4250305a0001c0c4d100401a4818103812402c0761158607100f80201a4070003090f0b01e04e00c1a5141c0000c25202e68090051640c248110b10700351500c00603c0380400340854290459200d44921510000c2c0c0f500c20b01d4199502410580c0c0b4868242007003107641d000540c20040003500301c2012070002808000c04580c19140003c1e0340360140d0381076601c0e071405c5402640144140c10408520310880c00b10140321804c0e150307880d8040d0009001040120b220b003140d40d50316508462a0524191040c03030200148090020700044070340c1920ba0040c541807042400124403d01e0740516507080c0741c0d40c8105ca00b000f40721070800305d003580102d20489a00000d525000201b10698010140c4150558000e010400000415684ca00c2100038070035020384000c1d0700ca00740d8001c0c041e01100c0a50701c04148480150030031000d1303004030800c801640350440c02e003410080c403c01c6e14210618054492040e00d00c2e407001d0400f0502c0090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 449795287 1250 449794037 449794057
    0x180c0314070815090c18070e1309030c1208010303021b150304080d0f0e150a090f0506040b01080613112d1201020403051e0a0f030c33090503 62
    0x10a40c40703d441d580c82807a0011901c1131440e0145140240b05030410411182e69042da07481c00e000703d95201c10040320b40599200e18140d10403010600c0c8030000c2114455092a940a6540d5540020290800014201c0c01c5c00c001c10030400c01c080100040f0394003040b581d88002079807611f031300b2946808001038000d026a48001006d45c0c40001400704000c030b00700c0103040344825805c080c0100d051240d03003001199450040c00c2c1c203c0e00001003003c0c51041d8140c0b850781c030800c00c4900040e60f0100d9200d4103289141240b044581d070344000c01b4881884280c4a4040c014550100280040d00c1c0c001d2075141e4400c0e02500040464403400380d0582280e642d03902c0c0710743c14026150343d85403030b103101e2001020000a4450882c0180039203803154203d600103008480a407600b00004040c05448074502d005007030040004d11780302c0d004128215001642c04801284040d009a0301e00c110900542060b00b40821320311420060400d1425042c00c40b120007180391509d5100ca42400143d1000340d00b42242076120b020248 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 449796537 1250 449795287 449795293
    0x6181d0a051c11031207120c050a03151a0a080c0307020d0f110f0c0f061602091305030a26041128090c1106040b0a05190203070c0303180c03140708 65
    0x425416182000c0350320621b0142c1d11080401000d03a031081c100c80d09aa80720b80020810070800380000e0003034014a14005804411480642c0d880300c1d00b40100401d154281e048035000280f2480084d071107482681c104982c00c468500e10704184601958035503070390645400381b0081001031984980101c86010341c4072580c1c07013900d14011040041c41c0d1030b00141c5441a105803c1400702c020700c1e0500e94162a44080c5e11000140d624110307030204240404003d01030b030b10a000310010100060301c02e001810030003000341c0343d041b480310307060142e01a04440c20070f1001001242e4070803c8040740050035440c0c2060400c0c1e40c0c40c100e4185000c12406025060041c099250300c5545000482c0b0426034080369a41c82c9542c0c038040070b2840710701c042c0d4a410003030b0750180810a40e2070101d5145010799002c160450b01d00c1c40a0f2901c40c0961014805a070400c981407030100b040e80045409264050040c211080c2c040c0072841c075290000d42d641603c0d89803602014001e00440d80489104140400c0807078003034a820412 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 449797787 1250 449796537 449796547
    0x403030b030a050a0506010b0708090616020622170309040905030d0e0304171203041101360503070b0a120b030a0f050c030102030c0f030402010306181d0a051c1103 72
    0x40c0359104c0b2081c5048400d44108000010030202c1d06003a1001e807070b880070038a0310703110b200420003d6640124205681c2c034040c100c44c2c8801680c80e140207003810038120b00020500c48090310301ea0f5660b0290b50101e007080d0305200d0700c007115210200480d03520039402c032000075001405042c020303d98010700d600070081c51f1410000b241140000400b60049940c90142a0348442c0d41900603500c0e82080402c91507402340901c0840c00065103c040f44c050500c061500c68103501c507800440c00d0b080031901c8509440261b45402c456440340324208440984130590003040501c0c5000c5210103a48101c4c06120108801e140010820003c103030044a207000c2d0060480d09000c0640c00e0101c5003002c081c008071007900c603017000340c0b00a042c1030080d00d1182060102041c2002c2c035042c00300c039555200900490400d41e440101142d42080710141c4140e44454841c0011086010038182d2076151252044442c03e9000980e00b20010b5000078030390980c8174a0000d001a00441e1403816a6030064aa030407807001c0c040070071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 449799037 1250 449797787 449797793
    0x9091b0b0714010b01210f110403050c0f0303030c1315080609100b03010302150d09060209031506062b0e03270d060c05090a0b0301031106040e0106080403030b030a 72
    0x40901a410b0040782004031000600800c2801c075031202d815030340443c020f00c9082c0c00030701c045a5030f000d451100900208070508250900070071910508a070080c140b101141c10b00c1403110030488400840015140a00180400e200088d6680401000c1c1154000e001070703582000d01ca00100c40c001050400341203144101c1d40100a0040340040719181e004400500000c0c00c441d40c03e14034401282e0300c90f40b24511b9642141c09100e1485000444c45010b4882000888404e102901c00c0701006c6010382001030700c44200b2401c1500301b102c051050403985104006001301c641e204c10407034070409021038170010021188442c00306039560a294500c002c519160490309040000700090407540300749100c589680d02c1854501c4102156640070941007528120003800003a520340c4107024103901402d1003410192050000360901c81036400484c6c0981c4040010401c10140015100781e400040702d000d801d00d4201500e60005440506c03401007009440004203040c14080da00054070f80402505603603410344181 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 449800287 1250 449799037 449799059
    0x1111e0a0b0412080615030403050310121104050903040605090d060b030d2604030e04050a0e0a06091e030c03050f1b060402010e030127020f1008010e0705070c09091b 73
    0x104008020510390800a100c5d468440100078604180c80d800500715104d07914122850f80000b0041d03c40400701c4040400c01c10101c4110601480c0302d07c0100100144c00020312003500c1020f011004180c0c000d00c014000990800c06030783c2001c5040c1c680d02038514031030809101601d1123006483d0540030f501d16a2500304da0088000a640ca0983d0b1800c12040c141102d180100104540180004440654004003490250003240d00030f48030150104030380320704a880c142040e220000c116441c07035850002e8004c0000c6180300b108941050443e48450030700a441c081d00404450900404110f40001c0c0b0060031400441690039150301c00c035000c000c01103c0101c10ba0f5a541c16242a408248000c81591540c41c05002d0194a84410841c0c06401880b103181c4a0051050200403a440304001c181c584242d2103400f0341c4200b16600d9544c06a06524003108401400b82c060031150400c0300c10411040441d58503400750003205c0d42501c00050000c3d1a04240b00300485441440f440381d584a200090081108 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 449801537 1250 449800287 449800313
    0xd0609060c1805010c0809040216140a05060901110703080912030c0d1401030201050414030c031501030b150a0e0702010f0e0115061706090402010c06020c1b01111e0a0b04 75
    0x82c8541c90040d8942c001540c02145036800288180e1041010554500b0141c000c3c0030018080301607031560b007180c0e0f522211048002c8460880551040264000703014041000350f41154642008002604024000c0c8401b4428a0005014801c4e40d60203d403213800204a2900380d20500e41d030700703a2242082060340900ea40145000580c85043c85440b502c550b03940b0302d500c0e040301d60586415180030301d011a280050340010390034070b505003d46211030030300707031814070400c11070502080c03040b001c941c15450701d000422000b401c40e80300b0a913140f115100644404001c403050781e07050b449802440ea10b43c0d0049006d0030700741c100ea00c00c040c00c007400f001070394005400a0072014401e0071aa0b00164840904403210b240e4002c10881d400c14410104419040030a0300a40250061400130a0238040e42c0710395003030b41d102c1030b80c3c4252948100074aa00b030121001c82454401401d2a00810465583c0d01c2550784404900082c0c1c040400340d00181986001084040d00943c1c0c004010140d0b4541410056159088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 449802787 1250 449801537 449801567
    0x170702011101020c0c28090b03010e0307030804060b120a0605160c0503040317070b040c050f010804030507061d010f0f050c120f042f0f01020f0c0d0609060c 69
    0x3070354004404400600a6544a040c4a0001d100001907082000f03181c41840044c241022811104010f08008401c51000039240003400400c05002d0541414211148611944100c1d0810b11a103000264800300e40741e08541c0001c0b0200f02c80300140001144243c11620443d0684034070140c0004102c4290440ca20820340060b40225080310110183d1b140c00c503100307004141d82c000700810720000d1003e0b10118407d191030b8500b24100795959031541c0e46130a050714140c0d10800380d0f030420041850b000e981e03100000c1c004e282c20181400d20355000352503400b07240310041a86468156600c2d44080040010b01202d802070024404200102d000a00070101c0c0d1865141441c1407800003400001d0030012540c42055074200000555500c26034103900740800380048070304050144514103200d1784120000c546040c2c42d40e080308203007c408100b001c2e4000010255041d504070410b007009084010400c1c3d0300a90007555419460055451300400402d01404002d001d00c0c88c0a100b000b0f2030b6445194512150740e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 449804037 1250 449802787 449802797
    0x30f09030f0715050610270f060207080d03020702150a0c021005091206090d1404080d080105090f0103050d030c0e0414070206090111090f011806030c03060914070c020102070317070201 81
    0x3505402e000001d0486420302000c04d28180c0c1110324052101f81280034140003004008440b500d618030100d804485d40e0081006030302c001230a200300103040c0001c803d00b03401410110300e0301e0000d901013049100c107a01d45034003102000c16240501c9010b030294892044c0c0c010002910303006034100c040c2072908865100c41c040e021b1141524103803c00020394a01501444d0001c210a0034003000407290b001c0340300c5880241200510001941403401c2140e495490b9035038848107115030414082c40014100281901080c0c42110010404079074003254040c0c40302414a40414400e545d02000d0719608014000150850b1070f00b0380300e81c0e012030f100403414096020341c0d09548030381d210407030f03060f080e01d071000d00c1c0c8540d0201c01c00014543e468101d80ea07544c0c003101814140d508075039640c04030401d202150b121354042502c58082c404840d9040c440d03080a040002d20800070843c580000502101c0000c0072a41800304c180054810341e0300811581c0003d55100c5900741821011544078015500042012400f2034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 449805287 1250 449804037 449804041
    0x11404031e090b070219031718010503040c0b0f1201240809060708100321030605030a2604030203070b0a0f030203130b040309090e0f0d08010b030f09030f071505 71
    0x30348500c02d00d404440c2c140705404e0400003180c01700003080031001d81280e040760000300c00000003000d01422803003014031900392030344410480c0010700c003001134114150b041107410404c0100003144000c1d0103003034803800070025407685d030806a08003440c410700040c441648800c500009035940064040c80c80445c0c140d000d0b6070740d0003600d0000c0d68211400e44c1d03010501d0f00040000303405e017442a40c80301c0c0d01035044207840f001750b6665240c554100c0208010085410309600d45a08a00d800d03004203401020b0503001458a96041c1d101c40e0003150306841040040480a042811408020000d50b00038580040a4071802690f40200d00d0081c0e210110031408180101e026101e030600900c2542d1249101036272a241c0d908041d510000900300080040b41072050b0002d020030100c0c814460103400c03080c01c3d00100081280303400458a403ca91141384002c10115000601c100102c0700152a045103150f107007840346403584680d8604600844000540c0200003103031040c24071829418040f01700341e03255020403d0b5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 449806537 1250 449805287 449805347
    0x2040b010201060303050f1612021e060903251e0c050a030b010603051f0906030b060d051911130501090f0e1c090503010e1c020106060f1101140403 65
    0x1843c103e2002801094042c0301283e40d0307441050040c0049019800502e200c0b180f03a03940c0f6074202d890482e10b040183d03c20740f07401e980b0020844002001c026000002c00c01c51903c43e640315560322440701300c0c4c5002c4101c8000040903141e400c0d05904513503030002030003107610a495500f409005103080296103500100d1000074090034100d0f842815a90032060b20313080d1f0707802d12006802800000d04800d0380621007480c0c1102241c403680c003c80141000b400041407a600e94103282d40010030141041d031140c0c41208500001820005130f4400340c44d80c2141a110300702041c240092282100c00c0c001c2d8000d4000d00000620b00c140d0743c4000e0584016010800404c540e64413500e01704e50003044040c04603403044170136160904d595a080e01c00034099241c400c070203640300d401107070035200541c001703400c00d511110540c2c0d42074861507207006480c5407600c02002120700d0000010520b40b401a1080180700a107088885581401e40142d50201c03c41c0c00848014202850020181c00c1c03140414008252044482609 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 449807787 1250 449806537 449806541
    0x60f0a0207060504150c050309090406020405030106050f211905010b0405150306010b0d021e030a0c020a03020a11010908011e1107050c0f0613090c0801050f060d0507030209030f0a02040b010201 85
    0x280c41520310080c4410b2000401510346c448498801c0c3e8503444103109101440e500c040d0a24480c501c110070142c1c0321032418050500303480c102d82100d44200e26956406196456880481d00656528459840350040b00d00040b407e28800728204142c1440441301213041c0a41500190382150b01034034100700715514640254040781d2015062503058019000420850034040d01074020703400c03980740042ca403480600d180c404c4040341403403520b5121004810004842c0a610481010f020303140044c100ea40b02d6541c3c000e4503540109401422000e06101a10356644201304402c084c1040d180200034075200f0200e04280054602c0d410768a160034001c076001e0384104c60341940ca20b6a8450001d06c601d480b00810040415161541203401c540f060040c0f074410340700c08078650300400c000f080004030404907810003001c1c000142c01650140d0031003118284a62209001c40303450492000f800941901d4025044002c5c3c0305912071250f140c0b1407a650101c941ca400b1441c3d141c0f11b88210350030800884034800681c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 449809037 1250 449807787 449807789
    0x812030c07032a050109060b040501030b040f06020d0606032c120f090405040c090b03011a0603070201291807020715020a1a0108010c020c061c0b060f0a0207060504 72
    0x1000380414002440041d014030100201c006502641024011a180d0a44401d1003000070030f039440d03911818000103005091240703035025071054405000560560301d4220540c3e0000d400201008004110319003401480d0741611100001c02c4014000213a40b400000d010f42008908514403c0207031001000501d5900c0c1301107550840c240c05042c0c080c0740306000440300d800101f10900d498208000d1417000b40c0d118800d4600c22441980c182d080e4900345107510341100c41c0d460920307019030300d030414041000d94030265007003107800304403a0159a0347d1110000c901400480b5076455892491400f070742d0240ba100c1300c008070420010780d442a03181e10400c0d0803681043d400c6e1804009030708a264184810810196090748201d00b50048620407012542e41007008003031090750b040c00001d001c0c014854800203001c1c0d03140c0c41400d0b01c0100360f4254080d0020300a032103104000301c41c1034030b0800900c18901e0903400c00c50701e150004004036142e0030600401c6149a1019031010010f0140030070204500d4014000d4070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 449810287 1250 449809037 449809051
    0x218190b0906150c101d01020c06130201180b09010e0d020a06082502010504031b0b0a05060d0503040e101d041209090513020a06052104020f06070c081203 68
    0xa01e44a0030300303212141a80c44600f0001403000c02c004605220204400d10308011400e1001451860441c12150105246c60303480740c5d681d00400c1640b00d075900004183c0d800c5405c1c408400e001c100c02d0300c0143d489a240c0a041c05c46545100c50024240900034041c0148000a8035481c03440b400c46020031600c00e240e810001d41c0300c00e040d80240082842414180c1d40400706050101c5400b654050845841c031030282c180300141c0d1078004100c20140c0c404200410799654498140c0d00046540d11b1140004008040305034155039200000c2c5142e9640c50400c28031030b004010340c2d640f40d84490301520208000c80d4071145101c8803240010320704071002200c216201c140300b01403a031501c461307076a46554003440c1d1a8504000810201046848042c415140128030a800070030588007203205000601c00d940d4070a1080c00002e00201040048954040d104840f494140c0a0719680358070005441c0e80710ba0001030741080021668108009101d001ca8003034030840710131a0764042d102c410200a900c011a02a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 449811537 1250 449810287 449810299
    0x16050405090112050309030a0b0103020a050d08091e0a0308130b09010f0806040204150e09070816030b0307030812040b0c070819171e160c02010c0303090218190b 71
    0x100700024903c0e4a03e0000c61148054074680100c910019103231110525041d544540030030010402c41c034002c5203090042c4020b6584421005d043d03281d10142e80503070150f050040c4c0e03080030100c003420003c0104030b126580092501601c2a22400c0c03d0324982c00c420016100c07100d4507540428580590b005450301640144e40d01e0201105801d4100c441d4030018007182e820580901011a484c028620b40e001ca1340700665400e03141c00081c0c0c040081800c4041c212100b401120814400f091040459507402140e2a0802041c0076003402c0110b858200f82c0d520103000e07100040390041003100f005182034050344c0240d201d2010760322200c050740141d1160600c0142803d4080001181005032102c0e01151701d00d031070400d142042d11aa94000c1c0c0b58104559010851407042e200030000e5040315103036500b0041d8550b40704604581c541020341010301811020707050084844103001098441e8000100395076010340184aa1540d10061200c40b002c15600b4401e039580f1881140c0d892040740c440d81000c03074001486 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 449812787 1250 449811537 449811539
    0x1701091a12061b0909161d031213030c06030b010f030506010c0b13020909061609180207080f0c07050103060504092001050403020402121b070507061b0515160504050901 74
    0x4480f10701207101694002c10b00c0601100010303a82d0076400d40d11a0410501491078007603541001451419444503281000010a80316426034900144c00b22000d0320108000703581c0c1c0241d540d002ca884a0517032004028003038080d000f2500b42e034150090149031030281c0700c0390003121480d0303c10f4042e160200c4000c0d0000710310b610500045070802401681120310924441000082c68000c2101c07010100d8140d10940d0200b024003001081980c0628250809460200e00d035500f0709003021064100140c00b40090b64001c24030030140860002280c2450121640065444c5001d100b10707515403c40e4410a80801c2c6801c5000405080c81d0090411131a40440000801c03204507202840c9203203d84499410000305010210068855100400010741c074403410725030900e0240440c0900c4c1e00c05030780c43e100c0c0030010700c4075000265000564a09403070082c14514802000520051508845208007a0182c401d0000100004400c0000070b80990028802205d8400d4010f03000d0b01c41d0700c12407042c980c0103000000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 449814037 1250 449812787 449812801
    0x1030515040204021207021f060b040504020c0115030c05040c03111e040504111b0712110301090c0e0405010c02010c02070e1b04170f0c0d11011701091a1206 69
    0x158580d4000d01c014001810581c54405c00c1c01c070f4060807600440540d002120800d81001500c160b1a200c00490206124140c00c001c0d8100c1c46018a1244a00894001c1903201d8800002c9d08000360072109915440a11980c034100f4042005092081c10701951401d03070612500c038800d01500003040d02c406e40c402d1400c040c5000c140300d0a07011032603400d4103040501003c24107941750300070910300c000403131807140c1c40703075011054901c441d003000303603400b001790702c41c06040107841d210103500c00100d5000322210280144100210380034000c21903000300210110f1501041e440c0c04410707494040c0340544002c0245010700602a401c03500f02d9020714001d60300200c010080e0071840d00d44140c0c08a882d08038a0f40c0340898034841c0c0343c03070381040c0c02010150400701c0c03001801010400a9954024080340100082c601407c0412a148042c40d13000d0203082014842c801c00fa4090419540f82480f40c80c180040d560b92008688010700d19591032262104544041004501c0d0003203505040300c4140002d400c0548580f8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 449815287 1250 449814037 449814073
    0x509041202011409030d060b09220b1c060507020111030c0f090d06091b0501051c090f111002150f10031703100519180e030403110109050108010305 65
    0x2810a021503485043c0443c08900d00c030a0f10b030003030340383c0d900450300c03003a14000100a441e8650003151340da200c2070152010342c1d601d908042c82c0d0f03014818103042810325640d404038090400f0340c081a4104032801607600e40350101564030b500c1103000f580100030702d454280c4124280c484007490105800307030a0000c51440c035000302c001e0040150011001c1d141440110200e50780001108050300c40c155202a503009010f400983c2104940ca410980c18005040c100003804034069101a01c61011880c0d0341c40d0304400169100e00b1845802a424504007445031901450007880c017902c29006441141c034440d60180000750502071210900c06400540c0c2d102c01c0301901e0250300500d20a04150000be00101081000c04c902801c0d0346403c4200740d69161004000300048155807202c6d0041817410380316840030b07141c01e0001d8141c850503844130200400350031001c1c000d80a4a542d5076000c1c00300040000c01c004c811800000082001e80300c2d026090f507150015035031030b0424403004d042d9402c04004822280580 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 449816537 1250 449815287 449815313
    0x7080402010302090f030609160b040602030a030b040605090a0b13020c0c09070201150e040b0705070203190303061802031506070201080106080405030d060b0306030f21030c0705060c04140406050904 87
    0x540001e441801171000240341c0700d415203080d41240c000c484040350b9400c2c014078450140003440c00461030207180401c020f5881c400d03612000c08040d0746601c95100f59803650005001450004e1050310182011040d92006003540e00c00c46101d5000f82081c0360030680c290007500c0350440e04402038248042110203000c04840010880400c555890160362003121a004a0340007401c00b03040110418031717145c503101c0c201d01000703410b12050140601c20307400169400600c1c01e0b488103071019041680d809903d02079028040c00d402485500c0705290454583da91194041c520480b000418810614510070030b00c4602d10510f180030303000519036001440250300900780c054200707220b00b0880c0d00c3c18040d04016000c50340d0f560000300d01054000140841c0380f07070030044c5003240c2c3c7c41000684110108d07505100180c1142c00e200d0106180c0100002e400100b001041ea00c47c01c0d040701c00d95505141c01c06083c03a01364028000c1c466078180d003428044503820180710b41000d503000602080300c5616241c80d0300c2000d030781e9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 449817787 1250 449816537 449816539
    0x200705070803040303020d02010501051c02130f05070c020a05042007110d030801080c15041e05040903170a0b0d03030506130f1e0207050615011106040302070303080105090708040201030209 83
    0x1401500150300c1c101080180002c50195018180845000b0030007030130f4171410791103248941c81004580c5084144214001d44aa904450010040c40c12061141c0500400384081224600d0802002401900480307254002c6200711fa00e0f9001584480c100130840308070b0900c48900f991130300040700e04080c0402c000d00100b4000c0481013404810000014401e0711503c204400107000f000c01040319510410485031064812101d69071301b03021080079240c40740150f1141c100d0001c422040c02100514001034800900009002072100d44824203018140942d0881c4240a21000c40c0c0000c5001c8828401c607500d0b2240281807590854040c0c5046010b41000b6007540d47c4901864421005c1d40700d00c3c0b20300c1c4070000b00b6400201d465100e800d00b0ba20100340c14510340344194010850880041d0010170b180b0342c001208240b1060750f00711b282c012550210f15042d06c4040740314140c1808203054001031842c04070b901c281d44607445aa241c106101a009040d00c1134030203c7c43c1e51001c1001580241c02070440028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 449819037 1250 449817787 449817793
    0x503091c141c05090c030d0318080309010204030b0907030c09050618090a0b060d0209220503070525080318041e090209070e010206130204020d050a021309200705 71
    0x41101c101ea01c10624007480c09114084034102d56598042d5030361007010f80c40038003207070404c1c10082a02d602e0140c4c404802c1664920703107517100d0040c2168940329107400c151030680304d00d08400603034001d6121f40000da0740d802a40f0009443c6c0440094103030b081d00c3d440183d20740700130f2414000c40b0107000050080d9600078880b021141401d900300c00054452906000142207920003414a1208048050031050203003240c42c1d20000503031944000240c004071b4515052134120004621804454941c986c000c1c158000020482c040c410002004c2a41021400394601c00c80a4440e0202c4000528404c42c0c41a0b0801d01c01c0b40c0440150480e0000c101001030008a40c40050130b05030381d5132014601264034182e60b0f4920b680c0560500d0a0b000750300c8030705c1d0705040d41d00d82c40f04c800103903440400030060320321044076500d210119140c6406460410104460034400780c200494101c0180d040010b2401d414151400000391800b114090304004075100940320081002072242030100d03030307c1944103543c0343c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 449820143 1106 449819037 449819057
    0x43f021002301e0406090807080310060905210703050313060201240e0a0e1c260a020901051c0c09150e04091103070b09010f0503091c 59
    0x5100c0490158165654900070006c1d25200c90020180e48002c68904108460040135601850424040701d0000c1c0d1a00b9044400500521072254041520f032801c54850144204001d000310840c415a000f080c0c5a13100d080c43d590000110070700300072400908100c240d03420b06c200c260801064580b0301fa4203059010444104045d8001e440c1102d510402050900805610140218a002c415282078010f000c1100e81c0c400079210102022541040d4640c401e03881d03400015480c0e0544c80b0013070303100e40c882c5090100250040c002560501078100b242d001d43c1d000740c200b40318440e1103202e40441c001e02419070043c620070a907072110030800e0f010659030b20242d80008001c6d07254041514002070321001400c110f5226604010b24941500a074580411001c0b2080001d0002d0310081e00c0f0380c118007400e09801c0310948002c03a0207001d2a001080807040d40c41c5a0303c040d202c501110b00e00000c903a = true := by decide +kernel

theorem cover : BRFrame.Cov 449640287 449820143 := by
  have h0 := BRFrame.cov_init 449640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 449640287 ≤ n) (h2 : n < 449820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
