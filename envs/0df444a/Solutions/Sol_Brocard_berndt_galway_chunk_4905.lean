-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4905
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:07:05.273927+00:00
-- url     : https://prove2.me/submissions/951cb6e7-29a2-4352-978f-f83ee6291b60

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 882014388 ≤ n < 882194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 882015638 1250 882014388 882014411
    0x1801050702040f020a0210021c020325021b030309100e060d150f0608010e060d110303181e03030301150e030319180608041b0810150b0301030c09 64
    0x4251001280c0052080040a80030310100f0042d40c0201c0030100180075540305409408010710076180050040e4417514110120309540310001c1d800984003813841d1440080101059004000d151a0110580c0c040c22b110b400700340c418100403210b2000030b441ba420602c80c092070b0342c0f80d1603455a00c202840c94854286620030021844078481c00c486250071030309020f04841400d0354610101d040701d4078040300c21901070b40d13290b040b201c51100303000302001d81030b000010503500d00c0c10920340342d5aa80240300000703094681000192555100d00400c0c24031940d20b00807035209103400c6610000304100da0304910030a07a148000280c4a100c14040c040350b00c41b2540948800134402c401465401e44050300302c0b0f41d80c0b46a01010003859605131490740024000350119125003007035a400d070b001c0381c50685458100d5100c03a075a03800e4580200d5030100038802420070014420508220a032110140b4000000d40b036000640110036100903034110850100c0e041004000195900c0500b80c110f4941078800640486001c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 882016888 1250 882015638 882015647
    0x1c050a0e01081e0c27031e030f07030e060a12050c0c07120501091e050105070e060a110f10060f080d08241504170d050a0309080702060409020a0917031801 68
    0x4c1407030303845c0c8140c043d009031024038919240341c094000714100c80300c0494841c4488200c031181c0b03e03c0003050b00180005d8500d170710307104040c102d807034800e00f0b00081208100f404641e06421240200c40005d0396140c0c0700b0f005603c0780c03003070581081440300e400c1d00d4208003807120384d40d503201c500c50030f0b00790200440c4c1da03001d0240031b40c040031440340d0086d43c4c20181002c042e4860140c3c0c550801c02e0704c0d2540380101007540c943c0034402d581c030040d0010f0710240c14000030140c1914060b1071040007400900442c2d00707403030b10500140f06102412421442c00242e00b424a044040b24240e80d804c14040341e40b00e113020540e1240c0198005038000303012508144c12145e41b040b00d890000d8100c0e00315070051403c0f08150b00e1480000060800e0716400030b40780c45254a4403a182da0344d0001c04159102052040020741c2e035151098016912103806604140e24110050b8003180c0e06600c507601a091040d408030f80760a0266000c031100000b09500c0011501c7c035680191004d45910072030401c900800d90400c0c50320802d074080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 882018138 1250 882016888 882016897
    0x70201061521020706020306011101090c050f011e0818010501051503090f15070f0e130c0e060408010f05010608072a02040c0801080f07081e1c050a0e01081e0c 70
    0xb6510640d100d00461030114081d410a6a10318080350000f102c40a50b45414482c021081d600200141c0c80c461804044c042205d002c40140d80c10005a24070040729024400c2004140c0c0c559544c99040c9450008481e051507064032265800e40e034140401046195a0b41100500343c0410b64101540c82c0c4030b1350185441d00404010560040c001d0000a504201050940c01d2140c9416101c0c559000e015650441cbe05441104000c0d0b8001100e480021035190154000b82c0b00300301504002e51070003030f90000248160060703400a40680e44402e4812001095800b815004010905040c8403a00b0049001340184c9003024105460707006003041905180005003031100c25540242080107041002c03030000386118000d00400001d441102c007900c500240c000343c0758048a00c2035016142c03c6a100803100c01174080d440480c01c3d144103484064158400050856226003000c1e140d42d5550382d491040600b0200105d010300b8180311a2804000b40255007019030112240d44101200c4e02d03a0b5900f8008440d80074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 882019388 1250 882018138 882018197
    0x2030a021603020c0906040c0f0e0109090e030304120503090a06020c0a0606090f060b090d0212010e06010f031e170c0a0804120501110906040510050705100507080702010615 76
    0x7003458081890307004107248441d81c3c019682d201c081c0e0340d42e406007c19180743c601c0704000942850410501da0744954000b40380e0030380526041d8a110b03607a186101c155640e800b0382661030b400010600040212240001013110520b003012030039454900e00003911201440c4000c0c041c5600000e80c0840203006000c4d103003c2940c4048108229616840d852000704025541b8413a16468250042041c00300c074010748249a000818070100d4040035402e03c11400003060788502259218800711407000f805004d0f460180559007800142ca07031039410034044a00b03290740b2480141d800000c3d180f0101d281c2514208092403510189943c6070240100245402d2002030060f20051001c2000300d06050030225000440d40160000c0c410980100d898010310f12460301d1469009a0400041200c3d0401d0110094202e034103003091810b01c525034a40c5400d0131611103001c1240d51340c800401c000c4507000080150000c400d84020003020b4281043c0c074400004510141092000040f141012015042c1e00c4100740d84 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 882020638 1250 882019388 882019417
    0x1605030712050f011d012405061803061501260103080c0f0a0501150b0f041a040b0a0903171606150b070b040614240f1c0c0f0303050d02030a02 63
    0x50340055200003090349064115015401c00f00d16000100d0804007501079880710751461031f403840c0f4004c00c0009a500103d1500940c40c0c00c4007642d0b099039004d22010b48543d800307801d044420415031000400003086c80729001c040324006120340c504201204181d505603079000305c08503030714030000188514200307902a04010a03c50700c101401001010b40042d0880080c003a41220303d29183c0308440114000e5100da10304000007840100b200c3c0d18410400c0580a602d00c88a0b0300d055110f06003414517034042006031012440c20300b4200200610f401014861100d042001803c1c0b07d115040c090030000d5600001d4400c0303860f4180440c4190030000354500a1074007450066480305540b81c416001d0b40d003102e0581d8550300d046050500751a9a4200510480c2c902d40031208095880005016040d0260400d17500511202c11100c890f40380c03e08211061f000040800038495420301d031002e078080f40c6d50083c1c3c840c048540d50030030000c0e42050694100b5401c0d41c0f80075072071356200000f440003401000104015034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 882021888 1250 882020638 882020651
    0x2d04020d0501051e0c041a2521171303110f06150f0303040b0c1e102012180a080409110703050a030f0e01020316021605030712050f01 59
    0x85259600034a02400000c25281455440c0790000d0103902030f5128114003a1614087c0007183d00e03044000746000d079200c3c0030100d110403d00d00c54030b104424014003101d005c0c0000600065458003099031444d4403803103240044401e01e100019030f046400160907112072a9868240304201030141680080342641c050480e00150b4998040c0c40d82c4900c20b50310600c150036400c15547d003a0a11418240d200880540298a060b00c0c18000c401039078041000e6003658041e1154080030704540c20203851180042c4401007070001550315412007114000e60100d0900004070800c10290200b51003610541580b042c2a841c895071200320b0300c40d00c1d50902501e000580500d503c01d1040011440c050010741e03800f04020406128401c80c051000e02c40e90308050007242c81800200c00a9100b5081700411803100d0030042009101c41a42030b00ba40c0050b1240c074000715090b02c81c0c2c400715504004040d440c0d4a55141e03420035510b044040b940340c0c1c441e0b0041180210b40240e498080c4001007003a001605130200080081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 882023138 1250 882021888 882021901
    0x9040f05010e1b030703021c0510020406050d051021020102030c0f030a0f0c0c09180f060c020c040b060702010f1110060609240305191103040b2d04020d050105 70
    0x1507001d4a03580300c414454043d40300d032003400c0c005a00310a5903030280c0f40c00841e0443c1202841180002141116517200d150040300004010740045d000514039911181d48840e0251440030648000500d030141100e00042d0421960348401d1406045c40c4003030f185528000b595000403402c5105503c0010258419074446c000e445000000030620820640c0d100482c2c0d0442c0501211030520008000c0c1000301e40d500f0911804400c2d0380038440c00140e401d000c0f40c41b07101581d03035101c0700c46010038280d03642d5903603280f4811040e0b0184042170b10420b0443d000c1001c400b0b5100002d41e02d02031846c010f41001018035040d0300c43c5005002047d0428150b100300c07907001d40c014840310003501042c0500d10006075000c80020314001c2c045480704a145d4250441c080200c42404110300030311000348540d0f4415001080d2068910b90ba00c9012041020b1401c06652482c00c0e041c103e0401c0c0014120180d80380d0096000f03003040880c41420b510a02c81040714064644803070001070104594990301a01a51130720052080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 882024388 1250 882023138 882023143
    0x40b1204120503040f060b0a0302030607030f20220e2503140f06210115060509030a0b06040b0a090b030d050a0917030d143309040f05010e 61
    0x81030344504007800a41103545401c5842c1d00050318010711281c04009042c0c00240260804854000c0107030103424000d540f50000f82c07074480250740d568007003a41c0358240d290160b0640200c00101410105031018485207001d902072903c5040c41804c0050041080c1d1040000440584401482c0c21030b401d07501400e100c001d446a20b0a41c00c800014032081c882c4007400302d4080c1c0540c1e03201c00e604248502d240d035520a12a0f10826005126562100c000c1c50801407000e4184201541094080c0000806891104028140c80302503008502407000c14003140d80c541c0e8001401c0840319a0120141c602c3d5141e00000c20040d00c800c040d080e0b400402c80502107240040c90b44500d0000304110304507030849080001c02ea6461290944040000300b03e02c0f0288080c00c00000d01210008007401143c2ca0042c22440140480f071b000e80c14106018098428045201010498500004101c0c980c400316001c00009150240c2c011b00040e6000d49a01c6001a040c0006549280d0b012034000e8024461040c03500f9a664 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 882025638 1250 882024388 882024391
    0x5060c07050a082b170603120d02040603060806060604062109060b01030b04140a021b010c0f121401090e100e28050a020d08070606030c091b020607050a0302040b12 72
    0x4800c10301680000000703442d04c3c01c0c1d400c1d04075403544503903480b880081c084541c8a04018049a050321a054031900840000b1005003102c18800400680b15800c25100805540481d400b072030a0780d000c00284281c640d54402101c0459006080c4049070a8814480000d07000082c01c1600303400e4540619101400136580004401007400da908101111107141080101c6000204005507048440001009603145600074200ca0045c404c4058180c0354840d0340d0b5007910049550080002c0707004488403a00342c1c00489107014458112800e1000c5504095418206c0c8014414161000d8481c4080006010140716001505180d502d052142481c031002e1f46075203c90307139000040a401d1003602c038480540a080700340c2069505c00060407448000d03800308914a070f5040d030140e400c00d9081102c80c000903030620481c0c6c01941f180c008415400d2401c3c10040132580740194400e0800b01400310540c80503404640682c0c4805641483c648903600d40c20102c000703009582060030104d10000b0102e00c800300350502203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 882026888 1250 882025638 882025663
    0xa170a1101051315020c0a080a0b010b161b030f0308010810110d0c050c0609060105090f090c010810211209060c111801030609020f030609030405060c07050a08 70
    0x4410310042000448a92064002d101d9030444482c42c180003a030002c0349460f0344421a0301c101d0f20100035480008840a010740d00944107603028034128810044100310080c01403060398107040c1850181d001440a48030350581c002c0c0784001c4e400d8440504400c0100000140d600014031004201543c030b0042c0c40c0c01000e000b048954821001105c200300030311b0080c2461016040302c150b04051845803103401030f0103000b4115040c0b01c000c0c0601d41d4600300810560f4850b1500340300508165160009201c0c0c1004d018001041a01805040050a40000070b400241c5d00d003c1c0b030210400d0340c46111805002c121038000c2c2034035001e403550180b80f000050495541482c0500390019003104108420381d2440007500c0740f01e011442280449000c5000c5100c00718256034060300c044441d21056818000f602e400b41c10845101e030395141d044c03040d41002103488256400c00e17401008a400c2045c00781c0e50300d000d1885454401c031800501200180000d10802c1c00414010348104070346511820200d4840141b02c1c1e0a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 882028138 1250 882026888 882026903
    0x13060e0c0108091f2c031306051323060a02010e25050d030e031606110729040509010e07120b0d02010c0501020715061401020127020a170a 61
    0x110f1000000403894040720450310300480380740d02c411004040508500a14695071000714043c400c02e401c46410240250642e00c1c025590314070354814074070280c2c0a59000318041200a00006441e000f01106680540703030301549d0450a01841b45160759003117009000240c20000c0803812415682e0150843d20b044078255003a60403400031a8812884888015051614542c07504410881410b0112030b24942d14040e01d8800e400200180100e450800340040e02c40310007203100410414030343c5c40492410300180250103030207142e1401c3d4082c60404940314180400540e20301c0b84503145032039001210002c0c50041c0941d0340b250b94940e2442e500c10b40880e901000b14501d8284003003103030050b00c11010101001000038240600e2900110b0300080d200c0021201036608004050202d21501d58104200d1140076011880c3c47c140040041610410400c0d141560b0500b0b01043c10805012580c1c85800c8442128410509680c0000b41d000c0010307500030b008466000240811441d80440c0d4000310302d02400c1c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 882029388 1250 882028138 882028141
    0x303010f051804060e070b03151018061b0218010503240408030a09060e0c01030c020705010806062a0c0103150e07030f02040f06090305060906190513060e0c0108 71
    0x1d101c0c1e0050b40d0030100046003103400000e4002181a804004000c129004544c0001d4441141c0680c17503009031104070380300c05030107484c0f14540342c03040741c0c3ea2190b0400e181800c101e0003090500c40540800d40200000d01010f102e241501c060b403460360380c050f560000d100d01c10b5000f003241c2d00c1650010a0055074024055100c101452020401c000340c3e00184011340c2c0d503555600d0340c403a4010750300301a140344021a162410340e000318030180541100f10083c0e40207010121240800501100c03489140c1809541202200b00060b0b81c00001542d031008003601e0071032341c4402d0805003828a080300071101c0512011100804410000014a04004402070f20100200306021940400410707951144c800861000780c00210200d100e900000d0300e80c842240054200398450710718104100003504000d000a60040d01001030010400005422542d0403000c1c2041d800c2c00300e0b000300c190111030203022100b0f8460003c100100e4500d0280c14806030845010030000d076100b0b000a1b00c3d402c20068050014040d41d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 882030638 1250 882029388 882029399
    0x304120302040803040e1b03040b0603060105030601180b0607050304080703140106150f030f110703021c05040302011b15050109051b0a1805060c06091204060c060e0307140303010f 79
    0x7007224141c542c8080158101440c0020b03116400200030300044040500c0800420004e6003100594010361007031003040c91520f8600d0905140900580c41240b080c1d00610040000180c00003244000d103c0007040850a51440d1020074090b00c62860000d10902c4000b41c0040d01c014003080303880580784102040603081141c45100c500b42d5130580614421070342218195041035001d000106c0d240b04040c100807529010320002902100c5998040c09a4801c0010f0355804140c2d042c001c414041c0d008025039031284026110040c418052400002d040c001c80d11510340f040c082041c5030781c602c02d40c444000c010a180c1413800e00043e003028400d9200482c2030401180c100700c14070034503004400c4d16007401c80c2448098201101c00c00c900320201d000c13014156401141070f40301c0b00010b103030702072008009008a00704002503d28111a01c440061154000d200c00c1c00040d0b488a40040300640060380403070a0741e40e0040e6181075204026005081d1014a07040b03190f4800b0200c0514100c80e10300034030a03100d640e0381 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 882031888 1250 882030638 882030641
    0x7150f080705030402011b051014010807120f1401061517060405060d0f08090f19050103090c180603031d090a090807020603100503010b06091f020102090406090203041203 75
    0x820382900014604511800145610034014508001c00c0300b48001a5808041115401c1d02c0320382181c600b01c020b0000600a6a8030f24020a203045030642c9040200c075111502c0e80161080403001304401d030309001303112001c07070101504810401c0081d80180a090300a0401d44159503c91510040c0e40c00d005004024940d003808079202a1030a60390343c102040020900141003a0b031100b4001d58083c081505030b410400414481c0030142e0b82d44002204201c040d081c0901440d100314040450310714405403c0d007214084075028200801c00481d9441c20340400340c80c0d07070007003100242d140c0d00003080e40f4880d412070800c990182d00c83d031807007040e21074200d4404685207140f90381000e001c0001c140360741c449503c005043c0d4003a5518504240d5643d00092407544195046004104000800d0105140c20b114407810980704030b50b1301d4a4408510045030501c0412069002c02c0e40f485084204524001c0d0115869044000d000b040300540b500610780094000783c800b80d40c0403000412111710342e03006c1d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 882033138 1250 882031888 882031907
    0x3190206010807062c010908030703021f0e070303050306060415021606030c0c1e170d0c020a030e3f06100f2c010e0601031802010905040c05090a03050715 68
    0x25601c80f81c0281d0104045c469140c44c0c00e210504011895100151603c8288043c10312240300b94041c10301c160401c140105442c0c07123040800c840c14600124003440100004e003010441ea49810919226603501c40050501e0040c3c2d801142d01c0600b5207940c840b40b87d4003040043e102c00c442843e1807851502d82c13400310700719540d1001f01c2d03002c1051f1a28001c00300314083c803d0b41440f024007203004c840940700d660345020388241d9144000e00550125240c81c68031810301030860700307100a100802c5000300b141c0340102106845140d05020790361048a449101d0a02d03094880e20841414500c8030b140781071030b40c04003442c0020300c81e2080b40c002c01011072030115042c007000044601c014036081c409414001c545804410b030b0000c1e0100c20003034100d41201800340649060007403283c41100051440c180c000501034403a10078500494070700e803040e5200141e80002084050760310a590002c3d84403056003043c0c50794451b0040d080d03804149900000108a0300217240015034403907291182c48030f951180c060301d48250 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 882034388 1250 882033138 882033167
    0x60905040f1b050702060d1a03071514071b1401092301210e01021305102a020616020f030609033702151b03040b04050319020601080706 60
    0x7040b05000e151540300340301078000c1e03c0c0002c10492821030b003125488226020910341c030403000c080c6d036852603262030309100c0d00006040d40c0c80400e6142d051014010032070501d03c40300c202c3c0080042406020f01c500188102088072151841b0102291518041780c61208418401c80c0050008400401d80c0b0304180c1d800340b4902c0358050b220609108481c015903448015020250300c00d840c25108940840181c061110301e00030780341c0010b98440d0704003000400034045400540c0282c0746084000b142c5070707118090040310071310440c2e82d21960800200e1010b2008801030701a40c401400704800b400405c2852a550b0710501c00c90380240315102c42803d140c1c550700200c45045060b042800444000c028021054803010150708900a0181d20f01401084850864604d80d00503130100c1c1c018100d080d600c280d00c90308a00549c0c0000010071507111400d1042c800200000c08042901c40401c1c02c205013001911180c0d60b245201d1220745504e0000203544036000d00c54030318a40700350100014210b00685c100c144044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 882035638 1250 882034388 882034421
    0x120114010b03130c1526240406030809040b1f05130509090109170c03090f0d1416140907081f08030913020c0307030f090f060905040f 59
    0x1c0ca019540303106034000a00a140103140c03522910001448900900d01400c164051810010640100248200403411010707a59840d44500c606001d40c0c0c09108540c01020605098201c8120704020700640004102c1075030894103105020041111000107408406410340c0c003040480781a00401c21404100790407e01c00d0405030103080390003803044c0002d00c2032992003030905003403d5651012510071a01103c0003101c0f65035070760b41301040080d109107600440b411745400f1350400082c910880c2d100c1c850303450301c03d02c02d01d2400c224000750703103412044025050300901c03060440740030310014035209c1a20240030740c1548440d40c000320b81c14040c5030480e070400704081d2040c07000381d545010944034421b018151a413004802c00140701b000600e00c080e0742c042d104e003a0107191102c041c041446925900d0a44c0001424014010248082800030559141c103805140c00009100160b40503911003000303411484120003c204003180158104641030300b15082601d0801070b21400304501e01c1268000810001d200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 882036888 1250 882035638 882035641
    0xa020721110d020f010c0501060f0308070b060d0b0c0c07080d0e09010609060e040b31060f0315050c0c031818040b01060e04140a0c200304090203040c050d05010902120114 75
    0xc5d4440e015010403248903000008034162a4443c4003940760190340100c6000703800044000070814207003c016000541901c1d1451564203640d04c14926038001011a86614000300c2c1c03c1c41000340411181004001325826580e85040d500700040c080a4103904950090340403d0000880f284a8850801120219a6458046030b180310410002c6c280d10313203882e0740c84820f2402d030910300d80084949050709594088416034581c00301180d01c0030785110340d204003400031003800d041002c03c05481d16010303189800040004c003903442a040d691103004242c801c10740b80c4400b1401c805d144204840c0301141000480f02c0413055900880700c0c0d640c0d44406c0342c005281064010040000c0750244840e0f48005100074404200050940c64a05802208555130700f5281c3e2a0354110888035007262400c200c4403500741015a083e40c00702034a40d500c0c030841c4140901c8903800400102808071300f13a1084007501c401000d0704144000740c140705000c0e040c0920140d1050902107410060f61105115650110020900c6007485 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 882038138 1250 882036888 882036919
    0x20423090d0246020f010311070807021507030315050603011d09070b072607030f0e06070c08060f160e041802031903320a020721110d02 60
    0x360349a140403980150303201401e211001c40f2074035242600a0440e541d81101031001e0042001c580c0c0c4403140181414070300502c4039100c0903c0c1d0115042c080c0c11600c2165901030300d101068041c070703403681041120360300411014201a031603080002c4000507043c03250350441d290410400188428070501003245029030400003421542c01101c1e40c01310403542a40e0300541d5075660766403c1e80c000368044603203034942002501d502c151200005018880d403103403a81880900e64019196412085c20b050501402000c0240d450340c810b0200e07505260b20a07001c00405d03580e03401850380e40009490030b14001210300b0004182c08054820355000d8505a55001c01c1403c0d03880900c00200480d0714455089026408031601680f001c0000500070152140c55004000d42c40c00c0080506100c44100003016000c58524040c1d1402d2100705a0080b940c600e03103660340d00503d10182c0c604600384d40061401c07000982002024140000d03038550887c000e08501440090a03802c108003c0781101001313501003011402e003800c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 882039388 1250 882038138 882038173
    0x1f08070f15031d03130801090b0f0414011a100c081c0b030304030f150209060a2607030618050c0301170a0b101406030907091503020423090d02 63
    0x3007118070741000904820849680500c0c11030300c108190312980005450300306503180b40a8100101403580080090300d0007940d51a41c01c01f00070300021946c03240d0401050500c0a10200c0c1d40c0040e5507070008200791444202090b00060111850501c41c0407128440104280640007110b50160701c002e490b481c2c0003005540a03101c840f00185025910350f140a422b825407410401080070314061644075602001070714101c03131120056480800002e005001e1800344c0c0d190203080d20050341003410710508665071102c0102d0200007803d210044460454148040a5015170108007610b08400d9810381c18034a816009040d900306540c443e00a000030001000b80010b031070310044c0b200c0d080c0002d803072081c2003e440c0c10740c003040e003078884440202c114001044801070010160a84520036a002425840e04c0d03142c407a1036440c140b00701c449403070b00d59408510001400002c0350141d41d0041003004000055800080040582c00400300c0005480b004100074000004200c05180c00c41e6008011400c0f8440e104103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 882040638 1250 882039388 882039419
    0x903030421021603080315010207060e090c210103030813020918070f030b06011b03020604020d020109120501020c0c0603061005070201050f0d0b1302131712031f08070f 74
    0x704601400c003840c40d5561010003000000d50003446469100d050000142c11401d6180c2402e60642d0b12141c2d080014640200025004003012070300c00d03100d50366030f0240c260644140f02c0d42000358803803c480c14200010160703580341628080d540e4100d15940c0d02151441c00e5501c071a000e0b50241074070380051036209010820038620309059095072401aa50711095052000581007202e000c2c1412003088110750f441200c0700e001c10442210340000b0310460310301944501e40540003902a0f080c04207000d040da4016907240f0000c10b480411018030300340e9410658002d4010090b94841c030f009281380c1d28070b245440d50a80740201c800511074442111402800e031045c2d400720104905120f800c1c002401680342c036002400003900c103031704041000b002c101c2c10001c812800b44910000b151050103c0c1d1214031200c20184113644884960806001508000701d1030700c403102000004c04d48000007000303924400912048000e500c9101c460041685400350745807903042a0280001c41c0b0b42d044020444c08541030441c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 882041888 1250 882040638 882040703
    0xc040e0901060806091c09051807020703084605030714041d0f040c14060f0a030b150406120504060f05090313090203011503020702010212130e09030304 67
    0x40c2c0c95a1402040d0030001d04517071441442e084400059045050844200c1045030a032416011150030040059152000d2424901070780e4480d10006401600030001e00c400b442c3c01c5980503480c3c0500d8440c9010006146034011485a5030455244850043e245030914000b43c80301c03800a01045017200f00d4090300020034840410205a9802010350b2031800144098030003840401401c85606440c200c802030054114901d40d036444003048003080441100e40d065821000d1281600041c02d4002006402210740c02c84600400040d0803c41320b030968894065070009403103500b850100c000c45036105004a20903280031800107d191446a900c03503000e0f030741c094403c540000d00c3d4442c201c004d6049540c03c42d0640c43d1540b00152084400100c2c080c0b040003002c103404194910341c103048a2400e001040504003090540220700c20702160b0003444100248200045042e403540c0414400000340300c454404c51025010700c10106007454008411203124a0b007002d03a070a9144d10001000c19810b01d5942013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 882043138 1250 882041888 882041891
    0xd0c0504140105130918110906130b0d14031e1306210207120e040c020a080307270f0e0402061c150806040b0f06130504030203040b0f1902060c040e0901 67
    0x481c1c200303520310a407101051080488501c031411b40c9440b10030f4401c102c4110348a114076500b0040035903500800354071086100c00b00070440c641c840b0042055a441c250000307061007151080e000501500002030144c4096102c038224003586a907185903803a00c43d035850741400101c210010b020b8180100e5550300b050000800ca41c0a644081c00d000040383c005d0380003100c000c101c040d200800240c6c46540211684001c0343c007001901d2484801075904c00c0b0040d402443d40c040800001c841500846081000409840c4041e8091003041d040c645255210300505003c201041c0c404202004860100c901c41c40d8003030030700c030702d41500f04a002c1c0001e1100e2403040500d40e00c400d448000040006d003038000074204000201400d060919000da07259000802d51449408003c04004265481005013000c1200a2400043c0e030b0700d9506040f42503100d50341025400110028404050140d040020b080342403880701032002062140ea0126203400094807402000d070b1050006001e5880c0103a0042d811080c100d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 882044388 1250 882043138 882043177
    0x939010504181b0302040807090e030d090b072d05131809060f1b120e011104180b030d1d04060308070b07050c03030c1813020d0c0504140105 62
    0x180c508607412410b6110200b6071540c884034070701201140032264002c0f403402d00354146400c2000741075850900f485400d00840c0c4520310010414824030480f509036003850b1080c81216541c0c100b034161800240c450300c00103022840345501d10000048002d6a002d407980d2803111584d141c8108440e15048403624800b01d110015001a41010008034503038504085a408507400c071175800c0c01001c68001cbc16109045508221020004c05a41c0058142411447c1000c401d120841610303807005198882c0d40d90f13041d610f04900780490a42c60009041211074102d000002100341c00d400b242900c041a802c9a015400100008107060040c040c8441030301c04025841511007049000805030b0300c0d903a00545245000180100602900300d6540707501010506110340381103809002117540e03110003800b9240302c820108007592121046803021001c81070051015820301820a0244001d50120a408203613a00c0c0c861800b011f80d0140054404490200d5a00c6080c000d10720010341e181d0b400605521a00c0c0da4201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 882045638 1250 882044388 882044399
    0x1020312040302010501080c0a05030d03020a121509110c06040b0a2306100f09090f0f02030403080f10060e0d030216030c0303030b0915040905120d050939010504 71
    0x11074450307030183c0d0011039503524028407942000c4c108070546000d0a0340802c2440552400681021001010321700165518030301101100c8501c45400001d0038541480c5403150100c000c0400d1b0800d841c40002c040001190485489481d88103080202e0203541003903001502141850000c0d03036000750b103000c0100d0703804003c0c80440180c1c212a6a03c0540d20900010b1142c1420701c109103441e41c90590509000e902e20134000504201d03141d10541a0190322082c04681710002900900c602c825072207030554036420285030103064500111404010500070780005210191462001022a00d1646400c110384040c401800601d0b00c01140036002c0d480b900d50450b0b05074080007450b0009501440f0070580041c11442e00170183c4840041461162001034140b02040002000c030028143c4200c80002d11091986844c605004600301c04090442e0042154035a2540541150340b06c1c5250b0b0054a40e4420400c0c840c1074610090b10800850131081640c00348038040f0100f14000b20b40c01410054113059482 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 882046888 1250 882045638 882045667
    0x1030515191a030403300603030302031e060d0209040f0f0507080f1f02180303041806050a03030e060a0225090b030a1113060e011e17030a0e010203 65
    0x74041201007082101041001503541010b00d020400e4180e081c510305140d28000c10644e007282150161043d6507407010314001d5541c0f04c08040c00500c1c5c0050000d9940d0f820050025002142d401d01c0382451440c0c002c3c80e00d044d1081c0c8031b21400c402800361031100704030f80a0082d41880100304030b80e82e04800c1d80c07003408500d40204110003988140010003540d4217201406041400d160040591584002030400b02c0308450100e481303003e20301880040e00e8400d1488580701c0501041d4009805000019011400070340d001020440a0040721080c0300c4141c0e00c00600074059410b1102400140c071340f4056a00038500040240400c04083c41100e1480183c0060009046503040803030380244821310b000c00059200d80103440c5182c4044001c2c0004115a480740800d540c400c001e1030380b04e104051140c204c94812a03000001030400382c40758004d03a43e1116014014285803000e4420120705405001400084043c9404810038021001d103003040d2540105540e1b01e0b0344203109905600045c007044c980c020a8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 882048138 1250 882046888 882046909
    0x6030901091a0f0c0a120e060105150708030606031317070201080f06030705061309050406060e0c070309051909050403200a0803011403160807080c09011401030515 72
    0x2000001100c6005162001034040703445190740c88560060100080c04942d00006076016940720040d9a40e441044402c462441c1ea110000101c1d5107000a1600e45150015a00341695411b0f9207490b180008004c0030075aa0060340002000d0304001c000141413030810b107006d103821402c6140c2d400144d03090f0366a020007081d40d541b002403c400000c141c100a56078049126038110229004003c45820040d01090300c41b0340307030700030326005c0d1134000f402d2401c40501503559001010401c40800550a0501d491009070100c0d00c903503d11020f00901003506030a2070011108199403544405803514034013001e000999813155124240100100400182440d0a00842d40304a21035640e0481c48104101c1408034100f19020304022503115940d0700c0002001981141c0c1503c0a20303451030754040c0020b000903c3d1004201c12191001c0019000145000000441c1ca0a44807544140d942e00c441c40800d101001c84244170300c00161650110f202c510b9400390744802d8002200c8000c5040e100c8000000c214610740 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 882049388 1250 882048138 882048151
    0x90301090c0618050904031e02100c050d1a0607060b24190504120618080406080a0506040207030e0d0c05041b0e041503170c0a03030501051017150f0603 67
    0x82103c0302240c0003030f503050100c0140c001140c1348000c0e4107080d1001006142c5001c1101c40c0300340b84e0404218018001c1026284812085034103100460160300000c043d50130a40b8111092800c0010340c200c85075101c4510800717154041c01040c10480e05444120207040f200d54216003140710900c1d28011080c1c0808401c09208180010079540c04645204001103c50b140d940804c100c0c09200501c001420100f10f41c030b020703402c940040740c040551417008200010841d4014000340000800196840e0440000c41c0715801c020320801150b075490302407000341d10400900a0029401140842262074100f19219110b80a841c540000781c0e100d0303000c9000c075014550024000c00a400040d0482540290341d0702c80550180c50601c0240030214a40c0201141e5001c000c18481051802008422009090710340b20040a03088484800850030050001c000070b008050140281c07da48511250061203041400380c0380e10391802035640c520841904480c42d101c03016510054048400c881652600b01a500940 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 882050638 1250 882049388 882049397
    0xc091701050702062e0f050f01030b060f070602042408090606030a02090424020c10090b040b0705190e011b2d0203070e0a0c0c0521070501020d0b012003030a02090301090c06 76
    0x7c0c1424200070325a520f200040b810142410709400c12510703aa4159402030841a03105901d07a0b501d0703d010f030302902403900308144c40c50303020801c2c2c0e804440d00300c24545050751176101c9841c00c1d00c442190179281e0508540c3d0603095408007100c0c4005040511006174414029824150030f11fa44406082c190040721a1100100e0b8003c20351210098003482140000080e01804002c4510907940328205040010b20141c030411104000828a1340584202ca4001440b41c444041b101040e1501500940c019001140000d6462075010400d4004400c0b11072896041818a50a440030b85001703441402130301c04003150010b50910300c1006071030800c0030002500c000c0c00c1c40358031403074411102800c03160750030924420417132006c800901180d800308040e01d01c005000043d440d0707170441798125002485229401001c1d98400100260132000650025064030026a42d6170400d0082512003d40480690410b03a1180c20030000b14580074050f60081c101558050000314145000780c42c0d4512300440c0c3d0340240c0101c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 882051888 1250 882050638 882050669
    0x90d050c151303021e090c070b010f05090609041e080d050603010606120209030a0c03050a02011112220b21070201020f030a0b130c091701050702062e 66
    0xd1030701c1400281080090300c41941406264024038003440807910001c3c0c09507035041c04144040364a214140d03070b4407502401c0030f41e05080c0008200c5240c1e00001c419107081040e0400400c5244012040d2022240b00078107542290701c85000b0031440c01000790003190500041c442001d0900d0205105001180c0140189511901e28440c0c00303083c1ea100400031031013a45080d01c00e105254100415006c001c5079050010707126159a03021900d4074034007100143c110b059840000082100000e110b443c0c0364800c1e0b03207001c0c01c0801d080003c0c0da1180821015200c4103c28031080822104001d01141144089a1002066541c803484014a0f03440028000018040510822503810324180c0541c1c010255100841c0340c004002c0102c6190301000c0c102c0c455042e20342895018580d2543c2200e484d40414490030489031800780301c0680311183d18803804020110690300c44c0f1004106100d003621540c01170b00030389195610840c208161059410340e81000420304c0056403550700d26030036184003a1a150000c614030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 882053138 1250 882051888 882051913
    0xf010207022404030807170f07060c0f080604090507030f0c06090b070f080d020c0706120f0608151816141f0e01110604060203040c0503060c040605090105090d05 71
    0x80e070070000e412005280d211800302080c0d50300100f2076040740d0700310a0080d140c1e1303803030302d0141e9441070b4622810b28041c20210b088141c54007110020000d4500c40d002c00c100c1c00c9a0f05c002030707510240d000c1c5403401003000500000c0305424660080650107114106440402c0c0c2c50b03a850303d0910281060654824001c080d040c40360740d0b00310460308085c00101c0b49082c20b02e565951000c10a0540140c02000d03204041105c030305012a80d0161541e4400500507681d890352500b4000b0808a6807048100784542001040000c0f8103451042c002603418040207491012040e4020340c0b00708101034180c00b0400e100c605840c1a240c0c0038040e10100b1480c0c00408003030701c0d00c3c010107d664848507422051280100c10022100c10044007111021142c060800c00a101000001a54841c01e000c0c0b02ca10340340158410082000901c2d8000e610551052a0b0b90710741d252100145551540100c5059004003010403040c04594060030260403000f20515005242020b0b8030085401c0c801c21440480f82070f403007110344481 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 882054388 1250 882053138 882053149
    0x905070503120306010c061121150d0803090c12030307030507050309030304120210020a030509010f020408100b040b060a03090201022b12150f150c320f01020702 71
    0x6000c21402404000030000020200303200141c0390030706000740740280d0030070045983c10240211009122950b101c03000b405001e4402401d600c1031040c580a00e0b00040d40190212003002520300c0050300c860640b04466481d00c07480c3c1d01c00761500c6858450010342c2c000c01d984039000000140b6801010710780740e0406010107400d0f00c0002c0d282c501031010a2080000c078800c0042620b038000e4105100f811501c0030444164242103800341c0600105000060482c1c2581e010740009002d080380c3c100030010b03c03000544540490180e0b0081c4c1d0242e130040502c40040d0030f50f80d0041c54400340000c00024251020200090b0640d05c40b01c0842d001c60740312200d80c000c4d582c05204010075002021301c040148017042e50150b1210001d441140148509000786070740c05080f56100600b1000409070229401d43c0360039011142410510656a841f005034603a4003c1521444075810000e901c50300108041414521030080410b4203505141114440700c00100480360420621182c0c200880c001070780d0780300700e006210 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 882055638 1250 882054388 882054403
    0x50126041202010c030513020607060605091806150102070e0901150e19110d1d070e090607020d020303060f0607020907030c11030c0c0108220b010e01061e111f0905 72
    0x1c0c14582020040808488800340081c154109c90444d135032551440c08000504607034000301e400c07444000c20440000b120b00d00f1092410810390840b1559034402090640320350f821007109005801503042045842c25240f08213400000300800890240c0003102c000520000560100c82424040401d10141e030a50880c440d82c108604130050102460400c0341022502c40c20340c40020301c5580b07625103900b2050f40080a0459030408003030b04d21030b5a4841c01c0c100c401100340d4420001d4098040400c80307050002824120008494001d542581d0f111020000e80d18021300030a40c20031030811400f0010f03071300c010809128a581e80c80000b4501402d160082c40c002c1d8100c0c1500d402e0344104540020301000144902e09401e0905e0f01e0b408640e9110314081c14401341102c4844024514200031081104910821b41030f15a85a01d02a15a80c0c030481283c10408000d80344802e005511110040140b0801c1c3c1c41e0811113444044400015540c1500940600500004480143e541c40b500c0d00300082882400f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 882056888 1250 882055638 882055661
    0x1510030f03080f0a052a0d05043c0f030c05030a030e0c0105070302190201140a050307020c0406050d0f0305041a04050a0f06200c130e070806070905012604120201 71
    0x200168600b103a1100030408030340c0c030711454000f10100ca520765120081c0454407c080141002c1c805401c01d03161071044410708280f00114030f4601d42d0340c4400307900d1000305905024166071071025201003035100c040500c503d0207030a8003000594005040800c1c000c20040c086821035035000155840c80c0d80d807480c142650540300d1410031900b040382c040400da0028104058491094000c1c0c441111440140c601903010311420201c145c1c00306042030000d0b0000c02440c0b01c0c1e1241d8003a19001481c3c1c2007000116050ba00800354017111020890001c50041804010120b20a0a045113015121045c40c1c4803141031108a40888500040c2804a400c00303600071401048024400d00c0718508001000d411003980500c205001041070b0f9800031403010402540c4030604018003c01003410240c00100c1c054410103c40c80454030440358001021100020018844e242d42c0e503405000508003801150b0070790581c0e840482038070000401c698000102c0250602032841000e006031821048600031303081d9050200c44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 882058138 1250 882056888 882056891
    0x402090618011107080a151b171e010b0a03090204051513060308091c0c0303081e0403080c09030f0111030906010605040803040302060d0e0723121510030f03080f0a 72
    0x1300001c980001e0a0158141e010240c0d110700c088100206000f00f01800d48c0d100714007078001a0704440380d0410200c404180010010f000c2c9551490b2104440940e102c0ca40308003000007200401450a04074060001243c040c98042585041500020290768041d0b64141c40003480c140d0203100b900e0404428101ca003d01d100074081c0c540355864035041401420702050003141030307003036180c00807407070200e01194141e22000320b120903500ca00340140740744400c43d07030300c0c42d07080f5006030b00e68527010404481ca01c5513074540c0d2001c0081d55001c44003480c1c0d030041100d0355058841c0c40c1d031510790002c080c008c0104030f032000c07050a42c07a40740c421022894104180d0115007841400c0000303205a034000b000321819250150385955540c0c0702c1810440003070415492500240c002c80c0f00126010802e00d920040740d00705522036a50790740d81c3c0303001c021318030a007414410b01d80e501500040c1c00c000402c803005980005070800c0f060712a540e81e1169800008071000c220006900a000c005020781c860401a4009109100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 882059388 1250 882058138 882058153
    0x114250c080904091b090506011b12032003090307050c0108040c420311040501050301090f0b030304060e04201614070906090506180f0604020906180111 67
    0x403880028030401d50b00034015030f01c4081ca0700038410075085036042e0aa0080890361400d07601c00c5594000c06040d00c0b442d00080300742d040a142039500a81000d56640c100c3c200441445060409500a285284440c10901e80300c1da010312445e10100d02461150360503101a40d500c2001e031400074102200000c409040c03050b110b091001040407000400c0c284c994540e10600c050307107520403601549800c020040c07800b00341c0d0720b812601017001c1c1100c1c601d40d40c0d66841c14410030503011128040d5006501038980041c0c410b10040105241360b401042070b0340c2801c200041c050124901080c1542e00941064010580006d0900c5450070240310b1402c40400c17091280304141203031130040300507100b060318412107846801d080310203000040590340c2944140c04204d8000f1580c500500e8050715040c414401c19070302d0f110000c0c4007401d0a8039840104c480301075520080fa550840440042c120140c0400e400a500780002600d0781c0301c2900030180104c590310360b103914070b0b40710000501c1003c481150142a40041b070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 882060638 1250 882059388 882059393
    0xb011e08070e07030906020a020c030c04020301060e150904021306180b0703030c09080601082d1e0c03030f030405010b01140910030e06010308070506010608071407050114250c 77
    0xe04500340c40c1e5103580c0d1030983d150f00340d04901034035032103602800492000070051017540d0002041000240103030141c4183d11b800e041001700302d000034032500000c03a514180f410400d00d0061202c040201c0c407004483e050580e82000705d0100e0300421b0102200d0b04121070280308941c0c04c101c213030500102c2050080c045a061041c1410507000700c0700014245a128158cc00100303000350341d80700142c061241120b00c19079581002c140d645415a1058011440804460349503154041d2400980c416800081000050300e402101070496000c2080c230450003190418007540d81c051000705007062003460182c1c0c490034941005e500315521004414107212568483c0090981c8a41c256130040d1401c6403044980d014100040c0d01804060003102c07080c0c081c600020041040c8607018004481c0130304201e0300c07030307a0300c4c1c24040e1a46030341030b074403500454242a481004510440024100c0c50b00c00d80020540303d0b450b030036000c603151061380c5120036000260741c0c4615104002c3d6034130629100c0c6141000c032002e5141c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 882061888 1250 882060638 882060643
    0x15062d030c0605030613050408030a0c020313150908010501090c270b090301021b030c1903020a0807081b0d021b0a140a050306070e010801050a030b0f061c0b011e08 72
    0x1d20520b020301102100040065030b510881002141c11a4010301141c1b82900e41500150300445484115500d80404506030794800425620480b00307900c0480302150600c0c00c40c1c4560402948071034100300c0c0d82000450059020b018150003440300301c20108008000c0c6070003500158140c24880040700ca020143c46440c0a102101e00c100c0740758440e1907030303621254401f0a01a00c10704030030491840301d4100c01118840004000e00c425007004050310180303002d0b20824590780c400b810010300180d10a4484001040c005070040c26038234842c801c07240c07400392070414007050b550740d4142c2c00c8055001040d044000e645c05000e8440d05008622000212455a00008214900c01d000f00b0b4400300b54038500500700d0325103c140b0070240034020b04031002e525020100500c142143d19100780081d00e01c000000d50342c00c3c07240306981038a40c007840c00c0340a541c840c0524400240c0c02424554001240c01c0c4100c41c26800c1034441c20050300516244100358102106259042e0b03110419210a07582d2120130004c00102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 882063138 1250 882061888 882061913
    0x7090c260a0e03041e1701020f042709150c05030108030a030f24030614070c02092a07031106010302100c06060f0b07060b041103070c15062d03 63
    0x80c100e0001e00d081e02070190b50b15501503900320411401d17030000740c014a0303c5030054140c21034900c0745c18034003403003085406d85090b8014280c41c50702080b0705000600418882d054010107440051400360b03900c448490455041e00d00340e080c2074131911645002842109400d0242400329505070401d1071441d4134100c2c1d03031607031380c4100b2203200d082603503409054520701c510b03400040000d8a224800c00742c96a5141c9150280c1c0314910044502614042d00420505408a66a403023066180c07a2941604055000e203c61010001c00c41d4202e080381c0c800000040050f001101d1a0440741c0740101c0d1610030f1f41c5400fa22035007003410900d440d035002c4001080142c0e11a40040303610035132071600740c0b5070320894038126002d044140c01400f2034030402c92000c1441c21402024080780344c011300c13091040200c00400d01040300d0120400100c5802e0400003ea00c06000311b0b29610024400e000400484003d2072641084405030f8005a151401d012001c4002046060401c40c28461501141d40707081d01d174bc1d4621140084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 882064388 1250 882063138 882063151
    0x80d0b010906140a110d030b03070618060818010e0c01021504230712050d0806010305060a0918050102030a022808040303270f050714030c09060d020307090c26 70
    0x100010454400c4c1d115030a071440c10303210f88040700c2d1102285000070b40500002c2514a00a101e1602d0001d501c91180c010440c048450718002c000c02420044125441d00b402000f180b94481c5100b00801d040d0300c2485004c858188032000390001c2e50311400024100040314110003445400d0340b05100204105c0c141415000344141c7c6540c145c02c2c6003409903030814006a102915410300052a0f6003803040110340300c08040340c5a079078580c55680301c0005608603203094480c44d40101801005001010303865002c80d00c64100c041c00400026066940c541c02d80c0d00031100014500c0e00824160a4101d841c02c92121080c03018400071042c2d4140d070401020350200600180415032140c0c0c0d01a5004125000c03155100c0c0c90f400311241c021084d00302018a0f11910000301c46a1240410000e0b810042c0944c06c046030350b008006d403000001881c2040040c2ca4098045580010007034502c0c0e006070780c20130100c03001348003921020a04406c1307902e01919040744580354039a1540d100034861103644452801e241d0124 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 882065638 1250 882064388 882064427
    0x2108132f1c1a060d05060910141909060b04060b18030f150a090b07020f0d021b09060f0d0b01150c0305040e0711071412071a0322080d0b010906 63
    0x10340c0c40c00042c5505803210b02c0a01300c3c0c0900e9007401f02240e4042010a8400212001031003440b8006d20343c6005084202c030ba5208060800c010400ea5100310b41210454600031203020603a1000c0000003002c0b2090380d400070640440005d9101c04a40e0600b071164880c000440140c0790780f00c0a201150345502e01040011451041080020140e100c950302c00101150011800001031404c65030181d03640d40e012555803a02c0c4110050080100d100050211802e42d0075009104452502010700640d40c0c0081c1005a0041c2c03807581105142c0c07078142da490f010f68010b017071408640d40b500418290149503064410104500e4141e0350010035005030454045403418190b81c800e60b0703607040b4101d54088102d4120003090040c040000785a260311000040c040804548002c4251088002c0c540d940d90188918207014140e8480481480c40f0800559407040042e030200300280c003031101c4010840603000f0b00312035144020403411040c20355031044001c145801c0c204002d4403070070300b05e01512450010a0640303921 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 882066888 1250 882065638 882065641
    0xb0307140d0c03020903060603071503090501020f0309070302090708100302120f0a0b01050415080a030807021002130e070e09041106070602040306092108132f1c1a 72
    0x205800d00729000003928007000c00c00c01060610040203544545e20302d911901c03801d400300c2d445280109504040b14811a08500e940c0101d00d4150094840900103840a560034404d12901c1981040190700c41c0310944080c280d03040c198810020030f1030000d0b2903542044aa8801c10005000307181d03012041e40c0d0112010b00c0148030302c01c0d00a00d010a0a20290214042e404500d81081801c42215061b5901242c051041620341c04001c80360240e20712400005901003507080000c03900400311030307070080f01c80e2050301d840050111840007641c1c44120103d070498035241c403c110f41070407210001d400440b0341ca4000c803100c80d50310015907001300280020300b11002803601001d6a995400c1214a50703648a81705544580c0d603414090010010308009403640041110510841c040440200345000c440d0303180d1104644400400710350102400340d0807100300d02d2084d410607408030046001e08848450700b11032a140e030012400d204d00065a004440f8482140401d481c0000d6010300c3c0102d110040c05030b042926 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 882068138 1250 882066888 882066917
    0x6010f05042414130c0c0204050a0b0f06091504030f1a04080a122409060602010209033c0d0315051c080910051207080601080103020906010201060306020c010c0212040b0307 76
    0x981c4614000c1c22030711171504100e01e2a05030880c01701c00380c0714021502000213560703488903242950490030702c441d48040c240d8000040c1c5c2c078000000e04250800600350100820010340c1c1a0712503030050b00142c2c2c1100245000c40100a031041005040152103022680141031030340d1440601d0040f0040ea90a1000032144d15022030300e240d1100b41c003122030500c0170300c52203610320744d003d2941c00c80d00940711a28209100815454014000c4600c1c182000c0c2c01800d91003840e0041c13500d00700f0b034100240f440d40a04152001f40303c50700b01c0c160145101d41d902600183c20a2407001d41190b1480d9084282800581c00c10065070b50b81c43e161440095000f8103d140740c00503031401e059103201d0000703000e40c0030030a90304140050398088050700c03901c00b441000310304544030000c0550b1203000444003c1d002803110401030005080070144103400c0389041c000401c000752281d4508050fa0000420502c143e07664031032000103694100808440c1d6207004181d0f80c0351506007800c000e410b100042c000024030107070400c402c2301d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 882069388 1250 882068138 882068149
    0x70b0a120f0606030207050f15010b0a0507060f1a0a06021b0d060c0806100504050a060509030313140f0409080d0902060d060902130e130b1806010f05042414 69
    0x703110600c400304101558954102030700940004006407000e100b45502071401490026451a0b607400b00550151140c3c6003070301000040d0320602400d41040310034050100040c0e0304d4000c400c00c0e10048034010a030305907031103000200c80301d00c0548141f1802c0342040800006401140c1c0050340390301c80104101068502c800f0030f14048c0c4610780188068a442954508079a0211982e40903000c02c80f0725254000b00707a03030105c0b80d0340614016150302c103000300b00070001d1601600007454004000340590b410140410b0515000d41e070070b544100d0486200038442e00c1a4a03103071054039404081142c04102d03441c265103034540c0c540900c1d803640580980ea55401c0e015942c40340b0940c1c480e08a2500e0501115443d0b0f03005202039006400c982002070360151000c20b1604403881207a102d01c049030810035440110782c0310280145405008a1200380714900030049201003440014041d10884581c0700381180381000340310444d0651000c15200503284035a6440e03880700280340c1300442e030741c040485031008001c000055 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 882070638 1250 882069388 882069401
    0xd031205131407090507020304030809010c0614090714030111040e090c130b010806011704020f0103060f09050609070302070f0803090312130203121c050a0902030607080a0509070b0a12 81
    0xd103808803030300340016041c1c2e0009815058441d503000c14004c035150300600303980c7c2c1d0096000c001d091390404e104a04d0f0651040003213014060069034046850784921404e800901e00641d2001440d41000d0801d104030204c9502c0d60140760002d400800285080d03054004490041c2e0103081032007400d0f0008214011030420030380c0807240c401020080d00c0305060448030000c020310303500b850120f104d19001490940c050000b01603090300380324070700e0044e036966401c1000030140203442605050391001d001c151182d9448200700682007140c1e00080034140001080004039004140d0320425004020707540020f44042030042c2400d60249c14a5225110481203900710f006002c200d0081104034010030030351840504001c3c01c0903000383c0c103607003921400c030401d000c46201d010802040d09481c10451035100c2c0040d032033168404658907000504c1001c660010303082841c00d0b0398600000d09000140258500740c1e100d40d0f5002404400104040380ca01400030209008400c0d0840c00c1c030629000c2c2c2240e43e4020380184 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 882071888 1250 882070638 882070643
    0x423100c080702130c080a1109010804120309060c1809060b3a06031506080c060c0f060106020d17011212030e070b1309181b0f060306030b060d03120513 67
    0x5d1204042140c8000c104082c22a140e084c00350a290942c601d6900d03800443d070080c0c3c0c060751071040a80c0c03580c0355038071a004101c006004041d510036160000c140301c1d11420307603010709a98400c1d800c201015104004412a5007190743c40c0303440c00b4030400040000c002110b00c2c00030507443c032183d58850460003810b20440c2c02d00030b43c280c81901c2d00fa051814507079840407003035903c1000b4401c0c1c070900003e070349000c40d2100d002d0300c4001d41c80010341c2009850210043c2c401400200215004d9002c220394441c188078003039010002680c03000185d2800300d500030714014410740c0201c034850441d614110040440c0101d801c1302400e40f4400484101e0018030a8201440c1d0420740d900302c0301140d40c0c030596190340e03030b0086502c01c11641c0ca0500214451100e0f001d0b8003400c10745d405050b2600101c7e5180d9802003400c0c6035810b03210ba000203400240c110014100780c1d00500c42510b00158071407940c20881c1c00780c080184030318401c0307807040380392400a80c0055500d8429043c8010002c2e45540b1059060301006580070f01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 882073138 1250 882071888 882071891
    0x1c0314190509190c0906081902041e0e06070f050a020742081e0103110316270c0818030f04030b06100201050708010605030403140423100c08070213 65
    0xf4501405115060907048507071240e800c0102c46d42d581708994485402d00c400d41070144e5008400000341ca40b54201151480308001d41c00c14540a9803110003c03200380106c00750760f07130b0018410044070640140c0b10f50501555420002e140c240d40d990029259005400b61640d40020348800440d11210303020610050424064109011440300650701038029070130850b50005100340c4009034407200c40c0d02c04000480d0111650300d15036420342d51420030803c588042c46801d4850095031401a0842c01c08940051240c42985072420180c402c0c0000c0080020300351010980c107004403d2599030b840700000b940030501c240800b1a5500b106040350442c0700307140740404190782c04180031007402800007450b40102e008881d904180220b19409170300faa6800c85600000c10100f100402445002e04011135002d4400c3c82c0a1014400303440007004d0540107a045440392038007407400682d000d001c0300c0d0800c0c0082003c40f9120401501c0010051200e03502c28801046250085040011500c03030030403003899030280000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 882074388 1250 882073138 882073183
    0xf1101150806160e030d031a03031303050c0312160302070308040f060306050420072f182e050d1415010b0a0f111c0314190509 56
    0x2210742d5035440554030307180d10003240d080c0403940500800c00c181c61000041c0c0604002c505051041c0c00901c51024184520a0030b030440208544d01030006000c441a04010303114200d0950030b10380c2c81c003031000198600991200c07024009842406c020307545814074807007440740b0f054228a801c07410007059a0005111035070101d004259110089088810741d815076a08200345641c0304c04000c20307104c00520182c1a5524800c032610303040300c0ca100401f900c07400b8509a900f915440144107185840d50081d941d04d0140c10002e400d8580742200d40340700d540c031100001650074144002c414480c007040070408c00d1221040c00c810b14844800170384180c010b0400401801045840303003040400204000081041e9010b2150b8000008803183d0482e8140c620140101d03051000c0341400fa2102c4400c424090144140c600019000190400000b141049100d810861207000c0c10400b60075900b1038052924580e020a040082146401c1c003101c41c042000c1d40d010580391640c200c11401c007051482c0c640c064100300030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 882075638 1250 882074388 882074399
    0x801121109040f050d052718070507150501060f02010c08010b0a0c06050109020711100503010902031b0c0f07090b060d021b0d110c01030501050f0f03030d02160b06010f0f110115 78
    0xd010600b200740071a0106043c65141407690070208258248d2081c2c002c001d440c00300120303415996100986090035840c0c402a511281210136001c002c6510007a00e4000503c450f540c40640030a0490341ca000a20026030b402c2400303040c90f03e05014040c0140c00104001101c103100b8075070341d42e01035040841041156140d440b240040d512124050310498010000001c01d824110b946000904450740c80500756400c24081c100a0740c0058960740c142d0512440300b50746041854004d00450340074000070020b1068540c1e4007400d003441a40121001484d081120040b40c40e68403c940d000410504010383e14030301aa0980d000c0b107030300e420740b403203c1c8102c8484500b5650005485045000c98008444e08400d41400440c2502e03405d000c0ca9400500090032212541048011002c0c10785c0300a05490030000c0c0f81d440e2104980055000c3c0d01d50841803141d11044c0720010080310303040442880d2141c800039140d079010b0700034201622880304021b050302104109800039840b1000e40180202c04182c45079454 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 882076888 1250 882075638 882075647
    0x91305040611070605091203040b0f0a11040b0a0e0405190905010216030203040f0b1801050705070315060e06121905150406060602011d0c04020c030f040b03070801121109040f050d 79
    0x440b0f001c041b41c407400758000030750b04880003030b00e2040d94440c880151645d1380344a03072000220301a200189039a1180720031301c0c0f402c1d100000340c0080c080405003a0f0f1104001c0100501d40007010000a00070fa14080c240140310811105038030031900014400b080350b12051070403d00a2094085040013001d0510505040550201c002c0040302d012400c025606074807221070700480e2080710311611080d01641c000440035409403000d000703001d02403001d440806a40b41c03100e9202c5600d0100541005070b480c401800031000c510a2140c01000c20740b8580b5142100301031655554802100901020342129807280401ca0100b00c07600c00c02e40c1c902003a810500b040c1c60304401502c4a4082d404c00755080180714081c407003c3e500f590214441c0400101021003101003030200070f5110751400801400104003003510704000800800013004c10209140c0d480c41c00d01d600600b08001a0002c0304d8108000c507090002c504204214403c48400300d507803031742c5a280da24007401a0500b8140080c05401140d58001c01e00d6000b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 882078138 1250 882076888 882076891
    0xf0807050111060601021e150702010c030e0601080303010509090a0f03030f05011e03150e0313030209090610140103090f030c0309060c0f060203090f151605091305040611070605 78
    0x81c2c86015210001d101c203252140c0c0100c4800f40164000f02a07403400b401c04e00301100c440081981503e00e4046c01c01c428081c005400c60b814030260303440c0d51a525410354180715082c42007031048041c00300c41d41401182900c1c0e10040c8a40340c8640403583c041800158240844800140d01501c5000c02c16541d16014002e020346201c628565854000001583c082014400308031132800c0c2030301e12090f402d540c1c2d0044a0400c03e05c8094625640300035408504404100400503418003250f81504a0329610421629180040942a164000c841070002100c0d02c510100300f0340c0c1802244000e140d4604c070048008000b400c4000d0841c0c491003511200f03068010115208880c000c0e030381e1340452502d81409407400190305200410b100681018000400c030103a01640d080380400040e120380c000842d82d11441c00e1112840a41801d4058060004601900e100c0c45502040d27410701904200b240000103800748040c5c00101c4156031035000082c200600b80d0300440000791540c00c1c0a4890001c0e080c00381c02000c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 882079388 1250 882078138 882078149
    0x1503050a0c050a0b0a080709051206060301051005060d090303021303230f0309010c020d0212030a0e0a050a0e06010c06020c03250203061b0f19021b1311040f0807 71
    0x5841804160b0307051148554081d0f846402c15186411000c082c21121000c00030511010070003c00008a02c1d6980c0e41081710300705590318000c00140c20400105400c42d0f4010300200044502c48134100056102c04007950680740c0134040016241c250b5040070740c0070f0701c0303016000802100da44802004115121240708800443c04080400440724410502d5444145030340d603543e00d50003440403103000d40c41030818024441c4040c000c9a0a0340c600e40c04240d0035810044040c1050308045034503490240d000c0e95021210408032080b00031145840d0105d02649201d00688061201d2200000e000da40904101c10740c140d4005070856a4500d6008a1074680d00040a0354198003000050740300d03c43e050142c41c89060350024080c0c0595103038078008099002408000c030b610960140118084031217080080e1428038280104030111405da01c1c0000d090001c9042100c4403100001141c15441c0c585100300d0300c040301580e40025000c02c4250340c40286004a60000e0384040c041c5030007040070800425240c08541d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 882080638 1250 882079388 882079403
    0x5030702010e06010605181906391416090e0c0402090a090207020a080102070c031a071d0102100f02070302120c100203150603090c01081602070e06041503050a 70
    0x4144402d0b81d1144030070300c0781e0000503c042c02002140902d07030b01c100120041c010000c01801c1c840350031005001019078841004503411008000c1c0341c0d58080400a01d444608044e00052183c2e20380c0710360043d2290b10041d00600e05490464242c0d0002c11078203d005144c0301490980c10350310840f40d000780806502c6200140100c2d0f540c903180e82402d00950394a070f40010300c00180e45040024500c02908903d90a980c0700800c2c480000e2000020701c000d050940c00740002c90042801c500b00708440c0c1c003141d41c2200004034103004000e03076035502100d00c40005600d00d03203c004104001d00100d142c00340c9024103012880c030f00644114140c2c4076900600e5220f102380c080c0c4020301c2c50003c070301c14203010314802d40106420144000344402c50b9540110b600c46144031084041c0100c000119400350000c40d0401c140c1c0e4000b0381ea840032527030040c038100e900203000c20302602207010400001b9250346c0144548140b009000c0b01003540e5540359000840103c0b51665a04101aa41d08082d075880fa5540d0301580e02c107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 882081888 1250 882080638 882080651
    0x1116050a061506140a0504120b060405060a0312030b120327010305070903060c091a0d0605030303190506030708030c0d0e040b18040303090b070c0501141b07030c080a0503070201 78
    0x40d100311031642c02c03140240c849a2441d18413004400490307200d0303c03070300040103c00c21021420002c1010001c08060203000002e126103414018042119405800d90b0310030b80401030100000b589064020650000b00d142c0840c110f2102c80120700685505000c0900e24000440d018400b00500f40740c00c8031030150400c0300c01400c0c4095005404880d015103d400c00248143c10600c0440d0003070704858140305062401540541c0d690003610041c1c034456560340d141d0400020103c006078900d001d0240582011005140b95040490041d034082c015100a9600c490320348000a140756400d0003c00300400341203065950301c441a040d00c4d51210303032649100340810440005400e1904284c0701740303005007601400121600742c4c900700c0c0a030003d0009104034201601d426004c0c0014034048841400f400707690701c0d83e2100521600d0900d0075180249444012021101c003041040404d005c0ca100e2020401445566910441c8c01c080714904032040e03028200c1800051806140c9601c5002580f084440ea40200405d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 882083138 1250 882081888 882081911
    0x240e010605180c1b0a082808190b1203091017010303030b2103030105011d03070501050c160608160201090c0b0a03060e01090911030a0b0a1116050a06 66
    0x510309115007504294030b50310005001d0b51601001050007002015080000f0755603400e42d20720307104040710101c0360040c02242a21400165a81c010800c103048046101382c1551100001c2065900814075051070303140d818810427814544e40401c0982d0000f1703188802c42606500025904d5101b10111401030b0500100c0301e0049102e0703030070420b140d10070071000c00080c4d10b0340d00c086000c2c103940c07007805510101400c0100c002c42002d500c00703901001c50340080e588030b61608001521044640d5180015620b5000070300080d907030082003030801d4400c02d0808036260609142210f29107004189208120340038a8404503001c1d800c0342e0340c24070421502d0300d5001c1c24034a8810403401d807412000700809102c02c0d01c00a01207004400e000d171070000d80900e00041e11665506240f00300d02c10a0348680c0c40303140d1b1a2081000e200714020080c0e80d8420940003807041da0219030701d5494000009000c1140c0315075030200000c03010072a000311340b103221403200c3d8403e1204d5107060070358a403082084101c0d80c661401918184 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 882084388 1250 882083138 882083149
    0xf0c0906141f0323010e01060c03080601050a0e030d090e07050403050304031b0506030408121e070c110a0e010906210b040303020405040c0e18160818060115020f0109021507240e010605 81
    0x2427507456915520b89883d100e0040d50940c1010030801c0c03c3c003c20300030030307405030300c080200c5000c8108955900340c1d824a801070400103c00c0180500d420007004000601c04514000700300c400b100e90181c601344c009a0741c856080d18601c1c8036001036900440000511040c05180c1c0e02802145549010849950701c170600c4507001d0b43c1064603c8102c0c542c00400103045c8034004e24003000c401c2d01440b44901c0c0390780341d100042c2141c0c055400803022880380c000180301031861441070030094890381c0240c0f5500354001d02040c940c1c0060790b80007060715144100203000c043c441e8050740c0040102600600c00c94001c0c51018088140650aa0f030113581408546681851040e900034041e81e04040303040c4440301c580c1411070303d03a04010a158550056065103a80081003006010b008200c0480307401220500240d00a003480c040d00c412200d0741c0e040082a80150ba0351494624480400c1900030395200d019203085421000c055003039a408041da20300c200304040098014515482140f8020000306448908100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 882085638 1250 882084388 882084407
    0x204090c09090b06041d130203190b15060712030603050a06020a0305060a180c050c0d09080d0503092a15130b04030c140d0f0c0906141f0323010e0106 66
    0x69440000c6d045032502100701150043d00510424000d02d5500754540120303183c908290010100702c0ca44c05085418401c010300b013541c000811354040a220414140081d040340500701c40038044280340d200d42a4454002d6210000030344d8440141c0b40310007001d0810300002e40241c10b85002003410070780059007501d00400e0440994411032054105040c05100c0803005080f09041c11040c8a02000b00d0740d00390781c0410030050340281590b98051158100207a00c0d0916071040d603c1405e102003842403210b0000041070004401000c0c1c0b5800d0106420440c1007030280080341d181a4020000442102100c0300960040500302405078031b07a144666103944480b03513441240f0001e17101020504041c080258411032420240c2002400c8a00040036a11b9180136130b968124100d90030310a001007000100503600400b00108410740000048008850119071030254a14201c40707141456070180f07040c0c0f4000e41c4a0000c003400c28005660b1500300100380305042400b8040c44461440003c00020200e22030300345d00c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 882086888 1250 882085638 882085649
    0x110a110f07351f150b1305030d02030315011704120e15030a0f0902060c070312051207140408120904060e07020a08070f140604020a060f020c060d0204090c09090b0604 73
    0x2041da0720044150005010007800c40221219110340d000c180d030204d2242200041c0c0358400c0c0c001e42e5010382d08204500c0075003d5202c05e00940104111001668011042d0395112886180d61030001100d400100c41c0501d9529003000450340034420301c0140140780d40c01c3c1d00317100070507224515020602d0040041e20748200c81d401200640c10000a40c0d190002e80041080321541080803a0000a0754006081038000c00d40c5034540343c0c8480010418040101d110f080c2e0902203007005c1d85001d17503035080715214007801000c2c2d009000742c0710351010710588410225401840540160398a5214601a400d025400710956610450401202040b103030108a03a49000340203603001400e580010342c0d1890140d0b0020b94050314113070044440e030b44c04213481e41100c0e00c2c02400d04001c1c01440c0380510401808c203865400007400c0000340810901096000160401910401c581654a4035092403e4030003910a68210007082420001040c8055800603039030300c2030f200f23045420b000f141d44480512582d806148584d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 882088138 1250 882086888 882086893
    0x501080c150f091c03140304020a0306091106041401020c0402191d090c21190e19140715051801110703111201110a110f0735 55
    0x8403030749007001848000075182c9500c1c101089600007030340d12000a10034540d0040604295800c01d42c1c81221040f03001c0e240407006c1e08504007500410030b4000d00740802400b181c0d07658444014441500880c2c030324124010f1a86079a00d8441014214440d8558502070151080e814205041d182030f00a540b00d6011110b010440118100340880303141c01c20b040017440c0100c2c241c00c2c2030400e480341801c052190a03440892543e40103085504e05020201040140c000e8001c00140311007170001030790740a0b040005281c080303010760b400000c090520b04905000550064484101360401c0000c0da40301c154803030410295003400e40d50388100740031619170740c0c10040007403000c0120f4104004003c418800748035041c540010341d040f070b1503201d511b4032a25030000c2c5c0d5480038210142220f441c008800e50a1500100000e000c402c80c0203900c043c203406070b0112902480682074242d018080204002c402071549481140c09031a51030b24004407010038001c16890021001581c031181860100c00348006510b00c800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 882089388 1250 882088138 882088159
    0x81f150e01051c0b01090905010905100803130501030f0b0405100302044514100b0f030309040e0a080a0525050c090a061502070503060717041202030d0504080a02010501080c 76
    0x1403000900e00c504c202414001c00384800f0400f81914451540a402c15050004003400d1080114071074901d59800601c642e07004000c080242c502c082c041e24100d51003030070b0100361800b82040000142114030a041d4000f0300e04020403820301c2d980301c54401224025a0300304582c840340554502d40d0284004007000109203d0704480c4111800107041000c902040000d00403c0a240d413a0500900000704a0300c00303074000b03203a501b00c000c060b00c2120f5a00400701c42451800c204600030039128003450056521450780e0f035051460289080c054921280d500ca115142d946000d040c000c0d0054202840e2034445080902007110810704d4140003010b00354000c00280f000040315401c00588440040070040300300d80b00c101c00222100d180340a140e0b4003441d900a885e0b058280403d16281c90401005801045145040e0b807400f0100d22401a030020340000000d800311941c5031090f807843c812850f14a040b149054104404c2c400041c014044104443d03000303002c1666204c0b01255581d180c04065031f0310510040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 882090638 1250 882089388 882089437
    0x30c010219111e0c090108060f0a020a0f030504290f130b06090601021c02030901180b0a05160c09050f060405012103031d06010806010e090706081f150e0105 69
    0x125240b0f120f03814101115404035516010540b0000d003a40308812940c0b1507000d02c441c1303294035480994402c20b00c0e00118109184420020702c2d00c42000640818560765002103014080250440400241c42141d0551842d00a000360000108200c40b0741d5819007002022580d4401c543c090f25032400e8000c8010700d81c0382c8840b4100411010301814160561240040f20610101792401035509d60000381c0156444860242c000343c024410300405100d8490900000d02001040d44107691204029107007503a10740c0c0c081e08002e10285d036190342c040d11001366104000b541c441d00b40c00051165907402c1030f807800c1307841e0841030105a410038091085006100c00f00700c8800400e425100881074080c0c9030100d83c12885005450100300305c028055407542041005000f0b0b00003c100480c010011501c0b011414941500080e440300d0301c0b4040c1074200311548000c0b4981d00c1e40d03441418011508204420b00c165608c2054003140548042c040c00400c01b5600000101d41c000d030309484003401c2c4038107441c40400100c0f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 882091888 1250 882090638 882090673
    0xa020f03070b0402130b040905030a0e0105120103080906120a091406041a06130207080a020f070b0d1526010b0f0a0e070c0f0503030f01050a26030408030c01021911 72
    0x2480116a015910f46c0545c0d0265614000c2a800340d0195020315030b140c1c01200000c0c020390130200c016051000070000e02c02c100c0120002141121303081017107a600c81b912a07001402e10703c2075034002d90b50490201c050121144041e4841d0304241c0c8280b0880c00c01c510a6240e650f1601300c2100c0c00b422421860f104a0044002c1001040c0d02c031100a20340842820340b000324008a811955080e61110000b181c03041800d034040241140c0290414028001c940c90442901e00521811121840c10b1780c44060302d8491800caa00e008001c3c2201150807000322240c00345403200b0f11003a0004102c00d6003130102c48000d0f41002503021440020182c102100d280c10201c06421091010b0100000c02ca105030110004c10a2400c904072600d20880c00f03140d4a06100d0f034184076844041c0c000620410141c071082003242c00b0074010410002c0095518070014000042803411800795034494180da01000070001081d4106500034001c1a0300e02c00d0340b82c240f4440380380032102100900c2545450303074003140e502020781c80b08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 882093138 1250 882091888 882091909
    0xf0c02040e0a030507110a0b0f090406030b0705073309080f030f040c0f0608152202040608010e0103020a05060c011509050103110103110d1a12030a020f03070b0402 72
    0x251001c984030316500180c82c80c00038982015400241d02160001c10000100c482d1107045100310b400c45034407810910b1940c0c0c82c0c41540520a214400050300c0c0c40c1c3c0740c5803500100c00031500030049946520b8520400340096104440445100c0c3d50801d00380005201002c2001c0302c023403078048581842c7c28802001c401000c950707000307a038082e40c240302a40e103000c5250000d6100d0101c1d9102d40c1503a090515110fa240071164201141c0881e11500a210459001c414540c0c04084c4841034503000086101083d00c8854010801f1404900c40c038280048031502d0700280202c680d5551640070700c0c0e90321007100c407140400f03000080d406074814100308240e181c280d0240c941d140301c0701c00000790500c040c501c0b200c58007140e41c0641718450b151401042402100c2c6c0405820307081c03c1c03d0a1007401d1580e000c0159510031030340c840c04a0755450b016121500c074010140402401c001e407050582d03803070821080b5038942100c40001c00603c204650003a1400b004020340714002d40c0302c00c01042a413520341c01c00c4400c084 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 882094388 1250 882093138 882093143
    0x142802040b0406021f140c031815090f0a020907081b04090c0e2707030204030f0b01050f030706092105010906060e0c0403020307052b03030e06160f0c 66
    0x1000d01010800074050001400104500c0d0024008146984501a00003025040d01103a0a14290301c40c803644013102000c560141c00200c46640d070756920401c5905600004400c80701503c1103410804017074049580701402a44604d048540040106180326a1907210b41c20003904061400003280c0028054800203821412041e044603954940d1240300000b0782281c0c0c0310070842a20340400e45003907134206c1c112100c0d01905a4039900310b81c1103514011400110a1480c3d0300d2074480e9000903400d144070740d05880c0a03540c041e8890004030240e061000820b0070a008107480741400d192003911529000443c0b004a803a1a00c0e03440b8800d1410102100301c128111081d00b641c40356844a030005182072054401c40d5118000001d2143d042c005010081708000b44800010201040180701582d4002603031800c4600440300c4080d1541b0f40c0e6030340c007070352003a00300028030005406502200701900f541200e2850300d4150106ca440eaa00c5070030f40945601584640c60205806601443e503284c480d0101c58120b07030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 882095638 1250 882094388 882094391
    0x30c0304091802030607050405040c080c090d020f0301090c0311010306050312090a030b07030c08161205060315010b040806060102010203070903020d1109181605091303030912080a1428 81
    0x4000f5000300781000000c0790f81000180380000e080c40645041d00c01e20102c0700d42ca117000350951238500741010380340c0308110a0600c0b5450300385d1000110358440383c00c0e0950740720141c0284841c1c89185045500d114640c00100d811060001146d290381d403180c03041c0b00450700028020003615850702d42a2803070f03074800d2030150380140310f4181c040040385210226900070f0103159000246481e036000c0090844602600e010251291503030b02d01000c61b0301c1300d038a10000c00b1104000035903803a9580068a085a07007000340380301d6a181ca00001d00c07890150040c1003204d10190995400e961410f004900304d00c4211008004103a520380188094140322039900c030030031700c00c188620155203914002103e106040300c541c842480790341054411450140444050055030b03494a030721484c1494002000094000e2281501000c01110a4241032180c1c1102c0e00540e000240080b118486150080c01414100c0f1410f0000b801c1c0111210301089600e065803141a0040300540c903650b4841044040c056502900c040c441d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 882096888 1250 882095638 882095681
    0x71403040606091b0201050a0903080105010f120c020c010f0201050105061204021c2109031502220f030614040209070503090f06150f090106080a0b060c1501030b0603030c030409 78
    0x203841a44000207041540584561030913000a007504d0008082000d50350504003c5030020341c104504034196030302400e18400c2e071049214200c1d408420504519015403c00032415400d5801140d40c032000c100070382c0e0352007008c0707844d0006a0a9030401e1042c240c001b0410484800c0d9003000c0d000403600075100070440424490144143d01c50081e0b07140b000d56508402c0e03800c18114070b11003803500c1c170500c840e41890102c20303165455a04581110b5414925805d03000a080c8044074451b64601054808214070b50b90070fa0346036101c0000c8040b40e0b003c1107420501c0d21a100c400e0382c00c0c0c84a040d01c00c1c2d40c002c0403180300343d444000407203054001030050380440c800c00600012140c02445103a00ca4010400822249003040041110054505e1079490040703020100500c00250709c442c0d100c0d03003d00700b9040407075000640c0010448900c01c8031010403181c001c42c1c1c1403610382c0404081c5141228014070074a20281c48040c2010b8403403007820310b081019481000b04200c0351045800000c910003280441c500328 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 882098138 1250 882096888 882096899
    0x50d0e01020a0306051c15020304020f0a0b191407170912030c0c04020921100606030f27020108100905010305060f070215060f0d05161d071403040606 66
    0x7a82c01400350340380440e403203800910840c01c0801c4a01c480407407074902d00c107040c04591540d02c0c0004510b507408031031075000400542552640000c521b04080040d0526030700c1981c82c517680382c5641216050100c0a035a5100038213466100b40c9801241c6642c01504a181c070b6220703551034061403801d10030710102038820f01c03500506690307040d03582030f03e0031081018541d124807003c4018103100b11048600d01c40c170b1042c0070700701051301c400400c10700ba40041203449400c107030312441d01c5140c442127483c000e40c001e0400c40046010380c1c0c103420604202c0b8404405008406c0b0710840d00840c4806646030110304c0002c2080e10003d98803070b0a02e25041001000b50300000c9403281000d4040d03643c00d82040c2e807554080310a1045500c904a500d41e4450401e1010b4002c0750036080b0200d600e030360043d0840e841914030000d03c660070b60f107603a09a8019507100c001c070740d2074201c1701441000601c804d00c1280c4031420210003ca82408128440074440c811a54480c280c0c419503032000001ea80000d41b080e50001e0392948003065 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 882099388 1250 882098138 882098141
    0xb0c07180903022413111302091c15020d0603020607061b261e0709150212091c050a060911030d0e01030c0201200307030c050c070303050d0e01 63
    0x81480e8003804503400801c0c1c02d01a2a2821800c07010010030311341000840e40d000e0655040d5004284102d40c041c2d202100d0410700d2080302c4004107a42c3c0000310100c1080507910340e80c0180343e41074003989c80048884520a019442030482c24028000156900000202601c1503005000304040103d000840711748035004038400c0c0e00031840446000342d0b514034000c1d00c0e040b40e2005607420400340c50302c9003011003620400e040e420703c50311083c5001e0380204007065005074039082c018540282141c3c840400e240000c00101702d115103100d424a2450419002d480e96072004c07902070b998802e0300c071006240120360750030b01280c056440810303550111966808000104140039130440309018000200c0d0008150a200d540f1405407100300e446984545208070140e500604010706100b0242000110486000d0041e80500254250f00040c18100c621420500da2070708080e40c01a40030b554100440300e03c141c41901d0310b00c55140510840d41c0543d4040000034810342c028402540e204502049405510a1003030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 882100638 1250 882099388 882099419
    0x150405070e01050904050c0603060d02042f090f1207180203070f0f0206040f03050c03040806041104060302010219051c020d121b0c0c0b030103081b010c08010b0c07 72
    0x5856811440042100d94080741005002d454119903890150a00d607545a80e2003440c1c03054980600c20120000c0d0442d60762404081810350068400d00003601014040c0303141c1031082c109800805522204103031901ca401058540380c2401402a01e036280521041021b88203196020454034422890080307585260f005003155204040360002d030f183d00b880400a800002500e841a0030040030742948034506070300182036500315402a25940440695003002c403140d2189080501c3c0034403000a0010300420005101440b4502448290070324540302810041562850301c40603006a00603403000e80382c94406007042c00c20030b115804480f880000e502480c1c2c50007000da0f9901000d83c20012101400503001001108000003844080000580320100d440c200745c8000810b00800540c03501e0a000c1240028240014088490074140c6075a960305d000c5811345d12001d440110901030480c0700460000500584000c803849440c2c8490b43d070308000c90804a07030001030301c4a0302c501c100000000c3e081c7d4240c9900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 882101888 1250 882100638 882100643
    0x9030715020304080d0804121b1b08010b091303050309101d0d03050403080a09080d06090504170408070b09030102071b090c02030c03040b1b011820211504 68
    0x45031614a01002103003011300c02000c117000c5c410744404020010300303403601300b2400c26918100305c40e0b2003102c4c10039034002c1da200380e90081c00704010721803588084800300a2078044840d51002401819102c41c207201c0b0090003501d03013880326a4400c2ea0140020301400145611940503401c0b1510131031000100815240044902290160724a40f902c3c2c40c58028007100880c0400f904041c405070909590040503c08001c11403c41c0c181d41300100020070031014112a4141e641c0c403814000d05449102a600400b402d417411200c56803400c041e1048400d400301074404445910000d40040340c5000b0200301c40303922074100c03e941175500b001403500044409140c0494000d410a86c1e401d141d0400d202881191507030150401590320922204400350300000844099800e40ca07143d40d180c5440859507070200919180c0784ca215400c29608140619009201c1e0401c90b000300410041b00c007111000100c2d05000c49649900128901c6410b142c00e2440610980d044580034103c17246115401041103004a069a08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 882103138 1250 882101888 882101893
    0x1b03130b180316031e0b010806090607090b030106080c12040f030311070b010510020f0706020d14040602061f080d11010b15030f100b0301141807140903071502 70
    0x4901103501510603200310200141e0040400840803c142e50840b246880300500940700400b401c81281c0080410819841e802046918a540c442c0d41075a12180c04076203540e0203114007070000e480340f032198080c00211015008070314590303400c0940c01c8800a4005185070b0040400b0011031100c801540100380c0300d0b0f03008115000e01c404182c81e00500341e54444445401100d02401610042268441c806044610854461980e0903c0701004d0b41441d020414061640c001c0900c0042c1140e000310322228048000d41d81c240701e290800001c1d103e1030065014800c016403050700056402594006010105011f62512803240c03590384540e01c0c600001c0a40075400038003500020005071409000d06e04058408030b4004504a01c0b11070312a445000081c65101921034843c0801c4401e40c004c2c403020044c01e0702001e01543c035070b140c03400840a00e1101350480d01440e030381d0030407480040d0b042054078058005a66400c5007030b4040000035100f900040600b562501409400040c003c00c00c0c0f0006980d280280c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 882104388 1250 882103138 882103147
    0x1a0f0403030e0901061e030b030a020a171207150b0d0831060804021e0301110318010b01020c061804060603060302100806010e04020c152404111b03130b 67
    0x340204550f060f030050061141c244c43c04031b50502400d106800d020303050b24002071495482000240f0f000c0f500706e006900b05a10345030105100307100000303081841d8020000c49004d40d9000d22540c03480e216580e0050f0001c2114004100d040342287c000b01c2403104028107452020707906440b00d040c0341e4010380200103c4554900c0703001e1141405480414a55600d8005009461038040c0180c02c03100b00a0000744141850031043c810301215070300100d091000070300204204241003100b00855030003925034810742c00800d900e0740c2410105026525a5500c10303030107024940300700d10074490250003001c0711032684100b039041c0444c2a00c4030301c1080000e04003a640401e640b4610b0040c0140d40a0482a440c10400402c00300030f21640c0022031210046004d94006985c1c141c00d05216040404204280c000020880b003809031800d46039410798444000d40c29042c15600d2401308000440341020f14862742980d051105000c0000d06c404007004114805040d40c0ca400c0940c1e0145480040c181c002c8007102c040800c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 882105638 1250 882104388 882104417
    0x130f0b0307060c053a030606030533031e030307030e0a0305070b0c2b0e1501120c05030604030909140123060d18050609070b041a0f040303 61
    0x1c0007000e85060401c441d04668440342c2d1030b15900c80152009807100491300c441c400c03407078000c00f11000b51108006194400d1060041c06441c46104040002c3c1c10000803c0444114140d01240c5c201d400c0e16080c103101d82d04103680c0c81c816240e00442e5050080703190a0301071006165241200c0c03d030704405140d41b80b42c080300203011100c0f01010101c1c40d0b44020072290010360068101c03000e240d004107140b500740e924541000030324420160301d90401c80c8041c41d181007206025080030b042040e0039000b4012841144440c0e070342c07040384800c0190b50700c14800c010859507044404201c401381c0a032600c0e01e0302e1900c6401081c9850340641b802c500048402c28200301e034541d0341c491103009007800ba890010b41d5140c0070500300c40c91020440d030400701141c16032030f548983d1420200d0b4210540300f4018400c0c8001c0c01c0c000040b0f1400d9a0050720035009040001d800c2d40310100b5084196803500781c015040c90705080c0c82d001e540207119609a10740004200c0420390b1280c0c0405000214400c0e5a2940c1078100c08 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 882106888 1250 882105638 882105643
    0x30c0a0c09051e06042d0f0b031b0409020907090f0812040302042f0403020307050a210609151d07050102030d0b03010605092a0a09050906130f0b03 65
    0x9038001c0210a1800040c402d03907030540404411a901d50025199a80c1c8900e8001002042c0c0784004800100101010b44a403e1075040300e41d03242e99104004003d910610380032441510300510103680d00d500560f00740b56000c05580004220120040d00c0010801000d038042122144291444070104940c160100119609004100058042c00e000b50080b06034110040130180102e010092269484008011070000b0180c20001503150210500000468030b8521007140c0d409030200364082c0c0a01c020108881c100300d40301c0b4085070080d92140e0342081c03040301506020314864004541e031945458140c004582c1c820320003845c24445540000b05216a80030007440700501960341d840a400c92007007004140c1c0c020082d00c0314035486400101c0e071958050000380c01820242c11069000001c0d00910000d1002c4c103134141100e201150240817542000d05080c0070b140500300b03084001540c0040244010b04082c0c10490b00311f07001606218005408a410100303803441903060560884d5154082005440d04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 882108138 1250 882106888 882106913
    0x80f0a0e09070207300c060801060912020d08090613060521040b0a110d0e010606080912041202040b03060405010e07050a1a090604030c0e09070e150d14030c0a 70
    0x103800202011460051281c1c03031031101c0c1900a140041108050032010101c6000000d801e500a94094140f600c7d00405002c07100280a860002002c1200c00320700000175442c0002072039001003100642071044d5880c990f0300d6102c010b4903500f01034184111032040794955002809480c503070b183d00d9100c05185200900f040d403000c01c500841f6102d0001e0001242e504400950004414240032507052440c0c10145460310540d41c55414507483d026080b1640f05040d8021400d544140d940c68100b521b501d114280d039440c103202400e142560030403081040d0412402082c08582c800b03003002c1450b02c0b180300001c2c10040e084800355504c2e515491406954007051000700060301040750708044241c14070707549a0084501c0900e05013082800150b03800955203810540300110745c0103114600303164039418180d662a4007912003607103500c218880456601d680c941035504c0740c903802a80e00b2110070401c0c00c01c0100003122400755036561001d90b0071102c0520920083c50503209441c001d1012290074500324001c00e20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 882109388 1250 882108138 882108151
    0x20f0d0c0806090c0316020f07030b090d0e0a090207020a0b070602030901140106021005060301200a0305131709040f1a091b03160207090603060f0b0d0c0b07080f0a0e09 74
    0x50f4010040144060300540e03401c11081004500045126082a8503240c8210103d0b4411300c40d5060000400c90300d10112807040101405440071403940c054103454080703100c251560b114000c40e806200f40086903010b00529800100700801540d92002e550340d6980c04a042640d03a5078000007000744291090143d1140b01004002154603503241810007503c503106c000208841c0ca44a0700407170000d40d0b00750000100c825416140b00304454803056203410300da0050110201007400d0a00180301d90f02000c0a900c125500151101050102600802c01592001c880b042d07009640d0703070074000d19180714400ea0003d1041900c81c2820b05150314200101180010f26100e42114207080160300c00703442c101a02c2c0c2080c501540c0d82d440800302801a814070350380e500200c4145140007000414800d10750804c5109a90600003040190410f03400d124884c4420a0060550025044100142c10040c40249140d9009003030041c01c082c6121818242540141c1d440000905141c3c0e900c0a285018803445030020f5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 882110638 1250 882109388 882109399
    0xa030e0a0221210304020a080c06030712021c0c030e1b041d0313061d09070806040603021f0305010608010f050105090609040c021f022b020f0d0c0806 66
    0x140c0e940c00140c072901100c0a400c0105110030340511680020000190115483d000c2c10b8041c020b9410418119003007264145e106482101002410f1040450b1241001c1c2004d003003286540e484040070341351210f40d0305040012503820000c50294a25503500b030f5008854800001c10400341034034009065407080245190950043c5450140769440f001d40b4509965080d900031820207050324510a1403900c00203410b090740400561004501c54900d103202c02da8a56407a031034401c0c800070540c010400410f0500507004000301001c80c002500907002540e00c05030051012421503100d9001c180d10700c101e030201c1c0040040c002c5800801980502406014010302e1038030008541c58001c07544002d8203581718103414003c0000d4042025201e078001c455903803e001c1d100780010120001c0081d604d4980070307003140f1003a440f0241c54104810074000c03038514030b0304040392100312020f049010708108402c3c08034035501a401c019444181200002030040d0079220b5a0000c1c030450010f20103000d881c4000c100a1151 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 882111888 1250 882110638 882110653
    0x302071e05250e0615120f090d0c15050a0e0732060f030901021e090f01030b0a05040e0a060908130f150509040e1c0e03010b01172a0a030e 61
    0x39000c00c01c1c0c0c0c01324003151071090302e00e07400c0100b08561081d920604c00108068042102139850400d9090050385513008072600554614000c071403080c00b410000f412640d21190a000e0054550406074001d03400c05c02c0041d22048d0400f80301c1c83d00e01c050b806000410030180003044400c226009102507003403c00e07000302c49a06c2160014104d84100c44900341c41000101c0070030f0704072000758107681e41010898607404a407480d100002880d43c0100100750711452080e030903141194401c1c099846580c038060f01d841644da0511080001410920209810b40c1c8522454880469818003603141d0050280420715990340e1700c0f050f0010303030002d40d4100180442d0b0405c8100712204064050b0f200741906403034003c2c2c0794404540040c000c0c0807610300c000140e03c946200584c1702c840c4ca00002c8068810754aa01809441e00018542651140092107022905540c194000801c0385622242c0c400b90308215418504c03034031025a02d800028841d060f41e40f50000c00c500d440c0c20f4251107920b1110b4001c40050624 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 882113138 1250 882111888 882111899
    0x3160206090c0d03050c28050c031204120f0b040303060f0b0306100e01031b090503010606080105030604080c030c010c020d1202031005040c02010204080319200604030302071e0525 79
    0x3d41c811500c01810020005418800318905202540483c400c100d602004048400c810028803516160b091b103490060082e54203071480c0008a002100640212032030134145400b0310010301092800040e9000d90100400f00300249255800340c1c0b0407071094074006025800e06010300151603640c0c002d0004114100140302c17565903041606581450f00c3d103803c01e41e1421541c0101c000d8410522405c0e8095600c0440944180c0c0102c001819078206500800c10144d035006c0881300c14200f071282a400d60420b402040110703100d000102107030329084084901c0e082c0c40340788481c00c545000f0810310068110014078440f03207034400310f00810300760070900942c114280745422400c40403181c4907051140355160024203189000b901030f40c00402802d001d0b00e46418060f07078860000c0d101082c1d2a400911881d8130707480c441860306020030208d40c840000304102d549070340d01500250b204443c01d81c1d0358a0703116a1510050003038201030741d0551182c030250140f9681c004402d085102c10480302604502142400d01c203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 882114388 1250 882113138 882113149
    0xf010509130f031b03030e192117010f0302100c020102060f090c040f0204140102070b3a1d060610180915061101050f150a0b03160206090c 61
    0x20041d08280340c01c60060043c41c0c151030a0440410a42520540c4030a03807041c1501680034022000710102640c1d00803481e240400c42011400e00300405c190b000c18020b070421800d901c0e03074400b0b031001803e098815400d0010440400b482c240e03c41c44803689601d80038021810010000c0340103c155003888401603c5550000c0c0d200c0c500146030280c09299640041c90074141003242c0403100300041c00030003103958981c3e404000703036200d0f000700c2038500d88821020289501c0094640c00302c0b03d40d050140d060400030154100741c10580220804504003500905070304c00308602590901c081010301c00244010040c42420042404c3c020070310f0a9040320007084103588410402441d003001d5440e200780b00c2c2101c2d14040c00c62240a03000304040350301e040c0300c540c07407046100102019601306440c2c01400d001c282e90f04500b0380b00d0071108401030380106004112141403440602144c41001001000071685440c002d5030f82d03404c02c44102407020051902100100d406105003608403400f04090710701e080d00b02c0085003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 882115638 1250 882114388 882114421
    0x504050c03040f0201090e0c04050301111318020f120106020c15030105040f0f0501030b07080f01060f03020702061209280b010303083705090c0f1e03150f010509 71
    0x1808816074041c00f5007160f1180c05600701900000100302018200009050065001401924040d40ca05a80e440f29020104c0c1a18a000b880041501c0d4050a000108040c00428410b08500c150280481c0d01c07a040410040d01010030044842803042d03240400080c5030050042d1a0f5000b410854000a1004041403c0720705585064030301203443d0030f21289290003000340022203410300e803904001000b003001490105011701c3c0a60389030003081e207c2c2d01c0500018035003031003500d010660040aa2040500a030040c00d541d81c00104994100042c1310707440c120510084a0f81d040d150048068110100b6a500b40c01d041c07803048040002403000d40c0d40d03c2c10440c0c4810302020702801800d10005120031080b00306003001485440c81184200107074900c4c4446660f26005000c1c01c1c2d030420700010814003000a4001140c20001c101e640c80e03506490a000c07c1008846031944031403500d1003250010340b8104a1802008a80f01c0c1c0c0382d19500d06640c80a49034201a005180f18051a0013807020f00e40c40c00c1d0000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 882116888 1250 882115638 882115643
    0x42136091505010518130f051e01260a0b0a0c03090201050405060d02070206131404020c0a0201080403030f0c080919051e0307060c08090114100603020c0309120f070504050c0304 78
    0x2590713100a07003225140807100d01c00c41146d00850140c6006c03400605604402c84d0b04510540a00940d241c4002400103586000800000e19401200401214035842c0080041007408803440154020091510b4100080408240d0b0b08610450521128070031510400f02e40e20424581004401c0050340000c2441c0b0540c40f0b12f078480e03480420b998a0b1900a43d046500c295401010319a59a0001069041906143c490a071a034580042c0000030350809000700c800102c034440281c02044503a03030043d58200340162003130302010354071188890002410300c100c401c05030ba80c2c2c4450016182c12050b03503142c50b0704440b080507003e0179007003510000780c4009400094075400402c802402e003503800c18171346140a0281e0241000307040451780c16200ba00300c04c0b406d0040e011800288030000e50421071030f151090071749103400d00d1601248100101c1e480399000e4500c401c88801660f14003004800060040241c902001d10303039030851034110b00e200500b0800100100070640c0c0521952034100c2c0500381500008001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 882118138 1250 882116888 882116897
    0x1204121b0b0a02100605010c0b0c03360f0f06010e130605040b15040e0d0e01051b0c09150a1403010e101a0904213609150501 55
    0x551100341091120050581502082d4480380c0c0b441000350303244015801d040b5280c0c036107400030036594443c0e050b001083d0341100e0f01d10859103030812400500d0303200405403041c100c0b81c0d011200c2c034a01c030320080a1451203100c0036000041406074400741899408441b50200c0e41c00310706c05000d120b2001c41c9550448108101c0c0421690340e075454610800c40c2e4038802401e862410b405c22080160302110b59024070600e1601440320034004007848115501b04007403501a07805481c4040b841d510450801e14540010b14209003001091400d241c4440004d84c1451125000901c0c1500582481c01030140d02443c10510140340031044404210010141d01a500801016038105142900c09411540742148800125643d02c034043c1c04c090f000784010700c0b0350060700c5249801d21600e8a40100c0e0240076076041813035040c00904031000e160040c002d040e4010300b444a040c002c0c001c0301c400c007140c4d0401030750181c0008550503818400c00c6492040c58210b404040d162021090416854030305120944030203082 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 882119388 1250 882118138 882118163
    0x2901171603050907170d08011509050906011110020a03180b01060e060712020610050105043b0406020c0c01090315050c0d02070f02090c040b07122d02120412 69
    0x1107070410005030840c090b019403420007030300c20600001c6c20f40c0b030040030756494103003a9803200781c00c4514036010b1a13503100182c4880c03010302c402d240030440c441d080101410901c0c020300d50b100103142451254000100010f80c003281e003c07406a01030255180000340403106540300300942d515110500010b00640b010054001d089034159121f0008540c6441d80240c0300030b02031640468000e54600044440c400c0c214400700300001e995003d60161015501014500b40140f54602c0d01ca0260080d00400d44210004a1010408801c5441d00090190340101e00141c1d48030615041645080b83c8120708604201b404401080030606084150114401c41c2e500031905448440310310465000e8035140f031035074034070004d0706d001001081d20003032652501c01c3d10500d82c41d589217202e201d5140240e218189040004100b8480010740640309100f84100d282040e0520160386600d42d881c0c103040541511200103103401c158483d94041080240856468001a180a0401c41700301d00702c02e8541c400410321103a0b2032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 882120638 1250 882119388 882119401
    0xf0b04060f02121501090f0b070206160c140306190b1207060e24030403140c011e0b041109040207110d050604030f0203090102070b0904290117160305 66
    0xc12032901000080000e54807203d2089035601c580314150340e0741d580c4c1ca40b905084100e03540140c4031401141c8203003d030311140e1898251016650f501030030381241e110340c04000030030a003101800003900d2580181e4110855600b40841400d4042d107040140d0b00c290300180811520700600794100c00c40d08031001d00420003075800303404100e0600c041010800c1c00d001d001c10100c0c1c0030764800380380d01c4000b000711080d090b02d800d800180602d14003101c0c010716003840304000140210340904820840310041d500701618040e01c19442e682107940c0500c401d4205410201d80009148081c003400d140c41c50b086908009602c6940300114180c448c1c81980d80c000c68002c280c8400780000303000700140368200900482c40d00c88443c5030464407014115000c401081701d20b9a629259880002600e00759601a0000d284081c00c2c2800700543c2c1e000004001c0c1c0c450344a003100c04a00c0e1540c4a50381d080001c40c0200b00c82802c61100151045540480072640c41c2c075003004202c010b400310002c00d030400d026400e00050949807007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 882121888 1250 882120638 882120641
    0xd210c0c0b01080609010c0507110108070c0804080303060f1009180f02030405013206060708040503030712080106050703050706020901020c0d08090f090702100f06090c02150604090f0b0406 83
    0x3100035007841a0308000149480c80468614401e241d40d00003001054911407040d91607004005014014203004001c200455006d160090b0b0040365600700256628042d60341c6406d1079106801c4401c40d80c2010040c413480d03040424919541da042199610900000140020405041c5114041e603906e401d6110040c0104a035018401d154188c850641d5245800d0030014003a00c0180840134200340c0e90001280120250600002031030010041d02419803101401c00106400c10b213001d952040c0f08000c0042c150b07904000910003248203500303149844040400140040302d05900180034000f04010500001e035010003110301040d4804401a2248071100040349040001c1030415007110600390703584e0900403040040c204848e001c6400240d5280700c44288007480c401542e04401590181030100b51081c09078010040c0e03d85400381c0007a01554400c403103000d49001c42c0c200e8015800c030152407004003101001c0d45078445002e850038040d100f440e94030000940314660020f402c2c40d04100c0442c04111030b0b03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 882123138 1250 882121888 882121907
    0x916020613060e0f0303060a0b04050105030a0f18050f060f01080c21010c050d0f0b0d0f020315010609061215051002010204031b140909060a090203030f030702010e0d210c 75
    0x8040b110313000010440141d0b60f501c103813403c80c410300720b000c00000c54502210848003901c5060f55002d04540b116002503028111100700d0040603500d901d841740446c0058504108424014002800c100400c6c5143c24244a000342c02041c0398900c00d001804803010010308100802c8041c0c5200f07101c9c620000340034070690204c1c0f5800409501f00701082d4201c0d54404c02074009410b0008080201403c400b424408880441c002150810100340100020038000401c000d5040d0003e03050351060030402410001c005000d8200310045160080305106083e40101751500304c1c4080c4104000060041c0742d00344121220b03200300d610440c02d190031184ca15101313405440055a0007210885100c0c0c0b22805107525400034050825921b141c003528150a25040c90310710b0084010a01420454490582e042d01900865000343d806110400c408655000e00c20000c610410703041c2c0c00000c6c15034011001a0a0070480340e4108200400280c449002003480600170708010703280c600006095001c0801030302c0c1071a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 882124388 1250 882123138 882123161
    0x71707090204060f110c0306130203030c060a020d0605010305010308030c03040314040f1701021204120912060b01031407020d030f23040203010f180b2e0302091602061306 75
    0xb15000400d26001243d29140021030349070740b24081142c104a564450079180390036410f80c8404003003060481c10200511403d40045c0503070345481c11413182175180c07540982d50b01608503400224030011044500c60319000e09024a001c0c401945076882d00920f42c007019000110504002000c5002c06000c1d5051030307503520307040003415100c41d99583d40982541a51043e0000c201d020481c01401c92018070032a81961944040140765848984502c001c10404542c0c270402e0140504012644000b0b07060303201c00b82445190040b034501303604030004095030b12204450030f41e18a15800d0111b020f801142548901846103400160410541401c9010f00580c0e8122881c0001e422220501e00582d07180013845a0f00940003805080c41120a8070100d072244141001060740720702c10040000e2944181c11307007101c0b883c155203a04189140700107111000210003c5041d150b003000400850400c40b00e600c1d842003503044110900c4450704030103515850001d007050560505000c17a5402c00000780d114540707030803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 882125638 1250 882124388 882124391
    0x130b042307060c02090a020c0d0e0a0b181c050307121e0203130e0106090b0d020f0c0703031403060a120317100608130807030c03090803070c0501110a0507170709 71
    0x596400c0040c111150912082c0c0c000c0b018000011441c4119000300e07617032806494018040824078070310071a2001c85801c0aa984596a4be00004020140d003028269084e048003881404001c0202084196000c20381400050011a81080d012810100907101d185800c0410240c480041c1306048941e610000865403400c03050400d2300030280d600101810301c60700c030415801035054885500c811041003d202d8580001d51640082c45000307d0351018010f800d4021402505108420340382c4031041d001800c80380c1c0994403c0604006241d8003120004244182911062940c02c2120104189500754043e804020a092201104040c82003030310140e0400000920041070030a02d60302815089103103d10800558140082405020758941c006452a40b10351514503180e156541a92a904031007010f0b0300740a03500d4030006a000c000d10052032101d01c52202e202c01141800c0014103c01c2c041c4040c02d80552050700004000740000074001c1c103540e01311070b54603088400010b8951424910390400c92085 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 882126888 1250 882125638 882125653
    0x406050d020c34030c12260729010302150c01090b010f0f080d081305070602030a080a0e060a0509010b0604080a021c2d0b090a0209130b0423 62
    0x22161102080040f0240c2c4015642207020241e0301805030b030240009030521444038002c000803048881101072017441080c10180e429406490070040071000d038110103034500e00180c14000c000b02994400d00040d02c1002481d08101d10311751120a010381400001e0049042401c4510010104815605580c103440001e004009551403c4090b1100038440e441e20b1101040010410341c0540561005032840d103802040d00100c0c480d01102c010740068030811403104454000c80225078140092005000700742c00441d5155555107000388242c00041402c0c1009140c072049485000c1c021942c2c60300445149008110b585030b50552a00501c0c5407295241c4c002000140020348503008580000601d008460b084400304440021990031600c03620002d000c1c1a0a100c11100b0804480c02c03c05040c0c0c001030500200012075940d104039040680c0c0e00c04242d48240d50340001c514002e081940c0c8200808441c094202c4550354200d01c8034000750006102409039014035610384880009100800c01800860fa0f04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 882128138 1250 882126888 882126913
    0x406081b0403240b04020f0f18181506070210030c02070506071506080f0a0b041104060b1c020906160206120f07030e0a021008071707050c01150b0406050d020c 70
    0x103500791404940f2041e0401d071000070140340c54030907907071070354a07d0540781d02d00300409000c01169809646444100107013002d51525503100c542074114803c1704041d28020300d0500d40c841081c0b4601102116100d603400304440300044c0c446503040c44040b180d5080104981c0c81c441810380c00c0402d9600056008032010844906004001786843c181200d103600c1008070303948858420740c5403404006071604661040c4d0754000000c0c00700f210f86911601070718508501c1040030b80000c0c01e0300c8103944000c55844001c00e1240000d03143c0340300840740400307480e005c52500d9200c8005c1991401462809800003029906100035511000200c54116006814080700d501e01003c0203c070391101552503200103854284489017661000807124a21900109800740c0c580128408448001c00101400b0400a00c12405448a40c00201050080c80702c0c2d00c555854803801c40405017110a200c00c10190b041548504200005444d000c803400c0d110140307040313943c5100c00096480644140403640d1028464491391502 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 882129388 1250 882128138 882128183
    0x180a1407031d0105010b030f040c0803120f0f090d0e12070608090d050c120304030c02090f19050c0301140a0f06080709050405040b22170904050c0406081b0403 70
    0x489101629910010b4004412400c90300e007405081da0f500340070000700b0300b062501d5180d542d01c1881000032170b011944600c0107600719003043d107060b042e0b070604100303000441c004940482e0b8004801d403544811803034500c52159607070440550042c140101407406a81b10303101c0742c039840055200c07081152201640c601c001011070314219544021030207002090780e80709120b80100c81040003001c0040403040706e10007507018280d101a10031400d10000c440c8020041c1c503400b40c01c80c825961080c15200f5841c00850383c0b1107400e060b844462050389403004211172918403c003968103440603502103812840c10030002c04c094101e85c1c1c00c0146c8015001e240051810b901034110ba1180078035640b1120000c0d62072041c40241e85041d100144550744c3c0342c000840b0014024241031010300c2640d60405c4900d00c0361038100d45600006604d500d100f1002404449604140c044c041c6c00c03645000400b0714140c0307041d100400b030500280454a81451180500c59201806400d880155410548000400641190300b44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 882130638 1250 882129388 882129401
    0x50d0e03040b040f050306010f0303260f06090702031c0e03120c03221a04032703020306070c030c0b0c04030b13060c0306230402070c030818040605180a140703 70
    0x14a09884134102107514140450118101d5400811900d0400d0450760b0a81d001c1521031102885000200302440d43c91040300d8a29000308a0340b0b45c2825075040c40014040c414100030042d00540d801080480b0b014076031030082e00c44025200100003070040700c0300009401c6120701d11020001080f1780c0140907a00407110019401b414480100c010001c91102c04003400d49100742000e40703400d9403140c025a070a20100d00c02c540c0140f10345044581102c9484411018009505444100c41e4080d0701c10320840c1410020560070410074285800c40c9502964010b040c0c0028030300c02041d1040076404910724500070420b880182d0307404034500816183c607160a1015504241d015189203080000b4100ca2038001e104403c142c0303030000c04980c0446408003105208900c07102c4600d80040c0d080065002144403c520100518455a55169181c2c107222201c1c0d015072100311903d1180b0b192500c01c0241c0e80d668142c0700c5c9408005c1e0300f20041c903940d681104000702a10100c00032034804071410001c10030340c10360203407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 882131888 1250 882130638 882130649
    0xf050616020f1f1d070f031e0b04150b04050106080906130506061c140c131b08060105070b1f060e0d080f071208061c050a03050d0e03040b04 62
    0x71400c1010701d444503a502c2c0241119200040c2c400c1c04a0342009190303420001d13001410540c2c000c070075140040507601d080d020740d005203400901101b0034070401c01110400c5800354030b403043da100c603110952611018550050001001c82e01e00700b214107031049440d0040b0071601c5c4d0041c0208102e41e56008040e0290300c040300c105906016910000e000140c7e442d082c0102e550b0407800800c020f03907401042c0850740c5c078600e850000307490a4842800002d4440071020a00a064201400034041000103004528440b110510f50b85400e20071481c0304030100310a003240e021410301e8034a04076114100160340074401c402014002d01800020082a64a188011600a252b100c44c1c07200d015528001110344401184010307600c9419a80e60324040703590700020700160841328180614040c0c290390340540418100003200301041e01398081181c546001240800304c0481d0381d8030358080c842c0307950307609c0d45a684036080142840303c0482d1141011125520400781c07601940102c960340c9031256400c03041a04284503a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 882133138 1250 882131888 882131893
    0x3001050115051c02041508130f03140f220f1212110d02060417120c0901050426011b0e090405210909100807180f061403010c0f1b0f05061602 62
    0x42614280d04529402850303400c08a602c2c0d000002b0b50713007205d940707084000012981c403041c032a0106080d2088000c02c01c4000700807580111451086241d040450703079900c01e41c001e2a0260040014044441e02c03110400d5220700d841c001d00011107010b4555650204a04000348191544c420401e038000a4040c012401400d901142c25010307001403c40784111f4000504040000001c03a0315850070a004c0d2402c48014101281410703181c01824640a40d05a00b00881c0303000680108801c103002e110300002d00c002000000112648d0f0030014144d180340082041c02400030600140034484244040c074031103c641420150844002000040da50300b06070380b018030860105001c079503c6000c4002c810101c031081030280079440d10b001c03100450140050b003134012454640700401c0a0020b2482000301400010000d00b0003807009100341421507000b00150340a002425029003242a08841001500008124080f00c2c5410b0380c41c140d2512102054024038510500701404101c1c003403c052419403546035801c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 882134388 1250 882133138 882133141
    0x120b0324041106191202070b040f0b010b0403081c0605031006030c0e07020d110a02090705030f09011119020106050310140a0501060f0302183001050115051c02041508 73
    0x7000824032402d800841800601016942a9402094400000c1c00d170540018140346150302c428051041c102d03404c5410000208410042080c15162507015203031044055040c14210741d1004464410075440d42d0204400303840ca0b0020400340c3d00000003820340a0160b40300351190031490405807009000444d1300d8035603d0350200d09a100c4d171410350322410184d8010f151100c80c0c400f09440155110071a040c042c0980900e080150b1145500180100003a40e982603403441c3c414807402101c00003800034038881c0d0400016080e415a0314003920704000541170380112243c4800000d9004000daa408182c05000d4124142c0303060040f0f60101d010074240b041000c4940d61b8951050703040354001d010311401f040758940001d201511039400340c19015043c402c882c3c004210500000c804000c0814152000b01e484140704540164100300c3e00384440d5440020b022650400c00d901da0304402900e10101007290104403840074140040610031000001481150365540320b000301a022151003c207000410000390 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 882135638 1250 882134388 882134423
    0x2a0507020d1b0b030610050c0c090c12010e310213090b0c090f01050f03130c051206070306090b011e1e02070e01211103070510020f010b0a06120b032404 67
    0x1042300d0381903446070081c0c124481c2c160f00300701c0e1441000d071a420104c4402d01806500301c8029801c03501828443c13181400f2481c2051100300c4401404050780a41e981d09488070303200001003e10100c0c10350381200c42c00000748507852030000404941c14040c103200e8850045c8040160958010640e480c8152150b0b00000f0480c001900c061088008220034070364100300081e108610401303940084c500c54024101c010340e0b110006a84c51111b810014003540241051142d42d17605845514018920310205010b03001c00c020000c0c1400d5100038201460041130081901d0b15449032134000c0c1c42c10740c10340034514070310400d42009650b40b515000725200c6003c0903002244507002c103000d2050030f038003c140f01c2c88002d029a0b107001060405401c401c1c2c051044003c0419151781d10b5a6005c03200a5550003000e05241480c0b41c00e00b5254030000060180c030311400107120481c0e0013183c44070503070034155011443c0100c100200b480c24072074002250f04403003c0346a01105203103444020b070043d030043c03e01c640e0b008008c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 882136888 1250 882135638 882135647
    0x90c290a030e100c0e190506040501080a150602030309060901060f05061b0709020c060c04261c091805061f0207030b0405012a0507020d1b0b030610 65
    0x41409441004061281940941c0300e50044990708902a080e24a00c0142d0070512043d120451031680100d289040c0c884500d0a01251a01d44c0c44401c40755040300380d1030300b00800c4170351041340204ca04101c9007400142040d202c80c0c000c11246480500b15400242d6a80710003034803900f00b81c03291000340c090140450b0030350380c0500400c1c003500e42c4000d41d64465480c0200308040365004501b5000340302040d0b40c8804104005200701401007455040141e035455a20040380e0600348000c000081640c02032000340000641c0400c0003a0102c0402c8131a032000744030000440c5444080700a0441481c05210720503000d95202090404984e000c0e01c141890012000e6020107032141190802d400c00d656420f220700d212400c0c0740c00c0d8040c07100c5c0d00503100d00c19280d80b143c2c01038010489007911160345807050384c03504c0d04204e0035001d0350003003280b84000240ba4140004225204c0c1400203032080302c505411074144079045078800c0d0714500e0000708240ea550b9a0b4182e50160b08203c601504c115140d140710340845005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 882138138 1250 882136888 882136949
    0x2040e0a021207050c0f07090e0d0c08070b040c0b030408120604090f230f0c030c0108150f01051204060b01030e0d0c080307020109050708010501032d030e0112090c 72
    0x407004041d65540f021002c4031550000009194070340700d07400700302894a1050280b20041c0034925401300781d05001d011068504440c1d40500701c2000041c1e2400b00100f4450030584803c030b80c1c05440c110554450381401e840350b4000e0707005003800d040b00000340010840810010302c3d400300021011304895a89070b0403c030858180000180042410f8100000007456040d40c0d0440440703454010600d070008001c0340e0385442c0d64400d9031020369102c05010076092900b080750360b000300002d01c1c042c945c600c0d100341e00c0602c0a0201090901500a190b480074560b8015819158201c080ba04240300b0f42c9040c0c02e00d480a014080030050100e0b24049a8511000002c00c3c420000c00e100c3c0c648101d400d40315130780d400c101d0707200414000855580e00d0408000440601071000103061050022a5070b504508241004000c03120f201d40c1c0d40407403481014980709c0c50480b03040c50f6903050b09100741d4003121800180d41000c000d8100c101400d00d4040c090040060b104480b405680c84080c40c00b403810160001c401c200541d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 882139388 1250 882138138 882138157
    0x10b091f120204150e240f210f071a0f04210f08031e0705070b060a0b030f040b1006202107060501090e030403020d1110050d0c021219170a02040e0a02 66
    0xc7d10015098203041042040c0e07010200307200303902801d203210304400e82070851411126036590883c42041225180300c1071b541100c880740d0420545000da801e40c0400542c41184a00f241c0809112100d6003407601094080d000315400c0340321101e2414180ca007200407a84112080f00c1650010400e9403842c036011410342e0b100b4003458503031300d2a00c00541c88002c4135290062059603c2212100c0200302c1c0841c00c1c000e103024101551800f247d5003031518106c14400d0004000101002c0001d208005040c0c0c814a21443c0c620140c05a00320144c08405450030846103140703598509000030010034180740c60388000c2990034000c3d0b6003080f190362114030b6501500d4002442070003aa03c140700034005440d0900741112400d206c0c01070a0b1794049081c0118440341c10034021b007000301d400486c00301204201030149030801c500710b102801103c0d0001d40141058000c1c18204094424601b20a81032213018144104c0703030b080d06600401c0245081c500500296100c0e0060201070340340c41c40842c0070764203103000ba01c02655 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 882140638 1250 882139388 882139399
    0xd050a15051f140402130906270e0304050411090d03020313060e090a05060105040e1006080106020a03080f07020c0409060b04111c0902060f0c010b091f120204150e24 73
    0xf0601002c100280d00500381e038104800e40420005a010080e1150000512014000d2624110300420b1002e103025200c05450323000e030401341169007110f004400c440560714100e400060180e4911291f043c0c5000e0003501e141c020207681400024035400002520401580c07490300c908040c3c4801c411603407060009071894010005c28081007a1079802d400407507010006140060425a44e00000210580280d80c001402048440c01f0301610340d010403c0c902401450008010580312554000c0102c00010311800424585102080b0306a03c00d008800d10000001c04c2403245815505000000700720b0131002c03a2040f0300d05001450346030085810345642c1410b21074984403402040d6003d0000d0192510101d0f0300c40c204004000f850701c6224007912019144200000fa0310b10390b07400303110301e008001e00113450f5090200d40c291140651400032030199014108072910190151002c10082c10340400444040d0000010110341c2009240c401449000c42003140e10000340380340d01101244101c200c800790401c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 882141888 1250 882140638 882140669
    0x90708010e210a0c170c01050601080705070b0a110a030608010501050906100e0105091c021e0a0314160b181909090201111905010e010b0f0d050a15051f 67
    0x312290340141046074614144950444080e54440740170088440d01014070000104005d43c0c0c4803424401c07554060802c0c00c010026007000031024089003d4841d000f032070030b030340d00c000500020307000d401c00c2143c1c00c0d0140c86151918500d14000c0c004c0c0c00e850040880039840c103000080c00d45095556540204400f520318500039081400031a50061481000d0781480010005101d01d520791404004002207216040000b46090348100712035001d41e514401046000d100c124419a45d4490040c402c0340e0380b018642c81844402d9007030a00308840d884c400c500701c0304590000a0074007500c9009160011001040d12114203032441003058032020940152280b10110105000e4010756500171080c0600506000d0110100b20304468a06111a02d4207081aa41c00702d0240402ca02400b03140c07840e02c02e8100074440c641141002c41c9503a8000040710b03101d104011808818001c0c244243c0c1e541c00e80007140c81600c1000300c0301d804003620044c0c840d003030841400e2406403a4070350210074110545d01c85d01d0120091 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 882143138 1250 882141888 882141943
    0x30a0f1a0f01111603110f09060604180e0d080711070b040e27030d20180120010b0a0503061501110309062719030b0c070605090708010e 60
    0x210f411078640308507201c0c0c0354000400036440b0301c1020055200c2c00805201050382024404040c500c80d090354002c41d0741c0c1c01803140300d88d218801e982c2a66081081551584118000c0c000940300721480100d05c0c1c0a150403100c1c140394480b403050301c1100c20f601c450a07000c4c2c040a02c9642c1e5011481505120b842c00e100621a00c0d82c40070300f040e040020003074202d400c43c1d0380b038070086401c1c0621810200103610009420189540d280541c81c083d000b400c03110220940c140c11034492900c42d680031a1a44004882001c450307a020b141c2c7d028004403044000348035a220888818001c0105065031842070614150008480c500001d1082c40b6000501585454084c040c0065039507000b8256120714600082c81548001e031150406000402d00040c0300c80601e40081b05080105074100d45c80501503820307003410681e036000007181601165400b50352941c1507034604141004a01804400610361400d240a0000080b40000c00c141511484002003008040b24948541c0e503980c881e030368068152803844590324 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 882144388 1250 882143138 882143147
    0x4090804230d11090402010c14070e060a060e1504210201020105060d03020a2d0602130b0c2e020307031a04150605030406090b070210060b1219090503030a0f1a0f01 72
    0x2000791040c1040d95041088d80e890301105d00081c104400c1544c442d403c100809a02242c105070048016104100070908042c0000c01070301b03400c0d41040c050300602c882032224441c050201c0300100302202588603070100a403140b80e02607206e40e2090b8010740c01e04010034003a00e0a820045001c5038181c0041890313905650740d0381c02c07881e0310038030b503000d00032481020114414085410319015440740c03038016603501c0300d90040c020b8181d03250450210b01005018650320003c0010300d40444000040d5807080307045102940c0c007600d490124004031602d00100c180700c0400d4040d0058011010300a0042c141c415011051008540050984000d03810075403904101041c09a17008513001401040c010465507030355102e040401c2007e844110060f404402102103025061094801400d86600114030782410124203d2070f2140162040400103080039070101070907000d9102912542c1d00000341ca859103801d01e4806c0003441c0405001c86082d01344255404907202c00b21508408880081c0008000b4215600459 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 882145638 1250 882144388 882144391
    0x803032701110c01090501060b0405150c100c17071e030b15040e0115170c0d09020d11010914030d050304020102071205160e070f030b04090804230d1109 67
    0x352195038400c560480008a01d00400c88640c2640000ca001ca80519141d1300711406079002105641e8103200500c040d50307400700c40c499242c18103040ea0351140c14a4503014280b010b080c00c546500341c9003403a504480d941040021528911501140f81d8070350b142001500d1482841c541d0b031145c00c0443d010209074500940c405010300703038060b00c0743c1c0c403c91213211102150344c004d801204101661b040100010700f254442d82d03160345941e2901302d03501c00c144400049041c40243c0089010030707000c035003840311416690080d5259a00203048555131081d81c10711240e000c0c0702c02c084030700090b141280880d030900b129802c8140240c0c094010300d4040c1400104455035000600200c0c118019581c000542e0300305122090f4926028101501010002d000800b41d610042d50260f6298030720b00f820842d1b040c3d0001c01e124141c00c0c00c0d06022500c41e840c240041c0003482c41902c010300059000c20302113440c1c0f5140c1d5030740b01c003126400344054490054000700885404507100081055507903040c209520b0a0468003213 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 882146888 1250 882145638 882145711
    0x30c05040302040f1506020d08062229010509130c03090210050301150905371202030706030608030703030902040f0f020304200f040e101104030c080303 67
    0x45040c9922030b400201503651240c25110195140c54541070880501c0640034000c000d0380c001001c40c1010b086005d0961007005011a10030000150842e00108407070b20304101600e44a0420004000340aa007243c450900c0400100c074800341d03900b040c220b5405981240c00d940e5004150304458440c03806d901c000341503002007003c00c2580304c42c5081c4c01601c4a1003000c0e8003811941f94262a0341c1400401030a2094291a11007005180603003000191960410500b1510310341500c1c007001c8100b01204c1c450010f11070030240e00350160002c005610040454085141d9200700c0c1038401d000c0d901c010881c2030361868026140686c00c100103190004e4082e50101d00b0302c03440540081000c0c0e5803a010481201d41c40c5130704640700c1c0d40002c10842003110b0103a01407403101e05201e512000d24814004221a02c03d40840240100c0e521800c0c030085140402010a0b1114069014010405c03da01039001326006440212510103640c00f010800401c08070560384a61880c08e17582c514003c5420b0300c3c601324822034850 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 882148138 1250 882146888 882146897
    0x9070e06040228080c1c1a1e01020c0607080a050a1701090209120a15090f0b01080706140405030d30150f080c04021b0709050411060304030e01030c 65
    0x1044446030180444540d00b42044036502c080b41420405800114005c05003400c9510802100c5c0b04480c00304c580c0d28070780c1c414080c0002c501240380d20740b00d01d000b00c1d580d0050b4000e081030b0707240008540d0700d001000403910a17400d40c0c480385041d000f4013606010b0f461009181e101c0501c040340344940b1820181560241c02c0c50000d03100400c1c040000704407039080c1c1041200ca9000030f40040d640c10f201d00c4114181030039070300410350f9032101d881c2c0c080d80c0c61007a0714100d112600e5107081c00c140400c1540d0785150380d0b04101c582500c0d59440028a03a00d84843c410040420207031070070301000301502c3c42035a040301d501a0103048242900c80044031008107540350b00c2c00081c401044828040c40a08002440c0901240006981c03400d078600948100c202d40d014030000c4151080a2284010110b84450540000c0e89c000d61204c4e0f02d105500e011005113001784d10203114400001030504a02e4212034045c0c1d0060908461200002c0244000c40c8011078000d404122603441c0540b80394460303401a140203c182c0742 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 882149388 1250 882148138 882148147
    0xc130e0a060c0306091b09290309010606030509190206070c090c0216080c060d090c03140105060f1c030f02030c030f0904060801050103020139061a01050309070e060402 74
    0x851004945291031003000013503030760105210103c41403184240344440c02d9000c0c180e08801d002c0040809280e4040d11303005540d440031400f00c11840e01d2408100200f502c05507504c070310704142c100d070007081c0c01e1149800080c244000b0801c0c03c100441c4100d2038105008205151403095001c0c400168000780c8111071807142c14200181c1480d01c2e20a0000184003070340601002c3c9160302d00d01d0f120b40c0d10741c2c01102c05c5400140300c1000c2903403001c0481302e507540d200c4c1000c00e5810f040d042c0001682265400941454003248100c01d00c8401980840d01c0303650120b0301003d03089119001c1c805500d40b006204222588058890b85c0400d024040c00280c400785441101c0c5481d8001d1502d40c00e60308202045a041070011036441041e1400b4040d482c00f41107000001c104540c0f45400081c0f00004140c01038031110200b015540004076059a40005e040391043c00c10350401c03480c544540100300f2400080c0d9040c0f80e0b9940e01c0c005601c6902200d0158a041e030003090380e5414604041181000500100e90040d0b0820 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 882150638 1250 882149388 882149393
    0x80f0f0613020a210519050c0706110d050f0105060a0809072102030f0105100b071104020414040b0d03360e01081219120b040504060614030c130e0a 65
    0x41c91600c8003690350104d4001504c02030288800c41c14110f1044c20b00302410010007625140c10f10000030080da00124854469210f003400a02c00c40e03001400c141e040c84c0012010101e0300c0010710005840d603800300095903400c1006012014203004484d8461810050094031a01c1140340381c0d00001c001040d20101c0e507645509900015503800fa55030003102c0ca54910080d842d0521145031007840340c00090090b0b00e001c200c0380c0283c010781d002e1406841d070041b5001d4240050322038140909030010340f0855945490752100b40c81d40301410300c070901c41c0e420300c0b1606103641010f019000706e055154803032141c0e00135003021a04803840701c504d422601c030301c130200c2002c0c21440c84041d00c0d00030700184410107100d5040001c0c20b800d014590b044031030354460070004005000303505004a000044c3c07038034000340307a4128100b5400282090980307141d401414a4240020f21110f42e02840c2180d00c00310300085a102e948017450303205c00f9171a52150f403001c2c01c52417802e20680035030801d017580a980c60a87d101070710a507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 882151888 1250 882150638 882150641
    0x1506010e120606010e0612060d031202040f170d0c060b0f0418051612060225050c10090323011806050f010506070807030e0a0b0409050412080f0f0613 66
    0x628444402d5110009012495070401d085180075074040e101c003443c05600c0c0c0c0d2618441c000182403a405485040404001c0c18031841c4003481c507104840082d555aa66049061400780c518010030401d40408214060a0280052840e01c5d0804075200c0341d03c00310054075008000e220840030a604001c4011010764241d03680e118100b03035540c0801114105564605040b454810b2402d500b29103100301c0e00d018807110030b80310030b008202035103c400503076102d1f0910b58086590000310640e01054910b50011407c0180c04260300d40c0301842070359400076500d4240c40440d000091484090415100c944680c010411405101c64450a070034001144004902e004020382c01c1900300181d0320b10f0795400500049004100c201c3c1d0042108641403400d2032440c0c0c85a0800b81f04043d401018482400003083c111b4444000f504001d02504c41c03401c1e2680d80d02d4160002504c412102114891000601c030361280c0d0240719124013840e0000040081c590b07a550b5071202650000e04500d50080342c000d228032210045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 882153138 1250 882151888 882151909
    0x120c05040b3405071502071d1605090a06110f03030705030a060608012304061502030a0905030d0c080310050a2301032702010c0204050a020a140c1506010e 68
    0x15440681440540d03081d00311840740380603950702c07a082c162402650200c0c0c400245041501c0105644401107844040c040e403a0503a00d6010035117100e00c0140c40e089001c840201e80b0301c034800f801202d800039098170034100d9144c03066002c51580300308490802e01c001e61207400580101001071003124242282c1c6800e451850700f04503100700008100204002031100700b401000e00500c407074203040740103504010020011490307111401e40c80009102e03420059036156040403000742180044000b660300303140402900c2ea03205125941c0418200100090681000585014400400c0d60392070b41d0340c252907a07410469171024041d0022610104004100b556078510b50000030414903903603642c04000301451a01040c000f20b8107e05240c0760080105035240390305070200000581d8440d04400d00000d20050300c6e9072142a0010350028900410804e56007916801001880c6083d1559680049081802c0310648907469000700b0a0300602502e800760345c145202140c1100050402c90f02070404c0d40045103001c0031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 882154388 1250 882153138 882153157
    0x2405130905040c15020303010e130c1701200405040905120a03020a0f031a061e0706050a0b0d053d06031b0f1a070b090c090c0a120c05040b 61
    0x1941da0500c0100400c0080030401040c0c9914003408a005144c00030751030380814410006048a517800041144810081c0d080e8810b5222800c148096107945104c040010030014043c0345610303042560005071068421450405859030600c4d103801c0c10401440090405620219090322600c42c1e04000303880030101030b14100c885a85c1c0140c44440740c3d08028a9014014141401d16103000152414210040002d0f10320020550b010340e51108024041e0204181c58074001e0710825000c98003804001b81d9402060040000d0082440640b05240802680055500d80180503901800d5407003045114440188400807012000c5d03101e4080510007440f110031702641d1000c5950355100107004000095803841d0f150f0b140240d801014504105004800b662980079070725185e0003a083d54041c02c0c0580007128800740d8840a05001410902007442d96107a19030003040c8520781c0b90001a9280030054240c42a28403541e032807101d9101c09144a00083c1441c801e03c0042090070031003c503044000078000d08a41d81c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 882155638 1250 882154388 882154391
    0x30304020f040b03120a170c0a0f120612020301060b09031e0c060c0307060f201303020d050f070602060705070f1505010b09130212010e130c090c031524051309 70
    0x3146e010340140610410b001c85210721180c503050011041d04a015a01d48401c03500742503088a058081c00e81d149444160b030550018181035000c90408004050000d00078800d50007400301546525008000c0c0c0500600140c141d400f00190321600c20018030840701c1c20714440c00b5944404507100c0030600d1940a440e100030160300000340c0302c0030005240b05400c83c5c0707185e11804102800d20710041005100761601c403c9001480030444910106108552100455004100780721070505486c1c1140c4905403102c82101c140121180041c015001003003007403185d500e946d9501d240c12910340d641110a2003406090340d50340048881030706038103c58842d40d03018024039010180c807103908000f08081d00740e604840310b070014014007103944020000c01195041d10820109100301ea80c480405c1d21149000601c0a080400c100000044442c403070760244040d1140c0380c0d014000f822100048120346d00251060210003400d02010000f45400c87c6540e0003035000610b029454158140001c450312007903504140c0480e0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 882156888 1250 882155638 882155647
    0x804060f0c0806031e030316020f03160c15090302130f0c1805060408030315060705010f06090513051002030a1416080f010602030d32010e1503030304020f040b0312 72
    0x4c3c50100114043c14030405201d00d805c5020907400b940380c0c00003a001e064808090021044031500074001150f06050f149c1c21651103680e9124081400040d43c2029903c200c115400841e152004450800e9000c481d921002c008520315800d10034003401ea01d007000100d559403102140d4420b01070040803036080c115910420447c01d98500703603901c1c0ca060341c4040e2081404010412610002005a9a004500140e40d11183c40e4040c0403421502c0f920100920320f5207000e280c04000302d00342c1e001000341c2c0c2c20484100103561740c0c034001c031034a80003041001c4d0035170b480100c80d582201170343e40007543e102c14940d0f0041030101c04a03520510313480741070750a1400300c400100210042d551111004da0721184540305100b1f80d5240c03540181d1240700d03250700d1650365a1994842414080c4071140c50078000c190042c0781900c0e592092500c3d0b41800700380160303030b0100c2004000c1802103e550111442c20b000050145145442d20741c200002c202c5039021154109441c1e903140040750341d00780300720000c00c03080d0001142c2d40c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 882158138 1250 882156888 882156901
    0x908031003061a03430e01121505090309120601030210140304141606080a050109111c0902030a030f030506010507031704030c06060603060611030f0a0804060f0c08 72
    0x6503a20680c6000000d2581d0700810501e5600040c2216040103038500f6400302c5c1098000000f90001640c030404c4c0c40307030300d039501c420f82c1707503801642e850880c0c2a0801588182c1d0301c2d8141c43c1e00000d13417040b02826001504031b03040c989082c1c690000b60800220011a46003100804c042188001c2080d400007151300408010420f504000034907001e41c1d811803070204d00c00c4c0c043c114035a00d1800083c001510500307681000c070800c0c2c0300c04c210340c1080c1d0760240141e110459070741030000c0182208441c0c0c1c541c0e240c281400002c0035007a070700a1141c0c941c035250080e8144043c0500311960340505d240941c4910b03444084400150314103029040c1028001d036541c1d009045841d40250684801404980c10800308000d9840441d5002d4400c06d4041c0b02c0b803419140e191654241210041c40c02000030b405140340c484005a5580c00d03a20450440d0103a0b10b5041c95503014843c01d5443e070103900384e030030742d14182000200d00151058000030740c414440c840c000b40e82c090720500d4408813002000a180407541c0101888230 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 882159388 1250 882158138 882158141
    0x1701090c080607171e0a05090c120d110c040c050a02070e0114010f0302070c0f05180f0609040c0305010c020a11060705072c0c09180f04020d06090803100306 69
    0x7808400c00100440d0801030b030004c00054000c400f00e0f19484201c808a824956200ea0500c04601080c40c031107600d080c500092001014150741c84681ca02c10480d050710b040c03c02c5040b880082009502400c0c4030102c51000780d030340101d4082800028050344100004d990784601c0354891704201c0d50b80d03460310340d0300504010b8580316054214029000c0b054004002281458610444006080c60910318002603a00c0c10340103402103400003042850000d80c0403841b060800c5c0110103d65080f9024004810160900e0a111005407120364480900e20002040341c1403d401568000d4400c04284034400e40d251282821100303c60b14010058201d6100c200c02c1c00054110380f528924105c4041e1b03d00030040d035441da03036440d462044010b100460203c0b00b041c6200c4d07100081d0f054441d201c44c0545072030b10315064800b550200a04900c20340e0180c0064200041402000c0d1145044880f6600c8a0700c4640800941150b800c7c81110600e4036980c61400040340c01000d140185060060f49404a003149401070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 882160638 1250 882159388 882159413
    0x60204090c0815010f090929121b01091d01090506060406021f0b040c08270d11100e0309240a0507140d020a0b06040b09070513170109 59
    0x2002408820721164003104540c12250b0f40090801407441180c103407040d1141c0c0c209a104400c1a842d11410141000314111600001109501103030024142d81007000700128000140100c1980b0940c00c90448110a0085c007a181c10141000c101071983c49a40740f1111202c480100803026081004005064440c050305030000002c5500b00d050500700100255035802030010f028007495030100d091940d1046038001c5080000241052010100030780020b8040354060b1203100164000d200340c580b01a16580e030041e00c1403030020181c0902c115082d01200d004448408495a03030107a00b454800d142d1551141c04104c0c1042405140c480c180c0e4420441442d01c0f0021a00d20345409003009461080c941c0c04a5030400d0250403c540c5400b91400c0c80712340000142c079842c0d010311074036014144490f000101c0c0c09030103118454090f840c0e5542c000348000d50b159800d015030001895004204400d004d8030190400712480015154101ea507203004540303132448038a001807a80d42d50384910050103802d03110301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 882161888 1250 882160638 882160661
    0x1b0a02040c2703020904061505060d0b0f1203090909010e070306061e1512060905280e030d090503070209010b0c1b09060607050f0105040605151e10110a06020409 71
    0x3840b195107581c001c5030840800510007003c665a500304401e150518800791409050050400c58a03588075050001c01042d6803007800e071291902c03108080461a00e11a4840c80110410207035003807000500034809082005003030820079540352044281801c004106840080d8040c00001c41c1062500081c84070402044040001e8500b20b54401c0c0030394004d04003501201d501c01e02d00429108009480c0c200246095040340d06024146000d020440d4108200c00303044142605803800f42545643c0300000702d5100b1100355625800a002c24060351400d41d0184c410310b401002503924001031640029040d8500f42c000061110740070031100700d0100c3c10003c512491812501107083c0c04040c40c00194802d0f00105a81d20920780010f03040c0411030305100620803117151000034052801c00c1d00e02400504001c032140008040d0684c18900300b8607000804121121900c000703400c01030390150500803602c510307100da08140124605190070808081202842990051238011780762410400440c0c250368002c043c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 882163138 1250 882161888 882161957
    0x603061a010207060f050c0a140606010c0f03120b030d080103030e01050403242004050414040b070806040b0d0605040b0f060913060b0d05010b04050f010b1b0a02040c 73
    0x5142d0300080c08105852440c10080402c029059080341c0b584a40e0b100b110540c02841c007004100051800c65903841c84926007594003d41e25080110717090100d9420161034509174402d400c0120380600380c60b026407111038602042c11012100820300e050162403032000003640c25401042810ba00800b0307015000424a8024505451600e4001611100000b000c80d080740c40c22010343c1041da03076400300800380c0c604050105008200c82d5100c21541051180c00e003d68104460034140710341c1500400d100301e501403c24981034403503500403128000e0040800342c0040e512088a18030380d880c01c1014101da0b100d1311001c100351805290221054030003901c210002c04948040c031103550341d4041f10a90100001c01030310000700b018140344002e07000030340030103030000319026560381030200c1034105880c040000d507010f002c152107401d0800c4241c0e5013441000c610480c10321880c180f8009403504100c4028080b1b040316254174064000a0803607007014030b5940810350740e030010300c06d00c2074844540d11000c41c0e4000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 882164388 1250 882163138 882163181
    0xc0507060c050f070b180a051b04050103030807080901060807140f0406050105030711250302120f070909020f0a090207050f030304020105030402090a1d0f0f07080a24020706060306 79
    0xa12083c0e4040c00400419030400724000400803551a02d544040449142c111810f103592424a0340e03c3d089450148910a418202603c555003000c1c003440b130490380d02da556401c0395500d0318402c40d0510f00c050f2030070115548964001500c024100054009000d5030f82040c03c2440c110010814401a4503007071500890a10074100a00e0780c100c410b03654003103140d080850424182e4601c7c0e605106481044032514469445408030706807103542c102098910980d4080c40d1441000e0f60940d0300e40c40a0318840c826400b10b8410b004440f0507401c48668144040c00d00a4415061800500301c844280c1007560308550106294050090412800e603c070f0f0600340c050b5107182007680000300307184002030004c0d0090b030410f00413801000c17465005030b0040c244c00d04000c010341c02c88600c183d110b5101641a00340d03407091700030190300c45a000c01d01c0d5048581200050070305000903078844024181c03405030b1200388041c1100d4010018003600040000500c2040f00003006411407500700c0840304002030004080c5840c60 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 882165638 1250 882164388 882164407
    0x190b010f061403150a1a04152f10060e040302120c030d020f040b0a0804031e091e05060c0c030d09050906040b040b03010c1e170c0901120c0507060c05 66
    0x8003204e4100502d6508412481104800b05260051035402001c280017441100c4c5094801940940140c44115500384c680c1d0655000483e4903901030004000c5a412807010380240d84101844441ea0402d2401900e031803494045105040360440d500104071002c58004010800d5418060103080e60002814141881100720200e0f6032030092002d11003149074000342865035107003d502940e0041210440c3c19030703584011280140402d1080d0741c1280429108003920b40f8040c074005400c211680140d036088143d51a060152500c002a070013810403150341030202082c02e8445a004103101ca040c44014600e0f00645801d25151040100016080042c10101403001d0b5807007004158200a0031070b070100e001002400020020322601c040c1c10b40c5586170100c8132111a400445040b000320440008807034200d40784500751601e0010449004000d0130790301c00502900040d1019200380c6006261030201c0009840e4841e00b100c03001c0000c1c901290340410b008041103614080e542c00b030900c2d441c042c0e00700181030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 882166888 1250 882165638 882165677
    0x180506101d070305060402130603020909090705060a050f0c2409030f0306210304090b0406090c021507020c060d09120e03071203030b0a0e010608090c0f12190b010f06 73
    0x10303003030104142e2600040341c0303a5031b10b41d015035094100740e48a15004940d906000340c0258080081c150141e03020600041c6c400c9004100c803021584040c0245d40390a801c440211982d600401d0404900b40b428852045e500380e00700300926014011015511040800742007601002c00c0090219095500421800b41c580f200c00d405d0b6074001c0c0056540e041201302419203596101d4141c8981402440040ba0000e43e442c0207030030041151310152001c12039a0303112103900090f50362170407245001d40e00410420103001c03213103012664000440d205681c0034100c00000625241c1c00120651500c0f512412034400340160750020034038044d21410f04450341020000800c0d240c95181c81942c112001450b101802d16005c0e0308614413119000300380349a0981c841c52001c00e2041b013030081700c0002e1a0343c000244101e400080d03043d10702000a18000316a84420204040c07007000550203011406840c2e090140d90b403000b050001094401d42c2c0341030081d8141610342030080b050f1b40c000c901b08011800b0495408404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 882168138 1250 882166888 882166891
    0x3100605180703290a0b07020622030602030a15051207230a330c0206030606040306091a090a020d06020f0f0d0203040b010b0f0d05040501180506101d 66
    0x29078206580740d0303407040103400810750310f0441d118045030b4001d240424804900007010808040b07864101c0030791210400065401040c0c002900542e0810100507825103039201c1f0b05801801d8409013500c50f032641e9070003090742c00c151580c84100c1d448001d41e1703040390004641c074006028180d54601810121003076440d683c03802d521490340d401c080d22540c0c2c42e0303000c100741c40540300c407602030459240513564069251440781c254245a8540741180001004140c9004442d4601c0c07003191754030120f0a44d15001c00c02c41c0d910240940d0b0f44240100000030000c0d6a0f40035900e4018003d94001c0202850511082023501b001403012604e50407506040006a0721120401203054001c500180c4900c12440c0201c0c40c1c1c425100c0440448501151f451003c18a6030001d5100e0391040448101a0341e03106c0da8680c55000e411143c102045080c04142d003440810b1380260750040c0110000319041402640302907005040080a4840e0b80158040084019107464400e004182d4181450f00782c1d4001c92991001e02c60 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 882169388 1250 882168138 882168169
    0xb0a0e0111010b0a0e0406140118020919030b181f050603070308040f0305010c030612060e10020c0706091208071209030b0f06091005091b040315020903100605 70
    0x55401e9040300c80c040960140c000e040001d85038030380690325520100031400742120202c400e43d0400903126422240c4030403160403145a28400301d41c448004400b40040c0d00622070b000d40103094507602580c001034003000e01000710f001c1c007180c01907402c00c20741c850600000c000b01018180c1c4055034085007568581960900042211740005294858400003800d000a56201512845000c00c001c0b5468800c040040c0c100d0340f2820007080449072802086c2d054130704d44e20961041001309015000414000d0300300312449207158044c0c075a2103401103c3c00d022a00b0400ea4401c0c0c0b40d102003014441c0d02d811080080103040305401000646c051a1f9a461852051000c0104000c0040c002c031104c5170701803000030010b542e202c0320701420f40c0f0b8880d0100d4070500044451a129448020100317450b8458401d5140540d500604401c01c00d036145024146048240035459031300d220200320000104440c800618204600d80001580c0c82d407800c820586070801521302c000e1100d10708401041a9501c65055852017403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 882170638 1250 882169388 882169397
    0xa092f011b06091a010e010506070237170303010b04152001090c063608011806050709080a15020d020d0e07230609120a03080a060b0a0e01 61
    0x140341c18071001d045030010042c541ca08214141041005a41c24944036a070100e1800c506aa6940c82c801d110350b070284295030f0451420003d010141c10100100d00110f960442c240020303540e00e400200c2c0240002440001d11800003405104c0e00b064221007091015102008505650500c000300d9064030452181d8134003d0508039110303e0460040b107801703820111032015540402003150285000c1d08030400201d47d4140707441c3c004a8654041c4803684441d005600010030700981c41181c440c420701c15a0060312000450600020b00704c0000d0003204600d409041181c051514903140c0841600e601400030410711100400c02d1041c07500028041c07036034a800215111904440280c0c0000070311800b41a0100c036400021484610301c50754100301d48240c10702d012500b0050303961f01d445801800351402d841e84514807050390482c07403138034034068102c0e4f0f0001490740c0f589105006080f850009110b108030701107001c0d1003c2101c3d8075003d00c2490003c281609445d890244011801055194211002410702 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 882171888 1250 882170638 882170657
    0x6120b09370507030803010306060914090c010c06060b0408010906050a021c02090a050405010b1b0609030406030911121c020d0f0c111c06050c070308011a0c060a092f01 74
    0x1c40200f000200454209174040d1740c2c0c0d41c4070308081e40500400d008100182c0d0520302c144414070301c4804030030f100710240341c0506420b40f0b02c00011104034446400076180d41c2d84072040418244107007c0100000e10140c1c0c000600c4d04018174101041c0e0341c008280e008840c1c41403000c41000141343e4a040304907000c2d590b006aa940700440000c10280550304416042458034001055078540301c00103000780c2e00518940f07080ca500c1c200006565402c102c0d403120041c0c00a100c2000560301035084000b0b41c600c100b80020a9038403d00116000c1c441001040844c1d81c40308aa8070b40949824004101600d01c1e80b003d041d402d01500e1028054010fa500220100180001000c1c1407120440012084020003400c0e00c03c1d6000612111b2820941580c3c140d6440c2d10301030124a002c0010070844804a0385a00c7d803240030303881c0203003440c03881c2c40c2c275102410003090410941481520503c40d1030321400b000840003d611b82c0ca4101030011141020325424256062460f5891491801000083c442800d10308450034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 882173138 1250 882171888 882171893
    0x807030e060406020706050907061407080405040e030a090e070c12022a0103150503150c071e030e01020318091f031217010f0e0a06120b0937 62
    0x344102600a2000d0080e50140820030481d5001490800c2c0207620034040e50301c1e4080c50b240c481c0c04511800010448240501d01c541c0d0201c0003500010740141040303800d060351032010070280c0705008007400783ca0300002800880950400e00e02070141c401c04c0d031101614940307200302818050900304064030240b0100b4100b08414400c018107244010a260382522003010f0000c03039006000e07031018043c0424107000d9405942c0c0c043d201e800f4100c400040042c100b0b05480c4400314100100501180400030042144038007288040b00441f20603451302d41281c130f1100881c00c0080500312946409070464204100002c80e110b00c001d01c0e0420014104d69176542c0b6100c0d9011030301822001c01c03e00494240c81b10000050005c40160301020782c9a03501c5070ba594031400c00ca8020038442c2402070440c41e807407641c0140520007501d5001980310500050000301151241704208000c640248125049484081040042e201c14015410021481c4602214600e0119500380b018001010f004403102e081c10703142000e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 882174388 1250 882173138 882173141
    0x903071113110c0a061802060d0f020403170a0e04090b04060506062a0d020c06070305090a0e01080c0117151302041a040f060203030c120910050a1a0f010906080703 72
    0x103aa0103285025a500c00c1d42a00c0e030b54685070805810381c1c11754600568850403003042040c0921065009008a2420918058050017040c0c0402540e4115509200c0400003a010100030004140034500075500d0300700340c1800606800c0840c8c40c0038001c0e4140b810100c00a41c140300826001603000301c012039141d42c4d03540130071410300405041412945c800f10909810880030300446001002010a0755540175046a06a031303100b268803040da4000c6010405000440d1042c0054205140010500c25140d55070309121408880203800c120b81c0c54200c800c99044c2c80d0b8100101c170118001d901c416665520f403007641c100741c108150307000c64014800c00390141c8880700c1660459020b0440e8460402c061101494840c4075600180189010629048030100312603000000356071159003403180ea01d1800341140c0c2420300c07644029000c60384a10904c0380c041c0c0b240d1503a0240310f202d503901c640002004280b00130010030100d4400301d0540a00c40c01e42c1e141c042a60b0000c2d03417406036002c9040881d039580f00c1d01002c50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 882175638 1250 882174388 882174401
    0x6090a0f111302270603040b0f070c020a0e060301141510021e0618030408030409111b0c15090a060c0807050a0c0302090f070c061112040c0504050903071113 69
    0x40c0c468030000e442c000c0500307110344101e40030710590081440e1300c0460003170080c28442564082d180c0c101c0e5400040560424490340e90f8004420300d03101046101c5580410350513151034018001000343c2c1c60401c82542024451000b03416203800c1c10722068140301d000747c684c0b03811069119002e0082c940c4078a030100c0c001c1140a5251200201466000940b03a200e29141e22042d6400c85020030468200c1c111028000240ca0561f001d01c40918502403030001c1701030050120301d0103400c1d0002d0900207100100650b021010f51b501e500d5010301100a0010104400150948100c100248040c030001095407102130002040d1041c0f4140044030841c41d05242115000b5484020601d200ea41c0104082100c000800b1017200e1003070710310700b60f01c0d01e41030b00b043e080080403180e1400281c0510400408071b006a009003818400c1504624a440e06884010307045060403101543d6001c424401003006081901c1075a9210a120010354108201e0799a08456107075008181c512400d0013100c00c194082c601c1d03100b072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 882176888 1250 882175638 882175669
    0xe0118053706020c06130e06011e020c040f140c07020402070f150b010305151504170105010513020a09030b1f03110301050907080304091d031b06090a0f11 68
    0x204401c0c40c580001094980c0d41c003940c40140550070758521113081240036603801c81e0455074400031960402941603c04500100904d041020038058941c800340095240340803001c2d280d010380805c0303141000348400e550500a004d40c1c040d141607003080c00d120916400e1604031440401099550031140002000f9000f400809051140c00c2c01e850b508009003811a1114810b40e03641c107002d00048400194100d407005c0700c1108540807050036540300e0f8138000c1104a11081c05e852600d00707041c0c5406000c450710b468480995400e079941d030010301c400d103003003d840f205044d1660402d600d13110b0718001c001d0650103140301c01041c590303601021071843c21034003005810141c0c2403042d0100455490030b21004035028240f15a02a502c0c01c40810284000442da02040e01d2199004515040c41d0060610082c41405515960f03040744964002c40c3d2041030004010b808032021000d5580024108003604003403015144240c10340c401031302d62000940e40c00e450700c0c440380c03c040f91681c00101c0e40041140001402c554 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 882178138 1250 882176888 882176959
    0x12040803030f0a11030114010c08041e0e0423070902030c030a0f060e06010507031b03050705120c07180219030509010c0503091509070b03010e04030e011805 69
    0x20855950010185114440552115005498a00098040324000f40407100030340000c0006001d5052045810341d407894040c5015202c05120f40c64842441c0c000360403c074042c48002000c02c0034102d078180114050f12105405a0b41c3d41429500d1068840640c0d07200403650410307091020b1180d80c240030000003000c0384481950b8a1800070681820b6030310854010182e20b181c40c1c0d2001c0f0404591083d03200342c0300c03240401d0083e9200c22005442030b4110704001c40030046262040c6401d03481520140a400344a84c1f1140e071034030300d20719085040c460943c00003525280c091060801050300024450700315174074071402c1c01c1a103034426031b194041d11a500821004101c14000c0d03001c15541a030000e846081d88100070403403004032590442d100d10082d64804110740c0300c0540c000000400c0204560404900000c0300d22040d41c1d5280301002d41c200342e21003010700708144200010306801000f500b40403042480c00c0807040070710000d6440410b100c2d0060902402c60f580c282d40c1c008601122858403d100305a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 882179388 1250 882178138 882178147
    0x8070306050f150d03080c0715090b0610080133020f0111092d1c02030606100c0609080c03040308090a0b091309050c04050903030403080906010501170912 68
    0x10240c0203030400755807209107008000002420192003041c803404008000b4950200e41c2800d40703086540c6030010b840715688100403c07c0400060105140880510f007144000c94620043d0514000300b5000812a80c010391303150b0b400203081c1e5400205c1c6415514241d0403102003c1c82423210200000c482542c0e00315104079400501c09035900015030183c1100010004c3c06201002800007819001d1903595540041003801d92035401406d81508078480c000e054034110540c0b40d043d000881c805940076036486210702d42d403400c105505050040076440003090f200154140020352001f001581e135400c016007800d941d51030071410000c2c820101e0b00700780c2c814001c0781d0b115502d0781050050355020b564081d1051303a008030000f50303407419101522400300005010300c485004d528114001342c00c02c150100d8460003000d000d503100f0b80d82c601c80e16000e441c240d0f000399282d103094035000d0405c43c0c02401d10041540000010003540ea070001007409034200034072242d825500e90000076860814030001c036451b05c81c0c0c0850b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 882180638 1250 882179388 882179393
    0x4050606040e0924040c0b040f09021b06070f08060303090a3c0e090105060a150903020303070f060f0608030a030c0903021c05060c031012110a09050a0b030c0f010315080703 76
    0x400c1385028501800580500507034403070b21517040c2d104a11515a540f5806201000724049d294058103c12103040c105803440d451500500f81081e00c00c44460022400000c8c1c40466164882c8185da80032074142c00462503d40f01c40001441d050319403146d103191414001c511880b000c41102d140e1003188001c0740103023002d10b2050f182d409215a9002d000f09110102c2d000440d846c2050080c00e000380c00150503081c18034142000c55400608903428071003402412280040180c0b0100b000300f6141d1300440382c0c01400166482e210041d1081d1040c030303440345801c0180500500002008a0743c80d29518140050087c1038148243c42c0c0040075480030b5407009034030000d10301c5011008141c40c2214484c5080d01c2c5a03585d0b606240c00140400d5403404003c10304920240300c0490b00032060a0040d00031803180b60750582c2c90340081c220b03500d280c001e07000b01a125414807400d041c05000c0c0c180740c0b07130088028005440d120b40c0403a007000c2e24281d9071810151504d0441409620803e018805800590240c4200a03100d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 882181888 1250 882180638 882180703
    0xf18060c04050126040f0302071815080313260601080105091c0c0b071b060603110a30021201020a1d0108070807050c030705010b03010b04050606040e09 67
    0x1480b0b82c5011810980d64800100303c4d41e4403680b0091412840e10480392520b440d195446224220101c041d072041c0b10010031680074a00000740c560b40041d501151b111010f84000d50b002005da4046c00155200b48245400010001400d034181d411188420400c0c2c00000c0c1c1e41905140d80b0300000005000382000800c2103801900701510802c22401165904e00c041c2e42412512802c81c01440d0011340421072220000b4900303040c040d00301000c0e16104c0440c0190025140c02a8070020044648647d590300030070821a519176201c1e04010101d03200c8900c20b00d02030881541210a0200e010540004800700c0d41619034461504180360b00078100341109988121218002c1d40514400400300702ca83d4000c04030113030b50003d40010100107940b816480e0311011001d54502c0c1d4058210030034800103000420f15144100040c081640c015000400c11501c400241401c44942c0700c2c1040c05141820100031701500d03200d0484040f40c0b107402541c10190f895000d5141414047d5900d01d0000c48108419180c031b80e0740 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 882183138 1250 882181888 882181897
    0x813080405041514060c030301060810150203031035070f060503040506220807061427010605010c030c03020114040f120201051504110f030a1509060e0f18060c 70
    0x2021144c00d80449442000098018044862000c0d8410001030103858456080725410a00035090700103170640ba40c603600c01855021942000503400882000000c50b0f00822880040c20b0b1178a00c2c0700d04880622142100c1c06010381208285400d001001803103042c1017000c10000c02c04180c2c0c0d02005a200c05000f40075030b10946003658144180300114050000d08105200c0000f024028140350001c03680d40da0700d00d13810480d001d95003180d55000da40502d01015070854030030540020907071686604650f2000a81c0c10b09a68504182e1600900703200740e9030499000e1f508942c041c105424103013107a1130106d02500050024250bd9021501400200000204101c3c203844c4108000d03016052010012400c0320800c484852804100b2000c00b00142802e500c882904d210004c01035142c02c04030140800c00350f0054a203200040d94a069600e203103074030100ca03403014107641081031052a1815000500e40c10f00640507890703244011002c60505441d691040d061010b00d20150354040c40c103101c9203142c9812 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 882184388 1250 882183138 882183149
    0x8040608011a0f090d0501090f080c0f0601470a0905030c0a260604120e090103080d15080d030c02071205030301030f030c0b0a0b130c08130804050415 66
    0x41101c0c0304504420030340252021881c00203c01400e150190040100120300035406458030b546c0c0b0522203020031107004820107864003600b80079a5800341e10380541e04d451602c5215480b140c110100600842c0380d060a0144404688010100c0c054440000c2c00346405440e81d0800030200d0011820f4a805844805809001c140d91600074040d43e80e1018584c41c0d02d004002168070000316001804078a44616084011501d50b071448085000342e81c00980c07912805440540307001d200401d8607a041079005406c0e03580850169003007a0154956612aa0b0714054109500c0b241601c4003405a070456504020b04002d0009a0850b540c1001500c0c003e0000d240c02c0b025800140104070020400505441c052554030b58004015483e40c0e10f50380b0380554001050078101c003040074000001c0e001c17030178200c4040d010310401d0301c001a07010110401c21000307100240109100b5414000307102c48041d00a402150710000e040c4542400d80c0b101e1038100c41034410b83e0001a0301500e0009041494980c1c00084415182c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 882185638 1250 882184388 882184409
    0x9050a06080604200316050409140415021c050618010e1515090d052517120304020f0a1505040501031a030c21010507031e0b0901120f0804060801 64
    0x2010003e0190390740c003603140c084c1c0c0581c410008980060a907403034a64070101c00345021402c0980301d10840007078810010004a140448405000c188220281c110400034010340c01149440c41c2049010600c81c45490364040c410360321400039070262030348080c4003d0b90880c10b10306d03025980c48210324946450b0030380d1815840351800000c070790700781071084043c280d55181c800c40302e050941400070022080c100440407101c0e40691703a54034601d00d086c0811441400c101031003500b0002c0c100ac18200703220507408444e04880d4440d01c441d01543c4500d10807a41c100c0e40682c4d4091103020103401041e4001100d40c01083c550105810411610f0350007405030054850903a01440341d40580010380c1c2d03044180c0715020ba45604013a44000c0b1030b01c1c3c070000c00f0b400003080708081c44001c003d403580a0700b114411181d44010988401000348001d8132a010702c060003000e250300300841222440480d0102c001409440f80c01c0741d02c1e21501c0c040c050080d440a20540e4058003031340d91079480e441e00506102080c0b10340701050707 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 882186888 1250 882185638 882185651
    0x7050c0d031709070e0615120c1b0d050f090d0b040c2615060d080d0f0612050c01050c010b031e120304050c010507060906020d0b0a09060e0c070309050a06080604 71
    0x2000459010100da00c0005c43e1005900d802041001120100d1020b46018408210590380ca00d030380518944110100211036403118038840340020018108094a0042c1d0810074080080941000036101c1000da90148251031310300210210321642c0c003e00d00941011640c00c208410800c8264501d0180c1d0781c0500b1941508604403004c9402548401599002e500456245030020500c403e0040c0c4c8000300501c0405616026100c4521a510001c8030150258490818030355000c094003c0d840200141055a04421440d0321410703121601150510b042110004608180300000d4000c00640040101924112210420126443c26240200688a01501820705810303481346040da0b100e950058040e0010807080700045915900c044000c80b06242c0d16060031021441c180302601113081c40341000900f41e4040300800c600354076980d0080120030b0902e1401d10002c1610b01a84c0d4010b150703c2400b544440b41460251a40c1030142c000e280c1008031200e0005115503c03011150141c403060318204040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 882188138 1250 882186888 882186901
    0x341806051003271a01060f0201110a0516050c061314040510140a1805090c060c0d120e0307051f0510030305030402030106170106050a0902130b07050c0d0317 69
    0x35103810344003a41200392030030b8440e481400c4400d10f0482442c400c3c3d00c1c40101c0b00e203501c48440d00703031002e800c50300005403100c07211513106da02403154080d8540c2e04000c0f51f0800c0e070b04200c01407040c800e80d66044214205c074021a810090b00304102545601e00518150301c4151340001c22106620622448101e140244007100383c500b4184038a9000d00d040c0801600d10a0030702c004046a4012950000d4100824980015000340035081e5803000c812440c50200751030030009146458040641d03e181e10400c020071008003040d80018a0780014103550034001d04006201c45030600501c145c1600c00011700000a10f02c04020020802264510800d80200c801400710110003046880445260fa4074820010702031002c00c1c001d4010319031140c0700800210301e06440700091403003818121035035003240e91103100c00d1101e0701e4928026806006200c8003107081090309051204881403a118a900d00700d800a441c0003840428006a0003440700540103044802d207511f401043c4261144003046203403035030030201c2c3c60b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 882189388 1250 882188138 882188141
    0x60b091302160b0c191e090803031b0c01060b03071b0b06151b01060f0602031c180501020c0d080114010f0e0111120417341806051003 59
    0x10049120140c0d807207000350541c1c81100e044406007040000450901001c80c5403a50344452180b1704c440ea564043c000a46500f40c0061b00c0354050410040c003c00401c1404016000402c0d03951003c0c410804080b003c00c0c07190390b60001d1003a034007204115420100c0c0841c4400000d002540546c10031340c0e65074400d0840c1a0324218103003a40c640204400b003040f002c103020f071038400d000c03500200340e101c05185800b1100707010792070380115400020680d944070101080061080c420500080490340059490030010348122010303941c0e407a2415040c05d0396140c04003031901c6503154078104070b48c0c0035000310360350003461100d99507d0307100300ca0000014071014000305001900c214441c46041c81a1101e0702c0c2d0b07049042d000d581c03101c0201461030400001440140c0154000c0110115800d40c1c0700c01665140d050125181c2e40003030b110103042c69a400000c5c141b1020403468a80c0d02c04103000010fa810f205000e088040594000780c2c01681c2c2c0030300b42e80184410300e07920703031101d4110f40085070b040702420303e070010950 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 882190638 1250 882189388 882189397
    0x80403120915050703300603030f050703201c080a0b0a0b0306091b040603050f06010e031209031507030f0c030c02031803010b040e16120f020d060b04060b091302 71
    0x2e001403000c0c002c1500190040705290103006d04071244060b140499415000f661050b158070142c0142c076280d08009050b009a01219042e80901e0a070740b502d480ea84000d45112229850380c00580000702c21260b1003c818009014400100f141d204e03223680f25000000d00040f07017507810710091850202d01c0442c6140c08501401200e03143e0703445501b10f9544108010320640010f2034075102c10b840e003000c02e070782d010008003c00c00ba041719100003880b4202002e4610501c24000c0401741800010341c0700059564000418281071501415207940c3c610b00f510210f82021021006100d4a20200e010b01640d103405401103c0d030039211003020001074461420031410703940001d06420241e0002c104605140e42c0004003054040400360001c82d4440480b40401e045034406003000202e40c01007040701c042248071841d8040105440400107010f5082600c6500901d0042070b0000e22030400d043e0403004001c841d4101300f200c00401002007104a41d102a81215035104406d0340307104410620f11542c6d002064420f40703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 882191888 1250 882190638 882190679
    0xe04060b21070b13210204020c0a0c1a04180b06190e030619021303021509150c0706031a0d0506010531020913180213090f02100c0804031209 62
    0x31400b06151502e005c00c03031542407054031400c002c01040640580c41d00d000800b4041c0241c80100702c40001070410b401100707820b40141e9001c1a00c00d06038030301101c01400341d406842010415071030b24490070b40303030b18028220403241c03503001480400c0401200100600c3c803004a0890340700c0b4071124a815040544134802121661603a13420320010702124440c40e1b000d0045528500002c0c411b1585a0700040c8101c0b008410040e403580c00020790300c001381820b222807130404424000c01424100c41420f915110fa80b940200810180d440300703202c4100d0065040200895005001c10350701040300e00b4880c0c0c03030340c80c240a80c9019150000f074050800390080025202e845e45503200764408141d408000000e0340c811501c081e800501c4c45642000c01440f4031541c18003152501c03149040c80551b2045c008044090650703210b03968900403000011600e42c4581ca442c003030b811100c4124401c00c42d00c06451403056140040c0c0704100116000c01046000010310700c21090303a841d41402d0039035590f80000038206a0008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 882193138 1250 882191888 882191917
    0xd0f0b041425020a0602040b0a0f1103160c0e04030c02191419150e04060b030609040320150f0a05060607060f020405060c010c030b0f0a0e04060b21070b 67
    0xc8403521880e1150b100e103901018819140348000a4650206980040d00b016011050000365610074580042c00c01350444441c0c14100c10004051038180e440e40a030181035581010703a071111204000581143d10007501d400c4018444604190500903c03840c400300d4124010b14803003804003000c42e15804400102e8038295030458200440c0f9062061404043e510003610a024130303404505a0108401c2d104902c40654a03d002c0c2c0b0240410003096803190340c45584552400c005104480d214106807550251f0981046014a00711110a103403044d0028044440c9000e401440b0403600000420a070003855201d0614003261118100075045410a0b180242d125074100400e00c0000c0b4981c0200364504c002010040c24156120040780080d4440101401580d40d180200818a50588581e6009040955080844c004c0e07034000308407141001d00036154010200d8001401700728481d00205810200a80800104c1c10004071a52a0b18240010204540070704903011881d14107a50607904002d040600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 882194244 1106 882193138 882193171
    0x70b040312090c0501050c0c13060501081e04150b0a0e0a0c090e0a0e07031209150c050606060703021e0601090b1c1202030d0f0b0414 59
    0x403007501c0c8626000489011401c00d1400c001a01c400f0b00b00305903038102c081c0440b860101c2c0c098a942e4410040b08a04800456640143c001c90701c080c0c036000b80607103401e0803000348221103001d024681568500024007103445a008901510346224001449801000104805005c113401c58805207c408040c4030302000300317200703003504540c02d03203031040700c0f01c1c02d001e0781d4204038001500c3c401c92207850307483c44854100140040030065500c04c0b11040714001d6810042e150207164171540c12410011a1000c6405001d01c1c581d0301e0b00350b80100503000e60780d00c1d0001c00c0310941001c06d098003188034500c086850f043c81c81c0c8041380c00f402d4540007000e2541c03514130506e040d121900200703030041d00b40c0c0d00004011441d00445c80c16071070340180307807000b503407000300d000c03407960240154941c141170806240008078442c0e98446043c080d0151400c0c00300100710019110f189000b80d40300e0011025920 = true := by decide +kernel

theorem cover : BRFrame.Cov 882014388 882194244 := by
  have h0 := BRFrame.cov_init 882014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 882014388 ≤ n) (h2 : n < 882194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
