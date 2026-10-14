-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3142
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:47:00.243742+00:00
-- url     : https://prove2.me/submissions/e33e3576-b118-4a11-8e35-ca09d1728118

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 564928057 ≤ n < 565107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 564929307 1250 564928057 564928081
    0x2315030f070c02060d231012030212030f06030601150e0108060609090703050a151409071107060302030109050a0c0f0509010c06020c0a1101020a03120203040804090903030c0201051e 80
    0x2880c034207144034625841d0f800200e464101c21098060942e40c0c1c844c1c40304038a842940d42d405810901c44100407403c181d103d1034180f4050380100c0f0f40403100300d1104070405200f00806050004a8038105859003072404905036034074002d540051081c8108400401d1461740b0304841021307880c85c0d131502c1002540000040d0741d00c1c0c03030040091f40d12074400d102e43d158944840da0041c0c4240c80e5981c0002d1146030061480c01155109588182c1420700000280081401080b000c1d01c6404202c810048650f0745810031182c4680940e80e80804e4052100c0c00109035400d07801a505841c0445018851031341d846440c2e8040350084020b10380000c0e0554154a5114040d02c000c100004041c50462a8030015450380c01c281d078484000054268086c01208080c014081030f41c1000c140e0920140a680800361002041e884100042c808815070002c04201040000c0d01101c0080030301e200d040c41390130014200a030003051212411070141d400c041c001206c4001900225490301c0c11007805404d107840e560401d4007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 564930557 1250 564929307 564929311
    0x15120a050c04051008220201410705060604090503030a1e1418011e0f0209040501060807090e1003060e0c030115030303110f0901030905162315030f 65
    0xc64580704200105443d103842000403036001c1c864035030300300c82d04202c04c030181c40300c0c292a51410640d00b01402180142c2c2e0108142c4a20400c481581400408038007402c1c608411609a9045140f0301d640a5070700343c409100034110490045003558119544d6800380816120540001003140d001000052104840c039400300600112300c5440030415001c21402c10304440800752090074149580042109440000e83d942860001e554002d03c0302c80d04880850360905032109810b904203480300441400c0940c00d6050b105a224014002d0065594842025100010660b03140001498080b404269030300500700300c0d0b010f10314480030795110501d5034852030000c1100c0341c0e401c60540540d881e840d960360b50174055481ca90b0350048910b0407480c510301c3c01804031040f00c1007d100e181b000303001007c640024101034030402c04003801c021920054030720f0282c3c21b16000344404110400c00450104045010000301005604038000d050f0440c2c00e80710401003008203646590384494810000038100c6804d016140d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 564931807 1250 564930557 564930571
    0xa0819171e180909150604150509040f0b0c0405010f090803040b0d060902190215090718020c060a0e01060e06090c0c100507050d1a010c03051b03041415120a05 70
    0x214540409400682102c006450140706a0312845d01da80b1089460020241c2041044038204502544190a0300c034080e1036200352071060340048006414070582004000c4174603400140304100e45041044200c079030b0002c0c010725002a03c3e00c003140488a026001c8030065074585002142018035002c03030800283c1c0002101000140c48110000742802c06002600c468481074400c800408030031a40286420b6800050100c02c03003c05040c00403100300880c0e40c0d01034480b2040c8003502203900b404040e01134131070040d030702550348250740801c502401558092405030003e84000c5c818203668201644001c40240e6000b80d02c042c50001245002c050f000007401e04111480c1915401020100d07160200c3c2c1e0119884d6004c80d50018000f03001c680e4500c10700e21503045030000400b035950404002083c2c40e040341e00060500200003a9081c0b002028401404510b28440480340c0d01c58031000d0007000800c5640ac61401001c108008101c51503004055401401e800b511036451503640100070009854003070218 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 564933057 1250 564931807 564931837
    0x917061902041e0608061f0f03090b0a150b0f041202010912030314160e1009052715010c1502070609031d060f07020402090a0819171e 59
    0x1071015011205a100110003905005110300c0e04c0000b41081c0002403110307108000d1041c043c14840c80010308905103a40d1843c2507508064280f5040d07005000c84035029115480810800034552265082040040300c44103440c400c4665030f80844049018020020304501030510040c818260720403a4900281c4c0149007404040c1c0d61055410b9003403584050035400030b03845050350002d42030441c1144e90042c52050400c049913081510061440d178038659074a02c02e09a06c000494101d01c5900842c001d0f09005000841e590140389440b500c0900418008002d28024400145e000e02d01c500c1c01140f07460b041c1c480c00000fa603507a4409003030b448038440448500c0e41c00d01401000c1542886400d82ca548070380c1300c2e40306d43c914101180182021504405118070070400031090100341d85416200b6060341a100940c0321105100002d02404143d081001c0d03d200310305110900f81c14103444c20203d035009104c03110240009524a200c10301c5500300b8540c0505100c00351f0940c06100e04010f01d40d500e088851 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 564934307 1250 564933057 564933059
    0x7030209040c121b0b0a0503010e071709010e0c030105061804050102040906060801060215070228060207080702100c030c141501081c031401150507080304030906091706190204 77
    0x300f006540e9400e4400c0c2c03070f00380c031300f10396a4804228400e1460150a61019039400c224141200400d00d1005004424410542b4408100014080c0075681d2b44913140c111503503135510300b0206885c000d00d584826445d80b0320500034141c95505040c8115401280d002e08107540a01c46c8a150380e6007840058011100c41d9420000010050098440d0a014212555038021a545820f03c001e14202c141d07003440c5640031140c420321200b25000aa00200400a4641001200d5074580000780c0642c3c5008081c1496000050703d01c204103902c0018100b9a108035801134604004100444460009007001004580c0c4028810b021481082912070721a64070000c6528010f00f801003095068004c1c0d110782c4040d0310245580005100448801c841010720f85000c1003c42d05c407101e804142034061044540c818034903419001c80d1403080d0300710b5941c0d6402c2224243e0307138241858014030720401403255600003100e16801060002c00c40500ca075000b03e42e10000c24464541410118032820f110940005aa42c2000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 564935557 1250 564934307 564934319
    0xe0f0a0509160f051203030f01090b030304030c0b030708180601140f0d0f12020c130e03041d010302180c030610020f0d090f06051303110409081909080c010207030209040c 75
    0x545500901000a41040c43c6840d140910000d03040042004107190820310420202d4071442402c541103481c05c840100c0c050305000e0200341984110380011380141603244001c689241d001d00118007034002aa0b401c2c1e0030340d5444600780221100c1da9121250780c0c1000300100134005600d2812a00100c0050080005070201800510078010140d011150260300c10101014000021502040185140043c1421241d508000f42ca01170b038043d100002c0603035414040d0206901041a00c015085000c251017035400303605102038800380c09102c201d00c01c0e103608001507006003500c841d16001d03407086080ca81c110303100d10080182440b011401c0c9800c43c0f2071001c100c0c140341020072080c4081c0341e264641e1646681005d41d90100c1030b615410060a00c1810004540d5600064807403a080700d03041016101002e42050000f00a0000460b0191071a880480c040701c080900c1c11001d04c01000301c0e01c071048084c2d074440f038130b940752000b4005560158110301ca0030005030422041c0716503c50f2140c1000d040058640d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 564936807 1250 564935557 564935593
    0xd0b071b03020f0607090f18020c0d05312310031a090610050c01020f07033f1d0a080301061403160e01031d0102130e0f0a0509 56
    0x120341600140d00480c907540843d4024400b850f0030040a150945403242021089410380403640f0861402075040344801d005040343e581514241801281500c12103052910028400e800200c0141e0014841900344800c98680c0340e1942e14240e2034401d000b9106140c002d4215103510401084450382e03d650203000210b80d21244400407511444c1c03400181c0c0141c051000300400a4107103914091042c96044c490300d556888400078000b0704500e40945d840040c0c0b082d65019024075130420a40d4200880c1c000201500404d0701040390241c2d42804c203030358805c4100d4020710341c00b2161115211005100b40100c90400f40c0140c0301090358034039150848c2c1401002030703180c40d46550090300d42d924084014403103a680024801901040080102e055082c107040951042c810b8030740d41411301110f510801d1023a4000d400c00140c1c2c800b800d8269850041c803440c4517021f0750121010300c4055a6200e008a030f10521003807601d001d104052408689503071003d200310000e02019200c40c0c001c1c424406000d0750340440e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 564938057 1250 564936807 564936857
    0x512030c060108030322021f0c0c06020a2a180603020307030f020406050d0834030c23030d020a0c0b0408070b0a020f0d0b130c02031201050406050d0b07 67
    0x100020b5540e0b10b0046d03260000d00710324940b900840a06010b10307001581d0750540c88480060384039401103007451001010388017100d02d030340700070000c009400f000a0b401c1d401141c2002841e0050440070500d20303449403e01c2c12641001c0502c1c01503c8166014002e10f03200711a0180400750240300000c0d41d64032600060318104c8d06a00817113000c40702d50001000c6040074020f00d00200025100080100c200381da4042240c001c1d48040b000c1c0c1c8105800e06031070400b20300551020f0a0a540241c00d9a004509000788000310072281601c450040e078181c0c901c00b4500c1000e138165400550080c60074100c291368044007962020f24240304000000b00841d010070001c1003414051403044200b2962030101c1d161042050500070103460b5894418001c00c3c0c0c0b0004244100c2c2e11010b0400c10005d0f45410200024441c0d002d80e80384c0703081c414606203000c00a42d40000c01085090b4109505000e0f581c0c2c1e42c0701700401e41c3e000b0f00132070341c10291854080d0b000586607111140c0100c0b050510381001380e02c001c2624403401c44 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 564939307 1250 564938057 564938069
    0x1c0203031b070801180b0117120f0a0206010f1d180f030d180f060f0f0e030702010306150f140c150f1008031b010e150108071706010512030c0601 64
    0x2c14010080d00c28244500440407440f50443c15082031140c50f1000d265005114507a4600c610a2003012041000c0c84916450341030b03540c03003580b03d1500300910354558216840b01750140c840c4500104107004104a440111080307209421201495050218803101026010b0000b500b0404a003100401c070a101038802c0b031f10404000c58543c2c01c05402a0103840d6030082d2030144107a001c2d804c80c040762811100c03e00d159041140425074040e09048480144240e8804940c0e01d8038000866502c400c02000415029000b6602844003a8070b4110803036211130250180004606032440e0224014041c2c000003410340c003000d000c10b080030007100c0c00f2030802c106a0400621030f803001c0300304001100c4445065412041c45100015001c1c2002d001503500d2080200001c80f1841d4502019200c034000d4000b0494900c201c800d40b00752500403041d01074100000c0c01494030a0013050000304520310542c070401c801c52a00c40003410300f03901e8001800f00700c14021003220300c01e0000300189080c0c0c080811440f802000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 564940557 1250 564939307 564939313
    0xa12140c0c120405010c0623070e03100b0d06050709080303010801021225030209220c090501020d02030307030b010e0d110f0a0b07063306030c0e1c0203031b 69
    0x1107209160341801481403910500300000d10041c40a643d200340b050015541c00a070004214403150f81400e80300e485803250004241184040059040e4000c00034100000c0540c00c0382d500d4940d625070941070700e803200381141c2c10615505003100850300b075030026a0003a034203080c01544147c030703000c200f41198401d070020842d50b900060a001c0c400d09813a039550740101c040b66482c903007000d222410b00051203060055410140c0204207480700760707110100320a900c800c02420000e02c1c0c41e0180c1250141080030241380c0403881c082c100081d154004074407109a01110780c082c41c60b65440090517801043d541b803c8504002400150099a4507003050300030a1501a140380d021600303440c403c10040003034194140340540151042040801061070035140c000741d00c5031000c907540325035900b0740c029000040400c1d003906010b200c1c45a00c0e05030418107901500c406990500c0307001e1504400742c4150b0b01e183c10345600449207140d1075a1503881d0a243c0c0d101c83e4801804e80740741c500403a950124000c421844007520f90 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 564941807 1250 564940557 564940567
    0x80301120b0a0506030a0303090512070309090e0a0812070e060703030906050114180a150f03061514100309080a090f0e070806120718021b060c0a12140c 67
    0x414407403440ca07031100b4019028440d502c0d228022135142c100040006042c50f031120320343c20801c042445400203400c1003003610341c1c51703018504000b0a0607490307108124110f860021520f901c4140415080da00c190000d180f00e207081203c0d41c2509802c00020006400c0103e07600c4194a40c2c0d840d14000d1010ba4002c0e0741c0400c3d005224240f0908455060b448000e070300d1f1402c510181680c070351800503481840404c010540039610b88040001920040503960079000180c1c03408210103441100000c26a070041c40c00300300c1e00e0aa8149894904020b02500282c50144c40b005600d40c6850341c1c100c0440b008074600803602c0740c1c0b0341d519442582c0041d010400440c101d40800e02008101c49000c60081c1014030020045041c1b1007030203085210040c00503401011341410246084204018120044c4441d0003a940c1e0001d0036042103000303420080342400300c5d11b211101ea00d0000c800003001d9006014614400e441c3c40c0c3d1401043d80d400c400f505403050000d44400d15400d4410030000014070036400c1581041d81c1d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 564943057 1250 564941807 564941813
    0x1b080a03080906181c200706140702060d0209031006090515010503102d0311210606040f0f020408030903010b010c05070e1905090a03120618090c0308030112 69
    0x8450010844102c2c904c0414500815040c0080c2c64001c0c00365240300000d807103400010880b640e19403c82c28280000001c82810840000003400e9022280c403552154803034101c00c00d00403068440c0c00d10207507200e5001e011410f40000c2941c001c2c000400020300701d0700081000304040003510800c0d031011844a80e50402c101c2e98902a18220707494003800d103083d604e90b00c0c0503100c08841c12540e004a44510b40190f6003900e06035071116456000c01490a10410b600d40d0300d19000000841c166883e034000c00c40710024041ea059000040d4078000d2a07440a4052565103d007400020100313007a0b50321000e501d070304094100345e41d1840104090b0903060061540c03030383e0b180141400c1d100740741c9140d4108505801d402c400b1441c0804c80300c0c03d80d41074508012054403001e5001c4110803040407103074402c51a1000b4001c1d6182d001070030542c0355100740c45c0d5031400d000842e0b039102145d08901c140c46500d8080324010442c00202da1040d2000341c07054078240e017501c1d240d4031008410380098101d2401c86001058003014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 564944307 1250 564943057 564943063
    0xe010b15090a03140f060f040302010c0c050307030e1c0305030402240304030e0f1002160504060b0a0804020a0b0c0601060806091012031125170a1b080a030809 70
    0x209009621016241c030041c40c0209440030710703a11002d8072904100c0d0004c0b4000b00c0c180404841c06804000300c0700c950522803990050b140c000e4030101c008d50b11300b032540c041060241e4901d029542e0004051810220261416602d07161000da54940c402701d07a55400c0421018501c4014500e8020b80e1499100e180034418460741c21000c80307541c0c5000b01c40e0451202035900400489501981c14646464480502030216260f207007840002c640c0100c0160944880340c2d40000c4c40c409041034010549400359490040c001250418000c0c1441a00c0411621640714020048070381c0192000e820140c2541d40c0d10f2004c8410b030004a10550649c000c58010810b43c4e40c0010826000002158409150f04214541c00b50a901794814080c1c0030340301c800c1c2c000074180220100f000ba80c18003c192500c50380a5442840068500034040f00219465800807545840f203140c0c42d0801d91810005000031190307621010f1058030b5000106551882e40c003404076022006106603401207100b61118103c608021800c0f900b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 564945557 1250 564944307 564944329
    0x70809190f170f2802040f02070b0609040206160507031703090f0f030a2d030f0c1d0d020a17030301090b0108070905120f060408030609010503071d07120e010b 70
    0x4407503000b008080781243c0040b44194104a00d0784c4040801003142099808030311a444000e98801d150103800074080b9103135001410220721400d403442e41d503524101000b18030345003500d010390040000d0248030380c00094066690641405071044410455032a650195890205c0b049074032800303004028024000c60030030a007a81864460027038010300700060031302a90382c0914560402006001c01404e1811880c6079090300b03007649404c0d000085034200c124058081d180000160305850b00e000000b6a030140301d41047c0c0d4080003002861f00f149214a0104400b18201c5036050360320146d2428006600400c802440c82d4141522019540361f40c9441416800c440030a44142d0500c01701804114250f23a0281e20710003901c100b15280c0d40c16900301000300d8500300c0400140b225502c03949080c03000b03014401e40514400c200840e00c01d43c042c1c1c3c03034100340b43d11440c0d540b2516094404900543d484d4582900c41309520048a1600d512240140758085017511020300c4c440b4201c1e55191a400c40c40e05001c0c241403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 564946807 1250 564945557 564945599
    0x5040b0604081c141603080c1804050601180e09071203050307032705160b0c060f0705210603010f020a0509010e0d063e070809190f 58
    0x1500701441d0444140d01c40c001415100500c03007000320900c500c0703401400210342002007145203c0e1201c5c810310144041c01c1c04000207901003000ca00c0060103402d03c3c0e4040b106d01c80c2e0591890f0140343ca4070020711016150151031a4184840044020660100744000e80000d041e0100d20719507600340040321508020094002100e0001c80c0c0c0598800b090f04081204d4000001c0c1c0383c00a01c0c0300100c4a54154240b07001c0408000c800b011200000380240011148071003044940f00310712540d40c544501d0f805108200c590078003038020074001a0f44028048031581d010501d4203006150412440c81d00540301485028a07a60316400014000caa040034440c0700070244002c07008614041234208064942c1c0104128641008114120090700d91182c48035400044c2e8400010300c884d940b2003803004050030340108040d505242035000704c071011101d00c040c251070008003413840340307444060307221400c0581c0081e2210750801a40d881104d40d540102d01100c006105940c032521080341000281c2c00180c000390141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 564948057 1250 564946807 564946819
    0x9120f021822030f0c02010903020a09020d1b141b032115030601051203041e1502030405090105040911221a03070e071103030103060f0c210518011505040b 68
    0xb00000390000c8070805004001c0c00d01304403901c41440120307000c94554000940009921070002041140b58000c3d1501000240d818007600180741c030b0160b005030480d55440d0004100b240c1011525400700d00400076022040d828000415441091310324603840041d00c0c440c00b45811540c2e9002110a07070b43c05030030500c045d0420131030035840000290303141018007859115400000d000c03001000100204e40042ca494140ca09420301d011281601400c2188190004000e003180e00c101c2c4c1d103101004032000d40b20010f042440a074204070602005180091048500300c8445c1c3d564041d40d81c58441980c84040c40006e1207601030a0080414103413aa40148255034030200e2401c280e81369408104078058401000ca00d08607640c41e110210740303a002d000403c14007808000004024403100c0e0f088031071400c1c1c2c3c000047c405007805030021981e00004810b1191019a1191000700709415130b00b0460700840320b03e884184c3d219501001508682c03580e940300c06d50303081149040241d410103016040000004a8130 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 564949307 1250 564948057 564948121
    0x90a080f0315040b0f060a03091506080609070f0b09040b030102120411040c0804060e01180302060a0606080c0712030b030714040b0307030f0b0a1107030c03020f0c0109120f0218 78
    0x400c0c044040b0f017201c28804c01001c81c40304460741c440d51120b0340103900b01804180c22b1a00322655002004240100c3c0e5031406010000f5248003400500c440c05c464003140c0b00c82d400b914102003400c00750840d24900f68010389800310155540e8090002c2c051809880b00b00c80498100751802d049000e0010303002901076410a0030411241c0c3e0801c2e981a40603030024804a180c0007400700f018014205e50401c1a44015091004c00c14940d000840c3d910440c84c0020411509841c3c210079501d85070110f4104680b001c00701303e0f900000742d04082e0010480c1040c1800704844d841c00b40040d041585a40150383c08546900d807103002480c0c076004802404105030064200f0904640396529131514035407002d4400300741f4201155140c8065403002816000f00c1c41a00d880c1d03070701858004c18801d40070b4000d400601c074014925000750f102103400207409805841c0c0e0f0042c546416414a451484e02c0d00070303180014004000405a05d8000c14100309407540c6820602d6480c100711003240c005025150031240c0155816 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 564950557 1250 564949307 564949309
    0x30c1407060b030f0c0d062003010b07062901051c0204080f011802010905011b0f03030b040b09150409061b02071814060405130f030905180f0a05090a080f0315040b 72
    0xa04074080300d0700810301140792008230100700c20200210554030444200040009100003801c40500b440038410700c1c00744142207441d80d003a450f045c402c1c803140400b10010700d416181580914014041c0d960109021380c460441c6c00f5000080b80c0050740140b0080e00700342c24142c1e0342c0c0000e10031040d80005040700301d02082c0b016000285240e1550040c40d0502600da040100980004642c1080ea6076001d400e0881c802d200d8503000b03018180c6814264010b9042c000070405520300094464802c0301d042d4003210601400804000c040c110300c15050750015a0707014031010f101d41e9a0001840140150000c002a61506402e52464001100c9107140c40d0f1902c04454031004082e4080c50304660111004682c980380c04442c4507500744c92090042030310019009010030550404101011560112030007010661143c620103203ca004a910403150019080002c020380819400660481c101108071400038a669403104034960020000ca6040b03480401004030100864100c04001c5005071814403507030714880c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 564951807 1250 564950557 564950569
    0x6010e150301050616050a030f03060909030c0809180c0a260c07111017010506040819050f030a081f0b18221a03010b0a06030c1407060b030f0c 63
    0x7003d8107128100015406129440e0700d00340000c0315401400b03698910b941c52401a1595480000340804a4141400099400e0769803060303128042c1c15031140c24900503507580d02d2200382c0c001d9034482d030302000c8840814003804c040c0001d80d1040032200903441e9504005c02019000c1060031510420010b240c100110180350302c080c00541110034100d100b0344074016850700d00c00110303007159250340140ccc1030400440c1e0560b00101e20f840150b000320040c6010b0b600c0d00c0900602d0310607070181401030f41c4500590b4000c980600c803c0445180502c2c181e850224908440f01d041d5071015000c04001100390040c401414813804100058181018039144060329250164503180039014001c6403c0f540090120321a13160b0f00001014141140c090b1001b1181174404030009148420804042d031910072039484107410148200c1020711002001542081e14002c01100604001c10301c3c1004c0000c41100f0041ca0341002c00540380e014854400440d66400e68001d042c500002482d40046aa11800c05402c0686500c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 564953057 1250 564951807 564951809
    0x4050c0403120c0c090c0c152c0316030c110a140d0303060509090a060609050130021e01031a0603010b0a18240c0804050d030c020d060506010e150301 66
    0xa410040c0440c0e50f60b00b03041200000a07800440d1803030500040e03410195100c4203e9000c01e02c2150060049148006c00c04112000100c02106521503200e01c008200c1d0680c80482404a0300404c881c038001c803011100c021401080c0d0101c02081050031050200080b00c03608030301071002660034401c49850012041030404030055454004d0b024074880f602414860b030095000b500010b0a0b02115007408070f0000d0750342840f40c80544109103001404246a0000d0003401d0480300a100404891410040401d208000044c8040103545490079a43d00584540d113076101c1c2c41034801c0384000b0b0114040009400e40c3d002603d1802450b0550001d05240d654070826281902ca0204e2003c0c0c031040000300540785d42e502c4040d5003890417405600041d40341808210031003815102c004640b0b0b05201000b003038903060040760b4010158041440184140d04180f91244003560281c9444000035055401007001c179941c0c440c007030b82c0d915198010020700c0e503000303080c00040a03000d5582d188007101c61302030f0308814001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 564954307 1250 564953057 564953093
    0xb0102030a0305090102090a080f1209090601030b06040e04061d0303070f030b030c0306040503030907120519170c0d020c1c0f050f0f010501152a1b0b040504050c0403 73
    0x10f01c10200300c000c0801d506840030038501405060017103444441c01039132201101d400c80c07024402e03200f001c01c12480d010281d0380c044001500625040d20380b40c0041d4081c108425886070061014000081c0002c0a010070900642c003c1d000000c0c00b0701601100d852101344c081001b15654010410b006226601004104007412985000102c5109200c00030b03017409103900e10168941f003030b4028030052004c04001580107007622401c1b210079079540d040045844c8890b440280c8650000210842480000080089c00e01d20801c1000307080344079500341c403460f03820010000701250700048001421940400c076400c2c0d200011115900c01c060494030103190661032480081030203075503a0301c1d1001c00c403042002d1010401c0d10001c1d078001c0c44140720100d000300024030824440b10001c036201c0550038050301e00100c40002c102c2240c424030024a9072a40c0440c0201c43c11101280d10444102e40c1004566540002d400c902000b81e039142c0c94842004180c49001e420390b40080b00821081000804c04440e080c08910 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 564955557 1250 564954307 564954311
    0x20c04050c0c010603030e032515120603050d0327060f020c12130506040f03110d14160e010e04030f03020c0d0903140114060d020a03050d030204030309090b0102030a03 74
    0x40e80700e007161810302400031034141540c20300d0004410903800c4050700011000a4044401c10880c1c840010b2405401d500552050609480300b40b0070203524030410003e0281c28144005589041044101140d0386a8402c1c3c80d070340c100b4580014100e6043c001c9030b4020000b049155440e06c6000f60407002111401c80042036607989020282c2c2480c0a50152040707000c446054554041140b80905016845244e96950100f81e00c440420710b0300e86442600c00366091400512072490560380d91440e1282c0c1c040500e03603c00c1030307130102500007120780c201d14140068200c0540304140349c041c0010341000b8540c003c840c025480c1c0e001030203881d010080b0250f0054052a00110401011030207900a10582000c081d10307002e90002c2c1d069482d040600502203074460f1510804015607050326a00f25100030020701015540d0b1808150540380c81070507150ae10340020100d680c00c070344d40c2da0f9561801b10410104804203030045400c000f8141c000030041c00404c03200006000002410000075107034410540d00300b0a145d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 564956807 1250 564955557 564955561
    0xa0e0303070c2d0210050a0507141906020c010f061404110d0212060913030c02040e0309030601090e3a20071a09030c060306120607030506040c0906020c0405 69
    0x220020010706031401440b083c0ca20315040ca9400f100c02d41c19941c040e40182990802c42550074865402c850f4071100030780d1014280049541c6105d101001070407048441e01c108181254900110b50042030540d1041e03e00590b50f101114040f804e403070784010442d40e000d00d0201c04001100e010848410a460100c0f000180442e03405401502c03400f0f1002400c3c6814408216103401e0000b1001560182e0411950200ba03a034601d241c40410343e488a070300034001000c00301c601005040c030b90010700c20301d0001c005a07402c01d107a02000c81d161139000d92000381819140c10007490021824084c84244803a0610681d00081a90150841c030031040b40c07990013104051204a449548600d03603c80e03507143e003003507580e920107611030300307199100100d00944007000007810365002d2908800f0100c620200000e4003800840ca038117010010030781c00c010041500b180043d4100486800144801d40c80703900f003510001502c0c10868144170488041ca140c2c0700a019034801d0a0106580024581e07654060840340071036a9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 564958057 1250 564956807 564956813
    0x114060130020c060415110307121a0d200607030903110402040909030f02060705130504091b1d06090709050405041716060b0402090604061b1b09050a0e0303070c 71
    0x7885040c0c401c03d8940034030b81c02c1c00304001c00206019002600001c040c00b1b140b03080134500c6a548416a8a00c1c003080b03148014842d038200c1c64118107003074510020384010030070184000c03c4c15514180d404403000c0c0c0070701c0d082c00801c6008072070341c9a8100082c0c6000307082030b8081d074010b400c0d003400c0d00018100d6540405000b540b6a110340480c1c000c0c001c0ac42d42880000021301e40507041c03030305280104c0058000c56001034502c80c451800d803202040d030002c40011007454041440300400e102d4005544210302a8010038000041c9040d802c010f04444c44042c8201c0f15424403002207080261419200d43c15035010b00c02b0715139002201c507041e240f0071600001c01c0e8840b403400a400115032901007400d04408558110403101c00c0316440c0016004081c02e0291f20211800c100492140c200f03040d5021805000600015110310000005a0300c00d2001040381201501c03501c00c40e001c003041411115040180c10b01c00e1400034094070740c004402d014140180012812034640724000101a14108004000100d041c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 564959307 1250 564958057 564958061
    0x3040c0302030334051f0b04110406090602010209030706030c1205010b0c0c0406030b04080708160503072f010f090905090a0c0807060c060b0d06020c0114060130 71
    0x1541e00404480d40c1e409414040c4500b03c03061801c0058200c59240c18004640700c41c1c01c0f201c08140e0000103003107128080560070305070140500202d9005680ca51041c0500c0e01d55102d0141100d0b00380e80c8940d01c46280c600005c110030101d07000304c0216401030028500b6030f00d00007940001e8030b04604010900800300070f01240d003000e0620030542c5c0e0505081c000180c5c0d8903200020811041040309444802c80c4800610007940c1340303480000c01454a8400240c04100300f40040d101079031040580c20301c0c10305a081e03414048603103244152070582001a07820100888140c014100084a480f00d005100301030198141941c0034007a0103042c0480c6488e01340205c4c0c0f1940140c0080d08590000b08030310705100402c00d680d682c1c8140129a00c0401050119900038006070841c12550031356034030445000c40341d071008003400e01080890f402182c000c9259001860320700281803113484050000401028195840000320b03c05090941030142a5512188101c40390704614040001d0411011500900300e00401c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 564960557 1250 564959307 564959309
    0xf0b130819140a0c0501110c0a1101020a150e1005040209060d02040209040914062a0901021f0c09051504031103070801180512120109090507270510030b0c03040c 71
    0x401c2d60000700403201036003003020b5200b92409a4001c0000c4104582d24113554800c008200480e58804040b10000412448800610200c1071051303515002e41c43c1c3e20308942051200426003110788800c2441450501080340c40d2040c01131440a02a504198011400014001d001680907403061043c48003907407580d4044a01c8514050010440e400940c10902c110328601c1e40042c1030744c082c440100e080081204000c2c48254020b2060000658102c0b0350000507600c1415924150301911042480c84000d898004084c00b2008071301140340051884000c08001194100d030f0700c600901292111034480e458281c41c2940d61081140910485c1d100000341707010360590112030a5801c2240300fa0954003c1185107ca0901c04c0048030310440d0701580c244150b000b24400c0c08940f03101c00d001000740094580048082d5400741043e02c00450322101c07104641501c3c00d078280c0569044800030310042d19a0b108940e4011081e410340d0041901710ba94200e04603c01900340200c80c3c502100ac90305014843ca200d01c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 564961807 1250 564960557 564960587
    0x8061305060414181203040b181f020c010f0e100f020c0304090603120518060a050c0601060807021209060703210c03091e0201080609090111070f0b130819 68
    0x3201071038202c00d5640210380000b50745600c2e01845c0f10080c1c10740300a4041d04c0c082c03070344195000c41c2ca544d03018218415011072420380005128011505c41e0f8506200da800c52034040040000d80c2e1a00070803006400e40346000f00c54054180b5040d108108608042a4810f801d17003041c80210f03100c0208030494010380240c55441c821030000280029070340c05194855803c4900c174102d4107880d0800c0a400b03940d03500411460070000603104244040c1c4c4c1c03030241c0c01460813440a040071030900d02048280b500d015000d820800102d5030304014450241d404000401e455085074104502d8000c5560205c0c00f6070050610003024410044401014028008910850200400e01c10041d04d2141a0000d02822007100b090f00d03050718090200000c0503548110601040d010707107464415840c5d0700d017031040d100c0004040c200d580d562500c503213502c0004100100f184500502c3d1a190f980c204c1e09100c09071200192060448604401d514030004000000380d4520f4010050107082c2c96001490070307501405101034407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 564963057 1250 564961807 564961841
    0x60c0905040f0b03060f01240c0503030a0c021606050d0c110303040501020301030204060e070219060b030106081c020d1b0501090b0a050a0506040c020c0607020a0f0b0a03050601080613050604 84
    0x80d00c00c0380b085034409a46074000314111280d907111603407021517030002806201c001c0d0090204101d11245c4040c1e03240300707008280c0b5002d8414206501d0b25800c541040c0d46070140c0940300c281d055040d80d810006032000c5448030030b10700c9201d8034100001e800c91003500c1c1c0c0000300c01d854200e49190300f40201c44048003170a8202c240e03070f80c3e45031078603020303000b540f09020880c80b0754030300030010849080c002200d074030600040d00209060a205080a5487c0b0b2003070000b00e0300151103143c0440745881c07e0007650010b141000c004e0072502c49000311034240181d848084404c661100c1101540107510906010602e00032121255803059907003400d0780905814040075000c0c40c440313024400c80181d40d0b8403107032065818100c01c000c2d5499103000c0100780c40c4104074440060380441a14103181c50400c0003044030302d00c01480441c20650ba051002101426a4000490550080742d00d03070149806002e01d80e84004246440e00c00c0c2d1a20400051407251101c155103155956640000e006031259032000d400094026a5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 564964307 1250 564963057 564963071
    0x706030506030f0717061501050909040c1a180904030e01110708011d0f0d0504050f030106090f0203060a12020d23010e031b060f04060b150705030d1a010c060c090504 73
    0x141e20305c1012680800e4001e1040310009aa81c4418500c00701c10044140d46103880c0c090084104294080054800d40c0c8030a2469000070703000c00f0101c2c050740103000001c8800c1d291880c0760702400f9000410509240980301140401000a07400040358489a1090034500405034854014501c0c100f60340e0031145d50356280c40c2c02c0380448030030324214041c80050942210140c81d080c0c10003d45600e030920700f20010034070901060015180600d40d280c2a4080039000241180c0e8400c030b0082a07650300110034032200d0303001041c400c0714140071134903c020f401480c00611302c480f01540400c04841200d10003608460300741c0c0c0c50140c040c06011340740b050081620300030300000310300c851550b4a0360f00c100c04010200c2c01e25100000e00074804507449100e050745440c500c0e8260b4541d01c0d4540078054a4981590000014031004002042000a4035015006200440d101c007070320324500303049907101e40c4441c0e00442d9891007070086a9110805445c03031940040d0100308110564001e03108512550803680c0e1003418481e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 564965557 1250 564964307 564964319
    0x21c0503040f26060105150c010f05010e060d080f0a0c0b0907081011030a3602030105130519050c0d0b0f0615042d08010f060e07020706030506030f07 66
    0x5009025988145114081e601d2081100c60000074060380943c20742c1c212000412031031802c6100341c6030444941c90020302e0b10840009041c2111841c111403c001e41e0303a040144642c9059140042d88828141e45020010400e0b40740e0700e5860040f00d10140d01e0f40c4001480d500344904c10340a0400640e44280341403198140030350220f80390081c900481304684142e141c00201c2c00340034000c031a911903409032180e29503151505040044c10350004017801e05080c1240d04844480310015840d20320340c5072081503181030054410107080d904041d00428440c0001c0420344040b03080401e066101b103021105c5218000d9441c0b5040c0d080001704038517685c0c04004c001000c02440b1802c500e140c450002c480c0c48503615a215420029100e022900300406010f0900c018401409612101c0300408141002c1c602d1000c100448600e041881d034000c04ca890b51240e81c502828040d60003010b014104a200e403945915184400a5991146100e00b504041d11200031a00b9500c050090844c9240240155603030203407100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 564966807 1250 564965557 564965579
    0x60b0d1202010218040c1d240d06080309100e0a150201020a080f0c03160314040f020420030c1309090f052803030507030b04091209060801030807021c050304 69
    0x1072003440d16013041d00740c540800d1925224030602c404042d2074030210030100120903000502445c000c250005c6a41004001160150018144158402101c0342c0c1d00c1c0f031b505140c00f05a8075107900c01c44056000788008000d9580d0640b03807210703400c01d518054118003448400110080c801e03502509850310b9200b05a00440e60640041021a07071a49038000984c85600f80306544000403264179144240600103d80340f6042c03040444200589454040755940c20101c2c02001c020094400300c4119005030000c0c000c605150003103035084210950a14100d88002c1501174403440010b0150150600004498424401d010b040d00050a40c0034800c000448040c9412440354910520540e514890701c80c00c81024004122001c003007101343c1084001844055901b80e025110141c803900a043e1aa1642c403066103c6104800b00c7c00d016401290504612000c090003101a940181b41046402c00041c00850100d10880302c11a5054490b045420f52440318010512190840205503000000780007a09043d44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 564968057 1250 564966807 564966817
    0x30e0312090313050f090408090d0b090c180f01050f0406080115030507210f210816030204290f0403050607030b011706150c0304030813170a060b0d12020102 69
    0x748641c00e03c143d845104100c0305000520300554030043c4540041c0004641501030700540d03a0103000e85803082d1141d80c8100c0800300868000d074480e80811241c0307046280103050303103410390080c00b80d103250744c00e20200d07500e6001014040d40340107154803103030145940c0b190742c80b020062506000800041ba0b4070028800c041d40c1c1484180c0e194801c0c58404103007515066010703041429001010305c4107013556174411460103e11001580c903220105a2a65181c0300000b030341050421903940c81e04d2a20313011802d51500043c1c41c10440c20980305220a0100000001d00c94091007a407036103005081702c0b840d4a1403024818207600e100b40700008600041000000240e0b20b00800070780d1010300c2404650801101c400c00e40c044004020031018022501ca810041c4401c880c0c4810601c55034600284c5600079407940d44154400c03100a100040c01c8410412036501d0480900307040c0078541041d042644a103079440c101144041e00c0d080c3d070f5280500c00c40d5946006c0082045c1d111510002c11660040043c1c002e41203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 564969307 1250 564968057 564968077
    0x20313080109020f03030a200a0804060c0303060f0803090909030408010c05070309060c02090f060a0e090a020a08030a080708071e03050a050f090304060509030a0503030103120f03051006030e03120903 88
    0x1e113850b40c1c0545004400d0755a00d0308140c1d100d0714100f000100300c81030031564200551b03603400b4203d54007000c1a003800060024106a07200c424805401c0e1500404032150b550214240d5141c8180c188a0708101100721317880e4143c00c0b2080b190316110f500030b01e0308511842d44845001d610b040e842c44030161b00200644041400303916a602166a20700b019150480ca450000754041d4103400040d5481240c1403646811010103051003501c20b0715002c004031001400da0307094007280d00030408101145030440306403021303021110240d0b0800004070005001500040c007020701f8040c1200009654500c00e84145140e40c0d440019120384007000c550140c0246003c0e20035080090030040004d0020100809541c01114504025490f251030500111443d030815024554107000e6540308401060782080078601860107190f142021000c0b0301c0002d0222407009501c80c0605040404115112214103c4042100e10380d080c00708080c111805100d05501c03c0c0b036a5440710320000c109000c0760060000180442c800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 564970557 1250 564969307 564969319
    0x4050f06010e07121a03060c09270a051305030d020d0609020a020d1826010b090708060d0305071b0f0b0c190807020306010b0904051311010c0302031308010902 70
    0x40c03256a140305005085481c6000b1035a2042c010b03078030404171362000e030103a1038070300000e90a90b0000c40060704048080d140f0400c19000070441140d24a080c4510b05003202c410341100d030f4500b03e07030388a19003e0310006009062481d510000180c12007281ca04100c030069110081d2a51282c02c84107900003908010305041c40c80f86004c50126205400d03200b111000751303160b0001c20500003a1402200c14080701ca0a4404841c0f110304009030f0080328034803040001d00640b40200c1c41048900303100e821500010f102e2445141d90801780001c45400000864003d4016601202c042940d41010746440c0b080030002403a41c004420500d02d00210701b0b41001c20342d180c0c0c0e0521910950f407503030380035494024003101d8003543d000a40c140008081e1903a6900c98180701d0f04207a81041003d400203414a8070903400019088000294104289030910595078040740321800d4038942c070b1f40e40d22280d545c644260001d0341481182a04035040c14003c1040d21031b1185d907200d070401c44988507150a4040c06c15100c3c1240500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 564971807 1250 564970557 564970559
    0x70206040b12190507020307020d03020705040c050903160f030809010201140c09031c0504181b02060109060f0f090c02100c09050f0306041208100504151e14101704050f0601 76
    0x41050141c28044d07401713940103605020b1550204a155070301e49400314194841c10b1000506500e89002d10f078004007250301c40b070703803154240c81c241030a241d4454040c2c80380a030180b10620080702c0100204040d20382100c00300d900e881c60380300103070300421001c0540061b44401d03408015441194000802d040002135041d5072140c03080400c82c106500300d8500b14030110302c2c14481440490710102e0b00996a0425040100302c00c801e14180c1c1e540100107094100c016045800107016104080c0200001040621a006c2c007182c038059040c001d034000e0b4000c040c6180e0302c034101d0f0040341e03100704202c0c100c5150b81e0700c081282c40c2d002030010b8940b007440c0c8640d5020300d100c82d0840200313141c0400c045200c0c90700305070584240d501c0c248045504010040042401c19001800400c0300d46031b6110f0310114041001404055508240384102c0801401d00c44481c61a8840400e00c4000320f0b0f4404c0c0c0308503003020f855518605040c120306441044010380c081083d00034040402007440030020303464001c40002c2c0b095403100d07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 564973057 1250 564971807 564971851
    0x20d14160f110a030206091201060b030f041b060c1515080f010b2b05030f0304111c020f0f06070807060903110d0c030507060225030f020d0e06070206040b12 69
    0x42411301c4044d521840138829201c05083c5030b9203c40055000e0000019a65105c030f00020103900306680c01d24100d05d00c44104070402085110030080c0e1740c24655001201480d226000305401c0a00c00f0050080c1000c902c00500c0740b070244c000303503000d0782220024030019444e000c90340da407030001080785001503091609400d45400c00e1846003d00e828085106400b0b015110340444201260840864240c482000504132070004070b0080e501030752080c0400403104403810108020b07a50340c21480c2100034000ba1004006030b440284d25090003400381d43c0e2882503505000064540d0040355030203804c02a00040d41c408204040d0b1000410354802d4031068512a051708880d603440c89100c0143d40450441c1c0341c401b003c40e00460180415a1180102524001d10b103c460480540d01a40f0107132001d07042c8140d18101608108004401c45003072008088654108100502c2c00c1d2064024900440c00003683c00295120303402200d0241c0241044660f464bc126400403203022421a03c0c08082c090707e84a44001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 564974307 1250 564973057 564973069
    0x106090608151804080424080f18010f0e010c0c080d0b0f0a0801140106141c0b0d1a06091302040c030b0306070509040f0c020d14160f11 60
    0x6a4996036201015540d41803003040089030542c0000358011600b01c1c007110511008004a48030b24440e0042d1764645103000c00e245400c002802d08100c10280700824900d2039640900c0c060b0f8460406a100401c40d01d038241590048140c0880c14601542800c00c00041501071740c01c4a0803845d8040c00030032044082e00c4049445207481c2e40c00400c610420002e825400540360004c81120ba4002c0003100d07001203510000d070002500f80e0105840d070751a807003400850303c49983c0e400e00400765030a00d40c40d020303907200c6401f041c0c2c450b00e00c2c40c0b060012440c4100d002c13030026a000c00002103000d4031200bc00640d40c1090954020095840707044031444100045c0c00c0d041515480e80034021001a0b8030350112190708000113001c044914804056884420b00c0e4540d07000c0000034040c40654944941e2031080704240000c0d120590541041c050512a00c0420a50b0000300b40030518051b241165120503041070400c1c3c035100c2c2e0881007032207115842550040c005039a0402d00c82d80c0c4203114076100d9458140c14441 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 564975557 1250 564974307 564974309
    0x1e0c1d03070e040501020d050f0a0c0e010e150f070303050912090a2106090c18150e0c040815070e1009030201051b06040501020d0c02160504090c120614010609 70
    0x90550000501044010804a10b442e041403064001504000d110501c10040790002c031203203040c201e0114244a2103607002d1241034011986441d02e0000301d880080003820058000c203c450140f42480001c0c2c00b000e4204c819507007074854180d00140d40300d105060042c0946000d0b60540b925014179481c00030704030000000c4415289020344001103507460611102002411018210348140c00c4004400000d003042c4103c203030003882039001c0441d09007001100c4455809000700d015809261404011000000c0c0005500312034070140a404155900c2c10286190f002e207600501082c41450480c850030251040c645126444640e0b0b90403c00b01d0f100304100900f10030810300c4001c035400312828005544950002c050944424840402c118609100701d803500300f00301d40684499501080050320804140107600618900784020250503500303030011580e03411030348540780c4500d5540e040d0404201400c0c0e8a10000c00c19020145000b07401814800701402c014502007054401007400030030203d0140e01c3d224 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 564976807 1250 564975557 564975559
    0x603030f08070f050d020421110402040806040807050a0f05060105150a0e010e0a05060a0801090b1801140f210607050414010c05030702040203130c060203090d080d1e0c1d 75
    0xa28040b83e0001540d07540d00c000361200c18541c007084082002d050441026002c880e40c4d11801964401c02e00f40280c200c4070302807031140300f5401008100200000080c00540140e0080c048a40d03070303c80c603d00b06151900b803000c001c240041680d100000e01202041c140e04032642559502192403a0f441e00388c0091107480300c0344020811440e03104c005540700d541c041650b5a400340c49600c0c034035110800640550881003d10700012100401031003030184d20f0048040580c019500640341117405000c0a55000050080300071140d45800f5842d100c0c0d40c0d500c48011002d101419914502c10968002c96021240d500520100c3c8034000100740300900c0380c012142103450b1210b080c005d0220303507070044032240f103001030a13130765807000707110741000341e51140f00075030203018000b00740549000d062030081d5641985a2000c01950810b20404d01d16855540d51891215403202e0742070364480c4680d16840043c00d00e4a0500e115510138601d040004425a108602000d0399880e241c44e40c0035040384a034800e0741200985 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 564978057 1250 564976807 564976817
    0x6040b01052506110a030b040212010312090b0a110c03060906070509131508070e0705070b132406120c030f1703040f1403031018090b0a0603030f0807 66
    0x598a82c2100d22015800604180c2c110b0b9040b4039100c201c19626151395209400303000055514007560117205440a01c60241d500b942015100c2519101c500c10501c0042c0c00c41400780100048144514441c40251003c0c07021743d61140c01c1a00014180c410310030059140c0d20805500700c0c014500001e0091040c50302c4c1c4000d00540da222002120181c22401c2c4a64100000c0f03021199012402e006580b0040240780881301c20b5807810008501d0b1044590040c1c0001c0c54010611500951110841c1c031007a030014040301143c1c440058101c03070307644404806400b01130120b0006610040140d20351032111b5034105e05100550311140d000380c0d0400c4038003008180105a0710208005040d5800b540c807124006d903034150f4580440c0c3d000f80700562044808072404002e4124840c200000540460711072000c01c00110700310b180100a042250880e80190307034590447c030501044802c0d298214400e0a80d026003500c9081c1800d24014025020341d0100300c01050b01c90150252aa20805070b10740310340c8480d03640e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 564979307 1250 564978057 564978067
    0x81e0a1209050112020c071815080609070b0a0f05030601090315060e010807081b010504080703030e04110a0c2003030d050402090a0b150915040803070308011e1418090d020606040b0105 81
    0x500420140d81308c60540b640d25004280d01426140401800401210020305140d00d0140415810070090342c20103414840b051011011907940407409040f403060703504140342ea81c0c03201030041e00c161140ba40020203e461417001c8401c01034072504402e0850701c0e60807a00744075036204c0003080c5e1111801c1c0100c107410f60040c14000510302404000914550060600b13626058581356200d0030140c0613003040d404552004500200c070308240c4903d0341d01d24000b40d021340c1408031210000304000300322080500320a010030003034800c0c8100e02501a00b118030040882e0340c1d64181e0340010b005070804507410b81c4650300200c0000c480103001d006001240d600200a40c5649421206c4440c0c5034004403900f0b504182c1c0c02c11542e004a200c4001000548280802541c0b980610701c0d00034000302050b001b000c00c000084000a803242e900c0344501058039920162040c10300c00306004a2a0719950f00048528800f620b01030140c142c1001c03951103000d201990903145540e0f074590502007a034007060300b507d000410800c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 564980557 1250 564979307 564979319
    0xc0c0f0102071d0a0b0301141f1d090f06090703031103040302030a02090c0d020d090b180d03020708090a0b1306030c08011809060e0309041401081e0a1209050112020c07 74
    0x443c6980301c0c54402c1d00040329840c80e00442d08503451090b00032103524031401804030b811884940701a120002001c0e03091900d0628190003d0003010185140d01c1c00e509002085110005200a81805117030b8000ca84541c50304d031600c656201d2043c401a00030410000701c0403111900401210103813500900209100005503085c4002c2143c000c1c804103025100313010f541e1503003296000030000b4503501e6074003180c4000e441c10266041c54000d00b1000e54200c0d900180b51448501141d400e03034825990800603190f0959040048080c4201c01030f03070758020700c1d9241c003003829103000000e0405034a05149508078681c895000394100d42c82c1142d00004501180c004000000c00c1c5140c00444c101e11050120300c0354401c0d81e810b0241c80b94109002e002e44c2010441c421181000c1c071503080091401080c5c483c1551400f50031680381c044003500c01c0c0748991814400582d0042c100080f020342c0d0b0744261040b02001030003100516000681c0101800541da141c0e44003020445030095941c2e4289001c09043d019160007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 564981807 1250 564980557 564980609
    0x9080301060804030203270f040b130216061e0c050a020c2407111903110415030503040b18010302072004061701050603060115080f04030903080c0c0f010207 69
    0x1031013101148410081e19000d0844103482d586900d503045c81680d1040d00c100100b02d039400d04e0350b200c0c074000e500e8044110b40c55030300c801454031440f4520500507952140da441e020b111440402d0003822043c145451419495900e400042c900300700d485003040b0f915a1080708032418410b1610141c01a4004103203480780b8034010100c203260108400d121032202000c86c2c0111b1050b00280c0043d1041c03540030700038480a08062115000b44d00082c2c2141c1501030030b560b40c2550303840e814011070b80690307524400a00c0208079503038014003950308034040702d49441d55002500010342c0031910751882043c21090f0030b582e3b54000d000756800b0b5230780140c82003140d00d0148101c0040032000c0700407a0307100c0e44070600060001581c0d049032400c0d5402c000040307800d00c3d100c82403501d8031006a00000e840880d03014182462350340300d644113411840341c0d00c6010094695060481d00360030540c001030603441c400566501c11a900241a01440009869074501c05403a4001640c81d00300703034418640c2504c2007801400f103400c42a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 564983057 1250 564981807 564981811
    0x6080a120302070b1503070f0b0d0b2704030201061d01060315091517030f0403021e06120108010c11060c0d0f020705010b090c071a0703021908060112090803010608 72
    0x14580181420070302d07141d0b001404c2c8107480e0300000056652900005050074070800c00038050703092075031b48041c0c0307420000c02640c843c9410300b040c0c065440c00700a4580d55091070716410020061442c420702c501e140c468102d00e14040d00c0840c051340ca030400008403030240d0340500d4103000c424680d2090305c1e0304e400b81c181c000d40522104911440021000445c0440c030500c50b140d480f441c1c0c0020b052107281844501e007540e0310003003c1c140c0191700520244c1d41c3c0c800c0810031281920740c10344800b51078070a05040f2248440d410400181c0c025008078650b03886400850b6000d04903240d15000340412000c000080c2e80740704554425403141c0e00b02d01c0c00103011060f141c0c0281042c04440c44c0010b6108070040e281350480e00140001c48003a51901c0c0d00303103100d18000f250960070080305c0d68280d16003d0b003991520034032206801d01c1416054600c000402680c0a58150307000800084240c0a90104000c030044c90300e5012503805000c64618841071700d001c4c016224910002e903004080a01d10b900340313031054030b0700030340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 564984307 1250 564983057 564983093
    0x18030a0e01030f05042a0e0a0207212607020c01230c07080c012d1b0b01031e0308133905060c100c051608040e0a06080a 53
    0x43e042d07030107002c00151040034407803401010500107000800764120388100c82100000401c0904035801d00200e0308903660650003005104006907160030718900200f44002002084c8804814650102445600585c0c5880c03000051464900582070303407034a880d02003c0030b8807890010313070200703000f041154012a8a106292402c90030602c4001c03813130310054642d600658135204950000442005061010844019580c40900302910100c4a4035490090b91203200c003a50500250050040103a0b8010302c40c0c2d40102c845048614010f140900b0309019402c0c00703200445602c0980110f0300c04000e02041c400d01c106038150b0b9603040988030100c400104810b059400d99881210400ea2030180d421010403000f01002d91201000b003641e40550381406000543c00540a2002001242030402c40070031088440d00c0d000f00c00003078005e040701c0100c0e018050807031501030300d00807840684180110303007001d0400c40b03074401c000f101c060b9521080d100035221b0300d10402c842540181d2281000884445c2c4604c80e001c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 564985557 1250 564984307 564984311
    0xd0507030905180a1e0c0203070203010615050d0c120501060507031d0f0402030c04120515070e060307051c060b07021e0303031801090c0608040b1003080a0f0e0301050103051518030a0e0103 83
    0x5c01c0030342c1541164112440e50000d42e1000442c841141000e0045800515500d1110710241141010150280c400c0c3d2486590b01c41d03807410b10021090107503d00c01032100c6900b070108070a6860300c00c054490b602030310083d40480c1c40242c071400f103103000300d601c0e01d1110009020004032a4029080c00040e40010b001007070900da0501005c900705100c61800c603c0179000300024003003041c024050552083c0e019000904104010f10000c48a4640800301c9800a11520701266142003695201482d030868007004095103080c040300084103240070020f0f040c0b1038022107843e00701d44410304401c01180116240c203074041d00b0510004c0c101c51805018030801001085c008200a807403599500f1070b0001c00c0d0802408604918140424420b050b4100c9902812000c101c180c1142180c4514280d8064140660b0411400080d003405407441500507800e40c0300043d000344030306d584030318025490b9100c0c52400440c890a15000807054082a049a1805512403002d58a01901624210f4048074100007981c1416 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 564986807 1250 564985557 564985601
    0x30b030c03010207061e0615050903210d0b1f08130b1009050108031305041a040504080d0e070b0f0a0e0907030e06070c0201140c0f0d0507030905180a 66
    0x3840030300040002600c00d61000801d03044601c408402200d1041003000c48921f409028804c3d401c02e2040c4040800c1a410080d440d03140103400039251090b9540c004000c01800e81da81607010f0346c4500a4541c40c407021406102c0380ca145018010b001440f0030619604010b2501842c8140c0d000d40304450f00700b03500300c100900b105002d80f1129131015050b0342c40c59020742c1c41c6004000f184464841c1d94090842440554917010081d944010644050302a42c0d1260f0b42e5188250700981d51140801000720014005201c01e24290034042c245801c00b07508681c40e0341c2012403000e400b01020035840103a0f4414642c480c1019040a54000d032a04001e0140050240c0280005501c2d0f540051151081b00d1035030340420285840080641000005000344051108001440c80142e8002806c50340800180700c225881c3c0f9a012200f40c6000300002c1851400e005440408014991010060031458000d03150401003e58540034010701c0c90501d10329094140e5204080703202e401258108800c0c2c0380e00490710840c08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 564988057 1250 564986807 564986809
    0x1020a171308070b04170f121014090907050409050610050f061909090905160512100e120a020d080702061905150a0f090e01090308010308070503070507060f120506010f030b030c 78
    0x5501103040035a500c0d03000b050701450148400c2407581d12401144241b2109ca04e40b4001014400d80e402510307210700030078000905013a0080150350004c201c001c205120130b210500b07026854880554146404001e080310104650420324104000803001801d0b01345410b40c64007504010b10a41403050007040070a5100103454011800381485041c0104040c00004110034211501003200da40300c0ea01a111446030203039010004100c8007201090660041803170404021078070b003000000e450300342a004c4049842001c1c0769000800705c604a00d940c54988441e1684001666180c0c000c8954014512500300044983c15980e040b0702d800140c1703940b8446840040c50000b4650f41142c0d041401200304c200d00c108144011070040c0000c07444002c0080005400d540ca000702010350501010b080303844001469010000100103c070081c035040b5040d40c01154a84000a1008103060791079000a0401150848841418403c09002d144161a6080741d40705010060300540043d0403095410301408081b1500c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 564989307 1250 564988057 564988103
    0x120f030c02060f18040911040f06031a090f06090c010c02010c1203051f051008060604090207050d080a020c060f060301020403080c0102030610080103030903060f0b0301020a171308070b04 82
    0x1003507000c040c401352a0320720403540d070851601c40031000e4031a5050803500300c0800c0410001010b0041b09540216904056070808000340c442c682c8028481c0c05183d2141d076001c002d080040f801140341800755001c070348640415581d60302003a1040c403070740c1d040311400c0f01081d802100343c0c8c00700c0d500c1070420110248154841c207655940e00c110020210352910200658100e01c120009021444950092005402c0101140c03181c4855445501485400c0e4042000c540d54001603500500303000c00155520b8502d840c002ea19205215000d03000301c0ca50b2001328005480301c8c000d840550303003600010300e070a03a516000c03100a100b014200301e0b0595801c101c00b20100722950000c03d0400c0100c0c0026a03241044400d008000ba0403c50010070000c0060042c00041d901c1085801200d400c4140030489402c00f0305180010444268526410f6200203280300400342c0160f02c1301c3e03030030203134220844059031410b40d02c55400e80d580c0402130541000b08480c3e40000d030380983d5250451302602a006600580016100ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 564990557 1250 564989307 564989317
    0x4020d0b03100c08070f050304170f190305010e160c060f020c01060f0503011e050601031404050d09081204050603040c0e1f0b1e0913050a02040302030610120f030c0206 74
    0x550980c48043d50b00300260001ca650382c00210380e290049401030341d200010014000a48028059061b04006105c81194401039880d81d8401014180e542d850b5800803c00d103011000c0b000c4c010030700705000003030040d114080044c0302d820403200c0d0322548204040c04540d0b04080e400225460380d075640c010b6606501d5132000d08220040ca400008250342403c0308400b915241da408184070340c2c10910424210407001258108450415001140c42e45407880140e0103442a0f0f015100410011010007007030203400100e4801848644c0c4800729020b407640201ca46914200000403480301c02004100401e013040401568024052840c00602c81c2e15a000a801200c050302c2d14402d10f08120340c12409140804c0b121130040082541c2da6150800290800d002c0c040d080080310b01e072032004220700304c40761120a49600d0b800ba040303100700140d15154064100079002800300307a01911410740010301c00385c0001c21481c1078801c222080e91001e000d0341c2d1401d40440318000c0480070070a04604041c0180c650101420f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 564991807 1250 564990557 564990583
    0xf060b0d0b03011d0d0f0e1e040c0921170301030302061b0307021b0103021306030204060e0103020405090c03130f03080a050a14041412030408070201080c0406080604020d0b03 77
    0x1180141c641000c250a441ca840d11481040507034580c055148100010180c0100040d4204110320034100e010691701c1aa2103a4850340010f901c40d08c00328814480d04600441c00001c59040000e2501e03007008032031162250281032071110703040d103460720191200c0142d54500340c4102600450b040d141d141000e040d80003a0f00c1140507034070a00500614108403121410071003220b1400d01d00b1440c0001d40255038900d81110352801d1007481c560009140d10a030110350307011324014000c0822503a00c2400400951181c880d600028124541c806030660dc64002c45c2c080b06c1c0010031400c15070f02c0d0042c45014039403011b4081250b0700c070108a02c10014054482e91040b07513010340c4410080789440d040c0401500e02c02010030100c285801807c042d556a1144c0303950b0865004110090240c042611075460a9110211808540400310412040142000060220754402c0c0c1e0f403000c080e20340c401c0300c00d4980034070f018400c0840e5a0304006061410194040c1440d00016907000c10f8003501c0d4000300c0d0400603101002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 564993057 1250 564991807 564991811
    0x7080301030227040807030c02042310060e090901180f02040f05040b1605040807180c0e06040b0c0109021c02150405130203060a0b0a020a1208060609040f060b0d 71
    0x1001940f820342815480d0740000180781840b0745480a090b103483d907006100410000b408940031050503c240c2000c0e824990281c000c10034210940d01001c505402da41c0c1d800010000700001603200c0c10b50030110012035a8513102d09090161000810800d504000c010a401c0e45da03c0188604681c0d003014558943c5000344000c816414060040c00291075096098400301404c0034188400210088441d50f8031a28030030005001c145500c0040b034440c4250350007415a0300c01e1101c08036030b45140308074aa502020904040044089541c2c0955801c03900d0401190b011000340810460b840b0614003e080e4552180c000041c068262b50000c2c10402c20381c242117015000c20100c04046003061514046d140c020302e41c200b0300340ba203000001050369039104150000c990f00400420072039103507a034003100504007000c10241c850303e140c0402940c0b220514010340f400700c030b550840c4282d18000d0034828060313003001e070545280c0709540003400040d180341080e00841c0c2d0b80c1c0d07040c009085001e010142c881c00203010300c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 564994307 1250 564993057 564993059
    0x10806061210060807030207020a05010c03090e0a0f0b041a010f2c03250504020f0403020a03050c0102160806010303110f07030c08101415010507080a230c0a1403040b07080301 77
    0x801843c000c030080499046c148104801005070740c0d5038100c281265003d20f0a9091443c441c54125980d80003548191420041c01c41401269007240c2c00c807130644041081e00300510280c50f030401c01a1008642c8120b40c1a4240c81c0030780c02c1e5482002040f09650180c2000240c24120b205801300503180100301c01c1c2d40b40100144920071345024088281441c500344900042243c102003444e007908030511605204a42c00110300351b02e280c0ea142620019500203100c0182d1554030308205441e0700d040b280150043c003035040c0403082c0c4000411801c041d202c2e264003d000036804d41e40c00b6180d25441f41c040c2c00081c0315408000e0010242042200060f6115005115005180083d603070700c0c000051b100c401c80b580c18000084060840070703140c0da0313001081c111195040c610079801a14a842055806017402000043c16195642c01c45240314402c041011440b59910401d02181c5260186aa9000c001d070045012400031928070200b0846595000782640e1405a0390100905958081c074001c070b40c10440800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 564995557 1250 564994307 564994319
    0x14012306092d0f010618060525051b090106090e0a06030f0c0501180621140129030106050d050601140a02010509011b1b030509041d100b01020309010806061210 70
    0xd43c580c0104094248000010110514502588828050340d42002004900b000e00303180e0002951105231500c00800600301d4080c2040c80d00e441410b0f11b01510405220701c007004a050050129040b2281c950311500900d090049203980308a014140071380f00c64603901c022001c0b807680301c05280040c1c4214459407072140f074a400540441c1c8102101c00704100b41420800000340c1200c01412840403c4e500c042d610141044040001e0071454045058000c220f800403c4400b000007088642d1301900300b0070000782144410710ba0881c8805d01504d4001903060200003022031242d00240d401010505100f0904e00c0c07005586880c50b002100b8000c0142e45440920882103001e2080c41c8c1c0380b4010f0034001202014220024003000c2e100801861441c2003980c0030030601d4840d4054409650004006206800704a100324245c01405406041c060144800842c3c051501d44a41c10703864a040c3c01032b5091030f82c2c1c1c13001034445800051a00b500104100715980e041e0448000c0c0d02d110b40100c08640021600f400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 564996807 1250 564995557 564995581
    0xb061602010822020f150309101803090e09010b031002090a0509060105040611190c0e091b210d080f1005010206010b0306040b0d14012306092d 63
    0x508100f82d20f80080d0f024103510b80081401d5100c0c0c0740c059801e00780582802c00402d048101b22264000c41e017101000f03001001001042d4188011102c000c2403000c00f5490b90011118505828001c001c04c40b400000c003c1141d854105e87c0e803107003a00c40006034803100c00300441e0405124405030714415500058403a5249482030f80c000141c4000e071100300b1149042c0002030031350f02c0345c6e005d20400c4c4011808100d40300e4404100213161002040d05000141c41c42d490513140685690154429820f00b071000192681e170300240d071459404042c0340c51001e025042c0140407031414601c800150035400714108000400e020859030300025200c1c2c0d08d40e0032626003150181101d50000d80708d040c1d000c401e11420401aa80000e240b070541d201080f40303d40d251500b20008004104403884140c216014503848028006112009030090050308024407013031192000600c150f0010320f042c80301d08007450002c0303400d504042140c0c981c408800c0b4200d80c6441d4050026004103010074044002089642c410801540029 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 564998057 1250 564996807 564996811
    0x1030f0e160513020c0d0302070804030f0f02150306010f031a06040e01080c0108130204050a0b030d0f18032f190609061731050601080d020a0c090504060b0616020108 73
    0x600340031800c2840700c080c269150b0828814450407d034020a0280500400e08202c60007151b000352040c1c0700201d40e15044010802c454426441520300a030320408510051040703c1c41418160f490104c1103031507500039401403084003420103250081010500450710350b0700c024006041074445005c000d41c5018120303498258003d030094104001c03801400b640013407408003a0803259048902003615612807600390006c0c10740c1442c0c0d03545445040020588550054544442104a999001080100060500c001031120b100003480180503590030010b001901010426080c400c141d001c04001583c0001010042101030703d4560b8880d001080200a0700320070804010b00300c5040100610200e0040201e400070010114000c0c1481c7c400b68840d88241e00204204469402d000d030f6000c5021410b2295584009020701030740761041f0a0f10400c80350001840c2c001841c2d2090701008554106040d801c0588009041241c1c085d446180d03d15440da01c000280411204001c6500305032441d90000500e00350300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 564999307 1250 564998057 564998089
    0xa1407090c051b03121803131d0108071206020304320c0f0616050c190519050904120915050306040b01080402091b0903010509160605040b0901030f0e1605 68
    0x801c0000d50314850301c510310a5400b06e003103030700107954504680c149030440c803c0f24a10990030341e0202c0701040824480c2c0f09504042000c00d0071001030307a00ea040043c1d8804480c082c94400309080150000010305540045074001c0c03240143c5007000702c240c02d1060b030b00480c036165001c0928403040d0452401d00100010100c4000440c3c11104100803807000c20050300c118100a4400c40540d0002d80600c0303010000d50210030341c060700b5042c04014440c42d08042a03241e020f4140301f25046c0c80000000b10303001000c0c0d0b0664400924401c090f48560340c0d58402c46c0d0400b081c64090101000c4005070318140d48229910011098403000d950b403510b0000c12080781d403039543c55414030001744140005a203c0381d20540d44034900000180090404c0090084113003d0f103a8030383c2d410b600300b1041060103074021689900d029243c070040e1184940350142500c1d540124083c04001e1101441410314541c803907005071549003003480000503040032400715241008070a02c1085030a98050300b0801c014200307558000b1742109 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 565000557 1250 564999307 564999313
    0x50606030d020d0c0305070305120109050907060519080619030b160c0c05011409040e0a1a0403050306040b0619020d090524071406040b0a05070f020a1407090c051b 72
    0x8900341e002c4d20f0b1690740c08001d804c100d40031500400701030050040f100742c507600c504841803c0da9a180e6a002501d002c840682d06806002000151180202d040d02c281c440b04031008401350741901000c031051302008005580c060f080c3c181c0c0c1d1003a403903074400840186002e952504494a004034040c07484650888071103080140200c03060000c15440e2003014260340c070901e407a182510600e52446c0c001d018100c0e14075441460080c0d24030b9a204002007030000308d40304038100700030030200b0486e10303038510300488002c1c020810820014480d807415900c5220003c80c010089400e11403501c031521070380d060703400041000d40d00c042c01040c0040e80003d0190020601200c3c0c0c41c190310069031741406070b40c0c20f9a9042c401d0300302c0482c109003080303000b00ca002e03440da400c84210352180c07920b81460071130400191454407440e031400300404c030894810070705121380c1c40700b81c0c00501a07034420307039178804e03074114500c1c0204030a009025011503206101d000d0000e00412581c0c4181c4c40b20501d6013054055010388401d090168 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 565001807 1250 565000557 565000573
    0xa0803030604060f1d09160f080d08040305070803040515040521090a030311010902040c0207090f0b060403200613060206090f071502120301150e0f15070609020d050606030d02 77
    0x6010140401028a96680d07805d099120003100320700e0710100302074810141d606403001180c0080d40d492400d048401c500d04407032001031061001d643c001016503015001490800000c4003007500c200042d40c00512030300844800780d001c1681c01c048140d041d1001c581c103402120ba03110409034a4020700c4080b45107058440e02e80040c0b440000d01009980c8030090602a04074601c4002c001c080d031107084183d40280c8144603c00400c000251241d20031f0054068070361900c2840e03424400e051144c40303101c04002e4a26441d0500315100d6400900401109042c40c45484050303048a898000250854511600284401504180f00a800c00030010001c501541c0141460303080c400002a102084641d0305007084d80424501504900f842c2441c13405840400b8000000513643e20300601248111126940e101300c407030068804c000100d58824003c075445240b503c1c0c52110a03035000010109130b44980360010343c10007280c6c046582840a04030540d91500038104028141c1414000d28003075280c0c0344080e160389 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 565003057 1250 565001807 565001819
    0xd0503090f010e0d110c09010303030212010909020d0b0919050303240d06540302100b01050d060314011506080712060801051807050604082a0a0803030604060f 70
    0x140504e40b0300d8200300301c1d8094070000005c0c0103101d003a0480d83c1c05443c2c0c2c9403642e1039040c050041c0d40000106038502b9a00c2000103151701d11071045005150307002313043c240c0702d0a1645801c050014054100300341350080d1221a45011146003214088034842c2014503120f16014900505591b15842055020410615040350a03943c0402c1081c1c0903921140014142042c041d0102e1080300b0100d80d0070840c0101c0d4001710600c012040007100b007100c4040c0e01c82c41e103150203c107200000d20300140280564040b080c10b455007040703030b08001325035481031401c83c1c200403c5004600c10360780030384e20644480a8151303039082c04c0c08003030162102001103d56481c92044c0340150003041501c004200c017082100e01c400c4040c5000c1e9a0304000003c01d1000000e0201d42080c000703075121400d0101c2d4215407440307402d40001d05401c100081d00c0494040c00302800c991184d0410782d0320481130040e000d440c4007040303224140070707941d81900030340103028694021516403600106000440750a900f2040718010940020854 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 565004307 1250 565003057 565003063
    0x30f0b0303091f0c021215070f02060a0b42090a12020102010b0d0506061801150e120109030c0317100302040e011506020a0506010e0f06060a110d0503090f010e 70
    0x142c4103200d0218460480c3c4003030443d0504001d010003980a015a2884205540002072400000340010001175040e15072030f500b0349550a01c000040d000d60040c40018510342d00da0b90005400103000b600b101c004040c51404545650f2003100c04020300d800364000d04000d41032914051640030705244017185003004602c000342d010780c0c0c5031281051121890400d8030842e4401c2d000b044105030041d1420a40500324901291212000ca52583c01645100c4843c0c082041414071716040307440e1700e254080041511201182c1c4034003900505a00329540701060400c95009206a0700781038040d607100d68403080b0600d001030105001d00315401c000300c880800c1c001904419902102100d80c103c80000b802c41e0b100f20000e001d42500281d06000d94210040050055004201d40c6900391086060311220781c0c0300c005074a404a419141d2100d01101200000d1240c10310100910240e062070030001c2241a000a41a02d025800d03010400014404400e02000040401c400800828100d00038044a00002000e60f9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 565005557 1250 565004307 565004329
    0x70f081f05061804060f03060b010c0b010909030c0803070e150a05030604020304140604060c030e21090d150f0b1819021b010b0f1801030b15090403030f0b030309 71
    0x100c10300001401c0691a8400c110b400c0180f0405041404216500c1c0e50307450740440c40d40301c00c0c1d62050603c0c40c101103540c4170784140803055500c003095860303136420401f40c0030050020440071814090303006684408900180051486120513540e030102d558041c8041c0004071980c4050070480c86014000d1001c125045010380b90700c02c10a640044e2690303694149244480101c03c0078071402d014000604c010b01150b13030440240523401e45c03002d100001d03140d4003499640c00c840040740044070345030348030040c000c2c502c030000d1807201001410a5442200790722203280c00145106214111607a4038802181d416090051002c52901241e285208040c3c10503503e8403042d0040588a0092804c0820301d45150a503050741c040d021400b50950605940c021043d008044403400710b48510b004000706241481e02041248c00e1540d02c001c1307080c41c1d91a564403683c403520003400081c5c035051040c80760815501c7d41030140303100d02e010327650210310610289003030302c202d9045491450081e081081110140c2d181d1621b801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 565006807 1250 565005557 565005559
    0x216081e12010902090d060e070501183209011202090123091b0a0201020418060b0d0c02070306090f0204062328030813060207060815030a0b070f081f05 67
    0x159a603440e1708000741ca003900301240148020701d0003001c1850890001a00e0060700c8081e203840c038a01c468150305280580301d030700ca101900100c20015244140c0c0651464100b1071a0351081c0c1112043d100c0080c04614090300401180c0300d41842c0181076180410b803540c01072040380d003904000f002c003411022100381d40060705400780d407840380490707214800c9400a071642141172080985506080380000e010394010710601c68117400712018910300503d140300f14012a096408550b00d40900210343c1806481c0401030f40c4150300540c180000440c006002e0001c605206050003400c0490910400040f2406500300e08125600c00e801c45444c404a0030300441e92590884d000d81c5004416020010008000319201d401d60090810000421044102404804140300c0001d60825100d00e81241e0302c803240d20400000800c48000302c0c04501c0301031848000203002a050b20b06c11030258680c1c8840036070507248000020400894180c40540c4040590740201100d41d0100c1c120040015214025105001e02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 565008057 1250 565006807 565006811
    0xa0c080c070b040c090501090212060316030f081c050915070f051e0a0504061d0303120603030c010c1d0f030a02150d060312030b04021608090102010216081e120109 72
    0x1260500c07613507104400090880c09020701840d1384840f0a48003039000781590180442d80c00d008181030346030108540b011542e40a82006042e440d5440c1d20842d4840448192400301003002041e40c1c0ca00b0b6041c000c1041550703054081503605010701490f2420b200c4a50815043e503085061005040e40442d02c90300c081c58520b809a180c0080c2c405000da400c000c13152045102070002280c80300076030070402920483c2d1707007906c5131f000780c1c02c48960012841c0065003420760300da04100110300d00010382c1c03050b041e040840a800c0324100310b5501c0c521030031102103200c240e010510302558807603452121a8038541e03041742078942c41c51801c0c910010a5641c0c1c40e41e20000e01c51004126011100d10b940c03030980d140c1819014050200541e281041c1c5003104201d207691380081e040200c070042e5030825008a0700320010010700940e520303640da11401ca140d00040d92941c11550204100d030401d03400c03d4005800140035210305c5030380341e40c0303092200090040300c259100d00080602c0000c440314400101c40f4112840304d400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 565009307 1250 565008057 565008061
    0x706112104111011191406040c1814070e0a05030307080d09030e031c020d0e010e010e131e05010509040f080a1404080a050601090b030c010e180405060a0c080c070b 72
    0x42560740840d0075815004071701c1140d141074403015a12055024141c0185290a0358454016010303071501c1d01128003401d4408007010230004070202290f140c01e4414065000660241c3e000b1141700030100643d440c2d40061000284000e042c03414007680f8000f010100d0013580341003015512003030716000e05060760001e10b5680d851081450b0040c136075030f030951100505444c241e501c3c14541902c40700620b01c80400502c01c0240f4540054013905060464820503110100c0c2440c0000044586219041010741c000c01d0f964280e40c0045030600403103000071172040d019640b030034910003043c00300e8205070700051003101d002d0144000b240f40c0c10590300200f17401003802650340c10002c400b501d551075540d01d80f2400d0580042c00094180000c12940600da104d04142e50716070f60317501401011b90304030350b00056068100c242003201030341c058550041130700b0010b004611001c91a5000001110003220240d410307070016020400744086603c2010345c500c40a00300072502e0b00f0242e10000741409185001400c2000d2400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 565010557 1250 565009307 565009339
    0x309020a050a060207090c0206040b060607030c1e0201120203040c0501051e120f0721022118070909030921060f02040f0e130b0c070611210411 63
    0x31108001d80300151900340400c1d501da03c001c1da180c13103502c14188814944801018020b20100d0540d0295030402c4290101d6114001002419030002608030b041c05680080034000942d4101a01d882c100445503003c407042660001400e11429616013850356403040040100007508680160309560084c40e00c907840d084441c031201c80300c1003524082c52a42d100818988020f0070204050303440f030f24401e0f0000310a51551031081e1070450004811000f10902c2ca50b48500b001d1032640507165403100b410070f8020f0b408540184042c1c0308402c3d0f44512800032140000310280e203040003a84014403443e00c04100320000d588000341a0351035800b802c0c1c540680b210300d07102100c000220510b0000d421500401900b018030300c03074130000e6100d4403428510125492000503161545000c1c030340304001c0089402119000340d5501c800f1504000c01200165800f8800d450226401307203d05e503008042e044081da0384504203148501d042c090b80444a00311025141008000741d614201103060000a648004800b16516 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 565011807 1250 565010557 565010569
    0x90f09090309170703110f090103030f0c021f02160b04152c0f060901050304150e07030308151c0209070509040f0501031a06010206130302030f0a05030609060307050d03030902 77
    0x15100041d04440000003640d461404141345084034428900052079900c007809020712101080c143e030354804a01401040440c3c040c90005800006c0752410b580583c43da43c5c00241c5c1e00c03040201d440442c42d0f088500c1c114060701049801d16001610300320040d010f00d041000c554078030682c010411140250003004c40c1c0703140190f0049e1180c1424030540e0030201002d00c01c0c401c001e035501031124403031403803c003010003a82040303401c88046d00c2c01a52490f156986544035417412104480c03900280c0c0b81c1d1030010032008901803004401a6200751390380f2000c2e080c14040c0c0380e51740ac034000d01207209000004007034042d424000d03000380740b00c3d6041d50960119a01d0410035103460103288038040e0083c0c2031048403411310701380d9801207040e44d1003070b00c80000030b40da00007906840c10743c210761722805039001c640071440050484c42c2402d443c40c460310440f0300d428800f040740300b1250024130481011610102c00d020003840c201074150b9002e50241d0040900c04c1c40d040004200000b5440050113156480003200306544900c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 565013057 1250 565011807 565011809
    0xa0b0c01091202060613020301080c0d02121504061a0619091e05190f0e0a020d0c0c0203010b010c2a05060403050c2403061002010209040c020d020c01090f09090309 72
    0x6004604910381008080d40314002105d00c50301c1341c51016a4880402c00f00d200752410b071038a02008119204a00301840642c501e0400280d03800380d8808444150090300b04a031b40d0602c04d580c030040c216401e0500e0300710240c0708540c08603d03079030381c000840d00440c0d2a401c0555102d500782401128480910180544102c0e10941114084080c4061003074950740c03514100740c040351001e0b1681140001d0030f114012100e01035003c1ca403003501001c1d608000202100e00880c1d0400c205442c0146010480100304045800c034110b10008108003807669000e40c80c0078410b1300980c4c41c00782001444803115036100c000300714506070300040207001210171001d039884452400b005000c0107413505560300c2c1c585c00c2c17155642c4103500c030b941c0c400c00071491103051089446400c10f5280710001c080d00d0035900e504080141c80404d1030b07400c108642d428445200c45685900800346480d440350040c0000509102000381003180c0004860305000011404104e555801c065a40440b180c5610005031442c2618003101c905000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 565014307 1250 565013057 565013063
    0x11706220e2d060f042307300b0631020c0d0906090308070f02090411010f050a050d051024020d0908060f190e0a1e020a0b0c0109 57
    0xa42c11507508000700e41184812070140350760380300010164682ca031555960086680d9160001040081000510242200564060424012140ea48081660520300911648070303800ba081c0b465500c00001e12214102c2e07034031440d0003001640808180c0c607802e041e070f1000361407a0300400b03800c03001190100024082ca04003ea2004410075040c120b44031040182d08040a07a041e2401058403034040140202e07521000ca50341a03e0b4183e1161552303d480f010790f00202c0044c0c0c0c0c0100812980b0006039070305100f42d8884d80c4a5910405a00c1e5500c000400040001484006028041018202c0035070068240e420a641000d004280f6a0303e000300c0c250460307020ba111001e448404101303800210307881d0b203c0c03c00b200826400c40e2040c18458100321102da01c0c5109464040e00000c020801410006080c5c96000a10381c0c10300c1548042101d42d82d08844095007a00240e0b00900607103020000c105405101000c0950458845c4288540000701d480300d8901c034030f168000d000a40c5804950084d003101e01900d030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 565015557 1250 565014307 565014313
    0xf060a1118121e0a0b131203090c0b0a170c0906041a0403080a0f0e0306060a06050912030d060315020309121b01060603050f100602100e0309030d0c02011706220e 71
    0x8541c41480d82d8584d25002d08450505078440000d40400052212405040d00704000c2e241c000411181076005020b061420340b0200c2c0e01d0800424000c06c07580080c095800c0641da00800300001181d0303003901201c054408010b51104008080040d40c5102c15503080d9070010711480700306508940d107000248190703070000703045401c04555070400e550442802c0c3c0e602c500d281c483e481102050000c0503101d0904446950780300a2070402408214854800f4144885d0080c001454190544940d2484c50704001c0700d240400782c55480c1401042910b20310842450201101981103091640c1c0c0305840d003c07910360908851074082000707100070442500c1410003007443c4c2c0082012507259203005000d040102c0b40c08a0301c1e01c02401140600003101140e10460310030f5030140481007040c02c12400030f08000101458507210901c50340055503011300c0320b00601e880da03840d0f9040340d04807072001610b6105000d08040b0f09801a1040040b507807a10f42c0700241c09040d45110084850b0700c200c462008000c0c0f00d043c400301d48 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 565016807 1250 565015557 565015603
    0x21b06040b21070513060c0203030a08041b091d03041d1b04080307060b0d2d02040f0b01031118010503040303020d0e1005131e02030f0f060a111812 65
    0x30342000c01401404c5a22a034041569206c01e003c0d22206440f0500035055807003000f0003018a4030400b00355401610031035481504140c0003545141c0300720b01b6049040802d41e00e500740792000100d04080c0d0320040d410702c003a506152800c04c28078920351070007400746820904c2d01c1c0080c030f004c0d14a02c0b541803007541002069841d50b44a85000d40e4a4010180883d0b050703140c041d040c1405c1c58814401d007001a400391203403c52070031045180d4503402148000001c1c00b00156200c03001030755103018100c001c020301c800005550781f6800c00141038460b1890164103528040001c4840e01829003d0913414031020f083c01a901d4039140b401300d00034030900701058941c6250880c4107464190105a0120b0046007580a01807500c80d20480c4002080c2010014400084c907100701003040e0b0682140058503000406407150381d0300c56101c041c00c0c80c0341c50602c02d410340c10900400468441602c02d044035801e10181180c01c001e0740c4e140070102800b420042e07500c2103000c108204440703541000030103084501623035012068 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 565018057 1250 565016807 565016821
    0x1103070305010212010f0e18010b040e010b0a0e0103080304111c060203040209010911311214161809080406020a140309012001091e03021b06040b21 65
    0xd40000c4004d4402e003412100028a80f20008004810744071400d0345202030740c89564140304a08807128103200305541321240f007ca150360f6803040c0e150b014400800450006038803820080d41020b142c00181d20a403182006001140b41041940c0d441980a0200d40001a2010014208201030004940146407181e61301c4108643c1d50055800742c0d00c2544c512000c0e98940242d1780941d90320251460032900184554500f80c4030702e103104402442380b503000100105440107150300307441c180d42000000210813003183c820043c01e04a1180020111009414079500c0c020328040c6102e07030b42c440e0b41d40700600c8449002c490078003940038200e1103038040103482e0b9550342c0d03090194559900b0403041c0d8210003801404903803800c001c801c4859421050751024640d0501c1c0c00e000140103001c824007161507580c0c00c40440020901122491115000c104a0003480d48070f1500074544292442c034055004003102c91840759840d00001d99041c0c0320344001b00d0b40ca54604106802c2740c221054101090440305c032003444a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 565019307 1250 565018057 565018061
    0xc0612060118030f0f060f050603100b010909020d1b020624011e0e0a06050408060403080c0403050307050a231b041e05041202060405030304200d061b0e010e0904110307030501 77
    0x200c41c03140d40300780011f05004400c18104c807800c0341d44a405401602000319071006035031200b801a041410142c9075503856406030012030700080070951009648034801c1c514804962440d0f01d04614034402001c50f45030441500040d000049054240c08408001c254016806207600e00e9011041c02e210000c5030f0090b40005000d41b115880c282d016459212020558510170002c440a0b90070400080c030031038545550860fa000001804031035550028400800081c1003031000b46001c500500c001c128040c0c0380d0070180e8181d0f803c031090382076550762000421b440341408504107140070081512812400e20000108000c0c1c4040146100030043c440008441e660a5610003405140590000604140b8203c0203a0381e800b400e81c0c001d84250b10600019001031580c0340310744861a2081c2802e007408014070701040e01801c0c050803c070f030510307101c240c51400c808103500203112586c824544a400348141e070340041c0400209140c0c05d801a00004001024800c1480501741c0b0080003404a810080e07580c141140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 565020557 1250 565019307 565019333
    0xd020a270608060307030327030c0f05040606050723030d020c0f12040303140901031508062401120f0219050c0d03060f060f120c09080c0612060118030f 67
    0x1250014000c03c1113401c0024201d41542d51545905407103c1c040e01d02c01c4859100c3d011158416000c0c4240400000c1c2d03644030900003000c07280d030a01f007070354144410041039a440750850b00403c141400720b0030200d15505a0722507041e00f082c038002c0103001200811402c5101d182008400c0c5400000d000c90281d00000d83d6503206000030050310300128103951040703d580f0a610000d0009200250000403850b254001821240c005040000b5130806019607400940115880800303a60000410015408804013007404401c9000170181c04110403140043c01002d03c000f064a91155900a1324030442e81c194101c5030398105143d407a2030701c50442e90004007140d00240c55070080c0c1c0940c070442c2840c0c6020740601002d0b1815071025214a505240c411102421844094030801000c0550000c00d81c8092007600d005c2c00c45a074441c2100c9050803445443d10034512241409800704101600b441d40c44580866040a002d01e0010721031048000c1640455500e90000740c00304805503180f008028a00220074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 565021807 1250 565020557 565020569
    0x9060b0c010506040203060609120f070603020a0e220b0d020913021215060f030109150204062c04020705030c0616170609040b0c120a0c0201050603120d020a27 70
    0x40b01c90350303c1c802840203030302060707400540000052008540034a007200d903503005044032404840940f0f22070f0a1451902c401a400100800d5000071141c0301194030130441050351000f175030100d09002d09c2074201002c210f004010134594a5681440b00f1959652440b0b403900190014000d035564244401d1035561120301580c100d115010780c18200e02e00400200326440c400c0425080ea540c2941c07200f0600c11201024620b440d81135596481000000d1400a01d00505130707881e03a0010b07281c609018000e8248615081c0c2c0036501c007030752013040300d800031748588000d1009000d40e000741e01c40303441d440c01502c0c60107003009a4080f409881c0400509620442c01d1060101050b90b95018841c07485040008541043c3c0e1029000761780200002c0128804a013010340100c00d4202c3c0c1071400b02d0056580d1030110080c0c4016204a0f00e640d82c060203035909018036608101c04501a040302080002c001d95503214030b602501d415500800c60411481c05a145801e40821110b0200304007000d802134041104a103004030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 565023057 1250 565021807 565021811
    0x2301090608091209151306090512061b2503030f02070503091210090312060902030603060103030c0804030b040f02040507051905250c0e07030b01050405060901030609060b0c01 77
    0x12100d00c101c1445001d81c0c1e0050240c242014090b1020703081da400048840d0308500b106180100c020100d100400d000011982c0c6050a00e040840003451219980d100500c80d00503082041d010050100c2c049401002400b1003c141001c1c24800c0103980c0202c050501400d00a0b407442c085604820050b005018841e035401c02440004c429a0300803401680f40290965200384820031a5080c45100103100e01d10383e4080328203800d000200e140c1078030220002100080c118000c00750580083d4080d03400600340b541415030461038454042550b038001440040c00300164014600c06102120003100d002c3d64025082840c14606420440d0340040b481404900031443d100000304503034402c809407100814180548903444c41c81e208100e81d03039040b1a04000025030301081c0b0f100b21104660304a170402d03224207007402140d0702c0c0032207400c100d0400030019005d1500b00081d24040707a901004440941d43e08071260350300d40300304d04012001030500c1e0f0000c0114924100002c42c80845c200090040c0503c84030007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 565024307 1250 565023057 565023059
    0x6040602060114100e061b010e0a29130303110a0327030203041a0d06032a0602030403150e010c0509040b061c0c120c2c01140a020106230109 62
    0x34040010241c3d0000400a401800d0315545d91a1400003040004030356060900700c00d220754a501c0c00c4942e40710031528550b0280c00005c0800104803483c3c3c130400c12040d1a203d00c030b03c80e004400c40c841c030300400786800c5040c10f4151600b014066071084803141040c1d00000d84039100140040e004040800c4038071110005019201c003c0d46210548405c2c0e158194040d40c180f9203004488501040c0c00c007036000c85000c4c01d0080c15504070103032003448001c500400c60301003c400d0078030b2040041c2d0856145107e0039860507206114142c0c0000884003200d40c000300c9951301640c40b00c01072000704280f0031000e455500700111030a5682d40702020b0841084121020004e40d120201040a2407040d0307000c044030300085460410702c090040d4054840d14086042240601601c03c4409013101c441540c3c000200c0c459180b010516011102283e103070000c25580780001da10b43c680064400070340500c20540314880011000c5166200b9009007008140401d50314100b01600c46225500c200c40300e515900003104408 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 565025557 1250 565024307 565024309
    0x20a0510020c04110c0a080706060e040503040303080712142409010b0d0908030a062102130c0201060b0406120e010504031b1109010315050603060c042306040602060114 74
    0xc180d4580461900140200c00ea902c0521016240350b824400b0108414488030003040b000b403000090052041c005643e4820b0b15140440485841c1c3d000003424079840820000082c400000f00c03410b0725010f003003000403603440300000c59400b040c50500b80021030030f1401d20310186030076080740d80c0a5030070350483c42107614402e00806004040040950b0348030f0300420042103403040900013851540c0d1038100c081104400e6446080a641c02070741c102202c181e49080411081e0700150211440940c6561004e1203443d403034000405520380900021519607a4680019a01e8000d502a0000344150030f82031351140d585020150103041044039448a00342084c0b0354064034181845202d01c1382d541a141c0350f128844507001030130720301060b2400b2038412010103100f90141d500c0d0581c40c1c2c020b52244010b62880b0b072004d100c1c402a079802520040c000d6014200380602880002c2c142c0701501c61050007034101c000c04054454000c5a080605500050001000b184455012810030706840c0f0f031441c503a60030403c1d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 565026807 1250 565025557 565025569
    0xc0806010f030e190c080304150306080c0f0f0307050a0b0d060e09120d0f050a020417010c1b030c0b0a0516020c0303040b2802030d060f050d060509030c070e0103020a05 74
    0x2070040d03600124041d103100da40c60b80d4620513807070040030861001d94941d0300d6035286501540103d55810741c40c0101412682d4107010f42d5014020000c0548000c58807480400c408444d9101203a00c81c11183e02940066242080303101b0040800030b00700c00344296640060162988141a41c0c4881030810b8800b16900d0005140d01d40201034000040ca4807640c0d14010408540100040d5000140c03981c0106080809d140140c2d802000d02c11070042c0d446140c41d10368039203108040b80412169041c80c3e400003500c0c0d00001c5014801d065860000b0400c10300c0e1500b25048d40310900010314800701c0c1c00512103c444258420743c800c0b10580400d40c920042d890742a40c0d02e180d07420485134507070700400040c815411400d02403c50a03101e1400d1960300f24181d003036100494960710440300140c0c4082010881303811503000e50303c01003200c03030740300709940c0d0074000800c1651495000141805445202107000300c0b2003041103a606244500070341702c8581c0c40b1180b07541c5000782840140d03c101007080c0c020495203044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 565028057 1250 565026807 565026821
    0x60e0609061b0a0c15260408090d0b040c080f06010e040f03090e040609230a02090606040b0304121d010c020d0c08011a031e06010909150c0806010f03 66
    0x41c0814105220121060014600c9000e0000280203a000300070001d03245100d0710740075207148840c013042c5030240e043c02084a0070300840c0c07180442d08907012240e03481507040e899400a40190f1745175038681d5143c000c206640150030005110b60720b078804010038010b002000c401644d0300081520a061007032440c1540ea60700a0284811759001000030600040c0c041d1212145241300317003000e921040c0d990700c04c40c520800c100c4094a02c180c40f04686000c021000191220400000d0f8900c3c18801e41103008980c0c0d003043d840000d001e13845100102c0c0403030782d071030050f20014669030300701c15500c5c03030306240010b1007030400315500d404a00c10f41c07039100307503c0503244048a01a40603500c03071316050711940800c10f110300014020740d0042c180c6440814189400e0145c0740c152a01c0d080310703070405449403091500e0480d0700f01038514132040c041e02d00024200c02064180c110380c07800501141c411601d0400d82c1803418002c2c02c0e5440710b0310300141e0410040e040704c0024428242601e034111406282541138050f1940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 565029307 1250 565028057 565028059
    0x180d1d0f0307060e15070b040308060108070903080c0708030415080c031308090f0613060e094b0108010b09041220010218030f01061503230f01060e0609 67
    0x840c82c000d0203024403400c201e9210910040c100c0540100102242c0c40907405200255101c0c0000300c104024183c000410540040c0c0a1030556098501034a0060048055000c002c01c4e0080c0010904a02c80040140001034111041035070b41e0389079900307020b2851301008560440270840c5640003800f920b0440c0c041c0c0707100301d8102c005240f00c504160b40b41c0701142e1054142e00d5108022070300a2550341c4442d8040c1006040071102c11400070304080014002e00c040c0d00720701348200070321010091860040b06a508242554a2002504090400c41403c0610421660380c0810026000120740503c164030300c2c0b4100e96040008028104e0309105008428104507005000704c0e0030f04424400062203000dd91801c104a05030592a0b01480320040b403d80e40480e079600361a060180c41c0b800c8501d010712207000481c65003030007003100d00d241c20070711403503050b41081d801d0500d41d441841c0c00022440e110446601d06100302c8100540c648502c0e0862102001c0c0039400000b800c0c0c40e1750101d14181482110007801e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 565030557 1250 565029307 565029313
    0x180c0c07091509020706020c070605370302070c0b030702030a11010c020a120201090b010b031b0c0606011805090a0507140a051603090806070206010614031509180d1d0f03 75
    0x20600103c1c401942c40404200d42440d03080006d03003040c074802d0100e5000b46ca41c03590744555803400b8031241c0c0a50100c0004401560002201e0390300801403d81d00ba8581e40c21301e0802580310900d47c00c2c1504106501e034001812003038004200081564044000d001d80c1c2255100c1d00458514281900d003201c40340b003003120150f4440d50f030201c085464500c45030a80d00b010f1001140740c0303000b81d0340e05401e42e0302030b0300089d821240402030001d4200c0c6c0407140311440151555841c24000803c00380740e600d030005001581446001c06030703201c0c0381e262005010b000e4071010f49202c1c0c0303e0134955504801000215441000109000c50b43c405103a2194211140012075994043c01c01801d034040107803c100c0b0110880074010755070400140c4143c244590340c4120300381c1d005000302e50714056025203402d06200a4007443d0030304104200210383c050510a1900a00f52920041569800c09400b20308402080c80980d41c40b442c0780702440b980c0d01107440c080d0300d181c0541030b41c02c014102d0140300307207001500c070b81c180c7c190 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 565031807 1250 565030557 565030559
    0xf01180503070201140c0109080d1a0112151a03040c05060a1d060412081309110301090504020f03100b0310050106080106080a020f0d061d061e180c0c070915 69
    0x140c407a15581c012040d20b02901880c0000009281f0708580c41100b08958040000c1000c2004007020311030b400344135015400c0f482c000032403100024000035880101100081e03035150140c417441c035000d025201600d502c103c2048400e11001c210422908219030032a0382544150000c038643c08c10100799000800b03180c0b107244240c115011100c0701171141d000034581040c018040018050784a640800c8210301030300c41c03250355035810a9031300b455014a80080504504001c10507079166040d0080301c0c11902034000002d89a1510710000d44c0c0e00b1080740842c0e516101d0fa2540c0e12058407554401040c1110072070494841100390307038684064490034400c0c80046540312004014260007461142e601c80c42c00b10006107040c0c00c201c001c4006401001310f002035503550b0901840380c1020718100b040700c0146e124011500d442c00300c001802d04100b9106003101c1c4101076030701d20150b0f2141b02124030b424060020100c41440d001c0711682e62a048070100c41043e02c11442e0008107606117100d5a0700030700e0300c82c1ea003020407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 565033057 1250 565031807 565031809
    0x50a0e0c040c0e090408040f060801050a0b0901020a14010506030708010b03032b05040b07080105030a050d0f030b120a11060414010e01210605031212040b09011503050f011805030702 80
    0x206200710180c0b0500101605420459440c00342c000d208a00c503420590311641091459441c2058a40100003401a5000181311541e02da124581c1181c0b03c2c0071074645c1e68041d610040381082e00c0088000d1074481400c4103c1100b032019044507100b07103801d40407100c0c2e05544050190907541088841d0380c0507001004600b00d601640340d40005070880900b81201004414002582200c0f41144d040d11100c0d4045d00380100780d40d01c614180d004140860003840403803842d40740c035600d500d0016241814041c03082a01c0e1441402508090b12a080051003840908401c034501c40d00c1d1010303141d04072900518051525070354074000f81520b042d41c8000a2020281da101801503030700d40103116146040c09644001d8000a10a41400007100d01d405032001c03900b24030700010306181510345c01c5d0744251004140444099030310703c0b40101d503220390803820308480364440966640c01050341c0303800c14010700d003808008001e000001800c8091600646c0080101c034080004145100c0400da000403c0c0b90010012a805 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 565034307 1250 565033057 565033061
    0x114090a0b0a0c120804120c05030d15170604110103060b0307050a0512090a110303181903141e0309061605152e05010c02010f02010f1e050a0e0c04 65
    0xc1d5149401d200000e00700d180c8030702084c0381104418000241460042108201c1c040c0314103e04154981080228030341c59603541520ba0007641c0c60180382e603640b1801c409003844129030301401441e4003c014400e42000311240303501ca00302107400b620290014902c0140c1035104c1d204000440d06070300300c15410b42c3c80e00d80c03040352140d1052900d2401c111007406080307078040d0841c018a0050f10110000c103a101070702e1400c0707a4070542d0445080c2c86500140481507071009a075019540c03102c403c40e600d6500310003020606a030840540c10141065240480c080a100d00001d400c2d103407440740441d0800d110368203c041a5513807140720380454100c11b040c407481c50a00011010102120302c220306440e94080d580300344140703000089614012003d00b450b00b0700403580c1843d8002c00d103078501c045510286411f1800107401d41036080002810410300c7d0f0264003655100303601c01c0da03500d40706640034081030700f03000e981143d4010074200360846140303881d0220b8081c0126100d0040c04000000c0908981c1a80f0300c00c203c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 565035557 1250 565034307 565034317
    0xd0c091e0303110c0415050f09071b030c050106080309090907080c040522050606040c02010b031b0a091103071b020108150a030503161109040c09091416050114090a0b 73
    0x710f84e204404c003040490f5698060790780725010141940c503950b407031300040125800403241140d01490f004001d2083c0301e9801162003101ca00c0e071000d41e82003180b040c507040b142402c0640e40a0825442d2040200f03a045000c001000241070480b01d800094480012141c2c8131131403882803c1c5d0607408038a10b25024142600095800019024087c1040c4500d01080d80050982c101c04c90b000e4001a00304945840c080c45000b180c2c03840e83c8000c10040d486600441d903281040610901200741312040080565643c10005003d0855100140421078030001361388400d820640d54070700030500c00b5601103a504207556807580f00030740503503070b60341e0640740c3c1c0b441c1301c6050941890310394200709190008004142c0402c01000500c0d0710b8041540144140c1c28080181d2008050840c41200d41500348030100310a9035202c000c4d0b0b0140c0701e00048006d16480c1442d041c1200001c0d10425020b80b076060315880580030140c038103d43e02a243e640e081c10244010801c0f511425007400e41c000e03a621401e002d031070030860241c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 565036807 1250 565035557 565035587
    0xb07030908120f07031e020d111605060703110a0e0a0b0a08040c17030a080603010209040518010e030c070306150b04230f1507170d0c091e0303 63
    0x365018141c1c881481c650b002c05006201d001104040c84084001c0a503a039511510901d000c1121910140d202448046100c461940071038000c900003040403502da02a40144070940443c039075690304240c040c500314404a2040c0c03020b0180d82c0009480500038001c0242810b00c401c035070391401c9440c0c074003a60914941008541c01114068010912081900040c012056541c031407554a2a003890701c1c0341400910740005048151404000700c4010002007600e0150805040807490740c1c0e01c00001c00e009000e90044958058203101c20f010145403030591803408042c1c01e800910001c1d5040360b200e681e91007450183c40c640d5225840400120300725a10840402c001402c0420a2035035402c0c41e2005074110b604100d52145076084680d940c900070b0700c5c04211b64082501e49550f203002c00400585840c0c1c415012104440001894000b04256142e0090841d0700d40e1803003a032182c4142d5442c030020101d241113000400c1040e04d002c1490054180040356028403845044802800e5580481d6a003110704464 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 565038057 1250 565036807 565036811
    0x100305180106091508070f1215050414060702010902090c07020105071524050a06110c1005210c0901031e110d060b09130e1e0a0311190b0703 62
    0xc04200c5000c0c02980c006000642011444040210304904141081e5100e4070072944200004c1102d2848010000111510180582503407440b0341400059120402c5403000c8291414041008200681369412094040c7c44125080c9568044050b82203418409006e58010400c8000905410401000b4480302e403040c5041401c000256544a04001c4031480c8a983c413a19074035080200421007004500c1c0d040074548008003e854240410600c0a00d0f01901003042240d18400d007030f04000f000028051580a020080c6480302c0440040c8160031104680c91084107884d840130401c05c1d005400c0303014180e2003000c5481c05e02300c080198014040c00710401591400c0c1c1851400c40300c03581c0b0400224442103c81559a88080b840c1442180c8030303a00400654034090044602ca83c4034450340e110619404480000e0b80706018041070714042d100151104204030340c02140e9050103011505102d414881d48598500c985501940c0c0e840320f1034001482e0111401c0344c05940410403440505810523480e00b40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 565039307 1250 565038057 565038091
    0x3040b07081527131e0309050d031e020c090108030703020c0607020d1e050d0504150e031204060302120108030717090a1508040b1b0d2c0a051506100305 67
    0x25040c0303508400c5071260703008074240c07805030284030721780030303c41c00d214003824000070b92803030326070380600000c25a000702d50155411050704410540031303215109151017008080c415038200703014001d43d29103002c080750f070084d0414000011119000410b440080790301d80c014100c1906000148000e6411081c81030340d002451846140104078804080207d00c03440406408102040303003809441c1c484d66080c0e800400c20100820010380b01c1404002c0c042d480e4618000c40b0701040b0b50700291418500080400716000001341c0040d40b107401d076005200142500e49110140c0e80d0301c201554684c0601803018120741e9080121146007282d08004040007c801000b03d5400342d01d0302072042d413601020148001080c0458103200c1400007014409074003010010380714500c1114200c40a50f2809150031804142d601d46001d01e00c2c0a526611440c081c103581d1045003109000950340703a82c0c40c03079803540036955401780708101d0000c1310501060310711a44015160540d00301c00508214002d090041a80a2140b040c8817 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 565040557 1250 565039307 565039369
    0x603400f0602130605180613051327110a030507030308190f0c020609010507020d11070b03091e0d0e0607060207060515040b0604120b101a03040b070815 67
    0x803d010300080d54030240c07280d1044409000c0c07506503440161060f401409500c41d880d01c10b03118041561015500c88515034045d107510000740003143c406010743d40844070380320291440b923401c2c4c2040500540c04940c000000b0000d0040070300540c0006482d54004050503c00b00e4010900a07170031804490306015107020010f07600044800381462200001c0e100e540c01c0904981c1000aa0303000900c520080045040844005e952041408054030074000e44804c1008419400d024802c02001c4640d5a01c1c0e59107001c101e00c0d621006505414804440401a03542800000240c6520034030741944860380108256000c104854010003070445200e07408010150000e091402000d0148041141c151622a040710800c0301740c41035040c4d03050081d14188810810b2600c1c000c01000459085800c810081e11400d04000121017190402e88074480c0b003841c4840c816585800540c07080e07000310002c094540722048112008032003581d0703c2001c408404001815454940c0309060180602452210a080020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 565041807 1250 565040557 565040587
    0x402010507060608160902090d0201031d0601080c12030c0c0f12012c010c390c031b080d030f0b150c010f0506060a0e010e0603400f0602 60
    0x60400c040701e8204403071060345a8102c8641c1c41c01b505440c802035082502c0b0340003055100083d00030280c101074462030070010101a015001100d50242e20907120550f0b11414200c0d60b8401c118019401001c506c20b010040000c0407093744c041e494407001401d0303441980d40030040e08071070360240b01d90310a01e190400030328201c09100340c9943c01c100c081825100303411004414243d48140b98948540c0e41003041841801c1d60000390b9401d042c14641e000f103c01c0c0360b120709196048081280c40301440042d0300e81c1c2c0f42400103941014044074458243d50310f0344c000010051400100501c05c8403210382c080c01c80e100c00079002c2e40000d0b400d5009450002111040f05000503101010340124440540c2700085070341e80c9110a024030a50440d14040501031404d102e004a406d0b480340071b441c00e041081c004900d800c078ae80310f141091410003008200130340303e08081d54a110002401b106a400d4000540b00b030054107500c0d40790001c140d615261540c8601f18458403100e0019014031030441b9426420046c0b002030720694 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 565043057 1250 565041807 565041809
    0x108120c10060e090c09130807050309090c1c0605090403030c14040b0c060a05070e0d1109160e1807052503020705010216080303010302010f1841040504020105070606 73
    0x2000b6100039083c13490004e0706102e882000c8900403020031082141070085003d8103078400c0e910080e1195603988604055040d4010f180c80c0950184000c001e03c84086007420140440740408440000586c50800700c04013110b40074421560015207030000a00880d01070b40c0a00e07600101e038200b0060541c130407009012142e11641013045414808282601e02440402000b68403a01e1904104800d0800c00e601820b24030358040c0c054480c010102800d010020170359090f42c140c0300c024009020340d06000041c8071800340c0108031a80003801070303422403000d490b1801c08500207000b45408c444840e2241d510403070302c6511100d034420303281c0800c00b0000d850300c6802500c46aa28000d80c0600300490500b00024200440e080300010400810740091006510210440741100d0382401c2c44610164448400d1f152001c502c0320010741004015800a0a6070740b0104101382d00c88054a1040100300704841c00c0d0341683ea185021603d03071000401c040e80d9052584c0840e1b00070b4014144a41010384075a0f5039401c0c3c91003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 565044307 1250 565043057 565043069
    0x6030c091f06080c0712050705160905070309020d030e031504050601090b060301031e020d0222110a020604140f0303150a150c0312200318060108120c1006 68
    0x7900e22580304100c1544000350140c2482d02c1d09860509142040d11401d0180180180c400000d0340e1403406600e000d08111890250b101e4142c8200320034801d0b001e2007180c0c01e8400c0080450900f00018041c601c00e20900030003d900420b00780c0f840915071000c40c0c07070350201603451381c243c4148003110419010561185114510610040c4140d40c100803c030005d07a980045014000d000500040c00040c4541010344498150038400e60405059400054030b80c124a00c2e01a410154500f85800d6040c000340a12650403442901070004a00e4401d04a246104450020340160042e5021600080c840000e002002503024100e80140300f44c0c51f04981194002e03a0701484501c4041800c505900300241c1c400d0040007050080c01840d1001c071000762a040540c00c6c001d08104108890400608060b44900010b03003214070048601702c2843c0c41e04001b41d10503034500388050707032640c020150103038001100c0b03050710384c05400307000403072412060001560041d2902d04024062504101165841031003a032009000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 565045557 1250 565044307 565044331
    0x61c15030809120c0109060c08120c070506010b2502030c1f093c080708010c030506060705030403080d0f020d0b0f1806120a02040608061b03040b0f06030c09 69
    0xb01420002402c48010385099180c100343c030b01002581c0c10180c0c0c0030840d0050304106110440d2454003130b52510586141107510502c101c00e00200040315030107801014032038011181d481e41c95034803c50042c0250f400031003150000c1090121448809a0200480761010301242d401c0c00c14500014840900c5080e41c1150007841ca6102c058a54482135403001040c001c1c900c1c011800a55540c072004500302603c0d10002051a000300121815042800009050000541d13148580341c144081c0605100c9041340c00103414040800d0035441d142045a0440e5030040c0118035061641d91800c0c1c09421400c00000c69a94a80c00c04015609034001030280500c141000075519804404000c0008020140e480c01004042c003440e18003001d2104c1183c0000d021a141d0380504940d4406500e000c00d8100f0094020b0b051060018041000040e81c5000e100310300501c03560303161461038004441c00105c4001d000c1d0f10141d404a10b00c192481519600300901905032244000040080b40d01603000b500c240c510030b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 565046807 1250 565045557 565045567
    0x402090303070506070c021305131101020c0d0309061d030a06110d1103010501090b030403080f150604030b010f060f02150c0405090907080f01020403021e0a0f0e04050106050a05061c150308 83
    0x100d003030003452039698902102008941080d0315000cac815480e1120040c02080032956190b81070303008100d9007804040003040b0340e1200100d403400410200e03075403007054003050081c0c45a940c1082c0219220344440c001030018101880c1c40e0300d803800901803240c00760b10004c00c200314113807690341540144010300c00310a864599951420780014401b80c526071051105000500c18400042d6200c2c0e480f41d000400f03403007030491a80700c40c0078041091014005a6501240c0007a0000c200680b022019048504240c4401088c0e070f6101002d1710703803480c0070103003600503049200e58031100d019002000780c03c644085009030500b0340b0345001c20b0420b1000e0b01c803446036902c41601004244010805410b110440314025800d207031655020444102c450034001c484c00025100765016511031807400001042074150482040391344070084103c490f429103041e5015420301d4000f140070309101c03070005d04840003c0d01e040d140c18030b80b4071034804040d283e07641c0f0507541e03840c0c81c111a003181079407040c100036602502a10b0b0b952 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 565048057 1250 565046807 565046809
    0x3071404030f12080c0d1d0123090d02100e03070221010c1404050d11030105040c03051011030c0d0905240a0e12131d16030b09060402090303070506070c02 68
    0x20140d409003e00400502038100803043c00c080b8252681205d0011011034000061003101c410a81d0b0078a81d100550f01e04500f0303c41c88845046c003080442504c2c4801d6107282c5451301a20346501da5030030601c0160340300e04100c00581c2030680c001030112400505490500d41c1641c00a60f00641c00090305000740e2301038220900b074503400e09c54102a4880c1b4184070b00c444000c0004c0c0709581c02503106051064004034040e0303052200070000c4109500c4c00030020010303440e00d45021051550240400d49242c4103055a05406010601c40c21507070085120800c1d041d0740d5403408014041c1d0213640f102e06215218440600080c408000102403010100e070a40060050642d4104058000401030204982401c03030500c4000130205e26106420050645a03550380540901c02c07941074020350118001c030203124401e003001e10403140038a000708030076902c131740d0a0940440220140c4400c900ca480d445460300001c10900d1400d64024000583c01802380e9003821443e450fa6814014110b86e00000b04600000203021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 565049307 1250 565048057 565048073
    0x50a122417010b01201023011203020303040b130209010602070810061d1f0b21061503100306020f2808040f08070204050a09110a081203071404030f 65
    0x14580148000c20110f5100000201400145500281c60b0000005c0d12180c90780144a0480604414071050009200103034a001038604209012400403040c3d00002c80c04102c001040032046415500542c2103803141d80b030341d1540e0f030b102920804041480c50b00440040e111000f00c4c1d4001c0010390041d0010130b18242a20b0b040c04000311450703602a280038000d000f560404030724600c0010f0400f0082e111aa91a01c200c8a6604e0034403d928680e8405100010300080d81001410401c4d94451660030342d2182444e0401454000d0b6019540416041c01440d40380d40ba00c8007559100c00c070340d15184070069032904d40d07204136400041d00c0708403070400040240c20340c5d440200e000c0810701c501561040040241100030440318002e40002c04441c80c50268800740041a41a01d0025400600c1080703542000d80c0c4840c01403403041c84c1201e1010300146100d00b2468644106c1e01100ca00c40c0103400341d03d00024101e0410f5000400c00030a01480c10a40311483e404140900059441641c800d100701d451400c3ca084 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 565050557 1250 565049307 565049339
    0x4030611071e1e05030d0b060c190c0b0705031e0f04090b120f1209040902130c03061517040c030c1d011509032003060a0b12060106050a1224 62
    0x50889000343d40300f000540f0020444002098000d8006400070b20f130310010740a0b1003164284071072480f5a0511400c2201010711002c4080c0c4590b034101d0030750b0340d00c042010031809010f1020f0950f4109004a03040c04c0c000100e482240075a02541030326140c420007049070b0541094104151a0b65a02c103e2051410408000011004190010844144002000d559a4612081c5040c2d51780700403c00e03402039101c680014034034070b60041c03220340359440d1403080a006084240c1e41c48002401c2900009980290021641c25511940d031a0300003020300c0000d844003ca400b6104585240801c1d50020114164242d07080280c011030400c07610340441d0001d807a281c00410f801500c1c089503500440c0886039080055007080300d50128070700c80d80d81412201741105010b5201c00d59014001e034010020703104000d501c1f80c4c0302044e040799401a00441d0540250b500c0000b40507500110f2420402c2d960000c0c00b0303041c40007885135520000f0521080e10001030341c000004a0700001e52500644c030a000c0951101032102c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 565051807 1250 565050557 565050593
    0x30201140402030c010f0c0515061e090c0a0c20100e0109060f02031b160914010e040c080f0102190206040b040b1905041a1b04030611071e 61
    0xc0824207280c0c00080d240c090000e216414400355001060015024408105039103030008240c41c4840289000104442822207a1500c00c02c2c0d403241e05a52540d0100041c1c050f850050300000c042d98802140c1034455004400c2c507418405141441c0d000940400e4030f15414000082a145a0744056170500504402c1a1845400c5c03100c18401185a41da21188600c11180303646800c00040ea80c03034205908501c034647c005441c0ca420100c2e2040800c07000250034032015960701400070401e0b80e40d10a03c049a85903103001c06407404d810010086600c070090034a030068041e0400900c92039643e420b06103040c09041e42030304103075000f0848010110010b1034459803101d17540080c0800e881c091b076840c0d02c85000148010580990080407556241650503003260074a1108801c03c65420302c4d041c5080c026402030078104a54040c140080d000050040755100c90000a0001c9810076056540380000b501a8041c1d01c410f0380000c2c003110b00442e0a031007003204203c2482448a0000311581800b42c01d4026480d461 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 565053057 1250 565051807 565051841
    0x21150613180b07140906031302060a0906081305031e0c06011d22031116030309030b0109021312020102010f050c120a1a01050c161d0a0c0509090604060b031003030201 73
    0x80c07662410550105d400c420412901e580e529030780c1032462901000c607564080e40210010074040c7d8000d41260039101951160784505a19075681d00810709000100d080040c03181d0020b211041d1404510121032020032071581243c0e0600550211440c82c00c8401d034002c00d00da2911064032074084c0b100500341d5400803800c20386030848a19900c0001d2011170204002000c00c4440c0945c2c0328500070600c800380d0000c0d500d0141c1c880c1d560350390500612814807404191034965000f8000600c485052080302c1c01648000c4001400c02d00d8211200798004c08424164155502c524800d18410f03010b1003001d105982922036543c075a083c415200d01c444a008152200c994030b03040d529210000141d414164001302464400d644020885185042015600082080180289010070301da80040ba04410850700300d45421500e5541c1070051040e100941d407150040386d41040842c21074100340c3c0c50b05034400e10280011422654486040120741e03c102c880d00d42104c1507200c18400c142d828041c402c4410901404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 565054307 1250 565053057 565053077
    0x7060f0512040b060a080706170f25050d06090905100b0303040b0c0f0709022515052203051309110f09030a050d0c0221150613180b07 59
    0x1041ca4500300281018065640e1100082c4035036546250341c002415901c003c0c0e81505541700301c0a048020303c403000300d42420000000480c0c8982c042c6159202c0c1000009402e195040c214010080c800c410004104000c0b042003102e0b0951a0350140c1c2c0018596040002100030360390821a082104401001c18088d0501c4201c1216640000c16101950b402041c643da80d030349800701940c42d151112402d101c550051030b2001540d0000d0340e015100c40541e443c61141004640321244001c040340715002440e440941c0f160850314805a407119503c8200d400802c00000212400e031503c0030010101240041c5001540e8550b420700544004011710020009100c0041000d80c2c8007000d014691424400101c0030030340100070791f000c100c100407c1c0e800c0340c1501c0000482d610300400412004005900a5040d00c08030305150b8148071a0b00d010000311000740040180c2c2188030340400c00081d180d642c0c4010400c403420b0000c1454801c4140c00e8541c1d00d0402c500c1012490403045030103004000f501130000702030f1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 565055557 1250 565054307 565054327
    0x20610050103150e270109170301060f200a0b06120705031c05040506180a050607020d061d0d03060905070504030c0303030e030409020f0c060604020906090f0612070207060f05 77
    0x3966000b0b84040441d8013003981d4a802c0580d100b2200d003c4003012400c0201d0340c0c01c4009006502c0819002d00541140760403100c405454062031100b0f10841c000100b6556549004c288113914008201210820200c0c4441c510100986012f081d03d07000d541500102d01031013210318105071201c4010802c0c1028142c50b40c60a00026202c80d0300d25602c260b40903100c40c00d5264644a0070445014100c01000c0c41d46401100508803440d000b11030800d030151030801d00c04940c600d403110aa0f031030550f000308620f82e22241135442c90080c16009410703a142500481404403185414402c10302440c0a681d4002a07081c0350003040b40c05c5d80d80c00b4004c51f050010400060011400a900c0042030766054200425001c000304401c600e907124581c040b00740c0c14800b042c4960600040d01c01044070011540c2100d81e191500b004010481c0b1880088c2e0790701c010100039441c0b03982450162941c0103a001802c141c1420744c80400e80d03500d068200d42c0c040050b04213010611541da00003812070904941441c1c62410402840c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 565056807 1250 565055557 565055591
    0xa1506122f09060d0c0c060e011b05180406060e030613050c06030c0d09030e0306060102010b06090f03010e0f070302100809030f090d14030c0124030308061206010303020610050103 79
    0x200c0c0c12003842000420b00e07010380f20001282c40c00558a44204091604503c0c0108000c03040c410840340b4508051000300300e540c05010b205181d0b4000564546050240c0c071050320300780d03c90800001c64000f900c2180c1d0741030b6568402c7c0f47c020907080c2c841c070a648040d6003c01d0308002004000c489020012003202c004100c00060344414490b05444040e500c1d10b0301c02c00170f90705004070390441001c103045c88400c1c0c0c10103034061510504a441a0103c074059111607006900b40d0faa032041c0c664103c10240f0101540d45860004060404405800062030030140c1c2d00590030131190000444213580540300410440c01d003440f030400f05c007c840c40e05655074140140c80355217034030074098000d00c20540411f004a1a42e40c55020301d9145070321100f0750028106c4940e19a8594100b40c0c0795509035483d094410005a80000050502c0750108118203003850455030241d5003014040d0071190040000b0118100d10f0f50704100040c0650b000f5002080c1d0b9290043c900070303011720030f42c0000741050b0801c01c894110030019 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 565058057 1250 565056807 565056881
    0x3060f08071401030510030b010b07021e0108160302040305071e0b03070f0807140d090506090a1e051204090b1e130507020c06220503010c090306050a150612 69
    0x91134007283c01d4032403c014161101c0c1c41d0f00068503440e410400098007040b040c2c004c0c884940309554040d0701c058a58010b0000c85c03529007002d804145864006001c40c501d48240101c0460107003001410301c3d48035101c0b50b00c1c0401c0c50304038003001240c0d40c20440300034810440d058001d192100c90300c4c2c650314000c50024090301b0450080e2051241c01004036981c14040c241d4200c1c68030064481171346a101000c1d000014100805040d2190301400007c685410008909120580c0c4c000b543c061000c030386200400d0200800d10310940c0c1c1d600500c019201c24011500c0108010103030303540b01140003410780c000c02c444040b51880003070100142105a4480d5240c0202c1001c1941c1000c1000401da510207000b1381c00c0c00610200e10358881e40000e581070341451011242c8605000610104440948800504d07088508014000003c0b40c0c9400b4100300144031508504c0d4062106900403035100909501c549030020b941d0881008603000e00c40c84085240940306200e540f5040042c40d2382c0c90161281c03a82c440c4144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 565059307 1250 565058057 565058059
    0x90d030c050a17070308060102062211190609050d02090c0d06080102031602070f0501020604140c0a15081005060406050c12030a0e06070302280e0d0303060f080714 72
    0x441203124061150521204035100d42042e900e403804a410070000810350b00c4400c00310007103412540803814035480020400e109110201110007131030070403000840070b907401140c2203501d403014809581094441e6400b200381035118600541c03d40b414800b0161416005812050040c0b40d0701c04644013580c2c804050680112520001d240e54480c1200014060121500003400640c000014042500009141011380e031601f542a03914403a2580781c180c00d60000b6100d020300690080780840d0100e1040d0203c80c045004000485140c1903514000c039404141562081a900740000c12014004e908901542c1d0300c003511135a1900e0031410040040d460b03000c0c90062004101c408034100c07005003020001d101da011400031507180c8031301c0c1442908014000303591040c5810700400b00860720b0a03000e4003e44021410b245900340007040a141280c1d8110f0100503a40c040001d010285801c0d82c499219241116000c3c0d500850840e0800001c0e0141c1201907110000a52040d001003007003401d00040c0c55000c8070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 565060557 1250 565059307 565059317
    0xb010e0607030201020904140901060503150423070e16210b040f0213060e0105131401051b06180f030403020607030c021c0501140105180711030a08010f0b090d03 71
    0x1d0281012802400395402058002d840e0018800420030b003030680c144a0041c2100a00c400b58072a02895141c8903082200d00c1511110300200340040c0c0ea07925045400b50101140724542500c00b11030b640740c50720aa0103d428840b81c202401900340141d04044840115802c01028009020035100320f050103801d4810b00880c0e86040d0392150380d45d140c0001c0da690b103000b5015501d80b501002040c50020540c03080a012411110011401cbe50103201a1001c4030741d0380c80800c0b8090300d05441d140210a000b10400c1c100301c001c002d8100001d040c103445003110711114006002900e40440880a92302c90340300c689901da03203c803031000400d820000813071b420342c1d03810f80301d00ba122180b0f0320301610b2107003000000075070211031240c0080c80190310559101e2141d0081009104540c091000d82c0540a001e000b01904840441c2580314065040a0300380d400c95043c5c60031200b0f112610310390504641000b4402800501c5030001000f00340c880344210409060030841c0145083c0d030b10b0002401e0440e61102c001c040c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 565061807 1250 565060557 565060567
    0xa11060c1f0513081e0c0d03020d060618030602030403090e16110c03070902090303310509042d0c09140906011419051504030209090715111c0e130b010e06 68
    0x482c505c240c8050300c0400040320740906920a01a010303410224002034a54980500040c01d184100500d0701c00b0302e042442c246006007552100c001a500052080d8117003c0709000c0051100c0340e6550041c49106101580c1c81104e5640200030702da28000d0514480d240d110400503032203a07030041742107400c0342c9075208016960b80030300000c40e066000d0806603c120707490851111300c0c4c594810b4000d190803d10703880194101c0761140c00b000403541c015500542070b0b55903a031284200c0b1000e550350043c2050040541c088017946641c0304070211000da00002c07401519080c0711260104a00351594124000b2000b41140f07604102090000d001e8509089104e1a155103920b80416071881001014043c090080c241d00900d0010081c220307441440308034000d568103000100f100314040340b40c03c156403500c19501204440410200d400d141c03034001c0c02e8030a0007050010101a1a9070618281c402c405171103044001400208105480c3c0300d1000d000029420702e0000c1c41c0e03a81e803104011844072000c980094541c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 565063057 1250 565061807 565061857
    0xa05090616030e031b12070f030f0e2809021c1509020a0503012303060105010f050c010213050f01020303092104090510090c02010606020a11060c1f051308 68
    0x2500f4030140703080c500d00001943ea00303403890200307041d2500e00f1000201c3e01007450307420100c001407041d80000307030840c1c5171038101c0000240700740046030980c3c40c5c0d843e0080d01a041f003c000303076442d036180d603200f00390500700c225410700345502452050003000603d80c11414a060118043c000c02e042640150b4542e69514451105481032180c140241c104018219155003240f040500300307910a00170318841c030a07110020114039620700303011003040002902924680c0d1030000150350b0310011a1024061003003d0080c2140785a091001c0d241c01c62240041601e560714201c00c2c40311040d801c50545045410400400104c07820018100560050040e5403103005021105410301a009540201403410304100c24414484440d050b8a42a030791011810012241b020f501030f82265860721943d000f503086a00320ba40411102c0d0003e8840b03400240c8407914000c61941054200340707041c01000740c0c900900c2000001551203214031540302c1440d01d21542110b0103900c0e460740c80d0240c8240e80302c2020400c0084108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 565064307 1250 565063057 565063061
    0x5160918020f070302010506040621031805101d04020301030c141807110c0a06140306030a020a030506042108010311030f0d02070501120516360e0a0509061603 70
    0x9110b03030301660356403a40001c1c60002e029101c20b03900356100d54103001010030120171202840c012071244071a485003803042554155903504844212094182d844440010340d0744550310031491a554559440c0c1c5400040480e1203104c590140d4114003c9105000600005038240884400c0e1f8998400035031002c0700000004100507003a5503006400003046080c41544e030781000c0407400c007078100c4043e501942c80090034006a004248110400688400194030b1101c0b003035030040d6040790010307040d11102411074020840003039187d0702c21602d981c410020481801858201c03a0108040008551100b031040c0750010300506060001426000411403080300c550b800b044140703c20411003003910120081303c41d020b52515040d12800d8041208031090210015040c800c1922440d0440001c042082000c40700300c1d0f1000080316074000c0f1030300006040b01c41b2859104000300940c0c0d22030000460034180640c02400150180c0311001003030400050102402010550356072001c48030311800d4201c5804101140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 565065557 1250 565064307 565064317
    0xb0a110f0d0603082a0c01080a0b060403050604030512090a050601051e0a0906140306060907051318050a0e0a0b060909030403021806040c140d05040602040e070c03030516091802 78
    0x105644d000200a801c04001c00c003209505403400f0b02c005624100c02d05a5522062202c840600081000000401c0c0059903401444411406065281429207039520545485800c0e60140c000c0b0303c0110300900583c1c0344d0f800d42a80004c41034050248070300309580b46591100d060040d6403240210350041c60301044410485401950001c242c8a05982c0e6111040010b0080d4046c0494505100b109065203040001b07440b806281c02900c000030550b6264004c40700364000c01e14484044400381c1c0d001030542c0d83d68401c038041e245040000101350a103007480340201c1e440607019180c55001100c0d0301004c6060a541207a202000351040b05490f0340e103c0c182030075441141c2000b5841908400d0400c0d0700f41c0d10706c2c0e0302480380e50150f80030840041c2111069400504000341c81680c074004014a007144c0025401907a0042d00c103882c05401e15854500c03081942c10b04403602000564000c400b07409055060041940210800d440b201400403a6803006010354081e01560b444100c00d4454a6110304469048807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 565066807 1250 565065557 565065563
    0x20702031009120504030503030c1b06010f50040f14060301050f0c09010302040f080a02010225170a061112060307060e040906090506090a0b0a110f0d0603 68
    0x2407081c6480008010090030301036826108110904000c00d0764900510450b070590307421400850565860b00c0381e0303420070303804070740104440c1340e0f0068410300c00d00c007c20803e8064418100081c40403800c0022034401086503850240000c112656112070030150600301d0307803150419548940074a0300c40390f0b0440c1d1000e5040c40c4d064100d844c2003600e22544400340d12401043c4551140c8000c00d40700d58080600741c0f6402c0d103000c0032105c607410118030200b49c2e42009014100041c1005802d01c1e03a2007110301d8517000545d01168994211030320740d00845da81403210003911031240799443c8a0030300d084042c0d821070010340906d000e05402e000d1960700d914420002ca074a4164805d00620650302c607940c44000680100c0340701044400800d02140091070041031030780956031b00d50345100009441d5402c0101506d07440a0560b58030ba510495140070034418002c8510848201c0c009020032030b641d141403580c02e00010b1007100030500d45411a00700c4914041154900c829058203d52940a00301881c4003e1040794001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 565068057 1250 565066807 565066813
    0x90606060a121a03060114040506180f070c08030115030b0a030b0105010c02030f0d02010b031203090604031d030f0f0c011b02092e03031b02130c021e01060509160206040303050a02070203 82
    0x40c410201900c80c2200c091f0540302032085880e0075091243c68080b05c42e195401211032800290b211441c410b1082e40100c05241100d105000c07511558071680c002e0b00606103104521a500c3c184580601941c40c00c41d42c143c51490340645581c4421040c03400c18054103042006040c800303410355408008600b00403102400703860b48400f041d10040d0080c100d852056010b406500b8010039003074116000d0341d04c20080c02018221a50310359030b04903102401e01d18418035403074090320b403a00b9036101080142c242c1006100100550080e243c9603900d4044000309035030401001c1c000c018601e02d00a0000810980d0507144000310f910b030034000444900d80f550319492413804a0300004042030000c2001411039001e6207540103103c00c800045a214040118080d4220303c0300d540b80120114141d021100c2c21741c042c0b05070f0302d40c41c6e0380040d030300c1c504102c0054030740e181e039110030781030013585402d5503095081a84c5000913a50788000c901c2c06500d0390001880078061554520000d00981019011030b89210b50040075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 565069307 1250 565068057 565068059
    0x6030a02010e0409080c3a0e01030906020d050103200109120807021504030204060f14011d130902040605010f0f0c050a0f050a05100c140306060d060b03090606060a121a030601 77
    0x45641d1fa002044a0754a402032044142030760750030314103072140981c9085e03401c808222105031090300d000201085040c101941c8101e00004203c091001c0c00c0302c110a0701000c1029450b5060050484055100100312802c6000a00456a0f0083c480c4401c54020740560107480c0b5050425001071f005944000c0d4003c5e41c0309001c6180329100c40001e1060b0b84c800c450400a103a1520b04522440c034040c0100301e441085954030403015800f541c06000c3c50351044588000001405000c15118402c072081070f07295644030120401180391038041c400c05840203190a081c10900b80400900c00700039141c0c038000344450203001605011050041444058200e03c0005034030740c5900d07102d6514440d0100c240c031540110407012403003030704030301501c4085e010a40c1c8049041038245808000b5510160640350321004c104040803070a042c50040300010500090410b880703190404c50325003040c40051045102c0c6070200030802415403c0200c041c3c04005070000000c440c25803513504e61040904c07024107a4184a00d0f40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 565070557 1250 565069307 565069327
    0x121b030708040506090d092601020d060306060b0315060304080403060c0509040e06010e01051002100e0d14281b23060f0f0702160f061706030a02010e040908 69
    0x590703240918800e004070341c125580d4800d00c6407207440d00151200000c00c10740301000200b0081c40e05642d1020180c070002243d10340c0700241422a8401c803040c50030192520744c1081030040307500c5044010b01c0c0f59105c8518620700340c440d469464480107401440303104040003050600c02c00405940c050340d841601000000040340b405000c13030b0080c40800d4803640c24020201ea9001000c030342141240d03c1003040a00c940d00b00300402c00c900f01030000c1c43d0210b2190203c10480400340307000340c002200311400038013800b008600c801032540b404918203041c2d4001c10030011001c4c915100400240020448160400d910780840484801d8000901100c105004060003024014040c3d19000b0000d010745031740c8906682c6000440d250fa904484640815085a0025104400b018003540d880742c110310540340110700d0b5040c40b84102c1c038a40c0200e203141408140030300680340c0062036181d0050f4580240001840d00d080002e41d14507001a00030b040203a0f2504001c22a1140e8018820300e9501034400381d16440242 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 565071807 1250 565070557 565070567
    0x615010c030207030804181a180a020909010b040302150406020c040915050708091006180902010212040e070306060c080d1a1201050f06012c030304030b15010201050a060506121b0307 80
    0x40030610300601e4105140c0f44808c2d043e40303014510070003a02c29500440c0215480c5840c0701c00402c0558019020000002a9600d000e019800b0748808030005459600394014040340c014a0200100c00c40c6d010441407102d00c0c0c00042c0b0488030b407011200480c080d0200e00c0c0000540485034003610070507091005004860350000910703485118004215140c1100000e1040c0656440340300700d0841c1900c1403d040c00b0b00300c1c10b401030620580180101c50400240d0190511039a006600c950440d08000c2c040c400c083d41d05000e81801020903107231954800c2130036281d002c010312460700c040c48401c0da1241d44e501903403090030403488500d01c024074040a0700000c070b02c564041e100448161407000303e580c1c002500c960048640c5a2a031203951000b8000f09a11020410705065000320b42c4d03818070007400000009000580400e2041600071811141e031002c190000e42941c201410540059003006810b1110391109030a451042070400903065143c0c84241d01203c000c14003e40352010b0300b10000c200507096800c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 565073057 1250 565071807 565071839
    0x90c260c12190e010b011202070c0e0f04110103060b0307120f021303140a0320030418020a02010e0f120a05070c031a07030e1032070e030615010c030207030804 70
    0x3410301400808403040d0f0050880798804143e6020400c10400f1224030f0032242e024145880c4600c85c014982070b1592030003c02c10008072110410700c14940100420410549900000aa000c0c201031041a0802c1050a401c4c04001c01c0700c4204100c0c00700001d404506138100036140c00d892041150340e1118100d501050501c14001030720319070b101123650031400b013002683c218540e030143e49082a42c0351105100c0c4224152a0800f01d0b035100c10700001c116901d407240460610b05001e000103960700341860020f800e45500c00e5003000c1c0c1d60010114031034481d40105070a49001702e01410907507200c2c7c0300c01c0c060b200e80c003590038060300c5c004c803030030001c010007614400001000c043d200700c60328196500c80e4110b090744d1380100440307010307003140700030380c0426040e500070400d0300303001c809011a107080c1d080c0c030240300a030121001c81d060702010060028160304103070241f10486059024024038542a803085250f4541162107904118440c4402c5c0306240c428080000507540c400c507202c2c0d1f60359440701d00c84412080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 565074307 1250 565073057 565073101
    0x15140106021006081f0c18090204031a0f070e0415030b010e060d081c18050d03061a092806031b09060824040e0106090c260c12 56
    0x182c8240031640700000183c600400c01501d4132170321400202c440c900c000d44005d10704a0107115031954007103850301e50302c0320620203048244001038840d491030910041d8448046410004507040c2410700c103007032100840441c0e003d0411b0404402954594000c10014042ca1801b035801c1840c0718004420810101740160403503032054100c80003a2645000c0108141d1224002000000200100f0301c44491544499800e0000f00e540003c2224000405200a103240c500444030360304039000d0030403106e415105000160101403541207140040f1207000d05640b048002c1684510b4032078514102e20001d12404450201c106016004440d681b924007034090a0510881e9440301c899002c210303015846660180104c030700760340c0e6800d1591101e10112840d14076038503692010780590491a0450f443e103009036440300c442c0400000745281391640741c0044421865a5004119035080355084054441c5035508074072030389038100c040584810b10b014030284160b82c000500100c40800300300d4503503030f444900800c21103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 565075557 1250 565074307 565074311
    0x80f0c0405071209030e04090f020102010606050405011409120a0f030e100c140c041a09010b181309330e0d05070503090a080c130905030304151401060210 68
    0xa20400c10065880071149480051480b2003555005640ca070000304c07199000703007005400d202d680408201a62500913003030303890304440d50481e011541d092040c03070b004090502d00541001d0410000030080301030782488087c815008074041180e541c4842400440c42d140c1c0d4102d80611405241140701150310103000d50120b0717a0100d54100da401d0a81d103644141e8400d9035244000f403c1c503500e01c80031440c90014600e00c1c0c450a01c50100d141c58600c80c0d03074451070101802064281c030a5040094681b0140c0041d044000c01340207800b0200d0f0802c0e407411001800315603848a10050054a40040c524402c010307019144070711b4000c0c4400304440003803208811000d0740188030785c84580200c080c0c0c2c3d40b01030408000d500002c1000aa01e1244016084083c0315a083c0c0303103000300080004070311100740e80240d080b80e04002d02c4c40e02035151180a542e03010340d0300c8206000140280c0c45258503404000c20250541e101c07a83c1d4203461950907842052a0b2140306070321086540c444800a5541c140c040012940314 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 565076807 1250 565075557 565075573
    0x703050c070e041b030b180f0d02060901060501030b030c01050306030a061404150203131103100509340e07090801020705060106020c030316020613030803010b0a090b310807080f 78
    0xc0c001070313a1019a0380101002c8072036140c080c0250520001d40b124007945010341d50804003403c40600c4074025441840d4018040e42c1041e040c00b50840758580c1c09a4181171411040c00041c1d2004901410349400900b404c0b502ca0f9103640220782004035261001380390368645010b82d808004401d5615002c1c601a019100a41c1e0406006a04070f102c181c894200c15248407503540c1c00a402007143da042a003029050f5071844450710101004c1d51403e803640c4400d0780080780c0301c540b02484480f60164030796040003004aa5928480c00300450401e6004011000803510002204103019603ca44c0040031414002c558490071410700035121002805030500500401c4580901441d000090314004c50802d92075981c000d9607039081082907031005500740c03010100d02c040000841c400101640c02000c090b00c2d50340d80c64401c004014400b031415041100074803c00d002e10428055104a69072640e107103036049031002c07010f00740004140c18080c0d0207480a88569003000c2031405012417006030747c8a045048500c50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 565078057 1250 565076807 565076843
    0x806010f1d041e0501020409020705030301140f1305071806030c30090f060606110c09040b0106030906090507140108090a11220c0e21120703050c070e04 67
    0x301640d0250440311402c181210703c0e6a5440c643c590310340b10701c000615060381e912543d000d90700301c0b80f41903401360804401005001c4034000200d1400d001180c00c800ca080080c0d0010310320400240d001c0344400d5840c0002000503009040300d210284040d910811019900c1a000f0050807107140c00c2400925006a100c00c422015011a81c0061014540551602e0021003640003428016002e507100603140810703d010891500c01d02d00036224641e00c201c1440e03004203d0300d24003e82024031343d00038a02a4100320108001c00030190540700c1500c5d01142c00c1c1140d00f4890040c140454002e072080c051135000003042980c007420000f122800389c0701c885407542e42685840c0c940983c000064140d1940019207032a900e00b4808000b0b141c4502c542a04071000d08110740302c00c40b445011041c0200d40404034622662401201d0803401c0ca030003090500000420812494031145581d00b8520041408200f038020140940c050302c039601514401c8030750b195594050703520f1905013980d0a55022004803107a81d42 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 565079307 1250 565078057 565078109
    0x10b1c030e010e03030418020f070f02011b0302060f07050c2512020a03290c03040218040201090b0a050c1506040b030a0f0809060c0109050a0c08010c1e090806010f 72
    0x101103001005035044c940703041c03c0440100c51440e190307d407466003080001e0002030580080c204180c0940401c1038482c1481c8000740440f041021010046a06d425031400040e9000074500c0d4000c0b110105041140c850041c140c0e2507019035804210313030f40600e0b20b81c0e01000303480e5864824080107034040440d08560341e049a05c0905030361f0740013940040021100b070003c100d40300ca1078480e1030507129508200c80ca801594031262401039860061014000043c40300707510700b06083c015560301c008518412410203074000392000c1c10500c500c20a40d800030030302c40c698600a02c1a0341d001032100301a038842d01452060344141f458200c8000b40700d1440c0c4001d500b01030400280a441e050f5014040803c424000d4031901c4e1240c0280c41003d9000c1410000ca01d4800c400313016000d580c1c0d1003031004062601c1c5506d0b00f80b0301e0003601e400140d000e80c0b40c902420185540160009c22151800b003c8401b01c100e030840c2200c48190b5a009468144038820002031003c87c0c103143c52007250020310102441202070710703507400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 565080557 1250 565079307 565079327
    0x3090109021e060d05130c06020f010c090b03060907030b03070311090f09100203090c0a1d0f090a08090307030501050c0307031a090a0c1215030204060911030c03040302010b1c030e01 80
    0x380203902480012080419030780099007054607002000c0580e080c80e035a5403200c0c2d2882d0031400c016042445034ad80c2c281001d0160841d801c4190402402440c00e0401461940c040100818821600710f00071070640d0b40294800500102c0103400c2c1d0f1401078a030700303207000c100d008640708278002c90300100000c0001c4503884076940941806400b400041c0c0c00c07444080060b400c042c1480308640503101c2901241c3c0c1e00d07144418018403065108920310098800040302400d070040c44040d4404010b810408103150128802440507071101601e615052208082172a0508540008060790b213440c0611840000b013501442c400d601030f680c03c0c0501d41e085082d10b1603281020941580040800001c00c111381ca441d003203050190414a4614082c012062188089d100380340441d121204400c403040c402e50415000b45000741003d50824010782c461501d8030203ea201c0100725094030680032001c501050710070340000c2c00c1050010640c04801700c80d4642c020705283c1506080b4041004120303010790650040c0c000c05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 565081807 1250 565080557 565080559
    0x317091c0305090907020309100e09091203060d060f0204030602030609150a030b090a15020405030c0306040507060c02060c060106030f1409250b0414010f08040803151503090109021e 80
    0x50f052070741e42001d005040d10080c0c040070550000f0710a0704ca698944140c26480b00b40c0503580d5100d180008030501c2003002002c0d00c0117035180c0080c10056076800c40c4600f1240c0040b01076920b41c003031001300e04207040140b421482c101d14103400020b001041c80100c0d000342d4040c684c04c60700c12a0644621207400326810030036640715002400024200045203242801a13440b905c1602580c100300102d43e60300fa600d034004441c1c25101a40882c060026080c2006000d003e401d05078004d00090400c0e45444d40e950200e44680c40400215003100c00454444a05440079503442c44100e456550715400c02601030030000450382442e516008251a0364202521280c1c0900090301c003034403200c3c040b0005d11019209040d003189104250034800101c4c1c0c036403a4010401812010f800790362000c850790004002681103403002040141d001c0070b00011a040714216500440c03402e48100c507054800c1c0100e80300101031220300345040300110400c400c90300103400c0300d40018803c0ba520007406c11075a0740e0f040000d00307121020f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 565083057 1250 565081807 565081817
    0x703020603060409080c071a0406120203060d0b0a05040308060f01050d0b01181706090d0f0f14030a050f091b04420e0613090c0317091c03 61
    0x10005824180001d6800400190001c01c40355603c2e121014a5400712010701d100e0f60010300c00b04001c000c1604501d44402840b030410b480c107480d1050080960140e02900d281e481d0f400004209140c2c5d403e012a0340042d4028100c9031145400b8007502c0c0100800c407016808594918002402498603102c44040f204c416107402d800c0c41d1104001c00700510020307400505100e020158810040b0030310300302ca0024285141c03030180c216010340b40d40c0e0070200050404045640000e0051000e01e400400c96040c542c40e61819500c5e540030488125a0075896500d03103908045d0000900440818640210340320360f15401c000c0c05540c9510741d01c0c9039a80042c400310b42000e00043e0a401c294989500804440c074801004400719102e944100c010340c031080881178100600c8451591825040d14400c00010401501c50030401d20700000415005583c0310000000107581e00c030180104010480c9110103107030005036023004806901d2111917154001e045061088054085401c11114100b4500a159a1596031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 565084307 1250 565083057 565083059
    0x106150c03031e0b120604030c150204030606090b0301180308010506070606080f030a090f0602060c0705030c0106090605010905031218310501050603160e01051b0a03081807 76
    0x411a038125001008508140d2503a021021200d000c01070140020b00c0c4810000303d1044c44410040060380264511a43e42c210508000110750400d4544c0382160b041210172022111141d030702e10003845540c100506052401c040440c1e5001e0f168455080d48006030020401800171205400c6488900e820050014511900501c0f25003060f10251006a20860300810000d44824180b07040240000c1412804d91004c0383d042142940400a00020a107243d803d002480c10040e0080d1141d070010240003203c2e0000850f03004001080044a00002e1003400030031141c0e8480c0d6051016003020302c80c00c1e001400b10140820700d8603020884c0e0b95079921803c4041c0c0b07041640785001f890030080500040c2d0022402030b0300301c0111043c0010800344d42000a00340b01c00091008a801113440682069018900030f004105451044010101000840b03003881e044488905004031003922600a0b00c00500c5e20520300c018485000040e03680d01544070391203081d095900d466081a01841220b08180d040e4003d9034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 565085557 1250 565084307 565084349
    0x3080612012d0603020d060b0a1a0412140615090c0a050304060e1603031206060e030a02041d1e0f0f0d030b0114121009050601120b0310060308040906080106 69
    0xd1100710600c181d10002c07a506a417500041e010200c6403000b65140c1d03403241c040300160314158850320b0280c07050001c2541e0031480540c4ca68828044c901644d001c42076020210014000084115001c5a880ea02210654a044512041c5401246201c030703003d8000ca10101d45540c000d01c0660700b1644260703980e9410b59840da1104c9018207007140e4616124001c00e2040c90003580c5107076210010b18001e072100071000e1107804094044642951121042000700c1c4200f140c16540403c1d8032070307120f0301254085480d101c441103c140b8040b440c90400a5482900c208072501d80c5d07100c00340003030076002c3c0c02a0350041c802d20802984071144220417001a40085c00c5500780070340070b64455501c60300185400314410305555040c1c004c0f5071007045180d03410303914902044142c4000c15200000f505540c817040c00f09040540000e045100a940800005030b01c40403100740399241005001440507841c8001e0052980c0c80c14043c100794000d0150200d401d0400d072000c541d50005001320001c0718039800960107d1101c0003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 565086807 1250 565085557 565085621
    0x6090d080a02071707030f02060408071112010c17010e0105033003040f140a0c090902011110020901090b0304020117190f05090d1d01031d0a0308061201 67
    0x5004203840c607801d11955004c2280744291194014044078510b907913540508000e048894040c5900e001c65120108020001355200b01f901d2003280d00034030b224640042000002c440c40083c8181ca111903180040b0560841d51000c0c41c0304548843d0206481140d0700c40300b4060103c2c209014003074250307100c402e42128944410349030680141c0d01d451b40d000c800c00c001d10030300000e91058500f40ea65418a80d5000148101ca814041080c0300034001850660482da4940e030001042e03100d424101e560310512007056900842504000e10b1081056441c00c007503900001c0002e401550301940024008070010600048100c00c0320301864050710303084040c005010007400e0b41f0780001c1810000404441a28444a04c10700810b50500f8180001060519100917a2464041c81003014820002403444c0701300e032102e0b22803500300210028030f404070351002c5d062112032540f940301c2a01041d0748200c0e9880390a0550000009015000c110ba42c0c00180c07611011403820786008420302200c041d00d82c0e0910030300000103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 565088057 1250 565086807 565086811
    0xf0b03040807230f150a0203090c060c010b03150f010501020703050a060c0903140106060f02010c0e091b0f030604060e070827070803040e06041806091110110f06090d08 74
    0x40c4810351810fa015a0295090040c1c031000d00d0031035400201410a4800d80c3c1100e07607406541103004506624101c140f00d6a1100c480c0c0c140ca02552000462092a1500f034101c034140700d10140840b4000c03080420921804035084a840c6c00540d000303070011501e980302080c6401240e4001c0000c0040d520140c560000401000c0c54010600860f01c00000004030f04030781d101000e8035400000a40b08d480c1100c00b0702012165079242c011645803021503c8601e420074550045140c0a5031200300c40d13070301c4000d403075040b18203001d807004150b801242200c030210510000394840e500c1a10140f00b0603a880d2540c248101c0e06846090208240c01d00003074400540880880407010404440440341d032601c42d005061600e96001070300c164100050910858010128140c0c0005059404114038400e5000d0400c0e045003024004250a4940396001c05100c500c5003011107040000f084040a21010b94015020920307500207a00280141288084041d41c0400c05510071000d81c1c0162105c410841d4040740d0705030380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 565089307 1250 565088057 565088093
    0x2070f061d060a080a0218040e01020a020609010b0d03141605070f0902070803010b03070e09070306060e060306060708030a060b04060c05160509161707094212150f0b03040807 77
    0x21420500010f99950b020b41070303e07801d603274000503a00e070300c0a24000d0501e00c005201d540168104030290380d943e22601c0000c40c1a1341c052070420305907400e4090b1444140318060300000090720311201380040c0074010404908903049000c3c0c030082d641d51600104180d001f5043d0150041d02e0034401001540c07241c400469020030185400719100006400146450701e040c1c03803180010782d40305030902134641c110003041400c980c07c50b900b90561a10034001042849545002482c00202102044c000c210a41000c0068140058620340f01d40c0ca0700300041c180180c21205407964412811074003040c510400041d0141d560207014414540d40761419454040240d040304070070408460030398542481030100c0039000380510b6440b004400d2415190000070840e00d000c41c03407020170420860011900f0328030f10b48901000324074520505100601c0c1075529092105852600701e00303040384002d0383c00404410380140c544030300607480d01c1901c995043d1964081220003c1500104000c188045030074800e21410720300c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 565090557 1250 565089307 565089337
    0x15012c010b0702180a0e010608010501050913021816120e100203190e07060f081003062d05070318150504020f0a1d0a2a02070f061d060a080a02 63
    0x210510200301c20880845051781040c0d5140380c0a40c1c0d0306000c1c001d44004041c490000d004e607504000003c0c03880071014010107034107103034160300004540703c102c09204100c1c05030200e14428a8442d12185040840d50014400903649450170030b17803002948521898030ba2080d00030082d2066000b071100080d80060070105800914501b0264500e000b40148054000c3d99409030810b6071600b08081c002c02c40303202440e41403001d03035010049001c444100080850f50405c0c030108510060354100b02031050005074100c1240050102041200c0440c2c00150142071240c3d010440200000300c0001c01c041c14080040403105056800324200d07001d5040300d40c206000410076244411000f000030103148069000054a901d00c41101e9a00d0300c0d58414568001035190060058031910940c1400c1c48013400840c4401c058010b9600c014a4400c01a0001922011134402d00c0c0741d480d030300040d08a21135858481c1c2900421041000300381020400da0740d00d401c4940761541242c07240311842d00a5000005403221001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 565091807 1250 565090557 565090579
    0xc03020a150f0e01090b01050d200a03021008090724120e0a120206060a030c0509040f0c060c02030c0303280e0406030803010e310302070815012c010b0702 68
    0x85290700c0341c0b00148030f030340d0000201003105142036a0000c505070b02c10361080b1603a483c01004a010303038000708ac5030398140c1003c201e042810700000d000d00085410281d008203500f0403640b0110b4004031558040c2803140101c48240d60741d003441c0c0c1c0c40d04015085074980302840c20484111207000e00c09024214443c5140481c41040c10342580346045048001920081e100281c90b44640d50140403064000c81e050340c400800500b035071207240710311509100c0c0c2c178010641d200024040c86a0440f111003819880104821a00c2da901070007021030407000e2050784280240c40b03401106180000030bc81d24541c0c0300941c400088403070008103110310b04040f508014040c0110a201c0c8503038a80c400c19014600c68141c003a12035041500000d2003034001020008415420010124428000100310902000e01543c00c44980d5052804a0500720140d008402504c034000c10000301501e899417690603242c001b43e2290481100709100801c00303817030528285040c51005c006208494440c8000c3c070f042c50020b030599103d6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 565093057 1250 565091807 565091831
    0x30c030f01090c12020a05090c0702090a0e3708130603020406080a090b0402040c0903060e010c0215041707020429040e03040506040b0c0f0604120f0c03020a15 70
    0x50501000102182d54072980241041040e050400103041c50325021135600d09554003194210406000d868441c40401c00001d07000c0002e681190062580908444480d05000c3e900d80c001e0050340f110520103000c0c008040d8071103440e0b08041055042140d07201010b80244241c050400580c3c00420745001030100103040c2c00c0d070301015481c0b0090030240c0c3d0041e5035134070b0700e03074000d08500c000303012200c05c2c504000388640403684810680d0f810039011034002840842c0580107a503140701c1e50744000d0040342410b201174180caa06607c021800400c540948040b40030a02e643c042c071880c11038005020350b8200f1091100900103d0140c04c0c0706201900c00200000c02100b0058030f0000300304500c074107070174950004ca414140b03401140c0030ae140303002c011400d0508103000108140240c0c000c07910f120b0710110700001050810071080409000c0c1c44151030340c905040c11300c1d106440c80480c00801048240090700704042c4a4200001d000d5050780c05408050102c0d40c0381800003210303542e00c80403251280b011200d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 565094307 1250 565093057 565093063
    0x1401081317030c070b01050105030f0a110d11070501060b120a052211010207091104050f03010204030f1a060303030c070303090309150c1a06030303011a0d0c0c060e0109031b02030c03 80
    0x1840f14011010340700d80e21450300041e5480c2c1600001e040180c24802c0c000c54402c00141203400200c80d550200703038481003c801d2010380c02005003011501e82082421041860004000c0c40e4040c0140024010103450300010500d40c070a0310b641c050307611030440c00644030700c1d141c0d8801c60308441d1004088031903201003203030003140700c032042021703540c0c00012000f800d03c81d0303010440b460062030f08000c01e000c003111000b1003030034601039407084601600d107005040e01c15035001c0d41101e01855101e50f0540e4800c1082c141054141154650054969140740210340649030010540b44600d4440458501e01001641d044002c0c1400220403400d02410300e6001c2603001171271529050b440d08a560380d4961201c1d90404109030702c80069180010907403c406c0c824151000700459055800724520300c038001c88452a000705a10614002c840118541500108103aa0005009902601611003440401c0703a0001c01402c8400740380d00100400d80048078441e0318140060036010a50009060350f010400210110341 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 565095557 1250 565094307 565094311
    0x11112030c0306010e040c0e011110020309010e061f03030507030c0501050103080913020301050904020d26181009050f0f3a0803070c110402180307140108131703 71
    0x1120321070201c1048003035640108000c0500c0000c0f00c0074020f02c014800c010340030a06403140070381009140080018108010000c6502c0301c81001400c641d01c0c50300a211900070311020703040e0160b60260b28082100e4200c5419440c0b400e00000803c07000031441c5640585140c0c0c4424011824480c452940340007150f02032042900031801480000d981e00760348000c010364030244080916420744140014092500c40e94152580160b056a105c56411183e0078822100f9009041c1e6500400e80e021160340d0304072201000d0b1400840500742030100a00d45410000d408109101070b100007141184100114a80485030b02c1d07030501c01410440c03404407504080f5141060082074854801e5401c400303050240b06000000101e49001031604180e2081590307a4451440050910010807035908680340600041840354216000010811996040d185c581c2d00b013042e0b40119010b1090088e034100084031041d12000402082050391606901d68a00c0c103140800b11080909a40300c1000c078403001580460790000314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 565096807 1250 565095557 565095571
    0x20030a030e07060516020607051c020c191d060103020d0608070e0c03071e05090a0305100c1b08250c090b01170604050402180106110106080304050f01111203 69
    0x11462048050310325141142c03590051040050401c40201e0302c1c0b84406440300700607411100e540e560701c001e0400c2c0385004015098030304981400704a04403095000188451808070075144503025940e904100c002c0140580f0419038041120302d420003400d0100d00f40381d5400030301418014240074850142001b11000c0750014400c5034081e42085c05201012400168072449050714540355151500d002002d1420220007182022002205a00214003032416521744440280aa42c043e1f41da070f00f051560740401079824982e02c0e150845010b0401d2150301402d210580d24801c0c01c81c0d40c0b84c640d4854a250b448040744588441102440c5160342c480034001600c40c0e4051038409a00c1810300038100100e80500345103d05003c0107040003e20a00c0c0c43c000750b98080e6084800150590f117030300200311480d070f5280c600b1880d0014003001003081c0b60010011400d52600380300803c0b159840d214034035540d02c41d42c00b8aa0f0b00c03515540c1100140d611480350060001134582c16a189100c210041c49400d400603220a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 565098057 1250 565096807 565096811
    0x105041d03180a0803160b0408040305061627050d0c0e07030203160203090f0108090a12030203150a05030606150d061401030b030d120b030a15050103020405010b0703080720030a03 79
    0x2c2e0301614018500601070044a0095864a0061241c50306210000980200030003041c80c005414031441909840043d0f80103402c0d12250311309100f0010b00a109600340c14041102c001884286600b100c40d540041100080c05404c61030400e0b0401c007400701d078040d045440d05507502e070103e2a6004032200c00c1c060061a00c0158032418030160fa071504900c0d60303c40e902194400c4c450703400c43e941c07040203d89085d40c080c2011861512181c4040741005800032000e001d14000c90300790302400354903a00952050b6400c08070140292082010440545010710815505920180100d50145000b41d10240e442441c00303127081c41c0c080140c0840c0140c5070720b0f5100c40c20074440303208500559601402405001c100031005054102d40c003450252844520b000b01517815562001d400310151002c0085020382034100c08100801d800303002e025400380400f404120b0240c1c4c100000011800a06800d5a601c242d154031181c20070b644e614421a103142010101e0080040000305c150352041d401d000428142240e23641c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 565099307 1250 565098057 565098097
    0x31d1e010f0e210703020c09190c080f090109050307120203071b1a030105010804031107230310050121030c020904030f0201050c0405010c0f08091801060306060e090105041d03 77
    0x10040c04074481e411045108001c01c0130b400002e5000c00c0c00400380d0300031180c03507030b440d00c1c3c4c14000185411070824054006240109001441d41c011501521660070b41200c0940c0e550b4007819142130b100701e00070041c800e600c1400940001040000120600c01c902c0c0704507410030450361504501486140c01c1d4001500907803e00380014401e0720524000e10408030090b902d554074050000703200d540f0040000e010001c906031070030200b00007405030a00030031030040040e58180c049503207034424840102419203c2e1186940e0b03a403400d2070398001d460480303402540d4030720341c0305607103800207505c03d8510001c8080102c11008000107a4074075040078010350181d501e18030941a0f1010290071a00050503800182c80c0034802080240e900241900c00a82d01c121240d06580061a064416004e8441c44070380c8500ca0030500b44410303001c4402203048070f18555040c0300d100e41e103600a41d581c0f08000d0100742c00110a800501c11420550407200e00001908298549611707210740c100c0c1103810280c0d07031018541144203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 565100557 1250 565099307 565099333
    0x2010f200a1b051c08090a030e090601031506050a09050a0b12040c0902070b04060c020f0c1e0307062105040c1205100c0818030c030a0e030a05010e0106030201031d1e010f0e 76
    0x380305500c5060f030b4004164406450302e01514441840301114030ad007075580c0009600c2d901c42d030486801300d400103a80485041d1101009804c2c0d03040b50343c00d6000104464000655880d04005140445030a0024075161514010010400200080c01a0384000c50b0403400245040148001d02070380d0300407041d0741c00600345482d040b41960022000c0300119400b04142507515400030030540c840440c01c64920404407482c10944042e2080300c100340d5498041d02e034000030400d070001424014809000342201f10200c06507241c1c0105d410584018201300c44002e0140308101120844561660050301201d00801c2000c0c03211013541e240c0880310340042c40c1c00080c407090010340d90b0000610000c841c040e50403d850180303260f07036030700407035400704100920a42c440c2d51645040c06500ca20540081c0280014404456018041c080c0c5100881c0000c0c5495081380c0000c1d51110307850303686110000580582240b44e540754050a1900c008105a556200e507624001800f901c43c020003400e40c0b00181c0f0001c50141d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 565101807 1250 565100557 565100567
    0x160506070e12060105040c03140411040509120d0903050403050a06060302120a020d06090c0e130c1a1606180f1709061b0a02090702010f200a1b051c 65
    0x100100d0182000c501c0c5542c0702c501c0881c20342c1c11340d041560000703054150311904602518007440001e58051800c0103110500400e050300003203504041d0350500407902d4a294003a51030600b0305040d01c005005010301e40d8420501c9d0042d030081c2d4042d1038011306040d01e0340c13220342c05c0a190440440d451a0b03030301410421810510024a6254158805014413024030f0700810250591400001e000655902c1c02d80100a0b0417010030700035080344d0f0b40c41052458207000242d4041102807041da56003030f0613080015003081d01502041c1018200500070704041d00007000b0b05c0c0c0c25038082e108032410783c1c4480e81550700310f6020f200c43d00d03003a00618043d14513103404d05181e48806032110103103000f24810400300700315032a440e0481e4081003544001034900840720480500301211030100035842000c0c01c060281040d4150021044040c0340f500c204401502d46004040000c01d4108605025809200d0b40c4512805004c0e42080201c11201c4003218450740e40e6140d0070b120301c40c06800703140e152240207012000c0e441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 565103057 1250 565101807 565101827
    0xc210601030e030a170402131d07050a050a030212150c07111c0807030504030206030f010504140402150c0102040b0403050609151003020d031808011d0a08090d0816050607 75
    0x141c0c020f5860066031300c1008008242012101c2c00f0699040046811500d40340a001040781d00e0850030000444035500f15a1244502e0f1003888440c13140410125580c9080b070845421034500410788000180785a0038020322038601c08c0301403018001d00403000000f04c000703e2441d01c54890f1100c582e5640540b407400b041d001112004840c0542107100314410410903c07485503411a40202c1c09136180c0c8400e14041356148940c4c4c0001b50003000100501c0002084001042d050ba1030403501408004e28802c50705e04040011036001c2c1d4010b54608c082d0088044110003488a0a5842d002503e00b64a90300ca00c40b442c0c6c040d900032107603035101000300183c140090186480801c19001424540c0c02c0003509840c00c2c001e580000380c4280b0002c0d11107010140514400e43c600d01c0c40320403c880140e034175800140240b1010b044242c1560b1145e512201400713001c03e5100d045544401d4160400d48540d0034000d014010400446205004001010002102c207141501191080004200034581000000d02c41451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 565104307 1250 565103057 565103081
    0xc0103060915120f080a0905040b0609100e04060e19050c030103050a0b0c0d0906060303091715072106181407080a0b04020703021c0f09030b0c21060103 67
    0x5420a0000710710b00188010b01120508840b000a078116418210220300d0b403190000d01000c000100c20910390340107800d20003115000c6904204200c100c40c00e001142c4100040198010044060720384107602584047c1340b4100050400221151a0b294101005006480036140c0250305080c449074070200b070040c91340c07042d141c00081d070440d45940c0d5001e0b983d20a10000800d4144080f0005030325000300010750350b1101d20524244003240c0281480001040706001c1a030008040d4007021480310620708a41c01c41e092203800621002043c505540e50700400a4621020080088040022900d9010500d101c4105084000403498a4001d241155500a80300400f80d94103024491882181d00c01071b040c3c0c04105402c00303d000b603441403100d800503d495200d26920902c08140300060540c0098004400d1280500e25142d44800181c2038941ca20203c0300c4c0390001d20065018400100e8494483c1e40003481404070500b488582103d00100d4560503da105003910f040c0100b007070070341c0e25000311924000d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 565105557 1250 565104307 565104311
    0x506040506010c02090103060225060b0f1e13020c030a26060d0b07020a141005060901080c1513090c1211040501180e15091005090403080901150303020c01030609 71
    0x301c0d0360105d1413040d41488080c1c00243d0100300500c0d00800c2a03850740400301500241c1c2000051440c3c500000c3c000c41e042503010b10210b4040c2d100728200440d502c41e00d80c200381c941d501c0307101040040001030038241c82072444981d000e1241c03c56070401040640110400340d00c4810080d0a91000f05182d01c1082d0400980d0800020038804961110721103440c1c510b40000303034003030103036580c0c0c0b0243c0c5000c002031001403400e05c102992000e211404966401e002c5140070040c081ca440f410104182c1072000c0c001c14400303800000340121145014070b480c44d500c0942803081420b00b81005404109002c0c00d5101c2e95120791151414440507500407400380c0b10080c00c2c0e004000c0800c1807143c043c2140079601901e418040c42aa64501d5010601030340b00040c01c00074801603441c0b502e00391a8151680c4411a640540c00010210f0640504daa203500141c91001d000e80310a552141c50480791030310003034075980c035030355a8804603050650424090400707503003c2c0e0014051011000001011103403d5400010628 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 565106807 1250 565105557 565105577
    0x30f0a020a171f0b0c0c0906330313020108010902070c03030f0908030301090c110d020a0308061c050a0b0a0603050604110102070b04081c0302070201021f06051201050604050601 78
    0x15000b4011103400b032051284610329030341c0c90700700103907140303000319030f029080c1150200058401054000380140c540a2080e41e42c1c1c12075140070300031441001d464241e4004194005800a84070310601c1400013011108149500b0b1605411240180e03c10303620b003040307001d40c210074030f040d0758100c4181e60040000314411464007450f81c0720750449880f14000101003000204445843c103204400f0740000e40b0288054035500e50351034226000500c82c1e44106e90110301c011200c0949d920780480c140307aa8407400e0f00a020200240c0e13908454034600189599400304540c0d00107040c030700350618a81c0006100d400113003c8024107080908805030300400700d9000b030f4100300d4140002600442d031a43c100341d0040c80101c8282c42c4200503410203c0c29000281f4420000ca00083d02d19400283c103500c1c01c03c0550006c2101d00f0300388003141070303116401029002d41d200c941c040690190036030b44c0310341886040c3e10005007103490700001107043c018040e917080b050303448030103000c1d4520b00b9100d002e40100007424840548 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 565107913 1106 565106807 565106827
    0x90b1806040801020a020703120504050102030d05100b19170c0406050702030c0d0c030309060801230f19061d010801031205130303050c0f1204090b0a0302040f02030f0a02 75
    0x1c0400100e0300c0344014081c0040f00d080d0703130068ec040c2d0b141c5240d1114440c0500005485000310b8423040400060b1728107000080c00720902c1b613000700590780d0213080000b4903a5040900164411b601d800c18040c0d03001440d000c880c05c035006414290b40340d040c6400081d0a10102040b031b59005103444807003034104100d500915059031320903100c0c06212a2903490031a030141090250224011029607481000c04007144041411100142424581c01041c1d010609210380c01e0051100c01d11003520910400e40c10100d241c0140c2802c24a944244020000090a000062101505031100b002d03d0040680c858011034814500d91540b0b0301c0c2c03150392450002c145074852a41c00da254040d035102c00a000e070700402c4a00840d42541d52450030542083e903550001c000303031419aa4041c0f180b040000041e200d9000e01c490101c0720a10040c2c503441e003881e85d01d070408002400310505610410405580c = true := by decide +kernel

theorem cover : BRFrame.Cov 564928057 565107913 := by
  have h0 := BRFrame.cov_init 564928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 564928057 ≤ n) (h2 : n < 565107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
