-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4726
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:32:04.219934+00:00
-- url     : https://prove2.me/submissions/7bc93e58-6824-4584-a6cc-c20ddda2f2e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 849820143 ≤ n < 850000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 849821393 1250 849820143 849820183
    0xe15061008071e0504030f0b06030609010207030f2a120e01110a080c030d02040b04210f060b0111030d0e01181a0a0b040c08191a09060102011104090b1c0203 69
    0x400c3e0220781501c039640005016000c1020050304000c1450605809410105e0030303107090b0b41e142140c4034203d0140385006400107103036800000039280221045000c1d00d0080c90070007101c29a146004075003491009003101e0919410401034209540100c2840700d002d42440e02e440c02500c6604880d56400e4254405488042c1c0040e00c112400f4081007190052000e5000c10740d00d03a6682e50304032041d0303045440f440800301d0804001b09103007059506180704050340310041400e220310b69102d2000070701d0710f036000d24140200320210286d800170810180010f1070f0304000210700001007000303c6007544c030441140da010245111042c0b000403a110304e1030940301500c80c82c013410359a814002501a0201c17242d4641c12070f1821014000c03859000950b644154400c0c0050003001e8683d0450900721100701e1542d0500717041012190702d0603d099201c0303903048401403002203004600d50180040c03940c1b00382e00401604d40e494900c0c41c094200306007842c0c1c1103124111540d0714a942c0b9000710361921481c40c113075000100a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 849822643 1250 849821393 849821447
    0x10e01090b060910050d030e04050a0216150e15041a1006080601091203110610050307121103061807080d120c021203070302130b04150804060e1506100807 68
    0x600126004040003840c0c40c04010843c10045c048c00035a6404074007841c2040c1c00548a2a0780b0700850b803d000208000090140740d40e01e501040030810307c10340d4907040d19546103102c40c2604000070190340c1c094154020544c10325252003104001c030b24000111400a20040090800406e80d6200c07c0301e00c4c0d414680342990782c8400403655850a900440c440114081c032003c00d00d40d1041da41d8650221200440310b031521000310f4506412070318850a541070744814000e0013070f03407030810310400382a00c107584019069130210002030070b0402c201c82c0007100b252818010301000b101044410000d08040014004040a0000c020190b0008200711030700d031902c46450b054124800c12805c520005000c01c05912403c00040003400b960020614150300007004c000444d00400c254220f404503840c206cae0741548503e044e8010b42d00002c0c01001600c03e81e035140124400124244241a86109400301810207460240e0800243c040f0920240702040071440030808007075042541070f003901072200c15078a86800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 849823893 1250 849822643 849822661
    0xe04080a02011119120519150b0415021b0303040501141b060106090506040e070309080f030903030609090109121b0c0e100602150a3605010e01090b0609 67
    0x50741880c0e4030000f1000035100301900c49a00c0c855442c0001c55690341c01540409001c041580e4003600d03481100c04004070b415480c052140e0111610403c2095004c60385640c50201d1603a41d001940601a1001d0103032501c51440da042c06540c0358800e01ca800758207480351110119940340164010541400360310f0680100d010240b009403a00c0b07148420b98841c0c1da0048032202d070303100c0d0b500384624800b1890b84400804c0503e480000d071015620344031032010303841c0c0d16040203c018003c8980c040e0703060f4801308805105201680c0085210f01e05140045949080c0882840300c12440189500030a91400c640903000070082d01885210401915000e020311043c003040c504034884010009003101c40c8450700040042c2144190707407051204040503000075a58410590700d800502002c0c9142c004d0100000307a4112440d84171011170b591010001c0070365a13a4203900c401c0e2404000c011104400300b900d070442000024020074042c003045000038000755400307595120340d481c8050320381840b0743c60380000100218 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 849825143 1250 849823893 849823901
    0x1c02030403052203020301060f03050a1b03021e030c040203010503030306040e100c180b0c030d050709090c031508010b030d0e191e240509120709150905010e04080a0201 74
    0x10026224850301c0c041c4401443c85512681d1201700d0195080040018114003030380892012690080301401d0013007007a950360485a101016906000d2440d0180400541c50351486581391811038050f83c0e298880c0c010815142954240d2054850f500402c0144503640300803098a070405010b940c0071441c801c584203140d04044410405506242c9040703d240301040d0f2040e0802202c298150840070030988600c2d03025140c3c85030340e800d1040ba40c810020b0b409894200c0d4841507104c2080d15000031401e0311810710300250b070404040440000e07140c02e0520a00003181082100500c0008001c120701044100480c0d1213100640420081c0600c54560801649a003000c0c2500132600e007081603c06a21039038040400511140410340c0060320345004114428802d0849d030313a0640e0740c0c2d0311051011030161f044506500c0307070100c01d8024000807800d1800d8082008503002a010003070340450315801c643d040303142c81e9000d03512003e2001d00317105c010040c41c20600041e41e04240c01c0f40104e41e890208080503400740c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 849826393 1250 849825143 849825157
    0x60f0902011d13020310060e0306060d0b1005030303041a100f150e0307270c02060411040e2a01030b0612041b1d07170a0f110705030d050105061c0203040305 69
    0x61400001009201d20031ba07020042621401d03180c801f86039006206241c0c0e102011141140c00400c0300103c5e0011400c1c405010b07a000d8007601000c240580c8400100342140c109440c11540c007081c06058907043c070780080c3c0c8107510100c02e01d002c8131814034050744401d440000307100720300710210480031b961b9404c1c0c072a4140c1403aa54000e021a03401d070707a0350107605555441560311800e000414a0034258204640d02802c1003a2080d54000c20f881d80b990b0b240c0d09550518041ea445d44923541c0d00c0010400d0400740b012002c031510115a40907040b01c1ea8001450b183c0c1322020140c101403820701818205d50f0b0b240c0556480c4031008190f0f84480d07645180c014100c10341d50006400c000702180e400242c0d5080740c0f0090940d4000c90f42d2403142e80e141c05c00300b65030300d00f03500342e50000959520000404d08a1741350301001c5042c4894101150080c4440b4070009541d0041900f603415800c002041030342040c50b070003040d0040c08191441c62514900760710140703440c407601c80d60040301e60300080810145446541a5210 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 849827643 1250 849826393 849826429
    0x308060607080f0a090f0b040510170411090c0c2503140a02040f0b0f12100e030405180708040f0804031a041b06050901050c16060c060f0902011d 64
    0x5141d8011210740410742200180d84001045210f0100b00b89940d601b0755001c4407040312206040c2814081005540c8001180c90000c1100102e007032001d1401c2c0040c180c0c0214025046d40646e40084400e0002402004110882448040108642d5980005001c101e49846036a84112241110304003040c0c80740d81d50b00c0580041010241c0da00c51943c007141407004107100b1107081254400051902e020b9500344954142e0110019174031441505080c2089281d00c0b403100700780e4098400126842044131420f24003034000f588081000d20490a00c80c416410781b00b034642c40f411030343c80c10440080c40740a00500080000301e810490404010340c0c80d06440c0603690240c0003043c48c82c0b81103402030240300110f400351071206c00c40e604101032894600d4a20107441c440e94816151802040041d10301740d02100c0c0794143d42c0b2800000001a04080b20100c0103414241d07038042c1c08422038105201640d0b0410821641c0c68500404500180c2c0c0011a04051034103451110007906003010025481c980d0320f81e18400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 849828893 1250 849827643 849827647
    0x50903071202030406081308040302011805130f05060d050c06280e130b06180d080403060902030609010c02030d1e05011707060e0f040504080403080f07120e010804030806060708 78
    0x1c10030b40120281c016a086a07413000704030ba80c4c4084160005c0400040500703990010081031015501c201000403513014200200d00702950f0f80c81c00b0411804021400e64074041c1e0f208040000650702c1d000d10f64228074111466803000f40540c840c0d84d261719100000a21541001404a00300002c003503503440990344a00c07070b600c04900d0860020b017030781d5103a048142c804e0b0910104860310541d1881503400c600c4028101c0750a00c540c6507411070401e43d4a0003140c1d4040040790071140015065001800610311402c80881e414a5a20601d0f03d0080043d200a0050341005650840303164004181e4070440003408000c901c17990410b40d07200030404400c080d080c40a05100000c1110240c1c0e11100c54210340e10021244490740d9414101c0e035103a001d036003c5921003410064540c1c0c514080d00500d0300305d03004416035450a07030391340c0d47c10381c403580314411340307110103001159480500c8801d160300701810b0120305040d0404050a03000a10904d4010002418012040089802c0e911070005940e0916403241c1030315 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 849830143 1250 849828893 849828923
    0xd1d0616021f09141002100f09020402030c07030e180402010507031205090706080705040503250e04110306010e09060a0f061e0e01150c0f030203090a030812061c0605090307 76
    0x81040240307004034900d0340c540f02911360260900348400041e4610700d03030180c10600c0041d480740e006410b802c202d80703490701d446004a601599891000f0f40c05010801c1f9200d03900c0c421442c000d00040c00b8580258407540c9035121249122078080b118540c803070b50928205030358081901c3e040d0fa0380c0c0d100c0b038078868801d880d01082042c1001e00023060000e8850948500101c0d030380e10102180c03030784514010315825400c9800483c1342010044a07030f1441c0f9081d180780d41449900e4419910104504a0707099075004510700d000340d2075060a10580b400340107c51483c0d00f852401c101340c1583c1d56005031514444503915103480d407144440c0d80c4203070042c040c40e03144104203034100700c0202080f0505001c0c07041c0d8025000000030315411180d810414003401a2106001000140c880c2d0780248010102035003503000c1000340e40e12135a19001140c000e54030980444d80c41d90180384c4480c20400000788024003c1c9000d401c01180c0d54140080c0a062550092000c1041c0d502d040c0c0e02825030041c00001004400424006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 849831393 1250 849830143 849830147
    0x80604150909020f06030112020105070602040e091014010e01031b08070b090406090b0d08071109070903050c0a030c050607031b080301050910181109030f0d1d0616021f 74
    0x1000d0160080340d4030b510400d41070b410000c03148428441c100401c6c20084004004ad40920054842240909801401c013070740c8694400300000c0865150260303401090b200018040184218040b2007044003020b402981040030781a8088010702001d4241c400703c2c03d100350300411100ca0b0101500140c3e00ba0360540c0d54a128000c15074112040c907034820342c101280420210154490941d036800000d11510090f5110744500740d059114560545201c40b2884116446448190b42d546c01219036a0b5a40d405900e142003590602001000b00c0b4481c4c1000d65003000401c05107201341c000d49030112001c96031840e0360320b426a80044440120420042da01c0d002ea018444000003942c1281c6081d10700207000d0f5601420804005514010319007020b0022020f41010b0034940c1c8607020195141c99524070344040200020b240101040c0000802d0340300d0454003105642c00146070794805120a0303d90384420325500050100d00540700940f41c24054404c034075040d956204c00c800b51804082a201c68221004580 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 849832643 1250 849831393 849831401
    0x9060f22170303060d171306022425030608070b030402101e050306012f0f01230603070b19090614030403201e06090d02030a0806041509 60
    0x40004001d440c01e80355480301c8002c01100d1103507100134100c5540700b00036502c1c0072640c084248268640e003424405951007003030140f5a040030700100c2c3c00070308219032100c481050503c290012111122940414000202c407000c0311180b51009414440742d0f40c02544a00301c1c0203010a5005001511030520300241413100d210045001d68025110f000350002c205400340c41e020b880f6802c4076001c040320105a11014030417005183c2182c014500310300202e51200c034070700c1a500702000480701d944860980c4800c201301000550401059000240b00d110f0030703500b00120301b01c0181105c05101007481d00141d403581c0c00344942405401110300d040c2d00e0705090651403400800201403030001c142601e0307000c110305002c2d9840b50b25010801005238178640e40c50b64115104a844c400d50590044034130007401d040542030190203105e00341c04410010300030b0720301070a0340340c1540900045c03803076008081e495101035408800c0720283c400343e04008050b80c41e20300100d4010f00b500500141e010280a030b0100d851b20b41e40d04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 849833893 1250 849832643 849832649
    0x250f03020f0d020d0e03030f0a0b040b151216051e160507060306060203090a051c02060a170f0106020a20180402031005061309020d050d11060c030c09060f22 69
    0x5005c01c002d100c02c00895070381e403209035100480308681c0340c0000c446424076006000705020240001c2003294034440480d64000031921800721079800429925a08200020b60039070001c3d8200c414521a02205005080d034400c8000c1180070340c00751440b040070305c08441d08441144507030719918680070038a401c0041c2c5803c6070340221000241480300009410384000182d0b41200303030043c03844a40340d15000c200700d075002c00d0540c0c030000c6049515110015a4500010300541542d40d260000b040f1540c411845400c900104a015481c11840050241079400154050025448000300743e09942ea000242d4900e01e004020541c810038610035406100791880c407150080b4400c0c0c0071a600b0040a007100c40aa550071a117040d0448000c3c1d440117400300f4641c01c01100b107400900b030a5105c4909449107401c00035802804804101003619200032210108a0305900c1200e401d03006045040c41a01501d142c840e0502151040c400403400940c0c0c0d0360710400715110340800324000a15200032442052446a50348 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 849835143 1250 849833893 849833917
    0x408070806070f02120a050702180106030b030127031b0803010f0905070807020a240f0b10210506060903150601030f06030507150504030c03030215250f03020f0d02 72
    0x3c1c80021a000003442210503c50800711820802148011500354000f06003d036441003109613420b001040d40300420f03000c0c207116540031a041070301d03070149030035a24501d28002404240c1484d15202040b00342d2490200790785071910704c0b800d20076054101081e0300441805040e4590000c00001c061001c16041700403114410030900c2150340d415410341d000401202d0741c9001d81c000100881c0081d00c0362501040345c00b6031207030201d04c0d070500e03102240c00c442001c1c0f443d140d500d540e00840c5840d8a8101020480340c0c03d28070304060a109110200f04146402c40c210f81e080f540c503440071a079140d84020548081c3e9001504841d01d030f420750000d00000f80c8050f05c0e594007192600340c89420400c0540980f0094940040040c6032607032800b111458072070607a0074203508000062201000140074010b90780000c500941c01442c01a0700102107003005007002d4a5490f41042c24403c0126501d1039100c1c007810a581c6003800d60400b1b04c86034081d4060b200d001c0001403804000185444140c0d420303400b03001c11440b45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 849836393 1250 849835143 849835157
    0x90609130503221202030a0b0702030f0706020c06060f0a090b030a0b0a0510050a0605071103100c0c0c060c0c060507050c040e0a2612091002030f060418230102040807080607 76
    0x10b0014101d11004d0004041e4044c0c01210389200030800f503800030740d000203081c030450b49407603444d010300e600b0307a000030744201c8080307130001845881c11008004c1580c00103412200070b04601400d178001030a0218a2240c0c4c20300640320303240c0200583d400d120707541c040c94009131840c1107031030940300900c001c0c601100c2d120303400e100d07501000c070745403c1a5130460140c60540d1200c0d07103070402c5c545030700d1560002141620b074148200c0c080d40034601044d024000c540d995a031621680200709280c940340114064111108225600c10110085641034500300121000c605225946109a003040c604082512400ca42c1080c18540e40c015031800009030324031101e00590220f6018442d9643c0027150b50f00e0181c061550b101c05220440c1d440905002882c1c2140054088a0408080c1d61890099801c03c90b440001401a80c08116213802e0038000d87c141000c1c030b9800101c04110540d2001440d88401041d003030345642e8040350f001d40030025411240900180300441e20071303545d644c440a6030b404080354075000103000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 849837643 1250 849836393 849836399
    0xa08090415030201050a0e0a0b0c060f090307030c06020c01091403031501020a0b0a05090a06140a0515030d0302091504140f0901150e01031409011a03030909060913050322 75
    0x240740340d550207580c1d0581d21186000c51034001212803002800780160300c2101c0010000340d0080503402441c40191070740180c0000d2a14260407400b0640007040000c2c990402c00056001940c01483c060307199910a00c01600c402c50303c005c0c02d0052400c000002d02140040707040c0f01c110900000618030411349000d0206001040e50012a280c401c034020090095004101203000c4001582210b54000d007400b046a600c10300c9901e900c2e007914491100410b01c01c003200144001c8800c54000d099110a851155001070780120740400d43e2884030300641020960702142c500003541d9001c800382075401341c2c1c0017a251035940f526404d00e00e2003507100260344aa058440d43d010030303003451784501d41224035401c01552120f242070400e82c0d02c0300e8030801942c105692a00025080209502042d0040d8000b00c000a1840c180603108d10342e48480c480000e200b0390050042100e25916030300351030b50180050f50740c2101915a80d04010303030b210b507447d0700070050301001ca1107241c0006089500c06804107080c1115880b036507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 849838893 1250 849837643 849837671
    0x630010f1b081b1909140a0e1503010213170105100f090e0a08071208071d01050d0f02073c0b10080d0c15050903041211030a080904 58
    0x10601e65000c0070501c1040055240400c00500290030070425561a1030081c02c504540824188040703c40b000c950312100c02d1008801828450168441c1a10140d0050b0b0500712460100d9000410708513500d410303803d007400300d92004e4054412851050546d03914407610381a10315881d002522421886620700360001d0604049919420100c440860a51001a05007101c81000d06445c404100c1c0b40d109203004040003441031401003e069000f185070b406079258110b0300408009025141d030081051715070440f000200001c40030b44425009007841c40e690300180103e907010300900c5200d800d40c24408580319052009200c1340c0407995155a044143c00302c0040c580040c48088030a50b40c0000c07601c0e04c009000100b00114030f54200c1c41c00070820208680e10f000d845d00d4040400c00e9100012200b0700d806007000701032a0200560540c40d1300a00051400c41e4550317903240100d20920540100d580030300e201340030008905020303a0384080c083c0d03a02d41009080c903200e90380c000c5551134042c034905800c00705051 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 849840143 1250 849838893 849838931
    0x30b03100e1b0a15090e280903091214070303030c0f05190c110406030c14040b1e010519080114010c0b010512030c0a12180308030630010f 61
    0x6034024030b44a00181440440c042e07021001c0b84d09010b000d0780205c003183e06142036844510483c02034000a1030108040c0d80300100001040e02e000001c2d0500d1840d000003900084080281c851b108641940c03d107190400101d014500d940160090140c110302205042d89a0042502620035466004038102ea00008564170702c40d840c80a4801441c0640070042a8800c80305a40c48174001c0f400142102c43d5200080c04950065008882d09110668100a4004d0a070200000b0b02d034225010001101e842022520313120762141031031010790a00320380741507981c010001d42d08041503850044031000c2a65030b01034198031080c044e040080958503040f00d0598495440495629070280080c03031180d181c0401d00a070145640d4000340745000a10000844c60310402040c00760601030030240b150013155103400340c61108020144101e2402c4060140003083c90752003101e80203201901c0004c01e0703280c28000184260b41c600510700d40800c412610400d0300308150401e00010489000c10404001803001c010094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 849841393 1250 849840143 849840193
    0x40503120c1c05090301021803070611100c110a0b04021302030403120b0a05060f1305060306010519020304150206070306060203090a0b0d0207060501030309090e0106180c030b03100e 80
    0xa42e1141d81d05a1401c1c079007000824100c4902d090860034151940300107800d9810103503032588010086c0f00207144514042000070300400342400c005020f05407038441d040d00c811440c040002010749230320040309058070030000140700f501c42c0402c2d0350411840385481100303803402b40d0f016441540b009403c0e0840500318130031280900c1d0f054550748400c541040202c00604101d1810990055017000700060a1f10307040000e01444c0540c5013aa50384e607000e00044908111250803060151105000308040c0343d800404890322040020107642668016010032407543c4280e800c40e008980c4c06040c0c212a041c2c0010318039000d0129a102400710585601d8100c3c0d5a015010341c503503129240074004c0007251034041c0148100524448050f2400701103440303c405481c0300b0703070040340001d105520810002e80305104001036a40b1040c024440f6500e0140c01100e20343d00318000400082e0740d55600e2100234000c0d440951020806010380d4201b240f403400302e500a01101281e0a403e0003140e43ca2500741c5030804c481980 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 849842643 1250 849841393 849841417
    0xb06010314040b06240d061205070b16081201140108070f0f02030c06090a1b030302030904020d1b1814060301030b0717090c010314040c031205071704050312 69
    0x1c5a902d607121442c03071100c09800617401c40505c040040c0301e00e03101c18869a0540480c1d01c540c0e520100c00d0048000c444090740001902298031690000142c0080740e0681200d002082c129260951f1040e0140e41c071045920050440900090070300340b0000911406040f00c641002c00b5441e43d00ca80c00648010102b04d94060016604070380394409540507100d56650ba000c41c0c41103904008103402e1007031230108241c480545907400481c4079810002d07080f680e000542a01c6404403482441c41e60702035541d0003441c009a03c903e4020400920403003d0740d03c042d5054900d8801e0309515049000301030711100c40c3e0380c18a100885030110114003881000212240d07044003510301451030780303186c5422011800151030581005048404001050001442c0600034031148000d0b0400381b0040d40003400711000043c80f8020702e00290b0800001c1a00e10320018116504403d143d0038131500c1c21170455403481203030002072000840c90ba007441f001c2d0504001c1c1065980560031a0803001e02800d00314020700070300d07001880c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 849843893 1250 849842643 849842681
    0x140f0408030a150806090d050f030a0504021503070c1407060c11010302090a03031206060801141003150f0f08070b1602010c02122407050a0c08090d050601030b060103 73
    0x1000034190001168460400c80001034901540d4100640402d11540310a98907480346050020b0b9900a00900d0203110a03070070a075161540050300984c607408024100c1e40d0441d44c0e9400207080d915869900701d0414401c445650f900d04c0c2c40034029011500410007655440c600394100e5440b400000341c1c0c80700b03031045030700c5540c040710140d5039265110b183d4031001410550244202002c1d0348035100c0400141d8860b0f142c06007910403070f007800c078121451a0f11a200300114000108581d4030400005140d201083d9040c48955400483c2a0b01510749039002d0f200d8045102c0300080d034a1203485544042e903810550381c12203256034402c1240e4031041030041526001c0104000c100c102480440024042e1041c101300c0e0200d246900002c2510300090f814001d21307000f841c200441520301c2c071021403010751a00f01000700c81c2060b20b4020720600030451000d0a20a003e0400418003603410709540015500034541541e1041e02d00d8000e413074170710a1100b145c1100312140400c8596000b0b018060341e0300e80b0030141c1c038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 849845143 1250 849843893 849843901
    0xc0b03190c0219060e01050f0a15030314031b0f0d0b0409080901050c010b1f0806030d020601061202040f17060a090f0f02061c151205030301060e1906020c04140f 71
    0x1019903801d1421506641d944824082809007030040c00d10450f21115840c2c46032030b02700030b11000d8a141240303201000c120350700c0500000750000c50804c803100d000c0c05110b803a680c0700902400c02d40c1c5840b82c421411100030854903140d4444000400314145085024000c0c00c000c1003c0c0300a0304c0c005080106020014000f00c001541b00b00c014003240005c00e0004900b908030074010075082000781c07201050034040c0600b03041299401402d0282c00440a40040440c0c0004402c001e44998060091000308081c00014074460030f2a50140da001c4e10110b2500150f9640d14007154081d11b070084103c02c41402503034000344200000d4400d6801039a04403000325024091540e030030a1884400034100d0344043c0c2400308800c0d64a0380d80d651100b014940800141c481040000180f01003c540c2c07050380802800f40c0e0706400918080141e90441d2101d0500003201c0c2c80f1070000031464001000404c0d020304a1601c00500140c0c00280032004070810356080042005201c17046220300310445076056079003030040101d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 849846393 1250 849845143 849845173
    0x1a04110901050c070905010602010b0f10080402040f1d2508250b0d2406052208060f160806010c030c03020123100e0609160207030c0b03190c02 63
    0x1015944203c0050700d0501c0d46a030f03403050444000380c01540c0141e40d030b82c100310400c2c145180d603c20300900032112440f0b02c85108800900411004000900035620342e5440e114903059504400c101c43c0341c640700081c51810744105175542c0c0d420301000100c64040410a6141121069a12001d603070380e10010705003092000050484981e8010083d043c6d418514200007000c2d01c648010b000030045a6a0100d51090820244214010188030110340301344003c40400545401c01d048400c0d041c0c880543ca185035031130640c46604015142e028400c01d000d800300300303c50400d002c1c4c40e83c0d20489010301c1500f410001e500c400c4800c0d440c22603003640441c1144905c00e020070700030403040040a1091002080380c0d4000c00191500a6000c48104200c420000600c03c2036010040204060070b407103001402c8920f442e034006190748030040d01c00300036940340e0074003503481c1e80c030900003035014541140242842c03da41c1c08650b6480e0b84215800d003142e50710380d4900b0040c070700c05006481c1100615801400c1c180442c6800d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 849847643 1250 849846393 849846397
    0x30308041505131a0105030a0b1e1e07140301050103090c050a1805010b03041e03120212011409010e0c090409060c05040e100e0c0c01020705010e011a0411090105 71
    0x980e00c009104008036000502401814441c0c284243c0600101a01d49002c411181065040e40300304540301d0f00511158600045000156401c921603109075203800090500240c500d00e4040303000a003040402c10f5450440440c480d13011600ca90b000c2c41769889140407110821101d06004040c18104010400d540c481c4c0c1000d800030b409400000c0d10503940d040020191040ca5204c03d20118200390182c00f0000c15229840c01032410452080c51858a0390b124442090a0828904840d100c0c060000605104080c003003403014811034119518070040d20803e402c2002449110070000410340001c03100d00700f6034034041c120fa101d240d035001c040d2150060301d881c0390012900b41d80c22940d11394144010a606000340d03610103030302e62180341e46c46050030300d8045072080040040b1a11003000c3c4040100010380750038984d0101903076090a8541c4e4026004038007910443d00040c00541c213090956521502c1903221502e119184240034140c0e0701d14405010a17100c1c0000201d82d07513441449020459406100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 849848893 1250 849847643 849847651
    0x1e1a0c0a14040806012c0415140c0d02130902040e0a0f1b051e1902010c0903120851010e12150108010c0311090904242901050c0601030308 61
    0x18446101b0311903804c0d406081e21080340c00b03882c1c0352840784410020b04090f101e032140803402000d40c0312191512032003008940c415100300c021030940c00652040d402e005604c07540040d01824100f90343c0c580e607484040c1441038003542d059140b0340c90b04003d0707000440644035000c2c03c441500c0c11228030700c0a040003594141c00c0700500c00b447d103202403202c80440c00000014030107481035501c00c800940f1004402801c540400d00c4070010f06c41c646005002148115041d11400c27021071415206954a1181c0d03404120030b4070304030002124018410481c88111611390f150b4030b055a0004901c0c10348078201800014030701218160104002d020190042d040c100c103d8600c0701500c0741242c450781c819032441881042c0981c0305005a95540030711984441e030502030f5a500b2080e00140343d04040c10318000940f0380354003030070050402c00c80c0c1054149100d040e02d610306c02d107804100b04002c0041845110000740070b08110390358045160220400443d8003075010b039100c011340d00d03005041c1c1d40e00b141c0d810398035294040c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 849850143 1250 849848893 849848939
    0xb0a0e030c010c020604120207061407030e0a0b0703030b01030b01050d02031003020907050c0c0105090a170f010204121109010e0105090403020c04020a030b090609041e1a0c0a1404080601 82
    0x100281e5101000d018606907285640e0007001d00e4a068184482244404a00e100440d080400704202c84d0303a019405503c546120103501eaa02c2541d0310302501c0d48003000c1c9244d038020051600000e401018000175146946c066142880f004428a0045044416044d2580d0110320207125030514412540c0c01340d1ba00040d41d4a4500e8a9516500000c440b42c0089900390002200051010100d11007400070150024082c2040b504141c6074200280d07540c452070081e41e20006104911120400c810400040d81400c030f030b80210350b01c98440a100708072075034001040e21030044d803200600171410b02103c114122200c40c4000380842c5d01303140402c013140030042c000ba01144900e1038580015511403004102d82d81d80d1fa200068200411003d2080d15040101044c1c802c503080810000804c2011142c00c1d04142c0485010304490440e142c203280f000301c0080190f00c410f0900040015041841c1c00400034280e4544030240c0aa03000c0141d241c480c4183d00032400f036600400c004211607410700b200109802910 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 849851393 1250 849850143 849850147
    0xc0305160e03030d02030c071b0e0a05041b03120f020303060310112104031d030a110307090f020901090b07050304180b03030a0c1b030f32060718030b0a0e03 69
    0x151544c0420f980058071032110154000400740100300b092040c11a07030380100e21150149601c0e00524a0002400800c0080c1d0540c07948000703001c00080004c4a0390034004910640555074a03030404069180800803444040b42e81900d800021600010540c0c0c818103000b0020590603400c2080a405400e2154070695500028805120341c0000107000c41d005d02c98254a4080b94a8241002000804c200501621941e6000381c0100503440c08200c17413814503003141134541e846a00202080c501100b540c8200c0c551450b241c103100c400c1c00c1640090020341402d0b80c1e030702444c60311150300c065203104821004080d984200410840b4019920b002e80f48014451400219610307a103010a0a40d8488001000090400700b001000c10826200040d0315210031042c4400d258116a5002428416210058150550540a46c8407012441d0250016000f0304c9182690000c8920696179280003e4545001007150940ca00b0f0008a00c1da4a49003102e0b00410500a56100c3c08030308002814454525100c50000b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 849852643 1250 849851393 849851407
    0x20319150f05120c0d060c0206070f1e21020306100e0a150302040302120c040c05092d0a0806090f0a0b1306060506180a0510050406050d02090301051008010c0305160e0303 75
    0x61780c009021030501884c000f00b8402d021040080c20204000c00880030300041d04940e4007003582c480306500b8001003980b034840d02d06014550a444801d550303185401040707503a10345032071241402c0d0051809076000382da480407800e1858001ba14240244415950808242e0340304201e1200c07a8204521003007141d040051425490f60046603000c521880c2010700c95000c07075076110003420b1a20400e900040d081c03508500b01100000042d400c03100500108840080312503001130070044007503000000c4100108184251595811090b4030b0f034000b02c0d4004028040e204070a581110042421210301d544540c0c4d0b50070603620404d400314401c80c5601300780c410664544000c20552603600c014640d20071002d088001803500182002603d05080c0c1000307010b403c0c0c0790448030255800400780c81c190382e2141040c0780c648441e6800d9400901a00700000e80c15801c280503c0700d03265040c80e843c819505000b0090142d49400e690a40c1500c10688081c1d4462506000500d0300500c41c1c0306001c20750cc40102560704c8c10b05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 849853893 1250 849852643 849852649
    0x160c0f02060f03070e0f10030c09120b040c09021c2f0d0b010309020a030b0c0f07060b040c050c0c0f01020a06140610020a1707080d020319150f05120c 66
    0x2e001584000c8000105206529401400d42c0e610b1500454000c1c034404050700110b0543c005c00800d040505da101d4041070307003141c02403860f1005008201d03100c6080143d6401c0c0825260401d660903950020b41d064003041c0390506000b110000504200070b242c2ca4407442d8240c0008000a807089008a00c005940c0342580303801e01841a00704105103030044d00d54139041500c03000c5446980001e130515141c42c0c40031005882b008003100881c0d0b0044070024050365103403005000c07449240c1025070300d0000040c0d4041003041642c0702c507000603410745040217000001c6c542610640b08010004090742c0c04000b88812a15200000007501001032060311038008043c1d40e05002e440c903500308000d40d4461001044414181500c010909a1840c07004080d454541d0725415401d01c0017070080070b40794000090182c14417000d0411074906da1903d200441d9249013414040740c0325102d41050a80007800c11a0035071040600c100d0038010703074440005c0101ca1078139000030411900407a0b0007000d02c5020342560f1100300e40d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 849855143 1250 849853893 849853897
    0x180c1e0a020106080c1818070519060905040b06090919020a03060e0c030106091203020a0b07180504050603030405040506030a06090b090d18032423010509160c0f0206 73
    0x445400104249043c030344d02c1070400d00102440c41c05440782c00096465242c1020200b600304524540001800b245410014140480c1c1c0c1c002c0c1d50001078580d645d00c103024090065004542150303942d80c1c609030301d500800c81503c400c806401e40c091421f1000000c04d281245100341c00c0f504042519500c02201e189100030781c0c000340f6065010965401040101c0c0c94068025588006036248041c0703958104100070345500200d00540d199540851004030405008004d03036402c0507000400c104180ca401c9600800c800c01a0303040c0d40820f00d40d52000140c0c0c1c1040e0142e5030080900030084c40c1440c3c05c4c80140002000010002c40e03061151811080c04a68a407094040041c05402041882e1401c0b660042c80d145c0c2c0c441400007040340842c3e0464021003001c02500680b50b008000c04004699a41c10804030fa9205c03643c00700c02868044100e24112102000001900c100c020750b000c03c0e0b0342e80c070402c0101002122181c0311881e150b0b00025201d84a1522501074900c03030305210340c00140d1900818929 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 849856393 1250 849855143 849855157
    0x509060306131a1c030f0804031101050a0c11010c020d0513120b071d0d022206061107050d051002032a0d0b0405091f0b0303031501080105180c1e 64
    0x180702080500c58290510407040d2813220641c11003001c03088041d5600a04200c40c03105500c0c00c000d94500031508151041c0820020000d00750001d20040c10900e10380401072445001000210301411040c18803508180184404406960050a515003007042c080e0342640c0000d50081c2d220005080100d04407480300b02d0210240c1c00f40c4940d180c94941200007038100540180e0b40203249440510110140d03440d065401e0100da41a211903000300d103844001100c0d54090241e14a409007030080c0442d41ca640706209200e40100c034001c8804103903660082c803440562404000d055500203205200c036200507074000b5500250000d881481041e00c0012030b43c7d11401041e0540381000780002d502c543d041c054080c042c0c040d1401c480c20005400c0808000d540c0d0450a1342e200040c003040c0c1d4010000d41c003594443c05000401038280c0303583e840c041d0025485030b40c540310020f0124807a01d0001c1000d00f055503035080c01103803c07010703c1510345403a0415503c40e000100401c841001b0005034500341d00001d00030f4068 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 849857643 1250 849856393 849856421
    0x140d26120109050105060301030c030f08300a1e020304030e03030c031206180f0601050d060f090c08070206041e020a0e04020301050108030f2d0703020f0d0c0201050906030613 77
    0xc15414100000140c51040c1c0c051840b600c400d00040c00854882d24102003100d60003c2018011207041c50101c455005000310b0040003103120899803a030786c4031680405911030050030042103a90350000d52030220780b00303a11400152407201142000c1420181d0045800900a041540325000f503a0002841c41d0701c417040074850f581002c2140c60695a4400f10031b0b410250885000038040c503482035070000b0440091403c05d0500402010402036400740003110300c4d288041005001c0ea13504d07101d40311000025845001400782c585900514018452441540205543d5010782150340721500c0300440042c80c400c1c10740c1031990181d0118010307510f11a00e0001001003291900207890140101342c2101c0050f40141c0d0a0b800810844012200700e9007200c0090300c4001e0110701080074007443c40140005000c032960010700018800c0c0501d0380000b900844030750388400b1030b002c412081404403038500307000200901146080c4241581c0f413a03c5005164440740280c800460300352406010300031f030ba0300000d001c01c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 849858893 1250 849857643 849857677
    0x30c010e030d0b0103110306040c0905150a021204030c03020d03022e0e0f071802040806070e120c09010e180d090906050f0f0f0a03120315140d26 64
    0x20340007202d40604507045209082c10898041c075180b0b40070b024400203000a2046940340e000e550850b010759540d01c0030782405081584100902d40003100d07940d00094a190241c424950640c400103d050211401d803a402400c44042616642c280070107249440e00407000d60141000e1504440401d0140704040c118501180300492810394900003261b16011406c91642c0041041c90f0040740700245107001c680e00f003141c2c0a200440314a081009000c0c54000542501985042c005101d601903007081e40d1020440f0500700500034060006c0e9102030b000d01158110380804010441c841720705900560000041e108140c0a0741c100f08082c0c1480c690600c42804602010801d00000c0324901c2901d0142c034040c0d84c41c4c80843c00020014200c4440da1020300c1c410501084d07003180079168400b0032401144d2007000a00101c0510703901a016040f280c5800c1c0303c3c09503d140018140084c400d101c4170100b0041c02803d010341080d00c42d452146d41604220388030400c450802c105c5101e03000000d010316100001512 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 849860143 1250 849858893 849858907
    0x5040c110105100f090e070b160f08120c13030803070e0d030807021c0e1e031209150f030402131b020604060e010b06120919080a020d020f03160203030c010e03 70
    0xc13040015000300d20342c81d1030a03444a050310350009400041d0f500850320107441d00d80122007180c224804100081c01029004150400c01240701c000e070002c0000381c1c500350b031a5501c0840052850141c1c0c0d03413050640c000d0f03010401c0424071400080d44c01c40898502003040e05207030800703d4184030118000728000b603411b03800c010507541e05000c001c00c4d000060320f20300000041000000c242481202c0041d21501c503103180030404034806103400c0d00c174040190544a14025820000201d038102c06240c1e4000d050020001040c508040d044410880406541d242035840d10340034015034658242c61103c03101d58802050003031800000d6884031303686650340140401c2c9018540b00301500c108501014107603050007004d481c140c0c1c802d0140c99803c101c01e088022203540d1440f09501e401114020b44851101d040004000e1000e00c5009020f4840316408490039446c0d038980407aa00c110007000601150424020001c2c07480031030481c10780060000302140c1c180a144100c8a00315038042014204542c0300082d04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 849861393 1250 849860143 849860159
    0x507051909180b07140d1d0d09120b0a150b0a091d070c060b0411070606090b010c080a091809020301230c0703200601150507080a051c0915150305030405040c11010510 73
    0x80040907180385007070708038545420740382c10601b01c8030030000b40614035100005424004982c4001e014613685800810844d3b9144280609a4421502000018071001c80842c88040004080d0603481c0301042c00420f941d9100e10440391107259070411103009840307040b807500541d03d5004000d440090524001d607251090703d0018200c0c0d0466210034121800c2060f042080e03a004040d661515420650440d41c41c01c14007000c4541c1001c0d03400418030460003800c142d2010381c003603005560b0648260000c10001c100d80d0942041240c02011701c2865004800000341d05808440182980c0e0784641008040c000c18101d41418100d90a0328480559101400401011100d015483c05105503414190701c1d20b0b0550300d0702080303413141403860414010000381c248100c041c03c55451450f44184641088000a070b0311b0105420074007103008440351400c0c030040040e40c4048010b190200c9034010019071505140405120142c55a21421424007103091607440c142142030080301d202c1e200c3c0340255061942002c0c81 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 849862643 1250 849861393 849861403
    0x60c0a0f0201022701230a0806131103040b0a02031b0903161211010801120f0c050d03080405010506010516060902030c0607050a02150a0206130507051909180b07140d1d 74
    0x186c91000385404800444c9014464100c4240f40c2c1c583c41c201c0c1c1d05a4401001c1013a07114000700320000c240c0b07400640050380040c1c4000d107003c2c9200c0c04400040c0d4071910701c0383c0107030300040c0c1c2d18402a1652008061a04074130780014401e50340d02800f0b5400040340d5070207250300032900e94061603010034a1042401040400711a2400b28407007420a28801d50420913403402220003180020040c205400886080c8241c0845520050200405d4201101d00d02e150080c03181074141d1b01291290b0234200811095030180056503d28408212800341e00c40168a03034101803e07200a003660140075103040c81601d502d0301ca0007803188030700810052040c0c502c01d1051288890800607284c10320315040c80501c0c0c004d54080307801600a480784000c2410000c440c2011400c0c5840e80d40540e03030090b880351058892010000000003110f104100030042200072110301d11001c454100001c049508400005451034040c00c1e442c030519000d92101820041028003160890382014081c2800011850303a02680b2141000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 849863893 1250 849862643 849862667
    0x1006090b0f04110a050c01020d090302010b0109050307140d080405030601060c05060c040302090f040302010f021c05010e0609161e0507050c0a0503060c0a0e0301151502060c0a0f0201022701 83
    0xb0b08100d02011007070342c018a07000710307071426041110010304a540b80800350140c802c00301c8450805c1100360042d1801900034100c9116003030100c0c3e80d41000094a00e000300c1c0520848041e10000704136800c03074808101c91203803c420200c81805040c2700c0410141c400300083e6010306150340b1001910380c0b040c2001440c110300203203202d0250344204414801600d070241424bc104d90142c03e008682d0721646000d038094440401d0040d070240c400704440c50084041800003000d41501d18042042d82d032500401d00c140d10003107800c5600a400701005c100d011503556541e0525005514113180032403032560710004072801041c110b071300054001c6051028080c3c03e01c03101b600c04c4401c4074200c40a40c50032010030b445039001046161b80c20400b1a0030049140501c0c2c05164090004008004a8841605c1d400c0311403000d000b00d003984400030320050101400068401c1c0121b0b406c0d84443c0c10140320201c01c55060b04d0b48240304003155028841000c0f4075907100c02c0c17118112800c0c214444000f82e440c00042120b50400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 849865143 1250 849863893 849863899
    0xf03360309031b170102031003121e030203061806030a030c050717010c030b0f030a02060a02101b020705190e0402011e030c0f2c06120a020309011b0e0d051006090b0f 73
    0x100323000d04030f5041e0340c070f440440303600240c0500c020a15001c1a80d4121100500101c1c08621640341024940c1c10343c021407017003500701c2e0718030011800882ca0000c602011903c403501680324510b5480424040e1580e2171000b0311400c1110a85915610581d00401500c1d6601585a4481c8140111150940920190aa0f096460381071100d44400001d5640b01003040190081c0000520048024400d0141c86040340429809002c401c01140c91810351301e00816100006016154000ca02454030005030303440d9020142c02004103a00308410004030810191003241801f03188203466030400e0f100641a60244101c0c2c03000507a03100d465802403d4180717220050420028050394907943c0308442096400400f1507541003c10865004000c02c01078805c80014656010000c0200282030080b50000c503c6007000000a00045945d10f00c03248001901c644110042024251295000e080101070420741c07600500c100c0300443c4401074404112410354110070000d6840da060a5044d040c4460414080342c815 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 849866393 1250 849865143 849865147
    0x3090310050603031c060801091a0c0307081504140c070606061803060e0322060e06120601111e330117030d0204060f03360309031b170102 61
    0x100d0b00194480c400c0c01400f5491540001300c44034608110b61010f0041d007100030007000040c2041c02c02002840000b5100c103c0d405000700090540410602500d0184031581c41c2c80d80b003034554500c40150300d48403d00c00703034003d941d65845540f4cc2e5000070f40a4000ea00101d9a02d6440c10242002d405540c0d4a41114040c824407081c03400c061200440024126030b0040c00014506000750016800c512418070364607840d0900d03c2c1102404410400d070071044071030540702c0410300710802090011500810086204c650300243c00100b940d4010764580f064607003100255018030715801e403070450000c00e050801015600180b000100711750007005a501c1000401d2845904501d0004024000c2205020301c0107001241452052444010425580f082103030070b05c255250703034451030001c0940700e40d0120f03080064107001c002000580300039089405141056448680c0c100f0761f1310030758074200e4280d01c00ca003002405180003006c202c0c1c00c01c21142c1c0c0e0001340c069440d014504821000804c003500d82c07440241e481 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 849867643 1250 849866393 849866401
    0xf060702030906090a05060a18140d0b1e100501090602120702011b0b070206190213030303050601090302180924040312060b1c0606050408031204060912020309031005 73
    0x41a142494401c644240c4d9034402007002c0b41c071002c40c0d03501c125040b03003002c60984290340d00710500412610480405905065960858141c0e10b03050b0580183c1000c8520260303800f140c2c041050b135174425003410219400364102003250200c54000c50b0040300c900c404036014850307507034040b1007034008003da440101054800c00200e040f407803181e201c001341031042621164401c0090090403000540e0401206039082c502008065210b6208552034401350012402000304a8524401da901d510b0070302070b603203040c0d6066036410740003000c028148034140f020001c17000005175120346000c0135078940e903003e034580b42c1448406185003002461043e0140611808481700054031307820705070741c01900b510304540140326001c40c0c0030007030049030004201410001815010804050169081ca007000d08042005c1c66070768070221014012400703089441d800c108841d900c44034090801c50f40241c052400011403909941d150384441c8a034551010160f0030114100c9480d1900703000c9180201c00401c010320041c50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 849868893 1250 849867643 849867647
    0x91112010e061809070305060610210b060409060f06210906140405010902010923010c11030703051b03030406080f100302100c0516060807051c0501060e030f0607 71
    0xa414055421044906400240c0c036a07541c1c2039020552404940c0700040303060000c3c009440743e0440c00203503003600c510808030f8100d040a00c141d490702c44541d0344200305401040d015000c250a428000c04086480381d0f4907540f15030b5410300810003040501000502c00d841d110245241c1c246030390120003401134098500d1109014411020a2802c1c44a00040c03a09281d14100000301502e0703010301490341c0c82108200030400c055201b416640d000b62640100c0a58506c0383c81082141c0e094807001010300e40041d1140c5501a07011403030782c20700c12101e5003601400000400d260071890f501c162070550201c1407140d401a861301e20b1991124050340a18607090410b58003900d41e5a000d480c24049451703040004030350b01d915080a0000d0355009092024800034001c0007031694250520540d1239000b408800100003809402d4641150300586400649680744202980c0c29007140c180ca42200b82d4003031050640900500c00d5a000e0419034403201407000304401803501c3c041d4000490f200302d60220044c00b004075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 849870143 1250 849868893 849868927
    0xf1503050c0d03050403150e19080a03110409020703091505090114031305060f0a0b0111061b041a030103060b01050304051b0a05040e011b09180908040803070303060911 74
    0x410582d05902150058030301111144529072000d005584a10f98103030340390360140c000000500c144400c6402d0b04a001000310013800742c3d40e00042403440204194081a80203800051040b42c44146403800c00d83d40707008a1069a12048080703000403c0700a0034000c00c8214000e4051030b441ca4a081d5051004030780001c2e040c0d85540304101180361012000a1000c04c0c0321641901050340101612400d041c100c0d42c078010000151445032885040001000013940300e011100c00140c0380b9001003116032200021a105c2a8034090504001642000f02141d044c013000c072840c01c0b102070302e444c00380d0765031641c00d00804503174601d02c085e07042140410900020400000b180c580020000410760380c40d0007990b0000d54540c40d160300c8250000d0900450385416801984883d4694015402813015000725810481d445a035900899031811a0490700c0715500d24203038403140e00704c5d100381e00c07071460640c0b50b16040d480c6400207030b000c40003c0c0e1160814030407141c0300e0003460148040a400241004601490102d000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 849871393 1250 849870143 849870163
    0x150507020703120819090b04200d0b130c030f0b0c0c0615120706021b031903030b0d02091807150203040302060f0909012d03021503091501090f150305 66
    0x90110041504500840a10170750040f10070030402040c9100d140c4600c1b138900c2142c2c15152018503c0e0a00180712400c004c3d40110080104000e28a50b000c2e541e0080c64a03002d8103244460043c0c1550900040c201c0c0804006540200441040c2c15081d01d801940307094010b00c1000720407020302110b41d42d10740025a180d0040e052603680900300d0040740c0440e080401c4028098200d11841400084042c7c0100303403600411100002d8104d801e031400b0a0666400d289000c45184001b42001e03100482d00c2175021f0305246000500c0341e01c034840c81e500094111031050b1006503803080144241002008104442002861003200c1e50800c0f03010210003079280d000f03e06c0040d000b4800042e001e0313070001c0300b0f00c2128190700c0020b020440a5840b0311449035410180c202076a02c482ca252215101e2281f190358140841e980200000d10440a070142400560805010780d00548181e16a80080c4480e0744041e038040c02014400068038100001004e041d00c00e07400101c0303401180243c040c00461008107100c854 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 849872643 1250 849871393 849871397
    0x1104030609052a01120e06040f0602130312020f0109020108010b0a050d0f0c020d02030f0a0518030607022401140d03111209120d0e12010603020d15050702070312 71
    0x862010390070071906224041250b0003c0010702da200c00c00900c1e121281e01c000803020b0780c0c3c0045c0c1e02d00744a005001c5130a1580d2101c3d80b6409500094000341300c1c011842e101c18070650b000750505410003071941080f403203504100c1e030382e4140d0516001d030603504110b1901001c0c9448020b00082a03181c00181030704070103001d941480480054a10000c902840840d41303500c91510701041042000041780c801400880c19100047c000c00076002103080c4008282c03404440c41543c080d180011502055420b40e01c20000c3c00c8520400c240c0e40307001da41e018462607105101a0b005804151426100264164a60341c1e0401d58800203200620022005403810310002c002650311290b071441034103003a6200c000041d49659a4807800c03010301030008424002c2c090404081e03600e038042c040700152881e1900070391403891001070008480306203540b4091101a0420717610000018040e5101c3d00411096005004155007000c62245600c2020340035100342d40d405540b91010f070414506640d281e4642030105d00315201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 849873893 1250 849872643 849872651
    0x6060f17060609150706091a09121c0507020a02040b0a08060c0a110d0203220e160302131d060109081b01030b0603010608041104020901020d11070506070b010e090111040306 76
    0x30f803a884070f001c1070f40c8071071920301510f4135401e1501d0600060704283e64100c031741015254640400042030303443c040c02800c81001400410405a24200080c3c2001c13252a6000726000c508071802c0c078480c030906d40a080658042c010380c04044c010310060b03407411104039000d1901414208815100400e000b0b23008164034000c01c2d83c4a09203d401c48012035001190340040c020301c000c5191485e00000100211540c0ea4800d0f08024428003001c0b800c05481c2c41039010715014580010640c0d41c0d203401c10580c04817a82030042c03e00103080d81c5206042c0d100d40103020084100451022a003201c17003e002d5000b1000d10b80f50814908154041c0d840d1100c0a0200380c1c00f10504042e08a240e000350001800c1610243c80f894a80d070359500f00402d5001c066600766100d65088950101509050085594200041c1c00070b00c00850340da04101c4061020913060b9200740200000865941c1d00c4200510810f8003031104054907504004030191010000740504070305a14040d40440304100aa0941c1d0884c0e810007800a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 849875143 1250 849873893 849873907
    0x80c1c0f050f0a050c03010938070306051207050609090a02041a0912010603030203031801020c010507020c10030501050d1101020f0a03030e160e0a150801020a0306060f170606 77
    0x150030464490002400c03030084840c0160420400502a110207000c1c900315826951450700703040c229000303c1e07000b030803441e803140307030480d00d038040c221400600300f51194031000712941008030407080f0380b0a89005001a881701d10400c80c500d8054185440742c0041c0016000a91074400050058401c00c1e440d41d004041c04c00c00204801d80c5641900d00400100d5034031200d041990401d480c843c0d00144200e03118500700f20203d103014a051280005603a41500210b2554642200916650003001900d002564080000071110b580078001c803401201b00e60000d00d050704d030440c200895406100310340c408161030880100450764405010b030f62903c0d0400305000141f1441d1004038101010440045e41610610003c0780030103905074014101480007030b003550600d541031507100c0d0244040d440b440740c8510010021442c0c1c1062035010f0b0300050480030403000107580d18444d42c0c0c2a0f8101d810280d000c6135564000b0030840740c11402000b0010100e2918020641d4284070310880380c440600060f02440c0d000c01d5031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 849876393 1250 849875143 849875153
    0xe0706030b13050c070b010915050103111605070905160f050a0309051506040b0409030c120c0516060e011b0b06130f0207051203040c091806060803030f01080c1c 71
    0x280b0b10852481000340301d6803403c082030030350395400624110b65110b9000c4c00020000414030a6007480300340d40f010490020300d40001140a00314a990001070b1940c00c01881d030b8403180880c0940c80b038034440c4001d4102a8a0841450b0440c6e200400358204046135070314543c541d0340d210710209081c1c000c50410320303281c0490410490052140f020010007500c01d44410083d030040c008030b0140700d004100c034107220f03105480091200381c0e01e1031080103010400900b030035800500608041c4c00c0095651405480b00c050545546103001201042403c607900c4400381404a15404440a90704817805c0c2047c2004103081154202404610440900b2078000c100c0413030415520259820024000d0710702c20301c6955000e400c864001e5000007800c644520402e46000a000f10100a480c03081e6041075030b140c2c4441c0791203d01e0000d030100004030580b05e180180d13481d0000d800381c80340001401512000715280c0c607018010f03211f0900180c0004960381d000c2400034034a40d940481d900703001080640d0744123525400d03240c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 849877643 1250 849876393 849876409
    0x40c08010314070b030a0b041b0516140307080c010608060c0304020405190614011d0108010b130504140a18120e06040b120403170f241008010f08010e0706030b 70
    0x81880d00e0f080010030700c000e4041640003220b405004440c1045160481117403020202141d111f80c0c4040ac80c140070540d5a0414071300000200d82c00340a504181c00c4240c00c480d070030f44e400804100c460000200704284102403d10903080034055810040c496410300c80c0891a8038007005000034070541d110030001d02c600762000345c1d5804244041700207000540d20340c15507402c0d105000410743e00181c40250b43d212410030005150a01c40c9046c0c440003010303401d0100c2881c01d9402040440c7caa41460700000649440d0b5204002d61228000107400203800c100d489042500d0401082013003a14030004454046618540038401c00303812410000300416503e00440c9441c0035507030000c0041c0c0000b00d65092054002e08505114a1207680d51071210a00c03a250b003981d42000f691440d4100c908403002401d140011000c4064840b50000000e0508081c80001000340411805480002d0261401040281410f018001c0078040a8000344400c000c05e43c005640e86003035104640030540c50f580003800507150514 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 849878893 1250 849877643 849877649
    0x121e0f0103080901171009270305070c120606090c230a1106040507090b03060103050a24020c0a0510090503091005040e04060c0e010c020d020d0201032306030c040c0801031407 77
    0x102108441c0b6000110610014141c1f082c800500d080c00e440e642081c0b4071680c013000305200d0142061107400141c038200c0b0940c0040030704445800f92944007041c54204004085021072203103201240890801c0070352000d544151030214140440030100d80c00881f0801c030ac01001c0c42070740c80c40688450607030b02d045a0b200c0308075011a225000e001c041c0010b00001103000c0c4143c0300c0e040030038003030b0880c0c14052507a02c880920018025401c110740076070024017205440c030060740354101c14000440e44641010100d9001c803035900746c00c1c0e10201d02e160400405010345c1d5103600c8281410044041c1680300c03e5120320030030b4ae065118544660349010114010f10948002e00014449841c0b58501231812200820309441104089010b014905940b584501800d5060a07070207000101d10200c2c5a00b88a50b00345410803c906054a901982200c110224044003038210481050070250400c00d00f41400d00300c01d0240503010301d08020842c1d01e019000858181146e52003290700d41c0080c0c1b0001640e080c400990 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 849880143 1250 849878893 849878927
    0x30c091202040b2103030f07090501050418020d05091b0405011d0901060305011107051501060c0639080f06031e0c04060e01030219030c05060d020c03121e0f0103080901 74
    0x1320201c0c1d619400006144200342e80b400400345030b11891002d03101b02c2c0c00b510800f40003443c00c12041c8001203500d440c91000c440c0344140035081c12501daa2040036144111401045640551a40c3d2001010840940c290002c15102006194144462075030040c20b5000d000220b60104400702e034000340c003540b14800440e0010000c04c01904e030b07028814803d5104270410b6400c0d104011101c442201d602e0b0300b0604035045600c0e640220752842c3c2d07404001e051041c10384045d14581e4001e01000c05582c06004005a20120f01c480c101043c855014215600140040084940300010018542c600003501621210403403c0004c0c9101c00b80328072480c204900e0549500a800d2140c00141c2c40354000b501230590344200d5003d03164000c0c89a40800007006407002800000811000708081e00b0154001c0c07110041500000d440c10b113417403d9151640d441403a9604503d0105030820958181412a1842000344071180303440ea0f040c202c080c2c10032240107020152100300b00103000d030800e038024031100050392148 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 849881393 1250 849880143 849880189
    0x4110c030a05090307150509041a12061b0301030c03030e0d08220509060117150306480a090e04050c010e0409050604150608100507030c091202040b 65
    0x8054002d160b40c1000c8030181c02880340341c4e0b010903801d80343d468001200c0d0180e92014248000c600820002d801c0160180000d00d80784200c02d00a600c4030300041d800072280d40000e101504060200c5030741d490280340390803902c1c1c80c1400103000241c40600e182049070f805180010180c290040013941131007005500030000e0710001074504041e0220820400f001c18880c0300510103030398400a01c008521704907461400191100d00d842c000558982c8220703041541e40860b0403819210401281c5040c4081e04c9102054102c601c890001e83c0d44020100c90b03c070991005849105007802e103c00d04070101c191203908901e00884c1440e8258806c3c1d100740018004040030444904081c14103980300d0b4802d040c0360340080c8400c012445241407a011f4210400d500c00300521541e40c40b5210000c00014603818080c419443d1003000600b91406c00c12140d00240e504d0000441d424400000b5080307440c001c00c202d05100d58450108a1200c604485211140d01694007240c2002c070321000501c40d0481d085111651204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 849882643 1250 849881393 849881407
    0x509070e09060a21060f150302150403031706060d09031205060103050c070230250f05040905010b040204080703020a24050a020106120b0f0f0f0604110c03 68
    0xc0085084009642560420229203402c400c1c01605a8a0b00606000480039414101c1034034022403180a010f000b80c200082c1814104200c006680c0d10944203a110b0030034407010310952401c00598407031304046220302494645981d40c064002c000c0420344c000030780118000100e06072500c500310f401e20724402c2002c1003920014138020b0320702c14070401c02e002d0030340c0340100160b0554020300c990340c06802c0344024182404031315420421444049202c18605c03c14100f00c461100e420a801071400007030b02c6c0040c3c45000721241c59440d0280b1803050780e04032030205010400c20000e6030071804040d5081590040b500420a0a1140c05003003088080354000d480050000b50343c4038003080b04000c0d60300c00c03122843d00307075502c8484429940d0140303e03607004018115501a0348a000303070001d200e64051030002099455481545640040e0f03260010384070400581c041140079814840f1055002c0321000b06c81c009c07400c1001d0b101810041c001c1c1524003556948001070b40c40540d080942c1c0041c1d11a104490303071408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 849883893 1250 849882643 849882647
    0xf09180709020a0f09050f0f0d1a160e0105071e05120a0207060c05060105042c0d0f081003120c0c08010b03150c0d02070f050316031101090213050c04050907 69
    0x10083e440c0d540043d01d03040c000c0300514420200300c0201e440040c04003989540f00c00421004c41c0300603d58070307031041c90001c44074006001c014220140b442024400701c458900001040c5800f9142101e01080003040c02102400b0385c0c025098800d07080e040318080f2513590307038403040401415807210083c1451044040e60b6100080c4000100001c07081a420b480c0c81513510202903c165001c0100100550403050042c00241015403190303001d44054650031039900ca500d140c2c80c0026104c2a0440c1ca00c0e005440c40c0c8005940211070160725149904e080001071034136113144c403c0c001d028040200710100c2c250340d40b9480e80c403541021722001d4002c008001000c2da02d0882c5802013044601840c042d00880420401541000340308511540e80d108265251403003486c4803c1c001d50251004071000c03001c00e00310001046081000d40728606030101e81103501c0b507090501401c0340c080352600301d84980c14005c4405c01a16080c545020340d590b00840452240c0311050312500301d01444e04503d82259418040140e003079 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 849885143 1250 849883893 849883897
    0x20403050a2d0b0a020c0102040f03060b150c1507050903150105150408030f222303030310140a030b040318060201200717030c04050406080c0f0918070902 68
    0xa140d115100c103010b141e000e0114100016450003030305040e2580f00049500132690010071160354208001890070340c0f0b0b800307030001d24a1780e5042580c210f40d803088590324a040c69100c02c900d8480144c000303030825046001c11541e601750301800c402c0e40a08400403d0303903640100183d60080301c0c014207980303441d15040354a031448030091103103910415440c3c0b9040e0780003000b04212819189404080c62401252110b0642c80303a01480858800703010402001090104440b8400c01410070380700c3ca0401020a010907070182035040754050321a03042041840400300e0121042c030211640300342d11482d607503c03080004002d43e603590f00240044111000300310800d544521801c0500c10400119504203841d800224200e800c10480311158048841d440e00580364039201134020640b0581240c908a044a8042a00381e0026a10080010b1000c20188050300d00303401080302610540c1d004048007040000007580c00b940017040140550902404102c08120400e056031034102a50200c54040307a4550b4403200035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 849886393 1250 849885143 849885173
    0xd0c03230c040b030c09090f011e0c020c03071503020909010e0f0f040b060f12120a120e07030803060319080a030c03050603070303140d0e0709050108030406170a020403050a 76
    0x40d02400740240c4030381c6080c0c031a1200707034900a0018140350800d10300740502c201b4080c0440d42c01d881516101c0d0f10400003406041c2060040200c24803508a6590001c0140e5414404103c1550042c449400064400090000031241c0c014910170215004140941c000c1c401e1040107904641d024001081e4882040031307060285800304105030190b030704c04034100000c820a890017002041d901c00419507629011040741e41070b6800514641c0040c1c400c8611519051070b20060840740e403404035903c084a500030042180c0e100390b142c01449103620702c21420740c440201d404018181400800403480544042114110100001488504140c03850a0141c05504080c4000c00080d040c4150480720038400d00486000f55400f40051030b04c2c50a42e074056510300702280d0081840310040c030500555104d280103524003011040081d10342c00e804c1542140580390140c10407156507204000801a0b641d0141d401076005803a080140900d840f1010400040c0c4504c0d4009840c9100f01403c610511980348000240 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 849887643 1250 849886393 849886463
    0x1e12230403020d050c06040809040b0301151e140d03051b0105100909030e010c050c10050417160306020c01020d11280c0b09070b030117060609150d0c03 67
    0x40c98038003e080b552031103040203c05050b0890300c04100041c02c184c001e0102600e00410205141c658400440c1c212840828440000d03501c0d9402040403911200c0c078094401d508001c1500240c2c203052062460008415447d03000e5592030310725805040c0714009641c02042d4000c102d00c88190311200312406800c040c1c0b0080c2d080b43c2c00400c0080c00720214894119950b0307042d01e8400c581c51a510041d1808e40d161241175a860184500303070f044a540b80100b8515564058646503101c9040200d5030115081d041000480755100c410905c40740803031100f50388100e0350b10076405a60b4154402c0014064010b5150400080e4200703456148405803c001502e04440c801c3c0c0d20301c0704509490701203502c507400012180c01141b12406200046000404420b40c4406880f08480940d507660603015110341c802d07409102a03140c00032103100d070140240b0506401c07040866500025051201007880d0349403541000c0c912844500b0850b60070004224030010003036400c106130032a60050068151780e50480301c1d4040d96 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 849888893 1250 849887643 849887653
    0x1212031807080703020d060c0c0b010603020423010207181e052a0a051305090a0b030609010b030705012006190e03121518070c02101e1223040302 64
    0x242d8210000380e040100c980081c080c01055240d92603410007015480c14460400c44091405030100e4035001602d4001c204079070380103980c3d904d00782c075003c0700d010b0010303c01c2c600005c07901c801c00c2c0710b03a80002c054080c0c44048080031070a00351440350324000c16046040f04078104c2c0701e0a03d240e0f286944e41c030980c403540c04042a12411000341d401a418910203866413007407241d0500a001d5054480c9001c0e010741650307116419003c0e40c075603002800032003046415030705c01034841d00d01503001c0c18280901c94208031700800038070004d044000065181c81c8940100c0d410072946107a9840d603002003110201d04000813009035a194103001e0119080b403000c121003000780504186000d2a102c2c8000102c0340e40e20b0405007680101c1d03d0700308014000500000d00b5550056141c0c00303c4084107201c0e801c8500986803030311000c62b0240c0b035206100611440c20110b0702449111005401e00050300c2c0784d0302ca00c402140c6049459000e0354a0b880000301801c40345c5007503403460a41d81d60461980d684416000741e009408880b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 849890143 1250 849888893 849888899
    0x3c030c0d08160804030f050306040b04051311030d2c10020d020d0207080c061608030c0306041503020105120a061d101a07080a2c01081807051212031807 67
    0x901c1005007550005c0005042e0425403140e1885400034540124000f400030031002c00301ea00040c2a11000d8460802c0c5403000c414460820524210581d0407446c154050310065012603c041c015400a1201d001d44a541a11702189500803072031440d00e0401c010000300100e50b006800a40e914010220480544104c0105145281c00050000101c6903208018040c1da5031143c280040b640008600c6200e22069104403000141d03100e0103544640c0207000d21a45131314000c401c000036900c3e1442032441b1881c600c0f5091015036400000c4822425020360391101d69212580d86100038031103a03010001621041143c7e0107580101c9600d58000c2c0f80400d000303192141c0f030702c0e11103c40c0f4002c1d007030107141180104040f034002142c80001c1c07d8040c40c60704008545401d000d400641400d05050345444505184009080540c1c200861a4102c144032408000340300c0c0c540390a5075140d907540141ca1040c04205107164445404001801506219041990310f030304102d4be9030700daa0080c0c26640581da0140e05804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 849891393 1250 849890143 849890147
    0xf020c0d020f0706140f0f03190204050d06090c0e0a2c07031b05032d011a0f0d0f0f0c1a03070e03032a3c030c0d0816 52
    0x1c403422901070283c44000e00e400c00664510f42400340d500004031090164000c3e200140703014080e503592074040550340340351101c0b0304092400e0802007642601d10520040c0120b4032000361600480e03500085c00501c0c0b1105040042c400c0015610402211480d0000c0155005103a0071519a000404840300300101e45010b010340841504200300569610504c030070404106094101c003841d00c00841d150b00081c0d01d074004642062042092904040400401e800d281c5d02c9084002010346200402000455058440c040701c14030000c1c07901c1c1c400e4075022140800d0381e41e040c03444292694000071920748802c0a01d4006002c034071001e02990185088800000c40140b000d1628104074050450140345070340d03200c02a20080f408114454040c401403120b0480300705039291f410a0000c1c8070984441103418040300c0ca02e814544880c041c003424941550141030070801c1015035a409100c480301ca405100103009900e50b003e000b900010502c5042500c088464012000500807c05002045c03e0880701ea001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 849892643 1250 849891393 849891403
    0x30a11030702130b130c020c12030c0709200d0605090709060c0204020310030b0405070f0506040807050d0f02090a1b0c121d030a06020c1c05070b04150f020c0d02 71
    0x8040d42020f00700c030703442c1c1c9001c84540c006104000b00038950306460301110380e8102140d0312a80c011015a02407004481c40303242c0070888040c01808039000358030b090b0141c10311641b522010300c200340240d515030b5200d00d00c400c6203071031000030480c801810035100d00c1c1e41e0a021014100c5889524001c429180120b100346110b0728030748064900d19140c80c0c40d040507030b50a000003540010541002d2280034900840003a000c2501a8051030140004000c51814066405a41c003820751217280b00c1c0408110401100c10049000740071030b001110900d8040c900d80c10003800080a40d14001c1d40008504104205807080e58000a402000a040d96507821296502510200568171026080101c0b08081e40e410a00c15a801d1102c0b4101c00480741013030200314042480c003d001d1004603800c0fa00070a27502d0b41c8034030400589000c030840c000010354030903201002808034803a1070009803404118800003000d01c1900c1e0b007002610500c1c03081c104000914110200f0094111001035030443c040e01409101480c40022 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 849893893 1250 849892643 849892657
    0xa061b140304050312041209080d02300f1908041e051e030703081608180102070f0b09160f12020411070c0807060f050301090c021608030a1103 63
    0x22944840c514008036540d03250802001122240700c2049010003a075001602c40d0b000f58400c0b040040c44000f60003001d0190a09608404816070060024142d81d81c2d00259620840d03240349058524580e50100b1054801d0401c1d100488200307000070208600010035008003205c1450100503400d41c601800c0403120b100007624003034062450036461746007080c00c0120810446203da401c80311010000200c00c000c00300901002c030200c0e0004030362403042c0358115290b968080c09031003142d520a40c032036001500900c001b070121945039980140a0f2844042541210b0045801031400c0943c00c0c214a84024030b1101260041c1d4540500c62000205908103052203058400380b1076004034403820703e411031151a0701d02c00282c1e4842c0d02e4010380c40c48040d05200920f245801603071680c620303500340b020f411f20f400c02c15440802045061030503000643c0e404402d490640d0801c2c2c00110740c80800c11401c910305100862000341181d078011b030000f42c079100003000344103142071500c4003000100050360700340d280e00801d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 849895143 1250 849893893 849893897
    0x50307031203090b100f050306010e07030c090e0f071106040201020a24060306050a0b01053604050f16050906041e170703020411030411010e120f0a061b 67
    0x1010a100044010744080208041860001420000d07510f410781e80300015200b10008180c418002e0060074095440030025020540090113154500700d100300b00f401c00107010340704050b03851440c40306551040180a00601035500341290a0411b00f0581c007581900b80c4d600d81c042500400e0b021640d10010403034030b100e10f4058001c2c240002d415299000c003000328141c01c2d01c01291000d44d5110410052085c1c80145010306400515881e01d0b40100e4129000ca0300814140310341800031240b41d060410000c84501c20024201c0f18079801c3c1103242480600e003c1d00144d01900b084100030720400c1c05a4a54801c0034851407016404081d05030942d11845984ac2032a0401c0f0704000520051b20300c14245801800305801c0711150715500c403200341c4130001608451501d03070015002003041d807800780521a170510782d28504070315500305540c49100310308007000000d0611034900440344040e1345000018061121a80584082c84005060141c845801d81d00441d07019240807000390048c00c4016400c05101095 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 849896393 1250 849895143 849895153
    0x10506091501200a050c100c02210a1e0605060a0602030a031503140a11150301030b07020c0604171501030302120d0e010207030e132a1b03050715060503 67
    0x2900115640d000d90300400c3e00300d1051198603000c41808101080c10640604041c000319000181041004601074095030200038138151340c40c026980311416144403407884000d41119002841d001030924901c581d01511411810308003072010383d01c0005130341324240b00d14001c1055656060402204021500541005a009020b440f00142c000c1c3e2000518405041015074450303920764400003102841948481d854116414110401004815000340110304550071001c5211608031503104c1d000520001d130582d1f01a0740402c0b40c0500a0000c0010072102402150307403103407030340c0c1006c000c10031072600c4440b00e2080e440e24200040705100c019050b2945603000c1c11010351904030781d41542c3c00803086100d19580e030b9500c0603c100001d10087c0081803107502c0d5079000c040321a003000014180c1190790310307200f4200101e41d040044e0390030f0404504c103410240b02e035007899480f00480301e007009142401c10b1221002105400d15400c50081d0030742d00c2c80b406040e6403910b80d54927008280da589114154045e400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 849897643 1250 849896393 849896431
    0x1022b050c090103180b09011527020a05070b040b01050310090f06320105120a030f030c05041a0c0c06130b03040f050105070c06060506040303090513150e060301050609 74
    0x801e0704019041d1640d17110741c4041c0e02c202e840304848054107031210011607544400d01041e29840c248000001c0400309000030403840e2071460721140c54000302c001d6501c242e0004408550070b0150381903880e00342e0002407a99403481d0515201070100d00a0003160706c80c0c4a03000c5103411000b06400b810100c541d1000001014110302c2d647d2201401003030101404020b003c008040e1200b9520320604c4200040d11602000f5502d00401d11100301c0e14800b2007500c0d0f0308803029030b030013080e001803668851070007502c2c000800111101c0d048078035000340d8010071310360548040342c402c13070407000d0000e000b904000354281d0305501683c1040042d54410f4415040520096080420886004002640d0f1107070143d49080150101d07552894210344013100d006002c25981c05241c01400013501c1000d01078001035401c10303c6c2c00c2c156200036002160500c1005d2203030411514200c012100703900310052070311500099000f4103440f122040303030f62081129468025841c007800070f0003602d05400464029a2500046185841 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 849898893 1250 849897643 849897647
    0x21006031a15060d02071e0209160306050612010f0905010f061b020a083d0209040f18060b03030f0a0c052b021b01080105130b0301022b050c0901 64
    0x14002c00e5002c1003542c03500001d5050300c1c0d5400410340d0710644507005a030b070301c803920308031f10f0005074229509001088441d00da80181c03a40060a5001081c61520302680440e0300b030101c0c0684901d800050f0040c501141c21a0800c1d03140c050700f03041c0e86488240039142a215414002287c900348204000a10b81107810440113000f40290303445000c60f01d0109440c030100740c010aa41d03964661000c1110b51188605c2c111a000c40014504822400103200d401c1d403410160440180440108005100d64009200302c00381d510b561200e00d40003024081400764051070940c0980da800018000c2d03404a00342590362403945000303c00c580000201c014042d00306807640700300300e603819000e40c000c03500c0d40705540e400c44030700704c3c0200303841e0680c8030b1044036045400008100904040840844028040d200140300307804e40e8000c085c82381544e0702542c948240800185985000d0480c3d9203441c1d415510015240074a8842d2042ca02040307085e11420145c4445040c440600319281180c00340d512050600c1501c0b4558 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 849900143 1250 849898893 849898943
    0x5070e060a0501080408220824070f0c02090406140a20091309240e0c06211609050102150a0b12070801021216120906020c030706060602100603 63
    0x10301510401e410180c82080d1f41a1405c00c003c0c07000c0b110a68000108480c0008000441000c480c407200709001c0198020f0b4912520000740c083d03800e10003102e0096614512075a1601142c507001807074a41c4608060074014010800b40400c0d07552051180b00007039081400b0f0088400301c80c490787c0c11b044a400c00220507010303030f00100c06655100c0c801000c0c04044680324002d100c20a0f004000c0141c01b44800380d004c2121401d400848080a4117010748010801d0f0040791500b4000010307600c3c0b568400303041d8003251801c0700840d40500b40680c8101400440480304071200c00e40c5003d91143d400d995203c00040e6580c42041c07000584100881000617445402a040850780c80c20280c82145030000000c4030030706095807a00040aa69400700e0711801030a11540312036001070000038055031600c00c103c8020607607244001469111511000c824081040e81c0d8125110000074000b925241d038001d10300343d8003819451140030014070070b03e036061001c2502849401c08a03607001880404c3e10390104070740a914 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 849901393 1250 849900143 849900151
    0x1b1911060a080109050c0d09031d0103090c05060702010311070c26060723070b1b070b07140d0c050726040909020301060e010609080615220b12010905070e060a050108 73
    0x3a040900047d01c4030160760061500d201d129842e2030f0202d0070410b418003100800b8900b0701d0304040c140b108550100710304501081c1600e000381e4500d56158950b00040e005003421004041245038005070030014480d151200d082604e84018000403803901d0b4206644502c40300d81c41504d459082a00461901c502a40e5070101c4012039001040c41141c001d001d040c40d80c1c00c002c0341503c3c1c1749001d2042021600807505c541e2910101211814104601c540b1140258180200074a05200c0340f00e61096244a003441a14003030340d04100c09000d560240c0740010515088200200c5a4580c28000c0400a22850301d1440074101c20119031428903140c44445d00250104103000e98140d581c50501040c1080c86254240c06000340751030781c0c0202803170456824686800100b03003466821904103280d080d07a440c1810041280c1c519420a2080e0700070198442c020008141d005500910a41d8444503840d81900140003960258055658041e03907480389130303011001103440301d0b4410805582440f0541c0650084c9801c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 849902643 1250 849901393 849901411
    0x703140f071a190e0a0602030a1404030b04030c1103060103060f0e0c011d01050409050a0c020f0a020102030f1b0a200909030910050d0908130902120406021b1911060a08010905 77
    0x4c00c440340104a1003503080d0810b00c0180c00002e40d038002d00d90403450b20b0b54460204009541341c030b441d6413920741104401a00090400506039034050070b11100038064410028020103413062035940340707410801480b0f00160005094144002c801b03e03c0008a4107940020041e10b4101d40b50300710322400340c844007650803924180181400003050600482c81602e20404400300c000a9503912a07901038a0940503001e000c0d1194400c9040b540141d902100b5a8a5501007648260301c803828403135134910300f80c103031100b80b00c0906c80c001701c2d40107202c1d40f0490520f001a406a1400100030f5060501c5220401101c85696907402007000481c02d0070220240e84d90b103403407440d0039401c0408190750801600c000880540fa50280400c147d5140000036112030000c0981030011854032210460944515400900c090184c0b80d002c00c1e07072100c901c040103180040f0319203d070a40f002c5072400c2c0e1800d1160b800c141010f44003c03050418484260401c0300481e03181d107880392140c0c5180d80c40d000640300549001450041c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 849903893 1250 849902643 849902657
    0x5090a0606030f030809030a120506041e1a18010b0306062a01360219180506010e0102060a05071b030503090f0606150c0703140f071a19 60
    0x420302510a14000d10322400c9a000c2420745424020100e40d0003814013150794008102002c41d107900200c0d0394030112020344004c01c860307481030000f4004081e6180c0001306900c400300b40c01c00350714203517000003041a0065100b1050038a45814004036807005204140d2180215006014000400700a56400303080113100c01e14109883d4001c15804030301e5062081d04150144110390048400c0c00350750351208466001203c3d0403142180030144882100d400000034181c24820810742d1100c000f4031002004003481e500603140e0b50013240c42090039041019036168504004180d013984154031000d83c17440140d0040205868070080305000705800783c202014021f10b1a046581510004408107040340261507040c0c4a10b0041089428130005101d204125000041041065640e41c2d003984d04602c05c220b400e589a5400c20340442c0f070022103030006007810b03c2c581101d08040900285000004050130142c403001a6180d51043c01801211804014100b00340a6451540e00c3ca51440102c0c03d4036180c604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 849905143 1250 849903893 849903913
    0xa0b09040204050402040b040914041a09010f180213060e07140408010c030c0e040b15070c3b041511120f1008060c0406081b040902030403030c050702130509 69
    0x8080f1b03032050740412a1400085000c0008104d18402c0c81d07106504030703040450f50324040d40c400082140141003001c5c0c600e1907401090400209510110380d0301c0b0b0814080103410903090b42c0018940b140b6004030b00c00c43d8a048540b51702c1010340203078805c442c042511048143c841290960703000500a903000c03c00340080c4000201c03400d09004540e5249070350780300022004421907009002d07007001c0c00b00c5d0740940c1c103103188801280c80342000d8407000181c04501d035403181080c0c42c3c4070302a0125036001380c4191251038540100c030400d0490842d42d1189492654404250882c4c0d0503448103070880c0d0142400c034030444448040c08694002842031740225015501d8003030880c10350020020150761695201012008101e168030300000380318060003048006180c00d290035101e980040c0310314011401007242d01000710340c00744d0f001c0001c1e004061080543c1c1d42c440f0b8440880c0380c022741003200c0030b40c002801c003818400941e00501c111042e8507000740c059a03089032981c0044014180242400c2500d12843e4011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 849906393 1250 849905143 849905149
    0x30e190201050f120402040b120c0105031003060e070815130206090d0206071a06010516061d0703050a0c0b180d110607050a0614070f08060a1d060a08010b0a0b0904020405 75
    0x3c080000541d000302025080071b006020468a140c2e100c980692046000c41441c0c0d140000c0b10540400240b03002980d03070341c461040280c10341483d071000349118200360300082a40d4010401200f0307229183d0840d552002001182d10925900751801e2444103681c481040140c00c0450003045000c1c4041c0045841d107140d0750215115a1015a0a46180c1c620409465072078280704515900a2000d00c5c0107400e2902d141240440d14000200c001d28165890201c1c06149040140c11007800d1113060541d15283c2d500e01780b46840e009044070888011018450104204020310250b4118203241a168500c2400c41401e102001c44640b42c2503510030000b0620782c54075911742d002006841c2c800e03c040e105c2c1040c54500001620900e0184544d0b11003580d0810004542c0201204140b5000cdd203802034103030b25110042030101116801c00442d0708210b808040c01d4018011099004803011341d51107081d1582c1c0c080c05400c9600300c2024641c09a13000b0010040c01200c68040e211840d0010001868a5651800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 849907643 1250 849906393 849906397
    0x6050114030717070305061e030c040209030c1c0302100501061b050c030d090303030b090f1f080d0306050f1206180102091002010b090106140306060d1508010e0d030e190201050f 78
    0x4c0140005e4883c4c2c00c21544d810144060702c0000d890300d182c00a13580c1480c00007603ea12020006500a90380421505440c1d50200104100e041000d0030040080072081c01000c0d025207034000c2a00588150720601416000a10a10341250b0f56a643c1c8001805001a00d1010503000740b81a60036110b0660602d01e40da8051028071860f10399a00c8030b0000700d2951a0213801d42d0020860248910340100c201b06404080300d00c0700b9880740301c030150912480306c6c6001a80d90800c0d260040d907490721803a464000a542c040d030100c1c0a407041110f2682c1180115801c001e003129003030010002540000001c40c08017034204055440054585002508102c03040c0041039500c3c64065100005070344404070301c5814140180fa035405420700d0315006500349010f210b43e011501c4050a0b59000700c10005040c41e84411a510001209900303d01b1381e800c0d190b079054001d0180525910720700b5640035100c078808059029111300003110f0b0340d040c0500f00b25421019180300e08600600241c7c103110080003003403402e80b80d00300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 849908893 1250 849907643 849907651
    0x80607051b0616121b0c080f040b030a051302130f060b03131101081e06010905040e0d0815010813050712060f050c0702030c1530070306050114030717 66
    0xa0f003c9042c146104008049000c40442010f0b84d514001c0007032040b05007000d13904104c40c4039040582080760f41e4030381240584079600c005124450049004a8200001c000540c05400161014007041c0c68401100c0b1304588881402903114902d03907044a9942000d0300041803400703074903800140150303032010303241c1c2180d00850718188105401c016a00401c440c001005503124002e00c3c0140b0186008011741004042490075200c8540340c10f0b0009843c1e03841084904050600503009102d1902580e81c02c0b9594480c1c41921400301e5031103000a00c2d100e41c1a0703640280a20140e40741d50041d101e58094000c1222422008d0750f490107190b0001c283c8900c00e0b2003800c0080d100c0c141c00520010304009000480b0340141409035841c2c400c001e9640540d800003034003082580e0450b0a291855145d10840c54248590002c2c4545000c0141000e420019034031402c6050032441303112089180d4030420300f10112a034900a140c0407031100305401041c0301158026550014260a140d00c0c020044002ea62054004032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 849910143 1250 849908893 849908911
    0xe0f010c080609150604090509031603052d16020307030204050415200a0509010c21080604020301050303031914270f030405060a02011d06100807080607051b06 70
    0x10922049041c1402030315130100d0920344e00c2040035a007100080c914801d611407001341d15110000301e82200010700454201c840c0c1030003125440e0f90f044c0f030083c0564002c4079032120010781c1d0f1000c03012440464104146000030f0840554174006001c03101900148801400b40c0e014410140c1c0440161501c0c800d1600803030050242c02c0c0f40b000440c001c0f000303558000d00d030106480c00c0f0101d074928505540058506007040c030700b8079603254a04440101c4801603024400345c4030f03a240140305c2c140c0b48103140c1c0740780e00303841c00356186c0344242c0e9400c06100580c40300388a540d40541c002c10001d031000400f110640d104029006d0046120710400344404600300302591641c20400300c0d4810a02d0001d0b4554018080030a60400b80c501c404844010f107403640140d200e528000c1c0d10000b103c1c0d08440c401c1d4803402580d5041800701e0045814000701c1e90740e03600200c0f039502580540046c042104030740016000d044400e418001d000c5603844040407106904002c0515111050f0b81075401002181400810b00c00c0c3c0d004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 849911393 1250 849910143 849910157
    0x402030106030b100e0d020d02010e0d08041a0414060a0516060518010b0a0608071101150f08070e0a0903090e0f04170c1b0613080708070603110901030e0f010c 70
    0x420104030f40c084c030030300034001401400403200100351100140d4280d001d404841d0600c003038481e400184d665502c010501c030392005200411030b04004030100035100b0365031944100c003d02c54000c2d03046030300340c800c6010f030a106a00100180181d0720f082401001040e58a282c814141200f041c1035003035003484240304484054440d410090003031030030001010102d038110000e01061606201240d825a8a401150100810440083d4609000d034034440800d080302c10003009014100b0105d07102c1e044c02c50050b82c2d15004a94400106e1102c0092050207603013001c21070700300320344859452070000e20041908509001e11540c001400645c944031480c0705508648030302e9214039061900c801c550a0b40348080c4205101885100f40b83e6100041700494050790b9410103205400e600001461405803044034211026803d2004c0307103851010941004580d01070003125080c03600d40c001501a100310022000100c1400c3c80142c06562003a00b140499800400c01d5860541d4105c00322800c0d074488a00150100307160b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 849912643 1250 849911393 849911411
    0x90e0a020c121308061b0702040f06170307021503040c1514281b031d0306180706021b0103150e0c30040b0a0b0307030f0b0702010b0603070c0f02040203010603 70
    0x418000c10303038440c1c4402c1b10342c0c40c6805101e980c0304107801011000790040d5651005c5000f020344641c460000382840003204280c25040e000156500d5118400407802112034001e80c0c4010b40036031003504d000d99409034900003041c0c200244211300c040e003500d01104000301c2c100c030700042c10518001401120400707000c0e1241c0002d4034030200000c0d11003800c0b080411510420140c0351001c2182c03c010f0035641440c0c115110240700e0451090103c1d48260140c0c07500400c41030011055030191800159143c0300143c1d19030300d40e222416a140c101e4080000e08103500c015400185600c070b0390100e030a1009112840c81c11030f480322451082e4160840e62200008400282041c251030100003155078241e101c0034801c4009145550280403000141005084d400030801082e09508c443c3c0081e60000d101400f111892607032400c1081441021000650b4800c1030880882c01c590b00c18001c420a510001c0c041a1940e140c03800d0880b0f00d601d20003000d03604540c07607d91000040e0340d94001540205001d54012030201a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 849913893 1250 849912643 849912659
    0x30203041b03020a05040b0301060f14130c020613050a0501050705031911070f0212030a02030409051806191523030607080c030402060d090f060c090e0a020c1213 71
    0x1008503040780c40000040010001681e90785501001e07201c060f44c001c25a4452603020a02605417501f1080542030a54408600184607e46e8959840001c440c3c0058403003d1520800071600c04035003c10050300418001410204400ca26800e00380c403c40172103542240a42350282114410345101c00065400814040e0103840c000c510a52250500420440401103840c03080c4c09100740c0760014a80e04d0101c3e1500c095550b548256201105540140d0741d0311140c110009440b40d010b4000e28581500e0900440c0081c0000f101041d42c000781c4c0401804a51141c1e801e41190310001c040041c003003230b01c4200c800310480d08560380000a00041c03085c1d02060300384844411158002220003806a40114200b2203159484090b10786c1140032800d129550f51584e00114090388111708144802c18140001c900400441d01c10307100b61203006140401c4881e800398411903d0f488a0320405030110310003400b145905042e540202903e40106045421000800c07000e140030340c200b13040880e2100074101e000c0003009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 849915143 1250 849913893 849913913
    0x6040f02040b01020d17090313150f030e0309010c02030c120610080f2a04050c1209010c05070201080c21091c050706361704050303070f05071503020304 67
    0xb007400504000c01941d50000c00c3c41c803034501c150140080003004502c07a1141031084404520200c1c4081c04099180e242004409012201c100001103c0810410806119110b0383c004804840045d501e0503a82c000111505440607000743e03854021850a15056541c024030000341065080103030820307141a40401148001079400303030300076800005000302202e03c0816440310382c006074021409920010f03008080300c2c040100c1816002890320051084485010000d400982c1500303551b00e000341e4649010340d0988401400400114030b06018010041d0300403050035510a640305c90640c01e10291307060044d851111700c1c41400c1005100c809100c4402d00034031190800c0040c80561080781124a00c2c02415882101d6014101c03030703900c14500c08100c41d11140c10300511400c444403011003003a03420008804040720002c48030f040c40102c00c00071004030002540e044410040285d41040f1a946409103c02442d420403611802103100200e0660915030041c2c10011041c1da0040e12840e05140c004460 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 849916393 1250 849915143 849915161
    0x1508010605060f0307230f1210080c0d030c02041a010f0203040e0c070302150a0e0709060302130b1219030806030105060a0306020c01020903010e0d0201060e0c04230306040f0204 78
    0x78141080301e8102e441401041326002016072070040545516801c10b18024041031481400741e141c0080d4009260700c540b40503103c1c2220000440406480e0300c1201400788155105500d06030300459081100e80c64080f12080b5000e0103400c020111900580c0080d0441d540440042c0880801121204295070b0201c0c10004102c107a0004602e4581449144c04018000400402c4400340000307201007018420b214080c49506010305e000c507941808518240605a890070f210240d01c24900300007000e070a18082e040403286c001e440300d00303104034412080d8058130b08980c0054101440700300c00951200200461990442d000b4040b1f00010603a16008000c0100542494400d80c10841880400d980e00300c0310710200d030b82c444030060369880c00c3e00c01035029014203c2601ea25501e02104102e200201044a42810360260b00802c9a20f448801e411032400c0c0c10398010b0444802880240080c00c0c4503d1518000b0351045c5c065111103084ac00080c1c6410800c40d03003100e803094000019000c508041c040c1e12a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 849917643 1250 849916393 849916399
    0xc0602031f290c0a0f060f050414060c070c1703070f05061f0b09042403050304090f051006230a050d0f020406050f160c06170f060f0402090f041508010605 68
    0x2400005440c416604c45948002810200c42c4c00c0000c000c02c0074541c0500442518540d00340542e01d003504210035004e0110310848058000c00380020054410801203801c203641c41b004070a8000c0c04c240c141c5511075865042a13045202c04c20400340424440c3c0305800c0d28620401c02865031349840d20344016204c0d07428810141d1301c181c00800f4014001e016082c1c0c1c00030781050f45d00250013080180e41d200308290070000942c1c0c90440c14408414000044010302c141d07003040506004018030039401c0e030225401142c05070002080c8240600006110388a40070701d07a01c5000300090030410b07403841c1e04500d5110800304070100d14002200740e4032100d60f000700704001481480c110b0801e890258068440c1c8610107040703604d40e4000130210004610818900002070704000e88403a904c1e01e6007405409440e100c0424096004401d0001e038001c1c1260000078442c000c00791409000032003038014072001c3c1d0010031013580c0c0891881c1c054a2a034665200d14a84809460004c51042d40f0300500c180c00c40c1c5150700104c0c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 849918893 1250 849917643 849917647
    0x4080f210a08040201030603020616051c0e2e0c051504050c1212040e0609150a090203090c040c0906030e160b0306030f0a031701060f0c0602031f29 65
    0x40003504a03040d2820001d0a080810342540c035440101c00030841c035040254011004503002001c4600c80011030452032040c410cc1c1c180b50008c100382c0c0060003c40760241c0c0000d02c80010710710306051081440c0302d912181500307400a00c144030345001000d00407001c450005480240f052040c06030400018284020b6062800b1090401c7e441c0c1607101c030300b0f03055410302500c240b481d01c0c030031003c2c20882c00340a510304400c60313a12507490303d0005069920541c0c1044c815500710f000314031128041547c030600c5a00051455021a10b0410404d0103500014a841802e0180d404070032640e0f1201c0c05440001050395580d40750250900700701404031152402c5081c55548244823240441c03c8000c9001d041e24040d200301ca4403a50b903000064a040740f010340c898847d001d001402c0040581000c1c44030503d090311002802d86070313291f00003110100c10205140000460b9645000302241c1154011900303e030703440740e0714545500e2a00c115002180c46600c04030f40510107000488070030811800d8407a413a040125014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 849920143 1250 849918893 849918943
    0x10507080c0307021216020603241005161e050a051c0c020d0f0510090b130f200a060c0c060309030f030c021f02030411010816140f04080f 61
    0xb50340c1c60201d45e01c400c03000000075540c11401020f188180c00386030700404d0304d980c81c1380010454000780405000c0a03503075008014410710603c0d00c064212940e148076601c560900c00d0784506400e130700840c050103039001d610b49414100e9004821041aa1403400751005041c4403907030f840c02070301c0c0c070403080d1343d0700845518407032081d105660200070100d07520303012a854601110241010b403400340384980c00420a02c2009941c81001442c0d8103c1d00001c0d01444004107035a49500600821681d0310034010002811580b041c00014440c0858a0013000c034684c15540c00324008010071001051138100c900032820b9000c8550402c84002e1003100544102d10301400480120f03640030317120324010303a0701d00241034071031038509000381c400c102540e00151001807000c032401c4100b401c18025030098a040c7d511219042462000b07502a6441c140641c646800613200403111708021140201420405000344204100c03502c5403030900300c00350002e090782002401103072007100d84e01031502c042c1400816100d501c82c2c00c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 849921393 1250 849920143 849920147
    0x3110c0604080d0c0507080628060f03020d1106042d05091b0d09060c17060603180c030109032712170d090813230f12030a02010507080c0307 62
    0x2008007081c0f5080a03111050545002030030a9140e0b00284014495030041024801c81108022a442c0000c203500e040c40d144125a4400c8d81e2060062005c00703e0744140810050400e001030310025400364a010041c0c08074000024102d600c15030105100300d80c0580304000888203074503440c4441151802d801d42143c544000b0580c10300000300301100000e4002c03119203c0c445c1d80802c4518440900408001c618003500d042030003005109003171400a01d51498020488120400d41c81c06210000c10040c2503a641901c1140c4490003200e9610480c010100000e00d5038409000d00064a0f200f41c440b001e101991500059150040d61100340ac440d40941040020400300700403100b29580005140041400407104e6402d03e11a00d040d2002441c82c14048000b889840350103415000000c80c0040c44c0a903440007130307480001601d5001c021044103440c1e200b0151824642c4112815005081010540701d440b29141c1180c1180c014100540d4445080005481c4d11070b403c2544a5440300714181581040703100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 849922643 1250 849921393 849921403
    0x5030718080a030c05151009051602120a090b041202030f030a050a05030703090b1602010f020f0414220614100f030908160309050a050301112506020703110c060408 72
    0x10b03060100c04d0f0301c00c1050010030702a034442111044050445d500304006150820b90191043c0c0994500d000b002c2040084110301c9100e1000d22a8000e080748001700140301620780c85a810041404a581350000c5d0780000c1901410040600e0460580320400d24010b0606000351a9445c060581040202d29407281d044002d039006c040091030901c1d1a940e070140158004c15400901400d210400d5081040004010014105802c1142d00a001140701c003103010041c1e0282c083c0c01c5024681c00c0c0320074000c1148515110020110003881c80c82e07001c408510b417a07500c07409896140039682d2030311028000101900c100e21941c8005890034490001c1d150001409865090311a004050b103071008031050002c24002d9880355070840c7e0301c2002c40b86040c50040e00c4030003281300703c50141c0340114002800d4607040c410a4014040004d400e0700d0103c00c4e141d005210010742008030850300d40310b285e000200720188042c0140c1442522804805c1c106095118039003451103115520403801040103010406010903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 849923893 1250 849922643 849922663
    0x1150519080a060302040905010b01030b100e0d06020915041517010909062405010306080c01020a1410110a03140405030a050a20150907080606010c06090506070503071808 75
    0x34180303915494194141d0043e00b540c0e44080d62041c10300412000340041984540c2ca50720003600c041040c030905100b441071091016010ba070108010203200902070511544a00500b880f800c801480c0840341300000d1402d1041043c106070090002c2802e0101800030a42411347c04114102152001090008041516014007032710003031a0b00c44004104022007508400080c0120f0141c403c1c2014800c40368098890b03ca20440780080c1c11300d28005641040490307080c0500106038081c2041440c661a108a0300b040300b11107001c0c5200e0a80b200386008900d120305030031021108a030943e41c010481d0f0081c29101208581c0c8034079040b01c414840050000412119041c915042c07549d01c0780f1070340800342d90284022072501215100b190700316600d12004610a52114285601d4a82d50340340d00525075910140d50081c1c98071a40000c012034451340c040d4804d8443c0354490200458141c0380380d07841c641004015100c203004a0303800b200348859141c00a9a00c0d40000200306454425813a007246070717503a601c5a076 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 849925143 1250 849923893 849923897
    0x207031b0513020c0a020a06030e07050a1503180b0f04031403091b03030405090412080c0c07140a1d012102090a02071b06080912070f0b270601150519 66
    0x94100d91203070085c411100c12a80040010350840e80c0e42c3c0b00540034140036541c0342418000c1a1021603d890030144000c01da400b07a8200f0700c10000c00082c260300500c500c440d00f120404c43e000c0000c0005901803030851040c00080c0b030642482c1041e203005085101d0543c0000942002402040391070100001d034154041c1030340401211038038082c0b011034194400c0b03420030342d00024160100030a00c2010902d400d8444507039582d000c000c0e079a0f041080600d01801155460310b4014003c1006481d03d80c0941602c4c00303200800c80d07401f1036914070b240150000e066409140c0c5201c0da00c0100710740c41d481c201c444a010100000042c01102580c00100703540300c0104050321996020440340103000012042401d99109940c502d02001e4490101400e025000c0b2410304041c824031032107582034052082501d42e180c0d8080c00030280380d038240d59488104800106402e00c0c00109541c50100c045c00906090031401e0300d8001307804154103041000600a5071541c0c0b05c003d1140c108082e2440710081c1d550512880790f18 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 849926393 1250 849925143 849925147
    0xc1908030613020c0d02010b09010602031e1c2f09060f0c1603030801140f0a030f03030e1e1e07061211072f091303020f0d0207031b051302 61
    0x80342d00740009009403000d0822a03c11443d505e035450f0f8056202c2c1d180d69004136240c0c40582c1c3da92804a940380310b034010100c14680758100c9140c140303a43c0c0c809070050483c410128840100140b07103c02c2140c2c0e08001d410b2400048807030b42038a031081804e9032a008824146070a107400c8001000c95100e2160604000c11504000703003095115505102d260300c101103a00340410156900d0074000c2c50040c0030700515488c001e541c09100d0152500007901034401401a000018203441d6498400d502440c0180c02d03410b25840c0c1a44443c80a0144868460070040b1100c000b4119075400d10030b0724080310400b1310142110300090151a06d040019800d0031555945842c4580c40710101d9000e01822160780c000782403603004513401c1e0810482da503605040700f03030101d8401401106e05c44251200c90b0084403054201c4034040c04a03e6101c600010405001e0090046501d86000141c91030320308001080c1100043c1c00040050017080306d041100903900807088082c1000074108000180360098000703103201c4030f40d80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 849927643 1250 849926393 849926419
    0x50a0b150a030e06271c120b13150e10270c020706030c0203120115170f0601080f041101230c0d030c0906020a020609041407050c19080306 61
    0x200f5007010201c00120740a03030b4000c0c103242030070700744050a040e1003241a910802135402e6042c0009640ba508000141c0104861800d108007942c0c100f90a80260f08502d441e10002c13580781d00c4500324000c001f580c88030000342103803000074103503c9552150401d5402c219101c00780b01468a80300c46020554801741400c209074402e002d08644000381070b200d00c00d2502d0429020003450303074000c10004115405a10180600041c0f13840c100c2c0c491285c5140310001101c520018044200320f402043d4000d10141490000d025446d403000940440c1100c0030185058218100082560320041c0303c3c3e0410762809504400d418543d5401180e1901c3e54070701410420041e076401d000d10b60480044e60041c1410400c82d5490094410349503c88981360040008203082421105200b40b14007140c0d02281d0180d4050402e024481d4200f0070a90f019180c01a03005850f0040c1c40b80000c01e000403e4003841440c3c894581ea41c41c00c41e401401c002001c00303030342c41c110020f40c0e900020907010000c60742d000004952420304200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 849928893 1250 849927643 849927647
    0xb0103020f0d0506152403070807090f1202041d0316020f0a080c090708150409020d1704240906081305060108030714010b03032713050406050a0b150a 66
    0x440c486000e08076100300014005d54102c0040c50030314540c02980d0810740d078081010070110480060300c1c0b03040002d404000240500348100d0039240c0109181c9032012103103035103122038103440030b25410200c1c501001c260000c0031440d05105800c008540ca5440404010724080099160300a001208101540b40b031450b0045566480349144482e10003844564283e444070760041c1c0e00d04908614501622400001c11003080c0035a6140e8494014031050003a40b030240824840540303103000d0200e800c4030024100c0c1c4000341315100480c54440740031204607152494200403c40203800049500b50b040c1091081140340c40c0d200368510103544007030408070100c0d00d5121104900403e9030b0310203400c40c02a1030012420080101c01403001340d01501c0d0034980852030305034139400c0710441c0ba5980c0c0e166208010703e20b103a00340e100450750a0071220f071003261040080c0d8042113440040d4040180c41641e22070400040110781d1245c1c64005110350030411810f9214408035001580301e690b10300d0104d0002c43c00000c03140c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 849930143 1250 849928893 849928909
    0x60e10361425030506071d0d030c020402030a020309060c0903060a091e0309060e040b090112030c1a011d06131116140f0d0203040b0d181203050705070b0103020f 71
    0x1040101c0702c090a03104041401d464655a400308a80501402000c15005845161a00c008108849044440410030002c020385206050b10440c107101050881d9070140c0e07940c1c4041c3d84900024000582d49160071400203041190080c1058182030061201c0c544644001924607404214000c00041201080c00d282003200904010614080b0300010300c40c0c101913120482d41c00316003003910b41c0140c0102040402c8140c5101078416a0080200d0004120444800c2c0c00e80380ea0b2400ba0600403000c0c0c20980b1099000e001000d40c8400e1912020010420510f070b1581e104840006a176508404c0e0804030001b030000083c81b400c49021a454040c04800059890116451001100c4410300c45519a20b030503104100e410301e095640d0300818143c4840018003042819210075103034055450941060000e107020b4020107100d552440e59103561052225041c0c1c2c03200b0846000b21400fa29403046014000c0c19140700801031801c01100344985070003d400d130a034060540ba41164a804040d6101002ca0001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 849931393 1250 849930143 849930163
    0x90f0614030606220315020412060f0e34031a0a180f021806090a0207030c020a0b03090d0e1c061104170607030c0f050304060e103614 59
    0x1032000460744030f4481401d03011300c41228440c41c3c03001c51000b0401d982200300d00507441110072507191808410001040c0e94405125410f81e40400100140003128151030101d03141032515120100c01d040004019600020084850803a48504000350075651109480d980079076003002d01e0101e2601007141c580783c9811107403120039010902034908a560400051000800c030003640201c504d10310064000034441166481250050050b2480303032a59600f40000b50310100e0b003a0101300c05a4091360043c1d83e0401e59800501102c2c00c816240d00700003980c1e81c2071140880c1c108050044c0b203040c00c1203d4940c035441e0601c0d09035100700c100c400c0c2114144000945544da18094000c900002d02142031221a1a96103902400b00110f0b8810744c0c3d250000d41c11030f180d20b0058404a4412054801d015100c1c100030760340688220404a11034076201e529501d0b02c8500008000030a0321800c013440030710000d858011800b0b410355214844540b41d0742c4c4546102c1201c0c01d01400268408003280380c1400204140809 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 849932643 1250 849931393 849931417
    0xa02031311031c0320120c0a0e061c0506180601140403060212160c030203030606070f0b040803070e19060c08162004021809090f0f010c090f0614030606 67
    0x43c8254801c0010020100c003a07004240201c42c0c842003510f01008000d444d01d10112000d03481d800e841d041e020b80e8054209a10035820000c2000c40222540ca8190188c1442001c05181d0140c40c00c82c0e0141c2e42c15950028002402400c0700e0010101110003005002c0d003000e0f003070030501480703507411942440030703c01c2ea08064491800014400d4403c0341e410390b403511580c0601003041050f81e00345812030b07a10b00fa012024005a0092020440904e8000d004000880c80b820023400c03074038070f03076660300055050448054854000c0801007003005500002c0034030300104100c0d010080038114102c0d0040228040c001c000400c10f000d0b01d0841000015411203440200b0300132200000d108600c0c100c011840500058500180005038042081c103043c003d81383c070b0078040212402c1020701c00c0705100140d04024a81800341c8140305070b2418156060184580d030011140c000714040c250080d000d460003089511040869400c03180811045921003080c807201003c22200c55034a45840001030542d0145046d0400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 849933893 1250 849932643 849932683
    0x30c1201030f0b10060f03021b010e0607090503010b030709090c0515040602070f0806071826010506060c060408130312020d030606031b120204030c0b0d050a0203131103 74
    0xc1840301080080104078418035220190307039120301c02d508004d081072080c01301040441005a81850081e00035101141c842c0d64000880900703241c000d400e40d4074610119049402c24810b01c10701950119084000d001c058009010191441010030f0352003680d8450400714590b21660305042100e503440d04801850000c003550040801030100c0303140356010f4490940503110b1031200050000030040c1d440700700d800c0c80d80942450707540d009082e201c06075088124922001c103150f003c42c58000d00307c4000004001c108010840482c208505801c45001400207845414144915004407000042c2c590b4003d030300c01942902e40343c0e81701408188100540000b04070011800c2c991204690000713a000c1030701c443d0f0307405100142d40d0700c0d026422180c2c00907101560606001880140300c0c003440040c0c83c80f080e20355006291940e25154444141c100703400501e400307080003c80c030700000014082d1070f03008400c1690862440c00c040c000e00340c070801c80c1070006050349030300c820312031203a0f4081c081e280100c0c070302000a80b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 849935143 1250 849933893 849933899
    0x1b1806040213060f0806010c03091203110303072a1119030503042c070503070f020c062a06070c110d02030f0309120f100510090903021b04140408030c1201 68
    0xc0d00600d043c2c4013010000e104140081ea0540c0f0500108060607090388a501a40307003882d404e0003503900100d0b000e5040c05108061a80a60b070700308002c43c4104055900c80d0049000c0d038000e416404881c240340a03035080042007101c04515800b00186a0341d0f0200c90700030f81c14548100307401c04014541d10190041c0404103000844e502a25522050040300480c881c0403080100f0380040f0966054500b400064420700c0015652401000801d411340c055004a40305400520001074030380c0d015240102254040310819600f0440c3c2e051918210b007801000350106c2e190410000f0100200100d02501452001030300201c291603013402c2c10141d0360090141d4400d170383d04071442035480c1e01600ca0300d0300420110400c5000003030040b0340758404003501c402600075404925841005800702130680350040c2d001c460700180c10b00140c8101d4407598804d4015000301c0f581250524000152005518091401c0c5504017807500c21304110264020703844080203032a40c072007544030001406030344502601200307180008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 849936393 1250 849935143 849935147
    0x6010e011107030c141c080a03021e0d0615080c160b04060501030c050d02180603010b0a06030507020d050304110111070f03080304200a091a130b031b180604021306 72
    0x2a13050fa4841031926011050300800c0c8076400100b40760312403208101c0880c210019a45400428480d0040c0c81c0145c01c00300002c484004803203441c0040c003564100040c405ca00c80038540240001014000d514616408c804400517000582c0103140d4000c040b400a061205040e0103800c03814002d402080710507040c034080c50b040c0010a400c1c0816600c80036400000905454141c4942e0304140e400350581601d0300c4c0c02074040c001d5a0001c0c0c103103a4155233940d81f80c4156104c00c40c511000348600d640200d00c0342010f00f00039080c400e0f1714981d0ba0400404008200100c2c0b004e03c00c158804a080c6010f8241c1c044100440303040206603040300c2c8140b0481607000041c000c1c00c2014500a60155410310745103152844402c50149010101d2600200e84100c20000601c040d405000d01ea941e421590700814451400244148a80704210305469a01c02003d400c600f01040b900107803808076115103200c00c0107640040c0e0102e05c0c02e201740340000051000515240c407150180c1d818015001c3d450000e00740c8400b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 849937643 1250 849936393 849936413
    0x90a08120618070e09130203390a06051e0a090311090103030e090406020403020607060501060215091c0309021507020102060c040f06051602101d120606010e01110703 73
    0x7503104101d105000c400030a0103a210310f005034201c2d103484264080c040709010180700000c045201c09000c0d85d2401d80542c03002e010101e444941443c044a40e407100d0540584408100d1080048001c0442022800340d140c0342840e4007517540509080380c8481c8a000b0301c1c4085041c0542c0c01401010101d80308200b19008250f00080c0c134410701e4045101460001400404002440041c0000e403040003102d98a041ca42083c68000e805500054034041c0c0f241c000c1210340e400341070101d90640d03544004018032681400f40c045a41c0d0400c04003596800c0c00c03034038143c3e102000d04c5c00202c01c088040841031030500035401600d6040d4040c11810740c0c40680240303c4202c0e04050010380c05070041f0f03400156013103002002ca405595014001c0003a50b41040b00465854001c900b4044092050120200160381c9101c8071a41c0708034150343c0c1880560a850112001100780100071b405585041c100c66003800010502ea44d0214003031800e10321010001d40126000200c54000d10124000c0850100500204a034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 849938893 1250 849937643 849937651
    0x30108010f110403030e0102070305190b4b091b0d0302070e040309030209040b01050406080d1706030a08180f0a08030d0b040f151526090a0812 63
    0x20001d51240c0a1820140d890100c030b14001090200400d00c000303405454655100c05040c811149200d440e580c84528241d1090700d4420940d0140020508200755114001ea2089580d14043c0943d409403101110344800f4690940859135035481d02c1c00071240000c16402d40c80103400340010f59040100b003080c0c40750540420003840d110260100c0040e414040001c2007903aa0550040412603d084810794100c42c014200b2420000500d6001000d80d40d0b41d408507002e14000d00008100d94944000c0108a4940da0b010760540c2d08240e06082d85a80c0024007107000da407007802c0c034a10035071311000000d043c1030f500340c4010010080031030306c0040c045503c80c003164003803c1501c10354045040001000081080d91180c008a03610800414100c04d040d60000700d05203e002c0c0001c2112510070413001d041c0c40f0000308820b6103e58980d01000681a5501082414902400c015449684424000401d070a480c920088038991810129010703410400c03031991401d41107802a921101060505852014161 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 849940143 1250 849938893 849938909
    0x706111b190603150e0708130602040902030a140127090c0909080a03111e0c0f031b120301030f03202a0301050f01060c26040e0c09031f02070c03080301 67
    0x300218000764840540340c0201d036252545201a0340342c040060407402c42c104102c5070279400307200000d41c8e1542d0b40041c5009040d1104041040d0040700d40e906c0045070705030300040f07500880e5820040002480e0300e40103030350042014042000e1502d41018104000b0304d92111501507d4850104140141840903102580c129078045c08944031044440c130303490081000f01c0000d1011344c94a1076810019000030100014a882074074800c0040c880c80d1070941d042032802524400c000d0701178160031036041c0048103114561205a500350750458840ca481000c8181c002800d00c881e80c0703600e860014482000c5900c044800084030f100e52641c4400780d074a003208c03400c4181640d41d400040f907480d00d418000c4a1044001c00301034a0700d6031a041080310321010b9040103a4140208521691114034918148078822469843c0d0541d01ca20340f113440c0350141002851008a000d0600540750f09580c0460507082100ba49000c00c94100340c1000410000e21440c0c2005001d01d10b4007100004002e00d200245040310120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 849941393 1250 849940143 849940181
    0xf0a030b100e0310050c03070309050a0c080601090b090c0906070201090f090f060e043302032a0c0a0605060a180603030305060a081c02150a06080706111b190603 71
    0x441e00740000e9074000c1d00c030240c2e40c6c0c40c02e200044501d131195020f50f802502450464040c5515511a40351808441e00403c00640040005104840b1103004080c00c1902c140e440346440c0c901054404428011400e010703204482c0050101c040da031040c803041000e480010614442181c0e1150750500625030700c030300d10b42090b0034090001400100e8401c81e612031500605064441c81940240701d401d40310020350210035091450240c81c045426201540c440e55161240d0302c1000240c09010b00c07403850190000540d004204022000e164010407000c442c0c5500c0704010804e80c84950005903003419540080300711281e103602500002c102034002004407130181d141005543c0712801849005d40c5d06c4c3c02a06040c0d400050b603044080d2120410b4a0070103c18030568182d120441000f00e0400415601c0119081e240c0805009501c2e09101c80300042105041c460022640120740b0380d114144001100b040303688528400007161a04007035001744c1541d03191600724032034582902400404000c41081c05610003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 849942643 1250 849941393 849941413
    0x201030f0501060e09040c1e0e060604030c0e0705071a0f010e0610082706190203070905010e0103090503030901022203030903080a020a170306100906050f0a030b100e03 74
    0x2036071151a069070455559616070141c1c8406000030004060000c44082aa183d00010344040740144905050546684080510b10344000404490000f5144501c03925080104000040c3c07403144460444445c011180c5482d03440010980d400d0061003805810388426030305130f142d552529000c06105585007016141141d03214041044140750072603016410048140004200500549046130b006d1401150426800e0085220708000010324000ca003040d1701c8001070050107040c4440d000440c0e02600302c11030443c50101d00040c0868400e110300790501c0a80948900245d00c00c2e08440780d180d070403200b00c0383c2d01c1c20801c0e80c040c002e60002f40080f1003000300c204644e000249100401088a03007594803604d2444c20758655440c964007a244090941c401c1103c02d03c0012007140161800c1500b101c201ca0b260300e050800e102c40c40b036400e0b24210030858880001d028103074111083d950160502c401542c0c407048010011390040072900c000c04d42c02101d440030640c865034003030410200c041c401c1e0151001403003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 849943893 1250 849942643 849942671
    0x1e010902211c021902030106180902091e0103020405060303130f05010f05090d170408010624052802030c15010501030b030307030c0204090f02120d0809150c0c0f19020103 75
    0x1c0c1802c03420010b8000c0aa03180000641410681c41d00740014000203c07156583e110740d2000d86140e454045a1392541c50420640c07511810b200e138004841600c1c1d840d0b180344101203e10f00c000500000744102d54071004594162400c1003504e400c000c4c0341c04c40d40a60307510b491000281c0e040310310490307000481402c030003207a0b14802c1080d50450b20f006000c0061a890135a40c494000f0381100036054840400d0000148040003402200010300e0494800490001143c0900b401c507000c00c001071082c0081000b04041413040032240070002100514002c0b85260204402c9045120300208500c16104081107045903804111031181201c200362810000300c401a01450f84a0140340d034003801090381d0f60030041c050f060980003000705c40d2040180b141c0b280b2250b0700281d804418070740340c401c882e4400c00d00040803d4102040c182c02060f9103000b44026a44d104404047d008021f02c19400360340085680c11040c034003080000742401c01901900c80c030f881c00010000480158101c240e00080c20107450301d0b540700d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 849945143 1250 849943893 849943933
    0x1b0816060e300d0c050f180a050105070210080c161a010602010c02280b13060b03070510030b1f0c0303050f0712180b191d1e01090221 59
    0x501a0750b440d034140f2081c60302420007080880444c034240001005241c20440031070005116440814545003040c00409007405170703040942d0001350601c4410044000542d40760710180400d40c09614047c002aa1403030300c0b580050081e0111141c05030080c00c511410407482807000300d500102217000680d66a0b0f44c1c84102d090f0782948001a0150300100403040c503800c0000c00c01d0034000c0041d48401242080d41d81d515407400800c8500003000c03c81d408000040003000d01800719501c000300c0007000c0322414800000c1e00805400c0243d01496070311184030300c041e16006011809200a000b618100358071000001d40601090002140007038036080c0003582c9102280c031514000c4811b031750742c00700d54000002000014440c0110040342c1d01801032410000840c1c1190740752082c0c03031103000e98004e0030106500c40d0543d104078408d21304c3c8000d85a041034110300f001503c402060791504410364070544808a0b41e004009144019420442c00c44840d011403c0131052100e82d102c40a0480315504802ca04d000800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 849946393 1250 849945143 849945223
    0x3030b0d03050324030601030c05040c0c0305040603021e0406030501061b0308010b1c0c030204080f150601031d030706150e0f060910051e030d1b0816060e 68
    0x110b0024008180580f5070b42a20b01e80c101e0680d10340807035258910000030f182c45030990003203030040e90703d0304140a942802d00072005003412908081100d040d00c4d65020700035000d0350142070200350703000c06d4807005919480316910050402c001642da807661199001009420240560b40214411044100702c2045070414010f070300f90150703198407141e4200b56403140c207035210b408000c010003035145420303614550b81e21501040d5041610700694680c90805c0d2141450151802c0350420340041001c1094078410032040359100c1c4003460300041c200c8001071716440c0600c0484a4840e1403202151003404c2245580c0b085906000c0c0102514142c0c1e0b4440a00c1c038442c004540401e54414070002042080c10948082a00803d42480e24281a501c60001c00d10805000c0c0c0300c2c598076102d1100c1d12185d42000e003c14000c1e04014038194400c0500203040700004504004024028203000500b0700101da101d0040c3c00351154041000d02001030803001e900d540c0c2c0d62000302c84200c100090400020034842003140402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 849947643 1250 849946393 849946397
    0x20102012003060f1201020a02010b13060b12090304080304080a06050f1303080901320115090303110705060304030509210d051b150907050a06120b041d01060303030b0d03 75
    0x203581e403a84144400d08031904e06064000d8200c00c9500346401d0f00380050030100f00d096000082d6102c0542c1008804006000d41d0600e9a14000c814821741c810f40c421218410485000c0b1980c945030701072103a181d440740ea8002c9070a40400b02d000b08108001190605030580600c400740011749608901c185d0024043e50207620144600a22200107030007110a158000015000002e0100360505403a40d407040f44050246e2124210f1800a0481e803516070356405008034480c496161001010050308a158600000c3c2c18020304041e10590b902003041018081e042c040d242c070352603040c24980504650840c04c0301a2140748a02e03101000503584030040c07400e6811110060000340c0d86404265880d03403141d54060f00400894001c81030005080150040c0c845032600b007011310345881040f03e0705019a94012138803896400000b0007070305030302445000342400f80060001e0004034500015009002174092024642c071440601d210b90b14041d401042141c0c00398400b0301004c01c5c42401c00194461030040140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 849948893 1250 849947643 849947647
    0x9100203030703050903180121110a03110c0601122103020406030b0301090507090e0f030a0c1203090f021e03060c0417030f031612021222030801140d1e0201020120 72
    0x80552700c5026000810403c1740003210110341e44600c66001d950a501821020340c000050401020380d05101d10084814004403044c1020a40c1c0801511508103208800100081801107001c0c0080302910401e1000c0c010740d0a1200c84422102030065000342c401c24000c40c1c604407501c80380d400c0601901c0e007030981c02805082e4070303410032813041c00a02190401003520b1040800d02d042142c01000200b0750741111f0b451f1803140c80c665281c42d03900661707000c000408146c00c1c11880c0000a604100c500c0086504845c51180c00a41201071140740100c840e990381d0600c921000c1c0104094054014401e9400014000a4068106642540e00c0c4114410401d04050800c00a24100710203500141c0107135081c9404c0e0940c0d8051130000d01a41c1000c1d06240d203818480303060211841c8a0461070302c0b01c08000260341600e030b1681d20302415601052003075200f0040761048100c080e503a050741514116511509014088940088410001c03034205e10403800f562814000c1d112050021003242c119800b21080b088c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 849950143 1250 849948893 849948937
    0xf0c0a021519050f0706231f0608070e1c051c020303060f04020405060a09050f010e01020604141227150f090604090e030306090f0601051e09100203030703050903 71
    0x452681c0444c0c0f4441c21039005101213400203801780900380100040741340500510141d50010280400007a08541d113a40301d010a40111100710005c2e58100c0f0030604080305e1541d181207003503c01c40342c1480900e600400540c100205110440d000c1c1e44114025000c07181001030701806504203030507804100015910500c000380451600c00715038518814007070b00250900b90381b4408140a42c00c03034890000414561f0400b4815404e00402c0780c5091602480c0c25008680d5000002c3c3d2203040c064409400b81c004542105001c14040100c0701d03840c48204102a511403070081c81409800e0341487c110300701c1c901e02a600c034441c5881000ca8102a180940082c0790070508080d814040c4d210348036140e0010410310002075414440d108000205071190041e6980c0c1c0341076400c00101c1d5000808a0340c21108441c184900d9913070080541c0c0017807100d941515a0314030442d03005c80540c090702201c07603803003d15180c440d0100d690200185000340c146480c02c2c0002d480d1900c40d9600c07401600544030079850b00061603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 849951393 1250 849950143 849950147
    0x2161a13020f0d060e030d1404021c17040602100605030c09010626011706070c08090613030203031809010f08030a080c0d09030e0118080703170f0c0a021519 69
    0x800000c2c00c000e00304030031400c2c0d507603580341503030f442400c50601c1da0008118840d80c46820b00800805400c80c0d12603224070315096000510481c881c0f484401142d80e9102040c040080000303100034207000c02c00b03605440701d0365038000942c5c40101c2030100c99207038100340c1e00284030305000034000140d05005000040b01c0e070070014101d44c107a0310010f1607450484d51510304000903c070064440c0c042c03e801882c0440850f00d0910f084c1c80d00d00050074810070420000310000c042000e1b40300b0359418290840380b060755040c0d05050302c42d4820755904040d42c580000558944c518001d00c4034045202c1042d01c0c2c4001d16030781e50044000c0c004851181050a170020400301565500c0b4104443d8407009805581e4100260310310881c04803001d0000440c085000681c2e00c481d1981c1001c40403c02d405080800008103080030300c660b0b20b03480c1174800180581c0310480400882d401c58000c1d50b030411f0142c1059034483c2020380c072450352900c0200c01680030b6041d02840003202c1f0100004c9401040f40c000030701030000e281c1581 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 849952643 1250 849951393 849951409
    0x22202030a1d100b31050f1501050c0c0301050118050c030f15012d09080321070201020f070507050a060e09060f032109120109120c030c020402161a1302 67
    0x1c4a038003001c008490b5806000340c0c4c00800400c0d0068402c0a85803c3c00f481e5582101d90207070001080c4921f40c0108000c01c01041c0c00b8288080080c40d09640300c0c841d0000ca07910303041c2610416039065080c08000328074070900e040d00440c405000a804c1c0710a807280c0c4040803080c80195003200440030001d0000c0c1da080e07040103c03456060410314044611170041c0750007801c3ea5045901c000c4040d07460030303071011245074000148009007280d903015500d0f104010326031100101010010654801c0d500f40002d01081c006e50581c5c643d14850050580c0e2055207140c05510741d0601e0060300e01c079075400d2802282051044117814111040034150048944030a020007100d540d00503411a8580704812081d10b019103400703102000b81e842d0040c01030320b40ca000d804015941081050f01501685030032520350206544121800343c903080d40c102121061001e060480e1001a408000b81d00316000042d4154051110248034108500580151006003040d1000344001c0c50b00303807010a000240c0e40d141d9809450090302c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 849953893 1250 849952643 849952661
    0x9041203020313020406030f0506011e06030515060c0d030e0114040807050709180203060f070504030305030901061208030405060709180b04090f0506180a1509022202030a1d10 77
    0x101060003c0500d50002c3d0a940407030b0802c91b12a50891040020054200191400341c0030080c01a484c0d810180340c104080c00e02c505c14001019101c0c030210b030030490f021b400c049624a000d00007070740c1da68005640076601e420a140325000640361249103904040b040c494000395030007140d0201429151901c0b50f000d82c1e00700c5541600c842c0100800090058210701c2a0742c054030011590502954250042500f008002811440c40704003001c1042400380d804000c0f81d0540c0c0d810b080158a80c1c0780c03500781c14010071698002e101562406000102400b00c55005184201d10800881d4079a0f0780c0c1050440b203000700c620170a803065842810380302401143da0020310325140040c2001402000030788540030142050b460613100d5400c60740c03c1c0012400240a10301c2c010600e0401000d900034503a40700c60039180302a481d00c101582c0d900710f0130115a00c124040c055080494060004d036035442030210300039401681c0e640010392401500c542000c2e204011951102464005080e0741c6002d007403480c001e400c01c09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 849955143 1250 849953893 849953911
    0x3060b060c1501090c080412030504030903050f0307120c05070b0c101b0905030f030d150510080901050a1808131d0103020315040f02010e04062111090412030203 71
    0xc04000c00a980410440812074040c4050016070b504d08022003080b00d006032001004c10054604100218100714544501c500c940d14000901d90780300d0034102c0703640e4079a4100600e20b0081c1009200d49080000282808a0264030000c401d1344c41600c00369110940b940c00140160001d140c20001c1141400240401402000560795026900d041510444039402d0480b589061514030710103295a014800c2800b07400250000d03e00c0c40404034505a407030113090280820241c135042c804d03c10f96020b07030800005007009802c2c801051113558015010701c4e401c440c080a0b5611344400030308400554000c03411041121011700d0000c41a50312485020344c07003641030705113034005150300003242103940c0060400d4220400141c58070b94158410141409040c0001c091446042e00078800820381680f13140240680c242803044800a414000ca80500820350141820b180c1c01041e02500d01d80d080382a6a040744190881c6815102842c100b2503d2a42954045c0c24900003140740c07000310780a035008641205e01b00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 849956393 1250 849955143 849955147
    0x20909130b190608010f02070501110913050a0b12030c0607050a092102150a09050114031603150816050306010b0906160c030f032c130902040501030c06091505030103060b06 76
    0xa03015003802d4540e03e4000b007186c1540002d0b8902400740078418000039621110005e8504480d010000312048509107403074420715520004590681007582c00100c040742c0c00b0344414504114407415544941000e00928514054000081c0080e8812000c40305410072648030314915074203251009849000d0300350134420007100b0b440c540c00035036503940040d800c0c00c5010340044e0743c403506204010002c99013036111358180001e4049140449400d08243e075403103055031403d0084500f800400f03d01400a02840c1400b5000b841d81c045a80000070500c01c0981c60038803800c105035581e60092643d10502442045080d10301403100306e001d8a00040284801c03561607689040c403030b107562100010261940d1084403001040c0085004040d0031141048183c0300b00c44117817070040140c4a003000403814802c201c0d8801c400b904c0020f14551400d40c4035401e550b4018008200940e1a4601212140b5241c003544000c901e5540c030014907840010071079006080c55555050850b4603540d00c040c0684a1f56062070b038402c0003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 849957643 1250 849956393 849956399
    0xb1f030902010e0a08060907060e01020703021c142413060905030c0f030a081f1a04080109120e0a060e06030606040902131e0803030103171309020909130b1906 70
    0x3441303080c1d001810720903010300100e041c2840c21300d10f4a505c0b91b00850901c10075440450060381c02040cc401100c0c0c060b1215417010400c4030b00b0000c1350407000d2000b0540300340364144804450300099441421130305a00040503c1a00e80100e12a640c0202d4602848170400c2594100181032a0401146240700340304403818070155505c1203042c600c255086a2a41c1c0c8007040c1c00749541c0d444030070240c0020010010300d040713103942101d8100420880c080d40140101400000152032207400032600140f480000070413810a6514040d100c100304030784080700040405205c0c0301240f0b09800f8032802c60369680c950303080d52003c1e281848480d400080406078001c40034800040e10803100d00040901c007032040c102603491070400f091580c040f0503282044110f2003040609000002002088038156504008110910103014030b0640c0e03540700c2c086000c243c4200503140040e00340c2d05500500440074044a540c4003585c2d620780c50155a80c11a80301400c2489040041044881e0615102102031841040821100d803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 849958893 1250 849957643 849957649
    0xd030c050f010c08010617070f02120f070b01050925051218061008070605090a09020a021e0c0a5301020f22050d14010b1f030902010e 59
    0x1056074030380559448940c02c81a65612a1615025042600b80b0724090912416400c400080c0206100300344036283c0364590b140d5008202c80c4030030440c0420078541d500c1c5440c102d00126003040808580075007048001040c03600d1b2000340c00d4400c50002c0b0302c0c0044011500d4018001d440c40d84146824081c0c104443c00c40c818a000740c10748504422031005a04034044117000d850310310000c2c0080720380344080009110201c4003180c3d003011107509160003074803000b40c540000c2c079107505c43d80b080540d5403001404030082d54000c50304d80e9000e940e10380014003180b005180d4a40b070b1102e00c0c00c45503110351105414490507040c0d08550075913266210b8100600898070048090071424030290130030304410710001c070360345500890903c08050ba03008004d50070b00801d041541598041d41c903825942500c036107100c3d0140c4074543c1650004100c020000c108c07480590501003110401e4110b4500d26500b4584034860506241c81c0411000c1c0d00142103500c2c4682100c4110001c10031240100e040001203d18401d10341d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 849960143 1250 849958893 849958903
    0xa0b06070b07050d0218130b01120c090f0e16030b0105090904060b0907030b04111204080703110d030c1d0d150b0d080c010b011d09194104020d030c05 66
    0x201d00c849286c10064a10401c001c000c0da000c016414009041c854955240c1c0d0b44146050014820003038040b50311a1a00000c0d00c80012039084001e002c4401c54000071071000c1d15040601808540f001020881c3d40000c045042c0da048410706808500c0030480010300342000c1040c7da80c068002e03400022450034007000034850384010750348076000a4860124070554941449014a2615403d143c0d62030090700142280284030001c00c0a44407400215a0000345402803002041c513000c25003d650080342000d4001d8014a80d100203003000a5100046420b9450005104558903030005c0031842c1e1909180d4460000310240001080402d80384c0c1e902d50825202d0000e4050343e01e21a14101d601d49018010480c211035014418504000c46a41346141d168106003407904007020654904a040d550a80d040740504103e110449250f850090809240c86042500000514038501c04140036049100010146003010a030324120025038000304c1c1c01880d10201c50443d480c0329040455241095803121400d01d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 849961393 1250 849960143 849960157
    0x90d0e01021c0f2c01120218040209190609031a010612091104020f04091103010e01140f10050c0f061626040b0a0b030a0807151509090b0a0b06070b07050d02 69
    0x1c81c030520458410b0340e000b80b08040c0408001c0000c500700841019681011219029564081c0cad40c00a503905d804e40703030f01c0451010304040c1c00c1200b41050f500c5074010f10000c21071000b611800d00341505500d0100941d40346034101c48a540c2c074690041e541c522140020700844804542e04401b00016500b51380b0740b8000341843e403000c00c0490b62a035142c04480c01c1130b504504000c01070124104018810701c10155910b50541d00100d403035548079140c07480461015001000c0c410b03032040036a40c10354001076001d030040c84c600721800d00795a402d8541041c01a99280c0a0703031400101c8500c86141415075203e107582c000d60b44904c103400344031000c0081c07020b0142032094505965098207241044000b04241c004c4555202c019001803a0554440d03c0b8400725028079000100702207214603001000c0c00044e0041c3d01c4840301034008548050361826500001d1481620841d07814044100103480925184660342020b0000351440c0d01c4d064490382c40b2160380701c004004100380711041c05840240942407001d02a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 849962643 1250 849961393 849961457
    0x70305070c330902031507051312060b1905012303010e090d020f0d0815040e06070221030402010f0504120602070c0e07170c12090d0e01021c0f 63
    0x32040d0b1110320162204810b018540c01c60070040c0c40c0780182c4000400c80329828014400710f01079111840e0494051044184159400d4070401021506000a000310040d00c1c0c407404003004500c0c10310b01400018614039201c180c801e04040020069135001c0c1ca40c02031b01c02041c00801102c45092038894010340c00030303005640d84a0300e60041080502003000310501c0c41c000d07400100300b5403068501d11991030041e00c0384a020006c0030004070b6000032060041102082d4018014002d203d004030f08981d0b01c0f501241c02100500c120500c141d020000d0a40000740381e901d21040300d10390740d190f40048d100450398500000410404110005192900030480104030344101c4000d0381d150304504002001808c2900025040a1040203000340342c0d4100403051403148450104104c2a59400c8021206008100400321050300301ca04028510380c01042c2d02103001d684c2e442d42c10345c0aa14400490350342102d5020416001428458004150300600f00c819070b43c0341918045144070401c15010901100c8038115210b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 849963893 1250 849962643 849962693
    0x110a0b060d14061006050c06151305040f0c09090c0509040503070c030c030b100b03070c05070f0b0418230a092906240d0207080f03010906060201090b070305070c 71
    0x840307480450300d6008000306d103441d608100b00840c000382c0783c0201820080424101c0452546a61203248143c0200c0000003000c100c9841c0c05d04054614a0108404132000084003030041540e0b40e0b2441001c03400340c0c010460111032130816050001420740503100f034a96102c1488000000383e04050601c0c042e6201c2c8070001302e4a850740c5001d1206400180c008a12070410120034407007003840c0c1c03060b664402c055180400b01000642041070030040e441c1c00442000b0702000c0081400c0707014000903c101e59030f00040c0584080c0b0010110b00b00c4007a0340e4403415800e0b058000c09444c2a01251254000720708100001d9140810359811a581210100204181080c0c0081a50f80420b030351069a00c09000d4a41c0c0840d100ba18001e021300400001400428100c00700b0399004007a840c0d81528101f59205101513a2200e25100000640d0400d1069084550408030003207040703481809148042c0e80d0000c2c0c0442580c654182c103401a20009140c041080503c0e641400840d9003005140c000409e5952418 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 849965143 1250 849963893 849963901
    0x1201081c02010507080402210106151404031109190507261b0a112d0703020108062133100e130c08070510110a0b060d1406 54
    0x45201412205034010369240c08100200c49030804000c40d8403550450300c40302002c04c0d0941030a03880c3d03d0321a051035203619000010641020201c40c1d0060311040340c4585d011140744030341c030305114407540c00010601c1d00310442d12089403c0c090344083d007001c08001d120101302403000c109011140100c1c0d043e80040d910340a400302c1c9000c0411043c20303511149407400c0d528038211041415103405280daa00075250001030700d4020078444d000d142110046582541c0030b05894010704912903410440700360380e04007407400081070b00d580011001d00322a41a100d038200d65a40c20700700001d01c0c0507102c80c004401038910303c481102e807007800950488818a00302c800781030914944254580320401030688020b6000c010300030b1102001030708504132100c140301e0405039074500113542c6003d11010402042c5500056000c034080d0008202d44081c0c0c1e5040d1007104074203c8d03c0030129045800c020043d030490f00f114100c88081182e000710240c0c08003000e4940a240036296880b80828004141007500d0f0b80c00c03480a01c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 849966393 1250 849965143 849965173
    0x21011505041a01081003020d050309030610060c03031d0102030a0f15030506040f1103030a0507030e0109030807030c050123040c0518010e060d061112070504060903030804020402120108 81
    0x1a4014010548080080042c0c0c0c48102a80550441c0e40701d040c445854006a00e81703202210440203190b029000d4002a0f03020b1510b01e959400515155100c0c0c0181000500d50b003015408900c2210f64940e43d03e4213641540d20154010180304285241c145540740004443e50000d0004600910904000140c0009450f120b0340844582c4030301101828036100701003020035000208c0c43c0c1c011380c00480c0500400700b1864444800c0003c50001901800080b505164058100e4041c00c00e0034060748510803240e0240c0700445030141c90340001400b005040c1301c00f0003c00e200f907114030392551041c0b000041c3d40485001300305d190f4440040640c0c0840c03214041004110603a4203890044c9401d40c1c0d02091021006c400902e950014010000001e04800005a190b51010054505503030081d9080050030000d40c12003c056200e01480c031134542c1508080780b20366111b803040301c00f02c4802c4d646203002035045560444401201400c1aa80a60240300800081c0e4900d900b050083c40c82c0401020310340c1c00c0000d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 849967643 1250 849966393 849966431
    0x180a170304150b24070c0608090f01090c0b0c100f0606020f0a1e0602070602030f01150c0203030f0a02070510080f180604020609120624042007022101 66
    0x201c003182802c003400040113403948070480d108050085140c501a400c8500030000a00031008040c041522800d00010140d400101240c01203412209544080100e404181c4c280c07a5036540c01000c070303e000702040141c100010302524980b4004000e40304186540000c541c280d44206904645080d9140000c10143d6010001910070300b04000c0980380118050b12a410515944040c5400000d0035030020000c101440d4122520380e50f001c0c3c0215242d00307040080348180c24003400380c01ba40c800b0600308450014018443c80e01f0540d0300900552030291240b41c09182d6412145001040d4496081c01280030360303900614440c4112a40c0c3c5561092400f074011008021018140000c613407807418034100e43d0640811042d030701a40560700d2a640382d0000c00441c4583c0701c14080c66425008842c00d01619030007105005000d0300c4240c0c9041c600151000400c802c51b400050710310350f881ca240b1070261070707811182d01070b084186c0018600b22082501c07003020942c080c01102d020403103954607540190b920840c0742d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 849968893 1250 849967643 849967673
    0x606080705270103030c08070f0c030b0f09370b07140309191a1006110c011d061b0d081e0402010c021219022106180a170304 55
    0x820591101030080c0c142c2c01c0c070010f000240c00c0040f6000e030300042c000400120ba07545c80d130091341e60200c03003402c3c20000d01d4050070703010489928041344042042d00714110b0341c080c020544140504840d9041900c2a02e403003155a0080000701201d8001c0e413a24419111041d481500816501d611031501900041c5030400e01d154410a403c030900503c0189400001c0e00303820b446101c80c0d40194461a400d0001041c0e02e070021203514186403104110301d04442e20005401c130f51103900c640d041031480c036440640b50b0080300c81c81c900107410f61000311509105a0b00a003051f80d4054070242c54040400c804070702c80380c0041301d076403000d5109850107200190b118400310741c003010021030b600150a401d000490005001380020b410425060090025560303a02c0c1c1ca0000c402445c1c3c210b41080c01411a694529040381e075059100c0e00c2c07100300300500c00540f20400800340d19086c01815a0740d46186e0181b00f05030150b0400790640c42007031010800a90800421100303d081102d40710748904d0280381c200314850880c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 849970143 1250 849968893 849968929
    0x31d061906052d040509030403080325020d1403072a02060a020a03020c01050f0a0e2d0a090515011b020306251d01030b0301090f0305030f0c090906060304030201090606080705 77
    0x117042000280c0040300b5142a641d01120311660b90f1203c12101ca0300d01040142d9060b0081002201c000e182e40000d00c50046803010340355040c200410080282607408100c880102007902c6841c622040c200e034010404000c80b4001e109402d5001075004a140b40d00100c80c01c00240c0d019405070340030325404001b070400c40303982440e00e90310b001d940204044160040398109028000c2400c01d01c80903a4410901c0d01c01d08108058400050030040c0302005c0c1500320103800380c00f03546051000b00c0e00c22140e0090900c81c0000d062107003080c0384440011101003004505410041d0b0240b840400181d40501006018580b90801751421000c04008a8910202c00d6060018480b400e02188225200031001204210090800041c1015914042405045071880003000140880040010107412101940c0130740c0e07822141d1701142e038070540328183c248a886103603030780f040311031000404a2508200840d8028400d20021401401969400f8291105500301c18901c0c2c001e080144281d052080701100e00d1a801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 849971393 1250 849970143 849970151
    0x509060f01031505040f05060403031b020a0515371a0a0303030507020f101a01020a0c030b0a0b030115030510090b0c0d02041701020901031d061906052d04 68
    0x240d5541800910210543c40d0300700c0e11440010309010880c3c0448452036084001c0e6080c0b4038140c0340083c02400004008008200030031600041c0920010760350b0002648a0000c003d02d00e200a80041c6104000704210001d002c4845c000540729241d240101c0d0b4080001e1525040e101c4541100701519401e48a030340107907203141030f40d030620382c4c0f800c0b00e08080f00e41500300012580c440510881c01c0c69020104001c1d076100e1945090031420490303000f803103001500101100002c1403907004984800d4020340c0038040101900c0248003280350a00300640100c1c418100180c00720010f40401d080d2040c010302d40640d052140741c100140308080c00481654001c082c010401c040c80d41d51414602440a002c3c1700d001e80003c5800342d0310f048280e0460703015000d10031b8035140401c12004840e02030340c01188490300283c10005c01c8219000714695000c24200210b01400c0b180d03445401c042e103200380e00c561170101103071209000902038440c00000c1c800c00e8400c0707a402900c00003003198500f90700b5188810f03902640ca8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 849972643 1250 849971393 849971399
    0x9091f0b0a0e061e010504050d03090302030f0f0304060315120f050d1803170f03010e1006300b0603130318050a0b0a0309020406062c01050a0f0306090603060509060f01 74
    0x10640d04103a0340e000202002c071340e00020001200e260089410842d0403a003035911900c02d00d40c120175520b048074821421510000d0120441c3c584507503280c0002d94165005010500600d402034200b40c040640003080894030a03550107140f21a94035507441a5084006600640c1c03e1001c184448440d141d04c90a21141e4010302d0410741400140501c0003030100b4018282c9003e400001400321010380401e50b40c480c1d1039507100e500d4500c40b00825107100341d0704c0504120006200340204405002c2d4030f14020024110414204110040c0034500705282c04c00c0c2e40d5039a10a810380e101c00145004046814041c29401181d15003e00002c4540d03884e24a40000c00300100810380d12411910306541d40440d01030780710011940c0903405000c0f1180005e60143c10318a0110f4600c3c0e00854841031b15401c1c1c081e101c001d021200000000e40144420300307002420400007041803600072410441c221017185800103842c2c1e0369506210464049400032035009845a040c03003000d070340801c1481d400880030140b028107549 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 849973893 1250 849972643 849972649
    0x300c0206102d08010203240a0e0c090301110901020d030e030306300309090601030209090402011b080c0606010306050a12020d060603080a02010509060702010606020c09091f0b0a0e06 80
    0x100d8031a10502060318045010442221599081c0d10700114000900ba10348410146020350012111100080071704e03441c0d104e45061610941d801d214000d4048803609052080417090042e00504036004210308102e641100c1e00c09114001c0324a601141c816110a00e45000a040500c0c03010b0070410942405000b80c07502101200300c82e08070300c04540b9108804968100c5d9039405800721242104c104810180341f00c00c0e10080300405091008680b0882c20f5541c82c001502207000707888585030442c0e40980020f0040d4014405209100c40d42c420240c00150150354180310703a808203a1180840d000350b001d00086507098007039070000d00412122880240e04040304a0388000f001070010303102d00303440f40300442807007012340c01003020f5500b000280340d135401144406400703410305456025040c4120303030005e0b0f243d03072040c80340c9001e0b54595070180ca001c944100030004001d03409001104075000340c810940d00034294041c000c0600d04904004074010b1004030800005038180d9001048401c50310080000f565 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 849975143 1250 849973893 849973921
    0x9020109080c060415030902060a020d09060c110d032f0c0d15020904021209031c0b280f081c080705042607091a2e300c0206 55
    0x2541310045d0b04000b40e400004401815410750040e42150340000c4250350030782d0115001d100401c05840c1c41c01c415685103002c4401d60054a030213062044500d0344550380e85030046500000d140289440610100303a5007070200c0116000f5100910f252089682802243d814858201241403c81e4507c88981040e290074000407040b1143c0301e580c40e400104804940c0d601c0c3e041d0740310310800c2c20070803056150103900d469980d80b0000500008500c8900c02c012110f841c3d0141c08500e82001d00040e4000354019121203040c0d0b981c031421010303036441035404120b00031003207000002001810014003102d150302042889030030403040083c1c10032200c80100100280c0060440301121108031100300c4031912000407a5820f4a0310190801ca0301506030005816203003174001030445002480b40803200a141e8081058001754405540d05100e82c00303000e2000410340628818a0700d000f030802c600c660784580c3c4080c44910071545031600e00d131800801480d2916561060901d00c664a00003000c107400d02c40c43e045041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 849976393 1250 849975143 849975149
    0x3110a0c12090b18281802040306020307020106051302040e07050d1e0e01060602030909010605071a0106120501050102011808030a060b040f031e031d040e030d09020109080c0604 78
    0x400c079521010741c65100d00c1c0004001e240d29505680c07981603640e2100715980a0016403403080804071000c3c43c50444ca0038804901c880082c0c4821500f6107003003000400d2a548104403109682e0034040040800d07001d000652042c0740303030350000a61608110030011780c00c0e054035008414074418481070115480b9650000e030019840d0800fa611000c00d106a60081c1c50071411301036602d030700c8200040c1c80c5c6035280c001d02e2460074160700a100e138984a0900b00c1e0340b8010070954551085801d0700422604c0d000303100414141c0d01070065200400c80e000d4a0886140081e80030701c1c001000210142440c00c5d01c1d22402d405440c09100034469140d44003041e040d4011011000340c10350100102003207006070140d00c5680281186007801c0c2c0c40d82e40e0b078406900c0940b501e11094401e207404a034061136840011000c0c00030702d039164840541c02e083c80000d01840800c41c0c088950010b0707585000c0508040c0800141440e405d4484002c2680c080138400145a0000c55202140d140e02c01081d030855a601e100a0f6415 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 849977643 1250 849976393 849976403
    0x12040801090b1e0406021c020a080601261602072102090c0c1c2601030c0e0705030c160609081b07120209090a0c1d090c06071101090314010c03110a0c 66
    0x340d810b02e6600e98502840c007007c014059100098240c0d01c680c000d0040c3c5e120f14401d8880301c144400802d03511180c0c0b02501d111520b810504400540315465141c0181c0900842c0c0c4100c411894884160014410116240c580654403840040b011072400050b220b90006803182000c2c2865242404d00759204840b0502d1900303903101c40d1292070340340e200300c090105c500c000007443d440300c540c0c00e200640c04400030b00003a5000700000300041031a00548000f035001d00030998800e859607640b04c0d49034403030f50001940e042c08000c02004220100b001805500d850a00a07808141c2c0c80011054640c984000c4184490440e04140710400920600222406007a6016642c810b5103603035a8101c035040c16800381c4003d040400314400820000003400380400700400000c0ea035696611072954903950f0f24807a58403075900280400100000480c1c0c2030140c6007445060510500d407544941d10009603000318140c285080e9940d000e0191010f505018071442054104102881c0c2103001c00b0040604540c6000a05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 849978893 1250 849977643 849977647
    0xc030e060307110d030605010e0d110112090c09020306041503030e010c0f02100e1c08070201110309150c01061e0308090a18050402011e08071112040801090b1e040602 73
    0x720280200c00404500082c3c02c103485800c14040e0019006260600a43d030000340004d0301c3d000142451000c04480580020801401d0200200115452403c12403c2030440303482e040c0110005103c089814050201c081c000743c1c0701e28154050004232860f20948150440c030003101040440c2c0c104040c2200c480080ca4a40d40c0c000d01740c1011030385450005c100070340024814101e211061340c0f0500c2030039145d500704d43c100c03c000100f580818850800304405423000208100d0f510040d8081c10421402026840980741448815000905070b004107031054030088178001070a000120081c0700b0309000c1c003c13740e412001c20340e1b444611254070440740402840000d000071300060b16a2003108410052400749406141401680c4c5001d01510094030f04130301103a9401e020540005014400c2401c080203940c401c10f555403400000c44050061100d682c1d000c1c040e210810360340031100380080026100760030001c64210f4080c0381c42800303050300410104030055240c41042a169a005030781d600290450805a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 849980143 1250 849978893 849978901
    0x4030806061317060429150f090f040c080111041404020903060c0702031005220201090b28050a020a0b04020312041805010501030e03092e0801150c030e0603 69
    0x2e1881c10703080c2c20442103051036204640408a0008078944258800d011040250b9039441c40c1040d0304219020307484200c2903080004601d0707040072208600000004148524140e400e202003055440d09541202000c1d401100300300c1882949044032004040400c02000038140064090794180030310b00450a554074030b000c1c400c0305540c032901034814040c0018103444441c00c00400c441801e9200c8901240240119040c4d819054914803840340700712441c001c26050306003814407000398402c5c4c0d4202203050195021011914010481c00b4110500740c020800c02c42c42c60b04043d070110010181d1380d01c02000705c00c019043c070307581e80800c0d54070205601a23440300326034580c0c0c030004c1c1c20401074041d0b204503203001040003e1880c0350b041850700f42c0501da0504200e1640c03580011016908002c28144c403681c0200041c184038200520400d00c004614039095803608a40174103614180f4a501c15500001e080c140140642800444080c85400d003d08050701d072004540d902030300d118a41a0001d1140c40040002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 849981393 1250 849980143 849980167
    0x70513061511010b06040e0f04060e1b03010509070b070f11040903030209040b010201060e01051c06111306080f0c0c0a050f0304080c151603020f0a0506041a0403080606 74
    0x1400301014010070016140400808161031180c850842e50300300300d8100100c0c01c00710103c0e016034040300300392003842c0d4030391201c0703030383c440d07010f03200b211429511241016002802c0c03045160b08050305014944a4001c6000c140c25104054540c800725009090108510742e507980440e07125640c80314215985108500b80741c0d144120050145801504103907a0004159141c0e005118166040f0b40800c40700320340400480c01ca031090300460304844070180051109207000101100c1710740c041c3c000720300c158240381c0e5003070241c55402c2081d41c40d1000104102c0c0e0310034070801910000d080c2c0da20f0814079501e8000c121074011240039041400000000a00c90104c10040c45010030a035008001c603003038450420903480c0c1c0e81e445845890752600908060066038500707401c0e01982e140007244181e0030301080040c206000940503100710103604c40c22440c22402d501c144101b000050091001d011185018144001c0c011340624120711071324418001c0100082e0403c80c400d4208600b618500d41301c00c0030000e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 849982643 1250 849981393 849981401
    0x40e0601050409060f170c150c030904020d050a05010509040b041e080a021e0d090b300105032107030c0c050406080304080c15030c1c02040909050c0f03070513 70
    0x204250704000c404110f400440ca000801c440a001c145001c804402031243e4513840321f520800d80c0300c1842010340203001c0c4401f02400265210f8001e5034507010000c0d0020b03041b40d00128110700101d40302c008001d0000080c0c41107600618095525052a00d401c1d55400e02c5401d0061008003c060300036080200b24080e80c501350211944011115a200c80c0c01c100a56940703455042c4007503602c91034200c1440d0341c2c4080341a6600c01c3c0b15031941d07c5944d0800401240c56000000d442c041c4448401415240c944025501001c1040c0d500b040ca0b180c0d410701040c9400c00066845007501a140600c04511042d202c00440f0500d54251825240e14486481d0003140e0b28026804a5442418640041a600380c040000c0c4125900e89044408012403807042c041480500c969071035810405000052482c6500740c001e10b20440c0221108480004041d00b84040360442c0e0405d50010750b588a88000f04041000420b400100483e00d80060654110020348d0b50b90040c041c0da401070354100200c0a000020b504 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 849983893 1250 849982643 849982649
    0x30a18020a030b1503012711032508120304060b0312030c04170708070b0c010207020303040605120604060510110f030c0c18070509040c0c050d0305010513020f040e06010504 76
    0xc5041d00c03035528101241060303401c0c0c50283c1c000201001c3c07003c0078501403041050602c6040008803840d0211600b66882013403800c03040c0e402140080142140d035600780310300c03110715612000d003c4032414800880c0301710440c150000d608640c404d0741054040606003094a44c030071762003040450a14011130200e418a42400060081c0c00e074040300340046500d161001e04260b500d0960078040041d9402c208a035911140e11600c100d81d007212000b44280c1c0899401000046083c4001502c0e01c010f80c7d0211386185c0c003560040c4000394004c0b90303021461010030758041d0804e0b01203409001040c180707030000300c501c5030003034201e0300303110194642c052440d000344050000901031209072911000500d141d1612031603000035151203081c0030307248480a5240d020700580919041d580c0c0b00d0518140c2001c3c440188143c065035018001a40c100a0003c1d204010790250780f0040d66004c9115450042030051000842111052031801880428603618040c4142e074202c03003060460a04646920f00140e54a2060303030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 849985143 1250 849983893 849983899
    0xc0f0105040b011d01052107180f0b042a1701090209010206010608070504120f0206180a050612060423040605010312030203090606010f110f160905010b030a1802 71
    0x3800c000034400c010528a0490701c100041454500f041520556000c9090082c658840301d8004102046440c103003042c0f0800c0d91600c201e400306a1180130905000c00160000100f2544035206506c3ca00904d000300b0300e203028240c90074414081400c42214050089262003000c40c203040050b448154401e0b00800d031086980e940308002541c40b283c8083c065840b0401043c050f125103000081c009103d00307245c62055a4039503540d4141802c0c550301d520198442803068680301c80c00b40c01540540d44400040c50b1030754040041c0d003071441c0e0300f105001d01100103a2107580710310018000e001241c54003511059000750100c40c0010049810300204442c00e00440701381c182800134004005c200001a0301050680e40110020b549160b40a4422000d91004580654513904450b010820550054080d100c03c180d0300e0405c034031a10740600c80c651400d0398421111010b540200040007507009030b0148000074050000081c08603604100100031140310141c0100034042d40c40d40d440400b11010766504003126402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 849986393 1250 849985143 849985151
    0x3030b0d060e0d0f050f130e0702100b0603070f0806041b080906060402030105130f0b030d0c0c150e06131805061305010602060112020f04051f06230c0f01 68
    0x203007000401003011006908640c89a4038401c90483d0003034444211071511503032014a445940550601c26070441c205060402c42c01040100d200100d010000c4d10602c03a99004242c010014000f80b0282c42c2d90041c2c441c015032041044c090081d610a0044480850908000f145600e40b00f0200700242001c070080343c442e02a0200440456a01607891400ba01c02030301151400d4407a001044100d100030300c103055126044a000080b550323a250030801c8d4540709510300041410001001ca4140341c80d103260a400510300441071800c2004189030785001d00700d003203030355940b00b880410080c200d403040030003161190a0126507000407802c0303032103802c020303001035581c800260100040b22030140200f41d0352a4818058252524003c108a10038141250184d60003850182d1900510301e41c44425a841680c100d0050b5081100c0754480d070195501402c07400180074105400c4548160075a8a150440401c000b22540c03501030400c10500c1c1039030540301d0b500100c0d07a25610070340514070300300d50410550b07030a50074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 849987643 1250 849986393 849986419
    0x409050f150708091b04050601031503061506021609180c18061401080f072c010e010206010311092701060305071e0b03150303120402010f0816030903030b 68
    0x407074481c550042c400c0fa00d6072100c58035009a110f07117403c0940403030503101030180e1200341c4614098000603000b6006050018a83c0c005210414030f1440c0d6030820f89400b520b90703120b07645124200e80c6800c010211407018112210b120b100511885149104403803005888104441400c4240748046010540c4411540015641d443c074408400081c24940490185042c0c000a84407910758803c202d1050140e645060a81c1d50f5035070959198405003003801082100c4511002c100e0303c00700305e0f40302c1d0084008c800c81c43c2c10184d03000408903003c0d05e03071960454000c0c0004200084c01c0c03c00740780c213010b0225030041d526079503c094803240c0b0b2680c8000541c2002e140b080e01403082010f51114040d00d0051081d02c01d465218200c00b2503072982001c058940d02c00c00d00c020460308050001650304010f60b01010090031005c43c000a1860304001c0e40748091440c0b10043c042190b82291620240e07480340c5c205a8182d2070181d0321702c01810804411300c0c06264440f000e00c070415119600424680400800440c0389144c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 849988893 1250 849987643 849987673
    0x608011806050d1a0c04180c0908070306050420102d270f05010e030f010e070f0e0708010527011503050a110405060a0302040306090f020f01110c0409050f 68
    0x1c2e126010381c40c0509130404640440c2d500c1c400c80d000c2c1c904110a0b811624a0152402d0050001411315002c01172031200206501c0000d0040100071070040c000854281000d06140c181d1120008211121080e10004e041c00c5032210302d8214003c1c0001d0909e44088241c84a01c0a200d95140d82d10701c40f007040c011245040250031603c3c1e0001c03203003100140082003840c0d64071001da0741e60034064a102a038004c01c0070021036105115046042c10701405540100c081101c0c02400d40c0e088811000d082c1c0c04c0700d0410b0017202d1045a014009050303403600c0080b9414030b84409806000c040c0682e9004006a910740700210011104810321385c060000b04071007070b6940d44041d62014026001140009051501007228980640541c0c084c2c1e22070038049900d810f1501c4200b01c101d6000301c40d01e40500d0340030700001001c00d400d0704c588041a4056109401d407101a8410015815060a0b07180d050200d040400a4003a40c00900002e000034280c0d400104001075007043d030b10303109036000144928403c51240300c003251 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 849990143 1250 849988893 849988913
    0x7080f0a1515090621080d0c260711010b010c06050601031b120e07080d080910051512030a0801090b030f031b01050f0c0d09080d0510050114040608011806050d 70
    0x95002c0c40082c0301205c0302820500c240e40e1968003924190f001d2000d01c0d0b030011182c1c810303003000043d0f0500b6600751f0704001000815880c10b030203103014040d0120130480c0854200c8110782a074030b03140e40204010061000064041c2c69402400382102d41d076803002034241e9000743d00c650058404e11824014074406440d00070900030140c00103012590070700950b4544480001260803d4400c00313001350040808540341140c14003030080c200f00d01c92081c26000481c8001d00c0c819140524420384110101044810510103e400d070303100032000552007049a00001d81e0700103440c0741500c200c2000440c0180e90440080d16100304002035071481e001c0041d2242c1c4003040c81a0a140020000707000b4040d650b29903031801c00440c02155071840b9000308001e9a641e14869900c02c401d118407900d0050f003401408078080c0100c0d2000c44039002c0390800200d05001039a00804200343c6c07d032013010301034a4203042060050400c1c0c0180f25030202c4a040c000511a801655040440071303200103002c8048006890a10780038003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 849991393 1250 849990143 849990149
    0x705070617010317250203070611060f041713060e060a0f0806060c030c160b0306063c0319060b0d0f0b0306070503100e010e04020f0307030b010f030507080f0a15150906 74
    0x20b08c191500003d0b41c900503044010302ca0407440c040d01041d40ca4086a29100700020310844030312102c210300141d41c1010902400000c1000340401040c02d0500d007014098003183e5004a20454050041701d140b10f0f0b03c1300c031a030641e05183c5404200ca4840001113800c13030040d8004080340d4000440c035621200c1000841c440c4005c520329a800c00781e41e0f9280c150050b031106981c456003002c420003158004003510394043d0400f180401ca03c003101c00004840c000d0422004401e0540e840b80041400b008111010241000c1a22480f0402600b49131407018401481101e80041e182c54880130b280c2e001c00e160340c1c040040c130030f40601602c295140c40c3c43c008040d540203c0d61409200b228080100382c0204039908103060300c07042e01004032191500e07001c02528007160441c040c1d140c400c888000c4001168081464000d00c4040318000b00c0c1c07411440c2c41410008030741c0140d501984550000342d01040d00040c141d403015044940703c200e02500c521110007400c4000c42e40700c0100050400042e410255138052012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 849992643 1250 849991393 849991399
    0x302190302040f1a1005041e030c0608180f060115230712020a03050406030b0607140c03010f0b060906071506031b081b12010b09040807050706170103172502 69
    0x2861407041e00700210701d060300905d4000200309000c1800310400040c840c141d04c003d820013124086699036100c5801d003500390401c4000030100c5080c0300500540c0300a02d1000d4005401501e0703a51310a0f08026621345051003040c181507030005500d400c2d140101c44511510003502140000c0d42150103070300701e0710b6102510884680c00304c0002544d0b420f10100f04211001e50550318985801d203800001c81c040c02c00c43c809158031603810404a40007409402c10041c0c04010980580b40407041c400400d400c484550403915084c0e820124942d0380350389c80c1c0c2e04581443e076049803210380b1187c5500f400105480a83340030f5000701d03d081404024449140c12181ca52001c050300207070840d840718035694503011a503401d40da8140216441400714900488002d44040506000044864154000500c1200d0558090f100c07150001a0541840418072610020300003904008010002901c4003003843d1005200c040c0cd00341c10703469510320104e8201c0496168140020385080b00b1040001c0d41c00c0001c140601c100d00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 849993893 1250 849992643 849992681
    0xb07030e0a080319050a090b09120406080a0e0607090f0b090a0b0711090c0306041a0f040b010e100908060708060d0305070f0b04121701050f0409050a0f12080a150302190302040f 78
    0x14049e4000510f51f0b4003811800c1254146403070300e40191164440a03052034400c1e900c0e03004800950030304001031840f443d4241e03102400586054002d91145043da040440c80c030008005002682d1103203488081191680c42d5075130f0340c0d03403254240725401c43c0030900036692055400007400844003040c80594000c440072941040240d1000103001298906502260f81200360000b8440d040d01c2c00764003590302c000060612640d480100000a843e00d861b076044032020030140f10b014400003c0c20425980c2c417005c241811010b0341000d00008414035000790005080000025101c803c01031030b540090080b56000624000c0c9050030716001d55050540d00100d80002c06004540b2b41090300300e02e599040b80e402801c01c03800035003100207000107040100021340349403042c3d60400c0001068240c8070018103002d0003140000f68400900100868009803541099504020070a01c3c81020380c680042203030340c1103d60300d00c421300e0700c1c000d404403044585c0003a52062a0813020350744591a5000010001d0380424a02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 849995143 1250 849993893 849993901
    0x71703040f03030510050a0e041b08100f0902011b08090303040e060103050f0c03070f0905030f011d01050c0f0a1e050c07211205071203090b07030e0a080319050a090b 73
    0x34045810341d2045c2544081c407000100401400f080c2d0298000380070312502600c03040c0016114141c0300c099030112f20341d58458201c0c2008464540303d01503003184330246c107020fa40381e1500000c04140041c223480c10101103800b191010004510101c40e4000c0e03024060f01c0d200c59452000a680c0b80d000c58000e80402e09000c00120464030460100b846201554401c070304580f00c0070800c40721400c4100a4106010003a04042120ba408020100150a1751390001c510164808215025295814a80000f036130409007448080441501920800184402c1c400e4403850241b008440740ba502c219407411005200c6035800407642e001005020400e0803208035900c3e0303603031a4008803040c040241a0300c22244141140c200041080f007148166072030700d2402e142041203588a42400182c5c130081c4c41e0101c1d070380322602000c00009540d0541e122099040030054001c500d060323962140c451400c0104000c80000000d8403520f0b400d00080c0315803940765002c001030715002c0230050080ca86040c050343c0e2485480005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 849996393 1250 849995143 849995161
    0xf110a11130213090b0105040504050f010312080906071809180204050903070506040206130305070b0c0610150309240e010501050d08040303030915140709170a08071703040f030305 79
    0x2e4807058046442d00c0f460074502a40b0000904c01748441ca070410a08110010b095580c90082502600300301304500110b51440c9000c0d07040c086d02203000002d02007040f04021217888082180c682c090341d68203000c4003010980c041480700104640000b91042d241c00700750030a20000320417034401f1601c2943c041105450f00d0a80b555280140400203209078090b80005005051903c003420b190b4a090414000c1c1c40d4a940d1381900309070598101110380c1101141c1020045810001141c02c004011101c504c2c0390306200e40e4060000a80100d4010300d03440303208030410082e00801c01c11000544402180c1050b140319020000742840d24801411036003890000f04141c54014500c0d6111948002028502403540c1ea054028092505064800706000c0c80703c80c55800742c1e4050030350b10348441d00341da110303030f140c441c5001d4240c920b10b42000c040307680011802003e5120000700c10300c2003500202516124002454404003090420389100198240032042c00301304003204a0402510340701c0d440a000c1035849032a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 849997643 1250 849996393 849996397
    0xf111e0a1406220f0602070f030e040b01051207090e072303060105250b0c040501110a150b0307240f0507050705090a020d090b07020f01110a0f110a111302 68
    0x180100f00b4038034074060800da44030a8048562503105602100d003952841e25140b080360401001554507407102d501250070150311400c24020120210740412091106c4000204140101000c10b4051085400401c80d643e001d00384420040012103041041860305103401407620004501c2c0030340c411001c0e0300c1101006003001c1aa0f1056074103940302810688040c1c5204134221400c86001104d250030a0000c001c200b4400c8410b106c0c00c0e02c1c01741c0d0342e1f55928100c001403c1ea00480400481c0350400240380d0b0016802c200301c44051003003800c02203810641c83e4000703820015164800780e00c04c0d40f070b041030b6950050510141041b000e0143c0315100b902e05681c0d01650f062047402002030854014010074000d910b0704003000d603080000c0080060400e00307030416401c1140c8080c401501c08035000e10030400915810080c15041e2403040f0000d00c00100c8004409199000340317950501071180e0310325860f0859204400c3c1d04c00d00308961089894541c06030038600c0c80743c0e8410700081d00401d002409882039401c00d000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 849998893 1250 849997643 849997651
    0x1608040f0f0b030402100903082803094709010b031b0d03050405061225052718061c02100e01030209030304170c010f0f111e0a1406 58
    0x1000c14615039895081006d500c4d65640079005100f0a00008030100e13641101405031b0070031110040204000d41d4020342c03600c1440141007020182003100d6100022003190314000b0340c407010000264510440c20b003001c5120002494104100c0e0440b5084040510314030407140500a42c0d002001f65010031400e05840d054003507003184621140304030f080e105003440b13400c4010f014000d02e030140c02c058644d0002160703036202c500400100030801d4140243d43c400240100300060a00e014a810059100405030107402503901c4860449000b00031034003650480c042608d43c2e210300078101018800000035002c0401020741c0d850f07005110705c1003201d1010300344041c0300781000d400404036000319025a208a42d01c4510210702c0f4105502484112041d440130006403000d0200d0725031040890007500b40c0c503071410b6009000310741000b040c0c824080b03071241c12200d140b14045051400a9140082115461070940f002c0200d5103d0390b040208405049400b00314040220b201d0b0b0026286043c0640285a5491040d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 850000000 1107 849998893 849998909
    0x30c0303021b0a12030204213002061f0905270a0204270b070201110a0c0210030e030901030b0f09040f0b0f0c160501021608040f0f 58
    0x3003000c4c161a64502181800e01d441160300302182d565849003c1404400310500c00e01983c0340c00c00d005404803042d03a081404010048245524181c4402001802102c2c00b0824a00c03408410080c09023003503540210316401e082011005000c090281c0360709018041c245404148040d40e03541c0600068000340c84103401c540140000c2e11148540d8143c041d1112004064206006d44c2c81c42110350050f1180d8039950324070030140c0c0101034481c02c09156000c0402e544260603801650003002c18425100c0c44a04c058000c41038041c2c40c0b02d00d501102070b40080c026010315511a038082e900000c0d000b0302c00201c80d40c600740880e41250084d80d05641c4441030040400c28042d5208045030000b9011010f541e281c50803801480d25070180503000100440c00020380400c1c498250180c80c0403a048005da601690070500e410034440d403041c850090510700003000014890803000110044403d51 = true := by decide +kernel

theorem cover : BRFrame.Cov 849820143 850000000 := by
  have h0 := BRFrame.cov_init 849820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 849820143 ≤ n) (h2 : n < 850000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
