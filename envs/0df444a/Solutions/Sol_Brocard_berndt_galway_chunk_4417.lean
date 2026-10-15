-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4417
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:33:15.031789+00:00
-- url     : https://prove2.me/submissions/8fd50aa3-a8ad-400a-baea-640744714ae0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 794244604 ≤ n < 794424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 794245854 1250 794244604 794244623
    0x604020c210f0a020c12070503070e09100c0c060b010e01120506040908030c0d2004060c08040503030d0218040614210a060903020d111b01121109040c0513030b0403020a050307 77
    0x605420550000006c2449200240c9201421311010940e102d26910410f80718810100015507071090074442154401d07007504c03061118a0700007100606201c81c1070004e861017440c08006017600d6029120106103040180c480000500e10a5521130040200801c4150002d44a44041c000504244020341c8540e84210946888161010341c2404640280341040003d5001011490070310800106503000c9540034074024410345410318004a0a010b0390707101c0c03a010312000c22100b44a429a4015201000d0403d4a880da5040728800300f005071080c904c120891200004100c0c00e05080402c40102100203c0d503104094031180841c0c2071825020520503101d040d03840516108040d07050043c01c0540e60070f8900303a14031603071071603483c0d40f98800366602c400341d40b1a070110412203900601c1c0c0485090384840003000004a130918051441d801102c005200d42d03d003603080b80c0010700903010f07a00000c0080c64083ca07098110766415194140140051701580700358000100050404c0000b4400c1070711600411 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 794247104 1250 794245854 794245873
    0x12051f0b0a0e0306040503090f2e030f0213090c0311070803150a080309011805030a0501050a20120c07080c0c090708090d081f03050f060604020c210f0a02 68
    0x2e04040302081600d110350010400c2c4004201d002007030703074580441112042032a40c480800100c9200d20150800391450080035011031548543c0b41c0d404400c001500d0520000c0240c4001c03100302d1045d00b8090310800040c402c20b100c060030580c008801c07003206081c005020102e403070460000703401c02c3c00d044841c0302002080000317210303003286586040002030724045800c5013044000360701d81c003e04034040c0c10410070402041c4885100c0b0070080c02428064156403222aa6040c11400b030401107078100b000e9410090200f010005180c41c2c084610350007100f607030a110840c40d07a411b1006000d020a615004141f0204000c11904801090002400d0b8018543d454060f400c3c043c0b1084000c01940511450104028410740b01245440d04500c1d58076154178242d0b1208000043c0e08100060b5601161610034080200000086c24510b0481000c2c207c070415901c040c204801ea01c6015400c41aa03008030045c00204c00b00030002c1e110111075020f2403800d0101100b04036465400084400005034040e8124 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 794248354 1250 794247104 794247107
    0x6151c060f06090f0b0316060311090604120303060e10050d110918070e130803071e02010204030c0e090d050a03020904181e0210050c16030f020a0e010612051f0b0a 72
    0x540d00d00040907001f6012a240001900303c115000b03110b00402e06071500340440100c3d4038003044601803040101403546860300c6100c24840700d04460002c43c0486d240c0007004c0745103492444524820300c000501e22103918102028440b11006040d41160305043c82c950b0b415041c2e841e03007440d0384640c145c42c29240d40a1300710701842e80761040d154001c403100e100c00c0b41406660154401c00d80480b940186c4215640c0d165500100d0b40000c09002c1c40144440d140084020664190010002c890040304400c5145498480d50b058800040d104000d05a01980d81c07208480d0252001d800540ca050400500348500003003c1800d880b41450102e109181c0f0822075402c000c1d4400328420848400e84541d01420030a5020a418140020b80c0070103215022940031f030440820040740081ca08104e6140892035075a143c212005110341c1c01c01c070f10a60011501003070300004804018104d62041da101d0a030b800420144000800d005424001401150b01200190006000500004000d003c0286e85e5a8039003800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 794249604 1250 794248354 794248361
    0x10c12020a02011e0909090312090311010605090105060d0c020a0503031f24031a0d08070b1b07110105040914090d090b0715061d010806151c060f06090f 67
    0x1813003404420340103900998680c402d8040701035441c040000982090a805c00350340396502494040b40103801c0c001e10301c040542c060038152001a014000b4020161604100445003000b4011640c010030280b29502c0d0310403403600201e14444080c01501d6188241d40c6900f42190300485071130310203a000c0000882c2d0011641d0801e0b0081c081c5003410a48404c41d80160340b800303107007501c4150405446601118411030341170703d0070064140041801c2d2104a540ca020304564000180a5420a2004c000100300c2035003e00240500a1880013951400303210303036510800607510301c0086041010521000c83c6546084c814645030301c00b0703150480e459103030a0700303040e2a1000c0c1c000d00c4400c00051a000308101030002c01030710000c9070707c00c1c2d04a02c2610041e403004010003d0364004100046c80c12440c00c405282940414140d4100ca07050b61132a03614034008480d8038014019040d085000d4403010044682400c050019040c440d5030086001b400c051040402e480307031508041d200603900c54001648912134807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 794250854 1250 794249604 794249627
    0xf280f0c03020307020108071e0201061809170304060b120606191a0c030c12120604090b060d030c080d0b132d09020a060905130e1b010c12020a0201 65
    0x1400c0d4528409941e0025141d008041d0028140652403001c9440e0030b000d40c40f03c100200a401d00d0a400d01000e0100a02811152140f15035020340c0d40b42e07414008110740280c00c0115040b0802c80700c40307940c8050031906640010000d4980c40c0c1d03034940c103031034556a09040e503008454240003000141003403000c04c1503180242403aa0b43e078121001d420400d81d003009a1100c5002903000726652500c28500c0400c0c20b61207600070030b8115011303000f032401941034640702609000360703001c5400c06155903070030600085548001025002e0044400081e200d4030703081505a000c180300f03291043c0c0813102c40c0e561588641018003d03003075150301c07080168110b0400241c880a409100ca60030b105450313080a82d00b0b50700281c680c001e140d07444540780700c1c90240704a400c0708c00c42c1a400303015540015518100104650280d0248070310805001040400500b92402030840100382100503142c0044a00c203884c0761120051820360502c4030354041c02e800310b031a80494040044c666005030000740580d1000500140441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 794252104 1250 794250854 794250857
    0x1b010e0a0b070c060608030406020f0d03110d051e0103060c0329090405030c0a0c050907020c03070501081e040f03140a0c08030402040212102c0406020f280f 69
    0x840460085106410110380000c2e490502d064150b82c0e609000c006040f1541100015100020300000c4940e4002504905800c0c07804c00da400090000408500f99810150510019170f0103000018031114581d001c0e03604440c900b9148140043c424803051010705099009698403587d800d06902e0b1541c250065880e403c1c00f000c0304d415a5082c4420031009070822180180c050b0b298400050704001080003215030f40f0761400c0865441242034506558ac030038181c0521802100d03541c0c04511260300014003002003130001000b42c003a55040100458580c00003c3c18445000101040d0b03010701101070f042075002d0360161040084605c00f17420007600d01c0d0a210800e2103160f00c204201c440d0258040380041c22240d008180a90701d40b00e0b400020064000d182c052003445052606015900b030341e102d4907904440c44240c0d5601000c94001204030850140720742d5424049101e80040d000441a034010440840000942d60a00c01c600ea0101500295405092030800700054201e40c070503004003c411502220303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 794253354 1250 794252104 794252113
    0x91009061d010c08090a0e0408070c170a06150512030c0114010e18030708040806071103180f03010f150603060905060109060e0307091b0311040806071407081b010e 72
    0x446000034802c11481d48040c001804c0451190495039490089070001c00c021051640c0b030f42000d0a050700c88d5404960200e804250038000020b0309041014500400c210100c06841084501e40300c100c09016000188103c2041072280421541c1c0c520b00d0103112102020025516820400066401c44080360190002110b8200c01000b02c0c101905220754005506c00c01d1200d880466214107140d4000d00800404a20000c500804c2d800800140d05101c4d15450361513250596011450135101c0c400d03000003100816400d20341407124104620b03807650a54002e0000140d50b0209006181150a41145040e00240c000030030410385038140030b40400340540010411079401c0c0b610000c2c0c0104050710441040c000900c29482071550107110500c0281241c1206006851a0120f000e02001c11400000d0100385004688600c0ca8a0b90781510165034914000301a5601c0f00f070000e83e2000c0c0c4065001c00c5042d41041504005040300020f82442084589030500788801401c2646c2590380c440240d0030f09500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 794254604 1250 794253354 794253407
    0x30c0d08091c0f09180f2a140c0d0509031c020a0303092a050312070f0201080c1b0307021305130209100902041419030b1b09100906 58
    0xd09001d150700e8005414501d83c0014000300031369110b40f82c2c0d400502000b400f07244030b01003070300150000b141600058008100c64140c0c06404110105014071a001e40c001ca02102c848a9001c1c02c003208004d6440e41895051001c40f413401c40c41d2a2181c201d00001441c08102c40d402c03800c0070800003081c2c4100342283c80061412100082d56504501e1025041544490044081c480807a20300307800104c180245030400303040c070301d035141c0c02204074413400e03020307208082c0c840d9030202014003900c40d40ca5101c0e441500034540d6400465110101410400d02d41e1410031000c1080c030b100500e0755002e044680091500c032502e0303004116101c1c032010842c040103400c00341005103c0400e41c1564017055030444a003070150710395440501c0a1411601311010041c40020081a4081840c08540343c0f16001c0311410003a006034081159860101c2c4001400d04800c640803464881c51040c0c160b41c1040d03201559800c205414000600400c1d0709860200030039180d03003081c081c2c40d5004505014400c0c019882007035200c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 794255854 1250 794254604 794254633
    0x2040f060203070f1b0308071a070507020d0f03020c09090109050d0908100510050a06170610082404050708040c0b04050a06110106080d18060c0308040b090f030c0d0809 74
    0x161034a000303020904815101840c05c070b030725043c040070350313085802ca6032140c80618140002d00c1410105290706940000050180340c4164112580c65070b0203411603041d42c0c3c0782c1d91801d1090610381c008505500503807400300b85c1c0b070701c41c81c24051003401c68000202e0400b055050550030403141d824680101f154102c1f090201c13010008040009126111002441e6690344d4542031950405403c542c9d8403000c202c0d070024809502c40f840b21507510b41c1660000440d20781d6420446841c0c1440811030202c0c4003000082c10660500390f0445983d0303142c1914000701000c0400160440303800700c4031030b0041041442130000341f10481c2100e0300601081440c0074a080d0401001684000f40f034440d1204101513145249618032081d00710780010284401160071116a581018005800800340540c444c180200c0000761248180c04842c404c035019280c3c036070142c66946603400e03a408028141c244510411503000c2481404200515503c0800e0007d09407182d480c02008000650191003400c0c1940036080d040c0701c02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 794257104 1250 794255854 794255873
    0x10110a05070b06010e030d032004050a030209130503030c12060a050f0f060f2b090218130c0303050c010606023c1002180315150406170102040f06020307 67
    0xb80c000c06014480d681e01c0f03004a403c4200101c40c5c940501802141c5a401c580680102601c201100081404400b480d200c4503682e011794450f55500508030364003040982005082183c01c9221a031400180c040e45448083c99580207944a0411010008802203074003081581107801c250111603840b080e500c3c010008240d0010040d525115407460703100d00955a8880c000c6400003202000c00c41e4a40040b103805510058104a039488030035064642129405514424403080c01d40c01848550301d180c60b4610444003040c01801d829203c0c680e00c050001042420b0602c0c0002c5110761b136841d0f80d0f00381c20300c440c070b095901c141d1002c001d541c0044040721920484540b00390801c00d800ca60325100340403420481034071500c0e5514801a84c020f09001c1d40050b031240c6c009010316903602642d501402c04075420f041d901c89481c0e0040e4020072244000c5850700f101003d4110615000610218001340c40c1c0c0c0d010414010542041d00091398000303020001003c0454200700144828000745041008548411058 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 794258354 1250 794257104 794257117
    0x3210c0218060d020901140901050d12081902070f0c090c0203030103120c020d05060a110406021f151d06030120030702150a090b100b040b0702150c10110a05 69
    0x30344a8000001d0b0740340c441040a0300d401e0780050060089594a81c4141c0f0403012801d80903000e101402d002062608200e04400700380d03544440e4541c3c2162a042c02100c00404c0078004003801c800090040140c0d900f0b5002900030203018010341d00541c44039160417807100c0c000707501c40e6032540d04000c2e513482d095402005803030449400210904002098980854160035a400000d6005000c13000300001d202e00041d0a0340318040001c410000281003130b1401c100b9010700d1241d10016403200c000201041c82d0384600a0f91080c1020000c6110a2103003030003004001139401100e144001800700d21050241d0042d200d4014009a0080206511141e1892110802c40358880151400040072070145031007040403000c40814008400e0b00c44c2041c5c08044040c240b03811055640c03e840b01c0200d000342c04d1800040046a14882c0b04a20702898604803280503040800140da11282404d21514002068002003280c600d0300704c00342c01d0b00031035429407200301ca100c6d001c0c2108100090000020550f00314049038036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 794259604 1250 794258354 794258389
    0x60906030f0902030708070e0c041412010609050a020702031216030507140d0c0201020f0606010206070c14030a0e090708040206181210051b07080706021b0703210c02 73
    0x5440d044448000080d000460000350144170f00301002030a2400070030b4003004e407040aa03500c2c0c0301d92200254404031380100d0281d0f0402d9010030141d149646407050740404106c0130100003080844e03440800004446007210450152030700028030204510b404d01503d11501d151800c41030408c4a48018442652a500b500a05010300002c44409001c200d600c00004440070b03008a809a00c4c00304001003120000800480c050303c00c0411160414a001c21610302c50081030b80240000d580b035840480320b0300f03c401d000340d851a000c3c00d4500204503080c0020507805509031105016500c041c02441081a03005010034100301c010301c00c6c800140e68040484094112039101054040794410001c2c0e44400b1039055268144905261a1405032041e040688144980b01484080f00c40c4c140e0f030007140344150030008103c0070301000b17808002902d9901030a46429684140511650101019172070300c81b190708140c90004a0009a10482c0b0003d0100e402c15013807803a244086504c0745c3c1c00300340c3d400c944250076003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 794260854 1250 794259604 794259611
    0x1c03110d091406030c1e07150209030a150e0a050601060206100e0c1e0d05040c0602070e041e1208010801060b070519151a090a02190c0222020d0509010606090603 71
    0xca41100a070142c0c1c151b80180c1c02c00b071070101c02000b40300031264881c82c000c444004030b455240c1e410004078800d445006001401030030a240c1955940ea0b80280c00c0c040305641d240e5102040040003c0070060341141e5489400109203c1d41000340c043d2400c0d030000e00c07980e902071490100f41f18000c40801c106400c164007080940d19000703840381405807003000420701d640c1980b0100c1d900714020360980215000b28020011f184401e034844100b280c40d0041d40c011586c0041d1080085400104001c10303c0c03504407032160703406007a03603100e0b0740d400c0382c54481011000004440f900140900c40c42807141030000e10315117481c01e244c02e075140d807200d0721180c00510b821138000c00004540140100c248401d005082c10314010042400c1c00c002c00300100e01d48201b59802079030780400161880da034034400c5070f20842880c021141c103c81e100300b00721551825450100d030014803034140380c1d014203010b008410107055000000341c3c03121900c40400c41110380c014a03203030b181d0f03040c502c04022081d00101160169a218035010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 794262104 1250 794260854 794260861
    0xd031b0309180504110307060e060d09050105071d0a030f0b070905040c030c03050a0606080f070c060f0c030e0604021509060f04060507120315050f1c03110d09140603 73
    0x66910052981c4451014240c0c101c82c1c001d910816400584920b2059102c820328003a98414135507241d8450007008046500c47c1c0b01e91030f81d498100c1c00781184c148500030104101707144d0307a2400e09417501a181e10010030710444c4003410104444a6011040c84142c038004401461070302c82c1681e030301c0e0700c000207000170001002040310383d403194a6030300140001400500802160324402030041c80c0c0042c0302c42c000b919140100d980c02c1214007601045541c0359903a081b02d610395580d080e00365203010f02040309200c0841c807104002881409560740003c0e0002d00080c0b21540c852020313041e074aa9202608154001608100050350303035200d45090903c61048894940010b040400c0e8188101c07000c410540d280402c00082160380080180040c80c45401c0a40303450091200035401c0d6007900c1d2009801401121003441941083c045914900d180105500c03d0007100e05103074014a08007400a40c0002e040f8840c00301c14180c10015001440018900107080c40c1c5032400b6286000c440c000700b184140030001c0030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 794263354 1250 794262104 794262107
    0x80d080f041a04110a0b040510050f0c1515040209010c060b181f0f03080909060114030907060917031b0c0604080607030c0302070209070c02010909020d0506040b0d031b03 75
    0x24080344031180e4080709035800e2030f042c10100034100c4400c240c031550440c0030101b1020400b4041d6411250040d041c1452803101480070344294111582c1c05100f100b0a20201c3c05802041001103250b000440c00c444950800c2c060a00284054183c00b03805507004001c20b82c42a64030941071000660000e100050614084002070203210706204052403e001110900a0a1200038404040d1588081b007142ca140c0e9907081c407822041041c4000f03030083e80700384400c0e100e0303040c2400d1035070744810149030202c030000848064403110740056132011150f9100c01c40a125582d00843d2080241c0350f522420b4001003e41c000296882c4521914034140b010f000030701030710810703040181ca90080c400401c2e160701c1d9601c8544c01a628102242c0b5540060b06100c1d1030710802b4040e1089800340341d000307840001550b80d03108060315800e0b02071b04100c0c100060140e0010ba0a15507201030f1401461641000c80c0c541002c20822090303a0503000002e00c00d070030b2444514000790b004000404a400707140264103561445050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 794264604 1250 794263354 794263373
    0xb18090316060b0f01030501030b0403050f13060309051b06040323030304350a110f010606171e060907030e030703081609031509080c0102041e080d080f04 68
    0x654020341d01c21140034404016890b0818200040241c4403462a104103800440030b41d8400e102c090446488040480c01003403080008080e400c005a1100f860700525014111f069007042c0e00c0701d80025610200c40041090034820801000300000381e0001800b010f40000300c940c41140720050480c0401101550313203020030160035000c1030000045d40c3d141e140605050185080c446500381e0765031542d151502c5000d00342041d000781441d0b00c2071000d050188059040d2101543d02d070501e40b061190b140c0d0409800424004c0c030018050541d1030551104c840c110807000c004010b4032020305072549650900104100c02c2440340d2000040707940102c591110b89061380200041c8603645564080000c0c01402d141d04490f00358094400c48201c141540215201161502e01c0340c04000c0441c10300981c5c1e02c85113500c3e6000340c040f0301d0082113081e1803c00202100c608aa02c1540060040241c0700240d50f406406000400000c103a000080d01d100000542d00908040c00100450314010507040460103000c0e5001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 794265854 1250 794264604 794264617
    0xc05010902091510090305030d0b010215190b090402130b190f14030309090103171317070803040f090504031101090c08010507051201050d1a070903020f040b180903 72
    0x5000c1d0340b2034100708080341d12195820202500800310030400524040c0f18140d00c60841380c01c500a541068200d1b129100580700d20900581180325001c0d20f03e0200181e118918003845e054a10084140c001048400079100c0701d401d000d2296241c00d080001580780c088071401d003a145c2107800540021000c0000ea0894918501c5c007a0a040440700403c040400d5503480f01601c0c048020a04440b10081c101984ca1244200c819040716042e0b00400000300c040d002104c40c030010201c0e8070304050403002040d4200c00d035540b2400141c0d500120341000324030305200e0440500f04150180d441c06052032000d0b007502e80c5512843c000f0715600c0c8001010300d032048018880082d0817400034000240c0030709000070000310502514815500c0c08001c90711084c01b640803606480740c1c014000c0e01c1a86040104012052040ca040e42c1c1c0088003c9540780001c82288010720951a81c0c44607400c1070700314014031800061880e900c900907458005a41c1195503400c4610b981500200344044040e520b172030340c42c0d05600480 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 794267104 1250 794265854 794265859
    0x4180f06061718250f090504030c1104021b030403020910032003120c150c091c1416080c01080c0d02070507080102030703060524030403350f0703050c04060c05010902 73
    0x142c3d0451000205040b101c0c4c01c491035064035058583d101c0c2c20f0303881111001e490080101d0300c2842e2400020b024800d0080122000400050820355208054061801c004001007002c5e00001010f00461600c400c3c0c0c15000400300040c0d001260031030f030b15142c00010840c5c5d4400c12030b040d030541c039603a0760b01001101040342c1e032032048130b0301c90b103810000c160703030f20551505160032801840024001d40004016580c0c030b80c00041c0504540c103026079001e400c0305402c18058880b4544141410120790041240059100741401c2c0324114524154030b2900384aa00040d082c10010300c031042c041c8900c102015030340746201c0c0081c01030b500c96091500c40d2502e8070561200300c055002004200403580c055000c4001c0340c0c425100348100700790056103070415030b140b074500f4030041c00203002040100e80320340300300c1007086900084180802c2e80d0007107039a0480c10040100f819680800d04205a0804040c03207a03405c01c6a5080600050800f062034007110f0003203000d40010402400710030410300c502508186c40c4a0f402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 794268354 1250 794267104 794267143
    0x40606120b09010b100f03020a0c06020f04051c050a110619021006050d020a0608100e0103080a0f020a02090103020906042007020307060203120c0f04180f06061718 72
    0xd915011008101c101c90301c1e4550f518098500030203080850a0615861959450b5542c42d800a5415002508981005810040030903007090000f02144000c15940c00300781100b607165440c000c20020303100484020301d008000e4400302180010800204e20040682c442d40840320541e050300821030500403a0106c080014401400d05190764020840d0900c03420204418407586071100180080369000d0100250402010901040301900c00d0500a410001840003c15002c0e5941d00c412491340c0d00f038109a03502c100002d85803007a5034126051003034048080c000303040c1144c02a00010801c40741480040e000708014800a60b803980c40da44441d20220f00b1100c1841c03204000400d618254010000481c00b0384078001004c115940004151110884495650130301781d03907521201c04554018941e0b40114207010b101c0490180007404a0000b0600110340000f17141d0700003030b8004192080c960090b0140400078450100019903a509a03a1010a885c0100f14000c8400000c600e044614540c10748030340a07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 794269604 1250 794268354 794268389
    0x20f060f182b0b06032a01050705070906080d1d0d02061603031a09010f0b0d0b15030a0f0506210307050d0507060c021501090915150905100617040606 66
    0x20102c042c40525000b03040b070310802d076140b200385569400054401c000c05402e0381405d004480b1580380648581c10185462400c103610340d03a903145441869041881c0c403079180c01d02401407003c10018031401c2c2d4220300c2c050040502803800e031804410400c514500412946000304190745488080f10301030320b81004824448291420024014070318a8014211844402000965442c0000502d4140c40c02080d25608072803914030080c1480d448038040424241d16079000ca80e0540d103104002c1035502c07006800b44e0b41e038034003039036900100c5980c840f1056a0b10301d40300a011040d250144103801303059010100c3c1c400c0c1c00b400c81030b6030714600844400600d02c0c480c1110303c4c07406551000141004600c00c0308103001c0700080c44000da03101c04510208482c002086030040103044c1d180c3d003107100d00f180174540244540d16000701400c10388100c00c44e41c005055a0800801403864944610b42e0b212200502c0280c0550031f12000070203118410071181140c83d0001c01107030a0040f90351120000308018000d41031004c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 794270854 1250 794269604 794269669
    0xa1802090301110306092a0a090e060411031b070c0f06080a060e0c0d0f0c020601411804050622050a03080c0c1603020f060f18 56
    0x60110900c9402075007490720550f600300e210f40589018810040290403d42d4a1481804500306000083c0c4100050868603910010342c4600820305104140d564980660801e081e0080a40d0003920980c000e52030b0244040c0c1d04a00c0c6810749410200140e050501c0c0041c0e481402d0480c0940d0001400c0e60400020000301380c840301c0000030440703a95840b40c04080e503404851400301c1d03846100d8401c2d0100700c603000490001e407244c010410705004042c0002c2c00c0000010074001c8842d55098070000d030380404c00500c01340011030b0000b00d8800410b8050310401304030103421020a5410344407241c2612400402e00c0041d07440c500440c66007004442c82a400f45058200240d603400c05452440d88030302c000d00c003006403504070b00e603a06150750004000e0500d9030003598100d819090060110600034030038801c03421010f10500c100c6101a02c02007000940d05d0443c01040381c1d06410880d41c91040310b00300103250050070001d091340c0c009800b018040c101c1c2c0c81c1b28404503410110840031038007690808041c901d8001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 794272104 1250 794270854 794270857
    0x60e160e061e04050414100504021e0309070303020609010c14090402071401022a06270f0a171309090201210509011125050a0206041706060d02010c0209060a1802 71
    0x3204c08480c00e01900c9900c010040c05103806a420388007003501414244a141030036001803403030000040306c2004c41d0802d40201c003044d40050310104a290040d4a0402c280340c2c2c10014141c0240d02e400081000040740c801c050101140c140c1200304420010400281c10742da079a054500f0742da000142800c10b440101000b6000394030101289070495001c2c15104c003401019484c407032224030400c00070203c41c0c641405c080580004d01d6501c00403060035944504480e001800180442c0e261180280101d5245140c203072441010f8a000b0b0202900070312140c1d402c009080300351811104010000540e03c00b2038001243e000603804001040340715400313043c1284000a5220b00d11034601e04000b0414038407100320901d00c0707100d200002c4d45400040306071620715081c09481c00c3c1e550351013801100d43c0442e590303000c035025402c141d0000680c40700c004543c1011000c00d000c0180c0c8070104a400044140c6107078000b920b000844e2701c019018021400004009458070a81c0340c01416030400c20031130328481681e03050083e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 794273354 1250 794272104 794272109
    0xd03090213021b0d021f1814011a0402090d02010f02010923010c090308090411040f080c010206010f1a030c13030c06020c060711100c080d0203040204060e160e061e04 73
    0x81c0c803440d0044213000740b010402c05601401d144144801c540e60030890b1025043c08112694200519415400010000750400d140c07901c000b40080b03150a0700c40f84480d240412030381e070baa000b00c0c010010410142e5400002c80007450782401d05241e04020004102d00502c00c00300c1c0148900302c5d102800c5000b1600200d035407030002c030303841c000d200425003004115110403241c48020b000c11420300075107040d4649078100e040d890004080e514103155950300100d0148803103074050b20700d130340040c01480440d590601c0158090280d182e1308101682c0b07450035000e0510311101c40090030007804804100071310940e0040790030b003002280c4805512030720782c1003060b0142a81d00c298409841610038111560034a101078031001038000c0f46e42c1100014007418000358124454075002040f00038a104030008410a01a05904010050040e20380c81d00744180001c903070071500000c6481607205c3c00c210350503030201c11400480140e440c00d6001d02d0801c0c008125540a5210340d500c180b68510b800e104010700100c050003c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 794274604 1250 794273354 794273407
    0x81e0a0506130212010e18060406050103020f090c03011a0405041e0c020c220b09010b0304060f1109010c030306051003140f130b1e04050a0213020c0d0309021302 71
    0x14500034080c908000c904c00c00c114518090141001007284a042c0c1c07201d80e41c09081040c40c07040000480d01554140b0101304e800b00c03005540c3c1c100510540c02c2a4802083c00f610603100c028150400c84030344201e90005119014140740480c24542200d01800305440050801070310500c0000c0c010b021042000818500504d0181d14104030300107420b02c001165021440e020f8141c400032507801c1115543d81b00c845480c440c0b459203450444803c2d4640c0040a4000d01c00c4500f12034072802d1501e071000942d1031501d0f64000103420800e0b40010700350940d0455980400909002c03403851082d2400f900a0003460340025440310b40d00100d5110940c1607041403a208221010041441d0344045440600c100151100307851169141c2e107a4000841441e00983c101d20350715240e0755408006521500c00c00c80449003210282c005504000850603c02d000c241c0c3c00c07100303913010750070900903100269890f01012041d004068840e1194000e54070361000c1c4592800450350305641d541c0c0c450b2190000116540c40855 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 794275854 1250 794274604 794274619
    0x2060f070605040215130b031305070f210b010b1c050903070302010608120306061b0a06091208010605090d020a050907030e06160903030809010b0d03030b010f081501081e0a0506 78
    0x40000b07206504a03549040000c0c0b6085040b800c0c40c282d5147c80e000207102e4030200e000d110802c0d010803000c1007424000d0201035030303110906d07061951100d00041c07800a0b082c3c0d40e5980300320403000102001c601e18151001d01001c0341e154030b02241001d03070400c6090501118649000c042c800b9016001c0020404c0364025002804516500d403482d035540d82401280c3c2d58003407804c0c8042242d40c40c000c1d000b4101c050803043c0c0151588000b84001c0d0500307290785002c4542d20b44e03982e01c10b000c01c043c03c80300b05031059460908000310343c58424050024401c3d46034440c4500512030002e4115074030038403a0400781030050030307800c07881c60401c0d000740c020300c05c0410b0080144602c400242098442d0040e2808036010340e640c0d03808003865540c0503150300201405181c40d07552a901403d0b115141c0003016560701d0302030741d00850703410134081c0003614100e654480c080810001d80d0400c2540812440f240c00a01c0085c40d06064556817003031030601c40004218919011902e1009001c0000c0f41d07a0070030f0740104400c42e10349 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 794277104 1250 794275854 794275879
    0x3180308150f0303030403030b1206090a2d060c03020f070b09060c0307050711010918060906090e070e071403040c061b020d061d0307030302030a0501090c08010b0702060f0706050402 80
    0x110402560b92011580340d0b00c10400031b80040d109400c4019821001350443d400c0e003103400e4038941040000c0f146042d140e07005086030401c0c8159031307050443d0820300d1036200d03050f00608a0f01c2c2108401401005c0c001c1c0d40c581041c082c07607d10a504448040e566405515141c52903882d002441800654940d01c07544221000300d0b03c6070014208032806644035440c1d00d8038010980c1d8400d009a411071282a05101400d00c00046010100700483d890280b00030300000c140d401c4c13421801c1114401e8100307002d86450f141e41c403008030b1400120380381990000016600d080e40e807448112108401d901901101101c0403042c0000c219030014142d0a41d403460b120121001d06510310400480c48042e8081d45c031003120f19080340031589940c07080c107080b01e540490745011200503510030320b181c2c01040e040f030000b5400010000c3c501d47c244202030160403140e10602c030010056070010500841802058038888000817038004658034081200c071801c800764000c6484e400c103810924010700342120242d0003000341720000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 794278354 1250 794277104 794277109
    0x905060a0e0f2d190c03180f080409060f06030606080c03190b040e1605030c0d0311030d090b160e090114210706021509031204030318030815 62
    0x1428411840a80c04141e207548056294001d4081c040c4600c41410082c200c28911074180158140b2661205010101320f8100c52030140c2101d000c00181010189020010a00c01e014440c583c0c0c1100d81140513030003940c1090070000030f48c0c401d6501c0000d20501d040340000c1e117149458090380440301c85850410005035641016100d03c07204681c012020841040042c1c220044250f001300d500d00c15030000102d2001c0c0102141c02c682100400384025400b001e8034500d503521410712803014160940113020040d54400100e01401040c0700001d051011003146211034160800c10f0b07442090a40e181400510f101d07042204000300f09031031100d034841c80d000b64603122a0249141003c0140e003e841460103078078082907640c1004455586c1a8025021070300800c0f20a040c900404c4861856405880440d10700440640f0b4101c50b002240345808903002001410385011040c0e40c403805202c030950303209581e03a00d0101d0007440110725102081018400e40814103a100080d01d01c1103242600c0c40a000031032108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 794279604 1250 794278354 794278379
    0x4030207031406160c0305160606140a152006010623031b1305060c010209030d1404270207060b01080105011107030f021c20041b0c1b0905060a 63
    0x400d40884900907181c0b411356403042421440c0103003c1e00d402420702041301c21450070640688000d035216600c0d00410701c0516628400441c4180d4200e80071b84101d49400140751100c111902d19500348004481403002014880156403543c00d821819900d056840d400003501c074003400d00076000b06544006002103e151082c5c00c6030b0042c0707120040341c4a8221441c10800c05540f08207551004a00398440004040c6c031110050050840100005a00c5041203003d00d441c2803038901409040092041c0d118010414020071941514803200c05900381c201a0204401c4d40000b140c0140e002600c0001c0c01c0040c840300e80e1206411a400740c0e14501943d036a035004545c2e01c060100d00078201c0c0c100d030b1000c1001461154a481d002031002c0c185280c204201040b1103003450340000103a554005042c0740c01001c080d1a40424070080d0100c1d010030910021010210f846140d42c031007802440010780c51303802400340040610402d2100780d001fa8103401e40f200e20a0001e007900b070f03c5581c0070341c00001010820317680031b04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 794280854 1250 794279604 794279611
    0x30c01020a0810060806330c0d02120f0a0905060d1a010f210603050a0b04030e01180905130206210a050103050c060a260106110d080c2104030207031406 67
    0x640e50344c2c0e507032030300010803a03003545070800b81441e0151070a454100d07000205100c280c1d0b47d1299003260b00d81090450603401c020b201c102c50b1046402c52010703a1240d052040c01d0702c03072a11003540d000344c0358184080c00341c03003001a80d00200d0f03008801003500590301626400603100350741070700070450340b0100180040d80d5000400c00341e0404241120310b10342c6809035020b80d4003844044040080f83d520307580d07102da83c04e041c0307051410f4070050500801c01084c146c000c0c4040d60003a1080c689030003001421a000303080040c1da4026400a91f4603400841c016501c2d29000e07a4156800804032540d603034510b5050004407990410310000b9030070190001c0e80400386031054504a0f41c00c403000e40015180b000070000683e00c034503042402d100302a0000d105c07030a0344031020141d4090101d0b1030820380d41811809401504441c039007032681d0b841201d04408440c0d02c40c0c4095004801604210344606070222400f01e240f88040381810f404a0510806c018940d0006141041700d02559114985001c2c0c4101e05c3e442c0c10048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 794282104 1250 794280854 794280857
    0x11b02060c070611030a0203090d02061308030718090f0b0f0a1401091502010c0e060a02070504051308030903070b0c04080a0b0604091a040312150b07060b03030c01020a081006 77
    0x34030006070000166001000018400d100001e5240c0d031491840007150000d1310340d9891282d01004001840004105481000388240003d0040c0c0c546440388007190089041d008149042c080041040d85015901030b80207440200c2491b540b2903150000d02000707100503036020020500f0030b400c048907810150395141040402802c0200414200f00f0700601d00707000c3c494498100602400c1c0011a802c6503e042106081d0a600115441411820041c0154188003050b8400c0700d0400c0588081900061060116070b0180c4000c0358540d145040c5c0c402001200d031014103d60000010413910920120003803800c1846458505025280c4d8200408280900c0c001c040e0a5400f01c4080f42c04201d99031203da41c410801000420040d07000d9840e010f00101000d04017140c120540188400c16401c00c800c9403009248113001c00c500074244502d100c904845100e422000381d80041c4020500c030054118604808014040744d50701c00c80410308600079488140309100254034240440d501405c06241e601c00c0702e556 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 794283354 1250 794282104 794282113
    0x70308010905090a0f0812060604051003050a110c01061e08060403211a1f02070608060301140405100501050a1202060d0e0d050720150c0a061a03011b02 67
    0x1c020034500100b00c050700e050203030301c100c052140000d8802030318918803610505da466211801c6502d0029207440191000d0b119031130074001072250b529030401408003001980740109a50315401029070041c040b41c090794424402c00140001e01800540210044410840c2180c048908041c01c425800c2c07181d02902c0304540000001c100480d22880c000321800340c0e00c812200d0701300c8103c060030040380c000c50503c20142c105e0883c40c100ea032a01c079103808034000041500001441c003021009403a40f2460040d81c09004916000c0b40094400f5030000c2c45234028501c0a110900717190030882d0f0b5405881e8070001d2024104030020a0701d04144022808030391200246242d064495402c21074660048502a40e140b80c3d2a000c81d04403e200300926450820035481380da43e10511400c04c2180c280000101c449403481c5617821090344c2d00c4409004407144401c500c4581c40c0d50f00e40c00c0880c14260f01a10240541d0b00341808001c2d83c10301c1c4800c074220400d0480013040340854000954114451400a850140e00f2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 794284604 1250 794283354 794283359
    0x311060f16111f02060f06010207150203070209180d050f0f0708130f171917130f2103170613140f011719060b0409050a0b010b07030801 60
    0x44a0450300c01c85118195004080821002258042d4204410405103004404805540781c1d01840b400350400c240d00c40d090480d142c00d50020359a00014420602c040810052100310b1601c03d04c01d840e130550f401007841c0301b58201000311700f02c1e030303282c9076000c154030b01884070710f0328078140a00704540c070203d1580c604600b00306c00315901c103202c1d801c030301c2c0c00303603803d00003000070601c002450900e0001400d150703100541c40c142010425158558442e80030000341e444201d840c0c3d40d52904018441241d58011580746d0b10649400c402c003454000c1014105c24000c0302c02000c6a00c14010b00b642c0c6c183c400c403060544440004c1d400000c400360400f00082e010804c2d42e42c20340718002ca9558981e03030107034024100f1140703204603c5200b0125443c8090a00540e203901c0f05000030103502045050046c10791010000f00e60551006503034490b006c442180500328014400c0c001041026002182441401041000028182d040403038842034030035011540094248008a45605d02c0c0d41940d601a41654034500039a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 794285854 1250 794284604 794284627
    0x717030a02160f0e0a0216030c06060909080702150903060a0b01080a090b0708040309120503130b03010302060f07150911150a020c1201060905040305040f06090501050a0804021212040311060f 84
    0x341c060443c41c80103408100d80005003540d01039040345c40740f08e551403130100b99290500408440481c0c009044407410b141c50403000c0b0b64000d041c0c030311003501151001100034007100401e01c0c1c2e10a2921440c2c060003040e0030070503e0f041e41d9018504c2c0c02002c2c0c035002d026070f403240c59840132100c081d0710040030803507040c3c08208800d10601c20b1560040c82800d043d080d081c1c44c2c4212411038010880708a417180e2001407408000c2c001a14140c1c020302d038000010342107504581c00610f0b5809018851040c2140101e105014451960506240c0b03500700e081c204811015418000f503e44c5020210340e015200c608007150104068000702c03201585554040c02c01d0211000422a00c00d580c0f07a030780e40956492b54404251200c09104040c0203911a44840342d40302e01e090016100e020140c0d005100b48524060100500d907042800c88001134031034608440255038a1000030b0448401d19817244640c420088003c01401c0500c0003002501c0c00b400d60840600c0b40d02c020461184100d41c0359070015a4180301c201502c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 794287104 1250 794285854 794285879
    0x108010908040603151e0f050609010806060708090a1419060e1c0c080303010611190602220801020307021501080d21020307020c010f2d020717030a02160f 68
    0x5502500c4100c01c0e076507500548411b0140038140c03a50340c4404820401003900c0740c6068a0040c8000d849650801070050006804220000c0505024400008440040000314421500c02c03402c024001c0e040f16440c1c1d52808101e0100004080c02404c041c1c000d14107201114030100110303a4269038080c40010400280040c004010000107070440751030511138001410714200741c0242046100a40e180e41c940000201a284c5030f002180c0160001c0c0440d0383d20101c0001c03008000c0d44c00c450096910181510044103084500006450350300492034042034604041d00294001e80040d801c90fa030000d451030881c2c0060000b03102c0c3c000c007517201000c2540e8490041c480680340c1c00301810100e10149509003598141c0e1b100700d03107440068003c20803211056170003010145900001c4e1230004500240071042c0c1507100720600b44002c25440040108802907c01c000d1140505105400810215004c03d280d5689401802200000d40102d1408407021070b05505081e08440d65030750302034444d40c0f40035000b101c80d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 794288354 1250 794287104 794287121
    0xe0a1b051b07090b2e1d09100303110106080601050d0c08060f04020901060e030a06110d0609020d0e010c140a02151305060a0b010905090903090a0312080108010908040603 75
    0x20400000140d5090200901600e002002c5120001c168070340400100078000124039010f4810303000551900b002c1c44045d0301400040d0304a0308100c1004100814034582e68074080c4a5240d0052200007000701000d10700815201300c034480e0705c1d050115000200c0503800d03038416010712540c0d135000b5801080b1900d040c6d00910320f2a1702400001e04043d45602c40d403401c200c0c04076103c500300f0f0105000d12086060043d402401840d40e86480314617032841c0d50000c0d84840b10b104004e0300c00342d02d90000c0c014008008085910440100d08200032140c1d9070500c440c081c0d0040e500c407001e09841c188030782500315018081c03814a20441c5d40c1e412006800d0320140200350304041400f0086105d148100716032a603458a02a0140e0941d078101656aa900d14290b441d003080240400044ca040625507410380e60085298001e81c0c00845894030703165952a0580d286029200710a58000d100b5280002880300005051108612076030301d00810703070b0f26011181c3c26100c54038801444035508001c10400e8070b00ca075208480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 794289604 1250 794288354 794288377
    0xc080d060b070c0602060a140c1b030c0f070506030705161703070305091c08010b0711130c020d0903020607080913110301080f0c031e030c030a090e0a1b05 68
    0x24015181d000021480d008000c00300c411203041031003449425010001d03503a0203118140e0038000c4840c03c0030751244860000d440c0b0100d2000102c0c6400901e0200100d03022030f40a0314048a0320343c240401d580e0703591203078801e90038081d0040310000f06a50a0200c00c4074411540c60311060315006030b43c04400f0b02c40308550390584800c4161140117500707a0426001754002e00c810f5030003003843d0411002850406801c590f400242c200b0001b1002011500b00c007081d4110381465035100d840d1600d60a00c0355554a410501d00e60240c02050b550391882d0407a0b1203601c640f1850f508a951004030000262500704450001a500410071f1100c0e5000a40c8007004028654002e8a02811559a1042c61007038a80c24031501c94002001320060009040070030030180340400140040010b8508ac1d8003082d21182c00d102c10384030602200004486004040003150f450500007070440b42e40f80855030004001c2d491074041c0341c44c0c03503603603901050445035940140f0051071501000c107446110071a1040d106684070300088031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 794290854 1250 794289604 794289611
    0x9150608090f030a0c030e030321071b05060a060605030f0a270b04020312040311130b1201140117030a0305041104091401050702010c08070c02030703020d11030f010c0c080d 76
    0x141003602c10320141c064907802c0d0b111048003185030b02e0050b240c0d02148002031b02030b900611481d45000f0340301c83c0d18031583c410910381da00303a52910081203c900501c41075083c410741c1061900710811078000750a038418802c1041c20012107440d0340048502d80b0023940c42c901d9003115480407850700070140e4007a2001e0b090344600711862040780d502101d0700300c010300426107500c5a01000c110550400303004071a14204900a400d240c44d04580da0b5400b510009403080f1701800011031018000c142651021820840061030305922404c80c003000c0b40030b810502543e0280301400c0000082d802d0303440c42d03100d11012000020310b00341803031450700b1001082c000b0000d440d2140c88480ba5010f50726148181002540030b00c202d4030090000811007400e44401401980031a858007a1074441980d200b0346e15a0440010f1819502465040c00000c0c580741440d00f002c0c4d4000b14614600d42042042030b4a203c0013001502910326103c20088000d08851404084401054440181d0000640500c009009282036280c000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 794292104 1250 794290854 794290873
    0x80423071505073005180409120306050405070c02060d060b04090c09082b03060801050a0207110a0320030304030f050a1a060d0609060e0a0b100915060809 68
    0x40303540204094007140070030b100040c450140700328a0180310b41090210100000084070030800104001a00105420000003041064810764201c6607544000c400500920050240d410102900c805a14100c00868035000340002c00c0d007002c0c01003e1240c000c0b034961b40f5400600790284901c0b035001703480c0305105565800700850130440d4200a4070280051220005006280e480c0c080d0400d08560000e00c2d140c0c1c0408404200a488080d0321030010744078011103c52074441c008280c021b404c05812180b00d40d400d240401029030240c0e40600703880f60007034040d111159900d409100d03401050340130180080701c0d080c01002d568180c0764a100010714025044901d06a660f880d09200b80b4040641124203410111081091180380160030840940000c55410181000c0c00010b12203042490020003043e150300f0300780223014280c3d01c040402c13012901500d0810740c0b107242c00c0901110855102a48e4990548042020507451042c1e043c6458400702070501941804029600c2d80c200410780007851155007c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 794293354 1250 794292104 794292119
    0x81b060936010b12250809070611100e0a05030a0c0c0e070e09130b1003110603070e0f210d0f030e03031302030715020f060c1204060c2703060b0108042307 68
    0x5d5001d584451365454178a030500e0341c1c110f400c12090b980004200304079141640b04501020909240049102d4800100c200381c81c1c1001d4107181f640c1c1d4018015000114148207810b410071082c4401603c140911041c0b80e8072500d264415400503151040052020700500a1909001d003090340c000c4000d14000c0400091070f44d9800c5680c00440d1402e8524200080c10403c000c0c500300175144c040c2044903140c0c294174203400000c4c1801c0d44805528841c2d100c0b460b00c2c0e1110b486804603015800c1c503200d181400c101d54182c43c0c0340c0d1351180b954000001001412062903035031282c8121945000950065071450312042d4a84840e078140c01d0080c0e03414020008000368902e500f02e0f50712280e4a154000c1d145101c440880e060030140b0003040b43c43d4408041003480c41c1010401d84072540194041e400180e04111148220384040141010300480482d4120003604804840691070032603210f50402e016141515004481e0404250790081541500e1081c00f4440559801440c00214840c012241c01e255102403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 794294604 1250 794293354 794293411
    0x717090a08011a15070b0a0b100512010501050913020d0b04051905011418070e21060112080412030c050709060e060307081b060936010b12 61
    0x211103100c1e0f640728484070b024200030310915041e40c021219404801c1c0044090201c920030701d07600038401c801c0b90001a00c020003035841034100a2001d00450301ca0300a08a010b001d550042c140307000c03c0c81c0c03c41d000152941c4250201c92203408094950900c0b002c00c0d0b41040007030340114050015031604d1f0040c3d10102d40340c0d807144a11469148940c2c0100c00410600c9008640701a008010407001d820715081240c0c0720003008503808840c04a0907181d03555807440803204103421f2100b1380d0f444003c60840c04403120707620f48070b103195680c510f060329140d9a94003000312590080290040c2107001c1840308105540c0281c0001882500070300301a401542d0759030704c203401e000b900d0300243d00b03081c0c1e505409c6c05030642044805d68051420b50003020102e06003d0b426503038a818505000f1a03c002e180c00000980f0340380c1c29601c010030090031036641c1089008980d007003804940210b01860442484181d6039182c1d40c4150f81c103c0b8000d0880d58507121701c0c0e000c28014000c0040820b1100e016156504080040001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 794295854 1250 794294604 794294609
    0x91204150539060402010f0c2105030a1401051809071205061909050705040b0d0b0901020a0311040b030a0c03060302060720040b030615191502210717090a 68
    0x2500b94500d140d030101e964582c110290895003407940503408010040c0d0f002825011582c0480c144a1903440350340c41d0520351074290f02c2c0c0b072000109082c03211740c085c3c03a04080654041c8403042803e112280c400e04110880007824454a940103500c0c01309880d440c00b80c08002504446010203071558a0348071001c503040c0c09240030303046030585c1c0072038100114a01101d4a58000a00910040c00421455261a96580d0701d6020b014855556030507040c15642c0c4850002d01e42540c03005201b5014a019200d090013900302203200804603043c4150b0000341209134007200e0079540000005410350f1500d000d103400501d000301040040c1a80c803200031016039520030150001034845c18100c00041500c032144c03002513601004e21401039040c142c2c00d0113540c1c2c000c10601c1d8000d28040c4110038800b07118000810003020841d0032100d03505801760100340110708040c81d0b00000c4180e0201c44c001521f03c0108a010b02503105110582e840c140000707000104242c4450f11151034075281c981c00c0c01880000107402081e00e6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 794297104 1250 794295854 794295907
    0x4120f0c0f03021603080d20122203050304021504180510120b1e090a0b0405030d09031115150603090f070b0a080f100e040f05070312080912041505 65
    0x106188544860074003810648e601c001800b20080c0071810344c00d20b0303280103441e0f00c90300746040708000603500c1100c00700d1184a4800c940c40c0c9400c421031800d01507c541d105a500744d000300e0155450300d40d2084e00908483c1140c941d0100b00c200f600d050845640180809480c201040e40794603c002a03103003c2100c102e5004e80a08118006400d0240c06e10740820080b02c4100780d00e944040422207010310108120525642107118643c4682d138030300d849400c61003500c2004512900e480c03465028540c0c445940891564ac5504562040c4469110f18131007450481e1245000e4100c0008020b40307003090809150052010400c881c401030f01031081c1410075205820a140100001c20a242c805600440d0380341c200c00a15419207041c1071660310050707110b025001e1650084482c4001c28100203401d250351a1507a0004103881e522900c03440c2204102090065900008281c02c010544000e008034140d0080307403070014010b00d41403404416128150064480070b043c003100313120311a0032143c07d4a0495030703124174 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 794298354 1250 794297104 794297107
    0x605060604210c1505221503020705031c0903110105040206071403090907030c0e0402180f0111010203070801050f01020c0f011407050717150c04090f0f021204120f0c0f0302160308 79
    0x6002c815140301b40710300f0710810000c0814100460403440301c001c2d0310341c001445c001d681e5180c9814101d1840c49030709000030740045240c60308101c56001e5403041c0c5803d480390740e071140c40c07c4091481038260f074020382c0d0296100004001000000b20280380b080c280740d015000313590600030030000049903880b00b1103c0d240869200c40007007044551108495449110840341181040250340c881c4108070042c40c2a11301075043c03030801600c503038020050303980b111114070002d55403450309040c01440c801d403c5c072405000302d0f0044900c0b801580007050212242e03070060401ea01c0d55010400444400c18122080702130810100b2034400030078003e10504001d422841010000c490f0251111450120041c58494250b500103040c03000a0301507904880c00c840100c140490b015618880c070380000c00d0b41c4d00e202d1200f98400500007050102410718144100d014000c01ca20203441604103480c1e103042c401c0d1230400111904860000550460360858095002c0d2040702c850408100040440800750342096415020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 794299604 1250 794298354 794298367
    0x1401030b0603040b0711030a020307062c01091e02031009210c0c060201050f13060605041407170106020327030105090703060e030a09050d140313030605060604210c1505 74
    0x20400100403600346c0860007549802401c540003511790080c03c000900d0b085d266420352000312001070300d59840c2d800401d00c13500781c440d4240c107a40c001d0849900c01c440c08500e03003111140a050030350994201c0303038010740a0a00250341484680051003d0340e812280c03201403070348581c0b06403c0a2032191900c410f54440d02e510034500d0418140072001540084116818941040006c018070348043d50402a5503104483c0d42c2440d2030100c01901241d0425500180780c03500210000400f810450301452564503507941d81500101c2d8415005001d024100141c0e00400810720144500350401154581e0500c1070341c03045000e00006030951740142c801c054903500105091050090900c580843c110440000f1464501040c1024181244030302c01d5510600301250440e0070f01c28045500f0380d07010a003109581e0707684410f0214071511159400140c40d80c0349840c0000e021414040115015600040b8010401000f8a414812205444041110f03050f55005002079041c1625000d080405542e443c0d960b20f402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 794300854 1250 794299604 794299607
    0x20609040603150e1e0304060807020307051212060d0c0b0708070c080d020d0309030f11150a0507020f0703050303040822030b0a14040221031b030d050f0c041401030b0603040b07 78
    0x500e001c5ca03103200b01d803507031aa40d12200c400108403400c0300c2941c244604140d980d1b10084c1c0c158001e007100a01640210300700b11641e034400d5002049816081d02a47d28262508402d0103000001c400700103001c11046c0109000c12441c000141020700d01c80c008480c60802540c0d220010340b0481d07407158265070300c000c2001c2a141d8043c08480d0040b041440e080041d1286900c00030720032800001d180007408001255100c144e43d0038040300c1500000720301501514103210001800401c41101c0c0300f8018041c1c0d0345890201c2c2c0c0045410011260450300030f60660302d42d500c0f510301c542d1100344a464007080381c01c505602ca00850b0b0302c8100079409600300054a00e03081e443d40b42600c0e810b024024181c04c0c54000c110059031a15498040500c0080c44807284c0610210020301d10701c2003080000b0841c00420170aa10fa210020007001d0744001480c05020603101d400c44460108025120f10021010600c01440280710050722500802814907020500803004d1b00400d4140d4010f40c1c080e07600d00e480100304803489 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 794302104 1250 794300854 794300863
    0x3160b01051f030209010302120718050312250c031a15461502071206020a050405041811030715050306040902030f0f0c03070b07020609040603150e 65
    0x512055a07080080148088120031040c5031000c0403003030583c04140d4224a0b486503044c3e400e0503640c501046020300382144c0c06080d4408180b4603900b69000d940c00400c0333034240490004040c45128140300d08010401c440c0480303640c82403500700d0614410380071500c04500001205002940114404d015860300c0c00c400880f801d0009120010300e09400714035800c1e50711351b2000d0f00014500d83c030112401c80c002c2c0d40c100d5000d0b080d000700c2c5a0a00003800e26044040821803c1004031030200e10407500b1070614240a90312000c00d8800d8004c54822038120340017064442c0c0050801403c1c618011b4506603c650004080720502d04510401209842c3c001003040000d08202851410440041c9181880c1ca00c0700703400200091011300804c000407001ca144da44454022502150b8024182c40c8030b01294550a41d0320944222680410f1050030315096060401040030029184003440a5152030101d40900440780d00480c25aa0400d0f91200e00202041103150084a0600220800300705a190600d83d44e140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 794303354 1250 794302104 794302109
    0x406030c151724040e010b01030f091106030c2502120703240906020a0f0815030303060111031215040b010203040b070204332d0905090102090303160b01 67
    0x2480590030740c4802c8048054030341d030781c0b1849925024030720350803003090150000801c0c50b04681240c180b82221402c205c040d0800d8a2403002a0b8080204000200c00032003a14101100a800607a514800c0388450038048001c580c8503441e0003805290803081500104c0c81c1050421001250010842c00011072070544215040e4031a00d000800340b20381592107442c0e121845440d15045900d0545024555a9403500500d801ca6040601107440d2070306404060004400d11008000107880d80c00081d0610600c1f80d0b14050004000c2c00a6096944d854010b480f8605c2403800101d0520081c04001050040d085080f842801d01050200f55800c0400a10041d00e07800403a05e4155042400280070f0450444203450400740c040b05c0201e0195441d48030044100258041c04101c032441580700d003002c2806191a4003201c4d01d0401d160441a00010101d4010360b540302030081c600b0085c6410400115207400c01ca40000402000500c1c0c1040d00c80042d1450740136150740090808640140800d214003c0d101d90300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 794304604 1250 794303354 794303357
    0x32006040c1401090f081510060e01080403120c091a0412060b15031816121506180510090e031c1e0b0a06030213031e020406030c15 58
    0x210341025518000d42890301c0c056600c07003101c61400001d5581c842c0301c40b54010125207522803011034841e05180c2d21081d04518042003003e1660114500c41040c1d0b80d004100e0b4130039920310b01903c0301c0f01d004442030749018105904201c400800c00b064100e4511601d640c80341e0f03649802803103916017180c95030f41a0030303444126a20ba80c103200402088c480c59140c80e11441d03206000103104100700c0c002500580319040c030140002008801c200e00424487d4061280c1d024040403a202200e007448100401102c0c0d0060f48828100b00c080107000810a1282d200700c0c1c01d610402044503520703038021111101400e09012400f946506c00d1200c54411003000f44040c220804041c014200490b058a40d01e11421054100b0704240d0f00d884400d8043c02e0340601c01004c03601c040c400d0700280e078480480203050780020482c450110103400180241c0a4800c5650b00c4080c00100c4903d03901d5600c40d0300c110904a034440f071030320996103580c000607170351842044082c503c110700400c011403c0021030031081001041040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 794305854 1250 794304604 794304613
    0x20a0809011a010e03240a0f0911061308030a022a01140a0306080303010f06030b01170112080d0507050406020d08010f0e061f02060106020d1706060901050f070320 72
    0x491507094003a03010b03040340081c01c090b65468041d10119181610009806520340b03c13003034501910800350303101a40a103000301130134056064061075480c1110a030441c01000d00d0001000da9600f410460040c09001e540c103041d0b0840e15a4403010300d030071075100d00c00f0702c401604040303d0055507102c00402900440c00c003410002c480c10703d00f400039081d00060b03030031440910000724081110300d100e604024013405000050300c1c0c8a50b91413007005140d80480c007038400801e0808c0d48103a842e500c900e014100580420b88641d08591030004c62032010750700b10f50f081c2c542c0d0004003c005400b101c9030051900600040d070f41c941d82d85203826002410268a04410010030900c50010090628030001c0c41c0d051b02e0004400e44040d4a9200c0065400410b00403c2041d02081114141071141c0100c1d42904895807602507500d5803c02500403130750f14008180c2140140d0707040010519604040c40981090740041c107003e40340032050303400032902d0740140404400180b00700807003c8000c2c884003d400d090100010040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 794307104 1250 794305854 794305871
    0x190210140105090f040206070615050a09180201230403080706051e04060b0d0b0702280302030d0e0a082206050c033c1b0705011b06020f0d020a080901 66
    0x280860f00c00781c5400c11034005100400c0944d80d0f100101c41c000c40e80b001c0200003452110395021411f204500c00d061140095001c00224481076004102c0304810a0810340081282940155101c3d40329413517120180180302c0340e00c410303010a20002c101640c004c240240d00d0340c1c030515005080e108001c1c11409120002e040d141c0400b001c8403200e80d0000d90042010034501d500801103030102d980c40c4070203400340c0905004e102c0c2e842c1e008203415810744000300e0b42c580e40100018a0401c00b0700c41020050040c0e1040240c0700d5812820342c04031400c81d100e401940d10220160f114145190402c4110916400c4000e0f80c2d20014141d94000200608103428014203018541c8101c607160b005045458000b641841002040892440314030880f08405200900001c000c802045820f500003440b01c03103001548945070441c0d00e1001600c1d034120b8034142d42e5070002640c0d03100340c02495460031000310790b0550244a54480707070003054050401d085c034610005072034000511009024040191000701e40d0f0740342c860403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 794308354 1250 794307104 794307109
    0x40501020a03081306050103030302070c140a060305090c0301060f0e1e01050d0309081605030c150a051326010c03090b1b0c10151d07030506010203190210140105 71
    0x880d00714075090b081621440d50b85081241462201d507030010078591410001104241e00b61303005d080003d001c0e500448130707161910407001c5508030580e01c2c0e0303034820140d1004204a52080d08075592000d035142c1a40c00506041c00880d00b0361300c0c20f41160316106402003050002c00c040703480d00c56000c496103484207207240c501501548142c2c01030190754003c0548010a00034540942110b80040000c0411210b1114115002003140c5e60039018a51180c0112081c1240915140c2d0240e100d0b03107194a4110310704003d108095900d60f10404000c1c03001031010b48005984c82e452000d82e610a02e07038041d0030301c200903183c207070078211f0783c1076001c0b0000c0c146040c0c400e2000c03c2c070700c003a0682d1100207200b0300c3c82400c01014840f069401a12980b10f03251207090040c0a020440d50031081d00d184103160300341c44440d200d40d01c00b02d401c1c1c511035010000204400008110a100b07800090300b001e01801a02e01e03003000c100d01e10020104c812172070300242c1d111030051200c01009100b085525a160f211409003541820300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 794309604 1250 794308354 794308363
    0x5270a0203010b0f0d0902030601091d030c030d090c150903140f0a02060c0a06020f09010f02060f24120f120703020307060902062b0b010c03022d01021201140604050102 74
    0x1340c244042c2c0010540500c0f0107000d501c5065040d80050485a1030340c1d48458050290000207108a0510422801501c0901d4004180d0340b100101d42c003d18201040e004800008044180050301c500320448030006402c107540a07890711001e056a1505d4619045007405003c480f1540241171040d4003020b0580c184c5035001c2087c1070324035030440b0090303510f081d0064541c2c50329640d500090401480020801c03491011100200640d50080e25a00c500c076040a10aa803074003070440b64850004e0000b4002802d600307202100c214514802280ca141c3c49880b440862910341000e4003071060350f4484040c0660241c000c101082c01080c1105180380742c81c01a0360029180d024a110040486450706004811551001d041d1f4031401c41426520748240f05c444030b0260241002200f48003a1803078119460b001e0352144081c80102c54042d00280000c2d03c050021046900b141d00c984030003000c0c10040c01510481c2030000342004a02ca0300070a0543d4105409014101a1030a141c0d20840040108110598001c203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 794310854 1250 794309604 794309617
    0x3090309030c0d08030415020d0c030207170304020a03060902242d0406081503030a05071a041131060f0815061002030f040609090e0a030e0f0102030405270a0203010b 73
    0x40c0342c07c00714000f03290f07003d002e070003940496607100741403a948001c02390341035024041003800351310300010b803407034584c1c06d5440c510003650065044800321900340b000c0f403a960040c3d00254405840781c0100a8082c46044071210610700c0900c00c80c0000036540555a215015030310200003c82100c0d0519100d500e0a050078421807280105104000e07000072402c088d008440d04100c907014061701d6540701445001070031980803c40c111125494065012000320103030501038800c0703170300060341d50741e10448004103e28091030361845010b0b030086001c14400c043d030100d0203440c000e07010140425850b003800c00c0208041440e4000e150f01e544010342408000529020701a04040709403200c045400a05070120b0031445482b403460070010303000600003120340d03000c81401e04070b4500403820032005031030251131a118401d9000c0500010a03031410071903185481d034040a420401401142d140903516004140300f004055003503c3c400d0f400150750301030740350070742c00f0326600c20041441103183d50b0500da159031043c040d81 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 794312104 1250 794310854 794310863
    0x20406050d05062b0203071805100b041a0c0c04090804060237020d1a060a061b032f010504060b0a0e0f060a030b0a0c122306041103090309030c0d080304 67
    0x26140c80085d03441c00c2c0f004401404854190071a90803030300708054003615090b42c1c4000c1841248000045401104003510140da20400100305607220b040015200c54012002d088001c2c0038406040395280c1d10303845202c0e001d40c071803c40c094071503140610103420300000c40c415100386401e00c9008080002c44042c42e20a50b1030b0203481c03002c5003220b80045403200002c2240200802b0750005c54400565001e032580f44502000c85030304203295203580003110f14030b45070580000c50402418440001900a4460660810034992500c418600910807280e0100d0fa00c1c4003c04e460355180240424008107000300081d00105883c0c1c810414540303510000d0040d030090900a49886010120316550707141e110150013543c0015040038142003141602c4010f200c07446001c00842e600e001820622001400742050320310100900c1612000d8a0740500d4034150300a010682c000d960396114105a01c0040103103002e0710481004549072100b00b41407615281390b0407041d030b00c01c42504841a00007400441265442940b2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 794313354 1250 794312104 794312179
    0xd0204021e1204110f010f21060e01030501060902040810051b030a0b030c042304140304030813050604050d14010b10170a0506010c020121020406050d0506 68
    0x20010103040807585601c40e141c20300400a04600102254004580500e00503407482d04030542010030044c4c0e040c450301000f400b080d0400b842402c0b2038082c40f80b1450700c01c010a21a0a10b2640340b19120454100c2c2d006030000104900050003481070910511000c2c0007503407021460305042000300c95940f0a0500c10a840d10b4403440050302e6006407010b503c803074060050711151207050900d40a0f0103058110002e0380207100e580c07000c11031441e0034040c950500511003800154903285075214181000001e01c1510580c405c9001e081000a0420081c00254060046c1a86a036401104000210516800b03144203120030701040c4070f10b46d40c1100d1200e01c00e0b48244016195080880110301403d102d0f0319003540180c8110162007156006210061107058100c43d5079126981d0320340e220103d0740c0965510703000a0040703100740015400b41d0b411186681d940c1083c0b4201c0c03854081c1000c1a41d109800400014001082141d030980a40c05a160450300496a5516603034144030340c6e54050b0014100303401b60b40f01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 794314604 1250 794313354 794313367
    0xc020a031428111203070602032508062b020316050a0614090913050601090b03010e0601120f03120f0b0f03010c02151806012402061009020d020f0a0f0e040b0d020402 73
    0x313041003182ea0440e40f1010554230f9103802020751305c59444d404d0801000000300940540358900c0380d00640e06c520001400f02100a10212054010100c450710840420412120407800350360100071464030307d17202c1d0840b02c4c0c0150807c0c007400b0900596502002c02c3c04040350030341282130a0401654500b0105603414003055503907140c4000040c80ba020040e185003d070000100e54400309030480042c001c8150b0090100c0c5240314049541c4450902c15400c1c144100ba402c40d001506c1602d1b010401802840c0c0150b1000e210400c030012101000045a1203030b42c0c0c1c1000001600b04043d079098100801c03802001111030411000e03480301c4105002c4c0810301c02c0c113070000b6107a47c600b01c02c1c6084041f001048603215a1a0405000209a602c1c030300080c8946002c005280b50f0b100082651150350000c003511401c0e4174140841010707400141c80d100c00a078003445540d4604030032002038100b00040b50b950b01501e4441140103401d410224905e98051410450109003a444909240c1c4109a059400607944d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 794315854 1250 794314604 794314639
    0x907020d3c020d140706050402190f051005030403080a0504060e0f01020909010b041a0a0201180803040308090610140a0302040908121311010c020a03142811 69
    0x1404650000005040004510001c280790701c0304008041c0c950200e480c40c004003282a18007402c02d0701411081031041003008001451074008542040c4003914001114410508614a100b041d402640015142503810803541c904454001c01c00041030906900d0760409480080c1010802000070201e1916440860200062030344850b0400d9010000d441e00c0b02d40601665012754428285680b2030f105d440008034a441d00b5800320b8040750051200d64010070440340140c65290040d0625601b076558a184502c409512400d000ca032662254482580e00c0c80c0c54500a0031821b006000c18581d9489002000000f5105040c0f04041d10078403441d02c1381400a000c005100c401d1540c00003074000e1b051a4480c0104204140542213521440034228490b560b09200f106400c414800e01802c00325150701a81e50030b5004664021080b0b001401e000095030f280e456001d10040001712354440d6a0100055210141244480416402e20704031145603002d900e464801c8030160b003c030504d2003500c12b2402d00d6103a6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 794317104 1250 794315854 794315897
    0x3080f040c2301020c0303090d032a110112090c060c080c030f030415140a1e0e100609050105090c0a09090501060903150519050c12090d0e0907020d 65
    0x2015615000707007030310707100d0900d81e03080222205620f0b0141c072843c801000b0901e030100c10384440100c090b05545229145803070841d8002c0070303524502d039005a00401e40c3c0c548119083e6100720180a4080d8600b00c0c1d4270400010500022082d0300505240b80000c2000091001c41002040751078a03d00410240c4240c00c00404500c2001310003801c07444002212440e020020000e1441280200700f4072000340f0318803403514103442000c11007002c40b00303610b0002a00075034113a001248450086004006035004468400d088034440031624140d5070088022103056191400303002e0290000d42c2041c401c80d403420000c10000540500719403916140481e401e070765644100034482c001c2c500800305103c1e40d41d440c01c014001186a010580e1100d180201507442401d850103024024428504280900d200c1000d400d001040042c011038020f510030822074290301280254070713000300107000160443c8403210308007600c0d060b540703941c05015003440800c01009030780210b42103511800740c0c148021000010108441e07a07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 794318354 1250 794317104 794317109
    0x6031a0d0b010806060a0803030c0d0207080307020604020a1406030609090c0a030f1a0c1b1c09050306072c010c08070501050406050a05010f03110402040f08030304110d03080f040c 79
    0x80548440480c05114075005854101e031000f9060711002c0d254001404030898150040c80400e60080020400080b80c00005120400f0344032401410001680d44440fa02c2c0d1040d1400030069101c082404107500d0807151800052080d24007148000d801030b0040783d402e0000404080c8202c0c8003c5c0000c151301c42c00d004560703603074900a003110101d07a1285003035040c81c01c1d100c5040e1125000e240d51441c010032a1400240900304407110f160034201190342d04110360400300c170030a94030301802114100300154203444194902e2291103d891250500c800c3c180380c2040100041304110000d110344002a01944001d02d039002c40b0030188000c0024400140c0c0c02d8104503400608441c400a95082444810b52049000750302c90f4200b4440c1c3d4840b424218207555080c0503514003184508820800200c5442131000765510140015040a42d01e800c1405800070030790100f0740c2078000000b0441008016a099683c2d40e1040312005860002900c1c024448075006060004074050340c0c0100e0284188251361600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 794319604 1250 794318354 794318359
    0x803060f1009060219021c05010f02040f03140106050604060804061e0504020415030b1612020304061401091a0906040b040e03090f0d050319050c011802100507020a06031a 75
    0x1d050380c00c1100400020780d40c4600c500600440030000300c0500d8052200c140c0540051111036240000f080e8400620030201c0300312107565032519550002e29090002d0300c010001c06024442c0c003841c50a1030130380c00e200c1b000089400d9160940138001c603030740e0100f5107054403003030b10300306425940f1458250b0041030700701e14910001c407a45014108604150700081e1246100380c506110701901044c800043c211b0501004110424010000d00c50300c4076802d80071080841d51034180c0e40e510b40070f00d4030303822641305403030951711941c940c481722184032462154140180aa01d90421003c0d1a040343c002c0b0b100c0000b12a103100c0d01080001c142683d032035401c004622080208100301000d800030300a6540d61000845a014580208100d4103514004424242064001c03016610380300121000280c040d80700b00c074140500c01c0510031a0302e140070034840c880d1500c0c0300c1c7c4071000c1900180d00401495000a20100c0c04010382000208010b86584103403070b088908500780031810051030005601c1a004540303c458 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 794320854 1250 794319604 794319619
    0xf1d030c1c09030b0a02092701172107030201110408031602121b040c0c02031f0608060a02180a0b0d15050d06092009011a0f0705010b03010515030a0803060f 69
    0x11001c1e030903900405032150100d03941d10840d4010b9084540c0407450038541070381d81c090100100b2081180ac1c03084001c00e11040706035410790000019a159840800c0c840c0c048000010401d44109074092080340d032848c5480d40790030308040c0b5005640f5644e119042201c1604941400280700315190b008181c00318424180135034442e6804c2c80c00ad10214032801d1000351080e810400d61040482c080c144402c070168002e009018500c0380c0007200580260800314003480c69950b01030001d0b207902c041c001e95000c2c4d00c07a40c1000d03a5600c00e049002c1503540408050511405501c9001c12241d144070080ba2030350174824101103241b42c1020502c0d8180179484d8000b0b030304084a0b0380340e50f00308011540700405c0c10b0710500b13400c0004c112404940362205007824540c2e800c0241ca41c014030800300c41c3e0207031725100c800c40003142b842c2c03071040804045550050f40c01111160344401e080c0c0c0030343c90203006855000b0205410541c0038261200080e5854131311320030140602000101083c4643c03201401c0413071945015140c034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 794322104 1250 794320854 794320861
    0x30f091502060604150501020a06110723060610050415020708070b1209010501031a0a0f020d0603020f120d051303170a0f17010e070c05010f1d030c1c09030b 69
    0x65182c40044030003901c6185007a040ba01c14180c681d102001740c030300617401440010b0059130762a0080c2102516803003411030610000b40041c00c85299100070b1317840741018a401c0c1e4400a00ea80c60000040c12281c0b007242031841050398603501070150341c00c461710705200058003504440c0030307070400320503803c690707007174080c400c00030800304661341c000c1901031812601407245a031580241ca088480078000201200308251040110788680c44000f0340056110000040030900030008204a0b40300703140f0078003240c1d140c80040003035180c80f0409a901000c00c4d40c85194080901c4042621045103002010500c035004c00d003e1241800d0081032805103a014000490420200007281384c1c070781280c1d0815002400f42c2e184600304034401d80400b40c001400000c215110703424020707640c0c9030300c000a003585c0c10401d600c00f4060100798240150240200b00c8100000c1c40b1403404019500c8026982c40c0c1c4480e94410003a044025100040d83c9c0189070f004040d0300e030b1169882000302c2e01c0524a5001500035012513041c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 794323354 1250 794322104 794322107
    0xd03050a090c15020f01020f0d09080c07031109130b04031d0310060e072a0602090d1a31050309130c0e040c080f07110d1e050412030f0915 61
    0x43d10400b200540848100e9030006001c1402c0c5d01c07680d011403450313000511051482403040d030051171004d4440c15020303040c41c60032961343c1e1510105500c282c3e0364050702408c114441c20011740813900325010644980c443c000380e0322000d40000c030161000301041186000c49519450261103080010360081c1503616060900c0400d8000c1d11160140368140c1c095030021550781405400c81142010a00081102000400640c404071050300c510070780e0460703000c000d00d8a46a80301c0b5900d0100c14400d41d07404034203aa0f00615a125020020715040c000282142c0d9180701c02200004441d01903281d20761403000c030001c0c0ca443ea046000b146012034110441426410700001503403c02414040da907540c00350041c44001c2080256412041d600740442c2e152408603104c0084d400c40c2561211450034071958034994084250f15040380f0140030382c002880340ca5942440c030746c5e044580002c1c10881c40d04500349410401c0000f00e01008510003824070086503007040d2014001d0724404002c2c00d00721210380318402c11050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 794324604 1250 794323354 794323379
    0x1020a020c03250e1f0b1c06061718030a0c0b0601022d0a0c0909020117010f0b0a110115030506090105070203030109270503040e180d03050a090c 64
    0x5030718420701aa454001c1e410004420310301c1c100d68465000d45a02c0d26001494400c0d050182001d080d0105807600c5400300d4403152a10f1340200311203628540d940094403902e11413401c0141e0240b245900b002401c010480e03008168085040c0d1a084a29050b1a200da804020320031a0644000e03901000c20102419030700501c400300320310301403041c00109581e00c800490b03c4800002005200c08410180b4030030301800c107411246502040380c222901504c881d100c203111b0025650004440d161254110000c40d40e001c1030020180c18052408402541409c80114400d00540111800c4100200d04030022900c00c0d01c484111009000080180c03000115845108100c140402da90a100d280082404201d0511a55216280590180d411a402c010a0318050148200c4000c08146032403407039a2607500d880400e10342c6c1e03481440256500e42c80c1001c2000700140040050003203015a07a0303425041200450140105034807860006150f94400e100c8034010001904082c2c018003081801290b092805103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 794325854 1250 794324604 794324623
    0x1206090203060a06020303070c0b04330e01090f030509180108070e060f0307212108060d080d0f0e060921090d12022a0103292101020a02 60
    0x101c803c190b06459504c1a6681d100580e21840000c04007244017020030150702c440f540140c4520b109030310400400e810f141c1c01e021209146c05d00da4102c180700070001c2e02203219642c200002d40d0000e0181400310b03200c1c8031200c954500090180a000107070b04125584668080d503104c90380300e049508a58445007801d55400b0746000720700d601c401c908040b83d518035020111540000004000b8000e0074140780c640516881152440d00c10071194a02c2c1d10002001c0c2120015000200303030007164541d101c240300900c000e1000d41058081c10052891001080800003100d941c842000000303c1e0001e200040350b0014540c45600c000240035280c2440b02d61907001c1124980506607001180d1305001c9003035001214854001c3e142c0d40048603201d22800120030081061035001d40780181c1360115210140d110380442c3c036003015810054240d1440c541c6607007602c120380d16011030b40a000f28a010300040c400c180400484424401c80c0c00941200f241a0f0034956010409003110003551038a04460000c0e59442042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 794327104 1250 794325854 794325859
    0x10c02070303050d0e0c27012310030e0d110606060408070b0c0a080a0c02010807050c0a2004022b0203070e04020c16080c0a0e060d080315040606080618070f0f120609020306 76
    0x1c4000a00c200b509818888402c1c3c276243c45150144120080240089a0b0340c035800506480e5003c042170340e00305100031011510706440b0b800c01c003070780d02001c0f60614030001c006a20800c4203100900076560001043c0043d50200d805030740d0345418074144c06181c501003c90041c043c4800040310081654041e69854595100b80c880358007540392a00183c0b0b80380241e03802601954408003150340403d140801400ca02c0d500c0444d40c00c0084a61000310b010307a4880001d448040d02c070a440001030807840f08510b41e80c00a241821411f50030702000c0103004801d41c26460384100d4010610341003140042c041c14500c00400001c08040507580e100007900c07145960407141c03054000343d07000280507000c00c103850b204840090152501007aa5079030980c0301e801c0503040c004420750100400ca041c0e2118402c0c20080e0600f5115509549040820055a4005410f10001142c42c0b1024041e07070a80002c04184001902d05040d074034a4402c5504a0b00a035442c15040005402e24500065405880c1d00450042100307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 794328354 1250 794327104 794327179
    0x60c01090203160608070c2d0f0b19090201020a0611090a060801050a05041103012d030f02040c0f14030a150b0301060327110607150509010c02070303050d0e0c 70
    0x4100f1b05903101c030548903020f0102803041c45941000800805c80310541c50000791520201d00712a1a80c00b109060f070507088030381c2007900092200c405079144090f0564401000300f84003450312580002c0d140e10400300e00a0072141c0781c40f603c17084400c01c0380903941142000f41801807156600c4500905000382071241c107006802c01c58012403030381080d02911101c1c0d20740d004414078503441c09884054825040c0d80030100210002248131440004400f04801107002e01c2601c1d9400da00f5004020031150146422000e001c1c0c0c8800b90b00003240c115201c520510300700b4403400c0d140c2d5a40310003140540075590125410b10b004100110f60481a0b00245051300c540f95010040341c28010800d02601101c603660104101c01d0010800001d007100c4002c480c06c00c001790031542820000e541d000290300b04106216110341d1aa810440e003110244540c4201d0340f803e10080c0499440c5840c050400e125694000ba80d0326103482200c0680c00040099045c0110041e0420f41401541c152204005c4800204030542034007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 794329604 1250 794328354 794328361
    0xa02040b061314030f030a03050601020d17180f070e0417030403090b070602120a050a0e01060f05011206170d120c05030c070302210d06050d030e060c01090203160608 73
    0x1c01409403244001d40a0002100504281c1d6140ca075110380c40c400b03a40340c443c149100300f040c0818000b80103558699100810036007000c60002e421700c5025821201001400140645544a90541d003074214158607041e030840c5100d81001424078070030700c1200541340708102e800107542d00284a4984200e014510b00c0003459582481c545c104d200c1520302500103100d11509100844ac800010000d40e88900c000514200c03420310030041e445802c8a0000c10300313a807001000050f03100d0340544501c00a110000700076135801c0100c1d5010260f03590103000e0400480d0104900340401583c010f0001e0120f144c041602d4008007242c0c103681e941c00340b070301d80d000400c401114130380c1100710300981110011a441d07075419656a580c021642381c10401050b03003180300342e480080001c0b000440c03d9201c203480780036140c0d950700c03100030341011f0b030715640e106900915950180e0000719501030035030034001c002103a49a0742d5901a103101d50140003141400395150080c258030604000c515400c18044640c60341b10000d1556 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 794330854 1250 794329604 794329609
    0x16080603011b08090703050a080406030b030f061317070c0501120b01080c030408070c09060f140a060c02060c06070e041a0f04050703060905040501020a020c030d09030206030a110c0a02040b 83
    0x400203080c400306442540d0b42c4041d2180111a2150b104d000c01007266030180e07583e00d0385880c003003000301d045d51a1540010280481645800303800030107030041d00140480034608800760b643e803d0082c800c820242c8900020000c001011000c5071143c414116402e880300924141021030049600c80d0a010401d0407102c4902c1529900a0071907010050b140d1541c1a59003840441c0355600003070045031100301c10010300c00041c64071880f0358050a0200d40c0060014148080c0140c40702540d0050071690368500c1140c170b07550340c44446d01c01c00e803405490954543c400901c081000790041b017009242a0154008000040390706c1503100031000400c135010702c1008100c3c0801514030103d1900c8542000c0c900c0943c454509154201030780000c00c500e0700140850342c81c0040c034200c400c162801c42d0301d81d4000680410441d03040000413010381040300500030400700518060010305592000034041c032740120024201d04100d9100b1508203000245003580c80014950b2941c8580341d4820483c0f04514100b030304002130 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 794332104 1250 794330854 794330861
    0x606090906010e06010e040c08010e0109090b06131407081909050615060c0a0b06031203092e2c030414010305150d0f03081b0726031608060301 63
    0x81811401510705079007414420300790034000500b82414020420480304050f240d921419034030f0301d00780e50388254550510100480102c0e060340802002420550b4013004036205e56030303440e004601101d50150307291011030180d000c0c0610104004401c222340d010066115004036039540f140e068800d03581d4007132131140c0c9404120740c0901e10242266001d88001821050f0728050040980d0000740041d0030002031002e000d142c440047e5040b00c408003000c06120042c24108019145081c9101c0114114a8041c9a107a51552044540210002c1c00400a582051001064079000541d40d03003d1041c3e015403002c2560070440c4590b1804901007035a40b1208400e0003000780c4080d00d180c207007149007104d00800110043c0502a100080985010701403985950f200351001303ea40d172107500720012044144c1000307841164024a024203c40060645904400c021800c542602e50300510350140305040440203080e6000b0400e02c0d5202c2d4034000180704000018210341d01c000e20842d034600105544540a2600780e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 794333354 1250 794332104 794332111
    0x30f0106180b0d0c03060c0c05030307050c011a0d120306030501020a030204031b15050702031c080412090b07060e03130f080d0203120f0603190c0608180a03120e030714060609 77
    0x4c662948005100081e01600310380d4501e0301c1031825207041003013501c402c0e0459005440d6903010840014406908180a0081c1c45030100c04001311041c10002902240907401802e100610000749041c00c4062540030f6404040510307000307002103498840b4040f004c0d00a512600094420503d000c1400c0484e102c10710032141a961609031b041c00c00c10504600b6990303500038001c03c80c0e0500503003001e480d10040f00445020111065600da07015414035043c030900c41640b00b05100e0410a60308402e00c1603045403000c851240798042c0c03000690705254200c03170f4218000c001169001005c030070000140c1000102107035082d988044182c1d0440003d00390f06076541d20410704055040c3e0b46100005440c80d00303000d00326501c481c01805407500380c3c1c0b0700701c01682c030803003140c004484140380360a040c001560700c0b030580d580c4101c0920318545d0300c60240b01020358a00e070640c4020b0400a01144280c00300c0d805411007800d03040d000b400c0769140c1d880b610301044441410010b00b2568802e0200203401e034601014031500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 794334604 1250 794333354 794333363
    0x3120403121103071211030d050a02031f080d0c0804030b0f011e050a1202010203120a15060314040b06040b0a0e010825030b070e090a02030609060f011d030f0106180b0d 74
    0x2c90003117000b42c0d4a240c80e141d51500301c3c001030201e01a004140e02030144150850a00141d81c1e14003034810122800000460001c4507845070001d1000910004a41401c04003500300381089400314135280c0302922a9400060481040300107000308503010120483c180d0304100d481d100d10324484c020426404a0520881d0746c482051807082040d07000c3c1410785c0800324010310540f445d0686030303003001c00042d9081d00e1200e401c44d507488001e030060b5451000c01c4007405d0700b0300c0c0c00c1c0b044a40d081300c00e105002001c1c01c00b40610920602064880d40c07168440940b820011f414403064503592560500c50900901c85c8003002d002c1c1c2c82010440040340c0d0141d2590107060350051001e1030554a980d01400d0004209a0910446400e21180ca503034003501300c0e01c50355914401603543e00d400c1e4107020008002a02050040c0c80860403c080e90382c0182e6000c0485144c104100304114000700000c0c5000c140c06d0300f0300b00715440e000d40420710000340345143e07540b0b40d1800c805005049a0409024040803400300282 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 794335854 1250 794334604 794334623
    0x5191b110622080408030309070f0515040501030f0f060602010e0114040c060c1104020d09020123091c0209070503070207060c02090c0a2601050a0b0c0a0f020312040312110307 77
    0x10b4900a030000700c4245074080d5101c40e0400791554006840c0d82d1060b00c80c58020391100070700b044902070b00b45c80303d809000d0586089900d6541c085102000d80070710300510b414035407140019001d030308480c0d002e80500780f0b10304818024250346a41c042d000b0015465082119424034a64441c445205042d040c040c076448140c1626507460300c40200d03420307461003408030b40c600042141e80440b603895001510701d0701c00143c000250220320348000342040101c01d8007040e0902c0800510700c038000144040e5582c0a030250b440d00c10030310b05002201080c07003078408000c0d4040d10030428001c0d5142c4c2b00c0d01441c41550701d9000c42e1145a21200e058540c160340000c025840300d04071000491066841c4060201c40020b418403242c400340b10a00038030703a00c551410720744022207524010015031a20743c16403001803502d001e50514012010700110b85070030400c40c01911414491100404640702003007025041c5400140c0540c9403901c0f45090380130f60706041c80c0f03000024444007109018000200899064940c02000c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 794337104 1250 794335854 794335891
    0x2010e011104300b091e030a0306080c030706050d11070804080601050a1a130b0a0c050c0103020a0203070624031202010f0b10110c0a0b040e090c010c0605191b1106 72
    0x195144100280700ca00e45d030080091280079445140c03c0380c08420190005961506c0002400501f1144207910100265101d00c2c00203895403004034008041d1001c07860300311790b10512661130340003802d0100a0b03070384c060303070001303020014401300c01d02400c1610521001e446050b66900c5c204800801c3c01d0060700c1440e0613171031684010101007402084980c0401a01e1804180c0c0e810404099800c0b1050003c003091310300c11307036104001090204400802c0c09003421070402000d810003c4d600e0107521070050203d0f548000c92840c2210022a050601008010240846413240303410420b0345440c51080c0055070803e2812280780c403503030040944628000c0e0000604085504049400b09450004900d20740504403217030010703459040d0750704041c0545054041d606d61402e020110814030081200183e90007110a410070344c5c0c6d00400b2040d089030454804580c540700d40d01d02c0c2c516205c03403c0c0d00400003840c185092005e1b0003080000c10040086441303041500702d01515081d1074078011034a861490703240f80180c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 794338354 1250 794337104 794337113
    0x252109030807081b0409090b0f281113060305060103050606070b0703060b0c0a0219030f142a0f010915260703062105060f0702010e01110430 62
    0x2059019003200750050b1408640184c21115900039084841c1e01c03a100d0110800f40b00c1c45101482c1c1010252204510901d4079008418940544040504031824000031002c10050035800010704e00c0e00d1881d116983d61008005503543c00d005100309000309041c500007a11a601900c1111301c1583c0c003600c501e00e4507901c0d0ba510105090020561414103035240780204001c4040d41c042c200c036500c504024a4071050500400c040480c1d55128400d200403c0c01040c0001040c3c200ca9415103580004503091070405800716a04103500342680d022103400d101e01e04041043e444030380d80f4000b941510801c03100c2d141100110303200c90050140c80103c201a451811a0707510410000540c5540c000781d40d0303080b1500f04c03450300000109444103c0000d4540400307201980c09407007200c0c08041c41c003c07010024800380d9519612210001d0190036400c00210018030598000c1d04074030500d5030800d00800c6070640c0358a540c1c0c095000743c0540b140140f81072007a03240740328481d152042144801421480c41a0082d0307103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 794339604 1250 794338354 794338367
    0xe0c0a0b071505070905242512090503211602031f02070b011e0510090e0906180307030e240a031505010e0604120611070302010204091103011409252109030807 70
    0x4080343e00088802a20020410410b85500140f102e44d880100ac0c2c0d00d40001c05142c841d0072203900c0c1210014010100d468049002141c0c40c4031103000d920440703c043d60001074180200c0302100340c240c0b0b605211f60041c2101680c014003195100e00403000042e6220100c03900e4420320300d9103060f980c0780004001d00680c40c0c4042c812000010924040d1002e580b1a000030f5031103101691004032540c448010311200c065180c59100c40c0385455802942400401d0301c00500c1c032000d03178965034051501c81c003004240e9800f4290203005550303074034800d507511044100002c00900c010200b50405003e035020110b4150710a41c140c030007001004002a082c08e080441e0201006200d69084078680e0769a40101001c4602ca40075144250080d00016201c1d80b40c050301d4010342d050a031800d0051344040006008520307801c0b085881c1108261140850356481c0c161250407a02c0345408198a2506030b94501c5031300b58044807002c3c600b4203220300f00c003000c21040104415541c811000501280500b40010300c454801c91 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 794340854 1250 794339604 794339647
    0x3070609050f0a061a01030c0914031216060b0108011d0901091a0f0609010302090708072a021f090b031306050c0901030e0c0a0b07150507090524 64
    0x8041c2d0751007400200702e0034600040740d0b504881e21510349590322541050785003000c1c81c680c0203081c01d00c2100d2a540b00101140b105024034a008682117160075403e07141005058074414a03c0c1509654140812041040030711075030003280c1e2a800e01c610242c1551180710414102c8094111603043c40c40c00119000300041e00418003007041d961070030388c080460403740707444032030040084005d015800c200c034000154400c000d000b80c0c050075070300300108011707205c011002d544112207107000748041d121180e0454441e21002008401038800c10b05030f0702001c0401c8a0000d000d8822107184088911406810100c00c00c0c1d1400c0e407000c40c0000e0820000d041c9140025070303105101103400907038451140c0da0001210400da4050300d2401010658500c9541c0600c508410310305104c00501e0500102000166610160b00810300318031310109541c2c080008980c0c0c503125440c611074080c00030740b0382184002c001088501c00c1c64440e601d01c2d42c486050035004851901000500d0840a2406000d004c40181070604207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 794342104 1250 794340854 794340863
    0xd0903020a051501030c09061a090303090a08010b040c0c05030301060c1a070306090605010e0a061404030803041118090616140d060603060503070617040f05031602030d0e0303070609 80
    0x4020780000440034080d074030102400e00102c01d015411401c0000ca08141c40c0c1001a01031301c4d1400a002c5400040031100910b5084000c82d6668000c0c03401290650180c0b481268004c0c0791242c010440900640140c0ca650500b51407c04c40c3c080b0031003049540d48210400034011307420401c0140601032081e451500a20300600d00028040317401d40b10481c0f0148105c582c11700180d581d107424882d400175402aa40141400d02c3c029a68134040c10001c0c0b110742040c4200410302c25100c0200809014400544000b103030004807082c1c40b45041d060807242d0021150001d403250b00001103403543d02c0d012804040c01042050010f1041c0c2e903401c8800304614801d08860024468414194921004600020414491000c10100e440341c42c0030405022b44442e0f41140c0d03c00c1c0c126070000e0181a074055110b201c0340d00c584c034904559840d80e051030741d41407070000300140080c000002d2030701c04203900c1c0cae048081c02d501c00ea08031062101942000c40700c02c00014a8260305400801544011900c5a000084840d024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 794343354 1250 794342104 794342113
    0x40206130b070b01050925081f030503030928120203070c030f05100c021005150603010f0612060e0115030f0515011106070503061e03150a0c0905060d090302 69
    0x759102280340303411407507086480840c040d0060249013003d10103281c101950b40c1d075660081e60010040225004103030f800604011000e4000f5100c40c82080100c4090509842e044030b283d5100d0818545aa008542225080c407c1000301483c1d40600c1c0a07462651404440c426049511a50380070a00030b5603884440440c4800c1c8103c0340812907070b107416001180f140940b00343e40a09440d040e81080540300b8100c1d0091714148030035200c2600401c202e003000a102c800090b9540da40d424150b00d004c810100d194000c00c1c040b001180c031022450251090f04c055454507001001a00c0004c0180d45c03907805a0a00790300380e54010068011048141d4502c80c1e09428042406240358030264203d600442d40442000f10300d0120086c507580100b160342400c410440601030ba46440c180141062201400050007441c001c01561805540da1401c0c1030001c0d4014213075038101c1c00514801c41e6100096407450f407050301d00010700c44000e001d00107002c2150805000c0b58100036840018100908030680144d056004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 794344604 1250 794343354 794343359
    0x61e0308072a0e070201141303050c2508010207030c03030906180b16050403020d140a170a0e060307140c0f0123070804050303060d0809190e1b0304020613 68
    0x481003016010788079000b050220380d5180040e4203100304000b0300100296403400d112003c1030640c0300c1070580e00804400038a001111145030480340da00c50a43c80d2080c50140b468807171401600344d824100002004014070031415104d88007130b0f00300d110380074005000c9500e1881c901c00090098010440741d9004400010300c000080c016849642c1d511141100c03100240400c01000303e0800c070004103003680318500725080606560101d1a901c64a08014041c03140c0910500c4c2c0042c020024500300075030000324403070b61000c1c2d0340c011340b81500071051200102e8400c910340c1c1207e00f00842034030703c10b100d103075194017246806402e0b031941540038400700c8086014078010340720703000d6090040c06200203a2503125a409840e8228540048002411080800c0500418407001c20000000d59811020454001c91168151f00d0418812f2140f559619080341003c09061000c1110482d0300342202c21803400f92241d40d40b110708000c40001444070b8804ca1040c20300100e070250620300058031514280200d060001e54 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 794345854 1250 794344604 794344643
    0xd051e0f0c07030510060305070e0a02090a030b09150702030909060a0b0412111207030305220b1e0a270e0f150319020405041106031603061e030807 65
    0xa01c0900700310150703071200008104103d000c0102840c10861080c1c100036840c11540c44a4a9190714483c0d460b0700151072000c918084101da040360010000201031103109681c80c03410003450796044038900d0359402405040d1002004060043e403040d00c0c240d0295141130308000070855245000741c07840d0340040c2c0c45c03407005c42d000c2c10f00b00042004d801c402036610040020340c41c051403400400c4e5a00360007094039423850340f0406070006200b015654141030903a00e400003d00900d4000d4204540307074004e0f45a001d40000c00030441c1c4020200081703500c2d003d01244032490340c5494280700d07a11042c40007030501d030140400f41190108489507507204810300030510765121150f400d9024140c0d013805c1c0d40e098400901ca42042608000844040150040e007140e101444801c5005440000007900480d04d0310001400c0000504420842c4440201800d0b203a050030034491800d0343c01d1141c2c4502081c80e1031004220030913082d103044810402907000102203803d40e542c071810343e080b40d50120342d41500b000c4002c8021 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 794347104 1250 794345854 794345857
    0x50a0c0f0c050c091e060a0e07140712051801090303080106201b01020d0206040b130f02040c1206050d0c06110f1002250c030b06150d0504020a080d051e0f 68
    0xf944171a4845040b00e1040c4100c2241004c0580240e00c03031011101b081040d000501029a402491030400003001c07442d00b400384410703102e10f68006100c0d01051002d21001500701000d440414007100101803039a1140c001134803c200316001c083c0106044c00010400c1d188901c402920240c4075150070010700f4042018540740180c1216010100100c48a607010343e568100529400d5411910050a00781030a4a0340d440b5400c0180c021440085414110400e0242c1c00036441d440310380c050410040c103940c03030303100a040700850384080c11914107020b00010240303407090420410076040b045442e00c0b07a240000a550009440381c0490341d9015900d00540c2c51481440500303c007401c284030150390f9a0740b800600c030b20201c00628103003901c449541300e20007080ad001400b038140c030750082ca1080c82e6107503100014010031075158204104007000510036510b080b681c000078000d510036500506050345a43c100798603628503420200000e1402e1201155203168207007070fa03d541c01800c00c2e81c2c0c80c2507000c804500e01ca = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 794348354 1250 794347104 794347111
    0x180605130503040906080c190e070504051e010e0f03061609050306010b0306130c020309041d030d14060603091203070c02090903070c27092307030501050a0c0f0c050c09 74
    0xc140c0d120300c100030000b018000c048200c04103d238030303e02000c1040020044c034401401030300e0408002000040c400e0340104101c90203068014280b402e0b05006014000d54143d0344000d05000605100408900b0705040d42c50070034009000300900069500d00f4208040c01b034001d07800c10304001c10354a000516071404c0c0469400b0f042d0402107956245016001e014120210070003100f030b51071074107404040c607560100030344490a0781100d020a81700c1c0d40c10040c0041c1556030401c002540000110903044222035442902007602e0b0080e554080e40c0c5220812036140021a90519240c000d90010070340740f003ea10007545e1101c06400d080c008a20f0a8010500c1a90202d071302e000b10340e000003030300000d01c00c00c5001c050003818907000ca0091000030040c4c202e034100c000d0072054140d98689070754004204031171402c00c1d0303890601080040308076402c0882941d101d1107071201b070390035502c0c2c00040748d0850b22a008141030305100313885105001c9081002115520a42903099801d030180c0040e4580355650074036010300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 794349604 1250 794348354 794348369
    0x5030d1e1d0a0b190e060a0c080402181e01090903030f0603111c050307030807230904021e0726041a2107050406033b0a080a090306050a18060513050304 67
    0x64a07d480700680f0111841c40351407506002d9a1001c1000503550480d81d506400001c0d1441041900c07038461104040070266803441100001800228050b1160b0b401816041c0c0203a4042c400c1c00c0c0341000c00070841d01c0300d0002505410081d200c03400942003161002c80c2070725100761103400d19a565254282036400101c0100e001034041c409014400742d1008400503032910072003200600d00201c1c81038a0b840d00c2400040d80c002d640202e044038920110034000c101603404160126a280c405107820012124130b00c2081c1c58000402140202c44140b0005a90a9514040c80d050f5039a440349218500d07a040b20300d15041c1e142c0c543c0c2c040f43c00c0a1100c00c0c41800b564103500c80e503440c1c500300a009003d4031501400d02c00c442031014040c420b240814515403003191525845003410103d1031250310b003003941c0c18a0107031024500180b01e12502c0c0d4800540c0045038000c1000708455114081800140d503494400304000a0401d00880b003c507185502c21a00403140405442c810201d03540e4050643d04560321904 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 794350854 1250 794349604 794349613
    0xf0b1305040c0506071b03030f120e061b04030501060305030901021204060206060f2d0906060901080a02031b04060521060d1202070515030426031305030d1e1d0a0b190e 74
    0x41c5007a02b090415011100e1a0410703c08188150b11660395030b00c0003041011484131180403107040a07291001c49024581100081c0a800e8a170b04149540e07601c104503250052144016040100b01c0d001c0a03181564119809841d15131039040c10000400f195000d00c80d4852801803040e604d0f181e0741e01d04602001c060382103101d854045e06c0304002e400e440060045000b0541003100135100c1e81d100c4005944610f28500060f181e0300c80e0321003000c03031243c0c90040c0e01c2182d50009012a2180c1c0083c00b41c903140b0303a100e901c0c28501c4c5440d04266110101943d515800007083c0b1800b00010f5481d209401c201c034250b20480340440e6454000949191400c000d5640c1000000184001e110341801d0444403010518a00441e45403142c14001c9a4030004005012000c2c11105000c00c1010034411038100344d0400b08280701246e0b0014081644000d01800c446c4024074007801600c40c1c10001643c0d01d640030580029108491a48c2c0b03401d91001030007040311103000c2284880303d0348151240700b64203070109980010b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 794352104 1250 794350854 794350877
    0xb04060f0f09060606030e1905120418150b07030309030216090b040b060a14070c0e0f090f0601030203120a02070f030803220b0106030903120f0b1305040c0506071b0303 74
    0x1c42e00313240c00910030942450b1040060f03480014480c0c02d151100c00c1140c02044030383c10602d00b030034294142c00584400018000842d501c1e010342034501d0702d42e0701c4d00801c0071440091003081c2a0410348184003140200740b1510020038000da00010005010307005407a10301c9a84d0500e16000768081c1c100803046684da4250341300d223040c01e200c1ca1541403016580c003480d0500000300680540ba4050940a00c0c2000084030010080c5145082c0000c080b6a58904124180b0000c1030351507110440d6101014400e941c00d5202200e030003c0d00381e04072500540940107180180021410503401200c80c0f40941c840d50704006140d141000001000b1405445550b86030305003464201c09800d42602c280c00e40d06010403d11001c20034103a00281145c0c414200040c0300c00d203518059810311602444410b819181440e0114100c5c0306030880800134004840542c442000d502d2200c0843e50281d60180c64040c000e0018000343c02d0000c005c0c1851401040182446040050750164810aa03001200080c1400015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 794353354 1250 794352104 794352113
    0x30e042309010c0509090c0a18061205130b04020906040902120115170c0405150414010806010605070f12090f15140f0306100905300c0108040b04060f0f09 68
    0x3d00c041c200b040e10b0320510300201440010034104014011000032680002c0e007d014602904a58036600714580c404103200380e072184040e04450301c0c104007840c1503051100040c074515040080042c1d80b80d2003944690203450b50703000d0142c41c0b0300080115401a903940314180c0540d0710b8000d0400c0c0d0988002c0081a280220000580081d92641c0064000800e08101c0c20600c0c00101e044008843c0594001545540d90000b42494a41800036a0b030428a49404182e0b250394040e0720701c1c140c0c4c09080450301d6030f03681c0305411107440c811050007908001c61030040b000003c010216078481c11610b8984604881c0c0c58030004043c80201c0e5124007200314034080318280320754016180c524001060300300c441c01c00e0074560803140d091100030700241c8110012042c00c0c030810b024041800103000c01a19107885d02c3c81021598061f0302c0760b403041101d0300410729003801000c0c40000e500c810042040c0c4d15a103154446a5441003c910040d20448240c4d46031b11405041006c240f1a01114440d6504040f0300401d56050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 794354604 1250 794353354 794353361
    0x10216060f1a0a151209060b2d092703210115120603210806311404030c140a0c050105090a031203091a090a030e04230901 54
    0x5032548034100b0144100b42940c62800c03076012600f0324080340d0803500c41003034121100c082a00c8a1802240b90452031010701034142e008030321000090b201c03443e0300e030122245240d0402c50141c650241d0f406180313041034070341850300d02c842d04082042100d049004241051489030b010741e154031011035101281380c26001039228141d018503085110079036555410032000c0340141c070410b0340e101c0911001c102140b04a5066620035401180c00180c60b0048510240c15102070940400383c5c000014a010049401c514003c58a03409440300c91000c15444c80405032880040d00340d403058068010381d240d401c4014008100000c600c658407c1da070340c0700c0448a600d4508800300d914084111141d201e48030000018100031a50700030380f482424400d0300c410745400058500384980d0001050800b04503002480c01d6095040001c000344500c9004200385001c00c640c10500c4012142c140c4180d00610444012074007a900880d442c00d005840032543c0100c0384100d036800d13108a041014960001d42c10400500802e00c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 794355854 1250 794354604 794354621
    0x3010e040c0e01030809010c0317040b070e01020c030705040510030804090f11030910150f030b0f01050102030c0304060503060a0321080c04120209072604050c090103020102060a0905010216060f 85
    0x40702d00950b94116281c0003400c0c0584c00c021341c18050704003501800d0601030340d12084800d60003203034514940b8184c0f41c681030004043d2079040100f40300c4081c00c4030941c0007050f44821004060014544c862a04d030811020b0200030707204081c0700440c003102001158515008102420b04001d020882418001012045400d84040600603440038024000031034070104046000d540010ba02040c00801080440b40942e142d0340407600c03000100e0300000030044040600c0d440f0700440c0001c42e4041c1e1b600e030010381c1c581c420300708240701c180c2042005000d102c1c060000f03113130480c030058a1060340c2c035104e0703a900c45800620300401c015100c5a00400540981c80100c59500080d95207405003003e04d400c40d012200d851200c0000c1c4031b100c40d00e00084c1d41c4d0344150042440b0308070400c02d84a4030200c10705000044002901c00b55510f028003041c4a01c64241040064122a41a8020000c0d03554030380304103004040120b0202c4203550208600030040d0802d98501c4040c60140500191052406003810f04480114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 794357104 1250 794355854 794355869
    0x30d020c1b0d02090601020c040f0b150405010c030807020705040f0e01050c0f040b09060708040609182c0a061118040b010c0b0c0405030105040b1e010f06030b120303010e040c 77
    0x14040c1e05240d2a0780001c41c50b0b441c1c0c1500c0900b040e4445400503820050340c1d401a82e0810700d00f840304081640b05030488042c1d403406a81c4c0000484101c245405d41e4401c900660740483c1807440440c000902c11408154800034500c103848041d921540001e05640584d4501a012500c40f084808078510030701c0303240c0c0c11442001120380b0385151a980c1c240c0b203028501c5074903400b07030020074075400035110002200c109030342c0301e1f01c02603a940d1101d4000e004814940a141c1c061921703160006400d01d240d11502e060f0400903c681d00f034030002c03082c03051500710f0b80c202e07181581d0060500104c0010301c01e020b603800f8850010384413901c40f0f55030b5140343d9804004d403110900c07450078801e400406981000310f00307801c1d64000c4890101da030348420003c035a900c907035400b841d0598a000c04120030b1000c03400031749000d10442e01c1c40d5400c00381c0c000d684c02c65082c0700780600c1e141c11444500420019009038010324510801400055080d641c0c00001c0341160400da2107050800502070070007007000041e028039005040ca8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 794358354 1250 794357104 794357143
    0x6060611060601120e0102090a0e1009021201050d02190602060601020d0c0803060904240204030b070c0302281406011e0803040504020318100b191a1b030d020c 70
    0x80400241022403031080b0281880d5284103012210305d0a404503031083c80041c0004401959419440f001c0b038808444404003004c3e031080104d00c00416000711464036005c422030107440d9082104005d950740142c00c080380c2c858031600340c2140c1085031342c07000c1c1c00804440c0c0280c085841c0010019080c000e003803110a04101c0c1c1c030491180050626003d582d0054000e9030078402039a0b8078503245080380c1460010300c1480012506900030500c080d00100141d1748905001c11140d1990441a281c40040c140014050b070044481e000340d00b28101c0d46800005403420700b503101d544041e101c02281e1200d04000b011580c2014005002d540031404140000f43d804201e007800761481c00d06001c0e200c0c0503900401d40700c2c6400102051020400301000503000030307076a05458141d1000b0559600400c41d1090690140040f820040030150300083e6100c121407000c070141b0051424440c07a921190b020041c02485c40d88c002e862007018641c00c0000d0220000066001030351039100d481c40602e440340c7d01101c60b806104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 794359604 1250 794358354 794358361
    0xf0601080105010c0b0415090c0803190806030a030c03030b040e06160c050622021c0b0a02030106050708030c070b09150a110f1303020301150920070201200a0606061106 74
    0xc1e402c0c0d250b070107a008100110304003031070a04074019010388c00018201c100020b00104110002100a1885903418016403004002c0300c0c0040d110000c0480300a581070708107440d040302290082e000009160303c40d00d800101280e802001800b1074044c3c03540005e1581c1300c5002c02614101504441c0021105820916009407040da1096558103008141c007a140c0f110900c49299400000801c040e0640d00510f01c108003000d0702c41902c0c1c043c1c5003c006035030020040001c034400c90714610860b03041e03c01650324245400408d0316850740320790000d0406041e1040401c1504089400101494000c4e4101d0000e03040c41d05402501d0340d115a4040d1108040303a1820825581340560030040321034210213049416103c10282a095049400035800070307406500700118022040c907043c00342019181d1502c0101300f420006407004c00701407001c0204a550003010040b080166003c1c0201540b2040c03034204505440c0007051500c3e0030080c071480221051b94956406001b1240c01600d10300c04440800020805880c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 794360854 1250 794359604 794359613
    0x19020f04063e0727050703141308220e10140d1b08010b100201051b0f0f0d050406060501020a0213021e0708040515120a150e0f0601080105010c 63
    0x11514000c0c4000158107216081e03600406101003001030403412510340070112459100c4ca80b010205044030701c007915100005006d0713406841440a0441c1e0384140824554a1034504240d5501d8040190703021030007481001d00d03212a4110303041c0c1750004807a102d690603284c0014407100718001750011481d00040c4209000038419084202c030801c000b190b10701481865402c20710394021520110b001d044103810b001142601c1e05400030030303034498280e80054010422041c12402c0382c106503070301c1490304c00c0441c007401c201082d200035008000a50f0801e83c6031540c2c4c000000e64990220a03504055912001044244000c900c581c00c0240020b00203000026103d030300042c480da0312090001c803c2d0b94041451031204c0f00e09899502d04811044101c4d903150340500340320303195400c42e110b00d0f4481c03480011a051050781d104241c400c41a08000301007803035110100b80402520012501e0304860141903000280329040c2008180981a540f8420301142042400185900030507007200307040c400681035000005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 794362104 1250 794360854 794360927
    0x6090605070f020114120a0b010216080c090c160309030b0606070f0f150c110d050a0f030c0c0c180b060405101b08030c040f0f0302010509040519020f0406 68
    0x280d0928100100194103c10a05e15004144034000048030300d0082008090b0f03560f10040340460242c085400c0c06080804003107040605008150a070782288210304841d0424540054000b860003202605105140e809642500888401500001c105410030420b005520707049070303042a03054030b24501c2d140461b120030b0083d81170820010020285003508100b4402500d40600310b2240604081c0b0450007680d0000703200b811440380620140c052140903101150141e41103600300340460300e5481540340e410006400a0025003800401e10041010b144002a25020a14041c0040c481c0e184214102220070307008565034013805134007442080106200e04c1d03803010070707002c0c15600034603082d04903005076100d000b40e032250108020100c01c0048140710300c0069800203002519404610010855a6141d142035000c080d4400a4089501080b000456003001d0b000701d540420708040442003131031403034503802c101c0e07100e10600080c240003c41c0a0004550103400c24945010b0002d02031540b403413055110300c51 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 794363354 1250 794362104 794362133
    0x51608040305090103110c150a0b030706110102120a020c0c01031512060e0615030f0601050f0904060b0d0516080606060d1d03070507051807090b0a270609060507 71
    0x2c0c000c0118240c04582c0c800c1d0800112909242125520b81c190200c0055880c1020494101403843d440d0002e001911503104454a01078002d00500c0d0003071820b4419035002141001c0714000355002c2100202410b03544100b14020390f83d00400603980d03c2030201c52401c0000400100c2d040505000c44a4445240e80100300155410f1280c2601031080074a00b000080000902484450080c1010040d802001c03440010460310154160340b00b060208040a44486d004d010b00744d0b200c002c42125601034103154288070ba005104a000242d41002c15000580032400124101c900740d021032604600b00000041d51401422008020072a909041c40022403e020703c892103100141e848445080d50420780b0118400d0020b50000e40384d4412081c1020303511104280211800342551155000d0600c07640704640b40f00b600e0719550200f07518101001c5e110594050300f0040b08200c3c01034041003402c0030320780f548040002e01c802a20b40742840c0501c00f17001c1500c1a400902485014880c40010a4500f44c0c00c895 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 794364604 1250 794363354 794363357
    0x1806052a0726040306050408071e1e020d0f14010f020901090308180d030504050a0f08190c05060417160305070306090606180b0114030601020706140702100207090516080403 76
    0x4034180b0300085000c650003240c0c40074204600782010301060094460003000c02c00d000e41c805010030710b80c1c000c2c4020704035900362004004a0480484030320780d0102e5044034144038802800c5808212807900c6005110350b8448040d07031040328011203640410006d108444960044134800d45c11301d000d0b0310002e09401141d10010307114040014a104010712100c0401c100940001e00b012030340c22480c24010a40e4200d40a09030180c4480c43e40445c155403c120b404044620040c006c01654400760301a0107282c4803c0400c580e0740e1440c250101d181d41e071b2000076002905011410b004000d0060042c549004440700258402080c00541480400da020889000390b0303401c8107020030104018944800108141d42c08400950003290b035800000025402040001c502641c548d0311401402e02003200718407044e5215400b591040d181001841c0c0921401c03182e034600384c181e103030602407260003040c0440758402404005801120090001c02103a01c03401e40c0040300b04000751220703004194086c040010160001c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 794365854 1250 794364604 794364653
    0xb1008090c0d0c090204060804030908011118040b0a1814011409070e040207120315061e03090602070602130b04031a06030f010603060b010e09191806052a07 69
    0x40c10300000f101e60000034000640210356075555204020104401a2011800154030500006e5004014000d20908248460a40f0b280c000491200c00800348414407041c2c0158568140d001240d40e517010300340080c00c01003110030001200b008424102c4403101c1078105141c01180061045003040c1c45080c420800944e888000c43c1c0390160191780803145022a651300c42d000181400c1005413218116009168946052101004414500d412414140501d000045280000c01444032400b11500c0d0446105e00340011040e800d600c44505130723441000c1c1981c1c0180c00040c00d00c3d40b00920410030b001030107003c895600b0309056035550310307680781d003201e03c7e44d2007020031004035480703a42c103011060340010014000c11084c0d0f81c17480e00a001c0e2a66102e90381c0400d40d0952441c10038140700c0141e5100360a8040700000b50345500d4038450042403201445044803100c030a011000412502c2614021310172100d41001d459484403907021005920f0440042410b408c0c4003030350028020000c0f188a2110040005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 794367104 1250 794365854 794365879
    0x80913090c120f0f1101030e0316060c1202031017060702060c2a0f060a110412080f070c0906050d02030a06051519091a030601060e04090c06030b1008090c 68
    0x10010b100d00f051000c0e0500c00d4a801c61800c028842c565800c1e000c10a032400d00ca0180590f04d101d440303009a400c00d40c03215023044816800149254031190f00c01d04103085c201c80c1a010b4440e21012a0011a003040840394400c105000b440300c401c5010811450200092280b403401840c0207403509000307011b02c600c1d9900400c400c44098000d1031140c0c3e4001000c884103404450a46889580e20701001000c84540220b00200314010203d005040e1441035012500c0d10709031510b00818455141d000040e20511001d20a40742c1c4808550b0041c0170f5507000c0d103080f4100a0030810b0640446816074441807089101c44031241c01a00e022a020400b00e800c20000500c50307803020080d111098260828903807011800d51080c82080b4640c4a020a40c0c2c007541e401c202c042c240c404191880c0e0a0f0320031240e0700d43e1001004100462141111580d980b402900100e1016817a545880c05441c0a8001c02c011a40703e40c0c0801050901c801c0e10401d00c01c45180c00006030410303030400741c1c5400701142d13410b01800c2c0400300c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 794368354 1250 794367104 794367113
    0x305070308030a02090607060209010e01030c020a0209100819030f0f082214150c120130060c0320040b07030c0206030a09051c05040e15090103080913090c12 69
    0x40c2c60440384041e1540350351f5002d130724015000750300114940d80814050008800694802d03c540000711505070000e019640d82c0d9020409414030040840d1110030070b8001c04030b01c02d003060206905c200c07042c001e107441550b02d07440c01401c404038000755842000f299640f50000c00b9448070b40d0740d1f00b01d20710030881c40c0040e6400c1c0a51178882d1607000050700c007840b4051000340103180001d041644102e0880d1030045515400381d550440e1042e203d039083c2002d1920014024450000740c0c050082d22413a00c1840d086d6158a818802c10300146800c0d2001035803004804803154040c025107102105030380c15024a60111a001b1625014034000d40c01a06000714070074040600442e25200829001001e254481c90022202c102618a0440440f05401a41c6420161154079407000e4075800c0d03035480d00d904003814080c21981c00c20005224038501600e495062905071201251203018601034060030f691540c408051104107060828080f010a2514000b04003052844018105403441c004225150388890300b0f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 794369604 1250 794368354 794368357
    0x7030314090910090c020102030405150709030c0e011802031605090411040f030c0b120f041e05060709050a051305060103110d0903020c120a1b1502060117010203010305070308030a02 80
    0x903020742000b000c20038803003070841c00000d07a4203e5120603c03d120b2201d011304120309038082594001c00036800301c4044002070074030050080d80100d10345081200740e41e40342c070b030983c0c0e041940d030000460024150041c451820710800362451504200d6040d481d508000700502c001d10381102440040100c0451001e20316900c507040003801e07614900b20356840315113402504000e078504d88400c44640c0e01103a000115015860190303039002d030000022003015681e41143c5000310200410843d2492401d5403002101c032440741c0c17444030040c01040140498a80284080e0806009410040c4551480403040006035200c551511814007000b4021855403280e000680c09810755400011010b103020032110200e080c250701041e45140242e00700c0d04480c0e0140e041c0094118082c14080b966002000c00300c5c0450513032840641a031460925908049507141c19808803a8500c0d159040141c2002e0300410502060014892103051510002c614651441d51100e50307600311840300500c03103680440010b00d00340b059030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 794370854 1250 794369604 794369617
    0x3050306040903030f0f0e0f120d3801020f191113060b030f0f15040e1501090606020c0a08190c0504020a08010e0a0504050c040209030a0606030f1202030c07030314 72
    0x17014070459050f8100e140160041e08800040ea01c19031440c46c0a0000014441c171106803042c3d03403a80303000c04462200300601612a10041c0c803601d0701245c28008141c12044640d60729940300c495144504010009040092002c800d000c140d00c074110714408404860240940550300c1130120301419403407404140820240c0c6e040701010384c44d12100003030a0030900b00561140c02040400d0166546100010f00c0c10300d0251034202c07040200d2505200c0750700b019401801c40b003c2900071980b16075070f054200c901a00092f0401c061543d19001e04200d4070390100001168460b0449010040c1d6040801c0e035559202884a40564502c2004842051140310003a0344083e080c041c0055650740071510000c1e0880c4003e228003801c40361500001103020040c1d11906018540c0305003c1c3c03c0e291001c078100070285d00300402c80303503040c06103089440020b6058820440114411030344c12603440c40c1810a10550b11203004000c056400c10060180500320100b00d44054036450f0400c1000c000070089441c2e401e0150f02e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 794372104 1250 794370854 794370881
    0xc0903032a0218040b0f07050409091509050106061d130b011b03050414041404110a05040608060a360c0801020c0f07080708070b0d14070509030705010c0305030604090303 75
    0x141c10560f240300c07182450501c218043c0c0c10540050311000c80404e04145c1c12560040059000e000a20040140341c00902d02c0038003c0c00c0400c14804078020b80c0c0105c915290044650342c0d50f400041203404e4226220407045105a007039000110007036408030b500c10b01c43c0004002070555074021500140e0081e5001110701840c000014000c10440ca030242407603010703000c0e4003414001180204510b1030301c0d000312070102c00300001070101ca80302d03aa0b80c00300000e40c003a0016400303482000d010074030f80c031244a0000203040c0c09004000e2410044036002c1121300a10501c0400c0b000301c6c0c2110354031894403e65a40003041c0d400b079032001c0b500a0070480f0b11840c082d0400d2206500004445001e00c20000d05000610110402d4480c0f150f904c050700c0399210120b108651058000c01810021002018043c00100000e1040031650385000e4101021500c811915480441c1000c00d4445c4a8201040120043c2074282000300b20055035481c0948907000043c400c0740b2482d201d020340c5040501c0303900007244440c0103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 794373354 1250 794372104 794372119
    0x1e1003020f0405072d0e06090102030d050603030f28050c03030c030403020a06020301170f031c0e0705090f0106320c0a38060a03020d0309080d050301090c0903032a02 73
    0x1c01c6211702c408000c18400e000014903880300c50450b0320b05031084841080c01600291705d04194030f107001000d270034000c0000307525002c20700400d10025071080040c4403100400705000215420b40e4100e44141140100800400c54180414a0032640020481c2c0d0040811401242c40b07544500d070880c50000e203c2001081280084000100d0359100958011229500002e540613620500c404a40e6401158035558009038030b003502140341065544803000c08242c04003900c0c141c50711500400d00c1514142e0300d00131900740760401001003d030f01080ad41007091000d2165680301c014188901006043c100701146074000008030060f00d883d08115202ca041e43c040c440e104184482d1a090b6410140c0a1007100e61403050307017124000341d000da20070034441c500040c010587c06045400b0302c02244e0000f8022400d00c0100840400c040c4c4040010302c01d01d88103540d035a03030380c0c0d8181480c13107087da64502440024000c900000303000013504071405420301030031075003140c5223006180741040140c07800000c0a03410060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 794374604 1250 794373354 794373407
    0x308070c05360403050301121e0804061101021c020d020910090815010e0f07050d05090a110f0d140a0c090509010605013209091e1003020f040507 64
    0x1444000c41034601001d80d08540740a10903400c0803030b02e104440041c00214200018030100d05021040c411280c0180e410034200003a41c14030200c0c0d114204c0c0300743d840c00c4010404120155001b111546030102060096041100c0000405c074442c0f2400300d003807030640c0c011825000303408065058400701103000749406412090f42401400040c014000c0300154012021403241400a01c0702c00c1d030407902e090074959120307a6281031801d116003024144504014003000092141d000c01e0141c180170341000005044882e041c0c1c03400300e41e0302204a081c80e0103a281307600c0200c22940d450244000700c40d04109007540078958014294285913141d900204410601900802d6002c5a40c2c00306102e0001c02c002000500e0b186c400540fa003070824401c00340807002900d08901a5284024880704c142c000d030f5165414000350301d00140141d0780842c0c0c070300a000410765010805000d0340c141c240c0c10540652058819500b541c02003200746900c1c110942c041d5494202140c03209110b01da143d000c3d400b100240341e12046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 794375854 1250 794374604 794374639
    0x90c140a09050312070809040207021c350315220605090109090c03030f030906050c09010206010f080304090e0a17070c0b03070c062406020d08010b040501090308070c05 74
    0x7180078950191040240d590f030b41e481c2c0384084070755494120980da401d14042c0000c10029501611040760440c1d4980c01c1c1120f81c110544000720f010303104001044501ca0f804000310143c83c04010410240c540b42220003d1014580c001c894010104600c40b100c1c0d808921301041c03d028000e0080c2803102070300d00c165242c04c030180d0320000a03118104e0f1030141c96661908061309649540c040030308244100c54040000a01a200c19484501107080204162807151a070000715807040311070040860001480580c25070341401042d000d000459107015860f410481e52aa0341e008034000d6481d0703203659000e0070040100401c004030000303a019110b80c0c44100c109054910b40e4001d11821248454071302d4020902440d03c0c0143c81c82420703103a0b11088800311503147c8502070075140b010030424499201c17245c04021070003425903014202a4004200220f400500100007800582c81401c04100902050007a40e0f801420981180e8005503003944070b102c2170401224079035040e48080d03071000900100304900b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 794377104 1250 794375854 794375867
    0x30f020717070e0105030a2f090a0204051801083a02070f06140f1b0a081b0111040504110f07050c01080c18060d09082a03070c090c140a 60
    0x250200c06070075542e40d1366841816903c80b9203480c0107104803291000c4d05448c444201c51030302454248039079000c600f0445004141003203001e8900070411900000c0610007810101245002050711804011a07985810307691500c5601d044069501d80c600004241703d000b01d00181c1285604850a000b140d0541d07045020f5968003452140072064400a1000106907005801e00510400c9000c400c1c1e151200c500b010b01900d5120700401d0100600100c45800c02c10010044084d540c4d01c100c50041d030360a0846030030918001c249180b190b040e03045c00f40c00203c02c0322041c03d480490f1410b403404100c10004116103445405000c00741e6412031008105041803090000d604503501200ba25041307000e071116002c0b609107118030003e40e00ca10280500098090824000908150342d11140020b01c554041d5624140c80e03000c40d00406034903040c140115405004a046150b0f20b5040d41c004615119482d60b848401e480d892141041e001d035100c8a0400b5180a44c040c20340c409401007145980d040c1a441c0034094 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 794378354 1250 794377104 794377109
    0xd0c0806010609120804060c0c180b01090f030525030209070504061e020606010f0e101d0d030206040311161e05011431180e1207030f02071707 63
    0x1264200005000481884d203900440d410044051515047c1041680d42038021007041302c05020a07100015680d4401d60b4440d0b80002882c1d006c60300c82c1c0144001041c140c401d4104540c10a0700c04410000118000b4107007078040c80e0714141440d804010345e01c60080d44019440690010214000c021105a0201c018819100562035030b0a40b106811840e0580008561601c0003507801030011400750740c01040044000102c61030900085480e48020840d40400c600040000c00c404003000803d0013000c0110220400c81595000000c00803600c0c001e54900001c1c0014051111090504c0c51510060002c4810707800400103206045a5030410480103480746c40140b202e00c4a11500821958841c600010040300210001c03410b102d50320485043e44848900001045500090807032481000c2101c0080100400044c02c1003150800901606543d462280d1038240c0d0042e23204556509150b80c142e852040d01440d19800403000070000368034011840d0044811582101940c071a040c0002444505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 794379604 1250 794378354 794378357
    0x70305090123060d06020a0e010311031003140c0a0b0706051602210d18030206011a1e07060e01051f08070b031b0a0306050a1409040209060d0c08060106 67
    0x180c0da4104080d00b200c02c058207901c03101e00c00c100600391040d025000650000740c0240540e000401541c1c6801c200d81c0440c40d001c01081401004002540c4c16110300c0350f0301c5100c180a140355161000070b61501880701c0c0001082ca6043c011a00ca800c1420404048980c4018203603202194075042e40002981040804541c1d007800d010008a4000c091400315080c1c000c0d603001403981002c1c028402c44601c9110ba03601c13100e86000d000e0980000b48a0040f02480760754920108051082414000e0038414140c1102d5510722041c00c100f00f03103c5841045510f11070302400c02a43d0550410500c9406215039003000d0f120301c3c2011b8420301ca003113040d845240030f4060145c0c00c8130b0295a8aa06504e0551580306418150b000390104000011400c8011503000a14500020910320041032201840c0c100c04144400256508014486400c0403401a0068070101c05108810311130390340018010f40c4000d01c024010308085000c1001074980b11200300d4010f40c0301100d240700b107488070b514583c4c3e110248603180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 794380854 1250 794379604 794379611
    0x2b02040e04060b0f03150604180b06101706010f0903051b040c0e0108040b090c06070507080d0c051b03161707052b110a230604060e0d080906030403080703 68
    0x80003807420300d070b07113a62071134014026050103910001c20740c404003c01031440b0740041d2100d4203ca08166522000840d440c4a82d026550328180f00c814040000381d511005410300c002c80c4c0f5100c00640c020042c103039005409280103180a643c81c0c60855000c803082e40010601d100d820b00300c03109a000c6a0f0031800c046000c3d10100070b69035190000303c4010000300050f5001c1200075000c00c010032281507860754040303240000c0300c60940144020030103944c030000d8107035810b800c08001441914014030110690010340d01d0403450080301500c0e0b160f21100f07010380d072214a000852140300b103614203204455400f81241c000d400d03600c1e95078445e02d40d540c0c845191070005010741c94002c21301d1b00d8403400f03031a580b02d500f40c11070807004000000c811030096101e405441c0740d0301c1250120165542c0c2d11404018140707a201450b840c641e29a00d01e6000c03400300c2c9009105890512083c0f1800781d1210103943c0804044650020f208030178100b400882c8900300307886400c00c0000041006054101128038010101541d080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 794382104 1250 794380854 794380871
    0xf16211b0e10050412110a0807150206250c11061b0c0d08070b180303130203010e0601060210020a0302090307030507030b070e030a080c0c030715090b0309032b02040e0406 75
    0xc445a11850040b4002c0c0c04800c0300d0b05d80454441c64030000c03144005824411130b140c546003424a0b00c18103078048800300004406200410f84c2c14410190400801841c00051081c044a0130380d001000140103c10402255000401d010344403081112140e400381c0406da031813044c0381c030090314580d440070f0250300b520543e80c0d648918201312421707100d480d400a41c0c85003172411030307590200740c50030180c100e2800c0d401d90710540d03800720340c24002540541d03102000c04d01111072920500d800c6d90310903050315180303400060040042c0d0343c002c512501e189840400059039192a954140c0c020f000d81600590035100e584c2c400f01c1041030000703411082d80d020b1140d002c01980c42100442e600e41d02503024540640118181000255180c8084c02c09440c0c80015034a0103000400400c1c07a1004a502c01d41039807024a81138102e864004803004058140340a580d413840c5440d00d4007558a00c1040326006020b40040d8403852800540240a1140340f0801815540d40785c0c2c907000c4618045040d0340a0b1240c501e040880e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 794383354 1250 794382104 794382107
    0x150f0b09010308131d180f1005190212160309050a060f150f05100e09150906030a0b0105090630060a061410120606080f16211b0e10 58
    0x80b500c11041701d45004213503440c48450f0f100d00c039010080e1102d910402d88404130700e0100380214a00d200401c800000d041c034150601001c10540d0b007a00085103481041400b000c808624041a40300c000c146403880040300c8401c00320010f00d0483e401800c5405004400f80801445030044102c640c8001800e008100406104400ba009284600380d075459000204000c0b504024015641e01609070403c84a05100400420b5241108035007540c07402c2041200d0103003034603045c000325401050640040c00481c01b541e41b5030348200320600880c0d10414500e80000c0b03155807201345018118650000059529100c0100d40781e40d02503c04811007079010740c1c00010200461441154203d601c2c619100740300241e00020b00008002108401c410080b621955903142c41003802203400412095842510915088444814158014290390b09002d03000192050090b8003419140d510624484103030303011104074100d50b000784480520300803d0540700000030f5041d908601100d100c01d00c1603a241144101543c0c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 794384604 1250 794383354 794383379
    0x8010e010207062313081201060f090b0a0e040b060c0d0503150d1218150908070b0c030406111501030f0201020f0609060703020703050f07111c150f0b0901030813 71
    0x64101da0070448000007900c1c080505d1814101304d008100701441d120b90200780413122030090b008000421810002d1002c85a0f020300301034000d01c0545041070401c0c1d28160003d210b81c0d5403a111501c540d0710745402c00e90316910f40c070841d01042400310464100001e00710f409041a0006c84a102608407030440b500a80d08101c101404040c0c1e00030300092a44400035010341c1c00602c03900010101c3c0c05507a4011501d0310703100015540d42175064035440d80c26441c0002c0640352441070381002010b80000d204006140d4000026541a10010708082d2600c039208403500e854490302100d80c00c02510341000000c24000b0034800800d415000785e099501c10217540340019500c450548050784590300c81d40000d403c80b4400d40c05040403500c82c0c54218030701841400703a00d80f690031010b810f450a40c643e84403880686030049001080c184801c1001d41c4020468644459203c004030a5190240e11481100c4008280d58050b44402c02e0003848003186586078145050f0301e400080704c007400c001600b0340100303c4030321505 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 794385854 1250 794384604 794384651
    0xc04020a0203270a230d061409010218060f1e0d020d0203160c020a03032105160806011b0605061807020604050111040e010b0a0903140c01020c010807020c010309050708010e01020706 80
    0x65585d60320701c500081c80312010311500e06503071041d5030344000c650486d440c003a00ca000f00000c0c030016071501c900ca60100d0403149a010002c0c403c01b004c0140d0b00c7c0a82e642c90540d0010140f00004482490a0f07218500c243d00c80c000c103603022640300180718082108a98055402031150700031404c0c3c1d40c56552000d403a100000c0c00040c1d8410f420920400c0000c0c8101d0714080100010740c1480040101c0c00c0503c1d0641e04140c401c00b0044000c4e400e0440e540c1c1d84442c40c2c5d50310035024a0301c41903040008583c903550540720039002d8001600d48000900e15201c0d0314019030500316203034542d42c0c21f20740800d00035200e000c2900d0407a01035082505088805046006a6055070280c001d44075459203040d400c01c0099226000c0102032008070075001012a850030381d0811490702c800c0140c42c01030498000241000c100c0c0101c6814401e00d0000d10455a60014019518043c20300b8006100c0700c1a013071181c60030401d80d00c084503039030804008103602d0310107401030042c140c4900400d0040421300380d4006010b0b001070307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 794387104 1250 794385854 794385899
    0xb070e0d08220b0c1911100504080f03070204110304020a090513020d0302060f0a0203160309211e050a050901110c0310061701050408030613150e1609080c04020a0203270a 75
    0x741207104031b500d02803612070311100c52801e00b14070f002e503505841380c00d041c03c60400b0303182600041020740030340c101801200020080310228074650306e81a0700040d034012403401010302042d641d034002800021815054036031140c00a00d866058103132071800958609040340d81140d22451a030108d03a010300c035070080e030340100d12408160a40030714801d001c5000704510403041d00c009042800e40d809140880d214220166025660b0301141c10701e013010803000b0b804181ca40410407804025060b0440ea10806582c81e011007442c204011502c0d4000172483c0203011180c4542c0f600602d8840c030701081c12503000008a40b1510304251041688540e03040c00c07184100d90240003404200300203442c44c0780000c14031600248a10000900341c1c051100c2c1d40c0b2000c0907400c12091070707007003006003c030f00300f14400e8054501d591440d00d21800c9081610720b035103844c40d000c050b5016540114130304401c54024010b0ba040c880144244c03a664041c102001444081d0b02c9505030f000d10800440400c1e0b00303500013082c010b003d449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 794388354 1250 794387104 794387123
    0x127050403020c040b010c06020c0105071b03021c1110020d150f140604030b130b06031606050c030d1b0306080303100612270b070e0d08220b0c19 64
    0x10318080c13102900240380d8280c10025180303200c1d00040c0b01032010342a0254007000005080c940600042c20358107028003900c5400c10b1041d06140040d074006030000042c03805c0340d14030207259101e00d010307120a242c00b005c82695000c0c50120185680080c0d01406101250550610140426002820f42054180030380c440745007031043c090016401d48059021405005001d4a00d420740d00e03118581864816980603e900001c003d45e1000d2007111800c183d003002c01140a031009194111080846081500c10007041c00004140107241030301c28002d81d480c01002d0041802210410b40403030200410040a50010924004002c9000d080010030741e44100108140c0008580c1070103419100c58148002540700b9544885a80c02c00044c0000511054a2180800e400540d25840c018201c440c0041c13a2408106400441d030036940e031404461450981c0145144c1e0f650b00340340199140d01048070214504031420310030300151080e00301d802800300007820002d0341e90340d8420b00806404156440b2028203400d05c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 794389604 1250 794388354 794388373
    0xd0804030b0c04030f0c0e060f0303070b0601030b0301021305031002120f0a110708031008031801080405010e060f1602010c08061e190f090b011e0314012705040302 72
    0x200d04505030304800e0220b103060070300741e40760381e01c0068800d4848115801c03c214001004055072800410307401c04412034403900014501c402103a0399001c1d10358058403410b0108085170b01e07079002c2e5109491600c0090000d555889051118034030600580c800c6a01034400c00c844030560201034801d0340c0c00921000c42c1c0114a45035041511842d84001d050840c0d00d40d541c4a00310b498030580c0c0003c1602511481d009034a91030030302040000d0841da948462882d0f003080200020080d00c07102c841c455040d09007002c54094540382841030040074a40c0302446144200800c0c000c00c641c00010310b0b071003a043d0100d00c0ba01d00981d00812401d03181a4461750020a9a43d00403c83ca0319151066080c40c0c1c15090144c3d44030b400ba400003401140080c50120b60080c1c001d00c052201d072901100b0100a040d035040244407480610340004c2010b0305400b20043c1e40e01498000b903086900c00e800c65103921007075800741445940c441565201c0b00c25054100d00041c411403500100401940c020588101c1d05900601239030103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 794390854 1250 794389604 794389613
    0x6090d050412050304080307120809120d090c0e070c12050c07050904050a050718060f030c05040e03040b070b061c050705040c051e0403060b0a030b1902091011010501050d080403 78
    0x5924002c129003a01080c000410030400c01c1010702001d0340220f1524042c0e0b1000310300a400301e04003038040d200c517411850005280c41c1d040400c840e42d8141d0250001800306040c04d00142000ea01c0d044000160001014817107140d0f0312150441013113014a049100896450b031082e980c0d4071070420ba203c40358001a400300003e10f001011541e02074065801d50304002c45554415080503d10382020300c0f032418455041c88040c105200c0c04000d420700e082001e15050071030300d848410403501c0c821584950745902d40c8034803e030340920903540181641400c450701c42003686400f4002c0c10003120340500520001c00403101e10540c402e004071200d070f00b140c040c00f44030b810803041c40050840c00181c0000d1200400049603002843c0421b10100500c4ea2601130300c0e44e0541c0307410030a4503040380145100d40500d100602c0410200f44000b90840d0002d00c0c445c80b240f8038041801e01034091003070101d44c004a007600c8103052507040003100354240c08810003000b50b0303038840b0304100804514040c003a11115040c4810b00001c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 794392104 1250 794390854 794390879
    0x60503070b180409151404120f050d0207080405090a02220b160309080d080a0f0b0108070c0c0b070b06040f1a0d170708040603060501030c0f05070201031e0e06090d0504 74
    0x942c002e05c81700000c0c8100170146010740b412200c0c1d1000d1209100100010b0106446458640d6145468000800003da0310f004015004046180740003c2e030001e203800421510700121002804c010381030640320301c0d0106e504002500300c200074a81c41401c011400781d1a1103070038588001c2d107100726401418404142c0c017004c500250781b0030440902c1001040030074140000c018401341d950060b60340702103d19146420600781c0c3c00032800d08075018104541e00c0c05584c2c1150740c02d03a02c04000c0c9440c441190b128204178107485a80d901000b018800020000b0a00201c1e1181902c05c2e903098400344a214002811001140e1050880c000c0c806400c80a030300003840c01c1070182e41c5a9025501d01e0300390b0501180301d402564000b50044600c1c1d41700003020040203030580660347c020402403c00304030180d203120003d072651480200751400c012000034501c08681c043e512007a504c003500420140700d440ca00080740014510102d90141c80d20524002451203080018500380b080600e50390740e82014603104441d88003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 794393354 1250 794392104 794392121
    0xe0a1e0203120d0c1823130603060e01090308010303050a090e070518150409021b0d0810061d13140709210c0519080a1109090624010309060e01060503070b1804 70
    0x40761207a00340c1b004240d40e007101c60f0b13080407000305000a0051840c0342c000111406005046401c1e4140a10f100c0400c1d0401d002c40c1c1102d8250038150350310351300c0300301c1151044ac203a0850080c440200060041340d9038800060090811240c0f980d41080d44441d040042200152401c140d1920f41000103220003941034019041c0350b00c0a180c070b41c1155811483d9142404280e80d1150000f60f030705070400c00c50200702100240148551304041605491812214400d0030080c680c0c1d90040800c0e81440410300002e0f80200400255483d9a1a66040c0103000611480041c03050203400020400c8143c0194800800e4206281d4428a21010380b031900c018407101c2668040b030307940454a00100050100700900c815500184078442c00389403400301e0020055400d40150070000a9405103040042980d810303a9884204030162078644d01c554034600c0120b000d8144580004c1c0410300740b190444031060150441400c1d200101c080c1c415654481b5001e2519020f0342c3d00041180401e00368501041c00c09500030141c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 794394604 1250 794393354 794393399
    0x611100e0c090114090c0309070e040f020d1b08010b011b0507080607090509070e09040f24020c010b030118060c0e180a06090e0a1e0203120d0c18 64
    0x240301c08840009244070000343e005a08a208100c4c2e02074491a000314501e0b4032900250b80c260640c1009410299145090700410883c41e4070000842e040c0f02a129454a44540c01045201c920740c01e4608540443c42810000c40d0000884601048040d410b008003154040181e5a040ea8140800f001c1007800c04440c500307844174051620301090305001405085c0c841c0007151076840000d4900410310928030380c001d010204100c22800c8a181c42d076552034500d84c2290700690400c00740032490406a00c40c10b000414080d00e6030f03103160160051600da4001d01080004100200802c0550800345800e0f03070000420701001034101c5803e07400081c00ca500c4041c40c403a66141820000c4041e00220b02c0518000c01c5800c805401d040030441002c0c0d090103900080d0580071000d0040d1100c0d08401d07035640c0f82404000704400c002c0724104150418218038407040f190010100c43ca64090078600c41e80076032100c046442085d0034030f520a03030001d004194868007410307006440079a041c0341c0501a8160505c0c10062407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 794395854 1250 794394604 794394613
    0xf011403100e07022a13020c070b03190509150c1c0603060b100903080f090114130303140a05040e0604020705010f0b100e060d0c02121306090611100e 66
    0x50750b0300802c2000e03100e040c2580007050100c01840210365080045400d99000d44a00c6036989072030380b1408015030020000c11805031b00c8001c0d54094509240300764111a00c0345001004120031800c9102d030780c00c1c00051041080019484001d080ca07190043c0012502d980e401c506c0c0811110605100204105002444c0550354a103520031b002065655544c03040d103500c0c1e11030402c4081440c2c207411580e02a109800d0000c80140b071941da0683d10300ae60041041c4290000c9040403003a4014486074182c0c441d50844141e80c1d1000c4030003109247c4c42d0b80015400140903500606809040808072540071015859043c2424500301d290104a80002d10943c2c201b902404a03400085e8240101e0100442840001c00e050751008284161040c815042d40d08003d5a0458011039440d004119404404110004600c441c0691010392030007181c92900700450500207401e5405084c00f9904009032412a40c40403012980c8050450b10000f00790310360460f03600490010f5040800343d5010080a8207101d040c2c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 794397104 1250 794395854 794395859
    0x812030603101503031d01021218040204090509010e120708090d0506250f120e16030b10090504080d2004090615050c0a03180e01060f02010b0f01140310 67
    0x1042503564002203141c00f4034611406004150b00400404101e1b50342e4220081c1000d80b000000703564820310068210fa2480000e10b401050f0450580200d94000140c01999925a100080740c000e0800321510303100c5510b046010008420041030700003284401c1c090503814004603803140500d036404000200d03400200040c040c0002081485814403c0310240b1741000013110b400f802d03000003c000c8620700304000040040001e1150899600a881e1b20010800a442c000c0c6c0740410b45891041200300c03001c21442440002004110400f2502c03c00d144a01050a240d640003040706480e4103640050828405001119046840350301c0b12807580360007034041003543c04914140d103156201e600000d400e81d031101c8090060103040102740340008124a07205107030940c0c4845241e2221100c02d070007010050010780d02d27690414000b0355a4080c00c6a0751480802d075070748402c003070b080030401da0741d8070059400d003039000c0054944640d17144800700e010307103601c00300e040541050300c4158401004031032640e81c0003002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 794398354 1250 794397104 794397133
    0x2070c08030702011101051605070c0803030103050d1218080a1707030c083904050a090f0c111e03070f0c080610060e0f0d050a0b07030b0a0812030603 66
    0x1400041450324069595000580001401413150443c2c000c201d07810181841812450094400d001120034503085440b68090f1038140000310861b80700c0072841c0300c040001300c1840404200881540d14a40301c15059400b0034198a066a10210510714070344125100900801c50903001000d0200c2d0314500540b0000c1002c40c2c0c41c414000503030303034080041e5581604d00d5205402031441e90b0401c3c040300da1001081000b00412040c145101264000c0c409100801910200c60400381c601030003006100c01c2c0340f180c82c0d40c5824002c0240b0440402e00320708020140803410300400300540f81800540c0505401c8070b02d2060000c402120500c1e10940c0d110070445500800d1038800329031501d41c42020215600c038501b5400924040c0c005c5d002c021079180741d00c03040109581050b030346001d00c0310a460409a03a8620b200003500170610000150860280c03100c000304215422005a11854481e181000601401d40c103100c5101614010380015902100c502d0030407105100195910050040840c2d4034002400c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 794399604 1250 794398354 794398373
    0xb092403010525020a0807020402070311120310140f1e0406030506101a0d0c050705100f150501080c07020f13050415050403020a022103220509090a150207 68
    0x10080c01c1c146400c0d20b500c1c8010003207110140f028600e8802080c40b003d140e22444268407c215000b44070303c1e8001058400c0601842040144000354016184ca08072166051013560380106c3c5d02c2032405015205c00b00b020b00e010000e501c2d0640c4054041d14000b55098140040c040c2041207040d000380c1c3d51007120a10303070340d1405841c0140d440f6a002c1d0102d030500360911041304500f500502c4c000804078102603c421f42c000c0540e20310842c00d42d00410701500c04142640c040c801d0180241050007003800c40c490030645600010f00c0d51842803010004089601d038895a008228029030340003841010100b044258007001400c4510300061031001c80c100310310f0014561900c80e401e00e541c4141c6036005c10041c072130300703102200849080b84014056403a0580e8001c2d1581c0207640021b00c035003610b00c0c10505150503c144440d86020001c100d950710403800c02c41040c2900c02c0ca0202910b80d03482e0001207005d00b0b00c40c6e00309010700340c000d0080040c54895a111202c103503046180d042e207983e0078852400132030030035603 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 794400854 1250 794399604 794399611
    0x160b011a1e13092f031311121b060a050d15121410060302061207140a270f0509090a02060f031e04051011090901081509010b0924030105 60
    0x10800100c014088441080e250102080240502a02d58813048404500301c12030713503c101d10f55450302c0d54042c2c0703162206440031211459900130110b040d5103004084001a004060880103000c1640070004608000345486410329840c001070040c0711000c02c10055801000e0815280000c0801407519021a9a21982144016035000c8d400102603808101c06204483d2800d4561200b40062819a00440c80301d10030040041444c003026030018007031901c40c0c182c42c0501d5401c0c04003160368201c10a401415080310f03210303e95043c074803400c00c04040c0340a4a01c08088443c000c1000d40c040e450041001501c0000901c00074090040b10982001a41d90760010140080881c000545a081522400b01c1c0440000004e5440d0014901800042000010f5860803995816130100fa9203104a514401900491000c00d800c1400b801c008a88401c0204510040c10050b55650119548441c47c95007a1004503400310b0f080300c0e000d4081944c044800ba4100030640145840301d5820703000d0000311b130854004a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 794402104 1250 794400854 794400869
    0xc0306030f0f0b01060804020a03020114120c090333040215030f012105150c090a03140d09120b1e150102011109090609090a08160b011a1e13 62
    0x501148200f000300c00989014100a1521000c0c3d860aa80440c03084400c900000e8188070380304003070720b08000d0031100305c8466003548030f0428041d09014440100c2900070686240c480d001300d0b1141c00130381020750392008541c11040c9090644c40c2c3e030b00c00c8540c0e08290240059810001122f501c4e68030000400013180204025410000d4640c0340410005016080e00034240704448074021602c04107000081098662500000641d40ca49940f1151220303841a5118641c000461000000c00c0c0300018440003004100308090320382460b401102101c440d6020700515140c0700d07514500e440401c0c00a680258040d500c0c1c02c0d0540d240814040103c070a0904490402c181c60303030b40310807c409503420300440915101e980c1c407407401c0100319000a445075000810b800e000b082c40100042c2c001e01308200d071040d8160040c400c16522920340d1001d2902e15843c040a80e052044580001090906141541e203103010000101e8140048902c000e1040240ea1141c91034155041c4408903034064404e604c400180400b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 794403354 1250 794402104 794402123
    0x9020d1b08060705030604110901053405061501090302060d050a020d0e0c0a08010501061403040f0803010609030c140d0209180f0a0204150503030306010f0201320a050402060d0c0306030f 82
    0x11b9402c01066a03106200744015a0b424030620009980213010b4030564a200b0b2010001c04d526000c0540d0109210100b52415a4003180c244080c0300000c40c2c158002c80e80446404c0541c0d00072001510108403a22009400000c200803c02d0b501548d03038059a00540c0c0b940c40036241c004151260790a40d9140c542c526100e4101d151000c0315032030941000d8000f00030b501c00a010561404002074640300303140b0405480c0920000c00141084030480d03281c070b41c2035404280d85441e545c5642c001440b01a180c0401c44841402480c0400c0b0a5103890203c900702c60002d102c400c8400d155400d00840e41805080001c2035045580c6d6880c0d0b640003070040320465014840103003491030144c0108000d0340d5100f00f0803c800014110b00f80070300c5d20701000b00d031390000302802c1000e10a01000d0f03040340101062104409841d8505e030382181c8214401220f1140072101c0c0340c014401d40c65030002241141c00c243c5009603c80410850002480c0307d5400241c2000c600b070900113140759076a1500b00640139074034800c8903c07182 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 794404604 1250 794403354 794403361
    0xa06300506090a0c0813050a1208061003090f080a0c02040f0b0102010c05040302180408040b0a030f0f020c150907030b0c0703180e0123130b0f0409020d1b0806070503 73
    0xc0c51a482c541c0044505070074480c40d0324050f0060900503000c2c14056800c1060300c0d813030b01804820003190028075404100c2c020503803c001c0000f03040d00342c00c0e10168840e5800c07400036512203100303004244146802141306604000e10740d6501340181e019600c00c1e01070010b03555210300940c3e61480741c20300b0800c2e003480214a4104001c002821100c0c0c80035003c0c14440140420700240c2c4803522a0309241300c03d41d0300313211262203d003031118040c000c543c8040c040d00000200d224245a00d500407000032210080203106114544007400140d00030711941640340d60151080d002503158412035a40c00c94102c6060300c0403691030362a06800b901080b02c12581900c4000340f10300070503512500c5900328010a08041d01c21728109150074000d0001071203200444900c032903907003010b69490102c0c00807050f801009490703c484c0e5020200b01500359190704c00d120390340e200008a00d60070316000750f10750300d580100303640c840001e150b0796042c1d840c81407000944062013040f404200c3d40da0810083c0d01402642d2a10354417842c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 794405854 1250 794404604 794404609
    0x1e08010905070306031e020619020106030309330302090d03032c07061215030f02090903090a030303021606020a080901060f0b0703030506031507030c030605030c0a06300506 76
    0x3800600320404240c41c0c40000c10200d84c0306040e0552880100c6c4001d0103040882c000600540960f8200885c11b2a52120404200c1d405601400840784243c9510608a98176540503020f40305004162900c5105040001c5000601d511031200c860440d080050070800714002103102458504800c80210b95560f1401c840e21702140e90503000d0b400c102050045001075440041d40b2000c05115a5080c00700c41440b505070060543c20145840340042c5d0441c0c0f296642e0b003001700c5540041e038001c0e0b0254940d10080380c40202e0200c01c8a01c13070034014000000322440c2d650120029400710034a0308141e58200101c000190440c0000c0c101c52640b980c0b100417a081554403a07003111107071b60002080d203202000070003d0038040c20582d82d5854050400040c0b556426010a0400c081421920150402d4030100302d003441d0940d00c04000c40c000c80d03130100011901c0c1c0d4181070340d036110841401c0d403206900200300452446041d118005030f2403035403064a12441e50140903142c1c44020240320360316440b641000f0090 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 794407104 1250 794405854 794405861
    0x2d17180613120c140a060c08090601030c060c0201020708030301090b1002010203040b010e04060f0e0102130e060906121509030703030e03280201021b07031101111b011e080109 77
    0x581881c026030003140d41d50121000c424120070061180d000d0b106000e020000442c0001a0703040d40c00d6070800c407264034240340145000d60212010920350400701c2d140150001c0c106041c1c076840400d440302181484010b891071440721408a045100d40b501c0400c02e0344040c8081e40c001e0041140100700d1700460020043c0d10300c07c8102ca2011a0320600c00c100205003801c83c0b41e41110a042d01c69049900c60f4200300025041d12244401c2c028140b0140741c8200030154010031000300c0400c01e655125440c1d4039258100c1000755013281d403000f0120045003189c0b90000e494401464100121560004401c0303005054100895284441c0c2d007000c181041459054044c1c04980c03c00d840155140c1071041c0303a44c0404405180c0e0400ea00c52039584031501141c001d50464000f002d04101281042085520707880e541c650781d002c2100c160f26208045621f55028840d140709100c0c107030b809040200130f58064800344180002849040111050240400e14110045036a009101d03070395141c0103604000c240000d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 794408354 1250 794407104 794407111
    0x2d0a0b0f07020f06011404020903030a0e04050108070303120f09020a18110c0a1101051303141209030a03030b180115141c05060411030906040b072d171806 68
    0x2590404041d50041481c007095060545030803e01524000746c100700800c00038001e1040316900341c0300024141e10100e420601003001d5450403030341884aaa2071390051500c92800b03100c01400704034012004490350b181500300c003105032040d00d00001d015907590005038149200343d10105015128031075000300c004841c01621388609402c900c8600d085103a808003542c0b21290720000c0c100b000b80010b50711050380700d0421100b02e40001ca590403a83c0ba1281401812800c00c00940380240c403450000b0103150550718140c80300e1440050103003101c07042948050b00640f4030f40220383d0748101c0111411011021155100b406042c1c50b50f0381d003240481c810006000203040e050007260b408024030080803551010655108124802c00d0b020a1540300c44000c90080c2200030700b00c1680020100c100005100c001030102e219030702650303c582075a20390713070360580c1d6034030640f0030a580e011040c1d044201c10200c000300c440000c0c40e030340c540118040362592070b500500030700380d440c511400740002415402c01400c1102580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 794409604 1250 794408354 794408357
    0x2110140103050714130b040b0409150b071401090b04060506040f090203030f0a1403041b060e0105041a09090403030b040b010216030b06120a060b041d2d0a0b0f07 71
    0x55414140c002902141240c5900b00040c000082d10340c01d441700c144500c0000342034440f035030390f2500d407110410301d060b40050140b102600e15240d030300d40d0f20741d051140d54400c03100b160200c18900680c50b02c034a9912000c100c502c20f907564a8505000008140f00180da1259015500008280c10b100003000141e9001c001014256824803007034030056074012044604072590250741c15620544400103440400b1445906a800000401000f0900080d4014009824068062000d0740358803a041521007060300f000190014070240f000307100110103407100103007103120306200905121300d100000e10711503400c80d82100004d48815103600d450809019800700300c4800d002900c002c840c00c455004405501f8407015240031504800724515445590340b564220002c5415120007400360309042d405407001601a074003913440c2540c4516820000c040b50070341e40704040c0c05420362502400c806441c0031804800b003003641c904200a0760080e4005c024920002e84a0610000706291050005400f0712004003100e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 794410854 1250 794409604 794409611
    0x10c17031005041a0907021e071d1315020904020d0605100e061c090209090307110402041d070e06070506241315030b0106021b01020d020309062110140103 68
    0x90f400039040f001380003242c60a50700c0010983d9014000c03481e04008850a02c049006a2076001201e400407510320151029004800d01c00c007600520320b280c69a0032a020b0012080b800c0300c6200081150038210000b51000102504000c6200e0010f0126030103d0300315045680d6440d404c03c800d0501c1d025009000c8401e043c802580100040416224400e040324036030f600d025a9510f0f0080341040e03100c050710503000b0f008040e141c90702000d003699981c030900c410364500701502c0546a892515000f00da0949601c40c94003000c0d40c1ea03c0508410a0b840604842d0504c074000c090b2900380d0b11801c0c0a040001d000d00300910701410300340318030200d4003d100c03040e03242003001c1c01d0b50303a80301d880701d80e240402100740c0b00c800640d000c619403441c0200c04103070304010300881c0380354000901c4641c005804400b884018000c03882d184141070040e41d0f940410610f01000da0003d211105281c9010000741c410291003507210362407043c010a003d240c8040440707118880403035005080c881c11020300015400301c0c1080c242007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 794412104 1250 794410854 794410871
    0x6080a060503061308070c1512060f061b0311061501080f010e01031b15050307020d0c0b1609031b030b150603130f141e1203060609010c1703100504 65
    0x61407103042501422000c00006d80c1000c005424103007800a246120386c402156440c1d01005204090045c542c031302250900c9404101c001404d00c90404480032615056002c11000081340307200f11883e40b064080c0800100303049035440e81400510f1084000c0114191b45070514800507000000c0a009180c0b42c040000041c007a2800200c51181500d801008140b24800c10070b4220700905003179080303a0144604002c0700c000c2180c006000c1d601a811680a90301201c070548800c50b1b04038654240500340317000f200c004c01e00031903500d00080400c4400340b400c0d500c2315480392239401283c5c81c00b1003600d0b034822441d4020402d201030308203200d03000f000d030302e400101011500c40058201d0201800800307062030310b031081c0c008001042c0e50401740c0380d6001e8054804204118078498403900d41c1c000c1e52007801402000b4207100007021030724180000b491a070207411038840d14240003540d0001c0c55220705001e15003100384082221403000c240c941c91610505a9640303090500788800d6181503102d94000d505040351b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 794413354 1250 794412104 794412121
    0xb06150903100e07090f14060f150d0603020307080a060501080313090b010302120f06030706021f0e0a050a050708100c020a0308061f0e040b060a02150406110406080a06050306 77
    0x51100750b40c05200c011455200c407a006a08013086503000040342490b2030207240c2420550340042114a80360405100c0b2a952a8244140440200d020030b9000e803803102d1215222011501030248041c0c00301001800c1c0ea00c0394003182c603040040d0408001a4821500e100403c0f800c5e0180d913014001c641c0155007071100e0200151072492150040b03130380550300c802c50942c0a03442039060315144c50480c0d00d025510b040c0055011514542524803d009019107040030401d0f03800040c81d0941d15640010a102e40d007040541a00202040c3e0076841a42c0500d5007004042041000481085170052000d08421860f181c400c5140480100c00100c1103030400e260340c1030a0740c0102e984600c50f60141020107c41d50307881c0004000c81460b80f4045507006105001010180c0d004c1c060003151f60054900b004400803040070000580900100f8400503841001c055454822803d00160000d00c01d008c04580d036441c005060100e600305811082c0003554540412469140c00d000d40e87c01003006401a00050a000d6003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 794414604 1250 794413354 794413363
    0x30c0f12121f060e0906010f1d060c060c210103020d200a1509090908030402060d11030109051909170a0903020a030c0f092a1107030b06150903 63
    0x50680e895003240c1c0004000c808080d030042030b8505040304980e40c2940398800541601203800c1201d006107040000034a0a5008881001851034030381c8a0210403080300700d07500390703c1182004094100c40c003400101e00e246020001c0b113000b81c41601a013922102d58401005030782d960f90412900d8040c00100410241c2c884900703900016401860314910002e1036010f04d800311450082c029004030803200f0015100742c0b21019028900802d03070b0b460354007996581016040e1050081c000c1d0040b0f4041000c140107241c04802440c081e024408040380e5039020400c3c001079074000f40c0c000d06000d07485208101d1020200d86941c040040d00800c03c01100c076260711010080d02c0161100b450445000507043d403118001c00c40000150f03070041c0032601e059242e290450351501c10788110b070380044072a02d0106088100d806098a000042d240b2041c284249041c15900e51025580350400d202540300c41a985101c2800320001640c0100300c01c00c000d040a81c2808001100da0b0305e10041c0e803070140400301e0503980105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 794415854 1250 794414604 794414617
    0x1a0a05040f0617360f0d0f02010b0a03020f1002100e010603021516060b01140309030a0201050903191821110a0f140102150106030902040b04090f0f080f0a02030c0f12 73
    0x19130043d00c0007a044e4990b00d0492003003410f0030b1600c9a0030940180f5503100200101c0301e407181d4020f0022020032001e10494000b203010095001e40c006003c0002c50070014400c1c0a00c035030900c1102c1900d0049143c807002c0b034120384050303040c603511958140150705211142002140d241c80c2d1861030b00c00d205201d004009020b0000500c465114a202c04241c0e101c0c04841c1c00a0fa080071a00f82d49040032001d65940b5881000210095401c10f400148a01404001e07503100380e450038280d0070b140300c3c0c10000310340f488908401c0d06094a1021401305e407019038007045030f040003002420501040a01e05103010044c4403417400754031440b5100c5090001605418210040f10f8100a034035403034041c50070060303040200c459614600c42c000507000144040e456006880203a009403010030801070b19105202c1039031111480505203540300f0101c0030002e0706d0070324106081400303511b40d18180311008015510b142d108880940c0140c2c00400e0f10051410207220741c1c07040402c107100414846a00b1907a10700c880c000c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 794417104 1250 794415854 794415931
    0x1a01050d050a0b040e0a05011409030708130b31080712050a0204050f040308060103020f16030c0506091b04020702030705060a020f0a24061a0a05040f0617 68
    0x10740100c1c891407025003000c40801001030081c021403941940041d91840014020780e110743c03c11085c04e540d5140e10032000c1c081da4085016500e481c0782a203400030700d644003034506204000e0700080081d0041108010b007802404d1101c540340040d80b803030800e40d8010071071840c0f0b0781e2040b4034a0741003010007800110041240d03c4401d003000d074120306084c070600f0400140000fa400074105000c000d1078102810105100310f12a45902400e600d500300118200e0052200400c840d00c0e0400406040f5007402568000c610320924020103c4500350341c0ea603080102c1510926640e034401c2d0303002607801c0d2410030640d401600c2a5003c42c01c2094680000381c0c0c41100e44515809060300040c0400c9280c401d10148503e13580380421501c4005151824003811303c03104010315096202c000d003c1110074280d002d80e40417100005030304024000500440c807429401615520f082c81000c03c40003410701ca4803801500100007175243d41103544043c40c21000001c00c0200388490303154069845d02c0301070303800e0003200c2c2d0030b031800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 794418354 1250 794417104 794417111
    0x305060f013e01021315202a0f030c1c150204080318010e0312090d0b181212010e04111c05010e07060504150318060608011a01050d 58
    0xd00c1402031407050030006604803034502c0c00000d00030710054000701442c40c404100d03000110750f9141121a000b035100780003000121988000411039840340b5000c1030310b1b42e03103c080c0d42082d90070b00e0340151191100040d001005411401142c41072802c4500001d0b2008154058140c0385c11607070004083d41000e240030078002c9a01070301034050001390024482d81440500045644a44514140d566604003100e0780301003580c0b0454205039948100e5120410b11006802070901d800b4460390000b20b5000300340100e0700b004d0744001c500046a16500c010f0700801c13800380620745d8109074195882c01c1564205d0001034450701000b41a1195a4000d03007541112035201180855845a280c14805800885195a84030ac0d480742c89003007001c05070720031318101407107034000b00061440801c800c2d0b291005440342030041001030000708080000c1e0101c0208280040c50001030151800e0318604400211907400d480150340d0391000d000541c003d104a85000c4241d4914000e01340481000070b0a5105e201c00300304400e42c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 794419604 1250 794418354 794418407
    0x30b0f03030a0206270703060e010f0915050c091903050f011e020a020c040207050d1e0923030f0d020f0303010b04060c0f0203010612050c0a0305030f03130209070f0305060f01 77
    0x2880b920701d405c0c0f2090300c4150755400d944c034102003016107015860807886d546010014003042110744202c03400f580d130080b90361785c02c3c4103032109139030003004002c01140c6030000070000074256070383e410514268049018180c410007402e41c2402454400c80800422042c0e02d4502204a10030090088501070b00403513801603038981260300128180502c0345038a03a001400072035010104032020900da000a81d40c2d86c0c600041900311184107201070b14048106011403840c820078403840c0c2142c4681702c612203004034041840010320001c030f85050241610303014103402c004003500325a6810701215000c1100d00c1c00540c03c0d541405120103462080d0b01c284407c0c0310088138188100721350300e06080b92281c0c00030020040d240d6100300348441c0c102907500c122040e000d020700040a43c81c1804641d025a80c0040c011400d100616000150a034406002c0c05040740031015110010b0791802c80705882014140da071581882000840039081e2030000c0c000034428000c5009107045664041c0c0d064030142e1072420354450514 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 794420854 1250 794419604 794419651
    0x1090e13060207030806040b0a06050f21090604200f21060f06040c03020c06150a0308040602150f09060703110c100204030b070206190c0519030b0f03030a0206 70
    0xc229000042516001052030024940c00c1418180f04540075242404004071071001c10426250500840f40031401c103000d10790700041184d0242900300c148a10000740c0140d8400c03000071800b800c40c0d1386059030744210200000c00c200001710008110604510304145410305000503900300100000320f0150304d078244038102a4000e0501e041c201c02c108001c0e204070f070603c5400341e50050382c01c0701c10a0060742804e226100041c80b900c05c44030400c401030083d01d1b030303600c0344001c4501d04248412600d5004441c0e010120109224200900081410f0303001005004641086c5044125000b4001c14000d0000d200b00b0200c0b12011403456800703881482c3c0001c400020841d418414000c0e022500241e1081004a600b1280740ba03008100340d0303006501c1c4000f03a032358841d000c9030340b4441240c0341940e550006144a15890f0070750800711000c96142003a600b03140f4400b208a0004018040c0200025103907040c44440d8142515004804d020aa025526044000c0030185d51100302920050089240c01c08080100703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 794422104 1250 794420854 794420881
    0x6050604380a0e1617040303050609060105071502070f08190912211e09052103070f0203010f0207030e0f010905010c1b03080703020f0d020105060f010e041d0a060b0303070201090e 79
    0x6002405c0c0c2c0351094201130070010300400040b11128000d06603d404100990f00030801d80d0782ca5988404548110321602294034040c0d00b20080441e09402e00300b40000c0055803540191072102032200f51007240f110010070040074510300c2c4d0310601c04003451084250104203000d0061004140d01b8071814580c09807a801150301d960949181d0100c047c400018040c103903400748540c07045600440b07814464107142c0300812443c0c143c03e03405014a034000c10000700028810003401082c0307400240002007495003554440c090b17078003c88080703001601c01c000002543c5041822006107013800e04e011000c083c04c09002030138107100904042c040c1c03154450f8045c05801880e031600d015540c8a10030030b40324152860080d51703a0b0311070039103240f1500800a003054541d00c14406d6510904c0300404105c403250100c0c0040d02d85040c211480354110780c0f180c0700740210030500a8200d4000c0d034501c004040c1b42ca0141010401c440c0051032040c0b007500100f003400d0240c3e90014030b0b0401d5607403c580c1c00c1d4207034440f102030705c180 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 794423354 1250 794422104 794422127
    0xa180308040f05030f0408100510120c030812090d030b010504090209040605041b080f04030903121e0f020c01090302090402150d050c0a09080a0c0306050604380a0e16 73
    0x41d01c00010380c5c030300e40207412004d0411548500c00301c2c2e030141140507002d000e0302d1088030b0000c000742d007881003049503c2e0151342c0d40304000c0c0900503810100341c480e10780c8200c50b40450341e8071407029101010722000b81d00400c8803000d000b035a0710f01080f0343c40d80c800009050b449584160f5460680104850120b0340e540c2c2c0c40321008080c01001007282c0ea101440d41b0b0042d8003185910400300f035000001540302e0940040951007164155030f030810790350841e078440b10308024071001030042204910b20220950040410980d0300603050b05d80304103144034440c00910f01105020b5013410000026010030050700c51340301c400e4000794100e88038250030200006001d068029400740020700c81c1020140f20381e5004d001c00400d4000703025035902e0380c01621100c10340c0d81d4030701c3c80c01d00800c0c69800000820119011741e001c10b810101c02440841d040200c0c48204401707003500c00010035000c40d010010302810f9031b02813041251a0040d52806100e40c0781c01066408030000903c180380d03044212000c29030030341c840c00800e181d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 794424460 1106 794423354 794423363
    0x40501050a0e060d03110d090f080f10090302210405090a14271212090c03030f0c03070c0b0706060803250809090403080f0a180308040f 60
    0x401c40b240e141d0036420000c1ba801d064480c140c0901140c0c01c41d208503500d1064050800158219000142d0b01540c100e51290400c1d40c0c3c2205c0c0880c883d52000e00c440300c00100b403915400d06904003291751034031104d00c40e140e400c09101040c605024106864003a00c20b0005c1d0b40d42c01100320304440d0307902071618403010f6000020b0f0341032030b890b1400c15100f0740900320f00c0040740039031303152a1800c0b10003212440842c401140c4c501464091100301a0300c103002c0402041c0680f104008a07480b4452101285100140046d8110003c0c030b007001103d12095000101d07400766607075819000c980d900494402c440c21424088009006900042901c0c019038130808a80c0481c0c400848490500f03d15032011100320301e003804104456030720000042e208902a0300c0306c545c02d1070480b141d0140198001c0034820042c2c6402c89030b500d50061807440500e02c41e40350401a10300c1e01c560405a441441e01c0c04001e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 794244604 794424460 := by
  have h0 := BRFrame.cov_init 794244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 794244604 ≤ n) (h2 : n < 794424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
