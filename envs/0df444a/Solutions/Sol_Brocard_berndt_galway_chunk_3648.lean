-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3648
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:16:51.686725+00:00
-- url     : https://prove2.me/submissions/1c8c5060-6fb4-4a9f-9030-ca34ed2daab4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 655935251 ≤ n < 656115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 655936501 1250 655935251 655935277
    0x71112011a090411011101090218090129010e010903021f02070b180103020a0c23100204051005030717090a020a1d0403110307061406030c012d05090303 67
    0x2a0580c07405460390076100100c04103880c910070516083d118040c0766121881058188016060350840360341003035009044040c1d004102c661020520000c0c0090480c048804250541c41c0624182d00003020111444480250030150850700d520314004440a0101c107080a06024000d207010006070b96044240341803004007000030b50402e0080e20000d00d0103032541c2c00044960700411040424030a000004e116005003802c01503625020484120350035003d002c00030b014085500300c9000c4250340c3e10075820000e0035001c11101c002c0241c580ba0800c070b00c1107124080c1d010003888040c008503801a005194440418103000b0140c84c1403280840e04914115894a20b0b500b10071606003c502d0721091800180940c00106681c1043c003030a12072900401401c0907007403103480d0303100ca800d001c030410407a541c403035004105210603451401401c400c00d6050702d03200e200b40150f10344102c7c00d51040595051400061245980302000b901040c150501160390490030081308000e40f440a8604100078006090015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 655937751 1250 655936501 655936511
    0x1090c050d02120610140304030503131b08060105040209060316020c09042402070b18011508102304080f0706050106050918010510030e07050405010303080f060103110f07111201 78
    0x44c20485442c03014a04c44040c02502e05425540081e400262a8800c0d894100fa580c1d9031600428104888000f820040c10205c0b044940422041e4241d442030403030389448100d5a0300c1e6215010801031b40595040550001810300001e42080b4031041100010300e0340740169091a440380001c50505c42c011a03050300c07941010312001410101c8052143e1460750707100d40450038850f8644c0d074040d146202a02c000c0398054400e03401d020000d403c0d4000c10300e420b122401d56240341d80c0d030560251514003071700750b81c4142840e18115850020362900c172103015150f02001e0090310f556560750608950005070242c03003851414040130001410a100c2c040c040c05054480315100c0000d407080111b240c900c08094410242c81da030041000d910342d000d20668040311414045807425110107401d1500d007480d440303554007904000001051581003208140034103061000081a50703140d0005405070382d1050480000c005082001e07154a0603458003400c222407056801100405080e800903900d005428085002c0d65520 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 655939001 1250 655937751 655937761
    0x204050c030f06090402010512071101051006080c040501090302011d09151f0806060703030e010f052502060f0606070c09020901110a05030a0302031e09010c0e0d0b01090c050d0212 79
    0x10700b244660094044451040c585401d500092580c0154070001c078000070700301f022944060060f000d4a5610203410020801d0b0b01e0303c4c141c1c4080d0700d00540f0441c00410712100c04288000410170840b81600c0042e110110503928690045a0340010b40c61207151660300b06071020350b03564a00000c1405101c00413080c25a82c8503034800c02801000c441881008854810825800c5070380040d001c503032026046440944907205400c0a8002c1c000144072583e484d4a410a080e0001e849a48000e0043c2c41c081d0700d140442c01c0e404082282108001540405a40b10000054203941851140e0340c0c0000081c14160401d5100d569041c20804160803203002ca980104054403603513400100080e18801510003002c3c0c0714100c0d2640c50b00d81c0306214450041580000000e8100341c081200c1e00310208004a9405052802100f181e000301050100c80d80010040704ca80c4846142c034404029040d50082c818000e40d920f051070310b0300101000d60b1b0080a2100034000410321442c544041d000c10400040050780700d14117 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 655940251 1250 655939001 655939021
    0x50a03020a1e02030c01034208151f050301020d0501061404050a03060b030a0b0f0a060b03090c040c0207151805060c1c02161d070302180613030204050c03 68
    0x1507820302c44484044428001d000d664000307203014a110003820000388482c1840c4140f06a2501210760080303020034651001549416002405802a2001c5e0f51034080346c1c40f10151503d80a114401d02511180e1001084881c45086442c01c403403a0344442c0044143e6a4201090070380e0401601d03541002d41d950300400a954114621040c0f00c44070740c060381c1c9042e003000c00140d00d0000500000d4a22903a40b40802d801c1c0d2420000756000642003480c085591910400d16200b20300116444a4121304209001582064aa054038060710b01c08024000e1031980d0028800140f48001000c002c600c5003600c00100440d00d90303600c00146140d40c0c2c0e288103407424510644c01c40c03400c80e0301581c001d6008100384507030701d1408034810100d406050012801c0746040358040b0303d00484260344001c04201400002040f0700c02c16416140c90114a003c1451907446050950484c080c811131440320400030b480004092804900403e00d5040e03581e00790b2080c9440347c010400f21407003124081c04017100081442000e403c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 655941501 1250 655940251 655940273
    0x60a0312051c0c0207032411180108010e040f0c1a0405032109060c100507050909090f030a0f090e041119030c1211191d0402061b0703050a03020a 64
    0xc407202d42480541c1c0fa0700d030000e50316030301c500c405081c612408004031090821034201682d16002c0b40c1c024003120809081114890340b21681c203840c4000b400c4201c400c80d50050100b1030488110401c466540c0e03480d0703155061040c400c40c00c1140e60144401000c52850707080440c40d1805444014280e4031581050141031514034034031140ca0000c0a002c0c1001140c400700021609000019101e294903241c006c1c9540e49001c1314030000c0d00300c0c1414081040b0809030b200c4041c03c28080c0480303140104d612a40400f42c0c55200c00e801c2082e1a1b002003020a022078040c80d01d03503a044082d8030700095001e954810b40100c8004c183c0c2c04985640101807501c02601d040100003208507024503400310320b141340d0381d5001e41e814001d101d400c80d02d491001005060001d480b084030b81c00440604190400147d1060120700304401e4050b0040b40030b0b17a050b4800102c4403010303c01d84140d0740507107244d02c1c2c416160030041036540384100da24820710410b8008000a501400506100b81c4240c0050903042ca441c5000c010b010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 655942751 1250 655941501 655941547
    0x304020619030b0f2b03090b120402041119260f041a01140f0f130605030609070308090613081509060a050c070605070e3001180b060a031205 62
    0x5a02e40059004e100c100740071071700003c03c0c00c1341181155203442c40c040d41d420120303a0101300e01d03010109205011440410a01d44030360301c22101000710b840d000c4503000340e5000e0320041c1c0100b1001703180c000c00d41a003d5500884c0d80c202c01401c8040600f1605101d00c244002110a5402c05660f5010300080008160300070071031190034a02045a036050000c08980140d455121a21400030404001c01d6900c0320120100c06401c041c000030041406030504001070811481142e01074810744000551000011452005030390344140481e00d02101c84003041001e0700040e400303810f42c481c0e0100002d040b81c0c0400106900c1502d000f09041e151130b180205505040d0001d08005415007408100104a00c0e44012100b0359544a1800030f841d4983d106c040b01c60070200510290044a05280401c14941041640c104040f5410a0884100c0300c002010f0a8032500f0f0244510749240c125500005999400c0080c0d102c10068540c04015a4a488100c92520134251400100b40c00203114034078103586000e061010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 655944001 1250 655942751 655942759
    0x603030c050f031219090c080a02030f060c0913060806190c1707050d1b09090e0309010509090c0c150105010314010302130b12070f06091a030c0304020619030b0f 71
    0x30074420301804e4844030043ca001c07042d8040b8880600c00003041da01a010164105402101e29078941d109265980b010480c241d200e44913007000c0d20050503001418610503011140070741e08000405040c400760344681c042c40c01d403080c1c03174040c0458869020803403d44920716404600121015036150041150300010b05481045003c51200c480001303120817641e007055140c40d11341c2c0e6030980b5400002c014903143c08901c80900900c02c041045541c0000e5030741c1980c0301c1c00400c129035010b190040ba5244540859180465018031000e092427a181002941c4a13107d22001c2e441c2400c1049400e00701080500c40c15030074001c880042c4000e50f45403041c2c42400c922843c5250040d41550009074045c003280785229041078441d0be8003c40354592070070040d482a05141101d14607922556209880784c13141c054400010f030811400544408e80c4500c0c40c045440c07541d2864038607102c030800e100310b42d0700c009c2c42030360042d404100410701d5501d1440044603a60490782c000418042001c04c00060041e04002c9603c0f03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 655945251 1250 655944001 655944007
    0x100303180501050307121b0503090f0106050907030c27030b0105030c010e04020d0b0a090624050f031e1f122d02030307030e030c0109032a090603030c050f03 69
    0x5241d0f0040201d030380046403414140700c03407a900c04c4c0c1c50740a01100c1801d504840c0c0f2207039403518a0354101020394081d00008050303600190300e50716450301f20780540c4a450b0f030201000740400d007601d002c1c1c1c1c01036207410514505070860311188040140491315101d00d011540056003401c00910140618450152000324003408400742200f000826515109845501c503550000300000d1068440e0701208180c030f8003828802d0065911000113008050a01c0f840300c1a464407510000650807041d420100d125117901c2e45410901c2034121100c3c5508002d003c0030622000025040284c4441c10580e8440c00100d004400f6120080c9071051403c04c240e0301c825071801c0400d20803000070304028203480c080981c00c0d401c42e40d110500008211142140b2101035050b0000003155800e140d48980050003131070313041c0c1c1141c414114660044a84001c90320018203c1c0504001841d0090390b80700d00362120004a003d203065081e00d60301c4260841c2c0c41544200c01048004442c10204141803002c00414412140a941 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 655946501 1250 655945251 655945259
    0x7050904110a0f141b06040c06030506180a06230f01030b1c0602120420060301060c080d09061b02060a0b0d0308091006060f3e030c0610030318 63
    0x30400100030f0002080c02004141d43c805802e10a05441c8804c035642d10072980003003000301e581d45494003074800740d5111803040c0c0081804c84c0240580740c02900301500c4982c0c2c1054441d00c00942d080d01900d4002e071307581c480c500001d80d00c203e40410303103401c07101140b1603550702c0160307040014000108a6840c10306043c10000705441d541c2c007545401302107044cc4044061061454503100034400e418003034100381d80c4003080c4000d0103507101c1c0310000080800120521180045c1c00c12100d40024841d203c0000d240681260011f1080005407111842062000c01c903e02076a035002d040d80d0610341d10003210000c1044050038176504112050b0000711141042001007100700c00725040e80314080014081c00040c2001c145400c004200c000c002c294001810000745864160080001801c4d03140c4130300080300e20100c41c490040da499840c10500716402880281d071b00c18003034802c040e014541c15290b07d010511083d6010042841a1445112031141c4808054210301e0043d001d2aa840c5001c000c500d84844240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 655947751 1250 655946501 655946507
    0x10c151416021515010c020607081e030405030d0e160611010c05030c07170d11180103181b0b0f031b07050304030b04080c0102070b04020918120705011407050904110a 73
    0x207800c49400500494584004001650141d46c81c02c802500800005207203018400100f0151481d107c10b403031000025040400544024082030341c01814a401c1085088440e10480e40715808111000d0140c0e03900712a01c1441e22000d180550061001c54004000714403014021301c12083c02070b00c00c0c140f071420760820302c81c9001e50340280c107402400780110107000e1f0b8403110b04409550720b4554900f401c0c0401401c12156203810341240c0c030b06903224506041c85000541c0240940c5001c000841400c0c40c490b6600d0325501d8881078440001c5210508466001c030710707800140000c10b030061031420402e80d03e0801d1004901220784038000b100c0142c0701400b9840028002000f140c045940240c103d841c1c80c1c0707071800d00b0030103403003004101c04c050b40c40014001c04201c020020b0502c9140211142601999a60050848044029240b13403031900a202c1e0a00400580c074081e10310740c1d001c1c41c0002022401a070400d20200c10075120100401c030007040100e06131805009040300c4031028145e503810494a41005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 655949001 1250 655947751 655947793
    0x120a0e0a1a2a040e060906090406200f0403050c0111070303051312030806030606040b06070b0a0f1401080c0402180402070f0b011e0e010f0302010c15141602 69
    0x20010301c180d444003141141c088501404042d6581d5604680c40c94094090092a544203101d00c0303540b1a0500d00145007854042d80076842813030041d0900030700360384903078030300c0000e02c4078009060600c00b1a06403982c0b142c48500c054400342c2440145280d6036403d500303213141b400402d104001d0401c00030007040c05981790042406411254107040c215111158248044404103803500301d642d240d01c11261600515500c403510703c0c0190000d505664440d15030300d0600c1300b0348002c0480f8903044502040f035440043d0b96161003d51040c2c01800004a408404010300c040e100c1140c1421b1080011744014081c44405000c185140c080407a802c44c030b0540d440c10b9000c603951410450074030403035010500c0c2092100040907260400d901048491866031299450f8150640e500040d1750100007103000803c10185100ca858161070107020022405891503004680c030402034003040f1504240c4840b20581c1030003e020f10001b0200c00c0300e10314214507051040c00a00302d00e900c41c10086502500ba001281c80d800c400c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 655950251 1250 655949001 655949033
    0x70b0702180403020705190e071818020928080d0804060e0309090c04060e010309080409200703020a02120303150f01030e1002040306060e330303120a0e0a 68
    0x101d00700c0e0707559080503801c0c04040c0c2c1c050303900555115040c0410300c24400c81441a42c844050112182c0c4480d0000c8903840041142e0700f40c2403440b100207122003100d01403048020080d600000d0f06c0d117002c99020801e803100d0482062044556030580d004c2801c00c82424201504d0070f14000c10001280410003420881c020f40064001c0741d840b803041c5440c031818800c80d8102100640b036603180d41499121182194032511800e40064410307184c00010b58400d00541e0300d126040091320b802d05040600c200011702c2e8060040800c01000c0503412582068440a00b00303a5010b03030003030644410140140a40035800d01100516500108100708a82c09040b26140b0400320a4444041d241c1c03580005070028000c500703130303034000d4030883c00b19080140c403e800078010b0343e100314420700489a0b1291515034110003038495950b002004000110204107058517840c40c130107401815010180444086400c40e484042c6a80d06034800004001000045028206c540382000008000f102c1d160303200c00390302d01a40c02c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 655951501 1250 655950251 655950289
    0x80a05100503240115090530150106050412080921060105030c2205040305090409231c030209010c06021c0e0601140409060b1210060801050601050304120c05031605070b0702 76
    0x1401c200555141c0441080c823842280000458220400c1d240d90788411200c41c103c0504400340020034181c2c42081a07804803414105d500242400569962a00c2e82003070801580110b03541000702445032600512026001c0d4203400703044154100002e045c14034a0740d440700b6020b2288040f41c2001c010090080c0c00d0710030000400040d06440d103103000c0764184103004840350b005081c00c1c51081440300d540b0500c5414100b0360b0000c01a82d81c0c0f5460301740c40310001509003035444201c0102c211514029001814503070f40502d0117030b1184105030745150880e0042041c4c400108040380c00c00b113141507240314040c40b81d244400100355a61414850f08480100007001314060707603c801c520300c20080c50740c0119140c00801000520345203203240c07a1550b07403034403c41001e943c1818410000348a140c18495503000c2c11040c2c3d1a181303180e03907948807020303019400003080042182280010b808100c0c248060a04907201076156103035445c0038100b40346005000e80007a00c42c0c0504010890050f607640e50841382108184d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 655952751 1250 655951501 655951519
    0xc0c0f0712020f0d0c180b03010504031b050313060e090603010b0f06090a0909050609121315050c1501080c010e030d140f04080604060f0b01080a051005032401150905 73
    0x8008180d4a42a520000b0941c40d810b0001180e00c410741d08a03190210524503003000100c7c2c4400c101402c3e901c00748ca01030045440300c3d81e2000c1001c45c12001c05a218002c2e4200e034a05101c0e212200d104070041c0c0d001400055507101030001d103290180103281c0040044000780405c0410000281070401c604c420320f0320991000980311455180d54182c0c02c01440281000c102c407104904040c1d40321074044400060900622a814624031004d0094a2082c11a01c0c040460b00f810700c0044000c15040d181440240722080c4000704020508004841e4801c50020200c001ca5240c02007a5181000a0300380340c0c1481400c2c10440e140b61030018800440e90b4440c0392026109040e1880720b035013803007140354111864000080c01b0600e924006040c6000310712a031010412210902d0325103044689111800e4001607640010030640b01050b040329401c00d5030550b260380384650704d600292519816242c0c03500b0415482540c880c0c078172018810a401011610550030080e6030791500108036180074001d252250401e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 655954001 1250 655952751 655952779
    0x1061206050411220b040504231003050d090e0f0612160302010e0f01080f0903160f0b070305090a0807050c0a14040b0a230f090c0c0f071202 62
    0x503000580208070203030042246144141c801c030718940c41000044850407150441c0c8210f00411034050007250540802d4a042c5400e100030407001d012060783d0744602104440c8000d40d98104185403e0141d00340c00c945200741451803801d1420103146040103400e005018404210700c0621107403960348140300c907401000c40d40c0d6640000705c00c0b00b03030329140808500c21603000014a02a00f103114082d24000d80701c1055514200301046042d1400c15140d6000401d004007244010000004940d0442480ca083d00d00340940d000660744c400780e00d035a09442c0343d0801d100ca0303000d200d61150020b8010720303d4901403000745000000b0a039204074001c801031030500c1c000380c08814040d041c0300850242c40b0081c0b101200540e20380c1e4117482c924141c2003a51080d450014800d185107440151401100c0c1100a0816100f02c507007178080210f04000d200e0740e0020121201c901c442d42d102c000262058401500d0305440f0384802c14058540040301050385906d43c4154000e0052860f40002e014010350304442200c400d00407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 655955251 1250 655954001 655954037
    0x109030b040f050102040b0a020714100c03030b09071706090402300105160215040b0711010e0105041b06030b010527040e010209010314040c030813030b0a06061d090106 74
    0xa544054040c4d440414007041c10180341c00140840c0c42140d085485d01b94943c091414002a8204a44d034081801410300072040d008400c00580c15000e818001100400d400100340b10901c1200c060300000e164601506911100c3c21a10b0341203101501d01c80311a01d0240e001c1445a84640000021070303241e22490f5210720079045060340102c1d818002800a81010b030206044002c1005151000d0302883e0856060326203030b010644e108640001c03c03c502c50710351074010b540d840c20b0000e6a41265407916048100300400b406414041c501c5680110030850042002d100880e55540001d42014200344458005a80c40415610314a410503400c031400c0c8000c1c0d503160034050a054100790020f08107110400581010350203400303440000c0e00e05001200d642c6100d140f10b0141228003d02d411302400d4144040750191000d0f00001c0e04031203140b400c80380c0301d845090b4038000444441b00700380c1d2680011b001a952100c0c25036142a580130360030110111003c0021200c3d05e0502036001080756403000140080b0b6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 655956501 1250 655955251 655955273
    0x8041a0c07050d1d031c031a030118020f121b01120c0207090c050a02060a020c070b030f010f0501050427180821060109090902030115080c1008060109030b04 69
    0x1500c4403c60380042c1c08040c0181450042c00200c84040c5003e07004511107082c04a18000301100c0701852640b1400d5090b401e400510750412030002d181c030014001062901d0901c1480e40480c2d110a20b080c005415204000ca528202000d0701e000d0103140701074413802400040c10040e545081c41103d1102c050250048800418500c4118810750401c500f060f0015004905442501d040d0b070002c2c498041c848105039524404e280c090303c01a4040030010300071101c10b82c003903d030b20000041640d09050741c070000c040d03640d00299003d0143d01c0d1200010802ca10700500706200501003801c1040c2002d2800c4030800701c800a09040740074400d90321120403000c04507940200c00c41c2410301d100c04d50265450a0440154005007512902c001c0c0080c200f100e407a080c601e04901c500816911000b40f80e0800070707000043c100c0c20101300e03059901e4044183c0d05d181d031014440054038405004000700004a001c11400e005208506000d2001001c00d1140d5a680014464142e9030004581c1506071101d1501401840d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 655957751 1250 655956501 655956503
    0x50f090d15020703140a0e0f031e071715150d06050c0703031a0a1214100b0f0114180102030405180702060f06010c060c05091005090301060608041a0c07 67
    0x40c0c1c4414000c00103011580c040e0040c24020b81c0c5412900502c11220441442001d41a401280c80d8618405441c5441100d00b502918082c0c00e42d001815440f038101246c40c0314014884481d04406421710000d81111414242d0f81c0509006107900c8901840060381403202420741501c0064150323910390b81761604001a040964001d000f04003901d011142da1209400c103060440000e4140001e051000500450710448080000c05801e0703500c0c0750a8201ca8504868a03080754040c8400c01c6e920b0542038144401481c00d0000030300883c0702c445410812900003011a00751f4144030740000c00301d007282e2460090f6601c868450030111074082d50800140c3c5140200d81c046075010400d00c90181c28006103000c00d078082e105a4084550f10340b00c50030910303141c0c3c800311034440c00200404a80400324009402210050300d0300c0c184070703142404000200f407101c2c02e00079a0001003000091070602e42d003800d204000003060680391540d401d003801e0b83c1c0c642c410341c030507043c042000003090040f9011079a0901185c18031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 655959001 1250 655957751 655957763
    0x1062709020708160308010f051206010b071e0506011d1003031d0402042907050c04090c05091807060e13020c01020f160210030e0c040e0c280501030606050f090d 71
    0x1c0b42e007510707000701b001009004070281d408601000049605080c0b100510346103c070304c0035040c0b680c2048908039040d000178030191005a400c04c2c0900451305da503000b0411040c0140094944c81d81441d140041110340060445580b80382c00c420024880c0d6802141403d40b90700d450903403c070001d0140c211222504d4070604941c8288000380c0000c84550ba0580f0700c212140d2070041589611800c40c250702e0381e0141d420042e00c0e9800c6003140003c0b03890a03034400b00300540302c1d0300204002601d0782c001c540780b0078040ba200051008074103402c1c900e01100308542c600030552032030204051007400000c038840051800c4410040c0d90040794a491040082d0103403040320342250712250f1a10101c0e00c95490701c1544a80c1039009a180c010200c845c02d129001d26410519584000c1c100c81140a0a11004001c580c4415100b070207003240341000d41d900d5510486911201c0a41c0300c515210505100c111240e01c2e034011414540707071640401686800c40150781e0100307004140d0039214040740c40031600700c03c03401c0001000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 655960251 1250 655959001 655959037
    0x2030c01120e16030512130e0a090602031e160f031a101d010212070b151003020a081503060f0a0207080a08010303080a14061002030c0a03020601062709020708 70
    0x341403c01d00c2024202ca0080342240c1003070400149140f424464001d0801041400d0402488450000941181c00c10701245000662550715224102281c00c1541e900c2c01d07000c00031240c8010780d0700d8126003540000e0004503040403030f004094050040c254080c2d00a05240d15110080c0c0301e0000904292100c0d080640101262100220018080b521210801c9640300940541c030f0280d510020b1001c0d809014030740f009191245641310a490701c0001030040740b481918001100c05921883c18000e44501ca64901584640c4480009040e0040051000140b0b1440d0b004035062560009504c581241c00d0404648051f1100c82280740a80329090001e000620300065401e02c21398000d8805040b41d00070780e103003801900e031030440d0405d4940c1091080c4403c61800041a8140b609000e0b01004d84400d004403032501c5a10340f1818102000d074501500982c01c400010411180c004401c0844d0034031640c01c10305901c40f00700034002c03901d255010b404070441e80411040108141c490031918078541982980341 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 655961501 1250 655960251 655960273
    0x12020a051c4a160b13091a0301060603060f12050d0809070b120703110c1e0c150a26070305040c170d030b01020d05091c150203010305160302030c01120e 67
    0x42c1e81c4030411200e41884141c1100043c0310148031302a00c2c1e82280190880341454030304071404000d0000300c001001d04034a81a101c0880307a40c2481a0780007060191404641a071400740703c0450125a40d120302c19012441080500041010911143c512110705080c000c50312404681032500f0b410390000e2080000020309a1840444c144010744591095a070500c0061408107003907a280c01540321003c6d40d9070081e000c0c0d0f84031041d012861108a1410000c490070122428005030201d0a00d50712441030001c0050041070590744140032101d54054008038402c01070141040e56010701009100d2010140d4660129080044045800300148410b0710b2826500e41078030307211034440070061062004289445d62003145540085065030704098a52510b41c109400c820921500100c001d00d0303003801c440c107001c06100040c4550300448004030350030742c0143ca9606520301a40352031200d201140704c107516200b08200607a0009a11795910800b882c00c441c01c4031038081c05001504003603407652414010b140100c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 655962751 1250 655961501 655961503
    0xc12021308031b100b03030706091106070321020306010c0b151e19050102120306030106030501090b09070b07080f0a1e0e03070f0b0a080712020a051c4a 67
    0x90009107180f81a140301d0b010b95102082200c07496541640c03d40c009120740f802094007a80951042401046903c00b800800030010309240d0200e1070441c081052007000314281e03c01450108660b40c81300b4811843d50a0500002c1c0016060600040c40c144803d00083c0c02984001d102d81000d04000c0c1c0b00c00c140320350350743c01036201c0d825480c00140510b150041e00400ea0f500c041d003a50032240183c014010b01228001c200741c60340d20007495290590749480000000500902c64005080d000d14150a0741d03003001516541440007a50000e504000180b0045010131400c2d011150907010105020b0341d9040a901c0a980100324104005801200c2d641171800305038110300402e0480404030103079201c0b80d4603401072541c0260715024200110000340100d944950041206940104143c2403000c420800301c1e0403c130990703005102c140300044011908400e0003030141d810100d0902c406c9000e10007403c04040f004807404494640360b003140c0b50143c2d200f1707401413080d0240d4030309541c0c074801c80c00d041d548520071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 655964001 1250 655962751 655962787
    0x307030f0636110904060203010f0b041412011d010c02211b030d0c120b011b02040c0905040e060105010e090f0f041716150c1202130803 60
    0x5031001070501880141520440709071801c02d540c202503402004031442005072074202119000c0f2203010514030000307034035a21541150311852040e4400340c0e0320b44c100340041d83d02c1d01083e8050007242c40d091105206560003204400380800c0c041e1000c00400c00418003031405440080740e8509074030402c610000d440710040d044100741082a8007190f014080b2520006030340c0030003242d0311060784010302040405014010a4030551110041180d0511504002c3c9004031040b4a0108001c40c003180901d8541d52800e0245003001100cd0804400c05a00e003403210500307143c140b00007442941c3c1d80c140c41d40710300e00070809580544000390040082d4002d0b440c100760795000078042c01d80844d2095182e200c0070315151103010301c507181048644196849007010f4404901c03015104031010384040c0c043c408010201c00c0680b41c9810501c4e0102980700c0745040c260b0b00080000781d50200d06080208207000250000c0018807604402d140059a90007039a1003d030886021360802c04c0c5a01000451084c01c8855100c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 655965251 1250 655964001 655964003
    0x160f03030c0504060c0b0a0e0609010501051c0f150e070b0d0501270f09020d0f23071403070f0605120109021306030b0a0806100e09151f03020307030f 66
    0x108000a031610001942d00740150b109440c00100c1c490080f000041000c20059004034505030b01062121070341c0382031070030107170103c403c0b8000743e5466004114031729041000c0c4d0005001c000c0c441c0a100416190381448110140700542580c0c61820080301000c20355108000c00725224090b507411680b0303114910855489400f0842c0c0284c1080008030341d4642c19070b035909a260b43c001010103590420941040600000e080c1ca14072182d4035201131001d1b0712510921000c144c8921640c6521000503e401001c0703a1031603c13004105140154814051a4009800c4040d280b04200c1c1c01000c00f01e400000380303005100d800100b80c0c0591400001600e50300130028001c4030f020903090254903a00c4445850480c0507400e05001d05480d44401002801d001340c0c840000b500d4058400c50360540c03260300051810105560328801004191410440ca440481105400c8038070407016040501411242849513500940501c00b2002c200b002c0896101c01d000b1504000c40e80502540d5141c1c0c1d80c3e0605a426450741c980c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 655966501 1250 655965251 655965257
    0x24240d1b0e010b0d1a0a06080712050f190b060901030e0a150b100f17070e030105070525020d021c050601060e1e01120f020c07031101020708070b160305160f03 70
    0x15143d914220175128a1080784050701e19086a0300d0000d04882044c0c018281c1c3d000c0c030403000c0c2d80c00510200c5014152080c0c0a01340c021019050603a140c01341408150142c0249506d88090349800388d40c6d2400700c5481000903e80400e443c00c650f4886401c0000c480d07002030800342c5c211a40c8044240356000b041034508104e4244072102940310080d6000d980c2c144101c8002100c10001042c00b044420040350004041d02e41a108820b030400428211042941c0c140c01154003c602c001724181000382002c40002d414442a580c1c0301c266003c1100460980350003407041200c1030851007600c550b50139003448107400c41e046543c2942e546034040d00c44020f14441c0e03405910204141000e40c1c06c0d107120401f5451060795114114094019050001e241d00c0d460410b01135000c20021821640402c000302c0514002c1e00c580f03440d420700000191030000c10742e0010000e03402111040280041c0607095030722002018055010585103482c040b1440d114421800c800111441d40c1c100c18858882d0b18500790703d00c251 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 655967751 1250 655966501 655966511
    0xb030c01050a0206040813030609140c0a14090604020f030112030e0901180b010201020d02071a130201080c0708071703040c08010509030703030b0324240d1b0e010b0d 73
    0x140045a15100b420041c501503440b08000c40c00151041c8001c0005036944900500c40300d8a0f60303100c4050b20903400d4261104038641d0290362000f074050049101580c82100d5007000f051619a03900c0c82c2050400700700e84203103424800180541c032181c0444091182a4100310307500d40c2c644109450401d8030761070580010303102c500c21003500e082181085041c0c84900d001b8014010b01d200d40000a00901c4e03094904554082c08503000300400750000d00946031040044c868240001c01c15404000401400543d072800c40740c042c2400f60341c20030000c80e008040700c41010781c0c1c0ca0444c1060303201442443c800030b12a5014004480000c203524024500230b42c4107649a03a0041c4c0d03290b1007503007a03d5081d110762000e42c01c1000b1142c0028000c0e8010a23203507102070180c5030b2241c101410a9a1606460b02848669020b8420007038246e0082c0e15001084001c18203040d0458400004111941c1030301c0b40040080350503625078607203005a40d00b800001e086030018410b0315a158680c160300e0307400800d140d0230720394102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 655969001 1250 655967751 655967773
    0x60b06030c1c140f100b0315040f0b010f05070c0317120f07091502120f0301081c022a030615040e010608030702061c020a0201090b0c1216020c0d060b03 67
    0x24021005441210840d8a40f0b03900d51030100c1d1403182c40581920020144c20100184aa40d680c014510602c040394810300c19804140501096400b4040141462458105a0240c40c2c1e005040f19400014625001d80c07514100d14096111400941000d00000001100160f00301c02c89002084460042c4062245689071618048042e641c1654030300c0104401c28000c0c07000f5400c0b1068150511070500c101e48034943e03898401d442079406004506000e0000200500070040c0412840d2b86c41ea000d8084503a58100e4003000940f00c103070019444540d000c4405002502554248504408000040641b845400c120076030300082c0080a8000d4040c0307081060300140c5201c10311030f40c0c04560000c400303940fa0038082e80c01c01119178840d084060384500ca945500f640104144003409906540d40c000140314405030402d007018100c001c1c105084840200301001c80b40c004001c400e0740220248440141030102001e059080039090b0010580008403c503000c0180b0541d900b014146d8403003a810360f4050001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 655970251 1250 655969001 655969057
    0x60f1d0603060c0904090b10061803080a0305100806070807180302150306010203070516030b0f070c030e03010608030f0d0609060509151c030507030e09071704060b06030c 75
    0x4200e60580c0d140c0c2009001a00b14501d00004003100c2100a02c0010416100c1e03940c2005c2c1001512200707140340f000e050a00103a50000e02039070003890445030180c5464515680e8000760b10840f8840010151a000880c520422040e20301c000f40683c0f0050703a60318502404000d0892000315590000280340c154003000c885500c0d012801641c0d000341c5046074000840312011056480900214118030041005001082080c020420003002d0820240101455402d0414000030040d18511244282202380b1800035005601c0501942d81030606500f0f00c00304034002270041c0103a0f407000d002800000f070750921240d80080107002d240c03c4402c2c10010b130741d29208a071003102e03000d000341c54110f148200810890721200011449614009100300b02c0b4080303010350764149009401086010400104905081581201800041000c10b0300c1c140040d01e40008001c05103905002c0704036030104401c0c04181032003a19041811030180103018250790703080c0502d2540043d40542c01310010000d0855403441c02d220 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 655971501 1250 655970251 655970309
    0x80d0506060f041a07050303010e0411010203090117040302011b0e0a090506180a0632030a03120221070f0908060c040506180d0501020415051204060b01050c01060f 72
    0x704040c15541894202213480c1c900041e14009003420326424808100000c40c1000118080d021400e4843c2c424145031800001e01c00b0640e0361107065420038040442c040c0d0340514030800c40a0000c000507034544550808ae401002c1450000b110724441c03034080aa071075081040d00c04001000d88084001d1582e9065420480307c080e90035940c8031b04050700e07281c81184100700481d000745e2242c00000b04203039103240c202c4c0807000c0300d030348200740510302001e001400b2448040c0d0340300100d042d0050449130050395130080441d840d03249e884070501c0d808183d6050b016901c00014224141180c1242c1450070021400703403d80c0d80b814405800035240000c0460a880081007803406070740c3c0c4510f000d040504001c2088695044005420201c00d0303880c65201140c4d0712460404c4125014800041e82d0b507007042c0c400e0425000040c000d105000c01000b0350207404211100c425401504920001014000031004039200d10400c00407a5030796080910104091314104040d001710788100c00c84a8202c0c803031002c000e43c00d00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 655972751 1250 655971501 655971517
    0x1e0d02090a0e0628061422020a020703020103230718090e071707080325150504021903020121060503030310060207060807050a0309081c0f1103060a1e12080d050606 72
    0x6c08500c4450390b441c100101903a215082c80c803880b28019004661003c22604072000a800507440400c1c1007096503094070030441302c4000c001420740070403020b00d0100c8814601908520800c042d4181c820311a241282c40c03a40030f4082c500c03051060303102c079200c4981d4030b40f02030161016100000c50310728602540041c00904403221140070310705080da0f210b50560628030018949801d50b4000600c3c1000031030003409042464141c1a002a480c06c007401840400100070609903030380c08011006201507a0001c042054990704140401c900b29104500000a480c0c50390100c1e1301484080180301500a07801040401d070f40e0340d86d0131204c505554080c100c1d01d804083d5501c10100d54104500a02948217800c000320b0310f0b01600c1d60924050300a9401c460f4504241100d0200d29a102102c5503407170041e01901c00c60000703058203103007181014000110343e10303002e20558400316042c461036080d960b411002c000c0200381400c00400c140c1450f040c0003215902601011080ca840c040c002841031603c50141d94030302d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 655974001 1250 655972751 655972769
    0xc121e0a02061315051303020d02010203070512093a0e0603040312140c1201120b01170a0501050f2502030a050f0919051e0d02090a0e062806 62
    0x2da207442d0100b52040c116200c0c140d03844002480080344649542c020320340101c1540c010805801d41606000341041c1c06da07451242107900420a11244507401016101d40b902402594025500c0303001101d450201324010401000c080750040c0140e0b518403080e46140c040d102910611054601441240c90100300c101c0c00d54024414000300380481d20404810302100c0055400148511b02161030180001c8111440022990006611581d008111030403500500c078240303140d198840b82e46c2c1c55135007e900c14018685507a241ca4860140c3d207008210240409410074001c009a040048018003a281c048916503142440280c20f80c1201c505001c2c1120f03140b08035070141d42060a840422241d1360320030b00d6040307100c460030701060500d0354803031806981348060f01e4001d290343e41c5401e05000c00a400b611a400318003080003010003058031103007140244039504a40000d507030380e5405200c030000d000c5030000407601d109100803c65695090040c55032a4800d040c130f5034414280b040c003c03a040d80e401e0301620081e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 655975251 1250 655974001 655974013
    0x601050a0e0712060b0901030e07050901060e03030415030603140607020d080711070e0f060a08030f1c09200f0d0b071b0b011e12030806060c121e0a02 66
    0x40c1e00c20005840e04220345181086503280c900888400b40c50b01900050800040000c8011083d80c0500c034005040c40180c015000c640d150900180300c0c2e07041440b0714010f0100f41503181426542c00c2c0200d4000d4034000c1c205030b4008404840003001410240411159101441c0243c140340f180000c00718480c90b0b0700d074010024a03001d0b407170032907440c400a4000020700010035440d0307510500c1801150007810303403d95a02560b00c0d10130818100c11101820450081100d400d0a00810402108172010071407161110340c0d86008400010b104090396091071440c0a10b000079810421141d002040560840c1c0044440180e4082c0c00f0050400144a41646d001072000c22140004440ca4812540300c1c0941c00d0048940c0e40000c3c0c42000996000d000b00c034100740c1d0100600090421501c04880d130300c4036010700c000d51418600401e203640000c00c0d0150a1041540001d0340390b9880200700c0700c45220a800b80d1302e5254060000c0d515a411120500403606419107001c01c1c0d0704546000c0d500c0e00d4940d507000b401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 655976501 1250 655975251 655975259
    0x15050c210304200303161203050403120c05090913120e010516050307050609060f070f12021605030c03090f2e0e04021207020c09090c040e01020403170403140601050a 73
    0x44294115160f01c0f82403900c500440b09540600203080f5081480c150140d0300501807401000341800d6001070740505141070103001c0460703405140380b13202507001c00000841075000e29040e1418050300c8001d07540f00026074200702e00320a00c0703012068054460040c0ca44411a5064151403080d02c0307503e0140003e1083c0b01c244080c1903151486240940a0301c05c0c2c2c1c0c900252a1142804c000003111540c0450384a08240450100c507502143d9125209107450a0f42c0b01401e2001050f9001c2c03001c05191140c1c001c600110350f510300c90080c3c104281d000d000c40c0c0d07440400c01d1005490b900110a500c0c460301d0b4212180340f660800145200401801c0d04a00091114200e01441d004d80d60b100038000704100b0407100411a03c1e580700400140c420a100d551091034503c10080c905004642c13254015001102070202e81e4400180e040003030f4204940c0803521503480c10050340240103503800a04135009807000c0048070083e0307030020000e0317074040e8802d1410850b81d150280d03513400082c864a600040c0c0184100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 655977751 1250 655976501 655976513
    0x60901061a1308100b031212060d020315091c030902030a020904170d050a0b04090c2d0f170a0b01140f03010213090b010e0102060f0a020415050c210304 67
    0x4030205070b0402d114600c003621140a1032038080f20081a20300a40d503650302c08a14641040101c1c01c1d81c11032000107240062001041036564030103003206010703120740c0182000b15035062002e4040810315060b04449031800c040103985d02c040c100b01641c89203600b100c1c2c0035070380d501c64041c1180b0190041c00929481442e030f800e02803c1000140181d031411421751807400c45850480050000305000300c1c0201c0e1030300304403a00c60101e0303021101442c482d0f0703d071101c11070001c2c417005280c6040b42c1024800d000651041081032107100041d002407080c2140950011511100c03010042040c1c0380403442c1d5160b40c5c90040622070b41d450031641d001c4e241c010701c04010468103403100201d0300303d0070300900240544075005020900b60307000802d0704441c06580b40010b0004020380e110f1442884400d1800c030002d40c600e0340010352202c80c0605070040c0c84000d900007440b850410f804890040884030707202e0300546c01ca140d008080ea0026607480d5440d000d11211225444004002200c0000100140a2554441d981d0340d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 655979001 1250 655977751 655977757
    0x5030a021005090904030e090c1213020307120f0605100b030a020c160e04150b060901050f090a1725060f02010b030f160b28111905060901061a 63
    0x7100c10440c00304100310041d00c071240864000c0d40b10340c0315000c0c8090300e0001c105107250002c2c6110081ba03010b00003191241144482242c200080f03003002040c2c0c034528004a81007100c0c82d0081e225130648440c0850801042c1e520b000a0135002e200b003040075484170382d03a0b8601c002c03032886003000020041c070101710624135071380c02440f003c00680c0c2102c0c420000a12000000d002681c072189100040004100c180903000342d10121451208900b0419020702100241d0b2034081d24003034604000d40403450241030001801211000c840052894009564602e02e03607903100707441c0c14140702d180140c02e4910407070080c0c03416020100c548529510645400d0a60844820301108060000c564a808044442d61014803280050244a101030881e1441000f503004403000d541d4002c84040750100414060001180c000c0e07851581070000c5c2d040d0b541013a2004603100610b6819810720b43c001c00b00c04000d445412030f500d0780b219100c0e01c2510300556079201d1241c00c071940c40c400c4100700072500703075800c1c3e8036401e032002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 655980251 1250 655979001 655979029
    0x30a0e13050903190c0203060a0c080730090c08030a0207060e0901030618230106050612061903051507080a0b011d0103020c01060f090612030914041122090605030a02 73
    0x441d422000303251b000246800825121140704a54a81c0e0450001742c2c0b040b815980a030860500c403000060000c5003880405803c1d01ca90305a034008400d1211070107440e044120515080f1020b42d0100d600d544d825a140d0788443c1100c4c001d07128840000032114040c070050000c9010042070803400b6865038503030302d01070719440c96140210f500501160000805e000d0070420070b50701200c091184a600140717803c2c01c58105402a81c0328640600212400324800f0b00141c0c2d004400b1f032004142c2005503002040e0b0281070b5007005100e401214000c607040b000f8152003070710864040e030307400c034050300d401c22542c0c211000c0400e4140001c125510070301410b0303107100f0070031100003041c5001490240a8008c0b02d003180c185400030012032549a80401c658200750146034080e00c0d900010020181c03030b41c0c0c1c4c0940496068400c801b00b8080700d4280c0b80c2283c0e2503900c80c812070411090740b10390b0b48410b009580c0c0346102038045090b6022402c8400b00343c8604074803903e0284c90002d0010800030403107408120b0304d01c400000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 655981501 1250 655980251 655980257
    0xc02240a180605100503071d190b03030c0303060109170a0314090d060626031b0304150507060f0c0c020906030a120206041a150607060608030a0e1305090319 69
    0x98090009000f40f0446101c1c0781300786030b003010460804003010b04010722030b8449899191035100c85c2040803210002107401400d903901d520680e83e500403021000e0030403149103e03814000400c0800e4101b90110086115690981c1e61850701a121103004003440c0d50880c0998a65000341c4c0c64000083c06a10445100244698014104a001000a9000400c0400072120240c850000b00503810414401d0001c0301510f541d5500040f048a051035030300d02401c0400d010500c0f010444040416080c400c90b009070000c01c08a00c01c0da0904070b009059a8001c0c68201d13070107440c1540295401c2a68480e01d01e40500c242d80d400c5583c00030340c08020002ea0058003044d0f0501441e82800d0010b1220010001c8a48164003e00000c2c5401e00f0003181090088140200440c1d510080152454406500d1140d102d02120210303240e022a04212008100716048031809100000d07001c10342d1a0015a0040c0d10b0504072540084034909081d0b41c01600c0007a1002c02407903105001c011600044111921381a2a1900d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 655982751 1250 655981501 655981541
    0xd05150408180420072402040e0a050403020a0f0c0b030708160c0b0105010c020604080102030103050a051b21010213091b030218010e03160909060b010305191a030609010c02240a 78
    0x100d1044821444106d04841299001504106220101143d00d50101c40d215040100d4501a1006521007029540c010048520143c00000b08600001880042c00410041503141d10b00004080d03c401401da4900014018450040851500c54181010060b6004407140d90700d918060055403440742050040b41d1003c401c0c440840d00c83d800344042d60003103014000400c0f0141550600c1810801c003000c8444110607000100d98031074031002c0f9600110348001d144403101c98078902e0014020301491290701d925100051002500715001d0f041111150030111007001242004030007a0100c0c13084a0b240c5400401c118074038401580a1140c10620b4603010b03007500d020014003115022500015008014000c0e42c8440c008180301c0f0610038031f40c5801003030030100001c0c109406004000000100d60010a580780c49008217102500f221412202c00c001c0d0444400b4102000c0b031030b0181c0038a0118400503c508254202c0b400071020f2007060358581c1880d0300c40035803038004002c1c0142c80d00042502c0d90050074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 655984001 1250 655982751 655982783
    0x90d0e06070813030b130f020d080705060a05010f1e0e07020c03060c0a140c0c0415120b061e0105030c0f04051005030f0a06080c0d0515040818042007 66
    0x403078003e0408030b074040014030100b13003585082d082a100c05001d11000c005103041c51400205001c1c602010150100d4010400075000c0c5051a054461440010f0aa0046000340420070307219400481c1603403141aa10203440b501c2d01c1c80150501d80010a544400e81c0c0e00000f08490b00d0003e807800c2c0c2008143c03065800459600010910b0310b481502c1c1100b010702c0021b02030040e00d9014a202001a20b182d1040c1d01d880c80b9448a5981c13114801d10480c07285a845008180c503112000fa444014942032444540c0100c2d14204890401700803a60a4001c4060700f03034855070300c550012045e1000b107050711241d0640d22045125503503500711400b01c142100c41000302091b03640e030703054065044603040d9a486607245000d00804290300300203003034400c0040c18a0814480c6442c00301d01810394943c155118802d00e20103080c900d150100510b605400e0100c940203200c00c2c88100401004103000f00803003030022092000920044580306e5405030021980c0320b904010011036840184860f90141003810301d50511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 655985251 1250 655984001 655984013
    0x402060d0e0d030b1806210f0703140a1703040c0902042601090b240904060c080708090d050706020904050a021b0703110f0d050d081509090d0e0607 65
    0x54020211207075485421000ba54a41c103011300d0380c010009441e200c05040524122400340e160142102d8403a410010b14469100309181c02000d07600c1a0004840b08942000d180b161240b0382da000c01d558400c0000f5240c04905c8001441c030681700e61008041d0b10032840e840c49042250005001252a86015070002400550900140c0081c003d002520b10380741840680314017000c0c0b840740002115074140000e120200740300c4030900b07500440644903010f0b4540512825074008202022241c2c2c00381d00f5900380170034401c1c1a4030660101759503845403d44ca0302c400c0f0095a06500844003495980d0000c030809103502d10079006460407501c40d000240c1010b084000103419500e0480741407003803660100710380a44003222102c9129a040400161140382d0039600e840d4202240c40c00894001c82c018581c219294441c0b228000f1640e4120f41510141c010481000304500303002c0e0381d030002200c03141e0032070030140c900b00c041d040c000c904c400e0007410040c50030407003640c54086040c0c0c1c503640080140302c0d160105030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 655986501 1250 655985251 655985261
    0x50313080c090106081612090516033e06090d050a020108010609050f04090503070b04031107060318030e0f0a030320030a050414030a0204020d0b03010c03020906120402060d 76
    0x301640c090895018a50248100140140c2c000d80401c01d01c03400348074240d80d82203035200c08604e080c9000d6086641c0140100050282060010598812020703401030140b00140110140d0707205007950303002e054151040c5840c84900390300c07100107600180f420382000301182d420000b01e2207024120710706240b4000c000607080070001c01e080c0d596400ca0490882150303400605103003d45134906003c0c440c2790901c4e02143e0314942518115015950b00c5860205000081050710100c50f803184121000e0702e003615006207184142d15030a40c040c07207954000f2865602038010ba45035540050103102d0780741519101102c03030180500050360004d581c0099018a40c890122150185001c1d480e03c410400e10068030b15546186400d9094440c1c000740301e8400c010764000100c5080740c410641544510071503c0010f4204461642c000f03611510000c0d000c6007060194101c8510400224002c0094080440301501a40b14248500381d028104110911040161642c2c0d103400c640054901b0307083c4900950704000310f07070f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 655987751 1250 655986501 655986509
    0x602010905150106020726030309030c150705030a20181212091201060f0303120513020a18060b07080301170c01080703020a0e100908070b03090d030207050313 70
    0x80d44603904034090140400a455031480003503014400c2d58900301000303490f0141406030320304101905c481c0070700000742d582002c0030140b50f00c01501d5603802c0c540b0703105503203900854612046004040e54840000c070100d030154414009a21458030719500c8000210050122200849120040d40a142e481040109c050490440700010303040d00c00ca0a802000045102e1071240000c0368095441045034986840070384008820644401045001960741c9602420700e5401913a12829000c80020505034001282d090300e5200080811181d10340304109900d02e011044007030b411031079803c8204a15440c1c1120011980b40d103c40002d5015161451500554844d10302a0396008010006004852483d0f100310840120f0710300400f000013000002800c0c11074002e0148003410750101d9800a4140035481103030b10b54200401400207010300010190910074103000790a030f6032280c11808599118500c08681c0a000c2d41002446402e419a10032000f0b540301640844941c00180018100c0754803a0300020060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 655989001 1250 655987751 655987753
    0x2060705031e1005120601031a0702101503030f0e0102060601111504111207060c08031302030d0804060b0604060c0b0709030c03060905013806090a0f080c01020d021b04090803010602 80
    0x10fa00e04020040460b501d0551226250082401040060685140e82c40704041c0c840d010031107642c0300b44090741070194a82200c641e80d8140401c018681041c000c0c61419244240c403801b0442034004402c44155903a00b4070070340587e0120f40810700da98011640d0301d003801da0704800c0b185580040c424501580d12f080e281240d1a8290013a009041d2400004410304002c68000500030286000c4c0c0041100b18401c034050140f200c004003117001c050f02c45200300003c0da0044d00321008600c203c1c40040014901702c6040d00ca55247c900d034207440d40b4011048034101d580c00d07a0342c4000008507440d05055210098003920070301800c09400800644100e49003030065001d80d03000510320419080c42425180c0000c10f40054101c4040491128200701e09a44e0104205c12a001880c419200c0070580612030100c4143d4400c2036440d000404d04000c141c0402950550015114200d10260040e0f03610303010b00140f5005a0411030b030007041b0350011008800c455100070404202a0555101c0d21182d5100b03130400001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 655990251 1250 655989001 655989031
    0x1d310c0e030f030c030d150f24030b0a09020d0e011803090605030106090306050907051201020403020f0f28210201020114060918010b06040905070f0c0302060705031e 73
    0x103945000d00012410018110207945811910000c3d15220700c10300303d908449964072003401502008401f00380014000da0400081c0945e110200014001145010004001042c4005003001c0d403080c0201100140c001e015400005c1c1040e0300e28010b07401c40840c10000030781e149101d104000c3e0074014011215100300305035034220614100244940c1071a04101d040c008200010010103500403d40d0048941081c0001540e0721342e08032150810143d40c0c0a160711105105031000c0c40310041d0300810840b4401c03108840c7d111940e0040c8201d800ea802e0703095500a2854403483d01065004854802440c0c1100c00203848544486c00d090400070401040c01e0622001c1041c0d800315602482240114824030b04010142d2234282c0008559a50040030303441c04441c403d01e078209084094000c2300120000901131500d841d120843c020013400c0c201c4420000454040c101400c640c010168200d210b601603020b45082e660300c0000f030312941c0c0040e025104548555030b0001c08600c03400a014045d00f0b00340311000b6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 655991501 1250 655990251 655990277
    0x5180315101503020c030a03020c0a0614150d020612071e02070e0f06030a120903060914150408071b0b1813020c1b040209130207031d310c 61
    0x402d00642d00c07142018144100840c011550001080d100707050310b980307009641d5080340900b00c0c0c104100a64024030f4207060001020351608104052440754040d010000c0484a445040007143c010746040650402d20070000240d4072a101070a02d91301500030b05180700c484d840072400001c405e86600c005801038024660a00109402e1500316401c460080d6118250f4100000002e0710360b24454802001620750340343c19540503005883c010025600108100007000180c20f0241d21802020801c903441d004e1341c4030711442d080c0010482406260000c401d2410720f1865507036450500c40c02c41d80700540d02010140054401402c1d8001e2003070651041709420140c4104040c416a8904c215282586034014070032400e079050000388100c0c0c0041a1040c96403495415404100244501094103401400c40c00c0c1c880c0140c620382c0c00409455210f40d5444800e10100001a0702800d500b8220952041000900d151800480c0030360883c1015884440c60035803199512050483d4441054a00420011b100e10b01e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 655992751 1250 655991501 655991519
    0x60a0501060e01080a0f0b1e03010e0111040e070207180e0c030d140325170c070b04151e0606090f0e0609070c05061311040605010518031510 62
    0x16004103114100b160314800c40c0000a01641801424007546599406280000b42c0b059080711102c0203024010550300300c403040303c40020707014503480a4020743c00c0500180c18010140710f00301200b582e010b41141003038249800d500020801418140841c401e03035038041101c01030024010122000f0780c1000072020050482c82d0300f0007034040c0c00742c0d100e500701c070801c0140c0c1c0c0c0e00403640301d030300b41441082544c4c0d9589042e0110400d51403410b80d4404404001c40b0200f2071038110f10392030301440d009002400d09039609060718003c0d10501d1002440d000c000303000704000440d5a90304105051005002141c0900601c146032003040c42c0045044045440300010030665800ca410310010f41a1814040401410400c0796071011402401c8030740190200800203a100744a4103818204541c02410782d0105c0c209126000d01c0301450441c240c840000212040c0c040b4a860702c1000100e0780103031500c4c1e08104002040d210a078481c0c071904c9400d400341c615201d82c40e024174045507100b204502070b4a0b44c22030500e0414 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 655994001 1250 655992751 655992761
    0x402031311010e01080c21070203071b03080904090203103e03070c02030304030c0b040603050109020c060f07051b0d0f0804050a080a0309080d0b01030b0105040f120609050609060a 79
    0x2082c10701206404221059901110300d99000c001400442c0da24214094a08441c44805d031641d001d1a01010500600d070b9404001000628090000358009149103200c5007a10209440010300004040241031514142a005044583e0005060314001011501c1c0c850940e010a011901101c10f400c4400b003038403008030030280c0500041724824074040301c0140000c2d11840003038030100c18005280244002c5603000c0048030091580194a607540e00d54828103080326404c94041c000119080500220340180d051095841d1880e90b14014030480c0c980301c030fa444c443c0d800030b1b2190040002c104007545101d120f45c40264a60042500280706070b1443c8c0800400411540d100311007000703103403018840402c000290391503669400605003030b0f03212100d8605800401c00c680c3c00a0103a000860fa40490540030350105c0703c901000c0c0c90900609403805c0044580d8480c5004850346c008000d4420f01ca500d455900c0a15a40e10410000030400c00c82d032241450100115403280c5903622030002c01c01640382a02913 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 655995251 1250 655994001 655994033
    0x905191203171e010b0306060906070803090d0c02030d110111040303090302180c0304080f070c030f020312031909060204090e07230609090703060e09030d140105010806150904020313 80
    0x3a4500f004180718040205041c10301c180c0c4c02500010000c17030041e6a072102140c015030002041c2c42d650382c02c9460041c240d41c0046680070428018491902e0003240514008100c20b40d004000d8011910081415101d00c0204445030030785641c0c0d81e0101a0400c140320080002d175000342c4510200f20b18610402c64080c01021402d03100c107202d81c062001801c0303083d0940b60000d5000320305945440a613001010315003d400400b405c003200e680e00010501c4000b900c15010540254282e44003ca1228200401c500c02038a2150401030007040304070040c82e441c1d1000301030510a10700546055a1081d00300182ca07503403060b0840c0c54000b02000c1140c016550030200261003c80d41100d002c0c2001c41c00180103000c0d40e00f806014070320100c000381d0104e00c2640144060b00000d8801e04090418106e0956260000300110501030316081100d058840c80040060407180c0594030444150780318014020303070450300070f240d0b141c2850a000340c40f519a0b440c0081c1d4407900303240720302070110240790402c1505043c007000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 655996501 1250 655995251 655995271
    0x2010e0f071208030705070807111008040305190e0d140d02070302030c0f01050c0105010305060a1103090706050a11030c0a02040f0510060806030c04020c0102030f070f090519120317 80
    0x4010085512488002051143c0150405480c1c1d51190002e0b90f01e4403500c00001d2420380d001660702e0400401001440403500c00755000c041510502c10169501041610042d0200f4000d00c42c003400701200c80b0f1100c0f40c4408030308d000200c5c112408045408029941d0f0704443c1e20449001c1c10315a0303103040110100c0030b14180b00030400e0910f55000300f42c8441890710154081c00140f00502310990041003211401206080204040e40e52401d080d40c4500e01030756442e04d100d0070030b00c001e0f1078040d400080d80c0c01002d15101a0081c1071070b003038090302e0301d503c1100d0000503c50111000c8401c1c1c6000c2c03004e0920404806e000d8540314180e8410030080f01c82681014010f2440c002c1402070741d0b92034100d1b0703405440c03183c01c04001d00d488290000e442c00511140c1700e60b0043c000101001c3c8040190051400b64608455251040d00e907560140c80f10380013200030600280c4612010401480c100c0d0411580b0340340004003208258443d0b1350700d102d4245041c0280c0102d2400701004440025030802c0320b034000d00c094 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 655997751 1250 655996501 655996513
    0x206060303030f0f07091d0115030e060105120c030f0a11040911010c0201020309060403050a0c05040203222102150a150302190b270307031109070e0a0602010e0f 71
    0xa0005203e100c040d081e03032002c10f002800100038a01070303244a8060009594101c0342d5441c1c0400d101a01d24090060214800021181c60420390003402000109410480500300c0b0f603080006011400034203c800c007049104a610359562600c1c14090001032400d004040c01c0e0310410703400d00c440710345000e4001900aa241c10b483c3c1e80812503125908140c10403d2030608038854031800103c2c13842c021004015070007440090008204000000c0c0318080c140319a04401d50030341d0320700410040b404121800401c0710000030030000b480c91240d200705c1c8694070481e00100200d00546003103007425855102c800c0568010440550032405018400350f01503d00c03a401d00107003170020301402c85120b9070300c4000e02420745140c503011004030404604001e0300078400795a40b941c100da0501c0c030306242e0410388800c400003074140700c10b107904003c2598403ea0b80c02144c0c20900811410502c4180e01c0000c0041040103d190703003036030a5a6440c11000020140c5900200b02900e05039035460030200188103400007a8058 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 655999001 1250 655997751 655997761
    0xc100506061602010e010e0301060f080f0307020a030f08070f0308190c0e01050f04090c0306031a06030a02060d1506051c0e0604030807051b101a0a181e0c020606030303 74
    0x2031441040b4990a00c1c203040c080300c0f904c0040e1142d0340d0300310712030b035141d402c2410109011000b41500300441d00719504070b5180000b0440c21644a00c11290041d400000c0d8000c00c0c0040f846400411489520a040480c501030154980c02080c4030680003c41c002800b03170381444400d9030300501c03c110110380a18104581a60000041d12990300c00450302e06120000c50504a080d00d184180d80080040c403406005092a2000c010018005408122822410340074440041c402c550007940c840d0340003400401d1511820780070071000c0e0304281da07100c0010303803210f10000900700d034103403400d00401c010385680b900d43da030b41034a40d298800d00980034030359140f07000303e031080c881c03030000b94035401035050304280109480d60380c070496840c42164031500c0c0c1088000e68928900e44006540c5000034110380042040030300c0c200f5440150608200c40a03400803201d2400d2005016004810701c040e8070800e00050307100d0902e01303a82840c5034203612044480c0c0c0d48507485903485d501070280030760018045018503c0c40c40c00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 656000251 1250 655999001 655999027
    0x906061e0311030c060706060806070807140304020a05190303080115021504050c0904080a020d0e01051c1e05010e160f0f02160b0315060a050403080f0f0c10050606 72
    0x551001910014160038000b0103503c1c10701040f500b0340400381120f6a1020300303061210141003140304080592040340001900b6911642d0000e00604072560360081c403511407210042d140d040540141da004003250360002d42a43e514028000d07000300c2026801d1005c3c51414080d2401005070310403603003030706003800c0c201e40c1683c003240d1b00f5214240391b00c194105407194288103141c14184000c4917000000103040c0300a02c00300d00c01605540c41c0c207a003100c0d00310038085130464424143d100a140484d40c00e01804441140403801221580d008000018011340c1c0042c9a000c000d122400c02c9003590350f1100144030004091001c00d503c8411200e80403590300d40305400a0001d804070300e0030340c100900c0c00c2115011920134400150100f0503000c00d01c02c2103444a000d00711950003582c00304040b0b00c415080c4440c50a084058a128110545606040c940355480792409540304541c410022801080700d42d9070642e200d0003420408808000412098450408580c2124409401c45211b117000380400c0d00e00d0b104d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 656001501 1250 656000251 656000309
    0x30f0c011506111f060308071a090118290109090c050603010e011208070206031e0604111c140c12010f0e060d0317070f030606050403051506130c03090606 68
    0x251134030181c0050001c01410b000074901500002c0981c0e00000b178100602c00c901c02c0111341183d0030840c002090b1100c020203400c0740c403004194055191021010380c0440c01607030629203e0310030300c119170089819940d41e00f036224509070800112590364003c1c080c1401940e02620000d42003c0c0c1d249844c5504000b8410aa44014440c81c01606030902d2468104130030341c1d0903a050540c0c0a0091901d0b8103000080241c868004e91010300c1c10112800015024a0319011340020200718068852800d540781844030010f890042402140c01e840d02e884420400413086c04501c25581b0024880d110a10780c20780308448041a8065503a19860100910840b0f0584140641184e41258080040700c0c442c41c1c1503842c51a41c4030352401a00300c81c0e081004050700900341640d1610305540400081341c49039000c0d952030140c1c0c0005069544a003d6081c036447c00d070500c4941005008101400010001c00600e0507281d0300c040110001c0d464598000420100d40260005000800e9010014400340b0803182c02c8a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 656002751 1250 656001501 656001523
    0x8180604150c0c0f0302010b0f190b0a020f120702120631060c0801030605012c07020a080c010c0f1d01030c26060f090c070b0702030f0c01150611 64
    0x80d40d118035280102e4015a88800299448180c1c9607014141d400c000e0300034121206000c0c0105140384283d986803814406c10b1464608800f4041011801c025030840241c104c00c0c2c07010194031031250310141c0c840c3c007000454104180c44085503074940c91841849a100d4039808403003242c2d0f0040007809442280c5c3c0a1340c1e02602d1a40241c2c4030f1064020b0005400310401000241480b0724010800320320030b6020754064183e03030091005100c1d990741c600c4424161502011013410184114501d50395040007108000d400c0301e564411a903024220303481c2e00e5110f03030140000c00c0f210383d9075042081c400c0b5002003540b420101207041c00c040206860031092480040a10309604050b682c20b402200c00e401044110f00103c42c5454044011030320a03490603a0f10342c00ea071007612441e00b206884000d4949220068410b5090b10450750906d00743e0307517a41005410240c21082540004e10400c40d081c00040054001601340314008103440c00441081e01007299a90044010405400750600106200056190400e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 656004001 1250 656002751 656002793
    0xa030f2708010c0215040f150509030a0905121002030a09020a0b0c010e07061407050114090a05010605060721110d090e0723090a0f0605190c0f0b0a02071208180604 72
    0x41101c07440e00c0b48c00e00b804010075244052601c400d00138000e0700080606030313801c203e8407501e0300079894034100007810821464191559108240d40521482c0c1d0350007031a08041e0203003000c619400d140d40064144025500003d140580100b01021841000d00402142c0d4000c0300c082d00e0343c10b050440083c04140000c80c1c00c281110005110b00401800350300403045d1800710007140c00e090629809a90720351400020a071038035030074100080b907945464003c44858070350200d4030b403015407820304448404d02a140e1603a014072840003040e6071240c400b80954a100b040983e030341e0400701d0516456107a500b0000c0c3c94402041006c0b500e94602c028440c007541a480c2204003c545c4070400381002881d500156000000504004200028050340010241c002d00c03030664034500021081c440111800440d04801400100000d040e66000c1900300c4075142d0000d03000000946010100d407548600006103609a20001d00d5840c10840a150541d60203110444040003800190801e504c94207900040010034160b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 656005251 1250 656004001 656004023
    0x2040504050a0c0326030610200d05090a061110050a060f0902032205030a030c03020403061a0901060c032c1203040905060406080a030f2708010c021504 67
    0x6100d0304200340c0d0540e82c1d0000d038001201e0340300c1c0780a102209402e24000e140c0c0c8205080c9100582184051b03c0c403c260107440001d0b107402c000011038108040540141f4202011018002002010b00078803620048a4031500d0f614004403041c003032030105070382c0010f0412800610000091030701003010080503002c4d02c40400d40303441d0390344070760024812075010f11b4075400d51400002d000c41080d006584503c03040c1010041c2c0a030591170220005002c0d40d00180f07560001c0001440f818026408121000003503e001400c1603242d41d038400488142200908410a024012110758a88003001901502091405105000c41650050844626003540300d003401056262040c11804040c8800d1104100400304e03031501c0b200d00803c3c2e8032640140100c0d60a21b04ac000020590b08082c00307018103ca0268000349441422030710122004504c80705640e0800c54002745580b00f1710345901c601540324400341d130003500413454040140d00319444030104c903095401480d20740c508200382c0040c895103c0c1e003021080c0c0c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 656006501 1250 656005251 656005253
    0xf1d070c060236040c08010b030a1518200f03060f180405120703120506030a0606170601121220030415020d14030105040f0f020a02010209090a06050102030702040504 73
    0x1a00401201c0091a04010440a4440700f103111520315400e5141ea03540c502c0c0c558105000c00e564440e41c048000c00c50311001085250001170085501008688002444480070401181174180c43d502410040c10444440b110348d409601c12960042402c000d502c5030b074080b40035801c107503004d07c200700d41e105035003c400651542c61300c8013803180d141c0e00100003584285111004030781e20302c0196801c1c0c40c5445044000e0192045032004ca482164040c0c4440d205140344021100191078000e0107580c00d8020050084006445401075801034101020030384e40b50003903941e540740307424030582c02440100d907060000c2000c41c00070140140020120301d00301589041d07500000d0041c0303190780315000c282c0c03200190002d040040851041d160b54074a80c20f88500e111009411075001050204850124034100010444c2e0300d020f03071202ca415034280704080361314007015180c0402c1b608202c503401c0260750002490000b41c03500d8409039a2040a64908210352410032000035a68000e120000307004607507a8003c14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 656007751 1250 656006501 656006513
    0x50a150203090a270506010e0f04090b0a06150507080a0513120503130e0628050d060f050c0a0905040c03060801091a0604060815100b0a02070f1d070c 66
    0x82d002c000080c0000d4101c41d61000c08481001c1500724400136100004070041100e95540280f5015440c144c1d65580115884810450040d0085207543d501903559407a060008101d5181103122b00020240080c00601e00322a01d4803030780486106000f000300411038070300010a50001da481c01201031400940322904140c0441e0499420703000310700d250aa075018001000307000402000341010900ca8402d0b42d60390303089004806801030b90311a070b028004040b4a8494000f5050074012044410080001c0581d1840440e02c0d04404240c2507501d562a4152650b070308460b401141d8001d1011000c1900d85881c036800142042c5090080512540d10342215885051090304100e018004c0d1000170031120301c00c1d2403c0c100a05800c1c4407200403004510008107031f80340922840044a14070000f41503006c00c0c152201e600c000c0c005011200102440002250240011010f4051001190000c02d001c6061000000007005503a00060044810549000c1c010320007505041e0008841d090a501041a0349088 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 656009001 1250 656007751 656007757
    0x3120311030a0e071a031b0f0f030603070f0303020d0e030106032003060105190e04021302040e040507080a0c09020309100e0703030e0402030717090a02030105010e011e050a150203 79
    0x4151504404800d0000b4050654005007030042d560049550003550341410781c0400c11001d518071002d0b0030a10001d4180035601c034203219100b2203450003e02d46032207100810320030b402401c1c01c0314840c00080200302041c03c04000003400313040200c020702e000301d140d076030000e6030b510442903044200603a000ca030004544013508540c001e10341c081c1d00d620707655402d2125004030404400065210344113900c00007445007000b80045200c5407844810900303450415058007400900900200d80000d004c44042c0380000d010300c00780010300401c5a030356800d400e282c201149042080c1d0040400354202001a0b800101001c2d0f141d803c0710420000544c407662401c0740c090420900f40a09c005040c2844400c40714000e001c90071100b0390384a9211000c940c54540103101c100e000031215040480d00e00040448080e94520a05038002e01c0c1c101190f8000249902003800c0d039000f070b401030703a8105507400180105100b001c2c00503210018002241c1101d45010002000809580b1804800003855044c5528141c420320031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 656010251 1250 656009001 656009021
    0x181104180f1a010603050a05070801030302100b011206080303010f0b120703180f0303050a0c090b030f1009111804050411060d02122403070e010302010e0628080702070b04031203 78
    0x110b01c029a501d40d0058094502100c88002807403402e00062001401504807a068a030035a0082c01c41e01030b040080380017031601c400c495040c4410403003003a81c40318550003084003900000b000f41d501ca5141980f50902d036606604031020f51003007400081400000103800c2ca6000d0301c1860046403203c0690180320340400d14000140945112003010014507425400c520b00480c055241000302100e1420304591145c414041c814440c402040810312070702901c408148c01c44c0c108441c002801d65a1503415044810328402c0700303088640410146803070054850f51050504055605215929050343c40745029980302103018030410b4045041c01c3c080c2425815641440c0d001002044103082020785800541681042d235402d4121694402d425420701060303080c22a26036091000b02a400c56006441d481d421004144d0402010701c001070280b20680d200c020800c50382e1524030080001c0b50f0005000d010010203400c1594400e40741081070320b0b86a0300300c0d0f007100d401c010304952021000004074090500245 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 656011501 1250 656010251 656010293
    0x80d17060f041a0114070506041203060803160c0509091c02120c01061e0f0e2a07060b090c070602070f020306070f02070801050c0702100e04181104180f 67
    0x38041c0030030600003c8880103801c0989841d0402110398aa00c4820b2140405c02070039a0004400b00b0f00040308101c500c0c0410926007030200719141c54062462071038100f0300500280c100c1103089042804121800c030340180c00280c440c3d140750f10f4240440b0780e84220f403140444508084002004409109005001240c42e0580466550344014010345000e05014080c01c003285c0001c900c150741c00002000544115004041c0000c0c2d0740c1d103046e00c203c1411900802d42588403000c45200100c00140429070080c140082143d151542e6881c10f110301100d9807043c0c1e44d03000f00644001d201240c5039800aa48003241d00203c05070740d0b0105c600d400c001c42020018004e4051262200b804085900f1001582a01c42c40ba402c90b10715039030310070340d09081c0d48064401d84900c0c18100884800b506040881c1320300000141440841030300d5000105046822892800f902c012465144504001c05071180c041ca903001100c3c107103d504413031801242080ca000d40010010351008100500f040b2400130b5030012454048 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 656012751 1250 656011501 656011511
    0x20040609020f0702010e0f030a0212070506070c180c0206060f0a09090b1806040f0308130b161101150e1e0a0c0912030f051803010203041b080d17060f04 67
    0x41880b008a8014802c1240850001c00058040d801c200000b200d014a00030300800003a6250380922100f01080d002d500c90341d005440c03012485449000007820400d1050b841c080d00e991400400008240120041c1001c0310b06001c0d01d00803907540010007503003008c0e0440c1c000c8807401020001580701c4030f03240c0c4580740031401d04c401e031020320140a140a00c9194400b40009403400304505541e00c64000f29001041d240c1c214035000d01081c4205032003a8003607074400400d1000002d948490000c40c0c01100c0310a9100d403030541d0621129400b001106c0d40e904802d0091009103c0110121200c100c54081c00c03c0710f00c07031440000c80a0f03841c3c01074400f00341201081c11034507041840840c009001c20b40f284202160070058001030880f0000100c02c05d0580698802030764403103450007181d95901503040010000c01303546507003119030350a00c02907014602c01d00b4001444d620340013000a40b1541a4440440b40e08445c0d0f0b03541006421003a607000308030541410681c1a600e64001903420900c2801c5640c11038502 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 656014001 1250 656012751 656012767
    0x30204090602180d080f0702130f0b030c0d03120c030207080f040e060901050904110609040e070e0c0a091a1201030b060f1203090112060b0703020601030b01050301092004060902 78
    0x40d4000c101d568400c804480300c615190080c844900c03201c4800900017a001c200c00400321005030007411507103100825150445841c54041026a014484c50f80c2c0e0003651a05050b546241c10400d00585440580341840822400c8d200030304040c2c1a82802280291a19011203074144298102d03051150301c03c020340d448024284007481650414092040f8520b2101c01103021441c03ca201d150407294000c1031140d0540d2180e0f210034659005400003a00b094090080c5102c5039924000c41c8000342c41c2d64028052145440c0c0345500b080d6001c0d20b128030042e0308218040e02c3c59404402e0b0002c1d00d05200440d55684030003078941c642171260200c400301c0601c030a80007004111100c000030780290802c4410f807140c00402c84c2000420240095142c48c0d540c4104800007039035000e1401100f0074aa841000655035903904900ca000d640051021001a045040180300300410000c000d80540020340003000490f03510340e24080c550005409196490400b038008400c5540c80750003050203894401c0c1c041d0744502079 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 656015251 1250 656014001 656014013
    0xe0912040b0c070914160309080d0b0f040b0a0b1c1409100605010824030f0109051005090307080c1f0b0a06080c040911040b0a0f08010b0901120f0603020409 69
    0xb00d496010242d000c1c44000040d046140e000c0d03180540c8070941045031030745030302400c01e0803a40f540c83c0d00c00c14103460318007031385c04580060050841c1d504010b00214041d4100c0c4104001804440c903690710841c6401e07a005c0f07090b110841030b03005444101c02c41c6a0346036040341d0400960b20741030380603814250030719403800d61b003103131035400d841c0070b804079200301c40000880d0032848054403482c1c01124005000b8030300050702d80c2d0070201180c140509401454807210003000110303080c050360072071750700300b1341e4680211a080100801c481008103842ca80d0421503802c08070411501c174810220098000340b0041a0602c3c010000c1c030800040300100006c403411150f01740c0740036002d40000043e6500c0b4110540000a2040c0140340080c4103e0306020308c9840c280c10b0007040001060214907003c01410b051001203035400883c3c000b01944400c1d525002e0340886002c400511843d0f050b08013101060090005000ca40d030003e098480c03807480e00b5404101d42c0080010000207100700e500103980135007000002024400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 656016501 1250 656015251 656015257
    0x1501030f0b0601020109050606010e060c0a0b060a0f03030906030209040e340506040314070b1201090c141b0c1003020315060a021c030b280e100e0912040b 68
    0x44101c1003029966500070040e03003216a14640582150441d000003040c546c0b0503040900c00c2c0c42c008260905001d80185524a841d080c110201d410f843d5103018041c203450000c0d11000105100d0555400042c02d540e001440d6801a12410f4241764021a001145035190b81003020402034003411074680d00038000f100141c048294840a0071030182032078043c80c40c401c0380102c200761100540814a094035550380c504940708040f100c4d00c041d0240e00004148403070075000400b015151444520003650403e16040304075035000000b401031200d54407016036843d00c10030075a010483c0d5865a50320314120b0f0344429003050080e45031603a02c0003482102c5240c9607007641c0554041c032805908100c000c110482403001c1d5215141c20400580c7c8508080031a414015141305907282291601050361007912006c00c59491125101c000010150506410800301c412210401419102d078a0b4800d4107294941391400d00c0540a940311015140d400241894000c005480748804407191640e5031365507030f541d650a0340d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 656017751 1250 656016501 656016503
    0xa0b0904060b0909011512080c15040c2108070501060807062d020a0f050c0604061d090c0405100201060302060f0c0d050309030301090209030a0c060509030d030515040902031501030f 80
    0x468400c0108413114414810028109480241d8038000c0b070a04c84030b42c6c0c070081c8141d1304075401d0004006050f8044020b10031b840405039619001c2695041614125826403801d4211072a6440c409540742e40c19242d01c07400ca0143c07600550070603524030703c03424441e01410700c6c1d4000590912a080002800c681c0c003100106030481c0004100d800445611a000c070003ca80c482030307a0040e0f10010313512002c6690b000220101a103e02c5c1215814003503c000f143d010b800c030368009008500305031a0540e9000405000d10442003044808201a2801880301105800741d40110342c0211400180024104c0c006d5000c0000f4640041c100b0340c5840030221001c83c15030050610380700c7d901130000c018034880d0003482a01d01480b038007400b17541141e08000314100250090851503074103200d003444140204104840d84001307046261340341c40d40c9802400900d40343c1803004000354209840c3c2802c004403468894903208400904403000301e003181e254000039280030304502d04207402c100700b42c000104000185079507601217 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 656019001 1250 656017751 656017759
    0x60c120306010e04020711040e030c010612061a031b010e040207080d0e06070c020f01090e070305040501050601050c190303200403020301060b070f0209090f0a052a010909050a0b0904060b 82
    0x50101c4009004c20303402003a000800c6e5940760021000302d0b10703164000d65218207480e01164280500160740c9825286035601c42400d1440030030684083c032005001c0e0920b02000144c0205001000c3c80110340e88044103401b00f280001070901d8844a684600616402d580000300195120700b42c900344580c10b5841640003102003858020000324581001c50110301c03c546507110b52400d940280c00307010401551381d88a50400035038800100302100105070302409100140d0740064145058a4070908542001d8a0541804000d101c0501e0120001440c1e49074803403a12003e00f03804080c0c1c6819000303844400d5160081c0c0800201011300c5503000c00160003140c2c0210024860700d0b0340d41c4940c081d14840c0d6040a07200c0c41e91030340715901509008880d540c10003207403002c842d40c0031800e900d9641005c2c0000411142a00495003540b4400054aa410400b0001d24000e2005502d580c00180c03482da02c0e80b00f000c1c03849407503500240010030217910440a446002e080c2514918161410318014070480c44c00c2c03482 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 656020251 1250 656019001 656019017
    0x302071e090c03060614090303042606180717010e0a08070b0f0c0403230607020102040914060603041e06110408060a09020604060c0f06090f15050f011202060c12030601 74
    0xb41c1440b0340183c408030360094541940100c0c9118003500c2c1c5038005840c580d0144810000010b04014950b06401d0b031104841c5040b6480041440780c0f07007404009006080041d008001a0300200b1001c101c5070201c1da0b80c60b20950803000300744205809404142c0c500302903400342428000c03d12449400610003d803150390818a0340d0768030b04024001c601c0595903003190220a120a04c0010040007a19a80307115030042000f030f010042c1092807400c64111081f00050350049000c020f480341c640110405104d41010180441c607110b008154103000040c03001d00f03107406038050164000c8c1c40740c88140d1543d0700514203010800e600c103541c4085900c640b061844071b01c42d1038009400c5246501c54021a6a8020f10003440c25181c64012100000090f05c180e95000c850b80c0c45400080e002c4c815400d50608c1041520341c941410f0a120b651202420152000c4a007031030100000100e00d4510181517540b04500c5003440300c0c4a00215086000c0d00c68072a00704d2244000740040120b201c3c024501c200300036620018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 656021501 1250 656020251 656020271
    0xd12050a030b0a15120c0503070509180703061401030504020907030c0c1a040311010c1205092440080c030309061008070302010e060702010513030c1509030506040b040302071e09 78
    0x204aa501b4903180000403420300100300120710480003800c0101c0700a10958052100418006003080240d502c400800d907074800c200310841c6242c81c1d080700d42c1001d003000c1015140c00e0300070400701e0394001c00c54010140d9803040c80903503034002c0a0f4000c1054006420101c2c3c500b1a00038854401e500b61002e40c0030038a0011601303401d00b4140170315418010281e035140b8100d40003103401c0018040140544526005480240c40e11000c45611424003c61811004180b42824100030940c3c000c0a084500003080386003082411041203101a02c00c4e010101154080e05150704040c490390040300301c242524000001407104440300042d01c0e030300a100500d12180c4440e980e1030040d95441c2e01b403100a010903a90703425102d135032400e4409841d0850040c10301a291810201c0524000741c0141c000316034016001c2001c0c00462603a0280004c00c030f80900f0549451030450f29229a10540184001d0652640400003020980300380039000082c024002c246400d05109940e041c008a51270182c910301d1454408590 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 656022751 1250 656021501 656021537
    0x30a0b010207090e210d09060f111213060605040c05090108090303190f0e01060b130b040308041203110f01200414090403020a200f0d12050a030b0a15 66
    0x10801d0844e0800070407594403044169000d031007681d40a442503900611202084e42c24034005d844445208803000115048031004020440f80e10f25108084040d041c0425402507211500f040d810a481401d880c1c0688190f2504030042d1a8a4104c540c00c10300304900d0940c1c142e04000a002191002d13203424203150340e02502035503203010889011580d404406e0047c0c0c24648658480300e420344c181384001c10001c41500c00c040c00d40d08994000c4080c10400542c0a5000041d640948040d00d00350f444a480e1610b1030301c801c40d55004038050014490008900c1c8800c00d402046445200740c0c07075405507002c00301d205001c3e41c003c00740c61441c1c3c42c0c2c5284a07080c0200c0808a0412203054420b1610300c404014408011710a4004004100b2070a620039040004081418500d00f8905100541c0060311401e0b2220148041e80d403400301e150303000340d41c0c0b04c1c0a0b100164281811059064071380c5003458030b41406540807000303004038280d0542c00c42c1c80444081903900311410340b50b001d0349041e11407100f0300c0032102d866 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 656024001 1250 656022751 656022761
    0x120a02030a03090806240f010903020a1508090d0e010302090f090f0601030621030807090815160c020307350303040615060e0904060603080a023f0309070b030a0b01020709 75
    0x65510306e9107000c5100014509024000c00c0650189008130001c0e481e0b6001c82c480403140d80101480012006404000d076903c648455840061840075003050303034813010701401c0c90201d05122414160081050f242030303221103e20485d10b010043c4030310b01508181c2d41500e03400c0c20568946000031708007603000c68a070301c103819400072a0414080001414116131400c49451038007a120304100418000006401c20080110340301c41c0005280f090510705251310b0300d4110b18007000d66101840004085030700942d40110351a42120340c00c0d10000b140c3e551844c000701026026200078922000360246088045400101451046116500410103d14450000341c0701d04074600c03a15000640c0c4a0503946942400400c480d0050310844000c65810b440b40d88010640c0c00c0006100c0041e80146000c84403035185c3c1050184200d000d42e04d43c0c202030400350000300b0165800b06821030146002000c40c02c1c0001c20030014004004130400f00c1c0c0c4a04151070f080c0050f0007000342c2c1328014415a9804101d11081d0310031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 656025251 1250 656024001 656024041
    0x10f0e013f0606050328330506091608070201180c030605010905160309110a090911150d02091f0503010e0108030307080612010e0f030403170301060e120a02030a03090806 75
    0x5860301440c2101429402d180301d02d0f41180d0000046010280c12030406000e540301c1c14031440b503811801700e06203007841208c4000b0186489808060180510601110500c1d152032107207281543c000c0c0e5404909030b003d041d00300c2100351a10b01c010505024442e42401741c02c140e80c0b10320002e2002e40d81e210303d18400d550082d503030700306001003190700120031900a03880020711601c500218015459018000340081d07034103501c940c0d0341c0780c1c9604064040110b0403210b034a2003034046480140a0700ba03411040664021a20929070741035000803092415522a52007004500d843d8140e41244e100340754000780a40c00c04c0c4a95050595031400100d004036003c0141c920030340e070582e207055256440781d0800031039013012130400c1d40741c0d541e9000d003e0f000403003808034581c180426801103594038903610308040900c60705880000082020b0005102e62a03000201307204000c4210b0314a10080d0b00c407500345092041864009505106444d40c0c1780030035810a000700110340142050740c01c9a038480f1032005090500a038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 656026501 1250 656025251 656025283
    0xf030e06061f260711151b0c010e0c010f09050f01050703050c0f0c0f0d051b0109081c030605030a260706050906040b010f0e013f06060503 61
    0x80a04240729000e24079500341c0300d0702d03c0c103444240181c8694200640c003909482d241c074030454080052950700402c200704070426100083c29403095090a0010044014083d2011014000c0904051840b59030960300000d000740000c1145541f00f00320641d56421144555000c144100c04c48009940510411422610060a15102e0b2031030200116041d0b8001141142481000c0c810055810402c002d60441c4410001c000d200d091280c104200ba000c81a034940c03803086901143c0000011030115805c000314594401141d600404000180c400d08125005030016104c0c2200461003168600c00c96403c2ca00036440c1000f041d0b1715001416250340e07151f0700180070f401b8449004000b13030400413001d0f9200603d0201881c1044a20f503102d0083d039006850918042c0c0c0f042c8140428021180d8400f0b0050010b0208500354925008100007524014400c280c0582944034044060190721810203a42c03d880100281691400906404098015040c1a1009440c013000441da50800103112080030720812 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 656027751 1250 656026501 656026519
    0x5090403170a0204080d020601050109170a020d031e0e010e0406140922030507020f0d03022509090308090d03150308070501090b0c0304061103040b04032303070f030e0606 75
    0x1840406401c00c040c014054a6508000010b540e4800340615010301c4c0c560340c0905650751400300010503580d5903401801204505c7c161620002d000026024a502d605885070000080c4038142075030768800c9045040c050b810010310587d151640b100e0305484146098945040a11101042c04226076260041e031b000180c480c41d90220f545404040582d00c0043e4101c0420b0000742c503008140302829070181100440c01c0800c00c04210f05e44134601c503121745030607161000c141002c0d84000b50b41e2424031811030031685100070310701c401990142110700a01038420090090f20550b00d002030030b01c601160720481c540078201070015884c0c400c2c05500241200b10301c02c800c0090540c1c075110307404d5003e402e00715400d658500c80b910004051070300355449a0f880d001601e07142c0ca801c0c2401010340f00c10103484d5030806010410003000540300711000d900260140381441d0603120031001c10880000c00009c494007081c0120421100a5201d5914891081e059400340412228180c00681c0c80701d080d030303c843d4072034024 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 656029001 1250 656027751 656027777
    0x906040c061805041d0d0f1d09041203020d0c0504090e06091b04062301110d080408030402130501140a0e100314120c0c04050c0a0c141e0601030c05090403 68
    0x20703802100201399203001000407402d002d8480761901548045207804155102c94100c1000d030040c01c05016929140230f400c04c503042c1000020741d5040028001480c4400d4220030b11079440c440c0c0e043e03500c05611400e04001c1c10300b003024084c0454010784070780340340981485680d403c80c0c1c0380802c101c0d0280c002c020041c94802c0b07a60500717984a4001c87c11190704156102400996084c00710031521340140800c500e00707a00c40c10100010201a030200c420800342d4098642010515030040e03403607a1042c1c2003d0b0713242d200d0b1100d10001d80c800318402400b6150508100011440c03100c0341e101481582012500d051a10b580c90b100e4801c194422949503100080100007080401c1c04007100e0040c2d482c2c8201600d0f8020118851015980c000c0070f1148210b50003401020700340e0031b1510809400540c4500320721b04100b80380074010880101420000e0040101000ca8441e508042100022445001400d540740421001c515a44e481003444203031b0f5101c00c0300900142078100a0080750180ea019038070f4029034008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 656030251 1250 656029001 656029009
    0x90b0111060f13020a170708030a0503011e080303090114130503030c0702010908060f06010207060306050f04110904090308160504050607140a02060f0a03150501050405270906040c061805 82
    0xd000d6142d07007602031008001a45c418100c03d029103000700700c0c031440d1900c0c6040315152401c0b5030407032482688100080c0305110741000030743c3d04445a42c400307966190442a41d4140c52a9103601c1404644008414480c139808190400e078044580e044682d55655140d04a03042a603841200c0946282c00c00c00211360010b07070a1000300744150041c184440700d0760743d8030503071481d0410441e003080441d01010107200c03056070705010407002800b80b46428071030a0300b04000104c1c1c0c5004104010700c180c0d41c07001c0c0c0460300c003041130036141c1419009200300410412400d010b004808211880005a0a01044048110b02030000c0d14103035a0058099424a41566941c004a030340166400045200d132400c04001666010010a14210451031507900c616941d1b40c0601642c0d0891540c90720540c84241c24401641d00100756802c031041242c00ca071003800443c0440c0d0005041864500d6411090010041040030014441d40628032440f82d02700219640c280455055645483d40c000ca0100303440204501d2030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 656031501 1250 656030251 656030281
    0xf06120b031207030305060d030f0c031e020a02010908030a02120f0405030109080d0c08070e0402131206061802040b0f0a051603090512060105090a0e1006030c090b011106 75
    0x459090000350000c00200002e1600c181d030445030b1248800051000d08140d490302415801c50710035528600e4500007a5409440483e40340104420000828140d10616100d1090401c0c4041100d03458200c0446c80d01e802512121a80380507804101500c00005600c00000308941c0d005d9820380c00b40610b100080405003940d48000401900d10400307001c0800ca42d603003071050b41e1502d40324000c01991440c0104a510030b0f01c0c0a030307808a05101540d0708101c400f64011100d008800411180169214441e40e0b0b8014840b0090b081001d110349200724440810490342c0c0a001a544145845804003001c0d80c1c50100742e1250f40a6800c5084092010020b05801c1310090180304055040c441c1c05c0074a03a01440c26185c0d00c0420030740004007010000c114508000d0b4400c225080008081d18040d0f0500e0080b4240345001340c100b20314246d441d40412003100080c050030240d0703400035606101140e40ea0411007403a0945020310048a4035000c10b00350298010806200d080100343c0280c440741d074464126945000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 656032751 1250 656031501 656031527
    0x100506070f0804090606090e060306060909030412230304080703030e01030e030d090b09030a17060a050901032103050402030c090624040e06121902060423030d0203040f06 75
    0x410070710000c000400c80006040038181d0a071000610515010b0000c00c02e00495200d6500a41d11505101c003035140812100d900010030342e441c41070f42d120003228526520507988840000082030b00d00c6400c116090441e6550039034071071a101764281d006034109880344250b00c03d0800903401540e00300002030003030181080c0741c01c050400140e0b054084204609542c0500c5803a41d005640c0c070302213010000426102034200148500642c1460741200000d0726080422450008013204000080c056580703450100000d014007400e0a175042d40d6a103400140780640c01e0005070080605411807039524030a12078030b0300c01c41d001001014401c0b0107105106c40918040c1c015a0040240b03c0c3d0000380c140340c2c040742c068250f002c03c00c2c1c0b50b450f481e02584070441840a8003a51149401410740c030300f144800142414060340c079000c2c3c0340202e0b80030700c0002c0aa20031076010507401c6685042e03006504c4a10003004034440d1055082d20000048101c3c120303100d101e5409450141d02c2c90f400c003808114403c0d2210b540c42d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 656034001 1250 656032751 656032763
    0x1504020109091d0d090518060406050a0e240108070f12050903070b01050d080328050a0b01030c020d080714160f12050c0c04051e010e0106140310050607 67
    0x50b454900e20000c2e0303070160340c44034488007151a1000210504105001c01e010451503d1400740342458005520003070301418183c080b0b000079000c110143c0da998401740090400034190701540307595019140a21400f00c07001d06502c12140a5542c01210450036844030104c141d44c1ca5115603201041595802d90110b1604104000c5021880e1406514800d036030151107844001e40c2c450405142c10024460140c11a070301825182d02c4a000141440081d01c0d04480c00001c40b4a02e46030158142c2001642c2c0700603200e00c94280018050105501e9100c1d10840c00c003a40c003070000240400050fa510075040ba5204000760b17810700010b00c00b0303110782000c1410382c0c0800309861074061406ca1720305003000400000e07200302e041c4008032410800511106130041c1c426040c42800e24001e81c0307100d42c036007410710401400f40d40c4540c0040c00109018601600d488100c0912400c00d5031214010392404000b4000c50303010415001c0056154640320054a2186c0b40c2c11401d0700c5c0c402e042605100081d00000800c44070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 656035251 1250 656034001 656034017
    0xc090e0c070b0403050d0c09050301061d06060901230912010902010c11030c03100213080715031e090606080f03130911040512150109090305030a150909030e120f15040201 75
    0x40301024000da0f8641010b0356500c00c08e440c02c020030103007180c07080d601c843c005100254504110340c181a91443d40403c4c21504151900305603001a9000d0712031111042030a000501c04050307410340c02d0068416000b060b2058000315441250082c22168400740c0640461041500040061344005400480303084c09010b940880400b8804a490f00c00d10050404940740c01058181e40f5441c0304403403800a200ea440140119803a00740071b22840032456090030109501c8440707078400005403103100f6540740c0441208001c1040b0342d050520042000d801040da407401141d00c0140074100000680d00a940c0707258002c100f07545003000c4d49005240509114507200c00a00000801da6100d0301074010000d10381c005401c0240ca00043c03907031414816042410110304d071004d80000319500500303403079001030001d10000380c080011134031400b40a41d980c4044071160031b0200d12000c00d41d2007840c58603410000e0707a030042e07130039641e4900940b00c40580d81c4170001303a400f204c04200141d004402c4542c1040c01810300c028 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 656036501 1250 656035251 656035267
    0x31a0319080f04090912031103040f060b1203070b010b0918090c040e061f031505090f03040611060c0f03071407150c1205160e0406180c090e0c070b040305 68
    0x2001da0030a40c0511a0b4958400f50641070020700e10700c00440d1b000e01d01e010412403000101ea00c503107000c064006030030010000561420800b00390f0080480100042424032940a55001700350703a40c0c00824105c0340764001100002d41b510403001612035a4600410b44410180000f0707940382210401406c034401489213a44000c020b840780c1c42001100108907024000b9440d02d00e0100d0b80b0300380c1c80c1004c00c1d10310254803401c1000c107035a1824240b4000904502189a858111807a481c288666400d440580030019002036001d40082024000350714000036142281d0b100440c51809009041c3c01d0084a07030b00b0070020320303140e20540300e64401800014049003003130300c0750b01d6441c0051503910340f00c903840c0d84d116142c414007a00402d080d03101a41d400420f0026203400502c0fa21000100c8015109001c1f6035000c0d42000d586a421010241000021021064090a4601014000301002c1102041e40e2001c082151442801028403d0300b500d09038600c2c082855440802d4450001d01c02d5007041000c1c05062 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 656037751 1250 656036501 656036527
    0x311010f0f120e01090b1f0e07080601030209010e0a0e1608040f1b0b040306020d05361912081008030f0307200609010b010203070b0115020106030b0106020607031a031908 75
    0x7401241c10b1001d0500e2a894034481f11414070b050713001240185c0703c001c104900303982e002c040d0981c001c00a2070056165083c08005807002007000e1901903010500c8100861000041f0002c90b200e190044040d000c0030141d01d41c00d40358540152405403c0c400504140000300f02180348904d04600c00b03000c1031241f86c0da00d194082c999001500221541600081c8008a506c0c0c83c2c042c103a040310041500300110382c00446901c254410310b80680b000c031500a03aa20403002000d0220000c40320b54015840349030081403070a103820b858140b80030f002140030390002c542c182c01e02840c21026a240701004528002c0815103024494000402da041008103181c102180418600004811803400b0401031a440c02c04191560a4480c5490b03000e0466006000ea000410a15040107045403805e1441201c3c02c2605401207015042e44d4002800302122100002071250707001825034462139082d80c08000f000401001c0f48881c2120060040d410340c40100f402040e030b02110a4942ca20344166213240c0b030030360403130b0841c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 656039001 1250 656037751 656037773
    0x2112070504260705100c060e0c04150312231608040308181c0809041805060f25030b010e1509040f2706150311010f0f120e0109 56
    0x101c1602c00c940c6020041c900000c0100601402084510f54410380b04228003c0101070b0124024204548540c503098000c0b00c1801101c0d003062014106000980f40140a0120700e003080c401203804418000c1c251280e58815440c8480f039005820300881011000400605c954014848050108444440c000c000511410041005500c20341c00c01b81c65900b010002412010780101ca2030042da0940c00444040304074001c15204140c0c082095a1503001400215000700b8403031280c1c001c00d1102c0c01405090100001b50948502c0030a03000c6a90b656625000c1204d01200c291141c0d006070114840e100803500a400805c01200306250206071151100d0000e014868a41b480b0f12019400040a003039a09040c003071220300d01c5810809100325480481d400d01c0c040d035041408078070320703815a12107420068242c120084240440d2005d4800da5100d0801940c2c81c403000503a10301080740c4140041806008102c441d40c280229160f030f140ea00c85801b8110090305a00e0745a20b015583d403031501d00042ca000b484 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 656040251 1250 656039001 656039039
    0x303070518061b16030302031b010603080d05061011100b0d0c0f060201060f030b160c0b16030b1206040210020f120405030c011e05090604080a0f03022112070504 71
    0x140000c0303070f110340c00b4941490a9a010000b1440300c0c1042880803a40000c100c6440030b400340740702280c03100c58004850041980b40c0000b401c0c404009951003179580300d42c008901410701240ca81455544007602901c1928240d15510103503045415401c6800000307600142c070075000a070401c604049a9614035601c055250800708407081010020f103c1c00364244101006000d9105403a9205421515802e1100350b0043c05041174008000448503464490955206103c0e0b214100340740508020307050390740030b044103510100001d103440070000709858541c85a50320340d07130f10310007402154807613800303201520225600000070351103030440480c007881c804c03c8030340005800251803c0c0c0343c3d42040c041506000040d119a4100070014016078011102896910a056814113081d5034440f540000304596019a0740501c0c00c600444144400380070090180304140c1c0e01c258203880c81140002c090400300d085480c0743d014107850a2180c500800e8080f02c025801c030340f46052543c01c10355604a8010b040c141c0442d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 656041501 1250 656040251 656040277
    0xa0f0f0504060e0c011107090e0a05100b030c04090f0b060f180105090c12070305070e1e011713021e0a06050715050f0c0a0309061802130e030307051806 67
    0x480c0506055050080c09410013007403030b043c1040e001e10766410b0754416407802011900c0396954010744900b101000442251544201564100382c01c44111500070940b08c000c0b03d009006d0000b21140e149414810a91103950000020403102d01d00d44800d402d5050080a03103810001d81d80b00314400d9a940000113075540c1c85104038011a41c140014020b440d0310241c001c02c1c1d0701700c0500405020100100482e640540c0d00d16000482d965410000c640d80c00e40040d106d60400380340030902c01311411114000f03980702c0c1c003a25100f100f620000e80500a0200c1160400c0b03194000c85042e0380146800c055060000506a6072051519141c00005001030215807060010a0380024610104602040403002c141103070a0100050326014030343c0b40582c2801004000d100000161005500c2d0182d030009103a50741100e002c02c20940100074502014080700700980c440c030f05280142d008058030f8000c00090001b8000654107545444009032556080703428040c009041004043c07200c0c2d150b060190181150041d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 656042751 1250 656041501 656041511
    0x30080310081905151b030703060501030b1002100f0605030328020307030e09041a01090e151302120304210606123306080109060c05040e0a0f0f050406 66
    0x112503a85070000008003840d8500d0744110798800b0071004613489030713800080c8540c10300315a1041034410b683c3d504056140910000131052150059156018a060f204d080c1c804100038185a010080c0d01d20884200c0c10051703001c407481d207075811866004903200c8841c500d40814003d0301c8600207070940e000040d81200001210344041c0c101c100c014001003e80b40c0f00d00103103250440c5034400034000d81b480b1040600a14030b050100e42002804401d0b0350140804050421041d61104075140182031000801a41403140c440107880660341c010b0170b1170040507043e50380903550015a0a011410307074117200c0b580f80707804140000507100c5000b2641e40c90015207140904102c00031460700704100c60f0303541c208240703a40c86003074403c001030740156200d035101c0551000d9011500c030182060040344004a03102e540b0070f0500c2000525071038150045440c1a1080310144070003101080c0c00c503903074007461050030202843c80c0c1c0445d840340141e0b0701c606440b0503003030b50104802c1c0e05200032400303454099400b15a01030b030f24 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 656044001 1250 656042751 656042759
    0x30a121103300c120c12340e0f040b060705010b15090603040609050705030d0804050d0305060102100c030204030f080310050105030910240f090b040630080310 70
    0xd030b01115a201c4420703592008509215160701014001e0040e1070450042010214807030140c00420340382016843c0c43c401d0f01c03601e031400b640c03400c441c002c00da0441244400c034003142c41454840e00d00c0e61445410760b01c1c0315480322160100031807080040440d0750440d0361801080007985400300280302040c01200080741c612150f4050140b000641d41c5050101d40342888000400d94824080340d4209070840b00101e8074800c541032007401d04c00785d07502640e4188a40e0b07100c5250700740c0040c0c48501c03460241e01914002d80482400340c0a803a0300320b4442e401030f0010860548181461760109481d51500d16006040c6a1265101d424030a000743c410385d4241d030003000f04801100d59001450150030207107030640c2107042003c1180d03075034000c000f03443d03680648500c0c040340c6030303200c400d100210300364452009800180d41d080348000207422401a920381c181010300d98580d50a150044508485884c9240a0b200305042040c1c0d1101c2c04404031511500c001d0045000421b211001540c0183d0201a60364219454 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 656045251 1250 656044001 656044057
    0xa020a110a03211e08010608060f0603240a1a0c0708030a0e031e070b0717030f0405060106030c020613031e02010c110106120f021813021806030a121103 67
    0xb08980131850105050110542035201c440181110350a040007032480e00c66800180445100310110f0340c000720088100050b005290a011141010410003060040c0880d400d020110400d40105079000050722070004070140020000e2141c55030500a03150442d0f140c2c0c2400d42954425540180001c0c079810aa0119150074007400c00e40341643d4520000301c0020390511502c5440c00e100350350841a001c101817041c0540c0303020041c1c0b047c0791a0107080c0d0324584040520074042090703605641a104640c008280300e802071140b004031b40c4084d00146426510b200324454040c04100e0100d0410072002005502d4084c800d644008075551900041070b0304194202c0101080c1c0d1420382150981e042240800c802000b4403401c3e4074454200e40e01e07026510060022a1200880541e25400000400204070360303080703c480a070f4802403007204c0f418600043c405003231254402c140d6505074140c00001140c000600140036500940e10386007411540c41c0b00803078a644c01e640090740150072100e451102800c80c003003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 656046501 1250 656045251 656045267
    0xc0703111302040320040c0f03020c0f0f061e0405070302040908160b0103151a04020a020c030304030c1e0602150a0b181b19050313062c030a020a110a0321 68
    0x7060b0780404c107801035480010010032480c08c0a005160380000c022400d481c041c40946402c0c0301e140d040751082c1c40482040c66407810125079904d544c500000540e018100300845a034005c503003001c001c100450031602004003c101c00c81d0220b518103020440c8580400654829130000c80c0100c1c00000b0740e600d14208140b40420080c03c10805503e000721040d030307007481501212480c58003a68010385a0300c4058003a07281c40a504d0780c41d03501d40700100d400410003460f071540209944458414154048082c000c42d07090124a00807000960020441005040c01115106074411721030300700451503e05007004150311a103c0156040000c68000410100304454003522404645202e0b8541c50175034000d048440740783d81052110100034000010034582e400307488114408641090b001c001d10a4104d40303220300c04080b00500400d0f03101500040301c840f00044160381204031180c014203009401079988441c460300d52441c241e80400300c10404004500840e968500c80d80a01500c2c144103500c558024107000d0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 656047751 1250 656046501 656046563
    0x304030806032a0a08160603060602030f040509040f020622210803100e010b090111010c1d0409050d03060e010b131a0702100801050f04020c07031113020403 69
    0x1030302048155a4070402031016244101009804002c9014900001341400031030340d02c1400b9510031303d000f010f004540b040300d03501200d00b81d131400c2100c140d841e0401d0b82c0b02e0264403940110442c080c002000142810102c140e4030501c5241d610030384810503800100c141e0000305074810b0351005d41311138001164065954202034a0b02881d4480c0050354681d600d1204401f100004184900107c0880e480c64180c040b024050100610074017001d41c1c41c0c0211041d181c00c9001c0740c0c0e000544060401c5070086040c4551400040c0541d1088401d00c0e15605070050405030891003500035a413242040c010440611003c0c201c80c078039503808205145031a8828010001c1a04461603200003003140b041c040c081c1400050445051039803040348071010126031640c0b8011741d40041d400c05e011485032112298801c1d04075050383e5040b01e0750460011804244002c034001e091031085268001ea00c1840881d2061803002d511900003131001d00c1403500942c0039400c0c0c0e001940304132542006141240040d102d01101d0032691 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 656049001 1250 656047751 656047753
    0x1608060a0b0411030103080c07150f141c0b030307080d0203090607020f0a0312090b1806160c021203070c030f0203060c0c0d080702030d0c1707031503081305100203030403080603 78
    0x40b03c04825080407511042c071006141e0400003035003500907001441951b00809015100703660840c05200060580d02d24000b80f0740000f046038070344000c200364107000d44d000885038456030510301c10002c0070701c1c008281c1c0b00025035042c4001d000c03000c00038000c41c1c000c040c1410042030150702c906006401ca440c1c07060103800303502950810403540384a06400240d03080720a4241c035000c40320b245040103c3c4014109100e001d080384041104104204c000222001480802442145c025903107001c0c4d84000d07540700c54010030014844950b118054a4440c4190f03502241f040f09032498184a03079612003807441264801c85d104096407200740b09618043c41a103501101c0408551b141096502d04162140da50b180071100b4010640007042d16144204143ca038100100402000301845480001d400404a030328000c42d14401000080c81480c440e0240d04081c01c00e4040c0545410f09540d034100d21508401d803010801c0703003401d600190940d549208450090855000f4554a0074213082c010a071072001040e007401b07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 656050251 1250 656049001 656049011
    0x20f0904020303030403030504020a050a03060b101103040306090602090a080d0305160e060c0a02041113080c01050403331407110607030e030f040f1e150e01021608060a0b04 76
    0x5a10b02008803a0300c175515280010386030b51944001280542d07241c01040c0c110f81c00c00b0010040001380d502c006802d2408503280481d0501c1c0d01011101c00741420a24a4030350010b04c400c10000300960003406c29a84038080150400c4210000f00f408000e1690000f2240d0b401300000f1103c441c1c0611405801c9403241095528811848201910318100d040b03606000306400210308509100920030740b480964010700c107001403540c80d01c078001d01c0e805c40c2100d034248800903800050000c40020300d0742601c080684503241468a181c44408042010034a103e202c0701e010380c10380c0c034207605901140c4004801510300050300000c0701011110746000070802c0e41880b18480d04000510300010310154411107d141c00301340c85040709007060460241442c484140300c0b01140100f00c201e1112000d4007a100c51410107004a46541c42500c0310344102c0c46882c9102c1250105a0691403062000f9100b4410600450b10306c14842c460f0307000140d00e554460380c4550030600c103000f2440c000f40610504040215400d201c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 656051501 1250 656050251 656050253
    0xd0e131a0607060e10050604180209040f030c0f0309031a060328080711030f0303220807050303040c0609080102041a16080309061b04081c030609020a0309020f0904 72
    0x109452140a203442090701085000800009800c0210003501000039030380702c6200d40d10644041c04081e12010303c5030341006910b4042003224083c000b45103800400e0842d1355140c985a440c240301c1e55400c1070742000790607030b03810020807400c0c52001c2c11a031003540e030f51701640e241d03080c20390382c0c80760140c44014400714050078824107680020b00c500000b81401405040e44403c40e02c49408031080c80002000c0b1200460040e051106011615800e80e03000d0b000d03529090b0007800900e499110803140000070340e401c003594084400d201c03100f160a080c0300701c42c1240303000c2d45a00c6151031600700b25000c68070761401e10024014180d000c00d07240000c10070300c002503003080d042080d0345a4030840441c005180d0f01d4080340c54910350448051400100c0e80202c0b0440d44d074201603c0254840504540d0304900c3c10251364070113002040041254201c40309180544a14002d005000802901412104003055215280071030700c100580b00415071040039840003d081591441400085250428014402e800c002e007044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 656052751 1250 656051501 656051531
    0x90120031906080d030b091605030c030c040e0f090c03071505030a0b0409031e090f0302010503060d05010e0a03020c0306040302070e13060603150b220216050d0e13 72
    0xe4000644074a4940c00041d5414100024007860f484008140b1a480c0b850014079055403142c180103a064920060b20703a500c0900e950242c0e070070050309000400400004010003e5038014640011090360b1151405944840a0700440d0007030310029074400480043c00701c85003080001c505180381c00c0c0d01410280d4030b08040206450041e90500003800000000500b03103500d03175449082c04500017072041009200500b07008003050300d602510804804c441ca490f0880314059603203c0111400c0004e88940c090540e401100d5030340010700b800390021100803101001035400c1c042c202a44981c1801455075815a0400a1600d000c0c4089207029400240500c00440e0780880c01c00141c400b2100800c2503500c0e0440100065640080081e041500d024000320400000c04a100007148a03402d0a12284105600700641c510750840e034101e400c505195003004d071455940150032030554507280e00011f8507841d200ca601700303200c040807140080c090036802d9046142403580a503448004803170400a00000c24062 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 656054001 1250 656052751 656052757
    0x30905090a052202280302150301170f0c010e030a170a0f170703090317041a0601030e10051305060a020d1401080c0f1318110f09010b0c010b0a030506090120 69
    0x141462844581a03170a0012025801800940c2d003d0240d404100c07150180184c19042805443e000b01a190300080b0b032080001103088040c280100a482141c1a01005640d80035603030036465010302a440700100070540850280d840841000d95280d9149c044c07c40c000c0140d40d0000d90501482821504480d21401c02d01c10107034821200d003400144000345080a4601d44020054948502202d8040004110403980849041100c80d0761449950f2542c80c0107400380d0711501ea0315052079000b404a0040c3c8800d5030400c0d600540c0e134080325034106000e03403152814100110303a49416550006a8000540100e00c610310010350302d1210000e41e541001760990310342150481c03030751113502d0b2080d5814480e51400040d03029900950000c000d080707441d99a141c0501c103580c01c25103060070824010001c3e41030980200d048e404009004101c00d03828000b5400c02c0340c01006880da102d40d80c40c141c500c0300e6198841c111001e580190011b00c020320704003100c0c07401c0d245100e800003814042c400d01500580e100d038040d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 656055251 1250 656054001 656054029
    0x215070306270e06041203050705070f0b060f031e0610030b1302061614071e0905040503120106080f060604050d0f0312110d0509030f03040807030905090a052202 71
    0x40d0310742c4464200803201030590b0300b42c6400d840c0100e406110400480444444c0075130200c0d14148040d036150f000959541c0904440a0038403000c94200b00c000030030b0302801e10341c000301c001d104603504450100400c1c0b0308820384080c001c001c4100d41610000e080708008540d4404800c0352281c1c005400c540c4c03414503244011f0b201212461000001204640e2a081661140c5102c400552030b80c0465081c94020744002c0d14900c1c00d140640c83c4003041c1c0d008100c0c084001e01030200d81198100c1d10303040040b40140402081176805000502850001002c9000d8242c020034a40d900e81000f810068603001001c10080c00883c803400381004208041d4803035001c0d81d88003a40220020701030304028102600c42148905440090700d251154211120003550081c10011503240c03020422540c072900e00607902d09c5200190b03404040148000740004020b2001019000e1081c6801526240d072000810042070b402d50312891241c0c0c0380e408010075541030f0f4080e5030b901020604155042074141d00424200c0800c582c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 656056501 1250 656055251 656055299
    0x1c110604020d02010f1407111c1e0201050c070f05091f050108130b042d051905160b0301170307020109170f0a050c0a050a1d070e030d0215070306 64
    0x185201058000c06c1e00030504080d210b0700c541d81d10000d02d07000c000c13545c0060768148202c1070a442c0541c46134900481260566006640046070a40f00c05481014a02820224100201007016507003000d07051083d80020407a117458408120f060000b04600400020f003585080540041035000d040301d402c0e1070404607034081c01d0650300c50300d55403020320751b0820034074018155038011020b020130040700314503600c14180e05c80c1d40140010984c0806007080a09402c0140ca942d001000440b0403070150000940d0552090302200c540901d04c00710b2080240d15a40b0854403448003100400210200382200070005001c9000f0310b00d000c0e01a80040d002440d02d00400310015401011010003480422141c0d0f50702c6044000c03144e5000d00c80c90501d030745502c19481e040c094420107100140703d090440b102c80170b68044c020f20190000d50408800f061540040c050410403228811512494806000d0700401c104a0340c0540400021401d51119000d8080c018070205850032508106113000600d02c04d400c126824 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 656057751 1250 656056501 656056517
    0x114030f0d030c0e03010e25050915030102160b04020f0111030a08180307050c040605030303161b020901060804060c020f120f07050d120b0405060f211c110604020d0201 74
    0xc450130041407859682661030312620a10000000800b0b1141c0c2c015030700c42d007035001484211004265004d100b4103401c56141c0011406100a100030066000c002600041c03d0003000c4020051000c00301d17406960650720301c01030006506021205210300700302803d1504a182c03500c2c00c1d61307039640305200ca08010072030300740086444000090405018407a16508a0740c0f03c641d20b00303025071107a29081c1324500c564501000007449003004401d41c0d110301820991290901648141a15989000d400c0b41c410114140400720041e594413030200d0181c01255994011440c0070f10b090b10407185240450300543d480120b030a1039000d0300095140b120205242d0290b110340c0152000b074124046c83d44024010b00a402042c00c10711360008078031048040302c140c24442c5100480522007103c0080c1c0d100354115160740401c85039403c040c045800310381400c0a020500c0b000700c54899060a142d007501e20010203ca200518180394030121600f270140a070006402c2c0307801d2503800910b9070801c264000341801010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 656059001 1250 656057751 656057771
    0x90804050f12160503300d02070501020f090319020901060507030c0503033103080103061116150605030f030a0c03120203010305070312030507080c090303040b0d050114030f0d03 78
    0x746140701542c2d040c2412551110070498201c6440c2e10240a4140a07102d0100c2c540242d06102c0b0403034a4500c0d01c03c2c440c2511502c04159070070607502c03468010941d25000c02440c0006102440144040c030200110b59449030b00300b00406003000281104840600c07041d920880141e920b8500e541c0c112411420402c1d80e80c6078078681543c0300400f0a9001d001800f0110400c4040700c03904d205030304000601003407982e4520300015a103e05590840010340012501401071000440c9c941c04607600004010b01c00c0d040034845134410606a02c400b90864140307030b10a8540c5840100d0340039150140c4011800740907000c180d11401381c4c5e00d000725036002c410408400355030000e00d030041d683c04039140b5005c5410341d500d603100e043c1141e4500341e51008941d900c1d1441d14845100d0301c6803144074010810b5941c1e20b0416210304030840c489030042c0c216260315000400000a007400f00304014281c0c034400c0540440c2d10340c5000f00c010010000244c0c3e0707030302076006103401400e40580454212116901814006104880 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 656060251 1250 656059001 656059009
    0x1170c01050319050907080f1b0f04110a020d11070e06040504030917030a1418040c0504050406030c1d01061209060b12011a040b030a150207080f120703090804050f 72
    0x3461401030103c40c54141800140d05002c0388100a0300c00c0c08040b03500b075000c01440543e0f214902c514922050030740340504d040515060031004160f81000300041854041d40002644c19804600c0744405030384041954100c80f03400100c003056684103000030b404503074985054440c21000080089106a03500c0300020304241c0100b0201c03015084070322102c03c0c0340c0074071081280d07a46e115008050204480c43c41e0444a16102c100325a8120b0b0800105081d0820340e20612018041c5060f4410610505110106098956100381d80c0154094642029000d10b08120030440d28030800f05075801003207000040c00b246401c1443d00044140070f072000610b51540341850720040c410390007038942c861000c08807001200d405400003584034105030629907405000c141000129001c0c90080c2e40c00d0303040603107010046417040140020248003640d016140961940c0c80034803035409035401c02c0c0d004c0404242035803110401090113620502da41400c0150204035200c2d00803a00441c8035003403160000035007664107522 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 656061501 1250 656060251 656060281
    0xc030615031e0603081213020f0d1a0c040918080318010e120a0e09040221010204181d070e0f071707020705031b060304030327060c030501170c010503 66
    0x101000c108805620ba280040b1981d0000000e030b005c0e0300001340810544001c1d5007d10b0030301580204400610b00042081c40074090391800e09403107600070946005c480c0011051242e03c1100800410380e80d41d82031501100480d006409003030079001a840010b8000703042001100d800c19058060300207003100c0091070780c1c003401c450000d440644c0512081289204041400b8091900762900c600e0440c6101c84c09008480f10211000b0754040070707000d00c80303040c0c1241001740054001c1c941c00241c50107442c0e8445030344004d48844060131459845169010250189002d0412800044044d2040b02e1030400906c030b85050291008104000380c10205440d24024500d041910a50744001c0c4e01514120b04083d4490000788100760190092410070032804d040711008005d1500020186400c5440e41d4504800a140806503c0e00b04002030070302805680700700781d51400e1944681e07000f10740014120300045c2650b5042c0e00c1000129620b43d00c40803050400724040010220a103403854491740d0701003000003010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 656062751 1250 656061501 656061551
    0xe0d0e1309060218030c0a17070302031605091006020303060f06120f180c090c0904061a1c0207080904110f0d0b030c1912031205070f02010c03061503 66
    0x5890107005004200c0307030350050a410030038108444001c204c0300d82850388400b542120030b80e200c00c104100344900b00d0b00800200b40032020400f1944066101c1d404a03160070945000c8410300b40c0301103810070013807404256555108042c4055212481c0c1b401a0103552404083e142905c00c80310714640000f2511200283e41383c07903109101800c05030810320200400d40301c00340c401b110310001d4210344a40351100003400034401040549280c1c800e80e640101e10180d42c000d60030495000ba110710b400a003444500c88070307410011112149a60300e41103d00382d240001140b0101e1441d16005201c0075001c00c2c0c40c141555070a1500340c8001c90f81c008505a00d2714148143d0841340c8100c0b8020803841c40b9804070764080561400282c040b40c118081d06000c000c4100c18015412070200c110b41c0e01808044170146000300054401c1c1084055028860004425103001311000000101c0d86004c0c1c01017180e0902807444948024201048080e00300300420b00c8001262640300c051546604c003030700c01c1c1145a14860700c69 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 656064001 1250 656062751 656062789
    0x604020f0406030507110c060703261f0501021f0f200a14040b07081602040f02180907090b160507030308190e0a0b04080d0c0305190e0d0e 61
    0x80e90b100c950160040c102a42c4490014071211005100c080300050200800c0d08005c100b9820541a6074044554085002c0c46c202c1555010110700040ca500f1402c541c0244840140d00030003003074180c09164484071a601c424111340c031040300b440440e40d0011001813030310040c050100c1d100240c84c0c01d005c040e004002901404a44107400109400c07580d5001e802144120703561000f14001c45594008a0300403405040f60b90082007051500254044000b4401440000d29140c45030055400060480f201c0c030901d9600c264001407007030141b0f0b801307060807616250111620585130500d4000101200024058400c5c10000000d42a103681c1f00c0c80b01c1c0060b10782e40142203440141d12440e0040c00340300301340d0b050407035080842d41c2904407e425000d81c4210701c981070300034004461240c07600d0480d80d07001740080d80c06e007000300300b0310010076101d00070440d000c1d0703c64034041072505106a010700c4900d204900e248000303150010081d260400030030000c242c00c084e03140150441c58454006a04810307101c40340b01c03078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 656065251 1250 656064001 656064007
    0x90626010807051302040503190201170c0315060703082202151206060309100906021c0e0c010309080702040522050c0f04020a17150303040807080d0e01020d080604020f 74
    0x650341c000501c0e403090760400e13140c0400c0d910b00c41140030107900441c000c00740e250f040280303956140485502c1001055005242061402c0d07100c000e240c0d03240d401503914030504000042085400040141e540e48510000d40e8091310301052900c0050615002074610b504c0d078441d000040100c1002c4490f21400070307800424007c0d40400c04039420000fa40221300e0640000c0b500c4001170050310f4002c082d6032040e030f8400090580c05988001c080c000b810721510860b0038550074170049143c502d00010400d1002482a0009a1004020041e51a1845a880c96070406003001d10315000a400300c015104241d0b415140072426803030b101d042c031180500401c00303110080d02d0b400151040c04030000c1da40424001c2644c030b4110008004c81444207034490000940b0100c0c400c07010510805003000d000c0355000f005045070030310702c0002100081c1954000e900043c40e590140e5001d0096200034401422104100c1c2041805031350800000b03912007003190b60708010301c69980c1c0003035900d849030f03012590342100000034295 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 656066501 1250 656065251 656065259
    0xc0a030e030f0c01021c0e0709020c10020c01020901020715090e04020f060a0206010f1a040b0901030f0204080d14071212140a0905101103060d0204020d060f180c09062601 75
    0xc000d4000860422072070302030a40d00100d5104607c10310f103100b042c8102a11003182890550b001a60000e600c00c2c42c1840b42c11050341c503040c070070300c0030b030038200c031501c00159841d188500024580001e5400400c2c0d201c003801541461950405403d00442c1c6a48400020702d6407140002940c03130320140000e035008040094400c40345076010580078107807080c03c1e69199180707840c1d070f003264210400741e0b0740741d0207440d0704000074041d100601e0003802d0702400514002c203040058010100590f001035100803035550000c40080d26503038014a52044000c002c40c4400e060410075140d80074008802e444030b109005800214810076000c0e500018410031105035402140e08000c40002d0007404411f030305175000d0040c10103426041409000c2c4140700320000e5440307070451b20381c4002c10448007404202281e00c15402c1021010076211800b03210000c00d400c0d031210b0107162134011030030350000b41040320006c414a04169818050341240e00c1805440c05450095045c14202100200e0002c6224a64210300c0040d00002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 656067751 1250 656066501 656066503
    0x21008041202030a08070503090c03070303050d0605090c0a083103091403060a18061d0111071e0206070204020d0e0f0106060e1c0c0f0312080c0a030e030f0c 69
    0x2602403031154a0000e268044000c0480e128099941c666000480d44d40200d12071a01c0343c0003a68000000b40305403101031038070500092403c101c03680118003040000c2441803c240c560310401000300f000307540c1b02405180c0901c0119003486810814014800b901000c00d12003841d40308050303e001d4627400d55900501d201201081c0c110741e144800c1300020024440820078100003100d8400340c40000e0000c1910b40c950000d84000741052898406900c0119188400440e016000c0e03444c080a0203070302c03a62500442003c5500f0b540511174180740365181041000005800c00d040d840720301403480140d201c00c0d0391600c0001c40030f1145220103540a4004070b141c0800d66941e81c0121400d0740c0200840310201c0700d0441290a80b00e80b445020045001004034a4041c2400a601444541e814864011a2a140e074a2211218a80c0c00c50349955442c41e5040c010072500f50780d071404020359030030030030464500300c6010311103440340c0d05140081545407100074030103803000c10130384551040741c1c00035a40f100400b1283c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 656069001 1250 656067751 656067767
    0x1d0d020d0611031906090b01120e0f0a08030603010e03160602090604180203100501030b030d121104080a030f02010501150e0a030602160c0e060f09070516030e090f06010f18030210 79
    0x102e5801403800311700103290900783c0f10f0585d0560041c1c40d203421030300c2004840c0000b00220b400c20039540c05025091400b0300020310442045510905401c1d8030390800ca0145821201044c29003002d6500030050030b1a451100d20711440d4841d806035015a80d2142c11020600f03e010f190f111500e45940311b18450030110058004d94420a00c2404042d401071f07460004409650400b54410b4041d0402c3c10500b041d244039200b2594603000848010650030685034402d045580306a020141c0d542041000c0002c1507071005014031101d01901c02170002d54105806840c8582da4100c81100741f1a4041c5800065180d41c810706000b19009002151036884480150208103a00c100484012640540c04203440d0240c9810034020000034000d4889080301c001800f844842c060b0003074051020a001200003844d6944805400d188240d444000400c01c4106224100304080d003a80c40c100220f004011590740c2c00030582c5a40e4025141100360b400c00320000143c08845a08041e410480507041da800d81d68002401d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 656070251 1250 656069001 656069041
    0x120c16090f2a1b020910060f02160510200106060e0118120f150b1512061003020409020c01050105100507030e06070c0909121d0d020d061103 62
    0x414002c0201d450401c0c50780140c1d24005120103901c50080341100c91241d0721100e450481600c00c408254400e400050056000711100740b00c03894540b0040c416a540b21a0040c0c010000d4002061240313040a001c10640c200c9025090040f44034100540c4110b00c11380135a4003103505074481480f1807030f64100c540d02a2000780500e00100302d001d041ea00c440d51040d029003054100d84002040d01d182000d10300c001c2c42402c0001500c121900b101c0a0010902c405c00c3d00c0c044141d0f0940000315214401c0c10301c4012550b6a0240060034414400e2050003c510042d090b402502200c15070011300e034501081c0c009019940141748524404150700c140600c056011505032842216a400104103400046983e0311446d031004001a0305c0038200385041c10202d001c0d2403281c0c4180b840c0714030152202514001c83c0d0044009543d05806100101c4040c0d030881c00c25100051640c5002101e1016900882c1303980b030503680002e0241001121000510803a5400f4000d1203d28100590340c0c0d040411240500c50b2070514 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 656071501 1250 656070251 656070281
    0x70b040209060429010f05040b1902010b1306090b0103180f02041503030815040608070b0f040b0f1e04060903080318010603031205010e071d03070801330602120c1609 73
    0x8011300d61b0f00c1c000c070241c1341281c0f4050159858852030f103800d000d140d0940c003c640c02395921044510940d543e0342540303c1040711b0180c400520380c1c2ca41100e84e0700790f682030000ac2c4d06151038250040d51219070000c0091480381c100318880b10580c01440032800070010003e5604054007158800f104140d802500300380103e81c601303603076201500c2c00410003046400a109010302640404401c000140b401400ba201c0340070100c2c00e45007800c1e03552007400c81591000c6c0400c25211000105d01e04002684064150840c2074072800d02e0415061603000391040c0010f002c06005240044002a56290f80d58030318401c40120100901c5010340d40e01d40600080c40e00c0000c04440740c01c0400109400e854581c61070700c5010566154240fa011b18601060300d10700548080d501402050b201048400003400b0b090611604403180c40003188070b602960703490740b02260131219003091403e010000c46600046200c3c1080e0782c0300685984801d58240e291428a0a00e03013907881c940803043c000f4034925940c0c03210a81c07036040741c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 656072751 1250 656071501 656071517
    0x11e17180c04020f1e0f040906080d0c15090c0b0f0406080c120601050c01200301050a0609031502090a18090b0627090f010f0204090c05070b04020906042901 69
    0x10100b10690080012101c0b220800340009850540d0103008114205000600b152400460b844c05000c254000d802c0511196240c070001c100c110030800c4030fa43c0b14040b5144c401407610250344c031049a00d103680039081d20704e034403060901c00703010181c80d01a00626034044020b036a025a07404107101074129104007000b003000c4600041d040640d00381150981d142c62501050742c0d603110340040d600e58121021581c8070b59a100c41003412100c94040da13007000011040003a440b503142c80304001034140035401c004200000c180302007000078943c00e240010746002c020003688800410010034009880c43d0702030b42c42c5402130b591700300c00354225038803011410b40a0980100b4075502d500601c0034804056035507a61003c10148840a440307001c07080250021840c0c2d095400010291050509480080501c0d00b05164006010030805210381b28142c52625141012800d1001c41c0d10b91050302d800c0148064000c0e82c1420000304c0c10b55a95010f0300d030000d540c00019040304e41031020014400000100310b40814170306 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 656074001 1250 656072751 656072773
    0x2100f0905130b1005030c091017090c100302070537111c020603070806010203040f030305280507060f02040e0a0e011512020d020f03030301060f0914011e1718 70
    0x14904a0348640a8080b4807843e005030301c0700f400380ca41072270700f1b52400700071080100c40101d400e00780d0103034024082d400040031281492410040d561403001404000d1605c1001070f42c0c00104045800c072641800c3c0e1140e080c1300d0a1401c000380e040d007145468040b00342120100001088400710007040b11000035104c01d4850a00d0b0010480c0302c054000c6c028ad03200c3e0003440019a001d20036880a41d0009040c410b4a043c01c0d90f40a030840d2050294000328041034002c284c40c04400700c26220803007280d0b130403c000040680c0b1444098118415080e003e40019102c9904003003006c2e140c6c04075402405148090f001c9403514010443c010842700150070480c0d400e11022910141d280b5000c0800d0b0360020007207a00c0c0000381d50070441714000084040b6005408a403003c00740d40c0d4280301a41c020900b80e191544500d200020050040301d0175000b03040c110a81c1139001900e641d12940450903556051820200da400f00d0105451041c590b4440100030f1204000304403003840202c100d0100440c052003100d0400c0c1d10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 656075251 1250 656074001 656074007
    0x2031f0c09051c0201140c03040501030f0c140703020102070c14030c0d031b05160b0a02070609030c0909081303150e0703020f0f1809160503030702100f0905130b10 72
    0x11074810302d80d00605040500b80350044a01811011610505040036030300e4100a041031a504070040b00c0710b84c0e0b00049010046d5503094010140c03008042d02003086444003821000d040b5001d410b14034400d0140204a1104043c000d604540c0160b4004a0103101107a8911101c10b400580c9613286000b401280791060203400c040b68000c003244d03030580320468500c0b80400c90701c440300740b510000c5e02c01d44100031225400f00c1c0f00c110420041c0c06459150740d9101c005850292074021568400c1c41007010320071040001c9030030022040e095400820000c00c1d40000350901c038405000d6107481e0781400b00f20560020800c0414a01209503e644000512041c40e05001c10798403030000f80300103500520380e003038510440e1828240d4120034003001018211501140c020303000c40404101c600b032000354025440386000c00300c0b10b03541c98004c4c4801c070700861030081d0590118011a00f034130303064001d2094140358408414041c440308005420084c0900300115225502c00000d4408000340c0743c0103d480d42d8424a8044c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 656076501 1250 656075251 656075267
    0x3081902131d07021e12031f120f020d020402040306140a0c140f0c0102040b070b01140609030a0303051b072307030203121c06080a0302011b0e01030b030a02031f0c 72
    0x2c4550058412105400d814003c0140317561700321a40740c0142c018070b40050710305502850299881010a072410404810b50207088000380d0848014004455040b60018424031400c00c0e6190341901c078808042082d1006c00d0280c00b594000800c00d0381054102e00c1f503907803a0503105109124280050208016503a01942c42d0500030540d45091281004060001c00c8080000d0560812260005140503a12118000d2a4002da001107444540c006c00402440d00c1c0c0340c050065049003100e0340791600c03040000280c2c0d51030040c0001402e0544810004124000100240c0d16124048036031135549c00c0703145072200b18218900840c40f020003015407144a042030020b0064141d9074044c000785052110018100b50356003082c0600cbd0619210f0406460740c040140c000c000080403108002c00799a00a03140103401c0d0b0369103418481c0003074604000d503da0f5960250b1005189802801c0015008640b0404a0f04007800100065098852014091812030b403800b0000c0201c00c0070f100400000e1210030080b1a924 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 656077751 1250 656076501 656076511
    0x4050c0c0105160917071d2e030605091c03140a0506010903080d06050d030c020405090114061c050f03090a080a030c03030515132003011203081902131d 67
    0x102c03141002e0044070401a240170400d4000c00071112099500d800800000001240f2001003a9465044c1b0204104211010031410030210082e0551032810075000c0714101c503807001401080d2581c01042840c50280b01c031540300c0c564034070301d01c40396801c3c140080c024110081301c00398806003240000d42c0e030180c00e02ca402d000d2a0140d403180d407001e00c4c5855241c0303c0c2c4c02ca20704400032182c1d0340000140c1341d81c80300365000300c6501c20345a2404c10035840c0100001c41341c00506d4004140d040c00c0421542410320b48005a100a007112080360000342e00400f401c0c810949240200984560001c00d007540c0c13070000c094011004104c0c0c0a509003601c43c0074281d2108a503240003800f18100c9840b550029000342c05c0b55a0150005100514640d100000111000000c20b01c440515590303094108180041800715428109050b1407117155501d0100d080500c3c0e003100c08084c0401900002003a51646041c20b07015464100020541d1202c0040450a070f42403e42c3c8607a210305244c020001c100c05648020083c411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 656079001 1250 656077751 656077757
    0x30709050406051315080a0b060a08010b0a05271f1a03160e03241305030f07021507080301060e0f01052d121012051009020f04050c0c010516 62
    0x800702c144d80100a018103000205010308101307030103d5466801c018a1000601841d165005400d001040c020008186d4100104076410040c840a583d1141d002e1728040320000ea5210884940d1381a43e80808503070042e03400450a420401c0c89650030060030780480d4080d080036196403065071405500401c0c540b5405c1c0c41116007082c030015200321214194540c24403150f08080d465031110b00002424a24000030b030400e01080451000302510031480c40a40c440f010040301301ca0302800386c031101d503280211084044440c100003050003c548400880591070103110400d15128404d510300f40003580c00074058900001d00d51403860040d4607107500d015003c0041030312110319024240003500301e522a1034010a2803c031405128004859140004150f8401e05041c02c41355810600b10120303a440c001d9004070560501c0c0100032000c0741003c61940c0111044080000d640d000510100301402c000d000c0c01544940b40800b046a080100c500414043d20004003c00007540d801b81008419031000300b60b0000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 656080251 1250 656079001 656079019
    0x3010e0711010212070201050a060905070c290103140d030501030201090b03040c0b0307110c0a03023001061517160e01030b040f0606090e090c01050d090606060503070905040605 78
    0xc560055045412040d00d40e4005450025080d40ea004048410707101900145e5440d410061154060310800001d84481c0109000c2d5041c5103100401291081c40058035a00c0256000300412030803450307202d4079996841152140350b0796070401500d51003503032001100da80698844081f60038440d01ca0141629030586a0a00e075a007042e403020f140b600010b1044600628440021074196071103c0a107104185503550010b83d0340d403107603906040c85081c4410901544541105100503644d108001c146540c036070700095407900d40d004c00900c805421890707000b200d51a080000c5402c1a100720104602c0082d52142240050b00548088100d00308641c0c040801d250961001c0c100c511407100a12040b005160206225801c40b00013030845080030901d24a40e5550507040055540cc811120300505060140c00028a000c41485490f03000e402c112504020001512410b0015036034800251950003800c02c000150703d0b40c0b8050120381c0140d41e00b0000c6140140b00081d01d242c03d020f580c003510340142a01c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 656081501 1250 656080251 656080261
    0xd2f011a01320901020f0a080c070b120c03040c03080c07030b0106110c01082d15030a0c120c0e04050f071208090f040908030a05041a040b040f020a09020a020a02030d0503010e 77
    0x103150307005900f45a04500410360b025a10510401407d0000c40c01090354a035a01c151030072840c9030000740d83c092104500309000ca8251081c090440a5110590a0080340e495a81346003c801582103030f00014120b1501054104001c100050759105a80c410307080801141d0b00c42c48c00b80c3d100c44040003525825130010311804002e500c60ba40c3c4a800240c00c0311b407641c90980304014040c01d010011001c0429428040c20020508601114015900382c00d03400f40c0307003000c0561035452007204180102d4030710314070046000003009a4045408010007000c0302c040c001e81403900d8890340f98041614180750f2842101d601180082d200241101ea80380e00402c2c0c1c61520b4100c2003030054072402c00c404194895500e449040c00f250395070009520452400d10002018501843c08034110260140e007084c5241100c020403000455208019030825008503422507a20400d00c00207002e881582c002000e2203001080e040c038020780008039140c2040c0700700c043c0d41c1140d00004080300c0c00e000c2441403815440c1ca802c0428 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 656082751 1250 656081501 656081597
    0x5060a14040b0a0e0708010c0c0519080304060c1202070f06050c1314040b06070309080106061803031d030f070e0a0c0f08070203090a030b180d2f011a01 67
    0xc0713600300c136071003580c2d1000c1d5100007039401c40c0d410b559103001041c0040c80c92000c00006010350301e5081c80b20501906c480303141c0e448403011404000c1006003460740d140c128101481c045c4210040a0301540815543d500701071400070840c9900540c01c840f031f2070130700c004507800b0b0701090700751350880c801840c1400c07505241c94924041c026242101e507411590b564284061038a43e07400401005002e82c60b2076140500d001c1c1f801d421034040f9031010007007201035400610802c500c1c80c0407004036a01490403041c00400c8112180d0104100d840c0c02d0350510a0100070f61801d2408500d6004a031540c8446010647d50788400400f03441003060315400050b102d180c0345e40910700600e86950021501c1c81124101404000850300300001ca40007910310b43c44420400600d104008011412302848001030000c1c4035515402404040c85000340c5410906900800062801840d6003043d0314075213a4000d015207051800d84240d43c240c1c11400c140040c21140c0350001e24240d0928690740860715140c6c440c5040c409030011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 656084001 1250 656082751 656082761
    0x509040b01030908070b0f0a1116060b041d01061a07030c0f060e011506030b010e21060a09020f011707050a09080f0607110d020a08070c030f05060a14040b0a 69
    0x2418559074607000804500144d01404025108602054950502c010405a8554024243e407007060070241c002c5203d00341c40050300c001aa000100080782c4185103401c1c4060103a08551540181c40c141c0300c0740800c08800e00061103040d604000f08221030302d50f1042d4002c040c5000b07500e00050820821500024414245143c0c0c25010701c2e5004841c00c855510103043d11b4070480034a41507034481d03244110000c665001e400041c0264141080304101400000c0c7c0f50300481805944a0711100304224040031260100d07130b140400040c1500d500c1d107410707042d003001040c1c801803c1e4007c8a02101c10800d0754081c1c0103600042000c0e4000c011103aa03495011540d60740302c1806002044402100000c4040c01000304416408084025001614240e500240403a10b41040e8259940c0002c42d4280920340204000c0031850300124081e03039490990420070301648071940001c1000c0000c1c06403000b40324002c82d810707018910400f070900030b4402d17020301e0000d54607095802501c445003400c041001c14206e6482 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 656085251 1250 656084001 656084021
    0x30b210f06070509010206010e090a060b041e06140d080706020d23041520031512030a170402010509010507112205090d02030f0d0f110415020d050904 66
    0x498a008a06220507030401005442c00710105802048400f2150b03014000300e400340c01e95a80c0c4500da441c00d110b21681d01c2d42d0327003800500700554480d4030030750a448940003084003507140301d104952080350001c6400100f000e0f10555151403004200c0001925000841681032034101030000e09110441d1140e000942c4046402d252044e41d8080e9400107540000041d403550610302c010706564a80707424800201113070301810395032541c600807110711200c08880c0394407800103407a0b507034648954814405241e802594289503031b2290031b6600841d0342c254000002c0040c81407541c1e076808900c920400c0022444400d840081c00310700103100450442d4403d401603e10a4040c0107a040b500d02000007160140d8010000c82145001000c0c4010481845000c1c01d90000c98101c0284440d00d01280c00030348a0150504070b90b08854001504c0c4c008000c02c0d045950180d40a010030401403008680c00340b803d500900c5501027103000100d841c40c00600208024480c00c41c20340340c0b1842c000c8420104001800c2001c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 656086501 1250 656085251 656085253
    0x1b20030706051005180c041a0d0509030c1902010c030c0321020306032503021c050f03130920030a02040e010305061509070c02090a0e030a0f090501030b21 68
    0x10603000300e0748900546003e190039081c020f00f07040c100340c1440101c840c14103140c00d0352011a410b00a940d1481002c4400f12810107005540c04400403400002c5480b889903508145030818080c020010004802010342042920480300c034074011415094403240c1000f0042d002c9034100000c40b0119001c1c03600700c103003144245004103013038000041803202ca994200540352201e502000304100c88c141000f83e450b18072103c175800d07040034811000d41300b003010303032808020700801e0300c0c0310094819094040b0700d00c02150300c031040e603010240295056940e40c2112801e0440341050000025003a605032184030300c080581d01d24140058808000c0903120341c0090000101035a00304000504403601042c514041c501c580c002e04917504005a40c00540c102c85008c0c98401c030500c07014003000329000000d4101a40c1c2c10b450000c1c540e510070342054003d2029820240d850700002501a4400380c0c0311511503030313015154a0707000f51251180c0045003128007209180c1e4121000c0d8407800c42e105a5812490421801e040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 656087751 1250 656086501 656086507
    0x1303052203120807080112020d11180a0e120a02030315030f10140c09062203060606020a061104050d020d020a030206040620061b0c0f061006031b2003 66
    0x390310740c42c0190005107000b0000b0080c42c1801405644030040c20f00504e0b040710a81d00c0794240790001603c09803a0312000703225240064444001d074803180c00c944d040504034003460304103207030600c0503402919040000703010754050009008401c10140c0150b4611284c59402582160341d0b0362020505098144100c40d8148075010003c02c4420703040122032000c0a0100c800b1900985c175111250104401509a4241c04814019290191a280242c07004e4204200342203031a20803d000c0200c4d8200d160304090001d030300341140495400d400188201462b4030076641001001801a142d030307494029401419440100800d205002d45024100d1100443c0000d1a90190b650750380c3c005140d5a00030751040010804014050000b4414203600e842c10995840142036145400008041480c11520484092110124036103544a008011f81c032111800c003000c031030880c100742420456a044512039880064142542c2d828038203070200122444061644660a800c1c0400c48248500d0241040e404541d10083c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 656089001 1250 656087751 656087753
    0x3150118090204060809010b0f090c2106010e0315070f121404150507080f041b0602010f06050109032112060303120b0f0109141c0b070201051303052203 67
    0x100c98000800c80114010380d07503403800b08040c2c13195000a006210030b0f494440d0404240c1c49a00c008004098200ca50424075a600c04d0720705000e0140204000d00c02c0707804408510b10300d20400c03060740629826214117498401600400d0781e9070b20401080103c5110400105030301c5c1e07019550782c0030700c01000d080c101500551102480115254404241c0341e441c1d0407000e00041c0704004040c000d40c501605d000b841146016100030342001e6010f082d05c0c1841350540002011b200e030140320250400966007110300382640e141c0c00280a0f08210044004517413034400002240e40c010200b50080760390011141206404101058105642e0003001e41c0c140030600c50700440b120501d00c204000b440c840e4851a608410086001e4112241c1001141c050701c90f0b401020b0032030b03030810040d5003180c1000b445a0705141003c404590350340300a00c0d030050207050005481e0200813076554424400d0780158020001591141c000c402480e002c00c1d030290114400700810300c0c50b406204110201d24205028520440790f403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 656090251 1250 656089001 656089037
    0xe280b04050f04020907050304050309011805030a0b010302090109060f090c11120a1d060315130f1b03020715020c0c150a0906030203090706050304060b0a080703050f12031501 77
    0x4100e40c000708400094040000b1845c240f890759401c22103030310f009411494a55103c41e40d030f04c1004d4074075044c413000d521541807114400018102516000d030a0381d84040d468503148140c000c1c280000c912034848100085840041481601304469065030301020441ca400813480080c10012403072010400c1002c20003803003940421444040c00081082d1942c0d4500c483d000518541081035040c6881e0404c00c200203903603503450300f602d4010800c4400c901c028012400050040d03010803126401540c1845500c0303407015160b501a500e0107848080092152403030f41e80841c100d12580e0320061a1002c440450f40b60640c0300d0780580f0031040b00350121000c20840c013002035610001406688013282000513001c1d0388503800011240107107060309056040d81000c00440b5115410340c0610800c010010002070240250754002c4055580090150b1118035221a2616180e030001c0c002540c06100c0c00110881800d0300280d11107030412848074490543e04c80340c003212400e603544185141042040120383d020981 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 656091501 1250 656090251 656090261
    0x16050121090b0103030e0612060609030f01180c0f27090501090f1506050604090908090a080c0901082d01230612070b0f1309180204060e280b04 63
    0x4002c10b0342c20500d41c510b1800908015245074640d01810062014089a54034001c00540040085074650744445145020074646030308100c10755002e40c204140310270b8040c400029600810f01400306080c0c81c507100c400904500021b40b0420b000b030310914086042117200e120b610340c000225010003042090322038032091f00303582c000d0000380c4540d00c0d10510303c01040340745c0d030001e1142294100c0904c8810301e4540090a503018510402a400b40c68a10b07540400c01d074a81101e912070740050041908549a0300c0715036441c1011100940a160000c001042c1a41c0001d5144004007814003050500385002d09208200900041040c402c2e40d00d034529542d081c100030303a44402001004512084514080d002c100d6005000740013144290024403040c0002d403400c104403070002940c6c4031900c1e41c0c0c0c040d407a007a000300400c1d030348070711500b6140c0206503c0340c14044000c030ba50075008a40601442d500d4030410055184141d502600c00340d883c02540040c001d8040b085400740701e00c203800060340b01d9542c01060544d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 656092751 1250 656091501 656091503
    0x130f0f030e043e0705060f010503010525030207030e04021606060506180d03020c130203010f0b041d1521060703050f0112411605012109 60
    0x841c40305921529040c02c0c8116905030003107120000386444a504418806412003540d482d003500300010020a00ca4000b088a8013903038801c0803125140360140144201a00c00c0c01a203110b5420080419403d01055048401c104841820120002d22245041d402544500c600f1028003c88102c0070645a565201404420b618100301c24600c2e00c103850240c0484949400044c8200003d01c904e11a80c0c07040300034604940000e07145180d03a0191820144e1400f40c5200d406070380708404135044610030405401a40c100d4644d2240400210346405400742903000b60b000704145200c06916105409001d2080103400000c11440c40002104650128280c80040d031714500790b61100301a5401003407420007010382d00c022903250802003800c2c01003480003110418801d041c80301e5050300c4894207004001c0c082641c0002c5ea00b80b4004100d48203188004400310005a00c84600303c0200c0280400d2004604045880f8489030040005800c01005490000314807941d40320201000680042c0d103a11032050070340b41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 656094001 1250 656092751 656092757
    0x6060b070201090b0a050a05030901090203011806060807030308130c0e01090b09010909030519021c031a010806031e01110a020c030d050412061d0601030c051215130f0f03 75
    0x6010140000750040883e81d01100d0080010000f149819502c1016503c5c00100d0780b904968130b031200f8400c039016100c5904c2c06581075181c0046841c0184584094454180c0328150901c041591417080e10b031074400d184005000709048000080b500c0c1d4458080701101c070b200e506101032041d1510000f2180318000d07008219990317501d180800640c0742c01c10851307004044100b400c1c0501c1080b13a0700100b550040c04c241c58000503946918000042c002e110340e090402d0b5108084012180e4908024090030200f03000040e41c00e01074039407035269440769040c40d10844025000303240e14220564400c41d9219040400b42e400d559441581030000c1c211001003d8406141d40105000d4072480101070603d0360125900007441001c00003001041c00c0904841aa9900218001440d100040200c10f41c8400c1d0341c0c0328901800384400220410020f044548259001030711024031500d50403248981d0380082c0e02109030141c42d10000200c0b04950800300e000c280344030b210502c1400400c0d50302c40900d502204021004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 656095251 1250 656094001 656094007
    0x2030402011e08011a092b0f0803061003090201020a08030a060b070c141c0f0602040923130b01171606020102040e13021c06060b0d0509010b09091506010c06060b 71
    0x25160a41105017200c05050303020350300e4604004006002500c01c62014440301008800030301188a20902501c41a50801900500c0d00000e10341088140d0040f15064461300c20210043c450a21a01c40c01303015550680040072510095121242240c1004149417030342c545506003c00c1c11601c4101800d03070a03106010000c006810004006508400d9143d00c0e40a001d20304942c9000c01640380560f00140d40000c064042918a400c0c1030b4040d10864010100c1c0394206040d06c03014100c182c00c06d0b60085c810713040c0c1d100787e034644031141e02103806041405410260362000500c040d4441e03100130651002c0c5407040316030320740c40661009981c8629600031000341c0d601003410040400104d251982c00010400c5811198a40d540080c00f40c0101020120324090317260310840401c03601d58410405401c689415030b445035460326440d0054507044a5040d01075092216650107402c01c01d11460081e40598041c0024823b2990b0b454110100100340310b0400c04607040c04000b1640342d114001c06801e540f440540d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 656096501 1250 656095251 656095259
    0x3070210030b01050d0525020f120a140f070b07230f0f09030705030f0109021e09010b030c0708160506101a090105040302130504150c020303070302030402011e0801 72
    0x440080c008000400745410007454803a581e80c05012284100301011000035070740c1340d09000020f07003080d0300300641010807802c2440c18042d40000e0740300c9440e0001300464480c0c0301e44200790141d42c051042001e001c50041c12a00300c0d03400a202c0545140b94007004140e00b031080e03a03100c0362040c3c070302519200c0c041800d4a82c1400c403190810105804860040b50b12443c051814850103624440c034803007004071004c0465040382c160f80c00d00c0b9920041c00c0050454011a0009840e6030081011100c1244a5005003000ba44a000c0720680304200100040c8000842d80c0f0700701e1031900c2a440100031808190003049800c000904901c0a4503c0042c4500c09844000d403c4c035201e45010b0b800f404842d12901c0d07400080103a4030b4507002c0d0b003003d0010b1449658461054400688032801690070096101c800c070030480480346d010b980316504c21409110b24440080040a5000840c0c10744d2040c4001038108200044a81d4000d80043d82c00c01d1046c907144146000d103201142114090f9052000000e00e004c2c0104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 656097751 1250 656096501 656096509
    0x70f0506010f0e060622170c011d04181b050109050916030e0307051212060a0311040b0d050f010f0e030901090e1008030a0c060c0908030d091104020408030702 70
    0xd015016400181c4002403c0c6411100440e40c0105910b209410000702c86440c40100003440910204640003400120b0719529860102c940c5c1e103c8040c42440b8114400541e9841810078144500da4107440e030346e00042203003c0c440a040701c8508141400c503490f4000f40022082a602d014001001d0305423103400f4100000144403582c0359100610880e0310310284446040b00040c5002d0022460a0014060b542da1040034118000e01c0b1024001d400f407508100c071180002c07801048d803101568070000040c1c2e50f0400300001424280401b0340301040301c08032903031a810203502240005000501100916640740e179094074003c41442806410394450003461032601182c054000824410f0000c0d60a0140010009204071110b01c520048886228003084c01c5d444540d0400020f054000e082d66130f28010a8001f402d20010482d00700c0f400ca18003001d20b415103205440303030010341c4d02d0800a10303d010f0810041c40040c00100d0300070b440c02d03403a821414010740c2c1c0e148028001000740c0f601440e201c05e07280c0100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 656099001 1250 656097751 656097763
    0xa050304060207060f120b0a1205060a0e030a08180133050a05030d05160c120c081c0e041b03150b0c1c0302090306011403060a0606051803010e0102070f05 68
    0xd60305100300c0f8007071400d17010340016402e032100691500004010400500250180b01c03281d00c5100384501c181c5000e41440404034100e4030074a20b05000b0f000d440114080181c2d80d1203116900305c00100d840d404140094940c041c0c0c1c10041d820b4000200321017500c030051a40c28403c58141d80010110512400950424941c081000b082d040f11003529092406020036100d05103844681c0c20014009801c18030b2596501041e405d030341d001058003500a0700d0742220429044080c01c10795001065007800980c8a20002e20240c5a4400340c0c18041c410880d51000d4800d04000b80e003161b4860786038810540c000b040e0740001c0710302d180f065802203040610702e500085842c0581d0000d00703040c603003048240c03c880da0004080303100c60707e80d0000310040050410218001d0042d1003c46606000d003c0000481c4803840b074010000076021001d9404503125445c1d6041103504900c0b50202080c014060607907107000340e00c0c03d403040500240000c80c028100c0e22005003240d11034201120910760603c03101c030a01c1010041c2c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 656100251 1250 656099001 656099009
    0x519060215010f050d03051c0207050601080c030a0605090c030d02060604110708070305130e0c0a081f0b030601020709050a1a1e0f27060f1e210a050304060207 70
    0x41c0006941030101c460142e58441c081c541c041d60900c8080d00070144500211001540381c1c8400340f0600c100300100d0800383d40030301c405561600c12100003003080070380446c3c0002801c1d4010010019940d0a503100c0c4041c140080010b01540646014802d40d42c03401e101d00c0c01021000c0c1d02078151450440e04000480301e1010944121401c18800500020903941c1110281d5415007025500c0b8000e41660780e800c100c0e150801da0880d00c0c40c0c01480801b4207258060948215103071140801685c2c0d140100e07011040c14220780213000d40c1c0046c10410a01900010b58000d007042c41504d01c1e542d1203481c0d42d020b0f14025900c10100903503520821010225801c03507a404e5a100300c440001c0c0f2640c0d9012224031048140c03103188590786c45030080310306030340e4544001c0048000710100c1d0104142c12080c003001040032606a4080e641c10000c000a074074100450884e09081c400c00c24039842c02c0320301440b20341d40c02103400c1200004502502c6001c0402005440c424074481c20085503160b040030f4000742080140d0744 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 656101501 1250 656100251 656100283
    0x30c02070515160f030e0108060d0f0b0c090a1707090c0f080a02120f100f06121802031501060311030c030105010507051002030709030c0f03020616050705190602 71
    0x1410300503a51860568078220201405498031800ca0841041c00000c03c41001805900001e802c2c9003090781004c2c51090040003629518040d50340d850910076110301f40f0388010f0500c4104100c00c000644142d01c25500560003110880c10141110301282c08400c0c10381000641e54030b0304e4807015a0f118104011405001840c806100840715968041d01440c071903105034003440944000180081c00582c1900e5181c541e485c1d114000d401c104030040410041500e81000e01101240c0104807862003015500441d07080e59101c1403010800200c0d0401454050850402c1d26981e260500251b5001c110141d02002d000b4248043ca52404034045c04691070381754903901550003131003000403070107081060701c2c11500c0a0800700d684030b41030701d04142046045806444854404420302140399406409881500c4c4581070038204103446141c000d40c16030041c480294846410001c3c0143c001194030028442c1c2e10030001c4400c400d4503107000640e803003428038441002040d20b500400640740d04101c40b4010b01d00e101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 656102751 1250 656101501 656101513
    0x1517060105030118031112041706182a03010501060503071107030c120203101e0e010e10020906040308040b0712080708040201080c09090a020c070f0f091802030a060b01030c02 77
    0x84089900011141020317044c003000000d8100e40103070921200030800b012510f0180c1c2d50b0303212401180752102e00c10601c00c81340714000004070f2680400d980358442921613030042080c4000440195901000d48030140b041e5104036941c20250b8800f405081d02a1000f515040c2d124070313140c80005d150a0004010f10b1150380504d10804c0402c64030780300c40c002d4541c0c1644a1088c0b048500120389000703c0000400c0b042460210344910025a009c00540244a021410300c45152981070b100c0c01e07680040504411904410203079580519507500600b00014068111414181c0d83d840c1d05070603030001d500004441c140094035404018100c0440c41d00400315007402402410503060090400200600084c188450580840d81084c20503007500d6400300000d0404040303252210170340d00690030151303818880d841080400f0030311402c1035020750107036440c000004101500e005c1c603410203440040203000a50000c10780c800c0c0542c500340964561280a05808906030324000c0004040314800401142190030403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 656104001 1250 656102751 656102771
    0xc0102041d06150a1d0306040f03080711030f1303050d030207112b2a09140c071101090306180203060a1a0d061d0706020118020d02090a15170601050301 67
    0x1c003030f6089102d0300d00c1d05c50341c41c000c0480400e5803148134810705a0f252107800204804c101020015a440b40e20a503034440c443d48540c40f00351090700660001078260f8109000c0c8041d0540f490300640112003884514031180c9540f6140c260804e400100910000703a0001412000e110850140c0c0d00d070007805035101818900c2004020340308804c810415440b070144410283e040c4103010392886540c43c030f0ba15441da0121041d00e440d100c0c805151041d40c0c40309041240c0c04441c2141507824030311408404a030185030800e1981c80395140000900d803203051040c4001c2c00b0011504a10174944806070440c00303003001c0d1840c1d00400d1b00d4540014012644282001c44007204a565046600f40b03804090325140005101850618003030a003c0418268070150071000d1a40e0041c005000e400300c8169030000c00040c0e00c007030030750305000ca0a1800a034020300c030300603440e00504100b0882036000600306c600190598000304246d00d510415481a5070445019036001c0c02c40d032041c0078680c0100800c40007081000c0351 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 656105251 1250 656104001 656104039
    0x1b0301082a1c0f0b07020c031c090608040f0c0e1906030213111213020a060e0a0b0f120c0c07061d0d0807080d0207061103090a11060c0102041d06 64
    0x4100c000b5151803080d0810410003001c0080b000b10564405024883d520b44200c00030354079009081243e100b4855030907a2091442c02d107504419020f09c0e96500340815040135010b4490030800341c001c4450300b100f001300ca0b01040c9481c5640e0090011400302891a04103452151000000c51240b813040750710b8040100010399411011500100680b000460144c400072a10056401540e01a05001d00305d681000210141c540651b40740b03034030031101014550703120703070040354003075500d03041c19810409240092094155520140080d09140c104291800d06003e0303602d00010401d6401540f03014020806011380e030424040a00541801d00d080350080740042008007105c010305801c54019200040c3d45002c2c003001c0812101e4094005800302d580e58000d0103540001d41c0070b0351058808a24004c92800c2c24a00d98048902130031102e002812065200c0c2c03110b2030f64082c0c035090940e00200c1000410a4a072003800504020b0482c400050499543c00c140415000d00040903039200b210443c4103180c139400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 656106501 1250 656105251 656105269
    0x13170c150903090301060905070305010b04060507030c02040e010915050c0a0e0d0309080607120c091404051f0b0705100204050112050709170c0111010b181b0301082a 73
    0x240d80e0145454648454078220708501c21031400c15019400c0c102c01085106054004038080d6086a8040040740c0c3e940b0001007490240d8051000052410840340c00840d200e560950340481c0001c00003e029035015040750308640703a600b402c40e6030780c10403030401c168802c09104c0d80354050503280202e4030b480c0d100c40004090160b0149820310602003002d950701418801d82a4401504500381103481c40e00b441c04d4087d06030840003441d00d00550034980c4600126219803508011a500500c0080300e81c0800010003001d090010b1180600b111075044200321000f460b50010010031040310b04540c0c031100b6049c25800c10740d80030001e01080780104010026070b6802144081909141a000030b078079152280b04403910383e10b66010000341840c6040c2c40e215003801041d000500c0200740c84450942c081001e5450a0b500c407180c89a0b401040d6000103004900b18110389540000c2c0d454003242c56848043c4001000d41007a04000702a6100441e1a0b01040d1404100610a08440442d0103000410070000320070003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 656107751 1250 656106501 656106523
    0x1120213051c0c17070501050403020f0121021603020f010e12070302010b10032909010b09030a050a030f14030c1b0118150c08040f0305070302120313170c 68
    0x4240c1486200c107102203120300a40d199002100d140d83c95642d005640c0b4440808400c00454016030500281a600a00c00c9070220381c5d014140c400142c03580300056a150b4041e04100540421401540b090312000340b006000540310000e10342c600e1032560400a14000d400303440981c50380c0c5485400079003000006442c40480c0444c1d00b03841e5403811b4624049024100c096581500442112081001550560081c1201c5905030b10303890148803176480e40c8003210b0000103440360800044c00c01409500c83e80c800a140c0100050222103210354075a45030781c60700c3c00001060780016080d121800245074080ca8146602e010b0044c1f080c150f080c5066501e00310300c1401ca40c1c103680c81d1400c440050f524000c0d0041c4c1002918110b550800703010600341080200c4036095180c1354203142c100c0c0e50301c0301405501840d0207190814400d09081c00350b60b5007034855512494003a03043d03100d1a15000c00120048000314420084034604181620700d51074041850b03107502800401050b403c0c080300014800000f40c0103806 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 656109001 1250 656107751 656107759
    0x609150f0e1501110708150c0a090623071a010b04030819090510030c020105181c140c0f0d0c0809210304080304080f0a030c060225110112021305 64
    0x21001042c0140c40041118020300464007600100040889010843c000b42c0051f1071468842030f6208411503079244140021880400e0741410140400e620131071b84400020300c0100311008081e01180a1314084d084494210f50440044004101c0340b0054107085004000040105007454110b550b8001c0a018540c010440502c0045101c0e00a5116031900740080101070b003816424040345c080280540781592814000d50700705000300310703890b100a2102c00695512000f0706001080c821041c841d842158807108200131003864050402c81030b0a0040a00d000c4075402404000710140c2d182c0d0a100c411034a180034013076410070307120105100c0c104860740003804480e14035500104014400d03445005869241052002060200d40784800200500690310004120ba84802d241880c10340d941c48408001000070b180200844006843c0360003400b9141140140c0d9102d440c100d40000c4600502c060040e21210000101030f01c41d5600042001c001040820040d03190400b80c505190480110348515405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 656110251 1250 656109001 656109031
    0x101d0f070314070e0108060a1b0c02240f0408070e01050906060306040906020c0c0f0a030822080d0804200a1403010212160f0915030b040905010609150f0e 68
    0x80007000303124443c0600007803003010005586540e91141d07240422208407003a50302d040a9807260071180d002826803200f196031341c4030b03d000142d030902c4022041506181000c070315811031102c01c24000006003000c040c3c440011074441c1d280c0890745103020004c1d4441001c3d8030b0001d0040c03001c0e81740c40603499407103442034a145940e525128003240090040d4040079004610100fa0000c8941c4007040c2034007594070803510300d648801c1c09410001101d1607480000e0001c44200600801903e00000081210004a103000d030b245a8402e9940d0400789450812800601c041c01000104280040e0244178030011056480d21400d5810100314214003d015a441a0b46403644030640c0d503500350100c0e9644039000c0706140c0b031030400d99000c1c05400d01c0341d40c01c00f002c038500103001d2501503c5600b002080714070100d6810b450049151054009284001800740c2280c0c03150056008124240560070040003e0301000170f00003145003403420a02442c0d004a0350201c00d18008000d8100440d03050f60b04103c0c44071400c40e03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 656111501 1250 656110251 656110283
    0x206070309020111060a0605040c02010b0607123f050402010c02040b040216110a05030610091104031b0e0705210604090203160e070806210708101d0f0703 68
    0x680c4004d02008940780b80715040400c40640481e82220040316402c0e2002d1001d0350004400307130f0a031180f00120a41001c2c080c85104081b41031002039241c103214604044141003002514441030074810425410241c2c0083c501e186540400703501c8503144001d03103408208034107040d400202400c04c0f000001c0d11454942003007148960359a41140d10400c600b15113200003030070910700302c107001000320745040c800c040da26400038844c01d011a20920414202c0c1120820904000084000304400c1da00d40c000d40c0001d000200001e052024440001c8101034400300c040c500d070a00784541054000c1540e81009010f0081910010414520300100340c001d1342610456501c20f40800d00400f45d000380690b2510400845260300003400c0411402d035191860011303040d51311444181c0d0107003070640d802a0404522525420640503104461049032051016181c1c0e103030782c690015240c070290b102c0000f03070b040d80d40c2d20b90b1542c082403400076442d100c50000645540d100207604681c5031701442c84060031741c2071442c4a042d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 656112751 1250 656111501 656111507
    0x50f010c1401021303050a020306010e0118090510020f03040605070906020a0602161a090d0c080306011112030108010b0901050a0f0510050702040501030b0402120f0c060d140f041b0602060703090201 87
    0x313031144828010526525a403810641e5440442e407405030300a0040e1400407402c031a442d01d9090503101d05030754803c621010b4101d140001c000300c020995aa0240c000600c401800a000502c104514800b41a8070b900389070510000f1514083c1c2808140420040100207490f0045a01c5190b607800c9440181c8401281c800c0f0f0201c4841000c0040c42e08429100040001c01c8044965008110180403504440c01803101541c2666004402a285d0502813000908a610801c440d0388012140815109403090000070800142c0003038025089994480b4070031031240c148140010f005200481e11905040e16041c09480d100741b981c000d040c0145c000018420303105000c0c0086920103940500200060341c0d4031b007040914243c068030102d202d1000d04500f40d184650016559400c008614040c144400c2d0390020800305a2156480d540b0940e11828900a00365490380010f00c20241e2095580040c5010300c2c142401922001411100d042401824400c0b503034005016540503e95080019540403940016 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 656114001 1250 656112751 656112757
    0x209070e010c050601240206060f12150903030121020f0d0219090c030516120c03240806070206010f050f0607050d03090302100902060d050c07080d1401050f010c140102 74
    0x30f016072090078000590711b86a4001c220441400c80c4943c0c10250002000700d23110340003610301d168030150340300c5800c1c0c5525102a1041c80003455100f1034100c05d08250701c0c0f02c81c91500315030038102508044010800350000203220403250100c0c0102c0284109180d0000392140b0621941a0250410450907800c40d290458400013101c20709d24042036059440d020f001c0501020404400042d0070310000c980081c481d42c40001c121603640d154606d40d0740701c03c1c4007036000307142c44111801016110a1142c1c250350401103030030061410000c0c000c503030300d06040c40c040c9046005441c1c6811907201d040104240c2c18a2500007050b10301c100c4080400103259000203003980181a40541503006501007060355640542c000c200c6a4400d4007034401120508111000301c4500c804040c0d0000001c10450100300070607446035900548402100c2d003031001c0c03600c03001010307040410749150700e42c2d03980c901c544000c005094007801000300315841c544400e60b03440000e000e40154070000301480d030368540d418082842901a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 656115107 1106 656114001 656114003
    0x81207141c0c051e180105040302090103060c030f060608090606060307090909140312011703041a0a0c050d0c0204050f09120714100b03190209070e010c 67
    0x7050000d810542140303030800c1400c1200c00c8403003002490b240341e0495030f104482c2c0c584101e00c002c0b904a000400f540c605001d0244020001659161045810340c0c0d40b0490101d40007a84007410b9001c1e000e440385c00310718103040800c00300d00682e00103c114403481090f400c690f0252182030900c0b00310320087e070b40a0009160b0090500485200350030030080030b40302d03581000303100800307884036419900a00d1030f20000b60900401041445a43c407552003c00ca591805036241621304a0500050400c80c002c2d00f54002000c5501800315000300758030740c04030703403c0002d48000b20681030000704007101400080303101368901008121138900052011b4403c110b500c0052003140071020706034400c4d41000200b10303520404681031019000d014440050f015104207804980103400d00101420301a86240203e524000f044003040581c5e21409501e8202541d4108112501e5810004a0380c160321040 = true := by decide +kernel

theorem cover : BRFrame.Cov 655935251 656115107 := by
  have h0 := BRFrame.cov_init 655935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 655935251 ≤ n) (h2 : n < 656115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
