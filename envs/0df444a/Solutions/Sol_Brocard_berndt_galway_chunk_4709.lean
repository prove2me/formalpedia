-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4709
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:29:12.457785+00:00
-- url     : https://prove2.me/submissions/1e21cc97-b2d4-4995-8b20-1412647206d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 846762589 ≤ n < 846942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 846763839 1250 846762589 846762601
    0x2030d090e15010903060501031a0c0301051c0609021206041a13020f03011e0f0e03180d0f02060f2a0303190b13061d1501052b05100e 59
    0xa800039400c4426030b20a10342401494004a40d0400c4c1c030380001d82002d050400000030000003d100c604170b0b095880c0c4440760b907290760301e8200d2031703100c28451a0351000d0b107031007594542d003200e9445080440c030464000520311400d07400b2482d61300d00414207400682100c010001131004458503d03d40101c0203c0c1c0e9040752400100e10408a03282641c064051003481c2e0b010202918254000b110882080389550760307500030043e07003001914015402040c02d80c20480104903016000041d91400e0a104806500921800040c40f0560003110011f44907a040d200040001d603c454000300050a070103460240e50b800c008014050502941d40c0c0710f8444145458620307021035000c41680c5d08501c4441e141d1500703103a50400500644540f0708016030080c9d001038a54001205540000101c4195818446500c89803034107560b0701c1c0c40e040390080080311122044242d2588504e00130180160300420b01079264002070700c0b224443e107000001c03140041d524000d01c2503e13006180107030018802803405641c030345016 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 846765089 1250 846763839 846763859
    0x2010c02030f0f0c070306020c161a07020d06020307080609070e0108070f050f120714190509120d080919111507080708070c0b0304030e360402030d09 66
    0x10401034881c040b004295594080c6281c2c044031800300c020011111400d8480c140354009501c41c0c48042c240b4030a6004000c014441650018112010b0100402c241c000043c4d65203100e52058404a9004840200f0980052103920240d0b000340829502c2c0940c9160a030140480580040c0440083c8031001d4081e15250383e001403000e504c01da16203050400c43c1c0e0414002e944a02980109510782d0401181410403000c0382816207110f24001c0c2e035140e407401c1c2001011032251080c440d0801000105d0450400e059005100030440000d000e804401c0003c40303150705a003070864020f2882c00041203802800790fa500c00308603203108008419084e81c1c07802141e0741c4007801402800d00442c01040b0505102d0501c40134a029100f041d5003220703625039034031518030700748410f0f038403241c002c46540307901c1c02020840e07041072000d403885294140c45204400c22000204000030408038140c400a25030321414010150348205000c070f10b48080710380090542010301c10182042c20031062340e0708008030940200803203895 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 846766339 1250 846765089 846765097
    0x90c0605120601270b0d0605040b0a1a0d050103061b1b140307061b1805060322050304090c110105090606191a04060e014503080a0f02010c0203 63
    0xb09007040c1048591000840b02210407000c481001c5a9112100040109102005119040820300c08011140d2110f0400003150a0914150b0300174021101c240840c4246d03a0140850000d40620f040c00c0c58002d03420402a500c00740c1044501a440350002e43c0140f11483d04a800c4da401070a095920f10081d800704001061145005000021b42490707403101901e0600c12243d07055004001405595004407244a12038140c900d00d030300055001101c04803490079020001c0c1950f000510003461503d4a400342c85c148000c46202400aa4810100b080010410401000140300210010580200c101d4000c0c3c160104445040c4e0540d04ac201008010400810040d070303c940102c0b4903081869054881e0100940340d40c12031400c501480d101020302c130a02c940500111400341d0b4514a248010b0401110306820703c50005c44042d4041c140c0291004030101c105100500d908448a0254031401c018181d07810345a0090720700c0c550004c3c075409900d501c02e00004540c60140000e2000e481e08400081d82d80c8a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 846767589 1250 846766339 846766351
    0x110d0809131d030702030609121b0c030a150f02070210031806020c01091e121103160b1503150a050a020c0d120c03060e0c0d0b090a090c060512 63
    0x103a519030651804003240d005031441c0c1111210140601c030140b4036550341e50b20407034060780320380309540c00100b0500000a541501051030400c40e0704244403882002c007811800d0030010b42d24000e0181c031510710346080001d4844079004101411507540c0c001508070441c0d150782d414000c1580100308031000340e11500100810700c0028680050410034015180403940ca10301c800030318050000918086040e0705400c030342051401200040344800d00c081082c2584031201c007000b0800f0744107800d9a60510300807803004503991305060a481c6810703507000b01115518042207045880d00301c0e4005101d40004541030402124030103500600d698070305208841e1a04038001d040c00c441c5911813001030f014510700e40503500300305126400c0f642600300130039000d07107600441403902003003901e04034030386044900c24001c01003190010709514402d49c5400301002041d80c0300e2a00c01c10f0a903102c60078544c403a182c94190394460f07414007800080d201664a0310804007140783d4000010404c00b440400210f191030502c06070445 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 846768839 1250 846767589 846767599
    0x302010606110705180a0605090a0c03050c12070e01050f0c070f0f030201020a06111b0309031b010905190317040807060203030c12040609081b0106050a2103031b0c110d0809 76
    0x350f50103546d400980b05580180d6041007d900a2101203400d81c1c004440c07040040d2018003075941c8201c0030b020305000700310302c80d81c0a021110100341c1079802404890307030940d03040c50898540b0710031083c038000d01c3e40411a181c10681c003044041049294050300341c00980260075082c0d450307625640000b9070b510711811f0050501c9990b2001c0c0100c0d618104102e9956809180c040100344481c401030a443c0c1e045404414024003600010790845a40209107d44140058650358041800c200c14404844181941404802d01c24240400030403c0c02c06000b0445c00c41441c01c0f0766070f5092501d410b042020a900c9070f4107552060042c44403100011040d58411034003c900180c0340c5e80e540c1072074005401400b00c00390409070f00145656a503c0c55a0707010010200382c0e4000d220076981d9106015030701103d48030790400303150015851110b4070a16080c000350240a80b4002c43d04172080c80c03100701903110f416840c90100c0d907080401801c112603030742442d012083c201c600c1c415500240d01c0d100c034940b10f008107040c410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 846770089 1250 846768839 846768841
    0x105090c101407020d0606050906010809120a1b0b04030f08090c010c03051204060f0e0c0d06230c0405013f0f020414090105120a021e0d030201060611070518 69
    0x180b5000300781c41d04203070000d220f184940c1180c14084014103090007034900461903040000c4d01940640160390041d4034132002400e000311000c44031380c1940c0250664100f040850107000e030096a00900c6500068018208440d06007400d18000e01354000303c6003841d090001044c1003000c0081e01142d4401440001e08040c7d094110600d4216442d00c15201c038000401400001e020030f01a01d5030144001c034039600010440c22042500700c5903901041c02010b61700425901c50744000904a410030001c08003404294038000c8004000040390400840c0c0070345c20701c4804a0304000c15079110703a0b0f550341a0035100021441c40c020b980604181c9900360200c18140405881c2d003d000c4002d41e1200b4810b0700292011529a5265203a41030000071400c600d07803061260b980045814a0b0101c000d0092341e812000501d1025410360900107590326030b02d0b00711070135040807401c14255100e10841540305480780e4000200c0f2403d2540160070745101e0180329170030b603101c0c0e10248030a841d502010184070850b4840040c036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 846771339 1250 846770089 846770117
    0x90904080705100c030c21181208061c020d14123f07030b030a080a03020a030e010b131109120f010b0102011a190b031302030105090c10 60
    0x42441801e00c002c10b148a00250021003943d80d6002e5404151960780a020200740c1a4003103070301204002c030300302d00043c8128076594011a00d0380300c070040d03c00c6115200507151041e110100040c07142c0c0c800201185042e000c21509243c11f080070311031118491b01c54010f4000c1a00440d500c2019540b0040134911600302c14980c84d4800c2001c00c445194011210b0796a201c0d01100110001d0002565801c00e03031507a0ba8039422080100300011865840d40c064052070790b030a601200a040080c1c58150180607a40300100840c1e0714000422421550342c501594600304140010300719018165502c0050340b40400c0d88240756150459481980f0072070401150150b1181c00c80c140611501c60324652001401c0540841d03018007145030a81106904c0c020820b550324000164280d0f01d030303120401364100d0340c154041c00c1483d0010b11260a5000c0b84429400280c4401303030190603a0081e84c0c00f00d046901c1481c0c81c01180303024010503500803055405841c0d50031102010406902d40e0950000c1401105071445d08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 846772589 1250 846771339 846771353
    0x270b0103022106010c1b140d0519080405060a0507020f03011103010b0d0e0610061211030a090311060f090705010903050c042403031206080318010e0102070e0c09030f060903090904 79
    0x170641d0070000c1484000440b0400000c101e0040c41650303c408100f686c014030030329004901403040707604040500518491080014400b190141c030455481c10240401300e015141c00c07014200c60303030b140d499865840042e0700400ca03208440e01441c038404c4e03040c010306c410b603c1c62800649045031000c0c1e2145450300300f4100c104010300380d501c90102c8c40f44610030030040d035400309189100446180d605c610745600f000d44900000d6802240325011801e108001081010385650b01c401201406407038001e41490450b151203040ca0300540d0509040090321b002d0080b44071007400240010002420304a82da240b450303403400d0b243c0e80c01f040c0701c52149507982140650742c2d01142500100a181a007a00321098603494003600c403d060b4918114000d18100e004208000c0010071031b0614607034000c41340f040e1104140111841a808140e480c1140603504c40014205181000c40c3c1c0603000240d400f0351100e210000341480e1005074410344180d075005206001125401200b00c9030140025945141203555a0410359 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 846773839 1250 846772589 846772607
    0x90627110f010903020301051009110301061e210b130c09090e0f0a060504030206071134031a0c042603070f0b0f013c270b010302210601 60
    0xb94144d401d16041000c1827804c002504161082d0f6682000300301d219002d19401400300f40105000309140e01e202803e039010b4040803a40d454a60324141c075240385c2441445080100317500081c2d00058542c50000302e18034110355034005006010008101e000c114040041a01996200305034100340d84400d02d2034080d4061001c0c031009242142210040b41c0f030381c03070420014041200c0641c014080c030320105143c0b5100b01d0103031070900140c40040a202401100c07498002052080d0032090701601010540440141c1ca4000020f5010319240428602c600310030015000004207880d113000740c10030081c4803000998041061800130342c01051070800c1e5050b04c05203548070f0450003501c40d01d0300004800411081c090258030a40103001070590590b0f84421029071000a144010900d61544440402d00c84036007107107141c2c4a00d0108852450399881c0440f100c00c5414440030014106e00b00003140e888aa03600032100341d040d003032900f1890580d144040c02203406003560450138121300322001c1107040c7e102e49188 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 846775089 1250 846773839 846773843
    0xa020c010e040e03160c0e060607230f0a0611040b03010b0703050409050f18060c0315030109021807110f1b03010f0e061012110405100306090627110f010903 69
    0x5a0361440380111940503c605a501102c000320761440104108445024290041c8005840582808296500e0bc60001d208107240354071030448080c103801403402000301805041002e000b9102183d082d0424506440c3c0541882007a008108020841000c0c6034040700c0c1150700150180e5255000c920f0100d419109a0703201c20800ea044c035040c40403001c1020b881c03600400c2d010850309050303020b0403101910b0741c030111034641582c2d400784009101500760700c0312841200c81c010000036042a69030300141c040c00c900010b548004084c0e00800407203640051510b03030010301e0714005240c005c0f035044002d81d4401c1404100f10720801f0800a5840c544c82c250410304d000b174480c0100740103880b400c1d8803d0b9a603510444001200c03031800fa0002422a1804d44014400c1ea0030150036107003c19200c0501010b014098a91007039002e003d9800804645203104803034543e44108008212082810031038020420318810885003400400d482d1000211345d40c200300c2540704199a504803004200c401aa4250115800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 846776339 1250 846775089 846775093
    0xa06050c070b0c06011508070f0e0a080a12110609060a09060b06031e1b030c16050d020f0c09010506031f0b0406090e010b040e04030e13020c0c03120a020c010e040e 72
    0xc03c0b084808602070341643d44000315241c6002d109001282d20b6841900c0c40c0c8081103c801542c2000c0b41b1504020101c1035000e443d861000359280109850f200b000003094600307030803482c007007464a03502040e40d0408443c440010015810818000c0e42c0b10b203c05003911f444140e82e81040410010784c0c1d000000390700750041c145600d0b4035010410b41402c420304400c514003410305000180c0ca201e07130090990042014210400d056603100700d854140c6601100d150f03e614070b2004180360024004000d61115801540d020341810803603142507034545500140542d102d0a01a03005104903268a8103036640301c056a0b00c085904440150101d45029813600803040700034000030702207905074012880900b162481042e0044580c0d9440300329515000f103011b1020f05180103c04074012a2003091008210359008180325400208001707503070304170f030301c0501455055088004246124681488010380c000c07800324520f498103000d108001c2d2218440d080c941d040c408040701004250712980c1c0112541046102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 846777589 1250 846776339 846776347
    0x914040c061b0f0b090d141b0f01020a0c0c2c10030b01060f020f060408090d0c0f03060615020105100512070533040302030a0602090d0b0403090611010207020a06050c070b 75
    0x7400184243c007202c10b188076106070302c00c40302d9147c400c0c1d40c491152100c5c82d0b0300034100400d803000c403458018220000001482150120070300d05000384020628040c041d25040325030f01d80f6160000d00d512880e840920500c1007003040c00d035032134240c02070200c240301890000c0310950b550300c1341c2e942083c410b5040607103c141e00c40000320b01c25401003090040c08410380c0071106645d10641c0c3c2180c1d03902084400820154041c02a84403d0824081303142407648148404421192100381d000554086507000b80c49da280c1322542000a010320b0100c5d811611000e100078081e0f132038074601a8000074050301c00c0368011090b02d08c400310740302010700c0344001030070004000c1407841d4082c0342a0b990701c1201407800d0006840c1d00d405010080c1010313007224100c03903000e0054a0803ca054940200035044601d05a42040000c04500000780c950380099200f81d22030746071121072506050008000d00000e0744d032501e10f68410011040540d075076404c04000c99015140c1036580f04506d80c1d40604100c0d00d544001d0003184086 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 846778839 1250 846777589 846777593
    0x90f050606030106081605012627011416030207150f110c150c1b07030b070309050c040c030213080a2616060b03070806010914040c061b0f 61
    0x4944680078000031002400101e490f104003640f0f840740300a4804000000d6a003c000650092020b030a800500050030b01180305a643d8403c1000c5040711261a42c150844001801c410787c1e01d01740b401d480d103440c001c0001444a140480c490000a0880303d11507240450341c0d000c20b031003a011242c109a0000710345481404940b1400058001420000c24503401c045d261100c1d1030052095403003443c0414000c0121018800100d05000800340c2107030f040001c10001c402c0c4620010710740c8400540e824005100381c030710f9030400c0440c894014001c4c0c2c0400d4140004c510110364001203101c20489d04450014804074145000e178020310400c0c000700002500b00381d00152104010546840c1a070044011515494403400082482c82c401000120054020312040219059800d00140c0040c03140c400042c02106010020780f40016683c4451801d5000d10010b1058400b0b502416064007111825000c49082540c1d87c3c0d8030f40c0806c2c1c060b900401054000503d520f01c0c0da443e0019800c0d4004140d00915401f44c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 846780089 1250 846778839 846778843
    0xd080906040f05180f0a0c020a141f020408280c1d0705090a09090f020429060c060c13030c06050901080907030b070c0501020717031902040e010303080a090f05 70
    0x2886080d00c1245080c4e805511405045005481503074240c103503184d02e0703664030301190061400100c488110311074400a440080e8003880c408030020402c800809404c42074040490924400b07030070001e580f50041c0b008001030140090418064846000e203c61001f05e98441205000c001c0c21010749201800d05000070810940c0181055000e000070030b0301c01c80d5031840b0041d1800e2040a000b0342d044404000c04105030b84d155030040d030321144101414102812a6000241a6009000380403074030030f4031f20031803108280441042c0003e4403098403030034100f0100342d152a4032010300a2174086030b20070000d10403c20f20b00701a0504003450380700310501526600c801c4024190f030002d001030b0f40850184170204100788400124007085941c0032030115042c0d501d4002c12514512900d00c220380e9503400703000501c005000d2a00c0718104000d2030a2007600c900c5d042d0780c182c2300014889c040c5005031740304200a02c0b0707204646034180e05403a0076061106041d103c40402000500e0511070107030088102c40a908204140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 846781339 1250 846780089 846780119
    0xf0c01050c01270c09050606071e0614071b0c090c1b050312070e10050a030e03030a0b010207060f020d031806020d1e0b0102030d090219030305030109140f060d08090604 74
    0x3290752000d800c0c0c0b909005c2c02110410754205510000174424903000420504101c03400d00c0e82e5201441910110b55034140a0340c69002c01003509c81c00d840b0410074440d5100400303000000e00d80c0800040c0c03482a4555445c10b407500e0041e040c10540f1a00c480009a00030070b0201440b1030000c04010070040304d410001e4030f1360005066842442c100c0c2d008100014400c0110440851009110380350b00c102400080c3c0d4a81d000c2c0c6401e105042d2110544003a01200340b020754464040c0314400700c1c0800188000a0030882c0a4100c0c005204007002d00d104400c0c2e00003813109280c0e205003800104c0141d10945024407a001a00003000c0e02e0001503020441d071665080300010005007128a411503c40500e40c205a40911070800d0041e8010300103504100c202d9009084030900280551000c000100100d03044050690019400302c0c0000004020904c801c0c45010740c0c41c01c8184c841180390501421585034142c018111511030440030f19403a0520011208482206c500107107850b565076039a058030604114 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 846782589 1250 846781339 846781343
    0x806070207140904122102040f0806090d05040311031c031a01300b04181205030f0f19020301060207080c030a050a14010204090203010b07140f0c01050c0127 69
    0x2645480d000c0642c1804811203008903400001e4400c2010051021a40c0b182c0a000d004107040000f8041e280b41da240f440123001a2200c1d000c2c0d103a00908000c640d070b14020014001d0480d40e48000c03884035400b81d1100541d030681c0d07031043d2012401c8890700c0010746031401800c000a00c0c500e041145034001901a44020ba02d41c082100c9044910461001942c40b01c174000741d44403501c801c0c603081d00b20030075980c01c030381c0d94012115200090713030359445011508a540c4106607490700b21007582e0340b4007842400d05030541c1602c0d43d4603180380703140ba21410280482d0f5015064150840e04040804c00b05078140d00d8040001c002440215100d40e514100250b6804a6220f0350707070103005000d8402e1440c200451012a03a43c0c00034010094028280d8808098175030481640c0020f550900003c540d4200e640029802011454000d5480d0b02e80d0b400e04650a001050712204140e10041d220311441e43c0c0072514201c0501c09080660b141c0800f054942e002d0040400348000e8a03801c0c11008818103036545541f01e000f4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 846783839 1250 846782589 846782609
    0xf090506060f09010614190503100906030818040e0f070f0504230915090106030209060301230a0b0409050307030f0906050d2d060e090a080702190806070207 69
    0x600c0320810312810100c0b0010103500005488010300c0621701402e0780168280003a000c0b03610304010307101d0041425902d81c41100008000106100404250380d0856024142c0414108405072a40e07440c10342910403003036104111f02d2041240c1d540c03507441ea0b0044100d2a462003d603102100240c42c1d10ba101d44490080a43e0310b0700750348001c503041c00c0600c00c1620007510704c01041884000102004040000280400d209210381a004c2001e0b0760800c883c18020030b803110012500905510410121240041441c0d00982c9002d06609a549140030964003910600c2c41d503200d162260711084002d0040070700b00903002401c00c0c0300c040030003c001004218072806646c6456910344420707401c540c2c1070307100c1c030902c0e000034001e001041c6290308903440010318412182c40a00400c2c044080d0011b000113100c2c490868640d5110108005c2d031000842c99800401342003d847d5032010341d66502268007a54402a011b070b440c90100109041d11401104090a924401c84020749004c0000941c0c079000c0380503c100300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 846785089 1250 846783839 846783841
    0x1030908070c0608090a0f060e031911011b021507050c010c090503010b01020601030c151806050a111c0c05070b04120303140c120406200702120705061b100f090506 72
    0x1174400815400341d155401040081c92040b20307110b80001d4284010300d00914003080200303064075641880d0b188090880b9884145400e03407580101ca08443c041c465510218010341c4203910a540d0100310460b800c40c08540c40e110f2619281011541e50150031026248c9600c0c1c25101c5150a0300306420750101d600c118001d0055074410401280c48401c28131004004180343c1c81e0500c40e01c8110003980d001c421031480c0400e1954805a171441400d4180d600070000305000159040009038064041d000510306600280111040c0d240c4202d0303a1300c1d50785d51100c2000301181341c0a04012050000c0f00050810000490310345440e01c940034182c0c130590904601091a140744514072000b12a01d0078801c0d680c02d80300d1401d040e0b5842103911f91010040c0211450341d55641c0e400b140700550b104032140301060b00b601a4641120b40706021110303203502906401984100010456a030740c5904480025001186c00803120030030408907403801e800c0428000000c0d05212034a200c0030303c540e01c10404103004400715211 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 846786339 1250 846785089 846785101
    0x15060317121806010302091b040611060709080d030c0507050337020a03081509070f03060e1902070f0f030804020a0b0a171e040f1a1e0601030908070c0608 68
    0x80b181050360704030020340040004001520380210666070025604200c0341c03018100420031211980990406004280c0c1c0100c4a0307883d8104200980d84a146414240700d40d60401440c9a0359547d1049854101519000700da08003501c51007e0b10061944081103e0b29402411700300c0401c002c1100000220304880710402c0401c401103140341c00c1d884c580f600500200011620200c880b940000d00b00c07400c60400b020340032a00d403074030441103108840d00d03508c1d034481c5001c0d0301c0010103541311a40f00402c9207940c0c4c01400300070004d4404000c1480d1391000c00685c5d5082c2d0f03180c0114000c030800c001929042c942c02c4510289a044118148520b10031503284682c1c43c0c4907039040400d805009920740001e080098213005003003e610034550060801000171240b032a18404072000e48008840880380d0021104842040040d00d0304100d81a200c00918000149002c0d091031003440d81d03da1508440006600100c0d00da64000d40c00b00348003507003000483e59240321030705084039144000c0c8504000a01c0803000614 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 846787589 1250 846786339 846786361
    0xe10111317011512020d1403030411030d0c020102300c010618050f040209090102130311041d150408040e01081522110f120615011b1506031712 63
    0x84e00d4100d08528124400c40c1c00780031062020450482e462900c0e0400469103180400c003851003944034004050064a80394181410408400354071000c3c4030300340c406940144e03008102c100c54440c400d10f40800700c46545c0b2071010010701c10380003050a00f50015030104c1003001900f00c0700a036019103404d0b920840000380e000c421a10200c03206e640c2800184042070042c0340c452001342e0400350800003d802c2221700002d5145a119552044074040d5000c407003415a030130725008449030ba094003508039041005122001d51112a4005200c01425980e00000d007002040303c03d41c0c016202d031040e440e00c00c2da15412015540c0100f0314202d41c021003208001450032030501b411004864081e103400340c24450603034504c4450420011095032207000720b000c05021f5152025822840b0054070300400060500c0c3c40082c959006061720305040244145010040040340c1c054051555800020020b82c0807200e808240284450380008000c07007002e9800342e901c051000b01500c000c3e640241003d4254a4001c6004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 846788839 1250 846787589 846787631
    0x1506030a031407020315160909151203111207060e0f07050f0102010204050d0305040509010e16051b0d0203040602010c18060f050f04090609050a0e1011131701 70
    0x8000a240c41c5840d180456803a01030404584054200e0f0a06503840100d420346c100c0c125465040410741543e00c10403c1d600c003001e1002888800800c0003009500791480700411480d025400c00c0c2a04005031004141c8564503041c81500607600b5569601d40c071040b5450141e000030803d80d1400d00f41b600d40c404400e00441d002c01c09283ca1401020300314601010302003400300c0705091a0540d50300340000503e07912640038030351007588a0754805a8460600040060f41d02c1c046c1c00c440601204201003100c1310000381d000c111042082e0626684030084a40c0c070400c04c490030b0122142e03a0040c200e2070b0f01c10f140c00001510039140f00c0d80090040709000c0004881100c000b540501020240d00801c21401d4000c000251140c491868114500070741c420903049184d001d680440e40080e901c03501004246594800d442d00701c032210307070240719403403414174090f0707448a02003181c0180c81e5440640303600006810007210b285c09880c0b503080082540e500a074007481490300544418950818281d030003a5491207083c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 846790089 1250 846788839 846788843
    0xc05031e04171e0f0c010806190806040302150f04020f0a050607031d2220031f0e010b120907180b030d0c03050f13030611032e05091f03051506030a 65
    0x14007850020781700469411001411142c0c000d03c00400a5201e9045009c244000d40580340040c8114185464002d03c0c01c010314070b410003009981010301a40c80c084a5520703800c550115490040001140005106520a80e01c01c9030300000009604080640001300755110b40310301036078403411104050602c2488820007401c0f14407191034246510f580070f865440031389000c0c1165162040d020344412280b84c0d503441504c0582111161540383e00d000301b542051503000d0510700060352000d5140c81c00c00002401802401d0700003144500000e50003260401100c4018080c2046060030401800d480310020108142a903000e40181040c105544d401900b00005256055407510728210f264441001da542004221400d41c03461a2000004a099401044110100c121500c0d58a007003003100b409a031602202c0b5031640880340e0760320b81c5001422541f42e01c102c400c241d90440f410756525407910356549951301c0020f042294500c003c0284100003a8245513922080445461501c8800425a6070aa80000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 846791339 1250 846790089 846790093
    0xe0c211e1306051509010f0e100609150215130c230d030c020a090608060609010b041a070204020c0d020f0a1e0302030712031a010c05031e04171e0f 65
    0x540d800051943d80640c3d800305080340030141c0c481c448000181c803000d0a0f80108000421042c0c10700138401a0034415410044050a03003030702518210001d407006105200300340d48100b99400020000e030003400360490740d03680081341c0681c92500f00c442d081c0302201c900c030543d01001d07942c03070110b038044142a100c52181500c52240d880c00c1d200e04108098248034810450402c0300000240005807a8240d03d00040d006a01c40410f034141403500300c0e4a1f102c802040c0c0da00c10340650004114054404003240c05440b02104494a00e040506030004c0340e208011009420600c00618241462400314561091006c903900b9124110b071140c005540d240c501c0304020b8550203c441c025100c0250001c0024585e501c02d005580c245001ca4890980c500742c0118241c2c0404c1c1c45940300601107401d80040d2102110908280c62030010540f505992401080f2130800280c00d4010552803181d40101601d004004003010401c0b9082d1350b524864030b50301b211402c0410304035170502074a800c90012888804034400c0c040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 846792589 1250 846791339 846791371
    0x11d01030510230103051018030f0f030e0703050a0c0806041502090109030203030d0906180305040306050a0e0a110102010c0509061602010302090406031a0901020f040e0c211e 77
    0x820b1030000e01d00040003114514101c0c101c000da500550b90a10700035402100900000081140b8181c02c2d43c0e071003841c2c561004914445d0301e00194000c214200c0d0715040f07244c1151180400742082d03004007005890070050b8480c0d21800810404001580800c0500c1044841d004969070a46265561010349000308040140000035441e120250b01901c0c80440506d007002205a9a802003070440e44000300d22010030b07841c0c58082050120324059000226001040c0c582d250106440c020301900440c040244026100d0b030105920300d40170740085028110031001d407030b017420f000d20340b00c5001900142268055400c04080d0201c0030300420644940c3c290152801749031801c05041d8071039901a00d60101d0606900b84613483d02a11396118010145205016034100c005422400800c111402800705000360b00403c019030003a190041664104e80310400100342a031680c080c0d02c40c0600458441720b10301c96810300e80b40c403105c4981e401c3c1d0740103088191080246e820b0003415960b00b5502200c0089401413a00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 846793839 1250 846792589 846792613
    0x30c031221020c16091d03040b0f09030106030507150f14160312230f0705190c05012a0f091202130603030215090309030c090a0f14011d010305 63
    0x90010300381c3c0603002054481d41e8203507110b4034000062a81040300e01a95481403070203101c1c001203c1c5100c4002241c0194141490b040d41d51803188100c2ca43c1560340c4501284487e6152002d400000141d9405002c1ea010395454800d82d0603184003802d035140001c3c0034101082011130068141c1d120800300c5645d00352400c1007955446170a4000c4a07400ca0800ca510208151701c060b82c0d1081500b0079034844650403007803980040c040170409001e805000d10202507414020950340020884010005031189000880d0300000c05455406141c034001d030241d400c0041403440803034200304200c9803c0c0284a03c0300082e404900484280c00e2001c0000040344001000740168012141081c550f43e1006100420041c10900c0810580313011740e104901507800f1004e100608145101c0442d40300d00d524006508005404000941d02c0002c200710502503d1001c0105203a0035040e0405e036118900c071801800070f00c04000ca0490002002d10401d00c0c11a0501885200040089100ca0407241c0000c000c1c4042d94080e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 846795089 1250 846793839 846793841
    0x1051204030203091210060602031303020427080403021e0a060509120f0109030e09090d050906070f030c020a0506120c090d120525050a1101050c0106030c031221 71
    0x18100740c080d8070041c440490507a0b0f50003002015100f60700003400c1d400e421b0b01d450109a401d50b0300404150b41042c0010601115000c14040840b50112004901880c061000d03020403100238000ca0082c0c1038020070142800701e00f000070f20803030748269020440180c0c0b42650581e4a42c001a5a60340414482c2c1d0412010f482078018080c401e6005103d203000644c00402545081010342003d40b20380d444000403000c0c15080b4050f0540c000c020364040c045442d0008240351a80c41c00640401071110100e50318003240c907254242c030000c2d0381c09401d007420030301c1608010301258100301e800c920403994041c0c04901400c0800c107642c1204601c1c40656801c0c0c840c03811015050b040392a18a4004001d0004c180c0480c8400b42c42d4072982a00b511107550301e41008034105030010440080b903c1c286503510203e40003070350002d065001c03503401c4650780c9084041500120340c1c0d480f40184e050320b40d600b40a40031041c002c0c05078001044901c1749003090341819200708103445031104180442d0220440c2e40b180c0131902d000b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 846796339 1250 846795089 846795091
    0xc02090f062706130b03030c100b0f0a0e070306030b040807120f0c230303010b031801360b0a0c0809010506010c0209040311060f061206090c040b060d0c021614010512 73
    0x80b130300200d01140e40c4008289150041078515600f80c0c031001d00540000c04a1080f900410003e07503040354403240440108141c0c0c11544540c468094215001812a51107540014045c591200c6440c8160909003080211608032031402c0e1100e2040d8000040174500681002e1a000c4d0544c5031080c0c1520540c848641c0904c2615070040c0e010406110304d0504070303052008502900011282c9900c0303041c510101207601c2c240750303902181c582c5008a60b6003880115000e281d91010110440c0b03165500040c482d5040c0c01441d80c004081800100a0001d028510781100c6440c440d1540e441c2c3ca030759070b202c0c410741c01d0390010f95040340442c5000c0441c1001d4104005141d03406406401c081e8140e950214045262100c11182c1c0107581c2804414411a4074040c904550791003900d034028110790800e0b201c6c0301d403660140b1542520482d0382e104030304a1500c0b50419105400c80c0b01008000d00306036008069180d0040c4501d844900405103008511114500c40c11090840706a581c80d080010b91640e644d941c7d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 846797589 1250 846796339 846796369
    0x20604150c0c0203010e06071707021218100302031b07020a0312170f060a0602010515040507020f16050a0509010f0501080604022b0f200a0c02090f062706 68
    0x10701c0b6803141016071024020944074410700f800074040c618141c1c90050190004060200410303800c0828480718980c0060300640c4038004000042c0d403140940e0108001003d03074401c8a41081040010310b40e219010740c091449542440350860203840100d64031403040c4210140298031031081c9005001161485c91130b68004681420300f00102d10107070f920022001c0003110500c4804516074200240707801c04080c00d00013008240000d03ca50706044103140320035208103040c14010f55a450000328920300c2049405a840c513040203444068050750183c0c00c860347c0a018050140c5200180000c580c282380110504a401407401d0803406030501c00115406203024040303d0b03009400b84000003440c681c0007501a10702e441002c0306459103403c030109070305940401200c4c0403018942203034004201030700c0c040740b8034443c5401d509a41d101d084810680e203402c46444042c4d0041209010420b030042d0030208240645011964a10008a24003040e0345003a03444502190100001e000b040c4603040c86012114810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 846798839 1250 846797589 846797597
    0x9071b12140705100f09140106030512282c0324041709060a0e040e06151203040b0301060c060b090103020d03030218030d030b04050f0106080c07030509040f0c080601020604150c 78
    0x115003602d0345047e02260200d102056503658208004000c42084120034160142c100703e828400e01d0031601d40400c40072044481100f040c0c9407070900c0c07544150240c00743c04186401c811156080b940b500a004841d20607198040d108480c804520f074050722100c4801d580d04031800b20501d1f51265039a414041900c00c1d2900c4024062000c1030990396900040c2103076840c1a0744044c651030084003040250b641c01d00c0c0340001a00030b4021f000801d04a20b10003039007501d007030724092010350400480c01d2851082c0d5100841d200c0c4080008109158040501c1c0c00700c50059801b4001e442203281002a082000c3c40001c2d4420041e1704030600080c0a07402901e854203080c01810300c0d0b1820384000c2420014400888070000750717154295041c5207050305c1603513044444070280d0070456040401c00703842c8401c06000030500304004940a030070140300d801110303030034140030f0014007440003900f2060024100362400fa0001c103d070180003610355403000403102d10454000745c07000d40004d160301e840b400410490320300314204 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 846800089 1250 846798839 846798851
    0xa0f02060c16150b0303070b0f100e0105041107050303040609170a0806010f020307020d05101103151504120b04030f0305062b0501051e10120209071b12140705100f 72
    0x3980d006d0000d414081c2c0141040d011501c2c044020426901008206c1c070100c42c8000009c1c00081200b14043d81500c105071800a488101c210340a00c0034062080b000306180300000800081188130340019001c907101b6200300c40714003c2000c25040754000c810745503001070310740340000d4010340c41030041d1242c11140340180e0b0300c7c0400326000b240d105140300d4416259079014203500c082d0b4004038490300310f4202d40b01c1c5003107045041c2800918001d52420300418400c090545d212000141e0080c111402010160b00054030404545088901ca0744121001d60100d901d80704c0c420354290007801014800c50005000c80300040c4004015000300c060541c0209601c6140c051002c0054001d2141c00c1c003d0000c00b4581910030380401c0030091088006101c41e1410303c5450b410055001031001e0801d8203941102c0044481d61004001c5443c6412a50620356600144040e2000d200900e441400304290f00c0d9940c050302e5668000ea5100c522a4100c020520743c4140b990542d1030b2200e500c1240c18601401c004298 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 846801339 1250 846800089 846800111
    0xb0a020c100f080709180b01120c0210050c0c0a0c0905070503010305061902041502010203190204050a0e06060d02030f090609011104090e07090903020f190c17010f020a0f02060c1615 80
    0x108501b004400d52409680306420092981c00a41c105804a00460700f440281d40a80000f1b46500041e003c0d41103058441002c02d080580c1c010a580d0b4810442c01110041300960502902c0b2501e28032907072242514100128400620901c12241030ba0b400c1130060405807500c3c0070400304d040c011a000c0074181d41c00c0c48040b41485803401d09809200560740050b0301e030f0408030102c41c5d5407422005202c90f400e10400c020003e80d1240507550085030f14022060b035140da0303542c02042c1241718a20000e0000342c40001000345c1c0e0855050340a00601401048a955640e9807914a0880384115062010880180820002641c980d00321810400c000d03029558050f0f0341d6916101622818081240035030070143c08000c04400401c4031020703400440039200b509040c0c58031003440701c444d41c0c01120045082e11001c41c2441c082500808100071240381e046540ba42d08103070060030310340d0050404005004140201e03c903484590305450114107103e03000110480715540b6a22441440d03041c840c1420748890070110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 846802589 1250 846801339 846801359
    0x105011b0b0709030302070807140d06140c0d05161e05070b04030c051c1e021921080c1b070e01030501020706110c07210605010b0a020c100f080709 65
    0x30240c02c090f00e80c40091411854081d09051880c0c100543e19400304000300801c4010b00c201440c140f0b0140c0700c1c5907038200e850400001030030003d5441c44058417000e003404203946607a801041100480c4000f0003003511100c160280c440b40d038080e82000152102901281e42c0c01c540004000e0800c03038100246030024a5403442d486074011141500850301c0c031040d140500c40144030107103590700300a42c0f9038940e840004014203210325060f017020041d0007518040c40da55008202600d2031802401020030080c0103440c04089400c801049140ca0035480c40b04014098018030005010700c0c0b410400c80d041110000c144005880b0700101c2d40c80a2294120004110400a0107940138500440025a56820904100042c3c4031740c00141a14010200991403091001141110565803a43e100450001008801d4079160548003406170285180000000340c1508000050900602c00c1c0c0a0300e1051683d40b04002891300300c518001e01060a6400c07a12000d80708441c4654880c3ca076003040c040040d12902d0301a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 846803839 1250 846802589 846802591
    0x12020f0f12060a0605041d070e040f0614041103010903051213150b030705010906210b041109031507121e05130b01050312370c0c09090206030105011b0b 67
    0x1100d560b913041d0503c09400c0c207000d002c0c400c0214007201070315804100e040e1070f81c80c0751a100b025098034040c0f01140400114142045d0b15a4012100b4407d41a0f86010424004000d403400c0380c10251030040501075041c18050181c80d15015146d0500f400c04504801c422138000403c1c6003440c0361039100d24000148010700d1401191a000b4001448000c8107051500d05070141e0031240c1480348100c000c01599600a5440148000010040b040380241d01030020240a1400080d9402414080e00e038030003400d044054114008110116211401840080c074840300058070200700081c0391080110f109821030b040242040f80310800c158121006501d814110b60742611200d69044004045400340902d03103004a02416040740946071400502030b060295118131000103500c0c0e070394404507480344044050300c0300c490401c203072100350603101d00800100080006001100d02c140d00b20f10104142180d8420540f0140c2e000d81716502c0d40c0d00707000054805140102000c440c4030800e000300e40008020900035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 846805089 1250 846803839 846803851
    0x90c06030c0d140718120602090a03120203120a0219211107110108090d0320030f1f030f030332060a1d06010c02011404031104050112020f0f1206 64
    0x9501903041030741000f011800c0d0780140e00b0b20345c10981424401c41641118849050350310400047e40c4c1c014134404181c040310113900c0505211480c544002e0b080313401000520705c4909503090300c482903543e4131001c4102d0103035202180c00c0100c0e040b803040c011409011203c40c020310078420140391800e000c0261052b542c0e40c0d400500da00b030340850130700108074440303440190382c00003400c00d40480d113081c1e140c4681e02c03440c030355145040648581d0a562019114400c034035505101d003000e640d50707140c00141510034050a135070321000342c528405410f0410064411240c183c03580901c0402c01540740751400c801900c40040d5425040c00c10540008190560030070315003003101300120038195480c0140411110b590658450940c1440055210217018040043c1d1644071909081c841d040c806280012101207010010b99401d203100086c0120034410751900c080c482060886003800280c0e21441c04041140a900f0002d400c6060005056818070b44a400406c140802030104908004403402540c0b900d8415298 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 846806339 1250 846805089 846805121
    0x1c110f0d0b070f0f32040306022109060405120d022811071a030414060403090801060b09011e0e0a0e06100302160f02041d0606090f090c06030c0d 64
    0x212500d9003014154080304d6481c2000800d62096120705201c54880c014420822060071040490011069081e41c1c0510341028045444170b040b869800548003000382d86020b034100c1c100000d61404000260f40b44141d6005018240c8c100790b82c052040e042d003010115030065602408420140602c658450250151907442c072a1204440d03078015141c40040c42c815051a0000841070103110401030140705281440b1052645e81c0d940c0d070034024070502c0b08d00c001c040c0d41e000790fa080c00107141c0d00844903020399403610b00030060155901545040380c820a00b050340031510049074252492030303460410b804c100030341c1003070341c4030301d0703894000070080d42180d08001d160100348014818282800410805540782c0d41c1011458659402940c0d151200c0190006002c0480400001d00f1901e445d0007541c0001108003403954058149200181c56550440e0742c94091f1416100150070651907003800c5000708240c0d0090543c0440072810301c84940d10041582107101020072800c44101041c0c0705400c1a011b5641c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 846807589 1250 846806339 846806357
    0x150a0b0304061404290105010c030c0203030c0111030138070c210303050105090103020102070533090111060c0406030914030307020d0909090b070f030905010f06051c110f0d0b07 78
    0x81000c4071042c81c1760400e208900800d0050050f41d821a101c6400c040c1c060030071644039941440041d140d44118090b03810f143d42000c2c0d04040500c81c80d03000d541611500301c2a00a00340c400540a194620214207003004d4420035801c9403407602e03104005060880c01007581021042d00c0310078210814452510251036a4158051501810b070705106490140c641140c00c50b04551440c0c0000790b8842050117941e10402402e07503496521011908001c240500103921525428007189110040d50040322a840c08900142c40c100340d60000401c0c0d07188690b025040242c01c0c1400c0000c220001c0105502c100c3d40880074860004000d00100040d520a01156000300300668070181300070b007840d84541c00340342020b003019840800511000c0c0d004d64040e040b40b4000c00f44241150007140a0080640701a029510f06000904800040d4020005490040e03032008001c072503808200d49681000b000207000c01c810600021090702d484441c8000d4807000500314880c11141c0e44a418440c5415100c56003c00c0080c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 846808839 1250 846807589 846807623
    0x3080c07050102071a1c09081305040203070801140a080a1101031107080720190e0c1e030c0f0301060903030909020406080613060801020706090b150a0b0304061404 72
    0x40494040e080a1015180c86440c1411210b031000c100034171000c18400c08510b1038008840f00c00500d0300c01844810500c08248141171014069110a00c10f100904080384041100c1c2014000c03a03000e841d07035030740c1c80300709a1070b243c0c40f5400c00021204466020000c1c040016140004100201d07426010700450803808034010009011104c2c50261a410b61310140069000302c1e40c00d00640d5009074011001c96000000084010111103070140050f500614152400d0f1882865103224801c2c0c1e0b0071810390900c1a2140d21602d00b00740101c0107000c040501980c210908034100b1400765403c0401c030050681002c10000d44028660800d070000b030300044030800104189a4420f1628004000c0c0300011031405003040002881c3c85401081d007400740b02680140c100200c010b40c0400000e00048000319120b070320701c3c0384c840003070164484127a40748500314011401e41144a440024850300081c01d10403000d02d4002c4c11102c5410040c400e95203031707558044500600100503a4288250303c10051100444499 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 846810089 1250 846808839 846808843
    0x20f01060308190c030f030213180507030507090803090d0c030218041707080a08040c03020901060509030f070f030b100302030a0605091902010e010c061b110d05070317061903080c 79
    0x4943d900c0100000020700c1c20100790040a210500500341c84c000d82d60300c0c0a11450705113030300d80703620146900e019140c000404403901d910850241103660b03004d018075241c0c00d0b01251000000d0003000d040b50400c02001c0d100385004101a40d14511030111901c0081c3e59400141159070711211403d500e215000400c0200480212844a105c6030200800c0c10554a51034041e424001c3d07092410078408003401050510080d40103201c01194000d024118030740e1585001041034101c049500d0091103030400c018406100841c145056540c0d40015032521451921081c180c0c10000c1c1190100d40e00944000c00580c40901a12840c00d008000200d05c4d814028042482c201110f0740040351402e03200581d10040c1ea20060a205811003480c0c0081c1c5803026082039002801c001100c0700d144113926140c2501607402c42031545864038010305491103956250380649a91060070746c0200050015184d8501d0850144001da801c014040d002e9541c4102c254038800400340c040c0c106079200c030340200780700391b2030780e01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 846811339 1250 846810089 846810127
    0x3020607080f06042c250b0d0c0c05070608060a0e060f090a0b030609060f01050114030c1c0c02010515220e2b080703110a0f020f01060308 61
    0x186404181494600d01c0b5044070790003e0038003842280c550001c145030f50500328089201c80030160303900601000c040300150366264040308000e0400c501140000c40001c40f03442003c2202e9100160f0740c544400510040014490045654184591122a440402c400b003100b10041d01898961890a05001080108200007580154a05107250013001816210140041c000180517103100c142070b1161000d2001900400c140c1036018802c038420031481000000c0c86500034035110303403100d20990300c0380d004581f80c0100115544030646d04001040841d5015001484410032a480c5c810607680040740c100103035a41448030f2030060f074451080c40908170345c40c801040107450864407210a88107140500446010507100341c2422690780071001c045000500c0403891604c100c1d100740e49860212500b280b20903902c0099280094080b100007045940070344596145486652291810000690310403281c1c40b680034110300441c09503040000a0080134003070b039006140f00703104840c0c4483c0820701030415121 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 846812589 1250 846811339 846811351
    0x30507090606170714073009032a08030c0714101d04090507080f010203070c08030403210204060e041b0c0602160b040213060510030c110105090a030206 67
    0x129180c810081c60760000c910a8402890f0040328146036240c0105581c80c1415088103402c0090000d031800400a0704100100d03c4482004808607500410320310000c1030041d40901c40100d040c0c11400d10102e1001d46d000c1e001034403030011107043c00c041d96000300001c0c100355120f0700d103940c40803400d40040071043c006000980202c030f481c8252002c0c01030000700a1503100b07804030140008000410200c0444403050141c42a01030b1060015002a01d0b10b607540320403d1240c03061f18082d03125a009400418001c4070700801950342da004082d40143c03519501680060002c07000d008004008402c41640e162841c0300309040a03d005858a00c1d011010702074507e44484240f0a610b401c41c0040c0c4001c07040c10210f0110198500000c0b034504503c0d00c4002841551031444040c51804020030402518109203440f9900c2540d405040d000d00e42d00b42c0050b2400c0380074169211020580100c01184607501a04070236040c0d286c201c00d02c450703201143e400c41e20107913200003854002030054818035804000540d0000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 846813839 1250 846812589 846812591
    0x39030c1115030a020901140c07060f0c0c150c1406090c03070b0406080402030f0f0105010f0506031303050309010212100e100b0f0a09031208012402060a0b031f0603050709 75
    0x201456010072061000601d600412039020a01011903485481181280400c02c00700716902e85920100c03a44c0d644851041c0703400140a00c661a0b40c140c4103c1c00414410340c4542090b002c4c5d405e10b0b41d5041482c8070041d540080082c14075250010405410030002c4541390b400c0503095504081111a090100b0401200e0103588100000c0000c1d0f203150040318120344061620b911151a03610009080014030004462107201e1400c8605003114198002c82c12545041c24030b51000fa50303401401103900040361040150360207a031050740884d005000031a40400e801c5e0005203044c0c0d907000d0741014030f40213071010700c0030341e6107001d040c02034882c86200a034101c0d004401e1074204529000b01c80d4154880da01e08900d10040201d0034104441c010403000002d19884642c06500c504c0840004046044c244202a510b000702c000300e018946101080012001c02580908041d68400d403042c000b410036078400d02d80600c1882a540000784001c004914900080800440d04528504107180b4100150300b14441003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 846815089 1250 846813839 846813859
    0x5030c030c0d11061201080c09070c1203050417120103021801080d0c1a160f0f050a050309070b07050a11010f0509100e04020f0702040e0703020139030c11 68
    0x3a80d02c0010040c1c200740e12204129a01c00c025010807098085c05955100600442001080710800884d40d550307000000d954201c0346070354051089840f44844240501505030041213014103902c690080744c1d20601564000b12a0a00c81c1e03000c0340e031544a01ca40c400000c031500014030851901e50b4070444019400000350243d941081170082d101c0d60601244001d01c03409240d808200a0040b81710f5445181e00240079034503140800c96468841200310000d00091041c1a401e01414040c00c00902c82880c2a6984c504103c0c2c181c1c020350b0107a1010741100d0281c032414500040f0510a08002c3c01c00c0b510841c00f0f0300c4010740724584940780f884491001c0b414030024000b0075a500d5030040035650b515104071090719840e02c07105015a044c540a02005400500005840d0703a0308100d40006c052407482907030100311424030f031110261540c1043c04001e0009081c3c1003c003c516149030f02034011071301c00c000640100654030b80001000d0300780400450208012a1160051040c180aa0400038805403050340c0c1d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 846816339 1250 846815089 846815113
    0x12010e0729070311061006230a050f040e010305070302120619020a030207060e0d11030924040914150301050712020c0705032b052506090609060605030c03 68
    0x85481c41403038401e900320100b000400e0510544103a41803240c3c1c0b00c1076036090b04114101c0103200c44079019200c01300d4000303044807030307103842800155942c0400048098203001022104560035404500d02d50301140061202058001c900c1441500139440381d0024904135243d8414442100c6192180c08015000705082008080c1e16524000402c1c0b420100180d0b1042d0a0100794001d0144410140c00185804100c640b5600001070360b4141b040184c44660403616051006a038a00c5042d0b11190400c0041e000808403ca54002c8081d00e90000144141032179110b61000084401401c0c06040e8031060300284403503090040d200010502c0c0a900030300041c60140c10261490a1454002588681c001071724070703004000380245400340100070155580b10a03820940550044283c0142e545040c042030000d0009001d5011254410150f0006001412071880c000d03654140d9040251240c0d51141ca0200004410344034003a062881841c3c005072072400c103000e01d460645150760690099000c0548450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 846817589 1250 846816339 846816389
    0x102030a06150c0c0501030f02040b071103011a030a08030907080f01020a0e010804051b03010204090612140a02090a1505060c010f05010e0105150c030906070305181c0311070512010e07 81
    0x4d6917000e09010034608216110800217200d1a0b114139100c48010401c08100441141e200784180d2046000340716003204550380c10151541862900e90580c8440c10000c0001c1c0088061a404211503040e50300559170303030000c94103020110a2482c0c1507540042e800e9100b40e0840b0401004203801c1c0b8003094185090742d0361030380d1045050f40c040d0184200801030310196909404580c040c08035210280503041e980c41201e5182020020103d40d04a0030284182490b03000241200c48141c0081c142160307900d500031007000a121091034005050302000c0c02245540313881006229042c0104000501c0b0700b44d0310411001c070f95060f00111504140d19004006c19034607041040070807511020b003560346401145286185216030032147d50000030114004044c59005000381406000111a55041c01c06450810200c0c001500040317030098070034640f10b000709100307007070000083e002e0750103e511058070b40d800034960007843d0301c0120403a0744504038111004000d021201c000c00c50803801100c10700c08010428 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 846818839 1250 846817589 846817613
    0x40e030d360b01060c110a06020d08010506091807032a2d0e040b0d0f0b0a020304170d180501061707050609010e0d0606080c0906091509180102030a06150c 68
    0x60800602e2840072050004844017041c55006c000c0c80030b03e0455503400d001c1d40343d20920000d500461204000000c0c582003090407180344280091a030b924155500e414040f8011018005d00d01701a9a01c1001c003100c144070311a032070301801c4002d20600f10100a203004100b014001d080c4003410400c13211111075240101e800c0e407003c403118140081d01c0b4405002150041081440c9158403116513407030302091000ea00041d00043d401004607400e156101120305080c0d10054070018160140d10a410a8185552010707101d050022000420b00020300c00783c00004644240c2e094a01d40d5680b2801c0102e010350070260008841c0031800b62419915100c0010350324002c0006041c14010208101c581d56030351601c9414540340d00440c1044801d40b540c0c0b059a649510325980c80c0604a00408030b26a031500c2001c09100b000c001481c04005024401404170444010301541005012a83c0041500600f030000d5403084518a00000d190742c54500e8101400110405410a000b001c42801000c581a02c10300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 846820089 1250 846818839 846818849
    0x30827090f070c1506090e0f0a030509060906030a1a030a020a090203150907030b010327060b04020c0307050c150310090b03072601060f080c040e030d360b01 69
    0x108000e544408059030620032040c0d004011341e50007524000d108150740c0c088400e403000c480c400c0001024440f000c42e0b1740d00105451070041e6200030303041070002e88248028049034001502c0c850030960b4900115000f600140c480691705a15001c170b0311110880b03001c5060800c0c3c0304a0040203101d1603900881ca4084080c09144c403041d40000020b8402c100c11b10f8550100240074150366010b00e0480710083c014085100c03194006030400815001c15100e0b030300d021201d0f0104908000a0103050703510403008149009296030000d03001e00c1807010068007800a014224003a80c0a0201100c6210412030034200c0c100814202c62003d03c1803003405240101d40300c056551031040000c0d0617007000b0000f490281d281d032100c5598014001880406a007600f039410030b000c1d0040081c4190f43e01c0f50084103001c0340e0380c0542d09071a449084610340b1031070035401034500004003100362403402e51032803461010384002402a15240d80c11891000e0780b980d40e4070605001c100319071507550780001d5559503251070400612031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 846821339 1250 846820089 846820111
    0x71a03060418050f10110a1211220503011a06070609050a080a0f0815040209040609050a200720012601050301110f1614010603082709 59
    0x1403096100d552010384120080a05035000003018603000b59204005400d5400380c0c0101202d00d64166040c1c05140076100100c170b0001c0c206080c0b10f408035040d01c01d00c80300036405038440340c140b404091084000d01c400d442c40011b84004943d480301c1e840c0e10804580c07055020343c0c54108004035010800c3d4120800b0041103501940c0d480d142d090070b9005c0e044c0c01d01d000e005801035002082c01c110714103000381040841030f03c90320102c06440b1000c2c6c1d01041c00712140c244000701410036071154a4190300500322001d0092001a1044c0c40300c2d0742c0011140101e8824a90640d00ca0f01c01200c4a0352803d0032111a0304c90b003001c1e20f008400c2d42d401c3c40310340042400c0c01246003c04018503140c0e00607600c00da200004048a800b0312007140303210310041d52081c42502c1c025440c0184404511198030201d031800c1d28060b100300e20300314071401e90b0407003041e00760b0301542c441201030300c1c07801408404c1c041d9a00550003840d9480c0c4420520b4400c40707000162025034140d01c00f41044901264440c82c510310303030060701005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 846822589 1250 846821339 846821341
    0x1609020405102604051005070807321e1b010e070b04031101030603060f06050a0f0303090b2a0106050f12060a0905120a09080f0a0503040e07020724030e071a03 70
    0x2404503c3c0074840140041207e0401d000c0203400d07540700c0c4005203d484965600149c07840b040c480c80c0c00f500848000c28098451a02841c41c2170b843e04c00040041500c400040800413a1101f0b92000c0c68224480b03044802003a003180001101c800d01886d01103c4105e00030305a2685000da00c0c0303416209511000346003100400d078408441e8083d9218000a541086080c0480c01200310160010942d6004051041122400c0827486010014498080d41d62640300c20f1086820901e00e00714681010108000d11052044105a04841301c0c1c1d00c0c00d51221014000728505041008110101c050308a14a0244200040b110502c40d000510f142d001080780300d0004494a05041890900010510012824030001441d10070b042e440f0b40a1402c80d80303420140e5081c84401e5000f0742c2c46003a1004041c0003548140b100780320b291400c22100d40c00c02c0c4580100d510b095a5410350824441d4540403143c0000f00151001040c9601401042d490309080005800c601e400c0420036180c0c088611409005140048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 846823839 1250 846822589 846822593
    0xc1b0f020307030b1806280203040f0f0b07030f0b21010b1c110405060105040608151e100c02010816120504050129011b03021609020405102604 63
    0x2004400107903070411001031041c0360802e00e04090019041e4101124401c060001c0e00403c01c8510346c604d80347c81c04010b00e18000c900c0d88004080e4202074410340b0021002c0c406880002c0c0e0650310302e41d1042c4605410107584ca0250405004c44600140300345080382803010701c91040d52000c1480c00d02140f20f01c9100d64800903c20b0b800d005100713041400390001c045092003005410200c003034098103481380501101102c58481440306a032026036585000c0340e41803209106060007003a410b94062a662203d0303100c003034000002092080b220304040c095030b920803e18103181c20f042126140403001418207500d404034542c00244120310013402039220701841d8030b014410314460384c400b01002500204c24070140c2003e041c41030080080340601c04c2c50005580c820741203841703030342140100d000c01619400030448001c01c40b40900e030541da40440850003018192024407e1380e05075200607004c188401a2101d0501090240c110700b640f16400a0081850b82d094110400107000700660581c4025174406440b00c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 846825089 1250 846823839 846823843
    0xd0203010f051e1501050a45060309024f060b0c07090c0504050409080316140a14120a061701060e191401080105151f0315080d05030a0c1b0f0203 64
    0x944855480725050001000e01c10042401c02350015031580c401c000d1a556481a8211126040000d4000020303c0d8600002041c200a4102c03a204140305c101c0b03468407030141406400c1058074141c28900b08810164501820351044e00080e08100b510103103004000414a47e4a5000b4400c86401e251031390740d0040c1c1e50f403155040d030740141b4000e0424000180d05140c40740070341d001110000e4407100803a40c10340f500d80c8a103480c082c0401011712818030f0014050004c0b00c030301da2400526a401e840801020003503035041c40c10548602040e00c000984a802d001c110350740c400025204425071f80c1022400c2c420300340341d02210758001030050043c200d4020004400c10241c10b41c4d60307060b102004058000584600107400991203001c1c44d50004035035810880c01c00842c1c10034000e0840c090038500340c0300f4406900a034031800e03a00620522a0b1200755555000c0c40c0781c42c0d20340309074400080002c404d004000b111401031180c0d500241c1040c642d100d1003a40038030b1186100001c040e00502d104104003003903441c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 846826339 1250 846825089 846825137
    0x61507020f300c0303070f120512010905090f010507270f03030207060e030102040b0f03061305010f03030806030705031518030f2a0c0d0203010f051e1501050a 70
    0x10300d428606441c42c810009842c040808030051040e0f00482e41c000001d40b801000f120245540001d0100340c0051544403101051411045241030060400900c4400601e900c6451700030010300e1000316180c589002c0c072a041800180111005c1c1e030402c0700b404256908403880360341c2c10300302810321050007201d1500d0500358540780c1c2c04000301c0442d541012081c5580483e285050321071a440d00c9054070700e150141030807446031b4402c2c0d030850001840020010034200c1d0046400ca10020890220042c0703200c01c1030b00325582a401202c1c451015a8100105074110501903401001100584a4a4035110102e1f403502c80124141e02085404070015160a000c101220150140c040c200e1752101c10409188105501c5441c44034000006000c0008650711240c0072000c032590424050301d40c3d1101c28091142017040702070300703c0c0d040d502c0d4030f00404c84111a200300b030320904105d41e44040e4504ca03219a0b40c9180c030050107245021074008000802640c0280880b4078080091a0064065284000040440e030b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 846827589 1250 846826339 846826369
    0x60d0201090312230f030118090c080106060207050909070e090307080d0902010e04150614070602070606030218070e100923030105150a140402121e061507020f 70
    0xb4401042405503031303004184060048034050021030348420182c0c0d00340c0e10702031a001c0348140501040144445044020980700c00d0808801c08074580440b40c1d11002040e4464108001c20380d941d4108000c1c080d8100301c0b40c0f005100c02c0d43d11080794207001d900c03140c5948441c002d0f1411245ca5101285954100708221201e4903000340d1542e440b030188042600180090010607800602c2501108030746103090301c01d0765910300350030801040c407518012041e46d422000c0041c00622000034046540803c83c180010980103204007000600d01e410b41c0304002054140c030301d01003d4000c0e448100275905030407090748548a42d0071995480303401948203040781c4201c1280c00a0651140c01d601d050130f400d440400205038014110003e11655450425070b4103407001e044511540001c02c814100004c181c001507d03180d003440644050b01e4115100d40116000c43d007610036606040e9403814804a401031503e4258100360100c8a07017005ca10740d800e001455016652000c1d00c00e89804c0102d203625560341207a00c040d54 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 846828839 1250 846827589 846827603
    0x6042a080705360109050c0a0f08060102160e06120705090a200406031a0405071b0822080f0102071104050a0605220e011107080f0d0204090c02010f0b010503060d02010903 75
    0x400c0680c1a08551082c803800c00840c0c203040100702e607d559481036640e50f900076a5403c0c28241c0704041203680c0358004d4100d41c1940a09400c0070140d0b00d510082c40d000d0064001d44030054200f080501c801c0500e00d86000200d80c110710428011552034000103034001040590114604140c0100c4c0e45446403100c0b818140c11100150014403180c140c0c00101c441403541e214510250b01040900040d01e84c00c94011000403c44181c05a07982c0220581400003802003a40c0c50a00081e08603121882042081d028540c00e079010040080706400c03c01c036542050b0600080d0308004c055642e4030015030064510910403901d03100060560720ba20360002d001084010a090080c41003035410140401c1e01c25001031940b404d1003001e01080d0760502070450505085d0542901d4a00b482d140c008c3c15400c2400e0044907841c0400c40c0c00d00c000310f1030010704054040110f0010300e21501540281c2154102d13011b08a402c0d003004c210034000e07a00030b002c0d039500400640b1103e203250351500c0122600092500000c20341 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 846830089 1250 846828839 846828919
    0x1d040b04080d0b040c030f0f110417010b040f0506130204060f0305070509090c030a0e06010f0303080c1b1f0e0c0402090109120f05300a030e06042a080705 68
    0x349a140c7c0241c001c401600000308a045100012130f000e4030344a02c003995040700b0420081040340c1e0050700c41405240e803100005080c0b03101e10001030a842c641c81d25542c1c825150b80c28460a032911031f14018181200100440c90140740440c050801012890024203041d6914001b601c00d030702440c02c423981c111005295012a1401c0698000c1350342017030342c0001490b0720301103000d028850000381d858184c409003074ad001a260725603034040b1054200200f810410300801d01418505e0302282da01d54080b081850050500c24030008008454204c0307001a580801d400d000d408100300c400401d9041400700152000741e6280c131541c005a504043c180d001028a400241d0202c0900642284a03900c25103d001078551890302c0c0204a104c00c030b61001418000d0200d40f150384040c2c038010000b4506208c42e0f00b0017140c1000760160250500c6070850f010f4a1200300d11040f2141d0207060390a28204002010403903501c1400c1c08900c030fa660325940112406088020006000000b04959a9031007142c80c60030241e603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 846831339 1250 846830089 846830111
    0x703030b0306192a200115140616060c080705070b06010c0501021e07060c050a021e07030236130609081e0409060f0303050702060d20041d040b04080d0b04 68
    0x1d02c104440341c9201c0d8406080c1d45800000042c018400036425141d0001d47c102c1c04c0c8002503420b010058409a40000c00300301c0701224a1000c58160310f180e0042d500010041000040034114030002040f00e41041010054030001603182040a42c02140a10f000f144aa2443c9065402403041000317040030202c60700182058030701040014101244240400d000c102050039003540c0c54011a00103902503040700b503c61220f01140109000c400c020a022209115529004145010488000c103800a5122910418076144000d41c82d114110300449100b610700e81111413041e100d40c1600002d11550301c4111400501c901034055a80b50035896410034a4201175041c0d081c002c0d030040c81030207159030400e40001000f2042c280e45004890b015202d45151180c590b0800c009603208890380303000c07944e44004814081a01d8103640c40382d02240300c0526611401e1481d903880ba40e08061160b43c0e4000a1800c000000d110403240325081640042c5d86612000e9586100c005001908000b41d00070380741c0800d00c00c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 846832589 1250 846831339 846831347
    0x30e0303101805070206010b032a030f180303010506280806010909050c04050d030315030804330318080c030301060905030f0c011103041a0703030b0306192a 69
    0x11190542c00740086207084401c2c94040d039104481e03150160300084010400c603c007007801107922070f0343c681a10300b05904940c040e803110560314402c9031354890b01004100c47c4e0014000b0f0550020041d46000f1040f081c0c1d40003056403448140039090241c20041802501c640720100072110358203010030710a040b00aa400000c00d4100200d528500040d980b01c1c001521039860303c80c540c0121520b403e0325242501f0903050050740c0d20a0b40f000c40800d580c40325120343c0b5060440070800958410070040b0381c0c4526142444403640c50b806403a03514582c02c0c40030503500d002c03240300c080e00c01025410081251826040d20100c00c0014510250140000241c0294414000300045040c0d0303000e61140042d1540b0f903028140c0d144580c04d824070b11680300381c1c29509258040d211a42c694640a01181c0c0b8094540c1c011006406440030a4140c4400100303900b030801d6003500400a4600d003e070010b0030300d45000da4803a8111820b900b143c490066030781ca00d8407092201c0140d102e44101e605a64422100c1007410010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 846833839 1250 846832589 846832621
    0x4107120e0604050604080c1513060c020d06050703092913050325020a0e0108030a1d0d030512060f0a03060e10020f09010f050c1e03070c080d080114100807030e0303 72
    0x40c07003021f183d00e010750050103a009482040065034200c0c009c0034100501660000d0b07030140240d920042005c901d000003445405800c3c811a4140c2e004101c43c5c91501d4503804250340707154100180c1540000da0a0011040809143c7c0640c000d4015812540743c4c1c280719055215943e01d460000d010019641c7c0707407942c034090050f00c2c184261413400700d2640d1008112142002070042c0003298004100b910314852181c005102015542d04030086012240400180c10b00b0541d4170840106101107904007209130a07002e050360120094410445a0100340001442c400c0d45010043c080781e540c1405807071804080200c00700010000c0c008640d115400009903105800c10015580019144401140c10703e1082c001d50b0f14004140f001800d01c40350890308003c0401c052401900e03144030501142b07000c101000c15041c010100c4d00e01a00611562400c014a0080140c00c00118840c08403e92070041d142d0074120504c000140c41c19454948521000301c000d0050401c00e82980d10010041c0819204108881 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 846835089 1250 846833839 846833863
    0x3911040912080108030306010c020d03030e0f0709140f071b0209071d0a05030c040b01020115120302060901052206090b010e161404154107120e060405060408 69
    0x1140b40e0707607a800280d924030049405c1e90000350745c0000c0c0c100604100b80300032013a900c079080204142031021500e0b4544240c0c004a002c05e9440700e0010041540c2c03a1040341030b4401070503254400c070300d800c40e011aa5071001800950400407541c01c24141ca041c02c0702500003055006104030800c0c1440c4000401c05205880c0301c54000c140c143c983e020528101c0011030480e640a0050078565030380004010040168075601d0f4159501e551040113022424401400609551444c0c3c040100560030028a0300300000c25107082603141c02c0500c815072070700c5a807544c2482550081d00b001c1c0b240c0b91030700601502800c84010b00e016132032000030604816a0195038494107007a260181403280c01a8100c4100c2100041e01e4100041000180102d441449122000e1041401d00c04001c69104039400c3c400103140070340c1c2250b030350880440e140b6001c0c041d40c01c1d00c004202140b11418411280c4078160f09a20f076810120511518683d01040c94840c6402c3d28002c040040107640c0b81c0d0b41c0c4d0304006031600189086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 846836339 1250 846835089 846835097
    0xa0c0504080706080603070902030c0a110109050d030b04060b030406020309070501080717180d020c09090106030201090506090a0305030706020c01061502150a0e010e0f1213060f1e0c02013911040912 87
    0x2c1d404840302c1480fc860941d60400002c0bc3d101400c001c041c0d0007003010302145600592a80c10100d85108a800250b000f07034850040142c0d686840c058003814a985070700020304001c100340074460043c3d03001c00394948034500301003a550700307845030008100e15500005004085024240000c1441600402e816002c0354060b41e146a045e5240c0c07000c01d00301c0e2458040240460b82180d81800f403401d21b1805401c0785c2d140a40805040c035180d480d203c2c078640091030b080721400e07000110303245103000a02030800202080720040300038099121002c1c0d140d0160101c845101001c010000f40045204d411404143c03410030000c2004507142c0300117035125456000401c42620070040055010308d40710302180c203900700150358104050306102c0111b60b404c408814490811610702010100410b80c2c2aa01d02c40e141c454880f6100d5000b40e00c005451591305011504980c060610f000c4c1880254111101d910305480f201614505807030318202404051004405070082e117002d8010b020410528100c42c009062034079 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 846837589 1250 846836339 846836357
    0x106030b04151d01140105040306020d0621110303031b0309250e061c02010f03060915150f230c0a0308060312040609090b270a0c0504080706080603070902030c0a 71
    0x1015105d5043d0008a1a00141c400c01080010520a9000d0502c0c503a00300004240710703a9602c13420422441092403e1080b1010494440402108e078100ba0781e026400e4020354203601d0a4120364400722845200f43d04071404c0000020b083c4501480f02203800f1480c2284500f140d0248413800542d40454061440903040703900c081802c034070b004946c51a003101503440c1c03401c8031143c40d0b0044604075500300410702416102c0c01d01240c420714030302031545101003005601190510381011181000f60715044402401a1210072290060f80001d0202c0450510303008020f05500f601021340d41d03849480c1c1a42032602444245a0401da84414194001d400c11400c0740d07100542a0600a460b228521030311001c42c26080c804c01c200c5c8030b43c0d00012104400144a42d8401d4000d84450070441d0b041c110382c1c1051844401002210300c7c80348505014003a482c68420f05150503e0030362907803221a80203060a0042c2640090025903007040850080c00d10b03003100790f45034100901b4401e841e0b0040e42c5801d002c0b40f0005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 846838839 1250 846837589 846837599
    0x182a0503071805030a02010f02070e0901270b0c0a0207180e0610060c1205040b0c010b040c0908070e0c13080c0907052802120705150604090b0106030b04151d01 70
    0x80602c106841001340030b058140c038594015a00400e454003000150b0249101c0040d403942c50007003840c49080004008140700b001090040307075489065200348560b810780c551100100302c202c00559070041009403001e85d030742c80005007a460300c030b1b0313075402682c2002c06120340300d1204886400c41c06402c1c141204031081516081d982031900c4880e4065080092900c0c4a200086207200c15004820f0220f41010f0340b400e03840e5401141d45521102c50911280c3d1900c4400120b82814800d12001184500d80420982e041c2500d036501e030303101c510501309080e1130007010541341031400c0c08070f421441104008616450740e42207401e80714106804000e100381d03a14800a0719260180045a0f0b203600744040d0107540400c1d240300c0c0c03000c00e940070f84c13524118424035040583c11489100140b5055003d0030081201740c25844804615040041c081e6000d181003102c07220000c1c00d002104d905407815401c02064140c051008100100902081c038448624182400a40c242001e00d00b1400c000382120850f419070303200c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 846840089 1250 846838839 846838877
    0x1617040f030209060301201612031506091d0a0f0203040c0305070914060d0c2c1308070b0a1b030e06060103060e06130905070803040f06020601182a050307 68
    0x1f442010b443c8990040100c603112141d00024400f40302580750218143d80a925141c003001e15602d45000440d0765085441141ea048400343c4004240702c1c41c18140e500d0411101440c3c090b50742820613412030b082d0740451001d40c1c6642041000c481e001500310344034500350900036224201c511050301e0364025500c1c0410b4500c0f1f28000c2c1d01400003c0741000205443d204d0a0182041c45050282c9014854400100d0a0006c05460000780c80c924a4000501100344808080101c80607040040429100e880400050382880540b01e2060300b01c6a218410f559050102c401b0304400319460580034119000c0800c00c0c3e4065011802180c0104111190b43d40d9190065007100c48500658400d0450000041c40c1854401c190351005141d00402040440a170340e205494044160440d00030f0785c20100707060040102e8500c1c4030009020b10310007880654900321848a02c030524180c1c810011b5211100820b02803000d10301070000c81c2c220101c91040c48080e00000f00107800903a41f4000162503461009580240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 846841339 1250 846840089 846840101
    0x603030909270201030b0405150406060504030c0b03220b270a060b1306090501081203150d08071b1a0403201f020d0201051b1617040f030209060301 65
    0x7001008044082907442c1c098902e108200807410544c890030003120316211401040c2c011850b41000c283c010040c0710421082e50400e4100600b0000140001c00114401c007001c0411296020078299813610b410840e001c00d0040c80c001010a100c841c0c0c0c0c858208038000c07600ba442282040390815151402c01a4034102110a003249507080d481b0310380490100e00e05a000074200301005180003425103a01d040da009583d65135208560340f5980750010080f2060511580c43d401c43c1c3d01048a25500d800e05240d4860101000010b024060107403007002000b0300b81c421142801d401a03e1440040ca981d8908441c1004a00616900814030318819180203505001d4406803640520b06001400106c0e20307000c02a600c0300b5450343d21004107401c130310035082c44d42d0140240f03050f075a000e0020601d001c01d01900b510f4019080a0855040c01815000c03d8280001e507a040f10b0b90310340d0201d03402e400e410b1030120005071303084e46001c0100001c1d000a094010080301e108883c400e80703010009907103200805081f200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 846842589 1250 846841339 846841361
    0x905030312090c09330415090b010c150c0903021201050703060902041224060605031501021603030e0a030b18010e030909010501050c030f030a020c06181e1f0603030909 74
    0x81e03281d180424841d00c00c1812104c4031a0541c10411200d01880018107461805030892881f00ca0110180640311150245a13016442070800c0b09040c00c00e03035603000269131900c540c0d4045941d6441c82c850340034070813901c03000103603001000e41c5002d8202242e1617000700400c4d0340d9600031030300c0c3c40b20001c4d03104c840b40240d0b1b00b114242c440340011004241ca422420b11101d64100040340d14a04102d04000f030300f8402c41c07000e030086650b61a00e91803e414000fa4070001c1c041414199486500300340d003148880403400d403d407580351a029003450350100208074103c025400041400b0a042c00f00645000c0500021600080d1007009001d00034158110315201e11686c11142d400c950494014401540540000d0007030b6200041201c7c502864071510040d107070000d0350b5050000350001841d90030b02034200403181d00080b00380302c0d107224000c83d000400c0c2e40300304004100d03104000010550813110b5090003600340d80c00030165040030750121000c0c0d860007010760740402c8020400088001c030b1341e11254820f80070164 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 846843839 1250 846842589 846842611
    0xa03050301090216080408060118021903021b01090b1501090e06010305060612010801020319051006110312011403160e0114040b030d21091a070905030312090c09 71
    0x10b400c1c010325002a51103001c030001c000200a02002c0000c3d4400002d00003040780c000030300300329410682d00942000c00140301100c0503005200b003a01c101051031a08503038000900b0016941c1c200e03406110745403119008000705075444e21740110103011035051001e1181d100340f5403e4210700740c60b0006581000c1030340901e940004e80e8600003051940640d214642001c8014101410945101210351410409800c041c2c82179401205000603007584d4200d1860420481e00207001e2841d10b42403540307841110b4411402081050001d03490000c2050007210005c000c0c0c4040d4210560312140d06120003007140700107078004d210342e107034901c417024280d094a8217580c02c0c3c2045a009134684803054006c2d40c0459441a446641c41a851100f55810080c806820655403038403c5400c0c40090003400003601c1050051800d41014440000918110b0b60440c0c0c40d400b9a50240c02c1d13403181001120003682076000a5054131000846c0b21446000b0143c0760312450390300040340d0003040440305003e4518001c2d07510700056 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 846845089 1250 846843839 846843841
    0x4230f0c060a1d060c0d11100b01081302010302040506040905090c0102010912050717030f2e2603160b09190818030115030308060301020f090d030c05100605030f0a030503 75
    0x118200340c80b490b4070650028102c40c1002040c5005c541090041c011103408100f42a070050300556080c0903000050969101c100644000c00e000642020305c0141880303560040072001504580c0241e0607140a00400b4018503111a100c220000040100343c03241040392282042e041d490750300c14051140210741c0300700413036800707200310340140c459403c04603040320801e00310011164100301d000b02075440303504c41d00360780c10903401c0c09000403400e100d100b0b1000c0d04010140840074100c24052100034100c0c1c11004011100c4002c1201d0485a0007aa40c0b0001c228000080c082402002c1280e1070b606680c05400070703038030a03211b00b00c04030741d034940344000c10301125501d401c02804901098081e2005403005080806580789010009084a400c91444142c071107080b08140103043c1d00c0302a46a00c210260021894410130030044480790060100344d61040360300c00c40410405100360310340c8030284c0d484001c4a880c404203030001e0000d4051400345600901c90824220504500041c10305640c03605070711600c0c51 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 846846339 1250 846845089 846845117
    0x215010918151103040c051c0b130606080a0809090c090d03030f0e1c030c0203090a0b0901020703080301091409030a2a0f06090309060503010f050904230f0c060a 71
    0x1211421a50542d2029550480040f241e500400118401c520507480303d00080c2c1000100b010f000f59803001849211130412603400000c000854803500001d1000d60540050070070300d0150040c0030250085007060180036004010411400003501446004541003a01552086544003150041040481d0301c00408604040800d00a5200800c1c05070300c0c2c040824808a0400c00710b16088550700b80c0742c40e46d100600c010300d0701d41d03051249184800882c400380d0710b0b1103104400105a60901c1c0a00200c01400144540b4030741c0c02007141d00300550748442c2d6191a5039488070400f0080080c01b40140c3d403e0104000900d06001c080100c4003000110307102d044c080076000b1405038130703054078080100c0c515003540c2486002c1120408140a89032040754041401091032070020010302e010750001c014004244014004101c402c0c11030000d45005580f1948030344d41d2421710311141c001e0650007804d9505911088041240041042210048054100d5501010702c0b0180413940c0300c0c2c00c00e00c1d40041e5602030003541c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 846847589 1250 846846339 846846353
    0x1050108030f1621020a02130c0c020934090611030a18082a010f050406080702010f05190605012a05122101060e060307050a020703050d0215010918 65
    0x21806020b04907071342e100c132007500c0e2000c01c24135800221005a4001e080c10021850a1040105101e0070048148002c45060401402990600344000d22412030100001d5034460b01d071310300d4000d104c6003445500314004d0a000007002d2440100c4000005694418089a014001c2c1c0b071b107a03855290304000350b10b4007000000445010b404590340d143c1811b46440300080d160310400c096011103040041d084d10005100501c00910341000d00f81d5814040f4944818844075000380680f01200c10604000d4119515020224010300c3c0159030204030340c3c500fa06028004d06031004040350300519090800c031140c1c40d1001920200c80d41460078501040068070340841c04160311a140c40b0a100d58101c0b2200c0240030040302031500a0001c1228032503188100c50180201c5a424500620700c03411b100c00641180000328480303100060121050090000381c40d40b40c14403c0145000958004064072030740c8107a008000d4907034100b104000a130641010005c103c29400348102e0504400110004c180f81c01c0d990b44080d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 846848839 1250 846847589 846847627
    0xb010e131a090f070605040609050f0d120e190602010c1e030e10020406111204050f10020c0916020c1903021c0b13140c0f120f0f0d0201050108030f 65
    0x10303501c3d0041c1e00341c22002c042c00300400c4000d08083d4035030030303152414081d0060034034200b03600035032003500111082d01064072203021480c2000d82041b5500500710384103909541008900c852113400500046103044140140c2481c1c10907034071168000c0c0721540116004a030703080c0c046100d14405451090016208901a91141c01000d55030420307141c0c1400c400124404980003079101c0c80c0400c954814410b40081d090101c40c0100400c0d1b14054181820600840e001e01111040300c0e01424001c65240c0005000700150b6400040042c000b02940c80c1881c0707062580c5190301540d03000342c8241d642400030303440c01d89a003803440361003980c05c02d40d10741c03654081104115414103010b1005035000d056802140805c07010501c5060514000c0c00e19203510314000e20341d00304201e2000782da0b40102c080402195904401c84031524402c58503000344414a02c1964246103000421010034402c51f69001d48000c004200402090441d400800850703076a10304064a030312500144080c08a0108a04980a903d00ca008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 846850089 1250 846848839 846848851
    0xc0e09010905030d0504021206090a1514130213060602060a0f0e030f0705060105090705030a090203010222090e12070303020a0306090e01020d0b0402040f0905040f06090b010e131a 79
    0x11410341429190b03141103604c1030b824075480300d440d0010070080d4180804810181c0a0039802032070340c1e1500c2240300d51141c0766240001c08140340d4200c0103007401d4880d0810303001c410310454060708505201c01c04942140c00400202d015503094000501b10b18020300c1010704559254018007166922802c44800070000952880011640c5101114403010f080020b0002203101107081c41c1c3c3d0f84002d091007890101c0503402280b140000c00100400703940d0160640e6000f10078910b010171068180c0c40040d019008491250714a402d041b1700d50303000717178034045200b03c121428a4420811400800815912024a040c22400070401000000d001171700c41d60007444001e03000d1600180007a1030720301c81d001b90f45411007408090f07034001c02c0c4496240540c0c0300700c09928004540840c90545070510801d541d81151161030b10840d5a00001000e00c103080c4140024164013081c10060540b80f03103001280d094007030007000300b03d450342000513058030ba1000d4005e92486e0400c0200300401020002d04103412001018 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 846851339 1250 846850089 846850091
    0x61b0c0a0c0e01080609010501060f1110050a0209040f0b030a260307170601020703020f150f0d05071d031c05071b0504152d0b040602061905040c0e0901 67
    0x10080c082803450410710058601402107040551408602510340100a40760581591500b0b004220300c1390440300080a070300301030410300115040031000505210a0458800d105070a140c20800b03103070390b0741c1d00500c0e85150890302048600d0005500c00101c418203400290168408001c500100e819411028110540410024040005003250302907a410944100d4082003040c030010003890302e03100015500c000e0a20040018915640010710b125654014141c001c1c02800d00096030b582c01d030030445111481001c80d00f40e445001e00c0380d6000030042142d0003400114241c9116540c0c68010310684e500740c00040081040a42e0410010100703002c8814450900c04100f15010004000e0182d007102100c115440c04034035031818040c8000d0700e40080061121b00c00070326082c0400104480221002011250f0341800c0d0100010000076401701d582100b41ca6400c08140016030039800181c0a00c56030001c6050a92040080501c0d0143c802c25a0020051118020180400780c264a90079a10001d0080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 846852589 1250 846851339 846851353
    0xc06040b0c0403120e01032d02180a030516051009031217040c06030c0c030c060c0c050312061005031e09030904020c0703020a06022b211409061b0c 65
    0x244241350406a9051640030500ea5403407030140d5130b0944190822180c80c07195922128102c1030300004c544800f00c0034004855400700e4045115a8210154030700c00001428040780d16449092140d9640075800c0c0d9051007150864011403a4142080c44900a40d210740340d07514564110740d21814010360002c0034204001d601100500805400e0700c17030a000f02d00558150351a942413420080694152503003903401e0001031080840003d5100da00d501e290740d04920f0005003103c0900c1b0071580904801c001410307030300c40800c2080e02600c4509199009071011500070050000c070031000d0b034003400b045815511425040b112541c29000004180d98840325020980740361540e20800142243c10640c51900d403944002014401c40c1130400d02d25000d000140000d10701c2a48071140700c44261400c217032414140c003081c02008006070040c2d03001104100c0c1d19505220341c0e091101c00f171000308560400345240b12003031808180c0894010030a40e000b00955421074804010242c0c04404543c1310054403001482100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 846853839 1250 846852589 846852593
    0x10141c0f0501180f051b0711060a020d020106080601050616021302030108100b060c0601060f110d08150a030b06280f0515160f0204020712090611030c06040b0c0403 72
    0x8401c09020708150b580c2c400c4400c0360b0755440d900729440442205000c44ca02414004254801422003068804202c07034156208914a001041d0004100036507800c54408102d007012180c01091195464905500070405560b4030740182d0366034402031050541101c030802c090000800c62000604005001070508a01238680b10003e908a034001d07401180c4513007010b140da07036207603815014022410038100c40c014184102ea408103916280107204480900891460a140050040b880c1100c5180100300b074a030542508500500380c00000c58030f910108001a00000d10f030f1a22000101c2680d4012040c481256644000c0c815a60000501ca00710710291081d003401d00440141c034007014110b5a002180310502d04420f00107400d100fa552074422100900100b03070f00940c1481c1c244001c9400c801d40000110103030011400a1199940c06010701e4907a80300f01d0395081d0805045022626956a80030110105030003441e104e00601500c0d0405400400118001c40e550045840d040540d82d00c03131a00c0d00e0790707030303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 846855089 1250 846853839 846853841
    0x52b0e010503180706020c1e18040f0f030305010e06060703090317070f060207051204031101260709050913051c090b1303020a0f0303230405030f0c10141c0f 69
    0x35901550040e400303074803820300c103042c49188c1140b0340703800000094900ea040700000d44000c5070b60f180c0308810200480000c081c001140780e030954440d00302c602c5503845001400d0060103400240a01e024a0507228007103641400e040044514452b0150389441a6a06550310084060041c01e01101d094006004d0500410904101090309038401c45005940f00c0c61880d00c14140703070705414401e45245041c00f040020a0100060f540602d10910703020a40e100500c14040c100e0500200000901703103940d00304201180c0080c600825601c00b200e4035100383d5200c2c0b840c483e60014404008181340c203c0240540b485500400745480c24401e82041121191100142203c5420042c0341c10154640342c1020819424a0041c40020b003c0e15130014120f1806d580300a06240d04d03071003411114007000782c601000208864241c8000d0100142501c1002055141c007039030f0b1385a9555014410b9500580c0158105d02601c5a0303140c11002500766810540301651041c01c2050f0051201420703500e4000c984500b01e02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 846856339 1250 846855089 846855103
    0x30a2310020c060c0703050a031e050411040b0909210906030903040e01060923041104180f02130b30070f02060c1c0b0d052b0e01050318 60
    0x68100050b00c514180340143c0c6882d10103002201c1d00c010400815000c00d902c8011184000464200810701d041c0f400e03072028810141403115140146480d007840300704034645400c0030008408450a00c001c00898082042003001552081d24a40c0130030819405845090408882c43e8041c5140904011442020813125070040b640200d403a00005410b00a1084c2c85e21410701620301c2c1c5c5003448040c0d0521500000c01032442485a00300c074003c104404150b0785a412144100007a61002c0781c0b2250b80301d6400441c9100c200394000294144410082040e5043c0f080d28000740c8268225000c083c1340c501107650581c0245103000c404070b044602c80c01c45505440044ca4040c3d00400e00c03503080d25001d20000c01d510704036040d0300c08540001041c0190044070506680207000d10341e0100450303040a056000050405003120364124003e0b40c1c8120600c1400302c0d8100e60340f66059001c0d0042e01f1000502c0010310079110306030011030303009a9002c40741e500c241c0c06143c2c40610700c450f50020b0000182c40e0f504e8048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 846857589 1250 846856339 846856363
    0xf07080423060703030225030e0310050603190f06020a1701061805060901050c011a010306150221040305160f08032502010c1e02040c050405030a23 65
    0x28000408000100112104016000410110032004081507000408521a89101801701038000c508080c41c0206502c05403401c5c03403280003a65a2007914078014001d0000054081c0c4280512403200c0522203181c040d5511810008026100524201c83c3d11104050180c2e402e03200030344060041c10021b4a24401400d030b1150710303100c4000d1001d0110400c10b04e40d070140c000504120151a2035078000d04050590070503500101d0b9400d0322510800300403121809420300c100c0c0780351b090035030384c1d010341100701d820303180814003a40d00f80102600c85281640301003c0d6080540160b03c0001480601c5007460b003250080354444004a14060742c1b0703100c10b882c0654070400b041c050719480b01d08100040882094100800160000c0c40c1404007145101401e00a00700000103140b010220a808680c807461801d8042030340021220680b0840c01459500703204142001c0380500d14050740c100300f150169081d1011030340c0050003844000c0035540e5a02002002000328105121512416000f9210900030111075074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 846858839 1250 846857589 846857603
    0x50a230a0b07020906010f0c1202030903070612050a06030f150f0f0b040e010c020d08040c1502100e010908070f06090212030c161523040617060a0f1a0f07 68
    0x2c1800d004020f80d6520251002e810701145c8151701045981142002c0d0f80c2d25007040d298039401c940c50500f13a04621500382c0c840d615000d00c042c0881c0c55a081100d44016284183e4100415901c00009004503070701d500000d0135000039841c030781e0700140101c0e004900c0d0040d060701c00700e07040040c18008000e803500e4540b0141c480d41c0b94140001641040d1040450392800b0390700a000b1500ea01c04081e448149400100381040100c400040c24450b010043c80c000b055641071b0001d5030714200000949a00c60b4001150000d0b0403d1417008840c141405068800340e001030840786840d58950725501122941c003c1100c0c044c1c0c07542403c0700907a48a036549605408982c0c061961804500102070030b14103084012440c1000602c41030000a03100c6038005045001790a203210042a214525082007511100d40041200c0016010a04580c002c000c010030741130510141302c0300c0e25070004008451030140620402030040e16170411018024183c00001741c848032040074034282200100c00d80ca5400700300c2c1500d102c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 846860089 1250 846858839 846858847
    0xf12090b071110031e09020f06030702010c080702031305100c02040f02030a200306040b01021606020c1002031e090103020702030a320c0d0c0b130806060109050a230a0b 74
    0x280c100f0005110701c80d101c515080101000c11589031140148541405c05080c1e40e4140b4041152142141d941ca4558001c01d00364491604c100020f01800400340c0c07c03400204814089280140000150740c060410488a54045401c1806000541c036500c0074401c10400310903448005a00d1340d1040006023242c1c55409680c0b031501043e004203555090340e290b41029900d9881c00400b070500001d80f07401540407540401c00400e4034004038601035800c41105200324003400700082954001804155401d815075180b020070803140c50030f9071603000714503401c05005030740710040040c026110000e003510b00050500500300780b40e94000c24540b05807440b0803541050911b108148000900d00904003240b1995002c03003030310f494000a25111080303044654020341d00c00d000d4600704038901c5942c1e005400c0c18500e0310b8a94441c20300405400c03445105902060203440041982d65101c0d18005043d15005860fa003003407482c0480c00300950b000e1500940e0500700791203a00740c0c0c50b515900950010100e2081c500d881d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 846861339 1250 846860089 846860123
    0x11120f010f050a0e04020f0d080a08160e090f0a241701050c04030816020d06020a0f0807020a0b0417161109221103030c0304060801050a030f12090b07 66
    0x4038240c1d412030b910607109410100100003030082d80c1540140d040c3d410139201d400e44000715503030700e1035080010442c2c1c00c00306003404600c1d0b03c14034081c822110b1004a80e001d00c2c0029050340d02c0c402c11580350f40c00101520004101c1c80800000d203070400d00c40c01c00000d000c00345075118440c0d2581e142c00b180d04803a0543d000c00401001840245800030040005c100500741641081598441c600c801400c070342c0701180400d80101049e80310154650082c1459500d6226403625800a50019004401288079075441c9848070b841840a940704112a4005004c029226110004aa18020002c440031100324400780e0fa1031807048040d10344509941c0750086108042c2ca0090120902c142246003c4c400c100704002c1c40701880c03108070b02524624040110080142d0600c02000c060582020f505403000143c15815007100000800c100c5020340c3c1d41c100266203480810218941610015005021401503400030a8810543c0c0902c0c030b2403030a013042410381d114605490b980060074161901c40c1c100c0e203620700c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 846862589 1250 846861339 846861359
    0x120415090504060b1c0e06010b030618070210020d021b06010305060906070f0e030c1905042703030e25060e030102070510020c07050616111002030d11120f01 69
    0x4094501128140300d01c3e800d040c0d4050090040d16401c80c010307031000d0b0f83c40030440f0040d442905031041c1c040135180c05603102d1041c01116801a10924000e07541840f40380e1420303c461740c1542c0644410b0340a01000c42805441c003000c0c0d0010b540c400030341a820055140081104404103046a0074140646043d603d981801d90620070010000d056940044003007004495208000380304800d401e060402c09001c4a0010914104241032070075000701a4880000390401003411f10b00407034100711810f1000005244480d8401020b044006d8883c4003402d40307001c0000c1c004d41102011501c484101c0d000f1318244006000c5081040d01580070100b40b103d0140310340da81c040384440c0d03800000d070025841c041e5980e59081d51401880380d50b030640c1e580800d005200d4003092120f000101402044140c417030b51414511900395507a400c0c00c85032003402001d048403d0501102c504440102c1d50040d41c285514111260064031038044030700388a060800174020030307490700114a03005003c41500c0070750700e60400c101a5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 846863839 1250 846862589 846862607
    0xe091005010201050c031605030a020f0c010617030f03010911092101180213050a0b10031a04180b060a030605070c050105070504050607140c220b06090f12120415 71
    0x18000d050030010002c2070071f850802140c1420903440c08a5485c0e4800d0320040090080c05a1480388503000185d050481701c3c150000e07016151901c401c2460406200d2070150f072482101c040710b22022040c40100012074180d8030804000001c00200c40c030742010000040c0000d00500d40186010403040d041c100d8890092050a4003003400703141900b8040c541e900007a1501c08402c0c02c170b45016454400044920a00d1b03041003111100c0038200380c000401842c00a006000c2010154050300c410307140450491400b80605082158100c0441e001081c56844034800080001e007242d402a0080c140000002c8517880740e580b15551315601c80350140340c180360490030b66002510942c00c0003420b0009004660b500030448030481ea00501036012500501d0710303942450001a0540d51186800000d00401d88490b16412071624401004100315a2144200101400348003003c1d80c020320035070060030f410b003070488030a904040d40900b19211205900c01e180d03d141c1c0300d80c202041000704e85684081050700070041c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 846865089 1250 846863839 846863851
    0xf011d06032512110f03010509060d0c080a140705150a05070f060e06180c191223010e030f07020d02090114010908060c072d080306010f0f17070e09100501020105 71
    0xa181740045c0b10081080501040c000d030742c41520480c002c242d090307540008010000707a200d4030000c807180ea1175019070b86480c5003020555445100c054800c9184402140c03540a440d0000c0a41c407004a010708000f40300e801038001d03a0107200e4100003c034045440080c030b11585031710a035404030b003000000ba40b43c0c1c10501c015108001100d2506602949003002003030a948180007610320210151410302851119210381d4003500c0c09100749a114424410740800140d000700d00b88852440d40302c2441c2c0c00908a0303010300004491078200380700c40802d8000c0c200c0282480ca0004002c2000c6010680000340184020303031054ad4440000c2c4941b0301c455800c10411001810080041c11072490010042c9040c1c1c450800010000103900e5201501e240c50824041c00300003141016a081191600d0100c0d07083d401a1110740c0842c24403110320003290310846012010071103942e19480d520060140055003c00c020b800507040c001d4a2801c40c02903120210034034810b07a40070070300605880c0b0700384c00039003151006028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 846866339 1250 846865089 846865121
    0xf0601081b0906090a1e0906020c16121b21050c010203090a150311132120040e030d060f05150703050711041a0f011d06032512 56
    0x1c01c48541e480582032940040707000004100c91402c6102c01c1000d01020f4880c0c48803615021f9290b045c805141d01411892255500302c030510688810000450343c82c0e8400c201680c811008402c1c0007481d020616226041c1614403250040d840b802c20844d8152410b2480812400940c81b107018003804100003003000780203002451a101a0038041031313800505000d00720b08095030300c0c807111007144039a01118100451b24141600c034000300d184069141094400d4000c10340e6075051070950402c01000b0714004039807103c11140c1d01c115501046000345074440c90740340c2c010f40d5032004401c0c0180520040901c4542d1000c001111800c203819000c10000e80d8201070301500f00d0391a0805105d081c0e9040783c54072078043c240303940c45045130704d040903500560001c6c498005042044a41084d01d01c0d0b400913108450445d5207103002c45100c00110381000a0500d0188007a458410350300c09820040b00464000604860812075001e40520002c0b100940c680e80c080020100d0428080601082c41412000c45100701 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 846867589 1250 846866339 846866341
    0x221e0203100b0f010318060903051207050a080402010c0f0506101809020a050607080f19080a05070509150909090304050a06090302030a031419020708010b010504260f0601081b09 78
    0x426a0041d120340d0b00f5040c5503940303410030010307282404881c881540c420400e01000c582d42c54000e110b500710803000e1412207080404500c402e4040c0c000c2d20340100c0d0543d9500a80d99554004455903400d45106650104040d180345000c2030341481080e00c10145048401601e40c41c06038004040d0f032180c400e500b1001e1038070f2800030042e9a11000001103840c100d83c121b0716403105007480d10a0717209600b4101994600083c118000a4218201400c0e0713403665281c034140360744c031105514103a80d003c80c0d548001030001c002d81409480c05075510038924070380d042c030702e402c0c2051100422952142a02e450a103940049020082ca182020340a405481c0d1461b0038041c3d40d2855020030380d16858401c009042c401c1400c006408295143c056400c0d080401c035010209400c0050041d40342e8415000307180d880e50819031401c2165003d4400c6a040300d0980f201c182d0001145440c3c521203400c09044102240102c40c1c0c6024007510801586000e081c0c4d40e0041d00301446180c103070b102d2001d8590400c6000342d003444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 846868839 1250 846867589 846867611
    0x10305062e11010e0a080c1905010605090901181b1a070506060a0303050d050c1606060306180f0809060906030f060108070323041e060902040614030303221e020310 72
    0x2003240e0180c1a4002046ea448020780c111342410485040c07502c2010704d040ba5a03002c144001508400c00329401551804582c0d01d5079000386090756a9045601c5d4900c146079400f10019003810b07040a03210410b4040305450689a010a0341d14408481c15980040004145a02449024010290865011101c4403240c42c07035550043c1c51806548945920103503904c001940003d0480b084444120700c4404064040b2030b60b00c0c1800050096000c1a40ca00f0700d012030100c0003980301340700881099000014400f0401640da01c5101940c00006100e4008800b0311807240d082c4c94020240d8000e8881d89051421442c00e90001040103500400c01c508240c107005a082088030f0003000d0400d01ca40250f029405552181000b0400c4140c91100b600c000310b03179400030024009158000b0104038801c440610540d603840c6c8120303880d500c2a606243d4141c108102042d0315600c40542040c0c40d581d9000e468000042035181e0b1007003458025000b60103000c004440100b18901070010388032030032000a0402004e0350741 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 846870089 1250 846868839 846868843
    0x714010e06130c17010e070b0f0906090a030b040b16030b0d02330408010608210a11150a15150f030608030d0905070e15010305062e11010e 61
    0x2605803030300c10102100b144180100581000c0c090014a0703403100d101307030780640d00900130b2200c5030400c00203004040c80801c1182c441c1c0201c0300740c8405540d0035400c040d00e5904000b107950007818030300d5004144440000000317010949031340c89a4060b5120303c5407440c00c07100080c1c9030f0840152540805150607034041c0c007540c549100324030003074055802481144007808102d000300c2d000b201d41521240d40380039101c9518000b00090003540e04c05402413240c81c3d5903144041d900d0905002010294207000c0205101c40001d40c090012a0711030324200d2084900404018101001b000b01c90b541a9050383c03c12184191a00541c550701d580b010981c00098504865980713800035290009040002c03454400308840e00c40c0d0485400f6000e03500640782c1d68012690164000d0241e644110780034082c4407000a000b48119644030301c1410403180754071160810400440042030002c140a904c1001a40c0d00b0102690006050000403c518480d0380104070a040103048454043d9a81d0350a07810000e08598070800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 846871339 1250 846870089 846870091
    0x1b06021e04030b13060b030f0c0a0501020303010e1b0f0406020304090b0d0b062206080c01080f01080606151224040207051504021225060327170f0714010e06 69
    0x130011075124400080c0f424001070f00c034865803143d041c840c40071101034041c2d01080c0c2104407101120703401c065a41d40c80c01a40c0700d000900c2591407039100c20001904106000300d0140e1030b622484c1100d0b1405683e501c0203000c542054012100507840403500340200004c500c240400c0764002c56103601c40c290355a940360400ca000500090007186004600c984a410020050307500b1000450305000340d07a164811070790b80b00103146c91140002c0d0a54089040e00031b081b614141602c0c401400b43c0020340c0d50b40c0034040180c007288100848000704111019001c0d4156840602821020b24420301306240e007600103a0ba0014181401d1050341304018000000b0f10004803010400c0c01c1044010b81692180005610009120303050401400344074a100031507001d001090001c10691000c03003001586038142102101c0b01030700045100b40d540e9041100e16000c00800b09221340c481c010300c1c0b009100c2400001e4082d081714030310758035008000c6044020880d212020700d0a00642c60001c0000b203d141c40d00c1661610 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 846872589 1250 846871339 846871351
    0x609080a031812060e0d0305040804120206091809060a06050109030623041425050d06090c0605040f0902030708190e0109080d0e07030b01151b06021e04030b 69
    0x24003103000300c09000300001040d000700060480c080f11102d003401c045001e02007061010000c0d0082d84041e1207207a01074403403180540d400180d0380e4102070808400306200d5104020a81e4003440c1485403918956541e120742d101c10340c18000c400154240a0303001c5141c56805410480303101e090501c1400141d03849020601260b070080d170085031580c0452021000c000b60b60070080034030b03140c000404c01800042000f003803500c1a5481101d504500e2900e100c8054890516885082542c104c0704114600d011f101804000c3e00910001901c4441e03556101075030b11281e40001d000c50000306040000b45140c0305001d00500006100b58918501080000c040c039400038980900000c5000214490341344540c40f1440f90044480200300d00300301810303c415284c21150814004d139040c118202e11481c40419101e08070303540b1207890007042e400d003d1102c07080c40795094107904028040b494001d0b43c0900741343c818002406034000503601c00300071401c0c0b40e0501c6c4150861560440400c400c000141c004403a982d0711403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 846873839 1250 846872589 846872597
    0x3030d020901110109030c0203100e06130812010609170609060f0c0d050c040f090b010f1d09040f062301140616140c0418020d060b1005130609080a03 66
    0x5801d8500588480c5440503491140358608000c000426400c1400004503034002c5044500400c04035000300140e130032038003550781c190300684003003480107020003400c00c03503039201d05c41040c03c151540c00b00a880c91009d900403000210301e07120400079150380f8030078034170891260b1b005003a59143c0007003043d640d40703405002c0030012113000b4002611110388000f40c03036801072040810310003410003e40081881d0080c2c0a1181e101c0400c40700020001c42d94800e21343c1c01d00068544480d40b01a400742541c000e51655840c08030100d01c3c003041c0c000c96a0f050011885503205400800b500d00c51810a03800b10b40c1d0504c00341180d400c0c400141da11001101c88060b04644489181c910ae01c2c984502140640c043c82c80141c0e940280b40900c10f0801c0105040c5d54041c9149000304c40b2080c040208001c1581d8000f2000c0c8078010184d244c0320f016040081030042d03514014000400c501d0740080120380100003000f1800001040401d8100222144203041d43c000d020314500010218102051303107813640b105600040c240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 846875089 1250 846873839 846873847
    0x311070209090703050a03030e1605010806040504210503041b0e0c030406020403200112110f030a0908030f040c05090402010f0c0516080714090705040e04240906150503030d02 77
    0x82d0700704209a801a60b07004c000e64002a10302d150140180140f0710100240e402511401b0400c0d5040c2d90665040391416550302d070350364660000303100c000d003130140c0155a10307075619034006580340246203a260350210a55410360b8915103810194080c2901d054480000820118204031240291812a4000b540c03800d445a403034956161550003441254802020b40e4502c6d940f158100758000c00d81c404e0281c0a0700c50f130388a102011100700480e00e0002d080c4c20451018004560900f04110140d9030140c202540080d600950b034441001c00d810840f0003420700515603003000300b0802c01815a2000f00026240c0380740c0c0703080a40c0060a40a0000d1490301084507100d25041130280410a1000b08100d82520b510556100c030b0301c86448501c5802207007090580c40b1107001c9541003a021441c071903621541c60303a00301810240c4840700c41c040504240c07410020141041010301c080c480e0061440c6c0079400005039500c4528009054880b201c0c00d441c440b003080c5000b00550b440202c2240c80c041e1003400016a5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 846876339 1250 846875089 846875101
    0x60605180d170f160606080c03060108030f0a0e0a032f0f010c0f0204050403050405010906050f040b131d15101202130e0a020705060112030507110a05060c06010609060311070209 78
    0x610300401505121800c509100c120900c0080c2d4040401da404447c05c0d5030b860800101030541e2503400388198403181e4000c0140c5004055410041d1405c1005407400b039500c08086d9002507840003207900305440003140c0150001e820f040145a449036035842c0070705402c091a02c60300280465001007001810b02c841e8030200d50412120200c064005940100708200c0c0c4e0900b814014020342183c00383d140820501d45001c80c00c03d00460a0b103000785a00d80013149020705240c0846050740000220741c0306030b1690413010440c4242c16880c1d861040c0b0b251000001e5240a2003180c074518149461640901440d401652000e5400902074514422160700540c1d207500c00300800e4a1038849521203496414078100740324240364560000d0110701d014a04607038050362034a41c0b00440101880008002c02c40070040500000c200c4e4502d1315240704002c0c03100580e03e9030340740072500a51002840c4a000d400070300c014052070b074220341c030f10019102925040290300103c0503030180c90711440b40086d104404076400554 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 846877589 1250 846876339 846876367
    0x30f05040b0703020a1e11060a0309120201150f05010503180f030c150105120703122a02040c08011d04140d020d020106050d0c0303030c0201090501060605180d17 71
    0x1c0039103440050390b440050038000c2d10b8100d018001c450800c140446035030b40015581c5680c2609410818140104001d24100705082d4042c400341000d25490740060303008650b4903041c03141090055000801d1200c14468169501c20301c40c0c02c0001215400401031141d6640041038035442078002d001c4442c0c0c00c3c41c90300b41500d0031801381801c0c495440f00280300c3c440000081505540c004211865603140e0740c0341c6040018101b5401c032001c0041c0d002d0001040495059000c9580741075a40c140f51000031000080c220401240c80c0440ca14808040ca078402142064815000842001c1c90b0060346541410740402c444080c1c08040045000054081824030500c0c3c02c0c100b42d00042039049614685031540c0180d00c810300904800095444c008001071141003040e07000c51459400740d00b0b04c01140c00e69605500a02401081e80c00315036840c92070100045007480303544087c121a483d04d030340351b001101c010500c451300091154041d04a06006200140410300742c04e40a406501e60b160715100070f036440d80 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 846878839 1250 846877589 846877597
    0xb16030c140d03050c0304080a08150306040308093901030b03030d050402130614040f240f080102071106070201021f050109110c071512050f0a0c0f0203030103030f05 73
    0x16019580707010600c0e0346060005000440c0302560f0b14148070580e02c1000299117400100e4000d81404c074104005582c55105212842e4400c00c200102c20800f0041000300b841c00104031012004501c025040c440c100b681000028080c0302c40c1030310b685e000303503515031800c4902c0c010740c09802517840c0700d040c003002e2030380070780c100300010036016080b00d86070b400031501100501010350f0142e001c1d07202c120b80301c0c4130704071980038110640720f91003204588a100c04d014000104110700a0819540e83c580d121080e02200c481c6c100c41c0900020400032143e81810465010041244d211010301c0e0b2041023800001104030b500d4600b07002c4110b82080e103400c2d640c00141d04002c2c1c8480403040d15841070740542c204081d1a403200e0b05071400c006c0c04000091001c0110100762141c100d6002050b4003a2608210080030078821440104051030514004c241c0d0b807070b0784000e94005440884520320b0260401105a80610070344480040c90f00e85462481400140139440e48010f00016003081202000288960b000e00110307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 846880089 1250 846878839 846878843
    0xa081503122a010605011412060f06090607152f0708040f0f03030f0302070b06040f0204050d0f050c0f09010e091e0a0507050919050a11030717060405010b16030c 71
    0x104140100820050f4000c20307041c043c80d804129003219a0541d245d0a0301503922440405d860b600701d07916075004010601001e00e0407207610801c20401038010380c0b290805415120f100741d212612285040304c10303805840c00c02510a124412148110000050b46a26004039100c043ca5144d6245494140b5554520807070304150401c8441e0b001c0003800d030001c100c4000440b80240d0b00c041291021420440a034454050040c04001500010581c2031401d80d200c0082c10303035036440041c40c250f078800c0030803c2041307071100650307217601c00f0b40c02c18041c461305001240800b02c1c101c408031407020326200092403a22040c003e2070503150820380050b11002042202d0141e0400d0050324002400802070001d40c0da4036074150841c0d15000b1410700155030b042406005002d8900e070444524070940aa08590092100800c0c40c4040c94540503252415200000110b006150035668219030040d140345000b000e150242010303015600d4100108a00e15145058515840c12009119940500380c14200d032540119000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 846881339 1250 846880089 846880147
    0x3030d05070504080d030507050702100c05100209031006080a080703090f15110c130c2d0f0e0a030b1e150f12030a0c0201051b030a08150312 62
    0x91000d01038001020f0821140608222045030303007030f01011400d5400688042011880500606e0014030b401c010504000e54945820074000c400c0e03031940c925128140c01c0a800c45680081c1404480c1401d009003400c40c0422102480410703e00000c40f641c814017081c02034040c00380898410304161003031420000809481d44c0c0e195209840740700c51051082c1143c0084081628080100e82140000c5040410144010300702d246655104240c2009804081042c0003040019001101a45150014454081c6181c0038a05014440d250b002d00504061550311041c086010704400007552040604001e8a81c401d2480302d00b601c07032058070286007510317031b9202c01141a00c504004040c8462115010500011940300400d400e4036014040e41841c400032021080c0c008000d0651030031701402c0000c0d00a441031400601c0c11000f460908050302c5004d101a8564100080a19000f0b41c08035900d41c00c91024101c00500d13074450740c0001d0341c2c0d802c4030940020301c190100e0000f0364210035602d1010b407982081030f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 846882589 1250 846881339 846881341
    0x310030c0618060e090601030509010b130e0f070b25020d1518080f0a0c02100903110103020316030507030b1002060f0c0403032c040f052401120b03030d05 68
    0x4042c08a40300a8640110300c000c842c0001440e9200c0c2000c8062200080d011812549450004402401000f0440182c56480f0070110445480d0494180000ca800c01d1000604000c42640c007400c004a000d685101d541c4111014082584108115030b011780c103510040e4003040c1ca900c0c0e0103030b100300c1e85200603500102e4020b03e00c007403080c00440c00a80c0031250301d01f0084080c40d0540314230101042c0e0000743c0520030134031042a0807001c030f01c0108604405811718440541055000505a0300607048110009104400401c10461140c03441c500c0f4039001d080c20341c25890310710f06907141c2c4a0300e80045010507484030049001d02c4e0007070b403007604006805440760a01d06003940f0081d660f100d06892540d154080d0100103078114100d2000d0f45c09883e4582d0312003041000c1c01080e10040390380000700d032248a4001e817104003182d85a00c00c00305080340c0202c010581c0d01e80001b0003010754100c1840c0a0000c108003014407401d0384d05c0b500d100c2c84d419808000188400e05500481d00d10f000304031108099500d854 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 846883839 1250 846882589 846882599
    0x50f0d2003090f0d0c02060c0a08040305030d0605060414010e211609050f07080915010603061401020c010206130809040603081c0608060609070c06050a061e1206020310030c 76
    0x40c0041d071050581e641207071150361110810310350b1114911001000150268106001464120014007080e21208200c6001d01d5880d1a94001d640c00307580222001e034800504100c44150304d001e00002040c041741c0c50b50034945040b0400c0000340d0300e1101681000b5941c00c06100c155140500c04024000180300704c40b45d294000006a500c090902d044109904922400076807190180625072060801e001c0320721207070315040d005a508000c0980144c205000d40002074a5102c640c0b1003560003408259404180303507141c80100d01c04041000d120f6411500a4060481d60380d0700010703803d40203a1000300d0f58420329480d04000000b4012200040d074000d042001c00024801c80c00045c1c00340c041c821103107001c0707890303040012821078182e889120116004440003c604c0c2c41c3c02c07840d05500010382e017803005561322150703070705c0040301d4041381c003100880d42d203600c00e0140c020020300300440722040c50140b0303d1942c14541035580801c6800340041c402500000010107003900317003920300011540840180c03169a124 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 846885089 1250 846883839 846883901
    0x6012a051006090b06070221010203090a06050603060402030a120507020414010f0b0403110906041103041a2a0304050c0603010920190315120803180c01050f0d 70
    0x1846614403450504030041044010f51090080d0702000420040c9800003590a00c0158043d00c140070070142110301c48803111000070300040d84580d10711000f82c1800142c0346406000c440002e40b03458043d9010004110040e200052108000c40d04543c2d1404c0100120310116000d105110000f034205091800140c0350102000300c0070705030b4441a0419010940781c0300703100294000d0788005006c2c107a40b5600310300f0310700b00302d108143c12980140010810503511200e0303020b994026501221070020100c1340c807001000200040e034104c08201da00f40c0300d00510190007010305032420841a452031000021504005081100c2184c4001c0600700039202d61f924100c480041c1640d822141c43c40000491100d0131200d1070f81100c1e144103100c7c02c3c41c070700025650411402040d0030847c0594029071a54003107601d00b2030b01d03030040c50035125101c8a542c9203010320034103655080302000d00c140d944c003e41e110780b8541e8014042d52900601700280780c0d01ca0107441404000703060280e0201111140c2107200220b40303812 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 846886339 1250 846885089 846885103
    0x8191103221a1c1811040906050f101703090f0d1217090a030903032601121104051308030406020d051305191203020d0204050907020f0d021506012a05 66
    0x540c05202c2c0c40003c409a51006450448003003407100c1d244076201c040054110724502c3c0c111400034200169818680e555a0100c0750103403180040a078a1000300818804410b40d118080d0011004229400100c001c0300c550300e00800d110140703c1d190100e4180c6e6503440b404c41a928054020548801012020b14080d01c030808140840109880400000320049000101d100c0c1c010341c90b6071944051491518100c6a140c140f00c107040c0d028541c209484904039030031462502814010b604042810980d03d000791918845c1101940102e0a201c2040100200990703814601a00000700d29641c0c1c0c0e0ba4507041d030081c8201050400710a280c44140544540074078a041e030b442d803081080721100d41103180c21a620343d0f80588010804440c562407540d4151190b006825084000034026007400d4980000507807181080740d10b10b0050380825400600c0610030410850a04001e00181c6620390083d0035138034201200611007418401e1812090460000816494110305c0c850240c110701c04c40c907458500c2c1c41d105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 846887589 1250 846886339 846886357
    0x3180803100f080d05030603030c0a12091d06010c0206192016140d050f01020a091703070204110c010e06071e1220040308191103221a 59
    0xd4100701145480b80c0d00d01d034405035424440209292445060102e5095000504080d05800300348108120380340104102524144680600708103810600001032000c2d2070781d8810b01201d4010301c3c1c0c10802d8819400c64541083c42072034407022031762050000c91294451901c055401c412484211281c0c2c40e070000031020070200d08001403c5005110800580d00e80c001d100055004090010070054181c10780c0300581c440c44003421122104016450b10740c148003201b0503c40a85c0d40004070100020750005804001d410003800c0b070500c6e10030600c035440d030b00d020b0f0580c024003c40d80c40c643d00300c40d44801d90548201c003128100a1100304030741114a42c46020035501e89010a030f04202c1c60803031840103400103901150681e29485c055441d028041d01a01450ba2020321508400d10b0b040305500122008002a40c003494501c4d903200c1c801030260000750011001c0700304008200400f90700d00b05c800300031218080840540811650414651059210000c0e0711014044500000c6072545500d01009800848 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 846888839 1250 846887589 846887611
    0x120108061005150d0b0a0b3106120b01050909072706020a0f0f0503031003110411031503070b0a03090201030501050301180f1109150301290d0303180803 67
    0x50b511410b000d0140928503c0c0303000c100091100c050020300d541d00084400000428030314845913142d00322905075004080900801c403a405c1900c003c074515042d845094a03600200c94101480d000d0020090038101d410350744d00f030780c482d90f1004042c0e108070141c1d0700b540790084c80c1c01094202001c01410391a1a0075406040003250120079030a01c15410b0000c041b554a0703000303000c20b014142d54046031004140e40c00c54060820344c1100e80810f1041016512071403090701c03190501c3c2e00314202a103071464480081c1e0f1159003401c0310181c01901090959410005000d00c3d00e02c2c800d403c10010742013102d10b070003114080c1008030710342805652540295031018000e072010000e0340d0706d54042c1405d85030102d401540c40c005500800300001c121044184d103884c001c0c034020071404036042c009400300a064501196219040c5802d071f40c00d02c0c0078400e84280d80c0c50800103144621503841a9000f1007031641c0b03201c0c42441080f00900c18076000303400110300f41c0d8150b0f1b251004040325140030f0020fa00240d030442c1c000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 846890089 1250 846888839 846888871
    0xa08151c0204050a06080c2403040b180d020d050f0706090b220c1202011101060608070801060f0915030b0a0b1306052502041407080114010525060212010806 69
    0x44c81c9912401043d104948080d017025400a000e1000d2000c08050303284030140007540310702d086060300f40618001c910030010701d10181810b01c4141c2d041d4582c28800c01b4950040e4504444080d000101e165041505081c040c1e29080d600c0b01e04201c0f4003402d03a01070b01c520305060031002008500050284a1003213000c0c0900300d010302c09039014040d42c214000406d4040018403d000c070a8076418002c950b40d10500d4100d81803052160480c0c04e440c9030354441d001144002051040c01500460000e0142a062414800503049080c0c02010500d1600c540c5c001c00c00050018192240f01e6081120814005056450b550340d407140381044980c0140707450310031a0f80007000400c40a20860490b2445401c070120185c1d0000903010304440c29880d440120b9116039959401c48801d101c020046e84101c01d02c1c3c0b1003003403c0d850103040740801903868102d070341001030401400d0010305455072036141e400501442d000c0a4900740c54000001e12410030030360b4240480354000075600500051461251040106540c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 846891339 1250 846890089 846890101
    0x6030903211d0d05030f060d05070914181b120d120e07030b04060e0316230606150d110403080418020f07060228031d0a080a08151c020405 61
    0x890840c00d1643d00004d4081010a4410040c0208642c108900510002044559036101c03490442550b20882c0d450703488168820388010b29240c455800b02001804040001d851a145070300c1e501d105292107030329000f4055199160b2078031482c40314801041821250248441000a452045c40b8102059404d090181509801001184290407a54030480c01051074403540e032004003910070700c1a0070580e8403051089500f180a000045000c0314040c1d14170010041100c00b588110707180c2c68818103c15800113091140c551501100e1006014480c041c1544400018260b20003070321060100d80b1803000081804030600049900500803a00e003d03035403044904e0410701802c164011460340360000300b4140322201c04900d0341d40040c252185a0340300e20000c071100c10560f000d4552407000d4040020355500c04840c6a241d0380c000b140550344e4200041280c02d0103035880301d0300f0b8410840b1500c1003200090200c0c0e111141c600c224040d002000b001c0410110151120b5401507201c01d006a1045c0d041c82d000c10700b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 846892589 1250 846891339 846891343
    0x5030708010608150703110f0904050906092e06030b27030f09031507110c010302070503031501090b161e020307050405130606031101022506030903211d 67
    0x1141c140f5405041e82100025900030004401003180b4141615a00e00030900901071006200201e07a1601c0c068450403c02d0600080f610002c0c401c0704036030b20031b80500c0200f0100040380141d0007010000d403a84114280801607540461200c1040224145480441000804a182c4e33101d144083d01d480482107040c0c02c101b69402c258030f5820003540080000b41c01c000103180040c000d851000cac0c2103a10b0b885002c01e5028005400b1910b4000003081035000220124050105484154007440c0c00d500b4105191180d58403480041c240d0301d03901140da8590084c40e400b420584000304800c4014545515006200521231201c4a00442e081d26200c3d004198903160281030345060794024009000c00741c281002c0c0002850003501010707000030708036020070024406004003400f07144502c164000e0304644800281c5810030480c0740f881303801902445403442403140030f00d2004690051070085026020740c181680d0758080701601d00d01c1c8003180724080d001418550003282d005a00d080d560f210400565500d1a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 846893839 1250 846892589 846892601
    0x1b03040f0b0f07120c0221100209150c0303040b0105010816030c09090f06030203070b0f030c0a140705010b01021216080c07170a11010306140d0609060f060503070801 73
    0x40340c8140015828007102140300301400360388406020461030207045490b01078107001008a1603002800d070180b4002142444060301460344078015601c1403000c0d40c66012515205060801c42c4c0ca01e07800b2403030405541d510003044800c4080306d00c50036910300ea42d21000d078403680102d805840c500380d440000959548140c9100d80304850900d9050740203003502d00110b002d08201d81e5006c00f049008680880c0d03102052040c59071019840381c3c001180c0d861441070600b05001548140d90468060042c0d504080710402241d5203c085000810f995900c44017042e25800d04541d80030103800d801107400307401c0210550041c16001400d07002c031403440010f80d403000024403800e8440380c0e4965003c1036200003c2c00c08005091640540301c15914055100c80e0202d0403006500d031441c101350701410446081c00801c81c0f40080c1d00d2428030f4203000407414610802c1d0100300080c0250f006800900c444001d103c916441700001035440384050200d0801f500132140a080b8600500e442800386400c0040e500300c4c14402c00e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 846895089 1250 846893839 846893849
    0x90f0b06061204030e0f0a060c030914030303010611120406080f0f040206092b03021c020609120f1b07090b04090f0308040c0306020409050a050105180402090c04050909031b0304 78
    0x982e5962540c003114611141000d80750030261142e503050569560980045c0034094542d91803200b113200c2c0c00d004005c900d143d030002d04201001503003040e035520080101d9040d91400e09214007070240ca11003192a244c40c84604000324034001c200841d0007640901c02034003503440800c1821280c0c8501101702284d040507034001b980900b0802003640c45003801c1070400010031101c0303c0b40030404c011a5500d082401c03404002c60060704440d0006c0c0c42c1c88a10404d41901600c20b02c002c002c80d05e00300d1101135a80c02700c40f0110212020202d201c0d8032100301d4400f140d103540381c410034101f0b101003054849030340d174036042c0282d400d150f0070511501460306040c1305130307107403180c00c00106500d40c1c01e240c5007a540b4040140050ba03401172003240100c08100d0500080c001407059110010b114940700610404440c41030304135500c81d007003040903005544218640c0341d401a40495580b940707034844180c44480c5118035848079420115510411101c54400f2028100440c042c018a142040655800307640b0303071055000b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 846896339 1250 846895089 846895117
    0x10216060e010e030c01080f1008030d0e0106120b0c07330c021f02030a1805071a072004060807090e0d090b0313230c0a0807140402030a0f090f0b0606 66
    0x202071202300d06e0700a41180d041c1d81010002c03a25481c0c0c560950f48130181c4100c0094642c80700212060007446941d004003035070300c8880c54400090340c940c60411000380a080d4051000f01b0010140034100c0650b100c4045403001c04c10022010500c04440380084121080c0308a160100040806001144070004404920000115002d001c00780e88001e40002d80b02840695441910040c41100a07280110f400d0280004103451840d00078014840c5100f000b52402142062200e80b000482010410b1700c4c001400c21a00c0ba00038a400100d0000c00c2a5403000d80c0500c94017030002502c3e8440e41c41100c00200043c00da82100c07082040c20b5a0000e040d2081058014081001030340483c4840340341a21284100f42c603443c003c145601203604464016500d0303c558010601c0303030080c0d2800322800c1005104510140175404d02c0d0610a80c405001d2892503030207030b500000040c06400c455072024900122200c020001c229440c104049001c038035510480e02d80c00c00d000442d650780b0f840d0081c3c9450510f4810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 846897589 1250 846896339 846896341
    0x4120b07080c0c030919091416020a1703060d0c170106170a03050c071802030105011707091403070308040602032203080d090303020d1a030d050306030a0809010216060e010e030c0108 80
    0x42c055030044c01b0610940030403400501282c0020389001d9130420310182c012074055030600e13040c0d420b807190504e5501010b561186d864500041e06904010100e4a11210015103941da41408544010300c8000000c051107802000441c0c0300746200032600c20108100020003080d03440b00c0200c1c00d1070031040c9600b11164040c07000f40c0300017445100180780c419041d00580d6500d55a400d54007180900d4088071380d40075500400180502e5a01501344c9008482042081800d800d102a019001040e107004140c0140c540340c0d034100b0f081d01d04200b00c00c02194072000141e07580343c1d0f6080084d200d4000d4030000140ca01d00d01c0041146040084900c0140c3c1d8001d564035103048064400d000003400200c104400345502070100e00b20403801e51142044414241200000c02c455850806041a81003000c0c00180f2005106000c071986002412400700d691005109d0781c0c80e941c1500603458104115038660700c10540700d5020640c1644028010401c240a0700c49040300c101c41810151100443c50000d070005a21030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 846898839 1250 846897589 846897607
    0x140d021906230907140405060a0e0901180c03060e0f1005060f1f030c03110d090602160606050307060503041e080d02040b12090c100302030c04120b07080c0c03 70
    0x503219841e0012006072040c1c20b02e070b515244040070365040302d01c051036400c01c040170803802065200d40512a4001c0710104002d00d01a00012404100d90003031806152905001550140096100090603054800c21180c03000300c80c50070001401c2e85020880c0c03482d04051007403421a0000502400c040b00c82c44c05090250317911820b400c000c2000908895001c3d814544460326501c98030400c200010403c100344468003181c0c840502074819071510b44040502e4070fa00000131040d0300040e12142540d500e40800c2c8403061f4140322003e4000c41600f0000e000f1040320300800c000783c543c0309a045404c190203844509030f60310402e4803580001c85000d800ca000003e0b500001d04d01203032a04552510076a1501e05082c140002082203070050b400c041000e000020301003038010406894580d20122200007071404e40e20f1040425000184541948245500800400e90071030f8000c090390090100c4505001c03195050b42041e0409610590704040071488803008210011800e1f411908421405270085103058102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 846900089 1250 846898839 846898841
    0x5271c0203060723030106120c0203090d110a05060327030708043521040812070c0305241609180608010501090203011d0108070e0402030a0b04140d021906 68
    0x381c130011381e45800034120708030f0805950014602801043ea1048204c46065030542c00300d400020002041d5032050124a02d107948620078405410b520440701384140c400000446e400701c801e600003d0f4400c2c000f10400c1444900c0b161403620415101c00d407421a00004d24046842e0300c10500701400700300e01044140448240c280c22010000540707100513441d51403421032172480240e08503805119420007030400d802d161700c40c0d04481124400070f031080e180030300c0d104126684030401285000c2d88000420070b8405c2c400200c0ea41001141c200044e10461004107504810094020300030384042c0e0040000320340b90b91520304813482000c0c09525000f4140d4140840c00b980e103030300440500b60294a509001c034203d4402c1c09464020403007040c016032254103100304102c604458540d0b80043c01000401007141e8100020040304035000a01103da09403214004a0b051a071003400207000b5900220a000c100811601500c403010341c46020341d4181044158102e031260341d1000e512031500170300c0641001040381 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 846901339 1250 846900089 846900107
    0x17040b0c07020105070204110c0d1707081009090602030a2f0d11040f050f0607030e210124150207030206090102030c07032a060c1205271c02030607 65
    0x14180b0350304084541e8001425070342504a52366031301340003240d1a85201d10810041e0b15000700703800c206d107052885811a102041d40100079038204a00d28004c00d6100070407a90800c00341408050174003282c615410190040d5100340c41001e5460300d81040008891f1209001c00c400d00748000b1840e03050300701e42c2020b4801d1341102c02c0303a22000365a20114016508010b0081009010403400e05640ca0710380410008801c031240c80180c0540010008440001da115a031140040c9040b98585030074401010030201a00781e000072022250b20700000403804490005085602d20140707190003030030035101c65505a0009180d80700f0005a4440a0b0a20051030001c0151505240610440e42801c1882030001d2400c0354030751050304d601d41c00100008202d02c8070700400d2069441900c0741d040280c50070350010100304120f00040e000031102a1009500c6104d14211000409088080c1c03444006483c4114042240080b0b558480c840803c0201c0510b103215270481c070850307002000352001b955285415140801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 846902589 1250 846901339 846901343
    0x20d020405091905010e0c190e0c19170907081b04111303030e0105161203090c06110c15041a0c010606031b02070e0604110c01060603020a17040b0c07 66
    0x9035095480f00d80300e8002d001000c1c24012000803603601c2e499000581414811828580200044880340c41caa070310300403040c8200c0341480c00e050155076941c100703a4158001c82c12000803007440030025003807555000c540c0921098824100ca001619607a400c10b51b9800a4860001d00d9000f0109590105203500c0200c00c2e21100984045100c1c003010150591f00d80c400b0040380c60607902c2a0060092590090704660440c80a0800d2071410582e4004004015441e070300040c0b491175400e0051a189100743c100c0c204040d404160240010348945010313011030703601812400c0520600415114525000c0001c2c4c0407090044007542c605401d12480c0a2954a05141401c2d0a141001142c450010034450100101440d54002030181c0c170b07143c051490303030002030740c400110340c400c1d0030078000d18a00741c00b0780e900306504460014003c80300c91411140350007030154a440d65403800c81c0c0000d801c1d0305500104000380300c6036501c421000d02000b02615840c0d080d40c0160403090507100050359021210000c001c100c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 846903839 1250 846902589 846902593
    0xf18020913150b040209043b1504030c060615020c011d0f2e090801020319150f031202070b0408030304020f060705061e090102072d0b0903130909020d02040509 70
    0x1b102c8000c9825614040c00e40540c4240c40b03d40c1c04800208002d001e04460301c1a4600e074641e9100e003007042d030380e01d00140d03140025800c0000031804060207a10348149040d0300450074031101d41d5131004445a00c010405990140c022034801d1a03981d8407032403902d01c203c9980141200c8032101c070010702079001c00082c059034002c0342d14828042103240c80b00e150041070151100c1d40c10000f004082c0181020700c0d43e07001d01c1c0c3c20383c018400d20030f0401040071071210300401c410002407818044c2c0e043c1803e4101c607070b000084100e05102c01100b8007100388881c0081034243e4003192000360303450f0b030100454030462007910120740050021600614100074003051425000b401141080000e07100d407401c0000070b4440f07203040341107035091151205a01c03904e641d0143c403040003142404804d0715100048145941900846100c1d1001381c01c00040341003d03120096040015002d031840c000407819501d9001c1260a40300028130100044c0d54480750107203440465018098000070a0b0380c2c1e0a0102130400500525414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 846905089 1250 846903839 846903847
    0xb18041101021212090c060f0d2a11010b09040302070e0601300b0103020306010903171207050703031a0a2612070218060a030f03030f18020913150b0402 67
    0x1a000c5400501101020b050390780d0103d0401540c07045c68030080300e05490040500740407500c40e0007614416103080c00340ca2640400c001d00c0c82511001005036452140b400f0601c103a01e80340c03c154bc4200540c0308904998001c2046a00c003004100030f20000b02c3c0e0060040e80a60020f0000300b00303001c0f5050300070340c2c103060042c41c0c4e420700144040e4a1404907180610700585600050405117207000e100b01e020002e090441c514104840003c006030f045010240c0a0100c0640041a42061701c0031614420302c00007030010141030215008081d6440340302c054000905000160911996000300700d980c620009210300340e01c5103800c001d811190a602000080d00314121010014401d00740900045c400101d003580d5661402841044040100940290000c3e681c1400308000c0741c070741c040d030041581d4000d0741004c5504240c1c9000c030043e00744107422204441c18845640030505080b4610b6404a1003104e210003181d81d4030002c00c20451400310043d140a0220300c1842d00b2030000d9100174000440070b0b20151030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 846906339 1250 846905089 846905113
    0x50703050d1b0f03050f0a0c0210050705030105120102031509220503090a0b0c070b1e0a0903150b0915030a0c030c0305061b0f03070504090f0506040b1804110102 71
    0x2264044600c101c11041e91080305540b0340d40c403001400d122040743c01c0c10000342c203044240204541e03006180000259807118107100c0c181c000c108080220882c10010f10075480c1905c8001d0141d0020b10640e4001c0e450488071209205c018000e503071003600d0049200704200c0c2c1000c104082c110b0302030042008080030310b1420400800080b80541d401e03014030011591040030b00c0511414418641c402000071034107001d045801c9102041400403941c1d003140554a074010b0b240c9501652412400c024103001c4009800105070303404c01070300400c403070181400341c585420620303000c4190b0341d60000c00da510801c001c00144000401303041d00c3c0780b006030140454203107036030035a40d004000d85a0f820a43d26108808810002c02c00b040001a6001d03503c003803090321844240494103198000c001144000038808400900058480c030305884c01840e042c00c0600085542c03104031401041d0540c2d40e036020f2418400d02c0c25250810341003004559545a42d00c2c0241d9889450b201c10b402400707407496045025010401300307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 846907589 1250 846906339 846906341
    0x3031d061e1b1e251e051504030201062402010c0f0c15060f08010b0a081501121509110a0803040f090f092a0f0608070315180902040506040b0d03050703050d 69
    0xa1a0a249019141002c0d00707414000c3c17202c011a081525140c4020f04c82074005440880d4212400054034007212880e1528034007a0301400386904111362405110501c1040d800342c41410801085498008004070202c0c0782d0100c0d0070b01c010031704034008a480d00300c40f90700082100b58076441c03c8030310000c00901c6649807407450b88103900a0748810103d0703440311074441d143c5c581496074070000c1c196000206440f5206000c003206a40c014401d001a001900c1030301010301c0310720058003902501c00c0310204a0003940e0700e040310034111405980da028001d040e80118840c1c80000c11107041d0340110721a03800d42441c08200502408018085c0c40b40c0c507407524040c2c00003400b1154002411442042d2400c072110680200012031101a404211003640c0d902007081890380000e00c10f03800000c546001319180d0000651380c511080783ea4803901881040394498020100c030395100b02d9840d072080341c0c14031a68841000300020f6403111024140e0181c00f134019440000e000320003e00490b4403e051103811701015051400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 846908839 1250 846907589 846907627
    0x90e04020a09051f080601031110030b18180718020a090305011503120f081311090f1b03040c0506130b030a020d0606021903031d061e1b1e 61
    0x444028019001310001c01280050301d00900040001040c056155449029401710841501d40c0900350a6100490320b5210f50008591620b0141c080c03a0352006082c50302c3c103090400c4841c3c42c5d121149124416240780080341030412202655040d405a012594950000703500010000b070520084000001c0069000e0203040003034007002a10306101031650810228558048060000304451646e515a810360421032030f60308182403244280c0720031410310b030124a0091185134107900690a01c10000e03403000c0c00600324130820f5400c2d10949800c104001d00c4000d80401d42c0d00a00315200300c45e09006a0030080080d1028a112040c041e00b069030300e241c941880d90041d510a420700da000102d440350a4154081c240050001e40700034184807580508c056111703e00b11030700804040d01c2e00d040201241d07581060112802003901a907506080c042d00e00001441d00300f01380750440080c5400070354100c0f007840603040104a52200b81c0e05d0005000c181186800c2c2010b02d0300e8007a9024402602180a030606403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 846910089 1250 846908839 846908851
    0x30f11120904060306060902190908061b04032f010306030f150b0904151505060d0b04200c011505030a08030a02130905040302010f0e0a14190c0608010603020406090e04020a0905 78
    0x103a8496901480700c03140540f89c0549400d20a080000304029000041c0c2c540c1d020807481c0074000c9040b4000d0390b8035030b140b00d036610180071500c50400c80910b007414a40500c46101c111480040020107a00041d026200544400781c110513080400c800400c4a1026003803081004c003600051403004813000a04603441900d090b43c1d8100b807500c407441c2a002034881d05440204180314200703200e25020000c0d085206880340003c00c00d0310f482c1a00410b840d1a0070011052070104a4442142e400d00711420b00c98205500441e0303158204442ea03281c02402e0030890060390000ba0107480b000ca0b0989811f4000d0b030026103e41e0340c03141d08005410142c414582c0c03103c040c200c10240490309080a00b8003e0a498400d1105810703a803404a45403000c0174005010080650700c0180c02d80c0844030501602d050083c81c130120802c0303041084150040211a2030300c6001d661168682000d50b036250201281240260300807e40070880c096820301480221850f4964024402170040040c151111001c6080d05c205480c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 846911339 1250 846910089 846910091
    0x90b0108030c0d030605100e01020f0d0302091306030203190f0b010315051506041401230702090703050603030304020904140a060f060b0903070b0f040e0f04030f111209040603060609 80
    0x5142d0109509101d2280190300d585401d0164a06110004d1302c0d0007c00c84080d018001000d0321988542d00074400c908280c0c02460a48540302c0100b180600a5440121418800c50b050080d03540c0c4420a42302b00001e03a600034004003c0107002c10140d10440ca81034105840302070302101c0c0cc00000c0d00c0104101e0227507100d0402170015481005407181130300c4002d0122560744c540c444040c070b903030307103480b010388089501070040490382d500301c0070051720030400e10320049090f00c0d40c01c59004e1840b01401d004114092007558010925541d2030400c07802c6800543d80294550410004537026203080050560003d000340b009984400c450020240390510682c41212142e072200031780018100b440c8240401026900d055518025500c000242c59540301d0160000c0c0c8071010403041c0b01d8403103407010344015100782c03030850b46241080c01e0344030848842201d0403400261283d40400301e4a100e0a2442554500c80e80100311030400c0095042c004c0d041102120307001580d42c20000040350503809120028580484 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 846912589 1250 846911339 846911347
    0x1309120e0d24110304124a1201050f101208400b0f090d0809100806090c04030302030f0705100f1a0f0109090f090b010803 54
    0x400a049006a401441d100303030305481070040440e1021400c0503030804519048001c282014079050000c20105250b144046408020081005007000d0b4041d510003968071142803402c0d10b5040700d001142c94035200301403002510b15441c40681007154215510480000204900740f00c4004101d0103264448000080c0e911181032140110f039003001c16400a109040d80c0c46d00c2420400945a80881101c00402c440e80000e90f0000078000101d0b96802c0c200000754984003541910b0381070301c0e1000064290801c8030304100000031060030700c1c011107000480b1084940c0c208040c0c0d00410021002d80c140c06c1c1e2b102d050821000e0704039a00d85541c40c1e401560303a1a6055242003403004c1c0b0410650080c050004000c04100030301c00b0a40002c1942d981c4503a1034002551070f1050f16243e0f08201c0c04c14011601c1a043c410550252085d98020800500031005040b05400920003004402d100c80c96406021450044060000100e550802d205400108101041c5420707590341d12519a4000d80c0a0310154201003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 846913839 1250 846912589 846912623
    0x120c050904060e010602030f031f081e010507140904091514062707090b0d020a020c15040605070f080c0d1e0912050f06090705040c0c0f060b1309 64
    0x4424400a050340c140d80f074400d5810100e000c0d649221304081000f02203804400214803458041842040074000200f1724a000d60f034034140313a51000210300030500580c4034450289040414031a040c032400325a030f9030f00580d810024840d14158002080d5a8005407101d880c0f0010401e001c2c14a404000c0d08500050203c1800c0c41c1c00c03090002c050080d92190700b1070014482d01a01865010610420f03012144013691243d4006580c411410b50207560f0324140410a5070034500a41c0c06040c2c94040b6070240e03003000c043c0d5003c0100845c07468417044c042140500050000c58441d40c060311080d44102c2a07072484058035160401540c010044e031210a501c03403504c0c41030a56100000d1a15140c1a070000d40800d074403d5000b80104842d030281500c4225640200001c0c850100201c440c100d2044c41520071604280009a07240c400d9070041d00d000d141442d0241020038428802d030120990440f000740d842e03c0d01d40ea41c1401074186602c5203640400060452044981c135032184540d024440e0144170801076140e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 846915089 1250 846913839 846913841
    0x90406230117040b22080a09210605060f0d1115070c050105031512010e0f070f0b13080316020a05090618060123040f0e0702120a120c050904 62
    0x50020034108480800b608040001e0010090f80080d40b0120341803442ea03500c020b21404d0001a10b16107009031110081c0d07410301c24500000d12840003036a40c2d8500c0252204000f080030005040400d410b8403590b480c0a02151f1a0740c0519000f0200601c5d40350b00444100c0001c0744205103c074250b42941140500100900d0188209405040440340f446e003064180e80780c420700003500d032280d0341c1404000000500e0340c3e1f1080d000b4000c0001c0081040d0200c000c01c0841c00c0c02491144001d1007a44107440c0341c02601c0c2c1001074072900b00c0d1250450091214103050f210551a0442c60003030040410252002c80c0c4c400060000c0c00c3d4440494001ca07070310b40080e0040010010b42d9a01c4075000d10401d5040c402d55403680c1c209079481c118003004107800c035200e12004940d4200c10341850365061000480c04003640300c05034010012581d410030000c00c0e440c0ca41ca2021490a42a82c00d440541e0181c2c0c180b1300ca003002c0030081d10301c4500d00c0c10480f5402c2d00b5040948107070746a440c00f110000700001540d0303c0c86c0c601 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 846916339 1250 846915089 846915149
    0x13080105090105090d1103040302090406020705060a021602010c02360606070b2706161805090403082d070f0903121b05010903031407080402060a03090602090406 71
    0x20300700244000d04145641c103468200702906001003206000034204003d80c100704a50066501400c00031041c40c0605044009402841c02141c00d4003828021440c07110b014026900791110ba821340c4050306180360b00644480641810481e005240c031001c8900d032081e0882d0058406200c44500032080a03800701c40e035202da4000381110702c545814040400484c0d4001a90b5604c084025141d030f80d070801444603070f02d610071040c488414612600d4108000c1500c225078020307030b240309501c919034810748000011001c19213500809401000704030009000c24071504140350082240e0303001910208502400405260001c03402c1c0b1401a2010140002c46038054007810b8403a05902d06410740c68290b9030780c085c511a445095908211146000044810110402c9544543d05c000200f10540783d51070b000d405480302d0350340c0c0c0c4c601a00c0780e400a90924010f825261190f41d00800c03840c070f0100300000980040072440b03030075540513501b44410072554645200d480058109448804811241c1c0005000020305c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 846917589 1250 846916339 846916351
    0x1527111f0207180f110406020114092806060834050f0a0b03162a06051e04030905040f200702040b0312041d070f180b13080105 56
    0x20282501040d240c1d000c036150702640c001201c007003080f2a40c40e00c0319010703007903400503960850310b010b0301940d21032400d000070012154035400078048003000c40794000b0401011224224190040040c84003c4d10003a620b1490b1500d41d1546011380a10781e88548041b00e180342c10440c05903000d12030041c0b140580340c1c60740d40f056204110b00e0311100c242c106000c003500d01900c42c450040c02200c000440c036580d0380340e0b448044d1003500c060a48a1815501844500d4520900c43c800318175980b07000602e03001960210804c4182402509080c9a010f9940100070003008061113801040d1100b2040d075100308100c585d0080e40a6a42c0003000c4e070500007000200d8a000e010b01c0c1000b4908051102041c014400c10345080820410389903e40c03085001150162041411b40c81e854000c502200b404a0341c040c0c003800035078078148140070301c40e244844850340d41c80e002c5c0d44010210307800d02481c0750f42c00d00c10302091013110340240320b1580b4030b46d40314843c02c6560004c2c2c040b95003d07050712505104c011024422154004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 846918839 1250 846917589 846917629
    0x3020102010b04230606091009090c02070b0a050a090b070809090702060603191a0108031926090a06050928030e09040c1208070b0f0103152711 63
    0x2982074540d01d642c2004d0109a50589440200003c10694078403040e20444a800780c002c180d10940000010008402c0303000780c061031460082d0801603d0301c0046c3c204241d40c40c03c1c1c0054900908904256215040401c1c081c040000012012800184020103411307103620407c0c0180e01c8042d030200f002590140207100ca401c56110ba020810346660004800c2c100e041603000300080c0440605002c01c01c0f1018045030068600d00500004403544004018031518003081b600b0540702e0003045080701c42114820b040030030744084402e5210810842040c140d086180407088072401c101668410b41031f01c6049501a400d0340040310481c90011441450081c440c0c0001c1081d0080364156034080d01da48681c00c005409401c66100150800000c405440050500307041c031215007280c50318008041341d02504044452030501004039000034464082181644c1c0d0000260700c4220f90500ba0300001e043c41d1007110701544103400c0140d00b0800d0041201c40c4ac501600203140501916020321901301010700c1c034000d02d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 846920089 1250 846918839 846918851
    0xa0c0305250603110f0a020607090b0f0405041a090106050901120203011a03040212060903031006021b0609011b110f09010b07080304140d02011a0a03051e03070f060603020102010b04 80
    0x10811007040d400603910141000110303901e4401541c00e00303001c1c0d042d030450003010016941c025a500001c0042c401c28290303441d440540e48410900c6841d00840c411000624802d1200380054a020740101c60180300500b40d00400004005c001070100200780d02070004210b0000d0245c1d1556480360a2a807600040c0f541945507502d00020320300c1c6514072034030b428070340d0902101241c00c56980000e0680001c00d03004c12250345003041000b141d260b60040d2078070782c1003103081000000d1040c0080317240b80075480c1010050054111030014042136500c2050454104010094050280d402d034030900c020f040e0003484c0c801c003200354050500c50140c8014020f00c1c407800c2028010005854100d00f16034000c2d074000022600ca807070368600460903544030301143c1c2041c080c510f0441003181e41540800399851501b120180c4451021090207915041d44c08068026000031810700440164041c8030220700481e0f50849107000f001e5100c151480e80ca6060441e03180da115181082990b13424001c050103400120340411803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 846921339 1250 846920089 846920143
    0x7020904020f04021303060507020c01080105090f09120f070510050426160f060f15122604060206070f090e061f030902010908030f070b15030a0c0305 66
    0x1421000380024401d40e85481c07078400030380f1180c0607110360402e1012500d034525100d18100000d420200c50b4540140319200f0541070a610654440d07040b12005444000c0c961039081091411042c01049000c052240440f1070b590354884800515811201914540e01c0d085503207042409e04005029031035080e401c0c00c1c24400418007920b405405101c3c2904901540700c041500d401306809486a40216018501215800d100180030303045650b5110354800c000c3c91742c01000520403244003144c00340409000c4d41040c840d12454524108d1040e00406181d2100380e680d41c21441000c000c1003982500d541c005c20100009a0100f1083d508a00c0c0750500c40001030600a002300200c406102e0b601d1804034401c049401915404045403540810001c0c5000e11644414041c003d007215840490000b100640300185490000c0180c034600e40c00c03c45054680080c84d219004a400050b15024101c0e050995031407490345c0800c48201d442c0e2080708414801469818050306140d1103000e032210581c40c441060407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 846922589 1250 846921339 846921349
    0x406081807080601033e0607020307030605090a030f11060402130906060b2d0a0c0512160c06050306030d080a0f0203041401181a070e090423030702 65
    0xd44000440032a0521a0020503200c0c60608207510100540c05040c0012082c403400c840c60710381e0502c000c1c007200c03800150006250301c2d1440d010f001107120b4064044c000080d1400300000d10340180010200c5038080e85a0305d84400300c0c0e0301607038500c045034800340d80c035010982c208100c81c4000ca05403c10200e4004c84800b040e072120310003040244100c46042000701c2c409081e502c1180c002c0c0c0c1040081100d0b0352039154400840c0d00520b6403803402c150195600d280c1e012290702d0011030807030200c0d02e6810301c40000c0080c2e85002c82c88404481900030103203a0901703d481034001e009001d404040301a001c0c0201e041c000c2070a070361a000b90041000403c204940c03900c0009604c814641c881ca8a0025565040007850040004c0780e003c0c3d0040d4000030601060211440580c1b00d442120b02c02000009a01e0100d10000402440010f14104040b02040110701c0c003011364503403002c07041c14809010314640c000102a110300b120110380a83c08150b800b2441d40c460201c0c10f40a152200007149451001e0b0000f031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 846923839 1250 846922589 846922591
    0x3110a0507150908010f090201090b040807091508061f060311030708150a17060a050415050a06050619110f070e0c070c18140103020603010504241e0803040608 70
    0x40702c1240c0044060080c07841843d40030028520100200150600365030000c018014044003a8002200201c01241e0020580215421920140000e0118501d4514200040c00809610024404c00c000002400f603905125003440343d041c06800c82c00035039000b01041c60124007908102c08062034060040b500c04941011070f500240682008046a6246914502e010b00d41651142e00050722120029000b0322402140718040300000540d561980c60095520072244200c8018080c10f0a003424032010b0036069000ca44c00605010011540d1070300c44001c90040d500c41c0e184018548070b070303007450710701c5981c4020406844520320700548503807440d00b90000d9940741c0c103018003d543c480003404286001c034200c044a45a80d84000107038fc68035503d001c0e141c207103880500c02e50056420a4403030b4244200c9242c106041e44d5004040c03500f035074244018000100300700c05040e50a203114583c3c0c400022515040a030080480c100000d25007482020182012a00c6620900b0141d0090105020551700a2122 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 846925089 1250 846923839 846923849
    0x503070332090a060e0a05070b0a05070f080403080711100201050103170c160602071d01051302220e1006020f06011a04030c08030a08130c0306110c0303090a03110a0507 74
    0x4440d00e03480340506141072840302d810041410345411461401d85401060b900e80f547c0c0240180d9014075640c080c41d1079144103400622000841c1007005c0302c00140e07080f5440041c4e41c02101410f05141d00d0350b0341c44085a220003030075910440c58811005161500c0c03445070701c91068500c0244a154956560081003001c18070f0921241e80d004a909031184008103c0e4a082040d001c52000c0710f296a140041e4984c070060080d40307641042c05000ea440340d040515a54100d0324094411039486001400000085d0004c801120003c1412800c00e400c0106140c600340141550803040c5066090000100e600005243e02100c19134100d0340180b40c0310000495240c0c1128002a81c00b00143c0100400136424441d07074100420f00f0a01038400b0407061030000151102c00030f240c5802d100303501c0d1340713101034031000250400030143e409083c02400007030083d07007090082c0308441c40391b00d0401f0700c200004c90554004452215140e804481c0080500d0792180443c18018206005880450203c5d200c03140c440020b4019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 846926339 1250 846925089 846925181
    0x1d06070c0605092706120a0506040813050415090b010c0b01050d020301110d06031e0f030f11010f09050607110304090b0f040c030509070e070f0c1502030705030703 72
    0x8150960380b5004000c04004c50086044422080c1040d525031082800b42c40190041c0c0c1c50b0012404800400200c844d40c0c0c40e0010000d01e604e5507070b036551b190241d2200d02d000034204030300c800000b008d80b1030740a104d200d0f0021202d040d40103810404884200d40844008034104042412208045000c9018047c190369052711800300d00005c5002081c054640d0007510552014000788a000450380c03948600182d900ca00420903102c3c0202455000c010701105d0060905075030241c5144c00a0300031405c480444406080405554950300201400c440a0003010407008d621031030742c1c608121080c00819030048960400d6641c1c20000c07607489640b0b000b10300074500603560f1a40c4230607240d0382d47c02c01c100060500030018042c1880140008000e0711050780c5003002d03846521404140c0c0c0300030503000d511401c2c480d5902040d90821110803591100b0309082a40c0c043c01800c9200c11183c00c0340002c1d0b00c2150103884250390303403d1181c801000c4922140c0e5118002c2c04c0e09114004081c820700784054008105c0c80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 846927589 1250 846926339 846926347
    0x91b010e030a05060f0114060403080a0e010c121d1f08040305070f0f0b070c350307030605190302060a0e011214151c02100c0506071d06070c0605 64
    0x700340382c00e50024001d08244030711002c01c89040380d80c4008070b0507141a40e214550a100020501c01c00703000e075010062010310140410b540c007910900070390114000c149052682e003c840e0b00e610000841e00d42c08080040c0382c0816071201d0100c2c0708030f105d400710320039125100c000111801c032001743d140c0c03004000d04001c000008101454270070780541321007e800c02040340411002d40383c00f8501176001241200c110007808001010b0300d000b44200041c10b0333000000b040040340b5070b085c4c01c4030381550a288200c6426800500050448a41001c0c51041c13802e900c001400c141060104100360900091100070008106418001030b00c440050721002d80c200e0800d2005000c0500041c0c80743c2254a41c00c0ca0f03120f1030080450010302c24108058045d02c4403050702d01104607803d0074001d0355814107a69001103485003480000600740b12400341940c1d071051500b10005805642e55905142e010b4070320a0000c0e29424888404a004000703031000d80e0340484040c0d01e44045da9581d44000d00c100e210ba013080c404042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 846928839 1250 846927589 846927617
    0xf050a060302130801110a03050109090b060906271510120b06070f0f0c0f0f150203070c030f05150f0a0b030304090f0504060608030903060412050702040501060512091b01 75
    0x10700700c03005420102d0003845032101b405502c220540080c42d242c0c2c00a0304100000454140d28490f80c10310340d40010b8098070550300d0b1014041c016801030485070304000841c2080640407050740c0101c0385000c1c01c050900780e50a145c007540e851a0441c82441e482468030241c3c1500d0180c205040310040014044049136890110b030028616000e03004001c0c154401e101c1c19442006503040b00220014416206003082a0712000204c1c01c0d1015406001e03411800c560043c401210903038804800e00310544103e914110311343d511004155519401218000701160360142004801d1200142e91456042402d80e81d26160007081c02c07080000c0c5c140c8a203240c3d11310000761151428022500544a4041c0c18071540000103404001440100d806a8400b8902900402c05640100403240a2103005000b84175540b102d407520b500c1c482c01d51180000b4050100000001a1590b0291038000c00168a031aa11020120381010880c1c0e001807015501d6009003c004020b0202d0307101d82c440c60741d401e10b007000c91715001c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 846930089 1250 846928839 846928867
    0x101a060d050627040609110a0303020109060501090c050a08040503161a07210e070305010c020706140a0807080c041d070e01320c060c090a090e0303040204052203080a060f050a060302 80
    0x390540f2340000509a001c0203050701500586103031071054104020581e82c4000d000229001c00001c40001407041217044110391003a404190401e0141040da868140ca0140003200d90101d246c00b12000d41c1c10010f000c00701ca41102d200d40d0301c080c150038650001c0300021401c440ca440251414081260754041006042c1010009000559844002003041084040001c0d540f4141c621031040010710003066800210003450a40c3d03084403050300c03030581546840e0410740341e00724002c04580f80090244800a1000d201c0c62801c0030103601881d00310301300d04044200402203c00784240300e0501c0100c80900f900704104015000a68001c05010302d2095940080404148a04042500340e803241d00300b88003440c8900c90041140d076604940038030601e5542c50411040d1100d16100d440c0903082400020301605044d001684d002d18249001b03d840c4000344410b9140211065096000032581800c1180c002d60303900c03412001d84030445209601610309000203850140d1401494201900410705a01d4049a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 846931339 1250 846930089 846930113
    0x1021c0908090405070203180105070807030e0d15061a030f0411040e011a09091c1b08070c17030c031b03130303050d140603101a060d050627040609 65
    0x1c003d100f03101c80d00b4003e100075501d421003070416443d00401d150030080356010300125201154001070503030a10785191004d594102c00b440d007030f54001e6000d4801c1c6000455050882d000460760b414001000ca040070151918012595070303402c400c07003040051003401e400c4100e60036400341d40f000803060710410b0030010074050042e126400e0713565802c1c141c001032a09600b41900980040c10307200782001383d5a030348540c3d646000500000001d065803041c42203086202d084401c20307014101140c08040b000d9591106d00503800084159100092508240800b82c1c7d0300308401c086400c0b0700020b41c1400c841c64801510b0f031141600e8803e211115110502001000f8010340e8a030880c0c1c0000001400e40c0d038200602035a0080810086203442d011501d000c000c046901540900c401800a0110900a4141c03c00400d010800c03451304641e0880f451845545401c01001c20020300303000843c99051980501010b2030301e1801c00d201848403450035840001c0004e00955106030030032b85c0820070700310b03c1c204035101c104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 846932589 1250 846931339 846931357
    0x2d0f040204030c08060606031003060b03190602030f0106030e12030414070b03070e0d0b132406060306050f09190209100c03110615040c030608070801150801021c0908 73
    0xc0041000400d122050100108a034030306400d480c041c4c0d44450802c03c06100840d4618480d103081074082c008201194892480000d000d0101c8038900f49140703d48241c08110030301101c040e50000100030142c11200c0d001c0b0b00400c01c508051041c80a004078250f2143c1c00da081d608030910010000809000d21050000d0b504e440301400d65060b20f88036545269994030807142c000100701d125083c074109040007400b050890303800907041c000766110000420014502c44005075501001d104500d8640c1d55144c03120302d0402c9081c000001c10518014020701a1a5154041407050400440404094840110640d880360340410801d29039201c40562341e00030300501e1102a0400b20602d11090580d402000e200103082c02a21003840c0500444402651004112841074401028181c224502c1c1010f070403c2e4607042c2603040c0400c2d21798542010b249450031a61186105039102c207508081c1031a40300f20000581041c40081d4035003280c00d96035809000c11240b2900070355541e01c10a10074000300034192541c001c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 846933839 1250 846932589 846932591
    0x24040b0604031a01232106010f14040510060e030304031401021305061c0203070c02042a090602031813050a05060f04020406021015030f0b010806062d0f04 68
    0x64480c10841d00742c41001d420b003da40b45001d030022507110b01003214440034a40da2282c65800340c049006000180f003a010084907005460011001c103d00184440c50281c50000b81c1003041503c0c090250410ba0b4400c2c203410700440c81c210620041c140600f51344000d0341d6050402d0410994100b012034918440da60000d00032848801050071109010740040035055441030100100c10340340d00421603a0f100e0321010b030100c02079101d0145000720703980e00034582c049402d04010346448440e40100e01070341d03061030900d11400c0ca6a621356049240d1807040512500c01c9180402d81c03a4288a40a5030701d02c10044140902440c1c02c034a28403942c0c07520001030b51080d0740c50041c00941040c0c01e68001a020907900a8454015020301900300d00b854400d6508940b00d03507008000080f25070090781c0051110001d0100700c04288000031011841c5038450320091481425061b140b5803410b400c036030074013101500152203682114071a441128011700860600110441005214209203002900000010b1925a001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 846935089 1250 846933839 846933847
    0x40b0705010b01121407030b120709020d11190c05010f0c0c030f14040501050d18050d0905220c1701080d0207120803040b040302010f140a0b0924040b06 67
    0x1106400c4001000001c1c3c9136102d525824140250a03200300d201c24036400f200100019600d14800d8214203000c2801620a40805482e950018100400ca82105080396000603c1401d074201511503148480745030740109080c1540e1244900c03c0316142c603158401c02030710b040c1e2807090110a61188500e8103010508000300c0402040162805444800503004246202000700b0fa4501a80480340341c0e00c0c104083d07074685030400d401903503103070460006110050f90b030b001701d0780300b41000041125101d80100003d100a0031100ca005042020940040e406002c074021007048a03000300d080040b84103079204010404005c00303c0700b250b94904070300c0580342244401d8000240100040380c2c08c0a0640c0c0b55095894454441040ca07a83d000306007401072140c40c0400c002000710f03140c95600d82c2c10620034400032480c000244048801e5440e14894001d81008950074017408015921420400c20420f1382d0140707007803400c924140c000c2c401001c0b180550031030182000ca0541d0b0780f07034821520006d008100c540c40d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 846936339 1250 846935089 846935093
    0x90c0f030f19060605030c0f130e0613060302030c150c0a1b09050c040b1c140f01080d020c04051017030a021207121b1e060501050d03170408040b07 65
    0x3a0003000d603242c540090181c1c1070b00980708000d008400c1515000e40725246035450380315030101030743c0c403160401e908818144244c034100c80c0c4039030b101002040088160907050078100100f05a5105d1420903000051801d4020001078a01241d0480c00c0f050445601c0f040c0010050344034014031034604140858080c00700e40d281005200040740106032070842007050411346034880e03802250b205485103141c80d0f90900c0100801c500800003407080c48c1140351b1445040d4140041c0c8416146200b142c40d201c18044410009843d01c0f2001c424010403021000703102d120402e0001070344580141000600850f1110002402c03000c602c08040b00030190142c5402c40e03861402d40e032548a030001489080103004100005101e03164650569000d42d8004c0200700513007131413150075901e6126010f03000c04818034046000e004500c094901c41c502c445160510340305c298072490030004442050700807511031380c00c0d1a614004030f940500721f0340400f0850142c000458842e410b1001c1940078580c0300503c0741c1c5e80017580703000f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 846937589 1250 846936339 846936361
    0x109030501021c0b030c01090b03071701080d180e04112101020715111204030201180f03030609020a0e09090304090e0a0302060714071b0504150e100305060402090c0f03 74
    0x241150070501d08004030003a004c00c060f29210703507101e118006402c2d10800c1c8000580346000b0b54000e941410000c03002154104070000e030386801d9015540a820524050000681195100070181003d242c00700c152070904044008000002e0000b030311501d440c0780c000344562500e0300c00481000d0f22310340258280e418548401e02075440710001700c612003011a00c0117260341c900e010300440e140b01049498141031010101640c1c4000081040d011503403680b03683e80880709201c10680a190144040c036020b040e05003009070988800742d10030342c0c1240c810085410f1003070340900329100c8100c1c11103020400783c403a00407080c0743d80070b590002a5842d142c1401d03401c0510002983d00003041c443c0c0c082e1800d40d99001c1d816138000d082c18036101d04503d010060200041d540d41603c0d54548620400400581c7d158004642103c0c20340c140e4181c0c00701d00280c02d01070f01d240700002ea40d1210f060610226450301b903546441c0c07140700162009005800c0c250218104180035800d84030190007504009441b440e112049030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 846938839 1250 846937589 846937627
    0x5070c0320010e0f06030610020c15091f08011206110a0503043807021c0801060e0307030f0311120705010902100f170606040f080c040606210b010903050102 69
    0x2d020400750305110300f060038134098010803818000d000c24210303650701003400900012180f0040c214040d061004065681c2c070510042205420300c0219107a07020241440b0f0090b510304a02d003400c003500c4c0d000d000030b02d0b80101070f141900c2041d1140d071300d94092440c151010340043c00c0c0c8650702c600045690501c407540840918070543c01240c0c0c5010703080121000080c5411490a065200e40701c1001d001c004081c104240c3d0f03080155481140c204c40d15070552280c015009040200004080c100100201c5900180c0100010405c41c05042c4091840d520700c41010692130008081c807040310b560305038120003030200030103105440e94803a9039040c051903c02e0081103006d408a1090308140f50804841c1e209080d00707843d114054890318400c2c660700d080e08440794802800c7c1580024100008250840f520741010000c2081d00000c000504100f01040185c400c55000182086a1a8504802515440c82d69803590340a60380025503c02964012034441006401c042c242e9800000e82920480b070345c900d20 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 846940089 1250 846938839 846938903
    0x10c02010b0a080c040b06040803160c06020d120c03020f03070c020928111b010b03060c2704090f12021209300d020a0c061e05070c03 59
    0xc016900200c0d003041031030b800c0340c000c80d00079a00900702c0e2020303810943d00c81c4819100082025003000e0b95060581d185d507111054040044121008000c2040100009400a41054005003d407035603401c200601001254451619450f01d89090740e01403402541141c80340e07400e006200b40e41c0c2c40c01640c094005001034a00300e0003800003400050300050010214441c0160781c410241c0a0050344420b50003034420001c026090f508100026030404100b8000c24000c860240d0010400c2c0c4491003c150401c0d00c014403c03501c4c4001040310101a0312043c40500450b059015505417000e502c1c00458014558240010600c03031002c002d04080c04041c0d4500501c20510741d085911519480ae020b2000c2d01600c0010758001014022100c00d142c20b0104c0004c80c0300c00c1e81c155000b448043e0380d5080c5840c29084009025070803854044d41485441d80c4142c01601c5941030161441030300d5a00821071080300e150290130400c01142201c100708803014400300564000091600c654072034460321008525100352 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 846941339 1250 846940089 846940091
    0xd02030c0403020a0e01060f08060a1203020138060306061605150a060905071d0d0f080f07030206010b091c050c1009152c0d050105070f0314040b0117030d020c010c0201 74
    0xf040d423092194110600c203103000780c410540e4a140c402a04c1040003462411825075403100c511820f41060300004a402400901c6d500740056442c8540070f000e40c403000407003805040104200725041d2540001c4030b07410144030303103522001a0281042c5050103101c40d522440c9a48100070301480714555000031003943c0407c2d104001da03440350300342990002c0c10300c000c40102c0e02c0f4031440c8820314900a019507122501401501941e00032075641c91189620031403800d120001c0100390801415810004103015011055100d860708562030001903611041ea450a50f8907544c14051108009042c40820b00034000038200031040c0f141d40b08080d1490905000b556240241010800f44003849298000c3c0314002d191803550340d952400c00c07584941241a600703a504510300d1442000003d40074071441d8844c000990300c45004104404000f070035075420016414942c04a04140008500e8034034080c0d0442c0c080c0c14029400c01d80c4982100c0c15070182e1486101d51910204520083d00d40640124108650740d40c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 846942446 1107 846941339 846941357
    0xd0b010e150a0203161235040c03050f1c020c01080c090a030c090203040501051003051b150a09030209010b1e0a03060902030a0b010e04050603030d02030c0403020a0e0106 75
    0x4480c0c0c4ca803a511001342c50b6034001f461102d400303480400d0030b800041000d25040340c03019000c4401c4080c0542001b140c1080628240c910045a000085d1051030044014950711065001d0952008008000210035031b00d101290410102d00141c48001c0951200d02811400350014103409800000150020000c02d00032603e070b030000e09032110090707a2072802c1e24082e801d591000c0d100000305c504040047c0005200868904ea00700c0a0070030310021103040c0000143e00c0034050b9107544003c4800035035100d0f66a40004480107490080e0b603a5000f03640e07a0101c011483c03091080c1411319040c2c0048a40c10b0840070f00040c10310ba11145000304003a500c1300b00d540102e900541d00180c50325070381c403419407465030050380c3d1242544080b01d040126240c00700200380c99105600003800e00560010000e84840504001d880155030040e0100d1002621000c0c0054026401e00406d000705d16009 = true := by decide +kernel

theorem cover : BRFrame.Cov 846762589 846942446 := by
  have h0 := BRFrame.cov_init 846762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 846762589 ≤ n) (h2 : n < 846942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
