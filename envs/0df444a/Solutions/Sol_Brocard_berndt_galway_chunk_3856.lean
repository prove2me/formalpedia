-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3856
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:52:51.865797+00:00
-- url     : https://prove2.me/submissions/ba9efdf3-39a1-429f-8168-275b40a2cc07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 693345323 ≤ n < 693525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 693346573 1250 693345323 693345347
    0x904080910050d020d1b1d0f040e01060602030a03060e0103080316111b0a0608091b01120213030b0601050f160c080316060c0e0303040e06190306020306040c0e01120c 73
    0x5002c0d5121540c195a0402a21410700402c00103006c0f10200c010291003592040468500311006101c80b800c0c1d4001d0200c04225420340035041601c03000d800d07031440401d01c074910040440740e02441c0c4400d100100181510603561001c5c02140c091001031002c98955002c80c4d40200b80f500301d0715820076543c5426507803043c4000301240d1038050b0070808002401d40d40f01510703c80c00304a965413174a5858500940b030302c040a6502d07003166405a900000c10309114014004929014103042881c501c5607520002aa800a43c40040d00c40040f4002c100b0441c2e0060400e422141c242043c0d13042c2180007219003480c0c0641c80401c02c0c9410034200344810b010301d03941d034130300502008030a880c1d0307440380b42c80c608100e08840c4400300c46191400107481c2c0c0c0271340300342e008041244000340914070b040d01d4119042420880500b00d1a8840c03c11a40000d1801c0c4111005d402984180c4001d42c9920340304003080200e03500b00c02c51506100c10b56440050f160380c00040955041e000c00c4d40000c84540d0140c0849001c0c034001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 693347823 1250 693346573 693346597
    0x3150a08070b0913091a060111030f2106090f0a140403020c03070807050604170f0601170105010e0106051210030b070e030c0a032102101107020f090408091005 70
    0x1c085004400d4200409400707005498807004108062800d0044803014a000340000601011007541d00b03a041c1401a0070410525103040c0c00f00908803007506513482041d403240c12044c00141c5500280d004240e809203038281c0c009041e0b061508a01041110100074000b140501000001451038143c44c0d101c0000c803c4081c140001c14901894041c2d511624104000c0c804d100700c0000080110300000c04006440d4060401401d0900d000e06840c040b012009014855000f4454088102d10040002c0360003443d81001c42c02c0700250300503c50b42110410303008010310000b018018003e581c2c1020490b000d01403444504030199a901000101d04034064100403c2d40441809119141da0721007011155840c0031000d541e0f5810141040042c1042d00780b2006152007403224180d03101007050321007185032541c14015100c4c04850807108038111042202305414114000c104001035082049440c0120402954170a80034200303034035103003000e000780101e2902c0760140781400e81c95a031040d02902c441202003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 693349073 1250 693347823 693347833
    0x1020a0e0118080d0518100203040e0c0a0801060c210e03070e0112020d24060906171b01120e0a02040b0102060f0f060f09090c0a060c03020303150a08 66
    0x590401400848030303400c4540020401c000307890340344400c02e0120044550040081c25028031804007503d480e001020700704c14004402c1e480b180c003502e8550b4500e034803070030035405903650342d0908020300e4501034064400214114180104034496400a50b80c505507146030401080c2c000040c0340c40c000350482081c40032107101400d50f100c42a50340080302c03402c4924003101942c0c03e064450600110382d500034462409406040300011015082407410101003c0c01403141a400c40c004820f404207078441c0c5040400a01c3da82c190070081ba01c058070420014125100d0886075031002e070310b09030b5501e00c204a20884041c0c0344201a00f1540e02a400c4a1034454002d5020b011640111a481d5211004004143c0c0180c0c208549442d1541c8081002c51003000039020070b4442e5112041c811868010082200d034001d00300d03030780a03402079039456030483c1713f10b078540018a40c460503941070002c1c1803075940c420f00c18400c8071102440000d4000c400e682d40301a008c3c842c0c0c104880204009411420164461031960081c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 693350323 1250 693349073 693349087
    0x1020a0210060501230310051c02010e1f110f0f1605010e011e171f0f05130e010f090c0812030112030c03031509060612020a080f040f050102 62
    0x1c90214144901050204440399890340150780500c21124081010703210b041c41150004800b6024641150710314440310325054451001c280d44110f8200840740c22000402c5050456900c0351071040e64100039240c14505500041041d000741c4504800d213000c2c4050420b200b240d9640070400c80d0b444004440403075200701040d601194440811600e407807030b54046048086250350042240d403a134001c06958404400c3c84499a02642d580c802d0900420411800d20400c00326412031b007110700403400b01020b004021080032032031035a81002d84c0049011103010b082041b540d0307544055a41082294140460803243c08803011380107111803607000130128034014100c400d1110001c001020b8800c500103e40c03141e01181d42060a90009124503518400c03c1d41400c00064490001c06486920900f030204021913a6562442c0c809425040400b02c203a8810f010404541c1c0142d4102c038490a456046142000c4c1a41c000c0411100502c0829070206100c045020084031028100119421800854071200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 693351573 1250 693350323 693350327
    0x109020a171507200c09060111010905030f040e09011406011d090109021213051c18170d030207110d1e0602090a150e1309050613050118110d0c0801020a 67
    0x248400b103203400f003840381d40013840c9503100041000720820000c1c40b06410f540c40e140115016400203101004554903401c068000450403c058040006500c50343c1c0d40321820f10001c2c035a90003005041030110f0703042c040785d00e400e003c02c0405103810000a01e00020390358807160000c0c803031111000c040c0d50400203c000001d48010b4503806451118000300c00442c00b41c961f0b900040078081e9165000d01710350448106104e40104403a12500000e4240c241000c1506c00e03800e00c000641d503194043c541107480100302807101c880604c1220a0400503040c00c40c20407181c2e8030b820010042c0103c100e07014140134103844061101705103119207520b05800a1030004a02454040040d4020540450003400361400200703407480401103003410003015517240448030014504001d410203036114003145c0266600348500c04a001031007018840c100100ca01032287c2103a107072440c2142c21082c04100701000842c000000110f00e101d02103000da2044401401218150070f001080741d010b58007035102c40d840050030f004059 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 693352823 1250 693351573 693351587
    0x301b131202030105070f05190e1e09090102130e040309050916031107031e050903010f232701110a030e0607050c030a0315032f030109020a171507 64
    0x2074800d50080c052620307050000c0c2d0703886040c5c43e801c802042040c07211200004042c0f040070f5840b011071510a2030092030030007207480d9141503220341c1c4001500e0784084070f95091420000f600181024000c500d0b200748116503400b5820b41e8083c910100c0e02d220081005d1510408884020740030081071508039083c10070104034225410381d9000c2c0400d09044010507074401c404152007240e50161540040600010340e11842c03480c401c003442d41803010502c140031039600c0900c102060180c4066000401c0d00d000c124000d414246002c041c102c0e85c10324010460302940d40d02e0034056240080d0100d0380d0044040b002d907805081158804c8802d43d03000302d40440040da15420420840c0402e006075041a1100c01e8211220310410104410941c0104003c19004d4420b40c421036216845103001200a030b120b0362440304070045a540044070034483d0121040804204c0c0c51244106800c40c020048d103d081d03070100c1c40a014030702c034503242c880310341c01c0382072121505002c4a8030809003042c0c0d42c5101d02c1e046030060290 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 693354073 1250 693352823 693352859
    0x110406030204060f15050910030203073b060301080d0809030f0f09040c0309210c02030d051e07030c020d060b030604141006050a0b030712020a05301b13 67
    0x701c0c5415a40b10518041c8044803261a005040d8208d000905d1a00350040d51002e0b08000c10800720b055001511030b28030090351314030402d084e4403c1d419100c0d0340c5081400083c00201521941c0100010000c2160008180c0c6444c1c0090800c0101e030b55841c7c100c5070650103440041700d146070b400905080042d00b408020b111b40c1b0400c4a082003c00c80c80001101140d40203000141861b600b15482008403a1000402500000c41d00d403050742422103a002c242060b600d06d901901160001c1004d02d83d240264102c3c031404243c07448110b0500d00e10382c60081c420740030520060701a25803403000c5070038040c0580155600c403101400b154801e040514100d008001036503100d14076809a444230018400c198080c0800301c403002880612106d0522401c8440380d400508641c0c00d00407520b0441504040a0001c5c162a0302d803921002d41382c10304419035491200110568440010804807015000300d0021039581c0c020392000c2526683c0ea83c4203001c8140d42c4580e41009100f9441c6100001d2105030b884009036070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 693355323 1250 693354073 693354089
    0x110601084603171302060d0b040f02070209220303020a090b19081003080306130209090103030903171903110d151a0703090312022b021c02030403110406030204060f 72
    0x3c0409071251000782100e0a44030500c081d0141d004800140c64088050008050049030024100e0300c0d803070000d0125441e00300600d24040d00400d07014298a0200210795000c4d408400d004012044485ea0b1400c00908407001002e142c0d0208000010620070b841d034000ad415003058617076949000c04510341c01020f940110000040c801800115056600088141229807201807030382151102c0d07042040c0c8414541110484607824001d09926a9456161900850203038031404083c03070a40c10201c680181c203104549000c079003045110780d581c4031001c02102c02c810b280b5000075039841c04075580d1600c0c810740d410141e807181001d411841007031a120804080703609940c07481030b15500d85a4410b8440c010081d001d4003080e8002e9042000ca02d00125101c603014181c8141c419000104490101800b1030984e0b44611198811025003030b50b804103c900034401d907458060b045405128002503603407140d800024502e25503800c0800c815151a00800003541d07004105109007030300c55402118652651180a01c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 693356573 1250 693355323 693355337
    0x30c0c022e0509011205060f06042306120708280f0605031903050304030e0d21082403010e01020412031e0c060506120f01020901110601084603 63
    0x803090b00075000c0b02c0e180300068490212401d550072202e0001c0800900494000301c007014080040c0e1780b060000d00150044039034000d002c008802c070740306e946206c2003041c9000d51420040c04001080014201c2d074440c50a24201890380d42d0348005064240032904500380741c0c1c40c002c841600001e015000804482000c034030401a89544004160f03455018401c407207a1481a400f8000109104100840d8454003d04001680c1a10000415005d284024042c4d4081c0c0e50036542107200c0301d8072500c0071566101454600c11074200b4480c06411082042c4c1408107401824500d10040c1e01e00b9000f200c84031005070021500c0729038801d4204500200400124000b0303404400d4480802202280a04aa40341d40d460782002c4906e56500780080c40b0280485520440c42c065610f00c1e95010003190031942040380000d61a5005000098595450465200d819400c82c0300180183e5600244080c1514401103400f070500c60305103000d00c90440040e8041d604009401c41902c0140010019901494400e42e5009 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 693357823 1250 693356573 693356659
    0x1d060f0d030806010216030f06200f0310050d020f04020a020f070f0f06051207080a0f02070c05041104032109030b0906010807090e0a020f0301020d02070308060901060309050a03030c0c02 82
    0xf100546c0e03408010a403000300401c400208601d42e20100030281d10380c81212920ba0204a08040c40c2c004400304c42c21114004100071a100d0f0030114030009010a032000ca807400304079400030b0b65007020742c07083c280a0ba601045002640e4420000081101c41a80607a103000c0c0d207485120111000c1d070b00421014185001c030000f17459104a0840d000005010b00034003140d2070703000c011a035901016080141254a40c80700c80d0151210788002c2481a2043c12004c0c50140b40409101c01c2d2030703000c1900c80c0d01b42d0003400300b0130114cc48650702c0b03a08045045c481c0801580104010b0340e41d80082d41002e083c0000f01400c1100d00c16000035214141c0f000300c42110000d59680494000f0303554000c0944074181c10070450030006040c81140c250010a000307001508080406c01204126007040700150300286032801440614202404054090710540c90240a10b00302038030344503070b1264900c1c4014109651041203600c4c041c4520589045681c0c010b1401050003444032001500106074400f203202e00100300082 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 693359073 1250 693357823 693357853
    0x50a0503340e070807030c050414090c04030c081e1c051303060c0918050403050412080706050420010f0e06070311030403060204080f06011d060f0d0308060102 70
    0x10721149805444900c5945110342011841041201c0d084104081004004122152400070703031803043c203440d500c01c240b601d88884014161044000d202007071001c200001c0c03103a900400d1001643c00419900d00d441030b250754224160074442c1d0f60010b00083c2001101244201003c40c030480c140c0314211030304000f000d500150545071038141141c00c010708107410304a402580103001403e0502c0d5420818000710b0390329103c00c02518011103c0900007115000d0600106604400d00c080804122a0800180c5010303500940144614000e00c0742010740003000e00d08001c40360044504041e03201600b030100341030900c1c00d8544040c8522041082d4400c804400340b081d4401d6680101c5208d442d0f45140405000000f803044c42e610011051302000b40c01c1c429050719400400040c0015441544016521b40c503014100d41001031100c0482626080000100054807500304845d0284181d001241c80586a54000071602c052101d042a040900d0030601c609068004107001e115040a80a540a02c841320b810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 693360323 1250 693359073 693359083
    0x90506010f05090a110c0601090e070b0f0307620403030f0204051f020607050313120e03010c03061403030c060a0c020a0803191128200106050a0503 65
    0x5125000395011001030300c1c1c404203810181d0a170100c06001d45c83d0403120036404e03050400c01d82181002640328030a010503074104203c0d40000308181890a1b04042800041b955140b1028294604008541407880703821008203042100038880d42d540100d807031802203588200d5050061510218844c20070000c40d01002d403110508001c48013403581003941c3c2d030f10f69080d8000d20b004020001002c1e400d01002c10140c0700d2000d50460f50040388114001303491082c10013850b01d400107011074200b040501c2070100c01c60131400a000b089901200010b0315510b80c3c4000c607200d000d40d550760b07139041d800d004000040f950140d00440a4404580302241c0e151001c0040c1a560311400303c5815507980220001004980c81f0303070021911000501c141c0300003d015031034114064100743e80c0b410f04030307114010030321803207a140c800d0b030910200b25a005410040401d00c0300b40700420603085180940f088502541c030a0b44541141d20700b049041565641300254201c01c06d00800050241c0303406032070f880b2000320b0a4900062 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 693361573 1250 693360323 693360329
    0x20117010e07081e040213112703151302011416050d02010c0228050f06240d03050a121517031201030807080f030a02070515060303190c02040f090506010f 68
    0x1c107030030141d140e95091242d01c01e10f00e603d01089230f0303032810200361102c284401080c1907084880418007804c80f0a1480703400703240182c2001e02c640d000d00c1070310080404590385907902c80c000c00c082444892190006a44094452407a04815100010001c000e800b042041d600940d0042040354108802c440050f0300b2541007044200250b484003007141044510f44002001a200c9500c00ca402d07071030340e552070328901072040c8200c3d401500000208202018006102c28a02201c900019590300310400841c0312180c1140d809020041e0002c0e41021060140b214208008042a01000901e81040a42c252084076005100c0110340d42907010b8100e81000003541e9207081000c0103011036900e10740d10f510381c3c0c0d4803522080b10407401c107015544900d2002c5024522480040801503a503481904d4601d080070814051141d0b80c4000c6420311050f0384002066481502d20140c001c1800d00c5410001e070b84800c1c0b03003400203602c241882141c0705400540c0e00105002403207041152a1640c841400c2c0f002d0800300c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 693362823 1250 693361573 693361621
    0x10303020609061b0c120c151f090b0316060801061d0f010e03120403080d0509030a0806062104080705070807080307030c0f0f0615060f05070609020117010e0708 71
    0x800b4000203850380041510310703800d50840700c0740c0240701b040d02801c0d0080c2d0442ca00c0340e0042100e0702c034540e140b00c0300c180e4001086544081d1203041c6c91201c200304c0f5124000e0a042540d03800301079540e601c0030007601000700005005045006da95107030090080701d090044e100060786910112001204800075061040da000f002d965403851070100442d00010640d0310300b5410b1066408600115994500500155010701748066503113012907040015510040d042c00950752013005003103a50341d071058409800100881700035071b4600000c1c81080c270010710410825020506a02444100000d41c002855401e01c1a41a01d03011580d0303892042e1504d0300c6110310852134204001c1a00000e10603106041e4140c41380290190040b0180c455550170018070350b0403140159034903502c00c400780c000d040e8500148a940303440b020840c12814000c00c0c90240b02802012147c03a5405c000c1160b000c3e0701001040c6044d0002d41c20f042d81d4408072160300a0080c2c9440e8045440742c030200780032115104a5140c00c502d10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 693364073 1250 693362823 693362851
    0xf05150609011e051903091205071104050a06050a1d0106020c01020d080c12070c06320901060302090c070c0609031a07020c100c02010e0d0f1202010902060403030801030302060906 79
    0x10740005002c0c80250b1903d4030400c242008080f00140d18001240b40b0800d16580c0040c1c0c910052410070302000b0500110b4003804400e01500c1e00203014550788680404003030b640402c1c80d8889503580c40180026401c070039032046081b0008114007404518051542102c58101881c42c6d0741d404007662500d001254113801a04110381e038501140c0512540b50300056010750301c0313207040f83c8030440300c204d01c1d0244d8807a00085c114200f080144070307032400f4104aa0032814a0904254400f4800980c1c0420405010580c01c4440c1c000507070100c420b510140c001c60f00540550300d81e01d41140b40c020958080681200c07207003000d0001290796442401c101c015a0b52040750710101f0000ca60040508105c024403803411441442d40000494031401c090024040c4544c0310300900149500c0050300002c0103000c0e80c0d01401890003901c011402c0400204800381e0401e50039900c600c4c8590782203025200e400b002941180c2d0000300081095840500c041c100c9000b81c0c02d0b03418984420a9454848500f030b21081e101e0125 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 693365323 1250 693364073 693364097
    0x1a040603050c01180f0f050907030b100f09050d0803090f0609030d0f0b130c020c03030f0d051b180109060302070f12021005190e0f03041e090f0515060901 68
    0x40e00550404c11241d06000d0074a90b9942100c101c0e01300c01d0300242130340000d110041040e410f04c0c00354075403ca003c03410103000d200c01c4000440c800d4100f8071115410010018030144003c3e0080c100703440035010141c03000c601d091042c10030b0314a40c0e000303681d442d00fa03219001d800209000c01140c00c500070151040a0f41c501040d014400303000e010030403080340703007982c0d40daa030214555910000e01e001422036020108004545d04006030910158940960207504100058004609008111220b2034045200051a03449202c00240400d81c400c14030400d160000610541e0304003802104900c091090307031081078044d1218012010f80c010110300a00300c501100341036002903000300c2c084050350b086104a1715520410852081507541c01c1c2d40040b10309085a52728108c28403180101d0840340d8807000184a12141d142c4003a0b40e0b48100e00c40c10325020001c241341c94509131040f15507001861801c405000101c803480e2142d0090506488550840b0441c60204a0304c0c14240261610070905840310241401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 693366573 1250 693365323 693365327
    0x40510020306040e01020c100e0109020a120c0510050c060105010504060512151504260703060b1c030210150803040918052a0406140609031e011a040603050c01 70
    0x7001c0d00c0d00d40d00ca91184203190388600248081c00c0c20301e80400c0100201c26000101d8411540c01c1044100340ea418a584507026845400301d40085603d4031800e821064102e040ca000380441d2900b00076402050394000e4a01a40d2100140000c0d00c02d04051748c0b0103903a241c005617802e200b90b204540200d603040c000785000c6220070314426071001c1c440060f1201102400d000501212030113200218035a400b05003800000c152001c444602611254001d815030720301481d0300d90b5141c0c1c0b807000400044c1c6070640201144c883c07c0314042c0e00c10140c40200c2000d805464042c2d00d8030200c907503030300c8490f180148902424205414007012585c3c920091458642814400000361a400d40f03103050070303549040f141000a404000e45d500d81d0982c2c8141b06420700031588983c80340400444041c0c031880c10003c0c00d00c116958100301c276406500803030740c0303030740d14040400484d0038135a43e08030001e0301e90752000311220349080640180304030512481440184001c001e0030001110818000900b00b43c1c880d01946003694 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 693367823 1250 693366573 693366577
    0xb1e2203050c15100906151704050f030708040e070305040c050105070303090206070c0f09050f0112050a020307060e0a051e01140d02040303031a090915060a2d0e04051002 75
    0x60300c0b60007900d5031001e000b031041540c940b00f80c03448100e07022040800c1044490718420f00740507003070780c0e984400700c0c94410200070410701b64148a01e5a014905001c107081007000c120000650110b0402c1e242c0b241401d042460300c90f0420320034049141d40c04c3c1c000a88c402e10a100b001c2c410740c4e01900c100000d5050900440d056005514101d00340343d5034100d09400341c2c0c1c0300c03000380c081140701e00984100d507400d11001c00110519513006840e160305003418001c1203042c94084d51705590740000c1c24941e441c1141400c519203a02681c0183d00f40c01013007004190281d200717031030000c0741e07209031904040b055860041c081580c2c1d081d82d0410308150021901681c82d0303c200c070408a00000c0c020000c0c145180059440b0407031307015900032004a69034400c50386002200055420100e03104581180072403405400c001c0e11013400280c0c0c4410301c1203420000320640c0c1c07500f00705805011003500b80c20301c3e0000e680c0140400c40d0180c4ca03107030040e40c5951000230a1552425000d101d650b00c1006010441c1021100c1d1b0702075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 693369073 1250 693367823 693367837
    0x709060c0213110f0c0a11100e0f0103060909110a170a111f12050f1311060f0417120421060609050c07031821050a0b1e220305 56
    0x82d6008002003d505070f40c00f0060403003898900061b01c4180103030b02e00802800c10080d0810f0085d03080c001503c0059802c60040e03810320500350f1301e00e6440d0000000483c0101601c0d003105031814a8201d48130b05006403c03171a9009400280c0d8051038141d110403c620b0980709400003c04c2603803080c21600d000a20f01004011a4403000d082c00741c130391502285c041028100c07448540c001544454690301c1d041c40d0350241a4003c0c60324070401020341011000c680b00740081807000f4103480c080b2030b40303503202d62038000c21038425410f4140517a03100c680b10114041c1c00110b154101c00c0c284640200c1c1c2c607818401c04101e078101c90745040b1134124411024411000007034219419107a4658502d40051085954000c503032003240045c451541e50b008510780500040c020358104100c03110211000e1084150180315201c4480d05000925082d422919055190000c46040102038020074014405904c41d82e030f1200004807207403041c02c040d550b1003014010003102900070300c07051500098405008240107000800b41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 693370323 1250 693369073 693369101
    0x50c09040f1418010506100903031d04150302130c050412150f0f0510081009140d09060f0503060312031314250f0501110708060a050709060c0213 64
    0x390118440b00100103160840300100408034041001518000a102c1d00f940300d10211140e60706010800f90080039242d881c0801014003a160000b0a18801721482a00304d99900901c00c1c0710710204440041640710051208a000742d81c00101d0f02c00c440340324010450298960ba0359142030030701d48140304c10301e0402c1c5642135800c04640780c400040e0003118043c8030004164281c0101e01e14880c1480a070841e040100780103c1840059420300c0040740120b07012240754040c01d03010920b80c815040013054801300c02400f01c00361040ca82c3c212001da8011000408683e501c0c0c844406841e9542001e54991008035040c55242d00801900005d10480c00007560304103903002100c143c40c0180742e03a5041440b00b002019121544910304401100c0d1440602c0c00100b03100140b481111480c1c480d40b8220369160707000c1c0754180325103440c0060051404106000c001c4c800e8200310b030141d00300348840c540100019641000003641c10003003c20018002c40c400c0400a80c047d1401444d00002c0e03c0306c000605c40303800c401d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 693371573 1250 693370323 693370331
    0xc070b071202180f0111071e0b1903060501080103050d080a1b0206061011100207020d0c0603020702211504021c0302060603011b020d05090d0204090614060103050c09040f 75
    0x40e210340380c0c0b01814584100903c115403d0310403004000544503445402810040142e03030f0a008144081032030030031141e03114121408407242c0c0081440d0401250403031440383c540401c1e96015103038111140c007000c0c1c00303c1d2020409144c90b81d0044610280902028060703501c941d400e540f090b440362030165031082440e04000755440d80c00010810645403040d80b1070040e40010180203251410014400c0c90248504140b0709541038030039007944820240602030609035012440f0401d54540c6002554115801110354800302c0c0c58002c080c0007900b003644242d002c0c00a541002e6a80003100d500a015040308100500c2022042c002201c0e5140d0003c10403608440e010b60b4060505400742811014184660040c00c103915129040c10300310783e0502d03c00c41106c2201440c0803a91600400c100c0c00004040c07600700c3d034510302d020105180e04d401c800004d4109152290400500809900501054180070045192915094011400e4a40c1500e400da0044000c00c10717840c0344d1501d54400c441c2ca0300c140304086 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 693372823 1250 693371573 693371597
    0x60b0f0d0803192d0f0f0b03060a0c0f031d01050108100c0903020d06051e0a0209030f0a0b060d0c15051b01110f0d0b18060109121e0501021e0c01140c070b07 69
    0x4098071000f940c04104691201c020340c0307d03403409100700c4d13a1040c0341510800021021500090100c00b17528004014540d40d10390b040b14402003c0103481444109900a1005513940d51034030307544a0300c400100d1241842c0065001500d0f2058034814103ca030000c10300305000f0803d0700e51100420703010b072031003208101c107003446480c1c07041070060180708524072100103031540740007418107060182c0d00c003801906800c191003502c0051004403825820820075100b89582c032043e07190444a00b4820b41000d041c2c419190340c170465007607100e4000d0039a0b00004007805c543c0c03c20019103509960003603003045e068000510581440c0030140d400351200341d0809102240c8d103103800000c0b41408d000e1907050740d6076500e02c1082100c00d50b0055003400c010f01d2903900e00c00a000064a03804118009c2030908011110f1250480c4240700003501950360305042245030b50f01480c02d103030070341e6820b0340f080348946065400c1c02907100031040918202072280d514542d405103000c45ca541d1b51101d610f4000c201c1c00c180b0074114840 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 693374073 1250 693372823 693372851
    0x1090e0a060f05010503070e010b1b0f03070506060a0b2a1005040804050f031501030b0a0209030f160f06080a0e0a051218090c07060b0f0d0803192d 65
    0x2c1c42000070b004000034555040106250808116400580449880000400030080001c04480440c11190081c81c1c000d8500804c0505140c002e4804004600c80843e68a00f03010300466498043c1e10100e0f10402c9003a501ca030301e0f4280d13004400c4c44141c0c00d0b1208541c1c88003105010017842000c50402d055031001c1c80000c02400860ba4291002d0f034801c0360201e001e000b241014004040810012001032a01003001c006891141c070b01400014202c1071410f000c24880030058041d105000002415948452100034031035030790304000301610900030400d00303000612200e00110141070b03030380c5965030720002e684030100b502c007030701042011491038070942540c0c03400f2480a10004010a02206800d540c0304001d000081103100c59804540c4070302d0001c800e01a01e0208242110315082c1d00c5140403844080c202c00040106101c5001140c0ac0702c508000c000812012100039032280011002c214010b06080f4140b40c21200701c002e0520050490704190790010205031500171400304400d80105070111200b60b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 693375323 1250 693374073 693374081
    0x905090c210a06141f2c0f04140a1808031303030b0a060f0507050709020a2304150e03010902120a0b010807030807080c0705040903260c0d0c020309030f0a030f020f0601090e0a06 78
    0x403050002c418400c1341c00c450301d01f407130854810710390443d420700603104a420302e925042c0000c0e001c450030381c2d40c0303004461416100d0001c110016400003401c64481c542060140800441148103e0001c0e15003241c082c0c1519004001c0410350340640c0d183c3c0f607640c04c0c141c000d80c1c0347e5000110a07101403052000c005070240c0240000c0c4404034081d0381d114a045100300c100c0c86008071120078619204003d010610102074060f900404659862500c8050381c0d42804c082801841d05c0040650807808168000c10140000035210091078400c088201c49a83e0301c14805403105010f003c001c0c241c1d0420040325010411a401a010a0400300c080e15542555140010101c600402d012404980141c400c4c2022204a0f000e590540c61802111903540c907240d1142c02140c402c00740c182e0b0700e480e65845042181442002620107255001e030481c0c50603003903000c0341540c070030245004600080005850130111031003c14080d80c003210b183e004040c981d0902801901624a14010306182c0c0310f12400c40001c03680c40e000f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 693376573 1250 693375323 693375377
    0x55e1406090d0f0309080106030b0621060f060f03011509050709080601140907051912021e040509130308270a030c06060807060905090c210a06141f 65
    0x80c03d26905110316018111344210741c0144010307498080c0810100d1011082c080c0e20032800c8a80c25003130b505000e0200401c2030340000184092180c04100b04000d040402a980509000c843c5469041c0c0c21000305420703161240c40c1d541d00c00e91a50b404000c5c042864011a40000f0300d0b05003000c0700c6807110742d250b2078208245e11440c416600d60300b42040740d081601c6400d404c0300e10b0b850712a141100000b4211403000170001d51104100070030700020340d4a00c42d5030503640114100743c41c00c40c1000400d40c1004003038000e4050f20340b0540141c0082030320145c4103075202c2039071a4151112802951400e4441410f03159a1400c40c010b100030281e0019040da06020041c5000d01c2a16000c80c048200c1c141a0201c81172074200d50306562100b1000d02400342c00600780360442d902110041e02669400f80c134040e140c01000c04641350140034007a1040030600d80d10265110703d00203042001040d0383e070300711044c850005556881c1c10500d0a20b60503500d1510f801f0f890898492410300541c0105081040c04421000310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 693377823 1250 693376573 693376583
    0x30412140a111e0d0201110115061d062b230906010f12151b2604020a17070302030f030d150e0106055e1406090d 50
    0xb00d40346803503d540c24208808002c0074090005040074007040140003045800307814003c0101040c2c0030000c00b5008804254201c06840600944c1c650b00039040c042e00c030204160410642000d41da0504040054602071000c1c101654913010640340000020200c1c411010701261b05c0d00052542c5214040e0b41d164941c9005c40072260500e001c141d40c43c100311068101d10000f0381200402c101a458a02c6803101480c6c00220712559501c2c1c5018450040664202915074110840c1480d80c20b190072070803903244603041c400c40407180d2844205071a61101e085900031350024185505101050207001a04840703000c1c10112000141c480d00042c0c90700300703c4062100b045d4400100c02850111070700900d4031541c4001240121030307041c002c0c225514401402842700f01301e00800c0c80000e0b98161001041d10074030095200110f404043c030717440203000e45804198160641d0f442c0b1056131801090481c1c0311800a0b80070b401c03806007080303407c510408070150310960040017800403458650740c0f0350540312024407031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 693379073 1250 693377823 693377843
    0x71403030f04021c080f0a020c0a080705150301080a0f020d020a0306020d060602010204050f040c1806030c17090703020f0607021201022d040e1902030a0f0617030412140a 75
    0x90300c10410701000d00394184c050300d210041e5950008002000380c404010412818035218181400200c1c42c00150281c002e030300145115000801d000045040f03400ea0700f040e0391441c0002c100200c0c00115100a21032624191710207122000401e020400305e43c4104e100030304111000e0010b40010b00d248500c1d4000350340b06680080d58023400300c4248982c600130a4580004c1d800c003458000020000b14141000f98010791f00c6602c12010184240c04904117111100c00c0b400081d901c1d80b100038003d101e45c070721000c04220623007402900c401c4415001482120410028030078141141d0074443d010310341150842d00f2203010301155005030358040d514400c00708100001601d0309002003110003840b004121050386140034403042442400c01c034088505a820410103134107a502e0741d240360010611a82c0b45183d0a900c00300c14018882e545810811140320080024000716031100c18211040c0300e00404084554400c010420240010181080c0d090f8041c0050440820042c05c100e4144141380d10101c54034040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 693380323 1250 693379073 693379081
    0x311070317180129010905010e0f06040315020c0d0c08030415061701090209130206180310180204060f06051e0c01090503120c03131515060c03020708030f040506071403030f 76
    0x100398214074001e0002d280c460006d51070100041c00702d400084e58907000f04c403a01d84d03011280d25100308482c0115403146040c0ba50304e000350031300c6009420082c0201c400c0d000700690b03c1651445100c2c60001203402030340d02e41c036580780c41d9120a08044040002002251260390004d4401c190400c2c103010745020400105100600d4410801c03080300003010820083c071804103040260311100b05a405064500540041d04214000000e107000c42443c002c990180c18900740c450395910384500c007800e41d842030398244000e90300c0312411100010030303009034030010b0b5051041c002e40c0c1580301200e95032464404816454406030b03441a900703440c00c0c070341b064403294400105d00c800e007500e054500303038080c01900e41c2d00c2c01c2d403c02c420140700c541c54110008e4141e503341d0703030b2a4070000010b5009400004017191840200b996034000038052160621040d00580511180000ca040001c02205c80510748450001e1070142000104041341e003101c0c0c0165030343d00c2036001d2a01c03020010001940201d404010128091034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 693381573 1250 693380323 693380381
    0x5221a09130c020c03160f0b0d1121090a02090a23010308070b090106030201020d030c0509090405070602011a0d0231021222020121060308040603110703171801 70
    0x3c4600d041b48800c2c1e8501740c100302c250008140c400a0324074074054696140030200b00140a4400c881505210300000a803160401042c0300056690200e950200f01166540d90001500c0c1c0e641c000000c0c0d00000d012000031a292419400001c00407080300c2c41070303028030704440f400c12000426041101e0000000072080c0074042c0b4169520f82c4400010024880b00781940e0000b9118040814660305150701c3d05100d108041c081c00c181d036520100a04600d100e0305d003604002e9554810ba220301030242d46031202c900000c40f524402194042c40c064100090080d6542c00d218a46440044448088203050001e1001c0d950480100720860103080c0c02603194150f95001055020016240c80c0000c10803a494040e0611121545d00019409003000321089006a41c120000840001155141c602d0b10030301108014011000e8000c1d641c1c65501007240740c0e0000b003081074500c04d4000c0079000c16507100500c040b6070a6050b20507800341804001d00007044681625500352044d10b80c40365000c06010b18003500c000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 693382823 1250 693381573 693381583
    0x1828090501060519050d08040510030902130b0a0b0c010608061302150a0c11010516050105150108060307030609060f0204082b0e270705221a09130c020c03 68
    0x843c1c12103500302160f1800e0448000083d081c89a540208207480c186001e00c00510103603802020040d01541180311100740013401031000d110f080b807056141c213960b01e40b00a414401c081044030050280140b03181005810402c3d03802a01703446c9800d6407100008608101d040c4130a0b4000e10328504c0c0c6031881c145520400403802c4603501c0d641714040d0103012091034650b00051145172180c000908030f0540d10080c0040b550b0f489044404407102402d56143c0042001c15480503210b0b807440801941c4c01c2c0055001110340c0041950400e9140e888181c0610104446034170a100c05031090000060031194190888144c0e0025400290381e50080c1030f00a4443c04050214840b25401d60780301c0000901071030001d00131802e14040140075807040b05071080110b01c40c0030f10441170119903503514510701d0451001010755001c07007002844412205047e02c4540d1b803103100801a180e480b09100030000c00440d52000941000795002e6201001d030015611100f050b10610b1084950799014158080242c07003418070700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 693384073 1250 693382823 693382829
    0x909020321030a0f1802064f060c03050c1015180b060301060f0c0b0c0a090f080c0d0f021518060909010302010e01020a050601061e0e182809050106 65
    0xd0703050034070440704440c41800501d90146c4c1142c0c11500c80c855039501034540d40b010242c501c1924000b420a2100d5500040d130890784954600543d1440041d03112003064900040c4140306c00f1800f2002d40200190103000035080088680b0100c40031200e2100b21314090740e605108500219044160030f114464000815181454040900707002c00324000000c00d0305440140700749403c01c651041850741040c81101440356660300304241001c142014644082c90368040c0004c140824a0002c00103404901d50301c0303c40848090101820304002003000b4801608084101103c0c079496000c0e41e4001a59818083e000b64094910f009444403a030030072440c400342c52003440c14410f01084c0a07002e203a503144d00c0442d0640ba420701e0402c640610200041c2d1030804090300050090007140004107a082c0c1c484200556072000d07504413204800100c10640345102880c0b460f84e001860100c40e828002d8102100e030390810320502000074103001211004043c203100f280260f020b55100d84400d41404000d004078009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 693385323 1250 693384073 693384101
    0x20a1707050306130c110a060f060503060f070e0f1002100f152904060f0e01030905030a0c020a1502151015271511010b0a0909020321030a 61
    0x1450030f1040018514401300780001c9055038684c0b02013428030b0700c10b110718038903008030700101d4604c1c84203454008060000b40d01d000f01c043e803800038005414030300040d43c28050002c0b000034440a4540c240202ca40000c03105149400c00300d81c4210001380c1e01e81d007400d9030b200c800d154058104007025203603040079618044060200b040c10850348280b13641d058a8554202c50381b004d0401ca815107214980090407552044c0840d04074808540000c0c003d4121901998a0013143d9070b00d00b800c0c14690040d401c990300f901000d801603005100d960850350043d00c3e004071181c001028400d0013583c482d030403206400b40006c00401600401d1002491040407102c194001ca50000e043c800c0f5401d00c84040b04903040c040d00e150401a861151105005994400c0030b26240004500650941c40c0c41010004041c0301c8030340c40c00104007031201100244103200b40105000300409258200303103042a07074006007801c3c94060ba418010b81e003c8801b1008601b41d00700d000f9246244054407460305814036011603440b01d4071046 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 693386573 1250 693385323 693385327
    0x612060801020f120a06050901030506150904030813020109080d200a0b07180302030a080c1b01021e071e0f0611030403060216060608100c0207050d2301020a170705 72
    0x1c1454082c02664100701c030f43ca508040c0780d17a0382803c480c041c040710391200b600082d494002100384540030450381d1081d13000204082c0002180c0041c481c810404480140005540c10701086030014002c076400c010500524014001c1ca03251182141040c192003042c01c0031800510503640e05103480032030240303100d4441014200e0300309652552022200d00805917010071039084e0340d00c4030490880c0030b10405950080c08440304240c4510348408154002006103400d032160307020794080c0301100547e548003900306a0240c034180d0b52200e8609808540b85104c100e40780200107000c1107460407801000c0522041c1c116034200c49241050320342c4003840e550404402c1040300b99060a41c41da00104660407aa4809001a41d44406001c00e901e00c00410170002c0c80a81009270003d108000082c0c8041c1807022040304100d14a182101642d540d540c40c13040580105a0034051f5020a03400d41140c9c1004140c0c544502111603200d94a0b400ca80c17100d055000400d4110040b503007000ca0000029038803501d14107003d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 693387823 1250 693386573 693386587
    0x40501110c0a0608091c0903020f06031512030d1404021f0801050d08040b12010f08070f0902030a091209031b05060304020d0606051003061d24010c020901061206080102 74
    0xe2021110703026000901003032002090800400301b141c014031610540048a4a601064000301401a648000d03840b031458440d44080610f4050300304d81c040e564821403004400c110701d05100e240f2a120340e44003c40c0c00181300302c4182c803610f8002d28285004c901c10302c00d0070b2301c0c1c148104802c800c4100640301440300121011059986c018096a041d42d2040303810000c0c00c0464030300000c05100310707001000704150110710f403003c80b5820149a4143e800c1c07004140d000e00e440e0b560b09959a0b1b241d106090803407115901c1000350701942d90095820440c030381404070301c2e4503c6444541004c07802407240e80c0000d4207060708100340311210450008410240245110a520b0b101c00282c01c0d0001030006480742e005110711004204880c0d00c0a80240f1024000036940c1603d20400740040c202072050100c050303c00b0591019010880c03401c18400c5028103422075030054035014030304010b050780111301d05018103071030f1110140e901c121a2500a08103541ea8990603d03450034590180d948680c001201c5a00612045c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 693389073 1250 693387823 693387829
    0xf0504091404050111070b0703050603120f090f03010b0609060702060405060a05040311090f16030621060e03120c0f0d110a020c040b01020c0103090c090f02120907031a0406021e040501110c 83
    0x42a040582c8c1d03d40407071581c0740e20f030000b0305104041881030220320300090401120800c110103484146000c58080010103442c4082c14266400c04a0480c0d000004210181d10b40c607000001c0c00c0503d00191155082035126004074156a11520170304010500108042040040c2e40d0403580c0001c805035520585804d10388080d0740817003030213048041402030002c2c00200451080c0d1010f0700414100c1c2c5079a00c4041d0855040003d440b500500392485070801d4242200101c0c00021510a1262182e92090343d03620352580804130307049803d206080b600200302d0000040c0c814002c107005040c0d0010301d0307552030240040180c0390260710321100b4042c604200342c941050b138002c945005907280071308000c500b1000e24030309010602c00f1600101030b030629000c880306240f41981d0180c031396100b030084d00d5400c54448401c0280c1d03a81841c8001806000c801101c080060301005186070054130808015081c201e0901e140008242e505448006490001c9020000d5680c03140c00701e07003c5080e14001d4001e0100100c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 693390323 1250 693389073 693389093
    0x18060b040e04020102031309050108190803010b030403120920041406040b0a120b06030d05040b030739020a0f0b0f0c0a150f0c0305070f0f050409140405011107 70
    0x80c0c40014070850300040d0a59000340100c0b0071524182600182041d102c40601004080c01e01130b1850912501c9849400f0103102030100b540c60780c024800c1403c681c80c01c0e600008946c170040c0100d04110070040d0703103d40c00090380101004203124480c03500c1800042011030b03202d1025401d5151049003049508c06448205284a603081b60082d030300071400e603042c0c20104002c1d000a600449110280c4980841840206410240031303400403801da0340c20710b0092000321218001c50007036a0710f030b41d42000403500703650040d001c0e6074850301025016003810180c880e05240701c01d65140303400a0fa402210b45a403c600c0c00100c1003014205140310740c038015050028010850042c0b580c1480004000140b800017004d007004844ca07540e500c1150456040300410310b24000c2c0000c40c1e48810a103040c0f21045c008240640103c0e4402c1405958006503240b65484c103c4002c07400b030f0040400e1040400c004942d25103503001d01c0b0b20205039039283d14464100b6280060071600d080d00003424150702409000c00081c002a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 693391573 1250 693390323 693390329
    0xf0f0804031d10080a05060603040209070c030c0c060206150105030c0708070809091e06031f020d1104090c0e060412080d02121e06030a0309150315030b0118060b04 72
    0xe0a05030a101e8441d000149502d100c1c2c1032030348150000f02d1058925800912507101da180311801340034075103400080c400140001d0350000e511805000018407120310606040c0c0c0c82d140a03280c00c070f0841c1003a465900b9120550381181006070406010042e0481540f640b4400b66031080c6801703031640c540251180964060644002c02115001030114280f1403500c0503550124001060200d00741040303020a1064032481c560256001d1110001840f58540400c218030a1501c644901c09003186e440134a02c000c6d070154443e4001c40b03a441500c11113218441c0040d001520321780e800040d02c201ca844000d0310381003c4400c001e01c03990040109003c1d0007040e85c0b983c2901a40100350300d445080e80b5030404013900540c4c40a000c4c2c0707400d1004201401d0700f421042180703180002c2032001c80340c80e09000e1540b180040c0b14064003003841c0304402c0001d80c800c1c81741000c070681d00340380010308a40c501c0d0313040700e03101880c0d0b00a5568241403c0180000e900000c503000d400403c0103010001e091400d0102d58843c0078901c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 693392823 1250 693391573 693391577
    0x8100209040e03030a020421080306010e011e2304050303090d0822030b0106030c1403270604050f0d0c03080a0b090a0501030b1308090f121209010f0f080403 69
    0x300e46400c440c0c403240c0142405904000c2540e8891405000f044002d42103071181d615181040d80c44542041e450703071a00c600090b007000c44145165207180055031680844818507040040d01280d800d99442c845040059065880d502e0a144240704606c050900e401a1203144c403005040208002d980e40000464003c90820340381810030425500f4032280c0c9004035465810a18411080c4407406480d45c140c0d04140c91045034001e800743d0f00c4100880071155249031040118a143c8500c010403a4280055035101d4500500400ea1140c2c50040750101d001d50048180551300c0441807104201c010b0040d0022500c01c40010001c25251800080c01500e0a19014003801b003414080b03015100180c020380c0c207107000500305031564100305411200400d000d1100307640b512082d8021540103000c0e200d004403903903008516182080710070702c100f01180180d40800340e80190181c680c00c00d40c550600101e911050360111075500e42e0742c8000054a241c2c103042404040264490000d80d15680026a00d90081e401d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 693394073 1250 693392823 693392827
    0x30c1c0203030c0609030403060609020a020c010815060c0c0907080408030118060e1302010e1009050f06090409050f0c010513060807140f04050406050d080a1d13050f060901081002 79
    0x640046401d62140c18004900f5000704001c014600b0000001842140c2c4215000c00082e9960b03d52803049009a03840c810047c1c0140c41074010755171062000ea030304900e81c0c6420b07440b1400000b0010b4131950220b0110b200680242d6400241071070003041541d408030721130821510900c2d1070f55614015100501540c0d00d07008921051900345100781e4400b46c0078069140b5840c50700d040403032448210710202c1004a001030040780c942c4041d400c0010a2302c070b110407243c64440c801b078105000c0161019181e000d281e0085d4060100c5861580c40b409051302d007500540280610030040b004072801c08041141e00760510004004803113140d40b0040001c02240c61074503108600c0c1c0c40351081190140c007941d61004540c01c000c60812043c881200c014000c5400032242080400d956409112074800382c081d024040030b001b80f10301c11429024000ca185054008860308181140100000d0510003609841150180e5900108940002403904258000c142100c03540003a6141151442d0754600398222608581e0300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 693395323 1250 693394073 693394129
    0x3050a06050105040b0a020715050706051e060d03030905031605190807020105180d061505011d060307090f093801140702040501083009221d0c030c 65
    0x800e2201001400c8500409c4101030058070006015820001040c4c6105140001151a048041d40302e80c04070702b0f20b04040300490b55613004205017801d0344035083c0d081c161941680400140181300170003030300e540c010786a021004d031804c00d1031404071040c02414013902040405408220108140e0b203949131709103415a80c441c10701040905e044240d00300345401c6a80708460030100001600b0803032a900f07040a00e5080700fa5106c0c01110304000b2400400c490002030034000100b0301b0001e00442e440429030805600895070340104011b0407403554000d1030429a195498488040c5900c88810002c0c60b039040100403018001c40c18140d18034410320141032009021566400c0500101a00c0380190000c00801c86c540e516807546403100d042020500e00000d4040152101c01824040170319540101c2c5240d43c00c0c004203006102200c0c803812000d000d0b003840014030003400c20440c0104445140c0003170a009a0380800140c5502c0c12003001c3d0464400e410808501480e500c61080c090748400c1600780c4d0901c2103070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 693396573 1250 693395323 693395327
    0x212031f0e0901050a050a0b06030a0c021203010b04060306050105041d0a0e0d030203090c031903080a110d140106090524131d060103110318100507030c03050a06050105040b0a 77
    0x1503a070000d41c0440d42441004907290043d0300c590f00c41c40800209010f40c0e0344941400048882c41083c080d800941400070075140e921079804426642114011600c13070550780754440359650000d90052240ba400010140700030303a494080c200060400b130802c141080d04189038207804100c003044140c00590042c1c009011202c450300084a224640c81c2640c0f0740029640c0c0c02400b0758002c80782000a8030410b9490310702c6040004600c81c210921400c95100c7c0c114541d02160700442c041c00c1c80ca4015101d250644600b14290700824040240c4a0700052500209480760800136059001400348401d01c0c0301000551030340c514608800c03c2c120020300d228040410100c102c0d000c3d128103242031103410100800c90303850710f0341d814441081d10064000e80d0344e180700044058900480041c0340d003d00c1800480c0314244400f843d000c9940c01b0005840340030440300202c504940086070700d000042d840300b01e82104640c0500c00c1c0ca82007841d1b0351040c8541d03820040040d0407031085101d14803903034900280d034080140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 693397823 1250 693396573 693396631
    0x80403050d0609150503160806060904030314071710080c04090c0f08070f0905040f02211c0306090917030712061512021305060c0f16060906021203 65
    0x110152108100b044c08002c00444110001d01400d4003d10410103ca04103000c06d8950004a424103002421140c0e158018402c1005002e0022800c0c541c50b0b0810f0000118814440c034899500d40e07468001000e000c040ba043d031700d68054052810a42d891506004854000c030b0b90700e02c452800d507404613064005281c490f00e8001a54440701450f07461040c04140d0310310114035402210b00d03039000e00208549920400040301e0301600c004145450100703c240050504040492900305011400381d000d0290040325030034140004070300d4400c13941800d00352030f4446c0c052064070090405d500d07013005075500315a40c05041001e040300c1c0e40852500840010400b40c41030f0341c440c0812100c050207001940d40c6000030540c1c203901d007034a00e010921701c00b054000308143c0d1080da9192031b541c03520f1b130021364a1720050085907489603081c0c40c010f01990281c031400c0b0f4002c000102170340b00040d0004208a01d0503000401c002c219170461402c64000030300c45441080c001e015260480345414907101c00c0503040340300c070342c1c28 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 693399073 1250 693397823 693397829
    0x280b18150306100e01150c060b04020904090309240212030c0708040b04050406090207260903070e09061b04090203130213090b2d0a0212011e08030a080403050d06 71
    0x40c410002002070000000850310211580803400e2880b6980310328007496984071b401800f030002071001c040d00d000b00300320703421025140001400051030f081c9420046026610300030415004242000002c000040300350202c98480c03050428494249112030318000e44440c40400007200e100800b02c042051156654100e0341c441d540302203038565442d5201074903261500203100d103078030031850020300082e907903100d000320350b030080e80000704080040c01c02c0144015843d1000551486460a008070103181e10100421805415040303100d01035441c264100d030749442002410350708c140c031400d2006502507081100f40d900fa90450b14001d40c8a41e600c010303483e003a940f4082c0c081d500005840c00d060b03c1001c00d50010000c03500036403ca20702540c40d55000401101c0940355103030b50b00d100c1258071140003003200105800c4401c1d0306000d480c000c1d02548031b25400c1d40a800403e4901c21010003186075524240d01c0e10001c1a5800156042406c10000a071860304010b01c05824010700003080100c2c0d01c4558021009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 693400323 1250 693399073 693399079
    0x909040c0819030807091401030906090b010816050d0c1a07170a1e020309010318021201060e0703140112050f10020a030b0108011a0c03070506280b1815 67
    0x2d412001a0380c912920442d00250046034201000c641c050f8881d040c410306503460f54407050340044121004600030090380c517094030729a580d0f03034520307000230b8040d020320f8003e21488005081000030030f1114050414203500441c8505840359204000510203504030f4111421071802002d8214025000301c0e0718424103100500414030742840d12061101e00000d400c40c0c40b1b0700d9a91000c810070001c0c02c08815034410b28040e01690041c40071060301d40c480c0e0068661203445d00001c490a550582c0400e894910310403038425541d4550406020020b8006a003ea1204880c6001d0002d03c1340c0c620004c008030340c18040c080c192800301705102c051000800102c020760703010404603480003400d0300c1e240e0020742040506000090400140c034143e50311034000103059881c443c8046441e2141502e65003180c0d0700c160f01204240c002480840f010078010b0003680d224401c0c0400d031044018814101503a00031000b9240c0c07600340c2c60180d2482e0300c1c0d1100d15810139400c200e158500003c7d01d0b041c81041c00c0d2140d5100d0164 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 693401573 1250 693400323 693400333
    0x29042703020d0e010e01120c1107080114071d15070206070c140d1e0201180617240f0a15020c03060106020f10090206040510050c160b0909040c08 64
    0x405500203041c50341e80200d0fa58019401000c40300440c0e4400242044900244010310034440d000314603070058046001c076040c1030054003444030030301d0304203507603503002074141d940d01c2558011000086048590258440c0b0700444081a1103003c10340d99210002400c0c0126a11414a03e261a0704412105440d0700204241d440c0c0c002854010254801809000584003820006800508060040c000c3e0640e1168008580c640e52505a0f8040030841c6804d03810015981400c45007800d00c00700240c00750207030340d5841c110760755241040d00d030614014102c40d9950404001c191040c2040c0c02d503910030040c086803d440b06500c00c000180491100340c214113803890000354084092500001c200060f081d040d8190351050f80c2e604c10903038803010005201259a0801c580994904a699200074129440140024185070f01c5401017040c000c02c0402c070501007280000d0a80c1141c0e010000c00c0342c00c10210084007901400c1122980a90044951007406081c1d20000b041c204407480c0d4081004d0824041198 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 693402823 1250 693401573 693401651
    0xb031009052d01061a0a0c020a0f06110105060f0105040e0601030f021c1401030201090501050714060c031e061e040603060e06060109060807050403290901020c012904 73
    0x2280c2c902c060408844540c40e1610000f02c401d4582420094405074561441c20301920304d400f91075580003040e003281d000b000590049500c41c08100105c01810303e907601d18030004841c000c454212a0098003451058000b48180000740e0f0303014040f81c0c1520003010301c1c41400d0b124000140c0c050484064400100c60001c152100b018509520b82d461050300d51800340034464140003008442d0000f0302029000401c0d629041c081540504000e02401d44201d040400f44203440d0440c1c0c1c24810252041b200700140041401410910144003040070004c3c1e403415000b0381406400640341024000301c40c0031291452918200980e15031740144003c1d508400144010890880203a46401d42282c400b40801c1d00d0f20b901050151160400320310030303291034444034a031038190745603821030540030180c00700042401041840d00c4001c407203446004200540001d80c40e404c000000354203542c14203011081c480b01160703039040e9100c1c4041c0c106800c1c5200746c0b8001190001200c003580044000204929800d805080072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 693404073 1250 693402823 693402883
    0x1f0b012607030b010305010e010b030705130e150603070807030518030d022113030309060b030f1e0d090302190e07080108010506090402060a0e0103150f0f08010b03100905 75
    0x41c4900740a5804001c4904050015404c0301c9003802541000707290b15005009911049001b0f54019105052040c105014001038008896079504161104010748041c808540e803804442c032800ba070704907442c03811490100c50042c0000703401400d84042644580200301042c0c18500d0741072400c10b086003600e66888070729000d04041e6200844041402403c4c03500c1c90295106e4803181c03806062060041800e44499880441c09007410101c1546d45554441c0d00c13000ca50380400001031550705180c0582851120b00140e1813410102a001807e160014a685c0315840d5100d1102c5007a1380c5e0441d1170f842c55102e01c0c01d4440307421895800000105882005000c0ca240d0400099812035840300024401035641009014030210241c0740250425424007417030383c200b802811881c900c4d43e810700d00002c2c04800f14613001001d0f0f40a5104604480090400f8808500ea410000020b410150300a00500001c1c0c80800d6a603003145506e0084156103d8904080103001e205042c00041040000c21100e0900100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 693405323 1250 693404073 693404147
    0x604110f270a020702010f0302030a0b1f0807031b0503100e01062a03080a0b0f04110924030609041b0306470f03010f05181f0b01 57
    0x100d4108030107030a0000d8003055941c02142c0580780d045e0343c1c110400000303200c10350180d0070152044009545600101c40c0d0764441c542201c10042c01c03000341c02140194524090801c1c0301c06800d5504044c14285140403030b40c4d00101e10400003825180c85a40c035600c260300300f10f0000042c0c1010031402e601d1400010f00c0c03071703000340409862242d040b0321102d41203100944135502e985184000b004110b2000000700403203484e0348560081c1c00040d00c1c1510061401000604030340d8020f000c40800d00340404c200b40b072814402c0000312890780380f902c00c2da0411890146005180002400c1500c107032030327110000303082060484241181d0000740f006d82212980328540000580034454501244400d1440c0c0e045101080070380c90103080d0100d0126600510544c0c9416128a02c1e800703c0c0c079002806000d4102054500740301c0c94001c80c194036000551403d00d42c189c4c0018401d03c00781c40b08a0b6000000402030654543c031083c80702500104009420159100182c0d140038a900e03a00842c0c600201d10f0300703481023203110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 693406573 1250 693405323 693405379
    0x6090a12050d11070b0d0b030d09091415040903020a0516030b0708070e040b0f0d0c031403030702060a1d03070f0507051023040f03080d050115020604110f 68
    0x200b564012241504201c800071400c1158021a43c003032441081810308103c002c200c42158900e0111791300d1460404645480200702c1400c0000b01d103240200401e10591140114111085032091075600300304554000c1003000d451400d200743e546246e80d5080500070030031040310a900509a0b030f600c0c003012240c043d00481a12085d40c0d90b00f068070026080e2480355515910402d03203500e50191140408007844010028074801641002c507550f402d043e42d03a07519403e0450640310350000c0c1032a40c03d5141900c00f5101401c100403880e070052041c806415008503805034405150000066801002185d10868030421113240d01c15000028117442401036580c0801c81c8240154104c0d40425914006d0100718003c1c004000000307910028030034005007201428010584201000034102038441001c1c480301c0e481c562007280c510b07100040084025100d40202401002200001e040121000402948402c40104003c0c41000001d0844807107a841110403075031000d010b4a1080d0301c6000305903034205104460 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 693407823 1250 693406573 693406583
    0x13020a080a050d171915090e070e0106091701090206030103030e0a0501020c010c0b1b0424030203011a1606110c010b090c120910090807020907140a05070206090a12 72
    0x100703603c01c4080c010140b1060440c0141c085103505c1d0350700058810401400715995000940f5200d00d0b261140c0d82c100e02801802c203100300090a48040f801c1e0384d1a10340c2c15030240801e10b00e883d0040003900c3e0841e803900d04965030082d1400702c110a91022600414501c0002988903502000101c240350707212904814420301510340c011555155801681e8940342ca4030413600080348a812503001410340801150007002059442c04210809440426a50000d0b080b48040344441408001c261814991000d1050f040c0d060442c51941405402c02c1c0030303100440c21500c108800a542c08900d200d05065441d26a0031100401c4590440c15640300c145d4080f0010071403940c20290844c1d4207241a120490103204540803d41c0f44c1003c104600c981203800408043c02801540b030f0352000b800032402444001c40c814103c55903a040030380304010b100780024041d4070400005080211000365a9003c440700318800381865903d411103171000400320305c10101ca26070004150240040c18071601552500b11612403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 693409073 1250 693407823 693407833
    0x307060e06030a020c0a0303090614090d0509030304030618021906050f07080d14010503071a0a0f17090d0809010b010c030305060d02061303060c170a0504020f120c0a09060b1213020a080a05 83
    0xd00b000c103241e042e00780c420115903009090070844dc1c9010300000c220409010741036a081c643c0d20744607070301124140d1181850640c3c803003c000f01140b600707000c0388000e825004408007004e0b04046000b04180500c94805000c14000180d01c2c3c02d0082c0c800907101b10401010081c000d00034104410900210203101d494040c0c070400c10081052012141202000c0d14418113440c00c004800e00304558514030002c0200a0140003588074083c0c2000003c0a03214103402c50080c9050b00700990000c002d240028600c1605906d040980c0049a0740017030b429070110b0b014036001c24982c65000010b20684d00c1c80d0310007580600002078400b81065012107040440740111001c20400407000b1003920080c2425625500101e00000010304904060340402d8101c0d001070041c3d03204280b10030100e024910196035100c0c041d440740342ea8100c0b40c80d203869010050441e680003032051910340f900803c111300176606110301c444106400595881c1d1102c19400704680c000b80581006036a5110035525040c080400b50342c036000d2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 693410323 1250 693409073 693409091
    0x303091a07082a0c060319020c030c2401060c060507020304080a0501150510080408180904260405060427060b03090d1d040b01020f01150806060307060e06030a020c0a03030906 77
    0x1000c0307181310240c04054607280c5540e035021941a042c011020100c0c500365401c0c894247c0381a8100050005049440c0c014003003032492503082010046002501c880480101c8010300031940e1101000d890310b0b5000002148a4480344800d0b811030240d900903400340d203d01001d032400d00c00d05400c8610315040080480d00300c0f07030301c6109000c100000c025883d07010440340e030081400107000300f00901c2c031000c030b43c0701c50804402a80c00140100354142c0e0184e800c00c100c0d82c10040b40e0050700d00710480700c40d0030215281c60a4039050203e403442c021482282d00030070328050b2410100c81648986031411031008810402c0300d4940a00d414241c00548d01c00b5a64480e00b00c00c1300045004c2e1802c100a01c0c40045802180c0d401341c6c0030040074082c3c4112040c11406000040595034400340a040d908002d070014100500f403c0451311071401078001e203101d1081e03000f1a0208000d03600042241380d801e000361420743e9250785030354010f0041c1c07242c0c2c882c030b00d040d2003040e27461400e0507415403040c84440d206100620002117 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 693411573 1250 693410323 693410407
    0x109060e030409060e15010f020a2004290d0f0f030f090608060f040f0b180601170c160821010e061008061309060f02041d010303091a0708 61
    0x71080325034401b04221030140031525805003002944265451040b501203071865581c3d003500030660203145c00b04080b00300b207041300c03460180114084155401c4400100644000f026480356141900ba28001d80020080310240300d011085101004d4102080b501c00c840c2e01e18006010020707031008003001414118010684a101d113040038000c0000904014000a001c41000018808068518105035807040f201c280d54654100c28020001c04241100c1c035440e017200050014100b00103140703140e4906004201540c51500309581009500c840d14940403d02481c1a144034898080c0701c81110b2062061031400700750705000329050b01d0108141129607210b56040c803003000034048040d0041100c00001500609240b0014031203084164404181700c03032943c403101e0449045d05108120030350001018858008102c400e05140c0f0182c03103041407a589152401054030b181d030301030202810007151444000c0c0e001081514441d90300880d4095681002c1d4030000c2c100004242941105007121144403103c41c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 693412823 1250 693411573 693411599
    0xc24010b03011a0405030d0c020f03012007140a080721080a05091603050705040b01051905031e07020c1206100909060e010501030f11060f0a110109060e03040906 71
    0x19298800c80c0e00310303403d050755903441c61010200c4104240c03050000195680d0300b001108141502504d40c17290f03140f12801031204d401042d1851500980c1000084580035800744541d160380c04c0c080e4401916a0441c0c50040045807020f2024105071258881003002d10440791f000705200ca1040640700d11180c45194101d030094080c0c0b041c9008104101b00051200341c5640105a00c6000d01050700c1c010030f201440000340116541064916600490007405681428840d0240295090809504181220707012040c1c80602c4c648100401001001088581000441e0200f000d20105440b50300341c0f07003807403000f9a52443d8000035803280400c00c0039121102c0010603424012500460503400003420005141c01602c0005021184c40780c4d905c10f1448410004c0c07144501a500c43c0078614111921800c000c8e604441c16460703144150000c0001005414404084900b130031660f09103213030811080b600550050244d580007510160400b200e20701e4414020008209070341c80c0d810304100f09622542064918 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 693414073 1250 693412823 693412829
    0x1701060f2709080f0a0210061a0c2b021e0319050c0d210c05070b0a1e1b08090a0b04050f1002090a15090308031305030c2401 55
    0x84508040301c191a041418410010104000400301c0c44aa690b541c0061650011894041c02c40001c6078100f941d6a040c4090100716010304004e0050714103040d030818030f1640c55464502030800005040c08a1a8107206030040540d05490b2010155a161302018804102d8911140180920f0008090b000c40788507a0b0f004d00401c2400a50924500e04503580c00708910080c02014040244640ca00b0208100502c2d00e5600c81a62050f20b00504642d4124040040c108104c0c450703400d00d00d6900d500c1c1d5102080e1045180c0200c0012031a40f80d540340c0c1ea000345070451800160341d006801c400040041c41d04180c40b500001e03c41610382440c140c00441e1396040642e440017040d04042150340111b5541d14a154005024900380c60003042800801458061a41c0f0310014040d00855440036601d09404100028024000b00669609a4020045c940d2070303e4080144a4400440411f400c17079a03004004640680c003004a03a40ca0801e1045165940d501d402c2c101c400da00080c0070043c060150316025412 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 693415323 1250 693414073 693414089
    0x1101080403140a02151806101a09040603060c0809061e0a05220609020109050901031e03090b07050309120a05030a03021c05040b0402011709030a030b0f04061701060f 73
    0x41042042241d015a03200f12005803c44c800c2c01a424040303400c28012a0255500c4007200519032007114120342021801030240b0381450119408011403010300701e80601c0c8403490f0418607070354085000010020f22803504003070203107460540c4501e07000d604200100d02650128040b00e8a0b030ba543e4888041c82102044005a02078188002c1110b20a582c1c11654010703030100100001a00d07043d034205050210410290745031512218464290b50304149004064103060703c60790300303a40c1140ca580910640f1282c03803022050302c400b098814503205404003009840321426050790343c1c81b00e0030495500e07002038100b82c1c17042c0e80c290075412145070001820a1030580c8040034500304403010310b0a400940050390a28103c0c1841c203c98214803c20340f00d070034800e91041c400040903040a00005007650f803880d52003400c0d90380c0c05080c00b282100001c00e60300f1580da280b034041661810100412095031001410035042410200040754a0a02004500b0b5841d02440200075441e07072460003080e02d0040c0d00c2a90380e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 693416573 1250 693415323 693415337
    0x503030a090509060f040e03070309080d09031101090b1b100e0d0513080d080702010e0105060913021305010b04240c0201050309010e0601081f09110405311101080403 73
    0xc9400d040c1c502130360084005011000034210031000c98103030303045407680f041541c0000907004201a040030310900078042c40d80040001955114001d007124141e800302500040000200b01079503885022820007500018440c0303600d40700c803420200003a9017044001e556901444200600c4246244030b8950081d036185d00820420003008026511035124240380668404144800718100d98108000503111010b6910820185001c120003402c40700f2030704548540e0790404041c003a096480020700d40c2c00001d40000142c1403030241c40000c0500f5034800403e0b1509040000006442d816000504116804a0707140a46903030420f41c11044071246130804808141003603890005940b0607005140d100c1030392000000c8442c0610aa985002800d9003d90350310760145050101940700341c40c1c00c9405004601c0280701040a9656a462031601c00c0c0c03000d402140e6640010707610f0b582400c00310341c0101c8401c00150420514807684071483c841d1100070303210f60300c10030400502e035445140c00c135102c1c54056943c24 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 693417823 1250 693416573 693416579
    0xf0b120f031b1213140d050d0e0d06090c03020f06030103050319090302040e250f03080a02010b0a030c06080114010804060e030d150305070902030705071101210203100503030a09 78
    0x4609502107640010700ca21800c0c80701159281c040000b094030b022850000b40d1101d161420344031810a501d41d40c607004106d002000303c0002d4001981d41440c402c075040c1212080094404183c01213100f28005e0715850030502481c052203c61655401541e00941c1c060000d02c2d00d505c10700c81944000c0c80028101d910410904824003240884e28600200514107081c840d552070300002e05a4400d005c41c40419004102001c00a5030b046085504501c4030306d8140205c0c40c0b809810140070100e51001410300180010307400c1c4820b10030b5021240110700203060000143d100d091682540c1d089024520100748201c1c00401c04415548a8060366001690751044030ba07155502d04002e040e034180d03503420510091003400203507000e5014485c40d0060101d41e010350a8554100140741c41c0b415170110810b50301c100284101c80d98048103e512071a04a0201e644102c3c1c1c21004072500084c00c103003101d5049200c1842440341d0410340046029000e000001100d01d0345860400d0745a01c2045024004524054410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 693419073 1250 693417823 693417847
    0x40908070b100306050916050a05011b020402040308070b091006030c120309091806180c1e050306070c02011116050d080d0c02070e0907060509040e100f0b120f03 71
    0x100e81c0401d25040300b58085590b0b40e114001d44009840124060300401803228032800e40a208034010321048410580c3c2601d404000391203440402c500d200b0008000981d1000d6440d950101c2e00156440800143e9450042c1464404070a00752103900c0035000303484503101140c0a41c01a00c0a9030f4204026a03900c1d854010b002c2c0c00d10180c202c0440501c0700c18400080d86143c903100307090445107030b11b51104954895180540c1140d2103155510241e02480c04041d0200e0b00c42050001652034005003043d0659000c0c0f5442c040c9070450780601e41c03601c1200204004035a0000d00d502c46140b00f80c9980e9040341070301042540341c0d01d0400910444000c64141008645060540c0c4100a80501302452a0940340c038041c2081e282c0014030329015a2002008100c030070702d03052149078448001c0b00900700303a9050600c014514442d40c0811881640c503174640c900c206009001c01c0c480c410030481c08200100500c407411000d00307400f03101544500c0851130034542080c4c021444554075042e580246142c0140704d055 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 693420323 1250 693419073 693419093
    0xd030519020c0f072418121e150e01050412080a29010206010f0608060402070c05040f090b0601030e030324060705030310050103060b073e030c04090807 67
    0x25050142c491410b07881d482083c14020000904411450500460460501c44000a070408011000c00000d0300c020380e000400c2054100170780c2d003045100c40d48102c070740c281108502e40341180c0d50300b0750303070003000c0d540801c90141800b03203044981c0d64007407141560000d00c25003210021540a0540000100742085451041c007115512801940d000200c0040d19035a200c80c4600d40c81410082e9030a401006983e980c04001d5140104020f07525006151706086000b049420044c1c012405030780c0120351032042007448501c0501421000d001007004080c00c10780c507c054600c0340c070280d51400118000c50a0f5502c07034000d18080300d2001c0015840c5440e0510010008402800030110a1007031003148000c641c0e840b002400e1541c09034005546a040c81442070f04855142d0b80018185440c00004000008103041522400e40d0410074929082c18149482d01c80300582020701c3e00c4036100e107428207035450078411143d20040b078284c00b103841d004d250714244012112180c801400000090015a0000d18000d076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 693421573 1250 693420323 693420337
    0x121e190c0305042705090102040614070201120f1a0102060601090302010c08091c05010f0501051305150306010f09150608010b0f120a1a220b010918020c0d03051902 72
    0x5000d510f010741d40c40c050540030761091810790707090441007030902a06003d80500d03a040380078440218905450400090100c01031804c0e02103188501140c5e040a5a00581104410300c0c20100c041c0f04080c441030080004005000302010b44006840300d140640d440018410710581c4180c4610f0401411a0010750765051988012290742c002000048055107903100020f119051690642102002624000c0d0948421400d802141c1d07107064010096a518561050a87c1402c1000003031944c594180c1040c0c1c201c60004a01c0d018442d640c00040c940e0f11140840e0125201603004100c0c800c5000390640440d9003d01c50030001440c140014080343c1c0c2a08000c00f401084040014a440115010440b1441040720121744207640c5e440c4e10402a80821030700d45080d003088440390b0501030300300c8804101200d144c1c0e1501416660300c401603000c0c0d0203515034802a01c02c4641d0b60544040070000351002c0e43c0440340302d441034000d04155102d00c60180c000d01d40500506651446484501103c4d68000d40080b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 693422823 1250 693421573 693421577
    0x90a0e0d020f060601141303030818160e04150542010509010908301e090301200a09060503100b0d0609020d0e4803121e190c03 56
    0x1f28112010720803048038011440380d00d40710001e00d0002c403a082c1e8680d60b400580700da0b4105202e1180d03440395200c420380540d4a803c00b030124035100d508102c5160071400c2c806c035140a10344000e004110705406402d49046005c0c0f0b451458145203401140c0110b0130065001c070b080d004520715200c50b0342c0140064008150103152840c045076840c0e02e03031440c0002a104000c1d0140110784400200003a40c2400c1401440e041134443c42c01c0f0000441495000790182d61001e605c60124000455035401c0d0050060440342c081d50bd1441100382c2d040c8080790340244040d42c08555424000650b4601520a69100314003d0b2103e60005203000c1c90b0341940d41c4074828442d9910b94494000c40c0000c1148042c001e00d040503031001803d01c852442c154500300c2c68660411440b420007200b5004540c110002642124040c180c3c1c46222114401c0244d110120501d1a9854054010f002e0881c014081c00b030b01c0813401010381c82c0d002060700040080c0c0d80c8688200c0c0070358602c1c202c0c855802e050140040e840c006c1d11074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 693424073 1250 693422823 693422827
    0x50a0b2a0f070b011215021c0b061308010203090c030d081801020d0e0c04200405040e0307020607080a090609120318150201020a0305240111010b090a0e0d020f06060114 74
    0x1907583c0008030000341c203d601d10412103131402c0c0c10301854491300051007040c12011850401c41e009400d900c40704d28050103000c140c685024140c1c076201e0000384c90383c030451320229249040c1c4441e00326001c0d42046404401e14401d928100e0101c0c0307400076110348840d502c0d03202c64202e6260401e02c1800d5500310b40101e449907400f00000081d203202c80c81103070690340040c2c020f0800d11000301c0801c4103480e140c034101641d5103910754200441d01085002c89045034402c890029018407d00034060960091410107544110702060f50002e00030f19000030a000c12080e5210404a515891f056030f03505140e0007a034603040701c6103000304002400b50255020621150031801121035071200074200c0c00d81264000c1b001070b5000b01d503400c130481c0c05000e115040101c00d10020108011f020407452a07800c140040f034100039200700001d842c2d501c29031206043d0718014011480524200200c080501114504000c89126241448203940e00c04100700310301400200250079541c40d8000110f030400b01d00d0801101540341 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 693425323 1250 693424073 693424087
    0xf010c050102040609060e0906281a1b071a07030318110a15200c0a08032d0a0e01050f0304050a0209010503010905060105010e150c0d03060f0605031308090d050a0b2a0f 74
    0xb03202c4414200c1814030380c40a41d0742c0c1440d003008101005600213343c080d80001000e0180c80212482d15540c40b0758200040e44400e0a410110b000d050789000d446008220180d04800b404940601c3c5244a04142e40300310083e07a44001000107041800505000100b0144030110521403505100400800c44800c4400140340007000584d810300359030003104150f0002945104480404450f80760058203812030740300c806075003002507103071307104860080b410031090307101c04042d582c000c8041e80e002c0000c40044a40740d2400340b815542c0c81d800788100780c1c0705c0c201c42400002c8034501406aa0001540240a0249a441c043c010764912109142d07081e407250b400400f070f090180012028044101c40c03040201807030b81d0190300140403103650b0707000010002c0d0b900340c0a11400d0340200131260071010f041228502081541040d001030b00611030040c3d80072122482120a000d0b000a6000178940982091505034840d60703101105600c509212804014012a01841c030f07001c10303405805040403801c0010300e0565 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 693426573 1250 693425323 693425339
    0xb07110a03061805190804050415080307030314130812060301020f070f0c0b03010302060307050c010902040c020c03010c030b0a050105031b03070f020601091104050f010c050102040609060e090628 86
    0x20703031101c00070a150f80e4019406221042000f4041d908500c2e140440c0840e8613117903030449120b14040c25000d140c903110f19040d072009600d036440045c40300c0d80c10740791150f0311490010050b01024003442c00b0188000c002c5841d10080c6a05041c142c0c2e48034441ca86042c00c010b9030409031000092040390305542c284200207801102c0030060000e1131007001002c25000080c501080403085c070340c105541d500020b000510042e1958401c480d04645d1908141c1d071911000320342a4050201190f0003900241010307011408a80c00054603228000110000d002e00820030074218221048420203070351000b1064020845035000d48001c40d0808004041d07404290340034200b03400d01d60b00503143c6000080d00341c1d21004006505000081c05824401428000c8045d0215804254015401070314032546007071180d070505138040c03100c01522a034030000954460b83e0b0f0300005041c45655104200228000884400c12841e04295440c424540104107603840250440303240d03911004550418a02019401d02054100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 693427823 1250 693426573 693426581
    0x60e0c03100605180702030a11011b0507050c0409080a0309060b0d080405090106020c010c0b090a0b070f09051f03180c0e06011209200d14012003010b07110a0306 71
    0x2034032007400411141d18040602515064242c880ba07101e000aa050103081a404012201c4801107450503c901214070305140740141014500e009000301845000042c50b07800c00060828980903c0681d04081c907003c080c48150703800000300500590007003000404940c00395000141c03441c028000001e8a03080c401c04100703240c552281c252004440031a0030004c46c45d083ca60940502040c3c0301810000031080d001804014100f103005040c0c901010019155040c01c010f444506900904801c50303d00f0411006004103100704900c0380028140b11b00030465082c240c003000d001e080300005400c0129040807088005010304210440c1100b410818000810902c680c0e0340003400d440071000c3c24604000001603d003ea4003816894003505008100c800319403646c0480940c1803202d01150034008084000842c801c1c60440007c0c400800011034541c024015030010402d10310035644c11900d0301180f5000c0942d070109101c1d00c03400c1c400401c07001000400b601c0140e0074015002e860f1054161320703566614240c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 693429073 1250 693427823 693427843
    0x3171821040f0b0c0c0a350102030403080f01050f06072003070e01052d010c080904020a0819050108030417010207081602040605040e07090203100e0c0a09150c060e0c03 74
    0x40c03004a00c0202c90316060084115505040781e03d4900070340340139150f01e801807104987c84520f88500c40801d203070740102c5d00b80c00084200040215582d01c2d00303207009081c0c107206503180b1001c0b800100000c10f0b00e0400c2c0c1d28528160a004110134249030351340d960604080a030902d1a402224041c28040380e640f41080355030041c101c2d01541d000158140018812000030f440483c0030807282c0180310703520f41d8602181c00c65000c0828a00041c82642d01c0c1400801841007120a40c0c020384001800d880e00c0d80c0c49101a8054000002200b003c1c0c001000f100017030714800e000d105200e4204010802840d201d1000900f07082c001070002506000e20340d120620304ea00000d01e04660180342c10b00c58011464903110f0301014040446d400c01107034640088641d601c400e6405aa19195400400f05a141c00c00101210040001c501209071500e003161200030641c100d1240c11004c03800040d1302060000b981440d259a42503239540b000c18100c8a5120b0034041c0084c12031000c1540229140040c041e04c0c1030100c0942 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 693430323 1250 693429073 693429089
    0x8071709070f060f02010c1404050405151f080112020a1502070902030123010216090213030b04050a053003041b151b080702092203171821040f 63
    0x3020301500304c0a030a54221011490802602c0441100035001840c10340d03041e41c00940f0001101c0d620721038068813246410050f03030390040b01e203480c0041c030100b0683e0101643c58103540319403480c2d036607500800560101a8009601105040c0306002d00c0000c01c02d4500600503d20440ba4110340d03441a0704122b1b4021b07006526500018101808103120298000c00d000100f84014a14400034448120008041d07018114005070001841d80b002003001ca2810007031504403061144a00300351502036511042e60741d0440300c0b070042020010400c180b440c8a480804500c00404060004140c030b40c40c0c565000030005c0f2016614a420038050340543c503154005400921020080100549130151090000180b441d03116060046564001111182640c03c1c80741d05a415191907180d24000c0300b0582140e80c0201071002d0801c1004040c5035201c42c0f0800341c0c1005031903091668031425020031000007120b40440c1664010b00c0121900d034203030045400100300c03041c1043d0138141c451481c840c030100300340d1000c0c407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 693431573 1250 693430323 693430337
    0x602070305180105090112051308121605030912030406090b040f02092a0f09030f010b01201506031009030216090c080117030403080406120c08071709070f06 69
    0x660703444010380c2c0304651082400e09030300342050350000a148207510240103039a1900c40010958007902500d0410701c1310391040c1040d031101d00440b0511500300c001c546602e02042da4031044030300c041c00386045078000e1314030401a01d6880b162100542040d44042d0085806582d02c19910001c40d445034006da000c1e80c4a141c000034070802c98010444200800340448032a09805840c001c59010784c1c500707414040d90f0781c000300707529105203040401c098081c0c0d1740ea150309406100c6034081d06801c1075115550840c401d888070004001c203484240030740998204007020a520100c50428540401c507280c6510000c000e04072282d604001d8070310301c195030100b82c045002d40d10540304c030301c04103505401e680c0190a03420000c001003010490300038001a01841454425002d18900118190051003103402441c0c010305202d65031a035401000b00031145148900d4062858203521960641c8184003850207202d0350b90380d0003003c07600311f10104801c41c0301808412552107221760025121101d6640304e4000c01d0b103915010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 693432823 1250 693431573 693431587
    0xc0e04060b0307170a170d021909090b0f0108130203010c0c0203010509010c140705070f180e01110301090e0f0f0a05071e0312110a1b1a0f090a030602070305 69
    0x40c5045602e800812400d4411313080b00b01a40740020b036821843c2e40003400c00750445940440014544514030921050b10300005081c00d4200068803201150b6045980703040400d0381e50f50140003102c004408180d4445000101090650b00c55451582c00120620f0141d919030101c3c0d00003421241030b5104080840d00d9401c1c508103600e82031040c1640076030844024880c410084900400b0b0b11307803c4406802c200380218907c0300340a0100701000c05040c02c014001d200c5600d4114006020500c5920501c82c24103005184003110018041c0510b4010340010b0700b03042d07900307242040300a01680503002000c2d01c29081525a1404100070305080008002c02401c2b4400460505901300398858000003888903040320032402c541080f00c91142101c2d00444d40940c116448a0210b4184856080040c80c5204801a10042c0303c4034600c01c80f035100d440401c40d44030750b0762048000300b00000b51281c00f0042c01305000f91600e6003a0380c03000b0911410010880d502c074503203a0781d441041342c11901007a40000d1003c2600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 693434073 1250 693432823 693432829
    0xb03010e0d0f140c06040b0702151015230306040b04020d05011e150807050d091407080c0603160207080703030503010f05010c020d0312061d1b040308160c0e04060b 72
    0x3c190300852000c000346815020744c1d40e15940c9034040d01c010014145c101c0080e200602c00c0c0001198110b1910404665081a400928985085d07010b511081b407100d45580c1081409002840e12079440d581c03800c01001c100030300307019035608000c3c0102d07082a111a01c8600c0c59a540c0300a01c1c800c0c611100001e21035040070000c001c0c114000390280706003c1d4044003404031800510381c80c0c40040080c608615203641d1007404139070380d01500780d00c0900f10307003014904420424415103402c41c1440000c12111550343d03d00d070072941c4181a41c00207401800800218030400310100c514401e55006004907080240d49a0f8070b2131602d440d903032098001440200041c0042d00f960381852005000919001c0400080764000401750305005500a0034001d0301e50790200f504005400c08001440071a1079048080400b0070b0715402d803801180d0aa0100303543e00c1c01d0701c0c503c59841042e201a00e030018081d50402c4101421131100700341c0301d281520040392081d000940c40183c0540640b10f64410540411440125814 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 693435323 1250 693434073 693434087
    0x501090e0304030b130c180b0405070318031211040e04120c0206120604060b03011706090f1c02160603090b16141602100206010e0906040201120b03010e0d0f 69
    0xc51060340d003040000700046000040785907000010581c4401c61001e01d40303425545100030340d00105a580d2601d0f60700520700c900758040140e810060700c00b480b595903198400c9084034a4543d0f1540c1c40142c0c002c100003c80c0c41108106140d201841c2d00154881554001320041d42180e44050307400d514030000c0004010110001c158103507040d00b84a044108250b0000b51107000c1c901d1039642e504e0004000039029038a5070054001000c4a104859a950312001400000141d494030000e1910a01c801306800303100000e1151000c8415a002d1b0910b0700e440c0805c40d03120705085002c2c004500c610b0300d03900250303822407070782800a140c5030302c0004000b0381e5032034030002c4030000501c000c613480700d40c80e208110700f0340041502e80420b40140601755542c01d00501e0034170044101101039001490580c5c411826074001800d5410384001601c480e403507507140d0045541ea2502118000d001600c5201015119100c941020b4541c4030014004105e180e1144955840c0048124035440042c1001c2102d2011b02c1d08504 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 693436573 1250 693435323 693435341
    0xc080903030729040c0b1602090108010c0306290f070b1f090e0c13090f0b09010501050a060f03020310080a0f0b07030b0102070b181306081009020315090c0d06050109 73
    0x4001c00042c80c0517194004100f08600c16010b0095000509042c6480ca84440041c4603500820020a9507120300310719008182c0e095558011034507005000c034002c01c6400510014089400201103055064a020030407030300304800030521110203101c008002000040c0340c1384a8121382518261109440b5011064a032265203c1c0781da0524003142d140030280003180c0340c42900f006803110350200140e41100d4008040c04d040107003501480c10720702001c0000c540d20305070082188200900599807200200112011305101304808145a4100d200109000c5d801a40d44081c01440300c0f05141e0b90f42a000b4103006040008561b401c481102005c1084041d0002540000312031400704600a010000030b540c823601400364804400700401e0203401d0305004200c42c1180a8040d00480e60000e00c04200d0000e017443e40520744050040c0d510000b041d003458030a041c0103940040040500c001c00784c11f002c454801c003921400d4a40031341c001d142240d848410000c640d15110304400141d9601d481404002c60701104c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 693437823 1250 693436573 693436643
    0x60a020306011812240c03060f050405090a030e180106051b060c04090e01021308030409061401080412020a0b13110a1d10050a0e0118090507060c0809030307 69
    0x140c001d00c00e224004d03444403050b031751100c0141d100d0420016992190f60310b03030421000860a001400c0b24140d45504004200c61031080c8004170315841d802040f090b01d01c101d03558820359000f00080030100b07129800302e03007125501500041c64000400c1e01c180003401c09030071000100700b0025214040c420030001420040b42c2a8002c0c0006092604010030140318034824008425107500d15580e17081000e50440341041804650f100703689603101003207600c03500584115010580750100025000784840200f00c0e10000503950210715603241d07a611800311082840384011445011800c000192050038154000c0d440b111440340c440b80c5619000480414000129000340d111003010020001c50000d41c110015440040ca00e541c0d80304c0d500c00d44500080d5024039441002c0007800203062900c8440705040e94043d84503a854034034007045140c2960f114800041070b0b948240000c0000c03610512990007000c3c40b80d41074a20f420b1100380004c0ca545c00004050f02c00e10a904e11641c01c0d004100c054224800c215 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 693439073 1250 693437823 693437867
    0x6040b0604140102100c09080d02012a05070605191d031911060a140106020c01090605030903041e090b0d050a03080c0904091412041202040c0c0203060a02030601 71
    0x2100106219000301c1c41110411042042d000700c040c1e0080c00500390b00fa5510750100403804041400030b141502e0780c840e001690117500e8200040500c1800b40d004070360714212140480106041ca480d04072161030b0000c1040200c21b10200c0c0000d80076008642c081d50303070b0241124038031f10300c220a441214143c00e00700700c3d00034a901c101c0b1001d89011041e11203a0400f60071840741c9810b14103007900d480c03000010018884c000e51080241034100c903401008440c08520343d03006c0740ea1700c81d80140d954200426226003c2441074200b081458450002542c1c04100c0d001030301e00702030303a60b4034081e401641c481104041c14034640060008d006580b2450a0a070000c448602c1d4440480c1c031803546544500f08003508100760072000800c0783c7c0b01c0d030044031016080504100f0050a590414407009081030354408e543d0302900b08040c1c203009100d000d59003a1074500c0c00d5950034030042d0b800c200c010b107000d03141041440180b540501c05650240087d81c0304407000517000d40d1b00d04d44400010003000003072210f0006d02c0340c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 693440323 1250 693439073 693439091
    0xf0714030601050415050909011410050303090904031e02030c0607210902210604022806110a020303130e0a0207200310061e05040204030b0613020c12120604 69
    0xc00601241107035000c0e00d00240040c080e43c0c0c81c1110820507000181c102600344180081036038158450b50007991901140c80b856102c0649404507500140f0503150b01d54414058400545002c0e050250001e2027820009281140282c0c05041071864600d8100560004520301540d0102440074a47c002d4403440e05101d161108450840c050a08181d1685101e80e2102c0c100110740b00e141c4d0052280200030428150f00c1d0800e8a180d5803488100d80490084039a1b44c40034003003c080591902d0074200d564940c02100d41072607011501c4141c0740c0800300c1c1c0c0340b01b800710307040151300c1c2030000b4400241208030600030395007005031142c42d00102400200a844c4100700f10404100d45041014945615805501c015020302c000207150604200700d1a0b52186041000184d103075981c03040050b12400680e083d030005581f178040000702d000c2e5200140c0314549100005085141c81c01403a81c0351420340314010708111451307280510300011130301c1c0e60100e080d0005065490074030041701c45038046011075041c0030b0150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 693441573 1250 693440323 693440329
    0x32007031e080c1b0714031011030a1503080a03061a030910050415050109020306010e0f1003050402030a1b0609120c14060f0705030316080403020d0c02011101020c0f0714 75
    0x402003226010308004140e8034503d2641d9007100e54030750050f00845d641c0d1502c80103030b811a2140703034504a00c00d1241e090401096042130180c500710044541405096690700d4a03240c000d002c0903900c003030b203020000401000064440f4003402d0003000550340001c0b0107003446400c0c410003442010780c0024450030b004001d1507800018400c600c808106501164688071450400d4405103070944001009040900100d1190309960185101d20826614080408810030030700c41601c070405247c603003143c401c81d04144028025080980c0162001c4c04031485007084d51202191002c603000680c1145020000403c860765001d00030902a008894140b128074001b42c1c6c44040d002c132244200d60086500e1219141160350711000d94104e05d906804855a61400c0c2c60220303140c0c0d0045405c120b242c1c003103000711114a44580500c0744902d82c550001d00800f00c2c07101040d00e94a28800c4100c0c10040c0c0e1074030184075600280003402441030f010300100407401c2d41100c813908081d1150401c20241c8803d100d0520f0640d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 693442823 1250 693441573 693441587
    0x60901030503160305040509190c0504060c230a060f110f0a03240f230603010b0f090a08012c1e030708040e0403030b091b030601032007031e 62
    0x83d058006201400e4035131318090380d0341e004a0f4031165000e141c500c108000c2d90011050380500000c09881088203008120040d91540514020540018207105098000450030100c007080c0719202c403200f44c5030804141c0c540749071000480044070f490340ca8010400581c0818000c104051003141913850600b0482d0a0f110501d0103070603c03650415840e01e81401304031880c15210004050305074100d50049840d045400320024680c424103400074100d108195078a001e1801a03481ca8100401c5a450341e4684842d4041a4106071202c04000508020503101a55400c242600401c0a800003044006040342c610311451182200070702c6001c00d06969110481021824402d2000c0f8500401d01a08001c14007d155004e0294000d0011100280108800700e0b0403001d60f21980c880d6806000c1c8142e50014412100c8003a2030103001c00306040c400707180c000140005107030300c5441850001560b242644907003d0400503400d0814800f40c000a6003400e241e8004030085800e8110540a00401c5403814020025 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 693444073 1250 693442823 693442837
    0x30c010e010815100201021e16020603070509062a011b110705060d0b100e0d0209040206130303120b0303030f161e05031909050a0303150302130212060901030503 71
    0xb051000000f90310858020400c8018840a003002c204260030000190003035014620800100d40c2d11907042c040054044d040742e07602e010307000040b12000031690070310029800c0517104500f40700c0180a8582c49803540320180010254a5501c0b01c075040254040403401d5013003101010490741014034900a884d050340901c03552401d28501036000000c6031413541d0400308641c200980c002c9000a0030708000007144c103e81c000d5141160b00e40c5205844803016a244030080344415000b2a0180070b65005d842c2030403400358403070300207000c040c40c00c041c4522415902da05600f00302c000c40c403090b80454154905100300d40204006500031844c5041601101d205c2c443d005261220380032601c01f03c1d01d0900d01c54100249404904914640024203c15000e40750b908215107280400304e1600c0c001500f404c0074020780e074440b5045000f070404d44a072903c2c1200501102c002e181c030340d01050304001005841c1c195074000401c0c0310103001a140d0080040030342e83c101c0f02401507442103120b0030040c00812408001c032440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 693445323 1250 693444073 693444077
    0x709050a062303070318060c0908060f010e06060c0a0b0f010b0f070b0403021911030c0607200609030a0c17031306120920100302041a0c0a0501090c14030c010e01 71
    0x5139911280c045010b00300300d00b00d5500185a018040041280f55000040011b104d621001c440649640d0300075560348040710740313084150031403004200c0c44294080e101d030403007000340c08180380c9041c2c201d0003880e250b425082202c66480c0c0e50100152107096918050242c85841405803524000c040d060b9990b004010018050341648c0d8041400c06008102914103030f032540003d21846460303070400082c15507826500382d000780100801040103107415421101321a5120b5680c14000c112252a00203000b004001c1e16001030b800c10524281d60b07000c100ca692202c1c46424054140303400c004829092583c00c480d5101c0135407083c000801c0c038a4009801d83e068860132b180108503042d00e20070a0010300040b00000c2c2080f18540601070b0301b400d01010b0b400321184140c91aa090075400c81c4110100d100301d12504610b1381c0304214100c00081403c0081112800480c122000040580c81e00c508440c5a684210780e001100c400401221216040b1040b0750302c01103029080c000342c01d80c00a4549a145205141 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 693446573 1250 693445323 693445327
    0x60a080c090604021e070c090506010c030e010903060227060703020303070c06091208011502070e1914010602012307080708040515070f17040203120a170709050a0623 73
    0x51910386038140e80d2500c1c2080c107004139005c0980041c0c0065031000c00244c80d1540300c42d40c00f160b501c0700350203000d011f42c5040e0750322500005e03607440807601040540041ca04001c41080004041440c44c00500031620745100c0c3c1d44440d521003c020102500621003c0c0c1c041e144c2442080301003034001c803c1e81e80c800428102043c02d40410f1500d03100500c191207000700354644016282ea112540075900905031b407802c1e01c408a11654400c010780c0d5510382482800040b00c0c50400068a500c111003044407a4011140080b5540c500e41aa01d040d190090308484010b0799504d2004015030040c034101c848440c2941135121490901200040804000610220a000013140030908104040103400210b400650702c03200d80d401d2050700200100b0144c0501e10015074403542004a42114a901600a950003001415501c1a4012030b00c556003000f404502880068002481c1703094004503414802d0201e55100e240ca10b040000700140c01e40c10390403131800c103c0030204290845107042d825010684a035461b441d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 693447823 1250 693446573 693446581
    0x3071d012607060329091506070204090f0203062d18010c08191103011e03050a0503030601091d0a15090f09150c02100f0b090108030a0206060a080c09 66
    0x1c41d9030308894910044601c1400c900043d07142c1e05038400907003141011034440c08030110030b0000340103841829205c1c0d44849a40e003c1a6902c5000e50b9007580264060241030500b0b07855000034040b80d614400640e9400702c8100b001045207801c0c801c050b40242d116401822580e40100c903407030000300c1c040e450400302a42c8000300c0c24241c2c005104044100b000d0b0000d002103c0340c3c24004060040954101210361030405807000d14401c5070181c6440d0320301c2d0040c094150f03880c03c44040409440c442c204044d2076004000440401c01c203001003a00580603000a5649080200006010b041c0d140c0c0503c5480c00c0401307024091500003003840d50400520580461240b501d84421200c88120794091007165103080008500303402c0c039811a14100740070326400b025401301000f02d10103950b800c410020041c1c0100c0c860701d1501481e60b1041d12030b88031884000510000c1000450807400e003e82244110b0342c4040b80d00c0c0760f125030400c03d681c0e00139026070354030300c2c0c0d10f10f040404d598030145c00300c0492007911860005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 693449073 1250 693447823 693447869
    0x1905030f030c0d031a060304080901030b10021009020a150207060e1806010507051e0706090b030c04120c08100504051e030301050d1119030308150f090a020702040c02030903071d01 79
    0x5040e030b45c80c0c020142540d03800c1c10319120255500100240d4003080c1450303a0b01d041c5141c4504100d43c1e20300150050940d000c00c4550300001417440c128101d82c4810700c0c0303801050110040701c1e602c034194407036002440b0035401d119000d800503403800d80da2403003070b04e02c0c3c1c5150102800c4841c4546c1c20050a003401622042c6c54548141003040c078003404c0a52240708040600e0340e0720002a0700c0202e84135074a8400d40340740c42c2d11003040244421540c404400c10300300005c00421002c00b401440160055020940351f039200e907503150501d0400f6000110181d1940c051005002007840042e884100407001c11402e2130750210708545902051185e50b2194610500e0001804410f420303042004000a1001191104080384842091074a0000f90006204400015480801c038200907001d103000400c8081030076000740810050b800010041d02002d5002e00041005031100d00031120241103c1d0003450301c42144509143c9415000e41c000150010030200c41907800c1c0a40441034151400560b5203c80c101e112946 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 693450323 1250 693449073 693449111
    0x20d0b03010e061602011b050c0f06040b040b0105061303020105090303071e030339120f060503010b06071a04170c07030c0605030108100e010b1905030f030c0d03 71
    0x251500355007841860b100740100070945a114000440d0104412642c0300c0e012400c0b90003010036034040351505980b2105080c014000b412481422400303c4607220b90034449a402c008003980d0031100c1409030010f0100700020a01014058182030b1240340c14441c0c52104081d201c8000c0c40064144200091959080c1d1000c0c0100e40041d134000b2189644001090040f140740798110400b42e0000c1e01c1d1007035103c009011000e51402a03048004450342e0742030f4003031100740d0000703c000ca0003043c41580d00c0490310226250152250740d41908000080c40d616010070725081d41c106600031380c0f00760410025100012001c1c0014400201142d440203c0c2d90364525011141d554854007803545075001040821085e0000980790302500c0c80360000c000703016035986017907600780000e003c1e220440d08070601e040b10001c9581d001481980f514000807074110315250220750419240310642c8200c0303c03141c03c184101c0c207040008403825001d9500075494244000c1c551512481002415002c01da00c8108094050550308a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 693451573 1250 693450323 693450341
    0xf180a1208040905100e01031101120606021b0907050a03050406060b0f0c0709050121060617030c011b05070f050a060513030206060118150c08040e100b0319020d 71
    0x506040004014100888070350414400c4405407400c080018525050782907a050481e02d14805c284c189034250307071300d240703440044220181c100a5070a070342103e0011540208c8006280603009040303041284110040c1140b51405503600500210040c00301c802d6008084030076110740741c5000038039a00d40b45410000f800c41e660040c2c988003c04903045500600c5036004140e4010380c84200c0b0a102d0380c0750000300036034000348240d201c5810308441e00c48420510210701c4140c135100d03600001d066600c844010100c050381180014456001044581030b65034240f280380000f80c1c9440b052403049046120081032881104001480002d0192140081103410403400c1c00407a8044402d2103140f4144e25803c1e41c1e001107079000d50040c8220000f240040d405a201c00b681500000d281c60841c0382444802040b281d00d000541040211001603007002c510030303102420151480c00c00300031050809400c2420125240e4000d201c10410070001d00058000d207070b1201c181c90300107600c05615040c3e0400a2402403002e14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 693452823 1250 693451573 693451589
    0x9010e0303030a0c0801080606010f110c10080105540a200a020c010e030f100504111e100309061e050c18090411030f011e020f180a 58
    0x1005003da49807031904000e01926080c1e035022620780e607400310a952407078180c0d48140415903071022007207528864070400c1d44010142c804c40e0801d921181c045600e0450710404400022030400050040b40b81601c0303034035000449460100040c2c10840d1f2101e43c00b40aa01e1120b52482c07460b80810b094541b803d103c1d541240d44200880305900c0c0500c580740c00380140000d0724040c001c44418101504244200b0f55000030019801048510302a0303006480304c02c505c03813915070703d0703c03581d41e004042200030001401c0302d02e001e0b08080791508007864503a0071501090401e0f4450345011a60b1800c00820b00a012180302c8125811907014440e45000c1d00107184401002d08182c0c1030041c4046400386040711150036004080c02003100e0341e503c04030500c03540142d464181441040351410159880c040c001c0070b40040c00380700240d54400d80240080d04d4005204e100c054180d444441048003081e42e00081c0d808a52041015440d21940502c6070305140304d550891164913548803050b40c00c94a6002c12100940088 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 693454073 1250 693452823 693452827
    0x1403060d0c0b071e030e09101502030705070806090a0b1e0c0a0e011b020d0804090e0d140906071203060305030d06080c040b0906090a0f0501270608030a030209010e0303 74
    0x55080c440e4030f510404081d5a5801c1c840000000e20002d1050084031640540ea0400c1d94280710040201898014100c2110b1160208011808441b401c50898194090790011503441c02b85240050410070a60700000b0306421070410040040300c0400d40e001d485501013403c84490f916103c83d001910001b21b40800b0258201e0704101503500488002d244070580c50711045000200c050044405094a40b4034040e031fa0b009034450801030400d044039200703440c803c14071340e401c0071380f0340d1004000c0b42c0c0c42c040c104a2680c0941c0d06800c5441c4c20001e444d101d05010080d50345409540c10200390144128070f1b00034050302d1181c400f1003141d44290312110140d640708058990307441098200300080d10b01402400814091031007204502d180a100326901c0301c1c40941480c003541c3d110b500308510b01c3d0000307241c0c2035440e40792400070075189568440c3c2400382409a10152070814644c40080c0380504c61035a00740c16510b40345090000d40c1000003507660002280c500982c0d00c88108004982e00302c5401495a054480 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 693455323 1250 693454073 693454079
    0x13050918011404061b05040902070503070b0a02070b01080109020904231015240e0a0f08030d0f0207110f01020a06050108030d050912090f0a03080307020109060c020a031403060d0c 79
    0x503002d0440e0080d8003c400602003075120003445005012a2003180300400ca0401c000c110300506038001c1c0048500034801d5038140340180d2110300d4054011281c2e1844070380c0c002120400c0000c4986528050f01002000300302c0032586901060b156607002d0000b604032014141d0144d22040d50783e40500700385c03d8403c10354211952004c4504c02500c00e411101a044c880420003041038001e542d4111390700e0080e0b4007001000b5141d07400585444203014500d5420010301d20020a035440482020001815044006c0d0354800030b5450600855075241000302105004210b8000441c0880d180307104114000c94080c03070400c10000051385801c080042c0100032500701800041c00f11408005010a40b00c20310050203e592155800c1d901ca1030800012174501c141445000b5081c01c110701041880703100a071681038002d449480d150443e4008881703140040c1c8d1603003444400c01036140035001d4010030303d000806100c58030303a80142c603107c081c10f0b00c003500036008400134031a562071910840700c282e002a800010340761 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 693456573 1250 693455323 693455351
    0x70f14040b10030903030b330f04030c06031109010509150d1d1b030327130213053c1c1b0e0105090402031608030a030609021305091801 60
    0x28020b44d054022a103040c2c400211400c0403c0031090400c12001c034109a0580141104040000f5016120781080140042840c0076000c00007003000d9409483d661031103c0c07618800605031a08034200c90740c01a4140400c0c00d883c1d800c081554122030741140e405c4200ca0300d000940300c440c002d4105c2140001d04141c01130030b423900303102d8861503403c0014041d0384800318821440c59410103c400c43c180c155208002c0381042c0b5000740d0304054170251075055062041c5441d0002400c8683c084481040c4581c0002c00305a4000c2000481d0001d19064400d104c2c10342c0f007240340c00043c0391540103510f4100000c0c00151982405072100a50654000304140c2c000904180c0c1891004015102100c080511221003c1c442c0c0e4503c03502d60480b8070401c90546103030700f814107100c0980000340003260580304405000f12044070102ca41801345c51028029522050003420003019141da580c0f1940050303104001d8800c0004001901d0000e64905a40f171140070384400c20b440b4100d21b45141c20744d00300e502c2c001080010768 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 693457823 1250 693456573 693456581
    0x3130f051c0230041203211a0a0605122203050a0e120c04090606090e0c0a080105190e0a0204060b03070e12060103021c0b27030a0c110a0b0d05040c08070f14040b1003 73
    0x3001084c450704040348c1c5102401481c0d50386001d0700010940603c4440c2c1170704032031300107580d0000101c202d03190b01d0210300442079841c185040e000c9010400c0070900c24645540185080e282e040212100c002074005207148580f03905034051034034059034a8295030000d10040d030304034000400c40b50b00104101d0080b00d040d2a20781c030074001c01a102e180003c00000341c05105000d042e01a00702d0121540100000040701d000801c0c0610303032603080703000d1100800301503a500d00c511002015841c0070b056580c42c00000003046405020384e00d611925648020704040000003401505481d4107441246aa40340c0100d8108044c60780340300105000002010041c0f8610031b0440307445c25440300702c090090382e0110a54152039019486814000a48a01025010800396502d15415520281c07a100d07c040d00d90003401c14a500c010703447d8030a2915402800100817103d4145802444080c0142001506202000001100501c01c0116282600000c94034641d030700c1e0322016510400500d401e05040d941c02d00a0f01030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 693459073 1250 693457823 693457841
    0xc030d060512070308040e15180105010810120602090604120303090201090902190f11010207051612050706081e011404050c03130f051c023004120321 66
    0x35840c080b00300046060024841c82500d81c4403031000c1c200307400c0601d0b8502c0c0d00300040816800c4103110040301d6071625072040204428840d17285461496041c0070000d000c030399015104803100d0450000070400f4080d4007078041c020300e6010501683d01c0c5110382c0001c10501607074001d012556403201c190005c26416501c0f142c80036200781c03105070180703551720350541c00c81c01622070140803051908552519280b103505100c0e00d40355a800c0075108041c40180c0c0c90700721b8000300401c071482c0c5d2100102e101000021041c090040c0426143d01e802c4418a80e106d42d1180c100b032213078405000c00310300402e00741250365000d0480903003000400b0303216603910180d1714210182800c841d07020343d2501e0086100b001741203017106d00c00c0240522802e5140c000e03650f0040c600c04003642c1a106c500400f95042c006900500240540141650003800818200b06140c42d60300400d4070350201440c40d03402c0241e100a03003007041d1012140c0343c145201e0b80c0d60311800e041e6200b010700801c460b4900c8411280603003c00c02603004243c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 693460323 1250 693459073 693459079
    0x4090c080f03030412020a110d020a030605090a060f0e030a08040809030a060c23030601201618060302010c020f241e070f0f1a0a050403081e0103170c030d0605 70
    0xc1703205500040e0780700d0107210005080b919000009240f00e09111015207601d44c4003a0006181558a46446041358826260207080c0d8129142e8003007400014000d2400012003c0f0041000a01c00400d20340c0c2c0b842011070080074400390304000380901002d0300684020020190903a005409240b44c2100140807125030100481c040c0841e05030440000c0690010a258980081c0e24503120040103684424502c4681c055a841900348075403444001d00c14441c0d05c040c4100c0c284291810110500e100303141e036650415006e840c1440400160f81c1c040000c2d00c140c0e0b0190f400d0580341030164042084103516005003800d01001e41d20f04000483c001c4010021154110501103821402d5001c42c41607110f0140c019243c20365a03c07202c2c000c12664034031035030113074440d821030403000c224070f8000c20131240304603401c2c0c00807a80c0b4000c02c0309164101413481d0788660401e1800e100d9610b42032601e41108010700005d401d41e8400d08010540100c4a0225954070340e0300c10803613444202045144000c5c0660303000d1140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 693461573 1250 693460323 693460343
    0x50f0a0305013b1b0406120812130f060c0c06091101020d022d070806070806090a020a020d14040504150513020c0d1214010b0309070e070c0204090c080f030304 70
    0x41059290200f0180e6800d801c0034000034038140c0f07580030003a614402e00b10ba101e6518100001c03100740c072000343d01c155031056003030075114201c680f18417170381080041c0b40200e200c0d00000d41000107111490306d00c11855201c0300001e8911303a1558120f40c41541b5400041007646000341c11000c0c00600c24074205408400d900715458551103031000c030784a40b4803070b1117401c0c1708a4020610f6000c0000d040c2e050140400d610031105680c0da52115a441d18505456000204130983d0911030b01d4101b0b26200c0e0f6100441c0401986440c1c00054000e54800e80ca481c1d0380308100c04401329030b1480101404940042c007004100f80300803826400c41d9042c03d4140d100b242d1144c01c0c00f941c41100d0414030700a0746d9a07044184003a0902500440382624a5440e01c0c1034406e040f56a004406150300e041001c01c0d02800040c0d168035181d02d89494902d1403c2c0640d007005580c80d4050042180203075000348940001a41038901080d021250303c0c24009141035078109400a002d50030090500c00b00000c0910b1141c1c1c002c4007824 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 693462823 1250 693461573 693461651
    0x603010b041b110321010e0109140f1003140106080f010501080c0105030c07080316030b0f0f150409020c0609061303050403030f020f160f05040501050604050f0a030501 74
    0xb156041c00040c00c05001d618034201a007806892401680030320101505c0c50300c21041d01e80d03010342104540c0b004040d20400c006109400e0a031258038090180c0311020800103140b152041e5520b8401007242d004c010040c00040d40c190000501d013401198803904661140c243e2452843c0a424140548001c500c500419100181030501416040700c8148029050318a500401120303154001801c281c010001013003850001480316000350310920514a001c1e00ba0700000e0b03002001e0360748064103640f040d440020300c6001941c40014126011f03104071080c0030b284100c520301995901842d4031030300b0300d1440421203201c54500401c000b0302c188004815200c01c0e90303500368201c0c14828201c0c0c000c3e000600130b00c0207000190052010754010642ca0044a01c500302074001c2c2868880c6201c40b480d8500f00540301003201121044001020300340c01c580900403076040c0701c0030407418025445058031072400d415a40000f500c50140490155411074020700039042d11468801c0e1120905200306c4c040200500c040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 693464073 1250 693462823 693462829
    0x1403160c14061b121b1204050c400f0501031101080603060f010308030a0e060403020d0305090c0616030e13140a02040302102307050a110109080d08040809060d050603010b 75
    0x4030031808006050320b00c607855169451074044c02c0c06841c105c1c0c1e0041000040380228240c3c0c4928460792250000342400d4000e076080c02050b06400541d032010309842806c01c5d070343c10442c11030010694249600c4a02c1c2c2130301d00c21414007901c020420000340034981000032091000c100b000c02c510381c03030a1322049401d0301c66500f496500c000840702000707503101030401480001c4d441e00c021604003201e07543c0030461400e059210350820a0a0784d040700943c0c010100340d00683c0d094011070303510081c5000079100d410004404200342c0d00c107003031190700200d00000443d81014041c0354108a03041c0003404052100484000d01e500070700c01c0300318a081c45034217000001d01c01541030086a040d02e0740a403407040305058081003911362500c1141030a00040b4012800e850b03c0c44120084e0130300d14000d000410704080070b402c000950310301e0825618100f003515041030181d1400012003417560012032519035440e5540781424842401015403041e03010070001003080d015402c641049001c2c074400c034001c0088041c11010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 693465323 1250 693464073 693464077
    0x30309023607051309050c071403090117100e19180318120605181b0a05030f0c060a0207090203070f020606010206220303020c0a1b061403160c14061b 66
    0x1c0c0e11600b84c02a042c811101e903608200e41003e0894507541c1000340c80e03519002d42c800d00c50000583c80d40b002c1b886600940c1c0c40509482c80c820340c4040d208541c141f407410205407031038038058460360746004404102400ea28686407004c0d810a02420003c0042e41002000d02185a0f1400d60004418a412028030000040903c088811414440018040c2a0368103c080c1038000e0129000322850400e2144030340c82030142c940421030f85100340000b50400342c04c0103240d01d00c5400c00740c02644880020900c801000032020302d960800c652243e00d5140c4e020040f8030348541c50304180314881c0040203200c48a03070002800340e100c612070707001d41d44036942d10703001241e03900c00864030b526400100f020001212811071211140c0b4501901e4094a403030409050a0f14007140c4807403c94114513441c0e5000c4000c5004114000904202d182c141c0e0a80090310a0902d107000190540d28110940b107640d14016014070044c084040d40303c0e110b1050103025083d219123919044030103c440e1040e81116583d40044001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 693466573 1250 693465323 693465337
    0x51207050d09170613062405180114060f070606030b0402011e0906110c0901030c080607020a0302060705091f031505041e230c0a02150603030703030902360705 70
    0x4001c01403561179088003001c000c40c081c0d040d602260b5030b01190f011709a0f940383d81c1a40035040130b0095115490700050050101008548848260b0f07180014040c0c00c25880000c4240d800c1111116181c1c231041010b01c88074810803000515081c40c021001040182d0140341c3c034402c900036200c8400d1040c50050511034941540450000110503002c00c2c407030140101e0000b0700e4818600c2c1250354403075903400411034a00081e0000e03a00c81500030020010740e00c040008a81c030041c0c52000c2d090501581c2d9001c0d548240c05070441003403180116908006440d4170141c2e40081408220400c42c5519500b400b40040101c0340d600c42c90b03403d5000000c0b45034202401545010440c2e01902641040b6030b600040c0108001860300c03e2203040c0c1c0d0340c2c03141405c42c0007050034051070303010b5500760351582482406481d020070400d1042e0100c0b507440810a1310f5402006480f2026018100440d11203850300c0040c0b1104a0002200a000c840240d00340e200080340084803a401e0300b501009185494221081c1c460b4010b4007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 693467823 1250 693466573 693466619
    0x503011215150803040305070f0501020a03230703050a03050907120201030f0e061e0a1122051306060e030a0f080c03040b0a0804030201051b090607051207050d09 71
    0x21810500007028401200c4075092107840c0010301c032442500b20750071911550b000d4800c0d9400407038180103115040c003100c0020301469118948907450040041e4030358000520142c1030002a03519200202c410f04440e0060f2502425041d940f580c50340341c050a2034001081e50000246031800040d041e480000310903080d02c0040e01d41220542c4a540118060a0000050540705031500882206c11208101c0e01e40558405907007801640020ba842070b00002004110240481c20f00000d9140405910308440d40e416840d00305070103131904c2e00c11314015140300ea8800c1e41c1003c0c0e83c05686a040b0390941c49081519415500c0b01d42c5044000c1c02c042d90b80e817400c41c002e00080490614100098189030080c44424024400d1703e01f019503a03c500c603e1a0003a200c1c020106000d88108400c0541c28400c941d40140f200d0400456184c10044aa0380e81c021141003501440000038500305000c81008102080c01b040030250b0350301d550030704c0c00c541c031207007800e0212000c140d02980110301c0c2032404c10402d02055440b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 693469073 1250 693467823 693467849
    0x91d0108060a0c17010335030c0708070b0408040906090e06060d0507170a06050a181b0b03090d110a2a030605180d020a0b1b04050904061b050301 64
    0x2205020b030040c0507048009041c0140d40c030308640040100400c1d98000c60240c0e40010310906045075020b94081d01d1400c44ca00110002200b601c11409a0180c1340c000c10800119070312500c081ca8025035520410300050081c89066080008100c50303031008109440da6040203100042d60307459204180d548080c3e00c1c035180c0e00501c0c00540241401d18542503507900440482d226940c0d03d001d4440504c213280b080a03065004282c460b814400c6901405800c800a82c1c42009030244c058182001942c60b00d200801d04110400c0280840e8a60520382c4060070444040c80d5890815265259803141641a42401700319403102c041d442e40808160080c0301904444900e042484405601008590300c0030014100003402001002142071481094811950005417810124030325941519080c100214802154007155220001800c44003130190400c014500300c04030303e0044800c0444a01441e084079411500c200100b10078800799800107801d441a56490404180b48040c044502d48403d0081ca15250701da = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 693470323 1250 693469073 693469081
    0xf0501091d1509011b0807020105070804020f0111010209061309140408180402160308061206240f030d0210050a0605060406121b0e09060d03170c0d0c091d010806 71
    0x4220350340f0940719800000c50f4804000c00c01c0e01000b0980c04080000c001800304440550248034039600602c4a0074200300b07610b03003603001a0402400d03088690411003040032900b40504250113682903900000c18068440c5000600c0d058202204d224951443c0e040035014803802c903070216118000c84e0030040091800e4800400c003903801c81c0e444a0341e50459400c0000b11b00d46400e412508582502c41e1b681c0c221241005000c0181000d1510240052a005941408040101d0301d07602800c02249024586c02c1a05d5603001501c0c0100d01c61103035405004008403248000d5001c10b46c400d40009000c002c00c540e4494007030410490300c071405400e030000c07410007003171202c14001c070310082d01001b403030001044000c003442c01900040d1400e0303500e0000c44ea070f8070000c40c0381c0e10701403c6003a44030301d042c0c034038880c4c40085844c0200a082c000d21400c212607881c3c40881c1e9800e15100440b0140100200c042c0403c03000b1800003084224948a085181443d81500541480040c81502c3c1298000c1d4010003190b01c2d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 693471573 1250 693470323 693470353
    0xa0c0f1202010c050307080706090210020105060f01030c0212030a06170303040302033f070f030b060717070c0602030d060602010c170a090f050a06110a02190c090f0501091d 76
    0x1240d202e0139038161000744080c1002840354401019070342d00c901004200c0b40c8c0f8074810b2107103038815200400151790421007004055110a100c01008150074a0003081c1041c400300280d04242a9070542c040003540041000603c08958000c50100d910190401340e0400d43e0039a000c5d2a8002920003c0041e00104000011901c4003016082d0107003000807600220703140c0a0001c41d0200d4050f00c241c0d074614015007000700c0c07c0d4101c440c92905c2c4e0003d040c00d1012400d158009006445015801404404880400c1f00c2984020041d1400241d019618824440c2c442202a64039004845440b00182c03c120022944601c10b002e10001172071240c482da11030410400c028072440c4e40060200d0113041e5110a094003041c141d110501c1c206010740040c0641e204c4a080170800d4a5250981c499408000c100300341030f05600240c841d4540d005500b09408107410f51034210084000e5500008009007000c02440c2050800c1c1d001a040b6500c0c4081003220b80b01e104c071000e06103107004045035443e070040c8070103440c144 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 693472823 1250 693471573 693471587
    0x8090f0a0e0c13150215060d02360f04050607110a060b01260a050c040e150d0803160906020d1d041803050706062718020a080a0c0f120201 61
    0x1041000c00c000d15a8442d142c900c0a4034001c00d500e001031b03110703c04083c80301c038a100c4142d0300110f003610714089242058000c55174040c0a10b081110300c0c000c205400800380789610900c104985041d030407010b2402c07c0341001520640030381e81580c00740030369404580028003c414004100f0245006004881c6007503d0320300c02007000300b0b440d178188003003007001d80001c280720080f400d0b1492840da8090540d0074110301280807248001d050421a40b01080b0500441b203944c148590b0091b01c0646130104059120082501d10401e048004c0014501106206018a85503e00c5018883c81d0780c442d503107695103001c1203940302d03202044000450007030300c0c5161f0310b101484040d02d8160300281001c03403450041030034802d1503030094509500041d0045074034002c01c0708900819008081c1d5060742c289000f210440c104103660f00d140a451800d0f614200d066500c085111a40c0080350020308a4920a03590f0141c41c0e00c0c0c03082d011044034034808035807010903841011030003541070707440868103c1e0052803140e0066030701e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 693474073 1250 693472823 693472837
    0x312060609030f03031602120307020703020607150510050f030607091203020c09070e1e01050a030b0112060e15010206010e06060304031808030405040e03072604090908090f0a0e0c 79
    0x1d40030f10700500054110801c010340c09541c04d03e610f000c0c0518950740090a003e901c03d41454611020804e00890940c0094204103594049035160398070003281c64170b6131a42440381040011541001c2c20001515500c102d40404c032407055030b004140000c601c0416403a0003049800c5e07400f05a44840a1150b800303ca960500018840d004071015202c140d00001c4105508070303948000074100044441c0b407414103030f04040c0b0030102e8120b018081c400d1200081c1650141c85044c1e41059500c1e000b4207500c1c1e1181c428013142c09528042084001e03110140c0100c100402c0300d4140f000181a011111194400100b0b40c1c101c2d1881d080c010721680f00c4c80b00300922980003030400c0e01001200c07002c80358088803a00c0200e006040346c8004583d41d5223003038148026079452403880b40300c90300140005004910500342005c8518800b002c01c071800511005070a00310b010b03039009003000ca440c081710141040382003801021031802c12202c403107403000c0301800c001801c0814002c0546c10103001c004100c0090006001d4040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 693475323 1250 693474073 693474079
    0xe0103050403120e030c03180f0a080a061808070506011505070c0b070501022203030e0103091a09070b07030306030c090203091504030530221104090f150c020312060609 74
    0x1034224444089403a5811038160b40c2000100c00002e122301c1e241c6074203140502c0030103540390b8003581e1070240b4081d124008030202600fa10388902c14850301c80400d5286501032640404c60a44441d19810f00310768030b002c240285a0703070b000140c2100110901400c2030711542d66003c8402c00001381868451a19038000e02c00845866400b48211b204007004088510300424641c40341c8007451b440c508000709030840104280c2c0c14140782425440c0440c031100b040500c16122000c442200c1d844071088103181003030a074410303c4915030101d4004100340d80f680180b003ca80c040c06052403490b89452104080344020f41c1e00c811542d002034444d520b04143e03003603d41c1d813150181c01c0950400c05122070710740f440c00200d45100030300b0f40d020a204801030454064150032032412040c03102d4404201a642d8100c032074080000e4182e40b10300514801969403034020003035650703015450342c030000740c1894158080b110100200d0384039824444c400c2c0c881407000055825054401d00350000a464080500485038006460950 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 693476573 1250 693475323 693475327
    0x103020d06050a0e04120c0b01030605130503040b0a180503150a11030a0f0c230706090c09021b0a03080106050306120607051c05102c090d0e0103050403120e03 70
    0x301555184400f90041a50040780721061a0900d0043c404452a404404c180700c3c00d0103030310000c00c4204104a0643c0d40c00a000141525a19469107200007503040003881031200140c0828010800c6028022401c0280c803003141004400d41e210540702040d002c0d40360183d000410703442c0b070000c6214149070404090b400002d0700c4444c00880c8a0643e00440301c0f000103c1d00d85201074180c580a03c41e90300b40c040d00c0d02e81b00345050740000d007240b16112003600d0050360b80c0c00030404405000d6940c1c85400d007680e00c902d0b98180282da54541201039000701d12400e8600380c1003007090001540102d203805100303515580b25105682854000d407043d0300050704042e005404040134161641c1c08001203401103c450f1030f400d403036215002024071451410b00310414050b09213410700c00f001c0f504c14401b006450025024030809000c5101e120540002031403d030b5041386844003403010720b0710046049036440e5204c0e034070030080004610041d4240d40c0c040e2002070010381100c0d41500300c03520395841404c6441e96102030364 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 693477823 1250 693476573 693476579
    0x70803070504032f0f0307060f0e0303030a0c0207051f0f090902130e011401170a02161a01090b010e010f03060503010c0509030c01111002210108010c08060901080307020103020d06 79
    0x3c0792451881c01c5030020394801504802070ba0014240075003050201c3e14005e15100200211340c0b281c43d5449000f007406044c0340540c500c207000707085c003150b10400501226220314003410a600035000240600380580a0710002240320300302481c1d1901401d40c601500c5a027100f0b0f18070100c1c1c500242601400400065600100b1400454001840d0003801001c40342d6410742884800200c0400680c0b080c501008220b501d00c45c5660040441405000311101c5018241e48901ca20030103031044200c20310b42c0704040d100c130b4402c00c0038640080e0240c3c078010890400582e21803648034100e50f42800303070902282c00c00c081d0b050298030032845600040300354540480d0b410f50f2038003c242900c0c54450a1004034401203010b120701d0030100449480f43c00e0901c1c02651244a0000c07841e110170b1404020400d2580004000c030f075020b0007075450f18003072240d00b083d5083d0f5a5107010160080c01e61491a030300041102001c50818a043c4038483d05940c01d0602840c503004450b40150005d602c004038001072076480302400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 693479073 1250 693477823 693477833
    0x303042306040801021801020309181305030406050309010c02012a020124060e300f0d081e0103230c041805060c040b040e0a0207050f0f15090307080307050403 70
    0x282c40102040400941c0b110f100c150940b810980400c0c030541194004e000b00c9002c1d90301d410341c458a0100e944402103a603102c100307080f55041c5001c8005401031200140001e100ca030b01000442c411171401c00200003555003114202e007680c401034459500b4101012241100e1907520038010404107890000040490340803035517130300d511803002c640d12049000e20001c020243c4c0005149101110486080044100e20180e03085042d41d0b4100c542e240303442810003080704983c20890f0698035a0340d00c04640300200007010007003802d0000c89840090f400c210842040000070031040d00c0c183c80d448503402d98030720b0070180070703080c040c0f5130428810701ca00ca2002c0e00506515144112030600340e0381c0c540c1c84400c8049003440c6150850103046042107000401c41000503507000e009650559800c010041c00d0303900c5a901d15000f9000715080601180902c0d10306800d0800001454004c2e0f441c10001d585102c50b56000c013034800e0b0b4013101c0400b201d40041015170002074229005503400310b03040c00c01e1801c094494a40c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 693480323 1250 693479073 693479077
    0x70204050114130204081209131113080c130c0224040b010e0c0f0a050c01020313050c04090503070b0421051c0b0d110f13020304020913020303042306 66
    0x201c0342d000709840030a903010f8100004940c4941820b0a81946807130f1500340e413181d07150701259444038083c1012981c1d42d400d80c1c0304801050402c52099060101e42001d40459405500401b4180c05181da10100000d51801c081603c0f9182c0380010300c1803c04452031038003840940b030511108011805a5124085200e0000503003000280301224100c3c0b551802d860000c030b2481040e04204884c0c401981049500d00e003240448581940050509854a000311025a50360041192200165001004002c9400500d040e88040c840c0150212401d10300310209000071906034a81c007404a4008028000c00311300d0b20f092060308a44138610f50055056081c1c2906120240b264010000400002d8000380e2408100ea922921800030340c0108115a0028000303071072512a5403008200742a407103a459030329a07039030004150110000c0e040041810402d03600308000e6000301c604a02c1006580049140e46003030076151080c030b56020700214503090801101010501d440c0e10300c1c012031200714000303961648580d80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 693481573 1250 693480323 693480329
    0x181801090c050f060424300606030e12180a3f030c0314180306131a091015030204050610140a05040f060c03140f030406020f0702040501 60
    0x107104009182482c00700503407010320043c4244614402d0206110300f00f0340440200c407564121424000d600c0300c4003400e550314203050070f840030b001c0445180d0306102a22000b40b01c6070503d0b02c450401c8080c0d241d08054045891007440b03030310954040d16040c02803601e0500184040c080d43c0300c3c04041903082030001120002280c000c13880c4442c00f000800003140a1551b141c0720b2101c46401890568107041026000014015000e0200441c142090301418001e00400c612106032400803996a10900320b105005136901001a01921411000548040a14034190303c02907010005a010108508201200da40040d042c80490b0040074014003103034110b032007041c3c01d60400004030750300c952450040008035079000703001e2406880060385581340d10344d00044611000034141c0e43e071030710364290100454660265070404000603000b0b05010401a80280c45500210710a82c0e0f081c1c0d800404c004106d4681c010340b59030300c0340da010600c04180060712036009040d0380b4000c41e140c0c600b0085a500050141c450a0b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 693482823 1250 693481573 693481583
    0x406060509190605030406050606070f290f0c0a0908011518051e150307030507090e03040b19211406060c0601030227090f01150518180109 61
    0x1e41c0a20908140ea1041a085400312400d0442841d25802400e140300c000d0000b018a540c6500003a81943c480c130955000a0f0040c0740582e61029a28200c08146031030561364006540600704040c2c0030034083c40503441980b420780865130644900200300d806e50041c80f00c100074014800400305202c0024800c124020013043c4002e051a0b14152158100184142421900c1ca00340002c01c42d4840401c4801a9405184418100c0c00d5550320507000c00c11145644040e03150141410000034018009110410f845042d401005560305000081d030342c034415071040910700d031814022010422180c1030f8410100d000750510900c484280c803400c000801803150700d40892981c41d461a030003440e02c40b10145d4802002d513141413a14071a401103541d56801488020320440c2c458030840d252160f00890b113507d4442d901d0038000b09081c030203906915520300318800304641d843c00f68400d0600b80015803d108684004c0c00040c02100340b018103c12401c001840400c0b03c0d010005481c91380e810900c00c1c2a4050b0251b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 693484073 1250 693482823 693482827
    0x1020705030c0309040b0a08030a081f0608041109070801030605040c050901080d0905030d050405040b0607061112071b141e0703150203100506031b0a0e030d021b130b04060605 77
    0x3220400003107506d400203142c01082c64980500014000000311075041215040c5042c490b910400444004cc0031200015030360310700f0000c0019001d40003001e0302d015600c60041c0e03c41c84100d481c144400444116502030002e0394140040010900d241d001c41d170400d000ea94091b14143d102c401182150100b84c1c07212850f0f611080102554550100d80311014100480180c101950390a070020000d000346d001d82d601c10340d0359030328000b80c644e40c1004440d01180d000000348554800f800700d215a50700100500041e80b22094006400548101d1a024101096a00d1882d804da007a03103130440990300c80031526195100d620709040c0e45190504039003c00124000052071100c0c00c524154041c201e82003604600c40b8010300622400c00e01c1455120242ca10681e04642c82e43d40b4401d081d252500d24890b24074015000284041c5000c1c1e0281211000382d00950849010000055049030356106540c154001c424030790710703500308070302d01355404420040644030080350000007580000c08441880d4094000700b100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 693485323 1250 693484073 693484087
    0xa0c1418070323040615081e0304080a08040f0e06031005220606150302070f030c020604030c0e010501080f1302190518010906060507030206040201030b0418032109031e0201020705030c03 82
    0xe24010351940486c0c60098500052409149996801c82626508042913481800304000c0000300262401009014200c0340c81040900741100035602900a10b096880300c101c0c0030821661400100e40140d00250041002030344801c0351100614025104030010810311070040b08210554100e003408902070705000416500d010b8202c03d651a0544014050500610500c404180c038114010b0303402d0f0f0142800c00c542641440012f0141c89150001007079903007030310008034030500701c0d40b0718034160744003a03d840380151101d0280d4022481308643c100d41e140c1310362000e1001800c0c818800321201c100412084551600e03000020107048002d00310003090403040c80108580b481d180200001029182400383c0341407403981300251030f007100400190600d62209000034664680d035001500800c0e4a0025507005843c910f00100300d445003c503003e0440e03551070301e89007905210341b20b120710385a8151910b1141d0990000c8ad00c40c200302584032441955400d01001004c00c10600041488113a0700c0c000c0c0d55581d03e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 693486573 1250 693485323 693485333
    0x8091c1a1b16030e131b0e06070210110316060c0908060f1009090f030e0f0618040209030729130603021c0e0a0c141807032304 56
    0x207288008003400c12440c811004441c8088030b404484000d2100d88a00c400e0505035000c0700c07491101908100414406402d4010750340c030421341d000401070201958081c0c590110798076101d00c0852507101c0c904000303180c0140391500c984580d092260501d00c1d005a21000c60500f140c01200c0d50b5440d00071070500c80350400c0154800c07030b0030940050500e00c1002c2d0a0400300c980d2002c000b0101c1c902d1084d044081848094400114402010039910902c403140086c40c0055840800c558110b010a05480b55103005180c001d201e00d8454201401d901c3c282030041c1d10100803204106220f540040c0c0c20400c600300d40d241400001c2c050090400c0058440100c91401118801000c0c0c09028000c014000b2044406c1c0800c0e001c0e0803134003285000b68a03030001030154515402c6c11000c5103411440c01601d0403811070003047c108082ca000c2e540d4541240e40d1052000c0c0c200c914002e44a0303100c80c00c4000405140034154010b0381061301850b001031248260280c1d094440340d480d0f44c84d00307581204802c001c100a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 693487823 1250 693486573 693486623
    0x20d230609010507050f03071407061407081b0f040e0a0902031c120b0609040903080a150311240d1b0c0b06100302070602030c0409062108091c 63
    0x1900070000c20807460b007000010300074018a90b5000401030000301142140e4440e001b6445a005000c24099847c1518540031000f0802c07403039600c03500e20b018000030383d4880c001d0f0340d010b00c2040524180d08002c00d8082c0c2030141d0b5444034142c43c2c0036081c1400045020301445850500c900240140002c07524428010145007a4580c0f00c0d0705181100340380b14601042d48a0021a40004046000b14460f1003042c0054803500516802c5a04903140c0750000007030580c4100003500a032807100d0100714842a2005290f041922800050040f42140c80c207512241412000040d4042082803601300b056506101100950f104505030440592280c06001c81d554001c0c140d034010284605103061880410350300c442c51013a00411191003400300c0c04082e0300301c80c002d404844d041c0394403040856030f0345000084841f550704580240d840380ca140002c0490460500c0885441c58118088401101d1050750b8802c4980d034001d178521504110304e02c0d0b60500620741041460035039440f4418003a40c0a5941d50441465 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 693489073 1250 693487823 693487831
    0x121e0106170318090604060308070b0105090702030702030a110616140111030124140408010915020a0203041203030216030c02040509060601090905040c080f160f050f010c020d2306 79
    0x150020400340808103801e00841103283d1080c2c903030070070340c1e0303100800a0000c014650000d807000a0000b1000c0070040a021040d0607180c08850016090f121520200da8034000c07984002e4065000300291000b1803213403001d9810b01940189668a44845115212a014000c1038110b5030f0041d0850100f41c402c1d42802030f40019034880000c0c5007150b15110031103c10028503041042400d091081c1844264860408400b40f080c900c02600c0c0d440c2d0344d910780907009110021041d143d421078201040d8000c0e40900868072540359a82c000d40c10141000078450101101c000118103040d402c01c140e01030100746400c0035100c140aa154016450021300502c000d440f0002c3c83c0e4050740d0809402c101c0180e8120a10b00309032210b4000004a9503280e1a01c1c0d620340030540c204000c50301c00c260300488005400900d82098050040240c201e141d5641e284689000c0c95006460744840d000d8803031750b10303075100d11072555007c0d000410320340407550240c540404402800c0001d040004098908566070b0f070013085401d0b00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 693490323 1250 693489073 693489119
    0x1e0a0203120c21070314010f0e0a0905030304020108070c0203070e0a0c0207030203030d0b0f0303030406050402031c080105120109060e0309011b0b04080c03040b160b0a150302121e0106 81
    0x5402215004043c01128405040c0e400000c1c010108110074031961104041da09082800841543c41e00b003405850041440348509040110303001650296407030162040442e400717001136003140c03102d80c0103507800e1400510001c100702c16000a003004d80e80030000340000f001210011107503414075900003016a0300c050920402e551100e01c2c10801614008110381d41130041c90800a500d031105000038003c0c0e0382900102c4d80c50701c400700030300c814408103500c028000e40c801c40850f00259400e40e0603010741001e804113200403580c0c4800401560a1004c98402c5001c1480d00004506800f5038441049a01c0f04484400c6039002040c0d8010341d50b080b030b111900c46c00300541082030403051a45c4107415000000c10041040c03a010910b5810400104141c41c09041c900001c1501c0d00c038014089072200381d04000c143d03604807024000ca03038090100d110310b660f108080c00b00c040c900e601b140c09000b182e01c3d046e8019480780c401c03071411036030090f0070711203249400d1050000881d6051a124400040840520245117 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 693491573 1250 693490323 693490327
    0x92421010e070c061116060f06050d080d0b041d06041203091e140a0b07080a1e0b0333070f020d030e070320030601170c061e0a0203120c 60
    0x202e1642104002d680198440c2c07000ca9408207648528030301d03010340d020525100101010070030400010760000614082c01840801440d952002005043d00c081c04016051620801c80b100005132240c2001c4403140000e00046529080c41e00c6c0341168080303900010400f41c02503014071013041a28642c204c2005284d18003449242e803183c0300c200000c64061441018140e07444c0040081004401883d69045251803d8500270040c1e81000c001c515000c480751000600711900244480a20707100d08140204165031110b0001e1448411f00014240d40c3c401607810310401902e49003800400c0080b0303a03c2d050041c1320311040045180c03040780300030000d8a039400b0f00c03141240c4a03408560014103840580d010749004a40c0e00781d800191400d01c01c1a070405041c44410b02000d50494940304064a0a408113500700c2e8066a0b0343c41541250b402070b0000042a600002403284151504030040e010140f40481d08290201c21409680a5076200c0700c0050056080031030803102049040c0c102035441080394034864 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 693492823 1250 693491573 693491581
    0x14070b0f1b06161b05030f2d03060f010e101211032208070606171606020709020c0712060504030906020114011203022a10050f092421010e 61
    0x41035103c402000010030021a08050f03440c81c80c3e40540300c0454002d82a259190300b011000b41050b48240000061009007913100fa4031410588c0030508020b031003032101c5013141c841c8010016541900c02006040040002e91a803a80e03480560490f0080501e481d17824840c90020b0002081c0c600303041034280705400901c20422824003080241d4800082a03000b081d1000d40351510034207600500c03001409a5141050100d001640c1c3e0400c030841084907001c4070b64240c00c48415007102c085034018000160000346c0e041001d102950041c04000c544003040d2000c058a944103130898102c903403819140c807600c0e10148014190447c4004004d010380d44002e03c0050160b08040a415a041c4035038568400c0400501092520130300c0301e6505001d62841d0210f182c0710007440880000e042c0c900c1180306081c403040baa82c820313025000300d5040c6540c0e0520181000040300401090407022003003808292081c50045411000c2500140b41001480b001e0860b00506e43c01034030740b5080c0580041400300f01c40c4080c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 693494073 1250 693492823 693492841
    0x81b0114090d03050f0409090c0b03070207090509070806040b010f08061e15041a011d090a020a1707120c0302030105012c1002061b04030f14070b0f1b06 67
    0x141c0d0072550a992181980c8464a0211150711404688042055000c5804100b000c01031f080120f034140a614030042c8907484001c01d4525100545071000507900c105400c02088045800c00d586c8500c41c40140c9030410360f120900e604041c0304440c1250600042c000500c141c52a0101300405456004009d04440c5031044007183c5100700394004001409141000441c504a0300b40002e16010707018009000c0012618003c01040808031050b03030204aa0050440e580d40503066010300f000740040c600307159a16881c1c5d141c3c0096101035403082c10403505a48075101245804051809448203548804e02e9900301824441102c080c841000308060040004101c207030b900c021003030200c44054101d03030f0074500c90f905101c2c126018184d40b1900001c01120741038481d40c0125001d446518a003c00c1c80310410568441040c80c4130f980170041190f044240302802007040d48010907003a0511104880009072115070314035503500600009001c0701d60001c0c2e44801c021004900f00d01d01c82000300140450b0400100b8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 693495323 1250 693494073 693494077
    0x20912010207051b061b0303160206060a0b0d11131706010e040318181a102c041e0c0f1421100e0c04030c06031d07081b0114 55
    0x800c0034058203410300007964804c070844070007120a80100c82c904401e82c1d01b4076181e404c11201001c040c482c1652040744d0368004a40a80300c1d01004095000403410000d035441c0c43c5e0404403050a20703640d0b429042c1100c0307195800401d10b028008401e946118544404080100c1c8045d103142c01c19000361004006001c404204182c1040c0e040c00c2c4501150010980005050060b5025010090f030f00d04140c1d0b0a50b00c2a03001c0d80301c41e00e0f54440b10104030018020310a50328650f141003400540458000081805198041e0380e010340301014019000d125180023906507448088407100e0b0b000318001c91109407500c0e21030784034280213504040000b0031400703802409010740201004500140040d80e100c105c003102e40c640d140d0b9006000301c0c0043c2d0400944009260320035001d0b031503c00140601261780c14005d80c055404403640264124852801d244044001d001d6401078407020342c9188685c6020104103204030005010244010312080890081d0762600c0c465111440d818024819031101c003611000701 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 693496573 1250 693495323 693495343
    0x1403012d140f0f0a0e01090b060705070b0a0c06060e070314070f0f090801020d0e16030803060d02040e0604060c08060a0609090c1404123c0809030d0302091201020705 73
    0x1580622141d03510001c1460303120312010495000c08113090206034050b107030003128141d5403080402c0144640880034800d0781d220360360b0080d100f40c0c08101c04000301c911910082000d602d141ca48400c01c00040c0d5100420346042d41c02420015000c0020045001c0d03061142070301d8144148040f00c15070170407080143c4481d45031481c600c00c0101c1c02d85d50444e0f4900952040c1c000300240d4008655442d03c1d0380000c002060b100c1c0c0c0c4015140180c103145440342c0c1c1081d03a0301064035080700e012840c54441908110000c94410700403608540c0712540154581030502086200d2401006c0124840c0004c2500606034400280510300c14804007005005a0f5403098030a801c1d0340c41c038140003440c444150016039030302c125000503061030080080e01003503428003842d2170103249201b50300320a4594080c42000c0c9500d02064401c8209615401d0000001091004035030380b024040e265103880c010521010038201440c1d000b20740c000c40d0b00060071a401c1e0504121403821501c1c050021814000030f0303907444d81c403065144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 693497823 1250 693496573 693496579
    0x30403032714030f0406020c180c2205060706050a15060905060c01020c030301080709060e040308190e030a0315080f120d060b0a0914010c050d0507031403012d14 71
    0x2009440b4080d80800c122501c3d20503540c005502e0300c0c2d03640002541d4041c5484840d01a02480403280c00809104038030300d0180900d25180c50900c0310260f4a41c07061511001010000c0d110040000780a403a60402407080350302450000c02d0601d44424140e042c1c800500354140f400c428210200546948802c10400f0340742c04030707441661610488410340c060301604186030307081e000000c0000380c240000510700003104c0d040c110604c000c035a01c403800786003200122005008100c4040003d6030104040c4140d1300d8010f4003090002d1030071300d2464000d245400c10000680803a59480c4107242c980b520000c5903004005441c01016025003841d6100d840c0d0b82c13002039038095102c01080e146000800e5805c68070241801c003124540340c00200000421003410f610904081c0c884a44a20303140d03500ca2a14658140c0d0401d000b42038180201d0021140c96102802c06e80c100010124103134420f120070801103000f081d100791028a0201d810300b03404a020034841c28682500c450000410130b100d18101040c0341d0070812 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 693499073 1250 693497823 693497843
    0xc0f0103020703090e01060507050f010204140607060f061806050d0f02040e19061a100c020919060e150d20121e1c0e040213050a0305030304030327 65
    0x91409840c4c03400701d50815800d45612100124031940e2080182002a0041048401c000c8214000c24201c0c8a24002d001020400c2c0b900e0f06c0030b034100711000303040c140c4c1b0071000003d45444500200b012210303a40c0254800b03203007422590700c0d400b03124050f21002d0700e800c59050f40034800682d5000266411b45500078082d81d100c8010070400039003484450380d0111021000940341400d4580314004206400743c2c0003104104001649260074181c11881e6003c1c190384490085200d0380c0c00300a80440c0007001b1801007420f00c00c2031409010b290044c800188081c114113805400c041c036222003d00c001002044c09424035030700c00703804160716003007081031074038501c030346c91592241d16010441c001b11002c242c01c03480c894006444550300c100801d0b8800c0041c040e00fa42c0c6003007003909a00aa00c0b00300c2403182e00048110b41c022080d854568010554a0100c42c0b000c030250795214045401181d081c1d1040d40d280d0808000c010a05805004000405180c0c081035120034030030007400d4610000b02d10002d8488005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 693500323 1250 693499073 693499087
    0x1050a05160c030212030d0c0905060901031104090e0c090c090105030a0b03032808070f1d0d020d0807030207050603010e07050309100213033c0305070b160e030c0f010302 75
    0x1180b0103040140d40c0103401e501005890ba001e036603a940c08945880c01c00d51512140c02c0d4418032940b1002c0c1a03400090060b403801c60140700440183c20000310030803160b00304000003c1c40a2a03407150010801250001d0002810000d0810010900007041d40080d14130401411015070303444821660300412003c000502c015840c0b01007450b5024200400d60f42111800102440c4448010704210521403070340c07000e1083e612408110b0301007844c600c0e07030808962010020403401c400d00e5402c0410341030103001e01000d1920707078000401040d00c46006945100002400b10140355042c0040000b6120035982e00340b45524000b00d402a69030b00602403420054048086580e40600740300c0d00340792032041c58080d5129280b201c22920101a244801c884584640c15242040044200f50321480321103154408203506850625500d058043c4404504000041003640002664841c000340100c643e860700d0700e0390954106014062181c0a5403141c070981c805a100f40b1036545407080f8800c181e0f001e203809611800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 693501573 1250 693500323 693500333
    0xc010801031b0504050a091e08090f030109080f03091006050f040b040b0d0507050328020904140105010603050612010227221a0603091b150d06060e01050a0516 70
    0x402e034110135402401c00e4180040d003012900709a80060049070048142500b103087c8030505050500028001101400030040d0380c0f90240d1800201c940150012071045166030750600300c0d0740003c11705500f40c0c00110a000240e4170401c2540e46000e0707071140c10014582401d00060325408168130881c481e40c1c452070304d031126031502d0b04841190745001e4500a034a80c0146007443d2125035500499000e4442d4500490614908066841c01c50070a0541001da0000680a11150300c9006000740c2d0a1194020481c000c14024440d01c0d0003448540e8000940b4180f180030002991040703400411541c0c01440b4110005061007030741040e0307116541c010b0300007000c408045030807030071940010f07401c0ca2124000110729204542101c95031605a120301e406001400040215038041591040410b912022810030100305180001c2084040240700c0c0d203481178400d032411003685c07054440c4d000080e01c0758405c1000319042002c110b42c18909003440c500740722000724014000d018074454980c07000e400c10304042c10700c9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 693502823 1250 693501573 693501623
    0x12171003151103090d0f0c0b06060a0507020916030c0c0818120706091409010305100b1305090a021503160c0f0c0e0f0603030f0703030903020f010e0d020f0c01080103 73
    0x100c030004041d03221301e04102240e8860045d07000304004503192495400d007240c4640085040994850000e01c02070719460144556600000400001e1010400042d805a56450312552040c18440d03200c089020304081c0060a8441801240b4184100c11240c1000204c600c0d098a4148086444c011200b140380c0c400075801c42502007030400b070703402400c10215080354000b46c840103032105501d01c140d000c0007103130922241d81e00902c4050b0140e0450001c2d178903901125008041030503c0101180f20105421402a0482c1e9095600074500d40c0000b00840450501035600c5259110341e90b8072074110701e8540c40415003e5036501501040214401c001070810103da0049441550042c600c5252151505440301084805807045c100c108594800a011031030004101d6011807100c0701104d04101040d80d00758090b0001c0720044055014400c00344204940902ca04a190b4860070003c1c60402c103030044c06800c01c0201c0e0305881c4a070f0003c1c01c401d001030740c11845050469a0000e2800b101090120b07071182c00b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 693504073 1250 693502823 693502841
    0x32406030f1003150204080c060c0c060703090f0b0c0c01020d050a0e0303270a2102060f1902100b040b030601050907050706020a020d030c0309050d1103070c031217100315 75
    0x136a0802281061150700b540a0829501c1c0c00d01103c4509000340204100c03800341c10034412150307010748144030710740c00c1401c06030030218880d00303201caa00c1e1388803003c8035400301c42c1e5001203220300400304800181c2207040140b86402482800600116032202c000140f061042043c65418409004160314a0303450800480d000c1e0f10f030001410050011088003842e0b0203940c000e515105429129002c519400d0003000b002c0d08030008000c0c4000d030101035080c0071050300a2384640f60400c03800d021050106d0301848030407030301800a42c041e0840c0c048111041d4101c400200c0c04601031480c181c02d00f00e1603140003500a0548004650f049002e94134840101c0b014400c04800402490003ca405404540c000801c3c0d0f10218141d1810300c00303401e120a00304d00701c504030000501198840c076a40071115000b50300900e85044c424080c2c0c0d1906816440f440c04403420380c0d20071030b02d44114840c0355050540c401031310104250f0141c8208958100847c184024016a0002a0460846803404052106194060010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 693505323 1250 693504073 693504083
    0x70306050c0d050c0313150b040905010e060a0204180f1107120f110616091703040e0606070209040611040f0b091216120213050408032406030f1003 65
    0xc0d031410103141c80840c0c104412100c1e0b118142004241c0c07500c007440507030303100300301d9040d0000754122662151107101d12010604000d85980c1c00c04044140c54070300501299502038000070403101104055a403070301030b0082a00d601281706220070701401c0800303c0342c41e44511700c0c40b0003c0745019040c4800c00c0180300c1808032000880c40001d159080000445040d406100b058586400c008110300e41035403003140e080740d25050360300f281002403c00440418100410b042c81c0c50f04080681d1594490031001525a14404456001041c2040542c83c00c100c0154881c100b0f80c4c03040d04000c04e5130b000c141042e0020300002c0419455800e610b0700d40008006450040c200c0b000703490300460390346c1c1031007002d90300c41d110941c0a8000600010703040e0b4400142d010440d00c000d00b002443c10315001e0320f254402164a0101ea011203041000c08245006029540c09240546c5000e6a24140030403400d10003084045e090b00361603198448030407980d8070340099a501410075641ca940c0d941c1d9101e511a9854050b41008003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 693506573 1250 693505323 693505331
    0x90a1a06030a0206180603011211191707030b010f051c05072601060603090b0a090c1a0f030f070f020a05070308030405010b040e100b1c080a090b0c010f06050108150909070306 77
    0x35103c0b02c050240111320701801c20ac126009008041c0008410407807a043c0c180303d1001410041020400c03090701c0c9803074602e41a5000c8689a50303030024241d0080e40210100d240e0010188014a4000050b07001c00c101c00c41800c0701ea42d01d0b60755143e15041c0030320841108084541300920640c0b041e060350b03000c6c5010f079002000f00c00c1e200c000180050006000c1500c031200088000780014816104165085400000709010300780303826403007124540400c00c0ca04020f50107111205029220002440c000e1196070407820440c030f01003100521240c0e10809410441d4000300c1000301045000c60b0390f40c142ca0300300e1411aa20b9503035041c4030740580403000d151600185400c5000300c5040c004540c4a04942c00c004040c40172801c4081001116820b441d0617402542d010300700c150004024000400c0d0440ea6420305d01c0b00d0750354407944800d03d50007405000e5100e07515482283c1801c1c80340d00c10580903010909141c002c50402c401e000150612102800e8010300d114408101d40c000104032101c000e61303200400784 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 693507823 1250 693506573 693506579
    0x9030b071107030f050a031706090606030705210105012309151b0c04051e0a0506010e090108030d270611221401050705030a0c06090b090a1a06030a020618060301 71
    0x5607142030091b825000501d080208806101701c021001d800b130100144515103a0715140c01304042c6a0001c0c0811060110030400003400c0031210840c004800344072180e0010b0340d0302d03101c009800d00480c80d02404007080389020541c0c910401105590b03c2c0d02081c0c646003404075424100e21901d200320143c1d050390200b02824501e03d400c00085a8071140c2080d1018420b50300e4040040c110103140070305080c10142074400041c003a8426030303c501d5002c081403400c00703404818800443d08110003030700041d0450f04001200003400c10360340582980b041480380172403481c0c1c00f161444504103801180090801d07840e4031400301c032001801c0030b850704400d1403100004000020000440c05035994401c0400051500600d4002c560044003501c0465820001961400703180316022501e040b002402101d16550b5566800089645c003807410703205000f21001891a03000a003000800140841c49103071100903404200481500c0200b00c03840341c4c03507041e00c00035200e01000c4400001018440303096038002d18040000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 693509073 1250 693507823 693507833
    0x10020304022b020a0b0c07150210110405100804061401050a0b130906080a11150702060f0f0403083a110c0102030c0405100306061e030b0910051009030b071107030f 72
    0x500d82d203501441203503515607803401e1090030046103034a08c90268214003070131225100540c0190364540e6070900d0041c40c040c0c80d2000141848941812400040c552904000c100940c1e40704840c01021034110000f9590300d00400100c01078464060481d088070b001c00d044810500356000100036000328030090260a0701c9003071040d0388180c558001d4414107401c5c070040c44103003070400d103024a507400380301c81c02d02e0114280c080c01010352100900e27615202d030030814045800055006040a18030078440035985c0e045a4a4183e4a00d011082c2c10a8034161204a06d0064001c1c5801d403040104501c00031030052005401c25440d4091003400480e107500000c104803054038071070010400c0d03a0b02100c4000c04049a400c00324120b526078003c45010030102942c1b1807a0705610b00c108024903d83d0314002c00c200d10a0000b02d00c402d001503c0030400a50441d009100301c1ca00a01e502540201c01c2c0341000c0568515106c17080f007624090300348400d000c000c42c030032400c1c0e440034407400307010b50f0308560341c0800341d0382e18031705 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 693510323 1250 693509073 693509077
    0xc0105090c0315270307050a0c051302030601120b210f07150903080906090d150606051c0b120d0503041232130f030510020304022b020a0b 61
    0x141d0780310b07015052503400319045201c000741c0128000c28100058000906510743c115400e038100116501c010b220010025804102e01d2021520541100c1c1f0380601d0034043c000e0500d008808050030500500410a050f6071100405000c5650150040350321421140840e00090509034040c00c00c2040b1803449800c40e1002403004030002081c411103c10355a128000c51000703490b51180c500246940d14200041a106000781107041c10041201c3d140200e031100060380c042044000322420546e6800504040e44240f0900b8010070305420001d1030321007101202100001c14100b40c0611300d58074180f11400d81c49011000d80c46600e00d00c1200e10030000c5204c0603019403c116412100b201c0c0d00340450401600c01e560b90100d0038060303030764400100c410400d031031407080c50726440c000f0b049003d118202d1030440101001e0b00602140c20b031440d8150641c1407103801c264070ec00800703040a004100340801038803070303049581030355074101d804c00c2c1c54022600484200750001d0700060740c40564102c01080300343c41440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 693511573 1250 693510323 693510343
    0xf090b0105091006090e09011104171b030c150d020c030712020106050108060d050f1b0108010801021218030906030a0c1b0201050f0a050904150602060c03010e1b0c010509 75
    0x900514180c0d0f90b28114030040322240107010000e2030106040050010802c40f4035008412903001080c1c40c4181c1c2242c17640c1e074029900c026403410044008030407090090000c0100034090f40000705020744002c1c00310799107490303c5803a24001c0505a020504280094040e2031300c00c0b0302c00409540d2500016410b650782d0308040301c00e41d900030800107180c0740b0f00c0c014032a0008a13001a102c112066686c20100f00c00507260300c03410f03a2701d8001c501203983c580d10203001203142e0058040059080c40c0f003040c00180300750f60580084ca682e80c410003014041c1c11810321816801032607290f6105100b401d00d0710542c214017508100ea40c200d5000b100b40302a040c42a040f21181400607524081e255821844144281c0c0d03212034041d02203001000030f0042041c0d0f0a00802402c0c0603070804618006034031001c50101c031000c080c000c5c07111400c4002440455030502401d40c00400008010781194144403074461002d01c0a8943e08494842007003101461490400381d07801c08190400800c106d1404000751616201512 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 693512823 1250 693511573 693511579
    0x6030a15121205030405210a0210021303121b06020301050f0103050403080c220f06091502120a091e06020c011106160c0f0813050a0e04150f090b0105 66
    0x400c0104a12100d06440c4010036001605040c030225594015645948040c00c260b400740900603d140000b14083c45018503440c5120703600b5074070340da0030100900b44490003040481c0140108800d04481421004400980b50814201044000d489400b540d000d8103207c0111168941000c0790010b2203d594007540c100d4100782c0300c45000300e010800440848034115001008600c43c2d0700030488100c01c45000d0940030444c565242064240c45a100500321459880300b08034410145040c0019036020007480000e24490400c100b4600e8600300180d204c19440340c5011800300d0100754151200c2c4a1009240101000c0140c00400740c1c040c1e1901207014110700800c4054400c1d075031002c94035449600c0003582c030b59500001c5d20032911040c100c481c43e8804042d00314200400904444003044d0340455001e2000d225180860340c03101c41d1030010701c80001a5004030f1003603445400400250140f0050950b019601c00d040041c80407018454800038028035000c040701c04e203018218010080008080c9043e14012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 693514073 1250 693512823 693512861
    0x140a050d020105160e1014040b3903120903040504020a180506042102300606090c0304030305060316060f090b03090a0f03140a031b0804051902030c06030a 68
    0x110310a8920317080d801d180c19000b010010141403458480d0840800422250400b9460f2a6030382d0700d1061540c00c100720001b415031084c1c000720702198450a0800c0408400c11134010022002400c2589038011010760042800d80440003600c150018412180900b5005008545031031070503c0052511142d01c01240060050503008140d0340750131000d4804441005a040410004c442902c45620155820481c0c1000c0c0718001c0c0c0403004800810100900da14800c1b1a20010060101070724085019082a000d001503d05002c402c1c0180707021a82e01c00d40600300862991644800701c0d19050f213528110138501c540d07090205925074002981c2d40d1020b4640d5420031074540300c102c842202d200c00d880303180c01e50340001081c038006201040c0045c03800303000742003000c4107200c0801000c0c080d034002440c00000030354035040c0c5025007051800c4100302600525048245290130350301c40740c0d10340007047d4012038240d0380e801c0b400455404110034040218040e01c4103449041a620110140540c8230310b0550308452 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 693515323 1250 693514073 693514111
    0xf06061c06141008061012020906041d0708010302090c18031f0b040203010b04030209100902040803030106031406010e1c140309010206010503030a020318011b050601030209060418140a050d020105 86
    0x811480f050207600018245805015042807da8002000d4900d010740240c081c40101c500f541c611011344006e20365031035100541d0041070030021030f28400905c41d0003802120303c01800540c460003840e036400980355560346d603070314104446502d00d901d41020b407903414803403a4a0200304104c111200160b600010784c0c10b00440200c1c20421060b40800d0042da440c080c0c05110400c090300e0100c01030350f0070142a189048549444000100c2607a00942107001c40d94000001000700075454410340f070410704180d0120941d42000700002300410304020700365218050a01c4181444600312884111700c50f4491002808401c40d10030480d00d07600003000d2603025004480002600c0e05001c003c480c036419199000e5440c1c5504c07034a0040900001000d602d0402c040200040c424040c0d03200210340c400d00075402024158594810807440c450001d0031140200e0030074a144e4042003050b568424040e40c010f44141400c422170b2501d5191510005001c1c1007803080c210b1a04400350194480ca00800b600c52201481d091 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 693516573 1250 693515323 693515327
    0x3031302011b030e151201060c05070b0f0910030e1902030607050f1b100f0e0115080709020702180708180109080d0f090c0f05180f06061c061410 64
    0x128018003a0200b000840e04c1075191070048501c0c42100c2141e00021300342403420b10341c07103001d64098208030081200032150405110040041c0c50080c00303000d4001d4500940381250910754001ca0300f401d801590f01800780340c901c2d030003074100e041c410100c081101c9030440e1420883d00c0c9001003080a90003409100003046c026445607045075807403421018031505c0d0044201101c0030000341c41188c00d170700f401100070b43c1121041e24080c2c00810282004049034102c00000790f2800c5a1900d0203445031101001400c008040c1c0206406085981c1079500607200c000c076001250034581c510b0705404400f07011100300948240c00840c0c0030700811031940003031420f0300f5101c0114200c3d03a0480010707041110a02c0f255820320a517070010400b401c190907012520111035501c1305c440d10b48a80102902d02800d1000340700c1d07410050701900d40402d0401c549406810001c541140f0858040c1c0b000d030003400000b0b040c00c070004c06150a26000c00b00b0103000c0120a989074200c042c180101070b0307082e2140d56100b00803207000d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 693517823 1250 693516573 693516617
    0xf030f030f1e03070f0c0f0b0703050103060b09010f0510030b04020705060f01171023040c1401170f0403090f29070b0708060406030501050a0603050f030f0406080c09030303130201 79
    0x4140ba456080628407000030030b81c0c51100c1b01c0c1003290711307180f044007910000304d1f150403c07400342c0420b482c0402c055056144c2041500e140c0900c241c000c0d40d4100041081c86442c1406108071041920760540001d81c0500c101c000e40105c40380d1540060002841381c00704580058118494001a007a0440a0341c940c181103188544c0407890212547c0184905009810170340c1c002c04504070203000c00c0140c10503443d15242c43e48002c03581917890542088041006000141e8030b10701c4000240b030000800c40702d071011441c1030325000d8000b68442c06040e00003410107009024140c060008400500d0741da9a882d42d241413804500d0340007103e5084a0b10b10740b407403028044244c5604641c41081415144d40b001003c079017895004209507131180d200c160000202d042803082070b000d01041c1c81e000c5180c82c25401c0a51408034110410b40c01a8000c010384240d900054082c2c40a13149107280c989181d8884d5000d50b12680100b0160729814007000040c0035500240074500e0348111320070f0303d590780c0004106001081c45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 693519073 1250 693517823 693517831
    0xc31091a0106080114040203151816140304060c0c020a090c17130b06011e0201051509070516020607021e0406080319080c2a0f0118020f030f030f1e03 66
    0x59510348190301701c40c902a00a1a400040001030403403c0320304900044200c3c8080341000c02c0220060240098400780c29201c1c1d80d01e0b002810554507800c190407002c0720301c0c17000400c00703843c869403030a0032000d4a224001c46514181c00a000300f04081c0c50341800300041401d440c26102186104264140611000240c07030301c105000a80304900d16620340303411850340001410310341000180d035505200c9010100c007541040440741d000013410b05e071858510b0100282d04041d18030959200e000c11010941c890115000b0003030150074540c0c451250f06c0440c0d80d501904030b000358400025001e150300500269440c080c0c072002101c050120702e641d0303030b00301d5122301c100b0118070141c0603000c0a950585004014480d00442d00c61516450590480048030070280d140d8544c44018980c080340424540f0104912030703140e0012402004140000c50400280706e14030381009004850044094400e036a0510610303200d5010081900d80d42c2c03051401040c5075610410030b4540d21449280410815130440c4160380c89 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 693520323 1250 693519073 693519089
    0xc0c0d0c171f0f06170d020601080303040f03110f0109080c240c0a090f08010b031c1e120606030b01180302060304060b0d140c0406080c31091a01060801 67
    0x1d0b01c641481c20405000c40480c0241070315151100021032000d803150039090a0100b40c00b4040488104100074113099040e403010300b042d4014014800898403590000b0342c5c0e194035081c8100c02c8815180c1440c20099901c3d41c0381131303035482c05400c10b06124007100280283e0380703c5425038030342000b11036003402d0100e01408440d102c9440e200c00100c00c0c04a00000300348043d0541080d84c1190b030344504c1610698a43e410142041e51285803030501c0d030800300540e0000c1e07241d03440d840751100c040100c001d1040c00e802d04608461004945ca840021740600e40140d80c00702c4480c030901001d030321406c01030060700300c2203002400a440d40a03080750b151801d400340800da90703004005c5131a40d15561a8072010300300c080c0240d5400845201e0b4000010600d000b031500766190100500b10344106501000200c40007030b80181d507160001c024807095540c4820140300030051107805011103050b54801c000103142c1e820540400c0515121021092102050f1403140c4c42c01d02501484450380c030741e0000c89850200f8414440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 693521573 1250 693520323 693520363
    0xa050907080a050a0b0319030e010c0b0c07080d020a2015061009050303130e01050a050310050702030c19060507020705010207231c0605010b0901050d020c0c0d0c17 72
    0x81111103908182e4006544820108105c860313480000c0c02c241d01c445410751400b00742c0e281e10003050b421561105d00d02d1001d08010f0289071581d03c5a03114254018440321080400041c2482088002000d8400001e2000c10841d10b64100607806040300c2ea030305c1c1d160046419038024421558034000b0382203280404c9416503019549a500c140888040c866070041c00340101c0c4000421540c40800280807041d44200128409600e043e24810ba0800180c00590140000905c00d0046417000540284004031700b900c00602c07903580301401c904500440d4803c441e540560004141408410300305040b20b1800784208015580794a03500740d17522441d520a00b4050b8000c014200701084406001c1200b80310800300c010141c1e4010300005840146003112128018a00800141030007900d00c261809006030a0701035151900e0440040c04c50302810380280c41d642d400003404040e51909114880d000700003d03229000720715051a041802c006280a0031009840340070b110a525800015201c0143d003414940349 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 693522823 1250 693521573 693521581
    0x10b030d03051008121b0114040b060d0b0106021f0515120f010c0302030108010f0501030809120a050a0b0f0703050408041203170c041401090b0f07050a05010504030804020a05090708 80
    0x7901a01c00201031600c0b80d801c20344005401c0c4000e010074041c54804502159803081c400140c0600040f00c98001c980d01c2e898580310300055441c3c203800a402c1500116110b80c07540d90400040c40b1480d010310020000000c40c1c3c000a0425000074150351019010b60fa1280110104041d440441c0e030200c40020a60072024204109030500c031103005c0040c100720b000d0b07918107408018103600b034841e00006140084c0d0f0020040104d96000c0c0709503110206178a906000c82c3d417441d1a545410301601d08032511619012040d072a4190701001000d11143d440b5058a0301c420007814503c0400200b203440f4a221400d44c800294164842c1c481e2030720840d4403500950a0505000b05d840d01f00c0d6800e801141030001c0340381c030380401d0071060201e10300c0f42003a841160740d200e00b0400f00c0d03070f01000d68080241c1400804241071084001d010244c40b04400242121074440070b071810b046240c003807603480c0a0004c1d40f8000a00c001c0c158001c0d40c05109038001c0e5407450b500b81d0340e05d091100702c2104552890004450402203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 693524073 1250 693522823 693522827
    0xf0c0503040c030f080c0105150a1707170f07080607030513170a0e120d09080c0d02240406050702090606160f03210f0e0c1c06061205150603010b030d 66
    0x60241207014089150500304c41b0b0402c5801c556040e110001c10340003002280361107191440804010b02600c020700700001c40c0654090b562444540a00c41c4400b010508582240d40100104140070691108481142d9074440c1455211031058642a00080c01c090004040742078038103806c200790f81d03c501c0700c400c0002d01c40005461904810541820409450360310a8541d8542c3c09003a404940341000e441207111208000d0101e41540c0e00144c0160481d81008180b07641d14005804020b4042e58140f52200c11006c0c40d941500d0512840300c04401c0210340451119480006004014800d50b0052003e452b140c040207014001c0d0b00b0607085542c5103410b80c01c00904200340441c41c072071084c2000300071440145440fa1001481415102640b5503480c4001261941c6001d6480005d80174800f0f0b060300310003400030545900c601c1c0005c0b904001810a440b0800401d0303400310b0000d1404076440400060b16190464550350380684800b00400358201103205483c06220b0042100030040040408420b002e41c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 693525179 1106 693524073 693524093
    0xc0903011b021b030a0503190f020601050d2303030c0c06010e0402030a0b07090e0c180a050a12030e0d08071a0702030a2a060f0c0503040c03 62
    0x118080154000c0f80e450310500314114800c0700000303108042883c0110b0700c00d0080851000240e0b02c2c0642e01c0204030600c9454943e40c03510020403500d0741c02c0b60703190401e0181560040762005500b0000300c0101a402d240c03101550020040364080d4a03050454004036000c28084100140c4500909000d103c010b004d4441c03030401c0c0784941000e8010a907600042c1200910034100940450300d203d001d200b50350001d00008158080c90b185c00c10b000c1c90a43c0040c1e54040000c1400d003203000841c40d0545031041501c1d8082c1209004500d48403582c40031600e041c03001d6040c8900c039905c4040c9034440b4003001800c039000c1d030400744d0303641c01d249041510212201d80140c2a1444c80c0c040c17000096000c03045811000b23340c6042d220725540f80d583d00f60000c0010180745200900c0d441c0340c1c010000f041d00180c030a05c40302c0d2010004440d9074601510580b0045030700900024101c20188001040040 = true := by decide +kernel

theorem cover : BRFrame.Cov 693345323 693525179 := by
  have h0 := BRFrame.cov_init 693345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 693345323 ≤ n) (h2 : n < 693525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
