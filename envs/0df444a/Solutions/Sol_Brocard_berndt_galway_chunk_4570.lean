-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4570
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:02:58.214156+00:00
-- url     : https://prove2.me/submissions/f99c4c61-50d9-4d16-bd8c-3322596d5091

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 821762589 ≤ n < 821942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 821763839 1250 821762589 821762593
    0x80309190318090905191e0303020a08060d02090604050a09081324141803030c0c0102070b070209190b03030c0105010f0611102c0114220b0a06030b09 66
    0x100800740308408050b50341c10141925141c0080000441c90005454806480486400320b00700316509216944401c505402c0c0c0669652020300000c056040c1c0c000c020304181c41c1d560303a1541d00d404081103401c00c2c00604c0690b010881d800801da891a003a8000b0750444007429000074a101140c0c1d0345080b0382c000d0f4810911a1313403503040402ca24480348c070001642c1118421904a8610407080140025142d5130703020041400210b0000303052015071070180710150b0005d003141e4442541c1d404559548900180c140e0050007006000154414110f083e9080558010142452035854440002170700c84561020384425440c0d842404551700c0074001016020041000071565604258a507000003046030301c1001040002d001c000ea9580b400b144590b09200078681c04102d81003070547d2442a1301c6019000399500440c0854055103100540c009410400c140c0100c021542ea1582104003c400040380d04212600c04c0321843d00140a03022001d5020484c07440c00203d054890301ca0588a22080b2342c621826 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 821765089 1250 821763839 821763857
    0x21b031b040b1c0b010506070b15030109020a0305010f061703040506090315090a061b0527040e07080c10091a0c01050c030402032b0e0a080f06010f0605070209040803091903 76
    0x20044130302c202405003d00380c0f07070345141403055510f40b901c50b1402048400224104020f00d142582c0a42044080b941c000349207100d15034807820014020000c01c1d03501c02420303103072442c009a059034040500c000446c00c070780a142890300c2d01c2c050080030351280200301e6240c022150038011007507a1204250103240d010004001071003451030a10304940040c616410900f101c1c0c042d81e02040e238048201c51034020b0305860110f0b000700d0009d40c280c1070f05500c0c646070381c007500780f0b4006500c008000641000316403141041f0350381c3d6024101800100c1590b40803800010b20401070134000c0903154100441c0c2230340c0381c203009031800d00e010b60100d0855000765401d201c5048004140130030341c0f41c10040c01c2d1081c07800c0c6ca80c0c050310100c900600c80c0002a40c400d10401d010007030240c1883c1c6d681b0361048000908520041d9154014140c00583d1101001d0007050b04a1050034000305400b842402510240c0354050017103a069103a6894541a40c4c10042941903180b1414030a000f8259152103880c4049200380c40304803103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 821766339 1250 821765089 821765093
    0x6062003091c0506150a1202010c150b0307060503100303082208091806091603020c07030b04170a1722120806042a0306080d020d021b031b040b1c 64
    0x900d14060300384170741e4210070b002d03482080e55000012030072145004031005040c059440140c94024511001900300c000c030004d4015110360300d400c88801914100e042e1000141c8412096400d0f020940740c02d000490071003801d00010740610700d0300d0703000450b4000404100c00083c000b2006003e0080e011030b503210010030b250030103040c40c0000d00100850f44804e040245000b1021a0544000034042c0340041140a4451080350095044400301505403027070310802620b90030000322261003034504603104010711000242e16440b00c82550740140c1d00b943c5d224080c91402c500038010860103020303482c00040c0c100c00f11850030100c04d940034403d417103000001ca002c000000d028102000007010603000d6030600409542c0c1c503203249401602e03014114401b140313084d10450103c0c000d1065411210051058401c040b84440e00003498010710700c600c0e800c071401d203400921000c000c80202421140c041d4014141d00d10100c4c0701060200da4417401410020b8100640700000758035030000201e40c0342d5410000e8407641 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 821767589 1250 821766339 821766343
    0x2a050409060b07031e050d1d060a0b060307110705092707120f0c050a0f08010e15010605071a1305010e0307120503040c0e24030106062003091c05 64
    0x24032500c1502c0b030422200e030714040c1800910100c8504c08025500418400d03a0258090b03441d8840c0e140c00400003d00c940420300221504042c05002e0752061100060b403501603401000010440a801d503800c580385c02a081c0c1c0c140054045180341030184000c00320302d41d102c401146109130110340000880340d220310070003d8034020050603000560130014080c420105a01c04006d000b5511010618002113113042104490095405c1070350b20a45e020800a0030405039404c6805464030744000304503a810128079542c0d6101b0700e8810303031403081c2030000401c0414083c40160030b03140d0058244c5043c0501500e1824040d240860300591000e284024100074040c007403240e404182000c000451400d00c880d281c500c0c14440ca03035552030400500000040c2000701010804005000d003d44884060a01c01d95085c07086025690b050100c0d110600c42d55a1803505000319011a600c0e0b44440c000e621203e0381c10380700e1121a154080301ca00c002c0000c4125a200c150b2050304c0c003003003a40904850031036454414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 821768839 1250 821767589 821767601
    0x19050d0c02070302031b0f0d0308061e090402010f03020702040e010614090c181f020d0e03010212010605031e0414071a0306010e0406121407090c0c02042a050409 71
    0x215070100100380f0040c0c4000680b07060840341085e40400c070901b150001039200d012400c3c0302e0741042000009004054020200c40c1c06240102d81d0050010340c00d1412100c2003914a003525400140440071601550051840704036907489844d005d8900010394000c0b9050300c0e281040c0c401582e40d2103030200070071080110242e4442d482218079200900780034000c590140a81d029000c0c02480b14080014540c1d115400d0b09600300f5140380202c80ba400c00080651510880750985000ca11440031010386890184200d0304014101d0200d94866424024200d80c4c6400003400401c00c0d07a01c520381680c02c0b140844119219500c01c0608001000c1c004081e1410b1a00315440081e0004005804000c6c02c00c0391029694000420302e04843c80e89003800001c2c001d0300312948082c418280e04003807a03060285020758040d080c0b5010046640c11507980d940c080c21a41111450400920b061140200620702074100c007242946a01d11000c40e085220b81c08013138032901040382e40205400040800c941041d5004003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 821770089 1250 821768839 821768861
    0x31101030b0604140a0e011710060302100e0f0303070803011e05030d1404180b0f01020601051e030309060c060a0c1d091b0409020903010608030304030903020904050319050d 76
    0x3846056000070100b011805540115200741d100f040130603d07aa120101920020b1140403642c0342113503900c06508070300d010005041229070040d80c441e100c500619005150460390302901d602c6562110361001c9947e1500c9031710f41d42e8003034100e004070010350350100b01405c6006d0040c078040380e51b549400c45c02d420711000c040e4846c03418100d03181c0030055031b82c1c0400d02018210540c140b0f099004c0b03002841d00401c1c42240c00040c0d09150050001c1650941640802d98824080e00c8080d98400704c040103a0741c40c0c00912503a5031068082e4084005015178881007461100058100c9007455030010000d41ca9800c001944065940104e00700145c3d42407a000d80450464075062040c81101c084402c807241200e0051014012038506011807001c102c2141d640098111000c020341c8c81d0b41d2503007244006903000d001c4e441c1c4290b08040000c20700341d030b0100c21240503c7e895107800400341e01d540d091054550700104292101e000a20094212f0340840755881c07138492955072056680e965810252048a03900f0070f030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 821771339 1250 821770089 821770091
    0x20a031b0f18030206070f03020f0307110f04090b060409060b0603010608190e12090d02041b020d18032301021323010807182408061509130204031b03110103 69
    0x420400345c0c0f111002c8a901a80000c0c0984000f0211704080c2c0ca8212190450981c600c00092900144083d18640c0c820b018001c4521101e6445103900700801d07101210006000081c944000c5440c0c2d2500e513014449e5140305000120b6048128000075816401c2644004007050841040288107484500c040c142d104440a0400042030326550740c0c0c0e80c580103a08041c00752840000c4a003880d42e20b41000e4020203070300802c02c2c00450040c0290780c43c40100c0c0004c1c3d801610524030011042d500076180360041c2e148401c8820f11591554681194040e0b01c28620b1041280b10b0500d510780001c01c1c00200050140c084001e1030360307441c002803201d019030518a10b940d90450003104840e160780c070146098024000e40b800030b841c0340e10f0440f12b0030580940d500c4114048580c031402c04a488170a0700c07030a000700d0540c440346e201d0f640d0a401c3c011910b40c22543d0201e181c20400c601da03000d1030038a00a400416032200010304083e12603640b0b2047c0d07150341c4240910300c207401e6010810009002d040329103001c0b003032034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 821772589 1250 821771339 821771387
    0x4210c0510060e060a0f0504021308010c020d020c01020c010e0f1203030f04020102070f0b0909100801020d1e060605040b1c050405031206030106050a050f1c080301150c1203020a031b0f 81
    0x1006c4541d280240a000d1040e600050b80300c10050803071050f02d01601c10000200f1819254000c060742e00c10042864402501070300903088010360001c030308a02d0104060315429650b0031202c04200001d1a4941c105502c007410241054079004104050b500c505a85040f4414500f050700000e4942001e642c401107101481c03400501c1020590026100c0f810360507a03c4818540f83c40320180c041e880383c1d801014841d84003140344c441d10411600321507689a400c00040e104841c20700c1d0790b00f0640303005004034004901d0810080140171904002045454072604408450490711080b000940b482038509560650000c500005c501d860a000365402c000c00f00d008105e83ca1030035000c00c1905082d0702c0740e940b080d000c011683c0303425202e1601d4011000201c2000b00c1202c178040c0350119040c0c0003030207001c0c0d44088402903080c1c03d5002e03103000c01940d45c0001211030b0105081030100c020b0362101850b1001c1540707907810140c19040d140440c0c9103164003511050800341c801480280702c05803980515250300c0c40c00c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 821773839 1250 821772589 821772599
    0x30f18031109041103011b0801050603040512070302030705060c030106031d060105130b15210108060609061804032001050112030503040203031b0c040506030604210c0510060e060a 79
    0x24018501128040c1c4820079141d481341003070481038464042c3c0e99010b50801001d45003040401a40c00314007000d54940b00707116626982800841d002c210780003040c1e80d1192010103a4904258007922040740300b441200c2c5001c1255403203d04010007a200749075014000b10040c403860780c0500480c140b041040315512120307000d840c510780c0c2d2400d044c4141c03400352082d00b070f407214134003d59000764010544c0070b4880564100074014502180d4028010b44240010110700303190044c00034000315040b02d0980004040740d407508030030440381071406002c10f80c0c04448003c0070403070b9080d01d0360b06500c0307280680c880c6221078451620001010b04501c1400c51700e030749054014888010791080d802c2c54650546040c40c1c403551944082071641c82003401e241d49182070005400101600054283c460300d109890a104548902c418159035520030340b0010050324100718141d1030848024900315038402146014005c10659443d11418006032000f0102c0345912110107104602e19143d00c913801120a950302d04000e4606 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 821775089 1250 821773839 821773853
    0x5120a1d0a0605280306090e0307170c01060906080c01021911010305130b0a0525080f07020c060c070524090d030207180212010602210a0c0606060302070c1e090908070c03030f1803 79
    0x20422885420bc0100e45002042425030140000e4444d83c40700700209a1203c0c0542d90f10440c00308903d00510030301021501000301701a0028500380d10a0340801c5900710300d00194042c00300180b40e8207100340c0208421004c2061400c030580501c0a646c00020075050184044a0040c0644c41c04080031840e015610300c200c0d0b100b1180c40d4401039107003008401d92603991041381003002d12460240d00550224021003101000700b9540100c036030464101c0a030b50a03440030510f03100d2040103245040c9609000580450400000c0810600d10038815500101e4039042c1541804a58400000300301d81c0c04203d442003061040003c07405003409000815852074110369000d52056044624225150085560b07040315008846900042c1d51100d014000941c131740c10010000e4016040540d1581a0b0840c00602041102c12490b0f52b101032519141e1034038141504100500786241c0d044030b1120b800c00108020511002450f00518407a5a0301d140a491180d0003c00500c0c410581005401200000700300240341d07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 821776339 1250 821775089 821775113
    0x307030f020409170a02010f0506060d0b150a050d2a2d05180411180f13050f0703180209040f05120a1d0a0605280306090e0307 56
    0x480002800303032802520104018100d8104000c00000352503909494080c0c90b140944400074040d03008100b54948081c602c826200c090352500d03040300c1c04114200c42da155542007040c0101001d4110100020522004d4440d64060000391b000100003161340010b000c058014170892218500c41001301c41295002080610242000202441681d0350302004440354540c00c000c5000c04207008240801b1502c6029001d030784556454107444a07201c03401c1c0e145103003a2080c0c03a81c60079402845e0f81014040e000004881900718006648035540c1e60035960300759540242010200c4403088003140328106891002c240c40c03400b4141c1c105050404450717071104a02014640300040e0115803c11047e02d49013020b12805103403400150160081420801c50740e1090001440d0400c6940d940c0b0001051054000b080c0709880c00e9640e50002640c0420014588684068026940188000520503228000718106030b00c1044011005c00c3d00d03008100190b54081c422416403620090286240c10b0301a0380d41036000035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 821777589 1250 821776339 821776343
    0x105120304080c0108041703010b0307081806061201020405130f050f012d03060e010501060206070906210e030d0b03070e0c0d0c1101020a0c02030616020709090303140403080a060b09030703 83
    0x3900003c5c042c041c287c0e0b03100fa21171301200c2c2c01503644d584440d200e0101d6401104c0702804500a4030103c1e03101d08141075840001810600985103544402d401c1211b04101e03044010155902400b0120352a92103501111a48149540004000600b80c201c4015560001c1090902080d00b0004110002403031108503161602014090381c440d1f86800c0c6916a244650009060f12b80340a00103103800b42c1c1540201d0695041d6002c440d9250358591084822440a01481c0e000a14441c2e00c000d003501d01c0500000720300d074220800301f034424000b0010791568101c56108858240c480000c01c10320700381844407002034030380c044d0705420724540840e05d2051445000405061956280c5840712031a03c00e148a814000019000350341d01c43c0684c6c1d00910110000205920070302800c40841d030245940e00d8a5050130b01c00f40c0292480c1898a400d1381c004040200f400d07401d064641115000362000608000c3c400c030f10a440d07540742d074100030b0b0242044420380d0300302c01d01d44141042420b04541c0c000803001e04990f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 821778839 1250 821777589 821777597
    0x30a080d0609050c0720030a030809010e151006020d140304030201060e09010e011a0d021c02040f050115091a070f170901021606081b070510050105120304080c01 71
    0x40034020412008060950100c00d00510b020280460001220005c01000b070040d2010540703140e4030081200c01e12a0400c0e101c0c2c1c90f9000014010000e1301804070b10b40e00140100000808140c130316145410407440000c0501808041000c1019001070110410b02400303562000348008180c43d0b4002d030054403045258044050040700080c00c1500c03d4108802401502035042064148520440d020f440b841c2e43d40e000950801c0281d0030380c1c140101e07496680d034200912014903484c2940900150200c401c3c4260a25806071040f01c0141c4c4440c010300e04c802115890005940d072400c0c1c040030821168940c4e11040002e240c4040040540c1c076003190000001040c0c600d962010340749481500d0070b00114008003070b900d40204054a00341d5050113880035080c00e0b0241e54840046406a1880070003600603d4013003480900450140c864074200490302d0711480141c3d41ca0b160868440c9850f00b010700c42410310054840c801401141400315401742d00c0309030580103500380343c1031038402600e580e49444002c0c104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 821780089 1250 821778839 821778847
    0x90c0602071206020d0b0d1b0501080402060f0a05160807060b060a0909151d07020724050306010e04290d1a10030f0501061e210201180f090e0c030a08 66
    0x500d64076400b41d0340c0c400c0010400074110030740d0301e44501526200c01c441100c0b20423101c000107080d402604164402d6600a096500e0b0900300c11021040e5041400880100f05090002006181c60300f8540c480d102c1c081c444458651400b46009420780d02004109030061340184405082150000c48600580f22142c00c0441c4043c00034151404040f1194031a0301d101184c0744001c0c004200004409010b884c0c00c0d42540c24090721002510b45804a010f600b81e200d8058800c101c203414030903000f83d0380001d014548200301010401c001000d44100100c40c0f5024044076548802c01c0d440c18003500d900e0302044d56400c5c1940001c2e00c0b942c0c03008105005401d01f11044000040148211481e1a0b02540e4024285c001185c810304040c5c3c02444180100c5914400c0f041540b890544410365030303012540c031345404103103044400c11040300b101081d0310120706004030b80c0e810800421070903210b6409408008034204081c0c0c60309003244196032051081c8030858000c142015156100030500ca03400790703002081540e60b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 821781339 1250 821780089 821780107
    0x4080a02040504031449020d0f060311030705040e15090c030601230a140f01030b040204270c09120c08060a050106021b0609010c02030309030d03090c060207120602 72
    0x841781c1413403e600c0380000240c000c00d021070400e03190814003a0b40c0c10300040d1208058441d1840015443d40448108600410b40d40c44401138008003400c0c0c4411501092031052158220140c40460304200c0307112803420045070750381c101001000c00420781207509210320a03407004401e8581d421191b10410030041100041c0300c0d00d50401c5203c8000d10040e0031140f0569442403030600403880c5541e51400024260400081807400040c001c01f034410b01c01c40d1101401c244400c1118100c2c441c07050606242d190204000c40755182c2c4040d2006003d00c0b00710090b05000c0500c07856448500e404814400c6240109050055500c801d0210586105c040d0710409200c240c20024428070705d640c04203d0501c0b8090401c10030b10401c1d00428101d514603022542c01070f010a103a01020030690340082d40200f002e114250b9a9031040380e140030543d0010742a00c0c83d108801010030f0502d0082000d8038042526a54804208003202c01441d0003440188080c01105003040559145c480150901800445e004210400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 821782589 1250 821781339 821781347
    0x30610030b0a0e03090d21050705030d1806060303110c18040b060d120306030c0e1506090612040c050a050a140d21022b08180a0804030b060405070504080a0204050403 73
    0x3240d490041084001040071f2420301926000060f15000049078062075110450060054030082c503404000341d41864040907913640280104490039000807003114141d004198240714540156000b5540d290b524641d0100c514a00364001e07203a02d000d01480341800307010041119a05420030b5111a14903120740b540400584170442c2000041c10550b850325a06d20f080350150b0084040324480c640c84c4881658030129104030303040c110750808a00d00d12243c07100c59031034400d0044c10607060040607e0f0030090082c4907003591040c2120300712005d2920001c00c0c0000d10380310358190300900048a007440e41c2e0781041305c0850b03c110800901402040c5030030703145080105200440a1000c004076214070010030420009542d14104070754002110100e581304071400100d135001c00c08022140d11001e6482c0c80701740a0050040b0310104623030841c040e0701501000515190001e000441c043c2c800754080382018000c000442c0c80280652052003410030041143c06070209990300d2181d01150002003039a81c60605413 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 821783839 1250 821782589 821782597
    0x60506040b12041b0b1c0209011b2f0307090c020a0303021e0a23190c0206130806180c01091403010e010e0102180f0a030f0305040b040b09030610030b0a0e03 69
    0x13402c403402040450003c140402420b0485c00048a240709141c0494655040b48509610341d030019101000800c07080c1259000221294810031241c015214081c041580648000b141c41d0312407024910003955600d410000301c00a002072071800c0010a00c00180690f68130b0700044010181500492a20707a41d49500340c1a402001d04c021010f956100704010003402a0b4000c0c6010704d541a80c80c4d10240309911b40425a5100035480e2421219140e00100540d04480714840c12a070000c0d0401c000e800f241e071303600240d00040081000410745418810100f218640b441200c030192a070043c42012420380e404502c03401113407424602166403549940219000d080c085400d00055030038544a904102030550091414440340c44000006428801c00c0041c4000f00d05c400ca58050210707802440441c0c0380d503440004580c42410b1a40c5020b82d205401d65194005601c0142030349000701d080f480e18141400603551101d01c10202c188a1030455440400408000d001d2241c900e507505210155600700700201c1e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 821785089 1250 821783839 821783873
    0x10080703180f060f050c03010b0711040f05040c151202030c0d290307080a030302030907031a01060306060e010207030611040b1209010b1507020d03031407020a0303060506040b1204 79
    0xc811040039041805008203590000c0703c0052915404144248051040724082d40c0c00182c2d2a203140d1900c040480e441d04224400d4a906034800c042c42c0060350755102d0072000d0142000081810b180c90f051000340181103034081106240603181c2100900d500c00501c08006a18210040e105d840304401504507009150800c50818506a82503614000300321007109036801c0502c0c4040d06a0411042c1901c0380b082d48a0704041e607000c2e80300640003030f00a03009903030b01024003400c40300000c0c0c2d0f03074462020440005040149040c50a0014809103525000341d0b4050002810601c05124445c3c000035604c401d00e2101511081c0c0d62010b40100368a001c1c03c4a0043c4000e0000382e4a51008410707001c440c42e029a10740c0020f600e440c0c4100b1031410700038156003021b241c16841ea810600c0740e4003442410068041d040b000c06585403185d000001040514a0083c0095402000aa002c2e480c0c040d0445403581c0000c1d220320030900c002c000c03600381e031822034010700d214490305c10840c0c40364901010404051404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 821786339 1250 821785089 821785121
    0x18061507060914060615040e0718090504150212040209060a150518040b012a06090506061e0d1704051c0c0f0f090b0d060203070207050102160510080703 67
    0x900014060381c3d904030f200044070b4005803031054840804210781c000b46200440300c00c203410712042020071000c04234641e003e0003e0514080359010b42a200070108003503000f0f10040d81c0e4600511041c049a40d80c1241e81c5050b02c0411031801540003d0700c00c002c3e00060000340714543c8030f4009003440d26428101401403e21002000388140300b02c401602c140c2001c00c054881c14200d4070140301c589010700a1146042060312001620918006a490b144c0994079400340021a05030b070080c0054050301c03e0100c8140944060f02c402c0c2450000c00c100e114410f02c0c10180010030314043c000660fa204114105642e0007140d5200750080034070400010b000d25030042e903000c04499030103401d14080f14903444116100b4100301d0082034403040f20ba80c07040711501800d0b502d141603c1050103151100d50180c0f881000050541d11180320719030310581640c0c011140103006801c503240802c42540c0400030445014800209940c405040202041048030042c180d40100596100443c0040c3d010794003168001c515192 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 821787589 1250 821786339 821786351
    0x50411060d2004030b0613140403030b01080f0615160c0303020c1f020c010302210703020c0c030f250807080106030b090a0c06030203070210050114010305061806150706 74
    0x70403002801a60550503a50031014002001c056480c1e08580549500102181032612000140080103802248815113a07554000681e62052156145445140301e5a0702281100c85170000400c6028040c160342880e5940a05101c0f030740d600c941c81c00c40043d9103000340c1921860344004074240201824070240c440c001c0c0f4480401455404580c05000410558500b0403020f8121180103c140100a0b03000040e0488884031540350311a800a095010722400700700d90640314400c203100c50407000c0c0c40160100b81d00244000d058103080c4059900100100e01801c18000d28207a1540c42d14202c041c412a54000002081034044442ea150800b03084480308940d809522010b107035008002c28041603421020080006e904d48038000f940807601c0b540f10642100300344c0f80c104203801941005c0d00300000c0d4007075201c6170000034000c1d200b51030080180b20141c1c4105d041c44400501141c01c06030042e070240c003101380c5411001c408245155000f41054070318255908003000d55040f1350081440040c01141030030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 821788839 1250 821787589 821787607
    0x111c0605010504111305060a120203090f010f090201170402040213060302030a0b0a0303020c040e010e0307050705040b0a0b071e0218040b100f180207060e070e06060909040605041106 80
    0x1034042810b84009540401c00002c0301d08100c02070b4040d43d09801402c140d480014081410301c0350160880320000d080094402c0350210910080c0d8100302c82c1c00c0c08903849401c0031350811009000d0820b848001c464100640609500001c204100b04241c1c000b6650450001c07600f1510703507030b04644c600d04148003000035181d20f4120060207940141e030101c2a46040810440c05450850708100c100c07507168008105095141c0c06000180c001d11201c240c65568941d101c50310402e06100070725065120740094000941098204000c031020342d001c060140024420602140a070340d01101c0c00c1680110072041c003041e038009420502c4c090140029002074201142002c1c050308070246a014601c101301c841c0582c0c1d00e902e10b041c0d1041c0e031481615207006907104100107109200700200d20034201a9000341c68220030307845031002e58240001c004010391001c0000c1001c4039031402c00d9a041441260803500d40101000000d4400101900141c9030300ea40741e001c542085008130300e50113513010140107103444103414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 821790089 1250 821788839 821788841
    0x50304030c0f0f140a030606060203040e0c0a051608090409060203010302042009011206030b0103080301150e1e062205030c01030e030a261504110c0a111c06 69
    0x612045914a01c140d00101d9034a9401d007402d020342d050001c070800d560785081c0f501e5a0000b0742d0100c2d01c1d000a840b41000c00803401a014060140485400035581d55240c40c41d00c040500c001415401503103411305c840840258001c046440300c445005601c0580251404c12484520900107103546c4140307800301c03100400515030084d41c100ca000700c070104800e00707140e1030100014040c100c0100b40007608000b40c140a600800b4107850f810b03060600080c4181c0c480e42c40103584002030300140c80f040808001002a1055103120b401030a0b041d00d400e00701114031001050240034082c204800c02c4c484100800119282c000c199801e80c0c212100002d004000740c0c2d03c0a042d0394140c09094020700800c2000902075010380a0140788c140003030021840d28402c854121040940561450300480c920142824a4405601f095008203030711564482e040e401401003104685a01d24a2501120103100a202c0322001292070032400340c000d85200720f0714040200041c12854107081100c0d01d030710086480750034013a031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 821791339 1250 821790089 821790097
    0xf1201022703060402090f1b070506090601080a050304030201050a11030a09080c061c1a090f090105010611030a08060a0906090f0518191e0f0308070807090e090a0b040503 75
    0x1101c24224581000100b419151a000c4401a40002440011a00190803c0c8403a0741c4075014107900580d550b0035005d0040d03168020b08050301c45078090360503c10300003014800c1c0340c010103182c0020040e510340c80c1c0c3c4154903400b46120203070500402140200400d40500400407001e01c0401c141c9546040005010f002c0d070b40a0b006240d1984500c1d50b4070707060783c1000d404441e45422811002001880058036410203090340c40743c22078030324402202a840303d860701c400042c01521081c0c10b035026460300700c460608441059001e00b00b0003c0c046840303905c0d004040100c6004400901d481180b6946180110b54603200680c0440c201525080001a080f080f0b41c6c840400c0503002481842152501c40e2212043e00c0c2c0080015010780004c940100008100c0d07000582291003102800d101c2400b0920411009503000b0003030301d00f0014004900e00300360b1311940b110341c03180c01401d00009a0400d460024a0140d09000d00418030951b000030418941d010010180c2c0c0c65032101c2e44241502e8540740058481c0c02c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 821792589 1250 821791339 821791387
    0x15020609011103070507080c031306090806070203030103020d12030b0a08010c020709111603140d06090f0e0727050114030f030703120902040b0301290a050d020f120102 74
    0x110700103101c240b107803105084a000c0c040c19903c003401c10610f03032180c1d00305038000030440405110400048981065129000f40200050345501c40c02c20300d4461641c4c14070340002e102c1011500100300600059441c010200006604422050201013001e0804d6004010703440c41140e2203145d01200081c010415084031a0344080d503402d8407a00e950710f40407482914a0900600c02c146408d00030200c0a064800044005500a00e090344480f08100c401c03400660003011030f80c44441d100c001c14095801c46001d00310030b07440b04c22020007940182d01e840d2512007002d40036900c1040301c1880d450300b0240e0b0004c00c0c1c0d8003a46400d041080389507035a620030403441c823f050665000780100700c4030f80c41c041d8004c0142c4c2c9810760561181c00c8064a4106814020012000c0c1260700c00d0f80c88a8a840310f4401b4420304d00c101c000304c0c01c001510702c1000e41010410400c0182203109204403502031085442c2d01c0c440c079000541c1500c5922066142c000001c440c08985403a695003503101040007102c4060300e20030040005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 821793839 1250 821792589 821792591
    0xc07030503090a0f36020f091e010e041508030f0309070f0315050c2203060f0b03120c1f05040b100806060f031e010b120a0f0803060a1502060901 64
    0x1c0d42d00c0004000a41142c0700382500e0320312901445464040340c500c1c10018182100c03107410b000009800b210106c0c0c1240100d525421f04c00b080d00c84941c00c00710301c450b80e0301c8061011038804420140c00200078510410426000c0c0342c549508541e0100000d01e107501900c8100305036030f1030b0b1550480d140c903142c20498655000384141d280c00a030840160280c20184c1c0d80240e21a58640703104040c81700038050240040c0620007080000c2007007201c607000e2894103c82d55048601789545141490b038240c500e01100300c1921031400581060550f00040da045a1100000700e441c1c580802a500300c1c00d06100e6030840e00303001000802c22590400c01c3d030103d8443c500c180c4013800507482e24003101e00d00054501442c01e003030344100d01064039481c2c04200d042028200038112004407521100c1c494160403038103500b64160b911560b20b81c8492410004003109040400010b0900e00a9600c0e02c0b0105803400c200640307c41c6000011405a865105150002c0c0511400703a42d803100718000025600d103811a0191065 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 821795089 1250 821793839 821793859
    0xb0306130207050616090b03010801140105040b010c0f020a241b0b01050415182c070e130c140f01030912050d020c15180610030b04080c0703050309 65
    0x500301620a442145070080014201903403038081300e01c1d0011083d0f20440521000c0d1400103000b801180042d4040c04201001203078020b02000501d82500d410f03000782d0b200703a00b01000c011940c0d9000006600140c0c101105040742d4080d4004078840c1c000c0303038202c031100c0c0d00d080e010500014540c4102c241400416a40c0101d40310080c1c640300c0b81d44103180001807055841030010000c516164101c14080c416219010360240c0d42c43d0030100000b00d60841c0c4000340c98a44a0051a40e1580c0b445070030b001c1800803e040d41c160350b18488644a1180d4016414241401c10201d10340d100f90882801d03c0b240d10141442446d5294550100e20034642c15406100e203080c015000c0e2154800d024401c900345e40160742d0511030418603c2507035160007010740e107180254203216581d5000001c00450110040c400080c2c04c0301c1c00c24036103a60640700103010700209a880002881050b2516041c00412290083e4031820303a13446901c3e12861610030303e60300c0c8080d0301c18038402200b8004080b00800040d00308440719408 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 821796339 1250 821795089 821795119
    0x61519170c0a0206160c0b18011d0c06040b0406050a0c170301150302160206091302070b060a06080f160306030807050c040b041a041a090c0403030339090902040b0306 73
    0x414030921406030008003440a00400203080d082da00d500071482142c1c2881101d8a100c0c11801c54400c0c0c4110308203d032520b90b41a0034950144090202d5040c155200b374a424140403142560b486648144001c20200260b07410340707640702d101049102540105010054006000c111141390028002d8011043e2a808500c9000d4000e208980804508843c4100203440c1d0b9002c000681d0044611036421516040320712002d13501610040200301e10a402d6644981441420301270f80481540004042c8101303a020f0100135000d02c51010741c00b10300c41c1034100c50000c00ca8000c80141c5221350008043d1107000c00c8050400c003001c100c50b08a04802e550810500a036041004180c41d0080101c0c8001b604140d03011401307003000d40080e4003024095002200c0e82001002241d02e48408a40486950001050902c10140d050150903c00d0041e9902030494440c402032002d0f010740ca08000410242551406940b8a806101010000c103400700303086440750b644503244c00050740708480b403d206d44000c600c8402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 821797589 1250 821796339 821796361
    0x309090504030e01080901060b040e040c0803071e020d0204020f09031615050d020f04080a03020c09220f1707210c20060403030f0305061519170c0a0206 67
    0x40700729016980c00340305080b5030300107490100c0c0203400d103070071075480381d4010511058000c001c000808050804890a145c03500b0007001501d4650446282da4000300a004089418003443c3c04001455040364203645e142840099844502040001e40140c00800d04460b0501c2c00f03800741c044080140c00b0303580f181d140440ca2028210740b900403d80541c83d87c080020500748614090005814a08030042c42c28000e24590301040e00a940b00b09955031008000c00101075061049014010040c1c4103803607103050525580d0944c0e0a8901c40d200c40190418001c0b060004080907906e60f942c01082d14030081d0400062441709074085a0b017a11020140c0180c1d0b02a05460280740354121807070303601d03103004480f1035079004c00700340200051043c2602c128440004596074040108001d500c25102c0081c6812a404040c083c4e40c1c0007040c6600c507600f1f594010b080d00c07034000d08030307101284200b1082050404100d005d4500080181d51120000548010043c5500303400e00100111165078003201c25a64403000c0005c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 821798839 1250 821797589 821797591
    0x20c1203040b1605190c050316121b060e0a060e1606090b040509090a0b0901021e0711060d0f06031101080c0a0f050702040209102c180405011e020703090905 69
    0x107800240c081000b03548104066000d048919494981003400541a1f01c540e03166403c0349003105003003005103a000082080c181c040c00d040801d141040764a21610134100f18040e400488060040c0381c80d103e010503481014450003500640c02700342000082c14011200d135842150382801203d040b9081800315810b40240f207500c00712118140d03c0380c505401c00c1c00348400c54001070082e01d030501c80e5424000004150901d00c7d803003001c840d0001a1610700000040c00030f03d554004c10b17a80010108030213401314a6003250b180525806480181d41d07440c100902c64001e12503085540407061600e080070040101c625002500a9401d9a400c6556140e602040145203d2300d0f01e000d01294802d01400c51aa0040014002c40c9000500060800786203001090302d400450702c0e16400107080c2e038000144c00c0c0510401205100762400b41314105001140030484900451014100144240000800b080025006a102600c041030040003001c030a6000b90042c0d00402e0003180030401d400c6002c00d459815110f02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 821800089 1250 821798839 821798881
    0x3160f060315031509151514120c040b01112512080a0e0a0b040b04030515061804150c0302030a0606080105010e010509030a0203150910090c03120e030106080a02011403060901150201020c1203040b 86
    0x80d140002d55101080014801e4003002814021582020b1080c3b000a10181e0314000e43d1907280b80c140540c1c00c2c4520030210840c0c00c00d00d0801d0941040001068504c4140c0c0ca140c3c1e803a080100c5942d42c07150001302c0741c07207032030f403040162003000100400c5100b54000500126031003142210018468000040440c1c0001c450064102c0c03a84885941100048143c0c217410034024420341a00d100086009404e4842d01d40c1c400011036000814005c0a400368840d41000741001d1800c0020795041400080030035500f000c2c8181002004107040d5513650b820706c200c80e045030303004041f141c0d12000c1409000b880542190704035018010030102403082901381c003038807520340e50103254510307414110b03600c150bc00030201c0d81c0d80c0108205400340700d9032601d00744103040161900788003c003401d844a100040500c1000c80c202c581ca10350910a101998994107001e9056800b0700d14000030350404410102c1c028041c542452085110f00b1003964840380441c8010750050b03004420220700d43d9180140e21030303803d9901c050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 821801339 1250 821800089 821800093
    0xe06060c0c0105030406020910030c0e12030d0c0306050402040306061d0f06120a0b010e010f140d0201030e03160c030b071d090603160f06031503150915151412 70
    0xa86a81c0c0d80b180000b184d2082c483e000043c18005014086a84040c88501c1c00000ca42d071259003083d0607421100d101c1414000b25545081010b20428032600c80c041c5032520b1208a441f49100e100c40e50203600b2810241001030411500c90340d0301c0c280100581443d00c50a040c4011842c40140700511441e120b0b4030961403c2c4141031035480303540c02e002810074080b0451016000c0c0d1040080014408007580d03000f07294002c49500310754105a5070245512140d80207407260118003018a5003601c071121140610358090800240b041045031200d4254840e88801c0024a0508032886080051527800001075030b000e4844c510955a401800b5507003c07048188088482c2c030128600401464402030141e030244015040d40c40541100500d07000b80036944d0001c0c841c61703140c0102403108660601ca100540e0601c10810300d50146551908000e41107c200424411a150316449003031060034101c0d01900d580b40d00041240d411180100341110080c0c4c000e40c00c0c090344602000c2c456181402483d00c81c00c1003000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 821802589 1250 821801339 821801353
    0xa030203040e1320040b0d051203060109270b092208040503070603050f07020109020a030f081902100608010b130509010902060a051201080d08040605150310060e06060c 74
    0x31030100ca40024204510004154640d500113840403a200c0c040c45104e46050072000c0407202004299662810601c0c00784081c143ca500104500082c032a2403142280a40ea51302e0b228000100c5205100390801c0344034035411220050703480c0a2440744030715041c03081020080d8120001c2000b0711a00161038480c0101c000c040300f4120248182c12030806580700c4c61009241c40c4e40e031004a801c04002e617004034003181c1d03540200700c000030060301310315400789040c802041003d40079400201141910700001d40036400c0b000a0004005800040307d00c56120076101422804600100070340d03412070b111409100600b80304ac0000e82d120140101868844014001c040100411424a0040070010000c0c0410b64880d8400700245e01c1e00c0000f07004580c0306a60b50703a0751b910041c035507000c03208040c1c1c40885140c0c042c602030500281d0012159411580c0300c0b201150545130303010344a200c0d000503590150316001d103c01c41501c60410f44c0c85039084a2031032802c80d541d03035245410002240203a003c090a1904400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 821803839 1250 821802589 821802599
    0x11063a05075403140705040b030c03030f0a021911011710170a0602030f0610090302060f0a300e0601030f1103100603050d08010b0c0703060c0504050411030601110a03020304 76
    0x250780c1244804400303800002c10303940c0c1c44107000c1101c2201104000e8114501c1404203042c540540401102d0076001080e00c4d41080000c26564442c01921111050b004503000c1c2c011071080c05040d0441700c60f900907003007100403800c2400320040115103643c045011200c070500c8601012241c10b114401c40090b040f0705a242a04100508400103480501d42c020888004006041407014500641d182d0170a0752940c60031006003d00c20800522503014801e10340410401603403108200c680001071200400c1c0c9404540c4820350306c00c030261111007040c100b044800007003288840e00c3d6840c07002c01c1000900c9842d1a1382c4100c1d407540c000780005009601130310302d0200403600c0503052210280000c0d0403948240c1e40381d0460011503040750411201038000c0455000541d9001e0081400b61504682e00c3d45031802c81c4986640d07403c0d2030f1200611240d1500c64030041d10703000d4804c3d18010074011b03200b4090000302c2413010807154421034085011804401441c160540b00041124843c2d130b01da0006d502e01820700d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 821805089 1250 821803839 821803967
    0x120f1b0c0a1b0906050108040f0305130306050a0905100b01020a0b070e1f030c1d090603030910170f070f050d1b0c11063a0507 56
    0x221038411107109a100d100005204031595101041600262008071410591060141c030303ca0791105040044000038000415100e8940e14009645402c180350345403006096107000d04040c0e072001e000e891820040240190944d00b100c80c2d440d1103a03055803682c00c0c03100405000c032804001a1801a071008100a0000d00c50030800758000300c545c2403a442e143d20a40c001011140e080c0e01614165030100502c5815070380500490592141742c0c01d04c04080420282405116119818510f100d4072104002c90010346090044070035054000c1c2084001c0103880300c028011183d00b05000305020041c10000e1000d03040c0c0f4a00c40e004081c2d9035549145150001822985600700c680c20703a40341c1e03698414842c11303c4074001d0405100390a80c0c07905101d68402d41480468211081c11550040c0707400c22100d136140280031510404600d95a041c441c0704009100a08801540ea80500c04454901014403100c01d030010b8054141158540341c0410400d201f008690b019a6511f00b06000180600003025501c420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 821806339 1250 821805089 821805097
    0x605010b180d0c03020904050307051203060942120a020906060309010e070f032010030903030f18230c010804080c101b0215161205010803120f1b 64
    0x2d04800700201c0c0d04c90b0001000d1000c142e4048680342e0001484008205052020000184480c50380c2421450144041a050640109000d020700000c01c07514040d44c040000303400b0810030414000c1c420542854200c0c80e1610b0003810300c2d104000d07544400144400c0080c8003440c0300d602600b820f2035500d8080510000d0740014240e200b170340d522488508950401002060001c7c03400700700e0501c800d13103141407200e040182ca911180c4104800d84840d11300b40c9480c2c055641c19401490005964005800c0481c002c1114005a10825042040800d40d03954803c004410300e6004621140d030001c1e40803511803e0407022810f44407d90820401148658050f155081e80a405160582d18110400060a0a041c9464420a00260f40d507283d060f046d2401300f04d040d240b40c46c41c00109009198040d103265000700080046240d0041605034010051013189140000740992001344070310358640c2381040d2283c100203550149540d60800055030014406503850003019101510100203854004814007540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 821807589 1250 821806339 821806343
    0x9020304020a0312030c1d0108010621060f0501081f0b0a120207050d020f07080601140f0d0503090f010525110a0e09060705040303020312060301060b070b040605010b180d 75
    0x120031100080444d10244022580005030740d800665182c00c8400039046d9080400d01c0e41401d6181d4600da68179980000c013a90646210f81407a20021510880c0080f01d405642007280c00903040c0312f80000d901da40c2c10712003410b40e00c0907210710341d21395259211010901d0b56a041d0000b4001010020845d4400c00c0001f0650f4600d14078101c0c00015041c820748003640e000e4081141d03903620100511440d5903041c402e502140121030701500815140025007a9101b006014848840a41040b6008141e82d01c000341004a940070f0603141c2a1000b03400d02a4403a00701043c09801105d120440364407662055048a00199a20304854210003080c0011944264460307000c0b5241190f103540d0305465950110060010000c40b00f042d0070900e0030108090074580c010b80102c040c004240b00a20000e900401911001544501c124910b0790b103210020340540701e582c2c0000034803000002d501c000d00c0240074a4604c02c40c0075280c20b0000e40d070f803200c581c1c0e6544a0fa03204805e41000354001400380d0302c4c1801e00602d0240c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 821808839 1250 821807589 821807599
    0x219020f300906040e040f0204061502030706180506040b010303020d0e061914030a060305010b120c091009020a0807020f0d0e0402071118061305070f050903012a030605190902030402 80
    0x1d134030b40c1780056111200355420744440d078841c1c0c41042146442e0299102900e0307183c00a06000580002c065507034010403500070b00603038035100000310b82010b10700c6c88464141c00030100c4017141014149520030b400c0a0005900500410b400302540c64062081c80601e8080548520702e001240003001e1a81790b890b141c00c204005152000749078200c2c803c0040c501800341a440050400c3c507524200e402c4920207400b144c000e2a034a4409140b203107001c500d48056210558100400e56503488180c03000c1d90342c0d6000300c800e080c804210170208036448002c0701c0c4114150703021150540480da01c9a80d503100c00d54200000550104640c00ca142001d40240072964807562181507143c04113130000e01d000f222020070200004c11041007102528244001c07011f1001903110420440c1003002c001801152129103045c00d00c00005055541914250700c80307903000c00c0c480300403240310304504408140701d660401c007440020304040000c07405185c0400030443c00717000b640c03440c00d010345400b4640029410042c82030340c1c0300c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 821810089 1250 821808839 821808847
    0xb0109030b090c12011a04090804090203040804030803090a1a091c020a0203011803090506120f1302060c1b030f1e15100f1202010e0904060219020f300906 68
    0x113481d001c680700c0d0f40628000c00404c080c0440c00301d900c624010700e03903124402d6040a19070700c04182c0500448081d01e101000150f0350795600c0c10404900c1c0f00399400102401e00000400100c000c0200348241401d00ca551800961507400d040089400000c2d03510507116005500403003003041080c038032004241c00c41c0c01642d044661903000a070840308031003c40700d80400d954140404065000702d804000c3c0c9801c8070b80604103009a462a1822000140354103030911407e00070403180300bc115800c1c100a0b42c01400755a44920490820381c903402516030700d4282c0350313010541a00c140f4010075007141a003000001041ca810840340c0b2038100c003540c02042c281c180220305040820069404040e841108821811081c3c03078a041c94004200d0700396880441d8200590710b02c600143e0b4070035070203002c0c1070701212515055112803e000b0000d00c10055402d112510048005030704980124010440751140c80650f11144245440203204507a8680490300c2161640b42d012200071241007d0300c04e4510144c209810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 821811339 1250 821810089 821810113
    0x170f071b0f2607120b04051203090d03020f040f03060f050c16030c08130e0118020702010c02060a03110307170a1404021c060623040603050607120b150a0809010b0109030b09 76
    0x3044046481951042c001c02c040109020041021800903c40c23082213a1841c030f01495459102c1d1003490030380d020190001001d1800d20807031026900640200c100900d040c603501d1618100400d80d58100c980010f0034680012102102c000135170301080e0341c08070481c1d004109560111604003500100302d490303100030710a00703684021700090400a0008100348204a5042000a44d501c0744108002000c440c01080310000603603004510841c12030b41500d11580303c000414080d000b82001002800c1c82d91004000c0000d45540100040400710702602c03070050a45035602c80000391000d1045504200130380d50085801070a0240008000d07009014148545000596411080e1000fa80c0548604003246a0818400314036074003942d46400700303c0b820030085107035503102615400000c041360280460b03d607a145079001d1640100050400c01040c00010100d9200e02120f00c4c1c000aa40c2c07000208520005004500c05124000041030161204100d542c03a6540380c52400c0801002c1c3c10203030280c40328610f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 821812589 1250 821811339 821811359
    0x1f02030f03040303060501200307240905010c0e0f18130f0b070e01020607080f1503060a020d14130b0403030e060f0f091504170f071b0f2607 62
    0x100452007580c020a10928000c0010700400c0c2309102030382802d0700006007000752480002294802c3c0e502c0700c130f800d055251600341044182e0f40401842c0c60300b0b05222070300040100c19401000242959110144501c40302d60901028424820740c06800084130320200381e1115004400540c030040d086980d8040c00a0340d0b8038541402178041c400c5611021504c20f103d80e1a070801940800740c1020303c01080075280010000f03100ca2000382844240c4046100841c00c800102c42034054401e2014040f14142e080840c003241c002d502c51062003135503a1901d00410f006403021840c41d03000d4518108200c0398003800d40c440d04140d5901501c2182030594520003441402d40601c00e2912034101100000726610f4521055407003000020000705068101550015250040f40c01c0260483c1c0c200c0c180032080c4040e540c54040341d100e92003c203c84402c010610700108034028070304c11803000d030340c201c0342031005c3d41e0700450020920720307005481d0401ca04804426144013949045400a8202001c444d065035451510352 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 821813839 1250 821812589 821812591
    0x7080f160c2301020307020904330c140f0a0e0916110c03071739010309030804060209030c091603050f0103120f022104140f1f02030f03 60
    0x210000380308a4204100480300c0941c0700b400c0440c10141c242e0302040c40c0005d40341d10800200074490b0ba0076001103814000d81c0003520020200c4041002c00355000e01c4003140102e0550307814448518106103131540258032179452051400038650341a41814071050003a0800e0304080c51030030070010302d05510003850751080113040c0140380561110200406000004210100601059203107611401541d00d05460010b01a0200ca610400321840c1540c031607000c6d800e0180d00c1440c0c1001500300c1e00800b011030340902119940019501402400b8042c0700b00541c141d07074210b03c019001c601603400140c0490525001003031000c00007000c0c0c542030124000007640f00802501c4a0903d00d01c900f8030303610078541610440d5040881001f202d4010342c555910100c0c403402d19a921410046498040b11505000300503454110710200c800c500c1e03140203100701101e1500135224001c40b85c2a2260800101d04044030341452400d40a0900c005e00701c0e0030306802850b400c11000800c210303c020000d40b584510018051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 821815089 1250 821813839 821813843
    0x4061202210a0c090e1b10030209040f091101110d02060c030c0903101e020c060105040e0a0f11040609020a09051504030507030614061512060109120303090b070f0507080f16 76
    0x640800b5064017524144030114248152001403c8007401c0703558003d0007481c3d950a610340035075900c00a4010a015000c0d100101c0981d9082c00300c0c0c84200181c45201114059081e624800502013101c3c0456842207450a00c0025820600100750240b80240c02194002d9001e0f09040c5040e40607000302c1c0c5005200d440803000c0f9a0b0f101101d0071100c0d0f00b0303414a0b03403203010200c05604250704901803d803102010310030144115030300c0101d00034580003804980e521941000100005070716600f414600c0004076500244120b142c41390200b1303128014425203044041d1542c0740e55216092000744080b44402012240b1044010700c000000203204001000c0994030030301e004590404903000c1c00c00c1a69024107403074402c03c074000360300e24030a002d01e041d074800f404501306540341a210580140c2d031030040c40e0050040f10b54401050300505400d82c02440c3c801d84a001e030010181d0342c04c2001c895000d007100304900050400c018103004903000502030961120b42c0980e440c44d14818181142c0003809101007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 821816339 1250 821815089 821815091
    0x4122319030501140a1517070e0f0103020c06130224041d07050307050904140f07020d080606220909150b0103021c091406100504061202210a0c09 64
    0x4240d1200d07a040c05502e0052940d94010702158107103a00081d4480c5a5004208040c0b19205201c09032a1040140010210510b01c002202c3d0030032100085c400203410310b50901a09450074492000d51180c030840f140c68182c40c01818840c1c803003002040402400f40004e070390000c0001d69100d45800c42e8501c400d8600c802e51940c5039280e00c0d01d214440405442800044844051820050300c02e0300007003181c0e407004a0b07182c0113603510010300000c8c1c01040312401108030325002c44200a00700704400d4803a402030809800f281c120b03518008080344e900e00c04039542c6800c910103204020302400348902c1c1580c4080030807180080030b510350b11180112806803205850040000000160859192041c003029900a290562134501110300c0009400404c14680165503611240b00f428070400c650b00b803540c0c0451038262152810080050982d0550070b00406114034901000001c9084c00400c944c040c09601a00c070b502203280800c400306001100403d072640030300400030000d00094010014330045c0241001c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 821817589 1250 821816339 821816377
    0x1150804020411180a090501151b0812010e09120f090301090b270111031306151e05030708060c1b0a1506050915100504090f0606080f041223 62
    0x401030600610340c01391800711f190000611504401120724405265181030071406c80030520902c0c04844951304000d0710b60680403642c00011494143e201e4100d441c0a583c1903a03540351614000d4907130010301c1110612800c20003000b02d80020b8000900800c450003000003a40d030788aa16840341a410884072007080c28500311414104000000b111002503540400070031440f40c01012002c15448050135640058645031158410031060f600140c3e01c405072141e00c0d01c40d05035135072034412007000700740c48002c00200c4424012429007070018010342201c2c1d00400030326158560112070030a0342c1c0100040703103070702d0703d106010300c0804030030405c54810070310450000c3c034402244642c040072205140c2203179101e142100140b0000c15050980c10b58005d504071502414800000d0042c0c0300341c41a54080e0200600304a803039510ba0890ba407000d001c462103030b00c45080350b584d1108140500001100c008000343c620b4500c1050862244800c01440c5842549000e144e8602d60149400e54000c000d2080e45800700c28 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 821818839 1250 821817589 821817637
    0xa0e0f030a020a02012001020a120f0b06030f06030c1509030616080f180106060c051c05030c03040215070809030d140a110102040b04030507081501150804020411 71
    0x12108448051550103141021034540c0000d440b0035032420040c0c10403070030031012044102502d01d03440c02d601c0303110001c55603148400da0180610b2545c2c00c0c1683c00b58036124580c45603000d40d020b0b80407042c40007407080b8515511444421050031024190503014811601e49820948070140b00011030200c0c2000e2a85807000042010701c3c0030340003810798141d4034500b0340000045400c501c00c141c2103103c50000114a940b00c3d410300e001800401e1500303070b0a60138601c1c0010100e030007174943c241d1b07a8041c0d41a80c6454240101e2811000c07264215040050303000c100182c010811304000c2d50300144000d164604030301d07032038005a4440c0c00083c030980d02c017240001d200300706d45030802240c0c062403840d007880400030020410a2483e400303a40d07490810f200504640b81d00c3c0d030302c085d4116806441c182040640342c0d5103e00744940e17a00258080e2044a10503072103c00c0321544510803840c1255541487e80f51201112030f81114000b034054000c03600b2640f40c1c15106829610580038003d954008594081d240e0014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 821820089 1250 821818839 821818843
    0x306041b09060f0302060903010e0d051c05010609120501020f0307080609071718160b1c27050102072f0108040507060e0616030905010305061c06150e0a0e 68
    0x681c041024149040700400191a800e41084112a01240c41c180c482240380d000c6409481400c01d07041180c055041210306460b000800b5081901300014900ba8040c0b41c3c80005003105d04c20f000b080045100110708000300400300d4010440244114000b42c2811a50b136620045074000340c3d424400700b404642000181d00b000350301d0742e60000051400d0700c41e82c076112207041e444d1314014020f103241501480e00d00503104000c220343c5810300c00041940c8400c6a80748100a5150840c10082d541440b01c82004121181680203210100401c4040c482075403c0803800c014805200301c6040b40c11795000e020101c04540c2181482301c542924422180c84124410620a0071481c00f072445810300030041d007807001058000898005940460410400b0f02400c40001061400751900e10704003102910030380c80815134058108800c030761003030720309000c6070700c4000c10040c0c4651190300e016820107202c455103000c2030203074004c111590120030041c5136494441c451340003150070803108541d0700c903210450000f0800342 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 821821339 1250 821820089 821820143
    0xa05100504021215070e0a1802121e06190504020a1806020114180f060a140c0301050121180302240f070804030e10170f01081218030604 60
    0x40d0f04040d02513501e1044007100706901c082c1444082091a03102440b8075100c55942030003500041013007105074021041c0e05000b0717604c45600029040c0e901d101291140c505060700ca1b954181c040302c03110b82c50f5503410074001c0c115081c09043d0303144108003100280584440c03000f0300d02d0720801d84c0c0f184001c0455112a6291840b980c0c800800c40e890b06410401c201c0000c800a40c02c0006000b00744183c01414040600c0c045400090494501808051114001903a480641442c803910140c1e000c95a540050117240c2c0030910a203070100d40e280e600419030f2400c1c64042000307030f07610310320000f24220a0740546d18900354940d02100035078803120608010905040040d1158085054400030501e0300070244480420040d1219040c0080e00010608250140348607410112025041c00040800c10000802840101003000c58a840480c0400e961f500334500180c103132040c3c0c100414405034080901e8405522101558909605120701001c0542c4c0c01c0c0415400f50b0b005405000000712940b90040c01098 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 821822589 1250 821821339 821821369
    0x2402030a02070b07060204050406180e0a021c030c12021605091b0a02030d0212011401020a0b270a110312130311190603020d1a03070b03090a0510050402 67
    0x200030310400890550005605050b18420042e240d1219228a00580030b8000e640109901c1030618a000c56900c40c5039145407551902c1c0322040c041d60070110030032602e41c0901403000e5000140104210010361800500c0901c15200c0d02d8141415040c684a038224140044185001070f001881482c1d0f51601000c1002c0c0503100c06c56400c5420f041c40750300e0091070b216048010441e100d000c6101e002c020f00a1084d40e000c040d40000035580d845400f1003a0106080034020070000c242c0c1450702c101a9440000e00c1040103902451401280c0c440b0321010450a00f90903500d04850f031800c0c217071548080181f0944000c60300c110441400042c0d1001014204210900420300e6100140301c11859030b4048158142101d41064a201400f80e0b1540402c0a13001002c0107492007104112000904c83d5140e0300400710080048406c0100280038010810090054606503515a206900601402d0b208500454102d034106085902e000c503a543d941341040740c2103141201d080d6907107040206504121107001d1841c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 821823839 1250 821822589 821822593
    0x5070f12050105060a03113a0506010e060d110f03270a0320030a0806031204180527010903140406231b0c2b1113062402 53
    0xd03041c0b8004c01d29a010380a510410183c0f20700c844e001c2d0200d40001c0391555000c0d0f22100d4420030f0559158900e04104000b09080418050303603200301443e180c820a1b0050070140d690303118054241c0c042040581011365000c40341c1c1d58403908200340308015001441161000e014890310780c54480e0b1056030700c0041040d402039480c0b80350802070440c54040303902c0041941c0342c01c0000581950300f40807000c0c0b4183c6082d00c034444c4000075829401c1c03a00701c55a2849030340110104ca07480c401c65008480c0600440c0701c3d540b500e039050b50941311404801d800039039110062740e00c120441c090101e011550029034441c00c903042c1c0d556800007000d00d1b03031102c80556012001c1d09104d1405140c05002000d440c402e000141406042900704400c018042d4115140c90069000c103201d0404010819500d8044000c0140c0c03068401c00c85181300c80300c5501c55841c3c3c0c2c00218480c250324880c42c0d00c0b90b29841071001c804c0c0c2c0d030008021001c0300d00540140f150101802c5405250044078681c800e0305001d19641d00400e800f1b43d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 821825089 1250 821823839 821823841
    0xb0a050102120a0207180e061b1803010b040501030b010306060501030b010e01030c02070b03070207210b130309050a060521062b0b0c0901090e0702070504020c1005070f1205 76
    0x1a6000036500b080205001041d554400d41110220b042503641d070884020000e403800181c1400c80c0d1034205850b00340f20103017a114561585100e4250800c440e0103e0743c1d0743c4205002c1012110441900c0503104030020b80086070424018000030111542600102e40f00081c2d0401402070101c24850040034241c06e0808000001141001818094000741558101921400718002d518401d00c1448003c10a603078409850341054507029403112018064040328802200007582a00401e95050b41d42da6040a00b6100544074003501c030f903800412500503001c1c4543c1c1c90740001c2e25101c0b484e00b40010859a51400d4a8003580700280000c00303942a16843d100c052101809103d5a5111004070b0159030305a40400d03000c183c4240c02c00c1402040c4000e0444040070040100380c12011000b05004603003682e546103025250102c00400003003c1e11040016070060600703002c6810154010090b4a903010110307419180c503403d1080540f08110360010000d0030500d01c5011058100b030304d00490940401051100d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 821826339 1250 821825089 821825099
    0xc0f0201091502091f05191b0b0603190f0209060910090203090a020603040f140303040c09050604020f07150b030307030e04020f040e040b010e0705030f040f02030102130611010b0a 79
    0x10b010490000c840b00030b54001114121580ca03000c00d0005c1903600340e583e6104200b0f01074060004e82054145407024200291460100c42c41948048607448400ca40c500a090322501c0d030740c14142e0b0083c00a50140300da203114003054200f040400060070300c00c051098526145106104082801410b80c0e40122101000d000d4a5598a0f181e030090340c0c0c0714a00140c9030b940d4018050b00d01501d540d00650041c2d000014003007409074100c0c4000341c440c091160f000c016400983c00d51780e2032108460203003845c404854181b0070940315800090300b0490040001d8100114003071421220784c0042d40c00c46981c4400c48030000040300b01d019070103041c0c03c204c024500f8404039032009000040803a00e50380c4901da0015101582060408c15a4064101c07800f4410140c47c080c50000c42c140b400b0b008185070a4a10b10010b00403901c501c003140d12980b0450f0400d1181c0c0c070756540307400745800500c0c0102c4c0c1c9550280860038070030745a01443c0e0018842550740d0083c41c4c0c4c40c0d842d114210303011900d50340e0040c1407407a401c0c41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 821827589 1250 821826339 821826353
    0x1030503030103050d08390408070504061202100e01050d021c0b010906020307060b0604030804150318030e0d0c081204090f0203090604170403080d140a05061c0c05060d0c0f020109 79
    0x8440c4080c40d44552a00505040002c900c9400c7c0084999404a00401c00b4000029403e0a0b52800c1e41e0410203981c48620060600c4065103000358000a004100f01140384200345011007543c0c18141903007405c1c0156a060280d810036410502041701050120003d04000d0203407549038002800c0507103502d824040000c1d00d91060b168050013164555030000f4550b1a900c003141c00031508182c9140d1900d807141c04440000725112000d200203414041005900d0203105000d500f02d03981078440c0720150b060310003070000a1389807400507986d010880c0c0d00090405400d02109040d0101051303402d5650341440c000c041122403283c461803149105004101c0c0d000301c000380003031704903400000c1c011424a00740d4000d038617441035800042c251000452508490b41090f0885054411070781c03540080c607518074500004a460480310a03030721990382843c42d840700380d941c1d1700748040a000c0d40701c0c600c201e41c80c1c00224035035170303c40f18015a500b40d45000d00039265030b218260b5003003038200d48002d001c044501d4803610303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 821828839 1250 821827589 821827621
    0x40b07050c0319030e10020906040e0703090605070201050117120f070807080a05030a0b0607021e0103020d0534090302060901120f0e190201171b0301030503030103050d08 75
    0x80140900003452040c590010000e8a5000000c01c0081c0610b4410301001800780103100860328840c1304054942606490310b0003507503100d9001800283c01c00d850007250614813203000e0920380505540f807101c000498414001c66114003800e8001003019450204008000d2549154031181e80c4c11042c0d2210410959200302c41226010a41407900d44280b814000e00381d2041a10041c503c180c0042c80d0122143c01201a51013007000c52401c0090039074150a00c0440e01c201d0310025406810094601c1d1021610102d6106c008010700d001800e00c4800580da0044400954014002605004601c10300b180c24092004201c01c2d4a440814890002034001d455041c0502009108803404101540145d102d03c030846125442c01350280b00c1e103840d0001d04001411000301c1c800284c003910450045d20550f040c24401001ea040c0e441c014100ea0815071084504805440c0c030311031404007980d03444a080c00d0302c003841c0131b0741c040d0018582d00c0d4514035000746000400b4070346000b8410130b0410440d20054048001e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 821830089 1250 821828839 821828851
    0x22e09082a030c0904031706010c02060327030f040302030105060a271401090c090503030a09170307050a080c01061a040605030709050402160303050a050408070f0f021302090315040b 80
    0x31001d080d5010000078140346122080076040903402080006243e440320140411103807402c2082815101c16004603506804a24007039008072013000413071480516039684501000040e801060314060542986082d513101d6010b1040c00c6c5000f0400b803040d07241c00e20a60342c118408582c110a800c0c9043c545801410000b8642c050041d2158507810301f140c017a030480c110070803118050306450342c2c50349030070700040480709086d03000224212030111f0941000412110003203481c2e107ca0004078500f03508007000030b40042c5040403a00081c02001d0002c0c070104204032005e07121304206600d0b100760b2070100c0e0031680e003980640b01c00d418050b000e115150005084800b42c81d441c0c5441e540e41d90342c01d60103980c882601e5008903040b40c030006040f82e1482c20b00310080002442550280013a4079040818001d4403c15100501001001c0001c030000078402c40c01c01048034414203504400541c15000204407100941204203103640000e401d00305c41c50180021050b2141c441c50204080c01d040d190084980700080c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 821831339 1250 821830089 821830153
    0x60604120b07110601240306210507120507170604080706020a180f0603060801050903030604230a1e020c0a1101030e370809010804022e0908 62
    0x8210894403900e603804108510104644d09035070b440a51002a0300f1208006581c1542c09130081c1019210740650401c4440124910000c0c1000340e0401c00560b81703089080f155803059030f8001501c02a9196882c1025000728050900b4a10f050a903007440101d011090210341c02441c00c200004070040c0544000701d4018000580701c01c02c0140c01c1c0c60030042c1e00c4603416414060200084c204419241007020f551160360180035090741e030082d0340c1c00c0c1d450a5442c1c00e441d820030f000181c16030410342d03c295500c41a402c2c6002c519941c449a043d9103032402d81e8030034000e0392603122041c40c00f0703180d800042d0000500201103103030540540c401d6072100d0511030000d080d10000000310355144c0c0b0035000100b24403540c0d82541c0000c0b01e410a001d151803141501c520b0b401d03440d414140448010b81c625000000d0304551a10b2801400350700440301c0103401401260310541c0f00010380b8507080c0d10040c1c02490003032000d50800b91020354501600b0840d0f141d10401c8203902108240440c0c0045080800000b012401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 821832589 1250 821831339 821831341
    0xa050102120d05060a1706041401020a021216081c062117040f06030203101703070b1e040f0605150f04050603010e0f0618030306060426030d0e0105060604120b 70
    0x4c0052048503e683c0006004948145003100c80d40000c20f055000301c0c410b0078454100290161054203030b0180d1008000075030002e100000400000380b004240c1c40c03500d80d92001c0400219a500c0f141500b10300c1d4400c070140d5211800c054020514490b07840600340c2e02980d814004904100b03404e141085200080c64049000d1780d010790a6540403d07100039103251000402c0726074407020018002e42003160103c400000e620000a14607005c8096540390740c0221f4051883d0030340d00e0b01c80400c01790b4040d0103441380c1d001c05c101c04032288440c001c000d03000754810740803907154812506092081e9a4042d1200140c41c0c40c182822402d551070060030032818105503808100da6480e07030300007070060003441da6110040c01080d02240440c40701080d03080c40307040307100050507200c10705803941c641c1c0e0301040b6161508204100014031900103420601a40d0b00c61845545030250011403484d41150003000d00030a6032034448100342c8c1d07000e8080c06403542c801402d88819007424903043c000041c60700d0341c0c00082c6c0f5080083c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 821833839 1250 821832589 821832601
    0x81602030109060e0a0c09020903150c131d0711030d0903030e0d17010f03080a0302031f08030d0606020a12050304170412020103051f0302091306090b060a050102120d05 74
    0x1d0010710710306401520030001640192241d580b04d002e4400d01b01e9aa52640001107540360042c800d88030001c0e009001007080d03800621198080080291036181d5040303091045600804208807080047d104d494034601c8900c607514a00200048040e20100622004c042c06000c0b80700e000007591031510001ca00400c4010250030300f5402008003443c003a106000d50440050155042080c1c00e500c06501d032844c0015a98071251140c82e90a00e0000900d0113508010300c0301c846100340c0113590044000e09a04045800108902000b15415031041003940c00c08240880058031510844004204900240c0460b0360f05995907119024809091014481c001c40482c06018205450200c07058481410030b9585840d00f1810038000090f820403070000c2d0800c000500c100326001280e085800c610301044032100d08650030001400030040c1011051104030710318078040303070081c00741d141c01500401200903e80dd00109102e009000703a0800303170556202942e4050701901c80d400f1600040c1c0c2001000034552120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 821835089 1250 821833839 821833841
    0x1091b03020c0a231b2704080d021204050a0309080d050d05102303122b020d020f090f030a050d03151511010c0305010b0d18050109030906110a0816020301 68
    0x130000b03203442801c0000c8064246815860b2140e5812614151607a081903031058211010034400541200440c011030300140c1c41c18090706a550b0f01c440d0241c180809140d00800c100c200306d81c2560710ba4000e2441d0414960043c3c42c060203004041d01411040034140000780c142d205210203140219512800140780441880032040a030000f807100c00c0b10b50184400342e51a146180c01c4492081c050b000154800010200441d02503031300a00480020400780d06e0240c0003a82e058000510007602041200a01c80181c80206603820302900360135241d110314800d018031300b0b0080384c5090090388030020302408a200004c55001a003418503010400d007008103200034494901d81e014402e06050000400d02d00741e0010749a07441007000d0380080291020403c401c50540d9001e01c41c034240004100903100c82071950390050460941d84400000584601c0c0d51600d0842e24540c50980026042c08020b100041e4000d0007041c2c1e20301040000c0c203403509142c68a42251041c01400102032644000304000c64a007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 821836339 1250 821835089 821835143
    0x4050705160609050123071d040b0a08010c0908010e03120f0405210c010c0905010e0f0d170c06070e0906043308070506160305070f0b01091b03020c0a 66
    0x4024000e00040c01303990746c0f000304e416103d20081e6442014900141c2c1c8203200300180b01c01992180c0203103000c800e41c0c10034000100704290304980c001c80d002c80e012403056024081c01c1c011281c10790714261654035020341c1600b198030200c50309506400401c0a125107100722280b00ea003000e8449010955600ca03450010b180c04880004140d1143c460740c2001c5440c648031000d004001c01c84002803110072103088044442140c01c1c011306010400000829800c0d09146640001c40d40000d000d50080d40c986403640c40c0c903102c1c44174030070714811400103c2c40300340e48051016070b0300b200e510304022560500718000215a11b80040041d400b641c0e40310b01141c4601030710210070854440119100f054501441004400c40440f8016a9410b00ca03444000a90f424601c0446450380b07107110050704c0c0001e99680480d907035070001e1030956640c0352100c900e001190400300c1450003841d01c0c0c40c0001d01501c50b104801108100403000006051060102150781c50740400c403030340c84a91082c40f0b4100c1000c6080d490404001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 821837589 1250 821836339 821836343
    0x20313081f180501090b220203061b091e010e0a0b0d150b0309071412060a02030a02090a0b04060206010504090809010e01051605010e060c0310091802040c1d04050705160609 76
    0x1c01e2205030021b0003a0504003901681c000c085c0c00d02c0076005400c0c080c040d90a0000b0082d0940d200b20002003c04455102060070320030f00d010350900c1c001086001448115845040d40d0f0300c40d4914520480da50b03040380d580c4165250030f07220100050302d000c00c0c644441c0102c00e400309540c0d4668000c2e06920030742c10190f4014041c1280c40743c7c1c50381070112543c0d545284a00600e080d00f00c0d0343e00c032140d051600e07a030030a40022912004200a58034031780c250f0080d400182c04071003282e40900010115a03186134000c1c024284905005443d603103000f000919040044c7c0c009400b40303143c00031070f0000c9030507041240c42c60042030034480100345803000100e1b03540c4207460b0082055020079940e2010080d042d00140f40c104208002c480494032803421019540c0300682e160300310340302d41600402a5000580044034188500001c216500b01540c020a003981c2c00c44010b00001001d1a10303124540360000310f4940c050000350381c20820b071300e84902c0c003520313910940c0c41081e42c042c0355403030040811805030080200d040e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 821838839 1250 821837589 821837591
    0x6040e010603140703180816020306040b041205030c071101210b03101406190e16080a0b061602040f02040b032202090c0904020c0607020313081f180501 67
    0x503035a40707002402004040045040b11429001113400c1e288240a2006e080d45501c1c04c0c2151400d103641d86e4469a8403440c81e03c0b14212545001402503030b0103000300f900c20780c014440015246410b01e844454441d03243c5010702880001c1c410700040112042c15183c00661001c0c0640c03107840e0080068922070403c0781300081c0e20304600c0c10810040e00540020340429800c1e030480340400c03c01203040d8150b50010244420f003910303540c0098080c0c90211a85180e9000448220703c1241c2c41e90609113000000321402c154487d65031900d00181507000103c580d00011090b0100200000200011018440c0310360340b007a60404020f010042d980c0320782c0a105154200d15085694543c3c4241000140c0c0044982c00c00c0c1031404070402d4054039900040e44022540100728010315a60700e001002d45800455629400c01d40c2800940301078401000b03071070301030031041d00156110b13000c2c881602c00c0000140c0003890039400021083c00d4418154080c10703008522007038003281e54036800c084416048040a0050565 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 821840089 1250 821838839 821838841
    0x21509030f212809090c0201060e010b13091e141e1506030c0714010b1f0815190909030e0f0108130201050c0a0b0108011406011d06040e 60
    0x15000141c15007080c0d060400a552030704078400e256900e8000c8412611030302c0080c0407039883c0e022621030320601c84880307800c040039243d884a92082c2111007804207000540c0d0750307690505c061515094400d0050400307800c010310f0314040d0400d40020010032311074401090385400b42070078021f10159041d0341c80e0044400402c0700d0018000d103090700c41c00545680340c40904202c105011421140003c0744101407200502030010784034804c0c85515400100294900c440c240900d074006464041c0c044603810401e0000306441ca010010400002d41d00c0d1046440a00784480714079109070400324495004241b1028501c134501103501241d0101c0c003c4450000000e03c641c000718444646038018011140039542d462050300d16031060024814065100a001c1203802000036174030013244905000040c818503010782408102c094261424030328003000c9480050800061149201c24814095241800300081d101c9051200002c0d00d1881089400360184803900707640b081d1a2181c100301e600800c030403010281740d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 821841339 1250 821840089 821840113
    0x1230f04090b01080c1801020c06160605181504020f10050d06050109060801031b081020210c0f0d0507030c0801030302121c0216030f08040b0402150903 67
    0x9940107004a000c071600d03040c038003110795200e940000e100e0381071400300c00d183c5801c0c0c41c1c07840c3c5201826522941103210b00c0780c00ea0340b03a4461101034243e5091050b03210000c0c003250304e802c000799240201040c400d240c10810f440491003000420443c512074074070019081d0b85450010400003105004aa600410b0704104604400c2d0b200d0b009000192201d0020030805842c0e034011503010130244030713120000d600b6000500c0461180400c01c010407581500035107a0744c0e03841212038140120410049641c6030f40e0045801403090940e00302c0d00301100456282d107000d0703101226400300c000072114012081c509a00190300c6200d40c070100c4961480d048a603039100c03a040c00c010005014110b9041c4000703030a2102001c8002d00461129040e2645600504071801410719000d005800c480c040041c003d025000082000e00b07944010206610303080b03500b07685140345042c00ba0000118030180010441c0c140700f00400300d414a0715140c2c000380d0458810003102461074424080e4050281c040354180154960180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 821842589 1250 821841339 821841367
    0x8150a1214060c09240307030e100e010501060f090503060c0a02150a1a0105210703110403200607081c240f06090b16020102030c120915070807020123 66
    0x104c00c5404603500300f40000da001010700311519501d03002041000038008500054000d80001c0319688584003118200d85147c100c03001a5049032020340b2480e59140e0043c058103a0041c008030340d84415060010b01c00e482d00b030100e55107907801000100049004150307840280d00c2845140e5484484002c07007205400e062002ea001803100910074101d40304141c0070329203d54050b100356038891520844c4c003078481c01141005400e1b401c0042817042055921007054200da001400940042e40c014070a542110961247c03007607000319080f58091003200c040c44007500084081080b036280800503a400c2c01410340c000c1c2c070034010b8841c1010580000c40b402d407240311071034800b038a02c1c81104e0041c5c01c2d131958542e0314141a9000d410728043c14070024020050200c0d0075290701080381c1141e10600c100c03440c150340d070018141400f2024107402d002450005400c40c440c503140d19080f00c2c9500b10040180782204030358541045110383d0070000d040c4119445040181590400c064210300500e650f907075a58400d400e00d0301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 821843839 1250 821842589 821842597
    0x309120f03070e0117040f03050d090507050a0b04050a1a0f070b0603280308104e060b0d020a0603090516030201020a080f0d0c0c0308150a1214060c 65
    0x110000f02201ca18000c99882814400c100e000d14498044184c3c1321a111061101000341060742841002c110881d50410203215021000e07002d00040c15503241050100f0100c0b110a034445940c4e040103000c00d1000350b58142143c0c00f00c41001a1031101401403003004064cd00420848260301e04022030348605100a020010340b0407142202501c1d24a13542d5241420b83d00c5d015401440f4a05040780d1000002c1d01030242c10341c0000d2002400080c055079035440015910103104907500c000000c403100442e049441e41c12a883e16254150505c4440034042c0090004040c5840a0801600c80220381c8094442d5138840d800190080c0038000e01c20744440c0040c0140c440110201c405d0304c5002c0c0c140603810041818501540d50583c007401203100161241400758008582d07803a00d188e8200700011600d000741c0302c0d03400362030010384031b03107a4002503801d0242c1140002441942030f2942c1d501c2c10107075607860100c100152074141729011035000003405e02d2441034088004403080d5100305801e003c8040b01031000b070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 821845089 1250 821843839 821843851
    0x4060902040915260109060612292202030d05032a0d151e030b091f0e120301122603070503040f05030307030903031a13020309120f03 59
    0xd002d02e043c50a0010408100e901c0f405422031309515881140020380301c00081c3c4c40c40420700103c1c4a210544420044680c3e55000410304060f03e80c0800410419643c04942da4900b04505011400c11080300c24403003000402040c41c2d02c06804540403402070202c000e010180c1c0190449591074050305000d0101ea0003582c10b2140c00c01040c0035400030b43d042903c2c44003069064140a81000800e49051021748829075065a0400200c40e000c200a01c0f2001a00c1c8540f0184003c55009840e50030000c2600b00040e084400070340028100000c0c000d003011410074054940000011002961005103040c01c0001c0141c120610000000042c07928002034440c01e113a0050174164290b0640507240b16207480720382c0c12083c1c2514240005003130240100003841d8054060075520740c40381000d613034860555204460180200c5d944500c03c600703060b898414548200da0218452102483c0305000078900c240c21228031610b1900000050514242031009100c401103200340380380c488184c2c0b441080b0a81048500c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 821846339 1250 821845089 821845091
    0xf03270f07050109080c060405040f0209130f0c09120f02010302190503090f030405030a1e0803130c080706020304030204050c09030a030518030109021309142d03031608070e040609020409 82
    0x110700700c0d00204040506c0d8500601192030070380340c4810f000250a180107140710311582070124102a4481d49070504514180b52000104416104946404c85884009070020400c81e01014010948242c621123030035500070018030741c0c0c0c020700d1004070042c0c4100352040114102c2c20030180c40880d0043c020350b0042c011030040d40c100315038543d0102d13500d008500c00e850f03146d8022101d040109400b1006c0000300c0740c04031540203185505455000c590b91043c0d5490f007003201840f00c00010312140100104c00382c0000030240428903d405802566400b030703400040d22543d03803500850f102410171030454100000c0681980e0f00704a40313040103881c40e001101d51200e04040a564120a4941841600100d07035000b00101f140c1d501c0b401c2032400414070800c0891341c864031307052038070748691080141d101c4041100b00000c501402003500440340c0302d82805445607d90042c8240014092190070100d00d01c5460302e0f040585554112040f24a47d0000340c009800070f1505802065221a580007401600d00843c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 821847589 1250 821846339 821846357
    0x4270506010b070507150509102609060105060a02010906050106091a090d06270602130504021204030e01180e010323070b0f040306110d0509030f03270f070501 70
    0x35141410f10410ba001003550300301180134803141074401c1040450b261146401d505000690010400ca055440c05900220b01c80754410048100c0d080c501e012501c1c20348600030304900b88500d00c0e581e07500042c000c180c400c4002007007000000340300354403d8644a41202083c031140d6581d0340040c1c07030002203000326810b510300c0103880300503400044100c400841021b0706c0c10880301555112031005002c51035040f094801821100c07100c400b07565211508042c021400180d0f1000300c40300c0300d200313081d0382e500c114000c82c01071140b48035a41c10031042e550b0158050421051004032440101ca294007124190b0146560241c0301184e040910398245050b644242141001c44105440000c0c03c1005011030814903030094500f1701c42d03a0340c02d401514a0700311030017000f400d0540304c2d5580d0080d22500d5510b294201d0f408600c01440b041c039402050b8015110320040c6143c941c2c8015984070b6880010040040445541110140e926041c0070845640e100d03c001d03117a403041d02c80314483d110001407180d20f0028100320 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 821848839 1250 821847589 821847599
    0x1e04050f0103120c0c0b0c0105011701110904110702030f0a030f11030703141b01020d050f040b040b040203070308070f12050c0312060a05060a0c0303060b0702130b0427050601 77
    0x2400103050b20307003001840c21049a007400032a00841507070001c490100c828000010740e205a980a0500445128008036503503050401642c00107607003010442e100c0e8144030070702c0c0002c000d8408942c84088140c401240d10554107000e05014401d151009415205000e11101040004504401402c0c480e90b1950007140b01000121440b4032a062010026003003008200d00180c061003181c03a20f0000c2110035400c20040e40c12421a83d0484448603031241d40014034a0016441c900c60307998405881040e21103642003d4030b1321402e41c00001d000070071811900c8003140075550104803035001558400000356880902c3c0c600001103a5400030b040340d9101008810200741b60144098542030310308400210309280400240704040d410182045030000002c02c3d0115403031b220400145a040c1160702d0b02004002580f80c0101101e11a07802206008001c4c0094001030b5200b080555065a4041c804915010341a000078001c0070440c501d5004400c031b10141200d40f00c41a020302005600920580b9103980c2e0321 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 821850089 1250 821848839 821848861
    0xa021c0b06060a050d0b12060915011d061201090b0a060e06010e011b020d020303071a0705071e050c090f161103040306150b0a0509040e0a0b07050d0207021e0405 71
    0x40f8500d0000c18001d00200d180300e40154800d1007101c1000b00a80f080081007040351307080040990b0710b81070641104a84031103c7c40300900d4a07006244480d80c00128100340d00342030f2940701010300b0301d40c4200704c4034842420f1044c0c250011b540c01a08100640c429061030021300c8020003103486070341075500038600000d0044d8003034403c1c103086030300c10784641c83c1e002c82c0c41e000e0f0707001541e640c0f20413a8000140d0448d1400340c1c6003040903203180ca1040800035010541c000e285614000028603407420000300304079080c00142030042c0402c142070350240c000700d001e2032468043d003841c01442203150040e40b18010020740300d003040321030f50080c140160f078001ca540d2520030456000c0710641c502c03119503104000070000210107611400115070900001100c040d03c0e40f1b0f03004000d0f4020301880b000288081200c200c030b45814400c0e0780e4071011000090054058598400752031400007000c000600802240c0c070840103141e03404403104958000d002040c043e500005c550307403005410b40f52a00072032500c40054005080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 821851339 1250 821850089 821850097
    0x4031b230d0308130512030406060f0b2208011e112b0b060a0905030105060f18070e0303040b0706140c0304060b011701240519110a021c0b0606 63
    0xc060504000110305071000c3d54040c0d00038081c2c2618000c18165280807420600c100c0044000d40d150080c0c0e2401c2608003481038400d160040425444004000c1200c82d009904851404450b0110005021500191101c200105a101c0d4078154246201840c01a0201c5000401c010030407100b0031440100284030140c50082e03144407032420010356001d1040d41680b4007030314143c07684610003048540c070482c04910f00d500144d0400c00428460202880185002e00420380c4c40501070f90016640183c6200041100c0744411440320400050004036100705d00c59205144241c0c005422a991180d84ac3d0600031b490b407080c80e0980da803600d8580340c4444580d80501d081c1c020401c05203030a0964486454520081007942001c3c1d040c044050442c104071064140070784e0090440c21120501011460074002d10001e0601c014401c01008005040ea040d070042542503241c0c0c00d503c3c15000700f06005030f10910b0b1003142c03040a54006400e0403d01980c0084500c100c0c0020f100b61900c44180d00c41c00103102440c06 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 821852589 1250 821851339 821851409
    0x70602120a050c010204030f0b01090b04181203060506031f0506070807022815020f0c06190c050604080316031b0503040618200612010e060604031b 65
    0x203020081000c020744070314060084059220700051a140d52030ba0f81c0301d44000015011641d203200f4400400c81d00040d4403407060306810a940501185011a01291105801c2c10300109044141c0c562070001d40c0c881d910040c05410f0141c0b01540d03906142c0071120f500d072600003014000c4c418040b404602400e011007500e85aaa01003001400c20380f095013045250750656a00b0031100d40064518420134035040841001015504010380ca49400100028100f550101c030007652607010091948058984404a40c25500016515100c5210842d8112021060040050800d2041c0024003084c420105c0003103002e40c3c0e48009021b9010404201a000c1d140001044041c164544500a0819006400540d4170a210b90030015508114091081518003442e6060301d240341d082c138401a030801100c42c03260540c01c0c100d8009080846021680250100c14010210000708000201d03543c3d0700da090594000d940e016100101c0c180c202c5481030301d80d00c3c052050500796914508412000031910383d007014801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 821853839 1250 821852589 821852623
    0x200a061a0f120c0931061b080f0703020c010e030a080112030903080d0b100c0c0609081902011e0206061008010e060904032006060406051519050d060314070602 70
    0x1950040811581d01c0700207141c40d800c001d206205ea24114101240c0354814901005045034191441c00e0079001c907203480341b0514141c0408070212044a070401a9240d02041000c8100d1596940e104102d001c1e0003a4070007000c066003428051200e10a012014000399195541c23985516a1b03100f98041c1c0d0306800010180118048940603c0413841c0f240080035000000070700460000e00c000d001c2594181c01e02c060800007014466084100060041d1150003040d892a02030725040c10940d001d0749806601c5002d0440b0781d600e2240e2011a400785103840504210868085d0216125120294440710b0480c1c41c540b00d0b04846401c100068001c20105058500c640d022040c00d5440105100d84010701030016410b000340d51865440c080f40b61030700010380b14444405080c481c00d1050900055078000d400c010302c54145d07212061044a0361106451101454154100c2512100c100c161420b03c02c0b07240ca044100d04000002c01480350480c03180603004c1440c4100c030040750350b9407000c0342c9075480903030501004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 821855089 1250 821853839 821853853
    0x30b06010e1302031b04091a041e091a040b07110d050405010f111609050c0403031e051213050610030309151e110706050307200a061a0f12 61
    0x4440554013944c1d21000007036400e81200800821850701d80c2290b8042e08240e0b0319100110034181400720810841c1c441070350309000028031440d8041800d50a1007240003003da9405040f4140525030900617a500201611803410f0b017030600706002d140c48115aa90f01141101ca04014003c60000301c00a100f0340564441741001d003800011950142e5000d00c003000c01a1ba685602c0c4020740c1400f4000d25080309a420712509440c0c503440505407980180101c5c01e900041c0000c0010a400507010415000e42d00500850754080f004c0507540d074010302d1250141c80481008004808108034829440a0300441c2111034956030b0300380600c00c2c00e429001c0100054401c2404003c125003414a41700c441d031040c101150405101010b04103d40e50b10600c0e08001800d0002ca180004000e21416021b00200c2c1b41043c903510f444000509007941005251040d01c2540c2051545950244400c0c641d065000c4002c2c05041b0403140c001800c035034580e40e61841080103400817020791801c201d281511083c041c000d4012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 821856339 1250 821855089 821855119
    0x80c040b04030b130605100f17030409020318030c03071a131e020319020f01090608061009080d080a0609020c0a1e2301060905060d200a030c030b06010e 67
    0x28483c0c01505070901c40030303000020400502540603942c40342a000c50501e51451030040303501201c100b25804030348041200c01e40711000000c0801214140d032801e1401503074035181e02c0b003e8100004d041444601c5804080f0b0130100300f05000c4001c2180ea401010106522540c1c00700110805509132142001c0758090241c2c940000c22500108400c1503241019030001d501d103401080c240311540d0700031445807040c10003d00841c98820054a15001c2c00c4c41d020b51001d0800d140070b4480b034000340100b0300c0340c848800341d82259440b8140031405440d40d01d00340c83d0000380f030300005481c5d004161030b0300030410b007045004110081b01e4400c0d00c2c4030844510040c400312059885104520b08071000360714298503905100740111ba01e81c0c102035100071780c00160000301c100c1d000c10700c0c2c216445038000385621410103040c4469135075816400501a0f42000c990603c10023078183c0041601004000c2c80d030450039a0704000284001c0e403265500701c81c010010340910b81d641da00118bd0783c88000620590082049101d010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 821857589 1250 821856339 821856353
    0x2130302060706140109182411040e07080f040b100302150a080a0b060711130c0f0807020c01080403050c0106030b0c040306140405120f0f0403111e030705061e03011203080c040b0403 80
    0x4130700b071007248d10604600d4640b600c034107607140e858030b030401044006004c104500d400c000c5683e00c200207240c25852400e10740c04000d81d00070040c1024000380c6031080403a04c144031500c030100c01198000c00403600000c900441c20311907080110b100c4082503100c1c0000b11144070314090b4a401c08030060449241c005541d0301c20024858501d092508800f240b220003181d200075124403660140980c940c2d0f00210f07d00d010046c00340c20002c00c450110b4029811007030490340c000c0001a041503040c00c0943e190210720b014940105910303031029145c3d07400c82050299410211004000b03580c0129000d20801c41c00000e1110034640a0360010031640c064038202c07000000350300240c82c0c05131814054078682550030400c43c81581042e0815203282401c0a0185411319001001096001a80c4034000b40c006c2c0724400240c451505c0d1283c03a004801c00070385140703080030207051142c0c003105120880d61256124114440c800e40300b040d0481c045007200c8042481c176180c4131709550485050400d424981401d40e5a501 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 821858839 1250 821857589 821857613
    0x10b0a0e0c0f130801061511030f03041a0a0c09081b060a1107030c06120e1b01020304050a0b130605030f0103020d06090501090f05060c0406050d0213030206070614010918 75
    0x508400d10501c00f2411071000245808020300c6254000f280c1da605016048801051440100042c05014088254403040c00304c03d540080100d041221b031039613124200394026021840036441c89503c6541001040e140f254401000700300c5540e29494181d841e0310150755509880841c03c0c240720b4412007000428034040000b0400c101e442e1800c404001304010f00c00385844200c0d00101c0701560700180a10080380d002d150030003528407580307040c4486004e003800c244d01e5038800b188030720210502e44070300d41d21079008000b21030052801406144040743d03581d039900920b03080b12030160074101149400045040c4a82c050b680030b101d83d040b000e40507034a15805c01202a0850400316035285d00c590940e0046403003840b510003002d0064200911007442442e106041950040901d08840c0d01804140300c010751140507241c0c1c4c4c14400100580c1c1d45160403000b00c96600d15030000b0b5201d040000c000c410848180c20200c1da0b860300042c0b2000907622442d586003960a030240624407200e10452a00c0460441c080380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 821860089 1250 821858839 821858857
    0x21209030a0f0c0e0703021801090b0909060a080d2703030f0831060f05010b0d0e030d09080d0b101b060b130204060e0d020607300c05010b0a0e0c 64
    0xf618403c0c1e5a42d0861300c000d20111540030120b0740c041141903401156143d1582c85000912b80018200e0a1555a1300305028595055005044440c00540c00d500d925000c1e8020380100402c441440d126480d009020329541c4007140001d1100740908001c6002014101090300e6040d19030510380007007800c04480030314000301b40c010100d0010b101c04030b0621110175031203100401e812044110210905245042c0d94280c1380d2040c0301e514001c0100449040700d020b4071042d110484000c1151411842c40900e5401028a4103400c43e180030031070400c04c00140c00a010000c41c840e02071100d03202c071740100403e0415480201c130124241e0718413401406034180e06d00e81c5d8544548000100c3d944040c0206a10740c50350740b02c1304c10161340020207101d820341010306a0b00a00007100d101c44e490040d40d01007001809050320040510510080d400801d4100415095000b1505048165000300d1035070020030310741d4064810340c0c0c0c40d4070700b20f224510745c2031040912054802c0009101d2950702c44902500540d408880d070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 821861339 1250 821860089 821860103
    0x91e0302011416060905060f1603020c0a06050703240305191a0f09101104050120060a0914190b06030111040905090625080a0609090b07021209030a0f 66
    0x2000450192420440fa00d00b80030700c50008550229150441c0381150117005c11407112004020440c0c2203800104014124480389030150b120340020008038a0800404801000075080000f00301c0c009a041c1c0c031410804034100b0310200c0d0364440b41100407110105001c06402604100081468032140c0032050302550b01c42d54402c12003040044d1140c0040e00c082d14005a001443c0085c0b02c1840c104000401a0144910042207021a0180440040e00c1540b003500e040c00130f12080c40c0000c860344400982007003059415030384036251950281d001411101e00444451046680b031001c4484002a0b40d0300c009044544a141100f50340c0700c0350b441d80c0004045540c150b40ba088107000b20340111025100408a550303000c180da0030089800ca05101006040b58401061100103151094543c1013585020300309041c80420b81d10348045a101401554228480c21b5040c0440d01080180c02d5407110301c01c1400e982a0b4002c90006c48200007288108054190b01da40140d00a1000c0746c01c401c0d5424069104401c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 821862589 1250 821861339 821861347
    0xd020d14160c1b08060f06040509032502030a05100605011808030a0c050c130b181306020c1006060c031d0109051e040c021c0c02010c150f020f0a091e03020114 70
    0x1449403400d002110f41b00701114151043c4a25824035000e810b8024032a0b030080c5040141010b000105450b52904401c0034031900a000015524207000300d0750215000002e6a83c0354003a82c0050f0042c2040f8480e83d8001441d002c5061b1904506900311400e8a14030b40c051413400c40c3c5c080088506c10000c00060b50580524105900740d82e46281083c410103440701ea011400720103400810070013003c4000e03052a036078040d90400601368000302e19141d4a41d408040161100c3c01d40050b6403034440402c840c0140c580c82c110002c00c1c281c0e001200824018441d60340c035200101c0803a80c03440c80300050254280402d10100b0117002c0d030710b04001d1365900d808090510703c00405100c40001c0a5817012211003000da00500c0308002d107201c410324403001800950034044a090f55580c00280000c0322841c003d07004104585d090456500300307801c1f100c40c0100c1d030070055440e80204030b4801d4041d4071014000010a0054500041190300006402844501c680402060500c1c540054030341540b41d103915003151200708 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 821863839 1250 821862589 821862599
    0x4020f1c0b03101509020708070b0910050f0604050702010c02030d0c11030a0302031006231b0627010605060706050402010203040f0305010204060e120717030d020d14160c1b 76
    0x1108103100c1c1030110340031624041904ca111901c90301134016506590041260030f000ca50180101c3e901a980100782c40c110303903284000d0504110b000b010032034040e4149010312801a410ba078020707014983c101c1e410001901c55580680c01c82e1000b0b440340c0701582052018a10a00499101e620a40c00300d01300923001c610854091811640070301101008a41d010045c02070344208001c0d080c01a10482c100880d03650a181c40b09407000c890039030300c0841000001035159200c0b00540001c51100352002c01c9441a003814101d110642c00e80361840144a00301d074500001442c4140031750070407600301800030b0b07280144071317203502d00986401001603040d480304000c0015250480d4140c0030085001c0c60006032114100f030b01c01031400c0386d285560b6204295195100241c18170100d85c143c112541500f912040040d102900c5003540100d00e400110584046922540c0b00500e41103c0d50740b119020050300c0a58a05075442101070004044a002400307000c3e00c0e10003d02d081e080b01e898041003d0103150a15600c8e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 821865089 1250 821863839 821863843
    0x612151e0115020106121a10120b1f0b030c07051903120b010801051e0307120c1a040f0312020703060c0f09060813021323090c04020f1c0b03 62
    0x1e03404001c40c80c01c400b0311044055420711402014280251000130201043d0719102c6d14820a000d40b4401c101c4803801007401c004020880c2d8000f03203a00b050348541107115062102d80c400c81220b680102c00220040c0f4001c1e142400042020345401c100101d0458880800c3e42c40030340c0207030b070044603075100b60030526003905215001081030b944659202001c2191400b44501594103a504190512030000014003650f620032882e160b44031015070010030481000c2d40002d1604005610100c482c014407101c800c00d110703516564505440d0b000020140c011a441c2c5911898801da11604544800c42134003800040c0f1003049070f0310007142d5841110969a240e850789000c0307607110615a004a1082240310050607007040c5540001d240c50b0605210380e180030380d004900e40b02c45450091080000c0e00440080003070f20307802594601c16403d00b80c501c00308002c00c09021158159508040b62103070849540c503a04e03080c001c8441d440145d008440c03e00640140c00c01105c4c003100000c110300c640b5a4030f100c00c0f80d101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 821866339 1250 821865089 821865091
    0x5010203100b400f080123073e01050606070803040b07020703021504080f070b0a0c0501021c061d0c070f03020a05100f0606110c0d1a0106170612151e 66
    0x1800c0c4c000410300e01450b490031103a0040c9450b8014000c0950800c203031070510140e9078000f07030034100842d00342c0d074500700422882d52a0070170080c050003400b02d18140000321010460421800c400030400c64a906042000501a481006141e01400c100040005966000d000d41040e500e00403100138649030390004412004000110700d96100115080101c1c03001000302c000c0c1030f0305003000303030201e035040008403181849600070040a000144c404007080100960443c0d490042d440040c1c0c0440c810288800083c168610541491409400d0000c0d4040c0141c41c41074003800080c4591841d1107010764600c44007000c104026410350141d040070202003001482800400f0761102e00c000395400c45007501400700d9182e81c0060041002900803000c0710400002e881c072083e1822280c038620401e50b4500070030207007417404008540c0750b070100c000148181c02031701e201d0700039440130039040305a0b8491040c4890082d0008000c0c2d075680c00701c5c01483d01d08901540064002004040f42c200e5152080d54102c50608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 821867589 1250 821866339 821866349
    0xe0604030803070216060c0f0210052803140f06130605040c030506120a050325020604140315062d190f09021e0f090d05010203100b40 59
    0x390038103440c03082000170b500000d0401418148003240e06900c5103142c0301c1081d14024000c07080c00320611055030254046c2c40d84201d40c14080030b04101c150b0210071401e854030f62401d0100b41085204020829000902d41c82641c00c012520b50a680b0401000b4141010101c08240b080d83c070075000c501c54445015003201c0380354a0720042614206502401000c60f2440d00d1440580c220001c02c90008001108980c0341040300c0d4280307103d602c24a505144203038550540290310003000140068101c6484101d51103020049040d0360781c03141041e1203005400000c8514a521031000b62002e42803140310380d001d440304c000340e4241d8030302001c0310300100f4890420101c905900b030080340803c004221752100020f0160008800950420781450b502e100f034030603a010035001e080008030710940400c5031241943c0c10a00c0080c20300d03c0d8070301079090040c002d52040d61400d01620500c940031800c06000b038201c4050886042c1001420f90400100b000c4031072000c121035012412402c003140b0809034814038080940 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 821868839 1250 821867589 821867593
    0x6050402030f0f07020d140c1203100e01080304150503131b090b04091101081305010c0f0e010e010801060e15030a2903060f1e1501021902030307030e06040308030702 73
    0x420103031089a1005401400d9004540c0011911121b007503015041080c5c62005000c16503e0784d2442d2556400c101100e9802c0281e0200031040025000040000340b0031078402c00d26070605130b44c0b6009801c3e2244658051002d02c1e062584640c4625072080c402140e106442880c0c0d5a020a015940c6000d200703050104c084074004c0900050000606078410000076035000c40d002c2005452030365401b02e5050808514605100210300061481540c002202c00f1103940301d4020800ca040811002d09042a030710459000210b955074850034035406080303060891401616a041640c3c0b03001002c90b02c090510200c2d9130000908400142c0340c580b2000994092600c829010580088400380d4407280c5240c0760682c9141301c0c2d80c0441c5c481c2c40d10003003602500a002a00b02c5820f903078448111040c801154410b43c2c29001d4028100300c40754800d40152031360080c00360709441c1c03141d100318003c040d020110705c1c000e54103801c204140c0000034006c86000091080151031a8142039032038540c1c404e0354100312842000b60b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 821870089 1250 821868839 821868841
    0x408090d060f0e06060f150c030a2c01021b040f020705010c032007020103051b211b0301150216030b0415020309030a0309060e07181d1002070606050402030f 69
    0x200803e000380720088030120010140c0b4a1300c01d000980700004d800b1140c2c0287c4190072014003410404040342c2c0d40507808004c60340c0c0c81c0112500280214a443c1e950b1000e10101407003400e00d5018800017244441e0140d00805943d08441480c11041c1c40200440340d1082d075a207960105100540007900b0074902403000060050a03040f0040d09685510158010200030921064441500a0160341a064081ca00028540da5003d81c0402e10002490303413030103541d00032842401c003a0005040001c10302c5003090306003080d00e41d28118280e44048100c1c268150740c0030f00041c0b1802025000500c08508244100c9400010005114007881c03242d8100b81d580c0d500f2a41000148101e0508682880c1581c1c80300b140f441c94810039540d00d0b4065800ca400c10107032075000110a20101d900810303d640c05581c242c4001d10303622000354285080841070f01155500704a40011100000c00f03059582000c01d00c05440c1200154039500001d6015070340031030301c4983d503210101d01614bd902c05944289800a03001c503403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 821871339 1250 821870089 821870111
    0x807030302031b010e0a08030c120114030111030907090b27091b01050301052e020a110904020108010b030c130e06030f01060b1608090616020a0f030210080408090d06 73
    0x841542c43c2040c140c1603040c400501751842000a101000941203030070302e600c0f600c545101c20700900c5640324422109007400300200c1e06003421469280401001c0300200880d02e0202030f611031324041220242c0164000d00402c1100c580e541c2c02c0310602c074030003c3c003080b9810f001081e038080b03036040c510841094880100400c00405801c0050421a46141c6040010284103100013000742c40140a694014031400321414824034401d0132400c81048140c3c0c94803584198000001e42d1100750990581d050b007000018100181000051140240d0301039490048070b03030801240c40d07810350024003103594500c0100650a202c0301e1590010002d801e01e15001c400505250040601d00003035504c1148140e494200c003000b41d944a0300451f001c0a0804030000d1000c0b00341d080020403405070010b0300d40c109000040d001c552010a40403030021501c03c031961140162034000d1150307014220f000081d040309201c440c0d035250501501001d82c2c814490b4184900c2c001c2d410300032401031000035070b044035060384500007000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 821872589 1250 821871339 821871367
    0x80115050913050706050a03021303060b010215010305060106080403020a080c010c0e031c0809120d060f230d02210d1211070f260909010b090117070306080703030203 73
    0x81c100500c0c0180c44000c0d000b0b915800d450b060389114840501c200064a048168007a4041e41d0304801070020803014940d6900b099000740c1030403102a4010300a00100904056540384610b0680342c000c40141401d07800c124041d100003078040d000b50154490111000001103400d8000e240000c1d0910000c20795840d020ba001d4104000480401d2083d080200c03d118000c40f800c0c0c2c070301e0b03003a2180e21b003000c9151940302c030076030400241700014000b542c07000030181d0100005400003012184000d1090002e2a520190361401161904403140443c6002c080280c035440e22803203011b9006d0005001d281c01c000c410b803030001038074102c1d2200307040358000840725003071140c00100a402c412150071007400700301244000101c02d485510f900510440003070b00d200f003d01440d41d038001c440540c0c8010070b800710703421035500e032003030307800000e28940b0400c0307003100118060088206413640c000781a144c525900102c09400381e00c14000428550405644101c001b41d407c900b001800c1c02540260007841c7d445800702032801d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 821873839 1250 821872589 821872591
    0x180c08060105040507020a0b040804080a0c0e0601020715030b21010f1530051203180307230c090a0207030809122d0301090608102a05040801150509 65
    0xa40f2403072418003040104e0340c0110703020100c0c80d400200c01c2c3d01581c61785840d510324050760300040250320071007010700104144031003480c00742e460010707e100b0903580380001240e40d68910b0060590001503506064010b5000760062446154010440c0340c03040544202a041e005040aa404160b07444040c0d1400074105d0344240b03030345481c4004c40c448015003003940d01158100d40e038107002d24000050700d85a01d1004007544601d4159400003e441030404202c2010203140c0090f24440f1028408013140c040320440041140c10742640040d002c02e403131200d881c6a8841027a50040d00d003481c003ca441c00c2c910fa0742d134503050600c03c0030129001a01c07070344141402401104001c040d0b501c65408810400c0c00001020250343c0c3c0309019465644002c01e200b601907040c0c923520003484409100210020500030860340010050b110500203c5902c080c6000c3d070b04096035900007a04088500542100480d03221041c3c2c1c1603215066030400910b0300e55a455190300715000360385100075107400b181d414001c41c90030f403640c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 821875089 1250 821873839 821873849
    0x30106030507030e030a05090d080309010501030308251103090a1e050402070209060603130c06050928060e030f100905010b061c0f1b08092518180c080601 68
    0x201300d030740107500740603550303110709004401400000f180300d401d15640c1d40742c001c00d1503078000001602d038281049518040c181c00c3c00210b01040400000035800c11a60700e03562000741500c01200f050051300b58080c8c0701e11440c0610043e0038001005400015150108800010000202c449030b0b00818103600c50900391158201c24862401040030300091b94840007040d40016085407543d950791500b9864132440c0100c4140104981c650a0002442a030808054070354882c2c02c0e40d00e43c660390390a440c190300c0e1816424800031065903003c03060007050320440320301c065240c001d011a80e48035005070758203141004603808002d0349525003c801c000c00c4420f001d483c042c19010b9501d0790030000c3c44a8519000c20b006511204183d0b03031440e40c2c1644805581010045030040440c1c0700c0540c55045004060f56801c4540008078032030401450301c1911142e5901603844c0a06c6103002d225814400403090500e482e107441a150385e200c9241703080b211244030b040c416032482961054031061401c10581c0c248030050b40301e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 821876339 1250 821875089 821875091
    0x905040f0e0a021302040e070504030303050f25030f0e011d0c0d0803040203120a0c030e190302040510090606090305060f04150b1f02010606031d070b13120803010603050703 76
    0xc408040010000080b0360b045070035200c0c000111400310024055a8020650701c10114144040180c104000744240c030301a42d428441580c6d50301d00048a0320090741c0c1000764507480c0481e01e100100e503440b0a4100240e91501059081e018981e0341c042d520f01c0100860240d5551001220010049038a11140031410011340032600d0704e1400203042003072103a400303003001e000000003078110b41c0d0910003441c288803e164825100e02d0140070040c0011038030441100070a002503041e10443c5070010b240071082250161003d402c41c21b660130b00000c5c0ca0041c006408113580920f000c9410a800d018420182c80d45030b03240021540b85091035443c040c4081c1c40c5440d0448103400b40404600000104101d121100d4808a807000c1c5050104010301000003054680e4402d0038044800d82c0e606410040444641c0e075010b00c041c40112440781d0060b42c000c1c10300c0c1100d5120300340401051660314060b2445a0806080c00d0a5942d64542c0301075602c50054100d4414400100500c4540e8052090a82218481c60 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 821877589 1250 821876339 821876351
    0x1905160915050a080a020d0c05041707081c03290112050c042606010605040f060e06071b17010f0608011b11070306020c0a020301050f07020307170f07030905040f 71
    0x1c0064030382e00c00c2d5072000d8204010840007824504050b011240c84a241620801c000d80d000c40004120750003a00a4042030300d40409414030702100041c6800507203941d44050180c00100e0b6100440080703e680f007170004d060711201c40c5800380c00c03048402c0703128024801d03600001003007803000101660b0312101c0381c0f0403062408051044840c1203505403010340c2e12082500621101c4903001d20719164444105011074840c6c80f0000c1441c0754880701800803110991101c901c503d07140d034029a41c000c81c0081091704180103200240c0030802c0c4081e4a215842c0060101c8081c030b131615a65510b4882058114030030b40c0d10380c1c51700e01c280420352207070300c0c000c0c41101d00804c0240804403c22280c0c52480e04e03000100428000514091303102481014000c540c0820110f5440c3c01d04840140c443c0700c1da0f80207074840c4d407070180001c8a02101d1803040d40f01e5500c03a0301540c5010308584d152611680805070b80c40b01c42d242404074034080100c0350010f10003680681ca0f8940503d1030001000144c580da40c460b18001802e00d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 821878839 1250 821877589 821877629
    0x40f0e010e0304211a09010603050111120a0f020c03040b0306180103050a02040f0b0607060b0f01090f12081b010b03120a050f0d0e03120907120809060319051609 71
    0x14a0400030307016007404040c041c103080d040186007004020301d4100100d51708401e015003080e055009a084a200c1d500900200b98145458125400b4000d46506221010f2001803200700d040e03449190b000c0c0340c0c403400600f80144c18030306d180f654000d90018171036202c0000c10700201d4542040203681c01918035413071070315941c1103603665611410000d0000f0301031601d036040e00b80f09909036002940268000381105803244154107201001c0c0c00d03500615800350f40040402400da510030803100741611402e0611028452401c02d04100080c941202543c480c44240305884d07503031121000312904500b40d00d001141d51140340d41050b04004440e846004051000c00c251071640380c000040d503d10300518a0111784900303280c0c0c410030141404500100b05030000081d804204d520041c901ca014450400480f00c0868880f080002040c250701d001414980b0103124100161510000855101d440c1e0000450f41d85030040005090b82d0781a161481036034010054000384d2940401050002c003d1b030750415035010b01d04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 821880089 1250 821878839 821878859
    0x30512090c1c060e1902130506100f020f01050c1207030504020f041d0307030f1e0210020a03022802190c1202010216090b100f120506010c02040f0e010e0304 69
    0x355014015a00d40d8020803e020950348014800c0b0b0482043d50000c0840d4a41d070754100e0403c10707040740b06080c0307000c10081210941c411248501d10190184150004080c401c3d162407100c40180c100310300c103031444071015100a01509000d007624010b801e403a65480310080c0e0f02c51000500701000c25180c2400c10000d40c0e11003644601d402001d641c0028038a920318040b60000b621500b540c402880001684820180d05c00807684494150380c1e65501c041c0d10800c003524010101024850050b0310621030003403181000d60040c00c0032401401c00520340004c403003602308410f42e100e4015841c1032500580c004030302d805100718030403120071001011200031550341c2e207540d8030070750f0180d48403d410a580d140304590080000c0c0346010007851100707418598980c0540050481641c0640c056100303407221080722405900e081e0003408258513aa0080c00c080c2321100014000101040d04011071000094090f1320340740306400032003100b00000b00e082046001d1060035281d81c03510410307096004000800540b000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 821881339 1250 821880089 821880109
    0x32a1c1805011719020f0708070204180525080105130c06030908030c0313020d060204050a0b040303054806060a0b0a120b0405071707020115050409020402070807030512090c 76
    0x407061030500c0030b0402d004c2480280a44101130380d206074001521070910043c81c0c06480350314070071235051040703110002d03480c031140d641414010005da02108802000907005c280c200840c103070310400a400719683e00d5078182991020380f044004d601c8120b0803c000d10400e000548003400c000e09007803003a052166101c0340c0d148401404510142030100100740004050803044a000350003c05007801ca02c22410400e00030340c4141304840c03140e04454800260121540142d804803501a12014140740252501407584d0440b4100844100304550311100518004c0b100c40c0010341158103d92120700744120401c0c584040035090b544030f9005c050b42040346040303542c2111040c40d09d5207000c851140e101020740000e41429686641d0180c242002c22191a80c446100c0c212188c8003006212141c44120003a0f00300c90315444145c142e641c200200340100d040a0b00300d0b18249101900045c500041502c0c1c501d0300350040c820460010303600107420b030515039011000c1ca8210401501070240d0074001c200007114261 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 821882589 1250 821881339 821881351
    0x907120804050409030503010e1506090904051501081515030c1207030f3504060c08120f0603100204080604301e02032a1c18050117 58
    0x226241810003005410300c162001802d0140c010720941c40c0d00e14029060b900309010700810820310000107450100101d40380b1f1404680981690325040105042c0030002100520540c0da0780304024041c50400240e60b503642c001c15010000e0050401e46e01004a52a44080c02600310301200c2815041d5a0350702080260281c581260364990700d0400e02085428145654005451010070480b62420320003030701c40c240c81c10301c54900d01c4810840403004554910301d00f540c00e1690111b080c8020f03c1610702401406890a004607091401d1a035610b0b01c00d5000c90084484a006016460500c141d074102000451981130004809604184c10305025030303522100100003404203046101c405400c08048810b00811549008041290710300c400d001a00c0c0d04200f800d44010300c011904004411880402540e400d5400c030400c043c50001d10801000441120100241c6240180c0ba00c022034400700044100c1861580d440c1d60404400702c50302400404120b900c800c0c107000c85031035030300500c4049407041a40a1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 821883839 1250 821882589 821882609
    0x360603071205100516080610080a020f07200102010c1704170f130f12020d0f0201050c06100e10080d0309030e060a0203041a0f0a050d1b170903030907 66
    0x6072a08045180c1401c0d408900038841c40c060910110848032009401c41106030b0300d4a0295490703205c18444822011040c0c02e0000f0801c1004c1082c40344a42c00800c3e143c100030303028508001a41e2960244007201020030801c04900880441c1c2039602800780d624011000d00707040043c450007500c040665030307000f40000e003614941c0e08010b40b64003510040c1c800c0f00c07800702289a120a442861241000468003031440b0760348504600068440040740c00c583e807598081c1062207401101d56404120780d49880089041c0401840b80e00300e9905c042048a2050182e80120410305190004042401201812041d100050550700b170281c0321000401c095003000c03030301d0006508149418200e50710940b1840080c0d00c9580013070fa1003180c2c3e0f400000741060380c035a044041480c8920221001c40382c07064103040c518000060006400040c0514040c4c5803041d040708001c6004004000c82480301041c24444c04081011030745640340381c0d00d48080d1b19078010055401145182041e0003415510103480c0700c0d0507410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 821885089 1250 821883839 821883869
    0xc0201031d01020304050106170c06030c16050307031101090804060f090302100203090901081b010810050303070609110f0901050f0a0312110d02061009050a020936060307 75
    0x164460303409203004081860010704074815515509020b98030954080d1170542c00c2441c0840e0648495090010304a4a54010b01c44240c2d40030074810700e0f400041018680b618241302c50540d0103c25800e0050061040703020310340c1c8604603c1d0140041515540c030003004e0385031003c0031000800c00000c40e010384645040104400c00c524408a41646440d040250404c0e594100c034412160000060310800750201d07002c802c141c1c3c0761401c0300c0d565020406480080e402003801c1042e0f0b5409410040e03006443c0c0281c1000305503e8101185c610ba10008080320660f5a230360440c4180414820400000e00f42201c407402d100d150000010a20001030181ca40f045688001078045540da0107400d200554dc0075081c40072109190801a0181c1c2006044070040e003d90ba00fa007041da80f0200d8100e100302d0080f4548400f26060540d850000c00006001c0d11600c4c0d42089030110f666280255410310140c610080f0385480c9640100d11403410300c00d8020b40c00b416000c0b050044a0750085a40000e81e0f45601800950b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 821886339 1250 821885089 821885093
    0xc0921060b0d05010908090406080a05060c0a050706091a0606070f030e060909040606030b071701180905100b010e030703080702090606070b0903030105210a061d1002040503060c040e070c 82
    0x482c1c4100c2070002c11941c6800707206010484907501400c007144c81140c0c00c01507296540001c1d034492214180003041a0000300c0014414140500a401c0102c0350f4505030341841c00c2980e92008807415407a0680e0540085114040c1200345c028040360302440075680681411811395541040c44034003d401018000b000c800d120309602c0c4c0030103507007601c0d41c01032044101d410b1605040004001c0780c001500c1a000f880001501a030048850031404c03d019802604541c0c60515480b241e403d590145000b4542c840082101185041040340c002c01e40d07207240040c0b01d04000c400900884101c606960094005040400228582c441138a5940307405450b440c940717940d1003000541602c19003000800d580351301005d100b41014000059416500156803011503078a803441014401e495008000803140d009100f420001510340d081040d600d000c00b103900541034807002c00e0a080203c6500c00c2c10070180c0c003040401052400308000e43e001280200407615040c20012034403190741e8001d14140c2800034080105003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 821887589 1250 821886339 821886349
    0x703050d090503160c0503010b1503040f0305070818031c021009060213030f050f0a02090103081e03160e0f010507030c080d06170f0607020705150c060a0c0921060b 72
    0x41d112002c1041d25500e201d2402451001d17040c01070501a6203048548451814407d098181c460749413001181190380344d541d00c1c0c444070b0308907004404100080c01079900054082020340101c45003e1003aa100281c0b130018907142c001c0884199965a03640103103440855000703d91240c42400f0034030041996021400c00310084d10071203e5420503030142c4507001060041c51403c101e4805c0c0b00d0300c141c4404668620340c080d691030034000041c2d80aa00c00c0010800154003074000e20031580030800d03400040351100041e5240b40c00c1280d2a040c480107034080e4809980d488070341c03040400402c40f48200484018400280b85005500005041c00600410b900c20b005010042d00c03c3c44607c80400d201c1a51620510440d00414640d00c2c0c00794032440786448410980410400d00c40d880d10741c0188100c91070308041001904103002c6a02c80442c0400610550344000d2040c10301c80d040d124004a041400000c00a00342c8c100c1e540041203c1c0900852611200e10342d840c8440d0654002c600407440da842800069 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 821888839 1250 821887589 821887597
    0xa141b1c0f1107030c09060f090501030c05120a1a060f01020610151b05010b120606010806010810120807050d0f020d0302180d060501090b040204050303160f0203120705120703050d090503 82
    0x64600c0c1706880c0300165a26140d0482000c1e10503004551086950710f0b0703c07507801e07901b0a001c010170403009450180841d0820980e4039544d100071104840e00107000f43c403042601c03034071008010f04503061901045002e0400348520400030707000380300a009920b042078030351940101c940108202e040620754500c00c0e19104001403102d0024050320702d501040b052501c2402452540076050145e01c2d40e1060010403000402c2c81441a08117031200c504940d5004011180c0040041050442908100000c070b00b150740100302d1422140b00e500d2403075491070541410fa02d4132601c1c240700701c00c112414900c040401e031701041c40b001c1c804140c2400f60310b0b00307840c51003811400b804010690300300790044403c0341403004542256048400e0304100304404191401440140d1059000e0b640d0540c4c001c2211a0b0002c0782c010695181d00c4c06120324054014590340020705102d070b01c80c11000901000b003001414458148080c03030f18907044e110440d1034045507640241007030050b0204418010758031000c5806000040c0111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 821890089 1250 821888839 821888843
    0x40c020a15020306031b1e061b0a1a101e03060f02071101020106061b02041803020a0c050a03021302030703110c0d0e03060c030c0a141b1c0f110703 65
    0x80c02075100e00700298002504100c038118428450098010300902140c4521941007134043c10340c0b4040c1d2552900e22100d241a12000354000b18208803d58040c13541490300d20040d078560014142d004441d00304900c0420305840c22200c810108014417a01d444d1a02c00714089842410351020310302c1d01e0032440d40c20b1840c0350784040d1000e42010f00400c03100440e58010503880d4403412045800300748460049089600c0c0d4010800031503040c03440b00400000c821038421500b0700c014802b18800139641001d1a44200c40c01007240580d1006144900308801c8a000501030322065840b00e8500d441d5070001070041103000c500d040c07596400008600781520940180340c80b14401c454a41c0e403104807100455584441003d1300c400030b040d11000803107902d0007280c4207020b01101c2000ca070540c0c86401d0b2040640d4801d08115050020b20a061031038203110001401800301d850204c03840e0701e4007250b541814129000001600e5003034043e544c4601c41c1c5c11111210f1445424540b81c80e441c550715020760b24100c00e60f040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 821891339 1250 821890089 821890103
    0x100b0c2a03210c0d03061701140a090203010207050a0606030c0b0c0319020f0604080c010e03040e04060c0224010306180215031008120c0d05070f0305031b1b01050123040c020a 77
    0x4110b020703174168006401300d801303d0044062005035064407600304c60341500b8141654071183e0100312032250b2500f00001c0306000800061800c030035030341c40d10324203d49410100c4906031190403c005020015480700c00625903806020b141041043e1280d4a9103d0401c182601e4000c6c01846400c0070320030032007c60300d07c2c034040455401d8281401d00605541049034940441d600745100b11007d10804010380b0100d415507101c00b02c4130303100c41d91044003034080c0c410301404610920341103601e480b02c41000400c080c0c40c00c2402c1e68055065003403010540d49542000320003224208103050040e2200104c82c445512205802e80d00c984480d40f504038113105c03a5104640e5842003c800c542c2c400840001400c003481e0b60740c100d400d4015200b5094455000e455409406081c200d01200d0109010744015a4083c40b400c2408102c562103655146450b0010403000c0c048004e45c01311090744040900c40c05001d17203200b080c225200b1280845980c0d81400c042031150069440c2e6542d0f00c40b1030f008210b0650300c1584006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 821892589 1250 821891339 821891353
    0x3041214011503120c020f2403070f0201110403030c0201080402150406080f130222110415030e0102040513150302090f0f061017100b0c2a03210c 64
    0x1902c6941400d8003068032004e00d241c2c44c00c00003e0140150845031540504400980348103641000079000200c00a4140000f180c0d50601030714500e980151711448558a88046022031130400074216880785242e00710600b4204410300c007090300010118402c81c0d0928020f016699140f000c94800c548050590310038590102c0e005c100b043e044140caa200301a03850741d504441e9107590480300710824250001e5041015000401d01350008920303000d81d0310030054408504d07107850210406459119501501b00c0090b4011f000310050751502580b00000c003210001d40c14a801c110010b0265601c08000c602070319560074120032070582060016000350b8004020b0180c518108403180310044003151000700101c1000001003051070000b4090703a42e13504075524581c046140d0f031203084240d24003804103110340449060008900f1121001042d4100864025015440f09035500d000c072074900c1c078000242d1410b41d0304c3c031b500b40da180012a01111035500390100240c9241d4903c44165100b580c0405110f4015a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 821893839 1250 821892589 821892611
    0x80909091612032a0807141603020306150609042004061e0206070e1c0c081b01090312081317030601110a03171e0907050306090706020304121401 64
    0x8154900903000e07480d000a0f11150714031301090814030815052030004c4102001c80803859510242c9815485010780d01e004051001c0801d2408880740c100c281500340d040402d000b181014480645c0010304229902e00d8031007000d0000341203000b00c02c6590300440d41d40c0041c07280c1b003d00f0810b07900c003001c12140c059515612400020035817402031641480d040000e14624050503c00516184181070643da005850b1201d00d080003103080f070f24508104002c404840050100f140200103500a1045c3d00007400500400110080c0840358003003440c0c14050125400c10114440c3e8010201c00c82441c03500c0580d41e60ba420102c80007045100001e4209400d400312031421014000040d4021035098803080091740000e8812681c0d2070030800c00600040c41001d0300750319240380701420f5401c07003083c8048069512889484444180b03040303034924902e5014032400c200300e040c280045600481c0c1c2c2030107403e0b40d40c00c15001944e41c2c89a031080010001c10403140c5814800b0a121410400d42041c0c000d010303d038464 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 821895089 1250 821893839 821893859
    0xc12120213030c0501050a02120f120a0c033903061806050a0902031315060801020f090a0b0307051801030b0d0b0402010825030b030325050c0108040809090916 70
    0x1901003100d00f050003020101d0150f0062080e031300c5155148d80100301750342141c3c0700e5a12940120000c4400500140700c09d441034009455102c3c41901c1a03903001030044500340008040e45e9050316200c10580100c1705210030401105191b808800403004411000c00710b54400310003c11890f80920030b291000300c81108581d205410071411104200c4001102a895404ca0000c07440306031003000303000c0200b80e400c8000441da0710880d50005007201e400603d0590300e880b0142641d2059450201d20380000412005502d0580d11140c094001007194078210300d84914040d00d00c0c030036003d401400c80c40452160f0120b81c400c0c1c01803c40b801d8003400c0110003d5407458141c100c02c0042d60704a022407141000902150740306000e554519142084410141c24421003c1e8014142e00607502d4060000704100c00d403040840b900913010044840422001000504000f424100d00501c000d0400541000f0301c404140b082d000e031040c55000f11080001c07034403800c4460785060980c10101c0110108014009201882 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 821896339 1250 821895089 821895127
    0x1e05090f06160503010320040f2c0606060313020d061b08090c130902120c150f04050907050d0e10112104030c060e1c0206070c121202 59
    0x410400c807612501c410a1140d0040e0120411100088083c40100042000400070401c141c1071600340708079104c003290109060794007134a020701380c880d11114450200b2141c03210803040034014480c541034140740000310030348540d00580298400d0a0100100e0300342d00f00c40580e801181e5009058030810b0071030b403a290002e0004582e0030100c00103850700e50b1003800e009202036403084424402404190000004005450341e0844d042d8070110703a190a0480182c0305c4940c03042c107502540c0001c00d04100307608104a080040c031107001038071000622030050115054000e9600b0f4401c21101e0070640d03620303420300b1074190040e1043d50358000d04005504c013240c103020401781c681580e1100c06015040e0815408540b40c4076100c1d640c418440ca80c2501442e00e500c1c81e00796070f0000d00c6031420030b098011076140d4100b51810700004030096041490607130119440f0f205218030580c5580041d0007549003803a0007404a0b40c10b50030140401c2d203008000070565105d80d4529505001c21681103440340058001a195450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 821897589 1250 821896339 821896363
    0x1f0b010906020a0507090f0f05011e050d0f12170f0103020102071d0103110109170106060e041109040c0e10080603060a1407050706090b19060b040b0403061e0509 71
    0x3000310085041d40c0b0200d501149590808010001c40345813206a800030406008a40402980c070a0040c540d0401c2d40107803402480c401d00440d400301d0130254000c001030703038039807110f4407541840e00100009092050031540e03ca4000509682c114000e00060f140500603008041c5554400c9041102c1da561450080341601e0003a4204c544680c0c0718800c0340560008459209044c01e070113801000040c1c80005d84400d400018504200882d556101c07114031814403006103400303651120000e1011030342c08604074800910407103081c014a8180c0003800194450600c5440c02151107400702c0881c0780c010a0700d044540d801800001c5064140d8000611160083e20001d129010b0480894000302c0e041c0076119048040c07180300b00f1703035444052003a42d1617800317481c0c101c8840b500c540c036240115960000240c82901c0c014801c0d0f64520807900e8560842e64943c00481c0d846409010a10100e8400030541c5c0990390311136400210b00d10b0200f40c4054403076114001700d0300e041c244810050802004900c02032804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 821898839 1250 821897589 821897597
    0x7080307170604020408030d09020f03160603140606040504020a0c0b1f0e100e070e030610050301050601030e0c06070303020c0a080a2d0f031b080702100b0d0f02031f0b01 75
    0x20721508200004d0f4403640c03141c5e03c0a42d0061180024105907948400d0941c0c0c4014034070b800c004190340c0405e00b00030300c00c095a642000c40d00420010b4541500455084140c0e4032000101454980d00042d0310340905c0c0180c6000301e0740403070700e41c01040c040d0040c140c01e80c0d0861100031080c580f000e158030801c0000103066210102c1d1134400a04070039001500f41c01410060000f00c2001d041034076112054100400d044200807200880720340940341448814016131b0f646000c01d4a084c2804141805d481001d4030690401d0b19005002041180200f20406008801c40e80f20740c6c4c17905181011000380c0500c6004e90110b002e26081d00381000740e41401481e01808a4440c801408500c000c191002100005e07400d11104030481642000f030300c204841c02560402d8140000c80129180385c82d210817460344d410b6004140c654092190103034040140b0500004454420f004012215001c2408200ca9000040c015050345107164110758051040d56040c284901c484054417043c600404041e200001c6614085 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 821900089 1250 821898839 821898841
    0x330f0b0303040509040b0c191d0907091403120f070506071805010305040312091202060901090305091e0607030203090109170a0f03030b03150421020706030e030708030717 75
    0x1400c0100075242150001040c0d941103035195120401603280007052010b442d10200f20704001d514418003041c07620001c40d42ca850361013416400700e203140950039048512500e0341d10304001400c5c0e0301c900000306680040c405118800302c09800300c0d03c0d0081c908500c4100c140d000c40c4614400120401400900380030350b0884102d80c4030390006450900100040100e086a2000140000e5000340c0045400511a19003c210600c50406850480341e00e040c007220030340c007200d8200025550400c18a81c10500a0000304a10451564082d2643c030680200c10700070a072110003903081c0d45140202c549001400740855654000354580251290300410520340070803014003010501120740401c010307801e2809402403204600e02d40302d8000c4c0542882048080540303d1080b01c001d07071810300241c5404500d80401e80030b5070070989000e0000c00360700c140420a0b1100c840b0b4000c171041e070020b03510044403818280011804481c060850031f504c92003002508445000007400403880d03200007407540c49003e4040080075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 821901339 1250 821900089 821900111
    0x316170d0f0f050720210d060e13060b12070609060306060c0308191d0106090f1802120a05070f03060c0c03120e0c0405010311100e060304330f 63
    0x40302c0f01601e01d5400900c00a024842601c3c2c4444644400c01c4041c04488401c40319076507000e06400d013011190300b4840080350344000c2c82030b54020322019108079880840d5501c0c2102113184980b41c0000040c00c0d0540352600b020140c4c031924030b04845003140e241520b072070030b80f03075074002d810160240710f8440043c0c90501d000031918403c00c440d01030180c0c56585d81406885882d581d03410303a44000000e6441c96503c018202e80019000741c0a42070080d1300c0c0000c11014a40920350382122b00080301c0340c81c0c5d507003401c40103250031942c4642216200d60403680740c001100107180b1070b860842070000081582c41901004180c032100540c5000c02c6071710a820512481c48500011920717110031a46c01004528000014608001c0c0c0e608a0300058500ca0100ca201950303e0000a041d56402c1c2d00030368501c0244008482d040c1001c515070381450740f96051041105800070041191848002c10190198040f40755240c2842d400e046209400600b40b43d142e80c80528900b501e0004280550320965500c2c60b00300c0e9180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 821902589 1250 821901339 821901341
    0xe0d080903150910050703020d091b0e0411280e160f021b0402070b130311030703120b0607120206010f0602071208130506040906030218090316170d0f0f 67
    0x4429007103c40500081210340c05490040c120151051040c10703000d0092003082010ba1040e0340000e03000701944038a600c0e10b07400741058143e564210345800f020440401000c00d09904240b801c042042d6a0400f40041d0383c014040c41d4503a040a2030306c050b00c4082c001941001d8406218000e0002c919008a507464100041d101030741143c0c000740150300021128114403030240aa0318100d50b001e04003510749030103980d03078205207082100e4640350f0b60045000c031014594000300018405083c0340c02546850311984000e07041004000b00d0750085510368190169680712001900d05142c0c0c480341c0c00900035200100a502d8000901900345510b00340040007444920024400c2c080f105511940d103100809034031401304070351050358000703580600504005119150000100010f1901400c001242c80c158030400104032602c0b5912900c4201060911052a0012080b40d6445c0648129011106400c0c0781009016003500012041010003054401e518102e54026803000b0343c0102c010048d01d504104104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 821903839 1250 821902589 821902591
    0x1b0506091506090a0b03190309081b0109031203090f080a0e1c26041e0902090108070c0c05030319081006020a030503071e1d03072102010e0d08090315 66
    0x2a031100411021138a07205491744031112200000e016a188501d0340050b4018005100804900050400404105500b020b110550700c1696000484028084d40ea0000700400c03d00c0c0000362504040c1120405028026484021200d9100f01c0b18100000396042c0300402c0d0b0018400680458910036841c240c5103030000d0b142b00206030707170307860348040000c541c46811100032030860004924003043d220408c150300142c0604010b14100790650300d20122441c450316003288030380c046c0c07284a00521000c01c503070f81c100c04600d40c050090301d070140b001c000d9410194200d606a40c01a50140800035106241d4064090000d0034aa10742d1151800c9407581a070880701441944580001a0000340ba0000000d1191005603001200c2d0f03e0b1543c183d8506041c81d074144088120200d0201d41c0075003079800801038040d024102064202e0103016164a40415a03440303403045804d082039112546a41011a8041c002180c4981c001500c503509240981c5040382190f03004c120018400d01c140300c05a660b54040b02142 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 821905089 1250 821903839 821903851
    0x105120a0b250f030b182703040e06010f02150601030504081210051804050a030e060c16170606010e13240302040b1c06052503060e0601090b191b05060915 68
    0x70728966a41c1e0502418001c19055047c5400d0b4a001c00c0c1f56500c3c100b00083c20280141d001d03d1a0750781400d2001400d400c0d00c8041110641d000780c540c410420007070601950b88400c1c21b0030f0100c2c50b03540350b00d402c40b41807140c82c0b9070301211540c140510203248031100c0c415099501c1a1204034141624105c4051f500c4c030110342c01041c503407002c01e6220000c0d00c42c00300741c00300c0c0c0c1000e04101e042445202c10181040b801c01544c1032011810441000710700740000341e030301036010f01e14050f0075181881e0b00002c0c5841e10020f0820702420843c1250911104d11f640040b1450300710300706401c103011032030b003900f80302500c02d1005a10803810074040381d0720303807500c074100590711112300e084c010b441d000f980e84040160400610380f00d00c1406556005015019124a10b00c104055950010340581004009890000042d2907941000540304090101e030300824100d50b1007407105448050b0315060800102c0341710500681c910a0f45901c4040f50080020000d4030500a441d00c07000e440d40341c401c0c108078a41c0140c0c01c83d91 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 821906339 1250 821905089 821905129
    0x106030b04020f0604120b0601020d1d01140c1e0c030c1e0a0b0301030807032010020c101503060e1204051e030105130201080105120a0b250f030b 64
    0x11800500e02000c212110070f201078a01030806903601074074114082181c00c1540c55101c00f0b400c2204942e414000b00b48190211308000510404003684101004010b858480c103200e2402d00900c0d40c44640c506032910035600d04103d68100140001e071101d000c05085242001d489881260030503442c0114040c202c882c4040d242c43c54040e5164424414420003612030b43c0c120f20041404114000c1004c011070280d0f00843ca80341e5a00c2461074018100b003012040741c201c2c1030420310203d4642c00d02080028040309441400340c1c6607001e402d42241850180449840e1652074203100e4042c00090106140c1200e0003080104214120b0140103502c403510101107041140041106001600d48409601c0300e00c0420281c04000c4d41d50000824211403055a02c40c41030031130044004110b46c0c0c0041d0003070140c0700a60302c000e031800040c85041c0d40c0c0e072000480140b20b00c0e24900040e5110000180010b901c0d0040201c0c1e000300706007801e01424031401c07400d0020000c0d0801c03078801203500b443c039001c058200400c84 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 821907589 1250 821906339 821906341
    0x15100e0f06030f070c1b030804140f01230d1406030708070807090c020f010504061a01110a08090d0804060504090506191710050a0212010806040803011202151b0106080106030b 77
    0xb07040b00c280503911710845220740b43c1006401c082a40c070380da110242d803081040e5540c407070812130300782c0b000c0a41c405400d110700104861103000da640802d4030f091418000d40ca600e1072614514011000307016502c4491400c40c40e100201c050481c0074988640686025025100c0050f121500c052320383c022805120701c25407040004109810146d80600440c4465206a81581c48504112400d41d14141c40075a219912138410500e1404420324035090b0340400d003401d44c0e00c3d48000000680341c8041d035034050006c0b1030120303a0b100716031600e5020010156101c501545e56544074500900603030414000e480041d4031f0a00002e0403400e14200050458928584403100781c0e1500b00114442640503520308136a0282503102c00300b10405014440c000c02c603048001d03837920310035110402d900d01f050b40703d051150b000301c0c20300011500e50340c1103e043d202e00103908000c0180c18004180348400c00c282c0c00c1a80720002600c00c09030451445005e001c40c591900074444140e40704807050aa54103400050031041300c004c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 821908839 1250 821907589 821907601
    0xf1401090c0207140d0309090c0905010e011817030c0d11060a09051c030f02181003050c0d0e2b02070f080706200a080703230301060815100e0f06030f 66
    0x1d00032005d24070900d01a140592100403980540e131200c4142d602040d640c2c0f01c00e108668010700c0344800d500c001e01c3c01c0510f222424180e0a8403070072601c43d900d58200d8480b002020a4028802c55111419140c00c132292614551001400d9081c6001070705024012400820401e2025000c0c4a012541050003020307181080400b000c460800c107690607040c10f54655480f0944962800580b0844030402807500c2040041000e0141c1c5c0c0420703135503e008142ca440704000d44500720b08107449540f94459400110911403103c018908845c10550403e5800c44070010f83d00f0028000d0b0005110520764213860719569a0400c1c0318132902c42e40680803164201c40028840d0500c522103902c02628132611030344940c5104091300b0308103100d056003910030100000701001455040b08011b22807400d071400c80f86600700043c8a00d40c0b140810300800d0100042100440c500e035109e4071080404400040101080f140f503c00090320a2205042c603501a5103200c490000e0707450060180e074130851400200c3c0308166600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 821910089 1250 821908839 821908849
    0x11112090d0e10200c030708010209151b010f0b031e0d11010b0604080304032d110402120108070f0905060f1014040602100b03011b120f1401090c020714 67
    0x88441001004082004900312130807080e605440045410041d04d002d0840700c0505007886450b4000304856801044900074644404910070001e040d03001101d512299404e030304e07000306100d601081c21258204001909900b501d41c1c4003e01104044089407002d0882404401441d030103032103140c1494003e400f900044038010051052b1400e0210000a1908107060000f00c00c4d4000e0f802c140148c0c1e00119040c0100900c2d4200740810701c2301e111450695000101c0410744c85405408014001310810a01c0161a12590141c40c25000303403400222036503840b00700d2280e5a1501744241002607054420014901855200d801c0c0110700213442901501c1002c01804100d82c03031b0327000c1c5404100340c500c01e00180c80c8420001d40003030a07540d030281c0001c4d910604101306499800d69031510a91501303000300c0d031a092004006220000a080907c00c400543d11102c00501034404000013490410114058000f820900c084c107880124104000038049410100d035540e0042c003908039500740c5003945030120710309 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 821911339 1250 821910089 821910109
    0x191505090c2d060f0412111002070f06050f0c1b2701141c080706111614070807061707031b03050402060702060a02061e09071404020705011112090d0e 66
    0x200299103103000c0d41c6040150305011b41140980780c103030242c02041c1071441c0c41561244042c1d035610040510703d0404503020941d071030700e200300c0b41403140001310700305d01000100c1944d1a61040c20280d540c1d0001790f549c0d61440d52031601b041c912810403141014005054643d159030201000c5140c9000f6a0070125200c160800c160403031039110b802403c9612840500707000d0014240e2052400f103464200514200c0195551100756512484040c800c841c45d07144418800300d0036a410217440c00da1a8a506419802c05030240c0005415004a2101013056030704000196180c458400280311182e403012401c5045401c00d0310501c0c5800203540890088502c01d4001c946c02c1800208007518008099000031041c0d0320044552000d60450f004000e10340542d10350803501030250084144907440d1682c03c4c00d407034180358040c1100e07401900b01d203140152150350540345941d81c410b0013004142d00e1020150140e8200c610a9848009403000040d103600000c55420205d143c29140e4111140b5800200600c2c050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 821912589 1250 821911339 821911357
    0x30203010f2102060313050105011a07062a02010c14030705041e05130f0506030607050910120603140f03190309060b03010c08070201110c191505090c2d06 68
    0x600e504042d03000d0f070b407400c0055004080740c812102001a00c0c2c500a0309403501640303d000510340030a4124070a0612500721900c050344440c0002d154100e03001c0940c2c2c96070701c0e0640e594001d01d0262180c01d0440d0158401d01866900b40c0310700c42071246901c1c1c1125a071100300c992400180d81800b04000c82d00d12040e1884172403a242110104241d10f450200c3c1030000031081c5004d019440380e1243c81040e666105203074000200390085c2031146004507020f0014480c0f5a10140121400c551050469124030680c181800d0844e00912000d65a4104006120000d1f200000036020340b4681101d03181000048400000f08180f0782c03041a031032170320150028500201c0c140c560a844034141c10640d80d082c410017081180f180ca0b01c035003d00b0400002400c41e4002000c40c280f501d410012161001c000084080c0b546500c0d04844c00f4500302460800d11840f45185480d50041c2400e00b132101103407000c550000301c0c10040d02c1007600b003ca240c03001e510401c40c2c0d0301941003039502411040b03050b0500d04001c0150350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 821913839 1250 821912589 821912639
    0x6062c061e16030906080903120c1602060f0a0813050a110409020301020a0306150302070b0109180b040302060103050c0a0b093a11040b031906200a020607030203010f 73
    0xc542c212410710b1100d420030481c0000c3c103a18060201680203130f6110780040c1200700540c10562410f644580511020345544402c0c000480da40c05080c0e00e00506d1500306a001e00640c0d242d035190694241d103500301c002c030400426015400a8428103121b840361803160780090003000c4030b1103582c550b54040c03c0803080c00c070b8000f0b403901c0340030000d03807424002858504040e54000842528140c008512120b0201800c010940100407000200303200d01481c4e81036401d0a00001110950104082140742000000501ca4224003042109058000c154941264010b6054980031201c0c0020070215100c0c600540990410034020045541485110029420070b04140c8070b0801c4207401078140508280145449001031680d040e400308050b1304007100c041941942c082c44920941c0001985404030a2203040c075113580c030882c5506021845e0031148200c488071820740300c3c1040c0744a04002e5a4070500d9194094031503040480c1210380303e231084034120b542011114011504005015801d01081074010b404a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 821915089 1250 821913839 821913847
    0x1c03050a031b0c050c030606011202090a03230712031d01170c1b010e070b0706020409180212070e0117030f0d1b09030305030604021c06062c061e 64
    0x441c62828500300c0040e8451860140513807403c1450003c030690402c1c0a80c00600c2400016608200c0341800c0d8107100901513100e003840000318000c1c1c42c81d50710181074081195460040c400c10340c00351440114020050310310480e00c522000d0200442c281d00100007030007400c20303010a00704c0c44000320412041450700709584402e2a900094446094500000070b17040068800c484442202c03245002281070700082c084c001c0021155a00c8611500c0780f9408407900003418010061b156040300c1c060892458200300c2e020500ca030307220090291100480c000c0300c040c443c51560810001c0c03094200c070610000e84406a0903c0020a00300003807c1100d0003d200502144248462440241c4100350135164006020444582944030084e100d020410911454810034008079900c8800c8952060702540c1c056616034500c1400490305030b103624141811450030742e01040f01d45d4083c503140c510b03c1882140000b900c010303403111006209440c0140d0760001c01044400c0f4644880641400c1d03804410030100e0078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 821916339 1250 821915089 821915111
    0x6181b0e04030527130c1812140703080d060f0e04170c0c030a050c03252309090607081b09100302042310030216020415080709050f061c03050a03 64
    0x1070a00310004804003981c03030300b8100044a03440b80c0909155030100c080500c005248c107500d2a4050b186241c058041024015419604c11040001e84015648000c26666030300c800424030004003d58050100c20f1011000005207410364100e1541c040c1d0342144001860300c0000d4901c21031944060000d6500d030040715030800d8551380500c04082c14a010744080c189521181c1c04141c140031440f030301000319654200b0034400c0303014140c41681c10f403641d04040d0002d420303100c00254016030020815541c058540410000d5800003c0382960059096454104141c0c4442e04404814100c522100780036002c2840903030b07034074600407540301494440c1e403d0051615440349140c90100d040001e050070703c03102d6a4403080042c204815509000c4405140031401c040c2071103000f005c03501c0d6081780030f44516100d14044045115030106103005100103c00c0b070340d01555a0f01a1400b4040440e0115030703040d40e0400143c0703181081c009588850710320800115403582982e5043d9501e412201480d000c040c4e41c0e05007191 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 821917589 1250 821916339 821916349
    0x312040807030605070c030206011202061201060509010906030b06091c0209160e0a0f121a07020a060e0a021021140a0c020706140706181b0e04030527 66
    0x903011a0000e0310749281141440d10030307035802070415800c02071800d650001190b404101203040d00c00f0740107015007510840c0000340180c0505480c5070741d8120210000944c90f40c01400800e4110400c0c1c81c0d84500c2c680c1c800d0240d0031a1104044150013140810581c1001d203040d030301402480c404460300605d40031242c0c0105d1140c1d1000c50381e0410414042c1868a500c40d00310350304440c1d2020403a07044142d141400303980c405d045181d00c0b0710707480000440800030800002c5400d04440ca143c95020609130319000d03400a607540c6810805840344c82c58150040f40d010310108411032425009000c1440a05000004a800001c084017115000f130350b00c3c1140c0c80303c100a0045851803001c1c03c4800042d03050681c0c14008172002d101501d0103540c0108801c002141e006040d40004044c1c000540d41c441c5458140034028004848100ea001f4800800f950308000454000a144030061400306901c141c0310b940203010300c00c09a07406004980103012010070288200c20b15900080c0e218840b184030610384000c20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 821918839 1250 821917589 821917597
    0xe0a051c0207080a050f1203091b01021e01150518060d020111030409050a0f050906010302060c0a0f0f0302010509030408061b1c140a0c050d050a1107050f0c1e0904020312 75
    0x207a85d0340000540560a46007000010340d1090f1100c499451414825407580e035035030022043d051792000861988180c0ea000380802c540800c2c1e42e0492450740c003c805c00b018001d0003103424560440b0503e100c02f08840c200035002e41e59100d580300c0741540684030101089140728a01008030b040000082d03408041d22000d01c0074000507d003284c0041100e0401c503007042d0980d00a040740010b403500d8401081900000011103a044903010381d402c1c0d942e0311755608120b04150b008030001c0e00e42e1815200302c40802c40300c0d40d004030103540294020401c40d191a8175254403403103144120542d0794049400700e8481d40000c8020040c12038003001c1245015203d582d0105207190054421141950f00e5020440d0915003542081e13102041c0c5100304914664002c0c00b4180d400b406461440042e0388400061904402d42d200804191100000d6070b141e0040740f030303c0380c1c1d18149480003002d18020004110101d042002d48918201120044969541c0c4088280301e81e00d00c00a205030b03490b1140301007503803103813070a20018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 821920089 1250 821918839 821918843
    0x1509072a081e0409110a020604020409030909060b0c1501080634120c0e03031206040e06090f0706020d17070e06190207080d210b100f02010e0a051c0207080a 69
    0xb501d0f2031629002504079036071260301020008003040024034156011801c15402681114000781010407418100d40680068200c61907062034104085240d11490003c2c101c6080d80d0801c4402d0024615001c10866400b80b05001041d444500814042c0e010041844044502c1c022502100454015690b1042c54000041c0021a1072000a035407803a0040c01fa990540040d810f014032059034400c040b176528880d0a6507100b55170b01040205c0c00b01d5469400040007074650070b040b03400c1410901103890321a031f419a10309640d40f269040004210340045802c1c51092010f0b00c0791451606200b4000c0c024540c001d021500b08188418552403e80e0707402c0140c980b401e0800943c14003c2522540039152004a030422169948020b1000e0303459940501c400411610580c0ee001d01150342185240181c00307200302a41c0d001c4a902c848100c134503488010804203001681c02480742110035038440e6150051014090035039044a450111000c0d442e0031030021880300780c81112129982c0b141d40a0034440b0840d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 821921339 1250 821920089 821920147
    0xe07021213050f0411030a09060603020a0608061e150924090102070e0c19021906050412051206062a16050a06170c09091509072a08 58
    0x180583d040c031402100d501c40741941c04002030b5080351428249400001e10702101992500c0102c6c0400c2090b400040007958003404001d28581c5030b200c00707010810101e403024000c88070881c001e00b4440c0441240c07000f03c0800383c080c0788142c20700b40350740c280d590100c0036140e0411541300f00450300c080a5910302d80c07410340c0260140e441c0c8644000090a10700141c0c05021074506200034072140000b031601f151810311001c4000c28a52000f400141d007020304038031220120304580c808880600c00e480e04001c1c4103c5c450311082c5600d200000d401e40b40b5000b400c560b03015500341540000d001d410a10002c01803000540c0a50721862a915203203000020310951551550700240b11448141c42c60402c454003608040304c0c00318845042810043c0303503c0400c240040700c1e0640c2d4020a50007210003084802500780508034406602d4010aa1424514401100d90156201c40009643c451040c50364809000f1907000254524600020703103548841140400c4d18015420000d24420495031500103810b55801d0003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 821922589 1250 821921339 821921377
    0x7080d110d23040509100503010b0f01140d23040302010c08070e010e060c0f0c190e0a0207111507110105030c27100c0b0606130b0d0b0604090f06090e0303010e070212 73
    0x1f090500392101d0142c414016081440e42c940145c0c2c00a01140d0341200d007031055900c0b00b50100e4060050600364000000da4000090340e0a40c0b80b5041000030b110313074020740080c0141003070140708544440303040b81c06000090b10f203050011990305c102920503240c0c40050102d4140a1080032031070910140d48000300f01381c4d121007800303503480c1032030940f81000c0d1203a19500001d03145091015011000010800c030b000940c000313161010480910040007000d40043c04803030000d46070b140030180b507500002060791140c42a42100d0b02e25845071003220700c6265100d10f1340e41014446900311010401440310850f99000403021488540c42d0401007070519940c980c1c49512041e941d0400a22800c000f6002c0b5004180801c4032200000c4038651b00d008880008115a1380d44009a0f100341c000d05080003142d502c800b001800041200468000b8042c10b15940c9003040007039070380c2d07010404450741d441400314240c00c240010840001822004c541c4081c0c0d50042d80c50b80801c041840001c2d41c0450070310904914060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 821923839 1250 821922589 821922599
    0x60a020a140712030807090e0c030106080f0108070515210f0a050402030c0906041803081b0316030c050d090c03030f020d021011070507080d110d2304050910 69
    0x7a21840c0e14405120240040d58140000107854243e0f000029003484881404205020f114598210007000d05040c024145e040002d00c0001c13690003813040100041e00240458110b012a0030414100e070140e01c0107000b05480c00051194001d07071031902c884007040c140100495203517503c1000c2d051180400c1c03c20f10030325100c520500e2400026020700c4031945820100001a02d00003030500000303900300c60040d40341ea21040002e024150300e0315200510081d5210b490101504098854055080c08003414142e82da40c8544041d2400100d8254807040082060341c1ca8040c0681e02c02d2056950a00d41140381003031032500c1d00c0540f00e40c80f100b03d03000c084918003001415402012401840028030180000d86200c1400950b569240c4020840e6290340d14404034810140d1800c0b86c8001e58041c00303864a217944d8208007500c0e4002a050400800d501014207500c1d81740110710306208890076255000399071980402d6000c4400701c00c0030103200302c1c400c0101003402e680d40030100e48039440001c00705040600301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 821925089 1250 821923839 821923853
    0xf091e060621030403020114070501020d0e0606030c090402090403020c0d140c0a03032c10030e160312110a0f060b01230412020d0b01030b04032c100e060a020a 70
    0x1d082801456401d10461200b070400401200e00322502445c10240c4014290421207075840360042c004d00942c4001980345a00c07240d41c0110b40001d01c5a81940c450381d80c3c59042c107440d20301801d040c43d80060030000040042c90311201868110b0702030310444043da0502800720701104c440311026603100000e9510401c546c481008030351088182640c402400c9481d42c0d40c0035180e5200703c5e0381c002c00000203407606094085184d82100f001000140300381580e0301b000d40041c000344400c1130500002d025201412082ca4401c01c202d008aaa0100401003060074000d001c913940241d001181c000c40c01607004000120b074105105804182c010301000914000c0352001402c1e00b02c4001061160101f040c00201180260409030340c103e565010440303000c00d10b10300c0041c584946004c001003031454260300120134090507400d5148aa0300c80e807070340f8400034001c21800700d6000680e43d014824111032012100b4904055050300141d80860400c11201c1080d000001c80a400c003480c0c0e800140d00000011042c0455 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 821926339 1250 821925089 821925109
    0xc1f0c0201180305071a0a060e371803050c1501180b0402090405090c090f060616140a08180a03050601030b0606070501060602010f0c0e03060f091e0606 67
    0x103400200701c1c2440e109500084081e180c0d001400340100800e40c1818800c0f8141c036405101080316017242140b4040c1030060040604c0d010f400d10030481000020807502d0a9007515644080303440300c0c4001c01c07130f25070081001500c0e80803a944141d520f5049a100c813030124034400502c0c0d0310075165030303486003031500c0c50030b103820444200b03030507040c801c2001048229a0a80700c403200d88be40c0d401c040b03140801c0700c01150107881030041040c0c1040c40c01040001e02800030440c010480000c0350456195229852042d401840603200d03160302c41000c05c88901131001304d000c08048640310b42102952400140b9045044c900480c800740c6042c3d00c00984010201c0c50000c01140c000000c0f9810b42d111801d540b0344950351181400010405e5100b2000709446d9503c0c0e9064401300c603804002804240c0c2c50740c43c001d0183c00074039110110142007c04110300d05010b041c2d04040404081c0c006c0031241e0759041d490010781d1b0081c0a40d8550f0003240504884a10301e607041d80f1760a405a0020001800c00c10144440c0b062 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 821927589 1250 821926339 821926361
    0x3050316150b0112151e0905091b04020706060810060501030506030a03080a02090409020a151b0b070c02281802070506011707230111030306010212030a020c1f 70
    0x12502c50441c40b01c0e071308405840b40d4810005000900d0036120014182daa11658100450000c1070034004541c004120300800141d884d900b00910840d01c40700388503692034880d003a1021001d103070086c1514a41c00c042c5e000d081640d001e00d4003ca8845d66440e0700301c0c241806140d85010042d101c0d00244444c0d40c1600416400c01816401001890b2194600510b200005002e0100040c1c002800b2512981c0701c0d0850960944c0080510428035500e0811404200c0c01408000c0443d407500118902d0440817440c0118480d00164254419503541c802200c40c100e64040c00c0342c0c49521a00d100c42c0a541490b030440b0031103000d41d101c0940c141414108420030488081c0e14070850700402020300091070101d2110704495804007000b00c00102080c03103d0034400d0b40e4100e52401090788000340c02600501590100c03035034003a00c0380c880e05444a00c2803500c91000b114980c0c090b07400507524040032810140216800b074002500141007a03a824aa6814022026880413401c03001b0301c481c008007645482142c0341e0407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 821928839 1250 821927589 821927591
    0x130506031618150b1201060806240310031704030c0918230607030f0b010306081b0f0307080f0f0304030b0601080a091218050a2d0305031615 62
    0x1619148056881e00c90091149203203e4903003610744082805005a140605501030b06035440320405d03901c21076900030901c41d02000446034004500c09041045900d007042c42443c8211b200c03482a200c044501d03620241405404210500001000c0748132100103101590861454580d5103140d42007500310120203030030141d5960300d400d40510140c2010211541c0e46540100c0003400d140c24550303450000c0762642203102d958003c01c030030021000c0d40b5902c114031f51002d40404001c2c0e07218420045084174903900682000d0340c8008142000881907500c1600c0c41c0000400d096040c07402d204c0420306041540d4440506680700482d9118658411320104c101101c01c0c000941c103107032850319800710900c40501103a0600c0701003c007043d40301115800c00917880380c221703d4080386801d001c84001c018081a81c81011000d102200108030792614000d00d00441e5007800810b25003103c65000d00f040b2008a00010441d824641c1d0000b0008405201034030001031000b4072101d07071080c9070500e401801c2944404040322 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 821930089 1250 821928839 821928883
    0x120a020d02030f0d0b011704060f141b0d090501140108060609040f0602031510020c120706021b061e07030801090501050619030b03070e2a0304031d13050603 69
    0x16401c03000303503142113082c242c001c2110340d003060059585401c02d1f2007050508034644104800e000c0306400c242008094880d08001440b071600201c40d600d08241c03065602031602c021400d1a404244010b0051448c03482e5002511090503030340d8508544d0003440300382041c03902c0c40042040d01020300005502010945003020f6516182d80c1c1c0341c00010703459400805059010000c03840360300c1c0104a180440902800e0540702418490029666034a056a079501c40c1c0c80440500d43c1c24840401c0107400c41d9800e40040603480900364228000c407080305000ca4100b10180400043c48006151001d12004154001c4d96a060360303080040004005070800d919031800c281c010841038841c4001ca41d280d41c8003e48110006c01c418008802401c4201c81c1c490380741c41111008940c0780090f0b140c0c2d40c01a028102c602003031440c41000e1810101900200350400b800030700015012038043c801400c4054070300032001c0d4086601c80006000854030b021100f29042c0d0b81c4d000c000c01070504000d0aa48603100f0b05602c408 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 821931339 1250 821930089 821930107
    0x1080a020a120c050a090203150103020903150c070501060308131406031609090204150e0d03021906020c0601181d0d031109090c03060316030b0a0905030c120a020d0203 74
    0x41c0034080d11a0340905007000581e00700348a241e40250000d020000e0405114640c0c03444444043d402c00d031044030191005900300000c66019208440a103840540034103081c0c0d03446001658020b00080034039412810400c00d20300011020300c107910103584114090b64644d40701003041034408015400c0a4001d00d10f90410b20300640c1c9244c213882c1d02542641c1418500c2000e00700480300c03441140d000380c1c90a4000f1402003400c00c2002c081c0c0300302c1c048964900160a081078104411141810f2015004d0f80205000c80120700c8100c03807070309e0081d0107201d02502d03181044403128170b4181c00f40d10000107815890030689164002d406103850020110f20340840f80e60b0b6111446440d1007010003200189a6207035080740c421010f01e01a241407000081c030a007801d03d81308008900a520446955101e80685035100c14404030040841d02501d4224403660340a54491003440014010030f4415035840c401404a8141d04104128209400c0b0440401c0c5031284007684010745410502c04a00c42950424405960 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 821932589 1250 821931339 821931349
    0xa0b100f0317090316090b0f0f01080603031b06041101031b230403050625050f0307110f160f080a1101090308030a0506190602190302070f03030809010501080a02 71
    0xc180e9402c4030b07244240c1c19000241005512071000d8040d05802000708442c42e514401a00a040f10341c800d8060200441040c100300c09003143c1d072a080e0703102d40001400805944141d50843d070040380a03044130300c0c1454078203030003a802540702406c1c0e040c0e5102c102000208011443c08003c020020300301445000e0742c41c004a418510580f0300c03030080002030401d050703210808003103444851161150380c1d551140c80b4107240f600c4ac041154140160a0040e00950000c9640c5007029030010880c5c2d6101e040c84800a00300c00e85504c0500082d0802052078800d44141000740704407001c5050b08001411230016084131034482c0d0600e84d10030302c420710480310100300003100811043c840a611005083c010406040161466091a000940362950100400100640c140e20690091030200c0316030100e42c218003818a0300543da4041c8000503000f0070001d0701c46888800c80312407500c0c071900540d0f6000d516410f00c0f41700942c1d00d82c82980010000c105212146100f031165a0140921001400d245845030b00454 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 821933839 1250 821932589 821932619
    0x5060f090405100e01020405150f030109050a110a020d140309190203101407090b03040213092102011514031e0c0307090f0e010606080c0f1b0a0b10 65
    0x140100040c0001800b080300900c000010b0f0420000c08020041040d16202e0007034005004040c0110b1824802c2c031641c032040300c03d50340d180503240c000740d1660f82800c031040e000c0c19000c3e005090b0700b074032402e02486896041c005403418401d6940145440c0c80e40d110014800303110f010062400d034500300300384502d03440041200d038128184a6600d00140100e071000c82d152462900c00114210b1030603040d09110045001c03600d0144c846641e540c43d4191711075a1a16007440281d030001c5d80600140e0052210956507000050f5841c000e066021700c0c403450340a00f175445841082881e0040c3d55842d4501440013a0b45040006130458a0b410b0304843ca18801103036455201c00e01400101d80791100074000d00e0401c002c45400600302409440e034a03551405548040c019410302c44004c14200544442a0360052080307a0450b0b1250341c58020075182c40030320702002e900540034810022400c021048621114051484600660300d00800f6803112070700b00400b019201510820b40005284420854440689044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 821935089 1250 821933839 821933869
    0x90103050a360507240201050f24030109050304230a330504230108041104091a0619061421100f0501030b130e031b010507120506 57
    0x802400d0294208594280302e42c00809074070a0030000308038108400c99100700b10404550844107400c00e241d0580c00e0740d1003121003c003852001c4000a40d8a40c003284000c440e151042c900220020680b404282580d83d000025195a40000790070401c1040041c024054000c4464100d2643c070000380c0007a035600c0551051982101200080c149a9602c41d503a6180d085c0c041d901c0700040100c4040054199041846148613040b002440024450304031065120184816500c000d015900c59680e8072542103500f1089400980e204c0b07040c40001e0000781414080d1110358448a802e240003001c0004105c0e40341c030300c00c40d5220101410840290889210003451081d14641525840804401403d2810480c505c1000b05480782c1802010b40c1d201c0c1e442010345019000302e462071a280d070019000d49001a0702950403489500030b25841001c00d501141c42840d401064910f424a852200390340c10402182c404141d941d190b00f40100325030004003904405c5114041130089107400390005d500440b0010007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 821936339 1250 821935089 821935151
    0x18121104020a14120105030c01050c06040210050c1615020f0304060806150f070c090b22061e0f1d0c09040e01180614060603160504031502090103050a 66
    0x10b2929500074480300000d81c0c142008152a100034001c140f102220a2090900034003510141c085294421400c48140d00314440007494507841c0d960a2044039180b080c2148100602071040100082080c800360209000784003000340076a052406100f401c0c12400d06007000c3d5480f070011014000340100981d011241c0e60308094255907200000329000c0d00c3c00c2407494111040018101d8010b860000203032031080e00851030320060a03281c840719000c031140800c10702c0d40a1184c4115500d0000c80da10240d080000e00c503400f040c481d680e030390710043c0c41e600b686c400024242c55440601c109500a149a8010f01d2601d5480716480c2e40e030244041910005402074103074a10008022055868a41110104070203510007000341000014200441e11400042110614140143d0f10f803900c881c500740c5070045c00000d0020385940ca5154004041c1c500c3d0021410034008144000004035894142c0c00000743c40c04000035907140500c070300040844030001d00031450359151144030800c14241028000142d040c07a04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 821937589 1250 821936339 821936347
    0x8191b1e060204150f17010e0112030c02120c15041a18030607030f0c02010203060f1207080715080a09050a140102130308040806180d08060607060504031812110402 72
    0x100070001e4800e80d0400c1e65180c000504040d24650310410482c426891503035801d411801440c10030312180c1d005c1c41140490302d442c030018408c5404070300005609034442e0600380041807a0b6404210b507401c4440380d0700b50300d40000340c4400040c14208203100e5a0718031082e4042c40d0504201081c0d0b00380303445c0c02040098013008150b0032690224445030441c5030714000e084500300c0c170348820000c016001407920340c45454140503500703000c640140266400341c6402403c1e03c0341c4842100c14010700c540c1848600d186441f6204000074100414000031000e03149101c20804409030349400508030003406840e45900340c0c60b08240710040350010a044800c1640120b1301700b418146201c040307001e40079115200204010781000041000b115100402c22134014105130f81250384c62500d94038420000046641894102100b42c140c05c5e44242100d5902c008020400b40c1054060745409049030000c4904402140c81494a581c641039505441001403903000001c0342840b14550320708820380c01c0c44441c2030049402003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 821938839 1250 821937589 821937593
    0x60412090e0906060406080a080f09041d0d0e010c050616050d0c0903050106060905011407060f021210050a05010f0e0f0d1212020315010c02030a08191b1e 68
    0x2540c41030080281c2407552a641c1441a04a611000251452482540340040018003250041180a0815007080f25281045600c1003c519a9880300518a138055600c0405410011200d1481c40b10034000b01c004004a40302004064030031280154200e050100d0402c150b00081d60009140e64482c0d4001a6220758480c7d420068442e40190004000e0140c00d02029004440c1d00100310f1044900a1000348144d696801065035400e405008140c006080f880c12b22540d4010350b0000d050861050300f0000d403403030752000c4032801ca800c1048007161103840b400a0140c1a03005981c11340103802c0498040520a1a010003c0c01911641d102c4005020303910101c0d103011740d610b0141d48a803200c06001c418813100e9a2030b0041c0c6a0f0740c4440c400c1c020600c501000801d080c5613101b42c0c0e00c50905200070301e520091800040d684000000800c0741d045c8203005c1c9880009510001034139803c8810340c859140090b004201510018078030b0340d80012158191501400705200040d031200350000b60110b0110700c00c0034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 821940089 1250 821938839 821938847
    0xc0801141c030c020d06050903070c0b030c0403030507110418061b020613020315040804030308070f050d0906020d1d1216060b01020f0109080301260a03051c060b091c05060412 77
    0x5c1c00001d08100d14000810103d00c20200042c0801031162641d132079040e0b215000884140001e0b41d406204a100340410320019003e00b00034481c0d6805055103003030980c4d00324001425517011130760120002040341d40c80c00800421b03000307408552021f64842854480304000081d40c0b00401000741c2030001100310400d0540d2000d00c0101c03000300810300410348a16140c100b050726503209120890000b01c01c1000030706030910580300110700404d03c3e50780380c2c170300302c001d103d45000780139800c000341d4040f0f9080001c1c655581092241001034900c4046c0ea22132540000001820542e01c0845101861810850300448408050460f03620075404800025004101d0004070b1800a255242c02c4156103045031400a00041c20f014504070740d01803044001c802c0046030502a54200110314007901e501c40d40180c1c00290180340500002a05600912002c1c444441001d00b510041e620910b80c80d50001081d072107a0030000c030910001c0d910b046152841c807002c0d82e5100e69420000780302a141580107104030700301d280702e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 821941339 1250 821940089 821940109
    0x40b1014071509030f1d10050405060a02100b030c09010302100c02121c0906020a11031204030308100509040f240c170105041e0506060405040c0801141c030c02 70
    0x300c0601c0000c110300c0c8200900a00c074085050b008245d00d01d20491596204100a02461001d00c460018a041200030300c110041d00345103140c180001400085465242d5201a0681c039100e03500519044d55055100821100c1c40c1d0301d0340c0e000c0e82100ca032a008030f4450b000400d04581c0d050314940418120b6500c102c1d0140864007009503c00c0440c1c0c1e4041c0c0d060000140f030450b01c9061010145600040101904d46501500c03c0d41c016070007111403c80800c40141c0c3e01c454400d070103810b071846080c0348502d0000719401a042240412068418041c90b210307107100f010081c24041d6030480d00340c02d00c0e490f14250a01004002000d80f000701d030303d59401428540d40c8080d20900c451003031040c2c0a0302100903012090b00d0117500f4465207031500001c1c040c6011f02030030f0360141c10800310103070801e83e000e150f401600c8001c19250b004a82000002144c1c0c840340302e003284001c115940e0301d04550400804a203900d10084c400740c802d03681c048c52017144101810203004500d0b4107091040b4001902c1c4003191307075555 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 821942446 1107 821941339 821941343
    0xe06010806040f1b170f0601091e030606120b06040c1b0c080f0c030f01140a021602030601080c010e01031b0503190e030d0b040b101407 60
    0xc2c15800100070721507000001c2002c2c8242c11207018020b124800181c00664403107100c0d244d00114401a9410040e41d4200c2e885a0a2100008140e840c2c1030050300b0300c01c507561001800020301c01140100559001605005241d95050706030346552005005841084c3c0c0b00300014500d1500e84213100b060300190316400d1108135030944604022004a10440759603910780d00105000d8000c03c402801d00044900401040c46a0710a2504018440301300042682c1011043c2c0e040b8208220310584c00b129081c0300689500800c0c0e010984040c552001940600030780c0008a800740011030420080a401c0e200c00c255006100d00450450b03400c003403071126940021003d150180d01c100021074208406200032500103100c11805411110500b00c2e00760070fa400040c05803100e00c614001d1400316001110200404c0c035035070380454074a001003004070080003482c0390700103c100c1c180019645520703 = true := by decide +kernel

theorem cover : BRFrame.Cov 821762589 821942446 := by
  have h0 := BRFrame.cov_init 821762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 821762589 ≤ n) (h2 : n < 821942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
