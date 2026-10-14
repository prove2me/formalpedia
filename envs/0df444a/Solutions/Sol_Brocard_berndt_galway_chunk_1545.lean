-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1545
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:30:19.767714+00:00
-- url     : https://prove2.me/submissions/a38bd9aa-7ad1-46e4-a14d-b856df969f81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 277697841 ≤ n < 277877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 277699091 1250 277697841 277697843
    0x7060b040e1f0903030204120809011b03050f0a0c02100e0109140907030b120106080601050109090911010e010e06030f01031406010e01030b040609020918010e0c15090105070f06020d1a0904 83
    0x125652803c0d02e01103001b4070807500503940365040441c403841405245405842090401e8803264900110700030740350f07081c40d6420401000a0710402c120b481811000d40908040105405c02110101c1558001095000c5064040001074508032003030030690380c44105d50005140d60007050b0000d458000118541910007090300080c1501c41c0343c00809505c904030591410004070000704003050b00d9410b034581b64031013032251034001900c1031740100d9400c1c5641300b808541c1d0390003001845034800c110015036084560381c184505200100e80b803034401c1d448138030046201d4000800b290300258110719100741c4002d03d140d10a04035610050050000102e040710704c0b41500d41111030103815650710700c0c1c90700251a060000942004c030b814140b0682000384005000804580b600030b20082888049559880110807421079004504400e0040781c0051800200380c50b1006150062071728603182c803401c07440314065004540e01c907030014102c140704e0481e1103141c015245a11148a103034120200054440d200580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 277700341 1250 277699091 277699153
    0x20a0b1f032a140108060f09040308041506080313060c0b010303050306041e050601120b01020703030509040e2e02071a10030b012601060501080c070c090207060b040e 73
    0x16a40a0741580e2141c03030b410103200d0720350508a6241c03403020725018901c04840e40400e003d080412064a4216040170b41d801014001090b0707542c0e161001c681c8040081c0094440001c02c046800f1690304600400d00500322410003960340f444140c0c0700e0408a6001c0e4004410060398030b11b50340c0050200500d00d41102d41514200fa229111800001c0c000d0a03642d1340350300604401c017050003040340c1d00e8001b6842400242c03140364040b02e4822403002a60791000041b80103030841003003840000c0c01940a8110941c0c041e0000411400c01400c082c80d02000103052000e00c4059402404045d042401e081303600300184a0660400c01d941e07854200c1002d90211220340c88028034001504000b40b0b412100c021500f040c0d241c40203596612800b80145000c9105140d043c48a125090459005000310340440304107a407408656500c0720082600d0741c020310004c80b2010790304040007032664403034005065074a000b240b000502d400c054080108442c1c00d41049800c41d00300140749034004000d0482e4100e41d840e011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 277701591 1250 277700341 277700363
    0xb06031903211a090601170a0911060d060f15020706031a0d03091e0f050d02030717030d1b0804060c14180a0b071106070c05060a020a0b1f03 62
    0xa003111074200114007400c0c0103107081d004540700c3d82e5000c02c040310701c40705a0b080207807905c0e0344004403480503c00030060f8071100e0400100e1845070603980810388640c01841c2c50340d000c0e5140383c0041c0155000c0c00761205202d450b404140240d1441c10040001440c0d80300c0300d0754460203904406500d508451282c2c03000d044c0d80d406000f40c00781ca00d00d40b400010310f0081448080c0001490081c00c00141400742010014200e1107101c0401c0490354000107840c51954032900c22403416081080b1495140b104a8040c001c0c0000098481010549555030f81c80120142d600c500321110b40d1012280042c26440004a1020f50542c00030740054503290010340010bc0484c030350003940c42c1910b4441045000081030000060100c07208204100c55000c201012030f41c0e8201ea9070303a80000d410502480a0140c800c42d465541c21026160482c0108a01ca1180542041050395400090941d400c458441809a0010f00402e0304014560340320715403050010790301107804120311184c101100301c3c9000c01400ba407614 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 277702841 1250 277701591 277701617
    0x8010e04021f02011e0903020a081806030c0a02120a2f0708030d061217070c0f0e15010906020d03020705030c010507020d090509040209040b060a080d05070b06031903 73
    0x1000b0701040d91411240c1041407003111102c000c0c02409109040b00281c0311a034010f208400e543d00811001941560003040c2051080c0c844002d554065060000d001a5135200d0609545804020314442c002048030181ca03141d0a041c0641054003c00e103c500c6503604210000e010b0b0703041a00d00d000380300142d2a01c01c0d0b1001c0301250810100b202c501c0006a40700301100050300c001c001008219140800c8020710140d5580d11103a0303036228804400a010b91204260245118aa807029184c0640a0009004500e035144200307214041c964220b801e09643c0e803002c000c48140c12100341e500c94602032a200a8031464040001c1d00c41c4080000141090340010722a02400300400503601a0b0b03103518020000c41c2425071010307641e50150191400404c14080d40000c092a16450052185401410310107413543c940e5030b140707900c000c002e12665114400580100340c0e0241080b046c804008142c4980f0356170010303400c08146080b4000e0810f031203a403140007240c40d0a5190515400003e40c5410000b41d02028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 277704091 1250 277702841 277702849
    0x60203090109051903090b070507150207030204060909061a01020c010302070c1a04060f03020906180d050703230111090603040320010203010e340909020310210308010e0402 76
    0x990340b000f0b0028801d91980c0e81c0c059402146900000748651240059607548884e004480c3c01103210160031f0360804c0314100b046240350248400d144c0d00c50b105851031543c40b40c0c0058126040ca80090b040541d4900070f0000304105817141050b4a00106800c0010031003000000307680e440f14046070b50415030041014820000d1440300320003e00511041500096280341c1c1c08a1141c015200b0200050013031150060901e0091081311400280a4082c1c1d29010341080582036010b443c00403190080510180031020600c00c6c0603010155100300c0c5d500748288600c03002e000c00920118940401641360002d45801842d90408685c000681612056100d1740c96040c00da0341001d43c04954a4212550954400810b0040d4001c40c16540a42da20a40c0380d1034035055180400840c8003900070000d0041c114200382420102c0c112402603103464a2045203488070b0601c0142c3c0c00555429003c01c08802c0c050100b003000750342e031800c082076a80041c14000a00e403030003010403c0602c60091080708290208082d034403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 277705341 1250 277704091 277704101
    0xd060f0f02030f0f0f010f030b04080f1c0b040212010905060a030209070810090c08040f0606050a1412010c14070503040b07050a11060408150a0e01150303080f010b070602030901 78
    0x10403030034115201d2030440301c00c00c030181048840e04803007030110000800d07401d42014213030b040c0e0f01d0000d66449081d0960341d0b20860003c001d00141c81d210030030b04c07182c0c407100c4174000285600a08042c00e0b03204580d80c3c2030b0010585000300e030114841c900501c050201c08003000b42c0c05045a40c120b002203001d49601002c920201c0950304007030f41007541c480422161035080700c0c04074024244100a4461680d903440183c0482d140e4100d0200003965010124000c10900040000524000c2c2000580684da0b500012245450b84d8010340189642c1146200b42d032404003003440d90a00240024000300d507189a00400b014140000c942d031151001c5400000d0050420550340604400720341c0380ea642009007000c079541c0c0d004030412070f82062450345440141c1404015502118800c00003401140350310034074410002002400d944909070340340103a04800f8401d0003007a43d1303403940c800d281075100d08504005091080060009460000390401003201000e403804840140340c005000585075150380c81c1141c0505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 277706591 1250 277705341 277705361
    0xb09011202041a1314090402010e01030b03061603050c030c040b13031b0305010c03140c0c0a0b1e13030f080402030c091f1d0a091506060306060f0e0d060f 68
    0x2c0c0b02c03c40c0405011a4a0001e000c00070720b060711071070740d00e544400e1034100500388402c40d50401c017007034045001940281d19040720038005040100d001c9900c503002c6440c0000c00ca401600700800d0082c0280b003950944a80740d08001804422403840c608402800b0140c41144103010030124001000301031020050030100103076602421600c0364540b1500b4541c01000c880c08140c07034035407802401c040c01074020f125455480c0c809181140703041ea0341c100b1105041e013009400c03102501501d00a00c00260f144d12000c1d114590308840041c1e602400d000c0804c1428004055400c0c2a00804441000c00d4101c41000f8404603a454500401c2d03890b480800d0411004421540c1c0114402081c00110203e05810801d84511207601c1100a641c0c0c48011105201c4003d250301d0000c91140458299441070300090b020034082e090001c0e41c4102616200f048803019405030002035504c140a0007510350020400f48042c80130b1500c5080901c0400004182e5580340500600341560390340c9140c00c81641c0d401120b094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 277707841 1250 277706591 277706609
    0x7050d0e0105070e0306060f1c0f0b070905100804020427030c0201080702070605090d020301090f05010b01180302090a050601120603290c030f040203030f030414160b0901120204 78
    0x4800403403601030103001c0c26901007010a4000707200d43d9440c1800038400340309000c0142521301050074181805007503c2c003210f05a21000381090408082803085649130151403040740c2040161403d91030041030400f15410492091080084171543c41d980703d000d1a4000390102d0300094103400d030100011140340a07028140b9415482550f5800345500f1021111140c0c1c000c0c5c0b1a1001a5181c0404036180c400e00c0c00f0b10780100e01d06111080c007506010080d2100244040d00010b1340000d0703138807007a401f14001c4204650581d1140c17a001020350b07000b90b10310380b01003118110401e42419580054041d030001080c01c04802eaa03540081c2c842da2041494180780c8a518108020050b1070b0300b002001c404400000d400304601c0a1444140301000480d403038414008010aa421a26a40000780300300e100640203a905100074007034580f660703c00c3c0f001075004c0c510900c0d590804d0301400b41410300b4140c00303590820100754081010400f040140044600000c024a42850b91800e00c051080c0280a2600300e0004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 277709091 1250 277707841 277707851
    0x6030604030207031502070b160908010b0d03110111130f0f0308030a0b040b090c0406030b0a150507050114010f05281401021009030e011d1807030209180a1503050604020907050d 78
    0x100c2480a400c031a0100e0155032b05015551540480c80c00d07208041101e0380c1009401c010100800e111b85480004196400e001092451803880f0f030f074080e5005407160054003449184104403850f654880180203000c00300f0400c8002c0c0c556143c1212500000301140042610b4403003401c05a5601d52184005a0001303050690a081004c000c10054100c0e029003c0031901e06203581c8d00078070300085500c04480e48905a94005010840c08551582001d00100e40a40d00e405c8400e2081c55808016806003445c0c50388510f207a071030201001108150325a114044407800c98060b40c140807607101030804e650003003800c000d081c0c13602e100403071078a071500036032882d507924200100f4105a40700402500341c5800f40c1e17034a603035104261020040f0000b94450305621982912211509520300000c0a9020019050050400550304081515020045020800810316400300507200e03909120b41503030a40001103e10403e815a03039015540c601c0904040d104660000000c4c05072803062049490184841c101841 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 277710341 1250 277709091 277709101
    0xa020c0d0305062d041d0109051f022809030212060603070b13090c12020706150b0403050606090c3f0c0a0f23040302040506030604030207031502070b 66
    0x1000340000d030348881c80b074210781382c03d040480d22070341c91802c1e02e4a02582c41134002409000300b00003040040343c1e0031030348440840240046c3d07034280f148404250054001e040d0b048450000c2c51003c0e69600d80900b0f0b0184103201e8040d0040c00038055034070220041003003961680802d58280c96080050340000d6200e80491078014210b00d01040c1c3c41c0c05084194100c50080f84c1324504181c01d8040c0310040d10000c9800d103c10840140300d40c00501c519074590a00010a04001040200f07070b0344070031002c1d1900c07626060340c0c0035101c0000c0010b00081050b001a04e05244c11550340b0ba868903006026284221411008943e880015200702c5214691098081d550010b15205190350003000148074800d0724050211030041c880500a20391140d420040e00d030349098842d11060310540b56900c400390030012010741410060802900000700c6108504a1a0b2103910b144100002d8a10003407005e4002e41204c414403000075000542d00e020b0703a80c0249498211200c1d180140300900483e000617103100401300501c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 277711591 1250 277710341 277710347
    0x801111312050d050d09120215060901050d1104060b1c050105030a0c150e1e1c02010512150603070e01120e0d050d110301090204150c0804030b0a020c0d 67
    0x15105140d40c00c0310459640c48009252107155034074081c1403900708aa000c031401c2d21800085c150080986030005418150351a040e4001d1a06036100002d1b030710078a508089804401c0b210340e4800d80031220030485605000120b4030b0f07207100060040461100c9218003590703566641004001d041d940c0810b03525621440b280003541c020b640840b41059140000102e12801c0100c0c10025a6070004801e440062138104840f13100301c0b4103060b0f1300c20004002d55841d01550388240083c81c04171100c0803014410318003001c03c099000c00b03912001481c007000600c08010b0f60840242c03503004d5400b45544001c0d42d910180924a60084064194849800001c00400c20780259403000c09840c00c2e0380c0c1a201184502c11401185c7c40190610f1469002286c0380e01440d2007007004081600c2841000f00d024240310600160540007a0000310340b85402150074040e01c8400d5411100030100d0780340c0140d06401d0f649502c0021303c01c0f40800340c18040c5403000200350048030b03011128802c110104039400342014100003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 277712841 1250 277711591 277711597
    0x504050903121308090d1112030a0e010912241401031707020a031412030a1a09010b0a0309030905120109111806061803070f060915020a020f0109080111 67
    0x1a20b4900e42408140d000f01100d8505001c181d008041a00c0c2c100410304101100181500442e811101d0030b242a410b07440c1c815100d029003c0d81001541c490384189070103413a00400b9454181041600030301041840426102c0e0900590000300380490001c01c030510403014240c02c800649203509002208142804001100f4100d034041d14410300164171100301d4026510501c2c801941c45a4650000c1c00414182c00b80c040d04000300d10112243c444c030810081c4007940080340c500c140c46030765641203144d100394684040714091044651801c2d07503042202441c913901074410918100340e61600c0c2c1c0d034201801401076002400307005210b4000c909c440000b040c068400310a00700c80e01c00a92034101d1150030981400d080ba00300101000c02c03980c0d100c909010282e040300000600c0c03a04a20f1000c0d09546042c1301030000342c10340e0108146600d0811034060032146043e4041c1c00e01481e0144100368107503001ca8514000303075046403100381152031640120f8400c00305410019544d441e0035101d00c1d140c0c4a203801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 277714091 1250 277712841 277712857
    0x60f0206061002070b130f14010e0f012a05010b01030908030f090309090a050910020a1403060d0b07050c1b1e04090b0114120c09061203400305030a180504050903 71
    0x315600c0d05460303600208c4800550900c040c04507400c690001e45500c3d000c005820504418034100040c40c01400b28a021814900d00720070f008002c0030021414800207005584901400703080a11000210341d803400344601c401042004002859004500c18080620444803a101d00400003075070741c200100d0100040100399004003480c401c440f09142004420300035038080101c540c4540e41c6284814141113000d45c0002c0001e03603c00c81c80c2150070006001ca24155000302402e9507945c1c0c44010300c4001c2e030302e441c0e01e503400c000401c0304400c007a8683c0e03581c85040003a0510f0219070f21800040072404200a860401d0700100f0041002d000803501000d04850018001d108030761106e40840c025412986804e030f041c80254001c0d10980010300c482c2003030b101509040549008503482c1c5100756003107801245d2b865845005102880401160b1101c2000c6c0d22001d001c45a0303410034143c1e140d651030546d00d04c034800528080c8107412850011705099690401c0081401810500c19031800029aa07100c0d842100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 277715341 1250 277714091 277714109
    0x21201060905040309080607081014040b18070906110c0409060e0d031a0604150c05120a120b04020a2c09040c26030403020402070602070f0f0507060f0206061002070b13 74
    0x1f000581c02c03131094680d10b009d2807442d442480d000e41020154034001c45500781a40d0810389414a065407500d4444c1d00d5000d281c1460458169410178880c024000c140650241040101c04080c0e40c2840300d0200700b00d645003c04860026010384c0345e15110b405069405001b00ca2809984802c1c0ca0041e0035801222081c80b0f000c000c0070004081c941000031500076409950300143c00c24400741d49103405072040e05842da01800880e0b000100603035581c1c1c80c80e449080100001102c06070a5052504140920f041500d801c6806508200d500d1100800e00d5500d00c2030b1040424200c0c8050221010644041e501d810015040c11050b14240c101241140d8251140d2507641070070b058404900b01c0c02101d00c0400d462a00040c0d0b140c2499a02000040d412026080d90210350811141002036480c001e501c40440c070a441d21144a01241032080c10245158000010f1001c0400c00c81492940410030303075400300f8202d84041103030008800880c0760400359001101c48050010302124840404001a02100c2040d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 277716591 1250 277715341 277715353
    0x9050a02010f1103070b040c0308030915060d0f020f06040906060815040606081504020d020c0a030e011103040501200102040b07060e243403060e0c0702120106090504030908 76
    0xa60121800804600c080f80290020300c84d010016112480081c0c01501031500d2030400c68076070301c82c401581e00c00e554006444d4001c1d00d40100c241400c100c1e40b44c3c04281200d9400600c50561170711040d03c0f429040082c410440006031080d1030380e5040548010f416401410441561140000362032805d00307507028411102117080c442124074180c001d45084d030320b032550b455a440c2c5800c1c07040a1107048908025900c50740038403030704c1d1980040380b01401507582e044005080301a090705000d882a41c2209509040002a140c008058070001044804650082c03030300040304010102c40c0081301a010b81c000c056035000040008402e0140300141a4403170040310100005100d010f0401e82d80e6001030b0151900c8030111000030220f46890790000da1101d00c1d03c0c00041d50340201000b080c6120b140c03180b62a0032002e00951504041c0e8075100e0f0300058107000e405001d0314244210548031500840400a00c80e40a80041e00c000c0c20742074200c10018418a4003c0c4000c3c1014540500200014040e41415101e51 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 277717841 1250 277716591 277716617
    0xb09010b0403080901111507080106080708010f140f1c0b0a0506090406090203030903070e010f080f06130f05060a4b0608060a1b020609150a06030609050a0201 70
    0x4640490f94000000e5203010404401920892241000c402d6036010f01f07030110015000710a126031013004c055580008941c10210003405800313000d0f0064081110000c014042501c56008102c00c2c0d4900740303c00441100c011000422003062031121301e80255180030415071010741090302210440c450b520201256981d0410310f000c4036405c41d0000e074021022004540410041d500c114a81c50019003982c1c80c00b00e944002c00d2070011690302004a180140c07004008204440e1075150140000d2405040103110b40b80f5440d0340c0340d42c044d01e0b5400d1809801801001c0100c1c403090380d90402d90041c2659100e2070300b80d48038402170641010304002071503e150f880545801c002680c5808540035404842a10314060f44500700d0901c84c5415a14155564800305218a082204034422001d0040c0410441407040c800d01c0e5a03045401c044080d0b4ac0442c092056a50001c80d030404090104090b074429179446c8007900000d8091548003401c00f500c4c012065050003008113120441600130f80f40d8008590007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 277719091 1250 277717841 277717859
    0x6092a190305090f060106030c09050405040c0305191722080102090f0906030d0320040803030402030c030a0308040b0c1303050a05010507050a0c0b090a060e0304030308091606080a0f0c02010b0901 86
    0x41c40740d022154000c0c0f1700510a680c02540803100c1c4282514203c80b0182d102d01c08607044a2043d03400355004100b000007001008010415060000c400e2000030054002302d030f440000490044200c00e400f00c00c04124403071000e5203d00d01c00e04222a8403201007240790745d160014002d500000296010f5a0150305600342030605070121409044080d0081c18165500348044000301052008000280101d0b000f100d030b003500c1403005e44042c001000180d542c07420b00340704051401c43c40b039401c1402034100713903081004290098001c5502030303005480601141e481002e11402d80c450341c0c500d07504008001c0804400d115002482d08c802d644290003c000940351b04900303a450380a140d1000002465400700072000441c9505500c0d003111901e400c0b078800300216035411342034500c5800002c1003640003080030021305500400d16a00150180c024015004030488a680100500c1c05020140490b0030041480c5000550080412009a1104000303240c0c088a0080c00380624030011486214108004140840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 277720341 1250 277719091 277719103
    0x2010614010815030303070e041d0d08070909140a0e160b18040c030213060e1f0e03060702010c030b12030405010c03090e1501080106050306092a19030509 68
    0x4984208000c1480e009401114400b0004080f003410340c20b00c031004442034038100041c5000300029240e000140d00c180d01404122030040d05070180e01103810f58128080c02d000b0498405604092a003c0000e64a01c001070fa10343d180f44d44a4901c16240000b01d00e44942c600c1c4416000307110440f4244403c2d2603c101c01c0359034121291030035908111114040054828507002069640603071244a2501c03610280003e08865071078101e5004241c000840d40c5810024007051070180000d410300c51003a0a280010681e02c503403100c2180220050a0321a84d8810b001d0300030040041c0c0002c0444160f441c08040090280048010810100c0c0c10251041118648041c0d2121703c0441d5800950829182900446100070103010a4051180b6007134040b0303c00202081031071280040300341001da030b0358100000401c048416440303081080024028840c45070382d0b0318502a000690000c10030840800350503d07003c40103804c645424501400141c8011320a600b480703844103614140c808016039541d110380340351608 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 277721591 1250 277720341 277720349
    0xe0402031006053108120703020309011b0501180b1303020a0803100b0c070f060509060d0905030c010e010b1c02090c1e07030203030a0b1c021e04090b041101020106 72
    0x10810000034803901c1d100c2c00107000700032801c0001d000d403040300031013a80341c50041804584080724840018840b8070003c004668074000c0c0c1901080c900881510020340b41d0017003003001810070070314002d85295150385080301c4d082ca641000017006041143c038048031b19544901c000b100ca40c0150300001c2c02e1071070a5140c1c290b4590f0540c010303004003000b40d654116070758401040107404440c6c10502240c5200e040c00901079804441000304074281c1441c6c0140000c00195000b00100300080003040040c1d01c3d15402e9076840c5030400c4002c039581400d86802421030080d0590070055610304460505401c005402c5071005282c10f64104195840210094544112819010b504040e81c1400b18103869108002044800d20b0f202000c04032440060314002c66510003030080c2e0050b03001101348a00c104451003a141c641c00125503500d2600340030f62100581ca5030411000e80308170142c2801503030527401c0c00131401c40e000006004103c10b1505140c90880a001a40d00b035400004c00f0303040a4143d401445444c05507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 277722841 1250 277721591 277721611
    0x3020a1412030316080c070f0f20060702040911062a06040f0b07091203030507030c0e10030221010305060702071401050904050c07050d0818031602040510030f0804060e040203 77
    0x9600301d88404c5e105000c020b0803010b4482010000744011442c0384804004540c0305080b28058140e082c14000d480100d00c9409509a0080310307275a000b150b40b000d044440c02a4184c4001c03810b61711500707110f040865113104a6401100020b40c10b41c14008c0f4072a0001720030840260b41d0a40e030b0340501503554890741250010312031001241e00a001c01e00350050309902158501d82002613035203e0f00503100a955106040740440d4483c0244210f60760180908030700e4420b0780c17501e07101100451000650780304480704000d0515600017209043c0d0150203030008000c10000218282c0d5595030f00d00701d50340d00c00c1111188014081d0380800b0030080b40d00c2c0300c00201c0000503550a0b0926003c00100001000e000d00300380d200711030410078800000d44c11302584016540036107aa05e680d10b890302e0951070340e04801e46038201c10b4001304000d800000040f850030002d40c0d0180c800068035500d02d0038068a13a1102d0b08080e003d000c2d881052400c110072400200140c1d140380d990320040c0c010040034002a80401d0382c0364810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 277724091 1250 277722841 277722871
    0x2062a07020d140a06150e04030915021e07050102010b03060c07021c1509020f06070201020601140406030512180603010e190b04090507051527040603020a14120303 72
    0x545410000e50b5101401a0640780020046190440c0b82841d10181207a650b0b48909240d92030500c1c02081d80d0040101c0307200b80f50585400d03a4020301060040c02a0ba40240440e8003007a0120310070030400d4448070401001f07000c1003075007041d002d990784e007944a0340d4010360034104040518100802c0702805842c0d50107005050041903802c000100300755040010b000f0200c510190089101540001c080507000707140017841401e1401803149000d418441d0340d004000800500e80181da0000b0581e0455400c03040c0080c00442140016016240700e0384050014800c4d40e40c0b1100030600ca50003090a41e05218000c0c1c40e00307119000740541e9000904c50b60110480d5003000500c201700c0000c40c07000e036400c0d070500003540b400003500050072508000d0b42a01c0300e82c0480700c2800541881c0b903143e0b5040a009000138200380c13203800e000c0400c0c411040e03000204015461401215103864011501450b40107100ca9500394440003041c103801c1041c007010b403041c4084082d06502d2280401124052041c0c0700e00705130 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 277725341 1250 277724091 277724093
    0x212160909111e130501050d03050304060b0604080313050a0b07060c230903070e06090610180306020d1508071e0b030106020c0907020105071e0c0c0602062a07 70
    0x801401e1004068441d000c5a00c1242d1443e40da042401600c0594000300c80c0e4120481d00900102c0c80c64045a19101c0c0d01c4d020043c49280c3c1d96a6a2032140d90381460320603960b0b0b41d00d20300030002d4042c4001807900301c140801c011403144804000f81c6501444999a141129a290204100340c0301d54865503070100003c101e6240855520b40204d8001030142c10440020720341c20109080101d0070100500c00c070b41c004140c103542403a0074048030004147c0d54001d441c4030b091140c00605190800741080c1d21131304c060801903a6035070007002c01c14620312301500c4140100e6a2420600042d511907071000128600d040c1b481021400b01406070010742e0703805402171103041d0504403241c2d9107991540d060300f0103080d10070780000e0b81b50035000158080d0000b0390261488542140c14070401c01c7c4041c100c4000d5904010400c411720354050754403009070181008005104000c01801da83c5e04040490250420100ca6000b0a20380d1b00015410300409064001101052000c0c5001d02c0f900c04d0350390000170140381008188 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 277726591 1250 277725341 277725359
    0x609040221040309080106050301450c060f1803030809010e0a0c1e1503020a050c0105040b16050a0824060c0610090606050a0804050c0319021216 64
    0x107003102a01c0d1001a450750049034100444084002800c042e03030602102800380100401400250000d121044c1846c19807012100ca004c00900d40251102d84061a035000901514080f1042030b42d0342d0100c019401d00c1902c0c43e40c1401060040340d801c50104942502c0742c8003100c10542c00da1581100c0f541180d80c1290140c03c0a42400310075920785184100360603003440a070112512508114001b54607100e440074288000380401984032541d40000c12046020b41c1c80445003003010318006988908581c803e840707501805190100c0c540c0392408010410610130402c4d40241d00c2408500101100078000b140c10b0321440b13400b500011122404240c00085444100300f1020803049594030380b122440c0456900e80044040c001160b2004007400060450106a0b00c0986041e1b00d080c4141824030384044d06520901c0b030488108070743c10700000d003402820302158450120080035076004205010a0141c800e02240d02603208126205c15148000d02c00940c404240d00507166444c200c0c2d10f050581 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 277727841 1250 277726591 277726597
    0x51803120601020f0d030920130c091a0903100b10230f1902070b0f0a090812041a0c06010b1b030d02180d0c170703050a030c140a0206090402 62
    0x400c2c1580300301c0c0300c42c140c885070a200004110650303a4000401c80c2050a00d1044041100118801d800d00c407002500107480300d8098010b50044e0344004111920340c00011503064075198000d80100c104216040e40384198180140a80300c01202121440321920241000301e90300f02c010260320844400c0d00e07184072070250041e40110300c1c8880341540c0e02c0d1000d01c111407541c0d000609980d003010000500e80c1040070180c000d1080c88940d8801408110308080c20001c0601c03c022403040045400314071b044a0030300c550014405091000241c03400c1005044d01da0141d07402ca400741d0020003545010104165401c941660f04803400342e00200281c1c0d180c03101c001c03040d5000e07075a006002c6d06100b044515045080005100d00050010010b944100c1c0000030151076250150003442030800e101e01402140716a500d01081c4c1d1101d40d0020030304120300012603e13105079a0700003059402242100c1c028913411001c00000a4014010780140c03041080555171108045400251b02042c14044010142025809 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 277729091 1250 277727841 277727851
    0x40827040b09060f130216030206010302011b05061b0714030405010e0d0503091203070803070207050918150a020409090822030503071205160f061b05030112020105090a09060905180312 81
    0xf00500d0400c409003061b0002c00b91fa5419000741c4c1c0301c0001041103581c0404440000500c4200f00d0408050950300c081c5c1715003029201c41004412a96810310381c40510084a820359441b0300340218000c030500540b0b48941152007411f0224007481d0000071141006404030a245600c10003070b45c81c2135004801c00800051340c0c0309101d058401406582c00207460180114010700e401c0d0001c0ca840340c41c0c81c04024403e10000c00540304c0b0400400f400c2598000003c824516200c0b000d0000c4550340d07101c901e4002030287e58000c00400782800801d03402c0c04074000061035070b54000740301403016900e83e0b1250824a00140300040095008100500104100710240d41d02100a464400e1a03d005850700d503603490600002528100c030740c205080d04110303103440703400d00c020700f040e140790300100203500058114001403140302c0a1031803108140301160b1041c41141d9113014003c2c40e041c40e864031106105d00400f183e01606e4070040c40c01010858942040000d003a110503a40011840c011200110310300c14940689 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 277730341 1250 277729091 277729129
    0x20a050a02090411130e10090f0b0603030903160503060106030b0102060705071e05010506120105070f050918070c030210050c2205120c0103060f030c050108040827040b09060f 77
    0x8103600260750302c048684080d0610315000c1a004651b4000d1030418030488102050985032441d89400540d061002c0741d040b0760020083c15981d603d040c08a07045200c2e20070181c0d491302134201c4504888040424600941d44240c04965082c4e2300c0e584290120350121a01d18090ba10000000d140f01e803046d07008000340381c4076400080400501c1000d43c1d075a0006580c00f02da05945890411555081c40d661144a040c800b4000340070b281012007001e000c000106130f00c0010001e0000350b101c81900c078245143e5507403809940140162500c103200400307103202041c0031401802540c003d0328001c84103006060190120030101d901e0540c1e09025416400400e80c0a81109408950001050b60380c1e5600840d116803030300302400c43c80c07045200040c11203640390417600403a100e0f08028400315106e407441e5000e5900c02c0c03c0000207905d030340c20100300307078010802645d10b820850309608014005100c41812513100a84060015200ea0020000102e50481d01030fa001038282090b404c441c6491140d01410b140c1c510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 277731591 1250 277730341 277730363
    0x70512090c060d1b0306151215080604140d05090409020f040603030206011a0c10051f150f03020a0f0f0e0603010b03040209010f06020a08131d01030c06020a050a020904 74
    0x26002c900030303801c021180000c41d503580800301c015203101c0c03501590001c450b140802c079040c10800d031501501c082d250148204110b100146084141d141d0100d050454034180e12207901e40e549400c5a034449044038201c0d00e40d400f003800040404000520f185101160b40c07505e9050064500501000b0111124282d920022841745031100351039078459407000e18080d80c05407841c0c0d030400b51140309034801d00000700c0c080c03c0300700b00c100300d9005d0100c3d0006c1c040c0311f00348020403180c4404c5001070a5000c8022120030341c03d40c48000054040e440e03038960040d440a80c4407440c60000c056425412405251200350114907002d1703524400600c51501004540d00c1400c081c103218030141c2c0812520340098014140e001400418001945000c9024500601556424969440c180300001f502d1704500b641c000c001450128415145411001000010b003107030f26105042c0c503903007082070400d04000303200a0307818440141c0c2c0850400e1011425154541e00100100442c0e41107a090001500b40101309071003614002d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 277732841 1250 277731591 277731613
    0x150c07020612010503010e0a03083c0103030e0603090c0d020a1a0d0f0b010909050a060e16030b040c0531030804060e03070e04060905070503030a091d07051209 70
    0x810054201c03100c407200b02e1600c2e50306010505007100c5031104841040d07408109050002640302024a42c80f00c81281390203614102c41ca14615441070f022041c040c9241c000050002020710942e50340c0c100ea0080c0d660620141956052200a2006441040141d04182e00e40d5120303052000d28951403920141480c01c0c90713641e8090441c00c41c02a80d51000c05100c0c00074440d65001c1d980e000300180110700850401c5180d00d0980041c1140200e88158401c11791143c0000381c812015901050040c4070155006c608c601e01070201d2035a080d010004140070031700d2300c044404642054400c29141c40d901d611120300d0b202c2507031008038000d40c14850642c40107901c058060740013000a225203008600c101c100e50b8540c1d0400704040d050b21101d00a65000e0f901c280800c00401c4d080c1d032215500300e41c0003880002c91509500702641465000d030070071a01444000b5a0004655120a03140101d480c2c0740b03503400c3c954600641074451014240c8007500060014004e982101d28040750362038008030001c00b140c81c1d440c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 277734091 1250 277732841 277732849
    0x4120804080a1d0306011502060c0a020613030201062102270a02070804120c150e01020a060b0303070219050a05040908030411010c240b04020c070e0a02040e01030606170f150c0702 79
    0x7d80003801034a0350b1b038407000c0202d0b404000c0d1a070004142c1d207455092a206110080d0f84800c0103004005d07031100350200e841854000e51103803015100004011443e0a13420744038040709462280e0890080d514000c08120071a00061404090000c4a4104445440340e48404010390800c010907030f1900c000300400551004401241c0040603c0785102ca02018a80900500c00c81030700304201c2d0a001e01c280055181d680c0c04624919090f80c08500040e80c5001000400c2c614000d01130000e4205008d0f618002d100c02040c01c4090407100100c90b64502191190148400d03120f00e01d00086c0010030500100740080c0c0500000c960481040c940058120b15903291030102c40302c0c1e450140b41294205000400d480f20b43d000f402e000d40f006072004e5160440d0046010303512881031250040300d6692102040b0a040107404442c024900200c420505513181c1c14100c0c01031005100e580c04007000220601c0704040d02082c848880c1072600050001002c45050058445800801e5101d004c8420000c480c01030707075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 277735341 1250 277734091 277734103
    0x70317160f02030c09041e081b010501051c0c0e130b010e07020d0e03030d050403110109060605120c060409020c011d0604031d060f0d02090402070b04120804080a1d03 73
    0x700404241407405403500601d400d01c000381114034002d0f460030040101007010802c000c080450b003040221360094250800d140c003070061038042e5095556001040d0300c2004150805030686204490070200400041100224040c8400c0001c0110610305010080b525002c1c00300750340000c0b1061040b810382d259a030b58642c13107402600a10031700e01104d002d100784154100006940304a880c1040111001a400025a68001d80c1c0d0f94032101ca07240c000150415200e8000c100b4803090000081c000001189000b50180c8801c0c022079000303111350280e00d8181c0b00c00141c1d100c40180d01030035070351030b01d8113080301c010295205210446281d9290307403d04c20701c0e00401e10090321204002001d0302090401d803034000d210144604a0703691000059405031645e51301c2104880d5a0001801010b545940b03606c4200e001c0d00808601031360107407010502105000800c100c00d48145d1003070940c0009501000340980300a20142da002d4103101c4240700301307180356004a01640005060302141c5200404801c00607107025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 277736591 1250 277735341 277735343
    0x171e0705060a0c0605010e011d090f190b090c0a0b0d0207230c0d0302030a0509011803080a0807081005041e05010b040503010608030c03030708061807021c0c020307031716 75
    0x400c80e08100c004e11109218490142401c040c044805500d003c407a104403030081c2481d4171031090703540701141c030035101000f088260390b034810151440b5040b5081c41e4501540100d405950b03000000b0000382001c0d1010801c003a426078003c06001318181004e22941c0281c100d0325821820b16400c005840200b014400c0c1807025182142c40c079400002841c01190902502c40c40441c0260b89294451000940100a5915882d0305141080c0c42c0c10741c910048420310000c60352012250b0740351001100b801190801081108410788900e156511000d0b011078564404550f410306540011805201380e1502e5040700801000c006241c0c10317800c11483c2030404544013070b402200e12510001d0308201c641001c0c041c400c000d02554000d14203003000d41084546901c802090300040005a1000485a0743d03090014400795074079a0b2082031900d0710a60103076803031103544050401f07800d00c075203005142449050000c58541e4040d019051403851b40da104000c4244100c801c0b02400000d01040c10841e401103050f8001c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 277737841 1250 277736591 277736597
    0x31a090f06060c011a01110309010804030e030109021315050a031a15040e07030b0a09020a0302240706020a1d010c1511070308010f0e0603030a111203010608040b01171e0705060a 78
    0xb40d545c100054220324141c0c00901080e0400c4c8040d10350b0740e822858455001e07030103041032440141e5940001c2d006003c110f40c004e40c401c070812260083c1c10501d900500083e19400c2200304d0141d202c00411140701143c0c0300080900400d0660200414151300c04290428580c0c56071132001030880f0001025103141400d05511680007440410900c00a402d8054000720384010030041d804154010404105250002a00904045d100e41e000c040081098100b206034009030710b603c0da8940c0c0781c000041d500c6443c980b800a50031144501c0800b566860310280c21005840f2040343c0b425660307a08036078005110b64041903d603a008145c3d00040d0150080902600c00d03601d60b081c960401541c140e0f84440c54200d02c2900ca21131007080356940300002207500344070449c20f00030303565040884094540610a28030340c00303100d0040000100950400e21280c0074a1150b40c05890710380c0c0300c1048402e80b4100415503109030b440342e08844100d0900500003038100003001d0650707408988600114040d41d0120340001c0c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 277739091 1250 277737841 277737881
    0x307030c031106190f12150b090307120308090d03141807170f1005010609030311100603081215090a0b0f120303010f060306050f0103020d090c0b0406031a090f06060c01 74
    0xc0c0b540100c68040e00002c0304004c10100145247c1d1100c00c07115402244d010900000c1d202c0c559a0381081040d004240900c02c50399108502e160041040c10183c0e041030040c442d81940000b00c0c0d01900070031500f00d0300c0c01c1c0da5071066030750744462022295480101507801e000c2c0f018041400e02c0111315100000320044001d28464059a04080c500800c1000940c025442c00300148640c07544085880100c98041c0b074022070224190440070700b080d850038a0f44881602e051000403c1007000c2c000b4001010b01e0499040071a66040e401c0110b1b500390300c000d0740e0b0140320400003400c0e001d07059028041002015006480002810021504100001086428661020004021519241c40858042c095a00e02406118501404205c4021603d201141031503008102e00380c1c00c0a0030740c043c110498000040365102950348141500907409402400002400c02c000541e400c107000d05140c14040c00982440c0d250307940c2054000c0c401c08040c05280d4070400070010b10f0304c819000d00030100454880a4100700b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 277740341 1250 277739091 277739117
    0x3010f0b0f030604050706030e4204110907020109080c03030901051e0408032d16050f04050418020d050f0d03061409040623060f0307030c03110619 65
    0x4482810340740090310a51110040000103500030a142e41111000c0c02d000c105c0d242d0a4501c18100215840500c2c0220250034084100c0c07121114019200420260031b4000a10060400c0d040c4210488003d002c8001c031512846c4030303061000359682d0041c0c0c00d100000301e02c98641d541f14141ea01812030420350b81d00c04028098409000c0c030869800002c4001c9840524841c1044a0303641c2c68000c0000d0f04009004c00050b407801c441000c6404100514021700e48000b45980196010714010356940d1210000100c1213051070340114110340448125031001800d1500e0081004041c04600f0b468000080026412900684403407032a080303840c0c41400034040300011401c21780e190440f2080100e04050600c10200318841e00d43c540d049160b94283c4210895642c1c13402c0c0f110103018441c201a51008800e00c40701e60781c64090080b10b01401080b120100b5060200c401c241d13542c542404007424103145120104001030700c2c1480e0301040b0b20b0151001d400c1c0040038101c50249180683d5110101e070000b24105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 277741591 1250 277740341 277740349
    0x2d06040b0408150609071b0803191b0905130b0619030b0d0305030103030807090b0c15010b0711090a0f020a030b0f0306160c0602070c090b01110d0c0308041103010f0b 73
    0x1000080720070f810b0354080d01c1c0c460f000504440002e402d203000d1189400e08281b0020321501d1501005400c1150f02e590303070400d0191341c5001c54903d142441a81d140c2086490900303480e0049030b140c4542950381040150a04040000040412990508180d99014891090385803403000c1e0208a01c580b801e102c01c1c0c00082005010f88103003071030b03041c411181118800002500041600c3c151380d0545050111030750303101400c1d16003200f941c1101c00140004201244404000520030000c201042d41c1c0c20040d0b665003004040502404030010442d2000180c80009400c0194049032b005041360b201003659454202144100c0c2d0196050f400000d0300da0000d10b049050140340444c3c490070583c01403d00d13182080140d45203c9214440204021039a101d4509005480c1c0660382e0307142d0401d0403606819a40c005901c01001c40519160120b4811036440c5034800001c2641901d40c000d61711887c090343c0f8207607000c4078109802001151410015421001662030900c41e5210220320080f00040494800c4100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 277742841 1250 277741591 277741603
    0x1508010b0a0c1415150a080a0b01090b060d0606021c0c0b010905070311042904030302191e0b0609010503120d18050a051f0203062d06040b0408 63
    0x80e40003000800c02a051282d01015564445811460310301c1c800c1c40d031030300300390070144400701414074410040c00780700ca291144403162600315070031201d06d424265503150480d1074049804001d451030451600410040c044e980083d000700300c0040400d843c1038050814041210520b40065005901c9814241800d0f5410481d1402840050611101a00c0340ba603441c02a0300d014045d1595043d110000304607140d000741c009000440f81149001c0d20340b034449038044640d0241441c0e100450f050031894150003050141200c0c00d481d090390140504298110b0481240c000b0042d0407504115454038204090001028440a07035205281c01c40b10703030174001c040120307444060b0000380c0700750444810500c0c01c1c1088011241503400115020070000f004001604140c5641800038156003c0d2010070020040081307007101c0c403c1c5c00201100780c0345180706458000c90100700d40442d04481c00d400d071a104001201750343d48000c9200020794142e01149000700f206500164804c0c1c9801c40045014000024180b00e4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 277744091 1250 277742841 277742849
    0x5102610020903100c03020f040b03090d140a081005121b01090f05010e15032805060108010308030604060f060906030e0318090c0903070b0307030f060609062106150801 74
    0x4150708001000e80040c0e200c400030f403001c1c29002d50b1440700c3c5d42d105001c5e80513180d100590412094072965984002c0b0f02c2940100ca081c2d82901401d54800401c1d0b00685c401501203441e000320b0b03400d0030780018050b198100007500c518100228030200246540d07941007495401c404410240000102d424a072005000c0205200760500404803814803010040c606108104e4000746440010446040c01140c0c01d440c404021a071104800001c101011070f0366100d400c5011001105402802960000c02c1e0460f41e068490500044d40d107801080403940c80d00203107400800c010000a0010350b22070f4000b494050305d520401c007154001c0c4040000b030380c02d032151031040179a4034007440c582030220322142c0701c0c103002c20103451146d031072040030074000e588a4003a5083c0c0710000d41150084c86e101d00305580035800480714440003d080000b8500e5100c00c0d4040c40b0121001511a103260b1410a801904c4450709240a2030525050305040c103102c1e06180540c0d0001c24000400b4011030b14449401000a001604 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 277745341 1250 277744091 277744123
    0xf180f09061332040b011a0316021504050c010f0201090b0703020c0a0606060302030f01170a110103090611030402040c050c06041101031407030f0b0a0612051026 71
    0x800805464000e014240d14401c900c1c0012003112100d960b000429403d0031009428002104060b1410a151885070180340109001e20007a81d0f95108050302c400084100000c0d0340050000c5038031000b10010072040c0088078010754031280303c520121079480700201d07800d0396036034000c10b034140709940c100303505c1c40d5040041d00c020b02c0394a020340c030340780380007180601103070300301540003414000b12030f414051403078200c0c0e110006002c0544e94507030040c0650800c0c0c481640354580701c0000140b5184030700c12500e064040708050080281c0b00e840b800c10070000800d4541c10f254603030303584a0010704e10348078101440a100021a840341414014001129030075030f203010a120003004182150b042c0041c48692051f0301c074415282c0100d0703a00048000e4003050b1840303159418014180b00c551a0103030440d410002d220001080382d90100820800d14403142d204803004950710b10b80d03141c01000e081e048164045108005450f40565840c181001640081c1d0f40c1100c030003900110302240c5e081407000c00c1070075445070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 277746591 1250 277745341 277745359
    0xd0f030806041503020f060f130501030b01050c0a03270b03160305040201170405030d0608010f2904050402030a02090f1608010b091002070801050c13090c090b07080f180f 75
    0xf641c0d501d6000307214040a48212076003140c00a4036514842119041d1107020b0310140c58480868002c3c1100e840d80c02214042420035180d404154492410340d030340c000c04074005003d00d160070344007907545000c45010a0b020b21070858061814848000482004240048815540740342508801d01d80940464009003054180320a0202603a84413604500a51302401c80b545540c950785000c601d10312507404030405d40e50800200041188040d4001c0c107050139517450902450b482001000c0001c2c007580710745100e030381615000781c6007070a003544901c4c1e0041c40a0304880000140d600011188502100c0f080868005c6a04200b1004500c10402140244030b0030204415410452028014001d8013845401000d40d041c080025610030000d5500038800c1e440204094108440b50303544940c4054008410113860032400a081d510394850b000304400a9611203584a040c0311982c0b40c1717a4003100c0181c400c0c403000d00c6400b004405007401805502d403030048a040190200d030921101d00e1480b501340340725030400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 277747841 1250 277746591 277746611
    0x2090a05040e0307200a150e0904060c121b050711040203040b011a070c05090705190206011508010e04080f1306080a05060306060d140f072d0b070f030e0d0f03080604 73
    0x10440320801e4541d600711900908020300c47c2280e9050103500325540c018170302024081031080d5540544207901c06540d603080820f090700c2a90090380c950b05904403c0c680203564031484980314102421040d0321451f442102c1c2040c0e9000a8107981041c3e0341503e9805458004006c0d04900c08540c058843e8900001401c004e11a03c488400304003d119040c0034403041030009107154468002c41d003031200f03c101c904104c01d0340581d009544480074003509421186800c510311080340128035030350407a110601242c04c140d56913954054550802c510f00310002d80207200301c10840911a0784c04003d050342e80e03100046481c1c220f900318240c81014160b40d01a8004909001c1a52505951580c0890300208130000c8012800491850640041c548541501906c040402d0929110800100b0303032400003540490201003141d24036090390304d88225003080c603080100c200015034502c41d83c2180c50086c103182090303030204400715120034800c80c0126010b901c122520810160054107a40d000707441074504000284034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 277749091 1250 277747841 277747849
    0x20d050601020d1704170c0d0e0a0e01050d031715190e0a09080d06080303180706050717370302090d060b0303091804050c030309060d02090a05040e030720 68
    0x513680c0b541c2c4641c040080054180080c01c00d800c9244080940640d9035442c0d0055803546072100301011314009141c04408480601c0c06240c41e200340c401007000c0e4000c07079117014100040304803103080440c148a8644c90b5218103410900d4040d2080310425500158141c1c40e0040090012090940c01011000880c05000c2102046140c541c495104400001d80301c141d800e00020f5400744030305540040b81403c4010403a030801002844c01441c03980001a40d0158000c61076450365001d0180000284007400b204000c2041c003a02540d0450f680e0f90014a0308088003000c1081040386001d035141020050040c02224981c0b001a920216080c502141400420400600c940c15140b03406400719840e005e10705816a401d008076940d50340c0013401072402503110508210b0030001214103603000d014052403980b803801d002c4100d610f0040c00a08052a12052036102c600941000460503003000802001240a480b503100d030640c1200c40d100219103810192810801100c8880d15030180c0c811014040555521 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 277750341 1250 277749091 277749107
    0x11070c0e010b0310061b050708010b0411040b0901050f041d07020d090b04060323040f0506010e160c1a18070b0915030402130504060212011403061501120e01020d050601020d 76
    0x14540782040c0c05046100080c0401b9070190702c0a40356000f1101d0002d903d40c4150312141d00060150380c04d06c0b0750b011202100c019400b5074816584243c0042001da20075611030401812500c025010041c1004c0d1244140e03180001181c0244590802c603d0902c03008503010020050030256910f04040342d681048402d1141e4007461090006050311404000fa1090006c009865502081c4580c862180b0301030a05410881f404013041c4c2d00b034020798002103443c8141c8502c0b284603116206100032008a010070841c2c078000c0064041e03440d0311010702c48086130071034a40304c0e034000c9455943c034071499640402d64904001599106040d0450204503682c055250b84080b049150711542c030090300da40e654004035852421a5020803102c034030704020041000001c0c0e0141840e19000118603440e030780c892800340910300d030b01020740f981075000000280818209136400a002c0e2010b252800c80d1031031720b84020003070b5140003501c502183d40202d0036501e031700f8141c03288a85c400300074030041c14640075a101c003514020f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 277751591 1250 277750341 277750349
    0xe060a0e01151412060c340323070f020901090903140c011b030e07050105030402010e0f04060909030e03010c090509040305090d0210020a11060f09010509030111070c0e010b0310 78
    0xc02e0f410724090041c1d4400502000000041c0c0a80d030552030564480b0640780d10900100324044a26900340203042c502905a002c1071001141c0b400c01e12107541c82c04d50781403526840004144122501b120096141580a0f0100e6441080f003a540008144100400b4880c1608041c0e04903141400000100340d02031034004810081035038140d035810b2a015550b025040c108205421307035181c00410981c196141d07102038024a02902a11040d52312000111850302c42500c005e4001608100c00740f010303180254820b808000c00401c0011000d94490200b015a04021000c1d808900e440e820425541000c3c0074040d050996443e0940300b4505000000d000d400010388041c08000e4041441c07102515002c3c4501e45454000b049210000424040290740d070007014811500c280d00c1c02e02048030b41c100070f000d550810091503035060a081c5403800443d01a00008203042e81592030701c00105100c0034081c01058268000c4084038803242c03c26a08051101e4182e0000c0803d203020000c2103610204e07500324400303031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 277752841 1250 277751591 277751609
    0xe0703020d1104063b0c280c0c0e0121050c1914090c0f09040f050405072402070303031d0106060809010b01021b0f0a090e060a0e0115 59
    0x40202070402d000c60711408500305810a25000010175000d021060313040104081d14030703a4a400f201201c640340140e44103404100360028140c04100b641c0e000030701418809042083c000f0410f000981d100f00d508035002d030384901003042203d2000034010680041000b90140681a00307071540740800c1ca411030a001250049003142e03502603d020070200b4840c0d0f1101c40d000801001c40c0700030b08802c07285e28881c42e00c5184080303d46100758000d542414800389100e2000440601c0c20b10680d003020340000c2c1d0000d007140d41e105a86024412403ca0207100301401140140c005200c03583c284400e559245103e007100c2070000800e020307905185540040d40a041c0c90745440c011694890283c030568001e603170b030000000355500380000452031a41c0305c0903c510560101000744018640c807001aa241e14180043c0282c1c1280301c54146031a040103408034240341405461000c036680c0e513030180e004403000d0403a50260350b04182c090000290190142e00400b0748118000c101491404441c5505000c15106903481c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 277754091 1250 277752841 277752859
    0x10b0a060302160f1101030501050d0506070503070e040609020a08060105030f0c070807060f0c0207060c02010210050907081e060f010503060402010827070f09053112030f050a0e070302 81
    0x510040c02403c1c074a00e900c04145811030f1000d00d401400c81c50030143d071500080c0f40100020f01803400b40781441074690403201500543e202c88038201c9590344000c14603828030032800b5050020b501e0b540300d01001004507080041e250524840d0041602a0141c004d50420400340b09001c03a08598403026900244401c9045a64603104c0c45c01c810700e07008940000e894181341412080304040c00344c0021800c0e4500fa03007940d003502c4e2036046c140d840455001c0080d00581c40300808110014181d807005030888000021a40c2c1d066841c400c1c586400c0d400e5800c072010046000c603030b01d00a50100000ca40112032846000c000d581001e0210742d60b41c500030f10290410180001245d2205060580510f06410400c0e03104148500490101ea444025100b508250943e6200010b071000d8540709407801580b56480f1030300200005000420003071902c8a40f0f400950f114082c031000209641820441b500d0b0036200132948101230000c00c1c044441c028003c0100300d0503c1c40181e418000402c0320019658100c032112a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 277755341 1250 277754091 277754107
    0x303180102010906110309011508031c061e0f0806060d1e0c14030f0102070816030e1003060905090703020f04021b160302030613050a0f0201051903051008010b0a060302 74
    0x400f40a040303501914841c134282070301c1c00c00c1035080300546c89411180b00900264100b8a00d18100e2000340c81480451b82051201d8540d45401060082c120b4000040200d18582c0340c08840e402203452582d0a203213078040b42000c01485d040c0740202c000903c2564050100d41c50070101142074202e2010004100224407a1451000091103600a082c260007c4a8811407034590043d2022401c42d9003030140301c0e1042c2032441e004030340c0c140211601c141d071140c213860410724611551400c004410000b10248020480d221020b9194125940d00404103503801085261801081504440380a4141c9106400c05402400983ca44032a100c44001040d00d00580c4c0b030a01d039503841d1188980426504141c040c0e11070b440c0710000030784060002e50b03000320103940c05138444c8100b0b0030100301c2c81d0703400030219000140583c0c040b40c1d02d403442002d4580181000c40c98541c2c1200035140103c0d8002400c40440d41c1c40c4280240009121240b01c0540500002081900da460001800b001400c1c0b04000170160000340d820 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 277756591 1250 277755341 277755343
    0x90c01030e15092104360908030609060603040f0b0c07050f01061412071203030902040e07140109030308060d03030e071512020a0804032f0609070b090303180102 71
    0x35000340e00b40c46114072030700f41082c225442d2602c0711520b02036200128003d00003420780408640031994000e202c03030741d1205040b08008281c0030b03c05140441c8075080400f200183e5450003180c4540744104903843d5603203030038420020140006004640160740c184204030020324641e001c01c11040c0c219a80944a59a80f01002d203a4401c09000402074090507928041c9088150061000e450040d89145110f00e1710f2811712002100c003408a4940390b00511080020088102c0c0086180b8040e240200e2402e2168002c20140e84450840310784581c0001c03404c000d1a921121840d04042c0240f801d14019469600e0041c038124000d03100502c070344c0d0b02e96142410140654420206150a40107440c102907503208003120b60f0301d4004400000c11402c21400c1410b400a00c200c581b904825107803241581c5654500f10380c8204e210640b8006081d03000711500b03510740107140210340607990900500e001c3c03520542460400e01c00b94002c0f00381074400d015030070580d940070050f10b02e161a03c9802420144e0f00383c00413 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 277757841 1250 277756591 277756603
    0x18090b09070c1230020d050a0c09030803150d0b06010f0201020f22120302030415030209060a0c0609080c0706030f0b01080117032205011d0906010e1203031305070905090c01030e 78
    0x500c1464804145113034072180c03103030058144056807800400980c4d8840203000261224049413100049250109000050780d21000d0f64000d0851101c26840c0704d0a40b0102d420400f02e58810f032403882190003000035940e4014014030244215100035803e01130109c007943e21b03d006d020501c2401030440f01a05a11f015861107075002000e0b00240031000603240e09010f51242e10500480305034600104002c0300031030190088459001001e0310b060701e40f2411040c1280c4006071800304403001030300e6190420100344031f40041e1070f5a41c004005020483c1c0f40c1240030741114103040c2d600c4c4001c0d0600201b000203030b0300208664111400b03259010150040240b8090451140aa0880e032002c141158072188000300806c1006580003a20350031294420340f04101880030106d5051035005800400098203948511690300207281c001e003a030144020a150748a00315003003101c14a104040c000640000c3c010100180c0c0010081c0e02002c001e90300f01202e4568407a260560b0700d905141d01d0361440410034000b0482 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 277759091 1250 277757841 277757897
    0x120f0618020f1509271f0612090f060203101403070603021c0c0c0c08011b050a110a151103090303010b03040201120c120e03090a120318090b09070c12 66
    0x182c2005d0707190b04690303488032a0303210304101c0555031100001010b229480400108040d281d41c1407a4000b49028800c4540c0e042e00708401c1d0b903090300c904043c800294181f920741c81113480340c4805030f200d01c0c00380490075101c0704682c03081c0d541410941241307500351804990401520954940540d0300c1030041d0241961040c004401e0006514140941648076401840d507040d407841b40031400403095644100030300f6a400b881e2015022019080845078141c0150000c180740011070410003207138070800300132a0078058015029180c468203082c01442a0000340b041c000300ca00c003c10024158205103071030aa80e40014040e48401c13601c0000400c0540e8043c1400d00d0f1003000e0740a05001e28201c21500615a110020504543c58144200240c074102c000c802e0721075944002d480c0b02c2d0042d04d03000c0b803001546030300706080e028041c070248803080c1c0b102010a520058039416402254000c4030406004410300010441d5040001c41c48a410006140d5900103080440c1890036400400800c0c2c41b022b041d03450741c60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 277760341 1250 277759091 277759099
    0xf050415210608010f0e250503100b1201090305160c0302060309030c06090304121509051c1701050a0915090507020c0108010f05010c020603070504120f0618020f1509 73
    0x9908000c1d811604a54165030307078040280125901c079243ca0b01030b00c0140319040115040302441801c24a1290504034146103c01000d841e41c0b66a030001c2410b040c00b00352030556440e19028080ca0a05002404a84c0141510000c20043d8081d890040c200d0159408900d4205025848901032001d003c8060300a540c0060486030340742071280c040ca603a644000c901220f81d0080000003040c40c82e01005035411641c00100514649107207507141051203400315940308065568110707820106104202c0354a4264404521745480096007001a000c5d0303c0c03550000003e402e120340140301545581ca020003c032084034102103003894800a00ea900d045142d08101016442c11003081030f0141d000404503104802a241c40c01c841c0d803140c40d602a001d0080c05071350b020481d0b92410100500300314008551001d441c2c9010342c10306498507003060540b030700c00d00c0541d0700c5004410240180a414420078100c030021404000e071045403503001c2942d41009469040c8100f004002c1041c01c6c8950100b215002d6130010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 277761591 1250 277760341 277760387
    0x30209060f220326160609021207031a06030123072307020108131703161b060e0a08130e0105010c0b0a02160f1208070f050415 56
    0x19000c0451a000220908408940b10341c00601c035480c2c4549041c25640c0000c46000e440001003a00c8242c1c4011502006101c10700300810700d203141d5541c4558020324412003000c18090345a004202490305c044000704102e4201e10800c20025100f0348859440b044100494459540e680300049d004201c0510014160900c590141c0ea10058141d0305501c1081c240c2c840032848840c100e044c0710074810f03580340007181440c00c01001d00598043c0f6180c0368045404008100307410390301d942e8402c1d4221941198043c1000200a0120440528001544110882c50500d40100c0825001010405c1075040905801d80c0e03100085034160040c040c0d00e02c4d0f507401c00509591580c034468800710403a00c0b0300c50300011410314000815191f101f00080c20f010f64008d5940d010030b8030b0304244000250707c481801d45440c940103075842d001451a1100d410201d0103100344d02d1420301c0b0404040c0640c07200400f03500401c10f01c5010000c034a0342020540d020707140c8801400110b544c040b1015104d0b404141840390940d4900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 277762841 1250 277761591 277761607
    0x902010e06070b0601080106050c0304030f020604050a080109061107020102060711010f020a11010e0303040b0703020919080102130e07020a060e151008120a0e330c0601120c0b030703020906 83
    0x201c401134010349080e40c819003580c1e6036040440c0c3c1401015a084800e400420041010034509481410b1581c00140f05620b41540c13900090b08004540c1e02c10344680e511000114140b0096110300e03001c03000e51100d4149000b0305580000e45032000140003c0500c0000e403035411148909601c9810071410518003107540b040303450302c06030400d481e01900450302e60800e402d504045001005480c0142d42c07020803640d80d500c82480c142d020307401483e60345400c9090040324071003a91304a403d82c030042081c00c00059403000c0d444e0806264030420380101d200c0c41122400e001507a54006803500c40e051300302c3c20005096002c40c4090b81400d409601290050460030280b140111581078000c3c2102c2440088445a1501034505130b040e000310104840403a12100c1c5100031801c1c0b4612001c01444200c01d41052517490444040c44880420401c0520b104080b0300ca03840d02d43c0c200445c5014044022807015401d041366640c40506065000f28184ca542c04004130390780a010348c05841040074000c000c540c9030468 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 277764091 1250 277762841 277762853
    0x1e01060207081006060e0d050109050703030c1b050f040e03040e0403090f0e06030613050c090a05060f0f03061f030b160f0503060f2407050f070e1501030902010e0607 73
    0x4501a02c2002d000c1d11140074a680598400c1c08116100c0e0786031013007018070034400c00804802014094415540710f03500b2500107841403001c00003551098a802401c2c00b440d003080d400d0004001c0d20210103010490003481180d0750151170510030001200d0200e100348a03038040c90300794085d40d40140350a288540a0008064200710a10301b9114600038803621260b644003c0d203400b81064a150341c140d0001c901040070071044440c011034060181c0201ea60400307002000c5040311004448440c2c070a5591418440249018a8180481d000172100103004002003400661200c9018000c02030141401107910150040d0000c2103004540010600689140010300144030740041060300c00051048400151a28040e05c1a24000c51020b0f01040e400041e40e018804282503104082001200f030b984220030301100000201540da00c2a0042c01c50312984914452820015800c1030825940da50704201800c0080d14208050810034a00414114490700050716107924101c8980e07040180060b0310824086 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 277765341 1250 277764091 277764103
    0x240d02090f06030114011202190207030309080f0c1c080c0c0301050105042c030405030106090608010c0c08030a0203060604050d14060c030106270902040e0a060915050402031e010602 80
    0x441038602500c415400d0701000800c0c4001d01403440313540e0050200e944c00f948952228261909100001440c01250840808a03da80c004942006a000050501c01c0690108580000341303456001000c400e102e2a0101e0b03115021854080d0050264010580d005003080450181d07140d0010255075684420301c0455883e000240d200c140258200030000940d4142441a4a110a540170503a00008070405c508500032840c980f18550600c4240004a0b0590f000e11079080201480080012020b10340020b8500351080141c10f201441683d4107100c01003192282265881020004016602d03641e440005166015642000703400c01d00c03d243d441c01300000e2403290340f84442a07104454803035907a246c4c20142031000b4000c41001070b240102440414641850b910507252880648044140e206c00b85038040380c0042e84420a45403100c0203002d4030305500d20411015084404080c0300b4151035040d001c000c681c0c5403003418095540040001c00c9000880d02d8003001c81071504860142e9651030030029501c0e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 277766591 1250 277765341 277765357
    0x611250f080714040c020f120714010c0f0c0c0803040608092b23072301020702060406050c010b090903180405100909081b0d0815030c240d02 62
    0x48040d021441090024146040f5800b0710405441200450240009000401e007164294810a800000302000a00c840035101d0402008240c40345800e0402c40e10a1045014203045645840070004083c1da1006802d050503849041002c002806403808c009055001e500c5800b050101060202c0e4042e40041c0260086003500300300d0b02d0100c10352007528a080c0e87c03014642001d0381680b106502c014000d80d4070012914a0900c0d64003d0342c400d040f6190310794007841c001c844c400030f401098030700010b1446001c5000070f6110000c50810702c1c10350126146200b40e0042c40148180820702181d091425048807207a41d1015200549505100c00595a02d40250f420051f000b140988225450f05151203144c0c4074030540324001c6c6180349486c6c0500c1c000c000010b0146e590300801c0002c1c449120f400c0020503560910500184801014400f00a00b0084007030071501c6104082d10240901743c0d00004c69000d6440205c0d8241c0706108008510042d2050710000c1c90311484002c50046081400395014210003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 277767841 1250 277766591 277766609
    0x81f120b0603151f0803130e09031e07020a06090b03040201120b030d0c050615090103020405060420030f07080106051801030e0f011b2105041502040e0411010206090304061125 77
    0x2e55280d001a036287d018100c0c003044a05148603007000010804c0d03070f0164100704840140ca00d4560380b0000c0e41c2c0c041440d80114202c5400c0003c9201c00c5003040710044006101610340350140900301031a0b0100340c840980040d041159010020703692100c0741c2d1100c1c840d6800102141d42015002e00c000d0000a02c0e8441034419000d00400070380468000902d1079043c2c58001e1000605038216401c00000b00005001c59800941d074003003003022419215183d0241002c021941034880c600100c2d641007001c80280f2080c2000190001040783c950030900303a81201c3d4501c500e2620109420004900924900015510307900c10f100d400003070110190f0080b05094400702c06020b59000c0324000b42c4d0302341c098400001c190540340991018440e095804550410b1245500d0303440241038580c803006a800070380040c0c0c0d210354031800b0b00040000c040703069200b24000f800036100300d20b04121019103034002d030b1045000b40412500f0034480d050041c041c403140031000701c0c0409580c0300d5403020b00003a903100307000e0001e05c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 277769091 1250 277767841 277767901
    0x3042d0f020a0605030601091214030703080406060f0b0d09031106130b010e090a08030a02090402040306060501080901141303050412060506030d021b040b01050903060403081f120b060315 82
    0xd04c21412039200e04010386844045900e030001d08000c00028034810f41d0b146200d0f200e11003e2450500051000364080c4e5280005410141444011542c60303501118020401900c20000d120204003614000010001d001901144034241a01c210401ea039403881a805164100219014420031039410b0303c0c06156110030700da0302d80c000300440c500142c940039400d51101c00d046001421581c011a0710064040d005410507007503001103002e81e0455041114410780320ba070240100d507440303061030364808041d1009101503400020800056031016040116105048041b8010f243c028001c56000308442e0007201800d00071402d0010040000355003e070707c28080c40350900346541c4002101d0025031280c42500d440000d080c01040002e000b00d5900321705024062114032469036052000c40c0c440c5010f512841c0301d51a150411400f0300c290448803207280b000094080c4504001c0c0851041c0e520b030302094401e0a91203040010b807801d429041340d0042d0310000740c01c00c0080440703585403000a14000f841144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 277770341 1250 277769091 277769099
    0x8120c0d0c0806060d1e1109090c0a4a090601090b0a0302090a0312030507030506011b0609060914010e0601050402041d0402061b010902150f03042d0f020a 68
    0x50076250903120070380d100d1024040d10b201141c40c0e07030001d040012a0454400300104450020050741c182c2211f08510182c04103040c0303198200101001d80c440842c561a40c5800d01404001d080c061200303070014040c40c5100c0c041014601442d0100980818401c2e40380e51000303030b045400860300c0560315440c1c0a00c1c0c142c1c020880c29402040da00058401c151388450801949110450007174006582980d07001420440010104500f03d006905910042d0380200d50791034001c4d80541030310006018281005200d08594404001040030401007603400100456041c1e100c0c104203002d00038002c40942508002458400b401c20150300c40d0b04404d20410a8426687e6104200002c034010b40c411900ba40162241c1c00c00100c0c4c0c070100450b40b140c4010708031418607200e90800240540c55440d80503071603543c0c1401d80151300e4070720742540200c1210401103107030071000182880580001340c0000d0410200310302e22641301105c8100078100c2d80c100c1c01e000c980e460507410168207000c4018402d81c020001048086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 277771591 1250 277770341 277770347
    0x10c020705010206220212030a020105061e1323010303080f060603011203020a060e03180f0a2709060606030e07031e0c03061b0908030715020708120c0d0c 68
    0xd084801c1600a850302d59280c201c1c0d4080542c05103507140340c500c1046030300300040c1c1d210032204040c8130340240110386840481c1006401c60f04054882849001d2189401044221484002c2c1b0f48031816070341d40c0a00c1c4c041d07030040000341c101c41c2d81d1203181c800e10360b04207840b0704603072210641268040d83d104c882c291580d5141e80308c40281074a4240d04060301b040103000c08000c0c001550104c40c070a10407610f48803196112041104d144000e940c80b9038000052145d0303021840103d01542d0342d001c481c036001100500c4001811036020b8440e0040091100d40c4002c2e40d100945e0042886082a1a0600040780d9520340030000b0f10050003800c0c081ba11f00955910203403000103890064a80c401c2c0e241030201c0920840b950102c0d222074044960300c00620010001560318084d22518080b074113410301c080c60a110000d415040035406c560b90643c000d001660224941c0d001b5004640940c950041c1c0c0c4400034203100c40144140420304c5e602074515810700802c40c82200080585140b8414104007603d00c4410031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 277772841 1250 277771591 277771603
    0xa0902090d0b25120b09160f0c0f0309030201080a150303080c0f040905090601080a1a0627070305060307121506080d080a060b030c0d2d0b03010c02 65
    0x54105001071480380000762800706503600040c0c2c03906402500118800c107032075003070410040040024100c004030307070801580d07000300b04034450110750342d6180b468007208910500d5060b814034010405c0c0042d5411f103150160010381540340e040b01200d48400741509019240300300c180301c103d000a01910002c0c04010151140f51035044007080c4d50183c0c035240d40c80c1101c44030760203029841c40c0f103410003c1a4580003020004e0000748403402010500b0728211620905000c030582c4844660340146484e0350009210401c1004c240000c510201019100c0102141303a0306100c1c442e121240c0450104240b00f100c4c800b0381c140c482c86180d54180150795514052648a00042c850701402daa00300180301c0c0086d025085491162801c002d0015103d980e41c1807030741c54070800914503400301d07a000080c0006130100b030003100c02420700c5000c82031843c1070039110101c00380306021400e42d1441d906e0400d00607074420b1000449000e20450542515070318103881d003000034808100903511940c6000f441c403c40354004610 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 277774091 1250 277772841 277772857
    0x7080a0506010e040b040b0a030c081b01021c12050106050306040b03011109090408090409230312130c0b0d0e1902030a030804050c040207031d090108060a0c0512090109020a0902 78
    0x504011825120113202c00340c041d400405500c5502c078400d100c2c0c19125200d01170015801a881d00c02240d20307104c503060812191203c40454420020603500795030760002201000c46a050340258041d8541c114225000103500d800071910a0403d0000502240d000c0d015600404044400704480900385040500300d030141207008083c6c41c0107101c100b2861030320075003044c5c1c0305002c0d01600345403252a000103401c894080f1800c48500d05441c25848540f46044070150001c80b061006515010124201c0c10080e40300400300444541000384410400c138004c8019001407010b410042c0c0c8599040c0411781c041e01c210741d2845042d1048000d4848541540810190044e03000750181c00d41c0c629030b8408032040c1000a01c00c0d02c1074480c040e441e503465203881c1300030f1212a0213641d54030703074205e8090500040600402c10480c480c0b8407401c014001e1046c0030560b40d4028a0010001a0364041042c06a0b014050341806a000030a405c040002c0044103400280d90503208856000c1102e0311341c00c644080f4010f00c90 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 277775341 1250 277774091 277774097
    0x3060b011701090b131b0206070804110d05010f0c080601020d09030b06041812031d0f100218090408070209100608041101030e060a06080105090a02010e090406140103060507080a050601 81
    0x4101e6000c255004d07144a11001d02000c802620b802c8088058442c810081c00c20961055482941107606101c06600010070745026030b00b03810b094464481c07192881117040c2c45212601c40c03050811009510002800c00481006d0003d900c5085000c0d007018401c50b007190240c000c5084002401c1e10418024040e6030f0712501c0c000303454036040f00f80001032600400203003602d440e030380d1a04046848030070480301c020120b0f035003c56860076214a0151050304803681c1c01d8940c0c841103007240110000b280000c0d80c409a80001a25a03081c1c2508450307014075650403541204400007404188101c0320020262a0700a4510240700e450f20b15003c200a0000e105a42c00a1841e001050024069003901840b1402c14074000c00d0011041064500307207542a0340d142e00b0741740d4441007080461000c0c010035074481600d070082c11511800d5000a08049949814607110f070a0701c600040800100b90700254480400e4420710304c8940c0c50340fa20b04020b20003612000085a08440001e280d01c01c0c500840744030f034006035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 277776591 1250 277775341 277775387
    0x5211b0d120504120c080715051903060f0f1401020a1211070b031501022107060e011416031401060c030302071403180112060605040e04050a0501020f0403060b01 71
    0x80c8400c0d8840c8800002a800c1000410000821350383e003541464085010780c02008400d454110000d185c44003a42c051894601e00900c00d41c680b541100556054003a2444054088407207044100c00803c0c01d60803107001c6180d20b040c045040141000c40e58140e543d0f41d0440000b0202c801e00582c0e4070000d514004140c1440303003510482c200e124240c000544400103084070b60181d110011800710740c204465220b506d020035078085446680c10000d030614904108241403949180c038004494502ca941000f0780342a07103d00c14074402590940c080e102e5900d100110030901d0400020b2408003441e800348034030000f03060a44e52900c5045054155048800c1501c2d070303a00664840e501075020750800300040e140362940f1042d642d801103050000f02407001c82070102c0036403020581c0001d0030349840c40c02c0300d90120f446c10704103115040d04041260183c490340900c0014079a2030380f41641c41c1280d40400181994004102c000c0e41012810283c030580384030700b109000c000011801103514058020b0802c5c06000c5007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 277777841 1250 277776591 277776593
    0xf120903030a050c0a0203010c030b0f010305040803011505040509040303051009020f0d0e030c0106030c05031614150d020d1e09021003020c0f030f0304030f020f031206010905211b0d 80
    0x86004103403013111076054450940b10358001a01b1540d03039900c0301001c2a111000800d803480c00e801d00241000003400c00300300508081c2c8070b58420f8081405008911030181c80c400301740318041d0702079400500006114003030500e007520b001809000d003940c6030b000003401040003140d4540240280c811200c6000c41e0355040441c452003140180400aa446105010400000039a01d4080c05810003440c081c070304c0c1d81c2507140f82c013007418030f030425048040018440490040c4000220b01d54007a0710010201d580c040d1513840010020003a105100c4042c915920010364503851a10940200c103180a0070f620340c034161103c1c42c00240590f080850000c0d8411071640b0f00385501d074001e41c0503001d48500302c000c542200f0300f03a01415140d507010380540803c0d600c000c810003080560107104034011400074400340c58003442810b1050380d40d0080b92012410311480300f00041c02a4450b401c001c1c010030b8014aa294084140d5200801c0e100314a08002401d00030314170302000503514402c500c80c4503075000d80172181c41846 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 277779091 1250 277777841 277777847
    0x2040c050705030c150703020a02191a07030902041104050319330506030a0503030129040618150c06050a0204051801151b060506040b060c0f120903030a 67
    0x1001001005000c400d0000300d001c904104050a4103000ba88000c0c41c00c0c414210100c004010000c0c904400c00d03004020249245601040c0b001140140d450050704006141c5044509454110601c141010742c410401c0052903068004144090080e1303010054952001c1080109108034010b0075012ba010075401140e1103180c101a40e40341e409000d40c80802001418049042c4801081450141c030310b80890b0307030352800a441201d40000d4218028071005140e503a880741c0700d0005111751300c0000b8420f480900080d003d03006840e00790001702221503aa6403038420280c4a0908150b81c5050918801404560a010000c2c241b085a0807a242c03201c200001ccd507030340406480300900540c4455000d00c800909034607180c0c1109610007400c2e100c00d60540c1004001a030498003030449400308480704016241b000c03150381908200c0c1d0780201001c2419561200854094403504c0c40d455084140000c011258a40210721021405503141c00c1d2240d2a459103208100d40c000d0700411549900300308448415a40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 277780341 1250 277779091 277779101
    0x60305010e150d08030a140105040b0a03020603150a03140f0609120d020c0a0b0103141902010c03031506051c022107090b0d0b0a0501051201030201030c05070f08041e060c0204 77
    0x2c0000c0200400c0d60b02c6545510b4650400d43c1e03803416540c1c440340b4104040c0d0002c14110b0160400351010071020740040001044c860306440064000c82c40040494130284054210240c201e4000d070a062445940f0f1405410603019880041030314019440502d40c80724001c980b2a000702ca880000f01198120560f018896500403404440c22543c00c12041c83e40300340c14003c0341c4085004020f081751542c9541441902c0c00f5081b4003c02d1981c11000411103400f2074091040300980d02840c01c1381c2d501c020b034a070540060214250311904807150341400140300303500c80001e005d801c00700e41145503260301559240c1c007a40a01010181400308242c280d02e51002892407040d400119481c0c00c0e0304040c1c0d250803180c001e41c403518285c030440e03445405004440c100041c2150091031f0a190891410f4440104c0c140b850106020082c105515001980183c034440c200f0380b10801d811010311081030055103090740403a8400d22a0303c031880c5240240305592540f01905408843c545d0b2900e6084200079030800000705 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 277781591 1250 277780341 277780381
    0x8160207030605160f020a0b2d1305010b0109050919021603020a03091409060d050102190c050115050303120601020307060e0303101410050c030f0c0a0309060305010e 73
    0x100c10084000045025805018041c800c4078a544081c41d5031181c00405002c2c6094400c419917001c0303101140000c90346c85849038810141814803542d101000f240c82c0e034241040a40c1c00c1c1c0c9580503820b10500e0541714040340869440b4000070424036510b50019500a00203100340c03507002c0c1600b00062000805440e87d1902c0312007043c0014500b0116a1180030380541c90101a4016405540800c042540012010025000e0150308150302842d00740080d11407280181160300451450340c50301c041160075011343d83c544445609161010790144001420301d10300c44400d0301e0035170a00c03802d03510003540d95811000380c50740075000c2c40c0380004440c0c1d5403076030038801303412141141310821110010a81c07901c9810480c580c60806980c2da8144441d080c011a001504079402042030700f0700700b800c2551003140c14a00212541807031394455000c100d58500318042d07820302081c44000042c44a06100e400300d00d18088034480e4a070583c000b034840c40b040782200e40900900b0b42c189031403070105107000b01d540d080520175 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 277782841 1250 277781591 277781593
    0x6090512160308030405100203220c0801020f0c0105010f080a1209050d0303060806090d02030d0902060d0f0b0a1502060114210303070e0f0f0415030b01030f021c0201081602 76
    0x10010050241e00c402229034400da03a085808801c2c070041290512010800b4000400c0a50a5061410f1510046101d020400c022103013419409000c10144143c40e40003050720070021911083c1001d01c81060740e0100d95455a10b5103000c0020801d0040b01c00c02ca8150f48402d8018290039100f0707500c0c40004480d4900940038050000c200080c541d5490002c00d441038406d550118105251180380c070b1902c000648851500d07003020507007400710b80d40001510700c4d0b44030480d40070405440702e001250f89482000402c0c4407050602c001c1c0114030740303144c02440c041402900c4500c1d12540d2102040b1403d0f061203880310060b0001c1d001000800c0d9001d50701000d0800060449a108444c1e401100c901401c140852446400200030131550390303004010451f42010640d0380404008e034141c0021000d0b183d020219214650360034009501c011179401050146d40c0c441da610800d56140d0505c44203c0c0d82d010b02c101d22a100207603000c40600e01c4100303102c11035a4107071101c80150304e420048002d0080b140c04c0c10011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 277784091 1250 277782841 277782853
    0xe011e060807141210091505040312051902030a090308070c080f07030e04090c0501031104080a0b130f03020a060b060f0a0c03110a0308040212030a1e03020415031a0a06090512 77
    0x18080c4c0c10b10840c000500350150005101d0420324141010b1840030882c1010709207000c0400c0042500480803072132504a4200001d5a84d9038055110081003400103070b070703010714408401c0105041c2960704c01c0c003219000382c480a00e04d0385c86000403030b160000803d0051500c0f20a00007103045510420180140c144a030a20140c1044170f840400d040b82e1090000b5950010006020016560140300d42044400120512440d141c248003400d42d56104d0105c00a02c420166800601e800387c92514405146500a00100bc005100c0c140299100580c032010345540d442c107441070740c0901e001c008403103002c0342c07507030b502410100d030b610040c0c42e611003141003902072010781018030350140010f000d0404058800d03110164981401d0042c800c015400e007a82014680c0104211400380e500113844664001c494000120b0074920414214040d0040c0c1d401080c0441001b8034602c0080d405420507441d80c80614509000b0032010410490a42d50501c910008a108440140484d0405801143d04e804200c0e0441d95 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 277785341 1250 277784091 277784119
    0x406031e0c05010504060e011d0315070908010207020f060313081911030708030609100e0c04050f04090201080a0c05070206040611160303080c030405100e011e06080714 74
    0x10441003a603445580303a99030341440e008005a4450035800380c9420b02c1c280b82028240307500542014032441d4010b041c819402c1910021810051200c8000c00001d02079070102c600b02c0b280e42a004070123403211004548401c0010231000720503c241e5421540041c02d108000302600c082c0f16841d88003400748008400c96605002c0820b191030028805ca601001c418031000400c00302c010030800c0304920120715030b042008800049140c1c0c0041d243c2041c0112410300b01a182c000180b14100c0d44c0d0b41c400d10700d0528420811158002c200040c004075681034a201020b210148200001c8407000d800080c0880d4003503020608101041d0301120711001242001c62509042e0b40004881d40c106500c01c000113101103409840c60902404560000d050028002e8941421035401515030080180680300760400880002c2c1804004c100e045030015100000708140e204512065019040d201d6000300d402066401082c0d19440d24484c041c102c4d0740a10141c68002e00b0500d1005011560b0341a00e03510141802480c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 277786591 1250 277785341 277785353
    0x3609030d06030c050103060b0315040c202812050a12060b0307090e10060338011404031106090a050a090213140d060518241602030403030c02040603 65
    0x14091030180c0146680c16281c10f0004003601c05941000781823030014010300901816142c40005c4009040f10045058000580b08560340c03211a81e000000300844419941c00e03510200b502c940c0710a008036043d100050b41c0070960041041c00e80002c3c034001d0803501c00160148184060002d070442842c00c0704800060140c0306059a020b9000300c03001040000a218840b0780146155008203a000e0b103039105450036000003000c14056200b40003d1680f030700d082d10b13180d55491070807007a9030b103803c0610044041058052074803200e0404101d400b04d07001d00041c0d0b070200c004c001038070201c0ba40603142000611080341800382c960001d280041c4c02459801022a6598614030f0800c040c0100d45d00050302c80c0d200c2c88100401e0b20b4a40d100c0300a032014201802c070103445540f040b9141c150040404601500c40403000d0340c01c4900200491003500901c0111481000c0418009012a40341081144551107200340d803144e20003421951340150f4030802c001c0000034012101d004e480341c0000c000203500d60b5291116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 277787841 1250 277786591 277786601
    0xc08030706050109050f09120a0c06111306020c0a0915080f061005010c1e1a070e0301050610090314030f0a0305010914090c060c0703060612023609030d 67
    0x1c607045a00c400041c0503481131031058030341c030a030420300e0b03048203081c90108162108000b003204000c50700300040d15040d01e070084620440096000c0000c01c41442c0c0c0c0e412000554010040f18045110f01d06d40000b10a8400107050030945001000502841c0c40e144c4258003c1c05840e24148035401d150100143c40c1809015586d0345420b0324001d00b1561800070903820440960707800c9241071201d2407004002040c0c2441c1e1070031880300c0c0390744001301c0940c0c00d081407404c026038554007000741084101009003456006001003404c580c03d030020301164450500304035901301808000700006000c044104081007100310741d1100380112000707591030301c032070340041924a40c003003581d8101294803000100038803c1c051107014010310f0720100024090130040320f06034031102502980e511071600440d0004048800780424002140c2c880020400d0300d41da001180781da600c0d039000c164410510000807031180d08651503081c4c0e0030200c070a040c07884030b07240b80c041004100c2d015018002a00c03040c000f0111034481ca12403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 277789091 1250 277787841 277787843
    0xf121203070e0111071503050702250f051203070f020d060e0616031a0934030e030304080f07061404030c150b01020717010e03040e16030e03160c080307 67
    0x3414000307002e500d0025290302c20500510701c099010960410103c9402400126200050702d00032900d62a401000c91030075002d907c0c80c0455080c00b81e2440031030180d0b9622123040b500920b4254000c241d0b0b540030029078140c0311480100e650400c2000c0400600061481c4401ea0300c0145540700761038494440c0c001b20303010f40f0b24107a2964040c60034400101100300c6c2002d5400c0b5649018480c2c1c01500da03103d802004000c0145001c1c528142c04900c41d004c490076044542c10042010406c5800c0581262480080d00094440400e00d04921008a10781c040301b100d11941c1c10080c01494110300c9082124143c2c422842515000d54810140c00042d003e0407032640114000d0b519039061440d107003400009030fa2104490310b81070346014148010760340c0100b100d030201c0b8244c10800304d42118180c8214090b1078500000401c0303000c00070340400c803100d081400c07074010741071404548440d001265096040740c41e45d400002d03540e0304c24803140ca8003a0400d0303c0f184030903110300498040996150300240ca03503008000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 277790341 1250 277789091 277789097
    0xb060f030f07080115020c01080408040902072d0308041205120114040e07050f010c08070c0e0417030f010e04050c040f0209120705010c1b122f0f12120307 68
    0x42c420b15039403203003005000d0140503050441c0b408101a01954444001280a06001c40030001605002040007503400900750503030b06655078059890000315210f070b83c01101100c483e140a2a0940c5442401040e44465051b11a01080d840b651038581003991000050401c10408000c40d112400281980724000c00e140301d000305107012104104800d0700d501e0070070000c26a101541c1007000e542e81e50030661030058203080c07041c40c694050030014030511461030058084d00d6040c0e000034100115840c498840d500a680424103412031103003a005510041e10b038000030551070750050184004017240c0c50f030803034072920460b009600d824000c1400c1d40c1100c912000202c0c1d006c158540355040c00004420b203481c58a0182807081c1c24400040d010080032640500354600c07000180c0d41001044030490040d00d194034070341c034060300d031464000f030801304140b44400c5650000300c000c030b140080b404440400f06402495801c0003628001802001d528004080b0310500c03e52507038041c1311b484480254015103540e9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 277791591 1250 277790341 277790371
    0x6110721031719020a11010525050a09090c0c0b0f1005061201090903110a08270306040212030d1508060108060f070e0d0203060709061b0f060b060f03 66
    0x800c025100781000e401c5090281154020045480883c1c01101d0528940b81c0006844a07a808001c41d4050304018580d011507181034180810105014070005d170300c5815030004403600c03c049508076420301800700840c020030700b211004e1044200035005400c141c1050320703200301e1121494680c034800e44015650440a000c0b0704041c8401c0103981c15461028020030b03640c05103030400c500b0320700240400500c520300d0041d6035600c0303030b80405102d511200035009592089070001400c4d03082545090380800d8140700310380d51000c2c00d866482030248030070307100a000401401d500d80c7c40d40c0a105081c140e10070181201e0000b040000400c030140d02c68034821100052400740042e09048a032460700d0380c103070000321039980002c0c1080014040b5185183d803001d0140342c00c100050184002c1047e107001c10100940c980903140400c4081030380804400116060380c1e8464152042c0200c40e072001c01c440d00005007540700000310790030104030305800202100c03501809091920400c2c0d034500581d50001c2d56540c4a89401c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 277792841 1250 277791591 277791593
    0x50d0504211d15091e0316032409050303100501080a09050a02330301030c0605040e181207051516171f061d040c09030b0a060302060d02130e090706110721 68
    0xb041000f54481c0d40382c030a47d85481c1140c403a0901000500060041c9000d9181414007510301e030382001c685194007008983c5ca81c00c1c11084c0307080100c618014140083c45070f5002501c041c00d68096001c1041d0050040c03d1581259001e2000c01c2002070810b698810400c0030102c40c0030f2102002c1c4c0000352506200c0347e03c0e035040d031030888032101d21070344690201b00d018003040c4040e040700b003e11504020040c4101108042040d030b80c0d41404004183e02d41400000f0070183c042c8540880c070707000088481d00301040d8940e5821144461500c4600308040001c0041d02036418051501c0e9985821140c9291a0408121240c00f012503a600c0c1e81c002340c001803014260391142c2e0f25650002154910211020321140900c150020444030052001905071036444002c81c1403182594046000f854014120360303a103004e41680a0083d5000c40000d41c10501c1040d00000c44881c1000351a016001d0040501000c6141160455910b1f000b0300040c143c1d030150a9000070f802c4c2d209241c4503031038070807060709840007001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 277794091 1250 277792841 277792843
    0x70501080115020624060706020301050f040608100c020312090f0d0f0c020609190f05190e0604051b070f06060603020c0c010807050d0504211d15091e03 67
    0x10b0b03011a882642c0204038801d6950046080382d405410400c103481040145e44404031a04903100f05c01c1e4000500060725400e0084d690020340c10396105960b6000350592a400344403c648440c46150166000984080c4100c1d01c0d941145049800c20320449092610004400f60005410366079042c0ca544170b050003240e050020320100310555841c1c00c02030083d411300030024040038181d10000344203280014156030035a13962649540c1d141d00140c0351000d410380341c10350b403100c1100340e00400e4850701000c3d505444d419001c460303000545103817140c0e0b207580342c540c20700b40b00107810090040b580c040ca0440a02c8085c21001e0054408a402509070b14402800b40c108601203c90320f40003001018010000007045840010f103c2100f1202031074000e14030303039480c44100c50078003440350008117403800c0c941031006008400c01c00c2c002031896401d000c02c00e10650801965503000d02d001c025010120414010f001d0310300102c179008a01c8500440c00d290207135030b00c0001ea090760300c804c034107103502d038000194039150038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 277795341 1250 277794091 277794107
    0x10121a010e0a0602070509190e0703060f021608070f020d2103050708061002070b0f0c0f06101401050418020705010b090603101d03070302031206012c040e0609070501 73
    0x10081da4241042d50600700020f44802c202c0c000d080c09480004d01017214128225400110601600301c100140d2600c0c00341780e620ba090b1032000f60b0326241440c00700b112954041c801c0300c0015010542e10401140c0f6a03035400200c0d00402c0c01601d40004e401800d40151300e91844040390b65100385c149079410410b40e03100000c0442c1d068040b404251804040005150b08800700c030b038109004880320035012407491400ca14010250b08500ba031800301081e4421540d504101610f00ca15110341070b209519082100c6654402c0e00300c4200300d030114020030801c011103202980d036401101c10b00d0031614058442040c400100007240b55452010350000700102840002e00c40c0d920502402c80d22a40b4500380400065a90b141651210030826a0790303189a08614600e03141d942c2c0d41c044c0340e0070b0f1b035200c20b058100a503d83d001559100380e03260724440000c03a590311414075824804080d0311403002800000c102d4012203140780d4001c03500581c0c6e07808000c0e0080c0c010403a04c1e04c16140c401c018003407941000001480c2c00c0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 277796591 1250 277795341 277795367
    0x5070b0d0e0114040b04260a02070b0a080106120f0c0801030219080c13090b07030e190804120516030c1a090d0f170c03090109080f06010510121a01 65
    0x30b490103078045540b80f090f0699a8020b0f03013180d43d0f0314458071241084149100442c003620410f01081c1d210031840c022850140005803203e40030f481d806031b6540b014000314441c070007018001030340000041c0f02260059190412422030003100140d500c1c6190f00d41011200301c0c04a80c0c0209070748800420444c9003524031044540d010303a010f019414900640e490b40e90060b00762591041b41040204110302c2e820f540800085500810510064144018041d0080c0000680502070380101c54040d16824410361540e0281548244400c0c03510f803400c041a2540c40d501c04003152240901142803040a18146060010b50b02034481201c10500c0c002c558420900d2a40d0403c8414905100481c000e0341d50002004009400071006900301000345085a0100b20403840710450320380119004500d0107000001c4c01907500281c88034520315071100d04456542c4482201c19036154405e20040c451810002c082a046003054103291481841452404042d140707680da43c80401c1030340c4410000a5030380f04400401d20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 277797841 1250 277796591 277796593
    0xb0c03040f1704090b10081915090b01030501051c0807061b030b090106140f070204020c0d03020c0637020c030715060506030c0708250501090b090601081b0a0305070b0d0e 75
    0x20140740103401c061009002d140c8030800c003580c44002d50215000148585270b003451481d90b0948407540c110042c0010511103001914040c0086100e04203a140269181e0640440340c1100c0b525035a14440303030b485000d0813182242c8442d1040c0341008800500f108821441c0c8000c500c800401052010300a8140c0c481020050420b03101c2042e545004c0403100f12020140d40c943e61824503001140c0a1310941901c50040d119000c54044620350560141c00c0142000e01558966150308212000e140c0c0ca455800c0d080d600030420303041d100011072090080c900d4502d80003504002e0707481c681c03e00390380090006603840e4440c003840039035110882c410313100605000c590490031400c1c80300303c500709406400c000412450001a100d140c0e01c400340145c4040e602604052060103101d40340c0703503020b048000c00480f82c20400a000c1a4020340104490303060342d0041008000009003001d072085d0580c074000b4859003113111548080b003c644180b0106029141c111286651500d813440290b04540c181e000303614403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 277799091 1250 277797841 277797859
    0xc0206010513021608070813060302030402130e1501170c040204030302150c091302120604092f060309030415020f03120403030f0c02010e190b0c03040f1704090b 71
    0x100d944124101c80b8070a03409400680381c5003e54500b160303e20710f0082c040e1105802003082010419000c0042c001101480b800b0715405564100075402c0c1e00007550004d61100755404106583e030b06942c4030001258400701180c8058111510742c0d40d6040c001c0e080000c04200c62030814841c80c1c0304000c1c4084680c421b882c11882c01e40745480007901c440d1081d0550f50740740488008a00440010400c0e00c50740e43c401071910441c1a4801c0040000f94000100050340c0b07981440001c2c101e140510030b0002d07294100c2c0c5440007054506895082d0140700d0300d00c580c0041407003010503120342c6440018501c80c866140c029907666007400c8403c007803240c0d1096450b0466000705968482644080f00fa10f100020140818520341c86600e0160080c0805000040244d4a03160b00c103407086034150030000803020210150342c00b01031150740c0c18910044031480074229911400100d000c1300e091200071035010b4011034180c03000c4880c0b1350310309281120843d00307040c0d803202c0402c0034003e0310f0051145441101c001c540e0046 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 277800341 1250 277799091 277799099
    0x10020105161b030804230c040b030d120509070b030f01030b18100c030e0307030f0e1c080c1203070206041b23150a0819090201091418010b0d0c020601 66
    0x1d1550040180107007040011130105040042c01c900d0b00c1100403441c0705200703600c0d00001c0304554803074001b5a207500c00c0c2c0c148058900e1354100400e001d520020f03207507242d260000d008000b0402800c0080c00c0306050f80b24040000443c140188040c5004030109810000300f945036040c510b48500015001d070b407400c2003000c018403030030500043c1d102c0c650451a0010a8031004001c0580080161002e031588074000024100105580f0481422245600b5142d001c0810700c00c505000d00fa440c288941d16403920f229582a010500c1390340038100c0c00b00010700301e0788030098502e4008016042900c0c0c01001da441030041c03004103c8a800ca9081c01c548007040c0164992802080c4200100710070703118402c80403801e00920203a221150b22100c2c103000030002c90307540c2050460040103610101c41d8408021075400a41c1a190094040e19018640580d5244419401c0c81c007028942001002403d030b2120041e006c544144003011a01e600030440401215222060350540100b590140c28080c0215008240140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 277801591 1250 277800341 277800377
    0x3100e011203080402040b0d050f100b0109030807050c0607052b05040509070c0203120405040b030a0222061d010306050928150e03030414011a040b0607021002010516 73
    0x28807a07035014680b4544070f072950300128000b05070080089400c01c00c025205024004006108400f40e0803010455020500f4a0451400c07501900343c040e000a0600d00c040010035060000303840c001d4011400d591000410000246103503022010031103003074100070a00d40d070b8079113030100c8040c19084450708907034a205100f5000f01248198080c0301c4c0310b20600b00c04540c21500c0790420420300340c2d028080391610382c0301d10703440319180c0c2140c89071500c164140300c03024840303082c0403c03440b503860350281c243c08034416060344c1c8044c0c00b10b00314507106032542d8825000407400c3c4200c000c03144c07030b000a03a0160202e504601b00201540c400811a00550744044031040d040c0492070920119501a5250f10326420201c0c54141e084c40d01d8502c10301001404d01303000400341c40c004401980aa4802c200d0300f0841e07100021064240c07103940c0c41c4400d40502e01c0c4148207840c03c1c02d030807101412070002d0489203440c05681c0003c20321080381c102440181e5483d070030409165074140c0d0240804500e41841540c96580c84001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 277802841 1250 277801591 277801619
    0x201060e040b0a090506150f0a0506030c03060105070807030e1c05060c0d0e06040b0601020c030f061603090605041a090c03030403080903150c0c010507140a0309140a030503100e01 79
    0x2008160b8210018020803060b5001034811648003043e240c035420446100180482e0400442c1d100e0940020400d5483c83c1068400045800180840d801c55070380c0070f120703819500b0092503541480420460200094404401060028400d448000f049414241400b103902400a45803145844072038519002c5140090703480c4c0c0c05041c40014940e249003842415010b00481180244103105070f609020403c207000c44000d04c151030030390854980303004400806a403900ca02a241134680c1000010410241c401240d1180d046802c1c28085031085c0155141790460b5012542030701c221125220134804c5150311440660405440402008030510079800a0380b688150301c8014501c6000003048100c6442c18000356a42146402000e811850701c41001361040c1d02c2480035040b40e51804d0300040320300340500b0301480664204800c1c5400d00c0c00d4008142c0081107111300a030b460440038154041c41c0d2008000c4011403603c2680d80c180c803410003201a0702d41201c42d800c4041c0e0003c3d448014007218101e0408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 277804091 1250 277802841 277802843
    0x10b0a0311040e0111040909020f04020f160201021606080714041505031306060f090c051905030907090c030915050108030913020708031311040b21031c060e070201060e04 75
    0x80060001d0008000380d00410108541d4070b02e45d030303000c01d0014500e0310039800441024029288206000001020442248250044403a5040c8280407400c1070a120b4000d060910348180100e800c25055250000b0300c05150358018030000e05c0300d50411840d81e5002010181e07118a641c203050425003403061540d2520818440841000740c007200103001100481d10b94190584c00072800c01c02180c0790041400da41c4581d009180041d820b200300b400e90b080c0300b80b0490f11000c0304a101d070310300c01c20052030444d0241c1c406490b00d01944a48800803070144a94030414040050503180000c5a13185860000420304c0b200042c60059860100108501d4001204a8200e18021902c00103040310f034810400080c02095805001214040704014440128410502c2c2640c000e00b480d10b4400c0c844004c200943d0102d80038180c1299116409820721807108a5111040c7c510f203081e24101a00c405040c1240900d003a000c0c00c4098403001c042209003a00b049068010314184001e02c0b01c14180000c016a00c100a04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 277805341 1250 277804091 277804099
    0x11401060f0e011215150c030f08040b0a05150907030c0906170c0c0a05061314010506130c02070302091e010f0b0901050a0512040c150f08160e03060117010b0a0311 72
    0x5000c6402500c044100007030103100c2d010a8a80c0708543d00209047c10281046010840d203602d895130850156840070300c166441a1180740c20b5981c00c10134070103484058800310780013010540060a56030b45011103881000503aa002a900d4000e81c00104001c6031a8096401c0c06100d40038881c2d424412201158495013142c1030030b5540d000c6d08a40740c0341410303900300505680100d00510901d602c400301c001459500450340030300a100c618154600b02da400741ca107a03600504403250012101d1854114002c43d41c258015500a180e03a82c003c80c006074400c50301040360100440f050841c3c1c1d000000c03c40c0c00360031300c04a1041a01d003403100c0001c0c5445807030b017554144000440c1d550392440c030400868404e00848480c6400700c0c10681b41c140324810282c068041030b2410000071841041c07051825040202490341e4008483e1908089162010b042142038010015070841e03555031b41d2402c20245000745a01070b00c48a0300c2c89404006802c4800314000ea0f40300d0300c00c200c02000458207094031013030810002ca03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 277806591 1250 277805341 277805351
    0xb060f0d1707020604060201020405030105011a031501110d0201050402040f02070507031b1d0601091a0405090a0207050102040b12060102011a012708010b0f0907140c010608011401060f0e0112 84
    0x942411128082c00c58001c0d405100003c2c0881d8050b410f402401c00c0303640a80c001e1240c0c0c0d813100d20441500840820901c400c4005000040c44004120008008a1010305008000e1034409440c20f041c01001740c03074400941e444405000440c1031074441c4c00880d070543c1e8800c6040c200d8a079140390703d808151202429005840e5a4401084481039105005190608042d400074510302c101960200c0211034850204844000000b6240c0d824420040300b04c00c0106510310781402c1008000f00300102410000040d6802d010140004500f44010005001c540c8074060702d17010703202031007001003900900803030440e4105441c0c0f48228510558824a0042c02d091403010294000e09900c1030300450841d654949400100c0062901010b40c81040040016284040740e803025500f0b1110b0f056081c1c90400001ea519010b01701c1e0200e8010260014400c01400800c80c207a40c1c1d080e05007512545800b82c05061211001040741035003080110010321400c1c100721803070408410001e40141c540a105000040d218 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 277807841 1250 277806591 277806623
    0xc1927081501030f1412070336120314040806061f170601021908030901110c0a0615150e0a090b3f16061b0305070305090612040b060f0d 60
    0x5000c4509881640b406e071a0b2070300d505040050240310f0400c08040000f03403094a00402d4480c0601d11116504030481070000310f8546480e002e0310700481e100170b40401c00e6a0b2881d09680407440003c100400040c8000e0000e400c140040002c1d4a40e01350303402c10b4184045001e44002a00011580910100c402d2040782ca81d403240010f0b42070400e103000841050010754155001c101c200340c017841c040e1000300020041c003040c0040d0365106118004400790a41d10000e603000015130240c100c6103003441100304901d9a0741c4c1d43c600c0c0145200306905010041703565a80c0742c14490401550510040401040c10302a0041c00b030701041403000c0c1d644864052010301d02d5510004001d40e005003910b85548142da0100501c101003054403200ca8041d9a11040300c40f2400180c450b20500c011032118404440e980d500d050136540a40e60b951010724218207001c01070000d01d1039aa1988003030104400703c07864105051030649442d08207120300a08081c0f1450101c0c82c9410280c80d0b0f003804100c031586c45030403101c0c54030403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 277809091 1250 277807841 277807843
    0x903031d0706180501080f0703060b0a020609010b04050402130902220e0d0908030a0c050705061b0c060a0e0f030c0301020a1d01080c1927081501030f14 67
    0x40101a2120312548802040011400081a2044941a0b030360f0500310010907801da091040d00c2d214481c005800c802c045400c6460402041c0d07000001e80c20700103000d90390b521000076107410080c449000340e00180300b0070403101c400b8000e40401c3e500c111020000ba103841e600103010b031421944052a000c2d5a24900303011510b41050080104030b0400424140541d401200f2018100000c4100e0340341c060348010104280c01031100c2410b903140314019506040b0b03290790807148800c0403001038071035200e00d01c400107031511560010484001c412514448400004064515003228640c3c1e26008a80800629140713581c0051600340004048031070458031071031000000d20f408205070502d681544000340360103440e1b4000480d01101d60b049032040d0200c41c0e040c001940c4a40d401c842c0c1906002c0304206100610646903c00380b00500c2e0b50410740202c4001c017400300840c4070904200540c1c01c18141080c05a0380f002c00c04016030380b42d240d180008640c1556950100b0403c80900100019146100ca040c0c1c40b074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 277810341 1250 277809091 277809101
    0x10605190e09090a170703081603060504060e060117060f01050a020a021c020a06170c0d0e0a150b0a03081605070306020c0a0c0b03060f0909031204060c1404030309030303090303 78
    0x540100300c107401d810300d0a05192244400d02e421034400401952201e010101d84090b43c0a80d60141c8039003008d5591074003506c010715214030090003016950400407480c2d0b611445400058402045c480e01e10f850080b0014020500c000140005040000304004150b031b21102c600d03103403030b2003032070980d40b40e1140e0102a46400d082540007940300300303207002c040e0060240d010a075a0042c001c459076405a40e59500a942109507a076050b07401000d05400201185c3c0e01d480140300180458200003010071900825070305080b011441201c4143c1c9a215014203802a8010118030020031104084068a10740d02c0f25078038400c82501e245003203200350f1582e0038007200303005141c011908000c0565450108075400358880c0c10b4140b00311140501510082100c406102c1a20b1086801414012101d001c0200300011030070020190070051100b000714002285280c2d58180c01144a41030229001d280c140028000304540c441030042c900051004001080d401200041242d8042c02d0000354169242012000742c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 277811591 1250 277810341 277810367
    0x14010608010e06061908120711030129190504051b0a0507051513060e0723090f040f03031109040603030c03020c0f100302090d141e010501060519 64
    0x546894014030b100080403075024480d4030200c9600c0c540355411440600005654011301d162584000380110400700e0b6080101440d0b801900f5010b11445d0200000b07003503400101c01c00b200025010b8108142c00c05503d5444a00309044075a4031950b52207003d180148030b0517200d903900c40c40d00c03a804650300584042001c042c21a007861001c1e0b07106070300c1c00082c0c20340c0d02c1100300321440d1040001c01c00070180880d403c0d90040c1a4010300a0010400c2d0b16a031000d4039207004251820701981400140c1c140358080803007110411244c1d100740702080941002744204001380307600c070078031105420000007070020051145090b62504002403121603500007440030f401103010036070f042443d100300030090541204d450000c1c18400c0c1e085402c3e509520080c03000202c03180303100540189600c0d4045200e680250041c1030320b44005481ca055650040d01c807100c1c0e409181030400e60981241c030480b88001c80c0e213a02c1501c4601800001e00c503951404c800284244101c1c40c03115040381c0700307041c440203192040310502d02c95 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 277812841 1250 277811591 277811593
    0x40b0f160c080d1116150201060503190501141e071b0606031e050c0105090402070c1d090d0203192d110a020307060f0c0c0909030e09100314010608 65
    0x541d48407507030310303030744200030f280040110310322616020701510001000791280f000d450305213103241e141c0042401d6000550000394299506c9000206868404208175891501070390240460546541071041c02c451115400c2c01441c140c01082242d00b8904403000300543c01e403d8009010b41d0740b01b5400300d03a0071110000100c0c40141c0c400c1141c003400025040031094030b000d030410181c01d6074580f1a40400c030045410041c003a4000010140d81c03580244090030900d0b1024001603c0c00055980c2c030709498013030790801030701c0504400310081c41c000320548040c1e021050354006d00c00004481800b0707549000c1c0d2920071920042400090400c184104651070011569010350f005d041c58150341441c42582d004810070024240405c0e80f002104000382c035484c182d401a000d4280c85c6e09042c022a4282509260318091007a03c03501c00f0001134200101034020030559200247e1407a00d8940100b1804948008a01c01c41c190828403410160b100040401c507607002e1031009030151018885405816994811922 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 277814091 1250 277812841 277812863
    0x40e0a0203150c0f030702010902010f020f070306021b01050103050a17040e130c081b01110c0a030b090f0a030206041704030203031602151303050c01020706051c09120c17040b0f16 79
    0x160b01508811827044c402d8031421901c0e000b084c01280c0d82e500c0d5009288565000310410000716880764001e040c0030406105194481d01c4500c0c049003581c41c02c1c1d0040341c10b039020046003418064083c7c065088845a100f400e0b25007880c1281400100c000074001034046240003065408010740300080b03c0040c1641c4081c0c83c2c1e03000c280d10002e58401407080400f03000c03070800d06665003004008a500c0c03440c14402800c1e01c803143c0c111b4845120f0400000c0c50f8020f07070302c14000c00d840b847c00d04000340b01d44940710f41e008050524040c038001202560704d80081c60007083c18481440165400f20607620840100381c4480d0061080d030000075025a40207840da00058000541c030351071882e81100c0041544c0c010412143c1481d00c0c807004980c0ea042504c01c0400044081c4142030518940003040b050001004401298603245910340007096079640d84c800020510b004600c1c000c201e44d0629100d07028005076280c2c0c1c1040c0c54140040040d01c81c00e100c58040b80e400051203190441c8440b5201c1825400c5007458030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 277815341 1250 277814091 277814101
    0x19060809101b0e2b0605180a112e0906050301140904021306090b0901050d121d03121c09120c020a0305100608100b01090b09041407020c040e0a0203150c0f03 69
    0x204c0119002c41611440c0c20100000d00000702401400031403225900104914403841d11100c0e480410b08044540c01044010031840c0320030030307504003e2003803243c6071580f07041c02c54518050315072500c6500000500c072040c00104107003004030040e203079030400c1919074400702e07a140d200040143d000d1303942882c9141e00c5c110010840c98096800725843c003c0944501d03d40d47d0f01d4004000320103100e10320040c410310320001c0012a22f48035060032803090340c2040220031042ca84c4400a0301303004101d08040b0341c03d00e010505a503c001102c00d541c62100404504005144858549150b20204012182e007400030381d2540c8011512004405002150080d041d559040c0d0702c20200d4015049a20849a41c1d00c00c918a8030003100892250001d18141611165001460460a070100b0340103040b040c0c0d8000c0e40e910354000203500324641503100303500c0d55020b400712030b4040c400c1004403284042c020882d58400344914005032800038117403440031040b00c01e80d44150344410b5283c18074803580c0c0c8058403000c00441800b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 277816591 1250 277815341 277815409
    0x3051209030c0f0109020d060e1e01090605180a080a0c0501140a11041401200102120f0705120a020304081e0414100203070f0219060809101b0e 63
    0x8070008800d081d2448880681da6241c261480101c010394030901e40124007002818949c8146070000e001401d4a10b0b0315200c0c0003a03400036a9400c91300880d41d440708010010040c0d0b9205049e4414018586c801103180d0403020316664100b5030030014040e82c4002500d0504a00a4281c40c3c8041c0c0d01c000280151000140f8000045509440c6040f400e41420850400c0301410350954056a0700100c0306001907580d08011100e190343c0e503c803903a407030710062000080310781c007800100b942c03031081829104582070041c0e150031748400003001d90041000a12100d804900a000e28903040284480056100d88881c02c4c070034014441c410180a000041c6910706510701d038004080d0003107034400724500d80045c0d202010311800100f0400c200340141c1080201c89c0016442640c81c00203c1c1c00504099001682207154004598041e000701001c24140410481420703401c0007801010b0314128400d00803441d0000102c804609200104000e200d45ca80e04949550de550808a28942e184011056040000702d100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 277817841 1250 277816591 277816597
    0x4060b070510060f06020d03020a1701083004030f1b06170601050a09180603050615030f0d0c120c0c140f040e03090d060b06040801020309101104120305120903 70
    0x2028510700f4424005443ca0106001c0011107907150090310707503004401000ca000f1350080480b03405204158010910101104001710f0280240500428220100034a075024101d5120240c3e140d0504424030a041c0101050690342107076488850002c07050b060b4601912500c103039007a50b00524240600019040d42c0c04828100069401c40402d40030752161f5004403401cbc8108140c1a000c5005010104a003100c441030305000400e41c640001000d9403696503003400cbc0542a500e404a080e407080040101e40340c2401100d8107000300da0001d0418140300e4501920722001228040c0001014406030a40e940c06050001e070314aa1018441c0d51181e100c1d69544511850101400d00400c1510420002e0b07080038410400350300c034054000c42c286181e00040100140342c1c02421210039803078440380d81944c0c4540d00508090401c000001d61a0300d40500030b18030703090002803092619414060102280c41c1e40c04100c0f81900c201c031680101612490509a841e80b040560524042c0d51070030420104240210203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 277819091 1250 277817841 277817863
    0x30b040c091719030c2604030b0c0c01140601030c030501120f15020d0c080711071a120a050103030e06120408131502060601110f07050409020f22050a0207050604060b04060b0705 78
    0x2506034400c1c86c082d005442a4076003900584040e4100000d0002c03d1902010552000441141d10f02c2d0040181c100c83c2554841c0400c0344081c80902c09201c029070b0540140c070200045443c1c2040258035001d198a43e0001401c4003410219076801200b05020030071040c1aa034212a00f829540d80b00c00303c11a40003440140364990004145802003000c41c0d00c0340d04078048241e0070304000c1c100f090a00500301c880415100c1c0032070044d03804011084603a03100145051040d001040c4c00150782d855410050940c40982800030700c106001c10803a8082244101c5640c1c10a4100c1842d075140d18040404081025050304103c01c00f02d800b01012442c59400101c852281100380e891003024510032070460360b140850300c22003111f40c106801c24006402c03e07034803800e00b441c0001e101403000c0f081c190114500740c240c84e49a803100c000039500581200454051700760040d08240d02145414280d4607a40d40303650740600020601c030303150b414265043d5500d80002001e00b01900a40d540c038400c900d0202c0d5130703c40340300c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 277820341 1250 277819091 277819103
    0x31a0103021503040503091513030c08070902040815070e040203010e071205091f020706020313030207050619030b0f0301050720150c1e0307030c030b040c091719030c 73
    0x140b030421041c000c2050328003c6500000550a001499082107240c00603d01c0c0103500b8041480040400c280760340324000190b026000c44205142400c124509111003900325507100b900401c802c120751072001440d031904460303a088020343c4d40c440c1001129818070780b1540552042c00400045020541e014410f40540841d03103411405826080d40f0a0545404450300d1000b50491142d070724003240c0140306510000c50940006282c01400d589603c22078006503140d9214460095507181015010800000034050032110181447c0e9040550003103e05411804d00416459900465440c1c44d0700d580c0b51040200180240218945410005d211000c5005210865007007100c0c0d03403044120124039600c860b12144010407250752184040f80059120310200a0f03086c8500c2c07840d15405c101080614021001a07401259008c9000705c02030a5603c02c800340381c0300344c1c60070141d00000746d00030004a0407100240c04c042d20b94201e1900c2d8504102c8a0700311010b02001041c000703400c15a1101c2300f00e500901c520 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 277821591 1250 277820341 277820359
    0x307061125110103091106030103230f030306041d0105070e130603020306010522050c09040501090216060c0201020403050601030c0e0705070f0201052a060403020c0111030f03040c031a010302 84
    0x14481040200d8103000500050b116118114980d4841d130800407005001d80c800c001941c41c0c0e240441c0c0c1540c0260300994210000c400801010462240208040c104c804003e001c103108044900340c482c440a000300b0304c9150b90342e00f50f8a5100d00070140074503a6440400070010761070716080c0038004280f070b60241880b0342c030114170000350b008542c46500140c03600503000308a181e00780300038066510104036008065030b00d0480762100840c07042c0603280c400c80142462a842d0004082031105a0304180c0140010500500030f200300e100180388240c41c00c6402400109401d900d40c40264024481c81e0006030460190380e001200340804441d19400300e454030010300785c0a035200c1004640b54080c108006103c031040040c12009584036001030003c88280b500901000209030f07140c1d80b2a400980381c8141e158102c14100014141c06200e1640c13845403c0c201680d490b0b01c9080c1d00798807880754002d2200c10300d50101c0403c0501c4949c110100145512403c03600390011480030840c6203603400d10041348503000103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 277822841 1250 277821591 277821637
    0xa050c0109051c080304030504081009120f1d0111100203060a09050c04030818040911010809060610031a0904030c051204050d12210e010615140c03070611 68
    0x3c41d10700b61480e0f40c1c0309240d08042c2d181c1c0d0b94a40681c4041c10560030458140700c0404c8500e018000144104c0229000042010184c50050b110401010010f0140f11402c2700c2c0030900368129082c030110044031412070300381001810050b2204484000b00241c2c51140c4100c08514140d50380c025030150504803204820b6a0751010b41100340c6204035030a80340110103010030000110f01c0c00c0644030705100c0059400341c00d5005008102100ca114000783c03424041c0140312203095230003c00464001c081ca03805010700b4070301340f03020480c5040014403000c20565a401d2a8500820092003865400b400814641c00340c1401d04000f0450b207540c1700c061361030340180005a209003e0641c112402c40d400a0001054045540c542c00c501895446040c01401602410612080070080c07a400c0c10384080d51001417030000b080c040c503003103e0183d0814035420901ea844407a00c2d42d0070540441d0145005070445503101d14100095007503024815009180e1400e144049172421a201c02400040c41100000c458680b41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 277824091 1250 277822841 277822849
    0x110301080f300a030e0105070806010e0d030206010612020403050a0309060f050313230109061b08060f060c0703080d02040905070309031d01022506022a210a050c010905 74
    0x4200b0500e404200b400b522200000b114801422902c8035604002641c1c00401c40d08a0a6500032100040001c0354042008419a002821441607240680d000c84410803ea5006540c8003c11b00403a814000082038168a031140b9030101c4019544c2b0009440c8003204a15014107000300ca07004010111314101611080248140e055a1040d1186484002d282c1d816440e085030440e00900c0e0350400040701303140b803004281c3c24018848100d20408001604518000c07030220740514002a48042041e10800e0211656490300c00701481e0108644155882c20f20f840b07444d241183c40c5e0b100600607071001c0707920b4480c00040c0c0c1c05081200c02080050040340c0d900c1700110103c4080c1000100451403d40c800703401e40d09588201c040d2180b042c012180400c0d2a40e00406050015030500c0008596184060041990500c0320303162000a0483c000580c80c5464904624807885103c00c6020b051982054250400c00c0f014100c800c1c044d0009681c0a2003ea00f40180c46108084a00340402c514517400289420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 277825341 1250 277824091 277824133
    0x30210080906060603040c17071a04060539060f0a0605031c05040b042304060e010b07020d080d020304060b240c030702040204150206011d1504110301080f 68
    0x92903030090300440c1c0e900810009117810140054503c00354a460100300954154914543c0c0030030703000102416440c11808a032600d0b403c01c84020307000c0060004102c0303940c01c40103507401c001e5200b844a194070800c1e0244020004020b81050000801074010001d07800c01081c0070f0700030041105100702e41d83d11401a10b00741d5004e8841c0c55010707405102046400d11803c02807020040040c9401d510306542c90203c0e6035150440d4210320f4004002011a01c40c0345044401d03410100340c2030700e091101602c0c0100e000c46a220520802141c540b0010b0031404560302c88803983e607901d030300c200103907120488501d88000a410455046030490320b0201e000e00c042c90140c861400300c61240c40c101c02384107907601d030580e681d400503005000180b00a00000c0d0040e50380c0e002400280056010880c08014400d000078a810741c103038000521b0406481d52408000090005107a010201845004010200b40086401812440d2405004030004000410121401715842b042c0311030400032504889412180709403104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 277826591 1250 277825341 277825351
    0xb03040b0103030c0510150509010806070906050a020312010e0405010f05040b2212030203092505060304020f090f180c030c0d0305070f1109010b0a080f0c04030510050103021008 78
    0x100c0398004100207480380780d56032481403060043d0740750280c4031207203001075a060500d90210204202001d1140e4244411881d00514419004054608104c1c101510400b600c4c058901004400a0908802c2c1d00030003c44030308030b84c55410009d142d07039654030310a42d20000765412142035007060f60813000c90303a00f80166401190007008a07202c82e210b86242051000740d14003a411300046030341d00c40c004660310382c0b0b10249d40c0c13070180c9002d40d0700c0c0707000e120190030202c042c0e002c0c0d1580c040303207124500010240840f100690704c040e00c4465984c0ca56000080085e45000c00030703a48003009804200000009100303050107043d85200e030030b0b032902c151402191500810074405030541e010803480d44251800c0c401405400f0f00a0a06038600034042d20f800751021240201640d40980c0b0b600c43c041541006001c003401000380c0c00c4e40e2404d00d4400f0b20010513041000e000c190020b602c0902040d103010000c0700702d400540e0b010040303500800405495101030b02c0c0911003617200d1030075644d880f4030580c02509014811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 277827841 1250 277826591 277826603
    0xe060c031810021614240c07050a03030e060f090613030204060803120f13290609040b07120608031606140603100e010f062301090807050103110702030d080703060b0304 74
    0x1103405e1131281c0048440003040c0d181d001d40c00a82c011043c000d41480c03100740499402d030b0300751b503001006855454816581e0245010303425842041001c83d40c401c0488220680881c0c0465441e02140440c00543c0184502d2551181002a22600034044420018102c038401d4030140b10003aa6500141d499006070149001c0103001440000d03040307403e00610355030003440300f0780801c000c2d03880792113024460400a050400d00c0034800345600c80d0710041c88007ea4408000c9480c60500d14281d51089050319001e01200244500303c412140e403032241c1e80001014004c0f03641125118452010701031060303c40a0710642c2c00350700d4a402e03411000203a0720258441d01025000303041c1c0d401c1c590f1440c00180307807400000b501956030704180c020f148003602030b280007020810745020001c08cd89184003880b0903064540c605100312140d080020301004142c140840d0340908002501d0100070b528140688107048001794035004003801443c540d5040310102d406440155020004641c0702d100d8071035948420b84018001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 277829091 1250 277827841 277827883
    0x112021201050c09010e0d0c0b040f050405070f0302070c0305100603151b08041505010b0301050f01030b01020c100c0606060302030108060112030503060607021305251d010e060c03181002 82
    0x4d55401400710085140c405402801082c0054890210400aa4011503109500000c0c01c022510341c40c0000710103004100c8081010b030404500250207441d010700280103060300802c201060012505800005503000401d81d070055181c0b0560000415035800111620034000401901c0481c4502ca03902c0b1891000f001007218030781c458000d6983c3c2400410845a6814118241040c01e0040c01034900074001c1001c0241c40e0f50402c01001000d4060942550400d4980031030224141e07800681ca400da110207a8030300c035084007084000c03101c5000700d000203403c440c102080003603041e40c135500940c12160100d056882598032003080510490300a0b001800040702803002c1401c920f0468010140c1c03520041400c00e203055030404810545004403480d056000c920294a8050300502c0c005000d402c605141001594a07521a050680030415180e10304002c1420b003051402e03202c000c00c0344d84480c2500b04aa88a640d110074128003032484400e402d00030003404080c0c2242900010b14409007152403011a05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 277830341 1250 277829091 277829107
    0xf0b03070c140a0507090b03210f090301091a0106090602060a022a06040b010b07020a0e0901020715051b0712030b061306020615030d080f0613050112021201050c 71
    0x50065500006031580c1030b541d00440301c030000800098108522600141511a20344000c2c0401c4a5482952038003941222060102c0c510210002890b860700c040421510b444800c0d1040c8070034012021a00e402d03600c0c000300f800c28405800b80000316100c06000782c058070382e224282124521724070720551003d6400b41012074503c5000d0b07005440081082c0c1740c0700500800710200c0b001c100344514200d85441d0080002e00c81803000c01503981d409802010700e4030b4504902c0340d012070124405441440f8155042e0740114210800c00e40444205a4028a40c005002c0c014108240103140c282e458600008a00031111190b0b4030710380039100216001220000d0090090700250060040d200400341c1c420410001b0f01042e60800c4800d60241200303500a04c0039241404e80d003098541c10f220032911940c032103203100d0051f41e4000505d9a01000407014407181d5260000070620800e06095081141c5007000300124009104039011803a845c001c072000d900100c59a42d2071400c030780d000d070b5101c0d140c5041080303101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 277831591 1250 277830341 277830347
    0x120501051c06020c120d0507090801181b030803040b15093d08030418060305030f0f0706090b09010506011e0f0c050601090603030f0203160f050a05011e060f0b0307 72
    0xc2101c04200c142c0d00c114540c95a41500759011084546c0000c2c0d59109101215501c4a07482c0c015083c1d81c8020012420400d10f8000790038681d58000300075104c29150344031104038a4907400000c55002c01c01e40d0302c034141803810729000300040b0340509104031361350803410319454140713401400b0300c1c0c4c0c0c03040230103107160042c114040a2008000b1084820030403204004103076620062400141420743c007a40c0c59074141502000c07181c2501d1000b008150400005002141003c81210701c480d0726508215565007880079000d078103003e007810240466281c012070406100c40c5844181c400c00040c4020031090f0303036039801503c2d420302602c0300302c51941420075840041801007030080c11080c1142072882000380580d550b02c2c5041826042480d440e500c480c1c08104150300000c9000c80580c00b40055030514511418180300070841c6003000d020188102403103004d0150a101500513682c00034028000e0700450a8142c00802c48d00040a1311245003200000380132041d8040700003070320780074080640b840d01c40400407 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 277832841 1250 277831591 277831597
    0x3e0309010917011e0605031b1008070c080d0501050405070c0b0c0921070501080f0405030313080f0d050103020a0504060303211803020607020d0e06070201030c0207090606120501051c0602 82
    0x844520365a80041d400840712202404104d00c0c8400c0000c0b80e03890400e402d1600308615017844075004d17503c28240144c15500c1020b0441a0010781c40e000c0850769407601c00b02e038021a4100060441c41c000200600c00070101d402580c141c9005503028030454855103406c039040f000030716010780100410404110440000c4000f020820350003800340c860010003a1080b115444158141d00e12688110000c010740c0d6000301007181c1c8100050013000c0d0300d1400d515a03d0b1240710080030b000c00301c01042003143c2001038481c2a1021f00c2c41e040703031103615500b040e5100e0004105c01e0000342c1c405c04041c0800100b900e014050305095952551300c54040d24000c200c1c0c0300c0207800a01b230101d13500d611414140f8642041002c3c0354800d9001e40e00510300d07420503580180c1003901c1c20302181c04010410390f07540295144d40046805840d0b0a00c1c000130031034120340d000c07070030320398590488040b00742810700010304603521640294440029880400031a681c80082000341c000d4900c04130f102c05000300b03440010420356809 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 277834091 1250 277832841 277832879
    0x60403050114060924040b060c0106030614070504030b0702030f031e06030127020d02030a050a03110105100b09040e061503101503020d0f0206030403050a0e0307060207090c3e03090109 81
    0x1203005040d10000400f09c1d0001320014040369500c0c4410014130010b402641c0520031628403552050030020070050080c4514000981030823410000310303407403d10801c03c071114184001c8206840e8185500402c1c8480100188100c0308015140421a41e10301031082508403d0b80d4407070614032020000f2820070452181e00240da21801c075000b42409610140041c001651081d406414001c03a1031401070000c40100f07100706560f070300d084c0410454281c00701d0b0702d00594140f0701d009912400500f000402070584045d110030305002d02418070800402542402500d160224150703070110307a204107048112010041ca0750f002c0b0002007801c002506103d03c0450100d1300940e15503031ba101e0540c01181c0a40e00580b8102c0008400141c0c069925600c50316011809008402411102d860124000c2da15210340c01101c48a540e01d0021314100f81c0039408405d048203204e0b06c1462040d048170a034500210084c148071601111a100c3d03400e0b40a4080102c1d04004416100c0c14403141c01c0c96079450202002c805 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 277835341 1250 277834091 277834099
    0x31504060504230109020c030a0311070f0309060f1d0d0f0c080d03050f04020310020d0605041107050106080304210804120b0a110403080d1a060403050114060924 71
    0x5010465071214041c0c500006440c0c260307248020144280e80700c141505170300168005106101050031400040201c0e503410344149800304d024201498a017003070b4490114018072241c210003c80041580103240301080b24041d484000c0002c08190080d2409240400c1701202d09260060b10b030f41b18507002005c1c2e802103001c1d16804084011980e40e106000304550004c140907801014420040d40e031600866901252000d021186424182e010039039500e40440b1081c030980c0c02003140c22002c1da85502620082c40c00034014000e41c0748c0d68070400c0759540709000030b440342d5007800000314201c000041107a0448000c2c404200624445041200c80603040342412509101e08000000741c1c8150140f507918241d018040114607030603c59031701801c8805d50580c3c1d0884240070300081000c07510b044d01f90b524010034450080307601e4181000c940c5d458189010507540c410701c08038001c814818150b10682d9141d20000581642d51620803c00c1518401201c420350030303000351b801555092949190301400c049000d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 277836591 1250 277835341 277835351
    0x3020c07262a010c02091302040b130504020906031603110301111c0b0109060c0209060f030d2114040f23010207051216260d0204140114031504 63
    0x10320864201100b01c00000041c628030794000c00d29492581e01120140001d0800ea00d03920b0290b404a102c040006014400d200c8000b91420195103e0f50014464104c0041c540301540b00340e40c1c00280284400c0c1c900b83c0c0110120301c0041d0441c1400159a10004442d0031022210380c038640e1040f2452000842c600e4255485500e2200c5450703508014048590032119100b00701d4040071900e070100e80305043c1d40386c108400f0001c104041a0008007800c113154054441965070ba669002240d590307030100e18540d4251207102c0f06034890700e51046070311300740c4090250740310702400070b0a042d031060b550107480e503030320304440b0b080468000303001c5142281040d4880c40a00c41c03c1440782c0e120300804010400b00d00156500000d04030100001841200c0f405403201c2e4500c2c0c00c04e840d01e0400190b520340300c20300070003410300e14026403d00c1583c984034105040c4480011170751402c0805074480a9002403040c065801900c0d001c60032a98054140002996494000181140c1d80c04031401c2c4904501c10095800940d21 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 277837841 1250 277836591 277836659
    0x201020909040b0402102c2412010909031b140618070605190c05070803070c1701020306031b01030908041d010806041203020a030b1c110103020c07 65
    0x900c04a82c800c901514008885140074014081030f4a80f0612003400c01002c1d15240f0901c1c1c0815003007412510030107103a4045407001c400400c1c5820001d11403d45044038031445d802600d182c0d4001400184030038180440e640e6680d403000c0054a001c50340040c046408514107114044e0106400c00015003e50480c640c00070100d07240f01d0038000c060b9500b03040901c1250380e5103040901080310350002c0c03805140c0149003200b032101d091034801042c200501006081d609807002d0100030000140074050b03003000c1e2691500c1c0b078545120700c8199441032410341c460100c89940d4040e418400d4034408c40d03000d000303420f40c803840d903602c0c1c2480001440b426040c19034900d0040c021840c10005080a84201c81e480d901a980c2501100d0325414164001a40307030780464100800914228134146c90f1441b2810701603180c4010b8001580030b852080c00b5242c0090300c0c1e080b0910b66501074024402d10758000d8a9070048243d030b009c01181607100e091078024030f552114008214066120710f0605414495401d000d0302c01d046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 277839091 1250 277837841 277837849
    0x209060403390303021504030302040315060906060f1710080a2901050303220902070f0311072d05100809070e06130c030b0406120501150305120a02010209 68
    0x540d05000c4107507101d03406568a40c40200902d022408541c0074100078040c40c2d40d40013540c901c003000b00c01e1091180480410209402a0151006154080c806071000c890717140300d200051007144110f0390942d0038400000381050013003040800c00e040941e2040308149030752000042c100c8000e0300b07105010002d8280010f81080501c088503800d4440e481c00704074a504030501182000000881d8010541c6a50041050b076900008440b002440400040740c44010036100d600710907029030158000c40d00000301401088140c0c01c1500003a031007503c43c100301d002c2803070300b40c1d5841e9180e01a00300755100a05100e09581400094980c0b11409010350401803034070345001c1152004681c2029001c200700c3d4051084c00302041c000c0e00c000c1c4c1074102c1107120a250600001c3e401c10b0b908110780000b07075652540c0019a074801e401804d1b026102038000d0128607503800c4a0384140f42144401c3d515075282a170350418040182c07102c0b004580c1c01c080202143e1140300600005584101144415907508000c4041c145c0c031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 277840341 1250 277839091 277839113
    0xd0c03050328060b04050f030313060f030e07030c031407080c150c01060905040b0a0203060f0108041e050d0306060513050405060a0e010e0106030e0115060e130905030d11070b0a0209060403 83
    0xc070b4614a0741c85600c3c1105100607c002d0742c0000b44640c02c107004800c0040260b464060440700c841c9001c0d44401e1103078038246c0017000d8201640c1441c1c001c501002c1305000010b03e90408403403050511362821007030911402e8a500c42801050501c1e04444045070b41840d0080010452100d9980028a80420f8040c19821580035a04c81703c2d503191118200320070b1013502207a455000300e850344298914500640003c0082c2e000030104c074140400c840218052240d02c40c03580c0720306e0b0f4441c3d403500f0150b109400e00c3d959622100006800290801401003031051141c02519880541c170503003454801c0c1010104000382c40020b008076007010005c04009003405a03081c0f00703402450540740600c3e140d41485401015a6a072804c502032a0f81440340e503248c1c0e9000c000e402c40484001c0d20b004609001c4240c0021028044070b08240e82e05070800d9a600c09004000c401030180740030310081040062804140c1502c0c9000752003018041e851800c0000d80010300c1038000b8035801c100100f40d103180036200d03919121041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 277841591 1250 277840341 277840349
    0x1207080c2814030403050702060d0e010f05220506040609050309060f0408070b032215020d0203010e18060c030a11071101120209060703110f1504050d0c0305032806 72
    0xe0301c0e071031500342201c0d00b0a120240c441c000900c0c00385540303020744024042e8030030a18000d0161900281140540d01a82d01c42007540c0f61403c02413007400700f0f041b08040a02010394407400300d25000c140da607000988003250b510300c3c140e2003009041d0540c0c46803200d40c0240b040c00c0c001d440e5404208070840d00c2c0d0f03946100038104c04c040070420700d03110b5091060f031a290000c00d42041000070010024000c8280650481001c070300844440412808424601020f6059509651409441c0042260200b801480d0095810386049c1c003050282d5030b42d0881030b8103400a482034081c0e62500301d000481c10101460008540c03009182c000411960002074030140ec0340d00c40c2c0002c0d1960300c01c005001c6440e42c2e121007140381d00003114605500306001c0200240c218800d059004060140301c0ca9607032140301c0c05100000c07844001c84251151440484e0350049800001c035400c4400340907100003244e2541c01881000550341d00340e034071181140d07551441800c10340320141514948850a80f46890410800e0040324060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 277842841 1250 277841591 277841647
    0x30703170301060f050a0818070807060302250201080f040f02030304230d02060409091119060207080307110f010c0c0303021f0e0a0f1a01150e03031207080c 69
    0xa41c94a44000c1810b45291300c800d0811100700700c07011109501500198000e04181c09000c0d840e15070303d000a241c40344a42c04241540110a00014280c1d050303405000a48002d50741402a82e01010380c0d940c03c0c1b4080c4100a0100e0800b00111f130505040d568a1a40103115000c2c10407041c0d01c1d50000ba11750f801070350001c40300c000904500654040c03d403041c40420308003541c1003100d0b400c0310f070f00242c0540100e0040c501c8566960400b00306002610144100251010b41a0101c4160a81000416012034000c1201500c00c52100090001c400000c03526002d411520741e0480e29245030030803030049480800c0904104502141401044240047c2c000031407080e00201405424040e000d0401c2c0703524140880701d20719058421041e818049080d0510310ba01030060003030005149414038084640f80a1f8000d40c5d0400400421070080034520941c9002581c0c4480c0d001e80e18038020140c0e244150b01c0c0c8d040300c407400400400e030101d0082a010341c2000c4504203440c182444282c00d40d90380e02d4240c0203030f441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 277844091 1250 277842841 277842847
    0x22b0c050708060a1512021003110906040909060c080403090902031008100603050607170a11071704030615051f020f0a0309140109030305040e04020109030f03020c040e0f1b03070317 80
    0xa40921040c0170002403540703440844460070b00d0340003d1582c034040f108903803e0549071110441000c40a104a0300c0c0c0390801024180c4950300c41030741100900005408440152624802005150003081001e1280d40c1c0755641d0241c1034140521980a504043d01808054800000102d03e0744410700006480c0000000c1c00107400349541030491400402408890030302c940d803003020140c513880031300e0113521191441c0081512144204150054070a0400c0038046980c0d035207901e10000d035000001d10480780510000c0c041d8040d450450800510b1300e2054680c80001032103680c646110101680ba00070102d4010f4541841c3c03801030701e50030200c8440080b03000274030482d400c0c4074400c82081d481042403070a180c098009801c41e80c1c060164411401500d01000507d00018111780c0300c1e000d07002c05142c1c4240c0031500b07280185000b941d21050808880d100354204243d0451000000624401036415100200011405410355081c00300c5030090746601805a42c0d000b001207001040c440540090801640e5a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 277845341 1250 277844091 277844111
    0x4030209010303080415020a0f2d02071401050a051204030c060e03090111010905030301061b0c15030b0117011802040b03090304080f01051510031506090501022b0c050708060a 77
    0x1a08407044006c83c4440b803050100ea50a5507001c07d00c00c1c41146541400d101d81c000c0742080108030b989a58648089048000704191110f070702180d11411604a500240d00305140c010040da09402103240301c00c0055800e001d100c40129070a5500c9410a029051400c905031054a810043d0f0f01841030f48100c0741d100250340c1c201b03542c1c0644131460044408000700200030040d550b103901c920040c4a014208140154080810065600844822903201c121106c2c925038071000010b1146001e01c0030408a8a09408908554002c1045074a403410081d800109a800c2448441000214090009040740d0034040443c10240302001180145400300043d5101c52400007a6441c00d5000d80c2e0404041e4184414002e80700c6c1442c5100505c204115a0602c50300102007040303008040b1072850752400f260000c0001020b80d004500141944c1d03003a03082d130318046101c10b400c00c4000c403e1010340240300400600340e10707a1441985c44002c114495016610015614900d0030f203007038400c0d11000a459510318084c1c2e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 277846591 1250 277845341 277845353
    0x7080a1e150512060c0304240203040501290a030303020d060801020c0705030601060c0c060c110603070c0b0a0c0512040228091b0543020909010506090406020a05040302090103030804 80
    0x14411941643c014285880d2981d103c0b2090700025100802191410202c2d6140c060341c00300d0344035440d814400c01c549910701814054003a100214281903000c20b080c0820071152031520000445000c05081c4032001440c56504500962012910030f02a40d900c500203c0c00d1402800200302c0c2580110003040002d05081c10141880b02c185d0200c002e0089aa0036000000c0004d10f5101c21903000c2d0a0501c81400f446c05c00d030910304407203110706a1040d8004100900c03540c000644840080c001e450044103513580030a15000c4407056000c00b00030031024411900141c4500701c800b44e02ca44064a15488a03541103106402d502c0c070a0318001144c212202c05000d000018403400b42c802c1c90440ca1400542c0d0003120182541c41800f0090a804500b10f12210f0b01d0084d0380340320402031a40b20b005542c12040c4c44481784d0f80c3c0c0e150350400c038404c500c101d000c51300c03545050040c03601402000785014000d44a41e55000000d42c004801d02080c840244000805a074805e070149000b5800390b12507070f6075890a0b103015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 277847841 1250 277846591 277846609
    0x315073b04020a021018020616060506061c0506060d1d0f0d0903060b0a0803030a020403030216050906101101051009140c1602041b0e01020708010507080a1e1505 71
    0x46806144107102d450b40241e400120900404c240f050b0000c6c41c10080300c10210a0501d020019410170310005074001d01507112000d0300951401440d0801603521100d04200c0b10f071160344c1c58421000008000c62210100580c0129040600140b009103001070480100064801c1e81e45c00301e1203040c4039202c1480a00092003869122440d0b5400341021000c4200054500c1101e4080500800c1d1b4400222008e511141c13182000b070804802140d45910305500490082c1d445800300b10014010001014220144040210300391200107003080310f15600c0f5000c0c0306051040d400310f038042042416005000352828404c00740074a040d0201003d0319410004010195004000b1130b41c0008145400c201001007081d094803003021121440881d00078860001602070284080c2c007490180e031000c40090802c1e0040d0420307440140c20380944048640da510003074200c0d90102c031a1b0021990000c0015228400c90b072204003a030824000c9000740084002c10f1100711000307410f0414403200240c000b40414078040d03030380c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 277849091 1250 277847841 277847957
    0x501090203060916300501050613050103021503041a040b040314071101110703170a0306080f030a030b0a0e0f090f1b1002030403020613031104020306031507 69
    0x5124915110540c4d04c040103052090342c24500000c00d50a060480034280c101c1984106490a690b24065040050003060240c079032911913844408094048940703806181d04a0f0b40091840c0b601050401c5002c0651b0310040c0116618200c85c90b2101d10680100d003014001e9018808450741441e140c0740c040d190f500c0810314464413500510029000618542070b6584142c2d00386451544d01d000e14646901d088034a1304000c0c000c0e47c031400e0a852416487d005401070a2040e6018004181c2d034151143d15900342e0080c51006030805c12940a4450003030b0000c2e40540c00242c0028500d03942c4900710b4402e040e0903146403080c44070100c144400c102c420409021031956820207003030219181c10064101030820b8105d503002c0d248500520400f14000c0c0152801160043c2c94907580c0c030f80e81d40103c0f15406043c00704031120541040f002c0d100341414070370f42e4402c40c0f02800804407980701201d40410044014400010000343c070825018400d0450070301288180101003030740c94003c07410f04611b029034941c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 277850341 1250 277849091 277849093
    0x10b040504110f01110d02010e011112010605070c030204020a0302070308090316020913061113060e0f121e030c0c0f15070303060e0132150c1905010902030609 70
    0xc01e00c00854070000694041d000b089820640124501005071180003254100800f80c1c000c0d20404503e00e0340641000f0b9501d43c840d0001c01c00032021112001032801041e030400e5804040d1001403001a004000034400c1c40e01501d02c03501003a980c8e40c001810790384002201d00010384c000c12100201908000e080d0340011700000a5810025046a000008200400c5c007a106d0341407100402d0742c2c0381d00300f8003007148503402c00f10512140e80015800103069211064811400b028500c0006040748210600808450001c1144030807052542c04c12043d03000c00d0100300300c0d034003814402520700300088214400c0014006c01454885400114407030400000042444c0603802c1010346462072b0303a44810404084190507001515100300b8241200249003a8000e441c0b1841c030300340042010000f8100350501c01d010107144951082c194181c0c0e80040d000d469400380c100c0500541a420402980701070075001d010740b02144d02030807000000000c0700c400324000365201e03595504200d055040501040341d003e88614 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 277851591 1250 277850341 277850351
    0x606011106070e13020a090503150702190201030b030d021b04090f0807030207030f08031b0a021c18090608010e0307170d180303050709050d0c030b1302180405010b04 73
    0x3100d007925904014610300030424440c0003101c0c540c1d0b4001d180c05091624980c215210080c41101070864180750184174401e10806a640f80c599840164043c400c078501d5018150003c400451001c1004d040c010803030525485950301030b5203443c02c005801070610554010081030721140e10f000040052004498012410240c1720b8021526000e200610302e90710601c0300390754680a0908a061100b035803c001e1880c04a5001c2ca0113225168000c0d502401030208014070941015100100780e10521800c9400760b041030064590301070180416148158450078a00c2080003130000c2c0103081482602701e810b42e41d03582c0409100480007486000c0e81507581000840c41c0410785d4075048400080d1115007034a0710070004841051032610342141c04040510300701e54440c5038861801801900c803c540002c0040c808180003d640c2c58074a1144403241c3d0401c04140704181591902e1010b1a001820801e0003003404e1108801600c8403880160074802c8194000024205403610909640c08170845512881c244 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 277852841 1250 277851591 277851617
    0x1d030901050403080a03060b180f0402180d1b0b03090c01020726010f020a0e030105060103061406030a0608030f12010b030106090b160b240a0b030f0a020408160305060601 75
    0x40221010760b5000003402e51a51026001180034151f0754102e100405c0300814500341c4080810020404040111061608109000b0901040380103c8501e40c640307044000c0141c0040c1008080c0b2648580181d07c8214000c106034142d100b0150a0b61007010040c000004000790b450007449071007802d00b0b00340b02505086140c54945040405038042d900071a010110124031808c00944c0500c0c41400c01500942d01c1d1203401d0005011803050702c101c50300035420800002c05662083c860003058071804218803200721440d0052040c1a0001002140425603a10001c50700d24410400303400080c0141202070303950100e0903085000035006902180014000b80014442580c1280e080341c20f90302c903800001e450b226a124224240381c0c0541c0e000c0c0c461844541480808900c00880845880015400125040d2207000307208840c041442507000000d0284045001003902c15041c03030b0042d94029001d414a80c858144905000c141007a2501c810082d00040007042018014154400c03000d00780000d1070540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 277854091 1250 277852841 277852847
    0x30a02160e04080f0319060312081308040b0f0405091005010f03060509240907120b1f0f02120a090e0901151710020414180405030d05041502030a1d030901 68
    0x60401a0b85400c180840006d42c8080a0410414010140481800b5a82e66401e21450f00b15007885000d00080c5c1e52400200c42c49155802c1415560b8010806480d013450070300307002c42c1904861421400310104000004080d035440030924000d8510300781c05c0010600e03260014001c50407140750f010178107044c5541003000340e40c1d145045501818000001a91104514151078004403442c1020383c01441c903014000c4841d8810b000b14100b103410742d001c019000d8844200300075560407141c0010b01d0310320217503010134441c490b846e02c003c0c40b0071030b004450380000e11020942d003541080c0500e100084140d10200145d11400813190740000401008101c084582861041801064082d482d00050401e41c40664070380100b0136421440e24101086440e40d4032840c0030510801d4119500340710740b900700b41004420b5000c1e02c0e000d0045901c54000d614000c1c0641c0700b1000b07884001d200b42c0d110542d4981904120300b6600081d88140c118890029501e890150020031000040d102410154400c0c8006061039030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 277855341 1250 277854091 277854097
    0x3010e01080d08090c0108040c030501020a090303020d030b03031605120415030b01080c0313050c0607061d0c3d030b010906050c032b140103051203190903030e030a02160e0408 77
    0x200c280703484c80032a48c95003440c5003454080d6000501941c0300091410202d40d2080300042540e129900f956407440b4158800c8040d60001c81c40c0329450341041064117411000282c20090301442232081d074041d0071600008180a8205910070105100014a40d03003503c3c0d071520501c030086100b42031054180c100440080700f0750000802d5800d030703054907194840038410200b020a1507504010000f43ea00c40d000d00e841d00181c6220142e01880c0c0d490807007410180e12003c101680d81600140051903158174841010514010403c1000312100b401e6015031108250608046003100043c1c4007c070b04560300300001002001594042404c04c01c1c01e100e80f0400032804001c132031030b582981403480c010b0520413050300e480c1100d10309c1c1400c11030702c1e021122030700d20002c0d00034a0490740039030b050300c0032228004440da003940b00441d190030410150700380d001e4042445612070420b9500901c0c00060301c0040c4842c451441c0d100244002c056480442d01c41281519a4100c1d00a0002d0707a00d40000350600d640d403000f80b80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 277856591 1250 277855341 277855363
    0x403020d030201150f06020f0607050a050a0e130b0909010603050c13060807080a050d03060303090501082d0a0c0e0303030a110c0a0b010f151409130203010e01080d0809 74
    0x5040e2802414400d400559261541401c0c8030070181d80c0c1c00d440780c2074207018403a0102600900c420901c02420110b2440d101c2d03812074440929103640440b040f140e03648040f030108240450500940503a403680b45120325880c8045000150f140c0e41002000040ca8009000c440070ba810706100307000140012500d8030402c64240d444032000484440f002c406445075400101c000e20842a001a5125000550780c00d01d41c012070a40d4400460064110f0a032070481c0000343c042501600100202c2d41b04018499001c0020142c50380d02032000b90010614140102003142c6041031441440401c0365280701e00e10340000c2a060a01c2c000b20380d2408245c0342e00000b0112a00965644010b00403039640d0811103005002280030b46584418078501003076144000c8c041c0840080c8900408140800c06654a00005020741c503034440f1040107580240d01580500351580e004540d03040c06100d0001680041c50103004026540c1c91079605051a1625001400c01030804010300c00c01401b11903903000c1000304c084 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 277857841 1250 277856591 277856599
    0x20102101a030f0309010824100306050d05010c0e06040f0902030603070e0405010c0e0609031005091911030c04020909070305060103020f0304050d09050301060f06110a08030c030a05060405010b040302 88
    0xc044441c4808120240c110701e80d0340c06005048106861280c0800142110030090302c40c401951101c00040c941405042c80500240380704000104042c900101c0030100c1c5001c520340400c3c1142c0302c202140341903007031002c00c50310f0780c0d118000b000c44a40c108010210040081c2c0303200382010301d001a034030105030541c45640f605c2e07031740040456003d4038280a520302078075450704070750147d08080c90a07500800401600400041d00107058407c989040703401c0f170b40b8128008004101d203880300d44400c0c0c020310000d44140964819140e0b98049007008081c00903105020314071101e03409081405050800e8a00010300b84258030403c00d440981da1640001c0b5000042e0f031400065036a22040140d00a202d00d0f40070681450001c800c000802c0000201442c450f4250781e544941c642e0346500b81401c1e0f840501407154801c00c0c5401c140301e42c0384100d1140c070111642c0c07803c64820301c0d1181c41e0901949e0055852015689000080060f82c80f140d0041c0c81d0811800c0c1c07010070480d0301d40703420309199000e5400000c0c17107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 277859091 1250 277857841 277857851
    0xc030601091e080618060907050f0418120f090e090a080a021603080712080c0d230406050612120304020d0212060a0605040c030207020a1202130c020d140702010210 72
    0x14160301040244058401c0c20204c03142c504007001d2500b4030501078226810503106450000b2002c04001c16110200c40000d800c1e40241050601040050480385051b07541480342201680d02144040503480300104039500c03109854514480001c2c172141741d641108141c1d48094082c4602c840300003071601c00144d0400c01850b158a120b00049040102c50216000d00180070701c0040103201010f8006d0242900c100b202d00c0c05414800000d4038142402c5448075261070060021070400810b9400003021103044a00120b50749000c0c240c01102d240003983c0c1914403964480410005050240b0492003048107040200082101c2c0b00380300001c0e200041c0020f00502d110034408046440b400110814881c83e50180e407107a01d841010780380140305900c10103104070305292411407107501a1088540d03113500600300608542c2000700381c0d4800d03407030454100d80104080c841e00c40c112140703100c1c0c817101d020346501600b0f915131000310040c00340f801c10001000b08202000201e00507a0000380340f0700000c1c60420041780b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 277860341 1250 277859091 277859129
    0x913090f0308040c090614041407080411180a06080d08011505090a091805010506040e2a030604030305070e01080727080d05130e010608070318021c03080c03060109 72
    0x101180d480d4811720680e0f080102c007080c004140300711908003035003c0c0e50400c44031070325510481038000207441c3d600106220300041000320390782d01c00003000b406001e00808400c0c4050040c81d843d418003114950030040d41c5203c10301c0781c0041840014200c401c285003051303180d4140601200ea40503401d15503018050000f0700300c002502e480120100070084800c0c00c10042040c0b441d0701500601c6044201c815510304000160203140174415801e0204204001307001d114608890403540301250103a45041c80308408880700295010010a8840d80c0b2070350340460b903420b103594080c146410541000303041c088800e00b0021241da0242d04010020b0b0a491500b461144211103801c3d0102913403c0703000f50703001e625141418142c0100050200c807040c5c40a42c41825502c848240c0280800c1c0200c01c0050030045c082680c0c94442d803c8501200021702048810f001c0560020310340d5210401c6500040070741115117402d050f0040c00440d40010540c204a20310300d046000200144201d00a81e0040f081000c8884 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 277861591 1250 277860341 277860353
    0xe01021e091f020307050c0102160501030f0b060f0a0e03011a01230c030a080105030106060c03210f05040b090705090612011112180309060306060f1e0913090f030804 73
    0x219008840d10042c84440d42100c0000f500c0f54010329050b90903128074003980089510020f038000002151a0001024608040044024142e41c0540451480e01c1c0c1018403490365400c4014101c54000581d0703295508070601c8041c1c0058542c030000d9119074506000b100c01c012008040d220386c1502441c24888a0341003550721754025691800c01c411400c3d0100d5980c601140000c01031844101d651621f002e1070b0f980360105030a85400d07000f001c0c00030b442c102c55000000d0141464416150034910b9020003000c0000303c1004076028012b005131015103400c203001c2441440086c298106014801400c2d900d400c00c4046007110001500050084e50940700205442c00294007294031134a0303207404a42d4541080c40c0301c00001d8800c1d5201700030100160b03034400d048100042114000c3c01301a00b002e041d590f40a04100f013580120f81c006072188401c01c80054071002c10601454800c1d030103a12a500d8014040900400c1380981965a5074503140100030800310340710b000c030f28820f02d03807502d401c000d0740c3c1c0c50b840c01d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 277862841 1250 277861591 277861609
    0x105030609071b050c0109050d0210031e0c0807090902030f040308090a0209090a03271202040204051c26030f18060f01032f100201061206050a0e01021e09 68
    0x460010001d000e200010881301040303c121007182640e8494546031610104907440c080c1120080d8810322010100701ca1501a82100040d0001155038141c3c160707000902d0b2040d2100400d00200054411040080700c0d900610003c002d412449421800c5141015007928084000f42018043c040b0100008401c40f1003001655040e5a0141013140745081400241e0f42e2a08080c0b0100d0110761503601806411a01040c049058000400c8501c205032400302c4032031032070400e24001d0b81c0203502080045040e84680441d0441e444524011000a07415401c0010002125240c0c411050f0740c09019610007802d100c0591742c11542041111400762aa8091741034541011140106240070b07840c10489000c81d0b403100c4a040720700a10760704e61030640126143d158203c21116004445202c50030403049401c106030a8002000e00c0d000000f030132a26110342c0d007010380c0c40802c100d64880d1a47d041008688450103180042008070f8025400c14014440000f484110708598207a1501d0101c1d1601c810381da00350300b03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 277864091 1250 277862841 277862867
    0x6021f11040305030c0706020a050d081510020606030c01050a020706030b0402160b01092703080405011104080f010b0a06020312100b0708031e040521040e010611070f05010503060907 80
    0x10980d441d075481c908a9181c1c0c01400c03005285004a6000140c054004254029507a42c0308026001910611078181c6100707101a001380b40e800313100f10251446803074440286110b47d071240c0052140b803804c1b008040c80d001702a450241003020a004264055400181460603580c450030003144042c1c0312170200f4001d0140283d07001d152104111248140501c171050345040c0c510038401070000c44400032110745007210321480c06524001940941d4040380c8900407040c0c00502c14000420001c0125000300d105400681140013580c10608010140090074401c00c01d213620180e41201c01680ba00348080c0d102d0003803101c92000c03140c100c1c000640302c0b02002218005441801c10f42030b03c0e1806801c213501c81d60021a200070700680024865140e1500c7c40100d24480e5a1100040c00001780302c010644508051140340da104560074400495000f0210200034040c0050f50780b000c1403070030348401d0a0b192001c29404407a40d038084110a120381d907400780840340c1c4844140d840c000d0580354072004031080baa070514 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 277865341 1250 277864091 277864121
    0xe030d0f140c0f030f0334030e010e0f010c09080a1a07050c0304080706090801090b0613091a040c0e010e04020d111815010f050d050a0b100906021606021f 68
    0x1503200d10200b51002847c0551202030480401001100c0c140b041158440c109090325401b03011002d00185c425048490160307442c4001140e40114220aa03181c0110380c5584482c694507000f001821650000401d8001c100e4074006107864101c544411550340716418952203409800000505aa40a24111400320b46403004980c0d6465561050a85440e1107000e004002100020000782180c41402403240c9242c01c503840318019180c4030104110700910f0303100c060386581c6079010a00403403641c0c06840c0d142c0a40c0030b0700209a14141c0303050042c0454540201406035452801880305800d001c1d0300aa1095042c3c9200c1650412414150411020a0070143c0c0c0017502c41c1805401d640603902e0580140c602c1c55a010700f0f20003401c015600443c02e4001c00300040c100f0304c07502c0d40085498001d141c10990034040011807548060115408025118490002c00e203845410410749604124038202c0300c4100703244490240c24050003e454420060300c001496607426807844003840303290701c42480c440c2d5200d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 277866591 1250 277865341 277865347
    0x1030b012d020a0c1d0a020a1238131401270203070f09050103110a0810031428080307050a030f1a0103050c090634030e030d0f140c0f03 60
    0xc05e45180365901c102c1c03002c00409030b440102c0d205446e24020348400c0c288903290001a400d000b521003006100700700624290441000201080d0381c0060403402600ea110311881d00d14401d8841800502401d00500d42002444e020f5002d40d5814001c00c4581542c80e0401e03035600e51b21b01d090007aa480c03503502000c0070f01c1510010038411004d0f0400304488030450240c46043e11195900010b500701d920869605164070010001400500c0c07107403150315880301c1c00d0100015616100e8070b60301156100c103500b03070100f60301c080788206142f032440c2c602c01000b0382c012131a00c210420301d80d610032041c0409098103060007400304944c24260301a8015403002613900d1001c001528034041807002d07814840a45070701107403401d40440d198072101400c42d0505030780508507924100c15001c050002c0881d80c02d0800c44010362284841540301c03203420880e030b518060f94481700710a00c240c0c2050b08240f41010100d060110703041c0507081c0c068000a0900e242d280031210941c44072803000d403a0742406200000021180000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 277867841 1250 277866591 277866599
    0xf1201170c040608060105060f0403060f230403020c0607021201050930030103030509011704080405090c19050306043b0a08222301030b012d020a0c 65
    0x24a101945111008a07111500804140422141d290081c489503802060041c4502d00f403601c001c0c250070781540d115031304d000d80d240c45d150b0859100c20407002c60551103480f030b02c4081c0005071710210360306010400802641440d55000c2e540d0039520120038021500071520405541d40c3c180c4032640d05041d400207004030700d0843e038941d0700d91240e500c01800180300b2200102200c020540018000c41c401e100c039a2131642151000d1322141c0003509a68104070a05041180542d020803810b8001d6100d1100c40341c1755410a0304000c0d9440e0300804500401c0c00a00c00c1280c6901494403c003e900d08500305a55203440740300206000e090360306202c0030141120f2000b12032840d0f801c0700907421400d454030001c010b0302440401d25202c000342800a80000010311140c141a1708060b642a141c06603161840825540d44840d0101034408000807400610007180306000e0796014064241019001d191500c402e400354800090840d46480c50021120481076450304400d00820800c10440e4020180002990766 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 277869091 1250 277867841 277867859
    0xf0a030906050703090c03110301090c1401030b010503042402040b0c0303040606050108060901030b0c09040614010e042306040204170601080d05040b190903060f020c061503120f1201 80
    0x40c0c0c40302140e80e1494039001404051007407060702812540038001e0500c0e0340c5140c65031980c07080c103001156819542e4543c6100040e410004543c0104400740131500c4a4250400140482d803880c08094144182001080700280c690862140c0c80c04000700ca0020742703508441010f0081c0a80d40100c0d110303210000e0280e10704c060010295200394410b001c207100c2c107610b82c0b0044420100035641650032042100050002490f81403200d0f500070000e00c522402e01d5440800a0705542d0150301100b216525400f075200e45591100d0141401d4a094a042c407424101c5c00d00813906c42403035422004003a2800c00461200e940b07039011540200380024080144050010a9648483c030a05c9210518410440c10040d21402402520103c1d4404e48405003011443c4140c034419911064100080025041d004400500640300e10200b8200c0f00800580b1505610f216600c1c0940c050711040c0d001d4240e030b00b0422039940008080a0307041c1c0c1003440310340f03580103448158601d0043c0146640380340c010600205900c0300c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 277870341 1250 277869091 277869101
    0x20a090e01230402040510120e0712050f0c15090109050a031b080a05030d024005031c030e030d110a030b01080609012c04111504060819020f0a03 64
    0x115140005007520b0703250040008900c542d2040d240c010f180a40010b82d480d0040030040203a44454101160501c4044800b90800b0341c43d030004494072484034003035000e00400300f01d03188250340d49a004100c84140c05001908000740c001c40359140d4000014101c0c1c10b0b9201e1004500123000181070b8100b169124a0201d10750000b00c016502c00403030080000444030800240c0d29644d6420070091494840b00300c242d00040e6108024500600445241181603078290400b15094804a482c403001d40303c6005a1500000f501342d070106100b9407201021072120003402043c40441070f03140c18005526007540810700e065014012582107414903000c2c0105840c590300000340180360040d82c003000384151701030065403e01001d80f00c298114110100620103225800742c40c1c050750082c05505483c0048030100d0440000d422101100c0000031a00703401c141e81020302e4290a0000c80440c03a508240c00c1290003001c920300140392078900707640c4940303207140003e15904462181e40902220390362081c000e180500a00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 277871591 1250 277870341 277870379
    0x905011706042d0b040f1407080c2b0303090c0509040803041103120f04030501180f060209010c02060a17010b16020d1415040506010603110409020a090e01 68
    0x412108440c000d900000c102a40300d50742c0b1401d84001000140e020341412014010400032241000c2d1109003c10400034109110b184112070110b05403d9510b0264000501c2c801c2021050740300b07075424082c0101c04034414102403c1a036201940f118201084c03088900780b898450300000403206d0100a040d41078000b2104580207820f44030342e0a030350303d06022030003804903005818070b4014008600007a841c00c6040b0300c2c289000301111100c0d55450390340900ca600407502d4203d5101c00080c1003080001c20300409080e0501c9200c44c6114141d1510380c8104020721400c020715280c0e00107104012a030003440c02014264000d444a6160b40d01c000340a0302c94540101e1075130303c81400c02e00000e0002410720484040560741944110035034281d03130910108442900085445040c01e901e0061079030350400c07a5450b00c1364810580e40003070405040460070404e060700300408049c188000d000980100404a5007103403900e41c070050307888904070b0048490b84803030340124003800c04c40c0000144604420000d04140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 277872841 1250 277871591 277871609
    0x510060f09050c0307080117010b0a060306080f010b0d0201080709031a0901051005010e01140d0513031b030e010f05070501060305070f2103030518030703020619050f041101021501090501 82
    0x25250f0f4075500706240000c4035008001410100140592000c404001001c0c003201c500100d004415000040e5119965420540000703555803800c01068000b00105609130719500b008004013244000802c9900e041d10a0180c18084070310041943c1c2d5104a0700500116041184071407002040401c0815202060b19a01c00b650708040100d4504600314088500b11030b03050b121340a80244403401501c040d050403450f01000c090511107091180000e0146611035001c0903001c0d509081e0f18640078100c01540340c03003501c00840c54035280e0b0009401919242c4c9980c000d09014003440fa401c0c1c0304a5180c030a030b0794010207a5007404000402c1004c005644410380f1140303981b504503592074042c3c11074061101900c0a0319000c43c1c002c000d010a0080c0d01054014a0107580390308403a0401e0081e500c0e40c2e000341c0342200180c0c000c3c400c200442050b450701002c4c1160000042c081400c150450080d01c4401800c050305808509407a446180c1c000c1041c002e0f0b1411004461420f5a5142c048800421007441001c002c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 277874091 1250 277872841 277872851
    0xe0a090c0f120b030c22090f21080c070609020402070b0a0516050d0f15120224070212031309050f06010f0504140607020418060e060118090510060f09 66
    0x78409290094540c10b19002d030042502c020800100074402015984199008486c800c03203030255203990089440e510300409488030410040e16002d1541505180c1406804011031040e82d4059030101032035800c8051081d005886441d1030034650024281d059000354010f00c006250010031541c800000d00c114040d140c10000d60340c13400c8044101b0100c580392074002510401c1605075800d01640200030b84054201e00041010040d1140380c000b5189802403440c0c808027403116403c5103400880c1086e00300d039030b10704520740c14203c2d00a00858020207d00a200b03445590300d00d1000601001514096628002c184003c20b9a070903000c0020f00081e116074206500c5140020380e0742d4011b11400d0b60960b03030750f603856103490325250023107402c04042d100550784960100300200150380e03180504605060000134421300b10740700d40f0f86401242c0c1c00c04158110b0707030003400040054081c00035140c010004200c02c046450b10180c603056007801030307080c0c200d4030907450302da004240d006440d5200000c0d1003180200300302c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 277875341 1250 277874091 277874117
    0x90501060b1603030515030a05060103060c0c020604030b04170f070c08122b1d1902030d03090201121a130b0d030c1407080105090712050a02010e0a090c0f 68
    0x70034824000c04240c5111904000c03030010b4440da028070760000c00222070503204004070000900304900000705644c0303070f40300c0300060003401024414680d40c60010b0400c1d03031ba00c0f801540400c506000c2c0d484081e00b01151040020144804846403210300760110400664403032030b81c0160b80c5a0341205005485100c6c2030b100101d42080006105c0c400d808038041210f060559420700e210b055401406401d4040010f4900820010b14034000c0b0809092800e000324100001180c03401c0c03070540000b50000319032012041c42400340c0c8022412440f0200145808030728a001800140e81303001019582d1841c0e10700e0240002c0c403070900b100b1454130050084a0050304002d07501803040079200402c00041d800701550b03240c0400240a0581080094031813000b21500d0007111808a040c074035113500100159459504000103824103112410150460030042d001c0d0800580316281d0b00c49000e10f00a040c0041080b51100e00e5652003440d00040243e4401402000c601001c01400c4004c2807452a020a440b5103200f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 277876591 1250 277875341 277875359
    0x2190521040b030f070c050f0a330e010b1309030206070c2103270203063702090d05240103021027030b100b0909010b0c01020d0c0309050106 62
    0xd01114140d911860550b29403074144200070340040d2421003401003070080d046c0021014001d044c4140c0b50000074019214490800d00b0840c03400e0300380c1c1c000c4420806442075800e056414076031071010810100003040c20748200003500428070f07007401507801030030b50000d0654400c294001900d26840bd60994445880d16a0180d80c220070b4088010004208040030080b40c840c0900b0030504000c152074003090041203200c0da40c1c1d41d1401d01244074214600c030790b50350341035050400109401c541c01e107408000c901c010b01d191403040d484902e001e0a10010b41d66030300b102c1040540541d03100d040010803401e201400c0d0300c1e180344c0d61804031480401e1041c1c00c00260002c0720300003c455040340d80103060401e01c4001c00d1012038043d81c2440d441c03500440e03041212510382c40207000d200c0180d840380f038800c103490411000354844002030703a00000241004002c001490707140c800a00d41102d15400c81d07641c40e0341c0d0a200c102e0190040c0c5032151a220700d0881c2500100b80d06800000e41b0300d01a0000b000201d0300d0300030302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 277877697 1106 277876591 277876597
    0x3020c0d0b040b1617040f0c080d020d0306030c35071403030301210f082a070506030112061b02010c11060601020709050702190521 58
    0x7080300e00c14050b40c0010720b0158134a082c0211030781c020b00105200c48885408940c9802280030040c0a00d200ca100c59071001c100da10054958600716591f00400f0a100014441c040c0c0403041345003c0e1007000c0649800400f000b6006040c001a88859048030039100684030200007034000c03583d80d8842d1111019400c10190264916040c1c14150100800407424480c0d002000100880105102c40141c00520b0040c0c08079840101d003400240041c0002026020718000915405e00f50000151440000c0e01c102ca9030700c2c1e1921081c8072680d030300464000d20380c0003801080180071040e400010403d640344101c0b0086500045841d0080110904e00c2c2c20f140540e448400304e02d070703041d0003e0500c800300d40c640740180324520301140001e40c0c03250584940c41605a461000c15a0300384280030000700d40c42020300c1200030122620b0b1071680c4030080f200c0100d075121281100324020a0300021 = true := by decide +kernel

theorem cover : BRFrame.Cov 277697841 277877697 := by
  have h0 := BRFrame.cov_init 277697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 277697841 ≤ n) (h2 : n < 277877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
